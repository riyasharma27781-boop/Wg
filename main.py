"""
Word Guess Mania - Telegram Game Bot
High-Performance, Low-Memory Architecture for 1GB RAM Linux VPS.
"""

import asyncio
import html
import logging
import os
import random
import signal
import sys
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from logging.handlers import QueueHandler, QueueListener
from queue import Queue as ThreadSafeQueue
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

import aiosqlite
from aiogram import BaseMiddleware, Bot, Dispatcher, F, types
from aiogram.client.default import DefaultBotProperties
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.enums import ParseMode
from aiogram.exceptions import (
    TelegramBadRequest,
    TelegramForbiddenError,
    TelegramRetryAfter,
)
from aiogram.filters import Command
from aiogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)

# Optional uvloop integration for 2x-4x speedup on Linux
try:
    import uvloop
    uvloop.install()
except ImportError:
    pass

import wr

# ============================================================================
# CONFIGURATION & CONSTANTS
# ============================================================================
BOT_TOKEN = os.getenv("BOT_TOKEN", "YOUR_BOT_TOKEN_HERE")
DB_PATH = "game_data.db"

# Security & Global Controls
OWNER_ID = 123456789  # Replace with your Telegram numeric User ID
MAINTENANCE_MODE = False
BANNED_USERS: Set[int] = set()
BANNED_CHATS: Set[int] = set()

# Game Rules
WORD_CHANGE_PENALTY = 10
WORD_FOUND_REWARD = 10
MAX_WORD_CYCLE_POOL = 50
GAME_INACTIVITY_TIMEOUT = 300  # 5 minutes idle timeout

# Rate Limits & Cache Bounds
GLOBAL_RATE_LIMIT = 25.0       # req/sec
RATE_LIMIT_BURST = 30
MAX_LRU_ENTRIES = 1024
ADMIN_CACHE_TTL = 300          # 5 minutes
COMMAND_COOLDOWN_SEC = 4.0


# ============================================================================
# SUBSYSTEM 6: NON-BLOCKING LOGGING PIPELINE
# ============================================================================
log_queue: ThreadSafeQueue = ThreadSafeQueue(-1)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(
    logging.Formatter("[%(asctime)s] [%(levelname)s] %(name)s: %(message)s")
)
queue_listener = QueueListener(log_queue, console_handler)
queue_listener.start()

logger = logging.getLogger("WordGuessBot")
logger.setLevel(logging.INFO)
logger.addHandler(QueueHandler(log_queue))


# ============================================================================
# SUBSYSTEM 4: BOUNDED LRU CACHE
# ============================================================================
class BoundedLRUCache:
    """O(1) Memory-bounded cache using collections.OrderedDict."""
    def __init__(self, maxsize: int = MAX_LRU_ENTRIES):
        self.maxsize = maxsize
        self._cache: OrderedDict = OrderedDict()

    def get(self, key: Any) -> Optional[Any]:
        if key not in self._cache:
            return None
        self._cache.move_to_end(key)
        return self._cache[key]

    def set(self, key: Any, value: Any) -> None:
        if key in self._cache:
            self._cache.move_to_end(key)
        self._cache[key] = value
        if len(self._cache) > self.maxsize:
            self._cache.popitem(last=False)

    def delete(self, key: Any) -> None:
        self._cache.pop(key, None)

    def __contains__(self, key: Any) -> bool:
        return key in self._cache


admin_cache = BoundedLRUCache(maxsize=1024)
cooldown_cache = BoundedLRUCache(maxsize=2048)


# ============================================================================
# SUBSYSTEM 1: GLOBAL TOKEN-BUCKET RATE LIMITER
# ============================================================================
class TokenBucketLimiter:
    """Enforces strict outgoing Telegram rate limits (25 req/s, burst 30)."""
    def __init__(self, rate: float = GLOBAL_RATE_LIMIT, capacity: int = RATE_LIMIT_BURST):
        self.rate = rate
        self.capacity = capacity
        self.tokens = float(capacity)
        self.last_refill = time.monotonic()
        self._lock = asyncio.Lock()

    async def acquire(self) -> None:
        async with self._lock:
            now = time.monotonic()
            elapsed = now - self.last_refill
            self.tokens = min(self.capacity, self.tokens + elapsed * self.rate)
            self.last_refill = now

            if self.tokens < 1.0:
                sleep_time = (1.0 - self.tokens) / self.rate
                await asyncio.sleep(sleep_time)
                self.tokens = 0.0
                self.last_refill = time.monotonic()
            else:
                self.tokens -= 1.0


token_bucket = TokenBucketLimiter()


class RateLimitedSession(AiohttpSession):
    """Wraps outgoing API calls with rate limiting and robust error handling."""
    async def make_request(self, bot: Bot, method: str, data: Optional[Dict[str, Any]] = None, **kwargs) -> Any:
        await token_bucket.acquire()
        while True:
            try:
                return await super().make_request(bot, method, data, **kwargs)
            except TelegramRetryAfter as e:
                logger.warning(f"Telegram flood limit reached. Sleeping for {e.retry_after}s")
                await asyncio.sleep(e.retry_after + 0.5)
            except TelegramForbiddenError:
                logger.warning(f"Forbidden error on {method} - bot was kicked or blocked.")
                return None
            except TelegramBadRequest as e:
                logger.warning(f"Bad request ignored on {method}: {e.message}")
                return None
            except Exception as e:
                logger.error(f"Unexpected network error during {method}: {e}")
                raise


# ============================================================================
# SUBSYSTEM 3: DATABASE ARCHITECTURE (SQLITE WAL + BATCH FLUSHER)
# ============================================================================
class DatabaseManager:
    """
    SQLite with WAL mode, Read/Write split, and In-Memory Batch Flushing.
    All score changes happen instantly in RAM and sync to disk periodically.
    """
    def __init__(self, db_path: str = DB_PATH):
        self.db_path = db_path
        self._write_conn: Optional[aiosqlite.Connection] = None
        self._read_conn: Optional[aiosqlite.Connection] = None
        self._write_lock = asyncio.Lock()
        # In-memory dirty scores: {user_id: {"name": str, "score_delta": int, "words_delta": int}}
        self._dirty_scores: Dict[int, Dict[str, Any]] = {}
        self._dirty_lock = asyncio.Lock()

    async def init(self) -> None:
        self._write_conn = await aiosqlite.connect(self.db_path)
        self._read_conn = await aiosqlite.connect(self.db_path)

        # Apply WAL Mode and performance tuning
        for conn in (self._write_conn, self._read_conn):
            await conn.execute("PRAGMA journal_mode=WAL;")
            await conn.execute("PRAGMA synchronous=NORMAL;")
            await conn.execute("PRAGMA temp_store=MEMORY;")
            await conn.execute("PRAGMA mmap_size=30000000;")

        await self._read_conn.execute("PRAGMA query_only=ON;")

        # Create tables
        async with self._write_lock:
            await self._write_conn.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY,
                    name TEXT NOT NULL,
                    score INTEGER DEFAULT 0,
                    words_found INTEGER DEFAULT 0,
                    updated_at INTEGER DEFAULT 0
                );
            """)
            await self._write_conn.execute("""
                CREATE INDEX IF NOT EXISTS idx_users_score ON users(score DESC);
            """)
            await self._write_conn.commit()
        logger.info("Database initialized with WAL mode & indexes.")

    async def buffer_score_delta(self, user_id: int, name: str, score_delta: int, words_delta: int = 0) -> None:
        """Applies score to RAM cache instantly; written to disk on next flush."""
        async with self._dirty_lock:
            if user_id not in self._dirty_scores:
                self._dirty_scores[user_id] = {
                    "name": name,
                    "score_delta": 0,
                    "words_delta": 0,
                }
            self._dirty_scores[user_id]["name"] = name
            self._dirty_scores[user_id]["score_delta"] += score_delta
            self._dirty_scores[user_id]["words_delta"] += words_delta

    async def flush_scores(self) -> None:
        """Batch flushes pending memory updates into SQLite."""
        async with self._dirty_lock:
            if not self._dirty_scores:
                return
            batch = self._dirty_scores.copy()
            self._dirty_scores.clear()

        now = int(time.time())
        data_to_upsert = [
            (uid, val["name"], val["score_delta"], val["words_delta"], now)
            for uid, val in batch.items()
        ]

        async with self._write_lock:
            try:
                await self._write_conn.executemany("""
                    INSERT INTO users (user_id, name, score, words_found, updated_at)
                    VALUES (?, ?, ?, ?, ?)
                    ON CONFLICT(user_id) DO UPDATE SET
                        name = excluded.name,
                        score = users.score + excluded.score,
                        words_found = users.words_found + excluded.words_found,
                        updated_at = excluded.updated_at;
                """, data_to_upsert)
                await self._write_conn.commit()
            except Exception as e:
                logger.error(f"Error during batch score flush: {e}")
                # Re-queue on failure
                async with self._dirty_lock:
                    for uid, val in batch.items():
                        if uid in self._dirty_scores:
                            self._dirty_scores[uid]["score_delta"] += val["score_delta"]
                            self._dirty_scores[uid]["words_delta"] += val["words_delta"]
                        else:
                            self._dirty_scores[uid] = val

    async def get_user_profile(self, user_id: int, current_name: str) -> Tuple[int, int, int]:
        """Returns (score, words_found, global_rank) accounting for uncommitted RAM scores."""
        # Ensure latest pending updates for this user are on disk before ranking
        await self.flush_scores()

        cursor = await self._read_conn.execute(
            "SELECT score, words_found FROM users WHERE user_id = ?;", (user_id,)
        )
        row = await cursor.fetchone()
        await cursor.close()

        if not row:
            score, words_found = 0, 0
        else:
            score, words_found = row[0], row[1]

        rank_cursor = await self._read_conn.execute(
            "SELECT COUNT(*) + 1 FROM users WHERE score > ?;", (score,)
        )
        rank_row = await rank_cursor.fetchone()
        await rank_cursor.close()
        rank = rank_row[0] if rank_row else 1

        return score, words_found, rank

    async def get_leaderboard(self) -> List[Tuple[str, int]]:
        """Returns top 10 global players."""
        await self.flush_scores()
        cursor = await self._read_conn.execute(
            "SELECT name, score FROM users ORDER BY score DESC LIMIT 10;"
        )
        rows = await cursor.fetchall()
        await cursor.close()
        return [(r[0], r[1]) for r in rows]

    async def close(self) -> None:
        await self.flush_scores()
        if self._write_conn:
            await self._write_conn.close()
        if self._read_conn:
            await self._read_conn.close()


db = DatabaseManager()


# ============================================================================
# SUBSYSTEM 2: PER-CHAT MESSAGE DISPATCH PIPELINE
# ============================================================================
class ChatPipeline:
    """Strict FIFO queue per chat to avoid out-of-order sends and race conditions."""
    def __init__(self, chat_id: int, bot: Bot):
        self.chat_id = chat_id
        self.bot = bot
        self.queue: asyncio.Queue = asyncio.Queue(maxsize=50)
        self.last_active = time.monotonic()
        self.worker_task = asyncio.create_task(self._worker())

    async def _worker(self) -> None:
        while True:
            try:
                coro = await self.queue.get()
                self.last_active = time.monotonic()
                try:
                    await coro
                except Exception as e:
                    logger.error(f"Pipeline error in chat {self.chat_id}: {e}")
                finally:
                    self.queue.task_done()
            except asyncio.CancelledError:
                break

    def enqueue(self, coro: Any) -> None:
        self.last_active = time.monotonic()
        try:
            self.queue.put_nowait(coro)
        except asyncio.QueueFull:
            logger.warning(f"Queue full in chat {self.chat_id}. Dropping oldest.")
            try:
                _ = self.queue.get_nowait()
                self.queue.task_done()
            except Exception:
                pass
            self.queue.put_nowait(coro)

    async def stop(self) -> None:
        self.worker_task.cancel()
        try:
            await self.worker_task
        except asyncio.CancelledError:
            pass


chat_pipelines: Dict[int, ChatPipeline] = {}
pipeline_lock = asyncio.Lock()


async def get_chat_pipeline(chat_id: int, bot: Bot) -> ChatPipeline:
    async with pipeline_lock:
        if chat_id not in chat_pipelines:
            chat_pipelines[chat_id] = ChatPipeline(chat_id, bot)
        return chat_pipelines[chat_id]


# ============================================================================
# GAME STATE MODELS & IN-MEMORY REGISTRY
# ============================================================================
@dataclass
class ActiveGame:
    chat_id: int
    turn_user_id: int
    turn_user_name: str
    current_word: str
    word_pool: List[str]
    pool_index: int = 0
    words_changed_count: int = 0
    message_id: Optional[int] = None
    last_activity: float = field(default_factory=time.monotonic)
    lock: asyncio.Lock = field(default_factory=asyncio.Lock)


# Fast in-memory lookup for active games
active_games: Dict[int, ActiveGame] = {}
active_games_lock = asyncio.Lock()


def get_random_word_pool() -> List[str]:
    """Selects up to 50 unique words from wr.py and randomizes their order."""
    pool_size = min(len(wr.WORDS), MAX_WORD_CYCLE_POOL)
    selected = random.sample(wr.WORDS, pool_size)
    random.shuffle(selected)
    return selected


# ============================================================================
# HELPER UTILITIES
# ============================================================================
def mention_user_html(user_id: int, name: str, bold: bool = False) -> str:
    escaped_name = html.escape(name)
    if bold:
        return f'<a href="tg://user?id={user_id}"><b>{escaped_name}</b></a>'
    return f'<a href="tg://user?id={user_id}">{escaped_name}</a>'


async def check_admin(chat_id: int, user_id: int, bot: Bot) -> bool:
    """Checks if a user is chat admin with a 300s TTL cache to prevent API floods."""
    cached = admin_cache.get((chat_id, user_id))
    now = time.monotonic()
    if cached is not None:
        is_adm, timestamp = cached
        if now - timestamp < ADMIN_CACHE_TTL:
            return is_adm

    try:
        member = await bot.get_chat_member(chat_id, user_id)
        is_adm = member.status in ("creator", "administrator")
        admin_cache.set((chat_id, user_id), (is_adm, now))
        return is_adm
    except Exception:
        return False


def get_game_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="See the word", callback_data="game:see"),
                InlineKeyboardButton(text="Next", callback_data="game:next"),
                InlineKeyboardButton(text="Cancel", callback_data="game:cancel"),
            ]
        ]
    )


def get_new_game_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="Start new game 🎮", callback_data="game:start_new")
            ]
        ]
    )


# ============================================================================
# SUBSYSTEM 5: SECURITY & ANTI-SPAM MIDDLEWARES
# ============================================================================
class SecurityAndMaintenanceMiddleware(BaseMiddleware):
    """Instantly drops requests from banned entities or during maintenance."""
    async def __call__(
        self,
        handler: Callable[[types.TelegramObject, Dict[str, Any]], Any],
        event: types.TelegramObject,
        data: Dict[str, Any]
    ) -> Any:
        user = data.get("event_from_user")
        chat = data.get("event_chat")

        if user and user.id in BANNED_USERS:
            return
        if chat and chat.id in BANNED_CHATS:
            return

        if MAINTENANCE_MODE:
            if user and user.id != OWNER_ID:
                if isinstance(event, Message) and event.text and event.text.startswith("/"):
                    await event.answer("🔧 Bot is under maintenance. Please check back later.")
                return

        return await handler(event, data)


class IgnoreInactiveGroupMessagesMiddleware(BaseMiddleware):
    """
    Blueprint Phase 2 Compliance:
    Completely ignores regular group text messages when no game is active.
    Commands are permitted; non-command messages are rejected in O(1) time.
    """
    async def __call__(
        self,
        handler: Callable[[types.TelegramObject, Dict[str, Any]], Any],
        event: types.TelegramObject,
        data: Dict[str, Any]
    ) -> Any:
        if isinstance(event, Message):
            if event.chat.type in ("group", "supergroup"):
                is_command = event.text and event.text.startswith("/")
                if not is_command and event.chat.id not in active_games:
                    # Drop silently to conserve memory and CPU
                    return

        return await handler(event, data)


# ============================================================================
# DISPATCHER SETUP & ROUTERS
# ============================================================================
session = RateLimitedSession()
bot = Bot(
    token=BOT_TOKEN,
    session=session,
    default=DefaultBotProperties(parse_mode=ParseMode.HTML)
)
dp = Dispatcher()

# Register Middlewares
dp.message.outer_middleware(SecurityAndMaintenanceMiddleware())
dp.callback_query.outer_middleware(SecurityAndMaintenanceMiddleware())
dp.message.middleware(IgnoreInactiveGroupMessagesMiddleware())


# ============================================================================
# PHASE 1 & 2: GAME CORE HANDLERS
# ============================================================================
async def start_game_core(chat_id: int, user_id: int, user_name: str, message_to_reply: Optional[Message] = None) -> None:
    """Atomic race-condition free starter for /game and 'Start new game 🎮' button."""
    async with active_games_lock:
        if chat_id in active_games:
            return

        pool = get_random_word_pool()
        current_word = pool[0]

        game = ActiveGame(
            chat_id=chat_id,
            turn_user_id=user_id,
            turn_user_name=user_name,
            current_word=current_word,
            word_pool=pool,
            pool_index=0,
            words_changed_count=0
        )
        active_games[chat_id] = game

    user_mention = mention_user_html(user_id, user_name, bold=False)
    text = f"{user_mention} is explaining the word"
    kb = get_game_keyboard()

    pipeline = await get_chat_pipeline(chat_id, bot)
    if message_to_reply:
        pipeline.enqueue(message_to_reply.answer(text, reply_markup=kb))
    else:
        pipeline.enqueue(bot.send_message(chat_id, text, reply_markup=kb))


@dp.message(Command("game"))
async def handle_game_command(message: Message) -> None:
    """Starts the game if not already running."""
    if message.chat.type not in ("group", "supergroup"):
        await message.answer("This game can only be played in group chats!")
        return

    # First player starts game; others ignored if active
    if message.chat.id in active_games:
        return

    await start_game_core(
        chat_id=message.chat.id,
        user_id=message.from_user.id,
        user_name=message.from_user.first_name,
        message_to_reply=message
    )


@dp.callback_query(F.data == "game:start_new")
async def handle_start_new_game_button(callback: CallbackQuery) -> None:
    """Handles 'Start new game 🎮' button atomically."""
    chat_id = callback.message.chat.id
    user = callback.from_user

    # Atomic start check
    if chat_id in active_games:
        await callback.answer("A game is already running!", show_alert=False, cache_time=5)
        return

    await callback.answer()
    await start_game_core(chat_id, user.id, user.first_name, callback.message)


@dp.callback_query(F.data == "game:see")
async def handle_see_word(callback: CallbackQuery) -> None:
    """Shows word to turn player; cached reject alert to others."""
    chat_id = callback.message.chat.id
    user_id = callback.from_user.id
    game = active_games.get(chat_id)

    if not game:
        await callback.answer("This game has ended.", show_alert=True, cache_time=10)
        return

    if user_id != game.turn_user_id:
        # Blueprint: Alert popup saved in local telegram servers via cache_time for light speed response
        await callback.answer("It's not your turn!", show_alert=True, cache_time=10)
        return

    game.last_activity = time.monotonic()
    await callback.answer(
        f"Your word: {game.current_word}\nExplain about it in the chat!",
        show_alert=True
    )


@dp.callback_query(F.data == "game:next")
async def handle_next_word(callback: CallbackQuery) -> None:
    """Changes word with 50-word bounded cycling and -10 coin penalty."""
    chat_id = callback.message.chat.id
    user = callback.from_user
    game = active_games.get(chat_id)

    if not game:
        await callback.answer("This game has ended.", show_alert=True, cache_time=10)
        return

    if user.id != game.turn_user_id:
        await callback.answer("It's not your turn!", show_alert=True, cache_time=10)
        return

    async with game.lock:
        old_word = game.current_word
        game.words_changed_count += 1

        # Cycle management: reuse same 50 words in shuffled order if pool is exhausted
        game.pool_index += 1
        if game.pool_index >= len(game.word_pool):
            random.shuffle(game.word_pool)
            game.pool_index = 0

        game.current_word = game.word_pool[game.pool_index]
        game.last_activity = time.monotonic()

    # Show new word alert to turn user
    await callback.answer(
        f"Your word: {game.current_word}\nExplain about it in the chat!",
        show_alert=True
    )

    # Deduct 10 coins
    await db.buffer_score_delta(user.id, user.first_name, -WORD_CHANGE_PENALTY, 0)

    # Announce in group
    user_mention = mention_user_html(user.id, user.first_name, bold=False)
    group_msg = (
        f"{user_mention} changed the word! \n"
        f"-10 coins\n"
        f"Their word was: {old_word}"
    )

    pipeline = await get_chat_pipeline(chat_id, bot)
    pipeline.enqueue(callback.message.answer(group_msg))


@dp.callback_query(F.data == "game:cancel")
async def handle_cancel_game(callback: CallbackQuery) -> None:
    """Stops the game if clicked by turn user or chat admin."""
    chat_id = callback.message.chat.id
    user = callback.from_user
    game = active_games.get(chat_id)

    if not game:
        await callback.answer("This game has ended.", show_alert=True, cache_time=10)
        return

    is_turn_user = (user.id == game.turn_user_id)
    is_adm = await check_admin(chat_id, user.id, bot)

    if not (is_turn_user or is_adm):
        await callback.answer("It's not your turn!", show_alert=True, cache_time=10)
        return

    async with active_games_lock:
        active_games.pop(chat_id, None)

    await callback.answer()
    user_mention = mention_user_html(user.id, user.first_name, bold=False)
    stop_msg = f"The game was stopped by {user_mention}"

    pipeline = await get_chat_pipeline(chat_id, bot)
    pipeline.enqueue(callback.message.answer(stop_msg))


@dp.message(F.text)
async def handle_group_text_guess(message: Message) -> None:
    """
    Blueprint Phase 2 Compliance:
    Evaluates guess if chat has active game.
    Exact case-insensitive match permitted, but strictly rejects leading/trailing spaces.
    """
    chat_id = message.chat.id
    game = active_games.get(chat_id)
    if not game:
        return

    # Turn user cannot claim points by guessing their own word
    if message.from_user.id == game.turn_user_id:
        return

    raw_text = message.text

    # Blueprint: Strictly reject words with leading/trailing spaces
    if raw_text.startswith(" ") or raw_text.endswith(" "):
        return

    if raw_text.lower() == game.current_word.lower():
        # Correct answer! Terminate current game state atomically
        async with active_games_lock:
            if chat_id not in active_games:
                return
            found_word = game.current_word
            active_games.pop(chat_id, None)

        user = message.from_user
        # Reward 10 coins and record word found
        await db.buffer_score_delta(user.id, user.first_name, WORD_FOUND_REWARD, 1)

        # Message format: Player name in blue and bold, word in bold
        user_mention_bold = mention_user_html(user.id, user.first_name, bold=True)
        winner_text = (
            f"{user_mention_bold} found the word!\n"
            f"Word: <b>{html.escape(found_word)}</b>\n\n"
            f"+10 coins 🏆"
        )
        kb = get_new_game_keyboard()

        pipeline = await get_chat_pipeline(chat_id, bot)
        pipeline.enqueue(message.answer(winner_text, reply_markup=kb))


# ============================================================================
# PHASE 3: PROFILE & LEADERBOARD COMMANDS
# ============================================================================
@dp.message(Command("profile"))
async def handle_profile_command(message: Message) -> None:
    """Displays user's score, words found, and global rank."""
    user = message.from_user
    cd_key = (message.chat.id, user.id, "profile")
    now = time.monotonic()
    last_call = cooldown_cache.get(cd_key)
    if last_call and now - last_call < COMMAND_COOLDOWN_SEC:
        return
    cooldown_cache.set(cd_key, now)

    score, words_found, rank = await db.get_user_profile(user.id, user.first_name)
    user_mention = mention_user_html(user.id, user.first_name, bold=False)

    text = (
        f"Player: {user_mention}\n"
        f"Score: {score}\n"
        f"Words found: {words_found}\n\n"
        f"Global rank: {rank}"
    )

    pipeline = await get_chat_pipeline(message.chat.id, bot)
    pipeline.enqueue(message.answer(text))


@dp.message(Command("leaderboard"))
async def handle_leaderboard_command(message: Message) -> None:
    """Displays global top 10 leaderboard."""
    cd_key = (message.chat.id, message.from_user.id, "leaderboard")
    now = time.monotonic()
    last_call = cooldown_cache.get(cd_key)
    if last_call and now - last_call < COMMAND_COOLDOWN_SEC:
        return
    cooldown_cache.set(cd_key, now)

    top_players = await db.get_leaderboard()
    if not top_players:
        text = "Global leaderboard\n\nNo records yet!"
    else:
        lines = ["Global leaderboard\n"]
        for idx, (p_name, p_score) in enumerate(top_players, start=1):
            lines.append(f"Player {idx}: {p_score} ({html.escape(p_name)})")
        text = "\n".join(lines)

    pipeline = await get_chat_pipeline(message.chat.id, bot)
    pipeline.enqueue(message.answer(text))


# ============================================================================
# SUBSYSTEM 4: GLOBAL INACTIVITY TICKER & CLEANUP LOOPS
# ============================================================================
async def global_ticker_loop() -> None:
    """Single global loop to monitor game timeouts and purge idle chat queues."""
    while True:
        try:
            await asyncio.sleep(2.0)
            now = time.monotonic()

            # 1. Check for expired active games
            timed_out_games: List[int] = []
            async with active_games_lock:
                for cid, g in active_games.items():
                    if now - g.last_activity > GAME_INACTIVITY_TIMEOUT:
                        timed_out_games.append(cid)
                for cid in timed_out_games:
                    active_games.pop(cid, None)

            for cid in timed_out_games:
                pipeline = await get_chat_pipeline(cid, bot)
                pipeline.enqueue(bot.send_message(cid, "⏳ The game was stopped due to inactivity."))

            # 2. Cleanup idle chat pipelines (> 60 seconds inactive)
            async with pipeline_lock:
                idle_cids = [
                    cid for cid, p in chat_pipelines.items()
                    if p.queue.empty() and (now - p.last_active > 60.0)
                ]
                for cid in idle_cids:
                    p = chat_pipelines.pop(cid)
                    await p.stop()

        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"Error in global ticker: {e}")


async def batch_score_flush_loop() -> None:
    """Periodic task syncing buffered memory scores to SQLite every 15 seconds."""
    while True:
        try:
            await asyncio.sleep(15.0)
            await db.flush_scores()
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"Error in score flush loop: {e}")


# ============================================================================
# SUBSYSTEM 6: GRACEFUL SHUTDOWN & APPLICATION LIFECYCLE
# ============================================================================
async def main() -> None:
    logger.info("Starting Word Guess Mania bot engine...")
    await db.init()

    # Launch background workers
    ticker_task = asyncio.create_task(global_ticker_loop())
    flush_task = asyncio.create_task(batch_score_flush_loop())

    # Graceful shutdown handler
    loop = asyncio.get_running_loop()
    stop_event = asyncio.Event()

    def _signal_handler() -> None:
        logger.info("Shutdown signal received.")
        stop_event.set()

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, _signal_handler)
        except NotImplementedError:
            pass

    try:
        # Start polling while dropping pending updates to prevent backlog flooding
        await bot.delete_webhook(drop_pending_updates=True)
        polling_task = asyncio.create_task(dp.start_polling(bot))

        # Wait until termination signal
        await stop_event.wait()
    finally:
        logger.info("Executing graceful shutdown...")
        polling_task.cancel()
        ticker_task.cancel()
        flush_task.cancel()

        # Drain chat pipelines
        async with pipeline_lock:
            for p in chat_pipelines.values():
                await p.stop()
            chat_pipelines.clear()

        # Flush remaining scores to disk and close DB
        await db.close()

        # Close bot network session
        await bot.session.close()

        # Stop queue logger
        queue_listener.stop()
        logger.info("Bot stopped cleanly.")


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        pass

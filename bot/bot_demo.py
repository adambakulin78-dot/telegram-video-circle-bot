"""Кружок-бот: превращает любое видео в «кружочек» (video note) Telegram.

Монетизация: 3 бесплатных кружка в день, безлимит — подписка за Telegram Stars.
Что умеет (2026-10-20): видео / ссылка (TikTok, VK, YouTube…) / фото / музыка → кружок; музыка и надпись поверх кружка;
кружок → обычное видео (сохранить в галерею) и голосовое; HD 640 без метки для платных.
"""
import asyncio
import html
import logging
import math
import os
import re
import sqlite3
import sys
import tempfile
import textwrap
import time
from collections import defaultdict
from contextlib import contextmanager
from datetime import date
from pathlib import Path
from urllib.parse import quote

from aiogram import Bot, Dispatcher, F
from aiogram.exceptions import TelegramForbiddenError
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    BotCommand,
    CallbackQuery,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    LabeledPrice,
    Message,
    PreCheckoutQuery,
)
from dotenv import load_dotenv

load_dotenv()

BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_ID = int(os.getenv("ADMIN_ID", "0"))
FREE_PER_DAY = int(os.getenv("FREE_PER_DAY", "3"))
PREMIUM_PRICE_STARS = int(os.getenv("PREMIUM_PRICE_STARS", "75"))
PREMIUM_DAYS = int(os.getenv("PREMIUM_DAYS", "30"))
REF_BONUS = int(os.getenv("REF_BONUS", "5"))  # бонусных кружков за приглашённого друга
# лестница за друзей, которые сделали хотя бы один кружок: (сколько друзей, дней безлимита HD)
LADDER = [(3, 7), (10, 30)]
# тарифы: ключ -> (название, звёзд, дней безлимита, бонусных кружков)
PLANS = {
    "pack10": ("10 HD-кружков без метки", 15, 0, 10),
    "week": ("Безлимит HD без метки, 7 дней", 25, 7, 0),
    "month": (f"Безлимит HD без метки, {PREMIUM_DAYS} дней", PREMIUM_PRICE_STARS, PREMIUM_DAYS, 0),
}
REMIND_EVERY = 3 * 86400  # напоминание о новых бесплатных кружках — не чаще раза в 3 дня
FFMPEG = os.getenv("FFMPEG", "ffmpeg")
FFPROBE = os.getenv("FFPROBE", "ffprobe")
PART_SEC = 60  # максимальная длина одного кружка
MAX_PARTS = 10  # длинное видео режем максимум на 10 кружков
PHOTO_SEC = 8  # длина кружка из фото без музыки
BOT_USERNAME = os.getenv("BOT_USERNAME", "krugi_video_bot")
CHECKOUT_NUDGE_SEC = 15 * 60  # через сколько после неоплаченного счёта подсказать, как купить звёзды
CLEAN1_PRICE = int(os.getenv("CLEAN1_PRICE", "5"))  # «этот кружок без метки» — покупка в один тап
SUB_BONUS = int(os.getenv("SUB_BONUS", "3"))  # разовый бонус за подписку на канал
CHANNEL = os.getenv("CHANNEL", "fishkitg_ru")  # канал «Фишки Telegram» — зовём туда мягко, без обязательной подписки
DB_PATH = Path(os.getenv("DB_PATH", "bot.db"))
# свой сервер Bot API (telegram-bot-api) снимает лимит 20 МБ — до 2 ГБ; без него работаем через api.telegram.org
API_SERVER = os.getenv("TELEGRAM_API_SERVER", "")
MAX_FILE_MB = int(os.getenv("MAX_FILE_MB", "2000" if API_SERVER else "20"))
LINK_MAX_MB = int(os.getenv("LINK_MAX_MB", "100"))  # видео по ссылке — не больше
EXAMPLE = Path(__file__).with_name("example.mp4")  # пример кружка для новичков
WATERMARK = Path(__file__).with_name("watermark.png")  # метка @krugi_video_bot на бесплатных кружках
FONT = os.getenv("FONT") or next(
    (p for p in ["/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "C:/Windows/Fonts/arialbd.ttf"] if Path(p).exists()), ""
)
CACHE = Path(os.getenv("CACHE_DIR", str(Path(tempfile.gettempdir()) / "kruzhok_cache")))
CACHE_TTL = 3 * 3600  # исходники держим 3 часа — для переделок без повторного скачивания
CACHE_MAX = 1500 * 1024 * 1024
FOLLOW_SEC = 30 * 60  # музыку/надпись после кружка накладываем на него, если прошло меньше 30 минут
_example_file_id: str | None = None  # после первой отправки шлём по file_id, без повторной загрузки

logging.basicConfig(level=logging.INFO)
dp = Dispatcher()
_ffmpeg_slots = asyncio.Semaphore(2)  # не больше 2 конвертаций одновременно
_locks: dict[int, asyncio.Lock] = defaultdict(asyncio.Lock)  # видео одного человека — строго по очереди (и честный лимит)
# задания для переделок: (чат, id сообщения с кнопками) -> что и как рендерили
_jobs: dict[tuple[int, int], dict] = {}
_last: dict[int, tuple[tuple[int, int], float]] = {}  # пользователь -> (ключ последнего кружка, когда)
_await_text: dict[int, tuple[int, int]] = {}  # ждём от пользователя текст надписи для кружка
_broadcast: dict[int, tuple[str, str]] = {}  # админ -> (текст рассылки, условие на язык), ждущий подтверждения
_codes: dict[int, str] = {}  # пользователь -> language_code из Telegram (для выбора языка)
RU_CODES = {"ru", "uk", "be", "kk", "ky", "uz", "tg"}  # кому по умолчанию отвечаем по-русски
PLANS_EN = {"pack10": "10 HD circles, no watermark", "week": "Unlimited HD, no watermark, 7 days",
            "month": f"Unlimited HD, no watermark, {PREMIUM_DAYS} days"}


def detect(code: str | None) -> str:
    """Язык по language_code: СНГ — русский, остальные — английский; неизвестно — русский."""
    if not code:
        return "ru"
    return "ru" if code.split("-")[0].lower() in RU_CODES else "en"


def lg(user_id: int) -> str:
    """Язык пользователя: выбранный в /lang или по настройкам Telegram."""
    try:
        with db() as c:
            row = c.execute("SELECT lang FROM users WHERE id=?", (user_id,)).fetchone()
        if row and row["lang"]:
            return row["lang"]
    except Exception:
        pass
    return detect(_codes.get(user_id))


def tx(lang: str, ru: str, en: str) -> str:
    return en if lang == "en" else ru


def nk(lang: str, n: int) -> str:
    """2 кружка / 2 circles."""
    return f"{n} circle{'' if n == 1 else 's'}" if lang == "en" else kruzhkov(n)


def plan_name(key: str, lang: str) -> str:
    return PLANS_EN[key] if lang == "en" else PLANS[key][0]


def fmt_date(ts: int | float) -> str:
    return time.strftime("%d.%m.%Y", time.localtime(ts))


# ---------- база данных ----------

@contextmanager
def db():
    try:
        conn = sqlite3.connect(DB_PATH)
    except sqlite3.OperationalError:
        # 27.10 бот сутки «жил» без базы и молчал — пусть лучше упадёт, systemd (Restart=always) поднимет заново
        logging.exception("база не открывается — перезапуск")
        os._exit(1)
    conn.row_factory = sqlite3.Row
    try:
        with conn:  # commit / rollback, как раньше
            yield conn
    finally:
        conn.close()  # sqlite3 сам соединение не закрывает — копились открытые файлы


def init_db() -> None:
    with db() as c:
        c.execute(
            """CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY,
                joined INTEGER NOT NULL,
                referrer INTEGER,
                premium_until INTEGER NOT NULL DEFAULT 0,
                bonus INTEGER NOT NULL DEFAULT 0,
                used_day TEXT NOT NULL DEFAULT '',
                used_count INTEGER NOT NULL DEFAULT 0,
                total INTEGER NOT NULL DEFAULT 0
            )"""
        )
        c.execute(
            """CREATE TABLE IF NOT EXISTS payments (
                charge_id TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                stars INTEGER NOT NULL,
                ts INTEGER NOT NULL
            )"""
        )
        # какими фишками пользуются — чтобы решать, что развивать
        c.execute("CREATE TABLE IF NOT EXISTS events (ts INTEGER NOT NULL, user_id INTEGER NOT NULL, kind TEXT NOT NULL)")
        cols = [r[1] for r in c.execute("PRAGMA table_info(users)")]
        if "source" not in cols:  # миграция: откуда пришёл пользователь
            c.execute("ALTER TABLE users ADD COLUMN source TEXT")
        # воронка и напоминания
        for col, ddl in [
            ("limit_day", "TEXT NOT NULL DEFAULT ''"),  # день, когда упёрся в лимит (сбрасывается после напоминания)
            ("hit_limit", "INTEGER NOT NULL DEFAULT 0"),  # хоть раз упирался в лимит
            ("invoices", "INTEGER NOT NULL DEFAULT 0"),  # сколько раз открывал оплату
            ("remind_off", "INTEGER NOT NULL DEFAULT 0"),
            ("last_remind", "INTEGER NOT NULL DEFAULT 0"),
            ("saw_plans", "INTEGER NOT NULL DEFAULT 0"),  # хоть раз видел тарифы (кнопка, подсказка или лимит)
            ("upsell_day", "TEXT NOT NULL DEFAULT ''"),  # день, когда показали подсказку «остался 1 кружок»
            ("sub_bonus", "INTEGER NOT NULL DEFAULT 0"),  # уже получил бонус за подписку на канал
            ("clean", "INTEGER NOT NULL DEFAULT 0"),  # сколько кружков осталось без метки (пакет, подписка)
            ("blocked", "INTEGER NOT NULL DEFAULT 0"),  # заблокировал бота (узнаём при рассылке/напоминании)
            ("ref_counted", "INTEGER NOT NULL DEFAULT 0"),  # приглашённый сделал кружок — засчитан пригласившему
            ("ref_tier", "INTEGER NOT NULL DEFAULT 0"),  # сколько ступеней лестницы за друзей уже выдано
            ("lang", "TEXT NOT NULL DEFAULT ''"),  # язык интерфейса: ru / en ('' — по настройкам Telegram)
            ("heard", "TEXT NOT NULL DEFAULT ''"),
            ("checkout_nudge", "INTEGER NOT NULL DEFAULT 0"),  # уже подсказали, как оплатить, после брошенного счёта  # откуда узнал: '' — не спрашивали, '?' — спросили, иначе ответ
            ("start_nudge", "INTEGER NOT NULL DEFAULT 0"),  # новичку без кружков уже напомнили «пришли видео»
        ]:
            if col not in cols:
                c.execute(f"ALTER TABLE users ADD COLUMN {col} {ddl}")
        # старые приглашённые, которые уже делали кружки, тоже идут в зачёт лестницы
        c.execute("UPDATE users SET ref_counted = 1 WHERE referrer IS NOT NULL AND total > 0 AND ref_counted = 0")


def log_event(user_id: int, kind: str) -> None:
    try:
        with db() as c:
            c.execute("INSERT INTO events VALUES (?, ?, ?)", (int(time.time()), user_id, kind))
    except Exception:
        logging.exception("log_event")


def get_user(user_id: int, referrer: int | None = None, source: str | None = None) -> sqlite3.Row:
    with db() as c:
        row = c.execute("SELECT * FROM users WHERE id=?", (user_id,)).fetchone()
        if row is None:
            if referrer == user_id:
                referrer = None
            c.execute(
                "INSERT INTO users (id, joined, referrer, source, lang) VALUES (?, ?, ?, ?, ?)",
                (user_id, int(time.time()), referrer, source or ("ref" if referrer else None),
                 detect(_codes.get(user_id)) if user_id in _codes else ""),
            )
            if referrer:
                c.execute("UPDATE users SET bonus = bonus + ? WHERE id=?", (REF_BONUS, referrer))
            row = c.execute("SELECT * FROM users WHERE id=?", (user_id,)).fetchone()
        elif row["blocked"]:
            c.execute("UPDATE users SET blocked = 0 WHERE id=?", (user_id,))  # снова пишет — значит разблокировал
        return row


def is_premium(u: sqlite3.Row) -> bool:
    return u["id"] == ADMIN_ID or u["premium_until"] > time.time()


def needs_mark(u: sqlite3.Row) -> bool:
    """Метка @krugi_video_bot — на бесплатных кружках; без неё — безлимит или кружки «без метки» в запасе."""
    return not is_premium(u) and u["clean"] <= 0


def use_clean(user_id: int) -> None:
    with db() as c:
        c.execute("UPDATE users SET clean = clean - 1 WHERE id=? AND clean > 0", (user_id,))


def left_today(u: sqlite3.Row) -> int:
    used = u["used_count"] if u["used_day"] == date.today().isoformat() else 0
    return max(FREE_PER_DAY - used, 0) + u["bonus"]


def consume(user_id: int) -> None:
    today = date.today().isoformat()
    with db() as c:
        u = c.execute("SELECT * FROM users WHERE id=?", (user_id,)).fetchone()
        used = u["used_count"] if u["used_day"] == today else 0
        if not is_premium(u) and used >= FREE_PER_DAY:
            c.execute("UPDATE users SET bonus = bonus - 1, total = total + 1 WHERE id=?", (user_id,))
        else:
            c.execute(
                "UPDATE users SET used_day=?, used_count=?, total = total + 1 WHERE id=?",
                (today, used + 1, user_id),
            )


def mark_limit(user_id: int) -> None:
    """Пользователь упёрся в лимит — для воронки и завтрашнего напоминания."""
    with db() as c:
        c.execute("UPDATE users SET limit_day=?, hit_limit=1, saw_plans=1 WHERE id=?", (date.today().isoformat(), user_id))


def free_left(u: sqlite3.Row) -> int:
    used = u["used_count"] if u["used_day"] == date.today().isoformat() else 0
    return max(FREE_PER_DAY - used, 0)


def need_upsell(u: sqlite3.Row) -> bool:
    """Мягкая подсказка с тарифами: раз в день, когда остался последний бесплатный кружок."""
    today = date.today().isoformat()
    if is_premium(u) or u["upsell_day"] == today or free_left(u) != 1 or u["bonus"] > 0:
        return False
    with db() as c:
        c.execute("UPDATE users SET upsell_day=?, saw_plans=1 WHERE id=?", (today, u["id"]))
    return True


def add_premium(user_id: int, charge_id: str, stars: int, days: int = PREMIUM_DAYS, bonus: int = 0) -> int:
    with db() as c:
        u = c.execute("SELECT premium_until FROM users WHERE id=?", (user_id,)).fetchone()
        until = u["premium_until"]
        if days:
            until = max(u["premium_until"], int(time.time())) + days * 86400
        c.execute("UPDATE users SET premium_until=?, bonus = bonus + ? WHERE id=?", (until, bonus, user_id))
        c.execute(
            "INSERT OR IGNORE INTO payments VALUES (?, ?, ?, ?)",
            (charge_id, user_id, stars, int(time.time())),
        )
        return until


def grant_days(user_id: int, days: int) -> int:
    """Безлимит в подарок (лестница за друзей, /gift) — без записи в платежи."""
    with db() as c:
        u = c.execute("SELECT premium_until FROM users WHERE id=?", (user_id,)).fetchone()
        until = max(u["premium_until"], int(time.time())) + days * 86400
        c.execute("UPDATE users SET premium_until=? WHERE id=?", (until, user_id))
        return until


def active_refs(user_id: int) -> int:
    """Сколько приглашённых этим человеком уже сделали хотя бы один кружок."""
    with db() as c:
        return c.execute("SELECT COUNT(*) FROM users WHERE referrer=? AND ref_counted=1", (user_id,)).fetchone()[0]


def ladder_progress(user_id: int) -> str:
    n = active_refs(user_id)
    lang = lg(user_id)
    nxt = next(((need, days) for need, days in LADDER if n < need), None)
    if not nxt:
        return tx(lang, f"Друзей с кружками: {n} — ты прошёл всю лестницу, спасибо! 🏆",
                  f"Friends making circles: {n} — you've completed the whole ladder, thank you! 🏆")
    need, days = nxt
    return tx(lang, f"Друзей с кружками: <b>{n} из {need}</b> до безлимита HD на {days} дней",
              f"Friends making circles: <b>{n} of {need}</b> to unlimited HD for {days} days")


async def check_ladder(bot: Bot, user_id: int) -> None:
    """Выдаёт ступени лестницы, до которых человек дорос (в том числе задним числом)."""
    n = active_refs(user_id)
    with db() as c:
        row = c.execute("SELECT ref_tier FROM users WHERE id=?", (user_id,)).fetchone()
    if not row:
        return
    for i, (need, days) in enumerate(LADDER):
        if i < row["ref_tier"] or n < need:
            continue
        with db() as c:
            done = c.execute("UPDATE users SET ref_tier=? WHERE id=? AND ref_tier=?", (i + 1, user_id, i)).rowcount
        if not done:
            return
        until = grant_days(user_id, days)
        log_event(user_id, f"ladder{need}")
        try:
            lang = lg(user_id)
            await bot.send_message(
                user_id,
                tx(lang, f"🏆 Твои друзья ({n}) уже делают кружки — дарю <b>безлимит HD без метки на {days} дней</b> "
                         f"(до {fmt_date(until)})!",
                   f"🏆 Your friends ({n}) are making circles — here's <b>unlimited HD with no watermark for {days} days</b> "
                   f"(until {fmt_date(until)})!") + f"\n{ladder_progress(user_id)}",
            )
        except Exception:
            pass
        if ADMIN_ID:
            await bot.send_message(ADMIN_ID, f"🏆 Лестница: {user_id} привёл {n} активных друзей → +{days} дн. безлимита")


async def count_ref(bot: Bot, user_id: int) -> None:
    """После кружка: если это приглашённый и его ещё не засчитали — засчитываем пригласившему."""
    with db() as c:
        u = c.execute("SELECT referrer, ref_counted FROM users WHERE id=?", (user_id,)).fetchone()
        if not u or not u["referrer"] or u["ref_counted"]:
            return
        c.execute("UPDATE users SET ref_counted=1 WHERE id=?", (user_id,))
    ref = u["referrer"]
    try:
        await bot.send_message(ref, tx(lg(ref), "🎉 Друг, которого ты пригласил, сделал первый кружок!",
                                       "🎉 A friend you invited just made their first circle!") + f"\n{ladder_progress(ref)}")
    except Exception:
        pass
    await check_ladder(bot, ref)


# ---------- кэш исходников ----------

def cache_file(suffix: str) -> Path:
    """Новый файл в кэше; заодно чистим старое (по времени и по общему размеру)."""
    CACHE.mkdir(parents=True, exist_ok=True)
    try:
        files = sorted((p for p in CACHE.iterdir() if p.is_file()), key=lambda p: p.stat().st_mtime)
        total = sum(p.stat().st_size for p in files)
        now = time.time()
        for p in files:
            st = p.stat()
            if now - st.st_mtime > CACHE_TTL or total > CACHE_MAX:
                total -= st.st_size
                p.unlink(missing_ok=True)
    except Exception:
        logging.exception("cache cleanup")
    return CACHE / f"{time.time_ns()}{suffix}"


def remember(key: tuple[int, int], job: dict, user_id: int) -> None:
    _jobs[key] = job
    _last[user_id] = (key, time.time())
    while len(_jobs) > 2000:
        _jobs.pop(next(iter(_jobs)))


def last_job(user_id: int) -> tuple[tuple[int, int], dict] | None:
    """Последний одиночный кружок пользователя, если он свежий и исходник ещё на диске."""
    item = _last.get(user_id)
    if not item or time.time() - item[1] > FOLLOW_SEC or item[0] not in _jobs:
        return None
    job = _jobs[item[0]]
    if job.get("src") and not Path(job["src"]).exists():
        return None
    return item[0], job


# ---------- конвертация ----------

POS = {"top": 0.0, "center": 0.5, "bottom": 1.0}  # какую часть кадра оставить

# эффекты для кружка (кнопка «🎭 Эффекты»): переделка бесплатная, как сдвиг кадра
VOICE_FX = {  # меняют только звук; длительность сохраняется (asetrate меняет и темп — atempo возвращает его)
    "chipmunk": "aresample=44100,asetrate=44100*1.45,aresample=44100,atempo=0.69",
    "deep": "aresample=44100,asetrate=44100*0.75,aresample=44100,atempo=1.3333",
    "robot": "aresample=44100,afftfilt=real='hypot(re,im)*sin(0)':imag='hypot(re,im)*cos(0)':win_size=512:overlap=0.75,volume=14dB,alimiter=limit=0.9",  # afftfilt глушит звук на ~15 дБ
}
REVERSE_SEC = 10  # reverse держит все кадры в памяти — на маленьком VPS не больше 10 секунд
BOOMERANG_SEC = 2.5  # кусок для «бумеранга»: вперёд-назад, два раза
HALLOWEEN_UNTIL = date(2026, 11, 2)  # кнопка 🎃 видна до этого дня
FX_NAMES = {
    "chipmunk": ("🐿 Бурундук", "🐿 Chipmunk"), "deep": ("👹 Низкий голос", "👹 Deep voice"),
    "robot": ("🤖 Робот", "🤖 Robot"), "reverse": ("⏪ Задом наперёд", "⏪ Reverse"),
    "boomerang": ("🔁 Бумеранг", "🔁 Boomerang"), "bw": ("🎞 Ч/б кино", "🎞 B&W film"), "vhs": ("📼 VHS-кассета", "📼 VHS tape"),
    "halloween": ("🎃 Хэллоуин", "🎃 Halloween"),
}


def halloween_on() -> bool:
    return date.today() < HALLOWEEN_UNTIL


def _esc(path: str | Path) -> str:
    """Путь для опций фильтров ffmpeg (двоеточие диска в Windows и т.п.)."""
    return str(path).replace("\\", "/").replace(":", "\\:").replace("'", "\\'")


def _crop(pos: str) -> str:
    p = POS.get(pos, 0.5)
    return f"crop='min(iw,ih)':'min(iw,ih)':'(iw-min(iw,ih))*{p}':'(ih-min(iw,ih))*{p}'"


async def run_ff(cmd: list[str]) -> None:
    async with _ffmpeg_slots:
        proc = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE)
        _, err = await proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(err.decode(errors="ignore")[-800:])


async def has_audio(src: Path) -> bool:
    proc = await asyncio.create_subprocess_exec(
        FFPROBE, "-v", "error", "-select_streams", "a", "-show_entries", "stream=index", "-of", "csv=p=0", str(src),
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL,
    )
    out, _ = await proc.communicate()
    return bool(out.strip())


async def render(job: dict, dst: Path, mark: bool, hd: bool) -> None:
    """Собирает кружок по заданию.

    job: kind = video | photo | music; src — видео/фото/обложка (у music может не быть); start/length — кусок;
    pos — какую часть кадра брать; text — надпись; audio/audio_start — музыка; mix — смешать с родным звуком.
    """
    S = 640 if hd else 512
    kind, length = job["kind"], max(0.5, min(job["length"], PART_SEC))
    fx = job.get("fx") or ""
    boom = min(BOOMERANG_SEC, length)
    if fx == "reverse":
        length = min(length, REVERSE_SEC)
    elif fx == "boomerang":
        length = boom * 4  # вперёд + назад, и ещё раз
    frames = int(length * 30)
    inp: list[str] = []
    fc: list[str] = []
    if kind == "video":
        inp += ["-ss", f"{job.get('start', 0):.2f}", "-i", str(job["src"])]
        fc.append(f"[0:v]{_crop(job.get('pos', 'center'))},scale={S}:{S}:flags=lanczos,fps=30,setsar=1[v0]")
    elif kind == "photo":
        inp += ["-loop", "1", "-framerate", "30", "-i", str(job["src"])]
        # медленный наезд (Ken Burns): из фото получается «живой» кружок
        fc.append(
            f"[0:v]{_crop(job.get('pos', 'center'))},scale={S * 2}:{S * 2}:flags=lanczos,"
            f"zoompan=z='1+0.15*on/{frames}':x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':d=1:s={S}x{S}:fps=30,setsar=1[v0]"
        )
    else:  # music: обложка (аватарка) крутится как пластинка
        if job.get("src"):
            inp += ["-loop", "1", "-framerate", "30", "-i", str(job["src"])]
            fc.append(f"[0:v]{_crop('center')},scale={S}:{S}:flags=lanczos,rotate='t*0.35':c=black,setsar=1[v0]")
        else:
            inp += ["-f", "lavfi", "-i", f"gradients=s={S}x{S}:c0=0x2f5bff:c1=0xff5a36:speed=0.015:r=30"]
            note = f",drawtext=fontfile='{_esc(FONT)}':text='♪':fontcolor=white@0.9:fontsize={S // 3}:x=(w-text_w)/2:y=(h-text_h)/2-{S // 10}" if FONT else ""
            fc.append(f"[0:v]setsar=1{note}[v0]")
    cur = "v0"
    if fx == "bw":
        fc.append(f"[{cur}]hue=s=0,eq=contrast=1.12[vf]")
        cur = "vf"
    elif fx == "vhs":
        # старая кассета: сдвиг цветов, шум, блеклые цвета и «► PLAY» с датой (внутри круга, края его не режут)
        osd = ""
        if FONT:
            common = f":fontfile='{_esc(FONT)}':fontcolor=white@0.9:fontsize={int(S * 0.06)}:shadowcolor=black@0.6:shadowx=2:shadowy=2"
            osd = (f",drawtext=text='► PLAY'{common}:x=(w-text_w)/2:y={int(S * 0.17)}"
                   f",drawtext=text='{date.today():%d.%m.%Y}'{common}:x=(w-text_w)/2:y=h-{int(S * 0.27)}")
        fc.append(f"[{cur}]rgbashift=rh={max(2, S // 128)}:bh=-{max(2, S // 128)},eq=saturation=0.75:contrast=1.15:gamma=1.05,"
                  f"noise=alls=12,gblur=sigma=0.6{osd}[vf]")  # шум без allf=t: меняющийся шум раздувает файл в разы
        cur = "vf"
    elif fx == "halloween":
        title = ""
        if FONT and job.get("fx_text"):
            title = (f",drawtext=fontfile='{_esc(FONT)}':text='{job['fx_text']}':fontcolor=0xff7a1a:fontsize={int(S * 0.08)}"
                     f":borderw={max(3, S // 110)}:bordercolor=black:x=(w-text_w)/2:y={int(S * 0.19)}")  # ниже — край круга не режет
        fc.append(f"[{cur}]colorbalance=rs=0.25:gs=-0.05:bs=-0.25:rm=0.15:bm=-0.1,eq=saturation=1.25:contrast=1.08,"
                  f"vignette=angle=PI/3.2{title}[vf]")
        cur = "vf"
    elif fx == "reverse":
        fc.append(f"[{cur}]trim=duration={length:.2f},setpts=PTS-STARTPTS,reverse[vf]")
        cur = "vf"
    elif fx == "boomerang":
        fc.append(f"[{cur}]trim=duration={boom:.2f},setpts=PTS-STARTPTS,split[bf][bb]")
        fc.append("[bb]reverse[br]")
        fc.append(f"[bf][br]concat=n=2:v=1:a=0,loop=loop=1:size={int(boom * 60)}:start=0,setpts=N/30/TB[vf]")
        cur = "vf"
    ai = None
    if job.get("audio"):
        ai = len([x for x in inp if x == "-i"])
        inp += ["-ss", f"{job.get('audio_start', 0):.2f}", "-i", str(job["audio"])]
    if kind == "music" and ai is not None:
        # волна звука поверх обложки
        fc.append(f"[{ai}:a]asplit=2[am][aw]")
        fc.append(f"[aw]showwaves=s={S}x{S // 5}:mode=cline:colors=white@0.8:rate=30,format=rgba[w]")
        fc.append(f"[{cur}][w]overlay=0:{int(S * 0.6)}[v1]")
        cur = "v1"
    text_file = None
    if job.get("text") and FONT:
        lines = textwrap.wrap(job["text"], 16)[:3] or [job["text"][:16]]
        text_file = dst.with_suffix(".txt")
        text_file.write_bytes("\n".join(lines).encode("utf-8"))  # без \r — иначе лишние пустые строки на Windows
        fs = int(S * (0.085 if len(lines) == 1 else 0.07))
        y = int(S * (0.6 if mark else 0.66))
        fc.append(
            f"[{cur}]drawtext=fontfile='{_esc(FONT)}':textfile='{_esc(text_file)}':fontcolor=white:fontsize={fs}"
            f":borderw={max(3, S // 120)}:bordercolor=black@0.85:line_spacing={S // 80}:text_align=C"
            f":x=(w-text_w)/2:y={y}-text_h/2[vt]"
        )
        cur = "vt"
    if mark and WATERMARK.exists():
        wi = len([x for x in inp if x == "-i"])
        inp += ["-i", str(WATERMARK)]
        fc.append(f"[{wi}:v]scale=iw*{S}/512:-1[wm]")
        fc.append(f"[{cur}][wm]overlay=(W-w)/2:H-h-{int(38 * S / 512)}[vm]")
        cur = "vm"
    fc.append(f"[{cur}]format=yuv420p[vout]")
    maps = ["-map", "[vout]"]
    if ai is not None:
        if kind == "video" and job.get("mix") and await has_audio(Path(job["src"])):
            fc.append(f"[0:a]volume=1.0[a0];[{ai}:a]volume=0.35[a1];[a0][a1]amix=inputs=2:duration=first:normalize=0[aout]")
            maps += ["-map", "[aout]"]
        elif kind == "music":
            maps += ["-map", "[am]"]
        else:
            maps += ["-map", f"{ai}:a"]
    elif kind == "video":
        maps += ["-map", "0:a?"]
    afx = VOICE_FX.get(fx) or (f"atrim=duration={length:.2f},asetpts=PTS-STARTPTS,areverse" if fx == "reverse" else "")
    if (afx or fx == "boomerang") and len(maps) > 2:
        spec = maps[3]
        if spec == "0:a?":
            label = "[0:a]" if await has_audio(Path(job["src"])) else ""
        else:
            label = spec if spec.startswith("[") else f"[{spec}]"
        maps = maps[:2]
        if label and fx == "boomerang":
            if spec.startswith("["):  # звук бумерангу не нужен, но выход фильтра нельзя оставить висеть
                fc.append(f"{label}anullsink")
        elif label:
            fc.append(f"{label}{afx}[afx]")
            maps += ["-map", "[afx]"]
    cmd = [
        FFMPEG, "-y", *inp, "-filter_complex", ";".join(fc), *maps, "-t", f"{length:.2f}",
        "-c:v", "libx264", "-preset", "veryfast", "-crf", "21" if hd else "24", "-pix_fmt", "yuv420p",
        "-c:a", "aac", "-b:a", "128k" if hd else "96k", "-ar", "44100", "-movflags", "+faststart", str(dst),
    ]
    try:
        await run_ff(cmd)
    finally:
        if text_file:
            text_file.unlink(missing_ok=True)


async def to_voice(src: Path, dst: Path, start: float, length: float) -> None:
    """Звук из видео/музыки → голосовое сообщение (OGG/Opus)."""
    await run_ff([
        FFMPEG, "-y", "-ss", f"{start:.2f}", "-i", str(src), "-t", f"{length:.2f}",
        "-vn", "-c:a", "libopus", "-b:a", "48k", "-ac", "1", str(dst),
    ])


async def probe_duration(src: Path) -> float:
    """Длительность файла в секундах (0, если не удалось узнать)."""
    proc = await asyncio.create_subprocess_exec(
        FFPROBE, "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", str(src),
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL,
    )
    out, _ = await proc.communicate()
    try:
        return float(out.decode().strip())
    except ValueError:
        return 0.0


async def probe_size(src: Path) -> tuple[int, int]:
    proc = await asyncio.create_subprocess_exec(
        FFPROBE, "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height", "-of", "csv=p=0", str(src),
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL,
    )
    out, _ = await proc.communicate()
    try:
        w, h = out.decode().strip().split(",")[:2]
        return int(w), int(h)
    except ValueError:
        return 0, 0


async def fetch_link(url: str) -> Path:
    """Скачивает видео по ссылке (TikTok, VK, YouTube Shorts, Rutube…) через yt-dlp."""
    dst = cache_file(".mp4")
    cmd = [
        sys.executable, "-m", "yt_dlp", "--no-playlist", "--no-warnings", "--quiet",
        "-f", "b[height<=720][ext=mp4]/bv*[height<=720]+ba/b[height<=720]/b",
        "--merge-output-format", "mp4", "--max-filesize", f"{LINK_MAX_MB}M",
        "--match-filter", "!is_live & duration <? 1200", "--socket-timeout", "20",
        "-o", str(dst), url,
    ]
    proc = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE)
    try:
        _, err = await asyncio.wait_for(proc.communicate(), timeout=150)
    except asyncio.TimeoutError:
        proc.kill()
        await proc.wait()
        raise RuntimeError("timeout")
    if not dst.exists():
        found = list(CACHE.glob(dst.stem + "*"))  # yt-dlp иногда сам ставит расширение
        if not found:
            raise RuntimeError(err.decode(errors="ignore")[-400:] or "no file")
        found[0].rename(dst)
    return dst


_TIME = r"(\d{1,2}:\d{2}(?::\d{2})?|\d+(?:[.,]\d+)?)"
_QUOTE = r"[«\"“„](.+?)[»\"”“]"


def _secs(t: str) -> float:
    parts = [float(x.replace(",", ".")) for x in t.split(":")]
    s = 0.0
    for x in parts:
        s = s * 60 + x
    return s


def parse_caption(text: str | None) -> tuple[float, float | None, str, str]:
    """Подпись к видео: «0:45», «0:45-1:30», «с 1:10», «верх», «низ», «лево», «право», "надпись в кавычках".

    Возвращает (начало, конец или None, положение кадра, надпись).
    """
    raw = text or ""
    q = re.search(_QUOTE, raw)
    label = q.group(1).strip()[:60] if q else ""
    t = re.sub(_QUOTE, " ", raw).lower()
    pos = "center"
    if re.search(r"верх|лев|top|left", t):
        pos = "top"
    elif re.search(r"низ|прав|bottom|right", t):
        pos = "bottom"
    start, end = 0.0, None
    # время с двоеточием ищем где угодно, голые числа («45», «30-50») — только если подпись из них и состоит,
    # чтобы «поздравление для 2 класса» не превратилось в «начать со 2-й секунды»
    has_colon = re.search(r"\d:\d{2}", t)
    clean = re.sub(r"верх\w*|низ\w*|лев\w*|прав\w*|top|bottom|left|right|сек\w*|микс\w*|mix|смеша\w*|\bс\b|\bот\b|\bдо\b|\bпо\b", " ", t)
    if has_colon or re.fullmatch(r"[\s\d.,:\-–—]+", clean or "-"):
        m = re.search(_TIME + r"\s*(?:[-–—]|\bдо\b|\bпо\b)\s*" + _TIME, t)
        if m:
            start, end = _secs(m.group(1)), _secs(m.group(2))
            if end <= start:
                end = None
        else:
            m = re.search(_TIME, t)
            if m:
                start = _secs(m.group(1))
    return start, end, pos, label


def kruzhkov(n: int) -> str:
    """2 кружка, 5 кружков, 21 кружок."""
    if n % 10 == 1 and n % 100 != 11:
        w = "кружок"
    elif 2 <= n % 10 <= 4 and not 12 <= n % 100 <= 14:
        w = "кружка"
    else:
        w = "кружков"
    return f"{n} {w}"


def share_btn(user_id: int) -> InlineKeyboardButton:
    """«Поделиться» открывает выбор чата в Telegram с готовым текстом и реф-ссылкой."""
    lang = lg(user_id)
    link = f"https://t.me/{BOT_USERNAME}?start=ref{user_id}"
    text = tx(lang, "Бот делает кружок из любого видео, фото или песни 🔵 Попробуй, 3 в день бесплатно",
              "This bot turns any video, photo or song into a Telegram video circle 🔵 3 a day free")
    return InlineKeyboardButton(
        text=tx(lang, f"📤 Позвать друга (+{kruzhkov(REF_BONUS)})", f"📤 Invite a friend (+{REF_BONUS} circles)"),
        url=f"https://t.me/share/url?url={quote(link)}&text={quote(text)}",
    )


def result_kb(job: dict, user_id: int, marked: bool) -> InlineKeyboardMarkup:
    """Кнопки под одиночным кружком: сдвиг кадра, надпись, музыка, голосовое."""
    rows = []
    lang = lg(user_id)
    if marked:
        rows.append([InlineKeyboardButton(text=tx(lang, f"✨ Этот кружок в HD без метки — {CLEAN1_PRICE} ⭐",
                                                  f"✨ This circle in HD, no watermark — {CLEAN1_PRICE} ⭐"), callback_data="clean1")])
    if job["kind"] in ("video", "photo"):
        if job.get("vertical", True):
            a, b = tx(lang, "⬆️ Верх", "⬆️ Up"), tx(lang, "⬇️ Низ", "⬇️ Down")
        else:
            a, b = tx(lang, "⬅️ Левее", "⬅️ Left"), tx(lang, "➡️ Правее", "➡️ Right")
        rows.append([
            InlineKeyboardButton(text=a, callback_data="pos:top"),
            InlineKeyboardButton(text=tx(lang, "⏺ Центр", "⏺ Center"), callback_data="pos:center"),
            InlineKeyboardButton(text=b, callback_data="pos:bottom"),
        ])
    rows.append([
        InlineKeyboardButton(text=tx(lang, "✏️ Надпись", "✏️ Text"), callback_data="text"),
        InlineKeyboardButton(text=tx(lang, "🎵 Музыка", "🎵 Music"), callback_data="music"),
        InlineKeyboardButton(text=tx(lang, "🎤 Голосовое", "🎤 Voice"), callback_data="voice"),
    ])
    fx_row = [InlineKeyboardButton(text=tx(lang, "🎭 Эффекты: голос, реверс, бумеранг", "🎭 Effects: voice, reverse, boomerang"),
                                   callback_data="fx")]
    if halloween_on():
        fx_row = [InlineKeyboardButton(text=tx(lang, "🎭 Эффекты", "🎭 Effects"), callback_data="fx"),
                  InlineKeyboardButton(text=FX_NAMES["halloween"][lang == "en"], callback_data="fx:halloween")]
    rows.append(fx_row)
    rows.append([share_btn(user_id)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def plans_btn(lang: str) -> InlineKeyboardButton:
    return InlineKeyboardButton(text=tx(lang, "✨ HD без метки и лимитов — тарифы", "✨ HD, no watermark, no limits — plans"),
                                callback_data="plans")


def sub_rows(u: sqlite3.Row) -> list[list[InlineKeyboardButton]]:
    """Кнопки канала: пока бонус не получен — «подпишись и забери +N», потом просто ссылка.
    Канал русскоязычный — англоязычным его не предлагаем."""
    lang = lg(u["id"])
    if lang == "en":
        return []
    if u["sub_bonus"]:
        return [[InlineKeyboardButton(text="📢 Канал: фишки Telegram", url=f"https://t.me/{CHANNEL}")]]
    return [
        [InlineKeyboardButton(text=f"📢 Подписаться на канал (+{kruzhkov(SUB_BONUS)})", url=f"https://t.me/{CHANNEL}")],
        [InlineKeyboardButton(text="✅ Я подписался — забрать бонус", callback_data="sub")],
    ]


def with_plans(kb: InlineKeyboardMarkup, u: sqlite3.Row) -> InlineKeyboardMarkup:
    """Кнопка тарифов под результатом — только для тех, у кого нет безлимита."""
    if is_premium(u):
        return kb
    return InlineKeyboardMarkup(inline_keyboard=kb.inline_keyboard + [[plans_btn(lg(u["id"]))]])


async def send_example(m: Message) -> None:
    """Показываем новичку готовый кружок, чтобы сразу было понятно, что он получит."""
    global _example_file_id
    if not _example_file_id and not EXAMPLE.exists():
        return
    try:
        sent = await m.answer_video_note(_example_file_id or FSInputFile(EXAMPLE), length=512)
        _example_file_id = sent.video_note.file_id
        await m.answer(tx(lg(m.from_user.id), "👆 Вот такой кружок получится из <b>твоего</b> видео",
                          "👆 This is what <b>your</b> video will look like as a circle"))
    except Exception:
        logging.exception("example failed")


def who(m: Message) -> str:
    """Кто написал — для уведомлений админу."""
    u = m.from_user
    name = html.escape(u.full_name or "")
    return f"{name} (@{u.username}, id {u.id})" if u.username else f"{name} (id {u.id})"


# ---------- клавиатуры и тексты ----------

def buy_kb(user_id: int | None = None, lang: str | None = None) -> InlineKeyboardMarkup:
    lang = lang or (lg(user_id) if user_id else "ru")
    rows = [
        [InlineKeyboardButton(text=f"⚡ {plan_name(key, lang)} — {stars} ⭐", callback_data=f"buy:{key}")]
        for key, (_, stars, _, _) in PLANS.items()
    ]
    if user_id:
        rows.append([share_btn(user_id)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def start_kb(u: sqlite3.Row, lang: str) -> InlineKeyboardMarkup:
    """Кнопки приветствия: самый продающий пакет, все тарифы, все фишки, канал (бонус)."""
    _, stars, _, _ = PLANS["pack10"]
    rows = [
        [InlineKeyboardButton(text=f"⚡ {plan_name('pack10', lang)} — {stars} ⭐", callback_data="buy:pack10")],
        [InlineKeyboardButton(text=tx(lang, "💎 Все тарифы", "💎 All plans"), callback_data="plans"),
         InlineKeyboardButton(text=tx(lang, "📖 Все фишки", "📖 All features"), callback_data="help")],
    ]
    return InlineKeyboardMarkup(inline_keyboard=rows + sub_rows(u))


def status_text(u: sqlite3.Row) -> str:
    lang = lg(u["id"])
    if u["id"] == ADMIN_ID:
        return tx(lang, "👑 Ты админ — безлимит навсегда", "👑 You're the admin — unlimited forever")
    if is_premium(u):
        until = fmt_date(u["premium_until"])
        return tx(lang, f"💎 Безлимит HD активен до {until}", f"💎 Unlimited HD active until {until}")
    text = tx(lang, f"🎟 Бесплатных сегодня: <b>{free_left(u)}</b> из {FREE_PER_DAY}", f"🎟 Free today: <b>{free_left(u)}</b> of {FREE_PER_DAY}")
    if u["bonus"] > 0:
        text += tx(lang, f" + {kruzhkov(u['bonus'])} в запасе", f" + {u['bonus']} in reserve")
    if u["clean"] > 0:
        text += tx(lang, f" (из них HD без метки: {u['clean']})", f" (HD without watermark: {u['clean']})")
    return text


HELP = (
    "🔵 <b>Что я умею</b>\n\n"
    "🎬 <b>Видео → кружок.</b> Любое видео до {mb} МБ. Длинное нарежу на несколько кружков подряд.\n"
    "🔗 <b>Ссылка → кружок.</b> Кинь ссылку на TikTok, VK, YouTube Shorts, Rutube — скачаю и сделаю кружок.\n"
    "🖼 <b>Фото → кружок</b> с плавным наездом камеры.\n"
    "🎵 <b>Музыка в кружке.</b> Сначала видео или фото, потом пришли песню (mp3) — наложу. "
    "Песня без видео — музыкальный кружок с твоей аватаркой.\n"
    "✏️ <b>Надпись.</b> Подпиши видео текстом в кавычках: <code>\"С днём рождения!\"</code> — или нажми ✏️ под кружком.\n"
    "⏱ <b>Кусок из середины.</b> Подпись <code>0:45</code> или <code>0:45-1:20</code>.\n"
    "⬆️ <b>Голова не влезла</b> — кнопки ⬆️⏺⬇️ под кружком, переделаю бесплатно.\n"
    "🔁 <b>Кружок → видео.</b> Перешли мне любой кружок — верну обычным видео, чтобы сохранить в галерею.\n"
    "🎤 <b>Голосовое</b> из звука видео — кнопкой под кружком.\n"
    "🎭 <b>Эффекты</b> — голос бурундука или робота, задом наперёд, бумеранг, VHS-кассета, ч/б: кнопка под кружком, бесплатно.\n\n"
    "Бесплатно {free} кружка в день. HD-качество без метки — /premium"
)


HELP_EN = (
    "🔵 <b>What I can do</b>\n\n"
    "🎬 <b>Video → circle.</b> Any video up to {mb} MB. Long videos are cut into several circles in a row.\n"
    "🔗 <b>Link → circle.</b> Send a TikTok, YouTube Shorts or other video link — I'll download it and make a circle.\n"
    "🖼 <b>Photo → circle</b> with a smooth camera zoom.\n"
    "🎵 <b>Music in a circle.</b> Send a video or photo, then a song (mp3) — I'll add it. "
    "A song alone becomes a music circle with your avatar spinning like a record.\n"
    "✏️ <b>Text.</b> Caption your video with text in quotes: <code>\"Happy birthday!\"</code> — or tap ✏️ under the circle.\n"
    "⏱ <b>A piece from the middle.</b> Caption <code>0:45</code> or <code>0:45-1:20</code>.\n"
    "⬆️ <b>Head cut off?</b> Tap ⬆️⏺⬇️ under the circle — I'll redo it for free.\n"
    "🔁 <b>Circle → video.</b> Forward me any circle — I'll send it back as a normal video to save to your gallery.\n"
    "🎤 <b>Voice message</b> from the video's sound — button under the circle.\n"
    "🎭 <b>Effects</b> — chipmunk or robot voice, reverse, boomerang, VHS tape, B&amp;W: button under the circle, free.\n\n"
    "{free} circles a day for free. HD with no watermark — /premium\n"
    "Язык / language: /lang"
)


def help_text(lang: str = "ru") -> str:
    return (HELP_EN if lang == "en" else HELP).format(mb=MAX_FILE_MB, free=FREE_PER_DAY)


# ---------- хендлеры: служебные ----------

@dp.message(CommandStart())
async def start(m: Message, bot: Bot):
    ref, source = None, None
    arg = (m.text or "").split(maxsplit=1)
    if len(arg) == 2 and arg[1].startswith("ref"):
        try:
            ref = int(arg[1][3:])
        except ValueError:
            pass
    elif len(arg) == 2:
        # метка площадки: t.me/krugi_video_bot?start=pikabu
        source = "".join(ch for ch in arg[1].lower() if ch.isalnum() or ch == "_")[:32] or None
    with db() as c:
        is_new = c.execute("SELECT 1 FROM users WHERE id=?", (m.from_user.id,)).fetchone() is None
    u = get_user(m.from_user.id, ref, source)
    if is_new and ADMIN_ID and m.from_user.id != ADMIN_ID:
        with db() as c:
            total = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        via = f", по приглашению {ref}" if ref else (f", источник: {html.escape(source)}" if source else ", без метки")
        await bot.send_message(ADMIN_ID, f"🆕 Новый пользователь {who(m)}{via}. Всего: {total}")
    if is_new:
        await send_example(m)
    lang = lg(m.from_user.id)
    if lang == "en":
        await m.answer(
            "👋 <b>Hi! I turn any video into a Telegram circle</b> 🔵\n\n"
            "1️⃣ Send me a video, photo, song or a TikTok link\n"
            "2️⃣ Get a round video message in a couple of seconds\n"
            "3️⃣ Forward it to a friend, a chat or your channel\n\n"
            "<blockquote expandable>💡 <b>Tips</b>\n"
            "• long video — I'll cut it into circles in a row\n"
            "• caption <code>0:45</code> — the circle starts from that moment\n"
            "• text in quotes <code>\"Happy birthday!\"</code> — it appears on the circle\n"
            "• send an mp3 after the circle — I'll add the music\n"
            "• under the circle — effects: chipmunk voice, reverse, VHS 🎭</blockquote>\n\n"
            f"{status_text(u)}\n"
            "Язык / language: /lang",
            reply_markup=start_kb(u, "en"),
        )
        return
    await m.answer(
        "👋 <b>Привет! Я делаю кружки из любого видео</b> 🔵\n\n"
        "1️⃣ Пришли видео, фото, песню или ссылку на TikTok\n"
        "2️⃣ Через пару секунд получишь кружок\n"
        "3️⃣ Перешли его другу, в чат или канал\n\n"
        "<blockquote expandable>💡 <b>Фишки</b>\n"
        "• длинное видео — нарежу на кружки подряд\n"
        "• подпись <code>0:45</code> — кружок с нужного момента\n"
        "• текст в кавычках <code>\"С днём рождения!\"</code> — надпись на кружке\n"
        "• после кружка пришли mp3 — наложу музыку\n"
        "• под кружком — эффекты: голос бурундука, реверс, VHS 🎭</blockquote>\n\n"
        f"{status_text(u)}\n"
        f"📢 Лайфхаки Telegram — @{CHANNEL}",
        reply_markup=start_kb(u, "ru"),
    )


@dp.message(Command("help"))
async def help_cmd(m: Message):
    await m.answer(help_text(lg(m.from_user.id)))


@dp.callback_query(F.data == "help")
async def help_cb(cq: CallbackQuery):
    await cq.answer()
    await cq.message.answer(help_text(lg(cq.from_user.id)))


@dp.message(Command("lang"))
async def lang_cmd(m: Message):
    await m.answer("🌐 Выбери язык / Choose your language:", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🇷🇺 Русский", callback_data="lang:ru"),
        InlineKeyboardButton(text="🇬🇧 English", callback_data="lang:en"),
    ]]))


@dp.callback_query(F.data.startswith("lang:"))
async def lang_set(cq: CallbackQuery):
    lang = cq.data.split(":", 1)[1]
    get_user(cq.from_user.id)
    with db() as c:
        c.execute("UPDATE users SET lang=? WHERE id=?", (lang, cq.from_user.id))
    await cq.answer()
    await cq.message.edit_text(tx(lang, "✅ Язык: русский. Все фишки — /help", "✅ Language: English. All features — /help"))


@dp.message(Command("invite"))
async def invite(m: Message, bot: Bot):
    uid = m.from_user.id
    get_user(uid)
    await check_ladder(bot, uid)  # вдруг друзья уже набрались, а награда ещё не выдана
    lang = lg(uid)
    if lang == "en":
        ladder = "\n".join(f"• {need} friends making circles → unlimited HD, no watermark, for {days} days" for need, days in LADDER)
        await m.answer(
            "🤝 <b>Invite friends — get unlimited</b>\n\n"
            f"+{REF_BONUS} circles right away for every friend, and once your friends start making circles:\n{ladder}\n\n"
            f"{ladder_progress(uid)}\n\n"
            f"Your link:\nhttps://t.me/{BOT_USERNAME}?start=ref{uid}\n\n"
            "💰 <b>Want Stars instead of circles?</b> Join the affiliate program: Settings → My Stars → Earn Stars → "
            f"find @{BOT_USERNAME} and get your link. You get 20% of every purchase made through it for 6 months.",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[share_btn(uid)]]),
        )
        return
    ladder = "\n".join(f"• {need} друзей с кружками → безлимит HD без метки на {days} дней" for need, days in LADDER)
    await m.answer(
        "🤝 <b>Приглашай друзей — получай безлимит</b>\n\n"
        f"За каждого друга сразу +{kruzhkov(REF_BONUS)}, а когда друзья начнут делать кружки:\n{ladder}\n\n"
        f"{ladder_progress(uid)}\n\n"
        f"Твоя ссылка:\nhttps://t.me/{BOT_USERNAME}?start=ref{uid}\n\n"
        "💰 <b>Хочешь звёзды, а не кружки?</b> Подключись к партнёрке: Настройки → Мои звёзды → «Зарабатывать звёзды» → "
        f"найди @{BOT_USERNAME} и получи свою ссылку. С каждой покупки по ней — 20% тебе, 6 месяцев.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[share_btn(uid)]]),
    )


@dp.message(Command("premium"))
async def premium(m: Message):
    u = get_user(m.from_user.id)
    lang = lg(m.from_user.id)
    await m.answer(
        f"{status_text(u)}\n\n" + tx(lang, f"В тарифах кружки в <b>HD 640px</b> и без метки @{BOT_USERNAME}.",
                                     f"Plans give you circles in <b>HD 640px</b> without the @{BOT_USERNAME} watermark."),
        reply_markup=buy_kb(lang=lang),
    )


@dp.message(Command("paysupport"))
async def paysupport(m: Message):
    # Telegram требует от ботов со Stars команду поддержки по платежам
    await m.answer(tx(lg(m.from_user.id),
                      "По вопросам оплаты напиши сюда же сообщение с описанием проблемы — мы ответим и при необходимости вернём звёзды.",
                      "For payment issues, describe the problem in a message here — we'll reply and refund the Stars if needed."))
    if ADMIN_ID:
        await m.bot.send_message(ADMIN_ID, f"💬 paysupport от {who(m)}")


@dp.message(Command("terms"))
async def terms(m: Message):
    await m.answer(tx(
        lg(m.from_user.id),
        "Подписка даёт безлимитную конвертацию в кружки HD без метки на указанный срок. "
        "Оплата в Telegram Stars. Если бот не работал по нашей вине — вернём звёзды через /paysupport. "
        "Присылая ссылку, ты подтверждаешь, что имеешь право использовать это видео.",
        "A subscription gives unlimited HD circles without a watermark for the stated period. "
        "Payment in Telegram Stars. If the bot didn't work through our fault, we'll refund the Stars via /paysupport. "
        "By sending a link you confirm you have the right to use that video.",
    ))


@dp.message(Command("stats"))
async def stats(m: Message):
    if m.from_user.id != ADMIN_ID:
        return
    with db() as c:
        users = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        total = c.execute("SELECT COALESCE(SUM(total),0) FROM users").fetchone()[0]
        prem = c.execute("SELECT COUNT(*) FROM users WHERE premium_until > ?", (int(time.time()),)).fetchone()[0]
        month_ago = int(time.time()) - 30 * 86400
        stars = c.execute("SELECT COALESCE(SUM(stars),0) FROM payments WHERE ts > ?", (month_ago,)).fetchone()[0]
        made = c.execute("SELECT COUNT(*) FROM users WHERE total > 0").fetchone()[0]
        hit = c.execute("SELECT COUNT(*) FROM users WHERE hit_limit = 1").fetchone()[0]
        opened = c.execute("SELECT COUNT(*) FROM users WHERE invoices > 0").fetchone()[0]
        payers = c.execute("SELECT COUNT(DISTINCT user_id) FROM payments").fetchone()[0]
        reminders_off = c.execute("SELECT COUNT(*) FROM users WHERE remind_off = 1").fetchone()[0]
        saw = c.execute("SELECT COUNT(*) FROM users WHERE saw_plans = 1").fetchone()[0]
        nudged = c.execute("SELECT COUNT(*) FROM users WHERE checkout_nudge = 1").fetchone()[0]
        start_n, start_ok = c.execute("SELECT COUNT(*), COALESCE(SUM(total > 0), 0) FROM users WHERE start_nudge = 1").fetchone()
        subs = c.execute("SELECT COUNT(*) FROM users WHERE sub_bonus = 1").fetchone()[0]
        refs_all = c.execute("SELECT COUNT(*) FROM users WHERE referrer IS NOT NULL").fetchone()[0]
        refs_act = c.execute("SELECT COUNT(*) FROM users WHERE ref_counted = 1").fetchone()[0]
        top_refs = c.execute(
            "SELECT referrer, COUNT(*), SUM(ref_counted) FROM users WHERE referrer IS NOT NULL "
            "GROUP BY referrer ORDER BY 3 DESC, 2 DESC LIMIT 5"
        ).fetchall()
        blocked = c.execute("SELECT COUNT(*) FROM users WHERE blocked = 1").fetchone()[0]
        week_ago = int(time.time()) - 7 * 86400
        feats = c.execute(
            "SELECT kind, COUNT(*), COUNT(DISTINCT user_id) FROM events WHERE ts > ? GROUP BY kind ORDER BY 2 DESC", (week_ago,)
        ).fetchall()
        sources = c.execute(
            "SELECT COALESCE(source, 'без метки'), COUNT(*), SUM(total > 0) FROM users GROUP BY 1 ORDER BY 2 DESC"
        ).fetchall()
        heard = c.execute(
            "SELECT heard, COUNT(*), SUM(invoices > 0) FROM users WHERE heard NOT IN ('', '?') GROUP BY 1 ORDER BY 2 DESC"
        ).fetchall()
        asked = c.execute("SELECT COUNT(*) FROM users WHERE heard != ''").fetchone()[0]
    src_lines = "\n".join(f"  • {html.escape(str(n))}: {cnt} (сделали кружок: {act or 0})" for n, cnt, act in sources)
    ref_lines = "".join(f"  • {r}: пришло {n}, с кружками {a or 0}\n" for r, n, a in top_refs)
    feat_lines = "\n".join(f"  • {k}: {n} раз, {p} чел." for k, n, p in feats if not k.startswith("heard_")) or "  пока нет"
    names = {k: ru for k, ru, _ in HEARD}
    heard_lines = "\n".join(f"  • {names.get(k, k)}: {n} (открыли оплату: {o or 0})" for k, n, o in heard) or "  пока никто"
    await m.answer(
        f"👥 Пользователей: {users} (заблокировали: {blocked})\n🔵 Кружков сделано: {total}\n"
        f"💎 Активных подписок: {prem}\n⭐ Звёзд за 30 дней: {stars}\n\n"
        f"🔻 Воронка:\n  запустили бота: {users}\n  напомнили новичкам без кружка: {start_n} (потом сделали кружок: {start_ok})\n  сделали кружок: {made}\n  увидели тарифы: {saw}\n  упёрлись в лимит: {hit}\n"
        f"  открыли оплату: {opened}\n  подсказали, как оплатить: {nudged}\n  оплатили: {payers}\n  отключили напоминания: {reminders_off}\n  подписались на канал за бонус: {subs}\n\n"
        f"🤝 По приглашениям: {refs_all}, из них сделали кружок {refs_act}\n{ref_lines}\n"
        f"🧩 Фишки за 7 дней:\n{feat_lines}\n\n"
        f"📍 Откуда пришли:\n{src_lines}\n\n"
        f"🙋 «Откуда узнали?» (спросили {asked}):\n{heard_lines}"
    )


@dp.callback_query(F.data == "sub")
async def sub_check(cq: CallbackQuery, bot: Bot):
    u = get_user(cq.from_user.id)
    if u["sub_bonus"]:
        await cq.answer("Бонус за подписку уже получен 👍", show_alert=True)
        return
    try:
        member = await bot.get_chat_member(f"@{CHANNEL}", cq.from_user.id)
    except Exception:
        logging.exception("get_chat_member failed")  # скорее всего бот не админ канала
        await cq.answer("Не получилось проверить подписку, попробуй позже 🙏", show_alert=True)
        if ADMIN_ID:
            await bot.send_message(ADMIN_ID, f"⚠️ Не могу проверить подписку на @{CHANNEL} — добавь бота админом в канал")
        return
    if member.status not in ("member", "administrator", "creator"):
        await cq.answer(f"Сначала подпишись на @{CHANNEL}, потом нажми ещё раз", show_alert=True)
        return
    with db() as c:
        c.execute("UPDATE users SET bonus = bonus + ?, clean = clean + ?, sub_bonus = 1 WHERE id=? AND sub_bonus = 0", (SUB_BONUS, SUB_BONUS, cq.from_user.id))
    await cq.answer(f"🎉 +{kruzhkov(SUB_BONUS)}! Спасибо за подписку", show_alert=True)
    await cq.message.answer(f"🎉 Начислил +{kruzhkov(SUB_BONUS)} в HD без метки за подписку на канал. {status_text(get_user(cq.from_user.id))}")


@dp.callback_query(F.data == "plans")
async def plans(cq: CallbackQuery):
    await cq.answer()
    with db() as c:
        c.execute("UPDATE users SET saw_plans=1 WHERE id=?", (cq.from_user.id,))
    await cq.message.answer(
        tx(lg(cq.from_user.id),
           f"Бесплатно — {kruzhkov(FREE_PER_DAY)} в день, с меткой. В тарифах:\n"
           "• <b>HD 640px</b> — заметно чётче обычного кружка\n"
           "• без метки @krugi_video_bot\n"
           "• 10 кружков не сгорают, неделя/месяц — без лимита\n\n"
           "Оплата звёздами Telegram ⭐, прямо в чате:",
           f"Free — {FREE_PER_DAY} circles a day, with a watermark. Plans give you:\n"
           "• <b>HD 640px</b> — noticeably sharper than a normal circle\n"
           "• no @krugi_video_bot watermark\n"
           "• 10 circles never expire, week/month — no limits\n\n"
           "Pay with Telegram Stars ⭐ right here in the chat:"),
        reply_markup=buy_kb(cq.from_user.id),
    )


@dp.callback_query(F.data.startswith("buy"))
async def buy(cq: CallbackQuery):
    await cq.answer()
    key = cq.data.split(":", 1)[1] if ":" in cq.data else "month"  # старые кнопки «buy» = месяц
    key = key if key in PLANS else "month"
    _, stars, days, bonus = PLANS[key]
    lang = lg(cq.from_user.id)
    name = plan_name(key, lang)
    with db() as c:
        c.execute("UPDATE users SET invoices = invoices + 1 WHERE id=?", (cq.from_user.id,))
    if bonus:
        desc = tx(lang, f"+{kruzhkov(bonus)} в HD без метки, не сгорают", f"+{bonus} HD circles without a watermark, never expire")
    else:
        desc = tx(lang, f"Кружки в HD без лимита и без метки на {days} дней", f"Unlimited HD circles without a watermark for {days} days")
    await cq.message.answer_invoice(
        title=name,
        description=desc,
        payload=key,
        currency="XTR",  # Telegram Stars, provider_token не нужен
        prices=[LabeledPrice(label=name, amount=stars)],
    )
    asyncio.create_task(checkout_nudge(cq.bot, cq.from_user.id, int(time.time())))


@dp.callback_query(F.data == "clean1")
async def clean1(cq: CallbackQuery):
    """Счёт на переделку этого кружка в HD без метки."""
    lang = lg(cq.from_user.id)
    if (cq.message.chat.id, cq.message.message_id) not in _jobs:
        await cq.answer(gone(lang), show_alert=True)
        return
    await cq.answer()
    with db() as c:
        c.execute("UPDATE users SET invoices = invoices + 1, saw_plans = 1 WHERE id=?", (cq.from_user.id,))
    title = tx(lang, "Кружок в HD без метки", "Circle in HD, no watermark")
    await cq.message.answer_invoice(
        title=title,
        description=tx(lang, "Переделаю этот кружок в HD 640px и без надписи @krugi_video_bot",
                       "I'll redo this circle in HD 640px without the @krugi_video_bot watermark"),
        payload=f"clean1:{cq.message.message_id}",
        currency="XTR",
        prices=[LabeledPrice(label=title, amount=CLEAN1_PRICE)],
    )
    asyncio.create_task(checkout_nudge(cq.bot, cq.from_user.id, int(time.time())))


async def checkout_nudge(bot: Bot, uid: int, ts: int) -> None:
    """Открыл счёт, но за 15 минут не оплатил: один раз подсказываем, где купить звёзды,
    и как получить кружки без метки бесплатно (часто мешает именно покупка звёзд)."""
    await asyncio.sleep(CHECKOUT_NUDGE_SEC)
    with db() as c:
        paid = c.execute("SELECT 1 FROM payments WHERE user_id=? AND ts>=?", (uid, ts)).fetchone()
        row = c.execute("SELECT checkout_nudge, blocked FROM users WHERE id=?", (uid,)).fetchone()
        if paid or not row or row["checkout_nudge"] or row["blocked"]:
            return
        c.execute("UPDATE users SET checkout_nudge = 1 WHERE id=?", (uid,))
    u = get_user(uid)
    lang = lg(uid)
    free = tx(lang, "\n• позови 3 друзей, которые сделают кружок, — неделя HD без метки (/invite)",
              "\n• invite 3 friends who make a circle — a week of HD with no watermark (/invite)")
    if lang != "en" and not u["sub_bonus"]:
        free = f"\n• подпишись на наш канал — +{kruzhkov(SUB_BONUS)} без метки" + free
    text = tx(lang,
              "🤔 Не получилось оплатить?\n\nЗвёзды покупаются прямо в Telegram: Настройки → «Мои звёзды». "
              "Если карта не проходит, звёзды продаёт и официальная площадка Telegram — fragment.com.\n\n"
              "А кружки без метки можно получить и бесплатно:" + free,
              "🤔 Couldn't complete the payment?\n\nStars can be bought right in Telegram: Settings → My Stars. "
              "If your card doesn't work, Telegram's official marketplace fragment.com sells Stars too.\n\n"
              "You can also get circles without a watermark for free:" + free)
    try:
        await bot.send_message(uid, text, reply_markup=InlineKeyboardMarkup(inline_keyboard=sub_rows(u) + [[share_btn(uid)]]))
        log_event(uid, "checkout_nudge")
    except Exception:
        logging.exception("checkout_nudge failed")


@dp.pre_checkout_query()
async def pre_checkout(q: PreCheckoutQuery):
    await q.answer(ok=True)

# ---------- создание кружков ----------

def gone(lang: str) -> str:
    return tx(lang, "Это видео уже не в памяти — пришли его ещё раз.", "This video is no longer in memory — please send it again.")


HEARD = [  # ключ, ru, en — варианты ответа «Откуда узнали?»
    ("tiktok", "TikTok", "TikTok"),
    ("youtube", "YouTube", "YouTube"),
    ("tgsearch", "Поиск в Telegram", "Telegram search"),
    ("friend", "Друг / кружок с меткой", "A friend / watermark"),
    ("other", "Другое", "Other"),
]


async def ask_heard(m: Message, u: sqlite3.Row, lang: str) -> None:
    """Один раз, после кружка, спрашиваем у пришедших без метки, откуда они узнали о боте."""
    if u["heard"] or u["source"] or u["id"] == ADMIN_ID:
        return
    with db() as c:
        c.execute("UPDATE users SET heard='?' WHERE id=?", (u["id"],))
    rows = [[InlineKeyboardButton(text=tx(lang, ru, en), callback_data=f"heard:{k}")] for k, ru, en in HEARD]
    await m.answer(tx(lang, "🙏 Один вопрос, один тап: откуда ты узнал о боте?",
                      "🙏 One quick tap: where did you hear about the bot?"),
                   reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))


@dp.callback_query(F.data.startswith("heard:"))
async def heard_set(cq: CallbackQuery):
    key = cq.data.split(":", 1)[1]
    if key not in {k for k, _, _ in HEARD}:
        await cq.answer()
        return
    with db() as c:
        c.execute("UPDATE users SET heard=? WHERE id=?", (key, cq.from_user.id))
    log_event(cq.from_user.id, f"heard_{key}")
    lang = lg(cq.from_user.id)
    await cq.message.edit_text(tx(lang, "Спасибо! 🙌 Это помогает делать бота лучше.",
                                  "Thanks! 🙌 That helps us make the bot better."))
    await cq.answer()


def mark_note(lang: str) -> str:
    return tx(lang, "\n🏷 <i>На бесплатных кружках внизу метка бота. В HD и без метки — кнопка ✨</i>",
              "\n🏷 <i>Free circles have a small bot watermark. HD without it — the ✨ button</i>")


async def ensure_src(bot: Bot, job: dict) -> bool:
    """Исходник задания на диске; если кэш почищен — перекачиваем из Telegram по file_id."""
    for path_key, id_key in (("src", "file_id"), ("audio", "audio_id")):
        p = job.get(path_key)
        if p and not Path(p).exists():
            if not job.get(id_key):
                return False
            await bot.download(job[id_key], destination=p)
    return True


async def make_series(m: Message, bot: Bot, src: Path, file_id: str | None, caption: str | None,
                      vertical: bool | None, origin: str, status: Message | None = None) -> None:
    """Видео (из Telegram или по ссылке) → один или несколько кружков. Лимит проверен и вызов под замком пользователя."""
    uid = m.from_user.id
    u = get_user(uid)
    lang = lg(uid)
    start, end, pos, label = parse_caption(caption)
    status = status or await m.answer(tx(lang, "⏳ Делаю кружок...", "⏳ Making your circle..."))
    await bot.send_chat_action(m.chat.id, "record_video_note")
    t0 = time.monotonic()
    duration = await probe_duration(src)
    if vertical is None:
        w, h = await probe_size(src)
        vertical = h >= w
    if end is None or (duration and end > duration):
        end = duration or start + PART_SEC
    if start >= end:
        await status.edit_text(tx(lang, f"⚠️ Видео короче, чем {start:.0f} с — не с чего начинать. Пришли его без подписи или с другим временем.",
                                  f"⚠️ The video is shorter than {start:.0f} s — nothing to start from. Send it without a caption or with another time."))
        return
    # округление вверх; хвост короче секунды отдельным кружком не делаем
    parts = max(1, min(MAX_PARTS, math.ceil((end - start - 1) / PART_SEC)))
    allowed = parts if is_premium(u) else min(parts, left_today(u))
    if parts > 1:
        await status.edit_text(tx(lang, f"⏳ Видео длинное — нарежу на {kruzhkov(parts)} подряд...",
                                  f"⏳ Long video — cutting it into {parts} circles in a row..."))
    sent, marked, hd_any = 0, False, False
    job = {}
    with tempfile.TemporaryDirectory() as tmp:
        try:
            for i in range(allowed):
                s = start + i * PART_SEC
                cur = get_user(uid)
                mark = needs_mark(cur) or (uid == ADMIN_ID and "метка" in (caption or "").lower())
                hd = not mark
                marked, hd_any = marked or mark, hd_any or hd
                job = {"kind": "video", "src": str(src), "file_id": file_id, "start": s, "length": min(PART_SEC, end - s),
                       "pos": pos, "text": label, "vertical": vertical}
                dst = Path(tmp) / f"out{i}.mp4"
                await render(job, dst, mark, hd)
                await m.answer_video_note(FSInputFile(dst), length=640 if hd else 512)
                consume(uid)
                if not mark and not is_premium(cur):
                    use_clean(uid)
                sent += 1
                if sent == 1:
                    await count_ref(bot, uid)
                if parts > 1 and i + 1 < allowed:
                    await bot.send_chat_action(m.chat.id, "record_video_note")
        except Exception:
            logging.exception("convert failed")
            if not sent:
                await status.edit_text(tx(lang, "❌ Не получилось обработать это видео. Попробуй другое.",
                                          "❌ Couldn't process this video. Try another one."))
                return
    log_event(uid, origin)
    if label:
        log_event(uid, "text")
    total = time.monotonic() - t0
    logging.info("convert user=%s origin=%s parts=%s/%s total=%.1fs", uid, origin, sent, parts, total)

    u = get_user(uid)
    if sent == 1:
        text = tx(lang, "✅ <b>Кружок готов!</b> Перешли его куда угодно.", "✅ <b>Your circle is ready!</b> Forward it anywhere.")
    else:
        text = tx(lang, f"✅ <b>Готово: {kruzhkov(sent)} подряд.</b> Пересылай по порядку.",
                  f"✅ <b>Done: {sent} circles in a row.</b> Forward them in order.")
    if sent < parts:
        mark_limit(uid)
        text += tx(lang, f"\n\n⚠️ Видео на {kruzhkov(parts)}, а бесплатных сегодня хватило на {sent}. "
                         "Остальное — завтра, за друга или с безлимитом:",
                   f"\n\n⚠️ The video needs {parts} circles, but today's free ones covered {sent}. "
                   "The rest — tomorrow, for a friend or with unlimited:")
        kb = buy_kb(uid)
    elif sent == 1:
        text += tx(lang, "\n<i>Ниже: сдвинуть кадр, надпись, музыка и эффекты</i> 👇",
                   "\n<i>Below: move the frame, add text, music or effects</i> 👇")
        kb = result_kb(job, uid, marked)
        remember((m.chat.id, status.message_id), job, uid)
    else:
        kb = InlineKeyboardMarkup(inline_keyboard=[[share_btn(uid)]])
    if sent >= parts:
        kb = with_plans(kb, u)
    if marked:
        text += mark_note(lang)
    elif hd_any:
        text += tx(lang, "\n💎 Качество HD 640px.", "\n💎 HD quality 640px.")
    text += f"\n\n{status_text(u)}"
    if uid == ADMIN_ID:
        text += f"\n⏱ всего {total:.1f} с"
    await status.edit_text(text, reply_markup=kb)
    if sent >= parts and need_upsell(u):
        await m.answer(
            tx(lang, "🔥 Остался 1 бесплатный кружок на сегодня.\n"
                     "Чтобы не ждать до завтра — 10 HD-кружков без метки за 15 ⭐ (не сгорают) или безлимит:",
               "🔥 1 free circle left for today.\n"
               "Don't want to wait until tomorrow? 10 HD circles without a watermark for 15 ⭐ (never expire) or unlimited:"),
            reply_markup=buy_kb(uid),
        )
    elif sent:
        await ask_heard(m, u, lang)


async def limit_reached(m: Message, u: sqlite3.Row) -> bool:
    """Если бесплатные кончились — говорим об этом и возвращаем True."""
    if is_premium(u) or left_today(u) > 0:
        return False
    mark_limit(m.from_user.id)
    if lg(m.from_user.id) == "en":
        text = ("😔 You're out of free circles for today.\n"
                f"Tomorrow you'll get {FREE_PER_DAY} more. Meanwhile — share the bot with a friend (+{REF_BONUS}) or grab a pack:")
    else:
        text = ("😔 Бесплатные кружки на сегодня закончились.\n"
                f"Завтра будет ещё {kruzhkov(FREE_PER_DAY)}. А пока — поделись ботом с другом (+{kruzhkov(REF_BONUS)})"
                + ("" if u["sub_bonus"] else f", подпишись на наш канал (+{kruzhkov(SUB_BONUS)})") + " или возьми пакет:")
    await m.answer(
        text,
        reply_markup=InlineKeyboardMarkup(inline_keyboard=buy_kb(m.from_user.id).inline_keyboard + sub_rows(u)),
    )
    return True


@dp.message(F.video | F.animation | F.document.mime_type.startswith("video/"))
async def convert(m: Message, bot: Bot):
    async with _locks[m.from_user.id]:
        u = get_user(m.from_user.id)
        if await limit_reached(m, u):
            return
        lang = lg(m.from_user.id)
        media = m.video or m.animation or m.document
        if media.file_size and media.file_size > MAX_FILE_MB * 1024 * 1024:
            await m.answer(tx(
                lang,
                f"Файл больше {MAX_FILE_MB} МБ — Telegram не даёт ботам скачивать такие.\n"
                "Выход: загрузи видео в TikTok/VK/YouTube (можно скрытым) и пришли мне <b>ссылку</b> — сделаю кружок по ней.",
                f"The file is over {MAX_FILE_MB} MB — Telegram doesn't let bots download files that big.\n"
                "Workaround: upload the video to TikTok/YouTube (can be unlisted) and send me the <b>link</b> — I'll make a circle from it.",
            ))
            return
        w, h = getattr(media, "width", 0) or 0, getattr(media, "height", 0) or 0
        status = await m.answer(tx(lang, "⏳ Делаю кружок...", "⏳ Making your circle..."))
        src = cache_file(".mp4")
        try:
            await bot.download(media, destination=src)
        except Exception:
            logging.exception("download failed")
            await status.edit_text(tx(lang, "❌ Не получилось скачать видео. Пришли ещё раз.", "❌ Couldn't download the video. Please send it again."))
            return
        await make_series(m, bot, src, media.file_id, m.caption, (h >= w) if (w and h) else None, "video", status)


URL_RE = re.compile(r"https?://\S+")


async def convert_link(m: Message, bot: Bot, url: str):
    async with _locks[m.from_user.id]:
        u = get_user(m.from_user.id)
        if await limit_reached(m, u):
            return
        lang = lg(m.from_user.id)
        status = await m.answer(tx(lang, "⏳ Скачиваю видео по ссылке...", "⏳ Downloading the video from the link..."))
        await bot.send_chat_action(m.chat.id, "upload_video")
        try:
            src = await fetch_link(url)
        except Exception as e:
            logging.warning("link failed %s: %s", url, str(e)[-200:])
            await status.edit_text(tx(
                lang,
                "❌ Не получилось скачать по этой ссылке. Бывает с закрытыми аккаунтами, Instagram и очень длинными видео.\n"
                "Сохрани видео в галерею и пришли мне файлом — сделаю кружок.",
                "❌ Couldn't download from this link. It happens with private accounts, Instagram and very long videos.\n"
                "Save the video to your gallery and send it to me as a file — I'll make a circle.",
            ))
            return
        caption = URL_RE.sub(" ", m.text or "")
        await status.edit_text(tx(lang, "⏳ Скачал, делаю кружок...", "⏳ Downloaded, making your circle..."))
        await make_series(m, bot, src, None, caption, None, "link", status)


@dp.message(F.photo | F.document.mime_type.startswith("image/"))
async def photo(m: Message, bot: Bot):
    """Фото → кружок с плавным наездом камеры."""
    async with _locks[m.from_user.id]:
        u = get_user(m.from_user.id)
        if await limit_reached(m, u):
            return
        lang = lg(m.from_user.id)
        media = m.photo[-1] if m.photo else m.document
        status = await m.answer(tx(lang, "⏳ Делаю кружок из фото...", "⏳ Making a circle from your photo..."))
        await bot.send_chat_action(m.chat.id, "record_video_note")
        src = cache_file(".jpg")
        _, _, pos, label = parse_caption(m.caption)
        w, h = getattr(media, "width", 0) or 0, getattr(media, "height", 0) or 0
        job = {"kind": "photo", "src": str(src), "file_id": media.file_id, "length": PHOTO_SEC, "pos": pos, "text": label,
               "vertical": h >= w}
        mark = needs_mark(u)
        try:
            await bot.download(media, destination=src)
            with tempfile.TemporaryDirectory() as tmp:
                dst = Path(tmp) / "out.mp4"
                await render(job, dst, mark, not mark)
                await m.answer_video_note(FSInputFile(dst), length=512 if mark else 640)
        except Exception:
            logging.exception("photo failed")
            await status.edit_text(tx(lang, "❌ Не получилось сделать кружок из этого фото.", "❌ Couldn't make a circle from this photo."))
            return
        consume(m.from_user.id)
        if not mark and not is_premium(u):
            use_clean(m.from_user.id)
        await count_ref(bot, m.from_user.id)
        log_event(m.from_user.id, "photo")
        remember((m.chat.id, status.message_id), job, m.from_user.id)
        u = get_user(m.from_user.id)
        await status.edit_text(
            tx(lang, "✅ <b>Кружок из фото готов!</b>\n🎵 Пришли песню (mp3) — наложу музыку, кружок станет длиной с трек (до минуты).",
               "✅ <b>Your photo circle is ready!</b>\n🎵 Send a song (mp3) — I'll add the music and the circle will match the track (up to a minute).")
            + (mark_note(lang) if mark else "")
            + f"\n\n{status_text(u)}",
            reply_markup=with_plans(result_kb(job, m.from_user.id, mark), u),
        )


@dp.message(F.audio | F.voice | F.document.mime_type.startswith("audio/"))
async def music(m: Message, bot: Bot):
    """Песня/голосовое: наложить на последний кружок или сделать музыкальный кружок с аватаркой."""
    uid = m.from_user.id
    async with _locks[uid]:
        u = get_user(uid)
        lang = lg(uid)
        media = m.audio or m.voice or m.document
        if media.file_size and media.file_size > MAX_FILE_MB * 1024 * 1024:
            await m.answer(tx(lang, f"Файл больше {MAX_FILE_MB} МБ — пришли трек поменьше.", f"The file is over {MAX_FILE_MB} MB — send a smaller track."))
            return
        a_start, _, _, _ = parse_caption(m.caption)
        mix = bool(re.search(r"микс|mix|смеша", (m.caption or "").lower()))
        audio = cache_file(".audio")
        found = last_job(uid)
        if not found and await limit_reached(m, u):
            return
        status = await m.answer(tx(lang, "⏳ Накладываю музыку...", "⏳ Adding the music...") if found
                                else tx(lang, "⏳ Делаю музыкальный кружок...", "⏳ Making a music circle..."))
        await bot.send_chat_action(m.chat.id, "record_video_note")
        try:
            await bot.download(media, destination=audio)
            a_len = await probe_duration(audio) - a_start
            if a_len <= 0.5:
                await status.edit_text(tx(lang, "⚠️ Трек короче, чем указанное время начала.", "⚠️ The track is shorter than the start time you gave."))
                return
            if found:
                key, base = found
                if not await ensure_src(bot, base):
                    raise RuntimeError("source lost")
                job = dict(base, audio=str(audio), audio_id=media.file_id, audio_start=a_start, mix=mix)
                if job["kind"] in ("photo", "music"):
                    job["length"] = min(PART_SEC, a_len)
                origin = "music_on_circle"
            else:
                cover = None
                try:
                    photos = await bot.get_user_profile_photos(uid, limit=1)
                    if photos.total_count:
                        cover = cache_file(".jpg")
                        await bot.download(photos.photos[0][-1], destination=cover)
                except Exception:
                    logging.exception("avatar")
                    cover = None
                job = {"kind": "music", "src": str(cover) if cover else None, "length": min(PART_SEC, a_len),
                       "audio": str(audio), "audio_id": media.file_id, "audio_start": a_start, "text": "", "vertical": True}
                origin = "music_circle"
            mark = needs_mark(u)
            with tempfile.TemporaryDirectory() as tmp:
                dst = Path(tmp) / "out.mp4"
                await render(job, dst, mark, not mark)
                await m.answer_video_note(FSInputFile(dst), length=512 if mark else 640)
        except Exception:
            logging.exception("music failed")
            await status.edit_text(tx(lang, "❌ Не получилось с этим файлом. Пришли трек в mp3.", "❌ Couldn't use this file. Please send the track as an mp3."))
            return
        if origin == "music_circle":
            consume(uid)
            if not mark and not is_premium(u):
                use_clean(uid)
            await count_ref(bot, uid)
        log_event(uid, origin)
        remember((m.chat.id, status.message_id), job, uid)
        u = get_user(uid)
        if origin == "music_circle":
            text = (tx(lang, "✅ <b>Музыкальный кружок готов!</b>", "✅ <b>Your music circle is ready!</b>")
                    + ("" if job["src"] else tx(lang, "\nПоставь аватарку в Telegram — в следующий раз она будет крутиться как пластинка.",
                                                "\nSet a Telegram profile photo — next time it will spin like a record."))
                    + tx(lang, "\nХочешь музыку на своё видео? Пришли видео, потом трек.",
                         "\nWant music on your own video? Send the video, then the track."))
        else:
            text = (tx(lang, "✅ <b>Музыка наложена!</b>", "✅ <b>Music added!</b>")
                    + (tx(lang, " Родной звук оставил тише.", " The original sound is kept, quieter.") if mix else
                       tx(lang, "\nХочешь оставить и родной звук — подпиши трек словом <code>микс</code>.",
                          "\nWant to keep the original sound too — caption the track <code>mix</code>."))
                    + tx(lang, "\nНачать песню с припева — подпиши трек временем, например <code>0:45</code>.",
                         "\nStart the song from the chorus — caption the track with a time, e.g. <code>0:45</code>."))
        if mark:
            text += mark_note(lang)
        await status.edit_text(text + f"\n\n{status_text(u)}", reply_markup=with_plans(result_kb(job, uid, mark), u))


@dp.message(F.video_note)
async def unround(m: Message, bot: Bot):
    """Кружок → обычное видео (чтобы сохранить в галерею) + кнопка «голосовое». Бесплатно."""
    async with _locks[m.from_user.id]:
        get_user(m.from_user.id)
        lang = lg(m.from_user.id)
        await bot.send_chat_action(m.chat.id, "upload_video")
        src = cache_file(".mp4")
        try:
            await bot.download(m.video_note, destination=src)
            dur = m.video_note.duration or await probe_duration(src)
            kb = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text=tx(lang, "🎤 Сделать голосовое", "🎤 Make a voice message"), callback_data="voice")],
                [share_btn(m.from_user.id)]])
            sent = await m.answer_video(
                FSInputFile(src, filename="krugi_video_bot.mp4"),
                caption=tx(lang, "🔁 Кружок → видео. Теперь его можно сохранить в галерею: ⋮ → «Сохранить».",
                           "🔁 Circle → video. Now you can save it to your gallery: ⋮ → Save."),
                reply_markup=kb,
            )
        except Exception:
            logging.exception("unround failed")
            await m.answer(tx(lang, "❌ Не получилось. Перешли кружок ещё раз.", "❌ Something went wrong. Forward the circle again."))
            return
        _jobs[(m.chat.id, sent.message_id)] = {"kind": "video", "src": str(src), "file_id": m.video_note.file_id,
                                               "start": 0, "length": dur, "pos": "center", "text": ""}
        log_event(m.from_user.id, "unround")


async def paid_clean1(m: Message, bot: Bot, msg_id: int) -> None:
    """Оплачен «этот кружок без метки»: переделываем в HD без метки; если видео забыто — даём 1 чистый кружок."""
    sp = m.successful_payment
    add_premium(m.from_user.id, sp.telegram_payment_charge_id, sp.total_amount, 0, 0)
    if ADMIN_ID:
        await bot.send_message(ADMIN_ID, f"💰 +{sp.total_amount}⭐ от {m.from_user.id} (кружок без метки)")
    job = _jobs.get((m.chat.id, msg_id))
    try:
        if not job or not await ensure_src(bot, job):
            raise LookupError
        await bot.send_chat_action(m.chat.id, "record_video_note")
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "out.mp4"
            await render(job, dst, mark=False, hd=True)
            await m.answer_video_note(FSInputFile(dst), length=640)
        await m.answer(tx(lg(m.from_user.id), "🎉 Готово — кружок в HD и без метки. Спасибо!", "🎉 Done — your circle in HD with no watermark. Thank you!"))
        log_event(m.from_user.id, "clean1")
    except Exception as e:
        if not isinstance(e, LookupError):
            logging.exception("clean1 failed")
        with db() as c:
            c.execute("UPDATE users SET clean = clean + 1 WHERE id=?", (m.from_user.id,))
        await m.answer(tx(lg(m.from_user.id), "🎉 Спасибо! Пришли видео ещё раз — следующий кружок будет в HD без метки.",
                          "🎉 Thank you! Send the video again — your next circle will be in HD with no watermark."))


async def remake(cq: CallbackQuery, bot: Bot, key: tuple[int, int], job: dict, kind: str) -> None:
    """Переделать кружок по изменённому заданию (кадр, надпись, музыка). Лимит не тратит."""
    u = get_user(cq.from_user.id)
    mark = needs_mark(u)
    await bot.send_chat_action(cq.message.chat.id, "record_video_note")
    try:
        if not await ensure_src(bot, job):
            raise RuntimeError("source lost")
        with tempfile.TemporaryDirectory() as tmp:
            dst = Path(tmp) / "out.mp4"
            await render(job, dst, mark, not mark)
            await cq.message.answer_video_note(FSInputFile(dst), length=512 if mark else 640)
        _jobs[key] = job
        _last[cq.from_user.id] = (key, time.time())
        log_event(cq.from_user.id, kind)
    except Exception:
        logging.exception("remake failed")
        await cq.message.answer(tx(lg(cq.from_user.id), "❌ Не получилось переделать. Пришли исходник ещё раз.",
                                   "❌ Couldn't redo it. Please send the original again."))


@dp.callback_query(F.data.startswith("pos:"))
async def recrop(cq: CallbackQuery, bot: Bot):
    """Пересделать кружок, сдвинув квадрат вверх/вниз (влево/вправо). Не тратит лимит."""
    key = (cq.message.chat.id, cq.message.message_id)
    lang = lg(cq.from_user.id)
    if key not in _jobs:
        await cq.answer(gone(lang), show_alert=True)
        return
    await cq.answer(tx(lang, "⏳ Переделываю...", "⏳ Redoing..."))
    async with _locks[cq.from_user.id]:
        await remake(cq, bot, key, dict(_jobs[key], pos=cq.data.split(":", 1)[1]), "recrop")


@dp.callback_query(F.data == "text")
async def ask_text(cq: CallbackQuery):
    key = (cq.message.chat.id, cq.message.message_id)
    lang = lg(cq.from_user.id)
    if key not in _jobs:
        await cq.answer(gone(lang), show_alert=True)
        return
    _await_text[cq.from_user.id] = key
    await cq.answer()
    await cq.message.answer(tx(lang, "✏️ Напиши текст надписи (до 60 символов) — например: <i>С днём рождения, мам!</i>\n"
                                     "Чтобы убрать надпись — пришли минус: <code>-</code>",
                               "✏️ Type the text for the circle (up to 60 characters) — for example: <i>Happy birthday, mom!</i>\n"
                               "To remove the text, send a minus: <code>-</code>"))


@dp.callback_query(F.data == "music")
async def ask_music(cq: CallbackQuery):
    key = (cq.message.chat.id, cq.message.message_id)
    lang = lg(cq.from_user.id)
    if key not in _jobs:
        await cq.answer(gone(lang), show_alert=True)
        return
    _last[cq.from_user.id] = (key, time.time())
    await cq.answer()
    await cq.message.answer(tx(
        lang,
        "🎵 Пришли песню файлом (mp3) или голосовое — наложу на этот кружок.\n"
        "• начать с припева — подпиши трек временем: <code>0:45</code>\n"
        "• оставить и родной звук — подпиши <code>микс</code>\n"
        "Где взять mp3: в музыкальном боте или своём плейлисте — «Поделиться» → Telegram → сюда.",
        "🎵 Send a song as a file (mp3) or a voice message — I'll add it to this circle.\n"
        "• start from the chorus — caption the track with a time: <code>0:45</code>\n"
        "• keep the original sound too — caption it <code>mix</code>\n"
        "Where to get an mp3: a music bot or your own library — Share → Telegram → here.",
    ))


@dp.callback_query(F.data == "voice")
async def voice(cq: CallbackQuery, bot: Bot):
    """Звук того же куска — голосовым сообщением. Не тратит лимит."""
    key = (cq.message.chat.id, cq.message.message_id)
    lang = lg(cq.from_user.id)
    job = _jobs.get(key)
    if not job:
        await cq.answer(gone(lang), show_alert=True)
        return
    if not job.get("audio") and job["kind"] != "video":
        await cq.answer(tx(lang, "В этом кружке нет звука — сначала добавь музыку 🎵", "This circle has no sound — add music first 🎵"), show_alert=True)
        return
    await cq.answer(tx(lang, "⏳ Делаю голосовое...", "⏳ Making a voice message..."))
    await bot.send_chat_action(cq.message.chat.id, "record_voice")
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / "out.ogg"
        try:
            if not await ensure_src(bot, job):
                raise RuntimeError("source lost")
            if job.get("audio"):
                await to_voice(Path(job["audio"]), dst, job.get("audio_start", 0), min(PART_SEC, job["length"]))
            else:
                await to_voice(Path(job["src"]), dst, job.get("start", 0), min(PART_SEC, job["length"]))
            await cq.message.answer_voice(FSInputFile(dst))
            log_event(cq.from_user.id, "voice")
        except Exception:
            logging.exception("voice failed")
            await cq.message.answer(tx(lang, "❌ Не получилось: возможно, в видео нет звука.", "❌ Didn't work: the video may have no sound."))


@dp.callback_query(F.data == "fx")
async def fx_menu(cq: CallbackQuery):
    """Меню эффектов — отдельным сообщением; в кнопках id сообщения с кружком, к которому их применять."""
    key = (cq.message.chat.id, cq.message.message_id)
    lang = lg(cq.from_user.id)
    if key not in _jobs:
        await cq.answer(gone(lang), show_alert=True)
        return
    await cq.answer()
    names = ["chipmunk", "deep", "robot", "reverse", "boomerang", "vhs", "bw"] + (["halloween"] if halloween_on() else [])
    btns = [InlineKeyboardButton(text=FX_NAMES[n][lang == "en"], callback_data=f"fx:{n}:{key[1]}") for n in names]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    rows.append([InlineKeyboardButton(text=tx(lang, "✖️ Без эффекта", "✖️ No effect"), callback_data=f"fx:none:{key[1]}")])
    await cq.message.answer(tx(lang, "🎭 Выбери эффект — переделаю кружок бесплатно:", "🎭 Pick an effect — I'll redo the circle for free:"),
                            reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))


@dp.callback_query(F.data.startswith("fx:"))
async def fx_apply(cq: CallbackQuery, bot: Bot):
    """Переделать кружок с эффектом. Лимит не тратит. fx:<эффект>[:<id сообщения с кружком>]."""
    parts = cq.data.split(":")
    name = parts[1]
    key = (cq.message.chat.id, int(parts[2]) if len(parts) > 2 else cq.message.message_id)
    lang = lg(cq.from_user.id)
    job = _jobs.get(key)
    if not job or (name not in FX_NAMES and name != "none"):
        await cq.answer(gone(lang), show_alert=True)
        return
    if name in VOICE_FX and not job.get("audio"):
        no_sound = job["kind"] != "video"
        if not no_sound and await ensure_src(bot, job):
            no_sound = not await has_audio(Path(job["src"]))
        if no_sound:
            await cq.answer(tx(lang, "В этом кружке нет звука — сначала добавь музыку 🎵", "This circle has no sound — add music first 🎵"),
                            show_alert=True)
            return
    await cq.answer(tx(lang, "⏳ Накладываю эффект...", "⏳ Applying the effect..."))
    new = dict(job, fx="" if name == "none" else name)
    if name == "halloween":
        new["fx_text"] = tx(lang, "С Хэллоуином!", "Happy Halloween!")
    async with _locks[cq.from_user.id]:
        await remake(cq, bot, key, new, f"fx_{name}")


@dp.callback_query(F.data == "remind:off")
async def remind_off(cq: CallbackQuery):
    with db() as c:
        c.execute("UPDATE users SET remind_off=1 WHERE id=?", (cq.from_user.id,))
    await cq.answer(tx(lg(cq.from_user.id), "Больше не напомню 👌", "I won't remind you again 👌"))
    await cq.message.edit_reply_markup(reply_markup=None)


async def remind_loop(bot: Bot) -> None:
    """Раз в час: тем, кто вчера (или раньше) упёрся в лимит, — одно напоминание, что бесплатные кружки снова есть.
    Не чаще раза в REMIND_EVERY, только днём, с кнопкой «Не напоминать». Заблокировавшим больше не пишем."""
    while True:
        try:
            hour = time.localtime().tm_hour
            if 9 <= hour < 21:
                today = date.today().isoformat()
                now = int(time.time())
                with db() as c:
                    rows = c.execute(
                        "SELECT id FROM users WHERE limit_day != '' AND limit_day < ? AND remind_off = 0 AND blocked = 0 "
                        "AND last_remind < ? AND premium_until < ? AND id != ?",
                        (today, now - REMIND_EVERY, now, ADMIN_ID),
                    ).fetchall()
                for (uid,) in rows:
                    lang = lg(uid)
                    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
                        text=tx(lang, "🔕 Не напоминать", "🔕 Don't remind me"), callback_data="remind:off")]])
                    try:
                        await bot.send_message(
                            uid,
                            tx(lang, f"🔵 Твои {kruzhkov(FREE_PER_DAY)} на сегодня снова доступны!\nПришли видео — сделаю кружок.",
                               f"🔵 Your {FREE_PER_DAY} free circles for today are back!\nSend a video and I'll make a circle."),
                            reply_markup=kb,
                        )
                        off = 0
                    except Exception:
                        off = 1  # заблокировал бота — больше не трогаем
                    with db() as c:
                        c.execute(
                            "UPDATE users SET limit_day='', last_remind=?, remind_off=MAX(remind_off, ?), blocked=MAX(blocked, ?) WHERE id=?",
                            (now, off, off, uid),
                        )
                    await asyncio.sleep(0.2)  # бережём лимиты Telegram
        except Exception:
            logging.exception("remind loop")
        await asyncio.sleep(3600)


START_NUDGE_AFTER = 3600  # через сколько после /start напомнить, если кружка так и не было
START_NUDGE_WINDOW = 24 * 3600  # старше суток не трогаем — это не рассылка по старым пользователям


async def start_nudge_loop(bot: Bot) -> None:
    """Раз в 10 минут: тем, кто запустил бота час–сутки назад и не сделал ни одного кружка, — одно сообщение
    «пришли видео» с подсказками, что ещё подойдёт (ссылка, фото, песня). Один раз на человека, только днём."""
    while True:
        try:
            if 9 <= time.localtime().tm_hour < 22:
                now = int(time.time())
                with db() as c:
                    rows = c.execute(
                        "SELECT id FROM users WHERE total = 0 AND start_nudge = 0 AND blocked = 0 AND id != ? "
                        "AND joined BETWEEN ? AND ?",
                        (ADMIN_ID, now - START_NUDGE_WINDOW, now - START_NUDGE_AFTER),
                    ).fetchall()
                for (uid,) in rows:
                    lang = lg(uid)
                    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(
                        text=tx(lang, "📖 Все фишки", "📖 All features"), callback_data="help")]])
                    try:
                        await bot.send_message(
                            uid,
                            tx(lang,
                               "👋 Кружок пока не сделан — а это занимает 2 секунды!\n\n"
                               "Пришли сюда любое видео из галереи — верну его кружком 🔵\n"
                               "Нет видео под рукой? Тоже подойдёт:\n"
                               "• ссылка на TikTok, YouTube Shorts или VK\n"
                               "• фото — сделаю живой кружок с наездом камеры\n"
                               "• песня (mp3) — музыкальный кружок с твоей аватаркой",
                               "👋 No circle yet — it only takes 2 seconds!\n\n"
                               "Send me any video from your gallery and I'll turn it into a circle 🔵\n"
                               "No video at hand? These work too:\n"
                               "• a TikTok, YouTube Shorts or VK link\n"
                               "• a photo — I'll make a living circle with a smooth zoom\n"
                               "• a song (mp3) — a music circle with your avatar"),
                            reply_markup=kb,
                        )
                        log_event(uid, "start_nudge")
                        off = 0
                    except Exception:
                        off = 1  # заблокировал бота
                    with db() as c:
                        c.execute("UPDATE users SET start_nudge = 1, blocked = MAX(blocked, ?) WHERE id=?", (off, uid))
                    await asyncio.sleep(0.2)
        except Exception:
            logging.exception("start nudge loop")
        await asyncio.sleep(600)


# ---------- админ ----------

@dp.message(Command("example"))
async def example(m: Message):
    """Админ смотрит, что видит новичок."""
    if m.from_user.id == ADMIN_ID:
        await send_example(m)


@dp.message(Command("reply"))
async def reply(m: Message, bot: Bot):
    """Ответ админа пользователю: /reply <id> <текст>."""
    if m.from_user.id != ADMIN_ID:
        return
    parts = (m.text or "").split(maxsplit=2)
    if len(parts) < 3 or not parts[1].isdigit():
        await m.answer("Формат: /reply <id> <текст>")
        return
    try:
        await bot.send_message(int(parts[1]), tx(lg(int(parts[1])), "💬 Ответ поддержки:", "💬 Support reply:") + f"\n{html.escape(parts[2])}")
        await m.answer("✅ Отправлено")
    except Exception as e:
        await m.answer(f"❌ Не доставлено: {html.escape(str(e))}")


@dp.message(Command("gift"))
async def gift(m: Message, bot: Bot):
    """Подарок от админа: /gift <id> <дней> — безлимит HD без метки."""
    if m.from_user.id != ADMIN_ID:
        return
    parts = (m.text or "").split()
    if len(parts) != 3 or not parts[1].isdigit() or not parts[2].isdigit():
        await m.answer("Формат: /gift <id> <дней>. id пользователя — в уведомлении о новом пользователе или в его сообщениях.")
        return
    uid, days = int(parts[1]), int(parts[2])
    with db() as c:
        if not c.execute("SELECT 1 FROM users WHERE id=?", (uid,)).fetchone():
            await m.answer("Такого пользователя нет в базе — он должен сначала нажать /start в боте.")
            return
    until = grant_days(uid, days)
    log_event(uid, "gift")
    note = ""
    try:
        await bot.send_message(
            uid,
            tx(lg(uid), f"🎁 Тебе подарили <b>безлимит HD без метки на {days} дней</b> (до {fmt_date(until)})!\n\n"
                        "Хочешь продлевать бесплатно — зови друзей: /invite",
               f"🎁 You've been gifted <b>unlimited HD with no watermark for {days} days</b> (until {fmt_date(until)})!\n\n"
               "Want to extend it for free — invite friends: /invite") + f"\n{ladder_progress(uid)}",
        )
    except Exception as e:
        note = f"\n⚠️ Сообщение не доставлено: {html.escape(str(e))}"
    await m.answer(f"✅ {uid}: безлимит до {time.strftime('%d.%m.%Y', time.localtime(until))}{note}")


@dp.message(Command("broadcast", "broadcast_en"))
async def broadcast(m: Message):
    """Рассылка: /broadcast — русскоязычным, /broadcast_en — англоязычным (можно HTML). Сначала превью, отправка — по кнопке."""
    if m.from_user.id != ADMIN_ID:
        return
    # форматирование из Telegram (жирный и т.п.) — через html_text; если его нет, теги вроде <b> можно набрать руками
    formatted = any(e.type != "bot_command" for e in (m.entities or []))
    parts = ((m.html_text if formatted else m.text) or "").split(maxsplit=1)
    if len(parts) < 2:
        await m.answer("Формат: /broadcast текст. Покажу превью и спрошу подтверждение.")
        return
    text = parts[1]
    en = parts[0].lower().startswith("/broadcast_en")
    where = "lang = 'en'" if en else "lang != 'en'"
    with db() as c:
        n = c.execute(f"SELECT COUNT(*) FROM users WHERE blocked = 0 AND id != ? AND {where}", (ADMIN_ID,)).fetchone()[0]
    _broadcast[m.from_user.id] = (text, where)
    try:
        await m.answer(text)
    except Exception as e:
        await m.answer(f"❌ Текст не отправляется: {html.escape(str(e))}")
        return
    await m.answer(f"👆 Так увидят пользователи ({'англоязычные' if en else 'русскоязычные'}). Отправить {n} людям?", reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"✅ Отправить ({n})", callback_data="bc:go"),
        InlineKeyboardButton(text="✖ Отмена", callback_data="bc:no"),
    ]]))


@dp.callback_query(F.data.startswith("bc:"))
async def broadcast_go(cq: CallbackQuery, bot: Bot):
    if cq.from_user.id != ADMIN_ID:
        return
    item = _broadcast.pop(cq.from_user.id, None)
    await cq.message.edit_reply_markup(reply_markup=None)
    if cq.data == "bc:no" or not item:
        await cq.answer("Отменено")
        return
    await cq.answer("Рассылаю...")
    text, where = item

    async def run():
        with db() as c:
            ids = [r[0] for r in c.execute(f"SELECT id FROM users WHERE blocked = 0 AND id != ? AND {where}", (ADMIN_ID,))]
        ok = bad = 0
        for uid in ids:
            try:
                await bot.send_message(uid, text)
                ok += 1
            except TelegramForbiddenError:
                bad += 1
                with db() as c:
                    c.execute("UPDATE users SET blocked = 1 WHERE id=?", (uid,))
            except Exception:
                bad += 1
                logging.exception("broadcast %s", uid)
            await asyncio.sleep(0.07)  # ~15 сообщений в секунду — в пределах лимитов Telegram
        await bot.send_message(ADMIN_ID, f"📣 Рассылка готова: доставлено {ok}, не доставлено {bad}.")

    asyncio.create_task(run())


# ---------- текст ----------

@dp.message(F.text)
async def on_text(m: Message, bot: Bot):
    uid = m.from_user.id
    text = m.text or ""
    if uid in _await_text and (text.startswith("/") or URL_RE.search(text)):
        _await_text.pop(uid)  # передумал с надписью — команду или ссылку обрабатываем как обычно
    if uid in _await_text:
        key = _await_text.pop(uid)
        job = _jobs.get(key)
        if not job:
            await m.answer(gone(lg(uid)))
            return
        label = "" if text.strip() in ("-", "—") else text.strip().strip("«»\"“”")[:60]
        async with _locks[uid]:
            u = get_user(uid)
            mark = needs_mark(u)
            new = dict(job, text=label)
            await bot.send_chat_action(m.chat.id, "record_video_note")
            try:
                if not await ensure_src(bot, new):
                    raise RuntimeError("source lost")
                with tempfile.TemporaryDirectory() as tmp:
                    dst = Path(tmp) / "out.mp4"
                    await render(new, dst, mark, not mark)
                    await m.answer_video_note(FSInputFile(dst), length=512 if mark else 640)
                _jobs[key] = new
                log_event(uid, "text")
            except Exception:
                logging.exception("text failed")
                await m.answer(tx(lg(uid), "❌ Не получилось добавить надпись. Пришли видео ещё раз.", "❌ Couldn't add the text. Please send the video again."))
        return
    url = URL_RE.search(text)
    if url and "t.me/" not in url.group(0):
        await convert_link(m, bot, url.group(0))
        return
    if text.startswith("/"):
        await m.answer(help_text(lg(uid)))
        return
    # текст от пользователя пересылаем админу — иначе вопросы в поддержку теряются
    if ADMIN_ID and uid != ADMIN_ID:
        await bot.send_message(
            ADMIN_ID,
            f"✉️ {who(m)}:\n{html.escape(text)}\n\nОтветить: <code>/reply {uid} текст</code>",
        )
        await m.answer(tx(lg(uid), "Сообщение передано, ответим здесь же 🙌\nА если нужен кружок — пришли видео, ссылку, фото или песню 🎬",
                          "Message forwarded, we'll reply right here 🙌\nNeed a circle? Send a video, link, photo or song 🎬"))


@dp.message()
async def fallback(m: Message):
    await m.answer(tx(lg(m.from_user.id), "Пришли мне видео, ссылку на видео, фото или песню 🎬 — сделаю кружок. Все фишки — /help",
                      "Send me a video, a video link, a photo or a song 🎬 — I'll make a circle. All features — /help"))


@dp.message.outer_middleware()
@dp.callback_query.outer_middleware()
async def remember_language(handler, event, data):
    """Запоминаем language_code из Telegram — по нему выбираем язык новым пользователям."""
    user = getattr(event, "from_user", None)
    if user and user.language_code:
        _codes[user.id] = user.language_code
    return await handler(event, data)


EN_NAME = "Video to Circle 🔵 Round video maker"
EN_SHORT = "Turn any video, link, photo or song into a Telegram video circle (round video message). 3 a day free."
EN_DESC = (
    "🔵 Turn any video into a Telegram video circle (round video message) in seconds.\n\n"
    "• Video, TikTok / YouTube Shorts link, photo or song → circle\n"
    "• Add music or text to your circle\n"
    "• Long videos → several circles in a row\n"
    "• Pick any piece: caption 0:45 or 0:45-1:20\n"
    "• Circle → normal video to save to your gallery\n"
    "• Effects: chipmunk voice, reverse, boomerang, VHS 🎭\n\n"
    "3 circles a day free. HD without watermark — with Telegram Stars."
)


async def setup_english_profile(bot: Bot) -> None:
    """Имя и описание бота для англоязычных — меняем, только если отличаются (у Telegram жёсткие лимиты на эти вызовы)."""
    try:
        if (await bot.get_my_name(language_code="en")).name != EN_NAME:
            await bot.set_my_name(name=EN_NAME, language_code="en")
        if (await bot.get_my_short_description(language_code="en")).short_description != EN_SHORT:
            await bot.set_my_short_description(short_description=EN_SHORT, language_code="en")
        if (await bot.get_my_description(language_code="en")).description != EN_DESC:
            await bot.set_my_description(description=EN_DESC, language_code="en")
    except Exception:
        logging.exception("english profile")


async def main():
    init_db()
    from aiogram.client.default import DefaultBotProperties
    session = None
    if API_SERVER:
        from aiogram.client.session.aiohttp import AiohttpSession
        from aiogram.client.telegram import TelegramAPIServer
        session = AiohttpSession(api=TelegramAPIServer.from_base(API_SERVER, is_local=True))
    bot = Bot(BOT_TOKEN, session=session, default=DefaultBotProperties(parse_mode="HTML"))
    try:
        await bot.set_my_commands([
            BotCommand(command="start", description="Начать"),
            BotCommand(command="help", description="Все фишки бота"),
            BotCommand(command="premium", description="HD без метки и лимитов"),
            BotCommand(command="invite", description="Бонусы за друзей"),
            BotCommand(command="lang", description="Язык / Language"),
        ])
        await bot.set_my_commands([
            BotCommand(command="start", description="Start"),
            BotCommand(command="help", description="All features"),
            BotCommand(command="premium", description="HD, no watermark, no limits"),
            BotCommand(command="invite", description="Bonuses for friends"),
            BotCommand(command="lang", description="Language / Язык"),
        ], language_code="en")
        await setup_english_profile(bot)
    except Exception:
        logging.exception("set_my_commands")
    reminder = asyncio.create_task(remind_loop(bot))  # noqa: F841 — держим ссылку, чтобы задачу не собрал GC
    newbie = asyncio.create_task(start_nudge_loop(bot))  # noqa: F841
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())

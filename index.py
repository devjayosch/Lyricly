import asyncio
import ctypes
import json
import msvcrt
import os
import re
import shutil
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from bisect import bisect_right
from datetime import datetime, timezone

if sys.platform != "win32":
    sys.exit("this version is for Windows only")

try:
    from winrt.windows.media.control import (
        GlobalSystemMediaTransportControlsSessionManager as MediaManager,
        GlobalSystemMediaTransportControlsSessionPlaybackStatus as PlaybackStatus,
    )
except ImportError:
    sys.exit(
        "missing packages. run:\n"
        "  pip install winrt-runtime winrt-Windows.Media.Control "
        "winrt-Windows.Foundation winrt-Windows.Foundation.Collections"
    )

UA = "term-lyrics/1.0 (personal use)"
API = "https://lrclib.net/api"
TS = re.compile(r"\[(\d+):(\d+(?:\.\d+)?)\]")
MARGIN = 2
POLL_INTERVAL = 0.5
BASE_OFFSET = float(os.environ.get("LYRICS_OFFSET", "0"))

RESET = "\x1b[0m"
BOLD = "\x1b[1m"
DIMC = "\x1b[38;5;243m"
REV = "\x1b[7m"

HELP = [
    ("j / k", "adjust lyric offset (-/+ 0.25s)"),
    ("left / right", "seek -/+ 5 seconds"),
    ("space", "play / pause"),
    ("n / p", "next / previous track"),
    ("up / down  + / -", "volume up / down"),
    ("m", "mute"),
    ("u", "toggle UI bar"),
    ("b", "toggle bold on current line"),
    ("c", "toggle centered lyrics"),
    ("U", "toggle uppercase current line"),
    ("i", "toggle dim inactive lines"),
    ("/", "search for lyrics manually"),
    ("r", "retry lyrics fetch"),
    ("?", "show help overlay"),
    ("q / esc", "quit"),
]

VK_VOLUME_MUTE, VK_VOLUME_DOWN, VK_VOLUME_UP = 0xAD, 0xAE, 0xAF


def fmt_time(sec):
    sec = max(0, int(sec))
    return f"{sec // 60}:{sec % 60:02d}"


def get_json(path, params, timeout=5):
    url = f"{API}/{path}?{urllib.parse.urlencode(params)}"
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise


def parse_lrc(raw):
    out = []
    for line in raw.splitlines():
        stamps = TS.findall(line)
        if not stamps:
            continue
        text = TS.sub("", line).strip()
        for m, s in stamps:
            out.append((int(m) * 60 + float(s), text))
    out.sort(key=lambda x: x[0])
    return out


def pick(results, dur):
    cands = [r for r in results if r.get("syncedLyrics")]
    if not cands:
        return None
    if dur:
        cands.sort(key=lambda r: abs((r.get("duration") or 0) - dur))
    return cands[0]


def run_jobs(jobs, dur):
    n = len(jobs)
    results = [None] * n
    done = [threading.Event() for _ in jobs]

    def work(i, path, params):
        try:
            results[i] = ("ok", get_json(path, params))
        except (OSError, ValueError):
            results[i] = ("err", None)
        done[i].set()

    for i, (path, params, _) in enumerate(jobs):
        threading.Thread(target=work, args=(i, path, params), daemon=True).start()

    def evaluate(i):
        kind, r = results[i]
        if kind == "err":
            return None
        if jobs[i][2]:
            r = pick(r or [], dur)
        if r and r.get("syncedLyrics"):
            return parse_lrc(r["syncedLyrics"])
        return None

    skipped = []
    for i in range(n):
        if done[i].wait(1.5):
            lines = evaluate(i)
            if lines:
                return lines, "ok"
        else:
            skipped.append(i)
    for i in skipped:
        done[i].wait(6)
        if results[i] is not None:
            lines = evaluate(i)
            if lines:
                return lines, "ok"
    if all(r is not None and r[0] == "err" for r in results):
        return [], "error"
    return [], "none"


def fetch_auto(artist, title, album, dur):
    clean = re.sub(r"\s*[\(\[].*?[\)\]]|\s+-\s+.*$", "", title).strip() or title
    first_artist = re.split(r",|&|\sfeat\.?\s|\sft\.?\s", artist)[0].strip() or artist
    full = {"artist_name": artist, "track_name": title, "album_name": album,
            "duration": int(dur) if dur else None}
    full = {k: v for k, v in full.items() if v}
    jobs = [
        ("get-cached", full, False),
        ("get", full, False),
        ("search", {"track_name": title, "artist_name": artist}, True),
        ("search", {"track_name": clean, "artist_name": first_artist}, True),
        ("search", {"q": f"{clean} {first_artist}"}, True),
    ]
    return run_jobs(jobs, dur)


def fetch_manual(query, dur):
    return run_jobs([("search", {"q": query}, True)], dur)


def press_media_key(vk, times=1):
    user32 = ctypes.windll.user32
    for _ in range(times):
        user32.keybd_event(vk, 0, 0, 0)
        user32.keybd_event(vk, 0, 2, 0)


def enable_vt():
    k32 = ctypes.windll.kernel32
    for std in (-11, -12):
        h = k32.GetStdHandle(std)
        mode = ctypes.c_ulong()
        if k32.GetConsoleMode(h, ctypes.byref(mode)):
            k32.SetConsoleMode(h, mode.value | 0x0004)
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass


def read_key():
    if not msvcrt.kbhit():
        return None
    ch = msvcrt.getwch()
    if ch in ("\x00", "\xe0"):
        code = msvcrt.getwch()
        return {"K": "LEFT", "M": "RIGHT", "H": "UP", "P": "DOWN"}.get(code, "")
    if ch in ("\x03", "\x1b"):
        return "ESC"
    if ch in ("\r", "\n"):
        return "ENTER"
    if ch in ("\x08", "\x7f"):
        return "BACKSPACE"
    return ch


class App:
    def __init__(self):
        self.lock = threading.RLock()
        self.running = True

        self.session = None
        self.app_id = None
        self.status = "Stopped"
        self.pos = 0.0
        self.stamp = time.monotonic()
        self.dur = 0.0
        self.artist = self.title = self.album = ""

        self.lines = []
        self.times = []
        self.lstate = "idle"
        self.gen = 0
        self.track_key = None
        self.offset = BASE_OFFSET

        self.ui = True
        self.bold = True
        self.center = False
        self.upper = False
        self.dim = True
        self.show_help = False
        self.searching = False
        self.query = ""
        self.msg = ""
        self.msg_until = 0.0

        self.prev_rows = []
        self.prev_size = (0, 0)

        self.loop = asyncio.new_event_loop()
        self.wake = None
        threading.Thread(target=self.loop.run_forever, daemon=True).start()
        asyncio.run_coroutine_threadsafe(self.poll(), self.loop)

    async def poll(self):
        flt = os.environ.get("LYRICS_APP", "").lower()
        self.wake = asyncio.Event()
        mgr = await MediaManager.request_async()
        while self.running:
            try:
                cands = list(mgr.get_sessions())
                if flt:
                    cands = [s for s in cands
                             if flt in (s.source_app_user_model_id or "").lower()]
                playing = [s for s in cands
                           if s.get_playback_info().playback_status == PlaybackStatus.PLAYING]
                sess = None
                for s in playing:
                    if s.source_app_user_model_id == self.app_id:
                        sess = s
                        break
                if sess is None:
                    sess = playing[0] if playing else (cands[0] if cands else None)

                if sess is None:
                    with self.lock:
                        self.session, self.status = None, "Stopped"
                        self.title = self.artist = self.album = ""
                else:
                    info = await sess.try_get_media_properties_async()
                    pb = sess.get_playback_info()
                    tl = sess.get_timeline_properties()
                    is_playing = pb.playback_status == PlaybackStatus.PLAYING
                    pos = tl.position.total_seconds()
                    dur = tl.end_time.total_seconds()
                    if is_playing:
                        try:
                            delta = (datetime.now(timezone.utc) - tl.last_updated_time).total_seconds()
                            if 0 <= delta <= (dur + 5 if dur else 3600):
                                pos += delta
                        except Exception:
                            pass
                    with self.lock:
                        self.session = sess
                        self.app_id = sess.source_app_user_model_id
                        self.status = "Playing" if is_playing else "Paused"
                        self.pos, self.stamp, self.dur = pos, time.monotonic(), dur
                        self.title = info.title or ""
                        self.artist = info.artist or ""
                        self.album = info.album_title or ""
            except Exception:
                with self.lock:
                    self.status = "Stopped"
            try:
                await asyncio.wait_for(self.wake.wait(), POLL_INTERVAL)
            except asyncio.TimeoutError:
                pass
            self.wake.clear()

    def submit(self, fn, settle=0.3):
        async def go():
            s = self.session
            if s is None:
                return
            try:
                await fn(s)
            except Exception:
                pass
            await asyncio.sleep(settle)
            if self.wake is not None:
                self.wake.set()
        asyncio.run_coroutine_threadsafe(go(), self.loop)

    def _pos(self):
        with self.lock:
            p = self.pos
            if self.status == "Playing":
                p += time.monotonic() - self.stamp
            return min(p, self.dur) if self.dur else p

    def flash(self, text, secs=2.0):
        self.msg, self.msg_until = text, time.monotonic() + secs

    def seek(self, d):
        target = max(0.0, self._pos() + d)
        if self.dur:
            target = min(target, self.dur)
        self.submit(lambda s: s.try_change_playback_position_async(int(target * 10_000_000)))
        with self.lock:
            self.pos, self.stamp = target, time.monotonic()

    def change_volume(self, up):
        press_media_key(VK_VOLUME_UP if up else VK_VOLUME_DOWN, times=2)
        self.flash("volume " + ("up" if up else "down"))

    def start_fetch(self, manual=None):
        with self.lock:
            self.gen += 1
            g = self.gen
            self.lstate = "loading"
            self.lines, self.times = [], []
            artist, title, album, dur = self.artist, self.title, self.album, self.dur

        def worker():
            if manual:
                lines, state = fetch_manual(manual, dur)
            else:
                lines, state = fetch_auto(artist, title, album, dur)
            with self.lock:
                if g == self.gen:
                    self.lines, self.times = lines, [t for t, _ in lines]
                    self.lstate = state

        threading.Thread(target=worker, daemon=True).start()

    def check_track(self):
        with self.lock:
            key = (self.title, self.artist) if self.title else None
        if key != self.track_key:
            self.track_key = key
            self.offset = BASE_OFFSET
            if key:
                self.start_fetch()
            else:
                with self.lock:
                    self.gen += 1
                    self.lines, self.times, self.lstate = [], [], "idle"

    def handle(self, ch):
        if self.searching:
            if ch == "ENTER":
                q = self.query.strip()
                self.searching = False
                if q:
                    self.start_fetch(manual=q)
            elif ch == "ESC":
                self.searching = False
            elif ch == "BACKSPACE":
                self.query = self.query[:-1]
            elif len(ch) == 1 and ch.isprintable():
                self.query += ch
            return True

        if self.show_help:
            if ch in ("?", "ESC", "q"):
                self.show_help = False
            return True

        if ch in ("q", "ESC"):
            return False
        if ch == "j":
            self.offset -= 0.25
        elif ch == "k":
            self.offset += 0.25
        elif ch == "LEFT":
            self.seek(-5)
        elif ch == "RIGHT":
            self.seek(5)
        elif ch == " ":
            self.submit(lambda s: s.try_toggle_play_pause_async())
        elif ch in ("n", ">"):
            self.submit(lambda s: s.try_skip_next_async(), settle=0.6)
        elif ch in ("p", "<"):
            self.submit(lambda s: s.try_skip_previous_async(), settle=0.6)
        elif ch in ("UP", "+", "="):
            self.change_volume(True)
        elif ch in ("DOWN", "-"):
            self.change_volume(False)
        elif ch == "m":
            press_media_key(VK_VOLUME_MUTE)
            self.flash("mute toggled")
        elif ch == "u":
            self.ui = not self.ui
        elif ch == "b":
            self.bold = not self.bold
        elif ch == "c":
            self.center = not self.center
        elif ch == "U":
            self.upper = not self.upper
        elif ch == "i":
            self.dim = not self.dim
        elif ch == "/":
            self.searching, self.query = True, ""
        elif ch == "r":
            if self.title:
                self.start_fetch()
        elif ch == "?":
            self.show_help = True
        return True

    def draw(self):
        cols, rows = shutil.get_terminal_size((100, 30))
        w, h = max(20, cols - 1), max(6, rows)
        if (cols, rows) != self.prev_size:
            self.prev_size = (cols, rows)
            self.prev_rows = []
            sys.stdout.write("\x1b[2J")
        grid = [[(" ", "")] * w for _ in range(h)]

        def put(y, x, s, style=""):
            if not 0 <= y < h:
                return
            row = grid[y]
            for i, chn in enumerate(s):
                if 0 <= x + i < w:
                    row[x + i] = (chn, style)

        avail = max(1, w - 2 * MARGIN)
        pos = self._pos()
        t = pos + self.offset
        with self.lock:
            title, artist, status, dur = self.title, self.artist, self.status, self.dur
            lines, times, lstate = self.lines, self.times, self.lstate

        top = 1
        if self.ui:
            head = title or "nothing playing"
            if artist:
                head += f"  \u2014  {artist}"
            put(1, MARGIN, head[:avail])
            tag = []
            if self.offset:
                tag.append(f"offset {self.offset:+.2f}s")
            if status == "Paused":
                tag.append("paused")
            if tag:
                s = "  ".join(tag)
                put(1, w - MARGIN - len(s), s, DIMC)
            left, right = fmt_time(pos), fmt_time(dur)
            put(2, MARGIN, left)
            bx = MARGIN + len(left) + 1
            bw = max(1, w - MARGIN - len(right) - 1 - bx)
            filled = int(bw * (pos / dur)) if dur else 0
            put(2, bx, "\u2500" * bw, DIMC)
            if filled:
                put(2, bx, "\u2500" * min(filled, bw), BOLD)
            put(2, w - MARGIN - len(right), right)
            top = 4
        bottom = h - 2

        if bottom > top:
            if lstate != "ok" or not lines:
                if status == "Stopped" and not title:
                    text = "no player found. play something in your browser"
                else:
                    text = {
                        "idle": "",
                        "loading": "fetching lyrics",
                        "none": "no synced lyrics found. press / to search, r to retry",
                        "error": "network error. press r to retry",
                    }.get(lstate, "")
                y = top + (bottom - top) // 2
                x = MARGIN + (max(0, avail - len(text)) // 2 if self.center else 0)
                put(y, x, text[:avail], DIMC)
            else:
                idx = bisect_right(times, t) - 1
                cur_y = top + int((bottom - top) * 0.55)
                first = idx - (cur_y - top)
                last = idx + (bottom - 1 - cur_y)
                for i in range(max(0, first), min(len(lines), last + 1)):
                    y = cur_y + (i - idx)
                    text = lines[i][1]
                    cur = i == idx
                    if cur:
                        if self.upper:
                            text = text.upper()
                        text = "\u276f " + (text or "\u266a")
                        style = BOLD if self.bold else ""
                    else:
                        style = DIMC if self.dim else ""
                    if len(text) > avail:
                        text = text[: avail - 1] + "\u2026"
                    x = MARGIN + (max(0, avail - len(text)) // 2 if self.center else 0)
                    put(y, x, text, style)

        if self.searching:
            put(h - 1, MARGIN, "/ " + self.query, BOLD)
            put(h - 1, MARGIN + 2 + len(self.query), " ", REV)
        elif self.msg and time.monotonic() < self.msg_until:
            put(h - 1, MARGIN, self.msg, DIMC)

        if self.show_help:
            kw = max(len(k) for k, _ in HELP)
            dw = max(len(d) for _, d in HELP)
            bw_, bh = kw + dw + 7, len(HELP) + 4
            x0, y0 = max(0, (w - bw_) // 2), max(0, (h - bh) // 2)
            put(y0, x0, "\u250c" + "\u2500" * (bw_ - 2) + "\u2510")
            for r in range(1, bh - 1):
                put(y0 + r, x0, "\u2502" + " " * (bw_ - 2) + "\u2502")
            put(y0 + bh - 1, x0, "\u2514" + "\u2500" * (bw_ - 2) + "\u2518")
            put(y0 + 1, x0 + 3, "keys", BOLD)
            for r, (k, d) in enumerate(HELP):
                put(y0 + 2 + r, x0 + 3, k.ljust(kw), BOLD)
                put(y0 + 2 + r, x0 + 5 + kw, d, DIMC)

        out = []
        new_rows = []
        for y, cells in enumerate(grid):
            parts, cur_style = [], None
            for chn, st in cells:
                if st != cur_style:
                    parts.append(RESET + st)
                    cur_style = st
                parts.append(chn)
            parts.append(RESET)
            rs = "".join(parts)
            new_rows.append(rs)
            if y >= len(self.prev_rows) or self.prev_rows[y] != rs:
                out.append(f"\x1b[{y + 1};1H{rs}")
        self.prev_rows = new_rows
        if out:
            sys.stdout.write("".join(out))
            sys.stdout.flush()


def main():
    enable_vt()
    app = App()
    sys.stdout.write("\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[2J")
    sys.stdout.flush()
    try:
        while True:
            app.check_track()
            quit_ = False
            while True:
                ch = read_key()
                if ch is None:
                    break   
                if ch == "":
                    continue
                if not app.handle(ch):
                    quit_ = True
                    break
            if quit_:
                break
            app.draw()
            time.sleep(0.05)
    except KeyboardInterrupt:
        pass
    finally:
        app.running = False
        sys.stdout.write(RESET + "\x1b[?7h\x1b[?25h\x1b[?1049l")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
#!/usr/bin/env python3
"""ppg_harvest.py - recolecta direcciones @ppg.com (y subdominios) publicadas en la web.

Descubrimiento : seeds + enlaces, sitemap.xml recursivo (--sitemap), Common Crawl (--cc)
Extraccion     : mailto:, texto plano, HTML (entidades), ofuscaciones, PDFs (--pdf)
Almacenamiento : SQLite (email UNIQUE) + exportacion CSV (email, source_url, first_seen)
Cortesia       : robots.txt por host, Crawl-delay, retardo por host, concurrencia limitada

Instalacion:  pip install "httpx>=0.27" "selectolax>=0.3.21" "pypdf>=4.2"
Ejemplo    :  python ppg_harvest.py --seeds https://www.ppg.com --sitemap --cc --pdf \
                  --max-pages 2000 --concurrency 8 --delay 1.0
"""
from __future__ import annotations

import argparse
import asyncio
import csv
import html
import io
import json
import logging
import re
import sqlite3
import sys
import time
import zlib
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Optional
from urllib import robotparser
from urllib.parse import unquote, urldefrag, urljoin, urlsplit, urlunsplit

import httpx
from pypdf import PdfReader
from selectolax.lexbor import LexborHTMLParser as HTMLParser

VERSION = "1.0"
TARGET_DOMAIN = "ppg.com"
DEFAULT_SEED = "https://www.ppg.com/"
COLLINFO_URL = "https://index.commoncrawl.org/collinfo.json"

HTML_MAX_BYTES = 5 * 1024 * 1024
PDF_MAX_BYTES = 30 * 1024 * 1024
SITEMAP_MAX_BYTES = 50 * 1024 * 1024
PDF_MAX_PAGES = 300
MAX_REDIRECTS = 5
MAX_RETRIES = 2
MAX_URL_LEN = 2000
MAX_SITEMAPS = 500
MAX_SITEMAP_LEVEL = 6
SITEMAP_URL_CAP = 200_000
MAX_CRAWL_DELAY = 30.0
REDIRECT_CODES = {301, 302, 303, 307, 308}

STATUS_PENDING, STATUS_DONE, STATUS_ERROR = 0, 1, 2

SKIP_EXT = {
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico", ".bmp", ".tif", ".tiff",
    ".css", ".js", ".map", ".woff", ".woff2", ".ttf", ".eot", ".otf",
    ".mp3", ".mp4", ".avi", ".mov", ".wmv", ".webm", ".m4a", ".wav", ".flac",
    ".zip", ".gz", ".tgz", ".tar", ".rar", ".7z", ".exe", ".dmg", ".msi", ".iso", ".bin", ".apk",
    ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".xml", ".rss", ".atom",
}

log = logging.getLogger("ppg_harvest")


# --------------------------------------------------------------------------- #
# Extraccion y desofuscacion de correos
# --------------------------------------------------------------------------- #

_LOCAL = r"[A-Za-z0-9_%+\-]+"
_LB = r"(?<![A-Za-z0-9._%+\-])"
_TAIL = r"(?![A-Za-z0-9\-])(?!\.[A-Za-z0-9])"
_ATW = r"(?:at|arroba)"
_DOTW = r"(?:dot|punto)"
_DOT_SEP = rf"(?:\.|\s+{_DOTW}\s+)"
_LOCAL_W = rf"(?:{_LOCAL}{_DOT_SEP})*{_LOCAL}"
_TAIL_W = rf"(?![A-Za-z0-9\-])(?!\.[A-Za-z0-9])(?!\s+{_DOTW}\s+[A-Za-z0-9])"

EMAIL_RE = re.compile(
    rf"{_LB}([A-Za-z0-9._%+\-]+)@((?:[A-Za-z0-9\-]+\.)*ppg\.com){_TAIL}", re.I
)
# "nombre@ppg dot com", "nombre dot apellido@ppg.com"
OBF_AT_RE = re.compile(
    rf"{_LB}{_LOCAL_W}\s*@\s*(?:[A-Za-z0-9\-]+{_DOT_SEP})*ppg{_DOT_SEP}com{_TAIL_W}", re.I
)
# "nombre at ppg dot com": el "at" en palabra exige "dot" en palabra (evita "look at ppg.com")
OBF_WORD_RE = re.compile(
    rf"{_LB}{_LOCAL_W}\s+{_ATW}\s+(?:[A-Za-z0-9\-]+\s+{_DOTW}\s+)*ppg\s+{_DOTW}\s+com{_TAIL_W}",
    re.I,
)
AT_BRACKET_RE = re.compile(r"\s*[\(\[\{<]\s*(?:at|arroba)\s*[\)\]\}>]\s*", re.I)
DOT_BRACKET_RE = re.compile(r"\s*[\(\[\{<]\s*(?:dot|punto)\s*[\)\]\}>]\s*", re.I)
_DOTW_SUB = re.compile(rf"\s+{_DOTW}\s+", re.I)
_ATW_SUB = re.compile(rf"\s+{_ATW}\s+|\s*@\s*", re.I)
JS_UNICODE_RE = re.compile(r"\\u([0-9a-fA-F]{4})")
URL_ENC_SEP_RE = re.compile(r"%(?:0[AaDd]|20|22|27|2[Cc]|3[AaBbCcDdEe])")
PPG_RE = re.compile(r"ppg", re.I)
LOC_RE = re.compile(r"<loc>\s*(?:<!\[CDATA\[)?\s*(.*?)\s*(?:\]\]>)?\s*</loc>", re.I | re.S)


def _canon(m: re.Match) -> str:
    s = _DOTW_SUB.sub(".", m.group(0))
    s = _ATW_SUB.sub("@", s, count=1)
    return f" {s} "


def _clean_email(local: str, domain: str) -> Optional[str]:
    # Quita separadores iniciales/finales ("-", "+", "." ...): evita falsos prefijos
    # y valores que un CSV/Excel interpretaria como formula.
    local = local.lstrip("._%+-").rstrip(".")
    if not local or len(local) > 64 or ".." in local:
        return None
    return f"{local}@{domain}".lower()


def find_emails(text: str) -> set[str]:
    """Devuelve los correos @ppg.com (incluye subdominios) presentes en `text`."""
    out: set[str] = set()
    if not text:
        return out
    t = text
    for _ in range(2):  # entidades HTML, incluso doblemente codificadas
        if "&" not in t:
            break
        u = html.unescape(t)
        if u == t:
            break
        t = u
    if "\\u" in t:
        t = JS_UNICODE_RE.sub(lambda m: chr(int(m.group(1), 16)), t)
    if "%" in t:
        t = t.replace("%40", "@")
        t = URL_ENC_SEP_RE.sub(" ", t)
    if not PPG_RE.search(t):
        return out

    # Trabaja solo en ventanas alrededor de cada "ppg" (rapido en paginas enormes).
    spans: list[list[int]] = []
    for m in PPG_RE.finditer(t):
        s, e = max(0, m.start() - 150), min(len(t), m.end() + 60)
        if spans and s <= spans[-1][1]:
            spans[-1][1] = e
        else:
            spans.append([s, e])
    for s, e in spans:
        w = t[s:e]
        w = AT_BRACKET_RE.sub("@", w)
        w = DOT_BRACKET_RE.sub(" dot ", w)
        w = OBF_AT_RE.sub(_canon, w)
        w = OBF_WORD_RE.sub(_canon, w)
        for m in EMAIL_RE.finditer(w):
            email = _clean_email(m.group(1), m.group(2))
            if email:
                out.add(email)
    return out


def decode_cfemail(hexstr: str) -> str:
    """Decodifica la proteccion de correo de Cloudflare (data-cfemail)."""
    try:
        raw = bytes.fromhex(hexstr.strip())
        key = raw[0]
        return bytes(c ^ key for c in raw[1:]).decode("utf-8", "ignore")
    except (ValueError, IndexError):
        return ""


@dataclass
class ParsedPage:
    emails: set[str] = field(default_factory=set)
    links: list[str] = field(default_factory=list)
    follow: bool = True


def _mailto_emails(href: str) -> set[str]:
    out: set[str] = set()
    addr = unquote(href[7:]).split("?", 1)[0]
    for part in re.split(r"[,;]", addr):
        out |= find_emails(part)
    return out


def parse_html(body: str, url: str) -> ParsedPage:
    page = ParsedPage()
    if not body.strip():
        return page
    page.emails |= find_emails(body)  # crudo: atributos, scripts, JSON embebido
    tree = HTMLParser(body)
    try:
        page.emails |= find_emails(tree.text(separator=" "))  # texto visible
    except Exception:  # noqa: BLE001 - un nodo raro no debe tirar la pagina
        pass

    base = url
    base_node = tree.css_first("base[href]")
    if base_node is not None:
        base = urljoin(url, (base_node.attributes.get("href") or "").strip()) or url

    for meta in tree.css("meta[name]"):
        name = (meta.attributes.get("name") or "").lower()
        content = (meta.attributes.get("content") or "").lower()
        if name in ("robots", "ppg-harvest") and ("nofollow" in content or "none" in content):
            page.follow = False

    for node in tree.css("[data-cfemail]"):
        page.emails |= find_emails(decode_cfemail(node.attributes.get("data-cfemail") or ""))

    for node in tree.css("a[href], area[href], iframe[src], frame[src]"):
        attrs = node.attributes
        ref = (attrs.get("href") or attrs.get("src") or "").strip()
        low = ref.lower()
        if not ref:
            continue
        if low.startswith("mailto:"):
            page.emails |= _mailto_emails(ref)
        elif "email-protection#" in low:
            page.emails |= find_emails(decode_cfemail(ref.split("#", 1)[1]))
        elif low.startswith(("javascript:", "tel:", "data:", "sms:", "#")):
            continue
        else:
            page.links.append(urljoin(base, ref))
    return page


def extract_pdf_emails(data: bytes) -> set[str]:
    """Extrae correos del texto de un PDF y de sus anotaciones mailto:."""
    out: set[str] = set()
    try:
        reader = PdfReader(io.BytesIO(data), strict=False)
        if reader.is_encrypted and not reader.decrypt(""):
            return out
        for i, page in enumerate(reader.pages):
            if i >= PDF_MAX_PAGES:
                break
            try:
                out |= find_emails(page.extract_text() or "")
            except Exception:  # noqa: BLE001
                pass
            try:
                for annot in page.get("/Annots") or []:
                    action = annot.get_object().get("/A")
                    uri = action.get_object().get("/URI") if action else None
                    if uri and str(uri).lower().startswith("mailto:"):
                        out |= _mailto_emails(str(uri))
            except Exception:  # noqa: BLE001
                pass
        try:
            for value in (reader.metadata or {}).values():
                out |= find_emails(str(value))
        except Exception:  # noqa: BLE001
            pass
    except Exception as exc:  # noqa: BLE001 - PDF corrupto/cifrado: se ignora
        log.debug("PDF ilegible: %s", exc)
    return out


# --------------------------------------------------------------------------- #
# URLs
# --------------------------------------------------------------------------- #

def normalize_url(raw: str, base: Optional[str] = None) -> Optional[str]:
    try:
        raw = raw.strip()
        if base:
            raw = urljoin(base, raw)
        raw, _ = urldefrag(raw)
        p = urlsplit(raw)
        scheme = p.scheme.lower()
        host = (p.hostname or "").lower().rstrip(".")
        if scheme not in ("http", "https") or not host:
            return None
        port = p.port
    except ValueError:
        return None
    if ":" in host:
        host = f"[{host}]"
    default = 443 if scheme == "https" else 80
    netloc = host if port in (None, default) else f"{host}:{port}"
    url = urlunsplit((scheme, netloc, p.path or "/", p.query, ""))
    return url if len(url) <= MAX_URL_LEN else None


def has_skipped_ext(url: str, allow_pdf: bool) -> bool:
    path = urlsplit(url).path.lower()
    dot = path.rfind(".")
    if dot == -1 or "/" in path[dot:]:
        return False
    ext = path[dot:]
    if ext == ".pdf":
        return not allow_pdf
    return ext in SKIP_EXT


def strip_www(host: str) -> str:
    return host[4:] if host.startswith("www.") else host


def classify(ctype: str, url: str) -> Optional[str]:
    path = urlsplit(url).path.lower()
    if "pdf" in ctype or (ctype in ("", "application/octet-stream") and path.endswith(".pdf")):
        return "pdf"
    if ctype in ("", "text/html", "application/xhtml+xml"):
        return "html"
    if ctype.startswith("text/") or ctype.endswith("+xml") or ctype in (
        "application/xml", "application/json"
    ):
        return "text"
    return None


def decode_body(body: bytes, content_type: str) -> str:
    m = re.search(r"charset=\"?([\w\-]+)", content_type, re.I)
    for enc in ([m.group(1)] if m else []) + ["utf-8"]:
        try:
            return body.decode(enc)
        except (LookupError, UnicodeDecodeError):
            continue
    return body.decode("latin-1", errors="replace")


def gunzip_capped(data: bytes, cap: int) -> bytes:
    d = zlib.decompressobj(16 + zlib.MAX_WBITS)
    out = d.decompress(data, cap)
    return out


# --------------------------------------------------------------------------- #
# Almacenamiento
# --------------------------------------------------------------------------- #

class Store:
    def __init__(self, path: str):
        Path(path).expanduser().resolve().parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(path)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS emails (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                email TEXT NOT NULL UNIQUE,
                source_url TEXT NOT NULL,
                first_seen TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS urls (
                url TEXT PRIMARY KEY,
                depth INTEGER NOT NULL,
                status INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
            """
        )
        self.conn.commit()
        self._dirty = 0

    def reset_crawl_state(self) -> None:
        self.conn.execute("DELETE FROM urls")
        self.conn.execute("DELETE FROM meta")
        self.conn.commit()

    def _touch(self) -> None:
        self._dirty += 1
        if self._dirty >= 200:
            self.commit()

    def commit(self) -> None:
        self.conn.commit()
        self._dirty = 0

    def add_email(self, email: str, source_url: str) -> bool:
        ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        cur = self.conn.execute(
            "INSERT OR IGNORE INTO emails (email, source_url, first_seen) VALUES (?, ?, ?)",
            (email, source_url, ts),
        )
        self.commit()  # los hallazgos nunca se pierden
        return cur.rowcount > 0

    def add_url(self, url: str, depth: int) -> bool:
        cur = self.conn.execute(
            "INSERT OR IGNORE INTO urls (url, depth, status) VALUES (?, ?, 0)", (url, depth)
        )
        self._touch()
        return cur.rowcount > 0

    def mark(self, url: str, status: int) -> None:
        self.conn.execute("UPDATE urls SET status = ? WHERE url = ?", (status, url))
        self._touch()

    def pending(self) -> list[tuple[str, int]]:
        return list(self.conn.execute("SELECT url, depth FROM urls WHERE status = 0 ORDER BY rowid"))

    def all_urls(self) -> set[str]:
        return {r[0] for r in self.conn.execute("SELECT url FROM urls")}

    def meta_get(self, key: str) -> Optional[str]:
        row = self.conn.execute("SELECT value FROM meta WHERE key = ?", (key,)).fetchone()
        return row[0] if row else None

    def meta_set(self, key: str, value: str) -> None:
        self.conn.execute("INSERT OR REPLACE INTO meta (key, value) VALUES (?, ?)", (key, value))
        self.commit()

    def count_emails(self) -> int:
        return self.conn.execute("SELECT COUNT(*) FROM emails").fetchone()[0]

    def count_pending(self) -> int:
        return self.conn.execute("SELECT COUNT(*) FROM urls WHERE status = 0").fetchone()[0]

    def export_csv(self, path: str) -> int:
        self.commit()
        rows = self.conn.execute(
            "SELECT email, source_url, first_seen FROM emails ORDER BY first_seen, email"
        ).fetchall()
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with p.open("w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(["email", "source_url", "first_seen"])
            w.writerows(rows)
        return len(rows)

    def close(self) -> None:
        self.commit()
        self.conn.close()


# --------------------------------------------------------------------------- #
# robots.txt
# --------------------------------------------------------------------------- #

@dataclass
class RobotsEntry:
    parser: Optional[robotparser.RobotFileParser] = None
    disallow_all: bool = False
    delay: float = 0.0
    sitemaps: list[str] = field(default_factory=list)


class Robots:
    """Cache de robots.txt por origen (esquema + host + puerto)."""

    def __init__(self, client: httpx.AsyncClient, sem: asyncio.Semaphore, user_agent: str):
        self.client, self.sem, self.ua = client, sem, user_agent
        self._tasks: dict[str, asyncio.Future] = {}

    async def entry(self, url: str) -> RobotsEntry:
        p = urlsplit(url)
        origin = f"{p.scheme}://{p.netloc}"
        task = self._tasks.get(origin)
        if task is None:
            task = asyncio.ensure_future(self._load(origin))
            self._tasks[origin] = task
        return await asyncio.shield(task)

    def allowed(self, entry: RobotsEntry, url: str) -> bool:
        if entry.disallow_all:
            return False
        return True if entry.parser is None else entry.parser.can_fetch(self.ua, url)

    async def _load(self, origin: str) -> RobotsEntry:
        try:
            async with self.sem:
                r = await self.client.get(origin + "/robots.txt", follow_redirects=True)
        except httpx.RequestError as exc:
            log.warning("robots.txt inaccesible en %s (%s): host omitido", origin, exc.__class__.__name__)
            return RobotsEntry(disallow_all=True)
        if r.status_code == 200:
            rp = robotparser.RobotFileParser()
            rp.parse(r.text[:512_000].splitlines())
            delay = rp.crawl_delay(self.ua) or 0
            return RobotsEntry(parser=rp, delay=float(delay), sitemaps=list(rp.site_maps() or []))
        if 400 <= r.status_code < 500:
            return RobotsEntry()  # sin robots.txt: todo permitido (RFC 9309)
        log.warning("robots.txt %s en %s: host omitido", r.status_code, origin)
        return RobotsEntry(disallow_all=True)


# --------------------------------------------------------------------------- #
# Crawler
# --------------------------------------------------------------------------- #

@dataclass
class Raw:
    status: int
    headers: httpx.Headers
    body: Optional[bytes]


@dataclass
class Fetched:
    url: str
    status: int
    content_type: str
    body: Optional[bytes]


class BudgetExhausted(Exception):
    """Se alcanzo --max-pages: la URL queda pendiente para --resume."""


class _Retry(Exception):
    pass


def _retry_after(headers: httpx.Headers) -> float:
    try:
        return min(float(headers.get("retry-after", "")), MAX_CRAWL_DELAY)
    except ValueError:
        return 0.0


class Crawler:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        self.ua = args.user_agent
        self.store = Store(args.db)
        self.seen: set[str] = set()
        self.pages = 0
        self.new_emails = 0
        self.scope_bases: set[str] = {TARGET_DOMAIN}
        self._host_locks: dict[str, asyncio.Lock] = {}
        self._host_next: dict[str, float] = {}

    # ---- alcance ---------------------------------------------------------- #
    def in_scope(self, url: str) -> bool:
        if self.args.follow_external:
            return True
        host = urlsplit(url).hostname or ""
        return any(host == b or host.endswith("." + b) for b in self.scope_bases)

    def add_url(self, raw: str, depth: int, base: Optional[str] = None, seed: bool = False) -> bool:
        url = normalize_url(raw, base)
        if not url or url in self.seen:
            return False
        if not seed and (not self.in_scope(url) or has_skipped_ext(url, self.args.pdf)):
            return False
        self.seen.add(url)
        self.store.add_url(url, depth)
        self.queue.put_nowait((url, depth))
        return True

    # ---- red -------------------------------------------------------------- #
    async def _throttle(self, host: str, delay: float) -> None:
        lock = self._host_locks.setdefault(host, asyncio.Lock())
        async with lock:
            now = time.monotonic()
            start = max(now, self._host_next.get(host, 0.0))
            if start > now:
                await asyncio.sleep(start - now)
            self._host_next[host] = start + delay

    async def _request(self, url: str, want: Callable[[str, str], Optional[int]], delay: float) -> Optional[Raw]:
        host = urlsplit(url).netloc.lower()
        for attempt in range(MAX_RETRIES + 1):
            await self._throttle(host, delay)
            wait_more = 0.0
            try:
                async with self.sem:
                    async with self.client.stream("GET", url) as resp:
                        status = resp.status_code
                        if status in REDIRECT_CODES:
                            return Raw(status, resp.headers, None)
                        if status == 429 or status >= 500:
                            if attempt < MAX_RETRIES:
                                wait_more = _retry_after(resp.headers)
                                raise _Retry
                            return Raw(status, resp.headers, None)
                        if status >= 400:
                            return Raw(status, resp.headers, None)
                        ctype = resp.headers.get("content-type", "").split(";")[0].strip().lower()
                        limit = want(ctype, url)
                        if limit is None:
                            return Raw(status, resp.headers, None)
                        clen = resp.headers.get("content-length", "")
                        if clen.isdigit() and int(clen) > limit:
                            log.debug("demasiado grande (%s bytes): %s", clen, url)
                            return Raw(status, resp.headers, None)
                        buf = bytearray()
                        async for chunk in resp.aiter_bytes():
                            buf.extend(chunk)
                            if len(buf) > limit:
                                log.debug("demasiado grande (>%s bytes): %s", limit, url)
                                return Raw(status, resp.headers, None)
                        return Raw(status, resp.headers, bytes(buf))
            except _Retry:
                pass
            except httpx.InvalidURL:
                return None
            except httpx.RequestError as exc:
                log.debug("error de red %s: %s", url, exc.__class__.__name__)
                if attempt == MAX_RETRIES:
                    return None
            await asyncio.sleep(min(wait_more or 2.0 * (attempt + 1), MAX_CRAWL_DELAY))
        return None

    async def fetch(
        self, url: str, want: Callable[[str, str], Optional[int]], count_page: bool
    ) -> Optional[Fetched]:
        """GET con alcance, robots.txt y redirecciones validados en cada salto."""
        current = url
        for hop in range(MAX_REDIRECTS + 1):
            if not self.in_scope(current):
                log.debug("fuera de alcance: %s", current)
                return None
            entry = await self.robots.entry(current)
            if not self.robots.allowed(entry, current):
                log.debug("bloqueado por robots.txt: %s", current)
                return None
            if count_page and hop == 0:
                if self.args.max_pages and self.pages >= self.args.max_pages:
                    raise BudgetExhausted
                self.pages += 1
            delay = max(self.args.delay, min(entry.delay, MAX_CRAWL_DELAY))
            raw = await self._request(current, want, delay)
            if raw is None:
                return None
            if raw.status in REDIRECT_CODES:
                loc = raw.headers.get("location")
                nxt = normalize_url(loc, base=current) if loc else None
                if not nxt:
                    return None
                current = nxt
                continue
            return Fetched(current, raw.status, raw.headers.get("content-type", ""), raw.body)
        return None

    def _page_limit(self, ctype: str, url: str) -> Optional[int]:
        kind = classify(ctype, url)
        if kind == "pdf":
            return PDF_MAX_BYTES if self.args.pdf else None
        return HTML_MAX_BYTES if kind else None

    # ---- procesamiento ---------------------------------------------------- #
    def _record(self, emails: set[str], source: str) -> int:
        n = 0
        for email in sorted(emails):
            if self.store.add_email(email, source):
                n += 1
                self.new_emails += 1
                log.info("EMAIL  %s  <-  %s", email, source)
        return n

    async def process(self, url: str, depth: int) -> None:
        res = await self.fetch(url, self._page_limit, count_page=True)
        if res is None or res.body is None or not (200 <= res.status < 300):
            if res is not None:
                log.info("%s  %s", res.status, url)
            return
        if res.url != url:
            self.seen.add(res.url)
        kind = classify(res.content_type.split(";")[0].strip().lower(), res.url)
        emails: set[str] = set()
        links: list[str] = []
        follow = True
        if kind == "pdf":
            emails = await asyncio.to_thread(extract_pdf_emails, res.body)
        elif kind in ("html", "text"):
            text = decode_body(res.body, res.content_type)
            if kind == "html":
                page = await asyncio.to_thread(parse_html, text, res.url)
                emails, links, follow = page.emails, page.links, page.follow
            else:
                emails = await asyncio.to_thread(find_emails, text)
        added = self._record(emails, res.url)
        log.info("%s  %s%s", res.status, res.url, f"  (+{added} nuevos)" if added else "")
        if kind == "html" and follow and depth < self.args.max_depth:
            for link in links:
                self.add_url(link, depth + 1)

    async def worker(self) -> None:
        while True:
            url, depth = await self.queue.get()
            try:
                await self.process(url, depth)
                self.store.mark(url, STATUS_DONE)
            except BudgetExhausted:
                pass  # sigue pendiente en la BD
            except asyncio.CancelledError:
                raise
            except Exception as exc:  # noqa: BLE001 - un fallo no debe matar el worker
                log.warning("error procesando %s: %s: %s", url, exc.__class__.__name__, exc)
                self.store.mark(url, STATUS_ERROR)
            finally:
                self.queue.task_done()

    # ---- descubrimiento: sitemap ----------------------------------------- #
    async def discover_sitemaps(self, origins: list[str]) -> None:
        for origin in origins:
            key = f"sitemap_done:{origin}"
            if self.store.meta_get(key):
                continue
            entry = await self.robots.entry(origin + "/")
            pending: deque[tuple[str, int]] = deque(
                (u, 0) for u in [*entry.sitemaps, origin + "/sitemap.xml", origin + "/sitemap_index.xml"]
            )
            visited: set[str] = set()
            found = 0
            while pending and len(visited) < MAX_SITEMAPS and found < SITEMAP_URL_CAP:
                sm_raw, level = pending.popleft()
                sm = normalize_url(sm_raw)
                if not sm or sm in visited:
                    continue
                visited.add(sm)
                res = await self.fetch(sm, lambda _c, _u: SITEMAP_MAX_BYTES, count_page=False)
                if res is None or res.status != 200 or not res.body:
                    continue
                data = res.body
                try:
                    if data[:2] == b"\x1f\x8b":
                        data = gunzip_capped(data, SITEMAP_MAX_BYTES)
                except zlib.error:
                    continue
                text = data.decode("utf-8", errors="replace")
                locs = [html.unescape(x) for x in LOC_RE.findall(text)]
                if re.search(r"<sitemapindex", text[:5000], re.I):
                    if level < MAX_SITEMAP_LEVEL:
                        pending.extend((u, level + 1) for u in locs)
                else:
                    for u in locs:
                        if self.add_url(u, 0):
                            found += 1
                            if found >= SITEMAP_URL_CAP:
                                break
            log.info("sitemap %s: %d sitemaps leidos, %d URLs nuevas", origin, len(visited), found)
            self.store.meta_set(key, "1")

    # ---- descubrimiento: Common Crawl ------------------------------------ #
    async def _cc_get(self, url: str, params: Optional[list[tuple[str, str]]] = None) -> Optional[httpx.Response]:
        for attempt in range(MAX_RETRIES + 2):
            await self._throttle("index.commoncrawl.org", max(self.args.delay, 1.0))
            try:
                async with self.sem:
                    r = await self.client.get(url, params=params, timeout=max(self.args.timeout, 60.0))
            except httpx.RequestError as exc:
                log.debug("Common Crawl: %s", exc.__class__.__name__)
                r = None
            if r is not None and r.status_code == 200:
                return r
            if r is not None and r.status_code == 404:
                return None
            await asyncio.sleep(5 * (attempt + 1))
        return None

    async def discover_common_crawl(self) -> None:
        if self.store.meta_get("cc_done"):
            return
        r = await self._cc_get(COLLINFO_URL)
        if r is None:
            log.warning("Common Crawl: no se pudo leer la lista de indices")
            return
        try:
            apis = [c["cdx-api"] for c in r.json()[: self.args.cc_indexes]]
        except (ValueError, KeyError, TypeError):
            log.warning("Common Crawl: respuesta inesperada de collinfo.json")
            return
        wanted_mimes = {"text/html", "application/xhtml+xml"} | ({"application/pdf"} if self.args.pdf else set())
        added = 0
        base_params = [
            ("url", TARGET_DOMAIN), ("matchType", "domain"), ("output", "json"),
            ("fl", "url,mime,status"), ("filter", "status:200"),
        ]
        for api in apis:
            rp = await self._cc_get(api, base_params + [("showNumPages", "true")])
            pages = 1
            if rp is not None:
                try:
                    pages = int(json.loads(rp.text.splitlines()[0]).get("pages", 1))
                except (ValueError, IndexError, AttributeError):
                    pages = 1
            for page in range(pages):
                if added >= self.args.cc_limit:
                    break
                rr = await self._cc_get(api, base_params + [("page", str(page))])
                if rr is None:
                    break
                for line in rr.text.splitlines():
                    try:
                        obj = json.loads(line)
                    except ValueError:
                        continue
                    mime = str(obj.get("mime", "")).lower()
                    if obj.get("url") and mime in wanted_mimes and self.add_url(obj["url"], 0):
                        added += 1
                        if added >= self.args.cc_limit:
                            break
            log.info("Common Crawl %s: %d URLs acumuladas", api.rsplit("/", 1)[-1], added)
        self.store.meta_set("cc_done", "1")

    # ---- ciclo principal -------------------------------------------------- #
    async def run(self) -> None:
        a = self.args
        self.queue: asyncio.Queue[tuple[str, int]] = asyncio.Queue()
        self.sem = asyncio.Semaphore(a.concurrency)
        headers = {
            "User-Agent": self.ua,
            "Accept": "text/html,application/xhtml+xml,application/pdf;q=0.9,*/*;q=0.5",
            "Accept-Language": "en,es;q=0.8",
        }
        limits = httpx.Limits(max_connections=a.concurrency * 2, max_keepalive_connections=a.concurrency)
        workers: list[asyncio.Task] = []
        async with httpx.AsyncClient(
            headers=headers, timeout=httpx.Timeout(a.timeout), limits=limits, follow_redirects=False
        ) as client:
            self.client = client
            self.robots = Robots(client, self.sem, self.ua)
            try:
                await self._run(workers)
            finally:
                for w in workers:
                    w.cancel()
                await asyncio.gather(*workers, return_exceptions=True)
                n = self.store.export_csv(a.csv)
                log.info(
                    "Fin: %d paginas, %d correos nuevos, %d en total, %d URLs pendientes -> %s",
                    self.pages, self.new_emails, n, self.store.count_pending(), a.csv,
                )
                self.store.close()

    async def _run(self, workers: list[asyncio.Task]) -> None:
        a = self.args
        seeds = [u for u in (normalize_url(s if "://" in s else f"https://{s}") for s in a.seed_list) if u]
        if not seeds:
            raise SystemExit("No hay seeds validas")
        for s in seeds:
            self.scope_bases.add(strip_www(urlsplit(s).hostname or ""))

        if a.resume:
            self.seen = self.store.all_urls()
            pending = self.store.pending()
            for url, depth in pending:
                self.queue.put_nowait((url, depth))
            log.info("Reanudando: %d URLs pendientes, %d ya conocidas", len(pending), len(self.seen))
        else:
            self.store.reset_crawl_state()

        for s in seeds:
            self.add_url(s, 0, seed=True)

        if a.sitemap:
            origins = list(dict.fromkeys(f"{urlsplit(s).scheme}://{urlsplit(s).netloc}" for s in seeds))
            await self.discover_sitemaps(origins)
        if a.cc:
            await self.discover_common_crawl()

        log.info("Iniciando crawl: %d URLs en cola, concurrencia=%d", self.queue.qsize(), a.concurrency)
        workers.extend(asyncio.create_task(self.worker()) for _ in range(a.concurrency))
        await self.queue.join()


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="ppg_harvest.py",
        description="Recolecta correos @ppg.com (y subdominios) publicados en la web.",
    )
    p.add_argument("--seeds", nargs="*", default=[], metavar="URL",
                   help="URLs/dominios semilla (separados por espacio o coma). Por defecto: %s" % DEFAULT_SEED)
    p.add_argument("--seed-file", metavar="ARCHIVO", help="archivo con una semilla por linea (# = comentario)")
    p.add_argument("--db", default="ppg_emails.db", help="base SQLite (default: %(default)s)")
    p.add_argument("--csv", default="ppg_emails.csv", help="CSV de salida (default: %(default)s)")
    p.add_argument("--max-pages", type=int, default=500,
                   help="maximo de paginas a descargar en esta ejecucion; 0 = sin limite (default: %(default)s)")
    p.add_argument("--max-depth", type=int, default=3, help="profundidad maxima de enlaces (default: %(default)s)")
    p.add_argument("--concurrency", type=int, default=10, help="peticiones simultaneas (default: %(default)s)")
    p.add_argument("--delay", type=float, default=1.0,
                   help="segundos minimos entre peticiones al mismo host (default: %(default)s)")
    p.add_argument("--pdf", action="store_true", help="descargar y analizar PDFs")
    p.add_argument("--cc", action="store_true", help="descubrir URLs con la Common Crawl index API (matchType=domain)")
    p.add_argument("--sitemap", action="store_true", help="descubrir URLs via sitemap.xml (recursivo)")
    p.add_argument("--resume", action="store_true", help="continuar con la cola pendiente guardada en --db")
    p.add_argument("--follow-external", action="store_true", help="seguir enlaces a dominios externos")
    p.add_argument("--user-agent", default=f"ppg-harvest/{VERSION} (+brand-protection research)",
                   help="User-Agent (el primer token, antes de '/', se usa para robots.txt)")
    p.add_argument("--timeout", type=float, default=20.0, help="timeout HTTP en segundos (default: %(default)s)")
    p.add_argument("--cc-indexes", type=int, default=1, help="cuantos indices recientes de Common Crawl consultar")
    p.add_argument("--cc-limit", type=int, default=5000, help="maximo de URLs a tomar de Common Crawl")
    p.add_argument("-v", "--verbose", action="store_true", help="log detallado (DEBUG)")
    return p


def collect_seeds(args: argparse.Namespace) -> list[str]:
    seeds: list[str] = []
    for item in args.seeds:
        seeds.extend(x.strip() for x in item.split(",") if x.strip())
    if args.seed_file:
        for line in Path(args.seed_file).read_text(encoding="utf-8").splitlines():
            line = line.split("#", 1)[0].strip()
            if line:
                seeds.append(line)
    return seeds or [DEFAULT_SEED]


def main(argv: Optional[list[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.concurrency < 1:
        parser.error("--concurrency debe ser >= 1")
    if args.delay < 0 or args.max_depth < 0 or args.max_pages < 0:
        parser.error("--delay, --max-depth y --max-pages no pueden ser negativos")
    try:
        args.seed_list = collect_seeds(args)
    except OSError as exc:
        parser.error(f"no se pudo leer --seed-file: {exc}")

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)-7s %(message)s",
        datefmt="%H:%M:%S",
        stream=sys.stderr,
    )
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)
    logging.getLogger("pypdf").setLevel(logging.ERROR)

    try:
        asyncio.run(Crawler(args).run())
    except KeyboardInterrupt:
        log.warning("Interrumpido. Estado guardado; continua con --resume.")
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())

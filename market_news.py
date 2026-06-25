#!/usr/bin/env python3
"""
Macro Market News Terminal  --  Koyfin-style aggregator for NASDAQ / S&P 500 macro news.

Zero dependencies (Python 3.9+ stdlib only). No API keys required.

Run:
    python market_news.py
Then open http://localhost:8765 in your browser.

Feeds are aggregated from free public RSS sources, deduped, categorized, and
ranked by recency. Items that mention key macro / index terms are flagged.

Edit the FEEDS list below to add/remove sources.
"""

import html
import ipaddress
import json
import re
import socket
import ssl
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import os

# Cloud hosts inject the port via $PORT and expect binding on 0.0.0.0.
# Locally these default to 8765 / localhost.
PORT = int(os.environ.get("PORT", "8765"))
HOST = os.environ.get("HOST", "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1")
REFRESH_FAST = 60              # refresh cadence while US market is active
REFRESH_SLOW = 300            # refresh cadence overnight / weekends
FETCH_TIMEOUT = 12             # per-feed network timeout
MAX_ITEMS_PER_FEED = 40
USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
              "AppleWebKit/537.36 (KHTML, like Gecko) "
              "Chrome/124.0 Safari/537.36")

# SSL context that trusts the Windows system cert store (so HTTPS-intercepting
# corporate/network proxies work) while relaxing OpenSSL's over-strict
# X509 basic-constraints check that such proxy CAs often trip.
SSL_CTX = ssl.create_default_context()
SSL_CTX.load_default_certs()
SSL_CTX.verify_flags &= ~ssl.VERIFY_X509_STRICT

# ----------------------------------------------------------------------------
# Feed sources.  Each: (display source name, url, category)
# Categories drive the tab filters in the UI.
# ----------------------------------------------------------------------------
FEEDS = [
    # --- Macro / Economy ---
    ("CNBC Economy",      "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=20910258", "Macro"),
    ("MarketWatch Pulse", "https://feeds.content.dowjones.io/public/rss/mw_marketpulse",                          "Macro"),
    ("Investing Economy", "https://www.investing.com/rss/news_25.rss",                                            "Macro"),
    ("Yahoo Finance",     "https://finance.yahoo.com/news/rssindex",                                              "Macro"),

    # --- Federal Reserve / Central Banks ---
    ("Fed Press",         "https://www.federalreserve.gov/feeds/press_all.xml",                                   "Fed"),
    ("Fed Monetary",      "https://www.federalreserve.gov/feeds/press_monetary.xml",                              "Fed"),

    # --- Markets / Indices ---
    ("CNBC Markets",      "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=20409666", "Markets"),
    ("CNBC Top News",     "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=100003114","Markets"),
    ("MarketWatch Top",   "https://feeds.content.dowjones.io/public/rss/mw_topstories",                           "Markets"),
    ("Nasdaq Markets",    "https://www.nasdaq.com/feed/rssoutbound?category=Markets",                             "Markets"),
    ("CNBC Investing",    "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=15839069", "Markets"),
    # Nasdaq "US Markets" republishes MT Newswires market wraps (pre-market /
    # midday / close "Stock Market News for ..." summaries) all session long.
    ("Nasdaq US Markets", "https://www.nasdaq.com/feed/rssoutbound?category=US%20Markets",                        "Markets"),

    # --- Tech / Nasdaq-heavy ---
    ("CNBC Technology",   "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=19854910", "Tech"),
    ("Nasdaq Tech",       "https://www.nasdaq.com/feed/rssoutbound?category=Technology",                          "Tech"),

    # --- Finance / Investing ---
    ("CNBC Finance",      "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=10000664", "Finance"),
    ("Investing Stocks",  "https://www.investing.com/rss/news_25.rss",                                            "Finance"),
]

# Virtual tab (not tied to a single feed): a live, cross-source view of every
# NASDAQ / S&P 500 related headline plus the MT Newswires market wraps.
MARKET_TAB = "Market Sentiments"
# Sources whose items always count as market-relevant, regardless of keywords
# (the MT Newswires daily wraps don't always say "S&P"/"Nasdaq" in the title).
MARKET_SOURCES = {"Nasdaq US Markets"}

# Tab order in the UI. Categories not listed fall to the end, alphabetically.
CATEGORY_ORDER = ["Macro", "Markets", "Fed", "Tech", "Finance"]


def ordered_categories():
    cats = {c for _, _, c in FEEDS}
    rank = {c: i for i, c in enumerate(CATEGORY_ORDER)}
    return sorted(cats, key=lambda c: (rank.get(c, len(CATEGORY_ORDER)), c))


# Terms that flag an item as especially relevant to NASDAQ / S&P 500 macro.
HOT_TERMS = [
    r"\bS&P\s*500\b", r"\bS&P500\b", r"\bSPX\b", r"\bnasdaq\b", r"\bndx\b",
    r"\bdow\b", r"\bfed(eral reserve)?\b", r"\bfomc\b", r"\bpowell\b",
    r"\binflation\b", r"\bcpi\b", r"\bpce\b", r"\bppi\b", r"\bjobs report\b",
    r"\bnonfarm\b", r"\bpayrolls?\b", r"\brate (cut|hike|decision)\b",
    r"\binterest rates?\b", r"\bgdp\b", r"\brecession\b", r"\byields?\b",
    r"\btreasur(y|ies)\b", r"\bunemployment\b", r"\bbond\b", r"\bearnings\b",
    r"\bmega.?cap\b", r"\bbig tech\b", r"\bsemiconductor\b", r"\bAI\b",
    r"\bSPY\b", r"\bQQQ\b", r"\bwall street\b", r"\bfutures\b",
    r"\bdow jones\b", r"\bstock market\b", r"\bpre.?market\b", r"\bmagnificent 7\b",
]
HOT_RE = re.compile("|".join(HOT_TERMS), re.IGNORECASE)

# Pre-market sentiment gauge.  Index FUTURES trade overnight, so they're the
# clearest read on "where the market is pointing before the open."
# (symbol, display label)
QUOTES = [
    ("ES=F",  "S&P 500 Fut"),
    ("NQ=F",  "Nasdaq-100 Fut"),
    ("^GSPC", "S&P 500"),
    ("^IXIC", "Nasdaq"),
    ("^DJI",  "Dow"),
    ("^VIX",  "VIX"),
]
QUOTE_REFRESH_SECONDS = 60

# --- AI article summaries (Google Gemini, free tier) ---------------------
# Set GEMINI_API_KEY (from https://aistudio.google.com/apikey) to enable.
# Free, no card required. Without a key the feature degrades gracefully.
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.0-flash")
GEMINI_URL = ("https://generativelanguage.googleapis.com/v1beta/models/"
              f"{GEMINI_MODEL}:generateContent")
# Cap daily summaries so a public visitor can't exhaust the free quota.
MAX_SUMMARIES_PER_DAY = int(os.environ.get("MAX_SUMMARIES_PER_DAY", "150"))

# Strip HTML tags / scripts from fetched article pages.
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")
SCRIPT_RE = re.compile(r"<(script|style)[^>]*>.*?</\1>", re.IGNORECASE | re.DOTALL)

_lock = threading.Lock()
_state = {"items": [], "updated": None, "errors": [], "quotes": [], "sentiment": {}}
_summaries = {}                       # url -> summary text (cache, avoids re-billing)
_summary_day = {"date": None, "count": 0}


def clean_text(s):
    if not s:
        return ""
    s = html.unescape(s)
    s = TAG_RE.sub(" ", s)
    s = WS_RE.sub(" ", s)
    return s.strip()


def parse_date(s):
    if not s:
        return None
    s = s.strip()
    # RFC 822 (RSS pubDate)
    try:
        dt = parsedate_to_datetime(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except Exception:
        pass
    # ISO 8601 (Atom updated/published)
    try:
        s2 = s.replace("Z", "+00:00")
        dt = datetime.fromisoformat(s2)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except Exception:
        return None


def strip_ns(tag):
    return tag.split("}")[-1] if "}" in tag else tag


def fetch_feed(name, url, category):
    items = []
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT,
                                               "Accept": "application/rss+xml, application/xml, text/xml, */*"})
    with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
        raw = resp.read()
    root = ET.fromstring(raw)

    # Handle both RSS (<channel><item>) and Atom (<feed><entry>)
    entries = []
    for el in root.iter():
        if strip_ns(el.tag) in ("item", "entry"):
            entries.append(el)

    for entry in entries[:MAX_ITEMS_PER_FEED]:
        title = link = summary = date_s = ""
        for child in entry:
            tag = strip_ns(child.tag)
            if tag == "title" and not title:
                title = clean_text(child.text or "")
            elif tag == "link":
                # Atom uses href attr; RSS uses text
                href = child.get("href")
                if href and not link:
                    link = href.strip()
                elif child.text and not link:
                    link = child.text.strip()
            elif tag in ("description", "summary", "content") and not summary:
                summary = clean_text(child.text or "")
            elif tag in ("pubDate", "published", "updated", "date") and not date_s:
                date_s = child.text or ""

        if not title or not link:
            continue
        dt = parse_date(date_s)
        hot = bool(HOT_RE.search(title + " " + summary))
        items.append({
            "title": title,
            "link": link,
            "summary": summary[:280],
            "source": name,
            "category": category,
            "ts": dt.timestamp() if dt else 0,
            "iso": dt.isoformat() if dt else "",
            "hot": hot,
            # "market" powers the live "Market Sentiments" tab: NASDAQ/S&P 500
            # related items from any source, plus the MT Newswires market wraps.
            "market": hot or name in MARKET_SOURCES,
        })
    return items


def refresh():
    all_items = []
    errors = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        futures = {ex.submit(fetch_feed, n, u, c): n for n, u, c in FEEDS}
        for fut in as_completed(futures):
            name = futures[fut]
            try:
                all_items.extend(fut.result())
            except Exception as e:
                errors.append(f"{name}: {type(e).__name__}: {e}")

    # Dedupe by normalized title (keep newest)
    seen = {}
    for it in all_items:
        key = re.sub(r"[^a-z0-9]", "", it["title"].lower())[:80]
        if key not in seen or it["ts"] > seen[key]["ts"]:
            seen[key] = it
    deduped = sorted(seen.values(), key=lambda x: x["ts"], reverse=True)

    with _lock:
        _state["items"] = deduped
        _state["updated"] = datetime.now(timezone.utc).isoformat()
        _state["errors"] = errors
    print(f"[{datetime.now().strftime('%H:%M:%S')}] refreshed: "
          f"{len(deduped)} items, {len(errors)} feed error(s)")


def market_is_active():
    """True during the US trading day incl. pre/after-hours (approx, ET).
    Keeps the news flowing fast while the market is open."""
    # US Eastern ~ UTC-4 (EDT). Good enough for choosing a refresh cadence.
    et = datetime.now(timezone.utc) - timedelta(hours=4)
    if et.weekday() >= 5:                       # Sat/Sun
        return False
    minutes = et.hour * 60 + et.minute
    return 7 * 60 <= minutes <= 20 * 60          # 7:00am–8:00pm ET


def background_refresher():
    while True:
        try:
            refresh()
        except Exception as e:
            print("refresh error:", e)
        time.sleep(REFRESH_FAST if market_is_active() else REFRESH_SLOW)


def fetch_quote(symbol, label):
    url = "https://query1.finance.yahoo.com/v8/finance/chart/" + urllib.parse.quote(symbol)
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
        data = json.load(resp)
    m = data["chart"]["result"][0]["meta"]
    price = m.get("regularMarketPrice")
    prev = m.get("chartPreviousClose") or m.get("previousClose")
    chg = (price - prev) / prev * 100 if price and prev else 0.0
    return {"symbol": symbol, "label": label,
            "price": round(price, 2) if price else None,
            "change": round(chg, 2),
            "state": m.get("marketState")}


def compute_sentiment(quotes):
    by = {q["label"]: q for q in quotes}
    futs = [by[l]["change"] for l in ("S&P 500 Fut", "Nasdaq-100 Fut") if l in by]
    cash = [by[l]["change"] for l in ("S&P 500", "Nasdaq", "Dow") if l in by]
    drivers = futs or cash          # prefer futures (overnight = pre-market read)
    bias = sum(drivers) / len(drivers) if drivers else 0.0
    vix = by.get("VIX", {}).get("change", 0.0)
    score = max(-100, min(100, round(bias * 25 - vix * 1.5)))
    if bias >= 0.35:
        label, tone = "Risk-On", "bull"
    elif bias <= -0.35:
        label, tone = "Risk-Off", "bear"
    else:
        label, tone = "Mixed / Flat", "flat"
    using = "futures" if futs else "cash indices"
    return {"label": label, "tone": tone, "bias": round(bias, 2),
            "vix": vix, "score": score, "basis": using}


def refresh_quotes():
    out = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = {ex.submit(fetch_quote, s, l): l for s, l in QUOTES}
        for fut in as_completed(futs):
            try:
                out.append(fut.result())
            except Exception:
                pass
    order = {l: i for i, (_, l) in enumerate(QUOTES)}
    out.sort(key=lambda q: order.get(q["label"], 99))
    with _lock:
        _state["quotes"] = out
        _state["sentiment"] = compute_sentiment(out)


def quotes_refresher():
    while True:
        try:
            refresh_quotes()
        except Exception as e:
            print("quote refresh error:", e)
        time.sleep(QUOTE_REFRESH_SECONDS)


# --------------------------------------------------------------------------
# AI summaries
# --------------------------------------------------------------------------
def is_safe_url(url):
    """Reject non-http(s) schemes and URLs that resolve to private/loopback
    addresses, so the summarize endpoint can't be abused for SSRF."""
    try:
        p = urllib.parse.urlparse(url)
    except Exception:
        return False
    if p.scheme not in ("http", "https") or not p.hostname:
        return False
    host = p.hostname.lower()
    if host == "localhost" or host.endswith(".local"):
        return False
    try:
        for info in socket.getaddrinfo(host, None):
            ip = ipaddress.ip_address(info[4][0])
            if (ip.is_private or ip.is_loopback or ip.is_link_local
                    or ip.is_reserved or ip.is_multicast):
                return False
    except Exception:
        return False
    return True


def extract_article_text(url):
    """Fetch an article page and return cleaned plain text (best-effort)."""
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
            charset = resp.headers.get_content_charset() or "utf-8"
            raw = resp.read(500_000)
        page = raw.decode(charset, "ignore")
    except Exception:
        return ""
    page = SCRIPT_RE.sub(" ", page)
    text = WS_RE.sub(" ", html.unescape(TAG_RE.sub(" ", page))).strip()
    return text[:6000]


def gemini_summarize(title, context_text):
    prompt = (
        "You are a markets analyst. Summarize the following financial news for a "
        "NASDAQ / S&P 500 trader as 3 short bullet points (one line each), then a "
        "final line starting 'Why it matters:' with one sentence on likely market "
        "impact. Be factual and concise; no preamble.\n\n"
        f"Headline: {title}\n\nArticle:\n{context_text}"
    )
    body = json.dumps({
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {"temperature": 0.3, "maxOutputTokens": 400},
    }).encode("utf-8")
    req = urllib.request.Request(
        GEMINI_URL, data=body, method="POST",
        headers={"Content-Type": "application/json", "x-goog-api-key": GEMINI_API_KEY},
    )
    with urllib.request.urlopen(req, timeout=25, context=SSL_CTX) as resp:
        data = json.load(resp)
    cands = data.get("candidates") or []
    if not cands:
        raise RuntimeError("Gemini returned no candidates")
    parts = cands[0].get("content", {}).get("parts", []) or []
    return "".join(p.get("text", "") for p in parts).strip()


def summarize_article(url, title, rss_summary):
    if not GEMINI_API_KEY:
        return {"error": "AI summaries aren't configured yet. Add a free "
                "GEMINI_API_KEY (from aistudio.google.com/apikey) to enable them."}
    if not is_safe_url(url):
        return {"error": "That article link can't be summarized."}

    with _lock:
        if url in _summaries:
            return {"summary": _summaries[url], "cached": True}
        today = datetime.now(timezone.utc).date().isoformat()
        if _summary_day["date"] != today:
            _summary_day.update(date=today, count=0)
        if _summary_day["count"] >= MAX_SUMMARIES_PER_DAY:
            return {"error": "Daily summary limit reached — try again tomorrow."}

    context_text = (extract_article_text(url) or rss_summary or title)[:6000]
    try:
        summary = gemini_summarize(title, context_text)
    except urllib.error.HTTPError as e:
        if e.code == 429:
            return {"error": "Gemini free-tier rate limit hit. Wait a minute and retry."}
        return {"error": f"Summary failed (HTTP {e.code})."}
    except Exception as e:
        return {"error": f"Summary failed: {type(e).__name__}."}
    if not summary:
        return {"error": "No summary was returned."}

    with _lock:
        _summaries[url] = summary
        _summary_day["count"] += 1
    return {"summary": summary}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass  # silence default logging

    def _send(self, code, body, ctype="application/json"):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype + "; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path.startswith("/api/news"):
            with _lock:
                payload = {
                    "items": _state["items"],
                    "updated": _state["updated"],
                    "errors": _state["errors"],
                    "categories": [MARKET_TAB] + ordered_categories(),
                    "quotes": _state["quotes"],
                    "sentiment": _state["sentiment"],
                }
            self._send(200, json.dumps(payload))
        elif self.path.startswith("/api/refresh"):
            threading.Thread(target=refresh, daemon=True).start()
            self._send(200, json.dumps({"ok": True}))
        elif self.path == "/" or self.path.startswith("/index"):
            self._send(200, PAGE, "text/html")
        else:
            self._send(404, json.dumps({"error": "not found"}))

    def do_POST(self):
        if self.path.startswith("/api/summarize"):
            try:
                length = int(self.headers.get("Content-Length", "0"))
                payload = json.loads(self.rfile.read(length) or b"{}")
            except Exception:
                self._send(400, json.dumps({"error": "bad request"}))
                return
            url = (payload.get("url") or "").strip()
            if not url.startswith("http"):
                self._send(400, json.dumps({"error": "invalid url"}))
                return
            result = summarize_article(url, payload.get("title", ""),
                                       payload.get("summary", ""))
            self._send(200, json.dumps(result))
        else:
            self._send(404, json.dumps({"error": "not found"}))


PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Macro News Terminal</title>
<style>
  :root{
    --bg:#0b0e14; --panel:#11151f; --panel2:#0e1218; --border:#1e2533;
    --text:#e6e9ef; --muted:#7d879c; --accent:#3b82f6; --hot:#f5a623;
    --hotbg:#221a0c; --green:#26a269; --hover:#161b27;
  }
  *{box-sizing:border-box}
  body{margin:0;background:var(--bg);color:var(--text);
    font:14px/1.45 "Segoe UI",system-ui,-apple-system,sans-serif}
  header{display:flex;align-items:center;gap:16px;padding:12px 18px;
    background:var(--panel);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:10}
  header h1{font-size:16px;margin:0;font-weight:700;letter-spacing:.3px}
  header h1 .dot{color:var(--green)}
  .status{color:var(--muted);font-size:12px;margin-left:auto;white-space:nowrap}
  .search{flex:1;max-width:340px}
  .search input{width:100%;background:var(--panel2);border:1px solid var(--border);
    color:var(--text);padding:7px 11px;border-radius:7px;outline:none;font-size:13px}
  .search input:focus{border-color:var(--accent)}
  .tabs{display:flex;gap:4px;padding:10px 18px;background:var(--panel);
    border-bottom:1px solid var(--border);flex-wrap:wrap;position:sticky;top:53px;z-index:9}
  .tab{padding:6px 14px;border-radius:7px;cursor:pointer;color:var(--muted);
    font-size:13px;font-weight:600;border:1px solid transparent;user-select:none}
  .tab:hover{background:var(--hover);color:var(--text)}
  .tab.active{background:var(--accent);color:#fff}
  .tab.hotfilter.active{background:var(--hot);color:#1a1206}
  .wrap{max-width:980px;margin:0 auto;padding:8px 14px 60px}
  .item{display:flex;gap:14px;padding:13px 12px;border-bottom:1px solid var(--border);
    text-decoration:none;color:inherit;border-radius:8px;cursor:pointer}
  .item:hover{background:var(--hover)}
  .src{font-size:11px;color:#9db4e8;text-decoration:none;border:1px solid #243049;
    padding:1px 8px;border-radius:20px}
  .src:hover{background:#1a2333}
  /* --- AI summary modal --- */
  .modal{position:fixed;inset:0;background:rgba(0,0,0,.6);display:flex;
    align-items:center;justify-content:center;z-index:50;padding:18px}
  .modal.hidden{display:none}
  .modal-card{background:var(--panel);border:1px solid var(--border);border-radius:14px;
    max-width:580px;width:100%;max-height:84vh;overflow:auto;padding:22px 24px;position:relative;
    box-shadow:0 20px 60px rgba(0,0,0,.5)}
  .modal-close{position:absolute;top:14px;right:14px;background:none;border:none;
    color:var(--muted);font-size:18px;cursor:pointer}
  .modal-close:hover{color:var(--text)}
  .modal-tag{font-size:11px;font-weight:700;color:#a78bfa;letter-spacing:.4px;
    text-transform:uppercase;margin-bottom:8px}
  .modal-card h3{margin:0 0 14px;font-size:16px;line-height:1.35;padding-right:24px}
  #modal-body .sum p{margin:0 0 9px;font-size:13.5px;line-height:1.5}
  #modal-body .spin{color:var(--muted);font-size:13px;padding:14px 0}
  #modal-body .errmsg{color:#f0a0a0;font-size:13px;background:#241316;
    border:1px solid #50262c;padding:10px 12px;border-radius:8px}
  .modal-link{display:inline-block;margin-top:14px;font-size:13px;color:#fff;
    background:var(--accent);padding:7px 14px;border-radius:8px;text-decoration:none;font-weight:600}
  .cachenote{font-size:10.5px;color:var(--muted);margin-top:8px}
  .item.hot{background:var(--hotbg)}
  .item.hot:hover{background:#2c2310}
  .meta{flex:0 0 78px;text-align:right;color:var(--muted);font-size:12px;padding-top:2px}
  .meta .time{font-weight:600;color:#aeb6c6}
  .body{flex:1;min-width:0}
  .title{font-size:14.5px;font-weight:600;margin:0 0 4px}
  .hot .title::before{content:"🔥 ";font-size:12px}
  .summary{color:var(--muted);font-size:12.5px;margin:0 0 6px;
    display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
  .badges{display:flex;gap:7px;align-items:center;flex-wrap:wrap}
  .badge{font-size:11px;color:var(--muted);background:var(--panel2);
    border:1px solid var(--border);padding:1px 8px;border-radius:20px}
  .badge.cat{color:#9db4e8;border-color:#243049}
  .empty{text-align:center;color:var(--muted);padding:60px 20px}
  .err{color:#e5534b;font-size:12px;padding:6px 18px;background:#1a1012;border-bottom:1px solid var(--border)}
  /* --- pre-market sentiment bar --- */
  .ticker{display:flex;align-items:center;gap:18px;padding:9px 18px;background:var(--panel2);
    border-bottom:1px solid var(--border);overflow-x:auto;white-space:nowrap;position:sticky;top:53px;z-index:9}
  .sent{display:flex;align-items:center;gap:8px;font-weight:700;font-size:13px;padding:3px 12px;
    border-radius:7px;flex:0 0 auto}
  .sent.bull{background:#0f2a1c;color:#3fd089;border:1px solid #1c5238}
  .sent.bear{background:#2a1115;color:#f0656a;border:1px solid #5a2228}
  .sent.flat{background:#1c2330;color:#9db0cf;border:1px solid #2c3850}
  .sent .score{font-size:11px;opacity:.85;font-weight:600}
  .quote{display:flex;flex-direction:column;line-height:1.25;flex:0 0 auto}
  .quote .lbl{font-size:10.5px;color:var(--muted);text-transform:uppercase;letter-spacing:.4px}
  .quote .val{font-size:13px;font-weight:600}
  .quote .chg{font-size:11.5px;font-weight:700}
  .up{color:#3fd089} .down{color:#f0656a} .flatc{color:#9db0cf}
  .tabs{top:99px}
  ::-webkit-scrollbar{width:10px}
  ::-webkit-scrollbar-thumb{background:#222a39;border-radius:6px}
  ::-webkit-scrollbar-track{background:transparent}
</style>
</head>
<body>
<header>
  <h1><span class="dot">●</span> Macro News Terminal</h1>
  <div class="search"><input id="q" placeholder="Search headlines… (e.g. CPI, Fed, Nvidia)"></div>
  <div class="status" id="status">loading…</div>
</header>
<div class="ticker" id="ticker"></div>
<div class="tabs" id="tabs"></div>
<div id="errbar"></div>
<div class="wrap"><div id="list"></div></div>

<div id="modal" class="modal hidden" onclick="if(event.target===this)closeSummary()">
  <div class="modal-card">
    <button class="modal-close" onclick="closeSummary()">✕</button>
    <div class="modal-tag">✨ AI Summary · Gemini</div>
    <h3 id="modal-title"></h3>
    <div id="modal-body"></div>
    <a id="modal-link" class="modal-link" target="_blank" rel="noopener">Read full article ↗</a>
  </div>
</div>

<script>
let DATA = {items:[], updated:null, errors:[], categories:[]};
const MARKET_TAB = "Market Sentiments";
let activeCat = MARKET_TAB;   // open on the live NASDAQ/S&P 500 view
let hotOnly = false;
let query = "";
let RENDERED = [];   // the currently-rendered item list (for click-to-summarize)

function fmtLine(l){ return esc(l.replace(/\*\*/g,'').replace(/^[\*\-•]\s*/,'')); }

async function openSummary(idx){
  const it = RENDERED[idx];
  if(!it) return;
  document.getElementById('modal-title').textContent = it.title;
  document.getElementById('modal-link').href = it.link;
  const body = document.getElementById('modal-body');
  body.innerHTML = '<div class="spin">✨ Summarizing…</div>';
  document.getElementById('modal').classList.remove('hidden');
  try{
    const r = await fetch('/api/summarize', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({url: it.link, title: it.title, summary: it.summary})
    });
    const d = await r.json();
    if(d.summary){
      const lines = d.summary.split('\n').map(s=>s.trim()).filter(Boolean);
      body.innerHTML = '<div class="sum">' + lines.map(l=>'<p>'+fmtLine(l)+'</p>').join('') + '</div>'
        + (d.cached?'<div class="cachenote">↺ cached — no new request used</div>':'');
    } else {
      body.innerHTML = '<div class="errmsg">'+ esc(d.error || 'No summary available.') +'</div>';
    }
  }catch(e){
    body.innerHTML = '<div class="errmsg">Could not reach the summary service.</div>';
  }
}
function closeSummary(){ document.getElementById('modal').classList.add('hidden'); }
document.addEventListener('keydown', e=>{ if(e.key==='Escape') closeSummary(); });

function timeAgo(ts){
  if(!ts) return "";
  const s = Math.floor(Date.now()/1000 - ts);
  if(s < 60) return s+"s";
  if(s < 3600) return Math.floor(s/60)+"m";
  if(s < 86400) return Math.floor(s/3600)+"h";
  return Math.floor(s/86400)+"d";
}
function fmtClock(ts){
  if(!ts) return "";
  const d = new Date(ts*1000);
  return d.toLocaleTimeString([], {hour:'2-digit', minute:'2-digit'});
}
function esc(s){const e=document.createElement('div');e.textContent=s;return e.innerHTML;}

function renderTabs(){
  const cats = ["All", ...DATA.categories];
  const t = document.getElementById('tabs');
  t.innerHTML = "";
  cats.forEach(c=>{
    const d = document.createElement('div');
    d.className = "tab"+(c===activeCat && !hotOnly ? " active":"");
    d.textContent = c;
    d.onclick = ()=>{activeCat=c; hotOnly=false; render();};
    t.appendChild(d);
  });
  const hot = document.createElement('div');
  hot.className = "tab hotfilter"+(hotOnly?" active":"");
  hot.textContent = "🔥 Hot";
  hot.onclick = ()=>{hotOnly=!hotOnly; render();};
  t.appendChild(hot);
}

function render(){
  renderTabs();
  let items = DATA.items;
  if(hotOnly) items = items.filter(i=>i.hot);
  else if(activeCat===MARKET_TAB) items = items.filter(i=>i.market);   // NASDAQ/S&P 500 only
  else if(activeCat!=="All") items = items.filter(i=>i.category===activeCat);
  if(query){
    const q = query.toLowerCase();
    items = items.filter(i=>(i.title+" "+i.summary+" "+i.source).toLowerCase().includes(q));
  }
  const list = document.getElementById('list');
  if(!items.length){ list.innerHTML='<div class="empty">No matching headlines.</div>'; return; }
  RENDERED = items;
  list.innerHTML = items.map((i,idx)=>`
    <div class="item ${i.hot?'hot':''}" onclick="openSummary(${idx})" title="Click for an AI summary">
      <div class="meta"><div class="time">${fmtClock(i.ts)}</div><div>${timeAgo(i.ts)} ago</div></div>
      <div class="body">
        <p class="title">${esc(i.title)}</p>
        ${i.summary?`<p class="summary">${esc(i.summary)}</p>`:''}
        <div class="badges">
          <span class="badge">${esc(i.source)}</span>
          <span class="badge cat">${esc(i.category)}</span>
          <a class="src" href="${esc(i.link)}" target="_blank" rel="noopener" onclick="event.stopPropagation()">↗ source</a>
        </div>
      </div>
    </div>`).join("");

  const errbar = document.getElementById('errbar');
  errbar.innerHTML = DATA.errors.length
    ? `<div class="err">⚠ ${DATA.errors.length} feed(s) unavailable: ${esc(DATA.errors.map(e=>e.split(':')[0]).join(', '))}</div>`
    : "";
}

function cls(v){ return v > 0.02 ? 'up' : (v < -0.02 ? 'down' : 'flatc'); }
function arrow(v){ return v > 0.02 ? '▲' : (v < -0.02 ? '▼' : '▬'); }

function renderTicker(){
  const t = document.getElementById('ticker');
  const s = DATA.sentiment || {};
  const quotes = DATA.quotes || [];
  if(!quotes.length){ t.innerHTML = ''; return; }
  const tone = s.tone || 'flat';
  const sentHtml = `<div class="sent ${tone}">
      <span>${s.tone==='bull'?'🟢':s.tone==='bear'?'🔴':'⚪'} ${esc(s.label||'—')}</span>
      <span class="score">${(s.bias>=0?'+':'')}${s.bias??'—'}% ${esc(s.basis||'')} · VIX ${(s.vix>=0?'+':'')}${s.vix??'—'}%</span>
    </div>`;
  const q = quotes.map(q=>`
    <div class="quote">
      <span class="lbl">${esc(q.label)}</span>
      <span class="val">${q.price!=null?q.price.toLocaleString():'—'}
        <span class="chg ${cls(q.change)}">${arrow(q.change)} ${(q.change>=0?'+':'')}${q.change}%</span>
      </span>
    </div>`).join('');
  t.innerHTML = sentHtml + q;
}

async function load(){
  try{
    const r = await fetch('/api/news');
    DATA = await r.json();
    const upd = DATA.updated ? new Date(DATA.updated).toLocaleTimeString() : "—";
    document.getElementById('status').textContent =
      `${DATA.items.length} headlines · updated ${upd}`;
    renderTicker();
    render();
  }catch(e){
    document.getElementById('status').textContent = "connection error";
  }
}

document.getElementById('q').addEventListener('input', e=>{query=e.target.value; render();});
load();
setInterval(load, 60000);           // poll backend every 60s
setInterval(()=>render(), 30000);   // refresh relative timestamps
</script>
</body>
</html>"""


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # avoid cp1252 console crashes
    except Exception:
        pass
    print("Fetching initial feeds...")
    refresh()
    refresh_quotes()
    threading.Thread(target=background_refresher, daemon=True).start()
    threading.Thread(target=quotes_refresher, daemon=True).start()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"\n  Macro News Terminal running ->  http://localhost:{PORT}  (bound {HOST}:{PORT})\n")
    print("  Press Ctrl+C to stop.\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down.")
        server.shutdown()


if __name__ == "__main__":
    main()

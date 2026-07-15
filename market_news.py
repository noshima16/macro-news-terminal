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
# Macro board: rates, dollar, commodities, crypto.
MACRO = [
    ("^TNX", "US 10Y"), ("^FVX", "US 5Y"), ("^TYX", "US 30Y"),
    ("DX-Y.NYB", "Dollar DXY"), ("CL=F", "Crude Oil"),
    ("GC=F", "Gold"), ("BTC-USD", "Bitcoin"),
]
# S&P sector ETFs for the heatmap (leaders/laggards on the day).
SECTORS = [
    ("XLK", "Technology"), ("XLC", "Comm Svcs"), ("XLY", "Cons Disc"),
    ("XLF", "Financials"), ("XLI", "Industrials"), ("XLV", "Health Care"),
    ("XLP", "Cons Staples"), ("XLE", "Energy"), ("XLU", "Utilities"),
    ("XLRE", "Real Estate"), ("XLB", "Materials"),
]
QUOTE_REFRESH_SECONDS = 90   # ~24 symbols per cycle; keep Yahoo happy

# Chart panel: symbols offered as quick tabs, and a short server-side cache.
CHART_TABS = [("NQ=F", "Nasdaq Fut"), ("ES=F", "S&P Fut"),
              ("^IXIC", "Nasdaq"), ("^GSPC", "S&P 500")]
CHART_CACHE_SECONDS = 60
SYMBOL_RE = re.compile(r"^[A-Za-z0-9\^\.\=\-]{1,12}$")

# --- AI article summaries (Google Gemini, free tier) ---------------------
# Set GEMINI_API_KEY (from https://aistudio.google.com/apikey) to enable.
# Free, no card required. Without a key the feature degrades gracefully.
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
GEMINI_URL = ("https://generativelanguage.googleapis.com/v1beta/models/"
              f"{GEMINI_MODEL}:generateContent")
# Cap daily summaries so a public visitor can't exhaust the free quota.
MAX_SUMMARIES_PER_DAY = int(os.environ.get("MAX_SUMMARIES_PER_DAY", "150"))
# How often to recompute the AI "daily bias" from the day's headlines.
DAILY_BIAS_REFRESH_SECONDS = int(os.environ.get("DAILY_BIAS_REFRESH_SECONDS", "1800"))

# --- Finnhub (optional, free tier) ---------------------------------------
# Free key from https://finnhub.io/register — 60 calls/min. Without it the app
# just runs on the RSS feeds.
FINNHUB_API_KEY = os.environ.get("FINNHUB_API_KEY", "").strip()

# --- Ticker tagging -------------------------------------------------------
# Company aliases per ticker. Bare tickers are matched case-SENSITIVELY (and
# only when >=3 chars) so "arm"/"on"/"all" don't false-positive; $TICKER always
# matches. Names are matched case-insensitively.
TICKER_MAP = {
    "AAPL": ["apple"], "MSFT": ["microsoft"], "NVDA": ["nvidia"],
    "AMZN": ["amazon"], "GOOGL": ["alphabet", "google"],
    "META": ["meta platforms", "facebook", "instagram"], "TSLA": ["tesla"],
    "AVGO": ["broadcom"], "AMD": ["advanced micro devices"], "INTC": ["intel"],
    "MU": ["micron"], "NFLX": ["netflix"], "ORCL": ["oracle"],
    "CRM": ["salesforce"], "ADBE": ["adobe"], "CSCO": ["cisco"],
    "QCOM": ["qualcomm"], "TXN": ["texas instruments"],
    "AMAT": ["applied materials"], "LRCX": ["lam research"],
    "ASML": ["asml"], "TSM": ["taiwan semiconductor", "tsmc"],
    "ARM": ["arm holdings"], "SMCI": ["super micro"], "PLTR": ["palantir"],
    "COIN": ["coinbase"], "JPM": ["jpmorgan", "jp morgan"],
    "GS": ["goldman sachs"], "BAC": ["bank of america"], "WFC": ["wells fargo"],
    "MS": ["morgan stanley"], "XOM": ["exxon"], "CVX": ["chevron"],
    "UNH": ["unitedhealth"], "LLY": ["eli lilly"], "PFE": ["pfizer"],
    "MRK": ["merck"], "WMT": ["walmart"], "COST": ["costco"],
    "HD": ["home depot"], "NKE": ["nike"], "DIS": ["disney"],
    "BA": ["boeing"], "CAT": ["caterpillar"], "GE": ["general electric"],
    "F": ["ford motor"], "GM": ["general motors"], "UBER": ["uber"],
    "ABNB": ["airbnb"], "SBUX": ["starbucks"], "PEP": ["pepsico"],
    "KO": ["coca-cola"], "IBM": ["international business machines"],
    "DELL": ["dell technologies"], "WDC": ["western digital"],
    "STX": ["seagate"], "MRVL": ["marvell"], "NXPI": ["nxp"],
}


def _build_ticker_pats():
    out = {}
    for tk, names in TICKER_MAP.items():
        name_rx = None
        if names:
            name_rx = re.compile(
                r"(?<![A-Za-z0-9])(?:" + "|".join(re.escape(n) for n in names)
                + r")(?![A-Za-z0-9])", re.IGNORECASE)
        alts = [r"\$" + re.escape(tk)]
        if len(tk) >= 3:
            alts.append(re.escape(tk))
        sym_rx = re.compile(r"(?<![A-Za-z0-9$])(?:" + "|".join(alts) + r")(?![A-Za-z0-9])")
        out[tk] = (name_rx, sym_rx)
    return out


TICKER_PATS = _build_ticker_pats()


def _mentions(symbol, text):
    """True if the text actually names this company/ticker (not a passing tag)."""
    pats = TICKER_PATS.get(symbol.upper())
    if pats:
        name_rx, sym_rx = pats
        return bool(sym_rx.search(text) or (name_rx and name_rx.search(text)))
    return bool(re.search(r"(?<![A-Za-z0-9])" + re.escape(symbol) + r"(?![A-Za-z0-9])",
                          text, re.IGNORECASE))


def tag_tickers(text):
    found = []
    for tk, (name_rx, sym_rx) in TICKER_PATS.items():
        if sym_rx.search(text) or (name_rx and name_rx.search(text)):
            found.append(tk)
        if len(found) >= 4:
            break
    return found


# --- Headline tone (rule-based, instant, no API cost) ---------------------
BULL_RE = re.compile(r"\b(?:beat|beats|tops|surge[sd]?|soar[sd]?|jump[sd]?|rall(?:y|ies|ied)"
                     r"|gain[sd]?|rise[sd]?|climb[sd]?|upgrade[sd]?|record high|all-time high"
                     r"|outperform|boost[sd]?|rebound[sd]?|bullish|optimis(?:m|tic)|higher"
                     r"|strong|stronger|profit[s]?|approval)\b", re.IGNORECASE)
BEAR_RE = re.compile(r"\b(?:miss|misses|missed|fall[sd]?|slump[sd]?|plunge[sd]?|tumble[sd]?"
                     r"|slide[sd]?|drop[sd]?|sink[sd]?|downgrade[sd]?|warn[sd]?|warning"
                     r"|layoff[s]?|weak|weaker|weakness|selloff|sell-off|bearish|recession"
                     r"|lower|decline[sd]?|loss(?:es)?|lawsuit|probe|investigation|fear[sd]?"
                     r"|slowdown|cuts?)\b", re.IGNORECASE)


def score_tone(text):
    b, s = len(BULL_RE.findall(text)), len(BEAR_RE.findall(text))
    return "bull" if b > s else "bear" if s > b else "neutral"


# Strip HTML tags / scripts from fetched article pages.
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")
SCRIPT_RE = re.compile(r"<(script|style)[^>]*>.*?</\1>", re.IGNORECASE | re.DOTALL)

_lock = threading.Lock()
_state = {"items": [], "updated": None, "errors": [], "quotes": [], "sentiment": {},
          "daily_bias": {}, "macro": [], "sectors": []}
_charts = {}                          # "symbol|range" -> (fetched_at, payload)
_seen_links = {}                      # link -> first-seen epoch (breaking flash)
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
        blob = title + " " + summary
        hot = bool(HOT_RE.search(blob))
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
            "tickers": tag_tickers(blob),
            "tone": score_tone(blob),
        })
    return items


def _finnhub_items(rows, category="Markets", source="Finnhub"):
    out = []
    for a in rows:
        title = clean_text(a.get("headline") or "")
        link = (a.get("url") or "").strip()
        if not title or not link:
            continue
        summary = clean_text(a.get("summary") or "")[:280]
        blob = title + " " + summary
        hot = bool(HOT_RE.search(blob))
        rel = [t.strip().upper() for t in (a.get("related") or "").split(",") if t.strip()]
        tickers = rel[:4] or tag_tickers(blob)
        ts = float(a.get("datetime") or 0)
        out.append({
            "title": title, "link": link, "summary": summary,
            "source": source, "category": category,
            "ts": ts,
            "iso": datetime.fromtimestamp(ts, timezone.utc).isoformat() if ts else "",
            "hot": hot, "market": hot or bool(tickers),
            "tickers": tickers, "tone": score_tone(blob),
        })
    return out


def fetch_finnhub_news():
    """General market news from Finnhub's free tier (skipped without a key)."""
    if not FINNHUB_API_KEY:
        return []
    url = ("https://finnhub.io/api/v1/news?category=general&token="
           + urllib.parse.quote(FINNHUB_API_KEY))
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
        rows = json.load(resp)
    return _finnhub_items(rows[:60] if isinstance(rows, list) else [])


def fetch_symbol_news(symbol):
    """Per-ticker company news (Bloomberg's CN-style view)."""
    if not FINNHUB_API_KEY:
        return []
    today = datetime.now(timezone.utc).date()
    frm = (today - timedelta(days=7)).isoformat()
    url = (f"https://finnhub.io/api/v1/company-news?symbol={urllib.parse.quote(symbol)}"
           f"&from={frm}&to={today.isoformat()}"
           f"&token={urllib.parse.quote(FINNHUB_API_KEY)}")
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
        rows = json.load(resp)
    items = _finnhub_items(rows[:60] if isinstance(rows, list) else [], source="Finnhub")
    # Finnhub's free company-news tags any article that merely mentions the
    # ticker, so it returns a lot of syndicated filler ("2 Beaten-Down GLP-1
    # Stocks" as NVDA news). Keep only stories that actually name the company.
    items = [it for it in items
             if _mentions(symbol, it["title"] + " " + it["summary"])]
    for it in items:
        if symbol.upper() not in it["tickers"]:
            it["tickers"] = [symbol.upper()] + it["tickers"][:3]
    return sorted(items, key=lambda x: x["ts"], reverse=True)


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

    if FINNHUB_API_KEY:
        try:
            all_items.extend(fetch_finnhub_news())
        except Exception as e:
            errors.append(f"Finnhub: {type(e).__name__}")

    # Dedupe by normalized title (keep newest)
    seen = {}
    for it in all_items:
        key = re.sub(r"[^a-z0-9]", "", it["title"].lower())[:80]
        if key not in seen or it["ts"] > seen[key]["ts"]:
            seen[key] = it
    deduped = sorted(seen.values(), key=lambda x: x["ts"], reverse=True)

    # Track when each story was first seen, so the UI can flash genuinely new
    # headlines. On the very first run nothing is "new" (first_seen = 0).
    now_ts = time.time()
    with _lock:
        first_run = not _seen_links
        for it in deduped:
            fs = _seen_links.get(it["link"])
            if fs is None:
                fs = 0 if first_run else now_ts
                _seen_links[it["link"]] = fs
            it["first_seen"] = fs
        live = {it["link"] for it in deduped}
        for link in [l for l in _seen_links if l not in live]:
            del _seen_links[link]

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
    # main() does the initial refresh, so sleep first (avoids a double fetch at
    # startup, which also spuriously flagged items as newly-seen).
    while True:
        time.sleep(REFRESH_FAST if market_is_active() else REFRESH_SLOW)
        try:
            refresh()
        except Exception as e:
            print("refresh error:", e)


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


def _fetch_group(group):
    """Fetch a list of (symbol, label) quotes, preserving the given order."""
    out = []
    with ThreadPoolExecutor(max_workers=8) as ex:
        futs = [ex.submit(fetch_quote, s, l) for s, l in group]
        for fut in as_completed(futs):
            try:
                out.append(fut.result())
            except Exception:
                pass
    order = {l: i for i, (_, l) in enumerate(group)}
    out.sort(key=lambda q: order.get(q["label"], 99))
    return out


def refresh_quotes():
    """Refresh the index strip, the macro board and the sector heatmap."""
    quotes = _fetch_group(QUOTES)
    macro = _fetch_group(MACRO)
    sectors = _fetch_group(SECTORS)
    with _lock:
        if quotes:
            _state["quotes"] = quotes
            _state["sentiment"] = compute_sentiment(quotes)
        if macro:
            _state["macro"] = macro
        if sectors:
            _state["sectors"] = sorted(sectors, key=lambda q: q["change"], reverse=True)


def quotes_refresher():
    while True:                       # main() does the initial fetch
        time.sleep(QUOTE_REFRESH_SECONDS)
        try:
            refresh_quotes()
        except Exception as e:
            print("quote refresh error:", e)


# --------------------------------------------------------------------------
# Chart data (Yahoo OHLC proxied server-side; browsers can't call it directly)
# --------------------------------------------------------------------------
RANGES = {"1d": "5m", "5d": "15m", "1mo": "1d", "6mo": "1d", "1y": "1d"}


def fetch_chart(symbol, rng="1d"):
    interval = RANGES.get(rng, "5m")
    key = f"{symbol}|{rng}"
    now = time.time()
    with _lock:
        hit = _charts.get(key)
        if hit and now - hit[0] < CHART_CACHE_SECONDS:
            return hit[1]

    url = ("https://query1.finance.yahoo.com/v8/finance/chart/"
           + urllib.parse.quote(symbol)
           + f"?range={rng}&interval={interval}")
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT, context=SSL_CTX) as resp:
        data = json.load(resp)

    res = (data.get("chart", {}).get("result") or [None])[0]
    if not res:
        raise RuntimeError("no chart data")
    meta = res.get("meta", {})
    stamps = res.get("timestamp") or []
    q = (res.get("indicators", {}).get("quote") or [{}])[0]
    o, h, l, c = (q.get("open") or [], q.get("high") or [],
                  q.get("low") or [], q.get("close") or [])
    candles = []
    for i, t in enumerate(stamps):
        try:
            if None in (o[i], h[i], l[i], c[i]):
                continue
            candles.append({"t": t, "o": round(o[i], 2), "h": round(h[i], 2),
                            "l": round(l[i], 2), "c": round(c[i], 2)})
        except Exception:
            continue
    price = meta.get("regularMarketPrice")
    prev = meta.get("chartPreviousClose") or meta.get("previousClose")
    payload = {
        "symbol": symbol,
        "name": meta.get("shortName") or symbol,
        "range": rng,
        "price": round(price, 2) if price else None,
        "change": round((price - prev) / prev * 100, 2) if price and prev else 0.0,
        "prev": round(prev, 2) if prev else None,
        "candles": candles[-320:],
    }
    with _lock:
        _charts[key] = (now, payload)
    return payload


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


def gemini_generate(prompt, max_tokens=700):
    body = json.dumps({
        "contents": [{"parts": [{"text": prompt}]}],
        # thinkingBudget 0 keeps the whole token budget for the answer (2.5-flash
        # otherwise spends part of it on internal reasoning and truncates output).
        "generationConfig": {"temperature": 0.3, "maxOutputTokens": max_tokens,
                             "thinkingConfig": {"thinkingBudget": 0}},
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


def gemini_summarize(title, context_text):
    prompt = (
        "You are a markets analyst. Summarize this financial news for a NASDAQ / "
        "S&P 500 trader using EXACTLY this structure and headings:\n"
        "Bias: <Bullish|Bearish|Neutral> for NASDAQ & S&P 500 (one word for the bias).\n"
        "What happened:\n"
        "- 2-3 bullet points with the key facts and numbers.\n"
        "Why it's happening: one or two sentences on the underlying cause/drivers "
        "behind the move.\n"
        "Why it matters: one sentence on the likely market impact.\n"
        "Be factual and concise. No preamble.\n\n"
        f"Headline: {title}\n\nArticle:\n{context_text}"
    )
    return gemini_generate(prompt, 700)


def compute_daily_bias():
    """Ask Gemini for the day's overall bullish/bearish read from the headlines."""
    if not GEMINI_API_KEY:
        return
    with _lock:
        items = [i for i in _state["items"] if i.get("market")][:25]
    if not items:
        return
    headlines = "\n".join(f"- {i['title']}" for i in items)
    prompt = (
        "You are a markets analyst. Based ONLY on these news headlines, give the "
        "overall bias for US equities (NASDAQ and S&P 500) for today. Respond on a "
        "SINGLE line in EXACTLY this format, nothing else:\n"
        "<Bullish|Bearish|Mixed> - <one short sentence explaining the net read>\n\n"
        "Headlines:\n" + headlines
    )
    try:
        txt = gemini_generate(prompt, 200)
    except Exception as e:
        print("daily bias error:", e)
        return
    low = txt.lower()
    label = "Bullish" if low.startswith("bull") else "Bearish" if low.startswith("bear") else "Mixed"
    rationale = txt
    for sep in (" - ", " — ", ":"):
        if sep in txt:
            rationale = txt.split(sep, 1)[1].strip()
            break
    with _lock:
        _state["daily_bias"] = {"label": label, "rationale": rationale[:240],
                                "updated": datetime.now(timezone.utc).isoformat()}
    print(f"[{datetime.now().strftime('%H:%M:%S')}] daily bias: {label}")


def daily_bias_refresher():
    while True:
        try:
            compute_daily_bias()
        except Exception as e:
            print("daily bias refresh error:", e)
        time.sleep(DAILY_BIAS_REFRESH_SECONDS)


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
        detail = ""
        try:
            detail = json.loads(e.read().decode("utf-8", "ignore")).get("error", {}).get("message", "")
        except Exception:
            pass
        if e.code == 429:
            return {"error": "Gemini free-tier rate limit hit. Wait a minute and retry."}
        return {"error": f"Summary failed (HTTP {e.code}): {detail[:200]}"}
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
                    "daily_bias": _state["daily_bias"],
                    "macro": _state["macro"],
                    "sectors": _state["sectors"],
                    "chart_tabs": [{"symbol": s, "label": l} for s, l in CHART_TABS],
                }
            self._send(200, json.dumps(payload))
        elif self.path.startswith("/api/symbolnews"):
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            symbol = (qs.get("symbol", [""])[0] or "").strip().upper()
            if not SYMBOL_RE.match(symbol):
                self._send(400, json.dumps({"error": "invalid symbol"}))
                return
            try:
                self._send(200, json.dumps({"items": fetch_symbol_news(symbol),
                                            "enabled": bool(FINNHUB_API_KEY)}))
            except Exception:
                self._send(200, json.dumps({"items": [], "enabled": bool(FINNHUB_API_KEY)}))
        elif self.path.startswith("/api/chart"):
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            symbol = (qs.get("symbol", [""])[0] or "").strip()
            rng = (qs.get("range", ["1d"])[0] or "1d").strip()
            if not SYMBOL_RE.match(symbol):
                self._send(400, json.dumps({"error": "invalid symbol"}))
                return
            if rng not in RANGES:
                rng = "1d"
            try:
                self._send(200, json.dumps(fetch_chart(symbol, rng)))
            except Exception:
                self._send(200, json.dumps({"error": f"No chart data for {symbol}."}))
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
  #modal-body .sum p strong{color:#a78bfa}
  #modal-body .sum p.li{padding-left:16px;position:relative;margin-bottom:5px}
  #modal-body .sum p.li:before{content:"▸";position:absolute;left:2px;color:var(--accent)}
  #modal-body .spin{color:var(--muted);font-size:13px;padding:14px 0}
  #modal-body .errmsg{color:#f0a0a0;font-size:13px;background:#241316;
    border:1px solid #50262c;padding:10px 12px;border-radius:8px}
  .modal-link{display:inline-block;margin-top:14px;font-size:13px;color:#fff;
    background:var(--accent);padding:7px 14px;border-radius:8px;text-decoration:none;font-weight:600}
  .cachenote{font-size:10.5px;color:var(--muted);margin-top:8px}
  /* per-article bias pill inside the summary modal */
  #modal-body .biaspill{display:inline-block;font-weight:800;font-size:12px;
    padding:4px 12px;border-radius:7px;margin-bottom:12px}
  #modal-body .biaspill.bull{background:#12492f;color:#46e08e}
  #modal-body .biaspill.bear{background:#5a1f25;color:#ff8088}
  #modal-body .biaspill.neut{background:#2a3550;color:#9db4e8}
  /* daily news bias banner under the ticker */
  .bias{display:flex;align-items:center;gap:11px;padding:8px 18px;font-size:12.5px;
    border-bottom:1px solid var(--border);flex-wrap:wrap}
  .bias .tag{color:var(--muted);font-size:10.5px;text-transform:uppercase;
    letter-spacing:.5px;font-weight:700}
  .bias .lab{font-weight:800;font-size:12px;padding:2px 11px;border-radius:6px}
  .bias .why{color:#aeb6c6;flex:1;min-width:200px}
  .bias.bull{background:#0c1f16} .bias.bull .lab{background:#12492f;color:#46e08e}
  .bias.bear{background:#1f0f12} .bias.bear .lab{background:#5a1f25;color:#ff8088}
  .bias.mixed{background:#161b26} .bias.mixed .lab{background:#2a3550;color:#9db4e8}
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
  /* ================= terminal layout ================= */
  /* Fixed-height app shell: the grid fills what's left and panels scroll
     internally, instead of the whole page growing to fit the news list. */
  html,body{height:100%}
  body{display:flex;flex-direction:column;overflow:hidden}
  header,.ticker,#bias{flex:0 0 auto}
  .ticker{position:static;top:auto}
  .cmdwrap{display:flex;align-items:center;gap:0;flex:1;max-width:420px}
  .cmdlabel{font-size:10px;font-weight:800;letter-spacing:.6px;color:#0b0e14;
    background:var(--accent);padding:7px 8px;border-radius:7px 0 0 7px}
  #cmd{flex:1;background:var(--panel2);border:1px solid var(--border);border-left:none;
    color:var(--text);padding:6px 11px;border-radius:0 7px 7px 0;outline:none;
    font-size:12.5px;font-family:ui-monospace,Consolas,monospace}
  #cmd:focus{border-color:var(--accent)}
  .grid{display:grid;grid-template-columns:1.45fr 1fr;
    grid-template-rows:1.2fr 1fr;gap:10px;padding:10px;flex:1;min-height:0}
  #p-chart{grid-column:1;grid-row:1}
  #p-news{grid-column:2;grid-row:1 / span 2}
  #p-bottom{grid-column:1;grid-row:2;display:grid;grid-template-columns:1fr 1fr;
    gap:10px;min-height:0}
  .panel{background:var(--panel);border:1px solid var(--border);border-radius:10px;
    display:flex;flex-direction:column;min-height:0;overflow:hidden}
  .phead{display:flex;align-items:center;gap:9px;padding:7px 11px;flex-wrap:wrap;
    border-bottom:1px solid var(--border);font-size:10.5px;font-weight:800;
    letter-spacing:.7px;text-transform:uppercase;color:var(--muted);background:var(--panel2)}
  .phead .spacer{flex:1}
  .phead .hint{font-weight:600;letter-spacing:.3px;text-transform:none}
  .pbody{flex:1;overflow:auto;min-height:0}
  .ctitle{text-transform:none;letter-spacing:0;font-size:12px;color:var(--text);font-weight:600}
  .ctitle b{font-size:13px}
  .minitabs{display:flex;gap:3px}
  .mt{background:var(--panel2);border:1px solid var(--border);color:var(--muted);
    font-size:10.5px;font-weight:700;padding:3px 8px;border-radius:5px;cursor:pointer}
  .mt:hover{color:var(--text);background:var(--hover)}
  .mt.on{background:var(--accent);color:#fff;border-color:var(--accent)}
  .chartbody{position:relative;padding:4px}
  #chart{display:block;width:100%;height:100%}
  .cmsg{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);
    color:var(--muted);font-size:12px}
  .nsearch{background:var(--bg);border:1px solid var(--border);color:var(--text);
    padding:4px 9px;border-radius:6px;outline:none;font-size:11.5px;width:150px;
    text-transform:none;letter-spacing:0;font-weight:400}
  .nsearch:focus{border-color:var(--accent)}
  #p-news .tabs{position:static;top:auto;padding:7px 9px;gap:3px}
  #p-news .tab{padding:3px 9px;font-size:11px}
  #list{padding:0 6px 8px}
  /* macro board */
  table.mb{width:100%;border-collapse:collapse;font-size:12px}
  table.mb td{padding:6px 11px;border-bottom:1px solid #161c28}
  table.mb td.n{color:var(--muted);font-size:11px}
  table.mb td.v{text-align:right;font-weight:700;
    font-family:ui-monospace,Consolas,monospace}
  table.mb td.c{text-align:right;font-weight:700;width:78px;
    font-family:ui-monospace,Consolas,monospace}
  /* sector heatmap */
  .heat{display:grid;grid-template-columns:repeat(auto-fill,minmax(84px,1fr));
    gap:4px;padding:7px}
  .tile{border-radius:6px;padding:7px 6px;display:flex;flex-direction:column;gap:1px;
    min-height:56px;justify-content:center}
  .tile .tl{font-size:12px;font-weight:800;color:#fff}
  .tile .tc{font-size:12px;font-weight:800;color:#fff;
    font-family:ui-monospace,Consolas,monospace}
  .tile .tn{font-size:9px;color:rgba(255,255,255,.75);text-transform:uppercase;
    letter-spacing:.3px}
  @media(max-width:1000px){
    /* phones/tablets: let the page scroll normally again */
    body{height:auto;overflow:auto}
    .grid{flex:none;grid-template-columns:1fr;grid-template-rows:auto}
    #p-chart,#p-news,#p-bottom{grid-column:1;grid-row:auto}
    #p-chart{height:300px} #p-news{height:75vh}
    #p-bottom{grid-template-columns:1fr;gap:10px}
    #p-bottom .panel{min-height:220px}
    .cmdwrap{max-width:none}
    header{flex-wrap:wrap}
  }
  /* ---- news: tone dot, ticker chips, breaking flash, symbol filter ---- */
  .tone{display:inline-block;width:7px;height:7px;border-radius:50%;margin-right:6px;
    flex:0 0 auto}
  .tone.bull{background:#3fd089} .tone.bear{background:#f0656a} .tone.neutral{background:#4a5670}
  .tk{font-size:10.5px;font-weight:800;color:#0b0e14;background:#8ea6d8;
    padding:1px 6px;border-radius:4px;cursor:pointer;letter-spacing:.3px}
  .tk:hover{background:var(--accent);color:#fff}
  .item.fresh{border-left:2px solid var(--accent);animation:flash 1.6s ease-out}
  @keyframes flash{0%{background:#16305e}100%{background:transparent}}
  .newchip{font-size:9.5px;font-weight:800;color:#fff;background:var(--accent);
    padding:1px 5px;border-radius:4px;letter-spacing:.4px}
  #symchip{display:flex;align-items:center;gap:6px}
  .sfilter{display:flex;align-items:center;gap:6px;background:var(--accent);color:#fff;
    font-size:10.5px;font-weight:800;padding:2px 8px;border-radius:5px;letter-spacing:.4px}
  .sfilter b{cursor:pointer}
  .bell{background:var(--panel2);border:1px solid var(--border);color:var(--muted);
    font-size:13px;padding:4px 9px;border-radius:7px;cursor:pointer}
  .bell.on{background:var(--hot);color:#1a1206;border-color:var(--hot)}
  ::-webkit-scrollbar{width:10px}
  ::-webkit-scrollbar-thumb{background:#222a39;border-radius:6px}
  ::-webkit-scrollbar-track{background:transparent}
</style>
</head>
<body>
<header>
  <h1><span class="dot">●</span> MACRO TERMINAL</h1>
  <div class="cmdwrap">
    <span class="cmdlabel">CMD</span>
    <input id="cmd" autocomplete="off" spellcheck="false"
           placeholder="Symbol + Enter — NQ, ES, SPX, VIX, DXY, AAPL, BTC…">
  </div>
  <div class="status" id="status">loading…</div>
</header>
<div class="ticker" id="ticker"></div>
<div id="bias"></div>

<div class="grid">
  <section class="panel" id="p-chart">
    <div class="phead">
      <span>Chart</span>
      <span id="chart-title" class="ctitle"></span>
      <span class="spacer"></span>
      <span class="minitabs" id="chart-tabs"></span>
      <span class="minitabs" id="range-tabs"></span>
    </div>
    <div class="pbody chartbody">
      <canvas id="chart"></canvas>
      <div id="chart-msg" class="cmsg"></div>
    </div>
  </section>

  <section class="panel" id="p-news">
    <div class="phead">
      <span>News</span>
      <span id="symchip"></span>
      <span class="spacer"></span>
      <button class="bell" id="bell" onclick="toggleAlerts()" title="Alert me on new hot headlines">🔔</button>
      <input id="q" class="nsearch" placeholder="Search headlines…" autocomplete="off">
    </div>
    <div class="tabs" id="tabs"></div>
    <div id="errbar"></div>
    <div class="pbody" id="list"></div>
  </section>

  <section id="p-bottom">
    <section class="panel">
      <div class="phead"><span>Macro Board</span></div>
      <div class="pbody" id="macro"></div>
    </section>
    <section class="panel">
      <div class="phead"><span>Sectors</span><span class="spacer"></span>
        <span class="hint">today %</span></div>
      <div class="pbody" id="sectors"></div>
    </section>
  </section>
</div>

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

function biasClass(v){ const s=(v||'').toLowerCase();
  return s.includes('bull')?'bull':s.includes('bear')?'bear':'neut'; }
function biasIcon(c){ return c==='bull'?'🟢':c==='bear'?'🔴':'⚪'; }

function renderSummary(text){
  return text.split('\n').map(s=>s.trim()).filter(Boolean).map(l=>{
    l = l.replace(/\*\*/g,'');
    const bm = l.match(/^bias:\s*(.+)$/i);
    if(bm){
      const c = biasClass(bm[1]);
      const word = c==='bull'?'Bullish':c==='bear'?'Bearish':'Neutral';
      return '<div class="biaspill '+c+'">'+biasIcon(c)+' '+word+' · NASDAQ &amp; S&amp;P 500</div>';
    }
    if(/^[\*\-•]/.test(l)) return '<p class="li">'+esc(l.replace(/^[\*\-•]\s*/,''))+'</p>';
    const m = l.match(/^([A-Za-z][^:]{2,28}:)(.*)$/);
    if(m) return '<p><strong>'+esc(m[1])+'</strong>'+esc(m[2])+'</p>';
    return '<p>'+esc(l)+'</p>';
  }).join('');
}

/* ---------------- chart ---------------- */
let CHART = {symbol:'NQ=F', range:'1d', data:null, init:false};
const RANGE_TABS = [['1d','1D'],['5d','5D'],['1mo','1M'],['6mo','6M'],['1y','1Y']];
const ALIASES = {NQ:'NQ=F',ES:'ES=F',YM:'YM=F',RTY:'RTY=F',SPX:'^GSPC',SP500:'^GSPC',
  NDX:'^IXIC',COMP:'^IXIC',NASDAQ:'^IXIC',DJI:'^DJI',DOW:'^DJI',VIX:'^VIX',
  BTC:'BTC-USD',ETH:'ETH-USD',GOLD:'GC=F',GC:'GC=F',OIL:'CL=F',CL:'CL=F',
  DXY:'DX-Y.NYB',US10Y:'^TNX',TNX:'^TNX',US30Y:'^TYX'};

function renderChartTabs(){
  document.getElementById('chart-tabs').innerHTML = (DATA.chart_tabs||[])
    .map(t=>`<button class="mt ${t.symbol===CHART.symbol?'on':''}" onclick="loadChart('${t.symbol}')">${esc(t.label)}</button>`).join('');
  document.getElementById('range-tabs').innerHTML = RANGE_TABS
    .map(([v,l])=>`<button class="mt ${v===CHART.range?'on':''}" onclick="loadChart(null,'${v}')">${l}</button>`).join('');
}

async function loadChart(sym, rng){
  const changed = sym && sym !== CHART.symbol;
  if(sym) CHART.symbol = sym;
  if(rng) CHART.range = rng;
  // Loading an equity ticker also pulls that ticker's news (Bloomberg CN-style).
  // Index/futures symbols (^GSPC, NQ=F) have no company news, so clear it.
  if(changed) setSymbolFilter(EQUITY_RE.test(CHART.symbol) ? CHART.symbol : null);
  const msg = document.getElementById('chart-msg');
  renderChartTabs();
  msg.textContent = 'Loading ' + CHART.symbol + '…';
  try{
    const r = await fetch('/api/chart?symbol='+encodeURIComponent(CHART.symbol)+'&range='+CHART.range);
    const d = await r.json();
    if(d.error || !d.candles || !d.candles.length){
      CHART.data = null; drawChart();
      msg.textContent = d.error || ('No chart data for '+CHART.symbol);
      document.getElementById('chart-title').textContent = '';
      return;
    }
    CHART.data = d; msg.textContent = '';
    const c = cls(d.change);
    document.getElementById('chart-title').innerHTML =
      esc(d.name)+' <b>'+(d.price!=null?d.price.toLocaleString():'—')+'</b> '+
      '<span class="'+c+'">'+arrow(d.change)+' '+(d.change>=0?'+':'')+d.change+'%</span>';
    drawChart();
  }catch(e){ msg.textContent = 'Chart unavailable.'; }
}

function drawChart(){
  const cv = document.getElementById('chart'), box = cv.parentElement;
  const dpr = window.devicePixelRatio || 1;
  const W = box.clientWidth, H = box.clientHeight;
  if(W<10 || H<10) return;
  cv.width = W*dpr; cv.height = H*dpr; cv.style.width = W+'px'; cv.style.height = H+'px';
  const x = cv.getContext('2d'); x.setTransform(dpr,0,0,dpr,0,0); x.clearRect(0,0,W,H);
  const d = CHART.data; if(!d || !d.candles.length) return;
  const c = d.candles, padL=8, padR=58, padT=10, padB=20;
  const w = W-padL-padR, h = H-padT-padB;
  let lo=Infinity, hi=-Infinity;
  c.forEach(k=>{ lo=Math.min(lo,k.l); hi=Math.max(hi,k.h); });
  if(d.prev){ lo=Math.min(lo,d.prev); hi=Math.max(hi,d.prev); }
  const pad=(hi-lo)*0.06 || 1; lo-=pad; hi+=pad;
  const Y = v => padT + (hi-v)/(hi-lo)*h;
  const n = c.length, step = w/n, cw = Math.max(1, step*0.62);
  x.font='10px ui-monospace,Consolas,monospace'; x.lineWidth=1;
  for(let i=0;i<=4;i++){
    const v = lo + (hi-lo)*i/4, yy = Y(v);
    x.strokeStyle='#161c28'; x.beginPath(); x.moveTo(padL,yy); x.lineTo(padL+w,yy); x.stroke();
    x.fillStyle='#7d879c'; x.fillText(v.toFixed(2), padL+w+6, yy+3);
  }
  if(d.prev){
    x.save(); x.setLineDash([4,4]); x.strokeStyle='#6b7794';
    const yy=Y(d.prev); x.beginPath(); x.moveTo(padL,yy); x.lineTo(padL+w,yy); x.stroke(); x.restore();
  }
  c.forEach((k,i)=>{
    const cx = padL + i*step + step/2, up = k.c>=k.o;
    x.strokeStyle = up ? '#3fd089' : '#f0656a'; x.fillStyle = x.strokeStyle;
    x.beginPath(); x.moveTo(cx, Y(k.h)); x.lineTo(cx, Y(k.l)); x.stroke();
    const yo=Y(k.o), yc=Y(k.c);
    x.fillRect(cx-cw/2, Math.min(yo,yc), cw, Math.max(1, Math.abs(yc-yo)));
  });
  x.fillStyle='#7d879c'; const intraday = (CHART.range==='1d'||CHART.range==='5d');
  [0, Math.floor(n/2), n-1].forEach(i=>{
    if(!c[i]) return;
    const dt = new Date(c[i].t*1000);
    const lab = intraday ? dt.toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'})
                         : dt.toLocaleDateString([], {month:'short', day:'numeric'});
    const cx = Math.min(Math.max(padL+i*step+step/2-16, padL), padL+w-32);
    x.fillText(lab, cx, H-6);
  });
}
window.addEventListener('resize', drawChart);

/* ---------------- macro board + sectors ---------------- */
function renderMacro(){
  const el = document.getElementById('macro'), m = DATA.macro||[];
  if(!m.length){ el.innerHTML=''; return; }
  el.innerHTML = '<table class="mb">' + m.map(q=>`<tr>
      <td class="n">${esc(q.label)}</td>
      <td class="v">${q.price!=null?q.price.toLocaleString():'—'}</td>
      <td class="c ${cls(q.change)}">${arrow(q.change)} ${(q.change>=0?'+':'')}${q.change}%</td>
    </tr>`).join('') + '</table>';
}

function renderSectors(){
  const el = document.getElementById('sectors'), s = DATA.sectors||[];
  if(!s.length){ el.innerHTML=''; return; }
  const mx = Math.max(...s.map(q=>Math.abs(q.change)), 0.5);
  el.innerHTML = '<div class="heat">' + s.map(q=>{
    const a = Math.min(1, Math.abs(q.change)/mx)*0.8 + 0.2;
    const bg = q.change>=0 ? `rgba(24,140,86,${a})` : `rgba(200,58,68,${a})`;
    return `<div class="tile" style="background:${bg}" title="${esc(q.label)}">
      <span class="tl">${esc(q.symbol)}</span>
      <span class="tc">${(q.change>=0?'+':'')}${q.change}%</span>
      <span class="tn">${esc(q.label)}</span></div>`;
  }).join('') + '</div>';
}

function renderBias(){
  const el = document.getElementById('bias');
  const b = DATA.daily_bias || {};
  if(!b.label){ el.innerHTML = ''; return; }
  const c = b.label==='Bullish'?'bull':b.label==='Bearish'?'bear':'mixed';
  const icon = b.label==='Bullish'?'🟢':b.label==='Bearish'?'🔴':'⚪';
  el.innerHTML = `<div class="bias ${c}">
    <span class="tag">📊 Daily News Bias</span>
    <span class="lab">${icon} ${esc(b.label)}</span>
    <span class="why">${esc(b.rationale||'')}</span>
  </div>`;
}

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
      body.innerHTML = '<div class="sum">' + renderSummary(d.summary) + '</div>'
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

/* ---------------- symbol filter (news-by-ticker) ---------------- */
let SYMFILTER = null, SYMNEWS = [];
const EQUITY_RE = /^[A-Z][A-Z.\-]{0,5}$/;

async function setSymbolFilter(sym){
  if(!sym || !EQUITY_RE.test(sym)){ SYMFILTER=null; SYMNEWS=[]; renderSymChip(); render(); return; }
  SYMFILTER = sym; SYMNEWS = [];
  renderSymChip(); render();
  try{
    const r = await fetch('/api/symbolnews?symbol='+encodeURIComponent(sym));
    const d = await r.json();
    SYMNEWS = d.items || [];
  }catch(e){ SYMNEWS = []; }
  render();
}
function clearSymbolFilter(){ SYMFILTER=null; SYMNEWS=[]; renderSymChip(); render(); }
function renderSymChip(){
  const el = document.getElementById('symchip');
  el.innerHTML = SYMFILTER
    ? `<span class="sfilter">${esc(SYMFILTER)} <b onclick="clearSymbolFilter()">✕</b></span>` : '';
}

/* ---------------- breaking alerts ---------------- */
let ALERTS = false;
const NOTIFIED = new Set();
function toggleAlerts(){
  ALERTS = !ALERTS;
  if(ALERTS && window.Notification && Notification.permission === 'default'){
    Notification.requestPermission();
  }
  document.getElementById('bell').classList.toggle('on', ALERTS);
}
function checkBreaking(){
  const nowS = Date.now()/1000;
  (DATA.items||[]).forEach(i=>{
    if(!i.hot || !i.first_seen || nowS - i.first_seen > 180) return;
    if(NOTIFIED.has(i.link)) return;
    NOTIFIED.add(i.link);
    if(ALERTS && window.Notification && Notification.permission === 'granted'){
      try{ new Notification('📈 ' + i.source, {body: i.title}); }catch(e){}
    }
  });
}

function render(){
  renderTabs();
  let items = DATA.items;
  if(SYMFILTER){
    const local = items.filter(i=>(i.tickers||[]).includes(SYMFILTER));
    const seenL = new Set(local.map(i=>i.link));
    items = local.concat(SYMNEWS.filter(i=>!seenL.has(i.link)))
                 .sort((a,b)=>(b.ts||0)-(a.ts||0));
  }
  else if(hotOnly) items = items.filter(i=>i.hot);
  else if(activeCat===MARKET_TAB) items = items.filter(i=>i.market);   // NASDAQ/S&P 500 only
  else if(activeCat!=="All") items = items.filter(i=>i.category===activeCat);
  if(query){
    const q = query.toLowerCase();
    items = items.filter(i=>(i.title+" "+i.summary+" "+i.source).toLowerCase().includes(q));
  }
  const list = document.getElementById('list');
  if(!items.length){
    list.innerHTML = SYMFILTER
      ? `<div class="empty">No recent news tagged <b>${esc(SYMFILTER)}</b>.<br><span style="font-size:11px">Add a free FINNHUB_API_KEY for full per-ticker news.</span></div>`
      : '<div class="empty">No matching headlines.</div>';
    return;
  }
  RENDERED = items;
  const nowS = Date.now()/1000;
  list.innerHTML = items.map((i,idx)=>{
    const isNew = i.first_seen && (nowS - i.first_seen) < 300;
    return `
    <div class="item ${i.hot?'hot':''} ${isNew?'fresh':''}" onclick="openSummary(${idx})" title="Click for an AI summary">
      <div class="meta"><div class="time">${fmtClock(i.ts)}</div><div>${timeAgo(i.ts)} ago</div></div>
      <div class="body">
        <p class="title"><span class="tone ${i.tone||'neutral'}"></span>${esc(i.title)}</p>
        ${i.summary?`<p class="summary">${esc(i.summary)}</p>`:''}
        <div class="badges">
          ${isNew?'<span class="newchip">NEW</span>':''}
          ${(i.tickers||[]).map(t=>`<span class="tk" onclick="event.stopPropagation();loadChart('${t}')">${esc(t)}</span>`).join('')}
          <span class="badge">${esc(i.source)}</span>
          <span class="badge cat">${esc(i.category)}</span>
          <a class="src" href="${esc(i.link)}" target="_blank" rel="noopener" onclick="event.stopPropagation()">↗ source</a>
        </div>
      </div>
    </div>`;}).join("");

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
    renderBias();
    renderMacro();
    renderSectors();
    checkBreaking();
    render();
    if(!CHART.init){ CHART.init = true; loadChart(); }
  }catch(e){
    document.getElementById('status').textContent = "connection error";
  }
}

document.getElementById('q').addEventListener('input', e=>{query=e.target.value; render();});

document.getElementById('cmd').addEventListener('keydown', e=>{
  if(e.key !== 'Enter') return;
  let v = e.target.value.trim().toUpperCase();
  if(!v) return;
  loadChart(ALIASES[v] || v, CHART.range);
  e.target.value = '';
});
// "/" focuses the command bar, terminal-style
document.addEventListener('keydown', e=>{
  if(e.key === '/' && document.activeElement.tagName !== 'INPUT'){
    e.preventDefault(); document.getElementById('cmd').focus();
  }
});

load();
setInterval(load, 30000);              // poll backend every 30s (served from memory)
setInterval(()=>render(), 30000);      // refresh relative timestamps
setInterval(()=>loadChart(), 60000);   // refresh the chart (server caches 60s)
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
    threading.Thread(target=daily_bias_refresher, daemon=True).start()
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

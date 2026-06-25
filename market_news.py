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
import json
import re
import ssl
import sys
import threading
import time
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import os

# Cloud hosts inject the port via $PORT and expect binding on 0.0.0.0.
# Locally these default to 8765 / localhost.
PORT = int(os.environ.get("PORT", "8765"))
HOST = os.environ.get("HOST", "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1")
REFRESH_SECONDS = 180          # background refresh interval
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

    # --- Tech / Nasdaq-heavy ---
    ("CNBC Technology",   "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=19854910", "Tech"),
    ("Nasdaq Tech",       "https://www.nasdaq.com/feed/rssoutbound?category=Technology",                          "Tech"),

    # --- Finance / Investing ---
    ("CNBC Finance",      "https://search.cnbc.com/rs/search/combinedcms/view.xml?partnerId=wrss01&id=10000664", "Finance"),
    ("Investing Stocks",  "https://www.investing.com/rss/news_25.rss",                                            "Finance"),
]

# Terms that flag an item as especially relevant to NASDAQ / S&P 500 macro.
HOT_TERMS = [
    r"\bS&P\s*500\b", r"\bS&P500\b", r"\bSPX\b", r"\bnasdaq\b", r"\bndx\b",
    r"\bdow\b", r"\bfed(eral reserve)?\b", r"\bfomc\b", r"\bpowell\b",
    r"\binflation\b", r"\bcpi\b", r"\bpce\b", r"\bppi\b", r"\bjobs report\b",
    r"\bnonfarm\b", r"\bpayrolls?\b", r"\brate (cut|hike|decision)\b",
    r"\binterest rates?\b", r"\bgdp\b", r"\brecession\b", r"\byields?\b",
    r"\btreasur(y|ies)\b", r"\bunemployment\b", r"\bbond\b", r"\bearnings\b",
    r"\bmega.?cap\b", r"\bbig tech\b", r"\bsemiconductor\b", r"\bAI\b",
]
HOT_RE = re.compile("|".join(HOT_TERMS), re.IGNORECASE)

# Strip HTML tags from summaries.
TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"\s+")

_lock = threading.Lock()
_state = {"items": [], "updated": None, "errors": []}


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
        items.append({
            "title": title,
            "link": link,
            "summary": summary[:280],
            "source": name,
            "category": category,
            "ts": dt.timestamp() if dt else 0,
            "iso": dt.isoformat() if dt else "",
            "hot": bool(HOT_RE.search(title + " " + summary)),
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


def background_refresher():
    while True:
        try:
            refresh()
        except Exception as e:
            print("refresh error:", e)
        time.sleep(REFRESH_SECONDS)


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
                    "categories": sorted({c for _, _, c in FEEDS}),
                }
            self._send(200, json.dumps(payload))
        elif self.path.startswith("/api/refresh"):
            threading.Thread(target=refresh, daemon=True).start()
            self._send(200, json.dumps({"ok": True}))
        elif self.path == "/" or self.path.startswith("/index"):
            self._send(200, PAGE, "text/html")
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
    text-decoration:none;color:inherit;border-radius:8px}
  .item:hover{background:var(--hover)}
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
<div class="tabs" id="tabs"></div>
<div id="errbar"></div>
<div class="wrap"><div id="list"></div></div>

<script>
let DATA = {items:[], updated:null, errors:[], categories:[]};
let activeCat = "All";
let hotOnly = false;
let query = "";

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
  else if(activeCat!=="All") items = items.filter(i=>i.category===activeCat);
  if(query){
    const q = query.toLowerCase();
    items = items.filter(i=>(i.title+" "+i.summary+" "+i.source).toLowerCase().includes(q));
  }
  const list = document.getElementById('list');
  if(!items.length){ list.innerHTML='<div class="empty">No matching headlines.</div>'; return; }
  list.innerHTML = items.map(i=>`
    <a class="item ${i.hot?'hot':''}" href="${esc(i.link)}" target="_blank" rel="noopener">
      <div class="meta"><div class="time">${fmtClock(i.ts)}</div><div>${timeAgo(i.ts)} ago</div></div>
      <div class="body">
        <p class="title">${esc(i.title)}</p>
        ${i.summary?`<p class="summary">${esc(i.summary)}</p>`:''}
        <div class="badges">
          <span class="badge">${esc(i.source)}</span>
          <span class="badge cat">${esc(i.category)}</span>
        </div>
      </div>
    </a>`).join("");

  const errbar = document.getElementById('errbar');
  errbar.innerHTML = DATA.errors.length
    ? `<div class="err">⚠ ${DATA.errors.length} feed(s) unavailable: ${esc(DATA.errors.map(e=>e.split(':')[0]).join(', '))}</div>`
    : "";
}

async function load(){
  try{
    const r = await fetch('/api/news');
    DATA = await r.json();
    const upd = DATA.updated ? new Date(DATA.updated).toLocaleTimeString() : "—";
    document.getElementById('status').textContent =
      `${DATA.items.length} headlines · updated ${upd}`;
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
    threading.Thread(target=background_refresher, daemon=True).start()
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

# Macro News Terminal

A Koyfin-style dark macro-news aggregator focused on **NASDAQ / S&P 500**.
Single Python file, **zero dependencies** (stdlib only), no API keys.

It pulls free public RSS feeds (CNBC, MarketWatch, Yahoo Finance, Investing.com,
Nasdaq, and the Federal Reserve), dedupes and sorts them by recency, and flags
headlines that mention key macro/index terms (S&P 500, Fed, CPI, rates, yields…).

## Run locally

```bash
python market_news.py
```

Then open <http://localhost:8765>.

## Features

- Category tabs: Macro · Fed · Markets · Tech · Finance, plus a 🔥 Hot filter
- Live headline search
- Auto-refresh (backend every 3 min, UI every 60 s)
- Click-through to the source article

## Configure

Edit the top of `market_news.py`:

- `FEEDS` — add/remove RSS sources
- `HOT_TERMS` — tune which headlines get flagged
- `REFRESH_SECONDS` — how often feeds are re-pulled

## Deploy (free)

The app reads `$PORT` and binds `0.0.0.0` automatically, so it runs on most
Python hosts unchanged. A `render.yaml` blueprint is included for
[Render](https://render.com)'s free tier — connect this repo as a new
**Web Service** and it deploys automatically.

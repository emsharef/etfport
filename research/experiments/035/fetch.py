"""Experiment 035: fetch monthly adjusted closes from Yahoo Finance (yfinance) for the pre-registered tickers, and the SEC
mutual-fund ticker map for the ETFs' expense ratios. Registered design: experiments/035-yahoo-pilot.md.
Run: uv run python experiments/035/fetch.py

Survivor-only: these are funds that exist today. Raw data is cached under experiments/035/cache/ (gitignored) and never
committed. At most one Yahoo request per second; sec.gov with the lab's User-Agent (ops/lab.toml).
"""
import datetime as dt
import json
import time
import tomllib
import urllib.request
from pathlib import Path

import yfinance as yf

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"


def main():
    CACHE.mkdir(exist_ok=True)
    tick = json.load(open(HERE / "tickers.json"))
    log = {"fetch_date": dt.date.today().isoformat(), "yahoo": {}}
    for group, names in tick.items():
        for t in names:
            f = CACHE / f"{t}_max.csv"                   # Deviation 3: each ticker's full history (first month), not from 1990
            if not f.exists():
                d = yf.download(t, start="1900-01-01", end="2025-07-01", interval="1mo", auto_adjust=True, progress=False)
                d.to_csv(f)
                time.sleep(1.0)
            log["yahoo"][t] = f.stat().st_size
    f = CACHE / "company_tickers_mf.json"
    if not f.exists():
        ua = tomllib.loads((ROOT / "ops" / "lab.toml").read_text())["sec_user_agent"]
        req = urllib.request.Request("https://www.sec.gov/files/company_tickers_mf.json", headers={"User-Agent": ua})
        f.write_bytes(urllib.request.urlopen(req, timeout=120).read())
    json.dump(log, open(CACHE / "fetch_log.json", "w"), indent=1)
    print(json.dumps(log, indent=1))


if __name__ == "__main__":
    main()

"""Experiment 041: fetch monthly adjusted closes (yfinance) for the committed universe, and the French Developed ex US
five-factor file. Raw data is cached under experiments/041/cache (gitignored) and never committed.
Run: uv run python experiments/041/fetch.py
"""
import datetime as dt
import hashlib
import json
import time
import urllib.request
from pathlib import Path

import yfinance as yf

HERE = Path(__file__).resolve().parent
CACHE = HERE / "cache"
DEV_URL = "https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/ftp/Developed_ex_US_5_Factors_CSV.zip"


def main():
    CACHE.mkdir(exist_ok=True)
    U = json.load(open(HERE / "universe.json"))
    log = {"fetch_date": dt.date.today().isoformat(), "yahoo_rows": {}}
    for f in U["funds"]:
        t = f["ticker"]; p = CACHE / f"{t}.csv"
        if not p.exists():
            d = yf.download(t, start="1990-01-01", end="2025-07-01", interval="1mo", auto_adjust=True, progress=False)
            d.to_csv(p); time.sleep(1.0)
        log["yahoo_rows"][t] = sum(1 for _ in open(p)) - 3
    for t in ("IWM",):                                   # Deviation 3: the registered claim-105 menu ETF not in the rule-built universe
        p = CACHE / f"{t}.csv"
        if not p.exists():
            yf.download(t, start="1990-01-01", end="2025-07-01", interval="1mo", auto_adjust=True, progress=False).to_csv(p); time.sleep(1.0)
    z = CACHE / "developed_ex_us_5.zip"
    if not z.exists():
        z.write_bytes(urllib.request.urlopen(urllib.request.Request(DEV_URL, headers={"User-Agent": "Mozilla/5.0"}), timeout=120).read())
    log["developed_ex_us_sha256"] = hashlib.sha256(z.read_bytes()).hexdigest()
    json.dump(log, open(CACHE / "fetch_log.json", "w"), indent=1)
    print(log["fetch_date"], log["developed_ex_us_sha256"], sum(v >= 60 for v in log["yahoo_rows"].values()), "of", len(log["yahoo_rows"]), "with >= 60 rows")


if __name__ == "__main__":
    main()

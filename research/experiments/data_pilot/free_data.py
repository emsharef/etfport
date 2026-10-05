"""Route 3 free-data pilot feasibility (backlog item; results go to experiments/DATA.md).
A survivor-only pilot feasibility check (AGENTS.md rule 19), not a historical evaluation.

1. SEC N-CEN data sets (sec.gov, User-Agent from ops/lab.toml): series reporting and series terminated
   (Item B.6, TERMINATED_ORGANIZATION) in filings made in 2023 and 2024; class tickers (SHARES_OUTSTANDING).
2. Yahoo Finance chart endpoint (the API yfinance wraps; yfinance itself is not added to the environment):
   coverage for fixed-seed random samples of (a) surviving non-index, non-ETF, non-money-market series,
   (b) ETFs, (c) series terminated in 2024 filings, tickers taken from their 2023 filings. One class ticker per
   series: the alphabetically first. One request per second.
3. FRED CSV availability (DTB3, DGS1MO).
Caches downloads under experiments/data_pilot/cache (never committed); writes results.json (counts, dates,
public tickers only; no prices).
"""
from __future__ import annotations

import csv
import io
import json
import random
import sys
import time
import tomllib
import urllib.request
import zipfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"
QUARTERS = [f"{y}q{q}" for y in (2023, 2024) for q in range(1, 5)]
SEED = 2029
N_ACTIVE, N_ETF, N_DEAD = 40, 30, 40
csv.field_size_limit(10 ** 9)


def ua_sec():
    return tomllib.loads((ROOT / "ops" / "lab.toml").read_text())["sec_user_agent"]


def get(url, ua, timeout=120):
    req = urllib.request.Request(url, headers={"User-Agent": ua})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.status, r.read()


def ncen(q):
    CACHE.mkdir(exist_ok=True)
    f = CACHE / f"{q}_ncen.zip"
    if not f.exists():
        _, b = get(f"https://www.sec.gov/files/dera/data/form-n-cen-data-sets/{q}_ncen.zip", ua_sec())
        f.write_bytes(b)
        time.sleep(0.5)
    return zipfile.ZipFile(f)


def rows(z, name):
    return list(csv.DictReader(io.TextIOWrapper(z.open(name), encoding="latin-1"), delimiter="\t"))


def yahoo(ticker):
    url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker}?range=max&interval=1mo"
           "&events=div%7Csplit")
    try:
        status, b = get(url, "Mozilla/5.0 (etfport-lab research)", timeout=30)
        d = json.loads(b)
        res = (d.get("chart") or {}).get("result")
        if not res:
            return dict(status=status, ok=False)
        r = res[0]
        ts = r.get("timestamp") or []
        adj = ((r.get("indicators") or {}).get("adjclose") or [{}])[0].get("adjclose")
        return dict(status=status, ok=bool(ts), months=len(ts),
                    first=time.strftime("%Y-%m", time.gmtime(ts[0])) if ts else None,
                    last=time.strftime("%Y-%m", time.gmtime(ts[-1])) if ts else None,
                    adjclose=bool(adj), type=(r.get("meta") or {}).get("instrumentType"))
    except Exception as e:  # noqa: BLE001 - recorded, not hidden
        return dict(status=getattr(e, "code", None), ok=False, error=type(e).__name__)


def main():
    t0 = time.time()
    by_year = defaultdict(lambda: dict(series={}, terminated={}, tickers=defaultdict(set)))
    for q in QUARTERS:
        z = ncen(q)
        sub = {r["ACCESSION_NUMBER"]: r["FILING_DATE"][-4:] for r in rows(z, "SUBMISSION.tsv")}
        fri = rows(z, "FUND_REPORTED_INFO.tsv")
        fund_series = {r["FUND_ID"]: r["SERIES_ID"] for r in fri}
        for r in fri:
            y = sub.get(r["ACCESSION_NUMBER"])
            by_year[y]["series"][r["SERIES_ID"]] = r
        for r in rows(z, "TERMINATED_ORGANIZATION.tsv"):
            y = sub.get(r["ACCESSION_NUMBER"])
            by_year[y]["terminated"][r["SERIES_ID"]] = r
        for r in rows(z, "SHARES_OUTSTANDING.tsv"):
            s = fund_series.get(r["FUND_ID"])
            t = (r.get("TICKER") or "").strip().upper()
            if s and t and t not in ("N/A", "NONE", "NA"):
                y = sub.get(next((a for a in [r.get("ACCESSION_NUMBER")] if a), ""), None)
                for yy in ("2023", "2024"):
                    if s in by_year[yy]["series"]:
                        by_year[yy]["tickers"][s].add(t)
    out = {"ncen": {}}
    for y in ("2023", "2024"):
        B = by_year[y]
        ser = B["series"]
        kinds = defaultdict(int)
        for r in ser.values():
            k = ("ETF" if r["IS_ETF"] == "Y" else "money market" if r["IS_MONEY_MARKET"] == "Y" else
                 "index (non-ETF)" if r["IS_INDEX"] == "Y" else "other (active, incl. fund of funds)")
            kinds[k] += 1
        out["ncen"][y] = dict(series_reporting=len(ser), series_terminated=len(B["terminated"]),
                              terminated_per_reporting=len(B["terminated"]) / max(1, len(ser)),
                              by_kind=dict(kinds), series_with_ticker=sum(1 for s in ser if B["tickers"].get(s)))
    rng = random.Random(SEED)
    s24, t23 = by_year["2024"], by_year["2023"]
    active = sorted(s for s, r in s24["series"].items() if r["IS_ETF"] != "Y" and r["IS_MONEY_MARKET"] != "Y"
                    and r["IS_INDEX"] != "Y" and r["IS_FUND_OF_FUND"] != "Y" and s24["tickers"].get(s))
    etfs = sorted(s for s, r in s24["series"].items() if r["IS_ETF"] == "Y" and s24["tickers"].get(s))
    dead = sorted(s for s in s24["terminated"] if t23["tickers"].get(s))
    samples = {"surviving active": (rng.sample(active, N_ACTIVE), s24["tickers"]),
               "ETF": (rng.sample(etfs, N_ETF), s24["tickers"]),
               "terminated in 2024 filings": (rng.sample(dead, min(N_DEAD, len(dead))), t23["tickers"])}
    out["pools"] = dict(active=len(active), etf=len(etfs), dead_with_2023_ticker=len(dead),
                        dead_total=len(s24["terminated"]))
    out["yahoo"] = {}
    for name, (ids, tick) in samples.items():
        res = []
        for s in ids:
            t = sorted(tick[s])[0]
            r = yahoo(t)
            r.update(series=s, ticker=t)
            res.append(r)
            time.sleep(1.0)
        ok = [r for r in res if r.get("ok")]
        out["yahoo"][name] = dict(n=len(res), available=len(ok), with_adjclose=sum(r.get("adjclose", False) for r in ok),
                                  median_first=sorted(r["first"] for r in ok)[len(ok) // 2] if ok else None,
                                  detail=res)
    out["fred"] = {}
    for sid in ("DTB3", "DGS1MO"):
        try:
            status, b = get(f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={sid}", "etfport-lab research", 90)
            lines = b.decode().strip().splitlines()
            out["fred"][sid] = dict(status=status, rows=len(lines) - 1, first=lines[1].split(",")[0], last=lines[-1].split(",")[0])
        except Exception as e:  # noqa: BLE001
            out["fred"][sid] = dict(error=type(e).__name__)
    (HERE / "results.json").write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k != "yahoo"}, indent=1))
    for k, v in out["yahoo"].items():
        print(k, {kk: vv for kk, vv in v.items() if kk != "detail"})
    print(f"seconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    sys.exit(main())

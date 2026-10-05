"""Experiment 041: build the fund universe by the registered rule, before any return is fetched.
Registered design: experiments/041-larger-pilot.md.  Run: uv run python experiments/041/universe.py
Writes experiments/041/universe.json (tickers, series, classes, categories, families and the rule's intermediate counts).

Sources: SEC N-CEN data sets for filings made in 2024 (experiments/data_pilot/cache, fetched by the route 3 probe;
refetched from sec.gov if missing), the SEC mutual-fund ticker map (company_tickers_mf.json) and the 2025 SEC
risk/return summary data sets (experiment 003's route). Nothing here is a return.
"""
import datetime as dt
import importlib.util
import io
import json
import re
import shutil
import tomllib
import urllib.request
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"
NCEN = ROOT / "experiments" / "data_pilot" / "cache"
_s = importlib.util.spec_from_file_location("m003", ROOT / "experiments" / "003" / "run.py"); m003 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m003)

CATS = [  # (category, class, patterns); first match wins; "short" needs Bond or Income as well
    ("muni", "muni", [r"municipal", r"tax[- ]exempt", r"tax[- ]free"]),
    ("tips", "bond", [r"inflation", r"\btips\b"]),
    ("high_yield", "bond", [r"high[- ]yield", r"high income"]),
    ("short_bond", "bond", [r"short[- ]term", r"short duration", r"ultra short"]),
    ("core_plus", "bond", [r"core plus", r"total return bond", r"strategic income", r"flexible bond"]),
    ("core_bond", "bond", [r"\bbond", r"aggregate", r"treasury", r"government income"]),
    ("intl_equity", "intl_equity", [r"international", r"overseas", r"developed", r"emerging", r"global ex", r"ex[- ]us", r"world ex"]),
    ("small", "us_equity", [r"\bsmall"]),
    ("mid", "us_equity", [r"\bmid"]),
    ("large_growth", "us_equity", [r"growth"]),
    ("large_value", "us_equity", [r"value", r"dividend", r"equity income"]),
    ("large_blend", "us_equity", [r"\b500\b", r"total stock", r"total market", r"large cap", r"blue chip", r"\bequity\b", r"\bstock\b", r"\bindex\b"]),
]
NAMED_ETFS = ["AGG", "BND", "SHY", "IEF", "TLT", "LQD", "HYG", "TIP", "MUB"]


def category(name):
    n = name.lower()
    for cat, cls, pats in CATS:
        if any(re.search(p, n) for p in pats):
            if cat == "short_bond" and not re.search(r"bond|income", n):
                continue
            return cat, cls
    return None, None


def is_mf_ticker(t):
    return len(t) == 5 and t.endswith("X")        # Deviation 1: share-class-level split (NASDAQ mutual-fund symbols)


def ua():
    return tomllib.loads((ROOT / "ops" / "lab.toml").read_text())["sec_user_agent"]


def load_ncen():
    frames = []
    for q in range(1, 5):
        f = NCEN / f"2024q{q}_ncen.zip"
        if not f.exists():
            NCEN.mkdir(parents=True, exist_ok=True)
            req = urllib.request.Request(f"https://www.sec.gov/files/dera/data/form-n-cen-data-sets/2024q{q}_ncen.zip", headers={"User-Agent": ua()})
            f.write_bytes(urllib.request.urlopen(req, timeout=600).read())
        z = zipfile.ZipFile(f)
        fr = pd.read_csv(io.BytesIO(z.read("FUND_REPORTED_INFO.tsv")), sep="\t", dtype=str, usecols=[
            "FUND_ID", "ACCESSION_NUMBER", "FUND_NAME", "SERIES_ID", "IS_ETF", "IS_ETMF", "IS_INDEX", "IS_MULTI_INVERSE_INDEX", "IS_INTERVAL",
            "IS_FUND_OF_FUND", "IS_MASTER_FEEDER", "IS_MONEY_MARKET", "IS_TARGET_DATE", "MONTHLY_AVG_NET_ASSETS"])
        rg = pd.read_csv(io.BytesIO(z.read("REGISTRANT.tsv")), sep="\t", dtype=str, usecols=["ACCESSION_NUMBER", "REGISTRANT_NAME", "FAMILY_INVESTMENT_COMPANY_NAME"])
        sb = pd.read_csv(io.BytesIO(z.read("SUBMISSION.tsv")), sep="\t", dtype=str, usecols=["ACCESSION_NUMBER", "FILING_DATE"])
        frames.append(fr.merge(rg, on="ACCESSION_NUMBER", how="left").merge(sb, on="ACCESSION_NUMBER", how="left"))
    d = pd.concat(frames, ignore_index=True)
    d["filed"] = pd.to_datetime(d.FILING_DATE, errors="coerce", format="mixed")
    d = d[d.filed.dt.year == 2024].dropna(subset=["SERIES_ID"])
    d = d.sort_values("filed").groupby("SERIES_ID").tail(1)          # each series' latest 2024 filing
    d["assets"] = pd.to_numeric(d.MONTHLY_AVG_NET_ASSETS, errors="coerce").fillna(0.0)
    fam = d.FAMILY_INVESTMENT_COMPANY_NAME.fillna("").str.strip()
    d["family"] = np.where(fam != "", fam, d.REGISTRANT_NAME.fillna("").str.strip()).astype(str)
    d["family"] = d.family.str.upper()
    return d


def main():
    CACHE.mkdir(exist_ok=True)
    tmf = CACHE / "company_tickers_mf.json"
    if not tmf.exists():
        src = ROOT / "experiments" / "035" / "cache" / "company_tickers_mf.json"
        if src.exists():
            shutil.copy(src, tmf)
        else:
            tmf.write_bytes(urllib.request.urlopen(urllib.request.Request("https://www.sec.gov/files/company_tickers_mf.json", headers={"User-Agent": ua()}), timeout=120).read())
    mf = json.load(open(tmf)); fi = mf["fields"]
    tick = pd.DataFrame(mf["data"], columns=fi)
    by_series = tick.groupby("seriesId")
    d = load_ncen()
    counts = {"series_2024_filings": int(len(d))}
    Y = lambda c: d[c].fillna("N").str.upper().eq("Y")
    excl = Y("IS_MONEY_MARKET") | Y("IS_FUND_OF_FUND") | Y("IS_TARGET_DATE") | Y("IS_INTERVAL") | Y("IS_MASTER_FEEDER") | Y("IS_ETMF") | Y("IS_MULTI_INVERSE_INDEX")
    d = d[~excl & d.SERIES_ID.isin(tick.seriesId)].copy()
    counts["eligible_with_ticker"] = int(len(d))
    d[["cat", "cls"]] = d.FUND_NAME.fillna("").apply(lambda n: pd.Series(category(n)))
    d["tickers"] = d.SERIES_ID.map(lambda s: list(by_series.get_group(s).symbol))
    d["classes"] = d.SERIES_ID.map(lambda s: list(zip(by_series.get_group(s).symbol, by_series.get_group(s).classId)))
    d["has_mf"] = d.tickers.map(lambda ts: any(is_mf_ticker(t) for t in ts))
    d["has_etf_class"] = d.tickers.map(lambda ts: any(not is_mf_ticker(t) for t in ts))
    d["index"] = Y("IS_INDEX").reindex(d.index); d["etf"] = Y("IS_ETF").reindex(d.index)
    fams = d[d.has_mf].groupby("family").assets.sum().sort_values(ascending=False)
    top = list(fams.index[:15])
    counts["families_top15"] = {f: float(fams[f]) for f in top}
    dc = d.dropna(subset=["cat"])
    counts["categorized"] = int(len(dc))
    active = dc[(~dc["index"]) & dc.has_mf & dc.family.isin(top)].sort_values("assets", ascending=False).groupby(["family", "cat"]).head(1)
    idx = dc[dc["index"] & dc.has_mf].sort_values("assets", ascending=False).groupby("cat").head(3)
    etf = dc[dc["etf"] & dc.has_etf_class].sort_values("assets", ascending=False).groupby("cat").head(3)
    snap, _ = m003.snapshot(2025, {})
    expense = snap["expense"] if "expense" in snap.columns else pd.Series(dtype=float)
    def pick_mf(classes):
        c = [(t, cid) for t, cid in classes if is_mf_ticker(t)]
        c.sort(key=lambda tc: (np.inf if tc[1] not in expense.index or pd.isna(expense.get(tc[1])) else float(expense[tc[1]]), tc[1]))
        return c[0]
    def pick_etf(classes):
        c = sorted([(t, cid) for t, cid in classes if not is_mf_ticker(t)], key=lambda tc: tc[1]); return c[0]
    rows = []
    for grp, frame, picker in (("active", active, pick_mf), ("index_mf", idx, pick_mf), ("etf", etf, pick_etf)):
        for _, r in frame.iterrows():
            t, cid = picker(r.classes)
            rows.append(dict(group=grp, ticker=t, class_id=cid, series=r.SERIES_ID, name=r.FUND_NAME, family=r.family, cat=r["cat"], cls=r["cls"],
                             assets=float(r.assets), expense=None if cid not in expense.index or pd.isna(expense.get(cid)) else float(expense[cid])))
    have = {r["ticker"] for r in rows}
    sym = tick.set_index("symbol")
    for t in NAMED_ETFS + ["SPY"]:
        if t not in have:
            s = sym.loc[t] if t in sym.index else None
            name = d.loc[d.SERIES_ID == s.seriesId, "FUND_NAME"].iloc[0] if (s is not None and (d.SERIES_ID == s.seriesId).any()) else t
            cat, cls = category(name) if name != t else (("large_blend", "us_equity") if t == "SPY" else (None, None))
            role = {"MUB": ("muni_named", "muni"), "SPY": ("large_blend", "us_equity")}.get(t, ("bond_factor", "bond"))   # Deviation 2: class by factor role
            cid = None if s is None else s.classId
            rows.append(dict(group="etf", ticker=t, class_id=cid, series=None if s is None else s.seriesId, name=name,
                             family=None, cat=role[0], cls=role[1], assets=None, named=True,
                             expense=None if (cid is None or cid not in expense.index or pd.isna(expense.get(cid))) else float(expense[cid])))
    counts.update(active=int((pd.Series([r["group"] for r in rows]) == "active").sum()), index_mf=int((pd.Series([r["group"] for r in rows]) == "index_mf").sum()),
                  etf=int((pd.Series([r["group"] for r in rows]) == "etf").sum()))
    out = dict(built=dt.date.today().isoformat(), rule="experiments/041-larger-pilot.md (Design: Universe) with Deviation 1", counts=counts, funds=rows)
    json.dump(out, open(HERE / "universe.json", "w"), indent=1)
    print(json.dumps(counts, indent=1))
    for g in ("active", "index_mf", "etf"):
        print(g, sorted({(str(r["cls"]), str(r["cat"])) for r in rows if r["group"] == g}))


if __name__ == "__main__":
    main()

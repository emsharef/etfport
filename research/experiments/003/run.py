"""Experiment 003: point-in-time EDGAR prospectus fee-table values for experiment 001's cost cases.
See experiments/003-edgar-fee-inputs.md. Prints every table in Markdown.

Data: SEC Mutual Fund Prospectus Risk/Return Summary data sets (quarterly zips), fetched on demand from
sec.gov with the User-Agent in ops/lab.toml `sec_user_agent` (Q-03 answer), at most one request at a time
with a pause between requests (well under SEC's 10 requests per second). Cached under cache/, never
committed. The SHA-256 of every zip used is printed.
"""
from __future__ import annotations

import hashlib
import importlib.util
import io
import time
import tomllib
import urllib.request
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"
URL = "https://www.sec.gov/files/dera/data/mutual-fund-prospectus-risk/return-summary-data-sets/{q}_rr1.zip"
YEARS = [2013, 2017, 2021, 2025]
PRIMARY_YEAR = 2025
PAUSE = 0.5  # seconds between sec.gov requests

TAGS = {
    "front": ["MaximumSalesChargeImposedOnPurchasesOverOfferingPrice"],
    "deferred": ["MaximumDeferredSalesChargeOverOfferingPrice", "MaximumDeferredSalesChargeOverOther"],
    "redemption": ["RedemptionFeeOverRedemption"],
    "exchange": ["ExchangeFeeOverRedemption"],
    "expense": ["ExpensesOverAssets"],
    "account_usd": ["MaximumAccountFee"],
}
RATE_KINDS = ["front", "deferred", "redemption", "exchange", "expense"]
LABEL = {"front": "Maximum front-end sales charge (of offering price)",
         "deferred": "Maximum deferred sales charge (of offering price or other base)",
         "redemption": "Redemption fee (of amount redeemed)",
         "exchange": "Exchange fee (of amount redeemed)",
         "expense": "Total annual operating expenses (internal; NOT a switching cost)"}


def user_agent() -> str:
    return tomllib.loads((ROOT / "ops" / "lab.toml").read_text())["sec_user_agent"]


def fetch(q: str) -> tuple[Path, str]:
    CACHE.mkdir(exist_ok=True)
    f = CACHE / f"{q}_rr1.zip"
    if not f.exists():
        req = urllib.request.Request(URL.format(q=q), headers={"User-Agent": user_agent()})
        f.write_bytes(urllib.request.urlopen(req, timeout=300).read())
        time.sleep(PAUSE)
    return f, hashlib.sha256(f.read_bytes()).hexdigest()


def load_quarter(path: Path) -> pd.DataFrame:
    want = {t for ts in TAGS.values() for t in ts}
    with zipfile.ZipFile(path) as z:
        sub = pd.read_csv(io.BytesIO(z.read("sub.tsv")), sep="\t", dtype=str,
                          usecols=["adsh", "form", "filed", "accepted"])
        num = pd.read_csv(io.BytesIO(z.read("num.tsv")), sep="\t", dtype=str, quoting=3,
                          usecols=["adsh", "tag", "uom", "class", "otherdims", "value"])
    num = num[num.tag.isin(want)].copy()
    cls = num["class"].fillna("")
    fromdims = num["otherdims"].fillna("").str.extract(r"Class=(C\d+)")[0].fillna("")
    num["cid"] = cls.where(cls != "", fromdims)
    num = num[num.cid != ""]
    num["value"] = pd.to_numeric(num.value, errors="coerce")
    return num.merge(sub, on="adsh", how="left")


def snapshot(year: int, hashes: dict) -> tuple[pd.DataFrame, dict]:
    frames = []
    for qn in range(1, 5):
        q = f"{year}q{qn}"
        path, sha = fetch(q)
        hashes[q] = sha
        frames.append(load_quarter(path))
    d = pd.concat(frames, ignore_index=True)
    d = d[d.filed.str[:4] == str(year)]
    kind_of = {t: k for k, ts in TAGS.items() for t in ts}
    d["kind"] = d.tag.map(kind_of)
    audit = {"facts": len(d), "nan": int(d.value.isna().sum())}
    d = d[d.value.notna()]
    # Deviation 1: the two "...OverRedemption" tags are filed with a negative sign (a deduction from
    # redemption proceeds); take the magnitude before the range check.
    neg = d.kind.isin(["redemption", "exchange"]) & (d.value < 0)
    audit["sign_normalized"] = int(neg.sum())
    d.loc[neg, "value"] = -d.loc[neg, "value"]
    rate = d.kind.isin(RATE_KINDS)
    bad = rate & ((d.value < 0) | (d.value >= 1))
    audit["excluded_out_of_range"] = int(bad.sum())
    d = d[~bad]
    d = d.sort_values(["filed", "accepted", "adsh"])
    # Per class and kind: the latest filing in the year that reports that kind; within it, the maximum.
    last = d.groupby(["cid", "kind"]).adsh.transform("last")
    d = d[d.adsh == last]
    out = d.groupby(["cid", "kind"]).value.max().unstack()
    audit["classes"] = len(out)
    return out, audit


def q(x: pd.Series, p: float) -> float:
    return float(np.quantile(x, p)) if len(x) else float("nan")


def bp(x: float) -> str:
    return "n/a" if np.isnan(x) else f"{1e4 * x:.0f}"


def exp001():
    spec = importlib.util.spec_from_file_location("exp001", ROOT / "experiments" / "001" / "run.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main() -> None:
    hashes, snaps = {}, {}
    for y in YEARS:
        snaps[y] = snapshot(y, hashes)

    print("### Inputs\n\n| Quarter | SHA-256 |\n|---|---|")
    for k, v in hashes.items():
        print(f"| {k} | {v} |")

    print("\n### Coverage and data-quality audit per snapshot year\n")
    print("| Year | Class-level facts | Non-numeric | Sign-normalized (redemption, exchange) | Excluded (rate < 0 or >= 1) | Classes | Classes with an expense ratio |")
    print("|---|---|---|---|---|---|---|")
    for y in YEARS:
        t, a = snaps[y]
        n_exp = int(t["expense"].notna().sum()) if "expense" in t else 0
        print(f"| {y} | {a['facts']} | {a['nan']} | {a['sign_normalized']} | {a['excluded_out_of_range']} | {a['classes']} | {n_exp} |")

    print("\n### Charges per share class (bp); denominator = classes with an expense ratio in that year\n")
    print("| Year | Charge | Classes reporting | Share > 0 | p10 of > 0 | Median of > 0 | p90 of > 0 | Max | Count > 1000 bp |")
    print("|---|---|---|---|---|---|---|---|---|")
    stats = {}
    for y in YEARS:
        t, _ = snaps[y]
        base = t[t["expense"].notna()] if "expense" in t else t.iloc[0:0]
        for k in RATE_KINDS:
            col = base[k].dropna() if k in base else pd.Series(dtype=float)
            pos = col[col > 0]
            share = len(pos) / len(base) if len(base) else float("nan")
            stats[(y, k)] = pos
            print(f"| {y} | {LABEL[k]} | {len(col)} | {share:.3f} | {bp(q(pos, .1))} | {bp(q(pos, .5))} | "
                  f"{bp(q(pos, .9))} | {bp(pos.max() if len(pos) else float('nan'))} | {int((pos > 0.10).sum())} |")
        acc = base["account_usd"].dropna() if "account_usd" in base else pd.Series(dtype=float)
        accp = acc[acc > 0]
        print(f"| {y} | Maximum account fee (USD per year, not a rate) | {len(acc)} | "
              f"{(len(accp) / len(base) if len(base) else float('nan')):.3f} | ${q(accp, .1):.0f} | "
              f"${q(accp, .5):.0f} | ${q(accp, .9):.0f} | ${(accp.max() if len(accp) else float('nan')):.0f} | n/a |")

    # Replacement of experiment 001's assumed rates, primary year.
    m = exp001()
    raw, sha = m.fetch()
    mm, _ = m.monthly(raw)
    st = m.stats(m.quarterly(mm))
    refs = list(m.ALPHA_REFS) + [(f"0.1 x {c} ({m.PRIMARY})", m.DELTA_LOADING * st[m.PRIMARY][c][1])
                                  for c in ["SMB", "HML"]]
    kE = 1  # bp, experiment 001's liquid ETF half-spread, still assumed
    rows = []
    for name, kind, side, assumed in (("LOAD-max", "front", "buy", 575), ("CDSC-1y", "deferred", "sell", 100),
                                      ("REDFEE", "redemption", "sell", 200)):
        pos = stats[(PRIMARY_YEAR, kind)]
        for qn, qq in (("median", .5), ("p90", .9)):
            rate = q(pos, qq)
            rows.append((f"{name} ({qn} of > 0, {PRIMARY_YEAR})", kind, side, 1e4 * rate, assumed))
    print(f"\n### Experiment 001's asymmetric cases with EDGAR {PRIMARY_YEAR} rates (active-fund side observed; "
          "ETF 1 bp half-spread still assumed)\n")
    print(f"French input: {m.PINNED} (SHA-256 {sha})\n")
    print("| Case | Active rate (bp, observed) | 001 assumed (bp) | Switch | M1 break-even entry (bp) | "
          + " | ".join(r for r, _ in refs) + " | Class (001 convention) |")
    print("|---|---|---|---|---|" + "---|" * len(refs) + "---|")
    for name, kind, side, rate_bp, assumed in rows:
        entry = {"in": kE + (rate_bp if side == "buy" else 0), "out": (rate_bp if side == "sell" else 0) + kE}
        for sw in ("in", "out"):
            be = entry[sw]
            rs = [be * 1e-4 / g for _, g in refs]
            cls = m.classify(min(rs)), m.classify(max(rs))
            c = cls[0] if cls[0] == cls[1] else f"{cls[0]} to {cls[1]}"
            print(f"| {name} | {rate_bp:.0f} | {assumed} | {sw} | {be:.0f} | " + " | ".join(m.sig3(r) for r in rs)
                  + f" | {c} |")

    print(f"\n### Front load as an M2-style purchase rate (charged on holdings delivered): kappa+ = L / (1 - L), "
          f"{PRIMARY_YEAR}\n")
    pos = stats[(PRIMARY_YEAR, "front")]
    print("| Quantile of > 0 | L (bp of offering price) | L/(1-L) (bp of holdings delivered) |\n|---|---|---|")
    for qn, qq in (("p10", .1), ("median", .5), ("p90", .9)):
        L = q(pos, qq)
        print(f"| {qn} | {1e4 * L:.0f} | {1e4 * L / (1 - L):.0f} |")


if __name__ == "__main__":
    main()

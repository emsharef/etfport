"""Red's independent reproduction of experiment 003, written from its Design without reading run.py.

Usage: uv run python experiments/003/red_reproduce.py [data_dir]
data_dir holds the 16 quarterly <yyyy>q<n>_rr1.zip files (default: experiments/003/cache/). They are
fetched from sec.gov with ops/lab.toml's sec_user_agent and never committed. Each file's SHA-256 is
checked against the value reported in the experiment's Results.
"""
import hashlib
import io
import sys
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd

SHA = {
    "2013q1": "54bc23f043001c034d45bead0aea439957a22d51ca6592fc29fabf45e50ed56e",
    "2013q2": "1be2f1610ae67cd2a7bc69685acd5ced0062fa233d052ed6ddf8471382727ac3",
    "2013q3": "a2342fa76dee86184adacf2fc01741185cfb86c31fddd181b97036449f13ab71",
    "2013q4": "26177e37dc09db5624ecad944c923bfab88eaa0278c549c1283d89a8c0769bc0",
    "2017q1": "426ef54468144cc371f3da8c6177c8cbe010c195d3d0dd705b66b8b98975bc82",
    "2017q2": "51d37411b19f54d6948271648a9850797c14a8caa1ba548c515fafb1aa1a30d0",
    "2017q3": "8d07e5d922f8f1b84f76c3d403ad8b11558165837e7cf0acfb157e338c212fb9",
    "2017q4": "e6782de0b973d866a482b965898ba64918b25a572173a1faff53210851bb3715",
    "2021q1": "738be61be7efa93338191c2f4ba08f6a605c42db16b9585317da06d1e3ceb3bb",
    "2021q2": "09ff881c72d1ea4f03fb9efd38b69dbc37dc3ac88ac029ab6056230bfe39dec3",
    "2021q3": "ff42c246ee4e2eaac655f5db7ebcf5cdb0b313a8988a99c6065e0567407a1f79",
    "2021q4": "c49c328a80b0456527e4fb114a0fde6c354b744b2334bdb44fd668b720b36b05",
    "2025q1": "e6e82498357800dfe93ec4464c6e9ce1cb004ec0516eefb583115ad57d10f38c",
    "2025q2": "e90ec89d493f038317adb3c7b2b114a9408c1a111414000638c45cbd3e34ea5b",
    "2025q3": "a2f84ebc97fc497361b4cef634d8c5a5a8d044901714dfc6461f8b50e2816d6f",
    "2025q4": "c7e397bd8f13545b8e756ac41e82d1fe7d8fc0d10316ba99242da1eefbec2f71",
}
KIND = {
    "MaximumSalesChargeImposedOnPurchasesOverOfferingPrice": "front",
    "MaximumDeferredSalesChargeOverOfferingPrice": "deferred",
    "MaximumDeferredSalesChargeOverOther": "deferred",
    "RedemptionFeeOverRedemption": "redemption",
    "ExchangeFeeOverRedemption": "exchange",
    "ExpensesOverAssets": "expense",
    "MaximumAccountFee": "account",
}
SIGN_FIX = {"redemption", "exchange"}          # Deviation 1
RATE = {"front", "deferred", "redemption", "exchange", "expense"}

data = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent / "cache"


def load_year(y):
    frames = []
    for q in range(1, 5):
        key = f"{y}q{q}"
        raw = (data / f"{key}_rr1.zip").read_bytes()
        assert hashlib.sha256(raw).hexdigest() == SHA[key], key
        z = zipfile.ZipFile(io.BytesIO(raw))
        sub = pd.read_csv(z.open("sub.tsv"), sep="\t", dtype=str, usecols=["adsh", "filed", "accepted"],
                          quoting=3)
        num = pd.read_csv(z.open("num.tsv"), sep="\t", dtype=str, quoting=3, keep_default_na=False,
                          usecols=["adsh", "tag", "class", "otherdims", "value"])
        num = num[num["tag"].isin(KIND)]
        cls = num["class"].where(num["class"] != "", None)
        from_dims = num["otherdims"].str.extract(r"Class=(C\d+)")[0]
        num = num.assign(cid=cls.fillna(from_dims))
        frames.append(num.merge(sub, on="adsh", how="inner"))
    df = pd.concat(frames, ignore_index=True)
    df = df[df["filed"].str[:4] == str(y)]
    # Facts repeated across quarterly sets are kept: they change only the audit counts, never a
    # statistic, because values are taken as the maximum within the latest filing.
    return df[df["cid"].notna()]


rows, audit, snap = [], [], {}
for y in (2013, 2017, 2021, 2025):
    df = load_year(y)
    n_facts = len(df)
    df = df.assign(kind=df["tag"].map(KIND), v=pd.to_numeric(df["value"], errors="coerce"))
    n_nonnum = int(df["v"].isna().sum())
    df = df[df["v"].notna()]
    neg = df["kind"].isin(SIGN_FIX) & (df["v"] < 0)
    n_sign = int(neg.sum())
    df.loc[neg, "v"] = -df.loc[neg, "v"]
    bad = df["kind"].isin(RATE) & ((df["v"] < 0) | (df["v"] >= 1))
    n_bad = int(bad.sum())
    df = df[~bad]
    # latest filing (filed, then accepted) per class and kind; maximum within that filing
    df = df.sort_values(["filed", "accepted"])
    last = df.groupby(["cid", "kind"])[["filed", "accepted"]].transform("last")
    df = df[(df["filed"] == last["filed"]) & (df["accepted"] == last["accepted"])]
    val = df.groupby(["cid", "kind"])["v"].max().unstack()
    denom = val["expense"].notna().sum()
    audit.append((y, n_facts, n_nonnum, n_sign, n_bad, len(val), denom))
    snap[y] = val
    er = val["expense"].notna()      # the Design's denominator; charge statistics use the same classes
    for kind in ("front", "deferred", "redemption", "exchange", "expense", "account"):
        s = val.loc[er, kind].dropna()
        pos = s[s > 0]
        scale = 1 if kind == "account" else 10_000
        qs = np.percentile(pos, [10, 50, 90]) * scale
        rows.append((y, kind, len(s), round(len(pos) / denom, 3),
                     *[round(float(x), 1) for x in qs], round(float(pos.max()) * scale, 1),
                     int((pos * 10_000 > 1000).sum()) if kind != "account" else "n/a"))

print("| Year | facts | non-numeric | sign-normalized | excluded | classes | with expense ratio |")
for a in audit:
    print("| " + " | ".join(str(x) for x in a) + " |")
print("\n| Year | Charge | reporting | share>0 | p10 | median | p90 | max | >1000bp |")
for r in rows:
    print("| " + " | ".join(str(x) for x in r) + " |")

# 2025 replacement rows: M1 entry cost with the 1 bp ETF leg, ratios against 001's primary references.
refs = {"a0.5": 12.5, "a1": 25.0, "a2": 50.0, "SMB": 4.39, "HML": 8.97}   # red's 001 reproduction (bp/q)
print("\n2025 replacement (entry bp; ratios vs a0.5, a1, a2, 0.1xSMB, 0.1xHML):")
v25 = snap[2025][snap[2025]["expense"].notna()]
for case, kind, side in (("LOAD-max", "front", "in"), ("CDSC-1y", "deferred", "out"), ("REDFEE", "redemption", "out")):
    pos = v25[kind].dropna()
    pos = pos[pos > 0] * 10_000
    for lab, rate in (("median", np.percentile(pos, 50)), ("p90", np.percentile(pos, 90))):
        entry = rate + 1
        print(case, lab, round(float(rate), 1), side, "entry", round(float(entry), 1),
              [f"{entry / refs[k]:.3g}" for k in refs])
front = v25["front"].dropna()
front = front[front > 0]
print("\nfront load L/(1-L) at p10, median, p90 (bp):",
      [round(float(L / (1 - L)) * 10_000) for L in np.percentile(front, [10, 50, 90])])

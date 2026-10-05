"""Addendum to experiment 003: sign audit of the two "...OverRedemption" tags in the cached zips.
Counts negative, zero and positive filed values per snapshot year (filings made in that year), before any
cleaning. Uses the same cache and loader as run.py; downloads nothing new if the cache is present.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("exp003", HERE / "run.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

print("| Year | Tag | Negative | Zero | Positive |\n|---|---|---|---|---|")
for y in m.YEARS:
    frames = [m.load_quarter(m.fetch(f"{y}q{q}")[0]) for q in range(1, 5)]
    d = __import__("pandas").concat(frames, ignore_index=True)
    d = d[(d.filed.str[:4] == str(y)) & d.value.notna()]
    for tag in ("RedemptionFeeOverRedemption", "ExchangeFeeOverRedemption"):
        v = d[d.tag == tag].value
        print(f"| {y} | {tag} | {int((v < 0).sum())} | {int((v == 0).sum())} | {int((v > 0).sum())} |")

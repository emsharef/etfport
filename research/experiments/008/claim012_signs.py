"""Experiment 008, Deviation 2 (reporting only, not preregistered): claim 012's sign pattern at every point.
Reads experiments/008/results.json (no new solves) and applies the registered resolution rule to
Delta_E - Delta_N > 0 and Delta_F - Delta_E < 0 at each fixture, schedule and cash level.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run import FLOOR_BP, MULT  # noqa: E402

res = json.loads((HERE / "results.json").read_text())["results"]
print("| Fixture | Schedule | cash c | Delta_E-Delta_N (unc.) | Delta_F-Delta_E (unc.) | claim 012 pattern |")
print("|---|---|---|---|---|---|")
tot = held = 0
for fx, r in res.items():
    for key, pt in r["points"].items():
        sch, c = key.split(",")
        d = pt["derived"]
        tot += 1
        if d is None:
            print(f"| {fx} | {sch} | {c} | unresolved | unresolved | unresolved |")
            continue
        e_ok = d["ETF"] > max(FLOOR_BP, MULT * d["uETF"])
        a_ok = -d["ACT"] > max(FLOOR_BP, MULT * d["uACT"])
        held += e_ok and a_ok
        print(f"| {fx} | {sch} | {c} | {d['ETF']:+.4f} ({d['uETF']:.1e}) | {d['ACT']:+.4f} ({d['uACT']:.1e}) | "
              f"{'holds (resolved)' if e_ok and a_ok else 'does not hold or unresolved'} |")
print(f"\nPoints where the pattern holds beyond the predeclared thresholds: {held} of {tot}")

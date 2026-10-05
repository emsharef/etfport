"""Experiment 006, Deviation 2 (reporting only): true medians for Part K.
run.py's "Median G*" columns print sorted[n // 2], the upper of the two middle elements for the even
cell counts here (60 per family, 12 per alpha row). This recomputes Part K exactly (same instances, same
exact solver) and prints the true median (mean of the two middle elements) beside the upper median.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run as r  # noqa: E402


def med(xs):
    s = sorted(xs)
    n = len(s)
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2


rows = r.part_k()
print("| Geometry | Costs | Median G* (bp) | Upper median as printed (bp) |\n|---|---|---|---|")
for geom, cost in product(r.GEOMETRY, r.COSTS):
    g = sorted(x[6] for x in rows if x[0] == geom and x[1] == cost)
    print(f"| {geom} | {cost} | {r.bp(med(g))} | {r.bp(g[len(g) // 2])} |")
print("\n| Geometry | alpha (bp/q) | Z | EQ5 | ETFC5 | ETF-stress |\n|---|---|---|---|---|---|")
for geom, alpha in product(r.GEOMETRY, r.ALPHA):
    cells = [r.bp(med([x[6] for x in rows if x[0] == geom and x[1] == c and x[2] == alpha]))
             for c in ["Z", "EQ5", "ETFC5", "ETF-stress"]]
    print(f"| {geom} | {float(alpha) * 1e4:.0f} | " + " | ".join(cells) + " |")

"""Experiment 006, Deviation 1 (reporting only): exact quantities the registered H_K needs but run.py's
tables do not print. Recomputes, with the same instances and the exact solver:
(1) max G* over the G1-exact, Z, alpha = 0 cells (H_K's second clause);
(2) for ETF-stress, whether any optimum (F or E) holds E2, which would explain identical G* across menus.
"""
from __future__ import annotations

import sys
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run as r  # noqa: E402

g1 = []
for gamma, sA, start in product(r.GAMMA, r.SA, r.STARTS):
    I = r.instance("G1-exact", "Z", r.Fr(0), gamma, sA, start)
    g1.append(r.solve(I, "F")[0] - r.solve(I, "E")[0])
print(f"(1) G1-exact, Z, alpha = 0: {len(g1)} cells; max G* = {float(max(g1)) * 1e4:.4f} bp; "
      f"cells >= 1 bp: {sum(x >= r.NONTRIVIAL for x in g1)}")

held, gaps = 0, {}
for geom, alpha, gamma, sA, start in product(r.GEOMETRY, r.ALPHA, r.GAMMA, r.SA, r.STARTS):
    I = r.instance(geom, "ETF-stress", alpha, gamma, sA, start)
    VF, wF, _ = r.solve(I, "F")
    VE, wE, _ = r.solve(I, "E")
    if I.n == 2 and (wF[2] != 0 or wE[2] != 0):
        held += 1
    gaps.setdefault((alpha, gamma, sA, start), set()).add(VF - VE)
print(f"(2) ETF-stress: cells where an optimum holds E2: {held}; "
      f"parameter points whose exact G* differs across the three menus: {sum(len(s) > 1 for s in gaps.values())}")

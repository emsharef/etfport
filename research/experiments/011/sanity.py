"""Experiment 011, Deviation 1 (post hoc, reporting only): does the registered gate certify at all?
Deterministic best case: the estimate equals the truth (zero sampling error), zero costs, and the exact
critical value t_{N,1/20} for N in {40, 80, 160}; t is also held at its N = 160 value for longer
hypothetical N (the chi-square-like limit). For each true gap, report the vertex lower bound ell. The gate
certifies iff ell > 0 (and C_N is nonempty, which holds when theta_hat = theta_* is in the domain).
"""
from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run as r  # noqa: E402

r.set_costs("zero")
eta = F(1, 20)
t160 = r.quantile_T(160, eta)
Ns = {40: r.quantile_T(40, eta), 80: r.quantile_T(80, eta), 160: t160, 640: t160, 2560: t160, 10240: t160}
print("| G_* (bp/q) | alpha_* | " + " | ".join(f"ell at N={N} ({N // 4} y), bp" for N in Ns) + " |")
print("|---|---|" + "---|" * len(Ns))
for g in (10, 25, 50, 100):
    a = r.alpha_for_gap(F(g, 10000))
    if a >= r.BOX[2][1]:
        continue
    th = r.LAM_STAR + (a,)
    w = r.opt(th, "F")
    cells = []
    for N, t in Ns.items():
        rad = [r.ub_sqrt(t * r.OM[i][i] / N) for i in range(3)]
        box = [(max(r.BOX[i][0], th[i] - rad[i]), min(r.BOX[i][1], th[i] + rad[i])) for i in range(3)]
        ell = min(r.Q(w, v) - r.supE(v) for v in product(*box))
        cells.append(f"{float(ell) * 1e4:+.1f}")
    print(f"| {g} | {float(a):.5f} | " + " | ".join(cells) + " |")

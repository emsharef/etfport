"""Experiment 007, Deviation 1 (reporting only, after red's review): H2 attribution counterfactuals.
Re-solves exactly the 168 registered H2 pairs (d = 1, adjacent c, fixed menu, a-, cost) with only the ETF
rates changed: (a) ETF sale rate 0; (b) ETFs costless in both directions. Counts H2 violations and whether
|active trade| changes. Uses run.py's instances and the experiment 004 exact solver.
"""
from __future__ import annotations

import sys
from dataclasses import replace
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run as r  # noqa: E402


def abs_trade(I):
    return abs(r.solve(I, "F")[1][0] - I.w0[0])


for label, mod in (("ETF sale rate 0", lambda I: replace(I, ksell=(I.ksell[0],) + (Fr(0),) * I.n)),
                   ("ETFs costless", lambda I: replace(I, kbuy=(I.kbuy[0],) + (Fr(0),) * I.n,
                                                       ksell=(I.ksell[0],) + (Fr(0),) * I.n))):
    viol = changed = pairs = 0
    for n, a0, (cost, _, _) in product(r.MENUS, r.A0S, r.COSTS):
        for c1, c2 in zip(r.CS, r.CS[1:]):
            pairs += 1
            I1, I2 = (mod(r.instance(n, a0, c, Fr(1), cost)) for c in (c1, c2))
            t1, t2 = abs_trade(I1), abs_trade(I2)
            viol += t2 > t1
            changed += t1 != t2
    print(f"{label}: {pairs} pairs, H2 violations {viol}, pairs where |trade| changes with c {changed}")

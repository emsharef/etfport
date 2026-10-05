"""Experiment 015 (D6 preparation): where does claim 012's continuation sign pattern hold in M3?
Registered design: experiments/015-m3-continuation-sign-search.md.
Reuses, with attribution, red's reviewed machinery: `make`, `bayes`, `returns` from
checks/red-m3-definition/check.py (M3 fixture builder and exact Bayes bookkeeping), and `solve`, `bracket`,
`SOL` from experiments/008/red_reproduce.py (the joint convex program per (root, continuation) cell, and a
certified Frank-Wolfe bracket on each cell's optimal certainty equivalent at a funded projection).
A contribution's sign is called only when its interval, from bracket interval arithmetic, excludes zero.
"""
from __future__ import annotations

import importlib.util
import itertools
import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "checks" / "red-m3-definition"))
from check import bayes, make, returns  # noqa: E402

_spec = importlib.util.spec_from_file_location("red008", ROOT / "experiments" / "008" / "red_reproduce.py")
red008 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(red008)

MENUS = {
    "1 ETF (1,0)": ((F(1), F(0)),),
    "2 ETFs, second spans factor 2 (0,1)": ((F(1), F(0)), (F(0), F(1))),
    "2 ETFs, second (1,1/2)": ((F(1), F(0)), (F(1), F(1, 2))),
}
COSTS = {  # (active buy, active sell, ETF buy, ETF sell); all assumed
    "zero": (F(0), F(0), F(0), F(0)),
    "INST_A-like": (F(1, 2000), F(0), F(1, 2000), F(1, 2000)),
    "ETF-costlier": (F(0), F(0), F(1, 200), F(1, 200)),
    "active-costlier (hypothetical)": (F(1, 200), F(1, 200), F(1, 2000), F(1, 2000)),
}
RHOS = [F(5), F(10), F(20)]
TILTS = {"tilt 31/50 (INST_A)": F(31, 50), "no factor-2 tilt": F(0)}
CELLS = [(D, R) for D in "FE" for R in "FEN"]


def instance(menu, cost, rho, tilt):
    BE = MENUS[menu]
    n = len(BE)
    ab, as_, eb, es = COSTS[cost]
    x0 = (F(43, 100), F(1767, 10000)) + (F(0),) * (n - 1)
    return make(BA=(F(23, 25), tilt), BE=BE, cE=(F(3, 10000),) + (F(0),) * (n - 1),
                lam1=(F(1, 100), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 50)),
                sizes=(F(9, 100), F(2, 25), F(3, 200)) + (F(1, 100),) * n,
                kb=(ab,) + (eb,) * n, ks=(as_,) + (es,) * n, x0=x0, rho=rho)


def checks(I):
    Y, P0, post = bayes(I)
    pos = all(1 + r > 0 for t in I["Theta"] for s in I["shocks"] for r in returns(I, t, s)[1])
    nondeg = all(len({returns(I, t, s)[1][i] for s in I["shocks"]}) > 1 for t in I["Theta"] for i in range(len(I["x0"])))
    amb = [y for y in Y if P0[y] > 0 and sum(v > 0 for v in post[y].values()) > 1]
    return dict(positive=pos, nondegenerate=nondeg, observations=sum(P0[y] > 0 for y in Y),
                ambiguous=len(amb), prob_ambiguous=float(sum(P0[y] for y in amb)))


def interval(br, plus, minus):
    lo = sum(br[c][0] for c in plus) - sum(br[c][1] for c in minus)
    hi = sum(br[c][1] for c in plus) - sum(br[c][0] for c in minus)
    return lo, hi


def sign(iv):
    return "+" if iv[0] > 0 else "-" if iv[1] < 0 else "?"


def main():
    t0 = time.time()
    rows = []
    for menu, cost, rho, tilt in itertools.product(MENUS, COSTS, RHOS, TILTS):
        I = instance(menu, cost, rho, TILTS[tilt])
        B = bayes(I)
        ck = checks(I)
        br, pt, u0A = {}, {}, {}
        for D, R in CELLS:
            V, u0 = red008.solve(I, B, D, R)
            if V is None:
                V, u0 = red008.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
            if V is None:
                continue
            pt[D, R] = float(red008.ce(V, I["rho"]))
            u0A[D, R] = float(u0[0])
            b = red008.bracket(I, B, D, R, u0, red008.SOL[0])
            if b is not None:
                br[D, R] = (float(b[0]), float(b[1]))
        row = dict(menu=menu, costs=cost, rho=str(rho), tilt=tilt, checks=ck,
                   brackets={f"{D}{R}": br.get((D, R)) for D, R in CELLS},
                   root_active_trade={f"{D}{R}": u0A.get((D, R)) for D, R in CELLS})
        if len(br) == 6:
            etf = interval(br, [("F", "E"), ("E", "N")], [("E", "E"), ("F", "N")])
            act = interval(br, [("F", "F"), ("E", "E")], [("E", "F"), ("F", "E")])
            row.update(etf=etf, act=act, etf_sign=sign(etf), act_sign=sign(act),
                       etf_point=pt["F", "E"] - pt["E", "E"] - pt["F", "N"] + pt["E", "N"],
                       act_point=pt["F", "F"] - pt["E", "F"] - pt["F", "E"] + pt["E", "E"])
        else:
            row.update(etf=None, act=None, etf_sign="?", act_sign="?")
        rows.append(row)
    (HERE / "results.json").write_text(json.dumps(rows, indent=1, default=str))
    print("| menu | costs | rho | tilt | ambiguous obs (prob) | Delta_E - Delta_N (bp) [certified interval] | "
          "Delta_F - Delta_E (bp) [interval] | pattern |\n|---|---|---|---|---|---|---|---|")
    for r in rows:
        ck = r["checks"]
        if r["etf"] is None:
            print(f"| {r['menu']} | {r['costs']} | {r['rho']} | {r['tilt']} | {ck['ambiguous']} ({ck['prob_ambiguous']:.3f}) | "
                  f"unresolved (bracket missing) | unresolved | ? |")
            continue
        pat = ("claim-012 pattern" if (r["etf_sign"], r["act_sign"]) == ("+", "-") else
               "unresolved" if "?" in (r["etf_sign"], r["act_sign"]) else f"FLIP ({r['etf_sign']}, {r['act_sign']})")
        print(f"| {r['menu']} | {r['costs']} | {r['rho']} | {r['tilt']} | {ck['ambiguous']} ({ck['prob_ambiguous']:.3f}) | "
              f"{r['etf_point']:+.4f} [{r['etf'][0]:+.4f}, {r['etf'][1]:+.4f}] | "
              f"{r['act_point']:+.4f} [{r['act'][0]:+.4f}, {r['act'][1]:+.4f}] | {pat} |")
    print("\n### Counts by feature\n")
    for feat in ("menu", "costs", "rho", "tilt"):
        vals = sorted({r[feat] for r in rows})
        print(f"**{feat}**")
        for v in vals:
            rs = [r for r in rows if r[feat] == v]
            c = lambda a, b: sum(1 for r in rs if (r["etf_sign"], r["act_sign"]) == (a, b))  # noqa: E731
            unres = sum(1 for r in rs if "?" in (r["etf_sign"], r["act_sign"]))
            print(f"- {v}: pattern (+,-) {c('+', '-')}; (+,+) {c('+', '+')}; (-,-) {c('-', '-')}; (-,+) {c('-', '+')}; "
                  f"unresolved {unres}; of {len(rs)}")
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

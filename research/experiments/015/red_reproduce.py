"""Red's reproduction of experiment 015, written from the registered Design without reading run.py or
reclassify.py.

Instances are built with `make` (checks/red-m3-definition/check.py) from the Design's description. Each of
the six (D, R) cells is solved with red's experiment 008 engine: CLARABEL with an SCS fallback, and a
certified Frank-Wolfe bracket (`bracket`). Contributions are interval sums, and signs are called with the
Design's rule after Deviation 1's widening, tau = 3.03e-3 bp. As a second-solver check, the point
contributions of every instance are re-solved with SCS and their signs compared.

Usage: uv run python experiments/015/red_reproduce.py
"""
import itertools
import re
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "008"))
import red_reproduce as R8  # noqa: E402  (red's experiment 008 engine)
from check import bayes, make  # noqa: E402  (red's M3 fixture builder)

MENUS = {"1 ETF (1,0)": ((F(1), F(0)),),
         "2 ETFs, second spans factor 2 (0,1)": ((F(1), F(0)), (F(0), F(1))),
         "2 ETFs (1,1/2)": ((F(1), F(0)), (F(1), F(1, 2)))}
BP = F(1, 10000)
COSTS = {"zero": (0, 0, 0, 0), "INST_A-like": (5, 0, 5, 5), "ETF-costlier": (0, 0, 50, 50),
         "active-costlier (hypothetical)": (50, 50, 5, 5)}
TILTS = {"tilt 31/50 (INST_A)": F(31, 50), "no factor-2 tilt": F(0)}
TAU = 3.03e-3
CELLS = [(D, R) for D in "FE" for R in "FEN"]


def instance(menu, cost, rho, tilt):
    BE = MENUS[menu]
    n = len(BE)
    ab, as_, eb, es = (c * BP for c in COSTS[cost])
    return make(BA=(F(23, 25), TILTS[tilt]), BE=BE, cE=(F(3, 10000),) + (F(0),) * (n - 1),
                lam1=(F(1, 100), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 50)),
                sizes=(F(9, 100), F(2, 25), F(3, 200)) + (F(1, 100),) * n,
                kb=(ab,) + (eb,) * n, ks=(as_,) + (es,) * n,
                x0=(F(43, 100), F(1767, 10000)) + (F(0),) * (n - 1), rho=F(rho))


def classify(ivs):
    (el, eh), (al, ah) = ivs
    se = "+" if el > 0 else "-" if eh < 0 else "?"
    sa = "+" if al > 0 else "-" if ah < 0 else "?"
    if "?" in se + sa:
        return "unresolved"
    return "claim-012 pattern" if (se, sa) == ("+", "-") else f"FLIP ({se}, {sa})"


def main():
    rep = {}
    for line in open(HERE.parent / "015-m3-continuation-sign-search.md"):
        c = [x.strip() for x in line.split("|")]
        if len(c) == 10 and c[1] in MENUS and c[3].isdigit():
            m = [re.match(r"\s*([+-]?[\d.]+(?:e[+-]?\d+)?)", c[k]) for k in (6, 7)]
            if all(m):
                rep[(c[1], c[2], int(c[3]), c[4])] = ([float(x.group(1)) for x in m], c[8])
    fails, rows, counts = [], [], {}
    worst_pt, scs_disagree, scs_done = 0.0, 0, 0
    for menu, cost, rho, tilt in itertools.product(MENUS, COSTS, (5, 10, 20), TILTS):
        I = instance(menu, cost, rho, tilt)
        B = bayes(I)
        br, pt, u0A = {}, {}, {}
        for D, R in CELLS:
            V, u0 = R8.solve(I, B, D, R)
            if V is None:
                V, u0 = R8.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
            b = R8.bracket(I, B, D, R, u0, R8.SOL[0]) if V is not None else None
            if b is None:
                br = None
                break
            lo, hi, _ = b
            br[D, R] = (min(lo, hi) - TAU, max(lo, hi) + TAU)
            pt[D, R] = R8.ce(V, I["rho"])
            u0A[D, R] = u0[0]
        if br is None:
            cls, ivs, pts = "unresolved", None, None
        else:
            etf = (br["F", "E"][0] - br["E", "E"][1] - br["F", "N"][1] + br["E", "N"][0],
                   br["F", "E"][1] - br["E", "E"][0] - br["F", "N"][0] + br["E", "N"][1])
            act = (br["F", "F"][0] - br["E", "F"][1] - br["F", "E"][1] + br["E", "E"][0],
                   br["F", "F"][1] - br["E", "F"][0] - br["F", "E"][0] + br["E", "E"][1])
            ivs = (etf, act)
            cls = classify(ivs)
            pts = (pt["F", "E"] - pt["E", "E"] - pt["F", "N"] + pt["E", "N"],
                   pt["F", "F"] - pt["E", "F"] - pt["F", "E"] + pt["E", "E"])
        key = (menu, cost, rho, tilt)
        counts[(rho, cls)] = counts.get((rho, cls), 0) + 1
        direction = "sells" if all(u0A[("F", R)] < -1e-6 for R in "FEN") else \
            "buys" if any(u0A[("F", R)] > 1e-6 for R in "FEN") else "no trade"
        rows.append((key, cls, pts, direction))
        if key in rep:
            rpts, rcls = rep[key]
            worst_pt = max(worst_pt, max(abs(a - b) for a, b in zip(pts, rpts)))
            if rcls != cls:
                fails.append(f"classification differs at {key}: red {cls}, reported {rcls}")
        # second solver: SCS point contributions, sign agreement where the certified call is resolved
        if cls != "unresolved":
            v = {c: R8.solve(I, B, *c, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)[0] for c in CELLS}
            if all(x is not None for x in v.values()):
                s = {c: R8.ce(x, I["rho"]) for c, x in v.items()}
                se = s["F", "E"] - s["E", "E"] - s["F", "N"] + s["E", "N"]
                sa = s["F", "F"] - s["E", "F"] - s["F", "E"] + s["E", "E"]
                scs_done += 1
                if (se > 0) != (pts[0] > 0) or (sa > 0) != (pts[1] > 0):
                    scs_disagree += 1
        print(f"{menu:36s} {cost:31s} rho={rho:>2} {tilt:20s} {cls:18s} "
              f"ETF {pts[0]:+.4f} ACT {pts[1]:+.4f} root-F {direction}", flush=True)
    print(f"\nclassification counts by rho: {dict(sorted(counts.items()))}")
    print(f"largest |red point - reported point| over {len(rep)} rows: {worst_pt:.2e} bp")
    print(f"SCS cross-check: {scs_done} resolved instances re-solved; sign disagreements {scs_disagree}")
    pat = [r for r in rows if r[1] == "claim-012 pattern"]
    flip = [r for r in rows if r[1].startswith("FLIP")]
    print(f"pattern instances: {len(pat)}, root-F sells in all: {all(r[3] == 'sells' for r in pat)}; "
          f"flips: {len(flip)}, ETF channel negative in all: {all(r[2][0] < 0 for r in flip)}, "
          f"root-F buys in all: {all(r[3] == 'buys' for r in flip)}")
    if scs_disagree:
        fails.append("SCS sign disagreement")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

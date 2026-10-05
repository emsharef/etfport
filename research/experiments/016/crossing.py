"""Experiment 016, Deviation 1 (b): search for a region crossing, Delta_N = 0 < Delta_E or Delta_E = 0 < Delta_N.
Registered before any stage-1 result was read (PM note 2026-09-28-exp016-adjustable-wealth).

With positive costs, {a0 : Delta_R = 0} is a no-active-trade band [L_R, U_R] (claim 011 part 4). An incumbent
below L_R buys up to L_R, and one above U_R sells down to U_R. So stage 1's root targets a0 + u*_{A,(F,R)}
locate the band edges: L_R is the median target over incumbents whose (F,R) root buys, U_R over those that
sell (optimizer outputs). A region crossing exists iff the two bands differ. For every instance group
(family, positive costs, tilt, rho) and every edge pair with |L_E - L_N| or |U_E - U_N| > 1e-4, five
incumbents evenly inside the gap are solved (same construction as stage 1: INST_A holds factor-1
exposure, claim 012's family holds a0 + e0 = 1/2).

Each point gets stage 1's four certified cells, plus, for R in {N, E}, a bracket of the F cell taken at the
E cell's optimizer (a feasible F point), whose Frank-Wolfe end bounds Delta_R from above:
    0 <= Delta_R <= FWbound_F(at E optimizer) - lo(E cell).
Classification, per R:
- Delta_R > 0 (certified): widened lo(F cell) - widened hi(E cell) > 0, with stage 1's tau;
- Delta_R = 0 to within eps = 1e-3 bp (certified upper bound, not an exact zero);
- otherwise unresolved.
A **region crossing** is one Delta certified > 0 and the other zero to within eps. For each, claim 022 part 3
is checked: Delta_N = 0 < Delta_E needs phi(A_E) > phi(B_N) (part 3a's contrapositive), and Delta_E = 0 <
Delta_N needs phi(A_N) < phi(B_E) (part 3b's), with phi from math's `solve_fixed` (floating).
Zero-cost groups are skipped: their band is a point.

Run: uv run python -W ignore experiments/016/crossing.py   (writes experiments/016/crossing.json)
"""
from __future__ import annotations

import importlib.util
import itertools
import json
import os
import statistics
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


r16 = _load("r16", HERE / "run.py")
math015 = _load("math015", ROOT / "checks" / "exp015-premia" / "check.py")
EPS = 1e-3


def edges(rs, R):
    buy = [float(F(r["a0"])) + r["cells"]["F" + R]["u0"][0] for r in rs if r["cells"]["F" + R] and r["cells"]["F" + R]["dirA"] == "buy"]
    sell = [float(F(r["a0"])) + r["cells"]["F" + R]["u0"][0] for r in rs if r["cells"]["F" + R] and r["cells"]["F" + R]["dirA"] == "sell"]
    return (statistics.median(buy) if buy else None, statistics.median(sell) if sell else None)


def points(rows):
    out = []
    groups = {}
    for r in rows:
        if r["family"] == "claim 012 own incumbent" or r["cost"] == "zero":
            continue
        groups.setdefault((r["family"], r["cost"], r["tilt"], r["rho"]), []).append(r)
    for (fam, cost, tilt, rho), rs in groups.items():
        LN, UN = edges(rs, "N"); LE, UE = edges(rs, "E")
        amax = F(1, 2) if fam == "claim 012" else r16.EXPO1 / F(23, 25)   # keep the incumbent ETF >= 0
        for x, y, side in ((LN, LE, "lower"), (UN, UE, "upper")):
            if x is None or y is None or abs(x - y) <= 1e-4:
                continue
            lo, hi = min(x, y), max(x, y)
            for k in range(1, 6):
                a0 = F(round((lo + (hi - lo) * k / 6) * 1e6), 10**6)
                if 0 <= a0 <= amax:
                    out.append(dict(family=fam, cost=cost, tilt=tilt, rho=rho, a0=str(a0), side=side,
                                    edges=dict(LN=LN, UN=UN, LE=LE, UE=UE)))
    return out


def task(s):
    I = r16.build(s)
    B = r16.bayes(I)
    cells = {D + R: r16.cell(I, B, D, R) for D, R in r16.CELLS}
    ub = {}
    for R in "NE":
        e = cells["E" + R]
        V, u0 = r16.red008.solve(I, B, "E", R)
        U1 = r16.red008.SOL[0]
        b = None if V is None else r16.red008.bracket(I, B, "F", R, u0, U1)
        ub[R] = None if b is None or e is None or e["bracket"] is None else float(b[1]) - min(e["bracket"])
    phi = {}
    if all(cells[c] for c in ("FN", "FE", "EN", "EE")):
        for name, c in (("A_N", "FN"), ("A_E", "FE"), ("B_N", "EN"), ("B_E", "EE")):
            u0 = cells[c]["u0"]
            cE, _ = math015.solve_fixed(I, B, u0, "E")
            cN, _ = math015.solve_fixed(I, B, u0, "N")
            phi[name] = (cE - cN) * 1e4
    return dict(s, cells=cells, ub=ub, phi=phi)


def main():
    rows = json.load(open(HERE / "results.json"))
    brs = [c["bracket"] for r in rows for c in r["cells"].values() if c and c["bracket"]]
    brs += [p[k] for r in rows for p in r["grid"] for k in ("WE", "WN") if p[k]]
    tau = 10 * max(max(0.0, b[0] - b[1]) for b in brs)
    if not (HERE / "crossing.json").exists():
        P = points(rows)
        print(f"{len(P)} fine incumbents")
        with Pool(int(os.environ.get("PROCS", "8"))) as pool:
            res = pool.map(task, P, chunksize=1)
        (HERE / "crossing.json").write_text(json.dumps(res, indent=0))
    res = json.load(open(HERE / "crossing.json"))
    wid = lambda b: (min(b) - tau, max(b) + tau)  # noqa: E731
    print("## Region-crossing search (fine incumbents inside band-edge gaps)\n")
    print("| family | costs | tilt | rho | side | a0 | Delta_N | Delta_E | crossing | part 3 check |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    ncross = nfail = 0
    for r in res:
        c = r["cells"]
        cls = {}
        for R in "NE":
            f, e = c["F" + R], c["E" + R]
            if not (f and e and f["bracket"] and e["bracket"]):
                cls[R] = "?"
                continue
            if wid(f["bracket"])[0] - wid(e["bracket"])[1] > 0:
                cls[R] = f"> 0 ({wid(f['bracket'])[0] - wid(e['bracket'])[1]:.4f})"
            elif r["ub"][R] is not None and r["ub"][R] <= EPS:
                cls[R] = f"0 (<= {max(r['ub'][R], 0):.1e})"
            else:
                cls[R] = "?"
        cross = ("N0 < E" if cls["N"].startswith("0") and cls["E"].startswith(">") else
                 "E0 < N" if cls["E"].startswith("0") and cls["N"].startswith(">") else "")
        chk = ""
        if cross and r["phi"]:
            p = r["phi"]
            ok = p["A_E"] > p["B_N"] if cross == "N0 < E" else p["A_N"] < p["B_E"]
            chk = (f"phi(A_E) {p['A_E']:.3f} > phi(B_N) {p['B_N']:.3f}" if cross == "N0 < E" else
                   f"phi(A_N) {p['A_N']:.3f} < phi(B_E) {p['B_E']:.3f}") + (" holds" if ok else " FAILS")
            nfail += not ok
        ncross += bool(cross)
        r["_cross"] = cross
        print(f"| {r['family']} | {r['cost']} | {r['tilt']} | {r['rho']} | {r['side']} | {float(F(r['a0'])):.4f} | "
              f"{cls['N']} | {cls['E']} | {cross or '-'} | {chk or '-'} |")
    print(f"\nfine incumbents {len(res)}; region crossings {ncross}; part-3 checks failing {nfail}")
    for fam in sorted({r["family"] for r in res}):
        print(f"- {fam}: fine incumbents {sum(1 for r in res if r['family'] == fam)}, "
              f"crossings {sum(1 for r in res if r['family'] == fam and r['_cross'])}")


if __name__ == "__main__":
    main()

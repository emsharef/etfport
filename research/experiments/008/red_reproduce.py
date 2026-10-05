"""Red's reproduction of experiment 008, written from the registered Design without reading run.py.

The fixtures INST_A and INST_C, the Bayes construction and the per-observation recheck come from
red's own `checks/red-m3-definition/check.py`, which the Design names. The convex program here is
re-implemented with a selectable solver. Every one of the 180 cells is solved with CLARABEL and rechecked
per observation, then compared with results.json. The headline cells are then re-solved with a
different algorithm (SCS, a first-order splitting method), so that the displayed witness, the free-ETF
diagnostic and fixture C's unconfirmed changes do not rest on one interior-point solver.

Usage: uv run python experiments/008/red_reproduce.py
"""
import itertools
import json
import sys
from collections import defaultdict
from fractions import Fraction as Fr
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "checks" / "red-m3-definition"))
from check import INST_A, INST_C, bayes, funded_projection, nested, returns  # noqa: E402

CS = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)]
CELLS = [(D, R) for D in "FE" for R in "FEN"]
SOL = [None]   # review-1 trades of the last successful joint solve, by observation


def build(base, c, schedule):
    I = dict(base)
    xa = base["x0"][0]
    I["x0"], I["h0"] = (xa, (1 - c) * (1 - xa)), c * (1 - xa)
    kb, ks = base["kb"], base["ks"]
    if schedule == "ETF-free":
        kb, ks = (kb[0], Fr(0)), (ks[0], Fr(0))
    elif schedule == "all-zero":
        kb, ks = (Fr(0), Fr(0)), (Fr(0), Fr(0))
    I["kb"], I["ks"] = kb, ks
    return I


def solve(I, B, root, cont, solver="CLARABEL", **opts):
    """V_{root,cont}: one convex program in (u_0, {u_1(y)}), scaled as exp(-rho (W_2 - 1))."""
    Y, P0, post = B
    d = len(I["x0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); rho = float(I["rho"])
    fee = lambda u: kb @ cp.pos(u) + ks @ cp.neg(u)
    u0 = cp.Variable(d)
    cons = [x0 + u0 >= 0, h0 - cp.sum(u0) - fee(u0) >= 0]
    cons += {"F": [], "E": [u0[0] == 0], "N": [u0 == 0]}[root]
    h0p = h0 - cp.sum(u0) - fee(u0)
    expo, mass, U1 = [], [], {}
    for y in Y:
        if P0[y] == 0:
            continue
        x1 = cp.multiply(np.array([1 + float(r) for r in y[1]]), x0 + u0)
        u1 = U1[y] = cp.Variable(d)
        cons += [x1 + u1 >= 0, h0p - cp.sum(u1) - fee(u1) >= 0]
        cons += {"F": [], "E": [u1[0] == 0], "N": [u1 == 0]}[cont]
        rows = []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    rows.append([1 + float(r) for r in returns(I, t, s)[1]])
                    mass.append(float(P0[y] * pt * s[0]))
        expo.append(-rho * (h0p - cp.sum(u1) - fee(u1) + np.array(rows) @ (x1 + u1) - 1))
    prob = cp.Problem(cp.Minimize(cp.sum(cp.multiply(np.array(mass), cp.exp(cp.hstack(expo))))), cons)
    try:
        prob.solve(solver=solver, **opts)
    except cp.error.SolverError:
        return None, None
    if prob.status != "optimal":
        return None, None
    SOL[0] = {y: v.value for y, v in U1.items()}
    return -prob.value * np.exp(-rho), u0.value


def bracket(I, B, D, R, u0, U1):
    """Bracket the optimal CE of cell (D, R) with a feasible policy and a Frank-Wolfe bound.

    Split every trade into purchase and sale parts, z = (p0, m0, {p1(y), m1(y)}) >= 0. Then the fees,
    funding and holdings constraints are linear, and terminal wealth on each path is affine in z. The
    lifted problem has the same optimum, since offsetting purchases and sales never raise wealth.
    S(z) = sum mass exp(-rho (W - 1)) is smooth and convex, and V = -exp(-rho) S. For a feasible zbar,
    S* <= S(zbar), and convexity gives S* >= S(zbar) + min over feasible w of grad S(zbar).(w - zbar),
    a linear program (HiGHS). So CE* lies in [1 - ln S(zbar)/rho, 1 - ln S_lo/rho].
    zbar is the joint solution after the funded projection at the root and at every node. The
    bracket is exact up to floating-point evaluation of S, its gradient and the LP."""
    from scipy.optimize import linprog
    Y, P0, post = B
    ys = [y for y in Y if P0[y] > 0]
    d = len(I["x0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); rho = float(I["rho"])
    zero_root = {"F": [], "E": [0], "N": list(range(d))}[D]
    zero_node = {"F": [], "E": [0], "N": list(range(d))}[R]
    # Feasible point: funded projection of the joint solution at the root and at each node.
    u = np.array(u0, dtype=float); u[zero_root] = 0.0
    x1p, h1, u = funded_projection(x0, h0, u, kb, ks)
    zb = [np.maximum(u, 0), np.maximum(-u, 0)]
    for y in ys:
        g1 = np.array([1 + float(r) for r in y[1]])
        v = np.zeros(d) if R == "N" else np.array(U1[y], dtype=float)
        v[zero_node] = 0.0
        _, hn, v = funded_projection(g1 * x1p, h1, v, kb, ks)
        if hn < -1e-12:
            raise AssertionError("projection left negative node cash")
        zb += [np.maximum(v, 0), np.maximum(-v, 0)]
    zb = np.concatenate(zb)
    n = len(zb)
    # Affine terminal wealth W = c + a.z for each path, with its mass.
    rows_a, consts, masses = [], [], []
    for k, y in enumerate(ys):
        g1 = np.array([1 + float(r) for r in y[1]])
        for t, pt in post[y].items():
            if pt == 0:
                continue
            for s in I["shocks"]:
                g2 = np.array([1 + float(r) for r in returns(I, t, s)[1]])
                a = np.zeros(n)
                a[0:d] = -1 - kb + g2 * g1
                a[d:2 * d] = 1 - ks - g2 * g1
                o = 2 * d * (k + 1)
                a[o:o + d] = -1 - kb + g2
                a[o + d:o + 2 * d] = 1 - ks - g2
                rows_a.append(a); consts.append(h0 + g2 @ (g1 * x0)); masses.append(float(P0[y] * pt * s[0]))
    Amat, cvec, mvec = np.array(rows_a), np.array(consts), np.array(masses)
    e = mvec * np.exp(-rho * (cvec + Amat @ zb - 1))
    S = e.sum()
    grad = -rho * (e @ Amat)
    # Linear constraints A_ub z <= b_ub and bounds.
    Aub, bub = [], []
    def row():
        return np.zeros(n)
    for i in range(d):                                   # root holdings: m0 - p0 <= x0
        r_ = row(); r_[i] = -1; r_[d + i] = 1; Aub.append(r_); bub.append(x0[i])
    r_ = row(); r_[0:d] = 1 + kb; r_[d:2 * d] = -(1 - ks); Aub.append(r_); bub.append(h0)   # root cash
    for k, y in enumerate(ys):
        g1 = np.array([1 + float(r) for r in y[1]])
        o = 2 * d * (k + 1)
        for i in range(d):                               # node holdings
            r_ = row(); r_[i] = -g1[i]; r_[d + i] = g1[i]; r_[o + i] = -1; r_[o + d + i] = 1
            Aub.append(r_); bub.append(g1[i] * x0[i])
        r_ = row(); r_[0:d] = 1 + kb; r_[d:2 * d] = -(1 - ks); r_[o:o + d] = 1 + kb; r_[o + d:o + 2 * d] = -(1 - ks)
        Aub.append(r_); bub.append(h0)                   # node cash
    bounds = [(0, None)] * n
    for i in zero_root:
        bounds[i] = bounds[d + i] = (0, 0)
    for k in range(len(ys)):
        o = 2 * d * (k + 1)
        for i in zero_node:
            bounds[o + i] = bounds[o + d + i] = (0, 0)
    resid = max((np.array(Aub) @ zb - np.array(bub)).max(), 0.0)
    lp = linprog(grad, A_ub=np.array(Aub), b_ub=np.array(bub), bounds=bounds, method="highs")
    if lp.status != 0:
        return None
    S_lo = S + lp.fun - grad @ zb
    if S_lo <= 0:
        return None
    lo, hi = (1 - np.log(S) / rho) * 1e4, (1 - np.log(S_lo) / rho) * 1e4
    return lo, hi, resid


def ce(V, rho):
    return -np.log(-V) / float(rho) * 1e4


def fixture_checks(I):
    Y, P0, post = bayes(I)
    pos = all(1 + r > 0 for t in I["Theta"] for s in I["shocks"] for r in returns(I, t, s)[1])
    nondeg = all(len({returns(I, t, s)[1][i] for s in I["shocks"]}) > 1
                 for t in I["Theta"] for i in range(len(I["x0"])))
    amb = [y for y in Y if P0[y] > 0 and sum(v > 0 for v in post[y].values()) > 1]
    return dict(observations=sum(P0[y] > 0 for y in Y), positive=pos, nondegenerate=nondeg,
                ambiguous=len(amb), prob=sum(P0[y] for y in amb))


def contributions(ceD):
    Dl = {R: ceD["F", R] - ceD["E", R] for R in "FEN"}
    return Dl, Dl["E"] - Dl["N"], Dl["F"] - Dl["E"]


def main():
    fails = []
    rep = json.load(open(HERE / "results.json"))["results"]
    fixtures = {"A": INST_A, "C": INST_C}
    grid, eps = {}, {}
    maxdiff, unresolved, fallback = 0.0, [], []
    brk, nobr = {}, []
    for name, base in fixtures.items():
        print(f"fixture {name}: {fixture_checks(base)}")
        for sched, c in itertools.product(("original", "ETF-free", "all-zero"), CS):
            I = build(base, c, sched)
            B = bayes(I)
            key = f"{sched},{c}" if sched != "original" else f"original,{c}"
            for D, R in CELLS:
                V, u0 = solve(I, B, D, R)
                if V is None:             # fall back to the first-order solver
                    V, u0 = solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
                    fallback.append((name, sched, str(c), D, R))
                if V is None:
                    unresolved.append((name, sched, str(c), D, R))
                    continue
                v = ce(V, I["rho"])
                u0p = np.array(u0)
                if D == "E":
                    u0p[0] = 0.0      # an E root trade is exactly zero on the active coordinate
                try:
                    eps[name, sched, c, D, R] = abs(v - ce(nested(I, B, R, u0p), I["rho"]))
                except RuntimeError:          # a per-observation re-solve was not optimal
                    eps[name, sched, c, D, R] = float("inf")
                grid[name, sched, c, D, R] = (v, u0[0])
                br = bracket(I, B, D, R, u0, SOL[0])
                if br is None:
                    nobr.append((name, sched, str(c), D, R))
                else:
                    brk[name, sched, c, D, R] = br
                theirs = rep[name]["points"].get(f"{sched},{c}", {}).get("cells", {}).get(f"{D},{R}")
                if theirs and theirs.get("CE") is not None:
                    maxdiff = max(maxdiff, abs(theirs["CE"] - v))
    print(f"cells solved {len(grid)} of 180 ({len(fallback)} by the SCS fallback); unresolved {len(unresolved)}")
    print(f"max |red CE - reported CE| over solved cells: {maxdiff:.2e} bp; max red recheck eps: "
          f"{max(e for e in eps.values() if e < float('inf')):.2e} bp; rechecks not optimal: "
          f"{sum(e == float('inf') for e in eps.values())}")

    # Free-ETF diagnostic and the claim-012 sign pattern.
    for name in fixtures:
        for sched in ("ETF-free", "all-zero"):
            ch = max(abs(grid[name, sched, c, D, R][0] - grid[name, sched, CS[0], D, R][0])
                     for c in CS for D, R in CELLS if (name, sched, c, D, R) in grid and (name, sched, CS[0], D, R) in grid)
            print(f"free-ETF diagnostic {name} {sched}: max |CE(c) - CE(0)| = {ch:.2e} bp")
            if ch > 1e-5:
                fails.append(f"free-ETF invariance fails in {name} {sched}")
    pattern = 0
    table = {}
    for name, sched, c in itertools.product(fixtures, ("original", "ETF-free", "all-zero"), CS):
        if all((name, sched, c, D, R) in grid for D, R in CELLS):
            _, etf, act = contributions({(D, R): grid[name, sched, c, D, R][0] for D, R in CELLS})
            table[name, sched, c] = (etf, act)
            pattern += etf > 0.01 and act < -0.01
    print(f"claim 012 pattern (ETF channel > 0, active channel < 0): {pattern} of {len(table)} points")
    for name in fixtures:
        print(f"  {name} original:", "  ".join(f"c={c}: {table[name, 'original', c][0]:+.4f} {table[name, 'original', c][1]:+.4f}"
                                              for c in CS if (name, "original", c) in table))

    # Cash-composition changes under the original schedule, with the registered resolution rule.
    cand = []
    for name in fixtures:
        for c1, c2 in itertools.combinations(CS, 2):
            if (name, "original", c1) in table and (name, "original", c2) in table:
                for k, lab in ((0, "ETF"), (1, "ACT")):
                    x = table[name, "original", c2][k] - table[name, "original", c1][k]
                    unc = sum(eps[name, "original", c, D, R] for c in (c1, c2) for D, R in CELLS)
                    if abs(x) > max(0.01, 3 * unc):
                        cand.append((name, c1, c2, lab, x, unc))
    print(f"resolved cash-composition changes (original schedule): {len(cand)}")
    wA = [x for x in cand if x[0] == "A"]
    print("  A:", [(str(a), str(b), lab, round(x, 4)) for _, a, b, lab, x, _ in wA])
    print("  C:", [(str(a), str(b), lab, round(x, 4)) for n_, a, b, lab, x, _ in cand if n_ == "C"])
    for c in (Fr(0), Fr(1)):
        print(f"  A original c={c}: Delta_E {grid['A', 'original', c, 'F', 'E'][0] - grid['A', 'original', c, 'E', 'E'][0]:.4f} bp; "
              f"root-F u0A under F_1, E_1, N_1: "
              + ", ".join(f"{grid['A', 'original', c, 'F', R][1]:+.5f}" for R in "FEN"))

    # Certified (up to floating point) brackets and the derived quantities as intervals.
    w = [hi - lo for lo, hi, _ in brk.values()]
    print(f"\nBrackets: {len(brk)} of {len(grid)} cells; no bracket {len(nobr)} {nobr[:4]}; width max {max(w):.2e} bp, "
          f"median {np.median(w):.2e} bp; max projected-point constraint residual {max(r for *_, r in brk.values()):.1e}; "
          f"largest excursion of a joint-solver CE outside its bracket {max(max(lo - grid[k][0], grid[k][0] - hi, 0) for k, (lo, hi, _) in brk.items()):.1e} bp; "
          f"cells with width > 1e-4 bp: {[(k, round(hi - lo, 5)) for k, (lo, hi, _) in brk.items() if hi - lo > 1e-4]}")
    def contrib_iv(name, sched, c):
        L = {k: brk[(name, sched, c) + k][0] for k in CELLS}; U = {k: brk[(name, sched, c) + k][1] for k in CELLS}
        # Delta_E - Delta_N = FE - EE - FN + EN; Delta_F - Delta_E = FF - EF - FE + EE
        etf = (L["F", "E"] - U["E", "E"] - U["F", "N"] + L["E", "N"], U["F", "E"] - L["E", "E"] - L["F", "N"] + U["E", "N"])
        act = (L["F", "F"] - U["E", "F"] - U["F", "E"] + L["E", "E"], U["F", "F"] - L["E", "F"] - L["F", "E"] + U["E", "E"])
        return etf, act
    ivs = {k: contrib_iv(*k) for k in table if all(k + c_ in brk for c_ in CELLS)}
    sign_ok = sum(e[0] > 0 and a[1] < 0 for e, a in ivs.values())
    print(f"claim 012 pattern certified by interval at {sign_ok} of {len(ivs)} points")
    cert = 0
    for name, c1, c2, lab, x, _ in cand:
        k = 0 if lab == "ETF" else 1
        if (name, "original", c1) in ivs and (name, "original", c2) in ivs:
            a1, a2 = ivs[name, "original", c1][k], ivs[name, "original", c2][k]
            lo_, hi_ = a2[0] - a1[1], a2[1] - a1[0]
            cert += (lo_ > 0) == (x > 0) and (lo_ > 0 or hi_ < 0)
            if name == "A" and c1 == 0:
                print(f"  witness A 0->1 {lab}: change in [{lo_:+.6f}, {hi_:+.6f}] bp (point {x:+.4f})")
    print(f"cash-composition changes whose sign is certified by interval: {cert} of {len(cand)}")
    fe = max(max(abs(ivs[n_, s_, c][k][j] - ivs[n_, s_, CS[0]][k][j]) for c in CS for k in (0, 1) for j in (0, 1))
             for n_ in fixtures for s_ in ("ETF-free", "all-zero"))
    print(f"free-ETF schedules: contribution intervals move by at most {fe:.1e} bp across c")

    # Cross-solver check with SCS on the witness, the free-ETF diagnostic and fixture C's changes.
    print("\nSCS cross-check (eps 1e-10); contributions in bp:")
    scs = {}
    for name, sched, c in [("A", "original", Fr(0)), ("A", "original", Fr(1)), ("A", "ETF-free", Fr(0)),
                           ("A", "ETF-free", Fr(1))] + [("C", "original", c) for c in CS]:
        I = build(fixtures[name], c, sched)
        B = bayes(I)
        vals = {}
        for D, R in CELLS:
            V, _ = solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
            vals[D, R] = None if V is None else ce(V, I["rho"])
        if any(v is None for v in vals.values()):
            print(f"  {name} {sched} c={c}: SCS failed in some cell")
            continue
        _, etf, act = contributions(vals)
        scs[name, sched, c] = (etf, act)
        dev = max(abs(vals[k] - grid[name, sched, c, k[0], k[1]][0]) for k in CELLS if (name, sched, c) + k in grid)
        print(f"  {name} {sched} c={c}: ETF {etf:+.4f} ACT {act:+.4f}; max |SCS - CLARABEL| CE {dev:.1e} bp")
    if ("A", "original", Fr(0)) in scs and ("A", "original", Fr(1)) in scs:
        d = [scs["A", "original", Fr(1)][k] - scs["A", "original", Fr(0)][k] for k in (0, 1)]
        print(f"  SCS witness A c=0->1: ETF {d[0]:+.4f}, ACT {d[1]:+.4f} bp (reported -0.3023, +0.3023)")
        if not (abs(d[0] + 0.3023) < 0.01 and abs(d[1] - 0.3023) < 0.01):
            fails.append("SCS does not reproduce the A witness")
    cs = [c for c in CS if ("C", "original", c) in scs]
    if len(cs) == 5:
        print("  SCS fixture C adjacent steps of the ETF contribution:",
              [round(scs["C", "original", b][0] - scs["C", "original", a][0], 3) for a, b in zip(cs, cs[1:])])
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

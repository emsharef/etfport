"""Experiment 008: M3 cash composition across future controls (registered design in
experiments/008-m3-cash-composition.md). Floating-point convex optimization (CLARABEL) with exact finite
expectations, a nested per-observation recheck and a tighter-tolerance recheck of candidate effects.

Fixtures INST_A and INST_C are imported unchanged from checks/red-m3-definition/check.py, as are its
`returns` and `bayes` (exact rational Bayes bookkeeping). Everything else is here.
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "checks" / "red-m3-definition"))
import check as red  # noqa: E402

FIXTURES = {"A": red.INST_A, "C": red.INST_C}
CASH = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)]      # initial cash as a fraction of the nonactive sleeve
SCHEDULES = ["original", "ETF-free", "all-zero"]
LADDER = [1e-10, 1e-9, 1e-8]                               # Deviation 1: first-pass tolerance ladder
TIGHT_LADDER = [1e-12, 1e-11]                              # Deviation 1: candidate recheck ladder
FLOOR_BP = 0.01                                            # predeclared minimum resolvable size (bp)
MULT = 3.0                                                 # resolved if |x| > max(FLOOR_BP, MULT * uncertainty)


def fixture(I, c, schedule):
    a0 = I["x0"][0]
    sleeve = 1 - a0
    J = dict(I)
    J["x0"] = (a0, (1 - c) * sleeve)
    J["h0"] = c * sleeve
    kb, ks = I["kb"], I["ks"]
    if schedule == "ETF-free":
        kb, ks = (kb[0], Fr(0)), (ks[0], Fr(0))
    elif schedule == "all-zero":
        kb, ks = (Fr(0), Fr(0)), (Fr(0), Fr(0))
    J["kb"], J["ks"] = kb, ks
    return J


def cost(u, kb, ks):
    return kb @ cp.pos(u) + ks @ cp.neg(u)


def solve_joint(I, B, D, R, tol):
    """V_{D,R} (expected U_rho(W_2), W_0 = 1) as one convex program; returns (V, u0, status)."""
    Y, P0, post = B
    d = len(I["x0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); rho = float(I["rho"])
    u0 = cp.Variable(d)
    cons = [x0 + u0 >= 0, h0 - cp.sum(u0) - cost(u0, kb, ks) >= 0]
    cons += {"F": [], "E": [u0[0] == 0]}[D]
    x0p, h0p = x0 + u0, h0 - cp.sum(u0) - cost(u0, kb, ks)
    expo, mass = [], []
    for y in Y:
        if P0[y] == 0:
            continue
        x1 = cp.multiply(np.array([1 + float(r) for r in y[1]]), x0p)
        u1 = cp.Variable(d)
        cons += [x1 + u1 >= 0, h0p - cp.sum(u1) - cost(u1, kb, ks) >= 0]
        cons += {"F": [], "E": [u1[0] == 0], "N": [u1 == 0]}[R]
        h1p = h0p - cp.sum(u1) - cost(u1, kb, ks)
        rows = []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    rows.append([1 + float(r) for r in red.returns(I, t, s)[1]])
                    mass.append(float(P0[y] * pt * s[0]))
        expo.append(-rho * (h1p + np.array(rows) @ (x1 + u1) - 1))   # scaled by exp(rho); undone below
    prob = cp.Problem(cp.Minimize(cp.sum(cp.multiply(np.array(mass), cp.exp(cp.hstack(expo))))), cons)
    for tl in tol:
        try:
            prob.solve(solver="CLARABEL", tol_gap_abs=tl, tol_gap_rel=tl, tol_feas=tl, max_iter=1000)
        except cp.error.SolverError:
            continue
        if prob.status == "optimal":
            return -prob.value * np.exp(-rho), np.array(u0.value), tl
    return None, None, prob.status


def nested(I, B, R, u0, tol):
    """Fix the root trade (projected onto the funded set) and solve each observation's review-1 problem
    separately: the value of a feasible policy, used as the numerical recheck."""
    Y, P0, post = B
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); rho = float(I["rho"])
    h0 = float(I["h0"])
    # Deviation 3: a genuine funded projection. Clip sales at the holdings, then scale the whole trade
    # toward zero until cash is nonnegative. Costs are positively homogeneous, so cash is linear along the
    # ray t*u; scaling preserves the F/E restriction (u_A = 0 stays 0). The old code clamped negative cash
    # to zero without reducing holdings, which can create wealth.
    u = np.maximum(np.asarray(u0, dtype=float), -x0)
    out = u.sum() + kb @ np.maximum(u, 0) + ks @ np.maximum(-u, 0)
    if out > h0:
        u = u * (h0 / out)
    x = x0 + u
    h = h0 - u.sum() - kb @ np.maximum(u, 0) - ks @ np.maximum(-u, 0)
    if h < -1e-12:
        raise RuntimeError(f"funded projection failed: cash {h}")
    h = max(h, 0.0)
    total = 0.0
    for y in Y:
        if P0[y] == 0:
            continue
        g = np.array([1 + float(r) for r in y[1]])
        x1 = x * g
        rows, mass = [], []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    rows.append([1 + float(r) for r in red.returns(I, t, s)[1]])
                    mass.append(float(pt * s[0]))
        rows, mass = np.array(rows), np.array(mass)
        if R == "N":
            total += float(P0[y]) * float(mass @ -np.exp(-rho * (h + rows @ x1)))
            continue
        u1 = cp.Variable(len(x))
        cons = [x1 + u1 >= 0, h - cp.sum(u1) - cost(u1, kb, ks) >= 0]
        if R == "E":
            cons.append(u1[0] == 0)
        h1 = h - cp.sum(u1) - cost(u1, kb, ks)
        prob = cp.Problem(cp.Minimize(mass @ cp.exp(-rho * (h1 + rows @ (x1 + u1) - 1))), cons)
        val = None
        for tl in tol:
            try:
                prob.solve(solver="CLARABEL", tol_gap_abs=tl, tol_gap_rel=tl, tol_feas=tl, max_iter=1000)
            except cp.error.SolverError:
                continue
            if prob.status == "optimal":
                val = prob.value
                break
        if val is None:
            return None
        total += float(P0[y]) * (-val * np.exp(-rho))
    return total


def ce_bp(V, rho):
    return -np.log(-V) / float(rho) * 1e4


def point(I, B, tol):
    out = {}
    for D, R in product("FE", "FEN"):
        V, u0, st = solve_joint(I, B, D, R, tol)
        if V is None:
            out[D, R] = dict(status=st)
            continue
        Vn = nested(I, B, R, u0, tol)
        ce, cen = ce_bp(V, I["rho"]), (None if Vn is None else ce_bp(Vn, I["rho"]))
        out[D, R] = dict(status="optimal" if cen is not None else "nested recheck failed", tol=st, CE=ce,
                         CE_nested=cen, eps=(None if cen is None else abs(ce - cen)),
                         u0A=float(u0[0]), u0E=float(u0[1]))
    return out


def derived(p):
    ok = all(p[k].get("eps") is not None for k in p)
    if not ok:
        return None
    D = {R: p["F", R]["CE"] - p["E", R]["CE"] for R in "FEN"}
    uD = {R: p["F", R]["eps"] + p["E", R]["eps"] for R in "FEN"}
    return dict(Delta=D, uDelta=uD, ETF=D["E"] - D["N"], uETF=uD["E"] + uD["N"],
                ACT=D["F"] - D["E"], uACT=uD["F"] + uD["E"])


def resolved(x, u):
    return abs(x) > max(FLOOR_BP, MULT * u)


def checks(I):
    """Conditional risk (per theta, every instrument's return varies over scenarios) and posterior
    ambiguity (observations with at least two positive posterior masses), exact."""
    Y, P0, post = red.bayes(I)
    risk = all(len({red.returns(I, t, s)[1][i] for s in I["shocks"]}) > 1
               for t in I["Theta"] for i in range(len(I["x0"])))
    amb = [y for y in Y if P0[y] > 0 and sum(1 for t in I["Theta"] if post[y][t] > 0) > 1]
    return dict(observations=len(Y), conditional_risk_nondegenerate=risk, ambiguous_observations=len(amb),
                prob_ambiguous=str(sum(P0[y] for y in amb)),
                positive_returns=all(1 + r > 0 for t in I["Theta"] for s in I["shocks"] for r in red.returns(I, t, s)[1]))


def main() -> None:
    t0 = time.time()
    res = {}
    for name, I0 in FIXTURES.items():
        res[name] = dict(checks=checks(I0), points={})
        for sch, c in product(SCHEDULES, CASH):
            I = fixture(I0, c, sch)
            B = red.bayes(I)
            p = point(I, B, LADDER)
            res[name]["points"][(sch, c)] = dict(cells=p, derived=derived(p))
    # candidate effects under the original schedule: all pairs of cash levels
    cands = []
    for name in FIXTURES:
        pts = res[name]["points"]
        for c1, c2 in [(a, b) for i, a in enumerate(CASH) for b in CASH[i + 1:]]:
            d1, d2 = pts[("original", c1)]["derived"], pts[("original", c2)]["derived"]
            if d1 is None or d2 is None:
                continue
            for key, ukey in (("ETF", "uETF"), ("ACT", "uACT")):
                x, u = d2[key] - d1[key], d1[ukey] + d2[ukey]
                if resolved(x, u):
                    cands.append((name, c1, c2, key, x, u))
    # recheck candidates with the tighter tolerance
    tight = {}
    for name, c1, c2, key, x, u in cands:
        for c in (c1, c2):
            if (name, c) not in tight:
                I = fixture(FIXTURES[name], c, "original")
                pt = point(I, red.bayes(I), TIGHT_LADDER)
                tight[(name, c)] = (derived(pt), max((v.get("tol") or 1) for v in pt.values()))
    confirmed, unconfirmed = [], []
    for name, c1, c2, key, x, u in cands:
        (a, ta), (b, tb) = tight[(name, c1)], tight[(name, c2)]
        first = max(v.get("tol") or 1 for c in (c1, c2)
                    for v in res[name]["points"][("original", c)]["cells"].values())
        if a is None or b is None or max(ta, tb) >= first:
            unconfirmed.append((name, c1, c2, key, x, u, "no tighter solve"))
            continue
        ukey = "u" + key
        xt, ut = b[key] - a[key], a[ukey] + b[ukey]
        if resolved(xt, ut) and np.sign(xt) == np.sign(x):
            confirmed.append((name, c1, c2, key, x, u, xt, ut))
        else:
            unconfirmed.append((name, c1, c2, key, x, u, f"tight change {xt:+.4f} (unc. {ut:.1e})"))
    report(res, cands, confirmed, unconfirmed)
    def ser(o):
        if isinstance(o, dict):
            return {(",".join(str(x) for x in k) if isinstance(k, tuple) else str(k)): ser(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)):
            return [ser(x) for x in o]
        if isinstance(o, (np.floating, float)):
            return float(o)
        if isinstance(o, (bool, int, str)) or o is None:
            return o
        return str(o)
    (HERE / "results.json").write_text(json.dumps(ser(dict(results=res, candidates=cands, confirmed=confirmed, unconfirmed=unconfirmed)),
                                                  indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


def report(res, cands, confirmed, unconfirmed):
    print("### Fixture checks (exact)\n")
    for n, r in res.items():
        print(f"- {n}: {r['checks']}")
    for n, r in res.items():
        print(f"\n### Fixture {n}: CE (bp of W_0), Delta_R, contributions and root active trade (root F)\n")
        print("| Schedule | cash c | CE F,F | CE E,F | CE F,E | CE E,E | CE F,N | CE E,N | Delta_F | Delta_E | "
              "Delta_N | Delta_E-Delta_N (unc.) | Delta_F-Delta_E (unc.) | u0A under F_1, E_1, N_1 | max recheck eps |")
        print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
        for (sch, c), v in r["points"].items():
            p, d = v["cells"], v["derived"]
            if d is None:
                print(f"| {sch} | {c} | unresolved: {[(k, p[k]['status']) for k in p if p[k].get('eps') is None]} |")
                continue
            ce = lambda D, R: f"{p[D, R]['CE']:.4f}"  # noqa: E731
            print(f"| {sch} | {c} | {ce('F','F')} | {ce('E','F')} | {ce('F','E')} | {ce('E','E')} | {ce('F','N')} | "
                  f"{ce('E','N')} | {d['Delta']['F']:.4f} | {d['Delta']['E']:.4f} | {d['Delta']['N']:.4f} | "
                  f"{d['ETF']:.4f} ({d['uETF']:.1e}) | {d['ACT']:.4f} ({d['uACT']:.1e}) | "
                  f"{p['F','F']['u0A']:+.5f}, {p['F','E']['u0A']:+.5f}, {p['F','N']['u0A']:+.5f} | "
                  f"{max(p[k]['eps'] for k in p):.1e} (tol <= {max(p[k]['tol'] for k in p):.0e}) |")
        print("\nFree-ETF diagnostic: max over c of |CE_{D,R}(c) - CE_{D,R}(0)| and max over c of |contribution(c) - "
              "contribution(0)| (bp); a resolved nonzero value is an implementation error.\n")
        for sch in ("ETF-free", "all-zero"):
            good = [c for c in CASH if r["points"][(sch, c)]["derived"] is not None]
            if len(good) < 2:
                print(f"- {sch}: fewer than two resolved cash levels ({good}); diagnostic not available")
                continue
            base = r["points"][(sch, good[0])]
            worst = 0.0
            for c in good[1:]:
                pc = r["points"][(sch, c)]
                for k in base["cells"]:
                    x = abs(pc["cells"][k]["CE"] - base["cells"][k]["CE"])
                    u = pc["cells"][k]["eps"] + base["cells"][k]["eps"]
                    worst = max(worst, x)
                    if resolved(x, u):
                        print(f"  RESOLVED VIOLATION: {sch}, c {good[0]} -> {c}, cell {k}: {x:.2e} bp (unc. {u:.1e})")
            dcon = max(abs(r["points"][(sch, c)]["derived"][key] - base["derived"][key])
                       for c in good for key in ("ETF", "ACT"))
            print(f"- {sch}: resolved cash levels {[str(c) for c in good]}; max |CE change| {worst:.2e} bp, "
                  f"max |contribution change| {dcon:.2e} bp")
    print(f"\n### Cash-composition effects under original costs (all cash pairs)\n")
    print(f"Candidates passing the predeclared rule |x| > max({FLOOR_BP} bp, {MULT} x uncertainty): {len(cands)}; "
          f"confirmed by a strictly tighter re-solve (ladder {TIGHT_LADDER}): {len(confirmed)}\n")
    for row in unconfirmed:
        print(f"- unconfirmed: fixture {row[0]}, {row[1]} -> {row[2]}, {row[3]}: change {row[4]:+.4f} (unc. {row[5]:.1e}); {row[6]}")
    print()
    print("| Fixture | c -> c' | Contribution | change (bp) | uncertainty | tight change | tight uncertainty |")
    print("|---|---|---|---|---|---|---|")
    for name, c1, c2, key, x, u, xt, ut in confirmed:
        lab = "Delta_E-Delta_N" if key == "ETF" else "Delta_F-Delta_E"
        print(f"| {name} | {c1} -> {c2} | {lab} | {x:+.4f} | {u:.1e} | {xt:+.4f} | {ut:.1e} |")


if __name__ == "__main__":
    main()

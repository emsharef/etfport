"""Red's reproduction of experiment 017, written from the registered Design without reading run.py.

Instances are built from the Design's calibration (known premia, two alphas m -+ 50 bp, two-point factor
and ETF shocks, a 5-point binomial active residual). Cells and brackets come from red's experiment 008
engine through red's experiment 016 driver (`cell`). The myopic root is red's own CVXPY solve of M2's
one-quarter score (model/SPEC.md M2), not experiments/004/m2.py. Premia come from red's per-observation
solves (`nested`).

Usage: uv run python -W ignore experiments/017/red_reproduce.py [stage1|report|crossings]
"""
import importlib.util
import json
import sys
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("red016", HERE.parent / "016" / "red_reproduce.py")
R16 = importlib.util.module_from_spec(spec); spec.loader.exec_module(R16)
from check import bayes, bp, nested  # noqa: E402  (on the path via R16)
R8 = R16.R8

BP = F(1, 10000)
LAM = (F(184, 10000), F(897, 100000))
SIZES = (F(854, 10000), F(6095, 100000))
RATES = {"no-load": ((0, 1), (0, 1)), "front load": (("L", 1), (0, 1)), "deferred": ((0, 1), (100, 1))}
CELLS6 = [(D, R) for D in "FE" for R in "FEN"]


def inst(sched, rho, a0, m):
    (ba, be), (sa, se) = RATES[sched]
    ba = F(525, 9475) if ba == "L" else ba * BP
    shocks = []
    for s1 in (-1, 1):
        for s2 in (-1, 1):
            for k, w in zip((-2, -1, 0, 1, 2), (1, 4, 6, 4, 1)):
                for se_ in (-1, 1):
                    shocks.append((F(w, 128), (s1 * SIZES[0], s2 * SIZES[1]), F(k, 100), (se_ * F(2, 1000),)))
    Theta = [(LAM[0], LAM[1], F(m - 50, 10000)), (LAM[0], LAM[1], F(m + 50, 10000))]
    x0 = (F(a0), F(3, 5) - F(a0))
    return dict(BA=(F(1), F(3, 10)), BE=((F(1), F(0)),), cE=(BP,), Theta=Theta, pi0={t: F(1, 2) for t in Theta},
                shocks=shocks, kb=(F(ba), be * BP), ks=(sa * BP, se * BP), x0=x0, h0=1 - sum(x0), rho=F(rho))


def grid():
    return [dict(sched=s, rho=r, a0=a, m=m) for s in RATES for r in (2, 5, 10)
            for a in ("0", "3/20", "3/10", "9/20", "3/5") for m in (-25, 0, 25)]


def myopic(I):
    """M2 class F: max b'lambda + a E[alpha] - p c^E - (gamma/2) w'Sigma w - tau(w - w0), funded, long-only, caps 1."""
    BA = np.array([float(x) for x in I["BA"]]); BE = np.array([float(x) for x in I["BE"][0]])
    lam = np.array([float(x) for x in LAM]); alpha = float(sum(t[2] for t in I["Theta"]) / 2)
    B = np.vstack([BA, BE]); Sf = np.diag([float(s) ** 2 for s in SIZES]); D = np.diag([1e-4, 4e-6])
    Sig = B @ Sf @ B.T + D
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    w0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); g = float(I["rho"])
    w = cp.Variable(2); up, dn = cp.Variable(2, nonneg=True), cp.Variable(2, nonneg=True)
    tau = kb @ up + ks @ dn
    obj = (w @ B) @ lam + w[0] * alpha - w[1] * float(I["cE"][0]) - g / 2 * cp.quad_form(w, Sig) - tau
    cons = [w - w0 == up - dn, w >= 0, w <= 1, h0 - cp.sum(w - w0) - tau >= 0]
    cp.Problem(cp.Maximize(obj), cons).solve(solver="CLARABEL")
    wv = np.maximum(w.value, 0.0)
    u = wv - w0
    cost = kb @ np.maximum(u, 0) + ks @ np.maximum(-u, 0)
    return wv, max(h0 - u.sum() - cost, 0.0)


def value_E(I, B, u0):
    """Expected utility with the root trade u0 fixed (after the funded projection) and review-1 ETF-only
    trading, observation by observation with red's experiment 008 engine (SCS fallback)."""
    from check import funded_projection
    Y, P0, post = B
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x, h, _ = funded_projection(np.array([float(v) for v in I["x0"]]), float(I["h0"]), u0, kb, ks)
    J = dict(I); J["x0"] = tuple(F(max(v, 0.0)).limit_denominator(10 ** 12) for v in x); J["h0"] = F(max(h, 0.0)).limit_denominator(10 ** 12)
    tot = 0.0
    for y in Y:
        if P0[y] == 0:
            continue
        By = ([y], {y: F(1)}, {y: post[y]})
        V, _ = R8.solve(J, By, "N", "E")
        if V is None:
            V, _ = R8.solve(J, By, "N", "E", solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
        if V is None:
            return None
        tot += float(P0[y]) * V
    return tot


def stage1(k):
    I = inst(k["sched"], k["rho"], F(k["a0"]), k["m"]); B = bayes(I)
    out = dict(k, cells={f"{D}{R}": R16.cell(I, B, D, R) for D, R in CELLS6})
    wv, h = myopic(I)
    J = dict(I); J["x0"] = tuple(F(x).limit_denominator(10 ** 12) for x in wv); J["h0"] = F(h).limit_denominator(10 ** 12)
    J["x0"] = tuple(max(x, F(0)) for x in J["x0"])
    out["myopic_w"] = wv.tolist()
    out["myopic"] = R16.cell(J, bayes(J), "N", "F")
    ph = {}
    for name, ck in (("A_N", "FN"), ("A_E", "FE"), ("B_N", "EN"), ("B_E", "EE")):
        c = out["cells"][ck]
        if c is None:
            ph[name] = None; continue
        if False:
            pass
        u0 = np.array([c["uA"], c["uE"]])
        vE = value_E(I, B, u0)
        ph[name] = None if vE is None else bp(vE, I["rho"]) - bp(nested(I, B, "N", u0), I["rho"])
    out["phi"] = ph
    if k == grid()[0]:
        Y, P0, post = B
        amb = [y for y in Y if P0[y] > 0 and sum(1 for p in post[y].values() if p > 0) == 2]
        out["obs"] = (len([y for y in Y if P0[y] > 0]), len(amb), float(sum(P0[y] for y in amb)))
    return out


def myopic_cell(I):
    """The myopic root's trade fixed, review-1 trading optimized: cell (N, F) of the post-trade instance.
    Cash below 1e-7 (0.001 bp) is set to zero: the solvers return optimal_inaccurate on the nearly
    degenerate budget otherwise, and dropping it can only lower the myopic value (a conservative loss)."""
    wv, h = myopic(I)
    J = dict(I); J["x0"] = tuple(max(F(x).limit_denominator(10 ** 12), F(0)) for x in wv)
    J["h0"] = F(0) if h < 1e-7 else F(h).limit_denominator(10 ** 12)
    return wv, R16.cell(J, bayes(J), "N", "F")


def fix_myopic(k):
    I = inst(k["sched"], k["rho"], F(k["a0"]), k["m"])
    return myopic_cell(I)[1]


def run_fix_myopic():
    res = json.load(open(HERE / "red_stage1.json"))
    todo = [i for i, r in enumerate(res) if r["myopic"] is None or r["myopic"]["lo"] is None]
    with Pool(8) as p:
        out = p.map(fix_myopic, [res[i] for i in todo])
    for i, c in zip(todo, out):
        res[i]["myopic"] = c
    print(f"recomputed {len(todo)} myopic cells with near-zero cash snapped; still missing {sum(c is None for c in out)}")
    json.dump(res, open(HERE / "red_stage1.json", "w"))


def run_stage1():
    with Pool(8) as p:
        res = p.map(stage1, grid(), chunksize=1)
    json.dump(res, open(HERE / "red_stage1.json", "w"))


def iv(c):
    return None if c is None or c["lo"] is None else (c["lo"], c["hi"])


def report():
    res = json.load(open(HERE / "red_stage1.json"))
    print("observations (count, ambiguous, probability):", res[0].get("obs"))
    allc = [c for r in res for c in list(r["cells"].values()) + [r["myopic"]]]
    formed = [c for c in allc if c is not None and c["lo"] is not None]
    inv = max(c["inv"] for c in formed); tau = 10 * inv
    print(f"stage-1 brackets formed {len(formed)} of {len(allc)}; largest inversion {inv:.3e}; tau {tau:.3e} bp")
    for r in res:
        for k, c in list(r["cells"].items()) + [("myopic", r["myopic"])]:
            if c is None or c["lo"] is None:
                print("   missing", r["sched"], r["rho"], r["a0"], r["m"], k)
    W = lambda c: None if iv(c) is None else (iv(c)[0] - tau, iv(c)[1] + tau)
    stats = {"etf": [], "act": []}; my = []
    for r in res:
        c = {k: W(v) for k, v in r["cells"].items()}
        def comb(p, m_):
            if any(c[x] is None for x in p + m_): return None
            return (sum(c[x][0] for x in p) - sum(c[x][1] for x in m_), sum(c[x][1] for x in p) - sum(c[x][0] for x in m_))
        r["etf"] = comb(["FE", "EN"], ["EE", "FN"])          # Delta_E - Delta_N
        r["act"] = comb(["FF", "EE"], ["EF", "FE"])          # Delta_F - Delta_E
        for key in ("etf", "act"):
            stats[key].append(r[key])
        cm = W(r["myopic"])
        if c["FF"] is not None and cm is not None:
            lo, hi = max(c["FF"][0] - cm[1], 0.0), max(c["FF"][1] - cm[0], 0.0)
            my.append((lo, hi, r["sched"], r["rho"], r["a0"], r["m"], r["myopic_w"]))
    for key, lab in (("etf", "future-ETF channel"), ("act", "future-active channel")):
        v = stats[key]
        pos = sum(1 for x in v if x and x[0] > 0); neg = sum(1 for x in v if x and x[1] < 0)
        unr = len(v) - pos - neg
        big = sum(1 for x in v if x and (x[0] >= 2 or x[1] <= -2))
        mids = [abs((x[0] + x[1]) / 2) for x in v if x]
        print(f"{lab}: + {pos}, - {neg}, unresolved {unr}; certified |.|>=2bp {big}; median |mid| {np.median(mids):.2f}; max |mid| {max(mids):.2f}")
    mids = [(a + b) / 2 for a, b, *_ in my]
    print(f"myopic loss: median mid {np.median(mids):.3f} bp; certified > 0 in {sum(1 for a, *_ in my if a > 0)}; "
          f"certified >= 2 in {sum(1 for a, *_ in my if a >= 2)}; max mid {max(mids):.2f}")
    for s in RATES:
        print(f"   max myopic mid, {s}: {max((a + b) / 2 for a, b, sc, *_ in my if sc == s):.2f} bp")
    for a, b, *rest in my:
        if a >= 2:
            print(f"   myopic >= 2 bp: [{a:.2f}, {b:.2f}] {rest[:4]} myopic w {np.round(rest[4], 3)}")
    # part 3 on this grid
    n = adj = phi = pd = 0
    for r in res:
        x = r["etf"]
        if x is None or not (x[0] > 0 or x[1] < 0) or any(r["phi"][k] is None for k in r["phi"]):
            continue
        sg = 1 if x[0] > 0 else -1; n += 1
        aE, aB = r["cells"]["FE"]["adj"], r["cells"]["EN"]["adj"]
        adj += np.sign(aE - aB) == sg; phi += np.sign(r["phi"]["A_E"] - r["phi"]["B_N"]) == sg
        pd += np.sign(r["phi"]["A_E"] / aE - r["phi"]["B_N"] / aB) == sg
    print(f"part 3 on this grid: {n} resolved ETF channels; sign follows adjustable {adj}, phi {phi}, per-dollar {pd}")
    json.dump(res, open(HERE / "red_stage1.json", "w"))


def cross_points():
    res = json.load(open(HERE / "red_stage1.json"))
    groups = {}
    for r in res:
        if r["sched"] != "no-load":
            groups.setdefault((r["sched"], r["rho"], r["m"]), []).append(r)
    pts, gaps = [], []
    for key, rs in groups.items():
        edges = {}
        for R in "NE":
            tg = [(float(F(r["a0"])) + r["cells"]["F" + R]["uA"], r["cells"]["F" + R]["uA"]) for r in rs if r["cells"]["F" + R]]
            buy = [t for t, u in tg if u > 1e-7]; sell = [t for t, u in tg if u < -1e-7]
            edges[R] = (np.median(buy) if buy else None, np.median(sell) if sell else None)
        for side in (0, 1):
            x, y = edges["N"][side], edges["E"][side]
            if x is None or y is None or abs(x - y) <= 1e-4:
                continue
            gaps.append((key, side, abs(x - y)))
            lo, hi = min(x, y), max(x, y)
            pts += [dict(sched=key[0], rho=key[1], m=key[2], a0=lo + (hi - lo) * j / 6) for j in range(1, 6)]
    return pts, gaps


def cross_one(k):
    a0 = F(k["a0"]).limit_denominator(10 ** 9)
    I = inst(k["sched"], k["rho"], a0, k["m"]); B = bayes(I)
    out = dict(k, cells={f"{D}{R}": R16.cell(I, B, D, R) for D, R in R16.CELLS})
    for R in "NE":
        V, u0 = R8.solve(I, B, "E", R)
        try:
            b = R8.bracket(I, B, "F", R, u0, R8.SOL[0]); out["Fat" + R] = max(b[0], b[1])
        except Exception:
            out["Fat" + R] = None
    return out


def run_crossings():
    pts, gaps = cross_points()
    print(f"groups with an edge gap > 1e-4: {len(gaps)} edges; gaps {min(g[2] for g in gaps):.5f}-{max(g[2] for g in gaps):.5f}; points {len(pts)}")
    with Pool(8) as p:
        res = p.map(cross_one, pts, chunksize=1)
    tau, ncross, both = 1.11e-3, 0, 0
    for r in res:
        c = r["cells"]; st = {}
        for R in "NE":
            if c["F" + R] is None or c["E" + R] is None:
                st[R] = "?"; continue
            lo = c["F" + R]["lo"] - c["E" + R]["hi"] - 2 * tau
            ub = None if r["Fat" + R] is None else r["Fat" + R] - c["E" + R]["lo"]
            st[R] = ">0" if lo > 0 else "0" if ub is not None and ub <= 1e-3 else "?"
        ncross += {st["N"], st["E"]} == {">0", "0"}
        both += st["N"] == st["E"] == ">0"
    print(f"crossing points {len(res)}: crossings {ncross}; both Deltas positive {both}")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "stage1"
    {"stage1": run_stage1, "report": report, "crossings": run_crossings, "fixmyopic": run_fix_myopic}[what]()

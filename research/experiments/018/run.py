"""Experiment 018 (D4): two-stage factor-then-manager procedure versus joint optimization in M2, exactly.
Registered design: experiments/018-m2-two-stage.md.

Calibration and grid reuse experiment 006's M2 cells (French premia and shock sizes, assumed alpha, residuals and
drag); active rates also include experiment 003's EDGAR medians. Every value is exact rational arithmetic with
the M2 solver of experiments/004/m2.py (sign-piece enumeration), so solver error is zero.

Stage 1 (factor allocation, without managers): b* = argmax_b lam'b - (gamma/2) b' Sf b over the implementable
exposure set R0 = {B'w : w >= 0, sum w <= 1} (no alpha, residuals, drag or costs).
Stage 2 (manager selection): maximize over M2's full-trading set
    [alpha w_A - c^E'w_E]  - tau(w - w0) - (gamma/2) [ (B'w - b*)' Sf (B'w - b*) + residual variance ],
with the bracketed term included in "2S-alpha" and omitted in "2S-lit" (the note's literal reading: meet the
target at least cost and residual risk). Stage 2 is an M2 problem with mean vector gamma B Sf b* (+ alpha, - c^E).
Check "2S-unc": stage 1 without R0 (b_u = (gamma Sf)^-1 lam) and 2S-alpha's stage 2 is the joint problem
itself, so its gap must be exactly 0.

Run: uv run python experiments/018/run.py          (writes experiments/018/results.json)
     uv run python experiments/018/run.py report
"""
from __future__ import annotations

import itertools
import json
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "004"))
from m2 import Instance2, check_instance, mean_vector, objective, sigma_formula, solve, tau  # noqa: E402

BP = Fr(1, 10000)
SF = (Fr(427, 5000), Fr(61, 1000))           # as 006: Mkt-RF SD 8.54%, HML SD 6.10% (data, gross)
LAM = (Fr(23, 1250), Fr(897, 100000))        # as 006: Mkt-RF mean 1.84%, HML mean 0.897% (data, gross)
BA = (Fr(1), Fr(3, 10))                      # as 006 (assumed)
SE_ETF = Fr(1, 500)                          # as 006 (assumed)
CE = Fr(1, 10000)                            # as 006 (assumed)
GEOMETRY = {                                 # as 006
    "G1-exact": ((Fr(1), Fr(0)), (Fr(1), Fr(3, 10))),
    "G2-missing": ((Fr(1), Fr(0)),),
    "G3-infeasible": ((Fr(1), Fr(0)), (Fr(1), Fr(3, 20))),
}
COSTS = {  # (active buy, active sell, ETF both ways)
    "Z": (Fr(0), Fr(0), Fr(0)),                                  # zero (006)
    "EQ5": (5 * BP, 5 * BP, 5 * BP),                             # assumed (006)
    "FL-554": (Fr(525, 9475), Fr(0), BP),                        # EDGAR median front load as M2 rate (003)
    "DC-100": (Fr(0), Fr(1, 100), BP),                           # EDGAR median deferred charge (003)
}
ALPHA = [Fr(-1, 200), Fr(-1, 400), Fr(0), Fr(1, 400), Fr(1, 200)]   # as 006 (assumed)
GAMMA = [Fr(2), Fr(5), Fr(10)]
SA = [Fr(1, 100), Fr(1, 50)]
STARTS = {"S1-active-heavy": (Fr(1, 2), Fr(2, 5)), "S2-etf-heavy": (Fr(1, 5), Fr(7, 10))}   # as 006


def instance(geom, cost, alpha, gamma, sA, start) -> Instance2:
    BE = GEOMETRY[geom]
    n = len(BE)
    ka_b, ka_s, ke = COSTS[cost]
    a0, p10 = STARTS[start]
    return Instance2(BA=BA, BE=BE, sf=SF, sA=sA, sE=(SE_ETF,) * n, lam=LAM, alpha=alpha, cE=(CE,) * n,
                     gamma=gamma, kbuy=(ka_b,) + (ke,) * n, ksell=(ka_s,) + (ke,) * n,
                     w0=(a0, p10) + (Fr(0),) * (n - 1), k0=1 - a0 - p10, wbar=(Fr(1),) * (1 + n))


def g1(b, gamma):
    return sum(LAM[k] * b[k] for k in range(2)) - gamma / 2 * sum(SF[k] ** 2 * b[k] ** 2 for k in range(2))


def in_hull(b, P):
    """b in conv(P) for 2-D points, exactly (Caratheodory: some triangle, segment or point contains it)."""
    for i, j, k in itertools.combinations(range(len(P)), 3):
        A, B_, C = P[i], P[j], P[k]
        det = (B_[0] - A[0]) * (C[1] - A[1]) - (C[0] - A[0]) * (B_[1] - A[1])
        if det == 0:
            continue
        l1 = ((b[0] - A[0]) * (C[1] - A[1]) - (C[0] - A[0]) * (b[1] - A[1])) / det
        l2 = ((B_[0] - A[0]) * (b[1] - A[1]) - (b[0] - A[0]) * (B_[1] - A[1])) / det
        if l1 >= 0 and l2 >= 0 and l1 + l2 <= 1:
            return True
    for i, j in itertools.combinations(range(len(P)), 2):   # degenerate hulls
        A, B_ = P[i], P[j]
        d = (B_[0] - A[0], B_[1] - A[1])
        if (b[0] - A[0]) * d[1] - (b[1] - A[1]) * d[0] == 0:
            dd = d[0] ** 2 + d[1] ** 2
            if dd and 0 <= ((b[0] - A[0]) * d[0] + (b[1] - A[1]) * d[1]) / dd <= 1:
                return True
    return any(tuple(b) == tuple(p) for p in P)


def stage1(I: Instance2, constrained=True):
    """Exact target exposures. Unconstrained: b_u = (gamma Sf)^-1 lam. Constrained: max over conv{0, rows of B}."""
    gam = I.gamma
    bu = tuple(LAM[k] / (gam * SF[k] ** 2) for k in range(2))
    if not constrained:
        return bu, False
    P = [(Fr(0), Fr(0)), tuple(I.BA)] + [tuple(r) for r in I.BE]
    if in_hull(bu, P):
        return bu, False
    cands = list(P)
    for A, B_ in itertools.combinations(P, 2):
        d = (B_[0] - A[0], B_[1] - A[1])
        den = gam * sum(SF[k] ** 2 * d[k] ** 2 for k in range(2))
        if den == 0:
            continue
        t = sum((LAM[k] - gam * SF[k] ** 2 * A[k]) * d[k] for k in range(2)) / den
        t = min(max(t, Fr(0)), Fr(1))
        cands.append((A[0] + t * d[0], A[1] + t * d[1]))
    return max(cands, key=lambda b: g1(b, gam)), True


def stage2(I: Instance2, bstar, with_alpha):
    """M2 problem whose mean vector is gamma B Sf b* (+ alpha e_A - c^E): exact."""
    lam2 = tuple(I.gamma * SF[k] ** 2 * bstar[k] for k in range(2))
    J = Instance2(BA=I.BA, BE=I.BE, sf=I.sf, sA=I.sA, sE=I.sE, lam=lam2,
                  alpha=I.alpha if with_alpha else Fr(0), cE=I.cE if with_alpha else (Fr(0),) * I.n,
                  gamma=I.gamma, kbuy=I.kbuy, ksell=I.ksell, w0=I.w0, k0=I.k0, wbar=I.wbar)
    _, w, opts = solve(J, "F", exact=True)
    return w, opts


def Q(I, w):
    return objective(I, sigma_formula(I), mean_vector(I), w)


def bind(I, w):
    v = [w[i] - I.w0[i] for i in range(I.d)]
    return dict(funding=sum(v) + tau(I, v) == I.k0, long_only=[i for i in range(I.d) if w[i] == 0],
                caps=[i for i in range(I.d) if w[i] == I.wbar[i]])


def expo(I, w):
    rows = [I.BA] + list(I.BE)
    return tuple(sum(w[i] * rows[i][k] for i in range(I.d)) for k in range(2))


def task(key):
    geom, cost, alpha, gamma, sA, start = key
    I = instance(geom, cost, Fr(alpha), Fr(gamma), Fr(sA), start)
    assert not check_instance(I), check_instance(I)
    VF, wJ, optsJ = solve(I, "F", exact=True)
    bstar, s1bind = stage1(I, True)
    bu, _ = stage1(I, False)
    out = dict(geom=geom, cost=cost, alpha=alpha, gamma=gamma, sA=sA, start=start, VF=str(VF),
               wJ=[str(x) for x in wJ], joint_optima=len(optsJ), bstar=[str(x) for x in bstar],
               bu=[str(x) for x in bu], stage1_binding=s1bind, bind_J=bind(I, wJ), expo_J=[str(x) for x in expo(I, wJ)])
    for name, b, wa in (("2S-lit", bstar, False), ("2S-alpha", bstar, True), ("2S-unc", bu, True)):
        w, opts = stage2(I, b, wa)
        # ties in stage 2: report the worst and best true value over its optimal candidates
        vals = [Q(I, o) for o in opts]
        gstar = sum(SF[k] ** 2 * (expo(I, w)[k] - b[k]) ** 2 for k in range(2))
        # decomposition: Q(w) = f2(w) + L(w) + const, with L(w) = (lam - gamma Sf b*)'(B'w - b*) [+ alpha w_A - c^E w_E if lit]
        Lf = lambda z: (sum((LAM[k] - I.gamma * SF[k] ** 2 * b[k]) * (expo(I, z)[k] - b[k]) for k in range(2))  # noqa: E731
                        + (0 if wa else I.alpha * z[0] - sum(I.cE[j] * z[1 + j] for j in range(I.n))))
        out[name] = dict(w=[str(x) for x in w], candidates=len(opts), gap=str(VF - Q(I, w)),
                         gap_worst=str(VF - min(vals)), gap_best=str(VF - max(vals)),
                         L_term=str(Lf(wJ) - Lf(w)), f2_term=str((VF - Q(I, w)) - (Lf(wJ) - Lf(w))),
                         mismatch=str(I.gamma / 2 * gstar), bind=bind(I, w), expo=[str(x) for x in expo(I, w)],
                         costs_paid=str(tau(I, [w[i] - I.w0[i] for i in range(I.d)])))
    out["costs_paid_J"] = str(tau(I, [wJ[i] - I.w0[i] for i in range(I.d)]))
    return out


def keys():
    return [(g, c, str(a), str(ga), str(s), st) for g, c, a, ga, s, st in
            itertools.product(GEOMETRY, COSTS, ALPHA, GAMMA, SA, STARTS)]


def run():
    t0 = time.time()
    K = keys()
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        rows = pool.map(task, K, chunksize=4)
    (HERE / "results.json").write_text(json.dumps(rows, indent=0))
    print(f"{len(rows)} cells, seconds: {time.time() - t0:.0f}")


def report():
    import statistics
    rows = json.load(open(HERE / "results.json"))
    bp = lambda x: float(Fr(x)) * 1e4  # noqa: E731
    print(f"cells {len(rows)}; 2S-unc identity: max |gap| = {max(abs(bp(r['2S-unc']['gap'])) for r in rows):.3e} bp "
          f"(exactly zero in {sum(Fr(r['2S-unc']['gap']) == 0 for r in rows)}); stage-2 ties (cells with >1 candidate): "
          f"lit {sum(r['2S-lit']['candidates'] > 1 for r in rows)}, alpha {sum(r['2S-alpha']['candidates'] > 1 for r in rows)}; "
          f"cells where tie-breaking changes the gap: {sum(r[m]['gap_worst'] != r[m]['gap_best'] for r in rows for m in ('2S-lit', '2S-alpha'))}")
    print(f"stage-1 target constrained (b_u outside R0) in {sum(r['stage1_binding'] for r in rows)} of {len(rows)}")
    for m in ("2S-lit", "2S-alpha"):
        g = [bp(r[m]["gap"]) for r in rows]
        print(f"\n## {m}: gap V_F - Q(w_2S), bp per quarter (exact)\n")
        print(f"- all: exactly zero {sum(Fr(r[m]['gap']) == 0 for r in rows)}; < 0.01 bp {sum(x < 0.01 for x in g)}; "
              f">= 1 bp {sum(x >= 1 for x in g)}; median {statistics.median(g):.3f}; max {max(g):.3f}")
        for key in ("geom", "cost", "alpha", "gamma", "sA", "start"):
            print(f"**by {key}**")
            for v in sorted({r[key] for r in rows}, key=lambda z: (len(z), z)):
                gv = [bp(r[m]["gap"]) for r in rows if r[key] == v]
                z = sum(1 for r in rows if r[key] == v and Fr(r[m]["gap"]) == 0)
                print(f"- {v}: zero {z}/{len(gv)}; >= 1 bp {sum(x >= 1 for x in gv)}; median {statistics.median(gv):.3f}; max {max(gv):.3f}")
        print("**by stage-1 binding**")
        for sb in (False, True):
            gv = [bp(r[m]["gap"]) for r in rows if r["stage1_binding"] == sb]
            if gv:
                print(f"- stage-1 target {'constrained' if sb else 'interior'}: n {len(gv)}; zero "
                      f"{sum(1 for r in rows if r['stage1_binding'] == sb and Fr(r[m]['gap']) == 0)}; median {statistics.median(gv):.3f}; max {max(gv):.3f}")
        print("**decomposition gap = L_term + f2_term (f2_term <= 0 by stage-2 optimality)**")
        L = [bp(r[m]["L_term"]) for r in rows]; f2 = [bp(r[m]["f2_term"]) for r in rows]
        print(f"- L_term median {statistics.median(L):.3f}, max {max(L):.3f}; f2_term median {statistics.median(f2):.3f}, min {min(f2):.3f}; "
              f"f2_term > 0 in {sum(x > 1e-12 for x in f2)} (must be 0)")
        print("**binding constraints at the two-stage and joint solutions**")
        for lab, f in (("funding", lambda b: b["funding"]), ("long-only", lambda b: bool(b["long_only"])), ("caps", lambda b: bool(b["caps"]))):
            print(f"- {lab}: two-stage {sum(f(r[m]['bind']) for r in rows)}, joint {sum(f(r['bind_J']) for r in rows)}")
        mm = [bp(r[m]["mismatch"]) for r in rows]
        print(f"- exposure mismatch penalty (gamma/2)|B'w - b*|^2_Sf at the two-stage solution: median {statistics.median(mm):.3f} bp, max {max(mm):.3f}")
        print("**equal cells (gap exactly 0)**")
        eq = [r for r in rows if Fr(r[m]["gap"]) == 0]
        for key in ("geom", "cost", "alpha", "start"):
            c = {}
            for r in eq:
                c[r[key]] = c.get(r[key], 0) + 1
            print(f"- {key}: {c}")


if __name__ == "__main__":
    report() if sys.argv[1:] == ["report"] else run()

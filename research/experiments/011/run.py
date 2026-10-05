"""Experiment 011: calibrated M4 certification (D3, proposal section 7.3 for Direction B).
Registered design: experiments/011-m4-calibrated-certification.md.
- Fixture: claims 015-016's geometry. The active fund carries an HML tilt the ETF lacks. Factor means
  and SDs are from experiment 001; all other inputs are assumed.
- The critical value t_{N,eta} is exact: with independent two-point shocks, T_N is a sum of three
  independent (2B-N)^2/N terms, B ~ Binomial(N, 1/2), convolved exactly in integers.
- Certification probabilities are Monte Carlo over the exact sufficient statistics (the three binomial
  counts), with common random numbers. Every decision is evaluated in exact rational arithmetic, using
  experiment 009-010's engine.
"""
from __future__ import annotations

import json
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, isqrt
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "002"))
from m1 import _solve_linear  # noqa: E402

A0, P0, K0 = F(0), F(1, 2), F(1, 2)
KA, KE = F(0), F(0)                                 # set per cost schedule by set_costs()
GAMMA = F(5)
BA, BE = (F(3, 10), F(1)), (F(0), F(1))              # factor 1 = HML (unspanned), factor 2 = Mkt-RF
BOX = ((F(-1, 100), F(3, 100)), (F(0), F(1, 25)), (F(-1, 100), F(1, 100)))
WBAR = (F(1), F(1))


SIG_H, SIG_M = F(1219, 20000), F(427, 5000)              # data: experiment 001, 1963Q3-2025Q2 quarterly SDs
SIG_A, SIG_E = F(1, 50), F(1, 500)                       # assumed: active residual 2%, ETF residual 0.2%


def shocks():
    """16 equiprobable scenarios: independent two-point shocks (+-SD) on HML, Mkt-RF, active and ETF
    residuals. Matches the calibrated variances; the two-point shape and zero correlations are assumed."""
    out = []
    for s1, s2, s3, s4 in product((-1, 1), repeat=4):
        out.append((F(1, 16), (s1 * SIG_H, s2 * SIG_M), s3 * SIG_A, s4 * SIG_E))
    return out


SH = shocks()


def sigma():
    S = [[F(0)] * 2 for _ in range(2)]
    for q, zf, zA, zE in SH:
        x = (BA[0] * zf[0] + BA[1] * zf[1] + zA, BE[0] * zf[0] + BE[1] * zf[1] + zE)
        for i in range(2):
            for j in range(2):
                S[i][j] += q * x[i] * x[j]
    return S


def omega():
    M = [[F(0)] * 3 for _ in range(3)]
    for q, zf, zA, _ in SH:
        v = (zf[0], zf[1], zA)
        for i in range(3):
            for j in range(3):
                M[i][j] += q * v[i] * v[j]
    return M


def inv3(M):
    cols = [_solve_linear([row[:] for row in M], [F(int(i == j)) for i in range(3)], True) for j in range(3)]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


S, OM = sigma(), omega()
OMI = inv3(OM)


def mu(th):
    lam, al = th[:2], th[2]
    return (BA[0] * lam[0] + BA[1] * lam[1] + al, BE[0] * lam[0] + BE[1] * lam[1])


def Q(w, th):
    m = mu(th)
    tau = KA * abs(w[0] - A0) + KE * abs(w[1] - P0)
    quad = sum(w[i] * S[i][j] * w[j] for i in range(2) for j in range(2))
    return m[0] * w[0] + m[1] * w[1] - GAMMA / 2 * quad - tau


def opt(th, cls):
    """Exact global maximizer of Q(.; th) over F or E (sign-piece / active-set enumeration as in
    experiments/004/m2.py), lexicographically smallest among ties."""
    m = mu(th)
    Hs = [[GAMMA * S[i][j] for j in range(2)] for i in range(2)]
    w0, kb, ks = (A0, P0), (KA, KE), (KA, KE)
    opts = [[A0]] if cls == "E" else [[None, F(0), WBAR[0], A0]]
    opts.append([None, F(0), WBAR[1], P0])
    cands = []
    for s in product((1, -1), repeat=2):
        rho = [kb[i] if s[i] == 1 else ks[i] for i in range(2)]
        lin = [m[i] - rho[i] * s[i] for i in range(2)]
        c = [1 + rho[i] * s[i] for i in range(2)]
        for fix in product(*opts):
            Fr_ = [i for i in range(2) if fix[i] is None]
            for beq in ((False, True) if Fr_ else (False,)):
                n = len(Fr_)
                rhs = [lin[i] - sum(Hs[i][j] * fix[j] for j in range(2) if fix[j] is not None) for i in Fr_]
                if beq:
                    A = [[Hs[Fr_[a]][Fr_[b]] for b in range(n)] + [c[Fr_[a]]] for a in range(n)]
                    A.append([c[Fr_[b]] for b in range(n)] + [F(0)])
                    br = K0 + sum(c[i] * w0[i] for i in range(2)) - sum(c[j] * fix[j] for j in range(2) if fix[j] is not None)
                    sol = _solve_linear(A, rhs + [br], True)
                else:
                    A = [[Hs[Fr_[a]][Fr_[b]] for b in range(n)] for a in range(n)]
                    sol = _solve_linear(A, rhs, True) if n else []
                if sol is None:
                    continue
                w = [fix[i] for i in range(2)]
                for a_, i in enumerate(Fr_):
                    w[i] = sol[a_]
                if any(s[i] * (w[i] - w0[i]) < 0 for i in range(2)):
                    continue
                if any(w[i] < 0 or w[i] > WBAR[i] for i in range(2)):
                    continue
                v = [w[i] - w0[i] for i in range(2)]
                if K0 - sum(v) - sum(kb[i] * max(v[i], 0) + ks[i] * max(-v[i], 0) for i in range(2)) < 0:
                    continue
                cands.append(tuple(w))
    best = max(Q(w, th) for w in cands)
    return min(w for w in cands if Q(w, th) == best)


_optE = {}


def optE(th):
    if th not in _optE:
        _optE[th] = opt(th, "E")
    return _optE[th]


def supE(th):
    return Q(optE(th), th)




LAM_STAR = (F(897, 100000), F(23, 1250))                 # data: HML 0.897%, Mkt-RF 1.840% per quarter
COSTS = {"zero": (F(0), F(0)), "equal 5 bp": (F(5, 10000), F(5, 10000))}   # assumed


def set_costs(name):
    global KA, KE
    KA, KE = COSTS[name]
    _optE.clear()


def G_star(th):
    return Q(opt(th, "F"), th) - supE(th)


def alpha_for_gap(target, lo=F(-1, 100), hi=F(1, 100), steps=60):
    """Smallest alpha with G_* >= target at LAM_STAR (G_* is nondecreasing in alpha here)."""
    for _ in range(steps):
        m = (lo + hi) / 2
        if G_star(LAM_STAR + (m,)) >= target:
            hi = m
        else:
            lo = m
    return hi


def quantile_T(N, eta):
    """Exact 1-eta quantile of T_N = sum_k (2B_k - N)^2 / N over three independent Binomial(N, 1/2)."""
    one = defaultdict(int)
    for b in range(N + 1):
        one[(2 * b - N) ** 2] += comb(N, b)
    dist = {0: 1}
    for _ in range(3):
        nxt = defaultdict(int)
        for x, wx in dist.items():
            for y, wy in one.items():
                nxt[x + y] += wx * wy
        dist = nxt
    total = 2 ** (3 * N)
    acc = 0
    for x in sorted(dist):
        acc += dist[x]
        if F(acc, total) >= 1 - eta:
            return F(x, N)


def ub_sqrt(x):
    return F(isqrt(-(-x.numerator * 10 ** 16 // x.denominator)) + 1, 10 ** 8)


def min_T_over_domain(th_hat, N):
    """Omega is diagonal: min over the box of N sum_k (th_hat_k - th_k)^2 / Omega_kk is separable."""
    tot = F(0)
    for k in range(3):
        c = min(max(th_hat[k], BOX[k][0]), BOX[k][1])
        tot += N * (th_hat[k] - c) ** 2 / OM[k][k]
    return tot


def decide(th_star, B, N, etas, ts, rs, delta):
    e = (SIG_H * F(2 * B[0] - N, N), SIG_M * F(2 * B[1] - N, N), SIG_A * F(2 * B[2] - N, N))
    th_hat = tuple(th_star[i] + e[i] for i in range(3))
    w_hat, v_hat = opt(th_hat, "F"), opt(th_hat, "E")
    sup_star = supE(th_star)
    advF, advE = Q(w_hat, th_star) - sup_star, Q(v_hat, th_star) - sup_star
    T = sum(N * e[k] ** 2 / OM[k][k] for k in range(3))
    tmin = min_T_over_domain(th_hat, N)
    out = {}
    for eta in etas:
        nonempty = tmin <= ts[eta]
        box = [(max(BOX[i][0], th_hat[i] - rs[eta][i]), min(BOX[i][1], th_hat[i] + rs[eta][i])) for i in range(3)]
        cert = False
        if nonempty and w_hat[0] != A0 and all(lo <= hi for lo, hi in box):
            ell = min(Q(w_hat, v) - supE(v) for v in product(*box))
            cert = ell > delta
        out[eta] = dict(cert=cert, false=cert and advF <= delta, advF=advF, advE=advE,
                        covered=T <= ts[eta], empty=not nonempty)
    return out


def cp_upper(k, n, conf=0.95):
    """Clopper-Pearson upper bound by bisection on the binomial tail (exact enough for reporting)."""
    if k == n:
        return 1.0
    lo, hi = k / n, 1.0
    for _ in range(60):
        p = (lo + hi) / 2
        tail = sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k + 1))
        if tail > 1 - conf:
            lo = p
        else:
            hi = p
    return hi


def claim_bounds(delta, eps):
    """Claim 015 and 016 history-length bounds (quarters) at calibrated inputs; constants are loose."""
    D, Hh = BA[0] * 1, SIG_H                              # D = HML exposure mismatch at A = 1; H = |Z| bound
    r = float(D * Hh / delta) ** 2
    c15 = (r * math.log(1 / eps) / (4 * math.pi ** 2), 32 * r * math.log(2 / eps))
    o11, o22, o33 = float(SIG_H ** 2), float(SIG_M ** 2), float(SIG_A ** 2)
    s2 = max(o11 + o33, o11 + o22 + o33)                  # claim 016's d_0, d_1 with a diagonal Omega
    q = s2 / float(delta) ** 2
    c16 = (q * math.log(1 / eps) / (16 * math.pi ** 2), 192 * q * math.log(6 / eps))
    return c15, c16


NS, ETAS, DELTA = [40, 80, 160], [F(1, 20), F(1, 4)], F(0)
GAPS_BP = [2, 5, 10, 25]
R0, R_MAX = 2000, 8000                                   # replications; null cells extend to R_MAX if needed
GRID = F(1, 10 ** 6)


def alpha_grid():
    """Per cost schedule: two null points (G_* = 0) and four alternatives with G_* at least 2, 5, 10, 25 bp."""
    thr = alpha_for_gap(F(1, 10 ** 12))
    down = (thr // GRID) * GRID - GRID                    # just below the zero-gap threshold
    nulls = [down - F(1, 1000), down]
    alts = []
    for g in GAPS_BP:
        a = alpha_for_gap(F(g, 10000))
        alts.append(-((-a) // GRID) * GRID)               # round up to the 1e-6 grid, so G_* >= target
    return nulls, alts


def run_cell(th_star, N, ts, rs, G, reps_start, reps_end, acc):
    for r in range(reps_start, reps_end):
        rng = np.random.default_rng([2011, N, r])        # common random numbers across alpha, costs and eta
        B = [int(x) for x in rng.binomial(N, 0.5, size=3)]
        d = decide(th_star, B, N, ETAS, ts, rs, DELTA)
        for eta, o in d.items():
            a = acc[eta]
            a["n"] += 1
            a["cert"].append(o["cert"])
            a["false"] += o["false"]
            a["cov"] += o["covered"]
            a["empty"] += o["empty"]
            a["missed"].append(float(G) if (not o["cert"] and G > DELTA) else 0.0)
            a["short"].append(float(-o["advE"]) if not o["cert"] else 0.0)
            a["advimp"].append(float(o["advF"] if o["cert"] else o["advE"]))


def main() -> None:
    t0 = time.time()
    rows = []
    for cname in COSTS:
        set_costs(cname)
        nulls, alts = alpha_grid()
        for astar in nulls + alts:
            th_star = LAM_STAR + (astar,)
            G = G_star(th_star)
            for N in NS:
                ts = {eta: quantile_T(N, eta) for eta in ETAS}
                rs = {eta: [ub_sqrt(ts[eta] * OM[i][i] / N) for i in range(3)] for eta in ETAS}
                acc = {eta: dict(n=0, cert=[], false=0, cov=0, empty=0, missed=[], short=[], advimp=[]) for eta in ETAS}
                run_cell(th_star, N, ts, rs, G, 0, R0, acc)
                if G <= DELTA:                             # null cell: precision rule on false certification
                    while any(cp_upper(acc[e]["false"], acc[e]["n"]) >= float(e) and acc[e]["false"] / acc[e]["n"] < float(e)
                              for e in ETAS) and acc[ETAS[0]]["n"] < R_MAX:
                        n = acc[ETAS[0]]["n"]
                        run_cell(th_star, N, ts, rs, G, n, min(n + R0, R_MAX), acc)
                for eta in ETAS:
                    a = acc[eta]
                    n = a["n"]
                    m = lambda v: (float(np.mean(v)), float(np.std(v, ddof=1) / math.sqrt(n)))  # noqa: E731
                    rows.append(dict(costs=cname, alpha=str(astar), G_bp=float(G) * 1e4, N=N, years=N / 4, eta=str(eta),
                                     R=n, t=str(ts[eta]), coverage=a["cov"] / n, empty=a["empty"] / n,
                                     certify=m([float(x) for x in a["cert"]]), false=a["false"] / n,
                                     false_cp95=cp_upper(a["false"], n), missed_bp=tuple(x * 1e4 for x in m(a["missed"])),
                                     shortfall_bp=tuple(x * 1e4 for x in m(a["short"])),
                                     adv_implemented_bp=tuple(x * 1e4 for x in m(a["advimp"]))))
    print("### Calibrated M4 gate (valid vertex lower bound), Monte Carlo over exact sufficient statistics\n")
    print("| costs | alpha_* | G_* (bp/q) | years | eta | R | coverage | P(empty) | P(certify) (SE) | P(false cert) [CP95 upper] | "
          "missed gain bp (SE) | fallback shortfall bp (SE) | E[Adv impl.] bp (SE) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['costs']} | {r['alpha']} | {r['G_bp']:.3f} | {r['years']:.0f} | {r['eta']} | {r['R']} | {r['coverage']:.4f} | "
              f"{r['empty']:.4f} | {r['certify'][0]:.4f} ({r['certify'][1]:.4f}) | {r['false']:.4f} [{r['false_cp95']:.4f}] | "
              f"{r['missed_bp'][0]:.3f} ({r['missed_bp'][1]:.3f}) | {r['shortfall_bp'][0]:.3f} ({r['shortfall_bp'][1]:.3f}) | "
              f"{r['adv_implemented_bp'][0]:.3f} ({r['adv_implemented_bp'][1]:.3f}) |")
    bad = [r for r in rows if r["false"] > float(F(r["eta"]))]
    print(f"\nCells with estimated P(false cert) > eta: {len(bad)}. Null cells whose CP95 upper bound is >= eta: "
          f"{sum(1 for r in rows if r['G_bp'] == 0 and r['false_cp95'] >= float(F(r['eta'])))}.")
    print("\n### Claims 015 and 016: history-length bounds at the calibrated inputs (quarters, and years), eps = 1/20\n")
    print("Constants are loose; claim 016 is evaluated outside its stated range ||J|| <= 1/100, as order of magnitude only.\n")
    print("| delta (bp/q) | claim 015 necessary | claim 015 sufficient | claim 016 necessary | claim 016 sufficient |")
    print("|---|---|---|---|---|")
    for g in GAPS_BP:
        (l15, u15), (l16, u16) = claim_bounds(F(g, 10000), F(1, 20))
        print(f"| {g} | {l15:,.0f} q ({l15 / 4:,.0f} y) | {u15:,.0f} q ({u15 / 4:,.0f} y) | {l16:,.0f} q ({l16 / 4:,.0f} y) | "
              f"{u16:,.0f} q ({u16 / 4:,.0f} y) |")
    (HERE / "results.json").write_text(json.dumps(rows, indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

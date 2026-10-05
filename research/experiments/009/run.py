"""Experiment 009: M4 certification gate, exact repeated-sampling measurement.
Registered design: experiments/009-m4-certificate-gate.md. Exact rational arithmetic throughout; every
probability is an exact sum over the finite sampling law (multinomial count vectors), so no Monte Carlo
error enters. Prints Markdown and writes experiments/009/results.json.
"""
from __future__ import annotations

import json
import sys
import time
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "002"))
from m1 import _solve_linear  # noqa: E402  exact Gaussian elimination (reused helper)

# =====================================================================================================
# Part X: claim 014's laws I and R (one active fund, one ETF, only alpha unknown)
# =====================================================================================================
H, MU = F(1, 10), F(1, 80)
BE014 = F(13, 1600)                                      # Adv(w_A; alpha) = alpha - 13/1600


def score014(w, alpha):
    a, p = w
    return a * alpha + p / 80 - a * a / 200 - p * p / 80


def cand014(alpha_hat):
    """Plug-in F optimum on the funded triangle a, p >= 0, a + p <= 1 (lexicographically smallest)."""
    clip = lambda a: max(F(0), min(F(1), a))  # noqa: E731
    ba = clip((alpha_hat + MU) / F(7, 200))
    cs = {(F(0), F(1, 2)), (clip(100 * alpha_hat), F(0)), (ba, 1 - ba), (F(0), F(0))}
    it = (100 * alpha_hat, F(1, 2))
    if it[0] >= 0 and sum(it) <= 1:
        cs.add(it)
    best = max(score014(w, alpha_hat) for w in cs)
    return min(w for w in cs if score014(w, alpha_hat) == best)


def part_x(etas, Ns, alphas):
    """M4 gate under law I or R: alpha_hat = alpha_* + H * mean(signs), identical in both laws."""
    rows = []
    for eta, N, astar in product(etas, Ns, alphas):
        err = defaultdict(F)
        for k in range(N + 1):                           # k positive signs among N
            err[H * F(2 * k - N, N)] += F(factorial(N), factorial(k) * factorial(N - k)) / 2 ** N
        stat = defaultdict(F)
        for e, m in err.items():
            stat[N * e * e / (H * H)] += m
        acc = F(0)
        for t in sorted(stat):
            acc += stat[t]
            if acc >= 1 - eta:
                break
        radius = max(abs(e) for e in err if N * e * e / (H * H) <= t)
        G = score014(cand014(astar), astar) - F(1, 320)      # sup_F - sup_E at theta_* (sup_E = 1/320)
        cert = false = cov = empty = F(0)
        for e, m in err.items():
            ah = astar + e
            lo, hi = max(-H, ah - radius), min(H, ah + radius)
            w = cand014(ah)
            cov += m * (N * e * e / (H * H) <= t)
            if lo > hi:
                empty += m
                continue
            ell = score014(w, lo) - F(1, 320)            # Adv is nondecreasing in alpha when a >= 0
            c = w[0] > 0 and ell > 0
            cert += m * c
            false += m * (c and score014(w, astar) - F(1, 320) <= 0)
        bench_I = min(F(1), 1 - F(1, 2 ** N) + eta)
        rows.append(dict(eta=eta, N=N, alpha=astar, t=t, coverage=cov, empty=empty, certify=cert,
                         false_cert=false, G=G, bench_I=bench_I, bench_R=F(1)))
    return rows


def np_power(N, eta, kind):
    """Independent check of claim 014's benchmark at theta_+: most powerful test of theta_- vs theta_+
    on the full public history (Neyman-Pearson with randomization), exact, small N only."""
    def atoms(alpha):
        out = defaultdict(F)
        for s, t_, u in product((-1, 1), repeat=3):
            ze = F(t_ * (3 - (u if kind == "I" else s)), 20)
            out[(alpha + H * s, MU + ze)] += F(1, 8)
        return out
    def hist(alpha):
        law = {(): F(1)}
        a = atoms(alpha)
        for _ in range(N):
            nxt = defaultdict(F)
            for h, m in law.items():
                for o, p in a.items():
                    nxt[h + (o,)] += m * p
            law = nxt
        return law
    null, alt = hist(-H), hist(H)
    power = sum(p for h, p in alt.items() if null.get(h, 0) == 0)
    budget = eta
    for _, c, b in sorted(((p / null[h], null[h], p) for h, p in alt.items() if null.get(h, 0) > 0), reverse=True):
        pr = min(F(1), budget / c)
        power += pr * b
        budget -= pr * c
    return power


# =====================================================================================================
# Part Y: red's M4 fixture (checks/red-m4-definition/check.py, Part B economics, nonsingular Omega)
# =====================================================================================================
A0, P0, K0 = F(3, 10), F(1, 2), F(1, 5)
KA, KE = F(1, 500), F(1, 2000)
GAMMA = F(2)
BA, BE = (F(1), F(1, 2)), (F(1), F(0))
BOX = ((F(1, 100), F(3, 100)), (F(0), F(1, 50)), (F(-1, 20), F(1, 10)))
WBAR = (F(1), F(1))


def shocks():
    out = []
    for s1, s2, s3 in product((-1, 1), repeat=3):
        zf = (F(3, 50) * s1 / 10, F(1, 50) * s2 / 10)
        zA = (F(1, 50) * s3 + F(1, 100) * s1) / 10
        out.append((F(1, 8), zf, zA, F(1, 200) * s2 / 10))
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


_supE = {}


def supE(th):
    if th not in _supE:
        _supE[th] = Q(opt(th, "E"), th)
    return _supE[th]


def count_law(N):
    """Exact law of e_N (sample-mean error) over multinomial count vectors of the 8 scenarios."""
    zs = [(zf[0], zf[1], zA) for _, zf, zA, _ in SH]
    k = len(zs)
    out = []
    for cut in combinations(range(N + k - 1), k - 1):
        counts = [b - a - 1 for a, b in zip((-1,) + cut, cut + (N + k - 1,))]
        mass = F(factorial(N))
        for c in counts:
            mass = mass / factorial(c) / F(8) ** c
        e = tuple(sum(c * z[i] for c, z in zip(counts, zs)) / N for i in range(3))
        out.append((mass, e))
    assert sum(m for m, _ in out) == 1
    return out


def Tstat(e, N):
    return N * sum(e[i] * OMI[i][j] * e[j] for i in range(3) for j in range(3))


def quantile(law, N, eta):
    T = defaultdict(F)
    for m, e in law:
        T[Tstat(e, N)] += m
    acc = F(0)
    for t in sorted(T):
        acc += T[t]
        if acc >= 1 - eta:
            return t


def ub_sqrt(x):
    """Rational upper bound on sqrt(x), within 1e-8."""
    return F(isqrt(-(-x.numerator * 10 ** 16 // x.denominator)) + 1, 10 ** 8)


def min_T_over_domain(th_hat, N):
    """Exact min over theta in Theta_4 (a box) of N (th_hat - theta)' Omega^-1 (th_hat - theta):
    enumerate each coordinate free / at its lower bound / at its upper bound; solve the free block."""
    A = [[N * OMI[i][j] for j in range(3)] for i in range(3)]
    best = None
    for choice in product((None, 0, 1), repeat=3):
        fix = [None if c is None else BOX[i][c] for i, c in enumerate(choice)]
        free = [i for i in range(3) if fix[i] is None]
        th = list(fix)
        if free:
            M = [[A[i][j] for j in free] for i in free]
            rhs = [sum(A[i][j] * th_hat[j] for j in free) - sum(A[i][j] * (fix[j] - th_hat[j]) for j in range(3) if fix[j] is not None)
                   for i in free]
            sol = _solve_linear(M, rhs, True)
            if sol is None:
                continue
            for a_, i in enumerate(free):
                th[i] = sol[a_]
        if any(not (BOX[i][0] <= th[i] <= BOX[i][1]) for i in range(3)):
            continue
        d = [th_hat[i] - th[i] for i in range(3)]
        val = sum(d[i] * A[i][j] * d[j] for i in range(3) for j in range(3))
        best = val if best is None or val < best else best
    return best


def part_y(alphas, Ns, etas, delta, lam):
    rows = []
    for astar, N in product(alphas, Ns):
        th_star = lam + (astar,)
        wF_star = opt(th_star, "F")
        G = Q(wF_star, th_star) - supE(th_star)
        law = count_law(N)
        ts = {eta: quantile(law, N, eta) for eta in etas}
        rs = {eta: [ub_sqrt(ts[eta] * OM[i][i] / N) for i in range(3)] for eta in etas}
        acc = {(eta, rule): defaultdict(F) for eta in etas for rule in ("valid", "weak", "plugin")}
        cov = {eta: F(0) for eta in etas}
        empt = {eta: F(0) for eta in etas}
        for m, e in law:
            th_hat = tuple(th_star[i] + e[i] for i in range(3))
            w_hat = opt(th_hat, "F")
            v_hat = opt(th_hat, "E")
            advF = Q(w_hat, th_star) - supE(th_star)
            advE = Q(v_hat, th_star) - supE(th_star)
            T = Tstat(e, N)
            tmin = min_T_over_domain(th_hat, N)
            plug = Q(w_hat, th_hat) - supE(th_hat)
            for eta in etas:
                cov[eta] += m * (T <= ts[eta])
                nonempty = tmin is not None and tmin <= ts[eta]
                empt[eta] += m * (not nonempty)
                box = [(max(BOX[i][0], th_hat[i] - rs[eta][i]), min(BOX[i][1], th_hat[i] + rs[eta][i])) for i in range(3)]
                trades = w_hat[0] != A0
                if nonempty and all(lo <= hi for lo, hi in box):
                    verts = list(product(*box))
                    ell = min(Q(w_hat, v) - supE(v) for v in verts)
                    ellw = min(Q(w_hat, v) - Q(v_hat, v) for v in verts)
                else:
                    ell = ellw = None
                certs = {"valid": nonempty and trades and ell is not None and ell > delta,
                         "weak": nonempty and trades and ellw is not None and ellw > delta,
                         "plugin": trades and plug > delta}
                for rule, c in certs.items():
                    a = acc[(eta, rule)]
                    a["certify"] += m * c
                    a["false_cert"] += m * (c and advF <= delta)
                    a["adv_implemented"] += m * (advF if c else advE)
                    a["missed_gain"] += m * (G if (not c and G > delta) else 0)
                    a["fallback_shortfall"] += m * (-advE if not c else 0)
        for eta in etas:
            for rule in ("valid", "weak", "plugin"):
                a = acc[(eta, rule)]
                rows.append(dict(alpha=astar, N=N, eta=eta, rule=rule, G=G, t=ts[eta], coverage=cov[eta],
                                 empty=empt[eta], **{k: a[k] for k in ("certify", "false_cert", "adv_implemented",
                                                                       "missed_gain", "fallback_shortfall")}))
    return rows


def checks_y(lam, alphas):
    pos = all(1 + BA[0] * v[0] + BA[1] * v[1] + v[2] + BA[0] * zf[0] + BA[1] * zf[1] + zA > 0 and
              1 + BE[0] * v[0] + BE[1] * v[1] + BE[0] * zf[0] + BE[1] * zf[1] + zE > 0
              for v in product(*BOX) for _, zf, zA, zE in SH)
    det = OM[0][0] * (OM[1][1] * OM[2][2] - OM[1][2] * OM[2][1]) - OM[0][1] * (OM[1][0] * OM[2][2] - OM[1][2] * OM[2][0]) \
        + OM[0][2] * (OM[1][0] * OM[2][1] - OM[1][1] * OM[2][0])
    inside = all(BOX[i][0] <= (lam + (a,))[i] <= BOX[i][1] for a in alphas for i in range(3))
    return dict(positive_returns_at_vertices=pos, Omega_det=str(det), Omega_nonsingular=det != 0,
                theta_star_in_domain=inside, cross_cov_factor1_alpha=str(OM[0][2]))


# =====================================================================================================
def fmt(x):
    return f"{float(x):.4f}"


def main() -> None:
    t0 = time.time()
    # ---------------- Part X
    X_ETAS, X_NS = [F(1, 16), F(1, 4)], list(range(1, 11))
    X_ALPHAS = [-H, -H / 2, F(0), BE014, F(1, 40), H]
    xr = part_x(X_ETAS, X_NS, X_ALPHAS)
    npcheck = {(kind, N, str(eta)): np_power(N, eta, kind) for kind in ("I", "R") for N in (1, 2, 3) for eta in X_ETAS}
    np_ok = all(v == (min(F(1), 1 - F(1, 2 ** N) + F(eta)) if kind == "I" else F(1))
                for (kind, N, eta), v in npcheck.items())
    print("### Part X: claim 014 laws I and R (the M4 gate is identical in both)\n")
    print(f"Independent Neyman-Pearson check of claim 014's benchmark formula at N = 1, 2, 3: {np_ok}\n")
    print("| eta | N_obs | gate P(certify) at theta_+ | benchmark I | benchmark R | gate / benchmark I | "
          "max P(false cert) over alpha grid | coverage | P(empty C_N) at theta_+ |")
    print("|---|---|---|---|---|---|---|---|---|")
    for eta, N in product(X_ETAS, X_NS):
        rs = [r for r in xr if r["eta"] == eta and r["N"] == N]
        rp = next(r for r in rs if r["alpha"] == H)
        mf = max(r["false_cert"] for r in rs)
        print(f"| {eta} | {N} | {fmt(rp['certify'])} | {fmt(rp['bench_I'])} | 1 | {fmt(rp['certify'] / rp['bench_I'])} | "
              f"{fmt(mf)} | {fmt(rp['coverage'])} | {fmt(rp['empty'])} |")
    # ---------------- Part Y
    LAM = (F(1, 50), F(1, 100))
    Y_ALPHAS = [F(-1, 20), F(-1, 100), F(0), F(1, 100), F(1, 40), F(1, 20), F(1, 10)]
    Y_NS, Y_ETAS, DELTA = [2, 4, 6, 8], [F(1, 20), F(1, 4)], F(0)
    ck = checks_y(LAM, Y_ALPHAS)
    yr = part_y(Y_ALPHAS, Y_NS, Y_ETAS, DELTA, LAM)
    print("\n### Part Y: red's M4 fixture (nonsingular Omega, one ETF), exact over all count vectors\n")
    print(f"Checks: {ck}\n")
    print("| rule | eta | alpha_* | G_* (bp) | N_obs | coverage | P(empty) | P(certify) | P(false cert) | "
          "E[Adv implemented] (bp) | missed gain (bp) | fallback shortfall (bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in yr:
        print(f"| {r['rule']} | {r['eta']} | {r['alpha']} | {float(r['G']) * 1e4:.3f} | {r['N']} | {fmt(r['coverage'])} | "
              f"{fmt(r['empty'])} | {fmt(r['certify'])} | {fmt(r['false_cert'])} | {float(r['adv_implemented']) * 1e4:.3f} | "
              f"{float(r['missed_gain']) * 1e4:.3f} | {float(r['fallback_shortfall']) * 1e4:.3f} |")
    # Deviation 1 (post hoc, supplementary): alpha_* inside the no-active-trade band, where G_* = 0.
    SUPP_ALPHAS = [F(-3, 400), F(-11, 2000), F(-7, 2000)]
    sr = part_y(SUPP_ALPHAS, Y_NS, Y_ETAS, DELTA, LAM)
    print("\n#### Supplementary cells (Deviation 1): alpha_* inside the no-active-trade band (G_* = 0)\n")
    print("| rule | eta | alpha_* | G_* (bp) | N_obs | coverage | P(empty) | P(certify) | P(false cert) | "
          "E[Adv implemented] (bp) | missed gain (bp) | fallback shortfall (bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in sr:
        print(f"| {r['rule']} | {r['eta']} | {r['alpha']} | {float(r['G']) * 1e4:.3f} | {r['N']} | {fmt(r['coverage'])} | "
              f"{fmt(r['empty'])} | {fmt(r['certify'])} | {fmt(r['false_cert'])} | {float(r['adv_implemented']) * 1e4:.3f} | "
              f"{float(r['missed_gain']) * 1e4:.3f} | {float(r['fallback_shortfall']) * 1e4:.3f} |")
    yr_all = yr + sr
    viol = [r for r in yr_all if r["rule"] == "valid" and r["false_cert"] > r["eta"]]
    cov_bad = [r for r in yr_all if r["coverage"] < 1 - r["eta"]]
    plug_over = [r for r in yr_all if r["rule"] == "plugin" and r["false_cert"] > r["eta"]]
    weak_over = [r for r in yr_all if r["rule"] == "weak" and r["false_cert"] > r["eta"]]
    print(f"\nValid gate: cells with P(false cert) > eta: {len(viol)}. Cells with coverage < 1 - eta: {len(cov_bad)}. "
          f"Plug-in rule: cells with P(false cert) > eta: {len(plug_over)} of {sum(r['rule'] == 'plugin' for r in yr_all)}. "
          f"Weaker target: cells with P(false cert) > eta: {len(weak_over)}. (Registered and supplementary cells.)")
    ser = lambda o: {k: (str(v) if isinstance(v, F) else v) for k, v in o.items()}  # noqa: E731
    (HERE / "results.json").write_text(json.dumps(dict(part_x=[ser(r) for r in xr], np_check={str(k): str(v) for k, v in npcheck.items()},
                                                       part_y_checks=ck, part_y=[ser(r) for r in yr], part_y_supplementary=[ser(r) for r in sr]), indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

"""Experiment 010: M4 certification with a moving ETF comparator (follow-up to experiment 009).
Registered design: experiments/010-m4-moving-comparator.md. Exact rational arithmetic; every probability
is an exact sum over multinomial count vectors (no Monte Carlo). Prints Markdown; writes results.json.
The engine is experiment 009's Part Y code, with the fixture constants changed and the parameter domain
passed explicitly (alpha-uncertain domain, or alpha known at alpha_*).
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
from m1 import _solve_linear  # noqa: E402

# =====================================================================================================
# Fixture: experiment 009's shock law and instruments; incumbent (3/10, 3/10, 2/5), gamma = 400, smaller domain
# =====================================================================================================
A0, P0, K0 = F(3, 10), F(3, 10), F(2, 5)
KA, KE = F(1, 500), F(1, 2000)
GAMMA = F(400)
BA, BE = (F(1), F(1, 2)), (F(1), F(0))
BOX = ((F(1, 100), F(1, 50)), (F(0), F(1, 50)), (F(-1, 100), F(1, 100)))
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


_optE = {}


def optE(th):
    if th not in _optE:
        _optE[th] = opt(th, "E")
    return _optE[th]


def supE(th):
    return Q(optE(th), th)


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


def min_T_over_domain(th_hat, N, dom):
    """Exact min over theta in Theta_4 (a box) of N (th_hat - theta)' Omega^-1 (th_hat - theta):
    enumerate each coordinate free / at its lower bound / at its upper bound; solve the free block."""
    A = [[N * OMI[i][j] for j in range(3)] for i in range(3)]
    best = None
    for choice in product((None, 0, 1), repeat=3):
        fix = [None if c is None else dom[i][c] for i, c in enumerate(choice)]
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
        if any(not (dom[i][0] <= th[i] <= dom[i][1]) for i in range(3)):
            continue
        d = [th_hat[i] - th[i] for i in range(3)]
        val = sum(d[i] * A[i][j] * d[j] for i in range(3) for j in range(3))
        best = val if best is None or val < best else best
    return best


def part_y(alphas, Ns, etas, delta, lam, domain_kind):
    rows = []
    for astar, N in product(alphas, Ns):
        th_star = lam + (astar,)
        dom = BOX if domain_kind == "alpha uncertain" else (BOX[0], BOX[1], (astar, astar))
        wF_star = opt(th_star, "F")
        vE_star = opt(th_star, "E")
        G = Q(wF_star, th_star) - supE(th_star)
        law = count_law(N)
        ts = {eta: quantile(law, N, eta) for eta in etas}
        rs = {eta: [ub_sqrt(ts[eta] * OM[i][i] / N) for i in range(3)] for eta in etas}
        acc = {(eta, rule): defaultdict(F) for eta in etas for rule in ("valid", "weak", "plugin")}
        extra = {eta: defaultdict(F) for eta in etas}
        for m, e in law:
            th_hat = tuple(th_star[i] + e[i] for i in range(3))
            w_hat = opt(th_hat, "F")
            v_hat = opt(th_hat, "E")
            advF = Q(w_hat, th_star) - supE(th_star)
            advE = Q(v_hat, th_star) - supE(th_star)
            T = Tstat(e, N)
            tmin = min_T_over_domain(th_hat, N, dom)
            plug = Q(w_hat, th_hat) - supE(th_hat)
            for eta in etas:
                x = extra[eta]
                x["coverage"] += m * (T <= ts[eta])
                nonempty = tmin is not None and tmin <= ts[eta]
                x["empty"] += m * (not nonempty)
                x["comparator_moves"] += m * (v_hat != vE_star)
                box = [(max(dom[i][0], th_hat[i] - rs[eta][i]), min(dom[i][1], th_hat[i] + rs[eta][i])) for i in range(3)]
                trades = w_hat[0] != A0
                if nonempty and all(lo <= hi for lo, hi in box):
                    verts = list(product(*box))
                    ell = min(Q(w_hat, v) - supE(v) for v in verts)
                    ellw = min(Q(w_hat, v) - Q(v_hat, v) for v in verts)
                    x["E_opt_varies_on_box"] += m * (len({optE(v) for v in verts}) > 1)
                else:
                    ell = ellw = None
                certs = {"valid": nonempty and trades and ell is not None and ell > delta,
                         "weak": nonempty and trades and ellw is not None and ellw > delta,
                         "plugin": trades and plug > delta}
                x["weak_differs_from_valid"] += m * (certs["weak"] != certs["valid"])
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
                rows.append(dict(domain=domain_kind, alpha=astar, N=N, eta=eta, rule=rule, G=G, t=ts[eta],
                                 **{k: extra[eta][k] for k in ("coverage", "empty", "comparator_moves",
                                                                "E_opt_varies_on_box", "weak_differs_from_valid")},
                                 **{k: a[k] for k in ("certify", "false_cert", "adv_implemented", "missed_gain",
                                                      "fallback_shortfall")}))
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


def fmt(x):
    return f"{float(x):.4f}"


def main() -> None:
    t0 = time.time()
    LAM = (F(1, 80), F(1, 100))
    NULL = [F(-49, 10000), F(-29, 10000), F(-1, 1000)]          # inside the no-active-trade band (G_* = 0)
    ALT = [F(-1, 125), F(1, 500), F(3, 500)]                    # outside it
    NS, ETAS, DELTA = [2, 4, 6, 8], [F(1, 20), F(1, 4)], F(0)
    ck = checks_y(LAM, NULL + ALT)
    ck["E_optimum_distinct_values_at_domain_vertices"] = len({opt(v, "E") for v in product(*BOX)})
    rows = []
    for kind in ("alpha uncertain", "alpha known"):
        rows += part_y(NULL + ALT, NS, ETAS, DELTA, LAM, kind)
    print(f"### Fixture checks\n\n{ck}\n")
    print("| domain | rule | eta | alpha_* | G_* (bp) | N | coverage | P(empty) | P(v_hat_E != oracle E) | "
          "P(E optimum varies on the cert. box) | P(weak != valid) | P(certify) | P(false cert) | "
          "E[Adv impl.] (bp) | missed gain (bp) | fallback shortfall (bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['domain']} | {r['rule']} | {r['eta']} | {r['alpha']} | {float(r['G']) * 1e4:.3f} | {r['N']} | "
              f"{fmt(r['coverage'])} | {fmt(r['empty'])} | {fmt(r['comparator_moves'])} | {fmt(r['E_opt_varies_on_box'])} | "
              f"{fmt(r['weak_differs_from_valid'])} | {fmt(r['certify'])} | {fmt(r['false_cert'])} | "
              f"{float(r['adv_implemented']) * 1e4:.3f} | {float(r['missed_gain']) * 1e4:.3f} | "
              f"{float(r['fallback_shortfall']) * 1e4:.3f} |")
    for rule in ("valid", "weak", "plugin"):
        over = [r for r in rows if r["rule"] == rule and r["false_cert"] > r["eta"]]
        print(f"\n{rule}: cells with P(false cert) > eta: {len(over)} of {sum(r['rule'] == rule for r in rows)}")
    cov_bad = [r for r in rows if r["rule"] == "valid" and r["coverage"] < 1 - r["eta"]]
    print(f"cells with coverage < 1 - eta: {len(cov_bad)}")
    ser = lambda o: {k: (str(v) if isinstance(v, F) else v) for k, v in o.items()}  # noqa: E731
    (HERE / "results.json").write_text(json.dumps(dict(checks={k: str(v) for k, v in ck.items()},
                                                       rows=[ser(r) for r in rows]), indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

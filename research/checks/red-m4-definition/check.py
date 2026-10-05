"""Red's review of the proposed M4 definition (model/SPEC.md, M4): exact attacks, not a claim.

Run: uv run python checks/red-m4-definition/check.py

Everything is exact rational arithmetic on the full finite sampling law. Histories are enumerated
by multinomial count vectors, since the sample mean depends only on the counts.

Part A, calibration and coverage: for a nonsingular Omega, a singular Omega (active residual
collinear with the first factor shock) and Omega = 0, compute the finite quantile t_{N,eta} as SPEC
defines it. Then check:
- every positive-mass zeta_s lies in Im(Omega);
- exact coverage P(T_N <= t) >= 1 - eta, independent of theta_*;
- a zero-mass scenario outside Im(Omega) never enters;
- Omega = 0 gives C_N = {theta_*}.

Part B, certificate direction and the uniform implication, end to end. Setup: one ETF, shocks scaled by
1/10, Theta_4 a box, true alphas bracketing the exact break-even alpha of a data-selected funded
candidate, and delta_econ = 0. Use a valid lower bound. D(theta) = Q(w;theta) - sup_E Q(v;theta)
is concave in theta, and C_N lies in the box theta_hat +- r intersected with Theta_4, where
r_i >= sqrt(t Omega_ii / N_obs). So the minimum of D over that box's vertices (sup_E evaluated
exactly) is <= L_N. The check computes the exact probabilities of non-coverage, certification and
false certification (Adv(w;theta_*) <= 0), and checks that false certification implies non-coverage
history by history. A plug-in "certificate" D(theta_hat), the value at a feasible point of the
minimization (an upper bound on L_N), is shown for contrast.
"""
import itertools
from fractions import Fraction as F
from math import comb, factorial, isqrt

import sympy as sp

ETA = F(1, 4)


def shocks(kind, scale=F(1)):
    """Scenarios (q, z^f, z^A, z^E) with one ETF. Signs are equiprobable."""
    out = []
    for s1, s2, s3 in itertools.product((-1, 1), repeat=3):
        zf = (F(3, 50) * s1 * scale, F(1, 50) * s2 * scale)
        if kind == "nonsingular":
            zA = (F(1, 50) * s3 + F(1, 100) * s1) * scale  # cross-covariance with the first factor
        elif kind == "singular":
            zA = F(1, 2) * zf[0]                          # collinear: Omega has rank 2
        else:
            zf, zA = (F(0), F(0)), F(0)                   # Omega = 0
        out.append((F(1, 8), zf, zA, (F(1, 200) * s2,)))
    return out


def omega(sh):
    M = sp.zeros(3, 3)
    for q, zf, zA, _ in sh:
        v = sp.Matrix([zf[0], zf[1], zA])
        M += q * v * v.T
    return M


def in_range(M, v):
    return (M * M.pinv() * v - v).is_zero_matrix


def law(sh, N):
    """Exact law of e_N = mean of zeta over N iid draws: list of (mass, e) by count vector."""
    zs = [sp.Matrix([zf[0], zf[1], zA]) for q, zf, zA, _ in sh if q > 0]
    qs = [q for q, *_ in sh if q > 0]
    k = len(zs)
    out = []
    for cut in itertools.combinations(range(N + k - 1), k - 1):
        counts = [b - a - 1 for a, b in zip((-1,) + cut, cut + (N + k - 1,))]
        mass = F(factorial(N))
        for c, q in zip(counts, qs):
            mass = mass / factorial(c) * q ** c
        e = sum((c * z for c, z in zip(counts, zs)), sp.zeros(3, 1)) / N
        out.append((mass, e))
    assert sum(m for m, _ in out) == 1
    return out


def quantile(L, Mp, N):
    T = {}
    for m, e in L:
        t = sp.nsimplify(N * (e.T * Mp * e)[0])
        T[t] = T.get(t, 0) + m
    acc = 0
    for t in sorted(T):
        acc += T[t]
        if acc >= 1 - ETA:
            return t, T
    raise AssertionError


def part_a():
    print("### Part A: calibration and coverage (exact)\n")
    print("| Omega | rank | N_obs | t_{N,eta} | exact coverage P(T_N <= t) | >= 1 - eta |\n|---|---|---|---|---|---|")
    fails = []
    for kind in ("nonsingular", "singular", "zero"):
        sh = shocks(kind)
        M = omega(sh)
        Mp = M.pinv()
        for q, zf, zA, _ in sh:
            if q > 0 and not in_range(M, sp.Matrix([zf[0], zf[1], zA])):
                fails.append(f"{kind}: a positive-mass zeta lies outside Im(Omega)")
        for N in (2, 4):
            L = law(sh, N)
            if any(not in_range(M, e) for _, e in L):
                fails.append(f"{kind}: a positive-mass sample error lies outside Im(Omega)")
            t, T = quantile(L, Mp, N)
            cov = sum(m for s, m in T.items() if s <= t)
            print(f"| {kind} | {M.rank()} | {N} | {t} | {cov} = {float(cov):.4f} | {cov >= 1 - ETA} |")
            if cov < 1 - ETA:
                fails.append(f"{kind} N={N}: coverage below 1 - eta")
            if kind == "zero" and (t != 0 or any(not e.is_zero_matrix for _, e in L)):
                fails.append("Omega = 0: t or the error is not zero, so C_N != {theta_*}")
    # A zero-mass scenario outside Im(Omega) must not enter the calibration.
    sh = shocks("singular") + [(F(0), (F(0), F(0)), F(1, 10), (F(0),))]
    M = omega(sh)
    out = not in_range(M, sp.Matrix([0, 0, F(1, 10)]))
    L = law(sh, 2)
    print(f"\nZero-mass scenario with zeta outside Im(Omega): outside = {out}; the enumerated law "
          f"(positive-mass scenarios only) has {len(L)} count vectors, all inside Im(Omega): "
          f"{all(in_range(M, e) for _, e in L)}.")
    # Without the range restriction, the pseudoinverse quadratic alone leaves the null direction free.
    null = (sp.eye(3) - M * M.pinv()) * sp.Matrix([0, 0, 1])
    print(f"Null direction of the singular Omega: {list(null.T)}. N e' Omega^+ e is unchanged along it, so "
          f"dropping the range restriction keeps coverage valid but makes the set an unbounded cylinder, "
          f"bounded only by Theta_4. The restriction matters for sharpness, not validity.")
    return fails


# ---------------------------------------------------------------- Part B: the certification chain
AM, PM, KM = F(3, 10), F(1, 2), F(1, 5)           # incumbent active, ETF, cash (W^- = 1)
KA, KE = F(1, 500), F(1, 2000)                     # symmetric rates: active, ETF
GAMMA = F(2)
BA, BE = (F(1), F(1, 2)), (F(1), F(0))
BOX = ((F(1, 100), F(3, 100)), (F(0), F(1, 50)), (F(-1, 20), F(1, 10)))   # Theta_4, a box


def sigma(sh):
    S = [[F(0)] * 2 for _ in range(2)]
    for q, zf, zA, zE in sh:
        x = (BA[0] * zf[0] + BA[1] * zf[1] + zA, BE[0] * zf[0] + BE[1] * zf[1] + zE[0])
        for i in range(2):
            for j in range(2):
                S[i][j] += q * x[i] * x[j]
    return S


def Q(w, th, S):
    a, p = w
    lam, al = th[:2], th[2]
    b = [BA[i] * a + BE[i] * p for i in range(2)]
    tau = KA * abs(a - AM) + KE * abs(p - PM)
    quad = a * a * S[0][0] + 2 * a * p * S[0][1] + p * p * S[1][1]
    return b[0] * lam[0] + b[1] * lam[1] + a * al - GAMMA / 2 * quad - tau


def supE(th, S):
    """Exact max of Q((AM, p); th) over E: p in [0, PM + KM/(1+KE)], piecewise concave quadratic."""
    hi = PM + KM / (1 + KE)
    cands = {F(0), PM, hi}
    lam = th[:2]
    lin = BE[0] * lam[0] + BE[1] * lam[1] - GAMMA * AM * S[0][1]
    for sgn, lo_, hi_ in ((-1, F(0), PM), (1, PM, hi)):     # d/dp = lin - gamma S11 p - sgn*KE
        p = (lin - sgn * KE) / (GAMMA * S[1][1])
        if lo_ <= p <= hi_:
            cands.add(p)
    return max(Q((AM, p), th, S) for p in cands)


def ub_sqrt(x):
    x = F(x)
    return F(isqrt(-(-x.numerator * 10 ** 16 // x.denominator)) + 1, 10 ** 8)


def candidate(th_hat):
    """A data-selected funded candidate: switch DA from the ETF into the active fund if the plug-in
    alpha is positive, else from the active fund into the ETF, keeping cash unchanged."""
    DA = F(1, 10)
    if th_hat[2] > 0:
        return (AM + DA, PM - (1 + KA) * DA / (1 - KE))
    return (AM - DA, PM + (1 - KA) * DA / (1 + KE))


def part_b():
    print("\n### Part B: certification chain (exact), delta_econ = 0, one ETF, nonsingular Omega "
          "(shocks scaled by 1/10)\n")
    sh = shocks("nonsingular", F(1, 10))
    S = sigma(sh)
    M = omega(sh)
    Mp = M.pinv()
    fails = []
    lam = (F(1, 50), F(1, 100))
    w_buy = candidate((0, 0, F(1)))
    adv0 = Q(w_buy, lam + (F(0),), S) - supE(lam + (F(0),), S)
    alpha_b = -adv0 / (w_buy[0] - AM)               # Adv of the buy candidate is linear in alpha, slope DA
    print(f"Break-even alpha of the buy candidate at lambda_*: {float(alpha_b):.6f} (exact rational in the code)\n")
    pos = all(1 + BA[0] * v[0] + BA[1] * v[1] + v[2] + BA[0] * zf[0] + BA[1] * zf[1] + zA > 0 and
              1 + BE[0] * v[0] + BE[1] * v[1] + BE[0] * zf[0] + BE[1] * zf[1] + zE[0] > 0
              for v in itertools.product(*BOX) for q, zf, zA, zE in sh)
    if not pos:
        fails.append("Theta_4 vertices do not give positive gross returns")
    print("| alpha_* | N_obs | P(non-coverage) | P(certify, valid) | P(false cert, valid) | "
          "P(false cert, plug-in) | false cert implies non-coverage |\n|---|---|---|---|---|---|---|")
    for alpha_star in (alpha_b - F(1, 10 ** 6), alpha_b + F(1, 400), alpha_b + F(1, 100)):
        th_star = lam + (alpha_star,)
        assert all(BOX[i][0] <= th_star[i] <= BOX[i][1] for i in range(3))
        for N in (4, 6):
            L = law(sh, N)
            t, _ = quantile(L, Mp, N)
            r = [ub_sqrt(F(int(sp.Rational(t * M[i, i] / N).p), int(sp.Rational(t * M[i, i] / N).q))) for i in range(3)]
            p_nc = p_cert = p_false = p_plug = F(0)
            implied = True
            for m, e in L:
                ef = [F(int(sp.Rational(x).p), int(sp.Rational(x).q)) for x in e]
                th_hat = tuple(th_star[i] + ef[i] for i in range(3))
                covered = bool(sp.nsimplify(N * (e.T * Mp * e)[0]) <= t)   # e is in Im(Omega) (Part A)
                w = candidate(th_hat)
                adv = Q(w, th_star, S) - supE(th_star, S)
                box = [(max(BOX[i][0], th_hat[i] - r[i]), min(BOX[i][1], th_hat[i] + r[i])) for i in range(3)]
                if all(lo <= hi for lo, hi in box):
                    ell = min(Q(w, v, S) - supE(v, S) for v in itertools.product(*box))
                    cert = w[0] != AM and ell > 0
                else:
                    cert = False                     # C_N is empty: no certificate
                plug = w[0] != AM and Q(w, th_hat, S) - supE(th_hat, S) > 0
                p_nc += m * (not covered)
                p_cert += m * cert
                p_false += m * (cert and adv <= 0)
                p_plug += m * (plug and adv <= 0)
                if cert and adv <= 0 and covered:
                    implied = False
            print(f"| {float(alpha_star):.6f} | {N} | {float(p_nc):.4f} | {float(p_cert):.4f} | {float(p_false):.4f} | "
                  f"{float(p_plug):.4f} | {implied} |")
            if not implied or p_false > ETA or p_false > p_nc:
                fails.append(f"alpha_*={alpha_star}, N={N}: false certification not controlled")
            plug_max = max(globals().get("plug_max", 0), p_plug); globals()["plug_max"] = plug_max
            cert_max = max(globals().get("cert_max", 0), p_cert); globals()["cert_max"] = cert_max
    if not globals().get("plug_max", 0) > ETA:
        fails.append("the plug-in contrast did not exceed eta (instance not informative)")
    if not globals().get("cert_max", 0) > 0:
        fails.append("the valid certifier never certifies (chain only vacuously safe)")
    return fails


def main():
    fails = part_a() + part_b()
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())

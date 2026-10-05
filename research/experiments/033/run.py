"""Experiment 033: claim 039 (when a return history can certify an active change) by exact computation.
Registered design: experiments/033-certification-check.md.  Run: uv run python experiments/033/run.py

Part 1: experiment 029's one-review solver. Parts 2-3: exact normal and binomial error probabilities, with the exact
minimax (Neyman-Pearson, randomized) minimal history. Part 5: the scalar Kalman prediction-variance recursion. Part 6:
Monte Carlo. Part 7: direct Gaussian conditioning on the stacked residual observations.
"""
import importlib.util
import itertools
import json
import math
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np
from scipy.stats import binom, norm

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run029", HERE.parent / "029" / "run.py")
m29 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m29)
GAMMA, V = m29.GAMMA, m29.V
SIGMAS = [0.005, 0.01, 0.02, 0.04]
DELTAS = [0.0002, 0.0005, 0.001, 0.0015, 0.0025, 0.005, 0.01]
EPSS = [0.01, 0.05, 0.1, 0.2]


# ---------------------------------------------------------------- part 1 ----------
def part1(args):
    rates, xm, lam = args
    kp, km = rates; cap = 0.25
    b, s = kp + GAMMA * V * xm, -km + GAMMA * V * xm
    rows = []
    for a in np.round(np.linspace(s - 0.005, b + 0.005, 41), 8):
        I = m29.Inst(np.array([[1.0, 0.5]]), np.eye(2), a, V, kp, km, xm, cap, lam=np.array(lam))
        x = [m29.solve(I, "joint", sv)[0] for sv in m29.SOLVERS]
        tr = x[0][0] - xm
        dec = "buy" if tr > 1e-5 else ("sell" if tr < -1e-5 else "hold")
        pred = "buy" if (a - b > 0 and xm < cap) else ("sell" if (s - a > 0 and xm > 0) else "hold")
        edge = min(abs(a - b), abs(a - s)) < 1e-7
        interior = bool(np.all(x[0][1:] > 1e-5) and np.all(x[0][1:] < 1 - 1e-5) and I.cash(x[0]) > 1e-5)
        rows.append(dict(a=float(a), dec=dec, pred=pred, edge=bool(edge), hyp=interior, x=float(x[0][0]), dx=float(abs(x[0][0] - x[1][0]))))
    return dict(rates=rates, xm=xm, lam=lam, rows=rows)


# ---------------------------------------------------------------- part 2 ----------
def part2():
    out = []
    for sg, d, e in itertools.product(SIGMAS, DELTAS, EPSS):
        z = norm.isf(e)
        n_suff = math.ceil(4 * sg ** 2 * z ** 2 / d ** 2)
        typeI = norm.sf(z)                                       # Delta = 0: P(mean - sigma z/sqrt n > b)
        power = norm.cdf(d * math.sqrt(n_suff) / sg - z)          # Delta = delta
        # exact minimax two-point (N(0) vs N(delta)): max error Phi(-delta sqrt(n) / (2 sigma)); smallest n with it <= eps
        n_min = math.ceil((2 * sg * z / d) ** 2)
        while n_min > 1 and norm.cdf(-d * math.sqrt(n_min - 1) / (2 * sg)) <= e:
            n_min -= 1
        while norm.cdf(-d * math.sqrt(n_min) / (2 * sg)) > e:
            n_min += 1
        lower = (4 * sg ** 2 / d ** 2) * math.log(1 / (4 * e)) if e < 0.25 else None
        out.append(dict(sigma=sg, delta=d, eps=e, n_suff=n_suff, typeI=typeI, power=power, n_min=n_min, lower=lower))
    # prior worth sigma^2/s^2 quarters
    pri = []
    for sg, s, n in itertools.product(SIGMAS, (0.001, 0.0035, 0.01), (0, 10, 100, 1000)):
        a = 1 / (1 / s ** 2 + n / sg ** 2); b = sg ** 2 / (n + sg ** 2 / s ** 2)
        pri.append(dict(sigma=sg, s=s, n=n, rel=abs(a - b) / a))
    return out, pri


# ---------------------------------------------------------------- part 3 ----------
def minimax_err(n, p0, p1):
    """Minimax (over the two simple hypotheses) error of the best randomized test on K ~ Bin(n, p), p0 < p1:
    for each threshold k (buy iff K > k, randomized with probability g at K = k), the best g, then the best k."""
    w = 6 * int(math.sqrt(n) + 3); kc = int(n * (p0 + p1) / 2)
    k = np.arange(max(0, kc - w), min(n, kc + w) + 1)
    a0, a1 = binom.sf(k, n, p0), binom.pmf(k, n, p0)
    b0, b1 = binom.cdf(k - 1, n, p1), binom.pmf(k, n, p1)
    den = a1 + b1
    g = np.clip(np.where(den > 0, (b0 + b1 - a0) / np.where(den > 0, den, 1), 0.0), 0.0, 1.0)
    return float(np.min(np.maximum(a0 + g * a1, b0 + (1 - g) * b1)))


def part3_cell(args):
    R, d, e = args
    p0, p1 = 0.5, 0.5 * (1 + d / R)
    nH = math.ceil(8 * R ** 2 / d ** 2 * math.log(1 / e))
    # Hoeffding rule on the two-point law: buy iff mean - R sqrt(2 log(1/eps)/n) > b; mean = b + Delta + R (2K/n - 1)
    thr = R * math.sqrt(2 * math.log(1 / e) / nH)
    kI = math.floor(nH * (1 + thr / R) / 2)                     # buy iff K > kI when Delta = 0
    typeI = binom.sf(kI, nH, p0)
    kII = math.floor(nH * (1 + (thr - d) / R) / 2)              # when Delta = delta
    power = binom.sf(kII, nH, p1)
    lo, hi = 1, max(2, nH)
    while minimax_err(hi, p0, p1) > e:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if minimax_err(mid, p0, p1) <= e:
            hi = mid
        else:
            lo = mid
    n = hi                                     # lattice effects: scan down for a smaller certifying n
    for m in range(hi - 1, max(0, hi - 200), -1):
        if minimax_err(m, p0, p1) <= e:
            n = m
    hi = n
    c = hi * d ** 2 / (R ** 2 * math.log(1 / e))
    return dict(R=R, delta=d, eps=e, nH=nH, typeI=float(typeI), power=float(power), n_min=hi, c=c)


# ---------------------------------------------------------------- part 5 ----------
def p_inf(phi, q, s2):
    a = q - s2 * (1 - phi ** 2)
    return (a + math.sqrt(a ** 2 + 4 * q * s2)) / 2


def part5():
    out = []
    for phi, qr, sg in itertools.product([0.0, 0.5, 0.8, 0.95, 0.99], [1e-4, 1e-3, 1e-2, 0.1, 1.0], [0.01, 0.02]):
        s2 = sg ** 2; q = qr * s2; pinf = p_inf(phi, q, s2)
        for mult in (1.0, 4.0):
            p = mult * q / (1 - phi ** 2); mono = True; minexc = math.inf
            for _ in range(10000):
                pn = phi ** 2 * p * s2 / (p + s2) + q
                mono &= pn <= p * (1 + 1e-15)
                minexc = min(minexc, (pn - pinf) / pinf); p = pn
            out.append(dict(phi=phi, qr=qr, sigma=sg, mult=mult, limit_rel=abs(p - pinf) / pinf, mono=bool(mono), min_rel_excess=minexc,
                            floor=float(norm.isf(0.05) * math.sqrt(pinf))))
    lim = dict(q_small=[p_inf(0.9, q, 0.02 ** 2) for q in (1e-8, 1e-10, 1e-12)],
               s_large=[(p_inf(0.9, 1e-6, s2), 1e-6 / (1 - 0.81)) for s2 in (1e-2, 1.0, 1e2)])
    return out, lim


# ---------------------------------------------------------------- part 6 ----------
def part6(n):
    rng = np.random.default_rng([2033, n]); draws = 20000
    Sf = m29.SF; lam = m29.LAM; sg = 0.02; bA = np.array([1.0, 0.5])
    out = {}
    for menu, BE in (("unreachable", np.array([[1.0, 0.0]])), ("spanning", np.eye(2))):
        Q_, _ = np.linalg.qr(BE.T); PiR = Q_ @ Q_.T; PiU = np.eye(2) - PiR
        St = Sf            # premia estimated by the sample mean of factor returns, prior ignored (part 6)
        SRR, SRU = PiR @ St @ PiR, PiR @ St @ PiU
        J = PiU - PiR @ np.linalg.pinv(SRR) @ SRU
        f = lam + rng.standard_normal((draws, n, 2)) @ np.linalg.cholesky(Sf).T
        z = sg * rng.standard_normal((draws, n))
        est = z.mean(1) + (f.mean(1) @ J) @ bA                    # alpha_hat - alpha + B^A J' lambda_hat (alpha = 0)
        v = est.var(ddof=1) * n
        se = v * math.sqrt(2 / (draws - 1))
        form = sg ** 2 + bA @ J.T @ Sf @ J @ bA
        out[menu] = dict(n=n, var_n=float(v), se=float(se), formula=float(form), ratio_formula=float(form / sg ** 2))
    return out


# ---------------------------------------------------------------- part 7 ----------
def part7():
    out = []; s, sg = 0.0035, 0.02
    for N, sh, n in itertools.product([2, 5, 30], [0.0, 0.5, 2.0], [0, 10, 100]):
        sb2 = sh * s ** 2
        P0 = sb2 * np.ones((N, N)) + s ** 2 * np.eye(N)
        if n == 0:
            Post = P0
        else:
            H = np.kron(np.eye(N), np.ones((n, 1)))              # stacked observations y = H alpha + z
            Syy = H @ P0 @ H.T + sg ** 2 * np.eye(N * n)
            Say = P0 @ H.T
            Post = P0 - Say @ np.linalg.solve(Syy, Say.T)
        one = np.ones(N) / N
        va = float(one @ Post @ one); fa = (1 / N) / (1 / (s ** 2 + N * sb2) + n / sg ** 2)
        e = np.zeros(N); e[0], e[1] = 1 / math.sqrt(2), -1 / math.sqrt(2)
        vr = float(e @ Post @ e); fr = 1 / (1 / s ** 2 + n / sg ** 2)
        out.append(dict(N=N, share=sh, n=n, avg=va, avg_formula=fa, rel_avg=abs(va - fa) / fa, relative=vr, rel_formula=fr, rel_rel=abs(vr - fr) / fr))
    return out


def part7_mp():
    """Deviation 2: the same conditioning at 50 digits (mpmath) on small cells, to separate round-off from the formula."""
    import mpmath as mp_
    mp_.mp.dps = 50; out = []
    s, sg = mp_.mpf("0.0035"), mp_.mpf("0.02")
    for N, sh, n in ((2, 0.5, 10), (5, 2.0, 10), (5, 0.5, 3)):
        sb2 = mp_.mpf(sh) * s ** 2
        P0 = mp_.matrix(N, N)
        for i in range(N):
            for j in range(N):
                P0[i, j] = sb2 + (s ** 2 if i == j else 0)
        H = mp_.matrix(N * n, N)
        for i in range(N):
            for k in range(n):
                H[i * n + k, i] = 1
        Syy = H * P0 * H.T + sg ** 2 * mp_.eye(N * n)
        Post = P0 - P0 * H.T * mp_.inverse(Syy) * H * P0
        one = mp_.matrix([mp_.mpf(1) / N] * N)
        va = (one.T * Post * one)[0]; fa = (mp_.mpf(1) / N) / (1 / (s ** 2 + N * sb2) + n / sg ** 2)
        out.append(dict(N=N, share=sh, n=n, rel=float(abs(va - fa) / fa)))
    return out


def main():
    t0 = time.time(); S = {}
    lams = [(0.015, 0.005), (0.01, 0.01), (0.02, 0.0), (0.005, 0.005), (0.03, 0.01)]
    with mp.Pool(9) as pool:
        S["part1"] = pool.map(part1, list(itertools.product([(0.001, 0.001), (0.005, 0.001), (0.0, 0.0)], [0.0, 0.1, 0.25], lams)))
        print("p1", time.time() - t0, flush=True)
        S["part3"] = pool.map(part3_cell, list(itertools.product([0.01, 0.02, 0.04], DELTAS, EPSS)))
        print("p3", time.time() - t0, flush=True)
        S["part6"] = pool.map(part6, [40, 160])
    S["part2"], S["part2_prior"] = part2()
    S["part5"], S["part5_limits"] = part5()
    S["part7"] = part7()
    S["part7_mp"] = part7_mp()
    S["seconds"] = time.time() - t0
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()

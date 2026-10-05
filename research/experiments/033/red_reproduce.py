"""Red's reproduction of experiment 033 (claim 039), written without reading run.py, report.py or checks/039."""
import warnings
import numpy as np, cvxpy as cp
from scipy.stats import norm, binom
warnings.simplefilter('ignore')

SIGS = [0.005, 0.01, 0.02, 0.04]; DELS = [0.0002, 0.0005, 0.001, 0.0015, 0.0025, 0.005, 0.01]; EPSS = [0.01, 0.05, 0.1, 0.2]


def part2():
    print("== Part 2 ==")
    worst_t1 = 0; bad_pow = 0; eq = 0; ratios = {}; lb_bad = 0; cells = 0
    for s in SIGS:
        for d in DELS:
            for e in EPSS:
                z = norm.isf(e); n = int(np.ceil(4 * s * s * z * z / (d * d))); cells += 1
                t1 = norm.sf(z)                                  # P(mean - s z/sqrt n > b | Delta = 0)
                pw = norm.sf(z - d * np.sqrt(n) / s)            # at Delta = delta
                worst_t1 = max(worst_t1, abs(t1 - e)); bad_pow += pw < 1 - e - 1e-15
                # exact minimax minimal n: best test's max error is Phi(-delta sqrt(n)/(2 sigma)) (equal-error NP test)
                nm = n
                while nm > 1 and norm.cdf(-d * np.sqrt(nm - 1) / (2 * s)) <= e: nm -= 1
                while norm.cdf(-d * np.sqrt(nm) / (2 * s)) > e: nm += 1
                eq += nm == n
                lb = 4 * s * s / (d * d) * np.log(1 / (4 * e)); lb_bad += nm < lb
                ratios.setdefault(e, []).append(nm / lb)
    print(f" {cells} cells: max|type I - eps| {worst_t1:.1g}; power < 1 - eps at {bad_pow}; exact minimal n = n_suff at {eq}; minimal n below the lower bound at {lb_bad}")
    print(" ratio n_min / lower bound by eps: " + ", ".join(f"{e}: {min(r):.2f}-{max(r):.2f}" for e, r in ratios.items()))
    for s, d in [(0.02, 0.001), (0.01, 0.0015)]:
        print(f" illustration sigma {s * 100:g}%, gap {d * 100:g}%, eps 0.05: n = {int(np.ceil(4 * s * s * norm.isf(0.05) ** 2 / d ** 2))}")
    err = 0
    for s in SIGS:
        for s2 in [1e-6, 1e-5, 1e-4]:
            for n in [0, 10, 100, 1000]:
                a = 1 / (1 / s2 + n / s ** 2); b = s ** 2 / (n + s ** 2 / s2); err = max(err, abs(a / b - 1))
    print(f" prior worth sigma^2/s^2 quarters: max relative difference {err:.1g}")


def np_power(n, p0, p1, e):
    """Most powerful level-e test of Bin(n,p0) vs Bin(n,p1), p1 > p0 (reject for large k, randomized)."""
    c = int(binom.isf(e, n, p0))                    # smallest c with P0(K > c) <= e
    while binom.sf(c, n, p0) > e: c += 1
    while c > 0 and binom.sf(c - 1, n, p0) <= e: c -= 1
    g = (e - binom.sf(c, n, p0)) / binom.pmf(c, n, p0)
    return binom.sf(c, n, p1) + g * binom.pmf(c, n, p1)


def part3():
    print("== Part 3 ==")
    cvals = {}; worst = 0; bad = 0; cons = []; cells = 0
    for R in [0.01, 0.02, 0.04]:
        for d in DELS:
            for e in EPSS:
                cells += 1; p0 = 0.5; p1 = (1 + d / R) / 2
                nH = int(np.ceil(8 * R * R / (d * d) * np.log(1 / e)))
                # Hoeffding rule, b = 0: buy iff mean > R sqrt(2 log(1/e)/n); mean = (2k - n) R / n
                thr = R * np.sqrt(2 * np.log(1 / e) / nH); kstar = int(np.floor((thr * nH / R + nH) / 2))   # buy iff k > kstar
                while (2 * kstar - nH) * R / nH > thr: kstar -= 1
                while (2 * (kstar + 1) - nH) * R / nH <= thr: kstar += 1
                t1 = binom.sf(kstar, nH, p0); pw = binom.sf(kstar, nH, p1)
                bad += t1 > e + 1e-12 or pw < 1 - e - 1e-12; worst = max(worst, t1 / e)
                ok = lambda n: np_power(n, p0, p1, e) >= 1 - e
                lo, hi = 1, nH
                while not ok(hi): hi *= 2
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    if ok(mid): hi = mid
                    else: lo = mid
                nmin = hi
                for n in range(max(1, hi - 200), hi):
                    if ok(n): nmin = n; break
                c = nmin * d * d / (R * R * np.log(1 / e)); cvals.setdefault(e, []).append(c); cons.append(nH / nmin)
    allc = np.concatenate(list(cvals.values()))
    print(f" {cells} cells: Hoeffding failures {bad}; largest type I / eps {worst:.2f}; c = n_min delta^2/(R^2 log(1/eps)) {allc.min():.2f}-{allc.max():.2f} (median {np.median(allc):.2f}); "
          + "; ".join(f"eps {e}: {min(v):.2f}-{max(v):.2f}" for e, v in cvals.items()) + f"; Hoeffding/n_min {min(cons):.1f}-{max(cons):.1f}")


def pinf(phi, q, s2):
    a = q - s2 * (1 - phi * phi); return (a + np.sqrt(a * a + 4 * q * s2)) / 2


def part5():
    print("== Part 5 ==")
    errlim = 0; nonmono = 0; below = 0; runs = 0
    for phi in [0, 0.5, 0.8, 0.95, 0.99]:
        for qr in [1e-4, 1e-3, 1e-2, 0.1, 1]:
            for s in [0.01, 0.02]:
                s2 = s * s; q = qr * s2; pi = pinf(phi, q, s2)
                for p0 in [q / (1 - phi ** 2), 4 * q / (1 - phi ** 2)]:
                    p = p0; prev = p; mn = np.inf; mono = True; runs += 1
                    for _ in range(10000):
                        p = phi * phi * p * s2 / (p + s2) + q
                        mono &= p <= prev * (1 + 1e-15); prev = p; mn = min(mn, (p - pi) / pi)
                    errlim = max(errlim, abs(p - pi) / pi); nonmono += not mono; below += mn < -1e-13
    print(f" {runs} runs: max relative |p_10000 - p_inf| {errlim:.1g}; non-monotone {nonmono}; below p_inf (beyond 1e-13 rel) {below}")
    s2 = 0.02 ** 2
    print(" q -> 0 (phi 0.95, sigma 2%): " + ", ".join(f"q {q:g}: {pinf(0.95, q, s2):.2g}" for q in [1e-8, 1e-10, 1e-12]))
    print(" sigma -> inf (phi 0.95, q 1e-6): p_inf/(q/(1-phi^2)) " + ", ".join(f"sigma {s:g}: {pinf(0.95, 1e-6, s * s) / (1e-6 / (1 - 0.95 ** 2)):.5f}" for s in [0.1, 1, 10]))
    z = norm.isf(0.05)
    for qr in [0.001, 0.01, 0.1]:
        print(f" floor z_0.05 sqrt(p_inf), sigma 2%, q/sigma^2 {qr}: " + ", ".join(f"phi {ph}: {z * np.sqrt(pinf(ph, qr * s2, s2)) * 100:.2f}%" for ph in [0, 0.5, 0.8, 0.95, 0.99]))


def part6():
    print("== Part 6 ==")
    Sf = np.diag([0.08 ** 2, 0.04 ** 2]); sA = 0.02; Bi = np.array([1.0, 0.5])
    for menu, BE in [('unreachable', np.array([[1.0, 0.0]])), ('spanning', np.eye(2))]:
        PiR = BE.T @ np.linalg.pinv(BE @ BE.T) @ BE; PiU = np.eye(2) - PiR
        RR = PiR @ Sf @ PiR; RU = PiR @ Sf @ PiU; J = PiU - PiR @ np.linalg.pinv(RR) @ RU
        w = J @ Bi                                            # B^A_i J' lambda = w' lambda
        pred = sA ** 2 + w @ Sf @ w
        for n in [40, 160]:
            rng = np.random.default_rng([2033, n, 7])
            f = rng.multivariate_normal(np.zeros(2), Sf, size=(20000, n)); e = rng.normal(0, sA, (20000, n))
            est = e.mean(1) + f.mean(1) @ w
            v = n * est.var(ddof=1); se = n * est.var(ddof=1) * np.sqrt(2 / 19999)
            print(f" {menu}, n {n}: n Var {v:.3e} (SE {se:.1e}) vs {pred:.3e}, z {(v - pred) / se:+.2f}; ratio {pred / sA ** 2:.3f}")


def part7():
    print("== Part 7 ==")
    sA = 0.02; s = 0.01; worst = worst_rel = 0
    for N in [2, 5, 30]:
        for r in [0, 0.5, 2]:
            for n in [0, 10, 100]:
                sb2 = r * s * s; P0 = s * s * np.eye(N) + sb2 * np.ones((N, N))
                if n == 0: P = P0
                else:
                    H = np.kron(np.eye(N), np.ones((n, 1)))           # (N n) x N, observation e_ij = alpha_i + z
                    S = H @ P0 @ H.T + sA ** 2 * np.eye(N * n)
                    P = P0 - P0 @ H.T @ np.linalg.solve(S, H @ P0)
                u = np.ones(N) / N; va = u @ P @ u
                fa = (1 / N) / (1 / (s * s + N * sb2) + n / sA ** 2); worst = max(worst, abs(va / fa - 1))
                c = np.zeros(N); c[0], c[1] = 1 / np.sqrt(2), -1 / np.sqrt(2)
                fr = 1 / (1 / (s * s) + n / sA ** 2); worst_rel = max(worst_rel, abs(c @ P @ c / fr - 1))
                if (N, r, n) == (30, 0.5, 100): illus = (fr / va, P[0, 0] / va)
    print(f" 27 cells: max relative error, average {worst:.1g}, relative direction {worst_rel:.1g}")
    print(f" N 30, s_bar^2/s^2 0.5, n 100 (s = 1%, sigma 2%): one fund's relative-direction variance / average's {illus[0]:.1f}; one fund's own posterior variance / average's {illus[1]:.1f}")


def part1():
    print("== Part 1 ==")
    gam = 5.0; Sf = np.diag([0.08 ** 2, 0.04 ** 2]) + np.diag([0.005 ** 2] * 2); L = np.linalg.cholesky(Sf); Bi = np.array([1.0, 0.5]); v = 0.02 ** 2 + 0.0035 ** 2; cap = 0.25
    a = cp.Parameter(); x0 = cp.Parameter(nonneg=True); kp = cp.Parameter(nonneg=True); km = cp.Parameter(nonneg=True); lam = cp.Parameter(2)
    x = cp.Variable(); xE = cp.Variable(2); up = cp.Variable(nonneg=True); dn = cp.Variable(nonneg=True)
    b = Bi * x + xE
    Q = lam @ b - gam / 2 * cp.sum_squares(L.T @ b) + a * x - gam / 2 * v * cp.square(x) - kp * up - km * dn
    cons = [x - x0 == up - dn, x >= 0, x <= cap, xE >= 0, xE <= 1, 1 - (x - x0) - cp.sum(xE) - kp * up - km * dn >= 0]
    pr = cp.Problem(cp.Maximize(1e4 * Q), cons)
    lams = [np.array([0.015, 0.005]), np.array([0.01, 0.002]), np.array([0.02, 0.008]), np.array([0.005, 0.0]), np.array([0.03, 0.01])]
    agree = n = edge = hyp_out = 0; cap_held = zero_held = 0; cap_n = zero_n = 0; spread = 0
    for x0v in [0, 0.1, 0.25]:
        for kpv, kmv in [(0.001, 0.001), (0.005, 0.001), (0.0, 0.0)]:
            bth = kpv + gam * v * x0v; sth = -kmv + gam * v * x0v
            for av in np.unique(np.concatenate([np.linspace(bth - 0.005, bth + 0.005, 41), np.linspace(sth - 0.005, sth + 0.005, 41)])):
                hold = []
                for lv in lams:
                    a.value, x0.value, kp.value, km.value, lam.value = av, x0v, kpv, kmv, lv
                    pr.solve(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12)
                    xe = xE.value; cash = 1 - (x.value - x0v) - xe.sum() - kpv * up.value - kmv * dn.value
                    if np.any(xe < 1e-5) or np.any(xe > 1 - 1e-5) or cash < 1e-7: hyp_out += 1; continue
                    D, Ds = av - bth, sth - av
                    if min(abs(D), abs(Ds)) < 1e-9: edge += 1; continue
                    pred = 1 if (x0v < cap and D > 0) else (-1 if (x0v > 0 and Ds > 0) else 0)
                    got = 1 if x.value > x0v + 1e-5 else (-1 if x.value < x0v - 1e-5 else 0)
                    n += 1; agree += pred == got; hold.append(x.value)
                    if x0v == cap and D > 0: cap_n += 1; cap_held += got == 0
                    if x0v == 0 and Ds > 0: zero_n += 1; zero_held += got == 0
                if len(hold) > 1: spread = max(spread, max(hold) - min(hold))
    print(f" {n} points meet the hypotheses ({hyp_out} with an ETF at a bound or cash binding, {edge} knife edges): agreement {agree}/{n}; "
          f"at the cap with a positive purchase gap held {cap_held}/{cap_n}; at zero with a positive sale gap held {zero_held}/{zero_n}; largest holding change across premia {spread:.1e}")


if __name__ == "__main__":
    part2(); part3(); part5(); part6(); part7(); part1()

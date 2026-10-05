"""Finite checks for claim 039 (D15b (ii): when data can support an active change); not its proof.

Run: uv run python checks/039/check.py

 (i)  part 2: Monte Carlo of the Gaussian rule's two error probabilities at the boundary and at margin delta on grids,
      at the sufficient n; the two-Gaussian affinity and the lower-bound arithmetic;
 (ii) part 5: the scalar Riccati iterates converge to the displayed root; the floor on the posterior probability;
 (iii) part 7: the pooled posterior variance of the average alpha against the matrix filter;
 (iv) part 1: the one-fund one-review optimum's direction against a grid maximizer.
Illustrations are printed only (rule 22).
"""
import itertools
import sys

import numpy as np
from scipy.stats import norm

rng = np.random.default_rng(39)


def part_i():
    paths = 20000
    for sigma, delta, eps in itertools.product([0.01, 0.03], [0.002, 0.006], [0.05, 0.1]):
        z = norm.isf(eps); n = int(np.ceil(4 * sigma ** 2 * z ** 2 / delta ** 2))
        b = 0.003
        for alpha, want_buy in [(b, False), (b + delta, True)]:
            means = alpha + sigma * rng.standard_normal((paths, n)).mean(axis=1)
            buy = means - sigma * z / np.sqrt(n) > b
            err = (buy != want_buy).mean()
            assert err <= eps + 4 * np.sqrt(eps / paths), (sigma, delta, eps, alpha, err)
        # affinity of N(0, s^2)^n and N(delta, s^2)^n is exp(-n delta^2/(8 s^2)); the two-error arithmetic
        rho = np.exp(-delta ** 2 / (8 * sigma ** 2))
        n_low = 4 * sigma ** 2 / delta ** 2 * np.log(1 / (4 * eps))
        assert rho ** (2 * n) <= 4 * eps + 1e-12 and n >= n_low   # the sufficient n exceeds the necessary one
    for e in np.linspace(1e-6, 0.2499, 2000):
        assert norm.isf(e) ** 2 >= np.log(1 / (4 * e))
    print("  part 2: Gaussian rule meets both error allowances at the sufficient n on the grid; affinity and lower-bound arithmetic consistent")


def riccati_root(phi, q, s2):
    a = q - s2 * (1 - phi ** 2)
    return (a + np.sqrt(a ** 2 + 4 * q * s2)) / 2


def part_ii():
    for phi, q, s2 in itertools.product([0.0, 0.5, 0.9, 0.99], [1e-8, 1e-6, 1e-5], [1e-4, 4e-4]):
        root = riccati_root(phi, q, s2)
        for p0 in [q / (1 - phi ** 2), 1e-3]:   # M5's stationary prior, and a diffuse one
            p = p0; assert p0 >= root - 1e-18
            for _ in range(20000):
                pn = phi ** 2 * p * s2 / (s2 + p) + q
                assert root - 1e-18 <= pn <= p + 1e-18, (phi, q, s2, p0, p, pn, root)   # decreases, stays above the root
                p = pn
            assert abs(p - root) < 1e-12 * max(root, 1e-12), (phi, q, s2, p0, p, root)
        assert abs(phi ** 2 * root * s2 / (s2 + root) + q - root) < 1e-15   # fixed-point identity
        # floor on the posterior probability: for any p >= p_inf, Phi(d/sqrt(p)) <= Phi(d/sqrt(p_inf)) for d > 0
        for d in [1e-4, 1e-3]:
            for p in [root, 2 * root, 10 * root]:
                assert norm.cdf(d / np.sqrt(p)) <= norm.cdf(d / np.sqrt(root)) + 1e-15
        assert root <= q / (1 - phi ** 2) + 1e-18
        if q == 1e-8 and phi < 1:
            assert root < 1e-6   # -> 0 as q -> 0
    print("  part 5: Riccati iterates from the stationary prior decrease to the displayed root and stay above it on the grid; the posterior-probability floor holds")


def part_iii():
    N, n = 4, 12; s2, sbar2, sig2 = 0.0035 ** 2, 0.002 ** 2, 0.02 ** 2
    P = sbar2 * np.ones((N, N)) + s2 * np.eye(N)
    for _ in range(n):
        P = np.linalg.inv(np.linalg.inv(P) + np.eye(N) / sig2)
    one = np.ones(N) / N
    var_avg = one @ P @ one
    closed = (1 / N) / (1 / (s2 + N * sbar2) + n / sig2)
    assert abs(var_avg - closed) < 1e-18, (var_avg, closed)
    e = np.zeros(N); e[0] = 1; e = e - one
    var_rel = e @ P @ e
    closed_rel = (1 - 1 / N) / (1 / s2 + n / sig2)
    assert abs(var_rel - closed_rel) < 1e-18, (var_rel, closed_rel)
    print(f"  part 7: pooled posterior variance of the average {var_avg:.3e} = closed form; relative direction {var_rel:.3e} = closed form (N = {N})")


def part_iv():
    for _ in range(200):
        alpha, v, gamma, xm, kp, km = rng.uniform(-0.01, 0.01), rng.uniform(1e-4, 1e-3), 5.0, rng.uniform(0, 0.5), rng.uniform(0, 0.01), rng.uniform(0, 0.01)
        grid = np.linspace(0, 1, 40001)
        obj = alpha * grid - 0.5 * gamma * v * grid ** 2 - kp * np.maximum(grid - xm, 0) - km * np.maximum(xm - grid, 0)
        x = grid[np.argmax(obj)]
        gap_buy = alpha - kp - gamma * v * xm; gap_sell = -km + gamma * v * xm - alpha
        if gap_buy > 1e-6: assert x > xm + 1e-9, (gap_buy, x, xm)
        elif gap_sell > 1e-6: assert x < xm - 1e-9, (gap_sell, x, xm)
        else: assert abs(x - xm) < 5e-5, (gap_buy, gap_sell, x, xm)
    print("  part 1: the one-fund one-review optimum's direction is the gap's sign on 200 random inputs")


def main():
    part_i(); part_ii(); part_iii(); part_iv()
    # illustrations (rule 22)
    for name, sigma, delta in [("equity-style", 0.02, 0.0010), ("fixed-income-style", 0.01, 0.0015)]:
        z = norm.isf(0.05)
        print(f"  {name} (illustration): sigma {sigma:.3f}, gap {delta:.4f}: sufficient history {int(np.ceil(4 * sigma ** 2 * z ** 2 / delta ** 2))} quarters at epsilon 0.05; "
              f"persistence floor at phi 0.9, q 1e-6: {norm.isf(0.05) * np.sqrt(riccati_root(0.9, 1e-6, sigma ** 2)):.4f}")
    print("checks/039: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)

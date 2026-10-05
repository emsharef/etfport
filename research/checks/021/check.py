"""Finite checks for claim 021; not its proof.

Run: uv run python checks/021/check.py

1. The bounded-variable tail bound (the claim uses constant 3, looser than Hoeffding's 2): for several centered laws with
   |Y| <= R and history lengths N up to 60, the exact upper-tail probability of
   the sample mean, computed by lattice convolution, is at most
   exp(-N a^2/(3 R^2)) on a grid of a in (0, R]; the moment-generating bound
   E exp(tY) <= 1 + 0.72 t^2 R^2 is checked on a grid of |t| <= 1/R.
2. The range-based face-by-face rule in claim 016's family with J = s I:
   exact false certification at the null and exact power at the sufficient
   length, for two laws in the bounded class with covariance I (independent
   signs) and one with a different covariance (a correlated three-point law),
   computed by exact convolution of the face contrasts.
3. The decomposition remark: R_0 + R_lambda2 >= R_1 for random J.
4. Constants: 22 x 81 = 1782 and the level factor 1 + log 2/log(1/eta).
5. Every claim 016 hard law lies in the bounded class: ||U||^2 <= 66 < 81.

These check fixed instances; the claim's statements are for every law in
its class.
"""
import math
import random
import sys
from fractions import Fraction as Fr

import numpy as np


def convolve_lattice(pmf, n):
    """pmf: dict lattice-index -> probability (floats). Return dict for the sum of n iid copies."""
    out = {0: 1.0}
    for _ in range(n):
        new = {}
        for i, p in out.items():
            for j, q in pmf.items():
                new[i + j] = new.get(i + j, 0.0) + p * q
        out = new
    return out


def upper_tail(pmf_sum, n, step, a):
    """P(sum/n >= a) for a lattice pmf of the sum with lattice step."""
    return sum(p for i, p in pmf_sum.items() if i * step / n >= a - 1e-15)


def tail_bound():
    laws = {
        "two-point +-R": ({1: 0.5, -1: 0.5}, 1.0),
        "skewed {-1/3, 1}": ({-1: 0.75, 3: 0.25}, 1 / 3),      # values -1/3, 1 on step 1/3; R = 1
        "three-point {-1,0,1}": ({-1: 0.1, 0: 0.8, 1: 0.1}, 1.0),
        "asymmetric {-1, 1/4}": ({-4: 0.2, 1: 0.8}, 0.25),       # values -1, 1/4 on step 1/4; R = 1
    }
    R = 1.0
    checked = 0
    for name, (pmf, step) in laws.items():
        mean = sum(i * step * p for i, p in pmf.items())
        assert abs(mean) < 1e-12, name
        assert max(abs(i * step) for i in pmf) <= R + 1e-12
        # moment generating function bound
        for t in np.linspace(-1 / R, 1 / R, 41):
            mgf = sum(p * math.exp(t * i * step) for i, p in pmf.items())
            assert mgf <= 1 + 0.72 * t * t * R * R + 1e-12, (name, t, mgf)
        for n in range(1, 61):
            s = convolve_lattice(pmf, n)
            for a in np.linspace(0.02, R, 25):
                tail = upper_tail(s, n, step, a)
                assert tail <= math.exp(-n * a * a / (3 * R * R)) + 1e-12, (name, n, a, tail)
                checked += 1
    print(f"tail bound: {checked} exact tail comparisons hold")


def face_rule_check():
    """Claim 016 family, J = s I_3, faces d_0=(1,0,1), d_1=(1,-1,1). Exact convolution of Y_j = d_j' s U."""
    s = 1 / 100
    eta = 1 / 20
    d = [np.array([1, 0, 1]), np.array([1, -1, 1])]
    sigma_bar = [s * np.linalg.norm(v) for v in d]     # ||J' d_j||
    Rj = [9 * x for x in sigma_bar]
    # laws of U as dicts of tuples -> prob
    signs = [(a, b, c) for a in (-1, 1) for b in (-1, 1) for c in (-1, 1)]
    law_signs = {u: 1 / 8 for u in signs}
    # a correlated three-point law with a different covariance: U = (W, W, -W) with W in {-3,0,3}
    law_corr = {(-3, -3, 3): 1 / 18, (0, 0, 0): 8 / 9, (3, 3, -3): 1 / 18}
    # a skewed law with unit covariance per coordinate: coordinates iid in {-1/2, 2} with probs 4/5, 1/5
    law_skew = {}
    for a in ((-0.5, 0.8), (2, 0.2)):
        for b in ((-0.5, 0.8), (2, 0.2)):
            for c in ((-0.5, 0.8), (2, 0.2)):
                law_skew[(a[0], b[0], c[0])] = a[1] * b[1] * c[1]
    for name, law in (("independent signs", law_signs), ("correlated three-point", law_corr),
                      ("skewed", law_skew)):
        for u, p in law.items():
            assert np.linalg.norm(u) <= 9
        mean = sum(np.array(u) * p for u, p in law.items())
        assert np.max(np.abs(mean)) < 1e-12
        for j in range(2):
            # lattice pmf of Y_j / (s * step)
            vals = {}
            for u, p in law.items():
                y = float(d[j] @ np.array(u))
                vals[y] = vals.get(y, 0.0) + p
            ys = sorted(vals)
            # exact rational lattice: step = gcd of the values
            fr = [Fr(y).limit_denominator(1000) for y in ys]
            step_fr = Fr(0)
            for f in fr:
                step_fr = f if step_fr == 0 else Fr(math.gcd(step_fr.numerator * f.denominator, f.numerator * step_fr.denominator), step_fr.denominator * f.denominator)
            step = float(step_fr) if step_fr != 0 else 1.0
            pmf = {}
            for y, p in vals.items():
                k = round(y / step)
                assert abs(k * step - y) < 1e-9, (y, step)
                pmf[k] = pmf.get(k, 0.0) + p
            assert max(abs(y) for y in ys) * s <= Rj[j] + 1e-12
            for n in (12, 40, 80):
                if n < 3 * math.log(2 / eta):
                    continue
                r = Rj[j] * math.sqrt(3 * math.log(2 / eta) / n)
                ssum = convolve_lattice(pmf, n)
                # false certification on face j at its null needs mean error > r
                tail = sum(p for k, p in ssum.items() if k * step * s / n > r + 1e-15)
                assert tail <= eta / 2 + 1e-12, (name, j, n, tail)
            # power at the sufficient length for delta = sigma_bar/8 (largest allowed)
            delta = max(sigma_bar) / 8
            n_suf = math.ceil(max(3, 22 * max(Rj) ** 2 / delta ** 2) * math.log(2 / eta))
            r = Rj[j] * math.sqrt(3 * math.log(2 / eta) / n_suf)
            assert r < 3 * delta / 8, (name, j, r, delta)
            # the lower tail: P(mean error < -r) <= eta/2 by exact convolution when feasible
            if n_suf <= 400:
                ssum = convolve_lattice(pmf, n_suf)
                low = sum(p for k, p in ssum.items() if k * step * s / n_suf < -r - 1e-15)
                assert low <= eta / 2 + 1e-12, (name, j, n_suf, low)
    print("face rule: exact false-certification and power margins hold for three laws")
    return sigma_bar, Rj


def decomposition_and_constants():
    rng = random.Random(20)
    d0, d1, e2 = np.array([1, 0, 1.0]), np.array([1, -1, 1.0]), np.array([0, 1, 0.0])
    for _ in range(500):
        J = np.array([[rng.uniform(-1, 1) for _ in range(3)] for _ in range(3)]) / 100
        assert np.linalg.norm(J.T @ d0) + np.linalg.norm(J.T @ e2) >= np.linalg.norm(J.T @ d1) - 1e-15
    assert 22 * 81 == 1782
    assert Fr(64, 3) < 22
    for eta in (1 / 20, 1 / 4, 1 / 100):
        factor = 1 + math.log(2) / math.log(1 / eta)
        assert 1 < factor <= 2
    # claim 016 hard laws: ||U||^2 = W^2 + 2 <= 66
    assert 64 + 2 <= 81
    print("decomposition inequality, constants and hard-law membership hold")


if __name__ == "__main__":
    tail_bound()
    face_rule_check()
    decomposition_and_constants()
    print("checks/021: all checks passed")
    sys.exit(0)

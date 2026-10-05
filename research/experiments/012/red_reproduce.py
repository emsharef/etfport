"""Red's reproduction of experiment 012, written from the registered Design without reading run.py.

- Part A exactly: the lattice law, rho and the power bound eps + sqrt(1 - rho^(2N)).
- Part C's two gates exactly, with no Monte Carlo: the law of the sample-mean error comes from repeated
  FFT convolution of the lattice law, and each gate's size and power are tail sums of that law.
- Part B's Neyman-Pearson benchmark by red's own Monte Carlo, with seeds independent of the analyst's.
- Part D exactly.
The alpha-driven comparison at the end is red's extrapolation (normal affinity), not part of the Design.

Usage: uv run python experiments/012/red_reproduce.py
"""
import math
import re
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SD, h = 0.06095, 1 / 3000
K = int(math.floor(4 * SD / h))                  # truncation at +-4 target SDs, on the lattice
ks = np.arange(-K, K + 1)
D0, MU = 0.3, 0.0184


def law(s):
    p = np.exp(-(ks * h) ** 2 / (2 * s * s))
    return p / p.sum()


lo, hi = 0.03, 0.12                               # bisection for the scale giving SD = 0.06095
for _ in range(200):
    mid = (lo + hi) / 2
    sd = math.sqrt(law(mid) @ (ks * h) ** 2)
    lo, hi = (mid, hi) if sd < SD else (lo, mid)
P = law((lo + hi) / 2)
print(f"lattice points {len(ks)}, H = {K * h:.5f}, SD = {math.sqrt(P @ (ks * h) ** 2):.6f}, mean {P @ ks * h:.1e}")


def rho(m):
    return float(np.sum(np.sqrt(P[m:] * P[:len(P) - m]))) if m else 1.0


def mean_error_law(N):
    """Law of the sum of N lattice indices, by FFT convolution (float)."""
    size = N * (len(P) - 1) + 1
    n = 1 << (size - 1).bit_length()
    f = np.fft.rfft(P, n) ** N
    q = np.fft.irfft(f, n)[:size]
    q = np.clip(q, 0, None)
    return q / q.sum(), -N * K                     # probabilities, index offset of the sum


def main():
    fails = []
    rep = {}
    for line in open(HERE.parent / "012-m4-nonidentifying-limits.md"):
        c = [x.strip() for x in line.split("|")]
        if len(c) == 13 and c[1] in ("zero",) and re.match(r"^\d", c[2]):
            rep[(int(c[2]), int(c[3]), c[4])] = [float(c[5]), float(c[6].split()[0]), float(c[8]), float(c[10]), float(c[11])]
    print("\n| gap | years | m | rho | bound eps=1/20 | bound eps=1/4 | NP power 1/20 (red MC, R=1e5) | sample-mean gate power / false 1/20 | claim-015 gate power 1/20 |")
    print("|---|---|---|---|---|---|---|---|---|")
    rng = np.random.default_rng(912)
    worst = 0.0
    for gap in (2, 5, 10, 25):
        m = round(gap * 1e-4 / (D0 * h))
        r1 = rho(m)
        for N, yrs in ((40, 10), (80, 20), (160, 40)):
            b = {eps: eps + math.sqrt(1 - r1 ** (2 * N)) for eps in (0.05, 0.25)}
            q, off = mean_error_law(N)
            S = (np.arange(len(q)) + off) * h / N           # sample-mean error values
            tail = np.cumsum(q[::-1])[::-1]                 # P(error >= S[j])
            res = {}
            for eps in (0.05, 0.25):
                # sample-mean gate: r = (1 - eps) quantile of |error|; certify iff lambda_hat - lambda_0 > r
                order = np.argsort(np.abs(S), kind="stable")
                cum = np.cumsum(q[order])
                r = abs(S[order][np.searchsorted(cum, 1 - eps - 1e-15)])
                false = q[S > r + 1e-15].sum()
                power = q[S + m * h > r + 1e-15].sum()
                rH = K * h * math.sqrt(2 * math.log(2 / eps) / N)
                powH = q[S + m * h > rH].sum()
                # Neyman-Pearson on the full history (red's MC: 100,000 null and 100,000 independent
                # alternative histories; reusing one sample for both biases the critical value's error)
                logP = np.log(np.where(P > 0, P, 1e-300))
                idx = rng.choice(len(P), size=(100000, N), p=P)
                def llr(i):        # log p_1(x)/p_0(x) for null-indexed draws i (alt law = shift by m)
                    j = i - m
                    return np.where(j >= 0, logP[np.clip(j, 0, None)], -np.inf) - logP[i]
                null = llr(idx).sum(1)
                crit = np.quantile(null, 1 - eps)
                alt_idx = rng.choice(len(P), size=(100000, N), p=P)   # under lambda_1, x = lambda_1 + k h: null index k + m
                j = alt_idx + m
                alt = (np.where(j < len(P), logP[np.clip(j - m, 0, len(P) - 1)] - logP[np.clip(j, 0, len(P) - 1)], np.inf)).sum(1)
                npp = float((alt > crit).mean())
                res[eps] = (power, false, powH, npp)
                key = (gap, yrs, f"{eps:.2f}")
                if key in rep:
                    rb, rnp, r15, rsm, rsmf = rep[key]
                    worst = max(worst, abs(b[eps] - rb) / 5e-5, abs(power - rsm) / 0.005, abs(false - rsmf) / 0.005,
                                abs(powH - r15) / 1e-4, abs(npp - rnp) / 0.01)
            print(f"| {gap} | {yrs} | {m} | {r1:.8f} | {b[0.05]:.4f} | {b[0.25]:.4f} | {res[0.05][3]:.4f} | "
                  f"{res[0.05][0]:.4f} / {res[0.05][1]:.4f} | {res[0.05][2]:.4f} |")
    print(f"\nlargest deviation from the reported table in tolerance units (bound 5e-5; gates 0.005; NP 0.01): {worst:.2f}")
    if worst > 1:
        fails.append("deviation from reported table beyond tolerance")
    # Part D
    print("\nclaim 015 lengths at eps = 1/20 (quarters): " + "; ".join(
        f"{g} bp: {(D0 * K * h / (g * 1e-4)) ** 2 * math.log(20) / (4 * math.pi ** 2):,.0f} / "
        f"{32 * (D0 * K * h / (g * 1e-4)) ** 2 * math.log(40):,.0f}" for g in (2, 5, 10, 25)))
    # Red's extrapolation: the same bound if the gap came from alpha with 2%/quarter residual volatility (normal affinity).
    print("alpha-driven comparison (normal affinity, residual SD 2%/q, gap = alpha shift): bound at eps = 1/20, 10/20/40 y: " +
          "; ".join(f"{g} bp: " + ", ".join(f"{0.05 + math.sqrt(1 - math.exp(-(g * 1e-4) ** 2 / (8 * 0.02 ** 2)) ** (2 * N)):.3f}"
                                           for N in (40, 80, 160)) for g in (2, 5, 10, 25)))
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

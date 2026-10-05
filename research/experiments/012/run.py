"""Experiment 012: limits of learning at calibrated volatility with a non-identifying law (M4, D3).
Registered design: experiments/012-m4-nonidentifying-limits.md.

Claim 015's scalar M4 geometry: only the unspanned (HML) premium lambda is unknown; alpha is known zero and
the ETF premium mu is known. One quarter's public observation is x = lambda + Z. Z has a lattice-discretized
normal law with step h and the calibrated HML quarterly SD, truncated at +-4 SD (so |Z| <= H), and parameter
gaps are lattice multiples, so histories under nearby parameters overlap (no identification).
Parts:
 A  law and non-identification: exact single-quarter Hellinger affinity rho, history affinity rho^N, and the
    exact bound on ANY level-eps test's power at the alternative: eps + sqrt(1 - rho^(2N)).
 B  full-history benchmark: Neyman-Pearson likelihood-ratio test of the boundary null lambda_0 (G_* = 0)
    against lambda_1 = lambda_0 + delta/D, Monte Carlo (critical value from null draws), common random numbers.
 C  gates: (i) claim 015's conservative certificate (Hoeffding radius; certified valid, formalized claim);
    (ii) a sample-mean gate with the critical value from the law of the sample mean computed by float
    convolution ("numerically calibrated", not certified), approximating M4's exact-quantile gate.
 D  claim 015's necessary and sufficient lengths (this law belongs to its class K_H); claim 016 not applicable.
"""
from __future__ import annotations

import json
import math
import time
from pathlib import Path

import numpy as np
from scipy.signal import fftconvolve

HERE = Path(__file__).resolve().parent
SIG = 0.06095                       # data: HML quarterly SD, experiment 001 (1963Q3-2025Q2)
MU = 0.0184                         # data: Mkt-RF quarterly mean, experiment 001 (ETF premium, known)
d = 0.3                             # assumed: active fund's HML loading (as in experiments 006, 011)
H_STEP = 1 / 3000                   # lattice step (3.33 bp); gaps delta/D are integer multiples at D = 0.3
TRUNC = 4.0                         # truncation at +-4 SD, so |Z| <= H = 4 SD
GAPS_BP = [2, 5, 10, 25]
NS = [40, 80, 160]
EPS = [1 / 20, 1 / 4]
COSTS = {"zero": 0.0, "5 bp purchase": 0.0005}   # assumed purchase rates kappa_A = kappa_E (sale rates zero)
R = 100_000
SEED = 2012


def lattice_law():
    K = int(math.floor(TRUNC * SIG / H_STEP))
    k = np.arange(-K, K + 1)
    # choose the normal scale s so the discretized, truncated law has SD exactly SIG (bisection)
    lo, hi = 0.5 * SIG, 2 * SIG
    for _ in range(200):
        s = (lo + hi) / 2
        w = np.exp(-0.5 * (k * H_STEP / s) ** 2)
        w /= w.sum()
        sd = math.sqrt(float((w * (k * H_STEP) ** 2).sum()))
        lo, hi = (s, hi) if sd < SIG else (lo, s)
    return k, w, sd, K * H_STEP


def geometry(kappa):
    """Claim 015: A = min(bar a, 1/(1+kappa_A)) with bar a = 1; D = d A; lambda_0 from its formula."""
    A = min(1.0, 1 / (1 + kappa))
    D = d * A
    qE = (MU - kappa) / (1 + kappa)
    lam0 = (kappa + (1 + kappa) * qE) / d
    return A, D, lam0


def mean_law(w, N):
    """Law of the sum of N iid lattice indices (float convolution by repeated squaring)."""
    res = np.array([1.0])
    base = w.copy()
    n = N
    while n:
        if n & 1:
            res = np.clip(fftconvolve(res, base), 0, None)
        n >>= 1
        if n:
            base = np.clip(fftconvolve(base, base), 0, None)
            base /= base.sum()
        res /= res.sum()
    return res   # index j corresponds to sum of indices = j - N*K


def main() -> None:
    t0 = time.time()
    k, w, sd, H = lattice_law()
    K = int(k[-1])
    logw = np.log(w)
    out = dict(law=dict(points=len(k), step=H_STEP, sd=sd, target_sd=SIG, H=H, mean=float((w * k).sum() * H_STEP)))
    print("### Part A: law and non-identification\n")
    print(f"Lattice points {len(k)}, step {H_STEP:.6f}, truncation H = {H:.4f}, SD {sd:.6f} (target {SIG}), mean "
          f"{out['law']['mean']:.2e}. Every history under lambda_0 has positive probability under lambda_1 and vice "
          "versa except at the truncation edges (overlap measured below).\n")
    rng = np.random.default_rng(SEED)
    Z = {N: rng.choice(len(k), size=(R, N), p=w).astype(np.int32) for N in NS}   # common random numbers (indices)
    rows, arows = [], []
    for cname, kappa in COSTS.items():
        A, D, lam0 = geometry(kappa)
        for g in GAPS_BP:
            m = int(round(g / 1e4 / D / H_STEP))
            delta = D * m * H_STEP                     # Deviation 1: realized, lattice-aligned gap
            rho = float(np.sum(np.sqrt(w[m:] * w[:-m])))            # affinity of x under lambda_0 and lambda_1
            # per-observation LLR at index i (x - lambda_0 = i*h): log w[i - m] - log w[i]; -inf/inf off support
            llr_idx = np.full(len(k), -np.inf)
            llr_idx[m:] = logw[:-m] - logw[m:]
            for N in NS:
                bound = {e: e + math.sqrt(max(0.0, 1 - rho ** (2 * N))) for e in EPS}
                arows.append(dict(costs=cname, gap_bp=g, gap_real_bp=delta * 1e4, N=N, years=N / 4, m=m, rho=rho, rho_N=rho ** N,
                                  power_upper={str(e): min(1.0, b) for e, b in bound.items()}))
                z = Z[N]
                # null: observed index = z; alternative: observed index = z + m (lattice shift)
                llr_null = np.where(z >= m, llr_idx[np.clip(z, 0, len(k) - 1)], -np.inf).sum(axis=1)
                zi = z + m
                llr_alt = np.where(zi < len(k), llr_idx[np.clip(zi, 0, len(k) - 1)], np.inf).sum(axis=1)
                lam_hat_err = (z - K).mean(axis=1) * H_STEP                  # sample mean error (null)
                ml = mean_law(w, N)
                cdf_abs = None
                # law of |mean error|: sums s in [-N K, N K]
                sums = np.arange(len(ml)) - N * K
                absv = np.abs(sums) * H_STEP / N
                order = np.argsort(absv)
                cum = np.cumsum(ml[order])
                for e in EPS:
                    c = np.quantile(llr_null, 1 - e)
                    np_power = float(np.mean(llr_alt > c))
                    np_size = float(np.mean(llr_null > c))
                    r_exact = float(absv[order][np.searchsorted(cum, 1 - e)])
                    r_hoeff = H * math.sqrt(2 * math.log(2 / e) / N)
                    res = {}
                    for gname, r in (("claim015 (certified)", r_hoeff), ("sample-mean, numerically calibrated", r_exact)):
                        # certify iff D (lambda_hat - r - lambda_0) > 0, i.e. lambda_hat - lambda_0 > r
                        cert_null = np.mean(lam_hat_err > r)                  # at lambda_0: false certification
                        cert_alt = np.mean(lam_hat_err + delta / D > r)       # at lambda_1: power
                        res[gname] = (float(cert_null), float(cert_alt), r)
                    rows.append(dict(costs=cname, gap_bp=g, gap_real_bp=delta * 1e4, N=N, years=N / 4, eps=e, np_power=np_power,
                                     np_power_se=math.sqrt(np_power * (1 - np_power) / R), np_size=np_size,
                                     upper=min(1.0, bound[e]),
                                     gate015_false=res["claim015 (certified)"][0], gate015_power=res["claim015 (certified)"][1],
                                     gate015_r=res["claim015 (certified)"][2],
                                     gatemean_false=res["sample-mean, numerically calibrated"][0],
                                     gatemean_power=res["sample-mean, numerically calibrated"][1],
                                     gatemean_r=res["sample-mean, numerically calibrated"][2]))
    print("| costs | target gap (bp/q) | realized gap | years | lattice shift m | rho (1 obs) | rho^N | power upper bound eps=1/20 | eps=1/4 |")
    print("|---|---|---|---|---|---|---|---|---|")
    for a in arows:
        print(f"| {a['costs']} | {a['gap_bp']} | {a['gap_real_bp']:.3f} | {a['years']:.0f} | {a['m']} | {a['rho']:.8f} | {a['rho_N']:.6f} | "
              f"{a['power_upper']['0.05']:.4f} | {a['power_upper']['0.25']:.4f} |")
    print(f"\n### Parts B-C: full-history benchmark and gates (Monte Carlo, R = {R:,}, common random numbers)\n")
    print("| costs | gap (bp/q) | years | eps | exact upper bound | NP benchmark power (SE) | NP size | claim-015 gate power | "
          "claim-015 gate false cert | sample-mean gate power | sample-mean gate false cert |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['costs']} | {r['gap_bp']} | {r['years']:.0f} | {r['eps']} | {r['upper']:.4f} | {r['np_power']:.4f} "
              f"({r['np_power_se']:.4f}) | {r['np_size']:.4f} | {r['gate015_power']:.4f} | {r['gate015_false']:.4f} | "
              f"{r['gatemean_power']:.4f} | {r['gatemean_false']:.4f} |")
    print("\n### Part D: claim 015's lengths for this law's class K_H (worst case over the class, not this law)\n")
    print("| costs | gap (bp/q) | D | H | necessary (quarters / years) | sufficient (quarters / years) |\n|---|---|---|---|---|---|")
    for cname, kappa in COSTS.items():
        A, D, lam0 = geometry(kappa)
        for g in GAPS_BP:
            delta = g / 1e4
            ratio = (D * H / delta) ** 2
            nec = ratio * math.log(20) / (4 * math.pi ** 2)
            suf = 32 * ratio * math.log(40)
            print(f"| {cname} | {g} | {D:.4f} | {H:.4f} | {nec:,.0f} / {nec / 4:,.0f} | {suf:,.0f} / {suf / 4:,.0f} |")
    print("\nClaim 016 is not evaluated: this scalar law is not in its class K_J (isotropic 3-D U, ||J|| <= 1/100).")
    (HERE / "results.json").write_text(json.dumps(dict(law=out["law"], affinity=arows, rows=rows), indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

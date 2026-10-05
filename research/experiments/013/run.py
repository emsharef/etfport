"""Experiment 013 (D5): known-law vs law-free certification against the optimized ETF class, under
misspecified laws and repeated quarterly reviews. Registered design: experiments/013-d5-law-free-certificates.md.

Geometry (claim 016): active fund B^A = (1, 0) (unspanned factor 1), ETF B^E = (0, 1), gamma = 0, zero costs,
alpha unknown. Whole-class advantage of the all-active action: Adv = min(m_0, m_1), m_j = d_j' theta,
d_0 = (1, 0, 1) (vs cash), d_1 = (1, -1, 1) (vs the ETF). Observation X = theta + J U, J = diag(SDs).
Rules at review n (reviews every quarter n = 4..160):
 (a) known-law whole-class gate (claim 016 part 3): ell = min_j [d_j' theta_hat_n - r_n sigma_j],
     r_n = sqrt(t_{n,eta}/n), t exact under the ASSUMED two-point law (valid only for that law, one review);
 (a*) the same gate with t simulated under the TRUE law (oracle; numerical, not certified);
 (b) law-free face-by-face gate: two-sided normal-mixture confidence sequence (howard2021time, eq. (14), p. 9)
     for each face j at alpha = eta/2, sub-Gaussian by boundedness |d_j' J U| <= B_j (Hoeffding's lemma,
     variance process V_n = n B_j^2); ell = min_j [d_j' theta_hat_n - u_j(n B_j^2)/n]; valid for every law with
     |U_k| <= b and time-uniform;
 (c) naive plug-in: min_j d_j' theta_hat_n > 0.
Certify iff ell > delta_econ = 0 (the certificate implies the all-active action is the plug-in optimum).
"""
from __future__ import annotations

import json
import math
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SD = np.array([0.06095, 0.08540, 0.02])        # data: HML and Mkt-RF quarterly SDs (exp 001); alpha residual assumed
LAM = (0.00897, 0.0184)                        # data: HML and Mkt-RF quarterly means (exp 001)
D = np.array([[1.0, 0.0, 1.0], [1.0, -1.0, 1.0]])
SIG_J = np.sqrt((D ** 2 * SD ** 2).sum(axis=1))   # sigma_j = sqrt(d_j' Omega d_j), Omega = diag(SD^2)
B_U = 4.0                                     # law-free class: |U_k| <= 4 (covers every law below)
B_J = B_U * (np.abs(D) * SD).sum(axis=1)      # |d_j' J U| <= B_J
ETAS = [0.05, 0.25]
REVIEWS = np.arange(4, 161)
SINGLE = [40, 80, 160]
GAPS_BP = [0, 5, 10, 25, 50, 100]
R = 20_000
R_CAL = 200_000
RHO_N = 80                                    # mixture tuning: rho = B_j^2 * RHO_N (pre-registered)
SEED = 2013


def laws():
    """Each: (values, probabilities) of a scalar U with mean 0, variance 1, |U| <= 4; used iid per coordinate."""
    h = 1 / 50
    k = np.arange(-200, 201)
    lo, hi = 0.5, 2.0
    for _ in range(200):
        s = (lo + hi) / 2
        w = np.exp(-0.5 * (k * h / s) ** 2); w /= w.sum()
        v = (w * (k * h) ** 2).sum()
        lo, hi = (s, hi) if v < 1 else (lo, s)
    return {
        "two-point (assumed)": (np.array([-1.0, 1.0]), np.array([0.5, 0.5])),
        "three-point": (np.array([-3.0, 0.0, 3.0]), np.array([1 / 18, 8 / 9, 1 / 18])),
        "skewed right": (np.array([-0.5, 2.0]), np.array([0.8, 0.2])),
        "skewed left": (np.array([0.5, -2.0]), np.array([0.8, 0.2])),
        "lattice normal (exp 012 shape)": (k * h, w),
    }


def t_two_point(n, eta):
    """Exact 1-eta quantile of T_n = sum_k (2B_k - n)^2 / n, B_k ~ Bin(n, 1/2) iid (the assumed law)."""
    from collections import defaultdict
    from math import comb
    one = defaultdict(int)
    for b in range(n + 1):
        one[(2 * b - n) ** 2] += comb(n, b)
    dist = {0: 1}
    for _ in range(3):
        nxt = defaultdict(int)
        for x, wx in dist.items():
            for y, wy in one.items():
                nxt[x + y] += wx * wy
        dist = nxt
    tot, acc = 2 ** (3 * n), 0
    for x in sorted(dist):
        acc += dist[x]
        if acc / tot >= 1 - eta:
            return x / n


def t_simulated(vals, p, n, eta, rng):
    U = rng.choice(vals, size=(R_CAL, n, 3), p=p) if n <= 40 else None
    if U is None:                                  # sums of n draws via repeated sampling in chunks
        S = np.zeros((R_CAL, 3))
        for _ in range(n):
            S += rng.choice(vals, size=(R_CAL, 3), p=p)
    else:
        S = U.sum(axis=1)
    T = (S ** 2).sum(axis=1) / n
    return float(np.quantile(T, 1 - eta))


def mixture_boundary(v, rho, alpha):
    """howard2021time eq. (14): two-sided normal mixture boundary, l0 = 1."""
    return np.sqrt((v + rho) * np.log((v + rho) / (alpha ** 2 * rho)))


def theta_for_gap(g):
    """ETF face binds: m_1 = lambda_1 - lambda_2 + alpha = g, m_0 = lambda_1 + alpha > m_1."""
    alpha = g - LAM[0] + LAM[1]
    return np.array([LAM[0], LAM[1], alpha])


def main() -> None:
    t0 = time.time()
    rng_cal = np.random.default_rng(SEED + 1)
    L = laws()
    t_assumed = {eta: np.array([t_two_point(int(n), eta) for n in REVIEWS]) for eta in ETAS}
    rows = []
    for lname, (vals, p) in L.items():
        rng = np.random.default_rng(SEED)                       # common random numbers across gaps and rules
        idx = rng.choice(len(vals), size=(R, REVIEWS[-1], 3), p=p)
        U = vals[idx]
        Ucum = np.cumsum(U, axis=1)                             # (R, n, 3)
        n_all = np.arange(1, REVIEWS[-1] + 1)
        err = Ucum / n_all[None, :, None] * SD[None, None, :]   # theta_hat_n - theta
        t_true = {eta: {n: t_simulated(vals, p, n, eta, rng_cal) for n in SINGLE} for eta in ETAS}
        for g in GAPS_BP:
            th = theta_for_gap(g / 1e4)
            m = D @ th                                          # true face margins
            G = max(0.0, float(m.min()))
            mhat = m[None, None, :] + np.einsum("rnk,jk->rnj", err, D)   # (R, n, 2)
            for eta in ETAS:
                sel = REVIEWS - 1
                mh = mhat[:, sel, :]                            # (R, reviews, 2)
                r_known = np.sqrt(t_assumed[eta] / REVIEWS)
                ell_a = (mh - r_known[None, :, None] * SIG_J[None, None, :]).min(axis=2)
                u = np.stack([mixture_boundary(REVIEWS * B_J[j] ** 2, B_J[j] ** 2 * RHO_N, eta / 2) / REVIEWS
                              for j in range(2)], axis=1)       # (reviews, 2)
                ell_b = (mh - u[None, :, :]).min(axis=2)
                ell_c = mh.min(axis=2)
                certs = {"(a) known-law, assumed two-point": ell_a > 0, "(b) law-free CS": ell_b > 0,
                         "(c) plug-in": ell_c > 0}
                for rule, C in certs.items():
                    ever = C.any(axis=1)
                    first = np.where(ever, C.argmax(axis=1), -1)
                    row = dict(law=lname, gap_bp=g, G_bp=G * 1e4, eta=eta, rule=rule,
                               ever_certify=float(ever.mean()),
                               median_first_review_years=(float(np.median(REVIEWS[first[ever]])) / 4 if ever.any() else None))
                    for n in SINGLE:
                        c = C[:, n - REVIEWS[0]]
                        row[f"single_{n}"] = float(c.mean())
                    row["missed_gain_bp_by_40y"] = G * 1e4 * float(1 - ever.mean())
                    rows.append(row)
                # (a*) oracle-calibrated known-law gate at the single reviews only
                row = dict(law=lname, gap_bp=g, G_bp=G * 1e4, eta=eta, rule="(a*) known-law, TRUE law (oracle, simulated t)",
                           ever_certify=None, median_first_review_years=None, missed_gain_bp_by_40y=None)
                for n in SINGLE:
                    r = math.sqrt(t_true[eta][n] / n)
                    ell = (mhat[:, n - 1, :] - r * SIG_J[None, :]).min(axis=1)
                    row[f"single_{n}"] = float((ell > 0).mean())
                rows.append(row)
    se = lambda p: math.sqrt(max(p * (1 - p), 1e-12) / R)  # noqa: E731
    print(f"sigma_j = {SIG_J.round(5).tolist()}, B_j = {B_J.round(4).tolist()}, R = {R:,}\n")
    print("### Null (G_* = 0; ETF face binds): false certification\n")
    print("| law | eta | rule | single review 10 y | 20 y | 40 y | ever, quarterly reviews 1-40 y |\n|---|---|---|---|---|---|---|")
    for r in rows:
        if r["gap_bp"] == 0:
            ev = "n/a" if r["ever_certify"] is None else f"{r['ever_certify']:.4f}"
            print(f"| {r['law']} | {r['eta']} | {r['rule']} | {r['single_40']:.4f} | {r['single_80']:.4f} | {r['single_160']:.4f} | {ev} |")
    print("\n### Alternatives: power and missed gain (two-point and lattice-normal laws)\n")
    print("| law | eta | G_* (bp/q) | rule | single 10 y | 20 y | 40 y | ever by 40 y | median first review (y) | missed gain by 40 y (bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        if r["gap_bp"] > 0 and r["law"] in ("two-point (assumed)", "lattice normal (exp 012 shape)"):
            ev = "n/a" if r["ever_certify"] is None else f"{r['ever_certify']:.4f}"
            md = "n/a" if r["median_first_review_years"] is None else f"{r['median_first_review_years']:.1f}"
            mg = "n/a" if r["missed_gain_bp_by_40y"] is None else f"{r['missed_gain_bp_by_40y']:.2f}"
            print(f"| {r['law']} | {r['eta']} | {r['G_bp']:.0f} | {r['rule']} | {r['single_40']:.4f} | {r['single_80']:.4f} | "
                  f"{r['single_160']:.4f} | {ev} | {md} | {mg} |")
    print(f"\nMonte Carlo SE: at most {se(0.5):.4f}; at p = 0.05, {se(0.05):.4f}.")
    print("\n### Claim 016's necessary length at the calibrated sigma (order of magnitude; outside its ||J|| <= 1/100 range)\n")
    s2 = float(SIG_J.max() ** 2)
    print("| G_* (bp/q) | necessary quarters (years), eps = 1/20 |\n|---|---|")
    for g in GAPS_BP[1:]:
        nq = s2 / (g / 1e4) ** 2 * math.log(20) / (16 * math.pi ** 2)
        print(f"| {g} | {nq:,.0f} ({nq / 4:,.0f}) |")
    (HERE / "results.json").write_text(json.dumps(rows, indent=1))
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

"""Experiment 014 (D5): variance-adaptive law-free certification, a two-face shared-component bound, and a
stress test of the known-law gate. Registered design: experiments/014-d5-variance-adaptive.md.
Same geometry, calibration and law set as experiment 013 (claim 016's two faces). Rules tested; their
validity is the cited theorems', not established here.
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location("exp013_run", HERE.parent / "013" / "run.py")
e13 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(e13)          # geometry, laws, known-law critical values, range-based CS

SD, LAM, D = e13.SD, e13.LAM, e13.D
SIG_J, B_J = e13.SIG_J, e13.B_J
REVIEWS, SINGLE = e13.REVIEWS, e13.SINGLE
ETAS = [0.05, 0.25]
GAPS_BP = [0, 5, 10, 25, 50, 100]
R = 20_000
SEED = 2014
# Known domain (assumed) giving known observation ranges for the empirical-Bernstein rules:
# lambda_1, lambda_2 in [-0.10, 0.10], alpha in [-0.05, 0.05]; |U_k| <= 4 as in experiment 013's class.
M_RANGE = {"face0": (-0.15, 0.15), "face1": (-0.25, 0.25), "u": (-0.15, 0.15), "lam2": (-0.10, 0.10)}
OBS_B = {"face0": B_J[0], "face1": B_J[1], "u": 4 * (SD[0] + SD[2]), "lam2": 4 * SD[1]}
# Polynomial stitched boundary (howard2021time Theorem 1, eq. (10)) with the worked example's choices
# (eta_s = 2, m = 1, s = 1.4) on data rescaled to [0, 1]; linear-term scale 2, which reproduces example (24).
ETA_S, M_S, S_S = 2.0, 1.0, 1.4
K1 = (ETA_S ** 0.25 + ETA_S ** -0.25) / math.sqrt(2)
K2 = (math.sqrt(ETA_S) + 1) / 2
C_LIN = 2.0


def ell(v, alpha):
    return S_S * np.log(np.log(ETA_S * v / M_S)) + math.log(zeta(S_S) / (alpha * math.log(ETA_S) ** S_S))


def stitched(v, alpha):
    v = np.maximum(v, M_S)
    L = ell(v, alpha)
    return K1 * np.sqrt(v * L) + C_LIN * K2 * L


def check_example_24():
    """At alpha = 0.025 (95% two-sided in Theorem 4) the boundary should match (24):
    1.7 sqrt(V (loglog(2V) + 3.8)) + 3.4 loglog(2V) + 13, to the printed rounding."""
    V = np.array([1.0, 10.0, 100.0, 1000.0])
    ours = stitched(V, 0.025)
    paper = 1.7 * np.sqrt(V * (np.log(np.log(2 * V)) + 3.8)) + 3.4 * np.log(np.log(2 * V)) + 13
    return float(np.max(np.abs(ours / paper - 1)))


def eb_lower(Y, key, alpha):
    """howard2021time Theorem 4: time-uniform lower bound on the mean of Y (R, T), coverage 1 - 2 alpha."""
    lo, hi = M_RANGE[key][0] - OBS_B[key], M_RANGE[key][1] + OBS_B[key]
    Z = (Y - lo) / (hi - lo)
    T = Y.shape[1]
    t = np.arange(1, T + 1)
    cs = np.cumsum(Z, axis=1)
    pred = np.concatenate([np.full((Z.shape[0], 1), 0.5), cs[:, :-1] / t[None, :-1]], axis=1)
    V = np.cumsum((Z - pred) ** 2, axis=1)
    rad = stitched(V, alpha) / t[None, :]
    return lo + (hi - lo) * (cs / t[None, :] - rad)


def mp_lower(Y, key, n, delta):
    """maurer2009empirical Theorem 4 (applied to 1 - Z): fixed-n lower bound, coverage 1 - delta."""
    lo, hi = M_RANGE[key][0] - OBS_B[key], M_RANGE[key][1] + OBS_B[key]
    Z = (Y[:, :n] - lo) / (hi - lo)
    Vn = Z.var(axis=1, ddof=1)
    rad = np.sqrt(2 * Vn * math.log(2 / delta) / n) + 7 * math.log(2 / delta) / (3 * (n - 1))
    return lo + (hi - lo) * (Z.mean(axis=1) - rad)


def theta_for_gap(g):
    return np.array([LAM[0], LAM[1], g - LAM[0] + LAM[1]])


def summarize(C, G, name, extra):
    ever = C.any(axis=1)
    first = np.where(ever, C.argmax(axis=1), -1)
    row = dict(rule=name, ever=float(ever.mean()),
               median_first_years=(float(np.median(REVIEWS[first[ever]])) / 4 if ever.any() else None),
               missed_gain_bp=G * 1e4 * float(1 - ever.mean()), **extra)
    for n in SINGLE:
        row[f"single_{n}"] = float(C[:, n - REVIEWS[0]].mean())
    return row


def main_question(L, t_assumed):
    rows, widths = [], {}
    for lname, (vals, p) in L.items():
        rng = np.random.default_rng(SEED)
        U = vals[rng.choice(len(vals), size=(R, REVIEWS[-1], 3), p=p)]
        E = U * SD[None, None, :]                               # observation errors J U
        sel = REVIEWS - 1
        for g in GAPS_BP:
            th = theta_for_gap(g / 1e4)
            m = D @ th
            G = max(0.0, float(m.min()))
            X = th[None, None, :] + E                           # (R, T, 3)
            Y0, Y1 = X[..., 0] + X[..., 2], X[..., 0] - X[..., 1] + X[..., 2]
            Yu, Y2 = Y0, X[..., 1]
            T = np.arange(1, REVIEWS[-1] + 1)
            mh0, mh1 = np.cumsum(Y0, 1) / T, np.cumsum(Y1, 1) / T
            for eta in ETAS:
                rk = np.sqrt(t_assumed[eta] / REVIEWS)
                ell_a = np.minimum(mh0[:, sel] - rk * SIG_J[0], mh1[:, sel] - rk * SIG_J[1])
                u0 = e13.mixture_boundary(REVIEWS * B_J[0] ** 2, B_J[0] ** 2 * e13.RHO_N, eta / 2) / REVIEWS
                u1 = e13.mixture_boundary(REVIEWS * B_J[1] ** 2, B_J[1] ** 2 * e13.RHO_N, eta / 2) / REVIEWS
                ell_b0 = np.minimum(mh0[:, sel] - u0, mh1[:, sel] - u1)
                lb0, lb1 = eb_lower(Y0, "face0", eta / 4), eb_lower(Y1, "face1", eta / 4)
                ell_b1 = np.minimum(lb0[:, sel], lb1[:, sel])
                lbu = eb_lower(Yu, "u", eta / 4)
                # upper bound on lambda_2: lower bound on the mean of -X_2 (range symmetric)
                ub2 = -eb_lower(-Y2, "lam2", eta / 4)
                ell_c = lbu[:, sel] - np.maximum(0.0, ub2[:, sel])
                ell_d = np.minimum(mh0[:, sel], mh1[:, sel])
                for name, ellx in (("(a) known-law gate (assumed two-point)", ell_a),
                                   ("(b0) range-based CS (exp 013)", ell_b0),
                                   ("(b1) empirical-Bernstein CS, face by face", ell_b1),
                                   ("(c) shared-component EB bound", ell_c),
                                   ("(d) plug-in", ell_d)):
                    rows.append(summarize(ellx > 0, G, name, dict(law=lname, gap_bp=g, G_bp=G * 1e4, eta=eta)))
                # Maurer-Pontil, single reviews only (not time-uniform): per face one-sided at delta = eta/2
                row = dict(rule="(b2) Maurer-Pontil EB, single review", law=lname, gap_bp=g, G_bp=G * 1e4, eta=eta,
                           ever=None, median_first_years=None, missed_gain_bp=None)
                for n in SINGLE:
                    ok = np.minimum(mp_lower(Y0, "face0", n, eta / 2), mp_lower(Y1, "face1", n, eta / 2)) > 0
                    row[f"single_{n}"] = float(ok.mean())
                rows.append(row)
                if g == 0 and lname == "lattice normal (exp 012 shape)":
                    widths[str(eta)] = {"known-law face0/face1 (bp)": [float(rk[-1] * SIG_J[0] * 1e4), float(rk[-1] * SIG_J[1] * 1e4)],
                                        "range CS face0/face1 (bp)": [float(u0[-1] * 1e4), float(u1[-1] * 1e4)],
                                        "EB CS face0/face1, median (bp)": [float(np.median(mh0[:, -1] - lb0[:, -1]) * 1e4),
                                                                          float(np.median(mh1[:, -1] - lb1[:, -1]) * 1e4)]}
    return rows, widths


def stress_laws():
    out = {}
    for a in (2.0, 3.0, 5.0, 8.0):
        q = 1 / (2 * a * a)
        out[f"three-point a={a:g} (kurtosis {a * a:g})"] = (np.array([-a, 0.0, a]), np.array([q, 1 - 2 * q, q]))
    for pr in (0.2, 0.05, 0.01, 0.002):
        big, small = math.sqrt((1 - pr) / pr), math.sqrt(pr / (1 - pr))
        out[f"skew-left p={pr:g}"] = (np.array([small, -big]), np.array([1 - pr, pr]))
        out[f"skew-right p={pr:g}"] = (np.array([-small, big]), np.array([1 - pr, pr]))
    return out


def stress(t_assumed):
    rows = []
    NS = [4, 8, 12, 20, 40, 80, 160]
    for lname, (vals, p) in stress_laws().items():
        rng = np.random.default_rng(SEED + 7)
        U = vals[rng.choice(len(vals), size=(R, REVIEWS[-1], 3), p=p)]
        th = theta_for_gap(0.0)
        X = th[None, None, :] + U * SD[None, None, :]
        T = np.arange(1, REVIEWS[-1] + 1)
        mh0 = np.cumsum(X[..., 0] + X[..., 2], 1) / T
        mh1 = np.cumsum(X[..., 0] - X[..., 1] + X[..., 2], 1) / T
        for eta in ETAS:
            rk = np.sqrt(t_assumed[eta] / REVIEWS)
            C = np.minimum(mh0[:, REVIEWS - 1] - rk * SIG_J[0], mh1[:, REVIEWS - 1] - rk * SIG_J[1]) > 0
            row = dict(law=lname, eta=eta, ever=float(C.any(axis=1).mean()))
            for n in NS:
                row[f"n{n}"] = float(C[:, n - REVIEWS[0]].mean())
            se = lambda x: math.sqrt(max(x * (1 - x), 1e-12) / R)  # noqa: E731
            fails = [k for k in ["ever"] + [f"n{n}" for n in NS] if row[k] - 2 * se(row[k]) > eta]
            row["exceeds_eta_at"] = fails
            rows.append(row)
    return rows


def main() -> None:
    t0 = time.time()
    dev = check_example_24()
    print(f"Unit check: stitched boundary vs howard2021time example (24), max relative deviation {dev:.4f} "
          "(the example's coefficients are printed rounded)\n")
    t_assumed = {eta: np.array([e13.t_two_point(int(n), eta) for n in REVIEWS]) for eta in ETAS}
    L = e13.laws()
    rows, widths = main_question(L, t_assumed)
    print("### Main question: validity at the null (G_* = 0), all five laws\n")
    print("| law | eta | rule | single 10 y | 20 y | 40 y | ever 1-40 y |\n|---|---|---|---|---|---|---|")
    for r in rows:
        if r["gap_bp"] == 0:
            ev = "n/a" if r["ever"] is None else f"{r['ever']:.4f}"
            print(f"| {r['law']} | {r['eta']} | {r['rule']} | {r['single_40']:.4f} | {r['single_80']:.4f} | {r['single_160']:.4f} | {ev} |")
    print("\n### Main question: power, time to certify, missed gain (lattice-normal law)\n")
    print("| eta | G_* (bp/q) | rule | single 10 y | 20 y | 40 y | ever by 40 y | median first (y) | missed gain (bp) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        if r["gap_bp"] > 0 and r["law"] == "lattice normal (exp 012 shape)":
            ev = "n/a" if r["ever"] is None else f"{r['ever']:.4f}"
            md = "n/a" if r["median_first_years"] is None else f"{r['median_first_years']:.1f}"
            mg = "n/a" if r["missed_gain_bp"] is None else f"{r['missed_gain_bp']:.2f}"
            print(f"| {r['eta']} | {r['G_bp']:.0f} | {r['rule']} | {r['single_40']:.4f} | {r['single_80']:.4f} | "
                  f"{r['single_160']:.4f} | {ev} | {md} | {mg} |")
    print("\n### Certificate half-widths at 40 years (lattice-normal law, null)\n")
    for eta, w in widths.items():
        print(f"- eta = {eta}: " + "; ".join(f"{k}: {v[0]:.0f} / {v[1]:.0f}" for k, v in w.items()))
    s2 = float(SIG_J.max() ** 2)
    print("\nClaim 016 necessary length at eps = 1/20 (order of magnitude): " +
          ", ".join(f"{g} bp: {s2 / (g / 1e4) ** 2 * math.log(20) / (16 * math.pi ** 2) / 4:,.0f} y" for g in GAPS_BP[1:]))
    st = stress(t_assumed)
    print("\n### Second question: known-law gate (a) at the null under heavier tails and skew\n")
    print("| law | eta | n=4 | 8 | 12 | 20 | 40 | 80 | 160 | ever | exceeds eta (estimate - 2 SE) at |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in st:
        print(f"| {r['law']} | {r['eta']} | " + " | ".join(f"{r[f'n{n}']:.4f}" for n in (4, 8, 12, 20, 40, 80, 160)) +
              f" | {r['ever']:.4f} | {', '.join(r['exceeds_eta_at']) or 'none'} |")
    (HERE / "results.json").write_text(json.dumps(dict(example24_dev=dev, main=rows, widths=widths, stress=st), indent=1))
    print(f"\nMonte Carlo: R = {R:,} per law; SE <= 0.0035. seconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()

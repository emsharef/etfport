"""Experiment 031 report and figures (uv run python experiments/031/report.py), from summary.json."""
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
TOL = 1e-9
LAMES = [1e-6, 1e-8, 1e-10]


def main():
    S = json.load(open(HERE / "summary.json"))
    C = S["c12"]
    print("Tolerance: 1e-9 on factors and bounds, or the reference's lambda_E-convergence error.\n")
    print("## Part 1 and B3: the learning factor L_t")
    for le in LAMES:
        rows = [r for c in C if c["lamE"] == le for r in c["rows"]]
        err = max(abs(r["L"] - r["fL"]) for r in rows)
        lo = sum(r["L"] < 1 - TOL for r in rows)
        up1 = sum(r["L"] > 1 / (1 - r["kap"]) + TOL for r in rows)
        up2 = sum(r["L"] - 1 > (r["kap"] / (1 - r["kap"])) ** 2 * r["dur"] + TOL for r in rows)
        print(f"- lambda_E = {le:.0e}: {len(rows)} (cell, t); |L_ref - L_formula| max {err:.2e}; L < 1: {lo}; L > 1/(1 - kappa): {up1}; "
              f"L - 1 > (kappa/(1 - kappa))^2 Dur: {up2}")
    rows = [(c, r) for c in C if c["lamE"] == 1e-10 for r in c["rows"]]
    last = [r for c, r in rows if r["t"] == c["T"] - 1]; before = [r for c, r in rows if r["t"] < c["T"] - 1]
    print(f"- L = 1 at t = T-1: max |L - 1| {max(abs(r['L'] - 1) for r in last):.1e}; L > 1 strictly before: min L - 1 = {min(r['L'] - 1 for r in before):.2e} "
          f"({sum(r['L'] - 1 <= 1e-12 for r in before)} of {len(before)} not above 1e-12)")
    tight1 = max((r["L"] - 1) / (r["kap"] / (1 - r["kap"])) for c, r in rows if r["kap"] > 0 and r["t"] < c["T"] - 1)
    tight2 = max((r["L"] - 1) / ((r["kap"] / (1 - r["kap"])) ** 2 * r["dur"]) for c, r in rows if r["dur"] > 0 and r["t"] < c["T"] - 1)
    print(f"- slack: largest (L - 1)/(kappa/(1 - kappa)) = {tight1:.3f}; largest (L - 1)/((kappa/(1 - kappa))^2 Dur) = {tight2:.3f}")
    print(f"- weights sum to 1: max |sum w - 1| {max(abs(r['wsum'] - 1) for c, r in rows):.1e}; |g_ref - g_formula| max {max(abs(r['g'] - r['fg']) for c, r in rows):.2e}")
    for nm, v in S["named"].items():
        print(f"- {nm} (claim 036's illustration inputs): kappa_0 {v['kap']:.3f}, Dur {v['dur']:.2f}; L_0 reference {v['L']:.4f}, formula {v['fL']:.4f}; "
              f"sharper bound {v['sharper']:.4f}, first-order bound {v['first']:.4f}")
    print()
    print("## Part 2: rate and trade")
    for le in LAMES:
        rows = [r for c in C if c["lamE"] == le for r in c["rows"]]
        tr = [t for r in rows for t in r["trades"]]
        print(f"- lambda_E = {le:.0e}: g > g^S: {sum(r['g'] > r['gS'] + TOL for r in rows)}; g^S - g > bound: {sum(r['gS'] - r['g'] > r['gbound'] + TOL for r in rows)} of {len(rows)}; "
              f"identity residual max {max(abs(t['ident']) for t in tr):.1e}; |u - u^S| > bound: {sum(t['du'] > t['bound'] + TOL for t in tr)} of {len(tr)}")
    rows = [r for c in C if c["lamE"] == 1e-10 for r in c["rows"]]
    tr = [t for r in rows for t in r["trades"] if t["bound"] > 1e-12]
    print(f"- largest |u - u^S| / bound {max(t['du'] / t['bound'] for t in tr):.3f} (median {np.median([t['du'] / t['bound'] for t in tr]):.3f}); "
          f"largest constant term |c|/|h alpha_hat| {max(r['c_over_h'] for r in rows):.1e}\n")
    print("## Part 3: mean reversion")
    C3 = S["c3"]
    for le in LAMES:
        rows = [(c, r) for c in C3 if c["lamE"] == le for r in c["rows"]]
        print(f"- lambda_E = {le:.0e}: {len(rows)} (cell, t); M outside [lower, 1]: {sum(r['M'] < r['lo'] - 1e-7 or r['M'] > 1 + 1e-7 for c, r in rows)} (margin 1e-7); "
              f"|M_ref - sum w~ phi^(s-t)| max {max(abs(r['M'] - r['Mf']) for c, r in rows):.1e}; M(1) = 1: max |M - 1| at phi = 1 {max(abs(r['M'] - 1) for c, r in rows if c['phi'] == 1.0):.1e}")
    for nm, v in S["named"].items():
        d = np.diff(v["M_phi"])
        print(f"- {nm}: M_0 over 101 phi values from {v['M_phi'][0]:.4f} (phi = 0) to {v['M_phi'][-1]:.4f}; decreasing steps {int(np.sum(d < -1e-9))}")
    print()
    print("## Part 4: limits")
    C4 = S["c4"]
    for lr in (1e-4, 1e-3, 1e-2):
        rs = [c for c in C4 if c["lamr"] == lr and c["lamE"] == 1e-10]
        print(f"- lambda ratio {lr:.0e}: max L_0 - 1 {max(c['Lm1'] for c in rs):.2e}; max 1 - M_0 (phi 0.5) {max(abs(c['oneMinusM']) for c in rs):.2e}")
    for le in LAMES:
        rs = [c for c in C4 if c["lamE"] == le]
        print(f"- ETF trade's dependence at lambda_E = {le:.0e}: on premium persistence max {max(c['etf_persist'] for c in rs):.1e}, "
              f"on future premium precision max {max(c['etf_precision'] for c in rs):.1e} (ETF trades up to {max(c['etf_trade'] for c in rs):.2f})")
    print()
    print("## Not shown in claim 036 (counted, not tested)")
    L = {(c["kap0"], c["lamr"], c["T"], c["rho"], r["t"]): r["L"] for c in C if c["lamE"] == 1e-10 for r in c["rows"]}
    lam_falls = tot = 0
    for (k, lr, T, rho, t), v in L.items():
        i = [0.01, 0.1, 1.0, 10.0, 100.0].index(lr)
        if i < 4 and t < T - 1:
            tot += 1; lam_falls += L[(k, [0.01, 0.1, 1.0, 10.0, 100.0][i + 1], T, rho, t)] < v - 1e-12
    T_falls = tot2 = 0
    for (k, lr, T, rho, t), v in L.items():
        if t == 0 and T < 20:
            T2 = [2, 4, 8, 20][[2, 4, 8, 20].index(T) + 1]; tot2 += 1; T_falls += L[(k, lr, T2, rho, 0)] < v - 1e-12
    print(f"- L_t - 1 falls as lambda_A rises (next grid value): {lam_falls} of {tot} (kappa_0, lambda, T, rho, t) cells")
    print(f"- L_0 - 1 falls as T rises (next grid value): {T_falls} of {tot2} cells\n")
    print("## Level sets (figures)")
    for r in S["level1"]:
        pass
    for th in (0.01, 0.05, 0.1):
        rs = [r for r in S["level1"] if r["theta"] == th]
        print(f"- learning, theta = {th}: exact kappa_0 crossing {[None if r['exact'] is None else round(r['exact'], 3) for r in rs]}; "
              f"sharper-bound crossing {[None if r['sharper'] is None else round(r['sharper'], 3) for r in rs]}; first-order {rs[0]['first']:.4f}; "
              f"exact >= sharper where both exist: {all(r['exact'] >= r['sharper'] - 1e-6 for r in rs if r['exact'] and r['sharper'])}")
    for th in (0.01, 0.05, 0.1):
        rs = [r for r in S["level3"] if r["theta"] == th]
        print(f"- mean reversion, theta = {th}: exact phi crossing {[None if r['exact'] is None else round(r['exact'], 3) for r in rs]}; "
              f"bound's crossing {[None if r['bound'] is None else round(r['bound'], 3) for r in rs]}")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    ax = axes[0]
    for th, col in zip((0.01, 0.05, 0.1), ("C0", "C1", "C2")):
        rs = [r for r in S["level1"] if r["theta"] == th]
        ax.plot([r["exact"] for r in rs if r["exact"]], [r["lamr"] for r in rs if r["exact"]], "-o", color=col, ms=3, label=f"exact L_0 - 1 = {th}")
        ax.plot([r["sharper"] for r in rs if r["sharper"]], [r["lamr"] for r in rs if r["sharper"]], "--", color=col, label=f"(k/(1-k))^2 Dur = {th}")
        ax.axvline(th / (1 + th), color=col, ls=":", lw=1)
    ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("prior Kalman gain kappa_0"); ax.set_ylabel("lambda_A/(gamma sigma_A^2)")
    ax.set_title("Learning moves the target by theta (T = 20, t = 0); dotted: kappa = theta/(1+theta)"); ax.legend(fontsize=6)
    ax = axes[1]
    for th, col in zip((0.01, 0.05, 0.1), ("C0", "C1", "C2")):
        rs = [r for r in S["level3"] if r["theta"] == th]
        ax.plot([r["lamr"] for r in rs if r["exact"] is not None], [r["exact"] for r in rs if r["exact"] is not None], "-o", color=col, ms=3, label=f"exact 1 - M_0 = {th}")
        ax.plot([r["lamr"] for r in rs if r["bound"] is not None], [r["bound"] for r in rs if r["bound"] is not None], "--", color=col, label=f"(1 - w~)(1 - phi^19) = {th}")
    ax.set_xscale("log"); ax.set_xlabel("lambda_A/(gamma sigma_A^2)"); ax.set_ylabel("persistence phi"); ax.set_title("Mean reversion (T = 20, kappa_0 = 0.23)")
    ax.legend(fontsize=6); fig.tight_layout(); fig.savefig(HERE / "fig_levelsets.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

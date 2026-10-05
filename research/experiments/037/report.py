"""Experiment 037 report and figures (uv run python experiments/037/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json"))
    D = S["draws"]; sw = [s["base"] for s in S["sweeps"]]
    allc = D + sw
    ok = [r for r in allc if r["slack"] and all(st == "optimal" for st in r["status"])]
    body = [r for r in ok if not r["edge"]]
    print(f"{len(D)} random draws (N = 3, K = M = 2) and {len(sw)} named-point sweep points (N = 1); {len(ok)} with a slack budget and slack ETF caps "
          f"and both solvers optimal; {len(ok) - len(body)} knife edges (a slack, a free holding or a fund marginal within 1e-6 of its threshold)\n")
    print("## Part 1: fund lines with the ETF slacks")
    print(f"- at the solved optimum, every fund's line with the solver's slacks: {sum(r['p1'] for r in body)}/{len(body)}; interior ETFs with zero marginal: {sum(r['etf_int_ok'] for r in body)}/{len(body)}")
    print(f"- at-zero ETFs per point: {dict(Counter(len(r['Zsol']) for r in body))}\n")
    print("## Part 2: the at-zero set in the inputs")
    print(f"- formula Z (complementarity at the solved fund holdings) = solver's at-zero set: {sum(r['Zsol'] == r['Zf'] for r in body)}/{len(body)}; "
          f"slack formula against the solver's -g_j: largest |difference| {max(r['zeta_err'] for r in body):.1e}; candidate sets satisfying both conditions: {dict(Counter(r['nsets'] for r in body))}")
    O = S["one_etf"]; ob = [r for r in O if r["margin"] > 1e-6]
    print(f"- one ETF (K = M = 1): at zero iff mu_E <= gamma sigma_EE q at {sum(r['at_zero_sol'] == r['at_zero_rule'] for r in ob)}/{len(ob)} ({sum(r['at_zero_sol'] for r in ob)} at zero)\n")
    print("## Part 3")
    print(f"- (a) hold test at the incumbent (every fund in its band with Z at the incumbent) = solver's 'no fund traded': {sum(r['hold_pred'] == r['hold_sol'] for r in body)}/{len(body)} "
          f"({sum(r['hold_sol'] for r in body)} holds)")
    n1 = [r for r in body if r["N"] == 1]
    print(f"- (c) one fund: buy / sell / hold from G(x^-) = solver: {sum(r['dec'] == r['pred'] for r in n1)}/{len(n1)}; decisions {dict(Counter(r['dec'] for r in n1))}\n")
    SW = [s for s in S["sweeps"] if s["base"]["slack"]]
    print("## Part 4 (one fund, along its trade; 101 holdings per sweep point)")
    print(f"- G(x): the solver's marginal (ETFs re-optimized at each x) against the formula: largest |difference| {max(s['G_err'] for s in SW):.1e}; "
          f"at-zero sets agree at {sum(s['Z_agree'] for s in SW)}/{sum(s['npts'] for s in SW)} holdings")
    se = [s["slope_err"] for s in SW if s["slope_err"] is not None]
    print(f"- slope on each piece against -gamma s^Z: largest |difference| {max(se):.1e}; sweep points with more than one piece on [0, 0.25]: {sum(s['pieces'] > 1 for s in SW)} of {len(SW)}")
    dz = [(s, abs(s["x_sol"] - s["x_drop"])) for s in SW if not s["base"]["edge"]]   # named sweeps
    inp = [(s, d) for s, d in dz if s["in_piece"]]; outp = [(s, d) for s, d in dz if not s["in_piece"]]
    print(f"- drop-Z rule: drop-Z holding inside the incumbent's piece at {len(inp)} points, where it equals the solve at {sum(d < 1e-5 for s, d in inp)}; "
          f"outside it at {len(outp)} points, where it differs at {sum(d >= 1e-5 for s, d in outp)} and coincides (both clipped to the same bound) at {sum(d < 1e-5 and s['same_bound'] for s, d in outp)}")
    dirs = Counter()
    for s, d in outp:
        if d >= 1e-5:
            shorter = abs(s["x_sol"] - s["base"]["tag"] and s["x_sol"] - 0) < 0
            dirs[("shorter" if abs(s["x_sol"] - xm_of(s)) < abs(s["x_drop"] - xm_of(s)) else "longer", "s^Z rises" if s["s_opt"] > s["s_m"] + 1e-15 else ("falls" if s["s_opt"] < s["s_m"] - 1e-15 else "same"))] += 1
    print(f"- where they differ: true trade (shorter/longer than drop-Z, curvature at the optimum vs the incumbent): {dict(dirs)}")
    P4 = [r for r in S["part4"] if r["ok"] and not r["edge"]]
    ip = [r for r in P4 if r["in_piece"]]; op = [r for r in P4 if not r["in_piece"]]
    print(f"- targeted one-fund draws (Deviation 2; {len(P4)} usable): drop-Z root in the incumbent's piece at {len(ip)}, drop-Z = solve at {sum(abs(r['x'] - r['xt']) < 1e-5 for r in ip)}; "
          f"outside it at {len(op)}, of which both clipped to the same bound {sum(r['both_same_bound'] for r in op)} (coincide: {sum(abs(r['x'] - r['xt']) < 1e-5 for r in op if r['both_same_bound'])})")
    dif = [r for r in op if not r["both_same_bound"]]
    print(f"  - outside the piece, not clipped alike: {len(dif)}, drop-Z differs from the solve at {sum(abs(r['x'] - r['xt']) >= 1e-5 for r in dif)}")
    sign_ok = n_sign = 0
    for r in dif:
        ch = set(r["changes"])
        if ch in ({1.0}, {-1.0}) and abs(r["x"] - r["xt"]) >= 1e-5 and 1e-9 < r["xt"] < r["cap"] - 1e-9:
            n_sign += 1
            shorter = abs(r["x"] - r["xm"]) < abs(r["xu"] - r["xm"])
            sign_ok += shorter == (ch == {1.0})
    print(f"  - direction (every change raises s^Z -> shorter; every change lowers it -> longer), unclipped drop-Z roots: {sign_ok}/{n_sign}")
    sh = [x for s in SW for x in s["shifts"] if x["Z_e"] == x["Z"]]
    print(f"- 3(d): {sum(1 for s in SW for x in s['shifts']) - len(sh)} shifts change the at-zero set at the fixed holdings and are set aside (Deviation 3)")
    print(f"- 3(d) premium-error shift of G at fixed holdings: largest |solver - r_iZ' B^E_Z.c e| {max(abs(x['dG_sol'] - x['dG_f']) for x in sh):.1e} over {len(sh)} shifts "
          f"(e = 1e-4); zero when Z is empty: {sum(abs(x['dG_sol']) < 1e-12 for x in sh if not x['Z'])}/{sum(1 for x in sh if not x['Z'])}; nonzero with Z nonempty: "
          f"{sum(abs(x['dG_sol']) > 1e-9 for x in sh if x['Z'])}/{sum(1 for x in sh if x['Z'])}")
    tr = [x for x in sh if x["dx_f"] is not None and not x["crosses"]]
    if tr:
        print(f"- trading fund's holding shift against dG/(gamma s^Z): {len(tr)} cases, largest |difference| {max(abs(x['dx_sol'] - x['dx_f']) for x in tr):.1e} (shifts up to {max(abs(x['dx_f']) for x in tr):.1e})")
    if "part5d" in S:
        R = [r for r in S["part5d"] if r["ok"] and r.get("Z")]
        print(f"\n## Part 5(d): fold-in (Deviation 4): {len(R)} instances with an ETF at zero; mu_E + zeta reproduces the constrained optimum at "
              f"{sum(r['fold_dx'] <= 1e-5 for r in R)}/{len(R)} (largest |difference| {max(r['fold_dx'] for r in R):.1e}); mu_E - zeta moves it at "
              f"{sum(r['old_sign_dx'] > 1e-5 for r in R)}/{len(R)} (median {np.median([r['old_sign_dx'] for r in R]):.2f})")
    print(f"\n- solver disagreement (holdings): {max(r['dx'] for r in allc):.1e}; non-optimal statuses {sum(any(st != 'optimal' for st in r['status']) for r in allc)}; seconds {S['seconds']:.0f}")
    figures(S)


def xm_of(s):
    return s["val"] if s["kind"] == "xm" else 0.1


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, nm in zip(axes, ("equity-style", "fixed-income-style")):
        rs = sorted([s for s in S["sweeps"] if s["name"] == nm and s["kind"] == "lam2"], key=lambda s: s["val"])
        ax.plot([s["val"] * 100 for s in rs], [s["x_sol"] for s in rs], "k-", label="solved holding")
        ax.plot([s["val"] * 100 for s in rs], [s["x_drop"] for s in rs], "C1--", label="drop-Z rule")
        z = [s["val"] * 100 for s in rs if s["Zopt"]]
        if z:
            ax.axvspan(min(z), max(z), color="0.9", label="an ETF at zero at the optimum")
        ax.set_xlabel("lambda_hat_2 (% per quarter)"); ax.set_ylabel("fund holding"); ax.set_title(f"{nm}: one fund (1, 0.5), x^- = 0.1"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_sweeps.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

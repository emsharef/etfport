"""Experiment 042 report and figure (uv run python experiments/042/report.py), from summary.json."""
import json
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json")); C = S["cells"]
    R = [(c, r) for c in C for r in c["rows"]]; last = [(c, c["rows"][-1]) for c in C]
    print(f"{len(C)} cells ({S['n036']} of experiment 036's, {sum(c['corr'] < 0 for c in C)} mirror cells), 8 reviews each; {S['statement']}")
    print(f"- usable fund bands (column, review): {sum(r['fund_cols'] for c, r in R)}; ETF bands (row, review): {sum(r.get('etf_rows', 0) for c, r in R)}; "
          f"set aside as non-contiguous: fund {sum(r['fund_noncontig'] for c, r in R)} "
          f"(in {len({(c['corr'], c['r'], r['t']) for c, r in R if r['fund_noncontig']})} (cell, review) pairs), ETF {sum(r.get('etf_noncontig', 0) for c, r in R)}")
    print(f"- cells with no interior ETF column: {sum(1 for c in C if all(r['fund_cols'] == 0 for r in c['rows']))}\n")
    print("## Part 1 (last review)")
    print(f"- ETF columns: {sum(r['p1_cols'] for c, r in last)}; excluded (ETF optimizer at the grid's edge): {sum(r['p1_excluded'] for c, r in last)}")
    print(f"- median formula: largest |DP - formula| {max(r['p1_err_max'] for c, r in last if r['p1_err_max'] is not None):.2f} res_A; "
          f"beyond 1 res_A: {sum(r['p1_beyond1'] for c, r in last)}, beyond 2: {sum(r['p1_beyond2'] for c, r in last)}")
    reg = defaultdict(lambda: [0, 0.0])
    for c, r in last:
        for k, v in r["p1_regimes"].items():
            reg[k][0] += v["n"]; reg[k][1] = max(reg[k][1], v["err_max"])
    print("- widths by regime (read off the formula): " + "; ".join(f"{k} {n} (largest error {e:.2f} res_A)" for k, (n, e) in reg.items()))
    print(f"- 1b's width expressions against the median formula's widths: largest |difference| {max(r['p1_1b_formula_err'] for c, r in last):.1e}")
    B = [b for c, r in last for b in r["bend"]]; U = [b for b in B if b["usable"]]
    print(f"- bend (1a): {len(B)} edges in cells with a costly ETF and corr != 0; measured {len(U)}; not measured: {dict(Counter(b['why'] for b in B if not b['usable']))}")
    print(f"  - length against (kappa^+_E + kappa^-_E)/c^res_E: largest |difference| {max(abs(b['length'] - b['formula']) / b['tol'] for b in U):.2f} of the tolerance "
          f"({max(abs(b['length'] - b['formula']) / b['formula'] for b in U) * 100:.1f}% of the length); beyond tolerance {sum(abs(b['length'] - b['formula']) > b['tol'] for b in U)}")
    print(f"  - slope / (-rho_A): {min(-b['slope'] / b['rhoA'] for b in U):.3f} to {max(-b['slope'] / b['rhoA'] for b in U):.3f}; "
          f"identity (lo^b - lo^s)/rho_A = (hi^b - hi^s)/rho_A = width: {max(r.get('bend_identity', 0) for c, r in last):.1e} relative")
    print(f"- 1c: no-trade points {sum(r['p1c_nt'] for c, r in last)}; outside the static parallelotope {sum(r['p1c_nt_outside'] for c, r in last)}; "
          f"inside it (away from the boundary) but trading {sum(r['p1c_inside_trades'] for c, r in last)}\n")
    print("## Part 2 (every review)")
    print(f"- fund edges in the ETF incumbent: wrong-direction steps {sum(r.get('fund_wrong', 0) for c, r in R)} of {sum(r.get('fund_pairs', 0) for c, r in R)} adjacent pairs "
          f"(beyond one h_A: {sum(r.get('fund_wrong2', 0) for c, r in R)}); with the policy's own tie-break: {sum(r['fund_wrong_raw'] or 0 for c, r in R)}")
    print(f"- ETF edges in the fund holding: wrong-direction steps {sum(r.get('etf_wrong', 0) for c, r in R)} of {sum(r.get('etf_pairs', 0) for c, r in R)} (beyond one h_E: {sum(r.get('etf_wrong2', 0) for c, r in R)})")
    fc = [r for c, r in R if r.get("fund_const") is not None]; ec = [r for c, r in R if "etf_const" in r]
    print(f"- constant edges (corr = 0, or a frictionless ETF for the fund): fund {sum(r['fund_const'] for r in fc)}/{len(fc)} reviews, ETF (corr = 0) {sum(r['etf_const'] for r in ec)}/{len(ec)}")
    print(f"- 2d: no-trade points {sum(r['nt_points'] for c, r in R)}; points where it differs from the intersection of the two bands: {sum(r['nt_mismatch'] for c, r in R)}")
    sl = [r for c, r in R if "slope_max" in r]
    print(f"- slope bound (observed, not claimed): largest secant slope over ten ETF columns minus |rho_A|, in the secant's resolution res_A/(10 h_E): "
          f"{max((r['slope_max'] - r['rhoA']) / r['slope_res'] for r in sl):.2f} over {len(sl)} (cell, review) pairs; exceeds |rho_A| beyond it at "
          f"{sum(r['slope_max'] > r['rhoA'] + r['slope_res'] for r in sl)}")
    print(f"\n- seconds {S['seconds']:.0f}")
    figure(S)


def figure(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, F in zip(axes, S["figure"]):
        p = np.array(F["dE"]); rhoA = F["SAE"] / F["SAA"]; kA, kE = F["kA"], F["kE"]; g = 5.0
        med = lambda b, i, s: np.median(np.stack([np.full_like(p, b), i, np.full_like(p, s)]), 0)
        lo = med(-(kA[0] - F["rho"] * kE[0]) / F["cres"], -rhoA * p - kA[0] / (g * F["SAA"]), -(kA[0] + F["rho"] * kE[1]) / F["cres"])
        hi = med((kA[1] + F["rho"] * kE[0]) / F["cres"], -rhoA * p + kA[1] / (g * F["SAA"]), (kA[1] - F["rho"] * kE[1]) / F["cres"])
        ax.plot(p, F["lo"], "k.", ms=1.5, label="DP edges"); ax.plot(p, F["hi"], "k.", ms=1.5)
        ax.plot(p, lo, "C1-", lw=1, label="median formula"); ax.plot(p, hi, "C1-", lw=1)
        ax.set_xlabel("ETF incumbent p^- - p*"); ax.set_ylabel("fund edge - a*"); ax.set_title(f"last review, corr {F['corr']}, fund 10 bp, ETF 10 bp"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_edges.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

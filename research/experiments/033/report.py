"""Experiment 033 report and figures (uv run python experiments/033/report.py), from summary.json."""
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import norm

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json"))
    rows = [r for c in S["part1"] for r in c["rows"]]
    hh = [r for r in rows if r["hyp"] and not r["edge"]]
    print("## Part 1 (the decision is the gap's sign; one-review solver)")
    print(f"- {len(rows)} points; {sum(not r['hyp'] for r in rows)} outside the hypotheses (an ETF at a bound or the budget binding); "
          f"{sum(r['edge'] for r in rows)} knife edges (|gap| < 1e-7)")
    print(f"- solved decision = the Statement's rule (with the cap and zero boundary cases): {sum(r['dec'] == r['pred'] for r in hh)}/{len(hh)}")
    from collections import Counter
    print(f"- decisions: {dict(Counter(r['dec'] for r in hh))}; at the cap, buys predicted {sum(1 for c in S['part1'] if c['xm'] == 0.25 for r in c['rows'] if r['pred'] == 'buy')}, "
          f"at zero, sells predicted {sum(1 for c in S['part1'] if c['xm'] == 0.0 for r in c['rows'] if r['pred'] == 'sell')}")
    cap_pos = [r for c in S["part1"] if c["xm"] == 0.25 for r in c["rows"] if r["hyp"] and not r["edge"] and r["a"] > c["rates"][0] + 5 * (0.02 ** 2 + 0.0035 ** 2) * 0.25]
    zero_neg = [r for c in S["part1"] if c["xm"] == 0.0 for r in c["rows"] if r["hyp"] and not r["edge"] and r["a"] < -c["rates"][1]]
    print(f"- boundary cases: at the cap with a positive purchase gap, held {sum(r['dec'] == 'hold' for r in cap_pos)}/{len(cap_pos)}; "
          f"at zero with a positive sale gap, held {sum(r['dec'] == 'hold' for r in zero_neg)}/{len(zero_neg)}")
    # premium independence: same (rates, xm, alpha) across the 5 premium vectors
    by = {}
    for c in S["part1"]:
        for r in c["rows"]:
            if r["hyp"]:
                by.setdefault((tuple(c["rates"]), c["xm"], round(r["a"], 8)), []).append(r["x"])
    spread = max(max(v) - min(v) for v in by.values() if len(v) > 1)
    print(f"- largest change of the fund holding across the 5 premium vectors (same alpha, rates, incumbent): {spread:.1e}; solver holding disagreement {max(r['dx'] for r in rows):.1e}\n")
    P2 = S["part2"]
    print("## Part 2 (known Gaussian law)")
    print(f"- at n_suff = ceil(4 sigma^2 z^2/delta^2): type I error max {max(r['typeI'] - r['eps'] for r in P2):+.1e} relative to eps; "
          f"power min {min(r['power'] - (1 - r['eps']) for r in P2):+.1e} relative to 1 - eps ({len(P2)} cells)")
    print(f"- exact minimax minimal n (two-point Neyman-Pearson) = n_suff at {sum(r['n_min'] == r['n_suff'] for r in P2)}/{len(P2)} cells "
          f"(largest |n_min - n_suff| {max(abs(r['n_min'] - r['n_suff']) for r in P2)})")
    lo = [r for r in P2 if r["lower"] is not None]
    print(f"- lower bound (4 sigma^2/delta^2) log(1/(4 eps)) <= n_min at {sum(r['n_min'] >= r['lower'] for r in lo)}/{len(lo)}; ratio n_min / lower from "
          f"{min(r['n_min'] / r['lower'] for r in lo):.2f} to {max(r['n_min'] / r['lower'] for r in lo):.2f} (eps 0.01: {np.median([r['n_min'] / r['lower'] for r in lo if r['eps'] == 0.01]):.2f}, eps 0.2: {np.median([r['n_min'] / r['lower'] for r in lo if r['eps'] == 0.2]):.2f})")
    for sg, d in ((0.02, 0.001), (0.01, 0.0015)):
        r = [x for x in P2 if x["sigma"] == sg and x["delta"] == d and x["eps"] == 0.05][0]
        print(f"- math's illustration sigma {sg * 100:.0f}%, gap {d * 100:.2f}%, eps 0.05: n_suff = n_min = {r['n_suff']} quarters (lower bound {r['lower']:.0f})")
    print(f"- prior worth sigma^2/s^2 quarters: largest relative difference {max(r['rel'] for r in S['part2_prior']):.1e}\n")
    P3 = S["part3"]
    print("## Part 3 (bounded residuals; the two-point law on {-R, +R})")
    print(f"- Hoeffding rule at n_H = ceil(8 R^2/delta^2 log(1/eps)): type I <= eps at {sum(r['typeI'] <= r['eps'] + 1e-12 for r in P3)}/{len(P3)} (largest type I / eps {max(r['typeI'] / r['eps'] for r in P3):.3f}); "
          f"power >= 1 - eps at {sum(r['power'] >= 1 - r['eps'] - 1e-12 for r in P3)}/{len(P3)}")
    cs = [r["c"] for r in P3]
    print(f"- exact minimax minimal n on the two-point law: c = n_min delta^2 / (R^2 log(1/eps)) from {min(cs):.2f} to {max(cs):.2f} (median {np.median(cs):.2f}); "
          f"n_H / n_min from {min(r['nH'] / r['n_min'] for r in P3):.2f} to {max(r['nH'] / r['n_min'] for r in P3):.2f}")
    for e in (0.01, 0.05, 0.1, 0.2):
        print(f"  - eps {e}: c in [{min(r['c'] for r in P3 if r['eps'] == e):.2f}, {max(r['c'] for r in P3 if r['eps'] == e):.2f}]")
    print()
    P5 = S["part5"]
    print("## Part 5 (persistent alpha: the floor)")
    print(f"- filter limit against p_inf: largest relative difference {max(r['limit_rel'] for r in P5):.1e} ({len(P5)} runs of 10,000 steps)")
    print(f"- monotone decreasing from p_0 >= p_inf: {sum(r['mono'] for r in P5)}/{len(P5)}; smallest (p_t - p_inf)/p_inf {min(r['min_rel_excess'] for r in P5):.1e}")
    L = S["part5_limits"]
    print(f"- q -> 0 (phi 0.9, sigma 2%): p_inf = {', '.join(f'{v:.1e}' for v in L['q_small'])} at q = 1e-8, 1e-10, 1e-12")
    print(f"- sigma -> infinity (phi 0.9, q 1e-6): p_inf / (q/(1 - phi^2)) = {', '.join(f'{a / b:.6f}' for a, b in L['s_large'])} at sigma^2 = 1e-2, 1, 1e2")
    for qr in (1e-3, 1e-2, 0.1):
        fl = [r for r in P5 if r["qr"] == qr and r["sigma"] == 0.02 and r["mult"] == 1.0]
        print(f"- floor z_0.05 sqrt(p_inf), sigma 2%, q/sigma^2 = {qr:g}: " + ", ".join(f"phi {r['phi']}: {r['floor'] * 100:.3f}%" for r in fl))
    print()
    print("## Part 6 (unspanned loading: variance ratio; 20,000 draws)")
    for d in S["part6"]:
        for menu, v in d.items():
            z = (v["var_n"] - v["formula"]) / v["se"]
            print(f"- n = {v['n']}, {menu}: n Var = {v['var_n']:.4e} (SE {v['se']:.1e}) against {v['formula']:.4e} (z = {z:+.2f}); history ratio {v['ratio_formula']:.2f}")
    print()
    P7 = S["part7"]
    print("## Part 7 (pooled prior: direct conditioning)")
    print(f"- average alpha: largest relative difference {max(r['rel_avg'] for r in P7):.1e}; relative direction: {max(r['rel_rel'] for r in P7):.1e} ({len(P7)} cells)")
    print(f"- at 50 digits (mpmath) on three small cells: largest relative difference {max(x['rel'] for x in S['part7_mp']):.1e}")
    r = [x for x in P7 if x["N"] == 30 and x["share"] == 0.5 and x["n"] == 100][0]
    print(f"- N = 30, s_bar^2/s^2 = 0.5, n = 100: Var(average) = {r['avg']:.3e} against a single fund's {r['rel_formula']:.3e} (ratio {r['rel_formula'] / r['avg']:.1f})")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    ax = axes[0]
    ds = np.logspace(np.log10(0.0002), np.log10(0.01), 60); z = norm.isf(0.05)
    for sg, col in ((0.01, "C0"), (0.02, "C1")):
        ax.plot(ds * 100, 4 * sg ** 2 * z ** 2 / ds ** 2, color=col, label=f"sufficient = exact minimum, sigma {sg * 100:.0f}%")
        ax.plot(ds * 100, 4 * sg ** 2 / ds ** 2 * math.log(1 / (4 * 0.05)), "--", color=col, label=f"lower bound, sigma {sg * 100:.0f}%")
    for sg, d in ((0.02, 0.001), (0.01, 0.0015)):
        ax.plot(d * 100, 4 * sg ** 2 * z ** 2 / d ** 2, "ko", ms=4)
    ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("gap delta (% per quarter)"); ax.set_ylabel("quarters of history"); ax.set_title("Part 2: history needed, eps = 0.05")
    ax.legend(fontsize=7)
    ax = axes[1]
    phis = np.linspace(0, 0.995, 100)
    for qr in (1e-3, 1e-2, 0.1):
        s2 = 0.02 ** 2
        fl = [norm.isf(0.05) * math.sqrt(((qr * s2 - s2 * (1 - p ** 2)) + math.sqrt((qr * s2 - s2 * (1 - p ** 2)) ** 2 + 4 * qr * s2 * s2)) / 2) * 100 for p in phis]
        ax.plot(phis, fl, label=f"q/sigma^2 = {qr:g}")
    ax.set_xlabel("alpha persistence phi"); ax.set_ylabel("certifiable-gap floor z_0.05 sqrt(p_inf), %"); ax.set_title("Part 5: the floor (sigma 2%)"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_history_and_floor.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

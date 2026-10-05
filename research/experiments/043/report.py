"""Experiment 043 report and figure (uv run python experiments/043/report.py), from summary.json."""
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def fit(L, key):
    """Least-squares line in eps through the three smallest eps: (intercept, slope)."""
    P = sorted(L, key=lambda p: p["eps"])[:3]
    s, i = np.polyfit([p["eps"] for p in P], [p[key] for p in P], 1)
    return i, s


def main():
    S = json.load(open(HERE / "summary.json"))
    print(S["statement"], "\n")
    p1 = S["part1"]
    print(f"## Part 1: identity largest relative residual {p1['identity_max']:.1e} (1,000 draws); innovation moments of (y_a, e) {p1['moments_max']:.1e}\n")
    print("## Part 2")
    for kind, name in (("a", "(a) Sigma_AE = 0 against the one-instrument DP (gamma Sigma_AA, v_A)"), ("b", "(b) frictionless ETF against the reduced DP (c^res, v_A)")):
        L = [c for c in S["part2ab"] if c["kind"] == kind]; R = [r for c in L for r in c["rows"]]
        print(f"- {name}: {len(L)} cells x 8 reviews, {sum(r['cols'] for r in R)} (ETF column, review) bands; largest edge difference "
              f"{max(r['diff_steps'] for r in R if r['diff_steps'] is not None)} fund steps ({max(r['diff_res'] for r in R if r['diff_res'] is not None):.2f} res_A); "
              f"range across ETF columns {max(r['range_steps'] for r in R if r['range_steps'] is not None)} steps; non-contiguous {sum(r['noncontig'] for r in R)}")
    C = S["part2c"]; R = [r for c in C for r in c["rows"]]
    print(f"- (c) frozen ETF against the idle-target DP (gamma Sigma_AA, the idle target's law): {len(C)} cells x 8 reviews, {sum(r['cols'] for r in R)} bands; "
          f"largest edge difference {max(r['diff_steps'] for r in R if r['diff_steps'] is not None)} steps; width / static ceiling at most "
          f"{max(r['width_over_ceiling'] for r in R if r['width_over_ceiling'] is not None):.3f}; v^idle from the law against the formula "
          f"{max(abs(c['v_idle_law'] - c['v_idle_formula']) / c['v_idle_formula'] for c in C):.1e}\n")
    print("## Part 3 (one-instrument average-cost DP; eps = sqrt(v)/Delta)")
    P = S["part3"]
    print(f"- all converged: {all(p['converged'] for p in P)} (largest iteration count {max(p['iters'] for p in P)}); held sets contiguous: {all(p['contig'] for p in P)}; "
          f"smallest room to the grid's edge {min(p['edge_room'] for p in P)} grid steps")
    g = defaultdict(list)
    for p in P:
        g[(p["kind"], p["corr"], tuple(p["kA"]), p["r"])].append(p)
    print("| reduction | corr | rates (bp) | r | Delta_DP/Delta at eps = 0.2, 0.1, 0.05, 0.02, 0.01 | limit (slope) | lambda_DP/lambda limit | centre/Delta |")
    print("|---|---|---|---|---|---|---|---|")
    lims = []
    for (kind, corr, kA, r), L in g.items():
        L.sort(key=lambda p: -p["eps"]); i, s = fit(L, "ratio"); ig, _ = fit(L, "gain_ratio"); lims.append((i, ig))
        print(f"| {kind} | {corr} | {kA[0] * 1e4:.0f}/{kA[1] * 1e4:.0f} | {r} | {', '.join(f'{p['ratio']:.4f}' for p in L)} | {i:.4f} ({s:+.3f}) | {ig:.4f} | "
              f"{max(abs(p['centre_over_Delta']) for p in L):.1e} |")
    print(f"- limits: Delta ratio {min(x for x, _ in lims):.4f} to {max(x for x, _ in lims):.4f} (8c would give 0.7937); lambda ratio {min(y for _, y in lims):.4f} to {max(y for _, y in lims):.4f}")
    if "part4" in S:
        print("\n## Part 4 (two-instrument average-cost DP at the ends of xi; r = 0, v_B = v_A, fund 10 bp)")
        print("| corr | xi | eps | converged (iterations) | F (band at p^- = p*) | free end | frozen end (DP; formula) | nearer | F_e0 (NT along e = 0) | fund idle | ETF idle |")
        print("|---|---|---|---|---|---|---|---|---|---|---|")
        for p in sorted(S["part4"], key=lambda p: (p["corr"], p["xi"], -p["eps"])):
            near = "free" if abs(p["F"] - p["free_end"]) < abs(p["F"] - p["frozen_end"]) else "frozen"
            print(f"| {p['corr']} | {p['xi']} | {p['eps']} | {p['converged']} ({p['iters']}) | {p['F']:.3f} | {p['free_end']:.3f} | {p['frozen_end']:.3f}; {p['frozen_end_formula']:.3f} | "
                  f"{near} | {p['F_e0']:.3f} | {p['fund_idle']:.3f} | {p['etf_idle']:.3f} |")
        print(f"- stationary law: last-step total variation at most {max(p['pi_tv_last'] for p in S['part4']):.1e}, per-step leak at most {max(p['pi_leak'] for p in S['part4']):.1e}; "
              f"band room to the grid's edge at least {min(p['col_room'] for p in S['part4'])} steps; frozen-end jump rounding at most {max(p['frozen_jump_rounding'] for p in S['part4']):.3f} u")
    figure(S)


def figure(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    g = defaultdict(list)
    for p in S["part3"]:
        if tuple(p["kA"]) == (0.001, 0.001) and p["corr"] in (0.0, 0.5):
            g[(p["kind"], p["r"])].append(p)
    for (kind, r), L in g.items():
        L.sort(key=lambda p: p["eps"]); e = [p["eps"] for p in L]
        lab = f"({kind})" + (f" r = {r}" if kind == "c" else "")
        axes[0].plot(e, [p["ratio"] for p in L], "o-", ms=3, label=lab); axes[1].plot(e, [p["gain_ratio"] for p in L], "o-", ms=3, label=lab)
    for ax, nm in zip(axes, ("half-width / Delta (4c law)", "average cost / (c Delta^2 / 2)")):
        ax.axhline(1, color="k", lw=0.8); ax.set_xscale("log"); ax.set_xlabel("eps = sqrt(v) / Delta"); ax.set_ylabel(nm); ax.legend(fontsize=7)
    axes[0].axhline(2 ** (-1 / 3), color="C3", ls="--", lw=0.8); axes[0].text(0.012, 0.80, "8c (refuted claim 101)", color="C3", fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_cuberoot.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

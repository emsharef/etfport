"""Experiment 048 report and figures (uv run python experiments/048/report.py), from summary.json."""
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
POL = (("myopic", "myopic"), ("ef111", "exposure-first (claim 111)"), ("ef041", "claim 041's stage"))


def main():
    S = json.load(open(HERE / "summary.json")); C = S["cells"]
    print(f"{len(C)} cells; {S['model']}; solver failures {sum(c['solver_failures'] for c in C)}, one-point-fibre fallbacks {sum(c['fallbacks'] for c in C)}\n")
    for k, nm in POL:
        F = [c[k]["loss_bp"] for c in C if c[k]["feasible"]]
        print(f"- {nm}: defined at {len(F)}; loss (bp of the objective) median {np.median(F):.4f}, max {max(F):.3f}; works well (< 0.01 bp) at {sum(x < 0.01 for x in F)}")
    print(f"- the dynamic policy's budget binds at {sum(c['dynamic']['binds'] for c in C)} cells; the myopic policy is optimal (holdings, 1e-5) at {sum(c['myopic_optimal'] for c in C)}; "
          f"claim 044's test agrees with that at {sum(c['myopic_optimal'] == c['claim044']['test_passes'] for c in C)}/{len(C)}")
    und = [c for c in C if not c["ef111"]["feasible"]]
    print(f"- exposure-first (claim 111) undefined at {len(und)} cells: {[(c['regime'], c['start'], c['cash'], c['unc'], c['costmul'], c['ef111'].get('states_fund_above_cap')) for c in und]}")
    print(f"- claim 041's stage unfundable at {sum(not c['ef041']['feasible'] for c in C)} cells, all at the root\n")
    print("| regime | start (fund, ETF) | cash | myopic: max loss (bp), works well | exposure-first: max loss, works well, undefined | claim 041's stage: max loss, works well, unfundable | budget binds (dynamic) | myopic optimal |")
    print("|---|---|---|---|---|---|---|---|")
    g = defaultdict(list)
    for c in C:
        g[(c["regime"], tuple(c["start"]), c["cash"])].append(c)
    for (rg, st, ca), L in sorted(g.items()):
        def s(p):
            F = [c[p]["loss_bp"] for c in L if c[p]["feasible"]]
            return f"{max(F):.3f}, {sum(x < 0.01 for x in F)}/6" + (f", {sum(not c[p]['feasible'] for c in L)}" if any(not c[p]['feasible'] for c in L) else "") if F else f"-, 0/6, {len(L)}"
        print(f"| {rg} | {st} | {ca} | {s('myopic')} | {s('ef111')} | {s('ef041')} | {sum(c['dynamic']['binds'] for c in L)}/6 | {sum(c['myopic_optimal'] for c in L)}/6 |")
    print("\nMyopic losses above 0.01 bp, with claim 044's quantities (the myopic policy's tomorrow):")
    print("| regime | start | cash | prior x | fund rate x | loss (bp) | root ETF: dynamic / myopic | residual_E | residual_A | E eta_1 |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for c in sorted(C, key=lambda c: (c["regime"], c["start"], c["cash"], c["unc"], c["costmul"])):
        if c["myopic"]["loss_bp"] > 0.01:
            ce = c["claim044"]; f = lambda v: "-" if v is None else f"{v:+.5f}"
            print(f"| {c['regime']} | {tuple(c['start'])} | {c['cash']} | {c['unc']} | {c['costmul']} | {c['myopic']['loss_bp']:.3f} | {c['dynamic']['x0'][1]:.3f} / {c['myopic']['x0'][1]:.3f} | "
                  f"{f(ce['residual_E'])} | {f(ce['residual_A'])} | {ce['E_eta1']:.1e} |")
    figures(C)


def figures(C):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(2, 3, figsize=(11, 6), sharey=True)
    starts = ((0.0, 0.9), (0.075, 0.45), (0.15, 0.0))
    for r, rg in enumerate(("equity-style", "fixed-income-style")):
        for j, st in enumerate(starts):
            ax = axes[r, j]
            for k, nm in POL:
                for ca, ls in ((1.0, "-"), (0.005, "--")):
                    L = sorted([c for c in C if c["regime"] == rg and tuple(c["start"]) == st and c["cash"] == ca and c["unc"] == 1.0], key=lambda c: c["costmul"])
                    xs = [c["costmul"] for c in L if c[k]["feasible"]]; ys = [max(c[k]["loss_bp"], 1e-5) for c in L if c[k]["feasible"]]
                    ax.plot(xs, ys, ls, marker="o", ms=3, label=f"{nm}, cash {'slack' if ca == 1.0 else 'tight'}")
            ax.axhline(0.01, color="0.6", lw=0.6, ls=":")
            ax.set_xscale("log"); ax.set_yscale("log"); ax.set_title(f"{rg}, start {st}", fontsize=8)
            if r == 1:
                ax.set_xlabel("fund rate / preset fund rate")
            if j == 0:
                ax.set_ylabel("loss vs dynamic (bp)")
    axes[0, 0].legend(fontsize=5.5)
    fig.suptitle("Experiment 048: simpler policies' losses (prior x1; dotted: 0.01 bp). Illustration at assumed inputs.", fontsize=9)
    fig.tight_layout(); fig.savefig(HERE / "fig_losses.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()

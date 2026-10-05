"""Experiment 054: tables and the registered figure from summary.json.
Run: uv run python experiments/054/report.py   (after run.py)
Writes report.md and losses.png next to this file.
"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
C = json.load(open(HERE / "summary.json"))["cells"]
WELL = 0.01
STARTS = [[0.05, 0.10], [0.05, 0.80], [0.22, 0.30], [0.10, 0.50]]
key = lambda c: (c["regime"], STARTS.index(c["start"]), -c["cash"], c["rv"], c["sell"])
C.sort(key=key)


def criterion():
    dom = [c for c in C if c["in_domain"]]
    fail = [c for c in dom if not (c["converged"] and c["loss_rule_bp"] < WELL and c["etf_gap"] < 1e-5)]
    moved = [c for c in dom if abs(c["reserve_dyn"][0]) > 1e-5]
    band = [c for c in dom if abs(c["x_my"][1] - c["start"][1]) <= 1e-7]
    return [f"- Domain cells (dynamic budget slack today and tomorrow, dynamic fund = a^my within 1e-5): {len(dom)} of {len(C)}"
            f" ({sum(c['regime'] == 'equity-style' for c in dom)} equity-style, {sum(c['regime'] == 'fixed-income-style' for c in dom)} fixed-income-style).",
            f"- Failures of the registered criterion: {len(fail)}. Largest domain loss {max(c['loss_rule_bp'] for c in dom):.1e} bp,"
            f" largest ETF gap {max(c['etf_gap'] for c in dom):.1e}, most iterations {max(c['iters'] for c in dom)}; non-converged cells: {sum(not c['converged'] for c in C)}.",
            f"- Domain cells where the dynamic ETF differs from the one-review ETF by more than 1e-5: {len(moved)}; where the one-review ETF is untraded"
            f" today: {len(band)}, of which the dynamic ETF moves in {sum(abs(c['reserve_dyn'][0]) > 1e-5 for c in band)} (the line leaves today's band).",
            f"- Rule clipped by the budget: {sum(c['clipped'] for c in C)} cells."]


def summary_rows():
    out = ["| cells | n | myopic works well | rule works well | rule worse than myopic by > 0.01 bp | largest loss myopic / rule (bp) | recovery (myopic loss > 0.01 bp): median [min, max] |",
           "|---|---|---|---|---|---|---|"]
    for lab, cs in (("all", C), ("domain", [c for c in C if c["in_domain"]]), ("budget binds", [c for c in C if c["dyn_binds"]]),
                    ("fund moves (slack)", [c for c in C if not c["dyn_binds"] and c["fund_gap"] > 1e-5])):
        rec = [c["recovery"] for c in cs if c["recovery"] is not None]
        r = f"{np.median(rec):.3f} [{min(rec):.3f}, {max(rec):.3f}] (n = {len(rec)})" if rec else "-"
        out.append(f"| {lab} | {len(cs)} | {sum(c['loss_my_bp'] < WELL for c in cs)} | {sum(c['loss_rule_bp'] < WELL for c in cs)} | "
                   f"{sum(c['loss_rule_bp'] > c['loss_my_bp'] + WELL for c in cs)} | {max(c['loss_my_bp'] for c in cs):.3f} / {max(c['loss_rule_bp'] for c in cs):.3f} | {r} |")
    return out


def cell_rows():
    out = ["| regime | start | cash | rv | sell | domain | binds | fund gap | ETF: my -> dyn (rule gap) | loss bp myopic / rule | iters | h^my / N | Res | Pi_E (x^my) |",
           "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for c in C:
        m = c["math"]
        out.append(f"| {c['regime'].split('-')[0]} | ({c['start'][0]:.2f}, {c['start'][1]:.2f}) | {c['cash']} | x{c['rv']:g} | x{c['sell']:g} | "
                   f"{'y' if c['in_domain'] else 'n'} | {'y' if c['dyn_binds'] else 'n'} | {c['fund_gap']:.4f} | "
                   f"{c['x_my'][1]:.4f} -> {c['x_dyn'][1]:.4f} ({c['etf_gap']:.1e}) | {c['loss_my_bp']:.3f} / {c['loss_rule_bp']:.3f} | {c['iters']} | "
                   f"{m['h_my']:.4f} / {m['N_my']:.4f} | {m['Res']:+.4f} | {m['Pi_E_sign_at_my'] or 'undefined'} |")
    return out


def figure():
    fig, ax = plt.subplots(figsize=(12, 4.8))
    x = np.arange(len(C))
    for k, lab, col, mk in (("loss_my_bp", "one-review (myopic)", "C0", "o"), ("loss_rule_bp", "literal rule", "C3", "s")):
        y = np.array([max(c[k], 0.0) for c in C]); d = np.array([c["in_domain"] for c in C])
        ax.scatter(x[d], y[d], color=col, marker=mk, s=16, label=f"{lab}, in part 3(b)'s domain")
        ax.scatter(x[~d], y[~d], facecolors="none", edgecolors=col, marker=mk, s=16, label=f"{lab}, outside")
    ax.set_yscale("symlog", linthresh=1e-3); ax.axhline(WELL, color="grey", lw=0.6, ls=":")
    edges = [i for i in range(1, len(C)) if (C[i]["regime"], C[i]["start"]) != (C[i - 1]["regime"], C[i - 1]["start"])]
    for e in edges:
        ax.axvline(e - 0.5, color="grey", lw=0.4)
    ticks = [0] + edges; ends = edges + [len(C)]
    ax.set_xticks([(a + b - 1) / 2 for a, b in zip(ticks, ends)])
    ax.set_xticklabels([f"{C[a]['regime'].split('-')[0]}\n({C[a]['start'][0]:.2f}, {C[a]['start'][1]:.2f})" for a in ticks], fontsize=7)
    ax.set_ylabel("loss against the dynamic optimum (bp, symlog)")
    ax.set_title("Experiment 054: 144 new cells, each block = cash x revision variance x ETF sale rate (illustration; dotted line 0.01 bp)", fontsize=9)
    ax.legend(fontsize=7, ncol=2, loc="upper left")
    fig.tight_layout(); fig.savefig(HERE / "losses.png", dpi=130)


def main():
    lines = ["# Experiment 054: tables (generated by report.py from summary.json)", "",
             "Losses are the dynamic optimum's expected objective minus the policy's, in bp. Tested cells only (AGENTS.md rule 22).", "",
             "## The registered criterion", ""] + criterion() + ["", "## Summary", ""] + summary_rows() + ["", "## Cells", ""] + cell_rows()
    (HERE / "report.md").write_text("\n".join(lines) + "\n")
    figure()
    print("\n".join(criterion() + [""] + summary_rows()))


if __name__ == "__main__":
    main()

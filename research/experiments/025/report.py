"""Experiment 025 report (uv run python experiments/025/report.py), from summary.json."""
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
CELLS = {"A50": "alpha 0.50, premia fixed", "A80": "alpha 0.80, premia fixed", "A95": "alpha 0.95, premia fixed",
         "L50": "premia 0.50, alpha fixed", "L80": "premia 0.80, alpha fixed", "L95": "premia 0.95, alpha fixed",
         "B80": "both 0.80"}


def d(ce, a, b):
    x = (np.array(ce[a]) - np.array(ce[b])) * 1e4
    return x.mean(), x.std(ddof=1) / np.sqrt(len(x))


def main():
    S = json.load(open(HERE / "summary.json"))
    print("## Differences, bp per quarter, mean (SE); true-parameter certainty equivalent on common random numbers\n")
    print("| cell | R | MPC-L CE | dynamic + learning: MPC-L minus one-quarter rule | learning: MPC-L minus MPC-S | "
          "aim in front: MPC-L minus MPC-flat | H = 8 minus H = 4 | MPC-L minus two-stage | MPC-L minus ETF-only | criterion (mean - 2 SE >= 1 bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for cell, lab in CELLS.items():
        if cell not in S:
            continue
        ce = S[cell]["ce"]
        f = lambda a, b: "{:.3f} ({:.3f})".format(*d(ce, a, b))  # noqa: E731
        dm, ds = d(ce, "MPC-L8", "myopic")
        crit = "meets" if dm - 2 * ds >= 1 else "fails"
        print(f"| {cell} ({lab}) | {S[cell]['R']} | {np.mean(ce['MPC-L8']) * 1e4:.2f} | {f('MPC-L8', 'myopic')} | {f('MPC-L8', 'MPC-S8')} | "
              f"{f('MPC-L8', 'MPC-flat8')} | {f('MPC-L8', 'MPC-L4')} | {f('MPC-L8', 'two-stage')} | {f('MPC-L8', 'ETF-only8')} | {crit} |")
    print("\n## Holdings and turnover (MPC-L8 and the one-quarter rule)\n")
    print("| cell | funds at zero (MPC-L / rule) | fund turnover per quarter (MPC-L / rule) | ETF turnover per quarter (MPC-L / rule) |")
    print("|---|---|---|---|")
    for cell in CELLS:
        if cell not in S:
            continue
        s = S[cell]
        print(f"| {cell} | {s['funds_at_zero']['MPC-L8']:.3f} / {s['funds_at_zero']['myopic']:.3f} | "
              f"{s['turnover_funds']['MPC-L8']:.4f} / {s['turnover_funds']['myopic']:.4f} | "
              f"{s['turnover_etfs']['MPC-L8']:.4f} / {s['turnover_etfs']['myopic']:.4f} |")
    print("\nseconds per cell: " + ", ".join(f"{c} {S[c]['seconds']:.0f}" for c in CELLS if c in S))


if __name__ == "__main__":
    main()

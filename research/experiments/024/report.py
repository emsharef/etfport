"""Experiment 024 report (uv run python experiments/024/report.py)."""
import json
import statistics
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
NAMES = {"MPC-L": "learning-aware receding horizon (MPC-L)", "MPC-S": "static-belief receding horizon (MPC-S)",
         "myopic": "plug-in myopic, with costs", "ETF-only": "ETF-only (receding horizon)", "two-stage": "two-stage (claim 027)",
         "equal": "equal weight (feasible)", "no-trade": "no trade"}
SIMPLE = ["myopic", "ETF-only", "two-stage", "equal", "no-trade"]


def table(d, label):
    pols = list(d["ce"].keys())
    ce = {p: np.array(d["ce"][p]) * 1e4 for p in pols}
    R = len(ce[pols[0]])
    print(f"**{label}** (R = {R}; bp per quarter; true-parameter certainty equivalent)\n")
    print("| policy | CE mean (SE) | MPC-L minus policy (SE) |")
    print("|---|---|---|")
    for p in pols:
        d = ce["MPC-L"] - ce[p]
        print(f"| {NAMES[p]} | {ce[p].mean():.2f} ({ce[p].std(ddof=1) / np.sqrt(R):.2f}) | "
              + ("-" if p == "MPC-L" else f"{d.mean():.3f} ({d.std(ddof=1) / np.sqrt(R):.3f})") + " |")
    best = max(SIMPLE, key=lambda p: ce[p].mean())
    d = ce["MPC-L"] - ce[best]
    lv = ce["MPC-L"] - ce["MPC-S"]
    se = d.std(ddof=1) / np.sqrt(R)
    print(f"\nbest simple rule: {NAMES[best]}; MPC-L minus it = {d.mean():.3f} (SE {se:.3f}); mean - 2 SE = {d.mean() - 2 * se:.3f} bp "
          f"-> {'meets' if d.mean() - 2 * se >= 1 else 'FAILS'} the 1 bp criterion")
    print(f"learning-aware value MPC-L minus MPC-S = {lv.mean():.3f} (SE {lv.std(ddof=1) / np.sqrt(R):.3f}) bp per quarter\n")
    return ce, best


def extras(d):
    ex = d["extras"]
    pols = list(ex.keys())
    print("| policy | funds at zero: mean share of quarters (min-max over funds) | ETFs at zero (mean) | inaction funds / ETFs | mean invested | budget binding |")
    print("|---|---|---|---|---|---|")
    for p in pols:
        zf = np.array(ex[p]["zero_funds"]); ze = np.array(ex[p]["zero_etfs"])
        print(f"| {NAMES.get(p, p)} | {zf.mean():.3f} ({zf.min():.3f}-{zf.max():.3f}) | {ze.mean():.3f} | "
              f"{ex[p]['inaction_funds']:.3f} / {ex[p]['inaction_etfs']:.3f} | {ex[p]['invested']:.3f} | {ex[p]['budget_binding']:.3f} |")


def main():
    D = json.load(open(HERE / "summary.json"))
    print("## Primary (alpha population mean -0.19% per quarter)\n")
    ce, best = table(D["main"]["data"], "Primary")
    extras(D["main"]["data"])
    h8 = np.array(D["h8"]["data"]["ce"]["MPC-L"]) * 1e4
    n = len(h8)
    d = h8 - ce["MPC-L"][:n]
    print(f"\n**Horizon check:** MPC-L with H = 8 minus H = 4 = {d.mean():.3f} (SE {d.std(ddof=1) / np.sqrt(n):.3f}) bp per quarter; "
          f"H = 8 minus best simple rule = {(h8 - ce[best][:n]).mean():.3f} bp")
    for dl, dd in D["sens"]["data"].items():
        mean = -0.19 + float(dl) * 100
        print(f"\n## Sensitivity: alpha population mean {mean:+.2f}% per quarter (delta {float(dl) * 1e4:.0f} bp)\n")
        table(dd, f"mean {mean:+.2f}%")
        extras(dd)
    P = D["prop"]["data"]
    e = P["extras"]["prop-L"]; hb = e["half_band"]
    print("\n## Band variant (MPC-L with proportional costs: fund 100 bp, ETF 5 bp)\n")
    print(f"- inaction: funds {e['inaction_funds']:.3f}, ETFs {e['inaction_etfs']:.3f} of instrument-quarters")
    print(f"- empirical half-band (90th percentile of |x^- - xhat| over no-trade instrument-quarters): funds "
          f"{hb['funds_p90']:.4f} (median {hb['funds_median']:.4f}; n = {hb['funds_n']}), ETFs {hb['etfs_p90']:.4f} "
          f"(median {hb['etfs_median']:.4f}; n = {hb['etfs_n']})")
    print(f"- certainty equivalent {np.mean(P['ce']['prop-L']) * 1e4:.2f} bp per quarter")
    print(f"\nseconds: main {D['main']['seconds']:.0f}")


if __name__ == "__main__":
    main()

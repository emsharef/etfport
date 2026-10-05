"""Experiment 022 report (uv run python experiments/022/report.py): tables from results.json and stationary.json."""
import json
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
NAMES = {"D12": "M5 optimal (D12 policy)", "myopic": "plug-in myopic, with costs", "static": "static-belief dynamic",
         "ETF-only": "ETF-only (optimal)", "two-stage": "two-stage (claim 027)", "equal": "equal weight",
         "no-trade": "no trade", "oracle": "oracle (true parameters)"}


def main():
    r = json.load(open(HERE / "results.json"))
    c = r["calibration"]
    print(f"## Calibration (data)\n\nFF5 quarterly, {c['n_quarters']} quarters; means (%): "
          + ", ".join(f"{v * 100:.3f}" for v in c["lam_hat"]) + "; SDs (%): "
          + ", ".join(f"{c['Sf'][i][i] ** 0.5 * 100:.3f}" for i in range(5)) + "\n")
    print(f"## Part 1: true-parameter certainty equivalent (bp per quarter; R = {r['R']} CRN paths)\n")
    print("| policy | CE mean (SE) | D12 minus policy (SE) | oracle minus policy (SE) |")
    print("|---|---|---|---|")
    for p, v in r["main"].items():
        d = r["pairs"].get(f"D12 - {p}"); o = r["pairs"].get(f"oracle - {p}")
        fm = lambda x: "-" if x is None else f"{x['mean_bp']:.2f} ({x['se_bp']:.2f})"  # noqa: E731
        print(f"| {NAMES[p]} | {v['mean_bp']:.2f} ({v['se_bp']:.2f}) | {fm(d)} | {fm(o)} |")
    print("\n## Part 2: where the value comes from (R = 5,000 paths of the first pass)\n")
    print("| policy | alpha captured x_A'alpha (bp/q) | of which from short fund positions | share of fund-quarters short | "
          "mean gross leverage sum abs(x) | turnover funds / ETFs per quarter | registered: x_A'mu_A (per quarter) |")
    print("|---|---|---|---|---|---|---|")
    for p, v in r["extra"].items():
        print(f"| {NAMES[p]} | {v['alpha_capture_bp']:.1f} | {v['alpha_capture_short_bp']:.1f} | {v['share_short_fund_positions']:.3f} | "
              f"{v['gross_leverage']:.2f} | {v['turnover_funds']:.3f} / {v['turnover_etfs']:.3f} | {v['fund_expected_return']:.4f} |")
    print("\n**D12 policy's trading speeds and aim (mean over paths; gross = sum of abs holdings):**\n")
    print("| t | speed funds | speed ETFs | aim gross funds / ETFs | aim net funds / ETFs | exposure part gross funds / ETFs | alpha part gross funds / ETFs |")
    print("|---|---|---|---|---|---|---|")
    for t, v in r["split"].items():
        print(f"| {t} | {v['speed_funds']:.3f} | {v['speed_etfs']:.3f} | {v['aim_gross_funds']:.2f} / {v['aim_gross_etfs']:.2f} | "
              f"{v['aim_net_funds']:.2f} / {v['aim_net_etfs']:.2f} | {v['exposure_part_gross_funds']:.2f} / {v['exposure_part_gross_etfs']:.2f} | "
              f"{v['alpha_part_gross_funds']:.2f} / {v['alpha_part_gross_etfs']:.2f} |")
    print("\n**Sensitivities (R = 2,000; bp per quarter, mean (SE)):**\n")
    print("| case | D12 minus ETF-only | D12 minus two-stage | oracle minus D12 |")
    print("|---|---|---|---|")
    for k, v in r["sensitivities"].items():
        g = lambda key: f"{v['pairs'][key]['mean_bp']:.1f} ({v['pairs'][key]['se_bp']:.2f})"  # noqa: E731
        print(f"| {k} | {g('D12 - ETF-only')} | {g('D12 - two-stage')} | {g('oracle - D12')} |")
    S = json.load(open(HERE / "stationary.json"))
    print("\n## Part 3: stationary instance (D13; proportional costs, caps; gamma 5; T = 120)\n")
    print("Median band width over belief points with an interior target, at t = 20 / 40 / 60 (h = 1/200); resolved = "
          "change < 10% from h = 1/100.\n")
    print("| Phi | innovation sd of belief (bp) | stationary belief sd (bp) | kappa (bp) | fund width t=20/40/60 | stationary | "
          "fund resolved | fund edge at a cap (t=40 points) | ETF width t=40 |")
    print("|---|---|---|---|---|---|---|---|---|")
    w = lambda e: None if e is None else e[1] - e[0]  # noqa: E731
    by = {(x["phi"], x["kappa"], round(1 / x["h"])): x for x in S}
    for (phi, k, h), x in sorted(by.items()):
        if h != 200:
            continue
        med = []
        for t in (20, 40, 60):
            ws = [w(b["edges"][0]) for b in x["bands"] if b["t"] == t and b["edges"][0]]
            med.append(statistics.median(ws) if ws else None)
        c100 = by[(phi, k, 100)]
        m100 = statistics.median([w(b["edges"][0]) for b in c100["bands"] if b["t"] == 40 and b["edges"][0]])
        stat = med[0] is not None and max(med) - min(med) <= x["h"] + 1e-12
        res = med[1] is not None and abs(m100 - med[1]) < 0.1 * med[1]
        caps = sum(1 for b in x["bands"] if b["t"] == 40 and b["edges"][0] and (b["edges"][0][2] or b["edges"][0][3]))
        npts = sum(1 for b in x["bands"] if b["t"] == 40 and b["edges"][0])
        ew = [w(b["edges"][1]) for b in x["bands"] if b["t"] == 40 and b["edges"][1]]
        print(f"| {phi} | {x['innov_sd'] * 1e4:.2f} | {x['belief_sd'] * 1e4:.1f} | {k * 1e4:.0f} | "
              + " / ".join(f"{v:.3f}" for v in med) + f" | {'yes' if stat else 'no'} | {'yes' if res else 'no'} | {caps} of {npts} | "
              f"{statistics.median(ew) if ew else float('nan'):.3f} |")


if __name__ == "__main__":
    main()

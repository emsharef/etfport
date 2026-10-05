"""Experiment 035 report (uv run python experiments/035/report.py), from summary.json: the ranges and the formulas at them."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json"))
    print(f"Fetch date {S['fetch_date']}; window to {S['window_end']}; dropped {S['dropped'] or 'none'}. {S['label']}.\n")
    for cls in ("equity", "fixed_income"):
        E = S["estimates"][cls]; s = E["summary"]
        print(f"## {cls}: per fund (quarterly; alpha net of fees; Newey-West SE, 3 lags)")
        print("| ticker | kind | start | months | alpha | SE | residual SD | factors omitted (built from it) |")
        print("|---|---|---|---|---|---|---|---|")
        for t, r in E["rows"].items():
            print(f"| {t} | {r['kind']} | {r['start']} | {r['months']} | {r['alpha_q'] * 100:+.3f}% | {r['alpha_se_q'] * 100:.3f}% | {r['resid_sd_q'] * 100:.2f}% | {', '.join(r['built_from_it']) or '-'} |")
        f = lambda d: f"{d['min'] * 100:.3f}% / {d['median'] * 100:.3f}% / {d['max'] * 100:.3f}%"
        print(f"\n- funds, min / median / max: alpha {f(s['alpha_q'])}; SE {f(s['alpha_se_q'])}; residual SD {f(s['resid_sd_q'])}")
        print(f"- cross-sectional SD of alpha {s['alpha_cross_sd'] * 100:.3f}%; illustrative prior SD s = sqrt(max(0, var - mean SE^2)) {s['prior_sd_illustrative'] * 100:.3f}% (6 funds cannot estimate it)")
        print(f"- ETF residual SD {f(s['etf_resid_sd_q'])}\n")
        T = S["thresholds"][cls]
        print(f"### Formulas at the ranges ({cls}; preset alpha {T['preset_alpha'] * 100:+.2f}%, sigma_A {T['preset_sigma_A'] * 100:.0f}%, fund rate {T['preset_fund_rate'] * 1e4:.0f} bp)")
        print("| input varied | at | purchase excess p (x^- = 0) | bought? | C^- (bp/quarter) | C^- at cap 0.25 | p (x^- = 0.1) | bought? |")
        print("|---|---|---|---|---|---|---|---|")
        rows = T["rows"]
        for var in ("alpha_q", "alpha_se_q", "resid_sd_q"):
            for q in ("min", "median", "max"):
                r0 = [r for r in rows if r["vary"] == var and r["at"] == q and r["xm"] == 0.0][0]; r1 = [r for r in rows if r["vary"] == var and r["at"] == q and r["xm"] == 0.1][0]
                print(f"| {var} | {q} | {r0['purchase_excess'] * 1e4:+.1f} bp | {r0['buy']} | {r0['C_minus_bp']:.2f} | {r0['C_minus_cap_bp']:.2f} | {r1['purchase_excess'] * 1e4:+.1f} bp | {r1['buy']} |")
        print(f"\n- claim 039's history (quarters) to certify a buy at eps = 0.05, sigma_A at the estimated residual SDs: {T['claim039_quarters']}\n")
    print("## Fixed-income spanning by {AGG, IEF, LQD}: unhedgeable share of each fund's factor variance")
    for t, v in S["fi_unspanned_share"].items():
        print(f"- {t}: {v['unhedgeable_share'] * 100:.1f}%")
    print("\n## Expense ratios (annual; SEC risk/return summaries, 2025 filings; None = not in the data sets)")
    print(", ".join(f"{t} {'-' if v is None else f'{v * 1e4:.0f} bp'}" for t, v in S["expense_ratio_annual"].items()))


if __name__ == "__main__":
    main()

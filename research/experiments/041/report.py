"""Experiment 041 report (uv run python experiments/041/report.py), from summary.json."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = lambda d, k="p50", s=100: "-" if d is None else f"{d[k] * s:.2f}"


def main():
    S = json.load(open(HERE / "summary.json"))
    print(f"{S['label']}; fetched {S['fetch_date']}; {S['n']} funds kept; dropped {len(S['dropped'])}: {S['dropped']}; bond factors from {S['bond_factor_start']}\n")
    print("## Distributions (quarterly %, p10 / p50 / p90; expense annual %)")
    print("| group / class | n | net alpha | SE | residual SD | expense | market beta | funds with front / deferred load |")
    print("|---|---|---|---|---|---|---|---|")
    for k, d in S["distributions"].items():
        f = lambda x, s=100: "-" if x is None else f"{x['p10'] * s:.2f} / {x['p50'] * s:.2f} / {x['p90'] * s:.2f}"
        print(f"| {k} | {d['n']} | {f(d['alpha_q'])} | {f(d['se_q'])} | {f(d['sres_q'])} | {f(d['expense'])} | {f(d['mkt_beta'], 1)} | {d['front_load_nonzero']} / {d['deferred_nonzero']} |")
    print("\n## Empirical prior, active funds (quarterly %)")
    print("| class | n | mean m | s (90% bootstrap) | cross-sectional SD | RMS SE |")
    print("|---|---|---|---|---|---|")
    for c, p in S["prior"].items():
        print(f"| {c} | {p['n']} | {p['m'] * 100:+.3f} | {p['s'] * 100:.3f} ({p['s_lo'] * 100:.3f}-{p['s_hi'] * 100:.3f}) | {p['cross_sd'] * 100:.3f} | {p['mean_se'] * 100:.3f} |")
    print("\n## Claims 102/106 and 039 at the ranges (active funds; empirical-Bayes beliefs; kappa assumed one-way)")
    print("| class | kappa | share bought from an all-ETF start | C^- median if bought (bp/q; cap 0.25) | C^- sum over funds (bp/q) | history needed, p50 (quarters) | own history p50 (quarters) | share certifiable |")
    print("|---|---|---|---|---|---|---|---|")
    for c, t in S["theorems"].items():
        for k in ("kappa_0bp", "kappa_10bp", "kappa_50bp"):
            x = t[k]
            print(f"| {c} | {k[6:]} | {x['share_bought']:.2f} | {x['Cminus_bp_median_if_bought']:.2f} | {x['Cminus_bp_sum']:.2f} | "
                  f"{P(x['n_needed_quarters'], s=1)} | {P(x['history_quarters'], s=1)} | {x['share_certifiable']:.2f} |")
    print("\n## Claims 036/038: Kalman gain and the anticipation bound (active funds)")
    for c, t in S["theorems"].items():
        g = t["kalman_gain"]
        print(f"- {c}: gain p10/p50/p90 {g['p10']:.3f}/{g['p50']:.3f}/{g['p90']:.3f}; share with gain > theta/(1+theta): theta 1% {t['share_gain_over_theta']['0.01']:.2f}, "
              f"5% {t['share_gain_over_theta']['0.05']:.2f}; (kappa/(1-kappa))^2 Dur p90 at Dur 1/3/5: "
              + ", ".join(f"{t['anticipation_bound'][f'Dur{D}']['p90']:.4f}" for D in (1, 3, 5)))
    print("\n## Claim 105 (active funds against the stated menus)")
    for c, d in S["claim105"].items():
        print(f"- {c} vs {d['menu']} ({d['n']} funds): unhedgeable share p10/p50/p90 {P(d['unhedgeable_share'], 'p10')}/{P(d['unhedgeable_share'])}/{P(d['unhedgeable_share'], 'p90')}%; "
              f"holding shift per one-SD premium error p50/p90 {P(d['holding_shift_per_sd'], 'p50', 1)}/{P(d['holding_shift_per_sd'], 'p90', 1)} (unconstrained; share above 0.1: {d['share_shift_over_0_1']:.2f})")
    print("\n## Claim 104: two-stage loss bound L_E^2/(2 gamma), bp per quarter (spanning menu, one ETF per factor)")
    for c, d in S["claim104_bound_bp"].items():
        print(f"- {c}: ETF fees p10/p50/p90 {d['etf_fee_annual']['p10'] * 100:.2f}/{d['etf_fee_annual']['p50'] * 100:.2f}/{d['etf_fee_annual']['p90'] * 100:.2f}% a year; "
              + "; ".join(f"{k}: {v:.3f}" for k, v in d.items() if k != "etf_fee_annual"))


if __name__ == "__main__":
    main()

# Numerical supplement: illustrative forecast revisions

The inputs are assumed. All benefits below are differences in the additive quarterly mean–variance score, normalized by initial wealth. They are not realized or annualized returns. Transaction costs and the stipulated risk charge are already deducted. No empirical calibration or long-horizon gain is established.

The current fund-trading benefit compares joint and ETF-only one-review optimization. The planning gain compares the full two-review policy with repeated one-review optimization, evaluated over the same two reviews. Both policies can trade every instrument next quarter.

| Design | Cases | Median planning gain, bp | Maximum planning gain, bp | Maximum current fund benefit, bp |
|---|---:|---:|---:|---:|
| revisions | 108 | 0.003206 | 0.391720 | 1.093511 |
| extension | 49 | 0.211509 | 0.537351 | 6.300077 |

These medians summarize the specified grids, which include controls and duplicate no-news configurations; they do not estimate a population median.

## Complete trades and score comparisons

`instrument_trades.csv` supplies every instrument’s starting holding, current trade, post-trade holding and expected next-review trade for all 157 cases and all three policies. Holdings and trades are percentages of initial wealth. Cash and current trading cost are also reported; sales finance purchases and costs. `case_metrics.csv` supplies both benefit measures and current/expected next-review transaction costs for each policy. Source and case identifiers match the complete original case data in the bundle.

## Cash prices for the three Figure 2 cases

These are solver-selected multipliers from independently constructed quadratic programs. Multipliers measure marginal score per dollar of relaxed funding, not basis points of portfolio return. The effective current price includes expected future cash value. A fixed-policy continuation program does not identify an economically comparable root multiplier, so the repeated one-review root is solved separately.

| Forecast | One-review root multiplier | Planned root multiplier | Planned mean next multiplier | Effective planned current price | Planned next min | Planned next max |
|---|---:|---:|---:|---:|---:|---:|
| premium_down_persistent | 0.00250136 | 0.00267482 | 0.00270619 | 0.00538102 | 0.00223955 | 0.00349576 |
| alpha_up | 0.00279582 | 0.00277156 | 0.00265590 | 0.00542746 | 0.00195792 | 0.00337723 |
| alpha_down | 0.00259992 | 0.00250853 | 0.00263966 | 0.00514819 | 0.00197246 | 0.00336400 |

Cash is zero to numerical tolerance at both reviews. In both policies all next-review multipliers exceed 1e-7; the separately solved one-review root and the joint planned root are also positive. This establishes a positive marginal cash value for the selected solutions, not a decomposition of the planning gain into funding and cost-timing contributions. Multiplier nonuniqueness is possible.

Maximum holding discrepancy with the original calculations: 9.12e-09 of wealth. Maximum value discrepancy: 7.36e-08 bp. Solver warnings: 0.

## Fee credit and the negative-alpha case

Fee credits are obtained by multiplying the fund loading matrix in ETF units by the ETF fee vector: 2.10, 2.15, 1.10, 1.15, 3.10, 2.85 bp per quarter. This is an algebraic expected-payoff comparison at fixed factor exposure, not a fee-ablation estimate of fund allocations.

| Forecast in all-negative-old-alpha configuration | Gross fund trade, one review (% wealth) | Gross fund trade, planning (% wealth) |
|---|---:|---:|
| unchanged | 0.00000 | 0.00000 |
| premium_down_persistent | 0.00000 | 0.00000 |
| premium_up_persistent | 0.00000 | 0.00000 |
| premium_down_reverting | 0.00000 | 0.00000 |
| premium_up_reverting | 0.00000 | 0.00000 |
| alpha_up | 0.00000 | 3.51813 |
| alpha_down | 0.00000 | 3.68504 |
| anticipated_down | 0.00000 | 0.00000 |
| anticipated_up | 0.00000 | 0.00000 |

Initial fund share is 21.4269%; the remaining capital is in ETFs and starting cash is zero. No claim is made that this assumed configuration represents the average mutual fund.

## Reproduction

The analysis design was saved before recovering the omitted budget diagnostics. `analysis/review_round4/analyze.py` exports the two CSVs and solves the three selected dual diagnostics without changing any economic input. Its independent tree construction is `analysis/forecast_revision/verify.py`. The other designs, result files, verification records and source inputs are included under their respective analysis directories. Full source hashes, tolerances, conditional duals and warnings are in `diagnostics.json`.

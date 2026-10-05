# Responding to new forecasts from an already optimal portfolio

All inputs are assumed. This is a conditional numerical application of existing M9, not a backtest or a new theorem. The starting portfolio uses only old beliefs. Both policies respect the funded budget at both reviews.

## What the control establishes

Under unchanged beliefs, the baseline one-quarter and two-review policies both leave the starting holdings unchanged (planning gain 0.000000 bp). Thus the forecast-response examples below do not obtain their gain by correcting an arbitrary initial allocation. This is a result for these cases, not a general no-trade theorem.

The inherited portfolio is the old one-quarter optimum without investor trading costs, with acquisition costs treated as sunk. It is an assumed already-held target, not a claim that a previous cost-aware trading path or infinite-horizon policy would land exactly there. We independently reproduce it and verify that actual trading costs leave it optimal for the unchanged one-quarter problem. Future return marking and filtering remain active.

| Instrument | Old optimal holding | One-quarter after premium revision | Plan ahead after premium revision |
|---|---:|---:|---:|
| Equity A | 18.57% | 18.57% | 18.57% |
| Equity B | 8.05% | 8.05% | 8.05% |
| Duration A | 12.22% | 19.19% | 21.07% |
| Duration B | 0.00% | 0.00% | 0.00% |
| Credit A | 30.69% | 30.69% | 30.69% |
| Credit B | 10.01% | 10.01% | 10.01% |
| Equity ETF | 20.47% | 13.49% | 11.62% |
| Duration ETF | 0.00% | 0.00% | 0.00% |
| Credit ETF | 0.00% | 0.00% | 0.00% |

The prespecified headline revision lowers the equity sleeve premium from 120 to 105 bp per quarter and raises duration from 30 to 35 bp; credit stays at 60 bp. The revised means are expected to persist, with uncertain future realizations and further filtering. Current belief variances are held fixed across the revision.

Both policies sell the equity ETF to buy Duration A. Planning makes a larger adjustment. The ETF-only one-quarter alternative sells the equity ETF and buys the duration ETF instead; it respects the same budget and freezes fund dollar holdings today only.

Allowing fund trades improves the current one-quarter score over its ETF-only optimum by 0.0586 bp. Separately, planning improves the two-review score over repeated one-quarter optimization by 0.0595 bp. These are distinct comparisons, with different objectives and baselines.

![Actual trades after forecast revisions.](forecast_revision_trades.png)

## All nine baseline scenarios

The old ETF allocation is 20.47% of initial wealth. All percentages below use initial wealth, so holdings plus cash plus current costs sum to 100%. A small difference between purchase and sale amounts pays trading costs.

| Forecast scenario | One-quarter ETF | Plan-ahead ETF | One-quarter gross fund trades | Plan-ahead gross fund trades | Planning gain |
|---|---:|---:|---:|---:|---:|
| Unchanged forecasts | 20.47% | 20.47% | 0.00% | 0.00% | 0.0000 bp |
| Equity premium -15 bp; duration +5 bp, persistent | 13.49% | 11.62% | 6.97% | 8.84% | 0.0595 bp |
| Equity premium +15 bp; duration -5 bp, persistent | 27.44% | 28.85% | 6.98% | 8.39% | 0.0358 bp |
| Equity premium -15 bp; duration +5 bp, reverting | 13.49% | 12.60% | 6.97% | 7.86% | 0.0147 bp |
| Equity premium +15 bp; duration -5 bp, reverting | 27.44% | 27.86% | 6.98% | 7.40% | 0.0033 bp |
| Equity A alpha +5 bp, persistent | 20.47% | 17.12% | 0.00% | 3.34% | 0.0461 bp |
| Equity A alpha -5 bp, persistent | 20.47% | 24.25% | 0.00% | 3.79% | 0.0587 bp |
| Same current means; next equity -15 bp, duration +5 bp | 20.47% | 20.47% | 0.00% | 0.00% | 0.0000 bp |
| Same current means; next equity +15 bp, duration -5 bp | 20.47% | 20.47% | 0.00% | 0.00% | 0.0000 bp |

Gross fund trades sum the absolute fund purchases and sales; they are not net fund allocation changes. The reverting forecasts retain the same current revision as their persistent counterparts but expect 20% of it to reverse by the next review. Their one-quarter actions therefore agree; their planning decisions can differ.

The manager revisions give a particularly direct distinction: the one-quarter policy makes no current trade after either +5 or -5 bp in Equity A alpha, while planning buys after the increase and sells after the decrease. The revised estimate is still uncertain. This illustrates a forecast-dependent trade boundary; it does not imply that every update warrants trading.

Anticipated premium changes leave current means unchanged. At baseline neither policy trades today, even with planning: knowing about a future change does not automatically justify bringing the trade forward.

## Current versus future contribution to the planning gain

| Forecast | Change in current score | Change in expected continuation | Total planning gain |
|---|---:|---:|---:|
| Equity premium -15 bp; duration +5 bp, persistent | -0.0340 bp | 0.0935 bp | 0.0595 bp |
| Equity A alpha +5 bp, persistent | -0.0901 bp | 0.1362 bp | 0.0461 bp |
| Equity A alpha -5 bp, persistent | -0.1056 bp | 0.1643 bp | 0.0587 bp |

Current and continuation scores each include their own trading costs and risk charge. The decomposition is an accounting identity. It does not attribute the gain uniquely to learning, funding, or transaction-cost timing. In particular, the ETF change is not by itself a measurement of a liquidity reserve.

## Sensitivities, including unchanged-beliefs controls

The complete prespecified grid contains 108 cases, including both directions of forecast revisions, risk aversion 2–3, prior mean-error SD scales 0.5–2 for both premia and alpha, an all-negative-old-alpha configuration, and zero/equal/unequal investor trading costs. State-noise variance and realized-return risk are held separately fixed.

| Block | Cases | Median gain | Maximum gain | Cases above 1 bp |
|---|---:|---:|---:|---:|
| core | 54 | 0.0150 bp | 0.1844 bp | 0 |
| costs | 54 | 0.0001 bp | 0.3917 bp | 0 |
| all | 108 | 0.0032 bp | 0.3917 bp | 0 |

Largest gain: 0.391720 bp, `premium_up_persistent`, gamma 2.5, prior-SD scale 1.0, old-alpha offset 0 bp, fund cost 20.0 bp and ETF cost 2.0 bp. It is an extremum, not the selected headline.

| Configuration | Unchanged-beliefs planning gain |
|---|---:|
| gamma 2.5, SD scale 0.5, alpha offset 0 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 2.0, alpha offset 0 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 2.0, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 3.0, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset -5 bp, fund/ETF cost 5.0/2.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 0.0/0.0 bp | 0.000060 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 0.0/2.0 bp | 0.000061 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 20.0/2.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 5.0/0.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 5.0/5.0 bp | 0.000000 bp |
| gamma 2.5, SD scale 1.0, alpha offset 0 bp, fund/ETF cost 20.0/5.0 bp | 0.000000 bp |

The control need not vanish in every configuration: tomorrow’s marking, filtering and predictive risk can affect today’s funded allocation even without an expected mean change. `control_comparison.csv` reports each gain minus its matched unchanged-beliefs control; that difference is descriptive, not an additive causal decomposition or proof about flexibility.

## Interpretation and limits

The useful framing is a manager responding to revised beliefs while carrying an existing portfolio. Three decisions are visible: whether to trade now, how far to move, and whether to implement through ETFs or active funds. Planning does not systematically demand more or fewer ETFs. The resulting portfolio changes can be visible while the incremental score benefit remains small. These runs do not establish economically large performance gains.

The previous arbitrary-start examples remain saved. They answer portfolio construction or correction questions; they should not be used to claim that the same gains arise when rebalancing an already optimal portfolio. This new control addresses that confound without changing the opportunity set to manufacture a larger effect.

All numbers remain illustrative assumptions. The study conditions on forecast revisions; it does not model the news that generated them, simulate a historical path into the incumbent, estimate true alpha, or test out-of-sample returns. Its two-review additive mean-variance objective is not a terminal-wealth utility objective. The finite-law filter is linear rather than an exact posterior. No new theorem or Lean source was introduced.

## Numerical checks and reproduction

All 108 joint solves returned optimal. Maximum independent old-portfolio holding error: 3.07e-06; maximum one-quarter trade under old beliefs: 1.85e-10 of initial wealth. Maximum reconstructed objective error: 7.3e-13; minimum future cash: -7.35e-11 (solver-scale tolerance). Recorded main-run warnings: 90; independent warnings: 0.

A separate implementation reconstructs the baseline state law, moments, linear filter and vectorized QPs, without using the lab's tree or policy solver. Across all nine baseline scenarios it reproduces gains within 2.04e-08 bp and holdings within 9.12e-09 of initial wealth. This is a numerical check, not machine-checked formalization or a lab evidence-status promotion.

The 90 internal solver warnings were confined to five cost-sensitivity cases (IDs 78, 99, 101, 103, 107). A further independent vectorized-QP calculation checks all five and the largest-gain case (ID 74). All six checks completed with 0 warnings, matching gains within 3.19e-08 bp and every compared policy value within 1.03e-07 bp. The original warnings remain recorded; results are in [sensitivity_verification.json](sensitivity_verification.json).

The first run stopped at an independent SLSQP line-search failure. Its partial results are preserved in `initial_attempt.jsonl`; the numerical stopping-tolerance change is documented under Deviations in DESIGN.md. No economic scenario changed.

```bash
.venv/bin/python manuscript2/analysis/forecast_revision/run.py
.venv/bin/python manuscript2/analysis/forecast_revision/verify.py
.venv/bin/python manuscript2/analysis/forecast_revision/report.py
```

Inputs and source hashes: [results.json](results.json). Full tabular results: [results.csv](results.csv). Design: [DESIGN.md](DESIGN.md). Independent checks: [verification_comparison.json](verification_comparison.json).

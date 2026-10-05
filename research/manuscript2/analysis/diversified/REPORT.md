# Diversification first, then the value of planning

This setting has a portfolio to construct: equity, duration and credit provide different return/risk tradeoffs, and several active funds and ETFs offer overlapping implementations. Diversification is chosen by the objective, without position caps or target allocation constraints. The additional gain from planning ahead is measured separately and remains modest in the baseline.

All inputs are illustrative assumptions. This is existing M9 on a six-fund, three-ETF menu, not an empirical calibration or a new theorem. The design was saved before computation in [DESIGN.md](DESIGN.md); the previous studies are preserved, not silently recalibrated.

## Why this is a portfolio problem

The three underlying exposure sleeves have quarterly excess means 1.20%, 0.30%, 0.60%, return SDs 8%, 3%, 4%, and correlations 0 for equity-duration, 0.4 for equity-credit and 0.2 for duration-credit, before ETF tracking residuals and mean uncertainty. The sleeve returns are therefore neither identical nor assumed mutually independent. Two active funds per sleeve have different factor tilts, uncertain small net alphas, and residual return risks. Their returns correlate through the shared factors; independent fund residuals remain an explicit simplifying assumption.

Net alpha estimates are (4,2,1,0.5,3,1) bp per quarter, with alpha prior SDs (20,30,10,15,15,25) bp. Unlike the old example, a large alpha advantage does not select one fund to supply every exposure. Manager-specific forecasts can reverse the ordering within each pair. Initial uncertainty and future state noise are distinct inputs; the uncertainty sensitivity changes the former only.

First remove investor trading costs to inspect the opportunity set itself, retaining ETF fees and predictive risk. Risk aversion is 2.5; all holdings are funded, long-only and uncapped:

| Static alternative | Portfolio or largest holding | Quarterly score |
|---|---|---:|
| Best single instrument plus cash | 73.55% Equity ETF, remainder cash | 43.40 bp |
| ETF-only optimum | Equity 50.48%, duration 10.05%, credit 39.47% | 54.67 bp |
| Full fund/ETF optimum | 6 positions above 1%; largest 30.69% | 57.93 bp |

ETF diversification alone improves the quarterly score by 11.27 bp relative to the best single-instrument alternative. Allowing funds adds a further 3.26 bp. These are static comparisons; neither is a gain from planning ahead. The full optimum has expected quarterly excess return 0.890% and predictive return SD 4.988%.

Across the 27 prespecified static cases (gamma 2–3; alpha means 0,1,2 times baseline; initial alpha uncertainty 0.5,1,2 times baseline), the full portfolio's score advantage over the best single instrument plus cash is at least 8.99 bp. Its largest position never exceeds 42.07%. Those are observed outcomes, not imposed limits. An independently constructed covariance and SLSQP solve reproduce the baseline holdings within 7.3e-09 of initial wealth.

## Actual construction with trading costs

Baseline costs are 5 bp per fund purchase/redemption and 2 bp per ETF purchase/sale. Fees remain 2,1,3 bp per quarter for the equity, duration and credit ETFs. Starting from cash, the current allocations are:

| Instrument | One-quarter | Plan ahead |
|---|---:|---:|
| Equity A | 10.76% | 14.49% |
| Equity B | 3.71% | 5.90% |
| Duration A | 11.44% | 12.15% |
| Duration B | 0.00% | 0.00% |
| Credit A | 27.48% | 29.94% |
| Credit B | 8.56% | 9.94% |
| Equity ETF | 34.62% | 27.54% |
| Duration ETF | 0.00% | 0.00% |
| Credit ETF | 3.40% | 0.00% |
| Cash | 0.00% | 0.00% |
| Today's costs | 0.04% | 0.04% |

![Actual uncapped holdings, from cash.](../../figures/fig4_diversified.png)

One-quarter optimization holds 61.94% in funds and 38.02% in ETFs; planning ahead holds 72.41% and 27.54%. Both leave essentially zero cash. Planning gains 0.1933 bp in the two-review objective. The allocation changes are visible, but the gain is small: the objective values nearby implementations similarly. This is not evidence of a large investment-performance improvement.

## Starting holdings and forecast changes

All four starts have wealth one. The ETF and fund starts are equally weighted within their respective menus. The mixed start holds 40% funds, 55% ETFs and 5% cash, with instrument weights specified in the design. No portfolio gets free financing. Each policy sees the same returns and forecasts, uses the same linear filter, and respects every future budget. The one-quarter policy learns and reoptimizes; it omits continuation only when choosing today's action.

| Start, steady forecast | One-quarter funds / ETFs | Plan-ahead funds / ETFs | Planning gain |
|---|---:|---:|---:|
| cash | 61.94% / 38.02% | 72.41% / 27.54% | 0.1933 bp |
| etfs | 21.34% / 78.65% | 56.80% / 43.16% | 0.7481 bp |
| funds | 85.75% / 14.24% | 82.51% / 17.47% | 0.1616 bp |
| mixed | 44.48% / 55.52% | 63.56% / 36.42% | 0.3230 bp |

The manager-rotation forecast swaps each pair's next-review alpha means, so it does not preserve the same manager ranking forever. The premium rotation lowers the equity-sleeve premium by 15 bp and raises duration's by 5 bp while keeping credit's unchanged; the reverse forecast changes those signs. These are specified forecasts, not estimates of predictability. All use the same persistence and state-noise variances.

| Forecast | From cash | From ETFs | From funds | From mixed |
|---|---:|---:|---:|---:|
| steady | 0.1933 bp | 0.7481 bp | 0.1616 bp | 0.3230 bp |
| manager_rotation | 0.2782 bp | 0.6227 bp | 0.0687 bp | 0.2007 bp |
| premium_rotation | 0.3177 bp | 0.7158 bp | 0.1158 bp | 0.3669 bp |
| premium_reverse | 0.2155 bp | 0.6803 bp | 0.2137 bp | 0.3070 bp |

## Full sensitivity and scope

The 80 core cases cross the four starts and four forecasts with alpha uncertainty scales 0.5,1,2 at gamma 2.5 and gamma 2,3 at baseline uncertainty. The 64 cost cases separately vary fund costs to 0 or 20 bp and ETF costs to 0 or 5 bp, keeping other baseline inputs. These are planned sensitivities, not a random sample.

| Block | Cases | Median planning gain | Maximum planning gain | Cases above 1 bp |
|---|---:|---:|---:|---:|
| core | 80 | 0.2677 bp | 0.9736 bp | 0 |
| costs | 64 | 0.1254 bp | 1.3684 bp | 7 |
| all | 144 | 0.2321 bp | 1.3684 bp | 7 |

The grid maximum is 1.3684 bp: start `funds`, forecast `premium_reverse`, gamma 2.5, alpha-uncertainty scale 1, fund cost 20 bp and ETF cost 2 bp. It is reported as an extremum, not selected as the headline case.

Across all 144 dynamic comparisons and both policies, at least 3 instruments have positions above 1%, and the largest position is 52.62% of initial wealth. The setting supports diversified portfolios without mechanically fixing their composition. Factor exposure units need not sum to 100% because fund loadings differ from one; capital weights plus cash and costs do, and no investor leverage is allowed.

The interpretation is narrower than a claim that dynamics are always important: the opportunity set supports ordinary diversification; funds and ETFs supply different implementations; anticipation can change their mixture, but the incremental objective gains must be reported on their own scale. The static diversification calculation is standard portfolio mathematics, not a new research theorem. The dynamic solver instantiates the existing funded model, not a new algorithm. No result establishes empirical performance, optimal long-run weights, a stationary attractor, or the superiority of the linear filter to a true posterior.

Remaining assumptions include known loadings and return covariances, independent active residuals conditional on factors, small assumed alpha forecasts, assumed investor costs, and a two-review additive mean-variance objective. This is a coherent illustrative portfolio construction problem; it is not a calibrated real-world fund selection exercise.

## Verification and reproduction

All 144 joint solves returned optimal status. Recorded warnings: 0. Maximum reconstructed objective error: 7.3e-13; most negative reconstructed cash: -1.42e-11, within numerical tolerance. A separate implementation constructs the state law, diagonal filter and vectorized QPs independently of the lab's tree and solver. It reproduces the eight baseline steady/manager-rotation cases with maximum gain difference 7.53e-09 bp and maximum holding difference 6.9e-08. No formal source was changed.

```bash
.venv/bin/python manuscript2/analysis/diversified/static.py
.venv/bin/python manuscript2/analysis/diversified/run.py
.venv/bin/python manuscript2/analysis/diversified/verify.py
.venv/bin/python manuscript2/analysis/diversified/report.py
```

[results.csv](results.csv) contains every dynamic case; [results.json](results.json) includes holdings, costs, state details for baseline cases and source/environment metadata. [static_results.json](static_results.json) records all 27 construction checks. [verification.json](verification.json), [verification_comparison.json](verification_comparison.json) and [summary.json](summary.json) contain the independent results and summaries.

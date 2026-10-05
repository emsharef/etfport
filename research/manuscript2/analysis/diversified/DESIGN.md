# A portfolio construction problem with distinct exposures

Saved before computation, 2026-10-01. Numerical application of existing M9, not new theory. The user requested a setting where diversification has an economic purpose, rather than an imposed concentration cap. This design replaces the previous overlapping three-fund menu as the main application; earlier outputs remain intact.

## Economic design

Three investable exposure sleeves: equity, duration and credit. Their assumed quarterly excess means are 1.20%, 0.30%, 0.60%; return standard deviations 8%, 3%, 4%; correlations equity-duration 0, equity-credit 0.4, duration-credit 0.2. These are illustrative assumptions, not calibrated ETF observations. The differing return/risk profiles provide an economic diversification motive. No target sleeve weights, minimum positions or concentration caps are imposed.

Represent those correlated sleeves through three independent primitive factors, so the existing M9 solver and diagonal state dynamics apply without changing model definitions. ETF loadings are [[1,0,0],[0,1,0],[0.2,4/15,1]], primitive shock SDs [0.08,0.03,sqrt(0.00128)], and primitive means [0.012,0.003,0.0028]. Primitive mean prior SDs are [0.004,0.0015,0.002]. ETF quarterly fees are [2,1,3] bp; residual return SDs [0.001,0.0005,0.001]. All returns are in cash-account units.

Two active funds per sleeve. Their loadings in *ETF sleeve units*, before multiplying by the ETF loading matrix, are:

| Fund | Equity | Duration | Credit | Net alpha mean, bp/quarter | Residual return SD | Alpha prior SD, bp |
|---|---:|---:|---:|---:|---:|---:|
| Equity A | 1.05 | 0 | 0 | 4 | 4% | 20 |
| Equity B | 0.90 | 0.05 | 0.10 | 2 | 5% | 30 |
| Duration A | 0 | 1.10 | 0 | 1 | 1.5% | 10 |
| Duration B | 0.05 | 0.90 | 0.05 | 0.5 | 2% | 15 |
| Credit A | 0.05 | 0 | 1.00 | 3 | 2.5% | 15 |
| Credit B | 0 | 0.15 | 0.90 | 1 | 3% | 25 |

Alphas are small relative to total returns and uncertain; residual return risks represent imperfect active implementation. Fund returns are correlated through the factor exposures; fund residuals are independent in this illustration, a limitation to disclose. A positive-alpha fund need not replace its entire sleeve's ETF because it adds residual risk and has different exposures. ETF holdings are not required. A corner result remains permissible.

Risk aversion 2.5 initially, with 2 and 3 as sensitivities. Initial wealth 1; long-only, no borrowing, no additional instrument caps, no minimum cash, and no requirement to invest all wealth in risky assets. Baseline investor costs: 5 bp per fund purchase or redemption; 2 bp per ETF purchase or sale. These are assumed investor costs; fees and internal costs are distinct.

## Stage 1: validate static construction first

Before the dynamic experiment, solve (a) the ETF-only portfolio, (b) the full portfolio, and (c) the best single instrument plus cash, all with no investor transaction costs but including ETF fees and predictive risk. Report positions, sleeve exposures, expected return, volatility, score and the improvement over the best single-instrument alternative. Reconstruct the sleeve covariance independently from the declared means, volatilities and correlations; independently solve the baseline static problem. Compare baseline costs as well.

Run 27 static sensitivities: gamma 2,2.5,3; alpha means scaled by 0,1,2; alpha prior SDs scaled by 0.5,1,2. Record support size and concentration without imposing either. Examine whether diversification is supported by return/risk tradeoffs rather than an enforced mix. Do not tune means to hit target weights after seeing outputs. If the setup again collapses, document it before revising the design.

## Stage 2: compare funded policies

Use the existing 432-state finite axis law (18 parameter atoms times 24 return-shock atoms), with positive gross returns checked. Publicly observe factors and instrument returns regardless of ownership; the filter is linear, not the finite law's exact posterior. The two policies use identical information and forecast laws. One-review optimization reoptimizes next quarter; full two-review optimization anticipates that funded continuation. No borrowing relaxation is included.

All latent means have persistence 0.8. State-noise SDs are [0.001,0.0005,0.0008] for the primitive premia and 0.0005 for each alpha. Keep state-noise variances fixed when initial uncertainty is varied. The baseline long-run means equal current means. Four forecasts:

1. **Steady:** next-review mean forecasts equal today's means.
2. **Manager rotation:** swap the two funds' expected alphas within each sleeve at the next review. Set long-run means to obtain that change under persistence 0.8. This changes relative rankings, rather than adding the same alpha to every fund.
3. **Premium rotation:** next-review equity-sleeve mean falls 15 bp, duration-sleeve mean rises 5 bp, credit-sleeve mean is unchanged. Convert that change to primitive-factor means before setting long-run means.
4. **Reverse premium rotation:** the opposite premium change.

Initial portfolios: all cash; equally weighted ETFs; equally weighted funds; mixed fund weights [0.10,0.05,0.05,0.05,0.10,0.05], ETF weights [0.25,0.10,0.20], cash 0.05. All have wealth 1.

**80 core cases:** alpha-prior SD scales 0.5,1,2 at gamma 2.5, plus gamma 2 and 3 at uncertainty scale 1; each crossed with four starts and four forecasts. **64 cost cases:** at gamma 2.5 and uncertainty scale 1, separately change fund costs to 0 or 20 bp, or ETF costs to 0 or 5 bp; cross with four starts and four forecasts. Total **144 dynamic comparisons**. Baseline alpha means are unchanged throughout this dynamic grid.

Report the steady and manager-rotation baselines at all four starts, whether or not planning helps. Separate portfolio-construction benefits (static diversification) from incremental dynamic gains. Report all cases and extrema with their inputs. Do not select a new main case by maximizing the planning gain. There is no claim about long-horizon terminal utility, an allocation attractor or empirical performance.

## Verification and deliverables

Use the existing solver; no new theorem or formal-source edit. Check every budget, marking and objective identity. Independently reconstruct moments and solve baseline static and dynamic cases with separate code. Save design, code, source hashes, environment, full results and a report. A figure should show where the portfolio's diversification comes from and how planning changes actual trades, not just an unexplained policy-loss curve. Preserve the earlier studies and revise the manuscript's main numerical application only after this setting has been checked.

## Deviations

None at registration.

---
id: 36
title: "Check of D15c (claim 107): the fund's effective band and the no-trade region with one ETF across reviews, against an exact two-instrument dynamic program, with the targets' innovation correlation varied"
status: reproduced
model_version: M7
direction: D15c
claims: [29, 100, 102, 104, 107]
code: experiments/036/
---
## Question
**Job: verify behaviour under a theorem's assumptions**, and map one open item (proposal section 6; AGENTS.md
rule 22).

Routing:
- **Source:** mathb's note 2026-09-29-d15c-formulas, on claim 107.
- **Claim state:** red-passed at registration (red/review-107-recheck), not yet on main. The claims field lists
  the claims it builds on; 107 is added when it is on main.
- **Order:** by the formula-check order, it runs after the approved claims' checks.
- **Statement changes:** the check follows the Statement current at run time. Any change is recorded under
  Deviations.
- **Scope:** the human's scope-down applies. This checks stated formulas and plots them. The one open item is
  mapped only as the note asks.

- **Every input is an assumption.**
- **The claim's formulas are the result.**

Do claim 107's statements agree with an exact dynamic program for one fund A and one ETF E?
- **Part 1b, ceiling:** the fund's effective band has width at most (kappa^+_A + kappa^-_A)/(gamma
  sigma^2_{A.E}), the residual-variance ceiling, at every review, state and ETF incumbent.
- **Part 1c, bracket:** hi <= a* + [kappa^-_A + beta kappa^+_A + H^+]/c^res and lo >= a* - [kappa^+_A + beta
  kappa^-_A + H^-]/c^res.
- **Part 1d, last-review edges:** exact, with the three regimes.
  - ETFs re-hedging the same way at both edges: the ceiling, shifted by rho c_E/c^res.
  - Opposite directions: the ceiling minus |rho|(kappa^+_E + kappa^-_E)/c^res.
  - ETF idle at both edges: the fund-alone width (kappa^+_A + kappa^-_A)/(gamma Sigma_AA).
- **Part 2, outer parallelotope:** the no-trade region lies inside x* + (gamma Sigma)^{-1} prod_i [-(kappa^+_i +
  beta kappa^-_i), kappa^-_i + beta kappa^+_i]. Its Sigma-diameter obeys 029's 2b inequality.
- **Part 3, frictionless ETF:** the fund's band equals the one-instrument dynamic band of the reduced problem
  (curvature gamma sigma^2_{A.E}, target a*), and does not depend on the ETF incumbent.

**Open item** (mathb's request; mapped, not tested): how the fund's band moves inside the bracket with the
correlation of the two targets' innovations, at a fixed correlation of their risks.

**What counts against the claim:** at any point below, beyond the lattice resolution (one holdings-grid step h):
- a band wider than the ceiling;
- an edge outside the bracket;
- a last-review edge differing from 1d's;
- a no-trade point outside the parallelotope or violating the diameter inequality;
- a frictionless-ETF band that differs from the reduced one-instrument band or moves with the ETF incumbent.

Disagreements are located and sent to mathb and red by note.

## Design
### Model: M7 in tracking form, the finite-law variant (claims 029 and 107's Setting)
- **Objective.** Minimize E sum_t [(gamma/2)(x_t - x*_t)' Sigma (x_t - x*_t) + C_A(u_A) + C_E(u_E)].
- **Instruments.** One fund and one ETF, with directional rates. No marking (bar g = 1), beta = 1, slack budget.
- **Bounds.** The holdings grid is wide enough that no bound binds on the bands measured. Points where it
  binds are excluded and counted.
- **Covariance.** Sigma is fixed across reviews: gamma = 5, Sigma_EE = 0.0854^2 and Sigma_AA = 0.0854^2 +
  0.02^2. The risk correlation corr is in {0, 0.5, 0.9, 0.97}, with Sigma_AE = corr sqrt(Sigma_AA Sigma_EE).
  - 0.97 is the fund with market loading 1 and a 2% residual.
- **Targets.** Each target moves on its own lattice by +-1 step per review:
  - fund step u_A = 0.5 times the fund's residual static width;
  - ETF step u_E = 0.5 times the ETF's static width;
  - joint law P(++) = P(--) = (1 + r)/4 and P(+-) = P(-+) = (1 - r)/4, so the innovation correlation is r in
    {-0.8, 0, 0.8}.
  - The coarse step (0.5 width) and a fine step (0.1 width) are both run.
- **Rates** (kappa^+ = kappa^-):
  - fund in {10, 50} bp;
  - ETF in {0, 2, 10, 50} bp;
  - one asymmetric pair: fund 100/0 bp, ETF 5/5 bp.
- **Horizon:** T in {1, 4, 8}.

### Solver
The exact dynamic program on a two-dimensional holdings grid, one grid per target state:
- **Bellman step.** Experiment 023's exact L1 conjugate transform (fastdp.l1), applied along each instrument's
  axis in turn. Exact, because the trading cost is separable across instruments.
- **Expectation.** Over the four-point target law, exact.
- **Grid step.** h = 1/100 of the smaller static width. The grid covers the (1 + beta)-widened parallelotope
  plus 20%.
- **Last review (part 1d).** It is also solved as a convex program (experiment 029's solver pattern, CLARABEL)
  at 200 ETF incumbents per point, as a grid-free check.
- **Reduced problem (part 3).** The one-instrument DP of experiment 023 (fastdp) with curvature gamma
  sigma^2_{A.E}, the fund's rates and its target lattice.

### Measurements
At every review t, target state and ETF incumbent p^- on a grid of 41 values across the ETF band:
- **The fund's effective band** [lo, hi]: the set of fund incumbents from which the optimal fund trade is zero,
  read from the policy on the grid.
- **The no-trade region**: the grid points from which neither instrument trades.

### Checks and curves
1. **Part 1b.** The largest width / ceiling over all t, states and p^-, against 1 + h/width.
   - Figure: width against corr at fixed rates (fund 10 bp, ETF 10 bp, T = 8, t = 0), with the ceiling and the
     fund-alone width.
2. **Part 1c.** Edge violations of the bracket, beyond h; counts per cell.
3. **Part 1d** (t = T - 1).
   - The DP edges and the convex program's edges against 1d's formulas, classified by regime (same, opposite or
     idle ETF slopes at the two edges).
   - Figure: the last-review width against kappa_E at corr = 0.97 and 0.5, between the fund-alone width and the
     ceiling.
4. **Part 2.**
   - The no-trade region's extent along each axis against the parallelotope's.
   - The largest (gamma (x - y)' Sigma (x - y)) / sum_i (kappa^+_i + kappa^-_i)|x_i - y_i| over pairs of
     no-trade points, which the claim says is <= 1.
5. **Part 3** (kappa_E = 0).
   - The DP fund band against the reduced one-instrument band: largest edge difference.
   - The band's range across p^-: the claim says 0.
6. **Open item.** At corr = 0.97 and 0.5, fund 10 or 50 bp, ETF 10 bp, T = 8, t = 0, r in {-0.8, 0, 0.8},
   coarse and fine steps: the fund's band width and centre relative to the ceiling and the bracket.
   - Reported as a table and a figure. Any regularity goes to mathb as a conjecture candidate.

**Precision.** Exact on the lattice. The reported error is the grid step h. As a resolution check, one cell per
part is rerun at h/2.

**Output:**
- **Committed:** experiments/036/run.py, report.py, summary.json and the figures.
- **Notes:** the result goes to mathb and PM; disagreements go to mathb and red.

## Deviations
1. **Claim state and order** (recorded before reporting).
   - **Claim state.** Claim 107 was approved on main before this run, and the check follows that Statement. The
     claims field now lists 107.
   - **Order.** The run comes before experiment 035. The human's scope-down keeps the Yahoo pilot last, and claim
     107's approval made this check runnable.
2. **Grid and solver** (recorded before reporting).
   - **Deviation coordinates.** Sigma is fixed, beta = 1, there is no marking and no bound binds, so the value
     depends only on the deviation d = x - x*_t. The DP runs in d, with the targets' four-point step as an exact
     index shift.
   - **Horizons.** The T = 8 run's review 8 - k is the first review of the k-review problem (stationarity), so
     the registered horizons T in {1, 4, 8} are its reviews 7, 4 and 0.
   - **Grid step.** The Design's single h (1/100 of the smaller static width) is replaced by a per-axis step: 1/100
     of that instrument's static width, capped at 1,500 points per axis over the (1 + beta)-widened
     parallelotope.
     - Otherwise high-correlation cells with cheap ETFs need up to 10^8 points.
     - The cap coarsens the ETF axis in the correlation-0.97 cells, and the ETF step reaches the fund's edges
       through the hedge ratio. So the fund-edge resolution there is h_A + |Sigma_AE| gamma h_E / c^res.
   - **Frictionless ETF.** With kappa_E = 0 there is no ETF width. Its target step and grid use the 10 bp ETF's
     width instead.
   - **ETF incumbents.** 41 incumbents are sampled across the parallelotope's ETF extent (inner 90%).
   - **Convex cross-check.** It uses 10 incumbents per cell over 6 cells, not 200. Each bisection starts from a
     held point, the DP band's centre, because the band need not contain d_A = 0.
   - **Refinement.** Two cells are rerun at h/2 as registered, plus the asymmetric cell at h/2 and h/4 (see 1d).

## Results
**Commands:** `uv run python experiments/036/run.py` (18 s on 6 processes), then
`uv run python experiments/036/report.py`. The environment is `uv.lock` at the reporting commit.
- **Assumptions.** Every input is an assumption (rule 22).
- **Coverage.** 216 DP cells, each with 8 reviews: 66,978 (cell, review, ETF incumbent) fund bands away from the
  grid edges. 30 bands are non-contiguous on the grid and are set aside.

**Verdict: claim 107 agrees with the exact two-instrument DP at every point checked, within the grid's
resolution.**

### Part 1b: the residual-variance ceiling (`fig_bands.png`, left)
- **Ceiling.** Every band is at most (kappa^+_A + kappa^-_A)/(gamma sigma^2_A.E) plus one grid step: 66,978 of
  66,978, with the largest ratio 1.0000.
- **Size.** The ceiling is 1/(1 - corr^2) times the fund-alone width: 1, 1.33, 5.3 and 16.9 at risk correlations
  0, 0.5, 0.9 and 0.97.
- **Where widths fall.** Observed widths run from 0.05 to 1.00 of the ceiling. At high correlation, a fund whose
  ETF hedges it holds a band up to 17 times wider than it would alone.

### Part 1c: the bracket
- **Bracket.** No edge falls outside [a* - (kappa^+_A + beta kappa^-_A + H^-)/c^res, a* + (kappa^-_A + beta
  kappa^+_A + H^+)/c^res]: 0 violations in 66,978.
- **Attained.** Both ends of the bracket are reached (ratio 1.000).

### Part 1d: the last review
- **Regimes.** 8,376 bands: 3,714 with opposite ETF trades at the two edges, 2,556 with the ETF idle at both, 2,100
  mixed and 6 with the same slope.
- **Edges.** Where the ETF trades at an edge, the edge equals 1d's formula within one grid step.
- **Widths by regime:**
  - opposite: the ceiling minus |rho|(kappa^+_E + kappa^-_E)/c^res;
  - idle at both edges: the fund-alone width;
  - same slope: the ceiling.
  All within two grid steps, except 12 bands in one asymmetric cell (fund 100/0 bp, ETF 5/5 bp, corr 0.97), 3
  coarse steps off. At h/2 that cell's error is 0.04 fine steps (0.0008), and at h/4 it is 0.92 fine steps, so
  it is resolution.
- **Between the two regimes.** The last-review width lies between the fund-alone width and the ceiling, to one
  grid step.
- **Grid-free check.** The last-review convex program agrees with the DP at 60 incumbents, to 0.56 of the
  effective resolution. That is 10 fund steps in the correlation-0.97 cells, where the capped ETF step dominates
  (Deviation 2).

### Part 2: the outer parallelotope
- **Inclusion.** None of 3.1 million no-trade grid points lies outside x* + (gamma Sigma)^{-1} prod_i
  [-(kappa^+_i + beta kappa^-_i), kappa^-_i + beta kappa^+_i], beyond one grid step.
- **Sigma-diameter.** The inequality gamma (x - y)' Sigma (x - y) <= sum_i (kappa^+_i + kappa^-_i)|x_i - y_i|
  holds on 20,000 sampled pairs per (cell, review), with the extreme points added.
- **Extent.** The region fills 7% to 101% of the parallelotope's extent along each axis.

### Part 3: frictionless ETF
- **Reduced band.** With kappa_E = 0, the fund's band equals the reduced one-instrument DP's band to one grid
  step, at 384 (cell, review) pairs.
- **ETF incumbent.** The band does not move with the ETF incumbent: its range across incumbents is 0 grid
  steps.

### Open item: the targets' innovation correlation (mapped, not tested; `fig_bands.png`, right)
Median width/ceiling at t = 0 (T = 8, ETF 10 bp); the centres are 0 throughout (symmetric rates):

| risk corr | fund rate | target step | r = -0.8 | r = 0 | r = +0.8 |
|---|---|---|---|---|---|
| 0.97 | 10 bp | 0.5 width | 0.50 | 0.52 | 0.52 |
| 0.97 | 10 bp | 0.1 width | 0.27 | 0.27 | 0.28 |
| 0.97 | 50 bp | 0.5 | 0.67 | 0.67 | 0.67 |
| 0.5 | 10 bp | 0.5 | 0.63 | 0.68 | 0.75 |
| 0.5 | 10 bp | 0.1 | 0.28 | 0.30 | 0.32 |
| 0.5 | 50 bp | 0.5 | 0.65 | 0.67 | 0.68 |

- **Pattern.** At a moderate risk correlation (0.5), the fund's band widens as the targets' innovations become
  more correlated: 0.63 to 0.75 of the ceiling from r = -0.8 to +0.8, coarse step, fund 10 bp.
- **Where it is weak.** At risk correlation 0.97 the effect is 0.02 or less. It also shrinks with the fund's
  own rate and with the target step.
- **Status.** A regularity for mathb as a conjecture candidate, not a finding.
- **Resolution checks at h/2:** the median width changes by 0.5 coarse steps.

### Reading
Claim 107 holds as stated, across correlations 0-0.97, fund and ETF rates of 0-100 bp, and 1 to 8 remaining
reviews:
- the residual-variance ceiling;
- the bracket through the ETFs' cost bands;
- the three last-review regimes;
- the outer parallelotope and its Sigma-diameter;
- the frictionless reduction.

**Limits.**
- Fixed Sigma and a finite lattice law.
- No bounds and no marking.
- The ETF grid is coarse at correlation 0.97, where the effective resolution is reported.


## Review

**Red, 2026-09-29.** Reproduced. Red wrote its own exact two-instrument DP, `experiments/036/red_reproduce.py` (6 s on 6 processes), without reading run.py, report.py or fastdp.py:
- deviation coordinates, with the four-point target step as an index shift;
- two exact directional L1 transforms, one per axis;
- the fund's band read by comparing U = T_E[W] with T_A[T_E[W]], and the no-trade set by comparing W with the full transform;
- per-axis steps dividing the target steps, capped at 1,500 points per axis, as in Deviation 2;
- a separate one-instrument DP for part 3.

Red read report.py and run.py only afterwards, to locate a difference in the regime counts. It covers the same 216 cells and 8 reviews.

- **Coverage.** 64,237 contiguous fund bands away from the grid edges. 656 non-contiguous bands are set aside. 99 more are set aside where the ETF optimizer sits at the grid's edge, which acts as a binding ETF bound, outside 1c-1d's hypotheses; all 99 are in the correlation-0.97 cells with the capped ETF axis.
- **1b.** No width exceeds the ceiling beyond the fund-edge resolution h_A + |Sigma_AE| gamma h_E / c^res. The largest width/ceiling is 1.020, within that resolution.
- **1c.** No edge falls outside the bracket. Red used the beta = 1 bracket at every review, which is looser at t = T-1 than the report's beta = 0.
- **1d.**
  - Where the ETF trades at an edge, the edge equals 1d's formula within 0.83 resolutions (8,847 edges).
  - Widths by regime (red's counts; each within 0.83 resolutions of its formula): opposite 1,005 at the ceiling minus |rho|(kappa^+_E + kappa^-_E)/c^res; idle at both edges 1,368 at the fund-alone width; same slope 2,784 at the ceiling; mixed 1,269.
  - No last-review width lies outside [fund-alone, ceiling] beyond two resolutions.
  - Before excluding the ETF-at-grid-edge bands, the asymmetric correlation-0.97 cell missed by up to 22 resolutions. Its ETF optimizer was at the grid's edge. That is the same cell the report flags, and it is a grid-extent effect, not the claim.
- **2.** No no-trade grid point lies outside the widened parallelotope, and the Sigma-diameter inequality holds on 20,000 sampled pairs per (cell, review).
- **3.** With kappa_E = 0, the fund's band equals the reduced one-instrument DP's band to one fund step (384 pairs), and it does not move with the ETF incumbent (range 0).
- **Open item** (median width/ceiling at t = 0, T = 8, ETF 10 bp). Red's table matches the report to 0.01 in every entry (0.51 against 0.50 in one):

| risk corr | fund rate | step | r = -0.8 | r = 0 | r = +0.8 |
|---|---|---|---|---|---|
| 0.97 | 10 bp | 0.5 | 0.51 | 0.52 | 0.52 |
| 0.97 | 10 bp | 0.1 | 0.27 | 0.27 | 0.28 |
| 0.97 | 50 bp | 0.5 | 0.66 | 0.67 | 0.67 |
| 0.5 | 10 bp | 0.5 | 0.63 | 0.68 | 0.75 |
| 0.5 | 10 bp | 0.1 | 0.28 | 0.30 | 0.32 |
| 0.5 | 50 bp | 0.5 | 0.65 | 0.67 | 0.68 |

  The widening with r at risk correlation 0.5, and its absence at 0.97, reproduce.

**Deviations are honest.**
- *1.* Claim 107 is on main, and the order is recorded.
- *2.*
  - Running in deviation coordinates is exact under fixed Sigma, beta = 1, no marking and no binding bound.
  - Reading T in {1, 4, 8} off one T = 8 run is exact by time-homogeneity with V_T = 0.
  - The per-axis cap and its effective resolution are stated.
  - The frictionless ETF uses the 10 bp width.
  - The convex cross-check was reduced (6 cells x 10 incumbents), and the reduction is stated. Red did not redo the convex check.

**Nit (counts, not claims).** The report's last-review regime counts (3,714 opposite, 2,556 idle, 2,100 mixed, 6 same slope) depend on two choices it does not state:
- at t = T-1, run.py samples the 41 ETF incumbents across the *static* parallelotope (b = 0), not the widened one Deviation 2 describes. So few incumbents sit far enough outside the ETF band for "same slope";
- "opposite" counts both orders of the two edges' directions, and the frictionless cells are included.
Please state the last-review incumbent range in Deviation 2. No check is affected.

Verdict: reproduced

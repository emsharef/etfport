---
id: 48
title: "D18: the dynamic, myopic and exposure-first policies compared on one problem (M8, finite-law variant), over a registered 72-cell grid of starting holdings, cash, prior uncertainty, fund-to-ETF cost ratio and regime"
status: reproduced
model_version: M8
direction: D18
claims: [44, 104, 109, 110, 111]
code: experiments/048/
---
## Question
**Job: measure behaviour** (proposal section 6): which policy does what, and what the simpler policies lose, at the
tested inputs. It illustrates the tested cases only (AGENTS.md rule 22); the where-and-why is read in the inputs, and
no general conclusion is drawn.

Routing:
- **Source:** PM's note 2026-09-29-d18-register (ROADMAP D18; LAB_REQUEST.md item 2).
- **Decisions.** PM's decisions, math's answers to the analyst's D18 questions, and mathb's M8 note are recorded in
  experiments/d16-harness/D18-PLAN.md.
- **Model.** M8 in model/SPEC.md (merged 2026-09-29), finite-law variant.
- **Grid.** 72 cells, and the grid is the whole run: no sweeps beyond it.
- **Kill criterion (mathematical only).** A policy cannot be defined consistently on the common problem. If so, the
  report records which one and why.

- **Every input is an assumption.**

On one problem, with identical information, objective and feasible trades, how do three policies differ in actions
and in expected objective?
- the dynamic policy (the two-review optimum);
- the myopic policy (claim 110's one-review optimum at each review);
- exposure-first (claim 111's incumbent-aware two-stage split at each review).

Where do the simpler policies work well, and where do they not? Claim 044's test (experiment 047) is used to explain
each myopic gap.

## Design
### Model: M8, finite-law variant
- **Instruments.** One fund and one ETF, b_A = b_E = 1, one factor, reviews t = 0 and 1, gamma = 5, beta = 1, no ETF
  fee (c^E = 0), no ETF residual (sigma_E = 0), fund cap 0.25, no ETF cap.
  - With sigma_E = 0 the ETF's return reveals the factor return. The harness, which observes the two instruments'
    returns, then has M8's information y = (f, r^A, r^E).
  - Its matrix filter equals M8's scalar filter on the tree: beliefs to 3e-18, P_t to 1e-20, Sigma_t exactly. This
    was checked before registration on an M8 instance, as a solver check.
- **Finite laws** (M8's reference choice for the parameters):
  - theta takes two points per block, m_0 +- sqrt(P_0), so four equiprobable atoms;
  - each shock takes two points, +-sigma (f and z^A), so four equiprobable atoms;
  - so there are 16 states tomorrow. Every gross return is positive on the support.
- **Regimes.** experiments/presets.py mapped to one fund and one ETF: the market factor only (premium 1.5%,
  premium SD 0.5%, factor SD 8%), with alpha mean, alpha SD, residual SD 2%, fund and ETF rates as in each preset.
  - equity-style: alpha -0.19%, fund 50 bp, ETF 2 bp;
  - fixed-income-style: alpha +0.20%, fund 20 bp, ETF 50 bp.
  - The mapping drops the fixed-income preset's second factor. With one factor the ETF spans it.

### The grid (72 cells)
| input | levels |
|---|---|
| starting holdings (presets' STARTS) | all-ETF (0, 0.9), all-fund (0.15, 0), mixed (0.075, 0.45) |
| cash h^-_0 | slack (1.0, the presets' cash) or tight (0.005) |
| prior uncertainty | the preset's prior SDs (premium 0.5%, alpha 0.35%) times 1 or 3 |
| fund-to-ETF cost ratio | the preset's fund rate times 0.2, 1 or 5, with the ETF rate fixed (equity-style ratios 5, 25, 125; fixed-income-style 0.08, 0.4, 2) |
| regime | equity-style, fixed-income-style |

- **Cash that does not bind.** A tight level binds only where the policy buys. From the all-ETF and mixed starts the
  ETF starts above its target and is sold, so tight cash may not bind there (found when building D16's instances).
  The report states in which cells the budget binds, under each policy, rather than assuming it.

### The three policies (the same information, objective and feasible set)
- **Dynamic.** The harness's exact two-review program over the tree (experiments/d16-harness, validated;
  experiment 047).
- **Myopic.** Claim 110's one-review problem at the root, then at each state tomorrow from the marked holdings and
  the remaining cash, with the filter's beliefs.
- **Exposure-first,** at each review with the filter's beliefs:
  - Stage 1 is claim 111's incumbent-aware problem: the one-review objective with the fund frozen at its incumbent,
    and the ETF's rates, the zero bound and the budget on.
  - Stage 2 is claim 104's: the one-review objective over the fibre p + (b_A/b_E) a = w_1, with every friction and
    the budget.
  - **Beside it,** where fundable: claim 041's one-sided frictionless stage 1 (max G_E over w >= r a with a in the box)
    with the same stage 2. Where its fibre is unfundable (no holding on the fibre meets the budget), the share of cells
    and states is reported.

### Measurements, per cell
- **Actions:** each policy's root holdings (fund, ETF), and its expected holdings tomorrow.
- **Value and losses:** each policy's expected objective on the tree, and the losses of the myopic and exposure-first
  policies against the dynamic one, in basis points of the objective.
- **Claim 044's quantities,** for the myopic policy (math's per-cell items):
  - the cash prices eta_0 and eta_1 by state;
  - the incumbent values S_A and S_E;
  - the residuals S_i - beta E[eta_1](1 + kappa^+_i);
  - claim 044 part 3(c)'s existence test (experiment 047's LP) against the observed myopic loss.
- **Where the budget binds,** under each policy.

**"Works well"** is defined before the run: a loss below 0.01 bp of the objective, against the dynamic policy. The
cells where each simpler policy works well are listed, and read against the inputs.

**What would count against the design** (the kill criterion): a policy undefined at some cell. Examples are an
exposure-first stage with no feasible point, or an inconsistent information set. Such a cell is recorded as such,
not repaired.

**Precision.** The solvers are exact convex programs (CLARABEL), with objective agreement to about 1e-10. Loss
differences below 1e-8 are read as zero.

**Output.**
- **Committed:** experiments/048/run.py, report.py and summary.json. Two figures: loss against the cost ratio per
  regime and start, and root holdings per policy.
- **Notes:** the result goes to PM, math, mathb and red.

## Deviations
1. **Carried cash and solver retries** (recorded before reporting).
   - **Cash.** Carried cash of -1.8e-14 (rounding) is clamped at zero.
   - **Retries.** A CLARABEL failure is retried once with default settings, and any remaining failure is counted.
     None remains.
2. **One-point fibre** (recorded before reporting). One exposure-first step failed: equity-style, all-fund start,
   tight cash, prior x3, fund rate x0.2, one state tomorrow.
   - **Why the fallback is exact.** There, with no cash and positive rates, every move along the fibre sells one
     instrument to buy the other at a net cash cost, so stage 1's point is the fibre's only feasible point. CLARABEL
     fails on that one-point set, and OSQP returns the point.
   - **Rule.** The step takes stage 1's point, only under those conditions (zero cash, positive rates, a solver
     failure). It was used once.
3. **Myopic optimality read on holdings** (recorded before reporting).
   - **Why.** In 22 equity-style cells the dynamic and myopic root decisions differ by 5e-4 in the ETF, and the
     myopic loss is 4e-5 bp: genuine, but far below the 0.01 bp "works well" line. A loss threshold therefore cannot
     define "optimal".
   - **Rule.** As in experiment 047, "myopic optimal" means root and expected tomorrow holdings within 1e-5 of the
     dynamic policy's, and claim 044's test is compared with that. "Works well" keeps the registered 0.01 bp loss
     definition.
4. **Exposure-first undefined, recorded, not repaired** (as registered). In 4 cells (fixed-income-style, all-fund
   start, slack cash, fund rate x0.2 or x1, both priors), marking carries the fund above its 0.25 cap in 8 of the 16
   states tomorrow.
   - **Why it is undefined.** M6 caps only post-trade holdings, but claim 111's stage 1 freezes the fund at its
     incumbent, which is then infeasible. The exposure-first policy is not defined at those states. This is D18's
     kill criterion in part: one policy cannot be defined consistently on those states of the common problem.
   - **A possible fix, not applied.** Freeze the fund at min(a^-, bar a). That is PM's and mathb's to decide.
5. **PM's cap fix, after reporting** (PM's note 2026-09-29-exp048-cap-fix).
   - **The decision.** At states where marking carries the fund above its cap, claim 111's first stage freezes the
     fund at its incumbent clipped to the box, min(a^-, bar a). The forced sale to the cap is a trade, charged its
     cost and cash, and the dynamic and myopic policies make the same forced sale.
   - **The rerun.** The whole grid was rerun with this definition (`summary.json`). The reported run is kept as
     `summary_as_reported.json`. Only the 4 cells of Deviation 4 change, all in exposure-first; every other policy and
     cell is identical to 1e-9.
   - **The result in those cells.** Exposure-first is defined there and loses 1.93-2.16 bp (after Deviation 6's
     correction; first reported as 1.98-2.21), against the myopic
     policy's 1.78-1.95 bp in the same cells.
   - **What stands.** The undefined result of Deviation 4 stands as reported for the original definition. The tables
     below show both.
6. **Deviation 5's stage-2 exposure, corrected after red's reproduction** (red's note 2026-09-29-exp048-capfix-gap).
   - **The error.** In Deviation 5's implementation, stage 1 froze the fund at min(a^-, bar a) and charged the forced
     sale's cost and cash, as PM decided. But the fibre exposure passed to stage 2 was built from the unclipped
     marked incumbent, w_1 = p_1 + (b_A/b_E) a^-, not from stage 1's frozen holding. That is an implementation
     error, not a design choice.
   - **The fix.** w_1 now uses the frozen holding, p_1 + (b_A/b_E) min(a^-, bar a).
   - **The rerun.** Only the 8 over-cap states of the same 4 cells change. The losses become 2.125, 2.079, 2.156 and
     1.929 bp (from 2.174, 2.128, 2.208 and 1.981), and tomorrow's mean ETF holding becomes 0.064 in the first cells
     (from 0.076). This reproduces red's numbers exactly.
   - **What stands.** Every other cell is unchanged, and so is the reading: exposure-first loses slightly more than
     myopic there (1.78-1.95 bp).

## Results
**Commands:** `uv run python experiments/048/run.py` (7 s on 8 processes; with Deviation 5's cap fix since its rerun), then
`uv run python experiments/048/report.py`, which also writes `fig_losses.png`.
- **Assumptions.** Every input is an assumption (rule 22).
- **Model.** M8's finite-law variant at main 1e37529.
- **Coverage.** 72 cells, every one solved (after Deviations 1-2).
- **Units.** Losses are in basis points of the two-review objective, against the dynamic policy.

**Where the simpler policies work well** (loss below 0.01 bp):
| policy | defined | works well | median loss | largest loss |
|---|---|---|---|---|
| myopic | 72 | 54 | 0.0000 bp | 2.34 bp |
| exposure-first (claim 111's stage) | 68 (4 undefined, Deviation 4); 72 with PM's cap fix (Deviation 5) | 41 (41 with the fix) | 0.003 bp (0.003 with the fix) | 5.63 bp |
| claim 041's stage (beside it) | 60 (12 unfundable at the root) | 3 | 0.82 bp | 4.17 bp |

| regime | start (fund, ETF) | cash | myopic: max loss (bp), works well | exposure-first: max loss, works well, undefined | claim 041's stage: max loss, works well, unfundable | budget binds (dynamic) | myopic optimal |
|---|---|---|---|---|---|---|---|
| equity-style | (0, 0.9) | tight | 0.000, 6/6 | 0.003, 6/6 | 0.013, 1/6 | 0/6 | 0/6 |
| equity-style | (0, 0.9) | slack | 0.000, 6/6 | 0.003, 6/6 | 0.013, 1/6 | 0/6 | 0/6 |
| equity-style | (0.075, 0.45) | tight | 0.000, 6/6 | 0.029, 4/6 | 0.016, 0/6 | 0/6 | 1/6 |
| equity-style | (0.075, 0.45) | slack | 0.000, 6/6 | 0.029, 4/6 | 0.016, 0/6 | 0/6 | 1/6 |
| equity-style | (0.15, 0) | tight | 0.000, 6/6 | 5.625, 3/6 | -, 0/6, 6 | 6/6 | 6/6 |
| equity-style | (0.15, 0) | slack | 0.001, 6/6 | 0.004, 6/6 | 0.015, 1/6 | 0/6 | 0/6 |
| fixed-income-style | (0, 0.9) | tight | 2.341, 0/6 | 2.356, 0/6 | 3.543, 0/6 | 0/6 | 0/6 |
| fixed-income-style | (0, 0.9) | slack | 2.341, 0/6 | 2.356, 0/6 | 3.543, 0/6 | 0/6 | 0/6 |
| fixed-income-style | (0.075, 0.45) | tight | 0.000, 6/6 | 1.298, 3/6 | 3.926, 0/6 | 3/6 | 5/6 |
| fixed-income-style | (0.075, 0.45) | slack | 0.000, 6/6 | 1.614, 3/6 | 4.174, 0/6 | 0/6 | 5/6 |
| fixed-income-style | (0.15, 0) | tight | 0.000, 6/6 | 0.003, 6/6 | -, 0/6, 6 | 6/6 | 6/6 |
| fixed-income-style | (0.15, 0) | slack | 1.954, 0/6 | 1.806, 0/6, 4 undefined; with the cap fix 2.156, 0/6 (Deviation 6) | 3.796, 0/6 | 0/6 | 0/6 |

**Readings in the inputs** (these illustrate the tested cells; rule 22):
- **Myopic, where it works well.** In every equity-style cell (cheap ETF, 2 bp) and wherever the budget binds, the
  largest myopic loss is 0.001 bp. With tight cash from the all-fund start, both policies spend the cash on the
  same trade, and myopic is exactly optimal (12 of 12). So at these presets the binding budget adds no myopic loss:
  claim 044's cash-price channel is present (eta_0 > 0) but moves both policies alike.
- **Myopic, where it loses.** It loses only in fixed-income-style cells with a costly ETF (50 bp), from the all-ETF
  start (any cash) and the all-fund start (slack cash): 1.4 to 2.3 bp.
  - The dynamic policy holds less of the ETF from the all-ETF start (0.51-0.54 against 0.60-0.62) and more from the
    all-fund start (0.14 against 0.06), anticipating tomorrow's ETF trade.
  - Tomorrow's cash price is zero there (E eta_1 below 1e-13), so the loss is the trading costs' continuation
    (claims 029 and 036's channel), not the budget's.
  - The residual's sign matches the direction: residual_E is -0.0046 where the dynamic policy holds less, and +0.004
    to +0.005 where it holds more.
  - The fund's rate, varied fivefold either way, moves this loss little (1.4-2.3 bp): the ETF's rate drives it.
- **Claim 044's test** agrees with myopic optimality at 72 of 72 cells: 24 optimal, 48 not, of which 22 differ by
  under 1e-4 bp.
- **Exposure-first (claim 111's stage)** tracks the myopic policy where that works, with four exceptions:
  - equity-style, all-fund start, tight cash: 3 of 6 cells lose up to 5.6 bp, because freezing the fund when cash is
    short fixes an exposure the joint rule would reach by selling fund;
  - fixed-income-style, mixed start: up to 1.6 bp;
  - the 4 cells undefined under the original definition (Deviation 4), where with PM's cap fix it loses 1.93-2.16
    bp, slightly more than myopic (Deviation 5);
  - where myopic loses, it loses about as much.
- **Claim 041's stage** almost never works well (3 of 60 defined cells). It is unfundable at the root in all 12
  all-fund tight-cash cells: its frictionless target ignores the budget, as in experiment 044.

**Limits.**
- One fund, one ETF, one factor, two reviews, two-point shocks.
- The presets mapped to one factor drop the fixed-income preset's missing factor.
- Every input is assumed; the 72 cells are the whole run.

## Review

**Red, 2026-09-29.** Reproduced. Red wrote its own policies from the Design, without reading run.py, report.py or the d16 harness: `experiments/048/red_reproduce.py`, 11 s. Run it as `uv run python experiments/048/red_reproduce.py experiments/047`; it imports red's experiment 047 solver.
- **Model.** M8's finite law as registered: b = 1, gamma = 5, beta = 1, c^E = 0, sigma_E = 0, fund cap 0.25, 16 states tomorrow, the presets mapped to one factor.
- **Policies.**
  - Dynamic: the lifted joint program.
  - Myopic: claim 110's one-review program at each review.
  - Exposure-first: claim 111's stage 1 with the fund frozen at min(a^-, bar a) (PM's cap fix), then claim 104's fibre stage 2, at each review.
- **Also.** Claim 044's test is experiment 047's LP. Claim 041's side stage is not reproduced.

**Headline numbers:** every one matches the report.

| Figure | Red and the report |
|---|---|
| Myopic works well | 54 of 72 |
| Myopic median / largest loss | 0.0000 / 2.34 bp |
| Exposure-first (cap fix) works well | 41 of 72 |
| Exposure-first median / largest loss | 0.003 / 5.63 bp |
| Claim 044's test | agrees at 72 of 72 (24 myopic optimal) |
| Budget binds under the dynamic policy | 15 cells |

- Every row of the per-cell table matches: the largest losses, the works-well counts, the binding counts and the myopic-optimal counts. The one exception is the fixed-income-style all-fund slack row's exposure-first figure (below).
- Myopic losses match the report cell by cell to 1e-3 bp.
- The myopic losses' anatomy reproduces. From the all-ETF fixed-income start, the dynamic policy holds 0.51-0.54 of the ETF against myopic's 0.60-0.62, with E[eta_1] below 1e-15: the costs' continuation, not the budget.

**The four deviations:**
1. **Cash clamp and retries.** Harmless. Red's run needs the same clamp (rounding-level negative carried cash).
2. **One-point fibre.** Red's CLARABEL solved every stage 2 (0 fallbacks), and the affected row (equity-style, all-fund, tight: 5.625 bp, 3 of 6) matches the report exactly. So the fallback's point is the fibre's solution, as the deviation argues.
3. **Myopic optimality on holdings.** Honest. With the 1e-5 holdings rule, red finds the same 24 optimal cells and 72 of 72 agreement with claim 044's test.
4. **Exposure-first undefined, then PM's cap fix.**
   - Under the original freeze, red finds the same 4 undefined cells, with the fund marked above its cap in 8 of 16 states. The fund-rate x5 cells have no over-cap state.
   - With the fix, red's losses in those 4 cells are 2.125, 2.079, 2.156 and 1.929 bp. The report's are 2.174, 2.128, 2.208 and 1.981 bp, so red's are lower by 0.049-0.052 bp in each.
   - The root holdings agree (0.25, 0.0613), and so does tomorrow's mean fund holding. Red's policy holds less ETF tomorrow (mean 0.064 against 0.076), all in the over-cap states. There red's stage 1 freezes the fund at 0.25, sells the excess, and moves the ETF from 0.0668 to 0.0704.
   - Red also tried stage 1's exposure from the unclipped marked incumbent. It does not reproduce the report either (2.160 bp in the first cell).
   - The reading stands: exposure-first loses slightly more than myopic in each of the 4 cells (1.93-2.16 against 1.78-1.95). But Deviation 5's range should be checked. Please state exactly how stage 1 treats the forced sale, and reconcile the 0.05 bp.

**Not re-run:** claim 041's side stage (3 of 60, 12 unfundable) and the figures.

Verdict: reproduced

**Red, 2026-09-29, the cap-fix gap closed.** The analyst traced the 0.05 bp gap to an implementation error (Deviation 6): stage 2's fibre was built from the unclipped marked incumbent instead of stage 1's frozen holding. Deviation 6's rerun gives red's 2.125, 2.079, 2.156 and 1.929 bp and red's ETF mean of 0.064, and nothing else changes. The reproduction is now complete, with no open discrepancy.

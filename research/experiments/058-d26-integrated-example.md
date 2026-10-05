---
id: 58
title: "D26: an integrated allocation example on M9 (three funds, two ETFs, two factors) comparing repeated one-review, the plan without tomorrow's funding constraint and the funded two-review optimum; actual losses against claims 049's and 115's bound terms on a registered sensitivity design; the larger menu's computation; and what a manager must compute"
status: reproduced
model_version: M9
direction: D26
claims: [48, 49, 114, 115]
code: experiments/058/
---
## Question
**Job: measure behaviour** (proposal section 6). There is one integrated numerical study and no new theorem
(LAB_REQUEST_3.md; ROADMAP D26). It illustrates the registered cases only (rule 22). Every input is assumed.

Routing:
- **Source:** PM's note 2026-10-01-d26-start.
- **Definitions:** math's and mathb's notes of 2026-10-01 (claims 048-049, 114-115, all on main).
- **Preparation:** experiments/d26-prep on data/d26-prep, with no findings.

The questions (LAB_REQUEST_3 section 2), asked of the registered cases:
- **Q1.** When does the bound establish that repeated one-review optimization has a small loss?
- **Q2.** When does planning ahead materially change the allocation or the objective?
- **Q3.** When does ignoring tomorrow's funding constraint (policy 2) perform poorly?
- **Q4.** When is the bound too conservative to distinguish useful policies?
- **Q5.** Where does the coverage test fail although the actual funding constraint or the policy loss is negligible?

## Design
### Model, information and law
- **M9** (model/SPEC.md) on experiments/d16-harness/harness_n.py, validated in validate_n.py, validate_m9.py and
  validate_d26.py.
- **Observation:** the manager observes y = (f, r^A, r^E).
- **Filter:** M9's Kalman recursion, which is the best linear estimate under the finite law and not the exact
  posterior.
- **Kept distinct:** realized-return risk (Sigma_r), uncertainty about the conditional means (P_t), and the state's
  evolution (Phi, Q, theta_bar).
- **Reviews:** at t = 0 and 1, with marking at 2.
- **Law: the axis law** (harness_n.axis_law: 2d atoms of +- sqrt(d) sd per block, the stated means and covariances).
  It gives 2(K+N) parameter atoms times 2(K+N+M) shock atoms, so 140 states for the example. The product law (two
  points per coordinate, 4,096 states) is used for the worked example only, as a check of the law's effect.
- **Positive gross returns** are checked on every tree.

### The example (experiments/d26-prep/spec.py; every number assumed)
- **Instruments:** two factors; ETFs E1 (1.0, 0.0) and E2 (0.3, 1.0), with fees (3, 5) bp per quarter and tracking
  SDs (0.2%, 0.3%); funds F1 (1.0, 0.2), F2 (0.8, 0.6), F3 (0.5, 1.0), with residual SDs (2%, 2.5%, 3%).
- **Alpha means:** the regime preset's alpha_mean + (0, +0.002, -0.001). The alpha prior SD is the preset's.
- **Rates:** the regime preset's. Funds take fund_rate x (1, 1.5, 0.75) and ETFs etf_rate x (1, 1.5), on both sides.
- **Limits:** fund caps 0.25, uncapped ETFs, no shorting, gamma = 5, beta = 1.
- **The funded budget** applies at both reviews.
- **Scope:** Sigma_0 and Sigma_1 are entrywise nonnegative (checked per case), which the funding bounds need. Claim
  048's part 2 does not apply, because the ETFs carry fees and residuals; only its parts 1 and 4 are used.

### Policies and evaluation (math's definitions)
- **Policy 1, repeated one-review:** x^my_0 is today's one-review optimum; tomorrow, the funded one-review optimum
  in every state.
- **Policy 2, the plan without tomorrow's funding constraint:** x^s_0 is the root of the two-review program with
  every tomorrow budget deleted (today's budget kept). Tomorrow, the funded one-review optimum from g o x^s_0 and the
  carried cash, with no free financing.
- **Policy 3, the funded two-review optimum:** V^dyn.
- **Value:** J(x_0) = today's score net of costs + beta E[tomorrow's funded optimum].
- **Loss:** V^dyn - J(x_0), in bp of initial wealth W_0 = h^-_0 + sum_i x^-_{0,i} (holdings at par). Transaction
  expenditure is reported in bp of W_0 at both dates; it is already deducted in the objective.

### Bound terms (reported separately, as terms of upper bounds, never as a decomposition of the loss)
- **At x^my_0:**
  - claim 049's band term, (1/2) S'(gamma Sigma_0)^{-1} S minimized over the admissible incumbent-value box at the
    relaxed tomorrow;
  - its input-only form;
  - claim 115's band term, (1/2) rho' (gamma Sigma_0)^{-1} rho, from the QP.
- **At x^s_0:** claim 115's band term, which should be zero; it is reported as a check.
- **The tail term** beta E[eta_bar D] at each of x^my_0 and x^s_0.
- **Coverage at each root:** the uncovered fraction eps = P(D > 0), PP, Delta, VaR_{1-eps}(Delta) and the test's
  pass or fail at eps in {0, 0.05, 0.10}.

### The sensitivity design (78 in-scope cases + 6 out-of-scope + the worked example's law check + the larger menu)
- **Regimes (2):** equity-style and fixed-income-style.
- **Starts (3):**
  - construction from cash: x^- = 0, h^- = 1.0;
  - rebalancing: x^- = (0.10, 0.10, 0.05, 0.40, 0.20), h^- = 0.15;
  - tight rebalancing: the same holdings, h^- = 0.02.
- **Settings (13), one at a time from the base** (no predictable move, the preset's uncertainty, Q = 0, the preset's
  rates):

| setting | what varies |
|---|---|
| base | none |
| pred_alpha +0.004, -0.004 | theta_bar_alpha = m_0,alpha +- 0.004, phi_alpha = 0.5 (a predictable alpha rise or fall) |
| pred_lambda +0.005, -0.005 | theta_bar_lambda1 = lambda_1 +- 0.005, phi_lambda = 0.7 (a predictable premium move) |
| unc x0.25, x4 | the alpha prior variance (the revision uncertainty), no predictable move |
| pred_alpha +0.004 with unc x4 | the two together, to separate them |
| pred_alpha +0.008 | a predictable rise near or beyond the innovation's support (claim 115 part 3's corner) |
| q_alpha 1e-6 | state noise only |
| fund rates x2; ETF rates x4; ETF rates x0.25 | the relative costs within the regime |

- **Out of scope (6):** the base with fund 3 loading -0.6 on factor 2, so the covariances are negative (2 regimes x 3
  starts). They are labelled outside the funding bound; losses are reported, bounds marked out of scope.
- **The worked example:** the fixed-income-style regime, rebalancing start, pred_alpha +0.004. It is reported in
  full (today's holdings by policy, tomorrow's trades and needs by state). It is also recomputed under the product
  law (4,096 states), as a check of the law.
- **The larger menu:**
  - 30 funds, 4 ETFs, 3 factors (scale.py's menu generator, seed 26), axis law, base settings, construction from cash.
  - It is a computation check: the three policies, the bound terms and the runtimes.
  - If it does not solve within 30 minutes, the largest menu that does in scale.json is used, and the limit is
    reported.
  - The product law's limit is reported from scale.json.

### Readings defined in advance
- **The economic loss tolerance** tau is 1 bp of W_0, with sensitivity at 0.1 and 10 bp.
- **Q1:** the bound (claim 049's band + tail at x^my_0, and claim 115's) is at most tau.
- **Q2:** the dynamic root differs from x^my_0 by more than 0.01 of W_0 in some holding, or the myopic loss exceeds
  tau.
- **Q3:** policy 2's loss exceeds tau, reported with the myopic loss beside it.
- **Q4:** both policies' bounds exceed tau, while at least one policy's actual loss is below tau.
- **Q5:** the test fails at eps = 0 at a policy's root, while that policy's loss is below tau. The dynamic policy's
  tomorrow budget is also reported: slack in every state or not.

### Accuracy and the implementation account
- **Per case:** solver status; the funded policies' cash at every node >= -1e-8; J(dynamic root) - V^dyn; policy 2's
  relaxed tomorrow against per-state unbudgeted solves; claim 115's band term at x^s_0; and the runtime of each
  component (the joint program, the relaxed program, the per-state one-review solves, the band QPs, the coverage
  objects) on the machine stated.
- **Quantities are classed by what they need:**
  - the inputs alone: PP, need, liq, D, eta_bar and eps at a given holding, and claim 049's input-only line;
  - independent one-review solves at tomorrow's states: J, the admissible-slope box, and so claim 049's and 115's
    band terms;
  - a joint program: V^dyn and policy 2's root x^s_0.

  Any input taken from the benchmark is named. The losses need V^dyn; the bounds do not.

**What would count against the design:** a policy or a bound term that cannot be defined on the common model (D26's
kill criterion). It is recorded, not repaired.

**Output.**
- **Committed:** experiments/058/run.py and summary.json; experiments/058/REPORT.md, with the worked example, at most
  three proposed figures (today's allocations; tomorrow's trades and funding needs; losses against the bound terms),
  the implementation account and the larger-menu statement.
- **Notes:** to PM, red (to reproduce), the auditor (bound values against the claims) and the writer (copy-editing
  REPORT.md only).

## Deviations
1. **The need-versus-purchases diagnostic (post hoc, labelled).**
   - **Why.** The coverage test failed in every case.
   - **What was added.** run.py's `diag` part computes, at both roots of every in-scope case, the relaxed tomorrow's
     actual purchases with their rates beside claim 049's need, and the relaxed tomorrow's own shortfall.
   - **Effect.** It explains section 4 of REPORT.md and changes no registered quantity.
2. **Runtimes measured under load.** The design ran in 6 parallel processes, and the worked example and larger menu
   ran while experiments/d26-prep/scale.py was running in the background. The runtimes in REPORT.md section 5 are
   therefore upper indications, not quiet-machine measurements.
3. **The product-law scale limit is pending.** The human asked that the report not wait on the scale test and that
   its results be added when scale.json appears. REPORT.md section 6 said so at the report's merge. The full run's
   results are now added there (scale.json committed): the product law solves to 4 funds (16,384 states) and times
   out at 5; the axis law solves to 40 funds, 4 ETFs and 3 factors (8,084 states, 1.07M variables, 16 minutes) and
   times out at 60 x 5 x 4.
4. **Accuracy note.** Policy 2's relaxed tomorrow agreed with independent per-state unbudgeted solves to 3.9e-5 in
   holdings, not tighter. The worst cases are holdings at a fund cap in a nearly flat direction. At tighter solver
   tolerances the gap is 7e-7, with the root unchanged to six digits. No registered number depends on it at the
   reported precision.

## Results
The full answer is experiments/058/REPORT.md. The tables are in tables.md, and the three proposed figures are
fig_allocations.png, fig_tomorrow.png and fig_losses_bounds.png. All 84 registered cases are reported, with the
worked example under both laws and the larger menu. Every input is assumed (rule 22).

**Headline**, in bp of initial wealth, 78 in-scope cases, tau = 1 bp:
- **Policy 2** (the plan without tomorrow's funding constraint, with funded trades tomorrow) is within 0.007 bp of the
  funded optimum in every case (Q3: 0).
- **Repeated one-review** loses more than 1 bp in 27 cases, up to 18.9 bp, all in the fixed-income-style regime
  when rebalancing (Q2).
  - The loss rises with a predictable alpha rise and falls with a fall or with higher relative costs.
  - The revision uncertainty, varied separately, barely moves it.
  - The mechanism is front-loading the fund purchases tomorrow would make, paid for by selling ETFs. That means
    less ETF, not a larger reserve.
- **The bounds never establish a small loss** (Q1: 0).
  - The coverage test fails at every root in every case, and the tail term is 67-426 bp.
  - Claim 049's need sums the instruments' solo targets, 1.6-2.2 of wealth here. The relaxed tomorrow's actual
    purchases are a median 1.3% of it (Deviation 1).
  - Hence Q4 holds in 78/78, and Q5 in 51 (one-review loss below 1 bp) and 78 (policy 2) of 78. The optimum's tomorrow
    budget is slack in every state in 67 of the 78.
  - Claim 115's band term at the one-review root was at least the actual loss in all 78 cases (median ratio 0.31),
    an observation, not a bound.
- **The worked example** (fixed-income-style, rebalancing, alpha rise): one-review 12.2 bp; the planner buys F2 and F3
  and sells 78% of the broad ETF. The product law (4,096 states) agrees to 0.09 bp.
- **The larger menu** (30 funds, 4 ETFs, 3 factors, 4,884 states, 498k variables) solves in 9 minutes: one-review
  5.4 bp, policy 2 0.000 bp.
- **Out of scope** (6, negative covariances): losses reported, bounds not applicable.

## Review

**Red, 2026-10-01.** Reproduced. Red wrote its own solver from the registration, without reading run.py, report.py, harness_n or experiments/d26-prep: `experiments/058/red_reproduce.py`. Run `worked` for the worked example, 4 s, and `sample` for all 78 in-scope cases, 1 min.
- **Model.** M9 with two factors, three funds and two ETFs with fees and tracking residuals; the axis law (10 parameter atoms x 14 shock atoms = 140 states); policies 1-3 and V^dyn from red's own cvxpy/CLARABEL programs.
- **Bound terms.** Claim 049's band term and claim 115's band term, each minimized over the admissible incumbent-value box at the relaxed tomorrow, as in the corrected claims; the tail term and coverage at both roots.
- **Units.** Losses in bp of W_0 = h^- + sum x^-, which is 0.87 for the tight start, as registered.

**The worked example** (fixed-income-style, rebalancing, pred_alpha +0.004) reproduces exactly.

| | holdings (F1, F2, F3, E1, E2), cash | today's cost / E tomorrow's cost | loss |
|---|---|---|---|
| policy 1 | (0.039, 0.100, 0.050, 0.400, 0.200), 0.211 | 1.2 / 5.0 bp | 12.186 bp |
| policy 2 | (0.100, 0.244, 0.161, 0.089, 0.200), 0.204 | 21.5 / 0.6 bp | 0.000 bp |
| policy 3 | policy 2's holdings | | |

At the one-review root: claim 049's band 119 bp, claim 115's band 53 bp, tail 269 bp, eps = 1, need 1.56-1.89 of W_0. At policy 2's root: claim 115's band 5e-9 bp (zero, as claimed), tail 250 bp, eps = 1.

**The design: all 78 in-scope cases, compared row by row with tables.md.**
- Every one-review loss agrees within 0.04 bp. Policy 2's losses agree within 3e-4 bp, the band terms within 0.5 bp, and the tails within 1.3 bp.
- The only differences above 0.01 bp are in the q_alpha = 1e-6 cells, where red's state-noise reading may differ from the harness's in some detail, and they change no reading.
- The analyst's central claims all hold in red's run:
  - *Policy 2* is within 0.0073 bp of the optimum in all 78 (the report: 0.007).
  - *The coverage test* fails at eps = 0 at both roots in all 78, with eps = 1 at the one-review root in all 78. The need is about 1.6-1.9 of W_0 against actual purchases far smaller, which is Deviation 1's diagnostic. Red checked the need, not the purchase ratio itself.
  - *Claim 115's band term* at the one-review root is at least the one-review loss in 78 of 78 (loss/band median 0.31, maximum 0.79, as reported). At policy 2's root it is at most 6.5e-7 bp.
  - *The ranges* match: one-review losses up to 18.89 bp (fixed-income-style, tight start, pred_alpha +0.008), tails 67-426 bp, and the regime-and-start ranges of Q2.
- Red's first run normalized by 1 rather than W_0 = 0.87 for the tight start, and set phi_lambda on the first premium only. M9's Phi is per block, so phi_lambda applies to both. With both fixed the table agrees as above. The report's definitions were right in both cases.

**Not re-run:** the six out-of-scope cases, the product-law check (4,096 states), the larger menu and its runtimes, Deviation 1's purchase ratios, and Q1-Q5's counts. Q1-Q5 follow from the reproduced losses, bounds and coverage.

**Deviations** are honest.
- *Deviation 1* is labelled post hoc and changes no registered quantity.
- *Deviation 2's* runtimes are stated as upper indications.
- *Deviation 3's* pending scale limit is stated.
- *Deviation 4's* 3.9e-5 accuracy note is consistent with red's run: policy 2's loss agrees to 3e-4 bp.

**One reading point, for the writer, not a correction:** "Claim 115's band term at the one-review root was at least the actual loss in every case" is an observation on these cases. The band term alone is not a proven bound; claim 115's bound is band plus tail. The report already says so (Q1).

Verdict: reproduced

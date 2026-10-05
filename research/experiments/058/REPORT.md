# D26: an integrated allocation example, and whether the bounds are informative

Experiment 058 (registered in experiments/058-d26-integrated-example.md; LAB_REQUEST_3). Every number below is an
**assumed input or a result at assumed inputs** (rule 22). It illustrates the registered cases and is not empirical
performance.
- **Units.** Losses and transaction expenditure are in **bp of initial wealth** W_0 (cash plus holdings at par), at
  both dates under the same objective. Transaction expenditure is already deducted in the objective.
- **Losses** are differences in the two-review mean-variance objective. They are not realized returns.
- **Sources.** Full tables are in tables.md; machine-readable results in summary_design.json, summary_worked.json,
  summary_larger.json and summary_diag.json.

## 1. The model and the three policies
- **The model.** M9 (model/SPEC.md): two factors with premia that can move between reviews (Phi, Q, theta_bar), three
  funds with distinct factor footprints and uncertain alphas, two ETFs with fees and small tracking residuals, and
  cash. Purchase and sale rates come from the equity-style or fixed-income-style preset. Funds are capped at 0.25,
  there is no shorting, and the funded budget applies at both reviews. Holdings are marked by gross returns between
  the reviews.
- **What is kept distinct:**
  - realized-return risk (the shocks);
  - uncertainty about conditional means (the filter's P_t);
  - the evolution of the means themselves (Phi, Q).
- **What the manager observes.** Every factor and instrument return, y = (f, r^A, r^E). M9's Kalman filter updates the
  beliefs. Under the finite scenario law used here it is the best linear estimate, not the exact posterior.
- **The scenario law.** A finite law with the model's means and covariances on 140 tomorrow-states (the "axis" law,
  with 2d atoms for a block of dimension d). The worked example is repeated on the 4,096-state product law: losses agree to 0.09 bp and
  holdings to 0.011.
- **The three policies, under one objective and one information set:**
  1. **Repeated one-review:** optimize today ignoring tomorrow, then optimize again at each state tomorrow.
  2. **The plan without tomorrow's funding constraint:** today's holding from the two-review problem with tomorrow's
     budgets dropped (today's kept). It is evaluated with **funded** optimal trades tomorrow; it gets no free
     financing.
  3. **The full funded two-review optimum** (the benchmark).
- **Roots.** A policy's *root* is the holding it chooses today.

## 2. The worked example
The fixed-income-style regime, rebalancing an existing portfolio, with a predictable rise in every fund's alpha
(theta_bar_alpha = m_0 + 0.004, phi_alpha = 0.5). Inputs are assumed (spec.py).

| holding (fraction of W_0) | F1 | F2 | F3 | E1 | E2 | cash | today's cost | E tomorrow's cost | loss |
|---|---|---|---|---|---|---|---|---|---|
| start | 0.100 | 0.100 | 0.050 | 0.400 | 0.200 | 0.150 | | | |
| 1: repeated one-review | 0.039 | 0.100 | 0.050 | 0.400 | 0.200 | 0.211 | 1.2 bp | 5.0 bp | 12.2 bp |
| 2: plan without tomorrow's budget | 0.100 | 0.244 | 0.161 | 0.089 | 0.200 | 0.204 | 21.5 bp | 0.6 bp | 0.000 bp |
| 3: funded two-review optimum | 0.100 | 0.244 | 0.161 | 0.089 | 0.200 | 0.204 | 21.5 bp | 0.6 bp | (benchmark) |

**Today.**
- The one-review manager sells a little of F1 and otherwise stays inside its no-trade bands.
- The planning manager buys F2 and F3 toward their caps, paying with **a sale of three quarters of the broad ETF**.
  It anticipates both the predictable alpha rise and the fund purchases that tomorrow's revisions would call for.
- Anticipation here means **less** ETF and about the same cash, not a larger ETF or cash reserve.
- It pays 21.5 bp of trading cost today to save about 4.3 bp tomorrow, and it gains 12.2 bp in the objective.

**Tomorrow** (fig_tomorrow.png, left).
- From the one-review holding, the manager buys funds in nearly every state (up to 0.25 of W_0), mostly paid for by
  selling the ETFs.
- From the planned holding, tomorrow's trades are small.
- The dynamic budget never binds (0 of 140 states).
- The difference between the policies is the timing of the fund purchases. A funding shortage plays no part.

**Bound terms** (terms of upper bounds, not a decomposition of the loss).
- At the one-review root: claim 049's band term 119 bp, claim 115's 53 bp, and a tail term of 269 bp.
- At policy 2's root: claim 115's band term is 0, as the claim states, and the tail term is 250 bp.
- The coverage test fails in **every** state at both roots (eps = 1; fig_tomorrow.png, right). Claim 049's need is
  1.6-1.9 of W_0 in every state, against a liquid reserve of 0.21 and actual purchases of at most 0.25. Section 4
  explains why.

## 3. The registered sensitivity design (78 in-scope cases, 6 out of scope)
- **Design:** 2 regimes x 3 starts (construction from cash; rebalancing; rebalancing with cash 0.02) x 13 settings.
- **Settings:** a predictable alpha rise or fall, a premium move, the revision uncertainty x0.25 and x4 (separately
  from the predictable move), the two together, a larger rise, state noise, and the fund and ETF rates scaled within
  each regime.
- **Tolerance:** the registered economic loss tolerance is tau = 1 bp, with 0.1 and 10 bp shown.

| reading (in-scope cases) | tau = 0.1 bp | tau = 1 bp | tau = 10 bp |
|---|---|---|---|
| Q1: claim 049's bound at the one-review root <= tau | 0 | 0 | 0 |
| Q1: claim 115's bound at the one-review root <= tau | 0 | 0 | 0 |
| Q2: the optimum's holdings differ from the one-review ones by > 0.01 of W_0 (tau-free) | 76 | 76 | 76 |
| Q2: one-review loss > tau | 57 | 27 | 6 |
| Q3: policy 2's loss > tau | 0 | 0 | 0 |
| Q4: both policies' bounds > tau while a policy's actual loss < tau | 78 | 78 | 78 |
| Q5: the test fails (eps = 0 level) at the one-review root while its loss < tau | 21 | 51 | 72 |
| Q5: the same at policy 2's root | 78 | 78 | 78 |
| Q5: the test fails while the optimum's tomorrow budget is slack in every state (tau-free) | 67 | 67 | 67 |

**Q1. When does the bound establish that repeated one-review optimization has a small loss?**
- **Never in this design.** The tail term is 67-426 bp in every case, because the coverage test fails in every
  state (section 4).
- The band term alone comes far closer to the loss. Claim 115's band term at the one-review root was at least the actual loss in
  every case (loss/band ratio: median 0.31, maximum 0.79), and it was at most 1 bp in 23 cases. That is an
  observation on these cases. The band term alone is not a proven bound.
- Claim 049's band term is looser (ratio median 0.03), and its input-only form (119-8,746 bp) looser still.

**Q2. When does planning ahead materially change the allocation or the objective?**
- **The allocation:** almost always (76 of 78).
- **The objective, by regime and start:**
  - equity-style: at most 0.27 bp from cash and at most 1.9 bp when rebalancing;
  - fixed-income-style: 0.04-1.3 bp from cash and **0.7-18.9 bp when rebalancing**.
- **What moves it**, within fixed-income rebalancing:
  - the predictable alpha move: base 7.1 bp, rise +0.004 12.2 bp, +0.008 16.2 bp, fall 2.5 bp;
  - the relative costs: fund rates x2 2.4 bp; ETF rates x4 0.7 bp; ETF rates x0.25 1.5 bp;
  - the revision uncertainty, separately from the predictable move, barely: x0.25 7.2 bp, x4 6.7 bp;
  - state noise: not at all (7.2 bp).
- **The mechanism:** planning front-loads the fund purchases that tomorrow would make, and pays for them by selling
  ETFs.

**Q3. When does ignoring tomorrow's funding constraint perform poorly?**
- **Never in this design.** Policy 2's loss is at most 0.007 bp in all 78 in-scope cases, and at most 0 in the 6 out
  of scope.
- This holds in the 11 cases where the optimum's tomorrow budget binds in some states (up to 113 of 140). Funded
  optimal trades tomorrow absorb it.
- Read as a statement about these inputs: the funding constraint mattered little here. The timing of trades
  mattered.

**Q4. When is the bound too conservative to distinguish useful policies?**
- **In every case.** Both policies' bounds exceed 10 bp everywhere, because of the tail term.
- The actual values separate them clearly: policy 2 is within 0.007 bp of the optimum, and the one-review policy
  loses up to 18.9 bp.
- A smaller bound gives a stronger guarantee, not a smaller loss. The ranking here comes from the actual values.

**Q5. Where does the coverage test fail although the funding constraint or the policy loss is negligible?**
- **Everywhere.** The test fails at both roots in every case.
- The optimum's tomorrow budget is slack in every state in 67 of the 78. Policy 2's loss is below 0.1 bp in all 78,
  and the one-review loss is below 1 bp in 51.
- A failed sufficient test is not evidence that a reserve is needed, and here none was.

**Out of scope (6 cases).** Fund 3 loading -0.6 on factor 2 gives negative covariances, outside the funding bounds'
scope, so their bound terms are not applicable. The losses look like the in-scope base's: one-review 0.01-8.2 bp,
policy 2 at most 0.

## 4. Why the coverage test fails here (a diagnostic, Deviation 1)
- **What the test counts.** Claim 049's need sums every instrument's **solo target**: the holding it would have if
  held alone, (mu_i - kappa^+_i)^+/(gamma Sigma_ii). In this menu all five instruments load on the market factor, so
  the solo targets add to 1.6-2.2 times wealth, while the joint optimum holds far less of each.
- **What tomorrow actually buys.** Measured against that need, the relaxed tomorrow's actual purchases (with their
  rates) are a **median 1.3%** of it (at most 17.5%) at the one-review root, and 1.0% at policy 2's root.
- **What tomorrow actually lacks.** The relaxed tomorrow runs short of cash in some state in only 9 of 78 cases.
- **The reading.** The test is a valid sufficient condition (claim 049 part 1), but with several correlated
  instruments it is far from necessary. Its tail term then dominates the bound.
- **What would sharpen it.** A need built from the joint relaxed purchases rather than the solo targets would be much
  tighter. That needs tomorrow's solves, and it is not one of the claims' terms. This report does not propose it as a
  result.

## 5. What a manager must compute (measured)
Hardware: Apple M2 Pro (10 cores), 32 GB, macOS. Software: Python 3.13.6, cvxpy 1.9.3, CLARABEL 0.11.1, NumPy 2.5.3.
Solver tolerances: gap 1e-12 absolute and 1e-10 relative, feasibility 1e-10. The runtimes were measured while other
jobs ran on the machine (the design in 6 parallel processes, beside the scale test), so they are upper indications.

| quantity | what it needs | example (140 states) | product law (4,096 states) | larger menu (4,884 states, 34 instruments) |
|---|---|---|---|---|
| the planned purchase PP, the need, the liquid reserve, the shortfall, the cash-price bound eta_bar, the uncovered fraction eps; claim 049's input-only band | the inputs, at a given holding | 0.01 s | 0.2 s | 1.1 s |
| J(x): the value of a holding with funded trades tomorrow | one independent one-review solve per state | part of 2.5 s | part of 99 s | part of 370 s |
| the admissible incumbent-value box (relaxed tomorrow) | one independent unbudgeted solve per state | 0.5 s | 14.6 s | 22 s |
| claim 049's and 115's band terms | one small QP each, given the box | < 0.01 s | < 0.01 s | < 0.01 s |
| policy 2's root x^s_0 | a joint program (tomorrow's budgets dropped) | 0.01 s solver | 0.8 s solver | 46 s solver |
| V^dyn and the optimum (the losses) | the joint funded program | 0.01 s solver | 1.3 s solver | 88 s solver (498k variables) |

- **The bounds need no benchmark quantity.** At the one-review root they need the one-review solve today, the
  relaxed tomorrow's per-state solves (the box) and two small QPs. Only the **losses** need V^dyn.
- **Policy 2's root comes from a joint program,** not from an explicit recipe. Claim 048's separated form does not apply here
  (the ETFs carry fees and residuals), and in any case it characterizes the optimum at its own tomorrow numbers
  rather than giving them.
- **Most wall time is modelling-layer overhead** (cvxpy building the program); solver time is the smaller part.
- **No speed comparison between the policies is claimed.**

**Accuracy.**
- All programs solved to "optimal".
- J at the optimum's root equals V^dyn to 4e-13 (1e-13 for the larger menu).
- The funded policies' cash is >= -8e-12 at every node.
- Claim 115's band term at policy 2's root is at most 8e-8 bp, the claim's zero.
- Policy 2's relaxed tomorrow agrees with independent per-state unbudgeted solves to 3.9e-5 in holdings. The worst
  cases are holdings at a fund cap in a nearly flat direction: 7e-7 at tighter tolerances, with the root unchanged
  to six digits.

## 6. The larger menu: what it establishes and what it does not
- **The run:** 30 funds, 4 ETFs and 3 factors (menu generator seed 26), the axis law, 4,884 tomorrow-states and 498k
  variables in the joint program. All three policies and all bound terms were computed in 9 minutes: 88 s for the
  dynamic program and 46 s for policy 2's.
- **Its results:** the one-review loss is 5.4 bp; policy 2's is 0.000 bp. The tail term is 4,416 bp (the need sums
  34 solo targets), and the band terms are 89 bp (claim 115) and 208 bp (claim 049).
- **What it establishes.** The lab's exact scenario-tree program, with a finite law that grows linearly in the menu
  (the axis law), solves a charter-scale menu (tens of funds, several ETFs) to solver precision on a laptop. The
  policies and bound terms are computable there, and the diagnostics of sections 3-4 repeat.
- **The measured limit** (experiments/d26-prep/scale.py and scale.json; 30 minutes per case, one process per case,
  same machine, measured while other jobs ran):

| law | menu (funds x ETFs x factors) | tomorrow-states | variables | result | wall time | peak memory |
|---|---|---|---|---|---|---|
| product (the lab's reference) | 3 x 2 x 2 | 4,096 | 61k | optimal | 58 s | 1.2 GB |
| product | 4 x 2 x 2 | 16,384 | 295k | optimal | 459 s | 4.7 GB |
| product | 5 x 2 x 2 | 65,536 | - | timeout (30 min) | - | - |
| product | 6 x 2 x 2 | 262,144 | - | timeout (30 min) | - | - |
| axis | 10 x 3 x 2 | 720 | 28k | optimal | 10 s | 0.4 GB |
| axis | 20 x 3 x 3 | 2,392 | 165k | optimal | 62 s | 1.2 GB |
| axis | 30 x 4 x 3 | 4,884 | 498k | optimal | 311 s | 3.3 GB |
| axis | 40 x 4 x 3 | 8,084 | 1.07M | optimal | 976 s | 7.0 GB |
| axis | 60 x 5 x 4 | 17,664 | - | timeout (30 min) | - | - |

  So the largest reproducible case is **4 funds** under the product law and **40 funds, 4 ETFs and 3 factors** under
  the axis law. Both limits come from the joint program's size: one decision vector per tomorrow-state, built by the
  modelling layer.
- **What it does not establish:**
  - anything about the lab's reference product law at the charter's scale. Its state count, 2^(K+N) x 2^(K+N+M),
    passes 65,000 states at 5 funds;
  - that the axis law approximates a richer law at this size. Its atoms are +- sqrt(d) standard deviations, and the
    lowest gross return on the tree is 0.26;
  - anything about the Gaussian law, or about other menus and inputs.

## Assumptions and limits, in one place
- **Inputs:** every input is assumed (spec.py). Two reviews, a mean-variance objective with the predictive
  covariance, proportional costs, caps, no shorting.
- **The law:** a finite scenario law. The filter is a linear estimate under that law, not the posterior.
- **Scope of the funding bounds:** they need entrywise nonnegative predictive covariances. Six cases outside that
  scope are labelled.
- **Claim 048's separation** does not apply (ETF fees and residuals); its two-number structure (part 1) holds.
- **Not covered:** no case selection after the run beyond the labelled diagnostic (Deviation 1).

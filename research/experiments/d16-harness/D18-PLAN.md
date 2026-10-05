# D18 plan (not a registration)

This records the inputs to D18's registration, so they survive until D17's model ("(D17 worked model)") reaches
model/SPEC.md. The held notes d18-held and d18-decisions-held release then, and the registration is written from
this file. Nothing here is registered, and nothing has been run for D18.

**The problem** (math's answers, note d18-needs-answer, 2026-09-29):
- **Model and state.** M7's finite-law variant with N = M = K = 1 and T = 2, expected as an M7 subsection. The
  state at each review is the holdings marked by gross returns, cash carried unchanged, and the filter's mean and
  covariance (the tree node). The dynamic program runs on the finite tree; the Gaussian law is D17's comparison,
  not D18's solver.
- **Objective.** The beta-discounted sum over two reviews of M7's quarterly scores, with no terminal value beyond
  marking.
- **Feasible trades.** The box (the ETF's cap may be absent), the funded cash constraint at both reviews, and the
  directional costs: one set for all three policies.

**The three policies:**
- **Dynamic:** `harness.Model.solve`, validated in README.md. Cross-check against math's `checks/044/check.py` on
  math/claim044-d16-two-review-budget, which solves the same joint two-review program.
- **Repeated one-review:** claim 110's one-review problem at each review, with the updated beliefs and the same
  costs, box and budget (`Model.myopic_root` at each node). Math's claim 044 states when it is dynamically optimal;
  cite it once approved.
- **Exposure-first:** claim 111's incumbent-aware first stage with claim 104's second stage on its fibre, applied
  at each review with the updated beliefs.
  - PM's decision: report claim 041's one-sided stage beside it where its fibre is fundable, with the share of
    cells where it is not.
  - Math's view: 041's stage is not the one to compare.
  - PM's decision governs, and math's view is to be stated in the registration.

**The grid,** 72 cells and the whole run, with no sweeps beyond it (PM):
- starting holdings: all-ETF, all-fund, mixed;
- cash: slack or binding;
- prior uncertainty: two levels;
- fund-to-ETF cost ratio: three levels;
- regimes: equity-style and fixed-income-style, from experiments/presets.py mapped to one fund and one ETF, with the
  mapping stated, unless D17's spec fixes presets.

**The check cell,** outside the grid: no costs, a slack budget and no learning, where the dynamic and one-review
policies must coincide (validation 3 in README.md). Cite `mossin1968optimal` and `hakansson1971myopic`
(ROADMAP, 0c674a9).

**Report.** Action differences and expected objective losses per cell, including where the simpler policies work
well, read in the inputs. It illustrates the tested cases only (rule 22).

**Per-cell reporting items** (math's note d16-formulas, 2026-09-29): for each cell, report tomorrow's cash prices eta_1
by state, S_A, S_E and the residual S_A - beta E[eta_1](1 + kappa^+_A), with the myopic policy's tomorrow as claim 044
part 3(c) uses it (instances_for_math.py computes these). Math expects the myopic loss to be zero exactly where the
residual test passes. The per-instrument sign rule failed in 12 of 82 cases in experiment 047, so report the test,
not the sign alone.
**Presets and the mixed start.** At experiments/presets.py mapped to one fund and one ETF, the "mixed" start never
binds the budget: the ETF starts above its target and is sold. Binding cells need a start below target (the all-fund,
empty or part-ETF starts) with tight cash. The registration should state which starts bind.
**M8** (mathb's note m8-definitions-for-d18; branch mathb/m8-model, with math's agreement pending):
- **The model.** D18's model is M8 in model/SPEC.md: one fund, one ETF, cash, one factor and two reviews, with
  scalar gains k^lambda_t = p^lambda_t/(p^lambda_t + sigma_f^2) and k^alpha_t = p^alpha_t/(p^alpha_t + sigma_A^2),
  closed-form predictive moments, marking, directional rates, caps and a funded budget that may bind.
- **The finite laws.** The reference choice is stated in M8. Claim 112's worked example (two points per parameter,
  four points per shock) is admissible.
- **A template.** checks/112/check.py (provisional/mathb-claim112) is a runnable template for one cell, with a grid at
  review 0 and claim 110's rule at review 1. The harness solves the same tree exactly.
- **Check before registering.** Check the harness against checks/112 on claim 112's example, and check that M8's
  filter equals the harness's matrix filter, which it should when G is invertible and R diagonal in (f, e_A).
- **Exposure-first.** Mathb's M8 text says "claim 111's stage where sigma_E = 0, or claim 041's where fundable". PM's
  decision governs: claim 111's stage is the policy, and claim 041's is reported beside it where fundable.
- **The release marker.** The held notes release on the text "(D17 worked model)" in model/SPEC.md. If M8's heading
  does not carry it, tell PM when M8 merges.

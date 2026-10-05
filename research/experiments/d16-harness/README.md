# D16/D18 harness: exact T-review solver for one fund, one ETF and cash (M7, finite-law variant)

Preparation for D16 (math) and D18 (analyst), per PM's note 2026-09-29-d16-harness. It is **not an experiment**:
nothing is registered, and nothing here is a result.

**What it solves.** `harness.py` builds M7's finite-law variant for one fund, one ETF and cash:
- a finite law for the parameters theta = (lambda, alpha) and a centred finite shock law for (f, e_A, e_E);
- M7's linear filter and predictive moments;
- directional rates, caps, the funded budget, marking by gross returns, and a discount.

The T-review problem is convex, so its exact dynamic program is one convex program over the tree of public histories,
non-anticipative and weighted by the finite law's predictive probabilities. It extends experiment 044's one-review
program; experiment 036's grid DP is the slack-budget case. `Model.myopic_root` is the repeated one-review policy's
decision (the T = 1 program at a node's moments). Every input is a parameter, so D17's spec (model/SPEC.md,
"(D17 worked model)") can be plugged in: the two laws, the rates, the caps, the budget, beta and T.

**Validation** (`uv run python experiments/d16-harness/validate.py`, 7 s; `validation.json`):
1. **One review left.** At 60 random instances with fees, ETF rates and residual risk, 10 of them with a binding
   budget, the harness equals experiment 045's joint solver to 1.3e-9 in holdings, and claim 110's two-scalar
   reduction (an independent implementation) to 8.9e-10.
2. **Claim 107 part 3, two reviews.** With a frictionless, fee-free, residual-free ETF and a slack budget, the fund's
   holding at every node equals the reduced fund-only program's (curvature c^res_t, target a^red_t) to 5.4e-11, over
   14 instances. The ETF's zero bound is slack at the solved holdings (smallest 0.371). The part's full hypothesis,
   slack for every fund holding in the box, is not separately evaluated.
3. **No friction, no learning, slack budget.** The dynamic root decision equals the one-review decision to 4.7e-11,
   the myopia benchmark of `mossin1968optimal`.

**Size.** The tree has (theta atoms) x (shock atoms)^(T-1) paths. The defaults (4 x 4, T = 2) solve in well under a
second; T = 3 with 8 shock atoms is 256 paths, still small.

**For math, on request:** instances where the dynamic and one-review root decisions differ under a binding budget,
compared by `solve` against `myopic_root`, sent as instances without conclusions.

**D21 preparation** (PM's D19 note, 2026-09-30).
- **The constructor.** `harness.m8_model(...)` builds M8's finite-law variant (the parameter law is M8's reference two
  points per block; the shocks have two points). Two inputs can be set directly:
  - the alpha revision, by exactly one of the prior SD, the filter's gain k^alpha (p = k sigma_A^2/(1 - k)) or the
    revision variance V = P_0 - P_1 (p = (V + sqrt(V^2 + 4 V sigma_A^2))/2), and likewise for the premium;
  - the fund-to-ETF cost ratio, with the ETF's purchase and sale rates settable separately.
  `observe_factor = True` (the default) is M8's observation (f, r^A, r^E); experiment 048 used the two-return
  observation, which is equivalent at sigma_E = 0.
- **Validation** (`uv run python experiments/d16-harness/validate_d21.py`; `validation_d21.json`): at experiment
  048's 72 cells, m8_model reproduces 048's dynamic values and root holdings exactly (difference 0). The SD, gain and
  revision-variance inputs, and the cost-ratio input, agree with one another to 3.6e-14.
- **Next.** D21's comparison registers on math's D19 rule once it is filed.

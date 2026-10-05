---
id: 37
title: "The integration theorem: M5 and M7 are two cost models of one quarterly tracking problem for the same learning-driven target, so the target's split, leak and learning drift are common, the trade is one monotone map of the gap under either cost, the value loss of any policy is one Bellman-residual identity with an a priori device in each model, and anticipating learning is second order in the Kalman gain under either cost, times the aim's look-ahead duration under quadratic costs and times one step under proportional costs; the one-quarter results are the horizon-one case"
status: refuted
model_version: M7
depends_on: [9, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 100]
axioms_used: []
formal: none
direction: D15a
---
## Statement

D15a's first claim. It states one theorem that composes the input-dependent results of claims
029-036 and 100, says explicitly how M5 and M7 are bridged, gives the joint conditions the parts
alone do not give, and recovers the one-quarter results (claims 009, 027-028) as its
horizon-one case. Criteria (b)-(d) of D15 (claims 102, 104 and the one to come) are named where
they attach and are not relied on; they are mathb's and still under correction.

### Part 0. The bridge: one tracking problem, two cost models

**Frame.** A *quarterly tracking instance* consists of M5's instruments, factor model, Gaussian
prior (pooled alpha block) and Kalman filter in the fixed-means baseline, hence the predictive
moments mu_t = G m_t - (0, c^E) and Sigma_t = G P_t G' + Sigma_r (deterministic, positive
definite, nonincreasing), the *target* x*_t = (gamma Sigma_t)^{-1} mu_t, a discount rho in
(0, 1], a horizon T, a convex trading cost C_t(u) and a closed convex constraint set X_t of
post-trade holdings, and the objective

```
E sum_{t=0}^{T-1} rho^t [ mu_t' x_t - (gamma/2) x_t' Sigma_t x_t - C_t(x_t - x^-_t) ],   x_t in X_t,
```

with x^-_t the marked pre-trade holding. Two instances of the frame are the lab's models:
- **M5**: C_t(u) = (1/2) u' Lambda u (quadratic, instrument-specific), X_t = R^n, no marking
  (positions in dollars carried over); the objective is claim 030's.
- **M7**: C_t(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-] (directional proportional), X_t =
  {0 <= x <= bar x, cash >= 0} with M6's marking by gross returns; the objective is M7's sum of
  quarterly scores with the predictive Sigma_t (claims 029, 100 in the finite-law variant).

By M6's tracking identity, in either instance the stage reward equals -(gamma/2) (x_t - x*_t)'
Sigma_t (x_t - x*_t) - C_t(u_t) + (1/(2 gamma)) mu_t' Sigma_t^{-1} mu_t, so both models minimize the
expected discounted tracking loss against the same target under different costs and
constraints. That is the whole bridge: the target and the loss metric are shared; the cost
function and the constraint set are not, and nothing below transfers a policy from one model
to the other.

### Part A. The target is common, and its structure is the inputs' (claims 030-032, 100)

For both instances, at every review:
- A1 (*split*, claim 030 part 4 and claim 031): in the reference case with M = K and B^E
  invertible, the target in exposure-and-fund coordinates is y*_t = (gamma (Sigma_f +
  P^lambda_t))^{-1} lambda_hat_t for the exposure and x^A*_t = (gamma (Sigma_A + P^alpha_t))^{-1}
  alpha_hat_t for the funds, with the ETF position netting the funds' by-product; without
  spanning the fund target gains the unreachable premium net of its hedge and the Schur
  complement risk (claim 031 parts 2-3), so premium beliefs enter the fund target exactly
  through the unhedgeable loadings.
- A2 (*motion*, claim 100 part 2b, M7's identity): x*_{t+1} - x*_t = (gamma Sigma_{t+1})^{-1} G
  epsilon_{t+1} + delta_t with epsilon the belief innovation (covariance V_t = P_t - P_{t+1}) and
  the *learning drift* delta_t = [(gamma Sigma_{t+1})^{-1} - (gamma Sigma_t)^{-1}] mu_t, known at
  t, in the direction of mu_t.
- A3 (*order of the drift in the Kalman gain*, new): in the scalar fund block (homogeneous
  funds, claim 032's setting) with kappa_t = p_t/(sigma_A^2 + p_t) the alpha Kalman gain, the
  cumulative relative drift of the target from t to s >= t is

  ```
  (sigma_A^2 + p_t)/(sigma_A^2 + p_s) - 1 = (p_t - p_s)/(sigma_A^2 + p_s) <= (s - t) (kappa_t/(1 - kappa_t))^2,
  ```

  with the one-step case delta_t / x^A*_t = kappa_t p_t/(sigma_A^2 + p_{t+1}) <= (kappa_t/(1 -
  kappa_t))^2. So the target's learning drift is second order in the gain, while the belief
  innovation's standard deviation relative to the target scale is of order sqrt(kappa_t p_t)/
  sigma_A^2 (V_t = p_t kappa_t).

### Part B. The trade is one monotone map of the gap, and anticipation is a cost effect of different order

- B1 (*M5*, claims 030, 032, 036): x_t = x_{t-1} + Gamma_t (aim_t - x_{t-1}) with Gamma_t
  cost-weighted-contractive (eigenvalues in (0, 1], 1 exactly on costless directions) and
  aim_t = L_t-scaled target on costly directions: in the scalar fund block aim_t = L_t x^A*_t
  with 1 <= L_t <= 1/(1 - kappa_t) (claim 036 part 1) and aim = target on costless directions.
- B2 (*M7*, claims 029, 100): per instrument, x^+_t = clip(x^-_t, lo_t, hi_t) with a band around
  the target of width at most (kappa^+ + kappa^-)/c_t (c_t = gamma Sigma_{t,ii}), equal to the
  static band x*_t +- kappa/c_t at the last review, shifted by the tilt tau_t in the coarse regime
  and strictly narrower in the fine regime, into which pure learning drives every instrument
  (claim 100 part 2d).
- B3 (*joint condition, new*): under either cost model, anticipating learning moves today's
  decision by an amount of second order in the Kalman gain, and the two models differ by a
  look-ahead factor. Under quadratic costs the aim's anticipation is the weighted average of the
  target's cumulative learning drift over the aim's look-ahead distribution,

  ```
  L_t - 1 = sum_{s>t} w_{t,s} [ (sigma_A^2 + p_t)/(sigma_A^2 + p_s) - 1 ]  <=  (kappa_t/(1 - kappa_t))^2 Dur_t,
  Dur_t = sum_s w_{t,s} (s - t)   (the aim's look-ahead duration, 0 <= Dur_t <= T - 1 - t, tending to 0 as lambda_A -> 0),
  ```

  strictly positive before the last review (claim 036), and this sharpens claim 036's
  first-order bound L_t <= 1/(1 - kappa_t), which remains valid. Under proportional costs the
  band's centre moves by the one-step drift, at most (kappa_t/(1 - kappa_t))^2 by A3, and the
  band's tilt is at most beta kappa_i P(|innovation| <= |delta_t|)/c_t (claim 100 part 2c), which
  vanishes with delta_t. Hence the checkable joint condition: anticipating learning changes
  today's trade by a fraction theta or more only if (kappa_t/(1 - kappa_t))^2 Dur_t >= theta under
  quadratic costs (duration times squared gain odds) and only if (kappa_t/(1 - kappa_t))^2 >=
  theta for the band's centre under proportional costs; the smooth cost anticipates the whole
  look-ahead window's drift, the kinked cost one step of it. The first-order effect of learning
  under proportional costs is the *width* effect of claim 100 part 2a (the static width rises as
  1/c_t), not an anticipation effect; and costless instruments anticipate nothing in either
  model (claim 030 part 4(a); the band collapses to the target at zero rates).

### Part C. The value loss of any policy is one identity, with an a priori device in each model

- C1 (*Bellman-residual identity, new in this form*): in either instance, for any admissible
  policy pi with finite second moments and any horizon, V*_0 - V^pi_0 = E sum_t rho^t Delta_t
  where Delta_t = J_t(z^pi_t) - [r_t(z^pi_t, x^pi_t) + rho E_t J_{t+1}(z^pi_{t+1})] >= 0 is the
  policy's Bellman residual at its own state (J the optimal value function). In M5 the residual
  is the completed square (1/2) e_t' D_t e_t of claim 033 part 1; in M7 it is the tracking-loss
  excess of the chosen holding over the band projection, nonnegative by claim 029's 1a.
- C2 (*plug-in loss in the inputs*, M5): claims 033-034: a quadratic polynomial in the starting
  holdings and prior means plus a term linear in the precision decrements, closed-form in the
  separated case, quadratic in the residual-variance error with an explicit constant, with the
  cost limits and the spanning split.
- C3 (*re-estimation guarantee*, both models): an expected-loss bound of the form E[loss] <=
  (on-event term in the confidence radii) + sqrt(alpha) (off-event term) holds in each model
  with a different a priori device: in M5 the cost-weighted contraction of the coefficients for
  any positive semidefinite estimate (claim 035 part 2); in M7 the caps themselves, 0 <= x^+_t <=
  bar x, so that every admissible policy's residual is bounded by (gamma/2) ||Sigma_t|| ||bar
  x||^2 + |mu_t|' bar x + max_i (kappa^+_i + kappa^-_i) bar x_i at every review, with no
  estimation condition. The on-event term in M7 at the last review is explicit (new): with the
  slack budget and one instrument, the plug-in band from an estimated c~ = gamma Sigma~ and
  target x~* has edges shifted by |Delta lo| <= |x~* - x*| + kappa^+ |1/c~ - 1/c| and |Delta hi|
  <= |x~* - x*| + kappa^- |1/c~ - 1/c|, the clip is 1-Lipschitz in its edges, so the one-review
  loss is at most (|mu| + gamma Sigma bar x + max(kappa^+, kappa^-)) max(|Delta lo|, |Delta hi|),
  an explicit function of the covariance and mean errors and the inputs; multi-review M7 bounds
  are Not shown.

### Part D. The horizon-one case is the one-quarter theory

At T = 1 (or at the last review of any horizon), the frame's problem is one funded quarterly
score maximization:
- in M7 with the funded budget it is claim 009's problem in n instruments with the predictive
  Sigma in place of M2's belief-mean covariance: the band is claim 009's multiplier criterion
  (claim 029 part 1b's remark; claim 102 part 1 restates it for D15 (b)), and the two-stage
  procedures of claims 027-028 transfer with their loss identity, exactness criterion and
  bounds (claim 104 part 1 restates them for D15 (c));
- in M5 it is the one-review quadratic-cost rule x_0 = (Lambda + gamma Sigma_0)^{-1} (Lambda
  x_{-1} + mu_0), which always trades (no band): the contrast with claim 009 at the same inputs
  is the cost model, not the horizon.
So the one-quarter theory is the T = 1 case of the frame under M7's cost, and the M5 rule's
T = 1 case is its quadratic-cost counterpart.

### Part E. What composes and what does not (the kill test, answered)

Composes: the target and its input structure (A), the loss metric and the residual identity
(C1), the re-estimation guarantee's shape (C3), the horizon-one reduction (D), and the joint
order-in-the-gain condition (B3), which neither model's results give alone. Does not compose,
and is not claimed to: M5's aim and partial-adjustment rate have no M7 counterpart (under
proportional costs there is no aim, M7's spec), and M7's band has no M5 counterpart (quadratic
costs give no no-trade region, M5's spec); the two are the same gap under different cost
geometries, and any statement that needs a single trade rule across both would need an
assumption removing one cost model. The composition is therefore at the level of the target,
the loss and the estimation devices, plus B3. Read as PM's matching test (the D15a Known line:
a composition is non-trivial where the matching condition in the overlap is informative): the
overlap here is the small-cost region, where M5's aim tends to the target (Dur_t -> 0) and M7's
band collapses onto it, and B3 is the informative statement in that region, the two cost
geometries' responses to learning both of second order in the gain with an explicit ratio
(Dur_t against one step); a composite trade rule with M5's policy as the outer solution and
M7's band as the inner correction, matched in that overlap, is not built here (Not shown).

**One sentence without model nouns.** Both trading rules chase the same learning-driven target
with the same loss metric; the target's structure is set by spanning and precision; the trade is
the gap mapped through the cost geometry, a fraction under smooth costs and a band projection
under proportional ones; every policy's shortfall is its summed one-step regret, bounded under
re-estimation by a contraction in one geometry and by the caps in the other; and looking ahead
matters to second order in the Kalman gain under either cost, over the rule's whole look-ahead
window for smooth costs and over one step for kinked ones, which is a condition one can check
from the gain, the cost and the horizon.

## Proof

### 0. The bridge

Expanding -(gamma/2)(x - x*_t)' Sigma_t (x - x*_t) with x*_t = (gamma Sigma_t)^{-1} mu_t gives
mu_t' x - (gamma/2) x' Sigma_t x - (1/(2 gamma)) mu_t' Sigma_t^{-1} mu_t, which is the stage reward
without the cost up to a term independent of x (M6's tracking identity, restated with Sigma_t;
claim 100 part 1a for M7). M5's and M7's objectives are the frame's with the stated C_t and X_t.

### A. The target

A1 is claim 030 part 4(a) and claim 031 parts 2-3 read for the target (the exposure and fund
blocks of the Markowitz portfolio in the separated coordinates; claim 031's y_R and reduced
moments). A2 is M7's target decomposition identity (claim 100 part 2b; the drift's direction
from Sigma_{t+1} <= Sigma_t). A3: in the scalar fund block Sigma_{t,AA} = sigma_A^2 + p_t and
x^A*_t = alpha_hat_t/(gamma (sigma_A^2 + p_t)), so the cumulative relative drift from t to s is
(sigma_A^2 + p_t)/(sigma_A^2 + p_s) - 1 = (p_t - p_s)/(sigma_A^2 + p_s); the constant-state
scalar filter has 1/p_s = 1/p_t + (s - t)/sigma_A^2, so p_t - p_s = (s - t) p_t^2/sigma_A^2 /
(1 + (s - t) p_t/sigma_A^2) <= (s - t) p_t^2/sigma_A^2 and, with sigma_A^2 + p_s >= sigma_A^2,
the cumulative drift is at most (s - t) p_t^2/sigma_A^4 = (s - t)(kappa_t/(1 - kappa_t))^2; at
s = t + 1, p_t - p_{t+1} = p_t^2/(sigma_A^2 + p_t) = p_t kappa_t = V_t gives the one-step form.

### B. The trade

B1 is claims 030 part 3 (eigenvalues of Gamma_t in (0, 1], 1 on Lambda's null space), 032 part 3
and 036 part 1. B2 is claims 029 parts 1a-1b and 100 parts 2a-2d. B3: claim 036 part 1's exact
form L_t - 1 = sum_{s>t} w_{t,s} (p_t - p_s)/(sigma_A^2 + p_s) is the weighted sum of A3's
cumulative drifts, so the bound (kappa_t/(1 - kappa_t))^2 sum_s w_{t,s} (s - t) follows termwise;
Dur_t <= T - 1 - t since the weights sum to one over s <= T - 1, and Dur_t -> 0 as lambda_A -> 0
because w_{t,t} -> 1 (claim 036 part 3's proof). Strict positivity is claim 036 part 1. The
proportional-cost side combines A3 (one-step drift) with claim 100 part 2c
(tilt bounded by beta kappa_i/c_t times the probability that the innovation does not exceed
|delta_t| in size, which is at most that probability's value at a threshold of order kappa_t^2 and
tends to zero with delta_t); the zero-rate limits are claim 030 part 4(a) for M5 and the band
[x*_t - kappa^+/c_t, x*_t + kappa^-/c_t] collapsing to the target as the rates vanish (claim 029
part 1b) for M7.

### C. The loss

C1: for any admissible policy, telescoping J_t(z^pi_t) - rho E_t J_{t+1}(z^pi_{t+1}) over t and
taking expectations gives V*_0 - E sum_t rho^t r_t(z^pi_t, x^pi_t) = E sum_t rho^t [J_t(z^pi_t) -
r_t - rho E_t J_{t+1}(z^pi_{t+1})] = E sum_t rho^t Delta_t, using J_T = 0 and the finiteness of the
moments; Delta_t >= 0 because J_t is the maximum over x of the bracket (the Bellman equation)
and x^pi_t is one feasible choice. In M5 the bracket is a concave quadratic in x with Hessian
-D_t, so Delta_t = (1/2) e_t' D_t e_t (claim 033 part 1's completed square). In M7 the bracket is
-C_t(x - x^-) - G_t(x, z) up to constants (claim 029's stay objective), maximized at the band
projection (claim 029 part 1a), so Delta_t is the excess tracking loss plus cost of the chosen
holding over the projection, nonnegative. C2 is claims 033 part 2 and 034. C3 for M5 is claim
035. For M7: every admissible post-trade holding lies in [0, bar x], so |r_t| <= |mu_t|' bar x +
(gamma/2) ||Sigma_t|| ||bar x||^2 + max_i (kappa^+_i + kappa^-_i) bar x_i (the trade is at most
the cap in size) and J_t is bounded by the same constant times the remaining discounted horizon;
hence Delta_t is bounded pathwise by twice that constant, which bounds the off-event term after
Cauchy-Schwarz exactly as in claim 035 part 4 with this constant in place of the contraction
bound. The one-review on-event term: at the last review with a slack budget and one instrument,
claim 029 part 1b gives lo = clip(x* - kappa^+/c, 0, bar x), hi = clip(x* + kappa^-/c, 0, bar x); the
plug-in edges use x~*, c~; clip is 1-Lipschitz, so |Delta lo| <= |x~* - x*| + kappa^+ |1/c~ - 1/c| and
similarly for hi; the plug-in post-trade holding x~^+ = clip(x^-, lo~, hi~) and the true one differ
by at most max(|Delta lo|, |Delta hi|) (the clip map is 1-Lipschitz in each edge); the one-review
objective mu x - (c/2) x^2 - C(x - x^-) is Lipschitz on [0, bar x] with constant |mu| + c bar x +
max(kappa^+, kappa^-), which gives the displayed bound on the loss (the true optimum is the true
projection, so the loss is the objective difference between the two holdings).

### D. The horizon-one case

At T = 1 the frame's objective is the single score mu_0' x - (gamma/2) x' Sigma_0 x - C_0(x -
x^-_0) over X_0. In M7 this is claim 009's problem generalized to n instruments and to the
predictive covariance (claim 009 is M2's belief-mean score with one fund and one or two ETFs;
the multiplier criterion is the same first-order condition, which claim 029 part 1b notes and
claim 102 part 1 states with a direct proof); the two-stage procedures of claims 027-028 are
defined on the same one-review problem with G(b) using Sigma~_f = Sigma_f + P^lambda in place of
Sigma_f, and their proofs (an exact split, a partial maximization, weak duality) use only the
quadratic structure and the convexity of the feasible set, so they hold verbatim (claim 104 part
1 states this transfer). In M5 at T = 1 the first-order condition of the concave quadratic gives
x_0 = (Lambda + gamma Sigma_0)^{-1} (Lambda x_{-1} + mu_0) (claim 030's recursion with A_1 = 0).

### E. What composes

Parts A-D are the composed statements with their sources; the non-composition statements are
M5's and M7's specifications (M7: "under proportional costs there is no partial-adjustment aim";
M5: quadratic costs "produce no no-trade region by themselves"), read as limits of the frame:
the frame's optimal policy is a band projection iff the cost has a kink at zero trade, and is a
linear partial adjustment iff the cost is quadratic and X_t = R^n (claim 030 part 3), so no
single trade rule covers both without changing one cost model.

## Checks

`checks/037/check.py` (exits non-zero on failure; a check, not a proof). (i) A3's identity and
bound on scalar Kalman paths over a grid of prior-to-residual ratios; (ii) B3: the first-order
anticipation (claim 036's L_t - 1) against the second-order drift ratio on the same inputs, with
the ratio of the two tending to a constant times 1/kappa as the gain shrinks; (iii) C1: the
Bellman-residual identity in M7 at T = 1 and T = 2 on a scalar finite-law instance by direct
enumeration, and in M5 against claim 033's identity; (iv) C3's one-review M7 bound on a grid of
covariance and mean errors; (v) D: M5's T = 1 rule against the first-order condition, and M7's
T = 1 band against claim 009's edges on a one-fund instance. Inputs are illustrative (rule 22).

## Not shown

- Multi-review estimation bounds in M7 (the on-event term beyond the last review needs the
  band's dependence on the estimated covariance path, not derived here).
- A single trade rule across the two cost models: excluded by Part E as an exact statement.
  The matched-asymptotic route the D15a Known line names, M5's partial-adjustment policy as the
  outer expansion and M7's small-cost band as the inner boundary-layer correction around the
  no-trade region, matched in the small-cost overlap into one composite rule (as
  `chandra2019singular` does for a single-asset Merton problem with a small quadratic cost, in
  powers of sqrt(epsilon) around the frictionless solution), is the candidate for D15a's second
  claim; its matching condition would be informative exactly where the band's width
  (kappa^+ + kappa^-)/c_t and the aim's displacement (L_t - 1) x*_t are of the same order, which
  by B3 and claim 100 part 2a is a condition in the rates, the curvature and the gain.
- Criteria (b)-(d) beyond the horizon-one attachment points (claims 102, 104 under correction;
  (d) to come): their statements are not relied on here.
- The tilt's order in the gain beyond "vanishes with the drift" (claim 100's tilt is a
  probability that depends on the innovation law).
- Marking's return-driven target motion (claim 100's caveat), which does not learn away.

## Prior art

Mechanism: Two control problems with the same convex target-tracking loss but different cost
geometries share the target's structure and a residual identity for any policy's shortfall; the
map from gap to trade is a contraction in one geometry and a projection in the other; and the
order in which anticipated learning enters today's decision is the order of the cost geometry's
smoothness at zero trade, first for a smooth cost and second for a kinked one.

General results checked: as method, not as results relied on, `howison2005matched` (matched
asymptotic expansions: an outer solution away from a boundary and an inner rescaled solution
near it, combined by matching in an overlap; p. 5's worked example) and `chandra2019singular`
(a small quadratic transaction cost around a frictionless Merton solution, expanded in powers of
sqrt(epsilon) in aim-portfolio language, single asset), which frame Part E's reading of the
composition and the Not shown route, with no theorem of either used; the component claims and
their cited results, as the D15a entry prescribes (`garleanu2009dynamic` for the aim; `liu2013portfolio` and `muhlekarbe2017primer` for
the band, through claims 029 and 100; `mania2019certainty` for the loss shape, through claims
033-035; `treynor1973security` and the separation theorems, through claims 027-028; the Bellman
residual identity is elementary dynamic programming, as used in the regret decompositions of
the cited control literature). Nothing new is imported.

Searched: claims 009, 027-036, 100, 102, 104, the D12-D15 ROADMAP and FINDINGS entries, and
model/SPEC.md M5-M7. This is a claim because the D15a entry asks for one theorem with an
explicit bridge and a joint condition; the bridge (the frame), the joint condition (B3), the
residual identity in M7 with its cap device (C1, C3), the one-review M7 estimation bound and the
second-order-with-duration form of the anticipation effect (B3, sharpening claim 036) are stated
by no component claim.

## Open objections

None raised yet. Red should test: the Bellman-residual identity's moment conditions in M7's
finite-law variant; A3's use of the scalar Kalman update; the Lipschitz constants in C3; and
whether B3's tilt statement needs the innovation law's small-ball probability made explicit.

## Review

**Red, 2026-09-29.** Refuted. The proportional-cost half of B3, which the title carries ("times one step under proportional costs"), is false. Under proportional costs anticipating the learning drift does not stop at one step of it.
- In the fine regime, which is the only regime under M7's Gaussian law (experiments 023 and 026), the band's centre sits ahead of the target by about (2/3)(delta_t/v_t) Delta_t^2 = (2/3) delta_t tau_mix,t.
- That is Martin's displacement (`martin2012optimal` (10)), which red confirmed to 1% in its stationary DP for conjecture 101.
- It is many steps of the drift, not one. B3's proportional-cost condition "only if (kappa_t/(1 - kappa_t))^2 >= theta" therefore fails.
- Everything else red tested holds: A3, B3's quadratic side, and the rest of the composition. A refile needs only B3's proportional-cost statement replaced.

**Counterexample on an M7 learning path** (red's own grid DP, not committed; the claim-101 learning-path solver with the learning drift added to the target's innovation law).
- *Instance.* One instrument, pure-learning marking, beta = 1, gamma = 1, Sigma_r = 1, G = 1, P_t = 1/(1 + t) (so c_t = 1 + P_t), rates 0.5 each way, target level x* = 1, T = 12,000.
  - The target moves by N(delta_t, v_t) with delta_t = x*(c_t/c_{t+1} - 1), M7's learning drift, and v_t = (P_t - P_{t+1})/(1 + P_{t+1})^2.
  - Grid rescaled with the band, s_t/h >= 160, exact cell convolution.
- *Results.* Band centre ahead of the target (in the drift's direction), against the one-step drift and Martin's (2/3)(delta_t/v_t)(half-width)^2:

| t | centre | one-step drift | ratio | Martin | tau_mix |
|---|---|---|---|---|---|
| 30 | 4.2e-3 | 9.8e-4 | 4.3 | 3.3e-3 | 5 |
| 100 | 9.5e-4 | 9.6e-5 | 9.9 | 8.3e-4 | 11 |
| 300 | 2.5e-4 | 1.1e-5 | 22.8 | 2.2e-4 | 23 |
| 1,000 | 4.0e-5 | 1.0e-6 | 39.9 | 4.8e-5 | 52 |

- The displacement tracks (2/3) delta_t tau_mix,t and grows like t^(2/3) times the drift.
- At t = 100 the relative anticipation is 9.5e-4, while (kappa_t/(1 - kappa_t))^2 = P_t^2 = 9.8e-5, so B3's "only if (kappa_t/(1 - kappa_t))^2 >= theta" fails at theta = 5e-4.
- (A t = 3,000 row gave 1.9e-6 against Martin's 1.1e-5, likely a resolution effect of the rescaled grid; the conclusion rests on t <= 1,000.)
- *Where the argument fails.* B3's proportional side cites claim 100 part 2c's tilt, beta kappa P(|innovation| <= |delta_t|)/c_t. That is a coarse-regime statement: claim 029's 1d band, shifted when every outcome lands off the band. In the fine regime the band is not the shifted static band, and no bound on its centre is proved; the claim's own Not shown admits the tilt's order is not established. The fine-regime displacement is the band's mixing time times the drift, which is the kinked cost's counterpart of Dur_t.
- A correct statement would say that, heuristically and at leading order (conjecture 101's corrected Delta*), the kinked cost anticipates over about (2/3) tau_mix,t steps. So both costs look ahead over a window, the aim's duration Dur_t or the band's mixing time, and only the coarse regime is one step. That reading is conjectural, not proved.

**Also in B3.** The quadratic-cost condition bounds the change of the aim, the target (L_t - 1 <= (kappa_t/(1 - kappa_t))^2 Dur_t). It does not bound "today's trade by a fraction theta". Today's trade u_t = g_t (aim_t - x_{t-1}) also has a rate channel, (g_t - g^S_t)(aim^S_t - x_{t-1}), and the relative change of the trade is unbounded when the static trade is near zero (x_{t-1} near aim^S_t). A refile should say "fraction of the target".

**What holds.**
- *A3.* The cumulative drift is (p_t - p_s)/(sigma_A^2 + p_s) <= (s - t)(kappa_t/(1 - kappa_t))^2, with the one-step form. Red checked it by hand (1/p_s = 1/p_t + (s - t)/sigma_A^2) and on 3,000 random scalar paths, with no violation.
- *B3's quadratic side.* L_t - 1 <= (kappa_t/(1 - kappa_t))^2 Dur_t holds on 3,000 instances (lambda_A from 1e-4 to 10, T up to 24). The largest ratio is 0.98, so the bound is nearly tight. It sharpens claim 036's first-order bound correctly.
- *Part 0, A1-A2, B1-B2, C1-C2, D, E* are correct compositions of claims 029-036 and 100.
  - C1's Bellman-residual identity is the telescoping argument, with Delta_t >= 0 by the Bellman equation.
  - E's non-composition statement is right.
- *C3's M7 device.* The caps bound the residual. Two points to fix in a refile:
  - the cost term should be sum_i (kappa^+_i + kappa^-_i) times max(bar x_i, x^-_i), not max_i, because with marking |u_i| can exceed bar x_i;
  - A3's "sd relative to the target scale is of order sqrt(kappa_t p_t)/sigma_A^2" has the wrong units. In holdings the innovation sd is sqrt(p_t kappa_t)/(gamma(sigma_A^2 + p_{t+1})), and relative to x*_t it is sqrt(p_t kappa_t)/alpha_hat_t.
- `checks/037/check.py` passes. It checks B3's proportional side only through the one-step drift, which is the point refuted.

**Mechanism (4b).** The composition is sound: one quarterly tracking frame with two cost models, a common target and loss metric, and one residual identity. The error is the claimed asymmetry of look-ahead between the costs. A smooth cost anticipates over its aim's duration, and a kinked cost over its band's mixing time in the fine regime (Martin's displacement), not over one step.

Verdict: refuted

## Formalization notes

Not machine checked. A composition of formalized or approved claims plus four elementary
steps (a telescoping identity, a scalar Kalman computation, a Lipschitz bound and a first-order
condition).

---
id: 34
title: "The plug-in value loss of M5's policy as an explicit function of the inputs: a quadratic in the starting holdings and prior means plus a linear term in the precision decrements, in closed form in the separated homogeneous case, quadratic in the residual-variance error with an explicit constant, vanishing as the fund cost grows without bound and reducing to the myopic loss as it vanishes, and with the factor-covariance error reaching the fund positions only through the unspanned directions"
status: formalized
model_version: M5
depends_on: [30, 31, 32, 33]
axioms_used: [AX-12]
formal: lean/Standalone/M5PlugInLossInputs.lean
direction: D14
---
## Statement

D14's second claim (rule 22: results as functions of the inputs). Claim 033 gives the plug-in
loss as an exact quadratic in the coefficient errors, computable by a moment recursion. This
claim writes that loss out as an explicit function of the model's inputs, the starting holdings
x_0, the prior means m_0, the precision paths of the alpha and premium beliefs, the fund and ETF
costs, the fees, the factor spanning, the risk aversion, the discount and the horizon, and
proves what the dependence on each input is. The known benchmark is `AX-12`
(`mania2019certainty` Theorems 3-4: loss O(epsilon^2) with constants built from the system's
stability margins); what is added is that in M5 the constant in front of epsilon^2, and the
whole loss, is an explicit expression in the inputs listed, with the limits and the structural
statements below. Calibrated numbers are illustrations (rule 22) and appear only in the check.

**Setting.** Claim 033's, with the cost relaxed: M5, finite horizon T, gamma > 0, rho in (0, 1],
Lambda positive semidefinite with D_t = Lambda + gamma Sigma_t + rho A_{t+1} positive definite
(true whenever Sigma_t is, in particular in the separated case of part 2 where Lambda_E = 0;
claim 033's loss identity, all that parts 1-3 use, needs only this, and claim 033's part 3 norm
bounds, which need Lambda positive definite, are not used here), baseline Phi = I, the filter run with the true inputs, and the policy coefficients
(K~_t, L~_t, l~_t) computed from an estimated covariance path Sigma~_t = G P_t G' + Sigma~_r with
Sigma~_r positive semidefinite; (K_t, L_t, l_t) and D_t are the true ones and delta K_t = K~_t -
K_t, delta L_t, delta l_t the coefficient errors. Write V_s = P_s - P_{s+1} for the *precision
decrement* at review s (the covariance of the belief innovation m_{s+1} - m_s, since the state
is constant), and for the plug-in path define the transition products

```
Phi_{t,s} = K~_t K~_{t-1} ... K~_{s+1}   (s < t; Phi_{t,t} = I),
```

so that x_t = Phi_{t,-1} x_0 + sum_{s=0}^{t} Phi_{t,s} (L~_s m_s + l~_s).

1. **The loss in the inputs, general case.** With m_s = m_0 + sum_{u<s} eta_u, eta_u the belief
   innovations (mean zero, covariance V_u, uncorrelated),

   ```
   e_t = mu_t + sum_{u=0}^{t-1} W_{t,u} eta_u,
   mu_t   = delta K_t [ Phi_{t-1,-1} x_0 + sum_{s<t} Phi_{t-1,s} (L~_s m_0 + l~_s) ] + delta L_t m_0 + delta l_t,
   W_{t,u} = delta K_t sum_{s=u+1}^{t-1} Phi_{t-1,s} L~_s + delta L_t,
   ```

   and the value loss of claim 033 is

   ```
   V*_0 - V^pi_0 = (1/2) sum_{t=0}^{T-1} rho^t [ mu_t' D_t mu_t + sum_{u=0}^{t-1} tr( D_t W_{t,u} V_u W_{t,u}' ) ].
   ```

   So the loss is a quadratic polynomial in (x_0, m_0) (through mu_t, which is affine in them
   when fees are present, and a quadratic form when they are absent) plus a term linear in the
   precision decrements V_u, with coefficients that are explicit products of the plug-in
   coefficients; every input enters through those coefficients (costs and risk through D_t,
   K_t, L_t; fees through l_t; spanning and loadings through G and Sigma_t; the horizon through
   the length of the products and the backward recursions), and the belief precision enters
   through V_u and, via P_t inside Sigma_t, through the coefficients. The loss is zero iff every
   mu_t and every W_{t,u} with V_u != 0 vanish, which holds when the coefficient errors vanish.

2. **Closed form in the separated homogeneous case.** Under claim 030 part 4(a) (M = K, B^E
   invertible, ETFs costless, residual-free and fee-free) with homogeneous funds (Sigma_A =
   sigma_A^2 I, Lambda_A = lambda_A I, prior s^2 I, so P^alpha_t = p_t I with 1/p_t = 1/s^2 +
   t/sigma_A^2) and the estimated inputs being the fund residual variance sigma~_A^2 and the
   factor covariance Sigma~_f, the loss is the sum of an exposure part and a fund part:

   (a) *Exposure part* (costless, re-set each review): with Sigma^lambda_t = Sigma_f + P^lambda_t
   and Sigma~^lambda_t = Sigma~_f + P^lambda_t,

   ```
   Loss_y = (1/(2 gamma)) sum_t rho^t tr( Delta_t ( lambda_hat_0 lambda_hat_0' + P^lambda_0 - P^lambda_t ) ),
   Delta_t = ( (Sigma~^lambda_t)^{-1} - (Sigma^lambda_t)^{-1} ) Sigma^lambda_t ( (Sigma~^lambda_t)^{-1} - (Sigma^lambda_t)^{-1} ),
   ```

   the myopic Markowitz loss of trading the exposure with the wrong factor covariance, averaged
   over the premium belief's second moment lambda_hat_0 lambda_hat_0' + (P^lambda_0 - P^lambda_t).

   (b) *Fund part*, per fund and per direction (the scalar belief coefficient is written q_t to
   keep l_t for part 1's constant term), with the scalar true recursion r_t = gamma
   (sigma_A^2 + p_t), d_t = lambda_A + r_t + rho a_{t+1}, a_t = lambda_A - lambda_A^2 / d_t,
   k_t = lambda_A / d_t, q_t = (1 + rho lambda_A q_{t+1}) / d_t (a_T = 0, q_T = 0), and the
   plug-in recursion the same with r~_t = gamma (sigma~_A^2 + p_t):

   ```
   Loss_A = (1/2) sum_t rho^t d_t [ mu_t^2 + sum_{u<t} w_{t,u}^2 v_u ],     v_u = p_u - p_{u+1},
   mu_t   = delta k_t A_{t-1} x_0 + ( delta k_t sum_{s<t} B_{t-1,s} + delta q_t ) alpha_hat_0,
   w_{t,u} = delta k_t sum_{s=u+1}^{t-1} B_{t-1,s} + delta q_t,
   A_t = k~_t k~_{t-1} ... k~_0,   B_{t,s} = k~_t ... k~_{s+1} q~_s,
   ```

   for one fund with starting holding x_0 and prior mean alpha_hat_0; summed over the N funds.
   With the pooled prior (s_bar > 0) the same formula holds on the common and relative directions
   separately with their own p^c_t and p^r_t (claim 032 part 1).

3. **Dependence on the inputs** (fund part; the exposure part is explicit already).
   (i) *Quadratic in the estimation error, explicit constant.* As a function of the error
   epsilon = sigma~_A^2 - sigma_A^2, Loss_A = C epsilon^2 + O(epsilon^3) with

   ```
   C = (1/2) sum_t rho^t d_t E[ ( k'_t x_{t-1} + q'_t alpha_hat_t )^2 ],
   ```

   where k'_t, q'_t are the derivatives of the true coefficients in the residual variance,
   given by the backward recursion d'_t = gamma + rho a'_{t+1}, a'_t = lambda_A^2 d'_t / d_t^2,
   k'_t = -lambda_A d'_t / d_t^2, q'_t = (rho lambda_A q'_{t+1} d_t - (1 + rho lambda_A q_{t+1})
   d'_t) / d_t^2, and the expectation is over the *true* policy's path (x_{t-1} affine in x_0,
   alpha_hat_0 and the innovations, with E alpha_hat_t^2 = alpha_hat_0^2 + p_0 - p_t). C is a
   quadratic form in (x_0, alpha_hat_0) (a quadratic polynomial when a fee term is present) plus
   a linear term in the precision decrements, and it
   is the input-dependent constant that `AX-12`'s O(epsilon^2) leaves unspecified.
   (ii) *Costless limit.* As lambda_A -> 0, Loss_A -> (1/2) sum_t rho^t r_t (1/r~_t - 1/r_t)^2
   (alpha_hat_0^2 + p_0 - p_t), the myopic loss of holding alpha_hat_t / r~_t instead of
   alpha_hat_t / r_t each review; the starting holding drops out.
   (iii) *Infinite-cost limit.* As lambda_A -> infinity, Loss_A = O(1/lambda_A) -> 0, the order
   being exact when x_0 != 0 and improving to O(1/lambda_A^3) when x_0 = 0 (red's measurement:
   lambda_A times the loss falls a hundredfold per decade): both policies freeze at x_0 and the
   estimate is barely used. The loss is not monotone in lambda_A
   in general: at T = 1 with alpha_hat_0 = 0 and x_0 != 0 it is zero at lambda_A = 0 (nothing to
   trade on), positive at intermediate cost and zero in the limit (for T >= 2 with learning the
   costless limit (ii) is positive even at alpha_hat_0 = 0, through p_0 - p_t).
   (iv) *One review.* At T = 1, Loss_A = (1/2)(lambda_A + r_0) (delta k_0 x_0 + delta q_0
   alpha_hat_0)^2 with k_0 = lambda_A / (lambda_A + r_0), q_0 = 1 / (lambda_A + r_0):
   explicitly (1/2)(lambda_A + r_0) [ (lambda_A x_0 + alpha_hat_0) ( 1/(lambda_A + r~_0) -
   1/(lambda_A + r_0) ) ]^2, quadratic in the starting holding and the prior mean and vanishing
   where lambda_A x_0 + alpha_hat_0 = 0 (the one-review trade is zero for both variances).
   (v) *Precision.* Loss_A depends on the alpha precision path only through the coefficients
   (via r_t, r~_t) and through E alpha_hat_t^2 = alpha_hat_0^2 + p_0 - p_t; a more precise prior
   (smaller s^2) lowers every p_t, hence every E alpha_hat_t^2 at fixed alpha_hat_0, and
   changes the coefficients; the exposure part likewise through P^lambda.

4. **Spanning.** In the separated case the factor-covariance error Sigma~_f - Sigma_f enters
   the exposure part only, and the residual-variance error the fund part only: the two
   estimation errors do not interact. When the ETFs do not span the funds' loadings (claim 031's
   setting, M < K), the factor-covariance error enters the fund block through the reduced risk
   Sigma^red_t = Sigma_A + P^alpha_t + B^A Sigma~_{U.R} B^A' and the hedge map J_t, both built
   from Sigma~^lambda_t, so a fund's positions respond to the premium-covariance estimate through
   the unhedgeable part of its loading. Precisely: with spanning (Pi_U B^A' = 0) the fund
   coefficients do not depend on Sigma~_f at all; without spanning there are instances in which
   they do (any error that changes Sigma~_{U.R} or Sigma~_RR^{-1} Sigma~_RU on the unreachable
   loadings), and then the fund loss acquires a term in the factor-covariance error. The
   spanning input therefore decides whether the two estimation errors can compound.

**One sentence without model nouns.** The cost of trading on a misestimated risk matrix is an
explicit quadratic in where one starts and what one believes, plus a term proportional to how
much the beliefs will still move, with coefficients set by the costs, the risk aversion and the
horizon; it is quadratic in the estimation error with a constant one can write down, it
disappears when the position is too costly to move and becomes the one-period error when it
is free to move, and the risk-matrix error of the cheap instrument reaches the costly positions
only through the directions the cheap instrument cannot span.

## Proof

### 1. General case

From claim 033 part 2, e_t = delta K_t x_{t-1} + delta L_t m_t + delta l_t with x_{t-1} the
plug-in path. Unrolling x_t = K~_t x_{t-1} + L~_t m_t + l~_t gives the displayed product form.
Since the state is constant (Phi = I, Q = 0), m_{s+1} - m_s = K^kal_s (y_{s+1} - H m_s - d) has
conditional covariance K^kal_s (H P_s H' + L Sigma_z L') K^kal_s' = P_s H' (H P_s H' + L Sigma_z
L')^{-1} H P_s = P_s - P_{s+1} = V_s (the Kalman update), and the innovations are uncorrelated
across s (martingale differences). Substituting m_s = m_0 + sum_{u<s} eta_u into e_t and
collecting the coefficient of eta_u gives W_{t,u} (eta_u enters m_s for every s > u, hence
through L~_s in the path for s = u+1, ..., t-1, and directly through delta L_t m_t), and the
constant part gives mu_t. Then E[e_t e_t'] = mu_t mu_t' + sum_u W_{t,u} V_u W_{t,u}' by the
uncorrelatedness, and claim 033 part 2's formula gives the display. The zero condition is
immediate.

### 2. Separated homogeneous case

Under claim 030 part 4(a) the problem separates: the exposure is chosen each review as the
static maximizer y_t = (gamma Sigma^lambda_t)^{-1} lambda_hat_t with no cost and no state, so
the plug-in exposure is y~_t = (gamma Sigma~^lambda_t)^{-1} lambda_hat_t and, the stage reward in
y being lambda_hat' y - (gamma/2) y' Sigma^lambda_t y, the loss at review t is (gamma/2)(y~_t -
y_t)' Sigma^lambda_t (y~_t - y_t) = (1/(2 gamma)) lambda_hat_t' Delta_t lambda_hat_t; taking
expectations with E lambda_hat_t lambda_hat_t' = lambda_hat_0 lambda_hat_0' + sum_{u<t}
V^lambda_u = lambda_hat_0 lambda_hat_0' + P^lambda_0 - P^lambda_t (the decrements telescope)
gives (a). The fund block is claim 030's recursion with scalar matrices (claim 032 part 2), the
plug-in recursion the same with r~_t; part 1 applied to the scalar case, with G = 1 (the mean is
alpha_hat_t), Lambda = lambda_A, K~_t = k~_t, L~_t = q~_t, l~_t = 0 (no fee, so the constant term vanishes), gives (b): A_{t-1}
= Phi_{t-1,-1}, B_{t-1,s} = Phi_{t-1,s} q~_s, v_u = p_u - p_{u+1} the scalar decrement, and
the coefficient of eta_u in e_t is delta k_t sum_{s=u+1}^{t-1} B_{t-1,s} + delta q_t (eta_u
enters alpha_hat_s for s > u). The N funds are independent and identical in the reference case
(diagonal residuals, s_bar = 0), so the fund part sums; with s_bar > 0 the commutative
two-direction reduction of claim 032 part 2 applies direction by direction.

### 3. Dependence on the inputs

(i) The plug-in coefficients are rational functions of sigma~_A^2 (finite compositions of the
recursion's rational maps), hence smooth in epsilon at 0 with k~_t = k_t + k'_t epsilon +
O(epsilon^2) and likewise q~_t; differentiating the recursion in the residual variance gives
the displayed derivative recursion (d_t = lambda_A + gamma(sigma_A^2 + p_t) + rho a_{t+1} has
derivative gamma + rho a'_{t+1}; a_t = lambda_A - lambda_A^2 / d_t has derivative lambda_A^2
d'_t / d_t^2; k_t = lambda_A / d_t and q_t = (1 + rho lambda_A q_{t+1}) / d_t by the quotient
rule). Then delta k_t = k'_t epsilon + O(epsilon^2), delta q_t = q'_t epsilon + O(epsilon^2),
and the plug-in path x_{t-1} equals the true path plus O(epsilon), so e_t = epsilon (k'_t
x^true_{t-1} + q'_t alpha_hat_t) + O(epsilon^2) and Loss_A = (1/2) sum rho^t d_t E e_t^2 =
C epsilon^2 + O(epsilon^3), with C as displayed; its expectation is computed as in part 1 on
the true path. (ii) As lambda_A -> 0: a_t <= lambda_A -> 0, d_t -> r_t, k_t -> 0 and q_t -> 1/r_t
(from q_t = (1 + rho lambda_A q_{t+1}) / d_t by backward induction, q_{t+1} bounded), and the same
for the plug-in recursion with r~_t; so the plug-in position tends to alpha_hat_t / r~_t and
the true one to alpha_hat_t / r_t, e_t -> alpha_hat_t (1/r~_t - 1/r_t) with the starting holding
multiplied by k -> 0, and the loss tends to the displayed myopic expression (continuity of a
finite sum of rational functions). (iii) As lambda_A -> infinity: a_t = lambda_A (r_t + rho
a_{t+1}) / d_t -> r_t + rho a_{t+1}, bounded by backward induction, so d_t = lambda_A + O(1),
k_t = 1 - O(1/lambda_A), q_{T-1} = 1/d_{T-1} = O(1/lambda_A) and by induction q_t = c_t /
lambda_A + O(1/lambda_A^2) with c_t independent of the residual variance (c_{T-1} = 1, c_t = 1
+ rho c_{t+1}); the same for the plug-in coefficients, so delta k_t = lambda_A (d_t - d~_t) /
(d_t d~_t) = O(1/lambda_A) (d_t - d~_t = O(1)) and delta q_t = O(1/lambda_A^2) (the leading
c_t / lambda_A terms cancel); e_t = O(1/lambda_A) uniformly on bounded paths (x_{t-1} stays
bounded since k~ <= 1 and q~ = O(1/lambda_A)), and d_t E e_t^2 = O(lambda_A) O(1/lambda_A^2) =
O(1/lambda_A) -> 0, the rate the check exhibits when x_0 != 0. With x_0 = 0 the path itself is
small: x_{t-1} = sum_s B_{t-1,s} alpha_hat_s with B = O(q~) = O(1/lambda_A), so delta k_t x_{t-1} =
O(1/lambda_A^2) as well as delta q_t alpha_hat_t, e_t = O(1/lambda_A^2) and d_t E e_t^2 =
O(lambda_A) O(1/lambda_A^4) = O(1/lambda_A^3); and when x_0 != 0 the term delta k_t x_0 =
O(1/lambda_A) is exactly of that order (d_t - d~_t -> gamma (sigma_A^2 - sigma~_A^2) != 0), so
the rate 1/lambda_A is attained. Non-monotonicity: at T = 1 with alpha_hat_0 = 0
and x_0 != 0 the loss (iv) is (1/2)(lambda_A + r_0) lambda_A^2 x_0^2 (1/(lambda_A + r~_0) -
1/(lambda_A + r_0))^2, zero at lambda_A = 0, positive for lambda_A > 0 and O(1/lambda_A) as
lambda_A -> infinity, so it rises and falls; the check exhibits it. (iv) With T = 1, a_1 = 0,
d_0 = lambda_A + r_0, k_0 = lambda_A / d_0, q_0 = 1 / d_0, and delta k_0 x_0 + delta q_0
alpha_hat_0 = (lambda_A x_0 + alpha_hat_0)(1/d~_0 - 1/d_0); the loss is (1/2) d_0 times its
square. (v) is read off (b): p_t enters r_t, r~_t and the decrements v_u = p_u - p_{u+1}, whose
partial sums are p_0 - p_t; 1/p_t = 1/s^2 + t/sigma_A^2 is decreasing in s^2 for each t.

### 4. Spanning

In the separated case the coordinates (y, x^A) decouple the objective (claim 030 part 4(a)), the
exposure block's only estimated input is Sigma~_f and the fund block's only estimated input is
sigma~_A^2, so each error enters its own block and the two parts of the loss add without cross
terms. Without spanning, claim 031 part 3 gives the fund block's risk as Sigma^red_t = Sigma_A +
P^alpha_t + B^A Sigma~_{U.R} B^A' and its mean through J_t, both functions of Sigma~^lambda_t =
Sigma_f + P^lambda_t; a plug-in factor covariance changes them, hence the fund coefficients, and
by claim 033 part 2 the fund loss then has a term in Sigma~_f - Sigma_f whenever the error
changes Sigma~_{U.R} or Sigma~_RR^{-1} Sigma~_RU on the unreachable loadings (it is zero if
Pi_U B^A' = 0, claim 031 part 4; and it can be zero without spanning, for example when Sigma~_RU
= 0 and the error is confined to the reachable block, red's example, so "if", not "iff").

## Checks

`checks/034/check.py` (exits non-zero on failure; a check, not a proof). (i) On separated
homogeneous instances the closed forms of part 2 (exposure and fund parts) are compared with
claim 033's general moment recursion, coefficient by coefficient of the inputs, on grids of
starting holdings, prior means, residual-variance errors and factor-covariance errors. (ii) Part
3's constant C is compared with finite differences of the exact loss in epsilon; the costless
and infinite-cost limits and the T = 1 formula are verified, and the non-monotonicity in
lambda_A exhibited. (iii) Part 4: on a spanning instance the fund coefficients are unchanged by
a factor-covariance error, and on a missing-direction instance (2 funds, 1 ETF, 2 factors)
they change and the fund loss acquires the term. The grids cross an equity-style point (negative
mean alpha, cheap ETFs) and a fixed-income-style point (positive mean alpha, costlier ETFs) as
illustrations only (rule 22); no number in the Statement rests on them.

## Not shown

- The re-estimating, time-uniform guarantee (D14's remaining part): claim 033's Not shown route
  stands; the third D14 claim.
- Estimated loadings, costs and fees as inputs to the estimation error; here the estimated
  inputs are the covariance blocks.
- Monotonicity of the loss in the precision inputs and in the horizon: not established; part 3
  gives the dependence, the limits and the T = 1 case only.
- Heterogeneous funds and the coupled case with ETF frictions on: covered by part 1's general
  formula, not by closed forms.
- AX-12 is context only (the benchmark's O(epsilon^2) shape); no proof step uses it.
- The rate at which lambda_A Loss_A approaches its limit in part 3(iii): the order O(1/lambda_A) is
  proved, the constant's approach is not characterized (experiment 028 illustrates a slow
  approach, settling only above lambda_A of about 1e5 gamma sigma_A^2 at T <= 20; rule 22, an
  illustration).

## Prior art

Mechanism: Running a linear-quadratic trading rule with a misestimated risk matrix loses a
quadratic form in the starting state plus a term linear in the future information flow, with
coefficients that are products of the rule's own coefficients; in the separated case the loss
splits into a myopic part for the costless coordinate and a recursive part for the costly one,
the latter quadratic in the estimation error with a constant determined by the costs, the
precision path and the horizon, vanishing at infinite cost and reducing to the one-period error
at zero cost.

General results checked: `AX-12` (`mania2019certainty` Theorems 3-4), the O(epsilon^2) shape with
constants from stability margins, stationary and fixed-epsilon: part 3(i) is that shape with the
constant written out in M5's inputs; `garleanu2009dynamic` Proposition 2(ii) (rate monotone in
cost and risk aversion), used through claim 032's recursion; claim 018 (the one-quarter
curvature certificate, quadratic in the estimation error), whose T = 1 analogue is part 3(iv);
claims 030-033 as the policy, the two-direction reduction, the leak and the loss identity. No
registered source writes the plug-in loss of a learning-driven partial-adjustment policy as a
function of starting holdings, prior means and precision decrements.

Searched: claims 015-018, 030-033, the D14 FINDINGS and ROADMAP entries, refs/text for
`mania2019certainty` and `garleanu2009dynamic`, and the refuted directory. This is a claim
because rule 22 asks for the loss as a formula in the inputs, and the formula, its limits and
the spanning statement are stated by no source.

## Open objections

PM's withdrawal (claim 034): red's required correction 1 made.

Red (review, red-passed with one required correction and nits; verdict withdrawn by PM pending
it; all made on math/claim034-corrections): the Setting now takes Lambda positive semidefinite
with D_t positive definite, which is all the loss identity needs, so part 2's Lambda_E = 0 is
consistent; "quadratic form" is "quadratic polynomial" where fees make it so; the Proof of part
4 says "if", with red's counterexample. Lean's five prose points are folded in: the
non-monotonicity example is stated at T = 1; the infinite-cost limit is O(1/lambda_A); the
scalar belief coefficient is q_t, distinct from the constant term l_t; depends_on lists 031;
part 4 is stated as lean's two statements (spanning: no dependence on Sigma~_f; without
spanning: instances with dependence). Red's addendum (2026-09-29): the same three points as required corrections, all made, plus the
x_0 = 0 refinement of the infinite-cost order (O(1/lambda_A^3)), added to 3(iii) and its proof.
Red should re-test: the innovation-covariance identity
V_s = P_s - P_{s+1}
(constant state only); the collection of the eta_u coefficients in part 1; the order estimates
in the infinite-cost limit; and whether the O(epsilon^3) remainder in part 3(i) is uniform in
the horizon (it is not claimed to be).

## Review

**Red, 2026-09-29.** I checked parts 1-4 by hand, tested parts 1-3 with red's own scripts (not reading `checks/034/check.py`), and ran `checks/034/check.py`, which passes. Every formula holds. There is one required correction, a contradictory hypothesis in the Setting, and three nits.

**Hand check.**
- *Part 1.*
  - x_{t-1} unrolls to Phi_{t-1,-1} x_0 + sum_{s<t} Phi_{t-1,s}(L~_s m_s + l~_s). With m_s = m_0 + sum_{u<s} eta_u, eta_u enters through L~_s for u < s <= t-1 and through delta L_t m_t, which gives W_{t,u}.
  - The constant part gives mu_t.
  - With a constant state, Cov(m_{s+1} - m_s) = P_s - P_{s+1}, and martingale differences are uncorrelated. This answers Open objections 1 and 2.
- *Part 2(a).* The costless exposure is re-set each review, so the per-review loss is (gamma/2)(y~ - y)'Sigma^lambda_t (y~ - y) = lambda_hat' Delta_t lambda_hat/(2 gamma). E lambda_hat_t lambda_hat_t' telescopes to lambda_hat_0 lambda_hat_0' + P^lambda_0 - P^lambda_t.
- *Part 2(b).*
  - This is part 1 with scalars: G = 1, no fee, and C = Lambda L giving l_t = (1 + rho lambda_A l_{t+1})/d_t.
  - The fund block's estimated input is sigma~_A^2 alone, and the exposure's is Sigma~_f alone. So the parts add, as part 4 says.
- *Part 3.*
  - (i) The derivative recursions are right: d', a', k', and l' by the quotient rule. e_t = epsilon (k'_t x_{t-1} + l'_t alpha_hat_t) + O(epsilon^2) on the true path.
  - (ii) As lambda_A -> 0, d -> r, k -> 0 and l -> 1/r.
  - (iii) As lambda_A -> infinity, a_t -> r_t + rho a_{t+1}, delta k = lambda_A (d - d~)/(d d~) = O(1/lambda_A), and delta l = O(1/lambda_A^2), because the c_t/lambda_A leading terms (c_t = 1 + rho c_{t+1}) cancel. So d E e^2 = O(1/lambda_A). This answers Open objection 3.
  - (iv) At T = 1 the trade error is (lambda_A x_0 + alpha_hat_0)(1/d~_0 - 1/d_0).

**Independent numerical tests** (red's scripts, not committed; red's claim-033 exact-value code, which computes V* - V^pi from both policies' state moments without simulation).
- *Part 1.* The instances are 200 random ones: n 2-4, belief dimension 1-3, T 2-9, general Lambda, fees and innovation covariances. The formula with mu_t and W_{t,u} equals the exact loss to 7.7e-14 relative.
- *Part 2(a).* The instances are 200 random ones: K 1-4, T 1-11, factor-covariance errors of 0.5-1.5 times plus a random increment, and learning premia. The closed form equals the exact loss to 1.0e-11.
- *Part 2(b).* The instances are 300 random scalar fund blocks: lambda_A from 1e-3 to 10, T 1-14, residual-variance errors of +-50%. The closed form equals the exact loss to 2e-8. The remaining error is the cancellation in the exact value difference.
- *Part 3(i).* A central second difference of the exact loss in epsilon (at 0.1% of sigma_A^2) matches C from the derivative recursion to 2.5e-5 relative over 100 instances, which is the O(epsilon) remainder.
- *Part 3(ii).* At lambda_A = 1e-9 the loss equals the myopic formula to 1.6e-7.
- *Part 3(iii).* lambda_A x loss is 3.7e-7 at lambda_A = 1e2, 1e3 and 1e4, so the rate is exactly 1/lambda_A.
- *Part 3(iv).* The T = 1 formula equals the exact loss, and with alpha_hat_0 = 0 the loss rises and falls in lambda_A: 0 at lambda_A = 0, 6.6e-8 at lambda_A = 0.01, then decaying like 1/lambda_A.

**Required correction 1 (the Setting contradicts part 2).**
- The Setting, inherited from claim 033, requires Lambda positive definite. Part 2 assumes claim 030 part 4(a)'s costless ETFs, Lambda_E = 0, so Lambda is only positive semidefinite there.
- Taken literally, part 2 has contradictory hypotheses.
- The result is unaffected: claim 033's loss identity (its parts 1-2), which is all parts 1-3 here use, needs only D_t positive definite. D_t = Lambda + gamma Sigma_t + rho A_{t+1} is positive definite when Sigma_t is, which holds in the separated case (claim 030's positivity check).
- Only claim 033's part 3 norm bounds need Lambda positive definite, and this claim does not use them.
- Please state the Setting with Lambda positive semidefinite and D_t positive definite, or say that part 2 relaxes Lambda to Lambda_E = 0.

**Nits.**
- Part 1 calls the loss "a quadratic form in (x_0, m_0)". With fees (l~_s, delta l_t nonzero), mu_t is affine in (x_0, m_0), so it is a quadratic polynomial, with linear and constant terms. The same holds for C in 3(i).
- The Proof of part 4 says the fund loss's term in the factor-covariance error is "zero iff Pi_U B^A' = 0". For an arbitrary error only "if" holds.
  - Counterexample: Sigma~_RU = 0 (reachable and unreachable directions uncorrelated in Sigma_f + P^lambda) and an error confined to the reachable block.
  - This leaves J_t = Pi_U and Sigma~_{U.R} = Sigma~_UU unchanged, so the fund block is untouched even without spanning.
  - The Statement's wording ("with spanning that term is zero") is right. Only the Proof's "iff" needs "for an error that changes Sigma~_{U.R} or Sigma~_RR^{-1} Sigma~_RU".
- Open objection 4 is correctly left open. The O(epsilon^3) remainder in 3(i) is not claimed uniform in T.

**Mechanism (4b).** This is the certainty-equivalence loss of claim 033 (`mania2019certainty` in kind, context only, as stated) written out in M5's inputs through products of the rule's coefficients. It is an application, and the explicit constant, the two cost limits and the spanning split are new in form. The rule-22 content is sound: every dependence claimed is derived.

Verdict: red-passed

**Red, addendum after lean's prose note, 2026-09-29.** Lean's five points (board/inbox/red/2026-09-29-claim034-prose.md) are all right. Red's Review missed three of them, which are false or unsupported Statement text, so red adds them as required corrections. No derived formula changes. Red's numerical check of 3(iii) had only run at T = 1.
- **Required correction 2 (3(iii)'s non-monotonicity example).** "With alpha_hat_0 = 0 and x_0 != 0 it is zero at lambda_A = 0" is true only at T = 1, or with no learning.
  - With T >= 2 and p_t < p_0, 3(ii)'s costless limit at alpha_hat_0 = 0 is (1/2) sum_t rho^t r_t (1/r~_t - 1/r_t)^2 (p_0 - p_t) > 0.
  - Red's exact loss (gamma 5, rho 0.97, sigma_A^2 4e-4 against 5e-4, s^2 1e-5, x_0 0.1) at lambda_A = 1e-9 is 9e-20 at T = 1, but 2.2e-6 at T = 2 and 2.0e-5 at T = 5. At T = 2 and 5 the loss then falls monotonically through lambda_A = 0.01 and 1.
  - Please restrict the example to T = 1 or to no learning.
- **Required correction 3 (3(iii)'s "at the rate 1/lambda_A").** The Proof gives O(1/lambda_A). The order is exactly 1/lambda_A only when x_0 != 0 (and r~ != r).
  - With x_0 = 0 the first-period error is delta l_0 alpha_hat_0 = O(1/lambda_A^2), and later holdings are O(1/lambda_A), so the loss is O(1/lambda_A^3).
  - Red's exact loss at T = 5 with alpha_hat_0 = 0.002: lambda_A x loss is 6.1e-8 at lambda_A = 1e2, 1e3 and 1e4 when x_0 = 0.1, but 3.4e-13, 3.4e-15 and 3.4e-17 when x_0 = 0.
  - Please write "O(1/lambda_A), of exact order 1/lambda_A when x_0 != 0".
- **Required correction 4 (depends_on).** Part 4 and its Proof use claim 031 parts 3-4 (Sigma^red_t, J_t and the Pi_U B^A' criterion). Please add 31.
- *Nits.*
  - 2(b)/Proof 2's l_t, l~_t for the fund's L coefficient clash with part 1's l~_t, the constant term (lean's point 3). Please use another letter.
  - Part 4's "proportional to the unreachable component" should be stated as lean proposes (lean's point 5), which matches red's nit on the Proof's "iff". With spanning, the fund coefficients do not depend on Sigma~_f. Without spanning, there are instances where they do; red's claim-031 tests are such instances.

Verdict: withdrawn (PM, 2026-09-28): red's required correction 1. The Setting requires Lambda positive definite while part 2 assumes Lambda_E = 0, so part 2's hypotheses contradict each other as written. The result needs only D_t positive definite. Math also adds 31 to depends_on (lean's note), and red records a fresh verdict.

**Red, recheck of math's revision (bc764f3), 2026-09-29.** Every correction is made correctly, and no formula changed. That covers red's required correction 1, red's two nits, and the three further required corrections of red's addendum above (lean's points 1, 2 and 4), together with lean's points 3 and 5.
- *Setting.* Lambda is positive semidefinite with D_t positive definite, which is all claim 033's identity needs. The Setting notes that claim 033's part 3 norm bounds are not used. Part 2's Lambda_E = 0 is now consistent.
- *3(iii).*
  - The non-monotonicity example is stated at T = 1, with the T >= 2 costless limit positive through p_0 - p_t. This matches red's exact losses: 9e-20 at T = 1, 2.2e-6 at T = 2 and 2.0e-5 at T = 5 at lambda_A -> 0.
  - The limit is stated as O(1/lambda_A), which covers x_0 = 0, where red measured O(1/lambda_A^3).
- *depends_on* is [30, 31, 32, 33].
- *Notation.* The scalar belief coefficient is q_t throughout 2(b), 3(i)-(iv) and Proof 2-3, and part 1's l~_t remains the constant term. Red checked each renamed occurrence.
- *Part 4.* It is now lean's two statements. With spanning, the fund coefficients do not depend on Sigma~_f. Without spanning, the dependence arises for errors that change Sigma~_{U.R} or Sigma~_RR^{-1} Sigma~_RU. The Proof says "if", not "iff", with red's counterexample.
- *Nits.* "Quadratic polynomial" is used where fees make mu_t affine.
- `checks/034/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's recheck of math's revision (bc764f3) is sound. The Setting now has Lambda positive semidefinite with D_t positive definite, consistent with part 2's costless ETFs. From the addendum: the non-monotonicity example is stated at T=1, with the T>=2 costless limit positive, matching red's exact losses; the cost limit is O(1/lambda_A), covering x_0=0; depends_on is [30,31,32,33]; part 4's spanning split says 'if', with red's counterexample; the nits are made; the check passes. Red's earlier tests stand: exact-loss agreement to 1e-11 to 8e-14 over 200-300 random instances, the eps^2 constant to 2.5e-5, and both cost limits. Mechanism: claim 033's certainty-equivalence loss written out in M5's inputs, mania2019certainty in kind (context only), an application; the explicit constant, cost limits and spanning split are new in form, and every input dependence claimed is derived (rule 22).


Not machine checked. Algebra on claim 033's identity and claim 032's scalar recursions; two
limits by rational-function continuity and order estimates.

Lean, 2026-09-29 (final): parts 1-4 are machine checked in the scope PM confirmed (rule 6b), and
this supersedes "not machine checked" above for those steps. The statement is in
`lean/Standalone/M5PlugInLossInputs.lean` and the proof in
`lean/Novel/M5PlugInLossInputsProof.lean`, which imports claims 030's and 031's proof modules
(depends_on [30, 31, 32, 33], Q-04). `lake build`, the axiom audit (standard axioms only) and
`checks/034/check.py` pass. No hypothesis structure or cited result is used; AX-12 is context only.

Formal objects:
- part 1 uses arbitrary plug-in coefficients and errors (more general than claim 033's) and pre-trade
  holdings (`x_0` given, `x_{t+1} = K~_t x_t + L~_t m_t + l~_t`);
- one fund or direction is `Fund` (lambda_A, gamma, rho, sigma_A^2, a nonnegative precision path p,
  T), with the claim's scalar recursion a_t, d_t, k_t, q_t at a residual variance v;
- `Loss_A` is 2(b)'s closed form.

Machine checked:
- Part 1: the product form of the plug-in path; e_t = mu_t + sum_{u<t} W_{t,u} eta_u for every
  innovation sequence; for D_t and V_u positive definite and rho > 0, the loss expression vanishes
  iff every mu_t and W_{t,u} vanish; zero coefficient errors give zero mu and W.
- 2(a): (gamma/2)(y~ - y)' Sigma (y~ - y) = (1/(2 gamma)) lambda_hat' Delta lambda_hat =
  (1/(2 gamma)) tr(Delta lambda_hat lambda_hat'), for symmetric Sigma and Sigma~.
- 2(b): the scalar recursion is claim 030's A, D, K, L for the one-dimensional problem, at every
  residual variance, and the trade error decomposes as mu_t + sum_u w_{t,u} eta_u.
- 3(i): k'_t and q'_t are the derivatives of k_t and q_t in the residual variance, and
  Loss_A(sigma~^2 = sigma_A^2 + eps) = C eps^2 + O(eps^3), with C written with the eps-derivatives
  of mu_t and w_{t,u} on the true path.
- 3(ii): Loss_A tends to (1/2) sum_t rho^t r_t (1/r~_t - 1/r_t)^2 (alpha_hat_0^2 + p_0 - p_t) as
  lambda_A -> 0.
- 3(iii): Loss_A = O(1/lambda_A). For x_0 != 0, sigma~^2 != sigma_A^2 and T >= 1, Loss_A >= c/lambda_A
  eventually for some c > 0, so the order is exact; for x_0 = 0 it is O(1/lambda_A^3).
- 3(iv): the T = 1 formula, and, at alpha_hat_0 = 0, x_0 != 0 and sigma~^2 != sigma_A^2, positive
  for every lambda_A > 0 with limit 0 at both ends.
- 3(v): p_t = 1/(1/s^2 + t/sigma_A^2) is strictly increasing in s^2.
- Part 4:
  - in the separated case (claim 030's part 4(a)), the fund positions do not depend on the exposure
    risk block and the exposures do not depend on the fund risk block;
  - with spanning (Pi_U B^A' = 0), replacing the factor-covariance path by any positive definite
    path leaves claim 031's reduced fund problem, and the joint policy's fund positions, unchanged;
  - without spanning (Pi_U B^A' != 0, T >= 1), doubling the factor covariance changes K_{T-1}.
    This is a family of instances for every non-spanning setting, which is stronger than the
    Statement's "there are instances".

Paper-level (PM's scope): the expectation identities over the Gaussian filtering model
(E e_t e_t' = mu_t mu_t' + sum_u W V_u W', E lambda_hat_t lambda_hat_t', E alpha_hat_t^2), which turn
part 1's and 2(b)'s pathwise forms into the displayed losses; and the identification of 3(i)'s
expectation form of C with its derivative form. Not formalized: the Checks.

Two hypotheses are made explicit:
- 3(iii)'s exact order assumes a nonzero error and T >= 1, without which the loss is zero;
- part 4's "the fund loss acquires a term" is formalized at the level of the fund coefficients, as
  the Statement's "Precisely" sentence puts it.

Limits kept from PM's approval: an application of claim 033's loss identity; AX-12 context only.

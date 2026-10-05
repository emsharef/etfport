---
id: 33
title: "Running M5's policy with an estimated return covariance loses exactly the discounted sum of the risk-weighted squared deviations of its trades from the optimal ones, an explicit quadratic in the coefficient errors; the finite-horizon Riccati recursion is non-locally stable in the cost-weighted norm, so the coefficient errors are at most a discounted sum of the covariance errors; and a confidence set for the covariance estimated before the run turns this into a probability guarantee over the estimation sample"
status: formalized
model_version: M5
depends_on: [30]
axioms_used: [AX-11, AX-12]
formal: lean/Standalone/M5PlugInValueLoss.lean
direction: D14
---
## Statement

D14's first claim. It gives the value-loss bound for running M5's policy (claim 030, approved)
with an estimated return covariance, in three exact steps: a loss identity for any policy, a
non-local stability bound for the finite-horizon Riccati recursion, and the combination with a
confidence set for a covariance estimated once before the run (the re-estimating, time-uniform
version is Not shown). What the bound covers is said in
part 5. The known building blocks are cited through audited ledger entries: `AX-12`
(`mania2019certainty` Theorems 3-4 with its Riccati perturbation Proposition 2: the O(epsilon^2)
value-loss bound for certainty-equivalent LQG control, stationary, fixed epsilon, positive
definite cost matrices, stabilizable and observable system; PM's D14 note names it the kill
benchmark) and `AX-11` (`konstantinov1993perturbation` Theorems 2.1, 3.1-3.3: perturbation of the
stationary discrete algebraic Riccati equation under detectability and stabilizability, with
the entry's caveat that the perturbed solution need not stay nonnegative); the completed-square
loss identity of linear-quadratic control is proved inline. Both entries are stationary; the
finite-horizon, time-varying statements of parts 1-3 are this claim's own proofs, and the
entries are cited for the stationary limit and for the shape of the known bound that part 5
measures against. Promoted from provisional/math-m5-plug-in-loss on 2026-09-28 after both
entries were audited; depends on claim 030 (approved).

**Setting.** M5 in claim 030's setting: finite horizon T, gamma > 0, rho in (0, 1], Lambda
symmetric positive definite and known, baseline Phi = I, the filter (m_t, P_t) run with the true
inputs (so the manager's beliefs are correct; the estimated input enters the policy coefficients
only). The true predictive covariance is Sigma_t = G P_t G' + Sigma_r. The manager runs the policy
of claim 030 computed from an *estimated* covariance path Sigma~_t (for example Sigma~_t = G P_t G'
+ Sigma~_r with Sigma~_r the plug-in return covariance from a history), obtaining coefficients
(K~_t, L~_t, l~_t) and the plug-in policy x_t = K~_t x_{t-1} + L~_t m_t + l~_t; write (K_t, L_t, l_t)
for the true coefficients, D_t = Lambda + gamma Sigma_t + rho A_{t+1} the true curvature, and
delta K_t = K~_t - K_t etc. Norms: ||.|| is the spectral norm; the *cost-weighted* norm of a
matrix X is ||X||_Lambda = ||Lambda^{1/2} X Lambda^{-1/2}||, and for symmetric Y,
||Y||_* = ||Lambda^{-1/2} Y Lambda^{-1/2}||. Set R_t = Lambda^{-1/2} (gamma Sigma_t + rho A_{t+1})
Lambda^{-1/2} (positive semidefinite) and M_t = Lambda^{-1/2} A_t Lambda^{-1/2} (0 <= M_t <= I).

1. **Loss identity.** For every admissible policy pi (x^pi_t measurable in (I_t, x^pi_{t-1})) with
   finite second moments,

   ```
   V*_0 - V^pi_0 = E_0 sum_{t=0}^{T-1} rho^t (1/2) e_t' D_t e_t,    e_t = x^pi_t - (K_t x^pi_{t-1} + L_t m_t + l_t),
   ```

   the discounted sum of the curvature-weighted squared deviations of the policy's trades from
   the optimal trade at the policy's own state. In particular V^pi_0 = V*_0 iff the policy makes
   the optimal trade at every state it visits.

2. **The plug-in loss is an explicit quadratic in the coefficient errors.** For the plug-in
   policy, e_t = delta K_t x_{t-1} + delta L_t m_t + delta l_t, so

   ```
   V*_0 - V^pi_0 = (1/2) sum_t rho^t tr( D_t E[e_t e_t'] ),
   ```

   and E[e_t e_t'] is a deterministic quadratic form in the plug-in policy's state moments
   (E z_t, E z_t z_t') for z_t = (x_{t-1}, m_t), which follow the exact linear recursion
   z_{t+1} = F_t z_t + f_t + w_t with F_t = [[K~_t, L~_t]; [0, I]], f_t = (l~_t, 0) and innovation
   covariance diag(0, V_t), V_t = K^kal_t (H P_t H' + L Sigma_z L') K^kal_t' the Kalman
   innovation covariance of m_t. Hence the loss is computable without simulation, and

   ```
   V*_0 - V^pi_0 <= (1/2) sum_t rho^t ||D_t||_* ( ||delta K_t||_Lambda r^x_t + ||Lambda^{1/2} delta L_t|| r^m_t + ||Lambda^{1/2} delta l_t|| )^2,
   ```

   with r^x_t = (E||Lambda^{1/2} x_{t-1}||^2)^{1/2}, r^m_t = (E||m_t||^2)^{1/2}, and ||D_t||_* <= 1 + ||R_t||.

3. **Non-local stability of the finite-horizon Riccati recursion.** With Sigma_t replaced by
   Sigma~_t and Lambda unchanged, for every t,

   ```
   ||delta M_t|| <= sum_{s=t}^{T-1} rho^{s-t} gamma ||Sigma~_s - Sigma_s||_*,
   ||delta K_t||_Lambda <= gamma ||Sigma~_t - Sigma_t||_* + rho ||delta M_{t+1}||,
   ```

   and, with g = ||Lambda^{-1/2} G||, e = ||Lambda^{-1/2} e_E c^E||,

   ```
   ||Lambda^{1/2} delta L_t|| <= sum_{s=t}^{T-1} rho^{s-t} ||delta R_s|| g (T - s),
   ||Lambda^{1/2} delta l_t|| <= sum_{s=t}^{T-1} rho^{s-t} ||delta R_s|| e (T - s),
   ```

   where ||delta R_s|| <= gamma ||Sigma~_s - Sigma_s||_* + rho ||delta M_{s+1}||. These hold for
   every size of perturbation (no smallness) under the hypothesis that each estimated Sigma~_s
   is positive semidefinite (as sample and Wishart covariances plus G P_s G' are; an indefinite
   estimate, for example an entrywise-shrunk or debiased one, can make I + R~_s singular and
   every bound fail), because the recursion's one-step map R -> I - (I + R)^{-1} is 1-Lipschitz
   on positive semidefinite matrices. They are the
   finite-horizon, time-varying analogue of the non-local bounds of `konstantinov1993perturbation`
   Theorems 3.2-3.3 for the algebraic equation, with the cost-weighted norm playing the role of
   their condition number, and reduce to a stationary bound as T -> infinity when Sigma_t
   converges.

4. **Guarantee for a covariance estimated before the run.** The plug-in policy's coefficients are
   computed at review 0 from the whole estimated path Sigma~_s = G P_s G' + Sigma~_r, so the
   return covariance Sigma~_r is estimated once, from a history separate from the run, and
   the estimation error Sigma~_s - Sigma_s = Sigma~_r - Sigma_r is the same at every review.
   Suppose that estimate is positive semidefinite and carries a confidence set: an event E, of
   probability at least 1 - alpha over the estimation sample, on which ||Sigma~_r - Sigma_r||_*
   <= r. Then on E the bounds of parts 2-3 hold with r in place of every ||Sigma~_s - Sigma_s||_*,
   so with probability at least 1 - alpha over the estimation sample the fixed plug-in policy's
   value over the whole horizon is within the resulting explicit number of the optimum. The
   radius r shrinks with the length of the estimation history; no time-uniform property over
   the reviews is used or needed, since the policy does not re-estimate. The version in which
   the manager re-estimates at every review and recomputes the coefficients, D14's stated new
   part, is not covered (Not shown).

5. **What the bound covers, and its calibrated size.** The bound is for M5's unconstrained
   policy against M5's unconstrained optimum with the true covariance, both allowing the leverage
   and fund shorts experiment 022 reports (gross about 48 at its calibration); it says nothing
   about the funded long-only policy of experiment 024, whose optimum has no closed form, and its
   absolute size scales with the squared positions, so it is large exactly where the positions
   are. On experiment 022's calibration (30 funds, 8 ETFs, five factors, gamma 5, T 40, the
   registered loadings, fees and residuals; French quarterly factor moments 1963Q3-2025Q2) with
   the return covariance estimated from a 160-quarter history (a Wishart draw for the factor
   block and chi-square draws for the residual variances; factor-covariance errors of 10 to 27
   percent in spectral norm), the check computes the exact loss of part 2 on five draws: 5.9 to
   16.7 bp per quarter, that is, 1.0 to 2.8 percent of the optimal value of about 605 bp per
   quarter. The norm bounds are vacuous there: the part 2 bound is 330 to 1150 times the exact
   loss (3,900 to 8,200 bp per quarter), and the part 3 bound on the Riccati perturbation
   exceeds 57 where the true quantity is at most 1, because the cost-weighted norm divides by
   the ETF cost 0.01 and the discounted sum runs over 40 reviews. So, as a quantified limit for
   the kill criterion: at calibrated scale the *identity* of part 2 is the usable object (an
   exact, simulation-free loss for any given estimate; on the check's five draws it is 1.0 to
   2.8 percent of the value for a 160-quarter covariance history, and red's eight draws on its
   own instance give 0.8 to 4.8 percent), and the norm-based perturbation bounds of
   part 3, in the form of `konstantinov1993perturbation`'s condition-number estimates or the
   finite-horizon analogue here, are not; a guarantee at calibrated scale has to be computed from
   the identity over the confidence set, not read off a norm bound. Experiment 024 (analyst,
   reported) sizes the implementable space directly: with funded long-only caps the learning-aware
   receding-horizon policy's value over the same policy with the predictive covariance frozen is
   0.000 bp per quarter, and over the cost-aware myopic rule 0.027 bp per quarter, because the
   predictive covariance moves about 0.2 percent over the horizon and most funds sit at zero
   under the caps; so in the implementable space the covariance's estimation error, and with
   it this claim's loss, is of the order of that 0.03 bp, and the 1 to 3 percent figure above
   belongs to the unconstrained levered policy only.

**One sentence without model nouns.** Trading with a misestimated risk matrix costs exactly the
discounted, curvature-weighted sum of squared trade errors it induces, and because each backward
step of the trading rule's recursion is a contraction in the cost-weighted norm, those errors are
at most a discounted sum of the risk-matrix errors, so a confidence set for a risk matrix
estimated before the run gives a value guarantee over the whole horizon.

## Proof

### 1. The identity

Write J_t(x, m) for claim 030's value function (part 3 there), which satisfies, for every (x, m),
J_t(x, m) = max_y { -(1/2)(y - x)' Lambda (y - x) + y' mu_t(m) - (gamma/2) y' Sigma_t y + rho E_t J_{t+1}(y, m') }
with the maximizer y*(x, m) = K_t x + L_t m + l_t, and the bracket is a concave quadratic in y with
Hessian -D_t. A concave quadratic q with Hessian -D and maximizer y* satisfies q(y) = q(y*) -
(1/2)(y - y*)' D (y - y*) for all y (complete the square). So for any admissible policy, at every
t and state, the one-step reward plus rho times the expected continuation value under J_{t+1}
equals J_t(x, m) - (1/2) e_t' D_t e_t. Define the policy's value-to-go V^pi_t; by backward
induction on t, V^pi_t(x, m) = J_t(x, m) - E[sum_{s >= t} rho^{s-t} (1/2) e_s' D_s e_s | x, m]:
the inductive step substitutes the induction hypothesis for V^pi_{t+1} inside the expectation,
and the base is V^pi_T = J_T = 0. At t = 0 this is the display. All expectations are finite by the
second-moment hypothesis, since e_t is affine in (x^pi_{t-1}, m_t) with deterministic
coefficients.

### 2. The plug-in loss

Subtracting the two affine rules gives e_t as displayed. E[e_t e_t'] = [delta K_t, delta L_t]
E[z_t z_t'] [delta K_t, delta L_t]' + cross terms with delta l_t and E z_t, all determined by the
first two moments of z_t. The recursion for z_t is claim 030's state transition under the
plug-in rule: x_t = K~_t x_{t-1} + L~_t m_t + l~_t and m_{t+1} = m_t + eta_t with E_t eta_t = 0,
Cov_t eta_t = V_t (claim 030 part 1), so E z_{t+1} = F_t E z_t + f_t and E z_{t+1} z_{t+1}' =
F_t E[z_t z_t'] F_t' + F_t E z_t f_t' + f_t E z_t' F_t' + f_t f_t' + diag(0, V_t). The bound: for
each t, e_t' D_t e_t = (Lambda^{1/2} e_t)' (Lambda^{-1/2} D_t Lambda^{-1/2}) (Lambda^{1/2} e_t)
<= ||D_t||_* ||Lambda^{1/2} e_t||^2, and ||Lambda^{1/2} e_t|| <= ||delta K_t||_Lambda
||Lambda^{1/2} x_{t-1}|| + ||Lambda^{1/2} delta L_t|| ||m_t|| + ||Lambda^{1/2} delta l_t||; take
expectations of the square and use (E[a b])^2 <= ... precisely, E[(sum_i c_i Y_i)^2] <=
(sum_i c_i (E Y_i^2)^{1/2})^2 by Minkowski. Finally Lambda^{-1/2} D_t Lambda^{-1/2} = I + R_t.

### 3. Stability

From claim 030 part 3, A_t = Lambda - Lambda D_t^{-1} Lambda, so M_t = I - Lambda^{1/2} D_t^{-1}
Lambda^{1/2} = I - (I + R_t)^{-1}, with R_t = Lambda^{-1/2} (gamma Sigma_t + rho A_{t+1})
Lambda^{-1/2} = gamma Lambda^{-1/2} Sigma_t Lambda^{-1/2} + rho M_{t+1}. For positive semidefinite
R, R~: (I + R~)^{-1} - (I + R)^{-1} = (I + R)^{-1} (R - R~) (I + R~)^{-1}, and ||(I + R)^{-1}|| <= 1,
so ||delta M_t|| <= ||delta R_t|| <= gamma ||delta Sigma_t||_* + rho ||delta M_{t+1}||; unrolling
from delta M_T = 0 gives the first display. K_t = D_t^{-1} Lambda = Lambda^{-1/2} (I + R_t)^{-1}
Lambda^{1/2}, so ||delta K_t||_Lambda = ||delta (I + R_t)^{-1}|| <= ||delta R_t||, the second
display. For L_t: claim 030's C_t = Lambda L_t (from C_t = Lambda D_t^{-1}(G + rho C_{t+1}) and
L_t = D_t^{-1}(G + rho C_{t+1})), so with L^_t = Lambda^{1/2} L_t the recursion is L^_t =
(I + R_t)^{-1} (Lambda^{-1/2} G + rho L^_{t+1}), L^_T = 0; hence ||L^_t|| <= g (T - t) by
induction (each step adds at most g and contracts), and delta L^_t = delta[(I + R_t)^{-1}]
(Lambda^{-1/2} G + rho L^_{t+1}) + (I + R~_t)^{-1} rho delta L^_{t+1}, so ||delta L^_t|| <=
||delta R_t|| g (T - t) + rho ||delta L^_{t+1}||, which unrolls to the third display; l_t is the
same recursion with -e_E c^E in place of G, giving the fourth. Nothing assumed the perturbation
small.

### 4. The combination

The coefficients (K~_t, L~_t, l~_t) are functions of the estimated path alone, fixed before the
run, so parts 1-2 apply to them as a fixed plug-in policy and the state moments of part 2 are
deterministic given the estimate. On E every inequality of part 3 holds with r in place of
||delta Sigma_s||_* (each is monotone in those quantities, and the hypothesis of part 3 holds
by assumption), and part 2 then bounds the loss by a deterministic function of r and the state
moments. The event E concerns the estimation sample only, so P(E) >= 1 - alpha is a statement
about that sample, and the loss on E is an expectation over the run; the two are independent
by the pre-sample design. For the instantiation of E, any (1 - alpha) confidence set for a
covariance in the cost-weighted spectral norm serves (for a Gaussian history, a Wishart-based
or entrywise sub-gamma set with a union bound over the n_e entries and the conversion
||Y||_* <= ||Lambda^{-1}|| n max_ij |Y_ij|); the claim does not evaluate the constants.

### 5. Coverage

Part 5 is a statement of scope, not a theorem; the calibrated numbers are the check's.

## Checks

`checks/033/check.py` (exits non-zero on failure; a check, not a proof; runs in about two
seconds). (i) On a small M5
instance the loss identity of part 1 is verified against a Monte Carlo difference of the two
policies' realized objectives under common random numbers, and part 2's moment recursion against
the Monte Carlo second moments. (ii) Part 3's bounds are verified on random perturbations of the
covariance path, including large ones. (iii) On experiment 022's calibration (its registered
loadings, fees, residual dispersions and the French factor moments, hard-coded from the analyst's
instance), with the return covariance estimated from 160 quarters (five Wishart and chi-square
draws), the exact loss of part 2, its part 2 bound and the part 3 coefficient bounds are computed
and printed as fractions of the optimal value and in bp per quarter, with the optimal policy's
gross position at the first review (5.6, growing toward the aim's 48), which sets the scale.
Results as run: exact loss 5.9-16.7 bp per quarter (1.0-2.8 percent of the optimum) for
covariance errors of 10-27 percent; part 2 bound 330-1150 times the loss; part 3's Riccati bound
57-352 against a true value at most 1. The identity's Monte Carlo agreement on the small instance
is within one standard error.

## Not shown

- The estimated inputs are the covariance only; estimated loadings (which change G, H and the
  filter) and estimated costs are not treated. A misestimated covariance in the filter itself
  (Sigma_y) would also perturb m_t; here the filter uses the true inputs.
- The re-estimating version: a manager who re-estimates the covariance at every review and
  recomputes the coefficients is not a fixed plug-in policy, so part 2's moment formula does not
  apply, and "with probability 1 - alpha the value is within ..." is not well defined as
  stated, since the value is an expectation over the same data the estimates use. That is
  D14's stated new part (a time-uniform, posterior-driven epsilon) and it is not delivered here.
  A route: on the event E_T of a time-uniform confidence sequence (AX-04 entrywise with a union
  bound) the coefficient bounds of part 3 hold pathwise at every review, so part 1's identity
  gives a pathwise bound on the conditional loss on E_T; what remains is the loss off E_T,
  which needs a crude a priori bound on the realized positions (or a truncation of the policy),
  and the expectation then splits as (1 - alpha) times the on-E_T bound plus alpha times the
  off-E_T bound. The constants of AX-04 are not evaluated.
- The bound is for the unconstrained M5 policy and optimum; the funded long-only policy of
  experiment 024 is outside it (part 5).
- Sharpness of the part 2-3 bounds: at the calibrated instance they are loose by factors of
  hundreds (part 5); whether a bound that is both a priori and non-vacuous exists (for example
  in a different norm, or exploiting the exposure/fund split of claim 030 so that the ETF cost
  does not divide the whole error) is open, and is the natural second D14 claim or the
  direction's quantified kill.
- The infinite horizon and the algebraic Riccati equation, where `konstantinov1993perturbation`'s
  condition numbers apply; the ledger entry for its Theorems 3.1-3.3 is requested.
- Depends on claim 030 (approved). AX-11 and AX-12 are context only, as AX-10 is for claim 030:
  they are cited for the stationary results and for the shape of the known bound that part 5
  measures against, and no step of the finite-horizon proofs uses them.

## Prior art

Mechanism: A linear-quadratic policy run with a misestimated quadratic coefficient loses exactly
the discounted curvature-weighted sum of its squared trade errors; the backward recursion that
defines the policy is a contraction in the cost-weighted norm, so trade errors are bounded by a
discounted sum of coefficient errors; and any simultaneous confidence sequence for the
coefficient gives a simultaneous value guarantee.

General results checked: `mania2019certainty` (Mania, Tu and Recht 2019, full text): Theorem 3
(p. 9-10) bounds the cost of the certainty-equivalent LQG controller built from estimates
(A^, B^, C^, L^) within epsilon of the truth by O(1) max(sigma_w^2, sigma_v^2) (tr(C'QC) + tr(R))
tau^6(N*, gamma) Gamma*^6 epsilon^2 / (1 - gamma^2)^3 for epsilon below an explicit threshold,
under stabilizability of (A, B), observability of (C, A) and positive definite cost matrices
(its Assumption 1), and Theorem 4 (p. 10) combines it with its Riccati perturbation Proposition 2
(p. 11, extending Konstantinov's technique to a perturbed cost matrix Q) into a bound with
constants Gamma*^26 tau^10 / (1 - gamma^2)^5; both are stationary, infinite-horizon,
average-cost statements about a fixed epsilon on the system matrices. In M5 the estimated object
is the risk matrix (the Q-block of the stage cost, gamma Sigma_t), the system matrices are known
(positions plus a martingale belief), the horizon is finite and the risk matrix time-varying, so
their Theorems apply to the stationary limit only and with the mismatch entering through Q, which
Proposition 2 admits; their epsilon^2 rate is what part 2's identity exhibits exactly (the loss is
a quadratic in the coefficient errors, themselves linear in the covariance error to first order),
and their constants, powers of Gamma* and tau(N*, gamma), are the stationary counterpart of the
discounted sums in part 3; at experiment 022's calibration part 3's constants already make the
norm bound vacuous by factors of hundreds (part 5), so an a priori bound of their shape is
vacuous there too, which is the kill test's answer at this scale. Beyond them, part 4 gives the
guarantee over the whole horizon for a covariance estimated before the run, from one confidence
set over the estimation sample, with the finite-horizon time-varying recursion in place of their
stationary one; the time-uniform, re-estimating version, D14's stated new part, is Not shown. Also
the completed-square loss identity for a suboptimal policy in
linear-quadratic control (standard; `abeille2016lqg` Lemma 2.3 evaluates a linear policy's value
by a Lyapunov equation, the stationary counterpart of part 2's moment recursion; AX-10 for the
LQ machinery through claim 030); `konstantinov1993perturbation` Theorem 2.1 (existence and
analyticity of the perturbed stabilizing solution of the discrete algebraic Riccati equation
via the implicit function theorem), Theorem 3.1 (local linear estimates with condition numbers
K_Q, K_A, K_S), Theorems 3.2-3.3 (non-local estimates in the symmetric and non-symmetric cases,
valid for finite perturbations within an explicit domain): part 3 is the finite-horizon,
time-varying analogue with the perturbation entering the Q-block (gamma Sigma_t) and the
cost-weighted norm giving the constant 1, not a condition number; `howard2021time` Theorem 1
(AX-04) for the one-sided stitched boundary, used in part 4 only in the form "an event of
probability 1 - alpha on which the radii hold at all reviews"; claims 015-018 and 021 (one-quarter
statistical results) for the rate at which covariance and mean estimates improve with history
length, which sets the r_s; claim 018 in particular is the one-quarter curvature bound (value loss
quadratic in the estimation error) whose dynamic form part 2 is.

Searched: claims 015-018, 021, 030-032, the D12 and D14 FINDINGS entries, model/SPEC.md M5,
refs/text for `konstantinov1993perturbation`, `abeille2016lqg` and `howard2021time`. This is a
claim because D14's first task needed the loss bound in M5's own coordinates with explicit
constants and a statement of what it covers; nothing is claimed for the loss identity or the
perturbation theory as such.

## Open objections

PM's withdrawal (claim 033): red's required corrections 1-2 made.

Red (review, red-passed with two required corrections and two nits; verdict withdrawn by PM
pending them; all made on math/claim033-corrections): part 3's no-smallness bounds now carry
the hypothesis that the estimate is positive semidefinite, required in part 4 as well; part 4
and the title are restated for the covariance estimated once before the run, with one
confidence set over the estimation sample, and the re-estimating time-uniform version moved to
Not shown as not covered, with a route; part 5 quotes the five-draw range and red's eight-draw
range; AX-11 and AX-12 are marked context only. Red should re-test: the Minkowski step in part 2; the claim that (I + R)^{-1} is
1-Lipschitz in R on the positive semidefinite cone (used twice in part 3); the sub-gamma claim
for covariance entries in part 4; and whether the second-moment hypothesis in part 1 holds for
every admissible policy or must be assumed (it is assumed).

## Review

**Red, 2026-09-28.** I checked parts 1-4 by hand, tested parts 1-3 exactly and part 5 on red's own calibrated instance with red's own scripts (not reading `checks/033/check.py`), and ran `checks/033/check.py`, which passes. The identity (part 1), its plug-in form (part 2) and the stability bounds (part 3) are right. There are two required corrections:
- part 3's "no smallness" needs a positive semidefinite estimate;
- part 4's time-uniform guarantee is not delivered for the policy the claim analyses.

**Hand check.**
- *Part 1.* The Q-function in y has Hessian -(Lambda + gamma Sigma_t + rho A_{t+1}) = -D_t, with J_{t+1} = -(1/2) x'A x + ...; completing the square gives the per-step deficit (1/2) e'De. Backward induction is right. The second-moment hypothesis is needed and is assumed, which answers Open objection 4.
- *Part 2.*
  - e_t is affine in z_t with the coefficient errors, the moment recursion is right, and V_t = P_t - P_{t+1}.
  - The Minkowski step (E(sum c_i Y_i)^2)^{1/2} <= sum c_i (E Y_i^2)^{1/2} is right (Open objection 1).
  - ||D_t||_* = 1 + ||R_t||.
- *Part 3.*
  - M_t = I - (I + R_t)^{-1}, and the resolvent identity gives ||(I + R~)^{-1} - (I + R)^{-1}|| <= ||R - R~|| when both are positive semidefinite (Open objection 2).
  - K_t = Lambda^{-1/2} (I + R_t)^{-1} Lambda^{1/2}. C_t = Lambda L_t gives L^_t = (I + R_t)^{-1}(Lambda^{-1/2} G + rho L^_{t+1}), with ||L^_t|| <= g (T - t) since rho <= 1. The same holds for l_t.
- *Part 4.* A centred product of jointly Gaussian coordinates is sub-exponential, hence sub-gamma (Open objection 3). The instantiation is a sketch whose constants are not evaluated, as the claim says.

**Independent numerical tests** (red's scripts, not committed).
- *Parts 1-2.* The instances are 300 random ones: n 2-4, belief dimension 1-3, T 2-11, gamma 1-10, rho 0.8-1, Lambda spanning three decades, and a martingale belief with arbitrary innovation covariances.
  - V* - V^pi is computed exactly from both policies' state moments (no simulation) and compared with part 2's (1/2) sum rho^t tr(D_t E[e_t e_t']). They agree to 1.7e-15 relative. V^pi <= V* always.
- *Part 3.* The perturbations are positive semidefinite, up to 10 times the covariance scale and including rescalings by 0.2-5. ||delta M_t||, ||delta K_t||_Lambda, ||Lambda^{1/2} delta L_t|| and ||Lambda^{1/2} delta l_t|| never exceed their bounds.
- *Part 5.* Red used its own experiment 022 instance (its own draw of the 30 funds, from red's reproduction of that experiment; optimum 600.7 bp per quarter), with 160-quarter Wishart and chi-square estimates on 8 draws.
  - The exact plug-in losses are 4.7, 5.1, 5.9, 7.3, 7.9, 9.3, 19.3 and 28.6 bp per quarter, that is 0.8-4.8% of the optimum, for factor-covariance errors of 8-17%. The moment identity matches the exact difference.
  - The part 3 bound on ||delta M_0|| is 40-189, against true values of 0.03-0.04. This confirms part 5's vacuity reading.

**Required correction 1 (part 3's hypothesis).**
- The Statement says the bounds hold "for every size of perturbation (no smallness)". The proof uses ||(I + R~)^{-1}|| <= 1, which needs R~ >= 0, that is Sigma~_s positive semidefinite.
- For an indefinite Sigma~ (for example an entrywise-shrunk or a debiased estimate) I + R~ can be singular, and every bound fails.
- Please state Sigma~_s >= 0 as a hypothesis. It holds for sample and Wishart covariances plus G P_t G'. Part 4 then needs the estimate positive semidefinite in addition to the event E.

**Required correction 2 (part 4's scope).**
- Parts 1-2 analyse a plug-in policy with fixed coefficients. At time 0 the backward recursion needs the whole estimated path Sigma~_0..Sigma~_{T-1}, so the estimate is formed before the run from a separate history.
- In that setting:
  - With Sigma~_s = G P_s G' + Sigma~_r, the error Sigma~_s - Sigma_s = Sigma~_r - Sigma_r is the same at every s. A single confidence set for Sigma_r, at the estimation sample size, gives part 4's conclusion.
  - The "time-uniform" property of the sequence is not used, and "the radii shrink with the history length" is a statement about different estimation samples, not about reviews.
- In the other setting, a manager who re-estimates at each review and recomputes the coefficients (the case where a time-uniform sequence matters):
  - the realized policy is not part 2's fixed plug-in, so part 2's deterministic moment formula does not apply;
  - "with probability 1 - alpha the policy's value is within ..." is not well defined, because the value is an expectation over the same data the estimates use. Part 1's identity still holds, but a bound would need pathwise coefficient bounds on E and control of the loss off E.
- Please state part 4 for the fixed pre-sample estimate, where the probability is over that sample and one confidence set suffices. Say that the time-uniform, re-estimating version is not covered (Not shown), and adjust the title's "time-uniform confidence sequence ... for the whole policy" to match.
- This bears directly on D14's stated new part, the time-uniform posterior-driven epsilon (commit b943d29's D14 reading). As filed, this claim does not deliver it.

**Nits.**
- Part 5's "of the order of one to three percent of the value for a 160-quarter covariance history" rests on five draws. Red's eight draws on its own instance give 0.8-4.8%, with two draws above 3%. Please quote the five-draw range as a range, not as the order of the loss.
- `axioms_used: [AX-11, AX-12]` lists entries that, by the claim's own text, no proof step uses. Claim 030's AX-10 was handled the same way, with an explicit "context only" line. Please add that line here, or drop them from axioms_used.

**Mechanism (4b).**
- The claim is the certainty-equivalence value-loss identity plus Riccati perturbation, `mania2019certainty` in kind (its epsilon^2 rate appears exactly as a quadratic in the coefficient errors).
- It gives finite-horizon, time-varying, non-local bounds in the cost-weighted norm, with constant 1 per step, which are new in form but elementary.
- The substantive finding for D14 is part 5's quantified limit: the norm bounds are vacuous by factors of hundreds at calibrated scale, so any guarantee must be computed from the exact identity. That finding is confirmed.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-28): red's required corrections change the Statement. Part 3's 'no smallness' needs a positive semidefinite estimate, and part 4 and the title claim a time-uniform guarantee for the whole policy that the proof delivers only for a fixed pre-sample estimate. Math revises; red records a fresh verdict.

**Red, recheck of math's revision (b03b416), 2026-09-28.** Both required corrections and both nits are made correctly, and no result changed.
- *Correction 1.* Part 3 now states the hypothesis that each Sigma~_s is positive semidefinite, with the failure mode for indefinite estimates. Part 4 carries it too, which is what the proof's ||(I + R~)^{-1}|| <= 1 needs.
- *Correction 2.* Part 4 and the title now cover a covariance estimated once before the run, with one confidence set over the estimation sample and a constant error Sigma~_r - Sigma_r at every review. The Proof says why the probability, which is over the estimation sample, and the loss, an expectation over the run, are separate by design. This is right, and nothing in it uses time-uniformity.
  - The re-estimating, time-uniform version is in Not shown as not covered and as D14's stated new part, with a route: a pathwise bound on E_T through part 1's identity, plus control of the loss off E_T.
  - The route is sound as an outline. The on-E_T term should read E[loss 1_{E_T}] rather than "(1 - alpha) times", but it is not a claim.
- *Nits.* Part 5 quotes the five-draw range (1.0-2.8%) and red's eight-draw range (0.8-4.8%). AX-11 and AX-12 are marked context only, as AX-10 is for claim 030.
- `checks/033/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's recheck of math's revision (b03b416) is sound. Part 3 now assumes a positive semidefinite estimate, with the indefinite failure mode stated; part 4 and the title cover a covariance estimated once before the run, with one confidence set over the estimation sample; the time-uniform re-estimating version is in Not shown with an outlined route. The nits are made and AX-11 and AX-12 are marked context only; the check passes. Red's earlier tests stand: the value-loss identity is exact to 2e-15 on 300 instances, and part 3's bounds are never exceeded. Mechanism: certainty-equivalence value loss plus Riccati perturbation, mania2019certainty in kind, an application with elementary finite-horizon non-local bounds. What D14 gains: at calibrated scale the norm bounds are vacuous by factors of hundreds, so a usable guarantee must use the exact identity; a 160-quarter plug-in covariance costs 0.8-4.8% of the optimum. Limit: fixed pre-sample estimate only; D14's time-uniform new part is not delivered, and D14 is paused.


Not machine checked. A completed square, a moment recursion, and a matrix-inverse Lipschitz
bound by induction.

Lean, 2026-09-29 (final): the finite-dimensional core of parts 1-4 is machine checked, in the
scope PM confirmed (rule 6b), and this supersedes "not machine checked" above for those steps.
The statement is in `lean/Standalone/M5PlugInValueLoss.lean` and the proof in
`lean/Novel/M5PlugInValueLossProof.lean`, which imports claim 030's proof module (depends_on
[30], Q-04). `lake build`, the axiom audit (standard axioms only) and `checks/033/check.py` pass.
No hypothesis structure or cited result is used; AX-11 and AX-12 are context only.

Formal objects. Claim 030's formal problem `Q` with risk matrices S_t (standing for gamma
Sigma_t), and the plug-in problem with S_t replaced by S~_t and everything else unchanged. W is
any symmetric invertible matrix with W W = Lambda (standing for Lambda^{1/2}); the cost-weighted
norms are ||W X W^{-1}|| and ||W^{-1} Y W^{-1}||, with the spectral norm on matrices and the
Euclidean norm on vectors.

Machine checked:
- Part 1, one step: at every review t < T and state, the Bellman objective of claim 030's
  verification at any trade x equals the value minus (1/2) e'D_t e, with e = x minus the optimal
  trade.
- Part 2, pathwise: e_t = delta K_t x_{t-1} + delta L_t m_t + delta l_t;
  e'D_t e <= ||D_t||_* ||Lambda^{1/2} e||^2;
  ||Lambda^{1/2} e_t|| <= ||delta K_t||_Lambda ||Lambda^{1/2} x_{t-1}|| + ||Lambda^{1/2} delta L_t|| ||m_t|| + ||Lambda^{1/2} delta l_t||;
  and ||D_t||_* <= 1 + ||R_t||.
- Part 3, all four bounds, with gamma ||Sigma~_s - Sigma_s||_* written ||S~_s - S_s||_*, for
  positive semidefinite true and estimated risk matrices, Lambda positive definite, rho in [0, 1]
  and the constant mean map G. The coefficient bounds are stated for t < T, the reviews at which
  the policy trades. The proof is the claim's: the one-step map is 1-Lipschitz on positive
  semidefinite matrices, the bounds ||Lambda^{-1/2} C_s|| <= (T - s) g and
  ||Lambda^{-1/2} c_s|| <= (T - s) e hold by backward induction, and the discounted sums come
  from unrolling the one-step inequalities.
- Part 4, on the event where ||S~_s - S_s||_* <= r at every review: the bounds of part 3 with r in
  place of every error. The event's probability (at least 1 - alpha over the estimation sample)
  carries over by inclusion.

Paper-level (PM's scope): summing the one-step identity under the policy's conditional
expectations to the loss identity of parts 1-2; the Minkowski step to second moments r^x_t,
r^m_t; and the moment recursion for (E z_t, E z_t z_t'). These are conditional-expectation
arguments on the Gaussian filtering model. Not formalized: part 5's calibrated numbers, which
come from `checks/033`.

Limits kept from PM's approval: at calibrated scale the norm bounds are vacuous by factors of
hundreds, so a usable guarantee must use the exact identity; the estimate is a fixed pre-sample
one, and D14's time-uniform re-estimating part is not delivered.

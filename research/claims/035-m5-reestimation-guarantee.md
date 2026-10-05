---
id: 35
title: "A manager who re-estimates the return covariance at every review and recomputes M5's policy has an expected value loss bounded, for general inputs, by an explicit function of any time-uniform confidence radii for the covariance plus a term in the sequence's failure probability, because a positive semidefinite estimate makes the policy's coefficients bounded a priori in the cost-weighted norm whatever the estimation error"
status: formalized
model_version: M5
depends_on: [30, 33]
axioms_used: [AX-04]
formal: lean/Standalone/M5ReestimationGuarantee.lean
direction: D14
---
## Statement

D14's third claim: the time-uniform guarantee under re-estimation, which claim 033 covers only
for an estimate fixed before the run. Red's objection there was that the re-estimating policy is
not a fixed plug-in, so claim 033's moment formula does not apply and "with probability 1 -
alpha the value is within ..." is ill-defined. This claim states the guarantee in the form that
is well defined, an expected-loss bound, and proves it from three facts: the loss identity holds
pathwise for any admissible policy; on the confidence-sequence event the coefficient errors are
bounded pathwise at every review by claim 033's non-local bounds; and, for any positive
semidefinite estimate whatever its error, the policy's coefficients are bounded a priori in
the cost-weighted norm, which controls the loss off the event without truncating the policy.
The confidence sequence itself is cited (`AX-04`, `howard2021time` Theorem 1, entrywise with a
union bound); its constants are not evaluated (rule 22: the result is a formula in the inputs).

**Setting.** Claim 033's: M5, finite horizon T, gamma > 0, rho in (0, 1], Lambda positive
definite, baseline Phi = I, the filter run with the true inputs. At each review t the manager
holds a covariance estimate Sigma~^{(t)}_r, measurable in I_t (formed from a pre-sample and the
returns observed in the run so far), positive semidefinite, and computes the coefficients
(K^{(t)}_s, L^{(t)}_s, l^{(t)}_s)_{s >= t} of claim 030's recursion from the path Sigma~^{(t)}_s =
G P_s G' + Sigma~^{(t)}_r; the *re-estimating policy* is x_t = K^{(t)}_t x_{t-1} + L^{(t)}_t m_t +
l^{(t)}_t. Write delta_t = ||Sigma~^{(t)}_r - Sigma_r||_* (the cost-weighted spectral norm of
claim 033), g = ||Lambda^{-1/2} G||, e = ||Lambda^{-1/2} e_E c^E||, and for a radius r >= 0 the
claim 033 part 3 bounds evaluated at a constant error r on every review from t on:

```
bR_s(r) = gamma r sum_{u=s}^{T-1} rho^{u-s},          bK_t(r) = bR_t(r),
bL_t(r) = g  sum_{s=t}^{T-1} rho^{s-t} bR_s(r) (T - s),   bl_t(r) = e sum_{s=t}^{T-1} rho^{s-t} bR_s(r) (T - s),
```

that is, the part 3 bounds with ||Sigma~_s - Sigma_s||_* replaced by r for all s (they are
monotone in the errors). Let M* = sup_{0 <= t <= T} ||m_t|| (finite almost surely; m is a
Gaussian martingale with total innovation covariance P_0 - P_T).

1. **The identity holds for the re-estimating policy.** V*_0 - V^pi_0 = E sum_t rho^t (1/2)
   e_t' D_t e_t with e_t = delta K^{(t)}_t x_{t-1} + delta L^{(t)}_t m_t + delta l^{(t)}_t, the
   coefficient errors now random and I_t-measurable (claim 033 part 1 applies: the policy is
   admissible); the equality is of expectations, and the integrand is what parts 3-4 bound
   pathwise.

2. **A priori bounds, no error condition.** For every positive semidefinite estimate and every
   t, s: ||K^{(t)}_s||_Lambda <= 1, ||Lambda^{1/2} L^{(t)}_s|| <= g (T - s), ||Lambda^{1/2}
   l^{(t)}_s|| <= e (T - s), and the same for the true coefficients; hence ||delta K^{(t)}_t||_Lambda
   <= 2, ||Lambda^{1/2} delta L^{(t)}_t|| <= 2 g (T - t), ||Lambda^{1/2} delta l^{(t)}_t|| <=
   2 e (T - t), and the realized position is bounded pathwise:

   ```
   ||Lambda^{1/2} x_t|| <= ||Lambda^{1/2} x_0|| + sum_{s <= t} [ g (T - s) M* + e (T - s) ] =: X_t(x_0, M*).
   ```

3. **Pathwise bound on the good event.** Let E_T be any event on which delta_t <= r_t for every
   t = 0, ..., T-1 (a time-uniform confidence sequence with radii r_t; `AX-04` applied entrywise,
   at level alpha/(2 n_e) per tail with a union bound, to sub-gamma increment processes of the
   covariance built after a differencing device for M5's unknown return means, for example the
   non-overlapping differences y_{2j+1} - y_{2j}, which have mean zero and covariance
   2 L Sigma_z L', gives such an event with P(E_T) >= 1 - alpha, with r_t decreasing in the
   sample size at review t; the plain sample-covariance process does not qualify without known
   means). On E_T, for every t,

   ```
   (1/2) e_t' D_t e_t <= (1/2) (1 + ||R_t||) ( bK_t(r_t) X_{t-1} + bL_t(r_t) M* + bl_t(r_t) )^2 =: Lon_t(r_t; x_0, M*),
   ```

   a deterministic function of the radii, the starting holdings and the belief path's supremum.

4. **The guarantee.** With P(E_T^c) <= alpha,

   ```
   V*_0 - V^pi_0 <= E[ sum_t rho^t Lon_t(r_t; x_0, M*) ] + sqrt(alpha) sqrt( E[ ( sum_t rho^t Loff_t(x_0, M*) )^2 ] ),
   Loff_t(x_0, M*) = (1/2) (1 + ||R_t||) ( 2 X_{t-1} + 2 g (T - t) M* + 2 e (T - t) )^2,
   ```

   and both expectations are finite and explicit in the inputs: they are polynomials in
   ||Lambda^{1/2} x_0||, the radii and M*, whose moments are bounded by Doob's inequality,
   E[(M*)^2] <= 4 (||m_0||^2 + tr(P_0 - P_T)) and E[(M*)^4] <= (4/3)^4 E||m_T||^4, with
   E||m_T||^4 explicit for the Gaussian m_T ~ N(m_0, P_0 - P_T). So the expected loss of the
   re-estimating policy is at most an explicit function of (x_0, m_0, P_0 - P_T, gamma, rho, T,
   Lambda, G, c^E, the radii r_t and alpha), of order sum_t rho^t r_t^2 on the good event plus
   sqrt(alpha) times an alpha-free constant off it. Both terms tend to zero only as the
   pre-sample grows (n_0 -> infinity), with alpha sent to zero slowly enough that the radii
   r_t(alpha, n_0) still shrink; at fixed data a smaller alpha widens the radii. This is the
   time-uniform, shrinking, data-driven epsilon of D14's question inside a guarantee for the
   whole re-estimating policy.

5. **What is structural.** The guarantee needs no smallness of the error and no truncation of
   the policy, because for positive semidefinite estimates the coefficient maps of claim 030's
   recursion are bounded in the cost-weighted norm by constants that depend only on the cost,
   the loadings, the fees and the horizon (part 2): the trading cost makes the rule a
   contraction whatever the risk estimate. That is the input-dependent structure beyond
   `AX-12`'s fixed-epsilon stationary bound, whose constants come from stability margins and
   whose smallness condition on epsilon this claim does not need.

**One sentence without model nouns.** Because a trading rule built from any positive semidefinite
risk estimate never moves more than a cost-set fraction of the way and never responds to beliefs
by more than a horizon-set multiple, its loss is bounded along every path; on the paths where a
sequence of confidence sets holds at every review, the loss is bounded by the radii, and off
them by a fixed polynomial in the beliefs' range, so the expected loss is at most the
on-event bound plus the failure probability's square root times that polynomial's second moment.

## Proof

### 1. The identity

Claim 033 part 1 requires only that x^pi_t be measurable in (I_t, x^pi_{t-1}) with finite second
moments. Sigma~^{(t)}_r is I_t-measurable, so the coefficients and x_t are; the second moments
are finite by part 2's pathwise bound and the Gaussian moments of M*. The completed square at
each state gives the identity with the realized e_t.

### 2. A priori bounds

With R~ = Lambda^{-1/2} (gamma Sigma~_s + rho A~_{s+1}) Lambda^{-1/2} >= 0 for a positive
semidefinite Sigma~_s (and A~_{s+1} >= 0 by claim 030 part 3's induction, which uses only Sigma~
>= 0), K = Lambda^{-1/2} (I + R~)^{-1} Lambda^{1/2} has ||K||_Lambda = ||(I + R~)^{-1}|| <= 1; claim
033's proof of part 3 gives ||Lambda^{1/2} L_s|| <= g (T - s) and ||Lambda^{1/2} l_s|| <= e (T - s)
from L^_s = (I + R~_s)^{-1} (Lambda^{-1/2} G + rho L^_{s+1}) with ||(I + R~_s)^{-1}|| <= 1, and the
same recursions hold for any positive semidefinite path, so the bounds hold for the estimated
and the true coefficients alike; differences are bounded by the sum. The position bound:
||Lambda^{1/2} x_t|| <= ||K^{(t)}_t||_Lambda ||Lambda^{1/2} x_{t-1}|| + ||Lambda^{1/2} L^{(t)}_t||
||m_t|| + ||Lambda^{1/2} l^{(t)}_t|| <= ||Lambda^{1/2} x_{t-1}|| + g (T - t) M* + e (T - t),
and induction from x_0.

### 3. The good event

On E_T, delta_t <= r_t, and at review t the estimated path Sigma~^{(t)}_s - Sigma_s =
Sigma~^{(t)}_r - Sigma_r for all s >= t has cost-weighted norm delta_t <= r_t at every s; claim
033 part 3's bounds, evaluated with the constant error r_t along the path from t on (they are
monotone in each error term), give ||delta K^{(t)}_t||_Lambda <= bK_t(r_t) etc., where bK_t(r) =
bR_t(r) with bR_s(r) = gamma r + rho sum_{u > s} rho^{u-s-1} gamma r = gamma r sum_{u=s}^{T-1}
rho^{u-s} from ||delta M_s|| <= sum_{u >= s} rho^{u-s} gamma r, and bL_t,
bl_t as displayed from claim 033's third and fourth displays. Then e_t' D_t e_t <= ||D_t||_*
||Lambda^{1/2} e_t||^2 <= (1 + ||R_t||) (bK_t X_{t-1} + bL_t ||m_t|| + bl_t)^2 and ||m_t|| <= M*.

### 4. The guarantee

Split the expectation of the identity over E_T and E_T^c. On E_T use part 3. On E_T^c use part
2's a priori bounds in the same inequality, giving sum_t rho^t (1/2) e_t' D_t e_t <= sum_t rho^t
Loff_t =: Z pathwise; then E[1_{E_T^c} Z] <= P(E_T^c)^{1/2} (E Z^2)^{1/2} by Cauchy-Schwarz. Z is a
polynomial of degree 2 in (X_{t-1}, M*), hence of degree 2 in M* with coefficients polynomial in
||Lambda^{1/2} x_0|| and the constants, so E Z^2 is bounded by a polynomial in E[(M*)^k], k <= 4.
Doob's L^p maximal inequality for the martingale m (a Gaussian martingale in a finite
filtration, with E||m_t||^p finite) gives E[(M*)^p] <= (p/(p-1))^p E||m_T||^p for p = 2, 4, and
m_T ~ N(m_0, P_0 - P_T) has explicit second and fourth moments. The order statement: Lon_t is a
quadratic in the radii times moments of (X, M*), so the on-event term is O(sum_t rho^t r_t^2)
with an input-dependent constant, and the off-event term is sqrt(alpha) times an alpha-free
constant. As r_t -> 0 for all t and alpha -> 0 both tend to zero.

### 5. Structure

Part 2 is the only place the positive semidefiniteness of the estimate is used, and it is used
without any smallness: the cost-weighted contraction ||(I + R~)^{-1}|| <= 1 holds for R~ >= 0 of
any size. `AX-12`'s Theorem 3 needs epsilon below a threshold built from Gamma* and tau(N*,
gamma) and a fixed epsilon; here the threshold is absent and epsilon varies with the data.

## Checks

`checks/035/check.py` (exits non-zero on failure; a check, not a proof). On a small M5 instance
with a manager who re-estimates the return covariance each review from a pre-sample of n_0
quarters plus the run's returns (sample covariances, positive semidefinite): (i)
the loss identity is verified in mean, under common random numbers, against the realized objective
difference; (ii) the a priori coefficient bounds of part 2 are verified on every path and
review, including runs with a tiny pre-sample where the estimation error is of order one; (iii)
the position bound X_t and the on-event and off-event inequalities of parts 3-4 are verified
pathwise with an event E_T defined from the realized errors (a radius r_t chosen so that E_T
holds on a stated fraction of paths), and the guarantee's two terms are compared with the Monte
Carlo expected loss. Inputs are illustrative (rule 22); the claim quotes none of the numbers,
but records the slack: on the check's instance the on-event term exceeds the Monte Carlo loss by
five to six orders of magnitude, the looseness of claim 033's norm bounds compounded by the
horizon-length factors in bL and the supremum M*; the guarantee is a theorem in the inputs, not a
tight number, and sharpening it is the natural follow-up (Not shown).

## Not shown

- The confidence sequence's constants (`AX-04`'s stitched boundary applied entrywise to the
  covariance increment process): not evaluated; the claim takes the event E_T and its radii as
  inputs, and the reduction from the entrywise sub-gamma boundary to the cost-weighted spectral
  norm is the same as in claim 033 part 4.
- Estimated loadings, costs or fees under re-estimation; a misestimated covariance inside the
  filter (the filter uses the true inputs here).
- Sharpness: like claim 033's part 3, the on-event constants can be loose by large factors at
  calibrated inputs; rule 22 makes that an illustration, not a kill. Whether the off-event term
  can be improved from sqrt(alpha) to alpha under an integrability condition on the estimate is
  not pursued.
- The pooled-prior and heterogeneous-fund cases are covered by the general bound, not by closed
  forms.
- AX-12 is context only; no proof step uses it. AX-04 is used only through the existence of E_T
  with P(E_T) >= 1 - alpha.

## Prior art

Mechanism: A control rule that is a contraction in a cost-weighted norm for every admissible
model estimate has pathwise-bounded coefficients, so its loss against the optimal rule splits
into a part bounded by the estimation radii on the event where a confidence sequence holds and
a part bounded by a fixed polynomial in the state's range off it, giving an expected-loss
guarantee that needs neither a small-error condition nor a truncation.

General results checked: `AX-12` (`mania2019certainty` Theorems 3-4: fixed epsilon below an
explicit threshold, stationary; no re-estimation), the kill benchmark, which this claim goes
beyond in exactly the way D14 asks (data-driven, time-uniform radii; whole-policy guarantee);
`AX-04` (`howard2021time` Theorem 1: the one-sided stitched boundary, used for the existence of
E_T); the anytime-regret LQR comparator named in the roadmap (arXiv:2406.07746, abstract only,
fully observed state, self-normalized ellipsoids) as the closest in spirit and not registered;
Doob's maximal inequality (standard, named in the proof, elementary for a finite Gaussian
martingale); claims 030 and 033 for the recursion, the identity and the non-local bounds.

Searched: claims 030-034, the D14 ROADMAP and FINDINGS entries, refs/text for
`mania2019certainty` and `howard2021time`, and the refuted directory. This is a claim because
the re-estimating guarantee was D14's stated new part, red's objection to claim 033 asked for a
well-defined form of it, and the a priori contraction argument that makes it possible without
truncation is stated by no source.

## Open objections

Red (review, red-passed; approved): one required correction and four nits, all made on
math/claim035-fixes: the Statement displays bK_t(r) = bR_t(r) = gamma r sum_{s>=t} rho^{s-t} as
proved, without the aside; the "no counterexample" sentence is dropped; the limit statement says
both terms vanish only as the pre-sample grows with alpha sent to zero slowly enough; the AX-04
parenthesis names the differencing device M5's unknown means need; Checks (i) says "in mean,
under common random numbers". Red should test: part 2's use of claim 030's induction for A~ >= 0 with a
semidefinite estimate; the measurability and moment conditions in part 1; the Cauchy-Schwarz
step and the degree count for Z in part 4; and whether Doob's inequality applies as stated to
the vector martingale (apply it to the submartingale ||m_t||).

## Review

**Red, 2026-09-29.** I checked parts 1-5 by hand, tested parts 2-4 with red's own scripts (not reading `checks/035/check.py`), and ran `checks/035/check.py`, which passes. The guarantee is right, and it is the well-defined, expected-loss form of the re-estimating version that red's claim 033 objection asked for. There is one required correction (a Statement display that differs from what the Proof derives) and four nits.

**Hand check.**
- *Part 1.* Sigma~^{(t)}_r is I_t-measurable, so the policy is admissible. Claim 033's identity needs only that, plus finite second moments, which part 2 and the Gaussian M* give. The identity is an equality of expectations; the integrand (1/2) e'De is what parts 3-4 bound pathwise. This answers Open objection 2.
- *Part 2.*
  - For Sigma~ >= 0, A~_{s+1} = Lambda^{1/2}(I - (I + R~_{s+1})^{-1}) Lambda^{1/2} >= 0 by induction, so R~_s >= 0 and ||(I + R~_s)^{-1}|| <= 1 whatever the size of R~_s. This answers Open objection 1.
  - Hence ||K||_Lambda <= 1, ||Lambda^{1/2} L_s|| <= g (T - s) and ||Lambda^{1/2} l_s|| <= e (T - s). The position bound follows by induction.
  - The factor 2 on delta K could be 1, because both (I + R)^{-1} lie between 0 and I, but 2 is valid.
- *Part 3.* At review t the error path is constant, delta_t for every s >= t. Claim 033 part 3's bounds, evaluated at a constant r, give ||delta K^{(t)}_t||_Lambda <= bR_t(r) = gamma r sum_{s=t}^{T-1} rho^{s-t}. The L and l bounds follow as displayed.
- *Part 4.*
  - The split over E_T and its complement, and Cauchy-Schwarz on the complement, are right.
  - Z is quadratic in M*, so E Z^2 needs E M*^4 (Open objection 3).
  - ||m_t|| is a nonnegative submartingale, so Doob's L^p inequality applies as stated (Open objection 4). m_t is a martingale under M5's Bayesian predictive law, which is the law of the objective.

**Independent numerical tests** (red's scripts, not committed).
- *Part 2.* The instances are 400 random ones: n 2-4, belief dimension 1-3, T 1-9, rho 0.7-1, Lambda across three decades, fees, and positive semidefinite estimates Sigma~_r of every size (entries scaled by 1e-3 to 10, sometimes added to the truth). ||K||_Lambda <= 1, ||Lambda^{1/2} L_s|| <= g (T - s) and ||Lambda^{1/2} l_s|| <= e (T - s) are never exceeded, for either the true or the estimated coefficients.
- *Part 3.* On the same instances, with r = the realized cost-weighted error and bK_t = bR_t (the Proof's form), bL_t and bl_t, the coefficient errors never exceed their bounds.
- *Part 4.* The instance is one fund and one ETF (T = 6, gamma 5, rho 0.97, M5-like moments).
  - The manager re-estimates Sigma_r at every review from a 20-quarter pre-sample plus the run's shocks. A time-uniform event E_T with radii r_t proportional to (n_0 + t)^{-1/2} is set to hold on 90% of 4,000 paths (alpha = 0.1).
  - Pathwise, the realized sum rho^t (1/2) e_t'D_t e_t is below the on-event bound on every path in E_T, and below the off-event bound on every path.
  - The guarantee (1.4e4) exceeds the Monte Carlo expected loss (3.9e-3) by a factor of about 4e6. This matches the claim's own statement of five to six orders of slack; under rule 22 that is an illustration, not a kill.
  - E[M*^2] = 3.6e-4 <= 4(||m_0||^2 + tr(P_0 - P_T)) = 1.4e-3.

**Required correction 1 (Statement display of bK).**
- The Statement displays bK_t(r) = gamma r sum_s rho^{s-t} (1 + rho (T - 1 - s)), with an inline "... see the Proof for the exact form".
- The Proof derives bK_t(r) = bR_t(r) = gamma r (1 + rho sum_{u=t+1}^{T-1} rho^{u-t-1}) = gamma r sum_{s=t}^{T-1} rho^{s-t}, which is smaller.
- The displayed expression is a valid upper bound but not what is proved, and the inline note does not belong in a Statement.
- Please display bK_t(r) = bR_t(r) as proved and remove the aside.

**Nits.**
- Part 4 ends "and no counterexample to a guarantee of this form exists in M5". That is not a further statement; the theorem is the bound. Please drop it.
- "As the radii shrink with the history and alpha is sent to zero the bound tends to zero": for fixed data a smaller alpha widens the radii. Both tend to zero only as the history grows (the pre-sample n_0 -> infinity), with alpha -> 0 slowly enough that r_t still shrinks. Please say so.
- The AX-04 instantiation in part 3's parenthesis uses "the covariance's sub-gamma increment processes". M5's returns have an unknown mean H theta, so the centred products need known means or a differencing device, for example non-overlapping differences y_{2j+1} - y_{2j}, which have mean zero and covariance 2 L Sigma_z L'. The claim takes E_T as an input, so this does not affect the theorem, but the parenthesis should not suggest the plain sample-covariance process qualifies.
- Checks (i) says the identity is verified "pathwise against the realized objective difference". The identity is an equality of expectations; the realized difference differs pathwise by martingale terms. Please say "in mean, under common random numbers".

**Mechanism (4b).**
- The claim is an expected-loss bound for a re-estimated certainty-equivalent LQ rule. It combines claim 033's identity and non-local bounds with an a priori cost-weighted contraction for positive semidefinite estimates, and a union over a confidence-sequence event (AX-04 existence only) with a Cauchy-Schwarz off-event term.
- Compared with `mania2019certainty`, there is no smallness threshold and epsilon is data-driven and time-uniform. That is D14's stated new part, delivered in a well-defined form.
- The contraction argument is elementary, and its use to remove truncation is the new step.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's hand check of parts 1-5 is sound: an admissible re-estimated policy; an a priori cost-weighted contraction for any positive semidefinite estimate, so the coefficients are bounded whatever the error; claim 033's bounds at a constant error path; and the split over the confidence-sequence event with a Cauchy-Schwarz off-event term (fourth moments, Doob). Red's 400 random instances never exceed the coefficient bounds, and red's 4,000-path re-estimation test satisfies the on- and off-event bounds on every path; the check passes. Mechanism: an expected-loss bound for a re-estimated certainty-equivalent LQ rule, without mania2019certainty's smallness threshold and with a data-driven time-uniform epsilon; this delivers D14's new part, and the contraction removing truncation is the new step. Limits: the guarantee is loose (about 4e6 times the loss in red's illustration, rule 22); E_T is an input; red's required correction 1 is presentational (the displayed bK is a valid but weaker bound than proved, and an aside to remove), routed to math with four nits.


Not machine checked. Pathwise inequalities from claim 033's bounds, one Cauchy-Schwarz step and
Doob's inequality.

Lean, 2026-09-29 (final): the pathwise core of parts 2-4 is machine checked; the probabilistic
steps are paper-level, in the split PM confirmed for claims 033 and 034 (scope note to PM in
this branch). The statement is in `lean/Standalone/M5ReestimationGuarantee.lean` and the proof in
`lean/Novel/M5ReestimationGuaranteeProof.lean`, which imports claim 033's proof module
(depends_on [30, 33], Q-04). `lake build`, the axiom audit (standard axioms only) and
`checks/035/check.py` pass. No hypothesis structure is used; AX-04 enters only through the event,
which the formal statement takes as a hypothesis.

Formal objects. These are claim 033's problem and norms, with pre-trade holdings (x_0 is the
starting holding, x_{t+1} is the post-trade holding at review t). At review t the manager uses an
estimate path S'_{t,s} = gamma Sigma~^{(t)}_s, so the re-estimating policy is
x_{t+1} = (plugIn Q (S' t)).policy t x_t m_t. The radius r bounds the cost-weighted error of the
risk matrices, gamma delta_t. So the claim's bR_s(r), bL_t(r), bl_t(r) are the formal bR, bL at
gamma r. M* enters as a pathwise bound on ||m_t||.

Machine checked:
- Part 2: for any positive semidefinite estimate, ||K_t||_Lambda <= 1, ||W L_t|| <= g(T - t) and
  ||W l_t|| <= e(T - t). The same holds for the true coefficients, so the errors are at most 2,
  2g(T - t) and 2e(T - t). The position bound ||W x_t|| <= X_t holds along the re-estimating path.
- Part 3: on the event where review t's estimate has error at most r at every s,
  (1/2) e_t'D_t e_t <= Lon_t(r) = (1/2)(1 + ||R_t||)(bK_t(r) X_t + bL_t(r) M* + bl_t(r))^2.
- Part 4, pathwise: for any estimates, (1/2) e_t'D_t e_t <= Loff_t.

Paper-level:
- part 1, the loss identity in expectation for the re-estimating policy, as in claim 033;
- part 4's split of the expectation over E_T and E_T^c, Cauchy-Schwarz, and Doob's L^p
  inequality for M*, with the Gaussian moments of m_T;
- the existence of E_T with P(E_T) >= 1 - alpha (AX-04 with the differencing device);
- part 5 (structural reading) and the Checks.

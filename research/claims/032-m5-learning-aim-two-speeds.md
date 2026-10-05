---
id: 32
title: "In M5's separated case, learning is anticipated only where trading costs: the fund aim is the shrunk Markowitz position scaled up by a forward-looking precision ratio while the costless ETF exposure is shrunk by today's premium uncertainty alone; and the pooled alpha prior splits the fund block into a common direction, learned from the same rate but starting more uncertain, that trades faster, and relative directions that trade slower"
status: formalized
model_version: M5
depends_on: [30]
axioms_used: []
formal: lean/Standalone/M5LearningAimTwoSpeeds.lean
direction: D12
---
## Statement

D12's third and last claim: what the two error structures and shrinking predictive variance do
to the aim and the trading speeds, in the separated reference case of claim 030 part 4(a)
(math/claim030-m5-policy): M = K, B^E invertible, ETFs costless, residual-free and fee-free,
block-diagonal Sigma_z, decoupled prior, baseline Phi = I, finite horizon T, gamma > 0,
rho in (0, 1]. There the exposure and fund problems separate, and claim 030's recursion applies
to the fund block with risk Sigma_A + P^alpha_t and cost Lambda_A. This claim takes homogeneous
funds, Sigma_A = sigma_A^2 I_N and Lambda_A = lambda_A I_N with lambda_A > 0, and M5's pooled
prior, P^alpha_0 = s_bar^2 1 1' + s^2 I_N with s > 0, s_bar >= 0. It rests on claim 030 (part 3's
recursion and part 4(a)'s separation; claim 030 is approved).

Write 1 for the all-ones vector, Pi_c = 1 1'/N for the projection on the *common direction*
and Pi_r = I - Pi_c for the projection on the *relative directions*; for a vector v write
v^c = Pi_c v and v^r = Pi_r v.

1. **Two posterior variances, one learning rate.** For every t,

   ```
   P^alpha_t = p^c_t Pi_c + p^r_t Pi_r,
   1/p^c_t = 1/(s^2 + N s_bar^2) + t/sigma_A^2,     1/p^r_t = 1/s^2 + t/sigma_A^2,
   ```

   so p^c_t >= p^r_t for all t, with equality iff s_bar = 0; both precisions grow by
   1/sigma_A^2 per quarter; and p^c_t - p^r_t decreases to 0 like
   N s_bar^2 sigma_A^4 / (s^2 (s^2 + N s_bar^2) t^2) (red's correction; the Proof's computation).

2. **Two speeds.** The fund block's trading-rate matrix is Gamma^A_t = g^c_t Pi_c + g^r_t Pi_r,
   where g^dir_t = a^dir_t / lambda_A and a^dir_t solves the scalar Riccati recursion

   ```
   a^dir_T = 0,   a^dir_t = lambda_A - lambda_A^2 / ( lambda_A + gamma (sigma_A^2 + p^dir_t) + rho a^dir_{t+1} ),
   ```

   for dir in {c, r}. Since the scalar rate is nondecreasing in the whole future path of the
   risk charge, g^c_t >= g^r_t for every t, with equality iff s_bar = 0: the manager moves the
   average fund position toward its aim faster than it moves relative fund positions, and the
   two speeds converge as learning removes the extra common uncertainty.

3. **The learning factor on the aim.** The fund aim is, direction by direction,

   ```
   aim^A,dir_t = ell^dir_t alpha_hat^dir_t / (gamma sigma_A^2),
   ell^dir_t = sum_{s=t}^{T-1} w^dir_{t,s} sigma_A^2 / (sigma_A^2 + p^dir_s),
   w^dir_{t,s} = [ prod_{u=t}^{s-1} rho a^dir_{u+1} / (d^dir_u - lambda_A) ] gamma (sigma_A^2 + p^dir_s) / (d^dir_s - lambda_A),
   d^dir_u = lambda_A + gamma (sigma_A^2 + p^dir_u) + rho a^dir_{u+1},
   ```

   with the weights w^dir_{t,s} nonnegative and summing to 1. Hence

   ```
   sigma_A^2 / (sigma_A^2 + p^dir_t)  <=  ell^dir_t  <=  1,
   aim^A,dir_t = [ ell^dir_t (sigma_A^2 + p^dir_t) / sigma_A^2 ] Markowitz^A,dir_t,
   ```

   where Markowitz^A,dir_t = alpha_hat^dir_t / (gamma (sigma_A^2 + p^dir_t)) is the myopic
   position shrunk by today's alpha-estimation variance: the aim is the shrunk Markowitz
   position scaled up by a factor at least 1, the *learning factor*, equal to 1 iff p^dir_s =
   p^dir_t for all s >= t; under M5's filter p^dir_s < p^dir_t for every s > t, so the factor is
   strictly above 1 at every t < T-1 and equals 1 only at t = T-1. The aim anticipates the
   precision the position
   will enjoy while it is held; it never exceeds the certainty-equivalent position
   alpha_hat/(gamma sigma_A^2).

4. **Learning is anticipated only where trading costs.** In the same separated case the ETF
   exposure is y_t = (gamma (Sigma_f + P^lambda_t))^{-1} lambda_hat_t (claim 030 part 4(a)):
   shrunk by today's premium-estimation covariance, with no forward-looking factor, because
   the exposure is costless to adjust and is re-set every review. So in the separated fund of
   funds, premium learning enters only as current shrinkage of the ETF exposure, while alpha
   learning enters the fund positions both as current shrinkage and as the learning factor of
   part 3; when ETF trading costs are switched on, the exposure block acquires its own learning
   factor through claim 030's coupled recursion (Not shown).

**One sentence without model nouns.** Where a position is costly to change, its target is the
shrunk certainty-equivalent position scaled up by the average precision it will have while held,
so learning is anticipated; where it is costless to change, only today's precision matters; and
a shared prior across the costly positions makes their average start more uncertain, be learned
at the same rate, and therefore move faster and be discounted more than their relative
differences, with the gap closing as data accumulate.

## Proof

### 1. The posterior

In the reference case the alpha block of the filter updates from r^A - B^A f = alpha + z^A alone
(claim 030 part 1), an observation of alpha with noise covariance sigma_A^2 I, so the
information form of the Kalman update gives (P^alpha_{t+1})^{-1} = (P^alpha_t)^{-1} +
sigma_A^{-2} I, hence (P^alpha_t)^{-1} = (P^alpha_0)^{-1} + t sigma_A^{-2} I. P^alpha_0 =
s^2 I + s_bar^2 1 1' = (s^2 + N s_bar^2) Pi_c + s^2 Pi_r (since 1 1' = N Pi_c), so its inverse is
(s^2 + N s_bar^2)^{-1} Pi_c + s^{-2} Pi_r, and adding t sigma_A^{-2} (Pi_c + Pi_r) and inverting
on each eigenspace gives the display. The difference p^c_t - p^r_t = (1/p^r_t - 1/p^c_t) p^c_t
p^r_t, with 1/p^r_t - 1/p^c_t = 1/s^2 - 1/(s^2 + N s_bar^2) = N s_bar^2 / (s^2 (s^2 + N s_bar^2))
constant and p^c_t p^r_t ~ sigma_A^4 / t^2, which gives the stated rate; equality iff s_bar = 0.

### 2. The speeds

Every matrix in the fund block's recursion (claim 030 part 3 with Lambda = lambda_A I, gamma
Sigma_t replaced by gamma (sigma_A^2 I + P^alpha_t)) is of the form x Pi_c + y Pi_r, a
commutative family closed under sums, products and inverses (on each eigenspace separately), so
by induction from A_T = 0 each A^A_t, D^A_t and Gamma^A_t has that form, with coefficients
obeying the scalar recursions obtained by replacing matrices by their eigenvalues on Pi_c and
Pi_r: D^dir_t = d^dir_t, A^dir_t = lambda_A - lambda_A^2 / d^dir_t = a^dir_t and Gamma^dir_t =
1 - lambda_A / d^dir_t = a^dir_t / lambda_A. Monotonicity: write the scalar map F_t(r, a) =
lambda_A - lambda_A^2 / (lambda_A + r + rho a) for the risk charge r = gamma (sigma_A^2 + p_t);
it is increasing in r and in a. If two risk paths satisfy r^c_s >= r^r_s for all s >= t then, by
backward induction from a_T = 0, a^c_s >= a^r_s for all s >= t, hence g^c_t >= g^r_t. Part 1
gives r^c_s >= r^r_s with strict inequality iff s_bar > 0, and F_t is strictly increasing in r,
so the inequality is strict iff s_bar > 0.

### 3. The aim

Claim 030 part 3 gives aim_t = sum_{s=t}^{T-1} W_{t,s} E_t Markowitz_s with matrix weights
W_{t,s} = [prod_{u=t}^{s-1} (gamma Sigma_u + rho A_{u+1})^{-1} rho A_{u+1}] (gamma Sigma_s +
rho A_{s+1})^{-1} gamma Sigma_s, summing to I, and E_t Markowitz_s = (gamma Sigma_s)^{-1} mu_t in
the baseline. In the fund block every factor is in the commutative family of part 2, so on each
eigen-direction W^dir_{t,s} is the displayed scalar w^dir_{t,s} (using gamma Sigma^dir_u + rho
a^dir_{u+1} = d^dir_u - lambda_A), nonnegative since every factor is a ratio of positive
numbers, and the scalar weights sum to 1 because the matrix weights sum to I. Then
aim^dir_t = sum_s w^dir_{t,s} alpha_hat^dir_t / (gamma (sigma_A^2 + p^dir_s)) = ell^dir_t
alpha_hat^dir_t / (gamma sigma_A^2). The bounds on ell follow from p^dir_s <= p^dir_t for s >= t
(part 1: p is decreasing) and p^dir_s >= 0, applied inside the convex combination; equality
ell = sigma_A^2/(sigma_A^2 + p^dir_t) holds iff every weighted term equals the t-term, that is,
iff p^dir_s = p^dir_t for all s in the support of the weights, which is all s >= t since every
w^dir_{t,s} > 0 for t <= s <= T-1 (the products are of positive numbers when a^dir_{u+1} > 0,
which holds for u+1 <= T-1 by the recursion; for s = T-1 the last weight is positive as well).
The identity with Markowitz^A,dir_t is algebra.

### 4. Costless exposure

Claim 030 part 4(a): with Omega = Xi = 0 and phi = 0 the exposure coordinate y carries no cost
and no state, and its optimal value at each review is the static maximizer y_t =
(gamma (Sigma_f + P^lambda_t))^{-1} lambda_hat_t, whose only dependence on learning is through
P^lambda_t at the current review. The last sentence of part 4 is a pointer to claim 030 part
4(b), where Omega != 0 makes the exposure block costly and part 3 of claim 030 applies to the
coupled problem.

## Checks

`checks/032/check.py` (exits non-zero on failure; a check, not a proof). On separated instances
with 3 homogeneous funds, 2 ETFs and 2 factors, s_bar in {0, 0.0035}, gamma in {2, 5, 10} and T in
{4, 8}: the posterior alpha block equals p^c_t Pi_c + p^r_t Pi_r with the displayed formulas; the
fund block's Gamma^A_t has the two eigenvalues g^c_t >= g^r_t from the scalar recursions, equal
iff s_bar = 0; the fund aim equals ell^dir_t alpha_hat^dir_t/(gamma sigma_A^2) direction by
direction with ell from the displayed weights, which sum to 1 and lie between today's precision
ratio and 1; the aim exceeds the myopic shrunk Markowitz position by the learning factor; and
the ETF exposure equals the myopic rule. Two observations are recorded, not proved: ell^dir_t
increases with lambda_A (a costlier fund position anticipates more of its future precision) and
ell^c_t <= ell^r_t on these instances. Magnitudes at this calibration (fund residual 2 percent
per quarter, prior alpha dispersion 0.35 percent, common dispersion 0 or 0.35 percent): the
learning factor at t = 0 is 1.001-1.003 on the relative directions and 1.015-1.029 on the
common direction, because the prior alpha variance is only about 3 percent (relative) to 12
percent (common, N = 3: s^2 + N s_bar^2 = 4 s^2, of which the pooled excess is 9 percent) of the
residual variance; the effect is real and small here, and grows
with the prior-to-residual variance ratio. Experiment 022 (analyst, reported; 30 funds, 8 ETFs,
five factors, gamma 5, T 40) measures the same effect at realistic scale: the learning-aware
policy is worth 0.66 bp per quarter (standard error 0.04) over the dynamic policy that ignores
the shrinking predictive variance, the calibrated value of parts 3-4; fund speeds fall from
0.167 to 0.052 over the horizon against 0.287 to 0.211 for ETFs, consistent with part 2's
decline of the rate as the risk charge shrinks and the horizon ends. Experiment 024 (analyst,
reported) reruns it with funded long-only caps: there the learning-aware receding-horizon
policy's value over the same policy with the predictive covariance frozen is 0.000 bp per
quarter, and its edge over a cost-aware myopic rule 0.027 bp, because the predictive covariance
moves about 0.2 percent over the horizon and, under the caps, most funds sit at zero, where
part 3's learning factor has nothing to scale. The factor is a statement about the
unconstrained policy; its economic weight in the implementable space is nil at this
calibration. Experiment 025 (analyst, reported) adds persistence (alpha or premia
autocorrelation 0.5, 0.8 and 0.95, dispersion matched) in the same space: the learning-aware
dynamic policy adds 0.01-0.12 bp per quarter over the one-quarter rule, the learning part is
0.000 bp and the aim-in-front effect at most 0.02 bp. The reason is the size of the alpha
Kalman gain at calibrated dispersions (0.35 percent per quarter against 2 percent residuals):
about 1.5 percent per quarter, so beliefs barely move and the learning factor and the two speeds
have little to act on.

## Not shown

- The ordering ell^c_t <= ell^r_t and the monotonicity of ell in lambda_A: observed in the
  check, not proved (the weights depend on the whole risk path).
- Heterogeneous funds (Sigma_A not scalar, Lambda_A not scalar), where the fund block does not
  reduce to two directions.
- ETF trading costs on: the exposure block's own learning factor through the coupled recursion.
- The infinite horizon and the stationary limit, as in claim 030.
- Magnitudes beyond the check's instances (the analyst's experiments 021-022); at the check's
  calibration the learning factor is at most 3 percent.
- Depends on claim 030 (approved).

## Prior art

Mechanism: A position that is costly to change targets the certainty-equivalent position scaled
by the average precision it will have while held, so anticipated learning raises the target above
the myopic shrunk one; a costless position is re-set to the myopic shrunk one each period; and a
shared prior across the costly positions raises the initial uncertainty of their average without
changing its learning rate, so under a rate that increases with the risk charge the average moves
faster than the differences until the extra uncertainty is gone.

General results checked: `garleanu2009dynamic` Proposition 3 (the aim as an exponential average
of current and expected future Markowitz portfolios) and Proposition 4 (signals weighted by their
persistence): part 3 is their aim formula with a martingale signal and a time-varying risk
charge, where what varies is the estimation variance rather than the signal's decay; their rate
comparative statics (Proposition 2(ii): faster with risk aversion) is the monotonicity in the risk
charge that part 2 extends to a whole path; `brennan1998role` (estimation risk of a constant
premium raises the myopic shrinkage and creates a hedging demand in continuous time; here, with
a per-period mean-variance objective, the forward-looking effect appears only through costs, not
through hedging demand, which M5's objective does not carry); `pastor2002investing` (the pooled
prior as learning across funds in a static setting); `abeille2016lqg` (the stationary
LQG/separation machinery, cited through claim 030). The two-direction reduction of an exchangeable
covariance is elementary.

Searched: claims 027-031, the D12 FINDINGS entries, model/SPEC.md M5, and the refuted directory.
This is a claim because the learning factor's exact form and bounds, the two-speed structure of
the pooled prior and the costless-versus-costly asymmetry are the D12 restatement's "what
shrinking predictive variance does to the aim and the speeds", stated by no registered source;
nothing is claimed for the exponential-average form itself.

## Open objections

None raised yet. Red should test: the positivity of every weight w^dir_{t,s} (needed for the
strict "iff" in part 3); part 2's strict inequality; and part 1's use of the information form
under the decoupled filter.

## Review

**Red, 2026-09-28.** I checked parts 1-4 by hand, tested parts 1-3 with red's own script (written without reading `checks/032/check.py`), and ran `checks/032/check.py`, which passes. The claim's results hold. There are two required corrections: one wrong asymptotic formula in part 1 and the front matter. There are also three nits.

**Hand check.**
- *Part 1.* Under block-diagonal Sigma_z, L^{-1} y = (f, r^A - B^A f, r^E - B^E f + c^E) observes lambda through f and alpha through alpha + z^A. The third block carries no information about theta. So the alpha block's information grows by sigma_A^{-2} I per quarter. This answers the third Open objection. P^alpha_0 = (s^2 + N s_bar^2) Pi_c + s^2 Pi_r, and the display follows.
- *Part 2.* The family x Pi_c + y Pi_r is a commutative algebra, so claim 030's recursion reduces to two scalar recursions.
  - F(r, a) = lambda_A - lambda_A^2/(lambda_A + r + rho a) is strictly increasing in r and increasing in a. Backward induction gives a^c >= a^r at every s >= t.
  - It is strict at every t < T when s_bar > 0, because p^c_t > p^r_t at every finite t. This answers the second Open objection.
- *Part 3.*
  - Claim 030's weights reduce to the displayed scalars, since gamma Sigma_u + rho a_{u+1} = d_u - lambda_A. They telescope to 1.
  - a_{u+1} > 0 for u + 1 <= T-1, and a_{T-1} = lambda_A gamma(sigma_A^2 + p)/(lambda_A + gamma(sigma_A^2 + p)) > 0. So every w_{t,s} with t <= s <= T-1 is strictly positive, and the strict "iff" holds. This answers the first Open objection.
  - The bounds follow from 0 < p_s <= p_t inside the convex combination. |aim| <= |alpha_hat|/(gamma sigma_A^2).
- *Part 4.* This is claim 030 4(a)'s myopic exposure.

**Independent numerical tests** (red's script, not committed). The instances are 300 random ones: N 2-5, s, s_bar and sigma_A from 0.1% to 5% (s_bar = 0 in one fifth), lambda_A from 1e-3 to 1, gamma 1-10, rho 0.9-1, T 2-14.
- Claim 030's matrix recursion runs on the full N x N fund block, including the aim recursion aim_t = (gamma Sigma_t + rho A_{t+1})^{-1}[gamma Sigma_t Markowitz_t + rho A_{t+1} aim_{t+1}] as a linear map of alpha_hat.
- Pi_c and Pi_r are invariant, and Gamma^A_t, P^alpha_t and gamma sigma_A^2 x aim match g^dir_t, p^dir_t and ell^dir_t on both eigenspaces to 2.7e-13.
- The weights are positive and sum to 1. The bounds on ell hold everywhere.
- g^c_t > g^r_t at every t when s_bar > 0, with a smallest gap of 3.2e-8, and the two are equal to 1e-12 when s_bar = 0.

**Required correction 1 (part 1's rate).** "p^c_t - p^r_t decreases to 0 like (s_bar^2 N sigma_A^4)/t^2" has the wrong constant; it is not even dimensionally right.
- The Proof's own computation gives (1/p^r - 1/p^c) p^c p^r with 1/p^r - 1/p^c = N s_bar^2/(s^2 (s^2 + N s_bar^2)). So p^c_t - p^r_t ~ N s_bar^2 sigma_A^4/(s^2 (s^2 + N s_bar^2) t^2).
- At the check's calibration (N = 3, s = s_bar = 0.35%, sigma_A = 2%), t^2 (p^c_t - p^r_t) = 0.00943 at t = 1,000 and 0.00976 at t = 10,000. The limit is 0.00980, against the Statement's 5.9e-12.
- The Proof is right; please correct the Statement's display.

**Required correction 2 (front matter).** `depends_on: []` should list claim 030, whose parts 3 and 4(a) are used. Claim 031 was corrected the same way to `[30]`.

**Nits.**
- Part 3's "equal to 1 iff p^dir_s = p^dir_t for all s >= t (no further learning)" is right as an iff, but under M5's filter p^dir_s < p^dir_t for every s > t. So the learning factor is strictly above 1 at every t < T-1 and equals 1 only at T-1. Saying so is more informative.
- In Checks, "about 3 percent (relative) to 9 percent (common, N = 3)": the common direction's prior variance is s^2 + N s_bar^2 = 4 s^2, that is 12% of sigma_A^2. The 9% is the pooled excess N s_bar^2 alone.
- The Statement and Not shown still call claim 030 "proposed"; it is approved.
- The experiment 022 figures quoted in Checks (0.66 bp with standard error 0.04, fund speeds 0.167 to 0.052 and ETF speeds 0.287 to 0.211) match red's reproduction of that experiment.

**Mechanism (4b).** The claim's own statement is right.
- The aim is `garleanu2009dynamic` Proposition 3's weighted average of expected future Markowitz positions, with a martingale signal and a deterministic, falling risk charge.
- The two speeds come from the monotonicity of the Riccati rate in the risk path (GP Proposition 2(ii)) applied on the two eigenspaces of an exchangeable covariance.
- What is new for D12 is the explicit learning factor and its bounds, the costly-versus-costless asymmetry in anticipating learning, and the common-versus-relative speed split. The mechanism is known in kind, and this is an application.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-28): red's required correction 1 finds the Statement's displayed rate for p^c_t - p^r_t wrong. The correct constant is N s_bar^2 sigma_A^4/(s^2 (s^2 + N s_bar^2) t^2), which the Proof already derives. PM does not approve a false display. Math corrects it and sets depends_on to [30], and red records a fresh verdict.

**Red, re-review of the change since red's verdict, 2026-09-28.** The only change to the claim since red's Review is 40132f1, a Checks paragraph recording experiment 024.
- The paragraph is accurate against `experiments/024-*.md`, which has status reported, not yet reproduced:
  - learning-aware minus static-belief receding horizon: 0.000 bp per quarter (standard error 0.000);
  - edge over the cost-aware myopic rule: 0.027 bp (0.004);
  - funds at zero in 91% of quarters;
  - predictive covariance moves about 0.2% over the horizon.
- It correctly limits part 3's learning factor to the unconstrained policy. No Statement or Proof text changed, so red's hand check and numerical tests still apply.
- Red's two required corrections are **not yet made**: Statement part 1's displayed rate, and `depends_on: []`. PM routed them to math (board/inbox/math/2026-09-28-claim032-corrections.md). The verdict below is conditional on them and on the nits being folded in without changing any result, as PM asked. Red re-reviews when math's revision lands.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's verdict, conditional on its two required corrections, is met on main (8ad2ca4). PM verified that Statement part 1 shows red's rate N s_bar^2 sigma_A^4/(s^2(s^2+N s_bar^2)t^2) and that depends_on is [30]; the nits are folded in with no result changed. Red's hand check of parts 1-4 and 300 random instances matching claim 030's recursion to 3e-13 stand; red's re-review found the experiment 024 paragraph accurate. Mechanism: garleanu2009dynamic Proposition 3's weighted average of future targets, with a martingale signal and a falling risk charge, plus Riccati-rate monotonicity on the two eigenspaces of an exchangeable covariance, an application. What D12 gains: the explicit learning factor, the costly-versus-costless asymmetry, and the common-versus-relative speed split. Limit: economically tiny, since the learning-aware value is 0.000 bp per quarter in the implementable space (experiment 024, pending reproduction).


Not machine checked. Scalar recursions on two eigenspaces and one convex-combination bound.

Lean, 2026-09-28 (final): parts 1-4 are machine checked, and this supersedes "not machine
checked" above. The statement is in `lean/Standalone/M5LearningAimTwoSpeeds.lean` and the proof
in `lean/Novel/M5LearningAimTwoSpeedsProof.lean`, which imports claim 030's proof module
(depends_on [30], Q-04). `lake build`, the axiom audit (standard axioms only) and
`checks/032/check.py` pass. No hypothesis structure or cited result is used.

Formal objects. The fund block is claim 030's formal problem with:
- cost lambda_A I, risk gamma(sigma_A^2 I + P^alpha_t), mean map the identity on alpha_hat, and
  no fee;
- P^alpha_t the alpha block's Kalman covariance, with observation I, noise sigma_A^2 I and prior
  s^2 I + s_bar^2 11'.

Each direction (prior variance s^2 + N s_bar^2 or s^2) carries claim 030's scalar rate, variance,
a_t, d_t, the weights w_{t,s}, ell_t and the learning factor, defined as in the Statement.

Machine checked:
- Part 1:
  - P^alpha_t = p^c_t Pi_c + p^r_t Pi_r, with both precisions growing by 1/sigma_A^2 per quarter;
  - p^c_t >= p^r_t, with equality iff s_bar^2 = 0;
  - p^c_t - p^r_t is nonincreasing and t^2 (p^c_t - p^r_t) -> N s_bar^2 sigma_A^4/(s^2(s^2 + N s_bar^2)).
- Part 2:
  - Gamma^A_t = g^c_t Pi_c + g^r_t Pi_r and A^A_t = a^c_t Pi_c + a^r_t Pi_r;
  - g^c_t >= g^r_t, with equality iff s_bar^2 = 0;
  - "the two speeds converge" is formalized as: both rates have the same stationary limit a_inf,
    in the iterated order of claim 030 part 5.
- Part 3, per direction and for t < T:
  - the weights are positive (the Statement says nonnegative) and sum to 1;
  - sigma_A^2/(sigma_A^2 + p_t) <= ell_t <= 1, and the learning factor is >= 1, with equality iff
    t = T-1;
  - the fund aim is (ell^c_t/(gamma sigma_A^2)) alpha_hat^c + (ell^r_t/(gamma sigma_A^2)) alpha_hat^r;
  - the fund Markowitz portfolio is alpha_hat^dir/(gamma(sigma_A^2 + p^dir_t)) in each direction,
    and the aim is the learning factor times it.
- Part 4 is claim 030's part 4(a) (y_t = (gamma(Sigma_f + P^lambda_t))^{-1} lambda_hat_t,
  adjusted at speed I).

Paper-level steps are claim 030's, under PM's rule-6b decision there. Not formalized: part 4's
last sentence (Not shown in the claim) and the one-sentence reading. PM's limits stand.

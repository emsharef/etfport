---
id: 36
title: "When anticipating learning or mean reversion changes today's trade: in M5's separated case the learning-aware aim exceeds the static-belief aim by the factor ell_t(sigma_A^2 + p_t)/sigma_A^2, between 1 and 1 + kappa_t/(1 - kappa_t) with kappa_t the alpha Kalman gain, and mean reversion at persistence phi scales the aim's deviation part by a weight between w_{t,t} + (1 - w_{t,t}) phi^{T-1-t} and 1, so both effects are cost effects that vanish for costless instruments and are bounded by explicit functions of the gain, the persistence, the cost and the horizon"
status: formalized
model_version: M5
depends_on: [30, 32]
axioms_used: []
formal: lean/Standalone/M5WhenAnticipationMatters.lean
direction: D15
---
## Statement

D15's criterion (a). It gives, as formulas in the inputs, when anticipating learning or mean
reversion changes today's trade, in M5's separated homogeneous case (claim 030 part 4(a), claim
032's setting): M = K with B^E invertible, ETFs costless, residual-free and fee-free,
homogeneous funds with residual variance sigma_A^2 and cost lambda_A > 0, prior alpha variance
s^2 (s_bar = 0; the pooled case is direction by direction as in claim 032), gamma > 0, rho in
(0, 1], horizon T. The benchmark is `wachter2002portfolio`: the optimal allocation under a
mean-reverting risk premium splits exactly into a myopic term and a hedging term that vanishes
when the opportunity set is constant (its equation (35) and the discussion on p. 73). What the
funded, quarterly, fund-versus-ETF structure adds is in part 4.

**Objects.** The scalar fund block: p_t the alpha posterior variance (1/p_t = 1/s^2 +
t/sigma_A^2 in the baseline), r_t = gamma (sigma_A^2 + p_t), the recursion d_t = lambda_A + r_t
+ rho a_{t+1}, a_t = lambda_A - lambda_A^2/d_t, a_T = 0, rate g_t = a_t/lambda_A, weights w_{t,s}
of claim 032 part 3 (nonnegative, summing to 1 over s = t..T-1, with the *myopic weight*
w_{t,t} = r_t/(r_t + rho a_{t+1})), and the learning factor ell_t = sum_s w_{t,s} sigma_A^2/
(sigma_A^2 + p_s). The *Kalman gain* on alpha at review t is kappa_t = p_t/(sigma_A^2 + p_t),
the weight of one quarter's residual return in the belief update. The *static-belief* manager
freezes the risk path at review t (p_s = p_t for all s >= t) and re-solves each review: its
aim is aim^S_t = alpha_hat_t/(gamma (sigma_A^2 + p_t)) and its rate g^S_t is the rate of the
recursion with constant risk r_t from t to T-1. The *learning-aware* manager's aim is aim_t =
ell_t alpha_hat_t/(gamma sigma_A^2) with rate g_t (claim 032). Today's trade is u_t = g_t
(aim_t - x_{t-1}) and u^S_t = g^S_t (aim^S_t - x_{t-1}).

1. **Learning: the aim.** aim_t = L_t aim^S_t with the learning factor

   ```
   L_t = ell_t (sigma_A^2 + p_t)/sigma_A^2,      1 <= L_t <= 1 + p_t/sigma_A^2 = 1 + kappa_t/(1 - kappa_t) = 1/(1 - kappa_t),
   ```

   with L_t = 1 iff t = T-1 (no further learning) and L_t < 1/(1 - kappa_t) strictly for t <
   T-1. So anticipating learning raises today's target position by at most the factor
   1/(1 - kappa_t): the relative change of the target exceeds a fraction theta only if the alpha
   Kalman gain exceeds theta/(1 + theta), whatever the cost, horizon and starting holding. The
   exact change L_t - 1 = sum_{s>t} w_{t,s} (p_t - p_s)/(sigma_A^2 + p_s) has summands increasing
   in s, so any shift of the weights toward later reviews raises it, and it is increasing in the
   precision still to be gained (p_t - p_s); that larger lambda_A and a longer horizon produce
   such a shift is observed on every instance tested (Not shown), not proved.

2. **Learning: the rate and the trade.** g_t <= g^S_t (a manager who anticipates a falling risk
   charge trades more slowly), with g^S_t - g_t <= g(r_t; T - t) - g(gamma sigma_A^2; T - t),
   where g(r; n) is the rate of the constant-risk recursion with risk r and n reviews to go,
   explicit and increasing in r (claim 030 part 5's monotonicity in gamma, which enters only
   through r). Hence today's trade satisfies

   ```
   u_t - u^S_t = (g_t - g^S_t)(aim^S_t - x_{t-1}) + g_t (L_t - 1) aim^S_t,
   |u_t - u^S_t| <= [g(r_t; T-t) - g(gamma sigma_A^2; T-t)] |aim^S_t - x_{t-1}| + g_t kappa_t/(1 - kappa_t) |aim^S_t|,
   ```

   and both brackets tend to zero as p_t -> 0 (the second linearly in kappa_t; the first, by
   the mean value theorem on the rate, at most (partial g/partial r) gamma p_t with the
   derivative bounded by lambda_A/(lambda_A + gamma sigma_A^2)^2 times (T - t)). Anticipating
   learning therefore changes today's trade by an amount of first order in the Kalman gain,
   with explicit constants in the cost, the risk aversion, the horizon and the position; a
   checkable condition for "material" is that the right side exceed the stated fraction of
   |u^S_t|.

3. **Mean reversion.** In M5's persistence variant with Phi_alpha = phi I (0 <= phi <= 1),
   theta_bar_alpha = alpha_bar 1 and any innovation variance Q_alpha (so p_t is the filter's
   path under that variant), E_t alpha_hat_s = alpha_bar + phi^{s-t} (alpha_hat_t - alpha_bar),
   and the fund aim is

   ```
   aim_t = sum_s w_{t,s} [ alpha_bar + phi^{s-t} (alpha_hat_t - alpha_bar) ] / (gamma (sigma_A^2 + p_s))
         = ell_t alpha_bar/(gamma sigma_A^2) + M_t(phi) ell~_t (alpha_hat_t - alpha_bar)/(gamma sigma_A^2),
   ```

   where M_t(phi) = sum_s w~_{t,s} phi^{s-t} with w~ the weights renormalized by the precision
   ratios (w~_{t,s} proportional to w_{t,s} sigma_A^2/(sigma_A^2 + p_s), ell~_t their sum before
   normalization equals ell_t); M_t is nondecreasing in phi, M_t(1) = 1 and

   ```
   w~_{t,t} + (1 - w~_{t,t}) phi^{T-1-t}  <=  M_t(phi)  <=  1,
   ```

   so anticipating mean reversion shrinks the response to the current alpha deviation by at
   most (1 - w~_{t,t})(1 - phi^{T-1-t}), where 1 - w~_{t,t} = 1 - w_{t,t} sigma_A^2/((sigma_A^2 +
   p_t) ell_t) is the renormalized weight the recursion puts on the future, at least
   1 - w_{t,t} = rho a_{t+1}/(r_t + rho a_{t+1}) when p is nonincreasing (since then ell_t >=
   sigma_A^2/(sigma_A^2 + p_t)), and zero as lambda_A -> 0 (w_{t,t} -> 1 and ell_t ->
   sigma_A^2/(sigma_A^2 + p_t)) for every phi. A checkable condition: mean reversion changes the target's
   deviation part by more than a fraction theta only if (1 - w~_{t,t})(1 - phi^{T-1-t}) > theta,
   which requires both a cost large enough that the myopic weight is below 1 - theta and a
   persistence low enough over the remaining horizon; at zero cost, never.

4. **What the funded, quarterly, fund-versus-ETF structure adds.** (i) *No hedging demand.* In
   the benchmark the hedging term exists without trading costs and vanishes only when the
   opportunity set is constant; in M5 the objective is a per-review certainty equivalent, so
   there is no hedging demand at all, and the anticipation effects of parts 1-3 are cost
   effects: both vanish as lambda_A -> 0 (part 1's L_t -> 1 since w_{t,t} -> 1; part 3's
   M_t -> 1), whatever the persistence or the learning. (ii) *Costless instruments never
   anticipate.* The ETF exposure, costless in the separated case, is re-set to the myopic
   factor-space Markowitz position every review (claim 030 part 4(a)), so premium learning and
   premium mean reversion never change today's exposure trade beyond today's estimate; only the
   costly fund positions carry anticipation. With ETF trading costs switched on the exposure
   block acquires its own factors through claim 030's coupled recursion (Not shown). (iii)
   *Quarterly bands.* Under proportional costs and caps the same anticipation appears as the
   band's outward drift and tilt (claim 100 parts 2b-2c: the target's known drift
   delta_t = mu_t (1/Sigma_{t+1} - 1/Sigma_t)/gamma is the one-review increment of the learning
   factor, and the tilt has its sign), which is mathb's criterion (b) in D15.

**One sentence without model nouns.** Looking ahead changes today's trade only where trading
is costly, and then by at most the Kalman gain's odds for learning and by at most the future's
weight in the trading rule times the persistence shortfall for mean reversion, so the check
is: is the gain, or the product of the future weight and one minus persistence to the
remaining horizon, above the fraction one calls material; costless positions never look ahead,
and there is no hedging demand to add.

## Proof

### 1. The aim

Claim 032 part 3 gives aim_t = ell_t alpha_hat_t/(gamma sigma_A^2) and the bounds sigma_A^2/
(sigma_A^2 + p_t) <= ell_t <= 1 with the strictness at t < T-1; dividing by aim^S_t = alpha_hat_t/
(gamma (sigma_A^2 + p_t)) gives L_t and its bounds, and 1 + p_t/sigma_A^2 = (sigma_A^2 +
p_t)/sigma_A^2 = 1/(1 - kappa_t) with kappa_t = p_t/(sigma_A^2 + p_t) the Kalman gain: the
scalar update m_{t+1} = m_t + kappa_t (y_{t+1} - m_t) has gain p_t/(p_t + sigma_A^2). The exact
form L_t - 1 = sum_s w_{t,s} [(sigma_A^2 + p_t)/(sigma_A^2 + p_s) - 1] = sum_{s>t} w_{t,s}
(p_t - p_s)/(sigma_A^2 + p_s) (the s = t term vanishes). The threshold statement: L_t - 1 > theta
requires kappa_t/(1 - kappa_t) > theta, that is, kappa_t > theta/(1 + theta).

### 2. The rate and the trade

The static-belief rate g^S_t solves the recursion with r_s = r_t for all s >= t, and r_t >= r_s
for s >= t; claim 032 part 2's monotonicity (the scalar rate is nondecreasing in the whole
future risk path) gives g^S_t >= g_t, and, comparing with the constant path r_s = gamma
sigma_A^2 <= r_s for all s, g_t >= g(gamma sigma_A^2; T - t); hence 0 <= g^S_t - g_t <= g(r_t;
T - t) - g(gamma sigma_A^2; T - t). The trade identity is algebra: u_t - u^S_t = g_t (L_t
aim^S_t - x_{t-1}) - g^S_t (aim^S_t - x_{t-1}). The derivative bound: for the constant-risk
recursion, partial g_t/partial r is at most lambda_A/d^2 summed over the T - t reviews (each
step's r-derivative is lambda_A/d^2 and its a-derivative rho lambda_A^2/d^2, as in claim 030
part 5's proof, composed along the recursion, with d >= lambda_A + gamma sigma_A^2), giving the
displayed factor; the mean value
theorem on r in [gamma sigma_A^2, r_t] gives the O(p_t) statement.

### 3. Mean reversion

Under Phi_alpha = phi I with theta_bar, E_t theta_s = alpha_bar + phi^{s-t} (theta_t - alpha_bar)
componentwise, and E_t m_s = E_t E[theta_s | I_s] = E_t theta_s by the tower property, evaluated
at m_t: E_t alpha_hat_s = alpha_bar + phi^{s-t}(alpha_hat_t - alpha_bar). Lemma (claim 030's
recursion under persistence): claim 030 part 3's backward verification uses the mean dynamics
only through E_t J_{t+1}(x_t, m_{t+1}) = -(1/2) x_t' A_{t+1} x_t + x_t' (C_{t+1} E_t m_{t+1} +
c_{t+1}) + E_t q_{t+1}, so with E_t m_{t+1} = Phi m_t + (I - Phi) theta_bar in place of m_t the
same induction gives the same A_t and D_t, the coefficient recursions C_t = Lambda D_t^{-1}
(G + rho C_{t+1} Phi) and c_t = Lambda D_t^{-1} (rho C_{t+1} (I - Phi) theta_bar + rho c_{t+1} -
e_E c^E), and the aim recursion aim_t = (gamma Sigma_t + rho A_{t+1})^{-1} [gamma Sigma_t
Markowitz_t + rho A_{t+1} E_t aim_{t+1}] with aim_{t+1} evaluated at E_t m_{t+1} (as claim 031
extended it to a time-varying G_t; red's exact LQ confirms it). It unrolls to
aim_t = sum_s W_{t,s} E_t Markowitz_s = sum_s w_{t,s} E_t alpha_hat_s/(gamma (sigma_A^2 +
p_s)) in the scalar block (the p_s path is whatever the filter produces under Q_alpha; the
weights are claim 032's with that path). Substituting E_t alpha_hat_s and collecting the
alpha_bar and deviation terms gives the display, with w~_{t,s} = w_{t,s} sigma_A^2/(sigma_A^2 +
p_s)/ell_t summing to 1. M_t(phi) = sum_s w~_{t,s} phi^{s-t} is a convex combination of
phi^{s-t} in [phi^{T-1-t}, 1], nondecreasing in phi, equal to 1 at phi = 1, and at least
w~_{t,t} + (1 - w~_{t,t}) phi^{T-1-t} since phi^{s-t} >= phi^{T-1-t}. The cost limit: as
lambda_A -> 0, a_{t+1} -> 0 and w_{t,t} = r_t/(r_t + rho a_{t+1}) -> 1, so w~_{t,t} -> 1 and
M_t -> 1.

### 4. Structure

(i) is the definition of M5's objective (a discounted sum of per-review certainty equivalents,
no terminal utility), under which the optimal policy is claim 030's certainty-equivalent rule
with no intertemporal hedging term, and the two limits are parts 1 and 3's. (ii) is claim 030
part 4(a): the exposure block is a static maximization each review. (iii) is claim 100 parts
2b-2c read against part 1: delta_t = mu_t (1/Sigma_{t+1} - 1/Sigma_t)/gamma is, in the scalar
fund block, alpha_hat_t [1/(sigma_A^2 + p_{t+1}) - 1/(sigma_A^2 + p_t)]/gamma, the one-step
increment of the learning factor's numerator (sigma_A^2 + p_t)/(sigma_A^2 + p_{t+1}) - 1 times
aim^S_t.

## Checks

`checks/036/check.py` (exits non-zero on failure; a check, not a proof). On scalar fund blocks
over grids of (s^2/sigma_A^2, lambda_A, gamma, T, phi, x_{t-1}, alpha_hat_t): part 1's identity
and bounds, with L_t against 1/(1 - kappa_t) and the threshold kappa_t > theta/(1 + theta);
part 2's rate ordering and the trade bound; part 3's aim under an AR(1) alpha (computed by the
affine recursion with E_t m_{t+1} = phi m_t + (1 - phi) alpha_bar, independently of the weight
formula), the M_t(phi) bounds, monotonicity in phi and the zero-cost limit; and the equity-style
and fixed-income-style points as illustrations only (rule 22).

## Not shown

- ETF trading costs on (the exposure block's own anticipation factors through the coupled
  recursion), heterogeneous funds, and the pooled prior beyond the direction-by-direction
  reading.
- The band world's counterpart beyond the citation of claim 100 (proportional costs and caps
  change the trade from a rate times a gap to a projection onto a band; the anticipation
  condition there is mathb's criterion (b)).
- Whether the O(p_t) constant in part 2 is sharp; the exact expression is given.
- Monotonicity of L_t in lambda_A and in the horizon: observed on every instance tested by red
  (3,000) and by the check, not proved (claim 032 lists the same for ell_t).
- Persistence in the premia (Phi_lambda != I) affects only the costless exposure block in the
  separated case and therefore never changes today's exposure trade beyond today's estimate;
  with ETF costs it would, and that is not stated.

## Prior art

Mechanism: In a rule that trades a fraction of the way toward a target built from expected future
optima, looking ahead changes today's trade only through the weight the rule puts on the
future, which is zero without trading costs; its size for learning is bounded by the odds of
the Kalman gain and for mean reversion by that future weight times the persistence shortfall,
with no separate hedging term because the objective has no intertemporal risk preference.

General results checked: `wachter2002portfolio` (equation (35), p. 73: the myopic-plus-hedging
split in continuous time with a mean-reverting Sharpe ratio; the hedging term is a preference
effect present without costs and absent with a constant opportunity set), the benchmark, which
part 4(i) contrasts; `garleanu2009dynamic` Proposition 4 (signals weighted by their decay: part
3's M_t(phi) is their scaling factor in finite-horizon, time-varying-risk form, with the exact
bounds new); `kimomberg1996dynamic` (registered wanted, no text: the closed-form nonmyopic demand under a
mean-reverting premium; named as the roadmap's benchmark, not read and not relied on); claims 030 and 032 (the rule and the learning
factor), claim 100 (the band's drift and tilt under learning, mathb).

Searched: claims 009, 029-035, 100, the D15 ROADMAP and FINDINGS entries, refs/text for
`wachter2002portfolio` and `garleanu2009dynamic`, and the refuted directory. This is a claim
because criterion (a) asks for the condition in the inputs, and the Kalman-gain bound, the
future-weight bound and the no-hedging contrast are stated by no source; the formulas are read
off claims 030 and 032 and the persistence extension of their aim recursion.

## Open objections

PM's withdrawal (claim 036): red's required corrections 1-3 made.

Red (review, red-passed with three required corrections and three nits; verdict withdrawn by
PM pending them; all made on math/claim036-corrections): part 3's future weight is stated
exactly, 1 - w~_{t,t} = 1 - w_{t,t} sigma_A^2/((sigma_A^2 + p_t) ell_t), at least 1 - w_{t,t}
for a nonincreasing p (the "at most" clause pointed the wrong way, red's counterexample);
part 2's constant-risk rate is increasing in r; part 1's monotonicity in lambda_A and the
horizon is marked observed in Not shown; the r-derivative is lambda_A/d^2; the persistence
extension of claim 030's recursion is stated as a lemma; kimomberg1996dynamic is marked wanted
and not relied on. Red should re-test: the tower-property step for E_t m_s under persistence (the
filter is linear and the state Gaussian, so m_s = E[theta_s | I_s] and E_t m_s = E_t theta_s);
the derivative bound in part 2; and the renormalized weights w~ in part 3.

## Review

**Red, 2026-09-29.** I checked parts 1-4 by hand, tested parts 1-3 with red's own scripts (not reading `checks/036/check.py`), including an exact LQ solution of the persistence variant that is independent of the weight formula, and ran `checks/036/check.py`, which passes. The main results hold:
- the learning factor 1 <= L_t < 1/(1 - kappa_t);
- the rate ordering g(gamma sigma_A^2; T - t) <= g_t <= g^S_t and the trade bound;
- the persistence aim formula and 1 >= M_t(phi) >= w~_{t,t} + (1 - w~_{t,t}) phi^{T-1-t};
- the zero-cost limits.

Three Statement sentences are wrong or unproved. They are required corrections, and none touches a displayed main bound.

**Hand check.**
- *Part 1* follows from claim 032 part 3's bounds on ell_t divided by aim^S_t. The odds identity 1 + p_t/sigma_A^2 = 1/(1 - kappa_t) holds with kappa_t = p_t/(sigma_A^2 + p_t), the scalar Kalman gain.
- *Part 2.* g^S_t >= g_t >= g(gamma sigma_A^2; T - t) follows from claim 032 part 2's monotonicity in the risk path.
  - For the constant-risk recursion g_t = (r + rho lambda_A g_{t+1})/d, so dg_t/dr = lambda_A/d^2 + (rho lambda_A^2/d^2) dg_{t+1}/dr. Summing with rho lambda_A^2/d^2 <= 1 and d >= lambda_A + gamma sigma_A^2 gives the displayed (T - t) lambda_A/(lambda_A + gamma sigma_A^2)^2 bound. This answers Open objection 2.
  - The Proof's "each step's derivative -r/d^2" is the lambda_A-derivative; the r-derivative is lambda_A/d^2.
- *Part 3.*
  - Under the persistence variant m_s = E[theta_s | I_s], so E_t m_s = E_t theta_s = alpha_bar + phi^{s-t}(m_t - alpha_bar) by the tower property (Open objection 1).
  - Claim 030's Riccati A_t does not depend on the mean dynamics, and the aim recursion needs only E_t aim_{t+1} = aim_{t+1}(E_t m_{t+1}).
  - w~ = w x (precision ratio)/ell sums to 1 (Open objection 3), and M_t is a convex combination of phi^{s-t} in [phi^{T-1-t}, 1].
- *Part 4(iii).* The one-step learning drift delta_t equals aim^S_t [(sigma_A^2 + p_t)/(sigma_A^2 + p_{t+1}) - 1].

**Independent numerical tests** (red's scripts, not committed).
- *Part 1.* On 3,000 random instances (gamma 1-10, rho 0.8-1, s^2/sigma_A^2 from 0.01 to 10, T 2-19, lambda_A from 1e-4 to 10), 1 <= L_t < 1/(1 - kappa_t) holds throughout.
- *Part 2.* On 3,000 instances, g(gamma sigma_A^2; T - t) <= g_t <= g^S_t and the derivative bound hold. The constant-risk rate is never decreasing in r.
- *Part 3.* Red solved the scalar LQ problem with m' = phi m + (1 - phi) alpha_bar + noise exactly, by its own backward value recursion (aim = (L m + l)/(1 - K)), on 2,000 instances with random phi in [0, 1] and Q_alpha from 0 to 1.5 times the stationary level.
  - The displayed aim, ell_t alpha_bar/(gamma sigma_A^2) + M_t(phi) ell_t (alpha_hat_t - alpha_bar)/(gamma sigma_A^2), matches it to 1e-8 in every case.
  - The M_t(phi) bounds hold in every case.

**Required correction 1 (part 3's "at most 1 - r_t/(r_t + rho a_{t+1}) in general").**
- 1 - w~_{t,t} is not bounded by 1 - w_{t,t}. With learning, w~_{t,t} = w_{t,t} [sigma_A^2/(sigma_A^2 + p_t)]/ell_t <= w_{t,t}, because ell_t >= sigma_A^2/(sigma_A^2 + p_t) when p_s <= p_t. So the inequality points the other way.
- It fails in 1,449 of red's 2,000 persistence instances. A clean case without persistence: lambda_A 0.1, gamma 5, rho 1, sigma_A^2 = s^2 = 4e-4, T 5, t 0 gives w_{t,t} = 0.310 and w~_{t,t} = 0.229, so 1 - w~_{t,t} = 0.771 > 1 - w_{t,t} = 0.690.
- Please state 1 - w~_{t,t} = 1 - w_{t,t} sigma_A^2/((sigma_A^2 + p_t) ell_t), which is at least 1 - w_{t,t} when p is nonincreasing, or drop the "at most" clause. The zero-cost limit is unaffected, since w_{t,t} -> 1 and ell_t -> sigma_A^2/(sigma_A^2 + p_t).

**Required correction 2 (part 2's "g(r; n) ... explicit and decreasing in r").**
- The constant-risk rate is increasing in r: claim 030 part 5 has g increasing in gamma, and red found it never decreasing.
- The part's own bound, g^S_t - g_t <= g(r_t) - g(gamma sigma_A^2) >= 0 with r_t >= gamma sigma_A^2, uses that.
- Please change "decreasing" to "increasing".

**Required correction 3 (part 1's monotonicity assertion).**
- "L_t - 1 ... is increasing in the weight the recursion puts on later reviews (larger lambda_A, longer horizon)". The first half is right: the summands (p_t - p_s)/(sigma_A^2 + p_s) increase in s, so a first-order shift of the weights to later reviews raises the sum.
- The parenthesis asserts that larger lambda_A and a longer horizon produce such a shift, and nothing proves it. Claim 032 lists monotonicity of ell in lambda_A under Not shown.
- Red found L_t monotone in lambda_A and in T in all 3,000 of its instances, so it is plausibly true.
- Please prove it, or mark it as observed (Not shown).

**Nits.**
- Part 2's Proof says "each step's derivative -r/d^2", which is the lambda_A-derivative; the r-derivative is lambda_A/d^2. The bound itself is right.
- Part 3 relies on claim 030's aim recursion under persistence, which claim 030 states only for the martingale baseline. The extension is sound (A_t does not depend on the mean dynamics) and red's exact LQ confirms it. Please state it as a one-line lemma, as claim 031 did for a time-varying G.
- `kimomberg1996dynamic` is cited by title only while not read. Rule 6 wants a ledger entry, or the citation marked as wanted.

**Mechanism (4b).**
- It is certainty-equivalent partial adjustment toward an aim that is a weighted average of expected future Markowitz positions: `garleanu2009dynamic` Proposition 3-4 in finite-horizon, time-varying-risk form.
- It is contrasted correctly with `wachter2002portfolio`, whose hedging demand is a preference effect that M5's per-review objective does not have.
- What is new for D15 criterion (a) is the explicit bounds: the Kalman-gain odds for learning, the future-weight times persistence-shortfall for mean reversion, and zero at zero cost. It is an application, and elementary.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's three required corrections are to the Statement. Part 3's 'at most 1 - w_{t,t}' points the wrong way (1,449 of 2,000 counterexamples); part 2's rate is increasing, not decreasing, in r; and part 1's monotonicity in lambda_A and horizon is unproved. Math revises and red records a fresh verdict.

**Red, recheck of math's revision (ead6e2e), 2026-09-29.** All three required corrections and the three nits are made correctly, and no main bound changed.
- *Correction 1.* Part 3 now states the future weight exactly: 1 - w~_{t,t} = 1 - w_{t,t} sigma_A^2/((sigma_A^2 + p_t) ell_t). This is at least 1 - w_{t,t} when p is nonincreasing, the direction red's counterexample showed, and it tends to zero as lambda_A -> 0 because ell_t -> sigma_A^2/(sigma_A^2 + p_t).
- *Correction 2.* Part 2's constant-risk rate is now increasing in r.
- *Correction 3.* Part 1 keeps the proved statement: the summands increase in s, so any later-shift of the weights raises L_t - 1. The lambda_A and horizon monotonicity is marked observed (Not shown).
- *Nits.*
  - The r-derivative is lambda_A/d^2.
  - The persistence lemma is now stated. Its coefficient recursions, C_t = Lambda D_t^{-1}(G + rho C_{t+1} Phi) and c_t = Lambda D_t^{-1}(rho C_{t+1}(I - Phi) theta_bar + rho c_{t+1} - e_E c^E), are the ones red's exact LQ used (L = (1 + rho C phi)/D and l = rho (C (1 - phi) alpha_bar + c)/D in the scalar block), with A_t unchanged.
  - `kimomberg1996dynamic` is in refs/BIBLIOGRAPHY.md and is marked wanted, not relied on.
- `checks/036/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's recheck of math's revision (ead6e2e) is sound. Part 3 states the future weight exactly (at least 1 - w_{t,t} when p is nonincreasing, the direction red's counterexample showed); part 2's constant-risk rate is increasing in r; part 1 keeps the proved later-shift monotonicity and marks the lambda_A and horizon monotonicity observed. The persistence lemma is stated with the coefficient recursions red's exact LQ used; kimomberg1996dynamic is marked wanted; the check passes. Red's earlier tests stand: 3,000 instances for parts 1-2, and 2,000 exact persistence solves matching the aim to 1e-8. Mechanism: certainty-equivalent partial adjustment toward a weighted average of future Markowitz positions (garleanu2009dynamic Propositions 3-4, finite-horizon and time-varying), contrasted correctly with wachter2002portfolio's preference-driven hedging, an application. New for D15 criterion (a): explicit bounds in the inputs, the Kalman-gain odds for learning and future weight times persistence shortfall for mean reversion, both zero at zero cost.


Not machine checked. Algebra on claim 032's weights, one monotonicity argument and a convex
combination bound.

Lean, 2026-09-29 (final): parts 1-4 are machine checked except the steps listed below as
paper-level (scope note to PM in this branch). The statement is in
`lean/Standalone/M5WhenAnticipationMatters.lean` and the proof in
`lean/Novel/M5WhenAnticipationMattersProof.lean`, which imports claim 032's proof module
(depends_on [30, 32], Q-04). `lake build`, the axiom audit (standard axioms only) and
`checks/036/check.py` pass. No hypothesis structure or cited result is used.

Formal objects. One fund or direction of the separated block with a general positive precision
path p (`Blk`): claim 032's recursion, weights and learning average, the learning factor L_t, the
gain kappa_t, the renormalized weights and M_t(phi). `cg r n` is the constant-risk rate. On the
baseline path p_t = pvar s^2 sigma_A^2 t every object is claim 032's (`Link`), so claim 032's
`FundAim` (aim = ell_t alpha_hat/(gamma sigma_A^2)) applies.

Machine checked:
- Part 1, for a nonincreasing positive path:
  - aim_t = L_t aim^S_t, 1 <= L_t < 1/(1 - kappa_t) = 1 + p_t/sigma_A^2;
  - the exact form L_t - 1 = sum_{s>t} w_{t,s}(p_t - p_s)/(sigma_A^2 + p_s);
  - L_t = 1 iff t = T-1 for a strictly decreasing path;
  - the threshold: L_t - 1 > theta >= 0 forces kappa_t > theta/(1 + theta).

  The strict upper bound holds at every t, including T-1.
- Part 2:
  - cg(gamma sigma_A^2; T-t) <= g_t <= g^S_t = cg(r_t; T-t);
  - cg is strictly increasing in r (n >= 1) and Lipschitz with constant n lambda_A/(lambda_A + m)^2
    above m >= 0, so g^S_t - g_t <= (T-t) lambda_A/(lambda_A + gamma sigma_A^2)^2 gamma p_t;
  - the trade identity and the trade bound.
- Part 3, given the aim formula:
  - the split into the long-run part and M_t(phi) times the deviation part;
  - the renormalized weights form a probability, M_t(1) = 1, and M_t is nondecreasing on [0, 1];
  - w~_{t,t} + (1 - w~_{t,t}) phi^{T-1-t} <= M_t(phi) <= 1;
  - w_{t,t} = r_t/(r_t + rho a_{t+1}), and 1 - w_{t,t} <= 1 - w~_{t,t} for a nonincreasing path.
- Part 4(i): as lambda_A -> 0, w_{t,t} -> 1, L_t -> 1 and M_t(phi) -> 1 for every phi.
- Part 4(ii): claim 030's `Separation`.
- Part 4(iii): the drift identity linking claim 100's delta_t to the learning factor's one-step
  increment.

Paper-level:
- part 3's aim formula under persistence, from the tower property E_t alpha_hat_s =
  alpha_bar + phi^{s-t}(alpha_hat_t - alpha_bar) on the Gaussian model and the claim's lemma
  extending claim 030's recursion to Phi_alpha = phi I (a new verification step, not formalized
  here);
- part 4(i)'s reading that M5's objective has no hedging demand (its definition);
- part 4(iii)'s reading against claim 100's band, and the Checks.

Lean, 2026-09-29 (persistence lemma, at PM's request): the persistence lemma is machine checked in
the same files, and this supersedes "not formalized here" in the note above. Claim 030's recursion
and Bellman verification are extended to affine mean dynamics E_t m_{t+1} = Phi m_t + b:
- `Persistence`: A_t is claim 030's, and the coefficients C_t = Lambda D_t^{-1}(G_t + rho C_{t+1} Phi)
  and c_t = Lambda D_t^{-1}(rho(C_{t+1} b + c_{t+1}) - e) give a value J that satisfies the Bellman
  equation, with the affine policy its unique maximizer, at every review and state;
- `PersistAim`: the policy is partial adjustment at claim 030's rate toward
  aim_t = sum_s W_{t,s} Markowitz_s(E_t m_s), with E_t m_{t+d} = Phi^d m_t + sum_{j<d} Phi^j b;
- `PersistLink`: in the scalar fund block with Phi = phi and b = (1 - phi) alpha_bar, this aim is
  part 3's sum_s w_{t,s}[alpha_bar + phi^{s-t}(alpha_hat_t - alpha_bar)]/(gamma(sigma_A^2 + p_s)), the formula
  formal part 3 starts from.

Still paper-level: that M5's persistence variant has E_t m_{t+1} = Phi m_t + b (the tower property
on the Gaussian model), which enters Lean as the hypothesis `AffineMean`, and the step from the
Bellman equation to all measurable policies, as in claim 030. `lake build`, the axiom audit
(standard axioms only) and `checks/036/check.py` pass.

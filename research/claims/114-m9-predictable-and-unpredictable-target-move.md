---
id: 114
title: "Time-varying premia and alphas (M9): the target's move splits into a predictable part, known today in Phi, Q, theta_bar, the beliefs and the risk-charge change, and an innovation part with the filter's propagated innovation covariance; the band leans toward the predictable move by the probability that the innovation is smaller than the predictable move (the excess of the probability that it does not overturn the move over the probability that it does); a predictable rise (fall) that tomorrow's trade cannot avoid is front-loaded (back-loaded) today when the budget is slack, its incumbent value pinned at the bracket's end, and enters tomorrow's funding need as a planned purchase otherwise, while the reserve rules depend on the unpredictable part through the innovation law; the two-review criteria transfer verbatim, claim 100's rising width and outward drift do not, holding only while learning outweighs the state noise"
status: formalized
model_version: M9
depends_on: [029, 044, 046, 047, 100, 110, 112, 113]
axioms_used: [AX-10, AX-13]
formal: lean/Standalone/M9PredictableTargetMove.lean
direction: D24
---
## Statement

D24's first claim (LAB_REQUEST_2 item 6). In M9 (model/SPEC.md: M8 with M5's state equation,
Phi != I or Q != 0) the target moves because premia and alphas move, not only because beliefs
are revised. This claim writes the target's move as a predictable part and an unpredictable
part in the inputs (part 1), says how each enters the needed flexibility (parts 2-3: the
predictable part tilts the band and is front- or back-loaded today, or becomes a planned
purchase; the unpredictable part is what the reserve rules of claims 047 and 113 price), and
states what transfers from the fixed-means case and what does not (part 4). The kill
benchmark (the fixed-means rule with the revision variance replaced by the target's innovation
variance, nothing from the predictable move) fails on parts 1-3.

**Setting.** M9 as written, one fund and one ETF (N funds where a part says so, by claim 113's
reduction): loadings b_A, b_E > 0, drag c^E, Phi = diag(phi_lambda, phi_alpha), Q = diag(q_lambda, q_alpha),
theta_bar, the filter (K_t, P_t, P^u_t, V_t), predictive moments (mu_t, Sigma_t), the target
x*_t, reviews t = 0, 1 and marking at 2 (or t = 0..T-1 for part 2), the finite-law variant with
its public tree unless said otherwise, claim 044's objects (eta_0, eta_1(z'), eta_hat_0, the
incumbent values S_i) and claim 110's coordinates at each review. Write Delta^p_0 and
Delta^u_1 for M9's target decomposition, c_t = gamma Sigma_{t,ii} for an instrument's curvature,
and mu^p_1 = G(Phi m_0 + (I - Phi) theta_bar) - (0, c^E) for tomorrow's *predictable mean*.

### Part 1. The target's move in the inputs, and the static width's direction

1a. *Decomposition.* x*_1 - x*_0 = Delta^p_0 + Delta^u_1 with

    ```
    Delta^p_0 = (gamma Sigma_1)^{-1} G (Phi - I)(m_0 - theta_bar) + [ (gamma Sigma_1)^{-1} - (gamma Sigma_0)^{-1} ] mu_0,
    Delta^u_1 = (gamma Sigma_1)^{-1} G Phi K_0 nu_1,     E Delta^u_1 = 0,     Cov Delta^u_1 = (gamma Sigma_1)^{-1} G V_0 G' (gamma Sigma_1)^{-1},   V_0 = Phi (P_0 - P^u_0) Phi',
    ```

    Delta^p_0 known at review 0 (Sigma_1 is deterministic) and Delta^u_1 centred with the
    displayed covariance under either law (unconditionally under the finite law; a martingale
    difference under the Gaussian law). The predictable part has two sources: the mean's pull
    toward theta_bar at rate I - Phi, and the risk-charge change, which now has either sign.
1b. *The static width's direction.* Sigma_1 - Sigma_0 = G (P_1 - P_0) G' with
    P_1 - P_0 = Q - (P_0 - Phi P^u_0 Phi'). If the state noise Q is below what learning removes
    in the positive semidefinite order (P_1 <= P_0), every instrument's curvature c_t falls
    and every static width (kappa^+_i + kappa^-_i)/c_t of claim 029 rises (weakly), claim
    100's 2a; if Q is above it (P_1 >= P_0), every width falls; when the two blocks move in
    opposite directions an instrument's width goes with its own loadings' combination
    (b_i^2 times the lambda block's change plus, for the fund, the alpha block's), so the fund's
    width can rise while Q is not psd-below (lean's instance: a noise-dominant lambda block and
    a learning-dominant alpha block, b_A = 0.9), and the ETF's width, which sees the lambda
    block only, rises iff q_lambda < p^lambda_0 - phi_lambda^2 p^{u,lambda}_0. Per instrument the
    exact statement is: instrument i's width rises from t to t + 1 iff
    (G (Q - (P_t - Phi P^u_t Phi')) G')_{ii} < 0, that is, sum_k G_{ik}^2 (Q - (P_t - Phi P^u_t Phi'))_{kk} < 0
    with P diagonal; the PSD order is the sufficient condition for every instrument at once
    (red's counterexample at M8's inputs with Q = diag(0, 1e-4): the fund's width falls while the
    ETF's rises, and neither PSD relation holds). P_t converges: each block's recursion
    p_{t+1} = phi^2 p_t s/(p_t + s) + q (s the block's observation noise variance) is increasing
    and concave in p_t and bounded by phi^2 s + q, so its iterates are monotone and converge to
    a fixed point, unique when q > 0 or phi^2 < 1 (a concave map with value q at zero crosses
    the diagonal once); at the fixed point the widths are constant, and AX-10's Theorem 2.1
    gives that steady-state filter's form under its own hypotheses (cited for the form only).
    So claim 100's rising width and outward drift are the learning-dominant case, instrument
    by instrument, and in the steady state the band is claim 029's for a stationary moving
    target.

### Part 2. The band leans toward the predictable move

In the coarse regime of claim 029's 1d at (t, z) (its sufficient primitive condition: every
outcome moves the target across the static band), the one-instrument band is the static band
shifted by claim 029's tilt tau_t = beta (kappa^+ U - kappa^- D)/c_t, where now

```
U = P( Delta^u_{t+1,i} > -Delta^p_{t,i} | z ),     D = P( Delta^u_{t+1,i} < -Delta^p_{t,i} | z ),
```

the probabilities that the innovation does not, respectively does, overturn the predictable
move (claim 100's 2c with Delta^p in place of the learning drift). Under a symmetric innovation
law and kappa^+ = kappa^- = kappa, tau_t is zero or has the sign of Delta^p_{t,i}, with

```
|tau_t| = beta kappa P( |Delta^u_{t+1,i}| <= |Delta^p_{t,i}| | z ) / c_t,
```

when the innovation's conditional law has no atom at -Delta^p_{t,i} (in general U - D is the
half-open probability P(-|Delta^p| < Delta^u <= |Delta^p|), the display less the atom's mass at
-|Delta^p|, for Delta^p > 0, and its mirror), so the band leans toward the predictable move by
the probability that the innovation is smaller than the predictable move, the excess U - D of
the probability that it does not overturn the move over the probability that it does (not U
itself, which is at least one half and is one half at Delta^p = 0 where the tilt is zero), up to
beta kappa/c_t when the
predictable move exceeds the innovation's support (then U = 1 or D = 1: the whole band shifts
by beta kappa/c_t in the move's direction). This is
the predictable part's effect on today's no-trade decision in the inputs; with Phi = I and
Q = 0 it is claim 100's 2c.

### Part 3. Front-loading, back-loading and the planned purchase

3a. *Front-loading a predictable rise.* Suppose today's budget is slack at the dynamic root and
    at the myopic root and tomorrow's budget is slack in every state (eta_0 = eta_1 = 0), the
    ETF's holding is fixed (or absent), kappa^+_A > 0, and the fund is bought in every state
    tomorrow from the *myopic* root's marked holding (the predictable rise exceeds the
    innovation's support there: lo_{1,A}(z') > g_A(z') a^my_0 for every z', a condition
    checkable before solving the dynamic problem). Then the myopic policy's tomorrow pins the
    fund's incumbent value at its upper bracket, S_A = beta E[g_A] kappa^+_A > 0, and the
    dynamic root holds at least the myopic root's fund, a^dyn_0 >= a^my_0. The threshold
    reading is at the dynamic root with its *own* incumbent value S^dyn_A, read from the
    dynamic root's tomorrow: since s_A(z') <= kappa^+_A in every state, S^dyn_A <= beta E[g_A] kappa^+_A,
    and on a purchase the dynamic root line g_{0,A}(a^dyn_0) + S^dyn_A = kappa^+_A gives a
    purchase threshold kappa^+_A - S^dyn_A >= (1 - beta E[g_A]) kappa^+_A, with equality iff the
    dynamic root's tomorrow has slope kappa^+_A in every state, that is, every state buys the
    fund from the dynamic root's marked holding (lo_{1,A}(z') > g_A(z') a^dyn_0) or holds it at
    its purchase edge (idle strictly inside with g_{1,A} = kappa^+_A, or idle at the cap with
    g_{1,A} >= kappa^+_A; lean's precision), and in particular if every state buys: the
    predictable rise is bought today at a
    threshold cut by at most beta E[g_A] kappa^+_A, the cut being the full one when even the
    front-loaded holding is bought again in every state, because tomorrow would pay the rate
    anyway. The front-loading itself makes tomorrow's purchase less likely from the larger
    holding, so the full cut is the exception (the analyst's experiment 057: in 24 of 24 cells
    with the myopic condition the order held while the dynamic root's tomorrow traded in only
    4 to 14 of 16 states, the threshold lying strictly between the two ends).
3b. *Back-loading a predictable fall.* Mirror, with kappa^-_A > 0 and the fund sold in every
    state tomorrow from the myopic root's marked holding: S_A = -beta E[g_A] kappa^-_A < 0 and
    a^dyn_0 <= a^my_0; at the dynamic root, S^dyn_A >= -beta E[g_A] kappa^-_A, so on a sale its
    threshold -kappa^-_A - S^dyn_A <= -(1 - beta E[g_A]) kappa^-_A, with equality iff the dynamic
    root's tomorrow has slope -kappa^-_A in every state (every state sells the fund from the
    dynamic root's marked holding, or holds it at its sale edge).
3c. *With the ETF free.* The sign of the fund's move is claim 113's 3b: S_A corrected by the
    exposure price's and the cash price's changes, r_A (m^dyn_0 - m^my_0) - (eta_hat_0 - eta^my_0)(1 + kappa),
    so the ETF's own predictable move can offset the fund's through the shared exposure price.
3d. *The planned purchase and the reserve.* Tomorrow's solo target for the fund is
    x_hat_A(z') = ( mu^p_{1,A} + (G Phi K_0 nu_1)_A - kappa^+_A )^+/(gamma Sigma_{1,AA}), so the
    funding need of claims 046-047 and claim 113 at a state is

    ```
    need(z') = (1 + kappa^+_A) ( x_hat_A(z') - g_A(z') a_0 )^+ + (the ETF's term),    x_hat_A(z') = ( mu^p_{1,A} + (G Phi K_0 nu_1(z'))_A - kappa^+_A )^+/(gamma Sigma_{1,AA}),
    ```

    whose value at nu_1 = 0 with the worst marking, the *planned purchase*
    (1 + kappa^+_A)(x_hat^p_A - g^min_A a_0)^+ with x_hat^p_A = (mu^p_{1,A} - kappa^+_A)^+/(gamma Sigma_{1,AA}),
    is a deterministic base set by the predictable mean, the innovation contributing the
    difference need(z') minus that base (the positive parts do not split: the sum form holds
    only where mu^p_{1,A} - kappa^+_A >= 0 and the innovation keeps the target above the marked
    holding). The reserve rules transfer with
    the innovation law: claim 047's largest need and claim 113's aggregate no-reserve test use
    need(z') as displayed, so the *unpredictable* part is what the reserve prices, through the
    innovation covariance of 1a (the kill benchmark's replacement), while the predictable part
    is either front-loaded (3a, budget slack today) or, when today's budget binds, a planned
    purchase that tomorrow's liquidity must cover, best provided by the ETF's sale (claim 047's
    ETF-against-cash reading) since its size is known today. A predictable fall that exceeds
    the innovation's support needs no reserve at all: the fund is sold in every state, which
    raises cash; a smaller fall leaves states that still buy the fund, and their need counts.

### Part 4. What transfers and what does not

- *One-review results* (claims 102, 104, 106, 109-111, 040-041): at each review with the
  current (mu_t, Sigma_t), under either law, as in claim 112's part 3.
- *Two-review results on the finite tree* (claims 044, 046, 047, 113): verbatim, since their
  hypotheses are on the public tree with the given (mu_1(z'), Sigma_1) law; M9 changes the law
  of tomorrow's moments, not the program. So today's lines are claim 110's with alpha~ + S at
  (m_0, eta_hat_0), the cash-price and incumbent-value bounds hold, and the reserve rules read
  with 3d's need.
- *Claim 029's band* (M6, any public-state law): verbatim at every review, with c_t = gamma Sigma_{t,ii}
  from M9's P_t path; its tilt is part 2.
- *Claim 100's 2a-2d* (rising width, outward drift, pure learning ending the coarse regime):
  while the instrument's width rises, (G (Q - (P_t - Phi P^u_t Phi')) G')_{ii} < 0 (1b, per
  instrument; the PSD order gives it for all instruments); in the steady state the width is
  constant, the risk-charge drift is zero and the coarse regime is not ended by learning.
  Claim 100's 1a-1d (the transfer of claim 029 to a time-varying covariance) hold.
- *M5's results* (claims 030-032, 036): the aim's structure under mean reversion is claim 036's
  part 3 (the deviation part scaled by M_t(phi)), the quadratic-cost analogue of 3a-3b
  (`garleanu2009dynamic`'s aim portfolio weights future expected targets); it transfers as the
  target's structure only (claim 038's bridge), not as a policy.
- *Claim 112's laws*: the finite-law variant and the filter's moment identities transfer with
  M9's recursion; the Gaussian half's exact-posterior meaning with a state transition is the
  transient Kalman filter, standard but not in the ledger (AX-18 is the static case; AX-10 the
  steady state), so it is cited by name and Not shown.

**One sentence without model nouns.** When the target moves on its own, split its next move
into the part known today and the surprise: the known part tilts the no-trade band toward it
and, when it is large enough that tomorrow would trade anyway, is traded today at a cost
discount, or else is a purchase to plan cash for; the surprise is what a reserve is for, sized
by its dispersion exactly as before; and the old result that uncertainty shrinks the band's
scale as one learns holds only while learning outpaces the target's own noise.

## Proof

### 1. Decomposition and the width

1a: m_1 = Phi (m_0 + K_0 nu_1) + (I - Phi) theta_bar (M9's filter), so
mu_1 = G m_1 - (0, c^E) = mu^p_1 + G Phi K_0 nu_1 and x*_1 = (gamma Sigma_1)^{-1} mu_1; subtracting
x*_0 = (gamma Sigma_0)^{-1} mu_0 and adding and subtracting (gamma Sigma_1)^{-1} mu_0 gives the
display, since mu^p_1 - mu_0 = G (Phi - I)(m_0 - theta_bar). The innovation nu_1 = y_1 - m_0 - d
(H = I on the transformed observation) has mean zero and covariance P_0 + R, so
Cov(Phi K_0 nu_1) = Phi K_0 (P_0 + R) K_0' Phi' = Phi (P_0 - P^u_0) Phi' = V_0 (K_0 (P_0 + R) K_0' = P_0 (P_0 + R)^{-1} P_0 = P_0 - P^u_0);
under the Gaussian law nu_1 is independent of I_0 and Delta^u_1 a martingale difference. 1b:
Sigma_t = G P_t G' + Sigma_r with Sigma_r constant; P_1 - P_0 as displayed from
P_1 = Phi P^u_0 Phi' + Q; the width (kappa^+ + kappa^-)/c_t falls iff c_t rises; the steady state
the fixed point of each block's scalar recursion T(p) = phi^2 p s/(p + s) + q: T is
increasing (T' = phi^2 s^2/(p + s)^2 > 0) and concave on [0, infinity) with T(0) = q and
T(p) <= phi^2 s + q, so the iterates p_{t+1} = T(p_t) are monotone (nondecreasing if
p_0 <= T(p_0), nonincreasing otherwise) and bounded, hence convergent to a fixed point; the
fixed point is unique when q > 0 (T(p) - p is concave, positive at 0 and negative for large p,
so it has one root on (0, infinity)) or when phi^2 < 1 (then T'(p) <= phi^2 < 1 everywhere and
T is a contraction), while phi = 1 and q = 0 is M8's monotone case with the fixed point 0. At the
fixed point Sigma and c_t are constant. AX-10's Theorem 2.1 (A = Phi, C = I, Sigma_x = Q,
Sigma_y = R) gives the steady-state filter's form under its own Gaussian hypotheses and is
cited for that form only, not for the convergence.

### 2. The tilt

Claim 029's 1d gives, in the coarse regime, hi_t = x*_t + kappa^-/c + tau_t and lo_t = x*_t - kappa^+/c + tau_t
with tau_t = beta (kappa^+ U - kappa^- D)/c and U, D the probabilities that the target rises and
falls; by 1a the target rises iff Delta^u_{t+1,i} > -Delta^p_{t,i}. Under a symmetric law of
Delta^u_{t+1,i} given z and equal rates, for Delta^p > 0, D = P(Delta^u < -Delta^p) = P(Delta^u > Delta^p)
by symmetry, so U - D = P(-Delta^p < Delta^u <= Delta^p) = P(|Delta^u| <= Delta^p) less the mass
of an atom at -Delta^p (the boundary convention of claim 100's 2c, whose argument this is with
Delta^p for delta_t); the case Delta^p < 0 is the mirror; tau_t = beta kappa (U - D)/c has
Delta^p's sign, and U = 1 (or D = 1) when |Delta^p| exceeds the innovation's support.

### 3. Front-loading

3a (red's direct argument): suppose a^dyn_0 < a^my_0. Then the dynamic root's marked holding is
below the myopic one's in every state, so the fund is bought in every state tomorrow from the
dynamic root too (lo_{1,A}(z') > g_A(z') a^my_0 > g_A(z') a^dyn_0; lo_{1,A} does not depend on the
holding), and claim 044's part 2 pins s_A(z') = kappa^+_A with eta_1 = 0, S_A = beta E[g_A] kappa^+_A > 0.
If the dynamic root buys today (a^dyn_0 > a^-), its root line gives
g_{0,A}(a^dyn_0) = kappa^+_A - S_A < kappa^+_A = g_{0,A}(a^my_0) (the myopic root buys strictly inside
its box; if it buys to the cap, g_{0,A}(a^my_0) >= kappa^+_A), while g_{0,A} is decreasing in a_0
with the ETF fixed, so a^dyn_0 > a^my_0, a contradiction; if the dynamic root holds
(a^dyn_0 = a^- < a^my_0), its held line gives g_{0,A}(a^-) + S_A <= kappa^+_A, so g_{0,A}(a^-) < kappa^+_A,
while the myopic purchase from a^- needs g_{0,A}(a^-) > kappa^+_A (its band, claim 110), again a
contradiction; the dynamic root cannot sell (its line would need g_{0,A} + S_A <= -kappa^-_A
below the held case). Hence a^dyn_0 >= a^my_0. The threshold reading: at the dynamic root
claim 044's part 2 reads S^dyn_A = beta E[g_A s_A(z')] from the dynamic root's own tomorrow,
where s_A(z') = t_{1,A}(z') is kappa^+_A if that tomorrow buys, in [-kappa^-_A, kappa^+_A]
otherwise (the held marginal inside; kappa^+_A itself when the fund is held at its purchase
edge), so S^dyn_A <= beta E[g_A] kappa^+_A with equality iff t_{1,A}(z') = kappa^+_A in every
state, in particular when every state buys from the marked a^dyn_0 (lo_{1,A}(z') > g_A(z') a^dyn_0,
which a larger holding makes harder, so the myopic condition does not imply it); on a
purchase the dynamic root line is g_{0,A}(a^dyn_0) + S^dyn_A = kappa^+_A,
the displayed threshold and its bound. 3b is the mirror with s_A >= -kappa^-_A and
kappa^-_A > 0. 3c is claim 113's 3b. 3d: claim 046's x_hat with mu_1 = mu^p_1 + G Phi K_0 nu_1
substituted; the base is the value at nu_1 = 0 with the worst marking; the reserve claims'
hypotheses are on need(z') and the tree, unchanged.

### 4. Transfers

Each named claim's setting is a finite public tree with (mu_1(z'), Sigma_1) given (claims 044,
046, 047, 113), an M6 instance with a public law (claim 029), or one review (the one-review
claims), which M9's tree supplies; claim 100's 2a uses P_{t+1} <= P_t, which 1b replaces by its
condition; claim 036's part 3 is M5's own persistence variant; claim 112's Gaussian meaning
rests on AX-18's static state, which M9 leaves.

## Checks

`uv run python checks/114/check.py` (exits non-zero on failure; a check, not a proof). On M9's
128-branch, 72-node tree with claim 112's inputs and laws, an exact two-review program
(cvxpy/CLARABEL): (i) 1a's decomposition holds at every node for four (phi, Q) settings, the
innovation part is centred and its covariance equals the displayed formula, and P_1 rises or
falls against P_0 as 1b says (with phi = 0.6 and q_alpha = 4e-4 the alpha block rises); (ii) the
root band of a lone fund with a narrow band (20 bp each way) in the coarse regime, scanned over
incumbents, equals claim 029's static band shifted by part 2's tilt to within the scan step at
two settings with a predictable rise and a predictable fall (U = 1 and D = 1); (iii) with a
long-run alpha of 4% the fund is bought in every state tomorrow from the myopic root and the
dynamic root holds 0.423 against the myopic 0.400 with the ETF unchanged (front-loading), and
with -3% it is sold in every state and the dynamic root holds 0.399 against 0.749
(back-loading); the analyst's experiment 057 confirms 1a, 1b (720 of 720 per-instrument
tests) and part 2 exactly on the M9 harness, the order of 3a-3b in 24 of 24 cells, and finds
the full threshold cut attained in none of them, the dynamic root's threshold lying between
(1 - beta E[g_A]) kappa^+_A and kappa^+_A as 3a now says; (iv) on six
random M9 instances with persistence and state noise, the root clip with alpha~ + S at
(m_0, eta_hat_0) and claim 113's aggregate no-reserve test hold (108 covered states).

## Not shown

- The Gaussian law's exact-posterior meaning of M9's filter (the transient Kalman filter with a
  state transition), cited by name; AX-18 covers the static case and AX-10 the steady state.
- 3a-3b's threshold cut is a bound; its exact value needs the dynamic root's own tomorrow
  (S^dyn_A), a fixed point, and a condition in the inputs for the full cut (every state buying
  from the front-loaded holding) is not given beyond the restated equality case.
- 3a-3b assume the ETF fixed or absent and slack budgets; with the ETF free the sign is claim
  113's corrected one, and with a binding budget the predictable part enters as 3d's planned
  purchase, whose funding (ETF sale against cash) is claim 047's reading, not sized here.
- Part 2 is the coarse regime; the fine-regime order with a predictable move (the analogue of
  D15e's sandwich with a drift) is not stated; claim 100's t_0 has no analogue when the width
  does not rise.
- A second D24 claim, if wanted: the reserve's size in the innovation law's parameters (the
  propagated gain Phi K_t against the state noise Q) as claim 047's growth statement.
- No calibration; the check's instances are assumed inputs (rule 22).

## Prior art

Mechanism: a moving target's next step is the sum of a drift known today and a surprise; with
proportional costs the drift tilts the no-trade band toward itself by the chance the surprise
does not undo it and, when large, is executed today at a discounted threshold because the
trade would be paid for tomorrow anyway, while the surprise alone calls for a reserve; and the
estimate's precision stops improving once the target's own noise matches what a period's
observation removes, so results that rely on precision rising must be restricted to that
regime.

General results checked: `garleanu2009dynamic` and `garleanu2016dynamic` (registered): the
aim portfolio under mean-reverting factors weights current and future expected targets, the
quadratic-cost analogue of 3a-3b and of claim 036's part 3; claim 036 (formalized): mean
reversion's scaling of the aim's deviation part; claim 100 (formalized): the learning drift
and tilt, of which part 2 is the general-drift form; claim 029 (formalized): the band and its
tilt; claims 044, 046, 047, 113: the two-review criteria and reserve rules transferred; AX-10
(`abeille2016lqg` Theorem 2.1): the steady-state filter, cited for 1b with its hypotheses
checked (stabilizability of (Phi, Q^{1/2}) and detectability of (I, Phi)); AX-13 through claim
044. `merton1973intertemporal` is not used (no hedging demand in a quarterly-score objective,
claim 036's 4(i)). Searched: claims 029, 036, 038, 100, 044-047, 110-113; ROADMAP D24; M5's
persistence variant. No web search. This is a claim because D24 asks how flexibility depends
on the predictable and unpredictable parts in the inputs, and the kill benchmark (the
fixed-means rule with the variance replaced) has none of parts 1b, 2, 3a-3d.

## Open objections

none

## Review

**Red, 2026-09-30** (on e62ac039). Red-passed, with four required corrections: 1b's "iff" (and part 4's "only while"), 3d's need display, the citation for P_t's convergence, and part 2's atom (lean's). Red rederived every part by hand against M9's recursion in model/SPEC.md, and checked the counterexamples' arithmetic at M8's worked-example inputs.

**1a** is right. mu^p_1 - mu_0 = G(Phi - I)(m_0 - theta_bar) makes the decomposition an identity, and K_0(P_0 + R)K_0' = P_0 - P^u_0 gives the innovation covariance.

**Part 2** is claim 029's 1d tilt with the target's rise read through 1a. One precision point (lean's, which red adds as a required correction, 4 below): under a symmetric law and equal rates, U - D = P(-|Delta^p| < Delta^u <= |Delta^p|), which is the display's P(|Delta^u| <= |Delta^p|) less the atom P(Delta^u = -|Delta^p|). The proof mentions this, but the display drops it. Under the finite law Delta^u has atoms, so this matters.

**Part 3.**
- *3a's conclusion is right; its proof needs one change.* The proof reads claim 044's one-sided derivative at a^my, which needs the fund bought in every state from a^my's marked holding. The hypothesis states this at the dynamic root's.
  - A direct argument closes it. If a^dyn < a^my with both buying today, the root line gives g_{0,A}(a^dyn) = (1 - beta E[g_A]) kappa^+_A < kappa^+_A = g_{0,A}(a^my), but g_{0,A} decreases in a (the ETF fixed), a contradiction. A held a^dyn = a^- < a^my is excluded the same way, via the band.
  - Please use that argument, or state the hypothesis at a^my (a nit).
- *3b and 3c* are the mirror and claim 113's 3b.

**Required correction 1 (1b's "iff", and part 4's "only while").**
- *The claim.* "Each instrument's curvature ... rises with t iff the state noise Q is below what learning removes in the positive semidefinite order, falls iff above." The PSD order is sufficient for *every* instrument at once, not necessary for any one.
- *Why.* Instrument i's curvature changes by gamma (G (P_1 - P_0) G')_{ii} = gamma sum_k G_{ik}^2 (P_1 - P_0)_{kk} (P diagonal), whose sign depends on the loadings when the two blocks move oppositely.
- *Counterexample* at M8's worked-example inputs (b_A = 0.9, b_E = 1, sigma_f = 8.01%, sigma_A = 6.32%, P_0 = diag(1.6e-5, 4e-4)), with Phi = I and Q = diag(0, 1e-4).
  - Learning removes (3.98e-8, 3.64e-5), so P_1 - P_0 = (-3.98e-8, +6.36e-5), and neither PSD relation holds.
  - Yet the fund's curvature rises (b_A^2 dP_lambda + dP_alpha = +6.36e-5: its width falls) and the ETF's falls (b_E^2 dP_lambda < 0: its width rises).
- *Please* state 1b per instrument: instrument i's width rises iff (G(Q - (P_t - Phi P^u_t Phi'))G')_{ii} < 0, with the PSD order the sufficient condition for all instruments together. Part 4's "claim 100's 2a-2d ... only while Q < P_t - Phi P^u_t Phi'" should read "while", or be stated per instrument.

**Required correction 2 (3d's need display).**
- *The display.* It writes the fund's term as (1 + kappa^+_A)(x_hat^p_A + (G Phi K_0 nu_1)_A/(gamma Sigma_{1,AA}) - g_A a_0)^+ with x_hat^p_A = (mu^p_{1,A} - kappa^+_A)^+/(gamma Sigma_{1,AA}).
- *The error.* By 3d's own first line, the solo target is (mu^p_{1,A} + (G Phi K_0 nu_1)_A - kappa^+_A)^+/(gamma Sigma_{1,AA}), and (a + b)^+ != a^+ + b when a < 0.
- *Example.* With mu^p_{1,A} - kappa^+_A = -0.1% and an innovation of +0.5%, the display counts 0.5% where the target is 0.4%, over gamma Sigma_{1,AA}.
- *Please* keep the positive part around the sum, or state the display for mu^p_{1,A} >= kappa^+_A. The planned-purchase base at nu_1 = 0 is right.

**Required correction 3 (1b: "to which P_t converges ... (AX-10's Theorem 2.1)", and M9's SPEC).**
- *What AX-10 gives.* Its ledger statement (Theorem 2.1) gives the *steady-state* filter's form under stabilizability and detectability, for conditionally Gaussian noise. It does not state that P_t converges to that steady state from P_0, and its hypotheses include Gaussian noise, which M9's finite law does not have. (The Riccati recursion itself is law-free.)
- *The fix.* For M9's diagonal blocks, convergence is elementary: each block's update p -> phi^2 p s/(p + s) + q is increasing and concave with a unique positive fixed point. Please argue it in a line or two, or cite a ledger entry that states convergence, and keep AX-10 for the steady state's form (rule 21).
- M9's SPEC paragraph carries the same citation.

**Required correction 4 (part 2's display, the atom; lean's point).** Please state |tau_t| = beta kappa P(-|Delta^p| < Delta^u <= |Delta^p|)/c_t (the half-open interval), or add the condition that the innovation has no atom at -|Delta^p|.

lean's scoping note found red's corrections 1 and 3a's point independently. On 3a, lean also notes that kappa^+_A > 0 is needed for the strict push.

**Part 4** is right apart from correction 1's "only while".
- The two-review results transfer verbatim on the finite tree (M9 changes the law of (mu_1, Sigma_1), not the program).
- The transient Gaussian filter's exact-posterior meaning is honestly named and Not shown (AX-18 is the static case).

**Nit.** 3d's "a predictable fall needs no reserve at all: the fund is sold, which raises cash" holds only when the fall exceeds the innovation's support. Otherwise some states still buy the fund, and their need counts.

**Mechanism.** The Kalman predict-update split of the target's move, into its conditional mean and innovation, fed into claim 029's tilt and claim 044's incumbent values: an application. The kill benchmark fails on parts 1-3 as the claim says. The predictable part's front- and back-loading and the planned purchase are new in the inputs.

Verdict: red-passed

**Red, recheck of the corrections (9a6ffb38, with lean's eb786cb5), 2026-09-30.** All four of red's required corrections are made.
1. 1b is stated per instrument, with the PSD order as the sufficient condition, and part 4 reads "while".
2. 3d keeps the positive part around the sum.
3. P_t's convergence is argued directly, and the argument is right. T(p) = phi^2 p s/(p + s) + q is increasing and concave with T(0) = q and T bounded, so the iterates are monotone and converge. The fixed point is unique when q > 0 (T(p) - p is concave, positive at 0 and negative for large p) or when phi^2 < 1 (a contraction). AX-10 is kept for the steady state's form only, in M9's SPEC as well.
4. Part 2's atom condition is in.

The predictable-fall nit and 3a's hypothesis at the myopic root, with kappa^+_A > 0 (lean's), are made. 3a's main conclusion, a^dyn_0 >= a^my_0, is right: it follows from the one-sided derivative at a^my_0, with S_A pinned by the myopic tomorrow.

**One problem, in 3a's threshold reading (required).**
- *The claim.* The Statement says "on a purchase the dynamic root line is g_{0,A}(a_0) + S_A = kappa^+_A", with S_A = beta E[g_A] kappa^+_A, the myopic tomorrow's value. The Proof supports it with "at the dynamic root the fund is then bought in every state too (its marked holding is at least the myopic one's, and lo_{1,A}(z') does not depend on the holding)".
- *Why it fails.* That runs the wrong way. A purchase tomorrow needs lo_{1,A}(z') > g_A(z') a_0, and a *larger* a^dyn_0 >= a^my_0 makes that *harder*. So lo_{1,A} > g_A a^my_0 does not give lo_{1,A} > g_A a^dyn_0.
- *What is true.* At the dynamic root, S_A is read from the dynamic tomorrow. It equals beta E[g_A] kappa^+_A only where the fund is bought in every state from a^dyn_0 as well, and otherwise it is smaller (s_A <= kappa^+_A).
- *Please* state the threshold reading under that added condition (lo_{1,A}(z') > g_A(z') a^dyn_0 for every z'), or read the dynamic line with its own S_A <= beta E[g_A] kappa^+_A, so that the threshold is at least (1 - beta E[g_A]) kappa^+_A.
- a^dyn_0 >= a^my_0 is unaffected. 3b's mirror has the same step.

**Red, recheck of 3a-3b's restatement (f480b508, d073be89), 2026-09-30.** The restatement answers red's recheck, and it is right.
- The threshold reading now uses the dynamic root's own S^dyn_A, and s_A(z') <= kappa^+_A in every state gives S^dyn_A <= beta E[g_A] kappa^+_A and the threshold kappa^+_A - S^dyn_A >= (1 - beta E[g_A]) kappa^+_A.
- a^dyn_0 >= a^my_0 stays with the myopic hypothesis.
- 3b is the correct mirror.
- Experiment 057's 24 of 24 cells, with the dynamic tomorrow trading in only 4-14 of 16 states, illustrate that the full cut is the exception.

**Nit (lean's, not required).** The Statement's "with equality iff the fund is bought in every state tomorrow from the dynamic root's marked holding too" is slightly narrow. A state that holds the fund at its purchase edge (idle inside with g_{1,A} = kappa^+_A, or at the cap with g_{1,A} >= kappa^+_A) also has slope kappa^+_A. The Formalization notes already say "iff every state's slope tomorrow is kappa^+_A". Please use that wording in 3a (and the mirror in 3b), or write "if" for the one direction.

No result changed.

## Formalization notes

Approved 2026-09-30 by pm: Red's review is sound: every part re-derived by hand against M9's recursion (1a's identity and innovation covariance; part 2 as claim 029's tilt; 3a's conclusion with red's direct argument; part 4's verbatim transfer on the finite tree); the four required corrections made in 9a6ffb38 exactly as asked (1b and part 4 per instrument with the PSD order only sufficient, red's counterexample at M8's inputs; 3d's positive part kept around the sum; P_t's convergence argued for the scalar blocks with AX-10 for the steady state's form only, in the claim and M9's SPEC; part 2's half-open interval for atoms), plus 3a's proof and the nit; lean's three points made. Mechanism: the Kalman predict-update split of the target's move fed into claim 029's tilt and claim 044's incumbent values, an application; new in the inputs: front- and back-loading of the predictable move and its planned purchase in the need, with the reserve pricing only the innovation, so D24's kill criterion is not met. Limits: M9 on the finite tree; the transient Gaussian filter's posterior meaning Not shown; red records its recheck line.


mathb, 2026-09-30 (lean's three points, duty 1, before red's review): 1b's "iff" is replaced by
the two one-sided implications in the psd order, with an instrument's width following its
own loadings' combination when the blocks move oppositely (lean's instance) and the ETF's
"iff" on the lambda block; part 2's display carries the no-atom condition and the half-open
form; 3a-3b's hypothesis is placed at the myopic root (checkable before the dynamic solve)
with kappa^+_A > 0 (kappa^-_A > 0), and the proof pins S_A from the myopic policy's tomorrow.
No result changed.

mathb, 2026-09-30 (red's review, four required corrections, the 3a proof point and the nit):
1b and part 4 are per instrument (the PSD order sufficient for all instruments together, with
red's counterexample), 3d's need is written without splitting the positive part (the planned
purchase is the need at zero innovation with the worst marking), P_t's convergence is argued
by the scalar blocks' monotone concave recursion with AX-10 cited for the steady-state form
only (M9's SPEC paragraph corrected the same way), part 2's display carries the no-atom
condition and the half-open form (lean's point, made earlier), 3a's proof is red's direct
argument, and the nit on a predictable fall carries "exceeding the innovation's support". No
result changed.

mathb, 2026-09-30 (red's recheck and the analyst's experiment 057; a post-approval prose
correction, PM's decision, the claim staying approved and formalized): 3a's threshold reading
used the myopic tomorrow's S_A at the dynamic root, and its proof's step ("bought in every
state from the larger holding too") ran the wrong way. The reading is now at the dynamic root
with its own S^dyn_A <= beta E[g_A] kappa^+_A: the threshold is at least (1 - beta E[g_A]) kappa^+_A,
equal to it iff every state buys from the dynamic root's marked holding, which is the
hypothesis lean's formal `Threshold` already takes (the dynamic tomorrow buying in every state
from the dynamic holding), so the formal statement is unchanged and experiment 057's
instances fail the old prose only; 3b is the mirror. a^dyn_0 >= a^my_0 (<= for 3b) is unchanged.
No result changed.

mathb, 2026-09-30 (the auditor's FIDELITY points and lean's precision): 112 is added to
depends_on (lean's statement module imports claim 112's M8 objects); the equality case of the
threshold bound reads "iff the dynamic tomorrow's slope is kappa^+_A in every state", which
lean's `ThresholdBound` proves, slightly wider than "every state buys" (a state holding the
fund at its purchase edge has that slope too), with "if every state buys" as the one
direction; 3b likewise. No result changed.

mathb, 2026-09-30 (red's post-approval wording point from the manuscript's Proposition 25): the
title's and part 2's words "the probability that the innovation does not overturn it" named U
rather than the tilt's U - D; both now read "the probability that the innovation is smaller
than the predictable move", the excess of the non-overturning over the overturning probability.
The display, U's and D's definitions and the formal statement were right; no result changed.

Not machine checked. Part 1 is algebra and one cited steady-state result; part 2 is claim
029's tilt with the drift renamed; part 3 is claim 044's one-sided derivative in one variable;
part 4 is a table of settings.

Lean, 2026-09-30 (final): 1a, 1b, part 2's probabilities and 3a-3b are machine checked. The
statement is in `lean/Standalone/M9PredictableTargetMove.lean` and the proof in
`lean/Novel/M9PredictableTargetMoveProof.lean`.
- Model: M9's coordinates on claim 112's M8 objects (scalar blocks with phi, q and theta_bar), and
  claim 044's two-review objects for part 3.
- Imports: claim 044's proof module (Q-04; 044 in depends_on). Claim 112's statement supplies the
  M8 definitions (muP, SigP, the filter block, BlockLaw). Its proof is not imported; the block
  moments are re-proved here.
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/114/check.py` pass.

Machine checked:
- 1a:
  - the decomposition x*_1 - x*_0 = Delta^p_0 + Delta^u_1 as an identity, for any targets A_t mu_t;
  - under any finite laws with the stated moments and independent blocks, M eps has mean zero
    and covariance M diag(phi^2 (p - p^u)) M' for any linear image M.
- 1b:
  - p_1 - p = q - (p - phi^2 p^u);
  - Sigma_1 - Sigma_0 = G diag(Delta) G' entrywise;
  - per instrument, the curvature falls (the width rises) iff (G diag(Delta) G')_{ii} < 0;
  - both blocks learning-dominant lower every curvature, and noise-dominant raise it;
  - a constant P gives a constant Sigma;
  - lean's mixed-blocks instance;
  - each block's recursion p -> phi^2 p s/(p + s) + q converges from any p_0 >= 0 to a nonnegative
    fixed point, unique among nonnegative ones when q > 0 or phi^2 < 1 (the approved elementary
    argument).
- Part 2, for any finite symmetric innovation law:
  - U - D = sign(delta) P(-|delta| < u <= |delta|), which equals P(|u| <= |delta|) less the atom at
    -|delta|, and P(|u| <= |delta|) itself with no atom there;
  - the tilt has delta's sign;
  - U = 1 or D = 1 beyond the support.
- 3a-3b, with tomorrow's budget slack at the myopic tomorrow:
  - the root objective lies below the myopic root's tangent plane of slopes S_j;
  - if the myopic tomorrow buys (sells) the fund in every state, with kappa^+ > 0 (kappa^- > 0),
    then S_A = beta E[g_A] kappa^+_A (-beta E[g_A] kappa^-_A);
  - every smaller (larger) holding lowers the root objective strictly;
  - an optimal policy's root maximizes the root objective (new lemma);
  - so a^dyn_0 >= a^my_0 (<=) whenever the two roots agree off the fund;
  - the dynamic root's threshold: g_{0,A} = (1 - beta E[g_A]) kappa^+_A when the fund is bought in
    every state from the *dynamic* root's marked holding (`Threshold`; the hypothesis is on the
    dynamic policy's own tomorrow). In general (`ThresholdBound`, added after mathb's restatement),
    S^dyn_A <= beta E[g_A] kappa^+_A and the threshold kappa^+_A - S^dyn_A >= (1 - beta E[g_A]) kappa^+_A,
    with equality iff every state's slope tomorrow is kappa^+_A (bought, or held at the purchase
    edge).
- For the fidelity row (PM): 3a-3b are one-coordinate statements. Nothing is said about the joint
  move, which experiment 047 showed can reverse.

Paper-level:
- 3c (claim 113's reading) and 3d (claim 046's need with mu_1 substituted);
- part 4's transfer table;
- the transient Kalman filter's meaning;
- AX-10's steady-state form;
- the Checks.

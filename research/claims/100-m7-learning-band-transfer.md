---
id: 100
title: "Claim 029's quarterly band transfers to M5's learning path: the static width rises with learning, the target drifts outward, and a static-width band forces large target moves, so pure learning ends the coarse regime"
status: formalized
model_version: M7
depends_on: [029]
axioms_used: []
formal: lean/Standalone/M7LearningBandTransfer.lean
direction: D13
---
## Statement

PM's note (2026-09-28) asks how the band's width and tilt depend on the shrinking predictive
covariance, not only on the belief-mean innovations: that is where learning-driven target
motion differs from a generic moving target. This claim answers it in M7's finite-law variant
(`model/SPEC.md` M7) by transferring claim 029 to the time-varying curvature c_t and adding
what the Kalman path forces. It imports no literature theorem.

**Setting.** A slack-budget M7 instance in the finite-law variant: theta from a finite law
with mean m_0 and covariance P_0, shocks from a finite centered law with covariance Sigma_z,
positive gross returns, the manager running M5's linear filter with R = L Sigma_z L'; P_t,
Sigma_t = G P_t G' + Sigma_r, mu_t = G m_t - (0, c^E), x*_t = (gamma Sigma_t)^{-1} mu_t,
V_t = P_t - P_{t+1}, gamma > 0, beta in (0, 1], directional rates in [0, 1), finite caps, T >= 1,
V_T = 0. The public state is z_t = (t, y_1, ..., y_t); write c_t = gamma Sigma_{t,ii} for the
instrument under discussion, and lo_t(z), hi_t(z), NT_t(z), G_t, U, D, tau_t as in claim 029 with
Sigma(t, z) = Sigma_t.

### Part 1. Transfer of claim 029 to the learning path

1a. *M7 is an M6 instance with time-varying covariance.* Under the finite-law variant, z_t is a
    finite Markov chain, q_t(z' | z) is the finite prior's predictive law, mu(t, z) = mu_t and
    Sigma(t, z) = Sigma_t are functions of z, and M6's holdings, costs, caps, slack budget and
    objective are M7's. M6 as written fixes Sigma; every statement and proof of claim 029 uses
    Sigma only through positive definiteness at each (t, z) and through c = gamma Sigma at a
    fixed (t, z), except the two-date primitive conditions of its 1d, which are restated in 1c
    below with the curvatures written out.

1b. *One instrument.* For n = 1, claim 029's 1a (regularity, the band, trade to the edge), 1b
    (width ceiling by the static width (kappa^+ + kappa^-)/c_t and the last review's clips), 1c
    (edge brackets with c_t), 1d (coarse regime: hi_t = x*_t + kappa^-/c_t + tau_t,
    lo_t = x*_t - kappa^+/c_t + tau_t, tau_t = beta(kappa^+ U - kappa^- D)/c_t, width
    (kappa^+ + kappa^-)/c_t) and 1e (the width equals the static width iff both edges are
    first-order points and every outcome lands the marked band on one side of the next band)
    hold in M7 with c replaced by c_t = gamma Sigma_t at every (t, z). If Sigma_t is diagonal for
    every t, the n-instrument problem is n independent one-instrument problems and these hold
    per instrument with c_{t,i} = gamma Sigma_{t,ii}.

1c. *The two-date conditions.* Claim 029's sufficient primitive condition for the coarse regime
    at (t, z), without marking and with interior edges, reads in M7: every positive-mass target
    innovation x*_{t+1} - x*_t exceeds (kappa^- + beta kappa^+)/c_t + (kappa^+ + beta kappa^-)/c_{t+1}
    in absolute value; with marking, (up) holds when
    g' max(0, x*_t + (kappa^- + beta kappa^+ bar g_t)/c_t) < min(bar x, x*_{t+1} - (kappa^+ + beta kappa^- bar g_{t+1})/c_{t+1})
    and (down) when g' min(bar x, x*_t - (kappa^+ + beta kappa^- bar g_t)/c_t) > max(0, x*_{t+1} + (kappa^- + beta kappa^+ bar g_{t+1})/c_{t+1}).

1d. *Many instruments.* Claim 029's 2a, 2b (gamma (x - y)' Sigma_t (x - y) <= sum_i (kappa^+_i + kappa^-_i)|x_i - y_i|
    on NT_t(z)) and 2c (the static parallelotope at T-1 with Sigma_{T-1} and the bundling shift
    -(Sigma_{T-1,AE} d_E)/Sigma_{T-1,AA}) hold in M7. The transfer carries claim 029's elementary
    proof of 2b, the comparison along the segment between two no-trade holdings with strong
    convexity of modulus gamma Sigma_t, and cites nothing.

### Part 2. What the learning path adds

For one instrument (n = 1) unless stated; all of this uses only the filter's second moments.

2a. *The static width rises with learning.* P_t^{-1} = P_0^{-1} + t H' R^{-1} H, so P_{t+1} <= P_t
    in the positive semidefinite order, P_t -> 0 (H has full column rank), Sigma_{t+1} <= Sigma_t,
    Sigma_t -> Sigma_r, and c_t is nonincreasing with limit gamma Sigma_{r,ii}. Hence the static
    width w_t = (kappa^+ + kappa^-)/c_t is nondecreasing in t with limit
    (kappa^+ + kappa^-)/(gamma Sigma_{r,ii}), and the ceiling of claim 029's 1b loosens quarter
    by quarter: as estimation risk is learned away the same deviation costs less, and the band
    that a last review would set widens. For n instruments the same holds for each Sigma_{t,ii}
    and for the Sigma_t-diameter of 1d, whose right side is fixed while the left side's metric
    shrinks.

2b. *The target's motion has a martingale-type part and a known outward drift.* For every t,
    x*_{t+1} - x*_t = (gamma Sigma_{t+1})^{-1} G epsilon_{t+1} + delta_t with
    delta_t = [(gamma Sigma_{t+1})^{-1} - (gamma Sigma_t)^{-1}] mu_t, where epsilon_{t+1} has
    unconditional mean zero and covariance V_t = P_t - P_{t+1}, and the bracketed matrix is
    positive semidefinite; for n = 1, delta_t = mu_t (1/Sigma_{t+1} - 1/Sigma_t)/gamma has the
    sign of mu_t when the instrument's row G_i of G is nonzero, and is zero when G_i = 0 (an
    ETF with no factor loading, whose risk charge does not learn while mu_t = -c^E_i may be
    nonzero): the learning drift moves the target away from zero. Both V_t and the bracket
    are of order 1/t^2 as t grows, and both are deterministic. Under the finite-law variant
    epsilon_{t+1} is uncorrelated with the past but need not be centred given the history; the
    Gaussian law makes it a martingale difference (M7; not proved here).

2c. *Tilt.* In the coarse regime at (t, z), claim 029's tilt tau_t = beta(kappa^+ U - kappa^- D)/c_t
    is, in M7, scaled by the rising 1/c_t and decided by the return-weighted masses of the
    outcomes that carry the band up or down. Without marking and with interior edges, an (up)
    outcome is exactly one with x*_{t+1} > x*_t and a (down) outcome exactly one with
    x*_{t+1} < x*_t, so no outcome leaves the target unmoved, and by 2b an up outcome is one with
    (gamma Sigma_{t+1})^{-1} G epsilon_{t+1} > -delta_t. If the conditional law of epsilon_{t+1}
    given z is symmetric about zero (a hypothesis in the finite-law variant; the Gaussian law
    satisfies it) and kappa^+ = kappa^- = kappa, then tau_t is zero or has the sign of delta_t, with

    ```
    |tau_t| = beta kappa P( |(gamma Sigma_{t+1})^{-1} G epsilon_{t+1}| <= |delta_t| given z ) / c_t,
    ```

    zero, for kappa > 0, exactly when the conditional law puts no mass in (-|delta_t|, |delta_t|]
    (at kappa = 0 the tilt is zero for every law); and delta_t
    has the sign of mu_t when the instrument's row G_i of G is nonzero (then
    Sigma_{t+1,ii} < Sigma_{t,ii}, since V_t is positive definite), while delta_t = 0 when
    G_i = 0 (an instrument with no factor loading and no alpha, whose risk charge does not
    learn). So the band leans toward where the risk-charge decline is pushing the target, by the
    probability that the belief innovation does not overturn the drift. A pure martingale target
    with symmetric innovations has tau_t = 0 (claim 029's 1d); the learning drift is what makes
    the tilt nonzero here.

2d. *A static-width band forces large target moves, so pure learning ends the coarse regime.*
    Let kappa^+ + kappa^- > 0, t <= T-2, and no marking for the instrument (gross return one on
    every path, the *pure-learning marking*). Call an outcome (z', g') of q_t(. | z) an *up
    landing* if hi_t(z) <= lo_{t+1}(z') and a *down landing* if hi_{t+1}(z') <= lo_t(z), and let U
    and D be their probabilities (closed landings; they differ from claim 029's strict (up) and
    (down), and the two are disjoint when hi_t > lo_t). If hi_t(z) - lo_t(z) equals the static
    width (kappa^+ + kappa^-)/c_t, then every positive-mass outcome is an up or a down landing,
    U + D = 1, every outcome moves the target, and

    ```
    x*_{t+1} - x*_t >=  [kappa^-(1 - beta) + beta (kappa^+ + kappa^-) U]/c_t   on every up landing,
    x*_t - x*_{t+1} >=  [kappa^+(1 - beta) + beta (kappa^+ + kappa^-) D]/c_t   on every down landing.
    ```

    Consequently, in the finite-law variant with pure-learning marking there is a review t_0,
    determined by the prior, the shock law, gamma, beta, the rates and c_0 and not by the
    horizon, such that for every horizon T, every t with t_0 <= t <= T-2 and every history,
    hi_t(z) - lo_t(z) < (kappa^+ + kappa^-)/c_t: the band is strictly narrower than the static
    width. Learning shrinks the target's moves
    like 1/t (innovation standard deviation O(1/t), drift O(1/t^2), see 2b) while the static width rises, so the coarse regime is a transient of
    early quarters and every instrument is eventually in the fine regime.

    With real marking this need not hold: the deviation from the target also moves by
    x^+_t (g_{t+1} - 1), which does not shrink with learning, so an instrument whose own return
    dispersion times its holding exceeds the side-weight bound can stay in the coarse regime.
    Which instruments do is a calibration question (analyst's note).

**Consequence for D13** (a reading, not a further theorem). Along M5's learning path the two
anchors of claim 029 move in opposite directions: the static width rises with t (2a) and the
target's belief-driven motion falls like 1/t (2b), so the pure-learning band passes from coarse
to fine and then, by claim 029's 1e, is strictly narrower than the static width for the rest of
the horizon; in the coarse quarters it is the static band leaning toward the drift (2c). What a
fine-regime leading order must therefore carry is the pair (c_t, V_t): a Kalman-driven target is
not a stationary moving target, and the kill benchmark's band (`muhlekarbe2017primer`, section
4, a mean-reverting state variable with constant coefficients) has to be read with time-varying
coefficients and a drift term, or it does not apply. The return-driven deviation is the other
source of motion, and it does not learn away.

## Proof

### 1. Transfer

*1a.* Under the finite-law variant the observed history takes finitely many values, so
z_t = (t, y_1, ..., y_t) ranges over a finite set, and the next observation's law given the
history is the finite prior's predictive law, a finite law on y_{t+1} determining (z_{t+1}, g_{t+1})
(gross returns are functions of y_{t+1}, positive by hypothesis). The filter mean m_t is a
function of the history, so mu_t and x*_t are functions of z_t, and Sigma_t of t. Holdings,
costs, caps, the slack budget and the objective are M6's with Sigma(t, z) = Sigma_t.

*1b-1d.* Claim 029's proofs are read with Sigma = Sigma_t and c = c_t at a fixed (t, z). Its 1a
uses that G_t is a strictly convex quadratic in x with curvature c_t > 0 plus a convex function,
its 1b that phi = G_t - (c_t/2)(x - x*_t)^2 is convex, its 1c the derivative bounds with c_t, its
1d the first-order equalities at a fixed (t, z) and the affine pieces of V_{t+1}, its 1e the
affine-on-an-interval characterization of V_{t+1}, and its 2a-2c positive definiteness of
Sigma_t at the fixed (t, z), the segment comparison with modulus gamma Sigma_t, and the
quadratic at T-1 with Sigma_{T-1}. Nowhere does a proof compare Sigma at two dates: the only
two-date statements are the primitive sufficient conditions in 029's 1d, whose derivation
substitutes 029's 1c brackets at t and at t+1; with the curvatures written out they read as in
1c above. The claim-029 proofs therefore go through verbatim. For diagonal Sigma_t the tracking
loss, the cost, the caps and (under a slack budget) the feasible set are sums and products over
instruments, so V_t is the sum of n one-instrument value functions and the optimal trade is
coordinatewise the one-instrument trade.

### 2. The learning path

*2a.* With Phi = I and Q = 0 the filter update is P_{t+1} = P_t - P_t H'(H P_t H' + R)^{-1} H P_t,
and by the Woodbury identity P_{t+1}^{-1} = P_t^{-1} + H' R^{-1} H (R is positive definite as
L Sigma_z L' with L invertible, M5). Induction gives the information form. P_t^{-1} is
nondecreasing, so P_t is nonincreasing in the positive semidefinite order; since H has full
column rank (its first K rows are I_K and its middle N rows end in I_N), H' R^{-1} H is positive
definite, P_t^{-1} >= t H' R^{-1} H, and P_t -> 0. Then Sigma_{t+1} - Sigma_t = G (P_{t+1} - P_t) G'
is negative semidefinite, Sigma_t -> Sigma_r, and the diagonal entries and the quadratic form in
1d are nonincreasing in t. For n = 1, c_t = gamma Sigma_t is nonincreasing and the static width
is nondecreasing.

*2b.* The decomposition is the identity
(gamma Sigma_{t+1})^{-1} mu_{t+1} - (gamma Sigma_t)^{-1} mu_t = (gamma Sigma_{t+1})^{-1} (mu_{t+1} - mu_t) + [(gamma Sigma_{t+1})^{-1} - (gamma Sigma_t)^{-1}] mu_t
with mu_{t+1} - mu_t = G epsilon_{t+1}. The bracket is positive semidefinite because
Sigma_{t+1} <= Sigma_t implies Sigma_{t+1}^{-1} >= Sigma_t^{-1} for positive definite matrices;
for n = 1 it is the positive scalar (1/Sigma_{t+1} - 1/Sigma_t)/gamma times mu_t. The innovation:
epsilon_{t+1} = K_t (y_{t+1} - H m_t - d) = K_t (H (theta - m_t) + L z_{t+1}); the linear filter's
error theta - m_t has mean zero and covariance P_t under any law with the prior's first two
moments (the best linear predictor's error is uncorrelated with the data it uses, by induction
on the projection identities that define the Kalman recursion), and z_{t+1} is centered,
independent of (theta, y_1..y_t), with covariance Sigma_z; so E epsilon_{t+1} = 0 and
Cov(epsilon_{t+1}) = K_t (H P_t H' + R) K_t' = P_t H'(H P_t H' + R)^{-1} H P_t = P_t - P_{t+1} = V_t.
Orders: from the information form P_t = O(1/t), so P_t - P_{t+1} = P_t (P_t^{-1}... ) = P_t H' R^{-1} H P_{t+1} = O(1/t^2)
(using P_t - P_{t+1} = P_t (P_{t+1}^{-1} - P_t^{-1}) P_{t+1}), and Sigma_t - Sigma_{t+1} = G V_t G' = O(1/t^2),
hence so is Sigma_{t+1}^{-1} - Sigma_t^{-1} = Sigma_{t+1}^{-1} (Sigma_t - Sigma_{t+1}) Sigma_t^{-1};
and mu_t is bounded (m_t is a bounded linear function of bounded data under the finite law).

*2c.* *Landings are target moves.* In the coarse regime at (t, z) with interior edges and no
marking, claim 029's 1d gives hi_t = x*_t + [kappa^- + beta(kappa^+ U - kappa^- D)]/c_t >= x*_t,
since kappa^-(1 - beta D) + beta kappa^+ U >= 0, and lo_t = x*_t - [kappa^+(1 - beta U) + beta kappa^- D]/c_t <= x*_t.
On an (up) outcome, hi_t < lo_{t+1}, so lo_{t+1} > 0 and by claim 029's 1a G'_{t+1,-}(lo_{t+1}) <= -kappa^+,
while 029's 1c bracket gives G'_{t+1,-}(x) >= c_{t+1}(x - x*_{t+1}) - beta kappa^+; hence
c_{t+1}(lo_{t+1} - x*_{t+1}) <= -(1 - beta) kappa^+ <= 0 and x*_{t+1} >= lo_{t+1} > hi_t >= x*_t.
On a (down) outcome, lo_t > hi_{t+1}, so hi_{t+1} < bar x and G'_{t+1,+}(hi_{t+1}) >= kappa^-,
while G'_{t+1,+}(x) <= c_{t+1}(x - x*_{t+1}) + beta kappa^-; hence
c_{t+1}(hi_{t+1} - x*_{t+1}) >= (1 - beta) kappa^- >= 0 and x*_{t+1} <= hi_{t+1} < lo_t <= x*_t.
Every positive-mass outcome is (up) or (down), so the up outcomes are exactly the positive
target moves, the down outcomes exactly the negative ones, and no outcome has a zero move. By
2b, x*_{t+1} - x*_t > 0 iff eta > -delta_t with eta = (gamma Sigma_{t+1})^{-1} G epsilon_{t+1}.

*Sign and magnitude.* If the conditional law of epsilon_{t+1} is symmetric about zero, eta is
symmetric too (a linear image), and for delta_t > 0
U - D = P(eta > -delta_t) - P(eta < -delta_t) = P(eta > -delta_t) - P(eta > delta_t) = P(-delta_t < eta <= delta_t) >= 0,
and symmetrically U - D = -P(-|delta_t| < eta <= |delta_t|) <= 0 for delta_t < 0; U - D = 0 when
delta_t = 0. With kappa^+ = kappa^- = kappa, tau_t = beta kappa (U - D)/c_t, which is zero or has
the sign of delta_t and has the displayed magnitude; for kappa > 0 it is zero exactly when the
conditional law puts no mass in (-|delta_t|, |delta_t|], and at kappa = 0 it is zero identically. Finally delta_t = mu_t (1/Sigma_{t+1} - 1/Sigma_t)/gamma
for n = 1, and Sigma_t - Sigma_{t+1} = G V_t G' with V_t = P_t H'(H P_t H' + R)^{-1} H P_t positive
definite (P_t is positive definite by the information form and H has full column rank), so
Sigma_{t+1} < Sigma_t iff G != 0; then delta_t has the sign of mu_t, and delta_t = 0 if G = 0.

*2d.* Let the width at (t, z) be the static width. By claim 029's 1e (transferred in 1b) both
edges are first-order points, hi_t > lo_t, and every positive-mass outcome lands [lo_t, hi_t]
(no marking) in [0, lo_{t+1}] (an up landing, hi_t <= lo_{t+1}) or in [hi_{t+1}, infinity) (a
down landing, hi_{t+1} <= lo_t); the two are disjoint since hi_t > lo_t, so U + D = 1 with U and
D the Statement's closed-landing probabilities. The first-order
equalities G'_{t,-}(hi_t) = kappa^- and G'_{t,+}(lo_t) = -kappa^+ can be evaluated exactly as in
029's 1d even with the closed landing: on an up outcome hi_t <= lo_{t+1} with lo_{t+1} > 0, so
V'_{t+1,-}(hi_t) = -kappa^+ (V_{t+1} is affine with slope -kappa^+ on [0, lo_{t+1}]) and
V'_{t+1,+}(lo_t) = -kappa^+ (lo_t < hi_t <= lo_{t+1}); on a down outcome lo_t >= hi_{t+1}, so
V'_{t+1,+}(lo_t) = kappa^- and V'_{t+1,-}(hi_t) = kappa^- (hi_t > lo_t >= hi_{t+1}). Hence

```
kappa^-  = c_t (hi_t - x*_t) + beta (kappa^- D - kappa^+ U),
-kappa^+ = c_t (lo_t - x*_t) + beta (kappa^- D - kappa^+ U),
```

and so hi_t = x*_t + [kappa^-(1 - beta D) + beta kappa^+ U]/c_t and
lo_t = x*_t - [kappa^+(1 - beta U) + beta kappa^- D]/c_t. On an up outcome, 029's 1c bracket at
t+1 (with G'_{t+1,-}(lo_{t+1}) <= -kappa^+ since lo_{t+1} > 0, and G'_{t+1,-} >= c_{t+1}(x - x*_{t+1}) - beta kappa^+)
gives lo_{t+1} <= x*_{t+1} - (1 - beta) kappa^+/c_{t+1} <= x*_{t+1}; so
x*_{t+1} >= lo_{t+1} >= hi_t = x*_t + [kappa^-(1 - beta D) + beta kappa^+ U]/c_t, and
1 - beta D = (1 - beta) + beta U gives the displayed bound. On a down outcome, symmetrically
hi_{t+1} >= x*_{t+1} + (1 - beta) kappa^-/c_{t+1} >= x*_{t+1} (hi_{t+1} < bar x because
lo_t >= hi_{t+1} and lo_t <= hi_t <= bar x with hi_t > lo_t... if hi_{t+1} = bar x then
lo_t >= bar x forces lo_t = hi_t = bar x, excluded), so
x*_t - x*_{t+1} >= x*_t - hi_{t+1} >= x*_t - lo_t = [kappa^+(1 - beta U) + beta kappa^- D]/c_t
and 1 - beta U = (1 - beta) + beta D gives the bound. A zero move is excluded: an up outcome
with x*_{t+1} = x*_t would need kappa^-(1 - beta) + beta(kappa^+ + kappa^-) U = 0, hence beta = 1
and U = 0, so D = 1 and every outcome is down, contradicting the existence of this up outcome;
symmetrically for down.

*Eventual strict narrowing.* Under the finite-law variant with pure-learning marking, 2b gives
sup over histories of |x*_{t+1} - x*_t| -> 0 as t -> infinity: the innovation is
K_t (H (theta - m_t) + L z_{t+1}) with theta - m_t and z_{t+1} bounded (finite supports, m_t a
bounded linear function of bounded data) and K_t = P_{t+1} H' R^{-1} -> 0, and the drift is
bounded by the O(1/t^2) matrix norm times the bounded |mu_t|. None of these bounds involves
the horizon: the filter path, the tree and its masses are the same for every T, which only
truncates them. Choose t_0 with sup |x*_{t+1} - x*_t| < beta (kappa^+ + kappa^-)/(2 c_0) for all
t >= t_0; it depends on the prior, the shock law, gamma, beta, the rates and c_0 only (with a
finite horizon alone, t_0 = T - 1 would make the statement empty, which is why the horizon is
quantified after t_0). Fix any T. If some (t, z) with t_0 <= t <= T-2 had the static width, then U + D = 1 gives max(U, D) >= 1/2, and the bound of
2d on that side gives a positive-mass outcome moving the target by at least
beta (kappa^+ + kappa^-)/(2 c_t) >= beta (kappa^+ + kappa^-)/(2 c_0) (c_t <= c_0 by 2a), a
contradiction. Hence the width is strictly below the static width there. The remark on marking
is the observation that the deviation's innovation x^+_t (g_{t+1} - 1) - (x*_{t+1} - x*_t) keeps
its first term as t grows; no statement is made about which instruments it keeps coarse.

## Checks

`uv run python checks/100/check.py` (exits non-zero on failure; a check, not a proof; about two
minutes). An assumed one-fund, one-factor M7 instance in the finite-law variant (four-point
prior with the stated mean and covariance, four-point centered shocks, positive gross returns),
T = 5, the linear filter run on the whole observation tree: the information form and
monotonicity of P_t and Sigma_t; V_t against the tree's unconditional innovation covariance;
the target decomposition and the sign of the drift. Then claim 029's grid dynamic programming
with c_t over the tree (pure-learning marking) at two rate settings: 40 bp each way, where every
band is strictly narrower than the (rising) static width and all T-2 bands are narrow; and 2 bp
each way, where the early quarters are coarse: 312 static-width bands all satisfy 2d's
side-weight move bound, and 107 nodes meeting 1c's coarse condition match the tilted static
band. In every coarse node the up and down weights tie (the symmetric shock law makes the
belief innovation dominate the drift), so 2c's tilt sign is not exercised by this check. The
width ceiling, the last-review clips and the clip policy hold at every node in both settings.
All inputs are assumed; no calibration or economic magnitude is reported.

## Not shown

- Everything is proved in the finite-law variant. Under the Gaussian law (M5's), the
  finite-state framework, the positivity of gross returns and the boundedness used in 2d's
  limit argument all fail as stated; 2a-2b's second-moment facts hold there too, but the band
  statements are not proved for it.
- 2d assumes pure-learning marking for the instrument. With real marking the return-driven
  deviation does not vanish, and no statement is made about which instruments stay coarse;
  that is for the analyst's calibrated instances.
- 2c's symmetry of the conditional innovation law is a hypothesis in the finite-law variant.
- The fine-regime leading order (the cube-root band with time-varying coefficients, the kill
  benchmark read with (c_t, V_t) and a drift) is not stated; it is D13's next claim.
- Per-direction bands for the pooled alpha prior (common versus relative alpha directions,
  math's claim 032, provisional) are not treated; V_t is used as a matrix only through G.
- For n > 1 with non-diagonal Sigma_t, only the transferred 2a-2c of claim 029 hold; the
  learning statements 2a-2d are one-instrument (or diagonal) statements.
- The budget is slack; caps enter by clipping; no calibration, materiality or novelty claim.

## Prior art

Mechanism: along a learning path with a fixed unknown mean, the estimation-risk charge falls
deterministically, so the frictionless target's scale grows in a known direction while its
random motion shrinks; a no-trade band whose ceiling is inversely proportional to the risk
charge therefore widens while the target's moves that could keep it at full width vanish, and
the band leans toward the known drift while any coarse regime lasts.

General results checked: the Kalman filter's information form and the monotone decrease of the
error covariance for a fixed parameter (standard linear-filter algebra; `simon1956dynamic` and
`theil1957note` are the certainty-equivalence sources M5 names, wanted, cited at title level;
nothing here rests on them, the identities are proved inline). The coarse/fine anchors and the
band structure: claim 029 (approved), whose proofs this claim transfers rather than repeats.
The kill benchmark `muhlekarbe2017primer` (full text as registered; section 4 read at the
level of its stated setting: a target moved by a mean-reverting state variable with constant
coefficients and a band of width order lambda^{1/3}): its target neither learns nor drifts
deterministically, so its formula, if it applies to M7's fine regime at all, needs time-varying
coefficients, which is exactly what 2a-2b supply as inputs; no such application is made here.
`soner2013homogenization`, `possamai2015homogenization`, `whalley1997asymptotic` (full text) as
in claim 029. `garleanu2009dynamic` and math's claims 030-032 (provisional): the aim portfolio
under quadratic costs carries the learning drift as a factor at least one (math's note); under
proportional costs the relevant target is the Markowitz one, and the drift appears in the tilt
rather than in a trading speed. `pastor2002investing`, `brennan1998role` (learning in
portfolio choice): the shrinking predictive variance is their mechanism; the band consequence
is not in them.

Searched: claims 009, 029, the D12-D13 roadmap entries, the librarian's D12-D14 sweep and D13
follow-up in FINDINGS, math's D12 findings entry (claims 030-032), experiments 021-022's
registrations, the refuted directory, and the registered texts named above at the level stated.
No web search. This is still a claim because the direction's question is how learning-driven
target motion changes the band, and 2a-2d are the exact statements of that at quarterly reviews
in M7; they are elementary, and no priority is claimed for any ingredient.

## Open objections

none

## Review

**Red, 2026-09-28.** I read M7 (on this branch) and checked every part by hand, tested 2a-2b under a finite non-Gaussian law and 2d numerically, and ran `checks/100/check.py`, which passes.

**M7.** It is well defined for this claim.
- It takes M5's instruments, pooled prior, linear filter (with the erratum) and predictive moments, and puts them in M6's proportional costs, caps and quarterly score.
- In the finite-law variant the history is a finite tree, so M7 is an M6 instance with Sigma(t, z) = Sigma_t.
- M6 as frozen has a constant Sigma, and M7 says so; part 1 is the transfer.

**Hand check.**
- *1a-1d.* Red checked, when reviewing claim 029's Sigma(t, z) revision, that every claim-029 argument is per stage: c = c_t at a fixed (t, z). The only two-date statements are 029's primitive coarse conditions, and 1c writes them out correctly with c_t and c_{t+1}. The diagonal-Sigma_t decoupling is right under a slack budget.
- *2a.* With Phi = I and Q = 0, Woodbury gives P_{t+1}^{-1} = P_t^{-1} + H' R^{-1} H.
  - H = [[I_K, 0]; [B^A, I_N]; [B^E, 0]] has full column rank, so P_t decreases to 0, Sigma_t decreases to Sigma_r, c_t is nonincreasing and the static width rises.
  - The n-instrument remark (fixed right side, shrinking metric in the diameter) is right.
- *2b.* The decomposition is an identity, and the bracket is PSD because Sigma_{t+1} <= Sigma_t.
  - Under any law with the prior's first two moments, the linear filter's error has mean 0 and covariance P_t and is uncorrelated with z_{t+1}. So E epsilon = 0 and Cov(epsilon) = K(HPH' + R)K' = P_t - P_{t+1}.
  - The orders are right: V_t = P_t H'R^{-1}H P_{t+1} = O(1/t^2), so the target's moves are O(1/t) in sd and the drift O(1/t^2).
- *2c.* In the coarse regime without marking, (up) gives x*_{t+1} >= lo_{t+1} > hi_t >= x*_t. The bounds lo <= x* - (1 - beta)kappa^+/c and hi >= x* + (1 - beta)kappa^-/c follow from the edge first-order conditions and 029's slope bounds. So U and D are exactly the probabilities of a strict rise or fall, and with symmetry U - D = P(-delta < eta <= delta).
- *2d.*
  - At the static width, 1e gives first-order edges and one-sided landings. So hi_t - x*_t = [kappa^-(1 - beta D) + beta kappa^+ U]/c_t, and lo_{t+1} <= x*_{t+1} (with lo_{t+1} > 0 since lo_{t+1} >= hi_t > lo_t >= 0) gives the up bound; the down bound is symmetric.
  - The zero-move exclusion is right.
  - The t_0 argument is right: bounded theta - m_t and z, K_t -> 0, and the O(1/t^2) drift give a uniform move bound. With max(U, D) >= 1/2 and c_t <= c_0, that contradicts the static width.

**Independent numerical tests** (red's scripts, not committed).
- *2a-2b under a finite law.* One fund and two factors, a four-point prior, four-point centered shocks, the linear filter, 200,000 Monte Carlo paths over 8 quarters:
  - the information form holds and P_t is nonincreasing;
  - Cov(epsilon_{t+1}) matches V_t to a relative 0.2%;
  - the mean of epsilon is 0.004 sd, and its cross-covariance with past innovations is at most 0.7% of V_t: uncorrelated, not centred given the history, as 2b says;
  - the drift has the sign of mu for the one-instrument Sigma_t.
- *2d.* Red's grid dynamic programming with curvature c_t = c (1 + 0.4 t), no marking, 40 random instances. At every static-width band with t <= T-2, all 228 outcomes satisfy 2d's side-weight move bound, with no violation.
  - The same runs confirm the transferred 1b ceiling, the last-review clips and 1d's tilted band with c_t, c_{t+1}.
  - One band reads as static-width while a marked band overlaps the next band by 0.0006. There 1e's predicted narrowing (about 0.00017) is below the grid step, so it is resolution, not a counterexample.
- *`checks/100/check.py`* passes: the filter path; at 40 bp every band strictly narrow; at 2 bp, 312 static-width bands meet 2d's bound and 107 coarse nodes match the tilted band. As the claim says, 2c's tilt sign is not exercised there; red verified 2c by hand only.

**Notes** (not blocking):
1. *1d inherits claim 029's rule-6 point.* 029's 2b cites Rockafellar's sum rule without a ledger entry (lean's note; red's note to mathb, 2026-09-28-claim029-rule6). Once 029 uses the elementary strong-convexity route, the transfer carries it, since the modulus is gamma Sigma_t.
2. *2b's "Both V_t and the bracket are of order 1/t^2"* is right. 2d's parenthesis ("innovation standard deviation and drift both of order 1/t^2 in variance and level respectively") would read more clearly as "innovation sd O(1/t), drift O(1/t^2)".
3. *The Consequence's reading of the kill benchmark.* That `muhlekarbe2017primer` "needs time-varying coefficients and a drift" is a reading, labelled as such. The claim makes no application of it.

**Mechanism (4b).** A Kalman error covariance falling in the information form: an estimation-risk charge falling deterministically raises the static width and adds an outward drift, while the target's random moves shrink like 1/t. Composed with claim 029's exact anchors, this makes the coarse regime a transient of early quarters under pure learning. This is elementary linear filtering plus claim 029, an application. What it adds for D13 is that the fine-regime leading order must carry (c_t, V_t) and the drift.

Verdict: red-passed

## Formalization notes

mathb, 2026-09-28, after PM's approval: prose corrections at lean's request (their note), no
result weakened. 2c now states that the tilt is zero or has the sign of the drift, with the
magnitude formula deciding which, and that the drift has the sign of mu_t only when the
instrument's row of G is nonzero; its proof now proves, rather than assumes, that in the coarse
regime with interior edges and no marking the (up) and (down) outcomes are exactly the positive
and negative target moves. 2d now defines U and D as the closed-landing probabilities (distinct
from claim 029's strict masses, disjoint when the band has positive width), and states t_0 as
determined by the primitives and not by the horizon, quantifying over every horizon. Red's check of lean's points (their note) adds the same G_i != 0
qualifier to 2b's sign statement. PM's note of the same day folds in red's two non-blocking notes:
1d now says the transfer carries claim 029's elementary strong-convexity proof of 2b with modulus
gamma Sigma_t, and 2d's parenthesis reads "innovation sd O(1/t), drift O(1/t^2)".

mathb, 2026-09-29, after formalization: lean's note on 2c's "zero exactly when" clause. It now
reads for kappa > 0, with the kappa = 0 case (tilt zero for every law) stated; the sign and
magnitude formula is unchanged and holds for every kappa. Wording only, as lean's formal statement
has it.

Approved 2026-09-28 by pm: Red's verdict is sound. M7 is an M6 instance with Sigma_t in the finite-law variant, and claim 029's arguments are per stage, so the transfer (1a-1d) holds, with the two-date coarse conditions written with c_t and c_{t+1}. Part 2's information-form filter (full-rank H) gives the rising static width; the target move splits into an O(1/t) belief innovation and an O(1/t^2) outward drift; the tilt leans toward the drift; and 2d's side-weight bound makes the coarse regime a transient of early quarters under pure-learning marking. Red's 200,000-path finite-law check and 40-instance grid DP (228 outcomes) show no violation; the check passes. Mechanism: information-form Kalman covariance plus claim 029, an application; what it adds for D13 is that a fine-regime leading order must carry (c_t, V_t) and the drift. Limits: finite-law variant; with real marking the coarse regime can persist; 2c's tilt sign is verified by hand only; rule-6 point inherited from 029's 2b.


Not machine checked. Part 1 is a transfer of claim 029's formal objects with Sigma indexed by t;
part 2 is finite linear algebra (information form, monotonicity), a finite tree (the variant)
and the inequalities of 2d over claim 029's objects.

Lean, 2026-09-29 (final): parts 1 and 2 are machine checked, in the scope PM confirmed (rule 6b),
and this supersedes "not machine checked" above. The statement is in
`lean/Standalone/M7LearningBandTransfer.lean` and the proof in
`lean/Novel/M7LearningBandTransferProof.lean`, which imports claim 029's proof module
(depends_on [029], Q-04). `lake build` and the axiom audit (standard axioms only) pass. No
hypothesis structure or cited result is used.

Formal objects:
- `Filt` is M5's fixed-means filter: P0, m0, H, d, R, G, Sigma_r, c^E, gamma, with the covariance
  and mean recursions of the Setting and the mean after a history of observations. Its hypotheses
  are P0, R and Sigma_r positive definite, H of full column rank, and gamma > 0.
- `M7` is the finite-law variant: finitely many values of theta and of a quarter's shock, each
  with probability masses, and gross returns a positive function of the observation. Its
  horizon-T instance is claim 029's formal M6, which now takes a covariance Sigma(t, z). The
  states are the observation histories, and the next-state law is the prior's conditional law of
  the path given the history. The formal results use only that the masses are probability laws,
  not the prior's moments or the shocks' centring.

Machine checked:
- 1a: the instance satisfies M6's setting, with Sigma(t, z) = Sigma_t and mu(t, z) = mu_t. From a
  history of positive mass, every positive-mass outcome appends one observation and carries its
  gross return.
- 1b-1d: claim 029's statement for Sigma(t, z), proved by claim 029's own proofs read at a fixed
  (t, z). 1c's two-date condition uses both curvatures, as the Statement writes it. For diagonal
  Sigma(t, z), each instrument's problem is an M6 instance with c_{t,i} = gamma Sigma_{t,ii}, the
  value is the sum of the one-instrument values, and a holding is optimal iff each coordinate is.
- 2a: the information form, P_t positive definite, P_{t+1} <= P_t, P_t -> 0, Sigma_{t+1} <= Sigma_t
  (so every diagonal entry and 1d's quadratic form are nonincreasing), and Sigma_t -> Sigma_r. For
  each instrument, c_{t,i} is nonincreasing with limit gamma Sigma_{r,ii}, and the static width is
  nondecreasing with its limit.
- 2b, pathwise:
  - m_{t+1} - m_t = K_t(y - H m_t - d), and the target decomposition;
  - the bracket is positive semidefinite, and V_t = K_t(H P_t H' + R)K_t' is positive definite;
  - Sigma_{t,ii} falls strictly iff G_i != 0;
  - for one instrument, the drift's scalar form, with the sign of mu_t when G_0 != 0 and zero when
    G_0 = 0.

  The 1/t^2 orders are also machine checked, as exact limits: t(t+1)V_t -> J^{-1} with
  J = H'R^{-1}H, and t(t+1)[Sigma_{t+1}^{-1} - Sigma_t^{-1}] -> Sigma_r^{-1} G J^{-1} G' Sigma_r^{-1}.
- 2c: on any one-instrument M6 instance in the coarse regime, with no marking and interior edges,
  (up) iff the target rises and (down) iff it falls. If the move is eta + delta on positive-mass
  outcomes, the law of eta is symmetric (every expectation of f(eta) equals that of f(-eta)), and
  kappa^+ = kappa^- = kappa, then tau = sign(delta) beta kappa P(|eta| <= |delta|)/c_t. For
  kappa > 0, tau = 0 iff no positive-mass eta lies in (-|delta|, |delta|]. With 2b's
  decomposition this is the Statement's 2c.
- 2d: at static width with no marking, every positive-mass outcome is an up or a down landing,
  U + D = 1, every outcome moves the target, and the two move bounds hold. Eventual narrowing:
  there is a t_0, chosen from M7's data before the horizon, such that for every T, every t with
  t_0 <= t <= T - 2, and every history of positive mass, the band is strictly narrower than the
  static width. The proof bounds the target's moves uniformly over histories through the mean's
  information form, and the bound tends to 0.

Paper-level (PM's scope): 2b's unconditional moments of epsilon_{t+1} over the finite joint law
(mean zero, covariance V_t), with the best-linear-predictor argument behind them. No formal
conclusion uses them. Not formalized: the Consequence for D13 (a reading), the remark on real
marking, and the Checks.

Prose point, sent to mathb and red: 2c's "zero exactly when the conditional law puts no mass in
(-|delta|, |delta|]" needs kappa > 0; at kappa = 0 the tilt is zero for every law. The formal
statement adds kappa > 0 for that one conjunct only.

Limits kept from PM's approval: the finite-law variant only; with real marking the coarse regime
can persist; the mechanism is an application of the information-form filter and claim 029.

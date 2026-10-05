---
id: 31
title: "In M5, premium beliefs leak into fund choice exactly through the factor directions the ETFs do not span: the fund problem's mean gains the unreachable premium net of its ETF hedge and its risk the unreachable factor and estimation variance net of the hedge (a Schur complement), the ETF exposure is myopic plus a minimum-variance hedge of the funds' unreachable exposure, and with spanning the leak vanishes"
status: formalized
model_version: M5
depends_on: [30]
axioms_used: []
formal: lean/Standalone/M5MissingDirectionLeak.lean
direction: D12
---
## Statement

D12's second claim. Claim 030 (math/claim030-m5-policy) separates exposure from alpha when the
ETFs span the factors exactly (M = K, B^E invertible) and ETFs are costless, residual-free and
fee-free. This claim removes the spanning hypothesis, keeping the other three, and shows what
bundling does when some factor direction is reachable only through the funds: the program memo's
Q3 mechanism ("premium errors leak into fund choice unless the factor part is offset with ETFs")
made exact. It uses claim 030's part 3 (the partial-adjustment policy of a linear-quadratic
tracking problem with a martingale mean and deterministic risk) as its only lemma, restated below
as a definition; claim 030 is proposed on math/claim030-m5-policy, and this claim merges after it.

**Setting.** M5 in claim 030's setting and reference case (block-diagonal Sigma_z, decoupled
filter, baseline Phi = I), finite horizon T, gamma > 0, rho in (0, 1]; ETF frictions off:
Lambda_E = 0, Sigma_E = 0, c^E = 0, so the cost is (1/2)(Delta x^A)' Lambda_A (Delta x^A) with
Lambda_A positive definite. The ETF loading matrix B^E (M x K) has full row rank M <= K, so its
rows are linearly independent and span the *reachable* subspace L_E = row(B^E) of R^K, of
dimension M; L_E^perp is the *unreachable* subspace. Write Pi_R, Pi_U for the orthogonal
projections onto L_E and L_E^perp, and

```
Sigma~_t = Sigma_f + P^lambda_t   (the predictive factor covariance: return plus premium-estimation risk),
Sigma~_RR = Pi_R Sigma~_t Pi_R,  Sigma~_RU = Pi_R Sigma~_t Pi_U,  Sigma~_UU = Pi_U Sigma~_t Pi_U   (blocks on L_E, L_E^perp),
```

with Sigma~_RR invertible on L_E (write Sigma~_RR^{-1} for its inverse there) and the Schur
complement Sigma~_{U.R} = Sigma~_UU - Sigma~_UR Sigma~_RR^{-1} Sigma~_RU on L_E^perp (Sigma~_UR
= Sigma~_RU'). Define the *hedge map* J_t = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU (K x K: a vector's
unreachable projection minus the reachable position that hedges it at minimum variance, so
J_t' = Pi_U - Sigma~_UR Sigma~_RR^{-1} Pi_R) and the *reduced fund moments*

```
alpha^red_t = alpha_hat_t + B^A J_t' lambda_hat_t,
Sigma^red_t = Sigma_A + P^alpha_t + B^A Sigma~_{U.R} B^A'.
```

1. **Coordinates.** The map x = (x^A, x^E) -> (y_R, x^A) with y_R = Pi_R B' x = Pi_R B^A' x^A +
   B^E' x^E is a linear bijection between R^{N+M} and L_E x R^N, with inverse x^E = (B^E')^+ (y_R
   - Pi_R B^A' x^A), (B^E')^+ the left inverse of B^E' on L_E. The total exposure is y = y_R +
   Pi_U B^A' x^A: the unreachable exposure is carried by the funds alone.

2. **The ETF exposure is myopic plus a hedge.** At every review the optimal reachable exposure is

   ```
   y_R,t = Sigma~_RR^{-1} [ (1/gamma) Pi_R lambda_hat_t - Sigma~_RU B^A' x^A_t ],
   ```

   the factor-space Markowitz exposure on L_E minus the minimum-variance hedge, through the
   ETFs, of the funds' unreachable exposure; the ETF position is x^E_t = (B^E')^+ (y_R,t -
   Pi_R B^A' x^A_t). When Sigma~_RU = 0 (the factor shocks and the premium-estimation errors of
   reachable and unreachable directions are uncorrelated) the hedge vanishes and the ETF position
   nets only the funds' reachable by-product, as in claim 030.

3. **The fund problem and its policy.** The fund positions solve the linear-quadratic problem of
   claim 030 part 3 with mean alpha^red_t, risk Sigma^red_t and cost Lambda_A, where claim 030's
   part 3 extends verbatim to a deterministic time-varying mean map G_t, here G^red_t =
   [B^A J_t', I_N] acting on m_t = (lambda_hat_t, alpha_hat_t), with the substituted recursion
   C_t = Lambda D_t^{-1} (G_t + rho C_{t+1}), L_t = D_t^{-1} (G_t + rho C_{t+1}) (the backward
   verification uses only that G_t is deterministic and m_t a martingale):

   ```
   x^A_t = x^A_{t-1} + Gamma^A_t (aim^A_t - x^A_{t-1}),
   ```

   with Gamma^A_t and aim^A_t from claim 030's recursion applied to (alpha^red_t, Sigma^red_t,
   Lambda_A); alpha^red_t is affine in m_t, so aim^A_t is affine in m_t and E_t aim^A_{t+1} =
   aim^A_{t+1}(m_t). In particular the fund Markowitz portfolio is
   (gamma Sigma^red_t)^{-1} (alpha_hat_t + B^A J_t' lambda_hat_t).

4. **The leak.** The fund policy's sensitivity to premium beliefs at review t, restricted to
   the unreachable directions v in L_E^perp (on which J_s' v = v for every s), is
   D_t^{-1} M_t B^A v with M_t = I + rho Lambda_A D_{t+1}^{-1} M_{t+1}, M_{T-1} = I (red's
   reduction). *Vanishing.* When B^A's rows lie in L_E (the funds' loadings are replicable),
   Pi_U B^A' = 0, so J_t B^A' = 0 (equivalently B^A J_t' = 0) for every t, the sensitivity
   vanishes on L_E^perp and on L_E alike, and the leak is zero: claim 030's separation.
   *Converse.* If some fund loading has an unreachable component, so that B^A v != 0 for some v
   in L_E^perp, then the sensitivity D_t^{-1} M_t B^A v is nonzero whenever M_t is nonsingular,
   which holds at t = T-1 (M_{T-1} = I), at every t when T <= 3, in the stationary
   infinite-horizon limit (M = (I - rho Lambda_A D^{-1})^{-1}), and at any t at which the
   symmetric part of Lambda_A^{-1/2} M_{t+1} Lambda_A^{1/2} is positive definite; that M_t is
   nonsingular at every t for every horizon is verified numerically (red: 100,000 random cost
   matrices and covariance paths, every eigenvalue of M_t with real part at least 1) and not
   proved (Not shown). In those cases the fund's aim responds to lambda_hat_t through J_t (the
   unreachable premium net of its ETF hedge), and its risk Sigma^red_t gains the term
   B^A Sigma~_{U.R} B^A', positive semidefinite and nonzero, through which the unreachable
   premium-estimation covariance P^lambda_t enters; and that risk term changes the policy's
   own-position coefficient K_t at every t (not only where M_t is nonsingular), because the
   Riccati map is Loewner-increasing in the risk matrix: with the term, D_t exceeds its value
   without it by at least gamma B^A Sigma~_{U.R} B^A' != 0, so K_t = D_t^{-1} Lambda_A differs
   (red's argument, checked on 300 instances). Premium
   beliefs and their estimation error therefore reach fund choice exactly through the
   unhedgeable part of the funds' loadings, as a mean term and as a risk term, and nowhere else
   under the three zero-friction hypotheses.

5. **Learning and the leak.** Along the deterministic path P^lambda_t -> 0 (identifiable premia),
   Sigma~_{U.R} decreases to the return-only Schur complement Sigma_{f,U.R}, so the risk leak
   shrinks with learning while the mean leak B^A J_t' lambda_hat_t persists: an unreachable
   premium is a permanent reason for fund positions, its estimation error a transient one.

**One sentence without model nouns.** When the cheap instrument cannot reach every direction, the
costly positions inherit the unreachable directions' expected return net of the best cheap hedge
and their variance net of that hedge, so estimation error in the shared coefficients reaches the
costly choice exactly through the unhedgeable part of what those positions carry, as a mean term
that persists and a risk term that learning removes.

## Proof

### 1. Coordinates

B^E' : R^M -> R^K is injective with image L_E (full row rank of B^E), so it has a left inverse
(B^E')^+ = (B^E B^E')^{-1} B^E on L_E. Given (y_R, x^A) in L_E x R^N, y_R - Pi_R B^A' x^A lies in
L_E and x^E = (B^E')^+ (y_R - Pi_R B^A' x^A) is the unique ETF position with Pi_R B' x = y_R;
conversely any x gives y_R = Pi_R B' x in L_E. Pi_U B' x = Pi_U B^A' x^A + Pi_U B^E' x^E =
Pi_U B^A' x^A since B^E' x^E lies in L_E.

### 2. The reachable exposure

In the reference case with ETF frictions off, claim 030's stage reward at review t is

x' mu_t - (gamma/2) x' Sigma_t x - (1/2)(Delta x^A)' Lambda_A (Delta x^A)
= y' lambda_hat_t + x^A' alpha_hat_t - (gamma/2) [ y' Sigma~_t y + x^A' (Sigma_A + P^alpha_t) x^A ]
  - (1/2)(Delta x^A)' Lambda_A (Delta x^A),

using Sigma_t = B Sigma~_t B' + diag(Sigma_A + P^alpha_t, 0) (claim 030 part 1, with Sigma_E = 0)
and mu_t = B lambda_hat_t + e_A alpha_hat_t (c^E = 0). Substitute y = y_R + Pi_U B^A' x^A and
expand y' Sigma~_t y = y_R' Sigma~_RR y_R + 2 y_R' Sigma~_RU B^A' x^A + x^A' B^A Sigma~_UU B^A' x^A
and y' lambda_hat = y_R' Pi_R lambda_hat + x^A' B^A Pi_U lambda_hat. The reward depends on y_R
only through its own review (no cost, no state), so the dynamic problem's Bellman maximization
over (y_R,t, x^A_t) can maximize over y_R,t first for each x^A_t: the y_R-part is the strictly
concave quadratic y_R' Pi_R lambda_hat - (gamma/2) y_R' Sigma~_RR y_R - gamma y_R' Sigma~_RU B^A' x^A
on L_E, whose maximizer is the displayed y_R,t. (Sigma~_RR is positive definite on L_E because
Sigma~_t is positive definite.)

### 3. The reduced fund problem

Substituting the maximizer, the y_R-part's maximum equals (1/2)(Pi_R lambda_hat/gamma^{1/2}
... explicitly (gamma/2) v' Sigma~_RR^{-1} v with v = (1/gamma) Pi_R lambda_hat - Sigma~_RU B^A' x^A,
which expands to a constant in x^A, plus the linear term -x^A' B^A Sigma~_UR Sigma~_RR^{-1} Pi_R
lambda_hat, plus the quadratic (gamma/2) x^A' B^A Sigma~_UR Sigma~_RR^{-1} Sigma~_RU B^A' x^A.
Adding the x^A-terms of the stage reward gives

x^A' [alpha_hat + B^A (Pi_U - Sigma~_UR Sigma~_RR^{-1} Pi_R) lambda_hat]
- (gamma/2) x^A' [Sigma_A + P^alpha + B^A (Sigma~_UU - Sigma~_UR Sigma~_RR^{-1} Sigma~_RU) B^A'] x^A
- (1/2)(Delta x^A)' Lambda_A (Delta x^A) + (terms in m_t only),

that is, x^A' alpha^red_t - (gamma/2) x^A' Sigma^red_t x^A - cost, with J_t' = Pi_U -
Sigma~_UR Sigma~_RR^{-1} Pi_R (so J_t = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU, using the symmetry
of Sigma~_t) and Sigma~_{U.R} the Schur complement, positive semidefinite on L_E^perp. Sigma^red_t
is positive definite (Sigma_A is) and deterministic; alpha^red_t is affine in the martingale m_t.
The fund problem is therefore exactly the problem of claim 030 part 3 with (alpha^red_t,
Sigma^red_t, Lambda_A) in place of (mu_t, Sigma_t, Lambda), whose solution is the displayed
partial adjustment, and its Markowitz portfolio is (gamma Sigma^red_t)^{-1} alpha^red_t.

### 4. The leak

By part 3 the fund policy is x^A_t = K^A_t x^A_{t-1} + L^A_t m_t + l^A_t with L^A_t =
D_t^{-1}(G^red_t + rho C_{t+1}) and C_{t+1} = Lambda_A L^A_{t+1}. For v in L_E^perp, J_s' v =
Pi_U v - Sigma~_UR Sigma~_RR^{-1} Pi_R v = v for every s, so the lambda-columns of L^A_t applied to
v satisfy L^lambda_t v = D_t^{-1}(B^A v + rho Lambda_A L^lambda_{t+1} v), and by backward induction
L^lambda_t v = D_t^{-1} M_t B^A v with M_t = I + rho Lambda_A D_{t+1}^{-1} M_{t+1} and
M_{T-1} = I (red's reduction; the first filing's "sum of invertible multiples" argument does not
establish nonvanishing, since such sums can cancel).

Vanishing: if every row of B^A lies in L_E then Pi_U B^A' = 0, so y = y_R for every x (part 1),
the expansion of part 2 has no term joining lambda_hat_t or Sigma~_t to x^A, alpha^red_t =
alpha_hat_t and Sigma^red_t = Sigma_A + P^alpha_t, and J_t B^A' = Pi_U B^A' - Pi_R Sigma~_RR^{-1}
Sigma~_RU Pi_U B^A' = 0 for every t; the sensitivity to lambda_hat is zero on every direction,
and the policy is claim 030 part 4(a).

Converse, where M_t is nonsingular: then D_t^{-1} M_t is nonsingular and D_t^{-1} M_t B^A v != 0
whenever B^A v != 0, which is the case for some v in L_E^perp exactly when some row of B^A has a
nonzero unreachable component. Nonsingularity of M_t: at t = T-1, M = I. For T <= 3: M_{T-2} =
I + rho S with S = Lambda_A D_{T-1}^{-1} similar to the positive semidefinite
Lambda_A^{1/2} D_{T-1}^{-1} Lambda_A^{1/2}, so its eigenvalues are at least 1; and M_{T-3} =
I + X Y with X = rho Lambda_A D_{T-2}^{-1} similar to a positive semidefinite matrix and
Y = M_{T-2} similar to a positive definite one, so det(I + XY) >= 1 (red's verification). In the
stationary infinite-horizon limit M solves M = I + rho Lambda_A D^{-1} M, so M =
(I - rho Lambda_A D^{-1})^{-1}, invertible since rho Lambda_A D^{-1} is similar to rho
Lambda_A^{1/2} D^{-1} Lambda_A^{1/2} with eigenvalues in [0, rho) (D > Lambda_A). In general: if
the symmetric part of M~_{t+1} = Lambda_A^{-1/2} M_{t+1} Lambda_A^{1/2} is positive definite, then
M_t is nonsingular: M_t v = 0 gives, with w = M~_{t+1} Lambda_A^{-1/2} v and S =
Lambda_A^{1/2} D_{t+1}^{-1} Lambda_A^{1/2} > 0, the identity Lambda_A^{-1/2} v = -rho S w, hence
rho w' S w = -w' Lambda_A^{-1/2} v = -(Lambda_A^{-1/2} v)' M~_{t+1} (Lambda_A^{-1/2} v) < 0 unless
v = 0, a contradiction (red's lemma). The induction does not close, because positive
definiteness of the symmetric part is not shown to propagate; red's numerical search (100,000
random cost matrices and arbitrary covariance paths, n = 2-3, T <= 9) found every eigenvalue of
M_t with real part at least 1 and the smallest eigenvalue of the symmetric part of M~_t equal
to 0.88 over 50,000 paths, and the check reports the leak's size on its instances. The
premium-estimation covariance P^lambda_t enters Sigma^red_t through Sigma~_{U.R} and the mean
through J_t, and nowhere else. The risk term's effect on the policy is provable at every t:
write Delta_t = B^A Sigma~_{U.R} B^A', positive semidefinite and nonzero when some fund loading
has an unreachable component (Sigma~_{U.R} is positive definite on L_E^perp), and compare the
fund block's recursion with risk Sigma_A + P^alpha_t + Delta_t against the same recursion with
risk Sigma_A + P^alpha_t. The map D -> Lambda_A - Lambda_A D^{-1} Lambda_A is Loewner-increasing
in D on positive definite matrices (D -> -D^{-1} is), and D_t = Lambda_A + gamma Sigma_t +
rho A_{t+1} is Loewner-increasing in Sigma_t and in A_{t+1}; so by backward induction from
A_T = 0 the recursion with the term has A_{t+1} at least the recursion without it, hence
D_t(with) - D_t(without) >= gamma Delta_t != 0, D_t(with) != D_t(without), and
K_t = D_t^{-1} Lambda_A differs at every t (red's argument).

### 5. Learning

P^lambda_t is nonincreasing in the Loewner order along the Kalman path with a constant state, and
tends to 0 when (I_K) is observed with positive definite noise (the premia are identified from
the factor returns, whose observation matrix on the lambda block is the identity), so Sigma~_t
decreases to Sigma_f and the Schur complement, a monotone function of the block matrix in the
Loewner order, decreases to that of Sigma_f. The mean term B^A J_t' lambda_hat_t has J_t
converging to the return-only hedge map and lambda_hat_t a martingale with nonvanishing limit in
general.

## Checks

`checks/031/check.py` (exits non-zero on failure; a check, not a proof). On instances with 2 funds,
1 ETF and 2 factors (the missing-direction shape the analyst was asked to add to experiment 021 as
Q5), and with 3 funds, 2 ETFs and 2 factors as the spanning control, with ETF frictions off: the
full recursion of claim 030 in the original coordinates is compared with part 2's exposure rule
plus part 3's reduced fund recursion, coefficient by coefficient at every review; the fund
policy's sensitivity to lambda_hat is compared with L^A_t B^A J_t'; the leak is verified to
vanish when the fund loadings are moved into the ETF span, and to be nonzero otherwise; the
Schur complement's monotone decrease along the Kalman path is checked; and with correlated
factors (Sigma_f not diagonal) the hedge term in the ETF exposure is verified against a direct
minimum-variance regression.

## Not shown

- ETF frictions on (Lambda_E, Sigma_E, c^E nonzero) together with a missing direction: claim
  030's three cross terms and this claim's leak then combine in one joint recursion; not
  stated in closed form.
- The converse of part 4 at every review for every horizon: it is exactly the nonsingularity of
  M_t = I + rho Lambda_A D_{t+1}^{-1} M_{t+1}, proved at t = T-1, for T <= 3, in the stationary
  limit, and under a symmetric-part condition on M_{t+1}; in general it is verified numerically
  (red) and not proved. A route: show the symmetric part of Lambda_A^{-1/2} M_t Lambda_A^{1/2}
  stays positive definite along the recursion.
- Redundant ETFs (M > rank B^E) and the choice among replicating ETF portfolios.
- Long-only and funding constraints (D13), where a binding ETF cap creates an unreachable
  direction dynamically; the analyst's experiment 021 notes that caps make funds carry exposure.
- The magnitude of the leak at calibrated scale.
- The claim depends on claim 030's part 3 (proposed, math/claim030-m5-policy); it merges and
  is reviewed after that claim.

## Prior art

Mechanism: When the cheap instrument spans only a subspace of the directions the costly positions
carry, maximizing out the costless coordinate turns the costly problem into one whose expected
return is the original plus the unreachable directions' return net of the best cheap hedge, and
whose risk is the original plus the unreachable directions' variance net of that hedge (a Schur
complement); so shared-coefficient estimation error reaches the costly choice exactly through the
unhedgeable component.

General results checked: partial maximization of a quadratic over a costless coordinate giving a
Schur complement (elementary, proved in part 3); `treynor1973security` (equation (16)): its
explicit market position nets the active portfolio's by-product exactly because the market asset
spans the single factor; the missing direction is the case it does not cover, and claim 005 (M2)
is this lab's one-quarter version of that geometry (a direction outside the ETF span versus a
match blocked by funding), which this claim makes dynamic and quantified through J_t and
Sigma~_{U.R}; `garleanu2009dynamic` and `abeille2016lqg` (the policy machinery, cited through
claim 030); `pastor2002investing` (fund choice with benchmark and nonbenchmark assets in a static
Bayesian setting, where the unspanned part of a fund's return is likewise what the investor
cannot hedge; its Section 2 mispricing-versus-benchmark framing is the static analogue of the
mean leak). Claims 027-028 (M2 two-stage separation) are the constrained one-quarter analogue.

Searched: claims 004-005, 027-030, the D4 and D12 FINDINGS entries, model/SPEC.md M5, and the
refuted directory. This is a claim because the leak's exact form (hedge map and Schur complement
inside a dynamic partial-adjustment policy with learning) is stated by no registered source, and
because it is the fund-of-funds content D12's restated question asks for; no priority is claimed
for the Schur-complement step.

## Open objections

PM, 2026-09-28: red's required correction 1 (part 4's every-t converse, proved only at t = T-1,
for T <= 3 and in the stationary case) was open and the status reset to proposed so that red
records a fresh verdict on math's revision; PM holds approval until then.

Red (review, red-passed with three required corrections, made on math/claim031-corrections):
part 4's every-t converse was unproved (the sum-of-invertible-multiples step can cancel); it is
restated for the proved cases with red's reduction to the nonsingularity of M_t and the general
case moved to Not shown as numerically verified; claim 030's part 3 lemma is stated for the
time-varying mean map with the substituted recursion; depends_on is [30]; the nit J_t B^A' = 0
fixed. Red should also re-test: the invertibility claims on L_E (confirmed in red's review) and
the risk term's effect on the policy.

## Review

**Red, 2026-09-28.** I checked parts 1-5 by hand, tested parts 2-5 numerically with red's own script (written without reading `checks/031/check.py`), and ran `checks/031/check.py`, which passes. Parts 1-3 and 5, which carry the claim's content, hold exactly: the reachable exposure rule, and the reduced fund mean and risk with the hedge map and the Schur complement. Part 4's converse ("nonzero leak at every t") is proved only at T-1 and when T <= 3. Red finds it true numerically but asks for a proof or a narrower statement. Three smaller corrections follow.

**Hand check.**
- *Setting.* With Sigma_E = 0 and M < K, Sigma_t = B Sigma~_t B' + diag(Sigma_A + P^alpha_t, 0) is still positive definite: x' Sigma_t x = 0 forces x^A = 0 and then B^E' x^E = 0, so x^E = 0 by full row rank. The block-diagonal filter gives no premium-alpha cross term, and mu_t = B lambda_hat + e_A alpha_hat with c^E = 0.
- *Part 1.* (B^E B^E')^{-1} B^E is a left inverse of B^E', and Pi_U B^E' = 0, so the unreachable exposure is Pi_U B^A' x^A.
- *Part 2.*
  - The two expansions are right: y' lambda_hat = y_R' Pi_R lambda_hat + x^A' B^A Pi_U lambda_hat, and y' Sigma~ y has cross term 2 y_R' Sigma~_RU B^A' x^A.
  - With Lambda_E = 0, y_R has no cost and no state. The continuation depends on x^A only, so maximizing y_R first is legitimate, and the first-order condition gives the displayed y_R,t.
- *Part 3.*
  - The partial maximum is (gamma/2) v' Sigma~_RR^{-1} v, which gives the linear term x^A' B^A J_t' lambda_hat and the Schur-complement risk.
  - J_t' = Pi_U - Sigma~_UR Sigma~_RR^{-1} Pi_R is the transpose of the displayed J_t.
  - Sigma^red_t is positive definite and deterministic.
- *Part 5.* The Schur complement equals min_r of the quadratic form over the reachable part, so it is Loewner-monotone in Sigma~_t. P^lambda_t decreases to 0, because the premia are observed through f with identity loading. The mean leak's limit B^A J_inf' theta is nonzero in general.

**Independent numerical tests** (red's script, not committed). The instances are 200 random M5 shapes with N 1-3, K 2-4 and M 1-K, ETF frictions off, nondiagonal Sigma_f, Sigma_A and priors, gamma 5, rho 0.97 and T = 8.
- *Parts 2 and 3.* Claim 030's recursion in the original coordinates is computed with Lambda = diag(Lambda_A, 0). It agrees with part 2's exposure rule plus part 3's reduced recursion in every K_t and L_t coefficient, fund rows and ETF rows, at every review, to 5.7e-11 relative. The worst instance has cond(B^E B^E') = 2.7e5.
- *Spanning.* With fund loadings drawn in row(B^E), the fund policy's lambda-sensitivity is at most 1.1e-14 over 100 instances.
- *Part 5.* Sigma~_{U.R} is Loewner-nonincreasing at every step: the smallest eigenvalue of the step difference is -1.4e-17 over 300 instances with T = 12.
- *Part 4's converse.* The ratio |fund lambda-sensitivity on L_E^perp| / |B^A Pi_U| is at least 0.34 at every t over the same 300 instances.

**Required correction 1 (part 4's converse: the proof has a gap).**
- The proof says the lambda-sensitivity is a sum of terms "multiples of B^A J_s' by invertible matrices" and concludes that it is nonzero. A sum of such terms can cancel, so this does not follow.
- The exact reduction is this. For v in L_E^perp, J_s' v = v at every s. So the sensitivity along v is D_t^{-1} M_t B^A v, with M_t = I + rho Lambda_A D_{t+1}^{-1} M_{t+1} and M_{T-1} = I.
- Part 4's "iff at every t" is therefore exactly the statement that M_t is nonsingular. By the same argument, the other direction also needs the sensitivity along L_E to vanish, which holds because Pi_U B^A' = 0 makes B^A J_s' = 0 for every s. Also, B^A J_t' = 0 is equivalent to Pi_U B^A' = 0, which does not depend on t.
- What red can prove:
  - M_{T-1} = I.
  - M_{T-2} = I + rho S with S = Lambda_A D_{T-1}^{-1}, similar to a positive semidefinite matrix.
  - M_{T-3} has det(I + XY) >= 1, where X = rho Lambda_A D^{-1} is similar to a positive semidefinite matrix and Y = M_{T-2} to a positive definite one.
  - In the stationary case, M = (I - rho Lambda_A D^{-1})^{-1}.
  - If sym(Lambda_A^{-1/2} M_{t+1} Lambda_A^{1/2}) is positive definite, then M_t is nonsingular: M_t v = 0 gives rho w'Sw = -w'v, with w = M~_{t+1} v.
- For longer horizons, red has no proof. Numerically, over 100,000 random cost matrices and arbitrary covariance paths (n 2-3, T <= 9), every eigenvalue of M_t has real part >= 1; some eigenvalues are complex, 37 times. Over 50,000 paths the smallest eigenvalue of sym(Lambda_A^{-1/2} M_t Lambda_A^{1/2}) is 0.88.
- Please either prove M_t nonsingular (the symmetric-part induction above is one route), or state the converse at t = T-1 and at every t when T <= 3 or the risk is stationary, with "every t" numerically verified in general.
- The same gap is in part 4's closing risk-term sentence, which is fine for Sigma^red itself but not for its effect on the policy.

**Required correction 2 (part 3's lemma).** Claim 030's part 3 is stated for a constant mean map G, since mu_t = G m_t. Here the mean is G^red_t m_t with G^red_t = [B^A J_t', I_N], which is deterministic but time-varying, so "exactly the problem of claim 030 part 3" is not literally true. Claim 030's verification argument goes through unchanged with C_t = Lambda D_t^{-1} (G_t + rho C_{t+1}), and E_t aim_{t+1} = aim_{t+1}(m_t) still holds, as the Open objections say. Please state this extension, in one line, with the substituted recursion.

**Required correction 3 (front matter).** `depends_on: []` should be `[030]`: the claim uses claim 030's part 3 as its lemma, and claim 100's `[029]` is the precedent.

**Nit.** Part 4 of the Statement says "J_t' B^A' = 0". The quantity that vanishes is J_t B^A' (equivalently B^A J_t'). J_t' B^A' = -Sigma~_UR Sigma~_RR^{-1} B^A' is not zero in general when B^A's rows lie in L_E.

**Open objections answered.**
- The invertibility claims on L_E hold: Sigma~_RR is positive definite on L_E, and the left inverse of B^E' is as stated.
- E_t aim^A_{t+1} = aim^A_{t+1}(m_t) survives the time dependence (correction 2).
- The converse at every t is the gap in correction 1.

**Mechanism (4b).** The claim's own statement is right: it partially maximizes a quadratic over a costless coordinate, which yields a Schur complement, inside claim 030's LQ tracking. The Schur complement step is elementary. `pastor2002investing` is the static analogue, and `treynor1973security` eq. (16) the spanning case. What is new for D12 is the exact form of the leak in a dynamic learning policy: a persistent mean term through J_t, and a transient risk term through Sigma~_{U.R}.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-28): parked at proposed while red's required corrections (part 4's converse, depends_on [30]) are rechecked; red re-reviews the corrected claim (entered by the human's interface on PM's stated reason, f08c7f0/1c23df1).

Verdict: withdrawn (PM, 2026-09-28): red's required correction 1 changed the Statement (part 4's every-t converse was unproved beyond T <= 3 and the stationary case). Math has revised the claim (1c23df1), and red records a fresh verdict on the revision.

**Red, recheck of math's revision (1c23df1), 2026-09-28.** All three required corrections and the nit are made correctly. Nothing new is asserted beyond what is proved.
- *Correction 1: part 4's converse.* The Statement now asserts nonvanishing only where M_t is nonsingular. It lists the proved cases: t = T-1, every t when T <= 3, the stationary limit, and the symmetric-part condition. "Every t for every horizon" is in Not shown as numerically verified, with the route.
  - Red rechecked each proved case. For T <= 3, XY is similar to Y~^{1/2} (rho S_1) Y~^{1/2}, which is positive semidefinite, where Y~ = I + rho S_2 is the Lambda_A^{1/2}-conjugate of M_{T-2}; so the eigenvalues of M_{T-3} are real and at least 1. In the stationary limit the eigenvalues of rho Lambda_A^{1/2} D^{-1} Lambda_A^{1/2} lie in [0, rho).
  - The symmetric-part lemma is stated more carefully than in red's review: u = Lambda_A^{-1/2} v, w = M~_{t+1} u, u = -rho S w, so rho w'Sw = -u' M~_{t+1}' u < 0. It is right.
  - The Proof now derives L^lambda_t v = D_t^{-1} M_t B^A v by backward induction from J_s' v = v on L_E^perp. The vanishing direction uses J_t B^A' = 0 for every t.
- *Correction 2: the lemma extension.* Part 3 now states claim 030's part 3 for a deterministic time-varying G_t, with C_t = Lambda D_t^{-1} (G_t + rho C_{t+1}). This is right: the backward verification uses only that G_t is deterministic and that m_t is a martingale.
- *Correction 3: `depends_on: [30]`.* This is right in substance. Claim 100 writes `[029]`, so the two differ in zero-padding only; red leaves the format to PM.
- *Nit.* It is fixed: "J_t B^A' = 0 (equivalently B^A J_t' = 0)".
- *Optional.* Part 4's closing sentence says the risk term's effect on the policy is "the same nonsingularity question". It is in fact provable at every t, and easily.
  - The added term B^A Sigma~_{U.R} B^A' is positive semidefinite and nonzero. A_{t+1} is Loewner-nondecreasing in the risk matrices, because the Riccati map A = Lambda - Lambda D^{-1} Lambda is increasing in D.
  - So D_t strictly increases in the Loewner order, and K_t = D_t^{-1} Lambda_A changes at every t, since Lambda_A is invertible.
  - Red checked this numerically: over 300 random instances with T = 10, the smallest relative change in K_t caused by the risk term is 1.1e-4, and it is nonzero at every t.
  - The sentence could say so. This is not required.
- `checks/031/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's recheck of math's revision (1c23df1) is sound. Part 4's converse now asserts nonvanishing only where M_t is nonsingular, with the proved cases (t=T-1, T<=3, the stationary limit, the symmetric-part condition) rechecked by red; every t in general is in Not shown as numerically verified. Claim 030's part 3 extends to a deterministic time-varying mean map; depends_on [30]; the J_t B^A' nit is fixed; the check passes. Earlier: red's hand check of parts 2, 3 and 5, and 200 random instances agreeing with claim 030's recursion to 6e-11. Mechanism: partial maximization over a costless coordinate, giving a Schur complement inside claim 030's LQ tracking, an application; pastor2002investing is the static analogue and treynor1973security eq. (16) the spanning case. What D12 gains is the exact dynamic leak: a persistent mean term through J_t and a transient risk term. Limit: part 4's every-t converse is numerical only beyond the proved cases.


Not machine checked. Linear algebra (a bijection, a Schur complement) plus claim 030's part 3.

Lean, 2026-09-28 (final): parts 1-5 are machine checked, and this supersedes "not machine
checked" above. The statement is in `lean/Standalone/M5MissingDirectionLeak.lean` and the proof
in `lean/Novel/M5MissingDirectionLeakProof.lean`, which imports claim 030's proof module
(depends_on [30], Q-04). `lake build`, the axiom audit (standard axioms only) and
`checks/031/check.py` pass. No hypothesis structure or cited result is used.

Formal objects. The claim's objects are defined literally:
- Pi_R = B^E'(B^E B^E')^{-1}B^E and Pi_U = I - Pi_R;
- Sigma~_RR^{-1} realized as B^E'(B^E Sigma~ B^E')^{-1}B^E, which the statement checks is the
  inverse of Sigma~_RR on L_E;
- J = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU and the Schur complement Sigma~_UU - Sigma~_UR
  Sigma~_RR^{-1} Sigma~_RU;
- (B^E')^+ = (B^E B^E')^{-1}B^E, and the reduced moments.

There are two problems, both in claim 030's formal form:
- the joint problem in (x^A, x^E): cost diag(Lambda_A, 0), risk gamma(B Sigma~_t B' +
  diag(Sigma_A + P^alpha_t, 0)), mean map [[B^A, I]; [B^E, 0]];
- the reduced fund problem: cost Lambda_A, risk gamma Sigma^red_t, and the time-varying mean map
  G^red_t = [B^A J_t', I].

Claim 030's formal problem was generalized for this to a deterministic, time-varying G_t (part 3
here). Claim 030's own case is the constant one.

Machine checked:
- Part 1: Pi_R is the orthogonal projection onto row(B^E); the coordinate bijection and its
  inverse through (B^E')^+; y = y_R + Pi_U B^A'x^A.
- Part 2: at every review the joint policy's reachable exposure is
  Sigma~_RR^{-1}[(1/gamma)Pi_R lambda_hat - Sigma~_RU B^A'x^A]; the ETF position is
  (B^E')^+(y_R - Pi_R B^A'x^A); the hedge vanishes when Sigma~_RU = 0.
- Part 3:
  - the joint policy's fund positions are the reduced problem's policy, obtained through the
    Schur complement of the joint D_t over the ETF block, which is the reduced D_t;
  - they partially adjust toward the reduced aim;
  - the fund Markowitz portfolio is (gamma Sigma^red_t)^{-1}(alpha_hat + B^A J_t' lambda_hat).
- Part 4:
  - J'v = v on L_E^perp, and the lambda-sensitivity along v is D_t^{-1}M_t B^A v with the stated
    recursion for M_t;
  - vanishing: with Pi_U B^A' = 0, B^A J' = 0, Sigma^red = Sigma_A + P^alpha, and zero
    sensitivity along every direction;
  - converse: the sensitivity is nonzero when M_t is nonsingular and B^A v != 0. M_{T-1} = I;
    M_t is nonsingular at every t when T <= 3; red's symmetric-part lemma holds; and the
    stationary M = (I - rho Lambda_A D^{-1})^{-1} exists, solves its equation and is
    nonsingular.
  - the risk term is positive semidefinite, and nonzero when some fund loading is unreachable;
    Sigma~_{U.R} is positive definite on L_E^perp;
  - K_t differs from the problem without the risk term at every review, through
    Loewner-monotonicity of the Riccati map.
- Part 5: along the Kalman path of P^lambda_t (identity observation, noise Sigma_f),
  Sigma~_{U.R,t} is nonincreasing and tends to the return-only Sigma_{f,U.R}, and J_t tends to the
  return-only hedge map, which fixes unreachable directions.

Paper-level, as for claim 030 (PM's rule-6b decision there):
- the Gaussian conditional moments behind the martingale hypothesis of claim 030's Bellman
  verification, on which the reduced problem's optimality rests;
- the passage to all measurable policies.

Not formalized:
- part 4's numerical observation that M_t is nonsingular at every t (Not shown in the claim);
- part 5's reading that lambda_hat_t has a nonvanishing limit in general, which is probabilistic;
- the one-sentence reading.

PM's limits stand.

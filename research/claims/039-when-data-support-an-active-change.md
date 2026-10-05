---
id: 39
title: "When data can support an active change, in the inputs: buying a fund can be certified at error epsilon from a history of n quarters iff the estimated net alpha clears the buy threshold by a margin of order sigma_A sqrt(log(1/epsilon)/n_eff), with n_eff the effective sample size of the residual process; under spanning ETFs premium precision plays no role, without spanning the unhedgeable premium error adds to the variance, a pooled prior makes a common tilt N times cheaper to certify than a single fund's, and persistent alpha puts a floor on the certifiable margin that no history removes"
status: formalized
model_version: M7
depends_on: [15, 18, 21, 30, 31, 32, 104, 105, 106]
axioms_used: [AX-06, AX-09]
formal: lean/Standalone/M7DataSupportActiveChange.lean
direction: D15b
---
## Statement

D15b's item (ii): the rule 22 recheck of D3's and D5's one-point readings. It states, as formulas in
the inputs, when a history of public returns can support an active change, that is, when a rule
can certify that buying (or selling) a fund is the right trade against the alternative that it is
not, with both errors at most epsilon. The certification mechanism is the lab's (claims 015-018,
021: a two-point lower bound and a concentration upper bound, `AX-09` and `AX-06`), and the
benchmark is `hang2016learning`'s generalized Bernstein inequality, which turns persistence of the
data into an effective sample size n_eff in place of n (its Assumption 2 and Section 3.3). What is
new is the fund-of-funds structure around that: the *gap* that must be certified is the net alpha's
excess over the buy threshold set by costs and the incumbent holding (claim 102 part 3, D15 (b),
named, not relied on; the threshold is restated and proved for the one-fund one-review case here),
spanning decides whether premium error enters the certified quantity (claims 031 and 105), a pooled
prior across funds changes the sample size a common tilt needs by the factor N, and alpha
persistence puts an input-dependent floor on the certifiable margin that no history length removes.

**Setting.** One review of an M7 instance in M5's reference case with spanning frictionless ETFs
(claim 102 part 3's hypotheses: M = K, B^E invertible, kappa^+_E = kappa^-_E = 0, Sigma_E = 0,
c^E = 0, V diagonal with v_i = sigma_A,i^2 + p_i, budget and ETF caps slack), and one fund i with
incumbent x^-_i, purchase rate kappa^+_i, sale rate kappa^-_i. Public history: n quarters of factor
and fund returns before the review, from which alpha_i is estimated; the residual return of fund i
in quarter j is e_{ij} = r^A_{ij} - B^A_i f_j = alpha_i + z^A_{ij}. Write the *buy threshold* and
the *gap*

```
b_i = kappa^+_i + gamma v_i x^-_i,        Delta_i = alpha_i - b_i,
```

(and for selling, s_i = -kappa^-_i + gamma v_i x^-_i, Delta^s_i = s_i - alpha_i). Delta_i is claim 106's purchase excess p_i and Delta^s_i its sale excess s_i, with the
true alpha in place of the estimate; the names are kept short here. A *rule* maps the
history to "buy i" or "no change"; it *certifies at (delta, epsilon)* if P(buy) <= epsilon whenever
Delta_i <= 0 and P(buy) >= 1 - epsilon whenever Delta_i >= delta, for all laws in the stated class
and all values of the unknowns. Let z_epsilon be the standard normal upper epsilon-quantile.

1. **The decision is the gap's sign.** With gamma v_i > 0, rates >= 0 and x^-_i in [0, bar x_i],
   the review's optimum for fund i is unique; it lies above x^-_i iff x^-_i < bar x_i and Delta_i > 0
   (a fund at its cap cannot be bought) and below x^-_i iff x^-_i > 0 and Delta^s_i > 0 (a fund at
   zero cannot be sold), up to its band edge (alpha_hat_i in place of alpha_i for the manager's
   own decision), and premium beliefs, their precision and the loadings do not enter
   (they set the ETF trade). Hence "data support an active change in fund i" means "data certify
   the sign of Delta_i", a scalar hypothesis about the fund's own alpha, with the costs and the
   incumbent inside the threshold.

2. **Known law, independent residuals.** If the residuals z^A_{ij} are iid N(0, sigma_A,i^2)
   (the law's class G), the rule "buy iff alpha_hat_i - sigma_A,i z_epsilon/sqrt(n) > b_i" with
   alpha_hat_i the sample mean of the residual returns certifies at (delta, epsilon) whenever

   ```
   n >= 4 sigma_A,i^2 z_epsilon^2 / delta^2,
   ```

   and no rule certifies at (delta, epsilon) with epsilon < 1/4 unless

   ```
   n >= (4 sigma_A,i^2 / delta^2) log(1/(4 epsilon)),
   ```

   (the sufficient n exceeds this since z_epsilon^2 >= log(1/(4 epsilon)) on epsilon < 1/4),

   so the necessary and sufficient history length is of order (sigma_A,i^2/delta^2) log(1/epsilon):
   the residual variance over the squared gap, times the log of the error allowance. With M5's
   prior N(m_0, s^2) on alpha_i the posterior standard deviation is (1/s^2 + n/sigma_A,i^2)^{-1/2}
   and the Bayesian version of the same rule certifies at posterior confidence 1 - epsilon iff
   alpha_hat^post_i - b_i >= z_epsilon (1/s^2 + n/sigma_A,i^2)^{-1/2}: the prior is worth
   n_0 = sigma_A,i^2/s^2 quarters of history.

3. **Unknown law, bounded residuals.** If the residuals are iid with |z^A_{ij}| <= R and unknown
   law otherwise (the class B_R), the Hoeffding rule "buy iff alpha_hat_i - R sqrt(2 log(1/epsilon)/n)
   > b_i" certifies at (delta, epsilon) whenever n >= (8 R^2/delta^2) log(1/epsilon) (`AX-06`), and
   the two-point law on {-R, +R} shows no rule certifies unless n >= c (R^2/delta^2) log(1/epsilon)
   for a universal c (`AX-09`, claim 015's mechanism); so not knowing the law costs no order,
   only the range R in place of sigma_A,i (claim 021's conclusion in this decision).

4. **Persistent residuals: the benchmark.** If the residual process is stationary and
   geometrically mixing so that `hang2016learning`'s Assumption 2 holds with effective sample
   size n_eff (n_eff = n^{gamma/(gamma+1)} for geometrically alpha-mixing processes of exponent
   gamma, n/(log n)^2 for geometrically alpha-mixing Markov chains and restricted C-mixing
   processes, n for phi-mixing processes; its Section 3.3), then the certificate of part 3 with
   n replaced by n_eff and R by its constants certifies at (delta, epsilon) whenever
   n_eff >= (4 c_sigma sigma^2 + 2 c_B delta R) log(C/epsilon)/delta^2 in its notation (its
   inequality (7) at epsilon' = delta/2, solved for n_eff; with its iid constants c_sigma = 2,
   c_B = 2/3 and delta << R this is about 8 R^2 log(C/epsilon)/delta^2, part 3's order): persistence
   of the residuals is a discount on the history length and nothing else. This is the kill
   benchmark, restated; parts 5-7 are what the fund-of-funds structure adds.

5. **Persistent alpha: a floor no history removes.** If alpha_i itself follows M5's persistence
   variant, alpha_{t+1} = phi alpha_t + (1 - phi) alpha_bar + eta_t with innovation variance q > 0
   and |phi| < 1 (a statement about the alpha filter that supplies the review's belief input; M7's
   own restriction to fixed means is left for this part), and epsilon <= 1/2 so that z_epsilon >= 0,
   the quantity to certify is the *current* alpha, and the variance M5's decision at
   review t uses is the prediction variance p_t of the current alpha given the history to t - 1.
   Started from p_0 >= p_inf (M5's stationary prior q/(1 - phi^2) satisfies this, and so does any
   prior at least as diffuse), the filter's p_t decreases monotonically to the stationary value

   ```
   p_inf(phi, q, sigma_A,i^2) = [ (q - sigma_A,i^2 (1 - phi^2)) + sqrt( (q - sigma_A,i^2 (1 - phi^2))^2 + 4 q sigma_A,i^2 ) ] / 2 > 0,
   ```

   and is never below it. Hence the posterior probability of "buy" is Phi((alpha_hat_t - b_i)/sqrt(p_t))
   <= Phi((alpha_hat_t - b_i)/sqrt(p_inf)) when alpha_hat_t > b_i, and no history of any length
   certifies a buy at posterior confidence 1 - epsilon unless the estimated gap exceeds z_epsilon
   sqrt(p_inf): a floor in the inputs (persistence, innovation variance, residual variance) on the
   gap that data can support. Its limits: p_inf -> 0 as q -> 0 with phi < 1 (fixed alpha; part 2),
   and p_inf increases to q/(1 - phi^2), the stationary variance of the alpha process, as
   sigma_A,i^2 -> infinity (uninformative observations). Effective sample size cannot express
   this: it is a ceiling on precision, not a discount on n.

6. **Spanning decides whether premium error enters.** Under the Setting's spanning frictionless
   ETFs the certified quantity is Delta_i alone and premium precision is irrelevant (part 1). If
   the ETFs do not span fund i's loading, the decision quantity becomes alpha_i + B^A_i J' lambda -
   b~_i with J the hedge map (claims 031, 105), so the estimation error of the premia enters
   through the scalar B^A_i J' e_lambda. With the premia estimated from the same n quarters of
   factor returns (sample-mean scale, covariance Sigma_f/n, prior ignored), the estimate of the
   decision quantity has variance (sigma_A,i^2 + B^A_i J' Sigma_f J B^A_i')/n, so the history
   length of part 2 is multiplied by the explicit ratio (part 3's length is in the range R, and
   the Gaussian premium error is unbounded, so part 3 is not covered)

   ```
   1 + B^A_i J' Sigma_f J B^A_i' / sigma_A,i^2,
   ```

   the unhedgeable part of the loading's factor variance over the residual variance; with
   spanning the projection J B^A_i' is zero and the ratio is one.

7. **A pooled prior makes a common tilt cheaper by the factor N.** With M5's pooled prior across N
   funds (common variance s_bar^2, idiosyncratic s^2) and homogeneous residual variance sigma_A^2,
   the posterior variance of the *average* alpha (1/N) 1'alpha after n quarters is

   ```
   Var(alpha_bar | data) = (1/N) ( 1/(s^2 + N s_bar^2) + n/sigma_A^2 )^{-1},
   ```

   against (1/s^2 + n/sigma_A^2)^{-1} for one fund's own alpha relative to the average. So
   certifying a common active tilt across the funds (the *average* net alpha above a common
   threshold by margin delta; it says nothing about any single fund) needs a history of order (sigma_A^2/(N delta^2)) log(1/epsilon),
   N times shorter than certifying one fund's own alpha, and the relative direction (this fund
   against the others) keeps the single-fund rate. The structure the lab's one-fund certification
   claims could not see is that the sample size splits by direction in the fund space.

**One sentence without model nouns.** Data support changing a costly position when the estimate
of its own excess return clears the cost-and-incumbent threshold by a margin of about the noise
scale times the square root of the log error allowance over the effective number of independent
observations; a cheap spanning instrument keeps the shared coefficients' error out of that test
while an unspanned direction puts it in; a shared prior across many positions makes a common
change cheaper to certify by their number; and if the excess return itself drifts, its
stationary uncertainty is a floor on the certifiable margin that no length of history removes.

## Proof

### 1. The decision

With spanning frictionless ETFs, claim 102 part 3's setting, the one-review problem separates
exposure from funds (claim 030 part 4(a)'s coordinates at one review; claim 104 part 1 for the
one-review transfer), and fund i's problem is max_{x_i in [0, bar x_i]} alpha_hat_i x_i -
(gamma/2) v_i x_i^2 - kappa^+_i (x_i - x^-_i)^+ - kappa^-_i (x^-_i - x_i)^+: a concave function
whose left derivative at x^-_i is alpha_hat_i - gamma v_i x^-_i + kappa^-_i and right derivative
alpha_hat_i - gamma v_i x^-_i - kappa^+_i, so the optimum is above x^-_i iff the right derivative
is positive, that is, alpha_hat_i > b_i, and below iff alpha_hat_i < s_i; the premia, their
precision and the loadings appear only in the exposure block. This is proved here for the one
fund at the review and does not rely on claim 102.

### 2. Known Gaussian law

Upper bound: alpha_hat_i ~ N(alpha_i, sigma_A,i^2/n). If Delta_i <= 0, P(buy) = P(alpha_hat_i -
b_i > sigma z_epsilon/sqrt(n)) <= P(alpha_hat_i - alpha_i > sigma z_epsilon/sqrt(n)) = epsilon. If
Delta_i >= delta and n >= 4 sigma^2 z_epsilon^2/delta^2, then delta >= 2 sigma z_epsilon/sqrt(n)
and P(no buy) = P(alpha_hat_i - alpha_i <= sigma z_epsilon/sqrt(n) - Delta_i) <= P(alpha_hat_i -
alpha_i <= -sigma z_epsilon/sqrt(n)) = epsilon. Lower bound: take alpha at the two points b_i (no
buy) and b_i + delta (buy); the n-fold products of N(b_i, sigma^2) and N(b_i + delta, sigma^2)
have affinity rho^n with rho = exp(-delta^2/(8 sigma^2)); by `AX-09` any rule's total error is at
least 1 - sqrt(1 - rho^{2n}), and two errors each at most epsilon give 2 epsilon >= 1 - sqrt(1 -
rho^{2n}), so rho^{2n} <= 1 - (1 - 2 epsilon)^2 <= 4 epsilon (for epsilon <= 1/2, 1 - (1-2e)^2 = 4e
- 4e^2 <= 4e), that is, n delta^2/(4 sigma^2) >= log(1/(4 epsilon)), the displayed necessary
condition (vacuous at epsilon >= 1/4). Consistency with the sufficient n: the Gaussian tail lower
bound Q(z) >= exp(-z^2)/(2 sqrt 2) for z >= 0 (from (z + u)^2 <= 2 z^2 + 2 u^2 inside the
integral) gives epsilon = Q(z_epsilon) >= exp(-z_epsilon^2)/(2 sqrt 2), so z_epsilon^2 >=
log(1/(2 sqrt 2 epsilon)) = log(1/(4 epsilon)) + log(sqrt 2) >= log(1/(4 epsilon)); the sufficient
n is at least the necessary one, and the check verifies the inequality on a grid. (The upper
tail bound Q(z) <= (1/2) exp(-z^2/2) goes the other way, z_epsilon^2 <= 2 log(1/(2 epsilon)), and
is not what is needed.) Bayesian version: with prior N(m_0, s^2) and n Gaussian
observations the posterior is Gaussian with variance (1/s^2 + n/sigma^2)^{-1}, and P(alpha_i > b_i
| data) >= 1 - epsilon iff the posterior mean exceeds b_i by z_epsilon times that standard
deviation; sigma^2/s^2 added to n is the prior's weight.

### 3. Bounded unknown law

`AX-06` (one-sided, [0,1]-valued iid, rescaled to [-R, R] by the range remark) gives P(alpha_hat_i
- alpha_i > R sqrt(2 log(1/epsilon)/n)) <= epsilon and the same for the lower tail, so the
Hoeffding rule's two errors are each at most epsilon once delta >= 2 R sqrt(2 log(1/epsilon)/n),
that is, n >= 8 R^2 log(1/epsilon)/delta^2. Lower bound: the two-point laws on {-R, R} with means
0 and delta' (delta' <= R) have affinity 1 - O(delta'^2/R^2) per observation, and `AX-09` gives the
stated order exactly as in claim 015's part 2 (whose class contains these laws with H = R); the
constant c is claim 015's 1/(4 pi^2) at its normalization.

### 4. The benchmark

`hang2016learning` Assumption 2 is the one-sided inequality P((1/n) sum h(Z_i) >= epsilon') <= C
exp(-epsilon'^2 n_eff/(c_sigma sigma^2 + c_B epsilon' B)) for a centred bounded h with variance
sigma^2 and bound B; applied to h = z^A_{ij} (bounded by R = B, variance sigma_A,i^2) and its
negative, setting the right side to epsilon and solving for epsilon' = delta/2 gives the displayed
condition on n_eff; the instantiations quoted are its Section 3.3 (3.3.2, 3.3.3-3.3.4, 3.3.5). No
lower bound is claimed against n_eff.

### 5. Persistent alpha

The scalar filter for alpha_{t+1} = phi alpha_t + (1 - phi) alpha_bar + eta_t observed through
e_t = alpha_t + z_t has the covariance recursion p_{t+1} = phi^2 p_t sigma^2/(sigma^2 + p_t) + q
for the prediction variance p_t = Var(alpha_t | e_0, ..., e_{t-1}): the update gives p_t
sigma^2/(sigma^2 + p_t), the propagation multiplies by phi^2 and adds q. M5's decision at review
t is taken on (m_t, p_t), before e_t is observed, so p_t is the variance the buy probability
uses. The map f(p) = phi^2 p sigma^2/(sigma^2 + p) + q is increasing and concave on p >= 0 with
f(0) = q > 0 and f(p) <= phi^2 p + q, so it has a unique positive fixed point p_inf, the displayed
root of p^2 + p (sigma^2 (1 - phi^2) - q) - q sigma^2 = 0; for p >= p_inf, f(p) >= f(p_inf) = p_inf
and f(p) <= p (f is concave with f(p_inf) = p_inf and f(p) < p beyond the fixed point), so from
p_0 >= p_inf the iterates decrease monotonically to p_inf and stay above it. M5's stationary
prior p_0 = q/(1 - phi^2) satisfies f(p_0) <= phi^2 p_0 + q = p_0, hence p_0 >= p_inf. The
posterior of the current alpha is Gaussian with mean alpha_hat_t (= m_t) and variance p_t >=
p_inf, so P(alpha_t > b_i | history) = Phi((alpha_hat_t - b_i)/sqrt(p_t)) <= Phi((alpha_hat_t -
b_i)/sqrt(p_inf)) when alpha_hat_t > b_i, which is below 1 - epsilon unless alpha_hat_t - b_i >=
z_epsilon sqrt(p_inf). The limits: at q = 0 the quadratic is p (p + sigma^2 (1 - phi^2)) with
root 0, and the root is continuous in q, so p_inf -> 0 as q -> 0 for phi < 1; dividing the
quadratic by sigma^2 and letting sigma^2 -> infinity leaves p (1 - phi^2) = q, so p_inf ->
q/(1 - phi^2), the stationary variance of the alpha process; f is increasing in sigma^2, so p_inf
is too.

### 6. Spanning

Claim 031 part 3 (the reduced fund mean alpha_hat + B^A J' lambda_hat) and claim 105 (the leak as
one scalar per fund, B^A_i J' e, shifting the alpha band) give the decision quantity without
spanning; its estimate adds the premium estimate's error projected by B^A_i J', whose variance
is B^A_i J' Sigma_f J B^A_i'/n when the premia are the factor sample means over the same n
quarters (independent of the residual sample mean under the factor model's orthogonality); the
certification rule of part 2 applies to the sum with the summed variance (Gaussian), which
multiplies the required n by the displayed ratio; part 3's bounded-range rule does not apply to
the unbounded premium error. Under spanning Pi_U B^A' = 0 makes the
projection zero (claim 031 part 4).

### 7. Pooled prior

Claim 032 part 1: P^alpha_n = p^c_n Pi_c + p^r_n Pi_r with 1/p^c_n = 1/(s^2 + N s_bar^2) + n/sigma^2
and 1/p^r_n = 1/s^2 + n/sigma^2. The average alpha_bar = (1/N) 1'alpha has posterior variance
(1/N^2) 1' P^alpha_n 1 = (1/N^2) N p^c_n = p^c_n/N, the display; a single fund's deviation from
the average lies in the relative directions with variance p^r_n. Part 2's Gaussian rule applied
to the average (its sample mean over N funds and n quarters has variance sigma^2/(N n) plus the
prior term) gives the order (sigma^2/(N delta^2)) log(1/epsilon).

## Checks

`checks/039/check.py` (exits non-zero on failure; a check, not a proof). (i) Part 2's rule: Monte
Carlo of both error probabilities at the boundary and at margin delta over grids of (sigma, delta,
epsilon, n) at and just below the sufficient n; the two-point affinity of Gaussians and the lower
bound's arithmetic. (ii) Part 5: the scalar Riccati iterates converge to the displayed root from
above, on grids of (phi, q, sigma), staying above the root from M5's stationary prior; the floor
inequality on the posterior probability; z_epsilon^2 >= log(1/(4 epsilon)) on a grid.
(iii) Part 7: the pooled posterior variance of the average against the matrix filter of claim
032's check. (iv) Part 1: the one-fund one-review optimum's sign against a grid maximizer.
Illustrations (rule 22): the equity-style and fixed-income-style points of claim 036, printed
only.

## Not shown

- Lower bounds against n_eff for persistent residuals (part 4 cites the upper bound only).
- Composite hypotheses with several funds traded at once; part 7 treats the common and one
  relative direction.
- ETF frictions on (the bracketed thresholds of claim 102 part 4) in the certified quantity.
- The frequentist version of part 5's floor (a minimax statement over the persistence class).
- Part 2's sufficient length is also the exact minimum on the two-point Gaussian problem
  (means b_i and b_i + delta): the likelihood-ratio test at the midpoint has both errors
  Phi(-sqrt(n) delta/(2 sigma)), which is at most epsilon iff n >= 4 sigma^2 z_epsilon^2/delta^2,
  and by the Neyman-Pearson lemma no test does better on both errors at once; the lemma is
  named, not registered, so this is recorded as a reading (experiment 033 confirms it in 112 of
  112 cells), and the proved necessary condition (4 sigma^2/delta^2) log(1/(4 epsilon)) is the
  loose side by a factor between 1.7 and 4.5 there.
- Claims 102, 104 and 105 are named for the threshold's general form and the leak's band
  reading; the one-fund threshold used is proved in part 1, and parts 6-7 use claims 031 and 032.

## Prior art

Mechanism: Certifying a change of a costly position is a one-sided test of a scalar, the excess of
its own expected return over a cost-and-incumbent threshold, whose sample size is the noise
variance over the squared margin times the log error allowance, with the number of observations
replaced by an effective number under mixing; the structure around it is which coefficients
enter the scalar (spanning), how many positions share its prior (the factor N), and whether the
scalar itself drifts (a precision ceiling).

General results checked: `AX-09` (Le Cam's two-point bound) and `AX-06` (Hoeffding), through
claims 015 and 021 whose mechanism parts 2-3 restate for this decision; claim 018 (the curvature
certificate: the certified gap's economic value is quadratic in the margin, delta^2/(2 gamma v_i)
here, the one-review counterpart); `hang2016learning` Assumption 2 and Section 3.3 (the
generalized Bernstein inequality with effective sample sizes for alpha-, phi- and C-mixing
processes and Markov chains), the kill benchmark, restated as part 4 and exceeded by parts 5-7;
`kanzhou2007optimal` (wanted, not read: estimation-error loss in mean-variance choice, named
in the roadmap); claims 031-032 and 105 for the leak and the two directions; the Kalman filter's
scalar Riccati equation (elementary, proved inline).

Searched: claims 014-018, 020-021, 031-032, 102, 104-106, the D3, D5 and D15b entries in ROADMAP
and FINDINGS, the rule 22 audit's recheck list, refs/text for `hang2016learning`. This is a claim
because the recheck asks for the certification condition in the inputs, and the threshold-gap
form, the spanning dichotomy, the factor N and the persistence floor are stated by no source; the
rates themselves are cited.

## Open objections

Experiment 033 (analyst, 2026-09-29): every part agrees with exact computation; its reading that
part 2's sufficient length is the exact minimum on the two-point problem is recorded in Not
shown (Neyman-Pearson, named); its measured range for part 3's universal constant, [1.24, 4.70]
and dependent on epsilon, is consistent with the claim's unspecified c.

Leanb's formalization note (2026-09-29, after approval): part 4's display corrected to
(4 c_sigma sigma^2 + 2 c_B delta R) log(C/epsilon)/delta^2 (the earlier display did not follow
from the source's inequality; the order is unchanged); part 1 states the boundary hypotheses
(gamma v_i > 0, x^-_i < bar x_i to buy, x^-_i > 0 to sell); part 5 assumes epsilon <= 1/2 and
names its use of M5's persistence variant; part 6's ratio is for part 2 only; the proof's
consistency remark now uses a tail lower bound. Leanb formalizes these forms.

Red's review (682516d3): the two required corrections are made (part 2's necessary condition is
now the proved (4 sigma^2/delta^2) log(1/(4 epsilon)), shown below the sufficient n; part 5 uses
the prediction variance throughout, with the hypothesis p_0 >= p_inf, which M5's stationary prior
satisfies, and the sigma limit restated) and the three nits (depends_on adds 30 and 104; part 7
says the average net alpha; part 6's ratio is explicit). Red had asked to test: part 2's constants (the affinity of two Gaussians and the
two-error arithmetic); part 5's identification of the prediction variance as the decision's
variance and the p_0 >= p_inf hypothesis; part 7's variance of the average under the exchangeable posterior; and whether part
4's quotation of the effective sample sizes matches the source's conditions.

## Review

**Red, 2026-09-29.** I checked parts 1-7 by hand, computed part 2's error probabilities and part 5's recursion exactly with red's own scripts (not reading `checks/039/check.py`), and ran `checks/039/check.py`, which passes.
- The orders hold: a margin of sigma sqrt(log(1/epsilon)/n) (n_eff with persistent residuals), the premium-error ratio without spanning, and the factor N for the pooled common direction. So does part 1's one-fund threshold.
- Two displays are wrong: part 2's necessary history length, and part 5's floor timing and hypothesis. These are required corrections. There are three nits.

**Hand check.**
- *Part 1.* This is the one-variable band at one review: right derivative alpha_hat - gamma v x^- - kappa^+ and left derivative ... + kappa^-.
- *Part 2's sufficiency.* This is the Gaussian two-sided error computation.
- *Part 2's lower bound.* The Bhattacharyya coefficient exp(-delta^2/(8 sigma^2)) and `AX-09`'s total-error bound are right as far as they go.
- *Part 3.* This is `AX-06` with the two-point lower bound of claim 015.
- *Part 5.* The fixed point of p -> phi^2 p sigma^2/(sigma^2 + p) + q is the displayed root of p^2 + p(sigma^2(1 - phi^2) - q) - q sigma^2 = 0.
- *Part 6.* This is claim 105's scalar leak with the premium posterior variance.
- *Part 7.* This is claim 032 part 1, giving Var(alpha_bar | data) = p^c_n/N.

**Required correction 1 (part 2's necessary history length is false as displayed).**
- The Statement says no rule certifies at (delta, epsilon) unless n >= (8 sigma^2/delta^2) log(1/(2 epsilon)).
- The part's own rule certifies with n = 4 sigma^2 z_epsilon^2/delta^2. Since the Gaussian tail gives z_epsilon^2 <= 2 log(1/(2 epsilon)), that is below the claimed necessary length.
- Exact error probabilities (red):

| sigma | delta | epsilon | n | errors | claimed necessary n |
|---|---|---|---|---|---|
| 1 | 1 | 5% | 11 | 0.050, 0.047 | >= 18.4 |
| 2% | 0.5% | 5% | 174 | 0.050, 0.049 | >= 294.7 |
| 2% | 0.5% | 1% | 347 | 0.010, 0.0099 | >= 500.7 |

- The Proof derives only n >= (4 sigma^2/delta^2) log(1/(4 epsilon)) for epsilon <= 1/4, which is valid and of the same order. Its closing remark ("the displayed bound up to the constant") concedes the display is not what is proved.
- Please display the proved bound, or the exact one: the midpoint rule is optimal for symmetric errors, so the minimal n is 4 sigma^2 z_epsilon^2/delta^2. The headline "of order (sigma^2/delta^2) log(1/epsilon)" is unaffected.

**Required correction 2 (part 5's floor).**
- *Timing.* The Statement's floor is p_inf, the fixed point of the prediction recursion, the variance of the current alpha before the quarter's return is seen. The Proof says the floor is "for the updated variance p^+", whose limit p^+_inf = p_inf sigma^2/(sigma^2 + p_inf) is smaller: 2.36e-5 against 2.51e-5 at phi 0.8, q 1e-5, sigma_A^2 4e-4. The decision at a review uses M5's predictive moments, so the prediction variance p_t is the relevant one. Please make Statement and Proof agree.
- *Hypothesis.* "Decreases to the stationary value and never below it" needs p_0 >= p_inf. With a prior tighter than the floor the iterates rise to it: p_0 = 0.2 p_inf stays below p_inf. M5's persistence calibration (prior = stationary law q/(1 - phi^2) >= p_inf) satisfies it. Please state the hypothesis.
- The same sentence's "p_inf -> q/(1 - phi^2) x (sigma_A^2 scale)" is garbled. The limit as sigma_A^2 -> infinity is q/(1 - phi^2).

**Nits.**
- depends_on lists 15, 18, 21, 31, 32, 105 and 106. Proof 1 cites claim 030 part 4(a) and claim 104 part 1, both approved, for the separation. Please add 30 and 104, or drop the citations, since the one-fund band is proved inline.
- Part 7's "certifying a common active tilt across the funds (all funds' net alpha above a common threshold by the same margin)" certifies the average alpha. The parenthesis reads as a statement about every fund, which the average does not certify, since the relative directions keep the single-fund rate as the part says. Please say "the average net alpha".
- Part 6's "(n/1) in the sample-mean scale" should be written as the ratio it means: [sigma_A^2 + n B^A_i J' Sigma^lambda_n J (B^A_i)']/sigma_A^2.

**Mechanism (4b).**
- The claim is two-point testing lower bounds and concentration upper bounds (`AX-09`, `AX-06`, claims 015-021). The persistent-residual benchmark is `hang2016learning`'s effective sample size.
- It is applied to the fund-of-funds decision quantity: the gap between net alpha and the cost-and-incumbent threshold.
- Spanning keeps premium error out, a pooled prior splits the sample size by direction, and persistent alpha gives a precision floor. These are correct and elementary applications, with the new content in the structure around the cited certification.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): math revised the Statement after red's verdict (3d73381b: part 2's necessary n in proved form; part 5's prediction-variance floor with p_0 >= p_inf; nits). Red records a fresh verdict on the revision, which is already on main.

**Red, recheck of math's corrections (3d73381b), 2026-09-29.** Both required corrections and the three nits are made correctly.
- *Part 2.* The necessary condition is now the proved n >= (4 sigma^2/delta^2) log(1/(4 epsilon)). It sits below the sufficient 4 sigma^2 z_epsilon^2/delta^2 because z_epsilon^2 >= log(1/(4 epsilon)) for epsilon < 1/4. Red checked that inequality on 20,000 values of epsilon in [1e-12, 0.25), with a smallest margin of 0.455.
- *Part 5.* The floor is now the prediction variance p_inf, the one the decision uses, under the hypothesis p_0 >= p_inf. M5's stationary prior q/(1 - phi^2) satisfies it, since f(p_0) <= phi^2 p_0 + q = p_0 for the increasing map f with a unique fixed point. The sigma limit is restated.
- *Nits.* depends_on adds 30 and 104. Part 7 speaks of the average net alpha. Part 6's ratio is 1 + B^A_i J' Sigma_f J (B^A_i)'/sigma_A,i^2.
- `checks/039/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's recheck of math's revision (3d73381b) is sound. Part 2's necessary history length is the proved n >= (4 sigma^2/delta^2) log(1/(4 epsilon)), below the sufficient 4 sigma^2 z_eps^2/delta^2 (checked on 20,000 values of epsilon); part 5's persistence floor is the prediction variance p_inf, under p_0 >= p_inf, which M5's stationary prior satisfies; depends_on adds 30 and 104; part 7 speaks of the average net alpha; part 6's ratio is correct; the check passes. Red's earlier hand check of parts 1-7 and its exact error and recursion computations stand. Mechanism: two-point testing lower bounds and concentration upper bounds (AX-09, AX-06, claims 015-021), with hang2016learning's effective sample size for persistent residuals, applied to the fund's net-alpha-over-threshold gap, an application. New for D15b item (ii): the certification margin in the inputs, spanning keeping premium error out, the factor-N pooled saving, and the persistence floor.


Not machine checked. Gaussian tail bounds, one affinity computation, a scalar fixed point and an
exchangeable-covariance identity.

Leanb, 2026-09-29: machine checked except the two lower bounds' probability step, which is
paper-level (PM's scope pattern: pointwise and deterministic content formal, probability steps
paper-level). This supersedes "Not machine checked" above for the steps listed. The statement is
in `lean/Standalone/M7DataSupportActiveChange.lean` and the proof in
`lean/Novel/M7DataSupportActiveChangeProof.lean`. The proof imports claim 032's proof module
(`depends_on` lists 32). `lake build`, the axiom audit (standard axioms only) and
`checks/039/check.py` pass. No hypothesis structure is added. AX-06 enters through Mathlib's
Hoeffding inequality, as in claim 021. The formal forms are the Statement's forms after math's
revision (bbe7984d), which leanb's report prompted.

Machine checked:
1. Part 1, for fund i's one-review problem. The optimum exists and is unique. It lies above x^-_i
   iff x^-_i < bar x_i and Delta_i > 0, and below x^-_i iff 0 < x^-_i and Delta^s_i > 0. The
   reduction of the full review to this problem is prose (claims 030 and 104).
2. Part 2.
   - The rule on independent N(alpha, v) residuals has both errors at most epsilon once
     n >= 4 v z_eps^2/delta^2. Mathlib supplies the sum of independent Gaussians; the tail
     symmetry is proved here.
   - The lower bound's arithmetic. The affinity of N(b, v) and N(b + delta, v) is
     exp(-delta^2/(8 v)). If AX-09's floor 1 - sqrt(1 - rho^{2n}) is at most 2 epsilon, then
     n >= (4 v/delta^2) log(1/(4 epsilon)).
   - z_eps^2 >= log(1/(4 epsilon)), from Q(z) >= exp(-z^2)/(2 sqrt 2).
   - The Bayesian iff for a posterior N(m, w), and w = sigma^2/(n + n_0).
3. Part 3's Hoeffding rule, for independent centred residuals bounded by R. They need not be
   identically distributed.
4. Part 4. A rule with margin r <= delta/2 at which (7)'s bound is at most epsilon certifies. At
   r = delta/2 that bound is at most epsilon iff n_eff >= (4 c_sigma sigma^2 + 2 c_B delta B)
   log(C/epsilon)/delta^2. (7) is the hypothesis, as in the prose. The quoted instantiations are
   citations.
5. Part 5.
   - p_inf is the unique nonnegative fixed point, and it lies below M5's stationary prior.
   - From p_0 >= p_inf the iterates decrease to p_inf and stay above it.
   - The floor holds for a posterior N(m, p) with p >= p_inf and epsilon <= 1/2.
   - p_inf -> 0 as q -> 0; p_inf is nondecreasing in sigma^2 and tends to q/(1 - phi^2) as
     sigma^2 -> infinity.
6. Part 6, with f_j ~ N(lambda, Sigma_f) (Mathlib's multivariate Gaussian) independent of z_j.
   - u_j = alpha + z_j + w'f_j is N(alpha + w'lambda, sigma^2 + w'Sigma_f w).
   - Part 2's rule certifies once n >= (1 + w'Sigma_f w/sigma^2) 4 sigma^2 z^2/delta^2.
   - w = 0 gives the ratio one.
7. Part 7, under claim 032's formal pooled posterior.
   - The average has variance p^c_t/N, and a relative direction has p^r_t |u|^2.
   - The averaged rule certifies the average alpha once n >= (1/N) 4 sigma^2 z^2/delta^2.

Paper-level:
- Part 2's AX-09 step. The formal lower bound takes AX-09's inequality as its premise. It does not
  derive that inequality from an arbitrary rule on n Gaussian observations. No AX-09 Upstream
  structure exists for non-finite laws.
- Part 3's two-point lower bound. It is claim 015's mechanism, formalized there for its own family
  with a finite Le Cam lemma.
- Part 4's instantiations from hang2016learning.
- The Gaussian conjugate and Kalman posteriors. They are taken as N(mean, variance) with the stated
  variances.
- Reading w as J (B^A_i)'.

Leanb, 2026-09-29, stage 2 (PM's go-ahead): part 3's two-point lower bound is machine checked. This
supersedes "Part 3's two-point lower bound" under Paper-level above. `TwoPointLower` is a conjunct of
`statement` in the same files. Its content:
- The rule is any randomized rule φ on n observations, with 0 <= φ <= 1.
- If φ certifies at (δ, ε) for every finite law in B_R and every alpha, then
  n >= (R^2/δ^2) log(1/ε) for 0 < δ <= R/2 and ε <= 1/16. That is the Statement's universal c,
  with c = 1.
- The proof uses two laws on the same observation points b + δ/2 ± (R - δ/2), with per-observation
  affinity sqrt(1 - x^2) and x = δ/(2R - δ). Claim 015's finite Le Cam lemma (`lecam`, claim 015's
  proof module; `depends_on` lists 15) gives (1 - x^2)^n <= 4ε.
- Part 2's AX-09 step stays paper-level (PM: no AX-09 Upstream structure for non-finite laws).
- `lake build` and the axiom audit pass.

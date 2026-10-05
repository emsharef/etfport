---
id: 42
title: "The fund's fine-regime band with one costly ETF, in the inputs: the two-instrument tracking loss is the fund's residual loss plus the ETF's tracking-error loss, the ETF's cost reaching the fund only through that error; with uncorrelated risks the fund's band is its own one-instrument band whatever the targets' innovation correlation or the ETF's rate; with a frictionless ETF it is the one-instrument band with the residual curvature and the fund's own innovation variance, with a frozen ETF the one with the full curvature and the idle-target variance, each with the cited cube-root law Delta^3 = 3 (kappa^+ + kappa^-) v/(4c) of the first corrector solution, centred on the target whatever the rate asymmetry; between, the leading order depends on one dimensionless ratio of the ETF's band scale to the fund's, set by the rate ratio and the correlations, and, as a reading, not on the ETF's idle probability"
status: formalized
model_version: M7
depends_on: [29, 107]
axioms_used: [AX-15]
formal: lean/Standalone/M7FineBandOneCostlyEtf.lean
direction: D15e
---
## Statement

D15e's first claim. Mathb's conjecture (FINDINGS, experiments 036 and 038-039) says the fund's
band with one costly ETF is claim 029's one-instrument band with the residual curvature and a
mixture of two target-innovation variances, the idle-ETF one v^idle and the fund's own v_A,
weighted by the future ETF-idle probability. This claim gives the exact structure behind the
two variances (parts 1-2), proves the cube-root law with its corrected constant at the level of
the continuous-time ergodic problem the fine regime is read against (part 3), and shows that the
weight between the two ends is set by the ratio of the ETF's band scale to the fund's, a
function of the rate ratio and the correlations, not by the idle probability, which tends to one
in the fine regime at every rate ratio (part 4). The intermediate leading order is the solution
of a two-dimensional ergodic problem (the kill benchmark, `possamai2015homogenization`, named);
its closed form or bounds are the second claim's target.

**Setting.** A slack-budget M7 instance (finite-law variant, claim 107's setting) with one fund
(holding a, rates kappa^+_A, kappa^-_A) and one ETF (holding b, rates kappa^+_E, kappa^-_E),
risk covariance Sigma = [[Sigma_AA, Sigma_AE], [Sigma_AE, Sigma_EE]] positive definite with risk
correlation rc = Sigma_AE / sqrt(Sigma_AA Sigma_EE), gamma > 0, discount beta, frictionless
targets (a*_t, b*_t) whose innovations have variances v_A, v_B and correlation r per review,
caps slack. Write y_a = a - a*, y_b = b - b*, the *hedge ratio* rho_h = Sigma_AE / Sigma_EE (claim
107's rho), the *residual curvature* c^res = gamma (Sigma_AA - Sigma_AE^2 / Sigma_EE) = gamma
Sigma_AA (1 - rc^2) (claim 107's c^res), the *reverse ratio* rho' = Sigma_AE / Sigma_AA (mathb's rho),
and the two variances

```
v^idle = v_A + rho'^2 v_B + 2 rho' r sqrt(v_A v_B)      (the innovation variance of a* + rho' b*, the fund's effective target when the ETF is frozen),
v_B^eff = v_B + rho_h^2 v_A + 2 rho_h r sqrt(v_A v_B)   (the innovation variance of b* + rho_h a*, the ETF's effective target when it hedges the fund).
```

A *fine regime* is one in which the target's per-review step is small against the instrument's
static band, sqrt(v) << (kappa^+ + kappa^-)/c; the fine-regime leading order of a band is read,
as in claim 029's prior art, against the continuous-time ergodic problem with the same
curvature, rates and innovation variance per unit time (the identification is cited there and
not proved here; Not shown).

1. **The error coordinate (exact, any regime).** With e = y_b + rho_h y_a, the ETF's tracking error
   relative to the position that hedges the fund,

   ```
   (gamma/2) (y_a, y_b) Sigma (y_a, y_b)' = (c^res/2) y_a^2 + (gamma Sigma_EE/2) e^2,
   ```

   so the two-instrument tracking loss is the fund's residual loss plus the ETF's error loss. A
   fund trade da moves (y_a, e) by (da, rho_h da); an ETF trade db moves e alone; the innovations
   of (y_a, e) have variances (v_A, v_B^eff) and covariance r sqrt(v_A v_B) + rho_h v_A. The ETF's
   cost reaches the fund only through e: through the value of the error the fund's own trade
   creates and the ETF may or may not remove.

2. **Three exact reductions.** (a) *Uncorrelated risks.* If Sigma_AE = 0, the two-instrument
   problem is the sum of two one-instrument problems, whatever r and the ETF's rate: the fund's
   band at every review is its own one-instrument dynamic band (claims 029, 100) with curvature
   gamma Sigma_AA and innovation variance v_A; the targets' innovation correlation does not
   enter. (b) *Frictionless ETF.* If kappa^+_E = kappa^-_E = 0, the fund's problem is the
   one-instrument problem with curvature c^res, target a* and innovation variance v_A (claim 107
   part 3). (c) *Frozen ETF.* If the ETF never trades (its rates prohibitive in both directions, or its
   box pinned at its incumbent; a cap alone stops purchases only, lean's point), the fund's problem is the one-instrument problem with curvature gamma Sigma_AA,
   target a* + rho' (b* - b) and innovation variance v^idle.

3. **The one-instrument fine-regime law, at the ergodic level (AX-15, cited).** For the ergodic
   (first-corrector) problem of tracking a Brownian target of variance v per unit time with
   holding cost (c/2) y^2 and proportional rates kappa^+ (up) and kappa^-, the corrector's
   no-trade band is [-Delta, Delta], centred on the target whatever the split of the round-trip
   rate between the two sides, with

   ```
   Delta^3 = 3 (kappa^+ + kappa^-) v / (4 c),    average cost lambda = c Delta^2 / 2,    gradient constraint -kappa^+ <= w' <= kappa^-
   ```

   (`soner2013homogenization` (4.3)-(4.5), `muhlekarbe2017primer` (4.10)-(4.13), through AX-15;
   claim 101's refutation's constant, 4c in place of 8c, is the sources'). Its hypotheses hold
   for each of part 2's reductions: the tracking loss is exactly quadratic in the gap with a
   constant curvature, the target's innovations have a constant variance per review, and the
   rates are constant. Applied to part 2: the fund's fine-regime half-width is

   ```
   (a)  Delta_0^3 = 3 (kappa^+_A + kappa^-_A) v_A / (4 gamma Sigma_AA)         (uncorrelated risks, any r, any ETF rate),
   (b)  Delta_free^3 = 3 (kappa^+_A + kappa^-_A) v_A / (4 c^res)              (frictionless ETF),
   (c)  Delta_frozen^3 = 3 (kappa^+_A + kappa^-_A) v^idle / (4 gamma Sigma_AA)  (frozen ETF),
   ```

   with Delta_frozen^3 / Delta_free^3 = (1 - rc^2) v^idle / v_A, which can lie on either side of one.

4. **What sets the weight between the ends (exact), and the readings.** In part 1's coordinates the fine-regime problem
   with both instruments costly is a two-dimensional ergodic problem with diagonal holding cost
   (c^res, gamma Sigma_EE), an oblique fund control along (1, rho_h) at rate kappa_A, an ETF control
   along e at rate kappa_E, and innovation covariance from part 1. Its solution is a region of
   size kappa^{1/3}; scaled by the free half-width Delta_free and the ETF's own fine-regime scale
   Delta_E^3 = 3 (kappa^+_E + kappa^-_E) v_B^eff / (4 gamma Sigma_EE), the problem depends only on

   ```
   xi^3 = Delta_E^3 / Delta_free^3 = [ (kappa^+_E + kappa^-_E) / (kappa^+_A + kappa^-_A) ] [ v_B^eff / v_A ] [ c^res / (gamma Sigma_EE) ],
   ```

   the risk correlation rc, the innovation correlation r, v_B / v_A and Sigma_EE / Sigma_AA, and
   on the cost asymmetries: the fund's leading-order half-width is Delta_free F(xi, ...), with F
   the fund's band at the ETF holding b = b* (the no-trade region's cross-section along the
   line e = rho_h y_a in part 1's coordinates, claims 107-108's sense of the fund's band; not the
   cross-section along e = 0, whose frozen end would be Delta_frozen/(1 - rc^2), the analyst's
   experiment 043 point) (exact, by dimensional analysis), and F = 1 at
   rc = 0 exactly (part 2(a)); for one instrument the fraction of time spent pushing is zero at
   the ergodic level, so an instrument's idle fraction tends to one as its steps shrink (exact,
   part 3's reflected process). *Readings, conditional on what is not proved* (the continuity of
   the ergodic problem's cross-section at the ends of xi, and the two-dimensional policy's
   pushing set having measure zero): F -> 1 as xi -> 0 (the ETF's band negligible on the fund's
   scale, the ETF pinning e: part 2(b)'s reduction) and F -> Delta_frozen / Delta_free as xi ->
   infinity (the ETF's band wide on the fund's scale, e free: part 2(c)'s reduction), so that the
   ETF's idle probability, which would then tend to one at every xi while the ends of F differ,
   would not be the weight; the weight would be xi, the ETF's rate relative to the fund's through
   the cube root, times the variance and curvature ratios. F between the ends is the second
   claim's object. At basis-point ETF rates and
   quarterly target moves of percent, the ETF is not in its fine regime at all (its static band
   (kappa^+_E + kappa^-_E)/(gamma Sigma_EE) is below its target step), so the relevant asymptotic
   pairing for the paper is a fine fund with a coarse ETF, in which the ETF re-hedges every
   review to within its static half-width and the fund's leading order is (b), the residual law,
   perturbed by an error e bounded by the ETF's static half-width (a reading; Not shown).

**One sentence without model nouns.** The position's loss with a cheap hedging instrument
splits into its own residual loss and the hedge's tracking error, which is the only channel
through which the hedge's cost reaches it; with uncorrelated risks the two decouple whatever the
targets' co-movement; with a free hedge the position sees its residual curvature and its own
innovation, with a frozen hedge its full curvature and the co-moving target; the fine-regime
band is the cube root of three quarters of the round-trip rate times the innovation variance
over the curvature at either end; and between the ends the weight is the ratio of the hedge's
band scale to the position's, set by the rate ratio and the correlations, not by how often the
hedge is idle, which in the fine regime is almost always.

## Proof

### 1. The error coordinate

Expand (gamma/2)[Sigma_AA y_a^2 + 2 Sigma_AE y_a y_b + Sigma_EE y_b^2] with y_b = e - rho_h y_a:
Sigma_AA y_a^2 + 2 Sigma_AE y_a (e - rho_h y_a) + Sigma_EE (e - rho_h y_a)^2 = (Sigma_AA - 2 rho_h
Sigma_AE + rho_h^2 Sigma_EE) y_a^2 + 2 (Sigma_AE - rho_h Sigma_EE) y_a e + Sigma_EE e^2, and with rho_h =
Sigma_AE/Sigma_EE the cross coefficient vanishes and the y_a^2 coefficient is Sigma_AA - Sigma_AE^2/Sigma_EE.
The control and innovation statements are the definitions of e and of rho_h.

### 2. Reductions

(a) With Sigma_AE = 0 the stage loss, the cost and the box are sums of a fund term and an ETF
term, each depending on its own holding, and the policies are functions of the common public
state; the objective is therefore the sum of two one-instrument objectives with no coupling
through the controls, so its supremum is attained by optimizing each separately (the pair of
one-instrument optimal policies is admissible and no admissible pair does better on either
term). The fund's term is claim 029's one-instrument problem with curvature gamma Sigma_AA and
target a*, whose innovations have variance v_A; r enters only the joint law of the two targets,
which the fund's term does not see. (b) Claim 107 part 3, formalized: with frictionless ETFs the
fund's band at every review is the one-instrument dynamic band with curvature c^res_t and the
fund's reduced target, here a* (the ETF re-hedges the fund's risk exactly, so the fund's
marginal is c^res (a - a*)). (c) With b fixed, the stage loss is (gamma Sigma_AA/2)(y_a + rho' y_b)^2
+ (gamma/2)(Sigma_EE - Sigma_AE^2/Sigma_AA) y_b^2 (expand as in part 1 with the roles exchanged),
the second term free of a; so the fund's problem is one-instrument with curvature gamma Sigma_AA
and target a* - rho' y_b = a* + rho' (b* - b), whose innovation is da* + rho' db*, of variance
v^idle.

### 3. The one-instrument ergodic law

*Cited.* AX-15 (`soner2013homogenization` (4.3)-(4.5), Remark 3.3 for the ergodic reading;
`muhlekarbe2017primer` (4.10)-(4.13)): a solution of the first corrector equation is the quartic
w(y) = -(c/(12 v)) y^4 + (lambda/v) y^2 + ((kappa^- - kappa^+)/2) y on the band, linear outside, with
smooth fit at both edges forcing both to +-sqrt(2 lambda/c) (the band is symmetric about the
target whatever the rates; the asymmetry enters only w's odd term), lambda = c Delta^2/2, the
gradient constraint -kappa^+ <= w' <= kappa^- attained at the two edges, and Delta^3 = 3 (kappa^+
+ kappa^-) v/(4c). *Lemma (algebra, the project's own, rule 6).* For c, v > 0 and rates kappa^+,
kappa^- >= 0 not both zero: w'' = (2 lambda - c y^2)/v on the band by construction, so (v/2) w'' +
(c/2) y^2 = lambda there; w'' vanishes at +-Delta iff lambda = c Delta^2/2; and w'(Delta) = kappa^-,
w'(-Delta) = -kappa^+ hold iff (2 lambda Delta - c Delta^3/3)/v = (kappa^+ + kappa^-)/2, which with
lambda = c Delta^2/2 is (2 c Delta^3/3)/v = (kappa^+ + kappa^-)/2, that is, Delta^3 = 3 (kappa^+ +
kappa^-) v/(4c); on the band w'' >= 0, so w' runs monotonically from -kappa^+ to kappa^-, the
gradient constraint; and off the band, where w is linear (w'' = 0), (c/2) y^2 >= (c/2) Delta^2 =
lambda since |y| >= Delta, so the variational inequality holds there too (the auditor's note). This
is the closed algebraic content of the sources' solution, verified by substitution; the sources
supply the corrector framework and the ergodic reading, and uniqueness of the corrector
solution, which nothing here uses, is `possamai2015homogenization` Corollary 6.1, quoted in
ledger entry AX-16 (audited, on main). (The earlier inline verification is
withdrawn in favour of the citation; its gradient inequalities had the two rates on the wrong
sides, red's correction 1: the lower bound needs w' >= -kappa^+ against the up-pushes and
w' <= kappa^- against the down-pushes, and the ergodic band does not shift with the rate
asymmetry.) *Hypotheses in our instance.* Each of part 2's reductions is a scalar tracking
problem whose stage loss is (c/2) y^2 with a constant curvature c (part 1's identity, and the
frozen-ETF expansion), whose target innovation has a constant variance per review, and whose
rates are constant; the corrector problem is the fine-regime limit object read as in claim
029's prior art. The identification of the discrete fine-regime width with this Delta is the
cited step (Not shown).

Applying to part 2's reductions with (c, v) = (gamma Sigma_AA, v_A), (c^res, v_A), (gamma Sigma_AA,
v^idle) gives (a)-(c); the ratio is immediate.

### 4. The weight

*Exact.* The two-dimensional ergodic problem of part 4 is part 1's coordinates with Brownian innovations;
dividing lengths by Delta_free and time by Delta_free^2/v_A makes the fund's holding cost, rate
and innovation variance dimensionless with unit constants, and leaves the ETF's rate,
curvature and effective variance as the ratios displayed, the correlations and the asymmetries;
Delta_E is the ETF's own fine-regime scale by part 3, so xi is the ratio of the two scales. At
rc = 0, part 2(a) gives F = 1 exactly. For one instrument, the reflected process of part 3
spends Lebesgue-null time on {-Delta, Delta} almost surely (the pushes are singular with
respect to time), so its idle fraction tends to one as the discrete steps shrink; the check
illustrates the rate, the step-to-width ratio falling like v^{1/6}. *Readings.* As kappa_E -> 0
with kappa_A fixed the ETF's cost of holding e at zero vanishes and the reduction is part 2(b)'s;
as kappa_E -> infinity the ETF never trades and the reduction is part 2(c)'s; that F tends to
these ends needs the continuity of the ergodic problem's cross-section in xi at the ends, not
proved here; and that both idle probabilities tend to one in the two-dimensional problem needs
its pushing set to have measure zero, not proved here. Under both, the idle probability cannot
be the weight, as part 4 reads.

## Checks

`checks/042/check.py` (rule 22: illustrations; floating point). (i) Part 1's identity and the
frozen-ETF form on 200 random covariances. (ii) Part 3: the smooth-fit algebra (lambda = c
Delta^2/2, the gradient change, the cost split) on 50 random inputs, and a Monte Carlo of a
reflected random walk's average cost over a grid of half-widths in the fine regime (step 5% of
the half-width), whose minimizer is at the law's value within the grid. (iii) Part 2(b) and
(c) as path identities of the two-instrument loss along fund band policies. (iv) Part 4: the
end ratio; the ETF's idle fraction rising toward one as the step shrinks at four rate ratios,
and the observation that at basis-point ETF rates the ETF is coarse unless the step is tiny.

## Not shown

- The identification of the discrete fine-regime band with the ergodic problem's half-width
  (claim 029's cited step; `soner2013homogenization`, `muhlekarbe2017primer` at prior-art level).
- The intermediate F(xi, ...): its closed form, bounds or monotonicity (the second claim's
  target; `possamai2015homogenization` names the object). The end limits of F are readings of
  the exact reductions, not proved as limits of the ergodic problem.
- The band's centre beyond the leading order (at the ergodic level it is the target, AX-15);
  the O(kappa) shifts of the discrete, finite-horizon brackets are claim 107's, with the ETF's fees.
- The end limits of F and the two-dimensional idle-probability limit (readings in part 4, red's
  correction 2, option (a)).
- The fine-fund, coarse-ETF pairing as a theorem (the reading at the end of part 4).
- Several ETFs (the hedge ratio becomes a vector; part 1's identity extends with the residual
  curvature given all ETFs).

## Prior art

Mechanism: an exact change of coordinates makes the two-instrument loss diagonal in the fund's
gap and the ETF's tracking error, so the ETF's cost reaches the fund only through that error;
the one-instrument small-cost band is an ergodic control problem with a quartic value function,
whose half-width and average cost follow from smooth fit; the two-instrument problem is the
same object in two dimensions with an oblique control, explicit at its ends and at zero risk
correlation.

General results checked: claim 107 (the residual curvature, hedge ratio and the frictionless
reduction, formalized); claim 029 (the one-instrument dynamic band; its Not shown for the fine
regime), claim 100 (the band along a learning path), claim 101 refuted (the conjectured constant
8c, corrected to 4c here by the ergodic computation); `soner2013homogenization` (equation (4.4),
the first-corrector half-width; the same cube-root law) and `muhlekarbe2017primer` (section 4,
the one-dimensional expansion), the one-instrument law's sources, at the level of claim 029's
citation; `possamai2015homogenization` (full text registered; the multidimensional corrector: the
leading-order region is the solution of an ergodic problem, explicit only in special cases), the
kill benchmark, named: this claim's ergodic problem is its object for the pair, and parts 1-4
give the structure the benchmark leaves implicit (the diagonal coordinates, the three exact
reductions, the dimensionless ratio and the idle-probability negative); `liu2013portfolio`
(named, not used).

Searched: claims 029, 100, 101, 107; FINDINGS D15c entries; experiments 036-039; refs/text for
the three small-cost sources. This is a claim because D15e asks for the leading order in the
inputs and the roadmap's conjecture has a specific weight (the idle probability) that part 4
rules out, with the correct weight named.

## Open objections

The analyst's experiment 043 (2026-09-29, after approval; parts 1-4 agree, the half-width
tending to the 4c law and the band centred at every step): part 4's F is now named as the
fund's band at the ETF holding b = b* (the cross-section along e = rho_h y_a), which is the
object with the stated ends, not the cross-section along e = 0. PM's hold (2026-09-29) after red's verdict, one revision pass: (1) part 3 now cites AX-15 (both
sources state the constant as 4c: `soner2013homogenization` (4.4), `muhlekarbe2017primer` (4.12)
with unit rates), checks its hypotheses, and states that the ergodic band is centred on the
target whatever the rate asymmetry; the inline verification, whose gradient inequalities had
the rates on the wrong sides (red's correction 1), is withdrawn; (2) part 4's end limits of F,
the two-dimensional idle limit and the idle-probability negative are readings conditional on
the unproved continuity and measure-zero facts (red's correction 2, option (a)), in part 4, the
proof, Not shown and the title; the exact content (xi, F = 1 at rc = 0, the one-instrument idle
fraction) stays. Lean's scoping point (2026-09-29): part 2(c)'s frozen ETF needs both bounds
pinned or prohibitive rates both ways, since a cap alone stops purchases only. Earlier: none. Red should test: part 2(a)'s separation with correlated innovations (the
argument uses only that the objective is a sum with separate controls); part 3's lower-bound
argument (the boundary term for policies with unbounded excursions); the sign conventions in
v^idle and v_B^eff (which ratio multiplies which variance); and whether the check's fine-regime
Monte Carlo is fine enough (step 5% of the half-width).

## Review

**Red, 2026-09-29** (on abd716ad). Red-passed, **conditional on two required corrections**; PM, please hold approval until they land. Red re-derived each part by hand and tested parts 1-3 numerically with its own code, written without reading checks/042.

**Part 1.**
- The identity holds, and the innovation moments of (y_a, e) = -(da*, db* + rho_h da*) are v_A, v_B^eff and r sqrt(v_A v_B) + rho_h v_A.
- On 200 random covariances and innovation laws, both hold to 2.8e-15 relative.
- The sign conventions (the open objection) are right: v^idle carries rho' = Sigma_AE/Sigma_AA and v_B^eff carries rho_h = Sigma_AE/Sigma_EE.

**Part 2.**
- (a) Separation with correlated innovations holds. The objective is a sum with separate controls and no shared constraint (budget and caps slack), so r enters only the joint law, which neither term sees. In red's claim 108 DP at corr 0, the fund's edges did not move with the ETF incumbent at r = +-0.8.
- (b) is claim 107 part 3, which red reproduced in experiment 036.
- (c) is claim 108 part 3's completed square, which red checked against a one-instrument DP.

**Part 3.**
- The candidate w, smooth fit (lambda = c Delta^2/2), the gradient condition (4 c Delta^3/(3v) = kappa^+ + kappa^-) and attainment all check out. Attainment uses the reflected motion's uniform law, holding cost c Delta^2/6 and pushing rate v/(4 Delta) at each end.
- Red's average-cost relative value iteration (beta = 1, lazy +-s walk, v = s^2/2 per review, exact L1 transform) gives:
  - half-widths 0.900 and 0.950 Delta at step/Delta = 0.2 and 0.1, approaching Delta;
  - average cost 0.4983 and 0.4996 against c Delta^2/2 = 0.5.
  So the corrected 4c constant, not 8c (which would give 0.79 Delta), is the discrete limit. The check's 5% step is fine enough.

**Required correction 1 (part 3's lower bound: signs).** As written, the verification's inequalities do not give a lower bound:
- with (v/2) w'' + (c/2) y^2 >= lambda, Ito gives E[w(y_T) - w(y_0)] >= ..., not <=;
- the gradient constraints are stated as w' >= -kappa^- and w' <= kappa^+, with pushes U^+ at kappa^+.
The correct verification:
- For the minimization, require (v/2) w'' + (c/2) y^2 >= lambda, w' >= -kappa^+ (pushing up is never better than its cost) and w' <= kappa^- (pushing down).
- Then E[w(y_T)] - w(y_0) >= E int (lambda - (c/2) y^2) dt - kappa^+ E U^+_T - kappa^- E U^-_T.
- Hence the expected cost over [0, T] is >= lambda T + w(y_0) - E w(y_T), and the rest of the argument is unchanged. The candidate's w' runs from -kappa^+ at -Delta to kappa^- at +Delta; the total change kappa^+ + kappa^-, and hence the law, is unaffected.
- *Consequence for the centre.* Smooth fit puts both edges where w'' = 0, at +-sqrt(2 lambda / c), so at the ergodic level the band is symmetric about the target whatever the rate asymmetry; only w's levels shift.
  - The Proof's parenthetical "with asymmetric rates the band's centre shifts by the same computation" is therefore wrong. Please say the centre does not shift at leading order.
  - Red's value iteration at rates 1.8:0.2 and 1.98:0.02 gives centre +0.0000 and the same half-widths 0.900 and 0.950 as the symmetric case.
  - Not shown's O(kappa) centre shifts belong to the discrete, finite-horizon brackets, not to the leading order.

**Required correction 2 (part 4: readings stated as results).**
- Statement part 4 asserts "F -> 1 as xi -> 0" and "F -> Delta_frozen/Delta_free as xi -> infinity". The Proof says "the continuity of the ergodic problem's cross-section at these ends is not proved here (Not shown)", and Not shown agrees.
- The idle-probability negative ("both idle probabilities tend to one at every xi, while the ends of F differ") rests on those unproved limits. Its "at every xi" for the two-dimensional problem extends the one-instrument measure-zero fact without a proof about the 2D optimal policy.
- The title repeats both ("not on the ETF's idle probability, which tends to one in the fine regime at every rate ratio").
- *Fix, either:*
  - (a) state the end limits of F, the 2D idle-probability limit and hence the negative as a reading conditional on the unproved continuity (and on the 2D policy's pushing set having measure zero), in part 4 and the title; or
  - (b) prove them.
- What part 4 does establish is exact and stays: the reduction to one dimensionless ratio xi (dimensional analysis), F = 1 at rc = 0 (part 2(a)), and the one-instrument idle fraction tending to one.

**Mechanism (4b).** A diagonalizing change of coordinates (fund gap, ETF tracking error), three exact reductions, the one-instrument ergodic verification with the corrected constant, and a dimensionless weight xi. New: the error coordinate's decoupling, the three limits in one frame, and xi as the named weight. The intermediate F is left to the second claim, against `possamai2015homogenization`.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's two required corrections (part 3's verification signs and the centre statement; part 4's limits and the idle-probability negative stated as readings) and PM's rule 21 point (the one-instrument ergodic law cited through a ledger entry, not re-proved). Math revises, and red records a fresh verdict.

Revision (math, 2026-09-29, per PM's hold): rule 21 option taken: part 3 cites AX-15, since both
sources state the constant (4c); correction 1 is thereby settled except the centre statement,
which is added; correction 2 as red's option (a).


**Red, recheck after PM's withdrawal, 2026-09-29.** Red-passed. Both required corrections and PM's rule 21 point are made.
- *Rule 21: the law is cited, and its constant is 4c.* Part 3 now cites AX-15 (audited). `soner2013homogenization` (4.4), read in refs/text, gives rho_0 = (3 alpha-bar^2 (lambda_{1,0} + lambda_{0,1}) / (4 sigma^2))^{1/3}. With the entry's mapping (sigma^2 <-> c, alpha-bar^2 <-> v), that is Delta^3 = 3 (kappa^+ + kappa^-) v / (4c), the constant red confirmed by average-cost value iteration (half-width 0.95 Delta at step/Delta 0.1, average cost c Delta^2/2). (4.3) gives rho_0 = -rho_1, the symmetric band.
- *The hypotheses* (quadratic stage loss with constant curvature, constant innovation variance, constant rates, the corrector level) are checked for each reduction. The discrete-to-corrector identification stays Not shown.
- *Required correction 1 is made.*
  - The retained algebraic lemma (rule 6) has the right signs: w'(Delta) = kappa^-, w'(-Delta) = -kappa^+, the gradient constraint -kappa^+ <= w' <= kappa^-, and (c/2) y^2 >= lambda off the band. Red re-derived w'(+-Delta) from the quartic.
  - The band is stated centred on the target whatever the rate asymmetry. That matches red's value iteration at 99:1 rates (centre 0).
- *Required correction 2 is made.* Part 4 separates what is exact (the reduction to xi, F = 1 at rc = 0, the one-instrument idle fraction tending to one) from readings conditional on the unproved continuity and the 2D pushing set having measure zero (F's end limits, and the idle probability not being the weight). The title says "as a reading".
- *Lean's frozen-ETF point is in 2(c):* the box is pinned, or the rates prohibitive, since a cap alone stops purchases only.
No other part changed. Red's earlier tests of parts 1-2 stand.

Verdict: red-passed
## Formalization notes

Approved 2026-09-29 by pm: Red's review and recheck are sound: part 1's identity and moments to 2.8e-15 on 200 draws, part 2's three reductions checked against red's claim 107/108 DPs, part 3 now cites AX-15 (audited ok; Soner-Touzi (4.4) gives the 4c constant red confirmed by value iteration, band centred at 99:1 rates), part 4's exact content (the xi reduction, F = 1 at rc = 0) separated from readings; both required corrections and PM's rule 21 point made. Mechanism: a diagonalizing coordinate change, three exact reductions and the cited one-instrument corrector law, an application; new: the error-coordinate decoupling, the three limits in one frame and xi as the named weight. D15e's kill criterion is not yet decided: the intermediate F is the second claim's. Limits: discrete-to-corrector identification cited, not proved; F's end limits are readings.


Parts 1 and 2 are algebra and an exact decomposition; part 3 is a citation (AX-15) with a
hypothesis check; part 4's exact content is dimensional analysis plus a one-dimensional
measure-zero fact, the rest readings.

Lean, 2026-09-29 (final): the formal content of parts 1-4 is machine checked. The statement is in
`lean/Standalone/M7FineBandOneCostlyEtf.lean` and the proof in `lean/Novel/M7FineBandOneCostlyEtfProof.lean`.
- Imports: the proof imports claim 107's proof module (depends_on, Q-04).
- AX-15, the corrector law, is cited and not used by any formal conjunct beyond the formula it
  displays; there is no Upstream structure.
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/042/check.py` pass.
- Scope: lean's note to PM (lean/claim042-notes), PM's reply, and math's rule 6 note on part 3's
  lemma.

Machine checked:
- Part 1:
  - the error-coordinate identity;
  - v_B^eff, the covariance r sqrt(v_A v_B) + rho_h v_A and v^idle, as second moments of a finite law.
- Part 2(a), in claim 029's model with two instruments and Sigma_AE(t, z) = 0 at every review and
  state:
  - each instrument's instance is an M6 instance;
  - the value is the sum of the two one-instrument values;
  - a post-trade holding is optimal iff each coordinate is optimal in its own instance, whatever
    the outcome law and the ETF's rates.
- Part 2(b): claim 107's formal part 3.
- Part 2(c): the completed square for a fixed ETF holding.
- Part 3:
  - the corrector lemma: the quartic solves (v/2) w'' + (c/2) y^2 = lambda. w''(+-Delta) = 0 iff
    lambda = c Delta^2/2. Then w'(Delta) = kappa^- and w'(-Delta) = -kappa^+ iff
    Delta^3 = 3 (kappa^+ + kappa^-) v/(4c). On the band w'' >= 0 and -kappa^+ <= w' <= kappa^-, and
    off it (c/2) y^2 >= lambda;
  - its C^2 linear continuation off the band (`CorrectorC2`): the unique positive root, smooth fit at
    +-Delta, the symmetric band, and the attainment identity c Delta^2/6 + (kappa^+ + kappa^-) v/(4 Delta) = lambda;
  - the end ratio (1 - rc^2) v^idle/v_A.
- Part 4: the identity for xi^3.

Paper-level:
- part 2(c)'s dynamic reading (M6's box cannot pin an instrument);
- AX-15's corrector framework and the discrete-to-corrector identification;
- part 4's dimensional analysis, end readings and idle fractions;
- the Checks.

---
id: 101
title: "Fine-regime leading order along the learning path: the cube-root band with M7's shrinking inputs, its t^(-2/3) law, the drift displacement, and the crossover from the static anchor at a belief-innovation scale of the round-trip cost over root three"
status: refuted
model_version: M7
depends_on: [029, 100]
axioms_used: []
formal: none
direction: D13
---
## Statement

D13's third and last budgeted claim, per PM's scope note: the fine-regime leading order must
cover the learning path (time-varying c_t and V_t and the outward drift) and must say how it
differs from each kill benchmark with the target plugged in. No proof is at hand; parts 2-4
are conjectures with numerical evidence, part 1 is exact from claims 029 and 100, and part 5
is arithmetic on the conjectured formula. It imports no literature theorem.

**Setting.** A slack-budget M7 instance, one instrument (n = 1), beta = 1, pure-learning
marking (gross return one on every path), directional rates with kappa^+ + kappa^- > 0, no cap
binding, horizon T. Write, for the instrument,

```
c_t = gamma Sigma_t,                     the tracking curvature (claim 100),
w_t = (kappa^+ + kappa^-)/c_t,           the static width (claim 029's ceiling),
s_t^2 = v_t = G V_t G' / (gamma Sigma_{t+1})^2,    the target's belief-driven innovation variance,
delta_t = x*_t (Sigma_t/Sigma_{t+1} - 1),          the learning drift (claim 100's 2b, n = 1),
Delta_t = [ 3 (kappa^+ + kappa^-) v_t / (8 c_t) ]^(1/3),   the conjectured half-width,
tau_mix,t = Delta_t^2 / v_t,             the band's mixing time in quarters.
```

Under M7's fixed-means path, P_t = (P_0^{-1} + t H' R^{-1} H)^{-1}, so as t grows

```
V_t = P_t - P_{t+1} = M / t^2 + O(1/t^3),   M = (H' R^{-1} H)^{-1},
v_t = G M G' / (gamma^2 Sigma_r^2 t^2) + O(1/t^3),   c_t -> gamma Sigma_r,
Delta_t = A t^(-2/3) + O(t^(-1)),   A = [ 3 (kappa^+ + kappa^-) G M G' / (8 gamma^3 Sigma_r^3) ]^(1/3),
delta_t = O(1/t^2),   tau_mix,t = O(t^(2/3)).
```

1. **Exact anchors (claims 029 and 100; finite-law variant).** hi_t - lo_t <= w_t at every
   (t, z) with t <= T-1, with equality at T-1 when no bound binds; w_t is nondecreasing in t; and
   under pure-learning marking there is t_0, not depending on T, with hi_t - lo_t < w_t for all
   t_0 <= t <= T-2. Any leading order for the fine regime must lie below w_t and, by claim
   029's 1e, is attained only when some outcome leaves the marked band straddling the next
   band. Under a law with a density (M7's Gaussian law) every outcome set contains straddling
   outcomes, so the strict inequality is expected at every t <= T-2; that is not proved, since
   the finite framework does not cover the Gaussian law (M7).

2. **Conjecture (leading order along the learning path).** Under M7's Gaussian law, for every
   epsilon > 0 there are t_1 and h such that for all t >= t_1 and all horizons T with
   T - t >= h tau_mix,t, and every history,

   ```
   | (hi_t(z) - lo_t(z)) / (2 Delta_t) - 1 | <= epsilon.
   ```

   Equivalently the band's width is 2 A t^(-2/3) (1 + o(1)): it decays like the two-thirds
   power of the number of quarters learned, with the explicit constant A set by the round-trip
   cost, the asymptotic information matrix M of the filter, the instrument's row G of the
   loading map, gamma and the return-risk Sigma_r. The same statement is conjectured for
   finite-law variants whose innovations at every node have at least three atoms and a
   standard deviation s_t with s_t/Delta_t -> 0 (the two-point lattice of experiment 023 is
   excluded: there the fine width is quantized at about two lattice steps).

3. **Conjecture (displacement).** In the setting of part 2 the band's centre is displaced from
   the target in the direction of the learning drift,

   ```
   (hi_t + lo_t)/2 - x*_t = (2/3) (delta_t / v_t) Delta_t^2 (1 + o(1)) + (kappa^- - kappa^+)/(2 c_t) O(1),
   ```

   so that, relative to the half-width, the displacement is (2/3) delta_t Delta_t / v_t = O(t^(-2/3)):
   the band leans outward, away from zero, as the shrinking risk charge pushes the target
   outward, by a fraction of its half-width that vanishes with learning. The cost-asymmetry
   term is claim 029's static offset and does not decay.

4. **Conjecture (finite-law variant, same order).** In the finite-law variant of M7 with
   pure-learning marking and innovations with at least three atoms per node, the same two
   statements hold with the tree's conditional innovation variance in place of v_t.

5. **Consistency and crossover (arithmetic on the formula; proved).**
   (a) The formula is self-consistent with the exact ceiling exactly when
   2 Delta_t < w_t, that is 3 v_t c_t^2 < (kappa^+ + kappa^-)^2, that is
   s_t < w_t / sqrt(3); in belief units, since s_t c_t = sqrt(G V_t G') Sigma_t/Sigma_{t+1},

   ```
   sqrt(G V_t G') Sigma_t/Sigma_{t+1} < (kappa^+ + kappa^-)/sqrt(3):
   ```

   the instrument's belief-mean innovation standard deviation, in expected-return units, must
   be below its round-trip cost over root three. Before that quarter the conjectured width
   exceeds the exact ceiling and cannot be the band; after it the fine regime is the only
   consistent regime. This crossover does not involve gamma or Sigma. On M7's path the left
   side is O(1/t) and the right side is fixed, so the crossover quarter t_c is finite and
   every instrument crosses; an instrument whose initial belief innovation is already below
   its round-trip cost over root three (a fund with a 100 bp round trip needs an alpha-forecast
   innovation of 58 bp per quarter to be above it) is in the fine regime from the first
   review. (b) The band's mixing time tau_mix,t = (3 (kappa^+ + kappa^-) / (8 c_t s_t))^(2/3) is
   O(t^(2/3)), so the coefficients (c_t, v_t) change by a relative O(t^(-1/3)) over one mixing
   time, and the drift moves the target by a relative O(t^(-2/3)) of the half-width over one
   mixing time. These two facts are why part 2's quasi-stationary reading of the benchmark
   is conjectured to be exact in the limit and why the drift enters only at the next order.
   (c) Near the horizon's end the band returns to the static band over a scale of tau_mix,t
   quarters: at T-1 it is exactly w_t (claim 029), so part 2's h tau_mix,t clearance cannot be
   dropped.

**How this differs from each kill benchmark with the target plugged in** (PM's scope note).
- `muhlekarbe2017primer`, section 4, (4.14)-(4.15): the half-width lambda^(1/3) Delta_pi with
  Delta_pi = (3/(2 gamma) [pi^2(1-pi)^2 - 2 pi(1-pi) pi_f sigma_F/sigma_S + pi_f^2 sigma_F^2/sigma_S^2])^(1/3)
  in weight units, the bracket being the frictionless weight's quadratic variation over the
  asset's, for a target moved by a mean-reverting factor with constant coefficients. Part 2's
  Delta_t is that formula in dollar holdings with M7's (c_t, v_t) in place of constants: the
  same balance of displacement loss against reflection cost. What the benchmark does not
  contain: the coefficients' time dependence along a learning path and the explicit
  t^(-2/3) law with its constant A; the consistency conditions of part 5(b), which fail early
  (t small, where the exact ceiling binds) and near the end; the static ceiling and the
  crossover of part 5(a), because the benchmark trades continuously and has no one-review
  width; and the drift, which its target does not have.
- `martin2012optimal`, (9)-(10): half-width (3 epsilon G Gamma_0^2/2)^(1/3) with Gamma_0^2
  the ratio of the target's variation to the asset's, and a displacement
  (E_t[d g_0]/V_t[dX]) (2 epsilon^2 G^2/(3 Gamma_0^2))^(1/3) = (2/3) (target drift / target
  variance) x half-width^2 in the drift's direction. Part 3 is that displacement with M7's
  delta_t and v_t plugged in; the (2/3) constant is Martin's. So the drift-induced tilt is not
  new in kind. What is specific to the learning path is that the displacement is outward
  (delta_t has the sign of x*_t when G != 0, claim 100), that its relative size is O(t^(-2/3))
  and vanishes, and that in the coarse quarters before the crossover the tilt is instead claim
  029's exact beta(kappa^+ U - kappa^- D)/c_t, which does not vanish and is decided by sign
  masses, not by a drift-to-variance ratio.
- Neither benchmark has the bundling faces of claim 029's 2c for n > 1, which experiment 023
  found to set the calibrated ETF section; this claim is one-instrument and does not add to
  that.

**Reading for D13** (not a further claim). If parts 2-3 hold, the fine-regime boundary along the
learning path is the benchmarks' formula with M7's inputs plugged in, valid after the crossover
quarter and away from the horizon's end, with the drift at the next order and Martin's
constant. What the quarterly, learning-driven structure adds is exact and elementary: the
ceiling, the crossover criterion in belief units, the t^(-2/3) law, and the consistency
conditions that delimit where the plugged-in formula can hold. Whether that clears D13's kill
criterion is PM's reading.

## Proof

none yet for parts 2-4. Part 1 is claims 029 (1b, 1e) and 100 (2a, 2d), transferred as stated
there; the density remark is not proved. Part 5 is verified as follows.

*5(a).* 2 Delta_t < w_t iff 8 Delta_t^3 < w_t^3 iff 3 (kappa^+ + kappa^-) v_t / c_t < (kappa^+ + kappa^-)^3 / c_t^3
iff 3 v_t c_t^2 < (kappa^+ + kappa^-)^2 iff s_t c_t < (kappa^+ + kappa^-)/sqrt(3) iff s_t < w_t/sqrt(3).
With s_t = sqrt(G V_t G')/(gamma Sigma_{t+1}) and c_t = gamma Sigma_t, s_t c_t = sqrt(G V_t G') Sigma_t/Sigma_{t+1},
which does not involve gamma, and Sigma_t/Sigma_{t+1} -> 1. Claim 100's 2a-2b give
V_t = P_t - P_{t+1} = P_t (P_{t+1}^{-1} - P_t^{-1}) P_{t+1} = P_t H' R^{-1} H P_{t+1} and
P_t = M/t + O(1/t^2) with M = (H' R^{-1} H)^{-1}, hence V_t = M/t^2 + O(1/t^3) and the O(1/t)
claim; the right side is a positive constant, so the inequality holds for all t beyond some
finite t_c. The numerical example: (100 bp)/sqrt(3) = 57.7 bp.

*5(b).* tau_mix,t = Delta_t^2/v_t = Delta_t^2/s_t^2; with Delta_t^3 = 3(kappa^+ + kappa^-) s_t^2/(8 c_t),
Delta_t^2/s_t^2 = (Delta_t^3/s_t^3)^(2/3) = (3(kappa^+ + kappa^-)/(8 c_t s_t))^(2/3). On the path
s_t = O(1/t) and c_t is bounded away from zero, so tau_mix,t = O(t^(2/3)). The relative change of
v_t over tau_mix,t quarters is tau_mix,t |v_{t+1} - v_t|/v_t = O(t^(2/3)) O(1/t) = O(t^(-1/3)), and of
c_t likewise or smaller (c_t - c_{t+1} = gamma G V_t G' = O(1/t^2)). The drift over one mixing
time is tau_mix,t delta_t = O(t^(2/3)) O(1/t^2) = O(t^(-4/3)), against a half-width O(t^(-2/3)):
relative O(t^(-2/3)). Part 3's relative displacement (2/3) delta_t Delta_t/v_t is
O(1/t^2) O(t^(-2/3)) / O(1/t^2) = O(t^(-2/3)).

*5(c)* is claim 029's 1b at T-1, and the mixing-time reading of how far back the terminal band
propagates is part of the conjecture, not proved.

*Heuristic for parts 2-3 (not a proof).* Freeze (c, v, delta) and let the deviation from the
target be a Brownian motion with variance rate v and drift -delta, reflected at the band's
edges a < b. For delta = 0 the stationary law is uniform, the displacement loss rate is
c (b - a)^2/24 for a band centred at the target, and the reflection rates at the two edges are
v/(2(b - a)) each, costing (kappa^+ + kappa^-) v/(2(b - a)) per quarter; minimizing the sum over
the width gives (b - a)^3 = 6 (kappa^+ + kappa^-) v / c, that is b - a = 2 Delta_t. With a drift
the stationary law is exponentially tilted, and the first-order correction to the optimal
centre is Martin's (10) in these units, (2/3)(delta/v) Delta^2 in the drift's direction. The
learning path is then treated as quasi-stationary on the strength of 5(b). Making this
rigorous at quarterly reviews (a discrete reflected walk with time-varying coefficients and a
finite horizon) is the open proof.

## Checks

`uv run python checks/101/check.py` (exits non-zero on failure; a check, not a proof; it asserts
only the exact ceiling of part 1 and internal consistency, and prints the evidence for parts
2-3). An assumed one-fund, one-factor M7 instance with the Gaussian law, the fixed-means
filter path (P_t in information form), pure-learning marking, beta = 1, T = 120, the deviation
from the target as the state on a grid of step 1/1000 with exact affine extrapolation outside
the band, the target's innovation by 16-point Gauss-Hermite quadrature at every t, and the
drift frozen at the target's prior-mean level. Two rate settings, a fund-like 50 bp each way
and an ETF-like 5 bp each way. Reported at t in {1, 5, 10, 20, 40, 60, 80, 100}: the width over 2 Delta_t,
the width over w_t, the centre displacement over (2/3)(delta_t/v_t) Delta_t^2, and the
crossover quarter of part 5(a). The numbers are quoted in the FINDINGS entry filed with this
claim; they are evidence about these two instances only.

## Not shown

- Parts 2-4 are conjectures. Nothing here proves a leading order at quarterly reviews; the
  continuous-time benchmarks are cited as the origin of the formula, not as a proof for M7.
- Persistence is outside M7 (fixed means). Experiment 022's stationary AR(1) instance shows
  fund widths depending strongly and non-monotonically on alpha's persistence at fixed cost
  while the belief innovation barely varies, so with mean reversion of order 1 - Phi per
  quarter comparable to 1/tau_mix the quasi-stationary reading fails and the predictable
  reversion competes with the band; a version with persistence and a claim on it are outside
  D13's budget.
- One instrument only; for n > 1 the calibrated sections are set by claim 029's bundling
  faces (experiment 023), which this claim does not address.
- Pure-learning marking; with real marking the return-driven deviation adds a term to v_t
  that does not learn away (claim 100's 2d remark), so the t^(-2/3) law then holds for the
  learning part only.
- The Gaussian law is outside the finite framework; part 1's strict inequality under a
  density is expected, not proved.
- No calibration or economic magnitude; the 58 bp figure is an arithmetic example.

## Prior art

Mechanism: a position tracking a slowly moving target under proportional costs is held in a
band whose width balances a quadratic displacement loss against the cost of reflecting the
deviation at the edges, giving a cube-root law in the cost times the target's variation over
the curvature; along a path on which the target's variation and the curvature change slowly
relative to the band's mixing time, the same law holds with the current coefficients, a drift
displaces the band by a known fraction of its squared half-width, and a fixed review interval
imposes an exact one-review ceiling that the law must fall under before it can apply.

General results checked: `muhlekarbe2017primer` (full text, section 4, (4.13)-(4.15), read at
the level of those displays): the leading-order half-width under a mean-reverting factor with
constant coefficients; part 2 is that formula with M7's inputs, and the differences are
stated above. `martin2012optimal` (full text, (7)-(10), read at the level of those displays):
the cube-root half-width with the target's variation ratio and the drift displacement at
order epsilon^(2/3); part 3 is (10) with M7's drift and variance. `soner2013homogenization`
(4.4) and Lemma 8.2, `possamai2015homogenization` Theorems 3.1-3.2, `kallsen2017general`,
`davis1990portfolio` (full text, title level or the named displays): the rigorous
continuous-time expansions from which the balance argument is taken; none has a learning path,
a review interval or a static ceiling. `liu2013portfolio` (full text): caps, not used here.
Claims 029 and 100 (approved): the exact anchors and the learning path's second moments.
Experiments 022 (Part 3, stationary persistence) and 023 (exact reference; lattice fine widths
of two steps, calibrated sections set by bundling): the evidence that shaped the regime
statements. `garleanu2009dynamic` and math's claims 030-032 (provisional): the quadratic-cost
learning policy, whose trading speeds are the other cost geometry's counterpart of this band.

Searched: claims 009, 029, 100, the D13 roadmap entry and progress line, PM's scope notice, the
librarian's D13 sweeps in FINDINGS, experiments 021-023, the refuted directory, and the
registered texts named above at the level stated. No web search. This is filed as a
conjecture because D13's question is the leading-order band along the learning path and the
honest answer is the benchmark formula with M7's inputs plus the exact quarterly anchors that
delimit it; no priority is claimed for any ingredient.

## Open objections

none

## Review

**Red, 2026-09-28.** Refuted: the conjectured half-width's constant is wrong by a factor of 2 inside the cube root.
- The band is 2^(1/3) = 1.26 times the conjectured 2 Delta_t, both in the stationary limit and along the learning path.
- Every statement built on the constant inherits the error: the width law of parts 2 and 4, part 3's displacement value, and part 5's crossover and mixing time. Part 5(a)'s crossover changes from the round-trip cost over root three to the round-trip cost over root six.
- The shape of the result survives: a cube-root band with M7's inputs, the t^(-2/3) law with a corrected A, and Martin's (2/3)(delta/v) displacement in the drift's direction.

**1. The claim's own heuristic contradicts its formula.**
- The Proof's heuristic has loss rate c (b - a)^2/24 (stage loss (c/2) e^2 under a uniform law) and reflection cost (kappa^+ + kappa^-) v/(2(b - a)). Its minimizer is (b - a)^3 = 6 (kappa^+ + kappa^-) v/c, as the Proof says, and red confirmed the local-time rate v/(2W) by Ito on X^2.
- But b - a = 2 Delta_t with Delta_t^3 = 3 (kappa^+ + kappa^-) v/(8c) gives (b - a)^3 = 3 (kappa^+ + kappa^-) v/c, half of that.
- The heuristic's own half-width is Delta*_t^3 = 3 (kappa^+ + kappa^-) v_t/(4 c_t) = 2 Delta_t^3.
- The benchmarks agree with Delta*. `muhlekarbe2017primer` (4.15) and `martin2012optimal` (9) both give half-width^3 = (3/2) lambda v/c with lambda the one-way rate. With kappa^+ = kappa^- = lambda, that is 3 (kappa^+ + kappa^-) v/(4c).
- So the Statement's "Part 2's Delta_t is that formula in dollar holdings" is false: Delta_t is the benchmark's half-width divided by 2^(1/3).

**2. Stationary quarterly dynamic program** (red's own script, not committed; exact M6/M7 stage).
- *Model.* Loss (c/2) e^2 on the post-trade deviation, rates kappa^+ = kappa^- = k, Gaussian target moves N(0, v) per quarter, beta = 1, relative value iteration to convergence. The grid has step at most s/12 and Delta/150 with subgrid argmin refinement.
- *Results.* Width over the conjecture's 2 Delta:

| s/Delta_claim | width / 2 Delta_claim | width / 2 Delta* |
|---|---|---|
| 0.40 | 1.028 | 0.816 |
| 0.20 | 1.144 | 0.908 |
| 0.10 | 1.202 | 0.954 |
| 0.05 | 1.231 | 0.977 |

- *Reading.* The ratio to 2 Delta* is 1 - 0.46 (s/Delta_claim) to within the grid. This is the discrete-monitoring shift of Broadie, Glasserman and Kou, 0.5826 s per edge: 2 x 0.5826/2^(4/3) = 0.462. So the width tends to 2 Delta* = 2^(4/3) Delta_claim, not to 2 Delta_claim.

**3. Learning-path dynamic program** (part 2's own setting).
- *Model.*
  - One instrument with gamma = 1, Sigma_r = 1, G = 1, P_t = 1/(1 + t), so c_t = 1 + P_t and v_t = (P_t - P_{t+1})/(1 + P_{t+1})^2.
  - Rates k = 0.5 each way, pure-learning marking, beta = 1, drift frozen at zero, horizon T = 60,000.
  - Backward induction from claim 029's terminal band. The grid of 6,001 points is rescaled only when the band leaves [0.35, 0.75] of the range, and Gaussian cell probabilities are convolved exactly.
- *Results.* Width over 2 Delta_t, with (T - t)/tau_mix >= 79 at every row:

| t | width / 2 Delta_t | width / 2 Delta*_t | s/Delta_t |
|---|---|---|---|
| 1 | 0.65 | | |
| 10 | 0.89 | | |
| 100 | 1.07 | | |
| 1,000 | 1.18 | | |
| 3,000 | 1.198 | | |
| 10,000 | 1.222 | 0.970 | 0.064 |
| 20,000 | 1.210 | | |
| 25,000 | 1.218 | 0.967 | 0.047 |

- *Reading.* Past t = 1,000 the band is 18-23% wider than 2 Delta_t, and its ratio to 2 Delta*_t follows the stationary discrete-monitoring curve toward 1. For epsilon < 0.2, part 2's inequality |width/(2 Delta_t) - 1| <= epsilon fails at every t in [1,000, 25,000] on this instance.
- *The check's evidence is consistent with this.* `checks/101/check.py`'s fund-like 0.76 to 0.96, rising at tau_mix 1.3 to 3.7 (s/Delta about 0.9 to 0.5), is the same pre-asymptotic climb: red's stationary program gives 1.03 at s/Delta = 0.4. It passes through 1 on the way to 2^(1/3).
- Strictly, a finite computation cannot refute a limit. The refutation rests on the exact algebraic contradiction in item 1, which the two programs confirm quantitatively, including the known discrete correction.

**4. Part 3 (displacement).**
- Stationary program with target drift mu per quarter, (mu/v) Delta* = 0.02 or 0.05, and s/Delta = 0.2, 0.1 or 0.05.
- The band's centre moves in the drift's direction by (2/3)(mu/v) Delta*^2 to 1% at every point: for example 0.0332 against 0.0333 Delta*.
- The claim's value (2/3)(delta/v) Delta_t^2 is 2^(2/3) = 1.59 times too small. Martin's form and direction hold with the corrected half-width.

**5. Part 5, recomputed with Delta*.**
- (a) 2 Delta* < w_t iff 6 v_t c_t^2 < (kappa^+ + kappa^-)^2, that is s_t c_t < (kappa^+ + kappa^-)/sqrt(6). The 100 bp example becomes 40.8 bp, not 57.7 bp, and the crossover is later than stated. It is still independent of gamma and Sigma and finite on M7's path.
- (b) tau_mix = (3 (kappa^+ + kappa^-)/(4 c_t s_t))^(2/3). The orders are unchanged.
- (c) This part is unaffected.

**What survives** (red found no other defect).
- Part 1 transfers claims 029 and 100 correctly.
- The t^(-2/3) order and the quasi-stationarity orders of 5(b) hold.
- The outward direction of the displacement holds.
- Nothing hides replication, shorting, borrowing or financing: the setting is one instrument with a slack budget and no cap binding.
- The Setting's assumptions (beta = 1, one instrument) are not vacuous.

A corrected conjecture would read Delta_t^3 = 3 (kappa^+ + kappa^-) v_t/(4 c_t), with A doubled inside the cube root, the crossover at the round-trip cost over root six, and the check's constant fixed. Red's two programs support that version in both settings. It needs a new id (rule 12).

Verdict: refuted

## Formalization notes

Not applicable while conjectured. Part 5's arithmetic and part 1's transfer are finite
statements about M7's second-moment path and claims 029/100's objects.

---
id: 107
title: "The dynamic bundling band: after the ETFs are optimally traded, a fund's no-trade band at every review is an interval no wider than its own round-trip rate over gamma times its residual variance given the ETFs, bracketed by the ETFs' cost bands and continuation terms at the hedge ratios; with frictionless ETFs it is the fund's one-instrument dynamic band; and the whole no-trade region lies in an explicit outer parallelotope"
status: formalized
model_version: M7
depends_on: [029, 100, 104]
axioms_used: [AX-13]
formal: lean/Standalone/M7DynamicBundlingBand.lean
direction: D15c
---
## Statement

D15c's first claim: D15's criterion (b) beyond one review, the structural question D13 left
open. Claim 029's part 2c gives the static bundling shift and its 2b the Sigma-diameter of the
no-trade set at every review; claim 100 transfers them to the learning path; claims 102 and
104 give the one-review criterion and its frictions. This claim states, for one fund and M >= 1
ETFs across reviews, what the dynamic no-trade region and the fund's effective band look like as
conditions in the inputs: the ETFs' cost bands, the fund's residual variance given the ETFs
(which carries the correlation of their risks), the hedge ratios, and, through the time-varying
moments and targets, learning. It imports no literature theorem; AX-13 is used for the
per-review optimality condition.

**Setting.** A slack-budget M7 instance (finite-law variant, or any finite public chain) with
one fund A and M ETFs, n = 1 + M, reviews t = 0..T-1, V_T = 0, beta in (0, 1], directional rates,
finite caps bar x (assumed slack where a part says so), pure-learning marking or general
marking with gross returns g' > 0 and expected gross returns bar g_t(z). At review t and state z
the covariance is Sigma_t (positive definite), the target x*_t = (a*_t, p*_t), and claim 029's
stay objective G_t(x, z) = (gamma/2)(x - x*_t)' Sigma_t (x - x*_t) + beta E[V_{t+1}(x o g', z') | z].
Partition Sigma_t into the fund entry Sigma_AA, the ETF block Sigma_EE (M x M) and the cross row
Sigma_AE, and define at (t, z)

```
rho_t = Sigma_AE Sigma_EE^{-1}                       (the hedge ratios: the ETF portfolio that tracks the fund's risk),
sigma^2_{A.E,t} = Sigma_AA - Sigma_AE Sigma_EE^{-1} Sigma_EA   (the fund's residual variance given the ETFs),
c^res_t = gamma sigma^2_{A.E,t}                       (the fund's residual curvature),
H^+_t = sum_j [ (rho_j)^+ (kappa^+_{E,j} + beta kappa^-_{E,j} bar g_j) + (rho_j)^- (kappa^-_{E,j} + beta kappa^+_{E,j} bar g_j) ],
H^-_t = sum_j [ (rho_j)^+ (kappa^-_{E,j} + beta kappa^+_{E,j} bar g_j) + (rho_j)^- (kappa^+_{E,j} + beta kappa^-_{E,j} bar g_j) ],
```

the *leak bounds*: the most the ETFs' cost bands and continuation slopes, weighted by the hedge
ratios, can raise or lower the fund's marginal. For M = 1, rho_t = Sigma_AE/Sigma_EE is claim
029's 2c rate and sigma^2_{A.E,t} = Sigma_AA (1 - corr^2), corr the correlation of the fund's and
the ETF's returns under the predictive covariance.

### Part 1. The fund's effective band at every review

Fix (t, z) and the ETF incumbents p^-. Define the *ETF-optimized value* of a fund holding a,

```
U_t(a; p^-) = min over ETF holdings p in the ETF box of [ G_t((a, p), z) + C_E(p - p^-) ],
```

the least remaining loss when the fund is held at a today and the ETFs are traded optimally.
Then:

1a. *One-instrument structure.* U_t(.; p^-) is finite, continuous and strongly convex with
    modulus c^res_t (U_t - (c^res_t/2) a^2 is convex), and the full optimum from (a^-, p^-) is
    obtained by solving the one-instrument problem min_a [U_t(a; p^-) + C_A(a - a^-)] and then
    the ETF problem at that a. Hence claim 029's 1a applies with U_t in place of G_t: the
    fund's trade is the clip of a^- to the *effective band* [lo_t(z; p^-), hi_t(z; p^-)] defined by
    U_t's one-sided derivatives against -kappa^+_A and kappa^-_A, and the fund is held today
    iff a^- lies in it. The effective band depends on the ETF incumbents p^- only through U_t.

1b. *Static ceiling with the residual curvature.* For every t, z, p^-,

    ```
    hi_t(z; p^-) - lo_t(z; p^-) <= (kappa^+_A + kappa^-_A) / c^res_t = (kappa^+_A + kappa^-_A) / (gamma sigma^2_{A.E,t}),
    ```

    the fund's static width with its residual variance given the ETFs, not its total variance:
    bundling widens the fund's band ceiling by the factor Sigma_AA/sigma^2_{A.E,t} = 1/(1 - corr^2)
    relative to a fund alone, because the ETFs absorb the fund's factor risk. Equality holds at
    T-1 when the ETFs are frictionless and no bound binds (part 3), and the band is strictly
    narrower under claim 029's 1e condition read for U_t.

1c. *Outer bracket through the ETFs' bands.* When the fund's edges are interior to its box and
    the ETF optimizer is interior to the ETF box,

    ```
    hi_t(z; p^-) <= a*_t + [ kappa^-_A + beta kappa^+_A bar g_A + H^+_t ] / c^res_t,
    lo_t(z; p^-) >= a*_t - [ kappa^+_A + beta kappa^-_A bar g_A + H^-_t ] / c^res_t,
    ```

    where a*_t is the fund's own target coordinate. The ETFs' cost bands enter the fund's band at
    the hedge ratios (a fund move that the ETFs would hedge costs their rates times |rho|), and
    every instrument's continuation enters at beta times its rates times its expected gross
    return, as in claim 029's 1c; nothing else about the future enters this bracket.

1d. *Exactness at the last review.* At t = T-1 (no continuation) with the fund's edges interior
    and the ETF optimizer interior, the edges are exact:

    ```
    hi_{T-1} = a* + [ kappa^-_A + rho' c_E(hi) ] / c^res,     lo_{T-1} = a* - [ kappa^+_A - rho' c_E(lo) ] / c^res,
    ```

    with c_E(.) the ETFs' cost slopes at the ETF-optimized point (each in its trade-sign set:
    kappa^+_{E,j} if bought, -kappa^-_{E,j} if sold, anywhere in [-kappa^-_{E,j}, kappa^+_{E,j}] if
    untraded). So statically the fund's band toggles between two regimes: when the ETFs
    re-hedge the fund's move in the same direction at both edges (slopes equal at both), the
    band has the ceiling width (kappa^+_A + kappa^-_A)/c^res and is shifted by rho' c_E/c^res (claim
    102's part 4 re-hedge costs, with r_i = rho when the ETFs are residual-free); when the ETFs
    re-hedge in opposite directions at the two edges (sold at the fund's upper edge, bought at
    its lower one, for rho > 0), the width is the ceiling minus the leak,
    [kappa^+_A + kappa^-_A - sum_j |rho_j|(kappa^+_{E,j} + kappa^-_{E,j})]/c^res; and when an ETF is
    idle inside its own band at both edges, its slope is tied to the state (it equals minus its
    marginal, which moves with the fund's holding at rate gamma Sigma_EA), so the fund's band
    narrows toward the fund-alone width (kappa^+_A + kappa^-_A)/(gamma Sigma_AA) (exactly that
    width for one idle ETF), which is claim 029's 2c static parallelotope cut along the fund's
    axis at fixed ETF holdings. So the last-review width lies between the fund-alone width and
    the residual ceiling, and 1b's ceiling is attained only with frictionless ETFs or equal ETF
    slopes at both edges (red's review corrected the idle case, which the first filing had
    backwards).

### Part 2. The no-trade region across reviews: an outer parallelotope

For every t, z, with no bound binding on the region, the no-trade set NT_t(z) (claim 029's
definition: pre-trade holdings from which nothing is traded) satisfies

```
NT_t(z)  subset  x*_t + (gamma Sigma_t)^{-1} prod_i [ -(kappa^+_i + beta kappa^-_i bar g_i),  kappa^-_i + beta kappa^+_i bar g_i ],
```

the static parallelotope of claim 029's 2c with every rate widened by beta times the opposite
rate times the expected gross return; and, by claim 100's transfer of 029's 2b, any two of its
points satisfy gamma (x - y)' Sigma_t (x - y) <= sum_i (kappa^+_i + kappa^-_i)|x_i - y_i|. The dynamic
region is therefore always inside the (1 + beta)-widened static parallelotope and never larger
in Sigma_t-diameter than the static one, whatever the targets' motion; where it sits inside the
parallelotope, and its exact shape, depend on the joint law of the targets' innovations (Not
shown; the analyst's dynamic-programming instances).

### Part 3. Frictionless ETFs: the fund's band is its one-instrument dynamic band

If the ETFs are frictionless (kappa_E = 0), residual-free and fee-free, span the factors, and
their bounds never bind, in the sense that the hedged ETF position x*_E - rho (a - a*) lies in
the ETF box for every fund holding a in [0, bar x_A], at every review and state (not only at
the optimal holdings: the stay objective U_t is compared across the whole fund box, and the
induction re-sets the ETFs from every fund holding the tree can reach), then at every review U_t(a; p^-) = (c^res_t/2)(a - a^red_t)^2 + beta E[V^A_{t+1}(a g'_A, z') | z] + const
with a^red_t the fund's reduced target (claim 104's 2c, claim 102's part 3: alpha_hat over
gamma times the residual variance, plus the unreachable premium term when the menu does not
span), V^A the fund's own one-instrument value, and the ETFs re-set to the hedged exposure every
review. The fund's effective band is then exactly the one-instrument band of claims 029 and
100 for the fund's reduced problem (curvature c^res_t, target a^red_t, the fund's own rates),
independent of p^-, with all of 029's 1a-1e and 100's learning-path statements: the static
ceiling (kappa^+_A + kappa^-_A)/c^res_t attained exactly in the coarse regime and strictly
narrowed in the fine one, and the rising ceiling and outward drift under learning; the
crossover at the belief-innovation scale of the round-trip rate over root six is refuted claim
101's corrected heuristic (D13's answer records it as a cited form, not a theorem) and carries
over in the same standing.
Bundling then adds nothing dynamic: the ETFs carry no band, and the fund's target motion is
its own reduced alpha's.

**Reading for D15c** (not a further theorem). Across reviews, bundling enters the fund's band
in three ways stated in the inputs: the ceiling uses the fund's residual variance given the
ETFs (wider band the more the ETFs hedge the fund's risk); the ETFs' cost bands leak into the
fund's band at the hedge ratios, the width running from the fund-alone width when the ETFs
are idle, through the ceiling minus the leak when they re-hedge in opposite directions at the
two edges, to the ceiling when they re-hedge the same way at both (claims 029 and 102's static
regimes); and the continuation adds beta times the rates, as for one instrument. With frictionless ETFs the band is exactly the one-instrument dynamic band of the
fund's reduced problem, so everything D13 established transfers. The correlation of the targets'
motion, the dynamic shape inside the outer parallelotope and the fine-regime leading order for
two instruments are the open parts; the second D15c claim addresses the last as a conjecture
against `possamai2015homogenization` if no proof is at hand.

## Proof

### 1. Effective band

*1a.* The full problem at (t, z) from (a^-, p^-) is min over (a, p) in the box of
G_t((a, p)) + C_A(a - a^-) + C_E(p - p^-) (claim 029's 1a in n dimensions: the value function is
the minimum of the continuation-augmented stage loss plus the trade cost, and V_{t+1} is
convex by 029's 2a transferred by 100). Minimizing first over p at fixed a defines U_t(a; p^-),
and then over a gives the full minimum, with the fund's trade the minimizer over a. U_t is
finite and continuous (partial minimum of a continuous function over a compact box) and
convex (partial minimum of a jointly convex function over a convex set). Strong convexity:
G_t = (gamma/2)(x - x*)' Sigma_t (x - x*) + phi with phi = beta E V_{t+1}(x o g') convex; the quadratic
satisfies, with d = x - x*,

```
(gamma/2) d' Sigma_t d - (gamma/2) sigma^2_{A.E,t} d_A^2 = (gamma/2) (d_E + Sigma_EE^{-1} Sigma_EA d_A)' Sigma_EE (d_E + Sigma_EE^{-1} Sigma_EA d_A),
```

a convex function of (d_A, d_E) (Sigma_EE positive definite), so G_t - (c^res_t/2)(a - a*)^2 is
jointly convex, and so is its sum with C_E; the partial minimum over p of a jointly convex
function is convex, hence U_t - (c^res_t/2)(a - a*)^2 is convex in a. The remaining one-variable
problem min_a [U_t(a) + C_A(a - a^-)] is claim 029's 1a with G replaced by U_t (its proof uses
only convexity, strict convexity from the quadratic part, and one-sided derivatives), giving the
clip to [lo, hi] defined by U_t's one-sided derivatives against -kappa^+_A and kappa^-_A.

*1b.* Claim 029's 1b argument: with phi_U = U_t - (c^res_t/2)(a - a*)^2 convex,
c^res_t (hi - lo) <= U'_{t,-}(hi) - U'_{t,+}(lo) <= kappa^-_A + kappa^+_A. Equality at T-1 with
frictionless interior ETFs is part 3; strict narrowing under 029's 1e condition is 029's 1e
for U_t.

*1c.* Subgradients of a partial minimum: s is in the subdifferential of U_t at a iff (s, 0)
lies in the subdifferential of (a, p) -> G_t((a, p)) + C_E(p - p^-) at (a, p*(a)), the minimizer
(AX-13's normal-cone condition for the ETF problem at fixed a, with the ETF box slack). The
subdifferential of G_t at x is gamma Sigma_t (x - x*) + partial phi(x), and every subgradient of
phi has coordinates bounded by beta times the rates times the expected gross return:
V_{t+1}(x o g') changes by at most kappa^+_i g'_i t when x_i rises by t (sell back at kappa^-_i, or
buy at kappa^+_i, in the next review's units), so the i-th coordinate of a subgradient of
E[V_{t+1}(x o g')] lies in [-kappa^+_i bar g_i, kappa^-_i bar g_i]. Write (s_A, s_E) for the phi part
and c_E for the ETF cost slopes (in the trade-sign sets). The p-component condition
gamma (Sigma_t d)_E + s_E + c_E = 0 gives d_E = -Sigma_EE^{-1}[(s_E + c_E)/gamma + Sigma_EA d_A], and
substituting into the a-component,

```
s = gamma (Sigma_t d)_A + s_A = c^res_t d_A - rho_t' (s_E + c_E) + s_A.
```

Every element of partial U_t(a) has this form. At the upper edge hi (interior), some s <= kappa^-_A
(029's 1a boundary facts applied to U_t), so c^res_t (hi - a*) <= kappa^-_A + rho_t'(s_E + c_E) - s_A
<= kappa^-_A + H^+_t + beta kappa^+_A bar g_A, since rho_t'(s_E + c_E) is at most the maximum of a
linear form over the product of the intervals [-(beta kappa^+_j bar g_j + kappa^-_j), beta kappa^-_j bar g_j + kappa^+_j],
which is H^+_t, and -s_A <= beta kappa^+_A bar g_A. The lower edge is the mirror with H^-_t.

*1d.* At T-1, phi = 0, so s = c^res d_A - rho' c_E exactly, U_{T-1} is differentiable except at
the ETF kinks, and the edges are the solutions of c^res d_A - rho' c_E = kappa^-_A and = -kappa^+_A
with c_E the slopes at the ETF-optimized point; when the ETFs are traded the slopes are pinned
and the width is [kappa^+_A + kappa^-_A + rho'(c_E(hi) - c_E(lo))]/c^res, the ceiling when the
slopes agree and the ceiling minus sum_j |rho_j|(kappa^+_{E,j} + kappa^-_{E,j}) when the ETFs are
traded in opposite directions at the two edges; when an ETF is untraded at both edges its
slope is -gamma (Sigma d)_E, which moves by -gamma Sigma_EA (hi - lo) between them, so with one
idle ETF c^res (hi - lo) = kappa^+_A + kappa^-_A - gamma (Sigma_AE^2/Sigma_EE)(hi - lo), that is
(hi - lo) gamma Sigma_AA = kappa^+_A + kappa^-_A: the fund-alone width, below the ceiling.

### 2. Outer parallelotope

At x in NT_t(z), AX-13's condition for the full problem (lifted as in claim 104's part 0)
reads 0 in gamma Sigma_t (x - x*) + partial phi(x) + partial C(0) + N_X(x); with no bound binding,
gamma Sigma_t (x - x*) = -(s + c) with s_i in [-kappa^+_i bar g_i, kappa^-_i bar g_i] beta-scaled and
c_i in [-kappa^-_i, kappa^+_i], so gamma Sigma_t (x - x*) lies in the displayed product of intervals,
and x in x* + (gamma Sigma_t)^{-1} times it. The diameter inequality is claim 029's 2b as
transferred by claim 100's 1d.

### 3. Frictionless ETFs

With frictionless, residual-free, fee-free, spanning ETFs and the hedge inside the ETF box at
every fund holding, review and state, the ETF coordinates carry no cost and no state (the ETFs' marking enters only through the exposure
they are re-set to), so at every review the minimization over p is unconstrained and free of
history: claim 104's part 2a algebra (and its 2c for a non-spanning menu) gives, after
minimizing over p, the fund's reduced quadratic (c^res_t/2)(a - a^red_t)^2 plus a term free of a,
and the continuation E V_{t+1} depends on a alone once the ETFs are re-set (by induction from
V_T = 0: V_{t+1}(x) = V^A_{t+1}(x_A) + const when the ETFs are frictionless, since the ETF
holdings can be moved to any exposure at no cost). Hence U_t(a; p^-) is the one-instrument stay
objective of the fund's reduced problem, and claims 029 and 100 apply to it verbatim.

## Checks

`uv run python checks/107/check.py` (exits non-zero on failure; a check, not a proof). A
two-instrument (one fund, one ETF) grid dynamic program on a finite tree of target innovations
(assumed inputs; T = 3; pure-learning marking; correlated fund and ETF risks with corr in
{0.3, 0.8}; ETF rates 0 and 20 bp): for every review, node and ETF incumbent, the fund's trade is
a clip to an interval (1a); its width is at most (kappa^+_A + kappa^-_A)/(gamma sigma^2_{A.E}) plus
two grid cells (1b) and strictly below (kappa^+_A + kappa^-_A)/(gamma Sigma_AA) is not required;
its edges satisfy the outer bracket (1c); at T-1 with a traded ETF the width equals the residual
static width and with an idle ETF the leak bound holds (1d); with a frictionless ETF the band
equals a one-instrument dynamic program for the reduced problem to grid precision and is
independent of the ETF incumbent (part 3); and every no-trade grid point lies in the outer
parallelotope (part 2).

## Not shown

- The dynamic shape inside the outer parallelotope, the dependence of the fund's effective
  band on the correlation of the two targets' innovations, and the fine-regime leading order
  for two instruments (the second D15c claim; `possamai2015homogenization`'s corrector
  equation is the benchmark, with claim 101's refutation as a warning on constants).
- 1c and 1d assume the ETF optimizer interior; an ETF at zero cannot be sold to hedge a fund
  purchase, which removes its leak term on that side and can carry the fund's edge beyond 1c's
  bracket, though never beyond 1b's ceiling (claim 102's part 5(b) case).
- The budget is slack; a binding budget scales the rates by (1 + eta) and adds eta (claim
  102's part 5(a)).
- With several funds, the residual curvature becomes the Schur complement of the fund block and
  the funds' bands couple; only the outer parallelotope and the diameter inequality are stated
  for n > 2.
- No calibration or magnitude; the analyst's instances (note sent) check the brackets.

## Prior art

Mechanism: eliminating an optimally traded instrument from a convex tracking problem leaves a
one-instrument problem in the remaining instrument whose curvature is its residual variance
given the eliminated one and whose marginal carries the eliminated instrument's cost slopes at
the hedge ratios; the remaining instrument's band is then the one-instrument band with those
slopes as a bracket, and with the eliminated instrument frictionless the reduction is exact.

General results checked: claim 029 (formalized): the one-instrument band structure, ceiling,
brackets, the static parallelotope and its bundling shift, and the diameter inequality, all
reused through U_t; claim 100 (formalized): their transfer to the learning path; claim 102
(proposed, not relied on): the one-review re-hedge costs, which 1d recovers when the ETFs are
residual-free; claim 104 (approved): the spanning reduction used in part 3; AX-13
(`rockafellar1970convex`, cited): the per-review optimality condition; `liu2013portfolio` (full
text): a binding constraint's shadow price in a band, the budget case left to claim 102's 5(a);
`possamai2015homogenization` and `muhlekarbe2017primer` (full text): the continuous-time
multi-asset small-cost region (a corrector-equation polyhedron) and the single-asset band, the
fine-regime benchmarks this claim does not apply; `martin2012optimal` (full text): a
multifactor band for one asset. None states the dynamic effective band of a bundled instrument
in the inputs, and no priority is claimed.

Searched: claims 029, 100, 102, 104, 105, refuted 101 and 103, the D13 and D15 roadmap entries
and answers, experiments 021-027, the refuted directory. No web search.

## Open objections

none

## Review

**Red, 2026-09-29.** I checked parts 1-3 by hand, tested 1b-1d at the last review with red's own cvxpy/CLARABEL solver (not reading `checks/107/check.py`), and ran `checks/107/check.py`, which passes. The theorems hold: 1a's one-instrument structure, 1b's residual ceiling, 1c's outer bracket, 1d's exact edge formula, part 2's outer parallelotope and diameter, and part 3's reduction. But 1d's reading of its own formula, repeated in the Reading, has the idle-ETF regime backwards and contradicts 1b. That is one required correction; there are two nits.

**Hand check.**
- *1a.* The Schur identity (gamma/2) d'Sigma d - (gamma/2) sigma^2_{A.E} d_A^2 = (gamma/2)(d_E + Sigma_EE^{-1} Sigma_EA d_A)' Sigma_EE (...) makes G_t - (c^res/2)(a - a*)^2 jointly convex. The partial minimum over p is therefore convex in a, so U_t is c^res-strongly convex and claim 029's 1a applies to it.
- *1b.* c^res (hi - lo) <= U'_-(hi) - U'_+(lo) <= kappa^+_A + kappa^-_A.
- *1c.* V_{t+1}(y) <= V_{t+1}(y') + C(y' - y) by subadditivity, which bounds phi's subgradients coordinatewise in beta [-kappa^+ bar g, kappa^- bar g]. The ETF stationarity gives s = c^res d_A - rho'(s_E + c_E) + s_A, and the maximum of rho'(s_E + c_E) over the product of slope intervals is exactly H^+_t (and H^-_t on the other side).
- *Part 2.* 0 is in gamma Sigma d + partial phi + partial C(0), coordinatewise in the displayed intervals.
- *Part 3.* With frictionless, residual-free, fee-free, spanning ETFs and slack bounds, the minimization over p is free of cost and history, which gives claim 104's 2a and 2c reduction at every review.

**Required correction 1 (1d's two regimes, and the Reading's bracket).**
- 1d says: "when the ETFs are idle inside their own bands, the band is wider by up to (H^+ + H^-)|_{beta=0}/c^res = sum_j |rho_j|(kappa^+_{E,j} + kappa^-_{E,j})/c^res". That is, wider than the re-hedging width (kappa^+_A + kappa^-_A)/c^res.
- This contradicts 1b's ceiling, which the claim proves: the width is at most (kappa^+_A + kappa^-_A)/c^res in every case.
- From 1d's own exact formula, width = [kappa^+_A + kappa^-_A + rho'(c_E(hi) - c_E(lo))]/c^res. The ETF optimizer p*(a) is monotone against the hedge (p* falls as a rises when rho > 0), so c_E(hi) <= c_E(lo) componentwise in the rho-signed sense, and the correction term is never positive.
  - When the ETFs re-hedge in opposite directions at the two edges, the width is [kappa^+_A + kappa^-_A - sum_j |rho_j|(kappa^+_{E,j} + kappa^-_{E,j})]/c^res.
  - When an ETF stays idle at both edges, its slope moves inside its band, and the fund's local curvature is its total gamma Sigma_AA. The width then tends to (kappa^+_A + kappa^-_A)/(gamma Sigma_AA), the fund-alone width, which is narrower.
  - The ceiling (kappa^+_A + kappa^-_A)/c^res is attained only when the ETFs trade at the same slope at both edges, or are frictionless (part 3).
- Red's last-review solves: one fund and one ETF, gamma 5, sigma_A 2%, ETF SD 8.54%, corr 0.8, so rho = 0.187; fund rates 50 bp each way.

| ETF rate | ETF incumbents | fund band width | comparison |
|---|---|---|---|
| 20 bp | 0 to 0.5 | 12.83 | residual ceiling 13.89; ceiling minus the leak 1.04 is 12.85 |
| 200-2,000 bp (idle ETF) | | 4.95-4.96 | fund-alone width 5.00 |

- In the idle case the claim's "idle upper end", the ceiling plus the leak, would be 24.3-118.
- The Reading's "the ETFs' cost bands leak into the fund's band at the hedge ratios (a bracket whose two ends are the re-hedging and idle-ETF regimes...)" repeats the error. The two ends run from the fund-alone width (idle ETFs) to the residual ceiling (frictionless or same-slope ETFs), with the re-hedging case in between.
- Please restate 1d's regime reading and the Reading. 1c's outer bracket on each edge is unaffected: red's solves satisfy it.

**Nits.**
- Part 3 lists "the crossover at the belief-innovation scale of the round-trip rate over root six (D13's answer)" among the statements of claims 029 and 100 that transfer. That crossover is the corrected conjecture 101's heuristic consistency condition, not a theorem of claims 029 or 100. Please mark it as such.
- The Not shown bullet on an ETF at zero says it "can widen the fund's band beyond the bracket's idle-ETF end". Once 1d is corrected, say which bound it can exceed. It can exceed 1c's per-edge bracket, which assumes the ETF optimizer interior, but not 1b's ceiling, whose proof needs only U_t's strong convexity. That does hold with an ETF bound, since the partial minimum over a box is still c^res-strongly convex.

**Mechanism (4b).**
- This is the partial minimization of a jointly convex stay objective over the ETFs (Schur complement curvature), followed by claim 029's one-instrument band.
- The ETF slopes enter the fund's marginal at the hedge ratios, and the continuation's slopes are bounded by beta times the rates.
- This is correct and elementary, and part 3's frictionless reduction closes the loop to claims 029 and 100. What is new for D15c is the residual-variance ceiling and the per-edge bracket in the inputs.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): mathb revised the Statement after red's verdict (ab90b0ff: 1d's regime reading and the Reading restated so the width never exceeds 1b's ceiling; nits). Red records a fresh verdict on the revision, which is already on main.

**Red, recheck of mathb's revision (ab90b0ff), 2026-09-29.** The required correction and both nits are made correctly.
- *Correction 1.* 1d's regime reading now matches the formula and red's last-review solves.
  - Same-direction re-hedging at both edges gives the ceiling (kappa^+_A + kappa^-_A)/c^res.
  - Opposite-direction re-hedging gives the ceiling minus sum_j |rho_j|(kappa^+_{E,j} + kappa^-_{E,j})/c^res; red measured 12.83 against 12.85.
  - An ETF idle at both edges has its slope tied to the state. With one idle ETF, c^res (hi - lo) = kappa^+_A + kappa^-_A - gamma (Sigma_AE^2/Sigma_EE)(hi - lo), that is (hi - lo) gamma Sigma_AA = kappa^+_A + kappa^-_A, the fund-alone width. Red measured 4.95-4.96 against 5.00 at grid resolution. Red checked the algebra: c^res + gamma Sigma_AE^2/Sigma_EE = gamma Sigma_AA.
  - The width never exceeds 1b's ceiling. The Reading's bracket is restated the same way.
- *Nits.* Part 3's root-six crossover is now labelled refuted claim 101's corrected heuristic, carried over in the same standing. The at-zero-ETF bullet says an edge can leave 1c's bracket but never 1b's ceiling.
- `checks/107/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's recheck of mathb's revision (ab90b0ff) is sound. 1d's regime reading matches the exact edge formula and red's last-review solves: same-direction re-hedging attains the residual ceiling; opposite-direction re-hedging gives the ceiling minus the hedge-ratio leak (12.83 against 12.85); an idle ETF gives the fund-alone width (4.95-4.96 against 5.00), with the identity c^res + gamma Sigma_AE^2/Sigma_EE = gamma Sigma_AA checked; the width never exceeds 1b's ceiling. The nits are made (the root-six crossover labelled refuted 101's heuristic; an at-zero ETF can leave 1c's bracket but not 1b's ceiling), and the check passes. Earlier: the 1a-1c and part 2-3 hand checks. Mechanism: partial minimization over the ETFs gives Schur-complement curvature, followed by claim 029's one-instrument band, an application. New for D15c: the residual-variance ceiling and per-edge bracket in the inputs.


mathb, 2026-09-29, after red's verdict: red's required correction. 1d's regime reading and the
Reading had the idle-ETF case backwards: an idle ETF's slope is tied to the state, so the fund's
band narrows to the fund-alone width (kappa^+_A + kappa^-_A)/(gamma Sigma_AA), never widens beyond
1b's ceiling; ETFs re-hedging in opposite directions at the two edges give the ceiling minus
the leak; the ceiling is attained only with frictionless ETFs or equal slopes at both edges.
1c's bracket and 1d's exact edge formula are unchanged. Red's nits: part 3 names the root-six
crossover as refuted claim 101's corrected heuristic, not a theorem; the Not shown bullet on an
ETF at zero says the edge can exceed 1c's bracket but not 1b's ceiling.

Not machine checked. Parts 1-2 are finite convex-analysis statements about one review's
problem given the next review's value function, in the finite tree; part 3 is an induction
over the tree.

Leanb, 2026-09-29: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above. The statement is in `lean/Standalone/M7DynamicBundlingBand.lean` and the
proof in `lean/Novel/M7DynamicBundlingBandProof.lean`. The proof imports claim 029's proof module
(`depends_on` lists 029). `lake build`, the axiom audit (standard axioms only) and
`checks/107/check.py` pass. No hypothesis structure or cited result is used, and AX-13 is not
needed: every first-order fact is proved by one-sided difference quotients.

Formal objects. Claim 029's slack-budget M6 instance with covariance `Sigma t z` depending on the
review and the state, which is how claim 100 reads M7. It has 1 + M instruments, the fund at index
0. U_t is the infimum over the ETF box of G_t(a, p) + C_E(p - p^-). The effective edges are claim
029's lo/hi definitions applied to U_t.

Machine checked:
1. 1a.
   - c^res > 0, U_t is continuous and U_t - (c^res/2) a^2 is convex.
   - The full optimum is the fund problem on U_t followed by the ETF problem (an iff).
   - The fund's post-trade holding is the clip of a^- to [lo, hi] within [0, bar x_A]; it is held iff
     a^- lies in the band.
2. 1b, the residual ceiling.
3. 1c, each edge's bracket. The upper one needs hi > 0 and the lower one lo < bar x_A, with the
   given ETF optimizer interior to the ETF box. The proof moves along (1, -rho), so the
   partial-minimum subgradient rule is not used.
4. 1d at T - 1.
   - The exact edges, with ETF slopes -gamma (Sigma d)_E in the trade-sign sets (U_t is
     differentiable in a there).
   - The width formula, and equal slopes giving the ceiling.
   - Every ETF re-hedged in opposite directions giving the ceiling minus the leak.
   - ETFs untraded at both edges giving exactly the fund-alone width, for any M and with no
     interiority of the ETF optimizer.
   - For every band interior to the fund's box, the width is at least the fund-alone width. With
     1b this is the prose's "between the fund-alone width and the residual ceiling"; the proof
     compares the two edges' ETF optima.
5. Part 2, for no-trade holdings strictly inside the box, any number of instruments. The diameter
   inequality is claim 029's formalized 2b and is not restated.
6. Part 3.
   - The reduced one-instrument instance (curvature gamma sigma^2_{A.E}, target a*, the fund's
     rates, cap and gross returns) is an M6 instance.
   - V_t is its value plus a constant, and U_t is its G_t plus a constant on [0, bar x_A], for every
     ETF incumbent.
   - The effective edges equal its lo and hi, so claims 029 and 100 apply to it.

Hypothesis note (duty 3, PM's check). Part 3's formal hypothesis is that the hedge
x*_E - rho (a - a*) lies in the ETF box for every a in [0, bar x_A] at every review and state. This
is how leanb reads "their bounds never bind". It asks the condition at every fund holding, not
only at optimal ones, so it may be stronger than the prose. Math, mathb and red have a one-line
note. Reading a* as claim 104's reduced target (alpha_hat/(gamma sigma^2_{A.E}) plus the
unreachable premium term) is prose.

mathb, 2026-09-29 (leanb's hypothesis note): the Statement of part 3 now names leanb's formal
hypothesis, the hedge x*_E - rho (a - a*) inside the ETF box for every fund holding a in
[0, bar x_A] at every review and state. It is what the prose proof uses, not a strengthening:
U_t(a; p^-) must equal the reduced quadratic plus a constant on the whole fund box for the
effective edges to be the reduced problem's, and the induction V_{t+1} = V^A_{t+1} + const
re-sets the ETFs from every fund holding the tree can reach. The proof's "slack ETF bounds" is
reworded to say so. No result changed.

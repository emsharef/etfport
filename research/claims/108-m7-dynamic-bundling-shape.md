---
id: 108
title: "The dynamic shape of the bundling band: at the last review the fund's edges are exact medians, in the ETF incumbent, of the idle line and the two re-hedge levels, bending over an interval as long as the ETF's residual static width; at every review they are monotone in the ETF incumbent with the sign of the covariance, so the no-trade region is the intersection of two monotone bands inside the outer parallelotope; with a frozen ETF the fund's band is the one-instrument band of the idle target, through whose innovation law, of variance v^idle, the targets' correlation enters; and the last review is free of the innovation law"
status: formalized
model_version: M7
depends_on: [029, 100, 107]
axioms_used: [AX-14]
formal: lean/Standalone/M7DynamicBundlingShape.lean
direction: D15c
---
## Statement

D15c's second claim: the shape of the dynamic no-trade region for one fund and one ETF inside
claim 107's outer parallelotope, as functions of the inputs. Claim 107 gave the fund's
effective band at every review (an interval in the fund's incumbent for each ETF incumbent),
its residual-variance ceiling and its bracket. This claim says how that band, and the ETF's,
move with the other instrument's holding: exactly at the last review, monotonically at every
review; what a frozen ETF does to the fund's band (the idle regime as a theorem, with the
targets' innovation correlation entering through the idle target's innovation law, whose
variance is v^idle); and that the innovation law
is absent from the last review. The correlation's effect at earlier reviews is a stated
conjecture (Reading), supported by experiments 038-039 and not claimed.

**Setting.** Claim 107's setting with M = 1: a slack-budget M7 instance (finite-law variant, or
any finite public chain) with one fund A and one ETF E, reviews t = 0..T-1, V_T = 0,
beta in (0, 1], directional rates kappa^+_A, kappa^-_A, kappa^+_E, kappa^-_E >= 0, finite caps
bar x_A, bar x_E, strictly positive gross returns g' > 0 (pure-learning marking, g' = 1, where a
part says so). At review t and public state z the covariance is Sigma_t(z) (positive definite,
entries Sigma_AA, Sigma_AE, Sigma_EE), the targets are (a*_t, p*_t)(z), and claim 029's stay
objective is

```
G_t((a, p), z) = (gamma/2) (a - a*_t, p - p*_t) Sigma_t (a - a*_t, p - p*_t)' + beta E[ V_{t+1}((a g'_A, p g'_E), z') | z ],
V_t((a, p), z) = min over (a', p') in the box of [ C_A(a' - a) + C_E(p' - p) + G_t((a', p'), z) ],
```

with C_A(u) = kappa^+_A u^+ + kappa^-_A u^-, C_E likewise. Write (claim 107's objects and one new
one)

```
rho_t = Sigma_AE/Sigma_EE       (the ETF hedge ratio: the ETF position that tracks the fund's risk),
rho_{A,t} = Sigma_AE/Sigma_AA   (the fund-side hedge ratio: claim 029's 2c bundling-shift rate),
c^res_t = gamma Sigma_AA (1 - corr^2) = gamma (Sigma_AA - Sigma_AE^2/Sigma_EE)   (the fund's residual curvature),
c^res_{E,t} = gamma Sigma_EE (1 - corr^2)                                        (the ETF's residual curvature),
```

corr the correlation of the two returns under Sigma_t. U_t(a; p^-, z) is claim 107's
ETF-optimized value, min over p in the ETF box of G_t((a, p), z) + C_E(p - p^-), and
[lo_t(z; p^-), hi_t(z; p^-)] the fund's effective band (claim 029's 1a applied to U_t: the fund
is held today iff its incumbent lies in it). Symmetrically, for a fund holding a (post-trade),
the ETF's band given a is claim 029's band [lo^E_t(z; a), hi^E_t(z; a)] for the one-instrument
stay objective p -> G_t((a, p), z), against -kappa^+_E and kappa^-_E. The dynamic no-trade region
is NT_t(z) = {(a, p) in the box : the full optimum from (a, p) is (a, p)}. All bands are read
at the pre-trade holdings after marking. Fix (t, z) and drop the subscripts where no confusion
arises.

### Part 1. The last review: exact edges in the ETF incumbent

At t = T-1 (no continuation), for every ETF incumbent p^- at which the ETF box does not bind
at the fund's edges (the ETF optimizer at a = lo and at a = hi lies strictly inside
(0, bar x_E)), the fund's edges are the medians of three numbers: the *idle line*, the fund's
band edge when the ETF stays at p^- (claim 029's 2c static shift), and the two *re-hedge
levels*, the edges when the ETF is bought, respectively sold, at the fund's edge (claim 107's
1d values):

```
lo_{T-1}(p^-) = median( lo^b, lo^idle(p^-), lo^s ),     hi_{T-1}(p^-) = median( hi^b, hi^idle(p^-), hi^s ),

lo^idle(p^-) = a* - rho_A (p^- - p*) - kappa^+_A/(gamma Sigma_AA),    hi^idle(p^-) = a* - rho_A (p^- - p*) + kappa^-_A/(gamma Sigma_AA),
lo^b = a* - (kappa^+_A - rho kappa^+_E)/c^res,    lo^s = a* - (kappa^+_A + rho kappa^-_E)/c^res,
hi^b = a* + (kappa^-_A + rho kappa^+_E)/c^res,    hi^s = a* + (kappa^-_A - rho kappa^-_E)/c^res,
```

each median clipped to [0, bar x_A] (the edge is that clip when the median falls outside the
fund's box). Consequences, for Sigma_AE > 0 (mirror them in p^- for Sigma_AE < 0; for
Sigma_AE = 0 the three numbers coincide and the edges do not depend on p^-):

1a. *The bend.* Each edge is a continuous nonincreasing function of the ETF incumbent: flat at
    its bought level for small p^- (the ETF is bought at the fund's edge), falling along the
    idle line with slope -rho_A = -Sigma_AE/Sigma_AA over an interval of ETF incumbents of
    length exactly

    ```
    (lo^b - lo^s)/rho_A = (hi^b - hi^s)/rho_A = (kappa^+_E + kappa^-_E)/c^res_E,
    ```

    the ETF's own residual static width (claim 107's 1b ceiling for the ETF), and flat at its
    sold level beyond. The fund's edge therefore moves with the ETF's holding only while the
    ETF is idle at that edge, and then one for one at the bundling-shift rate.

1b. *Widths by regime, in p^-.* The width hi_{T-1}(p^-) - lo_{T-1}(p^-) is the residual
    ceiling (kappa^+_A + kappa^-_A)/c^res where both edges sit on their bought levels or both on
    their sold levels; the fund-alone width (kappa^+_A + kappa^-_A)/(gamma Sigma_AA) where both
    are on the idle line; the ceiling minus the leak, [kappa^+_A + kappa^-_A - rho (kappa^+_E + kappa^-_E)]/c^res,
    where the lower edge is on its bought level and the upper on its sold level; and between
    these in the mixed cases. This is claim 107's 1d with the regime read off p^-.

1c. *No trade region at the last review.* NT_{T-1}(z) is claim 029's 2c static set (the
    parallelotope x* + (gamma Sigma)^{-1} [-kappa^+_A, kappa^-_A] x [-kappa^+_E, kappa^-_E] where no
    bound binds); 1a-1b describe the fund's band outside it, where the ETF trades.

### Part 2. Every review: monotone edges and the intersection of two monotone bands

Assume Sigma_AE,t(z) >= 0 at every (t, z) (the fund and the ETF positively correlated along
the whole tree) and g' > 0. Then for every t < T and z:

2a. *Cross-monotone values.* V_t(., z) has increasing differences in (a, p) on the nonnegative
    quadrant: for a_1 <= a_2 and p_1 <= p_2,
    V_t(a_2, p_2) - V_t(a_1, p_2) >= V_t(a_2, p_1) - V_t(a_1, p_1). So do G_t(., z) on the box
    and the ETF-optimized value U_t(a; p^-, z) in (a, p^-).

2b. *Monotone fund edges.* lo_t(z; p^-) and hi_t(z; p^-) are nonincreasing in p^-: a larger ETF
    holding lowers both edges of the fund's band, at every review, whatever the ETF's rates,
    the horizon or the innovation law.

2c. *Monotone ETF edges.* lo^E_t(z; a) and hi^E_t(z; a) are nonincreasing in the fund holding a.

2d. *The region.* NT_t(z) = { (a, p) in the box : lo_t(z; p) <= a <= hi_t(z; p) and
    lo^E_t(z; a) <= p <= hi^E_t(z; a) }, the intersection of a band in a with nonincreasing
    edges in p and a band in p with nonincreasing edges in a; it lies in claim 107's outer
    parallelotope where no bound binds (claim 107's part 2).

If instead Sigma_AE,t(z) <= 0 at every (t, z), replace "increasing differences" by "decreasing
differences" and "nonincreasing" by "nondecreasing" throughout. If Sigma_AE,t(z) = 0 at every
(t, z), the values are sums of one-instrument values and no edge depends on the other
instrument. The sign is that of the covariance under the predictive covariance, an input.

### Part 3. Frozen ETF: the idle regime as a theorem

Let the ETF be frozen (it cannot trade; equivalently kappa^+_E = kappa^-_E = +infinity) at a
holding p_0, under pure-learning marking. Then the fund's problem at every (t, z) is claim
029's one-instrument M6 problem (with claim 100's reading of M7's state-dependent covariance)
with curvature gamma Sigma_AA,t(z), the fund's own rates and cap, and the *idle target*

```
a^idle_t(z) = a*_t(z) - rho_{A,t}(z) (p_0 - p*_t(z)),
```

so its band [lo_t(z; p_0), hi_t(z; p_0)] is claim 029's band for that problem, with 029's 1a-1e
verbatim: the clip structure, the static ceiling (kappa^+_A + kappa^-_A)/(gamma Sigma_AA), the
edge brackets in beta and the rates, and the coarse and fine regimes in the target's
innovations. Under a constant Sigma, with target innovations (a*_{t+1} - a*_t, p*_{t+1} - p*_t)
of variances v_A, v_E and correlation r, the idle target's innovation is
Delta a* + rho_A Delta p*, of variance

```
v^idle = v_A + rho_A^2 v_E + 2 rho_A r sqrt(v_A v_E),
```

increasing in r when rho_A > 0 and decreasing when rho_A < 0. The frozen-ETF band depends on
the targets' joint innovation law only through the law of Delta a* + rho_A Delta p*, so this is
the only way the targets' innovation correlation enters it; v^idle is that law's variance, and
the band is a function of v^idle alone only when the law is fixed by its variance (a Gaussian
or another scale family, or claim 029's fine-regime reading): two finite joint laws with the
same v_A, v_E and r can give different frozen bands. Claim 029's fine-regime statement applies
with v^idle in place of the one-instrument innovation variance; the
asymptotic order in v^idle is D15e's question (its one-instrument form is refuted claim 101's
corrected heuristic, D13's cited form, not a theorem). With a frictionless ETF, by contrast,
claim 107's part 3 gives the reduced one-instrument band with curvature c^res and target
innovation variance v_A, free of r.

### Part 4. The last review is free of the innovation law

lo_{T-1}(z; p^-), hi_{T-1}(z; p^-), the ETF's band and NT_{T-1}(z) depend on (t, z) only through
a*, p*, Sigma, the rates, the caps and the incumbents (part 1 and claim 029's 2c): no
innovation variance or correlation enters. For t < T-1 the innovation law enters V_t and U_t
only through E[V_{t+1}(., z') | z] (the definition), so any dependence of a band on the
targets' innovation correlation is a continuation effect.

**Reading for D15c** (not a further theorem; the conjecture is not claimed). The dynamic
region is not the static parallelotope shifted per instrument: at the last review the fund's
edge bends along the bundling-shift line over an ETF-incumbent interval as long as the ETF's
own residual width and is flat outside it, and at every review the boundaries of the region
are monotone in the other holding with the sign of the covariance. Bundling adds, dynamically,
the residual curvature and the leak (claim 107) and, through the ETF-idle states, the targets'
innovation correlation: part 3 is the frozen limit where it enters exactly through v^idle, and
claim 107's part 3 the frictionless limit where it does not enter. *Conjecture* (FINDINGS,
2026-09-29; experiments 038-039 and 039's addendum): at review t the fund's band is claim
029's band for U_t with the continuation's target-innovation variance a mixture of v^idle
(future review-states at which the ETF is idle at the fund's edges) and v_A (states at which
it re-hedges), weighted by their discounted probabilities along the tree from the post-trade
state; so r enters with the sign of rho_A r, not at all with one remaining review (part 4,
observed exactly on 3,444 pairs), and in the re-hedge regime in proportion to the future-idle
share (observed, Spearman +0.74). A proof would bound the continuation's second differences by
the regime probabilities. The fine-regime asymptotic order of the fund's band with one ETF
(a cube-root law in the mixture variance, against `possamai2015homogenization`'s corrector
equation, with claim 101's refutation as the warning on constants) is D15e's question, owned
by math, and no part of this claim.

## Proof

Throughout, "the box" is [0, bar x_A] x [0, bar x_E], a product of intervals, so it is closed under
the coordinatewise minimum (x ^ y) and maximum (x v y); so is the nonnegative quadrant.

### 1. The last review

Fix z and p^-, write a*, p*, Sigma for their values at (T-1, z), and let the ETF box be slack
as assumed. With V_T = 0, G(a, p) = (gamma/2)[Sigma_AA (a - a*)^2 + 2 Sigma_AE (a - a*)(p - p*) + Sigma_EE (p - p*)^2].

*The ETF optimizer.* For fixed a, p -> G(a, p) + C_E(p - p^-) is strictly convex, differentiable
except at p = p^-, with dG/dp = gamma [Sigma_AE (a - a*) + Sigma_EE (p - p*)]. Its minimizer is
p(a) = median( P_lo(a), p^-, P_hi(a) ) with

```
P_lo(a) = p* - rho (a - a*) - kappa^+_E/(gamma Sigma_EE),    P_hi(a) = p* - rho (a - a*) + kappa^-_E/(gamma Sigma_EE)
```

(claim 029's 1a at T-1 for the one-instrument problem in p: the clip of p^- to the band on
which dG/dp lies in [-kappa^+_E, kappa^-_E]); p(.) is continuous in a.

*U is differentiable with U'(a) = dG/da (a, p(a)).* For h > 0, using p(a) at a + h and p(a + h)
at a,

```
G(a+h, p(a+h)) - G(a, p(a+h)) <= U(a+h) - U(a) <= G(a+h, p(a)) - G(a, p(a)),
```

divide by h and let h -> 0: both bounds tend to dG/da (a, p(a)) = gamma [Sigma_AA (a - a*) + Sigma_AE (p(a) - p*)]
by continuity of p and of dG/da; the same for h < 0. So U'(a) exists and equals that value.

*U' is a median of three strictly increasing affine functions.* The map
p -> gamma [Sigma_AA (a - a*) + Sigma_AE (p - p*)] is affine and monotone (nondecreasing if
Sigma_AE >= 0, nonincreasing otherwise, constant if Sigma_AE = 0), and a monotone map sends the
median of three numbers to the median of their images. Hence

```
U'(a) = median( f_b(a), f_idle(a), f_s(a) ),
f_b(a) = gamma [Sigma_AA (a - a*) + Sigma_AE (P_lo(a) - p*)] = c^res (a - a*) - rho kappa^+_E,
f_s(a) = c^res (a - a*) + rho kappa^-_E,
f_idle(a) = gamma Sigma_AA (a - a*) + gamma Sigma_AE (p^- - p*),
```

using gamma Sigma_AA - gamma Sigma_AE rho = c^res and gamma Sigma_AE/(gamma Sigma_EE) = rho. Each
of f_b, f_s, f_idle is affine and strictly increasing (c^res > 0, gamma Sigma_AA > 0).

*Median-of-roots lemma.* If f_1, f_2, f_3 are continuous and strictly increasing on R with
roots r_1, r_2, r_3, then median(f_1, f_2, f_3) is continuous and strictly increasing (the
median is a monotone function of its arguments) and its unique root is median(r_1, r_2, r_3):
order the roots r_(1) <= r_(2) <= r_(3); at a = r_(2) one function is zero, one is >= 0 and one
is <= 0, so the median is 0.

*The edges.* By claim 107's 1a, lo = inf{a in [0, bar x_A) : U'(a) >= -kappa^+_A} and
hi = sup{a in (0, bar x_A] : U'(a) <= kappa^-_A}. Since U' is continuous and strictly increasing,
lo is the root of U' + kappa^+_A clipped to [0, bar x_A], and hi the root of U' - kappa^-_A clipped.
The roots of f_b + kappa^+_A, f_idle + kappa^+_A, f_s + kappa^+_A are lo^b, lo^idle(p^-), lo^s as
displayed, and those of f_b - kappa^-_A, f_idle - kappa^-_A, f_s - kappa^-_A are hi^b, hi^idle(p^-),
hi^s; the lemma gives the medians.

*1a.* For Sigma_AE > 0: lo^b - lo^s = rho (kappa^+_E + kappa^-_E)/c^res >= 0 and lo^idle is affine in
p^- with slope -rho_A < 0, so median(lo^b, lo^idle(p^-), lo^s) equals lo^b where lo^idle >= lo^b,
lo^idle(p^-) between, and lo^s where lo^idle <= lo^s: continuous, nonincreasing, with the
middle segment of length (lo^b - lo^s)/rho_A in p^-. Now
(lo^b - lo^s)/rho_A = rho (kappa^+_E + kappa^-_E) Sigma_AA/(c^res Sigma_AE) = (kappa^+_E + kappa^-_E)/(gamma Sigma_EE (1 - corr^2)),
using rho/rho_A = Sigma_AA/Sigma_EE and c^res = gamma Sigma_AA (1 - corr^2). The same for hi. The
regimes: on the bought segment p^- < P_lo(lo), so the ETF is bought at the fund's lower edge;
on the sold segment it is sold; between, p(lo) = p^- and the ETF is idle there. For
Sigma_AE < 0 the levels' order and the line's slope both flip, and the segment's length is the
same expression with |rho_A| and |rho|.

*1b.* Differences of the displayed levels: hi^b - lo^b = hi^s - lo^s = (kappa^+_A + kappa^-_A)/c^res;
hi^idle - lo^idle = (kappa^+_A + kappa^-_A)/(gamma Sigma_AA); hi^s - lo^b = [kappa^+_A + kappa^-_A - rho (kappa^+_E + kappa^-_E)]/c^res.
Which pair is active at a given p^- is read from 1a; the mixed cases lie between the extremes
by monotonicity of each edge in p^-.

*1c.* NT_{T-1}(z) is the set where neither instrument trades, claim 029's 2c.

### 2. Every review

*Definitions.* A function F of two real arguments has *increasing differences* if
F(s_2, t_2) - F(s_1, t_2) >= F(s_2, t_1) - F(s_1, t_1) whenever s_1 <= s_2 and t_1 <= t_2, and
*decreasing differences* if the reverse inequality holds. A function F on a product of
intervals D in R^m is *submodular* if F(x ^ y) + F(x v y) <= F(x) + F(y) for all x, y in D.

*Lemma A (pairwise terms).* On a product of real intervals (a product of chains, a sublattice
of R^m under the coordinatewise order): (i) a function of one coordinate is submodular (with
equality); (ii) a function with decreasing differences in every pair of coordinates (in
particular a function of two coordinates with decreasing differences in them, or a sum of
such functions and functions of one coordinate) is submodular; (iii) nonnegative
combinations of submodular functions are submodular; (iv) a submodular function has
decreasing differences in every pair of coordinates. (ii) and (iv) are ledger entry AX-14
(`topkis1978minimizing`, Theorems 3.2 and 3.1, cited): its hypotheses are that each factor is
a chain (a real interval) and, for (iv), that the domain is a sublattice of the product (a
product of intervals is one); "antitone differences" there is "decreasing differences" here.
(i) and (iii) are immediate from the definition (x ^ y and x v y carry the min and the max of
each coordinate; inequalities add), and the source states them too.

*Lemma B (convex functions of a difference).* If phi is convex on R then (s, t) -> phi(s - t)
has decreasing differences in (s, t). Proof: for s_1 <= s_2 the increment phi(x + (s_2 - s_1)) - phi(x)
is nondecreasing in x by convexity; at t_2 >= t_1 it is evaluated at x = s_1 - t_2 <= s_1 - t_1.

*Lemma C (partial minimization).* Let F be continuous and submodular on X x Y, X and Y
products of closed intervals with Y compact, and V(x) = min_{y in Y} F(x, y). Then V is
submodular on X. This is ledger entry AX-14 (`topkis1978minimizing`, Theorem 4.3, cited) with
its lattices X and Y the two products of intervals, S = X x Y (a sublattice of the product),
f = F submodular on S, and g(t) = inf over the section of F finite on the projection X: the
infimum is attained (F continuous, Y compact), so it is finite, which is the only hypothesis
to check.

*Flipped coordinates.* Put u = -a and u' = -a'. Increasing differences of a function of (a, p)
is decreasing differences of the same function of (u, p), and conversely; and composing with
a coordinatewise map that is decreasing in the first argument and increasing in the second
(such as (u', p') -> (-u' g_A, p' g_E) with g > 0) turns increasing differences in (a, p) into
decreasing differences in (u', p'): apply the definition to a_2 <= a_1.

*Induction.* Claim: V_t(., z) has decreasing differences in (u, p) for every t <= T and z. At
t = T, V_T = 0. Suppose it holds at t + 1. The minimand of V_t at (u, p; u', p'),

```
F(u, p, u', p') = C_A(u - u') + C_E(p' - p) + (gamma/2) Sigma_AA (a' - a*)^2 + (gamma/2) Sigma_EE (p' - p*)^2
                  - gamma Sigma_AE u' (p' - p*) - gamma Sigma_AE a* (p' - p*) + beta sum q(z', g'|z) V_{t+1}((-u' g'_A, p' g'_E), z'),
```

(a' - a = u - u'; C_A and C_E convex) is a sum of terms each depending on at most two
coordinates: C_A(u - u') has decreasing differences in (u, u') (Lemma B); C_E(p' - p) in
(p', p) (Lemma B); the bilinear term -gamma Sigma_AE u' p' has decreasing differences in (u', p')
since its increment in u' is -gamma Sigma_AE (Delta u') p', nonincreasing in p' when Sigma_AE >= 0;
each continuation term has decreasing differences in (u', p') by the induction hypothesis and
the flipped-coordinates remark (weights q >= 0, g' > 0); the remaining terms depend on one
coordinate. By Lemma A, F is submodular on R^2_{>=0} x box (in the coordinates (u, p, u', p')
with u ranging over the flipped quadrant, a product of intervals). F is continuous and the box
compact, so Lemma C gives V_t(., z) submodular in (u, p), hence decreasing differences (Lemma
A(iv)); that is, increasing differences in (a, p). The same argument with the minimization
over p' alone (and a = -u fixed as a parameter of F) gives U_t(a; p^-, z) increasing differences
in (a, p^-), and G_t(., z) has them directly as the sum displayed with (u', p') as the
arguments. This is 2a.

*2b.* Increasing differences of U_t in (a, p^-) give, for p_1 <= p_2 and h > 0,
[U_t(a + h; p_2) - U_t(a; p_2)]/h >= [U_t(a + h; p_1) - U_t(a; p_1)]/h, so the one-sided
derivatives satisfy U'_{t,+}(a; p_2) >= U'_{t,+}(a; p_1) and likewise for U'_{t,-} (U_t is convex
in a by claim 107's 1a, so they exist). The set {a : U'_{t,+}(a; p^-) >= -kappa^+_A} therefore
grows with p^-, so its infimum lo_t(z; p^-) is nonincreasing; the set {a : U'_{t,-}(a; p^-) <= kappa^-_A}
shrinks, so its supremum hi_t(z; p^-) is nonincreasing.

*2c.* The ETF's band given a is claim 029's band for p -> G_t((a, p), z), which is finite,
continuous and strictly convex in p (a positive definite quadratic plus a convex continuation;
claim 029's 1a regularity, or claim 107's 1a with the instruments' roles exchanged), and
G_t has increasing differences in (a, p) by 2a; the argument of 2b with a in place of p^-.

*2d.* From (a, p), claim 107's 1a gives the fund's post-trade holding a' = clip(a, lo_t(z; p), hi_t(z; p))
and then the ETF's post-trade holding as the optimum of p' -> G_t((a', p'), z) + C_E(p' - p),
which by claim 029's 1a is clip(p, lo^E_t(z; a'), hi^E_t(z; a')). So (a, p) is a no-trade point
iff a is in [lo_t(z; p), hi_t(z; p)] and p is in [lo^E_t(z; a), hi^E_t(z; a)]. Containment in the
outer parallelotope is claim 107's part 2.

*Signs.* For Sigma_AE <= 0 everywhere, flip p instead of a (put w = -p): the bilinear term
becomes -gamma |Sigma_AE| a' w' up to one-coordinate terms, and the same induction gives
decreasing differences in (a, p). For Sigma_AE = 0 the minimand is a sum of a function of
(a, a') and one of (p, p') plus the continuation, which by induction is such a sum too.

### 3. Frozen ETF

With the ETF frozen at p_0 under pure-learning marking, the recursion is
V^fr_t(a, z) = min_{a' in [0, bar x_A]} [C_A(a' - a) + G^fr_t(a', z)] with
G^fr_t(a, z) = (gamma/2)[Sigma_AA (a - a*)^2 + 2 Sigma_AE (a - a*)(p_0 - p*) + Sigma_EE (p_0 - p*)^2] + beta E[V^fr_{t+1}(a, z') | z].
Completing the square in a,

```
(gamma/2)[Sigma_AA (a - a*)^2 + 2 Sigma_AE (a - a*)(p_0 - p*)] = (gamma Sigma_AA/2) (a - a^idle)^2 - (gamma Sigma_AA/2) rho_A^2 (p_0 - p*)^2,
```

with a^idle = a* - rho_A (p_0 - p*), and the last term is free of a. So G^fr_t is claim 029's
one-instrument stay objective with curvature gamma Sigma_AA,t(z), target a^idle_t(z), the
fund's rates and cap, plus a constant, and V^fr_t its value plus a constant; claim 029's
1a-1e apply (claim 100's 1b for the state-dependent covariance). The innovation identity
Delta a^idle = Delta a* + rho_A Delta p* is the definition with rho_A and p_0 constant, and
its variance is the displayed quadratic form in (v_A, v_E, r); its derivative in r is
2 rho_A sqrt(v_A v_E). The frictionless comparison is claim 107's part 3.

### 4. The last review

Part 1's formulas and claim 029's 2c involve a*, p*, Sigma, the rates, the caps and p^- only.
For t < T-1 the only term of G_t through which the law of (z', g') enters is
beta E[V_{t+1}(., z') | z], by definition.

## Checks

`uv run python checks/108/check.py` (exits non-zero on failure; a check, not a proof). A
two-instrument grid dynamic program (fund step 0.005, ETF step 0.01; T = 3; a two-branch tree
moving both targets; pure-learning marking; assumed inputs) computing the ETF-optimized value
by an ETF pass and then a fund pass, at correlations 0.8, 0.3, 0.6 (asymmetric ETF rates) and
-0.5 with ETF rates 20 bp, and a frictionless ETF. It checks part 1's median formula for both
edges at every ETF incumbent where the ETF optimizer is interior and the edge is inside the
fund's box (1,273-1,928 edge points per run, to 1.5 grid steps), and the bend-length identity;
part 2's monotonicity of the fund's edges in the ETF incumbent and of the ETF's edges in the
fund holding, with the sign of the covariance, at every review and node; and part 3's
frozen-ETF trades against a one-instrument dynamic program with the idle target at every ETF
column (exact equality of the trade maps). Part 4 is immediate and not checked. The run also
prints the largest edge slope in the ETF incumbent for the Not shown observation.

## Not shown

- The conjecture in the Reading (the mixture over future idle and re-hedging states; the r
  dependence at reviews before the last, beyond parts 3-4) is not claimed; experiments 038-039
  and 039's addendum are its evidence, and a proof would bound the continuation's second
  differences by the regime probabilities.
- D15e's question (math): the fine-regime asymptotic order of the fund's band with one ETF,
  the cube-root law in the mixture variance against `possamai2015homogenization`. Nothing here
  states it; parts 3-4 give the two exact limits and the r-free last review it must match.
- Slope bound, observed and not claimed: at every review the fund's edge moves with the ETF
  incumbent at most at the idle line's rate, |d lo_t/d p^-| <= |rho_A|, attained on the idle
  segment at the last review (the check's runs: secant slopes over ten ETF steps of 0.650,
  0.250, 0.500, 0.600 against rho_A of 0.624, 0.234, 0.468, 0.702, within a grid step). The
  submodularity argument does not give it: in the coordinates (a + rho_A p, p) the fund's cost
  term has mixed signs.
- Part 1 assumes the ETF box slack at the fund's edges and clips the medians to the fund's box;
  with the ETF at a bound, its optimizer is one-sided and the median formula does not apply
  (D15d's territory, claims 040-041).
- Part 2 assumes one sign of Sigma_AE along the whole tree. With M ETFs the argument needs a
  sign pattern of Sigma that a coordinate flip makes nonpositive off the diagonal (the fund
  positively correlated with every ETF and the ETFs mutually nonpositively correlated, or the
  mirror); the common case of several positively correlated ETFs is outside it.
- Part 3 is stated under pure-learning marking with the ETF frozen; under general marking the
  frozen ETF's marked holding p_t is part of the public state and the same reduction holds
  with a^idle_t(z, p_t), Not shown in detail. The variance statement takes Sigma constant; with
  claim 100's learning path rho_A,t moves and v^idle is state-dependent. Claim 100's
  learning-path statements (rising ceiling, outward drift) transfer only where a^idle has the
  form its hypotheses need, not checked here.
- The budget is slack. No calibration or magnitude; the analyst has the formulas by note.

## Prior art

Mechanism: with two instruments and proportional costs, the no-trade boundary of one
instrument, as a function of the other's holding, follows the static hedging line while the
other instrument is idle and is flat while it trades, and when the two instruments' marginals
are complementary in the covariance the value function inherits increasing differences under
partial minimization, so every boundary is monotone in the other holding; freezing one
instrument turns the other's problem into a one-instrument problem whose target's innovations
are the hedged combination of both targets'.

General results checked: `topkis1978minimizing` (full text; ledger entry AX-14, cited):
submodularity is preserved by partial minimization on a lattice (Theorem 4.3), and pairwise
antitone differences characterize submodularity on products of chains (Theorems 3.1-3.2);
part 2's Lemmas A and C are these theorems on products of real intervals, and the claim
checks only their hypotheses (rule 21; PM's approval follow-up). Claim 107
(formalized): the ETF-optimized value, the effective band, 1d's last-review edge values and
the outer parallelotope, which parts 1-2 organize as functions of the ETF incumbent. Claim
029 (formalized): the band definitions, 2c's static shift and the one-instrument theory that
part 3 transfers; claim 100 (formalized): the state-dependent covariance. Claim 102 (approved):
the re-hedge costs behind the levels lo^b, lo^s. `possamai2015homogenization` (full text) and
`muhlekarbe2017primer` (full text): the multi-asset small-cost no-trade region is, to leading
order, an ellipsoid-like set from a corrector equation in the covariance; neither gives the
bend of part 1 (a finite-cost, exact statement), the monotonicity of part 2 (a comparative
static in the incumbents, not a small-cost expansion) or the frozen limit of part 3.
`liu2013portfolio` (full text): no-trade regions for several assets with proportional costs
under independence, where every boundary is flat in the other holdings, the Sigma_AE = 0
case of part 2. Claim 029's 2c (the static bundling shift) is the idle line of part 1.

Searched: claims 029, 100, 102, 104, 107 and the D15c roadmap entry; FINDINGS entries of
2026-09-29 on experiments 036, 038 and 039; the refuted directory (101); refs for Topkis,
Possamaï-Soner-Touzi, Muhle-Karbe-Reppen-Soner and Liu. No web search. This is a claim
because D15c asks for the region's shape in the inputs, and the kill test (the region is the
static parallelotope shifted per instrument by the benchmark small-cost formula) fails on
part 1's bend, whose length is the other instrument's residual width, and on part 2's
monotone boundaries, which no per-instrument shift produces.

## Open objections

none

## Review

**Red, 2026-09-29** (on fe372101). Red-passed. Red re-derived every step by hand and tested each part numerically with its own exact grid DP, written without reading checks/108:
- one fund and one ETF in deviation coordinates, with fixed Sigma, beta = 1 and no marking;
- directional L1 transforms along each axis;
- a four-point target law with correlation r;
- asymmetric rates on both instruments (fund 20/5 bp, ETF 10/3 bp);
- covariances of both signs and zero.

**Part 1** (the last review; checked by hand, then numerically).
- The ETF optimizer is median(P_lo(a), p^-, P_hi(a)).
- The two-sided envelope bound gives U'(a) = dG/da(a, p(a)). An affine monotone map sends a median to a median, which gives U' = median(f_b, f_idle, f_s) with f_b = c^res (a - a*) - rho kappa^+_E.
- The median-of-roots lemma is right: at the middle root one function is zero, one is nonnegative and one nonpositive. The six displayed levels follow.
- The bend length (lo^b - lo^s)/rho_A = (kappa^+_E + kappa^-_E)/c^res_E is algebraically exact.
- At T = 1, on 264-459 ETF incumbents per covariance (corr +0.8, +0.5, -0.6, 0) with the ETF optimizer interior at both fund edges, both fund edges equal the displayed medians within 0.30 of the fund-edge resolution h_A + |Sigma_AE| gamma h_E / c^res.
- The bend length equals the ETF's residual static width to 4 digits at corr +0.8, +0.5 and -0.6.
- At corr 0 the edges do not move with p^-, as stated.

**Part 2** (every review; checked by hand, then numerically).
- The flipped-coordinate induction is sound: pairwise decreasing differences (Lemmas A-B) for the cost terms, the bilinear term -gamma Sigma_AE u' p' and the continuation composed with (-u' g_A, p' g_E); then submodular partial minimization over a product of intervals (Lemma C). Applying the same argument to the minimization over p' alone gives U_t's increasing differences in (a, p^-), and 2b follows from the one-sided derivatives.
- The DP: T = 4, r = +-0.8, corr +0.8, +0.5, -0.6 and 0.
  - The fund's edges move with p^- in the covariance's direction at every review, with no wrong-direction step (0.00 resolutions). They are flat at corr 0.
  - The ETF's edges move with the fund holding in the same direction.
  - NT_t equals the intersection of the two bands at every one of 1.4-3.3 million grid points per run, with 0 mismatches.
- Marking (g' != 1) was not tested numerically. The proof's composition step with g' > 0 is sound.

**Part 3** (frozen ETF).
- Completing the square gives curvature gamma Sigma_AA and the idle target, and the state-dependent constant does not affect the policy.
- With kappa_E -> infinity in the 2D DP, the fund's band at every ETF column and review equals a separate one-instrument DP on y = a - a^idle, with the innovation law of eps_A + rho_A eps_E, to 0.00 fund steps (596-988 bands per run).
- r moves the band through v^idle with the sign of rho_A r. At t = 0 the band is [-0.016, 0.009] with the smaller v^idle and [-0.022, 0.021] with the larger. The runs corr +0.8 with r = -0.8 and corr -0.6 with r = +0.8, whose combined laws coincide, give identical bands.

**Part 4** is immediate from part 1's formulas and the definition of G_t.

**Mechanism (4b).** The last-review band is the median of an idle line and two re-hedge levels. Every-review monotonicity comes from Topkis-type submodularity preserved under partial minimization. The frozen limit is a completed square. New in the inputs: the bend of length equal to the ETF's residual width, and the monotone two-band shape of the region. The references (Topkis, Possamai-Soner-Touzi, Muhle-Karbe-Reppen-Soner, Liu) are in refs/ with full texts. Topkis's case is proved in full, so it needs no ledger entry.

**Nit** (not required). Proof part 2, the minimand: phi_A(v) = C_A(-v) with the term phi_A(u - u') gives C_A(u' - u), but a' - a = u - u', so the cost is C_A(u - u') (phi_A should be C_A itself). Only convexity of phi_A is used, so nothing changes. The swap only exchanges the fund's two rates in that line.

Verdict: red-passed


**Red, rule 21 check of mathb's AX-14 pass, 2026-09-29.** No result changed.
- *What changed.* Lemma A (ii), (iv) and Lemma C now cite AX-14. The quotes of `topkis1978minimizing` Theorems 3.1, 3.2 and 4.3 match refs/text lines 248, 259 and 432.
- *Hypotheses, checked in place.* The factors are real intervals, so they are chains. The domain is their product, a sublattice. For Theorem 4.3, S = X x Y and the partial infimum is finite because it is attained on a compact Y.
- *Unchanged.* Lemma B (a convex function of a difference) and the induction still carry the model-specific steps. Red's nit (the cost term is C_A(u - u')) is made.
- *Red's error.* Red's first review said the inline proof needed no ledger entry. Under rule 21 (agents/red.md 4b) it should have been a required correction.
## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: every part re-derived by hand and tested on red's own exact grid DP (part 1's median edges within 0.30 resolution and the bend length equal to the ETF's residual width to 4 digits; part 2's monotone edges with no wrong-direction step and NT = intersection of two bands at every one of 1.4-3.3M points; part 3's frozen limit to 0.00 steps, with r entering only through v^idle). Mechanism: an idle line and re-hedge levels, Topkis's submodularity under partial minimization, a completed square; new in the inputs: the bend of the ETF's residual width and the monotone two-band region, so D15c's kill criterion is not met. Limit and follow-up: Lemmas A and C re-prove Topkis's finite case, against rule 21, so it enters as a ledger entry and is cited (no result change); marking g' != 1 not tested numerically.


mathb, 2026-09-29 (PM's approval follow-up, rule 21): the proof of part 2 no longer re-proves
Topkis's finite case. Lemma A (ii) and (iv) and Lemma C are now ledger entry AX-14
(`topkis1978minimizing`, Theorems 3.1-3.2 and 4.3, drafted on the same branch for the auditor),
with the hypotheses checked in place (products of real intervals; the partial infimum attained
on a compact product); Lemma B and the induction are unchanged, and red's nit (the minimand's
cost term is C_A(u - u'), since a' - a = u - u') is made. AX-14 is in axioms_used. No result
changed.

mathb, 2026-09-29 (the auditor's wording point, from claim 108's FIDELITY row): part 3 and the
title said the correlation enters the frozen band "through one variance"; the band depends on
the whole law of the idle target's innovation, of which v^idle is the second moment, so the
wording now says "through the idle target's innovation law, whose variance is v^idle", with
the scale-family case noted. No result changed.

Not machine checked. Parts 1, 2 and 4 are finite convex-analysis statements about one
review's problem given the next review's value function, with a two-lemma submodularity
induction over the tree; part 3 is a completion of the square transferring claim 029.

Lean, 2026-09-29 (final): parts 1-4 are machine checked, with the limits below. The statement is in
`lean/Standalone/M7DynamicBundlingShape.lean` and the proof in
`lean/Novel/M7DynamicBundlingShapeProof.lean`.
- Model: claim 107's formal setting with one ETF (claim 029's M6 with the fund at index 0 and the
  ETF at 1), using 107's U, loU and hiU.
- Imports: the proof imports claims 029's and 107's proof modules (depends_on, Q-04).
- Topkis's Theorems 3.1, 3.2 and 4.3 enter as the Upstream hypothesis structure
  `Upstream.Topkis` (AX-14, audited ok; instance -xy on [0,1]^2). Part 2 takes their universal
  form `AX14` as a hypothesis (rule 21). Lemma B, the flipped coordinates and the induction are
  proved.
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/108/check.py` pass.
- Scope: PM confirmed the split (lean/claim108-scope-note).

Machine checked:
- Part 1, at the last review, for an ETF incumbent p^- whose ETF optimizer at the edge is strictly
  inside the ETF box: each edge equals the clip to [0, bar x_A] of the median of its bought level,
  its idle line and its sold level.
- 1a:
  - each median is continuous;
  - for Sigma_AE > 0 it is nonincreasing in p^- and for Sigma_AE < 0 nondecreasing. In both cases
    it runs from the bought level at small incumbents, along the idle line, to the sold level, over
    an interval of length (kappa^+_E + kappa^-_E)/c^res_E;
  - for Sigma_AE = 0 the three levels coincide.
- 1b: the regime widths, as algebra.
- 1c: claim 029's StaticShape.
- Part 2 (given AX-14), for Sigma_AE >= 0 along the tree and g' > 0:
  - V_t has increasing differences on the nonnegative quadrant, G_t on the box, and U_t in (a, p^-);
  - the fund's edges are nonincreasing in the ETF incumbent, and the ETF's edges in the fund
    holding;
  - NT_t is the intersection of the two bands.
  The edges are the unique minimizers from the incumbents 0 and bar x, so monotonicity follows by
  the argmin argument.
- Part 3:
  - with the ETF frozen at p_0 under pure-learning marking, the frozen value and stay objective are
    claim 029's value and G_t for the idle instance (curvature gamma Sigma_AA, target a^idle), plus
    constants at every review and state, so the fund's band is that instance's band;
  - v^idle is the second moment of da* + rho_A dp* (as algebra).
- Part 4: two instances that agree at the last review on the premia, the covariance, gamma, the
  rates and the caps have the same last-review bands and region, whatever their outcome laws.

Paper-level:
- part 2 for Sigma_AE <= 0 (the same argument with the ETF coordinate flipped) and for
  Sigma_AE = 0 (both signs together). PM allowed recording these in place of a formal statement;
  the fidelity row should note them;
- the Reading and its conjecture, D15e's question and the Checks.

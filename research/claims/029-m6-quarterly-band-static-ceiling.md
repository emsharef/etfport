---
id: 029
title: "Quarterly no-trade bands around a moving target: trade-to-edge structure, a static width ceiling, and exactness in the coarse-innovation regime"
status: formalized
model_version: M6
depends_on: []
axioms_used: []
formal: lean/Standalone/M6QuarterlyBandStaticCeiling.lean
direction: D13
---
## Statement

D13 asks for the leading-order small-cost no-trade band around a moving frictionless target
under proportional costs and long-only caps, per instrument class, starting from a generic
target process. This first claim settles the exact discrete-time structure that any such
asymptotic must respect at quarterly reviews, and identifies the regime in which target motion
adds nothing to the one-review band. It imports no literature theorem.

**Setting.** A slack-budget M6 instance (`model/SPEC.md` M6): n >= 1 instruments, finite
public chain z_t on Z with finite return laws q_t(z', g | z), g > 0 coordinatewise, belief
mean mu(t, z), positive definite Sigma, gamma > 0, beta in (0, 1], directional rates
kappa^+_i, kappa^-_i in [0, 1), finite dollar caps bar x_i, horizon T >= 1, V_T = 0, and
initial cash h_0^- >= T sum_i (1 + kappa^+_i) bar x_i so that the cash constraint never binds.
Write X = prod_i [0, bar x_i], x*(t, z) = Sigma^{-1} mu(t, z)/gamma for the frictionless
target, and C(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-]. For t < T define the
*stay objective*

```
G_t(x, z) = (gamma/2) (x - x*(t,z))' Sigma (x - x*(t,z)) + beta sum_{(z',g')} q_t(z',g'|z) V_{t+1}(x o g', z'),
V_t(x, z)  = min_{x' in X} [ C(x' - x) + G_t(x', z) ],      x in R^n, x >= 0,
```

where x o g' is the coordinatewise product (marking) and V_t is the minimal expected
discounted remaining tracking loss plus costs from pre-trade holdings x. By M6's tracking
identity, maximizing the M6 objective is the same as this minimization, and the optimal
post-trade holding x^+_t(x, z) is the minimizer in the display.

### Part 1. One instrument: trade to the edge, and the width ceiling

Let n = 1 and write c = gamma Sigma > 0 (the per-quarter tracking curvature), kappa^+, kappa^-,
bar x, x*_t = x*(t, z). For a convex function phi on an interval write phi'_- and phi'_+ for its
left and right derivatives. For each t < T and z in Z:

1a. *Regularity and the band.* G_t(., z) is finite, continuous and strictly convex on
    [0, infinity), with finite one-sided derivatives (right derivative at 0). V_t(., z) is
    finite, continuous and convex on [0, infinity), and its one-sided derivatives satisfy
    -kappa^+ <= V'_{t,-} <= V'_{t,+} <= kappa^- everywhere (right derivative at 0). Define

    ```
    lo_t(z) = inf { x in [0, bar x) : G'_{t,+}(x, z) >= -kappa^+ }     (bar x if the set is empty),
    hi_t(z) = sup { x in (0, bar x] : G'_{t,-}(x, z) <= kappa^-  }     (0 if the set is empty).
    ```

    Then 0 <= lo_t(z) <= hi_t(z) <= bar x, and for every pre-trade holding x >= 0 (including
    x > bar x after marking) the optimal post-trade holding is unique and equals

    ```
    x^+_t(x, z) = min( max( x, lo_t(z) ), hi_t(z) ).
    ```

    The no-trade band is [lo_t(z), hi_t(z)]; outside it the investor trades to the nearer edge.
    On [0, lo_t) the derivative of V_t is -kappa^+, on (hi_t, infinity) it is kappa^-, and on
    (lo_t, hi_t) it is G'_{t,+-}.

1b. *Static width ceiling.* For every t < T and z,

    ```
    hi_t(z) - lo_t(z) <= (kappa^+ + kappa^-) / c.
    ```

    The right side is the *static width*: at the last review t = T-1 the band is exactly

    ```
    lo_{T-1}(z) = clip( x*_{T-1} - kappa^+/c, 0, bar x ),   hi_{T-1}(z) = clip( x*_{T-1} + kappa^-/c, 0, bar x ),
    ```

    whose width is (kappa^+ + kappa^-)/c whenever neither bound binds. This is claim 009's
    one-quarter band in holding coordinates with a slack budget (its multiplier interval is
    {0}) and no ETF comparator; the correspondence is a remark, not a transfer of that result.
    So at quarterly reviews a moving target, learning-driven or not, can only *narrow* the
    band relative to the one-review band, never widen it.

1c. *Edge brackets.* With bar g_t(z) = sum q_t(z',g'|z) g' the expected gross return,

    ```
    lo_t(z) >= min( bar x, x*_t - (kappa^+ + beta kappa^- bar g_t(z))/c ),
    hi_t(z) <= max( 0,     x*_t + (kappa^- + beta kappa^+ bar g_t(z))/c ).
    ```

1d. *Coarse-innovation regime: the band is the static band, shifted.* Let t <= T-2, so that
    the next review's band exists (at t = T-1 the band is 1b's, with V_T = 0). Suppose both edges are
    interior, 0 < lo_t(z) and hi_t(z) < bar x, and every positive-mass outcome (z', g') of
    q_t(. | z) satisfies one of

    ```
    (up)    hi_t(z) g' < lo_{t+1}(z'),        (down)    lo_t(z) g' > hi_{t+1}(z'),
    ```

    that is, marking carries the whole current band strictly into the next review's buy
    region or strictly into its sell region. Let U = sum over (up) outcomes of q g' and
    D = sum over (down) outcomes of q g' (return-weighted masses). Then, with the *tilt*
    tau_t(z) = beta (kappa^+ U - kappa^- D)/c,

    ```
    hi_t(z) = x*_t + kappa^-/c + tau_t(z),      lo_t(z) = x*_t - kappa^+/c + tau_t(z),
    hi_t(z) - lo_t(z) = (kappa^+ + kappa^-)/c.
    ```

    The band has exactly the static width and is the static band translated by the tilt: up
    when the target is more likely to rise (a sale now would be reversed by a purchase, so
    the sell edge waits), down when it is more likely to fall. A sufficient primitive condition
    with no marking (g' = 1 in every outcome) and interior edges is that every positive-mass
    target innovation x*(t+1, z') - x*(t, z) exceeds (1 + beta)(kappa^+ + kappa^-)/c in
    absolute value; then U and D are the probabilities that the target rises and falls. With
    marking the same follows from 1c: (up) holds when
    g' max(0, x*_t + (kappa^- + beta kappa^+ bar g_t)/c) < min(bar x, x*_{t+1}(z') - (kappa^+ + beta kappa^- bar g_{t+1}(z'))/c),
    and (down) when g' min(bar x, x*_t - (kappa^+ + beta kappa^- bar g_t)/c) > max(0, x*_{t+1}(z') + (kappa^- + beta kappa^+ bar g_{t+1}(z'))/c).

    In particular, when U = D and kappa^+ = kappa^- the tilt is zero and the band *is* the
    last review's band: in the coarse regime a martingale target with a symmetric innovation
    law adds nothing to the static band, whatever drives its motion.

1e. *When the ceiling is attained.* Let t <= T-2 and kappa^+ + kappa^- > 0. Then hi_t(z) - lo_t(z) equals
    the static width if and only if G'_{t,-}(hi_t) = kappa^-, G'_{t,+}(lo_t) = -kappa^+ (both
    edges are first-order points, so neither the cap nor the zero bound clips the band) and,
    for every positive-mass outcome, the marked band [lo_t(z) g', hi_t(z) g'] lies in
    [0, lo_{t+1}(z')] or in [hi_{t+1}(z'), infinity). Otherwise the band is strictly narrower
    than the static width. Thus strict narrowing at quarterly reviews happens exactly when a
    bound clips the band or some outcome leaves the marked band straddling the next review's
    band: the *fine-innovation regime*, where the continuation loss is strictly convex across
    the band. At t = T-1 the continuation V_T = 0 is affine, so the width is the static width
    if and only if both edges are first-order points.

### Part 2. Many instruments: the no-trade set's Sigma-diameter and the static shape

For general n, t < T and z, let NT_t(z) = { x in X : x^+_t(x, z) = x } be the *no-trade set*.

2a. G_t(., z) is finite and convex on R^n_{>=0} and G_t - (gamma/2)(. - x*)' Sigma (. - x*) is
    convex; V_t(., z) is finite and convex; the optimal post-trade holding is unique; NT_t(z)
    is nonempty and contains every optimal post-trade holding.

2b. *Sigma-diameter inequality.* For all x, y in NT_t(z),

    ```
    gamma (x - y)' Sigma (x - y) <= sum_i (kappa^+_i + kappa^-_i) |x_i - y_i|.
    ```

    In particular two no-trade holdings differing only in instrument i differ by at most
    (kappa^+_i + kappa^-_i)/(gamma Sigma_ii), the instrument's own static width; and
    ||x - y||_2 <= sqrt(n) max_i (kappa^+_i + kappa^-_i) / (gamma lambda_min(Sigma)).

2c. *Static shape and the bundling shift.* At t = T-1, with d = x - x*_{T-1},

    ```
    NT_{T-1}(z) = { x in X : for every i, [gamma Sigma d]_i in [-kappa^+_i, kappa^-_i] if 0 < x_i < bar x_i,
                                           [gamma Sigma d]_i >= -kappa^+_i if x_i = 0,
                                           [gamma Sigma d]_i <= kappa^-_i  if x_i = bar x_i }.
    ```

    Where no bound binds this is the parallelotope x* + (gamma Sigma)^{-1} prod_i [-kappa^+_i, kappa^-_i].
    For one instrument A and the others E, the A-condition at an interior holding reads

    ```
    d_A in -(Sigma_AE d_E)/Sigma_AA + [-kappa^+_A, kappa^-_A] / (gamma Sigma_AA):
    ```

    the fund's static band is its own static width, centred not at its target but at the
    target minus the exposure the other instruments' deviations already supply: their
    deviation times Sigma_AE/Sigma_AA, the hedge ratio of the E-deviation portfolio's return
    on A's return (the regression of E on A). This is what bundling adds at the static level:
    an ETF deviation substitutes for a fund trade at the rate Sigma_AE/Sigma_AA. Its dynamic counterpart is not established here (Not shown).

**Consequence for D13** (a reading of 1b, 1d and 1e, not a further theorem). At quarterly
reviews the small-cost band around a moving target lives between two exact anchors: the
static width (kappa^+ + kappa^-)/(gamma Sigma_ii), attained exactly in the coarse regime, and
strict narrowing in the fine regime. Which regime an instrument is in is decided by the scale
of its target's quarterly innovation against its own static width. Instruments with small
rates (ETFs) have small static widths and are the more likely to be in the coarse regime,
where target motion adds nothing beyond a tilt; instruments with large rates (funds carrying
loads or redemption fees) have wide static widths and are the more likely to be in the fine
regime, where the band is strictly narrower and the continuous-time cube-root asymptotics is
the candidate leading order. Whether calibrated fund-of-funds instances fall on either side is
for the analyst's reference experiment; the fine-regime leading order is D13's next claim.

## Proof

### 0. Conventions

All sums over outcomes are finite. For a convex function phi on an interval, phi'_- <= phi'_+
at interior points, both are nondecreasing, phi'_+(a) <= phi'_-(b) for a < b, phi'_+ is
right-continuous and phi'_- is left-continuous, and phi'_+(a) = lim_{x downarrow a} phi'_-(x).
One-sided derivatives of a finite sum of convex functions are the sums of the one-sided
derivatives, and for g' > 0 the function x -> V(x g') has one-sided derivatives g' V'_{+-}(x g').
The optimality condition for minimizing a convex function psi over an interval [0, bar x] at
an interior point p is psi'_-(p) <= 0 <= psi'_+(p); at p = 0 it is psi'_+(0) >= 0; at p = bar x
it is psi'_-(bar x) <= 0.

### 1. One instrument

*1a, by backward induction on t.* Induction hypothesis at t+1: V_{t+1}(., z') is finite,
continuous and convex on [0, infinity) with one-sided derivatives in [-kappa^+, kappa^-]
(right derivative at 0). It holds at T (V_T = 0). Given it, G_t(., z) is a finite sum of the
strictly convex continuous quadratic (c/2)(x - x*_t)^2 and of convex continuous functions
x -> beta q V_{t+1}(x g', z'), so it is finite, continuous, strictly convex, and its one-sided
derivatives are c(x - x*_t) + beta sum q g' V'_{t+1,+-}(x g', z'), finite on [0, infinity).

The function (x, x') -> C(x' - x) + G_t(x', z) is jointly convex and continuous on
[0, infinity) x [0, bar x]. Its minimum over the compact set x' in [0, bar x] is attained and
unique in x' (strict convexity in x'), and V_t(., z) is finite, continuous (minimum of a jointly
continuous function over a fixed compact set) and convex (partial minimization of a jointly
convex function over a convex set).

*The band.* First lo_t <= hi_t: if hi_t < lo_t, pick x with hi_t < x < lo_t; then
G'_{t,+}(x) < -kappa^+ (x < lo_t, by the definition of lo_t as an infimum and monotonicity)
and G'_{t,-}(x) > kappa^- (x > hi_t), contradicting G'_{t,-} <= G'_{t,+} and -kappa^+ < kappa^-.
Also G'_{t,+}(lo_t) >= -kappa^+ when lo_t < bar x (right-continuity), and G'_{t,-}(hi_t) <= kappa^-
when hi_t > 0 (left-continuity); when lo_t > 0, G'_{t,-}(lo_t) <= -kappa^+ (left limit of values
below -kappa^+) and when hi_t < bar x, G'_{t,+}(hi_t) >= kappa^-.

Fix a pre-trade x >= 0 and let psi(x') = C(x' - x) + G_t(x', z) on [0, bar x], convex. Its
one-sided derivatives are G'_{t,+-}(x') + kappa^+ for x' > x, G'_{t,+-}(x') - kappa^- for x' < x,
and at x' = x the right derivative is G'_{t,+}(x) + kappa^+ and the left derivative is
G'_{t,-}(x) - kappa^-.

- If x < lo_t, the candidate is p = lo_t. For x' in [0, lo_t), x' != x: the right derivative of
  psi is at most G'_{t,+}(x') + kappa^+ < 0 (below lo_t, G'_{t,+} < -kappa^+; below x the
  derivative is even smaller by kappa^+ + kappa^-), and at x' = x it is G'_{t,+}(x) + kappa^+ < 0;
  so psi decreases on [0, lo_t]. If lo_t = bar x this proves p = bar x. Otherwise
  psi'_+(lo_t) = G'_{t,+}(lo_t) + kappa^+ >= 0 and psi'_-(lo_t) <= 0, so lo_t is a minimizer.
- If x > hi_t, symmetrically the candidate is p = hi_t: psi increases on [hi_t, bar x] (above
  hi_t, G'_{t,-} > kappa^-, and above x it is larger by kappa^+ + kappa^-), and at hi_t the
  optimality inequalities hold (or hi_t = 0). This covers x > bar x, where every feasible
  x' is a sale.
- If lo_t <= x <= hi_t (so x <= bar x), the candidate is p = x: psi'_+(x) = G'_{t,+}(x) + kappa^+
  >= G'_{t,+}(lo_t) + kappa^+ >= 0 when lo_t < bar x (and no right move exists when
  x = bar x), and psi'_-(x) = G'_{t,-}(x) - kappa^- <= G'_{t,-}(hi_t) - kappa^- <= 0 when
  hi_t > 0 (and no left move exists when x = 0).

Uniqueness of the minimizer makes the candidate the optimum in every case. The derivative
description of V_t follows: on [0, lo_t), V_t(x) = kappa^+(lo_t - x) + G_t(lo_t), derivative
-kappa^+; on (hi_t, infinity), V_t(x) = kappa^-(x - hi_t) + G_t(hi_t), derivative kappa^-; on
(lo_t, hi_t), V_t = G_t. At lo_t (if 0 < lo_t < bar x) the left derivative is -kappa^+ and the
right derivative is G'_{t,+}(lo_t) >= -kappa^+; at hi_t the left derivative is
G'_{t,-}(hi_t) <= kappa^- and the right derivative is kappa^-; at lo_t = hi_t both statements
hold. On (lo_t, hi_t), -kappa^+ <= G'_{t,+}(lo_t) <= G'_{t,+-}(x) <= G'_{t,-}(hi_t) <= kappa^-.
Hence V'_{t,+-} in [-kappa^+, kappa^-] on [0, infinity), which is the induction hypothesis at t.

*1b.* If hi_t = lo_t the ceiling is trivial. Otherwise hi_t > 0 and lo_t < bar x, so
G'_{t,-}(hi_t) <= kappa^- and G'_{t,+}(lo_t) >= -kappa^+. Let phi = G_t - (c/2)(. - x*_t)^2,
a finite sum of convex functions, hence convex, with phi'_+(lo_t) <= phi'_-(hi_t). Therefore

```
c (hi_t - lo_t) = [G'_{t,-}(hi_t) - phi'_-(hi_t)] - [G'_{t,+}(lo_t) - phi'_+(lo_t)]
                <= G'_{t,-}(hi_t) - G'_{t,+}(lo_t) <= kappa^- + kappa^+.
```

At t = T-1, G_{T-1} = (c/2)(x - x*)^2 has derivative c(x - x*), and the definitions give
lo_{T-1} = max(0, x* - kappa^+/c) when this is below bar x and bar x otherwise, and
hi_{T-1} = min(bar x, x* + kappa^-/c) when this is positive and 0 otherwise: the displayed
clips. The claim 009 correspondence: with a slack budget claim 009's compatible multiplier
interval is {0} and its band in the active belief mean is [alpha_c - kappa^-_A, alpha_c + kappa^+_A]
with alpha_c = gamma(Sigma w)_A - B^A bar lambda, that is mu_A - gamma(Sigma w)_A in
[-kappa^-_A, kappa^+_A], which is [gamma Sigma (w - x*)]_A in [-kappa^+_A, kappa^-_A]: the
static condition of 2c at the fixed ETF-optimal holding. Claim 009 fixes the incumbent and
varies the belief mean under a funded budget with an ETF comparator; 1b fixes the belief and
reads the same one-review condition in holding coordinates with a slack budget. Nothing is
transferred.

*1c.* From 1a at t+1, V'_{t+1,+-} <= kappa^- and >= -kappa^+, so for x in [0, infinity)

```
c(x - x*_t) - beta kappa^+ bar g_t(z) <= G'_{t,+-}(x, z) <= c(x - x*_t) + beta kappa^- bar g_t(z).
```

If x < x*_t - (kappa^+ + beta kappa^- bar g_t)/c then G'_{t,+}(x) < -kappa^+, so such x are
not in the set defining lo_t; hence lo_t >= x*_t - (kappa^+ + beta kappa^- bar g_t)/c when that
number is below bar x, and lo_t = bar x otherwise. The bound on hi_t is symmetric.

*1d.* On an (up) outcome, hi_t g' lies in (0, lo_{t+1}(z')), where V_{t+1}(., z') is affine
with slope -kappa^+ (1a at t+1); on a (down) outcome, lo_t g' and hi_t g' lie in
(hi_{t+1}(z'), infinity), where V_{t+1}(., z') is affine with slope kappa^-. Since lo_t <= hi_t,
on an (up) outcome also lo_t g' in (0, lo_{t+1}(z')). Hence V_{t+1}(., z') is differentiable
at hi_t g' and at lo_t g' on every positive-mass outcome, and G_t(., z) is differentiable at
hi_t and at lo_t with

```
G'_t(hi_t) = c(hi_t - x*_t) + beta (kappa^- D - kappa^+ U),
G'_t(lo_t) = c(lo_t - x*_t) + beta (kappa^- D - kappa^+ U).
```

Both edges are interior, so by the boundary facts in 1a, G'_{t,-}(hi_t) <= kappa^- <= G'_{t,+}(hi_t)
and G'_{t,-}(lo_t) <= -kappa^+ <= G'_{t,+}(lo_t); with differentiability these are equalities.
Solving gives hi_t = x*_t + [kappa^- - beta(kappa^- D - kappa^+ U)]/c = x*_t + kappa^-/c + tau_t
and lo_t = x*_t - kappa^+/c + tau_t, and subtracting gives the width. The primitive sufficient
conditions substitute 1c's brackets: hi_t <= max(0, x*_t + (kappa^- + beta kappa^+ bar g_t)/c),
lo_{t+1}(z') >= min(bar x, x*_{t+1}(z') - (kappa^+ + beta kappa^- bar g_{t+1}(z'))/c), and
symmetrically; without marking bar g = 1 and interior edges reduce (up) to
x*_{t+1}(z') - x*_t > (kappa^- + beta kappa^+)/c + (kappa^+ + beta kappa^-)/c = (1 + beta)(kappa^+ + kappa^-)/c
and (down) to the mirror inequality. The final sentence is tau_t = 0 read off the formula.

*1e.* By 1b, equality forces hi_t > lo_t (else the width is 0 < static width) and equality in
both inequalities of the chain: G'_{t,-}(hi_t) = kappa^-, G'_{t,+}(lo_t) = -kappa^+, and
phi'_+(lo_t) = phi'_-(hi_t). For a convex phi with lo_t < hi_t, phi'_+(lo_t) = phi'_-(hi_t)
holds if and only if phi' is constant on (lo_t, hi_t), that is, phi is affine on [lo_t, hi_t].
Now phi(x) = beta sum q V_{t+1}(x g', z') is a finite sum of convex functions with positive
weights; such a sum is affine on an interval if and only if every summand is (a convex
summand that is not affine lies strictly below its chord at some midpoint, and the sum would
then too). And V_{t+1}(., z') is affine on [lo_t g', hi_t g'] if and only if that interval lies
in [0, lo_{t+1}(z')] or in [hi_{t+1}(z'), infinity): by 1a, V_{t+1} is affine on those two
pieces and coincides with the strictly convex G_{t+1} on [lo_{t+1}, hi_{t+1}], so an interval
on which it is affine cannot contain a subinterval of (lo_{t+1}, hi_{t+1}), and when
lo_{t+1} = hi_{t+1} the two affine pieces have different slopes -kappa^+ < kappa^-
(kappa^+ + kappa^- > 0), so an affine interval cannot contain that point in its interior.
Conversely these three conditions give equality in the chain. The "otherwise" clause is 1b.

### 2. Many instruments

*2a.* As in 1a, by backward induction: G_t(., z) is the sum of the quadratic
(gamma/2)(x - x*)' Sigma (x - x*), strictly convex since Sigma is positive definite, and the
convex functions x -> beta q V_{t+1}(x o g', z') (a convex function composed with a linear map);
so G_t - (gamma/2)(. - x*)' Sigma (. - x*) is convex, G_t is finite, continuous and strictly
convex on R^n_{>=0}, the minimizer over the compact X is unique, and V_t is finite, continuous
and convex as the partial minimum of a jointly convex continuous function over a compact
convex set. For x in R^n_{>=0} let p = x^+_t(x, z). For any x'' in X, subadditivity and positive
homogeneity of C give C(x'' - x) <= C(p - x) + C(x'' - p), so

```
C(p - x) + G_t(p) <= C(x'' - x) + G_t(x'') <= C(p - x) + C(x'' - p) + G_t(x''),
```

hence G_t(p) <= C(x'' - p) + G_t(x''): no trade is optimal from p, and by uniqueness
x^+_t(p, z) = p. Thus p in NT_t(z), which is nonempty.

*2b.* Fix x, y in NT_t(z) and put d = y - x. Since X is convex, x + s d lies in X for every
s in (0, 1], so it is a feasible post-trade holding from x, and no trade being optimal from x
gives, with positive homogeneity of C,

```
G_t(x) <= C(s d) + G_t(x + s d) = s C(d) + G_t(x + s d).
```

G_t is the quadratic (gamma/2)(. - x*)' Sigma (. - x*) plus the convex phi (2a). For the
quadratic, (gamma/2)(x + s d - x*)' Sigma (x + s d - x*) = (1 - s) (gamma/2)(x - x*)' Sigma (x - x*)
+ s (gamma/2)(y - x*)' Sigma (y - x*) - (gamma/2) s (1 - s) d' Sigma d exactly, and for phi,
phi(x + s d) <= (1 - s) phi(x) + s phi(y); so

```
G_t(x + s d) <= (1 - s) G_t(x) + s G_t(y) - (gamma/2) s (1 - s) d' Sigma d.
```

Combining and dividing by s,

```
G_t(x) - G_t(y) <= C(d) - (gamma/2) (1 - s) d' Sigma d      for every s in (0, 1],
```

hence, letting s -> 0, G_t(x) - G_t(y) <= C(d) - (gamma/2) d' Sigma d. The same argument from
y with -d gives G_t(y) - G_t(x) <= C(-d) - (gamma/2) d' Sigma d. Adding,

```
gamma d' Sigma d <= C(d) + C(-d) = sum_i (kappa^+_i + kappa^-_i) |d_i|.
```

If d = w e_i this reads gamma Sigma_ii w^2 <= (kappa^+_i + kappa^-_i)|w|. In general
gamma lambda_min ||d||_2^2 <= max_i(kappa^+_i + kappa^-_i) ||d||_1 <= max_i(kappa^+_i + kappa^-_i) sqrt(n) ||d||_2.
No subdifferential calculus is used.

*2c.* At T-1, G_{T-1}(x') = (gamma/2)(x' - x*)' Sigma (x' - x*) with gradient gamma Sigma (x' - x*).
Write Q(x') = C(x' - x) + G_{T-1}(x') and d = x - x*, and let u = x' - x, so that

```
Q(x') - Q(x) = C(u) + (gamma Sigma d)' u + (gamma/2) u' Sigma u.
```

*Necessity.* Let x in NT_{T-1}(z). If x_i < bar x_i, then x' = x + s e_i is feasible for small
s > 0 and Q(x') - Q(x) = s [kappa^+_i + (gamma Sigma d)_i] + (gamma/2) s^2 Sigma_ii >= 0; dividing by s
and letting s -> 0 gives (gamma Sigma d)_i >= -kappa^+_i. If x_i > 0, then x' = x - s e_i is
feasible and Q(x') - Q(x) = s [kappa^-_i - (gamma Sigma d)_i] + (gamma/2) s^2 Sigma_ii >= 0 gives
(gamma Sigma d)_i <= kappa^-_i. An interior coordinate satisfies both, x_i = 0 only the first
and x_i = bar x_i only the second: the three cases.

*Sufficiency.* Let x in X satisfy the three cases and let x' in X, u = x' - x. Coordinatewise,
kappa^+_i u_i^+ + kappa^-_i u_i^- + (gamma Sigma d)_i u_i equals u_i^+ [kappa^+_i + (gamma Sigma d)_i]
+ u_i^- [kappa^-_i - (gamma Sigma d)_i]; when u_i > 0 feasibility forces x_i < bar x_i, where
(gamma Sigma d)_i >= -kappa^+_i, and when u_i < 0 it forces x_i > 0, where (gamma Sigma d)_i <= kappa^-_i,
so every term is nonnegative. With u' Sigma u >= 0 this gives Q(x') >= Q(x): x' = x is a
minimizer, and by uniqueness x in NT_{T-1}(z). Without binding bounds the condition is
gamma Sigma d in prod_i [-kappa^+_i, kappa^-_i], that is d in (gamma Sigma)^{-1} prod_i [-kappa^+_i, kappa^-_i].
The A-row of gamma Sigma d is gamma (Sigma_AA d_A + Sigma_AE d_E); dividing by gamma Sigma_AA > 0
gives the displayed interval.

## Checks

`uv run python checks/029/check.py` (exits non-zero on failure; a check, not a proof).
Backward induction on a fine holding grid with linear interpolation, for assumed one-instrument
M6 instances with finite target-innovation and return laws, beta in {1, 0.97}, caps and no
caps, T in {3, 4, 6}: (i) the computed policy is a clip to the computed edges at every grid point;
(ii) every band width is at most the static width plus two grid cells; (iii) the last review's
edges match 1b's clips; (iv) on coarse instances (every innovation beyond
(1 + beta)(kappa^+ + kappa^-)/c, edges interior) the edges match 1d's tilted static band, including
a skewed law where the tilt is nonzero, and the width is the static width; (v) on fine instances
(innovations one quarter of the static width) the width is strictly below the static width by
more than the grid tolerance; (vi) with marking (gross returns in {0.9, 1.1}) the edge brackets
of 1c hold. A two-instrument instance with Sigma_AE != 0 checks 2c's parallelotope against a
direct quadratic minimization on a two-dimensional grid and 2b's inequality on the no-trade set
at T-1 and T-2. All inputs are assumed; no calibration or economic magnitude is reported.

## Not shown

- The fine regime's leading order (the continuous-time cube-root band and its constant) is not
  proved, not even conjectured here with a constant: 1e only shows strict narrowing. It is
  D13's next claim, to be filed as a conjecture with the analyst's exact dynamic-programming
  evidence if a proof is not at hand.
- The funded budget is assumed slack (M6's slack-budget instance). Claim 009 shows that a
  binding budget scales the band by one plus the cash multiplier; that effect, and the
  coupling of instruments through cash, are outside this claim.
- Caps enter only through clipping and the one-sided derivatives. The magnitude by which a
  binding cap reshapes the interior edge (`liu2013portfolio`'s gap) is not quantified; 1c's
  brackets are crude there.
- For n > 1 only the Sigma-diameter inequality and the static shape are proved. The dynamic
  no-trade set need not be a box or a parallelotope, and the dynamic version of the bundling
  shift is not established. The coarse-regime formulas are one-instrument statements.
- The target process is generic: M6 takes mu(t, z) as given. Nothing here uses that a posterior
  mean is a martingale or that Kalman innovations shrink over time; the specialization to D12's
  aim portfolio and to learning-driven innovation laws is a later claim. "Learning-driven"
  enters this claim only as the innovation law of the target.
- The objective is the additive sum of quarterly conditional scores (M0 formulation 2), not a
  terminal-utility problem; the tracking identity is exact for that objective only. Dollar caps
  and cash-account units are M6 idealizations. No monotonicity of the band in the innovation
  scale, in beta or in T is asserted; 1d and 1e give exact equality and strict inequality, not
  a comparative static. No calibration, materiality or novelty claim is made; the assignment
  of ETFs to the coarse and funds to the fine regime is an expectation for the analyst to test.

## Prior art

Mechanism: minimizing a strictly convex holding loss plus a proportional trading charge over
successive decision dates makes the optimal action at each date a projection onto an interval
of positions; the interval is at most as wide as the one-date interval because the continuation
loss is convex, and it is exactly that wide when the continuation loss is affine across it,
which happens when every outcome throws the whole interval past one edge of the next date's
interval.

General results checked: the trade-to-the-edge band of discrete-time trading with proportional
or convex transaction costs is classical; its source is Constantinides (1979), "Multiperiod
Consumption and Investment Behavior with Convex Transactions Costs", Management Science 25(11)
(`constantinides1979multiperiod`, registered, `wanted`: no open copy exists and the human has
been asked for it; cited here by title only). Part 1a is a special case of that structure. It
is re-derived here, not imported, only to carry what this claim adds and its later parts use:
the moving target x*(t, z), the caps, marking by gross returns, and the one-sided derivative
bounds -kappa^+ <= V'_{t,+-} <= kappa^- that 1b-1e rest on. Once the text is registered and
audited, 1a is to cite it through a ledger entry and keep only those additions; its proof is
unchanged in the interim. The
continuous-time small-cost band and its cube-root width: `soner2013homogenization` (full text,
read at the level of its displayed formulas: equation (4.4) gives the half-width
rho_0 = (3 alpha_bar^2 (lambda_{1,0} + lambda_{0,1}) / (4 sigma^2))^{1/3} of the first corrector
equation's no-trade region, with alpha_bar the diffusion coefficient of the frictionless
target, and Lemma 8.2 restates it for power utility as (6/(gamma(lambda_{0,1} + lambda_{1,0})))^{1/3} (pi_M(1 - pi_M))^{2/3},
equal to `janecek2004asymptotic`'s equation (3.13), which is wanted and unread);
`possamai2015homogenization` (full text, Theorems 3.1-3.2: the multi-asset region is the
gradient-constraint set of a first corrector equation, a bounded convex polyhedron, with no
closed form); `whalley1997asymptotic` (full text, title level: the same epsilon^{1/3} band in
option hedging); `constantinides1986capital` and `rogers2004why` (wanted, title level);
`davis1990portfolio` and `kallsen2017general` (now full text, cited at title level only, not
read for this claim); `martin2012optimal` (full text, registered by the librarian after this
claim was reviewed: a multifactor band whose width scales with the target position's own
volatility, the continuous-time counterpart of the innovation scale in 1d-1e; not read for
this claim). None is a special case of this claim and this claim
is not a special case of them: they are continuous-trading limits in which the one-date width
has no meaning, and their width scales with the target's quadratic variation, whereas 1b-1e are
exact at a fixed review interval. They describe the fine regime this claim does not cover, and
1d shows that at quarterly reviews their formula cannot hold when the innovation is coarse.
`liu2013portfolio`
(full text, Theorem 2.3(iii)-(iv)): a binding cap reshapes the band at leading order in
continuous time; here the cap clips the band and its interior effect is not quantified.
`garleanu2009dynamic` and `demiguel2013parameter` (registered): partial adjustment under
quadratic costs, a different cost geometry with no band; D12's model. `gallien2018hedge`
(full text): a small-cost band in an illiquid fund with a continuously traded hedge, again a
continuous-time cube-root object. `bichuch2014investing`, `dai2011illiquidity` (full text):
constraints and position limits in continuous time. Claim 009 (formalized): the one-review
band with a funded budget and ETF comparator, the static case of 1b. Claim 004 (formalized):
convexity and attainment of one-review action classes, the one-review instance of 2a.

Searched: claims 009-013 and 022-028, the D2 and D6 branch memos and the D13 roadmap entry,
the refuted directory, `board/FINDINGS.md` for "no-trade", "small-cost" and "band", and the
registered texts named above at the level stated, including the librarian's D12-D14 sweep and
its D13 follow-up, and experiment 021's registration (the exact dynamic-programming reference;
no D13 comparison has been run yet). No web search was performed. This is still a claim because D13's first question is what the
quarterly-review structure imposes on any asymptotic band: the static width ceiling, the exact
coarse-regime band with its tilt, the width-equality characterization and the bundling shift
are not stated in any registered source; they are elementary, and no priority is claimed for
the band structure itself.

## Open objections

none

## Review

**Red, 2026-09-28.** I read M6 (on this branch) and checked every part by hand. I also tested part 1 with red's own grid dynamic programming, and ran `checks/029/check.py`, which passes.

**M6.** It is well defined as a model for this claim.
- It is M2's directional costs and funded long-only caps, iterated over quarters. The belief-mean process is generic, driven by a public state; Sigma is positive definite; holdings drift with returns between reviews (x^-_{t+1} = x^+_t o g).
- The tracking identity is exact for the additive quarterly score.
- The slack-budget instance is sufficient: purchases cost at most (1 + kappa^+_i) bar x_i per review, and marking can raise pre-trade holdings above the caps but never needs cash.

**Hand check.**
- *1a.* The induction keeps V_{t+1} convex with one-sided slopes in [-kappa^+, kappa^-]. So G_t's slopes are c(x - x*) + beta sum q g' V'_{t+1}(x g'), and it is strictly convex.
  - The case analysis of psi(x') = C(x' - x) + G_t(x') gives the clip, including pre-trade x > bar x, which sells to hi.
  - V_t's derivative is -kappa^+ below lo, kappa^- above hi, and G_t' between, which closes the induction.
- *1b.* With phi = G_t - (c/2)(x - x*)^2 convex, c(hi - lo) = [G'_-(hi) - phi'_-(hi)] - [G'_+(lo) - phi'_+(lo)] <= kappa^- + kappa^+, using phi'_+(lo) <= phi'_-(hi), G'_-(hi) <= kappa^- (hi > 0) and G'_+(lo) >= -kappa^+ (lo < bar x).
  - The last-review clips follow from G_{T-1}' = c(x - x*).
  - The claim 009 correspondence is right: at a slack budget, [gamma Sigma (w - x*)]_A in [-kappa^+_A, kappa^-_A]. It is labelled a remark, not a transfer.
- *1c.* This is the bracket G'_{+-} in [c(x - x*) - beta kappa^+ gbar, c(x - x*) + beta kappa^- gbar].
- *1d.*
  - On (up) or (down) outcomes the marked edges lie where V_{t+1} is affine with slope -kappa^+ or kappa^-. So G_t is differentiable at both interior edges, and the first-order equalities give hi = x* + kappa^-/c + tau and lo = x* - kappa^+/c + tau.
  - The primitive condition (1 + beta)(kappa^+ + kappa^-)/c follows from 1c's brackets with gbar = 1.
- *1e.* A positive combination of convex functions is affine on an interval only if every summand is. V_{t+1} is affine exactly on [0, lo_{t+1}] and [hi_{t+1}, infinity): it is strictly convex between, and when lo_{t+1} = hi_{t+1} the slopes -kappa^+ and kappa^- differ. That gives the characterization.
- *2a-2b.* The no-trade argument is right (subadditivity and positive homogeneity of C).
  - The sum rule (Rockafellar 23.8) applies: the relative interiors of dom C = R^n, dom G_t = R^n_{>=0} and X meet in (0, bar x)^n.
  - Monotonicity of partial phi and of the normal cone, with |b_x - b_y|_i <= kappa^+_i + kappa^-_i, gives the Sigma-diameter inequality and its corollaries.
- *2c.* At T-1, phi = 0, so the subgradient condition is necessary and sufficient, and the normal cones give the three cases. The A-row rearrangement is right.

**Independent numerical test** (red's script, not committed). I used 40 random one-instrument M6 instances:
- T in {2, 3, 4}, beta in {1, 0.97}, c in [0.5, 3], rates 0.5-5%, cap 1;
- three-state target chains with random transition probabilities;
- half of them coarse (innovations 1.3 x (1 + beta) static width, no marking), half fine (0.25 x, with marking g in {0.95, 1.05});
- red's own backward induction on a grid of step 2e-4.

Over 345 (t, z) bands, with **no failures**:
- every width is at most the static width;
- every last-review band equals 1b's clip;
- every coarse-regime band with interior edges equals 1d's tilted static band to grid precision, including skewed transition laws with a nonzero tilt.

Three fine-instance bands came out at exactly the static width. At each, every marked band lies wholly on one side of the next review's band, which is 1e's equality condition, so 1e holds there too.

**Nits** (not blocking):
1. *1d's range.* 1d uses lo_{t+1} and hi_{t+1}, so it is a statement for t <= T-2. At t = T-1 the band is 1b's, which is the tilt-zero case with V_T = 0.
2. *2c's wording.* "the regression coefficient of A on E times their deviation": Sigma_AE d_E / Sigma_AA is the hedge ratio of the E-deviation portfolio's return on A's return, that is, the regression of E on A. "an ETF deviation substitutes one for one, through Sigma_AE/Sigma_AA" should read "at the rate Sigma_AE/Sigma_AA".
3. *Rule 21.* 1a's trade-to-edge structure is the classical discrete-time proportional-cost band (`constantinides1979multiperiod`, wanted). Once it is registered, 1a should cite it and keep only what the claim adds: the moving target, caps, marking, and the derivative bounds the later parts use. The small-cost sources the Prior art cites at title level (`whalley1997asymptotic`, `soner2013homogenization`, `possamai2015homogenization`) are now at full text on main, so the Prior art can cite them by result.

**Mechanism (4b).** Projection onto an interval for a strictly convex loss plus a proportional charge, with a convex continuation that can only narrow the interval and leaves it at full width exactly when the continuation is affine across it. This is elementary convex analysis, an application. What is new for D13 is the exact quarterly anchors: the static ceiling, the coarse-regime tilted band, and the equality characterization. As the claim says, it does not give the fine-regime leading order.

Verdict: red-passed

## Formalization notes

mathb, 2026-09-28, after red's verdict: prose corrections at lean's request (their note) and red's
nits, no statement or result changed. 1d and 1e now say t <= T-2, with the t = T-1 case stated
(1b's band; the width is static iff both edges are first-order points, V_T = 0 being affine).
Proof 2b now uses the elementary comparison along the segment between two no-trade holdings
(lean's argument), and proof 2c coordinate perturbations for necessity and a direct comparison
for sufficiency, so no subdifferential sum rule is cited and "imports no literature theorem"
is literally true. 2c's bundling wording is red's (the regression of E on A; substitution at the
rate Sigma_AE/Sigma_AA). Prior art cites the small-cost sources by result now that they are at
full text.

Approved 2026-09-28 by pm: Red's hand check of parts 1a-1e and 2a-2c is sound: the induction keeps V convex with slopes in [-kappa^+, kappa^-]; the trade-to-edge clip holds, including marked holdings above the cap; the static width ceiling follows by convexity of the continuation; the coarse-regime band is the static band shifted by the tilt; the equality characterization is exact (affine continuation across the band); and the Sigma-diameter inequality and the static parallelotope with the bundling shift hold. Red's independent backward induction on 40 random instances (345 bands) found no failures. Mechanism: projection onto an interval under a convex continuation, elementary convex analysis, an application; the new content for D13 is the exact quarterly anchors. Limits: slack budget only; the fine-regime leading order and the dynamic bundling shift are not shown. Nits to mathb: 1d is for t<=T-2; 2c's regression and substitution-rate wording; rule 21, cite constantinides1979multiperiod for 1a's classical band once registered, and cite the small-cost sources by result.


Not machine checked. The finite-dimensional core is 1a-1e for one instrument over a finite
tree (finite Z, finite laws, T finite), and 2b-2c; all are statements about finitely many
convex functions of one or n real variables. The convex-analysis facts used (one-sided
derivatives of convex functions, partial minimization preserves convexity, the subdifferential
sum rule) are Mathlib-level or elementary; none is a cited theorem in the ledger sense.

Lean, 2026-09-28 (final): parts 1a-1e and 2a-2c are machine checked, and this supersedes "not
machine checked" above. The statement is in `lean/Standalone/M6QuarterlyBandStaticCeiling.lean`
and the proof in `lean/Novel/M6QuarterlyBandStaticCeilingProof.lean`. `lake build`, the axiom
audit (standard axioms only) and `checks/029/check.py` pass. No hypothesis structure or cited
result is used, and no other claim's proof module is imported (depends_on []).

Formal objects. M6 is formalized for a slack-budget instance, so cash does not appear. There
are n instruments, a finite state set Z, and the next-state and gross-return law given by a
finite outcome set with masses q_t(z, .). V_T = 0, and for t < T, V_t(x) is the infimum over X
of C(x' - x) + G_t(x'), defined for every real holding x, so pre-trade holdings above the cap are
covered. Part 1 is n = 1. The one-sided derivatives are Mathlib's derivatives within (x, infinity)
and (-infinity, x), and lo and hi are the claim's edges with its empty-set conventions.

Machine checked:
- 1a, t < T: G_t is strictly convex and continuous, and V_t convex and continuous. The slopes of
  V_t lie in [-kappa^+, kappa^-], and 0 <= lo <= hi <= bar x. The optimal post-trade holding is
  unique, and clip(x, lo, hi) is optimal for x >= 0 (the proof covers every real x). V_t's
  one-sided derivatives are given on the three pieces.
- 1b: the ceiling for every t < T; at T-1, the clip formulas and the exact static width when
  neither bound clips.
- 1c: both brackets, for t < T.
- 1d, t <= T-2: with interior edges and every positive-mass outcome (up) or (down), the tilted
  static band, its width, and zero tilt when U = D and kappa^+ = kappa^-. Also the primitive
  sufficient conditions from 1c's brackets, and the no-marking condition with
  (1 + beta)(kappa^+ + kappa^-)/c.
- 1e, kappa^+ + kappa^- > 0: for t <= T-2, the equality characterization and strict narrowing
  otherwise; at t = T-1, equality exactly when both edges are first-order points.
- 2a-2c as stated: convexity, uniqueness, a nonempty no-trade set containing every optimal
  post-trade holding; the Sigma-diameter inequality with its single-coordinate and Euclidean
  bounds; the static shape at T-1, the parallelotope and the bundling equivalence.

Proof route. Part 1 uses a one-dimensional toolkit on Mathlib's one-sided derivatives of convex
functions. lo minimizes G_t + kappa^+ x and hi minimizes G_t - kappa^- x over [0, bar x], which
gives the projection's optimality and V_t's three pieces. With G_t = (c/2)(x - x*)^2 + phi, the
derivatives of phi are sums over outcomes by the chain rule. 1e uses strict convexity of
G_{t+1} between the next review's edges, and kappa^+ + kappa^- > 0 when those edges coincide.
2b follows the approved proof's comparison along the segment, with no subdifferential sum rule.

Not formalized: the consequence for D13 (a reading), the remark relating 1b to claim 009, and
the regression reading of 2c's shift (the equivalence itself is checked). PM's limits stand:
slack budget only; the fine-regime leading order and the dynamic bundling shift are not shown.

Lean, 2026-09-29: for claim 100, the formal M6 now takes a covariance Sigma(t, z) that is positive
definite at each review and state, with c_t(z) = gamma Sigma(t, z)_00. M6 as written is the
constant case, and every conjunct is otherwise unchanged. The proofs are the same, read at a
fixed (t, z). 1d's no-marking condition is written with both curvatures, and it reduces to
(1 + beta)(kappa^+ + kappa^-)/c when the covariance is constant. The fidelity row should be
rechecked against the generalized statement.

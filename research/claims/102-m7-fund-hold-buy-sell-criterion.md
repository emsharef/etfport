---
id: 102
title: "When a fund is held, bought or sold versus adjusted through ETFs: the one-review criterion in the inputs, exact under frictionless spanning ETFs, bracketed by the ETF re-hedge cost otherwise, with the budget and cap corrections and the multi-review bracket"
status: formalized
model_version: M7
depends_on: [9, 029, 100, 104]
axioms_used: [AX-13]
formal: lean/Standalone/M7FundHoldBuySellCriterion.lean
direction: D15
---
## Statement

D15's criterion (b), in the inputs: net alpha and its precision, fund and ETF costs and fees,
factor spanning, starting holdings and constraints. The setting is one quarterly review of the
general fund-of-funds model with proportional costs; the multi-review case is bracketed at the
end from claims 029 and 100. It builds on claim 009's one-quarter band (one fund, funded), claim
029's static parallelotope, and the exposure-and-fund coordinates of claim 030 (quadratic costs,
cited for the coordinates only). It imports no literature theorem.

**Setting.** One review of an M7 instance (`model/SPEC.md` M7; the last review of any horizon, or
T = 1): N >= 1 funds and M >= 1 ETFs, n = N + M, K factors, loadings B = [B^A; B^E], belief mean
m = (lambda_hat, alpha_hat) with posterior covariance P = diag(P^lambda, P^alpha) (M5's reference
case: decoupled filter, block-diagonal Sigma_z), signed ETF drag c^E, predictive moments

```
mu = (alpha_hat + B^A lambda_hat,  B^E lambda_hat - c^E),
Sigma = B Sigma~_f B' + diag(V, Sigma_E),   Sigma~_f = Sigma_f + P^lambda,   V = Sigma_A + P^alpha,
```

gamma > 0, directional rates kappa^+_i, kappa^-_i in [0, 1), caps 0 <= x <= bar x, pre-trade
holdings x^- = (x^{A-}, x^{E-}) and cash h^- >= 0, cost C(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-],
funded cash k(x) = h^- - 1'(x - x^-) - C(x - x^-) >= 0. The review's problem is

```
maximize  mu' x - (gamma/2) x' Sigma x - C(x - x^-)   over  0 <= x <= bar x,  k(x) >= 0,
```

M7's quarterly score, with estimation risk charged through P. Write g(x) = mu - gamma Sigma x for
the smooth marginal, g_i its coordinates, and for each instrument the *trade-sign slope set*
T_i(x) = {kappa^+_i} if x_i > x^-_i, {-kappa^-_i} if x_i < x^-_i, [-kappa^-_i, kappa^+_i] if x_i = x^-_i.

### Part 1. The exact criterion at an optimum (any inputs)

An optimum exists and, since Sigma is positive definite, is unique. A feasible x is optimal if
and only if there are eta >= 0 with eta k(x) = 0 and slopes t_i in T_i(x) such that, for every i,

```
R_i(x) = g_i(x) - eta - (1 + eta) t_i    is  = 0 if 0 < x_i < bar x_i,   <= 0 if x_i = 0,   >= 0 if x_i = bar x_i
```

(both signs allowed when 0 = x_i = bar x_i). Read per instrument at the optimum x:

```
fund i is bought   iff  g_i(x) = eta + (1 + eta) kappa^+_i   with x^-_i < x_i < bar x_i  (a purchase up to the cap gives g_i(x) >= that value),
fund i is sold     iff  g_i(x) = eta - (1 + eta) kappa^-_i   with 0 < x_i < x^-_i        (a sale to zero gives g_i(x) <= that value),
fund i is held     iff  g_i(x) in [eta - (1 + eta) kappa^-_i,  eta + (1 + eta) kappa^+_i]   (interior),
                        g_i(x) <= eta + (1 + eta) kappa^+_i at x_i = 0,   g_i(x) >= eta - (1 + eta) kappa^-_i at x_i = bar x_i.
```

The same lines hold for each ETF. eta is the cash shadow price: zero when the budget is slack,
and then the criterion is claim 029's 2c. This is claim 009's marginal condition for n
instruments; it is exact but implicit, since g is evaluated at the optimum.

### Part 2. The ETF-optimized test: is any fund traded? (explicit in the inputs)

Let x_E be an optimum of the same problem with every fund fixed at x^{A-} (the ETF-only class),
and let I be the set of eta >= 0 compatible with part 1 at x_E on the ETF coordinates and the
budget (a closed interval [lo, hi], computable from the ETF marginals as in claim 009: I = {0}
when k(x_E) > 0). Then

```
no fund is traded at the full optimum
   iff  there is eta in I such that every fund i satisfies part 1's held condition at x_E:
        g_i(x_E) in [eta - (1 + eta) kappa^-_i, eta + (1 + eta) kappa^+_i], with the one-sided forms at 0 and bar x_i.
```

If for some fund i and every eta in I the held condition fails at x_E, the full optimum trades
at least one fund; it need not be fund i, because funds interact through Sigma. The per-fund
direction is settled in parts 3-4.

### Part 3. Frictionless spanning ETFs: the exact per-fund band in the inputs

Assume M = K with B^E invertible (ETFs span the factors), write R = (B^E)^{-1} and, for each fund
i, the *netting vector* r_i = R' (B^A_i)' in R^M (the ETF trade that offsets one unit of fund i's
factor exposure); assume the ETFs are frictionless, kappa^+_E = kappa^-_E = 0, Sigma_E = 0, c^E = 0;
assume V is diagonal with entries v_i = sigma^2_{A,i} + p_i (fund residual variance plus alpha
posterior variance, M5's reference case without the pooled component); assume x^- <= bar x
(marking can carry an incumbent above its cap, and then the clip below is not claimed); and
assume that at the optimum the budget is slack and every ETF is strictly inside its box,
0 < x^E_j < bar x_{E,j} (checked ex post). When an ETF sits at zero or at its cap, part 3's
rule is not claimed (part 5(b), Not shown). Then the optimum is explicit:

```
exposure:   y* = (gamma Sigma~_f)^{-1} lambda_hat                       (total factor exposure, set through the ETFs),
fund i:     x_i = clip( x^-_i,  lo_i,  hi_i ) clipped to [0, bar x_i],   lo_i = (alpha_hat_i - kappa^+_i)/(gamma v_i),   hi_i = (alpha_hat_i + kappa^-_i)/(gamma v_i),
ETFs:       x^E = R' ( y* - (B^A)' x^A ).
```

So, in the inputs,

```
fund i is bought   iff  alpha_hat_i - gamma v_i x^-_i  >  kappa^+_i   and  x^-_i < bar x_i     (up to lo_i, or to its cap),
fund i is sold     iff  alpha_hat_i - gamma v_i x^-_i  <  -kappa^-_i  and  x^-_i > 0           (down to hi_i, or to zero),
fund i is held     iff  neither: -kappa^-_i <= alpha_hat_i - gamma v_i x^-_i <= kappa^+_i, or the fund is at its cap
                        with alpha_hat_i - gamma v_i bar x_i >= -kappa^-_i, or at zero with alpha_hat_i <= kappa^+_i,
```

(a fund at its cap cannot be bought and one at zero cannot be sold, whatever its marginal),

and its factor exposure is adjusted through the ETFs one for one, by the netting trade -r_i per
unit of fund traded, on top of the exposure trade R'(y* - y^-) that responds to premium beliefs
alone. In particular a fund with no incumbent holding is bought iff its net alpha estimate
exceeds its purchase rate, alpha_hat_i > kappa^+_i; a fund is sold out entirely iff
alpha_hat_i <= -kappa^-_i; and premium beliefs, their precision and the factor loadings play no
role in the fund decision. Alpha precision enters only through v_i, which sets the size of the
trade, not whether one is made. Holding at zero is the rule whenever alpha_hat_i <= kappa^+_i,
whatever the fund's loadings.

### Part 4. ETF frictions: the exact bracket and the effective threshold

Keep spanning and diagonal V, drop the frictionless assumptions, keep the budget slack, and
keep every ETF strictly inside its box at the optimum, 0 < x^E_j < bar x_{E,j}. Define
for each fund i the *re-hedge costs* of a unit purchase and a unit sale,

```
h^+_i = sum_j [ (r_ij)^+ kappa^-_{E,j} + (r_ij)^- kappa^+_{E,j} ],      h^-_i = sum_j [ (r_ij)^+ kappa^+_{E,j} + (r_ij)^- kappa^-_{E,j} ],
```

(the ETF trading cost of netting the fund's factor by-product: a fund purchase adds exposure,
which is netted by selling the ETFs with r_ij > 0 and buying those with r_ij < 0, so h^+_i
carries the ETFs' sale rates on the positive weights; a fund sale is netted the other way),
and the *reduced marginal*

```
A_i(x) = alpha_hat_i + r_i' c^E - gamma v_i x_i + gamma r_i' Sigma_E x^E,
```

net alpha plus the ETF fees the fund's by-product exposure saves, less the fund's own risk
charge, plus the ETF residual risk the netting trade carries. Then at the optimum x,

```
bought  =>  A_i(x) >= kappa^+_i - h^-_i,        sold  =>  A_i(x) <= -kappa^-_i + h^+_i,
held (interior)  =>  -kappa^-_i - h^-_i <= A_i(x) <= kappa^+_i + h^+_i,
```

and if the ETFs re-hedge the fund exactly (every ETF j with r_ij != 0 is traded, in the direction
the netting requires), then an interior purchase (x^-_i < x_i < bar x_i) has
A_i(x) = kappa^+_i + h^+_i and a purchase to the cap has A_i(x) >= kappa^+_i + h^+_i; under the
sale re-hedge an interior sale has A_i(x) = -kappa^-_i - h^-_i and a sale to zero has
A_i(x) <= -kappa^-_i - h^-_i: the fund's effective threshold is its own rate plus the ETF
re-hedge cost. The converse fails: a fund held at its band edge (g_i(x) = kappa^+_i at
x_i = x^-_i) while the exposure trade itself sends the ETFs in the netting direction has
A_i(x) = kappa^+_i + h^+_i and is not bought, so the equality is a necessary condition of an
interior purchase, not a test for one; the sufficient conditions below are the test. More
generally, if every ETF j with r_ij != 0 is traded, in whatever directions, each slope is pinned
(t_j = kappa^+_{E,j} if ETF j is bought, t_j = -kappa^-_{E,j} if sold) and the threshold is exact
in the same sense: an interior purchase has A_i(x) = kappa^+_i - sum_j r_ij t_j (a purchase to
the cap, >=) and an interior sale has A_i(x) = -kappa^-_i - sum_j r_ij t_j (a sale to zero, <=),
so the fund's effective rate is its own rate plus sum_j |r_ij| times the rate of ETF j's own
trade, counted positive when that trade is the one the netting requires and negative otherwise;
the threshold's position in the bracket is set by which ETFs trade with the netting and which
against it. Sufficient conditions
at the incumbent, when Sigma_E = 0: if A_i(x^-) > kappa^+_i + h^+_i and x^-_i < bar x_i, every
optimum buys fund i; if A_i(x^-) < -kappa^-_i - h^-_i and x^-_i > 0, every optimum sells it. So the ETF re-hedge costs bound the
uncertainty of the fund's threshold: with costless ETFs (h_i = 0) part 3's rule is exact, and
with costly ETFs the threshold for buying fund i lies in [kappa^+_i - h^-_i, kappa^+_i + h^+_i]
around A_i, attained at the upper end when the ETFs re-hedge the purchase and at the lower end
when the ETFs are traded the other way (as they are when the exposure trade itself sells the
ETFs the netting would sell); between, the ETFs are idle inside their own bands (then the fund's factor
by-product is absorbed as an exposure deviation, and its exposure value enters the fund's
marginal through r_i' g_E). Fees enter as r_i' c^E: a fund whose by-product exposure would
otherwise be bought through fee-charging ETFs gains their fee, per unit, in its reduced alpha.

### Part 5. Constraints: the budget and the bounds

(a) *Binding budget.* With eta > 0 (k(x) = 0 at the optimum), parts 1 and 2's thresholds on the
smooth marginal g_i become eta + (1 + eta) kappa^+_i on the purchase side and eta - (1 + eta) kappa^-_i on
the sale side (claim 009's scaling): a binding cash constraint raises the marginal a purchase
needs by the shadow price plus its share of the rate, and lowers the marginal a sale needs by
the same. Parts 3 and 4 are stated on the fund's reduced marginal, which absorbs the ETF
marginals, and there the shift is eta (1 - sum_j r_ij), not eta: every interior frictionless
ETF's marginal equals eta at the optimum, so the fund's premium part B^A_i e equals
eta sum_j r_ij, the cash its by-product saves: a netted unit of the fund uses cash 1 - sum_j r_ij,
not 1, so the shadow price raises the net alpha a purchase needs by eta times that net cash,
which is negative when the netting trade frees more cash than the fund costs. In part 3 (frictionless spanning ETFs, every ETF
interior) a fund is therefore bought iff alpha_hat_i - gamma v_i x^-_i > eta (1 - sum_j r_ij) + (1 + eta) kappa^+_i
and sold iff alpha_hat_i - gamma v_i x^-_i < eta (1 - sum_j r_ij) - (1 + eta) kappa^-_i, and its
clip holds with the shifted endpoints
lo_i = (alpha_hat_i - eta (1 - sum_j r_ij) - (1 + eta) kappa^+_i)/(gamma v_i) and
hi_i = (alpha_hat_i - eta (1 - sum_j r_ij) + (1 + eta) kappa^-_i)/(gamma v_i) at the optimum's eta,
the exposure target being y*(eta) = (gamma Sigma~_f)^{-1} (lambda_hat - eta R 1). In part 4 the
ETF slopes scale likewise, and its brackets hold with A_i replaced by
A_i - eta (1 - sum_j r_ij) and every rate multiplied by (1 + eta). (b) *Long-only and caps.* A fund at zero is held unless
the purchase condition holds; a fund at its cap is held unless the sale condition holds; the
band clips as in part 3. An ETF at zero or at its cap has a one-sided marginal, so it drops out
of the netting: neither part 3's closed form (whose netting trade may need to short it) nor part
4's bracket is claimed then. This is the common long-only case (experiment 024 has ETFs at zero
in 74% of instrument-quarters) and is Not shown.

### Part 6. Multi-review bracket (one instrument's reduced problem)

In part 3's separated setting over a horizon with discount beta in (0, 1] and pure-learning
marking, each fund's problem is a one-instrument M7 tracking problem with curvature
c_t = gamma v_{i,t} and target alpha_hat_{i,t}/c_t, so claims 029 and 100 apply: the fund's band
at every review lies inside the one-review band of part 3 (the static width ceiling), is that
band exactly at the last review, and from claim 029's edge brackets

```
a fund with no incumbent holding is bought at review t  only if  alpha_hat_{i,t} > (1 - beta) kappa^+_i,
                                                          surely if  alpha_hat_{i,t} > kappa^+_i + beta kappa^-_i,
```

and, mirrored at the cap where the risk charge c_t bar x_i does not vanish, a fully held fund
(x^-_i = bar x_i) is sold at review t only if alpha_hat_{i,t} - c_t bar x_i < -(1 - beta) kappa^-_i
(it stays at its cap, hi_t = bar x_i, when alpha_hat_{i,t} - c_t bar x_i >= -(1 - beta) kappa^-_i);
and a fund is sold out entirely from any incumbent (hi_t = 0) only if alpha_hat_{i,t} <= -(1 - beta) kappa^-_i
and surely if alpha_hat_{i,t} < -(kappa^-_i + beta kappa^+_i), the exact mirror of the purchase
from zero, since the risk charge vanishes at zero on both sides.
Looking ahead lowers the alpha a purchase needs, from the one-review kappa^+_i to no less than
(1 - beta) kappa^+_i, because the position persists; the exact threshold depends on the
innovation law and the horizon (claim 100's coarse and fine regimes).

**Reading for D15** (not a further theorem). Criterion (b) in the inputs: with spanning ETFs the
fund decision is a band in the fund's net alpha, of width its round-trip rate widened by the
ETF re-hedge cost, centred at the fund's risk charge gamma v_i x^-_i on its current holding;
factor exposure is adjusted through the ETFs and does not enter the fund decision except through
the re-hedge cost and the fee credit. Starting holdings enter through the risk charge and the
sign of the trade; the budget through eta; the bounds by clipping; learning through v_i (size)
and, over several reviews, through the lower purchase threshold. What premium error does when
ETFs do not span is criterion (d).

## Proof

### 1. Exact criterion

Existence and uniqueness: the feasible set is nonempty (x^- is feasible: k(x^-) = h^- >= 0),
closed and bounded, the objective continuous and strictly concave (Sigma positive definite,
costs convex). The criterion is claim 009's multiplier condition in n dimensions, obtained from
the polyhedral KKT theorem, ledger entry AX-13 (`rockafellar1970convex`, Theorems 27.4 and
28.2-28.3, cited), applied to the lifted problem. Lift the cost: with a scalar y and one constraint c'(x - x^-) <= y per
sign vector c in prod_i {-kappa^-_i, kappa^+_i}, the budget 1'(x - x^-) + y <= h^-, and the box,
the lifted problem maximizes the differentiable concave quadratic mu'x - (gamma/2)x'Sigma x - y
over a polyhedron, and its optimal x are exactly the original optima (at an optimum y = C(x - x^-)).
AX-13's hypotheses hold for the lifted problem: its objective, a concave quadratic in x minus
y, is concave and finite on all of R^{n+1}, so the entry's constraint qualification is
automatic; its feasible set is a nonempty polyhedron (finitely many linear inequalities; x^-
with y = C(0) is feasible). AX-13 (Theorems 28.2-28.3) then gives: a feasible point is optimal
iff its gradient is a combination, with nonnegative multipliers that vanish on slack
constraints, of the tight constraints' normals. Writing eta >= 0 for the budget multiplier and
beta_c >= 0 for the tight cost pieces, the y-component gives sum beta_c = 1 + eta, and
t = sum beta_c c/(1 + eta) is a convex combination of tight slope vectors, hence t_i in T_i(x)
coordinatewise (the tight pieces at a bought coordinate all carry kappa^+_i, at a sold one
-kappa^-_i, at an untraded one either endpoint); conversely every t with t_i in T_i(x) is such a
combination (product weights). The x-components give g(x) - eta 1 - (1 + eta) t = R, with R in
the cone of the tight box normals: the three sign cases. Complementary slackness gives
eta k(x) = 0. The per-instrument readings are the cases of T_i(x).

### 2. ETF-optimized test

If some full optimum x* has x*^A = x^{A-}, then x* is feasible for the ETF-only problem, so the
ETF-only optimal value equals the full one and x_E (unique) is x*, a full optimum. Conversely if
x_E is a full optimum, no fund is traded at it. By part 1 applied to the ETF-only problem (the
same lifted problem with the fund coordinates fixed), x_E satisfies the ETF and budget
conditions for exactly the eta in a closed interval I, computable as in claim 009 (I = {0} when
the budget is slack; otherwise the intersection of the intervals each ETF's condition allows).
x_E is a full optimum iff part 1 holds at x_E, that is iff some eta in I also satisfies every
fund's condition with t_i in [-kappa^-_i, kappa^+_i] (zero trade), which is the held condition.
If no eta in I does, x_E is not a full optimum, so the full optimum has x^A != x^{A-}: some fund
is traded.

### 3. Frictionless spanning ETFs

With M = K and B^E invertible, (x^A, x^E) -> (x^A, y) with y = B'x = (B^A)'x^A + (B^E)'x^E is a
linear bijection with x^E = R'(y - (B^A)'x^A). In the reference case with c^E = 0 and Sigma_E = 0,

```
mu'x - (gamma/2) x'Sigma x = lambda_hat' y - (gamma/2) y' Sigma~_f y + sum_i [ alpha_hat_i x_i - (gamma/2) v_i x_i^2 ],
```

using (B^E lambda_hat)'x^E + (B^A lambda_hat)'x^A = lambda_hat'y and x'(B Sigma~_f B')x = y'Sigma~_f y.
With kappa_E = 0 the cost is sum over funds of kappa^+_i (x_i - x^-_i)^+ + kappa^-_i (x^-_i - x_i)^+.
When the budget and the ETF box do not bind, the problem is the sum of an unconstrained
concave quadratic in y, maximized at y* = (gamma Sigma~_f)^{-1} lambda_hat, and of N independent
one-variable problems on [0, bar x_i], each of which is claim 029's last-review problem with
curvature gamma v_i, target alpha_hat_i/(gamma v_i) and rates kappa^+_i, kappa^-_i, whose
solution is the clip to [lo_i, hi_i] intersected with the box (claim 029's 1a-1b at T-1). The
ETF positions follow from the bijection. The trade readings are the clip's cases, with the box:
the clip rises above x^-_i iff x^-_i < lo_i and x^-_i < bar x_i, that is alpha_hat_i - gamma v_i x^-_i > kappa^+_i
with room above, and falls below it iff x^-_i > hi_i and x^-_i > 0; at the cap the clip stays
iff bar x_i <= hi_i, that is alpha_hat_i - gamma v_i bar x_i >= -kappa^-_i, and at zero iff
0 >= lo_i, that is alpha_hat_i <= kappa^+_i. The netting decomposition x^E - x^{E-} = R'(y* - y^-) - R'(B^A)'(x^A - x^{A-}) = R'(y* - y^-) - sum_i r_i (x_i - x^-_i)
is the bijection applied to the trade.

### 4. Frictions

With Sigma_E and c^E present but Sigma_z block-diagonal, g_E(x) = B^E lambda_hat - c^E - gamma B^E Sigma~_f y - gamma Sigma_E x^E
= B^E e - c^E - gamma Sigma_E x^E with e = lambda_hat - gamma Sigma~_f y, and
g_i(x) = alpha_hat_i + B^A_i e - gamma v_i x_i for a fund. Solving the ETF line for e (B^E
invertible): e = R (g_E + c^E + gamma Sigma_E x^E), hence

```
g_i(x) = alpha_hat_i - gamma v_i x_i + r_i' ( g_E(x) + c^E + gamma Sigma_E x^E ) = A_i(x) + r_i' g_E(x).
```

At the optimum with a slack budget and no ETF bound binding, part 1 gives g_{E,j}(x) = t_j in
T_j(x) subset [-kappa^-_{E,j}, kappa^+_{E,j}], so r_i' g_E(x) lies in [-h^+_i, h^-_i] (the extreme values
of a linear form over the box: the minimum -h^+_i at t_j = -kappa^-_{E,j} for r_ij > 0 and
t_j = kappa^+_{E,j} for r_ij < 0, which are the slopes when every ETF with r_ij > 0 is sold and
every ETF with r_ij < 0 is bought, the re-hedge of a fund purchase; the maximum h^-_i at the
opposite corners, the re-hedge of a fund sale). Since g_i(x) = A_i(x) + r_i' g_E(x), the fund's
own condition in part 1 (eta = 0) gives: bought, g_i = kappa^+_i for an interior purchase and
g_i >= kappa^+_i for a purchase to the cap, so A_i = kappa^+_i - r_i' g_E >= kappa^+_i - h^-_i,
with A_i = kappa^+_i + h^+_i (interior) or >= (at the cap) under the purchase re-hedge; sold,
g_i = -kappa^-_i for an interior sale and <= for a sale to zero, so A_i <= -kappa^-_i + h^+_i, with
A_i = -kappa^-_i - h^-_i (interior) or <= (at zero) under the sale re-hedge; held interior,
g_i in [-kappa^-_i, kappa^+_i], so A_i in [-kappa^-_i - h^-_i, kappa^+_i + h^+_i]. These are the
displayed implications. The converse's counterexample is part 1's held case with t_i at the
endpoint kappa^+_i: g_i = kappa^+_i is allowed at x_i = x^-_i, and if the ETFs' own exposure trade
pins every g_{E,j} at the netting corner then A_i = kappa^+_i + h^+_i with the fund untraded. The
pinned-slope thresholds are the same identity with g_{E,j} = t_j for every j with r_ij != 0
(part 1's traded cases at eta = 0) and g_i = kappa^+_i (interior purchase) or -kappa^-_i
(interior sale), the cap and zero cases giving the inequalities; the exact
re-hedge case is t_j = -kappa^-_{E,j} for r_ij > 0 and kappa^+_{E,j} for r_ij < 0, which gives
sum_j r_ij t_j = -h^+_i. Sufficiency at the incumbent when Sigma_E = 0: suppose A_i(x^-) > kappa^+_i + h^+_i
and let x* be the optimum with x*_i <= x^-_i. Consider the feasible direction of buying
epsilon of fund i and trading -epsilon r_i in the ETFs (the total exposure is unchanged, so the
exposure term of the objective is unchanged; feasible for small epsilon since no bound binds
on these coordinates). The objective changes by epsilon [g_i(x*) - r_i' g_E(x*)] minus the
cost of the move, and the cost is at most epsilon (kappa^+_i + h^+_i) (each coordinate's marginal
cost is its slope in the move's direction, at most its rate). By the identity,
g_i(x*) - r_i' g_E(x*) = A_i(x*) = alpha_hat_i + r_i' c^E - gamma v_i x*_i >= A_i(x^-) (Sigma_E = 0,
x*_i <= x^-_i), so the change is at least epsilon [A_i(x^-) - kappa^+_i - h^+_i] > 0, contradicting
optimality. The sale case is symmetric.

### 5. Constraints

(a) is part 1 with eta > 0. Under part 3's hypotheses (kappa_E = 0, c^E = 0, Sigma_E = 0, every
ETF interior) part 1 gives g_{E,j} = eta for every ETF, so by part 4's identity
g_i = alpha_hat_i - gamma v_i x_i + eta sum_j r_ij, and the fund's condition
g_i = eta + (1 + eta) kappa^+_i at an interior bought coordinate (g_i = eta - (1 + eta) kappa^-_i
sold, between them held) is the displayed strip on alpha_hat_i - gamma v_i x_i; the clip with
the shifted endpoints follows as in part 3, and g_E = eta 1 solves to y*(eta). For part 4,
r_i' (eta 1 + (1 + eta) t) over the box. (b) is part 1's one-sided cases and part 3's clip.

### 6. Multi-review bracket

Under part 3's assumptions at every review, with pure-learning marking, the horizon objective is
the sum over reviews of the review objective, the exposure part is maximized review by review
(no cost, no state), and each fund's part is a one-instrument M7 problem with curvature
gamma v_{i,t}, target alpha_hat_{i,t}/(gamma v_{i,t}) and its own rates: claim 100's 1b gives claim
029's 1a-1c there. Claim 029's 1c with bar g = 1: lo_t >= x*_t - (kappa^+ + beta kappa^-)/c_t, so
lo_t > 0 when alpha_hat_{i,t} > kappa^+_i + beta kappa^-_i (the sure purchase from zero); and
G'_{t,+}(0) >= c_t (0 - x*_t) - beta kappa^+ = -alpha_hat_{i,t} - beta kappa^+_i, so when
alpha_hat_{i,t} <= (1 - beta) kappa^+_i the right derivative at zero is at least -kappa^+_i and lo_t = 0
(no purchase from zero). At the cap: G'_{t,-}(bar x) <= c_t (bar x - x*_t) + beta kappa^- =
c_t bar x - alpha_hat_{i,t} + beta kappa^-_i, so when alpha_hat_{i,t} - c_t bar x_i >= -(1 - beta) kappa^-_i
the left derivative at the cap is at most kappa^-_i and hi_t = bar x_i (no sale from the cap);
the risk charge c_t bar x_i does not vanish there, unlike at zero. Sold out only if: hi_t = 0
means G'_{t,-}(x) > kappa^-_i for every x in (0, bar x_i], and G'_{t,-}(x) <= c_t x - alpha_hat_{i,t} + beta kappa^-_i
(the continuation's left slope is at most beta kappa^-_i, claim 029's 1a with bar g = 1), so
letting x -> 0 gives alpha_hat_{i,t} <= -(1 - beta) kappa^-_i; at equality a sell-out remains
possible, so the condition is not strict. Sold out surely: claim 029's 1c gives
hi_t <= x*_t + (kappa^- + beta kappa^+)/c_t < 0 when alpha_hat_{i,t} < -(kappa^-_i + beta kappa^+_i),
so the clip of any incumbent lands at zero. The static ceiling is claim 029's 1b transferred by
claim 100.

## Checks

`uv run python checks/102/check.py` (exits non-zero on failure; a check, not a proof). On
random one-review instances (3 funds, 2 ETFs, 2 factors, random loadings with B^E invertible,
random beliefs, precisions, rates, fees, residuals, incumbents and caps; all assumed) solved by
CLARABEL through cvxpy (floating, not a certificate), it checks: part 1's criterion at the
solver's optimum with eta = 0 on slack-budget instances; part 2's ETF-optimized test against
the solver's full optimum; part 3's closed form on frictionless-spanning instances, to solver
tolerance; part 4's bracket at the optimum on friction instances, and the sufficient purchase
and sale conditions at the incumbent when Sigma_E = 0, and the pinned-slope thresholds when
every ETF is traded; part 5(a)'s scaling of part 1 on instances with a binding budget, using
the solver's dual variable as eta; and part 5(a)'s shifted strip, clip and exposure target on
frictionless-spanning instances with a binding budget and interior ETFs.

## Not shown

- Part 3 assumes M = K with B^E invertible, diagonal V (no pooled alpha component), and that
  x^- <= bar x, a slack budget and every ETF strictly inside its box at the optimum; part 4
  keeps spanning, a slack budget and interior ETFs. The case of an ETF at zero or at its cap,
  the common long-only one, is outside parts 3-4: the ETF's marginal is one-sided and the
  netting trade need not be feasible; only parts 1-2 and 5 speak to it. Non-spanning menus are criterion (d) (claim 031's leak enters A_i through B^A J'
  lambda_hat); the pooled prior gives V off-diagonal terms and couples the funds' bands.
- The per-fund direction when ETFs are costly is bracketed, not pinned: the exact threshold
  between kappa^+_i - h^-_i and kappa^+_i + h^+_i depends on which ETFs trade at the optimum,
  which is the solution of the joint problem. Part 4's sufficient conditions assume Sigma_E = 0.
- Part 6 is one-instrument bracketing; with several funds the separated dynamic problems are
  independent only under part 3's assumptions at every review.
- No calibration or magnitude. The criterion is stated in the inputs and the analyst's
  threshold curves check it (note sent).

## Prior art

Mechanism: at an optimum of a concave objective with proportional trading charges, each
instrument's smooth marginal lies in its cost band shifted by the funding multiplier; when a
subset of instruments (ETFs) can offset another's (a fund's) factor exposure exactly and
costlessly, the fund's decision reduces to a one-variable band in its own residual mean over
its own risk, and when the offset costs, the offset's cost is added to the fund's rate at one
extreme and absent at the other.

General results checked: subdifferential optimality with parametric ranging for concave
maximization over a polyhedron (ledger entry AX-13, `rockafellar1970convex`, cited by theorem
number and applied to the lifted problem in part 1's proof; claim 009's mechanism note); `liu2013portfolio` (full text): the
shadow price of a binding constraint scaling a no-trade width, part 5(a)'s mechanism;
`treynor1973security` (full text): funds chosen on alpha over residual variance with the
market held separately, the frictionless content of part 3 (no costs, no bands); claim 030
(approved): the exposure-and-fund coordinates and the three bundling terms under quadratic
costs, of which part 4's fee credit r_i' c^E and residual term are the proportional-cost
counterparts; claim 031 (formalized): the unreachable-direction leak, criterion (d); claim 027
(formalized): two-stage separation, criterion (c); claim 009 (formalized): the one-fund funded
band, part 1's n = 1 case; claim 029 (formalized) and 100 (formalized): the static parallelotope,
the last-review clips and the multi-review brackets. `garleanu2009dynamic` (registered):
partial adjustment, the quadratic-cost analogue. None of these states the per-fund criterion in
the inputs with the re-hedge cost bracket; that is elementary, and no priority is claimed.

Searched: claims 009, 027-031, 029, 100; the D15 roadmap entry and PM's opening note; the rule 22
audit in FINDINGS; the refuted directory; experiments 021-027's registrations. No web search.
This is a claim because D15 asks for criterion (b) as a formula in the inputs, and the
mathematical kill test is whether the cited results already state it: they give the pieces
(the KKT band, the coordinates, Treynor-Black's ratio), not the per-fund rule with its
re-hedge bracket, budget scaling and multi-review bounds.

## Open objections

PM's withdrawal (claim 102): red's required corrections 1-2 made.

## Review

**Red, 2026-09-29.** I checked parts 1-6 by hand, tested parts 2-5 with red's own cvxpy/CLARABEL solver on random instances (not reading `checks/102/check.py`), and ran `checks/102/check.py`, which passes. Every part holds. There are two required corrections, both about scope: which bounds must be slack, and depends_on. There are also three nits.

**Hand check.**
- *Part 1.* The Lagrangian marginal of the budget 1'(x - x^-) + C <= h^- is 1 + t, so the stationarity condition is g - eta 1 - (1 + eta) t in the box normal cone. The per-instrument readings are its cases. The lifted-cost argument is claim 009's.
- *Part 2.* If a full optimum trades no fund, it is feasible and optimal for the ETF-only problem, and so equals the unique x_E. Hence the full optimum trades no fund exactly when x_E satisfies part 1 with the funds' zero-trade slopes, for some eta the ETF-only conditions allow.
- *Part 3.* Under frictionless spanning ETFs with c^E = 0 and Sigma_E = 0, the objective splits into lambda_hat'y - (gamma/2) y'Sigma~_f y plus N one-variable fund problems. Each fund problem is solved by the clip to [lo_i, hi_i] with the displayed endpoints. From x^- = 0 the fund is bought iff alpha_hat > kappa^+. A fund is sold out iff hi <= 0, that is alpha_hat <= -kappa^-.
- *Part 4.*
  - g_E = B^E e - c^E - gamma Sigma_E x^E with e = lambda_hat - gamma Sigma~_f y. Solving for e with R = (B^E)^{-1} gives g_i = A_i + r_i' g_E.
  - Over g_{E,j} in [-kappa^-_{E,j}, kappa^+_{E,j}], r_i' g_E ranges over [-h^+_i, h^-_i] with h^+_i and h^-_i as displayed. The bracket follows.
  - The sufficiency proof works: along the direction (buy fund i, trade -r_i in the ETFs), exposure is unchanged, the objective gains A_i, and the cost is at most kappa^+_i + h^+_i. A_i(x*) >= A_i(x^-) when x*_i <= x^-_i and Sigma_E = 0.
- *Part 5(a).* With eta > 0, g_{E,j} = eta + (1 + eta) t_j, so g_i = A_i + eta sum_j r_ij + (1 + eta) r_i' t. A purchase then gives A_i - eta (1 - sum_j r_ij) in (1 + eta)[kappa^+ - h^-, kappa^+ + h^+], as stated.
- *Part 6.* Under part 3's separation at every review, each fund is a one-instrument M7 problem with pure-learning marking. Claim 029's 1c brackets give the two purchase-from-zero thresholds: lo_t > 0 if alpha_hat > kappa^+ + beta kappa^-, and lo_t = 0 if alpha_hat <= (1 - beta) kappa^+, because then G'_{t,+}(0) >= -alpha_hat - beta kappa^+ >= -kappa^+.

**Independent numerical tests** (red's script, not committed).
- *Instances.* 3 funds, 2 ETFs, 2 factors, random B^E with a dominant diagonal, random fund loadings, beliefs, residual and alpha variances, rates up to 100 bp for funds and 20 bp for ETFs, fees, incumbents, caps and budgets. Each is solved to 1e-11 gaps. Only instances whose optimum has every ETF strictly inside its box are used for parts 3-5.
- *Part 3.* 161 frictionless instances with a slack budget: the fund clip and the ETF netting x^E = R'(y* - B^A'x^A) match the solver to 1e-6 and 1e-5 on every coordinate.
- *Part 4.* 286 instances with ETF costs, fees and (in half) ETF residual risk: the bought, sold and held brackets on A_i hold for every fund.
- *Part 4 sufficiency.* In the half with Sigma_E = 0, the incumbent conditions occur 62 times (buy) and 89 times (sell), and every optimum trades in the stated direction.
- *Part 5(a).* 215 binding-budget instances, with eta taken from the solver's dual: the scaled bracket, with A_i - eta (1 - sum_j r_ij) and rates times (1 + eta), holds for every fund.
- *Part 2.* 300 slack-budget instances: the ETF-optimized test agrees with whether the full optimum trades a fund, with no disagreement.

**Required correction 1 (which bounds must be slack).**
- Parts 3 and 4 assume "the budget and the ETF caps do not bind". The Setting calls the whole box 0 <= x <= bar x "caps", but "caps" also reads as the upper bounds only. Under that reading both parts are false whenever an ETF sits at zero:
  - part 3's closed form needs x^E = R'(y* - B^A'x^A) >= 0, which fails when netting a fund's by-product would short an ETF;
  - part 4's bracket needs g_{E,j} in [-kappa^-, kappa^+], which fails at a zero bound, where the marginal is one-sided.
- At calibrated long-only instances that is the common case: experiment 024 has ETFs at zero in 74% of instrument-quarters. Part 5(b) already sends it to Not shown.
- Please state in parts 3 and 4 that every ETF is strictly inside (0, bar x_E) at the optimum, and that part 3's rule is otherwise not claimed.
- Part 4's sufficiency statement also needs x^-_i < bar x_i for the purchase and x^-_i > 0 for the sale.

**Required correction 2 (depends_on).** Part 1's Proof rests on claim 009's finite-cone lemma, and Prior art names claim 030 for the coordinates. `depends_on: [029, 100]` should add 9, since claim 009's argument is used as a lemma. Lean may import only the depends_on claims (Q-04), which is the precedent from claims 031 and 034.

**Nits.**
- In part 1's readings, "bought iff g_i(x) = eta + (1 + eta) kappa^+_i" holds for an interior x_i. A purchase up to the cap gives g_i >= that value. The sale to zero is the mirror.
- Not shown says the exact threshold lies "between kappa^+_i - h^+_i and kappa^+_i + h^+_i". Part 4 proves [kappa^+_i - h^-_i, kappa^+_i + h^+_i]. Please correct the lower end.
- Part 3's "clip(x^-_i, lo_i, hi_i) clipped to [0, bar x_i]" presumes x^-_i <= bar x_i, which the funded setting allows to fail after marking. Please say so.

**Mechanism (4b).** The claim reads a KKT band per instrument (claim 009) in the exposure-and-fund coordinates (claim 030's, with proportional costs). The offsetting instrument's slopes then bracket the fund's effective rate: the re-hedge cost at one extreme, and a credit at the other. This is elementary, as the claim says. What is new for D15 is criterion (b) written in the inputs: the band alpha_hat_i - gamma v_i x^-_i against [-kappa^-_i, kappa^+_i] widened by h^+_i and h^-_i, with the budget scaling and the multi-review thresholds (1 - beta) kappa^+ and kappa^+ + beta kappa^-.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's required correction 1. Parts 3 and 4 need every ETF strictly inside (0, bar x_E) at the optimum; read as upper bounds only, both fail whenever an ETF sits at zero, the common long-only case. Mathb restates the hypotheses, adds 9 to depends_on and fixes the nits, and red records a fresh verdict.

**Red, 2026-09-29, on the change since the withdrawal (e234df74).** The part 1 proof now cites ledger entry AX-13 (`rockafellar1970convex` Theorems 27.4 and 28.2-28.3, audited) on the lifted problem instead of outlining claim 009's finite-cone argument. The hypotheses are checked correctly: the objective is a concave quadratic in x minus y, finite on all of R^{n+1}, so AX-13's constraint qualification holds automatically, and the feasible set is a nonempty polyhedron. No result changed.
- Red's required corrections 1-2 are not yet made: ETF interiority in parts 3-4, and depends_on 9 (now partly covered by AX-13 in axioms_used). PM's withdrawal marker is absent.
- Following PM's recheck note (Q-11), red records no new verdict here. It will do so when mathb's revision lands.

**Red, recheck of mathb's revision (857ed54c), 2026-09-29.** Both required corrections and the three nits are made correctly, and no result changed. Red's earlier tests (parts 2-5 on red's own solver) used only instances with every ETF interior, so they stand under the restated hypotheses.
- *Correction 1.*
  - Parts 3 and 4 now assume every ETF strictly inside its box at the optimum, 0 < x^E_j < bar x_{E,j}, and part 3 also x^- <= bar x.
  - The case of an ETF at zero or at its cap is excluded from both and sent to part 5(b) and Not shown, noted as the common long-only case.
  - Part 4's sufficient conditions carry x^-_i < bar x_i (buy) and x^-_i > 0 (sell).
- *Correction 2.* depends_on is [9, 029, 100], and AX-13 stays in axioms_used for part 1's polyhedral KKT step, which red checked above.
- *Nits.* Part 1's "bought iff" is for an interior x_i, with the cap reading g_i >= eta + (1 + eta) kappa^+_i and the zero reading for sales. Not shown's threshold lower end is kappa^+_i - h^-_i. Part 3's x^- <= bar x is stated.
- `checks/102/check.py` passes on main.

Verdict: red-passed


**Red, text check of the post-approval changes, 2026-09-29.** Part 5(a) on main matches red's tests:
- the eta shift on g_i; part 3's strip and clip endpoints shifted by eta (1 - sum_j r_ij), with (1 + eta) rates; y*(eta) = (gamma Sigma~_f)^{-1}(lambda_hat - eta R 1), which is the interior ETF lines g_E = eta 1. Red's random instances matched the netted form to 1e-8 bp, and experiment 034's curve 3 to 3.8e-9;
- part 4's pinned-slope threshold A_i = kappa^+_i - sum_j r_ij t_j, which is red's experiment 034 curve 2 finding (position = sold share of |r| to 2.5e-6).

Mathb's pending pass (mathb/claim102-lean-edges, 23f03ea7) also checks out:
- 104 in depends_on;
- part 3's box readings, which are the strip-with-box of red's curve 1, 6,313 of 6,313;
- part 6's cap side. Red's exact DP on 1,632 (review, cell) pairs, from caps 0.25 and 1, never sells from the cap above alpha - c_t bar x = -(1 - beta) kappa^-. It sells out to zero on all 487,512 belief rows below -(kappa^- + beta kappa^+).

No result changed. The approval stands.
## Formalization notes

Approved 2026-09-29 by pm: Red's recheck of mathb's revision (857ed54c) is sound. Parts 3-4 assume every ETF strictly inside its box at the optimum (and x^- <= bar x), with ETFs at zero or at their cap, the common long-only case, sent to part 5(b) and Not shown; part 4's sufficiency carries x^-_i < bar x_i and x^-_i > 0; depends_on [9, 029, 100]; part 1 cites AX-13 (polyhedral KKT) and checks only its hypotheses; the nits are made and the check passes. Red's solver tests used interior-ETF instances only, so they stand: part 3's closed form 161/161, part 4's brackets on 286, sufficiency, the budget scaling on 215, and part 2 on 300. Mechanism: claim 009's KKT band in claim 030's exposure-and-fund coordinates, with ETF slopes bracketing the fund's effective rate, an application. New for D15 criterion (b): the hold/buy/sell criterion in the inputs. Limit: the at-zero ETF case is not covered.


mathb, 2026-09-29, after PM's withdrawal of the verdict (re-issued note; the first attempt's
edits never reached main): red's required corrections and nits made. Parts 3 and 4 now assume
every ETF strictly inside its box at the optimum (and part 3 x^- <= bar x), with the at-zero ETF
case sent to part 5(b) and Not shown; part 4's sufficient conditions carry x^-_i < bar x_i and
x^-_i > 0; depends_on adds claim 009 (its multiplier criterion is part 1's, through AX-13);
part 1's "bought iff" is for an interior x_i with the cap case stated; Not shown's threshold
lower end is kappa^+_i - h^-_i. No statement mathematics otherwise changed.

mathb, 2026-09-29 (PM's note, rule 21, together with claim 104): part 1's proof now cites ledger
entry AX-13, the polyhedral KKT theorem, applied to the lifted problem, and checks only its
hypotheses (a concave objective finite on all of R^{n+1}, hence an automatic constraint
qualification, and a polyhedral feasible set); the outline of claim 009's finite-cone argument is
removed and the multiplier elimination kept. AX-13 is in axioms_used. No result changed.

mathb, 2026-09-29 (analyst's experiment 034 note): part 5(a)'s general sentence said that every
threshold in parts 1-4 shifts by eta; that is right for part 1's thresholds on g_i and wrong for
part 3's strip on alpha_hat_i - gamma v_i x^-_i, whose shift is eta (1 - sum_j r_ij) (the form the
same paragraph already used for part 4). The sentence now says so, with part 3's shifted
endpoints and exposure target, and the proof of part 5 derives them from part 4's identity.
Part 4 also states the exact threshold when every ETF is traded (slopes pinned), the identity
the analyst observed as the threshold's position in the bracket. No approved result changed;
checks/102 covers both.

mathb, 2026-09-29 (lean's note, duty 1): part 4's "bought iff A_i = kappa^+_i + h^+_i" under exact
re-hedging was wrong at two edges. A purchase to the cap has g_i >= kappa^+_i, hence >=, not
equality; and a fund held at its band edge (g_i = kappa^+_i, untraded) while the exposure trade
sends the ETFs in the netting direction has the equality without a purchase. The Statement now
has lean's form: under the purchase re-hedge an interior purchase gives equality and a purchase
to the cap gives >=, mirrored for sales, with the converse's counterexample stated; the
pinned-slope thresholds are restated the same way. The bracket implications and the sufficient
conditions are unchanged. Lean formalizes that form.

mathb, 2026-09-29 (PM's revision note): depends_on adds claim 104, whose part 0 is this claim's
part 1 and whose part 2a is part 3, so that lean may import them (Q-04). The three items of PM's
pass (depends_on 104, part 5(a)'s strip shift, part 4's edge corrections) are this one revision;
no result changed. Red's note on 5(a) (its own solver: the netted form to 1e-8 bp on 32 traded
funds, the literal form off by up to 329 bp) asks for the same fix and for its cash reading,
the net cash 1 - sum_j r_ij of a netted unit, now in the text.

mathb, 2026-09-29 (lean's two edge notes, duty 1; the same edge as claim 105's 2c): part 3's
readings now carry the box, bought only with x^-_i < bar x_i and sold only with x^-_i > 0, the
held case listing the cap and zero readings, and "holding at zero" is the rule iff
alpha_hat_i <= kappa^+_i. Part 6's sale side is the mirror at the cap with the cap's risk charge
kept: a fully held fund is sold only if alpha_hat_{i,t} - c_t bar x_i < -(1 - beta) kappa^-_i, and
sold out surely if alpha_hat_{i,t} < -(kappa^-_i + beta kappa^+_i); the proof of part 6 now
writes the cap's left derivative instead of "the mirror". Lean formalizes these forms. No
result otherwise changed.

mathb, 2026-09-29 (auditor's note, from claim 102's FIDELITY row): the original sell-out "only
if" was right up to strictness, since hi_t = 0 forces alpha_hat_{i,t} <= -(1 - beta) kappa^-_i by
the continuation's slope bound as x -> 0, with equality still allowing a sell-out. Part 6 now
keeps it with "<=" beside lean's cap statement for any sale, and the proof of part 6 gives the
limit argument. No result changed.

Not machine checked. Parts 1-5 are finite convex-analysis statements about one quadratic
program; part 6 transfers claim 029 through claim 100.

Lean, 2026-09-29 (final): parts 1-5, including the pinned slopes and part 5(a)'s strip, and part 6's
thresholds are machine checked. The statement is
in `lean/Standalone/M7FundHoldBuySellCriterion.lean` and the proof in
`lean/Novel/M7FundHoldBuySellCriterionProof.lean`.
- Imports: the proof imports claim 104's proof module, for part 0 (the same AX-13 application, as
  the Upstream structure `PolyKKT`), 2a and the fund line, and claim 029's.
  - 104 is in depends_on (PM's option (a)).
  - Part 1's criterion and readings, and parts 2, 4 and 5, take `AX13` as a hypothesis. Part 1's
    existence and uniqueness do not (auditor's note).
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/102/check.py` pass.

Machine checked:
- Part 1:
  - with Sigma positive definite and gamma > 0, an optimum exists and is unique, by strict concavity
    at the midpoint;
  - a feasible x is optimal iff claim 104's multiplier criterion holds;
  - at the optimum, some eta >= 0 with eta k(x) = 0 gives every instrument's reading: the purchase
    line, the sale line, the held band, and their one-sided forms at 0 and bar x.
  The box signs are in normal-cone form, which is the claim's three cases with both signs at
  0 = bar x.
- Part 2: with x_E the ETF-only optimum and I the eta compatible with part 1 at x_E on the ETF
  coordinates and the budget, no fund is traded at the full optimum iff some eta in I makes every
  fund's held condition hold at x_E.
- Part 3 (frictionless spanning ETFs):
  - the band holding;
  - bought iff alpha_hat_i - gamma v_i x^-_i > kappa^+_i and x^-_i < bar x_i;
  - sold iff alpha_hat_i - gamma v_i x^-_i < -kappa^-_i and x^-_i > 0;
  - the zero-incumbent readings, and the sell-out iff alpha_hat_i <= -kappa^-_i;
  - the netting decomposition of the ETF trade.
  The box conditions on the incumbent (x^-_i < bar x_i to buy, x^-_i > 0 to sell) are in the
  revised text (mathb/claim102-lean-edges).
- Parts 4 and 5(a), for interior ETFs with the budget allowed to bind, with
  A' = A_i - eta(1 - sum_j r_ij):
  - a purchase gives A' >= (1 + eta)(kappa^+ - h^-), and a sale gives A' <= (1 + eta)(-kappa^- + h^+);
  - an interior hold gives the full bracket;
  - under the purchase re-hedge, an interior purchase gives A' = (1 + eta)(kappa^+ + h^+) and a purchase
    to the cap gives >=; the sale re-hedge is the mirror.
  - the converse's counterexample: under the purchase re-hedge, a fund held at x_i = x^-_i
    (interior) with g_i = eta + (1 + eta) kappa^+_i has A' = (1 + eta)(kappa^+ + h^+);
  - pinned slopes: if every ETF j with r_ij != 0 is traded, then with t_j = kappa^+_{E,j} (bought)
    or -kappa^-_{E,j} (sold), an interior purchase gives A' = (1 + eta)(kappa^+_i - sum_j r_ij t_j)
    (to the cap, >=), and an interior sale gives A' = (1 + eta)(-kappa^-_i - sum_j r_ij t_j)
    (to zero, <=).
  These are the edge corrections of lean's note, which mathb's revision adopts. With a slack
  budget, eta = 0 and these are part 4.
- Part 5(a) on part 3's strip (frictionless spanning ETFs, every ETF interior): some eta >= 0 with
  eta k(x) = 0 gives
  - the exposure y*(eta) = (gamma Sigma~_f)^{-1}(lambda_hat - eta (B^E)^{-1} 1);
  - x_i = the clip with lo_i, hi_i shifted by eta (1 - sum_j r_ij) and rates times (1 + eta);
  - bought iff alpha_hat_i - gamma v_i x^-_i > eta (1 - sum_j r_ij) + (1 + eta) kappa^+_i and
    x^-_i < bar x_i, and sold iff the mirror holds with x^-_i > 0. These are part 3's box
    conditions again.
- Part 4's sufficient conditions at the incumbent (Sigma_E = 0, slack budget).
- Part 6's thresholds in claim 029's one-instrument model, with pure-learning marking:
  - bought from zero when alpha_hat_t > kappa^+ + beta kappa^-;
  - sold out from the cap when alpha_hat_t < -(kappa^- + beta kappa^+);
  - no purchase from zero (lo_t = 0) when alpha_hat_t <= (1 - beta)kappa^+;
  - no sale from the cap (hi_t = bar x) when alpha_hat_t - c_t bar x >= -(1 - beta)kappa^-;
  - sold out entirely from any incumbent (hi_t = 0) only if alpha_hat_t <= -(1 - beta)kappa^-, the
    literal sell-out form the auditor noted.

  The last is the mirror at the cap. It carries the cap's risk charge c_t bar x, as the revised
  text does (mathb/claim102-lean-edges). The proofs use the convexity of the next review's value
  (claim 029's part 1a) through its one-sided derivatives.

Paper-level:
- part 6's reduction of the multi-review spanning problem to per-fund one-instrument problems;
- the static ceiling, which is claim 029's `Ceiling` transferred by claim 100;
- part 5(b)'s reading, the Reading for D15, and the Checks.

PM confirmed the scope (option (a); lean/claim102-notes).

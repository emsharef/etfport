---
id: 40
title: "The fund decision when ETFs sit at their zero bound, in the inputs: an ETF at zero has a one-sided marginal whose slack is the price of exposure in its direction; a fund's marginal is its net alpha plus the hedged premium of the by-product it carries in the at-zero directions, less the risk charge of that by-product, and the buy, sell and hold criterion reads on that marginal; which ETFs are at zero is fixed by the inputs through complementarity; along a fund's trade the at-zero set changes, so the response is piecewise linear with direction-dependent curvature, and dropping the at-zero ETFs from the menu is exact on the incumbent's piece and, off it, only by coincidence"
status: formalized
model_version: M7
depends_on: [30, 31, 102, 104]
axioms_used: [AX-13]
formal: lean/Standalone/M7FundDecisionEtfsAtZero.lean
direction: D15d
---
## Statement

D15d's first claim: the fund decision at one review when some ETFs sit at their zero bound, the
case claims 102 (part 5(b)) and 104 (2a-2b) exclude and the common long-only one (experiment 024:
ETFs at zero in 74% of instrument-quarters). Claim 102's criterion is exact but assumes every ETF
strictly inside its box; with an ETF at zero its marginal is one-sided, and netting a fund's
factor by-product may require selling that ETF below zero. The kill benchmark (ROADMAP D15d) is
claim 102 with the at-zero ETFs dropped from the menu. What is new here: the at-zero set is
determined by the inputs (part 2), the ETF's one-sided slack is the per-unit price of exposure in
its direction and enters every fund's marginal through the fund's netting vector (parts 1 and 3),
and along a fund's trade the at-zero set changes, so the fund's response is piecewise linear with
curvature that depends on the direction of trade, and the drop-the-ETFs rule is exact on the
incumbent's piece and, off it, only by coincidence (part 4). Two-stage exactness with ETFs at zero is
D15d's second claim.

**Setting.** One review of an M7 instance in claim 102's setting: N funds, M ETFs, K factors,
loadings B = [B^A; B^E], beliefs (lambda_hat, alpha_hat) with P = diag(P^lambda, P^alpha),
Sigma~_f = Sigma_f + P^lambda positive definite, V = Sigma_A + P^alpha positive definite, gamma > 0,
fund rates kappa^+_i, kappa^-_i in [0, 1), fund caps 0 <= x^A <= bar x^A, ETF bound x^E >= 0,
incumbents x^- = (x^{A-}, x^{E-}), objective Q(x) = mu'x - (gamma/2) x'Sigma x - C(x - x^-) with
mu = (alpha_hat + B^A lambda_hat, B^E lambda_hat - c^E), Sigma = B Sigma~_f B' + diag(V, Sigma_E),
smooth marginal g(x) = mu - gamma Sigma x, cash shadow price eta and trade-sign slope sets T_i(x)
as there. Part 1 is general. Parts 2-5 assume *spanning frictionless ETFs*: M = K, B^E invertible
with R = (B^E)^{-1}, kappa^+_E = kappa^-_E = 0, Sigma_E = 0 (fees c^E allowed), ETF caps absent or
slack and the budget slack at the optimum (checked ex post, as in claim 102 part 3), and use

```
Q = R' (B^A)'  (M x N, column r_i = R'(B^A_i)' the netting vector of fund i),
w = x^E + Q x^A   (the ETF-coordinate exposure: total factor exposure b = B'x = (B^E)' w),
mu_E = B^E lambda_hat - c^E,   Sigma_EE = B^E Sigma~_f (B^E)'  (positive definite),
alpha~ = alpha_hat + Q' c^E   (net alpha plus the fee credit of the fund's by-product, claim 102 part 4).
```

Then Q(x) = G_E(w) + alpha~' x^A - (gamma/2) x^A' V x^A - C_A(x^A - x^{A-}) with
G_E(w) = mu_E' w - (gamma/2) w' Sigma_EE w (exact algebra, proof part 0), and the ETF bound
reads w >= Q x^A: the exposure held through the ETFs cannot fall below the funds' by-product in
any ETF coordinate, because an ETF cannot be sold short.

1. **The exact criterion with one-sided ETF marginals (any frictions, AX-13).** Assume every ETF
   is strictly below its cap at the optimum (an ETF at its cap is the mirror case, Not shown). At
   the optimum x,
   with eta and slopes t as in claim 102 part 1, every ETF j at zero satisfies

   ```
   g_j(x) = eta + (1 + eta) t_j - zeta_j,    zeta_j >= 0,    t_j = kappa^+_{E,j} if x^{E-}_j = 0,   t_j = -kappa^-_{E,j} if x^{E-}_j > 0,
   ```

   (its marginal is at most its purchase threshold, or at most its sale threshold if it was sold
   out; zeta_j is the *slack*; for an untraded ETF at zero the slope set is an interval and
   several pairs (t_j, zeta_j) are valid multipliers, all with the same g_j: the convention here
   measures the slack from the purchase threshold, t_j = kappa^+_{E,j}, the largest admissible
   slope and hence the largest slack), and
   with spanning (M = K, B^E invertible) fund i's line becomes

   ```
   bought  iff  A_i(x) + r_i' (eta 1 + (1 + eta) t_E) - sum_{j at zero} r_ij zeta_j  =  eta + (1 + eta) kappa^+_i,
   ```

   and likewise for sold and held, with A_i claim 102 part 4's reduced marginal. The new term is
   the last: the fund's by-product exposure in the at-zero ETFs' directions is priced at minus
   their slacks, per unit of netting weight. A fund whose netting vector has r_ij > 0 (it adds
   exposure in an unwanted direction) loses r_ij zeta_j of marginal; one with r_ij < 0 (its
   by-product is short that direction) gains |r_ij| zeta_j. Where every ETF is interior, all
   slacks vanish and the line is claim 102's.

2. **Which ETFs are at zero, in the inputs (spanning frictionless ETFs).** For a by-product
   vector q = Q x^A, the exposure problem max {G_E(w) : w >= q} has a unique solution w(q) with
   unique multiplier zeta(q) >= 0 and at-zero set Z(q) = {j : w_j(q) = q_j}. Given a candidate set
   Z with complement c,

   ```
   w_c = Sigma_cc^{-1} ( mu_c / gamma - Sigma_cZ q_Z ),        w_Z = q_Z,
   zeta_Z = gamma Sigma_{ZZ.c} q_Z - mu_{Z.c},                  zeta_c = 0,
   Sigma_{ZZ.c} = Sigma_ZZ - Sigma_Zc Sigma_cc^{-1} Sigma_cZ,   mu_{Z.c} = mu_Z - Sigma_Zc Sigma_cc^{-1} mu_c
   ```

   (blocks of Sigma_EE and mu_E), and Z is the at-zero set iff zeta_Z >= 0 and w_c >= q_c; every
   set satisfying both gives the same w and zeta. In words: an ETF is at zero iff its premium,
   hedged by the free ETFs, does not cover the risk charge of the by-product exposure the funds
   already supply in its direction, hedged the same way. The value function V_E(q) = G_E(w(q)) is
   concave and differentiable with gradient -zeta(q).

3. **The fund marginal and the criterion.** Write Phi(x^A) = alpha~' x^A - (gamma/2) x^A' V x^A +
   V_E(Q x^A) - C_A(x^A - x^{A-}) for the fund problem with the exposure optimized out; its smooth
   part has gradient

   ```
   G_i(x^A) = alpha~_i - gamma (V x^A)_i - r_i' zeta(Q x^A) = alpha^Z_i - gamma (V^Z x^A)_i,    Z = Z(Q x^A),
   alpha^Z = alpha~ + Q_Z' mu_{Z.c},      V^Z = V + Q_Z' Sigma_{ZZ.c} Q_Z,
   ```

   (Q_Z the rows of Q in Z): the fund's net alpha plus the hedged premium of the by-product it
   carries in the at-zero directions, and its own risk plus the risk of that by-product, the funds
   now interacting through V^Z. For a given Z these are claim 031's reduced fund moments for the
   menu with Z removed (alpha^red = alpha_hat + B^A J' lambda_hat, Sigma^red = V + B^A Sigma~_{U.R} B^A',
   at zero fees; with fees, alpha~ in place of alpha_hat), the benchmark's form. Then:

   (a) *Hold test, exact for every N.* The incumbent x^{A-} (with the ETFs at w(Q x^{A-}) - Q x^{A-})
       is the review's optimum iff for every fund i, with Z^- = Z(Q x^{A-}),

       ```
       -kappa^-_i <= G_i(x^{A-}) <= kappa^+_i,    the lower bound dropped when x^-_i = 0, the upper when x^-_i = bar x_i.
       ```

   (b) *At the optimum x^A*, fund i is bought iff G_i(x^A) = kappa^+_i with x^-_i < x_i < bar x_i (>= at
       the cap), sold iff G_i(x^A) = -kappa^-_i with 0 < x_i < x^-_i (<= at zero), held iff G_i(x^A) is
       in the band, with Z = Z(Q x^A): claim 102 part 3's rule with alpha^Z and V^Z in place of
       alpha_hat and V.

   (c) *One fund (N = 1), exact and explicit:* bought iff G(x^-) > kappa^+ and x^- < bar x, sold iff
       G(x^-) < -kappa^- and x^- > 0, held otherwise, with G(x^-) = alpha^Z - gamma s^Z x^- evaluated at Z = Z(r x^-) and
       s^Z = v + r_Z' Sigma_{ZZ.c} r_Z. Premium beliefs and their precision enter the fund decision
       through mu_{Z.c} and Sigma_{ZZ.c} whenever Z is nonempty, although the ETFs span: an ETF at
       zero leaves its direction unhedged, exactly claim 031's leak with Z as the unreachable set,
       now produced by the bound rather than by the menu.

   (d) *How premium error enters through an ETF at zero.* Write B^E_{Z.c} = B^E_Z - Sigma_Zc
       Sigma_cc^{-1} B^E_c (the at-zero ETFs' loadings, hedged by the free ETFs; |Z| x K). A
       premium error e (lambda_hat in place of lambda_hat + e) shifts fund i's marginal by

       ```
       dG_i = r_iZ' B^E_{Z.c} e,
       ```

       the error projected on the at-zero directions after the free ETFs' hedge, weighted by the
       fund's netting weights there; a fund trading in the interior of its box, with Z fixed,
       moves by dG_i / (gamma s^Z_i) (one fund) or, with T the set of trading funds, by the i-th entry of
       (gamma V^Z_TT)^{-1} (Q_Z' B^E_{Z.c} e)_T, the restriction to T taken before the inversion, the
       other funds unmoved; a held fund does not move until the shift leaves its
       band. The shift is zero iff Z is empty or r_iZ = 0 (claim 105 part 1's spanning invariance,
       which needs every ETF bound slack); it is claim 105's scalar B^A_i J' e with the at-zero
       directions as the unreachable ones. Premium precision P^lambda enters the same way through
       Sigma_{ZZ.c}, in the risk charge of the by-product and its hedge. This is red's reading of
       experiment 027 (the leak vanishes only when no ETF bound binds and the ETFs are
       frictionless) stated in the inputs; the experiment's numbers illustrate it (rule 22).

4. **Along a fund's trade: direction-dependent reachable set (N = 1).** Let m(x) = G(x) for x in
   [0, bar x], one fund. Then m is continuous, nonincreasing and piecewise linear: on each maximal
   interval on which Z(r x) is constant (a *piece*) its slope is -gamma s^Z, and the pieces are
   separated by the points at which a free ETF's holding w_j(r x) - r_j x reaches zero or an
   at-zero ETF's slack zeta_j(r x) reaches zero, both affine in x on the piece, hence explicit in
   the inputs. The optimum is x* = the largest x >= x^- with m(x) >= kappa^+ (or bar x) when
   m(x^-) > kappa^+, the smallest x <= x^- with m(x) <= -kappa^- (or 0) when m(x^-) < -kappa^-, and
   x^- otherwise. The *drop-Z rule* (the kill benchmark: claim 102 part 3 on the menu without
   Z^- = Z(r x^-)) gives

   ```
   x~ = clip( x^-,  (alpha^{Z^-} - kappa^+)/(gamma s^{Z^-}),  (alpha^{Z^-} + kappa^-)/(gamma s^{Z^-}) )  clipped to [0, bar x],
   ```

   Write x*_u and x~_u for the roots before the clip to [0, bar x] (m extended beyond the box by
   its end pieces; x*_u = x*, x~_u = x~ when the root is inside). Then x~_u lies in the incumbent's
   piece (its end pieces extended) iff x*_u does, and then x*_u = x~_u; if the path leaves the
   piece strictly before x~_u (some y between x^- and x~_u has Z(r y) != Z^-) and every at-zero
   set off the piece has s^Z > s^{Z^-}, then x*_u < x~_u, and x*_u > x~_u when every one has
   s^Z < s^{Z^-} (the sale is the mirror); otherwise the roots can coincide, at the piece's open
   end (where a free ETF reaches zero and m = m~ still) or at a nongeneric level where m returns
   to the drop-Z line after status changes in both directions (lean's instances). x~ = x* iff x*_u = x~_u or both roots
   are clipped to the same bound of [0, bar x] (a sale that sells out under both rules, or a
   purchase to the cap, coincides although the at-zero set changes on the way; red's cases).
   Otherwise the true trade is shorter than the drop-Z trade when every status change between
   x^- and x~_u drives an ETF to zero (the curvature s^Z rises: the by-product loses a hedge) and
   longer when every one draws an ETF back from zero (s^Z falls: the by-product gains a hedge),
   for the unclipped roots. The pieces to the right and to the left of x^-
   differ, so a purchase and a sale of the same fund face different curvatures: the reachable set
   for netting depends on the direction of the trade, and the fund's response to its alpha is
   asymmetric beyond the asymmetry of its rates.

5. **Readings.** (a) *One ETF (M = K = 1).* With q = sum_i r_i x_i the funds' by-product in ETF
   units, the ETF is at zero iff mu_E <= gamma sigma_EE q: the premium net of fee does not cover
   the risk charge of the exposure the funds already carry; then every fund's marginal is
   alpha~_i + r_i mu_E - gamma [v_i x_i + r_i sigma_EE q], its total expected return less the full
   risk charge, and, for one fund (3(c)) or read at the optimum (3(b)), a fund below its cap is bought iff that
   exceeds kappa^+_i. (b) *What the benchmark misses.*
   Given Z, the marginal is the drop-Z marginal; but Z is not an input, the slack zeta_j prices the
   fund's by-product in the inputs (part 1), and a trade moves Z (part 4), so the drop-Z rule is
   exact on the incumbent's piece and, off it, only by a nongeneric coincidence. (c) *For the analyst.* With ETFs at zero, premium error
   reaches the fund decision under full spanning through alpha^Z, by 3(d)'s formula; this channel
   is present at zero ETF cost, beside the ETF-cost channel of claim 030 part 4, and red's
   reproduction of experiment 027 finds it to be the binding one on that grid.
   (d) *The fold-in form and the Jagannathan-Ma benchmark.* `jagannathan2003risk` Proposition 1
   (named; ROADMAP D15d's kill benchmark) folds binding long-only multipliers into the moments:
   the constrained minimum-variance portfolio is the unconstrained one for an adjusted covariance
   S~ = S + (delta 1' + 1 delta') - (lambda 1' + 1 lambda'), the multipliers read off the solution.
   Here the same fold-in reads: with the at-zero ETFs' multipliers zeta_Z taken as given, the
   optimum is the unconstrained optimum (claim 102 part 3's rule, ETFs free) for the premium
   vector (alpha~ - Q_Z' zeta_Z, mu_E + zeta) (part 2's zeta = gamma Sigma_EE w - mu_E gives
   w = (gamma Sigma_EE)^{-1}(mu_E + zeta): the multiplier raises the at-zero ETF's premium to
   indifference, since the ETF would be shorted otherwise, and lowers each fund's by the netting
   weights on Z; the premium form of the fold-in, since the objective has a mean and no budget
   identity). What the claim adds beyond
   that fold-in, and beyond dropping Z: zeta_Z is affine in the fund holdings (part 2), so on the
   fund block the fold-in is an adjusted premium *and* an adjusted covariance, alpha^Z and
   V^Z = V + Q_Z' Sigma_{ZZ.c} Q_Z, positive semidefinite of rank at most |Z| and explicit in the
   inputs given Z (Jagannathan-Ma's adjustment is rank two, indefinite in general, and implicit
   in the multipliers); the multipliers are not read off the solution but fixed by
   complementarity from the inputs (part 2); per-instrument costs turn the adjusted marginal
   into a band with one-sided forms at the fund's bounds (3a-c); the at-zero set moves along a
   trade, so the fold-in holds piecewise with direction-dependent curvature (part 4); premium
   error enters through the fold-in by an explicit projection (3d); and the two-stage question
   (D15d's second claim) asks when a stage that cannot see the fold-in still lands on it.

**One sentence without model nouns.** When a cheap instrument that would net a position's
side exposure cannot be sold below zero, that exposure stays and is priced at the instrument's
slack below its purchase threshold; the position's decision then reads on its own excess return
plus the hedged premium of the side exposure it carries in those directions, less that exposure's
risk charge, and since a trade moves which instruments are at zero, buying and selling face
different curvatures and the rule that simply removes the idle instruments is right while the
trade does not change which instruments are idle and otherwise only by coincidence.

## Proof

### 0. Coordinates

With Sigma_E = 0, x'Sigma x = b' Sigma~_f b + x^A' V x^A for b = B'x = (B^A)' x^A + (B^E)' x^E.
Since B^E is invertible, b = (B^E)' w with w = x^E + R'(B^A)' x^A = x^E + Q x^A, and
lambda_hat' b = (B^E lambda_hat)' w, b' Sigma~_f b = w' Sigma_EE w. The fee term is -c^E' x^E =
-c^E' w + c^E' Q x^A = -c^E' w + (Q' c^E)' x^A. Collecting, Q(x) = G_E(w) + alpha~' x^A -
(gamma/2) x^A' V x^A - C_A(x^A - x^{A-}) with mu_E = B^E lambda_hat - c^E; the ETF cost is zero.
The map (x^A, x^E) -> (x^A, w) is a bijection and x^E >= 0 iff w >= Q x^A. The joint problem is
therefore max over x^A in the fund box and w >= Q x^A of G_E(w) + [fund terms], and the exposure
can be optimized out for each x^A: Q's maximum equals max_{x^A} Phi(x^A).

### 1. One-sided marginals (general frictions)

Claim 102 part 1 (AX-13 applied to the lifted polyhedral problem, whose hypotheses claim 102 and
104 check) gives at the optimum R_j(x) = g_j(x) - eta - (1 + eta) t_j <= 0 at x^E_j = 0, with
t_j in T_j(x): T_j(x) = [-kappa^-_{E,j}, kappa^+_{E,j}] if x^{E-}_j = 0 (then the binding
inequality is the one with t_j = kappa^+_{E,j}, the largest threshold: some t_j in the set works
iff the largest does), and T_j(x) = {-kappa^-_{E,j}} if x^{E-}_j > 0. Define zeta_j = -R_j(x) >= 0.
For the fund line: g_i = mu_i - gamma (Sigma x)_i = alpha_hat_i + B^A_i lambda_hat - gamma
[B^A_i Sigma~_f b + (V x^A)_i], and r_i' g_E = B^A_i R [B^E lambda_hat - c^E - gamma (B^E Sigma~_f b
+ Sigma_E x^E)] = B^A_i lambda_hat - r_i' c^E - gamma B^A_i Sigma~_f b - gamma r_i' Sigma_E x^E,
so g_i = A_i + r_i' g_E with A_i = alpha_hat_i + r_i' c^E - gamma (V x^A)_i + gamma r_i' Sigma_E x^E
(claim 102's identity, with (V x^A)_i for general V). Substituting g_{E,j} = eta + (1 + eta) t_j -
zeta_j (zeta_j = 0 for interior ETFs, whose line is an equality) into claim 102 part 1's fund
line g_i = eta + (1 + eta) t_i gives the display.

### 2. The exposure problem

G_E is strictly concave (Sigma_EE positive definite) and {w >= q} is a closed convex set, so
w(q) exists and is unique. The constraint gradients are unit vectors, linearly independent, so
the KKT multiplier zeta(q) is unique: gamma Sigma_EE w - mu_E = zeta >= 0, zeta_j (w_j - q_j) = 0.
Given Z, the equations on c (zeta_c = 0) read Sigma_cc w_c + Sigma_cZ q_Z = mu_c/gamma, the
display for w_c, and on Z the definition of zeta_Z gives gamma (Sigma_ZZ q_Z + Sigma_Zc w_c) -
mu_Z, which is the Schur form after substituting w_c. Conversely, a set Z with zeta_Z >= 0 and
w_c >= q_c yields a KKT point, hence the unique optimum. Concavity of V_E: (w, q) -> G_E(w) on the
convex set {w >= q} is jointly concave, and a partial maximum of a jointly concave function is
concave. Supergradient: for any q', with w' = w(q') and w = w(q), G_E(w') <= G_E(w) + grad
G_E(w)'(w' - w) = V_E(q) - zeta'(w' - w), and zeta'(w' - w) = sum_{j in Z} zeta_j (w'_j - q_j) >=
sum_{j in Z} zeta_j (q'_j - q_j) = zeta'(q' - q) (w'_j >= q'_j, zeta_j >= 0, zeta_c = 0); so
V_E(q') <= V_E(q) - zeta(q)'(q' - q). Directional derivative: for a direction d and small s > 0,
the point w + s d^Z (d^Z_j = d_j on Z, 0 on c) is feasible for q + s d (on Z with equality; on c
because w_j > q_j), so V_E(q + s d) >= G_E(w + s d^Z) = V_E(q) - s zeta' d^Z - O(s^2) = V_E(q) -
s zeta' d - O(s^2); with the supergradient inequality, V_E'(q; d) = -zeta(q)' d for every d.
A concave finite function with linear directional derivatives is differentiable with gradient
-zeta(q).

### 3. The fund marginal and the criterion

Phi is concave (part 2 and the fund terms), and its smooth part is differentiable by part 2 with
gradient alpha~ - gamma V x^A - Q' zeta(Q x^A) by the chain rule. Substituting zeta_Z = gamma
Sigma_{ZZ.c} Q_Z x^A - mu_{Z.c} gives the reduced form. The identification with claim 031: fixing
the ETFs in Z at zero and optimizing the free ETFs is the problem claim 031 part 3 reduces, with
L_E = row(B^E_c) the reachable space; both expressions are the gradient of the same value
function (V_E with w_Z = q_Z), so they agree (the check verifies the coordinate identity).
(a) The directional derivative of Phi at x^{A-} in a direction d is G(x^{A-})' d - sum_i [kappa^+_i
d_i^+ + kappa^-_i d_i^-] (the smooth part is differentiable, the cost is separable and directionally
differentiable), a sum of one-coordinate directional derivatives. A concave function on a box is
maximized at x^{A-} iff every feasible directional derivative is nonpositive, iff each
one-coordinate derivative is nonpositive (the sum is over coordinates), iff G_i(x^{A-}) <= kappa^+_i
when x^-_i < bar x_i and G_i(x^{A-}) >= -kappa^-_i when x^-_i > 0: the display. (b) At the optimum
the same coordinatewise conditions hold for the direction sets at x^A, and a bought fund
(x_i > x^-_i, interior) has both one-sided derivatives along e_i nonpositive, G_i - kappa^+_i <= 0
and -(G_i - kappa^+_i) <= 0, so G_i = kappa^+_i; the other cases likewise (claim 102 part 1's
reading). (c) For N = 1, Phi is a concave function of one variable; it increases at x^- iff
G(x^-) > kappa^+ and decreases iff G(x^-) < -kappa^-, and the box allows the move iff x^- < bar x,
respectively x^- > 0. (d) mu_{Z.c} = (B^E_Z - Sigma_Zc Sigma_cc^{-1}
B^E_c) lambda_hat - (c^E_Z - Sigma_Zc Sigma_cc^{-1} c^E_c) is affine in lambda_hat with the displayed
matrix, and G_i depends on lambda_hat only through r_iZ' mu_{Z.c}; with Z fixed and the trading
funds interior, their first-order conditions G_i = +/- kappa_i are linear in x^A with matrix
-gamma V^Z on the trading block, giving the displayed response; the identification with claim
105 is part 3's with claim 031. Zero when Z is empty (no term) or r_iZ = 0.

### 4. The path

m(x) = G(x) is continuous (zeta(q) is continuous in q: the solution of a strictly concave QP with
a parametric constraint set is continuous, and zeta = gamma Sigma_EE w - mu_E) and nonincreasing
(Phi concave). On a piece, Z(r x) is constant and zeta_Z(r x) = gamma Sigma_{ZZ.c} r_Z x -
mu_{Z.c} is affine in x, so m(x) = alpha^Z - gamma s^Z x is affine with slope -gamma s^Z; the
holdings w_c(r x) - r_c x are affine in x too, so the piece ends where one of them, or one
zeta_j, reaches zero; for x beyond the end, part 2's complementarity picks the next set. The
optimum: Phi concave in one variable with a kink at x^- of slopes m(x^-) - kappa^+ (right) and
m(x^-) + kappa^- (left); when m(x^-) > kappa^+ the maximum is where m crosses kappa^+, the
largest x with m(x) >= kappa^+, or bar x if none; the sale case is symmetric. The drop-Z rule is
the root of the affine extension m~(x) = alpha^{Z^-} - gamma s^{Z^-} x of m from the incumbent's
piece. If x~_u lies in the piece, m = m~ there and x*_u = x~_u; if x*_u lies in the piece then
m~(x*_u) = m(x*_u) = kappa^+ so x~_u = x*_u; and if x~_u is outside the piece then x*_u is too,
since m and m~ are both strictly decreasing and agree on the piece. Beyond the piece's end e,
m - m~ is continuous, zero at e (the piece is open at e, where a free ETF reaches zero and joins
Z; m(e) = m~(e) by continuity) and affine on each later piece with slope -gamma (s^Z - s^{Z^-}).
If the path leaves the piece strictly before x~_u and every s^Z off the piece exceeds s^{Z^-},
then m - m~ < 0 on (e, x~_u], so m(x~_u) < kappa^+ and the root of m lies strictly below x~_u;
the mirror when every s^Z is below s^{Z^-}. Without the strict-before condition the roots can
coincide at e itself (a kappa^+ equal to m(e); lean's instance with a single rising change at
e = 0.0484766), and with status changes in both directions the slope can change sign, m - m~
can return to zero at some x beyond e, and a kappa^+ equal to m(x) there makes the roots
coincide (lean's instance: Z goes {2}, {1, 2}, {1} along a purchase, both roots at 0.403928),
nongeneric equalities. The clipped holdings x* = clip(x*_u),
x~ = clip(x~_u) then agree iff the unclipped roots agree or both are clipped to the same bound
(two distinct roots inside the box give distinct holdings; a root inside and one outside give
distinct holdings unless the inside root equals the bound exactly). Curvature monotonicity: adding an ETF
to Z removes a hedging instrument, and r_Z' Sigma_{ZZ.c} r_Z is the variance of the by-product's
Z-component after the minimum-variance hedge through c (the Schur complement), which cannot
decrease when the hedging set shrinks; so s^Z rises when an ETF joins Z and falls when one
leaves. If every status change between x^- and x~ raises s^Z, then m(x) <= m~(x) on [x^-, x~]
(m has the steeper descent), so m reaches kappa^+ no later than m~ and x*_u <= x~_u; the
opposite inequality when every change lowers s^Z; the clip preserves both orderings. Direction dependence: the pieces to the right of x^-
are traversed by a purchase and those to the left by a sale, and their sets Z differ from Z^-
(the first status change on each side is at a different ETF in general), so the curvatures
faced differ.

### 5. Readings

(a) With M = 1, part 2's Z is {1} iff gamma sigma_EE q - mu_E >= 0, and then alpha^Z_i = alpha~_i +
r_i mu_E, V^Z = V + sigma_EE r r' (Schur complement with an empty c is Sigma_EE itself), the
display; the total expected return alpha_hat_i + B^A_i lambda_hat equals alpha_hat_i + r_i B^E
lambda_hat = alpha~_i + r_i mu_E when c^E = 0, up to the fee terms. (b) and (c) are readings of
parts 1-4 and of claim 031's leak with Z in place of the unreachable directions.

## Checks

`checks/040/check.py` (cvxpy/CLARABEL for the joint optimum, active-set enumeration for the
exposure problem; floating point, not a certificate; rule 22: nothing decided by the numbers).
(i) Part 2: w(q), zeta(q), Z(q) against the solver's ETF holdings on 60 random instances (ETFs at
zero in 92 of 120 instrument slots); the gradient of V_E against central differences.
(ii) Part 3: both forms of the fund marginal agree; at the optimum every fund is on its band
edge or in its band with the right sign; the incumbent equal to the optimum is held; a random
incumbent is traded iff some fund is off its band; alpha^Z and V^Z equal claim 031's reduced
moments for the menu without Z. (iii) Part 4: one fund, three ETFs, 80 instances: m is
nonincreasing and piecewise linear with slope -gamma s^Z; the piecewise root matches the
solver; the drop-Z rule is exact in 41 trading cases and differs in 31, in the stated direction
in every one with monotone curvature. (iv) Part 5(a): the one-ETF condition on 100 instances. (v) Part 3(d): the fund holding's
response to a premium perturbation (central differences of the solver) against r_Z' B^E_{Z.c}/(gamma s^Z)
for one trading fund, and against zero when no ETF is at zero.

## Not shown

- ETF frictions and caps in parts 2-5 (part 1 covers the one-sided line with frictions; the
  explicit forms are frictionless). An ETF at its cap is the mirror case (slack below its sale
  threshold) and is not written out.
- A binding budget in parts 2-5 (claim 102 part 5(a)'s scaling applies to part 1).
- For N > 1, the per-fund direction from the incumbent's marginal alone: funds interact through
  V^Z, so only the hold test (3a) and the optimum's reading (3b) are exact; a fund with
  G_i(x^{A-}) > kappa^+_i need not be bought when another fund's purchase raises its by-product
  risk charge.
- Two-stage exactness with ETFs at zero: D15d's second claim.
- The response to premium precision (3(d) names the channel; no formula beyond Sigma_{ZZ.c}).
- Which ETFs are at zero as an explicit condition for M > 1 (part 2 gives complementarity, a
  finite computation, and part 5(a) the one-ETF closed form).

## Prior art

Mechanism: a bound-constrained quadratic exposure problem whose multipliers price the funds'
by-product exposure in the directions the bound blocks, an application of the polyhedral KKT
theorem (AX-13) and of the sensitivity of a strictly concave quadratic program in its constraint
vector (proved inline); the at-zero set is the active set, and the fund's marginal is claim 031's
reduced marginal with the active set as the unreachable directions.

General results checked: `jagannathan2003risk` Proposition 1 (full text; the fold-in of binding
long-only multipliers into an adjusted covariance, making the corner an unconstrained problem),
the roadmap's kill benchmark, restated in premium form and exceeded as part 5(d) lists: the
fold-in here is explicit in the inputs given the at-zero set, adds a covariance term of rank |Z|
on the fund block, sits inside a cost band, and moves along a trade; AX-13
(`rockafellar1970convex`, Theorems 27.4 and 28.2-28.3) through
claims 102 and 104; `liu2013portfolio` (named in the roadmap: the shadow price of a binding
portfolio bound in the small-cost expansion), the same object as zeta_j here, in a continuous-time
frictional setting, not used; claims 030 (the coordinates), 031 (hedge map, Schur complement,
reduced fund moments and the leak), 102 (the criterion and the frictionless-spanning closed
form, part 5(b) marking this case Not shown) and 104 (the joint optimality criterion).

Searched: claims 009, 027-031, 102, 104-106; ROADMAP D15d; experiments 024 and 027. This is a
claim because the roadmap asks for the criterion in the inputs with ETFs at zero, the case the
approved claims exclude, and the slack pricing, the complementarity determination of Z and the
piecewise path with its direction dependence are stated by no source.

## Open objections

Auditor's FIDELITY row (2026-09-29): part 1 states the assumption that every ETF is strictly
below its cap at the optimum; 5(a)'s closing sentence is restricted to one fund or to the
optimum; 3(d)'s multi-fund response restricts to the trading funds before inverting. No result
changes. Lean's piece-end point (2026-09-29): the revised difference statement failed at the piece's
open end (m = m~ there, so a kappa^+ equal to m(e) puts both roots at e, with a single rising
change); part 4 and its proof now use lean's form: the roots differ when the path leaves the
piece strictly before x~_u and every s^Z off the piece lies on one side of s^{Z^-}. PM's
revision pass (2026-09-29): the four other "only" phrasings (title, lead, 5(b), the one
sentence) weakened to "exact on the incumbent's piece and, off it, only by coincidence".
Lean's prose points (2026-09-29, after approval): part 4's "x*_u = x~_u iff x~_u in the piece" was
false in the "only if" direction after a non-monotone sequence of status changes (lean's
instance); it now reads in lean's form, with the roots differing under monotone changes and
coinciding only at the nongeneric crossing level; part 1's slack convention is the largest
slack (largest admissible slope); parts 3(c) and 5(a) carry the box conditions. PM's D15d note
on `jagannathan2003risk` (after the merge): part 5(d) and Prior art state the
fold-in form and what the claim adds beyond it. Red's re-review (0a3bce28, red-passed again):
5(d)'s ETF premium sign corrected to mu_E + zeta (the multiplier raises the at-zero ETF's premium
to indifference), as red found on 97 instances. PM's withdrawal (claim 040, 5(d)): red's required correction 2 made. Red's review (52ae7f24): the required correction
is made (part 4 states the criterion for the
unclipped roots and adds the case of both rules clipping to the same bound; the proof compares
roots, then holdings); the nits are made (the claim 031 identification at zero fees or with
alpha~; part 1's slack convention from the purchase threshold, one of several valid
multipliers). Earlier objections: none. Red should test: part 2's differentiability argument (the feasible perturbation
on c needs w_j > q_j strictly, which holds off Z by definition); part 3's identification with
claim 031's moments; part 4's ordering of x* and x~ (whether a non-monotone sequence of status
changes can reverse it, which the claim does not assert); and whether the check's random
instances reach the case of an ETF drawn back from zero along a purchase.

## Review

**Red, 2026-09-29.** I checked parts 0-5 by hand, tested parts 2-4 with red's own cvxpy/CLARABEL solver and active-set code (not reading `checks/040/check.py`), and ran `checks/040/check.py`, which passes. Every result holds except part 4's "iff" at the box bounds, which is one required correction. There are two nits.

**Hand check.**
- *Part 0.* The coordinates w = x^E + Q x^A and the fee credit are exact, and x^E >= 0 iff w >= Q x^A.
- *Part 1.* This is claim 102 part 1 via AX-13, with the one-sided ETF line.
- *Part 2.* The exposure KKT gives zeta = gamma Sigma_EE w - mu_E >= 0, and its complementary-slackness blocks give the displayed w_c and zeta_Z. The multiplier is unique because the constraint gradients are unit vectors. V_E is concave with gradient -zeta, and the proof of that is right.
- *Part 3.*
  - G_i = alpha~_i - gamma (V x)_i - r_i' zeta, and on a piece this is alpha^Z_i - gamma (V^Z x)_i.
  - The hold test is exact: the smooth part is differentiable and the cost separable, so the directional derivative at x^{A-} is a sum of coordinate terms, and it is nonpositive in every feasible direction iff each coordinate's is.
- *Part 4's direction statement.* r_Z' Sigma_{ZZ.c} r_Z is a constrained minimum variance over the free ETFs, so it cannot fall when an ETF joins Z.
- *Part 5(a).* This is part 2 with M = 1.

**Independent numerical tests** (red's scripts, not committed). Instances: K = M = 3 spanning frictionless ETFs with fees, the ETF zero bound active, a slack budget, and fund caps of 5.
- *Part 2.* On 120 two-fund instances (ETFs at zero in 230 of 360 slots), red's active-set solution w(q), Z(q) and zeta(q), at q = Q x^A of the solver's optimum, reproduces the solver's ETF holdings to 1e-6 every time.
- *Part 3(a).* The hold test at the incumbent agrees with whether the solver trades in all 120 instances (113 traded).
- *Part 4.* On about 130 one-fund trading instances, the drop-Z rule is exact in 95-111 and differs in 31-32. In every difference where the at-zero set changes monotonically along the path (29-31 cases), the true trade is shorter when ETFs are driven to zero and longer when they leave zero, as stated.

**Required correction 1 (part 4's "x~ = x* iff x~ lies in the incumbent's piece" fails at a box bound).**
- When the drop-Z rule and the true optimum both clip at the same bound of the fund's box, they coincide although x~ is outside the incumbent's piece.
- The typical case is a sale to zero, where the drop-Z root and the piecewise root both lie below 0. The at-zero set changes between x^- and 0, yet both rules sell out.
- Red found 8-15 such cases, all sales clipped at zero. For example: x^- = 0.073, Z^- = {1, 2}, the at-zero set at the sale's end {2}, x~ = x* = 0.
- The Proof's "if x~ is outside the piece then x* is too" compares roots, not clipped holdings.
- Please state the criterion for the unclipped roots, or add "or both clip to the same bound of [0, bar x]". The "if" direction and the direction-of-difference statement are unaffected.

**Nits.**
- Part 3's identification of alpha^Z and V^Z with claim 031's reduced moments holds with the fee credit Q'c^E folded into alpha~. Claim 031 has c^E = 0, so please say that the identification is at zero fees, or with alpha~ in place of alpha_hat.
- Part 1's slack zeta_j for an untraded ETF at zero is defined with t_j = kappa^+_{E,j}, the largest admissible slope. That is one valid choice. The multiplier representation is not unique there when kappa_E > 0, so zeta_j is "the slack at the purchase threshold", not a unique price.

**Mechanism (4b).**
- The ETF zero bound is a complementarity constraint on the exposure problem. Optimizing the exposure out leaves the fund problem with the at-zero directions unhedged: claim 031's leak, with the unreachable set produced by the bound instead of the menu.
- The drop-Z rule is the benchmark, and its exactness is the question of whether the trade crosses a change of the at-zero set.
- This is correct and elementary, and part 3(c) is consistent with red's experiment 027 finding: premium error reaches fund choice under full spanning only through ETF frictions or a binding ETF bound.

Verdict: red-passed

**Red, re-review of the change since red's verdict (300773f9, part 3(d)), 2026-09-29.** Part 3(d) is right. Red's required correction 1 (part 4's piece criterion at a box bound) is not yet made.
- *3(d) by hand.* G_i depends on lambda_hat only through r_iZ' mu_{Z.c}, and mu_{Z.c} = (B^E_Z - Sigma_Zc Sigma_cc^{-1} B^E_c) lambda_hat - (fee terms), so dG_i = r_iZ' B^E_{Z.c} e.
  - Because B^E is invertible, B^E_{Z.c} has full row rank |Z|: its rows are B^E_Z's minus combinations of B^E_c's.
  - So the shift vanishes for every e iff Z is empty or r_iZ = 0, as stated.
  - With Z fixed and the fund interior and trading, the response is dG_i/(gamma s^Z_i).
- *3(d) numerically.* This used red's solver with central differences in the premium mean along random directions (step 1e-7). Over 113 interior, trading one-fund instances, 112 of them with an ETF at zero, the response matches r_Z' B^E_{Z.c} e/(gamma s^Z) to 1.2e-3 relative, the finite-difference and solver-tolerance level. The one case with no ETF at zero has zero response.
- *The reading.* It agrees with red's reproduction of experiment 027: with all ETF frictions off and ETFs allowed to go short, so no bound binds, the premium sensitivity was about 1e-7.
- *Still outstanding.* Red's required correction 1: part 4's "x~ = x* iff x~ lies in the incumbent's piece" fails when both rules clip at the same box bound (sales to zero). Red's verdict stands with that correction.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): math changed the Statement after red's verdict. It added part 3(d), how premium error enters through an ETF at zero (300773f9), which red has not reviewed, and made red's part 4 correction at a box bound (d9a62906). Red records a fresh verdict on both, which are already on main.

**Red, re-review after PM's withdrawal, 2026-09-29.** This covers part 3(d) (300773f9), the part 4 correction (d9a62906) and the new part 5(d) (d7ae7985). 3(d) and part 4 are right. 5(d)'s fold-in has the sign of the ETF adjustment reversed, which is one required correction.
- *Part 3(d).*
  - G_i depends on lambda_hat only through r_iZ' mu_{Z.c}, so dG_i = r_iZ' B^E_{Z.c} e.
  - Because B^E is invertible, B^E_{Z.c} has full row rank |Z|, so the shift vanishes for every e iff Z is empty or r_iZ = 0.
  - Numerically, from red's solver with central differences along random premium directions: over 113 interior trading one-fund instances (112 with an ETF at zero), the response matches r_Z' B^E_{Z.c} e/(gamma s^Z) to 1.2e-3 relative, and the case with no ETF at zero has zero response.
  - This agrees with red's experiment 027 and 030 findings.
- *Part 4 correction.* The criterion now compares the unclipped roots. x*_u = x~_u iff x~_u lies in the incumbent's piece, and the clipped holdings agree iff the unclipped roots agree or both clip to the same bound. That is exactly the gap red found: 8-15 sales to zero, all of which are both-clipped cases. The "iff" argument for the unclipped roots is right, since m and m~ are strictly decreasing and agree on the piece. The nits (the zero-fee identification with claim 031, and the slack convention) are made.
- *Part 5(d) (required correction 2: the sign of the fold-in).* The Statement says the optimum is the unconstrained optimum for the premium vector (alpha~ - Q_Z' zeta_Z, mu_E - zeta), "the multiplier lowers the at-zero ETF's premium to indifference". The sign of the ETF part is reversed.
  - Part 2 defines zeta = gamma Sigma_EE w - mu_E >= 0, so the exposure's stationarity is w = (gamma Sigma_EE)^{-1}(mu_E + zeta).
  - An ETF at zero would be sold short if it could, so its marginal is -zeta_j <= 0, and folding in the multiplier raises its premium to indifference.
  - The fund part is right: in coordinates, raising the ETF premium by zeta lowers the fee credit, alpha~ -> alpha~ - Q' zeta.
  - Red solved the unconstrained fund-and-exposure problem with the ETFs free on 97 two-fund instances with an ETF at zero (red's claim 040 test instances). (alpha~ - Q_Z' zeta_Z, mu_E + zeta) reproduces the constrained optimum in all 97, holdings and exposure to 1e-5. The claim's (alpha~ - Q_Z' zeta_Z, mu_E - zeta) reproduces it in none.
  - Please change mu_E - zeta to mu_E + zeta and "lowers" to "raises".
  - The rest of 5(d) is right: the rank of at most |Z| is the rank of the added term Q_Z' Sigma_{ZZ.c} Q_Z (V^Z itself is positive definite), and Jagannathan-Ma's adjustment is rank two and indefinite.
- `checks/040/check.py` passes on main.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's required correction 2. Part 5(d)'s fold-in displays the ETF premium as mu_E - zeta and says the multiplier 'lowers' it; the correct form is mu_E + zeta, which 'raises' it (red: + reproduces the constrained optimum in 97 of 97 instances, - in 0). Math fixes the sign, and red records a fresh verdict.


**Red, recheck of 5(d), 2026-09-29.** Math's fix is on main, and the only Statement change since PM's withdrawal is 5(d)'s fold-in:
- the ETF premium is now mu_E + zeta, with the derivation w = (gamma Sigma_EE)^{-1}(mu_E + zeta) from part 2's zeta = gamma Sigma_EE w - mu_E;
- "lowers" is now "raises" for the at-zero ETF, and "lowers" is kept for each fund's premium by the netting weights on Z.

This is the form red tested: (alpha~ - Q_Z' zeta_Z, mu_E + zeta) reproduces the constrained optimum on 97 of 97 instances with an ETF at zero, with the ETFs free. The rest of 5(d), and red's earlier findings on parts 1-5, 3(d) and part 4, are unchanged. Required correction 2 is made. The Open objections line records it.

Verdict: red-passed

**Red, text check of the part 4 and prose revision (math/claim040-lean-prose, merged), 2026-09-29.** The wording is right:
- Part 4 now reads "x~_u lies in the incumbent's piece iff x*_u does, and then x*_u = x~_u".
- Off the piece, under monotone status changes (s^Z != s^{Z^-}), the roots differ: m - m~ is 0 at the piece's end and strictly monotone beyond it, with slope -gamma (s^Z - s^{Z^-}) of one sign.
- They can coincide only at the nongeneric recrossing level. Red reproduced lean's instance at 0.403928 with its own active-set solver, and kappa^+ +- 1e-4 separates the roots.
- No "exact only" wording is left in the title, lead, 5(b) or plain sentence.
- Part 1's convention now gives the largest slack.
- 3(c) and 5(a) carry the box conditions (x^- < bar x to buy, x^- > 0 to sell).

No other result changed. The approval stands.

**Red, text check of the piece-end fix (math/claim040-piece-end-fix, merged), 2026-09-29.** Part 4's ordering sentence is now right.
- *The condition.* The path leaves the incumbent's piece strictly before x~_u (some y between x^- and x~_u with Z(r y) != Z^-).
- *Why it orders the roots.* m = m~ at the piece's end e by continuity. When every at-zero set off the piece has s^Z > s^{Z^-}, m - m~ is strictly decreasing on (e, x~_u], so m(x~_u) < kappa^+ and x*_u < x~_u. The reverse sign gives the reverse order. The sale is the mirror.
- *The exceptions are named.* The roots can coincide at the piece's open end (lean's instance: red found both roots at e = 0.0484765 with kappa^+ = m(e)) and at the nongeneric two-sided recrossing.

No other result changed. The approval stands.
## Formalization notes

Approved 2026-09-29 by pm: Red's reviews are sound: parts 0-5 checked by hand and against red's own solver (part 2 on 120 instances, hold test 120/120, part 4's piecewise path with drop-Z exact only on the incumbent's piece, 3(d) to 1.2e-3); both required corrections (part 4 at a box bound, 5(d)'s sign mu_E + zeta) made and rechecked. Mechanism: AX-13 on the bound-constrained exposure problem, claim 031's leak with the active set as the unreachable directions, an application. New for D15d beyond the Jagannathan-Ma fold-in and the drop-Z benchmark: the slack pricing, Z fixed by complementarity in the inputs, the rank-|Z| covariance term, and the direction-dependent piecewise response, so D15d's kill criterion is not met. Limits: frictionless spanning ETFs and a slack budget in parts 2-5; N > 1 per-fund direction not shown.


Not machine checked. Quadratic programming with bound constraints; an envelope argument proved
inline; a one-variable concave maximization.

Lean, 2026-09-29 (final): parts 0-5 are machine checked, with the readings below left paper-level.
The statement is in `lean/Standalone/M7FundDecisionEtfsAtZero.lean` and the proof in
`lean/Novel/M7FundDecisionEtfsAtZeroProof.lean`.
- Imports: the proof imports claim 104's proof module (the AX-13 criterion, the reference-case
  marginals and the score split). The paper-level parts cite 30, 31 and 102. Part 1 takes `AX13` as
  a hypothesis; every other part is unconditional.
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/040/check.py` pass.
- PM's limits hold. Parts 2-5 assume frictionless spanning ETFs and a slack budget (the ex post
  check is part 0's transfer). The per-fund direction for N > 1 is not claimed.
- Scope: lean's note to PM (lean/claim040-notes), which PM confirmed. The ordering is stated under
  "the at-zero set contains Z^- along the path, or is contained in it", which is more general
  than monotone changes, and m is taken on all of R.
- Shared objects: the module holds the ETF coordinates, G_E, V_E, zeta and Z (`Coord`, `GE`, `Wset`,
  `VE`, `wopt`, `zeta`, `Zset`), which claim 041 imports.

Machine checked:
- Part 0, on claim 027's M2 `Data` with Sigma_E = 0, B^E invertible and frictionless ETFs (fees
  allowed):
  - the score equals G_E(w) + alpha~'x^A - (gamma/2) x^A'V x^A - C_A with w = x^E + Q x^A;
  - x^E >= 0 iff w >= Q x^A, and Sigma_EE is positive definite;
  - a holding in F whose coordinates maximize the coordinate problem is the review's optimum.
- Part 1 (given AX-13), at the optimum with every ETF below its cap, some eta >= 0 with
  eta k(x) = 0 and slopes t in the trade-sign sets give:
  - every ETF's line g_j = eta + (1 + eta) t_j - zeta_j, with zeta_j >= 0, zeta_j = 0 off zero, and
    t_j the convention at zero;
  - fund i's marginal A_i + r_i'(eta 1 + (1 + eta) t_E) - sum_j r_ij zeta_j, with the box signs of
    g_i - eta - (1 + eta) t_i.
  For an ETF at zero that was not held, zeta_j is the largest slack over the slope set, as the
  revised text says.
- Part 2, in the claim's coordinates (mu_E, Sigma_EE positive definite, gamma > 0):
  - w(q) exists and is unique, and V_E(q) = G_E(w(q));
  - (w, zeta) satisfies the KKT conditions iff it is (w(q), zeta(q)), so the multiplier is unique;
  - the Schur-block candidate for Z has zeta_Z >= 0 and w_c >= q_c iff it is w(q) with multiplier
    zeta_Z on Z and 0 on c, and Z(q) satisfies both;
  - V_E is concave and differentiable with gradient -zeta(q).
  The proof uses the complementarity estimate ||w(q') - w(q)||_Sigma <= ||q' - q||_Sigma.
- Part 3, with gamma > 0, Sigma_EE and V positive definite, nonnegative rates and 0 <= x^- <= bar x:
  - the smooth part of Phi has gradient G(x) = alpha~ - gamma V x - Q'zeta(Q x), and
    G = alpha^Z - gamma V^Z x on Z = Z(Q x);
  - the exposure optimizes out: a feasible point is optimal iff its funds maximize Phi and
    w = w(Q x^A); Phi has exactly one maximizer on the box;
  - (a) the hold test, exact for every N;
  - (b) the readings at the optimum, with their one-sided forms at the bounds;
  - (c) one fund: bought iff G(x^-) > kappa^+ and x^- < bar x, and sold iff G(x^-) < -kappa^- and
    x^- > 0, the revised text;
  - (d) at a fixed Z, a premium error moving mu_E by B^E e shifts G by Q_Z'B^E_{Z.c} e. With B^E
    invertible, fund i's shift vanishes for every e iff r_iZ = 0. The trading block's response is
    (gamma V^Z_TT)^{-1} times the shift, and for one fund the shift over gamma s^Z.
- Part 4, one fund, with m on the whole line (part 2 defines it there, so no extension by end
  pieces is needed):
  - m is Lipschitz and strictly decreasing;
  - each piece {x : Z(r x) = Z} is an interval cut out by the affine conditions zeta_Z >= 0 and
    w_c - r_c x > 0, and on it m = alpha^Z - gamma s^Z x;
  - s^Z is monotone in Z, and so is the quadratic form of V^Z for any N;
  - m = k has exactly one root for every k;
  - the optimum is the incumbent, or the clipped root of m = kappa^+ (purchase) or m = -kappa^-
    (sale);
  - for the drop-Z rule: x~_u lies in the incumbent's piece iff x*_u does, and then the two are
    equal; the holdings agree iff the roots agree or both clip to the same bound;
  - if the at-zero set contains Z^- along the way to the drop-Z root, the true trade is no longer;
    if it is contained in Z^-, it is no shorter. These are weaker hypotheses than monotone status
    changes;
  - if the path leaves the piece before the drop-Z root, and every at-zero set off the piece has
    s^Z > s^{Z^-} (every one s^Z < s^{Z^-}), the roots differ, in the stated direction.
  The revised "outside the piece the roots differ whenever ... s^Z moves one way" fails at the
  piece's open end: there a free ETF reaches zero, m = m~ by continuity, and a kappa^+ equal to
  m there makes the roots coincide. Lean's note to math and red gives an instance, and the formal
  form requires the path to leave the piece before the root.
- Part 5:
  - (a) one ETF: at zero iff mu_E <= gamma sigma_EE q, with the two forms of the marginal (V
    general);
  - (d) the fold-in: at the optimum, w = (gamma Sigma_EE)^{-1}(mu_E + zeta), Q'zeta = Q_Z'zeta_Z, and
    the optimum maximizes the review with the ETFs free at the premiums (alpha~ - Q'zeta, mu_E + zeta);
    V^Z - V is positive semidefinite of rank at most |Z|.

Paper-level:
- part 3's identification of alpha^Z and V^Z with claim 031's reduced moments (the check verifies
  it);
- 3(d)'s "a held fund does not move until the shift leaves its band";
- part 4's direction-dependence reading;
- 5(b), 5(c), and 5(d)'s comparison with Jagannathan-Ma;
- the Checks.

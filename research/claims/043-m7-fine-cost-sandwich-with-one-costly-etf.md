---
id: 43
title: "The fine-regime cost with one costly ETF, sandwiched in the inputs: the pair's corrector eigenvalue lies between the sum of the fund's and the ETF's one-instrument eigenvalues with the fund's rate lowered, and the same sum with the fund's rate raised, by the re-hedge cost, the hedge ratio times the ETF's rate; the two bounds coincide with uncorrelated risks, their relative gap is at most 2 [1 - (1 - x)^(2/3)] with x the re-hedge cost over the fund's rate, so the ETF's cost enters the fund's leading-order cost as a shift of the fund's rate by at most the re-hedge cost, with the residual curvature and the fund's own innovation variance and no idle-target variance"
status: formalized
model_version: M7
depends_on: [42, 107]
axioms_used: [AX-15, AX-16]
formal: lean/Standalone/M7FineCostSandwich.lean
direction: D15e
---
## Statement

D15e's second claim, on the intermediate object claim 042 left open. Claim 042 reduced the
two-instrument fine-regime problem to a two-dimensional corrector problem in the fund's gap and
the ETF's tracking error, with the diagonal cost (c^res, gamma Sigma_EE), an oblique fund control
and one dimensionless ratio xi; the fund's band at the ETF holding b = b*, F(xi), is that problem's non-contact set
along the line e = rho_h y_a (the analyst's experiment 043 point, made in claim 042). The non-contact set is not characterized here. What is characterized is the problem's
*eigenvalue*, the leading-order average cost of the pair, which `possamai2015homogenization`
(AX-16) shows exists, is unique and obeys a comparison principle: explicit separable sub- and
supersolutions built from AX-15's one-instrument solutions sandwich it in the inputs, and the
sandwich says how the ETF's cost reaches the fund at leading order: as a shift of the fund's rate
by at most the re-hedge cost |rho_h| kappa_E, claim 107's static re-hedge term transported to the
fine regime, with the fund's curvature c^res and its own innovation variance v_A, and with the
idle-target variance v^idle in no bound.

**Setting.** Claim 042's setting and coordinates, with the hypotheses the construction needs
stated: gamma > 0; Sigma positive definite, so c^res, c_E > 0; per-side rates kappa_A, kappa_E > 0
(symmetric; the round trips are 2 kappa_A, 2 kappa_E; C then has nonempty interior and delta_C is
coercive); v_A, v_B > 0 and |r| < 1, so the innovation covariance W below is positive definite
(AX-16's ellipticity) and v_B^eff = (1 - r^2) v_B + (r sqrt(v_B) + rho_h sqrt(v_A))^2 > 0 (leanb's
point: with v_B^eff = 0 the ETF piece would be zero and the supersolution would fail). Hedge ratio rho_h =
Sigma_AE/Sigma_EE, residual curvature c^res = gamma (Sigma_AA - Sigma_AE^2/Sigma_EE), ETF curvature
c_E = gamma Sigma_EE, innovation variances v_A of the fund's target and v_B^eff = v_B + rho_h^2 v_A +
2 rho_h r sqrt(v_A v_B) of the ETF's effective target (claim 042 part 1), innovation covariance
w = r sqrt(v_A v_B) + rho_h v_A. The *corrector problem of the pair* is the first corrector
equation of AX-16 for the state y = (y_a, e) with running cost (c^res/2) y_a^2 + (c_E/2) e^2,
Brownian innovation covariance W = [[v_A, w], [w, v_B^eff]], and the polytope of admissible
gradients

```
C = { p = (p_a, p_e) : |p_a + rho_h p_e| <= kappa_A,  |p_e| <= kappa_E }
```

(the fund's control moves y along (1, rho_h) at rate kappa_A per unit, the ETF's along (0, 1) at
rate kappa_E), with support function delta_C(y) = kappa_A |y_a| + kappa_E |e - rho_h y_a|. By AX-16
(Theorems 3.1-3.2, Corollary 6.1) it has a convex C^{1,1} solution w with eigenvalue a, unique
among solutions with the growth w/delta_C -> 1, and sub- and supersolutions with the matching
growth bound a from below and above. Write, from AX-15, the one-instrument eigenvalues

```
a_A(k) = (c^res/2) ( 3 (2k) v_A / (4 c^res) )^{2/3},    a_E(k) = (c_E/2) ( 3 (2k) v_B^eff / (4 c_E) )^{2/3}
```

(per-side rate k), and x = |rho_h| kappa_E / kappa_A.

1. **The sandwich.** If |rho_h| kappa_E < kappa_A,

   ```
   a_A(kappa_A - |rho_h| kappa_E) + a_E(kappa_E)  <=  a  <=  a_A(kappa_A + |rho_h| kappa_E) + a_E(kappa_E);
   ```

   in general the lower bound is max { a_A(k_A') + a_E(k_E') : k_A', k_E' >= 0, k_A' + |rho_h| k_E' <=
   kappa_A, k_E' <= kappa_E }, of which the displayed one is a (generally weaker) instance, and the
   upper bound is as displayed. The ETF's own term a_E(kappa_E) is common to both displayed
   bounds. A third lower bound, through the ETF's own gap y_b = e - rho_h y_a, which only the ETF
   moves: with c_b = c^res c_E / (c^res + rho_h^2 c_E) (the least curvature of the pair's cost at a
   fixed y_b, over the fund's holding),

   ```
   a  >=  a_b(kappa_E) := (c_b/2) ( 3 (2 kappa_E) v_B / (4 c_b) )^{2/3},
   ```

   which grows without bound as kappa_E does.

2. **Exactness with uncorrelated risks.** If Sigma_AE = 0 then a = a_A(kappa_A) + a_E(kappa_E),
   whatever the innovation correlation r (claim 042 part 2(a) at the corrector level).

3. **The gap.** With x < 1 the two bounds on the fund's term are a_A(kappa_A) (1 -+ x)^{2/3}, so

   ```
   (upper - lower) / a_A(kappa_A)  =  (1 + x)^{2/3} - (1 - x)^{2/3}  <=  2 [ 1 - (1 - x)^{2/3} ]  =  (4/3) x + O(x^2):
   ```

   the leading-order cost is the decoupled sum a_A(kappa_A) + a_E(kappa_E) up to a relative
   error of first order in the re-hedge cost over the fund's rate, times the fund's share.

4. **Readings.** (a) *An effective rate.* Since a_A is continuous and increasing, there is a
   k* in [kappa_A - |rho_h| kappa_E, kappa_A + |rho_h| kappa_E] with a = a_A(k*) + a_E(kappa_E): at
   leading order the ETF's cost enters the fund's cost as a shift of the fund's rate by at most
   the re-hedge cost |rho_h| kappa_E (the ETF's rate on the ETF trade that nets one unit of fund
   trade), with the fund's curvature c^res and its own innovation variance v_A; this is claim
   107's static re-hedge bracket H^+-, whose leading-order counterpart is the rate shift, not a
   change of variance: the idle-target variance v^idle enters no bound, so the mixture claim
   042 discussed is, at small rate ratio, a mixture on the fund's rate between kappa_A and
   kappa_A + |rho_h| kappa_E (where in the sandwich k* lies is open; red's discrete illustration
   puts it below kappa_A at r >= 0), not on the
   variance. (b) *For the band.* If the fund's cross-section followed the one-instrument law at
   its effective rate, F(xi)^3 would lie in [1 - x, 1 + x]; the non-contact set is not
   characterized here (AX-16's own caveat that the corrector's non-contact set is not shown to
   be an actual no-trade region applies), so this is a reading. (c) *The ends.* As kappa_E -> 0 the
   sandwich pinches to a_A(kappa_A), claim 042's frictionless-ETF end. As kappa_E -> infinity the
   general separable lower bound stays bounded (for kappa_E >= kappa_A/|rho_h| it no longer depends
   on kappa_E; leanb's instance), but the third lower bound a_b(kappa_E) grows like kappa_E^{2/3},
   so a -> infinity: the frozen-ETF end is not an ergodic object (the ETF's gap is moved only by
   the ETF, and a never-trading ETF has unbounded average error whatever the fund does), which
   is why claim 042's frozen reduction concerns the fund's band alone.

**One sentence without model nouns.** With a cheap hedging instrument, the leading-order
running cost of a costly position and its hedge together lies between the sum of their
separate costs with the position's rate lowered, and the same sum with it raised, by the
hedge's rate times the hedge ratio; the two coincide when the risks are uncorrelated, the gap
is first order in that re-hedge cost over the position's rate, and so the hedge's cost reaches
the position as a shift of its rate, with the position's residual curvature and its own
innovation, not as a change of the innovation it tracks.

## Proof

### 0. The corrector problem and the comparison principle

AX-16 (Theorem 3.2) gives, for the corrector problem with cost, covariance and polytope as in
the Setting, a convex C^{1,1} solution w with eigenvalue a and growth w/delta_C -> 1 at infinity;
Corollary 6.1 makes a unique among such solutions; Theorem 3.1 states that if w_1 is a viscosity
subsolution with eigenvalue a_1 and lim w_1/delta_C <= 1, and w_2 a viscosity supersolution with
eigenvalue a_2 and lim w_2/delta_C >= 1, then a_1 <= a_2. Applied with (w_2, a_2) = (w, a) and a
subsolution, or with (w_1, a_1) = (w, a) and a supersolution, it bounds a from below and above.

*Hypothesis check for AX-16 (rule 21; red's required correction).* The source's polytope has the
difference form -lambda_{j,i} <= rho_i - rho_j <= lambda_{i,j} with rho_0 = 0. In the coordinates
z_A = y_a, z_E = e - rho_h y_a (so y_a = z_A, e = rho_h z_A + z_E; y = M z with M = [[1, 0], [rho_h, 1]]),
each control moves one coordinate: a fund trade da moves y_a by da and e by rho_h da, hence z_A
by da and z_E not at all, and an ETF trade moves z_E alone. The gradients transform by q =
grad_z w~ = M' p, that is, q_A = p_a + rho_h p_e and q_E = p_e, so C is the box {|q_A| <= kappa_A,
|q_E| <= kappa_E}: the source's cash-only case (Example 3.1, lambda^{i,j} = infinity for i, j >= 1,
each instrument traded against cash at its own rate). The cost (c^res/2) z_A^2 + (c_E/2)(rho_h z_A
+ z_E)^2 is a positive definite quadratic (a sum of squares of two linearly independent linear
forms), and the innovation covariance of z is M^{-1} W M^{-1}', positive definite since W is
(the Setting's hypotheses). The equation, its eigenvalue, the sub- and supersolution
inequalities and the growth condition transform consistently under this linear change of
variables: tr(W D_y^2 w) = tr(M^{-1} W M^{-1}' D_z^2 w~), the inequalities are pointwise, and the
support function is invariant, delta_{C_z}(z) = kappa_A |z_A| + kappa_E |z_E| = kappa_A |y_a| + kappa_E
|e - rho_h y_a| = delta_C(y). So AX-16's Theorems 3.1-3.2 and Corollary 6.1 apply to the pair's
problem, and the bounds proved below in the y coordinates are the source's in the z ones.
The equation, in the form used below: max { a - (1/2) tr(W D^2 w) - cost(y), H_C(Dw) } = 0 with
H_C(p) < 0 for p in int C, = 0 on the boundary of C and > 0 outside; a subsolution has both
terms <= 0 everywhere, a supersolution has the maximum >= 0 everywhere (classical C^2 functions
are viscosity sub- and supersolutions when they satisfy the inequalities pointwise). The
support function: for p in C write p_a = q - rho_h p_e with |q| <= kappa_A, so p . y = q y_a + p_e
(e - rho_h y_a) and the supremum over C is kappa_A |y_a| + kappa_E |e - rho_h y_a|.

### 1. The one-instrument pieces

For c, v > 0 and per-side rate k >= 0, AX-15 (with claim 042's lemma) gives the C^2 function
w_k(y) = -(c/(12 v)) y^4 + (a(k)/v) y^2 on [-Delta, Delta], Delta^3 = 3 (2k) v/(4c), a(k) = c Delta^2/2,
extended linearly outside with slopes +-k, which satisfies (v/2) w_k'' + (c/2) y^2 = a(k) on the
band and (v/2) w_k'' + (c/2) y^2 = (c/2) y^2 >= a(k) outside, and |w_k'| <= k everywhere with
|w_k'| = k exactly outside the band. a(k) = (c/2)(3 (2k) v/(4c))^{2/3} is continuous and increasing
in k, with a(0) = 0 (w_0 = 0).

### 2. The sandwich

*Subsolution.* Take k_A', k_E' >= 0 with k_A' + |rho_h| k_E' <= kappa_A and k_E' <= kappa_E, and set
w_1(y_a, e) = w_{k_A'}(y_a) + w_{k_E'}(e) (fund piece with (c^res, v_A), ETF piece with (c_E, v_B^eff)),
a_1 = a_A(k_A') + a_E(k_E'). Since w_1 is a sum of a function of y_a and a function of e, its mixed
second derivative vanishes and (1/2) tr(W D^2 w_1) = (v_A/2) w_{k_A'}''(y_a) + (v_B^eff/2) w_{k_E'}''(e)
whatever the covariance w; by part 1, this plus the cost is >= a_1 everywhere, so the first term
of the equation is <= 0. The gradient Dw_1 = (w_{k_A'}'(y_a), w_{k_E'}'(e)) has |p_e| <= k_E' <= kappa_E
and |p_a + rho_h p_e| <= k_A' + |rho_h| k_E' <= kappa_A, so Dw_1 is in C everywhere and H_C(Dw_1) <= 0.
Growth: Dw_1 in C gives w_1(y) - w_1(0) <= sup_{p in C} p . y = delta_C(y), so lim sup w_1/delta_C <= 1
(delta_C is positive and positively homogeneous off the origin since C has nonempty interior).
By Theorem 3.1, a_1 <= a. Maximizing over admissible (k_A', k_E') gives part 1's lower bound; with
|rho_h| kappa_E < kappa_A the pair (kappa_A - |rho_h| kappa_E, kappa_E) is admissible and gives the
displayed one.

*The third lower bound.* Let w_3(y_a, e) = w_{kappa_E}(e - rho_h y_a), the one-instrument solution
of part 1 with (c_b, v_B) in the variable y_b = e - rho_h y_a, and a_3 = a_b(kappa_E). Its gradient is
w_{kappa_E}'(y_b) (-rho_h, 1), so p_e = w_{kappa_E}' has |p_e| <= kappa_E and p_a + rho_h p_e = 0: Dw_3 is
in C everywhere, and w_3 <= w_3(0) + delta_C as before. Its second derivative matrix is
w_{kappa_E}''(y_b) (-rho_h, 1)(-rho_h, 1)', so (1/2) tr(W D^2 w_3) = (1/2) w_{kappa_E}''(y_b) [v_B^eff -
2 rho_h w + rho_h^2 v_A] = (v_B/2) w_{kappa_E}''(y_b) (the innovation variance of y_b itself). The
cost is at least its minimum over y_a at fixed y_b: c^res y_a^2 + c_E (y_b + rho_h y_a)^2 >= c_b y_b^2
with c_b = c^res c_E/(c^res + rho_h^2 c_E) (a quadratic in y_a minimized at y_a = -rho_h c_E y_b/(c^res
+ rho_h^2 c_E)). So (1/2) tr(W D^2 w_3) + cost >= (v_B/2) w_{kappa_E}'' + (c_b/2) y_b^2 >= a_3 everywhere
by part 1, and w_3 is a subsolution with eigenvalue a_3; Theorem 3.1 gives a >= a_3.

*Supersolution.* Set w_2(y_a, e) = w_{kappa_A + |rho_h| kappa_E}(y_a) + w_{kappa_E}(e) and a_2 = a_A(kappa_A +
|rho_h| kappa_E) + a_E(kappa_E). Where |y_a| <= Delta_A^+ and |e| <= Delta_E (both pieces on their bands),
(1/2) tr(W D^2 w_2) + cost = a_2, so the first term of the equation is 0 and the maximum is >= 0.
Where |e| > Delta_E, |w_{kappa_E}'(e)| = kappa_E, so |p_e| = kappa_E and Dw_2 lies on the boundary of C or
outside it, H_C(Dw_2) >= 0. Where |y_a| > Delta_A^+, |w_{kappa_A + |rho_h| kappa_E}'(y_a)| = kappa_A + |rho_h| kappa_E,
so |p_a + rho_h p_e| >= kappa_A + |rho_h| kappa_E - |rho_h| |p_e| >= kappa_A and again H_C(Dw_2) >= 0. Thus
the maximum is >= 0 everywhere. Growth: w_2(y) >= (kappa_A + |rho_h| kappa_E) |y_a| + kappa_E |e| - const
>= kappa_A |y_a| + kappa_E |e - rho_h y_a| - const = delta_C(y) - const by the triangle inequality, so
lim inf w_2/delta_C >= 1. By Theorem 3.1, a <= a_2.

### 3. Exactness and the gap

With Sigma_AE = 0, rho_h = 0, the two bounds coincide at a_A(kappa_A) + a_E(kappa_E) (and C is the
box, the cost separable, the equation solved by the separable w). For the gap, a_A(kappa_A (1 -+ x))
= a_A(kappa_A) (1 -+ x)^{2/3} since a_A(k) is proportional to k^{2/3}; the derivative of g(x) =
(1 + x)^{2/3} - (1 - x)^{2/3} is (2/3)[(1 + x)^{-1/3} + (1 - x)^{-1/3}] <= (4/3)(1 - x)^{-1/3} on [0, 1),
and integrating from 0 gives g(x) <= 2 [1 - (1 - x)^{2/3}], whose expansion is (4/3) x + O(x^2).

### 4. Readings

(a) is the intermediate value theorem for the continuous increasing a_A on the interval of
rates, and the identification of |rho_h| kappa_E with claim 107's H^+- for one ETF at the
leading order (claim 107's H carries beta and the marking factors, which are the discrete
finite-horizon corrections). (b) and (c) are readings of parts 1-3; the ends are the limits of
the bounds.

## Checks

`checks/043/check.py` (rule 22; floating point). (i) Part 2: on 40 random instances, the
separable sub- and supersolutions satisfy the corrector inequalities on a 121 x 121 grid of the
(y_a, e) plane (the PDE inequality with the eigenvalue; the subsolution's gradient in C
everywhere; the supersolution's gradient on or outside int C wherever its PDE equality fails).
(ii) Part 3: the relative gap equals its stated expression on 200 instances and obeys the
elementary bound, which is checked on a grid of x. (iii) Illustration: a Monte Carlo of a
rectangle policy in (y_a, e) (fund band on y_a moving e by rho_h per unit, ETF band on e) gives
an average cost above the lower bound, as any policy must, and inside the sandwich near the
decoupled sum at the chosen inputs (a rate ratio of one tenth, hedge ratio one half).

## Not shown

- The non-contact set (the fund's cross-section F(xi)): the sandwich bounds the eigenvalue,
  not the region; reading 4(b) is conditional on the band following the effective-rate law.
- The identification of the corrector eigenvalue with the lab's discrete fine-regime average
  cost, and of the non-contact set with the no-trade region (AX-16 records that the source
  itself does not establish the latter; claim 042's cited step).
- Asymmetric rates (the polytope is then a shifted box; the same construction with the
  one-instrument solutions for asymmetric rates, whose band is still symmetric by AX-15).
- Where the effective rate k* lies within the sandwich (it lies in it by reading 4(a); where is
  open, and red's discrete illustration puts it below kappa_A at r >= 0).
- Several ETFs (C becomes a polytope with one constraint per instrument; the separable
  construction extends, with the fund's rate shifted by sum_j |rho_j| kappa_{E,j}).

## Prior art

Mechanism: the two-dimensional corrector problem's eigenvalue is trapped by separable test
functions assembled from one-dimensional corrector solutions, the oblique fund control
entering only through the polytope of admissible gradients, which the separable gradients
respect once the fund's rate is lowered (subsolution) or violated once it is raised
(supersolution) by the hedge ratio times the ETF's rate.

General results checked: AX-16 (`possamai2015homogenization` Theorems 3.1-3.2, Corollary 6.1:
existence, uniqueness and comparison for the first corrector equation in several dimensions;
its Example 3.1 is the cash-only case where the corrector is a sum of one-dimensional
solutions, the same separable structure this claim uses as test functions rather than as the
solution); AX-15 (the one-instrument solution); claim 042 (the coordinates, the polytope's
provenance and the ends); claim 107 (the re-hedge terms H^+- and the residual curvature).
`muhlekarbe2017primer` and `soner2013homogenization` through AX-15.

Searched: claims 029, 042, 107; AX-15, AX-16 and their sources' sections on the corrector
equation; FINDINGS D15c entries. This is a claim because the roadmap asks for F(xi) with
bounds or a closed form and the kill benchmark is the corrector with nothing explicit: the
sandwich is explicit in the inputs, exact with uncorrelated risks, and names the fund-of-funds
structure (the re-hedge rate shift) that the corrector leaves implicit.

## Open objections

PM's hold (2026-09-29) after red's verdict, one revision pass: proof part 0 now carries the
hypothesis check for AX-16 through the change of variables z_A = y_a, z_E = e - rho_h y_a (each
control moves one coordinate, C is the source's cash-only box of Example 3.1, cost and
covariance stay positive definite, eigenvalues, comparison and delta_C transform consistently),
red's required correction; and red's nit, 4(a)'s "proof device" and Not shown's conjecture on the
effective rate weakened to "k* lies in the sandwich; where is open". The analyst's experiment
046 (2026-09-29; rule 22, an illustration): every lattice cell it resolves lies inside the
sandwich; at small xi the pair's cost sits in the lower third, so k* is nearer kappa_A - |rho_h|
kappa_E than the upper end (consistent with red's illustration); at large xi the third bound a_b
is nearly tight (a/a_b 1.08 at xi = 4, 1.02 at xi = 8), which reads as a_b being the leading
order there, not proved. Leanb's prose check (2026-09-29, before red's verdict): the Setting states the hypotheses the
construction needs (positive rates, positive definite Sigma and W, hence v_B^eff > 0); part 1
says the displayed lower bound is a generally weaker instance of the maximum; and 4(c)'s
frozen-end sentence was wrong (the separable lower bound stays bounded as kappa_E grows),
replaced by a third, separately proved lower bound through the ETF's own gap, a >= a_b(kappa_E),
which diverges. Earlier: none. Red should test: the form of the corrector equation used in proof part 0
against the source's (2.5) (the sign and normalization of the gradient term H_C, which only
needs to be negative inside C, zero on its boundary and positive outside); the growth
conditions (the direction of each inequality in Theorem 3.1's hypothesis); the supersolution
at points where exactly one piece is off its band; and whether the covariance w can enter
through the mixed derivative (it cannot for separable test functions, but the true solution is
not separable).

## Review

**Red, 2026-09-29** (on 44df90f8). Red-passed, with one required correction; PM, please hold approval until it lands. Red checked parts 0-3 and the new third lower bound by hand, and tested the test functions numerically. The average-cost illustration below was stopped at the human's instruction (rule 22: it illustrates and decides nothing).

**The open objections.**
- *The equation's form.* refs/text renders the source's (2.5) as max{|sigma rho|^2/2 - (1/2) Tr[alpha-bar alpha-bar' w_rhorho] + a ; ...} = 0. Read literally, that cannot hold off a band, where w is linear and the first term is >= a > 0. The claim's form, max{a - (1/2) tr(W D^2 w) - cost ; H_C(Dw)} = 0, is the one consistent with:
  - AX-15's explicit solution (inside the band, (1/2) alpha-bar^2 w'' = a-bar - sigma^2 rho^2/2);
  - the source's convex w (Theorem 3.2).
  So the text has most likely lost a leading minus in extraction. Red could not render the PDF here.
- *The comparison direction.* The source's proof of Theorem 3.1 compares (1 - eps) w_1 - w_2 and concludes (1 - eps) a_1 - a_2 <= 0, so a subsolution bounds a from below, as used.
- *The growth conditions.*
  - Sub: Dw_1 in C gives w_1(y) - w_1(0) <= delta_C(y), so the lim sup is <= 1.
  - Super: w_2 >= (kappa_A + |rho_h| kappa_E)|y_a| + kappa_E |e| - const >= delta_C - const by the triangle inequality, so the lim inf is >= 1.
- *The supersolution where one piece is off its band.* H_C >= 0 there: |p_e| = kappa_E off the ETF band, and |p_a + rho_h p_e| >= kappa_A off the fund band.
- *The covariance.* It cannot enter separable test functions through the mixed derivative, and it enters the true a (see below).

**Numerical check of the test functions.** On 40 random instances (c^res, c_E, v_A, v_B^eff, rho_h, the rates and the covariance w all drawn, 161 x 161 grid):
- the subsolution's PDE term is <= 6.4e-16 and its gradient lies in C to 2.2e-16;
- the supersolution's max(PDE term, H_C) is >= -8.9e-16.
Both hold pointwise.

**The third lower bound** (5cb1e1e7) is right.
- Only the ETF moves y_b = e - rho_h y_a.
- min over y_a of (c^res/2) y_a^2 + (c_E/2)(y_b + rho_h y_a)^2 = (c_b/2) y_b^2.
- w_{kappa_E}(y_b) has gradient (-rho_h w', w'), which lies in C, and tr(W D^2 w) = v_B w''.
So a >= a_b(kappa_E), and it diverges with kappa_E. That settles the frozen end that leanb flagged. Leanb's other points (the hypotheses stated, the displayed lower bound as an instance) are made.

**Illustration (rule 22, stopped).** Red ran average-cost relative value iteration of the *discrete* pair in holdings coordinates, where the controls are separable: exact L1 transforms, a lazy four-point target walk, band over step about 5.
- *The control.* At Sigma_AE = 0, where a is exactly the decoupled sum, the discrete cost is 0.6% low (discretization).
- *At Sigma_AE = 0.6, kappa_E/kappa_A = 0.4, x = 0.24,* the positions in the sandwich (0 at the lower bound, 1 at the upper) are:
  - r = 0: 0.23;
  - r = -0.8: 0.78;
  - r = +0.8: 0.5% below the lower bound, inside the control's discretization bias.
  The decoupled sum sits at 0.52.
- So r moves a inside the sandwich, and at r >= 0 the effective rate k* of reading 4(a) appears to lie *below* kappa_A. That contradicts the Not shown conjecture "the effective rate lies in [kappa_A, kappa_A + |rho_h| kappa_E]" and 4(a)'s "the lower part of the sandwich being a proof device".
- This is an unrefined discrete illustration, not a finding. Please weaken both to "k* lies in the sandwich; where is open" (a nit).

**Required correction 1 (AX-16's hypotheses).** The claim applies AX-16 to the polytope C = {|p_a + rho_h p_e| <= kappa_A, |p_e| <= kappa_E}. The source's C has the difference form -lambda_{j,i} <= rho_i - rho_j <= lambda_{i,j} (rho_0 = 0), so the application needs one sentence:
- in the coordinates y_a = z_A, e = rho_h z_A + z_E, each control moves one coordinate;
- C is then the source's cash-only box (its Example 3.1, lambda^{i,j} = infinity for i, j >= 1);
- the cost stays a positive definite quadratic and the covariance a positive definite matrix;
- eigenvalues, the comparison principle and delta_C transform consistently under the linear change of variables.
As written, rule 21's hypothesis check for AX-16 is incomplete.

**Mechanism (4b).** The two-dimensional corrector's eigenvalue is trapped by separable test functions from the one-dimensional solutions (AX-15), with the oblique fund control entering only through the gradient polytope, plus a third subsolution in the ETF's own gap. New in the inputs: the re-hedge rate shift |rho_h| kappa_E as the fund's leading-order cost channel.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's required correction 1 (state AX-16's change of variables to the source's cash-only box, completing rule 21's hypothesis check) and red's nit on 4(a) and Not shown's effective-rate conjecture. Math revises, and red records a fresh verdict.


**Red, recheck after PM's hold, 2026-09-29.** Red-passed. Required correction 1 is made (27fa327d).
- *Controls.* In z_A = y_a, z_E = e - rho_h y_a (y = M z, M = [[1, 0], [rho_h, 1]]), a fund trade moves z_A alone (it moves e by rho_h da, which z_E removes) and an ETF trade moves z_E alone.
- *Gradients.* They map as q = M' p = (p_a + rho_h p_e, p_e), so C becomes the box {|q_A| <= kappa_A, |q_E| <= kappa_E}, the source's cash-only case (Example 3.1).
- *Cost and covariance.* The cost is a positive definite quadratic in z. The covariance becomes M^{-1} W M^{-1}', positive definite under the Setting's hypotheses.
- *The equation.* tr(W D^2_y w) = tr(M^{-1} W M^{-1}' D^2_z w~), because D^2_y w = M^{-1}' D^2_z w~ M^{-1}. The sub- and supersolution inequalities are pointwise, and delta_C is invariant: kappa_A |z_A| + kappa_E |z_E| = kappa_A |y_a| + kappa_E |e - rho_h y_a|.
So AX-16 applies with its hypotheses checked. Red re-derived each step.

Red's nit is also made: 4(a) and Not shown now say "k* lies in the sandwich; where is open". Experiment 046 is recorded as an illustration consistent with red's (k* in the lower part at small xi). No other part changed, and red's earlier checks stand.

Verdict: red-passed
## Formalization notes

Approved 2026-09-29 by pm: Red's review and recheck are sound: the separable sub- and supersolutions and the third, diverging lower bound checked by hand and on 40 random instances pointwise to 1e-15; the required correction is made, with AX-16 (audited ok) applied through the change of variables that turns C into the source's cash-only box, with cost, covariance, the equation and delta_C checked to transform consistently; red's nit made (k* lies in the sandwich; where is open); experiment 046 finds every resolved cell inside the sandwich. Mechanism: separable test functions from the one-dimensional solutions (AX-15) trapping the pair's corrector eigenvalue via AX-16's comparison, an application; new in the inputs: the re-hedge rate shift |rho_h| kappa_E as the fund's leading-order cost channel. Limits: the eigenvalue's exact position in the sandwich is open; ergodic level.


Not machine checked. The test functions are explicit polynomials; the inequalities are
pointwise algebra; the comparison principle is cited (AX-16).

Leanb, 2026-09-29: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M7FineCostSandwich.lean` and the proof
  `lean/Novel/M7FineCostSandwichProof.lean`. The proof imports claim 042's proof module, whose
  one-instrument corrector (`wp`, `wpp`, `correctorC2`) it reuses (Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/043/check.py` pass.
- *Setting.* The corrector problem is stated in the inputs gamma, Sigma, v_A, v_B, r and the rates,
  under the Setting's hypotheses. Classical (C^2) sub- and supersolutions have growth
  w_1 <= delta_C + K and w_2 >= delta_C - K.
- *AX-16.* `IsEig P a` says a lies between every classical subsolution's eigenvalue and every
  classical supersolution's. AX-16 enters only as the Prop `AX16`, which says such an a exists, as
  AX-13 did for claims 040 and 104. Every result below holds for every a with `IsEig P a`, so none
  of them assumes AX-16.

Machine checked:
1. Part 1.
   - The separable test functions are C^2 sub- and supersolutions with the growth bounds, which is
     proof part 2.
   - The general lower bound holds for every admissible (k_A', k_E'), and its maximum is attained.
   - The displayed bounds hold.
   - The third lower bound: w_{kappa_E}(e - rho_h y_a) is a subsolution with eigenvalue a_b(kappa_E),
     c_b = c^res c_E/(c^res + rho_h^2 c_E) and v_B, so a >= a_b(kappa_E).
2. Part 2: with Sigma_AE = 0, a = a_A(kappa_A) + a_E(kappa_E), whatever r.
3. Part 3: the identity, and the bound 2[1 - (1 - x)^{2/3}] (by concavity of t^{2/3}).
4. Part 4.
   - 4(a): with |rho_h| kappa_E <= kappa_A, a = a_A(k*) + a_E(kappa_E) for some k* in the sandwich.
   - 4(b)'s arithmetic: Delta_A(k)^3/Delta_A(kappa_A)^3 lies in [1 - x, 1 + x].
   - 4(c): a -> a_A(kappa_A) as kappa_E -> 0, by squeeze; and a -> infinity as kappa_E -> infinity,
     through a_b.

Paper-level:
- part 3's expansion (4/3)x + O(x^2);
- 4(a)'s identification with claim 107's H, and where k* lies (open);
- the readings of F(xi) and of the non-contact set;
- 4(c)'s non-ergodic reading;
- the hypothesis check that AX-16 applies to the pair's problem (proof part 0: the change of
  variables to the source's cash-only box). The Prop `AX16` is stated in the y coordinates this
  check justifies;
- the classical-to-viscosity step and the uniqueness of a (cited).

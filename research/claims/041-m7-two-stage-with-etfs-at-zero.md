---
id: 41
title: "Two-stage exactness when ETFs sit at their zero bound, in the inputs: the fibre-confined procedure is exact iff stage 2's fund holdings satisfy claim 040's bands with stage 1's own one-sided slacks, which stage 1 supplies as valid multipliers without seeing the funds; for one fund, iff the joint holding lies in the fibre interval that stage 1's exposure leaves for it, and the loss is the fund's misplacement in the joint objective, stage 1's exposure being optimal for every by-product on its fibre; the soft procedure stays exact with ETFs at zero whenever the factor Markowitz exposure is in stage 1's set, and with the feasible set it is exact if some fund holding's by-product lies below that exposure in every ETF coordinate, and otherwise iff the joint optimum also solves the tilted second stage"
status: formalized
model_version: M7
depends_on: [27, 28, 31, 40, 102, 104]
axioms_used: [AX-13]
formal: lean/Standalone/M7TwoStageEtfsAtZero.lean
direction: D15d
---
## Statement

D15d's second claim, the two-stage half of the question: claim 104's 2a-2b assume every ETF
strictly inside its box; with ETFs at zero (claim 040's case) the fibre-confined procedure can
force an ETF to zero and cut the fund off, as experiment 029 observed outside claim 104's
hypotheses (43 of 200 draws at a bound, fibre-confined losses up to 7.3 bp per quarter, the soft
procedure exact to solver tolerance; an illustration, rule 22). This claim states, in the inputs,
when each procedure is exact with ETFs at zero and what the fibre-confined one loses. The kill
benchmark (ROADMAP D15d) is claim 104 with the at-zero ETFs dropped from the menu (its 2c on the
reduced menu); what is new is that stage 1 sees the at-zero ETFs one-sidedly, so its exposure is
not the reduced-menu one, and the exactness condition reads on stage 1's own slacks.

**Setting.** Claim 040's parts 2-5 setting with fees off: one review of M7, spanning frictionless
ETFs (M = K, B^E invertible, R = (B^E)^{-1}, kappa_E = 0, Sigma_E = 0, c^E = 0), ETF caps absent
and the budget slack (as in claim 104's 2a, the funded constraint not binding at any solution
considered), fund box 0 <= x^A <= bar x^A, incumbents x^{A-}, the netting matrix Q = R'(B^A)'
(columns r_i), ETF-coordinate exposure w = x^E + Q x^A, mu_E = B^E lambda_hat, Sigma_EE =
B^E Sigma~_f (B^E)', G_E(w) = mu_E' w - (gamma/2) w' Sigma_EE w, the fund terms
H(x^A) = alpha_hat' x^A - (gamma/2) x^A' V x^A - C_A(x^A - x^{A-}), and the value function
V_E(q) = max {G_E(w) : w >= q} with multiplier zeta(q) and at-zero set Z(q) (claim 040 part 2).
Claim 104's procedures in these coordinates: the *fibre-confined* procedure's stage 1 maximizes
G over B_F = b(F), that is, G_E over

```
W_F = { w : w >= Q x^A for some x^A in the box } = Q(box) + R^M_+,
```

at w* (unique), and its stage 2 maximizes H over the fibre {x^A in the box : Q x^A <= w*} at x_2,
value T = G_E(w*) + H(x_2), loss Lambda = J - T with J the joint optimum's value (claim 027,
transferred by claim 104 part 1). The *soft* procedure's stage 1 maximizes G_E over a convex
R_E containing W_F, at w_s with multiplier nu_E = mu_E - gamma Sigma_EE w_s, and its stage 2
maximizes H(x^A) - (gamma/2)(w - w_s)' Sigma_EE (w - w_s) over the box and x^E >= 0 (claim 028),
loss Lambda_s. Write zeta* = gamma Sigma_EE w* - mu_E for *stage 1's slacks*.

1. **Fibre-confined exactness: stage 1's slacks are valid multipliers.** zeta* >= 0, and
   zeta*_j = 0 whenever w*_j > (Q x_2)_j. The procedure is exact, T = J, iff every fund satisfies
   claim 040's band at x_2 with stage 1's slacks in place of the joint ones:

   ```
   G_i := alpha_hat_i - gamma (V x_2)_i - r_i' zeta*   is  = kappa^+_i if x_{2,i} > x^-_i (>= at the cap),
                                                        = -kappa^-_i if x_{2,i} < x^-_i (<= at zero),
                                                        in [-kappa^-_i, kappa^+_i] if x_{2,i} = x^-_i (one-sided at the box).
   ```

   In words: stage 1 does not see the funds, but its one-sided marginals at the at-zero ETFs are
   exactly the prices the joint optimum would put on the funds' by-product there; two-stage is
   exact iff stage 2, which prices the fibre with its own multipliers, lands on holdings that
   are also optimal at stage 1's prices. Where stage 1 leaves an ETF interior (zeta*_j = 0) but
   stage 2's fibre binds at it (the funds want more by-product than w*_j allows), the two prices
   differ and the procedure is inexact unless the fund's band absorbs the difference. Where
   every ETF is interior at both solutions, zeta* = 0 and this is claim 104's 2a.

2. **One fund (N = 1): the fibre interval, the loss and its two parts.** With netting vector r,
   stage 1 is max over x in [0, bar x] of V_E(r x), so it implicitly chooses a fund holding x_1
   that makes the funds' by-product most useful to the exposure (any maximizer; when the factor
   Markowitz exposure w_TB = (gamma Sigma_EE)^{-1} mu_E is reachable the set is an interval on
   which zeta(r x) = 0 throughout and Z(r x) is empty in its interior, an endpoint x = w_TB,j/r_j
   having j in Z with zero multiplier) and sets w* = w(r x_1). Stage 2 sees the *fibre interval*

   ```
   [x_lo, x_hi] = [ max(0, max_{j: r_j < 0} w*_j / r_j),  min(bar x, min_{j: r_j > 0} w*_j / r_j) ],
   ```

   which contains x_1, with x_1 at its upper end when an ETF with r_j > 0 is at zero at stage 1
   (a fund purchase would need to sell it below zero) and at its lower end when one with r_j < 0
   is, and holds the fund at

   ```
   x_2 = clip( clip(x^-, (alpha_hat - kappa^+)/(gamma v), (alpha_hat + kappa^-)/(gamma v)),  x_lo,  x_hi ),
   ```

   claim 102 part 3's frictionless band solution clipped to the fibre interval. With x_J the
   joint holding (claim 040 part 4's root),

   ```
   T = J   iff   x_J lies in the fibre interval [x_lo, x_hi]   (equivalently x_2 = x_J),
   ```

   since V_E(r x) = G_E(w*) is constant on the interval, so the joint holding, if it lies there,
   maximizes H over it and is stage 2's clipped band solution. The loss is the fund's
   misplacement in the joint objective,

   ```
   Lambda = Phi(x_J) - Phi(x_2) >= 0,   Phi(x) = H(x) + V_E(r x),
   ```

   zero iff x_2 = x_J and explicit in the inputs through claim 040's piecewise forms; there is
   no exposure-misfit term, for any N, because stage 2's holdings lie on stage 1's fibre, where
   stage 1's exposure w* is already the optimal exposure for the by-product Q x_2 (V_E(Q x_2) =
   G_E(w*)), so T = Phi(x_2) exactly.

3. **The soft procedure.** (a) If w_TB is in R_E (in particular for an unconstrained stage 1,
   R_E = R^M), then nu_E = 0, stage 2 is the joint problem with the same premia, and Lambda_s = 0
   with ETFs at zero, at caps or anywhere: the soft procedure is exact whenever it was exact
   without the bound (claim 104 3d, restated), which is experiment 029's "exact to 6e-14". (b)
   With R_E = W_F (stage 1 restricted to the feasible exposures), w_s = w*, and the procedure is
   exact if w_TB is in W_F, that is,

   ```
   there is x^A in the box with  Q x^A <= w_TB   (one fund: max(0, max_{r_j < 0} w_TB,j / r_j) <= min(bar x, min_{r_j > 0} w_TB,j / r_j)  and  w_TB,j >= 0 for every j with r_j = 0),
   ```

   the factor Markowitz exposure is reachable without selling an ETF below zero once some fund
   holding carries the by-product. Otherwise nu_E lies in the normal cone of W_F at w*, nonzero,
   0 <= Lambda_s <= nu_E' (w_J - w_2) with w_2 the soft stage 2's exposure (claim 104 part 1, whose
   b_s is stage 2's exposure), and the procedure is exact iff the joint optimum also solves the
   nu_E-tilted stage 2 (claims 027-028's criterion); a nonzero nu_E need not move stage 2 when
   the fund sits at a box bound in both problems and every ETF coordinate with nonzero nu_E
   sits at the funds' by-product, at zero, in both (leanb's example: one fund at zero under a
   negative premium and a negative alpha; the analyst's experiment 040 found inexact draws with
   the fund holdings exactly the joint optimum's and the whole loss in the ETF sleeve, which the
   iff covers since the tilted stage 2 includes w), so unreachability alone does not decide.

4. **Against the benchmark.** Dropping the at-zero ETFs and applying claim 104's 2c gives stage
   1 the reduced menu, on which it chooses the premium-implied fund holding a* for the
   unreachable directions. Here stage 1 keeps the at-zero ETFs, available upward, so its
   exposure w* is the one-sided maximizer: it coincides with the reduced-menu choice only where
   the at-zero set at stage 1 equals the joint optimum's, and part 2's fibre interval shows the
   two sides: an at-zero ETF the fund's purchase would sell caps the fund from above, one its
   sale would sell floors it from below. The exactness condition is not 2c's a* = a_J but part
   1's band with stage 1's slacks, and the loss is the misplacement in the joint objective, whose
   exposure value function carries the one-sided bound.

**One sentence without model nouns.** A first stage that chooses exposures without seeing the
positions still prices, through its idle instruments' one-sided margins, exactly what the
positions' side exposure would be worth to the whole; the split is exact when the second
stage's positions are optimal at those prices, which for one position means the whole's best
holding lies in the room the first stage left for it, and otherwise the loss is the
misplacement of the position in the whole's objective; a first stage that only steers the
exposure softly loses nothing from the bound whenever it aims at the unconstrained best
exposure.

## Proof

### 0. Coordinates and the procedures

Claim 040 proof part 0 gives Q(x) = G_E(w) + H(x^A) with w = x^E + Q x^A and x^E >= 0 iff
w >= Q x^A (fees off). The feasible set F = box x R^M_+ maps to exposures b = (B^E)' w with
w in W_F = {w : w >= Q x^A, x^A in the box} = Q(box) + R^M_+, which is convex and closed (a compact
convex set plus a closed convex cone) and upward closed. Stage 1's objective G(b) = G_E(w) is
strictly concave in w, so w* is unique. The fibre of b* = (B^E)' w* is {x : x^E + Q x^A = w*, x^E >=
0} = {x^A in the box : Q x^A <= w*} with x^E = w* - Q x^A, and on it H depends on x^A alone (fees
off), so stage 2 is as displayed and T = G_E(w*) + H(x_2). The soft stage 2's penalty
(gamma/2)(b - b*)' Sigma~_f (b - b*) equals (gamma/2)(w - w_s)' Sigma_EE (w - w_s).

### 1. Fibre-confined exactness

*Stage 1's slacks.* W_F is upward closed, so for any d >= 0, w* + d is feasible and
G_E(w* + s d) <= G_E(w*) for s > 0 gives grad G_E(w*)' d <= 0, that is, zeta*' d >= 0 for all
d >= 0: zeta* >= 0. Complementarity: the set {w >= Q x_2} is contained in W_F and contains w* (x_2
is on the fibre), so w* maximizes G_E over it; the KKT conditions of that bound-constrained
strictly concave problem (unit constraint gradients, unique multiplier, claim 040 proof part 2)
give zeta*_j (w*_j - (Q x_2)_j) = 0.

*The criterion.* The joint problem is max G_E(w) + H(x^A) over w >= Q x^A, x^A in the box, a
concave maximization over a polyhedron; by AX-13 through claim 104 part 0 (the lifted problem's
qualification holds, the objective being finite), a pair (w, x^A) is optimal iff there are zeta >= 0
with zeta_j (w_j - (Q x^A)_j) = 0, gamma Sigma_EE w - mu_E = zeta (the w-lines, interior in w), and the
fund lines alpha_hat_i - gamma (V x^A)_i - r_i' zeta in the trade-sign and box form displayed
(claim 040 part 3(b)'s reading of the fund lines, with Q' zeta the by-product's price). At the
pair (w*, x_2) the w-lines hold with zeta = zeta* by the two facts above, so the pair is
optimal iff the fund lines hold with zeta*, the display. If they hold, (w*, x_2) is the joint
optimum and T = G_E(w*) + H(x_2) = J. Conversely, if T = J then (w*, x_2) attains the joint
maximum, so it is the (unique) joint optimum and satisfies the joint KKT conditions with the
unique multiplier gamma Sigma_EE w* - mu_E = zeta*, hence the fund lines hold with zeta*. The
readings: where w*_j > (Q x_2)_j, zeta*_j = 0; where the fibre binds, stage 2's own multiplier on
the constraint (Q x^A)_j <= w*_j is what its fund lines carry, and exactness needs the fund lines
to hold with zeta*_j instead. When every ETF is interior at both solutions zeta* = 0 and the fund
lines are claim 104 2a's frictionless bands.

### 2. One fund

*Stage 1 as a choice of holding.* max_{w in W_F} G_E(w) = max_{x in [0, bar x]} max_{w >= r x} G_E(w)
= max_x V_E(r x), and w* = w(r x_1) for any maximizer x_1 (the maximizer over the union of the
sets {w >= r x} lies in one of them and maximizes there; uniqueness of w* means every maximizer
x_1 gives the same w*). V_E(r x) is concave in x (claim 040 part 2, composed with a linear map),
so its maximizers form an interval; when w_TB is in W_F, V_E(r x) = G_E(w_TB) exactly on
{x : r x <= w_TB} and is smaller elsewhere, so the maximizers are that set, on which Z(r x) is
empty.

*The fibre interval.* The fibre {x in [0, bar x] : r x <= w*} is the displayed interval: for
r_j > 0 the constraint reads x <= w*_j/r_j, for r_j < 0 it reads x >= w*_j/r_j, and r_j = 0
imposes nothing (then w*_j >= 0 is stage 1's own feasibility). x_1 is in it since w* >= r x_1;
for j in Z(r x_1), w*_j = r_j x_1, so x_1 = w*_j/r_j is the end the sign of r_j selects.

*Stage 2.* H is concave in one variable with the kink at x^-, so its maximizer over the box is
the band solution x_f = clip(x^-, (alpha_hat - kappa^+)/(gamma v), (alpha_hat + kappa^-)/(gamma v)),
and over the sub-interval it is the clip of x_f to that interval (a concave function of one
variable restricted to an interval is maximized at the clip of its unconstrained maximizer).

*Exactness.* T = J iff (w*, x_2) is the joint optimum iff x_2 = x_J and w* = w(r x_J) (the joint
optimum is unique and its exposure is w(r x_J) by claim 040 part 2). If x_2 = x_J then r x_J <= w*,
so w* maximizes G_E over {w >= r x_J} (it maximizes over the larger W_F and lies in the smaller
set), hence w* = w(r x_J); so T = J iff x_2 = x_J. The interval form: for x in the fibre
interval, r x <= w*, so w* is feasible for V_E(r x) and V_E(r x) >= G_E(w*), while V_E(r x) <=
max_{W_F} G_E = G_E(w*); hence V_E(r x) = G_E(w*) and Phi(x) = H(x) + G_E(w*) on the interval. If
x_J lies in the interval then, x_J maximizing Phi over the box, H(x_J) >= H(x) for every x in the
interval, so x_J is H's unique maximizer there, which is x_2; conversely x_2 lies in the
interval, so x_J = x_2 does. (Leanb's strengthening of the earlier sufficient and necessary
conditions.)

*The loss.* Lambda = J - T = [H(x_J) + V_E(r x_J)] - [H(x_2) + G_E(w*)], using J = Phi(x_J) (claim
040 proof part 0). Since Q x_2 <= w* (x_2 is on the fibre), w* is feasible for V_E(Q x_2), so
V_E(Q x_2) >= G_E(w*); and {w >= Q x_2} is contained in W_F, so V_E(Q x_2) <= max_{W_F} G_E =
G_E(w*). Hence V_E(Q x_2) = G_E(w*), T = Phi(x_2), and Lambda = Phi(x_J) - Phi(x_2) >= 0, zero iff
x_2 = x_J (unique maximizer of the strictly concave Phi). This holds for any N; the analyst's
experiment 040 observed the vanishing of the would-be exposure-misfit term for one fund.

### 3. Soft procedure

(a) Claim 104 part 1 (claim 028's transfer): the soft stage 2 maximizes Q(x) - nu' b(x) + const
over F, so with nu = 0 it is the joint problem and Lambda_s = 0; nu_E = mu_E - gamma Sigma_EE w_s
= 0 iff w_s = w_TB, which is the maximizer over R_E iff w_TB is in R_E. The bound x^E >= 0 is
part of F and changes nothing in this argument. (b) With R_E = W_F, w_s = w* and w* = w_TB iff
w_TB is in W_F, that is, iff some x^A in the box has Q x^A <= w_TB; for one fund this is the
displayed interval condition together with w_TB,j >= 0 at every j with r_j = 0 (no fund holding
carries a by-product there, so the ETF itself must hold the exposure; for w* this is automatic
since w* is in W_F). Otherwise nu_E = -grad(-G_E)(w*) lies in the normal cone of W_F at w* by
stage 1's optimality and is nonzero since w* != w_TB, and claim 104 part 1's bound 0 <= Lambda_s
<= nu' (b_J - b_s), with b_s the soft procedure's final exposure, reads nu_E' (w_J - w_2) in ETF
coordinates (with stage 1's w_s in place of w_2 the right side would be <= 0 by stage 1's
optimality over W_F, which contains w_J). Exactness under a nonzero nu_E: the soft stage 2 is
the joint problem with the premia tilted by nu_E, so Lambda_s = 0 iff the joint optimum solves
that tilted problem (claim 028's criterion through claim 104 part 1); it can, when the fund sits
at a box bound in both problems and the tilt does not lift it off.

### 4. The benchmark

Claim 104's 2c on the menu without Z has stage 1 choose exposure over the reduced feasible set,
whose fund coordinate is the premium-implied holding a*; here stage 1's set W_F keeps each
at-zero ETF's upward direction, so its maximizer differs from the reduced-menu one unless the
reduced menu's unreachable directions are exactly those at zero at w*; part 2's interval gives
the one-sided cap and floor. In both, the loss is the fund's misplacement in the joint objective, since
stage 2 shares stage 1's exposure exactly in 2c and stage 1's exposure is optimal on its fibre here.

## Checks

`checks/041/check.py` (cvxpy/CLARABEL; uses claim 040's check for instances, the joint solver
and the active-set exposure solver; floating point, not a certificate; rule 22). (i) Part 1 on
80 random instances (three funds, two ETFs): stage 1's slacks are nonnegative and complementary
to the fibre at x_2; the procedure is exact iff the bands hold with zeta* at x_2 (both
directions, within solver resolution). (ii) Part 2 on 120 one-fund instances (three ETFs, a
third with strong positive premia so that the ETFs stay interior): the fibre interval and the
clipped band solution against the solver; exactness iff x_J lies in the fibre interval (both
directions); the loss equals Phi(x_J) - Phi(x_2) to 1e-6, the would-be misfit term V_E(r x_2) -
G_E(w*) vanishing. (iii) Part 3 on 60
instances: the soft procedure with an unconstrained stage 1 is exact; with R_E = W_F it is exact
whenever the Markowitz exposure is reachable, the multiplier is nonzero otherwise, the bound
with stage 2's exposure holds, and the cases exact under a nonzero multiplier are counted.

## Not shown

- Fees, ETF frictions and ETF caps (claim 104's 2b bracket with ETFs at zero); a binding budget.
- For N > 1, an explicit form of stage 1's implied fund holdings (part 1's criterion is exact;
  part 2's interval is the one-fund case).
- Bounds on the fibre-confined loss in terms of the inputs beyond the exact form Phi(x_J) -
  Phi(x_2) (claim 104's 3a-3b bounds assume ETFs interior).
- The soft procedure's loss beyond claim 104's multiplier bound when w_TB is unreachable.

## Prior art

Mechanism: the exposure stage's optimality over an upward-closed set makes its one-sided
marginals nonnegative and complementary to any fibre it contains, so they serve as the joint
problem's multipliers on the ETF bound; exactness of the split is then the fund lines at those
multipliers, and for one fund the joint holding's membership in the room the exposure leaves.

General results checked: AX-13 (`rockafellar1970convex`) through claim 104 part 0; claims 027
and 028 (loss identity, criterion and soft procedure) through claim 104 part 1; claim 040 (the
at-zero exposure problem, its multiplier, the fund marginal and the piecewise path); claim 102
part 3 (the band solution); claim 031 (the reduced menu that the benchmark uses);
`jagannathan2003risk` Proposition 1 (the fold-in that claim 040 part 5(d) discusses; the stage
that cannot see the fold-in is this claim's question). Experiment 029 (curve 4 and the 43
at-bound draws) is the illustration that prompted the claim.

Searched: claims 027-028, 031, 040, 102, 104; ROADMAP D15d; experiment 029. This is a claim
because the roadmap asks for the two-stage exactness condition with ETFs at zero, which claims
104 and 040 leave open, and the slack-as-multiplier criterion, the fibre interval and the loss
decomposition are stated by no source.

## Open objections

The analyst's experiment 040, Deviation 5 (2026-09-29, after approval): part 3(b) agrees at every
draw (the reachable case, the normal cone, the bound and the iff); its gloss on exactness under
a nonzero multiplier now also asks the ETF coordinates with nonzero nu_E to sit at the
by-product in both problems, the analyst's observation. Red's review (d085561f, red-passed): the required wording correction is made (the three
sentences that still asserted an exposure-misfit term, in Statement part 4, the one sentence
without model nouns and Proof part 4, now state the misplacement alone) and the nit (the soft
stage aims at the unconstrained best exposure). The analyst's experiment 040 (2026-09-29, before red's verdict): parts 1, 2 and 3(a) agree on
1,000 draws; its observation that part 2's exposure-misfit term is identically zero is right and
holds for any N (stage 2's holdings lie on stage 1's fibre, where w* is already optimal), so
the loss is now stated as the misplacement alone. Leanb's prose check (2026-09-29, before red's verdict): part 3(b)'s "iff" was false (leanb's
one-fund counterexample with the fund at zero in both problems); it now reads "if", with the
exact criterion under a nonzero multiplier; the soft bound uses stage 2's exposure, not stage
1's; the one-fund reachability condition adds w_TB,j >= 0 where r_j = 0; part 2's maximizer
interval has zero multiplier throughout and an empty at-zero set in its interior only; and part
2's exactness is the iff "x_J in the fibre interval", leanb's strengthening. Earlier: none. Red should test: part 1's necessity direction (the joint optimum's uniqueness
and the multiplier's uniqueness carry it); part 2's sufficiency when r_j = 0 for some ETF
(excluded from the interval but not from Z, harmless since r_j zeta_j = 0); whether the check's
instances reach x_J strictly inside the fibre interval; and part 3(b)'s "iff" when w_TB sits on
the boundary of W_F.

## Review

**Red, 2026-09-29** (on 34df9967). Red-passed. Red re-derived each part by hand. It then tested every part with its own cvxpy/CLARABEL solvers (joint problem, stage 1 over W_F, the fibre stage 2, the soft stage 2) and an active-set solver for V_E, written without reading checks/041. The instances are random, with gamma = 1 and Sigma_EE of order 1, so that exactness is decided well above solver resolution. About a quarter of them have an ETF row of Q equal to zero.

**Part 1** (400 instances: 3 funds, 2-3 ETFs; 347 with an ETF at zero at stage 2's x^E, 294 inexact).
- zeta* >= 0 always.
- zeta*_j (w*_j - (Q x_2)_j) = 0 to 1.6e-11.
- "Exact iff the fund lines hold with zeta* at x_2" agrees at 400 of 400, in both directions.
- The argument is sound. Upward closure gives zeta* >= 0. {w >= Q x_2} lies inside W_F and contains w*, which gives complementarity. Joint strict concavity makes the optimum and its multiplier gamma Sigma_EE w - mu_E unique, which carries necessity (the open objection's first point).

**Part 2** (500 one-fund instances, 100 with some r_j = 0).
- x_2 equals the band solution clipped to the displayed fibre interval to 4.1e-10, and x_1 lies in the interval.
- "T = J iff x_J is in [x_lo, x_hi]" holds at 500 of 500. 37 cases have x_J strictly inside, which answers the open objection.
- An r_j = 0 row is harmless: it imposes nothing on x, and r_j zeta_j = 0 in the fund lines.
- **The loss.** Math's last revision states the loss as the misplacement Phi(x_J) - Phi(x_2) alone. This is right for any N, by the same two inequalities as the interval's constancy: Q x_2 <= w* gives V_E(Q x_2) >= G_E(w*), and {w >= Q x_2} lies inside W_F. On 300 further instances with N = 1-3, |V_E(Q x_2) - G_E(w*)| <= 1.3e-12 and Lambda = Phi(x_J) - Phi(x_2) to 1.3e-12, with V_E computed by active-set enumeration.

**Part 3** (400 instances, 1-3 funds).
- (a) With an unconstrained stage 1, the soft procedure is exact at 400 of 400.
- (b) With R_E = W_F:
  - When w_TB is in W_F (an LP feasibility test), it is exact at 125 of 125. The one-fund form, the interval plus w_TB,j >= 0 at r_j = 0, matches the LP at every one-fund instance.
  - When w_TB is unreachable (275), 0 <= Lambda_s <= nu_E'(w_J - w_2) never fails.
  - nu_E'(w_J - w_s) <= 0 at 275 of 275, so the bound with stage 1's exposure would force Lambda_s = 0. Leanb's correction is needed.
  - 13 unreachable cases are exact under a nonzero nu_E. So "if", not "iff", is right, and the tilted-stage criterion is the exact test (the tilted objective is strictly concave, so its solution is unique).
- Leanb's example reproduces: the joint and soft solutions are (0, 0), up to solver slack, because the tilted objective is flat to first order in w at 0.

**Mechanism (4b).** Stage 1's optimality over an upward-closed set makes its one-sided marginals valid joint multipliers on the ETF bound. Exactness is the fund lines at those prices. For one fund, it is membership of the joint holding in the room stage 1 leaves. An application of claims 027-028 and 104 parts 0-1 to claim 040's at-zero geometry, new in the slack-as-multiplier criterion and the fibre interval.

**Required correction 1 (wording; no result changes).** Math's last revision proved the exposure-misfit term zero in part 2, but three sentences still assert it:
- Statement part 4, last sentence: "and the loss has the exposure-misfit part that 2c lacks";
- the one sentence without model nouns: "otherwise the loss is the misplacement of the position plus the misfit of the exposure held for it";
- Proof part 4: "The exposure-misfit term in part 2's loss is absent in 2c, whose stage 2 shares stage 1's exposure exactly".

Each should drop the misfit. For example, part 4 could end at "...but part 1's band with stage 1's slacks", and the plain sentence could say "otherwise the loss is the misplacement of the position".

**Nit** (not required). The same sentence says the soft first stage "loses nothing from the bound whenever it aims at a reachable exposure". With R_E = W_F the aim w* is always reachable, and exactness needs the *unconstrained* best exposure w_TB to be reachable. Suggest "whenever the unconstrained best exposure is reachable".

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: parts 1-3 re-derived by hand and tested with red's own solvers (part 1 400/400 both directions, part 2's fibre-interval iff 500/500 with 37 strictly inside, the misplacement-only loss for N = 1-3 to 1.3e-12, part 3(a) 400/400, 3(b)'s 'if' with 13 exact cases under nonzero nu_E); leanb's four corrections and the analyst's misfit observation are in, and red's required wording correction is the only change since (9d5c055d). Mechanism: claims 027-028 and 104 parts 0-1 applied to claim 040's at-zero geometry; new: stage 1's one-sided slacks as joint multipliers and the one-fund fibre interval, so D15d's kill criterion is not met. Limits: fees off, frictionless spanning ETFs, slack budget; soft loss beyond claim 104's bound not shown.


Not machine checked. KKT of a concave quadratic program with bound constraints; a one-variable
concave maximization over an interval; an exact loss decomposition.

Leanb, 2026-09-29 (first stage): machine checked, in the scope PM confirmed (rule 6b). This
supersedes "Not machine checked" above. The statement is in `lean/Standalone/M7TwoStageEtfsAtZero.lean`
and the proof in `lean/Novel/M7TwoStageEtfsAtZeroProof.lean`. `lake build`, the axiom audit (standard
axioms only) and `checks/041/check.py` pass. No hypothesis structure or cited result is used. AX-13
is not needed: every first-order condition is proved by difference quotients and a saddle
argument.

Claim 040's objects. `TS` extends `Etf` in `lean/Standalone/M7EtfCoordinates.lean`. That file is a
temporary copy of claim 040's ETF-coordinate objects: G_E, zeta, w_TB, V_E, w(q) and Z(q), with
their well-posedness proved in `lean/Novel/M7EtfCoordinatesProof.lean`. Lean's claim 040 module
(lean/Standalone/M7FundDecisionEtfsAtZero.lean, `Coord`) was not yet on main. A second stage switches
`TS` to lean's module and deletes the copy (PM, 2026-09-29).

Formal objects. The setting is the claim's, in ETF coordinates with fees off:
- mu_E, Sigma_EE (positive definite), gamma > 0, the netting matrix Q, and the fund box;
- V positive semidefinite (claim 040 assumes it positive definite; the results hold under the
  weaker assumption, with part 2 assuming v > 0);
- rates >= 0 and incumbents in the box.
W_F, the fibre and the joint feasible set are as defined in the claim. Every result is stated for
any maximizers, and `Existence` proves they exist, with stage 1's exposure unique.

Machine checked:
1. Part 1.
   - zeta* >= 0 and complementarity with Q x_2.
   - T = J iff the fund lines, displayed with their one-sided box forms, hold at x_2 with zeta*.
   - V_E(Q x_2) = G_E(w*) for any N.
2. Part 2 (one fund).
   - Stage 1 as a choice of holding x_1.
   - The maximizing holdings form an interval; when w_TB is reachable they are {x : r x <= w_TB},
     with V_E = G_E(w_TB) there.
   - The fibre is [x_lo, x_hi], with x_1 at the end an at-zero ETF selects.
   - x_2 = clip(x_f, x_lo, x_hi), the unique maximizer.
   - T = J iff x_2 = x_J iff x_J is in [x_lo, x_hi], with the strictly-inside form as a corollary.
   - J = Phi(x_J), T = Phi(x_2), and the loss is Phi(x_J) - Phi(x_2) >= 0.
   - w_TB is in W_F iff x_lo(w_TB) <= x_hi(w_TB) and w_TB,j >= 0 wherever r_j = 0.
3. Part 3.
   - (a) w_TB in R_E gives nu_E = 0 and a zero soft loss.
   - (b) With R_E = W_F, nu_E = 0 iff w_TB is in W_F, and then the soft procedure is exact.
   - Otherwise nu_E != 0 lies in the normal cone, 0 <= Lambda_s <= nu_E'(w_J - w_2) with w_2 stage
     2's exposure, and Lambda_s = 0 iff the joint optimum solves the tilted stage 2.

Paper-level:
- Part 0, the reduction of M7 to these coordinates (claims 040 and 104).
- Part 4's reading against claim 104's 2c.

Leanb, 2026-09-29 (second stage): claim 040's objects now come from lean's claim 040 module, and
the temporary copy (lean/Standalone/M7EtfCoordinates.lean and its proof) is deleted. `TS` extends
claim 040's `Coord` (lean/Standalone/M7FundDecisionEtfsAtZero.lean). `GE` and `VE` are claim 040's.
The field names follow lean's: `Sig` = Sigma_EE, `alt` = alpha_hat with fees off, `xbar` = the fund
caps. This claim keeps two objects of its own:
- the slack zeta(w) = gamma Sigma_EE w - mu_E at a given exposure; claim 040's zeta(q) is the same
  slack at w(q);
- w_TB.
The standing assumptions are unchanged (V positive semidefinite). No statement changed; `lake
build`, the axiom audit and `checks/041/check.py` pass.

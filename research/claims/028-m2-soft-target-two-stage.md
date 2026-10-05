---
id: 28
title: "The soft-target two-stage procedure in M2 (experiments 018-019) is the joint problem with the premia the target implies; its loss is at most stage 1's multiplier times the exposure distance, less the risk of the holding move, and is zero when the two solutions share an exposure"
status: formalized
model_version: M2
depends_on: [4]
axioms_used: []
formal: lean/Standalone/M2SoftTargetTwoStage.lean
direction: D4
---
## Statement

D4's second claim. Experiments 018 and 019 (analyst) ran a two-stage
procedure whose second stage is not confined to the target's exposure but
penalizes the distance from it (018's "2S-alpha"); experiment 019 Part S
found, on all 720 calibrated cells, that its loss is at most stage 1's
multiplier vector times the exposure difference, exactly that minus the
risk of the holding move in 560 cells, and zero exactly when the exposure
difference is zero. This claim proves those three facts for every M2
instance, and identifies the procedure. It is self-contained: the split of
the score it uses is restated below (it is claim 027's, on branch
math/claim027-two-stage, but nothing here rests on that claim).

**Setting.** Any M2 instance: one active fund and n in {1,2} ETFs with
loading matrix B (rows the instruments' factor loadings), belief means
lambda_bar (factor premia) and alpha_bar, factor shock covariance Sigma_f
(2-by-2, positive semidefinite), full risky covariance Sigma = B Sigma_f B'
+ (residual and cross terms), gamma>=0, the funded class F (nonempty,
convex, compact; claim 004), post-trade risky dollar holdings w, exposure
b(w)=B'w, and the implemented criterion

```
Qbar_0(w) = b(w)'lambda_bar - (gamma/2) w'Sigma w + a alpha_bar - p'c^E - tau(w-w^-),
```

concave in w (claim 004), with w'Sigma w = b(w)'Sigma_f b(w) + 2 b(w)'C(w)
+ R(w) for the cross and residual second moments C, R of the holding. The
joint optimum J = max_F Qbar_0 is attained (claim 004), at some w_J with
exposure b_J.

**The soft-target two-stage procedure.**
- *Stage 1.* A convex set R of exposures with b(F) subset of R (experiment
  018 uses R_0 = {B'w : w>=0, sum_i w_i <= 1}, the convex hull of 0 and the
  loading rows, which contains b(F) since a funded holding has nonnegative
  risky dollars summing to at most the unit wealth), and a target b* that
  maximizes the factor objective G(b) = b'lambda_bar - (gamma/2) b'Sigma_f b
  over R (attained: G is continuous and concave, R_0 is compact; in
  general assume attainment). Stage 1 sees lambda_bar, Sigma_f, gamma and
  R only. Its *multiplier vector* is nu = grad G(b*) = lambda_bar - gamma
  Sigma_f b*.
- *Stage 2.* Maximize over w in F the *soft-target objective*

  ```
  S(w) = a alpha_bar - p'c^E - tau(w-w^-) - (gamma/2)[ (b(w)-b*)'Sigma_f (b(w)-b*) + 2 b(w)'C(w) + R(w) ],
  ```

  the residual score with the factor risk charged on the distance from the
  target (018's 2S-alpha; its 2S-lit drops alpha_bar and c^E and is not
  treated here). Attained at some w_2 with exposure b_2 (S is continuous
  and concave on the compact F).
- *Two-stage value* T_s = Qbar_0(w_2) and *loss* Lambda_s = J - T_s >= 0.

Write Delta e = b_J - b_2 and Delta w = w_J - w_2.

1. **Identification.** For every w,

   ```
   S(w) = Qbar_0(w) - nu'b(w) - (gamma/2) b*'Sigma_f b*.
   ```

   Hence stage 2 is the joint M2 problem with the premia lambda_bar
   replaced by the *target-implied premia* lambda_hat = gamma Sigma_f b*
   (the premia under which the target is the unconstrained factor optimum),
   and it differs from the joint problem exactly by the linear term
   -nu'b(w): the procedure is the joint problem with the multiplier
   subtracted from the premia. In particular, if nu = 0 (the unconstrained
   factor optimum lies in R and is chosen), stage 2 is the joint problem
   and Lambda_s = 0.

2. **Multiplier bound.** For any F (convexity not needed for this part)
   and any maximizers w_J, w_2,

   ```
   0 <= Lambda_s <= nu'Delta e <= nu'(b* - b_2),
   ```

   the second inequality with equality iff w_J also maximizes S on F, and
   the third because nu'(b_J - b*) <= 0 (b_J is in R and b* maximizes the
   concave G on R). Consequently Lambda_s = 0 whenever Delta e = 0, that
   is, whenever the joint and the soft two-stage solutions share an
   exposure (experiment 019's 254 zero-loss cells all have Delta e = 0),
   and Lambda_s = 0 whenever b_2 = b*, the second stage reaching the
   target (which the calibrated cells never do, Not shown); and by
   Cauchy-Schwarz, in the Euclidean norm, Lambda_s <= |nu| |Delta e|: the
   loss is at most the multiplier's length times the exposure distance.

3. **Exact form.** Since F is convex, S is concave, and its quadratic part
   is -(gamma/2) w'Sigma w plus affine terms,

   ```
   Lambda_s = nu'Delta e - (gamma/2) Delta w'Sigma Delta w - s,   s >= 0,
   ```

   where s = -S'(w_2; Delta w) + k >= 0 is the sum of the first-order
   optimality slack of w_2 in the direction Delta w (the directional
   derivative -S'(w_2; Delta w) >= 0, which is the binding constraints'
   multipliers times Delta w's components into them) and the cost kink
   term k = [tau(w_J-w^-) - tau(w_2-w^-)] - tau'(w_2-w^-; Delta w) >= 0,
   zero when no instrument's trade changes sign between w_2 and w_J
   ((w_2-w^-)_i (w_J-w^-)_i >= 0 for every i). So
   Lambda_s <= nu'Delta e - (gamma/2) Delta w'Sigma Delta w always, with
   equality iff s = 0, which is experiment 019's exact form (560 of 720
   cells) and the general inequality (720 of 720).

4. **Relation to the fibre-confined procedure** (claim 027's, stage 2
   confined to {w in F : b(w) = b*}, value T = max of the residual
   objective on the fibre plus G(b*), when the fibre is nonempty). Since
   any holding w_T attaining T is feasible for the soft stage 2,
   T_s >= T - nu'(b* - b_2), so the soft procedure's loss exceeds the
   fibre-confined one's by at most nu'(b* - b_2): Lambda_s <= Lambda +
   nu'(b* - b_2). No ordering between T_s and T holds in general (Not
   shown).

5. **What the multiplier is.** nu lies in the normal cone of R at b*
   (optimality of b* for the concave G on the convex R), so it is the
   Lagrange multiplier vector of the stage-1 constraint b in R: when R =
   R_0 and b* lies on a face of R_0, nu is normal to that face. The loss
   bound in part 2 is therefore the value of the stage-1 constraint's
   multiplier on the exposure the joint optimum takes beyond the target.
   Since nu = lambda_bar - lambda_hat, the same bound reads: the loss is at
   most the difference between the believed premia and the target-implied
   premia, applied to the exposure difference.

**One sentence without model nouns.** Charging the second stage for the
distance from the first stage's target is the same as re-running the joint
problem with the returns the target implies, so the loss is at most the
first stage's constraint multiplier applied to the exposure the joint
choice takes beyond the target, less the risk of the move, and vanishes
when the second stage reaches the target; the funded constraint enters
only through that multiplier.

## Proof

### 1. Identification

Expanding the target distance, (b-b*)'Sigma_f(b-b*) = b'Sigma_f b -
2 b*'Sigma_f b + b*'Sigma_f b*, so

S(w) = a alpha_bar - p'c^E - tau(w-w^-) - (gamma/2)[b'Sigma_f b + 2b'C + R]
+ gamma b*'Sigma_f b - (gamma/2) b*'Sigma_f b*
= Qbar_0(w) - lambda_bar'b + (gamma Sigma_f b*)'b - (gamma/2) b*'Sigma_f b*
= Qbar_0(w) - nu'b(w) - (gamma/2) b*'Sigma_f b*,

with b = b(w). Replacing lambda_bar by lambda_hat in Qbar_0 subtracts
(lambda_bar - lambda_hat)'b = nu'b, which is the displayed identity up to
the constant. If nu = 0, S and Qbar_0 differ by a constant on F, so w_2
maximizes Qbar_0 and Lambda_s = 0.

### 2. The multiplier bound

w_2 maximizes S on F and w_J is in F, so S(w_J) <= S(w_2). By part 1,
Qbar_0(w_J) - nu'b_J <= Qbar_0(w_2) - nu'b_2, that is, Lambda_s = J - T_s
<= nu'(b_J - b_2) = nu'Delta e, with equality iff S(w_J) = S(w_2). Lambda_s
>= 0 since w_2 is in F. For the third inequality, G is concave and
differentiable on the convex R with maximizer b*, so for every b in R,
0 >= G(b) - G(b*) >= ... is not the right direction; use instead the
first-order condition: for t in (0,1], b* + t(b - b*) is in R, so
G(b* + t(b-b*)) <= G(b*); dividing by t and letting t -> 0 gives
grad G(b*)'(b - b*) = nu'(b - b*) <= 0. Apply it to b = b_J, which lies
in b(F) subset of R. Then nu'Delta e = nu'(b_J - b*) + nu'(b* - b_2) <=
nu'(b* - b_2). If Delta e = 0 the middle term is 0, and if b_2 = b* the
right side is 0; either way Lambda_s = 0. The Euclidean bound is
Cauchy-Schwarz on nu'Delta e.

### 3. The exact form

Fix w_2 and w_J and set w(t) = w_2 + t Delta w, t in [0,1], which lies in
F by convexity. Write S = A - (gamma/2) w'Sigma w - tau(w-w^-) with A
affine in w (part 1: S differs from Qbar_0 by an affine function of w, and
Qbar_0's non-affine parts are the quadratic and the cost). Then

S(w_J) - S(w_2) = [A(w_J)-A(w_2)] - (gamma/2)[w_J'Sigma w_J - w_2'Sigma w_2]
- [tau(w_J-w^-) - tau(w_2-w^-)].

The quadratic difference is 2 w_2'Sigma Delta w + Delta w'Sigma Delta w.
The cost tau is convex and piecewise linear, so its directional derivative
tau'(w_2-w^-; Delta w) exists and tau(w_J-w^-) - tau(w_2-w^-) =
tau'(w_2-w^-; Delta w) + k with k >= 0 (convexity), k = 0 when tau is
linear along the segment, that is, when no coordinate of w(t)-w^- changes
sign on [0,1]. Collecting the first-order terms, S'(w_2; Delta w) =
[A(w_J)-A(w_2)] - gamma w_2'Sigma Delta w - tau'(w_2-w^-; Delta w), so

S(w_J) - S(w_2) = S'(w_2; Delta w) - (gamma/2) Delta w'Sigma Delta w - k.

Optimality of w_2 on the convex F gives S(w(t)) <= S(w_2) for t in (0,1],
hence S'(w_2; Delta w) <= 0. By part 1, S(w_J) - S(w_2) = [Qbar_0(w_J) -
nu'b_J] - [Qbar_0(w_2) - nu'b_2] = Lambda_s - nu'Delta e, so Lambda_s =
nu'Delta e - (gamma/2) Delta w'Sigma Delta w - s with s = -S'(w_2; Delta w)
+ k >= 0, the sum of two nonnegative terms. When F is described by the linear
constraints of M2 and the directional derivative is a Lagrangian
expression, -S'(w_2; Delta w) is the sum over binding constraints of the
multiplier times the constraint's linearization along Delta w (KKT for a
concave program with linear constraints), which is the "slack" reading;
this reading is not needed for the inequality.

### 4. Relation to the fibre-confined procedure

Let w_T be in F with b(w_T) = b* and Qbar_0(w_T) = T (a fibre maximizer
plus G(b*), the fibre being nonempty by assumption). Then S(w_T) <= S(w_2)
gives Qbar_0(w_T) - nu'b* <= Qbar_0(w_2) - nu'b_2, that is, T_s >= T -
nu'(b* - b_2); subtracting from J gives Lambda_s <= Lambda + nu'(b* - b_2).

### 5. The multiplier

nu'(b - b*) <= 0 for all b in R (part 2) is the statement that nu is in
the normal cone of R at b*. When R = R_0 is a polytope and b* is in the
relative interior of a face, the normal cone is the face's normal cone, so
nu is normal to it; if b* is interior to R_0, nu = 0 and part 1 applies.

## Checks

`checks/028/check.py` (exits non-zero on failure; a check, not a proof).
On experiment 006's calibration (geometries G1-exact, G2-missing,
G3-infeasible; costs Z and EQ5; alpha from -50 to +50 bp; gamma 5; start
S1), floating CLARABEL solves of the joint problem, stage 1 over R_0 and
over b(F), the soft stage 2 and the fibre-confined stage 2: it verifies
the identity of part 1 at random holdings, the containment b_J in R_0
(nu'(b_J - b*) <= 0), the bounds of parts 2-4, and that the loss is zero
whenever Delta e = 0 (12 of the 30 cells at alpha +25 and +50 bp, where
both solutions hold the active fund at its cap and the same ETF position)
or b_2 = b* (never on these cells: the soft stage 2, seeing the
target-implied premia, does not stop at the target). The soft and the
fibre-confined losses order both ways on the same cells: at alpha -50 bp
in G3-infeasible the soft loss is 0.1 bp and the fibre-confined 22.4 bp,
and at alpha +25 bp in G1-exact the soft loss is 0 and the fibre-confined
0.64 bp. Experiment 019 Part S (analyst, exact rationals on 018's
720 cells) is the calibrated statement: the bound holds in 720 of 720,
the exact form with s = 0 in 560, zero loss iff Delta e = 0 in all 254
zero-loss cells, the ratio of loss to nu'Delta e between 0.110 and 0.999
(median 0.771), and |nu| between 61 and 77 bp per unit exposure.

## Not shown

- The converse "Lambda_s = 0 only if Delta e = 0" is not proved; it is
  false when nu = 0 (then any joint optimum is a stage-2 optimum whatever
  its exposure). Experiment 019 found it on its grid, where nu is never 0.
- No ordering between T_s and T in general: the soft stage 2 may move off
  the target (gaining) or the fibre may be empty (T undefined); part 4 is
  one-sided, and the check shows both orderings.
- The target-reached case b_2 = b* of part 2 is vacuous on the calibrated
  cells (the soft stage 2 never stops at the target there); the zero-loss
  cells are those where the joint and soft solutions coincide. Experiment
  019 (analyst, exact rationals on 018's results) confirms that in all
  254 zero-gap cells the two holdings are identical, w_J = w_2, with both
  optima unique, not merely the same exposure.
- The slack reading of s as multipliers times displacement is stated for
  the linear-constraint description of F and not used in the proof.
- The 2S-lit variant (stage 2 without alpha_bar and c^E) is not treated;
  part 1's identification fails for it, since dropping alpha_bar changes
  the residual score, not only the premia.
- The stage-1 attainment over a general convex R is assumed; for R_0 it
  holds.
- The calibrated numbers are the analyst's (experiment 019, reported); the
  check reproduces the inequalities in floating point on a subgrid.
- The four separation sources are read at full text and cited by page;
  nothing in the proof rests on them (the librarian's treynor-black-readable
  note is handled here and on claim 027's branch).

## Prior art

Mechanism: A second stage that charges a quadratic penalty for the
distance from a first-stage target is the joint problem with the target's
implied linear coefficients in place of the true ones, so by comparing
the two objectives at each other's optimizers its loss is bounded by the
coefficient difference, the first-stage constraint's multiplier, applied
to the difference of the two solutions' images, with a concave remainder.

General results checked: this is weak duality for a linear relaxation of
the stage-1 constraint (the multiplier nu is the constraint's Lagrange
multiplier and the bound is the Lagrangian's value on the joint solution),
elementary and proved inline in part 2 rather than cited; the shadow-price
mechanism of constrained portfolio results that the librarian's D4 sweep
named as the working hypothesis, `liu2013portfolio` (Theorem 2.3, Lemma
5.2: a binding cap's shadow price sets a no-trade width),
`dai2011illiquidity` (Propositions 3-4) and `bichuch2014investing`
(sections 2.2-2.3), which are the same mechanism in other objects, none of
which states a two-stage loss bound; the kill benchmark
`treynor1973security` (Treynor and Black 1973, at full text): its world
has "no restrictions on borrowing, or on selling securities short" (p. 67),
so its exposure set is the whole plane, the stage-1 multiplier nu is 0,
and part 1 makes the procedure the joint problem, which is the paper's
unconstrained Markowitz solution, equation (17) (p. 73-74); its specific
positions, equation (13) (p. 71-72), are the residual rule the soft stage
2 applies with the target-implied premia, and its explicit market
position, equation (16) (p. 72), is the netting that a funded long-only
class removes, which is where nu becomes nonzero; the separation theorems
`merton1972analytic` (Theorem I, p. 1857; Theorem II, p. 1864-1865, an
unrestricted riskless fund), `tobin1958liquidity` (section 3.6, the
composition of non-cash assets independent of their share) and
`cass1970structure` (monetary separation, p. 126-127; Theorems 3.1 and
6.1 on preferences), all at full text, are the nu = 0 case: Merton
(footnote 3, borrowing and short sales allowed) and Cass-Stiglitz
(footnote 4, short sales permitted) with an unrestricted riskless
position, and Tobin with nonnegative holdings summing to at most one
("All x_i are non-negative, and sum x_i = A <= 1", scan p. 42), so with no
borrowing, his separation holding while cash is positive, that is, while
the stage-1 constraint is slack; none states a loss bound for a
constrained stage 1;
`platanakis2019horses` Proposition 1 (estimators within a fixed two-stage
procedure, not a loss bound against the joint optimum); `pastor2002investing`
(joint problem only); claims 004 (attainment, concavity of the score) and
027 (the fibre-confined procedure, on its branch, referred to for part 4
only); experiments 018 and 019 (the procedure and the fit).

Searched: claims 004-009 and 027, the D4 roadmap entry, the librarian's D4
sweeps (FINDINGS, 2026-09-27 and 2026-09-28), experiments 018-019, and the
refuted directory. This is a claim because experiment 019's three
empirical regularities needed a proof and an identification of the
procedure the experiments ran, which no registered source states; the
result reads toward D4's kill (PM's reading, NOTICES 2026-09-28: a
constraint multiplier alone is not a structural leftover), and no priority
is claimed for any ingredient.

## Open objections

Lean (2026-09-28, note): two sign slips in part 3, s = -S' - k for
s = -S' + k in the Statement, and S(w_J) - S(w_2) = -Lambda_s - nu'Delta e
for Lambda_s - nu'Delta e in the Proof. Accepted and fixed; the displayed
result was already the corrected one. Red should test: part 3's kink term when a trade changes
sign between w_2 and w_J; the containment b(F) subset of R_0 under
experiment 018's normalization of wealth; part 4 when the fibre is empty;
and whether the check's stage 1 over R_0 matches experiment 018's exact
stage 1 on the hull's segments.

## Review

**Red, 2026-09-28.** I checked every part by hand and tested them on random instances of my own (red's script, not committed).

**Hand check.**
- *Part 1.* S - Qbar_0 = -(gamma/2)[(b-b*)'Sigma_f(b-b*) - b'Sigma_f b] - lambda_bar'b = -nu'b - (gamma/2) b*'Sigma_f b*. This holds for every Sigma, cross moments included, so S is concave whenever Qbar_0 is. Unlike claim 027's V, nothing here needs C = 0.
- *Part 2.* S(w_J) <= S(w_2) gives Lambda_s <= nu'Delta e, with equality iff w_J maximizes S. The step to nu'(b* - b_2) needs b(F) subset of R_0. That holds because a funded holding is nonnegative and sums to at most 1 - costs <= 1 (W^- = 1), which answers the second Open objection. The first-order condition of b* on the convex R gives nu'(b_J - b*) <= 0. The Cauchy-Schwarz form is right.
- *Part 3.* This is the corrected version.
  - The quadratic difference is 2w_2'Sigma Delta w + Delta w'Sigma Delta w.
  - Convexity of tau gives k >= 0, and k = 0 when (w_2 - w^-)_i (w_J - w^-)_i >= 0 for every i. This answers the first Open objection.
  - -S'(w_2; Delta w) >= 0 by optimality on the convex F.
  - S(w_J) - S(w_2) = Lambda_s - nu'Delta e.
  - Hence Lambda_s = nu'Delta e - (gamma/2) Delta w'Sigma Delta w - s with s = -S' + k >= 0.

  Red confirmed lean's two sign slips independently (red's note, 2026-09-28); both are fixed.
- *Part 4.* A fibre maximizer w_T is feasible for the soft stage 2, so Qbar_0(w_T) - nu'b* <= Qbar_0(w_2) - nu'b_2. This gives Lambda_s <= Lambda + nu'(b* - b_2). With an empty fibre, T is undefined and the part says nothing, which answers the third Open objection.
- *Part 5.* nu lies in the normal cone of R at b*, and nu = 0 at an interior b*. Both are correct.

**Independent tests.**
- *Random instances.* 200 random M2 instances with factor-correlated residual shocks (C != 0), one or two ETFs, random directional rates up to 50 bp, gamma in {2, 5, 10} and random incumbents. The soft stage 2 is solved as the joint problem with premia lambda_bar - nu. There are **no violations** of part 1's identity (at random holdings), the containment nu'(b_J - b*) <= 0, or the bounds 0 <= Lambda_s <= nu'Delta e - (gamma/2) Delta w'Sigma Delta w. The exact form (s = 0) holds in 127 of 200.
- *Calibrated cells.* Red's reproduction of experiment 019 Part S already confirms the calibrated statement exactly on experiment 018's 720 cells: bound 720/720, exact form 560/720, zero loss iff Delta e = 0.
- *The claim's check.* `checks/028/check.py` passes on this branch, which answers the fourth Open objection at check level.

**Prior art at full text.**
- *Treynor-Black.* The reading now matches the text: an unrestricted world (p. 67), the specific positions of eq. (13), and the explicit, possibly short, market position of eq. (16) as the netting that funded long-only removes.
- *Nit: Tobin.* "The separation theorems ... are the nu = 0 case with an unrestricted riskless position" is right for Merton 1972 (fn. 3) and Cass-Stiglitz (fn. 4), but not for Tobin. Tobin's holdings are nonnegative and sum to at most one, so there is no borrowing, and his separation holds while cash is positive. See red's note to math, 2026-09-28-d4-sources-fulltext.

**Mechanism (4b).** A quadratic target penalty is the joint problem with the target's implied linear coefficients, and the loss is bounded by the Lagrange multiplier of the relaxed stage-1 constraint (weak duality). This is elementary and an application, as the claim says. It reads toward D4's kill: the funded constraint enters only through nu.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check of all five parts is sound: the identification holds for any Sigma, cross moments included; the multiplier bound uses b(F) in R_0 with funded wealth at most 1; the exact form's kink term and first-order slack are nonnegative after lean's two sign fixes; part 4 with an empty fibre says nothing. Red's 200 random M2 instances with factor-correlated residuals show no violation, and red's reproduction of experiment 019 Part S confirms the calibrated statement (bound 720/720, exact 560/720, zero loss iff equal exposure). Mechanism: weak duality for the relaxed stage-1 constraint, an application; the funded constraint enters only through the multiplier, which reads toward D4's kill. Treynor-Black checked at full text. Limit: nothing on the fibre-confined procedure's ordering. Nit to math: Tobin's separation has no borrowing, so it is not the nu=0 unrestricted case.


Not machine checked. Parts 1-2 are algebra and one comparison of two
maximizers; part 3 is the directional derivative of a concave quadratic
plus a convex piecewise-linear cost along a segment; parts 4-5 are one
inequality each.

Lean, 2026-09-28 (final): parts 1-5 are machine checked. The statement is
in `lean/Standalone/M2SoftTargetTwoStage.lean` and the proof in
`lean/Novel/M2SoftTargetTwoStageProof.lean`. `lake build` and the axiom
audit pass (standard axioms only). No hypothesis structure or cited result
is used. The files are self-contained: they restate Sigma_f, C, R and G and
import only claim 004's proof module (depends_on [4], Q-04). Nothing rests
on claim 027.

Formal objects. The counts are general (m active funds, n ETFs, K factors),
and the criterion is the score at any parameter theta. By claim 003, Qbar_0
is the score at the belief mean. `nu`, `thetaHat`, `Ssoft` and `R0` are nu,
the target-implied parameters, S and R_0. `Dplus`, `tauD` and `SD` are the
one-sided directional derivatives: `Dplus` of max(x + t y, 0), then
tau'(v; d) and S'(w; d). Each is proved to be the right derivative along the
segment.

Machine checked:
- Setting: b(F) lies in R_0, and R_0 is convex and compact. Stage 1 on R_0,
  stage 2 and the joint problem attain their maxima.
- Part 1: S = Qbar - nu'b - (gamma/2) b*'Sigma_f b*, which is also the score at
  the target-implied premia less a constant. If nu = 0, every stage-2
  maximizer is a joint maximizer.
- Part 2, stated for any holding set (no convexity):
  - 0 <= Lambda_s <= nu'Delta e, with equality iff w_J maximizes S;
  - Lambda_s <= |nu| |Delta e| in the Euclidean norm, and Lambda_s = 0 when
    Delta e = 0;
  - for any convex R containing b(F) on which b* maximizes G,
    nu'Delta e <= nu'(b* - b_2), and Lambda_s = 0 when b_2 = b*.
- Part 3:
  - the directional derivatives exist, S'(w_2; Delta w) <= 0, and k >= 0;
  - k = 0 when (w_2 - w^-)_i (w_J - w^-)_i >= 0 for every i;
  - Lambda_s = nu'Delta e - (gamma/2) Delta w' Sigma (Delta w) - s with
    s = -S'(w_2; Delta w) + k, hence the inequality.
- Part 4: T_s >= Qbar(w_T) - nu'(b* - b_2) for any w_T in F with exposure b*,
  hence the bound relative to the fibre-confined loss (vacuous for an empty
  fibre).
- Part 5: nu = lambda_bar - lambda_hat. nu is in the normal cone of every
  convex R at a maximizer b* of G, and nu = 0 when b* is interior.

Not formalized: the KKT reading of -S' as binding multipliers (the proof
does not need it), and the face-normal reading in part 5 beyond the
normal-cone statement. Lean's two part-3 sign notes were fixed before
approval, and this is the corrected statement. PM's limit stands: nothing
is claimed about the ordering of the soft and fibre-confined procedures.

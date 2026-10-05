---
id: 27
title: "The two-stage factor-then-manager procedure in M2: its loss is the residual value function's gain from moving the exposure less the factor objective's loss, separation is exact iff the factor optimum also maximizes the factor objective plus that value (zero in the residual value's superdifferential when it is concave), and funded long-only trading makes that value not flat"
status: formalized
model_version: M2
depends_on: [4, 5]
axioms_used: []
formal: lean/Standalone/M2TwoStageSeparation.lean
direction: D4
---
## Statement

D4's first task (PM's note; proposal section 4 Direction C): state the two-stage
procedure, the information each stage uses and the comparator, and say whether
funded long-only ETF constraints break separation beyond the kill benchmark
before any proof. This claim does that in M2 and proves the loss identity,
the exact-separation criterion and a loss bound; it imports no literature
theorem. The kill benchmark and the separation theorems
(`treynor1973security`, `tobin1958liquidity`, `cass1970structure`,
`merton1972analytic`) are now at full text; Prior art compares against
them by page and equation. No step of the proof rests on any of them, so
the claim is not provisional under rule 8.

**Setting.** Any M2 instance: one active fund, n in {1,2} ETFs, two factors,
belief means lambda_bar (factor premia) and alpha_bar, the factor shock
covariance Sigma_f = sum_s q_s z^f_s (z^f_s)' (2-by-2, positive semidefinite),
gamma>=0, the funded class F, exposure b(w)=(B^A)'a+(B^E)'p, and the
implemented criterion Qbar_0. Write r_res(w)=a z^A+p'z^E for the residual
shock of a holding, and for the cross and residual second moments
C(w)=sum_s q_s z^f_s r_res,s(w) (a 2-vector) and R(w)=sum_s q_s r_res,s(w)^2.

**The exact split.** For every w,

```
Qbar_0(w) = G(b(w)) + H(w),
G(b)   = b'lambda_bar - (gamma/2) b'Sigma_f b,
H(w)   = a alpha_bar - p'c^E - (gamma/2)[2 b(w)'C(w) + R(w)] - tau(w-w^-),
```

G the *factor objective* (depends on w only through its exposure) and H the
*residual objective* (alpha, drag, cross and residual risk, switching
costs). The *funded feasible exposure set* is B_F=b(F), a nonempty compact
convex set (claim 004's compactness under the linear map b; claim 005
describes the ETF-only slice B_E). For b in B_F the *residual value
function* is

```
V(b) = max { H(w) : w in F, b(w)=b },
```

attained. G+V is concave on B_F, as the fibre maximum of the concave
Qbar_0; V itself is concave when the cross moments vanish on F (C(w)=0 for
all w in F, as when ETF and active residuals are uncorrelated with the
factor shocks, which holds in experiment 006's calibration) and not in
general (lean's counterexample, Not shown). The joint optimum under
identical forecasts is J=max_F Qbar_0=max_{b in B_F}[G(b)+V(b)] (claim
004), the comparator.

**The two-stage procedure.**
- *Stage 1 (factor allocation).* Information: lambda_bar, Sigma_f, gamma and
  the exposure set it is told to respect; not alpha_bar, drag, residual or
  cross risk, costs, or the incumbent's fund composition. Two variants: the
  *unconstrained target* b_TB=argmax_{R^2} G, equal to Sigma_f^{-1}
  lambda_bar/gamma when Sigma_f is positive definite and gamma>0 (the passive
  mean-variance target, the kill benchmark's factor stage), and the
  *feasibility-aware target* b*=argmax_{B_F} G (the benchmark plus the
  feasibility check). The unconstrained variant is implementable only when
  b_TB is in B_F, and then b*=b_TB.
- *Stage 2 (manager and ETF selection).* Information: everything in the
  instance. It chooses w in F with b(w)=b* maximizing H, attaining V(b*).
- *Two-stage value* T=G(b*)+V(b*); *loss* Lambda=J-T>=0.

1. **Loss identity.** For any joint maximizer w_J with exposure b_J=b(w_J),

   ```
   Lambda = [V(b_J)-V(b*)] - [G(b*)-G(b_J)],
   ```

   the residual value's gain from moving the exposure from the factor
   optimum to the joint one, less the factor objective's loss from the same
   move; both brackets are nonnegative, the second by optimality of b*.

2. **Exact separation.** T=J if and only if b* maximizes G+V on B_F, that
   is, iff 0 belongs to the superdifferential of the concave function G+V
   at b* (relative to B_F). In particular T=J whenever V is constant on
   B_F, and T=J whenever 0 is a supergradient of V at b* (V(b)<=V(b*) for
   all b in B_F), for any V. Conversely, when V is concave on B_F (as when
   C(w)=0 on F), Sigma_f is positive definite, gamma>0 and b* is in the
   relative interior of B_F (interior within the affine hull aff B_F, which
   is a segment's line in G1-exact with one ETF and the plane with two
   independent loadings), T=J if and only if 0 belongs to the
   superdifferential at b* of V restricted to aff B_F (V is flat at the
   factor optimum along B_F in the sense of concave functions), since then
   the gradient of G along aff B_F vanishes at b* and the superdifferential
   of G+V along aff B_F is that gradient plus that of V. Without concavity
   of V the "only if" fails (Not shown).

3. **Loss bound.** If Sigma_f is positive definite and gamma>0,

   ```
   Lambda <= V(b_J)-V(b*) - (gamma/2)||b_J-b*||^2_{Sigma_f},
   ```

   and if V is L-Lipschitz on B_F in the norm ||b||_{Sigma_f}=sqrt(b'Sigma_f b),

   ```
   Lambda <= min( L^2/(2 gamma), L ||b_J-b*||_{Sigma_f} ).
   ```

   The loss is controlled by the exposure mismatch in the factor-risk metric
   and by the regularity of the residual value function, which is what
   proposal section 4C asks a loss bound to depend on.

4. **When V is flat, and what funded long-only trading does to it.** V is
   constant on B_F when the residual problem does not see the exposure: the
   ETFs are residual-free (z^E=0), drag-free and costless, the cross moments
   vanish (C(w)=0), and for every b in B_F the fibre {w in F: b(w)=b}
   contains a holding with the active position a_H that maximizes
   a alpha_bar-(gamma/2)a^2 R_A-tau_A(a-a^-) over [0,bar a], R_A the active
   residual variance. Then V(b)=max of that function, T=J, and the
   procedure recovers the joint optimum: this is the kill benchmark's
   world, and its funded version needs only the feasibility check b_TB in
   B_F. Funded long-only trading breaks the last condition in three ways
   that a feasibility check does not see, each making V depend on b:
   (a) *manager-borne exposure*: the active fund's own loading (B^A)' puts
   a inside b, so the fibre bounds a by the exposure target
   (0<=a<=min over reachable decompositions), and when (B^A)' is outside the
   ETF span L_E (claim 005's missing direction) the fibre fixes a exactly,
   so stage 1 chooses the manager; (b) *shared budget*: implementing an
   exposure through ETF purchases consumes the cash that funds the active
   position, so when cash binds V falls with the exposure's cash cost;
   (c) *directional ETF costs and drag*: V has a kink at the incumbent's
   exposure and slopes against exposure changes. Hence separation fails
   beyond the feasibility check exactly when one of these makes V non-flat
   at b*.

5. **Calibrated instances** (numerical, `checks/027/check.py`, experiment
   006's M2 cells, floating solves). On the three geometries with zero and
   5 bp costs, gamma=5 and start S1, the unconstrained target is infeasible
   in every cell (the long-only ETF menu cannot reach its value-tilt ratio
   without shorting), the identity and the bound hold, and the loss is: at
   most 0.08 bp per quarter at zero alpha; 0.4 to 2.9 bp at alpha +25 and
   +50 bp, where the target caps the active holding; and 2.4 to 22.4 bp at
   alpha -25 and -50 bp in the missing-direction and infeasible geometries,
   where the exposure target forces holding a fund the joint optimum sells.
   In a pure-factor, costless, residual-free, slack-funded cell with a 1 bp
   alpha the loss is zero and the unconstrained target feasible; raising
   alpha to 25 bp in the same cell makes the target bind the active holding
   and the loss 0.17 bp.

**One sentence without model nouns** (the roadmap's first-task question).
A shared funding budget with no shorting breaks the separation of exposure
choice from residual choice beyond a feasibility check, because implementing
an exposure spends the budget the residual position needs and, when an
exposure direction is reachable only through the residual instrument,
dictates that position, so the residual value is not flat at the exposure
optimum; the loss is exactly the residual value's gain from moving the
exposure less the exposure objective's loss, and is at most the squared
regularity of the residual value over twice the exposure curvature.

## Proof

### 0. The split, the exposure set and the value function

For a holding w the risky return is r=B f+(alpha,-c^E)+r_res with
f=lambda_bar+z^f in the belief-mean score, so w'Sigma w = sum_s q_s
(b(w)'z^f_s+r_res,s(w))^2 = b'Sigma_f b+2 b'C(w)+R(w), and Qbar_0 splits as
displayed. F is nonempty, convex and compact (claim 004), and b is linear,
so B_F=b(F) is nonempty, convex and compact. For b in B_F the fibre is a
nonempty compact set and H is continuous, so V(b) is attained. Qbar_0 is
concave in w (claim 004: affine terms, minus the convex quadratic w'Sigma w,
minus a convex cost) and the set {(w,b): w in F, b=b(w)} is convex, so the
fibre maximum b -> max{Qbar_0(w): w in F, b(w)=b} = G(b)+V(b), a partial
maximization of a jointly concave function over a convex set, is concave
on B_F (for b,b' in B_F with fibre maximizers w,w', the point (1-t)w+tw'
lies in the fibre of (1-t)b+tb' and Qbar_0 there is at least
(1-t)Qbar_0(w)+tQbar_0(w')). H=Qbar_0-G(b(.)) is a difference of two
concave functions of w and is not concave in general, since its quadratic
part -(gamma/2)[2b(w)'C(w)+R(w)] is the difference of the convex forms
E[(b'z^f+r_res)^2] and E[(b'z^f)^2]; when C(w)=0 on F it is
-(gamma/2)R(w), so H is concave and the same partial-maximization argument
makes V concave. J=max_F Qbar_0 is attained (claim 004) and equals
max_{B_F}[G+V] by maximizing first over each fibre.

### 1. The identity

J=G(b_J)+V(b_J) because w_J maximizes H on its own fibre (any better point of
that fibre would beat w_J on Qbar_0). Subtracting T=G(b*)+V(b*) gives the
identity. G(b*)>=G(b_J) since b_J is in B_F and b* maximizes G there;
V(b_J)-V(b*)>=G(b*)-G(b_J)>=0 then follows from Lambda>=0.

### 2. Exact separation

T=J iff G(b*)+V(b*)=max_{B_F}(G+V), which is the first statement; since
G+V is concave on the convex B_F (part 0), b* maximizes it iff 0 is in its
superdifferential at b* relative to B_F. If V is constant, G+V and G have
the same maximizers. If 0 is a supergradient of V at b*, then V(b)<=V(b*)
and G(b)<=G(b*) for every b in B_F, so b* maximizes G+V; this uses no
concavity. For the converse under concavity of V, work in the affine hull
A=aff B_F with direction space D (D=R^2 with two independent loadings; a
line when B_F is a segment, as in G1-exact with one ETF), and read G, V
and superdifferentials as functions on A, supergradients taken in D: if
Sigma_f is positive definite, gamma>0 and b* is in the relative interior
of B_F, G is strictly concave and differentiable on A with gradient
grad_D G(b*)=0 (the projection of grad G(b*) onto D, zero by optimality of
b* on B_F at a relatively interior point), and the superdifferential of
G+V at a relatively interior point where G is differentiable is
grad_D G(b*)+partial V(b*) (the sum rule for a differentiable concave
function and a concave function, elementary here: a supergradient g in D
of G+V at b* satisfies V(b)-V(b*)<=g'(b-b*)-[G(b)-G(b*)]; along b=b*+t d
with d in D, dividing by t>0 and letting t->0 gives
V'(b*;d)<=(g-grad_D G(b*))'d for every direction d in D, so
g-grad_D G(b*) is a supergradient of the concave V on A; the reverse
inclusion is the sum of the two supergradient inequalities). Hence T=J iff
0 is in partial V(b*), the superdifferential of V restricted to A. When
V is not concave the "only if" fails: G+V can be maximized at a relatively
interior b* while V is strictly minimized there (lean's instance in Not
shown).

### 3. The bound

For positive definite Sigma_f and gamma>0, G is gamma Sigma_f-strongly
concave, so optimality of b* on the convex B_F gives, as in claim 018's
quadratic-gap argument, G(b*)-G(b_J)>=(gamma/2)||b_J-b*||^2_{Sigma_f}.
Substituting into the identity gives the first bound. With
V(b_J)-V(b*)<=L||b_J-b*||_{Sigma_f}, the right side is at most
L x-(gamma/2)x^2 with x=||b_J-b*||_{Sigma_f}, whose maximum over x>=0 is
L^2/(2 gamma); and it is at most L x directly.

### 4. Flatness and its funded failures

Under the stated conditions H(w)=a alpha_bar-(gamma/2)a^2 R_A-tau_A(a-a^-)
depends on a alone, so V(b) is its maximum over the a-values present in the
fibre of b; if every fibre contains a_H, V is constant. Each failure mode is
a statement about the fibre: (a) b(w)=(B^A)'a+(B^E)'p, so a enters the
exposure; if (B^A)' is outside L_E the component of b outside L_E is
(B^A)'_perp a and determines a (claim 005's missing direction), and
otherwise the nonnegativity of p bounds a by the largest a with b-(B^A)'a in
(B^E)'R^n_+ intersected with the box and cash constraints; (b) the cash
constraint k(w)>=0 couples the ETF dollars that implement b with the active
dollars a through one budget, so the fibre's admissible a shrinks as the
exposure's cash cost grows once k binds; (c) tau and c^E enter H through p,
which the fibre ties to b. In each case V varies with b, and part 2 gives
the criterion.

### 5. The numerical statement

The check solves the joint problem and both stages as convex programs in
w and reports the quantities of parts 1, 3 and 4 per cell.

## Checks

`checks/027/check.py` (exits non-zero on failure; a check, not a proof).
Experiment 006's calibration (French factor means and shock sizes, assumed
active residual 1 percent, ETF residual 0.2 percent, drag 1 bp, caps 1,
start S1, gamma 5), geometries G1-exact, G2-missing and G3-infeasible, costs
zero and 5 bp, alpha from -50 to +50 bp: it checks the identity, the bound,
nonnegativity, the feasibility of the unconstrained target, and the exact-
separation and binding-target cells described in part 5.

## Not shown

- The procedure is defined in M2 with belief means; no statement is made
  for M3 or for estimated inputs (experiment 006 Part M's estimated premia
  are not used here).
- The Lipschitz constant L is not computed in general; V is finite on B_F
  but its regularity up to the boundary is not established, and part 3's
  second bound is conditional on L.
- V is not concave in general, and the first filing said it was (lean's
  note of 2026-09-28, corrected here). Lean's instance: independent factor
  shocks of size 1/10 (Sigma_f=I/100), gamma=100, ETF 1 loading (1,0) with
  residual -f_1/2 and drag 3/16, ETF 2 loading (0,1) residual-free, an
  active fund with zero loadings and alpha=-1/100; then
  2b'C+R=-(3/4)p_1^2/100, H=a alpha-(3/16)p_1+(3/8)p_1^2 and
  V(b)=-(3/16)b_1+(3/8)b_1^2, convex in b_1. With lambda_bar=(1/4,1/4),
  b*=(1/4,1/4) is interior, G+V is maximized there (T=J), and V has a
  strict minimum in b_1 at b*, so 0 is not a supergradient of V: part 2's
  "only if" needs V concave, which is why it is stated for G+V in general
  and for V under C(w)=0 on F. Part 1, part 3 and part 4's flat case (which
  assumes C(w)=0) do not use concavity of V. Experiment 020 (analyst,
  reported) exhibits the failure at calibrated scale: midpoint concavity of
  V on a 21 x 21 exposure grid holds in all 54 cells without cross moments
  and fails in 7 to 45 of 54 cells once residuals correlate with the
  factor shocks (active-HML correlations of 0.2 to 0.4, or market
  correlations of 0.2 on both residuals), with a worst violation of
  0.02 bp; these are exhibited violations, and concavity where they are
  absent is not proven. Under the same cross moments the two-stage gap
  moves by a median of 0 bp and by at most 6.1 bp in single cells, and the
  joint optimum sits on a long-only or cap bound in 85 of the 94 cells
  with a gap of at least 1 bp. No simple observable rule predicts exact
  separation: the best, "alpha at least 25 bp or gamma at least 5", is
  right in 77 percent of experiment 018's cells against a 69 percent base
  rate.
- Part 4's sufficient condition for a flat V is one set of conditions, not a
  characterization; part 2 is the characterization.
- The four separation sources are read at full text (librarian,
  2026-09-28) and Prior art cites them by page and equation; the first
  filing's title-level reading of Treynor-Black, that the benchmark assumes
  the active portfolio carries no index exposure, was wrong (the benchmark
  nets that exposure with an explicit market position free in sign,
  equation (16)) and is corrected in Prior art. Nothing in the proof rests
  on them. Tobin's text is the Cowles discussion-paper version, cited by
  its section.
- Part 5 is numerical on solver optimizers of one calibration and two cost
  schedules. Experiment 018 (analyst, reported; red's required correction
  of 2026-09-28 applied here) does not measure this claim's procedure: its
  2S-alpha is the soft-target procedure, stage 2 penalizing the distance
  from b* rather than confined to its fibre, which is claim 028's. Its
  figures (exactly zero loss in 254 of 720 cells, below 1 bp per quarter in
  496, up to 9.2 bp) are claim 028's loss, bounded by nu'(b_J - b_2S) with
  nu = lambda_bar - gamma Sigma_f b* stage 1's multiplier and b_2S the soft
  solution's exposure (018's L_term); the term (lambda_bar - gamma Sigma_f
  b*)'(b_J - b*), which the first filing named here, is at most 0 by
  optimality of b* and carries no positive gap. This claim's own
  calibrated statement is experiment 018's Deviation 1 (analyst, exact
  rationals on the 180 zero-rate cells, where b(F) = conv{0, loading rows}
  is 018's target set; cost-bearing cells are not computed, since there
  b(F) is smaller): the fibre-confined loss is exactly 0 in 44 of 180
  cells, below 1 bp per quarter in 114, at least 1 bp in 66, median
  0.20 bp and maximum 42.0 bp; the identity of part 1 holds exactly in
  every cell (residual-stage gain median 0.47 bp, maximum 53.0; factor-stage
  cost median 0.23 bp, maximum 23.6; mismatch in the factor-risk norm at
  most 0.018); the unconstrained target lies outside b(F) in all 180. The
  large losses are at negative alpha (maxima 42.0 bp at -50 bp and 17.0 at
  -25 bp, against at most 2.9 bp at nonnegative alpha and 0.16 bp at zero
  alpha): at gamma 2 the target is the active fund's own loading, and in
  G2-missing and G3-infeasible the fibre then fixes the active holding at
  its cap, so stage 1 chooses the manager, part 4(a); in G1-exact an ETF
  carries that loading, the fibre does not force the manager, and the
  maximum is 2.9 bp. The soft-target loss on the same cells has maximum
  8.2 bp, and the two order both ways (worse in 96 cells, better in 60,
  equal in 24), as claim 028's check also shows. Part 5's check prints the
  same procedure in floating point on a subgrid including cost-bearing
  cells. Experiment 018's reading in which an unconstrained target is
  handed to a stage 2 that re-optimizes alpha and drag reproduces the
  joint problem by construction (gap 0 in all 720 cells), which is why
  this claim confines stage 2 to the fibre of the target.
- The one-sentence answer is a reading of parts 1-4; whether it is
  "something structural left over" in the kill criterion's sense is PM's.

## Prior art

Mechanism: A criterion that is a strongly concave function of a linear
image of the decision plus a residual term separates into a two-stage
choice, image first and residual second, with loss equal to the residual
value function's gain from moving the image less the image objective's
loss, so separation is exact iff the residual value is flat at the image
optimum; a shared budget with no shorting makes it non-flat.

General results checked, at full text. The kill benchmark
`treynor1973security` (Treynor and Black 1973): its model is "an idealized
world in which there are no restrictions on borrowing, or on selling
securities short", with equal lending and borrowing rates (p. 67); under
Sharpe's Diagonal Model the residuals are uncorrelated with each other and
with the market, equation (2) (p. 70); the market asset makes any market
exposure available "approximately independently" of the specific
positions, equation (5) (p. 71); the optimal specific positions are
appraisal premium over residual variance, equation (13) (p. 71-72),
unaffected by risk attitude or market expectations (equation (10), p. 72);
and the explicit market position is the optimal market exposure less the
by-product exposure accumulated through the specific positions, "which
may, of course, be negative, requiring an explicit position in the market
that is short", equation (16) (p. 72), the whole being the unconstrained
Markowitz solution, equation (17) (p. 73-74). In the terms above, equation
(13) is stage 2's residual choice, equation (16) is the exposure fibre's
ETF position, and V is flat because the explicit market position, free in
sign and size, nets whatever exposure the residual choice carries at no
cost: that is part 4's flat case, whose hypothesis C(w) = 0 is equation
(2). The benchmark's factor stage is this claim's unconstrained target
b_TB: equation (10) applied to the market asset as the (n+1)th
"independent security" (p. 71-72) gives the total optimal market
exposure, by-product included, as the market premium over the market
variance times the multiplier lambda, which the third stage sets from
risk attitude (lambda = 1/gamma for a mean-variance investor), that is,
lambda_bar/(gamma Sigma_f) in one factor and Sigma_f^{-1} lambda_bar/gamma
in the two-factor M2, and equation (16) implements it net of the
by-product; PM's check (note of 2026-09-28) is confirmed. The three
funded failures are the benchmark's assumptions removed
one at a time: (a) manager-borne exposure is the loss of the free-sign
netting position of equation (16) (no shorting, and in the missing
direction no ETF at all), not an assumption that the active portfolio
carries no index exposure, which the benchmark does not make; (b) the
shared budget is the loss of the unrestricted borrowing of p. 67, the
benchmark's third stage "scaling positions in the combined portfolio up
or down through lending or borrowing" (p. 74); (c) costs and drag are the
frictions p. 67 excludes. The benchmark's order is active portfolio first,
market blend second, leverage third (p. 74), the reverse of D4's
factor-first procedure; in the unconstrained world both orders give
equation (17), and this claim's factor-first order is the one proposal
section 4C asks about. Two-fund separation: `merton1972analytic` (Merton
1972), Theorem I (p. 1857; two mutual funds span the mean-variance
efficient set, under Section II's frontier problem whose only constraint
is the budget identity, equation (1), p. 1851-1852) and Theorem II
(p. 1864-1865; with a riskless asset the two funds can be taken as the
riskless asset and one risky fund); `tobin1958liquidity` (Tobin 1958),
section 3.6, the "proportionate composition of the non-cash assets is
independent of their aggregate share of the investment balance"
(discussion-paper p. 36); `cass1970structure` (Cass and Stiglitz 1970),
monetary separation defined on p. 126-127 (one of the two funds is money)
with Theorem 3.1 (p. 128) and Theorem 6.1 (p. 142) giving the preference
conditions for it. In the terms above the two funds are the riskless
position and the factor-optimal exposure, and the theorems are the flat-V
case of part 4. Merton and Cass-Stiglitz take an unrestricted riskless
position (Merton's frontier problem has no sign constraint, footnote 3
allows borrowing and short sales, and Theorem II's riskless fund is held
in any amount; Cass-Stiglitz footnote 4 permits short sales), which the
funded class F removes, so for them the hypothesis that fails in M2 is the
unrestricted riskless position, part 4(b). Tobin's section 3.6 is already
funded, long-only and lending-only ("All x_i are non-negative, and
sum x_i = A <= 1", scan p. 42), and his separation holds while cash is
positive; so for Tobin the funded budget breaks separation only at the
budget corner, which sharpens part 4(b): the failure is where cash binds,
not from the absence of borrowing as such (red's reading, 2026-09-28,
adopted). No claim is made that the funded class satisfies Cass and
Stiglitz's preference conditions, which concern utility, not the
constraint set; parametric
optimization and value-function
concavity under partial maximization (elementary, proved in part 0);
`platanakis2019horses` Proposition 1, which compares estimators within each
stage of a fixed two-stage procedure and does not compare the procedure with
the joint optimum, which is this claim's comparator; `pastor2002investing`,
which studies the joint problem only; claims 004 (compactness and
attainment), 005 (the missing-direction and infeasible-match geometry that
part 4(a) uses), 009 (the no-active-trade band, the residual stage's active
kink) and 018 (the strong-concavity gap used in part 3); experiment 006
(the calibrated cells).

Searched: claims 004-009, the D4 roadmap entry and its prior-art line, the
librarian's D4 sweeps (FINDINGS, 2026-09-27 and 2026-09-28, the latter
registering the four sources and naming the constrained-portfolio pattern
of `liu2013portfolio`, `dai2011illiquidity` and `bichuch2014investing` as
the working hypothesis; part 4 is that pattern's instance for separation),
proposal section 4C, and the refuted directory. This is still a claim because D4's first task needed the
procedure, its information and comparator fixed in M2 with a proof of what
its loss is and when it vanishes, which no registered source states for a
funded long-only menu with directional costs; no priority is claimed for
any ingredient.

## Open objections

Lean (2026-09-28, note): V need not be concave (ETF residuals correlated
with factor shocks make H a difference of convex forms), and part 2's
"only if" fails without it. Accepted and fixed above: the criterion is
stated for the concave G+V in general and for V when C(w)=0 on F; lean's
instance is recorded in Not shown; the ledger row is corrected.

Red (2026-09-28, verdict note on the first version c266b11, refuted on
red/review-027 with the same finding as lean's, red's instance being factor
shocks of 5 percent, z^A=-x/2, gamma=5, lambda_bar=(0.00375,0.00375),
alpha=-28.13 bp, loss 0 at the interior b*=(0.3,0.3) where V has a strict
minimum): accepted; the amended claim on this branch is the refile path red
named, and red's Review of the amended claim will record the first
version's refutation. Red's two further points: "interior" is now read
relative to aff B_F in part 2 and its proof (B_F is a segment in G1-exact
with one ETF); the ledger row "Two-stage procedure" is edited in place on
this branch, and a simulated merge into main (git merge-tree, 2026-09-28)
yields one row with that key, so the duplicate-key check passes on the
merge result.

Red (2026-09-28, D4 sources at full text): three corrections, all
adopted in Prior art: Treynor-Black's active positions do carry market
exposure, netted by an explicit, possibly short, index position (equation
(16), p. 72), so failure (a) is that netting position becoming infeasible,
not a failed assumption of the benchmark; Tobin's separation is funded,
long-only and lending-only (scan p. 42) and fails at the budget corner,
which sharpens part 4(b); and the sources are no longer cited as wanted.
b_TB as the benchmark's factor stage is confirmed. Red should also test:
the identity when w_J is not unique;
the bound's constant; and part 4's fibre descriptions under binding caps.

## Review

**Red, 2026-09-28.**
- **The first version is refuted.** The first version (c266b11) was refuted by red on red/review-027 (head 9c320e1). Its Setting and part 2 claimed V concave and a superdifferential-of-V criterion. Both fail when residual shocks correlate with factor shocks, which M1/M2 allow. Red's counterexample: factor shocks +-5%, z^A = -x/2, gamma = 5, lambda_bar = (0.00375, 0.00375), alpha = -28.13 bp. Exact solves give loss 0 at the interior b* = b_TB = (0.3, 0.3), where V has a strict minimum. Lean found the same failure independently.
- **This Review covers the amended claim.** The amended text on this branch follows the refile path red named. red/review-027 is withdrawn as a merge request, so the refuted first version does not enter main beside this one.

**The corrected parts, checked by hand.**
- *Part 0.* b -> max{Qbar_0(w) : w in F, b(w) = b} = G + V is a partial maximization of the concave Qbar_0 over the convex graph of b on F, so it is concave. H = Qbar_0 - G(b(.)) has quadratic part -(gamma/2) w'(Sigma - M Sigma_f M')w, which is concave exactly when that matrix is positive semidefinite. When C = 0 on F it is -(gamma/2) R(w), so H and V are concave. The claim now states exactly this.
- *Part 2.*
  - T = J iff b* maximizes the concave G + V on B_F. This needs no condition.
  - "0 is a supergradient of V at b* => T = J" holds for any V, since G is also maximized at b*.
  - *The converse.* For concave V, a relatively interior b*, Sigma_f positive definite and gamma > 0, the projected gradient grad_D G(b*) vanishes by optimality on B_F. The sum-rule argument on A = aff B_F is correct: a supergradient g of G + V gives V'(b*; d) <= (g - grad_D G(b*))'d for every d in D, and concavity turns that into a supergradient inequality for V. So T = J iff 0 is in the superdifferential of V on A. This also settles red's relative-interior point.
  - *Consistency with red's counterexample.* There V is strictly convex, so only the G + V form and the "if" apply, and both give T = J, which is correct.
- *Parts 1, 3 and 4* are unchanged and were checked in red's first review: the identity for any joint maximizer, the strong-concavity bounds, and the flat case under C = 0.
- *The claim's check.* `checks/027/check.py` passes on this branch.
- *ledger/TERMS.md.* The simulated merge with main (git merge-tree) has one "Two-stage procedure" row, and branch CI passes.

**Prior art at full text.** Red's three corrections are adopted and read correctly:
- Treynor-Black's explicit market position is free in sign (eq. 16, p. 72) and nets the by-product exposure, so failure (a) is that position becoming infeasible.
- Tobin's separation is funded, long-only and lending-only (scan p. 42), so 4(b)'s failure is at the budget corner.
- Merton and Cass-Stiglitz are the unrestricted case.

b_TB as the benchmark's factor stage via eq. (10) applied to the market asset is right.

**Required correction (Not shown, not the Statement).** The paragraph on experiment 018 presents 018's figures as the calibrated comparison for this claim's procedure: exactly 0 in 254 cells, below 1 bp in 496, up to 9.2 bp. But experiment 018's 2S-alpha is the *soft-target* procedure, stage 2 penalizing the distance from b* rather than confined to its fibre, which is claim 028's, not this claim's. Its gap is carried by nu'(b_J - b_2S), 018's L_term. The paragraph writes (lambda_bar - gamma Sigma_f b*)'(b_J - b*), which is <= 0 by optimality of b* and cannot carry a positive gap. It should say:
- 018 measures claim 028's soft-target loss, bounded by nu'(b_J - b_2S);
- this claim's fibre-confined loss on those calibrated cells is part 5's (the check prints it, for example 0.384 and 2.308 bp in G3-infeasible EQ5 at alpha +25 and +50);
- the two losses order both ways (claim 028's check).

The statement that 018's stage-1 set conv{0, loading rows} equals B_F at zero costs is correct: with zero costs F = {w >= 0, sum w <= 1}, so b(F) = conv{0, rows}.

**Mechanism (4b).** Partial maximization over the fibres of a linear map; the loss identity as an inequality between attained maxima; a strong-concavity gap. Against the kill benchmark at full text:
- the flat case is Treynor-Black's world: C = 0 is its eq. (2), and a free-sign market position nets the exposure;
- the funded failures are its assumptions removed one at a time.

This is an application with the funded failure modes made explicit. Whether that is "structural leftover" is PM's reading.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Amended after red's refutation (V need not be concave with factor-correlated residuals; red's and lean's counterexample). Red's hand check of the corrected parts is sound: G+V is concave as a partial maximization; T=J iff b* maximizes G+V, needing no condition; zero a supergradient of V suffices for any V; the converse holds for concave V at a relatively interior b* by the sum rule on aff B_F, consistent with red's counterexample. Parts 1, 3, 4 are as checked in red's first review, the check passes, and there is one TERMS row. Mechanism: partial maximization, an inequality between attained maxima, a strong-concavity gap; the flat case is Treynor-Black's world (read at full text) and the funded failures are its assumptions removed one at a time, an application. Limits: the only-if needs concave V; part 5 is floating solves. Required fix to math: Not shown's experiment 018 paragraph attributes the soft-target (claim 028) loss to this fibre-confined procedure.


Not machine checked. Parts 0-3 are finite-dimensional convex analysis on
claim 004's compact classes: a quadratic identity, a partial maximization,
an inequality between attained maxima and the strong-concavity gap of claim
018; part 4 is a description of fibres; part 5 is numerical.

Lean, 2026-09-28 (final): parts 0-4 are machine checked as amended. Part 5
is numerical (floating solves) and has no formal counterpart. The statement
is in `lean/Standalone/M2TwoStageSeparation.lean` and the proof in
`lean/Novel/M2TwoStageSeparationProof.lean`. `lake build` and the axiom
audit pass (standard axioms only). No hypothesis structure or cited result
is used. The proof imports claim 004's proof module (Q-04) and re-derives
claim 003's belief-average identity locally. The counts are general
(m active funds, n ETFs, K factors).

Machine checked:
0. The exact split, for the score and for Qbar_0 at the belief mean.
   - B_F is nonempty, convex and compact; V is attained on every fibre.
   - G + V is concave, and V is concave when C(w) = 0 on F.
   - J = G(b_J) + V(b_J) = max over B_F of G + V.
   - Stage 1's maximizer exists, and b_TB is the unique maximizer on B_F when
     it lies there (Sigma_f positive definite, gamma > 0).
1. The loss identity, with both brackets and Lambda nonnegative.
2. Exact separation.
   - T = J iff b* maximizes G + V on B_F, equivalently iff 0 is a
     supergradient of G + V relative to B_F.
   - T = J when V is constant, and when 0 is a supergradient of V at b*, for
     any V.
   - At a b* in the relative interior of B_F (Mathlib's `intrinsicInterior`),
     grad G(b*)'(b - b*) = 0 on B_F. If V is also concave (Sigma_f positive
     definite, gamma > 0), T = J iff V <= V(b*) on B_F.
   - At an interior b*, gamma Sigma_f b* = lambda.
3. Both loss bounds. They need no positive definiteness.
4. The flat case: V is constant and T = J. With one active fund whose
   loading is outside the ETF span, the exposure fixes the active position.
   Failure modes (b) and (c) are qualitative and are not formalized.

PM's limits stand: the "only if" needs concave V (red's and lean's
counterexample shows it fails otherwise), and part 5 is floating solves.

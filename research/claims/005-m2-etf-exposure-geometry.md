---
id: 005
title: "ETF-only exposure geometry under M2's funded directional costs"
status: formalized
model_version: M2
depends_on: [004]
axioms_used: []
formal: lean/Standalone/M2EtfExposureGeometry.lean
direction: D1
---
## Statement

Fix any M2 instance, including its initially compliant nonnegative holdings and cash,
one active fund, n in {1, 2} ETFs, two factors, fixed loadings, limits at most one and
purchase and sale rates in [0, 1). All action classes use M2's identical funding equation.
No bound is required to bind. This result concerns exposure feasibility, independently of
the specified means, signed ETF drag, scenario covariance, belief and risk coefficient.

Write bar p for the ETF coordinates of bar w and kappa^+_{E,j}, kappa^-_{E,j} for their
purchase and sale rates. For an ETF trade d in R^n define its net cash outlay

```
Psi_E(d) = sum_j [d_j + kappa^+_{E,j} max(d_j, 0)
                         + kappa^-_{E,j} max(-d_j, 0)],
P_E = {d : -p^-_j <= d_j <= bar p_j - p^-_j for every j,
           Psi_E(d) <= k^-}.
```

Psi_E can be negative when sales raise cash. Let sigma range over the 2^n choices that
assign either purchase or sale to each ETF, and set c_{sigma,j} equal to
`1 + kappa^+_{E,j}` for purchase and `1 - kappa^-_{E,j}` for sale. Then

```
Psi_E(d) = max_sigma c_sigma' d,
P_E = {d : -p^- <= d <= bar p - p^-, c_sigma' d <= k^- for every sigma},
E = {(a^-, p^- + d) : d in P_E},
D_E = {(B^E)' d : d in P_E},
B_E = b(w^-) + D_E.
```

P_E, D_E and B_E are nonempty, closed, bounded and convex. In particular 0 belongs to
P_E and D_E, and b(w^-) belongs to B_E. Moreover D_E is a subset of L_E. Neither D_E nor
B_E is asserted to be a linear space or to contain a neighborhood of its incumbent.

For any target exposure change delta in R^2, an ETF-only action matches that change if
and only if the following finite system has a solution d:

```
(B^E)' d = delta,
-p^- <= d <= bar p - p^-,
c_sigma' d <= k^- for every sigma.
```

If delta is outside L_E, the linear equation alone is impossible: this is a missing
direction. If delta belongs to L_E but has no solution satisfying the position bounds,
those bounds obstruct matching. If the equation has a solution within the bounds but
none of those solutions satisfies the cash inequalities, funding obstructs matching.
In the latter case the bounds may contribute to the obstruction; the classification
does not say that funding is the only restriction that matters. It tests all solutions,
not a chosen solution of the linear equation.

Two specializations make this test explicit:

* For n = 1, P_E is the closed interval
  `[-p^-, min(bar p - p^-, k^-/(1 + kappa^+_E))]`.
  Its image D_E is that interval times the ETF loading vector, including the zero-loading
  case where the image is {0}.
* For n = 2 with invertible (B^E)', L_E = R^2 and the only possible trade for delta is
  `d = ((B^E)')^(-1) delta`. It is a feasible match exactly when it satisfies the displayed
  position and cash inequalities. Full span alone gives no feasibility conclusion.

Finally, for any full action w = (a, p) in F with a != a^-, its exposure change is outside
L_E if and only if the active loading vector (B^A)' is outside L_E. If a = a^-, w itself
is an ETF-only match. For a != a^- and (B^A)' in L_E, feasibility still requires the
finite system above with delta = b(w) - b(w^-).

## Proof

For one ETF put A = 1 + kappa^+_E and H = 1 - kappa^-_E. Then A >= H > 0. If d >= 0,
the instrument's net outlay is A d and A d >= H d. If d < 0, its net outlay is H d and
H d >= A d. Thus its net outlay is max(A d, H d), including d = 0. For any selection of
one term per ETF, the sum is at most the sum of the individual maxima. Choosing a term
attaining each individual maximum attains that upper bound. Therefore the sum of the
individual maxima equals max_sigma c_sigma' d. Comparing the maximum to k^- proves
the finite cash-inequality representation of P_E.

An ETF-only action fixes a = a^-, so the active trade and its cost are zero. Substituting
w = (a^-, p^- + d) into M2's cash equation gives k(w) = k^- - Psi_E(d). Its active
position bounds already hold by initial compliance, and its ETF bounds are exactly
-p^- <= d <= bar p - p^-. This proves the asserted equality for E in both directions.
Linearity of the fixed exposure map gives

```
b(a^-, p^- + d) - b(w^-) = (B^E)' d.
```

Taking the images of all and only the feasible trades proves both exposure-set formulas.
The definition of L_E is the image of all of R^n under (B^E)', so it contains D_E.

Initial compliance and k^- >= 0 show that d = 0 belongs to P_E. The representation as
coordinate bounds and finitely many linear inequalities proves convexity: each inequality
is preserved under t d + (1-t) e for 0 <= t <= 1. Taking coordinate limits preserves the
same inequalities, proving closedness. Also -1 <= d_j <= 1 for each coordinate, because
both initial holdings and limits lie in [0, 1], so P_E is bounded. Linear images and
translation preserve convex combinations, proving convexity of D_E and B_E. Each coordinate
of (B^E)' d has absolute value at most sum_j |B^E_{j,k}|, proving boundedness of D_E;
adding the fixed b(w^-) proves boundedness of B_E. The zero trade proves the stated
nonemptiness and incumbent membership.

Closedness of an image requires an additional argument; it does not follow merely from
closedness of its domain. Let y_l be a convergent sequence in D_E with limit y, and choose
d_l in P_E with (B^E)' d_l = y_l. There is a convergent subsequence of d_l in [-1, 1]^n:
bisect every coordinate interval of this box, retain a closed child box containing infinitely
many sequence indices, and repeat. Choose strictly increasing indices from these nested
boxes. In each coordinate the supremum of their increasing lower endpoints lies in every
selected interval; their lengths tend to zero. The chosen subsequence therefore converges
coordinatewise to the vector d_* of these suprema. This is the same finite-box construction
used in claim 004, applied to trade coordinates. Closedness of P_E gives d_* in P_E.
Passing to the limit in each finite linear sum gives (B^E)' d_* = y, so y belongs to D_E.
Thus D_E is closed. For any convergent sequence in B_E, subtracting b(w^-) gives a
convergent sequence in D_E; adding b(w^-) back proves closedness of B_E.

The matching criterion now follows directly from the proven formula for D_E and the
inequality representation of P_E. By definition delta belongs to L_E exactly when the
linear equation has a real solution. Among such solutions, either none obeys the bounds,
or at least one does. In the second case matching is feasible exactly when at least one
bounded solution also obeys every cash inequality. This proves the obstruction statements
without selecting an arbitrary representative when the linear equation has multiple solutions.

For n = 1, the lower bound -p^- is nonpositive and the upper bound bar p - p^- is
nonnegative by initial compliance. Every d between -p^- and zero has net outlay
(1 - kappa^-_E)d <= 0 <= k^-, so its funding condition holds. Every d >= 0 has net outlay
(1 + kappa^+_E)d, so its funding condition is equivalent to
d <= k^-/(1 + kappa^+_E); the divisor is positive. Intersecting with the upper position
bound gives precisely the interval in the statement. Applying the established linear image
formula proves the description of D_E, including a zero loading vector.

For n = 2 and invertible (B^E)', multiplying the matching equation by the inverse shows
that any solution must be d = ((B^E)')^(-1) delta. Conversely multiplication verifies this
is a solution for every delta, so L_E = R^2. Substitution into the already proved criterion
gives necessity and sufficiency of its bounds and cash inequalities.

For the final assertion, finite distributivity gives

```
b(w) - b(w^-) = (a - a^-)(B^A)' + (B^E)'(p - p^-).
```

L_E is a linear space: sums and scalar multiples of ETF loading images are images of the
corresponding sums and scalar multiples of ETF vectors. The second term belongs to L_E.
If (B^A)' belongs to L_E, so does the whole change. Conversely, if the whole change belongs
to L_E and a - a^- is nonzero, subtracting the second term and dividing by a - a^- shows
(B^A)' belongs to L_E. Negating this equivalence proves the missing-direction assertion.
If a = a^-, membership w in F implies w in E by its definition. The remaining case is
exactly the already proved matching test.

## Checks

`uv run python checks/d1-etf-geometry/check.py` passes eight fixed exact-rational cases:
missing direction, a single-ETF match, prohibited shorting, insufficient cash, purchase
costs blocking a match, a binding position cap, sale proceeds funding a purchase, and
redundant ETFs where a different linear solution is feasible. It also compares the finite
cash inequalities with the direct M2 cash formula on a fixed trade grid in each case.
The code was committed before running. Every target comes from a feasible full action;
all assumed inputs extend to M2 with zero means and shocks and gross returns one.
The absence of a match is checked by exact vertex enumeration of the bounded finite
inequality system. These finite checks are not a proof of the general statement. The
examples do not test a strict score advantage or economic materiality.

## Not shown

Exposure matching does not establish equality of residual risk, expected return, switching
costs, cash, terminal wealth or score. No optimized value gap, economic magnitude, empirical
calibration, optimal trade direction or statistical certificate is established. In particular
a feasible full action with an unmatched exposure is not necessarily better than ETF-only
trading. Missing span and infeasible matching remain different obstructions.

The bounds include M2's upper position limits as well as nonnegativity. The full-span result
requires testing all funding costs; it does not authorize borrowing. The n = 1 interval uses
sale rates below one and nonnegative initial cash. No extension to fixed fees, settlement
delays, redemption windows, extra mandates, changing eligibility or another model version is
claimed. This is a one-quarter feasibility result and relaxes no proposal section 2 commitment.

## Prior art

Read board/FINDINGS.md, the refuted-claim registry (empty), the experiment status registry
(no failed or withdrawn entries), M2 and claim 004. The full-text model passages in
`gallien2018hedge` (section 2) and `garleanu2009dynamic` (equations 3-4), previously inspected
for claim 003, provide context only. Neither is used as a mathematical dependency. No
external theorem, numerical premise or new literature search is used here. This finite
linear-inequality and image description is a supporting lemma, not a novelty claim.

## Open objections

None recorded; independent review is pending.

## Review

Red, 2026-09-27. Re-derived independently.

**Independent exact check.** 19,995 random instances in rationals: n in {1, 2}; independent purchase and sale rates in [0, 1) for every instrument, the active fund included; random compliant starts with and without cash; random limits at least the start; random ETF trades d in [-1, 1]^n. On every instance:
(a) the direct net outlay sum_j [d_j + kappa^+_j d_j^+ + kappa^-_j d_j^-] equals max over the 2^n sign patterns of c_sigma' d;
(b) (a^-, p^- + d) lies in F by M2's own cash formula, which includes the active fund's rates, exactly when d lies in P_E. So E = {a^-} x (p^- + P_E), and the active rates correctly drop out;
(c) for n = 1, membership in P_E is exactly -p^- <= d <= min(bar p - p^-, k^-/(1 + kappa^+_E)).
Math's committed `checks/d1-etf-geometry/check.py` also passes all eight fixed cases when run by red; red ran it but did not rely on it.

**Proof read line by line.**
- The per-ETF outlay is max(A d, H d) with A = 1 + kappa^+ >= H = 1 - kappa^- > 0; this is right, and it is where kappa^- < 1 is used. The sum of maxima equals the maximum over sign selections.
- The ETF-only substitution into k(w) is right.
- Convexity and closedness of P_E follow from its finite linear description.
- Closedness of the image D_E is argued properly, by a convergent subsequence in the box rather than by assuming images of closed sets are closed.
- The missing-direction equivalence for a != a^- uses the decomposition b(w) - b(w^-) = (a - a^-)(B^A)' + (B^E)'(p - p^-) and the linearity of L_E, which is red's M1 review point (b), now proved.
- The n = 2 invertible case correctly concludes that full span says nothing about feasibility.

**Attacks tried.**
(i) *Span read as feasibility* (red's FINDINGS case 2, requirement (ii)): the matching criterion tests the position bounds and every cash inequality, over all solutions of the linear equation. FINDINGS case 2 (two spanning ETFs, a match needing a short E1 position) is exactly the "position bounds obstruct" branch.
(ii) *A representative solution chosen arbitrarily*: excluded, since the criterion quantifies over all solutions. The redundant-ETF case in math's check exercises this.
(iii) *Hidden borrowing*: none. P_E carries the funded cash constraint with the actual directional charges, and the sale side credits only (1 - kappa^-) of proceeds.
(iv) *Overlapping obstruction labels*: the Statement says the bounds may contribute when funding is named, so the classification is not presented as exclusive.

**Scope.** This is a feasibility lemma, as the file says: no score, value gap or magnitude. It supplies the "missing direction versus infeasible matching" vocabulary D1 asked for, with a decidable test. The worked examples of incomplete substitution can now cite it.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Whether a target vector is reachable as a linear image of a point in a polyhedron: "missing" means the target lies outside the image's span, and "blocked" means it lies inside the span but outside the polyhedral image.
- *General result.* LP feasibility and the Farkas theorem of alternatives for {d in P : B d = t}, with P polyhedral once each coordinate is split into purchase and sale parts (the 2^n sign regions of the claim).
- *Reduction.* The claim's test enumerates sign regions of a piecewise-linear funding constraint, and each region is a polyhedron. Feasibility in the union is LP feasibility region by region, and the span/polyhedron split is the standard decomposition.
- *Verdict: special case,* applied to M2's funded directional costs. Left over: the explicit region enumeration, a computation.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's exact check on 19,995 instances, line-by-line read (including the closedness-of-image argument) and attacks (span read as feasibility, arbitrary representative solution, hidden borrowing, overlapping obstruction labels) are sound and match PM's rerun of the fixed checks and own exact test of the outlay identity and one-ETF interval; no open objections; limits stated (feasibility lemma only: no score, value gap or magnitude; matched exposure is not matched return, risk or cost).


Not machine checked. The principal target is the finite cash-inequality representation and
the exposure-image/matching identities. Closedness of the exposure image additionally uses
real completeness via the explicit bounded-sequence construction. Neither numerical checks
nor the formalization status of earlier claims imply machine checking of this statement.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2EtfExposureGeometry.lean` and the
proof in `lean/Novel/M2EtfExposureGeometryProof.lean`. `lake build` and the axiom audit pass (standard
axioms only). No hypothesis structure or cited result is used. The statement reuses claim 003's
formal M2 objects and claim 004's `InitialPosition` and `RatesNonneg`.

Definitions. B_E, D_E and L_E are defined as the spec defines them: images of E, and the range of
(B^E)'. The claim's formulas in terms of P_E are proved conclusions, not definitions. A
purchase/sale assignment sigma is a function `Fin n -> Bool`.

Proved, with the hypotheses each part uses:
- (i) Psi_E(d) = max_sigma c_sigma' d, and P_E as the bounds plus the 2^n cash inequalities.
  Needs nonnegative rates only.
- (ii) k(a^-, p^- + d) = k^- - Psi_E(d) for every d, with no hypothesis.
  E = {(a^-, p^- + d) : d in P_E} for a compliant start.
- (iii) D_E = (B^E)' P_E for a compliant start. B_E = b(w^-) + D_E and D_E is a subset of L_E,
  with no hypothesis.
- (iv) P_E is closed and bounded, with no hypothesis. For a compliant start: 0 is in P_E and D_E,
  b(w^-) is in B_E, and D_E and B_E are closed and bounded. With nonnegative rates as well, all
  three are convex.
- (v) Matching holds iff the finite system has a solution, over all solutions. Failing to match
  holds iff one of the following holds: the target is outside L_E; it is in L_E with no solution
  within the bounds; or a solution within the bounds exists but none satisfies the cash
  inequalities. These three cases are disjoint by their definitions, but disjointness is not a
  separate formal conjunct. Red's remark stands: naming funding does not say the bounds play no
  role.
- (vi) For n = 1: the interval formula for P_E, needing kappa^+_E >= 0, kappa^-_E <= 1 and k^- >= 0.
  The image formula for D_E, and D_E = {0} for a zero loading, for a compliant start.
- (vii) For any square invertible ETF loading matrix (n = K, which includes M2's n = K = 2):
  L_E is all of R^n, the unique solution is ((B^E)')^(-1) delta, and matching holds iff that
  solution meets the bounds and every cash inequality.
- (viii) For m = 1 and any holding with a != a^-: the exposure change is in L_E iff (B^A)' is in
  L_E. Also, a holding in F with a = a^- is in E.

Relation to the prose. The claim fixes a whole M2 instance, including the compliant start. So
putting the compliant start on the closedness, boundedness and convexity of D_E and B_E is not
weaker than the prose. Not assumed anywhere: rates below one (the n = 1 interval needs only
kappa^-_E <= 1), limits at most one (each set is bounded by the box [-p^-, bar p - p^-]), and
w in F for (viii). Closedness of D_E uses compactness of P_E in place of the paper's bisection
argument. No gap was found between the formal statement and the prose. The limits PM recorded at
approval apply unchanged: this is a feasibility lemma only.

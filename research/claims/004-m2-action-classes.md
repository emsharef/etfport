---
id: 004
title: "Nested M2 action classes admit optimal one-quarter actions"
status: formalized
model_version: M2
depends_on: [003]
axioms_used: []
formal: lean/Standalone/M2ActionClasses.lean
direction: D1
---
## Statement

Fix any M2 instance. In particular, m = 1 and n in {1, 2}; initial holdings w^- and cash k^-
are nonnegative and sum to one; `0 <= w^-_i <= bar w_i <= 1`; purchase and sale rates satisfy
`0 <= kappa^+_i, kappa^-_i < 1`; gamma >= 0; and the finite scenario and belief masses q and pi
are nonnegative and sum to one. All loadings, means, signed ETF drag and centered shocks are
finite real data as specified by M2, with Sigma = sum_s q_s xi_s xi_s'. The only mandate is the
stated position limits. Every action class uses the same cash function and review cost:

```
tau(v) = sum_i [kappa^+_i max(v_i, 0) + kappa^-_i max(-v_i, 0)],
k(w) = k^- - sum_i (w_i - w^-_i) - tau(w - w^-),
F = {w : 0 <= w_i <= bar w_i for every i, k(w) >= 0},
E = {w in F : a = a^-},
N = {w^-}.
```

Then N is a subset of E, which is a subset of F. Each class is nonempty, closed, bounded and
convex. The M2 objective Qbar_0 is continuous and concave as a function of holdings. On each
of N, E and F it attains a finite maximum, and

```
max_{w in N} Qbar_0(w) <= max_{w in E} Qbar_0(w) <= max_{w in F} Qbar_0(w).
```

Closedness and continuity use the ordinary coordinate topology on finite real vectors.
Convexity of a class means it contains `t w + (1-t) z` whenever it contains w and z and
`0 <= t <= 1`. Concavity of Qbar_0 means
`Qbar_0(t w + (1-t) z) >= t Qbar_0(w) + (1-t) Qbar_0(z)`.
No restriction is required to bind, Sigma may be singular, gamma and cost rates may be zero,
and no interior feasible point, differentiability or strict concavity is assumed.

## Proof

For any real y, `max(y, 0) >= 0` and max(0, 0) = 0, so tau is nonnegative and tau(0) = 0.
At w^- the cash formula gives k(w^-) = k^- >= 0, and the initial position limits hold by
assumption. Thus w^- belongs to F and has a = a^-, so it belongs to E. This proves
N subset E subset F and nonemptiness of all three classes.

For real y, z and t in [0, 1], both y <= max(y, 0) and z <= max(z, 0), and the number
`t max(y, 0) + (1-t) max(z, 0)` is nonnegative. It therefore bounds both
`t y + (1-t) z` and zero above, proving

```
max(t y + (1-t) z, 0) <= t max(y, 0) + (1-t) max(z, 0).
```

Apply this also to -y and -z, multiply by the nonnegative purchase and sale rates and sum over
instruments. This proves convexity of tau. Its translation w -> tau(w - w^-) is convex, and
the cash function k is concave because its remaining terms are affine.

For w and z in F, every coordinate of t w + (1-t) z stays between zero and bar w_i.
Concavity gives `k(t w + (1-t) z) >= t k(w) + (1-t) k(z) >= 0`, so F is convex. If w and z
belong to E, their active coordinates equal a^- and the same is true of their convex combination,
so E is convex. A convex combination of w^- with itself is w^-, proving convexity of N.

The positive-part function is continuous: `max(y, 0) = (y + |y|)/2`, and
`||y| - |z|| <= |y - z|` shows continuity of absolute value. Finite sums and affine substitutions
therefore make tau and k continuous. A convergent sequence in F has a limit obeying each
coordinate bound and the nonnegative cash inequality, by passage to the limit; hence F is
closed. The extra equality defining E is preserved under limits, so E is closed. A convergent
sequence constantly equal to w^- has that same limit, so N is closed. All three classes lie
in the box `[0, 1]^(1+n)` and are bounded.

To check concavity of the objective, use Sigma's definition and finite distributivity:

```
w' Sigma w = sum_s q_s (w' xi_s)^2.
```

For any real x, y and t in [0, 1],
`t x^2 + (1-t) y^2 - [t x + (1-t) y]^2 = t(1-t)(x-y)^2 >= 0`.
Taking x = w' xi_s and y = z' xi_s, multiplying by q_s and summing proves convexity of
the quadratic form. Thus its negative multiple by gamma/2 is concave. For each theta,
the mean term `b(w)' lambda + a alpha - p' c^E` is affine in w, and the negative cost term
is concave as proved above. Hence Q_0(w; theta) is concave. Multiplication by nonnegative
pi_theta and finite summation preserve the displayed concavity inequality, proving concavity
of Qbar_0. The same formula is a finite sum of polynomials and continuous positive parts,
so Qbar_0 is continuous. No derivative at a zero trade is used.

For completeness, prove attainment directly from the closed box, rather than leave it as an
unproved optimization assumption. By claim 003, write the objective using the belief mean:

```
Qbar_0(w) = w' mu(bar theta) - (gamma/2) w' Sigma w - tau(w - w^-).
```

The notation mu(bar theta) evaluates M2's affine mean formula; bar theta need not belong to
Theta. On the whole box [0, 1]^(1+n), both w and the fixed w^- have coordinates in [0, 1].
Therefore every trade coordinate has absolute value at most one, and the absolute score is
bounded above by the finite real number

```
sum_i |mu_i(bar theta)| + (gamma/2) sum_i sum_j |Sigma_ij|
  + sum_i (kappa^+_i + kappa^-_i).
```

Indeed, bound the linear term by the first sum; bound each |w_i Sigma_ij w_j| by |Sigma_ij|;
and bound both positive parts of w_i - w^-_i by one. The triangle inequality then gives the
displayed bound.

Let D be any one of N, E and F. Its score set is nonempty and bounded above, so the completeness
of the real numbers gives a finite supremum V_D. For each positive integer l, the definition of
supremum supplies a holding w_l in D with `V_D - 1/l < Qbar_0(w_l) <= V_D`.

Construct a convergent subsequence inside the box explicitly. Bisect every coordinate interval
of [0, 1]^(1+n). The finitely many closed child boxes cover it, so at least one contains w_l
for infinitely many indices l. Select such a child and repeat inside it. This produces nested
closed boxes with coordinate side lengths 2^(-r) at stage r, each containing infinitely many
indices of the original sequence. Select strictly increasing indices l_r with w_{l_r} in the
stage-r box. In each coordinate the lower endpoints increase and are bounded by every upper
endpoint. Their real supremum lies in every coordinate interval, and the interval lengths
tend to zero. These coordinate suprema form a vector w_* in every selected box. Each
coordinate of w_{l_r} differs from w_* by at most 2^(-r), proving convergence to w_*.

Since D is closed and all w_{l_r} lie in D, w_* belongs to D. Continuity gives convergence of
their scores to Qbar_0(w_*). Their scores also converge to V_D, because l_r tends to infinity
and `V_D - 1/l_r < Qbar_0(w_{l_r}) <= V_D`. Hence Qbar_0(w_*) = V_D, proving attainment in D.
This argument applies to all three classes, including singleton or lower-dimensional ones.

Finally, take a maximizer on N. It is feasible in E, so its score is at most E's attained
maximum. Take a maximizer on E and apply the same argument in F. This proves the two weak
inequalities between the finite maxima.

## Checks

No numerical result is reported. The proof uses nonnegative rates, explicitly includes zero
rates and zero gamma, and treats the nondifferentiability of costs through positive-part
inequalities. Attainment is proved by a closed-box subsequence construction, not inferred
from an optimizer's numerical return. Independent red review is pending.

## Not shown

The inclusions and value inequalities need not be strict. There is no uniqueness claim, no
positive lower bound on an active-trading advantage, and no missing-direction or infeasible-
matching example here. Concavity alone is not a rule for interpreting an unbudgeted marginal
value; all optimization domains in the result include the same cash-budget restriction.

No solver accuracy, empirical cost ranking, statistical certificate or dynamic policy result
is established. The objective remains a belief average of conditional one-quarter scores,
not a predictive-variance criterion. Initial mandate compliance and the absence of additional
mandates are substantive M2 hypotheses: the result does not cover a forced active trade that
makes E empty. Discontinuous fixed fees, minimum trades and changing eligibility are outside
the model. No proposal section 2 commitment is relaxed.

## Prior art

Reviewed the current model, claims 001-003, board/FINDINGS.md and the refuted-claim and experiment
registries; no refuted claim or failed experiment supplies an obstruction under these hypotheses.
The registered model passages in `gallien2018hedge` (section 2) and `garleanu2009dynamic`
(equations 3-4), inspected for claim 003, are background only. No result from either source is
used here. Inclusion, convexity and existence are elementary supporting facts, not novelty.
The attainment argument is given explicitly from real completeness and finite box bisection;
no external existence theorem is assumed and no new web search is asserted.

## Open objections

None recorded; independent review is pending.

## Review

Red, 2026-09-27. Re-derived independently.

**Proof read line by line.** Every step holds.
- *Nesting and nonemptiness*: tau(0) = 0, so k(w^-) = k^- >= 0 and w^- lies in E and F.
- *Convexity*: the positive-part inequality max(ty + (1-t)z, 0) <= t max(y, 0) + (1-t) max(z, 0) is proved correctly, since the right side bounds both candidates. So tau is convex, k is concave, F and E are convex, and N is trivially convex.
- *Closedness and boundedness*: continuity via max(y, 0) = (y + |y|)/2 and the reverse triangle inequality. Limits preserve the bound constraints, the cash inequality and a = a^-. All classes lie in [0, 1]^(1+n) because bar w_i <= 1.
- *Concavity of Qbar_0*: the expansion w'Sigma w = sum_s q_s (w' xi_s)^2 and the identity t x^2 + (1-t) y^2 - (tx + (1-t)y)^2 = t(1-t)(x - y)^2 make the variance term convex with no assumption on the rank of Sigma. The cost term is concave, the mean term affine, and averaging over pi preserves concavity.
- *Attainment*: the score bound on the box is right, because |w_i| <= 1 and at most one positive part of each trade coordinate is nonzero. The supremum sequence plus coordinate bisection is a correct Bolzano-Weierstrass argument, and closedness plus continuity give attainment. It covers singleton and lower-dimensional classes, singular Sigma and gamma = 0.
- *Value chain*: a maximizer on the smaller class is feasible in the larger one.

**Independent checks.**
(i) Exact random test, 5,000 instances. Each has 2-3 instruments; random purchase and sale rates in [0, 1); random limits at least w^-; a random start summing to one with cash; 1-4 shock vectors; random means; gamma in [0, 10]. Every midpoint inequality held for k, and for Qbar_0 including the cost. On the 2,338 pairs with both points in F, every convex combination stayed in F, and in E after fixing a = a^-. Zero violations.
(ii) Attainment is consistent with experiment 004: on 400 M2 instances (800 class problems), red's exact KKT certificates confirmed attained maxima on F and E, with V_N <= V_E <= V_F in every case.

**Attacks tried.**
(i) *An empty ETF-only class*: impossible under M2, since w^- is always in E. The Not shown section says correctly that a forced active trade is outside the result.
(ii) *An incumbent passed off as a certificate*: attainment is proved, not read off a solver.
(iii) *Nondifferentiable costs*: handled by positive-part inequalities, with no derivative at zero.
(iv) *Borrowing hidden in a class*: all three classes carry the same funded cash constraint k(w) >= 0, which is red's FINDINGS requirement (i).

**Scope.** This is elementary existence and nesting; the file says so and claims no strict advantage. The dependency on claim 003 is used only to write Qbar_0 at theta_bar in the bound, and a direct finite-sum bound would also do. It is harmless, since 003 is approved.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* A nonempty compact convex feasible set and a continuous concave objective admit a maximum, and nested feasible sets give ordered maxima.
- *General result.* The Weierstrass extreme-value theorem. Convexity of sublevel sets of convex functions: the cash constraint is a convex cost plus a linear term.
- *Reduction.* The claim proves exactly these hypotheses for M2's F, E and N (closed, bounded, convex, nonempty) and applies them.
- *Verdict: special case.* Nothing is left over.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's line-by-line read, exact convexity test on 5,000 instances, cross-check against experiment 004's KKT certificates and attacks (empty E, incumbent-as-certificate, nondifferentiable costs, hidden borrowing) are sound and match PM's own concavity check; no open objections; limits stated (elementary nesting and existence, no strict advantage or uniqueness, forced active trades outside M2, same funded budget in every class).


Not machine checked. The domains and cost inequalities are finite real-vector statements.
The existence step additionally uses completeness of the reals via a bounded-score supremum
and a convergent subsequence in a closed finite box. It needs no financial hypothesis structure
or measure theory. Claim 003 supplies the already reviewed score representation, but its use
does not make the present convexity or attainment assertions independently reviewed.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2ActionClasses.lean` and the proof
in `lean/Novel/M2ActionClassesProof.lean`. `lake build` and the axiom audit pass (standard axioms
only). No hypothesis structure or cited result is used.

The statement reuses claim 003's formal M2 objects (`cash` for k(w), `tau`, F, E, N and
`beliefScore` for Qbar_0), so both claims are about the same definitions. As there, the counts are
arbitrary, and M2's m = 1, n in {1, 2}, K = 2 is a special case. The initial position is stated
in dollars as M2 defines it: W^- > 0, x^- >= 0, h^- >= 0 and w^-_i <= bar w_i. This gives the claim's
w^- >= 0, k^- >= 0 and sum w^- + k^- = 1. Holdings carry the coordinate (product) topology and
the sup-metric bornology. Convexity, concavity and maxima are Mathlib's `Convex`, `ConcaveOn` on
all holdings, and `IsMaxOn`, whose definitions are the claim's t w + (1-t) z inequalities and
its maxima.

Each part carries only the hypotheses its proof uses:
- nesting and nonemptiness need the initial position;
- closedness, boundedness and continuity of Qbar_0 need nothing;
- convexity of the classes needs nonnegative rates;
- concavity of Qbar_0 needs gamma >= 0, nonnegative rates, nonnegative scenario masses and
  nonnegative belief masses;
- attainment on N, E and F, and max_N <= max_E <= max_F for every choice of maximizers, need
  only the initial position. Attainment needs no concavity and no sign on gamma, the rates, q or pi.
Rates below one, bar w_i <= 1, masses summing to one and centered shocks are not assumed. Each
class is bounded because it lies in the box [0, bar w], whatever the limits.

So no formal part is weaker than the prose. Two differences from the paper proof: attainment uses
Mathlib's compactness of closed boxes and the extreme value theorem (`IsCompact.exists_isMaxOn`)
in place of the explicit bisection argument, and the formal proof does not use claim 003's score
representation, which red noted was inessential. The limits PM recorded at approval apply unchanged.

---
id: 002
title: "Paired mean-error identity with fixed loadings and risk inputs"
status: formalized
model_version: M0
depends_on: []
axioms_used: []
formal: lean/Standalone/PairedMeanError.lean
direction: D1
---
## Statement

This is a notation-level identity for the M0 one-quarter score formula. Fix finite instrument
and factor counts m, n and K, one review t, and loadings B^A and B^E of the M0 dimensions.
Take two holdings vectors `w = (a, p)` and `v = (a_v, p_v)` in the same pre-trade normalization,
with the same initial holdings w^-. Here v denotes a comparator holding, not a trade.
Use the same finite ETF drag c^E, risk coefficient gamma, matrix Sigma and switching-cost
function C_t in both score evaluations below. In particular, the covariance is held fixed when
means are replaced; this is an explicit restriction, not an assertion about arbitrary Sigma(theta).

For any real mean vectors `lambda, hat lambda in R^K` and `alpha, hat alpha in R^m`, write
the two algebraic score evaluations as

```
Q_t(w)     = b(w)' lambda + a' alpha - p' c^E
             - (gamma/2) w' Sigma w - C_t(w - w^-),
hat Q_t(w) = b(w)' hat lambda + a' hat alpha - p' c^E
             - (gamma/2) w' Sigma w - C_t(w - w^-),
```

and define Q_t(v) and hat Q_t(v) by the identical formulas with comparator holdings. Assume
all costs evaluated here are finite. Define

```
d_b = b(w) - b(v),       d_a = a - a_v,
e_lambda = hat lambda - lambda,    e_alpha = hat alpha - alpha.
```

Then, for every such pair of holdings and means,

```
[hat Q_t(w) - hat Q_t(v)] - [Q_t(w) - Q_t(v)]
    = d_b' e_lambda + d_a' e_alpha.
```

The factor-mean contribution vanishes for every possible `e_lambda in R^K` if and only if
`b(w) = b(v)`. Thus exposure matching leaves exactly `d_a' e_alpha` as the paired error;
matching active holdings as well makes the paired error zero. For a particular mean error,
the factor contribution can also vanish when d_b is nonzero but `d_b' e_lambda = 0`.

No feasibility, attainment, concavity, binding-constraint or probabilistic assumption is needed
for this algebraic identity. For an economic comparison, both holdings must separately be
feasible under the same specified working model. No such feasible pair is asserted to exist here.

## Proof

At w the drag, risk and switching-cost terms are identical in the two score evaluations, so
subtracting cancels them exactly and gives

```
hat Q_t(w) - Q_t(w) = b(w)' (hat lambda - lambda) + a' (hat alpha - alpha).
```

The same subtraction at v gives

```
hat Q_t(v) - Q_t(v) = b(v)' (hat lambda - lambda) + a_v' (hat alpha - alpha).
```

Subtract the second equality from the first. Distributivity of the finite dot products gives
`[b(w) - b(v)]' e_lambda + [a - a_v]' e_alpha`. Rearranging the four scalar score terms
on the left and substituting the definitions of d_b and d_a proves the displayed identity.
Costs and risk need not be equal between w and v: they cancel between estimated and original
evaluations at each fixed holding separately.

If d_b is zero, its dot product with every error vector is zero. Conversely, if the dot product
is zero for every real error vector, choose `e_lambda = d_b`. Then
`sum_{j=1}^K (d_b_j)^2 = 0`. Every summand is nonnegative, so each is zero; a real number with
zero square is zero. Thus every coordinate of d_b is zero, proving the converse. This also
covers K = 0, when there is only the empty vector. Substitution of d_b = 0 in the identity
gives the exposure-matching conclusion; substitution of d_a = 0 gives the further cancellation.
For an individual error vector the contribution is the dot product already displayed, proving
the final, weaker cancellation statement without a universal quantifier.

## Checks

No numerical result or experiment is reported. The proof explicitly verifies the orientation
of the estimated-minus-original difference and cancels non-mean terms at each holding.
Independent red review is pending.

## Not shown

This is not a concentration bound, confidence statement, certificate or belief-sensitive
decision rule. The error vectors may be dependent; no independence or distribution is assumed.
The identity alone gives no probability of a score-ranking error. It introduces neither a
return-risk penalty for mean uncertainty nor ambiguity aversion.

One exposure-matching comparator does not establish factor-error cancellation for an optimized
ETF-only comparison: other comparators need not match exposures and the optimizer can change
when means change. Feasible exposure matching and score superiority are not proved here.

The universal cancellation characterization ranges over all real factor-mean errors. For a
restricted error set, vanishing on that set need not imply d_b = 0. Estimated loadings, changing
covariance, drag or costs introduce terms not covered by this identity. No transfer to another
model version or multiperiod conclusion is asserted. No proposal section 2 commitment is
relaxed; the claim concerns only algebra at a quarterly review, with alpha kept distinct from
factor premia and internal costs distinct from investor switching costs.

## Prior art

Inspected board/FINDINGS.md, claims/refuted/, the experiment registry, refs/BIBLIOGRAPHY.md
and the project proof and statement entry files. No registered source text, refuted claim,
failed experiment or project lemma on this identity was present at inspection. No external
result is used and no web literature search is asserted. This is the elementary paired-error
foundation requested by D1, not a proposed novel contribution. The literature comparison
remains outstanding.

## Open objections

None recorded; independent red review has not occurred.

## Review

Red, 2026-09-27. Re-derived independently.

**Identity.** At each fixed holding, the estimated-minus-original score difference contains only the mean terms, because drag, risk and cost are evaluated identically: b(w)'e_lambda + a'e_alpha at w, and b(v)'e_lambda + a_v'e_alpha at v. Subtracting the two gives d_b'e_lambda + d_a'e_alpha, with the orientation as stated. I also checked the identity symbolically in sympy with m = 2, n = 2 and K = 3: fully symbolic loadings, holdings, both mean pairs and c^E, an arbitrary 4x4 matrix Sigma (not even assumed symmetric) and an arbitrary cost function C(w). The difference expands to zero. So the identity needs nothing about Sigma or C_t beyond using the same ones in both evaluations and costs being finite, as the Statement says.

**Characterization.** "Vanishes for every e_lambda in R^K iff d_b = 0" is correct; the choice e_lambda = d_b is the right witness, and the K = 0 case is trivial. The pointwise statement (d_b'e_lambda = 0 with d_b nonzero) is correctly marked weaker, and the restricted-error-set caveat in Not shown is accurate.

**Attacks tried.**
(i) *Hidden dependence of Sigma, c^E or C_t on the means*: excluded explicitly. In M0, Sigma(theta) may vary with theta, and the Statement restricts to a fixed Sigma rather than claiming the general case. That is honest.
(ii) *Correlation read as cancellation*: the Statement makes cancellation depend on d_b = 0, not on correlation between w and v, as proposal section 4B requires.
(iii) *Optimized comparator*: Not shown says correctly that the identity does not extend to sup over the ETF-only class, because the optimizer moves with the means. This is the gap proposal 4B warns about, and nothing here claims past it.
(iv) *Relabelling*: if the factor model is changed, for example by attributing a style exposure to alpha, then d_b, d_a and the errors are redefined together. The identity holds in each coordinate system, but how the error splits between d_b'e_lambda and d_a'e_alpha depends on the factor model. The claim fixes B^A and B^E, so this is in scope, but later uses should say which factor model defines alpha (red FINDINGS 2026-09-27).

**Scope and version.** M0 is admissible, since this is a notation-level identity. The formula instantiates directly in M1's Q_0 (fixed Sigma, tau in place of C_t, pre-trade normalization), and would in M2 as the ROADMAP now describes it. The claim asserts no transfer, correctly. A use in M1 or M2 should cite it with that instantiation made explicit rather than assume it. The claim is elementary linear algebra, and the file says so; it is a foundation, not a contribution.

**Prior art.** This is the linearity of a score in its mean parameters. No registered source states it as a result worth citing, and none is needed. Nothing in claims/refuted or FINDINGS conflicts.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* For scores linear in an unknown parameter with everything else held fixed, the error in an estimated difference between two actions is the parameter error applied to the actions' exposure difference (paired comparison, common-parameter evaluation).
- *General result.* If f(theta, w) = theta'Aw + c(w), then [f(theta_hat, w) - f(theta_hat, v)] - [f(theta, w) - f(theta, v)] = (theta_hat - theta)'A(w - v). Its variance under sample-mean estimation is (w - v)'A'Omega A(w - v)/N.
- *Reduction.* M0's score is affine in (lambda, alpha), with drag, Sigma and costs held fixed, which is the claim's explicit restriction.
- *Verdict: special case,* linearity. Nothing is left over.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's re-derivation, sympy check and attacks (fixed Sigma/costs, correlation vs d_b=0, optimized comparator, relabelling) are sound and match PM's own sympy check; no open objections; limits stated (M0 notation-level, fixed Sigma/costs/drag, no optimized-comparator cancellation, alpha split depends on the fixed factor model; any M1/M2 use must instantiate explicitly).


Not machine checked. The finite deterministic target is subtraction of four scores, linearity
of dot products, and the zero-sum-of-squares argument for the universal cancellation condition.
It needs no probability theory or imported financial result. This claim uses only M0's
permitted notation-level scope and does not rely on M1's pending model review or claim 001.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/PairedMeanError.lean` and the proof in
`lean/Novel/PairedMeanErrorProof.lean`. `lake build` and the axiom audit pass (standard axioms only).
No hypothesis structure or cited result is used. A holding is a pair `(a, p)` whose full vector is indexed
by `Fin m ⊕ Fin n`. Loadings, drag, gamma, Sigma, w^- and C_t form one shared record, so both
holdings are scored with the same inputs and only the means change. Sigma may be any real square
matrix (symmetry is not assumed), gamma any real number and C_t any real function, so nothing
beyond the claim is assumed. Proved:
- the identity, for every pair of holdings and means;
- `d_b' e = 0` for every real e if and only if `b(w) = b(v)`, for every K including 0;
- the exposure-matching and active-matching conclusions;
- for one particular error, with no hypothesis on d_b, `d_b' e_lambda = 0` gives paired error
  `d_a' e_alpha`.
The prose remark that this can happen with d_b nonzero is formalized as an explicit witness
(K = 2, m = 2, n = 0) in which both d_b and e_lambda are nonzero. The formal statement is not
weaker than the prose, and no gap was found. The limits PM recorded at approval (fixed Sigma, costs
and drag; no cancellation for an optimized comparator; M0 notation-level only) apply unchanged:
the formal statement fixes the same inputs and says nothing about optimized comparators or M1/M2.

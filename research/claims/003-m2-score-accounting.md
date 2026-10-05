---
id: 003
title: "M2 score accounting and dependence on the belief mean"
status: formalized
model_version: M2
depends_on: [001]
axioms_used: []
formal: lean/Standalone/M2ScoreAccounting.lean
direction: D1
---
## Statement

This combines D1's normalized accounting and belief-mean foundations: the latter is the short
finite averaging step applied to the same conditional-score formula. Model definitions are
unchanged; positive/negative trade parts keep M2's existing notation.

Fix any M2 instance: m = 1, n in {1, 2}, K = 2, strictly positive initial wealth W^-;
initial nonnegative holdings and cash satisfying the position limits; known loadings and signed
ETF drag c^E; nonnegative purchase and sale rates kappa^+_i, kappa^-_i below one; gamma >= 0;
and the specified finite nonempty sets Theta and S. The scenario masses q_s are nonnegative
and sum to one, the joint centered shocks have q-mean zero and are independent of theta and
the action, and every instrument gross return is positive at every theta and scenario. Let pi
be any nonnegative masses on Theta summing to one. No independence among shock coordinates,
no independence between the components of theta under pi, and no nonsingularity of Sigma is
assumed. Costs are paid at the review, and terminal wealth is marked without an exit cost.

For every feasible holding w = (a, p) in F, put v = w - w^-, u = W^- v and
`G_s(w; theta) = W_1(w; theta, s) / W^- - 1`. Define the finite conditional mean and variance
operators by `E_q X = sum_s q_s X_s` and `Var_q X = sum_s q_s (X_s - E_q X)^2`.
The following identities hold for every theta in Theta and every s in S:

```
C_0(W^- v) / W^- = tau(v),
sum_i w_i + k(w) + tau(v) = 1,
G_s(w; theta) = w' r_s(theta) - tau(v),
E_q G(w; theta) = w' mu(theta) - tau(v),
Var_q G(w; theta) = w' Sigma w,
Q_0(w; theta) = E_q G(w; theta) - (gamma/2) Var_q G(w; theta).
```

In particular the cost enters normalized conditional expected gain once. The variance here
is conditional on theta, not variance under a mixture over theta.

Define the belief mean `bar theta = sum_theta pi_theta theta`, with components
`bar lambda = sum_theta pi_theta lambda` and `bar alpha = sum_theta pi_theta alpha`.
Then, for every w in F,

```
Qbar_0(w) = b(w)' bar lambda + a bar alpha - p' c^E
           - (gamma/2) w' Sigma w - tau(w - w^-)
         = Q_0(w; bar theta).
```

The last expression means evaluation of the same affine score formula at bar theta; it does
not assert bar theta belongs to Theta. The affine return formula evaluated there also has
strictly positive instrument gross returns for every s in S.

Consequently, for any two beliefs on the same Theta with the same bar theta and all other
decision inputs fixed, Qbar_0 is identical at every feasible holding. The rankings and sets
of maximizers on F, E and N are therefore identical. This statement does not assert attainment;
it identifies the sets whether or not a maximizer exists. No constraint is assumed to bind,
and no concavity or attainment assertion is used in the identities.

## Proof

First verify the normalization needed to instantiate claim 001 in M2. For any real number y
and W^- > 0,
`max(W^- y, 0) = W^- max(y, 0)` and `max(-W^- y, 0) = W^- max(-y, 0)`.
If y >= 0, the first maxima are W^- y and y and the second are both zero; if y < 0,
the first maxima are zero and the second are -W^- y and -y. These cases also cover y = 0.
Apply the identities with y = v_i and substitute the directional cost definitions:

```
C_0(W^- v)
  = sum_i [kappa^+_i W^- max(v_i, 0) + kappa^-_i W^- max(-v_i, 0)]
  = W^- tau(v).
```

Division by W^- proves the first identity. This proof uses M2's rates on the gross change in
holdings at the review quote; it does not substitute a rate quoted on cash tendered.

The cost function C_0 is finite and nonnegative, because its finitely many rates and trade
parts are finite and nonnegative. Initial cash and holdings satisfy claim 001's assumptions.
With u = W^- v, the dollar cash equation divided by W^- gives

```
h^+ / W^- = k^- - sum_i v_i - C_0(W^- v)/W^- = k(w).
```

Also x^+ / W^- = w^- + v = w. Apply the self-financing identity of claim 001 at t = 0
with precisely this C_0 and u, and divide by W^- = sum_i x^-_i + h^- > 0. It gives
`sum_i w_i + k(w) + tau(v) = 1`. This is the explicit transfer and normalization of the M0
identity; claim 001 alone did not prove the M2 normalization.

Now divide M2's marked terminal wealth formula by W^- and subtract one:

```
G_s(w; theta)
  = k(w) + sum_i w_i [1 + r_{i,s}(theta)] - 1
  = k(w) + sum_i w_i - 1 + sum_i w_i r_{i,s}(theta)
  = w' r_s(theta) - tau(v).
```

There is no second payment at terminal marking. The tau term in this expression is the
review payment already removed from cash, expressed as a loss relative to initial wealth.

The M2 return definitions give r_s(theta) = mu(theta) + xi_s. The zero q-means of each
coordinate of z^f, z^A and z^E imply `sum_s q_s xi_s = 0` by distributivity through the
fixed loading matrices. Summing the displayed identity for G_s and using sum_s q_s = 1 gives
`E_q G(w; theta) = w' mu(theta) - tau(v)`. Subtracting this mean from G_s yields w' xi_s.
Hence its variance is

```
sum_s q_s (w' xi_s)^2
  = sum_s q_s sum_i sum_j w_i xi_{i,s} xi_{j,s} w_j
  = sum_i sum_j w_i [sum_s q_s xi_{i,s} xi_{j,s}] w_j
  = w' Sigma w.
```

All sums are finite, so these rearrangements require no interchange-of-limit assumption.
Finally, direct multiplication of the instrument mean vector gives
`w' mu(theta) = b(w)' lambda + a alpha - p' c^E`. Substitution in the conditional mean
and variance expressions proves the stated identity for Q_0, for either sign of c^E and
for unequal purchase and sale rates.

In the belief average, the loadings, holdings, drag, gamma, Sigma and cost are fixed in theta.
Distribute the finite sum over pi across Q_0. The lambda and alpha terms become
`b(w)' bar lambda` and `a bar alpha`, while each remaining term is multiplied by
`sum_theta pi_theta = 1`. This proves the formula for Qbar_0 without assuming independence
between the means or membership of bar theta in Theta.

For each instrument i and scenario s the return formula is affine in theta. By the same
finite-sum calculation,
`1 + r_{i,s}(bar theta) = sum_theta pi_theta [1 + r_{i,s}(theta)]`.
Each bracket is strictly positive. All coefficients are nonnegative and at least one is
positive because their finite sum is one, so the displayed gross return is strictly positive.

For two beliefs with the same bar theta, the explicit formula for Qbar_0 has equal right-hand
sides at every holding. Thus every pairwise score inequality on the common domain is the same
under the two beliefs. A holding is a maximizer precisely when its score is at least the score
of every holding in that domain, so maximizer sets also coincide. F and its subclasses E and N
depend on the fixed funding data, not on pi; therefore the argument applies to each class.

## Checks

No numerical experiment or check is reported here. The proof handles both signs of every
trade explicitly, zero scenario or belief masses, singular Sigma, and a belief mean outside
Theta. Red's model review allowed M2 claims; it is not independent review of this claim.

## Not shown

No existence or uniqueness of an optimizer, strict advantage of full trading, feasible ETF
replication, economically material effect or empirical calibration is established. These
identities are supporting foundations, not a contribution beyond the model's accounting.

The belief average is not a mean-variance score using predictive variance. Changing belief
dispersion or alpha/premium dependence while holding their means and other decision inputs
fixed cannot change this criterion or its optimizer sets. The claim does not restrict arbitrary
tie-breaking among the same maximizers. It supplies no confidence statement, uncertainty penalty,
ambiguity-aversion preference or dynamic learning effect.

The result is one-quarter conditional-score accounting in cash-account units. It includes the
review cost and no compulsory terminal liquidation cost; it is not a multiperiod or holding-period
wealth comparison. Fixed fees, actual load schedules and redemption windows remain outside M2.
No proposal section 2 commitment is relaxed. No transfer to a different model version or
automatic transfer of experiments 001 and 002 to general asymmetric M2 costs is asserted.

## Prior art

Read board/FINDINGS.md, the claim and experiment registries, and the M0 self-financing proof;
claims/refuted/ contained no refuted claim and no experiment was marked failed or withdrawn.
Inspected the registered model passages in `gallien2018hedge` (section 2, bank-account dynamics
and terminal-wealth objective) and `garleanu2009dynamic` (equations 3-4, quadratic trading costs
and dynamic score). These are full-text passages, not an audit of either paper's full argument.
They provide context for costs in wealth and score definitions; neither paper is used as a
proof dependency or claimed to be reproduced here. No literature theorem or external numerical
input is assumed. No new web search was performed. The result is a direct finite-sum derivation
of the chosen M2 criterion, with no novelty claim.

## Open objections

None recorded; independent review of this claim is pending.

## Review

Red, 2026-09-27. Re-derived independently.

**Exact check.** Red generated 398 random M2 instances from the model's definitions, in exact rationals:
- n in {1, 2};
- random loadings and signed ETF drag;
- 2-4 scenarios with random masses, some zero, and shocks centered exactly;
- 1-4 parameter points in Theta with random belief masses, some zero, so theta_bar is generally outside Theta;
- independent purchase and sale rates in [0, 1), and gamma in [0, 10] including 0;
- a random holding w.

Instances where some gross return was not positive were discarded, as M2 requires. On every instance, all six displayed identities hold exactly at every theta and scenario, with Sigma computed as sum_s q_s xi_s xi_s'. So do the belief-average formula (the sum over theta of pi_theta Q_0(w; theta) equals Q_0(w; theta_bar)) and the positivity of every gross return at theta_bar. The identities do not even need w in F; the Statement's restriction to F is harmless.

**Proof read line by line.**
- The positive-part homogeneity case split is complete.
- The transfer of claim 001 is valid: its hypotheses are finite nonnegative cost and nonnegative initial holdings and cash, all satisfied. The division by W^- = sum x^- + h^- > 0 is exactly the step red's review of claim 001 asked any M2 use to write out.
- The terminal-marking algebra charges tau once, as a review-date payment.
- The q-mean of xi_s is zero by linearity.
- The variance expansion is a finite rearrangement.
- The belief average uses only that the loadings, drag, Sigma, gamma and costs do not depend on theta.
- The positivity argument at theta_bar (a convex combination of positive numbers with weights summing to one) is correct.
- The maximizer-set conclusion follows from equality of the scores on a common domain and needs no attainment.

**Attacks tried.**
(i) *Cost counted twice*: tau enters G_s, and hence Q_0, once; the terminal marking adds no exit cost, and the claim says so.
(ii) *Mixture variance smuggled in*: Var_q is conditional on theta, and the belief average adds no variance of mu(theta) across the belief. The Statement and Not shown both say this, so no uncertainty effect is claimed.
(iii) *Membership of theta_bar in Theta*: not assumed. Only the affine formula is evaluated there, with positivity proved.
(iv) *Directional-cost base*: the proof uses M2's rates on the gross change in holdings and correctly declines to substitute an offering-price rate. That matters for loads; see red's M2 review note (c).
(v) *Transfer overreach*: none. Experiments 001 and 002 are explicitly not transferred to asymmetric rates.

**Scope.** This is accounting and a limitation, not a contribution, and the file says so. Its second half is the formal version of the obstruction in red's FINDINGS entry (2026-09-27, "relabelling is inert") and in PM's M1 review. In M2 no one-quarter decision can depend on belief dispersion or on dependence between alpha and premium beliefs at fixed means. D2 or D3 results must therefore get any uncertainty effect from a different criterion or model version. The prior-art keys `gallien2018hedge` and `garleanu2009dynamic` are registered; they are used as context only, correctly.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* When an objective is affine in an unknown parameter and every parameter-free term is known, a Bayes-average criterion depends on the belief only through its mean (certainty equivalence for linear-in-parameter objectives).
- *General result.* E_pi[a(w)'theta + c(w)] = a(w)'E_pi theta + c(w).
- *Reduction.* M2's conditional score is theta'Aw - p'c^E - (gamma/2)w'Sigma w - tau, with Sigma computed from a shock law independent of theta. So the hypotheses hold, and equal belief means give equal criteria and maximizing sets. The accounting half is claim 001's identity after normalization.
- *Verdict: special case.* This is also the standard observation that, with known covariance, a one-period mean-variance investor's parameter uncertainty enters only through the predictive mean. That literature, for example estimation-risk work from the 1970s, is for the librarian to pin down. Nothing is left over.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's exact check on 398 M2 instances, line-by-line proof read and attacks (double-counted cost, mixture variance, theta_bar outside Theta, directional-cost base, transfer overreach) are sound and match PM's own exact check on 300 instances; no open objections; limits stated (accounting and a limitation, not a contribution; no attainment or optimizer existence; belief enters M2 decisions only through its mean, so any uncertainty effect needs another criterion or version; no transfer of experiments 001-002 to asymmetric rates).


Not machine checked. Claim 001 is machine checked in M0; the positive-part homogeneity,
division by W^-, finite moment identities and belief averaging proved here are additional
paper steps. The proposed formal target is finite real algebra, with scenario and belief
weights summing to one; no measure-theoretic or cited-result hypothesis structure is needed.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2ScoreAccounting.lean` and the
proof in `lean/Novel/M2ScoreAccountingProof.lean`. `lake build` and the axiom audit pass (standard
axioms only). No hypothesis structure or cited result is used.

The statement file defines M2's objects directly from `model/SPEC.md` (M2 and the M1 definitions
it inherits), including C_0, tau, k(w), the dollar funding equations, F, E, N, b(w), r_s(theta),
mu(theta), xi_s, Sigma, W_1, G_s, E_q, Var_q, Q_0, Qbar_0 and bar theta. The counts are arbitrary:
m active funds, n ETFs, K factors. M2's m = 1, n in {1, 2}, K = 2 is a special case. Theta is a
finite index type mapped to parameter values, and the scenarios form a finite type.

Every part is stated for every holding w, not only w in F, as red observed is possible. Each part
carries only the hypotheses its proof uses:
- the cost normalization, the funding transfer (x^+ = W^- w, h^+ = W^- k(w) and
  sum_i w_i + k(w) + tau(v) = 1) and the gain identity need only W^- > 0;
- the moment and Q_0 identities also need the scenario masses to sum to one and each shock to have
  q-mean zero;
- the formula for w' mu(theta) needs nothing;
- Qbar_0(w) = Q_0(w; bar theta) and the same-mean conclusions need only belief masses summing to one;
- positivity of gross returns at bar theta also needs nonnegative belief masses and positive gross
  returns at every support point.
The remaining M2 restrictions are not needed and are not assumed: rates in [0, 1), gamma >= 0,
nonnegative scenario masses, compliant initial holdings, and independence of the shocks from theta.
So no formal part is weaker than the prose.

The same-mean conclusion is proved as equal Qbar_0 at every holding, equal pairwise rankings, and
equal maximizer sets on each of F, E and N, with no attainment assumed. One difference from the
paper proof: the formal proof re-derives the normalized self-financing identity directly in M2's
index type rather than importing claim 001's Lean lemma, which is stated over `Fin (m + n)`. The
content is the same finite algebra. The limits PM recorded at approval apply unchanged.

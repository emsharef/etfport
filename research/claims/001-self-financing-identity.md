---
id: 001
title: "Self-financing identity at a quarterly review"
status: formalized
model_version: M0
depends_on: []
axioms_used: []
formal: lean/Standalone/SelfFinancingIdentity.lean
direction: D1
---
## Statement

This is a notation-level identity in M0, not a result about a working return model.
Fix any finite instrument counts m and n, any review t, nonnegative real initial holdings
`x^- in R^(m+n)` and cash `h^-`, and any trade vector `u in R^(m+n)`. Let the shareholder
switching cost `C_t(u)` be a finite nonnegative real number. No proportionality, continuity,
convexity, attainment or nonempty optimization domain is assumed. Define, as in M0,

```
x^+ = x^- + u,
h^+ = h^- - sum_i u_i - C_t(u).
```

Then the self-financing identity is

```
sum_i x^+_i + h^+ + C_t(u) = sum_i x^-_i + h^-.
```

For the same trade, the funded long-only restrictions `x^+_i >= 0` for every i and `h^+ >= 0`
are equivalent to

```
x^-_i + u_i >= 0 for every i,
sum_i (x^-_i + u_i) + C_t(u) <= sum_i x^-_i + h^-.
```

For every trade satisfying these restrictions,
`0 <= C_t(u) <= sum_i x^-_i + h^-`. No particular restriction is assumed to bind. If in addition
`C_t(0) = 0`, the zero trade satisfies these restrictions and preserves total holdings plus cash.
These are funding restrictions only; additional mandates can still exclude a trade.

## Proof

Finite summation distributes over the coordinate identity `x^+_i = x^-_i + u_i`. Substituting
this and the definition of h^+ gives

```
sum_i x^+_i + h^+ + C_t(u)
  = sum_i x^-_i + sum_i u_i + h^- - sum_i u_i - C_t(u) + C_t(u)
  = sum_i x^-_i + h^-.
```

This calculation does not require feasibility or a cost sign. Rearranging it gives

```
h^+ = sum_i x^-_i + h^- - [sum_i (x^-_i + u_i) + C_t(u)].
```

For real numbers this cash amount is nonnegative exactly when the displayed budget inequality
in the statement holds. Coordinate by coordinate, `x^+_i >= 0` is exactly
`x^-_i + u_i >= 0`. Combining these equivalences proves both directions of the funding
reformulation, without invoking any other constraint.

For a feasible trade, all terms in `sum_i x^+_i + h^+` are nonnegative, so subtracting their
sum from the initial total in the identity bounds C_t(u) above by that total. The lower bound
is the assumed nonnegativity of the cost. Finally, when u is the zero vector and C_t(0) is zero,
the definitions give `x^+ = x^-` and `h^+ = h^-`. The assumed initial nonnegativity proves
feasibility, and these equalities prove preservation of the total.

## Checks

No numerical check or experiment is reported. The proof is finite algebra and covers purchases,
sales and mixed trades without assigning trade signs. Independent review is pending.

## Not shown

No claim about gross returns, terminal wealth, the normalization or timing of an objective,
optimality, strict ETF-only disadvantage, empirical costs or economic materiality is established.
This identity alone does not show how many cost deductions a specified return score contains.
No automatic transfer to a later model version is claimed. Zero-cost no trade requires the
extra hypothesis C_t(0) = 0; the algebraic identity itself does not imply that hypothesis.
No proposal section 2 commitment is relaxed: this statement is restricted to the accounting
at a review, and does not change any return, information or trading-frequency assumption.

## Prior art

Inspected board/FINDINGS.md, claims/refuted/, the experiment registry, refs/BIBLIOGRAPHY.md and
the project's Lean proof and statement entry files. At inspection there were no findings,
refuted claims, failed experiments, registered source texts or project lemmas addressing this
identity. No external source or theorem is used and no web literature search is asserted.
This is elementary supporting algebra from the funding definitions, not a proposed contribution
or a novelty claim. The broader literature comparison remains outstanding.

## Open objections

None recorded; independent red review has not occurred.

## Review

Red, 2026-09-27. Re-derived independently.

**Identity and funding equivalence.** In sympy with symbolic holdings, trades, cash and cost:
- sum x^+ + h^+ + C - (sum x^- + h^-) expands to 0;
- h^+ equals sum x^- + h^- - [sum(x^- + u) + C], so h^+ >= 0 is exactly the stated budget inequality;
- x^+_i >= 0 is exactly x^-_i + u_i >= 0.

Both directions of the equivalence hold, with no sign assumption on u and none on C for the identity itself. The bound 0 <= C_t(u) <= sum x^- + h^- for feasible trades follows because x^+ and h^+ are nonnegative. An exact rational search over 20,000 random integer instances found no feasible trade violating it. The zero-trade statement correctly needs the extra hypothesis C_t(0) = 0 and initial nonnegativity.

**Attacks tried.**
(i) *Hidden financing*: none. h^+ >= 0 is imposed on the post-cost cash, so the cost is paid from the same budget as the trades and cannot be borrowed. This is the budget whose omission manufactures an active trade in red's FINDINGS entry (case 1a).
(ii) *Cost counted twice*: the identity deducts C_t(u) once, from cash. The claim says correctly that this does not settle how many times a score deducts it, and so claims nothing about Q_t.
(iii) *Execution price*: positions are credited at the trade amount u_i, so any spread or load must sit in C_t(u), which is M0's convention. A cost embedded in the execution price and also charged in C_t would be counted twice. That is outside this identity, but later calibrations must respect it (compare the analyst's gross/net backlog item).
(iv) *Ambiguity*: "nonnegative real initial holdings x^- ... and cash h^-" should be read as covering h^- too. The proof's zero-trade step uses h^- >= 0, and M0 imposes it, so this is wording, not a gap.

**Scope and version.** M0 is admissible, since this is a notation-level identity. ROADMAP now says foundation claims name M2. The transfer to M2 is one line, which I checked: divide by W^- = sum x^- + h^- > 0 and set w = x^+/W^-, k = h^+/W^-, tau(v) = C_0(W^- v)/W^-. Then sum w + k + tau = 1, which is M2's k(w) definition. A later use in M2 should write that step rather than assume it; the claim does not assert it, correctly.

**Prior art.** Elementary accounting, and the file says so; nothing registered or refuted conflicts.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Paying a fee from cash when trading at quoted prices lowers total wealth by exactly the fee (the discrete-time self-financing budget).
- *General result.* The self-financing condition: post-trade holdings plus cash plus fee equal pre-trade holdings plus cash, whenever trades settle at the quote and fees are paid from cash.
- *Reduction.* The claim's hypotheses are exactly the definitions x^+ = x^- + u and h^+ = h^- - 1'u - C(u), and the identity follows by adding them. The long-only equivalences are restatements.
- *Verdict: special case,* a textbook accounting identity. Nothing is left over, and the claim already calls itself notation-level.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's symbolic re-derivation, exact random search and attacks (hidden financing, double-counted cost, execution price) are sound and match PM's own sympy check; no open objections; limits stated (M0 notation-level accounting only, h^- >= 0 read from M0, zero-trade needs C_t(0)=0, no score or terminal-wealth claim; any M2 use must write red's one-line normalization step).


Not machine checked. The target is finite real-valued sums, cancellation, and inequalities;
it needs no stochastic assumptions or imported financial result. The claim deliberately uses
M0's permitted notation-level scope and does not use unreviewed M1 assumptions.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/SelfFinancingIdentity.lean` and the
proof in `lean/Novel/SelfFinancingIdentityProof.lean`. `lake build` and the axiom audit pass (standard
axioms only). No hypothesis structure or cited result is used. Instruments are indexed by
`Fin (m + n)`; holdings and trades are real vectors; `C` is an arbitrary real function of the trade.
All four parts are proved:
- the identity and the funding equivalence, for every trade, with no sign, feasibility or cost
  hypothesis;
- the cost bound, for every trade satisfying the funded long-only restrictions with `0 <= C(u)`;
- for the zero trade, under `x^- >= 0`, `h^- >= 0` and `C(0) = 0`: feasibility, `x^+ = x^-`,
  `h^+ = h^-`, and preservation of the total.
Each part carries only the hypotheses its proof uses, so the formal statement is not weaker than
the prose, and no gap was found. `h^- >= 0` is read as red and PM read it, and only the zero-trade
part uses it. The limits PM recorded at approval apply unchanged: M0 notation-level accounting
only, with no score or terminal-wealth claim and no M2 normalization step formalized.

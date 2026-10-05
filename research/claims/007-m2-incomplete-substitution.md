---
id: 007
title: "An added ETF can enlarge active trading while its full-span menu still cannot match the optimum"
status: formalized
model_version: M2
depends_on: [003, 005]
axioms_used: []
formal: lean/Standalone/M2IncompleteSubstitution.lean
direction: D1
---
## Statement

Consider the following two assumed M2 instances, differing only by the presence of a second
ETF initially held at zero. They specify the equal-cost T1 example in experiment 005, but
the proof below is independent of its optimizer and search results. All quantities are
normalized by W^-=1; cash earns gross return one, gamma=1, and all position limits are one.
Both purchase and sale rates are 1/2000 for every instrument in both menus. No tax, flow,
interim trade, additional mandate or terminal liquidation cost is present.

| Instrument | Loading row | Residual shock size | ETF drag | Initial holding |
|---|---|---|---|---|
| Active fund | (1,1/2) | 3/100 | not applicable | 1/2 |
| First ETF | (1,0) | 1/200 | -1/10000 | 1/3 |
| Second ETF (two-ETF menu only) | (1,1/4) | 1/100 | 0 | 0 |

Initial cash is 1/6. The parameter support is the singleton
`theta=(lambda_1,lambda_2,alpha)=(1/50,1/200,-1/400)`, with belief mass one. All means,
costs and risks are assumed inputs, not observed or calibrated quantities. The active fund
remains eligible despite its negative alpha.

There are 32 equiprobable scenarios: five independent signs taking values -1 and 1 multiply
the first-factor, second-factor, active-residual, first-ETF-residual and second-ETF-residual
shock sizes, respectively. The factor shock sizes are 3/50 and 1/50; residual sizes are in
the table. In the one-ETF instance the last sign is unused. Thus the scenario law and joint
returns of the shared instruments agree between the two menus, and the law is independent
of actions and parameters. These are prospective decision inputs, not future observations.

Within each menu let F, E and N have M2's usual meanings, in particular E fixes a=1/2.
The unique class optima, their review costs, and their scores are:

| Menu and class | Optimal holding | Cash | Review cost | Score |
|---|---|---|---|---|
| One ETF, N | (1/2,1/3) | 1/6 | 0 | 11033/720000 |
| One ETF, E and F | (1/2,3001/6003) | 0 | 1/12006 | 61830113/3427920000 |
| Two ETFs, N | (1/2,1/3,0) | 1/6 | 0 | 11033/720000 |
| Two ETFs, E | (1/2,0,2999/6003) | 0 | 5/12006 | 2104284079/115315228800 |
| Two ETFs, F | (0,0,11995/12006) | 0 | 11/12006 | 8512677811/461260915200 |

Consequently, the full-minus-ETF-only optimal score gap is zero with one ETF and
`6369433/30750727680 > 0` with two. Both menus' E and F optima strictly improve on N.
The optimal active trade changes from zero to a sale of 1/2 when the second ETF is added.
The one-ETF optimum is ETF-only trading, not no trade: it buys 1000/6003 of the first ETF.

The exposure restrictions in the two menus are different:

1. With one ETF, L_E is the first-coordinate line. Voluntarily selling all holdings at the
   review is a feasible full action with exposure change (-5/6,-1/4), outside L_E. Thus some
   full actions have a missing-direction obstruction even though this menu's optimal gap is zero.
2. With two ETFs, L_E=R^2. Matching the full optimum's exposure while retaining a=1/2
   would uniquely require ETF holdings `(p1,p2)=(1/2,-11/12006)`. The negative second
   holding violates nonnegativity, so this full optimum has no feasible ETF-only exposure
   match despite full span. These are holding levels, not trade amounts.

The second menu therefore has incomplete feasible exposure substitution and a strict score
advantage from changing the active holding, under the identical funded budget in E and F.
This example does not identify the exposure obstruction as the sole cause of the gap;
alpha, residual risks and trading costs all enter the objective.

## Proof

### The instances and score

The initial holdings are nonnegative, below their limits, and sum to 5/6, leaving the stated
cash. All cost rates lie in [0,1). Independent symmetric signs make every shock centered and
all cross-products of different primitive shocks have zero mean. The conditional mean vector
for the two-ETF menu is

```
mu = (1/50, 201/10000, 17/800) = (800,804,850)/40000.
```

Indeed the active mean is 1/50+(1/2)(1/200)-1/400=1/50; the first ETF's signed drag adds
1/10000 to its factor-implied mean; the second ETF has mean 1/50+(1/4)(1/200)=17/800.
The absolute shock sums are 1/10, 13/200 and 3/40, respectively. Each is less than one,
and every mean is positive, so every instrument gross return is positive in every scenario.
This verifies M2's positivity restriction. The one-ETF instance simply omits the last coordinate.

Direct scenario covariance gives

```
Sigma = (1/40000) * [[184,144,146],
                     [144,145,144],
                     [146,144,149]].
```

For example its active diagonal is (3/50)^2+(1/2)^2(1/50)^2+(3/100)^2=184/40000;
its active/second-ETF entry is (3/50)^2+(1/2)(1/4)(1/50)^2=146/40000. All other entries
follow by the same products. The one-ETF covariance is the leading two-coordinate submatrix.
For every nonzero vector x the two-ETF quadratic form is

```
(3/50)^2 (x_A+x_1+x_2)^2 + (1/50)^2 (x_A/2+x_2/4)^2
  + (3/100)^2 x_A^2 + (1/200)^2 x_1^2 + (1/100)^2 x_2^2 > 0.
```

The residual-square terms prove strict positivity without a rank assumption or numerical
eigenvalue calculation. Omitting x_2 proves the same fact for the one-ETF covariance.

Let c=1/2000 and let w^- denote the stated initial vector in the appropriate menu. Write
`tau(w-w^-)=c sum_i |w_i-w^-_i|`. Because initial holdings plus cash sum to one, M2's
cash is `k(w)=1-sum_i w_i-tau(w-w^-)`. Its classes therefore share the restriction
`sum_i w_i+tau(w-w^-)<=1`, in addition to 0<=w_i<=1. E also fixes w_A=1/2.
By the M2 score and claim 003, the singleton belief gives

```
Qbar_0(w)=mu'w-(1/2)w'Sigma w-tau(w-w^-).
```

No second drag deduction, extra funding source or variance across parameter means is used.

### A direct sufficient inequality for these candidates

We give a complete inequality argument, not an invocation of an external KKT theorem.
For a feasible candidate w, choose a cost subgradient vector t as follows: t_i=c when
w_i>w^-_i, t_i=-c when w_i<w^-_i, and any t_i in [-c,c] when w_i=w^-_i. For every z,

```
tau(z-w^-)-tau(w-w^-) >= t'(z-w).
```

To see this coordinatewise, c|z_i-w^-_i| >= t_i(z_i-w^-_i) because |t_i|<=c; equality
holds at w_i since t_i has the specified sign there, or both sides vanish at a zero trade.
Subtract these coordinate equalities and sum.

Put g=mu-Sigma w. For eta_B>=0 define the score certificate residual
`R_i=g_i-eta_B-(1+eta_B)t_i`. Suppose the candidate has zero cash. Expanding the quadratic
score difference exactly, and then applying the subgradient inequality, yields

```
Qbar_0(z)-Qbar_0(w)
  = g'(z-w) - (1/2)(z-w)'Sigma(z-w)
      - [tau(z-w^-)-tau(w-w^-)]
  <= R'(z-w) - (1/2)(z-w)'Sigma(z-w)
      + eta_B [sum_i z_i+tau(z-w^-) - sum_i w_i-tau(w-w^-)]
  <= R'(z-w) - (1/2)(z-w)'Sigma(z-w)
```

for every feasible comparator z in the same class. For the first inequality, substitute
g=R+eta_B*1+(1+eta_B)t and note that the difference between the displayed upper bound
and the equality is `(1+eta_B)[tau(z-w^-)-tau(w-w^-)-t'(z-w)]>=0`. The second inequality
uses the candidate's binding budget and the comparator's identical funded restriction.

If R_i<=0 at candidate coordinates equal to zero, R_i>=0 at coordinates equal to one,
and R_i=0 at all other free coordinates, then R'(z-w)<=0. In E the active coordinate
is fixed, so its contribution vanishes for any value of R_A. Positive definiteness then
makes the score difference strictly negative whenever z!=w. These conditions suffice for
unique global optimality in the stated class; no assumption of differentiability at a kink
or of a strictly feasible point is needed.

### Exact candidates and certificates

The three nontrivial holdings in the Statement obey their position bounds. For the one-ETF
holding the only trade is a purchase 1000/6003, so its cost is 1/12006; its total holdings
are 12005/12006. For the two-ETF E holding, absolute trades sum to
1/3+2999/6003=5000/6003, so cost is 5/12006 and total holdings are 12001/12006.
For the two-ETF F holding, absolute trades sum to 5/6+11995/12006=22000/12006, so cost
is 11/12006 and total holdings are 11995/12006. Each sum of holdings and cost is one.
The E candidates fix a=1/2, so they belong to their stated classes.

Here are sufficient vectors for the inequality just proved. Each eta_B is positive.

| Candidate and class | eta_B | t | R |
|---|---|---|---|
| One ETF, F | 132379/8284140 | (-65869/841651900, 1/2000) | (0,0) |
| Two ETFs, F | 1635545/96096024 | (-1/2000,-1/2000,1/2000) | (-1215029/7687681920, -7778611/960960240000, 0) |
| Two ETFs, E | 204871/12012003 | (0,-1/2000,1/2000) | (-56648773/48048012000, -1093009/24024006000, 0) |

Every entry follows by substituting the displayed mu, Sigma and candidate holding into
g=mu-Sigma w and R=g-eta_B*1-(1+eta_B)t. These are finite rational identities. In the
one-ETF row the active trade is zero and its selected subgradient is legal because
`65869*2000=131738000 < 841651900`; the ETF is purchased, requiring t_E=c. Both positions
are interior and R is zero, so this is the unique F optimum. It fixes a=1/2, so it is also
the unique E optimum in that menu.

In the two-ETF F row the active fund and first ETF are sold to zero, the second ETF is
purchased to an interior holding, and the signs of t and R are exactly those required.
In the two-ETF E row the active holding is fixed with zero trade, so t_A=0 is legal and
R_A need not vanish; the first ETF is sold to zero and the purchased second ETF is interior.
The remaining R entries have the required signs. The sufficient inequality therefore proves
each unique optimum. N is a singleton, so its unique holding is immediate.

Substitution in the explicit quadratic score gives the rational scores in the Statement.
For N, the mean term is 167/10000 and half the variance is 991/720000, yielding
11033/720000 in both menus. The two-ETF score difference is

```
8512677811/461260915200 - 2104284079/115315228800
  = 95541495/461260915200 = 6369433/30750727680 > 0.
```

The one-ETF E/F score exceeds the no-trade score by direct cross-multiplication. Appending
a zero second-ETF position preserves its feasibility and score in the two-ETF E class.
That holding differs from the unique two-ETF E optimum, so the latter has strictly larger
score. Thus both menus' E and F values strictly exceed N as stated. The active-coordinate
comparisons and the ETF purchase 3001/6003-1/3=1000/6003 now follow from the optimal vectors.

### Missing span and constrained matching

With one ETF the incumbent exposure is (5/6,1/4), and every ETF-only exposure change lies
on the first-coordinate line. The review-date action w=(0,0) has cost
c(1/2+1/3)=1/2400 and cash 2399/2400, so it is feasible in F. Its exposure change is
(-5/6,-1/4), outside L_E; claim 005's missing-direction test rules out an ETF-only match.
This is a feasible action, not an optimum, consistent with the zero optimal gap in this menu.

With two ETFs, the loading rows (1,0) and (1,1/4) are linearly independent, so L_E=R^2.
The full optimum's exposure is `(11995/12006,11995/48024)`. An ETF-only holding retaining
a=1/2 could match it only if

```
1/2+p1+p2=11995/12006,
1/4+p2/4=11995/48024.
```

Solving the second equation gives p2=-11/12006; substituting in the first gives p1=1/2.
The solution is unique and violates p2>=0, so it fails claim 005's position-bound condition.
There is no missing span direction in this case. Feasibility, not the algebraic span, blocks
the match. This proves both obstruction statements without treating a short position as an
admissible M2 holding.

## Checks

`uv run python checks/exp005-equal-cost/check.py` independently constructs the scenario
covariance and verifies exact cash and subgradient certificates for both classes in both
menus, the score gap and the shorting obstruction. Its one-ETF implementation uses the
16 distinct shared-shock combinations instead of repeating each for the unused fifth sign;
the distribution is the same. These previously committed finite checks supplement the
complete paper proof above. They are not a proof about a general ETF menu or an independent
reproduction of the whole experiment 005 search.

## Not shown

All inputs are assumed. No economic materiality, empirical effect, statistical confidence,
optimal dynamic policy or realistic cost ranking is established. The equal rates eliminate
an assumed active-versus-ETF cost-rate disadvantage here; they do not equate the total costs
of different trades. A larger menu weakly improves each class's attainable objective by
preserving its old feasible actions, but the gap between the classes need not decrease.
This example only establishes its own strict gap and active-trade comparison.

The negative-alpha fund is not excluded by eligibility. Its initial holding and all estimates
are fixed without future information. Means have singleton support, so this example identifies
no role for estimation uncertainty or ambiguity aversion. It is a conditional one-quarter
score calculation, with no terminal exit charge. No proposal section 2 commitment is relaxed.

An unmatched feasible exposure alone does not imply a score advantage, as the one-ETF menu
shows. The two-ETF gap is not attributed solely to the shorting obstruction: expected returns,
residual risks and transaction amounts differ between the optima. Relaxing shorting, changing
initial holdings, deleting signed drag or changing any rates requires another comparison.
No transfer to a different model version, global monotonicity assertion or no-trade-band
result is claimed.

## Prior art

Read M2, claim 005, the current FINDINGS and the refuted/experiment registries. There is no
refuted claim. Experiment 005's failed T3 band conclusion is not used; its T1 equal-cost
instance supplies assumed input data, independently analyzed here. The registered passages
in `bichuch2014investing` (sections 2.1-2.2), `gallien2018hedge` (section 2) and
`garleanu2009dynamic` (equations 3-4) were previously inspected for D1 and are background
only. No literature theorem is imported, and no new search is claimed. The direct quadratic
and absolute-value inequalities are elementary supporting mathematics; the example is not
presented as a novel general allocation theorem.

## Open objections

None recorded; independent review is pending.

## Review

Red, 2026-09-27. Re-derived independently. Red had already certified this instance's optima once, as experiment 005's first T1 equal-cost counterexample, in red's reproduction of that experiment.

**Independent exact recomputation** with red's own code, not `checks/exp005-equal-cost/check.py`.
- mu = (1/50, 201/10000, 17/800) from the loadings, the singleton theta and the signed drag, which enters once.
- Sigma, by enumerating all 32 scenarios, equals (1/40000)[[184,144,146],[144,145,144],[146,144,149]]; the one-ETF Sigma is its leading block. Both are positive definite by sympy's exact test.
- Every gross return is positive.
- Each claimed optimum is feasible, with zero cash, and carries red's own exact KKT certificate for its class, found by red's multiplier-interval search rather than taken from the table. The optima are: one ETF E and F (1/2, 3001/6003); two ETFs E (1/2, 0, 2999/6003); two ETFs F (0, 0, 11995/12006).
- Scores: N 11033/720000 in both menus; one ETF 61830113/3427920000; two ETFs E 2104284079/115315228800 and F 8512677811/461260915200. The gap is exactly 6369433/30750727680 (about 2.1 bp per quarter), and the E and F values exceed N in both menus.
- The obstructions: with one ETF, selling everything is feasible (cash 2399/2400) and its exposure change (-5/6, -1/4) is off L_E. With two ETFs the match that keeps a = 1/2 is uniquely (p1, p2) = (1/2, -11/12006).

**Proof checked line by line.** The direct sufficient inequality is correct.
- The quadratic expansion is exact.
- Substituting g = R + eta_B 1 + (1 + eta_B) t leaves a term (1 + eta_B)[tau(z) - tau(w) - t'(z - w)] >= 0, by the coordinatewise subgradient inequality.
- The eta_B bracket is <= 0, because the candidate's budget binds and every comparator obeys the same funded budget.
- The sign conditions on R make R'(z - w) <= 0, and positive definiteness gives strict decrease, hence uniqueness.

Red recomputed all three certificate rows (eta_B, t, R) from the displayed mu, Sigma and holdings. They match exactly, satisfy |t_i| <= 1/2000 with the required signs, and have eta_B >= 0. The one-ETF zero-trade subgradient t_A = -65869/841651900 is legal.

**Attacks tried.**
(i) *Unequal funding* (FINDINGS requirement (i)): no. E and F share one funded budget, and every candidate's budget binds.
(ii) *Span read as feasibility* (requirement (ii)): no. The two-ETF menu has full span, and the match fails only through p2 >= 0, the "position bounds obstruct" branch of claim 005. This is the pattern of red's FINDINGS case 2, now with costs and residual risk.
(iii) *Drag counted twice* (requirement (iii)): no. c^E = -1/10000 enters mu_1 once.
(iv) *Alpha relabelling or belief effects* (requirement (iv)): none. The belief is a singleton and the alpha is stated against the two-factor model.
(v) *Causal overreach*: the claim explicitly does not attribute the gap to the shorting obstruction alone, and red agrees it cannot. The E optimum is forced to keep the negative-alpha fund and its factor-2 exposure. The F optimum sheds both and buys E2, which carries factor 2 without the negative alpha. Alpha, residual risk and costs all move.
(vi) *Missing direction presented as material*: the one-ETF missing-direction action is a feasible non-optimal sale, stated as such. The one-ETF gap is zero, which correctly shows that an unmatched feasible exposure does not imply an advantage.

**Scope.** This is an assumed, uncalibrated one-quarter example with a gap of about 2.1 bp per quarter. It is exactly the D1 worked example of incomplete feasible substitution, and it also makes experiment 005's T1 mechanism a proved statement: an added ETF enlarges active trading. Together with claim 006, it separates the case where only alpha matters (complete substitution) from the case where full span still leaves the optimum unmatched. It establishes no materiality, which D1's kill criterion still leaves to the analyst's realistic comparison.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Adding a generator can change the optimal use of an outside asset non-monotonically, and linear span does not imply reachability under nonnegativity and a budget, because the attainable set is a polytope, not a subspace.
- *General result.* Attainable long-only budgeted portfolios form a polytope, and spanning in the linear sense does not give feasibility (Farkas; the constrained-replication literature, such as hedge-fund replication). Comparative statics in the menu need not be monotone without lattice or supermodularity structure (Topkis).
- *Reduction.* Both halves are instances: the full-span two-ETF menu still needs a short to match, which is outside the polytope, and the active trade's growth is a failure of monotone comparative statics.
- *Verdict: special case, as an explicit example.* Left over: the exact example.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's own exact recomputation and certificates, line-by-line check of the direct sufficient inequality and attacks (unequal funding, span as feasibility, double drag, belief effects, causal overreach, missing direction as material) are sound and match PM's own 32-scenario covariance, candidate scores (gap 6369433/30750727680) and grid check of the two-ETF full class; no open objections; limits stated (assumed example, about 2 bp per quarter, gap not attributed to the shorting obstruction alone, no materiality).


Not machine checked. The formal target is this pair of finite rational instances, their
covariance and positive gross returns, the direct global score inequality with explicit
certificate vectors, the unique optima and the two exposure obstructions. Claims 003 and 005
being formalized does not establish machine checking of these additional computations.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2IncompleteSubstitution.lean` and
the proof in `lean/Novel/M2IncompleteSubstitutionProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used.

The instances. Both menus are entered literally into claim 003's formal M2 structure, with every
number as in the Statement. A scenario is a 5-tuple of independent signs, each of the 32 with mass
1/32; the one-ETF menu leaves the fifth sign unused. The singleton belief is a one-point type with
mass one. The statement uses claim 004's hypotheses and claim 005's L_E.

Proved:
- (i) Both instances satisfy every M2 restriction, including centered shocks, masses summing to
  one and positive gross returns in all 32 scenarios. The shared instruments have identical
  scenario returns in the two menus.
- (ii) All five rows of the table: the stated holding is the unique maximizer of its class (every
  other holding in the class scores strictly less), with the stated cash, review cost and score.
- (iii) The two gaps (0 and 6369433/30750727680 > 0); E and F strictly above N in both menus; the
  active trade (0, then -1/2); and the one-ETF ETF purchase 1000/6003.
- (iv) One ETF: selling everything is in F, and its exposure change (-5/6, -1/4) is outside L_E.
  Two ETFs: L_E = R^2; with a = 1/2, the full optimum's exposure is matched iff
  (p1, p2) = (1/2, -11/12006); and no holding in E has that exposure.

The proof. It writes each menu's criterion as mu'w - (1/2) Qf(w) - (1/2000) x (trade parts), with
Qf expanded over the 32 scenarios. That quadratic form is the Proof's sum of squares, including
the residual squares. Unique optimality is the Proof's certificate inequality: the score gap to
any feasible comparator z is at least Qf(z - w)/2, and Qf(z - w) > 0 whenever z != w. The
multipliers are found by `linarith` from the trade-part identities, the funded budget and the
position bounds. So the table's eta_B, t and R values are not themselves machine checked; they
belong to the Proof, not the Statement, and red recomputed them by hand.

Relation to the prose. The explicit covariance matrix appears only through Qf; it is not a
separate conjunct. The prose remark that the obstruction is not the sole cause of the gap is
interpretation. Part (iv) is stated for every ETF-only holding, not only for exact matching with
a = 1/2. No gap was found between the formal statement and the prose. The limits PM recorded at
approval apply unchanged.

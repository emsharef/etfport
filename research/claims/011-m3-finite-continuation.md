---
id: 11
title: "M3 admits optimal finite policies and an attained continuation representation"
status: formalized
model_version: M3
depends_on: [001]
axioms_used: []
formal: lean/Standalone/M3FiniteContinuation.lean
direction: D2
---
## Statement

Fix an M3 instance as reviewed in model/SPEC.md, including its certainty-equivalent scale.
All restrictions apply: one active fund, one or two ETFs, two quarterly reviews, finite
nonempty parameter and shock sets, probability masses pi_0 and q, fixed unknown means,
conditionally independent quarterly draws with the same law q independent of ownership,
strictly positive gross returns at every specified parameter/scenario pair, public factor
and all-fund first-quarter returns, fixed known loadings and signed ETF drag, fixed purchase
and sale rates in [0,1), nonnegative funded holdings and cash, all position limits one,
initial wealth W_0^->0, rho>0, and utility -exp(-rho W_2/W_0^-). There is no terminal
liquidation. No positive definiteness, positive mass at every state, strict feasibility,
unique optimum or differentiability at a trade kink is assumed.

Use M3's definitions of Y, P_0, pi_1, F/E/N controls, V_1^R, H_0^R, V_{D,R}, CE_{D,R}
and Delta_R. For each root label D in {F,E,N} and continuation label R in {F,E,N}, define
Pi_{D,R} to consist of a root dollar trade u_0 and one dollar trade u_1(y) for each y in Y.
The root trade belongs to D_0; each u_1(y) belongs to R_1 at the state marked after u_0
and y. Feasibility is required at every specified observation, including zero-probability
ones; zero trades are available at those nodes. Policies cannot distinguish hidden pairs
(theta,s_0) that generate the same y. Let Phi be M3's explicit finite expected-terminal-
utility sum on these policy vectors, and put

```
M=max({1} union {1+r_i(theta,s) : i,theta,s}).
```

The following hold simultaneously for all nine pairs (D,R).

1. Pi_{D,R} is nonempty, convex and compact in its finite-dimensional coordinate space.
   Phi is continuous and concave there and attains a maximum. Every feasible policy has
   strictly positive marked wealth at review 1 and terminal time, on every specified path,
   and `W_2<=M^2 W_0^-`. Consequently
   `-1<V_{D,R}<=-exp(-rho M^2)<0`, so CE_{D,R} is finite.
2. For each fixed posterior pi on Theta, including zero masses, each conditional problem
   V_1^R(x,h,pi) attains its maximum for all nonnegative x,h. Keep W_0^-, rho, the return
   law and cost rates fixed when varying x,h. Then V_1^R is jointly concave in (x,h) and
   nondecreasing in h. Its domain includes x=h=0, where the only feasible trade is zero
   and its value is -1. The posterior and marked holdings/cash are sufficient for the
   review-1 optimization problem in the explicit conditional sense proved below.
3. H_0^R is concave on the funded full root set F_0. For every feasible root trade the
   conditional optima can be chosen at all observations to form one feasible observable
   continuation policy. The exact, attained Bellman representation is

   `V_{D,R}=max_{Pi_{D,R}} Phi=max_{u_0 in D_0} H_0^R(u_0)`.

4. For every fixed R, `V_{N,R}<=V_{E,R}<=V_{F,R}`, and the corresponding CE values obey
   the same order. For every fixed D, `V_{D,N}<=V_{D,E}<=V_{D,F}`, again also on the CE
   scale. In particular Delta_R>=0, and

   `Delta_R=0` if and only if some optimal policy in Pi_{F,R} has `u_0,A=0`.

   This equivalence asserts existence, not that all full optima make no active trade.
   It supplies an exact value test, not an explicit scalar band or marginal formula.

This is a supporting finite-control result. It makes no sign claim for Delta_E-Delta_N
or Delta_F-Delta_E and no structural contribution or economic magnitude claim for D2.

## Proof

### 1. A single funded review

Write W=h+sum_i x_i for a nonnegative incoming state. The cost C is nonnegative,
continuous and convex: each positive-part function is continuous and convex, and its
coefficient is nonnegative. Its value at zero is zero. The funded constraints are
`x+u>=0` and `h-1'u-C(u)>=0`; E adds u_A=0, and N adds u=0. Zero is feasible in
all three classes. The first constraints are affine, the cash function is concave, and
the additional equalities are affine, so each class is closed and convex.

The accounting equation (the same substitution as claim 001) is

```
sum_i (x_i+u_i) + h-1'u-C(u) = W-C(u) <= W.
```

Every term on the left is nonnegative for a feasible trade. Thus
`-x_i<=u_i<=W-x_i` for every i. These finite bounds prove compactness of each class.
They also show that if W=0 the only feasible trade is zero.

If W>0, the post-review wealth cannot be zero. Otherwise all nonnegative post-review
holdings and cash would be zero, implying u=-x. For that trade the cash equals
`h+sum_i (1-kappa^-_i)x_i`, which is strictly positive since W>0 and every sale rate
is below one. This is a contradiction. Marking positive wealth consisting of nonnegative
positions and cash at strictly positive gross returns preserves positivity. Marking
increases wealth by at most the factor M, because cash has gross return one and each
risky gross return is at most M.

The root therefore has positive wealth after trading; the first marking and second
review also preserve positive wealth, as does terminal marking. Trading never increases
wealth. Two successive marking bounds give W_1^-<=M W_0^- and W_2<=M^2 W_0^-.
These statements hold on all specified paths, irrespective of their probability masses.

### 2. The finite policy set and objective

For y in Y let d_i(y)>0 be its observed gross return for instrument i. This is
well-defined because the public observation includes all instrument returns. At its node,

```
x_1,i^-(y;u_0)=d_i(y)(x_0,i^-+u_0,i),
h_1^-(u_0)=h_0^- - 1'u_0-C(u_0).
```

Thus each node's incoming risky holdings are affine in u_0 and its cash is concave in u_0.
The root risky constraints and the node risky constraints
`d_i(y)(x_0,i^-+u_0,i)+u_1,i(y)>=0` are affine inequalities. The node cash constraint is

```
h_0^- - 1'u_0-C(u_0) - 1'u_1(y)-C(u_1(y)) >= 0.
```

It is a superlevel set of a continuous concave function of the policy coordinates.
Every E or N restriction is a linear equality on the corresponding trade coordinates.
There are finitely many such closed convex constraints, so their intersection Pi_{D,R}
is closed and convex. The policy that makes zero trades at both reviews belongs to it.

The single-review bounds imply `|u_0,i|<=W_0^-` and, at every node,
`|u_1,i(y)|<=W_1^-(y)<=M W_0^-`. Hence Pi_{D,R} is bounded, and thus compact in its
finite-dimensional space. Zero-probability nodes cause no exception to these bounds.

For a path (theta,s_0,s_1), let y=Y_1(theta,s_0) and let
`d_i^1=1+r_i(theta,s_1)`. Expanding terminal wealth gives

```
W_2 = h_0^- - 1'u_0 - 1'u_1(y)
      + sum_i [d_i(y)(x_0,i^-+u_0,i)+u_1,i(y)] d_i^1
      - C(u_0)-C(u_1(y)).
```

For each fixed path this is an affine function minus two convex functions of the policy
coordinates, so it is continuous and concave. The utility U_rho is continuous, increasing
and concave: its first derivative is rho exp(-rho z)>0 and its second is
`-rho^2 exp(-rho z)<0`. For any convex mixture of two feasible policies, terminal wealth
at the mixture is at least the same mixture of terminal wealths. Applying monotonicity
and then concavity of U_rho proves the pathwise utility concavity inequality. A finite sum
with nonnegative masses pi_0(theta)q_{s_0}q_{s_1} preserves it, proving concavity and
continuity of Phi.

A continuous real function on this nonempty compact finite-dimensional policy set attains
its maximum. This is the elementary finite-dimensional extreme-value argument; it does
not use a stochastic-control existence theorem or an assumption about the optimum.
Every policy has positive terminal wealth on all paths, so its finite probability average
is strictly greater than -1. The uniform upper wealth bound gives utility at most
`-exp(-rho M^2)` pathwise. The attained value satisfies the bounds in part 1.

### 3. Conditional problems, state sufficiency and concavity

Fix a probability vector pi and a nonnegative state (x,h). The single-review feasible set
R_1(x,h) is nonempty compact. Its finite conditional objective is continuous in u, so a
maximum exists. The expression for its terminal wealth is

```
h-1'u-C(u)+sum_i (x_i+u_i)(1+r_i(theta,s)).
```

It is jointly concave in (x,h,u). The same composition argument proves joint concavity of
the conditional expected utility for fixed pi. If states (x,h) and (x',h') have optimal
trades u and u', take t in [0,1]. Their coordinatewise mixtures satisfy the risky constraints,
and convexity of C makes mixed-state post-trade cash at least the mixture of the two
nonnegative cash amounts. The trade restrictions u_A=0 or u=0 are preserved under mixing.
Thus the mixed trade is feasible at the mixed state. Its conditional expected utility is
at least t V_1^R(x,h,pi)+(1-t)V_1^R(x',h',pi), and maximization at that mixed state proves
joint concavity of V_1^R. This proof does not assume differentiability of a value function.

If cash increases while x and pi are fixed, any old feasible trade remains feasible and
its terminal wealth increases by exactly the cash increment on every scenario. The
increasing utility therefore gives nondecreasing V_1^R in h. At x=h=0 the earlier trade
bounds force u=0, making terminal wealth zero and value -1.

At an observation y with P_0(y)>0, independence of the second scenario draw conditional
on theta gives the conditional mass of (theta,s_1) as

```
[sum_{s_0:Y_1(theta,s_0)=y} pi_0(theta) q_{s_0} q_{s_1}]/P_0(y)
 = pi_1(theta|y) q_{s_1}.
```

The future feasible trades depend on past information only through marked x,h, since costs,
eligibility and review-1 restrictions are fixed and there are no lot or holding-age terms.
The conditional objective depends on it only through this state and pi_1. Thus histories
with the same (x,h,pi_1) have the same conditional optimization problem. No claim of
sufficiency is made for a different model or for a future law that depends on more history.

### 4. Exact conditional separation and root concavity

Fix a feasible u_0. Grouping the finite path sum by observation y and using the preceding
conditional identity gives, for every feasible continuation vector, its utility as

```
sum_{y:P_0(y)>0} P_0(y) [conditional utility of u_1(y)
                        at (x_1^-(y;u_0),h_1^-(u_0),pi_1(.|y))].
```

Each bracket is at most V_1^R at that node, so the sum is at most H_0^R(u_0).
Conversely, choose an attaining conditional trade at every positive-probability observation;
there are finitely many. Choose zero at the others. These choices form a feasible policy
with one trade per public observation, hence cannot distinguish hidden histories with the
same y. There is no coupling of controls across mutually exclusive observations. The
resulting sum equals H_0^R(u_0). This proves both fixed-root equality and existence of a
feasible continuation attaining it.

Taking root suprema proves V_{D,R}=sup_{u_0 in D_0} H_0^R(u_0). A policy attaining the
left side exists by part 1. Its root trade has H_0^R at least that policy's value by the
fixed-root upper bound. It cannot be strictly greater, since the fixed-root attainment
construction would then produce a policy better than the global maximum. Thus this root
trade attains the supremum, giving the two maxima in part 3. No unproved continuity of
H_0^R or measurable-selection result is needed.

Finally mix any u_0,v_0 in F_0 with coefficient t. At each y its marked risky holdings
are the mixture of the corresponding holdings, while its cash is at least their cash
mixture because C is convex. Its posterior is unchanged, since P_0 and pi_1 do not depend
on the action. Monotonicity in cash followed by joint concavity of V_1^R therefore gives

```
V_1^R(x_1^-(y;t u_0+(1-t)v_0),h_1^-(t u_0+(1-t)v_0),pi_1)
 >= t V_1^R(x_1^-(y;u_0),h_1^-(u_0),pi_1)
    +(1-t) V_1^R(x_1^-(y;v_0),h_1^-(v_0),pi_1).
```

Summing with nonnegative P_0(y) proves concavity of H_0^R on F_0. This specifically
accounts for the concave cash coordinate; it does not treat marked wealth as affine.

### 5. Class comparison and the no-active-trade value test

For fixed R, the root constraints give Pi_{N,R} subset Pi_{E,R} subset Pi_{F,R}.
For fixed D, zero belongs to E_1 and E_1 is contained in F_1 at every marked state,
giving Pi_{D,N} subset Pi_{D,E} subset Pi_{D,F}. Maximizing the identical Phi on these
nested sets gives the value orders. On (-infinity,0), `v -> -(1/rho)ln(-v)` is strictly
increasing, so it preserves the orders and equality. The values lie in its domain by part 1.
This gives Delta_R>=0 and `Delta_R=0 iff V_{F,R}=V_{E,R}`.

If the values are equal, a maximizing E-root policy exists and is feasible in the full
class with that same maximal value. Its active root trade is zero. Conversely, a full
maximizer whose active root trade is zero belongs to Pi_{E,R}, so the E-root maximum
is at least the full value. Nesting gives the opposite inequality, hence equality and
Delta_R=0. This proves exactly the existence equivalence, with no uniqueness inference.

## Checks

`uv run python checks/011/check.py` checks feasible mixtures of fixed policies in all nine
root/continuation combinations using M3's assumed finite instance, exact rational funding,
pathwise wealth concavity and bounds, and floating utility concavity. It explicitly preserves
one node trade per public observation and the E and N restrictions. These fixed cases do
not prove attainment or concavity in general.

`checks/m3-definition/check.py` checks Bayes normalization, fixed-policy path/posterior
agreement, rho rescaling and the CE scale. Red's separate `checks/red-m3-definition/check.py`
solves finite joint and conditional problems as a numerical check of the formulation; no
solver output is a premise of this proof.

## Not shown

- This establishes finite-control foundations, not a novel portfolio mechanism. No scalar
  alpha threshold, band width, cost monotonicity or strict continuation effect follows.
- Individual root and future class values are ordered; differences of root gaps across
  future controls need not be ordered. No sign for either CE contribution is proved.
- No differentiability, unique optimal policy, unique holding, or common supergradient is
  asserted. Equality of values gives some no-active-trade optimum, not all such optima.
- Concavity in (x,h) holds with pi, rho and the initial-wealth denominator fixed. It is not
  concavity in beliefs, a claim about mean-sufficient beliefs, or a fixed-rho result after
  changing the normalization denominator to current wealth. CE concavity is not asserted.
- The all-limits-one restriction ensures zero trades are always feasible after drift.
  General concentration caps, mandatory trades, private observations, changing fee eligibility,
  infinite observation supports and costs with fixed fees are outside this statement.
- No literature theorem is assumed, no empirical magnitude is estimated, and no M2 score
  or band result is silently applied to M3's terminal objective.

## Prior art

Checked M3, its two red definition reviews and CE recheck, the D2 roadmap and FINDINGS,
the refuted-claim directory, and the limitations of experiments 005 and 007 and claim 010.
The registered texts already read for D2, `bichuch2014investing` Theorem 2.2,
`gallien2018hedge` section 5 Proposition 1, and `liu2013portfolio` Theorem 2.3, study dynamic
transaction-cost control and boundaries in other models. Their economic results are not
imported here. This proof expands M3's finite sums and constraints directly; compactness,
concave maximization and finite conditional separation are supporting mathematics, not
claimed contributions. In particular neither existence nor the Bellman identity settles
D2's kill criterion or its requested structural marginal decomposition.

## Open objections

None yet; red review pending.

## Review

**Red, 2026-09-27.** I checked the proof by hand, tested its statements numerically and independently, and attacked it.

**The hand check holds.**
- *Single review.* The accounting sum_i(x_i + u_i) + h - 1'u - C(u) = W - C(u), with every term nonnegative, gives -x_i <= u_i <= W - x_i, and zero is the only trade at W = 0. Suppose post-trade wealth were zero with W > 0. Then u = -x, and the cash would be h + sum_i(1 - kappa^-_i)x_i > 0, a contradiction. Marking at gross returns of at most M, with cash at one, gives W_1^- <= M W_0^- and W_2 <= M^2 W_0^-. Hence every path's utility lies in (-1, -exp(-rho M^2)], and so does the attained value.
- *Policy set.* Pi_{D,R} is an intersection of affine constraints, superlevel sets of continuous concave cash functions and linear E/N equalities. It is bounded by |u_0,i| <= W_0^- and |u_1,i(y)| <= M W_0^-, including at zero-probability nodes. W_2 is affine minus two convex costs on each path, and U_rho is increasing and concave, so Phi is concave, and it attains its maximum on a compact set.
- *Conditional problems.* I re-derived the conditional law of (theta, s_1) given y as pi_1(theta | y) q_{s_1} directly from the finite sum. Mixing feasible trades at mixed states preserves the risky constraints, the E/N equalities and nonnegative cash, since C is convex. That gives joint concavity of V_1^R for fixed pi without differentiability. Monotonicity in h and V_1^R(0, 0, pi) = -1 follow as stated.
- *Bellman identity.* The regrouping by y is exact. Zero-mass nodes take the zero trade, which is always feasible. Attainment is transferred to the root trade without continuity of H_0^R or a selection theorem.
- *Concavity of H_0^R.* It correctly uses monotonicity in cash before joint concavity, because marked cash is only concave in u_0.
- *Orders.* The nesting in both labels holds at every marked state, and CE is strictly increasing on (-infinity, 0). The Delta_R = 0 equivalence is proved in both directions and claims existence only.

One wording point, not a gap: Section 2's list of constraints names the node cash constraints but not the root cash constraint h_0^+ >= 0. The node constraint does not imply the root one, because a review-1 sale could repair negative root cash. The Statement's definition (u_0 in D_0) does include it, and the argument treats it like the node constraints (closed, convex, bounded). A formal version must list it explicitly.

**Independent numerical checks** (`checks/red-m3-definition/check.py` on main, plus a scratch attack reusing its solver; floating CLARABEL, not certificates).
- *Bellman identity.* On instances A and B, all nine (D, R) cells solved as one joint convex program agree with the per-observation value H_0^R at the joint root trade to within 1e-6 bp in certainty equivalent. In instance C the six solved cells agree to a relative 8e-10.
- *Value orders.* Both orders hold in every cell of A and B, in each root-class column and each continuation row. For example, in A, root F gives 10135.46 >= 10121.88 >= 10113.86 bp across F_1, E_1 and N_1.
- *The Delta_R = 0 test.* In B, Delta_F and Delta_N are 0 to printed precision, with a full optimum whose u_0,A is 0 to 1e-6. Delta_E = 0.0325 bp > 0, with the full optimum's u_0,A = -0.0095.
- *Concavity and monotonicity.* Over instances A-C and R in {F, E, N}, I tested random midpoints: 50 of H_0^R on feasible root pairs in F_0, and 54 of V_1^R at random nonnegative (x, h) pairs, plus 54 tests of monotonicity in h (cash + 0.05). There were no violations at relative tolerance 1e-7, and every inequality held with a strict margin. Four random states where the solver returned "optimal_inaccurate" were skipped, not counted.
- *Claim's own check.* `checks/011/check.py` passes (36 fixed-policy mixtures across the nine controls).

**Attacks that did not succeed.**
- Policies that anticipate: one trade per y, fixed before any hidden path is summed.
- Zero-probability nodes breaking compactness or feasibility: bounded, with zero available.
- Wealth reaching zero, which would make the log undefined: excluded because kappa^- < 1.
- Concavity of H_0 through a wealth-affine shortcut: avoided.
- Existence read as all optima: explicitly excluded.
- Sufficiency overreach: limited to M3's history-free costs and conditionally i.i.d. law.
- Ordering of the CE contributions: correctly not claimed. My instances A and C show Delta_E - Delta_N and Delta_F - Delta_E with opposite signs, which is consistent with the Not shown.

**Scope.** The Not shown is honest. This is supporting finite-control mathematics (compactness, concave maximization and finite regrouping), with no economic mechanism, sign or magnitude, as the claim says. It does not count as a structural D2 result for the kill criterion. It contradicts nothing in the paper or in claims 009-010.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* A finite-horizon decision problem with finitely many observation nodes, compact convex action sets and a continuous concave objective has optimal policies and a Bellman decomposition, and its value is concave in the state.
- *General result.* Standard finite-stage dynamic programming (for example Bertsekas): measurable-selection issues vanish on finite observation spaces, and joint concavity is preserved by partial maximization over convex graphs.
- *Reduction.* The claim proves those hypotheses for M3's funded sets and exponential utility, then applies them.
- *Verdict: special case,* and the claim already calls itself supporting mathematics. Nothing is left over.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's hand check (single-review accounting, compact convex policy set, joint concavity of V_1^R without differentiability, exact Bellman regrouping with zero-mass nodes, concavity of H_0^R via monotonicity in cash, value orders, the Delta_R=0 existence test), numerical tests on three instances and attacks are sound, and PM reran checks/011; no open objections. Limits stated: supporting finite-control mathematics with no mechanism, sign or magnitude, not a structural D2 result; its Section 2 list omits the root cash constraint h_0^+>=0, which the Statement includes through D_0 and any formal version must list explicitly.


None yet. The finite policy constraints, positivity and bounds, pathwise concavity and
finite Bayes regrouping form the deterministic core. Exponential utility and logarithmic
CE require their ordinary analytic properties; no global axiom, conjecture or hidden
attainment hypothesis is introduced. The eventual formal statement must preserve all nine
controls, zero-probability nodes, the fixed W_0^- denominator and the existence-only scope
of the no-active-trade conclusion. This paper proof is not machine checked.

Lean, 2026-09-27: machine checked. The statement is in `lean/Standalone/M3FiniteContinuation.lean`
and the proof in `lean/Novel/M3FiniteContinuationProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used.

M3 in Lean. M3 had no formal counterpart, so the statement file defines it from `model/SPEC.md`,
reusing claim 003's M2 return and cost objects (`ret`, `cost`, `W0`, the scenario law q) with dollar
initial holdings and cash. The following are defined literally:
- the public observation (factor realization and every instrument's first-quarter return) and the
  finite set Y of all specified observations, including zero-probability ones;
- the likelihood, P_0 and the posterior, with the prior as bookkeeping when P_0(y) = 0;
- the classes F, E and N;
- the policy set Pi_{D,R}, with one root trade and one trade per y in Y, so policies cannot
  distinguish hidden pairs that give the same y;
- Phi, V_{D,R} (as a supremum), V_1^R, H_0^R, CE and Delta_R.
Counts are arbitrary (M3's n in {1, 2} and K = 2 are special cases).

The root cash constraint. PM asked at approval that any formal version state h_0^+ >= 0
explicitly. It does: the root trade must satisfy `Feas1` at (x_0^-, h_0^-), and `Feas1` includes
0 <= h_0^- - 1'u_0 - C(u_0), together with x_0^- + u_0 >= 0 and the class restriction. Every node
trade satisfies the same three conditions at its marked state.

Hypotheses used: rho > 0; scenario and prior masses nonnegative and summing to one; rates in
[0, 1); nonnegative initial holdings and cash with W_0^- > 0; strictly positive gross returns at
every specified parameter and scenario. Centered shocks are not needed. Conditional independence of
the two quarterly draws is built into Phi's weights pi_0(theta) q_{s_0} q_{s_1}, as M3 specifies.

Proved, for all nine (D, R):
- Part 1: Pi_{D,R} is nonempty, convex and compact in the product coordinate space; Phi is
  continuous and concave on it and attains its maximum, which equals V_{D,R}; W_1^- and W_2 are
  strictly positive on every path. For every bound M >= 1 on all gross returns (so in particular the
  claim's M), W_1^- <= M W_0^-, W_2 <= M^2 W_0^- and -1 < V_{D,R} <= -exp(-rho M^2).
- Part 2: for any nonnegative belief, V_1^R is attained at every nonnegative state, jointly concave
  in (x, h) on nonnegative states, and nondecreasing in h. At x = h = 0 only the zero trade is
  feasible, and the value is -1 when the belief sums to one.
- Part 3: the Bayes identity pi_0 L = P_0 pi_1; Phi as the P_0-weighted sum of conditional
  objectives at the marked state and posterior, which is the formal content of the claim's state
  sufficiency; concavity of H_0^R on F_0; for every feasible root trade, a feasible continuation
  attaining H_0^R, which also bounds every continuation; and V_{D,R} = max Phi = max over D_0 of
  H_0^R, both attained.
- Part 4: the value and CE orders over root classes and over continuation classes; Delta_R >= 0;
  and Delta_R = 0 iff some optimal policy in Pi_{F,R} has zero active root trade.

Relation to the prose. The attaining continuation chooses a conditional maximizer at every node,
including zero-probability ones, where the paper chooses zero; the claim asserts only existence.
The upper bounds are stated for every admissible M, which includes the claim's M. No gap was found
between the formal statement and the Statement. The limits PM recorded at approval apply unchanged:
this is supporting finite-control mathematics, with no mechanism, sign or magnitude.

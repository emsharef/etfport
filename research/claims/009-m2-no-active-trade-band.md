---
id: 009
title: "The M2 no-active-trade band after ETF optimization, including binding bounds"
status: formalized
model_version: M2
depends_on: [003, 004]
axioms_used: []
formal: lean/Standalone/M2NoActiveTradeBand.lean
direction: D2
---
## Statement

Fix an M2 instance. All its assumptions remain in force: one active fund, one or two ETFs,
nonnegative funded holdings, compliant initial holdings, position limits in [0,1], directional
rates in [0,1), gamma>=0, finite centered return scenarios, and one common funded budget.
No strict feasibility, positive definite covariance, nonzero position limit or uniqueness
is assumed. This is a one-quarter statement, with no continuation value.

### Alpha family and the meaning of no active trade

Index the original parameter support by h, with values (lambda_h,alpha_h) and masses pi_h.
Let bar alpha_0=sum_h pi_h alpha_h. Vary only the active belief mean x by replacing every
support point with `(lambda_h, alpha_h-bar alpha_0+x)`, keeping masses and every other
input fixed. The ETF gross returns remain positive. The family is an M2 instance exactly for

```
x in J=(alpha_min,infinity),
alpha_min = max_{h,s} [-1-B^A lambda_h-alpha_h+bar alpha_0-xi_A,s].
```

The maximum is over all specified support points and scenarios, including zero-mass ones,
since M2 imposes positivity there too. J is nonempty and contains bar alpha_0. Define the
same affine-quadratic score for all real x as an algebraic extension; values outside J are
not M2 instances. In this extension the mean vector is
`mu(x)=(B^A bar lambda+x, B^E bar lambda-c^E)`.

Let C be the set of real x for which some full-class maximizer has a=a^-. This is an
existence definition: when optima tie, it does not assert that every maximizer avoids an
active trade. The M2 no-active-trade set is C intersect J. E and F use the same original
cost and cash functions; neither class depends on x.

The set of E maximizers is nonempty and independent of x. Choose any one such holding
`w_E=(a^-,p_E)` once and for all. Every such choice gives the same C by the formulas below.
Write k_E=k(w_E) and

```
g_E,j = mu_E,j - gamma (Sigma w_E)_E,j,
alpha_c = gamma (Sigma w_E)_A - B^A bar lambda,
g_A(x) = x-alpha_c.
```

### Compatible budget multipliers from the ETF coordinates

For each ETF j set the cost-slope endpoints at its trade as follows:

| Trade at w_E | ell_j | u_j |
|---|---|---|
| p_E,j > p^-_j | kappa^+_E,j | kappa^+_E,j |
| p_E,j < p^-_j | -kappa^-_E,j | -kappa^-_E,j |
| p_E,j = p^-_j | -kappa^-_E,j | kappa^+_E,j |

Define I to be the set of eta>=0 such that eta*k_E=0 and the following inequalities hold:

```
g_E,j <= u_j + (1+u_j) eta     whenever p_E,j < bar p_j,
g_E,j >= ell_j + (1+ell_j) eta whenever p_E,j > 0.
```

If bar p_j=0 neither condition is imposed. Thus fixed ETF coordinates create no false
stationarity equality. All denominators 1+ell_j and 1+u_j are positive.

I is a nonempty closed interval with a finite attained lower endpoint lo>=0. Its upper
endpoint hi may be infinity. It is explicitly computable without an additional optimization:
if k_E>0, I={0}; otherwise

```
lo = max( {0} union {(g_E,j-u_j)/(1+u_j) : p_E,j < bar p_j} ),
hi = min( {(g_E,j-ell_j)/(1+ell_j) : p_E,j > 0} ),
```

where min of the empty set is infinity. I is [lo,hi] if hi is finite and [lo,infinity)
otherwise. If a^-<1, hi is finite. It need not be finite when a^-=1.

### The band and the marginal condition

Put b=kappa^+_A and s=kappa^-_A, and define

```
L = alpha_c - s + (1-s) lo,
U = alpha_c + b + (1+b) hi       when hi is finite.
```

Then the exact extended-score no-active-trade set is:

| Initial active position | C |
|---|---|
| 0<a^-<bar a | [L,U], with both endpoints finite |
| a^-=0<bar a | (-infinity,U], with U finite |
| 0<a^-=bar a | [L,infinity), whether or not hi is finite |
| a^-=bar a=0 | all real numbers |

In the interior case its width is exactly

```
U-L = b(1+hi) + s(1+lo) + (hi-lo).
```

For a given x, the equivalent marginal condition is that there exists eta in I and an
active cost slope t_A in [-s,b] such that
`g_A(x)-eta-(1+eta)t_A` is zero at an interior active position, nonpositive at a lower
bound only, nonnegative at an upper bound only, and unrestricted when bar a=0.
These signs apply to holdings bounds, not to trade signs. They are necessary and sufficient
for w_E to be globally F-optimal, not merely locally stationary.

For actual M2 instances intersect the table with J. That intersection can be empty or have
an open endpoint and need not have the displayed full width. A closed bounded interval in
the whole real line is asserted only for the algebraic interior case, not universally in M2.

If gamma>0 and Sigma is positive definite, E and F each have a unique maximizer for every
x, so C intersect J characterizes when the implemented unique optimum leaves the active
holding unchanged. Without such a strictness condition, uniqueness is not guaranteed and
the existence interpretation above is essential. This is a sufficient uniqueness condition,
not an asserted necessary one.

## Proof

### Positivity, attainment and the alpha-independent ETF problem

Only the active conditional mean changes under the support translation. Its gross return
at (h,s) is `1+B^A lambda_h+alpha_h-bar alpha_0+x+xi_A,s`. Strict positivity of every
one of these finitely many quantities is precisely x>alpha_min. The original instance
satisfies it at x=bar alpha_0, and the other M2 restrictions are unchanged.

The score at any holding changes by `(x-y)a` between x and y. In E, a=a^- is fixed,
so all E rankings and the entire maximizer set are unchanged. Claim 004 gives nonempty
compact F and E and attainment at the original instance. The feasible sets do not change;
for every real x the extended score is still a continuous function on these sets, so the
same compactness/attainment proof applies, even outside the return-positive domain. No
positive-gross-return inference is made about that extension. Claim 003 gives the stated
belief-mean representation; no predictive variance is added.

If some F maximizer belongs to E, its value equals the E maximum. Hence every E maximizer
is F-optimal. Conversely if the chosen w_E is F-optimal, it witnesses the definition of C.
This proves that characterizing optimality of any fixed w_E characterizes C independently
of the choice among E ties.

### An elementary finite-inequality optimality argument

We prove the multiplier criterion used here rather than assume a constraint qualification
or an external KKT theorem. First consider a differentiable concave quadratic f on a
nonempty polyhedron `{y: v_i'y<=d_i, i=1,...,r}`. At a maximizer y_0 its gradient is a
nonnegative combination of the normals v_i of the tight inequalities.

Here is a finite-dimensional proof. The cone of nonnegative combinations of finitely many
vectors is closed: any combination can be represented by a linearly independent subfamily.
Indeed, if its positive-coefficient vectors are dependent, take a nonzero linear relation,
change its sign so some coefficient is positive, and subtract the largest nonnegative
multiple that keeps all combination coefficients nonnegative. At least one coefficient
becomes zero without changing the represented vector. Repeating proves the reduction.
For each independent subfamily its coefficient map has a continuous inverse on its image
(use an invertible coordinate minor), so its nonnegative cone is closed. There are finitely
many such subfamilies, and their union is closed.

Let K be the cone generated by the tight normals. If g=grad f(y_0) were outside K, choose
a closest z in K. Such z exists: a minimizing sequence can be taken bounded, since 0 is
in K and its distance to g is finite; a coordinatewise convergent subsequence, as in claim
004's finite-box argument, has its limit in the closed K. For d=g-z, minimizing along
every segment from z toward v in K gives `d'(v-z)<=0`. Taking v=0 and v=2z gives d'z=0.
Thus d'v<=0 for every v in K, while d'g=||d||^2>0. In particular v_i'd<=0 for each tight
normal. Finitely many strictly slack inequalities remain satisfied by y_0+t*d for all
sufficiently small t>0. This is a feasible improving direction, since the derivative is
g'd>0, contradicting optimality. Therefore g belongs to K. Conversely, such a combination
implies `g'(y-y_0)<=0` for every feasible y. The concave quadratic expansion then gives
f(y)<=f(y_0), so the condition is sufficient too. A zero-width coordinate box simply
contributes both opposite bound normals; no strict feasible point was used.

Apply this fact by introducing a scalar y_cost and writing switching cost as a maximum of
finitely many affine forms. For each choice of one endpoint
`c_i in {-kappa^-_i,kappa^+_i}` per instrument, impose

```
c'(w-w^-) <= y_cost,
sum_i w_i + y_cost <= 1,
0 <= w_i <= bar w_i.
```

The maximum of those affine forms is exactly tau(w-w^-), since each coordinate can choose
its maximizing endpoint separately. The lifted differentiable concave objective is
`mu'w-(gamma/2)w'Sigma w-y_cost`. At any optimum y_cost=tau: lowering excess y_cost improves
the objective and relaxes the budget. Each feasible original holding has that lift, so the
lifted and original optimization problems have exactly the same optimal holdings.

Write eta>=0 for the multiplier on the budget inequality and beta_c>=0 for the tight cost
inequalities. The y_cost component of the gradient identity gives
`-1=eta-sum_c beta_c`, hence sum_c beta_c=1+eta. Let
`t=sum_c beta_c*c/(1+eta)`. It is a convex combination of tight cost slopes. Coordinatewise
it equals kappa^+ at a purchase, -kappa^- at a sale, and belongs to [-kappa^-,kappa^+] at
a zero trade. Conversely every such vector is a convex combination of tight slope vectors:
choose endpoint weights separately at each zero-trade coordinate and take their products;
at a nonzero trade choose its maximizing endpoint. Coincident endpoints cause no difficulty.

Writing g=mu-gamma*Sigma*w, the w components of the gradient identity give

```
R_i = g_i-eta-(1+eta)t_i,
eta>=0, eta*k(w)=0.
```

The residual R is a combination of tight position-bound normals. Thus it is <=0 at a
lower bound only, >=0 at an upper bound only, zero at an interior coordinate, and arbitrary
at a coordinate fixed by a zero-width box. These conditions are necessary.

For completeness, they are sufficient directly in the original holdings. The coordinate
slope conditions imply the cost inequality `tau(z-w^-)-tau(w-w^-)>=t'(z-w)` for every z
(by the two linear pieces of each absolute-direction cost). Write this cost difference as
Delta_tau. The exact quadratic expansion gives

```
Q(z)-Q(w) = g'(z-w) - (gamma/2)(z-w)'Sigma(z-w) - Delta_tau
 <= R'(z-w) - (gamma/2)(z-w)'Sigma(z-w)
       + eta [sum_i z_i+tau(z-w^-) - sum_i w_i-tau(w-w^-)]
 <= 0
```

for every feasible z. The first bound has nonnegative slack
`(1+eta)(Delta_tau-t'(z-w))`. For the last inequality, the position signs give R'(z-w)<=0,
Sigma is positive semidefinite (its finite second-moment definition), and the budget term
is <=0 if eta>0 by complementarity, and zero if eta=0. This proves global sufficiency.

Exactly the same lifted proof applies to E after eliminating the fixed active coordinate.
Its active cost is zero, its smooth ETF gradient is g_E, and the budget right side is
1-a^-. Coordinates with bar p_j=0 may either be retained with their two bounds or eliminated.
Hence the ETF signs with some common eta and slopes t_j are necessary and sufficient for
E optimality, even if E is a singleton or has no strictly feasible point.

### Eliminating the ETF slopes and bounding the multiplier interval

For fixed eta>=0, the possible values of `eta+(1+eta)t_j` fill
`[ell_j+(1+ell_j)eta, u_j+(1+u_j)eta]`. At a lower bound only, the residual need only be
nonpositive, so its upper endpoint must be at least g_E,j. At an upper bound only, the
lower endpoint must be at most g_E,j. An interior holding imposes both requirements; a
zero-width coordinate imposes neither. This proves exactly the inequalities defining I.
Choices of slopes at distinct coordinates are independent, as the product-weight argument
shows. The E optimality result proves I nonempty; it does not assume the answer by defining
an admissible multiplier to exist.

Because all rates are below one, 1+ell_j and 1+u_j are strictly positive. Solving the
inequalities for eta gives the displayed finite list of lower and upper bounds. If k_E>0,
complementarity leaves eta=0, which satisfies all of them by nonemptiness. If k_E=0, the
lower endpoint is a maximum of a finite nonempty list of real numbers and the upper endpoint
is either the minimum of a finite list or infinity. Nonemptiness ensures lo<=hi. This proves
closedness, endpoint attainment when finite, and the formulas without a Slater hypothesis.

To prove finiteness when a^-<1, only the case k_E=0 needs attention. If all p_E,j=0,
the cost is `sum_j kappa^-_E,j p^-_j`. If any initial ETF holding is positive, that cost
is strictly less than sum_j p^-_j because every sale rate is below one; therefore
`a^-+tau < a^-+sum_j p^-_j <= 1`, contradicting k_E=0. If all initial ETF holdings are
zero, the cost is zero and a^-<1 again contradicts k_E=0. Thus some p_E,j>0. That coordinate
supplies a finite upper bound `(g_E,j-ell_j)/(1+ell_j)` on eta, proving hi finite.

### Eliminating the active slope and taking the union

At w_E the active trade is zero, so its slope interval is [-s,b]. Its smooth marginal is
x-alpha_c. At an interior active holding, for fixed eta in I the full optimality condition is

```
alpha_c-s+(1-s)eta <= x <= alpha_c+b+(1+b)eta.
```

Both endpoints increase with eta, since s<1. The lower endpoint never exceeds the upper:
their difference is (s+b)(1+eta)>=0. Here a^-<bar a<=1 implies a^-<1, so I has finite
endpoints. All allowable x lie in [L,U], and both L and U are realized, at lo and hi
respectively. Every intermediate value is realized too: the set of pairs (eta,x) satisfying
these two linear inequalities and lo<=eta<=hi is convex. The segment between (lo,L) and
(hi,U) lies in it and its x coordinate traverses [L,U]. This argument also covers a collapsed
I or a zero-width band. Subtracting L from U gives the stated width formula.

At a lower active bound only, the condition is
`x<=alpha_c+b+(1+b)eta`. Here a^-=0<1 ensures finite hi; taking the union over eta in I
gives (-infinity,U]. At an upper active bound only, the condition is
`x>=alpha_c-s+(1-s)eta`; the attained smallest eta=lo gives precisely [L,infinity),
regardless of whether hi is finite. When bar a=0, the active coordinate cannot move,
F=E, and C is all real numbers. These prove the table and the marginal characterization.
Intersecting with J enforces exactly the original positivity requirement.

### Uniqueness and the limits of the unqualified candidate

For distinct w,z, a strictly positive gamma and positive definite Sigma give

```
Q(t*w+(1-t)*z) - t*Q(w) - (1-t)*Q(z)
  >= (gamma/2)*t*(1-t)*(w-z)'Sigma(w-z) > 0,   0<t<1,
```

because switching cost is convex. Two distinct maximizers on a convex class would contradict
this strict inequality. Claim 004 supplies convexity and attainment, proving the sufficient
uniqueness statement for E and F.

Uniqueness and universally finite hi are false in unrestricted M2. Two exact counterexamples
use one ETF, zero loadings, zero shocks, gamma=0, zero costs, unit limits, and singleton
support (lambda_1,lambda_2,alpha)=(0,0,x), with J=(-1,infinity). Scores are simply x*a.
Starting at (a^-,p^-,k^-)=(1/2,1/2,0), at x=0 every funded holding is optimal. The E
optimizer can be chosen with p_E=1/2; I={0}, alpha_c=0 and C={0}. Thus a no-active-trade
optimum need not be the only full optimum. Starting instead at (1,0,0), E is a singleton
and I=[0,infinity), since its only ETF inequality is 0<=eta. Yet C=[0,infinity): for x>=0
the incumbent is optimal, and for x<0 all cash strictly improves it. These instances satisfy
all M2 restrictions on J and show why the qualifications cannot be omitted.

## Checks

`uv run python checks/009/check.py` checks fixed exact instances against direct one-ETF
piecewise quadratic optimization, independently of the multiplier interval calculation.
It covers an interval of compatible multipliers, boundary active positions, zero-width ETF
boxes, a slack budget, a binding budget with zero multiplier, nonunique optima and an
unbounded compatible interval. All inputs are assumed. No random search or empirical result
is reported; these finite checks supplement the proof and do not prove the general claim.

`uv run python checks/t3-band-correction/check.py` is the previously committed independent
check of the two rational positive-definite cases in FINDINGS. It confirms the corrected
sale-cost sign and a tight budget with zero multiplier. Experiment 005's old T3 claim remains
withdrawn; no count from its search is a premise of this proof.

## Not shown

The originally unqualified candidate is not a theorem: uniqueness fails without strictness,
hi can be infinite at a fully invested active incumbent, active position bounds produce rays,
and the open positivity domain can cut off an endpoint. The corrected result states every
case and uses existence of a no-active-trade maximizer when ties remain. It does not silently
choose a tie-breaking rule or imply uniqueness from a numerical solver.

For an interior active position with lo=hi=eta the width is (b+s)(1+eta). A slack cash
constraint forces eta=0 and hence width b+s, but a tight budget can have eta=0 as well.
ETF kinks or bounds can permit hi>lo, giving an additional width contribution. A traded ETF
pins eta by an equality only when its holding is strictly within its position limits.
These are statements about the full extended-score interval; clipping to J can change width.

The marginal alpha centering value is `gamma*(Sigma w_E)_A-B^A bar lambda`. Risk, factor
mean, cost and budget terms are visible, but separating alpha from factor premium here is an
accounting decomposition of mu, not a new structural decision effect. Claim 003 still rules
out an effect of belief dispersion or dependence at fixed means. This family shifts the
belief mean while preserving its centered support; it introduces neither estimation-error
penalties nor ambiguity aversion. There is no continuation value, interim trading or learning.

No general monotonicity in factor premia, ETF menu size or a changing position limit follows:
w_E and I change when those inputs change. The counterexamples in experiment 005 and claim
007 are not contradicted. Rates, covariances and example inputs are assumed, not calibrated;
there is no materiality or inference claim. M2 is unchanged and all proposal section 2
commitments remain. Stage 2 requires a new model and a reviewed stage-1 claim.

## Prior art

Read M2, claims 003-004, FINDINGS' D2 candidate and its listed obligations, experiment 005's
withdrawn band conclusion, and the empty refuted-claim registry. Re-read the registered full
texts `bichuch2014investing`, section 2.3, Theorem 2.2(iii), and `gallien2018hedge`, sections
3 and 5, Proposition 1 and equations (5)-(7). Also read the newly registered full text
`liu2013portfolio`, section 2, Theorem 2.3(iii)-(iv), (vii), and Lemma 5.2, as required
by the updated D2 kill criterion. No literature theorem is imported or assumed.

The first source describes continuous-time, long-horizon CRRA optimal boundaries in the
illiquid holding weight, with a freely traded liquid risky asset. The second describes an
approximately optimal small-cost band in illiquid shares, with continuous liquid futures
hedging and a terminal wealth floor; its half-width has a cube-root small-cost expression.
Their bands vary the holding state and include dynamic risk/hedging effects. This claim
instead fixes the incumbent and solves exactly for the range of a conditional mean in a
one-review funded long-only quadratic problem, with directional rates, position limits and
ETF cost kinks. It is not a discretization, a limit theorem, or a restatement of either
source's width. Neither comparison establishes a new structural role for alpha uncertainty.

`liu2013portfolio` is the closer constraint precedent. Its investor has one risky asset,
one safe asset, fixed known drift and volatility, an infinite-horizon CRRA equivalent-safe-rate
objective, and a binding cap on the risky weight. Theorem 2.3(iii) gives a selling boundary
at that cap and a buying boundary equal to the cap times one minus a transaction-cost gap.
Part (iv) and Lemma 5.2 determine that gap through an ODE terminal condition; part (vii)
gives a square-root small-spread leading width under its nondegenerate binding-cap assumptions.
Thus the qualitative mechanism of a separate constraint reshaping a no-trade width is
already present in the literature and is not a contribution claimed here.

The source's gap parameter is called lambda, distinct from M2's factor premium and from
this claim's cash multiplier eta. Its shadow-price construction is not an identification
of that gap with the interval I. This claim fixes the incumbent and varies a belief-mean
alpha, uses an exact one-review quadratic score rather than a long-run utility rate, and
eliminates ETF cost slopes under one funded budget with position boxes and directional
rates. The source has no optimized ETF comparator, compatible interval of ETF budget
multipliers, or the four alpha-domain cases stated here. These differences prevent a direct
application of the cited theorem as this proof; they do not by themselves establish novelty.
The precise ETF-compatible interval and its boundary cases are the result to assess against
the precedent, not a purported first observation that constraints affect no-trade widths.

The finite multiplier argument is elementary polyhedral concave optimization, proved here
rather than credited as novel. Its explicit consequence is the budget- and ETF-dependent
width and the precise boundary cases, answering D2 stage 1's constraint question. This is
not a novelty claim for KKT conditions or for no-trade regions. PM must still assess D2's
kill criterion; no claim is made that one such calculation meets the direction's wider
structural or dynamic ambitions. No new web search was performed.

## Open objections

None recorded; independent review is pending.

## Review

Red, 2026-09-27. Re-derived independently. This claim proves, with every boundary case, the band red found numerically in experiment 005. Red's earlier note left necessity unproved; this file supplies it.

**Proof checked line by line.**
- *The cost lift.* The maximum of the 2^d affine forms c'(w - w^-) equals tau, coordinatewise.
- *The multipliers.* The y_cost component of the gradient identity gives sum beta_c = 1 + eta. Normalizing, t is a convex combination of tight slopes, so t_i = kappa^+_i at a purchase, -kappa^-_i at a sale, and anything in [-kappa^-_i, kappa^+_i] at no trade.
- *Necessity without a constraint qualification.* After the lift every constraint is linear. The finite-cone argument (closedness by reduction to independent subfamilies, a nearest point, and an improving direction) is correct, so no Slater point is needed. This closes the necessity gap in red's experiment 005 note.
- *Sufficiency.* Same inequality chain as claim 007: the cost subgradient slack, then the budget term, which is <= 0 by complementarity.
- *Eliminating the ETF slopes gives I.* The endpoints are right, including zero-width boxes (bar p_j = 0), which impose nothing.
- *Finiteness of hi when a^- < 1.* The case split is correct: if every ETF sits at zero with no cash, then either sales raised cash, because kappa^- < 1, or there was nothing to sell. Either way k_E > 0.
- *The active band.* The condition is x - alpha_c in [-s + (1 - s) eta, b + (1 + b) eta], with both ends increasing in eta, so the union over eta in [lo, hi] is [L, U]. The ray cases follow from the one-sided sign conditions at the active bounds.
- *The width.* b(1 + hi) + s(1 + lo) + (hi - lo), with math's corrected sale-cost sign.

**Independent check against the exact solver.** Red implemented the Statement's formulas literally: w_E, I, alpha_c, L, U and the four-row table. They were tested on 250 random M2 instances, which include:
- n in {1, 2};
- random directional rates up to 1%, and signed drag;
- fully invested starts and starts with no active incumbent;
- ETF caps, including zero-width boxes, and active caps equal to a^-.

The instances fell into all four cases: 104 interior, 43 at the active lower bound, 76 at the active upper bound and 27 with the active position fixed. Every instance has gamma > 0 and positive definite Sigma, so the full optimum is unique. On each, the experiment 004 solver was run at the exact finite endpoints, where it must give a* = a^-, and at the endpoints plus or minus 1e-12 outside them, where it must not. For rays and the fixed case red used interior probe points instead. Every returned optimum carries red's own exact directional KKT certificate.

There were zero disagreements, and no instance with a^- < 1 had hi infinite. The two degenerate counterexamples check by hand. With (1/2, 1/2, 0), choosing p_E = 1/2 gives I = {0}, L = U = 0 and C = {0}; choosing p_E = 0 gives k_E > 0 and the same C. With (1, 0, 0), E is a singleton, hi is infinite and C = [0, infinity).

**Attacks tried.**
(i) *A marginal condition without the budget multiplier* (red's FINDINGS requirement (i)): no. The condition carries eta, and the width depends on it.
(ii) *A scalar threshold claimed for a multidimensional boundary*: no. The band is in one scalar (the belief-mean alpha) with everything else fixed. The claim states that w_E and I move when premia, menus or limits change, and asserts no monotonicity. So it is consistent with experiment 005 T1 and T2 and with claim 007.
(iii) *Uniqueness from a solver*: no. The existence definition of C is kept, and uniqueness is proved only under gamma > 0 with positive definite Sigma.
(iv) *Positivity domain*: J is handled by intersecting, and the extended score outside J is labelled algebraic only.
(v) *Alpha/premium relabelling*: alpha_c is stated to be an accounting decomposition with no structural decision effect, consistent with claim 003 and red's FINDINGS.

**Scope.** This is a one-review result with no continuation value; the prior-art comparison with `bichuch2014investing` and `gallien2018hedge` is accurate about what differs. It answers D2 stage 1's constraint question exactly: the band's width is the active fund's costs scaled by (1 + budget multiplier), plus the ETF-kink term hi - lo. It is not the dynamic boundary D2 ultimately targets.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* In a convex program with a kinked linear cost, the range of a linear parameter over which a coordinate stays at its kink is the set of gradients compatible with that kink's subdifferential, shifted by the compatible multipliers of the other active constraints.
- *General result.* Subdifferential (KKT) optimality for concave maximization over a polyhedron, 0 in -∂Q(w*) + N_F(w*), combined with parametric ranging, the "range of optimality" of a fixed solution. When the parameter enters one coordinate's gradient linearly, the range is an interval whose endpoints add the cost slopes to the extreme compatible multipliers, which gives the kink width plus a multiplier-interval term. The qualitative point, that a constraint's shadow price reshapes a no-trade width, is in liu2013portfolio (registered).
- *Reduction.* M2's score is concave, affine in alpha, and alpha enters only the active coordinate's gradient. The feasible set is polyhedral after splitting trades into parts, so the hypotheses hold and the band is the ranging interval at the ETF-only optimum.
- *Verdict: special case of subdifferential optimality with parametric ranging.* Left over: the explicit closed-form multiplier interval [lo, hi] for M2's funded problem, and its four boundary cases. That is a computation, not a mechanism.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's line-by-line check (cost lift, constraint-qualification-free finite-cone necessity, sufficiency, multiplier interval, finiteness of hi, union over eta), exact solver test on 250 instances across all four boundary cases and attacks (missing multiplier, scalar-threshold overreach, solver uniqueness, positivity domain, alpha relabelling) are sound and match PM's rerun of checks/009 and own CLARABEL test of the band endpoints on 50 two-ETF interior instances; no open objections. Limits stated: one quarter, no continuation value; the alpha/premium split in alpha_c is accounting only; no monotonicity; the qualitative mechanism (a separate constraint reshaping a no-trade width) is already in liu2013portfolio, so the claimed content is the exact ETF-multiplier interval and its boundary cases, which PM weighs against D2's kill criterion.


Not machine checked. The target is the finite deterministic result including the piecewise
linear cost lift, the necessary and sufficient multiplier criterion without strict feasibility,
the interval and finiteness formulas, boundary cases, alpha-domain clipping, and the stated
uniqueness implication and counterexamples. The finite-cone argument is a proof obligation,
not a permitted unproved hypothesis equivalent to multiplier existence. The comparison to
continuous-time sources and the interpretation of alpha as accounting are prose limitations.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2NoActiveTradeBand.lean` and the
proof in `lean/Novel/M2NoActiveTradeBandProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used.

Setting. Any M2 instance with one active fund and n ETFs (claim 003's formal objects), any number
of factors, any finite scenario set and any finite support. M2's n in {1, 2} is a special case.
The hypotheses used are the compliant start, rates in [0, 1), limits at most one, gamma >= 0,
nonnegative scenario masses summing to one, and belief masses summing to one. Not assumed:
positive gross returns (except where the alpha-family part names them), centered shocks,
nonnegative belief masses, strict feasibility, positive definiteness and uniqueness.

Definitions. The following are defined literally from the Statement: the translated-alpha family,
its criterion for every real x, J, alpha_min's terms, C (by existence of a no-active-trade
F-maximizer), g_E, alpha_c, ell_j, u_j, I, lo (0 if k_E > 0, otherwise the maximum of
{0} ∪ {(g_E,j - u_j)/(1 + u_j) : p_E,j < bar p_j}), hi (0 if k_E > 0, otherwise the minimum of
{(g_E,j - ell_j)/(1 + ell_j) : p_E,j > 0}, finite exactly when k_E > 0 or that set is nonempty),
and L and U.

Proved:
- the family's belief-mean alpha is x; ETF returns are unchanged; J = {x > alpha_min}, with
  alpha_min attained; bar alpha_0 is in J; every gross return is positive on J;
- E- and F-maximizers exist for every real x, and the E-maximizers do not depend on x;
- for any E-maximizer w_E, x is in C iff w_E is F-optimal;
- I = [lo, hi] when hi is finite and [lo, infinity) otherwise; lo is in I; I = {0} when k_E > 0;
  hi is finite when a^- < 1;
- all four rows of the table, and the interior width;
- the marginal condition, necessary and sufficient;
- a unique E- and F-maximizer when gamma > 0 and Sigma is positive definite (v' Sigma v > 0 for
  v != 0);
- both counterexamples as stated, including their setting and J = (-1, infinity).

The proof differs from the paper's. Sufficiency is the paper's certificate inequality. Necessity
is proved by elementary feasible moves instead of the lifted-cost finite-cone argument. Each bound
in I and in the band is one move from w_E whose one-sided derivative would otherwise be positive:
- for I: buy an ETF from slack cash; sell an ETF into cash; swap one ETF for another;
- for the band: buy the active fund from cash or with an ETF sale; sell it into cash or into an
  ETF.
Along each move the piecewise-linear cost is exactly linear for small steps, the step stays
funded and within bounds, and the quadratic term is second order, so a small step strictly
improves. No constraint qualification or cone-closedness lemma is used. The lifted problem and the
finite-cone lemma, which red checked, are therefore not themselves machine checked; the
conclusions they were used for are.

Relation to the prose. The instruction to intersect the table with J for actual M2 instances is
commentary: the formal table is stated for the extended criterion, and J is characterized
separately. Red's remark that choosing p_E = 0 in the first counterexample gives the same C is
not formalized; the Statement's choice p_E = 1/2 is. The `liu2013portfolio` comparison in Prior art
is prose and has no formal counterpart. No gap was found between the formal statement and the
Statement. The limits PM recorded at approval apply unchanged.

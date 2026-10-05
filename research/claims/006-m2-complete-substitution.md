---
id: 006
title: "Complete feasible exposure substitution need not eliminate an active-trading advantage"
status: formalized
model_version: M2
depends_on: [003, 005]
axioms_used: []
formal: lean/Standalone/M2CompleteSubstitution.lean
direction: D1
---
## Statement

This is one fully specified, assumed M2 example. It establishes no calibrated magnitude or
novel general allocation rule. There is one active fund and one ETF, K=2, T=1, W^-=1,
initial holdings (a^-,p^-)=(0,0), initial cash k^-=1 and both position limits equal to one.
The eligible instruments have fixed identical loading rows B^A=B^E=(1,0). ETF drag is zero.
All purchase and sale cost rates, for both instruments, are 1/100 on M2's gross changes in
holdings; gamma=1. Costs are assumed equal, not measured. Cash earns gross return one.

The parameter support has the following two points, each of belief mass 1/2:

| Point | lambda_1 | lambda_2 | alpha |
|---|---|---|---|
| First | 1/100 | 0 | 0 |
| Second | 3/100 | 0 | 1/50 |

There are two scenarios, each of mass 1/2, with factor shocks (1/10,0) and (-1/10,0).
Active and ETF residual shocks are zero. This scenario law is independent of the parameter
and of the action. All inputs are available at the decision date; the action uses the given
belief, not knowledge of which parameter point or scenario is realized. No interim trading
or terminal liquidation is imposed.

Write t=a+p for total normalized risky holdings in this example. Then

```
F = {(a,p) : a>=0, p>=0, a+p<=100/101},
E = {(0,p) : 0<=p<=100/101},
N = {(0,0)},
b(a,p) = (t,0),
B_E = D_E = {(t,0) : 0<=t<=100/101}.
```

There is complete feasible exposure substitution: for every (a,p) in F the ETF-only
holding (0,a+p) belongs to E and has identical exposure, conditional variance, review cost
and post-review cash. No position, funding or span restriction blocks this replacement.
The missing second-factor direction lies outside the span of both the ETF and active
loadings; it is not an active fund exposure needing substitution here.

The belief-average conditional score and its matched difference are

```
Qbar_0(a,p) = t/100 + a/100 - t^2/200,
Qbar_0(a,p) - Qbar_0(0,t) = a/100.
```

The unique maximizers and attained scores are:

| Class | Optimal (a,p) | Cash | Review cost | Score |
|---|---|---|---|---|
| N | (0,0) | 1 | 0 | 0 |
| E | (0,100/101) | 0 | 1/101 | 51/10201 |
| F | (100/101,0) | 0 | 1/101 | 152/10201 |

Thus the full-minus-ETF-only optimal score gap is 1/101 > 0, despite complete feasible
exposure substitution. The two optima have the same factor exposure. The gap is attributable
to the assumed positive belief-mean alpha in this instance: risk, cash and review costs
agree at every matched pair. It is a one-quarter score gap, not a realized or multiperiod
wealth advantage.

## Proof

First verify the chosen data satisfy M2. Initial positions and cash are nonnegative, sum to
one and meet the position limits. Every cost rate is in [0,1). The scenario and belief masses
are nonnegative and sum to one. Factor shocks have zero scenario mean, and all residual
shocks vanish. The smallest possible instrument excess return is 1/100-1/10=-9/100;
the smallest gross return is therefore 91/100>0. This verifies positivity at every parameter
and scenario. The fixed scenario law has no action or parameter dependence. The covariance
is singular, which M2 permits: both instruments' centered return shocks equal the same
first-factor shock, so every entry of Sigma is 1/100.

Every admissible holding has a,p>=0 and starts from zero. Hence both trades are purchases,
and M2's cost is tau=(a+p)/100=t/100. The shared cash function is

```
k(a,p)=1-a-p-tau=1-(101/100)t.
```

Nonnegative cash is exactly t<=100/101. Together with a,p>=0 this already implies a,p<1,
so both individual upper bounds hold. Conversely each point in the displayed F obeys all
of M2's position and cash restrictions. This proves the exact description of F, and fixing
a=a^-=0 gives E; no trade is the singleton N.

Identical loadings give b(a,p)=(a+p,0). For any point in F, the holding (0,t) is nonnegative
and obeys t<=100/101, so it belongs to E. It has exactly the same t, hence the same exposure,
review cost t/100 and cash 1-(101/100)t. Claim 005's one-ETF interval also gives
P_E=[0,min(1,1/(1+1/100))]=[0,100/101], since p^-=0 and k^-=1. Applying its image
formula and using b(w^-)=(0,0) gives the asserted B_E and D_E. L_E is the first-coordinate
line; B^A lies on it as well. This explicitly checks feasibility, not just span membership.

The covariance computed above gives w'Sigma w=t^2/100, identical at a matched pair.
By finite belief averaging (claim 003), bar lambda=(1/50,0) and bar alpha=1/100. Substituting
in M2's conditional-score average, with gamma=1, gives

```
Qbar_0(a,p)=t/50+a/100-t^2/200-t/100=t/100+a/100-t^2/200.
```

Subtracting the same expression at (0,t) gives a/100. This calculation uses the conditional
scenario variance. It adds no variance of the conditional means across the belief.
At the first parameter point the conditional matched difference is zero; at the second it
is a/50. Their average is a/100, so the positive comparison does not assume the second
parameter point is known to be true.

To establish the maxima and uniqueness directly, consider E first. Its score at (0,t) is
t/100-t^2/200 for 0<=t<=100/101. For 0<=s<t<=100/101 its increase is

```
(t-s)[1/100-(t+s)/200] > 0,
```

because t+s<2. Thus its unique maximizer is t=100/101. In F, for any fixed t the only
composition-dependent term is a/100; since 0<=a<=t this is uniquely maximized at a=t,
p=0 (also the only possibility when t=0). The resulting score is t/50-t^2/200. Its increase
from s to t is

```
(t-s)[1/50-(t+s)/200] > 0,
```

again because t+s<2. Thus the unique full optimum has a=t=100/101 and p=0. This does not
infer uniqueness from strict concavity of the whole score, which fails in some directions;
it proves uniqueness from the composition comparison and strict increase in total holdings.
The singleton N has its stated unique holding and zero score.

At t=100/101, cost=t/100=1/101 and cash is zero. Substitution yields

```
Qbar_0(0,100/101)=1/101-50/10201=51/10201,
Qbar_0(100/101,0)=2/101-50/10201=152/10201.
```

Subtracting gives 101/10201=1/101. The full and ETF-only optima both have exposure
(100/101,0), completing the matched and optimized comparisons.

## Checks

`checks/006/check.py` independently computes conditional scores from marked terminal wealth
on the stated finite scenarios, then averages over the two parameter points. It checks the
optimal-point values and several feasible matched pairs in exact rational arithmetic.
It is a finite check, not a proof of the statements quantified over all holdings. The code
is committed before running; the complete algebraic proof above supplies those statements.

## Not shown

This is a supporting example, not a novelty claim or an empirical finding. All costs, means,
beliefs and risks are assumed; neither the size nor the existence of this score gap is
claimed to be realistic. It does not establish the economic-materiality part of D1's question
or satisfy D1's kill criterion, which requires the analyst's realistic-parameter comparison.

Complete substitution here concerns factor exposure. Conditional expected returns and terminal
wealth are not generally identical because alpha differs across the parameter points. This
is not the zero-alpha return-replication limiting case; that is a separate D1 stage. The
second factor is unused, residual risk is zero, the initial portfolio is all cash and the
covariance is singular. No assertion transfers this example to general initial holdings,
unequal trading costs, binding ETF limits, nonzero residual risk or another model version.

The positive average alpha is a decision-date assumption, not an eligibility filter using
future outcomes. The example gives no dependence on belief dispersion or correlation at
fixed means, confidence guarantee, ambiguity preference or continuation value. It includes
the review cost once, no terminal exit cost, and relaxes no proposal section 2 commitment.

## Prior art

Read the current M2 definition, claims 003 and 005, board/FINDINGS.md and the experiment
statuses; claims/refuted/ is empty. Experiment 005 is marked failed on its T3 conclusion,
with T1 and T2 reproduced; no part of that experiment is a premise of this new assumed example.
The registered passages in `bichuch2014investing` (sections 2.1-2.2), `gallien2018hedge`
(section 2) and `garleanu2009dynamic` (equations 3-4) were previously inspected for the D1
accounting and limiting-case work. They are background only here; no literature theorem
or numerical result is imported. No new web search is claimed. Identical exposures with
different mean alpha naturally give different scores: this standard distinction is what
the complete-substitution example makes explicit under one funded budget and equal costs.

## Open objections

None recorded; independent review is pending.

## Review

Red, 2026-09-27. Re-derived independently.

**Independent exact check**, with red's own code rather than `checks/006/check.py`.
- Scores come from M2's marked terminal wealth: E_q G - (gamma/2) Var_q G at each parameter point, averaged over the belief. Red's code does not use the claim's formula.
- The minimum gross return is 91/100.
- Both optima are feasible with zero cash, and each is proved optimal by red's exact KKT certificate with directional subdifferentials, as in red's experiment 004 reproduction. The certificate uses the belief-mean mu = (3/100, 2/100) and Sigma = (1/100) x all-ones.
- Scores: N 0, E 51/10201, F 152/10201, gap 1/101.
- On 2,000 random feasible points: the score equals t/100 + a/100 - t^2/200; the matched difference with (0, t) is exactly a/100 at equal cash; and no point beats the F optimum.

By hand: bar lambda_1 = 1/50 and bar alpha = 1/100 give mu_A = 3/100 and mu_E = 1/50, and the budget gives t <= 100/101. The two strict-increase comparisons in the uniqueness proof are correct, because t + s < 2. The composition argument (a/100 is maximized at a = t) correctly replaces strict concavity, which fails along the singular direction.

**Attacks tried.**
(i) *Unequal funding or cost across classes* (red's FINDINGS requirement (i)): no. The same budget applies throughout; purchases from all-cash cost t/100 in both classes; the matched pair has identical cash, cost, exposure and variance.
(ii) *Span read as feasibility*: no. Substitution is checked through claim 005's one-ETF interval, P_E = [0, 100/101], not through span membership.
(iii) *Alpha relabelled from an unspanned premium*: no. lambda_2 = 0, both loadings are (1, 0), and the second factor is unused, so the fund's extra mean is alpha against the stated two-factor model.
(iv) *Belief dispersion credited*: no. The positive gap uses only bar alpha, per claim 003. At the zero-alpha parameter point the conditional matched difference is 0, not negative. So the example does not claim that an investor who knew theta would prefer the fund.
(v) *An incumbent passed off as an optimum*: no. Optimality and uniqueness are proved, and red certified both optima independently.

**Scope, stated plainly.** The gap equals bar alpha times a* exactly (1/100 x 100/101): with complete substitution, equal costs and zero residual risk, the full-trading advantage is precisely the believed alpha on the fund holding, and nothing else. That is the expected answer, and the file calls it standard. Its use for D1 is as the complete-substitution benchmark against which the incomplete-substitution example must show something beyond alpha. The assumed alpha (1% per quarter) and gap (about 99 bp per quarter) are illustrative, not calibrated. Zero residual risk and singular Sigma are special: with residual risk sigma_e^2 > 0 the gap would shrink and could vanish. The claim asserts no transfer, correctly.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* If the alternative set reproduces an action's risky exposure, risk and cost exactly, the only remaining score difference is the idiosyncratic mean term (alpha as the non-replicable part of the mean).
- *General result.* For scores affine in exposures plus an idiosyncratic mean, Q(w) - Q(v) = (a_w - a_v)·alpha_bar whenever b(w) = b(v) and the risk and cost terms coincide. This is the Jensen and Dybvig-Ross view of alpha as the non-replicable excess mean.
- *Reduction.* In the claim's example B^A = B^E, the rates are equal and the residuals are zero, so the ETF replicates exposure and risk at equal cost and the gap is the mean-alpha term.
- *Verdict: special case,* realized in an explicit example. Left over: the example's exact numbers.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's own exact check from terminal wealth, KKT certificates for both optima and attacks (unequal funding, span as feasibility, alpha relabelling, belief dispersion credited, incumbent as optimum) are sound and match PM's direct score computation (E 51/10201, F 152/10201, gap 1/101) and grid check; no open objections; limits stated (assumed example; gap is exactly belief-mean alpha times the fund holding, the complete-substitution benchmark; zero residual risk and singular Sigma are special; no materiality).


Not machine checked. The instance has finite supports and rational data. A formal target can
verify its scenario moments and funded triangle, the replacement map and score formula,
and the two elementary strict-increase comparisons. Claims 003 and 005 are formalized, but
that does not machine-check this example, its optimizer identities or its gap.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2CompleteSubstitution.lean` and
the proof in `lean/Novel/M2CompleteSubstitutionProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used.

The instance. The data are entered literally into claim 003's formal M2 structure: m = n = 1,
K = 2, two scenarios, two support points, and every number as in the Statement. The statement
uses claim 004's `InitialPosition` and `RatesNonneg` and claim 005's B_E, D_E and L_E. Every
holding is written `hold a p`.

Proved:
- (i) The data satisfy every M2 restriction, including W^- = 1, rates below one, limits at most
  one, centered shocks, masses summing to one, and positive gross returns at both support points
  in both scenarios.
- (ii) The exact descriptions of F, E and N; b(a, p) = (a + p, 0); and
  B_E = D_E = {(t, 0) : 0 <= t <= 100/101}.
- (iii) Complete substitution: for every (a, p) in F, (0, a + p) is in E with the same exposure,
  w' Sigma w, review cost and cash. (0, 1) is outside both the ETF span and the active-loading span.
- (iv) For all a, p >= 0: w' Sigma w = t^2/100, tau = t/100 and k = 1 - (101/100) t.
  Qbar_0 = t/100 + a/100 - t^2/200, the matched difference is a/100, and the conditional matched
  differences are 0 at the first point and a/50 at the second.
- (v) (0,0), (0, 100/101) and (100/101, 0) are the unique maximizers on N, E and F: every other
  holding in the class scores strictly less. The table's cash, cost and scores hold; the E and F
  optima have equal exposure; and the gap is 1/101 > 0.

Relation to the prose. The score formulas are stated for all nonnegative holdings, not only
those in F. Singularity of Sigma appears in the proof (every entry is 1/100) but is not a separate
conjunct. The attribution of the gap to the positive belief-mean alpha is interpretation. Its
formal content is (iii) together with the conditional differences in (iv); red's scope remark
(gap = bar alpha x a*) follows from (iv) at a = t = 100/101. The formal proof computes the one-ETF
sets directly rather than applying claim 005's lemma. No gap was found between the formal
statement and the prose. The limits PM recorded at approval apply unchanged.

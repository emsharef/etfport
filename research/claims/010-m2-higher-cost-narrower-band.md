---
id: 10
title: "A higher common switching-cost rate can strictly narrow the M2 no-active-trade band"
status: formalized
model_version: M2
depends_on: [003, 004, 009]
axioms_used: []
formal: lean/Standalone/M2HigherCostNarrowerBand.lean
direction: D2
---
## Statement

There are two M2 instances differing only in their common symmetric shareholder switching-cost
rate, for which increasing that rate strictly decreases the width of claim 009's no-active-trade
band. The following exact, assumed instance establishes this existential statement. Width means
length in the active belief-mean alpha coordinate, with the incumbent portfolio fixed; it does
not mean a region in holdings or a set-inclusion comparison.

### Complete instance and alpha family

There is one active fund, one ETF and two factors. Set W^-=1, gamma=1,
`B^A=(1,1/2)`, `B^E=(1,0)`, `c^E=-1/10000`,
`(a^-,p^-,k^-)=(1/2,0,1/2)` and `(bar a,bar p)=(1,1/2)`.
Cash has gross return one. The four equally weighted parameter points have
`lambda_1 in {3/200,1/40}`, `lambda_2=1/200` and `alpha in {-1/400,1/400}`,
taking the Cartesian product. Their mean alpha is zero. To define the band as in claim 009,
replace both alpha values by `x-1/400` and `x+1/400`, leaving everything else fixed.

Use 32 equiprobable independent sign scenarios `s in {-1,1}^5`, with

```
z^f_s=(3 s_1/50, s_2/50),
z^A_s=3 s_3/100,       z^E_s=s_4/200.
```

The fifth sign is unused, retaining experiment 007's literal one-ETF scenario law.
Returns are exactly M2's `r_A=B^A f+alpha+z^A` and `r_E=B^E f-c^E+z^E`.
Set all four purchase/sale rates equal to kappa and compare
`kappa=0` with `kappa=1/2000`. Thus

```
tau(a-1/2,p)=kappa (|a-1/2|+|p|),
k(a,p)=1-a-p-tau(a-1/2,p).
```

Every other primitive, the entire belief at any fixed x, initial holdings and position limits
are identical between the two rate cases. Fees are charged on gross holding changes at the
review and deducted from cash once. There is no terminal liquidation cost, borrowing,
shorting, interim investor trade or alpha eligibility screen.

The admissible translated-alpha domain is `J=(-183/200,infinity)`. For each rate let
C_kappa be claim 009's extended-score no-active-trade set: values of x for which some
full-class maximizer has a=1/2. The M2 set is C_kappa intersect J. In this instance every
full-class maximizer is unique, and both displayed sets are wholly inside J.

### Exact optima, multipliers and bands

For every x, the unique ETF-only optimum is `(1/2,p_E)` with zero cash:

| kappa | p_E | I=[lo,hi] | alpha_c |
|---|---|---|---|
| 0 | 1/2 | [0,1319/80000] | -23/1250 |
| 1/2000 | 1000/2001 | {11032/690345} | -61367/3335000 |

The bands and their widths are

| kappa | C_kappa = [L,U] | U-L |
|---|---|---|
| 0 | [-23/1250, -153/80000] | 1319/80000 |
| 1/2000 | [-808663/276138000, -38269/20010000] | 701377/690345000 |

In particular

```
1319/80000 - 701377/690345000 = 170890979/11045520000 > 0.
```

At zero cost the ETF position cap and the cash constraint bind together. At positive cost
the ETF-only optimum is strictly below its cap, while cash still binds. The multiplier
interval therefore collapses to a point, removing the hi-lo term in claim 009's width.
The added active-fund cost terms are too small to offset that loss in this instance.

Corrected scope: for fixed finite lo and hi, claim 009's interior width
`b(1+hi)+s(1+lo)+(hi-lo)` increases with either active directional rate, with respective
slopes `1+hi` and `1+lo`. The comparison here changes ETF costs too, hence changes I;
it does not hold those endpoints fixed.

## Proof

### 1. The finite data satisfy M2

Each sign has mean zero; distinct signs have zero cross-moment and squared mean one.
The instrument shock vector is
`xi=(3 s_1/50+s_2/100+3 s_3/100, 3 s_1/50+s_4/200)`.
Consequently the conditional covariance and belief mean return are

```
Sigma = [[23/5000, 9/2500], [9/2500, 29/8000]],
mu(x)=(9/400+x, 201/10000).
```

For example Sigma_AA is `9/2500+1/10000+9/10000=23/5000`; Sigma_AE is
`9/2500`; Sigma_EE is `9/2500+1/40000=29/8000`. Thus the first diagonal entry is
positive and the determinant is `743/200000000>0`, so Sigma is positive definite.

The minimum active gross return over all four parameters and 32 scenarios is
`1+3/200+1/400+(x-1/400)-3/50-1/100-3/100 = x+183/200`.
The minimizing signs and parameter are present, so positivity is equivalent to x>-183/200.
The minimum ETF gross return is `1+3/200+1/10000-3/50-1/200=9501/10000>0`.
This proves the stated J, common to both rates. At x=0 the original prior is admissible.
All shocks and return laws are finite, known conditional laws independent of the parameter
and control. Initial holdings and cash are nonnegative, sum to one and obey the position
limits. Both rates lie in [0,1). The remaining M2 assumptions follow directly from the
specified timing, funding and charged amounts.

By claims 003 and 004 the funded score on each class is

```
Qbar_0(a,p;x) = (9/400+x)a + (201/10000)p
               - (1/2)(a,p)' Sigma (a,p)
               - kappa (|a-1/2|+|p|).
```

It has an attained maximum on F and E, which are nonempty convex compact sets. Positive
definiteness and gamma=1 make this score strictly concave: for distinct holdings the
negative quadratic is strictly concave, while the remaining affine and negative convex-cost
terms preserve the strict inequality. The compact feasible sets and continuous score also give attainment for every real x in
the affine extension, by the same compactness argument as claim 004; no positive-return
assumption is needed for that argument. Strict concavity gives uniqueness there as well.
On J this is the corresponding M2 optimization problem.

### 2. Solve the ETF-only problem

Fix a=1/2. Since p^- is zero and p is nonnegative, the only ETF trade is a purchase.
Funding becomes `k=1/2-(1+kappa)p`, so its feasible interval is
`0<=p<=min(1/2,1/[2(1+kappa)]) = 1/[2(1+kappa)]` for both compared rates.
The part of the score depending on p has derivative

```
201/10000 - 9/5000 - (29/8000)p - kappa.
```

For every feasible p and either rate this derivative is at least
`201/10000-9/5000-29/16000-1/2000=1279/80000>0`.
The score is therefore strictly increasing on that interval, with unique maximum
`p_E=1/[2(1+kappa)]`, and its post-trade cash is zero. This proof does not depend on x:
the active alpha contribution is the constant x/2 on E.

The active incumbent satisfies `0<1/2<bar a=1`, so claim 009's interior case applies.
At the ETF optimum p_E>0 and the ETF cost-slope endpoints are both kappa. The smooth
ETF marginal and alpha centering value are

```
g_E=201/10000-9/5000-(29/8000)p_E,
alpha_c=23/10000+(9/2500)p_E-9/400.
```

### 3. Compute I and apply the band characterization

When kappa=0, p_E=bar p=1/2. The ETF upper-bound condition in claim 009 imposes no lower
bound on eta besides eta>=0; the positive-position condition imposes eta<=g_E.
With zero cash complementarity is automatic. Since g_E=1319/80000, this gives
`I=[0,1319/80000]`. The centering value is -23/1250. Claim 009 with b=s=0 gives
`L=alpha_c` and `U=alpha_c+hi`, yielding the first band in the table.

When kappa=1/2000, `0<p_E=1000/2001<1/2`. Both ETF stationarity inequalities apply,
and together require `g_E=kappa+(1+kappa)eta`. Here
`g_E=11377/690000`, so

```
eta = (11377/690000-1/2000)/(1+1/2000) = 11032/690345 > 0.
```

Thus I is exactly that singleton. Substitution gives `alpha_c=-61367/3335000`.
Claim 009 gives

```
L=alpha_c-1/2000+(1999/2000)eta = -808663/276138000,
U=alpha_c+1/2000+(2001/2000)eta = -38269/20010000.
```

Their difference is `(1/1000)(1+eta)=701377/690345000`. All four band endpoints lie
strictly between -1/50 and zero, so both bands lie in J. Clipping by positivity changes
neither interval nor its width. Since optima are unique, each band describes precisely
when that unique full optimum has a=1/2, not merely the existence of a tied no-trade action.

Subtracting the two rational widths gives the positive difference in the Statement.
This proves strict narrowing while holding every non-cost input fixed. The corrected-scope
sentence follows by subtracting the width formula at two b values with s,lo,hi fixed,
or at two s values with b,lo,hi fixed. The resulting increments are
`(b_2-b_1)(1+hi)` and `(s_2-s_1)(1+lo)`; both coefficients are positive because lo,hi>=0.

## Checks

`uv run python checks/010/check.py` reconstructs the full finite data and rational band table,
checks every gross return at the band endpoints and independently checks full-class decisions
at and just outside the endpoints using experiment 004's exact solver. The earlier
`checks/exp007-monotonicity/check.py` checked the witness before it became this claim.
Experiment 007 registered the search before its results; this claim promotes its first H3
witness. These finite checks supplement the proof; they do not establish a general monotonicity.

## Not shown

- This is one assumed, uncalibrated pair of cost cases in M2, not a general decrease of
  width with costs. For this family's comparison from zero to 1/2000, narrowing requires
  bar p=1/2 exactly, the zero-cost cash-exhausting ETF purchase. At any other admissible
  ETF cap, the zero-cost width is zero: below 1/2 cash is slack and I={0}; above 1/2 the
  ETF is interior and I is a singleton. Positive cost then widens the band. Thus the
  zero-cost width is discontinuous in the cap, and perturbing the cap away from 1/2
  removes this narrowing. The result is not a typical or robust cost effect.
- Red's scope review does find narrowing between two strictly positive rates: with
  bar p=1000/2001, raising kappa from 1/2000 to 1/1000 narrows the band. At the lower
  rate the cap equals the cash-exhausting purchase and I=[0,11032/690345]; at the
  higher rate the ETF is interior and I={77524/5010005}. This is again a coincident
  corner, not evidence of robustness. That additional instance is recorded in Review;
  it is not added to this claim's Statement or proof.
- Narrowing is a length comparison, not an inclusion statement about the two intervals.
  No statement about bands in holdings, all prior shapes, or continuation in M3 follows.
- Alpha is varied only to define each band. The same complete translated prior is used in
  both cost cases at each x; there is no change of beliefs concealed in the cost comparison.
  Claim 003's belief-mean limitation remains: this is not an uncertainty effect.
- The literature comparison does not refute any cited source theorem or prove priority.
  PM's scope decision excludes this coincident-corner cost effect as D2's paper anchor;
  the claim does not itself settle D2's kill criterion.
- The cash-composition H2 witness stays in FINDINGS and is not part of this claim.

## Prior art

Read the registered full texts `bichuch2014investing`, section 2.3, Theorem 2.2(iii),(v);
`gallien2018hedge`, section 5, Proposition 1 and equations (5)-(7); and `liu2013portfolio`,
Theorem 2.3(iii),(vii) and section 3's small-cost discussion. Also checked FINDINGS, the
empty refuted-claim directory, claim 009 and experiment 007's failed H3 target. No literature
result is a proof premise, so no new upstream assumption is introduced.

`bichuch2014investing` gives continuous-time long-horizon CRRA boundaries in an illiquid
holding weight with a freely traded liquid risky asset. Under its nondegenerate small-cost
assumptions the leading band width scales with the cube root of the spread. Its alpha is
relative to its liquid index, not automatically M2's economic factor attribution.
`gallien2018hedge` Proposition 1 gives an approximately optimal small-cost band in illiquid
shares, with liquid futures hedging and a terminal wealth floor. Holding its state variables
fixed, its width parameter has cube-root cost scaling; the paper explicitly discusses widening
with costs. These statements concern dynamic holding bands under their own hypotheses.

`liu2013portfolio` is the closer constraint precedent: an infinite-horizon CRRA investor
with one risky and one safe asset and a binding risky-weight cap. Its selling boundary stays
at the cap and its buying boundary retreats by a positive square-root leading term as a small
spread is introduced. Thus a separate constraint reshaping a no-trade band is already known.
Its scalar gap named lambda is neither M2's factor premium nor the compatible cash multiplier.

Here the band is instead in the active conditional mean, at a fixed incumbent, for a single
funded quarterly quadratic problem. The cost change applies to the ETF comparator as well
as the active fund and moves that comparator below its own cap. Claim 009's compatible
multiplier interval then collapses, reducing the alpha-band width. This gives an exact failure
of transferring the usual widening heuristic to this object; it is not a contradiction of
those sources' small-cost holding-band results. No global cost-monotonicity theorem is
attributed to the sources beyond those stated regimes, and these distinctions alone do not
establish novelty.

## Open objections

None yet; red review pending.

## Review

**Red, 2026-09-27.** I checked the proof by hand, reproduced it independently, and then attacked its scope.

**The hand check holds line by line.**
- *Covariance and means.* The shock vector is xi_A = 3s_1/50 + s_2/100 + 3s_3/100 and xi_E = 3s_1/50 + s_4/200. That gives Sigma_AA = 23/5000, Sigma_AE = 9/2500 and Sigma_EE = 29/8000, with determinant 667/40000000 - 81/6250000 = 743/200000000 > 0. The means are mu = (9/400 + x, 201/10000).
- *Positivity domain.* The minimum active gross return is 0.915 + x, which gives J = (-183/200, infinity). The minimum ETF gross return is 9501/10000.
- *ETF-only problem.* On E, funding gives p <= 1/[2(1 + kappa)] <= bar p. The p-derivative 201/10000 - 9/5000 - (29/8000)p - kappa is at least 1279/80000 > 0. So p_E is the funding limit, with zero cash, independent of x.
- *Zero cost.* g_E = 1319/80000. The ETF sits at its cap, so no lower bound applies beyond 0, and I = [0, g_E]. alpha_c = 23/10000 + (9/2500)(1/2) - 9/400 = -23/1250, U = alpha_c + hi = -153/80000.
- *Rate 1/2000.* p_E = 1000/2001 is interior, so both ETF inequalities pin eta = (g_E - kappa)/(1 + kappa) = 11032/690345, with g_E = 11377/690000. The width is 2 kappa (1 + eta) = 701377/690345000, and the difference is 170890979/11045520000 > 0.
- *Uniqueness.* Strict concavity on compact sets gives a unique optimum for every real x, so each band is exactly the set where the unique full optimum keeps a = 1/2.
- *The corrected-scope sentence is right.* I depends only on the ETF-only problem, where a is fixed and the active rates never enter. alpha_c does not depend on the rates either. The width is therefore strictly increasing in each active rate, with slopes 1 + hi and 1 + lo, whenever the ETF rates are held fixed.

**Independent reproduction.** Claim 010's instance is experiment 007's menu-1 row with a- = 1/2, c = 1 and d = 1/2, at the Zero and Equal-low cost schedules. My reproduction `experiments/007/red_reproduce.py` (on red/exp007-review) uses its own Sigma, directional KKT certificate and claim-009 band. It returns the same p_E, I, alpha_c, C and widths in exact rationals. At L - 1e-12, L, U and U + 1e-12 the certified unique full optimum trades, holds, holds and trades, for both rates. The claim's own `checks/010/check.py` also passes when run from this branch.

**Attacks that did not succeed.**
- A belief change hidden in the cost comparison: the whole translated prior is identical at each x.
- Alpha relabelled from a factor premium: the factor means are fixed, and only the alpha translation defines the band.
- A clipped width: all four endpoints lie in (-1/50, 0), inside J.
- Non-uniqueness or a tie: the score is strictly concave.
- A misapplied claim 009 case: 0 < a- < bar a, so the interior case applies.
- Hidden borrowing, shorting or double-counted costs: none. c^E is deducted once, and fees are charged once from cash.

The prior-art summaries match the registered texts I spot-checked. For example, `liu2013portfolio` Theorem 2.3(iii) gives a selling boundary at pi_max and a buying boundary at (1 - lambda) pi_max.

**Scope (sharpenings; neither changes the verdict).**
1. **The witness is a knife-edge in the ETF cap.** Holding k- = 1/2 and varying only bar p, I computed exact certified bands with red's code. At zero cost the width is 0 for every cap other than 1/2 (tested 49/100, 4997/10000, 1000/2001, 49999/100000, 50001/100000, 51/100, 3/4 and 1): the budget or the cap then binds alone, which pins the multiplier or makes it zero. Only at bar p = 1/2 exactly, where the cap and cash exhaustion coincide, does the width jump to 164.875 bp. At every other tested cap a higher cost widens the band, to 10.00 or 10.16 bp. So the band width is discontinuous in the cap. The narrowing exists only at the coincident corner, and the strict inequality should not be read as a typical or robust cost effect. The existential Statement is unaffected. I suggest that math adds one Not shown sentence: in this family, any perturbation of bar p away from k- removes the narrowing.
2. **Narrowing between two strictly positive rates does occur.** The first Not shown bullet leaves this open. Put the coincidence at the lower rate: bar p = 1000/2001, the cash-limited purchase at kappa = 1/2000. The width then falls from 169.8841 bp (I = [0, 11032/690345]) at kappa = 1/2000 to 20.3095 bp (I = {77524/5010005}) at kappa = 1/1000. It does not narrow to kappa = 1/100 (201.2882 bp). This is again a coincident-corner instance, so point 1 applies to it too.

**Consistency with earlier results.** This is the exact form of experiment 007's refuted H3, and it sharpens the Results' reading: all three H3 violations are corner coincidences of this kind. It does not contradict claim 009, whose hi - lo term is exactly what collapses.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* At a degenerate optimum, where two constraints are active with one free direction, the multiplier set is an interval, so the range of optimality is fat. A data change that moves the solution off the corner pins the multiplier, and the range shrinks discontinuously.
- *General result.* Degeneracy in parametric linear and quadratic programming: dual solution sets are not singletons at degenerate primal solutions, and optimality ranges are discontinuous in the data.
- *Reduction.* The witness is degenerate at the rate kappa_1, because the cap equals the cash-exhausting purchase. The positive rate moves the ETF-only optimum into the interior, which pins eta. The knife-edge found in red's Review is exactly this degeneracy.
- *Verdict: special case.* Left over: the explicit witness.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's line-by-line hand check, independent exact reproduction through experiment 007's code and attacks (hidden belief change, alpha relabelling, clipped width, ties, misapplied case, hidden financing) are sound, and PM reran checks/010; no open objections. Limitation stated here from red's scope review: the narrowing is a knife-edge that exists only where the ETF cap exactly equals the cash-exhausting purchase (any other cap gives zero width at zero cost, and higher cost then widens the band), so the band width is discontinuous in the cap and the result is not a typical or robust cost effect; red also found narrowing between two positive rates, again only at such a coincident corner.


None yet. The finite rational instance, its M2 validity, ETF optimum and substitution into
claim 009 are candidates for the deterministic formal core. No machine checking of this
claim is asserted; a formal counterpart must preserve the exact prior/scenario family,
positivity domain and both complete intervals, not just compare two supplied width numbers.

Lean, 2026-09-27: machine checked. The statement is in
`lean/Standalone/M2HigherCostNarrowerBand.lean` and the proof in
`lean/Novel/M2HigherCostNarrowerBandProof.lean`. `lake build` and the axiom audit pass (standard
axioms only). No hypothesis structure or cited result is used.

The instance. It is entered literally at both rates: all primitives as stated, the 32 sign
scenarios with the fifth sign unused, and the four equally weighted support points. The band and
its ingredients are claim 009's formal definitions (C, I, alpha_c, L, U, J), so the formal result
is about the same band that claim 009 characterizes, not about two supplied width numbers.

Proved:
- at both rates: claim 009's setting holds, with rates below one, centered shocks and positive
  gross returns at the original prior; J = (-183/200, infinity); Sigma is positive definite; and
  every full-class maximizer is unique for every real x;
- for each rate, both table rows: for every x the unique ETF-only optimum is (1/2, p_E) with zero
  cash; I = [0, 1319/80000], respectively {11032/690345}; alpha_c; and
  C_kappa = [L, U] with the stated rational endpoints, contained in J;
- the two widths, their difference 170890979/11045520000 > 0, and the corrected-scope identities
  for the interior width in b and s.

Dependence on claim 009. The proof uses claim 009's machine-checked results (band table,
multiplier interval, uniqueness and the criterion formula) by importing its proof module
`Novel.M2NoActiveTradeBandProof`. This departs from the import convention written in
`lean/Novel.lean`; see Q-04 in `board/QUESTIONS.md`, where this is the default taken.

Relation to the prose. The ETF-only optimum is proved for every rate in [0, 1/2000], which covers
both compared rates. No gap was found between the formal statement and the Statement.

Scope. The limitation PM recorded at approval applies unchanged. The narrowing holds only at the
coincident corner where the ETF cap equals the cash-exhausting purchase, so it is a knife-edge
effect and not a robust cost effect. The formal result is exactly this existential instance and
does not widen that scope.

---
id: 008
title: "Zero-alpha non-participation under feasible, costless ETF replacement"
status: formalized
model_version: M2
depends_on: [003, 004]
axioms_used: []
formal: lean/Standalone/M2ZeroAlphaLimitingCase.lean
direction: D1
---
## Statement

Fix an M2 instance with one active fund and one ETF, arbitrary compliant initial holdings
`(a^-,p^-,k^-)`, and the following additional assumptions:

- The loading rows agree, B^A=B^E, and ETF drag c^E=0. All other M2 restrictions, including
  positive gross returns at every parameter/scenario pair, remain in force.
- The ETF purchase and sale rates are zero, and its position limit is bar p=1. The active
  position limit is arbitrary in [0,1], and its directional rates remain in [0,1).
- The belief-mean alpha is zero: bar alpha=0. This includes alpha=0 at every parameter point,
  but permits nonzero parameter alphas averaging to zero. Nothing assumes access to true alpha.
- Write xi_E for the ETF's centered conditional return shock and
  `epsilon_s = xi_A,s - xi_E,s`. Assume `sum_s q_s xi_E,s epsilon_s=0` and set
  `v_epsilon = sum_s q_s epsilon_s^2 >= 0`. These are finite scenario quantities independent
  of theta; epsilon is centered by M2. Zero covariance here is an additional assumption,
  not a consequence of the economic factor decomposition.
- Either (A) there is no incumbent active holding, a^-=0, or (B) active sales are free,
  kappa^-_A=0. Both can hold. Active purchases need not be free.

For every full feasible holding w=(a,p), its replacement holding `T(w)=(0,a+p)` is feasible,
has the same factor exposure, and has zero review cost. If tau denotes w's review cost, then

```
k(T(w)) - k(w) = tau(w-w^-),
Qbar_0(T(w)) - Qbar_0(w) = tau(w-w^-) + (gamma/2) a^2 v_epsilon >= 0.
```

There is consequently a full-class optimum with zero active holding. Moreover:

1. Under (A), T(w) belongs to E, so V_F=V_E. Every full optimum has a=0 if
   `kappa^+_A>0` or `gamma*v_epsilon>0`. This means all optima avoid new participation,
   not that the ETF and cash allocations are unique.
2. Under (B), every full optimum has a=0 if `gamma*v_epsilon>0`. When a^->0, a zero-active
   holding is not in E: this conclusion is about liquidation in F, not equality of F and E.
3. For exact return replication impose the stronger conditions alpha=0 at every theta and
   epsilon_s=0 at every scenario. Then r_A,s(theta)=r_E,s(theta) pointwise and
   `W_1(T(w);theta,s)-W_1(w;theta,s)=W^- tau(w-w^-)` for every theta,s.
   With zero review cost the replacement preserves wealth scenario by scenario. Under (A),
   a positive purchase rate still forces a=0 at every optimum; if purchase costs and residual
   risk both vanish, the general conclusion is existence, not uniqueness of non-participation.

The following assumed M2 cases demonstrate the limits. For all four, W^-=1, gamma=1,
B^A=B^E=(1,0), c^E=0, the belief is a singleton with lambda=(1/50,0), alpha=0, and the
factor shocks are (+/-1/10,0), each with mass 1/2. All residual shocks vanish, so instrument
returns are identical and positive in gross terms. ETF trading is free; both position limits
are one except the cap in the last row. Let H(t)=t/50-t^2/200.

| Case | Initial (a^-,p^-,k^-) | Active buy/sell rates | Optimal holdings and consequence |
|---|---|---|---|
| A positive purchase cost | (0,0,1) | (1/100,1/100) | Unique F optimum (0,1), score 3/200 |
| A costly incumbent | (1,0,0) | (1/100,1/100) | Unique F optimum (1,0), score 3/200; the best zero-active holding (0,99/100) has score 9799/2000000 |
| A tie under exact replication | (0,0,1) | (0,0) | Every (a,p) with a+p=1 is optimal, score 3/200; in particular (0,1) and (1,0) tie |
| A replacement blocked by the ETF cap | (0,0,1) | (0,0) | With bar p=1/4, every feasible a+p=1 is F-optimal, score 3/200; the E optimum is (0,1/4), score 3/640, giving V_F-V_E=33/3200 |

Thus neither zero alpha alone, nor identical instrument returns alone, implies compulsory
liquidation, that every optimum has zero active holdings, or that V_F=V_E. The replacement
and cost assumptions above are sufficient conditions, not asserted necessary conditions.

## Proof

### Feasible replacement and the score identity

M2 initial normalization gives a^-+p^-+k^-=1. Hence for every holding,
`k(w)=1-a-p-tau(w-w^-)`. The ETF incurs no cost, so

```
tau(w-w^-)=kappa^+_A max(a-a^-,0) + kappa^-_A max(a^--a,0).
```

Under (A), this is kappa^+_A a since a>=0. Under (B), it is
kappa^+_A max(a-a^-,0). At T(w), the active holding is zero, so its cost is
kappa^-_A a^-, which is zero under either (A) or (B). The ETF cost is still zero,
including when replacing an incumbent requires an ETF purchase.

For w in F, nonnegative cash and nonnegative costs imply 0<=a+p<=1. Thus T(w)'s active
holding satisfies its bound, its ETF holding lies in [0,bar p]=[0,1], and its cash
`1-a-p=k(w)+tau(w-w^-)` is nonnegative. This proves feasibility and the cash identity
without borrowing, shorting or additional wealth. B^A=B^E gives
b(w)=(B^E)'(a+p)=b(T(w)), so the factor exposure is preserved. Under (A) the replacement
also fixes a=a^-=0 and therefore belongs to E.

Write t=a+p within this proof. The centered random return on w is

```
a xi_A + p xi_E = t xi_E + a epsilon.
```

Both terms are centered. Expanding the finite second moment, the assumed zero cross-moment
eliminates the mixed term, giving

```
w' Sigma w = t^2 sum_s q_s xi_E,s^2 + a^2 v_epsilon,
T(w)' Sigma T(w) = t^2 sum_s q_s xi_E,s^2.
```

The expected return terms differ by a alpha at a fixed theta: the common exposure cancels,
and ETF drag is zero. Subtracting M2's scores, including the review costs once, therefore gives

```
Q_0(T(w);theta) - Q_0(w;theta)
  = -a alpha + (gamma/2) a^2 v_epsilon + tau(w-w^-).
```

Averaging over the finite belief replaces alpha by bar alpha=0, proving the score identity
and its nonnegative sign. This uses the belief average of conditional risk, not a predictive
variance across parameter means. Claim 003 supplies the same accounting and belief-mean
interpretation in M2; the displayed finite calculation also derives the difference directly.

### Attainment and strict non-participation

Claim 004 gives an attained F maximum for this M2 instance. Replace one such maximizer by
T(w). Feasibility and the score inequality show that the replacement also attains the F
maximum and has zero active holding. Under (A) it is in E, so V_E>=V_F; since E is a subset
of F the reverse inequality holds and the values are equal.

For a>0 under (A), the improvement is
`kappa^+_A a + (gamma/2) a^2 v_epsilon`. It is strictly positive if either stated strict
condition holds. No such w can maximize F. Under (B), the nonnegative cost term plus
`(gamma/2) a^2 v_epsilon` is strictly positive for a>0 when gamma*v_epsilon>0, yielding
its strict conclusion. No uniqueness assertion about p or cash was used. When the strict
conditions fail, the identity supplies only weak dominance; the tie example below shows
why it cannot generally be strengthened.

Under the stronger pointwise assumptions in part 3, equal loadings, zero drag, alpha=0
and xi_A=xi_E make the two instrument returns equal at every theta,s. Their total risky
holding t and risky terminal value therefore agree between w and T(w). Only the cash
term differs, by tau, yielding the stated W_1 identity after multiplying by W^-.
This is a per-scenario assertion; bar alpha=0 alone would not suffice for it.

### The four limits, proved directly

All four cases have centered two-point shocks, covariance
`Sigma=(1/100)*[[1,1],[1,1]]`, and gross returns 1+1/50+/-1/10, whose minimum is 23/25>0.
The initial holdings satisfy their limits, the rates are in [0,1), and each candidate uses
the same funded budget as its comparator. The score of a holding with t=a+p is
`H(t)-tau`. Every feasible holding has 0<=t<=1. For 0<=u<v<=1,

```
H(v)-H(u) = (v-u)[1/50-(u+v)/200] > 0,
```

because the bracket is at least 1/100. Thus H is strictly increasing on this interval and
H(1)=3/200. This algebra proves the required global maxima without an optimizer or a
first-order necessity theorem.

In the first case tau=a/100. The replacement result excludes a>0 at an optimum; at a=0,
feasibility is 0<=p<=1 and strict increase makes p=1 the unique optimum.

In the incumbent case a<=1 and tau=(1-a)/100. Therefore
`Qbar_0(w)=H(t)-(1-a)/100<=H(1)`. Equality requires a=1, and then funding forces p=0;
this candidate is feasible, proving its unique optimality. With a=0 the sale cost is 1/100,
so funding restricts p<=99/100. Strict increase gives the best zero-active holding as
(0,99/100), of score H(99/100)-1/100=9799/2000000. Its score is strictly below 3/200.
Here E fixes a=1 and consists of the incumbent alone; the liquidated holding is not an
ETF-only action. This case violates both (A) and (B), so it does not contradict the result.

In the third case tau=0 and the feasible set is a,p>=0, a+p<=1. Strict increase of H
makes exactly the holdings a+p=1 optimal. This includes both displayed endpoints. Exact
replication with zero costs makes the decomposition indeterminate even though total risky
holding is uniquely one.

In the fourth case the additional cap is p<=1/4. Full trading can still attain t=1, for
example with (a,p)=(3/4,1/4), and precisely the feasible holdings with t=1 maximize F.
In E, a=0 and p<=1/4, so its unique optimum is p=1/4. Direct evaluation gives H(1/4)=3/640
and H(1)-H(1/4)=33/3200. T(3/4,1/4)=(0,1) violates the ETF cap, identifying the actual
failure of replacement despite identical returns and matched loadings.

## Checks

`uv run python checks/m2-zero-alpha/check.py` checks the four fixed rational cases above,
using exact global certificates and no imported optimizer. Its code and these cases were
committed previously; they are finite checks, not the general proof.

`uv run python checks/008/check.py` checks the replacement identity against explicit finite
scenario moments, direct conditional scores, costs, cash and terminal wealth on fixed rational
holdings. It includes positive residual risk, a mean-zero-alpha belief with nonzero support
alphas, a free-sale incumbent, and exact replication. It checks the cross-moment assumption
and a nonzero-covariance case that violates it. These deterministic checks supplement the
paper proof; they are not experiments, empirical evidence or machine checking of the claim.

`uv run python checks/008/tracking_scope.py` independently reconstructs the finite scenario
covariance and global optimality certificate for red's tracking-noise scope example below.
It also checks that shared residual noise can satisfy the cross-moment hypothesis with a
noisy ETF. These are fixed assumed checks, not an empirical experiment.

## Not shown

This is a one-quarter result under explicit sufficient restrictions, not a characterization
of all zero-alpha instances or a multiperiod optimal policy. The known ETF is freely tradable,
its cap permits complete replacement, its drag is zero and its loading equals the active
fund's. The uncorrelated residual-difference restriction is additional to M2. Independent
active and ETF residuals can also supply a diversification benefit when the ETF has tracking
noise. A negative cross-moment is not removed by defining alpha relative to economic factors.

More precisely, equal loadings imply epsilon=z^A-z^E and the general finite identity

```
E_q[xi_E epsilon] = E_q[(B^E z^f)(z^A-z^E)]
                    + E_q[z^E z^A] - E_q[(z^E)^2].
```

If both residuals are uncorrelated with the factor shocks and with each other (in particular,
if all three primitive shocks are independent), this becomes -Var_q(z^E). In that subclass
the claim's zero-cross-moment hypothesis forces zero ETF residual variance. Independence of
the two residuals alone does not remove their cross-moments with factors; M2 imposes neither
restriction. In general a noisy ETF is compatible with the claim: take z^A=z^E+epsilon with
centered epsilon independent of both z^E and the factors. This gives the required zero
cross-moment even when Var_q(z^E)>0. The source-like unit-exposure decomposition is relative
to the ETF's full return shock, not just to its economic factor component.

Red's scope example, independently derived here: use the four examples' equal loadings,
singleton means and gamma; set costs to zero, limits to one and initial holdings to cash. Add independent
active and ETF residual signs of size 1/100 to the factor sign of size 1/10. There are eight
equiprobable sign triples; minimum gross return is 91/100. The covariance is
`[[101,100],[100,101]]/10000`, and E_q[xi_E epsilon]=-1/10000. For t=a+p and nonnegative
funded holdings, 0<=t<=1, the score is exactly

```
Qbar_0(a,p) = t/50 - 201*t^2/40000 - (a-p)^2/40000.
```

The first two terms strictly increase on [0,1]: their difference at u<v is
`(v-u)[1/50-201*(u+v)/40000]>0`, since the bracket is at least 199/20000.
The last term is nonpositive and vanishes only when a=p. Thus the unique F optimum is
(1/2,1/2), score 599/40000. In E, a=0 and the score is p/50-101*p^2/20000, strictly
increasing on [0,1] by the same difference calculation, so its unique optimum is (0,1),
score 299/20000. The gap is 1/40000. This is a diversification benefit from independent
tracking noise at zero alpha, outside the explicit cross-moment hypothesis. It is a scope
counterexample, not an additional part of the Statement or a general magnitude claim.

Belief-mean zero alpha is sufficient for the score conclusions; it does not assert true alpha
is zero, that active returns equal ETF returns, or that belief dispersion is penalized.
The stronger pointwise assumptions are required for exact return replication and the wealth
identity. No inference procedure, confidence statement or ambiguity-aversion penalty enters.
All four examples and check inputs are assumed and establish no materiality or calibration.

Free ETF trading and (when invoked) free active sales are benchmark restrictions, not observed
cost rankings. The positive active cost in the counterexamples is also assumed. No claim is
made that M2 ordinarily satisfies these restrictions. Eligibility is fixed without an alpha
screen, no future observation enters a decision, costs are shareholder costs paid at review,
and there is no terminal liquidation charge. No proposal section 2 commitment is relaxed;
these are deliberately narrow specializations within M2. D1's eight-claim budget is exhausted
by this filing; this fact does not itself decide D1's empirical kill criterion.

## Prior art

Read M2, claims 003-004, the zero-alpha FINDINGS entry and its previously committed checks,
the refuted registry (no claim there), and `bichuch2014investing`, sections 2.1-2.2, pp. 4-5
of the supplied full text. Section 2.2 gives the zero-alpha non-participation discussion after
the frictionless allocation formula (2.3); it is not the positive-alpha Theorem 2.2 of section
2.3. No literature result is a proof dependency or entered as an axiom. No new literature
search or general novelty claim is made; this is D1's requested limiting-case comparison.

| Issue | Source and precise M2 comparison |
|---|---|
| Zero-alpha conclusion | `bichuch2014investing`, section 2.2, says zero alpha makes avoiding the illiquid security optimal. Under (A), M2 recovers existence of a zero-active optimum and equality V_F=V_E; with positive purchase cost or gamma*v_epsilon>0 every optimum avoids it. |
| Residual risk versus exact replication | The source assumes positive risky volatilities and absolute correlation below one, giving strictly positive residual variance. Our equal-loading, zero-cross-moment case corresponds to unit exposure to the liquid asset plus residual risk. With gamma>0 and v_epsilon>0 it gives strict non-participation; exact return replication has v_epsilon=0 and is outside that nondegenerate source hypothesis. With zero costs it can give ties, as proved above. |
| Alpha's meaning | Source alpha is residual expected return relative to the liquid index. M2 alpha remains relative to economic factors. Equal loading, zero drag and the residual cross-moment condition align these decompositions in this restricted unit-exposure case (when ETF variance is positive); this is not a redefinition of M2 alpha for other ETF menus. Belief-mean zero alpha is an additional M2 score observation, not a source claim about uncertain parameters. |
| Funding and limits | The source's admissibility condition in definition 2.1 requires nonnegative liquidation value and permits liquid positions beyond M2's componentwise funded long-only restrictions. Here the explicit replacement map is proved feasible using bar p=1 and zero replacement cost. The cap counterexample explains why source intuition cannot bypass M2's position bounds. |
| Time, objective and an incumbent | The source maximizes an infinite-horizon CRRA equivalent safe rate (2.2), separating recurring effects from one-off setup and liquidation. M2 charges the current review cost in a conditional one-quarter mean-variance score. Its costly incumbent need not be liquidated. Part (B) supplies an existence result when sales are free, with strict liquidation if residual risk is penalized; it does not infer compulsory immediate liquidation from the source's long-run criterion. |
| Return law and preferences | The source has continuous geometric-Brownian returns and dynamic trading, with CRRA risk aversion positive and different from one in (2.2). M2 has finite scenarios and gamma>=0 as a score coefficient; it neither discretizes nor proves convergence to that source's dynamics. When gamma=0 and purchase costs vanish, strict non-participation need not hold. |

The recovered conclusion is a directly proved M2 replacement result. The differing uniqueness,
incumbent and constrained-replacement conclusions are precise obstructions to an unqualified
transfer, not refutations of `bichuch2014investing`.

## Open objections

Red's scope objection (Review below) is accepted: the earlier sentence about correlated
residuals understated the restriction. The Not shown section now proves red's independent-
residual example and explains the full cross-moment identity. It also qualifies the review's
"only if the ETF has zero residual variance" statement: that implication needs residuals
uncorrelated with factors and with each other. Shared active/ETF residual noise can satisfy
the claim with a noisy ETF. The Statement and its proof are unchanged; no mathematical
objection to them remains recorded. The review is preserved below as originally written.

## Review

Red, 2026-09-27. Re-derived independently.

**General statement, checked line by line.**
- *The replacement map.* With the ETF free, tau(w - w^-) is the active leg alone. T(w) = (0, a + p) costs kappa^-_A a^-, which is 0 under (A) or (B). Its cash is 1 - t = k(w) + tau >= 0, and t <= 1 <= bar p, so it is feasible under the same funded budget, with no borrowing or shorting.
- *The variance split.* a xi_A + p xi_E = t xi_E + a epsilon, and the assumed zero cross-moment gives w'Sigma w = t^2 Var(xi_E) + a^2 v_epsilon.
- *The mean difference.* With equal loadings and c^E = 0 the means differ by a alpha. So Q_0(T(w)) - Q_0(w) = -a alpha + (gamma/2) a^2 v_epsilon + tau(w - w^-), and averaging over pi replaces alpha by bar alpha = 0 (claim 003).
- *The strictness conditions.* Under (A), tau = kappa^+_A a; under (B), tau >= 0, so strictness there comes from gamma v_epsilon > 0. Attainment follows from claim 004, and V_F = V_E under (A) because T(w) lies in E.
- *Part 3.* The per-scenario wealth identity needs the pointwise assumptions, as stated.

**Four examples, checked independently.** Red used the experiment 004 solver, red's own scenario-enumerated Sigma and objective, and red's exact directional KKT certificates:
- Case 1: (0, 1) is certified optimal, with score 3/200.
- Case 2: the incumbent (1, 0) is certified, with score 3/200; the best zero-active holding (0, 99/100) scores 9799/2000000.
- Case 3: (0, 1), (1, 0) and (1/3, 2/3) are all certified optimal, so the optimum is a tie.
- Case 4: F's (3/4, 1/4) and E's (0, 1/4) are both certified, with gap 33/3200.
By hand, H(v) - H(u) = (v - u)[1/50 - (u + v)/200] > 0 on [0, 1] is correct.

**Attacks tried.**
(i) *Hidden financing or borrowing in the replacement*: none. Cash is 1 - t under the identical budget.
(ii) *Span read as feasibility*: no. Case 4 shows the ETF cap blocking replacement despite identical returns, which is the obstruction claim 005 classifies.
(iii) *Double-counted drag*: excluded, since c^E = 0.
(iv) *Belief-dispersion credit*: none. Only bar alpha enters, and part 3 correctly requires pointwise alpha = 0 for wealth equality.
(v) *Transfer from `bichuch2014investing` overstated*: no. The comparison table names the differences in funding, objective, incumbent treatment and return law, and calls them obstructions to an unqualified transfer, not refutations.

**Objection on scope (precise; not a refutation).** The zero cross-moment hypothesis sum_s q_s xi_E,s epsilon_s = 0 is much stronger than "uncorrelated residuals". With B^A = B^E, epsilon = z^A - z^E, so E[xi_E epsilon] = Cov(z^A, z^E) - Var(z^E). In M2's natural specification with independent residual shocks, the hypothesis therefore holds **only if the ETF has zero residual variance**, which is the source's case of a liquid asset that is the index itself.

Once the ETF has any tracking noise, zero-alpha non-participation fails even with independent residuals, zero costs and no incumbent. Red's certified instance has A = E = (1, 0), lambda = (1/50, 0), alpha = 0, a factor shock of +-1/10, independent residual shocks of +-1/100 on both instruments, gamma = 1, zero costs and an all-cash start. The cross-moment is -1/10000. The unique F optimum is (1/2, 1/2), holding the zero-alpha fund to diversify the ETF's residual, and V_F - V_E = 1/40000 > 0.

The claim's Not shown says "correlated residuals could supply a diversification benefit". That understates it: an ETF with its own tracking noise supplies one with uncorrelated residuals. Math should reword that sentence, for example: "With independent residuals the cross-moment hypothesis forces the ETF's residual variance to zero; with a noisy ETF a zero-alpha fund is held for diversification." This does not affect the Statement or proof, which assume the hypothesis explicitly.

**Scope.** This is a sufficient-condition limiting case with sharp counterexamples, as the file says. It recovers the source's zero-alpha conclusion only for a noiseless ETF, freely traded and uncapped. Red's instance above adds a fifth limit, and it matters for D1: tracking error alone makes an active fund worth holding at zero alpha in the one-quarter score.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* In an interior mean-variance optimum, an asset gets zero weight exactly when its regression intercept on the other available assets is zero. A zero intercept against non-tradable factors differs from a zero intercept against a noisy tradable proxy.
- *General result.* Mean-variance spanning and intercept tests (Huberman-Kandel; Jensen's alpha against a tradable benchmark; the Roll critique). With known mu and Sigma, no costs or bounds binding, w* = (gamma Sigma)^{-1} mu. The weight on A is zero iff mu_A - beta'mu_E = 0, with beta = Sigma_EE^{-1} Sigma_EA.
- *Reduction.* The claim's hypotheses are B^A = B^E, c^E = 0, costless uncapped ETF trades, and zero cross-moment between xi_E and epsilon = xi_A - xi_E. They give Cov(r_A, r_E) = Var(r_E), so beta = 1 and the intercept is alpha_bar = 0. A then has the ETF's mean plus uncorrelated noise, so it is dominated, and the costless replacement T(w) shows it. With independent tracking noise, beta < 1 and the intercept is alpha_bar + (1 - beta) E r_E, positive for a positive premium, which is the reviewed counterexample. The funded, long-only and incumbent conditions (A) or (B) make the replacement costless.
- *Verdict: special case.* Bichuch-Guasoni's non-participation is the zero-intercept case. Left over: the funded M2 formulation and the careful hypothesis list.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's line-by-line check, certified four limit cases and attacks (hidden financing, span as feasibility, double drag, belief credit, overstated transfer) are sound; PM reran checks/008 and verified red's noisy-ETF counterexample (cross-moment -1/10000, unique F optimum (1/2,1/2), V_F-V_E=1/40000). Limitation stated here, from red's open scope objection: with independent residuals the zero cross-moment hypothesis forces zero ETF tracking noise, so the result recovers zero-alpha non-participation only for a noiseless, free, uncapped ETF; with tracking noise a zero-alpha fund is held for diversification. Math is asked to reword Not shown accordingly.


Not machine checked. The deterministic core is the explicit funded replacement map, finite
moment and score identities, strict-improvement implications, and four rational examples.
Attainment may use claim 004. The source comparison is prose comparing two models, not an
imported stochastic-control theorem or a claim of machine-checked fidelity to that source.

Lean, 2026-09-27: machine checked. This replaces "Not machine checked" above; the earlier text
is kept as it was written. The statement is in `lean/Standalone/M2ZeroAlphaLimitingCase.lean` and
the proof in `lean/Novel/M2ZeroAlphaLimitingCaseProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used.

General part. It covers any M2 instance with one active fund and one ETF (claim 003's formal
objects), any number of factors, any finite scenario set and any finite belief. The hypotheses
are the claim's additional restrictions, as stated in the Statement: equal loadings, zero drag,
free ETF trading, ETF cap one, belief-mean alpha zero, zero cross-moment
sum_s q_s xi_E,s epsilon_s = 0, and case (A) or (B). Added to these are the M2 restrictions the
proof uses: compliant start, nonnegative active rates, gamma >= 0, nonnegative scenario masses
and belief masses summing to one. Scenario masses summing to one is assumed but unused. Not
assumed: positive gross returns, centered shocks, rates below one, and active limit at most one.

Proved:
- Replacement: for every w in F, T(w) is feasible, has the same exposure and zero review cost,
  satisfies the cash identity, and satisfies
  Qbar_0(T(w)) - Qbar_0(w) = tau + (gamma/2) a^2 v_epsilon >= 0.
- Existence of an F-optimum with a = 0.
- Under (A): T(w) is in E, the F and E optimal values are equal, and every F-optimum has a = 0 if
  kappa^+_A > 0 or gamma v_epsilon > 0.
- Under (B): every F-optimum has a = 0 if gamma v_epsilon > 0, and with a^- > 0 no holding in E
  has a = 0.
- Part 3: pointwise equal returns at every support point and scenario, and the W_1 identity for
  every holding. This part also assumes the compliant start, which the claim fixes.
- Attainment is re-proved (F compact, criterion continuous), not imported from claim 004's proof
  module.

Examples. All four instances are entered literally, and each is shown to satisfy every M2
restriction. Proved: the unique F optimum (0, 1) in case 1; in case 2, the unique F optimum (1, 0),
the unique best zero-active holding (0, 99/100) with its score, and neither (A) nor (B) holding;
in cases 3 and 4, the F maximizers are exactly the feasible a + p = 1; the unique E optimum
(0, 1/4) in case 4 with V_F - V_E = 33/3200; and T(3/4, 1/4) not in F.

Relation to the prose. The comparison with `bichuch2014investing` in Prior art is prose about two
models and has no formal counterpart. No gap found between the formal statement and the Statement.

Scope. The limitation PM recorded at approval applies to the formal result unchanged, because
the cross-moment hypothesis is carried exactly as stated. With independent residuals, that
hypothesis forces zero ETF tracking noise. So the formal result recovers zero-alpha
non-participation only for a noiseless, free, uncapped ETF. Machine checking does not widen that
scope.

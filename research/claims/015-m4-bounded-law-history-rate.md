---
id: 15
title: "A worst-case history-length rate for a funded unspanned-factor trade"
status: formalized
model_version: M4
depends_on: []
axioms_used: []
formal: lean/Standalone/M4BoundedLawRate.lean
direction: D3
---
## Statement

This is a scalar-factor specialization of M4, with worst case over an explicit
class of **known** finite shock laws. The lower bound ranges over full-history
rules, not over M4's ellipsoid gate alone. The upper bound supplies one valid
conservative implementation of that gate. The bounds match in order, not constants.

Fix one active fund and one ETF, initial wealth and cash one, zero risky holdings,
gamma=0, zero ETF drag, active cap bar a in (0,1], and ETF cap one. Purchase rates
kappa_A,kappa_E are in [0,1); sale rates are zero. Fix d>0, mu>kappa_E and H>0
with d H<=1/4. Set

```
B^A=(d,0),                 B^E=(0,1),
q_E=(mu-kappa_E)/(1+kappa_E),
lambda_0=[kappa_A+(1+kappa_A)q_E]/d,
Theta_4={(lambda,mu,0): lambda_0-H<=lambda<=lambda_0+H}.
```

Alpha is known zero and the second premium is known mu. The law class K_H consists
of every finite probability law of a real Z with E Z=0 and |Z|<=H. For each member,
the M4 shock is z^f=(Z,0), z^A=z^E=0. Its exact probabilities and support, and the
resulting risk covariance, are known to the rule before sampling. Each quarter's
public observation is consequently equivalent to x=lambda+Z: factors are (x,mu),
the active return is d x, and the ETF return is mu. No additional public residual
signal is in this class. Quarters are iid; the next holding-quarter draw is
independent, as in M4. These assumptions apply to every result below.

Define the maximum funded active holding and its remaining exposure mismatch by

```
A=min(bar a,1/(1+kappa_A)),       D=d A>0,
w_A=(A, [1-(1+kappa_A)A]/(1+kappa_E)),
v_E=(0,1/(1+kappa_E)).
```

Fix a score margin delta in (0,D H/2] and error allowance epsilon in (0,1/16].
Use eta=epsilon for M4's confidence calibration and delta_econ=delta/4 for its
economic threshold. All choices precede the history.

1. **Funded geometry and target.** Every instance is admissible in M4. The entire
   ETF-only class is optimized uniquely at v_E, with score q_E. For every lambda,

   ```
   Adv(w_A;theta)=D(lambda-lambda_0),
   G_*(theta)=D max(lambda-lambda_0,0).
   ```

   At lambda<lambda_0 every active action has negative Adv. At lambda>lambda_0
   the unique full optimizer is w_A. The first component of the exposure
   difference between w_A and *every* ETF-only action is D, since ETFs cannot
   reach factor 1. Funding and the active cap determine A; costs also set
   lambda_0. No algebraic span argument replaces the funded ETF optimization.

2. **Worst-case lower bound against full-history rules.** Suppose a positive
   integer N_obs has this property: for every known law in K_H there is a rule,
   allowed to use its full public history and independent randomization, which
   certifies a feasible active action or falls back to v_E, satisfying

   ```
   for every theta in Theta_4:
     P_theta(certify and Adv(certified action;theta)<=delta/4) <= epsilon;
   for every theta in Theta_4 with G_*(theta)>=delta:
     P_theta(certify and Adv(certified action;theta)>delta/4) >= 1-epsilon.
   ```

   The rule can differ with the known law, but not with unknown theta. Then

   ```
   N_obs >= [1/(4 pi^2)] (D H/delta)^2 log(1/epsilon).
   ```

   Thus even a rule told the exact law cannot meet both requirements uniformly
   over this class at smaller sample lengths. It is not asserted that each law
   is this hard.

3. **Matching conservative certificate.** For every law in K_H, both requirements
   in part 2 hold whenever

   ```
   N_obs >= 32 (D H/delta)^2 log(2/epsilon).
   ```

   A valid rule uses M4's prescribed C_N, plug-in optimizer and fallback. Define
   r_B=H sqrt(2 log(2/epsilon)/N_obs). If C_N is nonempty and the plug-in optimizer
   is w_A, use the conservative lower certificate

   ```
   ell_N(w_A)=D(lambda_hat_N-r_B-lambda_0).
   ```

   Otherwise return no active certificate. Certify only if ell_N>delta/4.
   The displayed ell_N is a lower bound on M4's **original** L_N(w_A), not a
   replacement confidence-set target. On the coverage event at every alternative
   with G_*>=delta, it is at least delta/2. Empty C_N still forces fallback.

All logarithms are natural. The necessary and sufficient lengths have the same
dependence (D H/delta)^2 log(1/epsilon) up to universal constants, since
log(2/epsilon)<=5 log(1/epsilon)/4 in the stated range. Integer lengths use the
ceiling of a sufficient real bound. This is a worst-case sample-length envelope;
it does not assert that a particular law's gate power increases with every added
observation or equals the optimal full-history power.

## Proof

### 1. Economic reduction, including the whole ETF class

The shock laws are finite and centered by assumption. Since lambda_0>0, the
minimum active gross return over the domain and support is at least
1+d(lambda_0-2H)>1-2dH>=1/2. The ETF gross return is 1+mu>0. The two domain
endpoints give the required finite vertex set. The compliant zero incumbent,
nonnegative caps and rates, and fixed public iid history satisfy M4's remaining
restrictions. Its covariances are Omega=diag(Var Z,0,0) and
Sigma=diag(d^2 Var Z,0); gamma=0 prevents any risk penalty in this specialization.

The exact funding and score formulas are

```
F={(a,p): 0<=a<=bar a, 0<=p<=1,
             (1+kappa_A)a+(1+kappa_E)p<=1},
E={ (0,p): 0<=p<=1/(1+kappa_E) },
Q((a,p);theta)=a(d lambda-kappa_A)+p(mu-kappa_E).
```

Because mu-kappa_E>0, for each a in [0,A] the unique best ETF holding is
p=[1-(1+kappa_A)a]/(1+kappa_E), which belongs to [0,1]. Substitution gives

```
max over funded p Q((a,p);theta) = q_E+a d(lambda-lambda_0).
```

The ETF maximum is the a=0 case. Maximizing this affine expression over [0,A]
proves the optimizer and gap formulas, including strict negativity of Adv for
every a>0 at lambda<lambda_0. At equality lambda=lambda_0 the lexicographic
optimizer is v_E. The same formulas apply to an unprojected estimate outside the
domain because Q is affine in its parameter. The exposure map is b(a,p)=(d a,p),
giving the stated mismatch against every v in E.

### 2. A finite centered hard law with overlapping full histories

Put Delta=delta/D and m=floor(H/Delta)+1. Then m>=3 and (m-1)Delta<=H. Let
phi=pi/(m+1), u_i=sin(i phi), S_m=sum_{i=1}^m u_i^2, and choose the single known law

```
Z_i=2 Delta [i-(m+1)/2],     q_i=u_i^2/S_m,     i=1,...,m.
```

All u_i are positive. Reflection i -> m+1-i preserves q_i and changes the sign
of Z_i, so the law is centered. Its support is bounded by H and its masses sum
to one. It is therefore in K_H. This law depends on the prespecified margin,
not on the unknown parameter or observed data. Use it unchanged at
lambda_-=lambda_0-Delta and lambda_+=lambda_0+Delta, both in the fixed domain.
At the former all certified active actions would be false, and at the latter
the oracle gap is exactly delta.

The two scalar observation supports are shifted by one grid step 2 Delta.
Their common atoms pair q_i from one law with q_{i+1} from the other. Full public
observations are injective deterministic functions of the scalar observation,
with no extra signal, so the same overlap applies to the full records. Their
one-record affinity (sum of square roots of paired probability masses) is

```
sum_{i=1}^{m-1} sqrt(q_i q_{i+1}) = cos(phi).
```

To verify the identity, set u_0=u_{m+1}=0 and use
u_{i-1}+u_{i+1}=2 cos(phi) u_i. Multiplying by u_i and summing gives
2 sum_{i=1}^{m-1} u_i u_{i+1}=2 cos(phi) S_m. Division by 2 S_m proves it.
For N_obs independent records, finite product expansion makes the affinity
cos(phi)^{N_obs}, even when histories outside the common support are included
with zero mass from the other law.

### 3. Testing bound, proved on the finite histories

Let P and Q be the negative- and positive-parameter history laws on their finite
union of supports. A randomized certification rule gives each history a number
g in [0,1], its conditional probability of certification. At lambda_- all active
certification is false, so sum P g<=epsilon. The required correct-certification
probability at lambda_+ implies sum Q(1-g)<=epsilon. Hence

```
2 epsilon >= sum [P g+Q(1-g)] >= sum min(P,Q) = 1-TV(P,Q),
TV(P,Q) = (1/2) sum |P-Q|.
```

Write aff=sum sqrt(P Q). Factoring |P-Q| and applying the finite Cauchy-Schwarz
inequality gives

```
TV(P,Q) <= (1/2) sqrt[sum(sqrt(P)-sqrt(Q))^2
                          * sum(sqrt(P)+sqrt(Q))^2]
         = sqrt(1-aff^2).
```

The finite inequality itself follows by expanding a nonnegative sum of squares;
no probability theorem is imported. Combining the inequalities, using
1-2 epsilon>0, and inserting the computed product affinity yields

```
cos(phi)^(2 N_obs) <= 4 epsilon(1-epsilon),
N_obs >= log[1/(4 epsilon(1-epsilon))]/[-2 log cos(phi)].
```

For 0<=x<=pi/4, sec(x)^2<=2, so integration gives tan(x)<=2x and then
-log cos(phi)=integral_0^phi tan(x) dx<=phi^2. This applies since m>=3.
Also m+1>=H/Delta. Finally epsilon<=1/16 implies
4 epsilon(1-epsilon)<=4 epsilon<=sqrt(epsilon). Therefore the last lower bound
is at least

```
(m+1)^2/(2 pi^2) * log[1/(4 epsilon(1-epsilon))]
 >= (H/Delta)^2/(4 pi^2) * log(1/epsilon).
```

The hard law was one of the laws for which the hypothesized rule had to work,
so this proves part 2 with the stated worst-case quantifiers. The proof covers
arbitrary feasible certified actions, not only the witness w_A.

### 4. Bounded-mean calibration bound without an imported concentration theorem

For any law in K_H and any real t, convexity of exp on [-H,H] bounds exp(tZ)
by the chord joining its endpoint values. Averaging and using E Z=0 gives
E exp(tZ)<=cosh(tH). The power series and (2j)!>=2^j j! imply
cosh(x)<=exp(x^2/2). Independence and finite product expansion therefore give

```
E exp[t sum_l Z_l] <= exp(N_obs t^2 H^2/2).
```

For a>0 and t>0, retaining only outcomes with sum_l Z_l>=N_obs a in this finite
expectation bounds their probability by exp(-t N_obs a+N_obs t^2 H^2/2).
Taking t=a/H^2 gives exp(-N_obs a^2/(2H^2)); replacing Z by -Z gives the lower
tail. Adding the two bounds yields

```
P(|lambda_hat_N-lambda|>=a) <= 2 exp[-N_obs a^2/(2 H^2)].
```

This is supporting bounded-mean mathematics, derived here in finite sums and not
claimed as novel.

If Var Z>0, M4's statistic is T_N=N_obs e_N^2/Var Z, with all errors in the
first coordinate. Write r_N=sqrt(t_{N,epsilon} Var Z/N_obs). Its calibration is
exactly the first discrete absolute-error radius whose coverage is at least
1-epsilon. The preceding tail bound at a=r_B implies r_N<=r_B. Its quantile
definition also proves P(|e_N|<=r_N)>=1-epsilon. Intersecting the confidence
interval with the known parameter domain does not change whether the true
parameter is included. If Var Z=0, every positive-mass Z is zero (a finite sum
of nonnegative q_i Z_i^2 vanishes), so r_N=0, the estimate is exact and coverage
is one. This handles all laws, including degenerate ones.

### 5. Valid certificate and uniform power envelope

For nonempty C_N its least first coordinate is
max(lambda_0-H,lambda_hat_N-r_N). Since r_N<=r_B and Adv(w_A;theta) is increasing
in lambda, the displayed ell_N(w_A) is at most the infimum defining L_N(w_A).
On the coverage event, L_N(w_A)<=Adv(w_A;theta). Any certification with
ell_N>delta/4 is thus correct on this event, simultaneously for every history
where it is made. Elsewhere the probability is at most epsilon, proving uniform
false-certification control. The policy never uses a nonempty-set convention
to authorize a trade on an empty C_N.

Under the sufficient length bound r_B<=delta/(4D). At any true parameter with
G_*>=delta, the geometric identity gives lambda-lambda_0>=delta/D. On coverage,
|lambda_hat_N-lambda|<=r_N<=r_B and C_N is nonempty. In particular
lambda_hat_N>lambda_0, so the actual plug-in optimizer is w_A, and

```
ell_N(w_A) >= D(lambda-lambda_0-2r_B) >= delta/2 > delta/4.
```

The certified action has true Adv>=delta, so it is a correct certification.
The coverage event has probability at least 1-epsilon for each law and parameter,
which proves the required uniform power. No monotonicity or optimality of M4's
gate was used; only a sufficient length envelope and its exact coverage event.

## Checks

`checks/015/check.py` checks the funded optimizer algebra and cap/funding cases,
constructs finite hard laws and verifies their centering, bounded support and
one- and two-record full-observation affinities exactly. It also checks a
conservative certificate on an exactly enumerated binomial history law using a
rational radius and no simulated coverage. These finite checks supplement, and
do not replace, the paper proof's arbitrary-law, arbitrary-margin quantifiers.

## Not shown

- Matching *order* only; the constants are loose, and the lower bound need not
  hold for an individual easy law. The adverse law can vary with the prespecified
  margin. The class allows arbitrarily many finite support points, exact real
  observations and known laws. No stability to rounding or unknown laws is proved.
- This is one uncertain factor and known zero alpha. The active fund supplies an
  unspanned factor, not manager skill. It shows a premium-information requirement
  despite exact alpha knowledge in this family; it does not establish a general
  multivariate separation of alpha and premium uncertainty.
- gamma=0, the ETF return is deterministic, sales are absent from the chosen
  all-cash incumbent, and the entire ETF optimum has a closed form. Positive
  purchase costs and a binding active cap are allowed; arbitrary incumbents,
  risk aversion, a moving ETF comparator or general exposure geometries are not
  covered. There is no calibrated economic magnitude or market-arbitrage claim.
- The upper rule is a valid conservative implementation, not a power benchmark.
  It retains exact finite calibration to check C_N and may require combinatorial
  work. No general polynomial-time algorithm or numerical-rounding certificate
  is supplied. All bounds refer to one fixed review; no repeated-live-testing
  or terminal-wealth conclusion follows.
- The rate is standard scalar mean-testing behavior. The specific result is its
  finite known-law worst case with an explicit full-history lower bound, funded
  ETF-class optimization, and a validated lower bound for M4's original L_N.
  This does not establish publication novelty or settle D3's kill criterion.

## Prior art

Checked the D3 source-level comparison in FINDINGS, the registered passages of
`petrik2016safe`, `esfahani2017data`, `manski1999statistical` and
`olivaresnadal2018technical`, existing claims (especially 014), the refuted directory
and experiments 005 and 007's failed conjectures. Shared-parameter robust regret,
coverage protection, bounded-outcome sampling bounds and uncertainty penalties are
already prior art. The scalar testing rate and the finite affinity argument are
not asserted to be new techniques. All inequalities used here are proved above;
no literature theorem is imported as an assumption.

The claim specifies the full likelihood class, supplies a centered finite hard law
even when its law is known, and maps its mean separation to the exact advantage
over the whole funded ETF class through D. Thus the lower bound is not inferred
from an ellipsoidal penalty or a covariance identity alone. Its conservative
upper certificate bounds the original optimized-comparator target, including
M4's empty-set rule. Whether this scalar benchmark is sufficient progress toward
a new D3 contribution remains a separate scientific judgement.

## Open objections

None raised yet. Red should check the known-law quantifier order, the shifted
finite-support affinity, the entire ETF optimization with purchase costs, and
that the upper certificate really bounds M4's unchanged L_N including empty sets.

## Review

**Red, 2026-09-28.** I checked every step by hand, tested each part numerically with my own code, and then probed the claim's scope.

**Hand check: every step holds.**
- *Part 1.* With gamma = 0 and an all-cash start, Q = a(d lambda - kappa_A) + p(mu - kappa_E) on F = {0 <= a <= bar a, 0 <= p <= 1, (1 + kappa_A)a + (1 + kappa_E)p <= 1}. Because mu > kappa_E, p = [1 - (1 + kappa_A)a]/(1 + kappa_E) is optimal and lies in [0, 1]. This gives q_E + a d(lambda - lambda_0), so the ETF-class supremum is q_E, and the gap formulas and the unique optimizers follow. The active gross return is at least 1 + d(lambda_0 - 2H) > 1/2.
- *Part 2.* delta <= DH/2 gives H/Delta >= 2, so m >= 3, and (m - 1)Delta <= H bounds the support. The shift lambda_+ - lambda_- = 2 Delta pairs q_i with q_{i+1}. With u_0 = u_{m+1} = 0, the recurrence u_{i-1} + u_{i+1} = 2 cos(phi) u_i gives an affinity of exactly cos(phi), and the product rule gives cos^{N_obs}(phi). At lambda_- every active certification is false, and at lambda_+ the gap is exactly delta.
- *Part 3.* sum |P - Q| = sum |sqrt P - sqrt Q|(sqrt P + sqrt Q) <= 2 sqrt(1 - aff^2), and 1 - 2 epsilon <= TV. Together they give cos^{2N}(phi) <= 4 epsilon(1 - epsilon). On [0, pi/4], sec^2 <= 2, so tan x <= 2x and -log cos(phi) <= phi^2, with phi <= pi/4 since m >= 3. Then m + 1 > H/Delta, and 4 epsilon <= sqrt(epsilon) for epsilon <= 1/16. The final constant 1/(4 pi^2) is correct.
- *Quantifier order.* The rule may depend on the known law but not on theta, and the proof uses only the hard law's rule, so this is a worst case over K_H. That is correct, and the power requirement's "Adv > delta/4" only strengthens what is used.
- *Part 4.* The chord bound gives E exp(tZ) <= cosh(tH) <= exp(t^2 H^2/2), and r_B makes the two-sided tail exactly epsilon. For r_N <= r_B: P(|e| < r_B) >= 1 - epsilon, so the first support radius with coverage >= 1 - epsilon lies below r_B. The Var Z = 0 case is handled.
- *Part 5.* Omega = diag(Var Z, 0, 0), and the mu- and alpha-estimates are exact. So C_N is an interval in lambda with lower end max(lambda_0 - H, lambda_hat - r_N) >= lambda_hat - r_B. sup_E Q = q_E does not depend on theta, so L_N(w_A) is the infimum of D(lambda - lambda_0) over C_N, which is at least ell_N. An empty C_N gives no certificate. With N_obs >= 32(DH/delta)^2 log(2/epsilon), r_B <= delta/(4D). The plug-in optimizer is then w_A on the coverage event and ell_N >= delta/2. The constant comparison log(2/epsilon) <= (5/4) log(1/epsilon) needs epsilon <= 1/16, which holds.

**Independent numerics** (red's own script, written without reading `checks/015/check.py`).
- *Funded geometry.* On 300 random exact instances (d, both purchase rates, mu, bar a including binding caps, lambda on both sides of lambda_0), a vertex enumeration of F and E gives sup_E Q = q_E and G_* = D max(lambda - lambda_0, 0) exactly.
- *Hard laws.* For m = 3..8 they are centered, bounded by (m - 1)Delta, and have affinity cos(pi/(m + 1)) to 1e-12.
- *Exact optimal test.* A Neyman-Pearson test by likelihood-ratio ordering on count classes shows the smallest N_obs allowing both errors <= epsilon. It is 5 (m = 3, epsilon = 1/16), 7 (m = 4, 1/16) and 10 (m = 3, 1/100), against affinity bounds of 2.09, 3.42 and 4.66 and stated bounds of 0.28, 0.63 and 0.47. So the lower bound is valid but loose.
  - *Clarified 2026-09-28 after the auditor's note.* These minima are over all full-history rules. For iid records the count vector over the union support is sufficient, and the likelihood ratio prod_i (q_{i-1}/q_i)^{c_i} depends on the whole count vector, not only on the summed grid index.
  - *Recheck at 40 digits (mpmath).* The optimal full-history type II errors are 0.043457 at (m, N) = (3, 5), 0.062382 <= 1/16 at (4, 7), and 0.006314 <= 1/100 at (3, 10). They are 0.101562 at (3, 4). So 5, 7 and 10 stand.
  - *Tests on the summed index alone* are not sufficient here and need 5, 8 and 11, which is the auditor's computation. At (4, 7) and (3, 10) their best type II errors are 0.0848 and 0.0166.
  - *Either way* every length lies above the affinity and stated lower bounds.
- *Upper side.* With Rademacher Z and N_obs set to the claim's sufficient value, M4's exact discrete calibration gives r_N/H = 0.090, 0.045, 0.099 and 0.050, all below r_B/H = 0.125, 0.0625, 0.125 and 0.0625. Coverage is 0.948, 0.942, 0.991 and 0.991, and r_B <= delta/(4D) in all four cases.
- *Claim's own check.* It passes.

**Attacks that did not succeed.**
- Quantifier reversal (the law chosen after the rule): the rule is per law, and the bound is a worst case.
- Overlap overstated by an extra public signal: the class has none, and observations are injective in x.
- The ETF comparator replaced by one selected action: the whole E class is optimized.
- A certificate bounding a replacement set: ell_N bounds M4's original L_N, and an empty C_N falls back.
- A degenerate law: Var Z = 0 gives exact estimates.

**Scope (sharpenings).**
1. **The funded geometry enters only as a unit conversion.** With Delta = delta/D, the rate is scalar mean testing in premium units, N ≍ (H/Delta)^2 log(1/epsilon). D converts a score margin into a factor-premium margin. The Not shown says the rate is standard. The paper should state it this way rather than as a portfolio-specific rate.
2. **The constants are far apart.** 1/(4 pi^2) ≈ 0.025 against 40, a factor of about 1600. My exact tests put the true minimal N_obs 10-20 times above the lower bound for small m. "Matching order" is correct and nothing more.
3. **The worst case needs support size growing like DH/delta.** For laws with a fixed support size, exact identification can hold, as in claim 014, and the rate need not apply. That is consistent with "not asserted that each law is this hard".
4. **Unspanned factor, not alpha, again.** As in claims 012-014, "active" means the only factor-1 vehicle with known zero alpha, so this certifies a premium, not manager skill. The Not shown says so.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* The sample complexity of certifying, at error epsilon, that a bounded-noise mean exceeds a threshold by a margin Delta is Theta((H/Delta)^2 log(1/epsilon)), worst case over bounded laws.
- *General result.* Minimax testing rates: the Le Cam two-point lower bound through Hellinger affinity, and the Hoeffding upper bound. The same rate appears as the one-arm case of best-arm-identification lower bounds (for example Mannor-Tsitsiklis).
- *Reduction.* The hard pair is two lattice laws with affinity cos(phi), which is Le Cam. The certificate is Hoeffding's interval. The portfolio enters only through D, which converts the score margin to a mean margin Delta = delta/D, as red's Review noted.
- *Verdict: special case.* Left over: the funded ETF-class optimization that gives D.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check of all five parts (whole funded ETF-class optimization with purchase costs, hard-law affinity cos(pi/(m+1)), the Hellinger-to-TV lower bound and its constant, per-law quantifier order, the sub-Gaussian upper certificate bounding M4's original L_N with empty-set fallback) and independent numerics (300 exact geometry instances, exact Neyman-Pearson minimal lengths, M4's exact calibration on the upper side) are sound, and PM reran checks/015; no open objections. Limits stated: the rate is standard scalar mean testing in premium units, with the funded geometry D entering only as a unit conversion; lower and upper constants differ by about 1600x (matching order only); the worst case needs support size growing like DH/delta; known zero alpha, so this certifies a premium through an unspanned factor, not manager skill.


Not machine checked. The probability calculations are finite sums and products,
not measure-theoretic asymptotics. The core includes real-valued bounds, a finite
sine-weight identity, elementary exponential and trigonometric inequalities,
and the funded affine optimization. No field equivalent to the rate result is
assumed; the hard distribution and conservative certificate are constructed.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4BoundedLawRate.lean` and the proof
in `lean/Novel/M4BoundedLawRateProof.lean`. `lake build` and the axiom audit pass (standard axioms
only). No hypothesis structure or cited result is used, and no rate or tail bound is assumed.

Formal objects. M4 comes from the formal definitions in `lean/Standalone/M4InformationObstruction.lean`
(claim 014's statement file), which formalize `model/SPEC.md` on claim 003's M2 objects. Only
definitions are shared, not claim 014's results, and no proof module is imported. Rules are those
of that file: each full history maps to a probability measure on actions, which covers any
independent randomization.
- The family is entered literally, with gamma = 0, zero sale rates, caps (bar a, 1), z^f = (Z, 0)
  and z^A = z^E = 0.
- A law in K_H is a finite scenario type with masses q >= 0 summing to one, E Z = 0 and |Z| <= H
  at every scenario point. Every law in K_H has such a representation, for example its support.
- A rule meets the requirements when it certifies a feasible action with a > 0 or falls back to
  v_E, has false-certification probability (Adv <= delta/4) at most epsilon at every theta in
  Theta_4, and has probability at least 1 - epsilon of a certification with Adv > delta/4 at every
  theta in Theta_4 with G_* >= delta.

Proved, for every input in the stated ranges:
1. Admissibility, Theta_4 = {(lambda, mu, 0) : |lambda - lambda_0| <= H}, the explicit F, E and Q,
   and D > 0. v_E is the unique ETF-class optimizer with value q_E. For every lambda,
   Adv(w_A) = D(lambda - lambda_0) and G_* = D max(lambda - lambda_0, 0). Every feasible active
   action has negative Adv below lambda_0, and w_A is the unique full optimizer above it. The
   first-exposure difference between w_A and every ETF-only action is D.
2. If at length N_obs >= 1 every law in K_H admits a rule meeting both requirements, then
   N_obs >= (DH/delta)^2 log(1/epsilon)/(4 pi^2). The hypothesis is quantified law by law, so the
   rule may depend on the known law but not on theta.
3. For every law in K_H and every N_obs >= 32 (DH/delta)^2 log(2/epsilon), the rule meets both
   requirements. That rule is M4's C_N (eta = epsilon), plug-in optimizer and the certificate
   ell_N = D(lambda_hat - r_B - lambda_0) with threshold delta/4. When C_N is nonempty and the
   plug-in optimizer is w_A, ell_N is at most M4's original L_N(w_A). On the coverage event at every
   alternative with G_* >= delta it is at least delta/2. M4's plug-in fallback equals v_E on every
   possible history.
4. log(2/epsilon) <= (5/4) log(1/epsilon) for epsilon in (0, 1/16].

The proof.
- Part 1 writes Q on F as q_E + a d(lambda - lambda_0) minus the unused funding slack times
  (mu - kappa_E), which gives every optimizer and gap formula.
- Part 2 uses the paper's sine-weighted grid law. Its common atoms at lambda_0 +- delta/D pair
  scenario j + 1 with j, and the affinity identity sum u_j u_{j+1} = cos(phi) S_m follows from the
  sine recurrence. The testing step differs from the paper: instead of the total-variation bound
  it uses sum min(P, Q) >= affinity^2/2 (finite Cauchy-Schwarz), giving cos(phi)^(2 N_obs) <=
  4 epsilon. The paper's own last step already weakens its bound to 4 epsilon, so the stated
  constant is unchanged. Then -log cos(phi) <= phi^2 follows from cos x >= 1 - x^2/2 and
  log y >= 1 - 1/y, in place of the paper's tangent integral.
- Part 3 proves the bounded-mean tail on finite histories: the chord bound for exp,
  cosh x <= exp(x^2/2), and the finite product expansion. The pseudoinverse acts on the range of
  Omega through the first Penrose equation, and the case Var Z = 0 is handled separately. The
  discrete quantile's own definition gives coverage at least 1 - epsilon. A positive-mass history
  with |mean error| < r_B that maximizes T_N shows t_{N,epsilon} <= N r_B^2/Var Z, so every error
  in A_{N,epsilon} has first coordinate at most r_B.

Relation to the prose. No gap was found between the formal statement and the Statement. The
limits PM recorded at approval apply unchanged. The rate is standard scalar mean testing in
premium units, with the funded geometry D entering only as a unit conversion. The lower and upper
constants differ by about 1600x, so the bounds match in order only. The worst case needs support
size growing like DH/delta. Alpha is known zero, so this certifies a premium through an unspanned
factor, not manager skill.

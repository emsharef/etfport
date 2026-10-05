---
id: 17
title: "Quadratic entry changes the history rate in economic advantage"
status: formalized
model_version: M4
depends_on: [16]
axioms_used: []
formal: lean/Standalone/M4CurvedEntryRate.lean
direction: D3
---
## Statement

Fix s in (0,1/100]. Specialize M4 to one active fund and one ETF, cash and
wealth one, zero risky incumbent, caps one, zero shareholder costs and ETF drag,
B^A=(1,0), B^E=(0,1), and gamma=1/s^2. Let

```
c=(0,1/4,0),            Theta_4=c+s[-1,1]^3,
K_s={known finite laws of U: E U=0, E U U'=I_3, ||U||_2<=9},
(z^f_1,z^f_2,z^A)=s U, z^E=0.
```

Thus K_s is claim 016's class K_J for J=s I_3, with a different parameter domain
and positive risk aversion. The domain and exact law are known before sampling;
theta=(lambda_1,lambda_2,alpha) is fixed and unknown. The full public record is
equivalent to X=(f_1,f_2,r^A-f_1)=theta+s U, with r^E=f_2. Use M4's iid histories,
unprojected estimator, exact confidence calibration, original L_N and empty-set
fallback. Omega=s^2 I_3 and the realized risky-return covariance is
Sigma=diag(2s^2,s^2); they have different roles and are never added.

1. **Continuous ETF adjustment and a shrinking active trade.** Write
   x=lambda_1+alpha and x_+=max(x,0). Throughout Theta_4 the unique optimizers are

   ```
   v_E(theta)=(0,lambda_2),   w_F(theta)=(x_+/2,lambda_2),
   sup_E Q=lambda_2^2/2,     G_*(theta)=x_+^2/4.
   ```

   They satisfy all position and cash constraints, with strict funding slack.
   The ETF optimum varies continuously with the unknown premium. For every
   feasible w=(a,p), its advantage over the whole ETF class is exactly

   ```
   Adv((a,p);theta)=a x-a^2-(p-lambda_2)^2/2.
   ```

   If x<0 every active action is worse than that class. At advantage delta>0
   the smallest positive mean signal is 2 sqrt(delta), and its optimal active
   holding is sqrt(delta). Both the trade and its paired mean-error exposure
   vanish at entry. The error of implementing an estimated ETF holding is
   separately the quadratic term (p-lambda_2)^2/2.

2. **Matching order in economic advantage.** Fix delta in (0,s^2/128] and
   epsilon in (0,1/16]. Set eta=epsilon and delta_econ=delta/4. Suppose that for
   every known law in K_s there exists a full-history rule, possibly randomized
   with an independent coin, which certifies a funded active action or falls
   back to a funded ETF-only action, and satisfies

   ```
   for all theta in Theta_4:
     P_theta(certify and Adv(certified action;theta)<=delta/4) <= epsilon;
   for all theta in Theta_4 with G_*(theta)>=delta:
     P_theta(certify and Adv(certified action;theta)>delta/4) >= 1-epsilon.
   ```

   The rule can depend on the known law, not unknown theta. Necessarily

   ```
   N_obs >= [s^2/(32 pi^2 delta)] log(1/epsilon).
   ```

   Conversely M4's plug-in rule with the conservative certificate below meets
   both requirements for every law in K_s whenever

   ```
   N_obs >= 768 (s^2/delta) log(6/epsilon).
   ```

   The worst-case order is therefore (s^2/delta) log(1/epsilon), for fixed s as
   delta decreases. The exponent in economic advantage is one here, compared
   with two in claims 015-016's linear, fixed-size entry constructions. This is
   a different risk-averse family, not an improvement to their stated bounds or
   a general assertion that risk aversion reduces data needs. Constants are loose.

3. **Certificate including the estimated ETF adjustment.** On every
   positive-probability history put

   ```
   x_hat=lambda_hat_1+alpha_hat,
   a_hat=max(x_hat,0)/2,     p_hat=lambda_hat_2,
   rho_N=s sqrt(t_{N,epsilon}/N_obs).
   ```

   The full plug-in optimizer is w_hat_F=(a_hat,p_hat), and the fallback is
   v_hat_E=(0,p_hat). Both are funded. For nonempty C_N a valid bound for the
   original optimized-class target is

   ```
   ell_N(w_hat_F)=a_hat*x_hat-a_hat^2-sqrt(2)*a_hat*rho_N-rho_N^2/2
                <= L_N(w_hat_F).
   ```

   Empty C_N forces fallback. Use the active action only when a_hat>0 and this
   bound is strictly greater than delta/4. On coverage it cannot falsely
   certify. If G_*>=delta and rho_N<=sqrt(delta)/8, then ell_N>=5 delta/8;
   hence the correct-certification probability is at least 1-epsilon under the
   sufficient length in part 2. Removing the rho_N^2/2 term is not justified by
   merely comparing with the selected ETF holding: the target optimizes that
   holding at the same unknown true theta.

## Proof

### Admissibility and complete funded optimization

The domain is a finite-vertex box. The active mean x lies in [-2s,2s] and its
shock s(U_1+U_3) has magnitude at most 9 sqrt(2)s. Its gross return is at least
1-(2+9 sqrt(2))s>1-20s>=4/5. The ETF mean is in [1/4-s,1/4+s] and its shock has
magnitude at most 9s, so its gross return is at least 5/4-10s>0. This holds
at every vertex and scenario, hence on the full box. Centering and E U U'=I_3
give the stated Omega and Sigma for every law in the class.

The funded classes and strictly concave score are

```
F={(a,p):a>=0,p>=0,a+p<=1}, E={(0,p):0<=p<=1},
Q((a,p);theta)=a x+p lambda_2-a^2-p^2/2.
```

Completing squares in p and in a when x>0 gives part 1. In detail,
lambda_2 in [1/4-s,1/4+s] is strictly between zero and one, so the unique ETF
maximum is at p=lambda_2. The unrestricted nonnegative active maximum is at
a=x_+/2<=s. Their sum is at most 1/4+2s<1. Thus the separately maximizing
coordinates are jointly funded; uniqueness follows from strict concavity.
Subtracting lambda_2^2/2 gives the stated advantage for every feasible holding.
When x<0 and a>0, both a x and -a^2 are negative, and the last square cannot
offset them. The advantage formula is against the entire optimized ETF class.

Every sample mean obeys ||U_bar||<=9. Consequently

```
3/20 <= lambda_hat_2 <= 7/20,
x_hat <= (2+9 sqrt(2))s <16s,
0 <= a_hat <= 8s <= 2/25.
```

Thus the plug-in maximizers also lie strictly within the cash constraint on
every positive-mass history, even if theta_hat_N lies outside Theta_4. This
justifies their formulas without projecting the estimator. The fixed law has
finite support, so rules may use ETF fallback on any off-support input history;
the assertions concern histories possible at some theta in the domain.

### Lower bound: a mean separation of order sqrt(delta)

Use claim 016's normalized finite sine construction, with

```
k=floor(s/(4 sqrt(2 delta)))>=2, m=4k-1, phi=pi/(4k),
q_i=sin^2(i phi)/(2k), z_i=i-2k, V=sum_i q_i z_i^2,
W_i=z_i/sqrt(V), a_k=1/(2 sqrt(V)),
h=(1,0,1)/sqrt(2), v_1=(0,1,0), v_2=(1,0,-1)/sqrt(2).
```

That construction proves, by finite trigonometric sums and reflection,
E W=0, E W^2=1, k^2/16<=V<=4k^2, |W|<=8 and
1/(4k)<=a_k<=2/k<=1. For completeness, the variance lower bound counts the
indices k through floor(3k/2) and their reflections: at least k indices, each
of mass at least 1/(4k) and squared displacement at least k^2/4. The upper bound
uses |z_i|<2k. Normalization follows from sum sin^2(i phi)=2k.

Take independent uniform signs S_1,S_2 and U=h W+v_1 S_1+v_2 S_2. Its covariance
is I_3 and ||U||^2=W^2+2<=66<81. Use the same known finite law under

```
theta_-=c-a_k s h,     theta_+=c+a_k s h.
```

They lie in the box since a_k<=1. Their active mean signals are respectively
-sqrt(2)s a_k and +sqrt(2)s a_k. Thus all active actions are bad at theta_-,
while

```
G_*(theta_+)=s^2 a_k^2/2 >= s^2/(32 k^2) >= delta.
```

Both endpoints have lambda_2=1/4. The lower bound does not need the ETF optimum
to move between this pair; the overall parameter domain and the upper bound
allow it to move. This is a lower bound from active entry, not an assertion that
ETF-mean uncertainty alone imposes that rate.

Give a testing rule the latent observation (W-a_k,S_1,S_2) or
(W+a_k,S_1,S_2). The common map
c+s(h y+v_1 s_1+v_2 s_2) produces X and therefore all public fund and factor
returns. The overlapping grid supports differ by one step; their one-record
affinity is cos(phi), since
sum sqrt(q_i q_{i+1})=cos(phi). This identity follows by multiplying the adjacent
sine recurrence by sin(i phi) and summing with zero endpoints, as in claim 016.
Independent signs leave affinity unchanged, and product histories have affinity
cos(phi)^N_obs.

Every public rule satisfying part 2 has probability of certification at most
epsilon at the negative endpoint and at least 1-epsilon at the positive one.
For its certification probability g in [0,1], finite summation gives
sum[P g+Q(1-g)]>=1-TV(P,Q), while Cauchy-Schwarz gives
TV(P,Q)<=sqrt(1-aff(P,Q)^2). Thus

```
cos(phi)^(2 N_obs) <= 4 epsilon(1-epsilon),
N_obs >= (4k)^2 log(1/epsilon)/(4 pi^2).
```

The second inequality uses 4 epsilon(1-epsilon)<=sqrt(epsilon) and
-log cos(phi)<=phi^2 (integrate tan(t)<=2t up to pi/4). Finally
k>=s/(8 sqrt(2 delta)), giving the claimed s^2/(32 pi^2 delta) constant.
The law may depend on the prescribed margin but is the same at both unknown
parameters; all covariances and economic inputs are fixed across the law class.

### Original-target certificate and false-certification control

Here Omega=s^2 I_3, so M4's error ellipsoid is exactly the Euclidean ball of
radius rho_N. Its discrete calibration gives coverage at least 1-epsilon,
independent of theta, because the true theta belongs to the box and
theta_hat_N-theta=s U_bar. Empty C_N cannot occur on coverage.

For each theta in nonempty C_N, Cauchy-Schwarz gives
|x-x_hat|<=sqrt(2)rho_N and |lambda_2-p_hat|<=rho_N. Insert both inequalities
in the exact advantage from part 1 at (a_hat,p_hat). Since a_hat>=0, this yields
Adv>=ell_N uniformly over C_N; taking the infimum proves ell_N<=L_N. This step
retains the oracle ETF optimum inside the advantage. If the gate certifies on
coverage, its implemented active action has true advantage greater than delta/4.
False certification is therefore at most epsilon at every domain parameter.

Suppose next that G_*>=delta and rho_N<=sqrt(delta)/8. Then x>=2 sqrt(delta).
On coverage x_hat>=2 sqrt(delta)-sqrt(2)rho_N>0, and
a_hat>=sqrt(delta)-rho_N/sqrt(2). In this case

```
ell_N=a_hat^2-sqrt(2)rho_N a_hat-rho_N^2/2.
```

This polynomial is increasing in a_hat for a_hat>=rho_N/sqrt(2); our lower
bound exceeds that value. Evaluating at the lower bound gives

```
ell_N >= delta-2 sqrt(2)rho_N sqrt(delta)+rho_N^2
      >= delta-3 rho_N sqrt(delta) >= 5 delta/8 > delta/4.
```

Thus every covered alternative is correctly certified, including its estimated
ETF adjustment. This bound controls both the linear paired-error term, which
shrinks with a_hat, and the quadratic ETF error term. It bounds their maxima
separately; it does not establish that their sum is an unavoidable penalty.

### A uniform sufficient sample length

For any coordinate Y of U, E Y=0, E Y^2=1 and |Y|<=9. As in claim 016, expand
the exponential series. For |t|<=1/18,

```
E exp(tY) <= 1+(t^2/2) sum_{r>=2}(9|t|)^(r-2) <= exp(t^2).
```

The bound uses E|Y|^r<=9^(r-2), and absolute convergence follows from bounded
support. Independence, the elementary exponential tail bound with t=b/2 and
its negative version give P(|Y_bar|>=b)<=2 exp(-N_obs b^2/4) for 0<b<=1/9.
For N_obs>=324 log(6/epsilon), choose b=2 sqrt(log(6/epsilon)/N_obs).
A union bound over three coordinates shows that
N_obs ||U_bar||^2<=12 log(6/epsilon) with probability at least 1-epsilon.
The first finite support quantile consequently obeys
t_{N,epsilon}<=12 log(6/epsilon).

Under the sufficient length of part 2, s^2/delta>=128 ensures the preceding
sample condition, and

```
rho_N^2 <= 12s^2 log(6/epsilon)/N_obs <= delta/64.
```

The previous part proves correct power at least 1-epsilon. This is a sufficient
envelope for every law, not monotonicity or optimality of the exact gate.

## Checks

`checks/017/check.py` checks funded quadratic optimization and the whole-class
advantage algebra, plug-in feasibility at extremal observation bounds, the hard
pair's covariance and score gap, and exact finite-history certificates including
the ETF estimation term. The checks are not the arbitrary-law sample-length proof.

An exact follow-up in that script uses independent sign shocks, N_obs=64,
epsilon=1/16 and the balanced-history estimate equal to the true parameter
(9s/16,1/4,9s/16). The calibrated radius is 3s sqrt(13)/32, and the entire ball
is inside Theta_4. Direct global minimization gives
L_N/s^2=(162-27 sqrt(26))/512>1/512, while the stated conservative bound is
ell_N/s^2=(531-108 sqrt(26))/2048<0. Thus the exact original-target gate can
certify this positive-probability history at delta=s^2/128 while the bound in
part 3 abstains. The calculation and factorization are recorded in FINDINGS;
this is a finite supporting check, not a new rate or a change to the Statement.

## Not shown

- Known finite shock laws, stationary public histories, known exposures and risk
  covariance, and one review only. No recommendation for actual history length,
  estimated loadings, unknown laws or rounded observations is established.
- All shareholder costs are zero and funding is slack at the relevant optima.
  Risk is positive and the ETF comparator moves continuously, but there is no
  active/ETF risk cross-covariance. The additive risk score makes the two optimal
  coordinates separable in this box; a binding-budget or correlated-risk rate is
  not covered. This is an M4 specialization, not a change to its frozen definition.
- The rate is worst-case over K_s; the hard support grows as s/sqrt(delta).
  Constants are loose. Fixed laws can be easier, as claim 014 warns, and the gate
  need not attain their optimal power. Neither constant improvements nor a
  computationally efficient exact-quantile algorithm is shown.
- Alpha and the unspanned premium enter through x=lambda_1+alpha. The result does
  not separate manager skill from compensation for that factor. Both estimation
  errors are nonzero in this family; no new exact-alpha limit is asserted.
- The changed exponent follows quadratic entry geometry, not a new statistical
  testing method. Risk aversion is normalized as gamma=1/s^2, so varying s changes
  risk aversion as well as the shock scale; the delta-rate comparison holds s
  fixed. No general cross-model ranking of required samples follows.
- The weak selected-ETF target is not claimed to fail at a particular probability
  here. The algebra identifies the additional whole-class penalty; experiment
  010 reports a separate fixture exhibiting such failure.

## Prior art

Read the current D3 FINDINGS comparisons, claims 014-016 and their limitations,
the empty refuted directory, and the registered full-text passages of
`petrik2016safe` (Definition 2 and its shared-model fixed-baseline comparison),
`esfahani2017data` (Theorems 3.4-3.5's calibrated uncertainty and finite-sample
protection), and `manski1999statistical` (Section 3.3's mean-gap-dependent expected
welfare bounds). These do not by themselves identify the economic-margin
exponent for this funded quadratic-entry certificate. None is imported as an
axiom or needed for the proof.

Quadratic optimization, shrinking local estimation exposure and conversion of a
mean-testing rate into a loss rate are standard in kind. The contribution here
is the explicit change in D3's economic-advantage rate once the optimal active
holding shrinks at entry, with a matching full-history lower bound and a valid
original-target certificate that pays for an estimated, continuously moving ETF
adjustment. It is a restricted structural comparison with claims 015-016, not a
priority claim for fast statistical rates or a publication anchor by itself.

## Open objections

None raised yet. Red should check the economic-margin conversion, the hard
pair's domain membership, uniform plug-in feasibility, and the certificate's
ETF estimation term before anyone builds on this result.

## Review

**Red, 2026-09-28.** I checked every step by hand, ran my own numerical checks, and then probed the claim's scope.

**Hand check: every step holds.**
- *Score.* The active shock is s(U_1 + U_3) and the ETF shock is sU_2, with E U U' = I, so Sigma = diag(2s^2, s^2) and gamma Sigma = diag(2, 1). That gives Q = ax + p lambda_2 - a^2 - p^2/2. The ETF optimum is p = lambda_2, in (0, 1), and the active optimum is a = x_+/2 <= s. Their sum is below 1/4 + 2s < 1, so both are funded, and Adv = ax - a^2 - (p - lambda_2)^2/2 against the whole optimized ETF class.
- *Admissibility.* 2s + 9 sqrt(2)s < 20s <= 1/5 for the active return, and 1/4 - 10s > 0 for the ETF.
- *Plug-in feasibility.* lambda_hat_2 is in [3/20, 7/20] and a_hat <= 8s on every positive-mass history, so the plug-in formulas need no projection.
- *Lower bound.* delta <= s^2/128 is exactly what gives k >= 2. |a_k h_i| <= a_k/sqrt(2) <= 1 keeps theta_± in the box. The signal is (1, 0, 1).(± a_k s h) = ± sqrt(2) s a_k. G_*(theta_+) = s^2 a_k^2/2 >= s^2/(32k^2) >= delta, because k <= s/(4 sqrt(2 delta)). The latent map c + s(h y + v_1 s_1 + v_2 s_2) reproduces X. With k >= s/(8 sqrt(2 delta)), (4k)^2/(4 pi^2) gives s^2/(32 pi^2 delta).
- *Certificate.* Omega = s^2 I makes C_N a Euclidean ball of radius rho_N, so |x - x_hat| <= sqrt(2) rho_N and |lambda_2 - p_hat| <= rho_N. With a_hat >= 0 this gives ell_N <= L_N, and it keeps the oracle ETF term (p_hat - lambda_2)^2/2. An empty C_N falls back.
- *Power.* At x_hat = 2 a_hat, ell_N = a_hat^2 - sqrt(2) rho a_hat - rho^2/2, which is increasing for a_hat >= rho/sqrt(2). At a_hat = sqrt(delta) - rho/sqrt(2) it equals delta - 2 sqrt(2) rho sqrt(delta) + rho^2 >= 5 delta/8 when rho <= sqrt(delta)/8. The constant 768 gives rho^2 <= 12 delta/768 = delta/64, and s^2/delta >= 128 makes N_obs >= 324 log(6/epsilon) automatic.

**Independent numerics** (red's own script, written without reading `checks/017/check.py`).
- *Optimization.* On 300 random theta in the box, the formulas for sup_F, sup_E and Adv match brute force over 20,000 random funded points each.
- *Hard pair.* On 1000 random (s, delta) with delta <= s^2/128: k >= 2, theta_± lie in the box, the signal is exactly sqrt(2) s a_k, and G_*(theta_+) >= delta.
- *Power algebra.* Over a grid of delta and rho <= sqrt(delta)/8, the smallest value of ell/delta at the extremal a_hat is 0.662, above 5/8.
- *Exact finite histories.* With U uniform on {±1}^3 (in K_s), s = 1/100, N_obs = 4 and 8, and two values of delta, there is no false certification at any x_* on a grid. At these lengths rho_N ≈ s, so the gate never certifies. The check therefore confirms validity only; the claim's own 64-record check supplies nonzero power.
- *Claim's own check.* It passes.

**Scope (sharpenings).**
1. **The changed exponent is a unit conversion, as the Not shown says.** In mean-signal units mu = 2 sqrt(delta), the rate is (s/mu)^2 log(1/epsilon), the same scalar mean-testing rate as in claims 015-016. At a quadratic entry G_* = x^2/4, so the economic margin is second order in the signal, and delta^{-1} replaces delta^{-2}. The comparison with claims 015-016 is across different maps from margin to signal: there, a fixed-size trade gives an advantage linear in the signal. The paper should say "at a smooth entry the advantage is quadratic in the signal" rather than "risk aversion halves the exponent".
2. **Risk aversion is tied to the shock scale** (gamma = 1/s^2, so gamma Sigma = diag(2, 1)). The rate's s^2 factor is therefore not a pure shock-scale effect, and s cannot be varied independently of preferences, as the Not shown notes.
3. **Constants are about 4 x 10^5 apart:** 768 x 32 pi^2 x log(6/epsilon)/log(1/epsilon).
4. **The margin still loads on x = lambda_1 + alpha,** so skill and the unspanned premium are not separated, as stated.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* When the optimal value is smooth (quadratic) in the parameter at the decision boundary, decision loss is quadratic in estimation error, so a loss margin delta needs order sigma^2/delta samples instead of sigma^2/delta^2.
- *General result.* Fast rates for plug-in decisions under smooth value or margin conditions (Audibert-Tsybakov for plug-in classifiers; Hirano-Porter local asymptotics for treatment rules). Equivalently, a mean-testing rate (sigma/mu)^2 composed with the margin map delta = mu^2/4.
- *Reduction.* G_* = x_+^2/4 at quadratic entry. The lower bound is claim 016's direction-wise Le Cam in mean units, and the certificate pays linear and quadratic error terms. Red's Review made the same reduction.
- *Verdict: special case.* Left over: the explicit funded instance with a moving ETF optimum.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check (whole-ETF-class score with a continuously moving ETF optimum, admissibility, plug-in feasibility without projection, the hard pair and its constant, the Euclidean-ball certificate keeping the ETF-estimation term and bounding M4's original L_N, the power algebra) and independent numerics (300 brute-force optimizations, 1000 hard pairs, exact finite histories) are sound, and PM reran checks/017; no open objections. Limits stated: the changed exponent in economic advantage is a unit conversion (at a smooth entry the advantage is quadratic in the mean signal, so in signal units the rate is the same scalar testing rate as claims 015-016; not 'risk aversion halves the exponent'); gamma is tied to the shock scale (gamma=1/s^2); constants about 4x10^5 apart; skill and the unspanned premium remain loaded together.


Not machine checked. Finite probability sums, quadratic optimization, the
normalized sine law and explicit exponential bounds form the core. The proof
uses claim 016's reviewed construction; it does not assume a rate as a hypothesis.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4CurvedEntryRate.lean` and the proof
in `lean/Novel/M4CurvedEntryRateProof.lean`. `lake build` and the axiom audit pass (standard axioms
only). No hypothesis structure or cited result is used, and no rate or tail bound is assumed.

Formal objects. M4 comes from claim 014's statement file, the requirement predicates from claim
015's, and K_s (claim 016's `InKJ`) and the rule restriction `AdmitsJ` from claim 016's. The proof
imports claim 016's proof module, as Q-04 allows for depends_on [16]. The family is entered
literally, with gamma = 1/s^2 and shocks s U. Rules map each full history to a probability measure
on actions. The gate implements M4's plug-in optimizer when C_N is nonempty, that optimizer is
funded, a_hat > 0 and ell_N > delta/4; otherwise it implements M4's plug-in fallback. The funding
condition is part of M4's gate.

Proved, for s in (0, 1/100]:
1. Admissibility; Theta_4 is exactly the box c + s[-1, 1]^3; Omega = s^2 I and
   Sigma = diag(2s^2, s^2); F, E and Q = a x + p lambda_2 - a^2 - p^2/2. On Theta_4:
   - the unique ETF and full optimizers (0, lambda_2) and (x_+/2, lambda_2);
   - sup_E Q = lambda_2^2/2 and G_* = x_+^2/4, with strict funding slack;
   - the whole-class advantage a x - a^2 - (p - lambda_2)^2/2 of every holding, and negative
     advantage below entry;
   - G_* >= delta exactly when x >= 2 sqrt(delta), with active holding sqrt(delta) at G_* = delta.
2. Lower bound N_obs >= s^2 log(1/epsilon)/(32 pi^2 delta); upper bound for every law at
   N_obs >= 768 (s^2/delta) log(6/epsilon).
3. On every history from the domain, M4's plug-in optimizer is the funded (a_hat, p_hat) and its
   fallback the funded (0, p_hat). For nonempty C_N, ell_N <= L_N(a_hat, p_hat). On coverage with
   G_* >= delta and rho_N <= sqrt(delta)/8, ell_N >= 5 delta/8.

The proof.
- Omega = s^2 I, and the first Penrose equation forces Omega^dagger = I/s^2. So C_N is the
  Euclidean ball of radius rho_N, giving |x - x_hat| <= sqrt(2) rho_N and
  |lambda_2 - p_hat| <= rho_N.
- The plug-in bounds come from coordinate averages: |U_bar_2| <= 9 and |U_bar_1 + U_bar_3| <= 13.
- The lower bound reuses claim 016's latent law (claim 015's sine grid on 4k - 1 points, with
  E W^2 = 1 and k^2/12 <= V <= 4k^2) along h = (1, 0, 1)/sqrt(2), completed by a Householder
  reflection. Claim 016's logarithm step is applied with sigma = s and margin sqrt(2 delta).
- The upper bound reuses claim 016's variance-based tail and quantile lemmas, with
  t_{N,epsilon} <= 12 log(6/epsilon) since T_N = N ||U_bar||^2 here.
- The lower bound's hypothesis s <= 1/100 is used, via funding slack at the hard parameters.

Relation to the prose. No gap was found between the formal statement and the Statement. The limits
PM recorded at approval apply unchanged:
- the changed exponent in economic advantage is a unit conversion (at a smooth entry the
  advantage is quadratic in the mean signal, so in signal units the rate is the same scalar
  testing rate as claims 015-016);
- gamma is tied to the shock scale;
- the constants are about 4x10^5 apart;
- skill and the unspanned premium remain loaded together.

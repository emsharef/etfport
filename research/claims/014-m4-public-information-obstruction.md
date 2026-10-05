---
id: 14
title: "Equal portfolio geometry and covariances can hide different certification information"
status: formalized
model_version: M4
depends_on: []
axioms_used: []
formal: lean/Standalone/M4InformationObstruction.lean
direction: D3
---
## Statement

This is an assumed finite-law counterexample within M4, with a sharp statistical
benchmark and an exact comparison to M4's prescribed gate. It is not a claim that
the benchmark rules implement M4's particular confidence set.

Use one active fund and one ETF, initial cash and wealth one, zero risky incumbent,
position limits one, all four shareholder cost rates zero, gamma=1, c^E=0,
B^A=(0,0), B^E=(1,0), and

```
Theta_4 = {(1/80,0,alpha): -1/10 <= alpha <= 1/10}.
```

Thus both factor premia are known and only alpha is unknown. In each quarter draw
three independent uniform signs (s,t,u); quarters are iid as M4 requires. Compare
two known shock laws, denoted I (independent residual) and R (revealing residual):

```
                 z^f           z^A             z^E
I                (0,0)         s/10            t(3-u)/20
R                (0,0)         s/10            t(3-s)/20.
```

Each law has the same eight equally weighted scenario labels; repeated observation
values in R are combined when evaluating probabilities. Both laws are centered.
Observations are the full public factor and fund-return history specified in M4.
In particular the observed ETF residual is r^E-1/80. Let theta_+ and theta_- be
the domain endpoints with alpha=1/10 and -1/10, respectively. Take delta_econ=0.

1. **Same economics and covariance.** Both are admissible M4 instances. Both have
   Omega=diag(0,0,1/100), Sigma=diag(1/100,1/40), the same marginal distribution of
   each instrument return at every theta, and the same full public-observation
   covariance. They have identical F, E, b, Q, G_*, and distributions of
   theta_hat_N at each theta and sample length. Explicitly,

   ```
   F={(a,p): a>=0, p>=0, a+p<=1},   E={(0,p): 0<=p<=1},
   Q((a,p);theta)=a alpha+p/80-a^2/200-p^2/80,
   sup_E Q = 1/320, attained uniquely at (0,1/2).
   ```

   At theta_- every active trade (a>0) has strictly negative Adv, and G_*=0.
   At theta_+ the unique full optimum is w_A=(1,0), with
   Adv(w_A;theta_+)=G_*(theta_+)=147/1600. For any alpha,
   Adv(w_A;theta)=alpha-13/1600. Thus the null and alternative refer to the whole
   optimized ETF-only class under the same funded budget, not to cash alone.

2. **Sharp full-history benchmark.** Fix any N_obs>=1 and eta in (0,1).
   A benchmark rule reads the full history and may use an independent random coin.
   It either certifies a feasible action with a>0, or falls back to (0,1/2).
   Require, for every theta in Theta_4,

   ```
   P_theta(certify and Adv(certified action;theta)<=0) <= eta.
   ```

   Probability includes the independent randomization when used. Write P^max_I
   and P^max_R for the suprema of certification probability at theta_+ over these
   rules, with the known law I or R, respectively. Then the suprema are attained:

   ```
   P^max_I = min(1, 1-2^(-N_obs)+eta),
   P^max_R = 1.
   ```

   The attaining rules always certify w_A, whose true advantage at theta_+ is
   positive; their power does not come from falsely certifying a bad action there.
   Consequently a certification probability at least 1-beta at theta_+, for
   beta in [0,1], is possible in I exactly when 2^(-N_obs)<=eta+beta, whereas R
   allows probability one after a single record with no false certification.
   These are sharp bounds over the whole domain's uniformly valid rules, not only
   rules whose validity is required at the two endpoints.

3. **The prescribed M4 gate discards the distinction.** M4's C_N, L_N, plug-in
   candidates and exact-gate decision (ell_N=L_N) are functions of theta_hat_N
   with the same definitions in I and R. Their distributions therefore agree at
   every theta and N_obs. At N_obs=1, every eta in (0,1), and theta_+, the exact
   M4 gate certifies with probability exactly 1/2 in both models. In R this loses
   half the certification probability available from its full public history.
   At eta=1/4, the corresponding full-history benchmarks are 3/4 in I and 1 in R.

Thus these identical funded exposure sets, scores, return covariances and
sample-mean error distributions cannot determine an instance's optimal
full-history certification power. They *do* determine the prescribed gate here.
The distinction concerns the information retained by that gate, not a failure of
its coverage. The corrected lower-bound object is the full observable history law
at parameters requiring conflicting actions; covariance and exposure mismatch alone
do not specify that law.

## Proof

### Admissibility and optimization over every ETF action

All signs have mean zero. In I the active and ETF residuals are independent. In R
their covariance is zero because the independent sign t has mean zero even after
s is fixed. In both laws E[(z^A)^2]=1/100 and
E[(z^E)^2]=((1/10)^2+(1/5)^2)/2=1/40. Factors are deterministic, giving the stated
Omega, Sigma and public-observation covariance. The ETF residual is uniformly
distributed on {-1/5,-1/10,1/10,1/5} in both laws. The active residual is uniform
on {-1/10,1/10}; only their joint dependence differs. All fund gross returns are
positive: the active gross return is at least 4/5 throughout Theta_4, and the ETF
gross return is at least 1+1/80-1/5=13/16. The domain is the convex hull of its
two endpoints. The zero incumbent is compliant; fees vanish and the cash
constraint is 1-a-p>=0. These facts verify all M4 primitive restrictions.

Substitution in Q gives part 1's formula. Over E,

```
Q((0,p);theta) = 1/320 - (2p-1)^2/320,
```

so the asserted ETF supremum and unique optimizer follow on the entire interval.
At theta_-, Q((a,p);theta_-)=Q((0,p);theta_-)-a/10-a^2/200.
The action (0,p) remains funded whenever (a,p) is funded, so all a>0 have Adv<0,
and the full optimum equals the ETF optimum. At theta_+, for any feasible (a,p),

```
Q(w_A;theta_+)-Q((a,p);theta_+)
 = (1-a)/10-(1-a^2)/200-p/80+p^2/80
 >= (1-a)(1/10-1/100-1/80)
 = (31/400)(1-a).
```

Here 1+a<=2 and p<=1-a. The last expression is positive unless a=1, which
forces p=0. This proves unique full optimality and the stated gaps by subtraction.
For arbitrary alpha the same subtraction at w_A gives alpha-13/1600. No selected
ETF action is silently substituted for the supremum; its optimization was just
solved exactly.

### Lower bound for law I using the full public history

Under theta_+, an active return is either 0 or 1/5. Under theta_-, it is either
-1/5 or 0. Hence the intersection of the two full-history supports consists
exactly of histories with every active return zero. Call this event Z_N.
Its probability under either endpoint is 2^(-N_obs). In I, the public ETF return
history is independent of the active shocks and has the same law at both
endpoints, and the factors are identical. Thus every observable history in Z_N
has *the same probability mass* at the two endpoints, not merely positive mass
at both. Independent randomization of a rule preserves this equality of event
probabilities on Z_N.

Every certification at theta_- is false by the preceding optimization. Uniform
validity therefore gives P_{theta_-}(certify intersect Z_N)<=eta. Equality of
the restricted laws makes the same bound true at theta_+. Outside Z_N, the
certification probability at theta_+ is at most 1-2^(-N_obs). Adding and also
using the bound one proves P^max_I<=min(1,1-2^(-N_obs)+eta), regardless of the
chosen funded active action or use of ETF observations.

### An attaining rule valid at every alpha, and law R

Write x for an observed active return. In I, whenever x>0 the only parameter
in [-1/10,1/10] consistent with x is alpha=x-1/10; whenever x<0 it is
alpha=x+1/10. Indeed the alternative sign would place alpha outside that domain.
Every nonzero return thus identifies alpha exactly. If a history has a nonzero
return, use its inferred alpha (all such inferences agree on any possible
history), and certify w_A exactly when alpha>13/1600. Otherwise fall back.
On an impossible or inconsistent history define fallback, to make the rule total.

If every active return is zero, toss an independent coin with certification
probability min(1,eta 2^{N_obs}); certify w_A if it succeeds and otherwise fall
back. Such a history is possible only at alpha=+-1/10. At the negative endpoint
its false-certification probability is
2^(-N_obs) min(1,eta 2^{N_obs})=min(2^(-N_obs),eta)<=eta.
At the positive endpoint the action is truly advantageous. At every interior
alpha there is no ambiguous history, so the rule never falsely certifies.
The rule is therefore uniformly valid over the continuum Theta_4. At theta_+
it certifies on all nonambiguous histories plus the stated fraction of Z_N,
attaining min(1,1-2^(-N_obs)+eta).

In R, a single public ETF residual identifies the active shock sign:
|r^E-1/80|=1/10 means s=1, whereas magnitude 1/5 means s=-1.
The same record therefore identifies alpha=r^A-s/10 exactly, for *every* alpha
in the domain. Certifying w_A exactly when this value exceeds 13/1600 is
uniformly free of false certification and always certifies at theta_+.
Fallback on inconsistent histories again defines a total rule. All the rules
used here are measurable: their decision regions use finitely many equalities,
inequalities and arithmetic operations, and the optional coin is independent.

The attaining rules also admit confidence-set certificates of the proposal's
strong form, using sets different from M4's fixed ellipsoid. In I, use the exact
identified-parameter singleton off Z_N. On Z_N use {theta_+} if the coin succeeds,
and all of Theta_4 otherwise. In R, use the exactly identified singleton. On
inconsistent histories take the empty set and fall back. Under every true
parameter in either law these alternative sets contain it with probability at
least 1-eta: the only possible exclusion on a positive-mass history is the
negative endpoint in I on a successful ambiguous-history coin, of probability
min(2^(-N_obs),eta). Minimizing Adv(w_A;theta) over these sets yields a positive
value exactly on the certification events described above. In particular the
benchmark can achieve its bounds with valid lower certificates against the whole
ETF class for these alternative sets. These are comparison constructions, not
a change to the C_N specified by M4.

The beta condition follows by rearranging the attained expression for P^max_I;
R attains one. The general overlapping-support argument is an elementary testing
bound proved here, not an imported literature assumption.

### Exact comparison with M4's selected confidence set

In both laws X_l=(1/80,0,alpha+s_l/10), with iid uniform s_l. Its full joint
history distribution, hence the distribution of theta_hat_N, is the same at any
fixed alpha. Omega and the complete finite law of e_N and T_N are also the same,
so t_{N,eta}, A_{N,eta} and C_N as functions of theta_hat_N coincide. Since the
economic Q, F and E coincide, their lexicographic plug-in selections and L_N
also coincide as functions of the estimate. M4's baseline gate with ell_N=L_N
therefore has identical distributions in the two models; it does not inspect
the ETF residual magnitudes that distinguish R.

For one record, e_N=(0,0,+-1/10), Omega^dagger=diag(0,0,100), so T_N=1 surely
and t_{N,eta}=1 for every eta in (0,1). Thus A has alpha coordinate [-1/10,1/10].
At theta_+, the estimated alpha is 0 or 1/5 with equal probability. When it is
0, C_N is all of Theta_4 and contains theta_-, where every active action has
negative Adv. Therefore no positive lower certificate exists for an active
action; moreover the plug-in full optimizer itself is (0,1/2), since at alpha=0
any a>0 strictly reduces Q. When estimated alpha is 1/5, C_N={theta_+}.
The same full-optimum inequality above with 1/10 replaced by 1/5 makes w_A
the unique plug-in optimizer. Its exact lower certificate is 147/1600>0.
The gate therefore certifies exactly half the time. This calculation concerns
the actual optimized-comparator L_N, not a local minimization incumbent.

For interpreting the one-record loss, at theta_+ the gate already certifies every
history outside Z_N in I. The benchmark's additional probability eta (when
eta<=1/2) comes entirely from certifying on a fraction of Z_N, whose observable
law is identical at theta_-. It therefore spends the allowed false-certification
budget there. No extra identification of a nonzero return accounts for this gain:
those histories were already certified. In fact the overlap argument with zero
allowed false certification bounds any I rule's power by 1/2, attained by the
gate. At eta=1/4 the 1/4 gap between I's and R's optimal benchmarks measures their
different full-history information; the full 1/2 gap between R's benchmark and
the gate should not all be attributed to the I/R dependence difference. This
decomposition is specific to the stated error allowance and favorable endpoint.

## Checks

`checks/014/check.py` independently aggregates exact full-observation laws,
checks covariance and the funded objective algebra, and solves the finite
endpoint testing allocation by exact likelihood-ratio ordering. It checks the
sharp benchmark for N_obs=1,2,3 and three error levels, verifies the attaining
rules on endpoints and interior alpha values (including the exact break-even
value), and checks the one-record M4 gate. These are finite exact checks, not
a substitute for the all-N_obs, all-eta and all-alpha paper proof.

The review follow-up independently optimizes Q over each face of the funded
triangle, calibrates the discrete error law, and minimizes Adv over the resulting
confidence interval. At eta=1/4 and theta_+, it gives the following exact values
in both I and R:

| N_obs | t_{N,eta} | Alpha error radius | Gate certification probability | Coverage probability | Empty-C_N probability |
|---|---|---|---|---|---|
| 1 | 1 | 1/10 | 1/2 | 1 | 0 |
| 2 | 2 | 1/10 | 1/4 | 1 | 0 |
| 3 | 1/3 | 1/30 | 3/4 | 3/4 | 1/8 |

These finite diagnostics confirm red's non-monotonicity observation; they do not
extend the numbered statement to a general sample-size power formula. For N_obs=3
the all-positive-shock history has estimated alpha 1/5 and an empty C_N, so the
gate falls back despite exact full-history identification. The one-record check
also verifies that all of I's benchmark gain at eta=1/4 occurs on Z_N, and equals
its false-certification probability at theta_-.

## Not shown

- No realistic information rate, magnitude or empirical conclusion. The known
  discrete law and exact real-valued observations permit exact identification;
  rounding, measurement error or unknown shock laws can destroy it. No stability
  to such perturbations is proved. The missing information in I is endpoint
  ambiguity, with probability 2^(-N_obs), not a root-N estimation barrier.
- The benchmark permits any uniformly valid full-history certification rule,
  including independent randomization. It is intentionally broader than M4's
  fixed C_N/plug-in/ell_N gate. The attaining benchmark rules are not approved
  replacements for that prescribed portfolio policy. A statistical lower bound
  over this larger class also constrains its subclasses; its matching upper
  bound need not be attained by the M4 gate, as part 3 explicitly shows.
- Only alpha is unknown. Factors are deterministic and Omega has rank one,
  although risky-return Sigma is positive definite. The result does not separate
  uncertain premia from alpha, quantify unspanned-factor estimation, or claim a
  general optimized-comparator computation. The whole ETF optimization is solved
  here and yields a fixed optimizer across theta; a moving comparator is not the
  mechanism. Costs are zero and caps one; no positive-cost extension is proved.
- The difference is dependence in *public* ETF observations, not information
  bought by holding the ETF. No ambiguity-aversion preference is added. The
  scores are one-quarter conditional mean-variance scores; no realized-wealth,
  Bayesian-posterior or repeated-review guarantee follows.
- The total benchmark-to-gate loss in R is not wholly the I/R dependence effect.
  At one record, I's gap instead uses a positive false-certification allowance
  on ambiguous histories, while the discrete-quantile gate has coverage one.
  Additional records need not monotonically increase that gate's power; the
  finite diagnostics above show a decrease from one to two records. The gate
  is not an optimal-power benchmark.
- The counterexample excludes an exact instance-wise power characterization
  based only on the listed covariance/geometry quantities. It does not exclude
  conservative bounds, or a worst-case result over a separately specified class
  of shock laws. Nor does it establish the roadmap's general matching-rate target
  or settle its kill criterion.

## Prior art

Checked the registered full texts compared in the 2026-09-28 FINDINGS source-level
entry, the existing claims, the empty refuted directory and the failed cases in
experiments 005 and 007. `petrik2016safe` already uses shared-model robust baseline
regret and has tightness and hardness results; `olivaresnadal2018technical` already
gives the norm-penalty/robust equivalence. `esfahani2017data` supplies selected-
action protection from coverage, and `manski1999statistical` bounds expected
welfare loss of specified empirical rules. No such result is imported here.

The claim is neither a new support-function penalty nor the elementary implication
from coverage. Its specific content is the pair of admissible M4 laws with the
same economic and covariance objects, different sharp full-history bounds against
the entire funded ETF class, and an exact power loss of the prescribed gate.
The support-overlap proof is elementary statistical testing, not a claimed new
testing technique. No broader priority claim is made; generic information-loss
phenomena are not new. Whether this stylized obstruction is useful enough to
anchor D3 remains for independent review and PM's direction assessment.

## Open objections

None. Red corrected review scope item 1 on 2026-09-28: I's one-record gap comes
entirely from using the permitted false-certification budget on Z_N, as the proof
clarification and exact follow-up show. The attribution issue is resolved; the
reported powers and approved numbered statement are unchanged.

## Review

**Red, 2026-09-28.** I checked every step by hand and reproduced the results in exact arithmetic, then attacked the claim's scope.

**Hand check: every step holds.**
- *The two laws.* In I the ETF residual t(3-u)/20 is uniform on {±1/10, ±1/5} and independent of s. In R, t(3-s)/20 has the same marginal but its magnitude reveals s, and it is uncorrelated with s/10 because E[t] = 0. So Omega = diag(0, 0, 1/100) and Sigma = diag(1/100, 1/40) in both. The minimum gross returns are 4/5 and 13/16.
- *Scores.* Q((0, p)) = (p - p^2)/80 = 1/320 - (2p - 1)^2/320. At theta_-, Q = Q((0, p)) - a/10 - a^2/200. At theta_+, Q(w_A) - Q(a, p) >= (1 - a)(1/10 - 1/100 - 1/80) = (31/400)(1 - a). Adv(w_A; alpha) = alpha - 1/200 - 1/320 = alpha - 13/1600, which equals 147/1600 at theta_+.
- *Upper bound for I.* Active returns are {0, 1/5} under theta_+ and {-1/5, 0} under theta_-. Every history in Z_N has mass 2^{-N_obs} times the same ETF-history mass at both endpoints, because in I the ETF history is independent of s. Every certification at theta_- is false. So P_{theta_+}(certify) <= 1 - 2^{-N_obs} + eta.
- *Attaining rule.* A nonzero active return x identifies alpha as x - 1/10 or x + 1/10, since the other sign leaves the domain. Z_N is possible only at the endpoints. The coin's false-certification probability at theta_- is min(2^{-N_obs}, eta), and at the break-even alpha = 13/1600, Adv = 0 gives no certification. In R, |r^E - 1/80| reveals s, so alpha = r^A - s/10 exactly.
- *The M4 gate at N_obs = 1.* T = 1 surely, so t = 1 and the alpha-radius is 1/10. At theta_+ the plug-in estimate is 0 or 1/5. At 0, C_N = Theta_4 contains theta_-, and the plug-in optimum (0, 1/2) is not active anyway. At 1/5, C_N = {theta_+} and w_A is certified with L_N = 147/1600. So the gate certifies exactly half the time, and it is a function of theta_hat_N alone in both laws.

**Independent exact check** (red's own script, written without reading `checks/014/check.py`). I enumerated full public-record laws for N_obs = 1, 2, 3 and eta in {1/10, 1/4, 1/2}, in both laws.
- The claim's attaining rule has false certification <= eta at seven alphas: both endpoints, 0, -1/20, 1/20, the break-even 13/1600 and 13/1600 + 10^{-6}. Its power at theta_+ equals the claimed min(1, 1 - 2^{-N_obs} + eta) in I, and 1 in R.
- Separately, the endpoint-only relaxation, maximizing P_+ subject to P_-(certify) <= eta and solved by likelihood-ratio ordering, returns exactly the same value. So the bound is sharp even against rules that only need to be valid at theta_-.
- I recomputed the M4 gate exactly (finite quantile, exact C_N interval, exact plug-in maximizer and L_N): 1/2 at N_obs = 1 in both laws. The claim's own check also passes.

**Scope (sharpenings; neither changes the verdict).**
1. **Two sources of loss, only one of them the I/R dependence** (corrected 2026-09-28 after math's note). At N_obs = 1 and eta = 1/4 the gate gives 1/2 and the benchmarks 3/4 (I) and 1 (R).
   - *The first quarter of R's loss is also present in I, but it is not a support-identification loss.* At theta_+ the gate already certifies every history off Z_N, where the estimated alpha is 1/5. The benchmark's extra 1/4 comes entirely from the coin on Z_N, whose law is shared with theta_-. That spends false-certification probability exactly eta at theta_-, whereas M4's discrete quantile has coverage one at N_obs = 1. So it is error allowance the gate leaves unused. The earlier version of this item wrongly attributed it to the gate ignoring the finite translated support.
   - *Support identification does cost power from N_obs = 2 on.* My exact split, at eta = 1/4 in I, of benchmark minus gate:
     - N_obs = 2: 1/2 off Z_N (mixed-sign histories reveal alpha = 1/10, but the gate's interval [0, 1/10] contains non-advantageous alphas) plus 1/4 of unused allowance on Z_N;
     - N_obs = 3: 1/8 off Z_N (the empty-set history of item 2) plus 1/8 on Z_N.
   - *Only the second quarter at N_obs = 1,* the gap between the I and R benchmarks, comes from the uncorrelated but dependent public ETF residual. The claim's content is that part, and part 3's "loses half" should not be attributed wholly to it.
2. **The gate's power is not even monotone in N_obs.** At eta = 1/4 and theta_+, my exact computation gives 1/2, 1/4 and 3/4 for N_obs = 1, 2, 3. At N_obs = 3, the history with all active shocks positive has estimated alpha 1/5 and T = 3 > t = 1/3, so C_N is empty and the gate falls back. Yet that history reveals alpha = 1/10 exactly. This is not a defect of the claim. It is further evidence, within M4's own estimator, of the information-discarding the claim identifies, and the paper should not present the ellipsoid gate as a power benchmark.
3. **Novelty is limited, as the claim says.** That second moments do not determine the likelihood is generic. The M4-specific content is the exact pair of admissible laws with identical economics and covariance objects, the sharp full-history bounds against the whole funded ETF class, and the exact gate comparison. Whether that anchors D3 is PM's judgement.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Two sampling models with identical means, covariances and decision geometry can have different likelihoods, so different optimal test power. A procedure that uses only the sample mean and the covariance cannot distinguish them.
- *General result.* Testing power is governed by the full likelihood, through Neyman-Pearson and the total variation or Hellinger distance between history laws (Le Cam). Second moments determine the likelihood only in Gaussian-type families, and outside exponential families the sample mean is not sufficient.
- *Reduction.* Laws I and R share Omega, Sigma and the law of the sample mean but differ in their joint law, because the ETF residual's magnitude reveals the active shock's sign in R. The benchmark bounds are Neyman-Pearson computations on the full records.
- *Verdict: special case,* realized in an explicit M4 instance. Left over: the instance and its exact gate comparison.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check (identical second moments of laws I and R, the upper bound for I, the uniform attaining rule, the M4 gate at N_obs=1) and independent exact enumeration for N_obs=1-3 and three etas (validity at seven alphas, endpoint-only sharpness, exact gate power) are sound, and PM reran checks/014; no open objections. Limits stated: a stylized finite-law obstruction whose novelty is generic (second moments do not determine the likelihood); the M4 gate's loss has two sources, and only the I-versus-R gap comes from dependence in the public ETF residual; the gate's power is not monotone in N_obs, so it is not a power benchmark; no rate, magnitude or stability to rounding or unknown laws.


Not machine checked. The core can be expressed as finite distributions on sign
histories, a finite overlap mass, and funded quadratic inequalities. Optional
randomization needs only a Bernoulli probability on each finite history. The
continuous alpha domain enters the explicit identification formulas and uniform
validity argument; no measure-theoretic asymptotic result is used.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4InformationObstruction.lean` and the
proof in `lean/Novel/M4InformationObstructionProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used, and no claim is imported.

M4. The statement file formalizes M4 from `model/SPEC.md`, reusing claim 003's M2 objects (`Data`,
`ret`, `covariance`, `score` = Q, `F`, `E`, `exposure` = b, `maximizers`):
- the admissibility restrictions and Theta_4 = conv V_4;
- the public record (f, r^A, r^E), iid histories and their law, the estimate theta_hat_N (not
  projected), zeta, and Omega;
- Omega^dagger, defined as the matrix satisfying the four Penrose equations;
- e_N, T_N, and t_{N,eta} (the first positive-mass support value of T_N with accumulated mass at
  least 1 - eta);
- A_{N,eta} with the range restriction, C_N, Adv, G_*, and L_N (in the extended reals, with
  -infinity on an empty C_N);
- the lexicographically smallest plug-in maximizers, and the exact gate (ell_N = L_N) with its
  implemented action.
The two laws are entered literally on the eight labels (s, t, u), and Theta_4 is conv{theta_+,
theta_-}.

Benchmark rules. A rule maps each full history to a probability measure on actions, carried by
the fallback (0, 1/2) and the feasible actions with a > 0. This covers any independent
randomization, including randomizing which action is certified, so it is at least as broad as the
prose's coin. Validity is required at every theta in Theta_4.

Proved:
1. Both laws are admissible. Theta_4 is exactly {(1/80, 0, alpha) : |alpha| <= 1/10}, Omega =
   diag(0, 0, 1/100) and Sigma = diag(1/100, 1/40) in both. Every instrument return has the same
   marginal law at every theta, and the public-record covariance is the same at every theta. F, E,
   b, Q and G_* coincide, and theta_hat_N has the same law for every theta and N_obs. The explicit
   F, E and Q, sup_E Q = 1/320 with (0, 1/2) its unique maximizer, the theta_- facts, the unique
   theta_+ optimum w_A with Adv = G_* = 147/1600, and Adv(w_A; (1/80, 0, alpha)) = alpha - 13/1600
   for every real alpha all hold for both laws.
2. For every N_obs >= 1 and eta in (0, 1), the certification powers of valid rules at theta_+ have
   greatest element min(1, 1 - 2^(-N_obs) + eta) in I and 1 in R. Both are attained by rules that
   certify only w_A, and R's rule never certifies falsely at any theta in Theta_4. For beta in
   [0, 1], power at least 1 - beta is attainable in I exactly when 2^(-N_obs) <= eta + beta.
3. C_N, L_N, the plug-in candidates, the gate's certification and its action are the same
   functions of the estimate in both laws, and theta_hat_N reads identical data. So the joint law
   of the gate's certification and action agrees at every theta, N_obs and eta. At N_obs = 1 and
   theta_+ the gate certifies with probability exactly 1/2 in both laws for every eta in (0, 1).
   At eta = 1/4 the benchmarks are 3/4 (I) and 1 (R).

The proof.
- The I upper bound is the paper's overlap argument. On histories whose active returns are all
  zero, theta_+ and theta_- give identical histories after flipping s, so those histories carry at
  most eta of theta_+'s certification mass. Every certification at theta_- is false.
- The attaining rule for I certifies w_A when some nonzero active return identifies alpha (the
  other sign leaves Theta_4) above 13/1600. When every active return is zero, it certifies with
  probability min(1, eta 2^N_obs). R's rule reads s from the first ETF residual's magnitude.
- For the gate at N_obs = 1: Omega^dagger exists (diag(0, 0, 100) satisfies the Penrose
  equations), and only the first equation is used: the product of Omega, Omega^dagger and Omega is
  Omega. For e = Omega x in the range of Omega it gives e' Omega^dagger e = x' Omega x. Hence
  T_1 = 1 surely, t = 1, and A is {(0, 0, y) : |y| <= 1/10}.
  C_N is {theta_+} at estimated alpha 1/5 (where L_N(w_A) = 147/1600), and the plug-in optimum at
  estimated alpha 0 is (0, 1/2).

Relation to the prose. No gap was found between the formal statement and the Statement. Not
formalized:
- the Proof's remark that the attaining rules also admit alternative confidence-set certificates
  (not part of the Statement);
- red's endpoint-only sharpness and gate non-monotonicity (numerical);
- coverage of M4's C_N (not claimed).
The limits PM recorded at approval apply unchanged. This is a stylized finite-law obstruction
whose novelty is generic: second moments do not determine the likelihood. The gate's loss has two
sources, and only the I-versus-R gap comes from dependence in the public ETF residual. The gate's
power is not monotone in N_obs, so it is not a power benchmark. There is no rate, no magnitude, and
no stability to rounding or unknown laws.

---
id: 16
title: "Joint directional information against a moving ETF comparator"
status: formalized
model_version: M4
depends_on: [2, 15]
axioms_used: []
formal: lean/Standalone/M4JointDirectionalRate.lean
direction: D3
---
## Statement

Use the following multivariate M4 family. There is one active fund and one ETF,
initial wealth and cash one, zero risky incumbent, caps one, zero shareholder
costs and ETF drag, gamma=0, B^A=(1,0), and B^E=(0,1). The ETF cannot hold factor 1.
Write theta=(lambda_1,lambda_2,alpha), and fix a known real 3-by-3 matrix J with
Euclidean operator norm at most 1/100. Set Omega=J J', and define

```
c_0=(0,-1/4,0),              c_1=(0,1/4,1/4),
Theta_4=conv{c_j+J v: j in {0,1}, v in {-1,1}^3},
d_0=(1,0,1),                d_1=(1,-1,1),
sigma_j^2=d_j' Omega d_j,    sigma=max(sigma_0,sigma_1).
```

For the nonzero-rate conclusions assume Omega_11>0 and sigma>0. The case
Omega_33>0 has uncertainty in both the unspanned premium and alpha; the conclusions
also allow Omega_33=0, when alpha is learned exactly from any record. The parameter
domain, including its unknown alpha values, is fixed before sampling.

The law class K_J consists of all **known finite** laws of U in R^3 with
E U=0, E U U'=I_3, and ||U||_2<=9. Set the M4 shocks

```
(z^f_1,z^f_2,z^A)=J U,       z^E=0.
```

The full public record is equivalent to X=(f_1,f_2,r^A-f_1)=theta+J U, since
r^E=f_2. All history and holding-quarter draws are iid conditional on fixed theta.
The exact finite law is known to the rule. Every law has the same joint
observation-error covariance Omega; this is not a claim about every instance
with that covariance outside K_J.

1. **Two necessary comparison directions.** The entire funded ETF-only class
   has score supremum max(0,lambda_2). Its optimizer is cash when lambda_2<0 and
   the ETF when lambda_2>0; both regimes occur in Theta_4. For w_A=(1,0),

   ```
   m_j(theta)=d_j' theta,
   Adv(w_A;theta)=min(m_0(theta),m_1(theta)),
   G_*(theta)=max(0,min(m_0(theta),m_1(theta))).
   ```

   If this minimum is positive, w_A is the unique full optimizer. If it is
   negative, every active action has negative Adv. Both d_j have a nonzero
   unspanned-premium component and an alpha component. The joint sample-mean
   covariance is Omega/N_obs, so each paired error has variance sigma_j^2/N_obs,
   retaining all cross-covariances. These are two score comparisons required by
   the optimized class, not a selected ETF substituted for that class.

2. **Worst-case history length with fixed covariance.** Fix delta in (0,sigma/8]
   and epsilon in (0,1/16]. Set eta=epsilon and delta_econ=delta/4. Suppose that
   for every known law in K_J there exists a full-history rule, possibly using
   independent randomization, which certifies a funded active action or falls
   back to a funded ETF-only action, and satisfies

   ```
   for all theta in Theta_4:
     P_theta(certify and Adv(certified action;theta)<=delta/4) <= epsilon;
   for all theta in Theta_4 with G_*(theta)>=delta:
     P_theta(certify and Adv(certified action;theta)>delta/4) >= 1-epsilon.
   ```

   A rule may depend on the known law but not on unknown theta. Necessarily

   ```
   N_obs >= [1/(16 pi^2)] (sigma^2/delta^2) log(1/epsilon).
   ```

   Conversely, both requirements hold for every law in K_J whenever

   ```
   N_obs >= 192 (sigma^2/delta^2) log(6/epsilon).
   ```

   Thus the worst-case rate matches in order, with loose universal constants.
   The lower bound allows every full-history rule; M4's gate is only the
   constructive upper bound, not the power benchmark. All logarithms are natural.

3. **Directional conservative certificate for the original M4 target.** For
   nonempty C_N, put r_N=sqrt(t_{N,epsilon}/N_obs) and use

   ```
   ell_N(w_A)=min_j [d_j' theta_hat_N-r_N sigma_j] <= L_N(w_A).
   ```

   Empty C_N forces fallback. A positive certificate above delta/4 implies that
   w_A is also the actual M4 plug-in optimizer. On the coverage event,

   ```
   ell_N(w_A) >= min_j [m_j(theta_*)-2 r_N sigma_j].
   ```

   Consequently the two margins and their directions can matter separately;
   one well-estimated comparison does not certify the other. Under the sufficient
   length in part 2 and G_*>=delta, this bound is at least delta/2. This certificate
   does not change C_N or the optimized-comparator L_N defined by M4.

4. **Precise alpha and matching only one comparator.** In coordinates
   (lambda_1,lambda_2,alpha),

   ```
   sigma_0^2=Omega_11+2 Omega_13+Omega_33,
   sigma_1^2=Omega_11+Omega_22+Omega_33
                  -2 Omega_12+2 Omega_13-2 Omega_23,
   sigma^2 >= (sqrt(Omega_11)-sqrt(Omega_33))^2.
   ```

   If the alpha standard deviation is at most half the unspanned-premium
   standard deviation, the lower bound in part 2 is at least
   Omega_11 log(1/epsilon)/(64 pi^2 delta^2). If Omega_33=0, its cross-covariances
   vanish and sigma^2>=Omega_11: the premium requirement persists although alpha
   is observed exactly. The lower construction in that case uses the same alpha
   at its two parameters, so revealing alpha before sampling does not remove it.

   For a concrete opposite effect, let s=1/1000, 0<tau<=1 and

   ```
   J=s [[1,0,0],[1,tau,0],[0,tau,0]].
   ```

   Then sigma_1=0 but sigma_0^2=s^2(1+tau^2)>0. Errors cancel exactly against
   the all-ETF action, while the whole ETF-class certificate still has a nonzero
   worst-case history requirement because cash can be the better comparator.
   This is within a fixed nonzero joint covariance, not a change of wealth or
   of funding between the action classes.

   If both sigma_j are zero (a separate degenerate case, outside part 2), both
   scores m_j are observed without error. One full record then permits a
   zero-false-certification benchmark by comparing the exact minimum with
   delta/4, with power one whenever G_*>=delta. M4's own gate may still fall back
   on empty C_N; no assertion removes that rule.

## Proof

### 1. Admissibility, moving comparator and paired errors

Write any domain point as a point on the segment [c_0,c_1] plus J v with
||v||<=sqrt(3)<2. The active mean on the base segment is between 0 and 1/4;
the ETF mean is between -1/4 and 1/4. The active mean perturbation has magnitude
at most ||d_0|| ||J|| ||v||<=4/100 and its return shock at most
||d_0|| ||J|| ||U||<=18/100. Its gross return is therefore at least 39/50.
The ETF mean perturbation is at most 2/100 and its shock at most 9/100, so its
gross return is at least 1-1/4-2/100-9/100=16/25. These bounds verify positive
returns at every domain vertex and scenario, including singular J. Centering
and the stated covariance follow from E U=0 and E U U'=I. The risky-return
covariance is a different object: it is the covariance of (d_0' J U,e_2' J U).
No covariance is added to another; gamma=0 here.

The action classes and score are

```
F={(a,p): a>=0,p>=0,a+p<=1},   E={(0,p):0<=p<=1},
Q((a,p);theta)=a(lambda_1+alpha)+p lambda_2.
```

Maximizing over the entire ETF interval gives max(0,lambda_2). Maximizing over
the funded triangle gives max(0,lambda_2,lambda_1+alpha), proving the gap formulas
and the positive-gap optimizer. For any a>0 and p<=1-a,

```
Q((a,p);theta)-sup_E Q <= a[lambda_1+alpha-max(0,lambda_2)].
```

This proves strict negativity for every active action at a negative gap. The
paired error identity of claim 002 transfers directly: these Q scores are its
affine formula with zero drag, costs and gamma. Subtracting at w_A and the two
ETF-class vertices gives d_j'(theta_hat_N-theta). Independence and centering
give covariance Omega/N_obs by expanding the finite double sum of errors.

### 2. A covariance-preserving finite hard law

Choose j with sigma_j=sigma and set h=J' d_j/sigma. Then ||h||=1. Complete h to
an orthonormal basis (h,v_1,v_2) of R^3. Put

```
k=floor(sigma/(4 delta))>=2,     m=4k-1,     phi=pi/(4k),
q_i=sin^2(i phi)/(2k),           z_i=i-2k,   i=1,...,m,
V=sum_i q_i z_i^2,              W_i=z_i/sqrt(V),
a_k=1/(2 sqrt(V)).
```

The finite cosine sum sum_{i=1}^{4k-1} cos(2i phi)=-1 follows from the geometric
series for the 4k-th roots of unity. Using sin^2(x)=(1-cos(2x))/2 proves
sum_i q_i=1. Reflection about 2k proves E W=0, and its normalization gives
E W^2=1. Here V>0 and the following useful bounds hold:

```
k^2/16 <= V <= 4k^2,      |W|<=8,
1/(4k) <= a_k <= 2/k <= 1.
```

For the lower variance bound, use indices k<=i<=floor(3k/2) and their reflected
partners. Together they contain at least k indices, each of probability at least
1/(4k), and each with |z_i|>=k/2. They contribute at least k^2/16 to V. The
upper bound follows from |z_i|<2k. The bounds on W and a_k follow immediately.

Let S_1,S_2 be independent uniform signs, independent of W, and set

```
U=h W+v_1 S_1+v_2 S_2.
```

This is a finite centered law with covariance I_3 and ||U||^2=W^2+2<=66<81.
It is in K_J and gives exactly the prescribed Omega after multiplication by J.
Use this same known law at the two parameters

```
theta_-=c_j-a_k J h,     theta_+=c_j+a_k J h.
```

Both lie in Theta_4 because every coordinate of a_k h has absolute value at
most one. The j-th contrast is respectively -a_k sigma and +a_k sigma.
The other contrast at c_j is 1/4, and its perturbation has magnitude at most
a_k sigma_{1-j}<=sigma<=sqrt(3)/100<1/50. Therefore the other contrast stays
above 23/100, while a_k sigma<=sigma<1/50. At theta_- every active action is
false, and at theta_+ the full gap is a_k sigma>=sigma/(4k)>=delta. The hard
parameters thus test the exact error and power requirements of part 2.

### 3. Full-history lower bound, including singular covariance

Give the testing rule the even more informative latent record
(W-a_k,S_1,S_2) under theta_- or (W+a_k,S_1,S_2) under theta_+. The same map

```
(y,s_1,s_2) -> c_j+J(h y+v_1 s_1+v_2 s_2)
```

produces X, hence every public fund and factor return. Every full-history rule
can be used on these latent records with exactly its original error probabilities.
This reasoning remains true if J is singular; injectivity is not required.

The two W supports differ by one grid step 2a_k=1/sqrt(V). Their affinity is
sum_{i=1}^{m-1} sqrt(q_i q_{i+1})=cos(phi). To see this, apply
sin((i-1)phi)+sin((i+1)phi)=2 cos(phi) sin(i phi), multiply by sin(i phi), sum,
and use the zero endpoint values and sum sin^2(i phi)=2k. The independent signs
do not change the affinity. Product expansion gives affinity cos(phi)^{N_obs}
for the latent histories.

The finite testing calculation used in claim 015 applies to any certification
probability g in [0,1] on the histories. For the negative and positive laws P,Q,
the two required errors imply

```
2 epsilon >= sum[P g+Q(1-g)] >= 1-TV(P,Q),
TV(P,Q) <= sqrt(1-aff(P,Q)^2).
```

The second inequality is finite Cauchy-Schwarz applied to
|P-Q|=|sqrt(P)-sqrt(Q)|(sqrt(P)+sqrt(Q)); thus no literature testing theorem is
being assumed. It follows that

```
N_obs >= log[1/(4 epsilon(1-epsilon))]/[-2 log cos(phi)]
       >= (4k)^2/(4 pi^2) log(1/epsilon).
```

The last step uses -log cos(phi)<=phi^2 for phi<=pi/4 (integrate tan x<=2x),
and 4 epsilon(1-epsilon)<=sqrt(epsilon). Since floor(x)>=x/2 for x>=2,
k>=sigma/(8 delta). Substitution proves the lower bound in part 2. The law may
depend on J and the prespecified margin, but not on the unknown choice between
theta_- and theta_+; it preserves Omega exactly throughout.

### 4. Calibration and a directional certificate for the whole class

Write e_N=J U_bar for the mean error. Every such error belongs to Im(Omega).
A singular-value decomposition of J shows that

```
e_N' Omega^dagger e_N = ||Pi U_bar||^2 <= ||U_bar||^2,
```

where Pi=J' (J J')^dagger J is the orthogonal projection onto the row space of J.
M4's finite quantile therefore gives coverage at least 1-epsilon for all theta:
the error law is theta-independent, and membership of the true theta in C_N
is precisely T_N<=t_{N,epsilon}. The prescribed intersection with Theta_4 does
not change this equivalence. Empty C_N cannot occur on coverage.

For any e in Im(Omega), a singular-value decomposition also gives

```
|d_j' e| <= sqrt(d_j' Omega d_j) sqrt(e' Omega^dagger e).
```

In particular every theta in C_N satisfies
d_j' theta>=d_j' theta_hat_N-r_N sigma_j. Taking the minimum over both comparison
vertices and then the infimum over C_N proves ell_N<=L_N for the whole optimized
ETF class. On coverage the same inequality applied to the estimation error gives
ell_N>=min_j(m_j(theta_*)-2r_N sigma_j). If ell_N>delta/4 then both estimated
contrasts are positive, so the unique plug-in full optimizer is w_A. If it is
certified on coverage its true Adv exceeds delta/4. Thus false certification is
at most epsilon, for every parameter and every law, at any sample length.

### 5. Uniform length sufficient for power

Each latent coordinate Y=U_l is centered, has variance one and |Y|<=9. For
|t|<=1/18, its power series gives

```
E exp(tY) <= 1+sum_{r>=2} |t|^r E|Y|^r/r!
          <= 1+(t^2/2) sum_{r>=2}(9|t|)^(r-2)
          <= 1+t^2 <= exp(t^2).
```

Here E|Y|^r<=9^(r-2) E Y^2. For 0<a<=1/9, independence and the elementary
exponential bound on a finite tail event, with t=a/2, yield
P(|Y_bar|>=a)<=2 exp(-N_obs a^2/4). Choose
a=2 sqrt(log(6/epsilon)/N_obs). When N_obs>=324 log(6/epsilon), a<=1/9.
A union bound over three coordinates gives ||U_bar||^2<=3a^2 with probability
at least 1-epsilon. Consequently the first finite quantile satisfies

```
t_{N,epsilon} <= 12 log(6/epsilon).
```

Under the sufficient sample length in part 2, sigma/delta>=8 makes the condition
N_obs>=324 log(6/epsilon) automatic. Also
2 r_N sigma<=2 sigma sqrt(12 log(6/epsilon)/N_obs)<=delta/2.
At any parameter with G_*>=delta both m_j>=delta. On coverage the certificate
is therefore at least delta/2>delta/4, and its certified action is truly better
than the ETF class. This proves uniform correct power at least 1-epsilon.
The argument is a sufficient envelope, not monotonicity of the exact quantile
or an assertion that the gate attains optimal power.

### 6. Alpha precision, cross-covariance and the second comparator

Expanding d_j' Omega d_j gives part 4's two variance formulas. Positive
semidefiniteness gives |Omega_13|<=sqrt(Omega_11 Omega_33), hence the displayed
lower bound by a square. If sqrt(Omega_33)<=sqrt(Omega_11)/2 it is at least
Omega_11/4; insert this in part 2's lower bound. If Omega_33=0, the whole third
row and column vanish. Then alpha is observed without noise, and the hard mean
shift J h=Omega d_j/sigma has third coordinate zero, so the two hard parameters
have identical alpha. Revealing that value cannot help distinguish them.

For the stated example J, its squared Frobenius norm is
2s^2(1+tau^2)<=4s^2<1/10000, so the required operator-norm bound holds.
d_1' J=0 while d_0' J=s(1,tau,0), proving the two contrast variances. The hard
face is cash, c_0, despite perfect error cancellation against the ETF vertex.
The rate is consequently governed by the whole comparator class, not by that
single noiseless match.

Finally, if both contrast variances are zero, d_j' J=0. Every record then gives
d_j' X=d_j' theta exactly, so the direct full-history benchmark described in
part 4 is correct with probability one. This fact does not override M4's
empty-confidence-set fallback.

## Checks

`checks/016/check.py` checks the two-comparator optimization, covariance and
cross-covariance examples, the normalized finite hard law and its directional
embedding, and the directional certificate inequality on exact finite histories.
The full-public-record follow-up constructs the actual factor and fund returns
under both hard parameters, combines coincident observations in the singular
fixtures, and computes the optimal randomized endpoint test at N_obs=1,2 with
epsilon=1/16. For each of the three checked embeddings it agrees with the scalar
overlap calculation and cannot attain correct power 1-epsilon, even under the
weaker requirement of validity at only the negative endpoint. This checks for
information inadvertently exposed by the public returns or hidden scenario labels.
These checks are not the arbitrary-law or sample-length proof.

## Not shown

- A worst case over K_J, not a rate for each fixed law. Support size in the hard
  construction grows as sigma/delta; the exact known finite law and real-valued
  observations remain idealizations. Claims 014's likelihood caveat remains.
- Matching order only. The constants are loose, and neither optimal constants
  nor a uniformly most powerful gate is established. Exact calibration may be
  combinatorial; no general efficient algorithm or rounding certificate is given.
- This is a two-vertex moving comparator under gamma=0, zero costs, an all-cash
  incumbent and caps one. It does not cover a continuously moving risk-averse
  ETF optimum, general menus, or simultaneous uncertainty in estimated loadings.
- Alpha and premia both vary in the domain, but the theorem does not identify
  them economically beyond this fixed exposure model. Its lower construction
  changes means along a joint direction, not necessarily a pure-alpha direction.
  Exact-alpha statements refer to zero observation-error variance (and to the
  hard pair's common alpha), not a Bayesian prior concentration argument.
- Cash and ETF contrasts explain why one matched comparator is insufficient.
  The individual ellipsoidal penalty and the testing techniques are standard;
  no priority claim for them or for generic multivariate mean testing is made.
  The result does not by itself establish a publication anchor or a calibrated
  history requirement. It concerns one fixed review, not terminal wealth.

## Prior art

Checked the D3 source-level FINDINGS comparison, the registered full-text
passages of `petrik2016safe` (shared-model regret against a fixed baseline) and
`esfahani2017data` (coverage-based protection for data-selected decisions), and
the penalty and sampling comparisons `olivaresnadal2018technical` and
`manski1999statistical`. Also checked claims 002, 014 and 015, the refuted
directory and the failed M2 conjectures. No literature theorem is imported.

Neither common-parameter evaluation nor the norm penalty is new. Here the
comparison must satisfy two distinct covariance directions because the oracle
ETF optimizer moves between cash and the ETF. The lower bound uses a known-law
class with covariance held fixed and a full-history test at either active face,
while the upper bound is valid for M4's original target. The exact-alpha floor
and the noiseless-ETF-but-hard-cash example are consequences of that complete
comparison. This remains a structured application of standard statistical
geometry; broader novelty requires independent scientific assessment.

## Open objections

None raised yet. Red should test the fixed-covariance hard law, singular-J
lifting, domain admissibility at both comparator faces, and the original-target
certificate (including the empty-set rule) before anyone builds on the result.

## Review

**Red, 2026-09-28.** I checked every part by hand, tested each numerically with my own code, and then probed the claim's scope.

**Hand check: every part holds.**
- *Part 1.* Q = a(lambda_1 + alpha) + p lambda_2 on the funded triangle, so sup_E = max(0, lambda_2) and sup_F = max(0, lambda_2, lambda_1 + alpha). Hence Adv(w_A) = min(d_0'theta, d_1'theta). Q - sup_E <= a[lambda_1 + alpha - max(0, lambda_2)] gives strict negativity at a negative gap. Both comparator regimes occur, with lambda_2 = -1/4 at c_0 and +1/4 at c_1.
- *Admissibility.* The perturbation bounds sqrt(2)(1/100)sqrt(3) <= 4/100 and sqrt(2)(1/100)(9) <= 18/100 give active gross returns >= 39/50. For the ETF, 1 - 1/4 - 2/100 - 9/100 = 16/25.
- *Hard law.* sum_{i=1}^{4k-1} cos(2 i phi) = -1 gives sum_i q_i = 1, and reflection about 2k gives centering. The variance bounds hold: indices k..floor(3k/2) have sin^2 >= 1/2, and there are at least k with their partners, each with |z| >= k/2. That gives V >= k^2/16, and V < 4k^2, |W| <= 8 and a_k in [1/(4k), 2/k] follow.
- *Embedding.* The U-embedding preserves E U U' = I, and ||U||^2 = W^2 + 2 <= 66. With h = J'd_j/sigma, d_j'J h = sigma, so the j-th contrast is ∓ a_k sigma at theta_±, because d_j'c_j = 0 for both j. The other contrast is 1/4 minus at most sigma < sqrt(3)/100. Since ||a_k h|| <= 1, theta_± lie in Theta_4.
- *Lower bound.* The latent lifting is valid for singular J: rules act through the map, so no injectivity is needed. The one-step shift 2a_k = 1/sqrt(V) gives affinity cos(phi). Then 4 epsilon(1 - epsilon) <= sqrt(epsilon), -log cos(phi) <= phi^2 and k >= sigma/(8 delta) combine into 1/(16 pi^2).
- *Certificate.* e'Omega^dagger e = ||Pi U_bar||^2 <= ||U_bar||^2, with Pi the row-space projection of J. Omega-Cauchy-Schwarz for e in Im(Omega) gives ell_N <= L_N for the whole ETF class, and on coverage ell_N >= min_j(m_j - 2 r_N sigma_j). An empty C_N falls back.
- *Upper bound.* With E|Y|^r <= 9^{r-2} and 9|t| <= 1/2, E e^{tY} <= 1 + t^2. With t = a/2 this gives a tail of 2exp(-N a^2/4), and the three-coordinate union gives t_{N,epsilon} <= 12 log(6/epsilon). Under the sufficient length, 2 r_N sigma <= delta/2, and 192 x 64 >= 324.
- *Part 4.* The sigma_j^2 expansions are correct, and so is the bound (sqrt(Omega_11) - sqrt(Omega_33))^2. When Omega_33 = 0, Omega d_j has zero third coordinate, so the hard pair shares alpha. For the example J, d_1'J = 0 and d_0'J = s(1, tau, 0).

**Independent numerics** (red's own script, written without reading `checks/016/check.py`).
- *Geometry.* On 2000 random theta, vertex maximization over the funded triangle and over E matches Adv = min(m_0, m_1) and G_* = max(0, min(m_0, m_1)).
- *Hard laws.* For k = 2..8: normalization, centering, E W^2 = 1, both V bounds, |W| <= 8, the a_k bounds, the one-step shift and the affinity cos(pi/(4k)) all hold. So does E e^{tW} <= 1 + t^2 on |t| <= 1/18.
- *Embedding.* For 400 random J with operator norm <= 1/100, a quarter of them rank-deficient: E U = 0, E U U' = I, ||U|| <= 9, theta_± inside Theta_4, the j-th contrast exactly ∓ a_k sigma, and the other contrast > 0.23.
- *Exact optimal test.* A likelihood-ratio test on the latent hard law at k = 2 needs N_obs = 17 (epsilon = 1/16) and 37 (1/100), against the latent bound (4k)^2 log(1/epsilon)/(4 pi^2) = 4.49 and 7.47.
- *Example J.* It gives sigma_1 = 0 and sigma_0^2 = s^2(1 + tau^2), with ||J|| = 1.5e-3.
- *Claim's own check.* It passes.

**Attacks that did not succeed.**
- A covariance change hidden in the hard law: E U U' = I exactly, so Omega is fixed.
- Singular J breaking the lower bound: the latent lifting needs no injectivity.
- A hard parameter outside the domain, or a face with the wrong comparator: ||a_k h|| <= 1, and the other contrast stays above 0.23.
- A certificate for a replacement target: ell_N bounds M4's original L_N over the whole ETF class.
- A single matched comparator substituted for the class: both contrasts are carried, and the example shows why.

**Scope (sharpenings).**
1. **Constants are far apart.** 1/(16 pi^2) ≈ 0.0063 against 192 log(6/epsilon), which is about 1.65 log(1/epsilon) at epsilon = 1/16, a factor of roughly 5 x 10^4. The exact tests sit about 4-5 times above the latent bound. "Matches in order" is all that is claimed and all that holds.
2. **The new structural content is the max over comparator directions.** Everything else is standard multivariate mean testing. The rate is set by sigma = max(sigma_0, sigma_1), not by the variance of the currently optimal comparison. The example, noiseless against the ETF but noisy against cash, is the claim's real point and is correct.
3. **The contrasts load on lambda_1 + alpha jointly.** The active fund is the only factor-1 vehicle plus alpha, so the result does not separate manager skill from the unspanned premium; the Not shown says so. The exact-alpha floor sharpens claim 015: even alpha known without error leaves the premium requirement, because the hard pair shares alpha.
4. **The worst case needs support growing like sigma/delta** within ||U|| <= 9. This is not a per-law rate, as stated.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Certifying that an action beats the best of k alternatives needs the sample size of the hardest comparison, max_j sigma_j^2/Delta^2 log(1/epsilon), where sigma_j^2 is the variance of the j-th paired contrast.
- *General result.* Le Cam two-point bounds applied along each contrast direction, combined with a union of one-sided tests, give Theta(max_j sigma_j^2/Delta^2 log(1/epsilon)) for certifying min_j d_j'theta > 0 under joint observation. This is the non-adaptive analogue of best-arm-identification complexity against the closest alternative (Garivier-Kaufmann; Kaufmann-Cappe-Garivier).
- *Reduction.* The whole-ETF-class target is the minimum of two linear functionals d_0'theta and d_1'theta, one per ETF-only optimum regime. The hard pair moves along the worst direction J'd_j/sigma, and the certificate is the union over the two contrasts.
- *Verdict: special case,* as the human referee said. Left over: identifying the moving comparator's regimes as the k alternatives, and the example with noiseless ETF but noisy cash contrasts.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check of all four parts (whole-ETF-class geometry with both comparator regimes, admissibility, hard-law normalization and variance bounds, the singular-J latent lifting, the lower-bound constant, the directional certificate bounding M4's original L_N, the sub-Gaussian upper bound, the Omega expansions and exact-alpha floor) and independent numerics (2000 geometry points, hard laws k=2..8, 400 random J including rank-deficient, exact tests, the example J) are sound, and PM reran checks/016; no open objections. Limits stated: matching order only, constants about 5x10^4 apart; the structural content is that the rate is set by the maximum over the comparator directions the optimized ETF class requires (errors can cancel against the ETF yet not against cash), the rest being standard multivariate testing; the contrasts load on lambda_1+alpha jointly, so skill is not separated from the unspanned premium; the worst case needs support growing like sigma/delta.


Not machine checked. The core uses finite probabilities, matrix and projection
identities, a finite sine-weight law, and explicit exponential bounds. The rate
is not assumed as a hypothesis; the adverse law and certificate are constructed.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4JointDirectionalRate.lean` and the
proof in `lean/Novel/M4JointDirectionalRateProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used, and no rate, tail or
covariance bound is assumed.

Formal objects. M4 comes from claim 014's statement file, and the requirement predicates from
claim 015's. The proof imports claim 015's proof module, as Q-04 allows for depends_on. Rules map
each full history to a probability measure on actions.
- The operator-norm bound on J is stated as ||J v||^2 <= (1/100)^2 ||v||^2 for every v.
- A law in K_J is a finite scenario type with masses q >= 0 summing to one, E U = 0, E U U' = I_3
  and ||U||^2 <= 81 at every scenario point.
- The paired contrast identity of claim 002 is re-derived directly for this score.

Proved:
1. Admissibility; M4's Omega equals J J'; the explicit F, E and Q; the ETF-class supremum
   max(0, lambda_2), with cash or the ETF as its unique optimizer by the sign of lambda_2, both
   regimes occurring in Theta_4; Adv(w_A) = min(d_0'theta, d_1'theta) and G_* = max(0, that
   minimum); w_A as the unique full optimizer when the minimum is positive, and negative Adv for
   every active action when it is negative; the two paired score differences d_j'(theta' - theta);
   and the joint covariance of theta_hat - theta equal to J J'/N_obs.
2. Lower bound: if every law in K_J admits a rule meeting both requirements at length N_obs, then
   N_obs >= sigma^2 log(1/epsilon)/(16 pi^2 delta^2).
   Upper bound: for every law in K_J and N_obs >= 192 (sigma^2/delta^2) log(6/epsilon), M4's gate
   with the directional certificate meets both requirements.
3. For nonempty C_N, ell_N <= M4's original L_N(w_A). ell_N > delta/4 makes w_A the plug-in
   optimizer. On coverage, ell_N >= min_j [m_j - 2 r_N sigma_j], which is at least delta/2 under
   the sufficient length when G_* >= delta.
4. The two variance formulas; (sqrt(Omega_11) - sqrt(Omega_33))^2 <= sigma^2 and the
   Omega_11/(64 pi^2 delta^2) floor. When Omega_33 = 0: vanishing cross-covariances,
   Omega_11 <= sigma^2, and alpha read exactly from every positive-mass record. The example J with
   sigma_1 = 0 < sigma_0. When both sigma_j are zero, a one-record rule has no false certification
   and power one.
The operator-norm bound is needed only for admissibility and the lower bound, so the upper bound,
part 3 and the degenerate benchmark are stated for every J. This is stronger than the prose.

The proof.
- Omega^dagger exists by the spectral theorem. Only its first Penrose equation is used, which shows
  that J equals Omega times (Omega^dagger J). Hence every error J U_bar lies in Im(Omega) with
  e' Omega^dagger e <= ||U_bar||^2, and |d'e| <= sigma_d sqrt(e' Omega^dagger e) on Im(Omega).
- The lower bound uses claim 015's sine-weighted grid on 4k - 1 points, normalized to unit variance.
  The variance bounds k^2/12 <= V <= 4k^2 come from sin^2 >= 1/2 on the middle band [k, 3k] and an
  exact sum of squares; this band argument differs slightly from the paper's. The grid is embedded
  along h = J' d_j/sigma with two fair signs through a Householder reflection, which keeps
  E U U' = I exactly for singular J as well. The two hard parameters give identical histories on
  the common atoms, and claim 015's testing inequality and logarithm bound finish.
- The upper bound uses E exp(tY) <= 1 + t^2 for |tY| <= 1, from |e^x - 1 - x| <= x^2, together with
  a finite product expansion and a union bound over the three coordinates. This gives
  t_{N,epsilon} <= 12 log(6/epsilon) from M4's quantile definition.

Relation to the prose. No gap was found between the formal statement and the Statement. The limits
PM recorded at approval apply unchanged:
- the bounds match in order only, with constants about 5x10^4 apart;
- the structural content is that the rate is set by the maximum over the comparator directions
  the optimized ETF class requires (errors can cancel against the ETF yet not against cash), the
  rest being standard multivariate testing;
- the contrasts load on lambda_1 + alpha jointly, so skill is not separated from the unspanned
  premium;
- the worst case needs support growing like sigma/delta.

Lean, 2026-09-28 (addendum, auditor's request): part 4's sentence "The lower construction in that
case uses the same alpha at its two parameters, so revealing alpha before sampling does not remove
it" is now machine checked as `KnownAlphaLower` in `lean/Standalone/M4JointDirectionalRate.lean`.
When Omega_33 = 0 there is a value alpha_0, fixed before N_obs, such that the part 2 lower bound
N_obs >= sigma^2 log(1/epsilon)/(16 pi^2 delta^2) holds even when both requirements are imposed
only on Theta_4 intersected with {alpha = alpha_0}. The value alpha_0 is the hard pair's common
alpha.

The proof now goes through a core lemma. It fixes the hard pair before the history length and the
law, and needs the rule's two requirements only at those two parameters. When Omega_33 = 0 the
third row of J vanishes, so J h has zero alpha component and the pair shares alpha. Both
`LowerBound` and `KnownAlphaLower` follow from the core lemma. The earlier note's "No gap was
found" overlooked this sentence; with the addendum it is covered. `lake build` and the axiom audit
pass (standard axioms only).

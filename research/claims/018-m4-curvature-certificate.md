---
id: 18
title: "Curvature controls certification with costs and binding constraints"
status: formalized
model_version: M4
depends_on: [4, 17]
axioms_used: []
formal: lean/Standalone/M4CurvatureCertificate.lean
direction: D3
---
## Statement

Use any admissible M4 instance with gamma>0 and positive-definite risky-return
covariance Sigma. Keep its entire funded classes F and E, arbitrary compliant
incumbent, directional proportional costs, position caps, ETF drag, and one or
two ETFs. No slack-budget, interior-optimizer, diagonal-risk or zero-cost
assumption is imposed. Define the 3-by-(1+n) mean-exposure matrix A by

```
A w=(b(w),a),
A=[ ((B^A)',1)  ((B^E_1)',0) ... ((B^E_n)',0) ].
```

Assume the known finite shock law has a representation

```
zeta=(z^f_1,z^f_2,z^A)=J U,
E U=0, E U U'=I_3, ||U||_2<=9,  Omega=J J',
```

where J is a known real 3-by-3 matrix and U has known finite support. The ETF
residuals may be correlated with U and each other, provided the full joint law
is known and meets M4's centering and positivity requirements. The estimator
continues to use M4's X only; all public returns remain available to benchmark
rules. Unlike claim 016, there is no norm bound on J: admissibility of the actual
M4 design is assumed explicitly, not inferred from a small numerical box.

Let K>=0 be the following known ratio of mean-estimation error to score curvature:

```
K=(1/gamma) max_{z != 0} ||J' A z||_2^2/(z' Sigma z).
```

It is finite, with the maximum attained on z' Sigma z=1. Omega and Sigma are
different covariance objects. K compares their action directions; it does not
add them or introduce ambiguity aversion.

1. **A whole-class certificate from two optimized scores.** Both score maxima
   are unique, at w_hat_F and v_hat_E for theta_hat_N. Put

   ```
   G_hat=Q(w_hat_F;theta_hat_N)-Q(v_hat_E;theta_hat_N)>=0,
   r_N=sqrt(t_{N,eta}/N_obs),   u_N=K r_N^2,
   ell_N=G_hat-sqrt(2 u_N G_hat)-u_N/2.
   ```

   Whenever C_N is nonempty,

   ```
   ell_N <= L_N(w_hat_F).
   ```

   Thus use M4's funded full optimizer only when ell_N>delta_econ; otherwise
   fall back to v_hat_E, including when C_N is empty. If ell_N>delta_econ>=0,
   the candidate necessarily changes the active holding a from a^-: otherwise
   G_hat=0. At every fixed theta_* the probability of certifying an action with
   true whole-class advantage at most delta_econ is at most eta.

   This bound optimizes the ETF comparator at every theta in C_N; it does not
   replace that comparator by v_hat_E. Global values of both plug-in problems
   are required. Unverified solver incumbents do not establish G_hat.

2. **Power under a curvature-normalized information condition.** Fix
   delta>0, epsilon in (0,1/16], eta=epsilon and delta_econ=delta/4. If
   u_N<=delta/128, then at every theta_* with G_*(theta_*)>=delta, coverage
   implies ell_N>delta/2, and hence correct certification with true advantage
   greater than delta/4. For every known law satisfying the above assumptions,
   both uniform false-certification control and correct power at least
   1-epsilon therefore hold whenever

   ```
   N_obs >= max(324, 1536 K/delta) log(6/epsilon).
   ```

   The maximum avoids a small-sample tail qualification; it is not a necessary
   condition. If K=0, the mean-estimation error has no effect on any score
   difference, and the formula for ell_N equals the true oracle gap almost surely
   at every positive sample length. This does not override empty-set fallback.

3. **Matching worst-case order over the specified designs.** Fix
   kappa in (0,1/10000] and delta in (0,kappa/128]. Consider all admissible M4
   designs and known laws above with K<=kappa; the rule may know the complete
   design and law. A rule certifies a funded holding with a!=a^- or falls back
   to a funded E holding. A common positive integer N_obs that permits a law-specific
   full-public-history rule, allowing independent randomization, with

   ```
   for every theta in that design's Theta_4:
     P_theta(certify and Adv(certified action;theta)<=delta/4) <= epsilon;
   for every theta in that design's Theta_4 with G_*(theta)>=delta:
     P_theta(certify and Adv(certified action;theta)>delta/4) >= 1-epsilon
   ```

   must satisfy

   ```
   N_obs >= [kappa/(32 pi^2 delta)] log(1/epsilon).
   ```

   Conversely N_obs>=1536 (kappa/delta) log(6/epsilon) suffices for every member
   of this class, by part 2. This is matching order in kappa/delta, with loose
   constants. The lower bound follows from an explicit fixed-design subfamily
   in claim 017. It is a worst case over designs and laws, not a lower bound for
   every constrained instance with the same K, nor a statement that fees or
   binding constraints themselves cause this rate.

## Proof

### Funded classes and a quadratic gap at an optimizer

M4 uses exactly M2's fixed funded action sets. The incumbent is in E, E is
contained in F, and both are closed bounded convex sets: the box constraints are
linear, and the cash requirement is a sublevel condition for the convex
directional cost plus a linear net purchase. This is claim 004's finite action
geometry, with the same coefficients and constraints, so it transfers directly.
The score is continuous in holdings even outside the parameter domain and is
gamma Sigma-strongly concave, since it is affine minus the convex cost and the
positive-definite quadratic risk term. Thus both maxima exist and are unique
for every real parameter vector, including the unprojected estimate.

For either class D, write w_D for its optimizer at a parameter theta. For v in D
and 0<h<1, strong concavity and optimality give

```
Q(w_D;theta) >= Q((1-h)w_D+h v;theta)
             >= (1-h)Q(w_D;theta)+h Q(v;theta)
                +(gamma/2)h(1-h)(v-w_D)'Sigma(v-w_D).
```

Divide by h and let h decrease to zero. This proves the quadratic gap

```
Q(w_D;theta)-Q(v;theta) >= (gamma/2)(v-w_D)'Sigma(v-w_D).
```

No differentiability of costs, first-order equality, or interiority is used.
In particular, for d=w_hat_F-v_hat_E, since v_hat_E is also in F,
G_hat>=(gamma/2)d'Sigma d. The same argument holds at every other parameter.

### Mean errors and movement of the entire ETF optimum

Positive definiteness of Sigma makes its unit ellipsoid compact, so K is finite
and attained. For every d, its definition gives

```
||J' A d||^2 <= gamma K d' Sigma d.
```

If e is in Im(Omega) and e'Omega^dagger e<=r^2, singular-value decomposition of
J yields a vector y with e=J y and ||y||<=r. Consequently

```
|e' A d| <= r ||J' A d|| <= r sqrt(gamma K d'Sigma d).
```

This includes singular J; Im(J J')=Im(J), and the minimum-norm representation
has squared norm e'(J J')^dagger e. When K=0, J'A=0, so all these score errors
vanish.

Fix any estimate theta_hat and theta=theta_hat-e of the stated form. For v in E
let d_E=v-v_hat_E. Write V_E(theta)=sup_E Q(v;theta). The quadratic gap on E
and the affine parameter dependence imply

```
Q(v;theta)
 <= Q(v_hat_E;theta_hat)-e' A v_hat_E
       -(gamma/2)d_E'Sigma d_E-e' A d_E
 <= Q(v_hat_E;theta_hat)-e' A v_hat_E+K r^2/2.
```

The last step maximizes the scalar upper bound
-(gamma/2)t^2+r sqrt(gamma K)t over t>=0; its maximum is K r^2/2.
Taking the supremum over the entire E proves the value bound, including any
change of the optimal ETF holding or its active constraints. Therefore

```
Adv(w_hat_F;theta)
 >= G_hat-e' A(w_hat_F-v_hat_E)-K r^2/2
 >= G_hat-r sqrt(2 K G_hat)-K r^2/2.
```

The second line uses the full-class quadratic gap. Applying this with r=r_N
to every theta in nonempty C_N proves part 1. Notice where the moving ETF
optimizer was controlled: the supremum over all v in E preceded the last
line. It was not replaced by a single selected comparison.

The sets C_N are compact when nonempty. The advantage is continuous there
(maximization of this fixed compact action class preserves continuity, since
the score's parameter dependence is affine and uniformly bounded in holdings),
so the infimum defining L_N is finite and attained. The lower-bound argument
does not require finding its minimizer.

### Coverage and two-sided gap stability

Under the known law the error is e_N=J U_bar. It lies in Im(Omega), and its
pseudoinverse quadratic form equals the squared norm of the projection of
U_bar onto J's row space. The exact finite quantile therefore gives
P(theta_* in C_N)>=1-eta at every theta_*. Intersecting with Theta_4 preserves
this event because theta_* is in the domain. Empty C_N is impossible on coverage.

Hence ell_N>delta_econ cannot falsely certify on coverage. Positivity also
forces G_hat>0, which forces w_hat_F outside E, exactly an active intervention
even with a nonzero incumbent. The fallback is M4's implementable v_hat_E,
not a clairvoyant ETF optimum.

For the power statement, write g=G_*(theta_*) and u=K r_N^2. The last displayed
advantage bound can also be applied with the roles of theta_* and theta_hat
reversed: the same error ball is symmetric, and the optimizing and quadratic
gap arguments hold for parameters outside Theta_4 as well. Maximizing the
candidate score at theta_hat then gives, on coverage,

```
G_hat >= g-sqrt(2 u g)-u/2.
```

For u>0 the function f_u(g)=g-sqrt(2u g)-u/2 is increasing for g>=u/2.
This follows from its derivative 1-sqrt(u/(2g)); for u=0 it is the identity.
If g>=delta and u<=delta/128, the preceding inequality yields

```
G_hat >= delta-delta/8-delta/256 = 223 delta/256 > 3 delta/4.
```

Apply the same monotonicity again to ell_N=f_u(G_hat), using
3 delta/4>=u/2. Since sqrt(3)<2,

```
ell_N >= 3 delta/4-(sqrt(3)/16)delta-delta/256
      > 159 delta/256 > delta/2.
```

This proves correct certification on coverage. When K=0 the affine score
perturbation is identically zero, so both sets' scores and optima agree between
theta_hat and theta_* almost surely, and G_hat=G_*(theta_*). The same holds
throughout any nonempty C_N, giving the stated degenerate case.

### Uniform sample length under the known bounded law class

For each coordinate Y of U, E Y=0, E Y^2=1 and |Y|<=9. The bounded power series
calculation in claim 017 gives E exp(tY)<=exp(t^2) for |t|<=1/18: bound its
r-th absolute moment by 9^(r-2) for r>=2 and sum the geometric majorant.
Independence and the exponential tail bound imply
P(|Y_bar|>=b)<=2 exp(-N_obs b^2/4) for 0<b<=1/9.

For N_obs>=324 log(6/epsilon), a union bound at
b=2 sqrt(log(6/epsilon)/N_obs) gives
N_obs ||U_bar||^2<=12 log(6/epsilon) with probability at least 1-epsilon.
The pseudoinverse statistic is no greater than this squared norm. Its first
finite support quantile thus satisfies t_{N,epsilon}<=12 log(6/epsilon).
The sample condition in part 2 ensures

```
u_N=K t_{N,epsilon}/N_obs <= delta/128,
```

with the case K=0 immediate. This proves the sufficient length. It is a
uniform envelope, not monotonicity of M4's discrete quantile or optimality of
this certificate for any fixed law.

### The matching lower-bound subfamily

Fix kappa as in part 3 and take claim 017 with s=sqrt(kappa). It is an
admissible M4 family with J=s I_3, gamma=1/s^2,

```
A=[[1,0],[0,1],[1,0]], Sigma=s^2 diag(2,1).
```

For every nonzero action direction z,
||J'A z||^2=z'Sigma z, so K=1/gamma=s^2=kappa. Every known finite hard law in
claim 017 is in the present class. Its necessary length, allowing every
full-public-history randomized rule and requiring uniform validity over its
domain, is kappa log(1/epsilon)/(32 pi^2 delta). This proves necessity for a
common length over the larger class; nothing asserts necessity for each member.
For sufficiency, kappa/delta>=128 makes 1536 kappa/delta exceed 324, so part 2
applies uniformly to K<=kappa. The class is nonempty by this same subfamily.

## Remark: certified gaps for approximate optimizer outputs

This paper derivation was independently verified by red on 2026-09-28 (see the
Review addendum); it is still not machine checked. The numbered Statement,
including its exact-optimizer power
bound, is unchanged. Approximate actions below need not equal M4's prescribed
exact plug-in; the remark bounds the same original L_N for those actions.

Let w_tilde be certified feasible in F and v_tilde certified feasible in E. At
theta_hat_N suppose certified nonnegative value gaps satisfy

```
V_F-Q(w_tilde;theta_hat_N) <= epsilon_F,
V_E-Q(v_tilde;theta_hat_N) <= epsilon_E,
V_D=max_{w in D} Q(w;theta_hat_N),
g=Q(w_tilde;theta_hat_N)-Q(v_tilde;theta_hat_N),  u=K r_N^2.
```

Here g can be negative, but g+epsilon_F>=0 because v_tilde is in F. For nonempty
C_N a valid corrected bound is

```
ell_gap = g-epsilon_E
          -sqrt(2u)[sqrt(epsilon_F)+sqrt(g+epsilon_F)]-u/2
        <= L_N(w_tilde).
```

A second valid bound, using the actual candidate/comparator difference, is

```
ell_dir = g-epsilon_E-r_N ||J'A(w_tilde-v_tilde)||
          -sqrt(2u epsilon_E)-u/2
        <= L_N(w_tilde).
```

It does not require a full-class optimality gap; any feasible w_tilde works.
One can use either bound or their maximum. With zero certified gaps the first
formula is exactly the Statement's bound. A strictly positive corrected bound
also forces w_tilde outside E: if w_tilde were in E, g<=epsilon_E and both
formulas would be nonpositive. Empty C_N still forces fallback. The pointwise
bound gives false-certification control for a data-selected approximate action
on the same coverage event, but the Statement's power bound is not transferred
to solvers with nonzero value gaps here.

**Proof.** Denote the exact optima by w_* and v_*, and their estimated gap by
G_exact=V_F-V_E. Strong concavity at these exact optima gives

```
||w_tilde-w_*||_Sigma <= sqrt(2 epsilon_F/gamma),
||v_tilde-v_*||_Sigma <= sqrt(2 epsilon_E/gamma),
||w_*-v_*||_Sigma <= sqrt(2 G_exact/gamma),
0 <= G_exact <= V_F-Q(v_tilde;theta_hat_N) <= g+epsilon_F,
```

where ||z||_Sigma=sqrt(z'Sigma z). For any theta=theta_hat_N-e in C_N the
already proved ETF value bound, centered at the exact v_*, gives

```
Adv(w_tilde;theta)
 >= Q(w_tilde;theta_hat_N)-V_E-e'A(w_tilde-v_*)-u/2.
```

The first difference is at least g-epsilon_E. The triangle inequality through
w_* bounds ||w_tilde-v_*||_Sigma by
sqrt(2/gamma)[sqrt(epsilon_F)+sqrt(g+epsilon_F)]. The mean-error inequality
from the proof then bounds its error by the two square-root terms in ell_gap.
Alternatively split w_tilde-v_*=(w_tilde-v_tilde)+(v_tilde-v_*). Bound the first
term directly by r_N||J'A(w_tilde-v_tilde)|| and the second by
sqrt(2u epsilon_E), proving ell_dir. Taking infima over C_N proves both claims.
Every inequality is uniform in theta in that same set, so selecting an
approximate action with the data does not require an additional union bound.

**Why simply adding value gaps is insufficient.** Review scope item 1 originally suggested
(gamma/2)||w_tilde-v_tilde||_Sigma^2<=g+epsilon_F. This does not follow from
approximate optimality. The safe triangle bound is instead

```
(gamma/2)||w_tilde-v_tilde||_Sigma^2
  <= [sqrt(epsilon_F)+sqrt(g+epsilon_F)]^2.
```

For this distance bound, use the triangle inequality through w_* and the
strong-concavity bound ||w_*-v_tilde||_Sigma<=sqrt(2(g+epsilon_F)/gamma).
Likewise centering the ETF value perturbation at v_tilde, rather than v_*, gives
an error at most epsilon_E+sqrt(2u epsilon_E)+u/2, not epsilon_E+u/2. The
extra term follows by writing v_*=v_tilde+(v_*-v_tilde) in the exact ETF
value bound and applying the mean-error inequality to the difference. The
formula ell_gap avoids this additional ETF square-root term by using v_* only
inside its proof; ell_dir includes it explicitly.

For a concrete M4 counterexample to the suggested shortcuts, take s=1/100,
J=s I_3 with independent sign U, B^A=(1,0), B^E=(0,1), gamma=1/s^2, zero costs
and drag, caps one, incumbent (2/5,1/4), and
Theta_4=(1/2,1/4,1/2)+[-1/10,1/10]^3. Its fund gross returns are positive at
every vertex and scenario. At theta_hat=(1/2,1/4,1/2), the score is
Q(a,p)=a-a^2+p/4-p^2/2. Set w_tilde=(3/5,1/4), v_tilde=(2/5,1/4).
The exact full optimizer is (1/2,1/4), and v_tilde is the exact ETF optimizer.
Then g=0, epsilon_F=1/100 and epsilon_E=0, but
(gamma/2)||w_tilde-v_tilde||_Sigma^2=1/25>1/100.

This can break the suggested certificate, not just its derivation. With N_obs=1,
the exact calibration has r_N^2=3 and u=3/10000. The estimate just specified
occurs with positive probability at theta_*=theta_hat-s(1,1,1), and theta_* is
in C_N. At this parameter the true whole-class advantage of w_tilde is
-81/20000. The shortcut g-epsilon_E-sqrt(2u(g+epsilon_F))-u/2 equals
-(20 sqrt(6)+3)/20000, which is larger than that advantage and hence larger
than L_N(w_tilde). The corrected ell_gap is -(40 sqrt(6)+3)/20000 and is valid.
For the ETF shortcut alone use v_tilde=(2/5,7/20): epsilon_E=1/200, while at
the same theta_* its ETF optimization loss is 121/20000, greater than
epsilon_E+u/2=103/20000. The cross term cannot generally be dropped.

**Numerical use.** Feasibility, score values, K, r_N and the value gaps need
certified bounds; a solver status or requested tolerance is not such a bound.
If objective arithmetic supplies g in [g_lo,g_hi], a safe interval version of
ell_gap uses g_lo outside the square root and g_hi+epsilon_F inside it, with
upper bounds for u and both epsilons. Valid inputs imply g_hi+epsilon_F>=0;
a negative value indicates inconsistent certificates, not a radicand to clamp.
Certified global upper values V_F^up,V_E^up and lower candidate scores q_F^lo,
q_E^lo give gaps epsilon_D=V_D^up-q_D^lo when nonnegative. Directed rounding or
interval evaluation is still needed in the displayed expression itself.

## Checks

`checks/018/check.py` independently solves two-asset funded quadratic programs
with asymmetric purchase/sale costs by exact region and face enumeration. It
checks the certificate with binding cash and cap constraints, correlated risk,
nonzero incumbents, active purchases and active sales, plus the normalization
of the lower-bound subfamily. These finite checks are not the general proof.
The approximate-solver follow-up checks both corrected bounds with exact value
gaps on the cost/cap fixtures, including negative candidate score gaps, and
reproduces the two shortcut counterexamples above. It also checks conservative
score intervals. These checks do not construct floating-point dual certificates.

## Not shown

- Positive gamma and positive-definite Sigma are essential hypotheses here.
  Singular risk, linear objectives, and no-curvature directions are not covered;
  claims 015-016's inverse-square economic-margin rates are not contradicted.
- The tail assumption is on a known standardized finite representation of the
  joint mean error. Arbitrary unknown laws, serial dependence, estimated loadings
  or covariances, repeated decisions and calibrated magnitudes remain outside M4.
- The lower bound is worst-case over designs and laws with K<=kappa, supplied
  by claim 017's slack-budget, zero-cost subfamily. No matching lower bound is
  proved for each particular cost schedule, binding face, or fixed finite law.
- K bounds all action directions, including infeasible ones, so it can be
  conservative. The certificate also bounds ETF movement and paired error
  separately. Exact joint minimization can certify more, as the claim 017
  follow-up demonstrates. No uniformly most powerful gate is claimed.
- The two plug-in optimizations are concave maximizations on convex compact
  sets, but a numerical solver's output still needs valid value/error bounds.
  The new remark supplies pointwise corrected formulas given those bounds; no
  floating-point certification algorithm, approximate-solver power guarantee or
  practical quantile runtime bound is supplied. This claim avoids directly
  minimizing L_N, not every computation.
- Alpha and premia enter jointly through A. The result does not identify manager
  skill separately or price uncertainty as a new risk term. It concerns one
  quarterly score, not a terminal-wealth utility problem.

## Prior art

Checked claims 004 and 014-017, their reviews, the D3 FINDINGS comparisons and
the refuted directory. The registered sources `petrik2016safe` (shared-model
fixed-baseline improvement), `esfahani2017data` (coverage protection for a
data-selected decision), `olivaresnadal2018technical` (uncertainty penalties),
and `manski1999statistical` (mean-gap-dependent expected welfare) already explain
why neither a norm penalty nor the coverage implication is new. No literature
theorem is imported; the curvature and probability inequalities are proved here
or inherited from the reviewed claim 017.

Strong concavity, quadratic optimizer gaps and stability of optimized values
are standard mathematical tools, and the inverse-advantage statistical order
is standard in kind. The D3 contribution is a whole-ETF-class certificate and
matching class-level bound that extend the rate beyond claim 017's separable
interior example to M4's directional fees, nonzero incumbents, correlated risk,
and binding constraints. The lower bound is not specific to those complications.
This is not a claim of statistical-method priority or a standalone publication
anchor; its scientific value and the calibrated experiment belong in D3's
closing assessment.

## Open objections

No unresolved objection to the numbered Statement or the solver-gap remark.
Red independently verified the remark on 2026-09-28 and revised Review scope
item 1 to withdraw its approximate-distance and ETF-perturbation shortcuts.
The remark remains a paper proof, not machine checked; machine checking covers
the numbered Statement only.

## Review

**Red, 2026-09-28.** I checked every step by hand, tested the certificate numerically on random general designs, and then probed the claim's scope.

**Hand check: every step holds.**
- *Quadratic gap.* Q = theta'Aw minus theta-free terms is gamma Sigma-strongly concave, because the costs are convex and Sigma is positive definite. Optimality over the convex class D along the segment, together with strong concavity, gives Q(w_D) - Q(v) >= (gamma/2)(1 - h) d'Sigma d for every h. Letting h -> 0 proves the quadratic gap with no differentiability, interiority or active-set assumption. So cost kinks and binding cash or caps are covered.
- *Error bound.* The minimum-norm y = J^dagger e has ||y||^2 = e'(JJ')^dagger e, since Im(JJ') = Im(J), and the definition of K gives |e'Ad| <= r sqrt(gamma K d'Sigma d). This covers singular J.
- *ETF value bound.* For every v in E, Q(v; theta_hat - e) <= Q(v_hat_E; theta_hat) - e'A v_hat_E - (gamma/2)t^2 + r sqrt(gamma K) t, with t = sqrt(d_E'Sigma d_E). The maximum over t is K r^2/2. The supremum over the whole class E is taken before any selected comparator appears, so the moving and constrained ETF optimum is controlled.
- *Certificate.* G_hat >= (gamma/2)(w_hat_F - v_hat_E)'Sigma(w_hat_F - v_hat_E), since v_hat_E is in F. Then |e'A d| <= r sqrt(2 K G_hat) gives Adv >= G_hat - sqrt(2 u G_hat) - u/2 on all of C_N. ell > 0 forces G_hat > 0, which forces w_hat_F outside E, a genuine active change even with a nonzero incumbent.
- *Power.* Swapping the roles of theta_hat and theta_* uses the same symmetric error set and optimality at an arbitrary real parameter, giving G_hat >= f_u(G_*). f_u is increasing for g >= u/2. The two evaluations give 223 delta/256 and then 3 delta/4 - (sqrt(3)/16) delta - delta/256 ≈ 0.638 delta > delta/2.
- *Sample length.* t_{N,epsilon} <= 12 log(6/epsilon), inherited from claims 016-017, and 12 x 128 = 1536.
- *Lower-bound reduction.* Claim 017 with s = sqrt(kappa) has A = [[1,0],[0,1],[1,0]] and ||J'Az||^2 = s^2(2 z_1^2 + z_2^2) = z'Sigma z, so K = s^2 = kappa. Its ranges s <= 1/100 and delta <= s^2/128 are exactly kappa <= 1/10000 and delta <= kappa/128. The quantifiers are in the right order: a common length for the larger class must also work on the subfamily.

**Independent numerics** (red's own script, written without reading `checks/018/check.py`; floating CLARABEL, not certificates).
- *Designs.* 40 random M4 designs with one or two ETFs: random positive loadings, correlated positive-definite Sigma, J singular in 30% of cases, directional purchase and sale rates up to 1%, nonzero incumbents, small cash, tight caps and signed drag. In 38 of the 40, the full optimum has a binding cash or cap constraint.
- *Certificate.* For each design and r in {0.3, 1, 3}, I evaluated Adv(w_hat_F; theta_hat - J y) against the fully re-optimized ETF class at ||y|| = r, in 52 directions including ±J'A(w_hat_F - v_hat_E). All 6240 values satisfy Adv >= ell_N; the smallest slack is 9.8e-4 and the median 7.2e-2. Sampled directions bound the infimum only from above, so this is an attack, not a proof.
- *Power.* With G_*(theta_*) = delta and random errors of Mahalanobis radius at most sqrt(delta/(128 K)), all 288 tests give ell_N > delta/2.
- *Subfamily and own check.* K for claim 017's subfamily equals s^2 numerically, and the claim's own check passes.

**Scope (sharpenings).**
1. **The certificate needs exact plug-in optima** (revised 2026-09-28 after math's correction). The quadratic gap uses exact optimality of both v_hat_E and w_hat_F. The corrections this item originally proposed were **wrong**: the distance bound (gamma/2) d'Sigma d <= G_hat + epsilon_F, and an ETF bound gaining only epsilon_E. The remark's exact M4 examples refute both; see the addendum below. The valid corrections are the remark's ell_gap and ell_dir.
2. **The lower bound is only as general as claim 017's subfamily,** which has slack funding, zero costs and separable risk. For a particular cost schedule or binding face the rate could be faster. The class-level "matching order" is honest because K <= kappa includes that subfamily.
3. **Constants are about 8 x 10^5 apart:** 1536 against 1/(32 pi^2), times log(6/epsilon)/log(1/epsilon). K is also a worst case over all action directions, including infeasible ones, as stated.
4. **This is standard strong-concavity value stability.** The claim's own framing is accurate: the content is carrying the whole-ETF-class target through costs, kinks and binding constraints, not a new statistical rate. As in claims 015-017, A mixes alpha with premia.


**Red addendum, 2026-09-28: review of the remark "certified gaps for approximate optimizer outputs". Result: verified.**
- *ell_gap.* The proof centres the already proved ETF value bound at the exact v_*, giving Adv(w_tilde; theta) >= Q(w_tilde; theta_hat) - V_E - e'A(w_tilde - v_*) - u/2, where the first difference is >= g - epsilon_E. Strong concavity at the exact optima gives ||w_tilde - w_*||_Sigma <= sqrt(2 epsilon_F/gamma) and ||w_* - v_*||_Sigma <= sqrt(2 G_exact/gamma), with G_exact = V_F - V_E <= V_F - Q(v_tilde) = (V_F - Q(w_tilde)) + g <= g + epsilon_F. Combining these with the mean-error inequality gives the two square-root terms. With zero gaps it reduces to the Statement's bound.
- *ell_dir.* It splits w_tilde - v_* at v_tilde, with r_N ||J'A(w_tilde - v_tilde)|| directly and sqrt(2 u epsilon_E) for v_tilde - v_*. It needs only feasibility of w_tilde.
- *Positivity.* Either bound being positive forces w_tilde outside E, since g <= epsilon_E otherwise.
- *Interval inputs.* Using g_lo outside the root, g_hi + epsilon_F inside it, and upper bounds on u and both epsilons, is the conservative direction, because each term is bounded separately. The remark correctly states that the approximate-solver case carries no power transfer.
- *Counterexamples, reproduced exactly (rationals).* In the distance counterexample g = 0, epsilon_F = 1/100, epsilon_E = 0 and (gamma/2)||w_tilde - v_tilde||_Sigma^2 = 1/25. With N_obs = 1, u = 3/10000 and theta_* = theta_hat - s(1, 1, 1), the true advantage is -81/20000. My shortcut gives -(20 sqrt(6) + 3)/20000 ≈ -0.00260, which is *above* the true advantage and therefore invalid. The corrected ell_gap = -(40 sqrt(6) + 3)/20000 ≈ -0.00505 is valid. In the ETF counterexample, v_tilde = (2/5, 7/20) has epsilon_E = 1/200 but a loss of 121/20000 at theta_*, which exceeds epsilon_E + u/2 = 103/20000. With the cross term, the bound is 0.006882 >= 0.00605.
- *Stress test* (floating CLARABEL, not a certificate). On 30 random constrained designs (binding cash or caps, directional costs, correlated risk, singular J in some), I used approximate feasible candidates obtained by shrinking the exact optima toward the incumbent, with their exact value gaps. All 5040 tests of Adv >= max(ell_gap, ell_dir), along adversarial and random directions of the error ball, hold. The smallest slack is 6.3e-5. `checks/018/check.py` passes.

The formula may be used by experiment 011, subject to the remark's own conditions: certified feasibility, value gaps, K and r_N, and directed rounding.
**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* For a strongly concave parametric program in which the parameter enters linearly, optimal values and optimizers are stable: the value error is at most quadratic in the parameter error's curvature-weighted norm, including under nonsmooth convex terms and binding constraints.
- *General result.* Perturbation analysis of parametric programs under the quadratic-growth or strong-concavity condition (Bonnans-Shapiro). A quadratic gap at the optimizer gives Lipschitz and Hölder stability of solutions and a second-order value bound, without differentiability or constraint qualification in the fixed-feasible-set case.
- *Reduction.* M4's feasible sets are fixed, convex and compact. The score is gamma Sigma-strongly concave (costs convex, Sigma positive definite) and affine in theta through A. K is the dual-norm ratio between the error covariance and the curvature. The claim's value bound and quadratic gap are exactly the general bounds. The rate reduction goes through claim 017.
- *Verdict: special case,* as the human referee said. Left over: carrying the whole-ETF-class target through the bound, and the solver-gap remark.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check (strong-concavity quadratic gap without differentiability or interiority, covering cost kinks and binding cash or caps; the minimum-norm error bound covering singular J; the ETF bound taken over the whole class before any selected comparator; the certificate forcing a genuine active change; power; the lower-bound reduction to claim 017 with K=s^2) and independent numerics (40 general designs, 38 with binding constraints; 6240 certificate evaluations; 288 power tests) are sound, and PM reran checks/018; no open objections. Limits stated: the certificate assumes exact global plug-in optima, so a numerical implementation must subtract certified optimality gaps (formula routed to math); the lower bound is only as general as claim 017's subfamily; constants about 8x10^5 apart; standard strong-concavity stability, alpha mixed with premia.


Not machine checked. Core obligations are compact finite-dimensional action
geometry, the strong-concavity gap without differentiability, matrix error
bounds, finite confidence calibration and the reduction to claim 017's lower
bound. No optimizer stability or rate is assumed as a hypothesis.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4CurvatureCertificate.lean` and the
proof in `lean/Novel/M4CurvatureCertificateProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used, and no optimizer
stability, tail bound or rate is assumed.

Formal objects. M4 comes from claim 014's statement file and K_J (`InKJ`) from claim 016's. The
setting `CurvSetting` is any admissible M4 instance with any n, gamma > 0, z'Sigma z > 0 for
z != 0, a law in K_J and zeta = J U. Costs, caps, drag, incumbent and ETF residuals are
unrestricted beyond M4 admissibility, and J is arbitrary (possibly singular). K is (1/gamma) times
the supremum of the ratio over nonzero z. G_hat uses M4's plug-in selections w_hat_F and v_hat_E,
and the gate certifies when C_N is nonempty and ell_N > delta_econ. Rules map each full history to
a probability measure on holdings carried by the funded holdings with a != a^- and the funded E
holdings; certifying means a != a^-. The proof imports claim 004's and claim 017's proof modules,
as Q-04 allows for depends_on [4, 17].

Proved, for every design and law in the setting:
1. 0 <= K; ||J'Az||^2 <= gamma K z'Sigma z for every z, with equality at some z with
   z'Sigma z = 1. At every real parameter the plug-in maximizer sets are exactly {w_hat_F} and
   {v_hat_E}, and G_hat >= 0. For N_obs >= 1 and nonempty C_N, ell_N <= L_N(w_hat_F).
   ell_N > delta_econ >= 0 forces a != a^-. The gate's false-certification probability is at most
   eta at every theta in Theta_4, for every N_obs >= 1, eta >= 0 and delta_econ.
2. For every estimate and every theta in its C_N with G_*(theta) >= delta, u_N <= delta/128 gives
   ell_N > delta/2. For epsilon in (0, 1), N_obs >= max(324, 1536 K/delta) log(6/epsilon) gives the
   rule restriction and both requirements with delta_econ = delta/4. If K = 0, ell_N = G_*(theta)
   on every history at every N_obs >= 1.
3. With the prose's ranges, the class lower bound kappa log(1/epsilon)/(32 pi^2 delta). For
   epsilon in (0, 1), sufficiency of 1536 (kappa/delta) log(6/epsilon) for every member with
   K <= kappa. For every kappa in (0, 1/10000], a member with K = kappa.

The proof.
- The score is theta'Aw plus a theta-free part whose concavity defect is exactly
  (gamma/2) a b (x-y)'Sigma(x-y), by claim 004's convex cost and sum-of-squares risk. The
  quadratic gap at a maximizer over a convex set follows by the h -> 0 argument, with no
  differentiability. Existence uses claim 004's compact classes; uniqueness follows from the gap
  and positive definiteness, so G_* = G_hat at every parameter.
- K: the ratio is continuous and homogeneous of degree zero, so it attains its maximum on the
  unit sphere.
- Omega = J J' from E U U' = I. Claim 016's pseudoinverse lemmas give e = J y with
  ||y||^2 <= r_N^2 for e in A_{N,eta}, hence (e'Ad)^2 <= gamma u_N d'Sigma d.
- The ETF value bound is proved over the whole class E for any two parameters whose difference
  satisfies that inequality. With (theta, theta_hat) it gives ell_N <= Adv; with the roles
  reversed it gives G_hat >= f_u(G_*). The power constant uses f_u(g) >= 4g/5 for 96u <= g, so
  ell_N >= 16 delta/25.
- Sufficiency reuses claim 016's variance tail, with its quantile lemmas restated for any number
  of ETFs: t_{N,epsilon} <= 12 log(6/epsilon) once N_obs >= 81 log(6/epsilon).
- The lower bound applies the class hypothesis to claim 017's family with s = sqrt(kappa) and
  J = s I (so K = s^2). It converts the rules (a != 0 and a > 0 agree on funded holdings, and the
  rest is null) and applies claim 017's lower bound. The member with K = kappa uses claim 016's
  latent law.

Relation to the prose. No gap was found between the formal statement and the Statement. Some
formal parts are stronger: the false-certification bound holds for every delta_econ, the coverage
implication holds at every estimate, and sufficiency needs only epsilon < 1. The remark on
certified gaps for approximate optimizer outputs was added after approval, is not yet reviewed,
and is not formalized here. The limits PM recorded at approval apply unchanged:
- the certificate assumes exact global plug-in optima (the formal G_hat is built from M4's exact
  maximizers), so a numerical implementation must subtract certified optimality gaps;
- the lower bound is only as general as claim 017's subfamily;
- the constants are about 8x10^5 apart;
- this is standard strong-concavity stability, with alpha mixed with premia.

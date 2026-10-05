---
id: 20
title: "The optimized ETF class is its finite face set exactly when the score is linear or the ETF-only optimizer is constant on the domain"
status: formalized
model_version: M4
depends_on: [17, 18]
axioms_used: [AX-05]
formal: lean/Standalone/M4FiniteComparatorFacesIff.lean
direction: D5
---
## Statement

This is the refile of claim 019 (refuted as filed: its universal "never when
the score is curved" was false, while every numbered part was verified by
red). It answers the deterministic part of D5's first question, what the
funded whole-class ETF comparator (moving cash and ETF faces, directional
costs, binding cash and caps) changes in validity, rate or tractability
relative to applying general certification results to a finite set of
comparator faces. It is a statement about the target functions Adv, G_* and
L_N; it makes no probability statement. The only literature input is the
linear-programming vertex theorem `AX-05` (rule 21), used through its
hypotheses only.

**Setting.** Any admissible M4 instance: one active fund, n in {1,2} ETFs,
caps bar w, a compliant incumbent w^-=(a^-,p^-) with k^->=0, directional
rates kappa^+_i,kappa^-_i in [0,1), signed drag c^E, gamma>=0, and M4's
classes F, E and score

```
Q(w;theta)=theta'A w+c(w)-(gamma/2)w'Sigma w,
c(w)=-p'c^E-tau(w-w^-),
```

with A the mean-exposure matrix of claim 018. All statements hold for every
real theta through the affine extension unless a domain is named.

**Definitions.** For sigma in {+1,-1}^{1+n} the cost-sign cell is

```
F_sigma={w in F: sigma_i (w_i-w^-_i)>=0 for all i},
```

and for rho in {+1,-1}^n, E_rho={w in E: rho_j (p_j-p^-_j)>=0 for all j};
the description of E_rho by 3n+1 halfspaces in the ETF coordinates with
a=a^- uses the compliant incumbent the Setting assumes (0<=a^-<=bar a and
k^->=0).
The face sets are Vert(F)=union over sigma of ext(F_sigma) and
Vert(E)=union over rho of ext(E_rho), ext denoting extreme points. For v in E
the single-comparator contrast is m_v(w;theta)=Q(w;theta)-Q(v;theta). The
finite contrast set is D={A(u-v): u in Vert(F), v in Vert(E)}. For gamma>0
and positive-definite Sigma, v_E(theta) denotes the unique E maximizer at
theta (claim 018), and a finite set S in E is *exact on a set T of
parameters* when V_E(theta)=max_{v in S} Q(v;theta) for every theta in T.

1. **Face sets are finite and fixed by the funded geometry.** Every cell is a
   nonempty compact polyhedron containing w^-, described by 3(1+n)+1
   (for F) or 3n+1 (for E) closed halfspaces. By `AX-05`, Vert(E) and Vert(F)
   are finite, and they depend only on (bar w, w^-, k^-, kappa^+, kappa^-):
   not on theta, the law, Sigma, gamma or c^E. Crude counts:

   ```
   |Vert(E)| <= 2^n binom(3n+1,n)      (8 for n=1, 84 for n=2),
   |Vert(F)| <= 2^(n+1) binom(3n+4,n+1) (84 for n=1, 960 for n=2).
   ```

   For n=1 exactly

   ```
   Vert(E)={(a^-,0), (a^-,p^-), (a^-, p^-+min(bar p-p^-, k^-/(1+kappa^+_E)))}:
   ```

   sell the ETF out, hold it (the incumbent's cost kink), or buy it to the cap
   or to cash exhaustion, whichever comes first. Directional costs add the
   kink face; binding cash and caps decide the third.

2. **Exact finite reduction when gamma=0.** For every theta in R^3 and w in F,

   ```
   V_E(theta)=max_{v in Vert(E)} Q(v;theta),  V_F(theta)=max_{u in Vert(F)} Q(u;theta),
   Adv(w;theta)=min_{v in Vert(E)} m_v(w;theta),   each m_v(w;.) affine in theta,
   G_*(theta)=max_{u in Vert(F)} min_{v in Vert(E)} m_v(u;theta).
   ```

   For every nonempty set C in R^3,

   ```
   inf_{theta in C} Adv(w;theta) = min_{v in Vert(E)} inf_{theta in C} m_v(w;theta).
   ```

   In particular, for nonempty C_N, L_N(w)=min_v inf_{C_N} m_v(w;.), each
   inner term the minimum of an affine function over the compact convex C_N,
   a convex program. On empty C_N, M4 sets L_N=-infinity and the rule falls
   back, so neither this identity nor ell_N below is used. Without
   the domain intersection the inner infimum over theta_hat_N-A_{N,eta} is the
   closed form

   ```
   m_v(w;theta_hat_N)-r_N sqrt(d'Omega d),   d=A(w-v),  r_N=sqrt(t_{N,eta}/N_obs),
   ```

   attained at e=r_N Omega d/sqrt(d'Omega d) when d'Omega d>0. Hence, for
   nonempty C_N,

   ```
   ell_N(w)=min_{v in Vert(E)} [m_v(w;theta_hat_N)-r_N sqrt(d_v'Omega d_v)] <= L_N(w),
   ```

   the proposal's paired mean-uncertainty penalty, minimized over the finite
   faces. Moreover M4's lexicographic plug-in optimizers satisfy
   w_hat_F in Vert(F) and v_hat_E in Vert(E) at every history, so the
   contrast vectors any history can require lie in the finite set D, fixed
   before sampling.

3. **What follows for any confidence construction, gamma=0.**
   (a) *Validity from finitely many scalar statements.* Suppose that on an
   event Ev every d in D satisfies d'theta_* in I_d for intervals I_d, which
   may depend on the data, and put C_D={theta: d'theta in I_d for all d in D}.
   Then theta_* in C_D on Ev, and the rule "implement w_hat_F if
   a_hat != a^- and

   ```
   ell_D(w_hat_F)=min_{v in Vert(E)} [inf I_{A(w_hat_F-v)}+c(w_hat_F)-c(v)] > delta_econ,
   ```

   otherwise v_hat_E" satisfies ell_D(w_hat_F) <= inf_{C_D} Adv(w_hat_F;.)
   <= Adv(w_hat_F;theta_*) on Ev. It never falsely certifies on Ev, uniformly
   over the data-selected candidate, and it uses only the |D| scalar
   sequences d'X_l, whose means are d'theta_*. No vector-valued confidence set
   is required. Nothing is asserted about which laws or times admit such an
   event, or about its power.
   (b) *Rate geometry.* For delta_e>=0 the no-certifiable-advantage set is

   ```
   Null(delta_e)={theta: G_*(theta)<=delta_e}
                =intersection_{u in Vert(F)} union_{v in Vert(E)} H_{uv}(delta_e),
   H_{uv}(delta_e)={theta: m_v(u;theta)<=delta_e},
   ```

   each H_{uv} a closed halfspace, all of R^3 or empty. Null is a finite
   union of polyhedra, and for every nonnegative function psi on R^3,

   ```
   inf_{Null(delta_e)} psi >= max_{u in Vert(F)} min_{v in Vert(E)} inf_{H_{uv}(delta_e)} psi.
   ```

   Applied to psi = the divergence from theta to a parameter, this is the
   "best face against its hardest comparator face" structure of claim 016's
   lower bound; it is an inequality, not the exact alternative set of any
   particular lower bound.

4. **Curvature deficit when gamma>0.** In any admissible M4 instance with
   gamma>0 and positive-definite Sigma, for every finite S in E and every real
   theta,

   ```
   V_E(theta)-max_{v in S} Q(v;theta) >= (gamma/2) min_{v in S} ||v-v_E(theta)||_Sigma^2.
   ```

   For every w in F the finite-comparator contrast min_{v in S} m_v(w;theta)
   exceeds Adv(w;theta) by exactly this deficit. It is a lower bound on the
   whole-class advantage only after subtracting it, so a finite-face rule that
   holds the overstatement below delta_e everywhere needs S to be a
   sqrt(2 delta_e/gamma)-net, in Sigma-norm, of the optimizer path
   {v_E(theta): theta in Theta_4}. In claim 017's family (s in (0,1/100],
   gamma=1/s^2), for every m-point S in E there is theta in Theta_4 with
   deficit at least s^2/(2(m+1)^2), and at such a theta with
   lambda_1+alpha=0 the funded active action w=(s/(2(m+1)),lambda_2) has

   ```
   Adv(w;theta)=-s^2/(4(m+1)^2)<0   while   min_{v in S} m_v(w;theta)>=s^2/(4(m+1)^2)>0:
   ```

   every one of the m pairwise comparisons certifies an action strictly worse
   than the whole ETF class. Holding the deficit below delta_econ=delta/4 with
   delta<=s^2/128 needs m+1>=s sqrt(2/delta)>=16 comparators, a number growing
   like delta^(-1/2), whereas claim 018's certificate uses no comparator set:
   two concave maximizations.

5. **When a finite face set is exact under curvature.** Let gamma>0, Sigma
   be positive definite, and T be a convex set of parameters (for example
   Theta_4, or its intersection with a confidence set). Then a finite S in E is
   exact on T if and only if v_E is constant on T, and then S must contain
   that constant optimizer. Consequently a finite face set can be exact under
   curvature: in experiment 009's reviewed fixture (gamma=2, one ETF with
   B^E=(1,0), incumbent (3/10,1/2,1/5), symmetric rates of 20 and 5 bp, all
   shocks scaled by 1/10, Theta_4=[1/100,3/100]x[0,1/50]x[-1/20,1/10]) the
   ETF-only optimizer is the cash-exhausting purchase (3/10, 2801/4002) at
   every theta in Theta_4, because the score's left derivative in p there is
   affine in theta with minimum 2600957/276000000>0 over the box's vertices;
   so the single comparator {(3/10, 2801/4002)} has zero deficit. An ETF cap
   of zero makes E a singleton and is the degenerate case. And a finite face
   set fails whenever the optimizer moves, as in claim 017's family, where
   part 4 quantifies the failure.

**Consequence for D5's question** (a reading of 1-5, not a further theorem).
With a linear score (gamma=0) the funded whole-class comparator changes
nothing relative to its finite faces: it is its finite faces, for every
candidate, every parameter set and every law. The funded geometry decides only
which faces exist. With a curved score (gamma>0) the class is a finite face
set exactly when the ETF-only optimizer does not move on the domain; once it
moves, no finite face set is exact, the deficit is a curvature term, and the
whole-class curvature certificate of claim 018 replaces face enumeration.
That gain is strong concavity's, a known perturbation mechanism, not an effect
of funding, costs or binding constraints. No change of rate is shown in either
case.

## Proof

### Cited facts (AX-05) and one elementary supplement

`AX-05` supplies, for a nonempty bounded polyhedron P={x in R^m: g_l'x<=h_l,
l=1..L}: (i) P has finitely many extreme points, each the unique solution of
m linearly independent active constraints, hence at most binom(L,m) of them;
(ii) every affine function attains its maximum over P at an extreme point.
The hypotheses are checked for each cell in Part 1 below. The only supplement
proved here concerns lexicographic minima:

(iii) *The lexicographically smallest maximizer of an affine l over P is an
extreme point of P.* The maximizer set M=P intersect {l>=max_P l} is again a
nonempty bounded polyhedron, and M is a face of P: if x in M is the midpoint
of y,z in P then l(y),l(z)<=max and their mean equals max, so y,z in M. The
lexicographic minimum x_lex of the compact M exists (minimize coordinates in
order over nested compact sets). It is extreme in M: if x_lex=(y+z)/2 with
y!=z in M, at the first index i where y_i!=z_i, say y_i<z_i, the earlier
coordinates of y agree with x_lex and y_i<x_lex,i, so y precedes x_lex, a
contradiction. Extreme in the face M means extreme in P: a midpoint
representation in P lies in M, where it is impossible.

### Part 1: the cells

Fix sigma. On F_sigma the trade w-w^- has the sign pattern sigma coordinate
by coordinate, so

```
tau(w-w^-)=sum_i kappa^{sigma_i}_i sigma_i (w_i-w^-_i)=t_sigma'(w-w^-),
k(w)=k^- - (1+t_sigma)'(w-w^-),
```

where kappa^{+1}=kappa^+, kappa^{-1}=kappa^-, and 1+t_sigma has coordinates
1+sigma_i kappa^{sigma_i}_i. Hence

```
F_sigma={w: 0<=w_i<=bar w_i, sigma_i(w_i-w^-_i)>=0, (1+t_sigma)'(w-w^-)<=k^-},
```

an intersection of 2(1+n)+(1+n)+1=3(1+n)+1 closed halfspaces inside the box,
so bounded; it contains w^- because the incumbent is compliant and k^->=0.
Every w in F has some sign pattern, so F is the union of the 2^(1+n) cells.
The same holds for E with the active coordinate fixed at a^-: E_rho is
described in the n ETF coordinates by 3n+1 halfspaces, and E is the union of
the 2^n cells E_rho. These are exactly the hypotheses of `AX-05`(i), which
gives the counts. The descriptions involve only bar w, w^-, k^- and the
rates, which proves the independence statement.

For n=1, on E_- (sales, p<=p^-) the cash inequality reads
(1-kappa^-_E)(p-p^-)<=k^-, which holds automatically since its left side is
nonpositive and kappa^-_E<1; so E_-=[0,p^-]. On E_+ it reads
(1+kappa^+_E)(p-p^-)<=k^-, so E_+=[p^-, p^-+min(bar p-p^-, k^-/(1+kappa^+_E))].
The extreme points of an interval are its endpoints, which gives the three
listed holdings (two coincide when p^-=0 or when the upper endpoint equals p^-).

### Part 2: exact reduction for gamma=0

With gamma=0, on each cell F_sigma the score is theta'Aw-p'c^E-t_sigma'(w-w^-),
affine in w. By `AX-05`(ii) the maximum of Q(.;theta) over F_sigma is
attained on ext(F_sigma), so max over F, a finite union of cells, equals the
maximum over Vert(F). The same argument on E gives V_E(theta)=max over
Vert(E). Then

```
Adv(w;theta)=Q(w;theta)-max_{v in Vert(E)} Q(v;theta)=min_{v in Vert(E)} m_v(w;theta),
```

and m_v(w;theta)=theta'A(w-v)+c(w)-c(v) is affine in theta. G_* follows by
maximizing over u in Vert(F). For any nonempty C, the infimum of a minimum of
finitely many functions is the minimum of their infima, which is the
displayed identity; the identity for L_N applies it to C=C_N and therefore
needs C_N nonempty, since M4's convention L_N=-infinity on an empty C_N
differs from the infimum over the empty set.

*Closed form on the error set.* Let J=Omega^{1/2} be the symmetric square
root, so Omega=J J, Im(Omega)=Im(J), and Omega^dagger=(J^dagger)^2. For e in
Im(Omega) write y=J^dagger e in Im(J); then e=Jy and e'Omega^dagger e=||y||^2.
For any d,

```
e'd=y'Jd <= ||y|| ||Jd|| = ||y|| sqrt(d'Omega d).
```

Over A_{N,eta}, ||y||<=r_N, so sup e'd<=r_N sqrt(d'Omega d). If d'Omega d>0,
y=r_N Jd/||Jd|| lies in Im(J), has norm r_N, and gives
e=r_N Omega d/sqrt(d'Omega d) with e'd=r_N sqrt(d'Omega d). If d'Omega d=0 then
Jd=0 and e'd=0 for every e in Im(Omega). Substituting theta=theta_hat_N-e in
the affine contrast gives the closed form and its attainment. Intersecting with
Theta_4 can only raise the infimum, so ell_N(w)<=L_N(w) whenever C_N is
nonempty; for empty C_N, L_N=-infinity by M4's convention and no bound is
claimed. Each inner problem
over C_N is a linear function minimized over a compact convex set.

*Plug-in optimizers are faces.* The maximizer set of Q(.;theta_hat_N) over F
is the union over sigma of M_sigma={w in F_sigma: Q(w)=V_F}, each either empty
or the maximizer set of an affine function over the polyhedron F_sigma. The
lexicographically smallest point of a finite union is the lexicographic
minimum of one of the nonempty M_sigma, which by (iii) is an extreme point of
F_sigma. The same holds for v_hat_E on E. Therefore every contrast
A(w_hat_F-v) with v in Vert(E), and every contrast between the two plug-in
selections, lies in D.

### Part 3: consequences

(a) On Ev, every d in D satisfies d'theta_* in I_d, so theta_* in C_D. For
each v in Vert(E), inf over theta in C_D of m_v(w_hat_F;theta) is at least
inf I_{A(w_hat_F-v)}+c(w_hat_F)-c(v), because theta in C_D forces
A(w_hat_F-v)'theta in that interval (w_hat_F in Vert(F) puts this contrast in
D). Taking the minimum over v and using Part 2 with C=C_D,

```
ell_D(w_hat_F) <= min_v inf_{C_D} m_v = inf_{C_D} Adv(w_hat_F;.) <= Adv(w_hat_F;theta_*).
```

A certification requires ell_D>delta_econ, hence Adv(w_hat_F;theta_*)>delta_econ
on Ev: no false certification there. The bound depends on the data only
through the intervals for the finitely many functionals d'theta, so it is the
same argument for every data-selected candidate. This is the whole content;
existence of Ev with a stated probability under a given law class is a
statement about that class and is not made here.

(b) By Part 2, G_*(theta)<=delta_e holds if and only if for every u in
Vert(F) some v in Vert(E) has m_v(u;theta)<=delta_e; that is the displayed
intersection of unions. Each H_{uv} is {theta: A(u-v)'theta<=delta_e-c(u)+c(v)},
a closed halfspace when A(u-v)!=0 and otherwise R^3 or empty. Distributing the
intersection over the unions writes Null as a union, over choice functions
v(.) on Vert(F), of the polyhedra intersect_u H_{u v(u)}: finitely many. For
the inequality, fix u; Null is contained in union_v H_{uv} because every point
of Null satisfies the u-th condition; hence inf over Null of psi is at least
inf over that union, which is min_v inf_{H_{uv}} psi. Taking the maximum over u
proves it.

### Part 4: the curvature deficit

Let gamma>0 and Sigma be positive definite. Claim 018 (formalized) proves,
for every real theta and every v in E, the quadratic gap

```
Q(v_E(theta);theta)-Q(v;theta) >= (gamma/2)(v-v_E(theta))'Sigma(v-v_E(theta)),
```

with v_E(theta) the unique maximizer over E. Taking the maximum over v in a
finite S gives the deficit inequality. For w in F,

```
min_{v in S} m_v(w;theta) = Q(w;theta)-max_S Q = Adv(w;theta)+[V_E(theta)-max_S Q],
```

which is the exact overstatement. If a finite-face rule is to overstate by at
most delta_e at every theta in Theta_4, the deficit inequality forces
min_{v in S}||v-v_E(theta)||_Sigma <= sqrt(2 delta_e/gamma) for every theta in
Theta_4, the net statement.

In claim 017's family (formalized), E={(0,p): 0<=p<=1},
Q((0,p);theta)=p lambda_2-p^2/2, v_E(theta)=(0,lambda_2), V_E=lambda_2^2/2 for
lambda_2 in [1/4-s,1/4+s], and Adv((a,p);theta)=a x-a^2-(p-lambda_2)^2/2 with
x=lambda_1+alpha. For S={(0,p_1),...,(0,p_m)},

```
V_E(theta)-max_S Q = min_i (lambda_2-p_i)^2/2.
```

The m open intervals of half-width s/(m+1) around the p_i have total length at
most 2sm/(m+1)<2s, the length of [1/4-s,1/4+s], so some lambda_2 in that
interval is at distance at least s/(m+1) from every p_i, giving deficit at
least s^2/(2(m+1)^2). The domain c+s[-1,1]^3 with c=(0,1/4,0) contains
(lambda_1,lambda_2,alpha)=(0,lambda_2,0), where x=0. Take
w=(a,lambda_2) with a=s/(2(m+1))<=1/400: it is in the box, a+lambda_2<1 so
cash stays nonnegative with zero costs, and it is an active action since
a^-=0. Then Adv(w;theta)=-a^2=-s^2/(4(m+1)^2) and

```
min_{v in S} m_v(w;theta) = -a^2+[V_E-max_S Q] >= -s^2/(4(m+1)^2)+s^2/(2(m+1)^2) = s^2/(4(m+1)^2).
```

Finally, deficit at most delta_e=delta/4 everywhere requires
s^2/(2(m+1)^2)<=delta/4, that is m+1>=s sqrt(2/delta), and delta<=s^2/128
makes the right side at least 16. Claim 018's certificate for this family is
its part 1, evaluated with two concave maximizations and no comparator set.

### Part 5: exactness under curvature

*Exact if and only if constant.* If v_E is constant on T, equal to v_0, then
S={v_0} (or any finite S containing v_0) has V_E(theta)=Q(v_0;theta) for every
theta in T: exact. Conversely suppose a finite S is exact on T. By Part 4's
deficit inequality, exactness at theta forces min_{v in S}||v-v_E(theta)||_Sigma=0,
that is v_E(theta) in S, so the image v_E(T) is contained in the finite set
S. It remains to show that a nonconstant v_E on a convex T has an infinite
image. Take theta_a,theta_b in T with v_a=v_E(theta_a)!=v_b=v_E(theta_b), and
the segment theta(t)=(1-t)theta_a+t theta_b, t in [0,1], which lies in T.

*Continuity along the segment.* Write phi(t)=v_E(theta(t)). For t,t' in
[0,1], the score difference between the two parameters is
(theta(t)-theta(t'))'A v, uniformly bounded over the compact E by
L|t-t'| with L=||theta_b-theta_a|| max_{v in E}||A v||. Claim 018's quadratic
gap at theta(t) applied to v=phi(t'), and at theta(t') applied to v=phi(t),
give

```
Q(phi(t);theta(t))-Q(phi(t');theta(t)) >= (gamma/2)||phi(t)-phi(t')||_Sigma^2,
Q(phi(t');theta(t'))-Q(phi(t);theta(t')) >= (gamma/2)||phi(t)-phi(t')||_Sigma^2.
```

Adding them, the left side is [Q(phi(t);theta(t))-Q(phi(t);theta(t'))]
+[Q(phi(t');theta(t'))-Q(phi(t');theta(t))], each bracket at most L|t-t'|.
Hence gamma||phi(t)-phi(t')||_Sigma^2<=2L|t-t'|, and phi is continuous.

*Infinite image.* Let u=v_b-v_a and g(t)=u'Sigma phi(t), a continuous real
function on [0,1] with g(0)=u'Sigma v_a and g(1)=u'Sigma v_b, which differ by
u'Sigma u>0. By the intermediate value theorem g takes every value between
them, so it takes infinitely many values, and phi has infinite image. This
contradicts v_E(T) in S. Hence exactness forces v_E constant on T, and then
S contains the constant value by the first inclusion.

*Red's instance.* In experiment 009's reviewed fixture, E is the segment
{(3/10,p): 0<=p<=2801/4002}: the cap of one is not reached because the cash
1/5 exhausts at p^-+k^-/(1+kappa^+_E)=1/2+(1/5)/(1+1/2000)=2801/4002. On the
purchase side the score is a strictly concave quadratic in p whose derivative
at the endpoint, lambda_1-gamma(Sigma_EA a^-+Sigma_EE p)-kappa^+_E, is affine
in theta; its minimum over the eight vertices of the box is
2600957/276000000>0 (the exact number is reproduced in `checks/020/check.py`
from red's fixture primitives), so the score increases up to the endpoint on
every parameter of the box, and the endpoint is the unique maximizer
throughout. The degenerate case is a zero ETF cap, when E is a singleton and
any finite S containing it is exact.

## Checks

`checks/020/check.py` (exits non-zero on failure; a check, not a proof).
Part A draws 120 random gamma=0 designs with one or two ETFs, directional
purchase and sale rates, caps, incumbents at zero, interior or at the cap, and
cash including zero. It enumerates Vert(E) and Vert(F) exactly in rational
arithmetic from the cost-sign cells and checks: the face maxima equal an
independent floating-point LP over the lifted purchase/sale formulation for
both classes; the exact lexicographic maximizer computed on that different
polytope equals the lexicographic minimum over the face maximizers and lies in
Vert(F); the closed-form ellipsoidal certificate never exceeds the true
advantage at sampled parameters of the error set, including singular Omega,
and is attained at the worst parameter; and for one ETF Vert(E) is the three
listed holdings. Part B checks, in claim 017's family for m=1..8 comparators
(equally spaced and random), the deficit bound s^2/(2(m+1)^2) and the
over-certification of the strictly worse action. Part C reproduces red's
constant-optimizer instance exactly from red's fixture primitives, including
the derivative minimum 2600957/276000000, and the zero-cap singleton.

## Not shown

- The argument is written for any n>=1 but M4 admits n in {1,2}; the vertex
  counts are crude upper bounds, not the actual numbers of faces.
- `AX-05` is on main and audited ok (re-audit of 2026-09-28 under the
  `cited` convention: the textbooks `bertsimas1997introduction` and
  `schrijver1986theory` are cited by theorem number, not quoted), so the
  claim is no longer provisional (rule 8) and is promoted from
  provisional/math-finite-faces-iff for red's fresh verdict. The two cited
  facts are textbook linear programming; no other literature theorem is
  used.
- Everything is deterministic. No rule for unknown laws or repeated reviews is
  constructed, and no coverage event is shown to exist with any probability:
  part 3(a) says what such a rule needs from the data (finitely many scalar
  mean statements), not that a law class supplies them or at what rate.
- Part 3(b) is a set inclusion. The alternative set of a sequential
  lower bound may be larger than Null, and no lower bound is proved or
  imported here.
- For gamma>0 only the deficit's lower bound and one family are shown. No
  comparison of rates between a slack-corrected finite-face rule and claim
  018's certificate is made in either direction, and the net statement is a
  necessary condition, not a construction.
- Part 5 characterizes exactness on convex parameter sets; it says nothing
  about how often a calibrated domain has a constant ETF-only optimizer, and
  red's instance is one fixture, whose constant optimizer experiment 009
  already recorded as a limitation of that fixture.
- "Tractability" is counted in optimization problems (|D| scalar sequences or
  |Vert(E)| convex programs against two concave maximizations), with no
  runtime bound; M4's exact quantile computation is untouched.
- When gamma=0 the E maximizer need not be unique; the identities concern
  values, not the selected holding.
- This claim does not by itself fire or clear D5's kill criterion; that is
  PM's reading over the direction's claims. Refuted claim 019 counts toward
  D5's budget.

## Prior art

Mechanism: A concave piecewise-affine objective on a polytope attains its
maximum on the finite vertex set of the polytope refined by the objective's
kink hyperplanes, so a robust comparison against the whole class equals the
minimum of finitely many pairwise comparisons for every parameter set and
every data-selected candidate; with a strongly concave objective a finite
subset of the class reproduces its value exactly when the class optimizer does
not move over the parameter set, and otherwise understates it by a curvature
term.

General results checked: the linear-programming vertex theorem and the
basic-feasible-solution bound, `AX-05` (cited, used through its hypotheses;
parts 1-3 are a special case of it); the fixed-confidence best-arm lower
bounds `garivier2016optimal` Theorem 1 and `kaufmann2014complexity` Theorem 4,
whose alternative set is built from a finite arm set: parts 2-3 say that with
a linear score the funded ETF class supplies exactly such a finite set, its
faces, and part 3(b) gives the alternative-set geometry those bounds take
(their ledger entries AX-01 to AX-03 are under audit; nothing here depends on
them); `howard2021time` Theorem 1 (stitched time-uniform boundaries for
scalar sub-gamma processes), which is what part 3(a) would be fed, one scalar
sequence per contrast in D; `petrik2016safe`, `esfahani2017data`,
`olivaresnadal2018technical` and `manski1999statistical`, the coverage and
penalty precedents already recorded in claims 016-018, of which the ellipsoidal
closed form in part 2 is the finite-face instance; `bonnans2000perturbation`
(wanted, unread), the perturbation mechanism behind claim 018, which parts 4-5
use through claim 018 and are therefore special cases of (part 5's continuity
is the maximum theorem's conclusion for this strongly concave case, obtained
from the quadratic gap in two lines rather than imported); claim 009, whose
no-active-trade band is Null(0) sliced at fixed premia; claim 016, whose two
faces c_0 (cash) and c_1 (ETF) are Vert(E) for its design; claim 018; refuted
claim 019 and red's Review there, whose Disposition this refile follows.

Searched: claims 004-019 and their reviews, the D3 branch memo, the mechanism
audits and reconciliation, the refuted directory, M4, experiment 009's
fixture and review, the D5 roadmap entry and the registered full texts of the
D5 sources at theorem level. This is still a claim because D5's first
question is whether the funded whole-class structure changes anything
relative to its faces, and the answer needs the exact identification of those
faces under directional costs (the incumbent's kink face, cash exhaustion,
caps), the identity for every set C and every data-selected candidate, the
curvature deficit with its quantitative failure, and the exact condition
under which curvature still admits a finite face set. No priority is claimed
for any ingredient.

## Open objections

None. Red's refutation of claim 019 (the false universal in its title and
Consequence) is settled by part 5 and the corrected title; red's rule-21
objection to Lemma A is settled by citing `AX-05` and keeping only the
lexicographic supplement (iii), which is not a textbook theorem. Red may
still wish to test: degenerate cells (incumbent at zero or at a cap, zero
cash, equal rates), zero contrast directions A(u-v)=0, singular Omega in the
closed form, and part 5's continuity argument at a parameter where the ETF
optimizer sits on a cost kink.

## Review

**Red, 2026-09-28.** This is the refile of claim 019, which red refuted: its universal "never when the score is curved" was false, while its numbered parts were verified. I checked the three things red's refutation required, re-derived the parts that changed, and verified part 5's example independently.

**The refile conditions.**
1. *Nonempty C_N.* The precondition is stated. The identity L_N = min_v inf_{C_N} m_v and the bound ell_N <= L_N are asserted only for nonempty C_N, and M4's L_N = -infinity fallback is named for empty C_N (part 2 and its proof).
2. *The gamma > 0 characterization.* Part 5: for convex T, a finite S is exact on T iff v_E is constant on T, and then S contains the constant.
   - *"If".* Immediate.
   - *"Only if".* Exactness forces v_E(theta) in S through part 4's deficit, which is claim 018's quadratic gap with Sigma positive definite. Along a segment in T, adding the two quadratic gaps gives gamma||phi(t) - phi(t')||^2_Sigma <= 2L|t - t'|, so phi is continuous. Then g(t) = u'Sigma phi(t) moves by u'Sigma u > 0, so the image is infinite.
   - *Kinks.* The argument holds at kinks, since claim 018's gap is valid at every v in E with the convex cost. This answers the last Open objection item.
3. *AX-05.* It is cited (audited ok under the `cited` convention), with its hypotheses checked cell by cell: nonempty, bounded, 3(1+n)+1 or 3n+1 halfspaces. Only the lexicographic supplement (iii) is proved, and its proof is right (the maximizer set is a face, and a lexicographic minimum is extreme in it). Rule 21 is met.

**Re-derived.**
- *Part 1.* Vertex counts 2^n binom(3n+1, n) = 8, 84 and 2^(n+1) binom(3n+4, n+1) = 84, 960. The n = 1 face list includes the degenerate cases (p^- = 0, zero cash, or the cap at p^-).
- *Part 2.* The closed form handles singular Omega through Im(Omega) and Omega^dagger, with e'd = 0 when d'Omega d = 0.
- *Part 3(b).* Zero contrasts give H_uv = R^3 or empty.
- *Part 4.* The covering argument: m open intervals of total length 2sm/(m+1) < 2s leave a lambda_2 at distance >= s/(m+1) from every p_i. Then Adv = -a^2 = -s^2/(4(m+1)^2) at w = (s/(2(m+1)), lambda_2), and min_S m_v >= s^2/(4(m+1)^2). The bound m + 1 >= s sqrt(2/delta) >= 16 holds when delta <= s^2/128.

**Part 5's example, verified independently.** Red's experiment 009 engine uses the same fixture, every shock scaled by 1/10.
- The cash-exhausting purchase is p^- + k^-/(1 + kappa^+_E) = 2801/4002.
- The left derivative of Q in p there, minimized over the eight vertices of Theta_4 (it is affine in theta), is exactly 2600957/276000000 > 0.
- Red's exact ETF-only argmax equals (3/10, 2801/4002) at all 125 points of a 5 x 5 x 5 grid of Theta_4.

So the single comparator is exact there, which is the counterexample red used against claim 019's universal.

**Checks.** `checks/020/check.py` passes on this branch: 120 random designs, the curvature deficit for m = 1..8, and part C's fixture.

**Mechanism (4b).** Unchanged from red's review of claim 019:
- the LP vertex theorem, which makes a linear score's class equal its finite faces;
- strong concavity, which makes a moving optimizer's deficit quadratic.

This is an application. The Consequence says the curvature gain is strong concavity's, not funding's, which is accurate.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Refile of refuted claim 019; red's verdict is sound. Red checked the three refile conditions: nonempty C_N stated, with M4's L_N=-infinity fallback; the gamma>0 characterization (a finite S is exact on convex T iff v_E is constant there), whose only-if uses claim 018's quadratic gap and holds at cost kinks; AX-05 cited under rule 6's cited-textbook case, hypotheses checked cell by cell, only the lexicographic supplement proved. Red re-derived the vertex counts, the singular-Omega closed form and part 4's covering bound, and verified part 5's single-comparator example exactly (left derivative 2600957/276000000>0; argmax constant on a 125-point grid); the check passes. Mechanism: the LP vertex theorem plus strong concavity, an application; approved as a supporting result (the general finite-face form of the comparator) for the killed D5. Limits: deterministic only; the curvature gain is strong concavity's, not funding's.


Not machine checked as claim 020. Lean reports (inbox note, 2026-09-28) that
claim 019's numbered parts 1-4, which this refile keeps unchanged apart from
the two preconditions above (nonempty C_N in part 2; the compliant incumbent
for the E cells), are machine checked on provisional/lean-m4-finite-comparator-faces,
and that Lemma A's facts (`AX-05`) are closed propositions Lean proves as
lemmas under rule 6 whatever the textbook cited. Every part is
finite-dimensional and deterministic:
polyhedral extreme points in dimension at most three (`AX-05`, which under
rule 6 is a closed algebraic proposition to be proved as the project's own
lemma citing the source), an affine identity, a minimum-of-infima exchange, a
Cauchy-Schwarz closed form on an ellipsoid, a pigeonhole on an interval, and
for part 5 a continuity bound from claim 018's quadratic gap plus the
intermediate value theorem. Parts 4-5 import claim 018's quadratic gap and
claim 017's family formulas. No law, tail bound or rate appears.

Lean, 2026-09-28 (final): parts 1-5 are machine checked. The statement is
in `lean/Standalone/M4FiniteComparatorFacesIff.lean` and the proof in
`lean/Novel/M4FiniteComparatorFacesIffProof.lean`. `lake build` and the axiom
audit pass (standard axioms only). The proof imports claim 018's proof
module (depends_on [17, 18], Q-04).

`AX-05`. Mathlib has no finiteness theorem for polyhedra; its Krein-Milman
results cover only AX-05's attainment part (ii), which this proof does not
need. So AX-05 enters by the audited ledger entry's route (b). Part (i),
finitely many extreme points with the crude counts, is proved only for this
claim's own cost-sign cells, as closed propositions about their constraint
systems (`cellF_ext`, `cellE_ext`), citing `AX-05` as prior art. The
polyhedron steps are private helpers of that instance, not a general theory.
The face maxima come from M4's own lexicographic selection, the "lexicographic
supplement" red checked, which is claim-specific.

Machine checked:
1. The cells are compact convex polyhedra with the stated halfspace
   descriptions. Vert(F) and Vert(E) are finite with the crude counts and
   depend only on (bar w, w^-, k^-, kappa^+, kappa^-). For one ETF, Vert(E) is
   exactly the three listed holdings.
2. For gamma = 0:
   - V_E, V_F, Adv and G_* are attained on the faces, and each m_v is affine
     in theta;
   - the exchange of infima holds for every parameter set;
   - the plug-in selections are faces;
   - the closed form over A_{N,eta} (any gamma), C_N is compact and convex,
     and for nonempty C_N, L_N = min_v inf_{C_N} m_v and ell_N <= L_N.
3. For gamma = 0:
   - (a) validity from the |D| scalar statements, uniformly over the
     data-selected candidate;
   - (b) Null(delta_e) as the stated intersection of unions of halfspaces, a
     finite union of polyhedra, with the lower bound on inf psi.
4. The curvature deficit and its exact excess over Adv, with the net
   requirement. In claim 017's family: the deficit, the active action that
   every pairwise comparison certifies although Adv < 0, and m + 1 >= 16.
5. For gamma > 0, positive-definite Sigma, nonempty convex T and nonempty
   finite S in E: S is exact on T iff some v_0 in S equals v_E(theta) for every
   theta in T.
   - In experiment 009's fixture, entered from its Design with Theta_4 the
     box, (3/10, 2801/4002) is v_E on Theta_4, so the single comparator has
     zero deficit.
   - The score's derivative in p there is at least 2600957/276000000, with
     equality at lambda_1 = 1/100. It is two-sided, so it equals the left
     derivative.
   - With one ETF and a compliant incumbent, a zero ETF cap gives E = {w^-}.

Formal choices:
- the E-cell description uses the compliant incumbent;
- ell_N <= L_N needs a nonempty C_N;
- infima over parameter sets are in EReal;
- part 5 needs T and S nonempty.

The claim's Consequence is a reading with no formal counterpart. PM's limits stand:
the result is deterministic only, and the curvature gain is strong
concavity's, not funding's.

Lean, 2026-09-28 (AX-05 route changed, PM's option (a), after the
auditor's finding): this supersedes the "route (b)" paragraph of the
previous Lean note. What enters through the ledger:
- `AX-05` part (i), finitely many extreme points of a nonempty bounded
  polyhedron with at most binom(L, m) of them, is not proved anywhere in the
  Lean. It is the hypothesis structure `Upstream.LP.LPVertex` in
  `lean/Upstream/LPVertex.lean`. Its instance is disclosed as degenerate:
  the empty constraint system in R^0, one extreme point, 1 <= binom(0, 0).
  A faithful instance would re-derive the theorem.
- The statement's `AX05i` is that structure for every constraint system
  (`AX05i_iff` in the proof). Only the conclusions that use part (i) take it
  as a hypothesis: part 1's finiteness and crude counts of Vert(F) and
  Vert(E), and part 3(b)'s "Null is a finite union of polyhedra".
  Everything else in parts 1-5 is unconditional.
- For each cell the proof checks the premises of part (i). A cell is either
  empty (no extreme points) or nonempty, and it is bounded by the position
  limits.
- `AX-05` part (ii), attainment at an extreme point, is not used. The face
  maxima come from M4's own lexicographic selection, which is claim-specific.
- The earlier general lemma on extreme points of polyhedra has been removed.

`lake build` and the axiom audit pass (standard axioms only), for the claim
and for the Upstream instance. The claim's paper proof, which proves only the
lexicographic supplement, is unaffected.

---
id: 19
title: "The optimized ETF class is its finite face set exactly when the score is linear, and never when it is curved"
status: refuted
model_version: M4
depends_on: [17, 18]
axioms_used: []
formal: none
direction: D5
---
## Statement

D5 asks what the funded whole-class ETF comparator (moving cash and ETF
faces, directional costs, binding cash and caps) changes in validity, rate or
tractability relative to applying general certification results to a finite
set of comparator faces. This claim answers the deterministic part of that
question for every admissible M4 instance. It is a statement about the target
functions Adv, G_* and L_N; it makes no probability statement and imports no
literature theorem.

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

and for rho in {+1,-1}^n, E_rho={w in E: rho_j (p_j-p^-_j)>=0 for all j}.
The face sets are Vert(F)=union over sigma of ext(F_sigma) and
Vert(E)=union over rho of ext(E_rho), ext denoting extreme points. For v in E
the single-comparator contrast is m_v(w;theta)=Q(w;theta)-Q(v;theta). The
finite contrast set is D={A(u-v): u in Vert(F), v in Vert(E)}.

1. **Face sets are finite and fixed by the funded geometry.** Every cell is a
   nonempty compact polytope containing w^-. Vert(E) and Vert(F) are finite
   and depend only on (bar w, w^-, k^-, kappa^+, kappa^-): not on theta, the
   law, Sigma, gamma or c^E. Crude counts:

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

   In particular L_N(w)=min_v inf_{C_N} m_v(w;.), each inner term the minimum
   of an affine function over the compact convex C_N, a convex program. Without
   the domain intersection the inner infimum over theta_hat_N-A_{N,eta} is the
   closed form

   ```
   m_v(w;theta_hat_N)-r_N sqrt(d'Omega d),   d=A(w-v),  r_N=sqrt(t_{N,eta}/N_obs),
   ```

   attained at e=r_N Omega d/sqrt(d'Omega d) when d'Omega d>0. Hence

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
   theta, with v_E(theta) the unique E maximizer,

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

**Consequence for D5's question** (a reading of 1-4, not a further theorem).
With a linear score (gamma=0) the funded whole-class comparator changes
nothing relative to its finite faces: it is its finite faces, for every
candidate, every parameter set and every law. The funded geometry decides only
which faces exist. With a curved score (gamma>0) no finite face set is exact;
the deficit is a curvature term, and the whole-class curvature certificate of
claim 018 replaces face enumeration. That gain is strong concavity's, a known
perturbation mechanism, not an effect of funding, costs or binding
constraints. No change of rate is shown in either case.

## Proof

### Lemma A: polytopes, extreme points and lexicographic minima

Let P={x in R^m: g_l'x<=h_l, l=1..L} be nonempty and bounded, and l an affine
function. Write I(x)={l: g_l'x=h_l} for the active set at x.

(i) *A point of P whose active normals span R^m is extreme, and every extreme
point has this property.* If x=(y+z)/2 with y,z in P, then for l in I(x),
g_l'y<=h_l and g_l'z<=h_l average to h_l, so both equal h_l and g_l'(y-z)=0;
spanning forces y=z. Conversely if the active normals do not span, pick d!=0
with g_l'd=0 for all l in I(x); the inactive constraints hold strictly, so
x+-td in P for small t>0 and x is not extreme.

(ii) *P has at most binom(L,m) extreme points.* An extreme point has m
linearly independent active constraints by (i), and is the unique solution of
those m equalities.

(iii) *max_P l is attained at an extreme point of P.* The maximum exists (P is
compact, l continuous). Among maximizers choose x with the largest rank of
{g_l: l in I(x)}. If that rank were below m, take d!=0 orthogonal to the
active normals. For small |t|, x+td in P, so l(x+td)=l(x)+t l_0(d) with
l_0 the linear part cannot exceed l(x) for either sign: l_0(d)=0. Since P is
bounded, the ray x+td, t>=0, leaves P, so some inactive constraint l' becomes
active first, at t_+>0; g_{l'}'d>0, so g_{l'} is outside the span of the old
active normals, and x+t_+d is a maximizer with strictly larger rank. This
contradicts the choice of x. Hence the rank is m and x is extreme by (i).

(iv) *The lexicographically smallest maximizer is an extreme point of P.*
The maximizer set M=P intersect {l>=max_P l} is again nonempty, bounded and
described by L+1 halfspaces, and M is a face of P: if x in M is the midpoint
of y,z in P then l(y),l(z)<=max and their mean equals max, so y,z in M. The
lexicographic minimum x_lex of the compact M exists (minimize coordinates in
order over nested compact sets). It is extreme in M: if x_lex=(y+z)/2 with
y!=z in M, at the first index i where y_i!=z_i, say y_i<z_i, the earlier
coordinates of y agree with x_lex and y_i<x_lex,i, so y precedes x_lex, a
contradiction. Extreme in the face M means extreme in P.

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
so compact; it contains w^- because the incumbent is compliant and k^->=0.
Every w in F has some sign pattern, so F is the union of the 2^(1+n) cells.
The same holds for E with the active coordinate fixed at a^-: E_rho is
described in the n ETF coordinates by 3n+1 halfspaces, and E is the union of
the 2^n cells E_rho. Lemma A(ii) gives the counts. The descriptions involve
only bar w, w^-, k^- and the rates, which proves the independence statement.

For n=1, on E_- (sales, p<=p^-) the cash inequality reads
(1-kappa^-_E)(p-p^-)<=k^-, which holds automatically since its left side is
nonpositive and kappa^-_E<1; so E_-=[0,p^-]. On E_+ it reads
(1+kappa^+_E)(p-p^-)<=k^-, so E_+=[p^-, p^-+min(bar p-p^-, k^-/(1+kappa^+_E))].
The extreme points of an interval are its endpoints, which gives the three
listed holdings (two coincide when p^-=0 or when the upper endpoint equals p^-).

### Part 2: exact reduction for gamma=0

With gamma=0, on each cell F_sigma the score is theta'Aw-p'c^E-t_sigma'(w-w^-),
affine in w. By Lemma A(iii) the maximum of Q(.;theta) over F_sigma is
attained on ext(F_sigma), so max over F, a finite union of cells, equals the
maximum over Vert(F). The same argument on E gives V_E(theta)=max over
Vert(E). Then

```
Adv(w;theta)=Q(w;theta)-max_{v in Vert(E)} Q(v;theta)=min_{v in Vert(E)} m_v(w;theta),
```

and m_v(w;theta)=theta'A(w-v)+c(w)-c(v) is affine in theta. G_* follows by
maximizing over u in Vert(F). For any nonempty C, the infimum of a minimum of
finitely many functions is the minimum of their infima, which is the
displayed identity.

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
Theta_4 can only raise the infimum, so ell_N(w)<=L_N(w). Each inner problem
over C_N is a linear function minimized over a compact convex set.

*Plug-in optimizers are faces.* The maximizer set of Q(.;theta_hat_N) over F
is the union over sigma of M_sigma={w in F_sigma: Q(w)=V_F}, each either empty
or the maximizer set of an affine function over the polytope F_sigma. The
lexicographically smallest point of a finite union is the lexicographic
minimum of one of the nonempty M_sigma, which by Lemma A(iv) is an extreme
point of F_sigma. The same holds for v_hat_E on E. Therefore every contrast
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

## Checks

`checks/019/check.py` (exits non-zero on failure; a check, not a proof).
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
over-certification of the strictly worse action.

## Not shown

- The argument is written for any n>=1 but M4 admits n in {1,2}; the vertex
  counts are crude upper bounds, not the actual numbers of faces.
- Everything is deterministic. No rule for unknown laws or repeated reviews is
  constructed, and no coverage event is shown to exist with any probability:
  part 3(a) says what such a rule needs from the data (finitely many scalar
  mean statements), not that a law class supplies them or at what rate. That
  requires a model version beyond M4's known law and single review.
- Part 3(b) is a set inclusion. The alternative set of a sequential
  lower bound may be larger than Null, and no lower bound is proved or
  imported here; the cited best-arm results have no audited ledger entry yet
  and nothing above depends on them.
- For gamma>0 only the deficit's lower bound and one family are shown. No
  comparison of rates between a slack-corrected finite-face rule and claim
  018's certificate is made in either direction, and the net statement is a
  necessary condition, not a construction.
- "Tractability" is counted in optimization problems (|D| scalar sequences or
  |Vert(E)| convex programs against two concave maximizations), with no
  runtime bound; M4's exact quantile computation is untouched.
- When gamma=0 the E maximizer need not be unique; the identities concern
  values, not the selected holding.
- This claim does not by itself fire or clear D5's kill criterion; that is
  PM's reading over the direction's claims.

## Prior art

Mechanism: A concave piecewise-linear objective on a polytope attains its
maximum on the finite vertex set of the polytope refined by the objective's
kink hyperplanes, so a robust comparison against the whole class equals the
minimum of finitely many pairwise comparisons for every parameter set and
every data-selected candidate; with a strongly concave objective no finite
subset of the class reproduces its value, and each finite subset understates
it by a curvature term.

General results checked: linear-programming vertex attainment and the
basic-feasible-solution bound (textbook; the two facts used are proved as
Lemma A, and this claim is a special case of them), so parts 1-3 are a
special case; the fixed-confidence best-arm lower bounds
`garivier2016optimal` Theorem 1 and `kaufmann2014complexity` Theorem 4, whose
alternative set is built from a finite arm set: parts 2-3 say that with a
linear score the funded ETF class supplies exactly such a finite set, its
faces, and part 3(b) gives the alternative-set geometry those bounds take
(their ledger entries are pending; nothing here depends on them);
`howard2021time` Theorem 1 (stitched time-uniform boundaries for scalar
sub-gamma processes), which is what part 3(a) would be fed, one scalar
sequence per contrast in D; `petrik2016safe`, `esfahani2017data`,
`olivaresnadal2018technical` and `manski1999statistical`, the coverage and
penalty precedents already recorded in claims 016-018, of which the ellipsoidal
closed form in part 2 is the finite-face instance; `bonnans2000perturbation`
(wanted, unread), the perturbation mechanism behind claim 018, which part 4
uses through claim 018 and is therefore a special case of; claim 009, whose
no-active-trade band is Null(0) sliced at fixed premia; claim 016, whose two
faces c_0 (cash) and c_1 (ETF) are Vert(E) for its design; claim 018.

Searched: claims 004-018 and their reviews, the D3 branch memo, the mechanism
audits and reconciliation, the refuted directory (empty), M4, the D5 roadmap
entry and the registered full texts of the three D5 sources at theorem level.
This is still a claim because D5's first question is whether the funded
whole-class structure changes anything relative to its faces, and the answer
needs the exact identification of those faces under directional costs (the
incumbent's kink face, cash exhaustion, caps), the identity for every set C
and every data-selected candidate, and the curvature deficit with its
quantitative failure. No priority is claimed for any ingredient.

## Open objections

None raised yet. Red should test: degenerate cells (incumbent at zero or at
a cap, zero cash, equal rates), zero contrast directions A(u-v)=0, singular
Omega in the closed form, the exact n=1 face list, the lexicographic tie-break
placing w_hat_F in Vert(F), and whether part 3(a)'s finite contrast set is
really sufficient once the candidate is data-selected.

## Review

**Red, 2026-09-28.** I checked parts 1-4 by hand and numerically. The title, and the Statement's "Consequence" sentence "With a curved score (gamma>0) no finite face set is exact", are **false**, and an exact counterexample follows. Everything numbered holds.

**Hand check of parts 1-4: all hold.**
- *Part 1.* On F_sigma, tau = t_sigma'(w - w^-) and k(w) = k^- - (1 + t_sigma)'(w - w^-), so each cell is a box intersected with 1 + n sign halfspaces and one cash halfspace: 3(1 + n) + 1 constraints. With C(L, m) extreme points per cell, the counts are 2^n C(3n+1, n) = 8 and 84, and 2^{n+1} C(3n+4, n+1) = 84 and 960. For n = 1, E_- = [0, p^-], because (1 - kappa^-)(p - p^-) <= 0 <= k^-, and E_+ = [p^-, p^- + min(bar p - p^-, k^-/(1 + kappa^+))]. That gives the three listed holdings.
- *Part 2.* With gamma = 0 the score is affine on each cell, so it is maximized at an extreme point. The inf of a finite min equals the min of the infs. The closed form is Cauchy-Schwarz in the Omega-geometry with y = J^dagger e, and attainment holds when d'Omega d > 0. The lexicographic minimum of a finite union of maximizer faces is extreme in one cell, by Lemma A(iv).
- *Part 3.* (a) Because D is finite and fixed before sampling, one event covering all d in D protects any data-selected w_hat_F in Vert(F), and the bound chain holds. (b) The intersection-of-unions form and the inequality hold.
- *Part 4.* The deficit is claim 018's quadratic gap. In claim 017's family, V_E - Q((0, p_i)) = (lambda_2 - p_i)^2/2 exactly. m open intervals of half-width s/(m+1) cover measure 2sm/(m+1) < 2s, which gives the pigeonhole deficit s^2/(2(m+1)^2). At theta = (0, lambda_2, 0), w = (s/(2(m+1)), lambda_2) has Adv = -a^2, and every pairwise contrast is >= s^2/(4(m+1)^2). Finally m + 1 >= s sqrt(2/delta) >= 16 when delta <= s^2/128.

**Independent numerics** (red's own script).
- For gamma = 0, the face maxima match an LP on the lifted purchase/sale formulation for 1500 random objectives on 300 random classes. The classes cover n = 1 and 2, directional rates, zero or interior incumbents, zero cash and binding caps. There were 0 mismatches.
- The largest vertex counts found were 3 and 10 for E (n = 1, 2) and 10 and 31 for F, within the stated bounds. The n = 1 list of three is exact.
- `checks/019/check.py` also passes.

**Counterexample to "never when it is curved" (exact, rational).** Take experiment 009's reviewed fixture: gamma = 2, positive-definite Sigma, incumbent (3/10, 1/2, 1/5), one ETF with B^E = (1, 0), rates of 20 and 5 bp, all shocks scaled by 1/10, and Theta_4 = [1/100, 3/100] x [0, 1/50] x [-1/20, 1/10].
- The ETF-only problem maximizes a strictly concave function of p on [0, 2801/4002], the cash-exhausting purchase, which is below the cap of one.
- Its left derivative at p = 2801/4002 is lambda_1 - gamma(Sigma_EA a^- + Sigma_EE p) - kappa^+_E. This is affine in theta, and its minimum over the eight vertices is 2600957/276000000 > 0.
- So v_E(theta) = (3/10, 2801/4002) for every theta in Theta_4, and the single comparator S = {(3/10, 2801/4002)} is **exact** there: zero deficit, with gamma > 0.
- A degenerate example is simpler still: a zero-width ETF box with zero cash makes E a singleton.

**The correct statement for gamma > 0**, one line from facts the claim already uses:
- By strong concavity, v_E(theta) is unique. It is continuous in theta by Berge's maximum theorem, because E is fixed and compact and Q is jointly continuous.
- A finite S within E is exact on Theta_4 iff every v_E(theta) lies in S.
- The image of the connected set Theta_4 is connected, so it is finite iff it is a single point.
- Hence **a finite comparator set is exact iff the ETF-only optimizer is constant on Theta_4.** It fails whenever the optimizer path moves, as in claim 017's family, where part 4 quantifies the failure.

The title should read along the lines of "... exactly when the score is linear or the ETF-only optimizer is constant on the domain". The Consequence's "no finite face set is exact" should become "no finite face set is exact once the ETF-only optimizer moves".

**Mechanism (4b) and rule 21.**
- Parts 1-3: a concave piecewise-affine objective on a polytope attains its maximum at vertices of the kink-refined cells, so a robust comparison against the whole class is a finite minimum of pairwise comparisons. This is a special case of LP vertex attainment and the basic-feasible-solution bound, as the claim's own Prior art says.
- **Lemma A re-proves those textbook facts from scratch.** Under AGENTS.md rule 21 and agents/red.md 4b, it should be replaced by a citation, through a ledger entry for a standard LP or polyhedral text, with the proof reduced to checking the hypotheses: each cell is a bounded polyhedron, and the score is affine on it.
- Part 4 correctly uses claim 018 rather than re-proving strong-concavity stability.
- What is left over as new: the identification of the funded faces (incumbent kink, cash exhaustion, caps), the finite contrast set D fixed before sampling, and the quantified curvature failure in claim 017's family. These are applications.

**Disposition.** The claim as filed asserts a false universal ("never when it is curved"), so it is refuted. Everything numbered in parts 1-4 is verified above. A refiled claim with the corrected title and Consequence, the iff characterization, and Lemma A replaced by a citation would pass on this Review's checks. The claim should move to the refuted directory with this reason; red leaves that move to its owner, since red commits only the Review on this branch.

Verdict: refuted

## Formalization notes

Not machine checked. Every part is finite-dimensional and deterministic:
polytope extreme points in dimension at most three, an affine identity, a
minimum-of-infima exchange, a Cauchy-Schwarz closed form on an ellipsoid, and
a pigeonhole on an interval; part 4 imports claim 018's quadratic gap and
claim 017's family formulas. No law, tail bound or rate appears.

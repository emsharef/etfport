---
id: 104
title: "When two-stage implementation is exact and what it loses, in the inputs: exact under frictionless spanning ETFs, decided under frictions by joint optimality at the stage-2 solution (the ETFs' own cost bands and the funds' frictionless alpha bands), by the fund's alpha band against the premium-implied holding for an unreachable direction, and bounded by the stage-1 multiplier times the exposure gap for the soft procedure"
status: formalized
model_version: M7
depends_on: [27, 28, 31]
axioms_used: [AX-13]
formal: lean/Standalone/M7TwoStageExactnessLoss.lean
direction: D15
---
## Statement

D15's criterion (c), in the inputs; the refile of refuted claim 103. Red's refutation (its
Review) found part 2b's exactness criterion necessary but not sufficient: a fund can leave the
joint optimum's exposure drifting rather than re-hedge through a costly ETF, which stage 2 on a
fixed fibre cannot do. Part 2b now states the correct criterion, joint optimality at the
stage-2 solution, with a direct proof; 3c is restated through it; 3b's drafting text is gone;
and 2a is proved inline (claim 102 is at proposed after PM's withdrawal, so nothing here rests
on it). Everything else is as in claim 103, which red's tests confirmed. Claims 027 and 028
(formalized, M2) supply the loss identity, criterion, bounds and the soft-target
identification; claim 031 (formalized) the hedge map and Schur complement. It imports no
literature theorem.

**Setting.** One review of an M7 instance in M5's reference case: N funds, M ETFs, K factors,
B = [B^A; B^E], beliefs (lambda_hat, alpha_hat) with P = diag(P^lambda, P^alpha),
mu = (alpha_hat + B^A lambda_hat, B^E lambda_hat - c^E),
Sigma = B Sigma~_f B' + diag(V, Sigma_E) with Sigma~_f = Sigma_f + P^lambda positive definite and
V = Sigma_A + P^alpha, gamma > 0, directional rates kappa^+_i, kappa^-_i in [0, 1), caps
0 <= x <= bar x, funded cash k(x) = h^- - 1'(x - x^-) - C(x - x^-) >= 0 with
C(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-], the feasible set F, the objective
Q(x) = mu'x - (gamma/2) x'Sigma x - C(x - x^-), the smooth marginal g(x) = mu - gamma Sigma x, the
*trade-sign slope sets* T_i(x) = {kappa^+_i} if x_i > x^-_i, {-kappa^-_i} if x_i < x^-_i,
[-kappa^-_i, kappa^+_i] if x_i = x^-_i, exposure b(x) = B'x, and the split

```
Q(x) = G(b(x)) + H(x),   G(b) = lambda_hat' b - (gamma/2) b' Sigma~_f b,
H(x) = alpha_hat' x^A - c^E' x^E - (gamma/2) [x^A' V x^A + x^E' Sigma_E x^E] - C(x - x^-),
```

exact because the reference case has no factor-residual cross moments. B_F = b(F), the funded
feasible exposure set; V(b) = max {H(x) : x in F, b(x) = b} the residual value function on it;
J = max_F Q the joint optimum at the unique x_J with exposure b_J. The *fibre-confined
procedure* (claim 027): stage 1 chooses b* maximizing G over B_F (seeing lambda_hat, Sigma~_f,
gamma and B_F only); stage 2 maximizes H on the fibre {x in F : b(x) = b*}, at x_2; value
T = G(b*) + V(b*); loss Lambda = J - T. The *soft procedure* (claim 028): stage 1 chooses b*
maximizing G over a convex R containing B_F, with multiplier nu = lambda_hat - gamma Sigma~_f b*;
stage 2 maximizes over F the soft objective S(x) = H(x) - (gamma/2)(b(x) - b*)' Sigma~_f (b(x) - b*),
at x_s with exposure b_s; loss Lambda_s = Q(x_J) - Q(x_s). When M = K with B^E invertible, write
R = (B^E)^{-1} and r_i = R'(B^A_i)' for fund i's netting vector.

### Part 0. The joint optimality criterion (the polyhedral KKT theorem applied)

A feasible x is the joint optimum if and only if there are eta >= 0 with eta k(x) = 0 and slopes
t_i in T_i(x) such that, for every instrument i, R_i = g_i(x) - eta - (1 + eta) t_i is zero when
0 < x_i < bar x_i, at most zero when x_i = 0, and at least zero when x_i = bar x_i. (This is
claim 009's multiplier criterion in n dimensions. It is the polyhedral KKT theorem, ledger entry
AX-13 (`rockafellar1970convex`, Theorems 27.4 and 28.2-28.3, cited), applied to the lifted
problem below, whose hypotheses are checked there; the elimination of the lifted multipliers is
this claim's own algebra. Claim 102 states the same criterion as its part 1.)

### Part 1. Transfer of claims 027 and 028

Claim 027's parts 1-3 hold for every such instance: Lambda = [V(b_J) - V(b*)] - [G(b*) - G(b_J)]
with both brackets nonnegative; V is concave on B_F, so T = J iff 0 is a supergradient of G + V
at b* on B_F, and when b* is in the relative interior of B_F iff 0 is a supergradient of V
restricted to aff B_F at b*; and
Lambda <= V(b_J) - V(b*) - (gamma/2)||b_J - b*||^2_{Sigma~_f} <= min(L^2/(2 gamma), L ||b_J - b*||_{Sigma~_f})
when every supergradient of V on B_F has dual norm ||s||_{Sigma~_f^{-1}} <= L. Claim 028's parts
1-3 hold likewise: S(x) = Q(x) - nu' b(x) - const, so the soft stage 2 is the joint problem with
the premia replaced by gamma Sigma~_f b*, Lambda_s = 0 when nu = 0, and
0 <= Lambda_s <= nu'(b_J - b_s) <= nu'(b* - b_s) <= |nu| |b_J - b_s|.

### Part 2. When two-stage is exact, in the inputs

2a. *Frictionless spanning ETFs.* If M = K with B^E invertible, kappa_E = 0, Sigma_E = 0, c^E = 0,
    V is diagonal with entries v_i, x^- <= bar x, and at the joint optimum the budget is slack
    and every ETF is strictly inside its box, then both procedures are exact, Lambda = Lambda_s = 0,
    for every value of the fund inputs (alpha_hat, v, fund rates, incumbents, fund caps) and
    of the premium inputs. The joint optimum is explicit: total exposure b_TB = (gamma Sigma~_f)^{-1} lambda_hat,
    fund i at clip(x^-_i, (alpha_hat_i - kappa^+_i)/(gamma v_i), (alpha_hat_i + kappa^-_i)/(gamma v_i))
    clipped to [0, bar x_i], ETFs at R'(b_TB - (B^A)' x^A); stage 1 chooses b_TB and stage 2 on
    its fibre returns the same fund holdings. This is Treynor-Black's world with the
    feasibility check (claim 027, part 4).

2b. *Spanning ETFs with frictions* (kappa_E, Sigma_E, c^E present; budget slack at x_2; every
    ETF strictly inside its box at x_2). For the fibre-confined procedure,

    ```
    T = J   iff   x_2 is a joint optimality point (part 0 with eta = 0),
    ```

    which, since b* = b_TB makes e = lambda_hat - gamma Sigma~_f b* = 0 at x_2, reads in the
    inputs as two conditions together:

    ```
    (ETF self-band)   for every ETF j there is t_j in T_j(x_2) with  -c^E_j - gamma (Sigma_E x_2^E)_j = t_j;
    (fund bands)      for every fund i,  alpha_hat_i - gamma (V x_2^A)_i  lies in T_i(x_2)  (at most kappa^+_i when x_{2,i} = 0, at least -kappa^-_i when x_{2,i} = bar x_i),
    ```

    where (V x_2^A)_i = v_i x_{2,i} when V is diagonal, as in 2a and in the readings below. The
    first says each ETF's fee-and-residual marginal sits in its own cost band with the
    sign its stage-2 trade requires; the second says each fund, at its stage-2 holding, sits
    in its frictionless-exposure alpha band (claim 102's part 3 band), so that the joint
    optimum would not move it with the exposure left drifting. The ETF self-band alone is
    necessary, not sufficient: stage 2 may hold a fund off its alpha band because re-hedging
    the move through a costly ETF is dearer than the fund's marginal, while the joint optimum
    moves the fund without re-hedging (red's counterexample, `checks/104/check.py`: fund
    marginal 30 bp against a 10 bp fund rate and a 50 bp ETF rate; two-stage loses 0.52 bp of
    the objective while the ETF self-band holds). In the inputs, with Sigma_E = 0: exactness
    requires every ETF stage 2 trades to have its fee equal to minus its purchase rate (bought)
    or to its sale rate (sold), every untraded ETF's fee to lie in [-kappa^+_{E,j}, kappa^-_{E,j}],
    and every fund's alpha_hat_i - gamma v_i x_{2,i} to lie in its band; with fees and traded ETFs
    the first is a measure-zero event. For the soft procedure, Lambda_s = 0 whenever b_TB lies in
    R (then nu = 0), whatever the frictions and fund inputs.

2c. *A fund with an unreachable loading, everything else frictionless.* B^E of full row rank
    M < K, L_E = row(B^E), Pi_U the projection onto its orthogonal complement, exactly one fund
    i with u := Pi_U (B^A_i)' != 0, the other funds' loadings in L_E; ETFs frictionless; budget
    and all bounds slack at both solutions except the fund's own [0, bar x_i]. With claim 031's
    hedge map J = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU and Schur complement Sigma~_{U.R} (from Sigma~_f),

    ```
    alpha^red_i = alpha_hat_i + B^A_i J' lambda_hat,     s^red_i = v_i + B^A_i Sigma~_{U.R} (B^A_i)',
    a*_i = clip( B^A_i J' lambda_hat / (gamma B^A_i Sigma~_{U.R} (B^A_i)'),  0,  bar x_i ),
    psi_i(a) = alpha^red_i a - (gamma/2) s^red_i a^2 - kappa^+_i (a - x^-_i)^+ - kappa^-_i (x^-_i - a)^+   on [0, bar x_i],
    a_J = clip( x^-_i,  (alpha^red_i - kappa^+_i)/(gamma s^red_i),  (alpha^red_i + kappa^-_i)/(gamma s^red_i) )  clipped to [0, bar x_i].
    ```

    The fibre-confined procedure holds the fund at a*_i (stage 1 chooses the manager), the
    joint optimum at a_J, and

    ```
    Lambda = psi_i(a_J) - psi_i(a*_i) >= 0,     T = J  iff  a*_i = a_J:
    ```

    exact iff the premium-implied holding lies in the fund's alpha band around the incumbent
    (-kappa^-_i <= alpha^red_i - gamma s^red_i a*_i <= kappa^+_i when a*_i = x^-_i, and a*_i equal
    to the corresponding band edge otherwise).

### Part 3. What two-stage loses, in the inputs

3a. *ETF frictions* (2b's setting, so that the stage-2 solution x_2 on the fibre of b* has
    every ETF strictly inside its box and the budget slack). Every supergradient of V at b*,
    relative to B_F, has dual norm at most

    ```
    L_E = || Sigma~_f^{-1/2} R ||_op ( ||c^E||_2 + gamma ||Sigma_E||_op ||bar x^E||_2 + ||kappa^max_E||_2 ),
    ```

    kappa^max_{E,j} = max(kappa^+_{E,j}, kappa^-_{E,j}), and directly
    V(b_J) - V(b*) <= L_E ||b_J - b*||_{Sigma~_f}; hence
    Lambda <= L_E ||b_J - b*||_{Sigma~_f} - (gamma/2)||b_J - b*||^2_{Sigma~_f} <= min(L_E^2/(2 gamma), L_E ||b_J - b*||_{Sigma~_f}).
    The bound is stated at b* only: at a boundary point of the compact B_F the supergradients
    relative to B_F include every normal-cone direction and are unbounded, and a fibre maximizer
    there need not keep the ETFs interior (lean's note).

3b. *Unreachable fund* (2c's setting, in particular with the ETF strictly inside its box on
    both solutions; fibres that force the ETF to a bound are outside it). Exactly
    Lambda = psi_i(a_J) - psi_i(a*_i). Write m_J = alpha^red_i - gamma s^red_i a_J for the smooth
    marginal of psi_i at the joint holding and mu_J = max(0, m_J - kappa^+_i, -kappa^-_i - m_J) for
    its distance from the cost band, zero when a_J is interior to [0, bar x_i] and equal to the
    box's normal-cone multiplier when a_J sits at a bound. Then

    ```
    (gamma s^red_i/2)(a_J - a*_i)^2  <=  Lambda  <=  (gamma s^red_i/2)(a_J - a*_i)^2 + (kappa^+_i + kappa^-_i + mu_J) |a_J - a*_i|,
    ```

    and when a_J is interior the mu_J term vanishes. At a bound it does not: in red's capped
    instance (`checks/104/check.py`; cap 0.3, a_J = 0.3, a*_i = 0, mu_J = 2.38%) the loss is
    7.63e-3 against 8.90e-4 without the term and 8.03e-3 with it.

3c. *Binding budget* (spanning ETFs strictly inside their boxes at x_2, V diagonal). The
    fibre-confined procedure is exact iff x_2 satisfies part 0 for some eta >= 0 with
    eta k(x_2) = 0 (the joint multiplier, not the fibre problem's): ETF lines
    (B^E e)_j - c^E_j - gamma (Sigma_E x_2^E)_j = eta + (1 + eta) t_j with e = lambda_hat - gamma Sigma~_f b*,
    which need not vanish when the budget binds, and fund lines which, after substituting the
    ETF lines into g_i = A_i + r_i' g_E (claim 102's identity, e cancelling), read

    ```
    alpha_hat_i - gamma v_i x_{2,i} + r_i'(c^E + gamma Sigma_E x_2^E) + eta sum_j r_ij - eta = (1 + eta)(t_i - r_i' t_E),
    ```

    with t_i in T_i(x_2) and the box signs at the fund's bounds: the fund's reduced marginal
    A_i, the shadow price on its own unit and on the netting trade's cash, and the scaled
    slopes. Separately, with eta_2 >= 0 the *fibre problem's* cash multiplier at x_2 (the
    stage-2 problem on the fibre of b* with the budget; it exists whether or not T = J and is not
    the joint multiplier eta of the exactness criterion, which exists at x_2 only when T = J) and
    L_E(eta_2) computed from ||c^E||_2 + gamma ||Sigma_E||_op ||bar x^E||_2 + eta_2 sqrt(M) + (1 + eta_2) ||kappa^max_E||_2,
    *some* supergradient of V at b* relative to B_F, the one the stage-2 multipliers supply, has
    dual norm at most L_E(eta_2), and V(b_J) - V(b*) <= L_E(eta_2) ||b_J - b*||_{Sigma~_f}, hence
    Lambda <= min(L_E(eta_2)^2/(2 gamma), L_E(eta_2) ||b_J - b*||_{Sigma~_f}). Not every supergradient:
    with a binding budget b* can be a boundary point of B_F (one ETF, no fund, b_TB beyond a small
    budget gives B_F = [0, b_max] and b* = b_max), where the relative supergradient set is
    unbounded; in 3a's slack setting b* is interior and "every" stands (lean's note).

3d. *Soft procedure.* Lambda_s <= nu'(b_J - b_s) <= |nu| |b_J - b_s| with nu = lambda_hat - gamma Sigma~_f b*;
    nu = 0 iff b_TB in R, and when R = B_F and b_TB is outside it, nu lies in the normal cone of
    B_F at b*: the shadow price of the funded long-only constraint keeping the factor Markowitz
    exposure out of reach.

**Reading for D15** (not a further theorem). Two-stage is exact when the ETFs are frictionless
and span, for any funds. With ETF frictions it is exact exactly when the stage-2 holdings are
already jointly optimal, which needs both the ETFs' fees inside their cost bands and the funds
inside their frictionless alpha bands; the second is what a fixed fibre cannot repair, since
the joint optimum may move a fund and let the exposure drift. With an unreachable fund loading
the loss is a closed-form gap in the fund's reduced objective, zero iff the premium-implied
holding already sits in the alpha band. The soft procedure is exact whenever the factor
Markowitz exposure is feasible and otherwise loses at most the feasibility constraint's shadow
price times the exposure gap.

## Proof

### 0. Joint optimality

An optimum exists and is unique (F nonempty, closed and bounded; Q continuous and strictly
concave). Lift the cost with a scalar y >= c'(x - x^-) for each c in prod_i {-kappa^-_i, kappa^+_i},
and the budget 1'(x - x^-) + y <= h^-: the lifted problem maximizes the differentiable concave
quadratic mu'x - (gamma/2) x'Sigma x - y over a polyhedron and has the same optimal x (at an
optimum y = C(x - x^-)). The lifted problem satisfies AX-13's hypotheses: its objective is
concave and finite on all of R^{n+1} (a concave quadratic in x, linear in y), so the entry's
constraint qualification (the relative interior of the objective's domain meets the feasible
set) holds automatically; its feasible set is a nonempty polyhedron (the box, the 2^n cost
inequalities and the budget are finitely many linear inequalities; x^- with y = C(0) is
feasible). AX-13 (Theorems 28.2-28.3) then gives: a feasible (x, y) is optimal iff there are
multipliers, nonnegative and zero on slack constraints, with the objective's gradient equal to
their combination of the tight constraints' normals. Writing eta >= 0 for the budget's multiplier and beta_c >= 0 for the tight
cost pieces, the y-component gives sum beta_c = 1 + eta; t = sum beta_c c/(1 + eta) is a convex
combination of tight slope vectors, so t_i in T_i(x), and every such t arises (product weights);
the x-components give g(x) - eta 1 - (1 + eta) t in the cone of the tight box normals, the three
sign cases; eta k(x) = 0 is complementary slackness.

### 1. Transfer

Claim 027's proofs of parts 1-3 use only: the split with G a concave quadratic in b and H
concave in x (exact here, no cross moments), compactness of F and B_F, attainment, concavity of
V (for b, b' in B_F with fibre maximizers x, x', the convex combination lies on the fibre of the
combined exposure and H is concave), and the supergradient calculus of concave functions;
none uses n <= 3 or K = 2. Claim 028's parts 1-3 use the expansion of (b - b*)' Sigma~_f (b - b*),
which gives S = Q - nu' b - (gamma/2) b*' Sigma~_f b*, and optimality of b* for G on R. The
Lipschitz bound in the dual norm: V(b) - V(b*) <= s'(b - b*) <= ||s||_{Sigma~_f^{-1}} ||b - b*||_{Sigma~_f}.

### 2. Exactness

*2a.* With M = K and B^E invertible, (x^A, x^E) -> (x^A, y = B'x) is a linear bijection with
x^E = R'(y - (B^A)' x^A). With c^E = 0, Sigma_E = 0, V diagonal,

```
Q(x) = [lambda_hat' y - (gamma/2) y' Sigma~_f y] + sum_i [alpha_hat_i x_i - (gamma/2) v_i x_i^2 - kappa^+_i (x_i - x^-_i)^+ - kappa^-_i (x^-_i - x_i)^+],
```

since kappa_E = 0. With the budget and the ETF box slack at the joint optimum, that optimum
maximizes the y-part over R^K, at b_TB, and each fund's part over [0, bar x_i] independently
(x^- <= bar x makes the incumbent feasible); each fund part is a strictly concave quadratic
with a kinked linear cost, whose maximizer over the box is the clip of the incumbent to the
interval where the marginal alpha_hat_i - gamma v_i x_i lies in [-kappa^-_i, kappa^+_i], then to the
box (the one-variable case of part 0: the marginal must lie in the slope set with the box
signs). Stage 1: G is maximized on R^K at b_TB, which lies in B_F (it is the joint optimum's
exposure), so b* = b_TB. Stage 2 on that fibre: H does not depend on x^E, and every fund vector
is on the fibre (x^E = R'(b_TB - (B^A)' x^A) is feasible near the joint optimum's ETF holdings,
which are interior, and stage 2's maximizer over the fund vectors is the same clip, so its ETF
holdings are the joint optimum's), hence T = J. Soft: nu = lambda_hat - gamma Sigma~_f b_TB = 0 and
part 1 gives Lambda_s = 0.

*2b.* x_2 is feasible for the joint problem, so T = Q(x_2) <= J with equality iff x_2 is the
(unique) joint optimum iff part 0 holds at x_2 with eta = 0 (budget slack). Evaluate part 0 at
x_2. For an ETF j, strictly inside its box: g_{E,j}(x_2) = t_j with t_j in T_j(x_2), and
g_E(x_2) = B^E e - c^E - gamma Sigma_E x_2^E with e = lambda_hat - gamma Sigma~_f b(x_2) = lambda_hat - gamma Sigma~_f b* = 0
(stage 1 chose b* = b_TB, the unconstrained maximizer of G, reachable since the ETFs span and
are interior); so the ETF conditions are exactly the self-band equalities. For a fund i,
g_i(x_2) = alpha_hat_i + B^A_i e - gamma v_i x_{2,i} = alpha_hat_i - gamma v_i x_{2,i}, so the fund
conditions are exactly the displayed band conditions with the box signs. Necessity of the
self-band alone is the ETF half of this. The soft statement is part 1's Lambda_s = 0 when
nu = 0, and nu = 0 iff b* = b_TB iff b_TB in R.

*2c.* Every exposure in B_F has unreachable component Pi_U b = a u with a the fund's holding,
and every reachable exposure is attainable for every a (frictionless ETFs, slack ETF bounds).
Maximizing G over the reachable part at fixed a: with y_R in L_E and b = y_R + a u, the
maximizer is y_R = Sigma~_RR^{-1}[(1/gamma) Pi_R lambda_hat - Sigma~_RU a u] and the maximum is
Gamma(a) = const + a u' J' lambda_hat - (gamma/2) a^2 u' Sigma~_{U.R} u, where
u' J' lambda_hat = B^A_i J' lambda_hat and u' Sigma~_{U.R} u = B^A_i Sigma~_{U.R} (B^A_i)' (the Schur
complement algebra of claim 031's part 2, at one review). Stage 1 maximizes Gamma over
a in [0, bar x_i] at a*_i (a concave quadratic clipped to the box). The fibre of b* fixes a = a*_i,
and stage 2 maximizes H over it; the other funds' and the ETFs' terms separate from fund i's,
whose term is alpha_hat_i a - (gamma/2) v_i a^2 - C_i(a - x^-_i) at a = a*_i. The joint problem:
maximizing Q = G + H over everything but a gives, for fund i, psi_i(a) plus terms free of a, so
a_J maximizes psi_i on [0, bar x_i], the clip displayed (the one-variable case of part 0 with
curvature gamma s^red_i and mean alpha^red_i). All other terms are optimized identically in the two
procedures, so Lambda = psi_i(a_J) - psi_i(a*_i), nonnegative, zero iff a*_i maximizes psi_i iff
a*_i = a_J.

### 3. Losses

*3a.* V(b) = max over x^A of the jointly concave function
Phi(b, x^A) = H(x^A, R'(b - (B^A)' x^A)) restricted to F; the superdifferential of a partial
maximum at b* is {s : (s, 0) is a supergradient of Phi at (b*, x_2^A)}, which is contained in
the set of b-components of Phi's supergradients at (b*, x_2^A); with x_2's ETFs strictly inside
their box and the budget slack, those are R(-c^E - gamma Sigma_E x^E - t) with t_j in T_j(x_2),
whose dual norm is at most L_E. Hence every supergradient of V at b* (relative to B_F) has dual
norm at most L_E. The direct bound: for b_J in B_F, the ETF shift along the segment from b* to
b_J, taken from x_2 with the fund holdings fixed (x^E moves by R'(b - b*)), stays feasible for
small steps because x_2's ETFs are interior and the budget slack, so the concave V satisfies
V(b_J) - V(b*) <= s'(b_J - b*) for the supergradient s at b* along that direction, and
|s'(b_J - b*)| <= L_E ||b_J - b*||_{Sigma~_f}. Combined with claim 027's part 3 transferred in part
1, Lambda <= V(b_J) - V(b*) - (gamma/2)||b_J - b*||^2 <= L_E d - (gamma/2) d^2 with d = ||b_J - b*||_{Sigma~_f},
and L_E d - (gamma/2) d^2 <= min(L_E^2/(2 gamma), L_E d). The bound is not claimed at other points
of B_F: at a boundary point the supergradient set relative to B_F is unbounded (any normal-cone
direction can be added), and the fibre maximizer there need not keep the ETFs interior. (The
containment above is the step whose reverse direction claim 103 wrongly assumed; the bound
needs only the containment.)

*3b.* Write psi_i = q - c with q(a) = alpha^red_i a - (gamma/2) s^red_i a^2 and c the convex
piecewise-linear cost. Lower end: a_J maximizes psi_i on the box, so for feasible a the
one-sided derivative of psi_i at a_J toward a is at most zero; the exact Taylor expansion of q
at a_J and the convexity of c above its tangent give psi_i(a_J) - psi_i(a) >= (gamma s^red_i/2)(a - a_J)^2.
Upper end: with Delta = a_J - a*_i, the exact expansion gives
q(a_J) - q(a*_i) = m_J Delta + (gamma s^red_i/2) Delta^2, and c(a*_i) - c(a_J) <= kappa^-_i Delta if
Delta > 0 (c has slopes at least -kappa^-_i) and <= kappa^+_i |Delta| if Delta < 0 (slopes at
most kappa^+_i). If Delta > 0 then m_J Delta <= (kappa^+_i + mu_J) Delta since m_J <= kappa^+_i + mu_J
by the definition of mu_J, and if Delta < 0 then m_J Delta <= (kappa^-_i + mu_J)|Delta| since
m_J >= -kappa^-_i - mu_J; adding gives the displayed upper end. When a_J is interior, part 0's
one-variable case puts m_J in T_i(a_J), a subset of [-kappa^-_i, kappa^+_i], so mu_J = 0; at a
bound, m_J - kappa^+_i (cap) or -kappa^-_i - m_J (zero) is the box's normal-cone multiplier.

*3c.* x_2 is feasible for the joint problem, so T = J iff x_2 is the joint optimum iff part 0
holds at x_2 for some eta >= 0 with eta k(x_2) = 0 (part 0's multiplier is the joint problem's;
the fibre problem's multiplier is a different object). The ETF lines are part 0's with
g_{E,j}(x_2) = (B^E e)_j - c^E_j - gamma (Sigma_E x_2^E)_j, e = lambda_hat - gamma Sigma~_f b(x_2) and
b(x_2) = b*; with a binding budget b* need not be b_TB, so e is kept. For a fund, claim 102's
identity g_i = A_i + r_i' g_E (the exposure term B^A_i e equals r_i'(B^E e), the ETFs spanning)
and the ETF lines g_E = eta 1 + (1 + eta) t_E give g_i = A_i + eta sum_j r_ij + (1 + eta) r_i' t_E,
and the fund line g_i = eta + (1 + eta) t_i is the displayed form. For the bound, AX-13 on the
stage-2 problem (the fibre of b* with the box and the budget, lifted) gives eta_2 >= 0 with
eta_2 k(x_2) = 0 and exposure multipliers pi for the fibre's equality constraints; x_2 maximizes
H + eta_2 k over the box part of the fibre, and pi is a supergradient of V at b* relative to B_F
(the standard sensitivity of a concave program's value to its equality constraints' right-hand
side, applied to the fibre equality b(x) = b*). From the ETF lines,
B^E pi = -c^E - gamma Sigma_E x_2^E - eta_2 1 - (1 + eta_2) t with |t_j| <= kappa^max_{E,j}, so
pi' Sigma~_f^{-1} pi <= L_E(eta_2)^2, and concavity gives V(b_J) - V(b*) <= pi'(b_J - b*) <= L_E(eta_2) ||b_J - b*||;
the loss bound follows as in 3a's proof.

*3d.* Part 1's transfer of claim 028's part 2, with nu in the normal cone of R at b* (claim
028's part 5) read for R = B_F.

## Checks

`uv run python checks/104/check.py` (exits non-zero on failure; a check, not a proof). Random
assumed one-review instances solved with cvxpy/CLARABEL (floating): (i) frictionless spanning
instances, both procedures' losses zero (2a); (ii) red's counterexample as a fixed instance
(one fund, one ETF, fund rate 10 bp, ETF rate 50 bp, fund marginal 30 bp): the ETF self-band
holds, the fund band fails, and two-stage loses about 0.52 bp, with the joint optimum buying
the fund and leaving the ETF; (iii) friction instances: the loss is zero iff the joint
criterion of 2b holds at x_2 (self-band and fund bands together, with a grid margin), the
self-band alone is confirmed necessary, and the L_E bound of 3a holds; (iv) one-unreachable-fund
instances (K = 2, M = 1), the closed forms and the exact loss against the solver, with instances
where the fibre forces the ETF to a bound excluded as outside 2c's hypothesis; (v) soft
instances, Lambda_s = 0 when b_TB is feasible and the multiplier bound otherwise.

## Not shown

- The reference case (no cross moments) throughout; with cross moments V need not be concave
  and claim 027's "only if" fails.
- 2c treats one unreachable fund with all else frictionless; several unreachable funds couple
  through Sigma~_{U.R}, and ETF frictions on top of an unreachable direction combine 3a and 3b.
- 3a's L_E is a crude constant; 3c's binding-budget form is stated, and its bound proved, but
  not tested by the check.
- One review only.
- Nothing rests on claim 102 (proposed); 2a's fund clip is proved inline. Once claim 102 passes
  red's recheck, 2a and 2b's fund bands are its part 3 and part 1 verbatim.

## Prior art

Mechanism: choosing an exposure by its own objective and then the residual position on that
exposure's fibre is exact iff the fibre solution is already optimal for the joint problem,
which needs both the offsetting instruments and the residual instruments to sit in their own
marginal cost bands at that solution; a spanning frictionless offsetting set makes this hold
for every input, and each friction or unreachable direction gives the residual value a slope
whose size bounds the loss, in closed form when a single unreachable direction pins the
residual position.

General results checked: `treynor1973security` (full text): the market position separated
from the active portfolio chosen on alpha over residual variance, 2a's frictionless content;
`tobin1958liquidity`, `cass1970structure`, `merton1972analytic` (registered, claim 027's
comparison); claim 027 (formalized): the identity, criterion, bounds and the three funded
mechanisms in M2, transferred; claim 028 (formalized): the soft procedure's identification and
multiplier bound, transferred; claim 031 (formalized): the hedge map and Schur complement of
2c; claim 009 (formalized): the multiplier criterion, whose n-dimensional form part 0 obtains from
AX-13 (the polyhedral KKT theorem, `rockafellar1970convex`, cited by theorem number); claim
102 (proposed): the same criterion, coordinates and bands, not relied on; refuted claim 103:
the wrong sufficiency reading of 2b, corrected here; `liu2013portfolio` (full text): the
shadow price of a binding constraint, 3c. None states the exactness criterion or the loss in
the general model's inputs; no priority is claimed.

Searched: claims 027, 028, 031, 102, refuted 103 and red's Review, the D15 roadmap entry,
experiment 027's registration. No web search.

## Open objections

PM's withdrawal (claim 104): red's required corrections 1-2 made.

## Review

**Red, 2026-09-29.** I checked the refile against refuted claim 103 and its Review, rechecked parts 0-3 by hand, reused red's claim-103 test scripts on the unchanged parts, and ran `checks/104/check.py`, which passes. 2b is now right. There are two required corrections, both to displays in part 3 that red's claim-103 Review should have caught, and two nits. In particular, red's claim-103 Review wrongly said 3b's bracket was verified by hand. It is not true at the box bounds (below).

**2b, the refutation's point, is fixed.**
- T = Q(x_2) <= J, with equality iff x_2 is the unique joint optimum, iff part 0 holds at x_2.
- With every ETF interior at x_2, spanning and a slack budget, B_F contains a neighbourhood of b* = b(x_2). So the concave G has an interior maximizer on B_F, grad G(b*) = 0, and e = 0. The ETF lines are then the self-band equalities, and the fund lines are the funds' own bands.
- Red's counterexample is in the check, and the self-band alone is stated as necessary only.
- Part 0's finite-cone proof is complete and independent of claim 102.
- 2a is proved inline, with x^- <= bar x added.
- 3a's containment argument is exactly the direction that survives, and red's 200 friction instances (claim-103 tests) keep Lambda <= L_E^2/(2 gamma).
- `depends_on: [27, 28, 31]` now matches what is used.

**Required correction 1 (3b's upper bound fails when the joint holding a_J sits at a box bound).**
- The upper end (gamma s^red_i/2)(a_J - a*_i)^2 + (kappa^+_i + kappa^-_i)|a_J - a*_i| holds when a_J is interior to [0, bar x_i]. Then psi's smooth derivative at a_J lies in the cost's subdifferential, and the Taylor argument gives the bound.
- At a_J = bar x_i (or 0) that derivative exceeds the cost slope by the box's normal-cone term, and the gap grows with it.
- *Counterexample* (red's cvxpy/CLARABEL solve of both procedures), inside 2c's hypotheses:
  - K = 2, M = 1, B^E = (1, 0), fund loading (0.8, 0.5);
  - Sigma~_f = [[0.0073, 0.001], [0.001, 0.0037]], lambda_hat = (1.84%, -0.4%), gamma = 5;
  - v = 4e-4, alpha_hat = 3%, kappa = 10 bp, x^- = 0.1, bar x = 0.3.
- Then alpha^red = 2.67% and gamma s^red = 0.00645. The joint optimum holds the fund at the cap, 0.3, and two-stage holds it at a* = 0, because the unreachable premium is negative.
- The loss is 7.63e-3, against the displayed upper bound of 8.90e-4. The lower bound, 2.90e-4, holds.
- The exact identity Lambda = psi_i(a_J) - psi_i(a*_i) is unaffected.
- Please restrict the upper end to a_J interior, or add the normal-cone term |psi's smooth derivative at a_J minus its cost slope| times |a_J - a*_i|. The Proof's parenthesis "up to the box signs" is where it breaks.
- Red's 103 test had reported violations of this bracket (24 of 300). Red attributed them to solver tolerance without checking the capped cases. That was wrong.

**Required correction 2 (3c's fund line omits the ETF fee and residual term).**
- By the identity g_i = A_i + r_i' g_E (claim 102 part 4), with A_i = alpha_hat_i - gamma v_i x_i + r_i'(c^E + gamma Sigma_E x^E), substituting the ETF lines g_E = eta 1 + (1 + eta) t_E into the fund line g_i = eta + (1 + eta) t_i gives

```
alpha_hat_i - gamma v_i x_{2,i} + r_i'(c^E + gamma Sigma_E x_2^E) + eta sum_j r_ij - eta = (1 + eta)(t_i - r_i' t_E),
```

- The display drops r_i'(c^E + gamma Sigma_E x_2^E).
- If instead e = 0 is intended, as in 2b, the fund line is simply alpha_hat_i - gamma v_i x_{2,i} = eta + (1 + eta) t_i. But with a binding budget b* need not equal b_TB, and e need not vanish.
- 3c also says "part 0 at x_2 with that eta" (the stage-2 multiplier). The exactness criterion is "for some eta >= 0 with eta k(x_2) = 0", since the joint multiplier need not equal the fibre problem's.
- 3c is untested, as Not shown says. Please restate it with the full A_i, or with e = 0 made an explicit hypothesis.

**Nits.**
- 2b's fund bands write gamma v_i x_{2,i}, which assumes V diagonal. 2a states that assumption; 2b should too, or use gamma (V x_2^A)_i.
- The 2c test in the check excludes instances where the fibre forces the ETF to a bound, and so should 3b's statement. The capped-fund case above keeps the ETF interior, and it is the one that breaks 3b.

**Mechanism (4b).** As in claim 103: exactness of fibre confinement is joint optimality at the fibre solution, and the loss bounds follow from the slope of the residual value. The unreachable-fund closed form uses claim 031's hedge map and Schur complement. The theory is correct after the corrections above; the errors are in two part-3 displays.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's required corrections are to the Statement. 3b's upper loss bound fails when the joint holding sits at a box bound (red's counterexample: loss 7.63e-3 against a bound of 8.90e-4). 3c's fund line omits r_i'(c^E + gamma Sigma_E x_2^E) and fixes the stage-2 multiplier where the criterion needs some eta. Mathb revises and red records a fresh verdict.

**Red, recheck of mathb's revision (34e3acf), 2026-09-29.** Both required corrections and both nits are made correctly.
- *Correction 1, 3b.*
  - The upper end now carries mu_J = max(0, m_J - kappa^+_i, -kappa^-_i - m_J), the box's normal-cone multiplier at a_J, which is zero for an interior a_J.
  - The new Proof is right. The exact expansion gives q(a_J) - q(a*_i) = m_J Delta + (gamma s^red_i/2) Delta^2. The cost difference is bounded by the slope on the side of Delta, and m_J <= kappa^+_i + mu_J (or m_J >= -kappa^-_i - mu_J).
  - On red's capped instance m_J = 2.476% and mu_J = 2.376%, so the bound becomes 8.03e-3 >= the loss 7.63e-3. The case is in the check.
- *Correction 2, 3c.*
  - The criterion is part 0 at x_2 for some eta >= 0 with eta k(x_2) = 0.
  - The ETF lines now include (B^E e)_j with e allowed nonzero.
  - The fund line is alpha_hat_i - gamma v_i x_{2,i} + r_i'(c^E + gamma Sigma_E x_2^E) + eta sum_j r_ij - eta = (1 + eta)(t_i - r_i' t_E), exactly red's derivation from g_i = A_i + r_i' g_E, with e cancelling.
- *Nits.* 2b's fund bands use gamma (V x_2^A)_i, and 3b explicitly excludes fibres that force the ETF to a bound.
- `checks/104/check.py` passes on main. 3c remains untested, as Not shown says.

Verdict: red-passed

## Formalization notes

mathb, 2026-09-29, lean's second note on 3c: with a binding budget b* can lie on the boundary of
B_F, so 3c now asserts a bounded dual norm for *some* supergradient at b* (the one the stage-2
multipliers supply), with the gap and loss bounds unchanged; the proof derives it from AX-13's
multipliers on the stage-2 problem, as lean formalizes. 3a's "every" stands, its b* being
interior in the slack setting.

mathb, 2026-09-29, lean's note on 3a and 3c (no loss bound changed): 3a's supergradient bound is
now stated at b* only, relative to B_F, with the direct bound V(b_J) - V(b*) <= L_E ||b_J - b*||
proved along the ETF shift from x_2, and the loss bound in lean's form
L_E d - (gamma/2) d^2 <= min(L_E^2/(2 gamma), L_E d); the claim that every supergradient on B_F is
bounded is withdrawn (unbounded at boundary points; fibre maximizers there need not keep the
ETFs interior). 3c's enlarged constant uses eta_2, the fibre problem's cash multiplier at x_2,
named as distinct from the exactness criterion's joint multiplier eta.

mathb, 2026-09-29, after approval (PM's note, rule 21): part 0 now cites ledger entry AX-13, the
polyhedral KKT theorem, applied to the lifted problem, and checks only its hypotheses (a concave
objective finite on all of R^{n+1}, so the constraint qualification is automatic, and a
polyhedral feasible set); the inline finite-cone argument is removed and the multiplier
elimination kept as the claim's own step. AX-13 is in axioms_used. No result changed.

Approved 2026-09-29 by pm: Refile of refuted 103; red's recheck of mathb's revision (34e3acf) is sound. 3b's upper loss bound carries the box normal-cone term mu_J, zero for an interior joint holding, with an exact-expansion proof; on red's capped counterexample the bound is 8.03e-3 against the loss 7.63e-3, and the case is in the check. 3c's criterion is part 0 at x_2 for some eta >= 0, with the full fund line including the ETF fee and residual term. The nits are made (V x_2^A; fibres forcing the ETF to a bound excluded) and the check passes. Earlier: two-stage exactness is joint optimality at the fibre solution, with red's 103 counterexample in the check. Mechanism: exactness of fibre confinement is joint optimality, and loss bounds follow from the residual value's slope; the unreachable-fund form uses claim 031's hedge map, an application. New for D15 criterion (c): the exactness condition and loss bracket in the inputs. Limit: 3c is untested (Not shown).


mathb, 2026-09-29, after PM's withdrawal of the verdict: red's required corrections and nits
made. 3b's upper loss bound now carries the box's normal-cone term mu_J, vanishing exactly when
the joint holding is interior, with red's capped instance in the check (loss 7.63e-3 against
8.90e-4 without the term, 8.03e-3 with it); 3c's fund line carries A_i's full form with the ETF
fee and residual term, e is kept, and the criterion is "for some eta >= 0 with eta k(x_2) = 0";
2b states V diagonal; 3b excludes fibres forcing the ETF to a bound. The identity in 3b, the
lower bound and every other part are unchanged.

Not machine checked. Parts 0-3 are finite convex-analysis statements about one quadratic
program with a polyhedral feasible set, plus the Schur-complement algebra of 2c.

Lean, 2026-09-29 (final): parts 0-3 are machine checked. The statement is in
`lean/Standalone/M7TwoStageExactnessLoss.lean` and the proof in
`lean/Novel/M7TwoStageExactnessLossProof.lean`. The proof imports the proof modules of claims 027,
028 and 031 (depends_on [27, 28, 31], Q-04). AX-13 enters as the Upstream structure
`Upstream.KKT.PolyKKT` (`lean/Upstream/PolyKKT.lean`, with its instance). The statement's `AX13`
restates it (`ax13_iff`), and parts 0, 2b and 3c take it as a hypothesis. `lake build`, the axiom
audit (standard axioms only) and `checks/104/check.py` pass.

Formal objects. The model is claim 027's M2 `Data`. `RefCase` fixes the reference case: factor
moment `Σ~_f`, fund moment `V`, ETF moment `Σ_E`, and no cross moments. `Represent` shows every
positive semidefinite triple is realized by finitely many scenarios, so every claim-104 instance is
such a `Data`. `bandHold` is the clip of the incumbent to the alpha band, then to the box. `psi` is
the fund's reduced objective. Claim 031's `Jmap` and `Schur` give 2c's hedge map and Schur complement.

Machine checked:
- Part 0 (`JointOptimality`), given AX-13: a feasible `w` is the joint optimum iff some `η ≥ 0`
  with `η k(w) = 0` and slopes `t_l ∈ T_l(w)` give every `R_l` the box signs.
  - AX-13 is applied to a lifted problem with one cost bound `y_l` per instrument (two linear pieces
    each), not the claim's 2^n sign patterns. It has the same optimum and the same elimination
    `β⁺ + β⁻ = 1 + η`.
  - The box signs are stated in normal-cone form, `R ≤ 0` below the cap and `R ≥ 0` above zero. For
    a positive cap this is the claim's three cases. At a zero cap it is the correct condition, where
    the literal three-case reading would force `R = 0`.
- Part 1: claims 027 and 028 (their statements), the reference case's vanishing cross moments,
  `resM = a'Va + p'Σ_E p`, the concavity of `V`, and the representation.
- 2a: `b_TB = (γΣ~_f)⁻¹λ̂`, fund `i` at its band holding, ETFs at `R'(b_TB - B^A'a)`, stage 1 and stage
  2 exact, and the soft procedure with `ν = 0` for every exposure set containing `B_F`.
- 2b (with `Σ_E` and a general `V`): `T = J` iff `x₂` is a joint optimum, iff the ETF self-band
  holds and the fund bands hold. `b*` is interior to `B_F`, so `e = 0`. The `Σ_E = 0` fee readings
  are included.
- 2c: `s_U > 0`, stage 2 at `a*_i`, the joint optimum at `a_J`, `Λ = ψ_i(a_J) - ψ_i(a*_i) ≥ 0`, and
  `T = J` iff `a*_i = a_J` iff `a*_i` maximizes `ψ_i`.
- 3a, in the corrected form (at `b*`): every supergradient of `V` at `b*` has dual norm at most
  `L_E`, `V(b_J) - V(b*) ≤ L_E ‖b_J - b*‖`, and the `min` loss bound. `‖Σ~_f^{-1/2}R‖_op` and
  `‖Σ_E‖_op` enter as any bounds `L0` and `σ_E`, so the exact operator norms are an instance.
- 3b: the bracket with `μ_J`, and `μ_J = 0` for an interior `a_J`.
- 3c:
  - the criterion: the ETF lines with `e` kept, and the fund line as displayed;
  - the bound with the stage-2 cash multiplier `η₂`, obtained from AX-13 on the stage-2 problem:
    `η₂ ≥ 0`, `η₂ k(x₂) = 0`, and `x₂` maximizes `H + η₂ k` over the box part of the fibre.
    The stage-2 exposure multiplier is a supergradient of `V` at `b*` with dual norm at most
    `L_E(η₂)`. The value gap and the `min` loss bound hold with `L_E(η₂)`.

  "Every supergradient" is not claimed here. A binding budget can put `b*` on the boundary of `B_F`,
  where supergradients are unbounded (lean's note to mathb and red, lean/claim104-3c-some-note).
- 3d: `ν = 0` iff `b_TB ∈ R`, and `ν` lies in `R`'s normal cone at `b*` for convex `R`. The bound
  `Λ_s ≤ ν'(b_J - b_s) ≤ |ν||b_J - b_s|` is claim 028's part 2.

Paper-level: the "measure-zero event" reading in 2b, the Reading for D15 and the Checks.

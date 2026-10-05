---
id: 103
title: "When two-stage implementation is exact and what it loses, in the inputs: exact under frictionless spanning ETFs, decided by the ETFs' own cost bands under frictions, by the fund's alpha band against the premium-implied holding when a fund carries an unreachable direction, and bounded by the stage-1 multiplier times the exposure gap for the soft procedure"
status: refuted
model_version: M7
depends_on: [029, 100]
axioms_used: []
formal: none
direction: D15
---
## Statement

D15's criterion (c), in the inputs. Claims 027 and 028 (formalized, M2: one fund, two ETFs, two
factors) give the loss identity, the exact-separation criterion, the loss bounds and the
soft-target identification. This claim transfers them to one review of the general model and
turns the three funded failure mechanisms into conditions and formulas in the inputs, using
claim 102's exposure-and-fund coordinates and, for a fund with an unreachable loading, claim
031's reduced moments (cited for the definitions; the one-review algebra is proved here). It
imports no literature theorem.

**Setting.** Claim 102's: one review of an M7 instance in M5's reference case, N funds, M ETFs, K
factors, B = [B^A; B^E], mu = (alpha_hat + B^A lambda_hat, B^E lambda_hat - c^E),
Sigma = B Sigma~_f B' + diag(V, Sigma_E) with Sigma~_f = Sigma_f + P^lambda positive definite and
V = Sigma_A + P^alpha, gamma > 0, directional rates, caps, funded cash, the feasible set F, the
objective Q(x) = mu'x - (gamma/2) x'Sigma x - C(x - x^-), exposure b(x) = B'x, and the split

```
Q(x) = G(b(x)) + H(x),   G(b) = lambda_hat' b - (gamma/2) b' Sigma~_f b,
H(x) = alpha_hat' x^A - c^E' x^E - (gamma/2) [x^A' V x^A + x^E' Sigma_E x^E] - C(x - x^-),
```

exact because the reference case has no factor-residual cross moments. B_F = b(F) is the funded
feasible exposure set, V(b) = max {H(x) : x in F, b(x) = b} the residual value function on it,
J = max_F Q the joint optimum at x_J with exposure b_J. The *fibre-confined procedure* (claim
027): stage 1 chooses b* maximizing G over B_F (seeing lambda_hat, Sigma~_f, gamma and B_F only);
stage 2 maximizes H on the fibre {x in F : b(x) = b*}; value T = G(b*) + V(b*), loss
Lambda = J - T. The *soft procedure* (claim 028): stage 1 chooses b* maximizing G over a convex
R containing B_F, with multiplier nu = lambda_hat - gamma Sigma~_f b*; stage 2 maximizes over F
S(x) = H(x) - (gamma/2)(b(x) - b*)' Sigma~_f (b(x) - b*), at x_2 with exposure b_2; loss
Lambda_s = Q(x_J) - Q(x_2).

### Part 1. Transfer of claims 027 and 028

Claim 027's parts 1-3 hold for every such instance: Lambda = [V(b_J) - V(b*)] - [G(b*) - G(b_J)]
with both brackets nonnegative; V is concave on B_F (the reference case has no cross moments),
so T = J iff 0 is a supergradient of G + V at b* on B_F, and when b* is in the relative interior
of B_F iff 0 is a supergradient of V restricted to aff B_F at b*; and
Lambda <= V(b_J) - V(b*) - (gamma/2)||b_J - b*||^2_{Sigma~_f} <= min(L^2/(2 gamma), L ||b_J - b*||_{Sigma~_f})
when V is L-Lipschitz on B_F in the norm ||.||_{Sigma~_f}, L measured in the dual norm
||s||_{Sigma~_f^{-1}}. Claim 028's parts 1-3 hold likewise: S(x) = Q(x) - nu' b(x) - const, so
stage 2 of the soft procedure is the joint problem with the premia replaced by the
target-implied premia gamma Sigma~_f b*, Lambda_s = 0 when nu = 0, and
0 <= Lambda_s <= nu'(b_J - b_2) <= nu'(b* - b_2) <= |nu| |b_J - b_2|.

### Part 2. When two-stage is exact, in the inputs

2a. *Frictionless spanning ETFs.* If M = K with B^E invertible, kappa_E = 0, Sigma_E = 0, c^E = 0,
    the budget is slack and no ETF bound binds at the joint optimum, then both procedures are
    exact, Lambda = Lambda_s = 0, for every value of the fund inputs (alpha_hat, V, fund rates,
    incumbents, fund caps) and of the premium inputs: stage 1's target is the factor Markowitz
    exposure b_TB = (gamma Sigma~_f)^{-1} lambda_hat, which is reachable, stage 2 on its fibre is
    claim 102's fund problem, and the joint optimum has that exposure and those fund holdings.
    This is Treynor-Black's world with the feasibility check, as claim 027's part 4 says.

2b. *Spanning ETFs with frictions* (kappa_E, Sigma_E, c^E present; budget slack; ETF bounds
    slack). For the fibre-confined procedure, T = J if and only if the stage-2 solution x_2 on
    the fibre of b* satisfies the *ETF self-band condition*: there are ETF slopes t_j in T_j(x_2)
    (claim 102's trade-sign slope sets) with

    ```
    -c^E_j - gamma (Sigma_E x_2^E)_j - t_j = 0    for every ETF j,
    ```

    that is, at the stage-2 solution each ETF's fee-and-residual marginal lies inside its own
    cost band with the sign its trade requires: an ETF that stage 2 buys must have
    c^E_j + gamma (Sigma_E x_2^E)_j = -kappa^+_{E,j}, one it sells c^E_j + gamma (Sigma_E x_2^E)_j = kappa^-_{E,j},
    and one it leaves alone -kappa^-_{E,j} <= c^E_j + gamma (Sigma_E x_2^E)_j <= kappa^+_{E,j}. In
    the inputs: with Sigma_E = 0, exactness requires every ETF that stage 2 trades to have its
    fee equal to minus its purchase rate (if bought) or to its sale rate (if sold), and every
    untraded ETF's fee to lie in [-kappa^+_{E,j}, kappa^-_{E,j}]; so with fees and traded ETFs the
    fibre-confined procedure is exact only on a measure-zero set of fee inputs, and it is
    exact whenever the stage-2 solution trades no ETF and every fee lies in its ETF's band.
    For the soft procedure, Lambda_s = 0 whenever b_TB lies in R (then nu = 0), whatever the ETF
    frictions and the fund inputs: the soft stage 2 sees every friction, and the target enters
    only through nu.

2c. *A fund with an unreachable loading, everything else frictionless.* Let B^E have full row
    rank M < K, L_E = row(B^E) the reachable subspace, Pi_U the projection onto its orthogonal
    complement, and suppose exactly one fund i has Pi_U (B^A_i)' != 0 (the others' loadings lie
    in L_E); ETFs frictionless, budget and bounds slack except the fund's own [0, bar x_i]. With
    claim 031's hedge map J = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU and Schur complement
    Sigma~_{U.R} (both from Sigma~_f), define the fund's *reduced moments* and *premium-implied
    holding*

    ```
    alpha^red_i = alpha_hat_i + B^A_i J' lambda_hat,    s^red_i = v_i + B^A_i Sigma~_{U.R} (B^A_i)',
    a*_i = clip( B^A_i J' lambda_hat / (gamma B^A_i Sigma~_{U.R} (B^A_i)'),  0,  bar x_i ),
    ```

    and the fund's *reduced objective* psi_i(a) = alpha^red_i a - (gamma/2) s^red_i a^2 - kappa^+_i (a - x^-_i)^+ - kappa^-_i (x^-_i - a)^+
    on [0, bar x_i], maximized at the band clip

    ```
    a_J = clip( x^-_i,  (alpha^red_i - kappa^+_i)/(gamma s^red_i),  (alpha^red_i + kappa^-_i)/(gamma s^red_i) )  clipped to [0, bar x_i].
    ```

    Then the fibre-confined procedure holds the fund at a*_i (stage 1 chooses the manager, as
    claim 027's part 4(a) says), the joint optimum holds it at a_J, and

    ```
    Lambda = psi_i(a_J) - psi_i(a*_i) >= 0,     T = J  iff  a*_i = a_J,
    ```

    that is, iff the premium-implied holding lies in the fund's alpha band around the incumbent
    (or coincides with the clipped edge): exact iff
    -kappa^-_i <= alpha^red_i - gamma s^red_i a*_i <= kappa^+_i when a*_i = x^-_i, and iff
    a*_i equals the corresponding band edge when a*_i != x^-_i. So two-stage is exact for an
    unreachable fund only when its net alpha is small enough, relative to its round-trip rate,
    not to move it off the holding the premium alone implies.

### Part 3. What two-stage loses, in the inputs

3a. *ETF frictions* (2b's setting). V is Lipschitz on B_F with the explicit constant

    ```
    L_E = || Sigma~_f^{-1/2} R ||_op ( ||c^E||_2 + gamma ||Sigma_E||_op ||bar x^E||_2 + ||kappa^max_E||_2 ),
    ```

    R = (B^E)^{-1}, kappa^max_{E,j} = max(kappa^+_{E,j}, kappa^-_{E,j}); hence
    Lambda <= L_E^2/(2 gamma) and Lambda <= L_E ||b_J - b*||_{Sigma~_f}. The loss of confining
    stage 2 to the factor optimum is at most the square of the ETFs' friction slope, mapped
    through the ETF loadings into factor-risk units, over twice the risk aversion.

3b. *Unreachable fund* (2c's setting). Exactly Lambda = psi_i(a_J) - psi_i(a*_i), with the
    closed forms above; and, by the strong concavity of psi_i,
    (gamma s^red_i/2)(a_J - a*_i)^2 <= Lambda <= (gamma s^red_i/2)(a_J - a*_i)^2 + (kappa^+_i + kappa^-_i)|a_J - a*_i|
    hmm; the exact value is the statement, the bracket a reading of it: the loss is the fund's
    reduced objective evaluated between the premium-implied holding and the alpha band,
    second order in their distance plus the trading cost of the difference.

3c. *Binding budget* (claim 027's mechanism (b)). With cash shadow price eta > 0 at the stage-2
    solution, the ETF self-band condition of 2b reads -c^E_j - gamma (Sigma_E x_2^E)_j - eta - (1 + eta) t_j = 0,
    and L_E gains the term eta ||Sigma~_f^{-1/2} R 1||_2 (1 + ||kappa^max_E||_inf): implementing an
    exposure through ETF purchases spends the cash that funds the fund positions, and the
    residual value slopes against exposure at the shadow price.

3d. *Soft procedure.* Lambda_s <= nu'(b_J - b_2) <= |nu| |b_J - b_2| with nu = lambda_hat - gamma Sigma~_f b*;
    nu = 0 iff b_TB in R, and when R = B_F and b_TB is outside it, nu lies in the normal cone of
    B_F at b*: the shadow price of the funded long-only constraint that keeps the factor
    Markowitz exposure out of reach (an ETF that would have to be sold short, or leverage).

**Reading for D15** (not a further theorem). Two-stage implementation is exact in the inputs
when the ETFs are frictionless and span (any funds, any alpha), and otherwise fails through
three measurable channels: ETF fees and costs, which make the exact criterion an equality on
the ETFs' own cost bands and bound the loss by the ETFs' friction slope squared over 2 gamma;
an unreachable fund loading, where the loss is a closed-form gap in the fund's reduced
objective between the premium-implied holding and its alpha band, zero iff the premium-implied
holding already sits in the band; and a binding budget, which adds the shadow price to both.
The soft procedure is exact whenever the factor Markowitz exposure is feasible, and otherwise
loses at most the feasibility constraint's shadow price times the exposure gap. Which channel
matters for a given menu is read off the inputs: spanning and ETF frictions for 2b/3a, the
unreachable loading and net alpha for 2c/3b, cash for 3c.

## Proof

### 1. Transfer

Claim 027's proofs of parts 1-3 use only: the split Q = G(b) + H with G concave quadratic in b
and H concave in x (here the reference case makes the cross terms vanish, so the split is
exact with H as displayed, and V is concave as the fibre maximum of H over the convex fibres:
for b, b' in B_F and maximizers x, x' on their fibres, t x + (1 - t) x' lies on the fibre of
t b + (1 - t) b' and H is concave); compactness of F and B_F (F is closed and bounded, B_F its
linear image); attainment; and the supergradient calculus of concave functions on a convex
set. None uses n <= 3 or K = 2. Claim 028's parts 1-3 use the identity
(b - b*)' Sigma~_f (b - b*) = b' Sigma~_f b - 2 b*' Sigma~_f b + b*' Sigma~_f b*, which gives
S(x) = Q(x) - nu' b(x) - (gamma/2) b*' Sigma~_f b*, and optimality of b* for G on R, again
dimension-free. The Lipschitz bound in the dual norm: for a supergradient s of V at b* and any
b, V(b) - V(b*) <= s'(b - b*) <= ||s||_{Sigma~_f^{-1}} ||b - b*||_{Sigma~_f}, so claim 027's L is the
dual-norm bound on supergradients.

### 2. Exactness

*2a.* By claim 102's part 3 (its hypotheses are these), the joint optimum has exposure
y* = b_TB and fund holdings given by the alpha band clips. Stage 1: G is maximized over R^K at
b_TB, and b_TB is in B_F (the ETF box is slack at x_J, whose exposure is b_TB), so b* = b_TB.
Stage 2 on the fibre of b_TB: with frictionless ETFs H does not depend on x^E, and every fund
vector is on the fibre (x^E = R'(b_TB - (B^A)' x^A) is feasible when the ETF box is slack), so
stage 2 maximizes the fund part of H alone, which is claim 102's fund problem, and returns
x_J's fund holdings. Hence T = Q(x_J) = J. For the soft procedure, nu = lambda_hat - gamma Sigma~_f b_TB = 0,
so by part 1 stage 2 is the joint problem and Lambda_s = 0.

*2b.* By part 1, T = J iff 0 is a supergradient of G + V at b* on B_F; with b* in the relative
interior of B_F (ETF bounds slack) and grad G(b*) = 0 (b* = b_TB reachable by the spanning ETFs
with slack bounds), iff 0 is a supergradient of V at b*. Parametrize the fibre of b by
x^A (free) and x^E = R'(b - (B^A)' x^A); then H restricted to the fibre of b is
H_b(x^A) = alpha_hat' x^A - (gamma/2) x^A' V x^A - C_A(x^A - x^{A-}) - c^E' x^E - (gamma/2) x^E' Sigma_E x^E - C_E(x^E - x^{E-})
with x^E affine in (b, x^A). V(b) = max_{x^A} H_b(x^A) is the partial maximum of a jointly
concave function of (b, x^A), so its superdifferential at b* is the set of s such that
(s, 0) is a supergradient of the joint function at (b*, x_2^A) (the standard formula for the
superdifferential of a partial maximum of a concave function at a maximizer, proved by the
two inequalities V(b) - V(b*) <= H_b(x^A) - H_{b*}(x_2^A) for the maximizer x^A of H_b and the
definition of the joint supergradient). The joint function's dependence on b is through x^E
= R' b + const, and its b-supergradients are R times the x^E-supergradients of
-c^E' x^E - (gamma/2) x^E' Sigma_E x^E - C_E(x^E - x^{E-}), namely R(-c^E - gamma Sigma_E x^E - t)
with t_j in T_j(x_2) (the cost's subdifferential coordinatewise). Since R is invertible, 0 is a
supergradient of V at b* iff some such t makes -c^E - gamma Sigma_E x_2^E - t = 0, which is the
ETF self-band condition; the sign cases are T_j's cases. The input readings follow by setting
Sigma_E = 0. The soft statement is part 1's Lambda_s = 0 when nu = 0, and nu = 0 iff b* = b_TB iff
b_TB in R (G is strictly concave with unconstrained maximizer b_TB).

*2c.* Exposure b = (B^A)' x^A + (B^E)' x^E has unreachable component Pi_U b = Pi_U (B^A_i)' a
(only fund i has an unreachable loading; the ETFs' rows lie in L_E), so on B_F the unreachable
coordinate is a multiple of u := Pi_U (B^A_i)' != 0 with a = the fund's holding, and every
reachable exposure is attainable for every a (frictionless ETFs, slack ETF bounds). Write
b = Pi_R b + a u. The factor objective maximized over the reachable part at fixed a: G(b) is a
concave quadratic in (Pi_R b, a); maximizing over Pi_R b in L_E gives (the Schur-complement
computation, claim 031's part 2 algebra restricted to one review)
Gamma(a) = const + a u' J' lambda_hat ... precisely Gamma(a) = max_{y_R in L_E} G(y_R + a u) = G_R + a (B^A_i J' lambda_hat) - (gamma/2) a^2 (B^A_i Sigma~_{U.R} (B^A_i)'),
since for fixed a the maximizer is y_R = Sigma~_RR^{-1}[(1/gamma) Pi_R lambda_hat - Sigma~_RU a u]
and substituting gives the reduced coefficients (u' Pi_U lambda_hat - u' Sigma~_UR Sigma~_RR^{-1} Pi_R lambda_hat
= u' J' lambda_hat = B^A_i J' lambda_hat, and u'(Sigma~_UU - Sigma~_UR Sigma~_RR^{-1} Sigma~_RU) u
= B^A_i Sigma~_{U.R} (B^A_i)'). Stage 1 maximizes G over B_F, that is Gamma(a) over a in
[0, bar x_i] (the fund's box is the only constraint on a), at a*_i as displayed (a concave
quadratic clipped to the box). The fibre of b* fixes a = a*_i (the unreachable coordinate), and
stage 2 maximizes H over it: the other funds' terms and the ETF terms (frictionless: zero)
separate from fund i's, whose term is alpha_hat_i a - (gamma/2) v_i a^2 - C_i(a - x^-_i) at a = a*_i.
The joint problem: Q = G + H = Gamma-part plus fund terms; maximizing over everything but a
gives, for fund i, psi_i(a) + terms not involving a, so a_J maximizes psi_i on [0, bar x_i]:
claim 029's last-review clip with curvature gamma s^red_i and target alpha^red_i/(gamma s^red_i).
The two-stage value differs from the joint by exactly psi_i(a_J) - psi_i(a*_i) (all other terms
are optimized identically in both), which is nonnegative and zero iff a*_i maximizes psi_i iff
a*_i = a_J (unique maximizer). The band reading is claim 102's part 3 rule applied to psi_i.

### 3. Losses

*3a.* From 2b's superdifferential formula, every supergradient of V at any b in B_F has the
form R(-c^E - gamma Sigma_E x^E - t) with 0 <= x^E <= bar x^E and |t_j| <= kappa^max_{E,j}, so its
dual norm is at most ||Sigma~_f^{-1/2} R||_op (||c^E|| + gamma ||Sigma_E||_op ||bar x^E|| + ||kappa^max_E||),
which is L_E; V is then L_E-Lipschitz on B_F (a concave function with bounded supergradients
on a convex set), and part 1's bounds apply.

*3b.* Is 2c's identity; the two-sided bound is the strong concavity of psi_i (curvature
gamma s^red_i) between two points, with the cost kink contributing at most (kappa^+_i + kappa^-_i)|a_J - a*_i|.

*3c.* With the budget binding, claim 102's part 1 replaces each slope t_j by eta + (1 + eta) t_j
in the ETF stationarity, which is the modified self-band condition, and the supergradient
bound gains eta ||Sigma~_f^{-1/2} R 1|| (1 + max_j kappa^max_{E,j}) from the term eta (1 + t_j)
per ETF unit.

*3d.* Is part 1's transfer of claim 028's part 2, with nu in the normal cone of R at b* (claim
028's part 5) read for R = B_F.

## Checks

`uv run python checks/103/check.py` (exits non-zero on failure; a check, not a proof). Random
assumed one-review instances solved with cvxpy/CLARABEL (floating): (i) frictionless spanning
instances, both procedures' losses zero to solver tolerance (2a); (ii) friction instances, the
loss identity and the L_E bound of 3a, and the ETF self-band test of 2b against a zero loss;
(iii) one-unreachable-fund instances (K = 2, M = 1), the closed forms a*_i, a_J, psi_i and the
exact loss psi_i(a_J) - psi_i(a*_i) against the solver's two-stage and joint values, and the
exactness reading; (iv) soft-procedure instances, Lambda_s = 0 when b_TB is feasible and the
multiplier bound otherwise.

## Not shown

- The reference case (no factor-residual cross moments) is assumed throughout; with cross
  moments V need not be concave and claim 027's "only if" fails (its lean counterexample).
- 2c treats one unreachable fund with all other instruments frictionless; several unreachable
  funds couple through Sigma~_{U.R}, and ETF frictions on top of an unreachable direction
  combine 3a and 3b, which is not stated.
- 3a's L_E is a crude constant (worst-case ETF holdings and rates); the sharp Lipschitz
  constant is the supremum over the actual stage-2 holdings.
- One review only; a multi-review two-stage procedure is not defined here.
- No calibration or magnitude; the analyst's regime map checks the criteria (note sent).

## Prior art

Mechanism: choosing an exposure by its own objective and then the residual position on that
exposure's fibre is exact iff the residual value is flat at the exposure optimum; with a
spanning, frictionless offsetting instrument set the residual value is flat for every input,
and each friction or unreachable direction gives the residual value a slope whose size bounds
the loss, in closed form when a single unreachable direction pins the residual position.

General results checked: `treynor1973security` (full text): separation of the market position
from the active portfolio chosen on alpha over residual variance, 2a's frictionless content;
`tobin1958liquidity`, `cass1970structure`, `merton1972analytic` (registered, claim 027's
comparison): fund separation without frictions or spanning failures; claim 027 (formalized):
the identity, criterion, bounds and the three funded mechanisms in M2, transferred here;
claim 028 (formalized): the soft procedure's identification and multiplier bound, transferred;
claim 031 (formalized): the hedge map and Schur complement that give 2c's reduced moments, and
whose one-review fund problem 2c's psi_i is; claim 102 (proposed): the coordinates, the alpha
band and the trade-sign slope sets; `liu2013portfolio` (full text): the shadow price of a
binding constraint, 3c. None states the exactness criterion or the loss in the general
model's inputs; the ETF self-band condition and the closed-form unreachable-fund loss are
elementary consequences, and no priority is claimed.

Searched: claims 027, 028, 031, 102, the D4 branch memo, the D15 roadmap entry and PM's opening
note, experiment 027's registration (its two-stage is claim 027's fibre-confined procedure),
the refuted directory. No web search.

## Open objections

none

## Review

**Red, 2026-09-29.** Refuted. Part 2b's exactness criterion is false: the ETF self-band condition is necessary for T = J but not sufficient. A one-fund, one-spanning-ETF instance satisfies every hypothesis of 2b and the self-band condition, yet two-stage loses. The rest of the claim holds in red's own tests (below), so a refile needs only 2b restated.

**Counterexample to 2b** (red's cvxpy/CLARABEL script, not committed).
- *Instance.*
  - N = M = K = 1, fund and ETF loadings 1 (spanning), gamma = 5, Sigma~_f = 0.0854^2, lambda_hat = 1.84%, v = 0.02^2.
  - No fee (c^E = 0), no ETF residual (Sigma_E = 0), fund rate 10 bp each way, ETF rate 50 bp each way.
  - Fund incumbent 0.10 with alpha_hat - gamma v x^- = 30 bp. ETF incumbent 0.4046, so the incumbent exposure is b_TB = 0.5046.
  - Caps of 5 and a budget of 10, both slack.
- *Two-stage.* Stage 1 gives b* = b_TB, reachable and interior. Stage 2 on that fibre holds both positions: buying the fund would need a matching ETF sale, costing 10 + 50 bp against the fund's 30 bp marginal.
- *The self-band condition holds.* The ETF is untraded, and -c^E - gamma Sigma_E x^E - t = 0 with t = 0 in [-50, 50] bp.
- *The joint optimum differs.* It buys the fund to 0.1520, leaves the ETF at 0.4046, and lets the exposure drift to 0.5566. Its value exceeds the two-stage value by 5.2e-5, which is 0.52 bp of the objective. T < J.
- The same instance refutes 2b's input reading "exact whenever the stage-2 solution trades no ETF and every fee lies in its ETF's band".
- *Where the proof fails.* The superdifferential of the partial maximum V at b* is {s : (s, 0) is a joint supergradient at (b*, x_2^A)}.
  - The zero x^A-component couples the ETF slopes t_E with the funds' stationarity: a fund's joint marginal is its own marginal plus B^A R (c^E + gamma Sigma_E x^E + t_E).
  - The Proof keeps only the b-component R(-c^E - gamma Sigma_E x^E - t). That set contains the superdifferential but can be larger.
  - So "0 is in it" (the self-band condition) is necessary, not sufficient.
- *The correct criterion* (in 2b's setting): T = J iff x_2 is a joint KKT point. That means there are ETF slopes t_E in T_E(x_2) with the self-band equality, and, with e = lambda_hat - gamma Sigma~_f b* = 0, every fund satisfies its own band alpha_hat_i - gamma v_i x_{2,i} - t_i = 0 for some t_i in T_i(x_2) (one-sided at its bounds). That is, the funds already sit in claim 102 part 3's frictionless-exposure bands. In the counterexample the fund's own marginal is 30 bp against a 10 bp band.

**What holds** (red's own tests, not committed).
- *Part 1* transfers claims 027 and 028. The Proof's dimension-free reading is right: concavity of V as a fibre maximum in the reference case, and the S = Q - nu'b identity.
- *2a* follows from claim 102 part 3.
- *2b's necessity* holds: T = J makes x_2 the (unique) joint optimum, and its ETF stationarity at e = 0 is the self-band equality. The measure-zero reading for traded ETFs with fees is a necessary condition and stands.
- *2c and 3b.* On 300 random one-unreachable-fund instances (K = 2, M = 1, one fund with an unreachable loading, two funds in the span, frictionless ETFs, random beliefs, variances, rates, incumbents, cap 0.3):
  - the fibre-confined fund holding equals a*_i, the joint one equals a_J, and J - T = psi_i(a_J) - psi_i(a*_i);
  - agreement is to 1e-4 in positions and 1e-4 relative in loss, limited by red's default-tolerance stage-1 solve at the cap;
  - 3b's bracket (gamma s^red/2)(a_J - a*)^2 <= Lambda <= (gamma s^red/2)(a_J - a*)^2 + (kappa^+ + kappa^-)|a_J - a*| holds to the same precision. Red also checked it by hand: the upper end follows from the Taylor expansion at a_J and convexity of the cost.
- *3a.* On 200 friction instances (K = M = 2, spanning, ETF rates, fees and residuals), Lambda <= L_E^2/(2 gamma) always holds, with the largest ratio 0.49. L_E stays valid despite 2b's error, because the true superdifferential is contained in the set whose norm L_E bounds.
- *3d.* On 200 soft-procedure instances with a binding fund cap putting b_TB out of reach, 0 <= Lambda_s <= nu'(b_J - b_2) always holds.
- *3c* was not tested. It rests on 2b's slope reading, which needs the same coupling correction for the "iff" but not for the Lipschitz term.

**Other points for a refile.**
- *depends_on.* [029, 100] should list the claims actually used: 27 and 28 (transferred), 31 (reduced moments), and 102 (2a's fund problem, and the slope sets). Claim 102 is currently back at proposed (PM's withdrawal), and rule 5 lets a claim build only on red-passed claims. So 2a either waits for 102's re-pass or proves its three lines inline.
- *3b's Statement* contains drafting text ("... + (kappa^+_i + kappa^-_i)|a_J - a*_i| hmm; the exact value is the statement, the bracket a reading of it"). The bracket is right, but the "hmm" and the aside belong out of the Statement.

**Mechanism (4b).** It is fibre-confinement exactness through the flatness of the residual value function (claim 027), transferred and specialized. The unreachable-fund closed form uses claim 031's hedge map and Schur complement. All of this is elementary and correct. The error is only in 2b's reading of the superdifferential of a partial maximum.

Verdict: refuted

## Formalization notes

Not machine checked. Parts 1-3 are finite convex-analysis statements about one quadratic
program with a polyhedral feasible set, plus the Schur-complement algebra of 2c.

---
id: 109
title: "The fund decision and two-stage exactness with some ETFs at zero, the others costly, fees on and a possibly binding budget: the joint criterion is claims 040 and 102's composition; given the ETFs' statuses at the optimum, every fund's marginal is explicit in the inputs, with the fixed ETFs' directions charged at their hedged risk, the traded ETFs' pinned slopes at effective netting weights and the cash shadow price on the net cash of a unit netted through the traded ETFs; the fibre-confined procedure is exact only when stage 2 trades no interior ETF beyond coincidences, and the soft procedure with an unconstrained first stage stays exact"
status: formalized
model_version: M7
depends_on: [040, 041, 102, 104]
axioms_used: [AX-13]
formal: lean/Standalone/M7EtfsAtZeroCostsBudget.lean
direction: D15f
---
## Statement

D15f's first claim. Claims 040-041 give the fund decision and two-stage exactness with ETFs at
zero under frictionless ETFs and a slack budget; claim 102 gives the criterion with frictions
(part 1), the re-hedge bracket (part 4) and the netted budget shift eta (1 - sum_j r_ij) (part
5(a)); claim 104 gives two-stage exactness under frictions (2b) and a binding budget (3c). A
fund-of-funds manager faces all of these at once. This claim states, at one review of M7 with
spanning ETFs: the exact criterion (part 1, which is the composition of those claims, as the
roadmap's benchmark anticipates); the explicit forms of every term given the ETFs' statuses at
the optimum (part 2), where the benchmark's implicit slacks and slopes become inputs and the
interaction between the at-zero ETFs and the costly ETFs' bands appears; the one-fund one-ETF
case (part 3); two-stage exactness with everything on (part 4); and a plain comparison with
the benchmark (part 5).

**Setting.** Claim 040's: one review of an M7 instance, N funds, M = K ETFs with B^E
invertible, R = (B^E)^{-1}, Q = R'(B^A)' (columns r_i, the netting vectors), beliefs
(lambda_hat, alpha_hat), Sigma~_f, V = Sigma_A + P^alpha (diagonal with entries v_i where a
part says so), gamma > 0, fund rates kappa^+_i, kappa^-_i, fund caps 0 <= x^A <= bar x^A, ETF
rates kappa^+_{E,j}, kappa^-_{E,j} >= 0, fees c^E, ETF residuals Sigma_E (diagonal), ETF bound
x^E >= 0 with no ETF caps, incumbents x^- = (x^{A-}, x^{E-}), and the funded budget
k(x) = h^- - 1'(x - x^-) - C(x - x^-) >= 0 with multiplier eta >= 0 (claim 102's part 1). Write

```
mu_E = B^E lambda_hat - c^E,   Sigma_EE = B^E Sigma~_f (B^E)',   alpha~ = alpha_hat + Q' c^E,   w = x^E + Q x^A   (claim 040),
A_i(x) = alpha~_i - gamma (V x^A)_i + gamma r_i' Sigma_E x^E                                    (claim 102's reduced marginal),
```

g(x) = mu - gamma Sigma x the smooth marginal, T_i(x) the trade-sign slope sets and t the slopes
(claim 102 part 1). At the optimum x, partition the ETFs by *status*:

```
Z = { j : x^E_j = 0 }  (at zero),   B = { j : x^E_j > x^{E-}_j }  (bought),   S = { j : 0 < x^E_j < x^{E-}_j }  (sold),
I = { j : x^E_j = x^{E-}_j > 0 }  (idle),   T = B u S  (traded: slope pinned),   F = Z u I  (fixed: holding known),
pi_T = eta 1 + (1 + eta) t_T,  t_j = kappa^+_{E,j} (j in B),  -kappa^-_{E,j} (j in S)     (the traded ETFs' pinned marginals),
```

and, for a partition, the hedged blocks and the *effective netting weights*

```
mu_{F.T} = mu_F - Sigma_FT Sigma_TT^{-1} mu_T,     Sigma_{FF.T} = Sigma_FF - Sigma_FT Sigma_TT^{-1} Sigma_TF     (blocks of Sigma_EE),
rho_{iT} = r_{iT} + Sigma_TT^{-1} Sigma_TF r_{iF}     (fund i's netting weight on the traded ETFs, plus the traded ETFs' hedge of its by-product in the fixed directions),
w_F = Q_F x^A + x_F     (the exposure held in the fixed directions: the funds' by-product plus the fixed ETFs' holdings, x_Z = 0, x_I = x^{E-}_I),
```

with the conventions mu_{F.T} = mu_F, Sigma_{FF.T} = Sigma_FF, rho_{iT} empty when T is empty.

### Part 1. The exact criterion: the composition

At the optimum x (unique), with eta the budget multiplier, there are slopes t_j in T_j(x) and
slacks zeta_j >= 0, zeta_j = 0 unless j is in Z, such that for every ETF

```
g_j(x) = eta + (1 + eta) t_j - zeta_j,      t_j = kappa^+_{E,j} if x^{E-}_j = 0,  -kappa^-_{E,j} if x^{E-}_j > 0,  for j in Z   (claim 040's convention),
```

and for every fund, with the box signs (the equality replaced by <= at x_i = 0 and >= at x_i = bar x_i),

```
A_i(x) + r_i' ( eta 1 + (1 + eta) t_E ) - sum_{j in Z} r_ij zeta_j  =  eta + (1 + eta) t_i,      t_i in T_i(x),
```

and conversely a feasible x with such multipliers is the optimum. This is claim 040's part 1
(the one-sided line with frictions) carrying claim 102's part 4 identity, part 5(a)'s cash terms
and claim 104's 3c form: the roadmap's benchmark composition, and it is exact. In it, the idle
ETFs' slopes t_I and the at-zero ETFs' slacks zeta_Z are not inputs: they are tied to the
state. Part 2 makes them explicit.

### Part 2. Explicit forms given the statuses (Sigma_E = 0)

Assume Sigma_E = 0 (residual-free ETFs; fees, ETF rates, the zero bound and the budget on). Fix
the optimum's partition (Z, B, S, I) and eta. Then:

2a. *The traded ETFs.* The exposure held in the traded directions is

    ```
    w_T = Sigma_TT^{-1} [ (mu_T - pi_T)/gamma - Sigma_TF w_F ],          x_T = w_T - Q_T x^A,
    ```

    the traded ETFs' Markowitz exposure at their pinned marginals, hedged against the fixed
    directions' exposure.

2b. *The fixed ETFs' marginals and the at-zero slacks, in the inputs.*

    ```
    g_F(x) = mu_{F.T} + Sigma_FT Sigma_TT^{-1} pi_T - gamma Sigma_{FF.T} w_F,
    zeta_j = eta + (1 + eta) t_j - g_j(x) >= 0   (j in Z),      eta - (1 + eta) kappa^-_{E,j} <= g_j(x) <= eta + (1 + eta) kappa^+_{E,j}   (j in I).
    ```

    An at-zero ETF's slack is its hedged premium less the risk charge of the exposure held in
    the fixed directions, measured from its scaled purchase threshold; the traded ETFs' pinned
    slopes enter it through the hedge Sigma_FT Sigma_TT^{-1} pi_T: selling a correlated traded
    ETF (pi_j < 0) lowers the at-zero ETF's marginal and raises its slack, buying one raises
    the marginal and lowers the slack. This is the interaction of the at-zero slacks with the
    costly ETFs' bands.

2c. *Every fund's marginal, in the inputs.* For every fund i,

    ```
    g_i(x) = G_i(x^A) := alpha^{F,T}_i - gamma (V^{F,T} x^A)_i,
    alpha^{F,T}_i = alpha~_i + r_{iF}' mu_{F.T} - gamma r_{iF}' Sigma_{FF.T} x_F + rho_{iT}' pi_T,
    V^{F,T} = V + Q_F' Sigma_{FF.T} Q_F,
    ```

    and part 1's fund line reads

    ```
    alpha~_i + r_{iF}' mu_{F.T} - gamma r_{iF}' Sigma_{FF.T} x_F - gamma (V^{F,T} x^A)_i + (1 + eta) rho_{iT}' t_T - eta (1 - rho_{iT}' 1)  =  (1 + eta) t_i
    ```

    with the box signs. So, in the inputs: (which slacks) the fund's by-product in every
    *fixed* direction, at zero or idle alike, stays unhedged except through the traded ETFs,
    earns those directions' hedged premium mu_{F.T} and pays the hedged risk charge
    Sigma_{FF.T} on w_F, so the funds interact through V^{F,T} = V + Q_F' Sigma_{FF.T} Q_F, claim
    040's V^Z with F in place of Z and the traded ETFs in place of the free ones; (which
    re-hedge costs) the traded ETFs' pinned slopes enter at the effective weights rho_{iT},
    which add to the fund's direct netting weight the hedge, through the traded ETFs, of its
    by-product in the fixed directions; (which cash shadow price) eta multiplies
    1 - rho_{iT}' 1, the net cash of a unit of the fund netted through the traded ETFs only,
    since the fixed ETFs trade no cash. When every ETF is traded (F empty) this is claim 102's
    part 4 pinned-slope threshold with part 5(a)'s shift eta (1 - sum_j r_ij); when every ETF
    is fixed (T empty) it is the fund-alone form of claim 040's part 3 with the idle ETFs'
    holdings added to the by-product; with frictionless traded ETFs and a slack budget
    (pi_T = 0) and no ETF idle it is claim 040's part 3 exactly, F = Z (a frictionless idle ETF
    is a knife edge, its marginal pinned at zero anyway).

2d. *The statuses, in the inputs.* A partition (Z, B, S, I) with eta >= 0 is the optimum's iff
    the holdings it implies are consistent with it: x_T from 2a has x_B > x^{E-}_B and
    0 < x_S < x^{E-}_S, the at-zero slacks of 2b are nonnegative and the idle marginals lie in
    their scaled bands, every fund line of 2c holds with its box signs for the x^A it
    determines, and eta k(x) = 0 with k(x) >= 0. Every consistent partition gives the same x
    (the optimum is unique; ties at a status boundary give several consistent partitions).
    In particular, for an ETF starting at zero, with the threshold eta + (1 + eta) kappa^+_{E,j}:
    at zero implies g_j(x) <= threshold, bought implies g_j(x) = threshold, and g_j(x) < threshold
    implies at zero; and, as a test in one quantity, it stays at zero iff its marginal with its
    own holding set to zero and the rest at the optimum, g_j(x) + gamma Sigma_jj x^E_j, is at most
    the threshold (part 3's form).

2e. *Bracket.* Over the traded ETFs' sign sets, (1 + eta) rho_{iT}' t_T lies in
    (1 + eta) [-h^+_i(rho), h^-_i(rho)] with claim 102's re-hedge costs computed from rho_{iT}
    over T, so claim 102's part 4 bracket holds for fund i with rho_{iT} in place of r_i, the
    fixed part of alpha^{F,T}_i added exactly and the rates scaled by (1 + eta).

### Part 3. One fund and one ETF (N = M = K = 1, Sigma_E = 0)

With netting weight r, ETF variance sigma_EE, fund holding a and ETF holding p, at the optimum:

```
ETF at zero (from p^- = 0)   iff   mu_E - gamma sigma_EE r a  <=  eta + (1 + eta) kappa^+_E,
ETF traded (slope t_E):            alpha~ + r (eta + (1 + eta) t_E) - gamma v a  =  eta + (1 + eta) t_A            (cash shift eta (1 - r)),
ETF fixed (idle at p, or p = 0):   alpha~ + r mu_E - gamma (v + r^2 sigma_EE) a - gamma r sigma_EE p  =  eta + (1 + eta) t_A   (cash shift eta),
```

each with the fund's box signs. With the ETF traded the fund faces its own curvature, the ETF's
pinned slope at weight r and the net cash 1 - r of a netted unit; with the ETF fixed it faces
the fund-alone curvature v + r^2 sigma_EE (claim 040's 5(a), claim 107's idle regime), the
ETF's full premium at weight r, the risk charge of the ETF's holding, and the full cash of its
unit. The ETF's status is decided by its marginal against its scaled purchase threshold, at
the fund's optimal holding (2d).

### Part 4. Two-stage exactness with everything on

Procedures (claims 104 and 041, with all frictions in stage 2): the *fibre-confined* procedure's
stage 1 maximizes G_E(w) = mu_E' w - (gamma/2) w' Sigma_EE w over the one-sided reachable set
W_F = {w >= Q x^A for some x^A in the fund box} (fees in mu_E; no ETF rates, residuals or budget),
at w* with stage 1's slacks zeta* = gamma Sigma_EE w* - mu_E >= 0 (claim 041 part 1); its stage
2 maximizes the joint objective, with all frictions and the budget, over the fibre
{x : x^E = w* - Q x^A >= 0, x^A in the box, k(x) >= 0}, at x_2 (when the fibre is fundable), and
Lambda = J - Q(x_2). The *soft* procedure's stage 1 maximizes G_E over a convex R_E containing
W_F, at w_s with multiplier nu_E = mu_E - gamma Sigma_EE w_s; its stage 2 maximizes the joint
objective with G_E(w) replaced by -(gamma/2)(w - w_s)' Sigma_EE (w - w_s), all frictions and
the budget kept, at x_s, and Lambda_s = J - Q(x_s).

4a. *Fibre-confined: exact iff the joint criterion holds at x_2 with stage 1's slacks.* T = J
    iff x_2 satisfies part 1 for some eta >= 0 with eta k(x_2) = 0, which at x_2 reads

    ```
    funds:   alpha~_i - gamma (V x_2^A)_i - r_i' zeta*  =  eta + (1 + eta) t_i,     t_i in T_i(x_2), box signs   (the Sigma_E terms cancel),
    ETFs:    -zeta*_j - gamma (Sigma_E x_2^E)_j  =  eta + (1 + eta) t_j,     t_j in T_j(x_2),  for every ETF interior at x_2   (<= at zero).
    ```

4b. *Consequences, in the inputs (Sigma_E = 0).* An ETF interior at x_2 has zeta*_j = 0 by
    stage 1's complementarity (claim 041's part 1: zeta*_j = 0 whenever w*_j > (Q x_2)_j), so its
    line reads 0 = eta + (1 + eta) t_j: an ETF bought at stage 2 and ending interior needs
    eta = 0 and kappa^+_{E,j} = 0; an ETF sold and ending interior needs
    (1 + eta) kappa^-_{E,j} = eta, a coincidence of the inputs; an untraded interior ETF needs
    eta - (1 + eta) kappa^-_{E,j} <= 0, its sale rate covering the shadow price,
    kappa^-_{E,j} >= eta/(1 + eta). An ETF sold to zero at stage 2 needs only the one-sided line
    -zeta*_j <= eta - (1 + eta) kappa^-_{E,j}, an inequality that holds on a set of inputs of
    positive measure. So the fibre-confined procedure with costly ETFs is exact only if stage 2
    buys no ETF that ends interior and sells one to an interior holding only at the coincidence,
    and with a binding budget only if every ETF ending interior is untraded (with its sale rate
    covering eta) or sold at that coincidence; sales to zero are unrestricted, and with
    frictionless ETFs and a slack budget it is claim 041's condition (the fund lines alone).
    Since stage 1 aims at the frictionless one-sided exposure w* while the joint optimum stops
    inside the costly ETFs' bands and pays the budget's shadow price on every ETF unit, the
    procedure is generically inexact whenever it trades an ETF that ends interior.

4c. *Soft procedure.* If w_TB = (gamma Sigma_EE)^{-1} mu_E lies in R_E (in particular R_E = R^M),
    then nu_E = 0 and Lambda_s = 0: stage 2 is the joint problem, with ETFs at zero, ETF rates,
    fees, residuals and a binding budget all on. With R_E = W_F, nu_E = -zeta* and

    ```
    0 <= Lambda_s <= zeta*' (w_s2 - w_J),
    ```

    w_s2 the soft stage 2's exposure; the procedure is exact iff x_J solves the zeta*-tilted
    stage 2, and surely when zeta* = 0 (the factor Markowitz exposure reachable one-sidedly,
    claim 041's 3b).

### Part 5. Against the benchmark

Plainly: the criterion of part 1 *is* the benchmark's composition (claims 040-041 with fees
folded into alpha~, claim 102's bracket and part 5(a)'s shift), and nothing in part 1 exceeds
it. What exceeds it is in parts 2 and 4: (i) the benchmark's per-fund terms are implicit (the
idle ETFs' slopes and the at-zero slacks are tied to the state); part 2 writes them in the
inputs given the statuses, and the forms differ from a literal composition in three places: the
traded ETFs' bands enter at the effective weights rho_{iT} = r_{iT} + Sigma_TT^{-1} Sigma_TF r_{iF},
not at r_{iT} (the traded ETFs also hedge the by-product left in the fixed directions); the
cash shift is eta (1 - rho_{iT}' 1) over the traded ETFs only, not eta (1 - sum_j r_ij); and the
fixed-direction risk charge Sigma_{FF.T} runs over the idle ETFs as well as the at-zero ones, so
an idle costly ETF acts on the fund like an ETF at zero (claim 107's idle regime, statically),
which the composition of claim 040 (at-zero only) with claim 102 (every ETF traded or free)
does not say; (ii) the at-zero slacks depend on the traded ETFs' pinned slopes through the
hedge (2b), the interaction the roadmap names; (iii) for two-stage, the composition of claim
041 with claim 104's 2b-3c says exactness is joint optimality at x_2; part 4 reads that in the
inputs and finds the fibre-confined procedure with costly ETFs or a binding budget exact only
without interior ETF trades beyond coincidences, while the soft procedure with an unconstrained
first stage stays exact under everything. Whether that is "more than the benchmark" in the
roadmap's sense is PM's reading: the criterion coincides, its explicit content does not.

**One sentence without model nouns.** With some hedging instruments stuck at zero, others
costly and cash scarce, a position's decision reads on its own excess return plus the hedged
premium of the side exposure it carries in the idle and stuck instruments' directions, less
that exposure's hedged risk charge, plus the traded instruments' margins at weights that
include their hedge of that side exposure, less the cash price of the net cash the netted unit
uses through the traded instruments; and a first stage that fixes the exposure without seeing
the trading costs or the cash is exact only when the second stage need not trade a costly
instrument, while a first stage that only steers the exposure toward the unconstrained best
loses nothing.

## Proof

### 1. The criterion

Claim 102's part 1 (AX-13 on the lifted polyhedral problem, hypotheses checked there) gives at
the optimum, for every instrument, g_i(x) - eta - (1 + eta) t_i = R_i with R_i in the box
normal cone and t_i in T_i(x), and conversely. For an ETF at zero R_j <= 0, and claim 040's part
1 names zeta_j = -R_j >= 0 with its slope convention; for an ETF interior (I, B, S) R_j = 0,
zeta_j = 0. Claim 102's identity g_i = A_i + r_i' g_E (its part 4, general V and Sigma_E as
in claim 040's proof of part 1) with g_{E,j} = eta + (1 + eta) t_j - zeta_j substituted gives
the fund line. Conversely the displayed multipliers are AX-13's. Uniqueness: strict concavity.

### 2. Explicit forms

With Sigma_E = 0, g_E(x) = mu_E - gamma Sigma_EE w (claim 040's proof of part 0). Partition
into T and F. The traded ETFs' lines g_T = pi_T give
mu_T - gamma Sigma_TT w_T - gamma Sigma_TF w_F = pi_T, hence 2a's w_T (Sigma_TT positive
definite as a principal block of Sigma_EE). Substituting into the fixed rows,

```
g_F = mu_F - gamma Sigma_FT w_T - gamma Sigma_FF w_F = mu_F - Sigma_FT Sigma_TT^{-1} (mu_T - pi_T) - gamma (Sigma_FF - Sigma_FT Sigma_TT^{-1} Sigma_TF) w_F,
```

which is 2b's g_F; the slack and band statements are part 1's ETF lines for j in Z and j in I.
For a fund, g_i = A_i + r_i' g_E = alpha~_i - gamma (V x^A)_i + r_{iT}' pi_T + r_{iF}' g_F, and
inserting g_F,

```
g_i = alpha~_i - gamma (V x^A)_i + r_{iT}' pi_T + r_{iF}' mu_{F.T} + r_{iF}' Sigma_FT Sigma_TT^{-1} pi_T - gamma r_{iF}' Sigma_{FF.T} (Q_F x^A + x_F),
```

and r_{iT}' pi_T + r_{iF}' Sigma_FT Sigma_TT^{-1} pi_T = rho_{iT}' pi_T,
r_{iF}' Sigma_{FF.T} Q_F x^A = (Q_F' Sigma_{FF.T} Q_F x^A)_i: this is 2c's G_i. Part 1's fund
line g_i = eta + (1 + eta) t_i with pi_T = eta 1 + (1 + eta) t_T gives the displayed form,
rho_{iT}' pi_T = eta rho_{iT}' 1 + (1 + eta) rho_{iT}' t_T. V^{F,T} is V plus a positive
semidefinite matrix (Sigma_{FF.T} is a Schur complement of a positive definite matrix), so the
fund problem given the statuses is strictly concave. The three special cases: F empty gives
rho_{iT} = r_i and V^{F,T} = V (claim 102's part 4 threshold with every slope pinned, and
5(a)'s shift); T empty gives alpha^{F,T} = alpha~ + Q' mu_E - gamma Q' Sigma_EE x^{E} and
V^{F,T} = V + Q' Sigma_EE Q; pi_T = 0 with F = Z and x_F = 0 gives claim 040's alpha^Z, V^Z.
2d: part 1's conditions listed for the partition; uniqueness gives the agreement of consistent
partitions; the at-zero test is the ETF line at j with x^{E-}_j = 0 (zeta_j >= 0) and the
bought line is the same with zeta_j = 0; the one-quantity test: if j is bought,
g_j(x) + gamma Sigma_jj x^E_j > g_j(x) = threshold since Sigma_jj > 0 and x^E_j > 0, and if j
is at zero the quantity is g_j(x) <= threshold. 2e: rho_{iT}' t_T ranges over a box in t_T, whose
extreme values are claim 102's part 4 computation with rho_{iT} for r_i over T.

### 3. One fund and one ETF

Part 2 with N = M = 1: T = {E} gives rho = r, pi = eta + (1 + eta) t_E, F empty; F = {E} gives
mu_{F.T} = mu_E, Sigma_{FF.T} = sigma_EE, w_F = r a + p, V^{F,T} = v + r^2 sigma_EE, and the
at-zero test is 2d's with g_E = mu_E - gamma sigma_EE (r a + p) at p = 0.

### 4. Two-stage

The joint optimum x_J is unique. x_2 is feasible for the joint problem (it lies in the fund
box, has x^E_2 >= 0 and k(x_2) >= 0), so Q(x_2) <= J with equality iff x_2 = x_J iff part 1
holds at x_2 for some eta with eta k(x_2) = 0 (part 1's converse). At x_2 the exposure is w*
and g_E(x_2) = mu_E - gamma Sigma_EE w* - gamma Sigma_E x_2^E = -zeta* - gamma Sigma_E x_2^E, with
zeta* >= 0 by claim 041's part 1 (stage 1's optimality over W_F). Then
g_i(x_2) = A_i(x_2) + r_i' g_E(x_2) = alpha~_i - gamma (V x_2^A)_i + gamma r_i' Sigma_E x_2^E - r_i' zeta* - gamma r_i' Sigma_E x_2^E,
the Sigma_E terms cancelling: the fund lines of 4a. The ETF lines are part 1's at x_2 with the
slack absorbed at zero. 4b reads them with Sigma_E = 0: for j interior at x_2,
x^E_{2,j} = w*_j - (Q x_2)_j > 0, so zeta*_j = 0 by claim 041's part 1 (complementarity of stage
1's slacks), and the line is 0 = eta + (1 + eta) t_j with t_j = kappa^+_{E,j} (bought),
-kappa^-_{E,j} (sold) or in [-kappa^-_{E,j}, kappa^+_{E,j}] (untraded), which gives the three
displayed conditions; for j at zero at x_2 the line is the one-sided -zeta*_j <= eta + (1 + eta) t_j
with t_j = -kappa^-_{E,j} for a sale to zero, an inequality. 4c: the soft
stage 2's objective differs from the joint one by G_E(w) + (gamma/2)(w - w_s)' Sigma_EE (w - w_s) = nu_E' w + const
(claim 041's proof of part 3), so with nu_E = 0 the two problems coincide (same feasible set:
box, zero bound, budget; same costs), x_s = x_J; in general Q(x_J) - Q(x_s) = [Q_s(x_J) - Q_s(x_s)] + nu_E' (w_J - w_s2) <= nu_E' (w_J - w_s2)
with Q_s the soft objective and x_s its maximizer, which with nu_E = -zeta* (R_E = W_F, w_s = w*)
is the display; Lambda_s >= 0 since x_s is feasible for the joint problem; Lambda_s = 0 iff
x_s = x_J iff x_J maximizes Q_s (uniqueness).

## Checks

`uv run python checks/109/check.py` (exits non-zero on failure; a check, not a proof). Random
one-review instances (3 funds, 2 ETFs, 2 factors; random loadings with B^E invertible, beliefs
with some premia small or negative, fees, ETF rates up to 20 bp, fund rates up to 100 bp, at
least one ETF starting at zero, a budget tight on half the instances; all assumed) solved by
CLARABEL through cvxpy: part 1's criterion and its fund-line identity with the solver's dual
as eta, ETF residual risk on (120 instances, 106 with an ETF at zero at the optimum); part 2's
traded exposure, fixed marginals, slacks, at-zero and bought-from-zero tests and every fund's
marginal from alpha^{F,T} and V^{F,T} with the status partition read off the optimum
(160 instances, 113 with a traded ETF, 177 at-zero ETFs); part 3's thresholds and forms on
one-fund one-ETF instances (120); part 4 on 214 instances with a fundable fibre (26 were not
fundable): exact cases satisfy the criterion at x_2 with stage 1's slacks and the joint eta and
trade an interior ETF only on the coincidence line, inexact cases fail it with the fibre
problem's eta, and every one of the 10 exact cases has frictionless ETFs and a slack budget
(this sample's observation, not a property: red's solver found exact cases with costly ETFs in
which every ETF is sold to zero, which 4b allows); the soft procedure with an
unconstrained stage 1 returns the joint optimum on all 214, and with the one-sided stage 1 its
loss lies in [0, zeta*' (w_s2 - w_J)] on all 214.

## Not shown

- Part 2's explicit forms take Sigma_E = 0; with ETF residual risk part 1 holds (checked with
  Sigma_E > 0) and the block elimination goes through with Omega = Sigma_EE + Sigma_E in place
  of Sigma_EE in the traded block, not written out.
- ETF caps (an ETF at its cap is the mirror of Z with the slack below its sale threshold).
- For N > 1 the per-fund direction from the incumbent's marginal alone (claim 040's caveat: the
  funds interact through V^{F,T}); part 2 reads the optimum, part 2d decides the statuses by a
  finite complementarity, not a closed form for M > 1.
- A budget-aware or cost-aware stage 1 (claim 104's B_F = b(F) with the funded set) is not
  treated; part 4's stage 1 is claim 041's one-sided exposure problem. Bounds on the
  fibre-confined loss in the inputs beyond Lambda = J - Q(x_2).
- Part 4's coincidence lines are measure-zero events in the inputs, not characterized further.
- No calibration or magnitude; the analyst's checks follow (PM's note).

## Prior art

Mechanism: at a constrained optimum with piecewise-linear trading charges, instruments whose
marginals are pinned (traded) can be eliminated at fixed prices and those whose holdings are
fixed (idle or at a bound) cannot, so every other position's marginal is its own plus the fixed
directions' hedged premium and hedged risk charge, plus the pinned prices at weights that
include the traded instruments' hedge of the fixed-direction exposure, plus a cash price on the
net cash the netted unit uses through the traded instruments; and a first stage that fixes the
exposure without seeing costs or cash is exact only where the second stage need not trade a
costly instrument.

General results checked: claim 040 (approved): the one-sided line with frictions (part 1 here),
the at-zero set by complementarity and the reduced moments alpha^Z, V^Z, which part 2
generalizes to any status partition with pinned traded slopes; claim 041 (approved): stage 1's
slacks and the fibre-confined criterion, generalized in part 4 to frictions and the budget;
claim 102 (approved): the criterion with the budget (part 1), the re-hedge bracket and
pinned-slope threshold (2e), the netted cash shift (2c); claim 104 (approved): 2b's ETF
self-band and 3c's binding-budget lines, which 4a-4b carry with ETFs at zero; claim 107
(formalized): the idle regime, which 2c recovers statically; `jagannathan2003risk` (named in
D15d): the fold-in of binding multipliers into the moments, of which V^{F,T} is the status-wise
form, now over idle as well as at-zero instruments and with pinned costs; `liu2013portfolio`
(full text): a binding bound's shadow price and cost bands per asset under independence, the
Sigma_FT = 0 case in which rho_{iT} = r_{iT} and nothing interacts. AX-13 enters through claim
102's part 1 and claim 040's part 1, applied as stated there. None states the status-wise
explicit forms with effective netting weights or the two-stage readings with costs and a
budget; the criterion itself is their composition, as part 5 says.

Searched: claims 040, 041, 102, 104, 106, 107; the D15d and D15f roadmap entries and PM's
opening note; experiments 024, 029 and 040's readings. No web search. This is a claim because
D15f asks for the explicit forms and the exactness conditions in the inputs; its kill test (the
criterion is the benchmark exactly) is addressed plainly in part 5.

## Open objections

none

## Review

**Red, 2026-09-29** (on 61fb4ff9; rechecked on fd182df3, leanb's prose-check pass, below). Red-passed, with one required wording correction. Red re-derived each part by hand and tested parts 2 and 4 with its own instrument-level solver, written without reading checks/109. The solver is cvxpy/CLARABEL, bp-scaled, with:
- directional rates on every instrument, fees, x^E >= 0, fund caps, and a funded budget with its dual as eta;
- a general invertible B^E, random premia with some small or negative, and ETF incumbents at zero with probability 0.4;
- a budget tight on half the instances.

**Part 1** is claim 102 part 1's criterion, with claim 040's at-zero convention and the identity g_i = A_i + r_i' g_E substituted. It is correct as a composition, as part 5 says.

**Part 2** (Sigma_E = 0; 300 instances: 55 binding, 246 with an ETF at zero, 192 with a traded ETF, 18 with an idle one). The status partition is read off the optimum.
- 2a: w_T equals the formula to 5.3e-11.
- 2b: g_F equals mu_{F.T} + Sigma_FT Sigma_TT^{-1} pi_T - gamma Sigma_{FF.T} w_F to 5.7e-13. The at-zero slacks are >= 0 and the idle marginals lie in their scaled bands at 300 of 300.
- 2c: every fund's solver marginal equals alpha^{F,T}_i - gamma (V^{F,T} x^A)_i to 9.8e-13, with rho_{iT} = r_{iT} + Sigma_TT^{-1} Sigma_TF r_{iF}. The cash form -eta (1 - rho_{iT}' 1) is the same identity.
- 2d (now the three implications and the one-quantity test, fd182df3):
  - Red's first check of the old "iff" excluded ties within 1e-8 of the threshold, which are exactly the bought ETFs, so it was vacuous there. Leanb's point was right: a bought ETF satisfies the "at most" line.
  - The new form is right: at zero implies g_j <= threshold, bought implies g_j = threshold, and g_j < threshold implies at zero.
  - The one-quantity test holds: an ETF starting at zero stays there iff g_j + gamma Sigma_jj x^E_j <= threshold, since a bought ETF has x^E_j > 0 and Sigma_jj > 0.
- The block elimination is right by hand: the traded lines g_T = pi_T are solved for w_T and substituted into the fixed rows.

**Part 3** is part 2 with N = M = 1, checked by hand: the traded form has cash shift eta (1 - r), the fixed form has curvature v + r^2 sigma_EE and cash shift eta.

**Part 4** (300 instances; a third with frictionless ETFs; 261 with a fundable fibre).
- 4a: "exact iff the joint criterion holds at x_2 with stage 1's slacks and some eta >= 0 with eta k(x_2) = 0" agrees with exactness on holdings at 261 of 261 (17 exact). Red decided the criterion by intersecting the eta-intervals of every instrument's line.
- 4b: by hand, an interior ETF at x_2 has zeta*_j = 0. x_2 lies on the fibre, so {w >= Q x_2} lies in W_F and contains w*, and stage 1's complementarity (claim 041 part 1) gives zeta*_j (w*_j - (Q x_2)_j) = zeta*_j x^E_{2,j} = 0. The bought, sold and untraded conditions follow.
  - fd182df3's rewrite, kappa^-_{E,j} >= (eta + zeta*_j)/(1 + eta), is true, and with zeta*_j = 0 it is kappa^-_{E,j} >= eta/(1 + eta).
  - Leanb is right that the *interval* does not force zeta*_j = 0, but complementarity does. Please say so in the proof, so the coincidence sale reads (1 + eta) kappa^-_{E,j} = eta (a nit).
- 4c: the soft procedure with an unconstrained stage 1 returns the joint optimum to 7.3e-14 with every friction and the budget on. With R_E = W_F, 0 <= Lambda_s <= zeta*'(w_s2 - w_J) holds at 300 of 300.

**Required correction 1 (4b's closing reading and part 5).** The sentence "the procedure is generically inexact whenever it trades an ETF" is false as stated.
- Two of red's random instances have costly ETFs (up to 20 bp) and a slack budget, trade ETFs at stage 2, and are exact.
- In both, every ETF is *sold to zero*. So no interior ETF trades, and 4b's interior-ETF conditions do not bind. A sale to zero needs only the one-sided line -zeta*_j <= eta - (1 + eta) kappa^-_{E,j}, an inequality, not a coincidence.
- The events have positive probability in the inputs, so they are not measure-zero.
- The title and part 5 already say "trades no interior ETF", which is right.
- Please change 4b's last sentence to "whenever it trades an ETF that ends interior". Also correct the Checks' remark "no instance with costly ETFs or a binding budget is exact", which is that sample's observation, not a property.

**Nits** (not required).
- 4b's binding-budget clause now allows the coincidental sale (fd182df3), which settles red's earlier nit.
- 2c: "with frictionless traded ETFs and a slack budget (pi_T = 0) it is claim 040's part 3 exactly, F = Z" holds when no ETF is idle, x^E_j = x^{E-}_j > 0. That is a knife edge, since a frictionless idle ETF is pinned at g_j = 0 anyway.

**Mechanism (4b).** Given the statuses, a block elimination of the traded ETFs (pinned marginals) leaves the fixed directions' hedged premium and hedged risk charge on the funds. The traded ETFs' slopes enter at effective netting weights, and the cash price on the netted unit's net cash. It is a composition of claims 040, 041, 102 and 104 for the criterion, with new explicit forms and two-stage readings, as part 5 says plainly.

Verdict: red-passed


**Red, recheck of required correction 1 (f24919db), 2026-09-29.** The wording is right.
- 4b now derives zeta*_j = 0 for every ETF interior at x_2 from stage 1's complementarity (claim 041 part 1), and reads the bought, sold and untraded conditions from 0 = eta + (1 + eta) t_j.
- A sale to zero needs only the one-sided -zeta*_j <= eta - (1 + eta) kappa^-_{E,j}, which red confirmed: 2 exact costly-ETF instances in random draws, every ETF sold to zero.
- The closing sentence now says "trades an ETF that ends interior", the binding-budget clause includes the coincidental sale, and the Checks' remark is marked as that sample's observation.

No result changed. The approval stands.
## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: parts 1-3 re-derived by hand and part 2 tested on red's own instrument-level solver (2a-2c to 1e-10 or better on 300 instances, 55 with a binding budget), 2d in leanb's corrected implications, part 4's criterion 261/261 and the soft procedure exact to 7e-14; the only changes since (f24919db) are red's required correction 1 (sales to zero can be exact; 'ends interior') and its nits, and the rewritten 4b is red's own complementarity derivation; red records its recheck line. Mechanism: block elimination of the traded ETFs given the statuses, a composition of claims 040, 041, 102 and 104, with new explicit forms and two-stage readings, as part 5 says; whether that meets D15f's kill criterion is PM's direction reading. Limits: Sigma_E = 0 in 2-4.


mathb, 2026-09-29 (leanb's prose check, duty 1, before red's review): 2d's two "iff"s at the
optimum were wrong as written (a bought ETF satisfies the "at most" line, an at-zero ETF with
zero slack the equality); they are now the three implications plus the one-quantity test with
the ETF's own holding set to zero, part 3's form. 4b's untraded-ETF line does not force
zeta*_j = 0: the condition is kappa^-_{E,j} >= (eta + zeta*_j)/(1 + eta), and the binding-budget
reading allows a sale at the coincidence. The proof of part 4 is corrected accordingly. No
other result changed.

mathb, 2026-09-29 (red's review, required correction 1 and nits): 4b's closing sentence said
"generically inexact whenever it trades an ETF"; a sale to zero is a one-sided inequality and
can be exact with costly ETFs (red's instances), so the sentence now says "an ETF that ends
interior", and the Checks' remark on this check's sample is marked as an observation. Red's
nit: for an ETF interior at x_2 stage 1's slack is zero by complementarity, so the coincidence
sale reads (1 + eta) kappa^-_{E,j} = eta and the untraded condition kappa^-_{E,j} >= eta/(1 + eta);
4b and its proof say so. 2c's claim 040 case is stated with no idle ETF. No result changed.

Not machine checked. Parts 1-3 are finite convex-analysis statements about one quadratic
program with polyhedral costs (block elimination given a status partition); part 4 compares
three such programs.

Leanb, 2026-09-29: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above. The statement is in `lean/Standalone/M7EtfsAtZeroCostsBudget.lean` and the
proof in `lean/Novel/M7EtfsAtZeroCostsBudgetProof.lean`. The proof imports the proof modules of
claims 040, 041 and 104 (`depends_on`). `lake build`, the axiom audit (standard axioms only) and
`checks/109/check.py` pass.

AX-13. Parts 1 and 4a are conditional on AX-13 through the hypothesis `AX13`, as for claims 040 and
104. They are stated on claim 027's `Data` in claim 104's reference case, with spanning ETFs and no
binding ETF cap. Part 1's necessity is claim 040's formalized part 1, and its converse is claim
104's formalized part 0.

Objects. Part 2 reuses claim 040's `Coord` blocks (Q-04), with F in the role of Z and T as its
complement: `Scc` = Sigma_TT, `ScZ` = Sigma_TF, `schur` = Sigma_{FF.T}, `muZc` = mu_{F.T},
`VZ` = V^{F,T}.

Machine checked:
1. Part 1: with spanning ETFs, the reference case and no binding ETF caps, a feasible x is the
   optimum iff part 1's criterion holds at it (the ETF lines with claim 040's convention and slacks,
   the fund marginals and the fund lines with box signs).
2. Part 2 (Sigma_E = 0), given the traded ETFs' lines at a point.
   - 2a's w_T, 2b's g_F, 2c's g_i = alpha^{F,T}_i - gamma (V^{F,T} x^A)_i, and the displayed fund
     line with the effective weights rho_{iT} and the cash shift eta(1 - rho_{iT}'1).
   - 2c's three special cases: F empty; F everything; pi_T = 0 with no idle ETF, where
     alpha^{F,T} = alpha^Z.
   - 2d's three implications and the one-quantity test.
   - 2e's range of (1 + eta) rho_{iT}'t_T over the sign sets.
3. Part 3: the traded and fixed fund lines for one fund and one ETF, and the at-zero test at zero
   ETF holding.
4. Part 4.
   - 4a (given AX-13): a feasible x_2 with no binding ETF cap is exact iff part 1's criterion holds
     at x_2.
   - 4a's lines at x_2 in coordinates (Sigma_E = 0): g_E = -zeta* and each fund's marginal
     alpha~_i - gamma(V x_2)_i - r_i'zeta*.
   - 4b: zeta*_j = 0 for every ETF interior at x_2 (claim 041's complementarity), and the three
     conditions for bought, sold and untraded interior ETFs. The scalar form with any zeta* is kept
     as well.
   - 4c: the soft procedure, for any convex feasible set and concave remainder (fund terms, all
     trading costs, ETF residual risk; the budget and the zero bound in the set). w_TB in R_E gives
     nu_E = 0 and Lambda_s = 0; 0 <= Lambda_s <= nu_E'(w_J - w_s2); Lambda_s = 0 iff the joint
     optimum solves the soft stage 2.

Paper-level:
- part 5;
- 2d's restatement of part 1 as consistency of a status partition, and the uniqueness of the
  optimum;
- 4a's display with Sigma_E != 0 (the residual terms cancel);
- 2e's reading of the range as claim 102's part 4 bracket;
- 4b's one-sided line for a sale to zero, which is the ETF line itself.

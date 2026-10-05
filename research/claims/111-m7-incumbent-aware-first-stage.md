---
id: 111
title: "A first stage that sees the ETFs' costs, fees, zero bounds and the budget (the ETF-only problem from the incumbents): the two-stage procedure is exact iff the fibre problem's exposure multiplier can be taken to vanish; it is exact whenever every fund is held at the ETF-only optimum, and whenever every ETF trades at the first stage in a direction the second stage keeps to an interior holding with a slack budget; and the loss of any fibre-confined procedure is at most the ETF-line residual's squared Sigma_EE^{-1}-norm over twice gamma, the residual being the gap between each ETF's marginal on the fibre and its scaled cost slope"
status: formalized
model_version: M7
depends_on: [041, 102, 104, 109]
axioms_used: [AX-13]
formal: lean/Standalone/M7IncumbentAwareFirstStage.lean
direction: D15f
---
## Statement

PM's second D15f question: claim 109's part 4 shows that claim 041's fibre-confined procedure
(a first stage that fixes the exposure by the frictionless one-sided problem) is generically
inexact once a costly ETF ends interior, because it aims at an exposure the joint optimum will
not pay to reach. The practical fix is a first stage that prices the ETF trades: the *ETF-only
problem from the incumbents*, with the ETFs' rates, fees, zero bounds and the budget, the funds
frozen at their incumbents (claim 106's ETF-only class E^0). This claim states when the
resulting two-stage procedure is exact and what any fibre-confined procedure loses, in the
inputs, through one vector: the *ETF-line residual* at the stage-2 solution, which is a
supergradient of the fibre value function and is zero exactly when the split is exact.

**Setting.** Claim 109's with Sigma_E = 0: spanning ETFs, fees c^E, ETF rates, the zero bound
x^E >= 0, no ETF caps, the funded budget k(x) >= 0 with h^- > 0, the objective Q(x), the joint
optimum x_J (unique) with value J and exposure w_J = x^E_J + Q x^A_J, and claim 109's status
notation. The *fibre value* of an exposure w is

```
V(w) = max { Q(x) : x^A in the box, x^E = w - Q x^A >= 0, k(x) >= 0 },
```

the best the funds can do once the ETFs must deliver exposure w (-infinity if the fibre is not
fundable); J = max_w V(w) = V(w_J). A *fibre-confined procedure* picks an exposure w_1 at a
first stage and takes x_2 as the maximizer in V(w_1) at the second; T = V(w_1), Lambda = J - T.

The *incumbent-aware first stage* solves

```
max { Q(x) : x^A = x^{A-},  x^E >= 0,  k(x) >= 0 }        (funds frozen; ETF rates, fees, zero bound and budget on),
```

at x_1 (unique), with exposure w_1 = x^E_1 + Q x^{A-}, statuses (Z_1, B_1, S_1, I_1), pinned
slopes pi_1 = eta_1 1 + (1 + eta_1) t_1 on T_1, at-zero slacks zeta_1 and cash price eta_1 (claim
109's part 2 with x^A = x^{A-}: w_{1,T} = Sigma_TT^{-1}[(mu_T - pi_1)/gamma - Sigma_TF w_{1,F}], w_{1,F} = Q_F x^{A-} + x_{1,F}).

For a fibre-confined procedure at w_1 with a fundable fibre, let (eta_2, t^{(2)}, zeta^{(2)}) be
KKT multipliers of the fibre problem at x_2 (the budget's, the ETF cost subgradients at the
ETF trades x^E_2 - x^{E-}, and the zero bound's; they exist by AX-13), and define the
*ETF-line residual*

```
s = g_E(x_2) - eta_2 1 - (1 + eta_2) t^{(2)} + zeta^{(2)},        g_E(x_2) = mu_E - gamma Sigma_EE w_1,
```

the amount by which each ETF's joint line (claim 109's part 1) fails at x_2 with the fibre's
multipliers: for an ETF traded to an interior holding, s_j = g_{E,j}(x_2) - eta_2 - (1 + eta_2) t_j
with t_j its pinned slope; for an untraded interior ETF, s_j is g_{E,j}(x_2) - eta_2 less the
band element the fibre's multipliers select; for an ETF at zero, the zero-bound multiplier is
added.

### Part 1. The residual is a supergradient of the fibre value, and the loss bound

V is concave, strongly so with modulus gamma Sigma_EE (V(w) + (gamma/2) w' Sigma_EE w is concave),
and for every fundable w' 

```
V(w') <= V(w_1) + s'(w' - w_1) - (gamma/2) (w' - w_1)' Sigma_EE (w' - w_1).
```

Hence, for any fibre-confined procedure and any valid choice of the fibre's multipliers,

```
(gamma/2) [ (x^A_J - x^A_2)' V (x^A_J - x^A_2) + ||w_J - w_1||^2_{Sigma_EE} ]  <=  Lambda  <=  min( s'(w_J - w_1),  s' Sigma_EE^{-1} s / (2 gamma) ),
||w_J - w_1||_{Sigma_EE} <= ||s||_{Sigma_EE^{-1}} / gamma,
```

with ||u||_{Sigma_EE} = (u' Sigma_EE u)^{1/2}. The loss of splitting is bounded above by the
residual's size in the ETFs' own metric, in the inputs at x_2, whatever the first stage was,
and below by the misplacement of the funds and of the exposure in their risk metrics; in
particular Lambda = 0 iff x_2 = x_J (V positive definite).

### Part 2. Exactness

T = J iff the fibre problem at x_2 admits multipliers with s = 0, and then x_2 = x_J; s = 0 is
claim 109's part 4a (the joint criterion at x_2). Whenever the multipliers of the fibre problem
are unique on a coordinate (an ETF traded to an interior holding with the fibre's cash price
determined), s_j = 0 there is necessary for exactness; at an ETF at zero, an untraded ETF, or
under a binding budget on the fibre (where the pair (eta_2, s) can move together), s need not
vanish at an exact split, and the bound of part 1 holds for every valid choice.

### Part 3. When the incumbent-aware split is exact, in the inputs

3a. *Every fund held at the ETF-only optimum.* If for every fund i, at x_1 with eta_1,

    ```
    eta_1 - (1 + eta_1) kappa^-_i <= g_i(x_1) <= eta_1 + (1 + eta_1) kappa^+_i    (the lower bound dropped when x^-_i = 0, the upper when x^-_i = bar x_i),
    ```

    then x_2 = x_1 = x_J and Lambda = 0 (claim 102's part 2, the ETF-optimized test, with the
    zero bound and the budget carried by claim 109's part 1).

3b. *Every ETF traded, directions kept, budget slack.* If every ETF is traded to an interior
    holding at x_1 (F_1 empty; a sale to zero puts the ETF in Z_1, claim 109's definitions), the budget is slack at x_1 and on the fibre at x_2, and at x_2 every ETF is
    traded in the same direction as at x_1 to an interior holding, then s = 0 and the split is
    exact: with every ETF traded, w_1 = Sigma_EE^{-1}(mu_E - pi_1)/gamma does not depend on the
    funds' by-product, so freezing the funds costs nothing.

3c. *Fixed ETFs.* If some ETF is fixed at x_1 (at zero or idle, F_1 nonempty), the exposure
    w_1 carries the incumbents' by-product Q_F x^{A-} in the fixed directions, and the joint
    optimum's carries Q_F x^A_J; if the statuses are kept at x_2 (the same T_1 with the same
    directions, F_1 fixed) and the budget is slack, then the residual is supported on the fixed
    directions, s_T = 0, the stage-2 trades carry no by-product into the fixed directions
    (Q_F (x^A_2 - x^{A-}) = 0 follows: both points lie on the fibre of w_1 with the same fixed
    holdings), and the split is exact if every fund's joint line holds at x_2 with stage 1's
    ETF marginals (its slopes and slacks), that is alpha~_i - gamma (V x_2^A)_i + r_i' g_E(x_1) in
    T_i(x_2) with the box signs. In general the loss is bounded by part 1 with s_F the fixed
    directions' residual.

3d. *Binding budget.* When the budget binds, the ETF-only problem's cash price eta_1 prices
    the ETF trades alone, while the joint optimum's prices the funds' trades too; the split is
    exact iff some fibre multipliers make s = 0 (part 2), and part 1 bounds the loss; no
    input-level sufficient condition beyond 3a is claimed.

### Part 4. Against claim 041's first stage

Claim 041's frictionless one-sided first stage fails exactly where an ETF ends interior with
a cost or a cash price (claim 109's 4b); its loss is also bounded by part 1, with s computed
at its own x_2. The incumbent-aware first stage is exact in 3b's case, which is where claim
041's fails, and it never fails through the ETFs' costs alone: its residual can be nonzero
only in the fixed directions (3c), through the budget (3d), or through a traded ETF changing
status at stage 2 (crossing its incumbent, or sold to zero, because the funds' trades move
x^E_2 = w_1 - Q x^A_2; then s_j = t_{1,j} - t^{(2)}_j != 0 even with F_1 empty and a slack
budget, the case 3b's "directions kept" excludes); all three come from the funds' trades
moving the by-product, the cash or the ETFs' statuses, which no first stage that does not see
the funds can anticipate. Its fibre is always fundable, since x_1 lies on it and satisfies the
budget, whereas claim 041's first stage, blind to the budget, can pick an exposure no funded
second stage can deliver (experiment 044: 41% of its draws). It is the better first stage on
exactness and fundability, not on loss: when it is inexact, the exposure it fixed carries the
funds' incumbent by-product, and funds that should move a lot then pay for it, so its loss can
exceed claim 041's on the draws where both fibres are fundable (experiment 045, assumed
inputs: exact at 122 against 15 of 594, median loss 32 bp against 15.5 bp when inexact). So the
practical rule: run the ETF-only problem from the incumbents as the first stage; if every fund
is then held (3a) or every ETF trades and the second stage keeps the directions (3b), the split
is exact; otherwise read the residual s at the second stage, part 1's bound says what the split
loses, and the soft procedure with an unconstrained first stage (claim 109's 4c) is exact if
the loss matters; re-running the first stage from the second stage's fund holdings (Not shown)
is the repair within the split.

**One sentence without model nouns.** A first stage that fixes the exposure by trading the
hedging instruments from their current positions, paying their costs and the cash price, is
exact whenever no position needs to move or whenever every instrument trades and keeps
trading the same way once the positions move; otherwise the split's loss is at most the
squared size, in the instruments' risk metric, of the gap between each instrument's marginal
on the fixed exposure and its cost slope, divided by twice the risk aversion.

## Proof

### 1. The supergradient and the bound

Concavity: the fibre problem's objective Q(x^A, w - Q x^A) is jointly concave in (x^A, w)
(Q concave, the map affine) and its feasible set {x^A in the box, w - Q x^A >= 0, k >= 0} is
convex (k concave), so V, a partial maximum, is concave; and Q(x^A, w - Q x^A) + (gamma/2) w' Sigma_EE w
is still jointly concave (G_E(w) + (gamma/2) w' Sigma_EE w = mu_E' w is linear; claim 040's
proof of part 0 for Q = G_E(w) + [fund terms] - C_E(w - Q x^A - x^{E-}) with Sigma_E = 0), so
V(w) + (gamma/2) w' Sigma_EE w is concave: V is strongly concave with modulus gamma Sigma_EE.
Supergradient: let L(x^A, w) = Q(x^A, w - Q x^A) + eta_2 k(x^A, w) + zeta^{(2)}' (w - Q x^A), concave in
(x^A, w). The fibre problem's KKT at x_2 (AX-13 on the lifted polyhedral problem, claim 102's
part 1 form, with the cost subgradient t^{(2)} and the multipliers eta_2 >= 0, zeta^{(2)} >= 0,
complementary slackness eta_2 k(x_2) = 0 and zeta^{(2)}' x^E_2 = 0) says that L has a supergradient
at (x_2, w_1) whose x^A-component lies in the box's normal cone at x^A_2 and whose w-component
is s as displayed (the derivative of L in w: mu_E - gamma Sigma_EE w - t^{(2)} - eta_2 (1 + t^{(2)}) + zeta^{(2)},
since k(x) = h^- - 1'(x - x^-) - C(x - x^-) contributes -1 - t per ETF unit). For any feasible
(x^A', w') with w' fundable: V(w') = Q(x') <= L(x', w') (the added terms are nonnegative)
<= L(x_2, w_1) + s'(w' - w_1) + n'(x^A' - x^A_2) <= Q(x_2) + s'(w' - w_1) (n in the normal cone,
complementary slackness), and Q(x_2) = V(w_1). The strong form adds the quadratic (apply the
same to L + (gamma/2) w' Sigma_EE w, whose w-supergradient is s + gamma Sigma_EE w_1). The
bounds: the upper ones from the strong inequality at w' = w_J, Lambda <= s' d - (gamma/2) d' Sigma_EE d
with d = w_J - w_1, at most s'd and, maximized over d, at most s' Sigma_EE^{-1} s/(2 gamma). The
lower one: Q is strongly concave with modulus gamma Sigma on the full holdings (Q + (gamma/2) x' Sigma x
is concave), the joint feasible set is polyhedral (the box, the zero bound and the lifted
budget), and at x_J some supergradient g of Q satisfies g'(x' - x_J) <= 0 for every feasible x'
(AX-13's optimality condition), so Q(x_2) <= Q(x_J) - (gamma/2)(x_2 - x_J)' Sigma (x_2 - x_J), and
(x_2 - x_J)' Sigma (x_2 - x_J) = (x^A_2 - x^A_J)' V (x^A_2 - x^A_J) + d' Sigma_EE d (claim 040's
part 0 identity with Sigma_E = 0). Combining the two, (gamma/2) ||d||^2_{Sigma_EE} <= Lambda <= s'd - (gamma/2) ||d||^2_{Sigma_EE},
so gamma ||d||^2_{Sigma_EE} <= s'd <= ||s||_{Sigma_EE^{-1}} ||d||_{Sigma_EE}, the exposure-gap
bound; and Lambda = 0 forces x_2 = x_J.

### 2. Exactness

If s = 0 for some fibre multipliers, the same multipliers satisfy the joint problem's KKT at
x_2 (the fund lines are the fibre's, the ETF lines are s = 0, the zero bound and budget
multipliers are as they are), so x_2 = x_J by AX-13's sufficiency and uniqueness. Conversely if
x_2 = x_J, the joint multipliers at x_J are fibre multipliers (the fibre's KKT is the joint's
with the ETF lines dropped) and give s = 0. Uniqueness on a coordinate: for an ETF traded to an
interior holding, t^{(2)}_j is the pinned slope and zeta^{(2)}_j = 0, so s_j = g_{E,j}(x_2) - eta_2 - (1 + eta_2) t_j
is determined once eta_2 is; with a slack budget eta_2 = 0 and s_j is unique.

### 3. Exactness conditions

3a: claim 102's part 2 with claim 109's part 1 as the criterion: x_1 is feasible for the joint
problem; if every fund's line holds at x_1 with eta_1 and the zero-trade slopes, x_1 satisfies
the joint KKT (the ETF lines hold at x_1 by its own optimality), so x_1 = x_J; and x_1 lies on
the fibre of w_1, where it is optimal, so x_2 = x_1. 3b: with F_1 empty, claim 109's 2a at x_1
gives w_1 = Sigma_EE^{-1}(mu_E - pi_1)/gamma; at x_2 every ETF is traded in the same direction and
interior, so the fibre's multipliers are pinned, t^{(2)} = t_1, zeta^{(2)} = 0, and with eta_2 = 0 = eta_1
the residual is s = mu_E - gamma Sigma_EE w_1 - t_1 = pi_1 - t_1 = 0; part 2 gives exactness. 3c:
with the statuses kept and eta = 0, the traded coordinates have s_T = g_T(x_2) - t_1 = mu_T - gamma (Sigma_EE w_1)_T - t_1 = 0
by x_1's ETF lines; on F, g_F(x_2) = g_F(x_1) (the exposure is w_1 in both), which satisfies the
idle band and the at-zero inequality at x_1, so stage 1's multipliers (t_{1,F}, zeta_{1,F}) make
the ETF lines hold at x_2; if moreover the fund lines hold at x_2 with those multipliers, the
joint KKT holds at x_2 and the split is exact (part 2). The by-product condition
Q_F (x^A_2 - x^{A-}) = 0 is what keeps w_{1,F} equal to the joint's exposure in the fixed
directions: it is not a hypothesis but a consequence of the kept statuses, since x_1 and x_2
both lie on the fibre of w_1 with x^E_{2,F} = x^E_{1,F}, so Q_F x^A_2 = w_{1,F} - x^E_{2,F} = Q_F x^{A-}.
3d is part 2 restated.

### 4. Comparison

Claim 109's 4b for claim 041's stage 1; part 1 applies to any w_1. In 3b's case claim 041's
stage 1 fails (its ETF lines need eta + (1 + eta) kappa^+_{E,j} = 0 for a bought interior ETF)
while the incumbent-aware one is exact.

## Checks

`uv run python checks/111/check.py` (exits non-zero on failure; a check, not a proof). Random
one-review instances as in checks/109 (3 funds, 2 ETFs, fees, ETF rates up to 20 bp on three
quarters of the instances, an ETF starting at zero on half, the budget tight on half; all
assumed), solved by CLARABEL through cvxpy. For the incumbent-aware first stage (239 fundable
fibres) and claim 041's frictionless one-sided first stage (217 fundable, 22 not): the fibre
problem's exposure multiplier, its sign fixed once by the supergradient test at perturbed
exposures, satisfies part 1's loss bounds and the exposure-gap bound on every instance; a zero
residual never occurs at an inexact split; at exact splits with a slack fibre budget the
pinned coordinates' residuals vanish (with a binding budget the fibre's cash price differs
from the joint's and the residual need not, as part 2 says); for traded interior ETFs the
residual equals g_j(x_2) - eta_2 - (1 + eta_2) t_j; 3a's hold test (6 instances) and 3b's
all-traded condition (24 instances) give exactness every time. The incumbent-aware split is
exact on 30 of 239 instances, 21 of them with costly ETFs; claim 041's on 10 of 217, none with
costly ETFs.

## Not shown

- Sigma_E > 0 (the same argument with Omega = Sigma_EE + Sigma_E; not written out); ETF caps.
- 3c gives a sufficient condition with fixed ETFs; a necessary and sufficient condition in the
  inputs alone, and 3d's binding-budget case, are left to the residual (parts 1-2).
- Marked incumbents above a cap (M6 caps post-trade holdings, so marking can carry a fund above
  bar x_i): the first stage as defined freezes the funds at x^{A-}, which is then infeasible.
  Convention (PM, from experiment 048, which met it in 4 of 72 cells): the first stage freezes
  each such fund at min(x^-_i, bar x_i), with the forced sale to the cap charged at its rate and
  its proceeds in the cash the first stage sees; the second stage then trades from x^{A-} as
  before. Parts 1-2 are unaffected (they take the fibre as given); 3a-3c are stated for
  x^{A-} <= bar x^A.
- A first stage that sees the funds' by-product (an iterated split: re-run the ETF-only problem
  from x_2's fund holdings) is not analysed; its fixed point is the joint optimum, and it is
  the repair for the incumbent by-product that experiment 045 finds in the one-shot split's
  loss.
- No calibration or magnitude; the analyst's checks follow.

## Prior art

Mechanism: the value of a constrained concave program as a function of a resource vector is
concave, and the multipliers of the constraints in which the resource enters are its
supergradients, so a split that fixes the resource by a proxy loses at most the squared size
of those multipliers, in the resource's curvature metric, over twice the curvature; the proxy
that trades the resource instruments from their current positions at their true costs is exact
whenever the positions need not move or every instrument's price stays pinned.

General results checked: claim 104 (approved): the supergradient bound Lambda <= L^2/(2 gamma)
and L ||b_J - b*|| in its 3a-3c, with a norm bound L in place of the residual itself; part 1 here
is the same argument with the exact multiplier vector and the zero bound, so the bound is
tighter and in the inputs at x_2. Claim 041 (approved): stage 1's slacks as multipliers (its
part 1), of which part 2 is the general form. Claim 109 (approved): 4a-4c, and 2a for 3b-3c.
Claim 102 (approved): part 2's ETF-optimized test (3a). Claim 106 (formalized): the ETF-only
class E^0 that the first stage solves. The concave-perturbation supergradient argument is
`rockafellar1970convex`'s Theorem 29.1 in substance; it is proved inline in six lines from the
fibre KKT (AX-13) because only the Lagrangian inequality is used, and the ledger entry AX-13
supplies the multipliers. No web search. This is a claim because D15f's second question asks
for the practical first stage and the loss in the inputs, and no cited claim states the
residual bound or the incumbent-aware split's exactness conditions.

## Open objections

none

## Review

**Red, 2026-09-29** (on 8b063c87). Red-passed. Red checked parts 1-3 by hand, including leanb's three points as mathb made them, and tested parts 1 and 3a-3b on random instances. The instances are red's claim 109 generator: 3 funds, 2 ETFs, fees, ETF rates up to 20 bp (a quarter frictionless), an ETF starting at zero with probability 0.4, and the budget tight on half. Red's bp-scaled cvxpy solves cover the joint problem, the incumbent-aware first stage (funds frozen at x^{A-}) and the fibre problem. The residual s is read as the fibre value's sensitivity to the exposure, the dual of the fibre equality x^E = w_1 - Q x^A, with its sign fixed by a finite difference along w_J - w_1. Red wrote this without reading checks/111.

**By hand.**
- *Concavity.* V is strongly concave with modulus gamma Sigma_EE, because G_E(w) + (gamma/2) w' Sigma_EE w = mu_E' w is linear and the rest is jointly concave in (x^A, w).
- *The residual.* s is the w-component of the Lagrangian's supergradient, g_E - eta_2 - (1 + eta_2) t^{(2)} + zeta^{(2)}, since the budget contributes -1 - t per ETF unit.
- *The upper bounds* follow from the strong inequality at w_J, maximized over d.
- *The lower bound.* Q's strong concavity at x_J over the polyhedral feasible set, with the Sigma_E = 0 identity x' Sigma x = x^A' V x^A + w' Sigma_EE w, gives the lower bound, so gamma ||d||^2 <= s'd, leanb's constant.
- *Part 2.* When s = 0 the fibre's fund lines become the joint ones, and the converse also holds.
- *3a-3c* follow. For 3b: with F_1 empty and eta_1 = 0, w_1 = Sigma_EE^{-1}(mu_E - t_1)/gamma, and with the directions kept, t^{(2)} = t_1, so s = 0.

**Numerically** (400 instances; the incumbent-aware fibre is fundable at all 400, since x_1 lies on it):
- Lambda >= (gamma/2)[(x^A_J - x^A_2)' V (x^A_J - x^A_2) + ||w_J - w_1||^2_{Sigma_EE}] at 400 of 400.
- Lambda <= min(s'(w_J - w_1), s' Sigma_EE^{-1} s/(2 gamma)) at 400 of 400.
- The exposure-gap bound holds at 400 of 400.
- A zero residual never occurs at an inexact split.
- 3a (every fund held at x_1 by the hold test with eta_1): exact at 22 of 22.
- 3b (every ETF traded *to an interior holding* at x_1, directions kept to interior holdings at x_2, budget slack at both): exact at 35 of 35.
- 55 of the 400 splits are exact.

**Nit** (not required). 3b's "every ETF is traded at x_1 (F_1 empty)" is right by claim 109's status definitions, where a sale to zero puts the ETF in Z, part of F. A reader can still take "traded" to include a sale to zero. Red's first screen did, and it flagged 34 inexact instances whose first stage sold an ETF to zero. Please write "every ETF traded to an interior holding at x_1".

**Mechanism (4b).** The fibre value is concave in the exposure, and the fibre problem's exposure multiplier is its supergradient. So any exposure-fixing split loses at most the residual's squared size in the ETFs' metric over twice gamma, and the incumbent-aware first stage pins that residual to zero where no fund moves or every ETF keeps trading. It is a sharpening of claim 104 3a-3c's norm bound with the exact multiplier vector. Part 4's comparison with claim 041 now reads exactness and fundability, not loss, which is right (experiment 045's observation).

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: parts 1-3 checked by hand (strong concavity of the fibre value in the exposure, the residual as the Lagrangian's w-supergradient, the upper and lower loss bounds, part 2's iff, 3a-3c) and tested on 400 random instances with fees, ETF rates, ETFs at zero and a tight budget on half (both loss bounds and the exposure-gap bound 400/400, no zero residual at an inexact split, 3a 22/22, 3b 35/35); leanb's prose points are made and part 4 reads exactness, not loss (experiment 045). Mechanism: a sharpening of claim 104 3a-3c's norm bound with the exact multiplier vector, an application. Limit: Sigma_E = 0; the iterated split Not shown; red's 3b wording nit routed.


mathb, 2026-09-29 (leanb's prose check, duty 1, before red's review): part 1's exposure-gap
constant needed the lower bound Lambda >= (gamma/2)[(x^A_J - x^A_2)' V (x^A_J - x^A_2) + ||w_J - w_1||^2_{Sigma_EE}],
now stated and proved from strong concavity at x_J; 3c's by-product condition is a consequence
of the kept statuses, not a hypothesis, and the proof says so; part 4 names the third route
to a nonzero residual (a traded ETF changing status at stage 2). No result changed.

mathb, 2026-09-29 (experiment 045): part 4's reading no longer presents the incumbent-aware
stage as the better first stage outright; it is better on exactness and fundability, and can
lose more when inexact (the incumbent by-product), with the iterated split named as the
repair. No result changed.

mathb, 2026-09-29 (red's nit, after approval): 3b's hypothesis reads "every ETF traded to an
interior holding at x_1", since a sale to zero belongs to F_1 under claim 109's definitions. No
result changed.

mathb, 2026-09-29 (PM's note from experiment 048): the incumbent-aware first stage is defined,
when marking carries a fund above its cap, by freezing that fund at min(x^-_i, bar x_i) with the
forced sale charged, recorded in Not shown; 3a-3c are stated for incumbents within the caps.
No result changed.

Not machine checked. Parts 1-3 are finite convex-analysis statements comparing three
quadratic programs with polyhedral costs; part 4 reads them.

Leanb, 2026-09-29: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M7IncumbentAwareFirstStage.lean` and the proof
  `lean/Novel/M7IncumbentAwareFirstStageProof.lean`. The proof imports the proof modules of claims
  104 and 109, and claim 040's only through 109's (within `depends_on`, Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/111/check.py` pass.
- *Setting.* Claim 027's `Data` in claim 104's reference case with Sigma_E = 0, spanning ETFs
  (B^E invertible), Sigma~_f positive definite and gamma > 0.
- *Reused objects.* Q and Sigma_EE are claim 040's `coord` objects (via `rvec`), and w(x) is
  `toCoord`'s exposure.
- *Multipliers.* The fibre's multipliers are a predicate (`FibreMult`), with s = g_E - eta - (1 + eta)
  t_E + zeta. "No ETF caps" is modelled as caps that do not bind, and it is needed only for part 2's
  converse.

Machine checked:
1. The marginals. g_E = mu_E - gamma Sigma_EE w(x), and claim 102's identity
   g_A = alpha~ - gamma V x^A + Q'g_E, both in `coord`'s fields.
2. Part 1, unconditional.
   - At any feasible x_2 with fibre multipliers, every feasible x satisfies
     Q(x) <= Q(x_2) + s'(w(x) - w(x_2)) - (gamma/2) ||w(x) - w(x_2)||^2_{Sigma_EE}
     - (gamma/2)(x^A - x^A_2)'V(x^A - x^A_2), which gives the claim's inequality for V.
   - The lower bound (gamma/2)[d_A'V d_A + ||d||^2_{Sigma_EE}] <= Lambda holds for every feasible x_2,
     by strong concavity along the segment from x_J. The approved proof cites AX-13's optimality
     condition at x_J; the Lean needs no AX-13. Lambda = 0 iff x_2 = x_J (V positive definite).
   - 0 <= Lambda <= min(s'd, s'Sigma_EE^-1 s/(2 gamma)).
   - The exposure gap gamma ||d||_{Sigma_EE} <= ||s||_{Sigma_EE^-1}, squared and as roots.
3. Part 2.
   - Fibre multipliers with s = 0 exist iff claim 109's `Criterion` (part 4a's joint criterion) holds
     at x_2. This is unconditional; it moves t_j to claim 040's convention at an ETF at zero.
   - s = 0 gives T = J, and x_2 = x_J with V positive definite.
   - The converse is given AX-13, through claim 104's `JointOptimality`, with no binding ETF cap.
   - At an ETF traded to an interior holding under a slack budget, s_j = g_j - kappa^+ or
     g_j + kappa^-. So s_j = 0 for every valid choice at an exact split (given AX-13).
4. Part 3.
   - 3a. x_1 is the joint optimum, and every fibre maximizer is x_1 (V positive definite).
   - 3b. For ETFs traded to interior holdings at x_1 (red's wording) and kept in direction to interior
     holdings at x_2, with a slack budget at both, every valid choice gives s = 0 and the split is
     exact.
   - 3c. s_T = 0; Q_F(x^A_2 - x^{A-}) = 0 as a consequence of the kept statuses; and exactness under
     the fund-line condition.
   - The joint criterion's sufficiency is proved directly, without AX-13.

Paper-level:
- the existence of the fibre multipliers (AX-13 on the fibre problem, rule 21);
- 3d (part 2 restated);
- part 4 and its experiment readings;
- the Checks.

In 3b, exactness is stated for every valid multiplier choice at x_2, so it rests on their existence
(AX-13).

---
id: 44
title: "Two reviews, one fund, one ETF and cash with a binding budget, in the inputs: today's buy, hold or sell lines are the one-review lines with the cash price replaced by the dynamic cash price, today's multiplier plus the discounted expected cash price tomorrow, and with each instrument's marginal raised by its incumbent value, the discounted expected marked value of a unit carried into tomorrow, which is tomorrow's marginal score if the unit is then held, its scaled purchase threshold if bought, its scaled sale threshold if sold; repeated one-review optimization is dynamically optimal iff its root holdings satisfy these lines with its own tomorrow multipliers; with a slack budget tomorrow the lines are claim 029's, so the binding budget's whole contribution is the expected cash price, a uniform rise of every threshold today, and the scaling of the incumbent values by one plus tomorrow's cash price"
status: formalized
model_version: M7
depends_on: [29, 102, 104, 110]
axioms_used: [AX-13]
formal: lean/Standalone/M7TwoReviewsBindingBudget.lean
direction: D16
---
## Statement

D16's first claim (LAB_REQUEST item 1). The two-review problem with one fund, one ETF and cash,
proportional costs, long-only caps, return marking, learning and a funded budget that may bind
at either review is one concave program over a polyhedron (part 1), so its optimality
conditions are explicit (AX-13): the root's lines are claim 110's one-review lines with two
changes, both read from tomorrow's solutions (part 2). The binding budget enters through
exactly these: the expected cash price tomorrow, added to today's multiplier, raises every
purchase threshold and lowers every sale threshold today by the same amount (the option value
of cash), and it scales tomorrow's incumbent values (part 3). Repeated one-review optimization
is dynamically optimal iff its root holdings satisfy the root lines with its own tomorrow
multipliers; the two signs of the difference, hoarding cash against tomorrow's binding budget
and front-loading a purchase ahead of it, are explicit (part 3). Which band and separation
results survive is stated in part 4. The model is M7's finite-law variant with N = M = K = 1
and T = 2, the funded budget not assumed slack; D17's worked instance is this instance, and no
new model version is needed (mathb told).

**Setting.** An M7 instance (`model/SPEC.md` M7, finite-law variant): one fund (holding a,
index A) and one ETF (holding p, index E), x = (a, p), cash h; reviews t = 0, 1 and marking at 2;
public state z_1 = z' tomorrow with finite law q(z' | z_0) and gross returns g(z') = (g_A, g_E) > 0;
predictive moments (mu_0, Sigma_0) today and (mu_1(z'), Sigma_1(z')) tomorrow, Sigma positive
definite; gamma > 0; discount beta in (0, 1]; directional rates kappa^+_i, kappa^-_i in [0, 1);
caps 0 <= x <= bar x (bar x_E may be +infinity); incumbents x^-_0 = (a^-, p^-) and cash h^-_0 > 0;
trades u_0 = x_0 - x^-_0 and u_1(z') = x_1(z') - g(z') o x_0; cost C(u) = sum_i [kappa^+_i u_i^+ +
kappa^-_i u_i^-]; cash after trading h^+_0 = h^-_0 - 1'u_0 - C(u_0) >= 0 and h^+_1(z') = h^+_0 -
1'u_1(z') - C(u_1(z')) >= 0 (the funded budget at both reviews; cash earns nothing). The objective
is Q_0(x_0) - C(u_0) + beta sum_{z'} q(z') [Q_1(x_1(z'); z') - C(u_1(z'))] with Q_t(x) = mu_t' x -
(gamma/2) x' Sigma_t x, maximized over x_0 and the family {x_1(z')}. Write g_{t,i} = (mu_t - gamma
Sigma_t x_t)_i for the smooth marginals and T_i(x; x^-) for claim 102's trade-sign slope sets.
The *repeated one-review policy* (myopic) solves claim 110's one-review problem today from
(x^-_0, h^-_0) and, in each state tomorrow, from (g(z') o x_0, h^+_0).

1. **Structure.** An optimal policy exists; the problem is a concave maximization of a finite
   sum over a polyhedron in (x_0, {x_1(z')}); the last review's value V_1(x^-, h^-; z') is concave
   in (x^-, h^-) and nondecreasing in h^-; and the root problem max_{x_0} Q_0(x_0) - C(u_0) +
   beta E V_1(g o x_0, h^+_0(x_0); z') is a concave maximization over a polyhedron.

2. **The root lines (exact).** x_0 with {x_1(z')} is optimal iff there are multipliers eta_0 >= 0
   with eta_0 h^+_0 = 0, eta_1(z') >= 0 with eta_1(z') h^+_1(z') = 0, and slopes t_0 in T(x_0; x^-_0),
   t_1(z') in T(x_1(z'); g(z') o x_0) such that tomorrow's lines hold in every state,

   ```
   g_{1,i}(x_1(z')) - eta_1(z') - (1 + eta_1(z')) t_{1,i}(z')   = 0 if 0 < x_{1,i} < bar x_i,  <= 0 at x_{1,i} = 0,  >= 0 at x_{1,i} = bar x_i
   ```

   (claim 110's part 1 at each state), and today's lines hold with the *dynamic cash price* and
   the *incumbent values*

   ```
   eta_hat_0 = eta_0 + beta sum_{z'} q(z') eta_1(z'),
   S_i = beta sum_{z'} q(z') g_i(z') s_i(z'),      s_i(z') = eta_1(z') + (1 + eta_1(z')) t_{1,i}(z'),
   g_{0,i}(x_0) + S_i - eta_hat_0 - (1 + eta_hat_0) t_{0,i}   = 0 if 0 < x_{0,i} < bar x_i,  <= 0 at x_{0,i} = 0,  >= 0 at x_{0,i} = bar x_i,
   ```

   with the same t_1(z') in both sets of lines. Read from tomorrow's regimes, the incumbent
   value s_i(z') of a unit of instrument i carried into state z' is

   ```
   g_{1,i}(x_1(z'))                    if the instrument is held strictly inside its box tomorrow (its marginal score),
   eta_1(z') + (1 + eta_1(z')) kappa^+_i   if bought tomorrow (its scaled purchase threshold; also when bought to the cap),
   eta_1(z') - (1 + eta_1(z')) kappa^-_i   if sold tomorrow (its scaled sale threshold; also when sold out),
   ```

   and lies in the interval between the two thresholds cut by tomorrow's one-sided line when
   held at zero or at the cap. So today's decision is claim 110's one-review rule with alpha~_i
   replaced by alpha~_i + S_i (the fund's incumbent value added to its net alpha, the ETF's to its
   premium) and eta replaced by eta_hat_0: the one-ETF two-scalar reduction holds at the root.

3. **The binding budget's contribution, and myopic optimality.**
   (a) *Slack budget tomorrow.* If h^+_1(z') > 0 in every state then eta_1 = 0, eta_hat_0 = eta_0 and
       s_i(z') = t_{1,i}(z') in [-kappa^-_i, kappa^+_i]: the root lines are claim 029's edge brackets
       (with the marking factors and beta) and claim 102 part 5(a)'s scaling by today's
       multiplier. The binding budget's whole contribution is therefore the eta_1 terms: a
       uniform rise beta E eta_1 of every purchase threshold and fall of every sale threshold today,
       and the factor (1 + eta_1(z')) on tomorrow's slopes inside the incumbent values.
   (b) *Bounds in the inputs.* S_i lies in [beta E[g_i (eta_1 - (1 + eta_1) kappa^-_i)], beta E[g_i (eta_1 +
       (1 + eta_1) kappa^+_i)]], so fund i is bought today only if g_{0,i}(x_0) >= eta_hat_0 + (1 +
       eta_hat_0) kappa^+_i - beta E[g_i (eta_1 + (1 + eta_1) kappa^+_i)] and sold only if g_{0,i}(x_0) <=
       eta_hat_0 - (1 + eta_hat_0) kappa^-_i - beta E[g_i (eta_1 - (1 + eta_1) kappa^-_i)] (weak
       inequalities: equality occurs when every state tomorrow trades the instrument the same way,
       so that S_i sits at the end of its interval; lean's point), the
       expectations over tomorrow's cash-price law; with eta_1 = 0 these are claim 029's.
   (c) *Myopic optimality.* The repeated one-review policy is dynamically optimal iff its root
       holdings x^my_0 satisfy the root lines of part 2 for *some* (eta_1(z'), t_1(z')) in the
       multiplier and slope sets of its own tomorrow problems (which are optimal given x^my_0)
       and some eta_0 >= 0 (zero if h^+_0(x^my_0) > 0) and t_0 admissible at x^my_0. Tomorrow's
       multiplier set is a singleton when the state trades some instrument strictly inside its
       box (that line pins eta_1(z')), and an interval when h^+_0(x^my_0) = 0 and the state trades
       nothing, or when every traded instrument is at a bound; the slope set is a singleton or the
       sub-interval of part 2's reading. This is an explicit test in the inputs once tomorrow's
       one-review problems are solved (claim 110's two scalars per state), and the quantifier
       matters: red found instances where the myopic policy is optimal while the test fails at
       one solver's multipliers and passes at another's. *The exact slack-tomorrow condition.*
       If h^+_1(z') > 0 in every state, then eta_1 = 0 and the test reads: for every instrument i,
       with tomorrow's slopes t_{1,i}(z') and some admissible t_{0,i},

       ```
       g_{0,i}(x^my_0) + beta E[g_i t_{1,i}] - eta_0 - (1 + eta_0) t_{0,i}   = 0 if x^my_{0,i} is strictly inside its box,  <= 0 at zero,  >= 0 at the cap;
       ```

       so, with today's budget slack at x^my_0 (eta_0 = 0 in both lines), an instrument traded
       strictly inside its box today needs beta E[g_i t_{1,i}] = 0 exactly (its line is an equality;
       a purchase today with some state buying it again tomorrow is never myopically optimal
       when no state sells it and no state holds it strictly inside its box with a negative
       marginal, since the states' terms q g_i t_{1,i} are then all nonnegative with one positive;
       otherwise the terms can cancel and the equation holds only on a knife edge), while with today's budget binding (h^+_0(x^my_0) = 0) the test's eta_0 is free and
       the traded instruments need beta E[g_i t_{1,i}] = (eta_0 - eta^my_0)(1 + kappa^+_i) for a
       purchase (1 - kappa^-_i for a sale) with one common eta_0 >= 0, which a single such
       instrument does not force to zero (lean's qualification; claim 046 part 3 states the
       binding case); and one held today needs g_{0,i} + beta E[g_i t_{1,i}] inside its
       scaled band [eta_0 - (1 + eta_0) kappa^-_i, eta_0 + (1 + eta_0) kappa^+_i] (claim 029's edge
       brackets, and claim 036's rule that costless instruments never anticipate, since their
       t_1 = 0). *The two signs.* Suppose today's budget is slack at x^my_0 (h^+_0(x^my_0) > 0) and
       the myopic root buys instrument i strictly inside its box. Write, for a choice of
       tomorrow's admissible multipliers and slopes,

       ```
       r_i = S_i - beta E[eta_1] (1 + kappa^+_i)   =   beta ( E[g_i s_i(z')] - E[eta_1] (1 + kappa^+_i) ),
       ```

       the instrument's expected marked incumbent value against tomorrow's expected cash price
       at the purchase scale. Then the root objective lies below the line of slope r_i through
       x^my_0 along instrument i, in both directions, for every admissible choice: its one-sided
       derivative along the purchase is at most r_i and along the sale at most -r_i; under unique
       tomorrow multipliers (the singleton case) the purchase derivative equals r_i, and in
       general it is the minimum of r_i over the admissible choices (the directional derivative
       of the concave V_1, lean's point). Hence a negative r_i for some admissible choice makes
       the purchase direction descend (the hoarding sign), a positive r_i for every admissible
       choice makes it ascend (the front-loading sign), and in either case the myopic purchase is
       not dynamically optimal, optimality needing some choice at which r_i vanishes (in a state
       with all cash spent today and the instrument idle inside its box tomorrow, both eta_1 = 0
       and a positive eta_1 can be admissible, giving different values).
       Reading: the sign gives the direction in which the dynamic policy would move instrument i
       *with the other instrument's holding fixed* (the one-dimensional comparative static of a
       concave function): negative is *hoarding* (less of i today, keeping cash for tomorrow's
       binding budget), positive *front-loading* (more of i ahead of tomorrow's dear cash); when
       the instrument is held strictly inside its box tomorrow in every state the sign is that
       of E[g_i g_{1,i}] - E[eta_1](1 + kappa^+_i). With both holdings free the joint move can reverse
       by substitution: the dynamic policy may move the other instrument the opposite way by
       more, through Sigma_AE and the shared budget, so that instrument i's own holding goes
       against its sign (the analyst's experiment 047: 12 of 82 cases, one of them with no binding
       budget at either review, the claim 029 cost channel alone; an instance report, rule 22).
       Claim 046 part 4 (the refile of refuted claim 045, in review) proves the comparative static in the one-dimensional case, a
       frictionless ETF held interior, with the residual evaluated at the ETF re-optimized at
       the myopic fund holding. The two signs are claims 012-013's opposite continuation effects,
       here attributed to the budget.

4. **What survives a binding budget.** (a) Claim 110's two-scalar rule at both reviews, at the
   root with (alpha~_i + S_i, eta_hat_0). (b) Claim 029's band at every review: today's no-trade
   interval per instrument is the one-review band in the marginal g_{0,i} + S_i with the
   thresholds scaled by (1 + eta_hat_0), of width (1 + eta_hat_0)(kappa^+_i + kappa^-_i) in the marginal
   at fixed S_i and eta_hat_0; with a slack budget today, E V_1 is concave in x_0 (part 1), so the
   continuation adds a nonpositive slope to the marginal and the no-trade interval in holdings
   is *at most* that width over gamma times the instrument's curvature (claim 107's residual
   ceiling times (1 + eta_hat_0) after the other instrument is optimized out); with a binding
   budget today the conversion is Not shown. (c) The separation results at the last review
   verbatim (claims 104, 111 at each state); at the root only in the modified one-review
   problem of (a), so exposure-first implementation at the root is exact under claim 111's
   condition applied to that problem (a reading, not proved here). (d) Claim 036's rule that
   costless instruments never anticipate: an instrument with kappa^+_i = kappa^-_i = 0 has S_i =
   beta E[g_i eta_1] and its line reads g_{0,i} = eta_hat_0 - beta E[g_i eta_1]; it still anticipates
   the budget, through the cash price alone.

**One sentence without model nouns.** When money will be tight at the next review, today's
decision is the usual one-review rule with two changes: every threshold moves by the expected
price of cash tomorrow, and each position's expected return is credited with what a unit of it
will be worth to tomorrow's problem, its marginal value if kept, the price of buying it if it
will be bought, the proceeds of selling it if it will be sold; repeating the one-review rule is
right exactly when its choice already meets these adjusted lines, and otherwise it buys too
much of what tomorrow will want to sell, or too little of what tomorrow will want to buy.

## Proof

### 1. Structure

Lift the costs: write u^+_0, u^-_0 >= 0 with u_0 = u^+_0 - u^-_0 and likewise u^+_1(z'), u^-_1(z'); the
objective with C replaced by sum_i [kappa^+_i u^+_i + kappa^-_i u^-_i] is concave (quadratics with
positive definite Sigma, minus linear costs), and at any optimum of the lifted problem no
coordinate has both u^+_i and u^-_i positive (reducing both by the same amount raises the
objective and relaxes the cash constraints), so the lifted and the original problems have the
same value and optima. The constraints are the boxes, the marking identities (linear in x_0
for each z'), and the cash constraints h^+_0 >= 0, h^+_1(z') >= 0, all linear in the lifted
variables: a polyhedron; nonempty (no trade is feasible from x^-_0 with h^-_0 > 0) and bounded
(caps on the fund; the ETF bounded by cash if uncapped, since each purchase costs at least one
unit of cash and cash is finite), so an optimum exists. V_1(x^-, h^-; z') = max {Q_1(x) - C(x - x^-) :
0 <= x <= bar x, h^- - 1'(x - x^-) - C(x - x^-) >= 0} is the partial maximum of a function jointly
concave in (x, x^-, h^-) (C convex in x - x^-) over a jointly convex set, hence concave; a larger
h^- enlarges the feasible set, hence V_1 is nondecreasing in h^-. The root objective is Q_0 - C
plus beta E V_1(g o x_0, h^+_0(x_0)), with g o x_0 linear and h^+_0 concave in x_0 and V_1
nondecreasing in its cash argument, so it is concave, and the root's feasible set is the
polyhedron {0 <= x_0 <= bar x, h^+_0(x_0) >= 0}.

### 2. The root lines

Apply AX-13 (the polyhedral KKT theorem; the objective is finite on R^n, so the qualification
holds, as in claims 102 and 104, whose lifting of the piecewise-linear cost to a smooth concave
program over a polyhedron, claim 104 part 0, is the one used here) to the lifted joint problem, with multipliers eta_0 for h^+_0 >= 0,
beta q(z') eta_1(z') for h^+_1(z') >= 0 (normalized so that eta_1(z') is the state's own cash
price), and box multipliers. Eliminating the lifted variables as in claim 102 part 1 gives, for
each state, the stationarity of the Lagrangian in x_1(z'): g_{1,i} - eta_1 - (1 + eta_1) t_{1,i} in the
box's normal cone, with t_{1,i}(z') the cost slope of u_1(z') (the subgradient of C at the state's
trade, a point of T_i(x_1(z'); g(z') o x_0)); these are tomorrow's lines. Stationarity in x_{0,i}
collects the terms of the Lagrangian that contain x_{0,i}: from Q_0 - C(u_0), g_{0,i} - t_{0,i}; from
eta_0 h^+_0, -eta_0 (1 + t_{0,i}); from each state, beta q(z') times the sum of [-C(u_1(z'))]'s
derivative through u_1 = x_1 - g o x_0, which is +g_i t_{1,i}, and of eta_1(z') times the derivative of
h^+_1(z') = h^+_0(x_0) - 1'u_1 - C(u_1), which is -(1 + t_{0,i}) + g_i + g_i t_{1,i}. Summing, the x_{0,i}
line is g_{0,i} - t_{0,i} - eta_0 (1 + t_{0,i}) + beta sum q(z') [g_i t_{1,i} + eta_1 (g_i (1 + t_{1,i}) - (1 + t_{0,i}))]
= g_{0,i} - eta_hat_0 - (1 + eta_hat_0) t_{0,i} + beta sum q(z') g_i [eta_1 + (1 + eta_1) t_{1,i}] in the
box's normal cone, the display, with the same t_{1,i}(z') as in tomorrow's line (the cost term
C(u_1(z')) has one subgradient in the Lagrangian). The readings of s_i(z'): for an instrument
held strictly inside its box tomorrow, tomorrow's line is an equality, eta_1 + (1 + eta_1) t_{1,i} =
g_{1,i}; for one bought (t_{1,i} = kappa^+_i) or sold (t_{1,i} = -kappa^-_i), including to the cap or to
zero, the slope is the rate; for one held at zero or at the cap, tomorrow's one-sided line
restricts t_{1,i} to the stated sub-interval of [-kappa^-_i, kappa^+_i]. Sufficiency and necessity
are AX-13's two directions for the lifted concave program.

### 3. Consequences

(a) With eta_1 = 0 the displays reduce as stated; claim 029's brackets are its part 1c with the
marking factor g_i and the discount. (b) The bounds are the extreme values of s_i(z') over
T_i, multiplied by beta q(z') g_i(z') > 0 and summed; a purchase today has t_{0,i} = kappa^+_i and
the line = 0 (interior) or >= 0 (to the cap), which with S_i at most its upper bound gives the
necessary condition; the sale case is the mirror. (c) The myopic policy's tomorrow problems
are claim 110's one-review problems from (g(z') o x^my_0, h^+_0(x^my_0)), whose optima are
tomorrow's optima given x^my_0; by part 2 (an existence statement over the multipliers) the
whole policy is optimal iff the root lines hold at x^my_0 for some multipliers and slopes in the
sets that tomorrow's lines admit, and some eta_0, t_0: hence the quantifier. Tomorrow's line
for an instrument traded strictly inside its box is an equality in eta_1(z') with the slope
pinned at the rate, so it determines eta_1(z'); if no instrument is traded interior and
h^+_1(z') = 0 (which requires h^+_0(x^my_0) = 0 when nothing trades), every eta_1(z') in the
interval cut by the held instruments' one-sided lines is admissible. The slack-tomorrow
condition is the test with eta_1 = 0 written out, the interior-trade case being an equality and
the held case a two-sided inequality. The sign: with h^+_0(x^my_0) > 0, eta_0 = 0 in both the
myopic and the dynamic root lines; the myopic line for a purchase strictly inside the box reads
g_{0,i} - kappa^+_i = 0, so the root objective's one-sided derivative in the purchase direction at
x^my_0 is S_i - beta E[eta_1](1 + kappa^+_i) (the root objective is concave, with the
continuation's one-sided derivative given by the incumbent values and the cash price, part 2's
computation at the myopic tomorrow solutions); a nonzero value means x^my_0 does not satisfy the
root's first-order condition in that coordinate, so it is not the dynamic optimum. The
direction of the dynamic optimum's fund coordinate is not inferred from this derivative (a
reading, as stated).
(d) is a reading of part 2, and the surviving band is the root line read as an interval in
g_{0,i} + S_i with the scaled thresholds; in holdings, with a slack budget today, the root
objective is the concave sum of the quadratic score, the cost and beta E V_1 (concave by part
1), so its marginal along instrument i falls at least as fast as the score's alone, -gamma
Sigma_ii (or the residual curvature after the other instrument is optimized out), which bounds
the no-trade interval's width by the marginal band's width over that curvature.

## Checks

`checks/044/check.py` (cvxpy/CLARABEL on the joint program, the multipliers from the duals;
rule 22; floating point). (i) Part 2's root lines hold at 40 dynamic optima on random
instances (a fund costing more than the ETF, three states tomorrow, a tight budget in 31 of
them), with tomorrow's slopes pinned by tomorrow's own lines. (ii) Part 3(c): on 40 instances,
the myopic policy is dynamically optimal in 17 and not in 23, and the root-line test at the
solver's tomorrow multipliers agrees in 38; the exceptions are of the shape red found (all cash
spent today, a state trading nothing tomorrow, the multiplier non-unique), where the test's
quantifier over the multiplier set matters. (iii) Part 3(a):
with a slack budget the multipliers vanish and the incumbent values lie in claim 029's bracket.
(iv) Illustration: over 60 tight-budget instances the dynamic policy holds less of the fund
than myopic today in 12 (hoarding), more in 15 (front-loading), the same in 33.

## Not shown

- More than two reviews (the same lifted program, with the incumbent values compounding
  through the later reviews' multipliers; the finite-law tree grows).
- The Gaussian law (M5's): the finite-law program is what AX-13 covers; D17 states the
  transfer question.
- Explicit closed forms for tomorrow's multipliers eta_1(z') in the inputs (claim 110 gives them
  as roots of monotone scalar equations per state, which is the explicit form used here).
- The band's width in holdings under a binding budget today (4(b) gives "at most" under a slack
  budget); the root's separation statement (4(c)) beyond the reading.
- The joint comparative static in 3(c) (only the one-sided derivative's sign, and the
  one-instrument direction with the other holding fixed, are proved; claim 045 part 4 proves
  the frictionless-ETF case). Target, not claimed: under the hypothesis that the other
  instrument's root line holds at the myopic point and the root objective is locally quadratic
  there with Hessian H, the joint move of instrument i has the sign of -(H^{-1})_{ii} times its
  residual plus the cross term from the other instrument's residual, which fixes the sign when
  the latter vanishes (red's candidate).
- Many funds (out of scope; the lines extend verbatim, the interactions being claim 110's).

## Prior art

Mechanism: the two-review problem is one concave program over a polyhedron, so its
optimality conditions are the polyhedral KKT conditions of the lifted problem; the
continuation enters today's lines through exactly two numbers per instrument, the discounted
expected cash price and the discounted expected marked incumbent value, the latter pinned by
tomorrow's own lines.

General results checked: AX-13 (`rockafellar1970convex`) through claims 102 and 104; claim 110
(the one-review two-scalar rule with a binding budget, used at each review); claim 029 (the
band and its edge brackets with beta and the marking factors, the slack-budget case); claim 102
part 5(a) (the budget scaling); claims 011-013 (M3's continuation channels with both signs; the
present lines put both signs in the inputs); claim 036 (costless instruments never anticipate,
now qualified by the cash price); claim 100 (the learning path); `garleanu2009dynamic` and
`garleanu2016dynamic` (named: the quadratic-cost dynamic policy has no budget and no band;
its aim-portfolio structure is D12's, not used here); `liu2013portfolio` (named: a binding
portfolio constraint's shadow price in the small-cost expansion, the continuous-time
counterpart of eta_1).

Searched: claims 011-013, 029, 036, 100, 102, 104, 107-111; M3, M6, M7 in SPEC; ROADMAP D16-D18;
LAB_REQUEST. This is a claim because the request asks for usable conditions on how the second
review changes today's decision under a binding budget, and the dynamic cash price and the
incumbent values, with the myopic-optimality test and the two signs, are stated by no claim.

## Open objections

The auditor's FIDELITY row (2026-09-29): the formal statement matches; its three prose points
are made here (the "= 0" statement with today's slack budget; "never myopically optimal" with
no state selling and no state holding with a negative marginal, else a knife edge; the
comparative-static reference moved from refuted 045 to claim 046). Lean's second formalization
note (2026-09-29, the slack-tomorrow readings): the "= 0 exactly"
statement is qualified by today's slack budget, with the binding form stated; "never myopically
optimal" needs no state selling the instrument; the sign statement now says what is proved,
the root objective below the line of slope r_i in both directions for every admissible choice,
with equality under unique multipliers and the minimum over choices in general. Lean's
formalization note (2026-09-29): the sign test in 3(c) is conclusive only when the
residual is nonzero for every admissible choice of tomorrow's multipliers and slopes (its
"for some" quantifier and the two-instrument restriction of the reading were already made).
PM's note after approval (2026-09-29, experiment 047): 3(c)'s reading of the sign as the direction
of instrument i's move is restricted to the other holding fixed, the joint move being reversible
by substitution through Sigma_AE and the shared budget (12 of 82 cases; one with no binding
budget); Not shown carries the joint comparative static as a target. The model is M8's instance
(mathb's D17 model on main), which is M7's instance by construction; the statement keeps M7.
Red's review (b51a82dc, red-passed): the four required corrections are made: 3(c)'s test
quantifies over tomorrow's multiplier and slope sets (with the singleton and interval cases
named); the sign statement carries the hypothesis that today's budget is slack and states what
is proved, the sign of the root objective's one-sided derivative along the purchase, with
"buys less/more" a reading; the "in particular" sentence is replaced by the exact
slack-tomorrow condition; 4(b)'s holdings width is "at most" under a slack budget today and Not
shown otherwise. Lean's scoping point (2026-09-29, before red's verdict): part 3(b)'s necessary conditions are weak
inequalities, with equality when every state tomorrow trades the instrument the same way. PM's
note (same day): depends_on adds claim 104, whose lifting to AX-13 the formal necessity of part
2 reuses. Earlier: none. Red should test: the elimination of the lifted variables in the joint program
(the single subgradient t_1(z') appearing in both lines); the normalization of eta_1(z'); part
3(c)'s sign argument when today's budget also binds (eta_0 > 0 may differ between the myopic and
the dynamic root); and the ETF uncapped case's boundedness.

## Review

**Red, 2026-09-29** (on 3f485c04). Red-passed, with four required corrections: three in part 3(c), one in part 4(b). Red re-derived parts 1 and 2 by hand and tested parts 2 and 3(c) with its own solver, written without reading checks/044. The solver is the lifted joint program in cvxpy/CLARABEL, bp-scaled, with:
- one capped fund and one uncapped ETF, directional rates, three states tomorrow with marking factors and moved moments, and beta = 0.97;
- the budget as a constraint at each review, with eta_0 its dual and eta_1(z') the state's dual divided by beta q(z');
- a tight budget on most instances (300 instances: 187 binding tomorrow, 139 today).

**Part 1** is right by hand. The lifting is claim 104 part 0's, V_1 is a partial maximum of a jointly concave function over a jointly convex set, and it is nondecreasing in cash. Boundedness with an uncapped ETF holds: each unit bought costs at least one unit of cash, and cash plus the fund's sale proceeds is bounded at both reviews.

**Part 2** (the objection list's elimination and normalization). At the 177 optima whose incumbent values are pinned (no instrument held at a bound tomorrow), today's lines hold with S_i and eta_hat_0 read from tomorrow's regimes. The maximum residual is 4.4e-13, and every held instrument lies in its scaled band. The normalization eta_1 = dual/(beta q) and the single t_1(z') in both lines are therefore right, and so is the collection of the x_{0,i} terms, which red redid by hand. A purchase to the cap or a sale to zero is one-sided, as the display says.

**Part 3(a)** is right by hand. **3(b)** is right in its weak form (lean's point, already made on this branch).

**Required correction 1 (3(c), the "iff": tomorrow's multipliers are not unique).** The test "with (eta_1(z'), t_1(z')) the multipliers and slopes of its own tomorrow problems" fails its "only if" direction when those multipliers are not unique.
- This happens when the myopic root spends all cash today (h^+_0(x^my_0) = 0) and a state trades nothing tomorrow. Tomorrow's lines then hold for every eta_1(z') in an interval, and the solver returns one point of it.
- Of 210 testable instances, red's test (eta_0 free, >= 0 when today binds) agrees with myopic optimality at 207. The 3 exceptions (red's seeds 66, 133 and 258) all have that shape: myopic is optimal (identical holdings to the joint optimum), yet the test fails at the myopic solves' multipliers.
  - At seed 66, the myopic solves give eta_1 = (1.47e-3, 1.42e-3, 5.2e-4) and the joint optimum gives (6.5e-4, 3.1e-4, 4.5e-4). Both are valid multipliers of the same tomorrow problems.
  - At all three seeds, the test passes with the joint optimum's multipliers.
- Part 2 is an existence statement, so the fix is one quantifier: "for some (eta_1(z'), t_1(z')) in the multiplier and slope sets of its own tomorrow problems". Please say when these sets are singletons (a state that trades an instrument interior pins eta_1(z')) and when they are intervals (h^+_0 = 0 with no trade, or an instrument held at a bound, which the part 2 reading already covers for t_1). The Checks' "(the rest within solver resolution)" in (ii) may be this case; please check.

**Required correction 2 (3(c), the two signs).** Two separate problems:
- *A missing hypothesis.* The statement's "the dynamic policy buys less / buys more" does not say today's budget is slack at x^my_0. The proof uses that hypothesis ("the budget slack today"). This is the objection list's own question, and the answer is that the sign argument needs it. Please put it in the statement.
- *A precise gap in the proof.* "A negative residual means the concave root objective decreases in x_{0,i} at x^my_0 along the purchase direction, so the optimum has a smaller purchase" infers the coordinate of a multivariate maximizer from one partial derivative. That is false monotonicity for concave functions in general.
  - Abstract counterexample: f(a, e) = -(a - e)^2 - (e - 1)^2 - epsilon a has df/da = -epsilon < 0 at (0, 0), but its maximizer has a = 1 - epsilon > 0.
  - In the root program, the ETF's root line generally fails at x^my_0 too. Moving the ETF then shifts the fund's marginal by -gamma Sigma_AE Delta e. For a locally quadratic root, Delta a is proportional to Sigma_EE r_A - Sigma_AE r_E, not to r_A.
  - Red's random search found no reversal: 74 sign cases over two bounded runs (the second with fund-ETF correlation 0.9-0.98), 0 mismatches. Rule 22: that does not settle it.
- Please either state what is proved (the sign of the root objective's one-sided derivative along instrument i's purchase at x^my_0, with "buys less/more" as a reading), or prove the comparative static under a stated hypothesis. One candidate: the other instrument's root line holds at x^my_0 and the root objective is locally quadratic there, where -(H^{-1})_{ii} > 0 gives the sign.

**Required correction 3 (3(c), "in particular it is optimal whenever ...").** "Tomorrow's budget is slack in every state and every instrument's incumbent value keeps its myopic line's sign" is not a condition red can check, and on its natural reading it is false.
- With eta_1 = 0, an instrument traded interior today needs S_i = beta E[g_i t_{1,i}] = 0 exactly (its root line is an equality), and a held one needs g_{0,i} + S_i in its scaled band.
- A fund bought interior today with S_i > 0 small (some state buys it tomorrow) keeps every sign, and myopic is not optimal.
- Please replace the sentence with the exact slack-tomorrow condition (part 2's lines with eta_hat_0 = eta_0 at x^my_0), or cite the precise statements of claims 029 and 036 it means.

**Correction to part 4(b) (required, small).** "In holdings its width is that over gamma times the instrument's curvature" converts the marginal band at a fixed S_i and eta_hat_0. Both move with x_0: S_i moves through tomorrow's regimes and marked holdings. With a slack budget today, E V_1 is concave in x_0, so the continuation adds a nonpositive slope and the holdings width is *at most* the stated one. Please write "at most" (slack today), or move the holdings width to Not shown, which already names "beyond the reading in part 4(b)".

**Parts 4(a), (c) and (d)** are right as readings of part 2. 4(d) checked by hand: kappa = 0 gives s_i = eta_1, so S_i = beta E[g_i eta_1].

**Mechanism.** The joint program is one concave program over a polyhedron (AX-13 via claim 104's lifting). Today's lines differ from claim 110's by two numbers per instrument: the dynamic cash price, and the incumbent value pinned by tomorrow's own regime.

Verdict: red-passed


**Red, recheck of the four required corrections (0be177ee), 2026-09-29.** All four are made correctly, and red checked each by hand.
- **3(c)'s test** quantifies over tomorrow's multiplier and slope sets. The singleton case (a state trading some instrument strictly inside its box) and the interval cases (all cash spent today with no trade, or every traded instrument at a bound) are right.
- **The exact slack-tomorrow condition** is part 2 with eta_1 = 0 and S_i = beta E[g_i t_{1,i}].
- **The sign statement** now carries today's slack budget (eta_0 = 0 at x^my_0) and states only the one-sided derivative S_i - beta E[eta_1](1 + kappa^+_i), with "buys less/more" a reading. Experiment 047's 12 of 82 substitution cases fit this, since there the ETF moves the fund through Sigma_AE.
- **4(b)'s "at most"** follows from E V_1's concavity in x_0 under a slack budget today.

Two nits (not required):
- "A purchase today with some state buying it again tomorrow is never myopically optimal" is slightly too strong. With eta_1 = 0, a state holding the instrument strictly inside its box tomorrow contributes t_{1,i} = g_{1,i}, which can be negative. So beta E[g_i t_{1,i}] = 0 can hold on a knife edge. "Generically not" is exact.
- Where S_i is not pinned (an instrument held at a bound tomorrow), the one-sided derivative in the purchase direction is the smallest value of S_i - beta E[eta_1](1 + kappa^+_i) over the admissible slopes (the concave directional derivative), not one value.

No result changed. The approval stands.

## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: parts 1-2 re-derived by hand (claim 104's lifting to AX-13, V_1 concave and nondecreasing in cash, boundedness with an uncapped ETF) and part 2's lines tested on red's own lifted solver at 177 pinned optima to 4.4e-13, with the normalization of eta_1 and the single t_1 confirmed; the four required corrections are made in 0be177ee exactly as red asked ('some' multipliers, with the singleton and interval cases; the sign rule under a slack budget today, stated as the one-sided derivative, with buy less/more a reading; the exact slack-tomorrow condition; 4(b) 'at most'); 3(b) weak (lean); depends_on adds 104. Mechanism: the two-review program's polyhedral KKT (AX-13) puts the continuation into today's lines through two numbers per instrument, the dynamic cash price and the pinned incumbent value, an application; new in the inputs, beyond Hakansson's qualitative failure: that channel and the myopic-optimality test, so D16's kill criterion is not met. Limits: one fund, one ETF; the comparative-static sign is a reading; red records its recheck line.


Not machine checked. A finite concave program's KKT conditions, algebra of the Lagrangian's
partial derivatives, and readings.

Lean, 2026-09-29 (final): parts 1, 2, 3(a)-(c), 4(a), 4(b) and 4(d) are machine checked, within the
limits below. The statement is in `lean/Standalone/M7TwoReviewsBindingBudget.lean` and the proof in
`lean/Novel/M7TwoReviewsBindingBudgetProof.lean`.
- Model: the claim's own two-review coordinates (`Two`), stated for any finite instrument set (the
  claim's case has two instruments) and a finite state set tomorrow. The hypotheses are weaker than
  the claim's:
  - each Sigma only needs to be symmetric positive semidefinite;
  - q > 0 need not sum to one;
  - the caps are finite; the uncapped ETF is paper-level (PM).
- Imports: claim 104's statement (its `AX13`) and proof module (Q-04; 104 is in depends_on). The
  two-review lifting of the costs follows claim 104's part 0 and is proved here, since claim 104's
  lifting is for one review (PM's fallback).
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/044/check.py` pass.
- Scope: PM's scope note (option (i) for AX-13, finite caps).

Machine checked:
- Part 1:
  - an optimal policy exists;
  - J is concave on the (convex) feasible set;
  - V_1 is concave on its domain and nondecreasing in cash;
  - every root-feasible x_0 carries into that domain;
  - the root objective is concave on the root polyhedron.
- Part 2:
  - sufficiency: a feasible policy satisfying the lines is optimal. This is proved directly by a
    Lagrangian bound, with no citation;
  - necessity: an optimal policy satisfies the lines, with one t_1(z) in both sets, conditional on
    AX-13;
  - the readings of s_i(z): tomorrow's marginal strictly inside the box, the scaled thresholds
    after a purchase or sale, always between them, and cut by the one-sided line at zero or at the
    cap.
- Part 3:
  - (a) slack tomorrow gives eta_1 = 0, eta_hat_0 = eta_0 and s_i = t_{1,i}, with S_i's bracket;
  - (b) S_i's bounds and the weak purchase and sale conditions;
  - (c) the test: under AX-13, the myopic policy is optimal iff the root lines hold for some
    multipliers and slopes of its own tomorrow problems and some admissible eta_0 and t_0;
  - (c) the pinned multiplier: any two multiplier sets agree in a state that trades some
    instrument strictly inside its box;
  - (c) the exact slack-tomorrow condition, and the held-today band;
  - (c) beta E[g_i t_{1,i}] = 0 for an instrument traded strictly inside its box today, with today's
    budget slack as well;
  - (c) the myopic line g_{0,i} = kappa^+_i (or -kappa^-_i after a sale), and the residual identity;
  - (c) the two signs as tangent bounds, with today's budget slack and a myopic purchase strictly
    inside the box, for any multipliers of the myopic tomorrow problems. Along instrument i, with the
    other holdings fixed, the root objective lies below the line of slope
    r = S_i - beta E[eta_1](1 + kappa^+_i) through the myopic root, in both directions. So its
    one-sided derivative along the purchase direction is at most r, and along the sale direction at
    most -r. For r < 0 no larger purchase raises it; for r > 0 no smaller one does.
- Part 4:
  - (a) each review's holdings maximize that review's one-review Lagrangian: at the root with
    (mu_0 + S, eta_hat_0), and tomorrow at eta_1(z) from the carried holdings;
  - (b) the band in the marginal g_{0,i} + S_i, of width (1 + eta_hat_0)(kappa^+_i + kappa^-_i), and the
    marginal's slope -gamma Sigma_{0,ii} along the coordinate;
  - (d) the costless instrument's S_i and line.

Paper-level:
- in 3(c):
  - the exact value of the one-sided derivative (equality with r, which with non-unique tomorrow
    multipliers depends on the choice);
  - strict improvement in the opposite direction;
  - the interval case of the multiplier set;
  - the joint comparative static (Not shown);
- 4(b)'s "at most" width in holdings under a slack budget today;
- 4(a)'s link to claim 110's `One` coordinates;
- 4(c), the uncapped ETF and the Checks.
- Two readings in 3(c) are formal only with an added hypothesis or a weaker conclusion (note to math
  and red):
  - "needs beta E[g_i t_{1,i}] = 0 exactly" is proved with today's budget slack. When
    h^+_0(x^my_0) = 0, the test's eta_0 need not equal the myopic one;
  - "a purchase today with some state buying it again tomorrow is never myopically optimal" does not
    follow when another state sells it.

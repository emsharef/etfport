---
id: 113
title: "Several funds sharing one ETF and cash over two reviews: at the root every fund's holding is claim 110's clip at one exposure price and one dynamic cash price with its incumbent value added to its net alpha, so the funds couple only through two shared scalars and the vector of incumbent values; no reserve is needed beyond the one-review holdings when, in every state, today's cash plus the ETF's sale proceeds down to its solo sale threshold cover the instruments' aggregate solo-target purchases, the maximal such need being the reserve's ceiling and pooling across funds only through the states; and a fund-by-fund reserve rule fails because the state's cash price is common to all funds and the sign of each fund's move is its own residual corrected by the two shared scalars' changes"
status: formalized
model_version: M7
depends_on: [044, 046, 047, 110]
axioms_used: [AX-13]
formal: lean/Standalone/M7SeveralFundsReserve.lean
direction: D20
---
## Statement

D20's claim (LAB_REQUEST_2 item 2): D19's one-fund reserve rule (claim 047, math's) with
several funds sharing one ETF and cash, through claim 110's two-scalar reduction. Claims 044
and 046 give today's lines with one fund and bound tomorrow's cash price and the incumbent
values in the inputs; claim 047 splits the one-fund reserve into a cost channel (the ETF's
expected marked cost slope tomorrow over its curvature, with the fund fixed) and a budget
channel (the cash-price terms), and defines the reserve through the funding capacity.
With N funds three things are new and stated here: the root still reduces to two scalars, the
exposure price and the dynamic cash price, once the vector of incumbent values is known, so
the funds couple only through them (part 1); the no-reserve test is one inequality per state on
the *aggregate* solo-target need against today's cash plus the ETF's sale proceeds, whose
maximum over states is the reserve's ceiling and pools across funds only through the states'
probabilities (part 2); and what fails fund by fund is precise: the cash price at a state is
one number for all funds, and each fund's dynamic-minus-myopic move has the sign of its own
residual corrected by the two shared scalars' changes, which a fund-by-fund rule cannot see
(part 3). The reserve itself is the funds' holdings foregone plus the cost difference, bounded
through part 3 (part 4). No many-ETF result is attempted.

**Setting.** Claim 044's, with N >= 1 funds: M7's finite-law variant (M8's instance with N
funds), one factor, funds i = 1..N with loadings b_i > 0, net alphas alpha_hat_i, residual
variances v_i = sigma_i^2 + p^alpha_i (independent residuals and a zero prior cross-covariance,
so Sigma_t is entrywise nonnegative), one ETF with loading b_E > 0, drag c^E, holdings
x = (a_1, ..., a_N, p), cash h, reviews t = 0, 1 and marking at 2, gross returns g(z') > 0,
directional rates in [0, 1), caps, the funded budget at both reviews, beta in (0, 1]. Claim
044's objects with N funds: today's multiplier eta_0, tomorrow's cash prices eta_1(z'), the
dynamic cash price eta_hat_0 = eta_0 + beta E eta_1, the incumbent values S_i = beta E[g_i s_i]
for every instrument i (funds and ETF), and the *repeated one-review policy* (myopic). Claim
110's coordinates at each review t: the netting weights r_i = b_i/b_E, sigma_EE,t = b_E^2
(sigma_f^2 + p^lambda_t), the exposure price m_t = mu_{t,E} - gamma sigma_EE,t w_t with
w_t = p_t + sum_i r_i a_{t,i}, and alpha~_{t,i} = mu_{t,i} - r_i mu_{t,E}. Claim 046's solo targets
and need, now over every instrument,

```
x_hat_i(z') = (mu_{1,i}(z') - kappa^+_i)^+/(gamma Sigma_{1,ii}(z')),        x_hat^s_E(z') = (mu_{1,E}(z') + kappa^-_E)/(gamma Sigma_{1,EE}(z'))   (the ETF's solo sale threshold),
need(z') = sum_{i in funds and E} (1 + kappa^+_i) ( x_hat_i(z') - g_i(z') x_{0,i} )^+,
liq(z') = h^+_0 + (1 - kappa^-_E) ( g_E(z') p_0 - (x_hat^s_E(z'))^+ )^+                 (today's cash plus the ETF's sale proceeds down to its solo sale threshold, clipped at zero: a negative threshold means the ETF is sold out),
N(x_0) = max_z' need(z')                                                                  (claim 047's largest funding need, now summed over the funds),
F(x_0) = h^+_0 + (1 - kappa^-_E) g^min_E p_0,   Res = F(x^dyn_0) - F(x^my_0)               (claim 047's funding capacity and signed reserve: the ETF at its worst-case liquidation),
R = (p_0 + h^+_0)^dyn - (p_0 + h^+_0)^my                                                  (the ETF-plus-cash reserve at par, this claim's part 4; Res = R - [1 - (1 - kappa^-_E) g^min_E] (p^dyn_0 - p^my_0)).
```

Claim 047's channels carry over with several funds: the cost-channel reserve is the ETF's
S_E/(gamma Sigma_{0,EE}) with the funds fixed (one ETF, so its form is unchanged), and the
budget channel is the aggregate one of part 2.

### Part 1. The root reduces to two scalars given the incumbent values

1a. Claim 044's parts 1 and 2 hold with N funds: the two-review problem is one concave
    program over a polyhedron in (x_0, {x_1(z')}); x_0 with {x_1(z')} is optimal iff
    tomorrow's lines hold in every state (claim 110's part 1 at each state, N funds) and today's
    lines hold with eta_hat_0 and the incumbent values, instrument by instrument, with the
    same tomorrow slopes in both sets.
1b. At the root, every fund's holding is claim 110's clip at the root's exposure price and the
    dynamic cash price with its incumbent value added to its net alpha:

    ```
    a_{0,i} = clip( a^-_i, lo_i, hi_i ) clipped to [0, bar a_i],
    lo_i = [ alpha~_{0,i} + S_i + r_i m_0 - eta_hat_0 - (1 + eta_hat_0) kappa^+_i ]/(gamma v_i),   hi_i = [ alpha~_{0,i} + S_i + r_i m_0 - eta_hat_0 + (1 + eta_hat_0) kappa^-_i ]/(gamma v_i),
    ```

    and the ETF's root line is m_0 - gamma sigma_E p_0 + S_E = eta_hat_0 + (1 + eta_hat_0) t_E - zeta
    (claim 110's ETF line with S_E added). So, given the vector S = (S_1, ..., S_N, S_E), the
    funds decouple: their interaction at the root runs through the two scalars m_0 and
    eta_hat_0 only, which claim 110's parts 2-3 determine from the ETF's line and the budget
    with alpha~ + S in place of alpha~ (the at-zero and idle candidates and the cash-slack
    search, unchanged in form). S itself is read from tomorrow's solutions, which depend on x_0
    (a fixed point, not a closed form); at every state tomorrow claim 110 applies exactly, with
    one common cash price eta_1(z') for all funds.

### Part 2. The aggregate no-reserve test with the ETF as reserve, and the reserve's ceiling

2a. *One inequality per state.* If liq(z') >= need(z') at state z' (both evaluated at the root
    holdings x_0 and cash h^+_0 in question), then eta_1(z') = 0 is admissible there: the state's
    optimum without the budget is feasible, so its budget does not bind. The purchases the
    state makes are at most the instruments' solo-target purchases, and the ETF's sale, if its
    marked holding exceeds its solo sale threshold clipped at zero, yields at least the
    proceeds counted in liq (all of it when the threshold is negative, the ETF then being sold
    out). This strengthens claim 046's 1(b) and claim 047's part 2(b) by counting the ETF's
    sale proceeds as liquidity and summing the need over the funds; it is this claim's.
2b. *No reserve needed.* If liq(z') >= need(z') in every state, evaluated at the dynamic root
    (x_0, h^+_0), then there is an admissible multiplier family with eta_1 = 0 in every state,
    for which eta_hat_0 = eta_0 and every incumbent value lies in claim 029's brackets,
    -beta E[g_i] kappa^-_i <= S_i <= beta E[g_i] kappa^+_i; when h^+_0 > 0 this holds for every
    admissible family (a positive cash price in a covered state would force no trade with all
    cash spent), while at the edge h^+_0 = 0 = need(z') a joint family can carry a positive
    eta_1(z') in a state that trades nothing with all cash spent (claim 046's 1(c) edge). So
    the shared reserve has no budget option value, and today's lines differ from the
    one-review lines only by the round-trip terms of claim 044's 3(a). The one-fund test of
    claim 046's 1(b) is the case N = 1 with the ETF's sale proceeds not counted.
2c. *The ceiling and pooling.* The liquidity that makes every state's budget slack is
    N(x_0) = max_z' need(z') (claim 047's largest need with the funds summed); beyond it no
    reserve, in cash or in the ETF, changes tomorrow's cash prices, so it is the reserve's
    ceiling in liquidity units (claim 047's part 5's cash bound, with N funds) (a reserve held in the ETF must
    deliver it after the sale's rate and marking: (1 - kappa^-_E) g_E(z') p_0 net of the solo
    sale threshold, state by state). The maximal aggregate need pools across funds only through
    the states:

    ```
    max_z' need(z')  <=  sum_i max_z' need_i(z'),
    ```

    with equality iff some state attains every instrument's maximal need at once; on M8's
    product tree with independent fund residuals such a state exists when each fund's need is
    maximal at its own worst residual and every fund's need peaks at the same factor value
    (the common factor shock drives each need through the premium revision and the marking,
    so the funds' maximizing states share a state only then), and the ceiling then does not
    pool, the pooling benefit of
    a shared reserve lies in the joint worst state's probability, the product of the funds'
    worst-state probabilities, which is what the dynamic cash prices E eta_1 weigh.

### Part 3. What fails fund by fund: the common cash price and the corrected sign

3a. *One cash price per state.* At a state whose budget binds, eta_1(z') is claim 110's cash
    root with N funds: the funds bought are those whose net alpha plus exposure term exceeds
    the scaled purchase line at the common price, alpha~_{1,i} + r_i m_1 - gamma v_i g_i a_{0,i} > eta_1 + (1 + eta_1) kappa^+_i,
    and the price is the smallest at which the aggregate purchases (net of sales) fit the
    liquidity. A rule that prices each fund's reserve with its own cash price is wrong whenever
    two funds would buy at the same state with the liquidity short: the state rations the
    reserve by one price, and every fund's incumbent value S_i carries that same eta_1(z').
3b. *The corrected sign.* If fund i trades strictly inside its box in the same direction at the
    dynamic root and at the myopic root (kappa = kappa^+_i for a purchase, -kappa^-_i for a sale),
    then

    ```
    sign( a^dyn_{0,i} - a^my_{0,i} ) = sign( S_i + r_i (m^dyn_0 - m^my_0) - (eta_hat_0 - eta^my_0) (1 + kappa) )   whenever the right side is nonzero,
    ```

    and the difference itself is that quantity over gamma v_i: the fund's own residual S_i,
    corrected by the change in the exposure price at its netting weight and by the change in
    the cash price at its trade's scale. In general, for a fund strictly inside its box at both
    roots (trading or held, in any directions), with t^dyn and t^my its slopes at the two
    roots (the pinned rate when trading, the held slope (g_{0,i} - eta)/(1 + eta) when not),

    ```
    a^dyn_{0,i} - a^my_{0,i} = [ S_i + r_i (m^dyn_0 - m^my_0) - (eta_hat_0 - eta^my_0) - (1 + eta_hat_0) t^dyn_i + (1 + eta^my_0) t^my_i ]/(gamma v_i),
    ```

    which covers the cells where the dynamic policy sells a fund the one-review policy holds
    (the analyst's experiment 055: a fund held inside its band at the one-review root and sold
    at the dynamic root, the slope term -(1 + eta_hat_0)(-kappa^-_i) + (1 + eta^my_0) t^my_i
    carrying the difference with S_i; claim 047's part 3(b) has the one-fund form). The corrections are the same two numbers for every
    fund, and they can flip a fund's sign against its own residual (substitution through the
    shared exposure and the shared budget), which is why claim 044's per-instrument reading
    fails with several instruments and why claim 046's part 4 needed its hedge term: with one
    fund and a frictionless residual-free ETF held interior at both roots, the ETF's root line
    pins m^dyn_0 = eta_hat_0 - S_E and m^my_0 = eta^my_0, so the correction is
    r (eta_hat_0 - eta^my_0 - S_E) - (eta_hat_0 - eta^my_0)(1 + kappa): the ETF's own residual
    passed to the fund at its netting weight, the role claim 046's hedge term plays (a
    comparison of roles, not an identity between the two statements, which are evaluated at
    different points). A fund-by-fund rule that ignores the corrections predicts the wrong
    direction exactly when the corrections outweigh S_i.

### Part 4. The reserve

The reserve at par, R = (p_0 + h^+_0)^dyn - (p_0 + h^+_0)^my (claim 047's signed reserve Res
counts the ETF at its worst-case liquidation instead; the two differ by
[1 - (1 - kappa^-_E) g^min_E] times the ETF's move, and either may be used), equals the funds'
holdings foregone plus the cost difference,

```
R = sum_i ( a^my_{0,i} - a^dyn_{0,i} ) + [ C(u^my_0) - C(u^dyn_0) ],
```

(the wealth identity), and can be negative (the dynamic policy front-loads funds). For every
fund strictly inside its box at both roots, part 3b's general form bounds its term, the slope
terms contributing at most (2 + eta_hat_0 + eta^my_0) kappa^max_i with kappa^max_i = max(kappa^+_i, kappa^-_i)
(zero on common trading pieces), so

```
|R| <= sum_i [ |S_i| + |r_i| |m^dyn_0 - m^my_0| + |eta_hat_0 - eta^my_0| + (2 + eta_hat_0 + eta^my_0) kappa^max_i ]/(gamma v_i) + |C(u^my_0) - C(u^dyn_0)|,
```

with |S_i| <= beta E[ g_i max(kappa^-_i, eta_1 + (1 + eta_1) kappa^+_i) ] (from s_i in
[eta_1 - (1 + eta_1) kappa^-_i, eta_1 + (1 + eta_1) kappa^+_i], whose lower end is at least -kappa^-_i)
and eta_hat_0 - eta_0 <= beta E[eta_bar]
by claim 046's parts 2 and 1(c) where they apply, which bounds |eta_hat_0 - eta^my_0| when
today's budget is slack at both roots (eta_0 = eta^my_0 = 0); with today's budget binding at
either root, eta_0 - eta^my_0 is a further term, not bounded here, and the exposure-price
change is not bounded in the inputs here either (both Not shown). With every state covered (2b) the bound has no cash-price terms
and the reserve is the round-trip effect alone.

**One sentence without model nouns.** With several positions and one cheap instrument as the
common reserve, each position still decides by its own band at two shared prices, the price
of exposure and the price of cash, once each position's value tomorrow is known; no reserve is
needed when, whatever happens, today's cash plus what the instrument fetches when sold to its
own threshold covers what all positions would together want to buy, and the most a reserve can
ever be worth is the largest such shortfall across states, which does not shrink by pooling
except through how unlikely the joint worst case is; and sizing the reserve position by
position fails because the price of cash in a state is the same for all of them and can turn a
position's move against its own signal.

## Proof

### 1. The root

Claim 044's proof is instrument-wise: the program is concave over a polyhedron (its part 1's
argument does not use N = 1), AX-13 gives the KKT lines for every instrument at every node
(the lifted polyhedral problem, hypotheses as in claim 102's part 1), and eliminating
tomorrow's multipliers into today's lines gives S_i and eta_hat_0 for each instrument exactly
as in claim 044's part 2 (each fund has its own line and its own S_i; the ETF likewise). 1b:
at the root the smooth marginal of fund i is g_{0,i} = alpha~_{0,i} + r_i m_0 - gamma v_i a_{0,i}
(claim 110's part 1 identity, which holds for any N since it is the ETF row eliminated
instrument by instrument), so the root line g_{0,i} + S_i - eta_hat_0 - (1 + eta_hat_0) t_{0,i}
in the box cone is claim 110's fund line with alpha~ + S_i, whose solution is the displayed
clip (claim 029's 1a at T - 1, as in claim 110's proof of part 1). The ETF's root line is claim
044's with claim 110's ETF marginal. Claim 110's parts 2-3 apply verbatim to the root problem
with the premia alpha~ + S and mu_E + S_E and the cash price eta_hat_0, for a fixed S.

### 2. The aggregate test

Fix z' and let x^0 be the state's optimum without the budget (unique). If x^0_i > g_i x_{0,i}
(bought), its line is mu_{1,i} - gamma (Sigma_1 x^0)_i = kappa^+_i, and since Sigma_1 is entrywise
nonnegative and x^0 >= 0, mu_{1,i} - gamma Sigma_{1,ii} x^0_i >= kappa^+_i, so x^0_i <= x_hat_i(z');
hence every purchase is at most (x_hat_i - g_i x_{0,i})^+ and its cash at most
(1 + kappa^+_i)(x_hat_i - g_i x_{0,i})^+. If g_E p_0 > (x_hat^s_E)^+, the ETF's marginal at its marked
holding, mu_{1,E} - gamma Sigma_{1,EE} g_E p_0 - gamma sum_i Sigma_{1,Ei} a_i <= mu_{1,E} - gamma Sigma_{1,EE} g_E p_0 < -kappa^-_E,
so the ETF is sold; its line at the post-trade holding p^0 gives g_{1,E} >= -kappa^-_E (equality
if p^0 > 0, the one-sided inequality if sold out), hence mu_{1,E} - gamma Sigma_{1,EE} p^0 >= -kappa^-_E
and p^0 <= x_hat^s_E, and p^0 >= 0, so p^0 <= (x_hat^s_E)^+ (when the threshold is negative the
ETF is sold out and the proceeds are all of (1 - kappa^-_E) g_E p_0); the sale's proceeds are
therefore at least (1 - kappa^-_E)(g_E p_0 - (x_hat^s_E)^+). Cash used by x^0 is the purchases'
cash less every sale's proceeds, at most need(z') - (1 - kappa^-_E)(g_E p_0 - (x_hat^s_E)^+)^+
<= h^+_0 by liq >= need, so x^0 satisfies the budget and is the budgeted optimum with
multiplier 0 (AX-13's sufficiency with eta_1 = 0). 2b: choose eta_1 = 0 in every state, an
admissible family, for which eta_hat_0 = eta_0 and s_i(z') = t_{1,i}(z') in [-kappa^-_i, kappa^+_i],
claim 044's 3(a); with h^+_0 > 0, any admissible family with eta_1(z') > 0 at a covered state
would have that state trading nothing with all its cash spent (complementary slackness) while
its unconstrained optimum is feasible and unique, a contradiction, so every family has
eta_1 = 0 there; the edge h^+_0 = 0 = need is claim 046's 1(c). 2c: for
h^+_0 >= max_z' need(z') the hypothesis of 2a holds in every state without the ETF's proceeds;
the inequality max of a sum <= sum of maxima is elementary with the stated equality case; the
product-tree remark is the definition of the tree.

### 3. The obstruction

3a: claim 110's part 3 at the state with N funds (claim 110's part 2's cash search with the
funds' clips at the common (m_1, eta_1); the funds bought are those whose lo_i exceeds their
marked incumbent). 3b: on the trading piece a_{0,i} = lo_i (purchase) or hi_i (sale), affine in
(S_i, m_0, eta_hat_0) with the displayed coefficients, and the myopic root's holding is the same
expression with S_i = 0, m^my_0 and eta^my_0 (claim 110 at the root without the continuation);
subtracting gives the difference over gamma v_i exactly. The general form: at either root a
fund strictly inside its box has g_{0,i} + S_i - eta - (1 + eta) t_i = 0 with its own (S_i, eta, t_i)
(S_i = 0 at the myopic root; t_i its pinned or held slope), and g_{0,i} = alpha~_{0,i} + r_i m_0 - gamma v_i a_{0,i}
(part 1b's identity), so each holding is [alpha~_{0,i} + S_i + r_i m_0 - eta - (1 + eta) t_i]/(gamma v_i)
and the difference is the display. The one-fund frictionless case: with
kappa_E = 0, sigma_E = 0 and the ETF interior at both roots, its root line (1b) reads
m_0 + S_E = eta_hat_0 at the dynamic root and m_0 = eta^my_0 at the myopic one (claim 110's ETF
line with t_E = 0, zeta = 0), which gives the displayed correction.

### 4. The reserve

Wealth before trading is h^-_0 + p^-_0 + sum_i a^-_i under both policies, and after trading
h^+_0 + p_0 + sum_i a_{0,i} + C(u_0); subtracting the two policies' identities gives the display.
The bound is 3b's difference on trading pieces, and a fund strictly inside its box at both roots
has its term given exactly by 3b's general form, whose slope terms are at most
(1 + eta_hat_0) kappa^max_i + (1 + eta^my_0) kappa^max_i in absolute value; a fund at a bound under
one policy moves by less than that expression (the clip is 1-Lipschitz in its arguments), so
the bound holds for every fund; claim 046's parts 1(c) and 2 bound the
S_i and the cash-price change where their hypotheses hold.

## Checks

`uv run python checks/113/check.py` (exits non-zero on failure; a check, not a proof). Eighteen
random instances (twelve with two funds on a 432-node tree with claim 112's finite laws, six
with three funds on a 768-node tree with two-point residual shocks; loadings, alphas, rates,
incumbents and cash random, the budget tight on half; all assumed), each solved exactly as one
concave two-review program over the public tree by CLARABEL through cvxpy, with tomorrow's
cash prices from the node budgets' duals. It checks: part 1's root clip at (m_0, eta_hat_0)
with alpha~ + S for all 42 fund holdings and the ETF's root line in every instance; part 2's
test at the 258 states where liq >= need (eta_1 = 0 admissible at each, read off the state's
lines) and claim 046's cash-price bound eta_1 <= eta_bar at 5,815 buying states; part 3b's
sign at the 6 fund moves that trade interior in the same direction at both roots; the pooling
inequality in every instance (strict in 5 of 18, equal in the others, where the joint worst
state attains every fund's maximal need); and part 4's reserve identity. Thirteen instances
have a binding budget at some review; the reserve ranges from -0.20 to +0.03 of wealth.

## Not shown

- A bound on the exposure-price change m^dyn_0 - m^my_0 in the inputs, and on today's
  cash-price change eta_0 - eta^my_0 when today's budget binds at either root (part 4's bound
  carries both as terms); the reserve's growth in the revision variance and the rates, and its maximum
  as a rule (D19's, one fund; once filed, part 4's per-fund terms take D19's bounds).
- A pooled alpha prior (common and relative components): the funds' needs then co-move and
  part 2c's equality case is the common component's worst state; not written out.
- Several ETFs; the Gaussian law (M8's finite-law variant throughout); more than two reviews.
- Part 3a describes the rationing at a state through claim 110; the order in which funds are
  served as the liquidity grows (a path in the cash price) is not stated.
- The experiment 055 readings: the |R| bound was measured outside the common-trading-piece
  case it was first stated for (it held in 48 of 48 cells; the general form now covers every
  interior fund), and a common worst state for 2c's equality existed in 12 of 48 cells.
- No calibration: the check's instances are assumed inputs (rule 22).

## Prior art

Mechanism: with several positions and one cheap instrument, the multi-period first-order
conditions still separate position by position given two shared prices and each position's
continuation value; a budget that may bind tomorrow is slack whenever the liquidity carried
covers the sum of what each position would buy on its own, so the largest such sum across
states caps the useful reserve and pools across positions only through the states; and a
position's multi-period deviation from its one-period choice is its own continuation value
corrected by the two shared prices' changes, so position-by-position sizing fails where the
shared prices move against a position's own signal.

General results checked: claim 044 (approved): the root lines, the dynamic cash price and the
incumbent values, extended instrument-wise to N funds (its proof does not use N = 1); claim
046 (approved): the cash-price bound, the no-reserve condition (its 1(b) is 2a with N = 1 and
without the ETF's proceeds), the incumbent-value brackets, and part 4's hedge term (3b's
one-fund case); claim 047 (red-passed, D19): the reserve's two channels, the largest need
N(x_0), the funding capacity and signed reserve, and the cash bound of its part 5, which parts
2c and 4 carry to N funds (its definitions are used as math's note fixes them); claim 110 (formalized): the two-scalar reduction, at the root with the
incumbent values and at every state; claim 111 (approved): not used beyond naming the
exposure-first policy. `hakansson1971myopic` (ROADMAP D19's Known): myopic optimality without
frictions, the case 2b reduces to when the round-trip terms vanish. Searched: claims 044, 046,
110-112, the D16-D21 roadmap entries, LAB_REQUEST_2.md. No web search. This is a claim
because D20 asks for a bound or a precise obstruction with several funds; its kill test (D19's
rule fund by fund with nothing from the shared ETF and budget) fails on 2a's aggregate need,
2c's pooling, and 3a-3b's common price and corrected sign.

## Open objections

none

## Review

**Red, 2026-09-30** (on 1c15647e). Red-passed, with two nits. leanb's three points (the clipped sale threshold in liq, 2b's family and edge, part 4's E[max] form) are made in this text. Red rederived every part by hand and tested parts 1b, 2a and 3b with its own solver, written without reading checks/113: one factor, N = 2 funds and one ETF, two reviews, 8 states tomorrow, Sigma_t = s b b' + diag(v, sigma_E^2), the lifted joint program and the one-review program in cvxpy/CLARABEL.

**Part 1b** is right. With one factor and positive loadings, g_{0,i} = alpha~_{0,i} + r_i m_0 - gamma v_i a_{0,i} for any N, since the factor term is r_i sigma_EE w. Each fund's root line is then claim 110's clip with alpha~ + S_i. At 152 fund holdings at dynamic roots, the displayed clip equals the holding to 4.3e-11.

**Part 2a** is right by hand. Sigma_1 is entrywise nonnegative, so a bought instrument ends at most at its solo target. An ETF marked above its solo sale threshold (clipped at zero) is sold down to at most (x_hat^s_E)^+, so the proceeds are at least those counted.
- *Test at arbitrary roots* (random post-trade holdings and cash, the claim being for any root). At 2,270 covered (state, root) pairs, the state's budget-free optimum spends at most h^+_0.
- *The ETF's proceeds.* At 454 of them cash alone falls short of the need and the ETF's proceeds carry the test, with no violation.
- This strengthens claim 046 1(b) and claim 047 part 2(b) as stated.

**Part 2b** is right, with claim 046's 1(c) edge named. **Part 2c's** inequality and equality case are right.

**Part 3.**
- *3a* is claim 110's cash search with N funds at the common eta_1.
- *3b* is exact: the difference of the two lower (or upper) clip ends. At 11 funds trading the same way strictly inside their boxes at both roots, the predicted difference matches to 7.0e-12.
- *The one-fund frictionless reduction* (m^dyn_0 = eta_hat_0 - S_E, m^my_0 = eta^my_0) is right, and the comparison with claim 046's hedge term is correctly labelled a comparison of roles.

**Part 4.** The wealth identity is right. The bound follows from 3b on the trading pieces and the clip being 1-Lipschitz in (lo, hi), which covers a fund trading under one policy and not the other.

**Nits.**
- *2c's product-tree remark.* "such a state exists when each fund's need is maximal at its own worst residual" ignores the common factor shock. Each fund's need depends on the factor through the premium revision and the marking, so the maximizing states share a state only if every fund's need peaks at the same factor value. Please add that condition.
- *Part 4's bound* uses |eta_hat_0 - eta^my_0|, but cites eta_hat_0 - eta_0 <= beta E[eta_bar]. The two agree only when today's budget is slack at both roots (eta_0 = eta^my_0 = 0). With today binding, eta_0 - eta^my_0 is a further term, not bounded here. Please say so, or add it to Not shown.

**Mechanism.** Claim 110's two-scalar reduction at the root with claim 044's incumbent values, claim 046's need summed over the funds with the ETF's sale proceeds as liquidity, and one-variable clip algebra: an application. New in the inputs: the aggregate no-reserve test with the ETF as reserve, and the precise fund-by-fund obstruction (the common cash price, and each fund's sign corrected by the two shared scalars' changes).

Verdict: red-passed

**Red, recheck of the nits branch (31bcce5d, eb5fb368), 2026-09-30.** Red's two nits are made: 2c's common factor value, and part 4's cash-price term with today's budget binding (Not shown). The general form added to 3(b) is right by hand.
- *The general form.* At either root, a fund strictly inside its box has g_{0,i} + S_i - eta - (1 + eta) t_i = 0 with its own (S_i, eta, t_i), and g_{0,i} = alpha~_{0,i} + r_i m_0 - gamma v_i a_{0,i}. So a_{0,i} = [alpha~_{0,i} + S_i + r_i m_0 - eta - (1 + eta) t_i]/(gamma v_i), and the difference of the two roots is the display.
- *The restated part 4 bound* holds, since the slope terms are at most (1 + eta_hat_0) kappa^max_i + (1 + eta^my_0) kappa^max_i.

Two precision slips, neither changing a result.
- The held slope at the dynamic root is (g_{0,i} + S_i - eta_hat_0)/(1 + eta_hat_0), with S_i. The text writes (g_{0,i} - eta)/(1 + eta), which is the myopic root's form (S_i = 0).
- "Zero on common trading pieces" is not right. On a common piece the slope term is -(1 + eta_hat_0) kappa + (1 + eta^my_0) kappa = -(eta_hat_0 - eta^my_0) kappa, which is zero only when the two cash prices agree. The bound is unaffected.

No result changed. The approval stands.

## Formalization notes

Approved 2026-09-30 by pm: Red's review is sound: every part re-derived by hand, and 1b, 2a and 3b tested on red's own two-fund, one-ETF lifted solver (the clip at 152 dynamic-root holdings to 4.3e-11; 2a's aggregate no-reserve test at 2,270 covered state-root pairs, 454 carried by the ETF's sale proceeds, no violation; 3b's exact difference at 11 trading funds to 7.0e-12); leanb's three prose points made. Mechanism: claim 110's two-scalar reduction at the root with claim 044's incumbent values and claim 046's need summed over funds, an application; new in the inputs: the aggregate no-reserve test with the ETF as the reserve, which strengthens claims 046 1(b) and 047 2(b), and the precise fund-by-fund obstruction through the common cash price, so D20's kill criterion is not met. Limits: one ETF; red's two nits (2c's common-factor condition; part 4's bound with today binding) routed.


mathb, 2026-09-30 (leanb's prose check, duty 1, before red's review): 2a's liquidity counts the
ETF's proceeds down to its solo sale threshold clipped at zero (a negative threshold means the
ETF is sold out, and its whole marked value is proceeds), with the proof through the ETF's
line at a sale; 2b says for which multiplier family eta_hat_0 = eta_0 holds (one admissible
family always, every family when h^+_0 > 0, claim 046's edge otherwise) and that liq and need
are evaluated at the dynamic root; part 4's |S_i| bound has the cash price inside the
expectation. checks/113 and the ledger row carry the clipped form. No result changed.

mathb, 2026-09-30 (math's D19 definitions note): re-keyed to claim 047's objects (N(x_0), the
funding capacity F and the signed reserve Res, the cost and budget channels), 047 added to
depends_on, the relation between Res and this claim's at-par reserve R stated, and 2a marked as
this claim's strengthening of claim 046's 1(b) and claim 047's 2(b). No result changed.

mathb, 2026-09-30 (red's two nits, after approval): 2c's product-tree remark now requires every
fund's need to peak at the same factor value; part 4's bound says claim 046's cash-price bound
covers |eta_hat_0 - eta^my_0| only with today's budget slack at both roots, today's cash-price
change being a further term otherwise (Not shown). No result changed.

mathb, 2026-09-30 (the analyst's experiment 055 note): 3b now states the general form of a
fund's dynamic-minus-myopic move for any fund strictly inside its box at both roots, with the
two roots' slopes (the analyst's display, claim 047's part 3(b) with several funds), which
covers a fund held at the one-review root and sold at the dynamic root; part 4's bound is
restated for every interior fund with the slope terms added; experiment 055's readings are in
Not shown. No result changed.

Not machine checked. Parts 1, 3 and 4 are finite convex-analysis statements about one concave
program on the tree (claim 044's with N funds) and claim 110's clip; part 2 is a feasibility
argument for the unconstrained-budget optimum.

Leanb, 2026-09-30: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M7SeveralFundsReserve.lean` and the proof
  `lean/Novel/M7SeveralFundsReserveProof.lean`, on claims 044's and 046's objects and claim 046's
  proof lemmas (Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/113/check.py` pass.
- *1a.* Claim 044's formal parts 1-2 are stated for any finite set of instruments, so N funds and the
  ETF are covered. They are cited, not restated.
- *The clip.* It is restated with claim 110's formula, and `ClipIsXi` proves it equals claim 110's
  `xi`. It is restated because `xi` takes claim 110's `One N` coordinates, with the ETF outside the
  funds' index, while claim 044's `Two ι Z` holds the ETF among its instruments.
- *Factor structure.* M8's factor structure is the hypothesis `Factor`.

Machine checked:
1. 1b: g_{0,i} = alpha~_i + r_i m - gamma v_i x_i, and every fund's root holding is claim 110's
   clip at (m, eta_hat_0) with S_i added to alpha~_i.
2. 2a, with the threshold clipped at zero: need <= liq at a state makes eta_1 = 0 admissible
   there, from any admissible multiplier.
3. 2b: every state covered gives an admissible family with eta_1 = 0, with eta_hat_0 = eta_0 and
   claim 029's brackets. With h^+_0 > 0, every family has eta_1 = 0.
4. 2c: max_z need <= sum_i max_z need_i, with equality when one state attains every maximum.
5. 3b: the exact difference [S_i + r_i Delta m - Delta eta (1 + kappa)]/(gamma v_i) on the trading
   pieces.
6. Part 4: the wealth identity, the clip's Lipschitz bound (each fund's move off the trading pieces
   too), and Res = R - [1 - (1 - kappa^-_E) g^min_E](p^dyn - p^my).

Paper-level:
- 3a (claim 110's cash root with N funds);
- 2c's product-tree remark;
- the fixed-point remark;
- the carried-over cost channel (claim 047's form, one ETF);
- the Checks.

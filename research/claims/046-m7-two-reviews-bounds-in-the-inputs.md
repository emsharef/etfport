---
id: 46
title: "The two-review criterion with a binding budget, bounded in the inputs: tomorrow's cash price never exceeds the best expected return net of its purchase rate, scaled, and is zero whenever the cash carried covers the solo-target purchases; the incumbent values never fall below claim 029's bracket and rise at most by the marked cash price and its scaling of the purchase rate; the residual that decides hoarding against front-loading is bracketed by the expected cash price weighted by the instrument's marked gain or loss; with a slack budget today, repeated one-review optimization is dynamically optimal only where it trades nothing today, trades to a bound, or trades an instrument costless on both sides with a slack budget tomorrow, an interior trade of an instrument costly on either side being consistent on one equation only; and with a frictionless interior ETF the fund's dynamic holding moves with the sign of the reduced residual, the residual with the ETF re-optimized at the myopic fund holding"
status: formalized
model_version: M7
depends_on: [29, 44, 102, 110]
axioms_used: [AX-13]
formal: lean/Standalone/M7TwoReviewsBounds.lean
direction: D16
---
## Statement

D16's second claim, the refile of refuted claim 045 (red's refutation: its part 3 failed when
today's budget binds at the myopic root, where eta_0 is free, and for a costless instrument with
a slack budget tomorrow, where the equation is an identity; part 3 is restated under today's
slack budget with those cases named, 1(c) says what is proved about the joint multipliers, and
the title's "covariance" is corrected; parts 1(a)-(b), 2 and 4 are as red passed them). Claim 044
gives today's lines exactly, with two numbers read from tomorrow's
solutions: the cash price eta_1(z') and the incumbent values. This claim bounds both in the
inputs without solving tomorrow (parts 1-2), turns the myopic-optimality test into a statement
about when repeated one-review optimization can be right at all (part 3), and proves the
comparative static behind the hoarding and front-loading readings in the case where it is
one-dimensional, a frictionless ETF held strictly inside its box, with the residual then
evaluated at the ETF re-optimized dynamically at the myopic fund holding (part 4). The
request's "usable conditions or bounds" are parts 1-3; its "counterexample with a corrected
restricted result" is part 4's restriction, the general comparative static being false in
principle (one partial derivative does not fix a multivariate maximizer's coordinate; claim
044's review).

**Setting.** Claim 044's (M7's finite-law variant, one fund A, one ETF E, cash, two reviews,
the funded budget; M8, mathb's D17 model on main, is this instance written out), with the additional hypothesis Sigma_AE >= 0 at both reviews (the fund's and
the ETF's risks are not negatively correlated) where stated; write Sigma_{1,ii}(z') for tomorrow's
own variances, mu_{1,i}(z') for tomorrow's means, g_i(z') for the gross returns, h^+_0 for the
cash carried into tomorrow, and

```
eta_bar(z') = max_i ( mu_{1,i}(z') - kappa^+_i )^+ / (1 + kappa^+_i)         (the best expected return tomorrow net of its purchase rate, scaled),
x_hat_i(z') = ( mu_{1,i}(z') - kappa^+_i )^+ / ( gamma Sigma_{1,ii}(z') )     (instrument i's solo target tomorrow),
need(z') = sum_i (1 + kappa^+_i) ( x_hat_i(z') - g_i(z') x_{0,i} )^+           (the cash the solo targets would need from the marked holdings).
```

1. **Tomorrow's cash price, in the inputs (Sigma_AE >= 0).** (a) In every state there is an
   admissible cash price (a member of the multiplier set of claim 044 part 3(c)) with
   eta_1(z') <= eta_bar(z'). (b) If h^+_0 >= need(z') then eta_1(z') = 0 is admissible: the state's
   budget does not bind. (c) For the joint multiplier family of AX-13 (claim 044 part 2), eta_1(z') <= eta_bar(z') in every
   state that buys some instrument or whose budget is slack ((a)'s pinned and slack cases), so
   eta_0 <= eta_hat_0 <= eta_0 + beta E[eta_bar] whenever no state holds everything with all cash
   spent; in such a state the joint family's eta_1(z') lies in an interval whose upper end can
   exceed eta_bar (unbounded when nothing is held above zero), and the per-state selection
   min(eta_1(z'), eta_bar(z')), admissible state by state, is not shown to satisfy today's lines
   jointly (red's LP found it did in 360 of 360; Not shown). eta_hat_0 = eta_0 whenever h^+_0 >= need(z') in every state: for every
   admissible family when h^+_0 > 0 (a positive multiplier in a covered state would force no
   trade and all cash spent, a contradiction), and for some admissible family in the edge h^+_0 =
   0 = need(z'), where a joint family can carry a positive eta_1(z') in a state that trades nothing
   with all cash spent (leanb's edge; moving that value into eta_0 keeps eta_hat_0 but can move
   s_i out of its bracket, so the selection form is the exact one there).

2. **The incumbent values and the residual, in the inputs.** With any admissible eta_1,

   ```
   - beta E[g_i] kappa^-_i  <=  S_i  <=  beta E[ g_i ( eta_1 + (1 + eta_1) kappa^+_i ) ],
   ```

   so the binding budget never lowers an instrument's incumbent value below claim 029's
   bracket and raises it at most by the marked cash price and its scaling of the purchase
   rate. The residual R_i = S_i - beta E[eta_1] (1 + kappa^+_i) of claim 044 part 3(c) lies in

   ```
   beta [ E[ eta_1 ( g_i (1 - kappa^-_i) - 1 - kappa^+_i ) ] - kappa^-_i E[g_i],   E[ eta_1 (g_i - 1) ] (1 + kappa^+_i) + kappa^+_i E[g_i] ],
   ```

   so R_i < 0 (the hoarding sign) whenever E[eta_1 (g_i - 1)] (1 + kappa^+_i) < - kappa^+_i E[g_i]:
   tomorrow's cash price is high in the states where the instrument is marked down, by more
   than its purchase rate covers; and R_i > 0 (the front-loading sign) whenever E[eta_1 (g_i (1 -
   kappa^-_i) - 1 - kappa^+_i)] > kappa^-_i E[g_i]: the cash price is high in the states where the
   instrument's gain, net of the round trip, covers the purchase. With eta_1 bounded by part 1
   these are conditions on the joint law of the marking and the cash price's bounds.

3. **When repeated one-review optimization can be right (today's budget slack).** The repeated
   one-review policy is dynamically optimal iff (claim 044 part 3(c)) its root lines hold for
   some admissible tomorrow multipliers and some eta_0. Suppose today's budget is slack at the
   myopic root, h^+_0(x^my_0) > 0, so that eta_0 = 0 in both the myopic and the root lines. Then
   an instrument traded strictly inside its box today is consistent iff, for some admissible
   tomorrow family, S_i = beta E[eta_1] (1 + kappa^+_i) (a purchase) or S_i = beta E[eta_1] (1 -
   kappa^-_i) (a sale); an instrument traded to a bound or held is consistent on an inequality.
   The equation is an identity when the instrument is costless on *both* sides (kappa^+_i =
   kappa^-_i = 0, so that t_{1,i} = 0 whatever tomorrow's trade) and tomorrow's budget is slack in
   every state (S_i = 0 = beta E[eta_1]; claim 036's rule); with only the trade's side costless a
   sale tomorrow gives t_{1,i} = -kappa^-_i and the equation is not an identity (red's correction:
   28 instances buying a purchase-costless ETF with every budget slack, myopic optimal at none);
   otherwise it is one equation on the inputs through tomorrow's solutions. So, with a slack
   budget today, *repeated one-review optimization is dynamically optimal only where it trades
   nothing, trades an instrument to zero or to its
   cap, or trades an instrument costless on both sides with a slack budget tomorrow*, apart from the inputs on which that equation happens to hold. *With a
   binding budget today* at the myopic root (cash price eta_0^my > 0 there), eta_0 is free in the
   root test, and an interior purchase of instrument i is consistent iff, for some admissible
   tomorrow family and some eta_0 >= 0 that also satisfies the other instrument's root line,

   ```
   S_i = ( eta_0 - eta_0^my + beta E[eta_1] ) (1 + kappa^+_i),     that is,     S_i >= ( beta E[eta_1] - eta_0^my ) (1 + kappa^+_i)
   ```

   (the sale form with 1 - kappa^-_i): an inequality, the incumbent value at least the excess of
   tomorrow's expected cash price over today's, at the purchase scale, so interior trades can
   be dynamically optimal on open sets there (red's 55 instances, the analyst's 53 in
   experiment 049, claim 112's worked example), which refuted claim 045's unqualified statement. With a slack budget tomorrow in every state
   (part 1(b)) the held condition is g_{0,i}(x^my_0) + beta E[g_i t_{1,i}] in the band [-kappa^-_i,
   kappa^+_i], claim 029's brackets.

4. **The comparative static, restricted (Sigma_AE >= 0 not needed).** Suppose the ETF is
   frictionless (kappa^+_E = kappa^-_E = 0) and uncapped, today's budget is slack both at the
   myopic root and at the *reduced myopic point* (the joint problem's optimum with the fund's
   root holding fixed at a^my), the myopic root buys the fund strictly inside its box, and the
   ETF is held strictly inside its box (p > 0) at the dynamic root and at the reduced point. Let
   R^red_A = S_A - beta E[eta_1](1 + kappa^+_A) and R^red_E = S_E - beta E[eta_1] be claim 044's fund and
   ETF residuals evaluated at the reduced point (its ETF holding, its tomorrow multipliers and
   slopes), and rho_0 = Sigma_{0,AE}/Sigma_{0,EE} today's hedge ratio. If tomorrow's multipliers are
   unique at the reduced point (claim 044 3(c)'s singleton case), or else for every admissible
   choice, then

   ```
   sign( a^dyn - a^my ) = sign( R^red_A - rho_0 R^red_E )   whenever the right side is nonzero:
   ```

   the fund's dynamic holding exceeds the myopic one iff its reduced residual net of the hedge
   ratio times the ETF's is positive (front-loading) and falls short iff it is negative
   (hoarding); the hedge term is the ETF's own continuation effect passed to the fund through
   today's covariance (leanb's correction of the earlier display, which dropped it), and it
   vanishes when Sigma_{0,AE} = 0 or R^red_E = 0. The residual at the myopic pair (a^my, p^my) is
   not the right object: the ETF's own line moves with the continuation, so p^red differs from
   p^my in general, and claim 044's reading uses the myopic pair. With a costly ETF no comparative static
   is claimed, and the request's counterexample is on record: in the analyst's experiment 047
   (main instance 106, an instance report, rule 22) the dynamic policy holds more of the fund
   than the myopic one (0.218 against 0.175) although the fund's residual is negative
   (-3.8e-5), because it sells the ETF instead (0.388 against 0.431, residual -6.1e-4): the joint
   move reverses by substitution through Sigma_AE and the shared budget; the corrected
   restricted result is the display above.

**One sentence without model nouns.** Without solving tomorrow, one can bound the price of
cash tomorrow by the best return available then net of its purchase cost, know it is zero
when today's leftover cash covers what each position would want on its own, bound what a unit
carried over is worth between its round-trip cost and that cash price with its purchase
premium, and read hoarding against front-loading from whether cash is dear in the states where
the position loses or gains; repeating the one-review rule is right only when it trades
nothing or fills or empties a position; and when the hedge is free and held, the position
moves in the direction of its residual computed with the hedge re-set at the position's
one-review holding.

## Proof

### 1. Tomorrow's cash price

Tomorrow's problem at a state is claim 110's one-review problem from (g o x_0, h^+_0); its
lines (claim 044 part 2) are g_{1,i} - eta_1 - (1 + eta_1) t_{1,i} in the box's normal cone with t_{1,i}
in T_i, and the multiplier set is the set of eta_1 >= 0 admitting such slopes with eta_1 h^+_1 = 0.
With Sigma_AE >= 0 and x_1 >= 0, (Sigma_1 x_1)_i >= 0, so g_{1,i} <= mu_{1,i}. (a) If some instrument is
bought strictly inside its box, its line is an equality with t = kappa^+_i: eta_1 = (g_{1,i} -
kappa^+_i)/(1 + kappa^+_i) <= eta_bar; if bought to its cap, the line reads >= 0 with t = kappa^+_i,
giving eta_1 <= (g_{1,i} - kappa^+_i)/(1 + kappa^+_i) <= eta_bar; if nothing is bought and something is sold, the
cash after trading is h^+_0 plus the net proceeds, which is positive, so the budget is slack and
eta_1 = 0 is admissible (a sale whose proceeds are spent needs a purchase, the case already
covered); if nothing is traded, the lines are g_{1,i} <= eta_1 + (1 + eta_1)
kappa^+_i for instruments below their caps and g_{1,i} >= eta_1 - (1 + eta_1) kappa^-_i for those
above zero, so the admissible set is an interval whose lower end is max(0, max_i (g_{1,i} -
kappa^+_i)/(1 + kappa^+_i)) over instruments below their caps, at most eta_bar. (b) The
eta = 0 problem's optimum x^u: a bought instrument has g_{1,i} >= kappa^+_i, so gamma Sigma_{1,ii}
x^u_i <= mu_{1,i} - kappa^+_i - gamma Sigma_AE x^u_j <= mu_{1,i} - kappa^+_i, so x^u_i <= x_hat_i and its
purchase is at most (x_hat_i - g_i x_{0,i})^+; the cash it spends is at most need(z'), sales
adding cash; if h^+_0 >= need(z'), x^u is feasible for the budget, and as the maximizer of the
objective over the larger set it is the constrained optimum, with eta_1 = 0 admissible (its
lines hold with eta = 0). (c) follows from claim 044's definition of eta_hat_0.

### 2. The incumbent values and the residual

s_i(z') = eta_1 + (1 + eta_1) t_{1,i} with t_{1,i} in [-kappa^-_i, kappa^+_i]; the lower end eta_1 (1 -
kappa^-_i) - kappa^-_i >= - kappa^-_i since eta_1 >= 0 and kappa^-_i < 1; the upper end is eta_1 + (1 +
eta_1) kappa^+_i. Multiplying by beta q(z') g_i(z') > 0 and summing gives the bracket on S_i, and
subtracting beta E[eta_1] (1 + kappa^+_i) gives the bracket on R_i; the sufficient conditions are
the bracket's ends' signs.

### 3. When repeated one-review optimization can be right

With h^+_0(x^my_0) > 0, eta_0 = 0 in the myopic line (complementary slackness) and eta_0 = 0 is the
only admissible value in the root test (the same constraint is slack at the same point). Claim
044 part 3(c) with the myopic line for an interior trade substituted: for a purchase the myopic
line is g_{0,i} - kappa^+_i = 0 and the root line is g_{0,i} + S_i - eta_hat_0 - (1 + eta_hat_0)
kappa^+_i = 0 with eta_hat_0 = beta E[eta_1], whose difference is S_i - beta E[eta_1] (1 + kappa^+_i) = 0;
for a sale, likewise S_i - beta E[eta_1] (1 - kappa^-_i) = 0. When the instrument is costless on
both sides and eta_1 = 0 in every state, both sides vanish (t_{1,i} = 0 whatever tomorrow's
trade, so S_i = beta E[g_i eta_1] = 0): an identity; with kappa^+_i = 0 < kappa^-_i a sale
tomorrow gives t_{1,i} = -kappa^-_i and S_i = -beta E[g_i kappa^-_i 1{sold}] != 0, no identity. Otherwise the left side is a nonconstant
function of the inputs through tomorrow's solutions, so the equation fails off a set of inputs
of dimension one less; at a bound or when held, claim 044's lines are inequalities, which hold
on sets with nonempty interior. With a binding budget today the subtraction is not available
(the test's eta_0 ranges over [0, infinity) while the myopic eta_0 is one number), and the root
line for an interior purchase, g_{0,i} + S_i - eta_hat_0 - (1 + eta_hat_0) kappa^+_i = 0 with g_{0,i} =
eta_0^my + (1 + eta_0^my) kappa^+_i from the myopic line and eta_hat_0 = eta_0 + beta E[eta_1], reads
S_i = (eta_0 - eta_0^my + beta E[eta_1])(1 + kappa^+_i); solving for eta_0 = eta_0^my - beta E[eta_1] +
S_i/(1 + kappa^+_i) and requiring eta_0 >= 0 gives the displayed inequality, with the same eta_0 to
be admissible for the other instrument's line; this is red's open set. The slack-tomorrow form
is claim 044 part 3(c)'s exact condition with eta_1 = 0.

### 4. The comparative static

With the ETF frictionless and uncapped, the joint root objective J(a, p) (the score minus the
fund's cost plus beta E V_1) is concave (claim 044 part 1) and strictly concave in p (Sigma_EE >
0, and E V_1 concave), and the reduced objective J^red(a) = max_p J(a, p) over the budget-feasible
p is concave in a. The dynamic optimum a^dyn maximizes J^red on the fund's box, so a^dyn > a^my
iff J^red has a positive right derivative at a^my and a^dyn < a^my iff a negative left
derivative (a concave function of one variable). *One-sided derivatives without an envelope
equality* (leanb): with p^red = argmax_p J(a^my, p) interior and the budget slack there, D^+J^red(a^my)
>= D^+_a J(a^my, p^red) and D^-J^red(a^my) <= D^-_a J(a^my, p^red) (J^red(a) >= J(a, p^red) with equality
at a^my); so a positive D^+_a J at the reduced point gives a^dyn > a^my and a negative D^-_a J
gives a^dyn < a^my. *The one-sided partial derivatives at the reduced point.* By claim 044 part
2's computation, with the fund's purchase slope t_{0,A} = kappa^+_A (the fund is bought at a^my)
and eta_0 = 0 (the budget slack at the reduced point), D^+-_a J(a^my, p^red) are the root line's
values g_{0,A}(red) + S_A - eta_hat - (1 + eta_hat) kappa^+_A with S_A over tomorrow's admissible
multipliers and slopes at the reduced point (the extremes, since V_1 is concave and not
differentiable in general; under unique multipliers the two coincide). *The hedge term.* The
myopic lines give g_{0,A}(my) = kappa^+_A and g_{0,E}(my) = 0 (both budgets slack, the ETF costless
and interior); the ETF's root line at the reduced point gives g_{0,E}(red) = eta_hat - S_E; since
g_{0,E} = mu_{0,E} - gamma (Sigma_{0,AE} a + Sigma_{0,EE} p), gamma Sigma_{0,EE}(p^red - p^my) = S_E -
eta_hat, and then g_{0,A}(red) = kappa^+_A - gamma Sigma_{0,AE}(p^red - p^my) = kappa^+_A - rho_0 (S_E -
eta_hat). Substituting, the root line's value at the reduced point is [S_A - eta_hat (1 +
kappa^+_A)] - rho_0 [S_E - eta_hat] = R^red_A - rho_0 R^red_E. When this is nonzero for the relevant
admissible choice (every choice, or the unique one), the corresponding one-sided derivative
has its sign and the display follows. That p^red != p^my in general is the ETF's root line
against its myopic line, which differ by S_E - beta E[eta_1] = R^red_E.

## Checks

`checks/046/check.py` (checks/045's check carried over; reuses claim 044's instances and solvers; cvxpy/CLARABEL; rule 22).
(i) Part 1(a): in 61 binding states an admissible cash price (the solver's when a state buys,
the held lines' lower end otherwise) is at most eta_bar; part 1(b): in 109 states where the cash
carried covers the solo-target purchases the multiplier vanishes. (ii) Part 2: on 60 tight
instances the incumbent values respect the bracket, the lower end never below claim 029's.
(iii) Part 4: over 400 draws biased toward a fund purchase today with a slack budget, the
qualifying frictionless-interior-ETF cases (few: 3) have the fund's dynamic-minus-myopic
holding of the reduced residual's sign; with a costly ETF the naive reading at the myopic pair
held in 30 of 30 draws, counted only, not asserted.

## Not shown

- Sigma_AE < 0 in parts 1-2 (the bound g <= mu fails; a version with |Sigma_AE| times the caps
  is straightforward and not written).
- The comparative static with a costly ETF, or with the ETF at zero or its cap at one of the
  two points (the counterexample is experiment 047's instance 106, cited in part 4; a joint
  condition, red's locally quadratic candidate in claim 044's Not shown, is the target).
- Parts 1-2's bounds are not tight; the cash price's exact value is claim 110's root per state.
- The joint admissibility of the per-state selection min(eta_1, eta_bar) with today's lines
  (1(c)); part 3 with a binding budget today (an interior trade can then be optimal on open
  sets, red's instances).
- The Gaussian law and more than two reviews (as in claim 044).

## Prior art

Mechanism: the multiplier set of a one-review budget problem is bounded by the lines of any
instrument the state trades or holds, and is zero when the unconstrained optimum is fundable;
the incumbent values are affine in the multipliers with bounded slopes; a one-dimensional
concave reduced objective moves its maximizer with the sign of its derivative.

General results checked: claim 044 (the lines, the myopic test, the residual); claim 110 (the
one-review problem with a binding budget); claim 029 (the slack-budget bracket); claim 102
(the scaling); AX-13 through claim 044 (the lines used are its KKT conditions; nothing new is
cited); Danskin-type envelope for a concave function with a unique inner maximizer, argued
inline for one variable (the one-sided derivatives of a partial maximum), the standard
convex-analysis fact, named. `liu2013portfolio` (named, the shadow price of a binding
constraint, continuous time).

Searched: claims 029, 044, 102, 110; the D16 entries; LAB_REQUEST. This is a claim because
the request asks for usable conditions or bounds in the inputs and a corrected restricted
comparative static, which claim 044 leaves as readings.

## Open objections

Leanb's formalization note (2026-09-29, after approval): 1(c)'s last sentence holds for every
admissible family when h^+_0 > 0 and for some admissible family in the edge h^+_0 = 0 = need; the
sentence now says so. The analyst's experiment 049 rerun (2026-09-29, at 2c533970, on its 9 instances, as a Deviation): the
restated part 3 holds at 9 of 9, today's budget binding at the myopic root at every one, the
inequality S_i >= (beta E[eta_1] - eta_0^my)(1 + kappa^+_i) holding with admissible margins of 1e-3 to
1.2e-2, and the root lines holding with eta_0 free. Red's review (9e9bd5e4, red-passed): the required correction is made, part 3's identity needing
the instrument costless on both sides, in the Statement, the title and the Proof; red confirms
the binding-today condition with both of its quantifiers needed. The analyst's experiment 049 (2026-09-29, on refuted 045's text; an instance report): parts 1, 2
and the revised part 4 agree with the exact two-review program (part 4's hedged display at 11
of 11, for every admissible choice; the front-loading condition met 17 times, always with the
right sign); the one-review policy was optimal with an interior trade today at 53 instances,
all with today's budget binding at the myopic root, the case this refile's part 3 excludes by
hypothesis, and at 9 of them the equation fails for every admissible choice, so the binding-today
case is genuinely an inequality, as part 3 now says. Refile of refuted claim 045 (red's
refutation, its Review): part 3 restated under today's slack
budget with the costless-and-slack identity named; 1(c) stated for the joint family with the
selection's joint admissibility Not shown; the title's "covariance" replaced. Red should test:
part 3's restated claim on red's 55 binding-today instances (now excluded by hypothesis) and 6
costless instances (now the named identity); 1(c)'s joint-family bound in the all-held
zero-cash states.

## Review

**Red, 2026-09-29** (on be8f38f2, rebased onto b1d67670 where the claim is unchanged; the refile of refuted 045, with math's binding-today condition in part 3). Red-passed, with one required correction to part 3's identity case. Red rechecked the restated parts by hand and on its own solver: the lifted joint program, the myopic program and claim 044's multiplier LP (`experiments/047/red_reproduce.py` and scratch scripts), written without reading checks/046.
- **Red's instances.** Experiment 047's design: 300 main and 60 costless-ETF instances, plus 200 with the ETF costless on purchases only.
- **The analyst's instances.** Their five binding-today instances (experiment 047 main 58, 75, 84, 125, 192), rebuilt in red's solver from experiment 047's seeds, and experiment 048's tight-cash cells.

**Part 1(c)** is right as restated. The joint family's eta_1(z') is a member of each state's own multiplier set, so (a)'s bound holds for it in every state that buys something (interior, pinned; to the cap, the one-sided line) or whose budget is slack (a pure sale leaves cash positive). The all-held zero-cash state, and the joint admissibility of the per-state selection, are honestly in Not shown.

**Part 2** is unchanged and right (red passed it on 045). The title's "expected cash price weighted by the instrument's marked gain or loss" is E[eta_1 (g_i - 1)], exactly the bracket's term.

**Part 3, today's budget slack.** Right, apart from the correction below.
- *The subtraction.* With h^+_0(x^my_0) > 0, eta_0 = 0 in both the myopic line and the root test, so the subtraction is valid, and an interior trade needs S_i = beta E[eta_1](1 + kappa^+_i), or (1 - kappa^-_i) for a sale.
- *Test.* With today's budget slack, red finds no myopic-optimal interior trade outside the named case: 0 of 231 main instances, and 6 of 48 costless-ETF instances, all 6 the costless-and-slack-tomorrow identity.
- *Uniqueness.* Tomorrow's multipliers are unique here outside knife edges. With cash left today, a state that trades nothing has cash left too, so eta_1 = 0. The instrument traded today is held strictly above zero tomorrow, so its slope is pinned unless it sits exactly at its cap.

**Part 3, today's budget binding (new).** Right.
- *By hand.* Substituting the myopic line g_{0,i} = eta_0^my + (1 + eta_0^my) kappa^+_i into the root line gives S_i = (eta_0 - eta_0^my + beta E[eta_1])(1 + kappa^+_i), and eta_0 >= 0 is the displayed inequality. The sale form, with (1 - kappa^-_i), follows the same way.
- *The analyst's five instances.* All bind today, trade one instrument strictly inside its box, and are myopic optimal, and the full test (claim 044's LP, eta_0 free) passes at each.
- *Red's instances.* At 69 binding-today instances with an interior trade, the full test agrees with optimality at 69. At experiment 048's tight-cash cells it agrees at 12 of 12.
- *Both quantifiers in the display are needed.*
  - *"Some admissible tomorrow family."* At the analyst's main 75, and at some of red's instances, the inequality fails at the myopic tomorrow solver's own multipliers (by 1.7e-5 at main 75), yet the policy is optimal. With all cash spent today, a state that trades nothing has an interval of multipliers, and another admissible family satisfies it (the LP finds one).
  - *"The same eta_0 for the other instrument's line."* 18 of red's instances satisfy the inequality but are not optimal, because the other instrument's line then fails.
  - A check that reads the display at one solver's multipliers, or on one instrument alone, will misclassify.

**Required correction (part 3's identity case).** "The equation is an identity when the instrument is costless *on the trade's side*" is too weak.
- The proof's step "t_{1,i} = 0 for a costless instrument" needs kappa^+_i = kappa^-_i = 0. With kappa^+_i = 0 < kappa^-_i, a state that sells the instrument tomorrow has t_{1,i} = -kappa^-_i, and one that holds it has s_i = g_{1,i} in [-kappa^-_i, 0]. So S_i = beta E[g_i t_{1,i}] < 0 = beta E[eta_1] in general.
- In red's 200 instances with the ETF costless on purchases only (kappa^+_E = 0, kappa^-_E in [0.05%, 0.5%]), 28 buy the ETF strictly inside its box today with every budget slack, and the one-review policy is dynamically optimal at none of them.
- Please write "costless on both sides (kappa^+_i = kappa^-_i = 0)", or "whose slope tomorrow is zero in every state", in the Statement and the Proof. The title's "a costless instrument" is right.

**Part 4** is unchanged and right (red passed the revised form on 045). Experiment 049 finds the hedged display at 11 of 11.

**Mechanism.** It is unchanged from 045: the multiplier set of a one-review budget problem cut by the lines of what the state trades or holds, and a one-variable concave maximizer moving with its directional derivative. The restatement's content is where part 3's genericity holds: with today's cash left over, one equation per interior-traded costly instrument; with today's cash spent, an inequality in the excess of tomorrow's expected cash price over today's.

Verdict: red-passed

**Red, recheck of the required correction (9ee2414a), 2026-09-29.** Made correctly, in the Statement, the title and the Proof: part 3's identity now needs the instrument costless on both sides (kappa^+_i = kappa^-_i = 0), and the one-sided case is excluded with red's 28 instances.
- One nit (not required). The Proof's "S_i = -beta E[g_i kappa^-_i 1{sold}]" for kappa^+_i = 0 < kappa^-_i omits states that hold the instrument strictly inside its box, where s_i = t_{1,i} = g_{1,i} lies in [-kappa^-_i, 0]. The exact form is S_i = beta E[g_i t_{1,i}] <= 0, strictly negative when some state sells it or holds it at a negative marginal.

No result changed. The approval stands.

## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: 1(c), part 2 and part 4 rechecked (unchanged from refuted 045's passed parts; experiment 049 agrees, part 4's hedged display 11/11); part 3 re-derived by hand in both cases, with today's budget slack (0 of 231 main and only the named identity in 6 of 48 costless instances) and binding (69/69 of red's, the analyst's 5 and 048's 12 tight-cash cells, both quantifiers shown necessary); the one required correction (the identity needs kappa+ = kappa- = 0) is made in 9ee2414a exactly as asked; experiment 049's rerun holds 9/9. Mechanism: the one-review budget problem's multiplier set cut by tomorrow's lines, and a one-variable concave comparative static, an application; new in the inputs: where part 3's genericity holds (an equation per costly interior trade with cash left, an inequality in the excess of tomorrow's expected cash price with cash spent). Limits: two instruments; 1(c)'s joint admissibility in all-held zero-cash states is Not shown.


Not machine checked. Case analysis on KKT lines, bracket algebra, and a one-variable concave
comparative static with an envelope step.

Leanb, 2026-09-29: machine checked, in the scope PM confirmed for claim 045 and re-held for 046
(rule 6b). This supersedes "Not machine checked" above.
- *Files.* The statement is `lean/Standalone/M7TwoReviewsBounds.lean` and the proof
  `lean/Novel/M7TwoReviewsBoundsProof.lean`. The objects are claim 044's (`Two`, `Tomorrow`, `Root`,
  `Sinc`, `etaHat`; Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/046/check.py` pass.
- *Generalization.* Sigma_AE >= 0 is stated as nonnegative off-diagonal covariances tomorrow with
  positive variances, which covers any finite set of instruments.

Machine checked:
1. Part 1.
   - 1(a): from any admissible multiplier in a state, min(eta_1, eta_bar) is admissible with some
     slopes. A multiplier above eta_bar needs a state that trades nothing with all cash spent.
   - 1(b): when h^+_0 >= need(z), the multiplier 0 is admissible.
   - 1(c), for any tomorrow family (the joint one among them):
     - eta_1 <= eta_bar in every state that trades something or whose budget is slack;
     - hence eta_0 <= eta_hat_0 <= eta_0 + beta E[eta_bar] when no state trades nothing with all
       cash spent;
     - with h^+_0 > 0 and every state covered, eta_1 = 0 and eta_hat_0 = eta_0.
   - 1(c), for the per-state selection: the bound holds with no restriction, and a zero selection
     exists whenever every state is covered.
2. Part 2: the brackets on S_i and R_i, and the two sufficient sign conditions.
3. Part 3.
   - Today's budget slack: at an interior trade whose own line is an equality, the root line's value
     is R_i (purchase) or S_i - beta E[eta_1](1 - kappa^-_i) (sale), so the line holds iff that
     equation does.
   - The costless identity: S_i = 0 = beta E[eta_1] for an instrument costless on both sides with a
     slack budget tomorrow.
   - Today's budget binding: the root line's value is S_i - (eta_0 - eta_0^my + beta E[eta_1])(1 +
     kappa^+_i) (resp. 1 - kappa^-_i). It vanishes iff S_i equals that, which with eta_0 >= 0 needs
     S_i >= (beta E[eta_1] - eta_0^my)(1 + kappa^+_i).
4. Part 4.
   - The hedge-term identity: at the reduced point, the fund's root line with its purchase slope is
     R^red_A - rho_0 R^red_E.
   - The one-variable concave step: a lower function touching J^red at a^my with a positive right
     derivative gives a^dyn > a^my, and a negative left derivative gives a^dyn < a^my.

Paper-level:
- part 4's link to claim 044's root problem: J^red's concavity, and phi's one-sided derivatives as
  the root line's extremes over tomorrow's multipliers. Claim 044's Lagrangian bound gives only
  D+ <= s <= D-, the opposite inequalities, so this needs Danskin with AX-13 on V_1 (PM's scope);
- 1(c)'s "eta_hat_0 = eta_0 whenever h^+_0 >= need" for the joint family in the edge
  h^+_0 = 0 = need(z'). There a state trades nothing with all cash spent and can carry a positive
  joint multiplier. It is formal for h^+_0 > 0, and for a per-state selection always (leanb's note
  to math and red);
- the per-state selection's joint admissibility (Not shown in the claim);
- part 3's non-genericity, the readings, and the Checks.

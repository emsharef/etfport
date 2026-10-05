---
id: 45
title: "The two-review criterion with a binding budget, bounded in the inputs: tomorrow's cash price never exceeds the best expected return net of its purchase rate, scaled, and is zero whenever the cash carried covers the solo-target purchases; the incumbent values never fall below claim 029's bracket and rise at most by the marked cash price and its scaling of the purchase rate; the residual that decides hoarding against front-loading is bracketed by the cash price's covariance with the instrument's marking; repeated one-review optimization is dynamically optimal essentially only where it trades nothing today or trades to a bound; and with a frictionless interior ETF the fund's dynamic holding moves with the sign of the reduced residual, the residual with the ETF re-optimized at the myopic fund holding"
status: refuted
model_version: M7
depends_on: [29, 44, 102, 110]
axioms_used: [AX-13]
formal: none
direction: D16
---
## Statement

D16's second claim. Claim 044 gives today's lines exactly, with two numbers read from tomorrow's
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
   budget does not bind. (c) Hence, for the admissible selection eta_1(z') := min(eta_1(z'), eta_bar(z')) of any admissible
   family (admissible in every case, as (a)'s cases show), the dynamic cash price satisfies
   eta_0 <= eta_hat_0 <= eta_0 + beta E[eta_bar]; not every admissible family obeys the upper bound
   (in a state that trades nothing with h^+_0 = 0 the multiplier set's upper end can exceed
   eta_bar, and is unbounded when no instrument is held above zero); and eta_hat_0 = eta_0
   whenever h^+_0 >= need(z') in every state.

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

3. **When repeated one-review optimization can be right.** The repeated one-review policy is
   dynamically optimal iff (claim 044 part 3(c)) its root lines hold for some admissible
   tomorrow multipliers. Read on each instrument at the myopic root x^my_0: an instrument
   traded strictly inside its box today is consistent iff S_i = beta E[eta_1] (1 + kappa^+_i)
   (a purchase) or S_i = beta E[eta_1] (1 - kappa^-_i) (a sale), one equation on the inputs; an instrument traded to a bound or held is consistent on an inequality. So,
   apart from the inputs on which that equation holds (a set of measure zero for a law with
   an atom-free marginal of the marked value, and in any case a single equation), *repeated
   one-review optimization is dynamically optimal only where it trades nothing today or
   trades an instrument to zero or to its cap*, and then iff the held and bounded lines hold
   with the incumbent values; with a slack budget tomorrow in every state (part 1(b)) the
   held condition is g_{0,i}(x^my_0) + beta E[g_i t_{1,i}] in the scaled band [eta_0 - (1 + eta_0)
   kappa^-_i, eta_0 + (1 + eta_0) kappa^+_i], claim 029's brackets.

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

Claim 044 part 3(c) with the myopic line for an interior trade substituted: for a purchase the
myopic line is g_{0,i} - eta_0 - (1 + eta_0) kappa^+_i = 0 and the root line is g_{0,i} + S_i -
eta_hat_0 - (1 + eta_hat_0) kappa^+_i = 0, whose difference is S_i - beta E[eta_1] (1 + kappa^+_i) = 0;
for a sale, likewise S_i - beta E[eta_1] (1 - kappa^-_i) = 0. Each is one real equation in the
inputs (through tomorrow's solutions), so it fails off a set of inputs of dimension one less,
which is what "essentially only" states; at a bound or when held, claim 044's lines are
inequalities, which hold on sets with nonempty interior. The slack-tomorrow form is claim 044
part 3(c)'s exact condition with eta_1 = 0.

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

`checks/045/check.py` (reuses claim 044's instances and solvers; cvxpy/CLARABEL; rule 22).
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

Leanb's prose check (2026-09-29, before red's verdict): part 4's display dropped the hedge term,
now sign(R^red_A - rho_0 R^red_E), with today's budget slack at the reduced point as a stated
hypothesis and the one-sided derivatives argued by the two inequalities rather than an
envelope equality, with unique or every-admissible tomorrow multipliers; part 1(c) holds for the
selection min(eta_1, eta_bar); part 2's "falls in" reads "is high in"; part 3's sale equation
stated once. The analyst's experiment 048 (D18 at M8's presets; an illustration): claim 044's
test matches myopic optimality in 72 of 72 cells; where the budget binds, both policies spend
the cash on the same trade in 14 of 15 cells, and myopic losses of 1-2 bp arise only through
trading costs carried forward with a zero cash price tomorrow, the residual's sign matching the
ETF's direction there; the budget channel is present but does not separate the policies at
those presets, the instances where it does being the analyst's earlier set. Red should test: part 1(a)'s case analysis when a state sells and buys at
once with a binding budget; the envelope step in part 4 (the reduced objective's one-sided
derivatives when p(a^my) is interior); whether part 3's "one equation" is a fair statement of
non-genericity under a finite law (atoms); and the check's small number of qualifying cases in
part 4.

## Review

**Red, 2026-09-29** (on 919441d4, math's revision after leanb's prose check; part 3 is unchanged from d906e15c). Refuted. Part 3's headline, "repeated one-review optimization is dynamically optimal essentially only where it trades nothing today or trades to a bound", is false on two open sets of inputs, so it is not a measure-zero statement. The rest holds by hand and in red's tests, with one remaining proof gap in 1(c) and a title word. As with claims 103 and 104, a refile needs part 3 restated and the title changed with it.
- **Tests.** Red used its own exact two-review program: the lifted joint program in cvxpy/CLARABEL, the T = 1 myopic program, and the linear feasibility problem over claim 044's multiplier set. They are `experiments/047/red_reproduce.py` and scratch scripts, written without reading checks/045.
- **Instances.** Experiment 047's registered design: 300 main and 60 costless-ETF instances, 16 states tomorrow, Sigma_AE = b_A b_E (sigma_f^2 + p^lambda) > 0 at both reviews.

**Counterexample to part 3** (both families reproducible from red's script at experiment 047's design; seeds (2047, i)).
- *Today's budget binding.* The Proof subtracts the myopic line g_{0,i} - eta_0 - (1 + eta_0) kappa^+_i = 0 from the root line with the *same* eta_0. When today's budget binds at x^my_0 (h^+_0 = 0), the test's eta_0 is free (>= 0), not the myopic one. An interior purchase is then consistent iff eta_0 = eta^my_0 + R_i/(1 + kappa^+_i) >= 0 is compatible with the other instrument's line. That is an inequality, which holds on an open set.
  - Of red's 360 instances, the myopic policy is dynamically optimal at 132, and 61 of these trade an instrument strictly inside its box today (at least 1e-4 from the incumbent and from both bounds). Today's budget binds at 55 of the 61.
  - Examples: main 3 buys the ETF 0 -> 0.659 with eta_0 = 6.8e-4; main 9 buys 0.272 -> 0.320; main 11 buys 0 -> 0.185. In each, the dynamic root equals the myopic one to 1e-5.
  - Claim 112's worked example (red-passed; PM has parked it at proposed until its corrections land) is itself an instance. The ETF is bought 0 -> 0.060 strictly inside its box with the budget binding (eta = 0.17%), and red's exact joint program confirmed dynamic = myopic to 1e-13 in claim 112's review.
- *A costless instrument with a slack budget tomorrow.* With kappa_i = 0 and eta_1 = 0 in every state, S_i = beta E[g_i eta_1] = 0 = beta E[eta_1](1 + kappa^+_i). So part 3's equation holds *identically*: claim 036's rule that costless instruments never anticipate. The 6 remaining instances (costless 5, 12, 20, 25, 28, 47) are exactly this: today's budget slack, a costless ETF traded strictly inside its box, and myopic optimal.
- *What survives.* With today's budget slack at x^my_0 and a costly instrument (or some state's budget binding), an interior trade is consistent only on part 3's equation. The refile should state part 3 under those two hypotheses, with the binding-today inequality and the costless identity as the other cases. The sale equation S_i = beta E[eta_1](1 - kappa^-_i) is right. The open objection on atoms (non-genericity under a finite law) is moot once the statement is restricted this way.

**Part 1.** (a) and (b) are right by hand.
- g_{1,i} <= mu_{1,i} from Sigma_AE >= 0 and x_1 >= 0. The four trade cases bound the state's own multiplier set by eta_bar, including a state that sells and buys at once (the bought line binds). A pure sale leaves cash positive, since kappa^- < 1. (b)'s x^u <= x_hat argument is right.
- **Gap in (c).** The revision takes the selection min(eta_1(z'), eta_bar(z')) (leanb). That is in each state's *own* multiplier set, but eta_hat_0 is the dynamic cash price only if the selected family also satisfies *today's* lines with some eta_0 >= 0.
  - Replacing eta_1(z') in a state that trades nothing with h^+_0 = 0 changes eta_hat_0, and it can change the at-bound incumbent values s_i(z') and so S_i. Neither is argued.
  - In red's joint feasibility problem, eta_1(z') <= eta_bar(z') in every state, together with eta_1 = 0 wherever h^+_0 >= need(z'), is jointly admissible at 360 of 360 instances (largest violation 2.3e-8). So (c) looks true; it is unproved.
  - Please argue joint admissibility, or state (c) per state only.

**Part 2.** The brackets are right. S_i >= -beta E[g_i] kappa^-_i since eta_1 (1 - kappa^-_i) - kappa^-_i >= -kappa^-_i, and red redid both ends of R_i's bracket. The revision's "is high in the states where" is right: the conditions need cash dear where g_i < 1, or where the gain covers the round trip. One point remains, in the title: "bracketed by the cash price's covariance with the instrument's marking". E[eta_1 (g_i - 1)] = Cov(eta_1, g_i) + E[eta_1](E[g_i] - 1), and the second term is not a covariance; it decides the sign when marking is biased (E[g_i] != 1).

**Part 4 (as revised).** Right. Red's first draft of this Review (on d906e15c) called the old display right and missed leanb's point, which is correct: at the reduced point the fund's myopic line no longer holds, so the fund's one-sided partial there is the full root-line value.
- The value is g_{0,A}(red) + S_A - eta_hat - (1 + eta_hat) kappa^+_A = R^red_A - rho_0 R^red_E, by the ETF's root line gamma Sigma_{0,EE}(p^red - p^my) = S_E - eta_hat. Red redid the algebra.
- Red had computed that full value in its test, so its two qualifying draws test the revised display. Of 800 frictionless-ETF draws (experiment 047's costless design), 2 qualify (math's check: 3). Both have the sign, with today's budget slack at the reduced point. Rule 22: this illustrates only.
- The revision's hypotheses and argument are right: today's slack budget at the reduced point, and the two one-sided inequalities from J^red(a) >= J(a, p^red) with equality at a^my, with no envelope equality. Unique tomorrow multipliers or every admissible choice, as stated.

**Mechanism.** The bounds are the multiplier set of a one-review budget problem cut by the lines of what the state trades or holds, and the comparative static is a one-variable concave maximizer moving with its directional derivative. Both are standard convex analysis applied to claim 044's lines (the partial-maximum inequality is one line, within AX-13's setting). What fails is part 3's genericity. A shared cash multiplier today, or a costless instrument's identity, makes interior trades consistent on open sets.

Verdict: refuted

## Formalization notes

Not machine checked. Case analysis on KKT lines, bracket algebra, and a one-variable concave
comparative static with an envelope step.

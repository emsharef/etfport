---
id: 47
title: "The reserve rule with one fund and one ETF (M8), in the inputs: today's ETF and cash differ from the one-review optimum through claim 044's two channels, and both make a reserve: with slack budgets the ETF-against-cash shift is the ETF's expected marked cost slope tomorrow over its curvature, with the fund fixed, held below the one-review level when the ETF is expected to be sold tomorrow and above when bought, at most the ETF's rate over its curvature; with cash short the budget channel adds a cash reserve; no reserve is needed when the revision cannot move the ETF out of its cost band tomorrow and the one-review leftover cash covers the largest solo-target purchase, both explicit in the revision's extreme values and the filter's gain, with a Gaussian tail-moment error bound; the reserve is carried in the ETF rather than in cash by the ETF's reserve premium; the funding need grows linearly in the alpha revision; and the cash carried never exceeds the largest need when any state prices cash"
status: formalized
model_version: M8
depends_on: [44, 46, 110]
axioms_used: [AX-13]
formal: lean/Standalone/M8ReserveRule.lean
direction: D19
---
## Statement

D19's first claim (LAB_REQUEST_2 item 1). Claims 044 and 046 say how tomorrow enters today's
decision: through the dynamic cash price eta_hat_0 = eta_0 + beta E[eta_1] and the incumbent
values S_i, and they bound both without solving tomorrow. This claim reads those results as a
*reserve rule*: which part of today's ETF and cash holdings beyond the one-review optimum is a
reserve against tomorrow's revision, when none is needed, whether it sits in the ETF or in
cash, how it and the need it answers grow with the inputs, and how large it can be. Both of
claim 044's channels make a reserve: with slack budgets, an ETF that tomorrow's revision is
expected to make the manager sell (to fund the fund) or buy carries its cost slope forward,
and the dynamic policy holds it below or above the one-review level by exactly that expected
marked slope over the ETF's curvature, the fund fixed, cash taking the difference (the
analyst's experiment 051 reading: material reserves with slack budgets, the fund unchanged,
zero reserve where the budget binds); with cash short, the budget channel adds the cash price.
The claim adds no new mechanism to claims 044 and 046; it sizes their objects in M8's inputs,
the revision's law included, and it names what is not monotone.

**Setting.** M8 (finite-law variant; the Gaussian law where said): one fund A and one ETF E,
cash, reviews 0 and 1, the funded budget at both, claim 044's notation. M8's filter: the belief
revision epsilon_1 = (epsilon^lambda, epsilon^alpha) has unconditional variances v^lambda = k^lambda_0
p^lambda_0 and v^alpha = k^alpha_0 p^alpha_0 (the gain times the prior variance), and tomorrow's
means are mu_{1,A} = mu_{0,A} + b_A epsilon^lambda + epsilon^alpha and mu_{1,E} = mu_{0,E} + b_E
epsilon^lambda; under the finite law the revision has finitely many values, with largest
epsilon^lambda_max, epsilon^alpha_max (the reference two-point law: k times the largest residual
return on the support). Write x^my_0 = (a^my, p^my) for the one-review optimum today (claim 110)
and h^my for its leftover cash, x^dyn_0 = (a^dyn, p^dyn) and h^dyn for the dynamic optimum's, g^min_i
for the smallest gross return of instrument i on the support, and, for post-trade holdings x_0
and a state z' (claim 046),

```
x_hat_i(z') = ( mu_{1,i}(z') - kappa^+_i )^+ / ( gamma Sigma_{1,ii} ),          need(z'; x_0) = sum_i (1 + kappa^+_i) ( x_hat_i(z') - g_i(z') x_{0,i} )^+,
N(x_0) = max_{z'} need(z'; x_0)                                                (the largest funding need tomorrow),
F(x_0) = h^+_0(x_0) + (1 - kappa^-_E) g^min_E p_0                                   (today's funding capacity: cash plus the ETF's worst-case liquidation),
Res = F(x^dyn_0) - F(x^my_0)                                                      (the reserve, signed).
```

1. **What the reserve is.** By claim 044 part 2, today's ETF line and the budget are the
   one-review ones with the cash price eta_hat_0 in place of eta_0 and the ETF's marginal raised
   by S_E; by claim 044 part 3(a), with eta_1 = 0 in every state these reduce to claim 029's
   slope terms. So the dynamic ETF and cash holdings differ from the one-review ones through
   two channels, and both are reserves: (a) the *cost-channel reserve*, present with slack
   budgets, S_E = beta E[g_E t_{1,E}] with t_{1,E} the ETF's cost slope tomorrow (-kappa^-_E where
   the revision makes the manager sell it, kappa^+_E where buy it, its held marginal between),
   which moves the ETF below the one-review level when its marked slope tomorrow is expected
   negative (sold, or held near its sale edge) and above when expected positive (bought, or held
   near its purchase edge), cash taking the difference (red's correction: the sign and size read
   through E[g_E t_{1,E}] including held marginals, not through the probability of a trade); and (b) the *budget-channel reserve*, the eta_1
   terms, present iff some state prices cash at the one-review root for every admissible
   family, which raises every threshold today and keeps cash. Res, the capacity difference,
   can have either sign (front-loading a fund purchase reduces the capacity), so "reserve"
   means the signed difference, positive when held.

2. **When no reserve is needed.** No reserve is needed iff both channels vanish: (a) the
   ETF's expected marked cost slope tomorrow is zero, E[g_E t_{1,E}] = 0, the exact condition;
   an ETF idle strictly inside its box tomorrow carries its held marginal g_{1,E}(x_1) as the
   slope (claim 044 part 2's reading), so idleness in every state gives E[g_E g_{1,E}], zero only
   when the marked held marginals average to zero (leanb's point); sufficient conditions in
   the inputs are the ETF held at its tomorrow target with marginal zero in every state, the ETF
   idle at zero in every state with a nonpositive marginal there (then zero is an admissible
   slope; the analyst's experiment 052: 126 of 135 such instances), or the ETF costless on both
   sides (then t_{1,E} = 0 whatever tomorrow does); idleness itself holds
   when the revision cannot move the ETF's marginal out of its cost band (|b_E| times the
   premium revision's extreme, plus the fund's marked change times gamma Sigma_AE, below the
   band's half-width (kappa^+_E + kappa^-_E)/2 around its centre), which bounds the shift of part
   3(b) by beta E[g_E |g_{1,E}|]/(gamma Sigma_EE) rather than removing it; and (b) the budget channel: at the one-review root, if h^my >
   0 and h^my >= N(x^my_0), then eta_1(z') = 0 in every state for every admissible family of the
   myopic policy's tomorrow problems (claim 046 part 1(b)-(c)) and no budget reserve is needed
   there; at the dynamic root the same condition, h^dyn > 0 and h^dyn >= N(x^dyn_0), makes the
   dynamic policy's budget channel vanish; and, as a certificate in the inputs, if the root x^s
   of claim 044's lines with eta_1 = 0 in every state (claim 029's lines) has h^s > 0 and h^s >=
   N(x^s), then x^s is the dynamic optimum and its budget channel is absent (leanb's
   correction: the condition at the one-review root alone does not carry to the dynamic root,
   which can front-load a purchase and leave its cash below its own need). For (b), in the
   inputs, since need is nondecreasing in the revision through the solo targets,

   ```
   N(x^my_0) <= (1 + kappa^+_A) [ ( mu_{0,A} + b_A epsilon^lambda_max + epsilon^alpha_max - kappa^+_A )^+ / (gamma Sigma_{1,AA}) - g^min_A a^my ]^+
              + (1 + kappa^+_E) [ ( mu_{0,E} + b_E epsilon^lambda_max - kappa^+_E )^+ / (gamma Sigma_{1,EE}) - g^min_E p^my ]^+,
   ```

   so cash at least this right side (at whichever root the condition is taken) suffices: the
   policy's leftover cash covers the fund's and the ETF's largest solo-target purchases at the
   revision's extreme. Under the Gaussian law the support is unbounded; at a root x_0 with cash
   h > 0, with the event U = {need(z'; x_0) > h} (uncovered states), the budget channel's terms
   are bounded by tail moments (claim 046 parts 1(a) and 2, for every admissible family since
   h > 0):

   ```
   eta_hat_0 - eta_0 = beta E[eta_1] <= beta E[ eta_bar(epsilon) 1_U ],     eta_bar(epsilon) = max_i ( mu_{1,i}(epsilon) - kappa^+_i )^+ / (1 + kappa^+_i),
   S_i <= beta E[ g_i t_{1,i} 1_{U^c} ] + beta E[ g_i ( eta_bar + (1 + eta_bar) kappa^+_i ) 1_U ],
   ```

   eta_bar affine in epsilon on its positive part, so the tail terms are explicit Gaussian tail
   moments; treating the budget reserve as unneeded (using the slack-tomorrow lines) errs in
   each purchase threshold today by at most (1 + kappa^+_i) times the first bound and in each
   sale threshold by at most (1 - kappa^-_i) times it (the thresholds being eta_hat_0 +- (1 +
   eta_hat_0) kappa, red's factor), and in each incumbent value by at most the second's tail term
   (measured against the slack-tomorrow value beta E[g_i t_{1,i}]; a stated error bound, the regime
   being P(U) small). Under the Gaussian law this is conditional on claim 044's lines holding
   there, which claim 044 proves for the finite law only (claim 112's Not shown: the Gaussian
   transfer on {x^-_1 >= 0}); under the finite law the same bound holds with U the uncovered
   states of the support.

3. **ETF against cash, and the size of the cost-channel reserve.** (a) At the dynamic optimum
   with today's budget slack, the ETF's root line (claim 044 part 2) differs from its
   one-review line by the *reserve premium*

   ```
   Pi_E = S_E - beta E[eta_1] (1 + t_{0,E}) = beta E[ eta_1 ( g_E (1 - kappa^-_E) - 1 - t_{0,E} ) 1{sold tomorrow} + eta_1 ( g_E (1 + kappa^+_E) - 1 - t_{0,E} ) 1{bought} + ( g_E g_{1,E} - eta_1 (1 + t_{0,E}) ) 1{held inside} ]
          - beta E[ g_E kappa^-_E 1{sold} ] + beta E[ g_E kappa^+_E 1{bought} ],
   ```

   t_{0,E} the ETF's slope today (kappa^+_E if bought, -kappa^-_E if sold, in between if held),
   in the three regimes displayed (an ETF held untraded at zero or at its cap tomorrow
   contributes s_E in the interval cut by its one-sided line, claim 044 part 2's reading), and
   the direction is read at the dynamic root with the fund fixed at a^dyn: there the ETF's
   one-review line takes the value -Pi_E (the ETF traded strictly inside its box), so by the
   one-review objective's concavity in p the one-review ETF holding at a^dyn lies below the
   dynamic one iff Pi_E > 0 and above iff Pi_E < 0 (red's nit on the point of reading; the joint
   move with the fund free can reverse by substitution, claim 046 part 4). Reading: the reserve is carried in the ETF rather than in
   cash when, in the states where cash is dear (eta_1 > 0) and the ETF is liquidated, its marked
   proceeds net of the sale rate, g_E (1 - kappa^-_E), exceed the unit's cost today, 1 + t_{0,E},
   by enough to cover the round-trip cost paid where it is sold with cash not dear; in cash
   otherwise. An ETF bought today only to be sold tomorrow in every state carries the reserve
   iff E[eta_1 (g_E (1 - kappa^-_E) - 1 - kappa^+_E)] >= E[g_E] kappa^-_E, explicit in the inputs given
   tomorrow's cash-price law (bounded by part 2's tail moments). (b) *The size, with slack
   budgets.* With eta_0 = 0 and eta_1 = 0 in every state, the fund held at its one-review holding
   a^my, and the ETF strictly inside its box at both the one-review optimum and the joint
   optimum with the fund so fixed,

   ```
   p^fix - p^my = [ S_E - (t^fix_{0,E} - t^my_{0,E}) ] / (gamma Sigma_{0,EE}),     S_E = beta E[ g_E t_{1,E} ],
   ```

   with t^fix, t^my the ETF's cost slopes today under the two and t_{1,E} the ETF's slope in the
   joint (fixed-fund) optimum's own tomorrow, so the display is a fixed-point condition in p^fix,
   not a one-shot size read from the one-review tomorrow (whose S_E can be off by a factor near 2;
   the analyst's experiment 053); when the ETF trades the same way
   today under both (both bought or both sold) the shift is S_E/(gamma Sigma_{0,EE}) exactly: the
   ETF's expected marked slope tomorrow over its curvature, negative (cash held instead)
   when the ETF is expected to be sold or held near its sale edge, positive (the ETF bought
   early) when expected to be bought or held near its purchase edge; and there is *no shift* for
   an ETF held untraded inside today's band whose band absorbs S_E: with t^my inside
   (-kappa^-_E, kappa^+_E) and t^my + S_E in [-kappa^-_E, kappa^+_E], the pair p^fix = p^my with
   t^fix = t^my + S_E satisfies the joint line, so p^fix = p^my. *The rule's computation* (the
   procedure's step): fix the fund at a^my; if the one-review root holds the ETF untraded and
   t^my + S_E stays in the band, hold it; otherwise solve g_{0,E}(a^my, p) + S_E(p) - t_{0,E}(p) = 0
   for p, with S_E(p) read from the tomorrow of the point p itself (a fixed point; a damped
   iteration converged in a few tens of steps in every cell of experiments 053 and 054, at
   most 21), and never from the one-review tomorrow. In every
   case

   ```
   |p^fix - p^my| <= [ beta max(kappa^+_E, kappa^-_E) E[g_E] + kappa^+_E + kappa^-_E ] / (gamma Sigma_{0,EE}),
   ```

   the cost-channel reserve's maximum in the inputs. Its size is set by where tomorrow's
   marginal sits in the ETF's band (the marked slope including held marginals, red's
   correction), whether the ETF is moved by the fund's need or by its own rebalancing (claim
   029's own-trade channel; experiment 053's all-ETF cells, where the fund never trades
   tomorrow), and by the ETF's rates; the ETF's rate over its
   curvature decides materiality (the analyst's fixed-income cells, 50 bp over gamma Sigma_EE of
   about 0.05, give about 0.1, as observed).

4. **How the need grows, and what does not.** The fund's need in a state, when its purchase
   is active, is affine in the alpha revision with slope

   ```
   d need_A / d epsilon^alpha = (1 + kappa^+_A) / (gamma Sigma_{1,AA}),
   ```

   so N grows with the revision's scale sqrt(v^alpha) at that rate through epsilon^alpha_max
   (and with epsilon^lambda through b_A); in the fund's purchase rate, d need_A / d kappa^+_A =
   (x_hat_A - g_A a_0) - (1 + kappa^+_A)/(gamma Sigma_{1,AA}), the cash per unit rising while the
   target falls, of either sign; and an ETF reserve that funds a need n must be n / ((1 -
   kappa^-_E) g^min_E) units, growing in the ETF's sale rate by the factor 1/(1 - kappa^-_E), while
   the sale rate also lowers Pi_E through the liquidation term, pushing the reserve toward
   cash. The reserve Res itself is not monotone in these inputs (it is negative where the
   dynamic policy front-loads the fund; the check's illustration); only the need is.

5. **The maximum.** The cost-channel reserve is bounded by part 3(b)'s display. For the budget
   channel: if some state prices cash at the dynamic optimum for every admissible family (such
   families exist by AX-13, claim 044 part 2), then h^dyn <= N(x^dyn_0), strictly when h^dyn > 0:
   the cash carried never exceeds the largest funding need tomorrow (the edge h^dyn = 0 = N
   being where a positive multiplier is carried harmlessly). Reading for the ETF part: an ETF reserve beyond N(x^dyn_0)/((1 - kappa^-_E) g^min_E)
   units is not a reserve (its liquidation could not be used), so the ETF held above the
   one-review level for the budget's sake is at most that; the ETF may be held above it for
   its own return (claim 029's channel), which is not a reserve.

**One sentence without model nouns.** Today's cheap-instrument and cash holdings differ from
the one-review choice through what each holding will be worth tomorrow and the price of cash
then: an instrument the revision is expected to make one sell is held below its one-review
level, and cash instead, by its expected sale cost over its curvature, and above when expected
to be bought, which is the whole reserve while cash is not short; no reserve is needed when the
revision cannot move the instrument out of its cost band and the cash the one-review choice leaves covers the largest
purchase any revision could call for, which is explicit in the revision's range and the
learning gain, and under a Gaussian revision the error of ignoring the reserve is a tail
moment; the reserve sits in the cheap instrument when its expected proceeds in the states where
cash is dear cover its round trip and in cash otherwise; the need grows linearly in the
revision at the purchase scale over the curvature, and the reserve held in the instrument must
be larger by its sale-cost factor; and cash is never carried beyond the largest need.

## Proof

### 1. What the reserve is

Claim 044 part 2 gives today's lines with eta_hat_0 and S_i; with eta_1 = 0 in every state
eta_hat_0 = eta_0 and s_i = t_{1,i}, claim 029's slopes (claim 044 part 3(a)). The two channels are
the two sets of terms; the budget channel is present iff some eta_1(z') > 0 in every admissible
family (if some family has eta_1 = 0 throughout, the lines hold without budget terms). F is
affine in (x_0, h^+_0), so Res is well defined and signed.

### 2. When no reserve is needed

Claim 046 part 1(b): if h^+_0 >= need(z') then eta_1(z') = 0 is admissible in that state; with
h > 0 leanb's argument in claim 046 part 1(c) makes it the only admissible value (a positive
multiplier in a covered state forces no trade and all cash spent, but the cash there is h > 0).
Applied at the myopic root this gives the one-review statement; applied at the dynamic root,
the dynamic one; the two roots differ (claim 029's slopes can front-load a purchase), so
neither implies the other. The certificate: x^s solves claim 044's lines with eta_1 = 0, and if
h^s > 0 and h^s >= N(x^s) then eta_1 = 0 is admissible in every state at x^s (part 1(b)), so the
whole family (eta_0 = 0 if h^s > 0, eta_1 = 0, the slopes of the lines) satisfies AX-13's
conditions at x^s, which is therefore the joint optimum (sufficiency). The bound on N: x_hat_i(z') is nondecreasing in mu_{1,i}(z'), which is affine
in the revision with positive coefficients (b_A, 1, b_E > 0), so the largest solo target is at
the largest revision, and g_i(z') x_{0,i} >= g^min_i x_{0,i}; summing gives the display. Gaussian
law: at a root with cash h > 0, eta_hat_0 - eta_0 = beta E[eta_1] for the root's family; in a
covered state the multiplier is zero (above), and in an uncovered one eta_1 <= eta_bar for every
family (a larger multiplier needs nothing traded and all cash spent, impossible with h > 0), so
E[eta_1] <= E[eta_bar 1_U]; the incumbent-value bound splits S_i over U and U^c, with claim 046
part 2's upper end on U and the slack value beta E[g_i t_{1,i}] on U^c; eta_bar is the maximum of two functions affine in epsilon on their positive
parts, so its tail moment under a Gaussian epsilon is explicit.

### 3. ETF against cash, and the size

(b) With eta_0 = 0 = eta_1, claim 044 part 2's ETF line at the joint optimum with the fund fixed at
a^my reads g_{0,E}(a^my, p^fix) + S_E - t^fix_{0,E} = 0 (the ETF interior), and the one-review line
g_{0,E}(a^my, p^my) - t^my_{0,E} = 0; since g_{0,E}(a, p) = mu_{0,E} - gamma (Sigma_{0,AE} a + Sigma_{0,EE} p),
subtracting gives gamma Sigma_{0,EE}(p^fix - p^my) = S_E - (t^fix - t^my), the display; with the
same slope the bracket is S_E; |S_E| <= beta max(kappa^+_E, kappa^-_E) E[g_E] since t_{1,E} lies in
[-kappa^-_E, kappa^+_E], and |t^fix - t^my| <= kappa^+_E + kappa^-_E, giving the bound. (a) Claim 044 part 2's ETF line at the dynamic root, minus the one-review line (both with eta_0 = 0
when today's budget is slack), is S_E - beta E[eta_1](1 + t_{0,E}) = Pi_E; expanding S_E = beta E[g_E
s_E] with s_E by tomorrow's regime (claim 044 part 2's reading) gives the display; the direction
with the fund fixed is claim 044 part 3(c)'s one-sided derivative statement; the reading
groups the terms by whether cash is dear. The bought-to-sell case has t_{0,E} = kappa^+_E and
1{sold} = 1.

### 4. Growth

need_A = (1 + kappa^+_A)(x_hat_A - g_A a_0)^+ with x_hat_A = (mu_{1,A} - kappa^+_A)/(gamma Sigma_{1,AA}) on
the active set, and mu_{1,A} = mu_{0,A} + b_A epsilon^lambda + epsilon^alpha; the derivatives follow. The
ETF's liquidation raises (1 - kappa^-_E) g_E per unit, at least (1 - kappa^-_E) g^min_E, so n units of
need require n/((1 - kappa^-_E) g^min_E) units. Non-monotonicity of Res: it is a difference of two
optima's capacities and is negative in the check's instances (front-loading), so no monotone
statement is made.

### 5. The maximum

If h^dyn >= need(z') for every z' and h^dyn > 0, claim 046 part 1(b) with leanb's argument gives
eta_1 = 0 in every state for every admissible family; contrapositively, if some state prices
cash for every admissible family, then h^dyn < need(z') for some z', that is, h^dyn < N(x^dyn_0)
(with h^dyn = 0 the statement is h^dyn <= N, trivially; the edge h^dyn = 0 = N is where a
positive multiplier can be carried harmlessly). The ETF reading is the unit count of part 4.

## Checks

`checks/047/check.py` (claim 044's joint solver on M8-shaped instances: four revision states,
the alpha revision's scale varied; rule 22). (i) Part 2: when the one-review leftover cash
covers the largest need, every tomorrow multiplier is zero for both policies (2 of 120
instances met the condition, the ETF's own solo-target purchase usually keeping N above h^my).
(ii) Part 5: at 120 dynamic optima with a binding state, the cash carried is below the largest
need. (iii) Part 3: the root lines hold at every dynamic optimum. (iv) Part 4 (illustration):
the fund's top-state need is active at every scale, and the dynamic reserve Res is negative
and slightly decreasing in sqrt(v^alpha) on one instance family (front-loading), which is why
no monotonicity of Res is claimed. (v) Part 3(b): with slack budgets and the fund fixed at its
one-review holding, the ETF's shift equals S_E/(gamma Sigma_EE) in 53 same-slope cases and
obeys its bound in all 67.

The analyst's experiment 053 (2026-09-30, D21, 84 cells; an instance report, rule 22): the
registered rule, the one-shot size S_E/(gamma Sigma_EE) with S_E from the one-review tomorrow, is
worse than the one-review policy in 16 of 84 cells (the one-review root holding the ETF inside
its band, where the (t^fix - t^my) term absorbs S_E; and S_E read at the wrong tomorrow, -0.0046
against -0.0027 at the joint point, the ETF idle there in every state); part 3(b)'s display
solved at its own point (the fund fixed at a^my, damped iteration) ties the dynamic ETF within
7e-8 in 84 of 84 cells, the dynamic fund equalling a^my within 4e-11. The analyst's experiment
054 (2026-09-30, D21, 144 new cells, the computation as stated): in the 93 cells with slack
budgets and the dynamic fund at a^my, the fixed point matched the dynamic ETF within 1.2e-8
(the band absorbing S_E and both holding the ETF in 16, the line leaving the band and both
moving in 17); Pi_E's sign at x^my disagrees with the ETF's direction in 12 cells, all with the
dynamic fund moving, as part 3(a)'s substitution clause allows; in the 24 fund-moving cells
the rule, holding a^my, leaves 0.10 to 0.26 bp, the fund step being D21's.

## Not shown

- Monotonicity of Res in the revision variance, the fund's purchase rate or the ETF's sale rate
  (part 4 shows the need's growth only; Res can be negative).
- A joint bound on the ETF part of the reserve (part 5's cash bound is proved; the ETF reading
  is a unit count).
- The Gaussian law beyond the tail-moment bound (claim 044's program is the finite-law one).
- Several funds (D20) and the procedure and comparison (D21).

## Prior art

Mechanism: claims 044 and 046 read as a reserve rule, with the funding need's dependence on
the revision made explicit through M8's filter.

General results checked: claims 044 and 046 (the channels and the bounds; cited, not
re-derived), 110 (the one-review optimum), 029 and 036 (the slack-budget channel);
`hakansson1971myopic` (wanted, not held: the conditions for myopic policies to be optimal in
multiperiod portfolio choice without costs, named); `boyd2017multiperiod` (full text; the
multi-period convex-optimization framing with a holding-cost and trading-cost separation, in
which a cash reserve appears as a constraint, not as this model's shadow price, named).

Searched: claims 029, 036, 044, 046, 110, 112; M8; experiments 047-049; LAB_REQUEST_2. This is a
claim because the request asks for the reserve sized in the inputs and the four conditions,
and the kill benchmark is claim 046's bounds restated with nothing sized: parts 2, 4 and 5 size
the need and the cash in the revision's range and the filter's gain, and part 3 states the
ETF-against-cash condition.

## Open objections

The analyst's experiment 051 reading (2026-09-30, before red's verdict; rule 22): in experiment
048's cells the material reserves (0.07-0.10 of wealth, fixed-income-style, ETF at 50 bp) occur
with slack budgets and the fund unchanged, as an ETF-against-cash swap in either direction, and
the reserve is zero where the budget binds; the larger revision variance raises them and the
ETF's rate decides materiality. The claim was revised on it: the cost-channel reserve of part
1(a) and its exact size in part 3(b) (about 0.1 at those inputs) are that pattern; the budget
channel is the second part. Leanb's prose check (2026-09-30, before red's verdict): part 2's
no-reserve statement is now made at each root separately, with the certificate through the
slack-tomorrow root; the Gaussian and finite-law bounds are taken at the root's own event, with
the incumbent-value error stated against the slack value; part 5 reads h^dyn <= N, strict when
h^dyn > 0, with the family's existence from AX-13; part 3's expansion says "in the three regimes
displayed". The analyst's experiment 052 (2026-09-30, at 5b6373ae, 346 instances; an instance report):
every part agrees where it applies (2(b) at the dynamic root and the certificate 177 of 177, the N
bound 346 of 346, 3(a)'s sign 62 of 62, 3(b)'s size 86 of 86 and bound 116 of 116, part 5 86 of
86); its report on 2(a)'s earlier gloss (an ETF idle strictly inside its box carries its held
marginal, so S_E is not zero: 85 of 145 such instances carry a reserve) is leanb's point, already
corrected, with the idle-at-zero case now named. PM's parking note (2026-09-30): red reviews the current text; red's corrections 3 and 4 are
in (the conditional Gaussian bound; the threshold factors, the sale threshold rising with the
dynamic cash price), and red's two nits are made: part 3(a)'s direction is read at the dynamic
root with the fund fixed, and the finite-cap regime is in the premium's expansion. Red's review
(cc8a26b9, on the original text 51d96a00, red-passed with four required corrections): (1) part 2's "for both policies" was false (red's seed 41: the cost channel spends
the one-review leftover cash and tomorrow binds), now stated at each root separately with the
certificate (made with leanb's point); (2) Res mixed both channels while part 1 called the
reserve the budget channel's part, now the two-part reading; (3) the Gaussian tail bound is
conditional on claim 044's lines under the Gaussian law; (4) the threshold errors carry the
factors (1 + kappa^+_i) and (1 - kappa^-_i). Leanb's second note (2026-09-30): 2(a)'s exact
condition is E[g_E t_{1,E}] = 0, idleness giving the held marginals, not zero; corrected. The
analyst's experiment 051 Deviation 1 (the ETF's
sale rate, an instance report): from the all-ETF start the ETF shift is -0.045, -0.084, -0.163 at
25, 50, 100 bp, doubling with the sale rate, and from the all-fund start the +0.07 to +0.09 shift
does not move with it, both as part 3(b)'s S_E/(gamma Sigma_EE) reads (the sold case carries
kappa^-_E, the bought case kappa^+_E). Red should test: part 2's step from the myopic root to the dynamic root (the
dynamic cash also covering the need when the myopic cash does); part 5's edge cases (h^dyn =
0); the sign conventions in Pi_E's expansion; and whether the Gaussian tail moment is the
right error object for the manuscript's procedure.

## Review

**Red, 2026-09-30** (on 51d96a00). Red-passed, with four required corrections: part 2's dynamic-policy clause is false, part 1's two definitions of the reserve disagree, part 2's Gaussian bound needs its conditions, and part 2's threshold error misses a factor. The title's statements survive under part 1's definition of "needed". Red worked each part by hand and tested parts 2 and 5 with its own solver, written without reading checks/047.
- **Solver.** The lifted joint program, the one-review program and claim 044's multiplier LP (`experiments/047/red_reproduce.py` and scratch scripts).
- **Instances.** Experiment 047's design: M8-shaped finite-law instances, one fund, one ETF, 16 states, Sigma_AE > 0.

**Required correction 1 (part 2: "eta_1(z') = 0 in every state for *both* policies").** This is false for the dynamic policy.
- Claim 046 part 1(b) applies at a policy's own root. The Proof's step, that the dynamic root's cash also covers its need because it differs from the one-review root only by claim 029's slopes, fails: the cost channel itself can spend the leftover cash today.
- *Counterexample* (red's experiment 047 generator, seed 41, cash set so the one-review root leaves 5% more than N(x^my_0)):
  - Inputs: rates kappa^+ = (0.38%, 0.09%), kappa^- = (0.02%, 0.21%), fund cap 0.25, incumbents (0.1307, 0), h^-_0 = 0.0688.
  - The one-review root is (0, 0.19145) and leaves 0.00788 >= N(x^my_0) = 0.00750.
  - The dynamic root is (0, 0.19933): it spends the leftover cash on the ETF, carries h^dyn = 0, and prices cash tomorrow for every admissible family (the LP with eta_1 = 0 is infeasible; the solver's largest eta_1 is 4.4e-4).
  - With tomorrow's budget dropped, the optimum has the same root and value, and its tomorrow is 0.00023 short of cash. So the cost channel spends the cash, and the budget then binds.
- *Frequency.* The same happens at 3 of 201 such instances with a 5% margin (seeds 41, 89, 217) and at 7 with a 0.1% margin. At 30 of the 201 (5% margin) the dynamic cash falls below the dynamic root's own need.
- *What survives.* Under part 1's definition ("needed" at the one-review root), h^my >= N(x^my_0) gives eta_1 = 0 in the one-review policy's tomorrow problems, so the title's "no reserve is needed" holds.
- *Please* restrict the conclusion to the one-review policy. State the dynamic one as "eta_1 = 0 at the dynamic root whenever h^dyn >= N(x^dyn_0)" (the condition checked at the dynamic root, as the Checks already do), and drop "the dynamic holdings differ from the one-review ones only through claim 029's slopes", which the counterexample breaks, if only by a small amount at the root.

**Required correction 2 (part 1: what Res measures).** Part 1 calls the reserve "the budget channel's part" of the dynamic ETF and cash holdings. But Res = F(x^dyn_0) - F(x^my_0) is the whole capacity difference, both channels included.
- In the counterexample above the difference is entirely claim 029's cost channel (the relaxed program gives the same root), yet Res != 0.
- Please either define the reserve as the difference between the dynamic optimum and the dynamic optimum with tomorrow's budget relaxed (the budget channel's part), or call Res the capacity difference and say that it mixes both channels. The check's "Res negative (front-loading)" reads the same either way.

**Required correction 3 (part 2's Gaussian bound: its conditions).** The bound applies claim 046 part 1(a) to eta_1(epsilon) under the Gaussian law. But claims 044 and 046 are proved on the finite tree, and claim 112 lists the Gaussian dynamic problem's existence and regularity, and review-1 feasibility off {x^-_1 >= 0}, as Not shown. With today's cash spent, review 1 can be infeasible. Please state the bound conditionally: given multipliers satisfying claim 044's lines under the Gaussian law, on the event {x^-_1 >= 0}. Or state it for a finite-law approximation. This answers the open objection on whether the tail moment is the right error object: it is, once those conditions are stated.

**Required correction 4 (part 2: "errs in every threshold today by at most that amount").** The purchase threshold moves by beta E[eta_1](1 + kappa^+_i), and the sale threshold by beta E[eta_1](1 - kappa^-_i), in the same direction: up. So the error bound for the purchase threshold is beta E[eta_bar 1{need > h^my}](1 + kappa^+_i), not the displayed amount. (Red found the same slip in claim 044 part 3(a) and the manuscript's Section 6.)

**Checked and right.**
- *Part 2's display.* N(x^my_0) is at most the right side at 300 of 300 instances. By hand, x_hat_i is nondecreasing in mu_{1,i}, which is affine in the revision with positive coefficients, Sigma_1 is deterministic, and g_i x_{0,i} >= g^min_i x_{0,i}.
- *Part 3's Pi_E* expansion, term by term, with t_{0,E} and the sold, bought and held-inside regimes; the sign conventions are right. The bought-to-sell condition is Pi_E >= 0 with every state selling.
- *Part 4's* derivatives, and the ETF unit count n/((1 - kappa^-_E) g^min_E).
- *Part 5.* Right by hand: the contrapositive of claim 046 1(b) with leanb's h > 0 argument. At the h^dyn = 0 = N edge, eta_1 = 0 is admissible state by state (with Sigma_AE >= 0 a held instrument's marginal is at most kappa^+), so the premise fails. At 84 of 84 instances priced for every family, h^dyn < N(x^dyn_0).

**Nits.**
- Part 3 says the ETF "moves from the one-review one in the direction of Pi_E's sign with the fund fixed", but not at which point. At the dynamic root with the fund fixed at a^dyn, the one-review line equals -Pi_E (with the ETF traded interior there), and the one-review objective's concavity in p gives the direction. Please say so.
- Pi_E's display omits an ETF held at a finite cap tomorrow (M8 allows one), where s_E is an interval.

**Mechanism.** Claims 044 and 046 read as a reserve rule, with the need's growth made explicit through M8's filter, an application; the kill benchmark's "restated with nothing sized" is escaped by parts 2, 4 and 5's sizing. Prior art as named.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-30): red's verdict (cc8a26b9) is on the original text 51d96a00. The Statement has since been restructured (e9d61b97, 5b6373ae, 0ca9b3f3): the two-part reserve with part 3(b)'s exact cost-channel size, 2(a)'s new condition, and a new title. Red records a fresh verdict on the current text, including its corrections 3 and 4.

**Red, fresh verdict on the restructured text (main, after 6550797a), 2026-09-30.** Red-passed, with one required correction to the cost-channel reserve's readings. The formulas are right; two sentences interpreting them are contradicted by the claim's own exact size.
- **Solver.** Red's own lifted joint program with a fixed-root-fund variant, and claim 044's multiplier LP (`experiments/047/red_reproduce.py`, `experiments/049/red_reproduce.py`, scratch scripts).
- **Instances.** Experiment 047's design, and experiment 048's cells.

**Red's four earlier corrections, on the current text.**
1. *Part 2(b)* is stated at each root, with a certificate. It is right by hand: the slack-tomorrow root x^s with h^s > 0 and h^s >= N(x^s) has a fundable tomorrow (claim 046 part 1(b), Sigma_AE >= 0), so it is the dynamic optimum. Red's seed 41 fails the certificate (h^s = 0), as it should.
2. *Part 1* now has two named parts of one reserve, and Res is the signed capacity difference.
3. *Part 2's Gaussian bound* is conditional on claim 044's lines under the Gaussian law, and the event U is the root's own.
4. *The threshold errors* carry (1 + kappa^+_i) and (1 - kappa^-_i).

Red's two nits (part 3(a)'s point of reading, and the finite-cap regime) and leanb's points (part 5's <=, the families' existence) are in.

**Part 2(a), new.** Right. The exact condition is E[g_E t_{1,E}] = 0, and idleness bounds the shift rather than removing it; this is the point red's rejected draft of this review made (23 of 23 idle instances with a shift up to 0.09). The three sufficient conditions are right by hand:
- *At the tomorrow target with zero marginal:* t_1 = 0.
- *Idle at zero with g_{1,E} <= 0:* the one-sided line admits t = 0.
- *Costless both ways:* t_1 = 0.

**Part 3(b), the exact size: confirmed.**
- By hand, the two ETF lines subtract to the display, and the bound follows.
- Across 23 instances of experiment 047's design with the same slope today, p^fix - p^my = S_E/(gamma Sigma_{0,EE}) to five decimals.
- At experiment 048's fixed-income all-ETF cells, with the ETF's sale rate at 25, 50 and 100 bp (experiment 051's Deviation 1), the fixed-fund shifts are -0.04511, -0.08380 and -0.16302, equal to S_E/(gamma Sigma_{0,EE}) to five decimals and to 051's -0.045, -0.084 and -0.163 (the fund free there). Cash does not change them (0.005 or 1.0).

**Required correction (the readings of the cost-channel reserve in parts 1(a) and 3(b)).** Two sentences attribute it to expected *trades* tomorrow.
- *Part 1(a):* the reserve "moves the ETF below the one-review level when it is expected to be sold and above when bought".
- *Part 3(b):* "its size grows with the probability that the revision makes the manager trade the ETF tomorrow".
- In experiment 051's own cells, the ETF is sold in 0 of 16 states tomorrow, yet the reserve is -0.084 at 50 bp and doubles with the sale rate. It is entirely the idle ETF's held marginal, g_{1,E} near its sale edge -kappa^-_E, which part 2(a) now names.
- Please read the sign and size through E[g_E t_{1,E}], the marked slope *including held marginals*: below the one-review level when the ETF is expected to be sold *or held near its sale edge*, above when bought or held near its purchase edge. The size is set by where tomorrow's marginal sits in the band, not by the probability of a trade. The "about 0.1" materiality reading stands (0.084).

**Parts 3(a), 4 and 5, and part 2's display,** are unchanged in substance and right (red's earlier review: N bound at 300 of 300, part 5 at 84 of 84).

Verdict: red-passed

**Red, recheck of the required correction (3add7ccd, d49dfe89), 2026-09-30.** Made correctly: parts 1(a) and 3(b) read the cost-channel reserve's sign and size through E[g_E t_{1,E}] including held marginals, and the probability-of-a-trade sentence is gone. The two additions are right by hand.
- *3(b) as a fixed point.* S_E depends on p through tomorrow's solutions, so the display is a condition at the fixed-fund optimum's own tomorrow, as red's exact confirmations computed it.
- *The no-shift case.* A held ETF has t^my = g_{0,E}(p^my) inside the band. If t^my + S_E stays in [-kappa^-_E, kappa^+_E], then p^fix = p^my with t^fix = t^my + S_E satisfies the joint line, the unique optimum with the fund fixed.
- The convergence of the damped iteration is an observation (experiments 053-054), which the text labels as such. No result changed. The verdict stands.

## Formalization notes

Approved 2026-09-30 by pm: Red's fresh verdict on the restructured text is sound: the four earlier corrections checked in place (part 2(b) at each root with the slack-tomorrow certificate, the two-part reserve, the Gaussian bound conditional on claim 044's lines, the (1 + kappa^+) factors); part 2(a)'s exact condition E[g_E t_{1,E}] = 0 and three sufficient cases right by hand; part 3(b)'s exact size p^fix - p^my = S_E/(gamma Sigma_EE) confirmed to five decimals on 23 instances and 051's cells (-0.045, -0.084, -0.163 at 25, 50, 100 bp); the one required correction (the reserve read through held marginals, not trades) made in 3add7ccd, and the rule's computation stated in d49dfe89 (S_E by fixed point at the rule's own root; no shift for an ETF untraded inside today's band), as experiment 053 showed necessary; experiment 052 agrees. Mechanism: claims 044 and 046 read as a reserve rule, with the need's growth made explicit through M8's filter, an application; D19's kill criterion not met (the reserve is sized in the inputs, beyond claim 046's bounds and Gallien et al.'s static zone). Limits: one fund, one ETF; the rule's policy form awaits experiment 054's registered confirmation; red records its recheck line on 3add7ccd and d49dfe89.


Not machine checked. Readings of claims 044 and 046 with elementary bounds on the need.

Leanb, 2026-09-30: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M8ReserveRule.lean` and the proof
  `lean/Novel/M8ReserveRuleProof.lean`. They use claims 044's and 046's objects and claim 046's
  proof lemmas (Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/047/check.py` pass.
- *Hypotheses.* M8's Sigma_AE > 0 satisfies claim 046's `Cov`. The revision enters as a hypothesis on
  tomorrow's means, bounded by its extremes (`RevisionMax`, `NeedBound`).

Machine checked:
1. Part 2.
   - At any root with h > 0 and h >= N(x_0), every tomorrow family has eta_1 = 0. This covers
     the one-review root, and the dynamic root in the approved form.
   - The certificate: a feasible policy with claim 044's lines at eta_1 = 0, h^s > 0 and
     h^s >= N(x^s) is the dynamic optimum (claim 044's `Sufficient`), with no budget channel.
   - N is bounded in the revision's extremes and g^min.
   - The finite-law budget channel at a root with h > 0: E[eta_1] <= E[eta_bar 1_U], and
     S_i <= beta E[g_i t_{1,i} 1_{U^c}] + beta E[g_i (eta_bar + (1 + eta_bar) kappa^+_i) 1_U], for
     every family.
   - The threshold errors, (1 + kappa^+) and (1 - kappa^-) times the bound.
2. Part 3.
   - The reserve premium Pi = S_i - beta E[eta_1](1 + t_0), as the root line minus the one-review
     line, with its expansion by state and the sold-everywhere form.
   - 3(b)'s cost-channel shift p^fix - p^my = [S_E - (t^fix - t^my)]/(gamma Sigma_EE), its bound,
     and the no-shift pair's line.
3. Part 4: the need's slopes in eps^alpha and in kappa^+ on the active set, and the ETF unit count.
4. Part 5: h <= N(x_0), strictly when h > 0, given that some family exists and every family
   prices cash somewhere.

Paper-level:
- part 1's definitions and readings;
- 3(a)'s direction: claim 046's one-variable step, once the one-review objective's derivative is
  identified with its line's value;
- 3(b)'s uniqueness and its fixed-point computation;
- 2(a)'s sufficient conditions and the idleness bound;
- the Gaussian tail moments (conditional on claim 044's lines, finite law only);
- Res's non-monotonicity;
- the Checks.

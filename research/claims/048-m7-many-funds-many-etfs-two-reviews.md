---
id: 48
title: "Many funds and many ETFs over two reviews with a funded budget: the two-number structure extends verbatim, one dynamic cash price for the whole menu and one incumbent value per instrument, with no coupling beyond the one-review one; with spanning frictionless ETFs the root's lines separate exactly, given the tomorrow numbers (the incumbent values and the cash price) evaluated at the optimum, into an ETF reserve problem, the frictionless exposure at the premium tilted by the ETFs' incumbent values net of the cash price, and a fund alpha problem, each fund's one-fund clip at its own incumbent value less the netting-weighted ETF incumbent values and the cash price on its net cash, with thresholds scaled by the cash price; the ETFs interact only through the factor covariance's inverse allocating the tilt; the two problems share the tomorrow numbers, a fixed point of the joint root, so they are not independent as at one review; with costly ETFs or ETFs at their bounds today even the lines fail to separate, as at one review, the two-scalar reduction surviving for one ETF only"
status: formalized
model_version: M7
depends_on: [44, 102, 104, 109, 110]
axioms_used: [AX-13]
formal: lean/Standalone/M7ManyFundsManyEtfsTwoReviews.lean
direction: D23
---
## Statement

D23's first claim (LAB_REQUEST_2 item 5). Claim 044 gave the two-review lines for one fund and
one ETF; its argument, one concave program over a polyhedron, is dimension-free, so the
structure extends to N funds and M ETFs verbatim (part 1): tomorrow enters today's decision
through one cash price for the whole menu and one incumbent value per instrument, and the
instruments couple only as they do at one review. The question whether spanning separates the
flexibility problem as it separates the one-review problem (claims 030, 104) is answered
exactly in part 2, with a qualification (red's correction): with spanning frictionless ETFs,
the root's *lines* are claim 104's 2a conditions at tilted inputs, so, *given the tomorrow
numbers* (S, eta_hat_0) evaluated at the optimum, they separate into an *ETF reserve problem*
(the frictionless exposure at a premium tilted by the ETFs' incumbent values net of the
dynamic cash price) and a *fund alpha problem* (each fund's clip at a residual alpha that
carries its own incumbent value, less the netting-weighted ETF incumbent values, less the cash
price on the net cash of a unit netted through the ETFs). The tomorrow numbers are read from
tomorrow's solutions, which depend on the whole root through the marked holdings and the
carried cash, so the two problems share them and are a fixed point of the joint root, not two
independent problems as at one review (claim 104): the separation is of the optimality
conditions, not of the optimization. The ETFs interact only through the factor covariance's
inverse, which allocates the reserve tilt across them (part 3). With costly ETFs or ETFs at
their bounds today even the lines fail to separate, as at one review (part 4): the obstruction
is claim 109's, not a new one, and claim 110's two-scalar reduction survives at the root for
one ETF.

**Setting.** M7's finite-law variant with N funds, M ETFs and K factors over two reviews, the
funded budget at both (claim 044's setting with the instrument index widened): loadings
B = [B^A; B^E], beliefs (lambda_hat, alpha_hat), predictive moments mu_t = (alpha_hat_t + B^A
lambda_hat_t, B^E lambda_hat_t - c^E), Sigma_t = B Sigma~_{f,t} B' + diag(V_t, Sigma_E), rates,
caps, incumbents, marking g(z'), trades u_0, u_1(z'), the objective and the lines' notation as in
claim 044; T_i the trade-sign slope sets; g_{t,i} the smooth marginals. For part 2: M = K, B^E
invertible with R = (B^E)^{-1}, netting vectors r_i = R'(B^A_i)' (claim 102), kappa_E = 0 (at both
reviews: the rates are review-independent in M7, lean's note), Sigma_E = 0, c^E = 0, ETF caps
slack today, V_0 diagonal with entries v_i, and today's budget slack at the dynamic root (eta_0 =
0), with the ETFs strictly inside their boxes there; tomorrow's budget, bounds and regimes
unrestricted.

1. **The two-number structure, any N and M.** The two-review problem is one concave program
   over a polyhedron, and x_0 with {x_1(z')} is optimal iff there are eta_0 >= 0, eta_1(z') >= 0
   (complementary to the two budgets) and slopes t_0, t_1(z') such that tomorrow's lines hold in
   every state (claim 109's part 1 form at each state) and, with the *dynamic cash price*
   eta_hat_0 = eta_0 + beta E[eta_1] and the *incumbent values* S_i = beta E[g_i (eta_1 + (1 + eta_1)
   t_{1,i})], every instrument's root line is

   ```
   g_{0,i}(x_0) + S_i - eta_hat_0 - (1 + eta_hat_0) t_{0,i}   = 0 inside its box,  <= 0 at zero,  >= 0 at its cap,   for every fund and every ETF,
   ```

   claim 044 part 2 with the index widened: N + M + 1 numbers read from tomorrow's solutions,
   the incumbent values pinned by tomorrow's regimes as there (the marginal score if held
   inside, the scaled thresholds if traded). Given (S, eta_hat_0), nothing couples the
   instruments in the root lines beyond the one-review coupling through g_{0}(x_0): the root
   lines are the one-review lines with mu_0 replaced by mu_0 + S and eta by eta_hat_0. The
   numbers (S, eta_hat_0) themselves depend on the whole root (through the marked holdings and
   the carried cash), as in claim 044.

2. **Spanning separates the root's lines.** Under part 2's hypotheses, with (S, eta_hat_0) the
   tomorrow numbers at the joint optimum, write

   ```
   lambda_hat^res = lambda_hat + R ( S_E - eta_hat_0 1 ),                                        (the premium tilted by the ETFs' incumbent values net of the cash price)
   alpha^res_i = alpha_hat_i + S_{A,i} - r_i' S_E - eta_hat_0 ( 1 - r_i' 1 ),                      (the fund's residual alpha)
   ```

   with 1 the vector of ones (each ETF unit costs one unit of cash; 1 - r_i' 1 is the net cash of
   a unit of fund i netted through the ETFs, claim 109). Then the dynamic root is

   ```
   exposure   b_0 = B' x_0 = ( gamma Sigma~_{f,0} )^{-1} lambda_hat^res,
   fund i     x_{0,i} = clip( x^-_{0,i},  ( alpha^res_i - (1 + eta_hat_0) kappa^+_i ) / (gamma v_i),  ( alpha^res_i + (1 + eta_hat_0) kappa^-_i ) / (gamma v_i) )  clipped to [0, bar x_i],
   ETFs       x^E_0 = R' ( b_0 - (B^A)' x^A_0 ),
   ```

   claim 104's 2a (Treynor-Black with the feasibility check) at the tilted inputs. So the root's
   optimality conditions separate given the tomorrow numbers: the *ETF reserve problem* is the
   frictionless exposure problem at lambda_hat^res, and the *fund alpha problem* is each fund's
   one-fund clip at alpha^res_i with its residual variance v_i and thresholds scaled by the cash
   price; the funds' lines see tomorrow through their own incumbent values, the netting-weighted
   ETF incumbent values (a fund whose by-product tomorrow's ETF trades will have to undo is
   charged those trades' values) and the cash price on their net cash; the ETFs' lines see it
   through S_E and eta_hat_0 alone. The numbers (S_A, S_E, eta_hat_0) are one fixed point of the
   joint root: moving the ETF holdings moves S_A through the marked holdings and the carried
   cash (red's test: a 1% move changes S_A by up to 3.8e-6 at the optimum), so the two problems
   are not solved independently; the exact statement is the displays, at the optimum's numbers.

3. **The ETFs' interaction.** The reserve tilt R(S_E - eta_hat_0 1) is allocated across the
   factors by (gamma Sigma~_{f,0})^{-1}, so the ETF holdings' departure from the untilted target is
   R' (gamma Sigma~_{f,0})^{-1} R (S_E - eta_hat_0 1) - (the funds' by-product change): the ETFs
   interact only through the factor covariance's inverse (an ETF whose incumbent value net of
   the cash price is high draws reserve into the factor directions it loads on, and pulls it
   from correlated ETFs), the many-ETF form of claim 047's one-ETF shift S_E/(gamma Sigma_EE).
   Since the ETFs are costless tomorrow too (the rates are review-independent), t_{1,E} = 0 in
   every state and S_E = beta E[g_E eta_1] always under part 2's hypotheses: the ETFs' incumbent
   values are the marked cash price alone, and the tilt is R (beta E[g_E eta_1] - beta E[eta_1] 1) =
   beta R E[(g_E - 1) eta_1]: the ETFs marked up in dear-cash states are held as the reserve. So
   the tilt is material only through the marking's deviation from one times the expected cash
   price (at most beta norm(R) max_z' |g_E(z') - 1| E[eta_1] in each coordinate); and a positive
   cash price with a frictionless ETF interior tomorrow means that ETF's marginal score equals
   the cash price (its line), while an ETF at zero tomorrow leaves nothing to sell (the
   analyst's experiment 056: eta_1 > 0 went with an ETF at zero or today's budget binding in
   19 of 22 tested cells, an observation on those cells only).

4. **Where separation fails.** With costly ETFs (kappa_E > 0, at both reviews), or an ETF at zero
   or its cap at the root, the root problem is claim 109's one-review problem at the tilted inputs, whose
   fund lines carry the ETFs' statuses (fixed ETFs' directions charged at their hedged risk,
   traded ETFs' pinned slopes at effective netting weights, the cash price on the net cash),
   decided by a finite complementarity across the ETFs: the separation fails exactly as at one
   review, and the obstruction is claim 109's, not a new one; with one ETF, claim 110's
   two-scalar reduction holds at the root (the root's exposure price and cash price, with
   alpha~_i + S_{A,i}), as claim 044 part 4(a) states. This part is a reading of claim 109's
   obstruction; the check's count with costly ETFs (15 of 15 draws) illustrates it and is not
   evidence in general.

**One sentence without model nouns.** With any number of positions and cheap instruments,
tomorrow reaches today's decision through one price of cash and one carried value per
holding, and nothing else; when the cheap instruments span the common risks and cost nothing
to trade, today's optimality conditions split as the one-period problem does, into an exposure problem
at a premium tilted by the instruments' carried values net of the cash price and a
position-by-position problem in which each position is credited with its own carried value,
charged the carried values of the instruments its side exposure will make one trade, and
charged the cash price on the cash it nets; but the carried values and the cash price are
set by the whole of today's holdings, so the two problems share them and are solved together,
not one after the other as in one period; the instruments share the reserve through the
inverse of the common risks; and when they cost to trade or sit at their bounds even the
conditions fail to split, as they do in one period.

## Proof

### 1. The two-number structure

Claim 044 part 1's argument is dimension-free: the lifted objective is concave (positive
definite Sigma_t, linear lifted costs), the constraints (boxes, marking identities, two cash
constraints) are linear in the lifted variables, the polyhedron is nonempty (no trade at the
root, and tomorrow no trade or the sale down to the cap of a holding marked above it) and
bounded (fund caps; ETFs bounded by cash), so an optimum exists and AX-13 applies (finite
objective). Stationarity in x_{1,i}(z') gives tomorrow's lines and in x_{0,i} the root line by
the same collection of terms as claim 044 proof part 2, for every i in 1..N + M: the derivative
of the root's score and cost, of eta_0 h^+_0, and of each state's cost and cash through the
marking, which sum to g_{0,i} - eta_hat_0 - (1 + eta_hat_0) t_{0,i} + S_i. The only coupling across
instruments is through g_0(x_0) = mu_0 - gamma Sigma_0 x_0, the one-review one.

### 2. Separation

By part 1 with eta_0 = 0, the root lines are those of the one-review problem with means mu_0 + S
and cash price eta_hat_0 (a constant in the lines). Claim 102's identity g_{0,i} = A_i + r_i' g_{0,E}
for a fund (Sigma_E = 0, c^E = 0: A_i = alpha_hat_i - gamma v_i x_{0,i}) holds since the ETFs span and
R B^E = I. The ETF lines with kappa_E = 0 and the ETFs strictly inside their boxes are equalities,
g_{0,E} + S_E - eta_hat_0 1 = 0, that is, B^E (lambda_hat - gamma Sigma~_{f,0} b_0) = eta_hat_0 1 - S_E,
so lambda_hat - gamma Sigma~_{f,0} b_0 = R (eta_hat_0 1 - S_E) and b_0 = (gamma Sigma~_{f,0})^{-1}
(lambda_hat + R (S_E - eta_hat_0 1)), the exposure display. Substituting g_{0,E} = eta_hat_0 1 - S_E
into a fund's line, alpha_hat_i - gamma v_i x_{0,i} + r_i' (eta_hat_0 1 - S_E) + S_{A,i} - eta_hat_0 -
(1 + eta_hat_0) t_{0,i} in the box's normal cone, that is, alpha^res_i - gamma v_i x_{0,i} - (1 +
eta_hat_0) t_{0,i} in the normal cone: the one-fund clip display (claim 102 part 3's rule with
the scaled thresholds, the fund's line being a concave one-variable condition). The ETF
holdings then follow from b_0 = (B^A)' x^A_0 + (B^E)' x^E_0. Sufficiency: the displayed point
satisfies all root lines with the given multipliers, hence is the joint optimum by part 1
(with tomorrow's lines holding at the corresponding tomorrow solutions).

### 3. The interaction

b_0 - b^TB_0 = (gamma Sigma~_{f,0})^{-1} R (S_E - eta_hat_0 1) with b^TB_0 the untilted target; x^E_0
= R'(b_0 - (B^A)' x^A_0) gives the display. With kappa_E = 0 the ETFs' slope sets tomorrow are {0},
so t_{1,E} = 0 in every state whatever tomorrow's regime, and S_E = beta E[g_E eta_1]; then
S_E - eta_hat_0 1 = beta E[g_E eta_1] - beta E[eta_1] 1 = beta E[(g_E - 1) eta_1] (eta_0 = 0).

### 4. Where separation fails

With kappa_E > 0 or an ETF at a bound, the ETF lines are inequalities or carry slopes, and the
substitution of part 2 gives claim 109's fund lines at the tilted inputs (its part 3's fixed and
traded forms), decided by the statuses' complementarity; claim 110's reduction for M = 1 is
its part 1-3 at the tilted inputs, as claim 044 part 4(a) already reads.

## Checks

`checks/048/check.py` (a general joint two-review solver for N funds and M ETFs; rule 22).
(i) Part 1: with N = 2 and M = 2, the root lines hold at 40 dynamic optima with one cash price
and per-instrument incumbent values (24 with a binding state tomorrow). (ii) Part 2: with
spanning frictionless ETFs today, a slack budget today and the ETFs interior, the dynamic
root's exposure equals the frictionless target at lambda_hat^res and the funds equal their
residual clips, in 6 of 6 qualifying draws (of 240, the rest failing a hypothesis or having an
incumbent value unpinned); with costly ETFs the separation fails in 15 of 15 (counted).

The analyst's experiment 056 (2026-09-30, two funds and two frictionless ETFs spanning two
factors; an instance report, rule 22): part 2's separated root holds wherever its hypotheses do,
to 1.5e-11 in the 6 qualifying cells of the registered grid of 32 and to 5.6e-13 in 4
supplementary cells; part 3's exposure identity to 3.5e-11 and its frictionless form to
4.6e-13; in the registered grid tomorrow's cash price is zero wherever the hypotheses hold, so
the reserve tilt is tested only in 3 supplementary cells (eta_1 up to 5e-3, tilt about 6e-6). No
instance the claim does not describe.

## Not shown

- ETF frictions today (part 4 records the failure; claim 111's residual bound applies to the
  root's tilted problem as a reading, not stated here).
- A bound on the ETFs' reserve allocation in the inputs beyond part 3's formula (which needs
  S_E and eta_hat_0 from tomorrow; claim 046's bounds apply per instrument).
- Several reviews; the Gaussian law (as in claim 044).
- The fund-by-fund comparative static with several ETFs (claim 046 part 4's caveat).

## Prior art

Mechanism: the joint two-review program's KKT conditions are claim 044's with the index
widened, and at frictionless spanning the root is claim 104's separated problem at inputs
tilted by the incumbent values and the cash price.

General results checked: claims 044 (the lines), 102 (the netting identity and the one-fund
clip), 104 (2a, the separation at one review), 109 (the fund lines with ETF statuses, the net
cash 1 - r_i' 1), 110 (the two-scalar reduction), 030 (the coordinates); AX-13 through claims
044 and 104; `garleanu2016dynamic` (named: the quadratic-cost multi-asset dynamic policy,
whose aim portfolio is D12's; no budget, no bound).

Searched: claims 030, 041, 044, 046, 104, 109-111; the D23 entry. This is a claim because the
request asks whether the structure extends and whether spanning separates the flexibility
problem, and the exact tilted separation with the ETFs' interaction through the factor
covariance's inverse is stated by no claim; the kill benchmark ("the index widened and nothing
from the ETFs' interaction") is escaped by parts 2-3.

## Open objections

None raised yet. Red should test: the cash-price term in the tilt (each ETF unit costing a
unit of cash: R eta_hat_0 1, and the fund's net cash 1 - r_i' 1); part 2's sufficiency
direction; and the interaction formula with the by-product change.

## Review

**Red, 2026-09-30** (on 7a192aff). Red-passed, with one required correction to what "separates" means. Red rederived parts 1-3 by hand and tested parts 1 and 2 with its own solver, written without reading checks/048.
- **Solver.** The lifted joint program for N = 2 funds and M = K = 2 spanning ETFs, two reviews, 6 states tomorrow with general moments and marking, and the funded budget at both reviews; cvxpy/CLARABEL, bp-scaled.
- **Multipliers.** eta_0 is the dual of today's budget, and eta_1(z') the state's dual over beta q(z'). Incumbent values are pinned by tomorrow's regimes.

**Part 1** is right. Claim 044's argument is dimension-free, and red redid the collection of the x_{0,i} terms. The root lines hold at 70 optima with pinned incumbent values, half with costly ETFs, to 6.4e-13.

**Part 2** is right by hand.
- With Sigma_E = 0 and c^E = 0, g_{0,i} = alpha_hat_i - gamma v_i x_{0,i} + r_i' g_{0,E} (claim 102's identity).
- The frictionless ETFs' root lines give g_{0,E} = eta_hat_0 1 - S_E, hence the tilted exposure and, substituted into each fund's line, the clip at alpha^res_i with thresholds scaled by (1 + eta_hat_0).
- Numerically, at 9 optima with frictionless ETFs, today's budget slack, the ETFs interior and tomorrow's budget binding, the exposure display holds to 2.8e-13, the fund clips to 1.8e-12 and the ETF holdings to 1.8e-12.

**Part 3's** algebra is right, including beta E[(g_E - 1) eta_1] for frictionless ETFs.

**Required correction (what "separates" means, in the title and parts 1-3).**
- *The claim.* It says the root "separates exactly into an ETF reserve problem ... and a fund alpha problem", that "the ETFs see [tomorrow] through S_E and eta_hat_0 alone", and that "the root problem is the one-review problem with mu_0 replaced by mu_0 + S".
- *The issue.* S_A, S_E and eta_hat_0 are read from tomorrow's solutions, which depend on the whole root, funds and ETFs together, through the marked holdings and the carried cash. So the displays are optimality conditions that decouple *given* (S, eta_hat_0), and those numbers are a fixed point of the joint root. They are not two problems that can be solved independently.
- *Test.* With the funds fixed at the optimum, moving the ETF holdings by 1% changes the funds' incumbent values S_A by up to 3.8e-6 (median 1e-6, 9 cases): small, but the coupling is there.
- *Please* say that the root's *lines* separate given the tomorrow numbers (S, eta_hat_0) evaluated at the optimum, as claim 044's "one-review problem with mu_0 + S" should also be read. One-review separation (claim 104) is a decomposition into independent problems; here the two problems share S and eta_hat_0.

**Nits.**
- The Setting says kappa_E = 0 "today" with "tomorrow unrestricted", but M7's rates are the same at both reviews. So under part 2's hypotheses t_{1,E} = 0 always, and part 3's "with frictionless spanning ETFs tomorrow as well" is automatic. Either say so, or allow review-dependent rates explicitly.
- Part 4's "15 of 15 draws" is a count, not evidence of failure in general. Part 4 is a reading of claim 109's obstruction, which is fine as stated.

**Mechanism.** Claim 044's dimension-free KKT lines plus claim 102's netting identity (Treynor-Black at tilted inputs, claim 104's 2a): an application. New in the inputs: the reserve tilt R(S_E - eta_hat_0 1) allocated by the factor covariance's inverse, and the fund's residual alpha net of the netted ETF incumbent values and the cash price on its net cash.

Verdict: red-passed

**Red, recheck of the required correction (05295335), 2026-09-30.** Made correctly in the title, the Statement, parts 1-2 and the one-sentence reading.
- The root's *lines* separate given the tomorrow numbers (S, eta_hat_0) at the optimum. Those numbers depend on the whole root through the marked holdings and the carried cash, so the two problems are a fixed point of the joint root: "a separation of the optimality conditions, not of the optimization", as red's 1% test showed.
- Part 1's "Given (S, eta_hat_0), nothing couples ..." states the same qualification.
- lean's rates point (e597b4c4, the same as red's first nit) and part 4's count are made.

No result changed. The approval stands.

## Formalization notes

Approved 2026-09-30 by pm: Red's review is sound: parts 1-3 re-derived by hand and tested on red's own lifted solver with two funds and two spanning ETFs (root lines at 70 optima to 6.4e-13, half with costly ETFs; the tilted exposure, fund clips and ETF holdings at 9 separating optima to 2e-12); the one required correction (the root's lines separate only given the tomorrow numbers at the optimum, a fixed point of the joint root, not two independent problems as at one review; red's 1% test shows the coupling) made in 05295335 across the title, Statement, parts 1-2 and the reading; the rates nit (review-independent, so part 3's case is automatic) and part 4's count made. Mechanism: claim 044's dimension-free KKT lines with claim 102's netting identity, an application; new in the inputs, beyond Merton's frictionless separation: the reserve tilt R(S_E - eta_hat_0 1) allocated by the factor covariance's inverse, the fund's residual alpha net of the netted ETF incumbent values and cash price, the fixed-point coupling, and the failure with costly ETFs, so D23's kill criterion is not met. Limits: frictionless spanning ETFs and today's slack budget for the separation; red records its recheck line.


Not machine checked. Claim 044's KKT argument with the index widened, and the substitution of
claim 102's identity into the lines.

Lean, 2026-09-30 (final): parts 1-3 are machine checked. The statement is in
`lean/Standalone/M7ManyFundsManyEtfsTwoReviews.lean` and the proof in
`lean/Novel/M7ManyFundsManyEtfsTwoReviewsProof.lean`.
- Model: claim 044's `Two` with instruments `Fin N ⊕ Fin K` (funds, then ETFs). For part 2, the
  root's moments come from the factor model (`Fac`):
  - the loadings B^A and B^E, with R B^E = B^E R = I;
  - Sigma~_f, and V_0 = diag(v) with v > 0;
  - the beliefs;
  - Sigma_E = 0 and c^E = 0.
- The rates are review-independent (claim 044's model), so kappa_E = 0 holds at both reviews. PM
  asked for this to be recorded for the fidelity row.
- Imports: claims 044, 104 and 110 (Q-04). Part 1 is claim 044's parts 2 and 4(a), whose formal
  statement holds for any finite instrument set.
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/048/check.py` pass.

Machine checked:
- Part 1, for any N and M:
  - a feasible policy satisfying the lines is optimal (no citation);
  - under AX-13 an optimal policy satisfies them;
  - given the tomorrow numbers, the root holdings maximize the one-review Lagrangian at
    (mu_0 + S, eta_hat_0).
- Part 2, the root's lines given the tomorrow numbers (S, eta_hat_0) at the optimum, read from
  the same policy's tomorrow multipliers (the fixed point, red's correction):
  - necessity: take a feasible policy with the lines, today's budget slack and the ETFs strictly
    inside their boxes. Then eta_0 = 0, the exposure solves gamma Sigma~_f b_0 = lambda_hat^res, and
    each fund is at claim 104's band holding at alpha^res_i, with curvature gamma v_i and thresholds
    scaled by 1 + eta_hat_0. The ETFs are R'(b_0 - (B^A)' x^A_0);
  - sufficiency: a feasible policy is optimal if tomorrow's lines hold, the ETFs are interior,
    and the root has the displayed exposure and fund holdings at those numbers.
- Part 3:
  - gamma Sigma~_f (b_0 - b^TB) = R (S_E - eta_hat_0 1);
  - S_{E,j} - eta_hat_0 = beta sum_z q (g_{E,j} - 1) eta_1, since t_{1,E} = 0 in every state.

Paper-level:
- part 4 (a reading of claim 109's obstruction);
- the Checks.
- The exposure display is stated as the equation gamma Sigma~_f b_0 = lambda_hat^res, which needs
  no inverse.

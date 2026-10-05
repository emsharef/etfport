---
id: 49
title: "A usable flexibility test for the full menu over two reviews: tomorrow's budget is slack in every state where the liquid reserve, today's cash plus the ETFs' sale proceeds down to their solo sale thresholds, covers the instruments' solo-target purchases; the test at level epsilon asks that the shortfall's (1 - epsilon)-quantile be zero, that is, that at most a fraction epsilon of the revision states be uncovered, the all-states case being claim 113's aggregate test; under it repeated one-review optimization with bands loses at most a band term, the incumbent values' quadratic form in the inverse curvature, at most the discounted marked rates squared over the curvature, plus a tail term, epsilon times the Rockafellar-Uryasev tail measure of the cash-price bound times the shortfall, both in the inputs; the tail term is the uncovered states' loss and vanishes at epsilon = 0"
status: formalized
model_version: M7
depends_on: [44, 46, 113]
axioms_used: [AX-13, AX-19]
formal: lean/Standalone/M7QuantileFlexibility.lean
direction: D25
---
## Statement

D25's claim (LAB_REQUEST_2 item 7). Claim 113's aggregate no-reserve test asks, in every
revision state, that today's cash plus the ETF's sale proceeds cover the instruments'
solo-target purchases. This claim states the test for the full menu (N funds, M ETFs; part 1),
relaxes it to a stated fraction of states through the shortfall's quantile (part 2), and gives
the loss of repeated one-review optimization with bands under it, in the inputs: a band term,
present with slack budgets, plus a tail term for the uncovered states, the expectation of the
cash-price bound times the shortfall, which under the test equals the uncovered fraction times
the Rockafellar-Uryasev tail measure (part 3). At level zero the test is claim 113's and only the band term remains.

**Setting.** M7's finite-law variant with N funds, M ETFs and K factors over two reviews with
the funded budget at both (claim 044's setting with the instrument index widened, as in claim
048): holdings x >= 0 with caps, directional rates kappa^+_i, kappa^-_i in [0, 1), marking by
gross returns g(z') > 0, beta in (0, 1], today's cash h^+_0, tomorrow's law q(z') on finitely
many states, predictive moments mu_1(z'), Sigma_1(z'), and Sigma_1(z') entrywise nonnegative
(nonnegative loadings, independent residuals, a zero prior cross-covariance, as in claim 113).
The *repeated one-review policy* (myopic): today's one-review optimum x^my_0 with cash h^my,
then in each state tomorrow's one-review optimum from the marked holdings, which is the last
review's dynamic optimum. V^dyn the dynamic optimum's value and J(x^my_0) the policy's value
(today's score net of costs plus beta times the expected value of tomorrow's budgeted problem).
Per state, at holdings x_0 and cash h (claim 113's objects over the full menu):

```
x_hat_i(z') = (mu_{1,i}(z') - kappa^+_i)^+/(gamma Sigma_{1,ii}(z')),   every instrument i          (solo targets),
need(z')    = sum_i (1 + kappa^+_i) ( x_hat_i(z') - g_i(z') x_{0,i} )^+                              (the solo-target purchases the revision calls for, with their rates),
x_check_E(z') = (mu_{1,E}(z') + kappa^-_E)/(gamma Sigma_{1,EE}(z')),    every ETF E                (solo sale thresholds),
liq(z')     = h + sum_E (1 - kappa^-_E) ( g_E(z') x_{0,E} - x_check_E(z')^+ )^+                     (the liquid reserve: cash plus the ETFs' sale proceeds down to their thresholds, net of the rates),
D(z')       = ( need(z') - liq(z') )^+                                                           (the shortfall),
eta_bar(z') = max_i (mu_{1,i}(z') - kappa^+_i)^+/(1 + kappa^+_i)                                 (claim 046's cash-price bound, over the menu),
eps(x_0, h) = P( D(z') > 0 )                                                                     (the uncovered fraction),
T_eps(Y)    = min_c [ c + E (Y - c)^+ / eps ],   eps in (0, 1]                                    (the Rockafellar-Uryasev tail measure at level 1 - eps, AX-19, on the finite law).
```

1. **Coverage, one inequality per state, full menu.** If liq(z') >= need(z') at (x_0, h), then
   tomorrow's budget is slack at z': the optimum without the budget buys at most the solo-target
   purchases and sells every ETF whose marked holding exceeds its clipped threshold down to at
   most the threshold, so it is fundable, and eta_1(z') = 0 is admissible. This is claim 113's
   2a with the ETFs' proceeds summed over M ETFs.

2. **The quantile test.** For eps in [0, 1), the test *passes at level eps* at (x_0, h) iff

   ```
   VaR_{1 - eps}( D )  =  0,      equivalently      P( D(z') > 0 )  <=  eps,
   ```

   the shortfall's (1 - eps)-quantile is zero: at most a fraction eps of the revision states
   are uncovered. When the reserve does not vary with the state (the ETFs unmarked and their
   thresholds state-free) this reads liq >= VaR_{1 - eps}(need): the liquid reserve covers the
   (1 - eps)-quantile of the purchases the target move calls for. At eps = 0 it is claim 113's
   all-states test (part 1 in every state). Whenever the test passes at a level eps > 0,

   ```
   E[ eta_bar(z') D(z') ]  =  eps T_eps( eta_bar D )  <=  eps max_z' eta_bar(z') D(z'),
   ```

   so under the test the tail term is the plain expectation E[eta_bar D] over the uncovered
   states (red's nit: the Rockafellar-Uryasev form adds content only where the test fails,
   P(D > 0) > eps, which this claim does not use; it is kept for the pairing of the quantile
   with the tail expectation).

3. **The loss bound.** With S = beta E[g_i t_{1,i}] the incumbent values at the myopic root's
   *relaxed* tomorrow (tomorrow's budget dropped; t_{1,i} in [-kappa^-_i, kappa^+_i] any
   admissible slope of that tomorrow's lines: the rate if traded, the held marginal if held
   inside, an interval at tomorrow's bound states, the bound holding for any admissible choice),

   ```
   V^dyn - J(x^my_0)  <=  (1/2) S' (gamma Sigma_0)^{-1} S  +  beta E[ eta_bar(z') D(z') ]                       (band term plus tail term)
                      <=  (beta^2/2) sum_i ( E[g_i] max(kappa^+_i, kappa^-_i) )^2  norm((gamma Sigma_0)^{-1})  +  beta eps T_eps( eta_bar D ),
   ```

   with D and eps at (x^my_0, h^my) and the operator norm; the second line is in the inputs.
   Under the test at level eps the tail term is the uncovered states' loss, the plain
   expectation beta E[eta_bar D] (part 2), at most beta eps max_z' eta_bar D; at eps = 0 only the band term remains, second order in the rates, which is
   what makes repeated one-review optimization with bands adequate under the test. With one
   ETF and the funds' incumbent values zero, the band term is S_E^2/(2 gamma Sigma_{EE.F}) with
   Sigma_{EE.F} = Sigma_{0,EE} - Sigma_{0,EF} Sigma_{0,FF}^{-1} Sigma_{0,FE} the ETF's residual
   variance given the funds (the Schur complement, at most Sigma_{0,EE}, since the band term's
   move is free in every coordinate); it equals claim 047's cost-channel shift times S_E/2 only
   with the funds fixed or uncorrelated with the ETF (leanb's check). No solution of tomorrow's
   problems is needed for the second line; the first needs the relaxed tomorrow at the myopic
   root only.

**One sentence without model nouns.** Sort the revision states by how far the purchases they
call for exceed the cash plus what the cheap instruments would fetch when sold down to their
own sale points; if at most a stated fraction of states are short, then optimizing one period
at a time with bands loses at most a fixed term set by the trading rates squared over the
risk curvature, plus that fraction times the average, over the short states, of the cash
price bound times the shortfall.

## Proof

### 1. Coverage

Tomorrow's problem at z' is the one-review problem from (g o x_0, h); the *relaxed* problem drops
the budget. Its optimum x^u exists (concave over a box) and satisfies claim 044 part 2's lines
with eta = 0 (AX-13): a bought instrument has g_{1,i}(x^u) >= kappa^+_i (equality strictly inside
the box, >= at its cap). Since Sigma_1(z') is entrywise nonnegative and x^u >= 0,
(Sigma_1 x^u)_i >= Sigma_{1,ii} x^u_i, so kappa^+_i <= g_{1,i}(x^u) <= mu_{1,i} - gamma Sigma_{1,ii} x^u_i and
x^u_i <= x_hat_i: the purchase is at most (x_hat_i - g_i x_{0,i})^+ and costs at most (1 +
kappa^+_i) times it. For an ETF with g_E x_{0,E} > x_check_E^+: if it were held or bought, its line
would need g_{1,E}(x^u) >= -kappa^-_E at x^u_E >= g_E x_{0,E}, but g_{1,E}(x^u) <= mu_{1,E} - gamma
Sigma_{1,EE} x^u_E < mu_{1,E} - gamma Sigma_{1,EE} x_check_E^+ <= -kappa^-_E (the last step: equality when
x_check_E >= 0, and mu_{1,E} < -kappa^-_E when x_check_E < 0); so it is sold, and after the sale
x^u_E <= x_check_E^+ (the sale line g_{1,E} = -kappa^-_E with (Sigma_1 x^u)_E >= Sigma_{1,EE} x^u_E if
x^u_E > 0; trivially if x^u_E = 0), yielding at least (1 - kappa^-_E)(g_E x_{0,E} - x_check_E^+). Other
sales only add cash. So the relaxed optimum's net cash use is at most need(z') - (liq(z') - h)
<= h: it is feasible for the budgeted problem, hence optimal there (the maximizer over the
larger set), and its lines hold with eta_1 = 0, which is therefore admissible.

### 2. The quantile test

D >= 0, so VaR_{1 - eps}(D) = min{c : P(D <= c) >= 1 - eps} is zero iff P(D <= 0) >= 1 - eps iff
P(D > 0) <= eps. With a state-free reserve, D > 0 iff need > liq, and P(need > liq) <= eps iff
P(need <= liq) >= 1 - eps iff liq >= VaR_{1 - eps}(need). The tail identity: let Y = eta_bar D >= 0
with P(Y > 0) <= eps, eps > 0. For c >= 0, (Y - c)^+ >= Y - c on {Y > 0} and >= 0 elsewhere, so
E(Y - c)^+ >= E[Y] - c P(Y > 0) >= E[Y] - c eps and c + E(Y - c)^+/eps >= E[Y]/eps; for c < 0,
c + E(Y - c)^+/eps = c + (E[Y] - c)/eps = E[Y]/eps + c (1 - 1/eps) >= E[Y]/eps. At c = 0 the value is
E[Y]/eps. So T_eps(Y) = E[Y]/eps, and T_eps(Y) <= max Y since c = max Y gives that value.

### 3. The loss bound

Write f_0(x_0) = score_0(x_0) - cost_0(x_0 - x^-_0) for today's one-review objective, C for today's
feasible set (the box and today's budget, convex), W(x_0, z') for tomorrow's budgeted value at
state z' from (g o x_0, h^+_0(x_0)) and W^s(x_0, z') for the relaxed value, and J(x_0) = f_0 + beta
E[W], J^s(x_0) = f_0 + beta E[W^s]. Three steps.

(a) W <= W^s pointwise (the budget dropped), so V^dyn = J(x^dyn_0) <= J^s(x^dyn_0) <= sup_C J^s.

(b) *The band term.* W^s(., z') is concave in x_0: it is the partial maximum over the box of
phi(x_0, x_1) = score_1(x_1) - cost_1(x_1 - g o x_0), jointly concave. At the relaxed optimum x^u
for x_0, let t be the cost's subgradient at the trade u^u = x^u - g o x_0 with which x^u's lines
hold (t_i in [-kappa^-_i, kappa^+_i], any admissible choice: kappa^+_i if bought, -kappa^-_i if
sold, the held marginal g_{1,i}(x^u) inside, an interval at a bound state; AX-13; the argument
below holds for every such t). By the convex chain rule for the linear
map (x_0, x_1) -> x_1 - g o x_0, (g o t, -t) is a supergradient of -cost_1(x_1 - g o x_0) at (x_0,
x^u), so (g o t, g_1(x^u) - t) is a supergradient of phi there, and g_1(x^u) - t lies in the box's
normal cone at x^u (the lines). Hence for every y, W^s(y) = phi(y, x^u(y)) <= phi(x_0, x^u) + (g o
t)'(y - x_0) + (g_1(x^u) - t)'(x^u(y) - x^u) <= W^s(x_0) + (g o t)'(y - x_0): g o t is a supergradient
of W^s(., z') at x_0, and S = beta E[g o t] one of beta E[W^s] at x^my_0. Next, x^my_0 maximizes
the concave f_0 over C, so there is a supergradient s_f of f_0 at x^my_0 with s_f'(y - x^my_0) <= 0
for all y in C (AX-13). score_0 is strongly concave with modulus gamma Sigma_0 and the rest of
J^s is concave, so for y in C, with d = y - x^my_0,

```
J^s(y) <= J^s(x^my_0) + (s_f + S)' d - (1/2) d' gamma Sigma_0 d <= J^s(x^my_0) + S' d - (1/2) d' gamma Sigma_0 d <= J^s(x^my_0) + (1/2) S' (gamma Sigma_0)^{-1} S,
```

the last by maximizing the quadratic in d. With (a), V^dyn <= J^s(x^my_0) + (1/2) S'(gamma
Sigma_0)^{-1} S.

(c) *The tail term.* J^s(x^my_0) - J(x^my_0) = beta E[W^s - W] at x^my_0. Fix z', write h = h^my and
let eta be the smallest admissible cash price of the budgeted problem at its optimum x^b (a KKT
multiplier, AX-13): x^b maximizes score_1(x_1) - cost_1(x_1 - g o x_0) - eta (cash used by x_1) over
the box (its lines are that problem's optimality conditions), and eta (cash used by x^b - h) = 0.
Applying this to the relaxed optimum x^u with cash use C^u: W^s - eta C^u <= W - eta h, so W^s - W
<= eta (C^u - h) <= eta (C^u - h)^+ <= eta D(z'), by part 1's accounting C^u - h <= need - liq. By
claim 046 part 1(a), whose proof uses only Sigma_1 >= 0 entrywise and x_1 >= 0 and applies with
the index widened, eta <= eta_bar(z'). Summing with beta q(z') gives the tail term; the identity
and the maximum bound are part 2's. The inputs line: |S_i| <= beta E[g_i] max(kappa^+_i, kappa^-_i)
coordinatewise, so (1/2) S'(gamma Sigma_0)^{-1} S <= (1/2) norm(S)^2 norm((gamma Sigma_0)^{-1}).
With eps = 0 the tail term is zero. With one ETF and S = (0, ..., 0, S_E), S'(gamma Sigma_0)^{-1} S =
S_E^2 [(gamma Sigma_0)^{-1}]_EE = S_E^2/(gamma Sigma_{EE.F}) by the block inverse (Schur
complement), which reduces to S_E^2/(gamma Sigma_{0,EE}) iff Sigma_{0,EF} = 0.

## Checks

`checks/049/check.py` (claim 048's joint solver, N = 2 funds and M = 2 ETFs; rule 22, floating
point). (i) Part 1: in 169 covered states of 360 (at myopic and dynamic roots, today's cash
swept), the relaxed optimum is fundable and the budgeted solve's multiplier is zero. (ii) Part 3:
at 80 instances (52 with an uncovered state) the myopic policy's loss is within the band-plus-tail
bound, the loss over the bound having median 0.013 and maximum 0.276, and each state's
relaxation gap is within eta_bar D. (iii) Part 2: E[eta_bar D] equals eps times the tail measure at
level 1 - eps in the 18 instances with 0 < eps < 1. A cash sweep on one instance (six states):
cash 0.05 to 4.0 takes the uncovered fraction from 0.67 to 0 while the loss stays at 10.9 bp,
the band term at 114 bp and the tail term falls from 180 bp to 0, illustrating the test's
conservatism (the solo-target need counts each ETF's solo target, which correlated ETFs do not
jointly reach).

## Not shown

- Fund sale proceeds are not counted in liq (they only add cash; counting them needs a lower
  bound on fund sales, which the solo sale threshold gives instrument by instrument, omitted).
- The need is conservative: it sums solo targets, which correlated instruments do not jointly
  reach; a tighter need requires solving tomorrow's relaxed problem, which the second line of
  part 3 avoids and the first uses.
- Tightness of the band term (the check's ratios are far below one); the Gaussian law (a
  quantile of D under it needs the tail moments of claim 047 part 2).
- Several reviews; a budget that binds today at the myopic root is allowed (the argument runs
  over today's feasible set), but the test itself is about tomorrow.

## Prior art

Mechanism: claim 113's aggregate no-reserve test extended to the full menu and relaxed to a
quantile, with the loss bound from strong concavity of today's score at the myopic root
(the band term, claim 044's incumbent values at the relaxed tomorrow) and the budgeted
problem's Lagrangian against its relaxed optimum (the tail term, claim 046's cash-price
bound), the tail expectation evaluated by Rockafellar-Uryasev's formula (AX-19).

General results checked: claims 044 (the lines, the incumbent values), 046 (parts 1(a)-(b): the
cash-price bound, the covered-state condition), 113 (2a-2b: the aggregate test with the ETF's
proceeds), 047 (the one-ETF shift), 029 (the bands); AX-13 (KKT for the concave programs);
AX-19 (`rockafellar2000optimization`: the tail measure's minimization formula (4)-(5), used as
the definition on the finite law, its Theorem 1's identification with the conditional tail
expectation not used since it assumes a continuous law). Named: `rockafellar2000optimization`
(the quantile and tail-expectation pairing).

Searched: claims 044, 046, 047, 113, 029, 110; the D25 entry. This is a claim because the
request asks for a sufficient condition in the inputs with a stated fraction of states and a
loss bound; the kill benchmark ("claim 046's covered-state condition restated with no quantile
or loss bound") is escaped by parts 2 and 3.

## Open objections

None raised yet. Red should test: the strong-concavity step with the cost's non-smoothness and
today's budget in C; the supergradient of the relaxed value in x_0 through the marking; the
Lagrangian step in (c) when the budgeted optimum is not unique; and the sale-threshold case
x_check_E < 0.

## Review

**Red, 2026-09-30** (on 940bb23c; rebased onto c86e8ac0, which changes only AX-19's ledger entry). Red-passed, with one required correction: the one-ETF form of the band term. Red rederived every step by hand and tested part 3's bound with its own solver, written without reading checks/049: experiment 047's design (one fund, one ETF, 16 states), the lifted joint program for V^dyn, the one-review program for the myopic policy, and the relaxed tomorrow for S.

**Part 1** is claim 113's 2a over M ETFs, and it is right: the solo-target bound with Sigma_1 entrywise nonnegative, and the ETFs above their clipped thresholds sold down to them.

**Part 2** is right. VaR_{1-eps}(D) = 0 iff P(D > 0) <= eps. On that event, T_eps(Y) = E[Y]/eps for Y = eta_bar D, with c = 0 optimal, as the proof shows.

**Part 3's bound** is right by hand.
- *(a)* Dropping tomorrow's budget can only raise the value.
- *(b)* g o t at the relaxed tomorrow is a supergradient of W^s (the chain rule through the marking). f_0 = score - cost is strongly concave with modulus gamma Sigma_0, and any supergradient of f_0 has the form grad(score) - dcost. So J^s(y) <= J^s(x^my_0) + S'd - d' gamma Sigma_0 d/2 on C, which gives the band term.
- *(c)* By Lagrangian duality at any KKT multiplier, W >= L(x^u) = W^s - eta (C^u - h). With part 1's accounting and claim 046 1(a) (the smallest admissible eta <= eta_bar), W^s - W <= eta_bar D.
- *Numerically*, V^dyn - J(x^my_0) <= band + tail at 300 of 300 random instances, 164 of them with a positive tail term. The largest ratio of loss to bound is 0.61.

**Required correction (part 3 and its proof: "With one ETF the band term is S_E^2/(2 gamma Sigma_EE), claim 047's cost-channel shift times S_E/2").**
- *The error.* With the funds' incumbent values zero, S = (0, ..., 0, S_E) and the band term is (1/2) S_E^2 [(gamma Sigma_0)^{-1}]_EE = S_E^2 / (2 gamma (Sigma_EE - Sigma_EA Sigma_AA^{-1} Sigma_AE)): the ETF's Schur complement, not Sigma_EE. The two agree only if the funds are held fixed (claim 047's shift is the fixed-fund one); the bound's d moves the funds too.
- *Numerically.* With a costless fund (so S_A = 0 exactly) and slack budgets, the loss exceeds S_E^2/(2 gamma Sigma_EE) at 30 of 300 instances, by up to 5.9 times (for example 1.24e-4 against 2.34e-5), while staying within the correct term (2.29e-4).
- *Please* write the Schur complement, or state the one-ETF form for the funds held fixed, and correct "claim 047's cost-channel shift times S_E/2" accordingly.

**Nit.** Under the test (P(D > 0) <= eps), T_eps(eta_bar D) = E[eta_bar D]/eps exactly, so "eps times the Rockafellar-Uryasev tail measure" is E[eta_bar D] written another way. "Computed from the inputs by sorting the states" is not needed: it is the plain expectation. The RU form only adds content where the test fails (P(D > 0) > eps), which the claim does not use. Please say so, so that a reader does not look for more.

**Mechanism.** Claim 113's coverage over M ETFs; a strong-concavity bound at a supergradient of the relaxed continuation (the band term); Lagrangian duality with claim 046's cash-price bound (the tail term): an application. New in the inputs: the myopic loss bound under a quantile coverage test.

Verdict: red-passed

**Red, recheck of the correction and the nit (daadc383, 66887346), 2026-09-30.** Both are made correctly.
- The one-ETF band term is S_E^2/(2 gamma Sigma_{EE.F}) with the ETF's Schur complement, which leanb's prose check made independently. Equality with claim 047's shift times S_E/2 is limited to funds fixed or uncorrelated with the ETF.
- Under the test, the tail term is stated as the plain expectation beta E[eta_bar D].

No result changed. The verdict stands.

## Formalization notes

Approved 2026-09-30 by pm: Red's review is sound: every step re-derived by hand (part 1 as claim 113's 2a over M ETFs; part 2's quantile and tail identity; part 3's band term from strong concavity at a supergradient of the relaxed continuation and the tail term from Lagrangian duality with claim 046's cash-price bound) and part 3's bound tested on red's own solver at 300 of 300 instances (164 with a positive tail term, largest loss-to-bound ratio 0.61); the required correction (the one-ETF band term uses the ETF's Schur complement, not Sigma_EE; 30 of 300 instances exceeded the old form, up to 5.9x) made in daadc383 from leanb's matching point, and red's nit (the tail term is the plain expectation E[eta_bar D] under the test) made in 66887346. Mechanism: claim 113's coverage with a strong-concavity and a duality bound, an application; new in the inputs: the myopic loss bound under a quantile coverage test, so D25's kill criterion is not met. Limits: fixed means (D25b extends it to M9); red records its recheck line.


Not machine checked. Part 2's tail identity is elementary; part 3 is a supergradient
inequality for a strongly concave function over a convex set plus one Lagrangian inequality.

Leanb, 2026-09-30: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M7QuantileFlexibility.lean` and the proof
  `lean/Novel/M7QuantileFlexibilityProof.lean`. The model is claim 044's with a set of ETFs among
  the instruments (the full menu). Claims 046's and 113's objects are reused, and claim 111's
  completed square (Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/049/check.py` pass.

Machine checked:
1. Part 1: need <= liq at a state makes eta_1 = 0 admissible there, from any admissible multiplier,
   with the proceeds summed over the ETFs.
2. Part 2: VaR_{1-eps}(D) = 0 iff P(D > 0) <= eps; the state-free form P(D > 0) <= eps iff
   VaR_{1-eps}(need) <= L; and, when P(Y > 0) <= eps, the Rockafellar-Uryasev objective's least
   value E[Y]/eps (so E[Y] = eps T_eps(Y)), at most max Y. These are proved directly on the finite
   law; AX-19 carries only the Gaussian reading.
3. Part 3.
   - The loss bound: every feasible policy, the dynamic optimum in particular, has claim 044's J
     at most J(myopic) + S'Sigma_0^{-1}S/(2 gamma) + beta E[eta_bar D].
   - The band term comes from today's strong concavity at the myopic root and the relaxed
     tomorrow's supergradient, with claim 111's completed square. The tail term comes from the
     budgeted tomorrow's Lagrangian bound (claim 044's lag_max) at an admissible
     min(eta, eta_bar) and part 1's accounting.
   - The assembly bounds J directly, so it needs no V_1 lemma.
   - The band term in the inputs, for any L bounding Sigma_0^{-1}'s form.

Paper-level:
- the existence of the multipliers (AX-13), taken as hypotheses;
- the one-ETF remark (Sigma_{EE.F});
- the Gaussian reading;
- the Checks.

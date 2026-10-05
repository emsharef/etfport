---
id: 115
title: "The quantile flexibility test with time-varying premia (M9): claim 049's test and loss bound transfer verbatim to M9's tree; tomorrow's need splits into the planned purchase, set by the predictable move at zero innovation with the worst marking, and an innovation-driven part, so the test at level epsilon reads: the liquid reserve covers the planned purchase plus the (1 - epsilon)-quantile of the innovation-driven part; the loss bound holds at any today's holding with the band term the root residual's quadratic form, which vanishes at the front-loaded point (the relaxed two-review optimum), so under the test at small epsilon front-loading the planned purchase loses at most the tail term, while at the one-review root the band term is the price of the planned purchase's timing, pinned at the discounted marked rate squared over the residual curvature when the predictable move exceeds the innovation's support"
status: formalized
model_version: M9
depends_on: [044, 046, 047, 049, 113, 114]
axioms_used: [AX-13, AX-19]
formal: lean/Standalone/M9QuantileTimeVarying.lean
direction: D25b
---
## Statement

D25b's claim (LAB_REQUEST_2 item 7 with the widening's state model). Claim 049 (math's D25,
red-passed; this claim states its dependence and is filed on it) gives, on M7's finite tree, the
quantile flexibility test and the loss of repeated one-review optimization with bands: a band
term plus a tail term. Claim 114 splits tomorrow's need in M9 into a planned purchase, set by
the predictable move, and an innovation-driven part. This claim puts the two together: the
test in split form, with the planned purchase covered in full and a quantile of the
innovation-driven part (part 1); the loss bound at any today's holding, whose band term is the
root residual's quadratic form and vanishes where the planned purchase is front-loaded, so the
timing of the planned purchase is exactly what the band term prices (part 2); and the pinned
form of that price when the predictable move exceeds the innovation's support (part 3). The
kill benchmark (claim 049 with the need's distribution replaced and nothing from the planned
purchase's timing) fails on parts 2-3.

**Setting.** M9 (model/SPEC.md) with one fund and one ETF over two reviews in the finite-law
variant (claim 114's setting; N funds and M ETFs by claims 113 and 049's widening, with the
planned purchase summed over instruments), claim 049's objects at today's holdings x_0 and cash
h: the solo targets x_hat_i(z'), the need, the ETF's clipped solo sale threshold, the liquid
reserve liq(z'), the shortfall D(z') = (need - liq)^+, the cash-price bound eta_bar(z'), the
uncovered fraction eps(x_0, h) = P(D > 0) and the tail measure T_eps (AX-19, as a definition on
the finite law); the repeated one-review policy (myopic) with root x^my_0 and cash h^my, its
value J(x^my_0), and the dynamic value V^dyn. From claim 114: tomorrow's predictable mean
mu^p_1 = G(Phi m_0 + (I - Phi) theta_bar) - (0, c^E), so that mu_1(z') = mu^p_1 + G Phi K_0 nu_1(z'),
and g^min the coordinatewise minimum gross return on the support. Define

```
x_hat^p_i = ( mu^p_{1,i} - kappa^+_i )^+/(gamma Sigma_{1,ii}),      PP(x_0) = sum_i (1 + kappa^+_i) ( x_hat^p_i - g^min_i x_{0,i} )^+          (the planned purchase: the need at zero innovation with the worst marking),
Delta(z') = need(z') - PP(x_0)                                                                                              (the innovation-driven part, of either sign),
```

and, for any today's holding x_0 in today's feasible set C (the box and today's budget) with
cash h(x_0), the *root residual* rho(x_0): the shortest vector, in the norm of
(gamma Sigma_0)^{-1}, of the form g_0(x_0) + S - l, where g_0 is today's smooth marginal, S
ranges over the *admissible incumbent values* at the relaxed tomorrow from x_0 (claim 049's
part 3: tomorrow's budgets dropped; S_i = beta E[g_i t_{1,i}] with t_{1,i}(z') the slope pinned by
that tomorrow's regime where the instrument trades or is held strictly inside its box, and,
where it is held at a bound, any slope in the interval its one-sided line cuts from
[-kappa^-_i, kappa^+_i], claim 044's part 2 reading; S is then a box), and l ranges over the set
of today's line values
{ eta 1 + (1 + eta) t + n : eta >= 0 (eta = 0 if h(x_0) > 0), t_i in the trade-sign slope set at x_0, n in the box's normal cone at x_0 }.
The minimum over S matters: with one fixed slope at a bound state the residual can be nonzero
where the free choice makes it zero (red's instances: 8 of 120 front-loaded points, band terms
up to 2.3e-4). rho(x_0) = 0 iff x_0 satisfies claim 044's root lines with the relaxed tomorrow
for some admissible choice; in particular at the *front-loaded point* x^s_0, the relaxed
two-review optimum (tomorrow's budgets dropped; claim 047's part 2(b) certificate point),
whose KKT conditions select such a choice, rho(x^s_0) = 0.

### Part 1. The test in split form, on M9's tree

1a. *Transfer.* Claim 049's parts 1-3 hold on M9's tree verbatim: its hypotheses are on the
    tree's law of (mu_1(z'), Sigma_1) and the marking, which M9 supplies (claim 114's part 4),
    with Sigma_1 entrywise nonnegative as there. In particular coverage at a state (liq >= need)
    makes a zero cash price admissible, and the test at level eps passes iff P(D > 0) <= eps.
1b. *The split.* need(z') = PP(x_0) + Delta(z'), with PP known at review 0 from Phi, theta_bar,
    the beliefs, the rates, the loadings and g^min, and Delta(z') carrying the innovation
    nu_1(z') and the marking (the positive parts do not split: Delta can be negative, and PP is
    the need's value at nu_1 = 0 with the worst marking, not a summand of solo targets). The
    test at level eps therefore reads

    ```
    P( Delta(z') > liq(z') - PP(x_0) )  <=  eps,        and with a state-free reserve        liq - PP(x_0)  >=  VaR_{1 - eps}( Delta ):
    ```

    the liquid reserve covers the planned purchase in full plus the (1 - eps)-quantile of the
    innovation-driven part. At eps = 0 it is claim 113's aggregate test with the need so split.
    Under M9's finite law Delta is a finite computation; under the Gaussian law its quantile
    needs claim 047's part 2 tail moments (Not shown).

### Part 2. The loss bound at any today's holding, and the timing of the planned purchase

2a. *The general bound.* For every x_0 in C, with D, eta_bar and eps evaluated at (x_0, h(x_0)),

    ```
    V^dyn - J(x_0)  <=  (1/2) rho(x_0)' (gamma Sigma_0)^{-1} rho(x_0)  +  beta E[ eta_bar(z') D(z') ],
    ```

    J(x_0) the value of holding x_0 today and tomorrow's budgeted optimum in every state. At
    the myopic root the residual's form is at most S'(gamma Sigma_0)^{-1} S (taking l at the
    myopic line's own cash price, slopes and cone element leaves rho = S; the nearest point can
    be closer), so this contains claim 049's part 3; at the front-loaded point x^s_0 the band
    term is zero and

    ```
    V^dyn - J(x^s_0)  <=  beta E[ eta_bar(z') D(z') ]  =  beta eps T_eps( eta_bar D )   under the test at level eps > 0 at (x^s_0, h(x^s_0)),
    ```

    the tail identity at the test's level (claim 049's part 2: E[Y] = eps T_eps(Y) whenever
    P(Y > 0) <= eps, the same eps on both sides; at the uncovered fraction itself it reads
    eps(x^s_0) T_{eps(x^s_0)}(eta_bar D)), so it is

    the tail term alone: front-loading the planned purchase (trading today to the root lines
    with the relaxed tomorrow) removes the band term, and under the test at a small level its
    loss is the uncovered states' loss only. The bound holds for every admissible choice of
    S and l, so it holds at the minimum; the vanishing at x^s_0 needs the minimum over the
    bound states' slopes (red's correction).
2b. *The timing, read.* The band term at the myopic root is the price of not acting today on
    what the relaxed tomorrow would trade; with a predictable move it is the price of the
    planned purchase's timing (part 3 gives its pinned value). Which point to hold is decided by
    the two bounds at the two points, both in the inputs once the relaxed tomorrow is solved:
    when the test passes at a small eps at the front-loaded point, front-loading is adequate
    (its bound is the small tail term); when today's cash is short, the front-loaded point spends
    cash the uncovered states would want, its tail term can exceed the myopic root's band plus
    tail, and the myopic root (or a partial front-loading) is the better of the two (the check's
    tight instances: the front-loaded point's realized loss exceeds the myopic policy's in all
    four, while both bounds hold). A rule: front-load the planned purchase to the extent the
    test still passes at the chosen level at the front-loaded holdings (a reading, rule 22;
    the check's tight instances illustrate it).

### Part 3. The pinned band term under a large predictable move

If today's budget is slack at the myopic root, tomorrow's budget is slack in every state, and
the fund is bought in every state tomorrow from the myopic root's marked holding (claim 114's
3a hypothesis: the predictable rise exceeds the innovation's support there) with kappa^+_A > 0,
then S_A(x^my_0) = beta E[g_A] kappa^+_A exactly, and with the ETF's incumbent value S_E the
band term at the myopic root is

```
(1/2) S' (gamma Sigma_0)^{-1} S  =  (beta E[g_A] kappa^+_A)^2/(2 gamma Sigma_{0,AA.E}) + (cross and ETF terms),      Sigma_{0,AA.E} = Sigma_{0,AA} - Sigma_{0,AE}^2/Sigma_{0,EE},
```

the fund's part being the discounted marked purchase rate squared over twice its residual
curvature given the ETF (the block inverse), the price of not front-loading a rise that
tomorrow buys anyway; the mirror holds for a fall sold in every state with kappa^-_A. This is
the sharpened first line of claim 049's part 3 under claim 114's hypothesis: an equality for
S_A rather than the bracket |S_A| <= beta E[g_A] max(kappa^+_A, kappa^-_A).

**One sentence without model nouns.** When the target's next move has a part known today,
tomorrow's cash need is a planned purchase plus a surprise; the flexibility test asks that
today's cash plus what the cheap instrument fetches cover the planned purchase in full and a
chosen quantile of the surprise; trading the planned purchase today removes the bound's
standing term and leaves only the uncovered states' loss, so under the test at a small level
front-loading is adequate, while with cash short today the one-period rule can be the better
of the two; and when the known move is large the standing term is exactly the discounted
purchase rate squared over the residual curvature.

## Proof

### 1. Transfer and the split

1a: claim 049's proofs use the tree's law of (mu_1(z'), Sigma_1(z')), the marking g(z') and the
entrywise nonnegativity of Sigma_1, and never the fixed-means structure; M9's tree supplies
these (claim 114's proof of part 4). 1b: need(z') as defined in claim 049 with mu_1(z') = mu^p_1 + G Phi K_0 nu_1(z')
(claim 114's 1a); PP is need at nu_1 = 0 with g replaced by g^min (a deterministic quantity;
since need is nonincreasing in the marking and the solo target is monotone in mu_1, PP is the
need's value at that point, not a bound); Delta = need - PP by definition, so
{need > liq} = {Delta > liq - PP} and part 2 of claim 049 gives the test; with liq state-free,
P(Delta > liq - PP) <= eps iff liq - PP >= VaR_{1 - eps}(Delta) (claim 049's proof of part 2 with
Delta for need and liq - PP for liq, Delta being real-valued rather than nonnegative, which
that argument does not use).

### 2. The general bound

Claim 049's proof of part 3, steps (a)-(c), with x_0 in place of x^my_0 in (b): V^dyn <= sup_C J^s
(step (a)); W^s(., z') is concave in x_0 with g o t a supergradient at x_0 for the relaxed
optimum's slopes t (step (b), unchanged), so S(x_0) is a supergradient of beta E[W^s] at x_0;
today's one-review objective f_0 is strongly concave with modulus gamma Sigma_0, and for any
supergradient s_f of f_0 at x_0 and any n in the normal cone N_C(x_0) of today's feasible set
(the box's cone plus, when the budget binds at x_0, the cash constraint's, eta (1 + t) with
eta >= 0 and t the cost's subgradient at today's trade, by AX-13's description of the
polyhedral normal cone of the lifted budget), n'(y - x_0) <= 0 for y in C, so for y in C with
d = y - x_0,

```
J^s(y) <= J^s(x_0) + (s_f + S)' d - (1/2) d' gamma Sigma_0 d <= J^s(x_0) + (s_f + S - n)' d - (1/2) d' gamma Sigma_0 d <= J^s(x_0) + (1/2) (s_f + S - n)' (gamma Sigma_0)^{-1} (s_f + S - n);
```

s_f ranges over g_0(x_0) - t with t in the trade-sign slope set at x_0 (the cost's
subdifferential); and S ranges over the admissible incumbent values, because claim 049's step
(b) uses only that x^u's lines hold with the chosen slopes t_1, which at a state holding an
instrument at a bound is true for every slope in the interval its one-sided line cuts (each
gives a supergradient g o t_1 of W^s there). So minimizing over (S, t, eta, n) gives the
residual rho(x_0) as defined, and V^dyn <= J^s(x_0) + (1/2) rho'(gamma Sigma_0)^{-1} rho, the
bound holding for every admissible (S, t, eta, n) and hence at the nearest point, which exists
(S ranges over a box and the set of line values is a polyhedral projection plus a convex cone,
closed and convex). Step (c) is unchanged:
J^s(x_0) - J(x_0) = beta E[W^s - W] <= beta E[eta_bar D] at (x_0, h(x_0)). At x^my_0, taking
(t, eta, n) as the myopic line's own (AX-13 at the one-review optimum gives g_0 - t_0 = eta_0 (1 + t_0) + n_0)
leaves g_0 + S - l = S, so the form is at most S'(gamma Sigma_0)^{-1} S, claim 049's, and the
nearest point can only lower it. At x^s_0, the relaxed two-review
program's optimality (AX-13: it is a concave program over C with the relaxed tomorrow) gives
g_0 + S in eta 1 + (1 + eta) t + N_box for the admissible S its KKT multipliers select (the
slopes at tomorrow's bound states being those multipliers' choice), so rho(x^s_0) = 0 at the
minimum over S, not necessarily at a fixed choice. 2b is a reading of 2a's two
bounds (the check's instances are an illustration, rule 22).

### 3. The pinned term

Claim 114's proof of 3a: the fund bought in every state from the myopic root's marked holding
pins s_A(z') = kappa^+_A with eta_1 = 0, so S_A = beta E[g_A] kappa^+_A; the band term's fund
part is the (A, A) entry of (gamma Sigma_0)^{-1} times S_A^2/2, and [(gamma Sigma_0)^{-1}]_{AA} = 1/(gamma Sigma_{0,AA.E})
by the block inverse (claim 049's part 3 remark with the roles of the fund and the ETF
exchanged); the cross term is S_A S_E [(gamma Sigma_0)^{-1}]_{AE} and the ETF's term S_E^2 [(gamma Sigma_0)^{-1}]_{EE}/2.

## Checks

`uv run python checks/115/check.py` (exits non-zero on failure; a check, not a proof). Eight
random M9 instances on the 72-node tree of claim 112's inputs (persistence 0.5-0.95, state
noise, a long-run alpha drift, random incumbents; today's cash tight on four), each solved
exactly as a two-review program (cvxpy/CLARABEL), with the relaxed two-review optimum as the
front-loaded point and the myopic policy's value from its root: (i) need = PP + Delta and the
split test agrees with claim 049's quantile test at 24 (instance, level) pairs, and the relaxed
optimum is fundable at all 96 covered states; (ii) claim 049's bound (both lines) holds for
the myopic policy on all eight, and the general bound holds at 21 today's holdings (the eight
front-loaded points and thirteen random feasible ones), the band term vanishing at every
front-loaded point (the residual minimised over held slopes, today's cash price and the box's
cone); in the four tight instances the front-loaded point's realized loss exceeds the myopic
policy's (for example 1.4e-3 against 1.7e-4 of wealth) while its bound, the tail term alone,
holds; (iii) at a long-run alpha of 4% the fund is bought in every state from the myopic
root and S_A = beta E[g_A] kappa^+_A = 0.00507, the fund's band term 1.2e-3.

## Not shown

- The Gaussian law's quantile of Delta (claim 047's tail moments); several reviews.
- The front-loaded point x^s_0 needs the relaxed two-review program (tomorrow's problems without
  budgets); a one-review approximation of it (claim 114's 3a threshold cut when the fund is
  bought in every state) is not given a bound here.
- Which of the myopic root and the front-loaded point loses less is decided by the two bounds
  (2b), not by a closed rule; partial front-loading (a point between them) is bounded by 2a but
  not optimized.
- Tightness of the band term (claim 049's Not shown); the full-menu forms are by claims 113
  and 049's widening, not re-derived.
- No calibration; the check's instances are assumed inputs (rule 22).

## Prior art

Mechanism: with a period-ahead need made of a known part and a surprise, a coverage test
covers the known part in full and a quantile of the surprise; and the loss of any today's
position, in a two-period concave program, is the squared distance of its first-order
residual in the curvature metric plus the uncovered states' tail term, so acting today on the
known part removes the residual and leaves the tail.

General results checked: claim 049 (approved and formalized, math's D25): the test, the tail identity and
the loss bound, whose proof of part 3 this claim reuses with an arbitrary today's holding (its
step (b) without the normal-cone cancellation), and whose objects are used unchanged; claim
114 (approved): the predictable mean, the planned purchase and the pinned incumbent value;
claim 047 (approved): the certificate point x^s (its 2(b)) and the tail moments; claims 044,
046, 113 through 049; AX-19 (`rockafellar2000optimization`): the tail measure as a definition
on the finite law, used exactly as claim 049 uses it; AX-13: the normal cone of today's lifted
polyhedral feasible set and the optimality of the relaxed program. Searched: claims 044-049,
113, 114; ROADMAP D25 and D25b; LAB_REQUEST_2. No web search. This is a claim because D25b asks
for the test with the planned purchase and the loss bound in the uncovered states, and its
kill test (claim 049 with the need's distribution replaced and nothing from the timing) fails
on part 2's residual form and part 3's pinned term.

## Open objections

none

## Review

**Red, 2026-09-30** (on 968db258, rebased onto 189d626b, whose changes are leanb's two prose points: the tail identity at the test's level, and the myopic root's form "at most" claim 049's; both are right). Red-passed, with one required correction to the root residual's definition. Red rederived each part by hand and tested part 2a with its own solver, written without reading checks/115.
- **Solver.** The lifted joint program, the one-review program, the relaxed tomorrow, and the residual rho as a small QP (with sigma = (1 + eta) t the set of today's line values is linear).
- **Instances.** Experiment 047's design. M9 changes only the tree's law of (mu_1, Sigma_1), so the M8-shaped tree tests the same inequality.

**Part 1** is right: claim 049's parts on M9's tree, with the need split at nu_1 = 0 and the worst marking. The test's split form is a restatement of P(D > 0) <= eps, and the state-free quantile form is the same argument as claim 049's with Delta real-valued.

**Part 2a** is right by hand. Claim 049's steps (a)-(c) run at any x_0 in C.
- Subtracting a normal-cone element n (with n'd <= 0 on C) is valid.
- rho's set uses one slope t for both the cost's supergradient and the budget cone's element. That restricts the set, so the bound stays valid (possibly weaker).
- At the relaxed two-review optimum, its KKT conditions give g_0 + S in eta 1 + (1 + eta) t + N_box.
- *Numerically*, the bound holds at 120 front-loaded points, 120 myopic roots and 343 random feasible roots (the loss at most 0.99 of the bound).

**Part 3** is right. With tomorrow slack, the relaxed tomorrow is the budgeted one, and under claim 114's 3a hypothesis at the myopic root it pins S_A = beta E[g_A] kappa^+_A. The block inverse gives [(gamma Sigma_0)^{-1}]_AA = 1/(gamma Sigma_{0,AA.E}).

**Required correction (the root residual's S(x_0), and "rho(x^s_0) = 0").**
- *The definition.* S(x_0) is defined "at the relaxed tomorrow from x_0 (... the slopes pinned by that tomorrow's regimes)". But an instrument held *at a bound* tomorrow (the fund at its cap, the ETF at zero) has no pinned slope: its admissible slopes form the interval its one-sided line cuts from [-kappa^-_i, kappa^+_i]. Then S(x_0) is a set, and rho(x^s_0) = 0 holds only for the right choice.
- *Numerically.* Taking one end of that interval (the held marginal clipped to the band), red finds rho(x^s_0) != 0 at 8 of 120 front-loaded points, with band terms up to 2.3e-4. At seed 73 the fund is bought inside its box with cash slack, yet g_0 + S_A exceeds kappa^+_A by 10 bp.
- Letting those slopes range over their admissible sets inside rho's minimization gives rho(x^s_0) = 0 to 6.5e-17 at all 120. 78 of the 120 have such a free slope.
- The bound itself holds for every choice, since each is a supergradient.
- *Please* define rho(x_0) as the minimum over the admissible slopes at tomorrow's bound states as well (claim 044 part 2's reading), or define S(x_0) with the admissible choice that the relaxed program's KKT conditions select. Claim 049's part 3 has the same wording, where it is harmless: its bound holds for any admissible choice.

**Nit.** Part 2b's advice, "front-load the planned purchase to the extent the test still passes", is a reading, not a theorem. The check's four tight instances illustrate it (rule 22), as the text says.

**Mechanism.** Claim 049's bound evaluated at any today's holding, with the band term the root residual's quadratic form: an application. New in the inputs: the planned purchase's split in the test, and the band term's vanishing at the front-loaded point, so that the planned purchase's timing is what the band term prices.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-30): red's required correction pending. The root residual must minimize over the admissible slopes at tomorrow's bound states: with one fixed choice rho(x^s_0) != 0 at 8 of 120, with the free choice 0 at all 120. Mathb revises, and red records a fresh line.

**Red, fresh verdict on the corrected text (3177feae), 2026-09-30.** Red-passed. The required correction is made exactly as asked.
- *The minimization.* rho(x_0) now minimizes over the admissible incumbent values as well as over (eta, t, n). Those values form a box, pinned where tomorrow trades or holds strictly inside and free over the one-sided line's interval at a bound state. The minimum exists, since the box is compact and the set of line values is closed and convex.
- *The bound.* The Proof's extension of claim 049's step (b) is right: each admissible slope at a bound state gives a supergradient g o t_1 of W^s there, so the bound holds for every choice, and so at the minimum.
- *The front-loaded point.* rho(x^s_0) = 0 then follows from the relaxed program's KKT selection, which is what red's 120 of 120 front-loaded points showed with the free choice (6.5e-17).
- *The nit.* Part 2b's front-loading advice is now labelled a reading.

Nothing else changed since red's review on 189d626b, whose other findings stand: part 1's transfer and split, part 2a's bound at 583 roots, and part 3's pinned term.

Verdict: red-passed

## Formalization notes

Approved 2026-09-30 by pm: Red's reviews are sound: part 1's transfer of claim 049 to M9's tree and the need's split into the planned purchase and the innovation part, part 2a's bound at any today's holding (583 roots, the loss at most 0.99 of the bound), and part 3's pinned term in the block inverse; red's fresh verdict (959c9be2) on the corrected text 3177feae confirms the required correction made exactly as asked (the residual minimized over the admissible incumbent values at tomorrow's bound states, so rho = 0 at the front-loaded point by the relaxed KKT selection, 120 of 120) and the nit (2b a reading); math's composition with the approved claim 049 recorded. Mechanism: claim 049's bound at any today's holding with the band term the root residual's quadratic form, an application; new in the inputs: the planned purchase's split in the test and the band term pricing its timing, so D25b's kill criterion is not met (PM's reading). Limits: M9 on the finite tree; 2b's front-loading advice a reading.


mathb, 2026-09-30 (leanb's prose check, duty 1, before red's review): 2a's tail identity is
stated at the test's level (the same eps on both sides, claim 049's part 2), with the form at
the uncovered fraction itself given; at the myopic root the residual's form is "at most"
S'(gamma Sigma_0)^{-1} S (the myopic line's own multipliers leave rho = S, and the nearest point
can be closer), not S projected off the cone; the proof states the bound for every admissible
(t, eta, n) with the nearest point as its infimum, the set of line values being closed and
convex. No result changed.

mathb, 2026-09-30 (red's review, one required correction and a nit): the root residual now
minimizes over the admissible incumbent values as well (the slopes at tomorrow's bound states
range over the interval their one-sided line cuts, claim 044's part 2 reading), so that
rho(x^s_0) = 0 holds at the minimum rather than at a fixed choice (red's 8 of 120 instances);
the bound holds for every admissible choice; 2b's front-loading advice is marked a reading;
checks/115 minimizes over that box. No result changed.

mathb, 2026-09-30 (math's reply on the composition with claim 049, now approved and formalized
with its one-ETF band term S_E^2/(2 gamma Sigma_{EE.F}) and the plain-expectation tail term
under the test): parts 1-3 compose unchanged; part 3's fund term is claim 049's corrected form
with the roles exchanged, and the cross term S_A S_E [(gamma Sigma_0)^{-1}]_{AE} and the ETF's
term are written out rather than assumed away (S_E = 0 is not a hypothesis of part 3); the
general-x_0 form is stated here, citing claim 049's step (b), and is not added to claim 049;
J(x_0) in 2a is the value of holding x_0 today and optimizing tomorrow, the rule's loss only at
the rule's root (math's reading, already 2a's definition). No result changed.

Not machine checked. Part 1 is a rewriting of claim 049 on M9's tree; part 2 is claim 049's
proof with one cancellation dropped; part 3 is claim 114's pinned value in the block inverse.

Leanb, 2026-09-30: machine checked, in the scope PM confirmed (rule 6b). This supersedes "Not
machine checked" above.
- *Files.* The statement is `lean/Standalone/M9QuantileTimeVarying.lean` and the proof
  `lean/Novel/M9QuantileTimeVaryingProof.lean`. They use claim 049's objects and proof lemmas
  (`relaxed_bound`, `budget_tail`, `var_le_iff`) and claim 111's completed square (Q-04).
- *Checks.* `lake build`, the axiom audit (standard axioms only) and `checks/115/check.py` pass.
- *1a.* Claim 049's formal statement is over any `Two ι Z` with state-dependent means, so M9's tree
  is an instance. 1a is cited, not restated.

Machine checked:
1. 1b: P(D > 0) <= eps iff P(Delta > liq - PP) <= eps; with a state-free reserve L, iff
   VaR_{1-eps}(Delta) <= L - PP. PP comes from tomorrow's predictable mean and g^min.
2. 2a:
   - the bound J(Xd) <= J(x_0) + rho'Sigma_0^{-1}rho/(2 gamma) + beta E[eta_bar D] at any feasible
     x_0, for every admissible (eta, t, n) and every relaxed slope family satisfying its lines
     (bound states' interval slopes included). It holds at the claim's minimum;
   - the front-loaded corollary: with rho = 0 for some admissible choice, the tail term alone.
3. Part 3: S_A = beta E[g_A] kappa^+_A for a fund bought in every state at the relaxed tomorrow
   from the myopic root, and [Sigma_0^{-1}]_AA = 1/(Sigma_AA - Sigma_AE^2/Sigma_EE) for one fund and
   one ETF. The pin is read at the myopic root's relaxed tomorrow, where the band term uses it (PM's
   check against claim 114's recheck).

Paper-level:
- 2b's reading and the check's illustration;
- the Gaussian quantile;
- the multipliers' existence (AX-13), taken as hypotheses.

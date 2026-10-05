---
id: 106
title: "The cost of the ETF-only restriction, in the inputs: the value of the forgone fund purchases, a sum over funds of the squared positive excess of net alpha over the purchase rate plus the risk charge on the incumbent, over twice the fund's curvature; the frozen-funds baseline adds the value of the forgone sales; unreachable directions and ETF frictions enter through the reduced alpha and the re-hedge costs"
status: formalized
model_version: M7
depends_on: [029, 31, 104, 105]
axioms_used: [AX-13]
formal: lean/Standalone/M7EtfOnlyRestrictionCost.lean
direction: D15b
---
## Statement

D15b's item (i), the first of the rule 22 audit's recheck items: the cost of the ETF-only
restriction as a function of net alpha, missing exposure, costs, fees and starting holdings,
with an ETF-only rule that may sell funds. It is stated for one review of the general model,
exactly under spanning frictionless ETFs, with one unreachable fund through claims 104-105's
reduced moments, and as a bracket under ETF frictions through claim 102's re-hedge costs
(claim 102 is at proposed, so its lines are reproved here where used). It also says what the
frozen-funds baseline of experiments 022-025 measured instead. It imports no literature theorem
except, for part 1a's criterion that C^0 = 0 iff the ETF-only optimum is jointly optimal, the
polyhedral KKT theorem of ledger entry AX-13 through claim 104's part 0; every other statement
is proved without it.

**Setting.** Claim 104's: one review of an M7 instance in M5's reference case, N funds, M ETFs,
K factors, beliefs (lambda_hat, alpha_hat), Sigma~_f = Sigma_f + P^lambda, V = Sigma_A + P^alpha
diagonal with entries v_i, gamma > 0, fund rates kappa^+_i, kappa^-_i, caps bar x_i, incumbents
x^-_i in [0, bar x_i], ETF rates, fees c^E and residuals Sigma_E as stated in each part, funded
cash, the feasible set F, the objective Q. Three action classes and their values:

```
F   (full trading),                                   J   = max_F Q,
E^0 = {x in F : x^A = x^{A-}}   (ETF-only, funds frozen),   J^0 = max_{E^0} Q,
E^- = {x in F : x^A <= x^{A-}}  (ETF-only, funds may be sold, not bought),   J^- = max_{E^-} Q,
```

all attained (compact sets, continuous objective), with E^0 subset of E^- subset of F, so
J^0 <= J^- <= J. The *cost of the ETF-only restriction* is C^- = J - J^-; the *frozen-funds cost*
is C^0 = J - J^0 = C^- + (J^- - J^0), the second term the *value of the permitted fund sales*.
For a fund write psi_i(a) = alpha_hat_i a - (gamma/2) v_i a^2 - kappa^+_i (a - x^-_i)^+ - kappa^-_i (x^-_i - a)^+,
lo_i = (alpha_hat_i - kappa^+_i)/(gamma v_i), hi_i = (alpha_hat_i + kappa^-_i)/(gamma v_i), and the
*purchase excess* and *sale excess*

```
p_i = alpha_hat_i - kappa^+_i - gamma v_i x^-_i,      s_i = gamma v_i x^-_i - alpha_hat_i - kappa^-_i,
```

net alpha over the purchase rate plus the risk charge on the incumbent, and the risk charge
over net alpha plus the sale rate (at most one of them is positive, since
kappa^+_i + kappa^-_i >= 0).

### Part 1. Structure, any inputs

1a. C^- = 0 if and only if no fund is bought at the joint optimum (x_J^A <= x^{A-}); C^0 = 0 if and
    only if no fund is traded at it, which claim 102's ETF-optimized test decides at the
    ETF-only optimum (reproved in part 1's proof for E^0 through claim 104's part 0, the one
    use of AX-13 in this claim). The restriction costs exactly the value of the purchases it
    forbids.

1b. J^- - J^0 >= 0 is the value of selling funds while keeping the ETF sleeve optimal for the
    funds kept; it is zero iff no fund is sold at the E^- optimum. Experiments 022-025's
    "ETF-only" baseline is E^0, so their "joint over ETF-only" figures are C^0 = C^- + (J^- - J^0)
    and include the value of selling the assumed bad incumbents, as the human's note said.

### Part 2. Spanning frictionless ETFs: closed forms

Assume M = K with B^E invertible, kappa_E = 0, Sigma_E = 0, c^E = 0, and the budget and every ETF
bound slack at the three optima. Then

```
C^-  = sum_i [ psi_i(a_i) - psi_i(min(x^-_i, hi_i^box)) ]  = sum over funds with p_i > 0 of  { (p_i)^2/(2 gamma v_i)   if lo_i <= bar x_i,
                                                                                          psi_i(bar x_i) - psi_i(x^-_i)   if lo_i > bar x_i },
J^- - J^0 = sum over funds with s_i > 0 of  { (s_i)^2/(2 gamma v_i)   if hi_i >= 0,   psi_i(0) - psi_i(x^-_i)   if hi_i < 0 },
```

where a_i = clip(x^-_i, lo_i, hi_i) in the box is claim 102's alpha-band holding and hi_i^box its
upper clip. So, in the inputs: the ETF-only restriction costs the sum over the funds it would
have bought of the squared purchase excess over twice the fund's curvature gamma v_i,
v_i = sigma^2_{A,i} + p_i the residual plus alpha-posterior variance; a fund contributes iff
its net alpha exceeds its purchase rate plus the risk charge on its incumbent, quadratically
in the excess; premium beliefs, their precision, the loadings and the ETF sleeve do not enter;
alpha precision enters only through v_i, which scales the contribution down. The frozen-funds
cost adds the same expression on the sale side. From zero incumbents, C^- = sum_i [(alpha_hat_i - kappa^+_i)^+]^2/(2 gamma v_i) when
lo_i <= bar x_i for every fund (otherwise that fund's term is its cap form psi_i(bar x_i) - psi_i(0))
and J^- - J^0 = 0: the restriction costs exactly the positive-net-alpha funds' value, and the
frozen baseline agrees with the restriction proper.

### Part 3. One unreachable fund, everything else frictionless

In claim 104's 2c setting (one fund i with an unreachable loading component, ETFs
frictionless, bounds slack except the fund's), the same formulas hold with fund i's reduced
moments alpha^red_i = alpha_hat_i + B^A_i J' lambda_hat and s^red_i = v_i + B^A_i Sigma~_{U.R} (B^A_i)'
in place of alpha_hat_i and v_i: p_i = alpha^red_i - kappa^+_i - gamma s^red_i x^-_i, and its
contribution (p_i)^2/(2 gamma s^red_i). Missing exposure therefore raises the restriction's
cost by the unreachable premium net of its hedge, credited to the fund's alpha, and lowers it
through the unhedgeable variance in s^red_i: an ETF-only manager who cannot reach a premium
direction forgoes it, and the forgone value is the fund's excess in that direction.

### Part 4. ETF frictions (spanning): a bracket through the re-hedge costs

Assume spanning, kappa_E and c^E present, Sigma_E = 0, and at the three optima a slack budget
with cash room for the netting trades' cost and every ETF strictly inside its box with room for
the netting trades below. With the netting
vectors r_i = R'(B^A_i)', the re-hedge costs h^+_i (netting a unit purchase) and h^-_i (a unit
sale) of claim 102, and A^0_i = alpha_hat_i + r_i' c^E - gamma v_i x^-_i (the fund's reduced marginal
at the incumbent),

```
sum_i g_i(A^0_i - kappa^+_i - h^+_i, bar x_i - x^-_i)   <=   C^-   <=   sum_i g_i(A^0_i - kappa^+_i + h^-_i, bar x_i - x^-_i),
sum_i g_i(-A^0_i - kappa^-_i - h^-_i, x^-_i)             <=   J^- - J^0   <=   sum_i g_i(-A^0_i - kappa^-_i + h^+_i, x^-_i),
g_i(m, d) = max over 0 <= delta <= d of [ m delta - (gamma v_i/2) delta^2 ] = m^2/(2 gamma v_i) when 0 <= m <= gamma v_i d, m d - (gamma v_i/2) d^2 when m > gamma v_i d, 0 when m <= 0,
```

the room restriction delta <= bar x_i - x^-_i for purchases and delta <= x^-_i for sales being
part 2's cap and floor adjustments. The ETF frictions enter the restriction's cost only through the effective purchase
rate, which lies between kappa^+_i - h^-_i and kappa^+_i + h^+_i, and the fee credit r_i' c^E.

**Reading for D15b** (not a further theorem). The cost of restricting a fund-of-funds manager
to ETF adjustment, with fund sales allowed, is the value of the fund purchases the
restriction forbids: in the inputs, a fund is worth buying when its net alpha exceeds its
purchase rate plus gamma times its residual-plus-posterior variance times its incumbent, and
the value forgone is that excess squared over twice gamma times that variance, with the
unreachable premium credited to the alpha when the ETFs cannot reach a direction and the ETF
re-hedge cost added to the rate when ETFs are costly. It is zero when no fund's net alpha
clears its purchase rate, whatever the premia and loadings, and it is independent of the
assumed incumbent except through the risk charge. What experiments 022-025 reported as the
ETF-only restriction's cost is this plus the value of selling the incumbents they assumed,
which the restriction proper does not forbid.

## Proof

### 1. Structure

E^0 subset of E^- subset of F gives J^0 <= J^- <= J. If x_J^A <= x^{A-} then x_J is in E^- and
J^- = J; conversely if J^- = J the (unique) E^- optimum attains J and is the joint optimum,
which then has x^A <= x^{A-}. Likewise C^0 = 0 iff x_J is in E^0 iff no fund is traded at it;
the ETF-optimized test: if x_J is in E^0 it is the E^0 optimum, so C^0 = 0 iff the E^0 optimum
is jointly optimal, which claim 104's part 0 decides at that point (the fund coordinates must
have their marginals in their zero-trade slope sets for some admissible multiplier). 1b is
the definition and the same optimum comparison for E^- against E^0.

### 2. Spanning frictionless

By claim 104's part 2a (self-contained), in the coordinates (x^A, y = B'x) the objective is
lambda_hat' y - (gamma/2) y' Sigma~_f y + sum_i psi_i(x_i), and with the budget and ETF bounds
slack the three classes differ only in the fund coordinates' constraints: F allows
x_i in [0, bar x_i], E^- allows x_i in [0, x^-_i], E^0 fixes x_i = x^-_i; the exposure part is
maximized at y* in every class. Hence J - J^- = sum_i [max_{[0, bar x_i]} psi_i - max_{[0, x^-_i]} psi_i]
and J^- - J^0 = sum_i [max_{[0, x^-_i]} psi_i - psi_i(x^-_i)]. Each psi_i is concave with the kink
at x^-_i; its maximizer on the box is the clip a_i (claim 029's last-review band); on [0, x^-_i]
it is min(x^-_i, a_i) when a_i <= x^-_i or x^-_i when a_i > x^-_i, that is min(x^-_i, hi_i^box). If
a_i > x^-_i (the fund is bought), which happens iff lo_i > x^-_i iff p_i > 0, then
psi_i(a_i) - psi_i(x^-_i) with a_i = lo_i <= bar x_i equals
(alpha_hat_i - kappa^+_i)(lo_i - x^-_i) - (gamma v_i/2)(lo_i^2 - (x^-_i)^2) = (lo_i - x^-_i)[gamma v_i lo_i - (gamma v_i/2)(lo_i + x^-_i)] = (gamma v_i/2)(lo_i - x^-_i)^2 = (p_i)^2/(2 gamma v_i),
and when lo_i > bar x_i the clip is bar x_i and the difference is psi_i(bar x_i) - psi_i(x^-_i).
The sale side is the mirror: a_i < x^-_i iff hi_i < x^-_i iff s_i > 0, and
psi_i(hi_i) - psi_i(x^-_i) = (s_i)^2/(2 gamma v_i) when hi_i >= 0, else psi_i(0) - psi_i(x^-_i).
The zero-incumbent readings set x^-_i = 0.

### 3. One unreachable fund

Claim 104's part 2c (and claim 105's use of it) reduces the joint problem, after maximizing
over everything but fund i's holding a, to psi^red_i(a) = alpha^red_i a - (gamma/2) s^red_i a^2 - C_i(a - x^-_i)
plus terms free of a; the same reduction holds for E^- and E^0, since they constrain only the
fund coordinates and the reachable exposure is re-optimized identically (the other funds and
the ETFs are frictionless and their bounds slack). Part 2's computation then applies to
psi^red_i with (alpha^red_i, s^red_i), and to the other funds with (alpha_hat_i, v_i).

### 4. ETF frictions

*Lower bound on C^-.* Let x^- * be the E^- optimum. From it, for each fund i with
A^0_i - kappa^+_i - h^+_i > 0, buy delta_i = min((A_i(x^-*) - kappa^+_i - h^+_i)/(gamma v_i), bar x_i - x^-*_i)
of fund i and trade -r_i delta_i in the ETFs (feasible: ETFs interior with room; the total
exposure is unchanged, so the exposure part of Q is unchanged). With Sigma_E = 0 the fund's
part changes by alpha_hat_i delta_i - (gamma v_i/2)(2 x^-*_i delta_i + delta_i^2) - kappa^+_i delta_i, the fee
part by + r_i' c^E delta_i (the netting sells the ETFs whose fee the fund's by-product now
saves), and the ETF cost by at most h^+_i delta_i (a unit of netting costs at most h^+_i, and the
cost is subadditive, so the combined netting of all funds costs at most the sum). Adding over
funds, J >= Q(x^-*) + sum_i [(A_i(x^-*) - kappa^+_i - h^+_i) delta_i - (gamma v_i/2) delta_i^2], and since
x^-*_i <= x^-_i gives A_i(x^-*) >= A^0_i, each bracket at its maximizing delta_i is at least
[(A^0_i - kappa^+_i - h^+_i)^+]^2/(2 gamma v_i) (or the capped value). *Upper bound.* Let x* be the
joint optimum, with purchases delta_i = (x*_i - x^-_i)^+. Undo them with netting: x~ has fund i
at x*_i - delta_i and ETFs at x*^E + sum_i r_i delta_i; x~ is in E^- and feasible (ETFs interior
with room). Then J^- >= Q(x~), and Q(x*) - Q(x~) equals the fund parts' change
sum_i [(alpha_hat_i - gamma v_i x^-_i) delta_i - (gamma v_i/2) delta_i^2 - kappa^+_i delta_i] plus the fee difference
sum_i r_i' c^E delta_i plus the ETF-cost difference C_E(u~) - C_E(u*) <= C_E(sum_i r_i delta_i) <= sum_i C_E(r_i delta_i) = sum_i h^-_i delta_i
(u~ = u* + sum_i r_i delta_i; subadditivity of C_E; a unit of +r_i, buying back the ETFs the
netting sold, costs h^-_i). So C^- <= sum_i max_{delta >= 0} [(A^0_i - kappa^+_i + h^-_i) delta - (gamma v_i/2) delta^2]
= sum_i [(A^0_i - kappa^+_i + h^-_i)^+]^2/(2 gamma v_i). The sale bracket is the mirror with the
E^0 optimum, sales delta_i = (x^-_i - x_i)^+, netting +r_i delta_i (a unit costs at most h^-_i) and
its undoing (at most h^+_i).

## Checks

`uv run python checks/106/check.py` (exits non-zero on failure; a check, not a proof). Random
assumed one-review instances solved with cvxpy/CLARABEL (floating), the three classes solved
directly: (i) spanning frictionless instances, C^- and J^- - J^0 against part 2's closed forms;
(ii) one-unreachable-fund instances, the same against part 3's reduced forms; (iii) friction
instances with Sigma_E = 0, part 4's brackets; (iv) part 1's structure: C^- = 0 iff no fund is
bought at the joint optimum, C^0 = 0 iff none is traded.

## Not shown

- One review; the multi-review restriction's cost (the value of purchases forgone over a
  horizon, with the band's narrowing of claims 029 and 100) is not stated.
- Part 4 assumes Sigma_E = 0 and ETFs interior with room for the netting trades; with ETF
  residual risk the bracket gains terms in gamma r_i' Sigma_E x^E, and an ETF at zero cannot be
  sold to net a purchase, which raises the restriction's cost by the exposure deviation the
  purchase then carries (claim 102's part 5(b) case).
- Several unreachable funds couple through Sigma~_{U.R}; the pooled alpha prior couples the
  funds' v_i.
- No calibration or magnitude; the formulas are for the analyst's regime map (note sent), and
  experiments 022-025's figures are not re-read here beyond part 1b's identification of what
  their baseline measured.

## Prior art

Mechanism: restricting a decision maker to a subset of instruments costs the value of the
forbidden trades at the optimum; when the forbidden instrument's decision separates into a
one-variable band, that value is the squared distance of the incumbent from the band's
purchase edge, in the band's own curvature, summed over instruments, and when an offsetting
instrument's frictions or an unreachable direction shift the edge, they shift the distance.

General results checked: claim 102 (proposed; its bands reproved through claim 104's
self-contained parts), claims 104 and 105 (approved): the alpha band, the reduced moments and
the re-hedge costs; claims 004-008 (formalized, M2): the one-fund ETF-only restriction and its
substitution benchmarks, whose general-N one-review cost this is; claim 029 (formalized): the
one-variable band; `treynor1973security` (full text): the value of active positions as alpha
over residual variance, part 2's frictionless content (the excess squared over twice the
curvature is the Treynor-Black appraisal value net of the purchase rate and the incumbent's
risk charge); experiment 006 and the rule 22 audit's D1 entry: the one-point magnitude this
formula replaces. None states the restriction's cost in the inputs with sales allowed or the
frozen-baseline decomposition; no priority is claimed.

Searched: claims 004-009, 102, 104, 105, the rule 22 audit and D1 branch memo in FINDINGS, the
human's note on experiments 022-025's baseline, the D15b roadmap entry. No web search.

## Open objections

none

## Review

**Red, 2026-09-29.** I checked parts 1-4 by hand, tested all four with red's own cvxpy/CLARABEL scripts (not reading `checks/106/check.py`), solving the three action classes F, E^- and E^0 directly, and ran `checks/106/check.py`, which passes. Every result holds, and there are no required corrections. There are four nits.

**Hand check.**
- *Part 1.* This follows from E^0 subset of E^- subset of F and uniqueness of the joint optimum.
- *Part 2.* In spanning coordinates the three classes differ only in the fund boxes: [0, bar x_i], [0, x^-_i] and {x^-_i}. The exposure part is maximized at y* in each.
  - For a bought fund (p_i > 0 iff lo_i > x^-_i), psi_i(lo_i) - psi_i(x^-_i) = (gamma v_i/2)(lo_i - x^-_i)^2 = p_i^2/(2 gamma v_i), with the cap case when lo_i > bar x_i.
  - The sale side is the mirror.
  - At most one of p_i and s_i is positive, since p_i + s_i = -(kappa^+_i + kappa^-_i).
- *Part 3.* Claim 104's 2c reduction (approved) carries over to E^- and E^0, since those classes constrain only fund coordinates and the reachable exposure is re-optimized identically.
- *Part 4.*
  - The lower bound: buy delta with netting from the E^- optimum. The combined netting costs at most sum_i h^+_i delta_i by subadditivity, and A_i(x^-*) >= A^0_i.
  - The upper bound: undo the joint optimum's purchases with netting. The quantity to bound is C_E(u~) - C_E(u*) <= C_E(sum_i r_i delta_i) = sum_i h^-_i delta_i, and the result is as displayed.

**Independent numerical tests** (red's scripts, not committed).
- *Parts 1-2.* On 150 spanning frictionless instances (K = M = 2, N = 3, random loadings, beliefs, rates, incumbents up to 0.15, caps 0.3):
  - J - J^- and J^- - J^0 equal the closed forms, with the cap and floor cases, to 1e-8;
  - C^- = 0 exactly when no fund is bought at the joint optimum, and C^0 = 0 exactly when none is traded, in every case.
- *Part 3.* On 150 one-unreachable-fund instances (K = 2, M = 1, fund 0 with an unreachable loading, fund 1 in the span), both differences equal the reduced forms, with (alpha^red, s^red) for fund 0 and (alpha_hat, v) for fund 1, to 1e-7.
- *Part 4.* On 200 friction instances (spanning, ETF rates up to 30 bp, fees, Sigma_E = 0, ETF box slack), the four brackets hold in every case once each term's delta is restricted to the fund's room: [0, bar x_i - x^-_i] for purchases and [0, x^-_i] for sales.
  - Red's first pass omitted that restriction, and the sale-side lower bound then "failed" whenever the unconstrained sale would go below zero. The claim does state the adjustment ("with the cap or floor adjustment of part 2"), so this was red's error, not the claim's.

**Nits.**
- Part 4's display should show the room restriction explicitly, since the unrestricted squares overstate the bounds: max over 0 <= delta <= bar x_i - x^-_i of [(A^0_i - kappa^+_i -+ h_i) delta - (gamma v_i/2) delta^2], and the same for sales with delta <= x^-_i. The prose "each term evaluated with the cap or floor adjustment" is correct but easy to misapply, as red's first test showed.
- In Proof 4, the upper bound's prose says "C_E(u*) - C_E(u~) <= C_E(-sum_i r_i delta_i) <= sum_i h^-_i delta_i". The quantity needed is C_E(u~) - C_E(u*) <= C_E(sum_i r_i delta_i) = sum_i h^-_i delta_i, a unit of +r_i being the ETF purchases that undo a purchase's netting. The result is unchanged.
- Part 2's zero-incumbent reading C^- = sum_i [(alpha_hat_i - kappa^+_i)^+]^2/(2 gamma v_i) holds when lo_i <= bar x_i. Otherwise use the cap form.
- Part 4's lower bound also needs room in the budget for the netting trades' cash, (1 - sum_j r_ij) delta_i plus costs, not just a slack budget at the optimum. The ETF "room" hypothesis should say so.

**Mechanism (4b).**
- The cost of forbidding a class of trades is the value of the forbidden trades.
- Under spanning frictionless ETFs it separates per fund into the value of a one-variable band move: the squared excess over twice the curvature.
- An unreachable direction shifts the fund's reduced alpha (claim 031, through claim 104).
- ETF frictions bracket the effective rate by the re-hedge costs (claim 102's slope bracket, reproved).
- This is elementary and correct. Part 1b's identification that experiments 022-025's "ETF-only" figure is C^0, and so includes the value of selling the assumed incumbents, is right and useful for the audit.

Verdict: red-passed

## Formalization notes

mathb, 2026-09-29, after PM's approval: red's four nits, no result changed. Part 4's brackets
now show the room restriction in the display (delta at most the room to the cap for purchases
and at most the incumbent for sales, through g_i); its hypothesis adds cash room for the netting
trades; proof 4's upper-bound prose reads C_E(u~) - C_E(u*) <= C_E(sum r_i delta_i) <= sum h^-_i delta_i;
part 2's zero-incumbent reading is stated for lo_i <= bar x_i with the cap form otherwise.

Approved 2026-09-29 by pm: Red's hand check of parts 1-4 is sound, with no required corrections. The ETF-only restriction's cost is the value of the forbidden trades: under spanning frictionless ETFs a per-fund squared excess of net alpha plus the incumbent risk charge over the purchase rate, over twice the curvature, with cap and floor forms (150 instances, to 1e-8); frozen funds add the forgone sales; an unreachable direction enters through the reduced alpha (150 instances, to 1e-7); ETF frictions bracket it by the re-hedge costs (200 instances). Mechanism: the value of forbidden trades read through claim 104's band and reduction, an application. New for D15b item (i): the restriction's cost in the inputs; part 1b shows experiments 022-025's ETF-only figure was the frozen-funds cost, including the value of selling the assumed incumbents, supporting the rule 22 audit. Nits routed to mathb: show part 4's room restriction explicitly, fix the upper-bound prose, the cap form of the zero-incumbent reading, and budget room for netting cash.


Not machine checked. Parts 1-4 are finite statements about three quadratic programs over
nested polyhedra; part 2 is closed-form algebra on one-variable concave functions.

Lean, 2026-09-29 (final): parts 1-4 are machine checked; part 1b's reading of experiments 022-025
and the Reading for D15b are paper-level (scope note to PM, lean/claim106-scope-note). The statement
is in `lean/Standalone/M7EtfOnlyRestrictionCost.lean` and the proof in
`lean/Novel/M7EtfOnlyRestrictionCostProof.lean`. The proof imports claim 104's and claim 105's proof
modules (depends_on, Q-04), for the band holding, part 0, the slack-dropping lemma, the spanning
realization and the hedge value. Only part 1's multiplier-criterion conjunct takes `AX13` as a
hypothesis; the rest of part 1, and parts 2-4, are unconditional (auditor's note). `lake build`, the
axiom audit (standard axioms only) and `checks/106/check.py` pass.

Formal objects. The classes are `F`, `Em` (`E^-`) and `E0` (`E^0`), and their values are the scores
at the classes' maximizers. The fund objective is claim 104's `psi`. `buyCost` and `sellCost` are
part 2's display, `gval` is `g_i(m, d)` and `move` is a fund move with its netting trade.

Machine checked:
- Part 1, with Sigma positive definite and gamma > 0 (uniqueness of each class's maximizer):
  - J^0 <= J^- <= J;
  - C^- = 0 iff no fund is bought at the joint optimum, and C^0 = 0 iff none is traded;
  - C^0 = 0 iff claim 104's multiplier criterion holds at the ETF-only optimum (given AX-13);
  - J^- - J^0 = 0 iff no fund is sold at the E^- optimum;
  - C^0 = C^- + (J^- - J^0).
- Part 2, at the three optima, each with a slack budget and interior ETFs:
  - C^- = sum_i [psi_i(a_i) - psi_i(a^-_i)] = sum_i buyCost_i, and J^- - J^0 = sum_i sellCost_i;
  - the one-fund forms, including a^-_i = min(x^-_i, hi_i^box);
  - the zero-incumbent readings.
- Part 3: the same forms, with the unreachable fund's reduced moments from claim 104's hedge value
  and the other funds' own moments.
- Part 4 (Sigma_E = 0, spanning): the four brackets, with g_i's room restriction. The room for the
  netting trades and their cash enters as the feasibility of the four netted holdings built from
  the optima.

mathb, 2026-09-29 (auditor's note, from claim 106's FIDELITY row): axioms_used adds AX-13, which
part 1a's criterion (C^0 = 0 iff claim 104's multiplier criterion holds at the ETF-only optimum)
uses through claim 104's part 0; the Statement's "no literature theorem" sentence now excepts
that one criterion. No result changed.

---
id: 105
title: "How premium error enters fund choice, in the inputs: not at all through spanning ETFs; through the hedged unreachable part of a fund's loading as a persistent shift of its alpha band and a transient narrowing of the band, moving the decision only beyond the band's slack; and, under naive total-return selection, in full, at an explicit loss"
status: formalized
model_version: M7
depends_on: [029, 31, 104]
axioms_used: []
formal: lean/Standalone/M7PremiumErrorInFundChoice.lean
direction: D15
---
## Statement

D15's criterion (d), in the inputs, and mathb's last budgeted D15 claim. Claim 031 (formalized,
M5, quadratic costs) proves that premium beliefs reach fund choice exactly through the factor
directions the ETFs cannot reach, as a mean term through the hedge map and a risk term through
a Schur complement. This claim states, for one review of the general model with proportional
costs, what that means for the decision and for its error: which inputs let a premium error
change a fund's hold, buy or sell decision, by how much it moves the holding, what it costs,
and what a naive rule that selects funds on total estimated return loses by letting the whole
premium and its error in. Claim 029's last-review band supplies the one-variable solution, and claim 104 (approved)
supplies three lemmas: the spanning closed form (its 2a), the one-unreachable-fund reduction
(its 2c) and the loss bracket with the normal-cone term (its 3b); nothing rests on claim 102
(proposed). It imports no literature theorem.

**Setting.** One review of an M7 instance in M5's reference case (claim 104's Setting):
N funds, M ETFs with B^E of full row rank M <= K, K factors, beliefs (lambda_hat, alpha_hat) with
P = diag(P^lambda, P^alpha), Sigma~_f = Sigma_f + P^lambda positive definite, V = Sigma_A + P^alpha
diagonal with entries v_i, gamma > 0, directional fund rates kappa^+_i, kappa^-_i, fund caps
bar x_i, incumbents x^-_i <= bar x_i; ETFs frictionless (kappa_E = 0, Sigma_E = 0, c^E = 0); the
budget and every ETF bound slack at every optimum the parts compare: the joint optimum at the
true premium and at the estimated one (parts 2b-2d), and, in part 3, the naive rule's ETF
re-optimization as well. The *premium error* is e = lambda_hat - lambda,
the estimate minus the true premium vector; under M7's filter its covariance is P^lambda. With
L_E = row(B^E), Pi_R and Pi_U the projections onto L_E and its orthogonal complement, claim
031's hedge map J = Pi_U - Pi_R Sigma~_RR^{-1} Sigma~_RU and Schur complement Sigma~_{U.R}
(from Sigma~_f), define for each fund

```
u_i = Pi_U (B^A_i)'                       (the unreachable part of fund i's loading),
alpha^red_i = alpha_hat_i + B^A_i J' lambda_hat,       s^red_i = v_i + B^A_i Sigma~_{U.R} (B^A_i)',
lo_i = (alpha^red_i - kappa^+_i)/(gamma s^red_i),      hi_i = (alpha^red_i + kappa^-_i)/(gamma s^red_i),
a_i(lambda_hat) = clip( x^-_i, lo_i, hi_i ) clipped to [0, bar x_i]      (the fund's alpha-band holding),
ell_i^2 = B^A_i J' P^lambda J (B^A_i)'                   (the leak variance),
slack_i = distance from alpha^red_i - gamma s^red_i x^-_i to the complement of [-kappa^-_i, kappa^+_i]
          when the fund is held (that number lies in the band), 0 otherwise.
```

Two hypotheses are used in turn: *spanning* (M = K, B^E invertible, so u_i = 0 for every fund)
and *one unreachable fund* (M < K, exactly one fund i with u_i != 0, the others' loadings in L_E).

### Part 1. Through spanning ETFs, premium error does not enter fund choice

Under spanning, the joint optimum's fund holdings are a_i(lambda_hat) with alpha^red_i = alpha_hat_i
and s^red_i = v_i (J = 0), for every fund: they do not depend on lambda_hat, on P^lambda or on the
loadings. Premium error enters only the exposure, y* = (gamma Sigma~_f)^{-1} lambda_hat, set through
the ETFs, and its cost is the Markowitz loss e' Sigma~_f^{-1} e/(2 gamma), which is paid in the ETF
sleeve whatever the funds do. So in the inputs: with a menu that spans the factors and ETFs
that are frictionless, no premium error, however large, changes any fund's hold, buy or sell
decision; only alpha and its precision (through v_i), the fund's rates, its incumbent and its cap
do.

### Part 2. Through an unreachable direction: a persistent shift and a transient narrowing

Under one unreachable fund, the joint optimum holds fund i at a_i(lambda_hat) with the reduced
moments above (claim 031's, at one review), the other funds at their spanning holdings, and
the ETFs at the hedged exposure. Hence:

2a. *Where the premium enters.* lambda_hat reaches fund i's decision only through the scalar
    B^A_i J' lambda_hat = u_i'(lambda_hat) net of its minimum-variance hedge, a shift of the fund's
    alpha band's centre; and P^lambda only through s^red_i, which narrows the band by the factor
    v_i/(v_i + B^A_i Sigma~_{U.R} (B^A_i)') relative to a spanned fund and shrinks to
    v_i + B^A_i Sigma_{f,U.R} (B^A_i)' as P^lambda -> 0 (claim 031's part 5): the mean leak
    persists, the risk leak is transient.

2b. *How much the holding moves.* As a function of lambda_hat, a_i is continuous and piecewise
    linear: on the two trading pieces (a_i < x^-_i or a_i > x^-_i, interior to the box) its
    gradient is J (B^A_i)'/(gamma s^red_i), and on the hold piece and at the fund's bounds it is
    zero. A premium error e therefore moves the holding by at most
    |B^A_i J' e|/(gamma s^red_i), and by exactly that when the true and estimated holdings lie on
    the same trading piece. The expected squared move under e ~ (0, P^lambda) is at most
    ell_i^2/(gamma s^red_i)^2.

2c. *When it changes the decision.* Write m = alpha^red_i(lambda) - gamma s^red_i x^-_i for the
    fund's true marginal at the incumbent and delta = B^A_i J' e for the hedged unreachable
    premium error. At the estimate lambda_hat the fund is bought iff m + delta > kappa^+_i and
    x^-_i < bar x_i, sold iff m + delta < -kappa^-_i and x^-_i > 0, and held otherwise. Hence, if
    the fund is held at the true premium (m in [-kappa^-_i, kappa^+_i], with slack slack_i), a premium
    error changes the decision if and only if delta > kappa^+_i - m with x^-_i < bar x_i (a
    purchase) or delta < -kappa^-_i - m with x^-_i > 0 (a sale); in particular no error with
    |delta| <= slack_i moves a held fund, and a fund at zero cannot be sold nor a fund at its
    cap bought, whatever the error. Conversely a fund bought at the true premium (m > kappa^+_i,
    x^-_i < bar x_i) is turned into a hold or a sale exactly by an error with
    delta <= kappa^+_i - m < 0 (at equality the estimated band's lower edge is the incumbent, and
    the fund is held). So the decision is robust to premium error up to the band's slack in
    alpha units, measured along the hedged unreachable direction only, and only within the box.

2d. *What it costs.* Holding a_i(lambda_hat) when the truth is lambda, the loss in the fund's
    reduced objective psi_i (claim 104's psi_i with the true reduced alpha) is
    psi_i(a_i(lambda)) - psi_i(a_i(lambda_hat)), which satisfies

    ```
    0 <= loss <= (gamma s^red_i/2) Delta^2 + (kappa^+_i + kappa^-_i + mu) |Delta|,   Delta = a_i(lambda_hat) - a_i(lambda),   |Delta| <= |B^A_i J' e|/(gamma s^red_i),
    ```

    mu the box's normal-cone term at a_i(lambda) (zero when it is interior). With e ~ (0, P^lambda)
    and a_i(lambda) interior, the expected loss is at most
    ell_i^2/(2 gamma s^red_i) + (kappa^+_i + kappa^-_i) ell_i/(gamma s^red_i): the leak variance over
    twice the fund's reduced curvature, plus the round-trip rate times the leak's standard
    deviation over the curvature. In the inputs, the cost of premium error in fund choice is
    second order in the hedged unreachable premium error and first order in it only through the
    trading cost of the misplaced trade.

### Part 3. Naive selection on total estimated return lets the whole premium in

Under spanning, consider the *naive rule* that chooses each fund's holding from its total
estimated mean mu_hat_i = alpha_hat_i + B^A_i lambda_hat and its own total variance
sigma_i^2 = v_i + B^A_i Sigma~_f (B^A_i)', by the band

```
a^naive_i = clip( x^-_i, (mu_hat_i - kappa^+_i)/(gamma sigma_i^2), (mu_hat_i + kappa^-_i)/(gamma sigma_i^2) ) clipped to [0, bar x_i],
```

and then sets the ETFs to the exposure that is optimal given those fund holdings. Its loss
against the joint optimum is exactly

```
Lambda^naive = sum_i [ psi_i(a_i(lambda_hat)) - psi_i(a^naive_i) ] >= 0,     psi_i(a) = alpha_hat_i a - (gamma/2) v_i a^2 - kappa^+_i (a - x^-_i)^+ - kappa^-_i (x^-_i - a)^+,
```

zero iff every fund's naive holding coincides with its alpha-band holding; and the premium
error enters the naive holdings in full, with gradient (B^A_i)'/(gamma sigma_i^2) on their trading
pieces, so the naive rule's expected squared holding error from premium error alone is
B^A_i P^lambda (B^A_i)'/(gamma sigma_i^2)^2 per fund, against zero for the hedged rule. In the
inputs: from a zero incumbent the naive rule buys fund i iff alpha_hat_i + B^A_i lambda_hat > kappa^+_i,
the hedged rule iff alpha_hat_i > kappa^+_i, so a fund with negative net alpha and a positive
loaded premium is bought naively and its loss is -psi_i(a^naive_i) = -[alpha_hat_i a - (gamma/2) v_i a^2 - kappa^+_i a]
at a = a^naive_i, positive whenever alpha_hat_i < kappa^+_i + (gamma/2) v_i a^naive_i; and a fund
with positive net alpha and a negative loaded premium is passed over naively, at the loss
psi_i(a_i) of the position not taken. The hedged rule's gain over the naive rule is
Lambda^naive, a formula in alpha_hat, lambda_hat, the loadings, v_i, Sigma~_f, the rates,
incumbents and caps.

**Reading for D15** (not a further theorem). Premium error enters fund choice in the inputs
through one scalar per fund, the hedged unreachable component of the fund's loading times the
error, B^A_i J' e, which is zero for every fund a spanning menu of frictionless ETFs can hedge
and nonzero exactly for loadings the menu cannot reach. That scalar shifts the fund's alpha band,
moves the holding by at most itself over gamma times the fund's reduced curvature, changes the
decision only when it exceeds the band's slack, and costs, in the fund's reduced objective, at
most its square over twice the curvature plus the trading cost of the misplaced trade (the ETF
exposure is mis-set by the same error too, at part 1's Markowitz cost in the reachable
directions, whatever the funds do); premium uncertainty narrows the band
through the Schur complement and that narrowing learns away, while the shift does not. A rule
that selects funds on total estimated return forgoes the hedge and admits the whole premium
error, at the explicit loss Lambda^naive, which is the gain from hedging the factor part with
ETFs (the program memo's Q3).

## Proof

### 1. Spanning

Claim 104's part 2a (whose proof is self-contained) gives the joint optimum under spanning:
in the coordinates (x^A, y = B'x), the objective is lambda_hat' y - (gamma/2) y' Sigma~_f y plus
the sum over funds of alpha_hat_i x_i - (gamma/2) v_i x_i^2 - C_i(x_i - x^-_i), so the y-part is
maximized at y* = (gamma Sigma~_f)^{-1} lambda_hat and each fund's part on [0, bar x_i] at the clip
of claim 029's 1a-1b (its last-review problem with curvature gamma v_i and target
alpha_hat_i/(gamma v_i)). The fund parts contain neither lambda_hat, P^lambda nor B. The exposure
loss: G(y*(lambda_hat)) evaluated at the true premium minus its maximum at the true premium is
(gamma/2)(y*(lambda_hat) - y*(lambda))' Sigma~_f (y*(lambda_hat) - y*(lambda)) = e' Sigma~_f^{-1} e/(2 gamma).

### 2. One unreachable fund

The reduction to the reduced moments is claim 104's part 2c (self-contained algebra, claim
031's Schur complement at one review): maximizing over everything but a = x_i gives, for fund i,
psi_i(a) = alpha^red_i a - (gamma/2) s^red_i a^2 - C_i(a - x^-_i) plus terms free of a, so the
joint holding is the clip a_i(lambda_hat) (claim 029's last-review band with curvature
gamma s^red_i and target alpha^red_i/(gamma s^red_i)); the other funds separate as in part 1 and
the ETFs deliver the hedged reachable exposure (claim 031's part 2 at one review). *2a* reads
off alpha^red_i and s^red_i: lambda_hat appears only in B^A_i J' lambda_hat, and P^lambda only in
Sigma~_{U.R} (through Sigma~_f = Sigma_f + P^lambda) and, when P^lambda -> 0, Sigma~_{U.R} -> Sigma_{f,U.R},
the return-only Schur complement (claim 031's part 5 argument: the Schur complement is
monotone in the matrix). *2b*: lo_i and hi_i are affine in lambda_hat with gradient
J (B^A_i)'/(gamma s^red_i), and a_i is the clip of the constant x^-_i to [lo_i, hi_i] then to the
box; a clip of a constant to an interval whose endpoints move with a common gradient is
continuous and piecewise linear, equal to the moving endpoint (gradient as stated) on the
pieces where the constant is outside the interval and the endpoint is inside the box, and
constant otherwise; the move bound is the mean-value property of a piecewise-linear
1-Lipschitz-in-that-gradient function, and the expectation bound is
E (B^A_i J' e)^2 = B^A_i J' P^lambda J (B^A_i)'. *2c*: the hold piece is the set of lambda_hat with
-kappa^-_i <= alpha^red_i - gamma s^red_i x^-_i <= kappa^+_i; a shift e changes that number by
B^A_i J' e, so it leaves the band iff the shift exceeds the slack in the leaving direction; the
purchase case is the same computation at the band's upper edge. *2d*: the loss is claim 104's
3b bracket for psi_i (its proof is self-contained: the exact Taylor expansion of the quadratic
part at the maximizer and the cost's slopes), with a_i(lambda) the maximizer of the true psi_i and
a_i(lambda_hat) the point compared; |Delta| <= |B^A_i J' e|/(gamma s^red_i) by 2b; the expectation
bound uses E Delta^2 <= ell_i^2/(gamma s^red_i)^2 and E|Delta| <= ell_i/(gamma s^red_i).

### 3. Naive selection

Under spanning, for any fixed fund vector x^A, the best exposure is y* and the ETFs deliver it,
so the value of a fund vector is sum_i psi_i(x_i) plus the same exposure term for every fund
vector (part 1's coordinates). The joint optimum maximizes each psi_i at a_i(lambda_hat); the
naive rule holds a^naive_i; the difference of values is the displayed sum, nonnegative termwise
and zero iff each a^naive_i maximizes psi_i, that is equals a_i(lambda_hat) (unique maximizer).
The naive holding's dependence on lambda_hat is through mu_hat_i = alpha_hat_i + B^A_i lambda_hat
with the clip structure of 2b, gradient (B^A_i)'/(gamma sigma_i^2) on its trading pieces, and
E (B^A_i e)^2 = B^A_i P^lambda (B^A_i)'. The zero-incumbent readings are the clips at x^-_i = 0:
the naive lower edge is positive iff mu_hat_i > kappa^+_i, the hedged one iff alpha_hat_i > kappa^+_i;
the loss of a fund bought naively is psi_i(0) - psi_i(a^naive_i) = -psi_i(a^naive_i) with the
purchase cost kappa^+_i a, positive iff alpha_hat_i a - (gamma/2) v_i a^2 - kappa^+_i a < 0 at
a = a^naive_i, that is iff alpha_hat_i < kappa^+_i + (gamma/2) v_i a^naive_i; the passed-over fund's
loss is psi_i(a_i) - psi_i(0) = psi_i(a_i) > 0 when a_i > 0.

## Checks

`uv run python checks/105/check.py` (exits non-zero on failure; a check, not a proof). Random
assumed one-review instances solved with cvxpy/CLARABEL (floating): (i) spanning frictionless
instances, the joint fund holdings unchanged under random premium perturbations while the
ETF exposure moves (part 1); (ii) one-unreachable-fund instances, the joint fund holding
against the closed form a_i(lambda_hat) along a line of premium perturbations, the piecewise
gradient J (B^A_i)'/(gamma s^red_i) on trading pieces and zero on the hold piece, the move bound,
the decision-flip test against the slack (2b-2c), and the loss bracket of 2d against the solver's
values at the true premium; (iii) spanning instances, the naive rule's loss formula against the
solver (funds fixed at the naive holdings, ETFs re-optimized) and its zero-incumbent readings
(part 3).

## Not shown

- One unreachable fund; several couple through Sigma~_{U.R} into a parallelotope of bands, and
  the per-fund scalar B^A_i J' e becomes a vector condition (claim 029's 2c shape).
- ETF frictions together with an unreachable direction (claim 031's Not shown), and ETF bounds
  that bind, which make a direction unreachable dynamically (an ETF at zero cannot be sold to
  hedge a fund's by-product); only the exact criterion of claim 104's part 0 speaks to them.
- The error e is treated as a fixed perturbation and, for the expectations, as having covariance
  P^lambda; no coverage or frequentist statement is made (M4's results are the certification
  layer, outside D15).
- One review; the multi-review leak is claim 031's under quadratic costs.
- No calibration or magnitude; the analyst's regime map moves the premium by one prior SD per
  factor and reports the fund holdings' L1 change, which 2b predicts in closed form (note sent).

## Prior art

Mechanism: when a costly instrument's exposure is offset by a cheap one at no cost, the costly
choice depends only on the costly instrument's own residual mean and variance, so an error in
the shared expected returns cannot reach it; when part of the exposure cannot be offset, the
error reaches the costly choice through that part net of the best cheap hedge, shifting the
band of inaction by that amount and narrowing it by the unhedgeable variance, and a rule that
ignores the hedge admits the whole error.

General results checked: claim 031 (formalized): the leak through unreachable directions, the
hedge map and the Schur complement, whose one-review form parts 2-3 read in the inputs;
`pastor2002investing` (full text) and `jones2002mutual` (registered): fund selection with
separate beliefs about alpha and the benchmark, the program memo's Q3 setting, without the
hedging rule or its band; `treynor1973security` (full text): funds chosen on alpha over residual
variance, part 1's frictionless content; `merton1980estimating` (registered): the size of
premium-estimation error, the input P^lambda; claim 029 (formalized): the one-variable band;
claim 104 (approved): the spanning closed form, the reduced moments' one-review algebra and
the psi bracket with the normal-cone term, used as lemmas. None states which inputs let a
premium error change a fund decision, by how much and at what cost, or the naive rule's loss;
no priority is claimed.

Searched: claims 029-031, 102, 104, the D15 roadmap entry, PM's opening note, experiment 027's
(d) protocol, the refuted directory. No web search.

## Open objections

none

## Review

**Red, 2026-09-29.** I checked parts 1-3 by hand, tested all three with red's own cvxpy/CLARABEL scripts (not reading `checks/105/check.py`), and ran `checks/105/check.py`, which passes. Every result holds. There is one required correction, about what the Proof rests on, and three nits.

**Hand check.**
- *Part 1.* Under spanning, the coordinates (x^A, y) split the objective into an exposure part and per-fund parts that contain no lambda_hat, P^lambda or B.
  - The exposure loss is (gamma/2)(y^ - y)'Sigma~_f(y^ - y), with y^ - y = (gamma Sigma~_f)^{-1} e, which equals e'Sigma~_f^{-1} e/(2 gamma).
- *Part 2.*
  - (2a) alpha^red_i and s^red_i are claim 031's reduced moments at one review. The Schur complement is monotone in Sigma~_f, so the risk leak learns away and the mean leak does not.
  - (2b) lo_i and hi_i move together with gradient J (B^A_i)'/(gamma s^red_i), so the clip of the constant incumbent is piecewise linear with that gradient or zero.
  - (2c) The held test is alpha^red_i - gamma s^red_i x^-_i against [-kappa^-_i, kappa^+_i], shifted by B^A_i J' e.
  - (2d) This is claim 104's corrected 3b bracket, with the normal-cone term mu. The expectations follow from E Delta^2 <= ell_i^2/(gamma s^red_i)^2 and Jensen's inequality.
- *Part 3.* Under spanning, the value of a fund vector with the best exposure is sum_i psi_i(x_i) plus a constant, so the naive rule's loss is the displayed sum. The zero-incumbent readings are the clip edges.

**Independent numerical tests** (red's scripts, not committed).
- *Part 1.* On 100 spanning instances (K = M = 2, N = 3, random loadings, beliefs, rates, incumbents and caps), the fund holdings do not change when the premium is redrawn, including negative premia.
- *Part 2.* On 120 one-unreachable-fund instances (K = 2, M = 1; fund 0 with an unreachable loading, fund 1 in the span) with 4 premium errors each (480 draws):
  - the solver's fund holding at lambda_hat equals the closed form a_i(lambda_hat) every time;
  - |a_i(lambda_hat) - a_i(lambda)| <= |B^A_i J' e|/(gamma s^red_i) always holds;
  - for funds held at the true premium, the flip test (|B^A_i J' e| beyond the one-sided slack) agrees with the actual decision in all cases, 51 of which flip;
  - 2d's bracket on the true reduced objective, with mu, always holds.
- *Part 3.* On 100 spanning instances, the joint value minus the value with funds fixed at the naive holdings and ETFs re-optimized equals sum_i [psi_i(a_i) - psi_i(a^naive_i)] to 1e-8.

**Required correction 1 (what the Proof rests on).**
- The Statement says "nothing rests on claims 102 or 104 (proposed)". Proof 1 and Proof 2 cite claim 104's parts 2a and 2c, and 2d uses claim 104's 3b bracket as its lemma, in the corrected form with mu.
- Claim 104 is at proposed until red's recheck (red/review-104-recheck, red-passed) merges and PM approves it. Rule 5 lets a claim build only on red-passed claims, and lean imports only depends_on (Q-04).
- Please either add 104 to depends_on and hold this claim until 104 is approved, or prove the three pieces inline. Each is short: the spanning clip, the one-unreachable reduction, and the Taylor bracket with mu. Then change the Statement's sentence to match.

**Nits.**
- 2c's "in particular a fund held with slack at least the round-trip rate cannot be moved by any error with |B^A_i J' e| <= slack_i" is vacuous. slack_i is the distance to the nearer band edge, so it is at most (kappa^+_i + kappa^-_i)/2 and never reaches the round-trip rate. Please drop it or restate it.
- The hypothesis "the budget and every ETF bound slack at the optimum" is needed at both the true and the estimated optima (2b-2d compare them), and for part 3's naive rule after the ETFs are re-optimized. Please say so.
- 2d's "loss" is the loss in fund i's reduced objective only. The ETF exposure is also mis-set by the error, at part 1's Markowitz cost (in the reachable directions). The Reading's "what it costs" should say which loss is meant.

**Mechanism (4b).** This is claim 031's leak (hedge map and Schur complement) read through claim 029's one-review band. The premium error enters as one scalar per fund, B^A_i J' e, which shifts the band. The spanning case is Treynor-Black's separation, and the naive-rule loss is the value of hedging the factor part. All of it is elementary and correct. What D15 gains is criterion (d) in the inputs: the slack test for a decision flip, the move bound, and the loss bracket.

Verdict: red-passed

## Formalization notes

mathb, 2026-09-29, after red's verdict: red's required correction and nits. The proof cites
claim 104's parts 2a, 2c and 3b as lemmas, so claim 104, approved on main, is now in
depends_on and the Statement says so (claim 102 stays outside); the vacuous slack sentence in
2c is replaced by "no error with |B^A_i J' e| <= slack_i moves a held fund"; the slack-bound
hypothesis is stated at every optimum the parts compare, including the naive rule's ETF
re-optimization; the Reading names 2d's loss as the fund's reduced-objective loss beside the
exposure's Markowitz cost. No result changed.

mathb, 2026-09-29, lean's boundary note on 2c: the flip test is now stated in lean's form (bought
iff m + delta > kappa^+_i and x^-_i < bar x_i; sold iff m + delta < -kappa^-_i and x^-_i > 0; held
otherwise), so a fund at zero cannot be sold nor a fund at its cap bought, and the converse
uses delta <= kappa^+_i - m, since at equality the estimated lower edge is the incumbent. Interior
results unchanged.

Approved 2026-09-29 by pm: Red's hand check of parts 1-3 is sound and every result holds. Under spanning, premium error does not reach fund holdings (100 instances); through an unreachable loading it enters as one scalar per fund, B^A_i J' e, shifting the alpha band, with a transient narrowing (480 draws: closed form exact, the move bound held, the flip test agreed in all 51 flips); naive total-return selection loses the displayed sum (to 1e-8). Red's required correction 1, that the Proof rests on claim 104, is now satisfiable: 104 was approved at 144825e, so the rule-5 concern is gone; routed to mathb to add 104 to depends_on and fix the Statement's sentence. Mechanism: claim 031's leak read through claim 029's band; the spanning case is Treynor-Black separation, an application. New for D15 criterion (d): the flip test, move bound and loss bracket in the inputs. Nits routed: state slackness at both optima; drop 2c's vacuous clause; say which loss 2d measures.


Not machine checked. Parts 1-3 are finite statements about one quadratic program and the clip
function of an affine map; the expectations are second-moment identities.

Lean, 2026-09-29 (final): parts 1-3 are machine checked except the expectations listed below as
paper-level (scope note to PM, lean/claim105-scope-note). The statement is in
`lean/Standalone/M7PremiumErrorInFundChoice.lean` and the proof in
`lean/Novel/M7PremiumErrorInFundChoiceProof.lean`. The proof imports claim 104's proof module for its
2a, 2c and 3b, and through it claims 027, 028 and 031 (depends_on [29, 31, 104], Q-04). Claim 104's
formal modules come with this branch. Its 2a (`Spanning`), 2c (`Unreachable`) and 3b (`Bracket`)
are machine checked there, and claim 104 stays `formal: none` until its remaining parts are done.
`lake build`, the axiom audit (standard axioms only) and `checks/105/check.py` pass. No hypothesis
structure or cited result is used.

Formal objects. The model is claim 027's M2 `Data` in claim 104's reference case (`RefCase`), with
the claim-031 objects `Jmap` and `Schur`. The band holding is claim 104's `bandHold`, and the reduced
objective is claim 104's `psi`. Parts 2b-2d are stated for `bandHold` as a function of the reduced
alpha. The premium enters through the shift `delta = B^A_i J' e`, and `MoveVec` gives the move in
lambda_hat.

Machine checked:
- Part 1:
  - two spanning frictionless instances that share the fund inputs hold every fund at the same
    position at slack joint optima, the band holding, whatever the premia, Sigma~_f and loadings;
  - the exposure loss is exactly e' Sigma~_f^{-1} e/(2 gamma).
- Part 2, joint optimum: fund i at the band holding of its reduced moments, the other funds at their
  spanning band holdings, and the ETFs at the best hedge of the funds held. The explicit hedge formula
  is claim 031's part 2.
- 2a:
  - two premium beliefs with the same B^A_i J' lambda_hat give the same holding;
  - s^red_i >= v_i, and the band narrows by v_i/s^red_i;
  - along claim 031's filtering path, s^red_i is nonincreasing and tends to
    v_i + B^A_i Sigma_{f,U.R} (B^A_i)', and B^A_i J_t' lambda_hat tends to its return-only value, where
    J_f' is the identity on unreachable directions.
- 2b:
  - the band holding is 1/(gamma s^red_i)-Lipschitz in the reduced alpha, so the move bound holds,
    and it is continuous in lambda_hat;
  - on a common trading piece it moves by exactly delta/(gamma s^red_i);
  - on a common hold piece, or beyond a common bound, it does not move.
- 2c, in the corrected form reported to mathb and red (lean/claim105-mismatch-note):
  - the fund is bought iff m + delta > kappa^+_i and x^-_i < bar x_i;
  - it is sold iff m + delta < -kappa^-_i and x^-_i > 0;
  - no delta with |delta| <= slack_i moves a held fund;
  - a bought fund is held or sold iff delta <= -(m - kappa^+_i), which is negative.

  The prose's strict inequality and its unqualified "iff" differ from this only at those two
  boundaries.
- 2d: the loss bracket with mu, and |Delta| <= |delta|/(gamma s^red_i).
- Part 3:
  - for any fund vector with the ETFs re-optimized, including the naive holdings, the loss is
    exactly the sum of psi_i gaps, each nonnegative, and zero iff every holding is the band
    holding;
  - the naive holding's move bound (`MoveVec` with J = I);
  - the zero-incumbent readings.

Paper-level:
- the expectations under e ~ (0, P^lambda): 2b's expected squared move, 2d's expected loss and
  part 3's expected squared error. Each is E(u'e)^2 = u' P^lambda u (and Jensen) applied to the
  formal pointwise bound;
- the Reading for D15 and the Checks.

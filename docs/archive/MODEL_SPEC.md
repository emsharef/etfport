# Model specification

One `## M<n>` section per version. A version is frozen once any claim or experiment names it; changes
make a new version with a one-line "Changes from M<n-1>" note. CI checks every `model_version` against
the headings here. Owned by math; red and PM read every new version before it is used.

Every version states, explicitly: instruments (m, n, K), return model, belief/information structure,
holdings and funding, action classes, costs, objective, and which proposal section 2 commitments it
relaxes or strengthens (none may be dropped silently).

## M0  Shared language (proposal section 3), 2026-09-27

Not a working model: the notation every later version specializes. Results may not claim M0 as their
setting except for notation-level identities.

- Instruments: m active funds, n ETFs, K economic factors; reviews at quarterly dates t = 0, 1, ..., T.
- Returns over (t, t+1]: `r^A = B^A f + alpha + eps^A`, `r^E = B^E f - c^E + eps^E`; loadings have
  instruments in rows, factors in columns. Conditional on the latent state theta_t: `E f = lambda_t`,
  residuals mean zero. Alpha is relative to an explicit economic factor model, net of internal fund
  costs; c^E is ETF fee and tracking drag.
- Beliefs: filtration I_t; a joint belief about theta_t including (lambda_t, alpha_t). Fund returns are
  public whether or not held.
- Holdings: dollar positions x, cash h, trades u; `x+ = x- + u`, `h+ = h- - 1'u - C_t(u)`, `x+, h+ >= 0`.
- Actions: no trade; ETF-only (active units, or pre-trade-normalized active dollars, fixed); full trading.
- Exposure: `b(a, p) = (B^A)' a + (B^E)' p` for positions normalized by pre-trade wealth.
- One-quarter score (surrogate, formulation 2): `Q_t(w; theta) = b(w)' lambda + a' alpha - p' c^E
  - (gamma/2) w' Sigma(theta) w - C_t(w - w-)`, with normalization, cash return and cost timing fixed by
  each working version.
- Commitments: proposal section 2, all in force.

## M1  One-quarter funded adjustment with fixed unknown means, 2026-09-27

Changes from M0: a working specialization with one active fund, one or two ETFs, two economic
factors, finite return scenarios, proportional shareholder costs and a single quarterly decision.
This section defines assumptions and decision objects; it establishes no claim or economic magnitude.
Red and PM must read this version before a claim or experiment uses it.

### Instruments, timing and information

- Set `m = 1`, `n in {1, 2}`, `K = 2`, `T = 1`. Trade once at review `t = 0`, then hold fund
  units and cash through `t = 1`, one quarter later. Terminal holdings are marked to value without
  compulsory liquidation or a second trading cost. There is no interim investor trading.
- All monetary values and gross returns are expressed relative to the cash account, whose gross
  return in these units is one. Excess returns below are gross returns in cash units minus one.
  The score is thus in cash-account units, not nominal dollars at different dates.
- Known loadings are `B^A in R^(1 x 2)` and `B^E in R^(n x 2)`. The factors are specified economic
  attribution factors; they need not be admissible securities. Known quarterly ETF drag is
  `c^E in R^n`, with `c^E_j >= 0`.
- The fixed unknown parameter is `theta = (lambda_1, lambda_2, alpha)` in a specified nonempty
  finite set `Theta`. At the decision cutoff the investor has a given joint belief `pi` on `Theta`,
  with nonnegative masses summing to one. Its support may be a singleton (known means) or may
  allow uncertainty about either or both means and dependence between them. There is no sign
  restriction on alpha or factor premia. This is a modelling belief, not a confidence region.
- `I_0` contains public information available before orders are submitted, the initial holdings,
  the instrument menu, loadings, cost schedule, mandate, return-scenario specification and `pi`.
  A feasible implemented action is chosen using only `I_0`. Neither the true unknown theta nor
  the next scenario is an available signal. Parameters chosen by an analyst for an illustration
  must be labelled assumed. A true-parameter optimization is an oracle comparison only.
- The menu and mandate are fixed before the future outcome, with no positive-alpha eligibility
  screen. Fund returns are publicly observed at `t = 1` whether or not held. Ownership changes
  neither the information received nor its law. A historical likelihood, an estimation method,
  repeated-sampling coverage and later belief updates are not specified by M1.

### Return scenarios and the three uncertainties

Fix a nonempty finite scenario set `S` and probabilities `q_s >= 0`, `sum_s q_s = 1`, independent
of theta and of the action. Each scenario specifies a factor shock `z^f_s in R^2`, an active
residual `z^A_s in R`, and ETF residuals `z^E_s in R^n`. Each shock has q-weighted mean zero.
There is no independence assumption among their coordinates. For every theta and scenario set

```
f_s(theta)   = lambda + z^f_s,
r^A_s(theta) = B^A f_s(theta) + alpha + z^A_s,
r^E_s(theta) = B^E f_s(theta) - c^E + z^E_s.
```

Assume `1 + r^A_s(theta) > 0` and `1 + r^E_{j,s}(theta) > 0` for every theta in Theta, s in S
and ETF j. This is a restriction on the chosen finite data, not a claim for arbitrary loadings
or means. It excludes a Gaussian return law used as an exact globally positive NAV model.

Let `r_s = (r^A_s, r^E_s)` and define the conditional mean vector and return covariance by

```
mu(theta) = (B^A lambda + alpha, B^E lambda - c^E),
xi_s     = (B^A z^f_s + z^A_s, B^E z^f_s + z^E_s),
Sigma    = sum_s q_s xi_s xi_s'.
```

Sigma is known, constant in theta and may be singular; it describes return risk conditional on
theta. The belief pi describes estimation uncertainty about conditional means. M1 imposes no
ambiguity-aversion penalty and makes no frequentist coverage assertion for pi. If later claims
introduce estimates or an uncertainty set, they must define those objects and their role explicitly.

Active NAV returns already include internal expenses and manager trading effects: alpha and the
residual specification are net of those effects. The ETF return specification subtracts c^E once.
Neither internal active costs nor ETF drag is added again to shareholder switching costs.

### Holdings, funding, mandates and costs

Take strictly positive pre-trade wealth `W^- = h^- + sum_i x^-_i`, with `x^-_i, h^- >= 0`.
For i indexing the active fund first and then ETFs, define

```
w^- = x^- / W^- = (a^-, p^-),    k^- = h^- / W^-,
v   = u / W^-,                  w = x^+ / W^- = w^- + v = (a, p).
```

Thus `sum_i w^-_i + k^- = 1`. These are dollars normalized by pre-trade wealth, not weights
renormalized after payment of costs. At this one review, fixing a fixes active units.

Fix known symmetric proportional cost rates `0 <= kappa_i < 1`. In dollar and normalized units,

```
C_0(u) = sum_i kappa_i |u_i|,
tau(v) = C_0(W^- v) / W^- = sum_i kappa_i |v_i|,
k(w)   = k^- - sum_i v_i - tau(v).
```

Costs are paid from cash at the review, before next-quarter returns. C_0 contains only investor
switching costs. Equal rates, all-zero rates, active rates below ETF rates and the reverse are
all allowed; a mutual-fund cost disadvantage is not assumed. Fixed fees, trade minima, nonlinear
impact, taxes, flows and settlement delays are absent. Execution and settlement occur at the
review's quoted values with immediate use of sale proceeds; this is an explicit idealization.

Optional position limits are specified by a vector `bar w in [0, 1]^(1+n)`, with
`w^-_i <= bar w_i`. Taking all limits equal to one removes any additional position restriction.
Limits are fractions of pre-trade wealth, not post-cost wealth. No other mandate or eligibility
restriction is imposed. Define the full action class, the ETF-only class and no trade by

```
F = {w : 0 <= w_i <= bar w_i for every i, k(w) >= 0},
E = {w in F : a = a^-},
N = {w^-}.
```

Cash is held as `h^+ = W^- k(w)`, so borrowing and short positions are prohibited. The initial
portfolio satisfies the mandate by assumption; a mandate forcing an active trade is outside M1.
For each feasible w and realized scenario the terminal marked wealth is defined by

```
W_1(w; theta, s) = W^- [k(w) + sum_i w_i (1 + r_{i,s}(theta))].
```

### Exposure and feasible substitution

Use `b(w) = (B^A)' a + (B^E)' p`. Define the ETF-only feasible exposure set and its changes from
the initial exposure by

```
B_E = {b(w) : w in E},
D_E = {b(w) - b(w^-) : w in E},
L_E = {(B^E)' d : d in R^n}.
```

L_E is the ETF linear span; its defining coefficients impose no funding or sign constraints.
For a candidate full action w, its exposure change is missing from the ETF span if
`b(w) - b(w^-)` is outside L_E. Matching its exposure by an ETF-only action means finding
`v in E` with `b(v) = b(w)`. A change in L_E need not admit such a v: long-only funding,
costs and the explicit position limits remain part of E. Claims must identify which constraint
prevents a proposed match. Exposure matching alone does not assert equality of alpha, ETF drag,
residual risk, switching costs, terminal wealth or the score. Exact return replication needs
additional restrictions, to be stated in a separate claim.

### Objective

Fix a known risk coefficient `gamma >= 0`. The one-quarter conditional score is defined as

```
Q_0(w; theta) = b(w)' lambda + a alpha - p' c^E
               - (gamma / 2) w' Sigma w - tau(w - w^-).
```

It measures normalized conditional expected gain net of switching costs, with a penalty for
conditional return variance. The wealth-accounting and moment identities connecting this formula
to W_1 are foundation proof obligations, not established results in this specification. Paying
tau through cash and expressing the same payment in expected gain is one payment; no second
switching-cost deduction is made from W_1.

The implementable M1 decision criterion is the belief average
`Qbar_0(w) = sum_{theta in Theta} pi_theta Q_0(w; theta)`, optimized over F or E as appropriate.
No trade evaluates it at w^-. This criterion averages conditional scores; it is not a score using
the full predictive variance. In particular it adds no variance penalty for the variation of
mu(theta) across the belief. That choice is deliberate, and cannot support a claim that M1
estimation uncertainty necessarily increases passive allocation. No terminal-utility or
multiperiod optimality assertion is made. Attainment and any strict advantage of F over E are
proof obligations for separate claims, not assumptions concealed in the word "optimized".

Required scope limitation, to be proved in the first M1 foundation claim: with the feasible
classes and all other decision inputs fixed, two beliefs having the same mean of (lambda, alpha)
give the same Qbar_0 at every feasible action. Consequently they have the same action rankings
and the same maximizing action sets whenever maxima are attained. The reason to be proved is
that Q_0 is affine in (lambda, alpha) and Sigma is constant in theta. This is a proof obligation,
not yet an independently reviewed result. M1 must not attribute a decision effect to belief
dispersion or to dependence between alpha and factor-premium beliefs while their means are
held fixed. An implementation's arbitrary choice among tied maximizers is not such an effect.
A decision effect of these uncertainty features needs a later model version defining a
predictive-variance score, a robust set or a certificate separately. The paired mean-error
identity remains a distinct foundation target about estimation error, not an uncertainty
effect on this decision criterion.

### Commitments and limits

All proposal section 2 commitments remain in force: quarterly investor decisions; distinct alpha
and factor premia; potentially different factor footprints with replication only a benchmark;
funded long-only positions; public returns independent of ownership; separation of internal and
shareholder costs; and no imposed ranking of active and ETF switching costs. Managers may trade
within the quarter; this is already reflected in their net fund returns.

M1 strengthens the general application to known fixed loadings, fixed unknown means with finite
belief support, a known finite shock law with strictly positive fund gross returns, constant
conditional covariance, one quarter, a fixed eligible menu and initially satisfied position limits.
It idealizes settlement and uses cash-account units. It does not model continuation value,
estimated exposures, dynamic learning, realistic calibration, statistical certification or a
two-stage procedure. No empirical claim, novelty claim or result borrowed from the literature
is asserted here. The next D1 stage is the self-financing and action-class foundation claims,
followed by geometry, paired mean error and worked substitution examples after model review.

## M2  One-quarter adjustment with separate purchase and sale rates, 2026-09-27

Changes from M1: replace symmetric proportional shareholder costs by separate purchase and sale
rates, with an explicit charged amount; allow known ETF drag c^E of either sign. All other M1
definitions apply subject to these replacements, including the belief-scope limitation. Experiment
001 retains model_version M1. M2 remains a one-quarter model, not the two-date version D2 needs.
Red and PM must read this version before a new claim or experiment uses it. The earlier M2
restriction-inventory draft was revised before any claim or experiment named M2, implementing
PM's cost-version decision of 2026-09-27.

### Instruments, returns, information and funding

The following inventory states the inherited objects and the changes explicitly.

- Instruments and timing: m = 1, n in {1, 2}, K = 2, T = 1; one investor trade at the quarterly
  review, followed by holding fund units and cash to terminal marking without forced liquidation.
  Monetary values and gross returns are in cash-account units. Cash has gross return one.
- Return model: known fixed B^A and B^E; fixed unknown theta = (lambda_1, lambda_2, alpha) in
  finite Theta; the finite scenario law (S, q) and the joint zero-mean shocks are exactly those
  of M1. Thus f_s = lambda + z^f_s, r^A_s = B^A f_s + alpha + z^A_s and
  r^E_s = B^E f_s - c^E + z^E_s. Here c^E is a known finite vector in R^n, with no sign
  restriction: a negative component contributes positively through the same subtraction.
  All instrument gross returns are strictly positive for every
  allowed theta and scenario. Sigma is the known, theta-independent covariance defined in M1.
- Information and belief: the given joint pi on Theta and the public decision information I_0
  have the M1 definitions. The eligible menu is fixed before future outcomes. Returns are public
  whether or not held; an implemented action has no access to the true theta or future scenario.
- Holdings and funding: W^- > 0 and w = (a, p) are normalized by pre-trade wealth. The initial
  portfolio is nonnegative and satisfies the known limits bar w. Cash is k(w) W^-, where
  k(w) = k^- - sum_i (w_i - w^-_i) - tau(w - w^-). No borrowing or shorting is allowed.
- Costs: the directional proportional C_0 and tau are defined below. These definitions replace
  M1's symmetric cost formula everywhere in funding, feasible sets, wealth and the score.
- Action classes: F = {w : 0 <= w_i <= bar w_i, k(w) >= 0},
  E = {w in F : a = a^-}, and N = {w^-}. All classes use the identical funded budget.
  The formulas for b(w), B_E, D_E and L_E are inherited, with E evaluated using M2's cash
  constraint. The resulting feasible sets need not coincide with those of an M1 instance.
- Objective: Q_0(w; theta) = b(w)' lambda + a alpha - p' c^E
  - (gamma/2) w' Sigma w - tau(w - w^-), with gamma >= 0; the implemented criterion is
  Qbar_0(w) = sum_theta pi_theta Q_0(w; theta). Terminal marked wealth W_1 has the M1 definition.
  This is a belief average of conditional one-quarter scores, not a predictive-variance score
  or a multiperiod objective. Return risk, estimation uncertainty and ambiguity aversion remain
  distinct; no ambiguity-aversion penalty is introduced.

### Directional proportional switching costs and charged amounts

For every instrument i, fix rates `kappa^+_i, kappa^-_i in [0, 1)` known at the decision cutoff.
The superscripts label purchase and sale rates, respectively. Define the nonnegative parts of a
real trade by `u_i^+ = max(u_i, 0)` and `u_i^- = max(-u_i, 0)`, and likewise for normalized
trades v = u / W^-. The plus/minus superscripts on u and v in this paragraph denote parts of
a signed trade, not holdings before and after the review. Define

```
C_0(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-],
tau(v) = sum_i [kappa^+_i v_i^+ + kappa^-_i v_i^-].
```

The charged amount is the change in instrument holdings valued at the review's quoted value,
before shareholder fees. On a purchase, u_i^+ is the value of holdings delivered, and the cash
outlay for that instrument is `(1 + kappa^+_i) u_i^+`. The purchase rate is not a fraction of
total cash tendered. On a sale, u_i^- is the gross value removed from holdings, and the cash
received is `(1 - kappa^-_i) u_i^-`. The sale rate is not a fraction of net cash received.
All amounts are in the cash-account units used throughout M2. Only the net trade per instrument
is modelled; simultaneous offsetting purchases and sales are not separate controls.

As in M1, costs are paid at the review from available cash and sale proceeds, with no borrowing:
`x^+ = x^- + u`, `h^+ = h^- - sum_i u_i - C_0(u)`, and `h^+ = W^- k(w)`.
The relation between the dollar and normalized cost expressions, like the resulting wealth
identity, is a foundation proof obligation. All action classes use these same cost and funding
equations. No terminal liquidation fee is charged.

Rates may be equal between purchase and sale, equal across instruments, asymmetric, or all zero.
There is no prescribed ranking between active-fund and ETF rates. Primary reference cases use
zero, equal and ETF-costlier rates; an active-fund-higher sensitivity is explicitly hypothetical.
These cost inputs are assumed unless separately documented as observed. Internal active-fund
expenses and trading effects already enter net NAV returns; ETF drag enters r^E once. Neither
is added to C_0. Mean inputs derived from net fund returns must not have internal costs or c^E
deducted a second time.

This specification does not implement a load schedule, a breakpoint or waiver rule, a deferred
sales-charge rule, or a redemption window. An exogenous purchase or sale rate is only the cost
function just defined; it must not be labelled a representation of an actual load or redemption
schedule without specifying its charged amount and eligibility conditions in a later model.
Fixed platform fees also remain excluded; replacing one by a proportional rate at one trade
size does not cover other trade sizes. Changes in fee eligibility, lot selection, holding ages,
minimum trades and nonlinear impact are not modelled.

### Complete restriction inventory and outstanding proof obligations

All proposal section 2 commitments remain in force. Relative to the broader application, M2
restricts the model to m = 1, n in {1, 2}, K = 2, known fixed loadings, fixed unknown means
with finite belief support, a known finite centered shock law (S, q, z) independent of theta
and of the action (not merely a constant covariance), strictly positive fund gross returns,
constant conditional covariance, one quarter, a fixed eligible menu, initially satisfied
pre-trade-normalized position limits,
known nonnegative purchase and sale rates below one with linear charges on each trade direction,
and a known fixed, possibly signed ETF fee-and-tracking term with zero ETF manager alpha.
There is no mandate beyond the position limits; the initial portfolio is compliant, so a
mandate forcing an active trade is outside M2. The absence of investor flows and taxes,
cash-account units, and immediate execution/settlement using sale proceeds are also restrictions.
Fixed fees, load schedules,
redemption windows and the other exclusions in the cost paragraph remain outside the model.
No borrowing, no shorting and public returns independent of ownership preserve the corresponding
proposal section 2 commitments. Managers may trade within their funds during the quarter.

The foundation claims still must prove the wealth-accounting, conditional-moment, action-class,
attainment and belief-mean identities; red's review is not a substitute for those claim files.
In particular, the equality of scores and maximizing sets for beliefs with identical means
remains a proof obligation, and no decision effect may be attributed to dispersion or dependence
at fixed means. A belief mean need not be an element of Theta: any evaluation there uses the
affine score formula and must not silently assume membership of the finite support.

Later exposure examples must distinguish a direction outside the ETF linear span from a match
prevented by funding, costs or nonnegative positions. Full-rank ETF loadings in two factors
leave no missing linear direction; a lack of a feasible match must identify the actual constraint.
Any marginal optimization claim must include the cash-budget restriction, as well as position
constraints, rather than interpret an unfunded marginal value as a feasible trading incentive.
A one-quarter score advantage includes the review cost and no terminal exit cost; it must not
be reported as a holding-period advantage. None of these required interpretations establishes
an optimization result, economic magnitude, source-based novelty claim or transfer of an
experiment or claim between versions.

## M3  Two quarterly reviews with public learning and terminal utility, 2026-09-27

Proposed D2 stage-2 working model, following reviewed claim 009. M0-M2 are unchanged.
This version keeps M2's instruments, factor attribution, positive finite return laws,
directional shareholder costs and signed ETF drag, but changes the horizon and objective.
An M2 optimality or band result does not transfer to M3 without a new proof. No claim of
dynamic attainment, concavity of the continuation value, a sufficient belief state, a band
or a continuation effect is assumed by this definition; the finite proof obligations are
listed below. The first-review accounting and feasible-set identifications are stated separately.

### Timing, returns and public information

There is one active fund, n in {1,2} ETFs, two economic factors, reviews at t=0 and t=1,
and terminal marking at t=2. Each interval is one quarter. There is no investor trade
between reviews and no forced terminal liquidation. Cash has gross return one in cash-account
units. The eligible menu, known loadings B^A and B^E, and signed ETF drag c^E are fixed for
both quarters, without an alpha eligibility screen. Factor series are attribution variables,
not additional tradable securities.

The latent parameter theta=(lambda_1,lambda_2,alpha) lies in a specified finite nonempty
Theta and is fixed for both quarters, initially unknown with given prior pi_0. Alpha and
factor premia remain distinct relative to the economic factor model. This initial version
introduces learning but not changing latent means or unequal persistence. A different
persistence mechanism would require a later version and separate motivation.

A finite nonempty scenario set S has masses q_s>=0 summing to one. Each s gives centered
shocks (z^f_s,z^A_s,z^E_s), as in M2, with arbitrary contemporaneous dependence. Conditional
on theta, the two quarterly scenario draws are independent with this same law q. The law
is independent of theta and ownership; unconditional returns across quarters can be dependent
through theta. In either quarter define

```
f(theta,s)=lambda+z^f_s,
r_A(theta,s)=B^A f(theta,s)+alpha+z^A_s,
r_E(theta,s)=B^E f(theta,s)-c^E+z^E_s.
```

Every instrument gross return 1+r_i(theta,s) is strictly positive for every specified theta,s,
including zero-mass entries. Internal fund expenses and internal trading effects are already
in net fund returns. Signed c^E enters the ETF return exactly once, and no internal expense
is added to shareholder switching costs.

The initial information I_0 consists of the prior, menu, return law, loadings, initial holdings,
preferences and known cost rates. At review 1, before the order cutoff, the full first-quarter
factor realization and all instrument total returns are public, including unheld funds:
`Y_1=(f(theta,s_0),r_A(theta,s_0),r_E(theta,s_0))`. This is an explicit idealization of timely
public factor and fund data, not an assertion about a data vendor's publication schedule.
The investor knows its previous action and marked holdings too. There is no observation of
theta itself or of the second-quarter draw. Orders execute after this information cutoff at
the review quotes, with immediate settlement. Exact finite observations may fully reveal
some parameters in special instances; perfect revelation is not imposed generally.

Let Y be the finite set of possible public observations. Define the likelihood, observation
probability and posterior for P_0(y)>0 by finite sums:

```
L_theta(y)=sum_{s: (f,r_A,r_E)(theta,s)=y} q_s,
P_0(y)=sum_theta pi_0(theta)L_theta(y),
pi_1(theta|y)=pi_0(theta)L_theta(y)/P_0(y).
```

For P_0(y)=0 set pi_1(.|y)=pi_0 as a bookkeeping convention; those nodes never contribute
to expected utility. The likelihood and posterior do not depend on holdings or trades.
A policy at review 1 may depend on y and its current marked portfolio, but it must choose
the same action for hidden histories with the same observable information and portfolio.
In particular it cannot choose separately for two (theta,s_0) pairs generating the same y.

### Exact dollar funding and the action comparison

Let x_t^- be risky dollar holdings and h_t^- cash before review t, with
W_t^-=h_t^-+sum_i x_t,i^-. Initially these are nonnegative and W_0^->0. A dollar trade u_t
at that review gives

```
C(u_t)=sum_i [kappa^+_i max(u_t,i,0)+kappa^-_i max(-u_t,i,0)],
x_t^+=x_t^-+u_t,
h_t^+=h_t^- - sum_i u_t,i - C(u_t).
```

Every purchase and sale rate is a fixed known number in [0,1), constant over both reviews.
The charged amount is the gross dollar change in delivered or removed holdings at that
review's quote, exactly as in M2; sale proceeds can fund simultaneous purchases. There is
no ranking of active and ETF rates. Zero rates, equal rates and either direction of cost
disadvantage are admissible. Fees are paid from cash once, not subtracted again from utility.

The funded full class F_t(x_t^-,h_t^-) imposes x_t^+>=0 and h_t^+>=0. The ETF-only class
E_t additionally fixes u_t,A=0, and N_t={0}. Fixing active dollar holdings at the review
fixes its units at the quoted price; weights after costs are not the control. All classes
use the same marked state and funding equations. There are no additional concentration caps
in M3: this is M2's all-limits-one benchmark at each review. Return drift therefore cannot
force an active trade to restore a concentration cap. Borrowing and shorting remain prohibited.
A later concentration-cap extension must address states at which the incumbent violates a cap
and E_t could be empty; it is not silently included here.

With no interim trades, the next review's marked state is

```
x_1,i^-=x_0,i^+ (1+r_i(theta,s_0)),    h_1^-=h_0^+.
```

After the second review, terminal wealth is

```
W_2=h_1^+ + sum_i x_1,i^+ (1+r_i(theta,s_1)).
```

Dollar units are preserved across dates. If a later claim normalizes at review t, it must
use that node's own W_t^- and explicitly rescale both trades and costs; it cannot carry
review-0 normalized holdings unchanged through realized returns. The full vector x_1^-,
not just wealth or factor exposure, matters for the next review's switching costs.
Normalizing terminal wealth by a positive W_1^- also changes the utility coefficient:
`rho_1=rho W_1^-/W_0^-`, since `rho W_2/W_0^-=rho_1 W_2/W_1^-`.
Keeping rho fixed while switching that denominator would change preferences. Thus even
at a fixed posterior a review-1 result in normalized holdings cannot carry over M2's
fixed-gamma picture; dollar holdings and normalized holdings must be distinguished.

The root comparison restricts only the review-0 action to F_0, E_0 or N_0. In all three
classes, review-1 controls are full trading F_1 after the same public observations. Thus
ETF-only at review 0 does not mean a ban on future active trading, and root no trade is
not a two-quarter buy-and-hold policy. The matched continuation controls defined below
also restrict review 1 to E_1 or N_1. Within each such comparison the same continuation
class is available to all three root classes; no class receives a different future menu.

### Objective and candidate continuation representation

Fix rho>0 and maximize expected terminal utility
`E[U_rho(W_2/W_0^-)]`, where `U_rho(z)=-exp(-rho*z)`.
The denominator is fixed initial wealth, not random future wealth. This is an increasing,
concave exponential utility of terminal wealth; rho is not M2's conditional-score gamma.
It is a modelling choice allowed by proposal section 3.3, not an empirical preference estimate.
There is no running reward, utility charge for C, sum of quarterly mean-variance scores,
terminal mean-variance precommitment objective, discount penalty or ambiguity-aversion term.

For a root trade and a feasible observable review-1 policy, the objective is the explicit sum

```
sum_{theta,s_0,s_1} pi_0(theta) q_{s_0} q_{s_1}
  U_rho(W_2(theta,s_0,s_1;policy)/W_0^-).
```

Conditional realized-return risk is the scenario law q; uncertainty about fixed means is
pi_0 and its posterior. Bayesian integration of terminal utility uses the joint predictive
law; it is not a mechanical addition of a return variance and a mean-error penalty. Public
signals are available under every policy, so no ownership-created information value enters.

For a pre-review-1 state (x,h) and posterior pi, define

```
V_1(x,h,pi)=sup_{u in F_1(x,h)} sum_{theta,s} pi(theta) q_s
  U_rho([h-1'u-C(u)+sum_i (x_i+u_i)(1+r_i(theta,s))]/W_0^-).
```

For a feasible root action u_0 let (x_1^-(y;u_0),h_1^-(u_0)) be its marked state at y.
Define its candidate continuation score

```
H_0(u_0)=sum_{y: P_0(y)>0} P_0(y)
  V_1(x_1^-(y;u_0),h_1^-(u_0),pi_1(.|y)).
```

The root class value is defined directly as the supremum of the explicit terminal-utility
sum over feasible policies with u_0 in that class. Equality to sup H_0 is a finite dynamic-
programming proof obligation, not an assumed result hidden in the notation. A sufficient
belief state, attainment and differentiability of V_1 are likewise not assumed.

For attribution, three matched continuation controls are required. Let D in {F,E,N}
label the root class D_0 and let R in {F,E,N} label the review-1 class R_1 at every public
observation. The symbol R here is a class label, not a return or the dollar cost C.

- R=F allows funded full trading at review 1, as in V_1 above.
- R=E allows funded ETF-only trading at review 1: u_1,A=0 fixes the marked active
  holdings at that node, not the original root active holding.
- R=N disables review-1 trading: u_1=0.

All nine root/continuation combinations retain identical initial holdings, beliefs, public
observations, two-quarter return law, utility, cost rates and funding equations. Define
`V_{D,R}` as the supremum of the explicit policy terminal-utility sum with root class D_0
and continuation class R_1. Define `V_1^R` by replacing F_1 with R_1 in the displayed
V_1 supremum, and `H_0^R` by using V_1^R in the observation sum. In particular V_1^F=V_1
and H_0^F=H_0. Equality `V_{D,R}=sup_{u_0 in D_0} H_0^R(u_0)` remains a proof obligation
for each control, not an additional assumption.

The primary continuation-effect object uses certainty equivalents in units of initial
wealth. For each of the nine controls define

```
CE_{D,R}=-(1/rho) ln(-V_{D,R}),
Delta_R=CE_{F,R}-CE_{E,R}=-(1/rho) ln(V_{F,R}/V_{E,R}).
```

These logarithms are well-defined without assuming attainment. Zero trades give a policy
in every class. Funded nonnegative holdings have nonnegative terminal wealth, bounded
uniformly over policies by W_0^- times the square of the larger of one and the largest
specified gross return: trading only subtracts nonnegative costs, and each holding interval
increases wealth by at most that gross-return bound. Hence every V_{D,R} lies in [-1,0)
and is bounded away from zero. CE is a reporting transformation of the expected-utility
supremum, not a change of optimization objective. It is applied after averaging utility,
not to each outcome before averaging.

Measure the change in the root active-intervention advantage due to future ETF adjustment
by `Delta_E-Delta_N`, and the incremental change due to future active trading by
`Delta_F-Delta_E`. Their sum is `Delta_F-Delta_N`. These are differences in the root
full-minus-ETF-only advantage, not the absolute value of future trading to either root
class. The total full-versus-disabled contrast alone cannot attribute an effect to future
ETF adjustment: the two contributions need not have the same sign. No sign or strict
inequality is imposed here. Multiplication by 10000 reports a certainty-equivalent amount
in basis points of initial wealth; it does not make it an expected-return difference.

The scale is invariant to a common sure terminal-wealth shift within each control. More
precisely, keep rho, W_0^-, feasible policies and information fixed, and add
`delta_R W_0^-` to every terminal payoff under control R, identically for both root classes.
Then `V_{D,R}` is multiplied by `exp(-rho delta_R)`, each `CE_{D,R}` increases by delta_R,
and Delta_R and the two contributions are unchanged, even if delta_R differs across
controls. This is an accounting invariance for terminal payoff shifts, not a statement
about adding initial cash that changes funding opportunities or W_0^-.

The auxiliary utility gap `G_R=V_{F,R}-V_{E,R}` may be used in proofs. For fixed R its
sign and zero set agree with those of Delta_R, because CE is strictly increasing in V.
However, differences of G_R across controls do not share the terminal-shift invariance:
a common sure gain under one control multiplies its G_R and can change the contribution's
sign. Such differences must not be reported as the primary value of ETF adjustment.
None of the three controls by itself separates learning from the other benefits of a
future adjustment, because observations remain available under all controls.

A claim about a root no-active-trade region must instead specify the varied admissible
inputs and whether it asserts existence of an optimum with u_0,A=0 or that every optimum
has this property. A change in Delta_R is not itself a proof of a boundary shift or a change
in the selected active trade. Equating a zero gap with existence of a no-active-trade
optimum requires attainment, which the next claim must establish.

Every comparison is exit-free: there is terminal marking, not liquidation. Sale charges
apply to sales actually made at either review; the N_1 control incurs no review-1 costs.
A result must not silently impose a terminal sale on any control. Finite public observations
can completely reveal theta for some return supports. Any example intended to demonstrate
continued uncertainty after learning must verify a positive-probability observation leaves
at least two positive posterior masses; perfect revelation is not evidence of that property.

### First-review transfer from M2 and its limits

This inventory concerns the all-limits-one M2 specialization accepted for M3; it does not
preserve M2 instances with tighter position limits. PM accepted this restriction when M3
merged (board/NOTICES.md, 2026-09-27). The earlier stage-2 request to keep position limits
unchanged is satisfied only for that specialization, not for general M2 caps. No change to
M0-M2 is made here.

For a root dollar trade, make the following substitution into M2, using the same return
parameters, shocks, prior, loadings, signed drag and directional rates:

```
W^- = W_0^-,   w^- = x_0^-/W_0^-,   k^- = h_0^-/W_0^-,
v = u_0/W_0^-,   w = w^-+v,   bar w_i = 1.
```

Positive initial wealth makes this an invertible affine change between root trades and
post-review normalized holdings. Positive homogeneity of each positive-part term gives
`C(u_0)/W_0^- = tau(v)`. Dividing the dollar cash equation gives
`h_0^+/W_0^- = k^- - sum_i v_i - tau(v) = k(w)`. Consequently
`sum_i w_i + k(w) + tau(v) = 1`. Nonnegative holdings and cash imply each `w_i<=1`,
so the M2 unit caps add no restriction to M3's root funded set. Conversely an M2 feasible
w gives the M3 trade `u_0=W_0^-(w-w^-)` with exactly that cash. The extra restrictions
`u_0,A=0` and `u_0=0` correspond respectively to `a=a^-` and `w=w^-`.

These substitutions identify precisely the following parts of existing results:

- Claim 003's cost, cash and conditional one-quarter gain identities apply to the first
  holding interval, ending just before review 1: `W_1^- = h_0^+ + sum_i x_0,i^+(1+r_i)`.
  In particular `W_1^-/W_0^- - 1 = w'r - tau(v)`, with conditional mean
  `w'mu(theta)-tau(v)` and conditional variance `w'Sigma w`. These identities describe
  marked wealth before the next trade; they are not identities for terminal utility.
- Claim 004's nesting, nonemptiness, convexity and compactness of the three root action
  sets apply through the same affine bijection. The initial normalized holdings satisfy
  the unit caps because they and cash are nonnegative and sum to one. This transfers the
  feasible-set part of the claim, not its optimization of the M2 quadratic score.
- Claim 005's ETF exposure-feasibility test applies to root normalized exposure with
  `bar p_j=1`: substituting `a=a^-` into the cash identity gives the identical ETF outlay
  and directional cash inequalities. Thus its distinction between a missing span direction
  and an infeasible exposure match still applies at review 0. Equal exposure alone does
  not identify the resulting cash, next marked holdings or continuation value.

These are explicit paper-level identifications with existing formalized M2 statements;
the M3 substitution itself is not machine checked; red's definition review checked these
identifications, separately from the continuation-control correction. They
introduce no new economic claim. Claim 003's belief-mean sufficiency and claim 004's score
optimality remain results about an auxiliary one-quarter score if one chooses to calculate
it. M3 instead averages nonlinear terminal utility and permits observation-dependent future
trades. Hence equal belief means do not, by those results, imply equal M3 objectives or
maximizers. Claims 006-008's score comparisons and limiting-case optimality, and claim 009's
band, cannot be used as first-review M3 optimality results. Their proofs do not compare
this terminal criterion or the cost of future trades. A transfer of any such conclusion,
or a continuation-value result, requires a new reviewed M3 claim.

### Restricted example and next proof obligations

A nontrivial assumed finite instance is given in `checks/m3-definition/check.py`: one active
fund with loading (1,1/2), one ETF with loading (1,0), uncertain lambda_1 and alpha, nonzero
factor and residual risks, negative ETF drag, and asymmetric positive switching rates.
Distinct hidden states sometimes generate the same public observation, so observing returns
does not automatically identify both unknown means. The check exercises Bayes probabilities
and funding for explicit policies; it establishes no optimizer or economic magnitude.

The next claim must prove the finite control representation, feasible continuation and
attainment needed for a marginal characterization for each of F_1, E_1 and N_1. A possible
route is a single finite program in the root trade and one trade per public observation:
prove convexity and compactness of its feasible policy set, positivity of marked wealth,
and concavity of its terminal-utility objective, then separate the conditional problems.
Joint concavity of V_1^R in marked risky holdings and cash, and monotonicity in cash, must
be proved before using them to infer concavity of H_0^R. These are proof tasks, not results
established by a numerical solver. Any concavity or supergradient argument
must account for the state-dependent switching-cost center, shared utility value of cash,
nonnegative positions and the complete set of compatible future marginal values. Do not
assume differentiability at trade kinks or combine unrelated coordinatewise supergradients.
A root active no-trade condition must include both immediate funding and continuation value.

A substantive continuation result must then hold current return law, costs, information,
utility and funding fixed while comparing E_1 against N_1 through Delta_E-Delta_N, with F_1
against E_1 reported separately through Delta_F-Delta_E. This identifies the opportunity for
future feasible ETF adjustment separately from future active trading. The total F_1
against N_1 comparison is insufficient for that attribution. No scalar band, monotonicity, strict gain or structural separation of alpha
and factor uncertainty is asserted yet. Claim 009's width does not automatically carry over:
terminal utility is nonlinear and future trades and posteriors enter the root problem.

M3 is deliberately narrower than the broader proposal: finite-support fixed unknown means,
known constant loadings and signed drag, conditionally independent quarterly shocks, no extra
concentration cap, no changing eligibility, taxes, flows, loads, fixed fees, redemption
restrictions, capacity or nonlinear impact. It does not add unequal persistence at this stage.
It retains quarterly investor control, public information independent of ownership, distinct
factor and alpha meanings, exact funded long-only trades, and separate internal/shareholder
cost accounting. M3 is a definition for proposed work, not a novelty or performance result;
D2's registered dynamic and constraint-based prior art remains applicable to later claims.

## M4  Repeated-sampling certification of a one-quarter M2 adjustment, 2026-09-28

Proposed D3 estimation layer. M0-M3 are unchanged. M4 uses M2's funded action classes,
directional shareholder costs and conditional one-quarter score; it replaces M2's
given finite Bayesian belief by a fixed unknown parameter and repeated public histories.
It does not extend M3's terminal-utility problem. PM and red review this definition
before any claim or registered experiment names M4. The probability guarantees and
computational reductions listed below remain proof obligations, not assumptions.

### Fixed economic design and the target parameter

There is one active fund, n in {1,2} ETFs and two economic factors. All of the following
are known and fixed before the history is sampled: the eligible menu, B^A, B^E, signed
c^E, the finite centered joint shock law (S,q,z^f,z^A,z^E), gamma>=0, initial wealth
W^->0, compliant normalized incumbent w^-=(a^-,p^-), and position limits and directional
cost rates from M2. Rates can be zero, equal or ordered either way across instruments.
The risk covariance Sigma is calculated from this same known shock law as in M2;
there is no risk-covariance or loading estimation in this first version.

Instead of a probability distribution on parameters, specify a known finite nonempty
vertex set V_4 in R^3 and the parameter domain Theta_4=conv(V_4). Every vertex and
every specified scenario must give strictly positive gross returns for every fund.
The fixed true parameter theta_*=(lambda_*,alpha_*) belongs to Theta_4 and stays
constant throughout the estimation history and the next holding quarter. It is not
drawn anew from a prior in each replicate. A singleton domain is allowed as a known-
parameter control; inferential examples must say when the domain is nontrivial.

This compact convex domain is an explicit change from M2's finite belief support.
The affine return and score formulas extend to it; positivity throughout its convex
hull is a finite affine-check obligation. There is no Bayesian prior or posterior in
M4's confidence construction. A prior used by a comparison method must be separately
declared and cannot supply the coverage guarantee below.

For normalized post-review holdings w=(a,p), retain exactly

```
b(w)=(B^A)'a+(B^E)'p,
tau(w-w^-)=sum_i [kappa^+_i max(w_i-w^-_i,0)+kappa^-_i max(w^-_i-w_i,0)],
k(w)=k^- - sum_i(w_i-w^-_i)-tau(w-w^-),
F={w: 0<=w_i<=bar w_i, k(w)>=0},
E={w in F: a=a^-},        N={w^-},
Q(w;theta)=b(w)'lambda+a alpha-p'c^E-(gamma/2)w'Sigma w-tau(w-w^-).
```

Both classes face one budget and the same initial wealth, costs, risk input and
parameter. Investor trades occur only at the review, followed by one holding quarter
and terminal marking without forced liquidation. Fees reduce cash once. Internal
expenses are already included in fund returns; ETF drag is subtracted once. This
objective is a conditional one-quarter score, not a multiperiod utility solution.

### Repeated public history and dependence assumptions

Fix a positive integer sample length N_obs, a confidence error level eta in (0,1),
and the review date before inspecting returns. The N_obs completed quarterly records
are all available before the decision cutoff. Each record contains the two factor
returns and the active and every ETF's net total return, in cash-account units:

```
H_N={(f_l,r^A_l,r^E_l): l=1,...,N_obs},
f_l=lambda_*+z^f_{s_l},
r^A_l=B^A f_l+alpha_*+z^A_{s_l},
r^E_l=B^E f_l-c^E+z^E_{s_l}.
```

The subscript N abbreviates N_obs; the standalone action-class label N still means
no trade.

Conditional on the fixed theta_*, s_1,...,s_{N_obs},s_next are independent draws from
q. The next draw occurs after the action and is independent of the history. No
independence is imposed among the factor, active-residual and ETF-residual shocks
within a record. In particular factor-mean and alpha estimation errors need not be
independent. Observations are public regardless of ownership; there are no missing
records, survival filters, changing share classes or ownership-created signals.

Write P_theta for this sampling distribution with theta held fixed. Repeated
sampling means drawing a fresh full history at that same theta and fixed design,
then re-estimating and reselecting the action. It does not mean conditioning on one
realized history or averaging coverage over a favorable prior on theta. The historical
stationarity, known shock law, complete data and fixed design are assumptions for
this benchmark, not claims about observed financial histories.

There is one decision after a fixed sample size. Serial dependence, overlapping
returns, drift, data-dependent stopping, rolling reviews and choosing N_obs, eta,
the menu or the nuisance inputs after looking at the history are outside the stated
coverage experiment. A later extension must supply its own simultaneous coverage
argument. Independent Monte Carlo replicates used to study this fixed experiment
do not justify repeated live testing at multiple dates.

### Estimators and joint error geometry

Use the observable three-vector and its sample mean

```
X_l=(f_l, r^A_l-B^A f_l),
theta_hat_N=(lambda_hat_N,alpha_hat_N)=(1/N_obs) sum_l X_l,
zeta_s=(z^f_s,z^A_s),
Omega=sum_s q_s zeta_s zeta_s'.
```

No second internal-fee subtraction is made in the active residual. ETF returns
remain in the public history, but this estimator does not use their residuals to
improve the mean estimate. It is not claimed to be a sufficient or efficient
statistic for the full finite likelihood. Known B^A is used literally; substituting
estimated exposures would change the sampling law and needs a new specification.

Omega is the 3-by-3 covariance of one factor/active-residual observation. Its
factor-alpha cross block sum_s q_s z^f_s z^A_s is retained. Sigma is instead the
(1+n)-by-(1+n) realized fund-return covariance from M2. The sampling covariance
Omega/N_obs and its implications must be established from the iid history; Omega
is not added to Sigma in Q. Neither the sample covariance nor a diagonal estimate
silently replaces either matrix. theta_hat_N is not projected onto Theta_4:
projection would change the error distribution used below. Its score may be
evaluated by the affine formula outside Theta_4, without claiming an admissible
predictive return law at that estimate.

### Joint confidence set and exact finite calibration

This first benchmark uses the known finite sampling law, not a normal or chi-square
approximation. Let Omega^dagger be the Moore-Penrose inverse of the positive
semidefinite Omega and Im(Omega) its range. For each ordered history of N_obs
positive-mass scenarios, form

```
e_N=(1/N_obs) sum_l zeta_{s_l},
T_N=N_obs e_N' Omega^dagger e_N,
history mass=product_l q_{s_l}.
```

Combine equal values of T_N and order the resulting finite support. Define
t_{N,eta} to be the first support value whose accumulated mass is at least 1-eta.
This is an explicit calibration algorithm on the specified shock law, not an
assumption that a desired coverage event has the desired probability. "Exact"
means exact computation of this discrete quantile, not equality of coverage to
1-eta: an atom can make coverage strictly larger. Ordered-history enumeration can
equivalently group histories by scenario counts: if there are m positive-mass
scenarios and their counts are n_1,...,n_m summing to N_obs, the count vector has
mass N_obs! product_i(q_i^{n_i}/n_i!) and error sum_i n_i zeta_i/N_obs. There are
binomial(N_obs+m-1,m-1) such count vectors, rather than m^{N_obs} ordered histories;
this reduces enumeration but remains combinatorial. Define

```
A_{N,eta}={e in Im(Omega): N_obs e' Omega^dagger e <= t_{N,eta}},
C_N(H_N)=Theta_4 intersect {theta_hat_N-e: e in A_{N,eta}},
Coverage_N(theta_*)={H_N: theta_* in C_N(H_N)}.
```

The range restriction is essential for sharpness, not for coverage validity: a
pseudoinverse quadratic alone ignores errors in zero-variance directions. Removing
the restriction enlarges the error set to a cylinder along the null space; only
intersection with Theta_4 then bounds those directions in the confidence set.
Enlarging the confidence set cannot reduce coverage, but can weaken the certificate.
If Omega=0, its range is {0}, the finite calibration
has t_{N,eta}=0, and the set is either {theta_hat_N} intersect Theta_4 or empty.
Under the specified sampling law theta_hat_N=theta_* almost surely in this case,
so C_N={theta_*} almost surely; the empty alternative concerns other input histories.
The construction keeps cross-covariance even when Omega is singular. The sign
theta_hat_N-e corresponds to the error theta_hat_N-theta_*.

The required frequentist guarantee is

```
for every theta_* in Theta_4,
P_{theta_*}(Coverage_N(theta_*)) >= 1-eta.
```

A claim must prove it, including that positive-mass sampling errors lie in the range
of Omega, the singular cases, and the effect of intersecting Theta_4. Nothing here
uses a Bayesian credible probability. Exact enumeration may be impractical for
large N_obs. Replacing it by a simulated percentile does not retain an exact
guarantee; an approximation requires a certified conservative critical value or
an explicitly budgeted additional statistical error, neither supplied by M4.

### Optimized comparator, candidate selection and certificate direction

The scientific target at a fixed theta is the advantage over the best feasible
ETF-only action at that same theta:

```
Adv(w;theta)=Q(w;theta)-sup_{v in E} Q(v;theta),
G_*(theta)=sup_{w in F} Q(w;theta)-sup_{v in E} Q(v;theta).
```

The oracle ETF action can depend on theta inside this definition; the investor
does not know it. For nonempty C_N, the proposal's strong target is

```
L_N(w)=inf_{theta in C_N(H_N)} [Q(w;theta)-sup_{v in E}Q(v;theta)].
```

The same theta is used in both scores. This is not defined as the difference of
two separately robust optimized class values. Replacing the oracle E class by a
single selected ETF comparator is a weaker target and must be labeled separately.
For any selected v in E, its infimum of Q(w;theta)-Q(v;theta) over C_N is at
least L_N(w). A lower bound on that weaker target is therefore not necessarily a
lower bound on L_N(w). Coverage protects the comparison against that selected v,
but does not transfer its false-certification bound to the oracle-comparator event
defined below.
For empty C_N, certification is disabled and use the operational convention
L_N(w)=-infinity, not inf(empty)=+infinity. An empty set signals inconsistency
with the model/calibration for that history; it never authorizes an active trade.

For fixed w, Q(w;theta) is affine in theta and sup_E Q(v;theta) is convex in
theta, so Adv(w;theta) is concave in theta. Computing L_N minimizes this concave
function over the convex set C_N; it is generally a nonconvex optimization problem.
Equivalently it jointly minimizes Q(w;theta)-Q(v;theta) over theta in C_N and
v in E, including the bilinear term -b(v)'lambda. A local minimization result or
any feasible pair gives an upper bound on L_N, not the lower bound certification
needs. One conservative route is a bounded polytope containing C_N: concavity
puts its minimum at a vertex, so the minimum of validated lower bounds on Adv at
all its vertices is a lower bound on L_N. Each such evaluation must bound the
ETF supremum from above (or compute it exactly). Vertices outside Theta_4 use
only the affine score extension, not an asserted return law there. Other routes
include branch and bound with valid lower bounds or certified outer approximations;
no generic local solver is a certificate. The empty-C_N fallback still applies.

For a baseline candidate rule, define w_hat_F as a global maximizer of Q(w;theta_hat_N)
over F and v_hat_E as one over E, choosing the lexicographically smallest optimizer
in coordinate order (a,p_1,...,p_n) when tied. Both classes are nonempty and compact:
the compliant incumbent belongs to them, and the continuous funding inequality,
closed position constraints and finite bounds make them closed and bounded. Q is
continuous in w, so both maxima are attained. Their optimizer sets are compact;
successively minimizing each coordinate on the remaining compact set supplies
the lexicographic selection. For each fixed theta_* the history law has finite
support, so every selector restricted to that support is measurable under its
discrete sampling law. This does not assert global Borel regularity of an arbitrary
selector across all possible real-valued histories. A computational implementation must specify its
feasible approximate candidates and numerical error instead of pretending to have
exact maximizers. The later coverage implication must hold uniformly over all
feasible data-selected candidates, not only these baseline optimizers.

Fix a nonnegative score threshold delta_econ before seeing data. A certification
routine must produce an actual lower bound ell_N(w)<=L_N(w). If C_N is nonempty,
w_hat_F is feasible, its active holding differs from a^-, and
ell_N(w_hat_F)>delta_econ, implement it. Otherwise implement the feasible ETF-only
fallback v_hat_E. If a numerical solver does not establish the required lower
bound, it returns no certificate. A feasible point of the minimization defining
L_N generally supplies an upper bound on its infimum; it does not authorize the
trade. All objective and feasibility errors must be included in ell_N or the
decision threshold. E is nonempty here because the fixed incumbent is compliant;
forced mandate restoration is outside M4.

The intended false-certification event is an implemented certified active trade
with Adv(w_hat_F;theta_*)<=delta_econ. Bounding its **unconditional**, per-review
probability by eta, uniformly in theta_* and in data-selected candidates, is a
proof obligation. No bound on its conditional probability given certification is
asserted. Fallback is a selected ETF policy, not a promise to attain the unknown
oracle ETF score. A score certificate is not realized-return or wealth dominance.

### D3 proof and experiment obligations; scope and prior-art boundary

The next claims must distinguish three steps: valid coverage from the sampling
model; a uniform coverage-event implication for the data-selected action; and a
computable conservative bound on the optimized-comparator target despite its
concave-minimization structure. Their novelty
cannot consist only of the elementary implication from set coverage. Claim 002's
paired mean-error identity and claim 005's feasible ETF exposure geometry are
starting points, but any transfer from their model versions must be made explicit.
In particular exposure cancellation concerns each candidate/comparator difference,
not a single chosen match substituted for the whole optimized E class.

Check the D3 kill-criterion sources `olivaresnadal2018technical`, `hautsch2017large`,
`garlappi2005portfolio` and `petrik2016safe` before claiming a new penalty or safety
result. A paired notation or the mere use of two classes does not establish a
difference from existing robust-optimization equivalences or robust baseline regret.
Any imported result needs the repository's source and axiom-ledger review. M4
imports none and asserts no novelty or rate. A lower bound must account for the
full public-history likelihood: known finite translated supports can distinguish
some parameters exactly, so covariance alone cannot justify a universal root-N
information lower bound.

A registered experiment must freeze the design, true parameter(s), N_obs, eta,
critical-value method, candidate/ETF selectors, threshold, numerical certificate
method, seeds and replicate count before results. It should report coverage,
false certification, certification frequency, the oracle gap G_*, true candidate
advantage and opportunity cost, with sampling error for estimated probabilities.
Known-parameter full and ETF optima use the same budget and costs. Distinguish
missed positive oracle gaps from absence of any true advantage; do not call
oracle quantities observed in historical data. Future-quarter draws, when used
to assess realized performance, are held out and common across paired policies.
Experiment 006 motivates this layer but does not automatically become an M4
experiment or provide confidence-set coverage under these assumptions.

All proposal section 2 commitments remain visible: quarterly control, distinct
alpha and premia, a fixed unfiltered eligible menu, different fund exposures,
funded long-only actions, public information regardless of ownership, and separate
internal and shareholder cost accounting without a cost ranking. Restrictions
include fixed means and loadings, a known stationary finite shock law and risk
covariance, a fixed compliant incumbent and menu, complete timely histories, and
one fixed-size review. Estimated loadings/covariances, serial dependence, drift,
survivorship, historical selection, taxes, flows, nonlinear fees and repeated-live-
review guarantees require later work. Estimation uncertainty shapes an evidential
gate here; no ambiguity-aversion preference or additional predictive-risk penalty
is introduced into the conditional M2 score.

## M5  Quarterly fund-of-funds rebalancing with Gaussian learning and quadratic costs, 2026-09-28

Proposed D12 working model (PM's D12-open note; ROADMAP D12-D15; the human's charter revision
of 2026-09-28). M0-M4 are unchanged. M5 is the first version at the charter's scale: N active
funds, M ETFs and K economic factors, an open sequence of quarterly reviews, Gaussian beliefs
about alphas and premia updated by a Kalman filter from public returns, quadratic instrument-
specific trading costs, ETF fees, and a quarterly mean-variance objective. It drops the funded
long-only constraint of M1-M4 as a declared counterfactual, which proposal section 2 allows
("borrowing, shorting, or futures may be counterfactuals, not hidden financing assumptions");
D13 (mathb) restores proportional costs and long-only caps around M5's target. No M1-M4 result
transfers to M5 without a new proof: the return law, the cost function and the constraint set
all differ. Everything named below as a target, an obligation or a property to verify is not
an assumption. Red and PM read this version before a claim or experiment names it.

### Instruments, timing and returns

- Instruments: N >= 1 active funds (index set A), M >= 1 ETFs (index set E), n = N + M
  instruments, K >= 1 factors. M0's (m, n) are M5's (N, M); the letter n now counts all
  instruments. Reviews at quarterly dates t = 0, 1, 2, ...; a finite horizon T is a special
  case obtained by stopping the sums below at T - 1. There is no trade between reviews, and no
  forced liquidation.
- Units: dollar positions, in a cash account whose excess return is zero; all returns below are
  excess returns over the riskless rate for the quarter (t, t+1]. Positive gross returns are not
  required (Gaussian returns are unbounded); M1-M4's positive-gross-return restriction is not in
  force.
- Loadings: known fixed B^A (N x K) and B^E (M x K), instruments in rows, factors in columns;
  B = [B^A; B^E] (n x K). ETFs need not span R^K and funds need not be replicable: section 2's
  different-footprints commitment is kept, and exact replication (B^A rows in the row space of
  B^E) is a benchmark case, not the default.
- Latent state: theta_t = (lambda_t, alpha_t) in R^K x R^N, the factor premia and the fund
  alphas for the coming quarter. They are distinct objects (section 2): alpha is net of internal
  fund expenses relative to the explicit factor model, and nothing in M5 conditions eligibility
  on a positive alpha.
- Returns over (t, t+1]:

  ```
  f_{t+1}   = lambda_t + z^f_{t+1},
  r^A_{t+1} = B^A f_{t+1} + alpha_t + z^A_{t+1},
  r^E_{t+1} = B^E f_{t+1} - c^E + z^E_{t+1},
  ```

  with c^E in R^M the known ETF fee-and-tracking drag (signed, as in M2), and the shock vector
  z_{t+1} = (z^f, z^A, z^E)_{t+1} ~ N(0, Sigma_z), independent across quarters and of the state
  process, Sigma_z = [[Sigma_f, C_fA, C_fE]; [., Sigma_A, C_AE]; [., ., Sigma_E]] known and
  positive definite. Contemporaneous dependence between residuals and factor shocks is allowed
  (M2's cross moments); the reference case is block-diagonal Sigma_z with Sigma_A diagonal
  (independent fund residuals). Internal fund costs are in r^A once; c^E is in r^E once; neither
  enters the trading cost below (section 2).
- State dynamics: theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta_{t+1}, eta ~ N(0, Q)
  independent over time and of z, with Phi = diag(Phi_lambda, Phi_alpha) and Q = diag(Q_lambda,
  Q_alpha). The **baseline** is fixed unknown means, Phi = I and Q = 0 (the proposal's
  stationary choice, as in M1-M4); unequal persistence of premia and alphas (Q4 of the program
  memo, ROADMAP D12's "different persistence") is the case Phi != I, Q != 0, admitted by the
  same formulas and requiring its own motivation before a claim uses it.

### Beliefs, public information and the Kalman filter

- Prior: theta_0 ~ N(m_0, P_0), Gaussian, with a **pooled alpha prior**: alpha_{0,i} = a_bar +
  eta_i, a_bar ~ N(mu_a, s_bar^2), eta_i iid N(0, s^2), so the alpha block of P_0 is
  s_bar^2 1 1' + s^2 I_N and the alpha block of m_0 is mu_a 1 (Bayesian fund selection with
  learning across funds, `pastor2002investing`; the calibration of mu_a, s_bar, s is the
  analyst's, from the fund-performance literature, not part of this definition). The premium
  block (m_0^lambda, P_0^lambda) is a separate prior from long factor histories. The prior
  cross-covariance between lambda and alpha is zero in the reference case and free in general.
- Information: I_t contains the prior, the model constants, all public returns through t
  (factor series f_1..f_t as attribution variables and every instrument's return, held or not,
  section 2), the manager's own holdings and past trades. Orders execute at the review after
  the information cutoff. The observation each quarter is y_{t+1} = (f_{t+1}, r^A_{t+1},
  r^E_{t+1}), linear in theta_t with Gaussian noise:

  ```
  y_{t+1} = H theta_t + d + L z_{t+1},   H = [[I_K, 0]; [B^A, I_N]; [B^E, 0]],   d = (0, 0, -c^E),
  L = [[I_K, 0, 0]; [B^A, I_N, 0]; [B^E, 0, I_M]],
  ```

  the noise being L z_{t+1} with covariance L Sigma_z L', because returns load on the realized
  factor f_{t+1} = lambda_t + z^f_{t+1}; equivalently the transformed observation
  L^{-1} y_{t+1} = (f, r^A - B^A f, r^E - B^E f + c^E)_{t+1} has noise exactly z_{t+1}
  (erratum of 2026-09-28, math; the merged text had noise z_{t+1} with covariance Sigma_z,
  which is wrong and which no claim or experiment used).

- Filter: beliefs stay Gaussian, theta_t | I_t ~ N(m_t, P_t), and (m_t, P_t) follow the Kalman
  filter for the state-space model above (predict with Phi, Q; update with H, Sigma_z). Two
  properties are to be verified in D12's first claim, not assumed: (i) **exogenous learning**:
  P_t is a deterministic sequence, independent of the manager's holdings and trades, because
  the observation is public and its noise does not depend on positions; hence there is no
  experimentation motive, and m_t is a martingale under the manager's own belief with
  innovation covariance K_t (H P_t^- H' + L Sigma_z L') K_t' set by the Kalman gain K_t; (ii) with
  block-diagonal Sigma_z and a zero prior cross-covariance, the premium and alpha blocks of the
  filter decouple (f identifies lambda; r^A - B^A f identifies alpha), so premium error reaches
  fund choice only through the loadings in the mean, not through the filter. A nonzero C_fA or
  prior cross-covariance couples the blocks; that is a stated departure, not the reference case.
- Predictive moments of next-quarter instrument returns given I_t:

  ```
  mu_t    = G m_t - (0, c^E),            G = [[B^A, I_N]; [B^E, 0]]  (n x (K+N)),
  Sigma_t = G P_t G' + Sigma_r,          Sigma_r = B Sigma_f B' + [[Sigma_A, C_AE]; [C_AE', Sigma_E]] + cross terms,
  ```

  where the cross terms are B [C_fA, C_fE] + its transpose, zero in the reference case. Sigma_t
  is the predictive covariance: return risk Sigma_r plus estimation risk G P_t G', which
  shrinks along the deterministic path of P_t. Unlike M1-M2's belief-averaged score, M5's
  objective charges estimation uncertainty through this predictive variance; that is the
  charter's "estimation error enters the optimization".

### Holdings, trades, costs and fees

- Positions: x_t^- in R^n before the review, trade u_t in R^n, x_t^+ = x_t^- + u_t. Cash is the
  residual and may be negative; positions may be negative. **No funding, long-only or cap
  constraint is imposed in M5**: this is the declared counterfactual, and D13 is where the
  funded long-only constraint returns. A claim in M5 must not describe its policy as
  implementable by a long-only fund of funds without D13's correction.
- Trading cost at the review: quadratic, C(u) = (1/2) u' Lambda u with Lambda symmetric positive
  definite and instrument-specific, reference case Lambda = diag(Lambda_A, Lambda_E) with
  Lambda_A = lambda_A I_N, Lambda_E = lambda_E I_M and lambda_A >= lambda_E >= 0 (funds costlier
  to trade than ETFs, the charter's premise). The general Lambda, including lambda_A < lambda_E
  and zero costs, is admitted; section 2's warning stands: no result may attribute its effect to
  a fund cost disadvantage that the instance does not carry. Quadratic costs are chosen for the
  linear-quadratic structure D12 targets (`garleanu2009dynamic`); they are not M2's directional
  proportional costs, produce no no-trade region by themselves, and D13's small-cost band is the
  proportional-cost correction around M5's target. Fees are in c^E, never in C.
- Wealth: W_{t+1} = W_t + (x_t^+)' r_{t+1} - C(u_t), with r_{t+1} = (r^A_{t+1}, r^E_{t+1}) the
  excess-return vector; the riskless return on the whole balance is the numeraire. Positions
  are dollars, not fractions of wealth, and the risk coefficient below is per squared dollar,
  as in `garleanu2009dynamic`; a wealth-normalized variant changes the coefficient along the
  path and is not the M5 objective.

### Objective

Fix gamma > 0 and a discount rho in (0, 1] (rho < 1 for the infinite horizon; rho = 1 allowed
with a finite T). The manager chooses a policy u_t = u_t(I_t, x_t^-) to maximize

```
V_0 = E_0 sum_{t >= 0} rho^t [ (x_t^+)' mu_t - (gamma/2) (x_t^+)' Sigma_t x_t^+ - (1/2) u_t' Lambda u_t ],
```

the discounted sum of quarterly certainty equivalents under the predictive moments, net of
trading costs (the quarterly mean-variance objective of the D12 note; M0's formulation 2 as a
sum over reviews). It is not expected terminal utility (M3's CARA objective is not used), it
charges variance with the predictive Sigma_t, and it charges the quadratic cost once, in the
same units as the expected gain. Because Sigma_t is deterministic and mu_t is a martingale
with known innovation covariance, this is a discrete-time linear-quadratic tracking problem
with a random linear coefficient; its solution is D12's first claim, cited through the ledger
where `garleanu2009dynamic` (with Bayesian learning, `brennan1998role`) already gives it, and
proved only for what M5's structure adds.

### Decision objects named for D12 (definitions and obligations, not results)

- Frictionless target: Markowitz_t = (gamma Sigma_t)^{-1} mu_t, the maximizer of the
  one-quarter certainty equivalent at Lambda = 0. Its exposure is B' Markowitz_t.
- Partial-adjustment form: a policy is of partial-adjustment form if x_t^+ = x_t^- + Gamma_t
  (aim_t - x_t^-) for an n x n trading-rate matrix Gamma_t and an aim portfolio aim_t measurable
  with respect to I_t. D12's target statements, to be proved, are that the optimal policy has
  this form; that Gamma_t = Lambda^{-1} A_t for A_t solving a (time-varying, because P_t moves)
  Riccati recursion whose stationary limit exists when P_t converges; that aim_t is a
  Gamma_t-weighted combination of the current and expected future Markowitz targets, the future
  targets' expectation computed with m_t (martingale) and the deterministic path of Sigma_t
  (so the aim accounts for predictive variance shrinking under learning and for future costs);
  and that the two trading speeds (fund block, ETF block of Gamma_t) are ordered by the two
  cost levels once bundling is accounted for.
- The split: write aim_t = aim_t^X + aim_t^alpha, the **exposure part** (the aim when alpha
  beliefs are set to their prior mean and only premium beliefs move) and the **alpha part**
  (the remainder), and the exposure aim's implementation through ETFs versus funds. D12's
  target is the explicit form of this split and how bundling (B^A != 0), the two error
  structures (the lambda and alpha blocks of P_t) and the two cost levels (Lambda_A, Lambda_E)
  set the split and the speeds: in particular whether premium news is traded through ETFs and
  alpha news through funds, and what a fund's factor part does to that. Any such statement is
  a claim with a proof; this paragraph only fixes the names.
- Comparators for experiments: the two-stage heuristics of claims 027-028 in M5's coordinates,
  ETF-only (u^A = 0), equal weighting and no trade; how they are defined in M5 is part of the
  experiment or claim that uses them.

### Section 2 commitments, restriction inventory and proof obligations

Section 2, read through the human's revision, is kept as follows. Decisions are quarterly, with
no interim trading. Alpha and premia are distinct latent objects with separate priors and
separate error structures. Funds and ETFs have different footprints, with replication a
benchmark case. Public returns are observed whether or not held, and learning is exogenous.
Internal fund costs sit in r^A, ETF fees in r^E, shareholder trading costs in C, each once.
Funds are not assumed costly: the ranking lambda_A >= lambda_E is the reference case and the
equal-cost and zero-cost cases are admitted. The one departure is funding: M5 has no long-only
or budget constraint, as a declared counterfactual that D13 removes.

M5 restricts the application to known fixed loadings, Gaussian shocks and beliefs (unbounded
returns), a known shock covariance, a linear-Gaussian state process with known Phi and Q
(baseline: fixed unknown means), quadratic costs, an unconstrained position space, a
per-quarter mean-variance objective with a fixed risk coefficient per squared dollar, and no
taxes, flows, capacity, fund closures or menu changes. Estimated loadings and covariances are
later work. The analyst's calibrations (French factors; the alpha distribution from the
fund-performance literature; fees and costs from SEC fee tables) are inputs to experiments,
not part of this definition.

Proof obligations before or within D12's first claim: the Kalman recursion for (m_t, P_t) with
P_t deterministic and m_t a martingale (property (i)); the block decoupling under the reference
case (property (ii)); the predictive-moment formulas; the existence of an optimal policy and the
finiteness of V_0 (for rho < 1 the per-period terms are bounded above by
(1/(2 gamma)) mu_t' Sigma_t^{-1} mu_t, whose expectation must be shown summable); the
partial-adjustment form and its Riccati characterization, cited where known; and the split.
None of these is established by this specification.

## M6  Quarterly tracking of a moving frictionless target under proportional costs and long-only caps, 2026-09-28

Proposed D13 working model (mathb). M0-M4 are unchanged; M5 (D12's quadratic-cost learning model,
math) is written separately and is not a prerequisite. M6 keeps M2's directional proportional
shareholder costs, funded long-only holdings and one-quarter conditional score, iterates the score
over quarterly reviews, and makes the moving frictionless target the object of study. The target
process is *generic* here: M6 takes the belief-mean process as given and does not specify how
beliefs are formed. The specialization to D12's aim portfolio and to Kalman-updated beliefs is a
later version. PM and red read this definition before a claim or experiment uses it. No band,
attainment, convexity or asymptotic statement is assumed here; those are proof obligations.

### Instruments, timing and public information

- Any finite numbers of instruments: N >= 0 active funds and M >= 0 ETFs, n = N + M >= 1 in all,
  indexed together by i; K economic factors. Reviews at t = 0, 1, ..., T-1 with T >= 1, terminal
  marking at T without forced liquidation and without a terminal trade. Each interval is one
  quarter; there is no interim investor trade. Cash-account units; cash has gross return one.
- A finite nonempty public state set Z and a public state z_t in Z known at review t. Given z_t = z,
  the next state and the vector of instrument gross returns over (t, t+1] have a known finite joint
  law q_t(z', g | z), g in R^n with every g_i > 0. This law is public and independent of holdings and
  trades: ownership creates no information. A degenerate law (one outcome, g = 1) is allowed.
- A known belief-mean function mu(t, z) in R^n: the belief mean, given z at review t, of next-quarter
  excess returns, written mu(t, z) = B lambda(t, z) + (alpha(t, z), -c^E) with known loadings B, belief
  means lambda(t, z) of the factor premia, alpha(t, z) of the fund alphas and known signed ETF drag
  c^E. Alpha and premia remain distinct objects; the generic stage uses only mu. When the belief mean
  is a posterior mean of a fixed parameter under public observations, z carries the belief and mu is a
  martingale in t; M6 does not impose this.
- A known constant positive definite return covariance Sigma in R^(n x n) and a risk coefficient
  gamma > 0. Positive definiteness is a strengthening of M2 (which allowed singular Sigma) needed to
  define the target. A discount factor beta in (0, 1]; beta = 1 is the reference case.

### Holdings, funding, costs and caps

Dollar holdings x_t^- in R^n, x_t^- >= 0, and cash h_t^- >= 0 before review t; trade u_t; post-trade
x_t^+ = x_t^- + u_t and h_t^+ = h_t^- - 1'u_t - C(u_t), with M2's directional cost
C(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-], rates in [0, 1), no ranking between fund and ETF rates.
Marking: x_{t+1}^- = x_t^+ o g_{t+1} (coordinatewise), h_{t+1}^- = h_t^+. Constraints at every review:
0 <= x_t^+ <= bar x (caps in dollars, bar x_i in (0, infinity]) and h_t^+ >= 0 (funded). A pre-trade
holding may exceed its cap after marking; the cap constrains post-trade holdings. The initial
holdings satisfy the caps. Fixed fees, loads, redemption windows, taxes, flows and nonlinear impact
are absent, as in M2.

*Slack-budget instance.* An instance with finite caps and h_0^- >= T sum_i (1 + kappa^+_i) bar x_i.
Purchases over the horizon cost at most that amount, so h_t^+ >= 0 holds for every feasible policy and
the cash constraint never binds. Claims may assume this; it is a restriction, not the model, and the
funded budget must be restored in a later claim. Cash earns nothing in cash-account units.

### Objective, frictionless target and tracking identity

Maximize, over policies measurable with respect to (t, z_t, x_t^-, h_t^-),

```
E sum_{t=0}^{T-1} beta^t [ mu(t, z_t)' x_t^+ - (gamma/2) x_t^+' Sigma x_t^+ - C(u_t) ].
```

This is M0's formulation 2 iterated: a sum of one-quarter belief-average conditional scores (claim
003's belief-mean representation applies quarter by quarter). It is not a terminal-utility or
terminal mean-variance problem and must not be presented as one (M0). No predictive-variance or
ambiguity term is added: as in M1-M2, two belief processes with the same means give the same
objective. Define the *frictionless target* and the *tracking identity*

```
x*(t, z) = Sigma^{-1} mu(t, z) / gamma,
mu' x - (gamma/2) x' Sigma x = mu' Sigma^{-1} mu / (2 gamma) - (gamma/2) (x - x*)' Sigma (x - x*).
```

The target is the unconstrained one-quarter optimum without costs; it may be negative or exceed a
cap. The first term depends only on (t, z), so maximizing the objective is minimizing the expected
discounted sum of tracking losses (gamma/2)(x_t^+ - x*_t)' Sigma (x_t^+ - x*_t) plus costs, subject to
the caps and funding. A claim that uses the constrained frictionless optimum instead must define it.
Define V_t(x, z) as the infimum of the expected discounted remaining loss from pre-trade holdings x at
public state z under a slack budget, with V_T = 0. Existence of an optimal policy, convexity of V_t
and the interval structure of the optimal trade are proof obligations for claim 029.

### Commitments and limits

All proposal section 2 commitments remain visible: quarterly decisions; alpha and premia distinct in
mu; instruments with different footprints through B and Sigma; funded long-only holdings with caps;
public returns and states independent of ownership; internal costs already in net returns, ETF drag
subtracted once, shareholder costs charged once; no imposed ranking of fund and ETF rates. M6
restricts to a known finite public state and return law, a given belief-mean process, constant
positive definite Sigma, dollar caps, and an additive quarterly-score objective. It does not model
how beliefs are formed, estimation error as a decision input beyond the belief mean, changing
loadings, or a terminal-utility criterion. It asserts no result.

## M7  M6 around M5's learning-driven target: proportional costs and caps with the predictive risk charge, 2026-09-28

Proposed D13 specializing version (mathb; PM's note of 2026-09-28 and math's fit reply). M0-M6 are
unchanged. M7 takes M5's instruments, factor model, pooled Gaussian prior, Kalman filter and
predictive moments verbatim, and replaces M5's quadratic costs and unconstrained positions by M6's
directional proportional costs, long-only caps and quarterly-score objective. It is M6 with the
belief-mean and covariance processes specified: the frictionless target is M5's Markowitz target,
and its motion has two parts, the belief-mean innovation and a deterministic drift from the
shrinking predictive risk charge. No M5 or M6 result transfers without proof; claim 100 is the
transfer of claim 029. PM and red read this definition before a claim or experiment names it.

### Beliefs, filter and predictive moments (from M5, fixed-means baseline)

- Instruments N >= 0 funds and M >= 0 ETFs, n = N + M >= 1, K factors, known loadings B^A, B^E,
  G = [[B^A, I_N]; [B^E, 0]], signed drag c^E, shock covariance Sigma_z (positive definite),
  Sigma_r = B Sigma_f B' + [[Sigma_A, C_AE]; [C_AE', Sigma_E]] + cross terms, all as in M5.
- Fixed unknown means (M5's baseline Phi = I, Q = 0): theta = (lambda, alpha) is drawn once, with
  mean m_0 and covariance P_0 (M5's pooled alpha prior), and held fixed over the horizon.
- Observation and filter, with M5's erratum: y_{t+1} = H theta + d + L z_{t+1}, R = L Sigma_z L';
  K_t = P_t H' (H P_t H' + R)^{-1}, m_{t+1} = m_t + K_t (y_{t+1} - H m_t - d), P_{t+1} = P_t - K_t H P_t.
  Since Phi = I and Q = 0, P_t^{-1} = P_0^{-1} + t H' R^{-1} H (information form), P_t is
  deterministic and nonincreasing in the positive semidefinite order, and V_t = P_t - P_{t+1} is
  the unconditional covariance of the belief-mean innovation epsilon_{t+1} = m_{t+1} - m_t.
- Predictive moments and target: mu_t = G m_t - (0, c^E), Sigma_t = G P_t G' + Sigma_r (positive
  definite; deterministic in t), x*_t = (gamma Sigma_t)^{-1} mu_t (M5's Markowitz_t). Under
  proportional costs there is no partial-adjustment aim; D12's aim portfolio is the comparator only
  when a claim compares M7 with M5's policy, and it must say so.
- Target decomposition, an identity: x*_{t+1} - x*_t = (gamma Sigma_{t+1})^{-1} G epsilon_{t+1}
  + [(gamma Sigma_{t+1})^{-1} - (gamma Sigma_t)^{-1}] mu_t. The first term has covariance
  (gamma Sigma_{t+1})^{-1} G V_t G' (gamma Sigma_{t+1})^{-1}; the second is the *learning drift*,
  known at t, from the falling risk charge. With the pooled prior the fund block carries a common
  and a relative direction with different uncertainty (math's claim 032, provisional); M7 keeps
  V_t as a matrix and leaves the per-direction reading to claims.

### Two shock laws; which one a claim uses

- *Gaussian law* (M5's): z ~ N(0, Sigma_z), theta ~ N(m_0, P_0). The filter is the exact posterior,
  epsilon_{t+1} is a martingale difference with conditional covariance V_t, and gross returns are
  unbounded and not positive. M6's finite-state framework does not cover it; a claim under this
  law must supply its own integrability and marking arguments.
- *Finite-law variant*: theta is drawn from a finite law with mean m_0 and covariance P_0, and
  z_{t+1} from a finite centered law with covariance Sigma_z, independent across quarters and of
  theta, with every gross return 1 + r_i positive. The manager still runs the linear filter above,
  which is then the best linear predictor with error covariance P_t, not the Bayesian posterior;
  epsilon_{t+1} has mean zero and covariance V_t unconditionally but need not be centred given the
  history. The public state is z_t = (t, y_1, ..., y_t), a finite tree; its transition law
  q_t(y_{t+1} | z_t) is the true predictive law of the finite prior; mu(t, z) = mu_t and
  Sigma(t, z) = Sigma_t as above. Under this variant M7 is an M6 instance with time-varying
  covariance (M6 as written has a constant Sigma; the transfer with Sigma_t is claim 100's part 1).
  This is the lab's exact evaluation device (as M1-M4, M6); it is not a claim that fund returns
  have finite support.

### Holdings, costs, caps, objective and commitments

M6's, with Sigma(t, z) = Sigma_t and mu(t, z) = mu_t: dollar holdings marked by gross returns,
directional rates kappa^+_i, kappa^-_i in [0, 1), caps bar x, funded cash with M6's slack-budget
instance available as a hypothesis, discount beta in (0, 1] (M5's rho), finite T, objective the
expected discounted sum of quarterly scores mu_t' x_t^+ - (gamma/2) x_t^+' Sigma_t x_t^+ - C(u_t),
and the tracking identity with Sigma_t. The predictive Sigma_t charges estimation risk as M5 does;
that is the charter's "estimation error enters the optimization", and it is the one place where
M7 differs from M6's belief-mean score. All proposal section 2 commitments remain as in M5 and
M6: quarterly decisions, distinct alpha and premia, different footprints, funded long-only caps,
public information independent of ownership, separate internal and shareholder costs, no cost
ranking. Restrictions: fixed means (no persistence), known loadings and covariances, a linear
filter, dollar caps, additive quarterly scores. M7 asserts no result.

## M8  One fund, one ETF and cash over two reviews: learning, predictive risk, return marking and a funded budget in one model (D17 worked model), 2026-09-29

The worked model of D16 and D17 (mathb, PM's D17 note; to be read by math before a D16 claim
names it). M8 is M7 specialized to one fund, one ETF, one factor, two reviews and the funded
budget, with the two shock laws stated side by side so that a claim says which one it uses. It
fixes definitions and asserts no result; claim 112 says which approved results apply to it.

### Instruments, returns and the latent means

- One active fund A, one ETF E, cash; one economic factor. Known loadings b_A > 0 and b_E > 0,
  known signed ETF drag c^E. Reviews at t = 0 and t = 1, terminal marking at t = 2 with no
  terminal trade. Cash-account units: cash has gross return one and excess return zero; every
  return below is an excess return over the quarter.
- Latent means theta = (lambda, alpha), the factor premium and the fund's net alpha per quarter,
  drawn once and fixed (M5's baseline, Phi = I, Q = 0). Returns over (t, t+1]:

  ```
  f_{t+1} = lambda + z^f_{t+1},   r^A_{t+1} = b_A f_{t+1} + alpha + z^A_{t+1},   r^E_{t+1} = b_E f_{t+1} - c^E + z^E_{t+1},
  ```

  with shocks (z^f, z^A, z^E)_{t+1} centred, independent across quarters and of theta, with
  covariance diag(sigma_f^2, sigma_A^2, sigma_E^2) (the reference block-diagonal case; a cross
  moment is a stated departure).

### Beliefs: one recursion, two laws

- Prior mean m_0 = (lambda_hat_0, alpha_hat_0) and covariance P_0 = diag(p^lambda_0, p^alpha_0)
  (zero prior cross-covariance, the reference case). Public observation at review t+1:
  y_{t+1} = (f, r^A, r^E)_{t+1}, equivalently (f, r^A - b_A f, r^E - b_E f + c^E)_{t+1} =
  (lambda + z^f, alpha + z^A, z^E)_{t+1}: the factor return observes the premium with noise z^f,
  the fund's residual return observes alpha with noise z^A, and the ETF's residual carries no
  information about theta.
- The *linear filter* (M5's Kalman recursion, scalar by block because the blocks decouple):

  ```
  k^lambda_t = p^lambda_t/(p^lambda_t + sigma_f^2),      lambda_hat_{t+1} = lambda_hat_t + k^lambda_t (f_{t+1} - lambda_hat_t),      p^lambda_{t+1} = (1 - k^lambda_t) p^lambda_t,
  k^alpha_t  = p^alpha_t/(p^alpha_t + sigma_A^2),        alpha_hat_{t+1}  = alpha_hat_t + k^alpha_t (r^A_{t+1} - b_A f_{t+1} - alpha_hat_t),   p^alpha_{t+1} = (1 - k^alpha_t) p^alpha_t,
  ```

  so 1/p_{t+1} = 1/p_t + 1/sigma^2 in each block: P_t is deterministic (exogenous learning; M5's
  property (i), claim 030), and V_t = P_t - P_{t+1} is the unconditional covariance of the
  belief-mean innovation epsilon_{t+1} = m_{t+1} - m_t under either law below.
- *Predictive moments* of next-quarter excess returns given the beliefs, x = (a, p) the fund and
  ETF holdings:

  ```
  mu_t = ( b_A lambda_hat_t + alpha_hat_t,  b_E lambda_hat_t - c^E ),
  Sigma_t = [[ b_A^2 (sigma_f^2 + p^lambda_t) + sigma_A^2 + p^alpha_t,   b_A b_E (sigma_f^2 + p^lambda_t) ],
             [ b_A b_E (sigma_f^2 + p^lambda_t),                          b_E^2 (sigma_f^2 + p^lambda_t) + sigma_E^2 ]],
  ```

  positive definite and deterministic; the frictionless target is x*_t = (gamma Sigma_t)^{-1} mu_t.
- *Gaussian law* (M5's): theta ~ N(m_0, P_0) and the shocks Gaussian. The filter is the exact
  posterior, m_t = E[theta | I_t], epsilon_{t+1} is a martingale difference with conditional
  covariance V_t, and gross returns are unbounded, so 1 + r can be nonpositive with positive
  probability.
- *Finite-law variant* (M7's, the lab's exact evaluation device): theta drawn from a finite law
  with mean m_0 and covariance P_0 (the reference choice: two points per block, m_0 +- sqrt(P_0)),
  and each shock from a finite centred law with the stated variance, independent, with every
  gross return 1 + r_i > 0 on the support. The manager runs the same linear filter, which is
  then the best linear predictor of theta given y_1, ..., y_t with error covariance P_t, not the
  posterior: epsilon_{t+1} has mean zero and covariance V_t unconditionally but need not be
  centred given the history, and the *exact posterior* E[theta | y_1, ..., y_t] under the finite
  law (finite Bayes' rule, as in M3) differs from m_t at some histories, agreeing with it in
  expectation. The public state is the observed history, a finite tree with the true predictive
  law q_t(y_{t+1} | history); the manager's mu_t and Sigma_t on the tree are the filter's. A
  claim under this variant may use the tree for exact evaluation and must say that the filter
  is not the posterior there; a claim under the Gaussian law must supply its own integrability
  and marking arguments.

### Holdings, marking, costs, caps and the funded budget

M6's, with M7's predictive moments: dollar holdings x^-_t = (a^-_t, p^-_t) >= 0 and cash h^-_t >= 0
before review t; trade u_t; post-trade x^+_t = x^-_t + u_t in [0, bar x] (caps) and
h^+_t = h^-_t - 1'u_t - C(u_t) >= 0 (funded), with C(u) = sum_i [kappa^+_i u_i^+ + kappa^-_i u_i^-],
rates in [0, 1) and no ranking between the fund's and the ETF's. Marking: x^-_{t+1} = x^+_t o
(1 + r_{t+1}) coordinatewise and h^-_{t+1} = h^+_t. Under the finite law marking keeps holdings
nonnegative; under the Gaussian law it need not (a stated limit). The budget may bind: M8 is
not the slack-budget instance, and every claim says whether it assumes a slack budget.

### Objective and the three policies

The manager maximizes, over policies measurable in the public history and its own holdings,

```
E sum_{t=0}^{1} beta^t [ mu_t' x^+_t - (gamma/2) x^+_t' Sigma_t x^+_t - C(u_t) ],
```

the expectation over the shock law (the tree under the finite law), the stage score using the
filter's predictive moments under either law, gamma > 0, beta in (0, 1]. By M6's tracking
identity this minimizes the expected tracking loss against x*_t plus costs. Three policies
are named for D16 and D18: the *dynamic* policy (the two-review optimum); the *myopic* policy
(at each review, the one-review optimum at the current beliefs, holdings and cash, claim 110's
rule); and an *exposure-first* policy (a two-stage split at each review: claim 111's
incumbent-aware first stage, or claim 041's frictionless one where fundable). All three see the
same information, objective and feasible trades.

### Commitments and limits

All proposal section 2 commitments as in M5-M7. Restrictions: one fund, one ETF, one factor,
two reviews, fixed means, known loadings and variances, block-diagonal shocks, a linear
filter, dollar caps, additive quarterly scores. M8 asserts no result; claim 112 states which
approved results apply to it and under which law, and gives the worked example.

## M9  M8 with M5's state equation: time-varying premia and alphas (D24), 2026-09-30

D24's model (mathb, PM's note; LAB_REQUEST_2 item 6): M8 with M5's persistence variant, the
one place M5 admits a moving latent mean "requiring its own motivation before a claim uses it".
The motivation is the request: the target moves because premia and alphas move, not only
because beliefs are revised. M9 is M8 in every respect except the latent means and the filter,
and it asserts no result; claim 114 says what transfers.

### The latent means and the filter

- Latent means theta_t = (lambda_t, alpha_t) follow M5's state equation,

  ```
  theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta_{t+1},      Phi = diag(phi_lambda, phi_alpha),  |phi| <= 1,  theta_bar = (lambda_bar, alpha_bar),
  ```

  with eta_{t+1} centred, covariance Q = diag(q_lambda, q_alpha), independent across quarters
  and of theta_0 and of the shocks z. Returns over (t, t+1] are M8's with theta_t. Phi = I and
  Q = 0 is M8.
- The observation is M8's, y_{t+1} = H theta_t + d + L z_{t+1} (returns over (t, t+1] carry
  theta_t), in transformed form (f, r^A - b_A f, r^E - b_E f + c^E)_{t+1} = (lambda_t + z^f, alpha_t + z^A, z^E)_{t+1}:
  H = I on the two blocks, R = diag(sigma_f^2, sigma_A^2).
- The *linear filter* (M5's Kalman recursion with predict and update; scalar by block since
  Phi, Q, P_0 and R are diagonal):

  ```
  K_t = P_t (P_t + R)^{-1},                nu_{t+1} = (f_{t+1} - lambda_hat_t,  r^A_{t+1} - b_A f_{t+1} - alpha_hat_t)     (the innovation),
  P^u_t = P_t - K_t P_t                    (theta_t's error covariance after y_{t+1}),
  m_{t+1} = Phi ( m_t + K_t nu_{t+1} ) + (I - Phi) theta_bar,        P_{t+1} = Phi P^u_t Phi' + Q,
  ```

  so the belief mean has a *predictable move* E_t m_{t+1} - m_t = (Phi - I)(m_t - theta_bar) and
  a *belief innovation* epsilon_{t+1} = Phi K_t nu_{t+1}, of unconditional mean zero and
  covariance V_t = Phi (P_t - P^u_t) Phi'. P_t is deterministic and no longer monotone:
  P_{t+1} - P_t = Q - (P_t - Phi P^u_t Phi'), positive when the state noise exceeds what a
  quarter's observation removes. Each block's recursion p_{t+1} = phi^2 p_t s/(p_t + s) + q
  (s the block's observation noise variance) is increasing and concave in p_t and bounded, so
  P_t converges to a fixed point, unique when q > 0 or phi^2 < 1 (claim 114's proof of 1b); the
  steady-state filter's form is AX-10's Theorem 2.1 under its own hypotheses (cited for the
  form only; the fixed-means case phi = 1, q = 0 has the fixed point 0).
- Predictive moments and target as in M8, mu_t = G m_t - (0, c^E), Sigma_t = G P_t G' + Sigma_r,
  x*_t = (gamma Sigma_t)^{-1} mu_t, and the *target decomposition*, an identity:

  ```
  x*_{t+1} - x*_t = Delta^p_t + Delta^u_{t+1},
  Delta^p_t     = (gamma Sigma_{t+1})^{-1} G (Phi - I)(m_t - theta_bar) + [ (gamma Sigma_{t+1})^{-1} - (gamma Sigma_t)^{-1} ] mu_t     (predictable: known at t),
  Delta^u_{t+1} = (gamma Sigma_{t+1})^{-1} G Phi K_t nu_{t+1}                                                                  (unpredictable: mean zero, covariance (gamma Sigma_{t+1})^{-1} G V_t G' (gamma Sigma_{t+1})^{-1}).
  ```

  With Phi = I the first term of Delta^p vanishes and the second is claim 100's learning drift.

### The two laws, holdings, objective and policies

As M8: the Gaussian law (theta_0, eta and z Gaussian; the filter is the exact posterior) and
the finite-law variant (finite supports with the stated moments, positive gross returns, the
public tree of observed histories with the true predictive law; the filter is the best linear
predictor). Holdings, marking, costs, caps, the funded budget, the two-review objective and the
three policies are M8's. Restrictions as M8, with fixed means replaced by M5's diagonal state
equation with known Phi, Q and theta_bar. M9 asserts no result.

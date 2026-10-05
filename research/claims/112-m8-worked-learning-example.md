---
id: 112
title: "One consistent worked learning example (M8): belief updates, predictive risk, return marking and the funded budget belong to one model under either shock law; the linear filter is the exact posterior under the Gaussian law and the best linear predictor under the finite law, where the two means differ at some histories and agree in expectation; which approved results apply to the example under which law; and the example at stated inputs, with the finite-law posterior against the filter, the budget binding today and the myopic policy dynamically optimal"
status: formalized
model_version: M8
depends_on: [029, 30, 038, 044, 100, 109, 110, 111]
axioms_used: [AX-13, AX-17, AX-18]
formal: lean/Standalone/M8WorkedLearningExample.lean
direction: D17
---
## Statement

D17's claim (LAB_REQUEST item 3): the worked learning example in one specified model. M8
(model/SPEC.md) is the model: one fund, one ETF and cash over two reviews, M7's learning-driven
target with the funded budget allowed to bind, and the two shock laws stated side by side.
This claim proves that its four elements are consistent under either law (part 1), resolves
the difference between exact Gaussian learning and the finite-law linear filter (part 2),
states which approved results transfer to M8 under which law and what remains unproved (part
3), and works the example through at stated inputs in a form the writer can use (part 4).

**Setting.** M8 as written: loadings b_A, b_E > 0, drag c^E, prior (m_0, P_0) with
P_0 = diag(p^lambda_0, p^alpha_0), shock variances (sigma_f^2, sigma_A^2, sigma_E^2), the linear
filter with gains k^lambda_t, k^alpha_t, predictive moments (mu_t, Sigma_t), rates, caps, the
incumbents (a^-_0, p^-_0, h^-_0) with h^-_0 >= 0, gamma > 0, beta in (0, 1], reviews t = 0, 1.
Under the finite law, theta takes the two values m_0 +- sqrt(P_0) per block and each shock a
finite centred law with the stated variance; the public tree has the observed histories as
nodes with the true predictive law.

### Part 1. The four elements belong together

1a. *Beliefs.* Under either law, (m_t, P_t) follow M8's recursion, P_t is deterministic and
    independent of holdings and trades (exogenous learning: the observation is public and its
    noise does not depend on positions), and P_1 = (P_0^{-1} + diag(1/sigma_f^2, 1/sigma_A^2))^{-1}.
1b. *Predictive risk.* Sigma_t = G P_t G' + Sigma_r is positive definite and deterministic, and
    the stage score mu_t' x - (gamma/2) x' Sigma_t x charges estimation risk through P_t; the
    target x*_t = (gamma Sigma_t)^{-1} mu_t is well defined at every history.
1c. *Marking.* Under the finite law every gross return is positive, so marking maps
    nonnegative holdings to nonnegative holdings and leaves cash unchanged; under the Gaussian
    law a pre-trade holding is negative with positive probability, the post-trade caps still
    apply and the stage score is finite, so the objective is finite, but M6's finite-state
    framework does not cover it (Not shown).
1d. *Funding.* Under the finite law the feasible set is nonempty and compact at every history
    and holdings: h^-_t >= 0 is preserved by marking and x^-_t >= 0 by 1c, so no trade is
    feasible when the marked holdings are within the caps, and when marking has carried a
    holding above its cap the sale down to the cap is feasible, since a sale raises cash (the
    same convention as claim 111's exposure-first first stage); hence the review problem has
    a unique optimum (strict concavity), and the two-review problem has an optimal policy,
    obtained by backward induction on the tree (claim 044's part 1 on M8's tree, which lean's
    formalization instantiates). Under the
    Gaussian law the same holds at review 0 and, at review 1, on the event {x^-_1 >= 0}; off it
    a negative marked holding must be bought back to zero, which costs cash, and with h^+_0 = 0
    (the example's own review-0 action) review 1 can be infeasible (Not shown); the review-1 problem at every node is
    claim 109's one-review problem with N = M = K = 1 and is solved by claim 110's rule, and the
    review-0 problem is a one-review problem with the continuation E[V_1 | history] added, a
    concave function of the post-trade holdings and cash.

### Part 2. The two laws resolved

2a. *Same recursion, different meaning.* The filter's (m_t, P_t) are the same functions of the
    observations under both laws. That under the Gaussian law m_t = E[theta | I_t] with
    posterior covariance P_t (so epsilon_{t+1} = m_{t+1} - m_t is a martingale difference with
    conditional covariance V_t = P_t - P_{t+1}), and that under any law with these first two
    moments m_t is the best linear predictor of theta given y_1, ..., y_t with error covariance
    P_t, are the two meanings of the recursion, cited (rule 21): the Gaussian half is ledger
    entry AX-18 (`murphy2007conjugate`, the exact conjugate posterior of a static Gaussian mean
    under Gaussian observations, precision adding with each one), applied block by block to
    M8's observations lambda + z^f and alpha + z^A with n = 1 (its hypotheses: a static state,
    a Gaussian prior, conditionally independent Gaussian noise, which M8's Gaussian law and
    zero prior cross-covariance supply; AX-10's steady-state statement does not cover this
    transient case); the general half is ledger entry AX-17 (`uhlmann2022gaussianity`, Kalman's
    Corollary 1: the recursion is the minimum-mean-squared-error affine predictor for any noise
    law with the stated finite first two moments, and the exact Bayes posterior under Gaussian
    noise, not in general otherwise), whose hypotheses M8's finite law meets. What this claim proves under the
    finite law is the moment content: epsilon_{t+1} has mean zero and covariance V_t
    *unconditionally* (a two-line computation), and the exact posterior mean
    theta_hat^B_t = E[theta | y_1, ..., y_t] satisfies E[theta_hat^B_t] = E[m_t] = m_0, and
    theta_hat^B_1 != m_1 at any observation y_1 reached from exactly two hidden branches with
    theta = m_0 + sqrt(P_0) and theta = m_0 - sqrt(P_0) in a block (the posterior mean of that
    block is then m_0's) whose filter innovation y_1 - H m_0 - d is nonzero in that block (the
    filter then moves): part 4's node A is such an observation, where the filter moves the
    alpha belief up by 0.55% while the exact posterior returns to the prior. The condition is
    needed: with theta and the noise both in {-1, +1}, equiprobable and independent, the
    posterior mean is y/2 at every observation, which is the filter's (red's counterexample).
2b. *Which manager the lab models.* Under both laws the manager's policy uses (m_t, P_t) and the
    predictive score, by M7-M8's definition; the objective's expectation is over the true law.
    Under the finite law a manager using the exact posterior would be a different decision
    maker (its beliefs are not linear in the data), and its policy is not the lab's; the
    finite law is the evaluation device that makes the dynamic program exact, and the Gaussian
    law is the one under which the filter is the posterior. The two coincide in the first two
    moments of every belief and return, which is all the stage score uses.
2c. *What differs beyond the moments.* The continuation value at review 0 is an expectation of
    the review-1 value over the tree, so it depends on the finite law beyond its second
    moments (as claim 108's Not shown says of the frozen band); two finite laws with the same
    moments may give different dynamic policies (no instance is given), while the myopic policy
    depends on the law through (m_t, P_t) only.

### Part 3. What transfers to M8, under which law, and what is unproved

- *One-review results, either law, every review on the finite tree; under the Gaussian law at
  review 0 and, at review 1, on {x^-_1 >= 0}.* Claims 102, 104, 106, 109, 110 and 111 (and
  claims 040-041 with the ETF at zero) are statements about one quadratic program with the
  current predictive moments and nonnegative incumbents, so they hold at each review of M8 on
  the finite tree and, under the Gaussian law, wherever the marked incumbents are nonnegative, with
  N = M = K = 1 and b_E > 0 for spanning (claim 111's explicit parts with the ETF residual off,
  sigma_E = 0, as its Setting requires). In particular claim 110 gives the myopic policy at
  both reviews as two scalar roots, and claim 111 the exposure-first policy's exactness and
  loss; claim 109's part 1 is the review-1 optimality criterion.
- *Dynamic band results, finite law, slack budget.* Claims 029, 100, 107 and 108 hold in M8's
  finite-law variant when the budget is slack (M6's slack-budget instance, h^-_0 large), with
  claim 100's learning-path statements for M8's P_t path (the static width rises, the target
  drifts outward); they are not claimed with a binding budget (D16), nor under the Gaussian law.
- *M5's results, the target only.* Claims 030-032 and 036 describe M5's quadratic-cost,
  unconstrained, unmarked policy under the Gaussian law; what transfers to M8 is the target's
  structure they share with M7 (claim 038's part A): the split of x*_t into an exposure and a
  fund part, its motion as a belief innovation plus the learning drift, and claim 036's factor
  for when anticipating learning changes the aim, as statements about the target under either
  law; no policy statement transfers (claim 038's part B).
- *Claim 038.* Its M7 side is M8's finite-law variant; the Bellman-residual identity (C1) holds
  on M8's tree for any policy, and the horizon-one part (D) is the review-1 theory.
- *Unproved.* Existence and regularity of the dynamic optimum under the Gaussian law (an
  infinite tree, unbounded returns, marking); the dynamic band and the myopic policy's
  optimality with a binding budget (D16's question, illustrated in part 4 only); the exact
  posterior manager's policy under the finite law; and any dependence of the dynamic policy on
  the finite law beyond its moments (2c).

### Part 4. The worked example (`checks/112/check.py`, deterministic; all inputs assumed, an illustration)

*Table 1, inputs (per quarter).* b_A = 0.9, b_E = 1, c^E = 5 bp; prior lambda ~ (1.0%, sd
0.4%), alpha ~ (0.4%, sd 2.0%); finite laws: lambda in {0.6%, 1.4%} and alpha in {-1.6%, 2.4%}
(two points per parameter, m_0 +- sqrt(P_0)), the factor shock in {-8.4, -7.6, +7.6, +8.4}%
(sd 8.01%), the fund's residual shock in {-8, -4, +4, +8}% (sd 6.32%), the ETF's residual shock
in {-0.5, +0.5}% (sd 0.5%), every support equiprobable and independent, the first two chosen on
a lattice so that some observations are reached from two hidden branches (128 hidden branches,
72 public nodes); gamma = 2.5, beta = 1; rates fund 50 bp, ETF 10 bp each way; caps 1;
incumbents fund 0.40, ETF 0 (at zero), cash 0.06.

*Table 2, beliefs and predictive moments at review 0.* P_0 = diag(1.6e-5, 4.0e-4); gains
k^lambda = 0.0025, k^alpha = 0.0909 (one quarter teaches little about the premium and about a
tenth of the alpha uncertainty); P_1 = diag(1.596e-5, 3.636e-4). mu_0 = (1.30%, 0.95%),
Sigma_0 = [[0.00961, 0.00579], [., 0.00646]], target x*_0 = (0.406, 0.225): the fund near its
incumbent, the ETF wanted at 0.225 against an incumbent of 0.

*Table 3, review-1 beliefs: the filter against the exact finite-law posterior.* 72 public
nodes; the largest gap between the exact posterior mean and the filter's is 0.42% on the
premium and 2.18% on the alpha, and both are zero in expectation. Node A (an ambiguous
observation, f_1 = +9.0%, fund residual +6.4%, probability 0.031): filter (1.020%, 0.945%),
exact posterior (1.000%, 0.400%), the residual being equally consistent with a high alpha and
a small shock or a low alpha and a large one. Node B (a revealing observation, f_1 = +9.8%,
residual +10.4%, probability 0.008): filter (1.022%, 1.309%), exact posterior (1.400%, 2.400%).
Under the Gaussian law with the same moments the filter's numbers are unchanged and are the
exact posterior.

*Table 4, today's decision at review 0.* Myopic (claim 110's rule): fund held at 0.40, ETF
bought from 0 to 0.060, cash 0: the budget binds with cash price eta = 0.174%, the ETF's status
is bought with its marginal g_E = 0.274% = eta + (1 + eta) kappa^+_E, and the fund's marginal is
0.252% = alpha~ + rho g_E - gamma v a with the net alpha alpha~ = mu_A - rho mu_E = 0.448%, the
netting weight rho = Sigma_AE/Sigma_EE = 0.8965 (the ETF residual included) and the residual
variance v = Sigma_AA - Sigma_AE^2/Sigma_EE = 0.00442, below its purchase line
eta + (1 + eta) kappa^+_A = 0.675%. Dynamic (the two-review program
on the tree, a 0.02 grid plus a 0.002 local grid around the myopic action): the same action,
fund 0.40, ETF 0.060, cash 0, value 0.007115 against the myopic policy's 0.007115 (red's exact
joint program over the 72 nodes confirms the same action to 1e-13). At these
inputs the second review's opportunity does not change today's decision: the ETF, at 10 bp, is
the liquidity reservoir, so keeping cash for a review-1 fund purchase is worth less than
holding the exposure now (D16's question, illustrated, not decided).

*Table 5, review-1 decisions from that action.* Node A (the ETF shock +0.5%; with -0.5% the
marked ETF is 0.065): marked holdings fund 0.458, ETF 0.066, cash 0; mu_1 = (1.863%, 0.970%),
target (0.907, -0.212); the manager holds (fund 0.458, ETF idle; the cash price is any value in
[0.17%, 0.30%], since nothing trades and no cash is held): the fund's marginal rose with the
filtered alpha but cash is exhausted and selling the ETF to buy the fund does not pay. Node B:
marked fund 0.477, ETF 0.066, cash 0; mu_1 = (2.229%, 0.972%), target (1.239, -0.508); the
manager sells the ETF to zero and buys the fund to 0.543 (eta = 0.43%). *Would a nonlinear
filter do better here?* A manager using the exact finite-law posterior mean (with the same
Sigma_1) trades identically at both nodes: at A it holds too (its mean is the prior's), and at
B, with alpha at 2.4%, it also sells the ETF to zero and buys the fund to 0.543, because the
purchase is limited by the ETF's sale proceeds, not by the belief; its stage score equals the
filter manager's under the posterior mean (0.00360 at A, 0.01594 at B; these two scores use
the posterior mean with the filter's Sigma_1, whereas Table 6's yardstick uses the posterior
covariance too, under which they are 0.00359 and 0.01608). At these two nodes the budget, not
the filter, decides the review-1 trade.

*Table 6, the exact-posterior manager beside the filter manager on the whole tree (PM's
question: does a nonlinear filter do better, and how does it change the decision).* The
exact-posterior manager uses the finite-law posterior mean and covariance at review 1 (at a
revealing node the covariance is zero; at an ambiguous node the prior's); both managers share
the prior at review 0. Both are scored on the same yardstick, the expected sum of scores with
the review-0 predictive moments and, at review 1, the posterior moments, which are the true
conditional moments under the finite law. Myopic policies: the filter manager's value 0.007589,
the exact-posterior manager's 0.008450, so the nonlinear filter gains 8.6 bp of wealth over the
two quarters. Dynamic policies: both managers choose the same review-0 action (fund 0.40, ETF
0.060, cash 0) and the same values as their myopic policies, so the gain is the same 8.6 bp and
comes entirely from review 1, where the two managers' decisions differ at 42 of the 72 public
nodes (at the 30 others, nodes A and B among them, the binding budget or the band makes them
coincide: at A the exact-posterior manager also holds, at B it also sells the ETF to zero and
buys the fund to 0.543). So at these inputs a nonlinear filter does better by about 4 bp per
quarter, does not change today's decision, and changes the review-1 decision at the nodes
where cash or the ETF's sale proceeds leave room; the lab's manager is the filter one by M8's
definition, and the gain is what that definition costs on this tree (an illustration, rule 22).

**One sentence without model nouns.** One recursion serves both laws: under Gaussian shocks
it is the posterior and its innovations are unpredictable, under a finite law it is the best
linear guess and can be wrong at a history while right on average; the stage decision uses
only the guess's first two moments, so every one-review result holds under either law, the
dynamic results hold on the finite tree with a slack budget, and in the example the cheap
instrument, not cash, is the reserve for tomorrow's opportunity.

## Proof

### 1. Consistency

1a: the blocks decouple because the transformed observation (f, r^A - b_A f, r^E - b_E f + c^E)
has noise (z^f, z^A, z^E) with diagonal covariance and the prior cross-covariance is zero, so
M7's recursion (M5's, written out; its meaning is 2a's) is the displayed pair of scalar
updates, a two-line scalar computation; P_t
depends on (P_0, sigma_f^2, sigma_A^2) only, and the information form is
1/p_{t+1} = 1/p_t + 1/sigma^2 by (1 - k) p = p sigma^2/(p + sigma^2). 1b: Sigma_t = G P_t G' + Sigma_r
with Sigma_r positive definite (sigma_A^2, sigma_E^2 > 0 and the factor term) and G P_t G'
positive semidefinite. 1c: finite law, 1 + r_i > 0 on the support by M8's definition, so
x^+ o (1 + r) >= 0; Gaussian law, P(1 + r_i <= 0) > 0 for a Gaussian r_i, and the stage score is
a quadratic in Gaussian variables with finite expectation. 1d: if x^- <= bar x, u = 0 gives x^+ = x^- >= 0
and h^+ = h^- >= 0; if marking has carried x^-_i above bar x_i, the trade u_i = bar x_i - x^-_i < 0
(and u_j = 0 otherwise) gives x^+ in the box and h^+ = h^- + (1 - kappa^-_i)(x^-_i - bar x_i) > h^- >= 0
since kappa^-_i < 1; so the feasible set is a nonempty compact polyhedron and the stage score strictly concave
(Sigma_t positive definite); on the finite tree the review-1 value is finite at every node and
the review-0 objective is a strictly concave stage score plus a concave continuation (the
review-1 value is concave in the post-trade holdings and cash, as the partial maximum of a
jointly concave function over a convex set parametrized affinely by them), so a maximizer
exists; claims 109 and 110 apply at review 1 by their settings (spanning: b_E > 0).

### 2. The laws

2a: the two meanings are AX-18 and AX-17, with their hypotheses checked in the Statement.
The moment content under the finite law: m_1 = m_0 + K_0 (y_1 - H m_0 - d) with y_1 - H m_0 - d =
H (theta - m_0) + L z_1 of mean zero and covariance H P_0 H' + R, so E epsilon_1 = 0 and
Cov epsilon_1 = K_0 (H P_0 H' + R) K_0' = P_0 H' (H P_0 H' + R)^{-1} H P_0 = P_0 - P_1 = V_0, the
projection identity (the same at t = 1 with P_1). E[theta_hat^B_t] = E theta = m_0 = E m_t by
the tower property and E epsilon = 0. Non-coincidence under the stated condition: an
observation reached from exactly the two hidden branches theta = m_0 +- sqrt(P_0) in a block,
with the same likelihood (the shock law is symmetric and the two branches use shocks of equal
probability), has posterior mean m_0 in that block, while m_1 - m_0 = K_0 (y_1 - H m_0 - d) is
nonzero in that block when the innovation is; the example's node A is such a history, and
red's {-1, +1} example shows the innovation condition cannot be dropped.
2b-2c are readings of the definitions: the stage score is a function of (m_t, P_t) and the
holdings; the continuation is an expectation over the tree.

### 3. Transfers

Each named claim's setting is checked against M8: the one-review claims take an instance
(mu, Sigma, rates, caps, incumbents, budget) with Sigma positive definite and, for spanning,
B^E invertible, which M8 supplies at each review with (mu_t, Sigma_t); claim 110 needs one
ETF and V diagonal (one fund); claim 111 needs Sigma_E = 0 in its explicit parts, which M8
does not impose (sigma_E > 0), so claim 111's parts 1-2 (the residual bound and the
exactness criterion, stated for Sigma_E = 0 in its Setting) transfer only when sigma_E = 0 and
its part 3 likewise; this is recorded in the table by "with the ETF residual off". The dynamic
claims take M6's slack-budget instance in the finite-law variant with M7's Sigma_t, which M8
is when h^-_0 >= 2 (1 + kappa^+) (bar x_A + bar x_E). Claims 030-032 and 036 take M5, which
M8 is not; claim 038's part A transfers what is common by its own statement. The unproved
list is the complement.

### 4. The example

`checks/112/check.py` computes tables 1-5 as described: the filter and predictive moments in
closed form; the 128 hidden branches and 72 public nodes of the finite tree with their
probabilities; the exact posterior by finite Bayes' rule (M3's formula); claim 110's rule at
review 1 (vectorized over incumbents) and at review 0 for the myopic policy; the dynamic
program by enumerating review-0 actions on a grid plus a local grid around the myopic action,
with the review-1 value at every public node from the rule; and the myopic policy's value on
the same tree. It checks positivity of the gross returns, the information form, the innovation
identities of 2a, the existence of a posterior-filter gap and its zero mean, the dynamic value
against the myopic policy's, and the review-1 rule against a grid at every node.

## Checks

`uv run python checks/112/check.py` (exits non-zero on failure; the worked example and a
check, not a proof). It prints tables 1-5 and passes the consistency checks listed in the
proof of part 4. The grids limit the dynamic comparison to 0.002 in the holdings; the review-1
solutions are exact to the rule's bisection (50 steps).

## Not shown

- The Gaussian law's dynamic problem: existence, regularity and the band results (1c, part 3),
  and review-1 feasibility off the event {x^-_1 >= 0} (1d; a negative marked holding with no
  cash), where the one-review claims do not apply either.
- The exact-posterior manager's policy in general (Table 6 computes it on the example's tree
  only); under the Gaussian law the two managers coincide.
- The exposure-first policy's definition when marking carries a fund above its cap (claim 111's
  incumbent-aware first stage freezes the fund at min(x^-_i, bar x_i) with the forced sale
  charged, PM's convention from experiment 048, recorded in claim 111's Not shown); the example
  does not run that policy.
- A binding budget's dynamic theory (D16): the example's finding that the myopic policy is
  dynamically optimal at its inputs is an illustration (rule 22), not a condition.
- Claim 111's explicit parts with sigma_E > 0 (its Not shown); the example's exposure-first
  policy is therefore not run (D18's experiment runs it where defined).
- The exact-posterior manager under the finite law; the finite law's higher moments in the
  continuation (2c).
- Calibration: the inputs are assumed round numbers in the ranges the analyst's experiments
  035 and 041 use; the example decides nothing.

## Prior art

Mechanism: a linear recursion for the mean and covariance of an unknown parameter is the
posterior when the noise is Gaussian and the best linear predictor otherwise, with the same
unconditional innovation moments; a decision rule that uses only the first two predictive
moments therefore behaves identically under the two laws review by review, while a dynamic
rule evaluated on a finite tree can depend on the tree beyond those moments.

General results checked: AX-17 (`uhlmann2022gaussianity`, full text; ROADMAP D17's Known):
the Kalman recursion is the minimum-mean-squared-error affine predictor for any finite-moment
noise and the exact posterior under Gaussian noise (sufficiency only, as the audited entry
states; the converse fails in general), 2a's general half; AX-18
(`murphy2007conjugate`): the exact conjugate Gaussian posterior for a static mean, 2a's
Gaussian half, which AX-10's steady-state Theorem 2.1 does not cover for the transient
fixed-means filter (red's review: (1, 0) is not stabilizable); both cited with their
hypotheses checked, and the innovation-moment identities of 2a are a two-line computation
from the definitions.
Claim 030 (formalized): M5's exogenous learning and the target's split; claim 038 (formalized):
the bridge between M5 and M7, whose part A and part D this claim's part 3 applies to M8;
claims 029 and 100 (formalized): the dynamic band on the finite tree; claims 109-111
(approved): the review problems of M8 and its three policies; M3 (model/SPEC.md): the finite
Bayes rule and the positive-gross-return device. `brennan1998role` and `pastor2002investing`
(registered): Bayesian learning about premia and alphas with Gaussian conjugate priors, the
setting in which the filter is the posterior. No web search. This is a claim because the
request asks that the four elements be shown to belong to one model and that the two laws be
resolved explicitly, which no model section or claim did.

## Open objections

none

## Review

**Red, 2026-09-29** (on c1e281a6; the promoted branch 1c85c8b6 differs only in depends_on). Red-passed, with five required corrections: two scope fixes (1d and part 3 under the Gaussian law; 2a's general non-coincidence), one citation (rule 21), and two in the worked example. Red re-derived parts 1-3 by hand and recomputed part 4 with its own script, written without reading checks/112. The script is numpy plus cvxpy/CLARABEL, and it solves the dynamic problem *exactly*, as the lifted joint concave program over all 72 public nodes, not on a grid.

**The finite-law supports** are not stated in the claim or in M8 (M8 fixes only theta's two points). Red inferred them from the claim's numbers:
- z^f in {+-7.6, +-8.4}% (sd 8.010%);
- z^A in {+-4, +-8}% (sd 6.325%);
- z^E in {+-0.5}%, **two** points, not four;
- all equiprobable.

These give exactly 128 hidden branches and 72 public nodes (6 x 6 x 2), and every number below.

**Part 4, reproduced:**
- *Table 2* matches: P_0, the gains 0.0025 and 0.0909, P_1 = (1.596e-5, 3.636e-4), mu_0 = (1.30%, 0.95%), Sigma_0, and the target (0.406, 0.225). The information form holds to 4e-12.
- *Table 3* matches.
  - 72 nodes; the largest posterior-filter gaps are 0.418% (premium) and 2.182% (alpha), with a mean gap of 0 (2e-19).
  - Node A: probability 0.0312 per ETF shock, filter (1.020%, 0.945%), posterior (1.000%, 0.400%). Node B: 0.0078, filter (1.022%, 1.309%), posterior (1.400%, 2.400%).
  - 2a's innovation identities hold on the tree: mean 0, covariance (3.980e-8, 3.636e-5) = V_0, cross-moment 0.
- *Table 4* matches.
  - Myopic: fund held at 0.40, ETF bought to 0.0599, cash 9e-14, eta = 0.1742%. The ETF's line is g_E = 0.2744% = eta + (1 + eta) kappa^+_E. The fund's marginal is 0.2523%, below its purchase line 0.675%.
  - The exact dynamic optimum is the same action to 1e-13, with the same value, 0.0071149 (difference 7e-16). This is stronger than the claim's grid comparison.
- *Table 5*, node B matches: the ETF is sold to zero, the fund bought to 0.542-0.543, eta = 0.43%.

**Part 1** is right under the finite law: 1a's information form, 1b's positive definiteness (also with sigma_E = 0, where det = b_E^2 s (sigma_A^2 + p^alpha) > 0), 1c's positivity (minimum gross return 0.834 on the tree), and 1d's backward induction. **Part 3**'s slack-budget condition h^-_0 >= 2 (1 + kappa^+)(bar x_A + bar x_E) is right by hand: at most one purchase from zero to the caps at each review.

**Required correction 1 (1d and part 3 under the Gaussian law).** 1d's first sentence ("at every history and holdings, no trade is feasible ... the feasible set is nonempty") is unqualified, but its proof ("within the caps by induction") uses the finite law.
- Under the Gaussian law, 1 + r_A < 0 with positive probability (1c), so the marked fund holding a^-_1 is negative, and x = x^- is not in the box.
- Reaching x_A >= 0 costs (1 + kappa^+_A)|a^-_1| in cash. With h^+_0 = 0 (the example's own review-0 action) and the ETF's marked value too small (a large negative f drives 1 + r_E down too), review 1's feasible set is empty.
- Likewise, part 3's "one-review results, either law, every review" fails at review 1 under the Gaussian law off the event {x^-_1 >= 0}. The one-review claims' settings take nonnegative incumbents.
- Please restrict 1d's feasibility and part 3's review-1 transfer under the Gaussian law to that event (or to review 0), and list the rest under Not shown next to 1c.

**Required correction 2 (2a's general non-coincidence).** "theta_hat^B_t != m_t at some histories whenever the finite prior has more than one point and the observation does not reveal theta" is false.
- Counterexample: theta in {-1, +1} and noise z in {-1, +1}, independent and equiprobable, y = theta + z. The filter has k = 1/2, so m_1 = y/2, and the exact posterior mean is +1, 0, -1 at y = 2, 0, -2: the same at every history. y = 0 does not reveal theta.
- The proof's mechanism needs the ambiguous observation to have a *nonzero innovation*, and here it has none.
- Please state the sufficient condition the proof uses (an observation reached from two hidden branches, with posterior mean the prior mean, and a nonzero filter innovation), or keep only the example's instance (node A).

**Required correction 3 (rule 21: the filter's two meanings are cited, not re-derived).**
- *Gaussian half.* AX-10's Theorem 2.1 is the steady-state filter under stabilizability of (A, Sigma_x). With fixed means, A = 1 and Sigma_x = 0, so (1, 0) is not stabilizable and the claim's transient P_t is not a steady state. AX-10's audit line also says the finite-horizon recursion is not covered. So AX-10 does not give "the filter is the exact posterior at t = 1".
- *Finite-law half.* The Proof re-derives the best-linear-predictor property inline ("no ledger entry"). ROADMAP's D17 Known lists `uhlmann2022gaussianity` to cite for exactly this distinction, and NOTICES (2026-09-29) records it.
- Please cite a ledger entry for each half: request one from the librarian for Uhlmann-Julier, and for the conjugate scalar Gaussian update or its finite-horizon filter form. Otherwise, move the statement to Not shown.

**Required correction 4 (Table 1: state the supports).** The example cannot be reproduced from the text. Please give the three shock supports (red's inference above, if that is what checks/112 uses) and correct "four equiprobable points per shock": the ETF's shock has two, which is what 128 hidden branches requires.

**Required correction 5 (Table 4's fund-marginal display).** "0.4% + 0.9 m - gamma v a = 0.25%" does not reproduce.
- With the stated numbers (m = 0.275%, v = sigma_A^2 + p^alpha = 0.0044, a = 0.40), it gives 0.2075%.
- The correct decomposition (claim 110's) uses the net alpha alpha~ = mu_A - rho mu_E = 0.448%, the netting weight rho = Sigma_AE/Sigma_EE = 0.8965, and the residual variance v = Sigma_AA - Sigma_AE^2/Sigma_EE = 0.00442: 0.448% + 0.8965 x 0.2744% - 2.5 x 0.00442 x 0.40 = 0.2523%.
- The writer will copy this line, so please use these quantities.

**Nits.**
- Node A's review-1 cash price is not unique. The manager neither trades nor holds cash there, so any eta in [0.172%, 0.302%] satisfies both held lines. 0.17% is that interval's lower end, the same non-uniqueness as claim 044's correction 1.
- Table 5's marked ETF at node A is 0.065 or 0.066, depending on the ETF shock, which the node does not fix.
- m = 0.2744% rounds to 0.274%, not 0.275%.
- 2c's "two finite laws with the same moments can give different dynamic policies" is an existence statement with no instance. Please give one, or say "may".

**For PM (scope, not the verdict).** ROADMAP's D17 entry says the example "must still say, for its own finite law, whether a nonlinear filter would do better, and how that affects the decision". The claim puts the exact-posterior manager under Not shown, and says only that at node B the posterior "would move it further".

**Mechanism.** One recursion, two meanings: the Gaussian posterior, or the finite law's best linear predictor with the same unconditional innovation moments. The stage score uses only the first two moments, so the review-by-review results are law-free, while the continuation is an expectation over the tree. In the example the 10 bp ETF is the liquidity reservoir, and myopic is exactly dynamically optimal at these inputs (an illustration, rule 22).

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's five required corrections (Gaussian-law feasibility at review 1; 2a's non-coincidence condition; rule 21 citations for the filter's two meanings; the shock supports; Table 4's decomposition), and PM's scope point: D17 asks whether a nonlinear filter does better in the example, so the exact-posterior manager's decisions and value on the tree are computed beside the filter's. Mathb revises, and red records a fresh verdict.

**Red, recheck of the revision (dacfb963, with ff56a529's Table 6), 2026-09-29.** Red-passed, with one required correction that red missed in both passes (lean's point, below). All five earlier required corrections and the nits are made, and red checked each against the revised text.
- **1d and part 3.** The Gaussian-law review-1 statements are restricted to {x^-_1 >= 0}, and the rest is under Not shown.
- **2a's non-coincidence condition** is right. The two hidden branches theta = m_0 +- sqrt(P_0) in a block have equal likelihood (symmetric, equiprobable shocks), and the blocks are independent (zero prior cross-covariance, independent noises), so that block's posterior mean is m_0. The filter moves when the innovation is nonzero. Red's {-1, +1} example is cited for why that condition is needed.
- **Rule 21.** AX-17 and AX-18 are audited ok on main. AX-18's hypotheses (a static mean, a Gaussian prior, conditionally independent Gaussian observations with known variance) hold block by block, with n = 1, for M8's lambda + z^f and alpha + z^A. AX-17's finite-moment hypotheses hold for M8's finite law. AX-10 is no longer cited for the transient filter.
- **Table 1's supports** are exactly the ones red inferred.
- **Table 4's decomposition** matches red's numbers: 0.448%, 0.8965, 0.00442, g_E = 0.274%, fund 0.252%.
- **Nits.** Node A's cash price is now the interval [0.17%, 0.30%], and 2c says "may".

**Table 6 (new), reproduced with red's own script.** The script extends red's claim 112 tree with finite-law posterior means and covariances per node (covariance zero in a revealed block, the prior's in an ambiguous one). It solves both managers' myopic and dynamic policies (the dynamic ones as exact joint programs over the 72 nodes) and scores both on the claim's yardstick: the review-0 prior predictive moments, and the posterior moments at review 1.
- Values: filter manager 0.007589, exact-posterior manager 0.008450, a gain of 8.61 bp, the same under the myopic and the dynamic policies.
- Both managers take the same review-0 action (0.40, 0.0599).
- Review-1 decisions differ at 42 of 72 public nodes (probability 0.469).
- At nodes A and B both managers hold (0.458, 0.066), or sell the ETF to zero and buy the fund to 0.543.
- Every number matches the claim.

**Required correction (1d; lean's scoping note, which red missed).** "Under the finite law, at every history and holdings, no trade is feasible" is false.
- Marking can carry a holding above its cap (x^-_1 = x^+_0 o (1 + r_1) with 1 + r > 1 near bar x), and then u = 0 violates the post-trade cap.
- The Proof's own argument (a holding above its cap is sold down to it, which raises cash) gives the right statement: the feasible set is nonempty, containing either no trade or a sale down to the cap.
- Please state 1d that way. The example's holdings stay far below their caps of 1, so no number in part 4 changes.

**Nits (not required).**
- Table 5 describes the exact-posterior manager "with the same Sigma_1", while Table 6 gives it the posterior covariance. At nodes A and B the decisions coincide either way, but please use Table 6's definition in both.
- "Does better by about 4 bp per quarter" averages a gain that Table 6 attributes entirely to review 1. "8.6 bp, all at review 1" is exact.

Verdict: red-passed

Verdict: withdrawn (PM, 2026-09-29): red's recheck leaves one required correction, 1d's feasibility statement: a marked holding above its cap makes no trade infeasible, so the feasible set is nonempty through a funded sale to the cap. PM's note also adds 044 to depends_on for lean's formal 1d. Mathb revises, and red records a line.

**Red, recheck of 1d (as merged in bb34a3f3; Statement and Proof identical to mathb's cb2781e0), 2026-09-29.** The required correction is made. 1d now says the feasible set is nonempty and compact: no trade is feasible within the caps, and if marking carries x^-_i above bar x_i, the sale u_i = bar x_i - x^-_i puts the holding in the box and raises cash by (1 - kappa^-_i)(x^-_i - bar x_i) > 0, since kappa^-_i < 1. That is right by hand, and so is the existence step through claim 044's part 1 (now in depends_on). Table 5's added scores reproduce on red's tree: 0.00360 and 0.01594 with the filter's Sigma_1, 0.00359 and 0.01608 with the posterior covariance. No result changed.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's reviews are sound: parts 1-3 re-derived by hand and part 4 recomputed with red's own exact joint program over the 72 public nodes (Tables 2-6 to their digits, the myopic policy exactly dynamically optimal at the example, the exact-posterior manager's 8.61 bp gain from review 1 alone, decisions differing at 42 of 72 nodes); all six required corrections made (Gaussian-law review-1 statements restricted to nonnegative marked holdings; 2a's non-coincidence condition; the filter's two meanings cited through AX-17 and AX-18, hypotheses checked; the shock supports; Table 4's decomposition; 1d's feasible set nonempty via a funded sale to the cap), plus PM's scope point (Table 6); experiment 050 reproduces it independently. Mechanism: one recursion with two meanings (AX-17, AX-18), a stage score using only the first two moments, an application; new: the example that connects learning, predictive risk, marking and the budget, with the value of the nonlinear filter computed. Limits: one example (rule 22); the exact-posterior policy in general is Not shown.


mathb, 2026-09-29 (red's review, five required corrections and nits): 1d and part 3 restrict
the Gaussian law's review-1 statements to {x^-_1 >= 0}; 2a states the sufficient condition for
the posterior-filter gap (two hidden branches, nonzero innovation) with red's counterexample;
the filter's two meanings are cited through ledger entries requested from the librarian and
are Not shown until audited, AX-10 no longer being cited for the transient filter; Table 1
states the three shock supports (the ETF's has two points); Table 4's fund marginal uses
alpha~ = 0.448%, rho = 0.8965, v = 0.00442 and g_E = 0.274%; node A's cash price is an
interval, its marked ETF depends on the ETF shock, 2c says "may", and Table 5 answers the
nonlinear-filter question at the two nodes (the budget decides). No result changed.

mathb, 2026-09-29 (the librarian's AX-17 and AX-18, audited ok on main): 2a's two meanings are
now cited through AX-18 (the conjugate Gaussian posterior, block by block with n = 1) and AX-17
(the best linear predictor for any finite-moment law; the posterior only under Gaussian noise),
with their hypotheses checked; the Not shown bullet that held them pending is removed and both
entries are in axioms_used. No result changed.

mathb, 2026-09-29 (PM's corrections note, item 6): Table 6 computes the exact-posterior manager's
myopic and dynamic policies and values beside the filter manager's on the example's tree, on
the posterior-moment yardstick: the same review-0 action, a gain of 8.6 bp over two quarters
from review 1 alone, decisions differing at 42 of 72 public nodes and coinciding at nodes A
and B. The exposure-first cap convention from experiment 048 is recorded in Not shown.

mathb, 2026-09-29 (the analyst's experiment 050 note): experiment 050 reproduces every entry of
Tables 2-6 independently (the harness extended to M8's observation, checks/112 unread), with
node A's cash-price interval [0.171%, 0.301%] and the 8.61 bp gain; Table 5 now says its two
stage scores use the filter's Sigma_1 while Table 6 uses the posterior covariance, with both
values given. No result changed.

mathb, 2026-09-29 (PM's note; lean's 1d point): 1d said "no trade is feasible at every history",
which fails when marking carries a holding above its cap; it now says the feasible set is
nonempty because the sale down to the cap is funded (a sale raises cash), with the proof
written out, and the two-review existence is claim 044's part 1 on M8's tree, so 044 is added
to depends_on (lean's formal 1d instantiates it, Q-04). No result changed.

mathb, 2026-09-29 (the auditor's FIDELITY wording point): 2a and Prior art cited AX-17 as
"the exact posterior only under Gaussian noise"; the audited entry states sufficiency only,
so the wording is now "under Gaussian noise, not in general otherwise". No result changed.

Not machine checked. Parts 1-2 are finite computations and two-line projection identities;
part 3 is a table of settings; part 4 is a deterministic script.

Lean, 2026-09-29 (final): parts 1a-1d under the finite law, 2a's moment content, part 3's slack-budget
threshold and part 4's Table 2 are machine checked, within PM's scope. The statement is in
`lean/Standalone/M8WorkedLearningExample.lean` and the proof in
`lean/Novel/M8WorkedLearningExampleProof.lean`.
- Model: M8's own coordinates.
  - The filter is scalar by block (gain, posterior variance, update).
  - The predictive moments mu_t and Sigma_t are M8's formulas.
  - A block's finite law is any finite prior and centred finite noise with the stated moments.
  - M8's finite tree is mapped into claim 044's two-review coordinates (`toTwo`): the review-1
    nodes are the states, the gross returns do the marking, and the moments are the filter's.
- Imports: claim 044's statement and proof (Q-04; 044 in depends_on). The two-review existence
  instantiates claim 044's part 1 (option (i), PM).
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/112/check.py` pass.

Machine checked:
- 1a: the posterior variance is positive and satisfies 1/p_1 = 1/p_0 + 1/sigma^2.
- 1b:
  - Sigma_t is symmetric and positive definite for nonnegative belief variances and sigma_f^2,
    with sigma_A^2, sigma_E^2 > 0;
  - gamma Sigma_t x = mu_t has exactly one solution (the target).
- 1c: marking with positive gross returns keeps holdings nonnegative.
- 1d, under the finite law:
  - a review's feasible set is nonempty from any nonnegative marked holdings (above a cap too) and
    nonnegative cash;
  - with Sigma positive definite, the review problem has exactly one optimum;
  - M8's tree meets claim 044's hypotheses with h^-_0 > 0, so an optimal policy exists and the root
    problem with beta E V_1 is concave on the root polyhedron;
  - Sigma_0 and Sigma_1 are positive definite.
- 2a, for any finite laws with the stated moments:
  - the innovation has mean zero and variance p_t - p_{t+1} at t = 0 and t = 1;
  - the error theta - m_1 has variance p_1;
  - the cross-block moment is zero;
  - the exact posterior mean averages to m_0 (finite Bayes);
  - the non-coincidence condition: two equally weighted branches m_0 +- d reached with equal
    likelihood give posterior mean m_0, while the filter moves when the innovation is nonzero;
  - red's {-1, +1} counterexample, exactly;
  - node A's alpha block, exactly: posterior 0.4%, gain 1/11, filter 0.4% + 6%/11.
- Part 3: with h^-_0 >= 2(1 + kappa) sum_i bar x_i and every purchase rate at most kappa, both budgets
  hold at every pair of in-box holdings.
- Part 4, Table 2 exactly: the gains 1/402 and 1/11, P_1, mu_0 and Sigma_0, and the target
  within 5e-4 of (0.406, 0.225).

Paper-level (PM):
- 1d with h^-_0 = 0;
- 2a's two meanings, cited through AX-17 and AX-18 (rule 21);
- 2b-2c and part 3's transfer table;
- the Gaussian-law statements;
- Tables 3-6 and the Checks.

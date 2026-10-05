---
id: 50
title: "Independent check of D17's worked example (claim 112, part 4): Tables 2-6 on the M8 harness, including the exact-posterior manager beside the filter manager on the whole tree"
status: reproduced
model_version: M8
direction: D17
claims: [110, 112]
code: experiments/050/
---
## Question
**Job: verify behaviour under a theorem's assumptions** (proposal section 6; AGENTS.md rule 22). This is an
independent reproduction of a worked example; its numbers are illustrations.

Routing:
- **Source:** PM's note 2026-09-29-exp050-claim112, item 1 (D17 first).
- **Claim state:** claim 112 is proposed and in re-review, on main at dacfb963 (Table 1 now states the shock
  supports; Table 6 was added at ff56a529). That Statement is checked, and later changes are recorded under
  Deviations. The claims field lists 112.
- **Independence:** per PM, checks/112/check.py is not read before the results are recorded. The harness
  (experiments/d16-harness) is the solver.

- **Every input is an assumption.**
- **The claim's numbers are the result.**

Do part 4's Tables 2-6 reproduce at Table 1's inputs, on an independent solver?
- **Table 2:** P_0, the gains, P_1, mu_0, Sigma_0 and the target x*_0.
- **Table 3:** 72 public nodes; the largest filter-against-exact-posterior gaps (0.42% on the premium, 2.18% on the
  alpha), zero in expectation; node A's and node B's filter and posterior means.
- **Table 4:**
  - the myopic root action (fund 0.40, ETF 0.060, cash 0), eta = 0.174%, g_E = 0.274%;
  - the fund's marginal 0.252%, alpha~ = 0.448%, rho = 0.8965, v = 0.00442, the purchase line 0.675%;
  - the dynamic program's action (the same) and value 0.007115 against myopic's 0.007115.
- **Table 5:**
  - node A: marked (0.458, 0.066), cash 0, mu_1 = (1.863%, 0.970%), target (0.907, -0.212), holds, with the cash
    price any value in [0.17%, 0.30%];
  - node B: marked (0.477, 0.066), mu_1 = (2.229%, 0.972%), target (1.239, -0.508), sells the ETF to zero and
    buys the fund to 0.543, eta = 0.43%;
  - the exact-posterior manager trades identically at A and B, with stage scores 0.00360 and 0.01594.
- **Table 6:**
  - on the yardstick (review-0 predictive moments; at review 1 the exact posterior moments), the myopic values are
    0.007589 (filter manager) and 0.008450 (exact-posterior manager), a gain of 8.6 bp;
  - the dynamic policies take the same review-0 action and have the same values;
  - the review-1 decisions differ at 42 of the 72 nodes.

**What counts against the claim:** any table entry off beyond its last printed digit (after rounding); the value
difference off by more than 0.1 bp; a decision at node A or B off by more than 1e-3; the count of differing nodes off.
Disagreements go to mathb and red.

## Design
### Solver: the D16/D18 harness, extended to M8's observation (a preparation change, recorded here)
- **M8's observation.** M8's manager observes y = (f, r^A, r^E), the factor return included. The harness observed
  only the two instruments' returns, which carries the same information only when sigma_E = 0. Table 1 has
  sigma_E = 0.5%, so the harness gains an M8 observation mode:
  - public nodes keyed by (f, r^A, r^E);
  - the linear filter with H = [[1, 0], [b_A, 1], [b_E, 0]], d = (0, 0, -c^E), and R the covariance of (z^f, b_A z^f
    + z^A, b_E z^f + z^E).
  This is the best linear predictor given M8's observation. It equals M8's scalar filter, because (f, r^A - b_A f,
  r^E - b_E f + c^E) is a linear bijection of the observation and the last coordinate carries no information about
  theta.
- **Checks of the mode.** Before any Table 1 number is read, the mode is checked against M8's scalar formulas on
  every node of a test tree, and against the two-return mode at sigma_E = 0.
- **The exact posterior.** Finite Bayes' rule over theta's atoms at each public node gives the posterior mean and
  covariance. The exact-posterior manager's review-1 moments are mu = G theta_hat^B + d and Sigma = G P^B G' + R.
- **The policies:**
  - myopic: the one-review program at each review;
  - dynamic: the harness's exact tree program. For the exact-posterior manager, its own review-1 moments enter its
    program.
- **The yardstick (Table 6):** review-0 predictive moments and, at review 1, the exact posterior moments. Both
  managers' policies are scored on it.
- **Multipliers.** The cash prices come from the budget duals. Node A's interval is read from experiment 047's LP:
  the minimum and maximum eta_1 over the admissible set at node A.

### Inputs (Table 1, as stated)
- b_A = 0.9, b_E = 1, c^E = 5 bp; lambda in {0.6%, 1.4%}, alpha in {-1.6%, 2.4%};
- factor shock in {-8.4, -7.6, +7.6, +8.4}%, fund residual in {-8, -4, +4, +8}%, ETF residual in {-0.5, +0.5}%, all
  equiprobable and independent;
- gamma = 2.5, beta = 1; fund 50 bp, ETF 10 bp each way; caps 1;
- incumbents: fund 0.40, ETF 0, cash 0.06.
- **Node A:** f_1 = +9.0%, fund residual +6.4%, ETF residual +0.5%. **Node B:** f_1 = +9.8%, fund residual
  +10.4%, ETF residual +0.5%.

**Output.** experiments/050/run.py and summary.json, with a table of the claim's value beside the harness's value for
every entry. The result goes to mathb, red and PM.

## Deviations
1. **Table 5's stage-score convention** (recorded before reporting). The registration scored Table 5's
   exact-posterior manager with the exact posterior's mean and covariance, Table 6's yardstick. That gives 0.00359
   at A and 0.01608 at B, against the claim's 0.00360 and 0.01594. Table 5's text says "the exact finite-law
   posterior mean (with the same Sigma_1)". Under that convention, the posterior mean with the filter's Sigma_1, the
   scores are 0.003597 and 0.015941, which reproduce the claim's numbers. The decisions are identical under both
   conventions. Both are reported, and the claim's is the one compared. Table 6 uses the posterior covariance, as its
   text says, and reproduces as registered.
2. **Harness hooks.** The harness gained M8's observation mode, a record of the parameter atoms reaching each node
   (for the exact posterior), and an optional moments function (each manager's own review-1 moments).
   - The default mode's validation reproduces identically.
   - The M8 mode was checked before any Table 1 number was read. On a test tree it matches M8's scalar filter to
     3e-18 (means) and 5e-21 (P_1). At sigma_E = 0 it matches the two-return mode, in values to 2e-18 and in holdings
     to 2e-15.

## Results
**Command:** `uv run python experiments/050/run.py` (seconds).
- **Independence.** checks/112 was not read.
- **Assumptions.** Every input is Table 1's and assumed (rule 22).
- **Statement.** Claim 112 at dacfb963.

**Verdict: every entry of part 4's Tables 2-6 reproduces to its printed digits,** Table 5's stage scores under the
claim's stated convention (Deviation 1). **The nonlinear filter's gain is 8.61 bp; the claim states 8.6.**

| table | entry | claim | harness |
|---|---|---|---|
| 2 | P_0; gains k^lambda, k^alpha; P_1 | diag(1.6e-5, 4.0e-4); 0.0025, 0.0909; diag(1.596e-5, 3.636e-4) | the same (k^lambda = 0.00249) |
| 2 | mu_0; Sigma_0; x*_0 | (1.30%, 0.95%); [[0.00961, 0.00579], [., 0.00646]]; (0.406, 0.225) | (1.300%, 0.950%); [[0.009610, 0.005789], [., 0.006457]]; (0.4057, 0.2248) |
| 3 | public nodes; largest gaps (premium, alpha); expected gap | 72; 0.42%, 2.18%; 0 | 72; 0.418%, 2.182%; 4e-19 |
| 3 | node A: probability; filter; exact | 0.031; (1.020%, 0.945%); (1.000%, 0.400%) | 0.031 (0.0625 over both ETF shocks); (1.020%, 0.945%); (1.000%, 0.400%) |
| 3 | node B: probability; filter; exact | 0.008; (1.022%, 1.309%); (1.400%, 2.400%) | 0.0078; (1.022%, 1.309%); (1.400%, 2.400%) |
| 4 | myopic root; cash; eta; g_E | fund 0.40, ETF 0.060; 0; 0.174%; 0.274% | 0.400, 0.0599; 2e-11; 0.1742%; 0.2744% |
| 4 | fund marginal; alpha~; rho; v; purchase line | 0.252%; 0.448%; 0.8965; 0.00442; 0.675% | 0.2523%; 0.4483%; 0.89652; 0.004420; 0.6751% |
| 4 | dynamic root; values (dynamic, myopic) | the same action; 0.007115, 0.007115 | (0.400, 0.0599); 0.0071149, 0.0071149 |
| 5 | node A: marked; mu_1; target; decision; cash price | (0.458, 0.066); (1.863%, 0.970%); (0.907, -0.212); holds; any in [0.17%, 0.30%] | (0.458, 0.0656); (1.863%, 0.970%); (0.907, -0.212); holds; [0.171%, 0.301%] |
| 5 | node B: marked; mu_1; target; decision; eta | (0.477, 0.066); (2.229%, 0.972%); (1.239, -0.508); ETF to 0, fund to 0.543; 0.43% | (0.477, 0.0661); (2.229%, 0.972%); (1.239, -0.508); ETF to 0, fund to 0.5426; 0.428% |
| 5 | exact-posterior manager at A and B; stage scores | trades identically; 0.00360, 0.01594 | identical; 0.003597, 0.015941 (Deviation 1) |
| 6 | myopic values (filter, exact posterior); gain | 0.007589, 0.008450; 8.6 bp | 0.0075887, 0.0084499; 8.61 bp |
| 6 | dynamic: review-0 action; values; gain | the same action; the same values; 8.6 bp | (0.400, 0.0599) for both managers; 0.0075887, 0.0084499; 8.61 bp |
| 6 | review-1 nodes where the managers differ | 42 of 72 | 42 of 72 (dynamic and myopic alike) |

**Limits.**
- One worked example, at assumed inputs.
- The numbers illustrate the claim's parts 1-3; they are not evidence for them.

## Review

**Red, 2026-09-29.** Reproduced. Red's own scripts were written for its claim 112 reviews, without the harness or checks/112. They compute the tree from Table 1's supports, the filter and the exact posterior by finite Bayes' rule, and claim 110's policies as cvxpy/CLARABEL one-review programs, and they solve the dynamic policies as exact lifted joint programs over the 72 nodes.
- `experiments/050/red_reproduce.py` covers Tables 2-5; run it from experiments/050, in seconds.
- `experiments/050/red_table6.py` covers Table 5's scores and Table 6; also seconds.

Every entry of the report's table matches red's independent numbers:
- **Table 2:** gains 0.0025 and 0.0909; P_1 = (1.5960e-5, 3.6364e-4); mu_0 = (1.30%, 0.95%); Sigma_0 as reported; target (0.406, 0.225).
- **Table 3:** 72 nodes and 128 branches; largest gaps 0.4179% and 2.1818%; mean gap 2e-19; node A (0.0312 per ETF shock, filter (1.020%, 0.945%), posterior (1.000%, 0.400%)) and node B.
- **Table 4:** myopic root (0.400, 0.0599), cash 9e-14, eta 0.1742%, g_E 0.2744%, fund marginal 0.2523%, alpha~ 0.4483%, rho 0.8965, v 0.00442, purchase line 0.6751%. Dynamic = myopic, with value 0.0071149 both, to 7e-16.
- **Table 5:** node A holds, with a cash price in [0.1714%, 0.3015%] at the ETF shock +0.5% (the report's [0.171%, 0.301%]). Node B sells the ETF to zero and buys the fund to 0.5426, eta 0.428%.
- **Table 6:** 0.007589 against 0.008450, a gain of 8.61 bp, with the same review-0 action (0.400, 0.0599) for both managers, myopic and dynamic alike. The managers' decisions differ at 42 of 72 nodes, and coincide at A and B.

**Deviation 1** is honest and correct. Red's scores are 0.003597 and 0.015941 with the posterior mean and the filter's Sigma_1 (the claim's printed convention), and 0.003588 and 0.016079 with the posterior covariance. Claim 112 now states both.

**Deviation 2:** the harness hooks are not examined. Red's code shares none of them and agrees everywhere.

Verdict: reproduced

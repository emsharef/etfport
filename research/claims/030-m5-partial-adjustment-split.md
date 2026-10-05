---
id: 30
title: "M5's optimal quarterly policy is partial adjustment toward an aim from a learning-driven Riccati recursion, the aim is the current Markowitz portfolio re-weighted by the shrinking future risk charge, and in exposure-and-fund coordinates the problem separates exactly into a myopic ETF exposure rule and a fund alpha rule with ETFs netting the funds' factor by-product, up to three explicit bundling terms (ETF cost, ETF residual risk, ETF fees)"
status: formalized
model_version: M5
depends_on: []
axioms_used: [AX-10]
formal: lean/Standalone/M5PartialAdjustmentSplit.lean
direction: D12
---
## Statement

D12's first claim. It states M5's dynamic problem as a linear-quadratic problem with an
exogenous learning state, gives the explicit policy in the two forms the analyst's exact
reference (experiment 021) compares against, and proves what the fund-of-funds structure adds:
an exact change of coordinates that separates exposure from alpha, the separated policy, and
the three bundling terms that couple them. The linear-quadratic solution is known in kind
(`garleanu2009dynamic` Propositions 1-3 for stationary predictors and constant risk; ledger
entry `AX-10`, `abeille2016lqg` Assumption 1 and Theorems 2.1-2.2, for the separation principle
and the stationary Riccati form). AX-10 is audited for the stationary, undiscounted, average-cost
statement with a positive definite cost matrix only; no step of the proof rests on it (part 2's
separation follows from the policy-independence of the covariance recursion, and part 3 is a
direct backward induction), and it is listed as the rule-21 citation of the known stationary
theory this recursion specializes, for context, at PM's instruction; lean's formalization does
not use it. Its
positive-definiteness hypothesis holds in M5's reference case (Lambda positive definite and
gamma Sigma_t positive definite, so the stage cost matrix diag(gamma Sigma_t, Lambda) is
positive definite; where part 4 switches ETF costs off, Lambda is only semidefinite and AX-10
is not invoked). The finite-horizon, discounted, time-varying recursion that learning produces
is not covered by AX-10 and is proved in part 3 by backward induction on a quadratic value
function, as rule 21 asks. Promoted from provisional/math-m5-policy on 2026-09-28 after AX-10
merged.

**Setting.** M5 (model/SPEC.md) with a finite horizon of T >= 1 reviews t = 0, ..., T-1 and no
terminal value; the baseline state process (Phi = I, Q = 0: fixed unknown premia and alphas);
gamma > 0, rho in (0, 1], Lambda symmetric positive semidefinite (positive definite in M5;
the semidefinite case is used in part 4 to switch ETF costs off). Positions x_t in R^n are
post-trade at review t, x_{-1} given, u_t = x_t - x_{t-1}. Beliefs (m_t, P_t) follow M5's Kalman
filter; write m_t = (lambda_hat_t, alpha_hat_t). With G = [[B^A, I_N]; [B^E, 0]] and
e_E c^E := (0_N, c^E),

```
mu_t = G m_t - e_E c^E,     Sigma_t = G P_t G' + Sigma_r,     Markowitz_t = (gamma Sigma_t)^{-1} mu_t,
```

Sigma_r the return covariance of M5 (Sigma_z propagated through the loadings). The *reference
case* is M5's: Sigma_z block diagonal, Sigma_A diagonal, prior cross-covariance zero. Because
returns load on the realized factor f = lambda + z^f, the observation y_{t+1} = (f, r^A,
r^E)_{t+1} equals H theta_t + d + L z_{t+1} with L = [[I_K, 0, 0]; [B^A, I_N, 0]; [B^E, 0,
I_M]], so its noise covariance is L Sigma_z L',
as M5's corrected display says (erratum merged 2026-09-28; the transformed observation
(f, r^A - B^A f, r^E - B^E f + c^E) has noise exactly z_{t+1}).

1. **Exogenous learning.** For every policy, P_t is the same deterministic sequence, given by
   the Kalman covariance recursion with no dependence on positions or trades; m_t is a
   martingale with respect to I_t under the manager's belief, E_t m_{t+1} = m_t, with a
   deterministic innovation covariance; and Sigma_t is deterministic and positive definite.
   In the reference case the filter decouples: P_t = diag(P^lambda_t, P^alpha_t) for all t,
   the premium block updated by the factor returns alone and the alpha block by the funds'
   residual returns r^A - B^A f alone, and

   ```
   Sigma_t = B (Sigma_f + P^lambda_t) B' + diag(Sigma_A + P^alpha_t, Sigma_E).
   ```

2. **The problem is linear-quadratic in (x_{t-1}, m_t).** The objective equals
   E_0 sum_t rho^t [x_t' mu_t - (gamma/2) x_t' Sigma_t x_t - (1/2) u_t' Lambda u_t] with mu_t
   and Sigma_t as displayed, and the control does not affect (m_t, P_t); so the manager
   faces a full-information linear-quadratic tracking problem whose exogenous state is the
   martingale m_t. No experimentation motive exists.

3. **The policy.** Define backward from A_T = 0, C_T = 0, c_T = 0:

   ```
   D_t = Lambda + gamma Sigma_t + rho A_{t+1}                  (positive definite),
   A_t = Lambda - Lambda D_t^{-1} Lambda,                       (Riccati recursion; 0 <= A_t <= Lambda)
   C_t = Lambda D_t^{-1} (G + rho C_{t+1}),      c_t = Lambda D_t^{-1} (rho c_{t+1} - e_E c^E).
   ```

   The optimal policy exists, is unique, and is affine in the state,

   ```
   x_t = K_t x_{t-1} + L_t m_t + l_t,
   K_t = D_t^{-1} Lambda,   L_t = D_t^{-1} (G + rho C_{t+1}),   l_t = D_t^{-1} (rho c_{t+1} - e_E c^E),
   ```

   equivalently partial adjustment toward an aim,

   ```
   x_t = x_{t-1} + Gamma_t (aim_t - x_{t-1}),
   Gamma_t = I - D_t^{-1} Lambda = D_t^{-1} (gamma Sigma_t + rho A_{t+1})   (= Lambda^{-1} A_t when Lambda is invertible),
   aim_t = (gamma Sigma_t + rho A_{t+1})^{-1} [ gamma Sigma_t Markowitz_t + rho A_{t+1} E_t aim_{t+1} ],   aim_{T-1} = Markowitz_{T-1},
   ```

   with E_t aim_{t+1} = aim_{t+1} evaluated at m_t (aim is affine in m and m is a martingale).
   Gamma_t is similar to a symmetric matrix with eigenvalues in (0, 1], and in (0, 1) when
   Lambda is positive definite, so that every trade is then a genuine partial adjustment; the
   value 1 occurs exactly on Lambda's null directions (costless instruments, as the ETFs of
   parts 4(a) and 5), where the position is re-set in full. Unrolling, aim_t = sum_{s=t}^{T-1} W_{t,s} E_t Markowitz_s with
   matrix weights W_{t,s} = [prod_{u=t}^{s-1} (gamma Sigma_u + rho A_{u+1})^{-1} rho A_{u+1}]
   (gamma Sigma_s + rho A_{s+1})^{-1} gamma Sigma_s summing to I, and in the baseline
   E_t Markowitz_s = (gamma Sigma_s)^{-1} mu_t: the aim is the current Markowitz portfolio
   re-weighted toward the future, smaller predictive covariances Sigma_s <= Sigma_t. That is
   how the aim accounts for predictive variance shrinking under learning and for future costs.
   The value function is J_t(x_{t-1}, m_t) = -(1/2) x_{t-1}' A_t x_{t-1} + x_{t-1}' (C_t m_t + c_t)
   + q_t(m_t) with q_t quadratic in m_t.

4. **Exposure-and-fund coordinates, exact separation, and the three bundling terms.** Assume
   M = K and B^E invertible (the ETFs span the factors exactly; the missing-direction case is
   Not shown). Let S = [[B^A', B^E']; [I_N, 0]], invertible, and w = S x = (y, x^A) with
   y = B' x the total factor exposure. In these coordinates the problem is again of the form in
   part 2 with

   ```
   mean       m~_t = (lambda_hat_t, alpha_hat_t) - S^{-T} e_E c^E,
   risk       Sigma~_t = S^{-T} Sigma_t S^{-1},
   cost       Lambda~ = S^{-T} Lambda S^{-1},
   ```

   and in the reference case, writing R = (B^E)^{-1} (so x^E = R' (y - B^A' x^A)),
   Omega = R Lambda_E R', Xi = R Sigma_E R', phi = R c^E:

   ```
   Sigma~_t = [[ Sigma_f + P^lambda_t + Xi,    -Xi B^A' ];
               [ -B^A Xi,                       Sigma_A + P^alpha_t + B^A Xi B^A' ]],
   Lambda~  = [[ Omega,                         -Omega B^A' ];
               [ -B^A Omega,                    Lambda_A + B^A Omega B^A' ]],
   m~_t     = ( lambda_hat_t - phi,   alpha_hat_t + B^A phi ).
   ```

   (a) *Exact separation.* If Lambda_E = 0, Sigma_E = 0 and c^E = 0 (ETFs costless to trade,
   residual-free and fee-free), the cross blocks vanish and the optimal policy is:

   ```
   y_t   = (gamma (Sigma_f + P^lambda_t))^{-1} lambda_hat_t                 (exposure: myopic factor-space Markowitz, fully adjusted each review),
   x^A_t = x^A_{t-1} + Gamma^A_t (aim^A_t - x^A_{t-1})                      (funds: part 3 with Lambda_A, gamma (Sigma_A + P^alpha_t), rho, and alpha_hat_t),
   x^E_t = R' ( y_t - B^A' x^A_t )                                          (ETFs: net the funds' factor by-product).
   ```

   The exposure trade responds to premium beliefs and their precision only, the fund trade to
   alpha beliefs and their precision only, and the ETF position is the difference between the
   desired exposure and the exposure the funds carry as a by-product, with either sign.

   (b) *What bundling adds.* Each of the three ETF frictions couples the two problems through
   the by-product map B^A R: nonzero ETF trading cost adds the cost cross block -Omega B^A'
   (a fund trade must be netted by an ETF trade that costs), so exposure is no longer myopic
   and the joint Riccati recursion of part 3 in the coordinates w applies; ETF residual risk
   adds the risk cross block -Xi B^A' (netting exposure through ETFs carries residual risk that
   the fund position affects); ETF fees shift the fund mean by +B^A phi (a fund's by-product
   exposure saves the fee that ETF exposure would pay) and the exposure mean by -phi. In the
   reference case these three are the only couplings: with them set to zero the policy is
   (a), and the general policy is part 3 applied to (m~_t, Sigma~_t, Lambda~).

5. **Trading speeds in the separated homogeneous case.** Under (a) with Lambda_A = lambda_A I,
   Sigma_A = sigma_A^2 I and a prior alpha block s^2 I (no pooled component, s_bar = 0), the
   fund block is scalar: P^alpha_t = p_t I with p_t = (1/s^2 + t/sigma_A^2)^{-1}, the Riccati
   recursion is scalar, Gamma^A_t = g_t I with g_t in (0, 1) (lambda_A > 0) decreasing in
   lambda_A and increasing in gamma at each t, and the ETF exposure adjusts at speed I. The
   stationary limit: write a_t^{(T)} for the fund block's scalar Riccati value at review t under
   horizon T and a_infinity for the unique root in [0, lambda_A] of

   ```
   a = lambda_A - lambda_A^2 / (lambda_A + gamma sigma_A^2 + rho a),
   ```

   that is, a_infinity = [ -(gamma sigma_A^2 + (1 - rho) lambda_A) + sqrt( (gamma sigma_A^2 + (1 - rho) lambda_A)^2 + 4 rho gamma sigma_A^2 lambda_A ) ] / (2 rho)
   for rho > 0 (and a_infinity = lambda_A gamma sigma_A^2 / (lambda_A + gamma sigma_A^2) at
   rho = 0). Then for every fixed t the limit a_t^{(infinity)} = lim_{T -> infinity} a_t^{(T)}
   exists, and lim_{t -> infinity} a_t^{(infinity)} = a_infinity, so the trading rate converges,
   in that order of limits, to g_infinity = a_infinity / lambda_A in (0, 1). Remark, not part of
   the statement: g_infinity is `garleanu2009dynamic`'s rate a/lambda (its equation (9), the
   case Lambda proportional to Sigma) with lambda = lambda_A / sigma_A^2 and their
   (gamma_GP, rho_GP) = (gamma/rho, 1 - rho), because they discount the stage reward by
   (1 - rho_GP)^{t+1} and the cost by (1 - rho_GP)^t while M5 discounts both by rho^t; the
   identification is derived in the proof (red's algebra) and checked numerically.

**One sentence without model nouns.** Trading a fraction of the way toward an aim that
anticipates how much learning will shrink the risk charge is the known linear-quadratic rule;
what the bundled instruments add is that, in exposure-and-position coordinates, the aim splits
into a myopic exposure rule and a costly-position rule with the cheap instrument netting the
by-product, and the split is exact unless the cheap instrument itself costs to trade, carries
its own risk, or charges a fee, each of which enters as one explicit cross term through the
by-product map.

## Proof

### 1. Exogenous learning

M5's filter is the Kalman filter for theta_{t+1} = theta_t (baseline), y_{t+1} = H theta_t + d
+ L z_{t+1}, with observation noise covariance Sigma_y = L Sigma_z L'. Its covariance
recursion P_{t+1} = P_t - P_t H' (H P_t H' + Sigma_y)^{-1} H P_t involves only P_0, H and
Sigma_y, none of which depends on positions or trades, so P_t is deterministic and
policy-independent. The mean recursion is m_{t+1} = m_t + K_t (y_{t+1} - H m_t - d) with
K_t = P_t H' (H P_t H' + Sigma_y)^{-1}; under the manager's belief theta_t | I_t ~ N(m_t, P_t)
and z_{t+1} independent of I_t, so E_t y_{t+1} = H m_t + d and E_t m_{t+1} = m_t; the
innovation y_{t+1} - H m_t - d has conditional covariance H P_t H' + Sigma_y, so the innovation
covariance of m is K_t (H P_t H' + Sigma_y) K_t', deterministic. Sigma_t = G P_t G'
+ Sigma_r is deterministic and positive definite because Sigma_r is (Sigma_z positive definite,
and the residual block enters Sigma_r with the identity). For the decoupling, transform the
observation by the invertible map L^{-1}: y -> (f, r^A - B^A f, r^E - B^E f + c^E) = (lambda +
z^f, alpha + z^A, z^E): the observation matrix becomes L^{-1} H = [[I_K, 0]; [0, I_N]; [0, 0]]
and the noise covariance becomes Sigma_z, in the reference case diag(Sigma_f, Sigma_A,
Sigma_E); a Gaussian posterior is invariant under invertible transformations of the
observation. A Kalman update with a
block-diagonal observation matrix, block-diagonal noise and block-diagonal prior covariance
produces a block-diagonal posterior covariance and updates each block from its own observation
block (the gain P H' (H P H' + Sigma_z)^{-1} is block diagonal), and the third block carries
no information; induction gives P_t = diag(P^lambda_t, P^alpha_t) with the stated update
sources. Then G P_t G' = B P^lambda_t B' + diag(P^alpha_t, 0) and Sigma_r = B Sigma_f B' +
diag(Sigma_A, Sigma_E), which is the displayed Sigma_t.

### 2. The linear-quadratic form

E_t [x_t' r_{t+1}] = x_t' mu_t and Var_t (x_t' r_{t+1}) = x_t' Sigma_t x_t by M5's predictive
moments, so the per-review certainty equivalent is the displayed quadratic in x_t with
coefficients (mu_t, Sigma_t) that are functions of (m_t, P_t). Since (m_t, P_t) evolve by part
1 regardless of the policy, the problem is a Markov decision problem with state (x_{t-1}, m_t),
exogenous component m_t, and a stage reward that is a concave quadratic in the control x_t.

### 3. The policy, by backward verification

Claim: for each t, J_t(x, m) = -(1/2) x' A_t x + x' (C_t m + c_t) + q_t(m), with A_t, C_t, c_t
as displayed and q_t a quadratic polynomial in m, and the maximizer is affine as displayed.
At t = T, J_T = 0 (no terminal value), matching A_T = C_T = c_T = 0. Suppose the claim at t+1.
The Bellman equation at t is

J_t(x_{t-1}, m_t) = max_{x_t} { -(1/2)(x_t - x_{t-1})' Lambda (x_t - x_{t-1}) + x_t' mu_t
- (gamma/2) x_t' Sigma_t x_t + rho E_t J_{t+1}(x_t, m_{t+1}) },

and E_t J_{t+1}(x_t, m_{t+1}) = -(1/2) x_t' A_{t+1} x_t + x_t' (C_{t+1} m_t + c_{t+1}) +
E_t q_{t+1}(m_{t+1}) by part 1 (E_t m_{t+1} = m_t; the last term is finite, a quadratic in m_t
plus a constant from the deterministic innovation covariance, and does not depend on x_t).
The bracket is a quadratic in x_t with Hessian -(Lambda + gamma Sigma_t + rho A_{t+1}) = -D_t.
D_t is positive definite (gamma Sigma_t is, Lambda and A_{t+1} are positive semidefinite, the
latter by the induction below), so the maximizer is unique and given by the first-order
condition D_t x_t = Lambda x_{t-1} + v_t with v_t = mu_t + rho (C_{t+1} m_t + c_{t+1}) =
(G + rho C_{t+1}) m_t + (rho c_{t+1} - e_E c^E): this is the K_t, L_t, l_t form. Substituting,
the maximum equals (1/2)(Lambda x_{t-1} + v_t)' D_t^{-1} (Lambda x_{t-1} + v_t)
- (1/2) x_{t-1}' Lambda x_{t-1} + (terms in m_t only), whose x_{t-1}-quadratic part is
-(1/2) x_{t-1}' (Lambda - Lambda D_t^{-1} Lambda) x_{t-1} = -(1/2) x_{t-1}' A_t x_{t-1} and
whose bilinear part is x_{t-1}' Lambda D_t^{-1} v_t = x_{t-1}' (C_t m_t + c_t); the rest is a
quadratic q_t(m_t). This proves the claim at t.

Positivity: with M_t = D_t^{-1/2} Lambda D_t^{-1/2}, 0 <= M_t <= I since 0 <= Lambda <= D_t, and
A_t = D_t^{1/2} (M_t - M_t^2) D_t^{1/2} >= 0 because M - M^2 >= 0 for 0 <= M <= I; also
A_t <= Lambda since Lambda D_t^{-1} Lambda >= 0. Gamma_t = I - D_t^{-1} Lambda = D_t^{-1/2}
(I - M_t) D_t^{1/2} is similar to I - M_t, symmetric with eigenvalues in (0, 1]: above 0 because
M_t < I strictly (D_t - Lambda = gamma Sigma_t + rho A_{t+1} is positive definite), and at most
1 with equality exactly on the null space of Lambda, where M_t vanishes; so the range is (0, 1)
when Lambda is positive definite. When Lambda is invertible, Lambda^{-1} A_t = I -
D_t^{-1} Lambda = Gamma_t.

Partial-adjustment form: x_t = D_t^{-1} Lambda x_{t-1} + D_t^{-1} v_t = x_{t-1} + Gamma_t
(aim_t - x_{t-1}) with Gamma_t aim_t = D_t^{-1} v_t, that is, aim_t = (gamma Sigma_t +
rho A_{t+1})^{-1} v_t. Since C_{t+1} m_t + c_{t+1} = Lambda D_{t+1}^{-1} v_{t+1}(m_t) =
Lambda Gamma_{t+1} aim_{t+1}(m_t) = A_{t+1} aim_{t+1}(m_t) (using Lambda Gamma_{t+1} = A_{t+1},
valid for semidefinite Lambda from Gamma = I - D^{-1} Lambda), and v_{t+1}(m_t) is v_{t+1}
with m_{t+1} replaced by m_t, which is E_t v_{t+1} by the martingale property, we get
v_t = gamma Sigma_t Markowitz_t + rho A_{t+1} E_t aim_{t+1}, the displayed recursion; at
t = T-1, A_T = 0 gives aim_{T-1} = Markowitz_{T-1}. Unrolling the recursion gives the matrix
weights W_{t,s}; they sum to I because at each step the two weights (gamma Sigma_t +
rho A_{t+1})^{-1} gamma Sigma_t and (gamma Sigma_t + rho A_{t+1})^{-1} rho A_{t+1} sum to I,
and induction on the tail. In the baseline E_t mu_s = G E_t m_s - e_E c^E = mu_t, so
E_t Markowitz_s = (gamma Sigma_s)^{-1} mu_t, and Sigma_s <= Sigma_t for s >= t because
P_s <= P_t (the Kalman covariance is nonincreasing in the Loewner order for a constant state).

Existence and uniqueness of the optimal policy over all admissible policies (measurable in
(I_t, x_{t-1})) follow from the verification: the affine policy attains the Bellman maximum at
every state and the value is finite, so by backward induction its expected objective is
J_0(x_{-1}, m_0), and any policy that deviates on a set of positive probability at some t loses
the strictly positive gap of the strictly concave stage problem there.

### 4. Coordinates, separation, bundling terms

S is invertible when B^E is: [[B^A', B^E']; [I, 0]] has inverse [[0, I]; [R', -R' B^A']] with
R = (B^E)^{-1}. For x = S^{-1} w, x' mu_t = w' S^{-T} mu_t, x' Sigma_t x = w' S^{-T} Sigma_t S^{-1} w,
u' Lambda u = (Delta w)' S^{-T} Lambda S^{-1} (Delta w): the problem in w is of the form of
part 2 with the displayed (m~_t, Sigma~_t, Lambda~), and S^{-T} G m_t = (lambda_hat_t, alpha_hat_t)
because G m_t = B lambda_hat + e_A alpha_hat and S^{-T} B = (I_K, 0)', S^{-T} e_A = (0, I_N)' (check:
S' (I,0)' = (B^A, B^E)'... precisely, S' = [[B^A, I]; [B^E, 0]] and S' (lambda, alpha) = (B^A lambda
+ alpha, B^E lambda) = G (lambda, alpha), so S^{-T} G = I). The reference-case block matrices
follow from x^E = R' (y - B^A' x^A) and x^A = x^A: Sigma_t in x-coordinates is B (Sigma_f +
P^lambda) B' + diag(Sigma_A + P^alpha, Sigma_E), and w' S^{-T} Sigma_t S^{-1} w = y' (Sigma_f +
P^lambda) y + x^A' (Sigma_A + P^alpha) x^A + (y - B^A' x^A)' R Sigma_E R' (y - B^A' x^A), which
expands to the displayed Sigma~_t; likewise for Lambda~ with Lambda = diag(Lambda_A, Lambda_E),
and S^{-T} e_E c^E = (R c^E, -B^A R c^E) = (phi, -B^A phi) gives m~_t.

(a) With Omega = Xi = 0 and phi = 0 the stage reward is the sum of y' lambda_hat_t - (gamma/2)
y' (Sigma_f + P^lambda_t) y, which has no cost term and no dependence on past y, and
x^A' alpha_hat_t - (gamma/2) x^A' (Sigma_A + P^alpha_t) x^A - (1/2)(Delta x^A)' Lambda_A
(Delta x^A), which depends on (x^A_{t-1}, alpha_hat_t) only. The Bellman maximization over
w_t = (y_t, x^A_t) therefore splits into two independent maximizations, and by induction the
value function is the sum of a y-part (the static maximum each review, attained at the
displayed y_t) and an x^A-part that is exactly part 3's problem for the fund block; the ETF
position is x^E_t = R' (y_t - B^A' x^A_t) by the coordinate change.

(b) is the reading of the block matrices: each of Omega, Xi, phi appears in exactly one cross
block or mean shift, all through B^A (bundling) composed with R (the ETF replication map),
and part 3 applied to (m~_t, Sigma~_t, Lambda~) is the optimal policy in w, mapped back by
x = S^{-1} w.

### 5. Speeds

With Sigma_A = sigma_A^2 I, prior s^2 I and the decoupled scalar updates of part 1, P^alpha_t
= p_t I with 1/p_t = 1/s^2 + t/sigma_A^2. With Lambda_A = lambda_A I every matrix in the fund
block's recursion is a multiple of I, so A^A_t = a_t I, D^A_t = (lambda_A + gamma (sigma_A^2 +
p_t) + rho a_{t+1}) I and g_t = 1 - lambda_A / d_t. Monotonicity, by backward induction on
the rate itself (red's correction): with r_t = gamma (sigma_A^2 + p_t) and a_{t+1} = lambda_A
g_{t+1},

g_t = (r_t + rho lambda_A g_{t+1}) / (lambda_A + r_t + rho lambda_A g_{t+1}),

whose partial derivative in lambda_A at fixed g_{t+1} is -r_t / d_t^2 < 0, in g_{t+1} at fixed
lambda_A is rho lambda_A^2 / d_t^2 > 0, and in r_t is lambda_A / d_t^2 > 0. Base case
g_{T-1} = r_{T-1} / (lambda_A + r_{T-1}), decreasing in lambda_A and increasing in gamma.
Inductive step: if g_{t+1} is nonincreasing in lambda_A, then g_t is, as the composition of a
map decreasing in lambda_A directly and increasing in a quantity that decreases in lambda_A;
this is the inequality a_{t+1} >= lambda_A a'_{t+1} of red's review, with a' the derivative in
lambda_A, in the normalization a = lambda_A g. Likewise if g_{t+1} is nondecreasing in gamma
then g_t is, since r_t increases in gamma. Hence g_t decreases in lambda_A and increases in
gamma at every t; g_t > 0 since r_t > 0 and g_t < 1 since lambda_A > 0. The exposure block
has Lambda~ block zero, hence Gamma = I. The stationary limit: the scalar map F(r, a) =
lambda_A - lambda_A^2 / (lambda_A + r + rho a) satisfies, for a, a' in [0, lambda_A] and
r >= r_min := gamma sigma_A^2 > 0, |F(r, a) - F(r, a')| <= kappa |a - a'| with kappa = rho
lambda_A^2 / (lambda_A + r_min)^2 < 1, and |F(r, a) - F(r', a)| <= |r - r'|, both from the
derivative bounds of the monotonicity paragraph. With r_s = gamma (sigma_A^2 + p_s) decreasing
to r_min, a_t^{(T)} = F(r_t, F(r_{t+1}, ... F(r_{T-1}, 0))) and a_t^{(T+1)} - a_t^{(T)} is, by the
contraction, at most kappa^{T-t} |F(r_T, 0)| <= kappa^{T-t} lambda_A in absolute value, so
(a_t^{(T)})_T is Cauchy and a_t^{(infinity)} exists, satisfying a_t^{(infinity)} = F(r_t,
a_{t+1}^{(infinity)}). Comparing with the constant-r recursion whose fixed point is a_infinity
(F(r_min, .) is a contraction on [0, lambda_A], so the fixed point exists, is unique there and
is the displayed root of the quadratic rho a^2 + (gamma sigma_A^2 + (1 - rho) lambda_A) a -
lambda_A gamma sigma_A^2 = 0), |a_t^{(infinity)} - a_infinity| <= sum_{s >= t} kappa^{s-t}
|r_s - r_min| = gamma sum_{s >= t} kappa^{s-t} p_s -> 0 as t -> infinity since p_s -> 0. The
identification of g_infinity with `garleanu2009dynamic`'s equation (9) is a remark: their
objective weights the stage reward at t by (1 - rho_GP)^{t+1} and the cost by (1 - rho_GP)^t
(their equation (4)), which equals M5's common weight rho^t with rho = 1 - rho_GP after scaling
the reward by (1 - rho_GP), that is, gamma_GP = gamma / rho; with lambda = lambda_A / sigma_A^2
substitute into their equation (9): gamma_GP (1 - rho_GP) = gamma, lambda rho_GP =
(1 - rho) lambda_A / sigma_A^2 and 4 gamma_GP lambda (1 - rho_GP)^2 = 4 rho gamma lambda_A /
sigma_A^2, with denominator 2 rho; their rate a/lambda is their a times sigma_A^2 / lambda_A, and
moving sigma_A^2 inside the square root gives [-(gamma sigma_A^2 + (1 - rho) lambda_A) +
sqrt((gamma sigma_A^2 + (1 - rho) lambda_A)^2 + 4 rho gamma sigma_A^2 lambda_A)] /
(2 rho lambda_A) = a_infinity / lambda_A = g_infinity (red's derivation, confirmed to 1e-15 at
three parameter points; part (vi) of the check).

## Checks

`checks/030/check.py` (exits non-zero on failure; a check, not a proof). On the analyst's
experiment 021 instance shapes (1 fund, 1 ETF, 1 factor; 2 funds, 1 ETF, 1 factor; 3 funds,
2 ETFs, 2 factors) with French-scale premia and shocks, the pooled alpha prior, fund and ETF
residuals of 2 and 0.2 percent, Lambda_fund = 0.1, Lambda_ETF = 0.01, gamma in {2, 5, 10} and
T in {4, 8}: (i) the Kalman covariance path is identical across simulated paths and the
posterior mean's sample innovations average to zero; (ii) the policy's one-step Bellman
optimality is checked at random states against a numerical maximizer that does not use the
recursion; (iii) the K_t, L_t, l_t form and the Gamma_t, aim_t form agree, Gamma_t's
eigenvalues lie in (0, 1), and the matrix weights W_{t,s} sum to I; (iv) with the exogenous
state frozen (no learning) the recursion's path equals the direct solution of the whole-path
quadratic program; (v) in the separated case (ETF cost, residual and fee zero, B^E invertible)
the recursion's policy equals the closed form of part 4(a) coefficient by coefficient, and
switching each of the three frictions on alone produces exactly the displayed cross block or
mean shift; (vi) in the scalar case the stationary fund rate matches Garleanu-Pedersen's
equation (9).

Experiment 021 (analyst, reported; exact backward recursion on the same instance shapes
under the ROADMAP reading, before M5's conventions) is consistent with parts 3-4 as observations:
fund trading speeds 0.09-0.23 per quarter against 0.56-0.83 for ETFs, rising with gamma and
falling toward the horizon; the aim's alpha part is a hedged position, the fund short offset one
for one by the ETF carrying the same loading (part 4(a)'s netting), and its exposure part sits
almost entirely in the ETFs; the coefficient-by-coefficient comparison with the (K_t, L_t, l_t)
form above follows the analyst's Deviation to M5.

Experiment 021 Deviation 4 (analyst): the coefficient-form policy above (D_t, A_t, C_t, c_t and
K_t, L_t, l_t at rho = 1) agrees with experiment 021's independent backward recursion to
2.1e-15 relative on all 18 of its instances (gamma 2, 5, 10; T 4, 8), every quarter and every
coefficient, against a registered threshold of 1e-8; the separated case and the missing-direction
shape (asked as Q4-Q5) are covered by this claim's and claim 031's own checks, not by a
registered experiment. Experiment 022 (analyst, reported; M5 at realistic scale, 30 funds, 8 ETFs, five factors,
gamma 5, T 40) gives the calibrated magnitudes: trading speeds 0.167 for funds against 0.287
for ETFs at t = 0, falling to 0.052 and 0.211 at t = 39; the aim's alpha part (belief revisions)
of 31-36 gross in funds hedged by 21-24 in ETFs, the netting of part 4(a) at scale; and the
policy's value over the same dynamic policy run with a frozen predictive variance of 0.66 bp
per quarter (standard error 0.04), which is the calibrated size of claim 032's learning factor.
The analyst's caution is adopted: the policy's value over the baselines (hundreds of bp) comes
from the leverage (gross about 48) and fund shorts that M5's unconstrained class permits and is
no evidence of economic value; D13 restores the constraints. On the split's definition
(experiment 022's point): this claim's split is the linear decomposition of the affine aim,
aim_t = A^lambda_t lambda_hat_t + A^alpha_t alpha_hat_t + a^c_t, into its premium response, its
alpha response and its fee term, that is, the exposure part is taken relative to zero alpha;
M5's decision-objects paragraph defines the exposure part with alpha beliefs at their prior
mean, which equals the zero-alpha exposure part plus the fixed vector A^alpha_t mu_a 1 (the
prior-mean fund positions, shorts when mu_a < 0) and so is not pure factor exposure. The
zero-alpha split is the one parts 4(a)-(b) prove statements about and the one D12 comparisons
should use; M5's text is frozen (experiments 021-022 name it) and is not edited. Experiment
025 (analyst, reported) repeats experiment 024 with persistence (autocorrelation 0.5 to 0.95 of
alpha or of the premia) in the funded long-only space: the dynamic policy adds 0.01-0.12 bp per
quarter over the one-quarter rule, with the aim-in-front effect at most 0.02 bp, because the
calibrated alpha Kalman gain is about 1.5 percent per quarter and beliefs barely move; the
policy's structure stands, its anticipatory terms carry little weight at this scale.

## Not shown

- The infinite horizon (rho < 1, T -> infinity): the backward recursion's limit and the
  stationary Riccati equation are not established here; part 5's stationary identification is
  a limit statement checked numerically.
- The missing-direction case (M < K or rank B^E < K): S is not invertible, the exposure is
  reachable only partly through ETFs, and the split of part 4 needs the reachable/unreachable
  decomposition of claim 005's geometry; the general policy of part 3 still applies.
- Redundant ETFs (M > K): part 4 is stated for M = K; with M > K the ETF residual and cost
  blocks select among replicating portfolios, not treated.
- The pooled prior (s_bar > 0) makes the alpha block exchangeable rather than scalar: two
  speeds, on the common-alpha direction and its complement; part 5 is the s_bar = 0 case.
- Unequal persistence (Phi != I, Q != 0) changes E_t m_{t+1} to Phi m_t + (I - Phi) theta_bar;
  parts 1-4 extend with that replacement and are not stated here.
- Long-only and funding constraints are absent by M5's design (D13).
- AX-10 covers the stationary average-cost statement only; the finite-horizon discounted
  recursion is this claim's own proof (part 3), and Theorem 3.1 of `abeille2016lqg` is not used.
- Nothing here is a magnitude; the analyst's experiment 021 and later experiments give those.
- The check's separated case uses a degenerate ETF observation (Sigma_E = 0), handled with the
  pseudo-inverse in the Kalman gain; the claim's part 4(a) is stated for that limit and the
  positive-definiteness of Sigma_t there holds because B^E is invertible.

## Prior art

Mechanism: A linear-quadratic control problem with an unobserved constant coefficient learned
from observations the control does not affect reduces by certainty equivalence to
full-information tracking of a martingale with a deterministic shrinking risk matrix, solved by
partial adjustment toward an aim from a backward Riccati recursion; when the controls split
into a cheap instrument that spans a coordinate and a costly instrument that carries that
coordinate as a by-product, the problem separates exactly in the split coordinates unless the
cheap instrument itself costs, is risky, or charges, each of which enters as one cross term.

General results checked: `garleanu2009dynamic` Propositions 1-2 (unique solution, quadratic
value function, trading rate Lambda^{-1} A_xx toward an aim, for any positive-definite Lambda)
and Proposition 3 (the aim as a weighted average of current and expected future Markowitz
portfolios under Assumption A, Lambda = lambda Sigma), stated for known stationary
mean-reverting predictors (their equation (2)) and constant Sigma; M5's learned constant is a
martingale predictor excluded by their stationarity condition and its risk matrix is
time-varying, so part 3 is their result in kind with a time-varying recursion and matrix
weights, verified in the proof (red's mechanism note, 2026-09-28: known in kind; rule 21).
Certainty equivalence and filter/control separation with exogenous observations:
`simon1956dynamic` and `theil1957note` (wanted; the origin, with known coefficients and no
learning), `ljungqvist2004recursive` (cited; the textbook LQ-with-Kalman-filter statement that
`garleanu2009dynamic` itself cites for its Riccati equations), and `abeille2016lqg` (full text;
ledger entry `AX-10`),
which poses N assets, a linear state space with Kalman filtering, an LQR law from a Riccati
equation and quadratic impact costs, states the separation principle as its Assumption 1
(noises martingale differences, conditionally Gaussian, mutually independent) and takes the
stationary Kalman and LQR solutions from Lancaster-Rodman (its Theorems 2.1-2.2); its Section 4
example separates a single asset's alpha from its impact, not N funds from M ETFs, and has one
cost level. In M5 the reduction of part 2 is direct because the objective is already stated in
predictive moments, and the finite-horizon recursion of part 3 is time-varying rather than the
stationary Riccati of `abeille2016lqg`. `garleanu2016dynamic` (full text) generalizes the 2009
model to general factor dynamics, persistent and transitory costs and, in its Section 3,
time-varying return volatility (Proposition 9), with Proposition 1 (unique strategy tracking an
aim at rate Lambda^{-1} A_xx) and Proposition 5 (the general discrete-time solution); it
requires the factor dynamics to be stationary (its equation (2)), which a Kalman-filtered
posterior mean, a martingale with shrinking innovation variance, is not, so its results do not
cover M5's learning case (the librarian's check, FINDINGS 2026-09-28). The librarian found no
source combining Kalman-filtered learning of a multi-asset mean with quadratic trading costs
in closed form; part 3 is therefore the known recursion in kind, verified for M5, and no
priority is claimed for it. `brennan1998role` (learning about a constant premium in continuous time, one asset,
hedging demand from estimation risk): the learning side, not the cost side. `pastor2002investing`
(Bayesian fund selection with learning across funds, static): the pooled prior's origin.
Treynor-Black (`treynor1973security`, equation (16)): part 4(a)'s netting of the funds'
by-product exposure by the ETF position is its explicit market position made dynamic and
costly. Claims 027-028 (two-stage separation in M2) are the one-quarter, funded, proportional-
cost analogue: there separation failed through the funded fibre and the constraint multiplier;
here, without constraints, it holds exactly under the three zero conditions of part 4(a) and
fails through the three explicit cross terms.

Searched: FINDINGS (D4 and D12 entries), the refuted directory, claims 004-005 and 027-028,
model/SPEC.md M5, refs/text for `garleanu2009dynamic`, `brennan1998role`, `pastor2002investing`
and `treynor1973security`. This is a claim because D12's first task needed the policy in M5's
learning form stated exactly (for experiment 021's coefficient-by-coefficient comparison) and
because the exact separation and its three coupling terms are the fund-of-funds content that no
registered source states; the linear-quadratic solution itself is cited in kind and claimed as
nothing new.

## Open objections

Red (review, approved): two required corrections, made on math/claim030-corrections: the
eigenvalue range of Gamma_t is (0, 1], and (0, 1) only for positive definite Lambda; part 5's
monotonicity is now a backward induction on the rate. Lean (note of 2026-09-28): the same
spectrum point; part 5's stationary limit made precise (fixed t, T -> infinity, then t ->
infinity, with the root in closed form and the Garleanu-Pedersen identification demoted to a
remark); AX-10 stated as context that no proof step uses. All folded in. Red should test: the
decoupling argument when Sigma_A is not diagonal (still
block-decoupled between lambda and alpha; the alpha block itself is then coupled across funds);
the semidefinite-Lambda case in part 3 (D_t positive definite needs gamma Sigma_t positive
definite, which needs Sigma_z positive definite); the sign and placement of the fee shifts in
part 4; and the monotonicity induction in part 5.

## Review

**Red, 2026-09-28.** I checked every part by hand, tested parts 3-5 numerically with red's own recursion, and ran `checks/030/check.py`, which passes. The Statement's results hold. Two required corrections are below: one Statement range and one proof step. Neither changes a result.

**Hand check.**
- *Part 1.* P_t depends only on (P_0, H, L Sigma_z L'). The transformed observation L^{-1} y has noise z and observation matrix diag(I_K, I_N) above a zero block. So with block-diagonal Sigma_z and prior the gain is block diagonal and the filter decouples.
  - Sigma_t is positive definite because Sigma_r = [B, I] Sigma_z [B, I]' with full row rank.
  - First Open objection: with Sigma_A not diagonal, lambda and alpha still decouple, and only the alpha block couples across funds.
- *Part 2.* It follows from M5's predictive moments.
- *Part 3.* Checked:
  - the FOC D_t x_t = Lambda x_{t-1} + (G + rho C_{t+1}) m_t + (rho c_{t+1} - e_E c^E), and the recursions for A_t, C_t, c_t;
  - Lambda Gamma_{t+1} = A_{t+1} and the martingale property, which give the aim recursion;
  - the weights W_{t,s} summing to I, and 0 <= A_t <= Lambda;
  - existence and uniqueness by verification.
- *Part 4.*
  - When M = K, S' = G, so S^{-T} G = I. S^{-T} e_E c^E = (phi, -B^A phi) gives m~ = (lambda_hat - phi, alpha_hat + B^A phi); the fee signs are right (third Open objection).
  - x^E = R'(y - B^A' x^A) expands Sigma~ and Lambda~ into the displayed blocks, with cross terms -Xi B^A' and -Omega B^A'.
  - With Omega = Xi = phi = 0 the Bellman problem splits. The y-part has no cost and no dependence on past y, so it is myopic.
- *Part 5.* With the fund block scalar the recursion is scalar. The stationary identification with `garleanu2009dynamic` eq. (9) is right under gamma_GP = gamma/rho and rho_GP = 1 - rho. Red rederived GP's scalar stationary Riccati: a = [-(lambda rho_G + gamma_G(1 - rho_G)) + sqrt(...)]/(2(1 - rho_G)), rate a/lambda. It equals M5's stationary 1 - lambda_A/d exactly: 0.12390 at rho 0.98, gamma 5, lambda_A 0.1; 0.24242 at rho 0.99, gamma 10, lambda_A 0.05.

**Independent numerical tests** (red's script, not committed). The case is K = M = 2 with invertible B^E, N = 3, random fund loadings and residuals, a deterministic shrinking P_t, gamma 5, rho 0.98 and T = 6.
- *4(a).* Red's recursion in x-coordinates equals the closed form (myopic y, the fund block's part-3 recursion, x^E = R'(y - B^A' x^A)) to 2.2e-15 at 50 random states.
- *4(b).* Each friction switched on alone (ETF cost 0.01, ETF residual 0.3%, ETF fee 3 bp) gives exactly the displayed cross block or mean shift.
- *Part 5 monotonicity.* g_t is decreasing in lambda_A over [0.01, 1] and increasing in gamma over [0.5, 20], at every t of a 30-quarter horizon.

**Required correction 1 (Statement, part 3): Gamma_t's eigenvalue range.** The Statement says Gamma_t "is similar to a symmetric matrix with eigenvalues in [0, 1), so every trade is a genuine partial adjustment", and the Setting admits positive semidefinite Lambda.
- With M_t = D_t^{-1/2} Lambda D_t^{-1/2}, gamma Sigma_t positive definite gives 0 <= M_t < I. So I - M_t has eigenvalues in **(0, 1]**, with 1 exactly on the null directions of Lambda; 0 never occurs.
- The claim's own part 4(a) ("fully adjusted each review") and part 5 ("the ETF exposure adjusts at speed I") use that value-1 case, and red's test shows it: with Lambda_E = 0, Gamma_0 has eigenvalues 0.041-0.077 (funds) and 1.000, 1.000 (ETFs).
- Please state "(0, 1], and (0, 1) when Lambda is positive definite", with "genuine partial adjustment" only for positive definite Lambda. The Proof's positivity paragraph already has "(0, 1) when Lambda is positive definite"; only the Statement's range is wrong. No result changes.

**Required correction 2 (Proof, part 5): the monotonicity step.** "d_t increases in lambda_A by at most one for one" is backward: d_t = lambda_A + gamma(sigma_A^2 + p_t) + rho a_{t+1}, so dd_t/dlambda_A = 1 + rho a'_{t+1} >= 1. What is needed is that lambda_A/d_t increases, that is, that (gamma(sigma_A^2 + p_t) + rho a_{t+1})/lambda_A decreases, which holds if a_{t+1} >= lambda_A a'_{t+1}.
- This is true at t = T-1 (a_{T-1} - lambda_A a'_{T-1} = lambda_A^2 gamma s/(lambda_A + gamma s)^2 >= 0 with s = sigma_A^2 + p_{T-1}), and it plausibly propagates by induction.
- The monotonicity itself holds numerically; please replace the step with that induction. The gamma part of the argument is right.

**Nits.**
- Part 4 is stated for M = K; the Not shown covers M > K and M < K.
- The split's definition (zero-alpha exposure part against M5's prior-mean definition) is handled clearly in the Checks section.

**Mechanism (4b).** Certainty-equivalent LQ tracking of a martingale with a deterministic shrinking risk matrix, solved by a finite-horizon Riccati recursion: `garleanu2009dynamic` in kind, with the separation principle through AX-10, as the claim says; rule 21 is met, with the time-varying recursion proved inline since AX-10 is stationary only. What it adds for D12 is the exact exposure-and-fund separation and its three explicit coupling terms, a dynamic, costly form of Treynor-Black's netting (eq. (16)).

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check of parts 1-5 is sound: exogenous learning with a decoupled filter; certainty-equivalent partial adjustment from a backward Riccati recursion with verified existence and uniqueness; exact exposure-and-fund separation for M=K with the three ETF coupling terms; the scalar fund block matching garleanu2009dynamic's stationary rate exactly. Red's independent recursion confirms 4(a) to 2e-15 and each coupling term alone. Mechanism: certainty-equivalent LQ tracking (garleanu2009dynamic in kind; separation via AX-10; the time-varying recursion proved inline, since AX-10 is stationary only), an application. What D12 gains is the exact separation and its coupling terms, a dynamic, costly Treynor-Black netting. Required corrections, results unchanged, routed to math: the Statement's Gamma_t eigenvalue range is (0,1], equal to (0,1) only for positive definite Lambda; part 5's monotonicity step needs the induction a_{t+1} >= lambda_A a'_{t+1}. Limits: part 4 is for M=K only.


Not machine checked. Parts 1-3 are finite-dimensional linear algebra and a backward induction
with Gaussian conditional expectations; part 4 is a change of variables; part 5 is scalar.

Lean, 2026-09-28 (final): parts 1-5 are machine checked, within the formal scope PM confirmed
(rule 6b), and this supersedes "not machine checked" above. The statement is in
`lean/Standalone/M5PartialAdjustmentSplit.lean` and the proof in
`lean/Novel/M5PartialAdjustmentSplitProof.lean`. `lake build`, the axiom audit (standard axioms
only) and `checks/030/check.py` pass. No hypothesis structure is used, and AX-10 is not used: the
finite-horizon policy is verified directly. No other claim's proof module is imported
(depends_on []).

Formal objects. Positions and beliefs are indexed by arbitrary finite types. Part 2's problem is
a structure with a trading-cost matrix Lambda >= 0, risk matrices gamma Sigma_t > 0, a discount
rho >= 0 and the mean map mu_t = G m_t - e. The recursion for A_t, C_t, c_t and the aim are
defined backward from T, as in the Statement.

Machine checked:
- Part 1:
  - every P_t is positive definite, with information form P_t^{-1} = P_0^{-1} + t H'R^{-1}H;
  - P_t is nonincreasing, and the innovation covariance is K_t(HP_tH' + R)K_t' = P_t - P_{t+1};
  - Sigma_t is positive definite and nonincreasing, with none of these depending on positions;
  - in the reference case, L is invertible with L^{-1}(f, r^A, r^E) = (f, r^A - B^A f, r^E - B^E f), and the filter with H = L H~ and noise L Sigma_z L' has P_t = diag(P^lambda_t, P^alpha_t);
  - the transformed gain is block diagonal with a zero ETF column, and the displayed Sigma_t holds.
- Part 3:
  - the Bellman verification: for some q_t with q_T = 0, J_t has the stated form, and the affine policy is the unique maximizer of the Bellman objective at every review and state;
  - D_t > 0 and 0 <= A_t <= Lambda;
  - Gamma_t = D_t^{-1}(gamma Sigma_t + rho A_{t+1}) is similar (through D_t^{1/2}) to a symmetric M with 0 < M <= I, and M < I when Lambda > 0; Gamma_t v = v exactly when Lambda v = 0; Gamma_t = Lambda^{-1}A_t when Lambda is invertible;
  - the policy is x_{t-1} + Gamma_t(aim_t - x_{t-1}), with aim_{T-1} = Markowitz_{T-1}, and aim_t = sum_s W_{t,s} Markowitz_s at the current mean, with weights summing to I.
- Part 4 (M = K, B^E invertible):
  - S and its inverse, S' = G (so S^{-T}G = I), S^{-T}(0, c^E) = (phi, -B^A phi), and x^E = R'(y - B^A'x^A);
  - for any invertible change of coordinates, the transformed problem satisfies part 3's hypotheses, and its policy is S times the original policy;
  - the reference-case blocks of Sigma~_t and Lambda~;
  - 4(a): with Lambda~ = diag(0, Lambda_A), block-diagonal risk, identity mean map and no fee, y_t = (gamma(Sigma_f + P^lambda_t))^{-1} lambda_hat_t, the fund block follows part 3 for (Lambda_A, gamma(Sigma_A + P^alpha_t), rho) and alpha_hat_t, and Gamma~_t = diag(I, Gamma^A_t).
- Part 5:
  - P^alpha_t = p_t I;
  - A^A_t = lambda_A g_t I and Gamma^A_t = g_t I, with g_t in (0, 1), strictly decreasing in lambda_A and strictly increasing in gamma;
  - for rho in [0, 1], a_infinity is the unique root in [0, lambda_A], with closed forms for rho > 0 and rho = 0 and a_infinity/lambda_A in (0, 1);
  - for each t, a_t^{(T)} converges as T -> infinity, and these limits converge to a_infinity as t -> infinity;
  - the remark's identification with `garleanu2009dynamic`'s rate is also checked, for 0 < rho < 1.

Paper-level, at PM's instruction (rule 6b), with the formal hypotheses they discharge:
- M5's Gaussian conditional moments. They discharge `Martingale E`, the hypothesis of the Bellman
  verification: the conditional expectation is linear and constant-preserving, and
  E_t m_{t+1} = m_t. They also give part 2's predictive moments, which make the objective the
  formal stage reward.
- The dynamic-programming verification. It passes from the Bellman verification to optimality
  among all admissible measurable policies.

Not formalized: that q_t is quadratic in m_t (it needs the innovation law, and the policy does not
depend on it), the Consequence's reading, and 4(b)'s reading beyond the block formulas. PM's limit
stands: part 4 is for M = K only.

Lean, 2026-09-28 (on lean/m5-missing-direction-leak): claim 030's formal problem now takes a
deterministic, time-varying mean map G_t, as claim 031's reduced fund problem needs (its part 3
says claim 030's part 3 extends verbatim). The constant G_t = G is this claim's case; every other
part of the formal statement is unchanged, and the proof goes through as before.

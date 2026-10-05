# Quarterly portfolio construction with uncertain alpha and factor premia

Draft of 2026-09-27 (skeleton; the center is chosen at the commitment milestone)

## Abstract

Draft abstract. We study an investor who can adjust active mutual funds
and exchange-traded funds (ETFs) only at quarterly reviews, under a funded,
long-only budget. An exchange-traded fund can replace an active fund's
factor exposure only if the required holdings also satisfy position
limits and funding. We give an exact feasibility test separating a
factor direction missing from the exchange-traded-fund span from a
direction present in the span but blocked by those constraints. Two
assumed one-quarter examples show why exposure substitution alone
does not settle the trading decision: an active-fund advantage can
remain despite complete feasible exposure replacement, while adding
an ETF can induce an active sale even when the larger
fund menu cannot feasibly match the full optimum's exposure. A
zero-alpha non-participation result, for a fund with no expected return
beyond its specified factor exposures, holds under a feasible, costless
replacement and a stated zero cross-moment; costly incumbents,
position limits and independent tracking noise give precise limits.
The one-quarter belief-average score depends on beliefs about alpha
and factor premia only through their means. In a separate finite
two-review model, we prove existence of optimal policies and an
attained continuation representation under public learning. An
assumed example with known zero alpha shows that future ETF
adjustment can raise today's active-trading advantage while
future active trading lowers it. A second assumed family retains
both signs with small conditional risk and uncertain alpha that
is not always revealed. Neither family gives a general
dynamic trading boundary or calibrated performance. In every
instance of the two-review model, the effect of future ETF
adjustment lies between differences of that adjustment's premium
at the two root optima. The premium is capped by the cash and
ETF holdings left after today's trade, and a third assumed family
has the opposite sign, so no sign holds across the model.
Caps on that premium built only from wealth and return ranges
cannot be sharp. Caps using risk-adjusted mean returns vanish
exactly when no favorable ETF trade has wealth to trade. In a
separate one-quarter statistical example, identical funded
portfolio geometry and covariances conceal different
full-history certification power. For a class of known bounded
finite laws, a second example gives matching-order worst-case history-length
bounds for certifying an unspanned-factor trade against the
optimized ETF-only class. In a third example, the ETF-only
optimizer moves between cash and the ETF; the worst-case rate
depends on both joint alpha/premium error directions. A risk-averse
example with a continuously moving ETF optimum has a smaller
exponent in the *economic advantage* margin because the active
trade shrinks at entry; in mean-signal units the testing rate is
unchanged. With positive definite return risk, a curvature
certificate extends the sufficient rate to directional costs
and binding funding or position constraints. Its matching
lower bound is class-wide and uses the zero-cost example.
When the shock law is unknown but bounded, certifying each
ETF-only comparison separately from its range already attains
the known-law worst-case order in the moving-comparator example,
and no joint or variance-adaptive rule improves that order.
Finally, a two-stage procedure that first sets a target factor
exposure and then chooses funds, charging for distance from the
target, is the joint problem at the premia the target implies. Its
loss is at most the first stage's constraint multiplier applied to
the exposure difference, and it vanishes when the unconstrained
target is admissible. If instead the funds must deliver the target
exposure exactly, the loss equals the gain in the best residual
outcome from moving the exposure, less the factor objective's loss.
Separation is exact when that residual value is maximized at the
factor target. A funded long-only menu with manager-borne exposure
makes that value depend on the exposure, which a feasibility check
on the target does not detect. Back in the statistical model, the
optimized ETF-only comparator is exactly a finite set of fixed
holdings when the score is linear, and under a curved score exactly
when the ETF-only optimizer does not move on the parameter domain.
Appendix A records the machine-checked scope.

## 1. Introduction

An investor may want to change an active mutual fund because its
expected manager contribution, factor exposure or risk has changed.
Manager alpha is the fund's expected return beyond its specified
economic factor exposures, net of internal fund costs.
An exchange-traded fund can offer another way to adjust exposure.
The relevant comparison is with the *best feasible* exchange-traded-fund
trade while leaving active holdings fixed. A spanning calculation
alone can miss an unaffordable or prohibited replacement.

The analysis below first fixes the accounting language for a
quarterly review, then studies a one-quarter model with one active
fund, one or two exchange-traded funds and two economic factors.
Both trading classes share one cash budget, long-only holdings and
explicit position limits. Purchase and sale costs may differ, and
exchange-traded-fund fee and tracking drag may have either sign.
The investor has a joint belief about conditional factor premia and
manager alpha. The model keeps realized-return risk, uncertainty
about those conditional means, and ambiguity aversion distinct.

The accounting identities, compact-optimum arguments and exposure
test below apply standard bookkeeping, linearity and convex geometry.
The no-trade band, continuation examples and statistical certificates
also use familiar budget-multiplier, future-flexibility, testing and
curvature mechanisms. The contribution here is their explicit scope and
limits
under a common funded ETF-only comparator, including exact examples;
none establishes a general new trading or testing principle. In
particular, the statistical rates do not supersede general
bounds for identifying the best of several alternatives, known as
best-arm identification.

The present draft establishes accounting identities, attained
action-class optima, a test for feasible exposure replacement and
exact one-quarter comparisons. The assumed examples show a
strict full-trading score advantage under complete substitution, a
change in active trading after an exchange-traded fund is added, and
the conditions under which zero alpha permits non-participation.
The score averages conditional mean-variance evaluations over the
belief; dispersion of that belief has no effect when its mean stays
fixed. The examples are mathematical benchmarks, not estimated
portfolio gains. A separate two-review model lets the investor
learn from public returns. We prove finite policy attainment and
an exact continuation representation there. A second exact example
shows opposite effects of future ETF and active trading on today's
active advantage when the active fund alone supplies one factor.
The signs persist in an explicit family with small conditional
risk and partially learned alpha, although the effect still runs
through the unspanned factor. These examples do not give a
general dynamic trade boundary. A later result gives the exact
comparison that decides the sign in every instance. The value
of future ETF adjustment is bounded by the cash and ETF holdings
that today's position leaves to redeploy. In an example where
spending all cash on the active fund leaves nothing to redeploy,
the sign is reversed. A further result shows how far such bounds
can be sharpened, and where they stop deciding the sign. A statistical rule for
deciding when an active trade is justified requires the public
history law: an exact example below holds portfolio economics
and covariances fixed while changing the information available
from ETF returns. It does not give a calibrated rule for
observed portfolios. A second statistical result gives a
worst-case history-length rate for learning one factor premium
when the active fund is its only investment vehicle. The rate
is scalar mean-testing behavior in factor-premium units. A
joint-error example then shows why checking only one ETF
comparison can miss the sampling requirement when the best
ETF-only action changes with the unknown parameter. A fourth
statistical example shows that a smoothly shrinking active
trade changes how a mean-signal error translates into an
economic advantage margin. A curvature bound then controls
the optimized ETF comparator under costs and binding
constraints, while retaining the same worst-case rate over
a broader class of designs. A last statistical result drops
knowledge of the shock law, keeping only a bound on its
range: comparing with the whole ETF-only class then gives no
gain in order over checking each ETF-only comparison
separately. Returning to one quarter, two results compare a
factor-then-fund procedure with joint optimization. With a soft
exposure target, the procedure loses only through the funded
budget's effect on the target, and the loss is bounded. With the
target imposed exactly, the loss is identified exactly, and
separation fails whenever funding makes the best residual choice
depend on the exposure. A last result returns to certification and
shows when the whole ETF-only comparator reduces to finitely many
fixed comparison holdings.

## 2. Setting and standing assumptions

### General review notation

An investor reviews a portfolio at quarterly dates. In the general
notation there are \(m\) active funds, \(n\) ETFs and \(K\) economic
factors. The loading matrices \(B^A\in\mathbb R^{m\times K}\) and
\(B^E\in\mathbb R^{n\times K}\) have instruments in rows. Conditional
on a parameter \(\theta_t\), next-quarter excess returns, measured
relative to cash, have the form

$$
r^A_{t+1}=B^A f_{t+1}+\alpha_t+\epsilon^A_{t+1},
\qquad
r^E_{t+1}=B^E f_{t+1}-c^E+\epsilon^E_{t+1},
\qquad \mathbb E[f_{t+1}\mid\theta_t]=\lambda_t.
$$

The residual shocks have conditional mean zero. The active-fund
alpha \(\alpha_t\) is relative to the economic factor model and net
of internal fund expenses and manager trading effects. The economic
factors need not be tradable securities. ETF drag \(c^E\) enters ETF
returns once; zero ETF manager alpha is assumed, not perfect
tracking. The investor has a joint belief about alpha and factor
premia at the review. Public fund returns are observed whether or
not the investor owns the fund; ownership creates no information.
The eligible menu is fixed without a positive-alpha screen and does
not depend on realized future alpha.

With pre-trade dollar holdings \(x^-\), cash \(h^-\), trades \(u\)
and shareholder switching cost \(C_t(u)\), accounting at a review is
\(x^+=x^-+u\) and
\(h^+=h^--\sum_i u_i-C_t(u)\). Funded long-only trading requires
\(x^+,h^+\geq0\). For holdings \(w=(a,p)\) expressed in a common
pre-trade normalization, let \(w^-\) be the initial normalized
holding. Factor exposure is
\(b(w)=(B^A)^\top a+(B^E)^\top p\). The general one-quarter score
used for the paired mean-error identity has the form

$$
Q_t(w;\theta)=b(w)^\top\lambda+a^\top\alpha-p^\top c^E
 -\frac{\gamma}{2}w^\top\Sigma(\theta)w-C_t(w-w^-).
$$

Here \(\gamma\) is a fixed risk coefficient and \(\Sigma(\theta)\)
is the conditional return-covariance input. The cost function in the score is finite
and evaluated in the same normalized units at each compared holding.
For the funding identity, \(C_t(u)\) is a finite nonnegative amount
in dollars. The two general
identities below use only this fixed algebraic form or the dollar
funding equation; they assert no optimizer or particular return law.

### Funded one-quarter model

For the optimization results, specialize to one active fund, one
or two ETFs, two factors and one investor trade at review \(t=0\).
Positions are then held until terminal marking one quarter later,
without interim trading or a terminal liquidation charge. Cash has
gross return one, and all returns and values are in cash-account
units. The loading rows are known and fixed. The parameter
\(\theta=(\lambda_1,\lambda_2,\alpha)\) belongs to a nonempty finite
set \(\Theta\); the decision-date joint belief \(\pi\) has
nonnegative masses summing to one. Alpha and factor premia may be
dependent in that belief, and neither has a sign restriction.
The known ETF fee-and-tracking term \(c^E\) may have either sign.
The investor knows the menu, initial holdings, limits, costs,
loadings, scenario law and belief before orders are submitted, but
not the true parameter or next return scenario.

A nonempty finite scenario set \(S\) has masses \(q_s\geq0\) summing
to one, fixed across parameter values and actions. Joint factor,
active-residual and ETF-residual shocks
\((z^f_s,z^A_s,z^E_s)\) each have zero \(q\)-weighted mean; their
coordinates need not be independent. For every \(\theta\in\Theta\)
and \(s\in S\), set

$$
\begin{aligned}
f_s(\theta)&=\lambda+z^f_s,\\
r^A_s(\theta)&=B^A f_s(\theta)+\alpha+z^A_s,\\
r^E_s(\theta)&=B^E f_s(\theta)-c^E+z^E_s,\\
\mu(\theta)&=(B^A\lambda+\alpha,\ B^E\lambda-c^E),\\
\xi_s&=(B^A z^f_s+z^A_s,\ B^E z^f_s+z^E_s),
\qquad \Sigma=\sum_s q_s\xi_s\xi_s^\top .
\end{aligned}
$$

All instrument gross returns \(1+r_{i,s}(\theta)\) are strictly
positive at every parameter-scenario pair. The finite scenario law,
and hence \(\Sigma\), is fixed across \(\theta\); \(\Sigma\) may be
singular. It describes conditional realized-return risk. The belief
describes estimation uncertainty about conditional means and is not
a confidence region. No ambiguity-aversion penalty is imposed.
For any scenario quantity \(X_s\), write
\(\mathbb E_qX=\sum_s q_sX_s\) and
\(\operatorname{Var}_qX=\sum_s q_s(X_s-\mathbb E_qX)^2\),
holding \(\theta\) fixed.

Pre-trade wealth \(W^-=h^-+\sum_i x_i^->0\) has nonnegative holdings
and cash. Write
\(w^-=x^-/W^-=(a^-,p^-)\), \(k^-=h^-/W^-\),
\(v=u/W^-\) and \(w=x^+/W^-=w^-+v=(a,p)\). Thus
\(\sum_iw_i^-+k^-=1\). These are dollars divided by *pre-trade*
wealth; they are never renormalized after review costs. Each known
position limit \(\bar w_i\in[0,1]\) is in the same units, and the
initial holding satisfies it.

Each instrument has known purchase and sale rates
\(\kappa_i^+,\kappa_i^-\in[0,1)\), with no imposed ranking between
the active fund and ETFs. For a signed trade, \(v_i^+=\max(v_i,0)\)
and \(v_i^-=\max(-v_i,0)\) denote its nonnegative purchase and sale
parts, not before- and after-review holdings; \(u_i^\pm\) use the
same convention. The shareholder costs,
post-review cash and terminal marked wealth are

$$
\begin{aligned}
C_0(u)&=\sum_i(\kappa_i^+u_i^++\kappa_i^-u_i^-),
&\tau(v)&=\sum_i(\kappa_i^+v_i^++\kappa_i^-v_i^-),\\
k(w)&=k^--\sum_i v_i-\tau(v),
&W_1(w;\theta,s)&=W^-\!\left[k(w)+\sum_iw_i(1+r_{i,s}(\theta))\right].
\end{aligned}
$$

A purchase rate applies to the quoted value of holdings delivered;
a sale rate applies to the gross value removed. Costs are paid at
the review from cash and sale proceeds. Active NAV returns already
include internal fund costs; \(c^E\) is subtracted from ETF returns
once and neither is charged again in \(\tau\). Execution and
settlement at the review quote are immediate. Fixed platform fees,
load schedules, taxes, investor flows and nonlinear impact are
outside this model.

All three action classes face the same funded cash constraint:
\(F=\{w:0\leq w_i\leq\bar w_i,\ k(w)\geq0\}\) permits full
trading; \(E=\{w\in F:a=a^-\}\) permits ETF-only adjustment; and
\(N=\{w^-\}\) is no trade. Cash is \(W^-k(w)\), so neither borrowing
nor shorting is hidden in \(F\) or \(E\). The initial holding is
compliant, and no additional mandate forces an active trade. The
inequalities involving holding vectors are componentwise. The
ETF-only feasible exposure set is \(B_E=\{b(w):w\in E\}\);
its changes from the incumbent are
\(D_E=\{b(w)-b(w^-):w\in E\}\). The ETF linear span
\(L_E=\{(B^E)^\top d:d\in\mathbb R^n\}\) ignores funding, limits
and signs. An exposure in \(L_E\) need not be attainable in \(E\).

For a known risk coefficient \(\gamma\geq0\), the conditional
one-quarter score and the implementable belief-average criterion are

$$
Q_0(w;\theta)=b(w)^\top\lambda+a\alpha-p^\top c^E
 -\frac{\gamma}{2}w^\top\Sigma w-\tau(w-w^-),
\qquad
\bar Q_0(w)=\sum_{\theta\in\Theta}\pi_\theta Q_0(w;\theta).
$$

The score deducts shareholder review cost once and penalizes
conditional return variance. It does not use predictive variance
over the belief, define a statistical certificate, or solve a
multiperiod control problem. Fund returns remain public regardless
of holdings. The one-quarter results below therefore have no
continuation-value or learning conclusion.

### Funded two-review model

For the finite continuation result, keep one active fund, one or two
ETFs, two factors, the fixed loading and return formulas above, and
the same known directional shareholder rates. Reviews occur at
\(t=0\) and \(t=1\), one quarter apart, with terminal marking at
\(t=2\). There is no investor trade between reviews or terminal
liquidation charge. The unknown parameter
\(\theta=(\lambda_1,\lambda_2,\alpha)\) is fixed for both quarters
and has a finite initial belief \(\pi_0\). Conditional on \(\theta\),
the two scenarios \(s_0,s_1\) are independent draws from the same
finite law \(q\). Every specified instrument gross return
\(1+r_i(\theta,s)\) is strictly positive, including at zero-mass
parameter-scenario pairs. The menu, loadings and possibly signed
ETF drag are fixed. All-fund returns are public whether or not the
investor holds the funds, and holdings create no information.

At each review use risky *dollar* holdings \(x_t^-\), cash \(h_t^-\)
and dollar trades \(u_t\), with the funding equations in the general
review notation. Initial holdings and cash are nonnegative and
\(W_0^-=h_0^-+\sum_i x_{0,i}^->0\). The same known purchase and
sale rates in \([0,1)\) apply at both reviews:
\(C(u)=\sum_i[\kappa_i^+u_i^++\kappa_i^-u_i^-]\).
The funded full trade class \(F_t\) requires
\(x_t^-+u_t\geq0\) and
\(h_t^--\sum_i u_{t,i}-C(u_t)\geq0\).
The ETF-only class \(E_t\) also requires \(u_{t,A}=0\);
\(N_t=\{0\}\) is no trade. There are no additional concentration
limits at either review. In particular, an unchanged dollar
active holding remains allowed after return drift. All classes
face the same funding equations, with no borrowing or shorting.

Before the second order, the investor observes the first-quarter
factor realization and *all* fund returns,
\(Y_1=(f(\theta,s_0),r^A(\theta,s_0),r^E(\theta,s_0))\).
Let \(Y\) be its finite range. For \(y\in Y\), define
\(L_\theta(y)=\sum_{s:Y_1(\theta,s)=y}q_s\) and
\(P_0(y)=\sum_\theta\pi_0(\theta)L_\theta(y)\).
At \(P_0(y)>0\) the posterior is

$$
\pi_1(\theta\mid y)
 =\frac{\pi_0(\theta)L_\theta(y)}{P_0(y)}.
$$

At a zero-probability observation set the posterior to \(\pi_0\)
as a bookkeeping convention. The public observation does not
reveal \(\theta\) in general. If the root trade is \(u_0\), its
post-review cash is \(h_0^+\); marking at the observed gross
returns \(d_i(y)=1+r_i(\theta,s_0)\) gives
\(x_{1,i}^-(y;u_0)=d_i(y)(x_{0,i}^-+u_{0,i})\) and
\(h_1^-(u_0)=h_0^+\). After a second trade \(u_1(y)\),
terminal wealth on the path \((\theta,s_0,s_1)\) is

$$
W_2=h_1^+ +\sum_i x_{1,i}^+
               [1+r_i(\theta,s_1)].
$$

The investor maximizes expected terminal utility
\(U_\rho(W_2/W_0^-)=-\exp(-\rho W_2/W_0^-)\), with
\(\rho>0\) and the *initial* wealth denominator fixed across
both reviews. This is not a sum of one-quarter mean-variance
scores. The scenario law describes realized-return risk; the
initial belief and posterior describe uncertainty about fixed
conditional means. Bayesian integration of terminal utility
does not add that uncertainty to the scenario covariance or
impose ambiguity aversion.

For a root class \(D\in\{F,E,N\}\) and continuation class
\(R\in\{F,E,N\}\), let \(\Pi_{D,R}\) consist of a root trade
\(u_0\in D_0\) and one feasible trade \(u_1(y)\in R_1\) at
each \(y\in Y\). Feasibility includes zero-probability nodes.
One action per public observation prevents a policy from
distinguishing hidden histories with the same observed data.
Let \(\Phi\) be the explicit expected-utility sum

$$
\Phi(u_0,u_1)
 =\sum_{\theta,s_0,s_1}\pi_0(\theta)q_{s_0}q_{s_1}
   U_\rho\!\left(\frac{W_2(\theta,s_0,s_1;u_0,u_1)}
                       {W_0^-}\right),
\qquad
V_{D,R}=\sup_{\Pi_{D,R}}\Phi .
$$

For a nonnegative marked state \((x,h)\) and posterior \(\pi\),
write \(V_1^R(x,h,\pi)\) for the supremum of conditional expected
terminal utility over \(R_1(x,h)\), retaining the same \(W_0^-\),
\(\rho\), return law and costs. For a feasible root trade define

$$
H_0^R(u_0)=
\sum_{y:P_0(y)>0}P_0(y)
V_1^R\!\left(x_1^-(y;u_0),h_1^-(u_0),
                  \pi_1(\cdot\mid y)\right).
$$

The equality of the policy value to an attained maximum of
\(H_0^R\) is a result below, rather than part of this definition.
Where \(V_{D,R}<0\), express values in units of initial wealth by
\(CE_{D,R}=-\rho^{-1}\log(-V_{D,R})\). For fixed continuation
class, set \(\Delta_R=CE_{F,R}-CE_{E,R}\). The continuation
classes compare future full trading, ETF-only adjustment and
no second trade under identical observations and return laws.
Restricting today's active trade does not ban an active trade
at the second review when \(R=F\).

### Repeated-sampling certification model

For a separate one-quarter statistical comparison, retain the funded
classes \(F,E\) and conditional score \(Q(w;\theta)\) above. The
factor premia and alpha form a fixed unknown parameter
\(\theta_*=(\lambda_*,\alpha_*)\) in a known domain
\(\Theta\), the convex hull of finitely many vertices. Loadings,
ETF drag, the centered finite shock law,
realized-return covariance \(\Sigma\), initial portfolio, limits,
costs and score coefficient are known. Before one quarterly
decision, observe \(N\geq1\) independent public records, each
containing the factor realizations and every fund return. The
same \(\theta_*\) governs all records and the following holding
quarter; observations do not depend on ownership.

Let \(X_l=(f_l,r_l^A-B^Af_l)\), write
\(\widehat\theta_N=N^{-1}\sum_lX_l\), and let
\(\zeta_s=(z_s^f,z_s^A)\) and
\(\Omega=\sum_s q_s\zeta_s\zeta_s^\top\).
ETF returns are public but do not enter this sample-mean
estimator. \(\Omega\) describes mean-estimation error; it is
not added to the realized-return covariance \(\Sigma\) in
\(Q\). For an error allowance \(\eta\in(0,1)\), the prescribed
confidence set uses the finite-law \((1-\eta)\)-quantile
\(t_{N,\eta}\) of
\(T_N=N e_N^\top\Omega^\dagger e_N\), where
\(e_N=N^{-1}\sum_l\zeta_{s_l}\) and
\(\Omega^\dagger\) is the Moore--Penrose inverse:

$$
C_N=\Theta\cap\{\widehat\theta_N-e:
e\in\operatorname{Im}(\Omega),\quad
N e^\top\Omega^\dagger e\leq t_{N,\eta}\}.
$$

For a feasible candidate \(w\), compare it with the *optimized*
ETF-only class at the same parameter:

$$
\operatorname{Adv}(w;\theta)
 =Q(w;\theta)-\sup_{v\in E}Q(v;\theta),\qquad
L_N(w)=\inf_{\theta\in C_N}\operatorname{Adv}(w;\theta).
$$

If \(C_N\) is empty, set \(L_N=-\infty\) and fall back to an
ETF-only action. The prescribed gate selects full and ETF-only
maximizers at \(\widehat\theta_N\) and certifies the selected
active trade only when its valid lower bound on \(L_N\) exceeds
the stated threshold. The example below uses threshold zero
and the exact value \(L_N\). A feasible point in the minimization
gives an upper bound on \(L_N\), not a certificate. This is a
frequentist repeated-sampling decision at one review, with no
Bayesian prior or ambiguity penalty and no multiperiod guarantee.

### Multi-review tracking model

For the last result, iterate the one-quarter score over many
quarterly reviews and study how the best holding follows a moving
target. There are \(n\geq1\) instruments, active funds and ETFs
indexed together, reviewed at \(t=0,1,\ldots,T-1\) and marked at \(T\)
without a terminal trade. A public state \(z_t\) in a finite set is
known at review \(t\). Given \(z_t=z\), the next state and the vector
\(g\) of instrument gross returns over the quarter have a known finite
law \(q_t(z',g\mid z)\), with every \(g_i>0\). The law does not depend on
holdings or trades. A known belief-mean function \(\mu(t,z)\) gives
next quarter's expected excess returns, built from loadings, premia,
alphas and ETF drag as in (1). The model takes this function as given
and does not specify how beliefs are formed. The return covariance
\(\Sigma\) is constant and positive definite, \(\gamma>0\), and future
quarters are discounted by \(\beta\in(0,1]\).

Holdings are in dollars. Before review \(t\) the investor holds
\(x^-_t\geq0\) and cash \(h^-_t\), trades \(u_t\) to
\(x^+_t=x^-_t+u_t\), and pays the directional cost
\(C(u)=\sum_i[\kappa^+_iu_i^++\kappa^-_iu_i^-]\) with rates in \([0,1)\).
Holdings are then marked, \(x^-_{t+1}=x^+_t\circ g_{t+1}\) coordinatewise.
Post-trade holdings must satisfy dollar caps \(0\leq x^+_t\leq\bar x\)
and, in general, keep cash nonnegative. In a *slack-budget* instance,
initial cash is large enough, \(h^-_0\geq T\sum_i(1+\kappa^+_i)\bar x_i\),
that the cash constraint never binds. The investor maximizes the
expected discounted sum of one-quarter belief-mean scores,
\(\mathbb E\sum_t\beta^t[\mu(t,z_t)^\top x^+_t-(\gamma/2)x^{+\top}_t\Sigma
x^+_t-C(u_t)]\). This is a sum of quarterly scores, not a
terminal-utility problem.

The *frictionless target* is \(x^*(t,z)=\Sigma^{-1}\mu(t,z)/\gamma\), the
one-quarter optimum without costs or caps; it may be negative or
exceed a cap. Since
\(\mu^\top x-(\gamma/2)x^\top\Sigma x\) equals a term free of \(x\) minus
\((\gamma/2)(x-x^*)^\top\Sigma(x-x^*)\), maximizing the objective is the
same as minimizing the expected discounted tracking loss
\((\gamma/2)(x^+_t-x^*_t)^\top\Sigma(x^+_t-x^*_t)\) plus costs. With
\(X=\prod_i[0,\bar x_i]\), \(V_T=0\) and, for \(t<T\), the *stay
objective*

$$
G_t(x,z)=\frac\gamma2(x-x^*(t,z))^\top\Sigma(x-x^*(t,z))
 +\beta\sum_{(z',g')}q_t(z',g'\mid z)\,V_{t+1}(x\circ g',z'),
$$

the minimal remaining loss from a pre-trade holding \(x\) is
\(V_t(x,z)=\min_{x'\in X}[C(x'-x)+G_t(x',z)]\), and the optimal
post-trade holding \(x^+_t(x,z)\) is the minimizer. The *no-trade set*
\(NT_t(z)\) collects the holdings \(x\in X\) with \(x^+_t(x,z)=x\).

### Fund-of-funds learning model

The last result studies a larger, stylized problem with learning. It
drops the funded long-only budget on purpose, as a declared
counterfactual, so its optimal policy is not implementable by a
long-only fund of funds. There are \(N\) active funds, \(M\) ETFs and
\(K\) factors, reviewed quarterly at \(t=0,\ldots,T-1\). Excess returns
over a quarter are

$$
f=\lambda+z^f,\qquad r^A=B^Af+\alpha+z^A,\qquad r^E=B^Ef-c^E+z^E,
$$

with known loadings \(B^A\), \(B^E\) and ETF drag \(c^E\), and shocks
\(z=(z^f,z^A,z^E)\) that are Gaussian with known positive definite
covariance \(\Sigma_z\), independent across quarters. The premia
\(\lambda\) and alphas \(\alpha\) are fixed and unknown. The prior on
\(\theta=(\lambda,\alpha)\) is Gaussian. In the *reference case* the
premium and alpha blocks of the prior are independent, \(\Sigma_z\) is
block diagonal, and fund residuals are independent. All fund returns
are public, so beliefs \(N(m_t,P_t)\) are updated by the Kalman filter
from public returns whatever the investor holds. With
\(G=[[B^A,I_N];[B^E,0]]\), the predictive mean and covariance of next
quarter's instrument returns are
\(\mu_t=Gm_t-(0,c^E)\) and \(\Sigma_t=GP_tG^\top+\Sigma_r\), where \(\Sigma_r\)
is the return covariance implied by \(\Sigma_z\). \(\Sigma_t\) adds
estimation risk to return risk, so this model, unlike the one-quarter
model, charges estimation uncertainty through predictive variance.

Positions \(x_t\in\mathbb R^n\), \(n=N+M\), are dollars after the review
and may be negative. A trade \(u_t=x_t-x_{t-1}\) costs
\(\tfrac12u_t^\top\Lambda u_t\) with \(\Lambda\) symmetric positive definite
and instrument-specific; the reference case is
\(\Lambda=\operatorname{diag}(\lambda_AI_N,\lambda_EI_M)\). For \(\gamma>0\) and a
discount \(\rho\in(0,1]\), the investor maximizes

$$
\mathbb E_0\sum_{t=0}^{T-1}\rho^t\Bigl[x_t^\top\mu_t-\frac\gamma2x_t^\top\Sigma_tx_t
 -\frac12u_t^\top\Lambda u_t\Bigr],
$$

a sum of quarterly certainty equivalents under the predictive moments,
net of trading costs. The *Markowitz portfolio*
\(\mathrm{Mk}_t=(\gamma\Sigma_t)^{-1}\mu_t\) maximizes one quarter's
certainty equivalent without costs.

### Learning-driven tracking model

The multi-review tracking model takes its target as given. Its
*learning-driven* version specifies the target: it is the Markowitz
portfolio of the fund-of-funds learning model,
\(x^*_t=(\gamma\Sigma_t)^{-1}\mu_t\), with that model's instruments, prior,
filter and predictive moments, and the fixed-means case. Costs,
long-only caps and the objective are those of the multi-review
tracking model, with the constant covariance replaced by the
predictive \(\Sigma_t\). In its *finite-law variant*, the premia and alphas
are drawn once from a finite law with the prior's mean and covariance,
and each quarter's shock from a finite centered law with the shocks'
covariance, so all gross returns are positive and the public state is
the finite history of observations. The manager runs the same linear
filter, which is then the best linear predictor rather than the exact
posterior. This variant is an exact evaluation device, not a claim
that returns have finite support.

The target moves for two reasons:

$$
x^*_{t+1}-x^*_t=(\gamma\Sigma_{t+1})^{-1}G\epsilon_{t+1}
 +\bigl[(\gamma\Sigma_{t+1})^{-1}-(\gamma\Sigma_t)^{-1}\bigr]\mu_t,
$$

a belief-mean innovation \(\epsilon_{t+1}=m_{t+1}-m_t\), with covariance
\(V_t=P_t-P_{t+1}\), and a *learning drift*, known at \(t\), from the falling
risk charge.

## 3. Main results

Estimated factor premia can affect a comparison between two fixed
portfolios differently from an estimate of manager alpha.

**Proposition 1 (Paired mean-error identity; general review notation; machine checked).** Consider two fixed
holdings \(w=(a,p)\) and \(v=(a_v,p_v)\), expressed in the same pre-trade normalization.
Evaluate the one-quarter score \(Q_t\) at both holdings, then evaluate it again as
\(\widehat Q_t\) after replacing only the factor premia \(\lambda\) and active-fund
alpha \(\alpha\) by \(\widehat\lambda\) and \(\widehat\alpha\). Keep the loadings,
ETF drag, risk coefficient, covariance matrix, pre-trade holdings and switching-cost
function identical in all four evaluations, and assume the evaluated costs are finite.
Then

\[
\begin{aligned}
&[\widehat Q_t(w)-\widehat Q_t(v)]-[Q_t(w)-Q_t(v)]\\
&\quad= [b(w)-b(v)]^\top(\widehat\lambda-\lambda)
       +(a-a_v)^\top(\widehat\alpha-\alpha). \tag{1}
\end{aligned}
\]

The factor-premium term is zero for every real factor-premium error if and only if
\(b(w)=b(v)\). Under that exposure match, the paired error is exactly the alpha-error
term; if \(a=a_v\) too, it is zero. For one particular factor-premium error, the term
can vanish even when exposures differ; for a restricted set of errors, the converse
need not hold.

The identity follows by subtracting the two scores at each fixed holding: ETF drag,
return risk and switching costs cancel, leaving the two mean-error terms. For the
universal cancellation condition, take the factor-premium error equal to
\(b(w)-b(v)\); its squared length is zero only when the exposure difference is zero.

This is an algebraic result. It does not
assert that a feasible exposure-matching pair exists or that the comparator remains
optimal when means change. It gives no probability bound or multiperiod decision rule.
See Appendix A for the machine-checked scope.

For an investor, matching factor exposure removes one source of
mean-estimation error from a fixed portfolio comparison. It does not
show that such a match is affordable or that either portfolio should
be traded. The cancellation is bilinearity of a fixed score, not a
new estimation theorem.

Every comparison of trading choices must first charge shareholder
costs to the same pool of available cash.

**Proposition 2 (Self-financing at a quarterly review; general review notation; machine checked).**
Let \(x^-\) be nonnegative initial dollar holdings in finitely many active funds and ETFs,
let \(h^-\geq 0\) be cash, and let \(u\) be any trade vector. For a finite, nonnegative
shareholder switching cost \(C_t(u)\), define \(x^+=x^-+u\) and
\(h^+=h^--\sum_i u_i-C_t(u)\). Then

\[
\sum_i x_i^+ + h^+ + C_t(u)=\sum_i x_i^- + h^-. \tag{2}
\]

The funded long-only restrictions \(x_i^+\geq0\) for every instrument and
\(h^+\geq0\) hold exactly when

\[
x_i^-+u_i\geq0\quad\text{for every }i,
\qquad
\sum_i(x_i^-+u_i)+C_t(u)\leq\sum_i x_i^-+h^-. \tag{3}
\]

For a trade satisfying these restrictions,
\(0\leq C_t(u)\leq\sum_i x_i^-+h^-\). If \(C_t(0)=0\), the zero trade
is feasible under these funding restrictions and leaves holdings and cash unchanged.
Additional mandates can still restrict trading.

To see (2), sum \(x_i^+=x_i^-+u_i\) and substitute the post-trade cash
definition; the trade and cost terms cancel. Rearranging the equality gives the
budget inequality in (3), while the holdings definition gives its coordinate
restriction. Nonnegative post-trade holdings and cash give the cost bound. This result
concerns accounting at one review. It does not establish a return, a trading score,
an optimal policy, or a transfer to a later model version.

The identity says that a trading cost reduces the resources left for
holdings and cash by exactly the amount paid. It gives no reason to
prefer an active-fund trade over an ETF adjustment. It is the usual
self-financing bookkeeping identity specialized to this review.

In the one-quarter model, the score must agree with the wealth and
cost accounting before it can be optimized.

**Proposition 3 (Score accounting and belief mean; funded one-quarter model; machine checked).**
Use the funded one-quarter model of Section 2: positive pre-trade wealth \(W^-\),
separate purchase and sale switching-cost rates, a finite centered return-scenario
law that is fixed across parameter values, known loadings and signed ETF drag,
and a finite joint belief \(\pi\) about factor premia and active-fund alpha.
For a feasible holding \(w=(a,p)\), set \(v=w-w^-\) and
\(G_s(w;\theta)=W_1(w;\theta,s)/W^--1\). The dollar and normalized cost definitions,
funding equation and terminal marking give

\[
\begin{aligned}
C_0(W^-v)/W^- &= \tau(v),\\
\sum_i w_i+k(w)+\tau(v) &= 1,\\
G_s(w;\theta) &= w^\top r_s(\theta)-\tau(v). \tag{4}
\end{aligned}
\]

With \(\mathbb E_q\) and \(\operatorname{Var}_q\) taken over scenarios at a fixed
\(\theta\), the conditional moments and one-quarter score satisfy

\[
\begin{aligned}
\mathbb E_q G(w;\theta)&=w^\top\mu(\theta)-\tau(v),\\
\operatorname{Var}_q G(w;\theta)&=w^\top\Sigma w,\\
Q_0(w;\theta)&=\mathbb E_q G(w;\theta)
              -\frac{\gamma}{2}\operatorname{Var}_q G(w;\theta). \tag{5}
\end{aligned}
\]

Thus the review cost enters normalized conditional expected gain once. If
\(\bar\theta=(\bar\lambda,\bar\alpha)\) is the belief mean, finite averaging gives

\[
\bar Q_0(w)=b(w)^\top\bar\lambda+a\bar\alpha-p^\top c^E
 -\frac{\gamma}{2}w^\top\Sigma w-\tau(v)
 =Q_0(w;\bar\theta). \tag{6}
\]

Evaluation at \(\bar\theta\) uses the same affine formula; \(\bar\theta\) need not
belong to the finite parameter support. Its scenario gross returns remain positive.
Two beliefs on that support with the same mean and all other inputs fixed therefore
give identical scores and rankings at every holding, and identical sets of maximizers
on the full-trading, ETF-only and no-trade action classes, whether or not a maximum is
attained. The result follows from positive homogeneity of the trade parts, the
self-financing equation, centered scenario shocks and linearity of finite belief
averages.

This score uses conditional return risk, not predictive variance over the belief.
Belief dispersion or dependence at a fixed mean cannot change its rankings; the result
adds no ambiguity-aversion penalty, optimizer-existence claim or multiperiod policy.
Its directional cost rates do not represent an actual load schedule or redemption
window without further assumptions.

Economically, this score responds to a changed belief *mean*, but not
to greater uncertainty or a changed dependence pattern at fixed
means. A decision effect from those features needs another
criterion or a model with learning; this proposition provides
neither. The dependence on the mean follows from finite averaging of
an affine score, not a general result about learning.

The best ETF-only and full-trading scores are meaningful only if
feasible optimal holdings exist in both classes.

**Proposition 4 (Attained optimal actions in nested classes; funded one-quarter model; machine checked).**
Suppose the nonnegative initial holdings in Section 2's funded one-quarter
model satisfy the position limits, initial
cash is nonnegative, and pre-trade wealth is positive. The purchase and sale cost
rates, scenario masses, belief masses and risk coefficient have the stated nonnegative
values. With the same funded cash function \(k(w)\) in every class, define

\[
F=\{w:0\leq w_i\leq\bar w_i\ \text{for every }i,\ k(w)\geq0\},
\quad E=\{w\in F:a=a^-\},\quad N=\{w^-\}. \tag{7}
\]

Then \(N\subseteq E\subseteq F\), and all three classes are nonempty, closed,
bounded and convex. The belief-average one-quarter score \(\bar Q_0\) is continuous
and concave in holdings. It attains a finite maximum on each class; writing
\(V_D=\max_{w\in D}\bar Q_0(w)\) for \(D\in\{N,E,F\}\),

\[
V_N\leq V_E\leq V_F. \tag{8}
\]

The initial holding belongs to every class because \(\tau(0)=0\). Nonnegative
purchase and sale rates make the directional cost convex and the post-trade cash
function concave; these facts preserve the funded constraint under convex
combinations. Nonnegative scenario masses make the return-risk quadratic convex,
and nonnegative belief masses preserve concavity under averaging. Its negative
risk and cost contributions therefore make the score concave.
The classes are closed subsets of a finite position-limit box, and continuity
gives attainment. Inclusion then gives (8).

The inequalities may be equalities. The result gives neither a unique optimal
action nor a strict advantage from active-fund trading. It covers the one-quarter
score under Section 2's fixed menu and compliant initial position, with no forced active
trade or additional mandate; it is not a multiperiod policy or a performance claim.

This guarantees that the investor can compare attained one-quarter
benchmarks under the same budget. The weak ordering alone says
nothing about the size, or even the existence, of an active-trading
advantage. Attainment is the compact-set extreme-value argument;
nesting gives the ordering.

Before comparing scores, we need to know which factor-exposure
changes an ETF-only trade can actually finance.

**Proposition 5 (ETF-only exposure geometry; funded one-quarter model; machine checked).**
Fix the funded one-quarter model's one active fund, one or two ETFs and
two factors, with a compliant
nonnegative initial holding, nonnegative initial cash, position limits and
purchase and sale rates in \([0,1)\). All actions use the same funded cash
constraint. Write \(p^-\) for initial ETF holdings, \(\bar p\) for their limits,
\(k^-\) for initial cash, and \(d=p-p^-\) for an ETF trade. Its net cash
outlay and feasible trade set are

$$
\begin{aligned}
\Psi_E(d)&=\sum_j\bigl[d_j+\kappa^+_{E,j}\max(d_j,0)
                         +\kappa^-_{E,j}\max(-d_j,0)\bigr],\\
P_E&=\{d:-p^-\leq d\leq\bar p-p^-,\ \Psi_E(d)\leq k^-\}.
\end{aligned}                                           \tag{9}
$$

For each purchase-or-sale assignment \(\sigma\) across the ETFs, let
\(c_{\sigma,j}=1+\kappa^+_{E,j}\) on a purchase and
\(c_{\sigma,j}=1-\kappa^-_{E,j}\) on a sale. Then
\(\Psi_E(d)=\max_\sigma c_\sigma^\top d\), so the last condition in (9)
is exactly the finite system \(c_\sigma^\top d\leq k^-\) for every
\(\sigma\). In particular, sales may have negative net outlay and finance
another ETF purchase. With \(b(w)=(B^A)^\top a+(B^E)^\top p\),

$$
E=\{(a^-,p^-+d):d\in P_E\},\quad
D_E=(B^E)^\top P_E,\quad B_E=b(w^-)+D_E.                 \tag{10}
$$

The sets \(P_E\), \(D_E\) and \(B_E\) are nonempty, closed, bounded and convex.
The zero trade lies in \(P_E\) and \(D_E\), the incumbent exposure lies
in \(B_E\), and \(D_E\subseteq L_E=\{(B^E)^\top d:d\in\mathbb R^n\}\).
A target exposure change \(\delta\) has an ETF-only match if and only if
there is a \(d\) satisfying

$$
(B^E)^\top d=\delta,\qquad
-p^-\leq d\leq\bar p-p^-,\qquad
c_\sigma^\top d\leq k^-\quad\text{for every }\sigma.    \tag{11}
$$

If \(\delta\notin L_E\), the direction is missing from the ETF span.
Within that span, the position bounds can rule out every solution; if
some bounded solution exists but none meets all cash inequalities,
funding rules out a match, possibly together with the bounds. The test
examines every solution of the exposure equation.

For one ETF, the entire trade set is the interval
$$
P_E=\left[-p^-,\
\min\left\{\bar p-p^-,\,\frac{k^-}{1+\kappa^+_E}\right\}\right].
                                                        \tag{12}
$$
Its exposure image is this interval times the ETF loading vector,
including \(\{0\}\) for a zero loading. For two ETFs with invertible
\((B^E)^\top\), \(L_E=\mathbb R^2\); the unique candidate
\(d=((B^E)^\top)^{-1}\delta\) matches exactly when it passes the bounds
and cash inequalities in (11). Thus full linear span alone gives no
feasible-substitution conclusion. For any full action \(w=(a,p)\) with
\(a\ne a^-\), its exposure change is outside \(L_E\) exactly when the
active loading \((B^A)^\top\) is outside \(L_E\); if \(a=a^-\), the action
itself is an ETF-only match.

For each ETF, net outlay is the maximum of
\((1+\kappa^+_{E,j})d_j\) and \((1-\kappa^-_{E,j})d_j\).
Summing these maxima gives the finite cash inequalities. Substituting
\(a=a^-\) in Section 2's cash equation gives \(k(a^-,p^-+d)=k^--\Psi_E(d)\)
and proves (10)--(11). The position box and finite inequalities make
\(P_E\) compact and convex; its linear image and translation have the
same properties. The special cases follow by solving the one-dimensional
cash bound or the invertible exposure equation.

This is a one-quarter feasibility result. Exposure matching does not
establish equal returns, residual risk, costs, cash or score, and an
unmatched feasible full action need not outperform ETF-only trading.
The result gives no value gap, economic magnitude, optimal trade
direction or extension to another model version.

For portfolio construction, an ETF loading matrix can span the
desired factors while the required trade still violates holdings
limits or the cash budget. The test identifies that obstruction,
but an exposure match alone does not establish equal investment
value. This is a bounded linear-image feasibility test from standard
finite-dimensional convex geometry.

The first exact example asks whether complete feasible exposure
replacement removes every reason to hold the active fund.

**Proposition 6 (Complete feasible exposure substitution with active-trading advantage; funded one-quarter model; machine checked).**
The following is one assumed instance of the funded one-quarter model.
There is one active fund and one ETF, two factors and one quarterly review.
Pre-trade wealth and cash are one, both initial fund holdings are zero, and
both position limits are one. The two instruments have the same loading
\((1,0)\), ETF drag is zero, every purchase and sale rate is \(1/100\), and
\(\gamma=1\). The belief assigns mass \(1/2\) to each parameter point
\((\lambda,\alpha)=((1/100,0),0)\) and
\(((3/100,0),1/50)\). Two equiprobable scenarios have factor shocks
\((1/10,0)\) and \((-1/10,0)\), with zero residual shocks. All instrument
gross returns are positive.

Write \(t=a+p\) for total risky holdings. The identical funded budget in
both action classes gives

$$
\begin{aligned}
F&=\{(a,p):a,p\geq0,\ a+p\leq100/101\},\\
E&=\{(0,p):0\leq p\leq100/101\},\qquad N=\{(0,0)\},\\
B_E&=D_E=\{(t,0):0\leq t\leq100/101\}.
\end{aligned}                                                   \tag{13}
$$

Every \((a,p)\in F\) has the feasible ETF-only replacement \((0,t)\in E\).
The pair has the same exposure \((t,0)\), conditional variance \(t^2/100\),
review cost \(t/100\), and post-review cash \(1-(101/100)t\). Thus exposure
substitution is complete and feasible here, although the second factor is
outside the span of both instruments. The belief-average scores satisfy

$$
\bar Q_0(a,p)=\frac{t}{100}+\frac{a}{100}-\frac{t^2}{200},
\qquad
\bar Q_0(a,p)-\bar Q_0(0,t)=\frac{a}{100}.              \tag{14}
$$

| Class | Unique maximizing holding \((a,p)\) | Cash | Review cost | One-quarter score |
|---|---:|---:|---:|---:|
| \(N\) | \((0,0)\) | \(1\) | \(0\) | \(0\) |
| \(E\) | \((0,100/101)\) | \(0\) | \(1/101\) | \(51/10201\) |
| \(F\) | \((100/101,0)\) | \(0\) | \(1/101\) | \(152/10201\) |

The two nonzero optima have the same exposure, but the full-minus-ETF-only
optimal score gap is

$$
V_F-V_E=\frac{1}{101}>0.                                \tag{15}
$$

Both trades are purchases from cash, so the shared review cost is \(t/100\)
and the cash constraint is \(t\leq100/101\). The return covariance has every
entry \(1/100\). Belief averaging gives mean factor premium \(1/50\) in the
first factor and mean alpha \(1/100\), which yields (14). At the first
parameter point the matched conditional-score difference is zero; at the
second it is \(a/50\). Thus the average difference uses the decision-date
belief, not knowledge of the realized parameter. On \(E\), the score
\(t/100-t^2/200\) increases strictly over its allowed interval. For each
fixed \(t\) in \(F\), the score is uniquely largest at \(a=t,p=0\), and
the resulting \(t/50-t^2/200\) also increases strictly. This proves the
unique maximizers and the exact gap. In this instance that gap is the
positive belief-mean alpha times the full optimum's active holding; matched
exposures, return risk, cash and review costs contribute no difference.

This is a one-quarter score example with assumed means, belief, shocks and
costs. It establishes neither a calibrated magnitude nor a realized or
multiperiod wealth advantage. The second factor is unused, residual risk
is zero and the covariance is singular. It is not a zero-alpha replication
result, and it gives no conclusion for other initial holdings, unequal
costs, binding ETF limits or another model version.

The investor can buy an ETF with the same factor exposure and risk,
yet the active fund has a higher believed return in this assumed
case. The positive one-quarter score gap is an alpha comparison,
not evidence that the active fund will outperform in realized
returns. Its equal-exposure accounting is the fixed-portfolio
linearity in Proposition 1, illustrated by assumed numbers.

An ETF added to the menu changes feasible adjustments and can also
change which active-fund trade is optimal.

**Proposition 7 (An added ETF and incomplete feasible substitution; funded one-quarter model; machine checked).**
Consider two assumed menus in the funded one-quarter model that differ
only by a second ETF, initially
held at zero. Pre-trade wealth is one, with active holding \(a^-=1/2\), first
ETF holding \(p^-_1=1/3\), and cash \(k^-=1/6\). All position limits are one,
all purchase and sale rates are \(1/2000\), and \(\gamma=1\). The singleton
parameter support has \(\lambda=(1/50,1/200)\) and \(\alpha=-1/400\); the
active fund stays eligible. The fixed instrument inputs are:

| Instrument | Factor loading | Residual shock size | ETF drag | Initial holding |
|---|---:|---:|---:|---:|
| Active fund | \((1,1/2)\) | \(3/100\) | none | \(1/2\) |
| First ETF | \((1,0)\) | \(1/200\) | \(-1/10000\) | \(1/3\) |
| Second ETF, when available | \((1,1/4)\) | \(1/100\) | \(0\) | \(0\) |

The scenario law gives equal mass to all 32 combinations of five independent
signs. The signs multiply factor shock sizes \(3/50,1/50\) and the three
residual sizes in the table. The last sign is unused in the one-ETF menu,
so the shared instruments have the same return law in both menus. Every
instrument has positive gross return in every scenario. The two-ETF
conditional mean and covariance are

$$
\mu=\left(\frac1{50},\frac{201}{10000},\frac{17}{800}\right),
\qquad
\Sigma=\frac1{40000}
\begin{pmatrix}184&144&146\\144&145&144\\146&144&149\end{pmatrix}.
                                                               \tag{16}
$$

The one-ETF covariance is the leading two-coordinate submatrix. With
\(w^-\) appropriate to each menu, both classes use
\(\sum_i w_i+\tau(w-w^-)\leq1\), and the belief-average score is
\(\bar Q_0(w)=\mu^\top w-\tfrac12w^\top\Sigma w-\tau(w-w^-)\).
Their unique maximizers are:

| Menu and class | Holding | Cash | Review cost | One-quarter score |
|---|---:|---:|---:|---:|
| One ETF, \(N\) | \((1/2,1/3)\) | \(1/6\) | \(0\) | \(11033/720000\) |
| One ETF, \(E\) and \(F\) | \((1/2,3001/6003)\) | \(0\) | \(1/12006\) | \(61830113/3427920000\) |
| Two ETFs, \(N\) | \((1/2,1/3,0)\) | \(1/6\) | \(0\) | \(11033/720000\) |
| Two ETFs, \(E\) | \((1/2,0,2999/6003)\) | \(0\) | \(5/12006\) | \(2104284079/115315228800\) |
| Two ETFs, \(F\) | \((0,0,11995/12006)\) | \(0\) | \(11/12006\) | \(8512677811/461260915200\) |

Thus the full-minus-ETF-only optimal score gap is zero with one ETF and

$$
V_F-V_E=\frac{6369433}{30750727680}>0
\quad\text{with two ETFs}.                                    \tag{17}
$$

Both menus' \(E\) and \(F\) optima beat no trade. With one ETF, the optimum
buys \(1000/6003\) of that ETF and makes no active trade; it is ETF-only
trading, not no trade. Adding the second ETF changes the optimal active
trade to a sale of \(1/2\).

The exposure facts are distinct. In the one-ETF menu, selling all holdings
is a feasible full action with exposure change \((-5/6,-1/4)\), outside the
ETF span, although the optimal gap is zero. In the two-ETF menu the loading
rows span \(\mathbb R^2\). Matching its full optimum while fixing
\(a=1/2\) uniquely requires ETF **holdings**
\((p_1,p_2)=(1/2,-11/12006)\). The second holding violates
nonnegativity, so no feasible ETF-only action matches that optimum's
exposure despite full linear span.

For the optimality check, independent centered signs give (16), whose
quadratic form is positive definite because each instrument has a positive
residual-square term. At each proposed optimum, the funded budget binds.
A directional-cost subgradient and a nonnegative budget multiplier give,
for any feasible comparator \(z\) in the same class, a score difference
bounded above by a position-bound residual with the correct sign minus
\(\tfrac12(z-w)^\top\Sigma(z-w)\). The residual vanishes at interior
coordinates and has the sign required at zero holdings. Hence every
distinct comparator scores strictly less; direct substitution gives the
table and (17). The one-ETF missing direction and two-ETF prohibited short
then follow by solving the exposure equations.

All means, costs and risks here are assumed. The strict gap is a
one-quarter score comparison, not a calibrated effect or a multiperiod
policy. The two-ETF gap is not attributed solely to the shorting
obstruction: alpha, residual risks and traded amounts also differ between
the optima. No global claim that adding an ETF increases active trading
or the class gap follows from these two instances.

The added ETF makes a sale of the active fund optimal in this
assumed case, even though the expanded ETF menu spans both factors.
The ETF-only exposure match would require a short position, and
the example gives no general prediction for what another ETF
addition would do. A long-only bound defeating an otherwise available
linear replication is a standard constrained-replication mechanism;
the result here is the exact funded example and its optimal actions.

A zero-alpha benchmark tests when an ETF can replace an active
fund without losing return or increasing conditional risk.

**Proposition 8 (Zero-alpha non-participation under feasible, costless ETF replacement; funded one-quarter model; machine checked).**
Consider an instance of the funded one-quarter model with one active
fund and one ETF, a compliant
initial holding \((a^-,p^-,k^-)\), equal loading rows \(B^A=B^E\), zero
ETF drag, free ETF purchases and sales, and ETF position limit
\(\bar p=1\). The active fund may have directional purchase and sale
costs and a position limit. Assume the belief-mean alpha
\(\bar\alpha=0\). With centered conditional return shocks \(\xi_A\)
and \(\xi_E\), put \(\varepsilon_s=\xi_{A,s}-\xi_{E,s}\) and
\(v_\varepsilon=\sum_s q_s\varepsilon_s^2\). Assume additionally
\(\sum_s q_s\xi_{E,s}\varepsilon_s=0\). Finally, suppose either
(A) \(a^-=0\), or (B) the active sale rate is zero. Then, for every
\(w=(a,p)\in F\), the holding \(T(w)=(0,a+p)\) is in \(F\), has the
same factor exposure and zero review cost, and satisfies

$$
\begin{aligned}
k(T(w))-k(w)&=\tau(w-w^-),\\
\bar Q_0(T(w))-\bar Q_0(w)
  &=\tau(w-w^-)+\frac{\gamma}{2}a^2v_\varepsilon\geq0.
\end{aligned}                                                     \tag{18}
$$

Thus \(F\) has an optimum with no active holding. Under (A), the
replacement also lies in \(E\), so \(V_F=V_E\). Every full-class
optimum then has \(a=0\) if the active purchase rate is positive
*or* \(\gamma v_\varepsilon>0\). Under (B), every full-class optimum
has \(a=0\) when \(\gamma v_\varepsilon>0\). If an incumbent has
\(a^->0\), this liquidation is a full-trading action and cannot
belong to \(E\), which fixes the active holding.

The score conclusion uses belief-mean zero alpha; it does not assert
equal realized returns. If alpha is zero at every parameter point
and \(\varepsilon_s=0\) in every scenario, the two instruments instead
have equal returns pointwise, and

$$
W_1(T(w);\theta,s)-W_1(w;\theta,s)
   =W^-\tau(w-w^-)\quad\text{for every }\theta,s.                 \tag{19}
$$

To see (18), the common loading and zero drag make the belief-mean
return difference zero. Writing \(t=a+p\), the risky return shock is
\(t\xi_E+a\varepsilon\); the zero cross-moment splits its conditional
variance into \(t^2\sum_s q_s\xi_{E,s}^2+a^2v_\varepsilon\).
Because \(w\) is funded, \(t\leq1\), so the uncapped, freely traded
ETF can hold \(t\). Under (A) or (B), selling the initial active
holding costs zero; hence the replacement's cash rises by the
original review cost. Proposition 4 supplies an attained maximum,
and strictly positive terms in (18) exclude \(a>0\) in the stated
cases.

The qualifications are substantive. In four assumed instances,
\(W^-=1\), both loading rows are \((1,0)\), all residual shocks
vanish, ETF trading is free, the active limit is one,
\(\lambda=(1/50,0)\), \(\alpha=c^E=0\), \(\gamma=1\), and equally likely
factor shocks are \((\pm1/10,0)\). Active and ETF returns are
identical, and the following outcomes are exact:

| Initial \((a^-,p^-,k^-)\) | Active buy/sell rates | ETF cap | Full optimum | Consequence |
|---|---:|---:|---:|---|
| \((0,0,1)\) | \(1/100\) each | \(1\) | unique \((0,1)\) | No new active participation |
| \((1,0,0)\) | \(1/100\) each | \(1\) | unique \((1,0)\) | Costly incumbent stays |
| \((0,0,1)\) | \(0\) each | \(1\) | every \(a+p=1\) | ETF and active optima tie |
| \((0,0,1)\) | \(0\) each | \(1/4\) | every feasible \(a+p=1\) | Replacement is blocked |

In the last row the ETF-only optimum is \((0,1/4)\), and the
full-minus-ETF-only score gap is \(33/3200\). In the incumbent row,
the best zero-active holding is \((0,99/100)\), with score
\(9799/2000000<3/200\) for the incumbent. The common return law is
positive in gross terms, and all numbers and costs are assumed.

This is a sufficient-condition result for a conditional one-quarter
score, not a general zero-alpha rule or a multiperiod policy. Equal
loadings give \(\varepsilon=z^A-z^E\). If both residuals are
uncorrelated with factor shocks and with each other, the assumed
cross-moment is \(-\operatorname{Var}_q(z^E)\), so this subclass
requires a noiseless ETF. The funded one-quarter model does not impose those extra
uncorrelatedness conditions: a noisy ETF is compatible with the
proposition when its residual shock is shared by the active fund
and the active fund has an increment independent of that residual
and the factor shocks. Conversely, using the preceding cases'
means, loadings, risk coefficient and unit limits, with independent
residual signs of size \(1/100\) on both instruments, zero costs
and an all-cash start, an assumed one-quarter
instance has unique full optimum \((1/2,1/2)\) and
\(V_F-V_E=1/40000\); its cross-moment is \(-1/10000\), outside
the proposition. A zero-alpha fund then supplies diversification
against ETF tracking noise. Exact return replication may leave tied
optima. These instances establish no calibrated magnitude or
result for another model version.

The result says that a zero-alpha active holding can be avoided
when its exposure can be moved into a costless ETF without a
diversification loss. It does not require liquidation of a costly
incumbent, and ETF tracking noise can make the active fund useful
even at zero alpha. This is a conditional analogue of zero-alpha
non-participation, and its alpha is defined against the stated
factor benchmark. An alpha of zero against those factors need not
mean zero excess return against a tradable, noisy ETF.

The ETF-only optimum also provides a starting point for asking which
active-fund beliefs leave the investor willing to make no active trade.

**Proposition 9 (No-active-trade band after ETF optimization; funded one-quarter model; machine checked).**
Keep the initial holdings, factor-premium belief, return shocks, loadings,
limits and directional costs fixed. Index the finite parameter support by
\(h\), with factor premia \(\lambda_h\), active alpha \(\alpha_h\) and
belief mass \(\pi_h\). Write
\(\bar\lambda=\sum_h\pi_h\lambda_h\) and
\(\bar\alpha_0=\sum_h\pi_h\alpha_h\). For a proposed active belief mean
\(x\), replace each \(\alpha_h\) by
\(\alpha_h-\bar\alpha_0+x\). The translated family satisfies the
model's strict gross-return condition exactly on

$$
\begin{aligned}
J&=(\alpha_{\min},\infty),\\
\alpha_{\min}
 &=\max_{h,s}\{-1-B^A\lambda_h-\alpha_h+\bar\alpha_0-\xi_{A,s}\},\\
\mu(x)&=(B^A\bar\lambda+x,\ B^E\bar\lambda-c^E).
\end{aligned}\tag{20}
$$

The maximum includes support points of zero belief mass. The original
mean \(\bar\alpha_0\) belongs to \(J\). For the following formulas,
extend the same one-quarter score algebraically to every real \(x\);
outside \(J\) it is not a return-positive model instance. Let \(C\)
contain the real \(x\) for which *some* full-trading optimum has
\(a=a^-\). The actual no-active-trade set is \(C\cap J\). Choose any
ETF-only optimum \(w_E=(a^-,p_E)\), and write \(k_E=k(w_E)\).
Such an optimum exists and its set of choices does not depend on \(x\).

The ETF smooth marginal scores and the active centering value are
\(g_{E,j}=B^E_j\bar\lambda-c^E_j-\gamma(\Sigma w_E)_{E,j}\) and
\(\alpha_c=\gamma(\Sigma w_E)_A-B^A\bar\lambda\), respectively. Thus
the active smooth marginal is \(x-\alpha_c\). For ETF \(j\), let
\([\ell_j,u_j]\) be the interval of marginal switching-cost slopes at
\(p_{E,j}-p^-_j\): it is
\([\kappa^+_{E,j},\kappa^+_{E,j}]\) after a purchase,
\([-\kappa^-_{E,j},-\kappa^-_{E,j}]\) after a sale, and
\([-\kappa^-_{E,j},\kappa^+_{E,j}]\) after no ETF trade.
The compatible nonnegative cash-budget multipliers form the interval

$$
\begin{aligned}
I=\{\eta\geq0:\;&\eta k_E=0,\\
&g_{E,j}\leq u_j+(1+u_j)\eta
       \quad\text{if }p_{E,j}<\bar p_j,\\
&g_{E,j}\geq\ell_j+(1+\ell_j)\eta
       \quad\text{if }p_{E,j}>0,\quad\text{for every ETF }j\}.
\end{aligned}\tag{21}
$$

A zero-width ETF limit imposes neither inequality. The interval is
nonempty. If \(k_E>0\), then \(I=\{0\}\). Otherwise
\(I=[\eta_{\rm lo},\eta_{\rm hi}]\), where the upper endpoint may be
\(+\infty\), and

$$
\begin{aligned}
\eta_{\rm lo}
 &=\max\!\left(\{0\}\cup
   \left\{\frac{g_{E,j}-u_j}{1+u_j}:p_{E,j}<\bar p_j\right\}\right),\\
\eta_{\rm hi}
 &=\min\!\left\{
   \frac{g_{E,j}-\ell_j}{1+\ell_j}:p_{E,j}>0\right\},
 \qquad\min\varnothing=+\infty .
\end{aligned}\tag{22}
$$

For \(I=\{0\}\), set both endpoints to zero. The lower endpoint is
always finite and attained. If \(a^-<1\), the upper endpoint is finite.
Put \(b=\kappa_A^+\), \(s=\kappa_A^-\), and
\(L=\alpha_c-s+(1-s)\eta_{\rm lo}\). When
\(\eta_{\rm hi}<+\infty\), put
\(U=\alpha_c+b+(1+b)\eta_{\rm hi}\). The exact extended-score set is

| Initial active holding | \(C\) |
|---|---|
| \(0<a^-<\bar a\) | \([L,U]\), with finite endpoints |
| \(a^-=0<\bar a\) | \((-\infty,U]\), with finite \(U\) |
| \(0<a^-=\bar a\) | \([L,\infty)\) |
| \(a^-=\bar a=0\) | all real \(x\) |

In the interior case the full algebraic band's width is

$$
U-L=b(1+\eta_{\rm hi})+s(1+\eta_{\rm lo})
       +\eta_{\rm hi}-\eta_{\rm lo}.\tag{23}
$$

Equivalently, \(w_E\) is a full-trading optimum at a given \(x\)
exactly when some \(\eta\in I\) and active cost slope
\(t_A\in[-s,b]\) make
\(x-\alpha_c-\eta-(1+\eta)t_A\) zero at an interior active holding,
nonpositive at the active lower bound only, or nonnegative at its
upper bound only. If \(\bar a=0\), no active-coordinate condition is
needed. These are signs for holding bounds, not for purchase or sale.
Any choice of ETF-only optimum gives the same set \(C\).

To see necessity without assuming an interior feasible point, express
each directional switching cost as the maximum of its finitely many
linear pieces and lift the cost to a separate variable. The resulting
concave quadratic problem has linear inequalities, whose active
normals give the budget and bound multipliers at an optimum. Its
coordinate conditions give (21) and the active marginal condition.
Conversely, the cost-slope inequality, concavity of the score and
funding complementarity make those conditions sufficient for a global
optimum. Eliminating the ETF slopes gives (22); taking the union of
the active marginal conditions over \(I\) gives the four cases and
(23).

The set \(C\) asserts existence, since tied full-trading optima may
also trade the active fund. If \(\gamma>0\) and \(\Sigma\) is positive
definite, both action classes have unique optima, so \(C\cap J\)
identifies when the unique full-trading optimum leaves the active
holding unchanged. Neither condition is assumed generally. For
example, with one ETF, zero costs, zero loadings and shocks, and
\(\gamma=0\), an initial allocation
\((a^-,p^-,k^-)=(1/2,1/2,0)\) has tied full optima at \(x=0\),
including active-trading choices. Starting instead from \((1,0,0)\)
gives \(I=[0,\infty)\) and \(C=[0,\infty)\). Both examples have unit
holding limits, score \(xa\) and return-positive domain
\(J=(-1,\infty)\).

The interval measures how active purchase and sale costs interact
with the funded budget after the ETF adjustment is optimized. ETF
cost kinks and holding bounds can widen it through the range of
compatible budget multipliers. The intersection with \(J\) can
remove an endpoint or the entire interval. This is a one-quarter
belief-mean calculation, with no claim about changing the ETF menu,
factor-premium belief, later trading or estimation uncertainty.
The shadow-price scaling of a no-trade width is a known mechanism;
this interval applies it to the funded ETF-optimized comparison.

The ETF adjustment can change when its trading cost changes, so a higher
cost need not widen the active belief-mean band in Proposition 9.

**Proposition 10 (A higher common switching-cost rate can narrow the no-active-trade band; funded one-quarter model; machine checked).**
There is an exact assumed instance with one active fund, one ETF and
two factors in which raising the common purchase and sale rate for
both instruments from \(0\) to \(1/2000\) strictly narrows that band.
Normalize initial wealth to one. Set \(\gamma=1\),
\(B^A=(1,1/2)\), \(B^E=(1,0)\), \(c^E=-1/10000\),
\((a^-,p^-,k^-)=(1/2,0,1/2)\), and
\((\bar a,\bar p)=(1,1/2)\). The belief assigns mass \(1/4\)
to each pair
\(\lambda_1\in\{3/200,1/40\}\) and
\(\alpha\in\{-1/400,1/400\}\), with
\(\lambda_2=1/200\). As in Proposition 9, replace the two alpha
values by \(x-1/400\) and \(x+1/400\) to vary only their mean.

The return scenario law gives equal mass to the 32 sign vectors
\((s_1,\ldots,s_5)\in\{-1,1\}^5\), with
\(z^f_s=(3s_1/50,s_2/50)\),
\(z^A_s=3s_3/100\), and \(z^E_s=s_4/200\);
the fifth sign is unused. The resulting belief-mean return and
conditional covariance are

$$
\mu(x)=(9/400+x,\ 201/10000),\qquad
\Sigma=
\begin{pmatrix}
23/5000&9/2500\\
9/2500&29/8000
\end{pmatrix},
\qquad J=(-183/200,\infty).
\tag{24}
$$

The covariance is positive definite, and \(J\) is the common
return-positive domain at both rates. Let \(C_\kappa\) be the
extended-score set of active belief means \(x\) for which the
full-trading optimum leaves the active holding at \(a^-=1/2\).
All four switching-cost rates equal \(\kappa\); every other input,
including the complete belief at each \(x\), stays fixed. The
ETF-only optimum has zero cash in both cases:

| \(\kappa\) | ETF-only holding \(p_E\) | Compatible interval \(I\) | Active centering \(\alpha_c\) |
|---|---|---|---|
| \(0\) | \(1/2\) | \([0,1319/80000]\) | \(-23/1250\) |
| \(1/2000\) | \(1000/2001\) | \(\{11032/690345\}\) | \(-61367/3335000\) |

| \(\kappa\) | \(C_\kappa=[L,U]\) | Width \(U-L\) |
|---|---|---|
| \(0\) | \([-23/1250,-153/80000]\) | \(1319/80000\) |
| \(1/2000\) | \([-808663/276138000,-38269/20010000]\) | \(701377/690345000\) |

Both bands lie wholly inside \(J\), so restricting them to valid
model instances changes neither width. Their width difference is

$$
\frac{1319}{80000}-\frac{701377}{690345000}
=\frac{170890979}{11045520000}>0.
\tag{25}
$$

For the ETF-only class, funding gives
\(0\leq p\leq1/[2(1+\kappa)]\). Its score increases throughout
this interval at both rates, making its upper endpoint the unique
ETF-only optimum. At zero cost that endpoint equals the ETF limit:
the limit and cash constraint bind together, leaving a positive
range of compatible budget multipliers. At rate \(1/2000\), the
cash constraint still binds but the ETF optimum falls strictly
below its limit. ETF stationarity then pins the multiplier to one
value. Substitution into Proposition 9 gives the two bands above.
Positive definiteness makes each full-trading optimum unique, so
\(C_\kappa\) describes the unique action, rather than the existence
of a tied no-trade action.

In expected-return units, the band narrows from \(164.875\) to about
\(10.160\) basis points per quarter. This is a length comparison in
the active belief mean, not an inclusion claim about the two
intervals or a comparison of regions in holdings. The example
relies on the zero-cost ETF purchase meeting its cap and exhausting
cash at the same point; this coincident corner is a knife-edge, so the
example establishes no typical or robust effect of higher costs.
It is an instance of degeneracy in parametric optimization: the
ETF-only optimum has a nontrivial interval of compatible budget
multipliers when both constraints bind, and the interval collapses
to a single multiplier when the positive cost moves that optimum
below the ETF cap. If the ETF multiplier endpoints are held fixed
instead, Proposition 9's interior width increases with either
active-fund directional cost. The comparison here changes ETF costs
too, and therefore changes those endpoints. It says nothing about
later reviews, learning or estimation uncertainty. The narrowing
contradicts the common heuristic that higher costs always widen a
no-trade band, not a theorem in the cited literature. It is not a
general comparative static.

The two-review setting requires an attained continuation problem
before an initial active-trade comparison can use future ETF
adjustments consistently.

**Proposition 11 (Optimal finite policies and continuation representation; funded two-review model; machine checked).**
Fix the finite two-review model in Section 2. Let \(M\) be the
maximum of one and all specified instrument gross returns. For
every pair of root and continuation classes
\((D,R)\in\{F,E,N\}^2\), the policy set \(\Pi_{D,R}\) is nonempty,
convex and compact. Its expected terminal utility \(\Phi\) is
continuous and concave and attains a maximum. Every feasible
policy has strictly positive wealth at the second review and at
terminal marking on every specified path, and

$$
W_2\leq M^2W_0^-,
\qquad
-1<V_{D,R}\leq-\exp(-\rho M^2)<0.
\tag{26}
$$

Thus all nine certainty equivalents are finite. For any fixed
posterior \(\pi\), including one with zero masses, the conditional
problem \(V_1^R(x,h,\pi)\) attains its maximum at every nonnegative
state \((x,h)\). With \(W_0^-\), \(\rho\), costs and return law fixed,
this value is jointly concave in risky dollar holdings and cash,
and nondecreasing in cash. At \(x=h=0\), zero is the only feasible
trade and \(V_1^R(0,0,\pi)=-1\). The posterior and marked holdings
and cash specify the review-1 conditional problem: the second
scenario draw has law \(q\) conditional on \(\theta\), and no cost
term depends on an earlier hidden history.

The root continuation value \(H_0^R\) is concave on the funded full
root set \(F_0\). For every feasible root trade, conditional optima
can be selected at the finitely many public observations to form
one feasible observable continuation policy. In particular,

$$
V_{D,R}
 =\max_{(u_0,u_1)\in\Pi_{D,R}}\Phi(u_0,u_1)
 =\max_{u_0\in D_0}H_0^R(u_0).
\tag{27}
$$

For any fixed continuation class \(R\), nesting of root classes
gives \(V_{N,R}\leq V_{E,R}\leq V_{F,R}\). For any fixed root
class \(D\), nesting of continuation classes gives
\(V_{D,N}\leq V_{D,E}\leq V_{D,F}\). The same inequalities hold
for the corresponding certainty equivalents, since the
certainty-equivalent transform is strictly increasing in utility
value. Therefore \(\Delta_R\geq0\), and

$$
\Delta_R=0
\quad\Longleftrightarrow\quad
\text{some optimal policy in }\Pi_{F,R}
       \text{ has }u_{0,A}=0 .
\tag{28}
$$

The equivalence is about the existence of one full-class optimum
with no active trade at the first review; other optima may trade
the fund. To prove the result, funded accounting bounds every
trade by incoming wealth and makes the finite policy sets
compact. Strictly positive gross returns and sale rates below
one preserve positive wealth. Terminal wealth is concave in
policy trades because review costs are convex; increasing
concave exponential utility preserves that concavity. For fixed
posterior, mixing feasible trades at mixed marked states proves
joint concavity of the conditional value, including the cash
coordinate. Grouping the finite expected-utility sum by public
observation gives the continuation formula; conditional
maximizers exist at each node, with zero trades available at
zero-probability nodes. The two class orders then give the
zero-gap equivalence by attained maxima.

This result makes the nine dynamic comparisons well defined.
It does not calculate a particular optimal trade, give a scalar
no-active-trade band, or show that future ETF adjustment changes
the initial active-trade advantage in either direction.
Differences such as \(\Delta_E-\Delta_N\) and
\(\Delta_F-\Delta_E\) have no asserted sign. The concavity claim
holds for fixed posterior and fixed initial-wealth normalization;
it is not concavity in beliefs or in certainty equivalents.
The result is finite-control groundwork, not evidence of an
economic magnitude or a new dynamic trading mechanism. Its attainment
and continuation identity are finite-horizon dynamic programming.

Future ETF adjustment and future active trading can change the
advantage of buying the active fund today in opposite directions,
even though each future opportunity weakly raises the value of
every root trading class.

**Proposition 12 (Opposite effects of future ETF and active trading; funded two-review model; machine checked).**
Consider an exact assumed instance with initial wealth one, held
entirely in cash. There is one active fund and one ETF with
\(B^A=(1,0)\), \(B^E=(0,1)\), zero ETF drag and
\(\rho=20\). Two equally likely, persistent parameters are
\(\theta_+=(1/2,-1/2,0)\) and
\(\theta_-=(-1/2,1/2,0)\). Each quarter has one zero-shock
scenario. The active and ETF gross returns are respectively
\((3/2,1/2)\) under \(\theta_+\) and \((1/2,3/2)\)
under \(\theta_-\). The first public observation reveals which
parameter holds, whether or not either fund was bought. Alpha is
known to be zero; the active fund is the only vehicle for the
first factor, which the ETF menu does not span. Let all four
active and ETF purchase and sale rates vary independently over
\([0,1/100]\), held fixed across the two reviews. Every member
of this family satisfies the funded two-review model.

On the certainty-equivalent scale in units of initial wealth,
the optimized root full-minus-ETF-only advantages obey,
*simultaneously for every rate choice in that box*,

$$
0\leq\Delta_N\leq\frac14,\qquad
\Delta_E>\frac{507}{2020},\qquad
0\leq\Delta_F\leq\frac{3}{202}.
\tag{29}
$$

Consequently the matched continuation comparisons have opposite
strict signs:

$$
\Delta_E-\Delta_N>\frac{1}{1010}>0,\qquad
\Delta_F-\Delta_E<-\frac{477}{2020}<0.
\tag{30}
$$

Every full-root optimum with future ETF-only trading buys a
positive active holding at the root. At zero shareholder costs,
\(\Delta_F=0\), and an optimal full-root policy with future full
trading keeps all wealth in cash at the root; this asserts
existence, not uniqueness.

The bounds follow from feasible policies and upper bounds on
whole action classes. If the second review is disabled, a
post-root allocation \((a,p,h)\) has terminal wealth
\(h+9a/4+p/4\) under \(\theta_+\) and
\(h+a/4+9p/4\) under \(\theta_-\). Their mean is at most
\(5/4\), which bounds \(CE_{F,N}\); staying in cash gives
\(CE_{E,N}\geq1\). If both reviews are ETF-only, the root
active holding is zero. For its root ETF holding \(p\), terminal
wealth is at most \(1-p/2\) under \(\theta_+\) and
\(3/2+3p/4\) under \(\theta_-\). The resulting
expected-utility upper bound is decreasing over \(0\leq p\leq1\)
and gives \(CE_{E,E}<21/20\).

For a funded full-root policy with future ETF-only adjustment,
buy \(a=(7/15)/(1+1/100)\) active dollars and
\(p=(8/15)/(1+1/100)\) ETF dollars today. Retain any cash
left after the actual charges. At the second review sell the
losing ETF under \(\theta_+\), and otherwise make no trade.
For every allowed rate the terminal wealth in each state is at
least \(657/505\), so \(CE_{F,E}\geq657/505\).
Finally, any full policy has expected terminal wealth at most
\(3/2\), while an ETF-only root policy can wait in cash and
buy the publicly revealed winning fund at the second review,
securing at least \(150/101\) in both states. These give
\(CE_{F,F}\leq3/2\) and \(CE_{E,F}\geq150/101\).
Certainty equivalent lies between a policy's minimum and mean
terminal wealth here; combining the bounds gives (29), then
(30). The strict ETF-continuation gap and Proposition 11's
attainment show that every corresponding full-root optimum
buys active exposure.

The mechanism is exposure and timing. Future ETF trading lets
an active purchase retain the unspanned first-factor exposure
while the losing ETF can be sold after public learning. Future
active trading instead lets cash wait and buy whichever fund
will earn \(3/2\) in the second quarter. The signs are proved
for the entire stated cost box, without a cost ranking or a
coincident position limit. The instance has known zero alpha,
zero conditional return shocks, complete revelation and assumed
quarterly returns of plus or minus \(50\%\). Its magnitudes
are not calibrated; the next result tests the signs under a
small, explicitly bounded departure from those conditions.
The continuation differences do not locate a general
no-active-trade boundary or separate learning from
the future trading opportunity; public information is the
same under all controls. No sign is asserted for
\(\Delta_F-\Delta_N\) over the cost box. Future flexibility changing
today's demand is a familiar option-value mechanism; the contribution
is the two opposite signs for these explicit funded comparators
throughout the stated cost box. It is not a hedge against risk: the
first observation reveals the parameter and there is no conditional
return risk, so future ETF adjustment is worth something here only
because it redeploys wealth into returns known after the first
review. Intertemporal hedging demand is a different mechanism
(Section 4).

**Proposition 13 (Opposite continuation effects with conditional risk and incomplete alpha learning; funded two-review model; machine checked).**
Fix \(0<\delta\leq1/1000\). As in Proposition 12, initial wealth
one is entirely in cash, \(B^A=(1,0)\), \(B^E=(0,1)\), ETF
drag is zero, and \(\rho=20\). Now the four persistent latent
parameters \(\theta_{\sigma,\xi}=(\sigma/2,-\sigma/2,\xi\delta)\),
for \(\sigma,\xi\in\{-1,1\}\), each have prior probability
\(1/4\). Each quarter independently draws a conditional shock
scenario \((s_A,s_E)\in\{-1,1\}^2\) with probability \(1/4\),
independent of the parameter. Factor shocks are zero, while the
active and ETF residual shocks are \(\delta s_A\) and
\(\delta s_E\). Thus their gross returns are
\(1+\sigma/2+\delta(\xi+s_A)\) and
\(1-\sigma/2+\delta s_E\). The four purchase and sale rates
vary independently over \([0,1/100]\) and remain fixed across
reviews. Every member of this family satisfies the funded
two-review model.

The conditional return covariance is the positive-definite
matrix \(\delta^2 I_2\). Alpha has two nonzero, equally likely
values \(\pm\delta\), independent of the factor-premium regime.
The first public observation reveals \(\sigma\). With probability
\(1/2\), the active residual observation is zero and the
posterior still assigns probability \(1/2\) to each alpha value.
Nevertheless, for *every* stated \(\delta\) and rate vector,
the optimized certainty-equivalent gaps, in fractions of initial
wealth, obey

$$
0\leq\Delta_N\leq\frac14+\delta^2,\qquad
\Delta_E>\frac{2129}{8080}-9\delta-\delta^2,\qquad
0\leq\Delta_F\leq\frac{3}{202}+\frac{402}{101}\delta.
\tag{31}
$$

Hence the two matched continuation effects retain opposite
strict signs throughout this family:

$$
\Delta_E-\Delta_N>\frac1{250}>0,\qquad
\Delta_F-\Delta_E<-\frac{23}{100}<0.
\tag{32}
$$

Every full-root optimum with future ETF-only trading buys a
positive active holding. Neither a unique optimum nor a zero
root gap under future full trading is asserted.

The bounds use whole-class upper bounds and funded policies
whose second-review choices depend only on the observed
\(\sigma\). With no future trade, mean terminal wealth under
any full-root policy is at most \(5/4+\delta^2\); staying in
cash gives the ETF-only root class at least one. With ETF-only
trading at both reviews, pathwise return bounds for a root ETF
holding \(p\) give
\(CE_{E,E}<83/80+3\delta+\delta^2\).
The same root purchases \(a=(7/15)/(1+1/100)\) and
\(p=(8/15)/(1+1/100)\) used in Proposition 12, followed by
an ETF sale only when \(\sigma=1\), yield terminal wealth at
least \(657/505-6\delta\) on every path. This lower-bounds
\(CE_{F,E}\). Under full future trading, every policy has
\(CE_{F,F}\leq3/2+2\delta\), while waiting in cash and then
buying the fund favored by the revealed regime gives
\(CE_{E,F}\geq(3/2-2\delta)/(1+1/100)\). These estimates
give (31), and their worst-case margins over
\(0<\delta\leq1/1000\) give (32). Attainment from
Proposition 11 turns \(\Delta_E>0\) into the assertion about
every full-root optimum.

This result shows that the signs in Proposition 12 are not
confined to zero conditional risk or complete parameter
revelation. It does not show a substantial-risk or alpha-driven
effect: alpha and shocks are at most \(0.1\%\) per quarter,
against factor premia of plus or minus \(50\%\). The factor
regime is revealed exactly, and both witness policies ignore
the unresolved alpha. The active fund still uniquely carries
the first factor. The law couples alpha and shock spacing so
that some observations overlap; arbitrary changes to that
information structure are outside the result. The values and
rates are assumed, not calibrated, and no general boundary or
cash-composition comparative static follows. This is a robustness
example for the same continuation mechanism as Proposition 12,
not a distinct principle about learning or hedging demand.

Portfolio moments can agree while public ETF returns reveal
different information about a profitable active trade.

**Proposition 14 (Equal portfolio geometry and covariances can hide different certification information; funded one-quarter model with public histories; machine checked).**
Take one active fund and one ETF, initial wealth one entirely
in cash, position limits one, zero shareholder costs,
\(\gamma=1\), zero ETF drag, and loadings
\(B^A=(0,0)\), \(B^E=(1,0)\). The factor premia are known and
\(\Theta=\{(1/80,0,\alpha):-1/10\leq\alpha\leq1/10\}\).
Each public record draws three independent uniform signs
\(s,t,u\). Factor shocks vanish and the active residual shock
is \(s/10\). Compare an *independent-residual* law
\(\mathcal I\), with ETF residual \(t(3-u)/20\), to a
*revealing-residual* law \(\mathcal R\), with ETF residual
\(t(3-s)/20\). The signs are redrawn independently each
quarter. Both known laws have centered shocks and positive
fund gross returns.

Both laws have the same funded classes
\(F=\{(a,p):a,p\geq0,\ a+p\leq1\}\) and
\(E=\{(0,p):0\leq p\leq1\}\), score, realized-return
covariance and mean-error covariance:

$$
\begin{aligned}
Q((a,p);\theta)&=a\alpha+\frac{p}{80}
                 -\frac{a^2}{200}-\frac{p^2}{80},\\
\sup_{v\in E}Q(v;\theta)&=\frac1{320}
                 \quad\text{at the unique ETF holding }(0,1/2),\\
\Sigma&=\operatorname{diag}(1/100,1/40),\qquad
\Omega=\operatorname{diag}(0,0,1/100).
\end{aligned}\tag{33}
$$

Their public-record covariance, each fund's marginal-return
law, and the distribution of \(\widehat\theta_N\) also agree.
The scores and advantages are one-quarter, initial-wealth-normalized
quantities, not realized returns.
At \(\theta_+=(1/80,0,1/10)\), the unique full optimum is
\(w_A=(1,0)\), with advantage \(147/1600\) against the
*entire* ETF-only class. At
\(\theta_-=(1/80,0,-1/10)\), every positive active holding
has negative advantage.

For a full-history benchmark, allow a rule to certify any
feasible active trade or fall back to \((0,1/2)\), with an
independent coin if desired. Require its probability of
certifying an action with nonpositive true advantage to be
at most \(\eta\), uniformly for every \(\theta\in\Theta\).
Let \(P^{\max}_{\mathcal I}\) and \(P^{\max}_{\mathcal R}\)
be the greatest certification probabilities at \(\theta_+\)
among such rules under their respective known laws. For every
\(N\geq1\) and \(0<\eta<1\), both bounds are attained and

$$
P^{\max}_{\mathcal I}
 =\min\{1,1-2^{-N}+\eta\},\qquad
P^{\max}_{\mathcal R}=1.
\tag{34}
$$

Thus, for \(0\leq\beta\leq1\), power at least \(1-\beta\) is attainable in
\(\mathcal I\) exactly when \(2^{-N}\leq\eta+\beta\);
\(\mathcal R\) permits power one after one record without
false certification. By contrast, the prescribed sample-mean
gate with exact \(L_N\) has the *same* certification law in
both models, and at \(N=1\) certifies with probability
\(1/2\) at \(\theta_+\) for every \(\eta\in(0,1)\).
At \(\eta=1/4\), the two full-history benchmarks are
\(3/4\) and one.

The overlap argument makes (34) sharp. Under \(\theta_+\)
and \(\theta_-\), all active returns are zero with probability
\(2^{-N}\). In \(\mathcal I\) the full public histories on
that event have identical probabilities at both endpoints.
Every active certification is false at \(\theta_-\), so at
most \(\eta\) certification probability can be spent on the
overlap; outside it, a nonzero active return identifies alpha.
Certifying \(w_A\) when its identified alpha makes its
advantage positive, and using a coin on the overlap, attains
the bound uniformly over \(\Theta\). In \(\mathcal R\), the
ETF residual's absolute size reveals \(s\), making alpha
exactly identifiable after one record. These signals are
public whether or not the ETF is held.

The sample-mean estimator discards that ETF residual in both
laws. At one record its exact quantile is one. At
\(\theta_+\), its estimated alpha is zero or \(1/5\) with
equal probability: the first confidence set contains
\(\theta_-\), and the second is \(\{\theta_+\}\).
The gate certifies only in the second case. With
\(\eta=1/4\), its \(1/4\) shortfall against
\(\mathcal I\)'s benchmark comes from leaving the permitted
false-certification allowance unused on all-zero histories;
the gate already certifies every nonzero active-return history
at \(\theta_+\). The further \(1/4\) difference between
the two *full-history benchmarks* is the value of the
revealing public ETF residual. The entire gap from
\(\mathcal R\)'s benchmark to the gate cannot be assigned to
that signal.

The obstruction is specific to a known discrete law with exact
return observations, known factor premia, unknown alpha alone,
zero switching costs and a fixed ETF optimum. It shows that
geometry and second moments do not determine an instance's
sharp full-history certification power. It does not establish
a general history-length rate, an economically calibrated
magnitude, or stability to rounding or unknown laws. The
full-history benchmarks use rules beyond the prescribed gate;
its power need not match their attainable upper values. The
underlying fact that second moments do not determine a
likelihood is generic, so no broad priority claim follows.
The comparison uses the general two-law information-obstruction
method; its specific content is the funded public-observation pair
and the quantified loss of certification power.

The public-history obstruction leaves open how many records a
uniformly valid decision needs when the observation law has no
extra ETF signal. The next result answers that question in one
bounded scalar family.

**Proposition 15 (Worst-case history-length rate for a funded unspanned-factor trade; one-quarter model with known finite laws; machine checked).**
Start with wealth one in cash, one active fund and one ETF,
zero risky incumbents, zero sale rates and ETF drag, and
\(\gamma=0\). The active cap is \(\bar a\in(0,1]\), the ETF
cap is one, and their purchase rates
\(\kappa_A,\kappa_E\) lie in \([0,1)\). Let \(d>0\),
\(\mu>\kappa_E\), \(H>0\), and \(dH\leq1/4\). Set
\(B^A=(d,0)\), \(B^E=(0,1)\), and

$$
\begin{aligned}
q_E&=\frac{\mu-\kappa_E}{1+\kappa_E},&
\lambda_0&=\frac{\kappa_A+(1+\kappa_A)q_E}{d},\\
A&=\min\{\bar a,(1+\kappa_A)^{-1}\},& D&=dA>0,\\
w_A&=\left(A,\frac{1-(1+\kappa_A)A}{1+\kappa_E}\right),&
v_E&=\left(0,(1+\kappa_E)^{-1}\right).
\end{aligned}\tag{35}
$$

The unknown parameter is
\(\theta=(\lambda,\mu,0)\), where
\(\lambda\in[\lambda_0-H,\lambda_0+H]\); alpha is known
to be zero. Let \(\mathcal K_H\) be the class of finite
centered laws of a real \(Z\) supported in \([-H,H]\).
For each law, the only random shock is the first factor shock
\(Z\); all residual shocks vanish. Public observations are equivalent to independent
draws of \(x=\lambda+Z\): the factor record is \((x,\mu)\),
the active return is \(dx\), and the ETF return is \(\mu\).
The next holding-quarter shock is independent. The law,
including its exact support and probabilities, is known before
sampling.

The funded ETF-only optimum is uniquely \(v_E\) with score
\(q_E\). The full optimum is uniquely \(w_A\) when
\(\lambda>\lambda_0\), and every active action has negative
advantage when \(\lambda<\lambda_0\). For every \(\lambda\),
\(\operatorname{Adv}(w_A;\theta)=D(\lambda-\lambda_0)\)
and \(G_*(\theta)=D\max\{\lambda-\lambda_0,0\}\).
The first-factor exposure difference between \(w_A\) and
*every* ETF-only holding is \(D\); funding and the cap fix
that conversion from a factor-premium difference to a score
difference.

Choose a score margin \(0<\delta\leq DH/2\) and error
allowance \(0<\varepsilon\leq1/16\) before sampling. Set the
economic certification threshold to \(\delta/4\) and the
confidence error allowance to \(\eta=\varepsilon\). Require,
at every parameter in the interval, unconditional probability
at most \(\varepsilon\) of certifying an active action with
true \(\operatorname{Adv}\leq\delta/4\). Also require
probability at least \(1-\varepsilon\) of certifying an active
action with true \(\operatorname{Adv}>\delta/4\) whenever
\(G_*(\theta)\geq\delta\). A rule may depend on the known
law but never on the unknown parameter; it either certifies
a feasible active action or falls back to \(v_E\). Then

$$
\begin{aligned}
\text{both requirements for every law in }\mathcal K_H
&\quad\Longrightarrow\quad
N\geq\frac{1}{4\pi^2}
       \left(\frac{DH}{\delta}\right)^2
       \log\frac1\varepsilon,\\
N\geq32\left(\frac{DH}{\delta}\right)^2
       \log\frac2\varepsilon
&\quad\Longrightarrow\quad
\text{both requirements for every law in }\mathcal K_H.
\end{aligned}\tag{36}
$$

The first implication holds even for full-public-history rules
that randomize and can certify *any* funded active action. The
second uses the prescribed confidence set \(C_N\), plug-in
optimizer and ETF-only fallback. With
\(r_B=H\sqrt{2\log(2/\varepsilon)/N}\), it certifies the
plug-in choice \(w_A\) only if \(C_N\ne\varnothing\) and

$$
\ell_N(w_A)=D(\widehat\lambda_N-r_B-\lambda_0)
 >\delta/4,\qquad
\ell_N(w_A)\leq L_N(w_A)
 \quad\text{on these histories}.
\tag{37}
$$

If the set is empty or the plug-in optimum is not \(w_A\),
the rule falls back to \(v_E\). On the calibrated coverage
event at an alternative with \(G_*\geq\delta\), the
sufficient length in (36) gives \(\ell_N(w_A)\geq\delta/2\).
The certificate thus bounds the *original* optimized-ETF
target \(L_N\), rather than a comparison with one chosen ETF
portfolio.

For the lower bound, put \(\Delta=\delta/D\),
\(m=\lfloor H/\Delta\rfloor+1\), and
\(\phi=\pi/(m+1)\). A centered law in \(\mathcal K_H\)
puts masses proportional to \(\sin^2(i\phi)\) at
\(Z_i=2\Delta[i-(m+1)/2]\), \(i=1,\ldots,m\). At
\(\lambda_\pm=\lambda_0\pm\Delta\), the full public
histories have one-record affinity \(\cos\phi\) and
\(N\)-record affinity \(\cos^N\phi\). The negative endpoint
makes every active certification false, while the positive
endpoint has \(G_*=\delta\). A finite overlap bound for
the two endpoint laws yields the first implication in (36).
For the upper bound, the centered bounded shock gives
\(\Pr(|\widehat\lambda_N-\lambda|\geq r_B)\leq\varepsilon\).
Exact finite calibration makes the prescribed confidence
radius no larger than \(r_B\); this proves both the lower
certificate in (37) and its coverage-event power guarantee.

This is the standard scalar mean-testing rate in premium
units, \((H/(\delta/D))^2\log(1/\varepsilon)\). The funded
geometry enters through \(D\) as a unit conversion. The
constants in (36) differ by up to roughly 1600 after the
logarithms are compared, so only the order matches. The hard
law can change with the prespecified margin and needs a
support size growing with \(DH/\delta\); an individual
known finite law can be much easier. The active fund uniquely
carries the first factor, with known zero alpha: this is
certification of a premium opportunity, not manager skill.
The family has zero mean-variance penalty, deterministic ETF
returns and exact public observations. It supplies neither a
multivariate rate nor a guarantee under rounded or unknown
laws, a moving ETF optimum, repeated live testing or calibrated
market returns. The inverse-square lower-bound mechanism is
standard best-arm-style mean testing; the stated rate converts it
to the funded, unspanned-factor score margin against the optimized
ETF-only class.

Proposition 15 has a fixed ETF optimum. The following family
makes that optimum switch with the unknown premium, so a
certificate must cover two comparison directions.

**Proposition 16 (Joint directional information against a moving ETF comparator; one-quarter model with known finite laws; machine checked).**
Take one active fund, one ETF, initial wealth one entirely in
cash, caps one, zero shareholder costs and ETF drag, and
\(\gamma=0\). Their loadings are
\(B^A=(1,0)\) and \(B^E=(0,1)\). Write
\(\theta=(\lambda_1,\lambda_2,\alpha)\). Fix a known real
\(3\times3\) matrix \(J\) of Euclidean operator norm at most
\(1/100\), and set

$$
\begin{gathered}
c_0=(0,-1/4,0),\qquad c_1=(0,1/4,1/4),\\
\Theta=\operatorname{conv}\{c_j+Jv:
j\in\{0,1\},\ v\in\{-1,1\}^3\},\qquad
\Omega=JJ^\top,\\
d_0=(1,0,1),\qquad d_1=(1,-1,1),\qquad
\sigma_j^2=d_j^\top\Omega d_j,\quad
\sigma=\max\{\sigma_0,\sigma_1\}.
\end{gathered}\tag{38}
$$

Let \(\mathcal K_J\) contain every *known finite* law of
\(U\in\mathbb R^3\) with
\(\mathbb E U=0\), \(\mathbb E UU^\top=I_3\) and
\(\|U\|_2\leq9\). The observation shock is
\((z^f_1,z^f_2,z^A)=JU\), while the ETF residual shock is
zero. Each public record is equivalent to
\(X=(f_1,f_2,r^A-f_1)=\theta+JU\); the ETF return is
\(r^E=f_2\). Histories and the next holding-quarter draw
are independent conditional on fixed \(\theta\). All laws
in \(\mathcal K_J\) have the same mean-error covariance
\(\Omega\). Under the nonzero-rate assumptions below,
\(\Omega_{33}>0\) makes both alpha and the first premium
uncertain; zero alpha-error variance is also allowed.

The funded classes are
\(F=\{(a,p):a,p\geq0,\ a+p\leq1\}\) and
\(E=\{(0,p):0\leq p\leq1\}\). With \(w_A=(1,0)\),
the whole ETF-only class and the full class give

$$
\begin{aligned}
\sup_{v\in E}Q(v;\theta)&=\max\{0,\lambda_2\},\\
m_j(\theta)&=d_j^\top\theta,\qquad
\operatorname{Adv}(w_A;\theta)=\min_{j=0,1}m_j(\theta),\\
G_*(\theta)&=\max\{0,\min_{j=0,1}m_j(\theta)\}.
\end{aligned}\tag{39}
$$

Cash uniquely optimizes \(E\) when \(\lambda_2<0\), and
the ETF does so when \(\lambda_2>0\); both regimes occur in
\(\Theta\). If the minimum in (39) is positive,
\(w_A\) is the unique full optimum. If it is negative,
every positive active holding has negative advantage. The
paired estimation errors in the two score comparisons have
variances \(\sigma_j^2/N\), including all alpha/premium
cross-covariances. Both directions have a first-premium and
an alpha component.

Assume \(\Omega_{11}>0\) and \(\sigma>0\). Fix
\(0<\delta\leq\sigma/8\),
\(0<\varepsilon\leq1/16\),
\(\eta=\varepsilon\), and economic threshold
\(\delta/4\) before sampling. As in Proposition 15, a rule
may depend on the known law, may randomize, and either
certifies a funded active action or falls back to an ETF-only
action. It must have unconditional false-certification
probability at most \(\varepsilon\) at every
\(\theta\in\Theta\), and correct-certification probability
at least \(1-\varepsilon\) whenever \(G_*(\theta)\geq\delta\).
Here false certification means an implemented active action
with true advantage at most \(\delta/4\), and correct
certification means true advantage above \(\delta/4\).
Then

$$
\begin{aligned}
\text{requirements for every law in }\mathcal K_J
&\Longrightarrow
N\geq\frac{\sigma^2}{16\pi^2\delta^2}
          \log\frac1\varepsilon,\\
N\geq192\frac{\sigma^2}{\delta^2}
          \log\frac6\varepsilon
&\Longrightarrow
\text{requirements for every law in }\mathcal K_J.
\end{aligned}\tag{40}
$$

The first implication holds for all full-history rules,
including randomized ones. For the second, let
\(t_{N,\varepsilon}\) be Section 2's exact finite-law
critical value and set
\(r_N=\sqrt{t_{N,\varepsilon}/N}\). On a nonempty
prescribed confidence set \(C_N\), the rule uses the
conservative certificate

$$
\ell_N(w_A)=\min_{j=0,1}
 \{d_j^\top\widehat\theta_N-r_N\sigma_j\}
 \leq L_N(w_A).
\tag{41}
$$

If \(\ell_N(w_A)>\delta/4\), then \(w_A\) is also the
actual plug-in full optimizer and the rule certifies it;
otherwise it uses the prescribed ETF-only fallback. Empty
\(C_N\) always forces fallback. On coverage,
\(\ell_N(w_A)\geq\min_j\{m_j(\theta_*)-2r_N\sigma_j\}\).
Under the sufficient length in (40), this is at least
\(\delta/2\) whenever \(G_*\geq\delta\). Thus (41) bounds
the original \(L_N\) against the *optimized* ETF class;
certifying against one selected ETF action would be weaker.

For the lower bound, choose the direction \(j\) with
\(\sigma_j=\sigma\). A centered sine-weighted finite law
is embedded along \(J^\top d_j/\sigma\), with independent
signs completing the three-dimensional covariance to
\(I_3\). It preserves \(\Omega=JJ^\top\), including when
\(J\) is singular. Two parameters on opposite sides of
that comparator face require conflicting certification
decisions. Their full public histories are images of latent
histories with one-record affinity
\(\cos(\pi/(4k))\), where
\(k=\lfloor\sigma/(4\delta)\rfloor\geq2\). A finite
overlap bound, applied even to rules with the latent history,
gives the first implication in (40). For the upper bound,
finite bounded-mean tails and a three-coordinate union bound
give \(t_{N,\varepsilon}\leq12\log(6/\varepsilon)\)
under the sufficient length. A covariance-direction
inequality on \(\operatorname{Im}(\Omega)\) proves (41) and
the coverage-event guarantee without dropping cross terms.

The two variances expose the directional effect:

$$
\begin{aligned}
\sigma_0^2&=\Omega_{11}+2\Omega_{13}+\Omega_{33},\\
\sigma_1^2&=\Omega_{11}+\Omega_{22}+\Omega_{33}
 -2\Omega_{12}+2\Omega_{13}-2\Omega_{23},\\
\sigma^2&\geq
 (\sqrt{\Omega_{11}}-\sqrt{\Omega_{33}})^2.
\end{aligned}\tag{42}
$$

If the alpha-error standard deviation is at most half the
first-premium error standard deviation, the necessary length
in (40) is at least
\(\Omega_{11}\log(1/\varepsilon)/(64\pi^2\delta^2)\).
When \(\Omega_{33}=0\), alpha is observed exactly and
\(\sigma^2\geq\Omega_{11}\). Moreover, there is a value
\(\alpha_0\), fixed before the history length and the law,
for which the lower bound in (40) still holds when a rule is
told alpha *before* sampling and its two requirements apply
only to \(\theta\in\Theta\) with \(\alpha=\alpha_0\).
This pre-disclosure conclusion is machine checked. It does
not assert that the bound holds on every alpha slice.
Conversely, for \(s=1/1000\), \(0<\tau\leq1\), and

$$
J=s\begin{pmatrix}1&0&0\\1&\tau&0\\0&\tau&0\end{pmatrix},
$$

one gets \(\sigma_1=0\) but
\(\sigma_0^2=s^2(1+\tau^2)>0\). Errors cancel against
the ETF, yet cash can be the better comparator and still
requires data. If both \(\sigma_j=0\), outside the
nonzero-rate statement, both comparisons are observed
exactly after one record and a full-history rule certifies
with zero false certification and power one; this does not
remove the prescribed gate's empty-set fallback.

The bounds match in order only. Their constants differ by
roughly \(5\times10^4\) at the largest allowed
\(\varepsilon\). The hard law's support grows as
\(\sigma/\delta\), so the rate is worst-case over
\(\mathcal K_J\), not a rate for each known law. The main
structural result is the maximum over both comparator
directions in this funded cash-versus-ETF geometry. A maximum over
alternatives and a two-point lower bound are standard
best-arm-identification tools; the finite testing and ellipsoidal
penalties are standard mathematics. Both contrasts load on
\(\lambda_1+\alpha\), so the result does not separately
identify manager skill from the unspanned premium. It assumes
zero costs and risk penalty, an all-cash incumbent, exact
known finite laws and a two-vertex ETF comparator. It gives
no calibrated market magnitude, general multivariate menu,
efficient calibration method or repeated-review guarantee.

The previous two history-length results have a fixed-size
profitable active action. With a smooth active entry, the
action itself becomes small as its advantage approaches zero.

**Proposition 17 (Quadratic entry changes the history rate in economic advantage; funded risk-averse one-quarter model with known finite laws; machine checked).**
Fix \(0<s\leq1/100\). Take one active fund and one ETF,
initial wealth one in cash, caps one, zero shareholder costs
and ETF drag, loadings \(B^A=(1,0)\), \(B^E=(0,1)\), and
\(\gamma=s^{-2}\). Set
\(c=(0,1/4,0)\) and
\(\Theta=c+s[-1,1]^3\) for
\(\theta=(\lambda_1,\lambda_2,\alpha)\). The class
\(\mathcal K_s\) consists of known finite laws of
\(U\in\mathbb R^3\) with
\(\mathbb E U=0\), \(\mathbb E UU^\top=I_3\), and
\(\|U\|_2\leq9\). For each law, take
\((z^f_1,z^f_2,z^A)=sU\) and zero ETF residual shock.
The public record is equivalent to
\(X=(f_1,f_2,r^A-f_1)=\theta+sU\), and the ETF return is
\(f_2\). Histories and the next holding-quarter draw are
independent conditional on fixed \(\theta\). The two
covariances have distinct roles:

$$
\Omega=s^2I_3,\qquad
\Sigma=\operatorname{diag}(2s^2,s^2),\qquad
Q((a,p);\theta)=a(\lambda_1+\alpha)+p\lambda_2-a^2-p^2/2.
\tag{43}
$$

Let \(x=\lambda_1+\alpha\) and \(x_+=\max\{x,0\}\).
The unique funded optima, both with strict cash slack, and
the advantage over the *entire* ETF-only class are

$$
\begin{aligned}
v_E(\theta)&=(0,\lambda_2),&
w_F(\theta)&=(x_+/2,\lambda_2),\\
\sup_{v\in E}Q(v;\theta)&=\lambda_2^2/2,&
G_*(\theta)&=x_+^2/4,\\
\operatorname{Adv}((a,p);\theta)
 &=a x-a^2-(p-\lambda_2)^2/2.
\end{aligned}\tag{44}
$$

The ETF optimizer moves continuously with its unknown
premium. At oracle advantage \(\delta>0\), the smallest
positive mean signal is \(x=2\sqrt\delta\), and the active
optimum holds \(a=\sqrt\delta\). Thus the active trade and
its paired mean-error exposure both shrink at entry. The
last term in (44) is the separate score loss from using an
estimated ETF holding rather than the true ETF optimum.

Fix \(0<\delta\leq s^2/128\) and
\(0<\varepsilon\leq1/16\), with confidence error
\(\eta=\varepsilon\) and economic threshold \(\delta/4\)
chosen before sampling. A rule may depend on the known law,
may randomize, and must either certify a feasible active
action or fall back to a funded ETF-only action. At every
\(\theta\in\Theta\), require probability at most
\(\varepsilon\) of certifying an active action whose true
advantage is at most \(\delta/4\). Whenever
\(G_*(\theta)\geq\delta\), require probability at least
\(1-\varepsilon\) of certifying an action whose true
advantage exceeds \(\delta/4\). Then

$$
\begin{aligned}
\text{requirements for every law in }\mathcal K_s
&\Longrightarrow
N\geq\frac{s^2}{32\pi^2\delta}
          \log\frac1\varepsilon,\\
N\geq768\frac{s^2}{\delta}\log\frac6\varepsilon
&\Longrightarrow
\text{requirements for every law in }\mathcal K_s.
\end{aligned}\tag{45}
$$

The first implication applies to every full-public-history
rule, including randomized ones. The second is attained by a
conservative version of the one-quarter model's prescribed
plug-in gate. On any
positive-probability history, put
\(\widehat x=\widehat\lambda_1+\widehat\alpha\),
\(\widehat a=\widehat x_+/2\),
\(\widehat p=\widehat\lambda_2\), and
\(\rho_N=s\sqrt{t_{N,\varepsilon}/N}\). Both plug-in
actions \((\widehat a,\widehat p)\) and
\((0,\widehat p)\) remain funded even when the unprojected
sample mean lies outside \(\Theta\). For nonempty \(C_N\),
the gate uses

$$
\begin{aligned}
\ell_N((\widehat a,\widehat p))
={}&\widehat a\widehat x-\widehat a^2
 -\sqrt2\,\widehat a\rho_N-\rho_N^2/2\\
\leq{}&L_N((\widehat a,\widehat p)).
\end{aligned}\tag{46}
$$

It certifies only when \(\widehat a>0\) and
\(\ell_N>\delta/4\); an empty confidence set forces the
ETF fallback. The \(\rho_N^2/2\) term protects against
error in the ETF optimum inside the original
optimized-comparator target. Comparing with only the
selected ETF action would omit that loss. On coverage, if
\(G_*\geq\delta\) and \(\rho_N\leq\sqrt\delta/8\),
the certificate is at least \(5\delta/8\), so the rule
correctly certifies. A bounded-mean calculation gives
\(t_{N,\varepsilon}\leq12\log(6/\varepsilon)\) under the
sufficient length in (45), which ensures that radius bound.

For the lower bound, use a centered normalized sine-weight
finite law embedded along the active signal direction
\((1,0,1)/\sqrt2\). Two parameters in \(\Theta\) have
opposite active signals of order \(\sqrt\delta\), while
both have \(\lambda_2=1/4\). At the negative parameter
every active certification is false; at the positive one
\(G_*\geq\delta\). The translated finite supports overlap,
and their one-record affinity is
\(\cos(\pi/(4k))\), where
\(k=\lfloor s/(4\sqrt{2\delta})\rfloor\geq2\).
Lifting any public rule to the more informative latent
history and applying the finite overlap bound gives the
first implication in (45). The lower pair holds the ETF
premium fixed: the bound comes from active entry even though
the ETF optimum varies across the full parameter domain.

The worst-case history length is therefore of order
\((s^2/\delta)\log(1/\varepsilon)\) for fixed \(s\),
with constants about \(4\times10^5\) apart. In *mean-signal*
units, however, \(x=2\sqrt\delta\) makes this the same
scalar inverse-square testing rate as the earlier examples.
The exponent change in economic advantage is the conversion
through the quadratic entry score, not a general effect of
risk aversion; \(\gamma=s^{-2}\) also ties preferences to
the shock scale. The result assumes zero costs, slack funding,
diagonal risky-return covariance, separable score coordinates,
known finite laws and exact observations. It neither separates
manager skill from the unspanned premium in
\(x=\lambda_1+\alpha\) nor gives a calibrated history
recommendation, a binding-budget rate or a multiperiod rule.
The faster rate in the economic margin is the familiar smooth-entry
conversion of a quadratic value gap, specialized here to the
funded certificate and a moving ETF optimum.

The next certificate uses positive definite return risk to
control a moving ETF optimum even with trading costs and
binding constraints.

**Proposition 18 (Curvature certificate with costs and binding constraints; funded one-quarter model with known finite laws; machine checked).**
Use the one-quarter statistical model of Section 2 with one active
fund and one or two ETFs. Allow a compliant incumbent, position
caps, directional purchase and sale costs, ETF drag, correlated
risky returns and binding cash. Assume \(\gamma>0\) and a
positive definite realized-return covariance \(\Sigma\). The
known finite law of the factor and active-residual shock is
\(\zeta=JU\), where \(J\) is known,
\(\mathbb E U=0\), \(\mathbb E UU^\top=I_3\), and
\(\|U\|_2\leq9\) at every scenario. ETF residual shocks may
be correlated with these shocks, subject to the known joint
law and positive gross returns. With \(n\in\{1,2\}\) ETFs,
define the mean-exposure map and its error scale by

$$
Aw=(b(w),a),\qquad
K=\frac1\gamma\max_{z\in\mathbb R^{1+n},\ z\ne0}
   \frac{\|J^\top A z\|_2^2}{z^\top\Sigma z},
\qquad \Omega=JJ^\top .\tag{47}
$$

The maximum is attained and \(K\geq0\). The covariance
\(\Omega\) governs mean-estimation error; \(\Sigma\)
governs realized-return risk. Formula (47) compares their
action directions without adding them.

At the unprojected estimate \(\widehat\theta_N\), let
\(\widehat w_F\) and \(\widehat v_E\) be the unique funded
score maximizers over \(F\) and \(E\). Put

$$
\begin{aligned}
\widehat G
 &=Q(\widehat w_F;\widehat\theta_N)
   -Q(\widehat v_E;\widehat\theta_N)\geq0,\\
r_N&=\sqrt{t_{N,\eta}/N},\qquad u_N=K r_N^2,\\
\ell_N(\widehat w_F)
 &=\widehat G-\sqrt{2u_N\widehat G}-u_N/2
 \leq L_N(\widehat w_F)
 \quad\text{when }C_N\ne\varnothing.
\end{aligned}\tag{48}
$$

The lower bound compares the candidate with the *entire*
ETF-only class optimized at each parameter in \(C_N\). The
gate certifies \(\widehat w_F\) only if
\(\ell_N>\delta_{\rm econ}\geq0\); otherwise, including
an empty confidence set, it uses \(\widehat v_E\). A
positive certificate forces an active change
\(\widehat a\ne a^-\). For every fixed true parameter, the
unconditional probability of certifying an action whose true
advantage is at most \(\delta_{\rm econ}\) is at most \(\eta\).

Fix \(\delta>0\), \(0<\varepsilon\leq1/16\),
\(\eta=\varepsilon\), and
\(\delta_{\rm econ}=\delta/4\) before sampling. On
coverage, \(u_N\leq\delta/128\) and
\(G_*(\theta_*)\geq\delta\) imply
\(\ell_N>\delta/2\). For every law just described,

$$
N\geq\max\{324,1536K/\delta\}\log(6/\varepsilon)
\quad\Longrightarrow\quad
\begin{cases}
\Pr(\text{false certification})\leq\varepsilon
  &\text{at every }\theta_*,\\
\Pr(\text{correct certification})\geq1-\varepsilon
  &\text{if }G_*(\theta_*)\geq\delta.
\end{cases}\tag{49}
$$

Correct certification means implementing an active change
whose true advantage over the optimized ETF class exceeds
\(\delta/4\). If \(K=0\), estimation error affects no
score difference and \(\ell_N=G_*(\theta_*)\) almost surely
for every positive sample length; the empty-set fallback
still applies.

For a matching *class-level* comparison, fix
\(0<\kappa\leq1/10000\) and
\(0<\delta\leq\kappa/128\). Consider every admissible
design and known law above with \(K\leq\kappa\). If a common
history length permits a law-specific, possibly randomized
full-public-history rule meeting the same false-certification
and correct-certification requirements at every parameter,
then

$$
N\geq\frac{\kappa}{32\pi^2\delta}
       \log\frac1\varepsilon,
\qquad
N\geq1536\frac{\kappa}{\delta}
       \log\frac6\varepsilon
\quad\text{is sufficient for the class}.\tag{50}
$$

For (48), convex directional costs and positive definite
\(\Sigma\) give a quadratic score gap at either optimizer,
even at a cost kink or binding constraint. For a confidence
error \(e\), (47) bounds its paired score error along a
holding difference \(z\) by
\(r_N\sqrt{\gamma K z^\top\Sigma z}\). The full-class
gap bounds the difference between \(\widehat w_F\) and
\(\widehat v_E\); a second quadratic gap bounds movement of
the optimized ETF value by \(u_N/2\). Taking the infimum
over \(C_N\) yields (48). Finite-law calibration gives
coverage and a bounded-mean radius for (49). The lower
bound in (50) uses Proposition 17's zero-cost, slack-cash
subfamily with \(s=\sqrt\kappa\) and \(K=\kappa\); its
upper bound follows from (49).

Formula (48) requires exact global plug-in optima and score
values. For feasible numerical candidates
\(\widetilde w\in F\), \(\widetilde v\in E\), let
\(g=Q(\widetilde w;\widehat\theta_N)
-Q(\widetilde v;\widehat\theta_N)\). Let
\(\varepsilon_F,\varepsilon_E\geq0\) be *certified global*
upper bounds on their respective optimizer value gaps; these
imply \(g+\varepsilon_F\geq0\). A
reviewed paper proof, not machine checked, gives the following
lower bound when \(C_N\) is nonempty:

$$
g-\varepsilon_E-\sqrt{2u_N}
  \bigl(\sqrt{\varepsilon_F}+\sqrt{g+\varepsilon_F}\bigr)
  -u_N/2
\ \leq\ L_N(\widetilde w).\tag{51}
$$

A positive bound in (51) forces an active change and retains
coverage-based false-certification control, but the power rate
in (49) is not
proved for approximate optima. Feasibility, both value gaps
and numerical rounding must be certified; a solver status or
tolerance does not supply them. Simply adding the value gaps
without the square-root terms can give an invalid lower bound.

The order in (50) is a worst case over designs, with loose
constants; its hard design has zero costs and slack cash. It
does not prove that fees or binding constraints cause that
rate, or give a lower bound for each constrained instance.
The upper certificate covers those constraints under strict
risk curvature, but \(K\) also bounds potentially infeasible
directions and can be conservative. Known finite laws, exact
calibration, fixed loadings and risk inputs, and one review
remain assumptions. No empirical history recommendation or
separate identification of manager skill follows. Stability under
strong concavity is a standard perturbation principle; the result
here is the explicit whole-ETF-class certificate with directional
costs and binding constraints, not a new stability theorem.

Propositions 15--18 let a rule know the exact law of the
observation shocks. The next result removes that knowledge in
Proposition 16's family. It asks whether comparing with the whole
optimized ETF-only class lets a rule that does not know the law do
better than checking each ETF-only comparison separately.

**Proposition 19 (Certification without knowing the law: separate comparison bounds attain the known-law order; one-quarter model with bounded unknown laws; machine checked).**
Use Proposition 16's family: its loadings, funded classes, domain
\(\Theta\), known matrix \(J\) of operator norm at most
\(1/100\), active action \(w_A=(1,0)\), and the score
comparisons \(m_j(\theta)=d_j^\top\theta\) of \(w_A\) with
cash (\(j=0\)) and with the ETF (\(j=1\)). Call each
comparison a *face* of the optimized ETF-only comparator; by
(39), \(\operatorname{Adv}(w_A;\theta)=\min_jm_j(\theta)\).
Replace the class \(\mathcal K_J\) by the larger class
\(\mathcal L_J\) of finite laws of \(U\in\mathbb R^3\) with
\(\mathbb EU=0\) and \(\|U\|_2\leq9\), keeping the
observation shock \(JU\) and the zero ETF residual shock.
\(\mathcal L_J\) restricts neither the covariance nor the
skewness or higher moments of \(U\). Put

$$
\bar\sigma_j=\|J^\top d_j\|_2,\qquad
\bar\sigma=\max_{j=0,1}\bar\sigma_j,\qquad
R_j=9\bar\sigma_j,\qquad R=\max_{j=0,1}R_j.\tag{52}
$$

Every law in \(\mathcal L_J\) gives an admissible instance of
Section 2's statistical model with the advantage formulas (39).
Each face's per-record estimation error \(d_j^\top JU\) lies
in \([-R_j,R_j]\). On \(\mathcal K_J\subset\mathcal L_J\),
\(\bar\sigma_j\) equals Proposition 16's \(\sigma_j\).

A *law-free* rule is a single full-history rule, possibly
randomized, fixed before the law is chosen. It reads only the
public history and the known \(J\), and it either certifies a
funded active action or falls back to a funded ETF-only action.
Fix \(\delta>0\), \(\varepsilon\in(0,1)\),
\(\eta=\varepsilon\) and economic threshold \(\delta/4\)
before sampling. Proposition 16's two requirements must now
hold at *every* law in \(\mathcal L_J\). The false-certification
probability must be at most \(\varepsilon\) at every
\(\theta\in\Theta\). The probability of certifying an action
with true advantage above \(\delta/4\) must be at least
\(1-\varepsilon\) whenever \(G_*(\theta)\geq\delta\).

(i) *A joint confidence set reduces to two face bounds.* For
every nonempty set \(C\subset\mathbb R^3\),

$$
\inf_{\theta\in C}\operatorname{Adv}(w_A;\theta)
 =\min_{j=0,1}\ \inf_{\theta\in C}m_j(\theta).\tag{53}
$$

Suppose a rule certifies \(w_A\) using a data-dependent set
\(C_N\) that contains the true parameter with probability at
least \(1-\eta\) at every parameter. Its certificate is then
\(\min_j\ell_j\) with \(\ell_j=\inf_{C_N}m_j\), and each
\(\ell_j\) is a lower confidence bound for \(m_j(\theta)\) at
the full level \(\eta\). Conversely, face bounds with error
probabilities \(\eta_0\) and \(\eta_1\) give, by the union
bound, a set with coverage at least \(1-\eta_0-\eta_1\)
whose certificate is their minimum. So the only difference
between a joint and a face-by-face construction is the error
level of each face bound, \(\eta\) against \(\eta/2\). For
face bounds whose width at level \(a\) is proportional to
\(\sqrt{\log(1/a)}\), this changes the required history
length by the factor \(1+\log2/\log(1/\eta)\), which lies
between 1.23 and 1.24 at \(\eta=1/20\). Bounding the ETF face
through the cash face and a separate bound on the ETF premium
does not help either: \(d_1=d_0-e_2\) with
\(e_2=(0,1,0)\), and the range of that route,
\(R_0+9\|J^\top e_2\|_2\), is never below \(R_1\).

(ii) *A range rule.* For \(N\geq1\) and
\(\eta\in(0,1)\), put

$$
r_j=R_j\sqrt{\frac{3\log(2/\eta)}{N}},\qquad
\ell_j=d_j^\top\widehat\theta_N-r_j.\tag{54}
$$

The rule certifies \(w_A\) if
\(\min_j\ell_j>\delta_{\rm econ}\). Otherwise it implements
the plug-in ETF-only action: the ETF if
\(\widehat\lambda_{2}>0\), and cash otherwise, where
\(\widehat\lambda_{2}\) is the second coordinate of
\(\widehat\theta_N\). The rule uses \(J\) and nothing else
about the law. At every law in \(\mathcal L_J\), every
\(\theta\) and every \(\delta_{\rm econ}\geq0\), the
probability that it certifies \(w_A\) while
\(\operatorname{Adv}(w_A;\theta)\leq\delta_{\rm econ}\) is
at most \(\eta\). With \(\eta=\varepsilon\) and
\(\delta_{\rm econ}=\delta/4\), both requirements hold at
every law in \(\mathcal L_J\) once
\(N\geq\max\{3,22R^2/\delta^2\}\log(2/\varepsilon)\). When
\(\bar\sigma\geq\delta\), this length is
\(1782(\bar\sigma/\delta)^2\log(2/\varepsilon)\).

(iii) *The known-law order binds every law-free rule and is
attained.* Let \(0<\delta\leq\bar\sigma/8\) and
\(0<\varepsilon\leq1/16\). Then

$$
\begin{aligned}
\text{a law-free rule meets both requirements on }\mathcal L_J
&\Longrightarrow
N\geq\frac{\bar\sigma^2}{16\pi^2\delta^2}
      \log\frac1\varepsilon,\\
N\geq1782\frac{\bar\sigma^2}{\delta^2}
      \log\frac6\varepsilon
&\Longrightarrow
\text{the range rule meets both requirements on }\mathcal L_J.
\end{aligned}\tag{55}
$$

For (53), the infimum of a minimum of two functions is the
minimum of their infima. On the event that \(C_N\) contains
\(\theta\), each \(\ell_j\) is at most \(m_j(\theta)\), which
gives the full-level face bounds; the converse is the union
bound. For (54), the face error
\(d_j^\top(\widehat\theta_N-\theta)\) is the mean of \(N\)
independent, identically distributed, centered variables
bounded by \(R_j\). Hoeffding's inequality for bounded
independent and identically distributed variables
(`maurer2009empirical`, Theorem 1), applied after an affine map
of \([-R_j,R_j]\) onto \([0,1]\), bounds each one-sided tail
by \(\exp(-Nr_j^2/(2R_j^2))\leq\eta/2\). A union bound over the
two faces gives \(\ell_j\leq m_j(\theta)\) for both faces with
probability at least \(1-\eta\), and a certification then
forces \(\operatorname{Adv}(w_A;\theta)>\delta_{\rm econ}\).
If \(G_*(\theta)\geq\delta\), both
\(m_j(\theta)\geq\delta\); with probability at least
\(1-\varepsilon\) each \(\ell_j\geq\delta-2r_j\), which
exceeds \(\delta/4\) once \(r_j<3\delta/8\). The lower bound in
(55) is Proposition 16's: a single law-free rule meeting both
requirements on \(\mathcal L_J\) meets them on
\(\mathcal K_J\), where the law-specific lower bound (40)
already binds, with \(\sigma=\bar\sigma\).

Over a bounded law class, then, the optimized ETF-only
comparator in this family is exactly its two faces, and
certification without knowledge of the law is separate scalar
mean certification of each face. Its worst-case history length
has the same order,
\((\bar\sigma/\delta)^2\log(1/\varepsilon)\), as with a
known law. No law-free rule, whether joint, variance-adaptive
or otherwise, improves that order. The funded ETF-only
structure enters only through which faces exist and through
their ranges. The ETF face carries the error in the ETF
premium, which is why \(R_1\) and \(R_0\) differ, and the rate
takes the larger of the two. Joint constructions and variance
adaptation can change constants only, joint constructions by at
most the level factor in (i).

The result does not say that the range rule is efficient at a
particular law. Its constants and those of the lower bound are
about \(2.8\times10^5\) apart. At a given law, let
\(s_j\) be the standard deviation of the face error
\(d_j^\top JU\). The range rule can then need up to
\((R_j/s_j)^2\) times as many records as a rule that uses
\(s_j\); for laws in \(\mathcal K_J\) this factor is 81.
The order match is a worst case over \(\mathcal L_J\). The class assumes a known \(J\) and a known
bound on \(\|U\|_2\); laws with unknown range or unknown
\(J\) are outside it. The family is Proposition 16's two-face
geometry with zero costs, zero risk penalty, an all-cash
incumbent and the fixed active action \(w_A\), so this is not
a result about a general plug-in gate over data-selected
candidates, although (53) applies to any joint construction.
The level-factor comparison in (i) covers face bounds of the
stated width shape, not the best possible bound at each level.
There is one review with a fixed history length: no
time-uniform guarantee over repeated reviews and no sequential
lower bound is proved. Both contrasts load on
\(\lambda_1+\alpha\), so the result does not separate manager
skill from the unspanned premium. The upper bound applies
Hoeffding's inequality and a union bound, and the lower bound is
Proposition 16's two-point bound; the result is an application
of these tools, not a new testing principle.

We return to the funded two-review model. Propositions 12 and 13
show that future ETF adjustment can raise today's active-trading
advantage, but only in specific families. The last result asks
what decides the sign of that effect in every instance of the
model, and whether the sign can be reversed.

**Proposition 20 (Future ETF adjustment moves today's active advantage by a difference of premia at two root optima, capped by adjustable wealth, with both signs; funded two-review model; machine checked).**
Fix any instance of the funded two-review model of Section 2.
For a feasible root trade \(u_0\in F_0\) and a continuation
class \(R\in\{F,E,N\}\), let
\(c_R(u_0)=-\rho^{-1}\log(-H_0^R(u_0))\) be the certainty
equivalent of trading \(u_0\) today and then behaving optimally
within \(R\). Define the *premium of future ETF adjustment* and
the *premium of future active trading* at \(u_0\) by

$$
\varphi(u_0)=c_E(u_0)-c_N(u_0),\qquad
\psi(u_0)=c_F(u_0)-c_E(u_0).\tag{56}
$$

For every pair of classes,
\(CE_{D,R}=\max_{u_0\in D_0}c_R(u_0)\), and the maximum is
attained; \(\varphi\) and \(\psi\) are nonnegative on
\(F_0\). Let \(A_R\) be any maximizer of \(c_R\) over the
full root class \(F_0\), and \(B_R\) any maximizer over the
ETF-only root class \(E_0\).

(i) *Sandwich.* For every choice of these maximizers,

$$
\begin{aligned}
\varphi(A_N)-\varphi(B_E)
 &\leq\Delta_E-\Delta_N\leq
 \varphi(A_E)-\varphi(B_N),\\
\psi(A_E)-\psi(B_F)
 &\leq\Delta_F-\Delta_E\leq
 \psi(A_F)-\psi(B_E).
\end{aligned}\tag{57}
$$

(ii) *Funded cap.* Let \(\bar g\) and \(\underline g\) be
upper and lower bounds on every ETF gross return over all
parameters and scenarios, and put
\(\mathrm{up}=\max\{\bar g-1,0\}\) and
\(\mathrm{down}=\max\{1-\underline g,0\}\). Write
\(h_0^+\) for cash after the root trade and \(x_{0,j}^+\) for
the dollars then held in ETF \(j\). For every feasible root
trade,

$$
0\leq\varphi(u_0)\leq\beta(u_0)
 =\frac{h_0^+\,\mathrm{up}
   +\bigl(\sum_jx_{0,j}^+\bigr)\bar g\,
    (\mathrm{up}+\mathrm{down})}{W_0^-}.\tag{58}
$$

In particular \(\varphi(u_0)=0\) when \(u_0\) leaves neither
cash nor an ETF holding. Hence, if some full-root maximizer
\(A_E\) leaves neither, then
\(\Delta_E-\Delta_N\leq-\varphi(B_N)\leq0\).

(iii) *Movement of the no-active-trade region.* If
\(\Delta_N=0\) and \(\varphi(A_E)\leq\varphi(B_N)\), then
\(\Delta_E=0\), and by (28) some optimal full-root policy with
future ETF-only trading makes no active trade today. If
\(\Delta_E=0\) and \(\varphi(A_N)\geq\varphi(B_E)\), then
\(\Delta_N=0\), with the corresponding no-active-trade optimum
when no second trade is allowed.

(iv) *A family with the opposite sign.* Initial wealth one is
held entirely in cash. There is one active fund and one ETF with
\(B^A=(1,0)\), \(B^E=(0,1)\), zero ETF drag and
\(\rho=20\). Each quarter has one zero-shock scenario. Two
persistent parameters are \(\theta_+=(1/2,1/2,0)\), with prior
probability \(1/3\), and \(\theta_-=(1/2,-1/2,0)\), with prior
probability \(2/3\). The active fund's gross return is \(3/2\)
in every quarter under both parameters. The ETF's is \(3/2\)
under \(\theta_+\) and \(1/2\) under \(\theta_-\), so the first
public observation reveals the parameter. The four purchase and
sale rates vary independently over \([0,1/200]\) and are fixed
across reviews. For every member of this family,

$$
\begin{gathered}
CE_{E,N}=1,\qquad
CE_{E,E}\geq1+\frac1{50}-\frac1{320000},\qquad
CE_{F,N}\geq\frac{450}{201},\qquad
CE_{F,E}\leq\frac94,\\
\Delta_E-\Delta_N\leq\frac9{804}-\frac1{50}+\frac1{320000}
 <-\frac1{125},
\end{gathered}\tag{59}
$$

and both \(\Delta_N\) and \(\Delta_E\) are positive. The root
trade that puts all cash into the active fund is feasible and
has \(\varphi=0\), while staying in cash at the root has
\(\varphi\geq1/50-1/320000\). With Proposition 12, both signs
of \(\Delta_E-\Delta_N\) occur in the funded two-review model.

The attainment statements come from Proposition 11. The
sandwich uses only feasibility and optimality. Since \(A_N\) is
feasible for the full root under future ETF-only trading,
\(CE_{F,E}\geq c_E(A_N)=CE_{F,N}+\varphi(A_N)\). Since
\(B_E\) maximizes \(c_E\) over \(E_0\) and
\(c_N(B_E)\leq CE_{E,N}\),
\(CE_{E,E}\leq CE_{E,N}+\varphi(B_E)\). Subtracting gives the
lower bound in (57); the other three bounds are the same
argument. For the cap, fix a second-review node. An ETF-only
trade there changes terminal wealth, relative to no trade, by
its purchases times the ETF's excess over cash, plus its sales
times the ETF's shortfall, minus charges. Purchases are funded
by cash and sale proceeds, and sales cannot exceed ETF holdings,
so on every path the gain is at most \(W_0^-\beta(u_0)\).
Exponential utility turns a constant wealth gain into a
multiplication of utility by \(\exp(-\rho\beta(u_0))\), which
gives \(c_E\leq c_N+\beta\). Part (iii) combines (57) with
\(\Delta_R\geq0\) and (28). In (iv), holding cash gives
\(CE_{E,N}=1\), and no ETF-only root does better without a
second trade, because the ETF's expected two-quarter gross
return is \(11/12\). Waiting in cash and buying the ETF only
after observing its gain gives the bound on \(CE_{E,E}\).
Putting all cash into the active fund gives \(CE_{F,N}\). No
funded policy ends above \(9/4\) on any path, which bounds
\(CE_{F,E}\).

The sign of the effect of future ETF adjustment on today's
active advantage is therefore decided by comparing the premium
of that future adjustment at a full-root optimum with its
premium at an ETF-only-root optimum. This is the
increasing-differences comparison of monotone comparative
statics, written directly for these matched controls; nothing
in (i) or (iii) is specific to funding. Increasing differences
of \(c_R\) in the root active dollars and the future menu,
ordered \(N<E\), is the hypothesis of Topkis's comparative-statics
theorem (`milgrom1994monotone`, Theorem 5 and the definition
preceding it, full text reviewed). It would make \(\varphi\)
nondecreasing in the root active holding. If, in addition,
\(\varphi\) did not depend on the root ETF holding and \(A_N\)
held at least the incumbent active position, (57) would give a
nonnegative effect. The family in (iv) shows that increasing
differences fails in the funded two-review model: \(\varphi\)
is zero at the all-active root and at least
\(1/50-1/320000\) at the all-cash root, so it is lower at
the root with more active dollars.

What funding adds is the cap (58). The premium of future ETF
adjustment is bounded by the wealth that can still be
redeployed, cash and ETF holdings, and a root purchase of the
active fund, which the ETF-only continuation cannot trade,
consumes that wealth. A root that spends everything on the
active fund makes future ETF adjustment a substitute for today's
active trade, as in (iv). There the ETF-only root instead keeps
cash, learns the parameter and then buys the ETF only if it is
the winner; this is a value of waiting to learn. In Propositions
12 and 13, by contrast, the full root keeps an ETF position
beside the active fund and sells it after learning, and future
ETF adjustment acts as a complement to today's active trade.
That contrast is a reading of the three families, not a
theorem. No sign holds across the model.

Parts (i)--(iii) are exact but give no closed-form sign
condition: the premia at the optimizers are defined through
optimized continuation values, and this result bounds them only
by the cap; Proposition 21 sharpens it. The cap is one-sided and crude. It ignores costs and uses
the extreme ETF returns, so the corner condition in (ii) is
sufficient for a nonpositive effect but does not characterize
it. The family in (iv) is degenerate in the same way as
Proposition 12's. It has no conditional return risk, full
revelation, assumed returns of plus or minus \(50\%\),
\(\rho=20\) and known zero alpha: the active advantage is a
known factor premium. It shows that the negative sign exists
with a margin, not its magnitude or its robustness. It does not
assert that the all-active root is the exact optimum when rates
are positive. No movement of the no-active-trade region itself
is exhibited, since the active trade is made under both
continuation classes here and in Proposition 12; (iii) states
what such a movement would require. Public information is the
same under all controls, so the result does not separate
learning from the change in the future menu, and it says
nothing about alpha as distinct from factor premia. Whether the
weaker single-crossing property of Milgrom and Shannon holds
in this model is not examined.

Proposition 20 decides the sign by comparing premia at two
optima, but it bounds each premium only from above, by a crude
cap. The next result asks how sharp a cap on the premium can be.
It shows that no cap built from wealth and return ranges alone
can separate premia of a few basis points, and it gives sharper
caps that use risk-adjusted mean returns.

We first split the premium across public observations. Fix a
feasible root trade \(u_0\). A *node* is a first-review
observation \(y\) with \(P_0(y)>0\), and its *node paths* are
the pairs \((\theta,s_1)\) with \(\pi_1(\theta\mid y)>0\) and
\(q_{s_1}>0\). In units of initial wealth \(W_0^-\), let \(h\)
be the cash left after the root trade and \(m_j(y)\) the marked
value of ETF \(j\) at \(y\). Let
\(c^R_y=-\rho^{-1}\log(-V_1^R(x_1^-(y;u_0),h_1^-(u_0),\pi_1(\cdot\mid y)))\)
be the certainty equivalent at \(y\) with continuation class
\(R\), and call \(G_y=c^E_y-c^N_y\geq0\) the *node gain*: the
value at \(y\) of being allowed an ETF-only trade rather than
none. With weights
\(w_y\propto P_0(y)\exp(-\rho c^N_y)\) summing to one, write

$$
\mathcal A_{u_0}(\ell)
 =-\frac1\rho\log\sum_yw_y\exp(-\rho\ell_y)\tag{60}
$$

for any node-wise numbers \(\ell_y\). \(\mathcal A_{u_0}\) is
strictly increasing in each \(\ell_y\), and
\(\varphi(u_0)=\mathcal A_{u_0}(G)\). Node-wise bounds on the
gains therefore give bounds on the premium. On the node paths,
let \(g_j\) be ETF \(j\)'s second-quarter gross return, with
largest and smallest values \(\bar g_{j,y}\) and
\(\underline g_{j,y}\), and let \(W^N_y\) be terminal wealth
without a second trade. The *tilted node measure* \(Q_y\)
weights each node path by its probability times
\(\exp(-\rho W^N_y)\), normalized. The *risk-adjusted excess
returns* of buying and selling ETF \(j\) are

$$
r^+_{j,y}=\mathbb E_{Q_y}\!\left[\frac{g_j-1-\kappa^+_j}
                                  {1+\kappa^+_j}\right],\qquad
r^-_{j,y}=\mathbb E_{Q_y}\!\left[1-\kappa^-_j-g_j\right].
$$

Finally, let \(\mathrm{up}_y\) and \(\mathrm{down}_y\) be the
largest \(\max\{\bar g_{j,y}-1,0\}\) and
\(\max\{1-\underline g_{j,y},0\}\) over ETFs, put
\(G^{\rm ub}_y=h\,\mathrm{up}_y+\sum_jm_j(y)
(\mathrm{up}_y+\mathrm{down}_y)\), the node form of the cap
(58), and \(\beta_{\rm node}(u_0)=\mathcal A_{u_0}(G^{\rm ub})\).

**Proposition 21 (Caps on the premium of future ETF adjustment: range-based caps cannot be sharp, and mean-based caps vanish exactly when no favorable trade has wealth; funded two-review model; machine checked, with a numerical comparison observed on assumed instances).**
Fix any instance of the funded two-review model.

(i) *Range-based caps.* Call a function \(C\) of the node data
(cash \(h\), marked ETF values \(m_j\), purchase and sale rates,
\(\rho\), and each ETF's return range
\([\underline g_j,\bar g_j]\) over the node paths, both ends
attained) a *range-type cap* if \(G_y\leq C\) at every node of
every instance with those data. For data that some node has, and
every ETF \(j\),

$$
C\geq h\left[\frac{\bar g_j}{1+\kappa^+_j}-1\right]^+,
\qquad
C\geq m_j\left[1-\kappa^-_j-\underline g_j\right]^+.\tag{61}
$$

Each right side is the gain from putting all cash into ETF \(j\)
at its best return, or selling all of it at its worst, and for
every \(\varepsilon>0\) some node with the same data has a gain
within \(\varepsilon\) of it. \(G^{\rm ub}_y\) is a range-type
cap. The bounds (61) do not bound \(G^{\rm ub}_y\) from below
by any factor: with one ETF, no cash and every node-path return
at least one, the gain is zero while \(G^{\rm ub}_y=m(\bar g-1)\).

(ii) *Tangent cap.* Let \(T_y\) be the largest first-order gain
of a feasible second-review ETF-only trade \(u\), in units of
\(W_0^-\), from the gain
\(\sum_j[(1+\kappa^+_j)r^+_{j,y}u_j^++r^-_{j,y}u_j^-]\), where
\(u_j^+\) and \(u_j^-\) are the purchase and sale of ETF \(j\).
Then

$$
G_y\leq T_y\leq
\Bigl(h+\sum_jm_j(y)\Bigr)
  \max_j\bigl((1+\kappa^+_j)r^+_{j,y}\bigr)^+
 +\sum_jm_j(y)\bigl(r^-_{j,y}\bigr)^+
\leq G^{\rm ub}_y.\tag{62}
$$

With one ETF, \(T_y=\max\{r^+_yh,\ r^-_ym(y),\ 0\}\).
\(T_y=0\) exactly when the node has *no adjustable wealth in
any favorable direction*: for every ETF \(j\), \(h=0\) or
\(r^+_{j,y}\leq0\) (no favorable purchase with cash); for every
ETF \(k\), \(m_k(y)=0\) or \(r^-_{k,y}\leq0\) (no favorable
sale); and for every \(k\) with \(m_k(y)>0\) and every \(j\),
\(r^-_{k,y}+(1-\kappa^-_k)r^+_{j,y}\leq0\) (no favorable switch
from \(k\) into \(j\)). Then \(G_y=0\). With one ETF the first
two conditions suffice, since a round trip in one ETF never
gains.

(iii) *Curvature cap, one ETF.* For buying, let
\(Z=(g-1-\kappa^+)/(1+\kappa^+)\) per dollar of cash, with
\(r=r^+_y\) and \(\bar\epsilon=h\); for selling, let
\(Z=1-\kappa^--g\) per ETF dollar, with \(r=r^-_y\) and
\(\bar\epsilon=m(y)\). Let \(\Delta W\) bound the range of
\(W^N_y\) over the node paths, let \([g_l,g_u]\) contain the
ETF's node-path returns, \(s=(g_u-g_l)/2\), and let
\(\operatorname{Var}_q(Z)\) be the variance of \(Z\) under the
node-path probabilities. With
\(v_{\min}=\exp(-\rho(\Delta W+2s\bar\epsilon))
\operatorname{Var}_q(Z)\), trading any amount in
\([0,\bar\epsilon]\) in that direction gains at most

$$
\bar q(r,v_{\min})=
\begin{cases}
0,& r\leq0,\\
r^2/(2\rho v_{\min}),& 0<r\leq\rho v_{\min}\bar\epsilon,\\
r\bar\epsilon-\rho v_{\min}\bar\epsilon^2/2,& \text{otherwise},
\end{cases}\tag{63}
$$

and \(G_y\) is at most the larger of the buying and selling
values.

(iv) *Aggregation and sign conditions.* For any number of ETFs,
let \(\bar T_y\) be the explicit middle bound in (62); then
\(\varphi(u_0)\leq\mathcal A_{u_0}(\bar T)\leq
\beta_{\rm node}(u_0)\). With one ETF, let
\(\beta_{\rm mean}(u_0)\) aggregate by (60) the smaller of
\(T_y\) and the curvature cap at each node. Then
\(\varphi(u_0)\leq\beta_{\rm mean}(u_0)\leq
\beta_{\rm node}(u_0)\).
With one ETF and Proposition 20's maximizers, let \(\ell_y\) be
any node-wise lower bounds on the gains at \(B_N\). If
\(\beta_{\rm mean}(A_E)<\mathcal A_{B_N}(\ell)\), then
\(\Delta_E-\Delta_N<0\). Symmetrically, with lower bounds on
the gains at \(A_N\), if
\(\beta_{\rm mean}(B_E)<\mathcal A_{A_N}(\ell)\), then
\(\Delta_E-\Delta_N>0\).

For (i), take one parameter, a riskless active fund and a node
at which ETF \(j\) earns \(\bar g_j\) except with a small
probability \(\eta\) that realizes the rest of the range; buying ETF \(j\) with
all cash then gains nearly the first bound in (61) as \(\eta\)
falls to zero, with the node data unchanged, and a sale with the
masses reversed gives the second. For (ii), the certainty
equivalent at a node is concave in the second-review trade, so
the gain is at most the first-order gain of the trade from
zero. Every feasible trade is a nonnegative combination of cash
purchases, sales and switches, so the first-order gain is
nonpositive for all trades exactly when it is for these three
kinds. For (iii), the second derivative of the certainty
equivalent along one direction is \(-\rho\) times the variance
of \(Z\) under a tilted measure, and each tilted path weight is
at least \(\exp(-\rho(\Delta W+2s\bar\epsilon))\) times its
probability. Integrating twice bounds the gain by (63). Part
(iv) follows from (60), because \(\mathcal A\) is increasing in
each node value, and from Proposition 20's sandwich.

A cap that sees only cash, holdings and return ranges cannot be
smaller than the gain from staking all adjustable wealth on the
best return in the range, because a return law concentrated near
that return has the same data. Caps that use risk-adjusted means
are sharper. They vanish exactly at nodes where no favorable
purchase, sale or switch has wealth to trade. This refines the
corner of Proposition 20: what matters is not idle wealth as
such but wealth available in a favorable direction.

The following comparison is numerical and not part of the
proposition. It uses six zero-cost, one-ETF instances of the
two-review model with nondegenerate return risk, partial learning
about a nonzero uncertain alpha, assumed quarterly factor premia
of 1 to 4 percent, and \(\rho\in\{5,10,20\}\), with optimizers
computed by a numerical convex solver. There the premia at the
root optima are 2.66 to 19.86 basis points per quarter of
initial wealth. The aggregated bounds (61) at the full root's
optimizers are 332 to 1023 basis points, so no range-type cap
certifies any of these signs. Where the premium is positive,
\(\beta_{\rm mean}\) is 1.36 to 15.4 times the premium. The
conditions in (iv) certify the positive sign in the two
instances with \(\rho=20\). There the ETF-only root's optimizers
sell the whole ETF position at the root, so at every node the
only favorable direction, selling, has nothing to sell, and the
premium is exactly zero. The other four signs are not certified:
the premia at the two optima differ by 23 to 63 percent, while
the caps at the compared optima are 1.41 to 6.5 times the
premium. A cap within a factor of 1.05 to 1.96 of the premium
would certify them. None is given, and no obstruction to one is
shown.

The proposition applies standard tools: an attained supremum
over laws with a given range, the tangent-plane bound for a
concave certainty equivalent, and a lower bound on a tilted
variance. The curvature cap is stated for one ETF, and its
tilted-variance bound discounts by the full wealth range, which
is crude. The numerical comparison uses solver optimizers of one
assumed base design at zero costs, so its certifications are
numerical observations, not theorems. The zero-premium corner at
\(\rho=20\) is observed from those optimizers, not derived.
Where the two premia are within the caps' factor, the sign has
to be computed for the instance; no structural inequality here
decides it. Nothing is shown about movement of the
no-active-trade region.

We return to the funded one-quarter model for a different
question: can the choice of factor exposure be separated from the
choice of funds? A common procedure first chooses a target factor
exposure and then chooses funds, charging the second stage for
missing the target. The last result identifies what that procedure
optimizes and bounds its loss against choosing everything jointly.

Write the factor shock covariance, and the cross and residual
second moments of a holding \(w=(a,p)\), as

$$
\Sigma_f=\mathbb E_q z^f(z^f)^\top,\qquad
C(w)=\mathbb E_q\bigl[z^f(az^A+p^\top z^E)\bigr],\qquad
R(w)=\mathbb E_q\bigl[(az^A+p^\top z^E)^2\bigr],\tag{64}
$$

so that \(w^\top\Sigma w=b(w)^\top\Sigma_fb(w)+2b(w)^\top C(w)
+R(w)\). Let \(J=\max_{w\in F}\bar Q_0(w)\) be the joint optimum,
attained at some \(w_J\) with exposure \(b_J\) (Proposition 4).

**Proposition 22 (A soft-target two-stage procedure is the joint problem with target-implied premia, and its loss is bounded by the first stage's multiplier; funded one-quarter model; machine checked).**
Fix any instance of the funded one-quarter model and evaluate the
score at the belief mean, as in (6). In *stage 1*, choose a convex
set \(\mathcal R\) of exposures containing every funded exposure
\(b(F)\), and a target \(b^*\) that maximizes the factor objective
\(G(b)=b^\top\bar\lambda-(\gamma/2)b^\top\Sigma_fb\) over
\(\mathcal R\). A natural choice is
\(\mathcal R_0=\{b(w):w\geq0,\ \sum_iw_i\leq1\}\), which contains
\(b(F)\) because funded holdings are nonnegative and sum to at most
one. Stage 1 sees only \(\bar\lambda\), \(\Sigma_f\), \(\gamma\) and
\(\mathcal R\). Its *multiplier vector* is
\(\nu=\bar\lambda-\gamma\Sigma_fb^*\), the gradient of \(G\) at the
target. In *stage 2*, maximize over \(w\in F\)

$$
S(w)=a\bar\alpha-p^\top c^E-\tau(w-w^-)
 -\frac\gamma2\Bigl[(b(w)-b^*)^\top\Sigma_f(b(w)-b^*)
 +2b(w)^\top C(w)+R(w)\Bigr],\tag{65}
$$

which charges factor risk on the distance from the target rather
than confining the holding to it. Let \(w_2\) be a maximizer, with
exposure \(b_2\), let \(T_s=\bar Q_0(w_2)\), and write
\(\Lambda_s=J-T_s\geq0\), \(\Delta e=b_J-b_2\) and
\(\Delta w=w_J-w_2\).

(i) *Identification.* For every \(w\),

$$
S(w)=\bar Q_0(w)-\nu^\top b(w)-\frac\gamma2 b^{*\top}\Sigma_fb^*.\tag{66}
$$

So stage 2 is the joint problem with the believed premia
\(\bar\lambda\) replaced by the *target-implied premia*
\(\gamma\Sigma_fb^*\), up to a constant. If \(\nu=0\), every
stage-2 maximizer is a joint maximizer and \(\Lambda_s=0\).

(ii) *Multiplier bound.* For any set of holdings, convex or not,
and any maximizers,
\(0\leq\Lambda_s\leq\nu^\top\Delta e\), with equality in the
second inequality exactly when \(w_J\) also maximizes \(S\). Hence
\(\Lambda_s\leq\|\nu\|\,\|\Delta e\|\) in the Euclidean norm, and
\(\Lambda_s=0\) when the two solutions share an exposure. Moreover
\(\nu^\top\Delta e\leq\nu^\top(b^*-b_2)\), so \(\Lambda_s=0\) also
when stage 2 reaches the target.

(iii) *Exact form.* With \(F\) convex,

$$
\Lambda_s=\nu^\top\Delta e-\frac\gamma2\,\Delta w^\top\Sigma\,\Delta w-s,
\qquad s\geq0,\tag{67}
$$

where \(s\) is the sum of the first-order optimality slack of
\(w_2\) in the direction \(\Delta w\) and a cost-kink term. The
kink term is zero when no instrument's trade changes sign between
\(w_2\) and \(w_J\). So the loss is at most the multiplier's value
on the exposure difference, less the risk of the holding move.

(iv) *A target-confined comparison.* For any \(w_T\in F\) with
\(b(w_T)=b^*\),
\(T_s\geq\bar Q_0(w_T)-\nu^\top(b^*-b_2)\). So the soft procedure
gives up at most \(\nu^\top(b^*-b_2)\) relative to any holding that
meets the target exactly. The bound is vacuous when no funded
holding meets it.

(v) *The multiplier.* \(\nu=\bar\lambda-\gamma\Sigma_fb^*\) lies in
the normal cone of \(\mathcal R\) at \(b^*\), so it is the
multiplier of the stage-1 constraint \(b\in\mathcal R\), and
\(\nu=0\) when \(b^*\) is interior to \(\mathcal R\).

Expanding the target distance in (65) gives (66). Since \(w_J\) is
feasible in stage 2, \(S(w_J)\leq S(w_2)\), which by (66) is the
first bound in (ii). The target maximizes the concave \(G\) over
the convex \(\mathcal R\), so \(\nu^\top(b-b^*)\leq0\) for every
\(b\in\mathcal R\), in particular for \(b_J\); this gives the
second bound in (ii) and part (v). For (67), move along the
segment from \(w_2\) to \(w_J\): the score is a concave quadratic
plus a convex, piecewise-linear cost, so the change in \(S\) is its
one-sided directional derivative, which is nonpositive at the
maximizer, minus the quadratic term and minus a nonnegative kink
term. Part (iv) is (ii)'s comparison with \(w_T\) in place of
\(w_J\).

Charging the second stage for distance from the target is the same
as re-running the joint problem with the returns the target
implies. The loss is therefore at most the first stage's constraint
multiplier applied to the exposure the joint choice takes beyond
the target. The funded budget enters only through that multiplier:
when the unconstrained factor optimum is admissible, \(\nu=0\) and
the procedure recovers the joint optimum, as the classical
separation results would suggest. The argument is weak duality for
the relaxed stage-1 constraint and is elementary. The result says
nothing about the size of the loss in particular portfolios, and
the converse of (ii) fails: when \(\nu=0\), the loss is zero
whatever the exposures. It treats only the procedure (65), in which
stage 2 keeps the believed alpha and the ETF fee term; a variant
that drops them is not the joint problem at any premia. It gives
no ordering between this procedure and one that confines stage 2
to holdings meeting the target exactly (Proposition 23). Stage 1's
maximum is attained on \(\mathcal R_0\); for a general
\(\mathcal R\) it is assumed.

Proposition 22 lets the second stage drift from the target. The
stricter procedure confines the second stage to holdings whose
exposure equals the target. Its loss has an exact description in
terms of how the best residual choice depends on the exposure.

Split the belief-mean score into a part that depends only on
exposure and a residual part. With (64), for every \(w\),

$$
\bar Q_0(w)=G(b(w))+H(w),\qquad
H(w)=a\bar\alpha-p^\top c^E-\frac\gamma2\bigl[2b(w)^\top C(w)+R(w)\bigr]
 -\tau(w-w^-),\tag{68}
$$

where \(G\) is Proposition 22's factor objective and \(H\) is the
*residual objective*: alpha, ETF fees and drag, cross and residual
risk, and trading costs. Let \(B_F=b(F)\) be the set of funded
exposures, and for \(b\in B_F\) let

$$
V(b)=\max\{H(w):w\in F,\ b(w)=b\}\tag{69}
$$

be the *residual value* of exposure \(b\): the best residual
outcome among funded holdings with that exposure.

**Proposition 23 (Target-confined two-stage procedure: exact loss, exact separation criterion, and the funded failures of separation; funded one-quarter model; machine checked, with a numerical illustration on calibrated factor inputs).**
Fix any instance of the funded one-quarter model. \(B_F\) is
nonempty, convex and compact, and \(V\) is attained on every
exposure. \(G+V\) is concave on \(B_F\), and the joint optimum is
\(J=\max_{B_F}(G+V)=G(b_J)+V(b_J)\) for any joint maximizer's
exposure \(b_J\). \(V\) itself is concave when the cross moments
vanish on \(F\) (\(C(w)=0\)), but not in general. In *stage 1*,
choose a target \(b^*\) that maximizes \(G\) over \(B_F\): the case
\(\mathcal R=B_F\) of Proposition 22, using only \(\bar\lambda\),
\(\Sigma_f\), \(\gamma\) and the funded exposure set. When
\(\Sigma_f\) is positive definite and \(\gamma>0\), the unconstrained
target \(\Sigma_f^{-1}\bar\lambda/\gamma\) is the unique such maximizer
whenever it lies in \(B_F\). In *stage 2*, choose \(w\in F\) with
\(b(w)=b^*\) to maximize \(H\), which attains \(V(b^*)\). Write
\(T=G(b^*)+V(b^*)\) and \(\Lambda=J-T\geq0\).

(i) *Loss identity.*

$$
\Lambda=\bigl[V(b_J)-V(b^*)\bigr]-\bigl[G(b^*)-G(b_J)\bigr],\tag{70}
$$

and both brackets are nonnegative. The loss is the residual value's
gain from moving the exposure from the factor optimum to the joint
one, less what that move costs the factor objective.

(ii) *Exact separation.* \(T=J\) if and only if \(b^*\) maximizes
\(G+V\) on \(B_F\), that is, if and only if zero is a supergradient
of \(G+V\) at \(b^*\) relative to \(B_F\). In particular \(T=J\)
when \(V\) is constant on \(B_F\), and whenever
\(V(b)\leq V(b^*)\) for all \(b\in B_F\). If \(V\) is concave,
\(\Sigma_f\) is positive definite, \(\gamma>0\) and \(b^*\) lies in
the relative interior of \(B_F\), then \(T=J\) exactly when
\(V(b)\leq V(b^*)\) on \(B_F\): the residual value must be
maximized at the factor optimum.

(iii) *Loss bound.* With \(\|b\|_{\Sigma_f}^2=b^\top\Sigma_fb\),

$$
\Lambda\leq V(b_J)-V(b^*)-\frac\gamma2\|b_J-b^*\|_{\Sigma_f}^2,
$$

and if \(V\) is \(L\)-Lipschitz on \(B_F\) in that norm, then
\(\Lambda\leq\min\{L^2/(2\gamma),\ L\|b_J-b^*\|_{\Sigma_f}\}\).

(iv) *When the residual value is flat, and why funding makes it
not flat.* Suppose the ETFs have no residual shock, drag or trading
cost, the cross moments vanish, and every exposure in \(B_F\) can be
reached by a funded holding whose active position maximizes
\(a\bar\alpha-(\gamma/2)a^2R_A-\tau_A(a-a^-)\) over the active
fund's allowed range, with \(R_A\) its residual variance. Then \(V\)
is constant, \(T=J\), and the procedure recovers the joint optimum.
With one active fund whose loading lies outside the ETF span, the
exposure fixes the active position, so stage 1 chooses the manager.

For (i), \(w_J\) maximizes \(H\) among holdings with its own
exposure, so \(J=G(b_J)+V(b_J)\); subtracting \(T\) gives (70), and
\(G(b^*)\geq G(b_J)\) because \(b^*\) maximizes \(G\) on \(B_F\).
Part (ii) is (i) together with concavity of \(G+V\), which holds
because maximizing the concave \(\bar Q_0\) over the holdings with a
given exposure preserves concavity. The converse under concave
\(V\) uses the sum rule for supergradients on the affine hull of
\(B_F\), where the gradient of \(G\) vanishes at a relatively
interior optimum. Part (iii) substitutes the strong-concavity gap
\(G(b^*)-G(b_J)\geq(\gamma/2)\|b_J-b^*\|^2_{\Sigma_f}\) into (70)
and maximizes \(Lx-(\gamma/2)x^2\) over \(x\geq0\). In (iv) the
residual objective depends on the active position alone, and every
exposure admits the best one.

The criterion is that separation is exact when the best residual
choice does not care which exposure it must deliver at the factor
optimum. The flat case in (iv) is the world of the Treynor–Black
benchmark discussed in Section 4. A funded, long-only menu breaks
that flatness in ways a feasibility check on the target does not
see, each making \(V\) depend on the exposure. First, the active
fund carries factor loadings, so the exposure target bounds the
active position, and fixes it when the fund's loading is outside
the ETF span (manager-borne exposure). Second, when cash binds,
buying ETFs to reach an exposure spends the budget the active
position needs (shared budget). Third, directional ETF costs and
drag put a kink in \(V\) at the incumbent's exposure. Of these,
only the first is a formal conjunct, in the case stated in (iv);
the shared-budget and cost channels are explanations, not
theorems. Compared with Proposition 22's soft procedure, part (iv)
there gives \(\Lambda_s\leq\Lambda+\nu^\top(b^*-b_2)\) when
\(\mathcal R=B_F\). No ordering of the two losses holds in general.

The following comparison is numerical and not part of the
proposition. It uses calibrated factor means and shock sizes,
assumed residual risks and drag, an active cap of one, \(\gamma=5\),
and three menus: an ETF that reproduces the active fund's loading, a
missing factor direction, and an infeasible match. Costs are zero
or 5 basis points, and the joint problem and both stages are solved
numerically. The unconstrained target lies outside \(B_F\) in every
case, because the long-only ETF menu cannot reach its
factor-exposure ratio without shorting. The loss is at most 0.08
basis points per quarter at zero alpha. It is 0.4 to 2.9 basis
points at alpha of \(+25\) and \(+50\) basis points, where the
target caps the active holding. It is 2.4 to 22.4 basis points at
alpha of \(-25\) and \(-50\) basis points in the missing-direction
and infeasible menus, where the target forces holding a fund the
joint optimum sells.

The result is an application of partial maximization, a comparison
of attained maxima and a strong-concavity gap. The "only if"
direction of (ii) at the residual value needs \(V\) concave; with
factor-correlated residuals \(V\) can be convex at the target while
\(G+V\) is still maximized there. The Lipschitz constant \(L\) is
not computed. The flat case in (iv) is one sufficient condition, not
a characterization. The result uses belief means in one quarter and
says nothing about estimated inputs or later reviews. The numerical
comparison uses solver outputs on one calibration.

We return last to the repeated-sampling certification model.
Proposition 19 showed that, in one family, the optimized ETF-only
comparator is exactly two faces. The final result asks when the
whole funded comparator reduces to a finite set of fixed ETF-only
holdings in general.

In that model the conditional score is affine in the parameter:
with the mean-exposure matrix \(A\) of (47),
\(Q(w;\theta)=\theta^\top Aw+c(w)-(\gamma/2)w^\top\Sigma w\), where
\(c(w)=-p^\top c^E-\tau(w-w^-)\). For a sign pattern
\(\sigma\in\{+1,-1\}^{1+n}\), the *cost-sign cell*
\(F_\sigma=\{w\in F:\sigma_i(w_i-w^-_i)\geq0\text{ for all }i\}\)
collects the funded holdings that buy or sell each instrument in the
pattern's direction. The cells \(E_\rho\) of the ETF-only class are
defined in the same way over the ETF coordinates, with the active
holding fixed. The *face sets* \(\operatorname{Vert}(F)\) and
\(\operatorname{Vert}(E)\) are the unions of the cells' extreme
points. For \(v\in E\), the *single-comparator contrast* is
\(m_v(w;\theta)=Q(w;\theta)-Q(v;\theta)\). Let \(A_{N,\eta}\) be the
ellipsoid of Section 2 before intersection with \(\Theta\), so that
\(C_N=\Theta\cap A_{N,\eta}\).

**Proposition 24 (The optimized ETF-only comparator is a finite face set exactly when the score is linear or the ETF-only optimizer does not move; one-quarter model with known finite laws; machine checked, with the finiteness of the faces conditional on the linear-programming vertex theorem).**
Fix any admissible instance of the repeated-sampling certification
model, with one or two ETFs, position caps, a compliant incumbent,
directional rates and signed ETF drag.

(i) *Finite faces fixed by the funded geometry.* Each cell is a
nonempty compact polyhedron containing the incumbent, cut out by
\(3(1+n)+1\) halfspaces for \(F\) and \(3n+1\) for \(E\). The face
sets are finite, conditional on the linear-programming vertex
theorem, and depend only on the caps, the incumbent, its cash
and the rates, not on the parameter, the law, \(\Sigma\), \(\gamma\)
or the drag. At most
\(|\operatorname{Vert}(E)|\leq2^n\binom{3n+1}{n}\) and
\(|\operatorname{Vert}(F)|\leq2^{n+1}\binom{3n+4}{n+1}\). With one
ETF,

$$
\operatorname{Vert}(E)=\Bigl\{(a^-,0),\ (a^-,p^-),\
\bigl(a^-,\ p^-+\min\{\bar p-p^-,\ k^-/(1+\kappa^+_E)\}\bigr)\Bigr\}:\tag{71}
$$

sell the ETF out, hold it, or buy it up to the cap or until cash
runs out.

(ii) *Exact finite reduction when \(\gamma=0\).* For every parameter
\(\theta\) and every \(w\in F\), the class optima are attained on the
faces, and

$$
\operatorname{Adv}(w;\theta)=\min_{v\in\operatorname{Vert}(E)}m_v(w;\theta),
\qquad
\inf_{\theta\in C}\operatorname{Adv}(w;\theta)
 =\min_{v\in\operatorname{Vert}(E)}\ \inf_{\theta\in C}m_v(w;\theta)\tag{72}
$$

for every set \(C\) of parameters, with each \(m_v(w;\cdot)\) affine.
In particular \(L_N(w)\) is a minimum of finitely many convex
programs when \(C_N\) is nonempty. Over the ellipsoid \(A_{N,\eta}\),
with \(d_v=A(w-v)\) and \(r_N=\sqrt{t_{N,\eta}/N}\),

$$
\ell_N(w)=\min_{v\in\operatorname{Vert}(E)}
 \Bigl[m_v(w;\widehat\theta_N)-r_N\sqrt{d_v^\top\Omega d_v}\Bigr]
 \leq L_N(w)\tag{73}
$$

when \(C_N\) is nonempty. This is a paired mean-uncertainty penalty,
minimized over the finite faces. The plug-in full and ETF-only
optimizers selected by the model's gate are themselves faces, so every
contrast vector a history can require lies in a finite set \(D\) fixed
before sampling.

(iii) *What a confidence construction needs when \(\gamma=0\).* If,
on some event, each \(d\in D\) has \(d^\top\theta_*\) in an interval
\(I_d\), then the rule that certifies the plug-in full optimizer when
\(\min_v[\inf I_{A(\hat w_F-v)}+c(\hat w_F)-c(v)]>\delta_{\rm econ}\)
never falsely certifies on that event, whichever candidate the data
select. It needs only \(|D|\) scalar mean statements, not a
vector-valued confidence set. The set of parameters with
\(G_*\leq\delta_{\rm econ}\) is a finite union of polyhedra, an
intersection over full-class faces of unions over ETF-only faces of
halfspaces.

(iv) *Curvature deficit when \(\gamma>0\).* With positive definite
\(\Sigma\), let \(v_E(\theta)\) be the unique ETF-only optimizer.
For every finite \(S\subset E\) and every \(\theta\),

$$
\max_{v\in E}Q(v;\theta)-\max_{v\in S}Q(v;\theta)
 \geq\frac\gamma2\min_{v\in S}\|v-v_E(\theta)\|_\Sigma^2,\tag{74}
$$

and the finite contrast \(\min_{v\in S}m_v(w;\theta)\) exceeds
\(\operatorname{Adv}(w;\theta)\) by exactly the left side. In
Proposition 17's family, every \(m\)-point comparator set has a
parameter with deficit at least \(s^2/(2(m+1)^2)\). There, a funded
active action has advantage \(-s^2/(4(m+1)^2)<0\), yet every one of
the \(m\) pairwise comparisons shows it at least
\(s^2/(4(m+1)^2)\) ahead. Keeping the deficit below \(\delta/4\) with
\(\delta\leq s^2/128\) needs at least \(s\sqrt{2/\delta}\geq16\)
comparators.

(v) *When a finite face set is exact under curvature.* With
\(\gamma>0\), positive definite \(\Sigma\) and a nonempty convex
parameter set \(T\), a nonempty finite \(S\subset E\) satisfies
\(\max_{v\in E}Q(v;\theta)=\max_{v\in S}Q(v;\theta)\) for all
\(\theta\in T\) if and only if some \(v_0\in S\) is the ETF-only
optimizer at every \(\theta\in T\). This happens in an assumed instance with
\(\gamma=2\), one ETF loading on the first factor, incumbent
\((3/10,1/2,1/5)\) in active, ETF and cash, position limits of one,
equal purchase and sale rates of 20 basis points on the active fund
and 5 on the ETF, shocks scaled by \(1/10\), and
\(\Theta=[1/100,3/100]\times[0,1/50]\times[-1/20,1/10]\). There the
cash-exhausting purchase \((3/10,\,2801/4002)\) is the ETF-only
optimizer throughout \(\Theta\), because the score's derivative in the
ETF holding there is at least \(2600957/276000000>0\).

For (i), on a cell every trade has a fixed sign in each coordinate, so
the trading cost and the cash constraint become linear, and the cell
is a bounded polyhedron. A bounded polyhedron has finitely many
extreme points, each fixed by linearly independent active
constraints, and a linear objective attains its maximum at one of them
(`bertsimas1997introduction`, Theorem 2.3, Corollary 2.1 and
Theorems 2.7--2.8; `schrijver1986theory`, Section 8; both cited by
theorem number, their texts not compared). The formal proof takes
the finiteness part as a stated hypothesis. With \(\gamma=0\) the score
is affine on each cell, which gives (ii); the infimum of a finite
minimum is the minimum of the infima; and the ellipsoid bound is
Cauchy–Schwarz in the \(\Omega\) inner product. Part (iii) follows
from (ii) on the stated event. Part (iv) is the quadratic gap of
Proposition 18 at the unique optimizer, with a pigeonhole argument
along Proposition 17's optimizer path. Part (v) combines that gap with
continuity of the optimizer on a convex set.

With a linear score the funded whole-class comparator is exactly its
finite faces, for every candidate, parameter set and law; the funded
geometry only decides which faces exist. With a curved score the
class is a finite face set exactly when the ETF-only optimizer does
not move on the domain. Once it moves, every finite comparator set
overstates the advantage by a curvature term, and Proposition 18's
whole-class certificate replaces face enumeration. That gain comes
from strong concavity, a known perturbation mechanism, not from
funding, costs or binding constraints. The result is deterministic:
it constructs no rule for unknown laws, shows no coverage event and
proves no rate. The vertex counts are crude upper bounds. Part (iv)
gives a necessary condition on comparator sets, not a construction.
Part (v) says nothing about how often a realistic domain has a
constant ETF-only optimizer. The single-comparator instance above is
one assumed design.

Proposition 21 bounded the premium of future ETF adjustment from
above. The last result supplies the matching floor, using the node
objects defined before Proposition 21: the node gains \(G_y\), the
weights \(w_y\), the aggregate \(\mathcal A_{u_0}\) of (60), the tilted
node measure \(Q_y\), the risk-adjusted excess returns
\(r^\pm_{j,y}\), and the node cap \(G^{\rm ub}_y\) with its aggregate
\(\beta_{\rm node}\).

**Proposition 25 (The premium of future ETF adjustment decomposes across observations and is floored by adjustable wealth; funded two-review model; machine checked).**
Fix any instance of the funded two-review model and a feasible root
trade \(u_0\).

(i) *Decomposition.* The premium is the aggregate of the node gains,

$$
\varphi(u_0)=\mathcal A_{u_0}(G),\qquad
\min_yG_y\leq\varphi(u_0)\leq\max_yG_y,\tag{75}
$$

and it is strictly increasing in each node gain. Node-wise bounds on
the gains therefore aggregate to bounds on the premium by (60).

(ii) *Floors by adjustable wealth.* At a node \(y\), with cash \(h\)
and marked ETF values \(m_j\) in units of initial wealth:
- if ETF \(j\)'s second-quarter gross return is at least
  \(1+\delta\) on every node path, with \(\delta>\kappa^+_j\), then
  \(G_y\geq h[(1+\delta)/(1+\kappa^+_j)-1]\); if it is at most
  \(1-\delta\) on every node path, with \(\delta>\kappa^-_j\), then
  \(G_y\geq m_j(\delta-\kappa^-_j)\);
- if \(r=r^+_{j,y}>0\) and \(s\) is half the range of ETF \(j\)'s
  node-path returns, then

$$
G_y\geq
\begin{cases}
r^2/(2\rho s^2), & r\leq\rho s^2h,\\
rh-\rho s^2h^2/2\ \geq\ rh/2, & \text{otherwise},
\end{cases}\tag{76}
$$

  read as \(rh\) when \(s=0\); the same holds for a sale with
  \(r=r^-_{j,y}\) and \(m_j\) in place of \(h\).

Let \(G^{\rm lb}_y\) be the largest applicable bound, zero if none
applies, and \(\alpha(u_0)=\mathcal A_{u_0}(G^{\rm lb})\). Then
\(\alpha(u_0)\leq\varphi(u_0)\leq\beta_{\rm node}(u_0)\leq\beta(u_0)\),
with \(\beta\) the cap (58).

(iii) *Sign conditions.* With Proposition 20's maximizers,

$$
\beta_{\rm node}(A_E)<\alpha(B_N)\ \Rightarrow\ \Delta_E-\Delta_N<0,
\qquad
\alpha(A_N)>\beta_{\rm node}(B_E)\ \Rightarrow\ \Delta_E-\Delta_N>0.\tag{77}
$$

Robust forms hold for any \(u\in F_0\) and \(v\in E_0\), paying each
one's suboptimality under no future trade:
\(\Delta_E-\Delta_N\geq\alpha(u)-[CE_{F,N}-c_N(u)]-\beta_{\rm node}(B_E)\)
and
\(\Delta_E-\Delta_N\leq\beta_{\rm node}(A_E)-\alpha(v)+[CE_{E,N}-c_N(v)]\).

(iv) *Two certifications at zero rates.* In Proposition 20's
sure-active family, the full root under future ETF-only trading is
uniquely the all-active trade, so \(\beta_{\rm node}(A_E)=0\), and the
ETF-only root's no-trade optimum is uniquely cash, so

$$
\alpha(B_N)=\frac{\ln(3/2)-\ln(1+e^{-10}/2)}{20}>\frac1{50},
\qquad \Delta_E-\Delta_N<-\frac1{50}.\tag{78}
$$

In Proposition 12's family, the robust lower form with the root
\((7/15,8/15)\) and the cash root gives \(\Delta_E-\Delta_N>3/100\).

For (i), group the two-review expected utility by the first public
observation: the tower property gives the premium as a certainty
equivalent of node certainty equivalents, which is (75). For the sure-sign floors, buying
with all cash, or selling all of ETF \(j\), gains at least the stated
amount on every path. For (76), the node certainty equivalent along a
purchase of size \(\epsilon\) is at least
\(r\epsilon-\rho s^2\epsilon^2/2\) by Hoeffding's lemma on the moment
generating function of a variable with range at most \(2s\), applied
under the tilted measure (`hoeffding1963probability`, inequalities
(4.15)-(4.16) in the proof of Theorem 2, full text reviewed);
maximizing over \(\epsilon\in[0,h]\) gives the two branches. The
caps are Proposition 20's argument node by node. Part (iii) is (77)
substituted into (57). Part (iv) computes the two families' node
gains in closed form.

Proposition 20's cap says funding limits what future ETF adjustment
is worth. This result says the converse. At each observation the
option to adjust is worth at least a risk-adjusted excess return
times the wealth that can be redeployed, less a risk term, and at
least half of it when that wealth binds. The sign of the future-ETF
channel is then bounded by comparing these quantities at the two
root optima. In the stylized families the bounds are tight: (78)
matches the channel's numerical value, \(-0.020272\), to six
decimals, and Proposition 12's lower form gives 0.032 against 0.0337.

The caps are the weak side. On assumed instances with nondegenerate
risk and partial learning, the floors \(\alpha\) are within about a
quarter of the premia (0.71 to 0.81 of them), but the caps
\(\beta_{\rm node}\) are 29 to 374 times the premia, and unbounded where
the premium is zero. So these conditions certify no sign on those
instances; Proposition 21 shows why no range-based cap can do much
better. These ratios are numerical, from solver optimizers, and are
not part of the proposition. The floors use one ETF and one trade
direction at a time; joint trades across ETFs are not counted. The
certifications are at zero rates, where the optimizers are
identified exactly. Nothing is said about the future-active channel,
or about movement of the no-active-trade region. The argument
applies the tower property, Hoeffding's lemma and Proposition 20's
cap and sandwich; it is not a new mechanism.

The one-quarter band of Proposition 9 describes one review. With many
reviews the target moves between them, and a trade made now may be
reversed later. The last result gives the exact structure of the
band at quarterly reviews around a moving target, before any
small-cost approximation.

**Proposition 26 (Quarterly no-trade bands around a moving target: trade to the edge, a static width ceiling, and exactness for coarse innovations; multi-review tracking model with a slack budget; machine checked).**
Fix a slack-budget instance of the multi-review tracking model, a
review \(t<T\) and a state \(z\).

(i) *One instrument: trade to the edge.* Let \(n=1\) and
\(c=\gamma\Sigma>0\). There are edges
\(0\leq lo_t(z)\leq hi_t(z)\leq\bar x\), defined by the one-sided
derivatives of \(G_t\) reaching \(-\kappa^+\) and \(\kappa^-\), such that
for every pre-trade holding \(x\geq0\), including one above the cap
after marking, the optimal post-trade holding is unique and

$$
x^+_t(x,z)=\min\bigl(\max(x,lo_t(z)),hi_t(z)\bigr).\tag{79}
$$

The investor does not trade inside \([lo_t,hi_t]\) and otherwise trades
to the nearer edge. \(V_t\) is convex with slopes in \([-\kappa^+,\kappa^-]\).

(ii) *A static width ceiling.* For every \(t<T\),

$$
hi_t(z)-lo_t(z)\leq\frac{\kappa^++\kappa^-}{c}.\tag{80}
$$

At the last review the band is exactly
\([\,x^*_{T-1}-\kappa^+/c,\ x^*_{T-1}+\kappa^-/c\,]\), clipped to
\([0,\bar x]\); its width is the static width whenever neither bound
binds. So a moving target can only narrow the band at quarterly
reviews, never widen it. With the expected gross return
\(\bar g_t=\sum q_t(z',g'\mid z)g'\), the edges also satisfy
\(lo_t\geq\min(\bar x,x^*_t-(\kappa^++\beta\kappa^-\bar g_t)/c)\) and
\(hi_t\leq\max(0,x^*_t+(\kappa^-+\beta\kappa^+\bar g_t)/c)\).

(iii) *Coarse innovations: the static band, tilted.* Let
\(t\leq T-2\), with both edges interior. Suppose every positive-mass
outcome \((z',g')\) marks the whole current band strictly into the next
review's buy region, \(hi_t g'<lo_{t+1}(z')\), or strictly into its
sell region, \(lo_t g'>hi_{t+1}(z')\). Let \(U\) and \(D\) be the
return-weighted masses of the two kinds of outcome. Then, with the
tilt \(\tau_t=\beta(\kappa^+U-\kappa^-D)/c\),

$$
lo_t=x^*_t-\frac{\kappa^+}c+\tau_t,\qquad
hi_t=x^*_t+\frac{\kappa^-}c+\tau_t,\qquad
hi_t-lo_t=\frac{\kappa^++\kappa^-}c.\tag{81}
$$

Without marking (\(g'=1\)), a sufficient condition is that every
target innovation exceeds \((1+\beta)(\kappa^++\kappa^-)/c\) in size. With
symmetric rates and \(U=D\), the tilt vanishes and the band is the
last review's band.

(iv) *When the ceiling is attained.* For \(t\leq T-2\) and
\(\kappa^++\kappa^->0\), the width equals the static width if and only if
neither bound clips the band and every outcome marks the band
entirely into \([0,lo_{t+1}(z')]\) or \([hi_{t+1}(z'),\infty)\). Otherwise
the band is strictly narrower.

(v) *Many instruments.* For general \(n\), the optimal post-trade
holding is unique and the no-trade set is nonempty. Any two no-trade
holdings satisfy

$$
\gamma(x-y)^\top\Sigma(x-y)\leq\sum_i(\kappa^+_i+\kappa^-_i)\,|x_i-y_i|,\tag{82}
$$

so two no-trade holdings differing only in instrument \(i\) differ by
at most its static width \((\kappa^+_i+\kappa^-_i)/(\gamma\Sigma_{ii})\). At the
last review, where no bound binds, the no-trade set is the
parallelotope \(x^*+(\gamma\Sigma)^{-1}\prod_i[-\kappa^+_i,\kappa^-_i]\). For an
active fund \(A\) beside the other instruments \(E\), its interior
condition reads
\(d_A\in-(\Sigma_{AE}d_E)/\Sigma_{AA}+[-\kappa^+_A,\kappa^-_A]/(\gamma\Sigma_{AA})\),
with \(d=x-x^*\): the fund's band has its own static width but is
centred at the target minus the exposure the other instruments'
deviations already supply, at the rate \(\Sigma_{AE}/\Sigma_{AA}\).

The proof is backward induction on \(t\). The continuation
\(V_{t+1}\) is convex with slopes in \([-\kappa^+,\kappa^-]\), so \(G_t\) is
strictly convex, and minimizing it plus a proportional cost over an
interval is a projection onto the set where its one-sided
derivatives lie within the cost rates. That gives (79). The ceiling
(80) holds because the continuation adds a convex term to the
tracking loss, which can only steepen it. In (iii) every outcome puts
the marked band on one side of the next band, where the continuation
is affine with slope \(-\kappa^+\) or \(\kappa^-\), so it shifts the
derivative by a constant, the tilt. Part (iv) is the converse: strict
convexity of the continuation anywhere across the marked band
strictly narrows it. For (v), comparing the objective along the
segment between two no-trade holdings gives (82), and coordinate
perturbations give the static shape.

At quarterly reviews, then, the band around a moving target lies
between two exact anchors. One is the static width, attained exactly
when the target's quarterly innovations are coarse relative to that
width; there the target's motion only tilts the band. The other is
strict narrowing, when innovations are fine. Instruments with small
trading rates, such as ETFs, have narrow static bands and are more
likely to be in the coarse regime; funds carrying loads or
redemption fees have wide bands and are more likely to be in the
fine regime. That assignment is an expectation, not a result.

The trade-to-the-edge band is the classical structure of
discrete-time trading with proportional costs, due to Constantinides
(`constantinides1979multiperiod`, cited by title; the text has not
been obtained). The proposition re-derives it only to carry the
moving target, the caps and marking, which its other parts use. In
continuous time, small-cost bands around a moving target have width
of order the cube root of the cost and scale with the target's
volatility (`soner2013homogenization`, equation (4.4), read at the
level of its displayed formulas; `muhlekarbe2017primer`, Section 4;
`martin2012optimal`, cited by title). Those are limits of continuous
trading, in which a one-review width has no meaning, and they describe
the fine regime this result does not cover. A binding cap reshapes a
band at leading order in continuous time (`liu2013portfolio`, full
text reviewed); here a cap only clips the band.

The result assumes a slack budget, so the cash coupling of Proposition
9 is absent, and it treats the target process as given. It uses
nothing about how beliefs are formed, so it does not specialize to a
learned, shrinking-variance target. The fine regime's leading order is
not established, and a cap's effect on an interior edge is not
quantified. For many instruments only the diameter inequality and the
static shape are proved; the dynamic no-trade set need not be a
parallelotope, and the dynamic version of the bundling shift is open.
No calibration or magnitude is claimed.

The earlier dynamic results used proportional costs and a given
target, and most had one active fund. With quadratic costs, many
funds and learning from public returns, the optimal policy has an
explicit form. The last result gives it, and
shows what bundling factor exposure inside funds adds to it.

**Proposition 27 (Partial adjustment toward a learning-driven aim, and exact separation of ETF exposure from fund alpha up to three bundling terms; fund-of-funds learning model, unconstrained counterfactual; machine checked, with the conditional-moment and dynamic-programming steps at paper level).**
Fix an instance of the fund-of-funds learning model with fixed
unknown premia and alphas.

(i) *Exogenous learning.* For every policy, the posterior covariances
\(P_t\) form the same deterministic sequence, and the posterior mean
\(m_t\) is a martingale, \(\mathbb E_tm_{t+1}=m_t\). \(\Sigma_t\) is
deterministic and positive definite, and it does not increase. In the
reference case the filter decouples: factor returns update the premia
and fund residual returns \(r^A-B^Af\) update the alphas, and

$$
\Sigma_t=B(\Sigma_f+P^\lambda_t)B^\top
 +\operatorname{diag}(\Sigma_A+P^\alpha_t,\ \Sigma_E).\tag{83}
$$

So the problem is a linear-quadratic tracking problem with the
martingale \(m_t\) as an exogenous state, and there is no motive to
trade in order to learn.

(ii) *The policy.* Define backward from \(A_T=0\):
\(D_t=\Lambda+\gamma\Sigma_t+\rho A_{t+1}\) and
\(A_t=\Lambda-\Lambda D_t^{-1}\Lambda\), so \(0\leq A_t\leq\Lambda\). The optimal
policy exists, is unique, and is partial adjustment toward an aim,

$$
x_t=x_{t-1}+\Gamma_t(\mathrm{aim}_t-x_{t-1}),\qquad
\Gamma_t=D_t^{-1}(\gamma\Sigma_t+\rho A_{t+1}),\tag{84}
$$

$$
\mathrm{aim}_t=(\gamma\Sigma_t+\rho A_{t+1})^{-1}
 \bigl[\gamma\Sigma_t\,\mathrm{Mk}_t+\rho A_{t+1}\,\mathbb E_t\mathrm{aim}_{t+1}\bigr],
\qquad \mathrm{aim}_{T-1}=\mathrm{Mk}_{T-1}.\tag{85}
$$

\(\Gamma_t\) has eigenvalues in \((0,1)\), so every trade is a genuine
partial adjustment. Unrolled, the aim is a matrix-weighted average of
\((\gamma\Sigma_s)^{-1}\mu_t\) over the remaining reviews \(s\geq t\), with
weights summing to the identity. It is the current Markowitz
portfolio re-weighted toward the smaller predictive covariances that
learning will bring.

(iii) *Exposure-and-fund coordinates.* Suppose \(M=K\) and \(B^E\) is
invertible, so ETFs span the factors exactly, and write
\(R=(B^E)^{-1}\). Use the total factor exposure \(y=B^\top x\) and the fund
positions \(x^A\) as coordinates; then \(x^E=R^\top(y-B^{A\top}x^A)\). If
ETFs cost nothing to trade, carry no residual risk and charge no fee
(\(\lambda_E=0\), \(\Sigma_E=0\), \(c^E=0\)), the problem separates exactly:

$$
y_t=\bigl(\gamma(\Sigma_f+P^\lambda_t)\bigr)^{-1}\hat\lambda_t,\qquad
x^A_t=x^A_{t-1}+\Gamma^A_t(\mathrm{aim}^A_t-x^A_{t-1}),\qquad
x^E_t=R^\top(y_t-B^{A\top}x^A_t),\tag{86}
$$

where the fund rule is (84)-(85) with cost \(\lambda_AI_N\), risk
\(\gamma(\Sigma_A+P^\alpha_t)\) and the alpha means \(\hat\alpha_t\). Exposure
follows premium beliefs myopically, funds follow alpha beliefs with
partial adjustment, and ETFs net the exposure the funds carry as a
by-product, with either sign.

(iv) *The three bundling terms.* In the reference case, the only
couplings between the two problems are: an ETF trading cost, which
adds a cost cross term, because a fund trade must be netted by a
costly ETF trade and exposure is then no longer myopic; ETF residual
risk, which adds a risk cross term; and ETF fees \(\phi=Rc^E\), which
shift the exposure mean by \(-\phi\) and the fund mean by \(+B^A\phi\), since
a fund's by-product exposure saves the fee ETF exposure would pay. With
all three set to zero the policy is (86); in general it is (84)-(85)
in the new coordinates.

(v) *Trading speeds.* In (86) with homogeneous funds
(\(\Sigma_A=\sigma_A^2I\), prior alpha variance \(s^2I\), no pooled
component), the fund rate is scalar, \(\Gamma^A_t=g_tI\) with \(g_t\in(0,1)\),
decreasing in \(\lambda_A\) and increasing in \(\gamma\), and the ETF
exposure adjusts in full. As the horizon and then \(t\) grow, \(g_t\)
converges to \(a_\infty/\lambda_A\), where \(a_\infty\) is the unique root in
\([0,\lambda_A]\) of

$$
a=\lambda_A-\frac{\lambda_A^2}{\lambda_A+\gamma\sigma_A^2+\rho a}.\tag{87}
$$

For (i), the Kalman covariance recursion involves only the prior, the
observation matrix and the noise covariance, none of which depends
on positions. Transforming the observation to
\((f,r^A-B^Af,r^E-B^Ef+c^E)\) makes its matrix and noise block diagonal
in the reference case, which decouples the filter. For (ii), backward
induction verifies a value function quadratic in the position, with
the stated recursion, and the maximizer of each Bellman objective is
affine in the state. Part (iii) is the same problem in new
coordinates: the transformed risk, cost and mean have zero cross
blocks exactly when the three ETF frictions vanish. Part (v) reduces
the fund block to a scalar recursion.

The machine check covers each numbered part. Two steps are kept at the
level of a paper proof. One is the Gaussian conditional-moment facts
that give the predictive moments and the martingale property, which
discharge a hypothesis of the formal Bellman verification. The other
is the dynamic-programming step from Bellman optimality to optimality
among all admissible policies.

Partial adjustment toward an aim under quadratic costs is Gârleanu
and Pedersen's rule (`garleanu2009dynamic`, Propositions 1-3, full
text reviewed), and filter/control separation with a Riccati control
law is standard linear-quadratic-Gaussian control (`abeille2016lqg`,
Assumption 1 and Theorems 2.1-2.2, full text reviewed). Those results
are stationary. The time-varying recursion that learning produces is
proved directly, so neither is used as a lemma. In (v), \(a_\infty/\lambda_A\)
coincides with Gârleanu and Pedersen's trading rate after matching
their discounting convention; that identification is checked. What
the fund-of-funds structure adds is (iii)-(iv): a dynamic, costly
version of Treynor and Black's netting (`treynor1973security`,
equation (16), full text reviewed), in which ETFs carry exposure
and funds carry alpha, with three explicit terms that couple them.

The result is for an unconstrained position space. Its policy may
short funds and use leverage, and it is not implementable by a
long-only fund of funds without the proportional-cost and cap
corrections that Proposition 26 begins. Part (iii) needs exactly as
many ETFs as factors, with full rank. The case where ETFs miss a factor
direction, redundant ETFs, a pooled alpha prior with two speeds, and
unequal persistence of premia and alphas are not treated. The infinite
horizon is reached only through the limit in (v). No magnitude is
claimed.

Proposition 27's exact split needs the ETFs to span every factor.
When some factor direction is reachable only through the funds,
premium beliefs reach fund choice. The last result says exactly how.

**Proposition 28 (Premium beliefs leak into fund choice through the factor directions ETFs cannot reach; fund-of-funds learning model, unconstrained counterfactual; machine checked, with the conditional-moment and dynamic-programming steps at paper level).**
Fix an instance of the fund-of-funds learning model in the reference
case with fixed unknown means. Switch ETF frictions off
(\(\lambda_E=0\), \(\Sigma_E=0\), \(c^E=0\)), so only funds cost \(\Lambda_A\) to
trade, and let \(B^E\) have full row rank \(M\leq K\). Its row space
\(L_E\) is the *reachable* subspace of factor directions, and its
orthogonal complement \(L_E^\perp\) the *unreachable* one, with
orthogonal projections \(\Pi_R\) and \(\Pi_U\). Let
\(\tilde\Sigma_t=\Sigma_f+P^\lambda_t\) be the predictive factor covariance,
return risk plus premium-estimation risk, with blocks
\(\tilde\Sigma_{RR},\tilde\Sigma_{RU},\tilde\Sigma_{UU}\) on the two subspaces, and let
\(\tilde\Sigma_{U\cdot R}=\tilde\Sigma_{UU}-\tilde\Sigma_{UR}\tilde\Sigma_{RR}^{-1}\tilde\Sigma_{RU}\)
be the Schur complement: the unreachable directions' variance net of
their best reachable hedge. The *hedge map*
\(J_t=\Pi_U-\Pi_R\tilde\Sigma_{RR}^{-1}\tilde\Sigma_{RU}\) takes a factor vector
to its unreachable part minus the reachable position that hedges it
at minimum variance. Define the *reduced fund moments*

$$
\alpha^{\rm red}_t=\hat\alpha_t+B^AJ_t^\top\hat\lambda_t,\qquad
\Sigma^{\rm red}_t=\Sigma_A+P^\alpha_t+B^A\tilde\Sigma_{U\cdot R}B^{A\top}.\tag{88}
$$

(i) *The ETF exposure is myopic plus a hedge.* The total exposure is
the reachable exposure \(y_R\) plus the funds' unreachable exposure
\(\Pi_UB^{A\top}x^A\), which the funds alone carry. At every review the
optimal reachable exposure is

$$
y_{R,t}=\tilde\Sigma_{RR}^{-1}\Bigl[\tfrac1\gamma\Pi_R\hat\lambda_t
 -\tilde\Sigma_{RU}B^{A\top}x^A_t\Bigr],\tag{89}
$$

the Markowitz exposure on the reachable directions minus the
minimum-variance hedge, through ETFs, of the funds' unreachable
exposure. The ETFs then net the funds' reachable by-product. When
\(\tilde\Sigma_{RU}=0\) the hedge vanishes.

(ii) *The fund problem.* The fund positions follow Proposition 27's
partial adjustment, with the time-varying mean map that gives the
mean \(\alpha^{\rm red}_t\), the risk \(\gamma\Sigma^{\rm red}_t\) and the cost
\(\Lambda_A\). Their one-quarter Markowitz portfolio is
\((\gamma\Sigma^{\rm red}_t)^{-1}(\hat\alpha_t+B^AJ_t^\top\hat\lambda_t)\).

(iii) *The leak.* Along an unreachable direction \(v\in L_E^\perp\), the
fund policy's sensitivity to premium beliefs at review \(t\) is

$$
D_t^{-1}M_tB^Av,\qquad M_t=I+\rho\Lambda_AD_{t+1}^{-1}M_{t+1},\quad M_{T-1}=I,\tag{90}
$$

with \(D_t\) the fund problem's matrix from Proposition 27. If every
fund loading lies in \(L_E\), the funds' factor exposure is replicable,
\(B^AJ_t^\top=0\), the risk term in (88) vanishes and there is no leak:
Proposition 27's separation. If some fund loading has an unreachable
component (\(B^Av\neq0\) for some \(v\in L_E^\perp\)), the sensitivity is
nonzero whenever \(M_t\) is nonsingular. That holds at the last review,
at every review when \(T\leq3\), in the stationary limit, and whenever a
symmetric-part condition holds along the recursion. In that case the
risk term \(B^A\tilde\Sigma_{U\cdot R}B^{A\top}\) is also nonzero, and it changes
the policy's own-position coefficient at every review.

(iv) *Learning and the leak.* Along the learning path, \(P^\lambda_t\)
shrinks, so \(\tilde\Sigma_{U\cdot R}\) decreases to its return-only value and
the risk leak shrinks. The mean leak \(B^AJ_t^\top\hat\lambda_t\) persists. An
unreachable premium is a permanent reason for fund positions, and its
estimation error a transient one.

Maximizing the joint problem over the costless reachable exposure
first gives (89). Substituting it back leaves a fund problem whose
mean and risk gain the unreachable premium and variance net of the
reachable hedge, the Schur complement in (88). The joint Riccati
matrix's Schur complement over the ETF block is the reduced one, so
the fund positions follow the reduced problem's policy. The leak
(90) follows by differentiating the backward recursion along \(v\),
where \(J_t^\top v=v\). The risk term raises the Riccati matrix in the
positive semidefinite order, so it changes the own-position
coefficient.

When ETFs cannot reach a factor, then, premium beliefs and their
estimation error reach fund choice exactly through the unhedgeable
part of the funds' loadings: as a mean term that persists and a risk
term that learning removes. This is the dynamic, quantified form of
the one-quarter geometry of Proposition 5, which separates a missing
direction from a match blocked by funding. Treynor and Black's
explicit market position nets a fund's by-product exactly because
the market asset spans their single factor (`treynor1973security`,
equation (16), full text reviewed). The unreachable direction is the
case it does not cover. The Schur-complement step is elementary
partial maximization of a quadratic.

The status is as for Proposition 27: the same two steps, the
Gaussian conditional moments and the passage to all admissible
policies, are reviewed paper proofs. That \(M_t\) is nonsingular at
every review for every horizon was observed in 100,000 random cases
and is not proved. So the leak's nonvanishing beyond the cases listed
in (iii) is a numerical observation. ETF frictions together with a
missing direction, redundant ETFs, long-only and funding constraints,
and the leak's magnitude at calibrated scale are not treated. The
policy is the unconstrained counterfactual of Proposition 27.

Proposition 27's aim leans toward the smaller risk charges that
learning will bring. The last result makes that anticipation explicit
in the separated case, and shows how a prior shared across funds
changes the trading speeds.

**Proposition 29 (Learning is anticipated only where trading costs, and a pooled alpha prior gives two trading speeds; fund-of-funds learning model, unconstrained counterfactual; machine checked, with the conditional-moment and dynamic-programming steps at paper level).**
Take the separated case of Proposition 27 (iii), with homogeneous
funds, \(\Sigma_A=\sigma_A^2I_N\) and \(\Lambda_A=\lambda_AI_N\) with \(\lambda_A>0\), and a
*pooled* alpha prior with covariance \(\bar s^2\mathbf 1\mathbf 1^\top+s^2I_N\),
\(s>0\), \(\bar s\geq0\): the funds' alphas share a common component. Let
\(\Pi_c=\mathbf 1\mathbf 1^\top/N\) project onto the *common direction*, the
average fund position, and \(\Pi_r=I-\Pi_c\) onto the *relative
directions*.

(i) *Two posterior variances, one learning rate.* For every \(t\),

$$
P^\alpha_t=p^c_t\Pi_c+p^r_t\Pi_r,\qquad
\frac1{p^c_t}=\frac1{s^2+N\bar s^2}+\frac t{\sigma_A^2},\qquad
\frac1{p^r_t}=\frac1{s^2}+\frac t{\sigma_A^2}.\tag{91}
$$

The common direction starts more uncertain, \(p^c_t\geq p^r_t\) with
equality exactly when \(\bar s=0\), and both precisions grow by
\(1/\sigma_A^2\) a quarter. The gap \(p^c_t-p^r_t\) falls like \(1/t^2\).

(ii) *Two speeds.* The fund trading rate is
\(\Gamma^A_t=g^c_t\Pi_c+g^r_t\Pi_r\). Each scalar rate comes from the scalar
recursion of Proposition 27 with risk \(\gamma(\sigma_A^2+p^{\rm dir}_t)\), and
\(g^c_t\geq g^r_t\), with equality exactly when \(\bar s=0\). The average fund
position moves toward its aim faster than relative positions, and
both rates have the same stationary limit.

(iii) *The learning factor.* In each direction the fund aim is the
shrunk Markowitz position scaled up,

$$
\mathrm{aim}^{A,\rm dir}_t=\ell^{\rm dir}_t\,
\frac{\sigma_A^2+p^{\rm dir}_t}{\sigma_A^2}\,
\frac{\hat\alpha^{\rm dir}_t}{\gamma(\sigma_A^2+p^{\rm dir}_t)},\qquad
\frac{\sigma_A^2}{\sigma_A^2+p^{\rm dir}_t}\leq\ell^{\rm dir}_t\leq1,\tag{92}
$$

where \(\ell^{\rm dir}_t\) is a weighted average of
\(\sigma_A^2/(\sigma_A^2+p^{\rm dir}_s)\) over the remaining reviews, with positive
weights from the Riccati recursion that sum to one. The factor
\(\ell^{\rm dir}_t(\sigma_A^2+p^{\rm dir}_t)/\sigma_A^2\), the *learning factor*, is at
least one, and equals one only at the last review. The aim therefore
lies above today's shrunk position, which reflects today's
estimation variance, and never above the position with alpha known,
\(\hat\alpha^{\rm dir}_t/(\gamma\sigma_A^2)\).

(iv) *Only where trading costs.* In the same case the ETF exposure is
\(y_t=(\gamma(\Sigma_f+P^\lambda_t))^{-1}\hat\lambda_t\), shrunk by today's
premium uncertainty with no forward-looking factor, because it is
costless to adjust and is re-set every review.

For (i), the pooled prior covariance and the posterior covariance
share the eigenvectors \(\Pi_c\) and \(\Pi_r\), and in each eigenspace the
precision grows by one observation's precision each quarter. For
(ii), the recursion of Proposition 27 splits along the same
eigenspaces, and its scalar rate is nondecreasing in the whole future
path of the risk charge, which is larger in the common direction.
For (iii), unrolling the aim recursion gives the weighted average,
and each term lies between today's shrinkage factor and one because
the posterior variance only falls. Part (iv) is Proposition 27 (iii).

Where a position is costly to change, then, its target anticipates
the precision it will have while held; where it is costless, only
today's precision matters. The aim formula is Gârleanu and Pedersen's
average of current and expected future Markowitz portfolios
(`garleanu2009dynamic`, Proposition 3, full text reviewed), with a
martingale signal and a time-varying risk charge: what changes over
time here is estimation variance, not the signal's decay. Their
result that trading is faster with more risk aversion (Proposition 2(ii))
is the monotonicity that (ii) extends to a whole path of risk charges.
Estimation risk about a constant premium produces a hedging demand in
Brennan's continuous-time setting (`brennan1998role`, cited for the
mechanism; not compared at theorem level). With a per-quarter
mean-variance objective, the forward-looking effect appears here only
through trading costs. The pooled prior is Pástor and Stambaugh's
learning across funds (`pastor2002investing`, full text reviewed),
made dynamic.

The status is Proposition 27's: the conditional-moment and
dynamic-programming steps are reviewed paper proofs. The result needs
homogeneous funds, and it does not treat ETF trading costs, under
which the exposure would acquire its own learning factor. Two
regularities observed numerically are not proved: that the learning
factor is smaller in the common direction, and that it falls with
fund costs. At the instances checked the learning factor is at most
3%. Magnitudes are not established.

Propositions 27-29 assume the return covariance is known. A manager
estimates it. The last result measures what running the policy of
Proposition 27 with an estimated covariance costs.

**Proposition 30 (Value loss from an estimated covariance: an exact identity, a non-local Riccati bound, and a guarantee for an estimate made before the run; fund-of-funds learning model, unconstrained counterfactual; machine checked in its finite-dimensional core, with the summation to the loss identity, the second-moment step and the state-moment recursion at paper level).**
Fix an instance of the fund-of-funds learning model with fixed
unknown means, and let the filter use the true inputs. The manager
runs the policy of Proposition 27 computed from an estimated
covariance path \(\tilde\Sigma_t\), which gives coefficients
\((\tilde K_t,\tilde L_t,\tilde l_t)\) and the plug-in policy
\(x_t=\tilde K_tx_{t-1}+\tilde L_tm_t+\tilde l_t\). Write \((K_t,L_t,l_t)\) for
the true coefficients, \(\delta K_t=\tilde K_t-K_t\) and so on, and \(D_t\) for
the true curvature matrix of Proposition 27. Use the cost-weighted
norms \(\|X\|_\Lambda=\|\Lambda^{1/2}X\Lambda^{-1/2}\|\) for a matrix and
\(\|Y\|_*=\|\Lambda^{-1/2}Y\Lambda^{-1/2}\|\) for a symmetric one, with
\(\|\cdot\|\) the spectral norm.

(i) *Loss identity.* For every admissible policy \(\pi\) with finite
second moments,

$$
V^*_0-V^\pi_0=\mathbb E_0\sum_{t=0}^{T-1}\rho^t\,\tfrac12\,e_t^\top D_te_t,
\qquad e_t=x^\pi_t-(K_tx^\pi_{t-1}+L_tm_t+l_t).\tag{93}
$$

The loss is the discounted, curvature-weighted sum of the squared
deviations of the policy's trades from the optimal trade at the
policy's own state.

(ii) *The plug-in loss.* For the plug-in policy,
\(e_t=\delta K_tx_{t-1}+\delta L_tm_t+\delta l_t\), so the loss is an explicit
quadratic in the coefficient errors and the state's first two moments.
Those moments follow an exact linear recursion, so the loss is
computable without simulation. A norm bound follows:
\(V^*_0-V^\pi_0\leq\frac12\sum_t\rho^t\|D_t\|_*(\|\delta K_t\|_\Lambda r^x_t
+\|\Lambda^{1/2}\delta L_t\|r^m_t+\|\Lambda^{1/2}\delta l_t\|)^2\), with \(r^x_t\) and
\(r^m_t\) the root mean squares of \(\Lambda^{1/2}x_{t-1}\) and \(m_t\).

(iii) *Non-local stability of the Riccati recursion.* If each
\(\tilde\Sigma_s\) is positive semidefinite, then for every \(t<T\) and every
size of error,

$$
\|\delta M_t\|\leq\sum_{s=t}^{T-1}\rho^{s-t}\gamma\|\tilde\Sigma_s-\Sigma_s\|_*,
\qquad
\|\delta K_t\|_\Lambda\leq\gamma\|\tilde\Sigma_t-\Sigma_t\|_*+\rho\|\delta M_{t+1}\|,\tag{94}
$$

where \(M_t=\Lambda^{-1/2}A_t\Lambda^{-1/2}\). The errors in \(L_t\) and \(l_t\) are
bounded by similar discounted sums. An indefinite estimate can break
every bound.

(iv) *A guarantee for an estimate made before the run.* Suppose the
return covariance is estimated once, from a history separate from
the run, and the estimate is positive semidefinite, with an event of
probability at least \(1-\alpha\) over that history on which its error
is at most \(r\) in the \(\|\cdot\|_*\) norm. Then on that event the bounds of
(ii)-(iii) hold with \(r\) in place of every covariance error:

$$
\Pr\bigl(V^*_0-V^\pi_0\leq B(r)\bigr)\geq1-\alpha,\tag{95}
$$

with \(B(r)\) the explicit number that (ii)-(iii) give.

For (i), completing the square in each Bellman step of Proposition 27
writes the objective at any trade as the value minus
\(\frac12e^\top D_te\), and summing under the policy's conditional
expectations gives (93). For (iii), the recursion's one-step map
\(R\mapsto I-(I+R)^{-1}\) is 1-Lipschitz on positive semidefinite
matrices, so errors propagate backward at most additively with
discounting. Part (iv) is (ii)-(iii) on the confidence event.

The machine check covers each one-step identity, the pathwise error
bounds, all four Riccati bounds, and the bounds on the confidence
event. Three steps are reviewed paper proofs, not machine checked:
summing the one-step identity into (93) under conditional
expectations, the passage from pathwise bounds to second moments, and
the recursion for the state moments.

The shape of the result is known. For stationary
linear-quadratic-Gaussian control, the value loss of the
certainty-equivalent controller is of second order in the parameter
error (`mania2019certainty`, Theorems 3-4 and Proposition 2, cited for
context as audited in the ledger). The stationary Riccati equation has non-local perturbation
bounds with a condition number (`konstantinov1993perturbation`,
Theorems 3.2-3.3, cited for context as audited in the ledger). Both are stationary and are cited
for context; the finite-horizon, time-varying statements here are
proved directly, with the cost-weighted norm in the role of the
condition number.

A numerical comparison, not part of the proposition, shows which
part is usable at realistic scale. On a calibrated instance with 30
funds, 8 ETFs, five factors and 40 reviews, with the covariance
estimated from 160 quarters, the exact loss (ii) is 5.9 to 16.7 bp
per quarter on five estimation draws, or 1.0 to 2.8% of the optimal
value. The norm bound is 330 to 1,150 times larger. The Riccati bound
(iii) exceeds 57 where the true quantity is at most 1, because the
cost-weighted norm divides by the small ETF trading cost and the sum
runs over 40 reviews. So the identity is the usable object, and a
guarantee at calibrated scale has to be computed from it over the
confidence set, not read off the norm bounds. These figures belong to
the unconstrained, levered policy. With funded long-only caps, a
learning-aware policy gains only about 0.03 bp per quarter over a
myopic one, so the covariance's estimation error matters on that
order.

The estimated input is the covariance only: estimated loadings and
costs, and a misestimated filter, are not treated. The estimate is
made once. A manager who re-estimates at every review is not a fixed
plug-in policy, and a time-uniform guarantee for that case is not
given. Whether an a-priori bound can be non-vacuous at realistic
scale is open.

Proposition 26 took the target process as given. The last result
puts the band on the learning path: the target is the learning
model's Markowitz portfolio, and the risk charge falls as premia and
alphas are learned.

**Proposition 31 (Quarterly bands on the learning path: the static width rises, the target drifts outward, and pure learning ends the coarse regime; learning-driven tracking model, finite-law variant, slack budget; machine checked, with the innovation's unconditional moments at paper level).**
Fix a slack-budget instance of the learning-driven tracking model in
its finite-law variant, and write \(c_t=\gamma\Sigma_{t,ii}\) for the
curvature of the instrument considered.

(i) *Transfer.* The instance is a multi-review tracking model with a
time-varying covariance. Every part of Proposition 26 holds with
\(c\) replaced by \(c_t\) at every review and state: the band and trade to
the edge, the ceiling \((\kappa^++\kappa^-)/c_t\), the edge brackets, the coarse
regime with tilt \(\beta(\kappa^+U-\kappa^-D)/c_t\), the equality
characterization, and, for many instruments, the diameter inequality
and the static shape with \(\Sigma_{T-1}\). In the coarse-regime condition
without marking, each target innovation must exceed
\((\kappa^-+\beta\kappa^+)/c_t+(\kappa^++\beta\kappa^-)/c_{t+1}\) in size. With a
diagonal \(\Sigma_t\) the instruments separate.

(ii) *The static width rises.* \(P_t^{-1}=P_0^{-1}+tH^\top R^{-1}H\), so
\(P_t\) falls to zero, \(\Sigma_t\) falls to \(\Sigma_r\), \(c_t\) is nonincreasing,
and the static width

$$
w_t=\frac{\kappa^++\kappa^-}{c_t}\ \uparrow\ \frac{\kappa^++\kappa^-}{\gamma\Sigma_{r,ii}}.\tag{96}
$$

As estimation risk is learned away, the same deviation costs less and
the ceiling loosens quarter by quarter.

(iii) *Drift and tilt.* The learning drift
\([(\gamma\Sigma_{t+1})^{-1}-(\gamma\Sigma_t)^{-1}]\mu_t\) is known at \(t\). For one
instrument it has the sign of \(\mu_t\) when the instrument's risk charge
learns, and is zero otherwise, so it pushes the target away from
zero. Both it and the innovation covariance \(V_t\) are of order
\(1/t^2\). In the coarse regime without marking, with symmetric trading
rates \(\kappa\) and a conditional innovation law symmetric about zero,
the tilt is zero or has the drift's sign, with

$$
|\tau_t|=\frac{\beta\kappa}{c_t}\,
 \Pr\bigl(|(\gamma\Sigma_{t+1})^{-1}G\epsilon_{t+1}|\leq|\delta_t|\ \big|\ z\bigr),\tag{97}
$$

where \(\delta_t\) is the drift. A martingale target with symmetric
innovations has no tilt; the learning drift is what tilts the band.

(iv) *Pure learning ends the coarse regime.* Suppose the instrument's
gross return is one on every path, so that only learning moves the
deviation from the target (*pure-learning marking*), and
\(\kappa^++\kappa^->0\). If the band at \(t\leq T-2\) has the static width, every
outcome moves the target by at least

$$
\frac{\kappa^-(1-\beta)+\beta(\kappa^++\kappa^-)U}{c_t}\ \text{up}
\qquad\text{or}\qquad
\frac{\kappa^+(1-\beta)+\beta(\kappa^++\kappa^-)D}{c_t}\ \text{down},\tag{98}
$$

where \(U\) and \(D\) are the probabilities of landing wholly above or
below the next band, with \(U+D=1\). Since learning shrinks the target's
moves while the static width rises, there is a review \(t_0\),
determined by the model's inputs and not by the horizon, after which
the band is strictly narrower than the static width at every review
and history, for every horizon.

For (i), every argument of Proposition 26 works at a fixed review and
state, and uses the covariance only through its value there. Part
(ii) is the information form of the filter with fixed means. Part
(iii) differentiates the target along the filter and computes the
coarse-regime tilt from the up and down masses. For (iv), a band of
static width requires every outcome to land it wholly on one side of
the next band, which forces a target move at least the size in (98).
The information form bounds the target's moves uniformly over
histories by a quantity that tends to zero.

Along the learning path the two anchors of Proposition 26 move apart.
The static width rises, and the target's learning-driven moves shrink,
so a pure-learning band passes from the coarse to the fine regime and
is strictly narrower thereafter. The continuous-time small-cost band
around a target moved by a mean-reverting factor with constant
coefficients (`muhlekarbe2017primer`, Section 4, full text reviewed)
therefore has to be read with time-varying curvature and a drift term
before it can describe a learned target.

The machine check covers each numbered part in the finite-law
variant, including the exact \(1/t^2\) limits and the existence of
\(t_0\) independent of the horizon. The unconditional mean and
covariance of the belief-mean innovation over the finite law, used
only to describe it, are a reviewed paper step and enter no formal
conclusion. The results are for the finite-law variant. Under the
Gaussian law the second-moment facts in (ii)-(iii) still hold, but the
band statements are not proved. Part (iv) needs pure-learning
marking: with real returns the deviation also moves by the
instrument's return, which does not learn away, so an instrument can
stay in the coarse regime, and which ones do is a calibration
question. The symmetry in (iii) is a hypothesis. The fine regime's
leading order, per-direction bands under the pooled prior, a binding
budget and non-diagonal many-instrument learning statements are not
treated. No calibration is claimed.

Proposition 30 wrote the plug-in loss as a quadratic in the
coefficient errors. The last result writes it as an explicit function
of the model's inputs: starting holdings, prior means, precision
paths, costs, fees, spanning, risk aversion and horizon.

**Proposition 32 (The plug-in value loss as a function of the inputs; fund-of-funds learning model, unconstrained counterfactual; machine checked in its deterministic and pathwise content, with the expectation identities at paper level).**
Use Proposition 30's setting, allowing \(\Lambda\) positive semidefinite
provided each \(D_t\) is positive definite. Write \(V_s=P_s-P_{s+1}\) for the
*precision decrement* at review \(s\), the covariance of the belief
update \(\eta_s=m_{s+1}-m_s\), and \(\Phi_{t,s}=\tilde K_t\cdots\tilde K_{s+1}\) for the
plug-in transition products.

(i) *General case.* The trade error is
\(e_t=\mu_t+\sum_{u<t}W_{t,u}\eta_u\), where \(\mu_t\) is an explicit affine
function of the starting holding \(x_0\) and the prior mean \(m_0\), and
\(W_{t,u}=\delta K_t\sum_{s=u+1}^{t-1}\Phi_{t-1,s}\tilde L_s+\delta L_t\). The value
loss is

$$
V^*_0-V^\pi_0=\frac12\sum_{t=0}^{T-1}\rho^t\Bigl[\mu_t^\top D_t\mu_t
 +\sum_{u<t}\operatorname{tr}\bigl(D_tW_{t,u}V_uW_{t,u}^\top\bigr)\Bigr]:\tag{99}
$$

a quadratic polynomial in \((x_0,m_0)\) plus a term linear in the
precision decrements, with coefficients that are explicit products of
the policy coefficients. It is zero exactly when every \(\mu_t\), and
every \(W_{t,u}\) with \(V_u\neq0\), vanishes.

(ii) *Closed form in the separated homogeneous case.* In Proposition
29's setting without the pooled component, with the fund residual
variance \(\sigma_A^2\) and the factor covariance \(\Sigma_f\) estimated, the
loss splits into an exposure part and a fund part. The exposure part
is the myopic Markowitz loss of using the wrong factor covariance,
averaged over the premium belief's second moment,

$$
\mathrm{Loss}_y=\frac1{2\gamma}\sum_t\rho^t
 \operatorname{tr}\bigl(\Delta_t(\hat\lambda_0\hat\lambda_0^\top+P^\lambda_0-P^\lambda_t)\bigr),\tag{100}
$$

with \(\Delta_t=(\tilde\Sigma^{\lambda\,-1}_t-\Sigma^{\lambda\,-1}_t)\Sigma^\lambda_t
(\tilde\Sigma^{\lambda\,-1}_t-\Sigma^{\lambda\,-1}_t)\) and \(\Sigma^\lambda_t=\Sigma_f+P^\lambda_t\). The
fund part, for each fund with starting holding \(x_0\) and prior mean
\(\hat\alpha_0\), is
\(\mathrm{Loss}_A=\frac12\sum_t\rho^td_t[\mu_t^2+\sum_{u<t}w_{t,u}^2(p_u-p_{u+1})]\),
with the scalar recursion of Proposition 29 and explicit \(\mu_t\) and
\(w_{t,u}\). With a pooled prior the same holds in the common and
relative directions.

(iii) *How the fund loss depends on the inputs.* As a function of the
residual-variance error \(\epsilon=\tilde\sigma_A^2-\sigma_A^2\),
\(\mathrm{Loss}_A=C\epsilon^2+O(\epsilon^3)\), with an explicit constant \(C\) that is a
quadratic form in \((x_0,\hat\alpha_0)\) plus a term linear in the precision
decrements. As the fund cost \(\lambda_A\to0\), the loss tends to the
myopic loss \(\frac12\sum_t\rho^tr_t(1/\tilde r_t-1/r_t)^2(\hat\alpha_0^2+p_0-p_t)\),
with \(r_t=\gamma(\sigma_A^2+p_t)\), and the starting holding drops out. As
\(\lambda_A\to\infty\), the loss is of order \(1/\lambda_A\), exactly when \(x_0\neq0\),
and of order \(1/\lambda_A^3\) when \(x_0=0\): both policies stay near the
starting holding. The loss need not be monotone in the cost. With one
review,

$$
\mathrm{Loss}_A=\tfrac12(\lambda_A+r_0)\Bigl[(\lambda_Ax_0+\hat\alpha_0)
 \Bigl(\frac1{\lambda_A+\tilde r_0}-\frac1{\lambda_A+r_0}\Bigr)\Bigr]^2,\tag{101}
$$

which vanishes where \(\lambda_Ax_0+\hat\alpha_0=0\), since the trade is then
zero under either variance.

(iv) *Spanning decides whether the errors compound.* In the separated
case the factor-covariance error enters only the exposure part and the
residual-variance error only the fund part. With spanning, the fund
coefficients do not depend on the factor covariance at all. Without
spanning (Proposition 28's setting), the fund coefficients can depend
on it, through the reduced risk and the hedge map: in every such
setting, doubling the factor covariance changes the last review's
fund coefficient.

Part (i) unrolls the plug-in path in Proposition 30's identity. Part
(ii) specializes it to the separated case, where Proposition 27 (iii)
splits the problem. Part (iii) differentiates the scalar recursion in
the residual variance and takes limits in the cost. Part (iv) reads
the dependence off Proposition 28's reduced fund problem.

The loss of trading on a misestimated risk matrix is thus explicit in
where the investor starts and what it believes, plus a term for how
much its beliefs will still move, with coefficients set by costs, risk
aversion and horizon. The second-order shape in the parameter error is
known for stationary linear-quadratic-Gaussian control
(`mania2019certainty`, Theorems 3-4, cited for context as audited in
the ledger). What is added here is the constant in front of it, and
the whole loss, as an explicit expression in the inputs.

The machine check covers the deterministic and pathwise content: the
product form, the trade-error decomposition and when the loss
vanishes, (100) as an identity, the scalar recursion, the expansion
in \(\epsilon\), both cost limits with the exact orders, the one-review formula
and its positivity at intermediate cost, and the spanning statements.
The expectation identities over the Gaussian filtering model, which
turn the pathwise forms into (99)-(100) and the expectation form of
\(C\), are reviewed paper proofs. The estimated inputs are the
covariance blocks only. Monotonicity in the precision inputs or the
horizon is not established, and heterogeneous funds and ETF
frictions are covered only by (99), not in closed form. The
re-estimating guarantee is a separate result.

Propositions 30 and 32 assume the covariance is estimated once, before
the run. A manager who re-estimates at every review is not following a
fixed plug-in policy. The last result bounds that manager's expected
loss.

**Proposition 33 (An expected-loss guarantee for a manager who re-estimates at every review; fund-of-funds learning model, unconstrained counterfactual; machine checked in its pathwise core, with the expectation, split and confidence-sequence steps at paper level).**
Use Proposition 30's setting. At each review \(t\) the manager holds a
positive semidefinite covariance estimate \(\tilde\Sigma^{(t)}_r\), formed from
data available at \(t\), recomputes the coefficients of Proposition 27
from it, and trades with the review-\(t\) coefficients. Write
\(g=\|\Lambda^{-1/2}G\|\) and \(e=\|\Lambda^{-1/2}(0,c^E)\|\), and
\(M^*=\sup_{t\leq T}\|m_t\|\) for the largest belief mean along the path.

(i) *A priori bounds.* For every positive semidefinite estimate,
whatever its error,

$$
\|K^{(t)}_s\|_\Lambda\leq1,\qquad
\|\Lambda^{1/2}L^{(t)}_s\|\leq g(T-s),\qquad
\|\Lambda^{1/2}l^{(t)}_s\|\leq e(T-s),\tag{102}
$$

and the same holds for the true coefficients. The realized position
is therefore bounded along every path,
\(\|\Lambda^{1/2}x_t\|\leq X_t=\|\Lambda^{1/2}x_0\|+\sum_{s\leq t}(T-s)(gM^*+e)\).

(ii) *On the good event.* Let \(E_T\) be any event on which the
estimation error is at most \(r_t\) in the cost-weighted norm at every
review. On \(E_T\), each review's curvature-weighted squared trade error
is at most an explicit function \(L^{\rm on}_t(r_t;x_0,M^*)\), built from
Proposition 30's bounds at the constant error \(r_t\).

(iii) *The guarantee.* Off \(E_T\), (102) bounds the same quantity by an
explicit \(L^{\rm off}_t(x_0,M^*)\) with no dependence on the error. If
\(\Pr(E_T^c)\leq\alpha\), then

$$
V^*_0-V^\pi_0\leq\mathbb E\Bigl[\sum_t\rho^tL^{\rm on}_t(r_t;x_0,M^*)\Bigr]
 +\sqrt\alpha\,\Bigl(\mathbb E\Bigl[\Bigl(\sum_t\rho^tL^{\rm off}_t(x_0,M^*)\Bigr)^2\Bigr]\Bigr)^{1/2}.\tag{103}
$$

Both expectations are polynomials in \(\|\Lambda^{1/2}x_0\|\), the radii and
\(M^*\), and \(M^*\)'s moments are bounded by Doob's inequality in terms of
\(m_0\) and \(P_0-P_T\). So the expected loss is an explicit function of
the inputs and the radii: of order \(\sum_t\rho^tr_t^2\) on the good event,
plus \(\sqrt\alpha\) times an \(\alpha\)-free constant. Both terms vanish only as
the data before the run grow, with \(\alpha\) falling slowly enough that
the radii still shrink.

A time-uniform confidence sequence for the covariance supplies such an
event (`howard2021time`, Theorem 1, full text reviewed), applied
entrywise with a union bound. It is applied to differences of
consecutive observations, which have mean zero whatever the unknown
means, since the plain sample covariance does not qualify when the
means are unknown. The sequence's constants are not evaluated: the
result takes the radii as inputs.

The structural fact is (i). With a positive definite trading cost, a
rule built from any positive semidefinite risk estimate never moves
more than a cost-set fraction of the way, and never responds to
beliefs by more than a horizon-set multiple. So the loss is bounded on
every path, without any smallness condition on the estimation error
and without truncating the policy. The known fixed-error bound for
stationary linear-quadratic-Gaussian control needs such a smallness
condition, with constants from stability margins (`mania2019certainty`,
Theorems 3-4, cited for context as audited in the ledger).

The machine check covers the pathwise core: the bounds (102) for any
positive semidefinite estimate and for the true coefficients, the
position bound along the re-estimating path, and the pathwise on-event
and off-event bounds. The following are reviewed paper proofs, not
machine checked:
- the loss identity in expectation for the re-estimating policy;
- the split of the expectation over \(E_T\) and its complement, with
  Cauchy-Schwarz and Doob's inequality for \(M^*\);
- the existence of \(E_T\) from the confidence sequence.

The on-event constants can be loose by large factors at realistic
inputs, and whether the \(\sqrt\alpha\) term can be improved to \(\alpha\) is not
pursued. Estimated loadings, costs or fees, and a misestimated filter,
are not treated.

Propositions 27 and 29 show that the aim anticipates learning. The
last result asks when that anticipation, or anticipation of mean
reversion in alpha, changes today's trade by a material amount, and
answers with explicit conditions on the inputs.

**Proposition 34 (When anticipating learning or mean reversion changes today's trade; fund-of-funds learning model, separated homogeneous case; machine checked, with the persistence aim formula and two readings at paper level).**
Take Proposition 29's separated homogeneous case without the pooled
component, with fund cost \(\lambda_A>0\). Let
\(\kappa_t=p_t/(\sigma_A^2+p_t)\) be the *Kalman gain* on alpha, the weight of
one quarter's residual return in the belief update. A *static-belief*
manager freezes the risk path at today's value and re-solves each
review. Its aim is \(\mathrm{aim}^S_t=\hat\alpha_t/(\gamma(\sigma_A^2+p_t))\), and its rate
\(g^S_t\) comes from the recursion with constant risk \(r_t=\gamma(\sigma_A^2+p_t)\). The
*learning-aware* manager of Proposition 29 has aim \(\mathrm{aim}_t\) and rate
\(g_t\). Today's trades are \(u_t=g_t(\mathrm{aim}_t-x_{t-1})\) and
\(u^S_t=g^S_t(\mathrm{aim}^S_t-x_{t-1})\).

(i) *Learning moves the aim by at most the gain's odds.*
\(\mathrm{aim}_t=L_t\,\mathrm{aim}^S_t\), with Proposition 29's learning factor

$$
1\leq L_t<\frac1{1-\kappa_t}=1+\frac{\kappa_t}{1-\kappa_t},\tag{104}
$$

and \(L_t=1\) exactly at the last review. So anticipating learning
raises today's target by a relative amount above \(\theta\) only if the
Kalman gain exceeds \(\theta/(1+\theta)\), whatever the cost, horizon and
starting holding.

(ii) *Learning slows trading, and the trade changes to first order in
the gain.* \(g_t\leq g^S_t\): a manager who expects a falling risk charge
trades more slowly. With \(g(r;n)\) the constant-risk rate with \(n\)
reviews to go,

$$
|u_t-u^S_t|\leq\bigl[g(r_t;T-t)-g(\gamma\sigma_A^2;T-t)\bigr]\,|\mathrm{aim}^S_t-x_{t-1}|
 +g_t\frac{\kappa_t}{1-\kappa_t}\,|\mathrm{aim}^S_t|,\tag{105}
$$

where the first bracket is at most
\((T-t)\lambda_A\gamma p_t/(\lambda_A+\gamma\sigma_A^2)^2\). Both terms are of first order in
the gain, with explicit constants in the cost, the risk aversion,
the horizon and the position. A checkable condition for a material
change is that the right side exceed a stated fraction of \(|u^S_t|\).

(iii) *Mean reversion.* If alphas revert to a long-run mean
\(\bar\alpha\) at persistence \(\phi\in[0,1]\), the aim splits into a long-run part
and a deviation part, and the deviation part is scaled by a weight
\(M_t(\phi)\) that is nondecreasing in \(\phi\), with \(M_t(1)=1\) and

$$
\tilde w_{t,t}+(1-\tilde w_{t,t})\phi^{T-1-t}\leq M_t(\phi)\leq1,\tag{106}
$$

where \(\tilde w_{t,t}\) is the recursion's weight on today, renormalized by
the precision ratios. Mean reversion changes the deviation part by more
than a fraction \(\theta\) only if \((1-\tilde w_{t,t})(1-\phi^{T-1-t})>\theta\). That
requires a cost high enough to put weight on the future, and a
persistence low enough over the remaining horizon.

(iv) *Only where trading costs.* As \(\lambda_A\to0\), \(L_t\to1\) and \(M_t(\phi)\to1\)
for every \(\phi\): both anticipation effects are cost effects. The costless
ETF exposure is re-set to its myopic position every review, so premium
learning and premium mean reversion never change today's exposure
trade beyond today's estimate.

Part (i) is Proposition 29's weighted average, whose terms lie between
today's precision ratio and one. For (ii), the constant-risk rate is
increasing in the risk and Lipschitz in it with an explicit constant.
For (iii), the recursion's weights, renormalized, form a probability
distribution over the remaining reviews, and \(M_t\) is its average of
\(\phi^{s-t}\). Part (iv) takes the limit of the weights.

The benchmark splits the optimal allocation under a mean-reverting
premium into a myopic term and a hedging term, which disappears when
the investment opportunity set is constant (`wachter2002portfolio`,
equation (35) and p. 73, full text reviewed). Here the objective is a
per-review certainty equivalent, so there is no hedging demand at
all. What remains are the cost effects above, which vanish for
costless instruments. Under proportional costs and caps, the same
anticipation appears as the outward drift and tilt of the band in
Proposition 31.

The machine check covers each numbered part on a general nonincreasing
positive precision path, including the exact form of \(L_t-1\), the
threshold condition, the rate bounds and Lipschitz constant, the trade
identity and bound, the properties of \(M_t\), and the zero-cost limits.
Three steps are reviewed paper proofs:
- the aim formula under mean reversion, which extends Proposition 27's
  recursion to persistent alphas;
- the reading that the objective carries no hedging demand, which is
  a matter of its definition;
- the reading against Proposition 31's band.

Heterogeneous funds, ETF trading costs, and the pooled prior beyond
the direction-by-direction reading are not treated. That the learning
factor rises with cost and horizon was observed in every case tested
but is not proved.

Proposition 28 showed, under quadratic costs, that premium beliefs
reach fund choice only through the factor directions ETFs cannot
reach. The last result states what that means for a single review
with proportional costs: when a premium error changes a fund's hold,
buy or sell decision, by how much, at what cost, and what a rule that
picks funds on total estimated return loses.

**Proposition 35 (How premium error enters fund choice: not through spanning ETFs, through the hedged unreachable part of a fund's loading, and in full under naive selection; learning-driven tracking model at one review, ETFs frictionless; machine checked, with the expectations over the premium error at paper level).**
Fix one review of the learning-driven tracking model in the reference
case, with \(N\) funds, \(M\) ETFs with \(B^E\) of full row rank \(M\leq K\), fund
purchase and sale rates \(\kappa^\pm_i\), caps \(\bar x_i\) and incumbents \(x^-_i\).
ETFs are frictionless, and the budget and every ETF bound are slack at
the optima compared. Let \(v_i=\Sigma_{A,ii}+P^\alpha_{ii}\), let \(e=\hat\lambda-\lambda\) be
the premium error, and use Proposition 28's hedge map \(J\) and Schur
complement \(\tilde\Sigma_{U\cdot R}\). For each fund define the reduced moments
\(\alpha^{\rm red}_i=\hat\alpha_i+B^A_iJ^\top\hat\lambda\) and
\(s^{\rm red}_i=v_i+B^A_i\tilde\Sigma_{U\cdot R}B^{A\top}_i\), and the *alpha-band holding*

$$
a_i=\mathrm{clip}\Bigl(x^-_i,\ \frac{\alpha^{\rm red}_i-\kappa^+_i}{\gamma s^{\rm red}_i},\
 \frac{\alpha^{\rm red}_i+\kappa^-_i}{\gamma s^{\rm red}_i}\Bigr),\ \text{clipped to }[0,\bar x_i]:\tag{107}
$$

hold inside the band, otherwise trade to its nearer edge.

(i) *Spanning ETFs keep premium error out.* If \(M=K\) with \(B^E\)
invertible, every fund is held at its alpha-band holding with
\(\alpha^{\rm red}_i=\hat\alpha_i\) and \(s^{\rm red}_i=v_i\). Fund holdings do not depend on
the premium belief, its uncertainty or the loadings. Premium error
reaches only the ETF exposure, at the Markowitz cost
\(e^\top\tilde\Sigma_f^{-1}e/(2\gamma)\).

(ii) *One unreachable fund: a persistent shift and a transient
narrowing.* If exactly one fund \(i\) has a loading with a component
outside the ETFs' reach, the joint optimum holds it at (107) with its
reduced moments and the others at their spanning holdings. The premium
reaches fund \(i\)'s decision only through the scalar \(\delta=B^A_iJ^\top e\), the
hedged unreachable part of its loading times the error, which shifts
the band's centre. Premium uncertainty narrows the band by the factor
\(v_i/s^{\rm red}_i\), and that narrowing learns away while the shift does not.
The holding moves by at most \(|\delta|/(\gamma s^{\rm red}_i)\), exactly that on a
common trading piece, and not at all on a common hold piece. A held
fund is moved by no error with \(|\delta|\) at most the band's slack. A bought
fund is turned into a hold or a sale only by a negative \(\delta\) at least as
large as its margin over the purchase threshold. The loss in the
fund's reduced objective satisfies

$$
0\leq\mathrm{loss}\leq\frac{\gamma s^{\rm red}_i}2\Delta^2+(\kappa^+_i+\kappa^-_i+\mu)|\Delta|,
\qquad|\Delta|\leq\frac{|\delta|}{\gamma s^{\rm red}_i},\tag{108}
$$

with \(\mu\) the cap's multiplier, zero at an interior holding. With
\(\ell_i^2=B^A_iJ^\top P^\lambda JB^{A\top}_i\), the leak variance, and \(\mu=0\), the expected
loss is at most \(\ell_i^2/(2\gamma s^{\rm red}_i)+(\kappa^+_i+\kappa^-_i)\ell_i/(\gamma s^{\rm red}_i)\):
second order in the premium error, and first order only through the
trading cost of the misplaced trade.

(iii) *Naive selection lets the whole premium in.* With spanning,
suppose each fund is chosen from its total estimated mean
\(\hat\alpha_i+B^A_i\hat\lambda\) and total variance \(v_i+B^A_i\tilde\Sigma_fB^{A\top}_i\) by the
same band rule, with ETFs then re-optimized. Its loss against the joint
optimum is exactly

$$
\Lambda^{\rm naive}=\sum_i\bigl[\psi_i(a_i)-\psi_i(a^{\rm naive}_i)\bigr]\geq0,\qquad
\psi_i(a)=\hat\alpha_ia-\tfrac\gamma2v_ia^2-\kappa^+_i(a-x^-_i)^+-\kappa^-_i(x^-_i-a)^+,\tag{109}
$$

zero exactly when every naive holding is the alpha-band holding. The
premium error enters the naive holdings in full. From a zero
incumbent, the naive rule buys fund \(i\) when
\(\hat\alpha_i+B^A_i\hat\lambda>\kappa^+_i\), and the hedged rule when \(\hat\alpha_i>\kappa^+_i\). So a
fund with negative net alpha but a positive loaded premium is bought
naively, at an explicit loss.

For (i), with spanning ETFs the exposure can be set freely, so the
fund problem separates from it and involves only alpha. For (ii), the
fund's problem is Proposition 28's reduced problem at one review, and
its solution is the band (107), which is Lipschitz in the reduced alpha
with constant \(1/(\gamma s^{\rm red}_i)\). The loss bound (108) compares the reduced
objective at two points on either side of a kink. Part (iii) sums the
reduced-objective gaps, since the ETFs re-optimize around any fund
holdings.

In the inputs, then, premium error enters fund choice through one
scalar per fund, \(B^A_iJ^\top e\). It is zero for every fund a spanning menu
of frictionless ETFs can hedge, and nonzero exactly for loadings the
menu cannot reach. A rule that picks funds on total estimated return
forgoes the hedge and admits the whole premium error, at the explicit
loss (109); that is the gain from hedging a fund's factor part with
ETFs. The static analogue of the unhedged part is the "nonbenchmark"
component of a fund's return in Pástor and Stambaugh's Bayesian fund
choice (`pastor2002investing`, full text reviewed).

The machine check covers each numbered statement pointwise: (i), the
joint optimum and each part of (ii) including the move and loss bounds,
and the exact identity and zero condition of (iii). The expectations
over the premium error, the expected squared move and expected loss in
(ii) and the expected squared error in (iii), are reviewed paper
proofs, each applying the formal pointwise bound. The result is for
one review with one unreachable fund. Several unreachable funds couple
through the Schur complement. ETF frictions, and ETF bounds that bind
(an ETF at zero cannot be sold to hedge), are not treated. The premium
error is a fixed perturbation, with covariance \(P^\lambda\) only for the
expectations. No coverage statement or magnitude is claimed.

Propositions 15-19 measured how much history certifies an active trade
against the optimized ETF-only class, in fixed families. The last
result restates that question for a fund decision, as conditions in the
inputs: when can a history of returns support buying (or selling) a
fund?

**Proposition 36 (When data can support an active change, in the inputs; learning-driven tracking model at one review, spanning frictionless ETFs; machine checked in its pointwise and deterministic content, with the probability steps at paper level).**
Fix one review with spanning, frictionless ETFs and slack budget and
caps, and one fund \(i\) with residual variance \(\sigma_{A,i}^2\), posterior
variance \(p_i\), \(v_i=\sigma_{A,i}^2+p_i\), incumbent \(x^-_i\) and trading rates
\(\kappa^\pm_i\). Define the *buy threshold* and the *gap*

$$
b_i=\kappa^+_i+\gamma v_ix^-_i,\qquad \Delta_i=\alpha_i-b_i.\tag{110}
$$

A rule maps an \(n\)-quarter history of the fund's residual returns
\(\alpha_i+z^A_{ij}\) to "buy" or "no change". It *certifies at \((\delta,\varepsilon)\)* if
it buys with probability at most \(\varepsilon\) whenever \(\Delta_i\leq0\) and at least
\(1-\varepsilon\) whenever \(\Delta_i\geq\delta\), for every law in the stated class.

(i) *The decision is the gap's sign.* The review's optimum for fund \(i\)
is unique, and lies above \(x^-_i\) exactly when \(x^-_i<\bar x_i\) and \(\Delta_i>0\);
a fund at its cap cannot be bought. Selling is symmetric, with sale
threshold \(s_i=-\kappa^-_i+\gamma v_ix^-_i\), and a fund at zero cannot be sold. Premium beliefs, their
precision and the loadings do not enter. Supporting an active change
therefore means certifying the sign of \(\Delta_i\), a hypothesis about the
fund's own alpha, with costs and the incumbent inside the threshold.

(ii) *Known Gaussian law.* The rule "buy if
\(\hat\alpha_i-\sigma_{A,i}z_\varepsilon/\sqrt n>b_i\)", with \(\hat\alpha_i\) the sample mean and \(z_\varepsilon\) the
normal quantile, certifies once \(n\geq4\sigma_{A,i}^2z_\varepsilon^2/\delta^2\). For
\(\varepsilon<1/4\), no rule certifies unless

$$
n\geq\frac{4\sigma_{A,i}^2}{\delta^2}\log\frac1{4\varepsilon},\tag{111}
$$

so the needed history is of order \((\sigma_{A,i}^2/\delta^2)\log(1/\varepsilon)\). A
normal prior with variance \(s^2\) is worth \(\sigma_{A,i}^2/s^2\) quarters of data.

(iii) *Unknown bounded law.* With residuals bounded by \(R\) and
otherwise unknown, the Hoeffding rule certifies once
\(n\geq(8R^2/\delta^2)\log(1/\varepsilon)\), and a two-point law shows that no rule
certifies unless \(n\geq(R^2/\delta^2)\log(1/\varepsilon)\), for \(0<\delta\leq R/2\) and
\(\varepsilon\leq1/16\). Not knowing the law costs no
order, only the range in place of the standard deviation, as in
Proposition 19.

(iv) *Persistent residuals.* If the residual process is stationary and
satisfies a generalized Bernstein inequality with an effective number
of observations \(n_{\rm eff}\leq n\), with constants \(c_\sigma,c_B,C\), variance
bound \(\sigma^2\) and range bound \(B\), the certificate with margin \(\delta/2\)
works once \(n_{\rm eff}\geq(4c_\sigma\sigma^2+2c_B\delta B)\log(C/\varepsilon)/\delta^2\). For
independent data this is of order (iii)'s length; persistence of the
residuals only discounts the history.

(v) *Persistent alpha: a floor no history removes.* If alpha itself
follows \(\alpha_{t+1}=\phi\alpha_t+(1-\phi)\bar\alpha+\eta_t\) with innovation variance
\(q>0\) and \(|\phi|<1\), the prediction variance of the current alpha falls
monotonically to

$$
p_\infty=\tfrac12\Bigl[(q-\sigma_{A,i}^2(1-\phi^2))
 +\sqrt{(q-\sigma_{A,i}^2(1-\phi^2))^2+4q\sigma_{A,i}^2}\Bigr]>0\tag{112}
$$

from any prior at least as diffuse, and never below it. So for
\(\varepsilon\leq1/2\) no history certifies a buy at posterior confidence \(1-\varepsilon\)
unless the estimated gap exceeds \(z_\varepsilon\sqrt{p_\infty}\). That is a ceiling on
precision, not a discount on \(n\); an effective sample size cannot
express it. It vanishes as \(q\to0\), and rises to the alpha process's
own stationary variance as the residuals become uninformative.

(vi) *Spanning keeps premium error out.* Under spanning, premium
precision plays no role. Without it, with premia estimated from the
same history, the needed history in (ii) is multiplied by

$$
1+\frac{B^A_iJ^\top\Sigma_fJB^{A\top}_i}{\sigma_{A,i}^2},\tag{113}
$$

the unhedgeable part of the loading's factor variance over the
residual variance, with \(J\) Proposition 28's hedge map. Part (iii) is
not covered, since Gaussian premium error is unbounded.

(vii) *A pooled prior makes a common tilt \(N\) times cheaper.* With the
pooled prior of Proposition 29 and homogeneous residuals, the average
alpha across \(N\) funds has posterior variance
\(\frac1N(1/(s^2+N\bar s^2)+n/\sigma_A^2)^{-1}\). Certifying a common tilt, the
average net alpha above a common threshold, needs a history of order
\((\sigma_A^2/(N\delta^2))\log(1/\varepsilon)\), \(N\) times shorter than one fund's own
alpha, while a relative direction keeps the single-fund rate.

The upper bounds are concentration: the Gaussian tail in (ii) and
Hoeffding's inequality in (iii) (`hoeffding1963probability`, Theorem 1,
full text reviewed). The lower bounds are Le Cam's two-point method
(`lecam1973convergence`, Lemma 1, full text reviewed), as in Propositions
15-16. Part (iv) is Hang and coauthors' generalized Bernstein
inequality with an effective number of observations
(`hang2016learning`, Assumption 2, inequality (7) and Section 3.3, full
text reviewed). Part (v) is the steady state of the scalar Kalman
filter. What the fund-of-funds structure adds is the threshold that
the costs and the incumbent set, the role of spanning, the direction
split under the pooled prior, and the precision floor from persistent
alpha.

The machine check covers the one-review decision (i), the certifying
rule and the arithmetic of the lower bound in (ii), the Hoeffding rule
and the two-point lower bound in (iii), the certificate under the effective-sample-size inequality
in (iv), the fixed point, monotone convergence and limits in (v), and
the Gaussian computations in (vi)-(vii). The following are reviewed
paper proofs, not machine checked:
- the probability step of (ii)'s lower bound, which takes Le Cam's
  inequality as a premise, since no formal structure for non-finite
  laws exists;
- the mixing instantiations in (iv), which are citations;
- the Gaussian and Kalman posterior forms;
- the reduction of the full review to the one-fund problem.

The threshold's general form with ETF frictions and several funds
traded at once are not treated. Lower bounds for persistent residuals
and a frequentist version of the floor in (v) are not given.

Propositions 26-36 were stated in two cost models, quadratic and
proportional. The last result says what the two share, what they do
not, and where the one-quarter theory of Propositions 9 and 22-23 sits
in both.

**Proposition 37 (One tracking problem under two cost models: a common target and loss, one trade map per cost, and an anticipation order set by the cost's smoothness; fund-of-funds learning model and learning-driven tracking model; machine checked in its new steps, with the component results through their formal statements, and the proportional-cost anticipation at paper level, cited at leading order).**
A *quarterly tracking instance* has the fund-of-funds learning model's
instruments, factor model, pooled Gaussian prior and Kalman filter
with fixed means. Its predictive moments \(\mu_t\) and \(\Sigma_t\) are
deterministic, with \(\Sigma_t\) positive definite and nonincreasing, and its
*target* is \(x^*_t=(\gamma\Sigma_t)^{-1}\mu_t\). Given a discount \(\rho\in(0,1]\), a horizon
\(T\), a convex trading cost \(C_t\) and a closed convex set \(X_t\) of
post-trade holdings, the objective is

$$
\mathbb E\sum_{t=0}^{T-1}\rho^t\Bigl[\mu_t^\top x_t-\frac\gamma2x_t^\top\Sigma_tx_t-C_t(x_t-x^-_t)\Bigr],
\qquad x_t\in X_t,\tag{114}
$$

with \(x^-_t\) the pre-trade holding. The fund-of-funds learning model is
the instance with \(C_t(u)=\frac12u^\top\Lambda u\) and no constraint; the
learning-driven tracking model is the instance with directional
proportional rates \(\kappa^\pm_i\), caps, a cash constraint and marking by
gross returns.

(i) *The bridge.* For every positive definite \(\Sigma\),

$$
\mu^\top x-\frac\gamma2x^\top\Sigma x=-\frac\gamma2(x-x^*)^\top\Sigma(x-x^*)+\frac1{2\gamma}\mu^\top\Sigma^{-1}\mu,\tag{115}
$$

so both models minimize expected discounted tracking loss against the
same target and in the same metric. Only the cost and the constraints
differ, and nothing below transfers a policy from one model to the
other.

(ii) *The target is common, and its learning drift is second order in
the gain.* The target's split into ETF exposure and fund alpha, the
leak of premium beliefs through directions ETFs cannot reach, and its
motion as belief innovation plus a known learning drift are properties
of the target (Propositions 27, 28 and 31), so they hold in both
models. In Proposition 29's scalar fund block with Kalman gain
\(\kappa_t=p_t/(\sigma_A^2+p_t)\), the target's cumulative relative drift from
review \(t\) to review \(s\geq t\) satisfies

$$
\frac{\sigma_A^2+p_t}{\sigma_A^2+p_s}-1=\frac{p_t-p_s}{\sigma_A^2+p_s}\leq(s-t)\Bigl(\frac{\kappa_t}{1-\kappa_t}\Bigr)^2,\tag{116}
$$

while the belief innovation has variance \(p_t\kappa_t\), which moves the
target by a relative standard deviation of order \(\sqrt{p_t\kappa_t}/|\hat\alpha_t|\).

(iii) *The trade is one map of the gap per cost, and anticipation has
the order of the cost's smoothness.* Under quadratic costs the trade is
partial adjustment toward an aim (Propositions 27, 29 and 34); under
proportional costs it is the projection onto a band around the target
(Propositions 26 and 31). With \(w_{t,s}\) the positive weights, summing to
one over the remaining reviews \(s\geq t\), of Proposition 29's weighted
average, the learning factor \(L_t\) satisfies

$$
L_t-1=\sum_{s>t}w_{t,s}\Bigl[\frac{\sigma_A^2+p_t}{\sigma_A^2+p_s}-1\Bigr]\leq\Bigl(\frac{\kappa_t}{1-\kappa_t}\Bigr)^2D_t,
\qquad D_t=\sum_{s>t}w_{t,s}(s-t),\tag{117}
$$

strictly positive before the last review, with the aim's look-ahead
duration \(0\leq D_t\leq T-1-t\) tending to zero with the fund cost. So
under quadratic costs anticipating learning changes the aim by a
fraction \(\theta\) only if \((\kappa_t/(1-\kappa_t))^2D_t\geq\theta\): order \(\kappa_t^2\) times a
bounded duration, which sharpens (104). Under proportional costs in the
coarse regime the band's shift is Proposition 31's tilt, one step of
the drift, which vanishes with it. In the fine regime no bound is
proved; the leading-order displacement from continuous trading is
about two thirds of the band's mixing time times the per-step drift,
which along the fixed-means path is of order \(\kappa_t^{4/3}\) if the
half-width falls like \(t^{-2/3}\). That order is a reading, not a result.
No condition on the relative change of today's trade is claimed, since
the static trade can be zero.

(iv) *The value loss of any policy is one identity.* On a finite-law
problem, for every feasible policy \(\pi\) and initial law,
\(V^*-V^\pi=\sum_t\rho^t\,\mathbb E\,\Delta_t\), where \(\Delta_t\geq0\) is the policy's Bellman
residual at its own state; with stage rewards bounded by \(c\) and \(H_t\)
the remaining discounted horizon, \(|J_t|\leq cH_t\) and \(\Delta_t\leq2cH_t\). Under
quadratic costs the residual is Proposition 30's completed square;
under proportional costs it is the excess tracking loss and cost of
the chosen holding over the band projection. The a priori device for
re-estimation is Proposition 33's contraction under quadratic costs,
and the caps under proportional costs: every admissible stage reward is
at most \(|\mu_t|^\top\bar x+\frac\gamma2\|\Sigma_t\|\|\bar x\|^2+\sum_i(\kappa^+_i+\kappa^-_i)\max(\bar x_i,x^-_{t,i})\) in size,
with no condition on the estimate. At the last review, with a slack
budget and one instrument, the band built from estimates \(\tilde c\) of
\(c=\gamma\Sigma\) and \(\tilde x^*\) of \(x^*\) loses at most

$$
\bigl(|\mu|+c\bar x+\max(\kappa^+,\kappa^-)\bigr)\max(|\Delta_{\rm lo}|,|\Delta_{\rm hi}|),\qquad
|\Delta_{\rm lo}|,|\Delta_{\rm hi}|\leq|\tilde x^*-x^*|+\kappa^\pm\Bigl|\frac1{\tilde c}-\frac1c\Bigr|,\tag{118}
$$

with \(\kappa^+\) for the lower edge and \(\kappa^-\) for the upper.

(v) *The horizon-one case is the one-quarter theory.* At \(T=1\), or at
the last review, the proportional-cost instance is Proposition 26's
last-review band, which is Proposition 9's multiplier criterion with
\(n\) instruments and the predictive covariance, and Propositions 22-23
apply to it. The quadratic-cost instance is
\(x_0=(\Lambda+\gamma\Sigma_0)^{-1}(\Lambda x^-+\mu_0)\), the unique maximizer, which trades
unless \(\mu_0=\gamma\Sigma_0x^-\). At the same inputs the contrast with
Proposition 9 is the cost model, not the horizon.

What composes is the target and its structure, the loss metric and
the residual identity, the shape of the re-estimation guarantee, the
horizon-one reduction, and the anticipation orders in (iii), which
neither model gives alone. What does not compose is the trade rule:
the aim has no proportional-cost counterpart and the band has no
quadratic-cost counterpart, so one trade rule for both would need to
drop one cost model.

Part (i) is the expansion of the quadratic. For (116), the scalar
filter with a constant state has \(1/p_s=1/p_t+(s-t)/\sigma_A^2\). Part (iii)'s
bound applies (116) termwise to Proposition 29's exact form of \(L_t-1\).
Part (iv) telescopes the value function along the policy, and the
residual is nonnegative because the Bellman equation maximizes over a
set containing the policy's choice. The last-review bound in (118)
uses that clipping is 1-Lipschitz in its edges and that the one-review
objective is Lipschitz on \([0,\bar x]\). Part (v) is the first-order
condition of a concave quadratic.

The fine-regime displacement is Martin's leading-order law for bands
around a moving target (`martin2012optimal`, equations (9)-(10), read
at the level of its displayed formulas), in the discrete form of
Proposition 31's model. It agreed with exact dynamic programs to about
one percent in the stationary case and to 10-30 percent on the
learning path; that agreement illustrates the law and does not prove
it. The residual identity is
elementary dynamic programming. Matched asymptotic expansions, an
outer solution away from a boundary joined to an inner one near it,
would give one composite rule, with the quadratic-cost policy outside
and the band as the inner correction (`howison2005matched` and, for one
asset with a small quadratic cost, `chandra2019singular`, both read at
the level of their abstracts). That rule is not built here.

A multi-review estimation bound under proportional costs, a proved
bound on the fine-regime band centre, the tilt's order in the gain,
and the return-driven motion of the target through marking are not
treated.

Proposition 26 gave one instrument's band across reviews and, in
(v), the static shape of the no-trade set when a fund sits beside
other instruments. The last result follows a fund's band across
reviews when the ETFs beside it are traded optimally.

**Proposition 38 (A fund's band beside optimally traded ETFs: a residual-variance ceiling, a bracket through the ETFs' cost bands, and the one-instrument band when ETFs are frictionless; learning-driven tracking model with a slack budget, one fund and \(M\geq1\) ETFs; machine checked).**
Fix a slack-budget instance of the multi-review tracking model with
covariance \(\Sigma_t\) depending on the review and the state, as
Proposition 31 reads the learning-driven model, one fund \(A\) and \(M\)
ETFs \(E\), and the stay objective \(G_t\) of Proposition 26. Partition \(\Sigma_t\)
into \(\Sigma_{AA}\), \(\Sigma_{AE}\) and \(\Sigma_{EE}\), and define the *hedge ratios*, the
fund's *residual variance given the ETFs* and its *residual curvature*,

$$
\rho_t=\Sigma_{AE}\Sigma_{EE}^{-1},\qquad
\sigma^2_{A\cdot E,t}=\Sigma_{AA}-\Sigma_{AE}\Sigma_{EE}^{-1}\Sigma_{EA},\qquad
c^{\rm res}_t=\gamma\sigma^2_{A\cdot E,t}.\tag{119}
$$

With \(\bar g_j\) the expected gross returns, the *leak bounds*

$$
\begin{aligned}
H^+_t&=\textstyle\sum_j\bigl[\rho_j^+(\kappa^+_{E,j}+\beta\kappa^-_{E,j}\bar g_j)+\rho_j^-(\kappa^-_{E,j}+\beta\kappa^+_{E,j}\bar g_j)\bigr],\\
H^-_t&=\textstyle\sum_j\bigl[\rho_j^+(\kappa^-_{E,j}+\beta\kappa^+_{E,j}\bar g_j)+\rho_j^-(\kappa^+_{E,j}+\beta\kappa^-_{E,j}\bar g_j)\bigr]
\end{aligned}\tag{120}
$$

are the most the ETFs' cost bands and continuation slopes, weighted by
the hedge ratios, can raise or lower the fund's marginal. The fund's
*ETF-optimized value* \(U_t(a;p^-)\) is the least of \(G_t((a,p),z)+C_E(p-p^-)\)
over ETF holdings \(p\) in the ETF box.

(i) *One-instrument structure.* \(U_t\) is continuous and
\(U_t-\frac12c^{\rm res}_ta^2\) is convex. The full optimum is the fund problem
\(\min_a[U_t(a;p^-)+C_A(a-a^-)]\) followed by the ETF problem at that \(a\). So
the fund's post-trade holding is the clip (79) of \(a^-\) to an *effective
band* \([lo_t,hi_t]\subseteq[0,\bar x_A]\), defined by \(U_t\)'s one-sided derivatives
reaching \(-\kappa^+_A\) and \(\kappa^-_A\), and the fund is held exactly when \(a^-\)
lies in it. The ETF incumbents enter only through \(U_t\).

(ii) *A residual-variance ceiling.* At every review and state, and for
every ETF incumbent,

$$
hi_t-lo_t\leq\frac{\kappa^+_A+\kappa^-_A}{\gamma\sigma^2_{A\cdot E,t}}.\tag{121}
$$

This is the fund's static width with its residual variance in place of
its total variance, wider than a fund alone by
\(\Sigma_{AA}/\sigma^2_{A\cdot E,t}\), which is \(1/(1-\mathrm{corr}^2)\) for one ETF: the ETFs
absorb the fund's factor risk.

(iii) *A bracket through the ETFs' bands.* With \(a^*_t\) the fund's
target coordinate and the ETF optimizer interior to the ETF box,

$$
hi_t\leq a^*_t+\frac{\kappa^-_A+\beta\kappa^+_A\bar g_A+H^+_t}{c^{\rm res}_t}\ \ (hi_t>0),\qquad
lo_t\geq a^*_t-\frac{\kappa^+_A+\beta\kappa^-_A\bar g_A+H^-_t}{c^{\rm res}_t}\ \ (lo_t<\bar x_A).\tag{122}
$$

The ETFs' costs enter the fund's band at the hedge ratios, and each
instrument's continuation at \(\beta\) times its rates times its expected
gross return; nothing else about the future enters.

(iv) *The last review: three regimes.* At \(T-1\), with the edges and the
ETF optimizer interior,

$$
hi_{T-1}=a^*+\frac{\kappa^-_A+\rho^\top c_E(hi)}{c^{\rm res}},\qquad
lo_{T-1}=a^*-\frac{\kappa^+_A-\rho^\top c_E(lo)}{c^{\rm res}},\tag{123}
$$

with \(c_E\) the ETFs' cost slopes at the ETF-optimized point. If the
ETFs re-hedge the same way at both edges, the width is the ceiling
(121). If every ETF re-hedges in opposite directions at the two edges,
it is the ceiling minus \(\sum_j|\rho_j|(\kappa^+_{E,j}+\kappa^-_{E,j})/c^{\rm res}\). If the ETFs
are untraded at both edges, it is exactly the fund-alone width
\((\kappa^+_A+\kappa^-_A)/(\gamma\Sigma_{AA})\), for any \(M\) and without the interiority
of the ETF optimizer. Every band interior to the fund's box is at least
that wide, so the last-review width lies between the fund-alone width
and the residual ceiling.

(v) *An outer parallelotope.* For any number of instruments, every
no-trade holding strictly inside the box lies in

$$
x^*_t+(\gamma\Sigma_t)^{-1}\prod_i\bigl[-(\kappa^+_i+\beta\kappa^-_i\bar g_i),\ \kappa^-_i+\beta\kappa^+_i\bar g_i\bigr],\tag{124}
$$

the static parallelotope of Proposition 26 (v) with each rate widened
by \(\beta\) times the opposite rate times the expected gross return.
With (82), the dynamic no-trade region never exceeds the static one's
\(\Sigma_t\)-diameter, whatever the targets' motion.

(vi) *Frictionless ETFs.* If the ETFs are frictionless, residual-free,
fee-free and spanning, and the hedge \(x^*_E-\rho_t(a-a^*_t)\) lies in the ETF
box for every \(a\in[0,\bar x_A]\) at every review and state, then, for every
ETF incumbent, \(U_t\) is up to a constant the stay objective of a
one-instrument instance with curvature \(c^{\rm res}_t\), target \(a^*_t\) and the
fund's own rates, cap and gross returns. The fund's band is then that
instance's band, so Proposition 26 applies to it, and so, on paper,
do Proposition 31's learning-path statements; the ETFs
carry no band of their own.

The proof minimizes over the ETFs first. The Schur identity
\(d^\top\Sigma d-\sigma^2_{A\cdot E}d_A^2=(d_E+\Sigma_{EE}^{-1}\Sigma_{EA}d_A)^\top\Sigma_{EE}(d_E+\Sigma_{EE}^{-1}\Sigma_{EA}d_A)\)
makes \(G_t-\frac12c^{\rm res}_ta^2\) jointly convex, and a partial minimum of a
jointly convex function over a convex set is convex. That gives (i),
and Proposition 26's argument applied to \(U_t\) gives (121). For (122)
the fund moves along the hedge direction \((1,-\rho_t)\), and the
continuation's slopes are bounded by \(\beta\) times the rates times the
expected gross returns. At the last review there is no continuation,
so (123) is exact; with idle ETFs their slopes move with the fund's
holding, and \(c^{\rm res}+\gamma\Sigma_{AE}\Sigma_{EE}^{-1}\Sigma_{EA}=\gamma\Sigma_{AA}\) gives the fund-alone width.
Part (v) compares one-sided differences coordinate by coordinate, and
(vi) is backward induction, since frictionless ETFs can be moved to any
exposure at no cost.

In continuous time with small costs, the multi-asset no-trade region
solves a corrector equation that has no explicit solution beyond one
dimension (`possamai2015homogenization`, read at the level of its
abstract and introduction). The result above is exact at quarterly
reviews and places the fund's band between explicit bounds in the
inputs instead. A binding cap reshapes a band at leading order in
continuous time (`liu2013portfolio`, full text reviewed); here the
budget is slack and the caps only clip.

The shape of the dynamic region inside (124), its dependence on the
correlation of the targets' innovations, and the fine-regime leading
order for two instruments are not treated. Parts (iii)-(iv) assume the
ETF optimizer interior: an ETF at zero can carry an edge beyond (122),
but not beyond (121). A binding budget and several funds, whose bands
then couple through the Schur complement of the fund block, are not
treated either.

Propositions 4-8 compared ETF-only actions with active ones in the
one-quarter model, one fund at a time. The last result prices the
ETF-only restriction at one review with \(N\) funds, as a function of
the inputs, and separates it from the frozen-funds baseline.

**Proposition 39 (The cost of the ETF-only restriction in the inputs: the value of the forgone fund purchases, with the frozen-funds baseline adding the forgone sales; learning-driven tracking model at one review; machine checked, with the multiplier test in (i) conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Fix one review as in Proposition 35, with \(N\) funds, \(v_i=\Sigma_{A,ii}+P^\alpha_{ii}\),
rates \(\kappa^\pm_i\), caps \(\bar x_i\) and incumbents \(x^-_i\in[0,\bar x_i]\). Compare three
action classes: full trading \(F\) with value \(J\); ETF-only with funds
that may be sold but not bought, \(E^-\), with value \(J^-\); and ETF-only
with funds frozen, \(E^0\), with value \(J^0\). The *cost of the ETF-only
restriction* is \(C^-=J-J^-\), and the *frozen-funds cost* is \(C^0=J-J^0\). For
each fund let \(\psi_i(a)=\hat\alpha_ia-\frac\gamma2v_ia^2-\kappa^+_i(a-x^-_i)^+-\kappa^-_i(x^-_i-a)^+\), and
define the *purchase excess* and *sale excess*

$$
p_i=\hat\alpha_i-\kappa^+_i-\gamma v_ix^-_i,\qquad s_i=\gamma v_ix^-_i-\hat\alpha_i-\kappa^-_i:\tag{125}
$$

net alpha over the purchase rate plus the risk charge on the incumbent,
and the reverse over the sale rate. At most one of them is positive.

(i) *Structure, for any inputs.* \(J^0\leq J^-\leq J\) and
\(C^0=C^-+(J^--J^0)\). \(C^-=0\) exactly when no fund is bought at the joint
optimum, and \(C^0=0\) exactly when no fund is traded there. Conditional
on the polyhedral Karush-Kuhn-Tucker theorem (`rockafellar1970convex`,
Theorems 27.4 and 28.2-28.3, cited by theorem number as a textbook
result), the latter holds exactly when a multiplier test on the funds'
marginals passes at the ETF-only optimum. \(J^--J^0\), the value of the
permitted fund sales, is zero exactly when no fund is sold at the \(E^-\)
optimum. The restriction costs exactly the value of the purchases it
forbids.

(ii) *Spanning frictionless ETFs.* With \(M=K\), \(B^E\) invertible,
frictionless residual-free fee-free ETFs, and the budget and every ETF
bound slack at the three optima,

$$
C^-=\sum_{i:\,p_i>0}\frac{p_i^2}{2\gamma v_i},\qquad
J^--J^0=\sum_{i:\,s_i>0}\frac{s_i^2}{2\gamma v_i},\tag{126}
$$

where a fund whose purchase edge \((\hat\alpha_i-\kappa^+_i)/(\gamma v_i)\) lies above its cap
contributes \(\psi_i(\bar x_i)-\psi_i(x^-_i)\) instead, and a fund whose sale edge lies
below zero contributes \(\psi_i(0)-\psi_i(x^-_i)\). So the restriction costs, for
each fund it would have bought, the squared purchase excess over twice
the fund's curvature \(\gamma v_i\). Premium beliefs, their precision, the
loadings and the ETF sleeve do not enter, and alpha precision enters
only through \(v_i\). From zero incumbents, with no cap binding,
\(C^-=\sum_i[(\hat\alpha_i-\kappa^+_i)^+]^2/(2\gamma v_i)\) and \(J^-=J^0\): the frozen baseline then agrees
with the restriction proper.

(iii) *One unreachable fund.* If, as in Proposition 35 (ii), exactly one
fund has a loading outside the ETFs' reach and everything else is
frictionless, (126) holds with that fund's reduced moments \(\alpha^{\rm red}_i\) and
\(s^{\rm red}_i\) in place of \(\hat\alpha_i\) and \(v_i\). A missing exposure raises the cost by
the unreachable premium net of its hedge, credited to the fund's
alpha, and lowers it through the unhedgeable variance.

(iv) *ETF frictions: a bracket through the re-hedge costs.* With
spanning ETFs that carry rates and fees but no residual risk, a slack
budget, and room at the three optima for the netting trades and their
cash, let \(r_i=R^\top B^{A\top}_i\) be fund \(i\)'s netting vector, \(h^+_i\) and \(h^-_i\)
the ETF cost of netting a unit purchase and a unit sale, and
\(A^0_i=\hat\alpha_i+r_i^\top c^E-\gamma v_ix^-_i\) the fund's reduced marginal at the incumbent.
With

$$
g_i(m,d)=\max_{0\leq\delta\leq d}\Bigl[m\delta-\frac{\gamma v_i}2\delta^2\Bigr],\tag{127}
$$

$$
\begin{aligned}
\textstyle\sum_ig_i(A^0_i-\kappa^+_i-h^+_i,\bar x_i-x^-_i)&\leq C^-\leq\textstyle\sum_ig_i(A^0_i-\kappa^+_i+h^-_i,\bar x_i-x^-_i),\\
\textstyle\sum_ig_i(-A^0_i-\kappa^-_i-h^-_i,x^-_i)&\leq J^--J^0\leq\textstyle\sum_ig_i(-A^0_i-\kappa^-_i+h^+_i,x^-_i).
\end{aligned}\tag{128}
$$

ETF frictions enter the restriction's cost only through the fee credit
\(r_i^\top c^E\) and an effective purchase rate between \(\kappa^+_i-h^-_i\) and \(\kappa^+_i+h^+_i\).

Part (i) follows from the nesting \(E^0\subseteq E^-\subseteq F\) and the uniqueness of
each class's optimum. For (ii), in exposure-and-fund coordinates the
three classes differ only in each fund's interval, \([0,\bar x_i]\), \([0,x^-_i]\)
or \(\{x^-_i\}\), and the exposure part is maximized at the same point in
all three. Each \(\psi_i\) is concave with its kink at \(x^-_i\); for a bought fund
the gain from the incumbent to the purchase edge is
\(\frac{\gamma v_i}2(\text{edge}-x^-_i)^2=p_i^2/(2\gamma v_i)\). Part (iii) is the same computation
after Proposition 35's reduction to one variable, which constrains
only fund coordinates. For (iv), from each class's optimum a fund move
with its netting trade leaves the exposure unchanged, and the ETF cost
of a combined netting is at most the sum of the unit costs by
subadditivity.

Part (ii) is the Treynor-Black logic of valuing an active position by
its own alpha and residual variance (`treynor1973security`, p. 67 and
equations (13) and (16), full text reviewed), net of the purchase rate
and the incumbent's risk charge, and summed over the funds a
restriction forbids. Earlier numerical comparisons reported the
ETF-only gap at fixed inputs; (i) shows that a baseline with
frozen funds measures \(C^0\), which adds the value of selling the
incumbents it assumes, and the restriction proper does not forbid
those sales.

The result is for one review. The multi-review cost, ETF residual risk
in (iv), an ETF at zero that cannot be sold to net a purchase, several
unreachable funds, and the pooled prior's coupling of the \(v_i\) are not
treated. No magnitude is claimed.

Propositions 35 and 39 kept every ETF strictly inside its bounds. The
last result drops that assumption for the two-stage procedures of
Propositions 22 and 23: when some ETFs sit at zero, when is each
procedure exact, and what does the target-confined one lose?

**Proposition 40 (Two-stage exactness with ETFs at zero: stage 1's one-sided slacks are the joint multipliers, the one-fund fibre interval, and the soft procedure; learning-driven tracking model at one review, spanning frictionless ETFs without fees; machine checked, with the reduction to ETF coordinates at paper level).**
Fix one review as in Proposition 39 (ii), with fees off, no ETF caps,
a slack budget and a fund box \(0\leq x^A\leq\bar x^A\). In ETF coordinates, let
\(Q=R^\top B^{A\top}\) be the netting matrix with columns \(r_i\), \(w=x^E+Qx^A\) the
exposure, \(\mu_E=B^E\hat\lambda\), \(\Sigma_{EE}=B^E\tilde\Sigma_fB^{E\top}\) and
\(G_E(w)=\mu_E^\top w-\frac\gamma2w^\top\Sigma_{EE}w\); nonnegative ETFs mean \(w\geq Qx^A\). Let
\(H(x^A)=\hat\alpha^\top x^A-\frac\gamma2x^{A\top}Vx^A-C_A(x^A-x^{A-})\) be the funds' part, \(w_{\rm TB}=(\gamma\Sigma_{EE})^{-1}\mu_E\)
the factor Markowitz exposure, \(V_E(q)=\max\{G_E(w):w\geq q\}\), and
\(W_F=\{w:w\geq Qx^A\text{ for some }x^A\text{ in the box}\}\). The joint problem
maximizes \(G_E(w)+H(x^A)\) over \(w\geq Qx^A\), with value \(J\) and holding \(x_J\).
The *target-confined* procedure (Proposition 23) takes stage 1's
exposure \(w^*=\arg\max_{W_F}G_E\), then maximizes \(H\) over the fibre
\(\{x^A:Qx^A\leq w^*\}\) at \(x_2\), with value \(T\) and loss \(\Lambda=J-T\). *Stage 1's
slacks* are \(\zeta^*=\gamma\Sigma_{EE}w^*-\mu_E\).

(i) *Stage 1's slacks are the joint multipliers.* \(\zeta^*\geq0\), and
\(\zeta^*_j=0\) wherever \(w^*_j>(Qx_2)_j\). The procedure is exact, \(T=J\), exactly
when every fund's marginal at stage 1's prices,

$$
g_i=\hat\alpha_i-\gamma(Vx_2)_i-r_i^\top\zeta^*,\tag{129}
$$

equals \(\kappa^+_i\) where \(x_2\) buys, \(-\kappa^-_i\) where it sells, and lies in
\([-\kappa^-_i,\kappa^+_i]\) where it holds, with the one-sided forms at the box
bounds. Stage 1 never sees the funds, yet its one-sided marginals at
the ETFs at zero are the prices the joint optimum puts on the funds'
by-product there. For any number of funds, \(V_E(Qx_2)=G_E(w^*)\): stage 1's
exposure is already optimal for stage 2's by-product, so the loss has
no exposure-misfit part.

(ii) *One fund: the fibre interval.* With one fund and netting vector
\(r\), stage 2 sees the interval

$$
[x_{\rm lo},x_{\rm hi}]=\Bigl[\max\Bigl(0,\max_{j:\,r_j<0}\frac{w^*_j}{r_j}\Bigr),\
\min\Bigl(\bar x,\min_{j:\,r_j>0}\frac{w^*_j}{r_j}\Bigr)\Bigr],\tag{130}
$$

and holds the fund at \(x_2=\mathrm{clip}(x_f,x_{\rm lo},x_{\rm hi})\), with \(x_f\) the
frictionless band holding of Proposition 35 (107) at spanning moments.
An ETF at zero that a purchase would sell caps the fund from above,
and one that a sale would sell floors it from below. With
\(\Phi(x)=H(x)+V_E(rx)\),

$$
T=J\iff x_J\in[x_{\rm lo},x_{\rm hi}],\qquad \Lambda=\Phi(x_J)-\Phi(x_2)\geq0:\tag{131}
$$

the loss is the fund's misplacement in the joint objective, zero
exactly when the joint holding lies in the room stage 1 leaves.

(iii) *The soft procedure.* If stage 1's set contains \(w_{\rm TB}\), in
particular if stage 1 is unconstrained, Proposition 22's multiplier
\(\nu_E\) is zero and the soft procedure is exact, with ETFs at zero or not.
If stage 1 is confined to \(W_F\), the procedure is exact when \(w_{\rm TB}\in W_F\),
that is, when some fund holding's by-product lies below \(w_{\rm TB}\) in every
ETF coordinate; for one fund, when (130) evaluated at \(w_{\rm TB}\) is nonempty
and \(w_{{\rm TB},j}\geq0\) wherever \(r_j=0\). Otherwise \(\nu_E\neq0\) lies in the normal
cone of \(W_F\) at \(w^*\), the soft loss satisfies \(0\leq\Lambda_s\leq\nu_E^\top(w_J-w_2)\) with
\(w_2\) stage 2's exposure, and \(\Lambda_s=0\) exactly when the joint optimum also
solves the \(\nu_E\)-tilted stage 2. A nonzero multiplier need not cost
anything: when the fund sits at a box bound in both problems and
every ETF direction with a nonzero multiplier sits at the funds'
by-product, at zero, in both, the tilted stage 2 can return the joint
optimum.

For (i), \(W_F\) is closed upward, so moving \(w^*\) up in any coordinate
cannot help stage 1; that gives \(\zeta^*\geq0\). The set \(\{w\geq Qx_2\}\) lies inside
\(W_F\) and contains \(w^*\), which gives complementarity and \(V_E(Qx_2)=G_E(w^*)\).
The joint problem's optimum and multiplier are unique, so exactness
is the fund lines at \(\zeta^*\). In (ii), \(V_E(rx)=G_E(w^*)\) on the whole fibre
interval, so the joint holding, if it lies there, maximizes \(H\) on it.
Part (iii) applies Propositions 22 and 23 with the ETF bound as part
of the feasible set. The first-order facts are proved by difference
quotients, without a Karush-Kuhn-Tucker citation.

Dropping the ETFs at zero from the menu would turn the fund's
by-product in their directions into an unreachable exposure, as in
Proposition 35 (ii). Stage 1 here keeps those ETFs available upward,
so its exposure is not the reduced-menu one, and the exactness
condition reads on stage 1's own slacks. In Jagannathan and Ma's terms
(Section 4) the slacks are the binding bounds' multipliers; here the
exposure stage computes them without seeing the funds.

Fees, ETF frictions, ETF caps and a binding budget are not treated,
nor are an explicit form of stage 1's implied fund holdings for
several funds, bounds on \(\Phi(x_J)-\Phi(x_2)\) in the inputs, and the soft
loss beyond the multiplier bound.

Proposition 40 kept the other ETFs frictionless, fees off and the
budget slack. The last result puts all of these back: some ETFs at
zero, the others costly, fees on and a budget that may bind.

**Proposition 41 (The fund decision and two-stage exactness with ETFs at zero, costly ETFs, fees and a binding budget; learning-driven tracking model at one review, spanning ETFs; machine checked, with the joint criterion in (i) and the exactness criterion in (iv) conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Fix one review with spanning ETFs (\(M=K\), \(B^E\) invertible, netting
matrix \(Q\) with columns \(r_i\)), fees \(c^E\), ETF rates \(\kappa^\pm_{E,j}\), ETF residual
covariance \(\Sigma_E\), the zero bound \(x^E\geq0\) and no ETF caps, a fund box, and
the funded budget \(k(x)\geq0\) with multiplier \(\eta\geq0\). Let
\(\mu_E=B^E\hat\lambda-c^E\), \(\Sigma_{EE}=B^E\tilde\Sigma_fB^{E\top}\), \(\tilde\alpha=\hat\alpha+Q^\top c^E\), \(w=x^E+Qx^A\), \(g\) the
smooth marginal of every instrument, and
\(A_i=\tilde\alpha_i-\gamma(Vx^A)_i+\gamma r_i^\top\Sigma_Ex^E\) the fund's reduced marginal, so that
\(g_i=A_i+r_i^\top g_E\). Trading slopes \(t\) lie in the trade-sign sets.

(i) *The joint criterion.* A feasible \(x\) is the optimum exactly when
there are \(\eta\), slopes \(t\) and slacks \(\zeta_j\geq0\), zero unless ETF \(j\) is at
zero, such that

$$
g_j=\eta+(1+\eta)t_j-\zeta_j,\qquad
A_i+r_i^\top\bigl(\eta\mathbf1+(1+\eta)t_E\bigr)-\sum_{j\text{ at zero}}r_{ij}\zeta_j=\eta+(1+\eta)t_i,\tag{132}
$$

for every ETF \(j\) and every fund \(i\), with the box signs on the funds and
\(\eta k(x)=0\). This composes the earlier one-sided and friction criteria
and adds nothing to them: the idle ETFs' slopes and the at-zero slacks
are tied to the state, not given.

(ii) *Explicit forms given the ETFs' statuses* (\(\Sigma_E=0\)). Split the ETFs
at the optimum into *traded* ones \(T\) (bought or sold, slope pinned),
with pinned marginals \(\pi_T=\eta\mathbf1+(1+\eta)t_T\), and *fixed* ones \(F\) (at zero,
or idle at a positive incumbent, holding known). With the hedged
blocks of \(\Sigma_{EE}\) and the *effective netting weights*

$$
\mu_{F\cdot T}=\mu_F-\Sigma_{FT}\Sigma_{TT}^{-1}\mu_T,\quad
\Sigma_{FF\cdot T}=\Sigma_{FF}-\Sigma_{FT}\Sigma_{TT}^{-1}\Sigma_{TF},\quad
\rho_{iT}=r_{iT}+\Sigma_{TT}^{-1}\Sigma_{TF}r_{iF},\tag{133}
$$

and \(w_F=Q_Fx^A+x_F\) the exposure held in the fixed directions, the traded
exposure is \(w_T=\Sigma_{TT}^{-1}[(\mu_T-\pi_T)/\gamma-\Sigma_{TF}w_F]\), the fixed ETFs' marginals are
\(g_F=\mu_{F\cdot T}+\Sigma_{FT}\Sigma_{TT}^{-1}\pi_T-\gamma\Sigma_{FF\cdot T}w_F\), which gives each at-zero slack and
each idle band, and every fund's marginal is

$$
g_i=\alpha^{F,T}_i-\gamma(V^{F,T}x^A)_i,\qquad
\alpha^{F,T}_i=\tilde\alpha_i+r_{iF}^\top\mu_{F\cdot T}-\gamma r_{iF}^\top\Sigma_{FF\cdot T}x_F+\rho_{iT}^\top\pi_T,\qquad
V^{F,T}=V+Q_F^\top\Sigma_{FF\cdot T}Q_F.\tag{134}
$$

The fund line then reads

$$
\alpha^{F,T}_i-\rho_{iT}^\top\pi_T-\gamma(V^{F,T}x^A)_i+(1+\eta)\rho_{iT}^\top t_T-\eta(1-\rho_{iT}^\top\mathbf1)=(1+\eta)t_i.\tag{135}
$$

So a fund's by-product in every fixed direction, at zero or idle
alike, earns those directions' hedged premium and pays their hedged
risk charge, and the funds interact through \(V^{F,T}\). The traded ETFs'
pinned slopes enter at \(\rho_{iT}\), which adds to the fund's own netting
weight the traded ETFs' hedge of its fixed-direction by-product, and
the shadow price \(\eta\) is charged on \(1-\rho_{iT}^\top\mathbf1\), the net cash of a unit
netted through the traded ETFs only. Selling a correlated traded ETF
raises an at-zero ETF's slack and buying one lowers it. With no ETF
fixed, this is the pinned-slope threshold with the cash shift
\(\eta(1-\sum_jr_{ij})\); with none traded, it is the fund-alone form with the
idle holdings added to the by-product. For an ETF starting at zero,
with threshold \(\eta+(1+\eta)\kappa^+_{E,j}\), being at zero implies \(g_j\) at most the
threshold, being bought implies equality, and \(g_j\) below it implies
being at zero; the ETF stays at zero exactly when \(g_j+\gamma\Sigma_{jj}x^E_j\) is at
most the threshold. Over the traded ETFs' sign sets,
\((1+\eta)\rho_{iT}^\top t_T\) ranges over an interval given by the re-hedge costs
computed with \(\rho_{iT}\).

(iii) *One fund and one ETF.* With netting weight \(r\), ETF variance \(\sigma_{EE}\),
fund holding \(a\) and ETF holding \(p\), each line with the fund's box signs:

$$
\begin{aligned}
&\text{ETF at zero from }p^-=0\iff\mu_E-\gamma\sigma_{EE}ra\leq\eta+(1+\eta)\kappa^+_E,\\
&\text{ETF traded: }\tilde\alpha+r(\eta+(1+\eta)t_E)-\gamma va=\eta+(1+\eta)t_A,\\
&\text{ETF fixed: }\tilde\alpha+r\mu_E-\gamma(v+r^2\sigma_{EE})a-\gamma r\sigma_{EE}p=\eta+(1+\eta)t_A.
\end{aligned}\tag{136}
$$

A traded ETF leaves the fund its own curvature and a net cash of \(1-r\)
per netted unit; a fixed one gives it the fund-alone curvature, the
ETF's full premium at weight \(r\) and the full cash of its unit.

(iv) *Two-stage exactness with everything on.* Take Proposition 40's
target-confined stage 1 (fees in \(\mu_E\); no ETF rates, residuals or
budget) with slacks \(\zeta^*\), and a stage 2 that keeps every friction and
the budget on the fibre, at \(x_2\). The procedure is exact exactly when
the criterion (132) holds at \(x_2\); there the fund marginals are
\(\tilde\alpha_i-\gamma(Vx^A_2)_i-r_i^\top\zeta^*\), the residual terms cancelling. With \(\Sigma_E=0\), an
ETF ending interior at \(x_2\) has \(\zeta^*_j=0\), so its line reads
\(0=\eta+(1+\eta)t_j\). Exactness therefore needs every ETF bought and ending
interior to be free with a slack budget, every ETF sold to an interior
holding to satisfy \((1+\eta)\kappa^-_{E,j}=\eta\), a coincidence of the inputs, and
every untraded interior ETF to have \(\kappa^-_{E,j}\geq\eta/(1+\eta)\). A sale to zero
needs only \(-\zeta^*_j\leq\eta-(1+\eta)\kappa^-_{E,j}\), which holds on a set of inputs of
positive measure. So the procedure is generically inexact whenever
it trades an ETF that ends interior. The soft procedure with an
unconstrained stage 1 stays exact with every friction and the budget
on. With stage 1 confined to the reachable exposures,
\(0\leq\Lambda_s\leq\zeta^{*\top}(w_{s2}-w_J)\), with \(w_{s2}\) stage 2's exposure, and it is exact
exactly when the joint optimum solves the \(\zeta^*\)-tilted stage 2.

The proof of (i) is the Karush-Kuhn-Tucker condition of the lifted
polyhedral problem with the identity \(g_i=A_i+r_i^\top g_E\) substituted. For
(ii), the traded ETFs' lines \(g_T=\pi_T\) are solved for \(w_T\) and substituted
into the fixed rows and the fund marginals: a block elimination given
the statuses. Since \(\Sigma_{FF\cdot T}\) is a Schur complement of a positive
definite matrix, the fund problem given the statuses stays strictly
concave. For (iv), \(x_2\) is feasible for the joint problem, so it is
exact exactly when it is the unique joint optimum; stage 1's
complementarity gives \(\zeta^*_j=0\) at every ETF interior at \(x_2\). The soft
stage 2 differs from the joint problem by \(\nu_E^\top w\), as in Proposition 22.

In the terms of Jagannathan and Ma (Section 4), \(V^{F,T}\) is the
status-wise fold-in of the fixed ETFs into the funds' covariance, here
over idle ETFs as well as those at zero, and with the traded ETFs'
costs pinned. Without cross covariance between traded and fixed ETFs,
\(\rho_{iT}=r_{iT}\) and nothing interacts.

The explicit forms take \(\Sigma_E=0\). ETF caps, a stage 1 that sees costs or
the budget, bounds on the target-confined loss in the inputs, and the
coincidence events in (iv) are not treated. With several ETFs, the
statuses are decided by a finite complementarity problem, not in
closed form. No magnitude is claimed.

Propositions 26 and 38 bound quarterly bands exactly but leave the
fine regime, where the target's quarterly step is small against the
band, to leading-order asymptotics. The last result gives that leading
order for a fund beside one costly ETF, at its two ends and in the
weight between them.

**Proposition 42 (A fund's fine-regime band beside one costly ETF: an error coordinate, three exact reductions, the cited cube-root law at each end, and one dimensionless weight between; learning-driven tracking model with a slack budget, one fund and one ETF; machine checked in its algebra and reductions, with the cube-root law resting on the cited corrector solution and the limits between the ends as readings).**
Fix Proposition 38's setting with one fund \(a\) and one ETF
\(b\), rates \(\kappa^\pm_A\) and \(\kappa^\pm_E\), risk correlation \(r_c\), and targets whose
per-review innovations have variances \(v_A\), \(v_B\) and correlation \(r\). Let
\(y_a=a-a^*\), \(y_b=b-b^*\), \(\rho_h=\Sigma_{AE}/\Sigma_{EE}\) the hedge ratio, \(\rho'=\Sigma_{AE}/\Sigma_{AA}\),
\(c^{\rm res}=\gamma\Sigma_{AA}(1-r_c^2)\), and

$$
v^{\rm idle}=v_A+\rho'^2v_B+2\rho'r\sqrt{v_Av_B},\qquad
v_B^{\rm eff}=v_B+\rho_h^2v_A+2\rho_hr\sqrt{v_Av_B},\tag{137}
$$

the innovation variances of \(a^*+\rho'b^*\), the fund's effective target when
the ETF is frozen, and of \(b^*+\rho_ha^*\), the ETF's effective target when it
hedges the fund.

(i) *The error coordinate.* With \(e=y_b+\rho_hy_a\), the ETF's tracking error
against the position that hedges the fund,

$$
\frac\gamma2(y_a,y_b)\Sigma(y_a,y_b)^\top=\frac{c^{\rm res}}2y_a^2+\frac{\gamma\Sigma_{EE}}2e^2.\tag{138}
$$

A fund trade moves \((y_a,e)\) along \((1,\rho_h)\), an ETF trade moves \(e\) alone,
and the innovations of \((y_a,e)\) have variances \(v_A\) and \(v_B^{\rm eff}\). The
ETF's cost reaches the fund only through \(e\).

(ii) *Three exact reductions.* (a) If \(\Sigma_{AE}=0\) at every review and
state, the value is the sum of two one-instrument values, and the fund's
band is its own one-instrument band with curvature \(\gamma\Sigma_{AA}\), whatever
the targets' innovation correlation or the ETF's rates. (b) With a
frictionless ETF, the fund's problem is the one-instrument problem
with curvature \(c^{\rm res}\) and innovation variance \(v_A\) (Proposition 38 (vi)).
(c) With the ETF frozen at \(b\), by prohibitive rates in both directions
or a pinned box, the fund's problem is the one-instrument problem with
curvature \(\gamma\Sigma_{AA}\), target \(a^*+\rho'(b^*-b)\) and innovation variance \(v^{\rm idle}\).

(iii) *The cube-root law at each end.* For tracking a Brownian target of
variance \(v\) per unit time with holding cost \(\frac c2y^2\) and rates \(\kappa^\pm\), the
first corrector problem's no-trade band is \([-\Delta,\Delta]\), centred on the
target whatever the split of the rates, with

$$
\Delta^3=\frac{3(\kappa^++\kappa^-)v}{4c},\qquad\text{average cost }\frac{c\Delta^2}2\tag{139}
$$

(`soner2013homogenization`, equations (4.3)-(4.5), read at the level of
its displayed formulas; `muhlekarbe2017primer`, Section 4, full text
reviewed). Each reduction in (ii) meets its hypotheses, so the fund's
fine-regime half-width is \(\Delta_0\) with \((c,v)=(\gamma\Sigma_{AA},v_A)\) for
uncorrelated risks, \(\Delta_{\rm free}\) with \((c^{\rm res},v_A)\) for a frictionless ETF, and
\(\Delta_{\rm frozen}\) with \((\gamma\Sigma_{AA},v^{\rm idle})\) for a frozen one. Their ratio,
\(\Delta_{\rm frozen}^3/\Delta_{\rm free}^3=(1-r_c^2)v^{\rm idle}/v_A\), can lie on either side of one.

(iv) *One weight between the ends.* With both instruments costly, the
fine-regime problem is a two-dimensional ergodic problem in \((y_a,e)\).
Scaled by \(\Delta_{\rm free}\) and by the ETF's own scale
\(\Delta_E^3=3(\kappa^+_E+\kappa^-_E)v_B^{\rm eff}/(4\gamma\Sigma_{EE})\), it depends on the rates only
through

$$
\xi^3=\frac{\Delta_E^3}{\Delta_{\rm free}^3}
=\frac{\kappa^+_E+\kappa^-_E}{\kappa^+_A+\kappa^-_A}\cdot\frac{v_B^{\rm eff}}{v_A}\cdot\frac{c^{\rm res}}{\gamma\Sigma_{EE}},\tag{140}
$$

together with the correlations, the variance and curvature ratios, and
the cost asymmetries. The fund's half-width is \(\Delta_{\rm free}F(\xi,\dots)\), with
\(F=1\) exactly at \(r_c=0\). *As a reading*, if the problem's cross-section is
continuous at the ends of \(\xi\) and its pushing set has measure zero,
then \(F\to1\) as \(\xi\to0\), \(F\to\Delta_{\rm frozen}/\Delta_{\rm free}\) as \(\xi\to\infty\), and the ETF's
idle probability, which tends to one at every \(\xi\), is not the weight;
\(\xi\) is. At basis-point ETF rates and quarterly target moves of about a
percent, the ETF is not in its fine regime at all, so the relevant
pairing is a fine fund beside a coarse ETF, whose leading order is (b)
perturbed by an error bounded by the ETF's static half-width (also a
reading).

Part (i) completes the square in \(y_a\) with \(\rho_h\). Part (ii) (a) holds
because the objective is a sum with separate controls and no shared
constraint, (b) is Proposition 38 (vi), and (c) completes the square
with \(\rho'\) at fixed \(b\). In (iii), the quartic corrector
\(w(y)=-\frac c{12v}y^4+\frac{\lambda}vy^2+\frac{\kappa^--\kappa^+}2y\) with \(\lambda=c\Delta^2/2\) satisfies
\(\frac v2w''+\frac c2y^2=\lambda\) on the band, has \(w''=0\), \(w'(-\Delta)=-\kappa^+\) and \(w'(\Delta)=\kappa^-\) at its
edges exactly when (139) holds, and keeps \(-\kappa^+\leq w'\leq\kappa^-\) on the band and
\(\frac c2y^2\geq\lambda\) off it: the rate asymmetry enters only the odd term, so
the band does not shift. Part (iv)'s \(\xi\) is dimensional analysis.

The one-instrument law is the sources'; what is added is the error
coordinate that makes the pair's loss diagonal, the three exact ends
in one frame, and \(\xi\) as the weight. The two-dimensional corrector
problem is the multidimensional object of `possamai2015homogenization`,
whose no-trade region has no explicit solution beyond one dimension
(read at the level of its abstract and introduction). The identification of the
quarterly fine-regime band with the corrector's half-width is cited,
not shown, as for Proposition 26. \(F\) between the ends, its end limits
as theorems, several ETFs, and the fine-fund coarse-ETF pairing as a
theorem are not treated.

Proposition 38 bounded a fund's band beside one ETF at each ETF
incumbent. The last result gives how that band, and the ETF's, move
with the other instrument's holding: exactly at the last review, and
monotonically at every review.

**Proposition 43 (The shape of the bundling band: median edges at the last review, monotone edges at every review, and the frozen-ETF band; learning-driven tracking model with a slack budget, one fund and one ETF; machine checked, with the monotonicity in (ii) conditional on Topkis's lattice theorems and its nonpositive-covariance case at paper level).**
Fix Proposition 38's setting with one fund and one ETF, finite caps
and gross returns \(g'>0\). Let \(\rho=\Sigma_{AE}/\Sigma_{EE}\), \(\rho_A=\Sigma_{AE}/\Sigma_{AA}\), and let
\(c^{\rm res}=\gamma\Sigma_{AA}(1-\mathrm{corr}^2)\) and \(c^{\rm res}_E=\gamma\Sigma_{EE}(1-\mathrm{corr}^2)\) be the two
residual curvatures. The fund's band \([lo_t,hi_t]\) at ETF incumbent \(p^-\) is
Proposition 38's effective band; the ETF's band given a fund holding \(a\)
is Proposition 26's band for \(p\mapsto G_t((a,p),z)\); and \(NT_t\) is the set of
holdings from which nothing trades.

(i) *The last review: median edges.* At \(T-1\), for every ETF incumbent
at which the ETF optimizer at the fund's edge is strictly inside the
ETF box, each fund edge is the median of its *bought level*, its *idle
line* and its *sold level*, clipped to \([0,\bar x_A]\):

$$
\begin{aligned}
lo_{T-1}(p^-)&=\mathrm{med}\Bigl(a^*-\frac{\kappa^+_A-\rho\kappa^+_E}{c^{\rm res}},\ a^*-\rho_A(p^--p^*)-\frac{\kappa^+_A}{\gamma\Sigma_{AA}},\ a^*-\frac{\kappa^+_A+\rho\kappa^-_E}{c^{\rm res}}\Bigr),\\
hi_{T-1}(p^-)&=\mathrm{med}\Bigl(a^*+\frac{\kappa^-_A+\rho\kappa^+_E}{c^{\rm res}},\ a^*-\rho_A(p^--p^*)+\frac{\kappa^-_A}{\gamma\Sigma_{AA}},\ a^*+\frac{\kappa^-_A-\rho\kappa^-_E}{c^{\rm res}}\Bigr).
\end{aligned}\tag{141}
$$

For \(\Sigma_{AE}>0\), each edge is continuous and nonincreasing in \(p^-\): flat
at its bought level while the ETF is bought at that edge, falling along
the idle line at slope \(-\rho_A\), and flat at its sold level beyond. The
idle segment has length

$$
\frac{\kappa^+_E+\kappa^-_E}{c^{\rm res}_E}\tag{142}
$$

in the ETF incumbent, the ETF's own residual static width. So the
fund's edge moves with the ETF's holding only while the ETF is idle at
that edge. For \(\Sigma_{AE}<0\) the picture mirrors, and for \(\Sigma_{AE}=0\) the three
levels coincide. The width is the residual ceiling (121) on two bought
or two sold levels, the fund-alone width on the idle lines, and the
ceiling minus the leak with the lower edge bought and the upper sold,
as in Proposition 38 (iv), now read off \(p^-\). The last-review region
is Proposition 26 (v)'s static parallelotope.

(ii) *Every review: monotone edges and a two-band region.* If \(\Sigma_{AE}\geq0\)
at every review and state, then \(V_t\) has increasing differences in the
two holdings, and so do \(G_t\) and the ETF-optimized value in \((a,p^-)\).
Hence both fund edges are nonincreasing in the ETF incumbent and both
ETF edges are nonincreasing in the fund holding, at every review,
whatever the rates, the horizon or the innovation law, and

$$
NT_t=\bigl\{(a,p):lo_t(p)\leq a\leq hi_t(p),\ lo^E_t(a)\leq p\leq hi^E_t(a)\bigr\},\tag{143}
$$

the intersection of two bands with monotone edges, inside Proposition
38's parallelotope (124). With \(\Sigma_{AE}\leq0\) everywhere the directions
reverse, and with \(\Sigma_{AE}=0\) no edge depends on the other holding.

(iii) *A frozen ETF.* If the ETF cannot trade and sits at \(p_0\), under
pure-learning marking the fund's problem at every review is the
one-instrument problem with curvature \(\gamma\Sigma_{AA}\), the fund's rates and cap,
and the *idle target* \(a^*_t-\rho_{A,t}(p_0-p^*_t)\), so Proposition 26 applies to it.
With constant covariance, the idle target's innovation has variance
\(v^{\rm idle}\) of (137), increasing in the targets' innovation correlation when
\(\rho_A>0\). The correlation enters the frozen-ETF band only through the
law of the idle target's innovation, whose variance is \(v^{\rm idle}\); it
enters through \(v^{\rm idle}\) alone when that law is fixed by its variance,
as for Gaussian innovations or in the fine-regime reading. With a
frictionless ETF it does not enter at all (Proposition 38 (vi)).

(iv) *The last review is free of the innovation law.* Two instances that
agree at the last review on the premia, the covariance, \(\gamma\), the rates
and the caps have the same last-review bands and region, whatever
their outcome laws. At earlier reviews the innovation law enters only
through the continuation.

For (i), the ETF's optimizer at fund holding \(a\) is a median of its own
band edges and \(p^-\), the ETF-optimized value is differentiable with
derivative \(\partial G/\partial a\) at that optimizer, and a monotone affine map sends
a median to a median. So the value's derivative is a median of three
strictly increasing affine functions, and its root is the median of
their roots. For (ii), in coordinates with the fund's holding negated,
the review's minimand is a sum of terms each with decreasing
differences in a pair of coordinates, hence submodular, and
submodularity survives partial minimization over a product of
intervals (`topkis1978minimizing`, Theorems 3.1, 3.2 and 4.3, read at
the level of the theorems); backward induction carries it through the
tree, and increasing differences move the one-sided derivatives, and
hence the edges, monotonically. Part (iii) completes the square at
fixed \(p_0\).

The small-cost literature gives the leading-order multi-asset region
from a corrector equation (Section 4). With independent assets every
boundary is flat in the other holdings (`liu2013portfolio`, full text
reviewed), which is the \(\Sigma_{AE}=0\) case of (ii). Here the bend in (i) is exact
at a finite cost, and its length is the other instrument's residual
static width.

How the targets' innovation correlation moves the band at reviews
before the last is not claimed. Experiments suggest a mixture of the
idle and re-hedging variances weighted by the future idle share, which
is a conjecture. A bound on the edges' slope in the ETF incumbent, the
ETF at a bound in (i), several ETFs in (ii), general marking in (iii),
and a binding budget are not treated.

Propositions 35-43 took the one-review fund decision as known. The
last result states it: when a fund is held, bought or sold, against
adjusting exposure through ETFs, at one review of the learning-driven
tracking model.

**Proposition 44 (The fund's hold, buy and sell criterion at one review: exact in general, explicit under frictionless spanning ETFs, bracketed by the re-hedge cost otherwise, with the budget, the bounds and several reviews; learning-driven tracking model; machine checked, with the multiplier criterion and the parts built on it conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Fix one review with \(N\) funds and \(M\) ETFs, predictive moments \(\mu\) and
\(\Sigma\) as in Proposition 35, rates \(\kappa^\pm_i\in[0,1)\), caps \(0\leq x\leq\bar x\),
pre-trade holdings \(x^-\) and cash \(h^-\), and funded cash
\(k(x)=h^--\mathbf1^\top(x-x^-)-C(x-x^-)\geq0\). Write \(g(x)=\mu-\gamma\Sigma x\) for the
smooth marginal.

(i) *The exact criterion.* The optimum exists and is unique. A
feasible \(x\) is optimal exactly when there is \(\eta\geq0\) with \(\eta k(x)=0\)
such that each instrument bought in the interior has
\(g_i=\eta+(1+\eta)\kappa^+_i\), each sold in the interior has
\(g_i=\eta-(1+\eta)\kappa^-_i\), and each held has \(g_i\) between the two, with
the one-sided forms at zero and at the cap. The criterion is exact but
implicit, since \(g\) is evaluated at the optimum.

(ii) *Is any fund traded?* With \(x_E\) the optimum over ETFs alone and \(I\)
the shadow prices compatible with it, no fund is traded at the full
optimum exactly when some \(\eta\in I\) puts every fund's marginal at \(x_E\)
in its held band.

(iii) *Frictionless spanning ETFs.* If \(M=K\) with \(B^E\) invertible, ETFs
are frictionless, \(V\) is diagonal with entries \(v_i\), and at the optimum
the budget is slack and every ETF strictly inside its box, then

$$
y^*=(\gamma\tilde\Sigma_f)^{-1}\hat\lambda,\qquad
x_i=\mathrm{clip}\Bigl(x^-_i,\frac{\hat\alpha_i-\kappa^+_i}{\gamma v_i},\frac{\hat\alpha_i+\kappa^-_i}{\gamma v_i}\Bigr)\text{ in }[0,\bar x_i],\qquad
x^E=R^\top(y^*-B^{A\top}x^A).\tag{144}
$$

Fund \(i\) is bought exactly when \(\hat\alpha_i-\gamma v_ix^-_i>\kappa^+_i\) and
\(x^-_i<\bar x_i\), sold exactly when \(\hat\alpha_i-\gamma v_ix^-_i<-\kappa^-_i\) and \(x^-_i>0\),
and held otherwise. Premium beliefs, their precision and the loadings
do not enter the decision.

(iv) *ETF frictions: a bracket.* With spanning, diagonal \(V\), a slack
budget and every ETF strictly inside its box, let the re-hedge costs
\(h^\pm_i\) be as in Proposition 39 (iv) and the reduced marginal be
\(A_i=\hat\alpha_i+r_i^\top c^E-\gamma v_ix_i+\gamma r_i^\top\Sigma_Ex^E\). Then

$$
\text{bought}\Rightarrow A_i\geq\kappa^+_i-h^-_i,\qquad
\text{sold}\Rightarrow A_i\leq-\kappa^-_i+h^+_i,\qquad
\text{held}\Rightarrow-\kappa^-_i-h^-_i\leq A_i\leq\kappa^+_i+h^+_i.\tag{145}
$$

Under the purchase re-hedge an interior purchase has
\(A_i=\kappa^+_i+h^+_i\) (at least that at the cap), and the sale is the
mirror; a held fund can satisfy the same equality, so it is necessary,
not a test. If every ETF the fund's netting uses is traded, the
slopes are pinned and an interior purchase has
\(A_i=\kappa^+_i-\sum_jr_{ij}t_j\). With no ETF residual risk,
\(A_i(x^-)>\kappa^+_i+h^+_i\) forces a purchase and \(A_i(x^-)<-\kappa^-_i-h^-_i\) a sale.

(v) *A binding budget.* The thresholds on \(g_i\) become
\(\eta\pm(1+\eta)\kappa^\pm_i\). On the reduced marginal the shift is
\(\eta(1-\sum_jr_{ij})\), the shadow price on the net cash of a netted unit,
and in (iii) fund \(i\) is bought exactly when

$$
\hat\alpha_i-\gamma v_ix^-_i>\eta\Bigl(1-\sum_jr_{ij}\Bigr)+(1+\eta)\kappa^+_i,\tag{146}
$$

with exposure \(y^*(\eta)=(\gamma\tilde\Sigma_f)^{-1}(\hat\lambda-\eta R\mathbf1)\).

(vi) *Several reviews.* In (iii)'s separated setting with discount \(\beta\)
and pure-learning marking, each fund is a one-instrument problem with
curvature \(c_t=\gamma v_{i,t}\), and

$$
\hat\alpha_{i,t}\leq(1-\beta)\kappa^+_i\Rightarrow\text{no purchase from zero},\qquad
\hat\alpha_{i,t}>\kappa^+_i+\beta\kappa^-_i\Rightarrow\text{a purchase from zero},\tag{147}
$$

with the mirror at the cap, carrying the cap's risk charge
\(c_t\bar x_i\), for sales. Looking ahead lowers the alpha a purchase needs,
because the position persists.

Part (i) is the polyhedral Karush-Kuhn-Tucker theorem applied to the
lifted problem (`rockafellar1970convex`, Theorems 27.4 and 28.2-28.3,
cited by theorem number), with the lifted multipliers eliminated.
Part (iii) solves out the frictionless ETF block. For (iv) and (v), the
identity \(g_i=A_i+r_i^\top g_E\) moves the ETF lines into the fund's, each
ETF's slope lying in its trade-sign set. Part (vi) reads Proposition 26's
edge brackets for each fund's reduced problem.

The fund decision is thus a band in net alpha, of width the round-trip
rate widened by the re-hedge cost, centred at the risk charge on the
current holding. Exposure is adjusted through the ETFs and enters the
fund decision only through the re-hedge cost, the fee credit and, with
a binding budget, the net cash of a netted unit. This is Proposition
9's multiplier condition for \(n\) instruments; Treynor and Black's
separation (`treynor1973security`, p. 67, full text reviewed) is (iii).

ETFs at zero or at their caps, the common long-only case, are
Propositions 40-41's; they are not covered by (iii)-(iv). A binding
budget with ETF frictions is covered by (iv)-(v) only as stated. No
magnitude is claimed.

Propositions 22 and 23 priced two-stage implementation in the
one-quarter model. The last result carries them to one review of the
learning-driven tracking model with several funds and ETFs, and states
in the inputs when each procedure is exact and what it loses.

**Proposition 45 (When two-stage implementation is exact and what it loses, at one review; learning-driven tracking model in the reference case; machine checked, with the joint criterion, the exactness criterion under frictions and the binding-budget case conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Fix one review as in Proposition 44, in the reference case, and split
the objective as \(Q(x)=G(b(x))+H(x)\), with exposure \(b=B^\top x\), factor part
\(G(b)=\hat\lambda^\top b-\frac\gamma2b^\top\tilde\Sigma_fb\) and residual part \(H\) (alpha, fees,
residual risk and costs). Let \(B_F\) be the funded feasible exposures,
\(J\) the joint optimum's value, at exposure \(b_J\). The *target-confined*
procedure (Proposition 23) chooses \(b^*\) maximizing \(G\) over \(B_F\), then
maximizes \(H\) on its fibre at \(x_2\); its loss is \(\Lambda=J-T\). The *soft*
procedure (Proposition 22) chooses \(b^*\) over a convex \(\mathcal R\supseteq B_F\),
with multiplier \(\nu=\hat\lambda-\gamma\tilde\Sigma_fb^*\), and loses \(\Lambda_s\).

(i) *Transfer.* Propositions 22 and 23 hold for every such instance:
the loss identity, the exactness criterion, the loss bounds, and the
soft procedure as the joint problem with the premia replaced by
\(\gamma\tilde\Sigma_fb^*\).

(ii) *Frictionless spanning ETFs.* With spanning, frictionless ETFs,
diagonal \(V\), and a slack budget with every ETF interior at the joint
optimum, both procedures are exact for every value of the fund and
premium inputs: stage 1 chooses \((\gamma\tilde\Sigma_f)^{-1}\hat\lambda\), and stage 2 on
its fibre returns (144)'s fund holdings.

(iii) *Spanning ETFs with frictions.* With a slack budget and every ETF
interior at \(x_2\), the target-confined procedure is exact exactly when
\(x_2\) is jointly optimal. In the inputs that is two conditions
together:

$$
-c^E_j-\gamma(\Sigma_Ex^E_2)_j\in T_j(x_2)\ \text{for every ETF},\qquad
\hat\alpha_i-\gamma(Vx^A_2)_i\in T_i(x_2)\ \text{for every fund},\tag{148}
$$

each ETF's fee and residual marginal in its own cost band with the
sign of its trade, and each fund in its frictionless alpha band. The
first alone is necessary, not sufficient. With fees and traded ETFs,
it holds only on a set of inputs of measure zero. The soft procedure is
exact whenever \((\gamma\tilde\Sigma_f)^{-1}\hat\lambda\in\mathcal R\), whatever the frictions.

(iv) *A fund with an unreachable loading.* With one fund whose loading
has a component outside the ETFs' reach, Proposition 35's reduced
moments and \(\psi_i\), stage 1 fixes the fund at the premium-implied
holding \(a^*_i\) and the joint optimum at the band holding \(a_J\), and

$$
\Lambda=\psi_i(a_J)-\psi_i(a^*_i)\geq0,\qquad
\frac{\gamma s^{\rm red}_i}2(a_J-a^*_i)^2\leq\Lambda\leq\frac{\gamma s^{\rm red}_i}2(a_J-a^*_i)^2+(\kappa^+_i+\kappa^-_i+\mu_J)|a_J-a^*_i|,\tag{149}
$$

with \(\mu_J\) the box multiplier at \(a_J\), zero when \(a_J\) is interior. Stage 1
chooses the manager, and the procedure is exact exactly when the
premium-implied holding lies in the fund's alpha band.

(v) *What the frictions cost.* In (iii)'s setting,

$$
\Lambda\leq\min\Bigl(\frac{L_E^2}{2\gamma},\ L_E\|b_J-b^*\|_{\tilde\Sigma_f}\Bigr),\quad
L_E=\|\tilde\Sigma_f^{-1/2}R\|\bigl(\|c^E\|+\gamma\|\Sigma_E\|\|\bar x^E\|+\|\kappa^{\max}_E\|\bigr).\tag{150}
$$

With a binding budget, the procedure is exact exactly when \(x_2\) meets
the joint criterion for some shadow price, and the bound holds with
\(L_E(\eta_2)\) computed at the fibre problem's own cash multiplier; there
it holds for the supergradient that multiplier supplies, not for every
one.

The criterion is the polyhedral Karush-Kuhn-Tucker theorem applied to
a lifted problem with one cost bound per instrument
(`rockafellar1970convex`, Theorems 27.4 and 28.2-28.3, cited by theorem
number). Part (ii) solves the frictionless block as in Proposition 44
(iii). For (iii), at \(x_2\) the exposure error vanishes because stage 1
chose the Markowitz exposure, so joint optimality reduces to (148).
Part (iv) reduces the joint and fibre problems to the one variable
\(a\) by Proposition 28's elimination. Part (v) bounds the residual value's
supergradients at \(b^*\) by the ETF frictions.

So choosing exposure first is harmless exactly in Treynor and Black's
world (`treynor1973security`, p. 67, full text reviewed) and costs, in
the inputs, the fund's misplacement for a missing direction and at
most \(L_E^2/(2\gamma)\) for ETF frictions, while the soft procedure with an
unconstrained first stage stays exact. ETFs at zero are Propositions
40-41's.

The bound in (v) is stated at \(b^*\) only: at a boundary point of \(B_F\) the
relative supergradients are unbounded. No magnitude is claimed.

Propositions 44 and 45 keep every ETF strictly inside its box. The
last result is the fund decision when some ETFs sit at their zero
bound, the common long-only case, on which Propositions 40-41 build.

**Proposition 46 (The fund decision with ETFs at zero: one-sided slacks price the funds' by-product, the at-zero set follows from the inputs, and the response is piecewise with direction-dependent curvature; learning-driven tracking model at one review; machine checked, with the general criterion in (i) conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Fix one review as in Proposition 44. Parts (ii)-(v) assume spanning
frictionless ETFs (fees allowed), ETF caps absent or slack and the
budget slack, and use Proposition 40's ETF coordinates: the netting
matrix \(Q\) with columns \(r_i\), the exposure \(w=x^E+Qx^A\), \(\mu_E=B^E\hat\lambda-c^E\),
\(\Sigma_{EE}=B^E\tilde\Sigma_fB^{E\top}\), and \(\tilde\alpha=\hat\alpha+Q^\top c^E\). The bound \(x^E\geq0\) reads \(w\geq Qx^A\).

(i) *The criterion with one-sided ETF marginals.* With every ETF below
its cap, at the optimum each ETF \(j\) at zero satisfies
\(g_j=\eta+(1+\eta)t_j-\zeta_j\) with a *slack* \(\zeta_j\geq0\), and with spanning fund
\(i\)'s line is Proposition 44's with the extra term \(-\sum_{j\text{ at zero}}r_{ij}\zeta_j\): the
fund's by-product in the at-zero directions is priced at minus their
slacks.

(ii) *Which ETFs are at zero.* For a by-product \(q=Qx^A\), the exposure
problem \(\max\{\mu_E^\top w-\frac\gamma2w^\top\Sigma_{EE}w:w\geq q\}\) has a unique solution \(w(q)\)
with a unique multiplier \(\zeta(q)\geq0\). For a candidate set \(Z\) with
complement \(c\),

$$
w_c=\Sigma_{cc}^{-1}\Bigl(\frac{\mu_c}\gamma-\Sigma_{cZ}q_Z\Bigr),\qquad
\zeta_Z=\gamma\Sigma_{ZZ\cdot c}q_Z-\mu_{Z\cdot c},\tag{151}
$$

and \(Z\) is an at-zero set exactly when \(\zeta_Z\geq0\) and \(w_c\geq q_c\); every such
set gives the same \(w\) and \(\zeta\). The value \(V_E(q)=\max\) is concave and
differentiable with gradient \(-\zeta(q)\).

(iii) *The fund marginal and the criterion.* With the exposure
optimized out, the funds' smooth marginal is

$$
G_i(x^A)=\alpha^Z_i-\gamma(V^Zx^A)_i,\qquad
\alpha^Z=\tilde\alpha+Q_Z^\top\mu_{Z\cdot c},\qquad V^Z=V+Q_Z^\top\Sigma_{ZZ\cdot c}Q_Z,\tag{152}
$$

at \(Z=Z(Qx^A)\). The incumbent is optimal exactly when
\(-\kappa^-_i\leq G_i(x^{A-})\leq\kappa^+_i\) for every fund, one-sided at the bounds, for
any \(N\). For one fund, it is bought exactly when \(G(x^-)>\kappa^+\) and
\(x^-<\bar x\), sold exactly when \(G(x^-)<-\kappa^-\) and \(x^->0\), and held
otherwise. A premium error \(e\) shifts \(G_i\) by \(r_{iZ}^\top B^E_{Z\cdot c}e\), with
\(B^E_{Z\cdot c}\) the at-zero ETFs' loadings hedged by the free ones, which is zero
for every \(e\) exactly when \(r_{iZ}=0\).

(iv) *Along a fund's trade* (\(N=1\)). The marginal \(m(x)=G(x)\) is
continuous, strictly decreasing and piecewise linear, with slope
\(-\gamma s^Z\), \(s^Z=v+r_Z^\top\Sigma_{ZZ\cdot c}r_Z\), on each piece where \(Z(rx)\) is constant;
the pieces end where a free ETF's holding or an at-zero slack reaches
zero, both affine in \(x\). The optimum is the incumbent or the clipped
root of \(m=\kappa^+\) or \(m=-\kappa^-\). The *drop-Z rule*, Proposition 44 (iii) on
the menu without the incumbent's at-zero set \(Z^-\),

$$
\tilde x=\mathrm{clip}\Bigl(x^-,\frac{\alpha^{Z^-}-\kappa^+}{\gamma s^{Z^-}},\frac{\alpha^{Z^-}+\kappa^-}{\gamma s^{Z^-}}\Bigr)\text{ in }[0,\bar x],\tag{153}
$$

agrees with the optimum exactly when their unclipped roots agree or
both clip to the same bound, and the unclipped roots agree exactly
when either lies in the incumbent's piece. If the at-zero set contains
\(Z^-\) all along the way to the drop-Z root, the true trade is no longer
than the drop-Z trade; if it is contained in \(Z^-\), no shorter. A purchase and a sale of the same fund face
different pieces, so different curvatures.

(v) *One ETF.* With \(M=K=1\) and \(q=\sum_ir_ix_i\), the ETF is at zero exactly
when \(\mu_E\leq\gamma\sigma_{EE}q\), and then every fund's marginal is
\(\tilde\alpha_i+r_i\mu_E-\gamma(v_ix_i+r_i\sigma_{EE}q)\): its total expected return less
the full risk charge.

Part (i) is Proposition 45's criterion with the ETF bound's multiplier
kept. Part (ii) is the Karush-Kuhn-Tucker system of a strictly concave
quadratic over an orthant translate, solved by a Schur complement on
the free block; its uniqueness uses the complementarity estimate
\(\|w(q')-w(q)\|_\Sigma\leq\|q'-q\|_\Sigma\). Part (iii) differentiates the reduced
objective, using (ii)'s gradient. Part (iv) follows the pieces of (ii)
along the line \(rx\).

With \(Z\) given, (152) is Proposition 28's reduced moments with the at-zero
directions as the unreachable ones, produced here by the bound rather
than by the menu, and premium beliefs reach the fund decision through
them although the ETFs span. In the language of Jagannathan and Ma
(`jagannathan2003risk`, Proposition 1, read at the level of the
proposition), the at-zero multipliers fold into the moments; here the
fold-in is an adjusted premium and an adjusted covariance \(V^Z\),
positive semidefinite of rank at most \(|Z|\), with the multipliers fixed
by complementarity from the inputs rather than read off the solution,
and it holds piecewise along a trade.

ETF frictions and a binding budget with ETFs at zero are Proposition
41's. An ETF at its cap, the per-fund direction for several funds, and
magnitudes are not treated.

Proposition 41 made every fund's marginal explicit once the ETFs'
statuses are known, but with several ETFs those statuses come from a
finite complementarity problem. With one ETF the last result removes
that step: two scalar prices decide everything.

**Proposition 47 (One ETF and any number of funds: the optimum through two monotone scalars, the exposure price and the cash price; learning-driven tracking model at one review; machine checked, with the existence of a binding budget's cash price at paper level through the polyhedral Karush-Kuhn-Tucker theorem).**
Take Proposition 41's setting with one ETF and one factor and a
diagonal \(V\) with entries \(v_i\): fund holdings \(x_i\in[0,\bar x_i]\), an ETF
holding \(p\geq0\) with no cap, loading \(b_E>0\), fee \(c^E\), rates \(\kappa^\pm_E\) and
residual variance \(\sigma_E\), and the funded budget with multiplier \(\eta\).
Write \(r_i=b_{A,i}/b_E\), \(\mu_E=b_E\hat\lambda-c^E\), \(\sigma_{EE}=b_E^2\tilde\sigma_f\),
\(\tilde\alpha_i=\hat\alpha_i+r_ic^E\), the *exposure price*
\(m(w)=\mu_E-\gamma\sigma_{EE}w\) at total exposure \(w=p+\sum_ir_ix_i\), the scaled ETF
thresholds \(\theta_b=\eta+(1+\eta)\kappa^+_E\) and \(\theta_s=\eta-(1+\eta)\kappa^-_E\), and the
one-fund clip at prices \((m,\eta)\)

$$
x_i(m,\eta)=\mathrm{clip}\Bigl(x^-_i,\ \frac{\tilde\alpha_i+r_im-\eta-(1+\eta)\kappa^+_i}{\gamma v_i},\ \frac{\tilde\alpha_i+r_im-\eta+(1+\eta)\kappa^-_i}{\gamma v_i}\Bigr)\text{ in }[0,\bar x_i],\tag{154}
$$

with \(q(m,\eta)=\sum_ir_ix_i(m,\eta)\) and \(p(m,\eta)=(\mu_E-m)/(\gamma\sigma_{EE})-q(m,\eta)\).

(i) *Every fund sees the ETF through one price.* Fund \(i\)'s marginal is
\(\tilde\alpha_i+r_im(w)-\gamma v_ix_i\), so at the optimum every fund holds its clip
(154) at \((m^*,\eta^*)\). \(q(\cdot,\eta)\) is continuous, nondecreasing and
bounded, \(p(\cdot,\eta)\) is continuous, strictly decreasing and onto, and each
\(x_i\) is nonincreasing in \(\eta\) at fixed \(m\).

(ii) *The ETF's status.* For each \(\eta\geq0\), let \(m_0\) be the root of
\(p(m,\eta)=0\) and, when \(p^->0\), \(m_I\) the root of \(p(m,\eta)=p^-\); both are
unique. With the ETF's own marginal \(e(m)=m-\gamma\sigma_Ep(m,\eta)\),

$$
\begin{aligned}
p^->0:&\ \text{bought iff }e(m_I)>\theta_b,\quad\text{idle iff }\theta_s\leq e(m_I)\leq\theta_b,\quad\text{sold iff }e(m_I)<\theta_s,\\
p^-=0:&\ \text{at zero iff }m_0\leq\theta_b,\ \text{else bought},
\end{aligned}\tag{155}
$$

a sale ending at a positive holding when \(m_0>\theta_s\) and at zero otherwise.
In each regime \(m^*\) is the stated price: \(m_I\) when idle, \(m_0\) at zero,
and in a traded regime the unique root of \(e(m)=\theta\), which is \(\theta\) itself
when \(\sigma_E=0\).

(iii) *The cash price.* The cash left by (ii)'s solution,
\(k(x(\eta))\), is nondecreasing in \(\eta\). If \(k(x(0))\geq0\) the budget is slack and
\(\eta^*=0\); otherwise any \(\eta>0\) with \(k(x(\eta))=0\) gives the optimum, and all
such \(\eta\) give the same holdings.

(iv) *Readings.* At the optimum's prices, fund \(i\) is bought exactly
when

$$
\tilde\alpha_i+r_im^*-\gamma v_ix^-_i>\eta^*+(1+\eta^*)\kappa^+_i\quad\text{and}\quad x^-_i<\bar x_i,\tag{156}
$$

sold under the mirror condition with \(x^-_i>0\), and held otherwise:
Proposition 44 (iii)'s rule with the exposure price added, exact for
every \(N\). A fund's holding moves by at most \(|r_i|/(\gamma v_i)\) per unit of
exposure price, and at a fixed exposure price it does not rise with the
cash price.

For each \(\eta\), the Lagrangian with the budget priced at \(\eta\) has exactly
one maximizer over the funds' boxes and \(p\geq0\); its fund coordinates are
the clips at the exposure price it induces, and (155) reads the ETF's
line against its scaled cost band. The monotonicity of \(q\) and \(p\) in \(m\)
makes each root unique. The existence of a positive \(\eta\) that exhausts
the budget, when \(\eta=0\) leaves it negative, is the multiplier of the
polyhedral Karush-Kuhn-Tucker theorem (`rockafellar1970convex`,
Theorems 27.4 and 28.2-28.3, cited by theorem number) through
Proposition 44 (i).

A manager with one broad ETF therefore needs no solver. Two monotone
scalar searches, each exact on finitely many linear pieces, give the
cash price and the exposure price; every fund is then its own band
decision, and the ETF's status is read off (155). Frictionless ETFs
with a slack budget are the case \(\theta_b=\theta_s=0\) of Proposition 46 (v).

Several ETFs, and a formal link from these one-ETF coordinates to the
general review model, are not treated. No magnitude is claimed.

Proposition 41 (iv) showed that a first stage fixing the exposure by
the frictionless one-sided problem is generically inexact once a
costly ETF ends interior. The last result gives a first stage that
prices the ETF trades, and a loss bound for any first stage.

**Proposition 48 (An incumbent-aware first stage, and the two-stage loss through the ETF-line residual; learning-driven tracking model at one review; machine checked, with the existence of the second stage's multipliers at paper level through the polyhedral Karush-Kuhn-Tucker theorem, and the converse of (ii) conditional on it).**
Take Proposition 41's setting with no ETF residual risk and the joint
optimum \(x_J\), value \(J\) and exposure \(w_J\). The *fibre value* \(V(w)\) is the
best objective the funds can reach when the ETFs must deliver exposure
\(w\) under the zero bound and the budget. A *fibre-confined* procedure
picks \(w_1\), then maximizes on its fibre at \(x_2\), losing \(\Lambda=J-V(w_1)\). The
*incumbent-aware* first stage solves the review with the funds frozen
at their incumbents, ETF costs, fees, zero bound and budget on, and
takes its exposure as \(w_1\). With multipliers of the fibre problem at
\(x_2\) (its cash price \(\eta_2\), cost slopes \(t^{(2)}\) and zero-bound multipliers
\(\zeta^{(2)}\)), the *ETF-line residual* is

$$
s=g_E(x_2)-\eta_2\mathbf1-(1+\eta_2)t^{(2)}+\zeta^{(2)},\qquad g_E(x_2)=\mu_E-\gamma\Sigma_{EE}w_1,\tag{157}
$$

the amount by which each ETF's joint line fails at \(x_2\).

(i) *A loss bound.* For any fibre-confined procedure and any valid
multipliers, with \(d=w_J-w_1\),

$$
\frac\gamma2\bigl[(x^A_J-x^A_2)^\top V(x^A_J-x^A_2)+\|d\|^2_{\Sigma_{EE}}\bigr]\leq\Lambda\leq\min\Bigl(s^\top d,\ \frac{s^\top\Sigma_{EE}^{-1}s}{2\gamma}\Bigr),\qquad
\gamma\|d\|_{\Sigma_{EE}}\leq\|s\|_{\Sigma_{EE}^{-1}},\tag{158}
$$

and \(\Lambda=0\) exactly when \(x_2=x_J\).

(ii) *Exactness.* Multipliers with \(s=0\) exist exactly when Proposition
41's joint criterion holds at \(x_2\), and then \(x_2=x_J\). Conversely, an exact
split admits such multipliers, and at an ETF traded to an interior
holding under a slack budget \(s_j=0\) for every valid choice.

(iii) *When the incumbent-aware split is exact.* It is exact if every
fund's marginal at the frozen-funds optimum lies in its scaled held
band (then that optimum is the joint one); if every ETF trades to an
interior holding at the first stage and keeps its direction to an
interior holding at the second, with a slack budget at both; and, when
some ETFs are fixed and keep their statuses, if every fund's line holds
at \(x_2\) with the first stage's ETF marginals, the residual then living
only in the fixed directions.

Part (i) bounds the joint objective at any feasible point by its value
at \(x_2\) plus the residual's linear term less the strong-concavity
terms in the exposure and the funds, and evaluates it at \(x_J\); the lower
bound is strong concavity along the segment from \(x_J\). Part (ii) matches
the residual's zero with the joint criterion, moving an at-zero ETF's
slope to Proposition 46's convention. Part (iii) reads the residual at
the first stage's statuses.

Pricing the ETF trades at the first stage removes the failure that ETF
costs alone cause: the incumbent-aware split can fail only when the
funds' trades move the by-product in fixed directions, the cash, or an
ETF's status. Its fibre is always fundable. It is the better first
stage on exactness and fundability, not on loss (experiment 045's
illustration, in Appendix A). The bound (158) sharpens Proposition 45
(v)'s norm bound with the exact multiplier vector.

ETF residual risk, the repeated split from the second stage's holdings,
and an input-level condition under a binding budget beyond (iii)'s
first case are not treated. No magnitude is claimed.

Proposition 42 left the fine-regime problem between its frictionless
and frozen ends as a two-dimensional corrector problem. The last
result traps that problem's leading-order cost between explicit bounds
in the inputs.

**Proposition 49 (The fine-regime cost with one costly ETF, sandwiched in the inputs; learning-driven tracking model with one fund and one ETF, at the ergodic level; machine checked for every eigenvalue the comparison principle brackets, with its application to the pair's corrector cited).**
Take Proposition 42's setting with symmetric per-side rates
\(\kappa_A,\kappa_E>0\), \(v_A,v_B>0\), \(|r|<1\), \(c_E=\gamma\Sigma_{EE}\), and \(v_B^{\rm eff}\) from
(137). The *corrector problem of the pair* is the first corrector
equation for the state \((y_a,e)\) with running cost \(\frac{c^{\rm res}}2y_a^2+\frac{c_E}2e^2\),
innovation covariance \(W\) with entries \(v_A\), \(r\sqrt{v_Av_B}+\rho_hv_A\) and
\(v_B^{\rm eff}\), and admissible gradients
\(C=\{p:|p_a+\rho_hp_e|\leq\kappa_A,\ |p_e|\leq\kappa_E\}\); write \(a\) for its eigenvalue, the
pair's leading-order average cost. With the one-instrument eigenvalues
at per-side rate \(k\),

$$
a_A(k)=\frac{c^{\rm res}}2\Bigl(\frac{3(2k)v_A}{4c^{\rm res}}\Bigr)^{2/3},\qquad
a_E(k)=\frac{c_E}2\Bigl(\frac{3(2k)v_B^{\rm eff}}{4c_E}\Bigr)^{2/3},\tag{159}
$$

and \(x=|\rho_h|\kappa_E/\kappa_A\):

(i) *The sandwich.* If \(x<1\),

$$
a_A\bigl(\kappa_A-|\rho_h|\kappa_E\bigr)+a_E(\kappa_E)\ \leq\ a\ \leq\ a_A\bigl(\kappa_A+|\rho_h|\kappa_E\bigr)+a_E(\kappa_E),\tag{160}
$$

and in general \(a\) is at least the largest \(a_A(k'_A)+a_E(k'_E)\) over
\(k'_A+|\rho_h|k'_E\leq\kappa_A\), \(k'_E\leq\kappa_E\). A third lower bound works through the
ETF's own gap, which only the ETF moves: \(a\geq a_b(\kappa_E)\), the
one-instrument eigenvalue with curvature \(c^{\rm res}c_E/(c^{\rm res}+\rho_h^2c_E)\) and
variance \(v_B\).

(ii) *Uncorrelated risks.* If \(\Sigma_{AE}=0\), \(a=a_A(\kappa_A)+a_E(\kappa_E)\), whatever \(r\).

(iii) *The gap.* Relative to \(a_A(\kappa_A)\), the bounds differ by
\((1+x)^{2/3}-(1-x)^{2/3}\leq2[1-(1-x)^{2/3}]\), of first order in \(x\).

(iv) *An effective rate and the ends.* When \(x\leq1\), \(a=a_A(k^*)+a_E(\kappa_E)\)
for some \(k^*\) within \(|\rho_h|\kappa_E\) of \(\kappa_A\). As \(\kappa_E\to0\), \(a\to a_A(\kappa_A)\), the
frictionless end; as \(\kappa_E\to\infty\), \(a\to\infty\) through the third bound, so the
frozen end is not an ergodic object.

The bounds come from separable test functions built from the
one-instrument corrector solutions of Proposition 42 (iii), which are
classical sub- and supersolutions of the pair's problem with matching
growth. The comparison principle for the multidimensional corrector
(`possamai2015homogenization`, Theorems 3.1-3.2 and Corollary 6.1,
audited for ledger entry AX-16) places the eigenvalue between any such
sub- and supersolution's values; the one-instrument solutions are
ledger entry AX-15 (`soner2013homogenization`, equations (4.3)-(4.5);
`muhlekarbe2017primer`, Section 4). Part (iii) is the concavity of
\(t\mapsto t^{2/3}\).

At leading order, then, the ETF's cost reaches the fund as a shift of
the fund's rate by at most the re-hedge cost \(|\rho_h|\kappa_E\), with the
fund's residual curvature and its own innovation variance; the idle
target's variance of Proposition 43 enters no bound. This is
Proposition 38's static re-hedge term transported to the fine regime.
The result bounds the pair's cost, not the fund's band: where \(k^*\)
lies, and the non-contact set between the ends, are open. The
identification of the discrete quarterly problem with the corrector
problem is cited, not shown, as for Proposition 42.

Every result so far with a funded budget is for one review. The last
result puts a budget that may bind into a two-review problem with one
fund, one ETF and cash, and says exactly what the budget adds to
today's decision.

**Proposition 50 (Two reviews with a binding budget: the dynamic cash price and the incumbent values; learning-driven tracking model, finite-law variant, one fund and one ETF; machine checked, with necessity of the lines and the myopic-optimality test conditional on the polyhedral Karush-Kuhn-Tucker theorem).**
Take the finite-law variant of the learning-driven tracking model with
one fund and one ETF, holdings \(x=(a,p)\), reviews \(t=0,1\) and marking at 2,
a finite state law \(q(z')\) for tomorrow with gross returns \(g(z')>0\),
predictive moments \((\mu_t,\Sigma_t)\), discount \(\beta\), rates \(\kappa^\pm_i\), caps, and
the funded budget at both reviews, \(h^+_0\geq0\) and \(h^+_1(z')\geq0\), cash earning
nothing. Write \(g_{t,i}=(\mu_t-\gamma\Sigma_tx_t)_i\) for the smooth marginals and \(T\)
for Proposition 44's trade-sign slope sets. The *repeated one-review*
(myopic) policy solves Proposition 47's one-review problem today, and
again in each state tomorrow from the marked holdings and the cash
left.

(i) *Structure.* An optimal policy exists; tomorrow's value is concave
in the carried holdings and cash and nondecreasing in cash; and the
root problem is a concave maximization over a polyhedron.

(ii) *Today's lines.* A policy is optimal exactly when, for multipliers
\(\eta_0\), \(\eta_1(z')\) complementary to the two budgets and slopes \(t_0\), \(t_1(z')\)
in their trade-sign sets, tomorrow's one-review lines hold in every
state and today's lines hold with the *dynamic cash price* and the
*incumbent values*

$$
\hat\eta_0=\eta_0+\beta\sum_{z'}q(z')\eta_1(z'),\qquad
S_i=\beta\sum_{z'}q(z')g_i(z')s_i(z'),\qquad s_i(z')=\eta_1(z')+(1+\eta_1(z'))t_{1,i}(z'),\tag{161}
$$

$$
g_{0,i}(x_0)+S_i-\hat\eta_0-(1+\hat\eta_0)t_{0,i}\ \ \begin{cases}=0&0<x_{0,i}<\bar x_i,\\\leq0&x_{0,i}=0,\\\geq0&x_{0,i}=\bar x_i.\end{cases}\tag{162}
$$

The incumbent value \(s_i(z')\) of a unit carried into state \(z'\) is
tomorrow's marginal score if the unit is then held inside its box, its
scaled purchase threshold if bought, and its scaled sale threshold if
sold. So today's decision is Proposition 47's one-review rule with each
instrument's net return raised by \(S_i\) and the cash price replaced by
\(\hat\eta_0\).

(iii) *What the budget adds.* If tomorrow's budget is slack in every
state, \(\eta_1=0\), \(\hat\eta_0=\eta_0\) and \(s_i=t_{1,i}\): today's lines are Proposition 26's
edge brackets with today's scaling. A budget that may bind tomorrow
therefore adds exactly two things: an upward shift of every threshold
today, the purchase threshold by \(\beta\mathbb E\eta_1(1+\kappa^+_i)\) and the sale threshold
by \(\beta\mathbb E\eta_1(1-\kappa^-_i)\), the option value of cash (so the manager buys less
and sells more readily today; the claim's own wording, a fall of the
sale threshold, is wrong, as red's read of the manuscript found); and the factor \(1+\eta_1(z')\) on tomorrow's slopes inside the
incumbent values. In the inputs,

$$
\beta\mathbb E\bigl[g_i(\eta_1-(1+\eta_1)\kappa^-_i)\bigr]\leq S_i\leq\beta\mathbb E\bigl[g_i(\eta_1+(1+\eta_1)\kappa^+_i)\bigr].\tag{163}
$$

(iv) *When repeating the one-review rule is optimal.* The myopic policy
is dynamically optimal exactly when its root holdings satisfy (162) for
some multipliers and slopes of its own tomorrow problems and some
admissible \(\eta_0\), \(t_0\). Tomorrow's multiplier is unique in any state that
trades some instrument strictly inside its box. If tomorrow's budget is
slack everywhere, the test reads
\(g_{0,i}(x^{\rm my}_0)+\beta\mathbb E[g_it_{1,i}]-\eta_0-(1+\eta_0)t_{0,i}\) with (162)'s signs; with
today's budget slack as well, an instrument traded strictly inside its
box today needs \(\beta\mathbb E[g_it_{1,i}]=0\). For a myopic purchase strictly inside
the box with today's budget slack, the root objective along that
instrument, with the other holding fixed, lies below the line of slope
\(r=S_i-\beta\mathbb E[\eta_1](1+\kappa^+_i)\) through the myopic root, in both directions.

(v) *What survives.* The two-price rule at both reviews; the band at
every review, in the marginal \(g_{0,i}+S_i\), of width \((1+\hat\eta_0)(\kappa^+_i+\kappa^-_i)\)
at fixed \(S_i\) and \(\hat\eta_0\); and a costless instrument still anticipates
the budget, through the cash price alone: \(S_i=\beta\mathbb E[g_i\eta_1]\).

The problem is one concave program over a polyhedron in today's and
tomorrow's holdings. Sufficiency of the lines is a direct Lagrangian
bound. Necessity is the polyhedral Karush-Kuhn-Tucker theorem
(`rockafellar1970convex`, Theorems 27.4 and 28.2-28.3, cited by theorem
number) on the lifted two-review problem, whose tomorrow multipliers
become \(\hat\eta_0\) and \(S_i\) when today's lines are read.

The result is the dynamic cash price and the incumbent values: a
binding budget tomorrow moves today's thresholds by the expected cash
price and credits each position with what a unit of it is worth to
tomorrow's problem. The slope \(r\) in (iv) says only how the root
objective moves along one instrument with the other held fixed:
negative reads as *hoarding* cash, positive as *front-loading* a
purchase. It is a one-instrument reading, not a rule for what the
dynamic policy buys. With both holdings free the joint move can
reverse by substitution through the covariance and the shared budget;
experiment 047 found this in 12 of 82 cases, one with no binding budget
at either review. The two signs are Propositions 12-13's opposite
continuation effects, here attributed to the budget.

More than two reviews, several funds or ETFs, the joint comparative
static, and the width of today's band in holdings with a binding
budget today are not treated. No magnitude is claimed.

Proposition 50's lines use two numbers read from tomorrow's solutions:
the cash price and the incumbent values. The last result bounds both
in the inputs without solving tomorrow, and turns the myopic test
into a statement about when repeating the one-review rule can be
right at all.

**Proposition 51 (The two-review criterion bounded in the inputs; learning-driven tracking model, finite-law variant, one fund and one ETF; machine checked given tomorrow's multipliers, with the sign result's link to the two-review problem at paper level).**
Take Proposition 50's setting. Write

$$
\bar\eta(z')=\max_i\frac{(\mu_{1,i}(z')-\kappa^+_i)^+}{1+\kappa^+_i},\qquad
\hat x_i(z')=\frac{(\mu_{1,i}(z')-\kappa^+_i)^+}{\gamma\Sigma_{1,ii}(z')},\qquad
\mathrm{need}(z')=\sum_i(1+\kappa^+_i)\bigl(\hat x_i(z')-g_i(z')x_{0,i}\bigr)^+,\tag{164}
$$

the best expected return tomorrow net of its purchase rate, instrument
\(i\)'s solo target, and the cash those targets would need.

(i) *Tomorrow's cash price.* With nonnegative covariances tomorrow, some
admissible cash price in each state is at most \(\bar\eta(z')\), and \(0\) is
admissible when the cash carried covers \(\mathrm{need}(z')\). For any family of
tomorrow multipliers, \(\eta_1\leq\bar\eta\) in every state that trades something
or has cash left, so \(\eta_0\leq\hat\eta_0\leq\eta_0+\beta\mathbb E[\bar\eta]\) unless some state trades
nothing with all cash spent.

(ii) *The incumbent values and the residual.* With any admissible \(\eta_1\),

$$
-\beta\mathbb E[g_i]\kappa^-_i\ \leq\ S_i\ \leq\ \beta\mathbb E\bigl[g_i(\eta_1+(1+\eta_1)\kappa^+_i)\bigr],\tag{165}
$$

and the residual \(R_i=S_i-\beta\mathbb E[\eta_1](1+\kappa^+_i)\) lies in an explicit bracket.
It is negative when tomorrow's cash price is high in the states where
the instrument is marked down, by more than its purchase rate covers,
and positive when the cash price is high where its marked gain, net of
the round trip, covers the purchase.

(iii) *When repeating the one-review rule can be right.* With today's
budget slack at the myopic root, an instrument the myopic policy trades
strictly inside its box passes the test of Proposition 50 (iv) exactly
when \(R_i=0\) for a purchase, or \(S_i=\beta\mathbb E[\eta_1](1-\kappa^-_i)\) for a sale, for some
admissible tomorrow family. That is an identity for an instrument
costless on both sides with a slack budget tomorrow, and otherwise one
equation on the inputs. With today's budget binding at the myopic root,
the condition is the inequality

$$
S_i\ \geq\ \bigl(\beta\mathbb E[\eta_1]-\eta_0^{\rm my}\bigr)(1+\kappa^+_i),\tag{166}
$$

which holds on open sets of inputs.

(iv) *A restricted comparative static.* With a frictionless, uncapped ETF
held strictly inside its box at the dynamic root and at the reduced
myopic point (the joint optimum with the fund held at its myopic
holding), today's budget slack at both, and a myopic purchase of the
fund strictly inside its box,

$$
\mathrm{sign}(a^{\rm dyn}-a^{\rm my})=\mathrm{sign}\bigl(R^{\rm red}_A-\rho_0R^{\rm red}_E\bigr)\tag{167}
$$

whenever the right side is nonzero, with the residuals evaluated at the
reduced point and \(\rho_0\) today's hedge ratio.

The bounds in (i) come from tomorrow's one-review lines: a cash price
above \(\bar\eta\) would make every purchase unattractive, and a state whose
cash covers the solo targets needs none. (ii) bounds each incumbent
value by its regime's thresholds. (iii) evaluates the root line at an
interior trade. For (iv), the fund's root line at the reduced point is
\(R^{\rm red}_A-\rho_0R^{\rm red}_E\), and a concave function of one variable with a
positive right derivative at the myopic holding is maximized to its
right.

So, with cash left today, repeating the one-review rule is dynamically
optimal only where it trades nothing, trades to a bound, or trades an
instrument costless both ways with a slack budget tomorrow, apart from
inputs on which one equation happens to hold; with cash spent today it
can be optimal on open sets. The sign in (iv) is the corrected,
restricted form of the hoarding and front-loading reading of
Proposition 50. With a costly ETF no comparative static is claimed:
experiment 047's instance 106 has the dynamic policy holding more of
the fund than the myopic one although the fund's residual is negative,
because it sells the ETF instead.

More than two reviews, several funds or ETFs, and the joint
admissibility of a per-state selection of tomorrow's multipliers are
not treated. No magnitude is claimed.

Propositions 50-51 use the finite-law variant, whose filter is the best
linear predictor, not the posterior. The last result puts learning,
predictive risk, marking and the budget into one model under either
shock law, says what the filter's output means under each, and works
an example.

**Proposition 52 (One worked model for learning, predictive risk, marking and the budget, under two laws; the learning-driven tracking model with one fund, one ETF and cash over two reviews; machine checked in its finite-law consistency, moment content and the example's first-review numbers, with the filter's two meanings cited and the transfer and later tables at paper level).**
Take the learning-driven tracking model with one fund (loading \(b_A\)) and
one ETF (loading \(b_E>0\), fee \(c^E\)), cash, reviews \(t=0,1\), the funded budget
allowed to bind, and a diagonal prior. Under the *Gaussian law* premia,
alphas and shocks are Gaussian; under the *finite law* each takes
finitely many values with the same first two moments (two values
\(m_0\pm\sqrt{P_0}\) per parameter block), so the public histories form a finite
tree.

(i) *Consistency.* Under either law the posterior variance path is
deterministic and independent of trades, with
\(P_1^{-1}=P_0^{-1}+\mathrm{diag}(1/\sigma_f^2,1/\sigma_A^2)\); the predictive covariance is positive
definite and the target well defined at every history. Under the finite
law marking keeps holdings nonnegative, every review's feasible set is
nonempty, its optimum unique, and the two-review problem has an optimal
policy.

(ii) *The filter's two meanings.* Under the Gaussian law the filter's
mean is the exact posterior mean (`murphy2007conjugate`, the conjugate
Gaussian update, ledger entry AX-18). Under any law with the same first
two moments it is the minimum-mean-squared-error affine predictor
(`uhlmann2022gaussianity`, on Kalman's Corollary 1, ledger entry AX-17,
which states the Gaussian case as sufficient only). Under the finite
law the innovation has mean zero and covariance \(P_t-P_{t+1}\), the exact
posterior mean averages to \(m_0\), and the two means differ at a history
reached from exactly two hidden states \(m_0\pm\sqrt{P_0}\) in a block whose
filter innovation is nonzero: the posterior returns to \(m_0\) while the
filter moves.

(iii) *What transfers.* Every one-review result holds at each review
under the finite law, and under the Gaussian law wherever the marked
holdings are nonnegative, since the stage score uses only the first two
moments. The multi-review band results hold under the finite law with a
slack budget, which holds at every pair of in-box holdings when initial
cash is at least \(2(1+\kappa)\sum_i\bar x_i\) with every purchase rate at most \(\kappa\).
From the quadratic-cost model only the target's structure transfers.
Unproved: the dynamic optimum under the Gaussian law, the exact-posterior
manager's policy under the finite law, and any dependence of the dynamic
policy on the finite law beyond its moments.

(iv) *The worked example* (all inputs assumed; an illustration). With
\(b_A=0.9\), \(b_E=1\), \(c^E=5\) basis points, prior premium 1.0% (sd 0.4%) and alpha
0.4% (sd 2.0%) a quarter, \(\gamma=2.5\), \(\beta=1\), rates of 50 basis points for the fund
and 10 for the ETF, caps of 1, and incumbents fund 0.40, ETF 0, cash
0.06: the gains are \(1/402\) and \(1/11\), today's target is (0.406, 0.225),
the budget binds with a cash price of 0.174%, and both the one-review
rule and the two-review optimum hold the fund and buy the ETF to 0.060.
After an ambiguous observation the filter raises the alpha estimate by
0.55 percentage points while the exact posterior stays at the prior;
both managers hold. A manager using the exact posterior gains 8.6 basis
points over the two quarters, all at the second review, with decisions
differing at 42 of the 72 public nodes.

Parts (i)-(ii) combine the scalar filter recursion with the finite
tree's Bayes computation; the two meanings are the cited ledger entries,
whose hypotheses the model's laws meet. Part (iii) reads each result's
hypotheses against the model. Part (iv) evaluates the formulas and
solves the finite two-review program.

In this model, current learning, today's updated means and predictive
risk, enters every decision under either law; the law changes what the
filter's mean is, not the rule that uses it. The cheap ETF, not cash, is
the reserve for tomorrow's adjustment at these inputs.

Propositions 50-52 say how tomorrow enters today's decision in the
two-review model. The last result reads them as a rule for the
reserve: which part of today's ETF and cash beyond the one-review
optimum answers tomorrow's revision, when none is needed, where it is
held, how it grows and how large it can be.

**Proposition 53 (The reserve rule with one fund and one ETF; the two-review worked model of Proposition 52, finite law; machine checked in its bounds, certificate and shift, with the direction reading, the computation's fixed point and the Gaussian tail bound at paper level).**
Take Proposition 52's model. Let \(x^{\rm my}_0=(a^{\rm my},p^{\rm my})\) with leftover cash \(h^{\rm my}\)
be the one-review optimum today, \(x^{\rm dyn}_0\) the dynamic optimum, and, for
holdings \(x_0\) and a state \(z'\), the solo targets \(\hat x_i(z')\) and \(\mathrm{need}(z';x_0)\)
of (164), with \(N(x_0)=\max_{z'}\mathrm{need}(z';x_0)\) the largest funding need
tomorrow. The alpha revision has variance \(v^\alpha=k^\alpha_0p^\alpha_0\), the gain times
the prior variance, and extreme \(\epsilon^\alpha_{\max}\); \(g^{\min}_i\) is instrument \(i\)'s smallest
gross return.

(i) *Two channels, two reserves.* Today's ETF and cash differ from the
one-review ones through Proposition 50's two channels. The
*cost-channel reserve*, present with slack budgets, is carried by
\(S_E=\beta\mathbb E[g_Et_{1,E}]\), the ETF's expected marked cost slope tomorrow: the
ETF is held below its one-review level when that slope is expected
negative and above when positive, with cash taking the difference.
The *budget-channel reserve* comes from states that price cash.

(ii) *When no reserve is needed.* The cost channel vanishes exactly when
\(\mathbb E[g_Et_{1,E}]=0\). The budget channel vanishes at any root \(x_0\) with cash
\(h>0\) and \(h\geq N(x_0)\), and in the inputs

$$
N(x^{\rm my}_0)\leq\sum_{i\in\{A,E\}}(1+\kappa^+_i)\Bigl[\frac{(\mu_{1,i}^{\max}-\kappa^+_i)^+}{\gamma\Sigma_{1,ii}}-g^{\min}_ix^{\rm my}_{0,i}\Bigr]^+,\tag{168}
$$

with \(\mu^{\max}_{1,A}=\mu_{0,A}+b_A\epsilon^\lambda_{\max}+\epsilon^\alpha_{\max}\) and \(\mu^{\max}_{1,E}=\mu_{0,E}+b_E\epsilon^\lambda_{\max}\): leftover cash
covering the largest solo-target purchases at the revision's extreme
suffices. As a certificate, a root of Proposition 50's lines with
\(\eta_1=0\) in every state whose cash is positive and covers its own need
is the dynamic optimum. When cash does not cover every state, the
budget channel's terms are bounded by the uncovered states' moments,
\(\beta\mathbb E[\eta_1]\leq\beta\mathbb E[\bar\eta\,\mathbf 1_U]\), and ignoring the reserve errs in each purchase
threshold by at most \((1+\kappa^+_i)\) times that.

(iii) *ETF against cash, and the size.* With today's budget slack, the
ETF's root line differs from its one-review line by the *reserve
premium* \(\Pi_E=S_E-\beta\mathbb E[\eta_1](1+t_{0,E})\), which by state reads as the ETF's
marked proceeds in the states where cash is dear against its cost
today. With both budgets slack and the fund fixed at \(a^{\rm my}\),

$$
p^{\rm fix}-p^{\rm my}=\frac{S_E-(t^{\rm fix}_{0,E}-t^{\rm my}_{0,E})}{\gamma\Sigma_{0,EE}},\qquad
|p^{\rm fix}-p^{\rm my}|\leq\frac{\beta\max(\kappa^+_E,\kappa^-_E)\mathbb E[g_E]+\kappa^+_E+\kappa^-_E}{\gamma\Sigma_{0,EE}},\tag{169}
$$

so the shift is exactly \(S_E/(\gamma\Sigma_{0,EE})\) when the ETF trades the same way
today under both, and zero when the ETF is held untraded inside
today's band and the band absorbs \(S_E\). Here \(S_E\) is read from the
tomorrow of the point \(p^{\rm fix}\) itself: (169) is a fixed-point
condition, not a size read from the one-review tomorrow.

(iv) *How the need grows.* On its active set the fund's need is affine
in the alpha revision,

$$
\frac{\partial\,\mathrm{need}_A}{\partial\epsilon^\alpha}=\frac{1+\kappa^+_A}{\gamma\Sigma_{1,AA}},\tag{170}
$$

and an ETF reserve funding a need \(n\) must be \(n/((1-\kappa^-_E)g^{\min}_E)\) units. The
reserve itself is not monotone in the inputs.

(v) *The maximum.* If some state prices cash for every admissible family
of tomorrow multipliers, the cash carried at the dynamic optimum
satisfies

$$
h^{\rm dyn}\leq N(x^{\rm dyn}_0),\ \text{strictly when }h^{\rm dyn}>0.\tag{171}
$$

The results are Propositions 50-51's objects sized in the model's
inputs, the revision's law included; no new mechanism is claimed. The
bounds read tomorrow's one-review lines at the revision's extremes;
(169) solves the ETF's root line with the fund fixed; (171) holds
because a positive cash price tomorrow in some state requires that
state's need to exceed the cash carried.

*The rule's computation.* Fix the fund at \(a^{\rm my}\). If the one-review root
holds the ETF untraded and \(t^{\rm my}+S_E\) stays in its band, hold it;
otherwise solve \(g_{0,E}(a^{\rm my},p)+S_E(p)-t_{0,E}(p)=0\) for \(p\), with \(S_E(p)\) read
from the tomorrow of \(p\) itself. A one-shot reading from the one-review
tomorrow can mislead: experiment 053 found it worse than repeating the
one-review rule in 16 of 84 cells. Applied as a fixed point, it tied
the dynamic optimum in all 93 of experiment 054's cells where its
hypotheses hold, and where the dynamic policy also sells the fund it
leaves 0.10 to 0.26 basis points (illustrations of the tested cells).

Several funds, an ETF reserve under the Gaussian law beyond the tail
bound, and the reserve's joint move with the fund free are not treated.
No magnitude is claimed.

Proposition 53 is for one fund. The last result extends the reserve
to several funds sharing one ETF and cash, and says exactly what a
fund-by-fund rule misses.

**Proposition 54 (Several funds sharing one ETF reserve; the two-review model with \(N\) funds and one ETF, finite law; machine checked, with the cash price's common root, the pooling remark and the carried-over cost channel at paper level).**
Take Proposition 50's model with \(N\) funds of loadings \(b_i>0\) and one ETF of
loading \(b_E>0\), with Proposition 47's netting weights \(r_i=b_i/b_E\), exposure
price \(m_t\) and net alphas \(\tilde\alpha_{t,i}\). Add the ETF's solo sale threshold
\(\hat x^s_E(z')=(\mu_{1,E}+\kappa^-_E)/(\gamma\Sigma_{1,EE})\), the aggregate need over every instrument,
and the liquidity \(\mathrm{liq}(z')=h^+_0+(1-\kappa^-_E)(g_E(z')p_0-\hat x^s_E(z')^+)^+\), today's cash
plus the ETF's sale proceeds down to that threshold.

(i) *Two shared scalars.* Every fund's root holding is Proposition 47's
clip at the root's exposure price \(m_0\) and the dynamic cash price \(\hat\eta_0\),
with its incumbent value \(S_i\) added to its net alpha. Given the vector
of incumbent values, the funds couple only through \(m_0\) and \(\hat\eta_0\).

(ii) *The aggregate no-reserve check.* If \(\mathrm{liq}(z')\geq\mathrm{need}(z')\) at a state,
\(\eta_1(z')=0\) is admissible there; if it holds in every state, some admissible
family has \(\eta_1=0\) everywhere, so \(\hat\eta_0=\eta_0\) and every incumbent value lies
in Proposition 26's bracket, and with positive cash today every
family does. This strengthens Propositions 51 (i) and 53 (ii) by
counting the ETF's sale proceeds and summing the need over the funds.
The largest need is the reserve's ceiling, and
\(\max_{z'}\mathrm{need}(z')\leq\sum_i\max_{z'}\mathrm{need}_i(z')\), with equality when one state attains every
instrument's maximum.

(iii) *What fails fund by fund.* If fund \(i\) trades strictly inside its
box in the same direction at the dynamic and the myopic roots, with
slope \(\kappa\),

$$
a^{\rm dyn}_{0,i}-a^{\rm my}_{0,i}=\frac{S_i+r_i(m^{\rm dyn}_0-m^{\rm my}_0)-(\hat\eta_0-\eta^{\rm my}_0)(1+\kappa)}{\gamma v_i}:\tag{172}
$$

the fund's own residual, corrected by the changes in the two shared
prices, which are the same for every fund and can flip its sign. At a
state whose budget binds, the cash price is one number for all funds,
so a rule that prices each fund's reserve with its own cash price is
wrong whenever two funds would buy there with liquidity short.

(iv) *The reserve.* The reserve at par, \(R=(p_0+h^+_0)^{\rm dyn}-(p_0+h^+_0)^{\rm my}\),
equals the funds' holdings forgone plus the cost difference,

$$
R=\sum_i\bigl(a^{\rm my}_{0,i}-a^{\rm dyn}_{0,i}\bigr)+\bigl[C(u^{\rm my}_0)-C(u^{\rm dyn}_0)\bigr],\tag{173}
$$

and is bounded by (172)'s numerators over \(\gamma v_i\) plus the cost difference;
it can be negative when the dynamic policy front-loads funds. With
every state covered the bound has no cash-price terms.

Part (i) substitutes the incumbent values into Proposition 47's
one-review reduction. Part (ii) builds a feasible tomorrow without the
budget from the ETF's sale down to its solo threshold. Part (iii)
subtracts the two roots' fund lines on a common trading piece. Part
(iv) is the wealth identity with the clip's Lipschitz bound.

A shared reserve therefore pools across funds only through the states:
the ceiling is the worst state's aggregate need, and what the cash
price weighs is that state's probability. Several ETFs, and a bound on
the exposure price's change in the inputs, are not treated.

Propositions 50-54 have one ETF. The last result takes many funds and
many ETFs and asks whether spanning separates the flexibility problem
as it separates the one-review problem (Propositions 27 and 45).

**Proposition 55 (Many funds and many ETFs over two reviews: the two-number structure, and spanning separates the root's lines given the tomorrow numbers; the two-review model with \(N\) funds and \(M\) ETFs, finite law; machine checked, with necessity of the lines conditional on the polyhedral Karush-Kuhn-Tucker theorem and the failure with costly ETFs a reading).**
Take Proposition 50's model with \(N\) funds, \(M\) ETFs and \(K\) factors.

(i) *Two numbers per instrument, one cash price.* A policy is optimal
exactly when tomorrow's lines hold in every state and every
instrument's root line holds with the dynamic cash price \(\hat\eta_0\) and its
own incumbent value \(S_i\), as in (162). Given \((S,\hat\eta_0)\), the root lines are
the one-review lines with \(\mu_0\) replaced by \(\mu_0+S\) and the cash price by
\(\hat\eta_0\); nothing couples the instruments beyond the one-review coupling.

(ii) *Spanning separates the lines.* With \(M=K\), \(B^E\) invertible
(\(R=(B^E)^{-1}\), netting vectors \(r_i\)), frictionless residual-free ETFs without
fees, a diagonal fund covariance, and today's budget slack with the
ETFs strictly inside their boxes at the dynamic root, write

$$
\hat\lambda^{\rm res}=\hat\lambda+R\bigl(S_E-\hat\eta_0\mathbf 1\bigr),\qquad
\alpha^{\rm res}_i=\hat\alpha_i+S_{A,i}-r_i^\top S_E-\hat\eta_0\bigl(1-r_i^\top\mathbf 1\bigr).\tag{174}
$$

Then the dynamic root is Proposition 45 (ii)'s optimum at these tilted
inputs:

$$
\begin{aligned}
&\gamma\tilde\Sigma_{f,0}b_0=\hat\lambda^{\rm res},\qquad x^E_0=R^\top(b_0-B^{A\top}x^A_0),\\
&x_{0,i}=\mathrm{clip}\Bigl(x^-_{0,i},\frac{\alpha^{\rm res}_i-(1+\hat\eta_0)\kappa^+_i}{\gamma v_i},\frac{\alpha^{\rm res}_i+(1+\hat\eta_0)\kappa^-_i}{\gamma v_i}\Bigr)\text{ in }[0,\bar x_i].
\end{aligned}\tag{175}
$$

So, given the tomorrow numbers at the optimum, the root's optimality
conditions separate into an *ETF reserve problem*, the frictionless
exposure at a premium tilted by the ETFs' incumbent values net of the
cash price, and a *fund alpha problem*, each fund's clip at a residual
alpha that carries its own incumbent value, less the netting-weighted
ETF incumbent values, less the cash price on its net cash. The tomorrow
numbers are set by the whole root, so the two problems share them and
are a fixed point, not two independent problems as at one review.

(iii) *The ETFs' interaction.* The exposure departs from the untilted
target by

$$
\gamma\tilde\Sigma_{f,0}\bigl(b_0-b^{\rm TB}\bigr)=R\bigl(S_E-\hat\eta_0\mathbf 1\bigr),\qquad
S_{E,j}-\hat\eta_0=\beta\,\mathbb E\bigl[(g_{E,j}-1)\eta_1\bigr],\tag{176}
$$

since frictionless ETFs have zero slope tomorrow: the ETFs share the
reserve only through the factor covariance's inverse, and those marked
up in the states where cash is dear are held as the reserve. With one
ETF this is Proposition 53's shift.

(iv) *Where separation fails.* With costly ETFs, or an ETF at a bound
today, the root is Proposition 41's one-review problem at the tilted
inputs, whose fund lines carry the ETFs' statuses: the lines fail to
separate exactly as at one review. With one ETF, Proposition 47's
two-scalar reduction holds at the root.

Part (i) is Proposition 50's argument, which never used the number of
instruments. Part (ii) substitutes the tilted inputs into Proposition
45 (ii); sufficiency is direct, and necessity reads the lines at an
optimum with today's budget slack. Part (iii) solves (175)'s exposure
equation and uses \(t_{1,E}=0\).

Spanning thus still splits the manager's question into exposure and
alpha, but over two reviews the split is of the optimality conditions,
not of the optimization: both halves read the same tomorrow numbers,
which depend on the whole of today's holdings. Separation in the
optimization itself, and many ETFs with costs, are not treated.

Propositions 51, 53 and 54 test tomorrow's funding state by state and
ask that every state be covered. The last result states the test for
the full menu, lets a stated fraction of states fail, and bounds what
repeated one-review optimization then loses, in the inputs.

**Proposition 56 (A flexibility test for the full menu, and the loss of repeated one-review optimization; the two-review model with \(N\) funds and \(M\) ETFs, finite law; machine checked, with the multipliers' existence conditional on the polyhedral Karush-Kuhn-Tucker theorem and the one-ETF form of the band term at paper level).**
Take Proposition 55's model, with tomorrow's predictive covariance
entrywise nonnegative in every state. At today's holdings \(x_0\) and cash
\(h\), take (164)'s solo targets, need and cash-price bound \(\bar\eta\) over every
instrument, each ETF's solo sale threshold \(\hat x^s_E(z')\) as in Proposition
54, and write

$$
\begin{aligned}
&\mathrm{liq}(z')=h+\sum_E(1-\kappa^-_E)\bigl(g_E(z')x_{0,E}-\hat x^s_E(z')^+\bigr)^+,\qquad
D(z')=\bigl(\mathrm{need}(z')-\mathrm{liq}(z')\bigr)^+,\\
&T_\varepsilon(Y)=\min_c\Bigl[c+\frac{\mathbb E(Y-c)^+}{\varepsilon}\Bigr],\quad\varepsilon\in(0,1],
\end{aligned}\tag{177}
$$

the *liquid reserve*, today's cash plus every ETF's sale proceeds down to
its solo sale threshold net of its rate; the *shortfall*; and the tail
measure of Rockafellar and Uryasev at level \(1-\varepsilon\)
(`rockafellar2000optimization`, audited for the ledger).

(i) *Coverage.* If \(\mathrm{liq}(z')\geq\mathrm{need}(z')\), then \(\eta_1(z')=0\) is admissible at
\(z'\): tomorrow's budget is slack there.

(ii) *The quantile test.* For \(\varepsilon\in[0,1)\) the test *passes at level* \(\varepsilon\)
when the shortfall's \((1-\varepsilon)\)-quantile is zero, equivalently
\(\Pr(D(z')>0)\leq\varepsilon\): at most a fraction \(\varepsilon\) of tomorrow's states are
uncovered. When the liquid reserve does not depend on the state, this
reads \(\mathrm{liq}\geq\mathrm{VaR}_{1-\varepsilon}(\mathrm{need})\). At \(\varepsilon=0\) it is Proposition 54 (ii)'s
all-states check. Whenever the test passes at a level \(\varepsilon>0\),
\(\mathbb E[\bar\eta D]=\varepsilon T_\varepsilon(\bar\eta D)\leq\varepsilon\max_{z'}\bar\eta D\).

(iii) *The loss bound.* Let \(S_i=\beta\mathbb E[g_it_{1,i}]\) be the incumbent values at
the myopic root's *relaxed* tomorrow, with tomorrow's budget dropped,
and take \(D\) and the uncovered fraction \(\varepsilon\) at the myopic root
\((x^{\rm my}_0,h^{\rm my})\). With \(V^{\rm dyn}\) the dynamic optimum's value and \(J(x^{\rm my}_0)\)
the repeated one-review policy's,

$$
\begin{aligned}
V^{\rm dyn}-J(x^{\rm my}_0)&\leq\tfrac12S^\top(\gamma\Sigma_0)^{-1}S+\beta\,\mathbb E\bigl[\bar\eta(z')D(z')\bigr]\\
&\leq\frac{\beta^2}2\bigl\|(\gamma\Sigma_0)^{-1}\bigr\|\sum_i\bigl(\mathbb E[g_i]\max(\kappa^+_i,\kappa^-_i)\bigr)^2+\beta\varepsilon\,T_\varepsilon(\bar\eta D),
\end{aligned}\tag{178}
$$

a *band term* plus a *tail term*, with the operator norm, the tail term
read as zero at \(\varepsilon=0\). The second line is in the inputs and needs no
solution of tomorrow's problems. At \(\varepsilon=0\) only the band term remains,
second order in the rates. With one ETF and the funds' incumbent
values zero, the band term is \(S_E^2/(2\gamma\Sigma_{EE\cdot F})\), with \(\Sigma_{EE\cdot F}\) the ETF's
variance net of its regression on the funds; it equals Proposition
53's cost-channel shift times \(S_E/2\) only with the funds fixed or
uncorrelated with the ETF.

Part (i) builds a fundable tomorrow without the budget, as in
Proposition 54 (ii), selling each ETF down to its threshold. Part (ii)
reads the quantile on the finite law; when \(\Pr(Y>0)\leq\varepsilon\) the tail
objective's least value is \(\mathbb E[Y]/\varepsilon\), attained at \(c=0\). Part (iii) bounds
the dynamic value by the relaxed problem, whose gain over the myopic
root is at most the completed square of Proposition 48 by today's
strong concavity and the relaxed tomorrow's supergradient \(S\); and it
bounds the myopic policy's loss from tomorrow's budget by the
Lagrangian at the cash price \(\min(\eta_1,\bar\eta)\), which costs nothing in
covered states.

A manager can therefore sort tomorrow's states by how far the
purchases they call for exceed the cash plus what the ETFs would fetch.
If at most a fraction \(\varepsilon\) are short, re-optimizing each quarter with
bands loses at most a term of second order in the rates plus \(\varepsilon\) times
the short states' average cash-price bound times the shortfall. The
bound takes premia and alphas as fixed; the test with time-varying
premia is not treated here.

Propositions 50-56 take premia and alphas as fixed and learned, so the
target moves only because beliefs are revised. The last result lets
them move on their own.

**Proposition 57 (The predictable and unpredictable target move under time-varying premia and alphas; Proposition 52's model with a state equation, one fund and one ETF over two reviews, finite law; machine checked in the decomposition, the width's direction, the tilt's probabilities and the one-coordinate front-loading with its threshold, with the case of a free ETF, the planned purchase, the transfer and the steady-state filter's form at paper level).**
Take Proposition 52's model and let premia and alphas follow
\(\theta_{t+1}=\Phi\theta_t+(I-\Phi)\bar\theta+w_{t+1}\), with persistence \(\Phi=\mathrm{diag}(\phi_\lambda,\phi_\alpha)\), long-run mean \(\bar\theta\)
and state noise of covariance \(Q=\mathrm{diag}(q_\lambda,q_\alpha)\), not both \(\Phi=I\) and \(Q=0\). The
filter carries the mean \(m_t\), the variance \(P_t\) entering review \(t\) and \(P^u_t\)
after its update, the gain \(K_t\) and the innovation \(\nu_{t+1}\); \(G\) maps the state
to the instruments' expected returns, \(\mu_t\) and \(\Sigma_t\) are the predictive
moments, \(x^*_t=(\gamma\Sigma_t)^{-1}\mu_t\) is the target, and \(c_t=\gamma\Sigma_{t,ii}\) an instrument's
curvature.

(i) *Two parts.* \(x^*_1-x^*_0=\Delta^p_0+\Delta^u_1\), with

$$
\begin{aligned}
&\Delta^p_0=(\gamma\Sigma_1)^{-1}G(\Phi-I)(m_0-\bar\theta)+\bigl[(\gamma\Sigma_1)^{-1}-(\gamma\Sigma_0)^{-1}\bigr]\mu_0,\qquad
\Delta^u_1=(\gamma\Sigma_1)^{-1}G\Phi K_0\nu_1,\\
&\mathbb E\,\Delta^u_1=0,\qquad
\mathrm{Cov}\,\Delta^u_1=(\gamma\Sigma_1)^{-1}GV_0G^\top(\gamma\Sigma_1)^{-1},\qquad V_0=\Phi(P_0-P^u_0)\Phi^\top.
\end{aligned}\tag{179}
$$

The *predictable* part \(\Delta^p_0\) is known today, since \(\Sigma_1\) is deterministic;
it has two sources, the pull toward \(\bar\theta\) at rate \(I-\Phi\) and the change in
the risk charge, which now has either sign. The *unpredictable* part \(\Delta^u_1\)
is centred, with the filter's propagated innovation covariance.

(ii) *The static width's direction.* \(\Sigma_1-\Sigma_0=G(P_1-P_0)G^\top\) with
\(P_1-P_0=Q-(P_0-\Phi P^u_0\Phi^\top)\). An instrument's static width \((\kappa^+_i+\kappa^-_i)/c_t\) of
Proposition 26 rises from \(t\) to \(t+1\) exactly when
\((G(Q-(P_t-\Phi P^u_t\Phi^\top))G^\top)_{ii}<0\). If learning removes more variance than the
state noise adds in both blocks, every width rises; if less, every
width falls; when the blocks move oppositely, the fund's and the ETF's
widths can move in opposite directions. Each block's variance recursion
converges monotonically to a fixed point, unique when \(q>0\) or \(\phi^2<1\), at
which the widths are constant.

(iii) *The band leans toward the predictable move.* In Proposition 26's
coarse regime the band is the static band shifted by
\(\tau_t=\beta(\kappa^+U-\kappa^-D)/c_t\), with \(U=\Pr(\Delta^u_{t+1,i}>-\Delta^p_{t,i})\) and \(D=\Pr(\Delta^u_{t+1,i}<-\Delta^p_{t,i})\).
With a symmetric innovation law and \(\kappa^+=\kappa^-=\kappa\), \(\tau_t\) has the sign of \(\Delta^p_{t,i}\)
(or is zero) and, without an atom at \(-\Delta^p_{t,i}\),
\(|\tau_t|=\beta\kappa\Pr(|\Delta^u_{t+1,i}|\leq|\Delta^p_{t,i}|)/c_t\): the band leans toward the predictable
move by the probability that the innovation is smaller than the
predictable move, the full \(\beta\kappa/c_t\) when the move exceeds the innovation's support. With \(\Phi=I\)
and \(Q=0\) this is Proposition 31's tilt.

(iv) *Front- and back-loading.* Suppose the budget is slack today at the
dynamic and the myopic roots and tomorrow in every state, the ETF's
holding is fixed, \(\kappa^+_A>0\), and tomorrow's purchase edge exceeds the
myopic root's marked fund holding \(g_A(z')a^{\rm my}_0\) in every state. Then the
myopic tomorrow pins the fund's incumbent value at \(S_A=\beta\mathbb E[g_A]\kappa^+_A\), and
\(a^{\rm dyn}_0\geq a^{\rm my}_0\). At the dynamic root its own incumbent value satisfies
\(S^{\rm dyn}_A\leq\beta\mathbb E[g_A]\kappa^+_A\), so on a purchase

$$
\kappa^+_A-S^{\rm dyn}_A\ \geq\ (1-\beta\,\mathbb E[g_A])\,\kappa^+_A,\tag{180}
$$

with equality exactly when every state's slope tomorrow is \(\kappa^+_A\), the
fund bought, or held at its purchase edge, from the dynamic root's
marked holding. The predictable rise is bought today at a threshold cut
by at most \(\beta\mathbb E[g_A]\kappa^+_A\), because tomorrow would pay the rate anyway; since
a larger holding makes tomorrow's purchase less likely, the full cut is
the exception. A predictable fall is the mirror, with \(\kappa^-_A>0\),
\(a^{\rm dyn}_0\leq a^{\rm my}_0\) and the sale threshold. With the ETF free, the sign of the
fund's move is (172)'s: \(S_A\) corrected by the changes in the exposure and
cash prices, so the ETF's own predictable move can offset the fund's.

(v) *The planned purchase.* Tomorrow's solo target for the fund is
\(\hat x_A(z')=(\mu^p_{1,A}+(G\Phi K_0\nu_1(z'))_A-\kappa^+_A)^+/(\gamma\Sigma_{1,AA})\), with
\(\mu^p_1=G(\Phi m_0+(I-\Phi)\bar\theta)-(0,c^E)\) tomorrow's *predictable mean*. The need (164)
at \(\nu_1=0\) with the worst marking, the *planned purchase*
\((1+\kappa^+_A)(\hat x^p_A-g^{\min}_Aa_0)^+\) with \(\hat x^p_A=(\mu^p_{1,A}-\kappa^+_A)^+/(\gamma\Sigma_{1,AA})\), is a base set by
the predictable mean; the innovation contributes the rest of the need
(the positive parts do not split in general). Propositions 53-56 read
with this need: the reserve prices the unpredictable part, through the
innovation covariance in (179), while the predictable part is
front-loaded when today's budget is slack or, when it binds, is a
planned purchase that tomorrow's liquidity must cover, best provided by
the ETF's sale since its size is known today. A predictable fall beyond
the innovation's support needs no reserve.

(vi) *What transfers.* The one-review results hold at each review.
Propositions 50, 51, 53 and 54 hold verbatim on the finite tree, which
the state equation changes only through the law of tomorrow's moments.
Proposition 26's band holds at every review with \(c_t\) from the variance
path, its tilt given by (iii). Proposition 31's rising width and outward
drift hold for an instrument only while (ii)'s condition does, that is,
while learning outweighs the state noise; in the steady state the width
is constant and learning does not end the coarse regime. Under
quadratic costs the aim's structure is Proposition 34 (iii)'s, as a
structure, not a policy.

Part (i) is the filter's predict-and-update algebra. Part (ii) writes
the variance change and uses that each block's recursion
\(p\mapsto\phi^2ps/(p+s)+q\) is increasing, concave and bounded. Part (iii) is
Proposition 26's tilt with the learning drift replaced by \(\Delta^p\). Part (iv)
places the root objective below the myopic root's tangent plane with
slopes \(S\), pins \(S_A\) from the myopic tomorrow's purchases, shows every
smaller holding lowers the root objective strictly, and bounds \(S^{\rm dyn}_A\) by
the bracket \(s_A\leq\kappa^+_A\). Part (v) substitutes \(\mu_1\) into (164). Part (vi)
checks each result's hypotheses against the state equation.

So when the target moves on its own, its next move splits into the
part known today and the surprise. The known part tilts the band
toward it and, when tomorrow would trade anyway, is traded today
instead, or else is a purchase to plan cash for; the surprise is what
a reserve is for, sized by its dispersion as before. The exact
posterior with a state transition and several ETFs under the state
equation are not treated here; the flexibility test with time-varying
premia is the next result.

Proposition 56's test takes premia and alphas as fixed. The last
result combines it with Proposition 57's split of tomorrow's need.

**Proposition 58 (The quantile flexibility test with time-varying premia, and the timing of the planned purchase; Proposition 57's model with one fund and one ETF over two reviews, finite law; machine checked in the split test, the bound at any holding and the pinned incumbent value, with the front-loaded point's zero residual conditional on the polyhedral Karush-Kuhn-Tucker theorem at paper level, and the assembly of (183), the mirror, the front-loading reading and the Gaussian quantile at paper level).**
Take Proposition 57's model and Proposition 56's objects at today's
holdings \(x_0\) and cash \(h\): the need (164), the liquid reserve, the
shortfall \(D\), the bound \(\bar\eta\) and the tail measure \(T_\varepsilon\) of (177). With
tomorrow's predictable mean \(\mu^p_1\) of Proposition 57 (v) and \(g^{\min}\) the
smallest gross return on the support, write

$$
\hat x^p_i=\frac{(\mu^p_{1,i}-\kappa^+_i)^+}{\gamma\Sigma_{1,ii}},\qquad
\mathrm{PP}(x_0)=\sum_i(1+\kappa^+_i)\bigl(\hat x^p_i-g^{\min}_ix_{0,i}\bigr)^+,\qquad
\Delta(z')=\mathrm{need}(z')-\mathrm{PP}(x_0),\tag{181}
$$

the *planned purchase*, the need at zero innovation with the worst
marking, known today, and the *innovation-driven part*, of either sign.
For a holding \(x_0\) in today's feasible set \(C\) with cash \(h(x_0)\), the *root
residual* \(\rho(x_0)\) is the shortest vector, in the norm of \((\gamma\Sigma_0)^{-1}\), of
the form \(g_0(x_0)+S-l\). Here \(S\) ranges over the admissible incumbent
values at the relaxed tomorrow from \(x_0\), tomorrow's budget dropped,
where an instrument held at a bound tomorrow has any slope in the
interval its one-sided line cuts from \([-\kappa^-_i,\kappa^+_i]\); and \(l\) ranges over
today's line values \(\eta\mathbf 1+(1+\eta)t+n\), with \(\eta\geq0\) (zero when \(h(x_0)>0\)), \(t\) in
today's trade-sign slope sets and \(n\) in the box's normal cone.

(i) *The test in split form.* Proposition 56 holds on this model's tree
verbatim. The test at level \(\varepsilon\) passes exactly when
\(\Pr(\Delta(z')>\mathrm{liq}(z')-\mathrm{PP}(x_0))\leq\varepsilon\), and, with a reserve that does not depend on
the state, exactly when \(\mathrm{liq}-\mathrm{PP}(x_0)\geq\mathrm{VaR}_{1-\varepsilon}(\Delta)\): the liquid reserve
covers the planned purchase in full and the \((1-\varepsilon)\)-quantile of the
innovation-driven part.

(ii) *The loss bound at any holding.* For every \(x_0\) in \(C\), with \(D\), \(\bar\eta\) and
\(\varepsilon\) at \((x_0,h(x_0))\) and \(J(x_0)\) the value of holding \(x_0\) today and
optimizing tomorrow,

$$
V^{\rm dyn}-J(x_0)\leq\tfrac12\rho(x_0)^\top(\gamma\Sigma_0)^{-1}\rho(x_0)+\beta\,\mathbb E\bigl[\bar\eta(z')D(z')\bigr].\tag{182}
$$

At the myopic root the band term is at most Proposition 56's, so (182)
contains (178). At the *front-loaded point* \(x^s_0\), the relaxed two-review
optimum, \(\rho(x^s_0)=0\); under the test at a level \(\varepsilon>0\) there,
\(V^{\rm dyn}-J(x^s_0)\leq\beta\varepsilon T_\varepsilon(\bar\eta D)\). Front-loading the planned purchase removes
the band term and leaves the uncovered states' loss.

(iii) *The pinned band term.* If today's budget is slack at the myopic
root and tomorrow's in every state, \(\kappa^+_A>0\), and the fund is bought in
every state tomorrow from the myopic root's marked holding, then
\(S_A=\beta\mathbb E[g_A]\kappa^+_A\) exactly, and the band term at the myopic root is

$$
\tfrac12S^\top(\gamma\Sigma_0)^{-1}S=\frac{(\beta\mathbb E[g_A]\kappa^+_A)^2}{2\gamma\Sigma_{0,AA\cdot E}}+S_AS_E\bigl[(\gamma\Sigma_0)^{-1}\bigr]_{AE}+\tfrac12S_E^2\bigl[(\gamma\Sigma_0)^{-1}\bigr]_{EE},\qquad
\Sigma_{0,AA\cdot E}=\Sigma_{0,AA}-\frac{\Sigma_{0,AE}^2}{\Sigma_{0,EE}}.\tag{183}
$$

The fund's part is the discounted marked purchase rate squared over
twice its curvature net of the ETF: the price of not front-loading a
rise that tomorrow buys anyway. A fall sold in every state is the
mirror, with \(\kappa^-_A\).

Part (i) rewrites Proposition 56's test with the need split. Part (ii)
runs Proposition 56's proof at any holding: every admissible slope
family gives a supergradient of the relaxed continuation, and the
completed square is taken about the nearest line value, so the bound
holds for every admissible choice and therefore at the minimum; at the
front-loaded point the relaxed program's optimality conditions select a
choice with zero residual. Part (iii) is Proposition 57 (iv)'s pinned
value read in the block inverse.

Which point to hold is decided by the two bounds, both in the inputs
once the relaxed tomorrow is solved. When the test passes at a small
level at the front-loaded point, front-loading is adequate. When
today's cash is short, the front-loaded point spends cash the uncovered
states would want, and the myopic root can do better: in the check's
four tight instances the front-loaded point's realized loss exceeded
the myopic policy's, while both bounds held. Front-loading the planned
purchase as far as the test still passes is a reading, not a result.
The Gaussian quantile, several ETFs under the state equation and more
reviews are not treated.

## 4. Related work

Propositions 1--3 unfold self-financing accounting, bilinearity and
finite averaging. Proposition 4 applies compact-set attainment;
Proposition 5 applies bounded linear-image feasibility; and
Proposition 6 is a numerical use of Proposition 1. Proposition 11
applies finite-horizon dynamic programming and compact attainment.
These are supporting facts, not new general theorems. The portfolio
specificity lies in the common funded action classes and in what
their comparison does and does not establish.

Gârleanu and Pedersen solve a dynamic trading problem with predictable security returns and
quadratic transaction costs. Their policy trades partway toward a position that incorporates
future expected returns. The solved control problem chooses positions in a directly tradable
security universe without the funded, long-only ETF-only action class considered here.
Accordingly, that policy provides a comparison for dynamic trading, while the comparison
between ETF-only and full-trading feasible exposure sets remains a separate question
(`garleanu2009dynamic`, full text reviewed).

Gallien, Kassibrakis and Malamud study an illiquid, alpha-generating fund hedged with a
liquid futures contract. With a lower bound on terminal wealth and small proportional costs
for trading the fund, they derive an approximate region in which the fund position is left
unchanged. Their continuously traded futures hedge differs from a funded, long-only ETF
adjustment made at a quarterly review. We have not established that their result is a
limiting case of the model here (`gallien2018hedge`, full text reviewed).

Bichuch and Guasoni solve a continuous-time, infinite-horizon CRRA problem with a risk-free
asset, a liquid index, and one illiquid asset with expected excess return
\(\mu_2=\beta_2\mu_1+\alpha\) and small proportional trading costs. With positive
idiosyncratic risk, their zero-alpha result says that the illiquid asset is never worth
holding. It is a benchmark for a zero-alpha limiting case, but does not establish a
liquidation rule in Section 2's model: their assets are not exact return replicas,
whereas that model permits exact
replication, an incumbent active holding with sale costs, and ETF position limits that
can obstruct replacement. Their model also has no funded long-only restriction or
belief uncertainty in \((\alpha,\beta)\), and uses one illiquid instrument rather than an
ETF-versus-active-fund menu with several factors (`bichuch2014investing`, full text
reviewed). Proposition 8 supplies a limited one-quarter analogue: when ETF
replacement is feasible and costless, belief-mean alpha is zero, and
the ETF shock has zero cross-moment with the fund-minus-ETF shock, a
zero-active full optimum exists. With no incumbent, its score equals
the ETF-only optimum; with a free active sale and positive penalized
residual-difference variance, every full optimum liquidates the fund.
Costly incumbent sales can instead preserve a zero-alpha holding,
costless exact replication can leave ties, and an ETF limit can block
replacement. Independent ETF tracking noise can also make a
zero-alpha active holding optimal through diversification: the
cross-moment assumption fails in the exact example accompanying
Proposition 8. Zero alpha against the specified economic factors
does not mean zero expected return advantage against a tradable,
noisy ETF;
the latter benchmark changes both the mean and risk comparison.
These are obstructions in the funded one-quarter model to an
unqualified transfer,
not counterexamples to the source's long-run result.

Dai, Jin and Liu study a finite-horizon fund manager with a risk-free asset, a liquid
stock, and an illiquid stock subject to exogenous position limits and proportional costs,
with fixed, known return parameters and no alpha/premium decomposition. Their trading
boundaries are monotone in the position limits, and a limit not currently binding can
still affect current trading through its anticipated future binding. Neither the ETF
span restriction nor belief uncertainty appears in their model (`dai2011illiquidity`,
full text reviewed). Proposition 12 has no extra position limit:
it compares initial active-trade advantages under matched future
trading menus after a public signal reveals factor premia, including
a factor direction unavailable through the ETF. The fund's alpha is
known to be zero in that example.
Its opposite continuation effects come from the future trading
opportunities, not an anticipated binding position limit or
learning about manager skill.

Liu and Muhle-Karbe study one risky asset with small proportional trading costs
and a binding upper portfolio constraint. Their no-trade boundaries depend on
that constraint, and the region's leading-order width changes from the
unconstrained cubic-root scale to a square-root scale in the spread
(`liu2013portfolio`, Theorem 2.3, full text reviewed). This is a
precedent for a constraint changing a no-trade band beyond the traded asset's
own cost. Its continuous-time, infinite-horizon, single-risky-asset problem
does not characterize a quarterly funded investor's active-trade boundary
after optimizing an ETF menu. Proposition 9 gives that one-quarter boundary
as an exact interval in the active belief mean, conditional on fixed other inputs.
For an interior active position, its algebraic width depends on active buy and
sell costs and the endpoints of the compatible ETF budget-multiplier interval.
That interval reflects ETF trade kinks, position bounds and cash funding. Its
position-bound cases differ from the cited dynamic boundary; the qualitative
effect of a binding constraint on a no-trade region is already known from this
precedent. Proposition 10 illustrates degeneracy
of parametric optimization: at the coincident ETF cap and cash-exhausting
purchase, compatible budget multipliers form an interval; a positive
cost moves the optimum off the cap and pins the multiplier. Its
knife-edge narrowing contradicts a common heuristic that higher
costs widen a no-trade band, not any cited theorem. It does not
imply a robust effect or a narrowing of the dynamic holding bands
studied in these sources.

Pástor and Stambaugh combine fund and passive-index return histories with prior beliefs
about pricing and manager skill. Their portfolio may include active funds even when the
investor believes managers cannot outperform passive indexes. They distinguish pricing-model
error from skill, and report that their sampled fund universe has no close substitutes
for the pricing-model benchmarks. Their portfolio is selected jointly; they do not
analyze a factor-allocation stage followed by manager selection or compare an ETF-only
adjustment to full trading under Section 2's common funded budget (`pastor2002investing`,
full text reviewed). Platanakis, Sutcliffe and Ye study asset allocation followed by
stock selection within asset classes. Under a common idiosyncratic variance,
their Proposition 1 gives formulas for the expected-loss difference between
mean-variance and equal weighting, separating an alpha-driven component and
specifying when idiosyncratic variance changes each component in a given
direction. This is a formal comparison of methods used within an
already-fixed two-stage procedure. They explicitly do not compare one-stage with
two-stage portfolio formation, so the result gives neither conditions for the
staged procedure to recover a joint optimum nor a bound on the loss from staging
(`platanakis2019horses`, Proposition 1, full text reviewed).

Proposition 22's two-stage procedure has classical precedents in
which separation is exact. Treynor and Black combine an active
portfolio with a passive index in "an idealized world in which there
are no restrictions on borrowing, or on selling securities short"
(`treynor1973security`, p. 67, full text reviewed). Positions in
the analyzed securities are taken "purely on the basis of expected
independent return and variance", and an explicit market position
complements the market exposure those positions accumulate
(equations (13) and (16)). Merton's mutual-fund
theorems derive two-fund separation for mean-variance investors,
with borrowing and short sales allowed (`merton1972analytic`,
Theorems I and II, full text reviewed). Cass and Stiglitz treat
separation as a property under which a few mutual funds span every
investor's relevant opportunities (`cass1970structure`, full text
reviewed). Tobin's analysis of several non-cash assets keeps holdings
nonnegative with total at most one, so it has no borrowing
(`tobin1958liquidity`, Section 3.6, full text reviewed). None of
these gives a loss bound for a first stage restricted to funded,
long-only exposures. In Proposition 22, an unrestricted first stage
has a zero multiplier, and the soft procedure then coincides with the
joint problem. The funded, long-only budget is what makes the
multiplier nonzero, and the loss bound is the value of that
multiplier, an application of weak duality. Proposition 23's flat
case is the Treynor–Black world read in these terms: residuals
uncorrelated with the market (their equation (2)) and an explicit
market position free in sign, which "may, of course, be negative,
requiring an explicit position in the market that is short"
(equation (16), p. 72), net any exposure the residual choice
carries. Its three funded failures remove those assumptions one at
a time: no short netting position, no unrestricted borrowing, and
no frictions. Tobin's no-borrowing budget suggests that the
shared-budget failure bites where cash binds, not from the absence
of borrowing as such.

Jones and Shanken model fund alphas through a shared population distribution
with fund-specific deviations, so information about one fund changes beliefs
about others (`jones2002mutual`, full text reviewed). That shared
component concerns manager skill, rather than a common factor-premium error.
Barras, Scaillet and Wermers use false-discovery control to estimate the
fractions of unskilled, zero-alpha and skilled funds in the presence of
dependence across estimated alphas (`barras2010false`, full text reviewed).
These are distinct ways to handle cross-fund estimation uncertainty; neither
gives the funded ETF-versus-active decision in Section 2 or shows that a one-quarter
belief-average score responds to belief dispersion at fixed means. Proposition 12
instead learns factor premia with known zero manager alpha. Proposition 13
allows uncertain alpha, but its witness policies use only the revealed factor
regime. Neither result separates the effects of learning about manager alpha
and factor premia on the active-trading decision.

Estimation uncertainty and trading costs are also studied jointly elsewhere: DeMiguel,
Martín-Utrera and Nogales analyze multiperiod losses and shrinkage policies
(`demiguel2013parameter`); Olivares-Nadal and DeMiguel express a turnover norm as
the worst mean-error loss in the trade direction over a dual-norm uncertainty set,
including an ellipsoidal case, and relate this to regularized and Bayesian
portfolio problems (`olivaresnadal2018technical`, Proposition 1, full text
reviewed); and Hautsch and Voigt connect turnover penalties with covariance
shrinkage under model uncertainty
(`hautsch2017large`; all full texts reviewed). Garlappi, Uppal and Wang use multiple
priors to represent ambiguity aversion about expected returns (`garlappi2005portfolio`,
full text reviewed). These cost and uncertainty results optimize a single action class;
they do not supply a comparison with the best feasible ETF-only action. Section 2's
one-quarter belief-average score depends on the belief mean alone, as Proposition 3
states; it does not implement their robust or multiperiod objectives.

Palczewski and coauthors give a numerical method for a dynamic portfolio problem with
state-dependent drift and proportional trading costs, rather than a closed-form
no-active-trade boundary (`palczewski2013dynamic`, full text reviewed). Petrik, Chow and
Ghavamzadeh compare a candidate policy with a fixed baseline under the same
uncertain transition model, before minimizing their performance difference.
They bound loss relative to the true optimum, exhibit tightness of that bound,
and prove their robust comparison is computationally hard
(`petrik2016safe`, Definition 2 and Theorems 5 and 6, full text reviewed).
Shared uncertainty and paired subtraction therefore have a direct precedent.
Their fixed-baseline decision process does not compare a candidate portfolio
with the best feasible ETF adjustment under one funded budget or give a
sampling-information lower bound for that decision. Howard and coauthors
give time-uniform confidence boundaries for sequential estimation; their theorem does
not by itself cover a changing latent conditional mean or establish a portfolio
decision rule. A specified process scale is required to apply the
stitched boundary in that theorem (`howard2021time`, Theorem 1,
full text reviewed).

For bounded independent and identically distributed observations,
Maurer and Pontil bound a
mean using the sample variance, without specifying the observation
law beyond a known range. Their finite-class extension controls
all members of a fixed finite function class by a union bound
(`maurer2009empirical`, Theorem 4 and Corollary 5, full text reviewed).
These are single-sample bounds for bounded variables. They offer a
general ingredient for an unknown-law comparison across finitely
many portfolio contrasts; they do not themselves certify an action
against a continuum of feasible ETF adjustments or control a rule
used at repeated reviews. The certificates of Propositions 15--18
instead calibrate to a known finite observation law; Proposition 19
uses only a known range.

Manski gives finite-sample bounds on the expected welfare of empirical treatment
rules in a binary-choice problem with bounded outcomes. The lower welfare bound
controls loss relative to the choice that knows the true mean outcomes,
but does not give a sample-size lower bound applying to every treatment rule
(`manski1999statistical`, Proposition, full text reviewed). Those bounds
concern expected welfare across samples, rather than the probability of a
false decision after a particular sample; both treatment outcome means are
unknown to the empirical rule. His adaptive minimax-regret rule uses
accumulated evidence to choose treatment allocations for successive
cohorts. Its per-cohort criterion does not establish a
finite-sample loss rate for a funded portfolio decision
(`manski2007adaptive`, Section 2.2, full text reviewed).

Mohajerin Esfahani and Kuhn size a Wasserstein ambiguity ball from independent
samples. Under their tail condition, the robust solution's worst-case cost bounds
its true expected cost with the stated confidence
(`esfahani2017data`, Theorem 3.5, full text reviewed). This one-sided
coverage statement applies to a data-selected decision. The ball's radius
also depends on concentration constants determined by tail conditions and
dimension; the displayed concentration theorem treats dimension two separately
(`esfahani2017data`, Assumption 3.3, Theorem 3.4 and equation (8), full text
reviewed). The guarantee does not compare the optimized full and ETF-only
classes under a common funded budget, nor give a matching lower bound on
the sample size needed for that comparison. The paper's one-quarter
belief-average score does not impose a Wasserstein ambiguity set.

Proposition 14 uses a two-law information comparison: equal funded
geometry and second moments leave different public-history likelihoods,
so they cannot determine the sharp certification power. Its exact
finite-law pair and the quantified gap for the prescribed gate are
the application here. The general fact that moments do not determine
a likelihood, and the use of two laws to bound testing power, are
not new statistical mechanisms.

Garivier and Kaufmann's best-arm-identification lower bound
optimizes information against alternative arm models and bounds
the expected stopping time of a fixed-confidence procedure
(`garivier2016optimal`, Theorem 1, full text reviewed).
Kaufmann, Cappé and Garivier give a divergence lower bound for
identifying the best arms in an identifiable bandit family
(`kaufmann2014complexity`, Theorem 4, full text reviewed).
The hardest-alternative logic, and inverse-square gap behavior in
regular mean models, behind Propositions 15--16 are therefore
established testing mechanisms. Those theorems concern adaptive
allocation and stopping
among a finite set of arms; the propositions here use fixed public
histories, known bounded finite laws and a funded ETF-only action
class. Neither cited theorem directly yields the stated portfolio
bounds or their constants. In particular, Proposition 15's
fixed-sample lower bound uses a two-law overlap inequality, while
its upper bound uses bounded-mean concentration. The adaptive
best-arm results are a benchmark for the mechanism, not the source
of either stated bound. The overlap step in Propositions 15--17 is
Le Cam's two-point method: the affinity of \(N\)-fold product laws
is the \(N\)-th power of the one-observation affinity, which bounds
their distance (`lecam1973convergence`, Lemma 1 and its proof, full
text reviewed). The propositions prove that step directly on finite
supports rather than citing it.

Proposition 15 converts a scalar premium-testing rate to an
economic score margin through funded exposure \(D\), with a fixed
ETF optimum and known zero alpha. Proposition 16 applies the
hardest-alternative idea when the ETF comparator switches between
cash and an ETF. Its specific two-direction variance calculation
uses both joint alpha/premium error directions, rather than only
the direction chosen at one estimate. The finite two-point
constructions and ellipsoidal upper penalties are standard
statistical tools. What is established here is their exact
application to these stated funded comparison classes, not a
new general lower-bound method or an optimal sampling policy.
The difficulty these rates express in premium units is the
classical one of estimating an expected return. In Merton's setting
of prices with a constant mean and variance in continuous time, the
precision of the estimated mean depends only on the calendar length
of the record, not on how often returns are sampled within it
(`merton1980estimating`, Appendix A, equation (A.3), full text
reviewed). The propositions here use quarterly records and define
no within-quarter returns, so that result is context, not an input.

The inverse-square dependence on the economic score margin in
Propositions 15 and 16 belongs to their stated fixed-action,
linear-gap families. Proposition 17 gives a distinct smooth-entry
family with a continuously moving, interior ETF optimum. Its
inverse-first-power economic-margin rate follows from the
quadratic map from active mean signal to optimized score advantage;
the underlying mean-testing rate remains inverse-square in the
signal. This conversion from a smooth mean signal to a
quadratic optimized-value gap is a fast-rate pattern, rather
than a new testing method. A full-text comparison has not determined
whether the specific quadratic-entry certificate is already a
corollary of an existing statistical-decision theorem.

Proposition 18 extends that certificate to directional costs
and binding constraints under positive definite return risk.
Its strong-concavity and optimized-value stability arguments
are standard mathematical tools; the class-level lower bound
still comes from Proposition 17's zero-cost family. The
constraint extension supplies neither a new statistical
method nor a lower bound for each costly, binding instance.
Whether the whole-ETF-class certificate follows from a general
optimization-sensitivity theorem has not been verified by a
full-text comparison.

Proposition 19 is an application of known tools. Its upper bound
is Hoeffding's inequality for bounded independent and identically
distributed variables (`hoeffding1963probability`, Theorem 1 and
the remark following it on variables in an interval \([a,b]\),
full text reviewed; restated as `maurer2009empirical`, Theorem 1),
with a union bound over the two comparator faces. Its lower bound is Proposition 16's two-point bound. The
empirical Bernstein bounds of Maurer and Pontil and the
time-uniform confidence sequences of Howard and coauthors are
variance-adaptive or sequential alternatives to the range bound
(`maurer2009empirical`, Theorem 4 and Corollary 5;
`howard2021time`, Theorems 1 and 4; full texts reviewed).
Proposition 19 implies that in its family they can improve the
worst-case history length by constants only; it does not analyze
their constants or give a time-uniform guarantee. Adaptive
best-arm identification over the two faces
(`garivier2016optimal`, `kaufmann2014complexity`) is the
sequential analogue of the maximum over faces; neither is used.
Proposition 24 generalizes the two-face reduction to any funded
menu with a linear score, using the linear-programming vertex
theorem (`bertsimas1997introduction`, Theorem 2.3, Corollary 2.1 and
Theorems 2.7--2.8; `schrijver1986theory`, Section 8; cited by
theorem number, texts not compared). Its curvature deficit is the
strong-concavity gap behind Proposition 18, and its reading, that
curvature rather than funding removes the finite reduction, is a
known perturbation mechanism.

The earlier feasibility and continuation examples have the
same boundary: Proposition 7 applies constrained replication
geometry, Proposition 8 depends on the chosen definition and
tradability of alpha's benchmark, and Propositions 12--13
illustrate continuation value from future flexibility and
learning. Their proved portfolios, signs and limits are the
paper's results; these general mechanisms are not claimed new.
That measured performance depends on the benchmark is itself a
known point. Roll shows that betas against an index that is not
mean-variance efficient need not line up with mean returns. For
every performance ranking obtained with such an index, another
non-efficient index reverses it (`roll1978ambiguity`, statements
S4 and S6, full text reviewed). Proposition 8's alpha is defined
against a stated factor benchmark and inherits that dependence.

Proposition 20's sandwich is the increasing-differences
comparison of monotone comparative statics. Topkis proves that
optimizer sets move monotonically with a parameter when the
objective has monotone differences in the choice and the
parameter and the constraint sets are ascending in the parameter;
his theorem is stated for minimizing submodular functions
(`topkis1978minimizing`, Theorem 6.1, full text reviewed).
Milgrom and Shannon restate that theorem for maximization and
characterize monotone maximizers by quasisupermodularity and the
weaker, ordinal single-crossing property (`milgrom1994monotone`,
Theorems 4 and 5, full text reviewed). Amir's survey gives a
version with box constraints whose endpoints increase in the
parameter, and shows that maximizing a supermodular function over
some coordinates of a fixed rectangle preserves supermodularity in
the rest (`amir2005supermodularity`, Theorems 8 and 11, full text
reviewed). Proposition 20 does not apply these theorems. It writes
the comparison as an inequality between four attained maxima and
shows that increasing differences fails in the funded two-review
model; it does not examine single crossing.

Their constraint hypotheses show where funding enters. The
continuation value under future ETF-only trading is a maximum over
the second-review ETF trade. That trade can buy at most the cash
left after the root trade, net of the purchase charge, and a root
purchase of the active fund reduces that cash one for one plus
costs. So the later choice's feasible range shrinks as the root
active holding rises, rather than being a fixed rectangle or
ascending. The general route from a supermodular objective to
increasing differences of the continuation value is therefore
unavailable here. The funded cap (58) is the value-side form of
that constraint, and it is elementary accounting rather than a
new mechanism.

The negative sign in Proposition 20's example comes from the value
of waiting to learn before committing. Merton's changing-expectations
examples show a related effect with a fixed menu: when future
returns are expected to become more favorable, an investor with
exponential utility holds less of the risky asset now and keeps
riskless wealth "as a reserve" for later investment
(`merton1971optimum`, Section 9, equation (129) and the discussion
following it, full text reviewed). There the opportunity set moves
while the menu is fixed. In Proposition 20 public information is
the same under every control and only the future menu changes.
The positive sign of Proposition 12 is not hedging demand either:
its family has no conditional return risk and reveals the
parameter at the first review, so future ETF adjustment gains
only by redeploying wealth into returns already known.
Gârleanu and Pedersen's signal persistence, which tilts today's
trade toward where a persistent predictor is heading, does not
arise, because the two-review model has fixed conditional means
(`garleanu2009dynamic`, full text reviewed).

Proposition 21's caps use standard tools and no cited theorem. Its
impossibility for range-based caps is the elementary fact that a
bound depending only on a payoff's range is attained by a law
concentrated near the best payoff. Its tangent cap is the
tangent-plane bound for a concave function, here the exponential
certainty equivalent, whose concavity in the trade follows from
convexity of the log-sum-exp function. Its curvature cap bounds
the second derivative of that function by a variance under a
tilted measure.

Propositions 26 and 27 extend the dynamic results to many reviews.
With proportional costs, the continuous-time small-cost literature
gives a no-trade band of width of order the cube root of the cost
around a target that moves with a mean-reverting state variable
(`muhlekarbe2017primer`, Section 4, full text reviewed; its
homogenization technique is `soner2013homogenization`, equation
(4.4), read at the level of its displayed formulas, and the
multidimensional `possamai2015homogenization`). That target does not
learn: its motion comes from a stationary factor, not a posterior mean
whose variance shrinks. Proposition 26 is exact at a fixed quarterly
interval, where a one-review width is meaningful. It shows that such
asymptotics describe only the regime of fine target innovations.
With quadratic costs, Gârleanu and Pedersen's continuous-time
extension to many securities and predictors imposes conditions that
make the predictors stationary (`garleanu2016dynamic`, Section 1,
full text reviewed). That excludes a learned posterior mean, which is
a martingale. Proposition 27 handles that case with a time-varying
recursion. Its filter/control separation is the standard
linear-quadratic-Gaussian one (`abeille2016lqg`, full text reviewed),
and its new content is the exposure/alpha split for bundled
instruments.

Propositions 30 and 32-34 concern trading on estimated inputs.
In one period, Kan and Zhou derive the expected loss of the plug-in
mean-variance rule exactly, as a function of the number of assets and
the length of the estimation window: \(N/(2\gamma T)\) when only the means are
estimated. They then treat the case of an estimated covariance with
known means (`kanzhou2007optimal`, equation (17) and the discussion
following it, full text reviewed). Propositions 30 and 32 are the
dynamic counterpart for the covariance, with trading costs and
learning. There the loss is a discounted sum over reviews, explicit in
the starting holdings, the prior means and the precision still to be
gained. Proposition 33 adds re-estimation at every review. Proposition
34's benchmark is Wachter's split of a dynamic allocation into a
myopic term and a hedging term (`wachter2002portfolio`, p. 73, full
text reviewed). Its point is that under a per-review objective the
anticipation that remains is a cost effect.

Two further sources fix how these results read. Without transaction
costs, "a greedy strategy that only considers one period at a time is
optimal, since performance for the current period does not depend on
previous holdings", while with costs "current holdings strongly affect
whether a return prediction can be profitably acted on"
(`boyd2017multiperiod`, Chapter 5, p. 45, full text reviewed).
Propositions 29, 31 and 34 are that distinction made exact for a
learning-driven target: anticipation of future learning enters today's
trade only through trading costs. And the Kalman recursion is the
minimum-mean-squared-error filter among affine rules for any noise
with finite second moments, and the exact posterior when the noise is
Gaussian (`uhlmann2022gaussianity`, Section 2, on Kalman's Corollary
1, full text reviewed). The source states only that sufficiency: under
other laws the posterior mean can differ from the filter's, but need
not, as the ledger's audit of its entry records. That is the difference
between the fund-of-funds learning model, whose filter is the exact
posterior, and the finite-law variant of the learning-driven tracking
model, whose same linear filter is the best linear predictor.

Propositions 26 (v) and 38 concern several instruments under
proportional costs. For two correlated risky assets, Lynch and Tan find
numerically that the no-trade region is a rectangle at zero
correlation and a parallelogram otherwise, distorted to exploit the
substitutability that positive correlation induces, and that with
predictable returns the conditional correlation sets the distortion
(`lynchtan2010multiple`, read at the level of its introduction).
Proposition 26 (v) gives that parallelogram exactly at the last review.
Proposition 38 bounds a fund's band at every review between explicit
anchors in the inputs, the fund-alone width and a ceiling set by the
residual variance given the ETFs, but it does not give the region's
dynamic shape. When some instruments sit at a bound, Jagannathan and
Ma show that the multipliers of the binding bounds fold into an
adjusted covariance, so the constrained minimum-variance portfolio is
an unconstrained one for that matrix (`jagannathan2003risk`,
Proposition 1, read at the level of the proposition). Propositions 35,
38 and 39 exclude ETFs at their bounds, and that fold-in is the
benchmark for extending them there. Proposition 40 takes the first
such step for the two-stage procedures.

Propositions 42 and 43 concern the fine regime and the shape of a
fund's band beside a costly ETF. For a position hedged through an
imperfectly correlated asset with fixed and proportional costs,
Whalley derives the leading-order no-transaction band by asymptotic
analysis; lowering the absolute correlation narrows the band and moves
its centre toward zero (`whalley2011optimal`, read at the level of its
abstract). Proposition 42 is the proportional-cost counterpart at
quarterly reviews. It is exact at the frictionless and frozen ends,
where the correlation enters through the residual curvature and the
idle target's variance, and it leaves the band between the ends open.
With a binding constraint, the effect of a small spread on the policy
changes order from \(\epsilon^{1/3}\) to \(\epsilon^{1/2}\), because the unconstrained optimum
lies outside the feasible set (`liu2013portfolio`, Section 3.1, full
text reviewed). Propositions 40 and 41 are exact at one review with
ETFs at zero and a binding budget, and any leading-order band for that
case must allow for this change of order.

Propositions 50-57 concern flexibility over two reviews. Moallemi and
Saglam evaluate a class of linear rebalancing rules against computed
upper bounds on any policy's value: in an execution example the best
linear rule comes within 5% of the value any policy can achieve, and in
a mean-variance trading example its improvement over the best
alternative policy reaches 18% as the horizon and costs vary
(`moallemi2015dynamic`, pp. 5, 30 and 32, read at those passages). The
lab's registered comparisons are against the exact dynamic optimum on a
finite tree instead, and Proposition 56 (iii) bounds the loss of
re-optimizing each quarter without solving the dynamic problem at all.
That bound's tail term is the Rockafellar-Uryasev tail measure, the
conditional expectation of a loss beyond its quantile, obtained as the
minimum of a convex function of the quantile level
(`rockafellar2000optimization`, Theorem 1 and the definitions before
it, read at that level); Proposition 56 uses only its elementary
identity on a finite law. Collin-Dufresne, Daniel and Saglam show that
with costly trading and a stochastic opportunity set a long-horizon
investor trades toward an aim portfolio that depends on costs and on
each asset's correlation with changes in the opportunity set, at a
speed set by the shock's persistence and how well it can be hedged
(`collindufresne2024optimal`, read at the level of its abstract).
Proposition 57's predictable move is the persistent part under a
per-review score, where no hedging demand arises: it enters through
the band's lean and front-loading, and the unpredictable part through
the reserve. The standard references on pooling one buffer across
several sources of need (`eppen1979effects`), on intertemporal
separation with several hedging funds (`merton1973intertemporal`) and
on investment under uncertainty (`dixitpindyck1994investment`) are
registered but not read; how Propositions 54, 55 and 57 relate to them
is not checked.

These source comparisons cover registered texts, not every
general result that could contain these mechanisms as special
cases. The search for a two-stage separation result beyond the
sources above is also incomplete. Candidate sources on constrained replication,
learning and flexibility,
smooth decision rules and optimization sensitivity have only been
identified from titles or abstracts; their precise coverage has
not been checked against full texts. No priority claim or transfer
theorem for the funded ETF-only comparison follows from this review.

## 5. Outlook

This draft establishes one-quarter accounting, feasibility geometry,
an exact no-active-trade band after ETF optimization for fixed other
inputs, exact assumed examples and finite two-review policy
attainment. An exact two-review example gives opposite effects of
future ETF and active trading on the root active advantage. It
does not estimate how often these mechanisms occur in observed
portfolios or give a
general rule with statistical coverage for choosing an active trade.
The one-quarter belief-average score cannot express a preference
against uncertainty about conditional means when their belief
averages are unchanged.

The two-review model supplies an explicit law for public learning
and an attained continuation value. The opposite-sign example
shows one structural effect of future adjustment. A bounded
extension retains the signs with positive conditional return
risk and alpha that remains uncertain after some observations.
Its alpha and shocks are small relative to the assumed factor
premia, and the mechanism still uses the revealed factor regime.
Proposition 20 shows that no sign of the future-ETF effect holds
across the model. In every instance the effect lies between
differences of the premium of future ETF adjustment at the two
root optima. That premium is capped by the cash and ETF holdings
left after today's trade, and an explicit family has the
opposite sign. Proposition 25 supplies a floor on the premium by
adjustable wealth, and its floors come within about a quarter of
the premia on assumed instances. The caps are the weak side, 29 to
374 times too large there, and no instance in which the
no-active-trade region itself moves is exhibited. Proposition 21
shows that no cap built from wealth and return ranges alone can be
sharp enough. Caps using risk-adjusted mean returns are sharper and
vanish exactly where no favorable trade has wealth, but in the
assumed numerical instances they decide only two of six signs.
Elsewhere the sign has to be computed instance by instance.
A statistical account would need a stated estimation procedure
and an evidential comparison with the best feasible ETF-only
alternative. Proposition 14 supplies a finite-law benchmark
against the optimized ETF-only class and shows that the
prescribed sample-mean gate can miss information in public
ETF returns. Its exact support calculations require a known
law and exact observations. Proposition 15 gives a matching-order
worst-case history-length envelope over a class of bounded known
finite laws, with a valid conservative certificate against the
whole funded ETF-only class. Its active trade earns an uncertain
factor premium with known zero alpha; the envelope is scalar
mean testing after converting the score margin by the funded
exposure \(D\). Proposition 16 lets alpha and premia vary
together and makes the optimized ETF comparator switch between
cash and the ETF. Its worst-case rate depends on the larger of
two covariance directions. Both the covariance floor when alpha
is observed exactly and the lower bound on a fixed known-alpha
slice are machine checked; the latter asserts the existence of
one alpha value, not a bound for every alpha value. An error-free comparison
against the ETF can still leave a noisy comparison against cash.
The result uses a bounded known-law class, two comparator
vertices, and loose constants. It does not give a general
empirical certificate or dynamic boundary.
Proposition 17 instead makes the active holding shrink smoothly
at entry while the optimal ETF holding moves continuously. Its
known-law worst-case rate is inverse-first-power in the economic
advantage margin and inverse-square in the active mean signal.
The result ties risk aversion to the shock scale, assumes zero
costs and slack funding, and does not identify a general rate
under binding constraints or a calibrated live-trading rule.
Proposition 18 gives a valid whole-class certificate with
costs, caps and binding funding when return risk is strictly
curved. Its worst-case lower bound uses Proposition 17's slack,
zero-cost subfamily. Numerical use requires certified global
optimizer values or the reviewed paper-proof gap bound; the
exact-optimizer power rate does not transfer to arbitrary
solver outputs. Neither result gives a calibrated history
recommendation, unknown-law coverage or repeated-review rule.
Proposition 19 removes knowledge of the law in the two-face
family, keeping only a known bound on the shocks. There the
optimized ETF-only comparator is exactly its two faces: a rule
that certifies each face separately from its range attains the
known-law worst-case order, and no law-free rule does better in
order. What remains open in that family is constants, which
decide whether any law-free rule has useful power at realistic
history lengths, and a time-uniform version for repeated
reviews.
Proposition 22 shows that choosing a factor target first and funds
second, with a soft penalty for missing the target, loses only
through the multiplier of the funded first-stage constraint. It
gives a bound, not a magnitude, for how large that loss is in
realistic portfolios. Proposition 23 identifies the loss exactly
when the second stage must meet the target, and names three ways
funded long-only trading breaks separation. Only the first of
these, manager-borne exposure, is proved; the shared budget and
the cost kink are explanations. The loss in its numerical
illustration is below 3 basis points per quarter except where the
target forces holding a fund the joint optimum would sell. Neither
procedure dominates the other in general.
Proposition 24 shows that with a linear score the whole funded
ETF-only comparator is its finite faces, so any certification rule
reduces to finitely many scalar mean statements. With a curved score
this holds only when the ETF-only optimizer is constant on the
domain. It says nothing about which law classes supply those
statements or at what rate.
Proposition 26 fixes the exact structure of quarterly no-trade bands
around a moving target, with a slack budget. The band is never wider
than the one-review band, and it equals it, shifted, when target
innovations are coarse. What remains open is the leading order of
the band when innovations are fine, the effect of a binding budget
and caps on its edges, the dynamic shape with many instruments, and
the specialization to a target driven by learning.
Proposition 27 gives the exact policy when positions are
unconstrained and costs are quadratic. It shows partial adjustment
toward an aim that anticipates learning, and an exact split of ETF
exposure from fund alpha that only ETF costs, residual risk and fees
couple. The policy is a counterfactual: it may short funds, and its
implementable, long-only version is open.
Proposition 28 shows that when ETFs miss a factor direction, premium
beliefs leak into fund choice through that direction, as a
persistent mean term and a risk term that learning removes. Open
there are whether the leak is nonzero at every review for every
horizon, beyond the proved cases, and its size at calibrated scale.
Proposition 29 shows that learning is anticipated only in positions
that are costly to trade, through a learning factor at most a few
percent in the instances checked, and that a pooled alpha prior makes
the average fund position trade faster than relative positions.
Proposition 30 gives the exact value loss from an estimated covariance
and a guarantee for an estimate made before the run. Its a-priori norm
bounds are vacuous at realistic scale, and a time-uniform guarantee
for a manager who re-estimates is open.
Proposition 31 puts Proposition 26's band on the learning path: the
static width rises while the learned target's moves shrink, so pure
learning ends the coarse regime. Which instruments stay coarse once
real returns move the deviation, and the fine regime's leading order,
are open.
Proposition 32 writes the plug-in loss as an explicit function of the
inputs, with limits in the fund cost and a statement of when spanning
keeps the two estimation errors apart. Its monotonicity in precision
and horizon is open.
Proposition 33 bounds the expected loss of a manager who re-estimates
at every review, with no smallness condition, as an explicit function
of the inputs and any time-uniform confidence radii. The confidence
sequence's constants, and so the bound's size at given data, are not
evaluated.
Proposition 34 gives explicit conditions for when anticipating
learning or mean reversion materially changes today's trade: the
Kalman gain for learning, and the future's weight times the
persistence shortfall for mean reversion. Both effects vanish for
costless instruments. Heterogeneous funds and ETF costs are open.
Proposition 35 says in the inputs how premium error enters fund
choice: not at all through spanning frictionless ETFs, through one
hedged scalar per fund otherwise, and in full under naive selection.
Several unreachable funds, ETF frictions and binding ETF bounds are
open; the last is the common case at long-only instances.
Proposition 36 states when data can support buying a fund, as a margin
over a cost-and-incumbent threshold of order the noise scale times
\(\sqrt{\log(1/\varepsilon)/n_{\rm eff}}\), with a precision floor from persistent alpha
that no history removes. Several funds traded at once, ETF frictions,
and lower bounds under persistence are open.
Proposition 37 places the two cost models in one tracking problem with
a common target and loss, and shows that anticipating learning has
order \(\kappa^2\) times a bounded duration under quadratic costs. The
proportional-cost order, about \(\kappa^{4/3}\) in the fine regime, rests on a
cited leading-order law; a proved bound on the band's centre, and a
composite rule matched between the two costs, are open.
Proposition 38 bounds a fund's band beside optimally traded ETFs at
every review, between the fund-alone width and a ceiling set by its
residual variance given the ETFs. The band's dependence on the
correlation of the targets' motion, and several funds whose bands
couple, are open.
Proposition 39 prices the ETF-only restriction at one review as the
value of the fund purchases it forbids, and shows that a frozen-funds
baseline adds the value of the forgone sales. The multi-review cost and
ETFs at their bounds are open.
Proposition 40 gives the two-stage procedures' exactness with ETFs at
zero, through stage 1's own slacks. With fees, ETF frictions and a
binding budget it is open.
Proposition 41 adds them: given the ETFs' statuses, every fund's
marginal is explicit in the inputs, and the target-confined procedure
is generically inexact once it trades a costly ETF that ends interior,
while the soft procedure with an unconstrained first stage stays exact.
ETF caps and a first stage that sees costs or the budget are open.
Proposition 42 gives a fund's fine-regime band beside one costly ETF
at its frictionless and frozen ends, through the cited cube-root law,
and names the weight between them. The band between the ends, and its
end limits as theorems, are open.
Proposition 43 gives the shape of the two-instrument band: exact
median edges at the last review, bending over the ETF's residual
width, and monotone edges at every review. How the targets'
correlation moves the band before the last review is a conjecture.
Proposition 44 states the one-review fund criterion on which the
bundling results rest: exact, explicit under frictionless spanning
ETFs, and bracketed by the re-hedge cost otherwise. Proposition 45
gives two-stage exactness and loss at one review in the inputs; a
first stage that sees costs or the budget is open. Proposition 46
gives the fund decision with ETFs at zero, on which the later results
with bounds rest; an ETF at its cap is open. Proposition 47 reduces
the one-ETF case to two monotone scalar prices, the exposure price and
the cash price. Proposition 48 gives a first stage that prices the
ETF trades and a loss bound for any split, through the ETF-line
residual. Proposition 49 sandwiches the fine-regime cost of a fund and
one costly ETF in the inputs; where the effective rate lies in the
sandwich, and the fund's band between the ends, are open. Proposition
50 extends the one-review rule to two reviews with a budget that may
bind, through the dynamic cash price and the incumbent values; more
reviews and the joint comparative static are open. Proposition 51
bounds tomorrow's cash price and the incumbent values in the inputs,
and restricts the sign reading to a frictionless interior ETF.
Proposition 52 puts learning, predictive risk, marking and the budget
into one worked model under either shock law; the dynamic optimum under
the Gaussian law is open. Proposition 53 turns Propositions 50-51 into
a reserve rule sized in the inputs, and Proposition 54 extends it to
several funds sharing one ETF. Proposition 55 shows that with many
ETFs spanning splits the two-review optimality conditions, not the
optimization; many costly ETFs are open. Proposition 56 gives the
full menu a quantile flexibility test and bounds the loss of
re-optimizing each quarter under it; the test with time-varying premia
is open. Proposition 57 lets premia and alphas move on their own: the
target's move splits into a predictable part, which tilts the band and
is front-loaded or planned for, and an unpredictable part, which the
reserve prices; the rising width holds only while learning outweighs
the state noise. Proposition 58 extends the test to that case: cover
the planned purchase in full and a quantile of the rest, and
front-loading the planned purchase removes the loss bound's band term.

## Appendix A. Machine verification

The repository version codes appear here only to trace paper results to their
formal statements. The general review notation is a notation-level setting;
the funded one-quarter and two-review models are the working
specializations of Section 2. The multi-review tracking model of
Section 2 is the version labelled M6, the fund-of-funds learning
model is M5, and the learning-driven tracking model is M7. The
two-review worked model is M8, and M8 with M5's state equation is M9.

| Paper result | Claim file | Model version |
|---|---|---|
| Proposition 1 | `claims/002-paired-mean-error.md` | M0 |
| Proposition 2 | `claims/001-self-financing-identity.md` | M0 |
| Proposition 3 | `claims/003-m2-score-accounting.md` | M2 |
| Proposition 4 | `claims/004-m2-action-classes.md` | M2 |
| Proposition 5 | `claims/005-m2-etf-exposure-geometry.md` | M2 |
| Proposition 6 | `claims/006-m2-complete-substitution.md` | M2 |
| Proposition 7 | `claims/007-m2-incomplete-substitution.md` | M2 |
| Proposition 8 | `claims/008-m2-zero-alpha-limiting-case.md` | M2 |
| Proposition 9 | `claims/009-m2-no-active-trade-band.md` | M2 |
| Proposition 10 | `claims/010-m2-higher-cost-narrower-band.md` | M2 |
| Proposition 11 | `claims/011-m3-finite-continuation.md` | M3 |
| Proposition 12 | `claims/012-opposite-continuation-effects.md` | M3 |
| Proposition 13 | `claims/013-continuation-with-risk-and-partial-learning.md` | M3 |
| Proposition 14 | `claims/014-m4-public-information-obstruction.md` | M4 |
| Proposition 15 | `claims/015-m4-bounded-law-history-rate.md` | M4 |
| Proposition 16 | `claims/016-m4-joint-directional-rate.md` | M4 |
| Proposition 17 | `claims/017-m4-curved-entry-rate.md` | M4 |
| Proposition 18 | `claims/018-m4-curvature-certificate.md` | M4 |
| Proposition 19 | `claims/021-m4-law-free-faces-match-order.md` | M4 |
| Proposition 20 | `claims/022-m3-etf-channel-sandwich.md` | M3 |
| Proposition 21 | `claims/026-m3-mean-type-caps.md` | M3 |
| Proposition 22 | `claims/028-m2-soft-target-two-stage.md` | M2 |
| Proposition 23 | `claims/027-m2-two-stage-separation.md` | M2 |
| Proposition 24 | `claims/020-m4-finite-comparator-faces-iff.md` | M4 |
| Proposition 25 | `claims/023-m3-premium-node-bounds.md` | M3 |
| Proposition 26 | `claims/029-m6-quarterly-band-static-ceiling.md` | M6 |
| Proposition 27 | `claims/030-m5-partial-adjustment-split.md` | M5 |
| Proposition 28 | `claims/031-m5-missing-direction-leak.md` | M5 |
| Proposition 29 | `claims/032-m5-learning-aim-two-speeds.md` | M5 |
| Proposition 30 | `claims/033-m5-plug-in-value-loss.md` | M5 |
| Proposition 31 | `claims/100-m7-learning-band-transfer.md` | M7 |
| Proposition 32 | `claims/034-m5-plug-in-loss-inputs.md` | M5 |
| Proposition 33 | `claims/035-m5-reestimation-guarantee.md` | M5 |
| Proposition 34 | `claims/036-m5-when-anticipation-matters.md` | M5 |
| Proposition 35 | `claims/105-m7-premium-error-in-fund-choice.md` | M7 |
| Proposition 36 | `claims/039-when-data-support-an-active-change.md` | M7 |
| Proposition 37 | `claims/038-integration-theorem.md` | M5, M7 |
| Proposition 38 | `claims/107-m7-dynamic-bundling-band.md` | M7 |
| Proposition 39 | `claims/106-m7-etf-only-restriction-cost.md` | M7 |
| Proposition 40 | `claims/041-m7-two-stage-with-etfs-at-zero.md` | M7 |
| Proposition 41 | `claims/109-m7-fund-decision-etfs-at-zero-costs-budget.md` | M7 |
| Proposition 42 | `claims/042-m7-fine-band-with-one-costly-etf.md` | M7 |
| Proposition 43 | `claims/108-m7-dynamic-bundling-shape.md` | M7 |
| Proposition 44 | `claims/102-m7-fund-hold-buy-sell-criterion.md` | M7 |
| Proposition 45 | `claims/104-m7-two-stage-exactness-loss.md` | M7 |
| Proposition 46 | `claims/040-m7-fund-decision-with-etfs-at-zero.md` | M7 |
| Proposition 47 | `claims/110-m7-one-etf-two-scalars.md` | M7 |
| Proposition 48 | `claims/111-m7-incumbent-aware-first-stage.md` | M7 |
| Proposition 49 | `claims/043-m7-fine-cost-sandwich-with-one-costly-etf.md` | M7 |
| Proposition 50 | `claims/044-m7-two-reviews-binding-budget.md` | M7 |
| Proposition 51 | `claims/046-m7-two-reviews-bounds-in-the-inputs.md` | M7 |
| Proposition 52 | `claims/112-m8-worked-learning-example.md` | M8 |
| Proposition 53 | `claims/047-m8-reserve-rule-one-fund-one-etf.md` | M8 |
| Proposition 54 | `claims/113-m7-several-funds-one-etf-reserve.md` | M7, M8 |
| Proposition 55 | `claims/048-m7-many-funds-many-etfs-two-reviews.md` | M7 |
| Proposition 56 | `claims/049-m7-quantile-flexibility-test-full-menu.md` | M7 |
| Proposition 57 | `claims/114-m9-predictable-and-unpredictable-target-move.md` | M9 |
| Proposition 58 | `claims/115-m9-quantile-flexibility-test-time-varying.md` | M9 |

Proposition 1 corresponds to \(\texttt{claims/002-paired-mean-error.md}\). Its identity,
universal and particular cancellation statements, exposure-matching consequences, and a
nonzero-exposure example of particular cancellation are machine checked in
\(\texttt{lean/Standalone/PairedMeanError.lean}\) and
\(\texttt{lean/Novel/PairedMeanErrorProof.lean}\). No cited result or project hypothesis
structure is used. The formal statement fixes the same loadings, covariance, ETF drag
and switching-cost function across score evaluations. It does not verify feasibility,
an optimized comparator, an error distribution, or a claim for either
one-quarter specialization; no simulation
is presented as evidence for Proposition 1.

Proposition 2 corresponds to \(\texttt{claims/001-self-financing-identity.md}\).
The identity, funded long-only equivalence, feasible-trade cost bound and zero-trade
conclusion are stated in
\(\texttt{lean/Standalone/SelfFinancingIdentity.lean}\) and machine checked by
\(\texttt{lean/Novel/SelfFinancingIdentityProof.lean}\). The identity and equivalence
need no sign assumption on the trade or cost; the bound uses a nonnegative cost and
funded long-only feasibility; the zero-trade conclusion additionally requires
nonnegative initial holdings and cash and \(C_t(0)=0\). No cited result or project
hypothesis structure is used. The formal statement verifies no score, terminal-wealth
or normalized one-quarter funding claim.

Proposition 3 corresponds to \(\texttt{claims/003-m2-score-accounting.md}\). The
cost normalization, funding transfer, gain and conditional-moment identities, score
formula, belief-mean evaluation, positivity at that mean and same-mean ranking and
maximizer-set conclusions are machine checked in
\(\texttt{lean/Standalone/M2ScoreAccounting.lean}\) and
\(\texttt{lean/Novel/M2ScoreAccountingProof.lean}\). The formal statement covers every
holding and arbitrary finite instrument and factor counts, so it includes the
funded one-quarter model's restricted counts and feasible holdings. Its funding
algebra is re-derived in that model's
index type rather than imported from Proposition 2's Lean proof. No cited result
or project hypothesis structure is used. The machine check does not establish
attainment, an effect of belief dispersion, a predictive-variance objective,
dynamic learning, or empirical relevance.

Proposition 4 corresponds to \(\texttt{claims/004-m2-action-classes.md}\). Nesting,
nonemptiness, closedness, boundedness and convexity of the classes; continuity and
concavity of the belief-average score; attained maxima; and the weak value chain
are machine checked in \(\texttt{lean/Standalone/M2ActionClasses.lean}\) and
\(\texttt{lean/Novel/M2ActionClassesProof.lean}\). The formal statement reuses
Proposition 3's one-quarter definitions, permits arbitrary finite instrument
counts, and drops hypotheses where a particular part does not need them. The Lean proof
uses compactness of a closed finite box and an extreme-value theorem for
attainment; the reviewed paper proof uses an explicit subsequence construction.
No cited result or project hypothesis structure is used. The machine check gives
no uniqueness, strict value gap or empirical materiality.

Proposition 5 corresponds to \(\texttt{claims/005-m2-etf-exposure-geometry.md}\).
The finite directional-cash representation, ETF-only action and exposure-image
identities, compactness and convexity, exact matching and obstruction test,
one-ETF interval, invertible two-ETF case, and active-loading span criterion
are machine checked in
\(\texttt{lean/Standalone/M2EtfExposureGeometry.lean}\) and
\(\texttt{lean/Novel/M2EtfExposureGeometryProof.lean}\). The formal statement
reuses Proposition 3's one-quarter objects and Proposition 4's initial-compliance and
nonnegative-rate predicates. It proves the set properties under the hypotheses
needed for each part; these cover Section 2's stated restrictions. Lean proves the
closedness of the exposure images using compactness, while the reviewed paper
proof uses a bounded-sequence construction. No cited result or project
hypothesis structure is used. The machine check establishes feasibility
geometry only: it proves no score comparison, strict value gap, economic
magnitude or transfer to another model version.

Proposition 6 corresponds to
\(\texttt{claims/006-m2-complete-substitution.md}\). The literal one-quarter data,
positive gross returns, exact funded action classes and exposure images,
feasible replacement for every full action, matched risk, cost and cash,
belief-average and conditional score differences, unique class maximizers,
their scores and the strict \(1/101\) gap are machine checked in
\(\texttt{lean/Standalone/M2CompleteSubstitution.lean}\) and
\(\texttt{lean/Novel/M2CompleteSubstitutionProof.lean}\). The formal instance
uses Proposition 3's one-quarter definitions, Proposition 4's compliance and rate
predicates, and Proposition 5's exposure-set definitions. The score identities
are proved for all nonnegative holdings, not only feasible ones. The formal
proof computes the one-ETF image directly; it does not import Proposition 5's
image lemma. No cited result or project hypothesis structure is used. The
machine check proves this assumed instance, not its empirical relevance,
another instance or a multiperiod return advantage.

Proposition 7 corresponds to
\(\texttt{claims/007-m2-incomplete-substitution.md}\). The two literal
one-quarter menus, all 32 scenario returns and their positivity, the shared return
law of common instruments, all five unique class optima with cash, costs
and scores, the zero and positive optimal gaps, the active-trade comparison,
the one-ETF missing direction and the two-ETF full-span but infeasible
match are machine checked in
\(\texttt{lean/Standalone/M2IncompleteSubstitution.lean}\) and
\(\texttt{lean/Novel/M2IncompleteSubstitutionProof.lean}\). The proof
reuses Proposition 3's one-quarter definitions, Proposition 4's feasibility
hypotheses and Proposition 5's ETF-span definition. It certifies strict
optimality through the funded score inequality and a positive quadratic
form. The paper proof displays particular multiplier and subgradient
vectors in the claim file; those vectors are not separate formal
conjuncts, although the optimizer statements are checked. No cited
result or project hypothesis structure is used. The machine check covers
these assumed instances only; it does not attribute the gap solely to
the shorting obstruction or establish economic materiality.

Proposition 8 corresponds to
\(\texttt{claims/008-m2-zero-alpha-limiting-case.md}\). The general
replacement map, its feasibility, exposure and cash identities, its
belief-average score identity, attained zero-active optimum,
\(V_F=V_E\) under no incumbent, and the stated strict
non-participation conclusions are machine checked in
\(\texttt{lean/Standalone/M2ZeroAlphaLimitingCase.lean}\) and
\(\texttt{lean/Novel/M2ZeroAlphaLimitingCaseProof.lean}\). The stronger
pointwise equal-return and terminal-wealth identities, and all four
literal examples with their one-quarter model validity, optimizer descriptions and
scores, are checked there too. The Lean statement uses Proposition
3's one-quarter definitions; it proves attainment directly rather than
importing Proposition 4's proof. It permits arbitrary finite factor,
scenario and belief sets in its general part, and omits unused one-quarter
hypotheses such as positive gross returns there. No cited theorem or
project hypothesis structure is used. The registered source's
continuous-time conclusion is compared in prose, not imported or
machine checked. The zero cross-moment remains an explicit formal
hypothesis. It forces zero ETF residual variance when both
residuals are uncorrelated with factor shocks and with each other;
shared ETF and active residual noise can instead satisfy it with
positive ETF residual variance. The independent-noise
counterexample above lies outside the formal hypothesis and is
checked by exact finite calculation, not a formal conjunct.
The machine check establishes no general zero-alpha rule. The
four formal examples and the counterexample use assumed inputs,
not empirical evidence.

Proposition 9 corresponds to
\(\texttt{claims/009-m2-no-active-trade-band.md}\). The translated
belief-mean family, return-positive domain, existence and
alpha-independence of ETF-only optima, multiplier interval and its
endpoints, all four active-bound cases, interior width, global
marginal equivalence, conditional uniqueness and both degenerate
counterexamples are machine checked in
\(\texttt{lean/Standalone/M2NoActiveTradeBand.lean}\) and
\(\texttt{lean/Novel/M2NoActiveTradeBandProof.lean}\).
The formal theorem permits any finite ETF menu and factor dimension;
the paper uses the one- or two-ETF specialization. Some unused model
hypotheses, including centered shocks, are omitted in the general
formal result. The Lean proof uses feasible-move necessity instead
of the paper proof's lifted-cost finite-cone argument, so that
particular proof device is not separately machine checked. The
four-row table is formalized for the algebraically extended score,
and the return-positive domain is characterized separately; the
paper's \(C\cap J\) applies both results. No cited theorem or
project hypothesis structure is imported. The assumed examples are
exact counterexamples, not empirical estimates. The independent
paper-to-formal fidelity review matches the claim, with no added or
strengthened hypotheses. The review also confirms that the
lifted-cost finite-cone argument is a paper proof, while its
optimality conclusion is machine checked by a different route.

Proposition 10 corresponds to
\(\texttt{claims/010-m2-higher-cost-narrower-band.md}\). The two
literal cost cases, their return-positive domains, positive
definite covariance, unique ETF-only and full-trading optima,
ETF multiplier intervals, complete bands inside the domain,
exact widths and strict width difference are machine checked in
\(\texttt{lean/Standalone/M2HigherCostNarrowerBand.lean}\) and
\(\texttt{lean/Novel/M2HigherCostNarrowerBandProof.lean}\).
The formal proof imports Proposition 9's proof to use its band
characterization; no cited theorem or hypothesis structure is
assumed. The two widths and their positive difference are exact
arithmetic identities linked to the formally characterized bands.
The formal scope statement checks the algebraic slopes of the
interior width at fixed ETF multiplier endpoints; their positivity
follows from Proposition 9's nonnegative multiplier interval, and
is not a separate formal conjunct. The cap-perturbation scope
analysis and the comparison to dynamic no-trade literature are not
formal conjuncts. This is one assumed instance, not evidence about
calibrated rates or a general cost comparative static. The
independent paper-to-formal fidelity review matches the claim with
no added or strengthened hypotheses.

Proposition 11 corresponds to
\(\texttt{claims/011-m3-finite-continuation.md}\). The formal
statement defines the two-review observation, posterior, dollar
funding classes, nine policy sets, terminal-utility sum,
conditional and root continuation values, and certainty-equivalent
comparison in
\(\texttt{lean/Standalone/M3FiniteContinuation.lean}\).
\(\texttt{lean/Novel/M3FiniteContinuationProof.lean}\) machine
checks policy compactness and convexity, objective concavity and
attainment, pathwise positive wealth and value bounds, conditional
attainment and state concavity, finite Bayes regrouping, the
attained Bellman representation, both class orders and the
existence-only zero-gap equivalence. The root cash constraint is
explicit in the formal feasibility definition. The proof chooses
conditional optimizers at every observation, including zero-mass
ones; the paper may choose zero trades there. The formal theorem
permits arbitrary finite instrument and factor counts and omits
centered-shock hypotheses unused by this finite-control argument.
Conditional independence is encoded in the two scenario weights
of the explicit utility sum. No cited theorem or project
hypothesis structure is imported. The machine check establishes
neither a dynamic trade boundary nor a sign or magnitude for the
effect of future ETF adjustment. The independent paper-to-formal
fidelity review matches the claim, with no added or strengthened
hypotheses. Its state-sufficiency content is the proved finite
conditional regrouping; the conditional objective depends on the
marked state and posterior by definition. The value bounds make
the logarithmic certainty equivalent meaningful. No
nondegenerate example is a formal conjunct.

Proposition 12 corresponds to
\(\texttt{claims/012-opposite-continuation-effects.md}\).
The literal two-parameter, one-scenario family with four
independently variable rates over \([0,1/100]\), its valid
two-review instances and public revelation, all three
certainty-equivalent gap bounds, the two strict continuation
signs, the positive active root trade under ETF-only
continuation, and the zero-cost waiting optimum are machine
checked in
\(\texttt{lean/Standalone/OppositeContinuationEffects.lean}\)
and \(\texttt{lean/Novel/OppositeContinuationEffectsProof.lean}\).
The proof imports Proposition 11's machine-checked attainment
and class orders. It proves the strict ETF-only upper bound
directly with exponential inequalities; the paper's
intermediate logarithmic expression and derivative argument
are not separate formal conjuncts. The exposure and timing
mechanism is an interpretation of the proved policies, not a
formal statement. No cited theorem or project hypothesis
structure is imported. Alpha is known zero and the active
fund alone carries the first factor. The law has no conditional
shock risk and reveals the parameter completely; the assumed
returns and preference coefficient are uncalibrated. The
uniform result concerns only the stated cost box. The
independent paper-to-formal fidelity review matches the claim,
with no added or strengthened hypotheses; it also confirms that
the mechanism narrative and intermediate derivative calculation
are paper arguments rather than separate formal conjuncts.

Proposition 13 corresponds to
\(\texttt{claims/013-continuation-with-risk-and-partial-learning.md}\).
The literal four-parameter, four-scenario family, for every
\(0<\delta\leq1/1000\) and all four independent rates in
\([0,1/100]\), is machine checked in
\(\texttt{lean/Standalone/ContinuationRobustness.lean}\)
and \(\texttt{lean/Novel/ContinuationRobustnessProof.lean}\).
The formal statement proves model admissibility, positive-definite
conditional covariance \(\delta^2I_2\), independent nonzero
alpha uncertainty, and the observation event of probability
\(1/2\) on which the alpha posterior remains split equally.
It also proves every gap bound in (31), both strict signs in
(32), and a positive root active purchase at every full-root
optimum with ETF-only continuation. The proof imports
Proposition 11's attainment and class orders and Proposition 12's
elementary exponential facts; it proves its utility bounds
from the specified returns and funded policies, without a
project hypothesis structure or cited theorem. Its ETF-only
upper bound uses an exponential inequality rather than the
paper proof's intermediate derivative argument, so that
intermediate calculation is not a separate formal conjunct.
The machine-checked limits are the stated small \(\delta\)
and rate boxes. Partial learning concerns alpha only; neither
the proof nor the witness policies attribute either sign to
unresolved alpha. Numerical probes at larger shocks are not
part of this result. No calibrated magnitude, alpha-driven
mechanism or general dynamic boundary is machine checked.

Proposition 14 corresponds to
\(\texttt{claims/014-m4-public-information-obstruction.md}\).
The two literal public-return laws, their common funded action
sets and score, the covariance and ETF-optimum identities in
(33), and the endpoint advantages are machine checked. The
statement is in
\(\texttt{lean/Standalone/M4InformationObstruction.lean}\).
Its proof is in
\(\texttt{lean/Novel/M4InformationObstructionProof.lean}\).
The formal statement defines the fixed-parameter, finite public
sampling law, sample-mean estimate, mean-error covariance,
discretely calibrated confidence set, optimized ETF comparator,
and exact selected-action gate. For every positive history
length and error allowance in \((0,1)\), it proves both attained
full-history benchmark powers in (34) against rules uniformly
valid over the entire parameter interval, allowing randomized
active actions. It proves that the prescribed gate has the same
decision law in both models at every parameter and sample
length, and certifies with probability \(1/2\) after one record
at the favorable endpoint. The two benchmark values at
\(\eta=1/4\) are formal too. No cited result, project hypothesis
structure or earlier claim is imported into the proof.
The paper's alternative confidence-set construction for the
full-history rules is not a formal conjunct; neither are red's
finite calculations of gate power at two and three records.
Uniform coverage of the prescribed confidence set for general
instances of the sampling model is not a result here.
In particular the gate is not asserted to have monotone power.
The one-record attribution of its shortfall follows the stated
overlap and gate calculations; no separate general attribution
theorem is claimed. Known discrete shocks, exact observations,
zero costs, known premia and the fixed ETF optimum delimit the
machine-checked example. No realistic magnitude, general
sample-size rate or robustness to rounding is proved.

Proposition 15 corresponds to
\(\texttt{claims/015-m4-bounded-law-history-rate.md}\).
The machine-checked statement and proof modules are listed in
the proof map.
The statement reuses the one-quarter sampling definitions from
Proposition 14's formal statement file, but imports no result
from its proof. The machine check covers the funded class and
unique ETF optimum, the advantage and exposure formulas in
(35), both quantified implications in (36), the conservative
certificate against the original \(L_N\) in (37), its
coverage-event power, and the logarithm comparison. The
lower-bound quantifiers allow a different full-history
randomized rule for each known finite law but require validity
over every parameter in the interval. The formal proof
constructs the sine-weighted hard law and a finite overlap
bound; it uses an affinity-squared bound rather than the
paper proof's total-variation inequality. Both yield the
stated constant. The bounded-mean tail and discrete confidence
radius are proved from finite sums, including zero-variance
laws. No rate, tail inequality, cited result or project
hypothesis structure is assumed; the axiom audit reports only
standard axioms.

The formal result is a worst case over laws whose finite
support may grow with the prespecified margin, and a sufficient
length for a specific conservative gate. It proves neither
matching constants nor monotone power for a particular law.
Alpha is known zero, and the ETF comparator is fixed in this
family. Unknown or rounded shock laws, a moving ETF optimum,
multivariate uncertainty and realized economic magnitudes are
outside its machine-checked scope.

Proposition 16 corresponds to
\(\texttt{claims/016-m4-joint-directional-rate.md}\).
The machine-checked statement and proof modules are listed in
the proof map. Red independently checked the claim and PM
approved it before formalization. The formal statement reuses
M4's definitions and Proposition 15's rule requirements;
its proof imports Proposition 15's proof module and
re-derives the paired score errors used here. It proves the
admissibility and covariance of the literal family, the
moving ETF optimum and two-direction advantage in (38)--(39),
both quantified length implications in (40), the original
optimized-comparator certificate and its coverage-event power
in (41), and the variance formulas and examples in (42).
The lower bound allows a separate randomized full-history
rule for each known law and remains valid for singular
\(J\): the proof lifts a public rule to a more informative
finite latent history. Its adverse law retains covariance
\(JJ^\top\). Finite concentration and calibration prove the
upper bound, including the empty-set fallback. The formal
statement also covers a one-record full-history benchmark
when both comparison variances vanish. No rate, tail or
covariance inequality is assumed as a project hypothesis;
the axiom audit reports only standard axioms.

When \(\Omega_{33}=0\), the formal statement proves that
alpha is read exactly from each record and that the
unspanned-premium variance floor remains. Its separate
known-alpha conjunct machine checks the lower bound when
both rule requirements are imposed only on the domain slice
\(\alpha=\alpha_0\), for an \(\alpha_0\) fixed before the
history length and law. The hard pair shares that alpha.
The formal statement asserts existence of this slice, not
the bound for every alpha value in the domain.

The formal scope is a worst case over a bounded class of
known finite laws, with support size allowed to grow as
\(\sigma/\delta\). The lower and upper constants differ by
roughly \(5\times10^4\) at \(\varepsilon=1/16\), so only
their order matches. The two contrasts combine the
unspanned premium and alpha; the result does not isolate
manager skill. A continuously moving risk-averse ETF
optimum, general menus, estimated loadings, rounded data,
efficient calibration and repeated live decisions remain
outside the machine-checked result.

Proposition 17 corresponds to
\(\texttt{claims/017-m4-curved-entry-rate.md}\). Red independently
checked it and PM approved it before formalization. The statement
and proof modules listed in the proof map machine check the funded
optima and optimized-class advantage in (43)--(44), both quantified
history-length implications in (45), and the conservative
original-target certificate and its coverage-event power in (46).
The formal proof imports Proposition 16's proof module for the
finite-law tools and re-establishes the required specialization;
no cited result or project hypothesis structure supplies the rate.
The lower implication covers law-specific randomized rules using
the full public history. The upper implication covers the stated
plug-in gate, including feasibility of its unprojected estimates,
the moving ETF comparator's quadratic penalty and fallback on an
empty confidence set. The axiom audit reports only standard axioms.

The machine check concerns the one-quarter family with
\(\gamma=s^{-2}\), known exact finite laws, zero costs and strict
cash slack. The hard law's support grows as \(s/\sqrt\delta\).
It does not establish an optimal rate for each individual law,
unknown shock laws, binding funding, general preferences, rounded
observations or repeated
reviews. Its mean signal combines the first factor premium and
manager alpha; it does not identify their separate contributions.

Proposition 18 corresponds to
\(\texttt{claims/018-m4-curvature-certificate.md}\). Red
independently checked the numbered claim and PM approved it
before formalization. The statement and proof modules in the
proof map machine check the admissible funded setting,
attainment and uniqueness of the exact plug-in optima, the
curvature-normalized scale in (47), and the original-target
certificate, active-change condition and uniform false-
certification bound in (48). They also check the coverage-event
power and sufficient length in (49), the \(K=0\) identity,
and both class-level implications in (50), including a member
with \(K=\kappa\). The formal proof imports Proposition 4's
action-class results and Proposition 17's lower-bound family;
it uses the finite-law machinery from Proposition 16. No
cited result, project hypothesis structure, optimizer-stability
assumption or statistical rate is imported as an axiom. The
axiom audit reports only standard axioms. The formal
admissibility condition keeps the paper's one- or two-ETF
scope. The independent fidelity review matches the numbered
statement without added hypotheses; it confirms that the
later approximate-optimizer remark is outside the formal
statement.

The approximate-optimizer formula (51) is a **reviewed paper
proof, not machine checked**. Red checked its derivation,
exact counterexamples to simpler value-gap shortcuts, and
finite numerical attacks; those checks do not establish a
floating-point certification algorithm. It requires certified
feasibility, global value gaps, the radius and directed
rounding. It preserves a pointwise lower bound and hence
coverage-based false-certification control, but no power
rate for approximate outputs is proved. The machine-checked
class lower bound uses Proposition 17's zero-cost subfamily;
it is not a rate for each binding face or cost schedule.

Proposition 19 corresponds to
\(\texttt{claims/021-m4-law-free-faces-match-order.md}\). Red
independently checked it, including a recheck after its tail
bound was replaced by a citation, and PM approved it before
formalization. The statement and proof modules in the proof map
machine check the setting (every law in \(\mathcal L_J\) gives
an admissible instance, the face formulas, the face ranges,
\(\mathcal K_J\subset\mathcal L_J\) and
\(\bar\sigma_j=\sigma_j\) there), all of part (i) including the
identity (53), the full-level face bounds, the union-bound
converse, the level-factor identities with its value at
\(\eta=1/20\) and the decomposition inequality, the range
rule's membership in the rule class, its false-certification
bound and both sufficient lengths in (ii), and both
implications in (55). The formal statement reuses Proposition
16's family, rule class and law class \(\mathcal K_J\),
Proposition 15's requirement predicates and Proposition 14's
sampling objects. A law-free rule is one formal rule fixed
before the law is quantified, and the range rule's estimate is
shown to be the sample mean under every law.

The paper proof cites Hoeffding's inequality
(`maurer2009empirical`, Theorem 1). The formal proof instead
uses Hoeffding's lemma as already proved in the pinned
Mathlib library, followed by a finite Chernoff step, so no
tail inequality is assumed and nothing is re-proved; the
axiom audit reports only standard axioms. Several formal
parts are stronger than the prose: the range rule's validity
holds for every history length, whereas the claim restricts
it to \(N\geq3\log(2/\eta)\); part (i)'s joint and
union-bound statements hold for any data-dependent sets and
bounds under any finite law; the sufficient lengths in (ii)
need only \(\varepsilon<1\); and the lower bound in (55)
needs neither \((JJ^\top)_{11}>0\) nor a minimum history
length. Infima are taken in the extended reals. The formal
lower bound applies to rules in Proposition 16's rule class,
which is the class the prose uses. The independent
paper-to-formal fidelity review matches the claim with no added
or strengthened hypotheses, and confirms the more general formal
parts listed here. It also notes that the width and
history-length reading of the level factor in (i) holds only
for face bounds of the stated width shape, as the proposition
says.

The machine check establishes worst-case order only, over a
bounded class with known \(J\) and known range, in the
two-face, zero-cost, all-cash family with the fixed active
action \(w_A\). Its constants are about \(2.8\times10^5\)
apart. It gives no per-law efficiency, no analysis of
empirical Bernstein constants, no time-uniform or sequential
guarantee over repeated reviews and no result for laws of
unknown range; it does not separate manager skill from the
unspanned premium.

Proposition 20 corresponds to
\(\texttt{claims/022-m3-etf-channel-sandwich.md}\). Red
independently checked it, including a recheck after the
monotone-comparative-statics reading was added, and PM approved
it before formalization. The statement and proof modules in the
proof map machine check, for every instance of the funded
two-review model: attainment of \(CE_{D,R}\) as the maximum of
\(c_R\) over the root class with \(\varphi,\psi\geq0\); both
sandwiches in (57) for every choice of maximizers; the cap
(58), the zero premium at a root with neither cash nor ETF
holdings, and the corner sign condition; and both
region-movement statements in (iii), each with an optimal
policy that makes no active root trade. For the family in (iv)
they check that every member is an instance whose first
observation reveals the parameter, all four certainty-equivalent
bounds and the channel bound in (59), positivity of both gaps,
feasibility and zero premium of the all-active root, and the
lower bound on the all-cash root's premium. Both signs are
formal: this family gives a negative channel and Proposition
12's family a positive one. The formal cap holds for any upper
and lower bounds on ETF gross returns, which includes the
tightest choice in the prose. The proof imports the proof
modules of Propositions 11 and 12. No cited result or project
hypothesis structure is used, and the axiom audit reports only
standard axioms.

The reading of increasing differences, single crossing, hedging
demand and signal persistence against the model is prose; only
its numerical fact about the two premia is a formal conjunct.
The machine check gives no closed-form sign condition, no lower
bound on the premium, no movement of the region itself and no
calibrated magnitude; its example has no conditional risk, full
revelation and known zero alpha. The independent paper-to-formal
fidelity review matches parts (i)--(iv) and the numerical fact
about the two premia, with no added or strengthened hypotheses.
It notes that the fall of the premium in the root active holding
is formal only as the comparison between the all-active and
all-cash roots, which is how the text states it.

Proposition 21 corresponds to
\(\texttt{claims/026-m3-mean-type-caps.md}\), which refiles two
earlier versions that red refuted for wording errors: a misdescribed
certified case, a false comparison, a buy-side cap written with the
wrong wealth amount, and a zero-gain condition without switches. Red
checked the refile, including 600 random two-ETF nodes solved
exactly, and PM approved it before formalization. The statement
and proof modules in the proof map machine check parts (i)--(iv)
for every instance of the funded two-review model: the
near-attaining node constructions and the lower bounds (61) on
every range-type cap, the realizability constraint on node data,
that \(G^{\rm ub}_y\) is a range-type cap, and the zero-gain
example; the tangent cap (62), the equivalence of \(T_y=0\)
with the three no-favorable-direction conditions, zero gain there,
and the one-ETF formula; the one-ETF curvature cap (63) in each
direction; and part (iv) as stated, including both sign
conditions with \(\beta_{\rm mean}\) built from \(T_y\). The node
objects, the weights, the aggregate (60) and the identity
\(\varphi=\mathcal A(G)\) come from the formal modules of a
companion result on node-wise lower bounds, which enter with this
result and are machine checked. That companion result is
Proposition 25; Proposition 21 uses only its definitions and the
identity. Several formal parts are stronger than the prose: parts
(iii) and (iv) hold for every valid wealth-range bound and return
bracket, and the sign conditions hold for any node-wise lower
bounds. The formal proof uses Jensen's inequality under the
tilted node measure for (ii) and a monotonicity argument on the
second derivative for (iii), rather than the paper's one-sided
derivative and double integration. The proof imports the proof
modules of Propositions 11 and 20. No cited result or project
hypothesis structure is used, and the axiom audit reports only
standard axioms.

The numerical comparison after the proposition has no formal
counterpart. It is computed from solver optimizers, not
certificates, on one assumed base design. The zero-premium corner
at \(\rho=20\) is read from those optimizers.

The independent paper-to-formal fidelity review matches parts
(i)--(iv) with no added hypotheses. Its first version found that
the formal cap in part (iv) was built from the looser middle bound
in (62) rather than \(T_y\). The formal statement was then
restated with \(T_y\), and the re-audit confirmed that part (iv)
is machine checked as stated. The numerical comparison computes
the same \(\beta_{\rm mean}\) that the formal statement defines.

Proposition 22 corresponds to
\(\texttt{claims/028-m2-soft-target-two-stage.md}\). Red
independently checked it, including 200 random instances with
factor-correlated residual shocks, and PM approved it before
formalization. The statement and proof modules in the proof map
machine check that \(b(F)\subset\mathcal R_0\) with
\(\mathcal R_0\) convex and compact, and that stage 1 on
\(\mathcal R_0\), stage 2 and the joint problem attain their
maxima. They also check the identification (66) and the \(\nu=0\)
case; all of (ii), including the equality condition, the Euclidean
bound and the target-reached case; the exact form (67) with
nonnegative slack and kink terms and the sign condition for a zero
kink; the target-confined comparison (iv); and the normal-cone
statement (v). The formal statement is more general than the
prose: it allows any numbers of active funds, ETFs and factors and
a score at any parameter, which by Proposition 3 includes the
belief-mean score. Part (ii) is proved for any holding set, and the
directional derivatives are proved to be right derivatives along
the segment. The files are self-contained. They import only
Proposition 4's proof module, and nothing rests on the
target-confined procedure's separate analysis. No cited result or
project hypothesis structure is used, and the axiom audit reports
only standard axioms. Not formal: the reading of the slack as
binding-constraint multipliers times the displacement, and the
face-normal reading of \(\nu\) beyond the normal-cone statement.
An independent paper-to-formal fidelity review of this result has
not yet been recorded.

Proposition 23 corresponds to
\(\texttt{claims/027-m2-two-stage-separation.md}\). Red
refuted its first filing, which asserted that the residual value
\(V\) is always concave; red and lean gave a counterexample with
factor-correlated residuals. The amended claim states concavity
for \(G+V\) in general and for \(V\) only under zero cross
moments. Red checked the amendment and PM approved it before
formalization. The statement and proof modules in the proof map
machine check: the split (68) at the belief mean; \(B_F\) nonempty,
convex and compact; attainment of \(V\); concavity of \(G+V\) and,
under zero cross moments, of \(V\); \(J=\max_{B_F}(G+V)\); stage 1's
maximizer and the unconstrained target's uniqueness when it lies in
\(B_F\); the identity (70) with both brackets nonnegative; the
separation criterion of (ii), including the relative-interior
converse for concave \(V\) (with the relative interior taken as the
intrinsic interior); both bounds of (iii); and the flat case of (iv)
with the missing-direction statement for one active fund. The formal
statement allows any numbers of active funds, ETFs and factors, and
its loss bounds need no positive definiteness. It re-derives the
belief-average identity locally and imports only Proposition 4's
proof module. No cited result or project hypothesis structure is
used, and the axiom audit reports only standard axioms.

The shared-budget and cost-kink failures of separation are
qualitative explanations and have no formal counterpart. The
numerical comparison after the proposition is computed from floating
solver outputs on one calibration, not certificates. The comparison
with Proposition 22's soft procedure uses that result's part (iv);
no ordering between the two is proved. The independent paper-to-formal
fidelity review matches parts (i)--(iv) with no added or
strengthened hypotheses. It confirms that, of the funded failures of
separation, only the missing-direction fact is formal, as the text
says.

Proposition 24 corresponds to
\(\texttt{claims/020-m4-finite-comparator-faces-iff.md}\), which
refiles a claim red refuted: that filing asserted that a finite face
set is never exact under a curved score, and red's single-comparator
instance in (v) shows otherwise. Red checked the refile, including
the vertex counts, the closed form (73) with singular \(\Omega\),
the covering bound in (iv) and the instance in (v) exactly. PM
approved it before formalization. The statement and proof modules
in the proof map machine check all five parts. That covers (i)
with the halfspace descriptions, finiteness, the counts,
independence from the parameter and law, and (71). It covers
(ii)'s attainment on faces, (72) for every parameter set, the
faces as plug-in selections, and (73) for nonempty \(C_N\). It also
covers (iii)(a) and the polyhedral structure of (iii)(b); (74),
the exact excess and the \(m+1\geq16\) count in Proposition 17's
family; and (v) with its instance. The finiteness of the faces
and their counts in (i), and the finite-union-of-polyhedra
statement in (iii), are conditional on the linear-programming vertex
theorem. It enters as the audited hypothesis structure
\(\texttt{LPVertex}\) (ledger entry AX-05), whose instance, the
empty constraint system in dimension zero, is degenerate and
disclosed, because a faithful instance would re-derive the cited
theorem. An earlier version of the formal proof proved the theorem
in general for these cells. The re-audit replaced that with the
cited hypothesis, as the project's rules require for a known general
theorem. Every other part of (i)--(v) is unconditional. The face
maxima use the model's lexicographic selection. The proof imports
Proposition 18's proof module, and the axiom audit reports only
standard axioms.
Formal choices: the ETF-only cells use the compliant incumbent,
(73) needs a nonempty \(C_N\), infima over parameter sets are in the
extended reals, and (v) needs \(T\) and \(S\) nonempty. The reading
after the proposition has no formal counterpart. The independent
paper-to-formal fidelity review matches the claim, with several
formal parts more general than the prose. Its re-audit confirms that
the vertex theorem is a hypothesis of the finiteness conclusions
only.

Proposition 16's existential known-alpha pre-disclosure conclusion is machine checked.
Proposition 25 corresponds to
\(\texttt{claims/023-m3-premium-node-bounds.md}\). Red checked it by
hand, recomputed the two certifications independently, tested the
node lemmas on random nodes and computed the true premia at the
numerical comparison's optimizers. After Red's recheck of the revision
that replaced a self-proved curvature step with the citation of
Hoeffding's lemma, PM approved it before formalization. The
statement and proof modules in the proof map machine check all five
parts. They cover the decomposition (75) with its bounds and
monotonicity; the sure-sign and risk-adjusted floors (76), including
the \(rh/2\) floor; the caps and the chain
\(\alpha\leq\varphi\leq\beta_{\rm node}\leq\beta\); the sign conditions
(77) and their robust forms; and both certifications, with the
uniqueness claims, closed-form aggregates and margins in (78). These
files entered main with Proposition 21, which builds on them, and are
unchanged. Hoeffding's lemma, ledger entry AX-08, enters through the
pinned Mathlib library's machine-checked lemma, applied under the
tilted node measure to a variable of range at most \(2s\). It is not
an assumed hypothesis, and nothing is re-proved. Several formal parts
are more general than the prose. The floors and caps hold for every
valid bracket of the node-path returns, the sure-sign bounds for every
\(\delta\), and the caps for every nonnegative bound on gains and
losses. In (iv), uniqueness of the cash root is proved with exponential
inequalities instead of the paper's concavity argument. The proof
imports the proof modules of Propositions 11, 12 and 20, and the axiom
audit reports only standard axioms. The numerical ratios after the
proposition, and the reading that the caps are the weak side, have no
formal counterpart. The independent paper-to-formal fidelity review
matches the claim.

Proposition 26 corresponds to
\(\texttt{claims/029-m6-quarterly-band-static-ceiling.md}\). Red
checked parts (i)--(v) by hand and ran an independent backward
induction on 40 random instances (345 bands) with no failure. PM
approved the claim before formalization. The statement and proof
modules in the proof map machine check every numbered part.
- (i): strict convexity and continuity of \(G_t\), convexity of \(V_t\)
  with slopes in \([-\kappa^+,\kappa^-]\), the ordering of the edges, and
  uniqueness and optimality of the clip (79) for every real
  pre-trade holding.
- (ii): the ceiling (80), the last-review band and the edge brackets.
- (iii): the tilted band (81) with its sufficient conditions.
- (iv): the equality characterization and strict narrowing otherwise.
- (v): uniqueness, the nonempty no-trade set, (82) with its
  single-coordinate and Euclidean corollaries, the static shape and
  the bundling equivalence.

The formal model is the slack-budget instance, so cash does not
appear, with a finite state set and finite outcome laws. Part (i)
uses Mathlib's one-sided derivatives of convex functions, and (v)
uses the comparison along a segment, with no subdifferential sum
rule. No cited result, project hypothesis structure or other claim's
proof module is used, and the axiom audit reports only standard
axioms. The trade-to-the-edge structure re-derives Constantinides'
classical band. When that source's text is obtained, the plan is to
cite it through a ledger entry and keep only the additions. Not
formal: the coarse/fine reading for ETFs and funds, the remark
relating (80) to Proposition 9, and the regression reading of the
bundling shift. The independent paper-to-formal fidelity review
matches the claim, with no added or strengthened hypothesis and
several conjuncts stronger than the prose.

Proposition 27 corresponds to
\(\texttt{claims/030-m5-partial-adjustment-split.md}\). Red checked
parts (i)-(v) by hand and confirmed the separated case (iii) with an
independent recursion to \(2\times10^{-15}\), together with each coupling
term alone. PM approved the claim, with two corrections that changed
no result: the eigenvalue range of \(\Gamma_t\), and an induction step
in (v). The statement and proof modules in the proof map machine
check, over arbitrary finite index sets:
- the filter facts of (i), including positive definiteness,
  monotonicity, the innovation covariance, the decoupling and (83);
- the Bellman verification of (ii) with the recursion, uniqueness,
  the eigenvalue and similarity facts for \(\Gamma_t\), the
  partial-adjustment form and the aim's weights summing to the
  identity;
- the coordinate change, reference-case blocks and exact separation
  (86) of (iii);
- the scalar speeds, monotonicity, the stationary root (87) and the
  two limits of (v), together with the identification with Gârleanu
  and Pedersen's rate.

At PM's instruction, under the formalization boundary for
measure-theoretic infrastructure, two steps are reviewed paper
proofs, not machine checked. The first is the Gaussian conditional
moments, which give the predictive moments and discharge the
martingale hypothesis of the formal Bellman verification. The second
is the dynamic-programming step from Bellman optimality to optimality
over all admissible measurable policies. Ledger entry AX-10 (the
stationary linear-quadratic-Gaussian separation) is cited as context
and not used; no hypothesis structure or other claim's proof module
is used, and the axiom audit reports only standard axioms. Not
formalized: that the value function's intercept is quadratic in the
belief mean, and the readings of (iii)-(iv) beyond the block
formulas. The independent paper-to-formal fidelity review matches the
claim within the disclosed formal scope, with no added hypothesis; the
formal statement is more general in allowing \(\rho\geq0\) and arbitrary
finite index sets.

Proposition 28 corresponds to
\(\texttt{claims/031-m5-missing-direction-leak.md}\). Red found that
the first version's converse in (iii), nonvanishing at every review,
was unproved beyond \(T\leq3\) and the stationary case, and required a
correction. PM withdrew the claim for revision, and red passed the
revision, which asserts nonvanishing only where \(M_t\) is
nonsingular. PM approved it before formalization. The statement and
proof modules in the proof map machine check:
- (i): the projection, the coordinate bijection, the reachable
  exposure (89) and the vanishing hedge;
- (ii): the fund positions as the reduced problem's policy, through
  the Schur complement of the joint Riccati matrix, with the reduced
  Markowitz portfolio;
- (iii): the sensitivity (90) with its recursion, the vanishing case,
  the proved nonsingular cases (last review, \(T\leq3\), the symmetric-part
  condition, and the stationary limit), the positive semidefinite,
  nonzero risk term, and its effect on the own-position coefficient at
  every review;
- (iv): the monotone convergence of the Schur complement and the hedge
  map along the learning path.

Proposition 27's formal problem was generalized to a deterministic,
time-varying mean map for this purpose. As for Proposition 27, the
Gaussian conditional moments and the passage to all measurable
policies are reviewed paper proofs, not machine checked. Not
formalized: the numerical observation that \(M_t\) is nonsingular at
every review, and the reading of (iv) that the premium estimate has a
nonzero limit. No cited result or project hypothesis structure is
used, and the axiom audit reports only standard axioms. The
independent paper-to-formal fidelity review matches the claim within
Proposition 27's disclosed formal scope, with no added hypothesis.

Proposition 29 corresponds to
\(\texttt{claims/032-m5-learning-aim-two-speeds.md}\). Red's verdict
required two corrections, which were met before PM's approval: the
\(1/t^2\) rate in (i), and the dependence on Proposition 27. No result
changed. The statement and proof modules in the proof map machine
check:
- (i): (91) with its equality condition, the monotone gap and its
  \(1/t^2\) limit;
- (ii): the two-direction decomposition of the rate and the Riccati
  matrix, \(g^c_t\geq g^r_t\) with its equality condition, and the common
  stationary limit;
- (iii): the positive weights summing to one, the bounds in (92), the
  learning factor at least one with equality exactly at the last
  review, and the aim and Markowitz formulas in each direction;
- (iv): as Proposition 27 (iii).

The proof imports Proposition 27's proof module. Its paper-level
steps are Proposition 27's. Not formalized: the effect of ETF costs
on the exposure, and the two numerically observed orderings. No cited
result or project hypothesis structure is used, and the axiom audit
reports only standard axioms. The independent paper-to-formal
fidelity review matches the claim within Proposition 27's disclosed
formal scope, with no added hypothesis and several conjuncts stronger
than the prose.

Proposition 30 corresponds to
\(\texttt{claims/033-m5-plug-in-value-loss.md}\). Red's first review
led to a revision that PM approved after red's recheck. The revision
assumes a positive semidefinite estimate in (iii), states the
indefinite failure mode, and restricts (iv) to a covariance estimated
once before the run. The statement and proof modules in the proof map
machine check:
- (i): the one-step identity at every review and state, the Bellman
  objective at any trade equal to the value minus \(\frac12e^\top D_te\);
- (ii): the pathwise error decomposition and bounds, including
  \(\|D_t\|_*\leq1+\|R_t\|\);
- (iii): all four Riccati bounds, for positive semidefinite true and
  estimated risk matrices, positive definite \(\Lambda\) and
  \(\rho\in[0,1]\);
- (iv): the bounds on the confidence event, whose probability carries
  over by inclusion.

Three steps are reviewed paper proofs, within the scope PM confirmed
under the formalization boundary: summing the one-step identity into
(93) under conditional expectations, the passage to second moments,
and the recursion for the state moments. Ledger entries AX-11 and
AX-12 (the stationary perturbation and certainty-equivalence results)
are cited as context and not used. The proof imports Proposition 27's
proof module, and the axiom audit reports only standard axioms. The
calibrated numbers come from a check script, not a formal statement.
The independent paper-to-formal fidelity review matches the claim on
the finite-dimensional core the formal file declares, with the
expectation-level steps at paper level, as disclosed.

Proposition 31 corresponds to
\(\texttt{claims/100-m7-learning-band-transfer.md}\). Red passed it
and PM approved it. Prose corrections followed at Lean's and red's
request and changed no result: the drift's sign requires a learning
risk charge, the landing probabilities in (iv) are closed, and \(t_0\)
does not depend on the horizon. The statement and proof modules in the proof map machine
check, in the finite-law variant:
- (i): the instance is a multi-review tracking model with covariance
  \(\Sigma(t,z)=\Sigma_t\), and Proposition 26's statement transfers, proved by
  its own proofs at a fixed review and state, including the two-date
  coarse condition and the separation for diagonal \(\Sigma_t\);
- (ii): the information form and the monotone convergence of \(P_t\),
  \(\Sigma_t\), \(c_t\) and the static width;
- (iii): the target decomposition, the positive semidefinite bracket,
  the drift's sign, the exact \(1/t^2\) limits, and the tilt formula
  (97), whose zero case needs \(\kappa>0\), a condition the formal
  statement adds;
- (iv): the landing dichotomy with \(U+D=1\), the move bounds (98), and
  eventual strict narrowing from a \(t_0\) fixed before the horizon.

The proof imports Proposition 26's proof module. The unconditional
moments of the belief-mean innovation over the finite law are a
reviewed paper step that enters no formal conclusion. No cited result
or project hypothesis structure is used, and the axiom audit reports
only standard axioms. The independent paper-to-formal fidelity
review matches the claim, with no added hypothesis and a formal model
more general than the claim's.

Proposition 32 corresponds to
\(\texttt{claims/034-m5-plug-in-loss-inputs.md}\). Red passed it and PM
approved it, with the formal scope confirmed as for Propositions 27 and
30. The statement and proof modules in the proof map machine check:
- (i): the plug-in path's product form, the decomposition
  \(e_t=\mu_t+\sum_uW_{t,u}\eta_u\) for every innovation sequence, and the loss's
  vanishing condition, for arbitrary plug-in coefficients;
- (ii): (100) as an identity for symmetric covariances, and the scalar
  recursion as Proposition 27's in one dimension;
- (iii): the derivatives of the coefficients and the \(C\epsilon^2+O(\epsilon^3)\)
  expansion, the costless limit, the \(1/\lambda_A\) order (exact for \(x_0\neq0\)
  with a nonzero error) and \(1/\lambda_A^3\) for \(x_0=0\), the one-review
  formula (101) with its positivity at intermediate cost, and the
  monotonicity of the posterior variance in the prior;
- (iv): separation of the two risk blocks, invariance of the fund
  positions to the factor covariance under spanning, and a family of
  instances in every non-spanning setting where the fund coefficient
  changes.

The expectation identities over the Gaussian filtering model, and the
identification of \(C\)'s expectation form with its derivative form, are
reviewed paper proofs. The proof imports the proof modules of
Propositions 27 and 28. Ledger entry AX-12 is context only, no cited
result or project hypothesis structure is used, and the axiom audit
reports only standard axioms. The independent paper-to-formal
fidelity review matches the claim on the deterministic core the file
declares, with several conjuncts stronger than the claim. It notes
three points where the formal statement is narrower than the prose.
The vanishing condition in (i) is formal only when every precision
decrement is positive definite. Of (iii)'s precision statement, only
the monotonicity of the posterior variance in the prior is formal. And
the split of the total loss into the exposure and fund parts in (ii)
is not itself a formal conjunct: it follows from Proposition 27's
separation and was confirmed numerically.

Proposition 33 corresponds to
\(\texttt{claims/035-m5-reestimation-guarantee.md}\). Red passed it and
PM approved it, with the formal scope split as for Propositions 30 and
32. The statement and proof modules in the proof map machine check
(102) for any positive semidefinite estimate and for the true
coefficients, the position bound along the re-estimating path, and
the pathwise on-event and off-event bounds. The good event is a
hypothesis of the formal statement. The loss identity in expectation,
the split with Cauchy-Schwarz and Doob's inequality, and the event's
existence from ledger entry AX-04 (the confidence sequence) are
reviewed paper proofs. The proof imports Proposition 30's proof
module; no project hypothesis structure is used, and the axiom audit
reports only standard axioms. The independent paper-to-formal
fidelity review matches the claim on the pathwise core the file
declares, with the expectation-level combination and the confidence
event at paper level, as disclosed.

Proposition 34 corresponds to
\(\texttt{claims/036-m5-when-anticipation-matters.md}\). Red passed it and
PM approved it. The statement and proof modules in the proof map
machine check, for one fund or direction with a general nonincreasing
positive precision path:
- (i): \(\mathrm{aim}_t=L_t\,\mathrm{aim}^S_t\), the bounds (104) with the strict upper
  bound at every review, the exact form of \(L_t-1\), \(L_t=1\) exactly at the
  last review for a strictly decreasing path, and the threshold;
- (ii): the rate ordering, the monotonicity and Lipschitz constant of
  the constant-risk rate, and the trade identity and bound (105);
- (iii): given the aim formula, the split, the renormalized weights as
  a probability, the properties of \(M_t\) and (106);
- (iv): the zero-cost limits and Proposition 27's separation, together
  with the identity linking Proposition 31's drift to the learning
  factor's one-step increment.

The aim formula under mean reversion, the no-hedging reading, and the
band reading are reviewed paper proofs. The proof imports Proposition
29's proof module. No cited result or project hypothesis structure is
used, and the axiom audit reports only standard axioms. The
independent paper-to-formal fidelity review matches the claim, with
several conjuncts stronger than the prose and two steps at paper level,
as disclosed.

Proposition 35 corresponds to
\(\texttt{claims/105-m7-premium-error-in-fund-choice.md}\). Red passed it and
PM approved it. The claim uses three lemmas from an approved companion
result on two-stage implementation, since written up as Proposition 45.
The formal modules of that companion result entered main with this one,
are imported by its proof and are machine checked. The alpha-band
holding and the reduced objective are defined in the proposition
itself. The statement and proof modules in the proof map machine check:
- (i): fund holdings at slack joint optima are the band holdings,
  independent of premia, factor covariance and loadings, and the
  exposure loss;
- (ii): the joint optimum's form, the invariance of the holding to the
  premium belief beyond \(B^A_iJ^\top\hat\lambda\), the narrowing factor and its limit
  along the learning path, the Lipschitz move bound, the exact move on a
  common trading piece and none on a common hold piece, the decision
  conditions, and the loss bracket (108);
- (iii): the exact loss identity (109) with its zero condition, the
  naive move bound, and the zero-incumbent readings.

In (ii), Lean corrected the decision conditions at two boundaries: the
purchase and sale conditions include the cap and the zero bound, and
an equality case at the threshold. The text states the corrected form.
The expectations over the premium error are reviewed paper proofs.
No cited result or project hypothesis structure is used, and the axiom
audit reports only standard axioms. The independent paper-to-formal
fidelity review finds a match except at those two boundaries in (ii),
where the formal statement is the correct one and the claim's prose,
not yet revised, is not; the text uses the formal form. The
expectations are at paper level.

Proposition 36 corresponds to
\(\texttt{claims/039-when-data-support-an-active-change.md}\). Red's review
required two corrections, the proved form of (ii)'s necessary length
and (v)'s hypothesis that the prior is at least as diffuse as the floor.
Math made them, red's recheck passed them, and PM approved the claim.
The formal forms follow math's later revision, which Lean B's report
prompted. The claim proves the one-fund, one-review threshold it uses
in (i) and names the general threshold of claim 102 without relying on
it. The statement and proof
modules in the proof map machine check:
- (i): existence and uniqueness of the one-fund optimum and the buy and
  sell conditions;
- (ii): the certifying rule's two errors under independent Gaussian
  residuals, the lower bound's arithmetic from the Gaussian affinity,
  \(z_\varepsilon^2\geq\log(1/(4\varepsilon))\), and the Bayesian condition;
- (iii): the Hoeffding rule for independent centred residuals bounded
  by \(R\), not necessarily identically distributed, and, in a second
  stage, the two-point lower bound for any randomized rule, through
  Proposition 15's finite Le Cam lemma;
- (iv): the certificate under inequality (7) as a hypothesis;
- (v): the fixed point (112), its uniqueness and position below the
  stationary prior, the monotone convergence, the floor, and both
  limits;
- (vi): the Gaussian variance of the decision quantity and the length
  ratio (113);
- (vii): the direction variances under the pooled posterior and the
  averaged rule's length.

Hoeffding's inequality enters through the pinned Mathlib library, as
for Proposition 19. Part (ii)'s lower bound takes ledger entry AX-09's
inequality as a premise, and together with the mixing instantiations,
the Gaussian and Kalman posterior forms, the reduction to the one-fund
problem (claims 030 and 104) and the reading of (113)'s loading as
\(J(B^A_i)^\top\), they are reviewed paper proofs. The proof imports
the proof modules of Propositions 15 and 29, and the axiom audit
reports only standard axioms. The independent paper-to-formal fidelity
review matches the claim for the first stage, with the lower bounds'
probability steps at paper level as then declared; the second stage's
formal two-point bound in (iii) has not yet been reviewed.

Proposition 37 corresponds to
\(\texttt{claims/038-integration-theorem.md}\), which refiles the refuted claim
037. Red refuted 037 on one point: under proportional costs in the fine
regime the band's centre anticipates about two thirds of a mixing time
of the learning drift, not one step. Red's review of the refile then
required the orders in the gain to be stated separately for the two
costs; math made that correction, red's recheck passed it, and PM
approved. The component results enter through the formal statements of
claims 009, 027-036 and 100, and the proof imports their proof modules.
The statement and proof modules in the proof map machine check the new
steps:
- (i): the tracking identity (115) for any positive definite covariance;
- (ii): the scalar Kalman path, the drift identity and bound (116), the
  innovation variance \(p_t\kappa_t\), and the one-step form;
- (iii): the quadratic-cost bound (117), its strict positivity, the
  bounds and zero-cost limit of \(D_t\), and the condition for a change
  of the aim by a fraction \(\theta\);
- (iv): the residual identity and its bounds on a finite-law decision
  problem, the stage-reward bound from the caps, and the last-review
  bound (118);
- (v): the quadratic-cost rule as the unique maximizer, and when it
  trades.
Reviewed paper proofs, not machine checked, are the proportional-cost
side of (iii), whose coarse-regime part is claim 100's statement and
whose fine-regime part is Martin's cited leading-order law in the
corrected form of refuted conjecture 101, checked numerically by red; the
off-event expectation step of the re-estimation guarantee under
proportional costs; the reading of the innovation variance as a
standard deviation of the target; the attachment of claim 104 at the
last review; and the composition reading. No cited result or project
hypothesis structure enters the formal proof, and the axiom audit
reports only standard axioms. An independent paper-to-formal fidelity
review of this result has not yet been recorded.

Proposition 38 corresponds to
\(\texttt{claims/107-m7-dynamic-bundling-band.md}\). Red's review found the
theorems sound but required a correction to the reading of (iv), which
had the idle-ETF regime widening the band beyond (121); mathb restated
it, red's recheck passed it, and PM approved. Experiment 036 compared
the result with an exact two-instrument dynamic program and agrees
within grid resolution; that is an illustration, not part of the
proof. The statement and proof modules in the proof map machine check
every numbered part:
- (i): the positive residual curvature, continuity and strong
  convexity of \(U_t\), the split of the full optimum into the fund and
  ETF problems, and the clip;
- (ii): the ceiling (121);
- (iii): each edge's bracket in (122), under its stated edge condition
  and an interior ETF optimizer;
- (iv): the exact edges (123), the width formula, the ceiling for equal
  slopes, the opposite-direction width, the fund-alone width for
  untraded ETFs, and the lower bound on any interior band's width;
- (v): the outer parallelotope (124) for any number of instruments,
  with the diameter bound taken from Proposition 26's formal (82);
- (vi): the reduced one-instrument instance, the value and stay
  objective up to constants, and the equality of the edges, so that
  Proposition 26's formal statement applies; carrying Proposition 31's
  learning-path statements to the reduced instance is prose.
The claim lists the per-review optimality condition AX-13, but the
formal proof does not use it: every first-order fact is proved by
one-sided difference quotients. The proof imports claim 029's proof
module, and the axiom audit reports only standard axioms. Reading
\(a^*_t\) in (vi) as claim 104's reduced target is prose. The hypothesis
in (vi) that the hedge lies in the ETF box at every fund holding, not
only at optimal ones, was Lean B's formal reading; mathb has since
written it into the claim's statement as what the paper proof uses.
The independent paper-to-formal fidelity review matches the claim and
finds several formal conjuncts more general than the prose: (vi) needs
only zero ETF rates among its four conditions on the ETFs, and the
narrowing under Proposition 26's condition in (ii) is prose, not a
conjunct.

Proposition 39 corresponds to
\(\texttt{claims/106-m7-etf-only-restriction-cost.md}\). Red found every
part sound with four nits: the room restriction in (iv)'s display, the
cap form of the zero-incumbent reading, the netting trades' cash room,
and one inequality's direction in the proof's prose. PM approved, and
mathb made the nits without changing a result. The statement and proof
modules in the proof map machine check:
- (i): the ordering of the values, both zero-cost conditions, the
  value-of-sales condition, the decomposition of \(C^0\), and, given AX-13,
  claim 104's multiplier criterion at the ETF-only optimum;
- (ii): (126) with the cap and floor forms and the zero-incumbent
  readings, at the three optima with a slack budget and interior ETFs;
- (iii): the same forms with the unreachable fund's reduced moments;
- (iv): the four brackets (128) with the room restriction in (127),
  the room for the netting trades and their cash entering as the
  feasibility of the four netted holdings.
Ledger entry AX-13, the polyhedral Karush-Kuhn-Tucker theorem, is
needed only by the multiplier criterion in (i). The formal statement
makes all of (i) conditional on it, so (i) is machine checked
conditional on the citation and (ii)-(iv) unconditionally. The proof imports the proof modules
of claims 104 and 105, the companions of Proposition 35, and the axiom
audit reports only standard axioms. The reading of the earlier
experiments' ETF-only baseline is paper level. The independent
paper-to-formal fidelity review matches the claim, with two
bookkeeping points: all of (i) is formally conditional on AX-13
although one conjunct needs it, and the claim's list of axioms used
omitted AX-13.

Proposition 40 corresponds to
\(\texttt{claims/041-m7-two-stage-with-etfs-at-zero.md}\). Lean B's prose
check found (iii)'s "iff" false for the confined soft procedure, with a
one-fund counterexample, and three narrower points; the analyst's
experiment 040 found the exposure-misfit term identically zero. Math
revised, red passed the revision with one wording correction, and PM
approved. The claim builds on claim 040 (the fund decision with ETFs
at zero), which is approved but neither formalized nor written up
here; the objects the result uses from it, \(V_E\), its multiplier and
its at-zero set, are defined in the statement above. The statement and
proof modules in the proof map machine check, for any maximizers,
whose existence and stage 1's uniqueness are proved:
- (i): the sign and complementarity of \(\zeta^*\), exactness iff the fund
  lines (129) hold at \(x_2\), and \(V_E(Qx_2)=G_E(w^*)\) for any number of
  funds;
- (ii): stage 1 as a choice of fund holding, the interval of such
  holdings, the fibre interval (130) with stage 1's holding at the end
  an ETF at zero selects, the clip, the equivalence and loss (131), and
  the one-fund reachability condition;
- (iii): the soft procedure's exactness when \(\nu_E=0\), the normal-cone
  property and bound otherwise, and the tilted-stage criterion.
The fund covariance \(V\) is only assumed positive semidefinite, more
generally than in the claim. AX-13 is listed by the claim but not used
formally. A second formal stage replaced the first stage's temporary
copy of claim 040's ETF-coordinate objects with claim 040's own module,
which is now formalized. The reduction of the model to ETF coordinates
and the comparison with the dropped-ETF benchmark are paper level.
Experiment 029, which prompted the claim, is an illustration; after
approval, experiment 040 led math to sharpen the gloss on exactness
under a nonzero multiplier in (iii), which the text follows. The
independent paper-to-formal fidelity review matches the revised
statement, rechecked after the second stage.

Proposition 41 corresponds to
\(\texttt{claims/109-m7-fund-decision-etfs-at-zero-costs-budget.md}\). Lean B's
prose check found the status tests in (ii) wrong as two equivalences
and questioned the untraded-ETF condition in (iv); mathb corrected
both before red's review, and red's nit then derived the condition's
simple form from stage 1's complementarity. Red passed the claim with one required correction: the
target-confined procedure can be exact while trading costly ETFs, when
every ETF is sold to zero, so its inexactness reading is restricted to
ETFs that end interior. Red's recheck passed the correction, and PM
approved. The criterion in (i) composes claim 040's one-sided line
(Proposition 46) with claim 102's friction and
budget criterion (Proposition 44) and claim 104's exactness forms
(Proposition 45); the claim says
plainly that nothing in (i) goes beyond that composition. The
statement and proof modules in the proof map machine check:
- (i), conditional on AX-13: a feasible holding is the optimum iff
  (132) holds, stated in claim 104's reference case with spanning ETFs;
  necessity is claim 040's formalized criterion and the converse claim
  104's;
- (ii), with \(\Sigma_E=0\) and given the traded ETFs' lines: the traded
  exposure, the fixed marginals, (134) and (135), the three special
  cases, the status implications and the one-quantity test, and the
  range of \((1+\eta)\rho_{iT}^\top t_T\);
- (iii): (136);
- (iv): the exactness criterion at \(x_2\), conditional on AX-13; the fund
  marginals at \(x_2\); \(\zeta^*_j=0\) at interior ETFs and the three conditions;
  and the soft procedure's exactness, bound and tilted-stage criterion,
  for any convex feasible set and concave remainder.
Paper level are the restatement of (i) as consistency of a status
partition with the uniqueness of the optimum, the display in (iv) with
ETF residual risk, the reading of the range in (ii) as the re-hedge
bracket, the one-sided line for a sale to zero, and the comparison
with the composition. The proof imports the proof modules of claims
040, 041 and 104, and the axiom audit reports only standard axioms.
The independent paper-to-formal fidelity review matches the claim as
revised, with (i) and (iv)'s exactness criterion conditional on AX-13
and the rest unconditional. Several parts are proved more generally
than stated, and the headline of (iv), "exact only if", is a
composition of formal pieces rather than one theorem.

Proposition 42 corresponds to
\(\texttt{claims/042-m7-fine-band-with-one-costly-etf.md}\). Red's first review
required two corrections: the corrector verification had the rates on
the wrong sides and wrongly let the band's centre shift with the rate
asymmetry, and (iv)'s end limits and the idle-probability negative were
stated as results. PM also asked that the one-instrument law be cited
through a ledger entry (AX-15), not re-proved. Math revised; red's
recheck passed it, and PM approved. The statement and proof modules in
the proof map machine check:
- (i): the identity (138), and the innovation moments (137) as second
  moments of a finite law;
- (ii): (a) in the multi-review tracking model with zero cross
  covariance at every review and state, as a sum of two
  one-instrument instances whose optima separate; (b) as Proposition
  38's formal (vi); (c) the completed square at a fixed ETF holding;
- (iii): the corrector lemma behind (139), its twice-differentiable
  linear continuation off the band, the symmetric band, the attainment
  identity, and the end ratio;
- (iv): the identity (140).
AX-15 is cited and enters no formal conjunct beyond the formula it
displays; its corrector framework and the identification of the
discrete band with the corrector's are paper level, as are (ii) (c)'s
dynamic reading, (iv)'s dimensional analysis, end readings and idle
fractions, and the checks, which illustrate. The proof imports claim
107's proof module, and the axiom audit reports only standard axioms.
An independent paper-to-formal fidelity review of this result has not
yet been recorded.

Proposition 43 corresponds to
\(\texttt{claims/108-m7-dynamic-bundling-shape.md}\). Red passed it on its own
exact grid dynamic program. PM approved it and asked, under rule 21,
that the proof cite Topkis's theorems through a ledger entry (AX-14)
instead of re-proving their finite case; mathb made that change
without changing a result, and red checked it. The statement and
proof modules in the proof map machine check:
- (i): the median edges (141) for an interior ETF optimizer, their
  continuity, direction and bend length (142) for either sign of the
  covariance, the coinciding levels at zero covariance, the regime
  widths, and the static last-review region;
- (ii), for \(\Sigma_{AE}\geq0\) along the tree and conditional on AX-14:
  increasing differences of \(V_t\), \(G_t\) and the ETF-optimized value,
  the monotone edges of both bands, and (143);
- (iii): the frozen value and stay objective as the idle instance's
  up to constants, and \(v^{\rm idle}\) as a second moment;
- (iv): equality of the last-review bands and region across outcome
  laws.
Topkis's Theorems 3.1, 3.2 and 4.3 enter as a hypothesis structure,
audited as nontrivial, so (ii) is conditional on that citation; the
convex-difference lemma, the coordinate flip and the induction are
proved. The cases \(\Sigma_{AE}\leq0\) and \(\Sigma_{AE}=0\) in (ii) are paper level, as PM
allowed, as are the conjecture and the checks. The proof imports the
proof modules of claims 029 and 107, and the axiom audit reports only
standard axioms. The independent paper-to-formal fidelity review
matches the claim, with (ii) conditional on AX-14 and formal for
nonnegative covariance. Its one precision point is on (iii): formally
the frozen band depends on the whole law of the idle target's
innovation, and two finite laws with the same variances and
correlation can give different bands, so "through \(v^{\rm idle}\) alone" holds
when that law is fixed by its variance. The text above states that
form.

Proposition 44 corresponds to
\(\texttt{claims/102-m7-fund-hold-buy-sell-criterion.md}\), written up after the
propositions that build on it. Red's review required corrections that
restricted (iii)-(iv) to ETFs strictly inside their boxes, sending the
at-zero case to Propositions 40-41; mathb made them and red's recheck
passed them before PM's approval. Later revisions, none changing an
approved result, cited AX-13 in place of re-proving the multiplier
criterion, corrected (v)'s shift on the reduced marginal to
\(\eta(1-\sum_jr_{ij})\) after experiment 034 and red found the literal form wrong,
and adopted Lean's forms at the box edges in (iii), (iv) and (vi). The
statement and proof modules in the proof map machine check:
- (i): existence and uniqueness, the criterion, and every instrument's
  readings with their one-sided forms;
- (ii): the no-trade test at the ETF-only optimum;
- (iii): the band holding (144), the bought and sold conditions with
  the box conditions, the zero-incumbent readings and the netting
  decomposition;
- (iv): the bracket (145), the re-hedge equalities and the converse's
  counterexample, the pinned-slope thresholds, and the sufficient
  conditions at the incumbent;
- (v): the shifted strip (146), the shifted exposure and the bracket
  with a binding budget;
- (vi): the thresholds (147) and their mirrors at the cap in the
  one-instrument model.
The criterion in (i) and the parts that use it, (ii), (iv) and (v), take
AX-13 as a hypothesis, so they are machine checked conditional on that
citation; existence, uniqueness, (iii) and (vi) are unconditional. The
reduction of the multi-review spanning problem to per-fund problems in
(vi), the static ceiling's transfer, and the reading of the at-zero
case are paper level. The proof imports the proof modules of claims 104
and 029, and the axiom audit reports only standard axioms. The
independent paper-to-formal fidelity review matches the claim; it
found the prose differing from the formal statement at two boundaries,
the box conditions in (iii) and the sale side of (vi), which math has
since corrected to the formal forms stated above.

Proposition 45 corresponds to
\(\texttt{claims/104-m7-two-stage-exactness-loss.md}\), the refile of claim 103,
which red refuted because its exactness criterion in (iii), the ETF
self-band alone, was necessary but not sufficient: a fund can leave
the exposure drifting rather than re-hedge through a costly ETF. Red's
review of the refile then required two corrections, the box
multiplier \(\mu_J\) in (149)'s upper bound (red's capped counterexample) and
the fee and residual terms and the choice of shadow price in the
binding-budget criterion; mathb made them, red's recheck passed them,
and PM approved. It is the companion result that Propositions 35 and
39 build on. The statement and proof modules in the proof map machine
check:
- the joint criterion, conditional on AX-13, through a lifted problem
  with one cost bound per instrument and the box signs in normal-cone
  form;
- (i): the transfer of Propositions 22 and 23, the reference case's
  vanishing cross moments, the concavity of the residual value, and
  the representation of every instance by finitely many scenarios;
- (ii): the explicit optimum and exactness of both procedures;
- (iii), conditional on AX-13: exactness iff (148), with general \(V\)
  and ETF residual risk, and the soft procedure's exactness;
- (iv): (149), with \(\mu_J=0\) at an interior holding;
- (v): (150) at \(b^*\), with the operator norms entering as any bounds,
  and, conditional on AX-13, the binding-budget criterion and the bound
  with the fibre problem's cash multiplier.
The measure-zero reading in (iii) is paper level. The proof imports the
proof modules of claims 027, 028 and 031, and the axiom audit reports
only standard axioms. The independent paper-to-formal fidelity review
matches the claim, with the joint criterion, (iii) and the
binding-budget case conditional on AX-13 and the rest unconditional.

Proposition 46 corresponds to
\(\texttt{claims/040-m7-fund-decision-with-etfs-at-zero.md}\), the companion
result Propositions 40 and 41 build on. Red's review required one
correction, the drop-Z comparison in (iv) at a box bound, where both
rules can clip to the same bound; after math added the premium-error
formula in (iii) and the fold-in reading, PM withdrew the verdict, and
red's re-review required a second correction, the sign of the fold-in's
ETF premium. Math made both, red passed the result, and PM approved.
The statement and proof modules in the proof map machine check:
- the coordinate change, the equivalence of the bound with \(w\geq Qx^A\), and
  the transfer of the coordinate optimum to the review's optimum;
- (i), conditional on AX-13: the ETF lines with their slacks and the
  fund lines with the at-zero term;
- (ii): existence and uniqueness of \(w(q)\) and \(\zeta(q)\), the Schur-block
  characterization (151), and the concavity and gradient of \(V_E\);
- (iii): the marginal (152), the optimization of the exposure, the
  hold test for any \(N\), the readings at the optimum, the one-fund rule
  with its box conditions, and the premium-error shift;
- (iv): the pieces and their slopes, the unique roots, the optimum, the
  drop-Z comparison with its box-bound case, and the ordering when the
  at-zero set grows or shrinks along the trade;
- (v): the one-ETF test and marginal.
Only (i) takes AX-13 as a hypothesis; the rest is unconditional. The
identification of (152) with Proposition 28's reduced moments, the
reading that a held fund does not move until the premium shift leaves
its band, the direction-dependence reading and the comparison with
Jagannathan and Ma are paper level. The proof imports claim 104's proof
module, whose ETF-coordinate objects Proposition 40's second formal
stage now uses, and the axiom audit reports only standard axioms. The
independent paper-to-formal fidelity review matches the claim, with (i)
conditional on AX-13; it notes that (i) needs every ETF below its cap,
which the text states.

Proposition 47 corresponds to
\(\texttt{claims/110-m7-one-etf-two-scalars.md}\). Red passed it on red's own
implementation of the two-scalar rule against a joint solve, and PM
approved; red's one nit, that the cash-price monotonicity in (iv) holds
at a fixed exposure price, is made. Experiment 045 agrees with it and
illustrates it. The statement and proof modules in the proof map machine
check:
- (i): the clip as the unique maximizer of each fund's one-fund problem,
  the monotonicity of \(r_ix_i\) in \(m\) and of \(x_i\) in \(\eta\), the properties of \(q\)
  and \(p\), the unique roots \(m_0\), \(m_I\) and the traded prices, and the fund
  marginal as a coordinate derivative;
- (ii), for every \(\eta\geq0\) and \(\sigma_E\geq0\): the Lagrangian's unique maximizer, the
  funds' clips and the ETF's holding at it, and the status table (155)
  with each regime's price;
- (iii): the monotone cash slack, the slack-budget case, and that any
  budget-exhausting \(\eta\) gives the unique constrained optimum;
- (iv): (156) and its mirror, and both comparative statics.
The existence of such an \(\eta\) when the budget binds is paper level,
through AX-13, and (iii)'s constrained-optimum statement is conditional
on it. The formal model is the claim's own one-ETF coordinates; its link
to the general review model is paper level, as PM's scope note says.
The proof uses Mathlib only, and the axiom audit reports only standard
axioms. The independent paper-to-formal fidelity review matches the
claim in these one-ETF coordinates, unconditional apart from the
declared cash price; the auditor checked the link to the general model
by hand.

Proposition 48 corresponds to
\(\texttt{claims/111-m7-incumbent-aware-first-stage.md}\). Lean B's prose
points were made before red's review; red passed the claim on 400 random
instances with fees, ETF rates, ETFs at zero and a tight budget on half,
and PM approved, with part 4 reading exactness and fundability, not
loss. Experiment 045 illustrates it: on the 594 draws where both first
stages could fund their exposure, the incumbent-aware stage was exact on
122 against 15 for Proposition 40's, but lost more when inexact (median
32 against 15.5 basis points); experiment 044 found Proposition 40's
first stage unfundable on 41% of its draws. The statement and proof
modules in the proof map machine check:
- the marginals \(g_E\) and the fund identity \(g_A=\tilde\alpha-\gamma Vx^A+Q^\top g_E\);
- (i), unconditionally: the objective bound at any feasible point, the
  lower bound by strong concavity (the paper proof cites AX-13 at \(x_J\);
  the formal one does not need it), (158), and \(\Lambda=0\) iff \(x_2=x_J\);
- (ii): the equivalence of \(s=0\) with Proposition 41's joint criterion,
  unconditionally, with its consequence \(x_2=x_J\); the converse, conditional
  on AX-13 through Proposition 45's joint optimality, with no binding
  ETF cap; and \(s_j=0\) at an interior traded ETF under a slack budget;
- (iii): the three exactness cases, the joint criterion's sufficiency
  proved directly.
The existence of the fibre multipliers is AX-13 on the fibre problem, a
paper step; the statements that hold for every valid choice rest on it.
The binding-budget reading, part 4's comparison and the experiment
readings are paper level. The proof imports the proof modules of
claims 104, 109 and 040, and the axiom audit reports only standard
axioms. An independent paper-to-formal fidelity review of this result
has not yet been recorded.

Proposition 49 corresponds to
\(\texttt{claims/043-m7-fine-cost-sandwich-with-one-costly-etf.md}\). Red's review
required one correction, applying AX-16 through a change of variables
that turns the pair's gradient set into the source's cash-only box,
with the cost, covariance, equation and support function checked to
transform consistently; math made it, red's recheck passed it with a
nit (that \(k^*\) lies in the sandwich while its position is open), and PM
approved. Experiment 046 finds every cell it resolves inside the
sandwich, an illustration. The statement and proof modules in the proof
map machine check, for every number \(a\) that lies between the values of
all classical subsolutions and supersolutions with the stated growth:
- (i): the separable test functions as sub- and supersolutions, the
  general lower bound with its maximum attained, (160), and the third
  lower bound;
- (ii): the uncorrelated case;
- (iii): the identity and the bound (by concavity);
- (iv): the effective rate, the band-width arithmetic of claim 042's
  reading, and both limits.
None of these uses AX-16: it enters the formal statement only as a
proposition asserting that such an \(a\) exists. That the pair's corrector
eigenvalue is such an \(a\), with the hypothesis check through the change
of variables and the classical-to-viscosity step, is the cited AX-16
and a reviewed paper step. The first-order expansion of (iii), the
identification with Proposition 38's re-hedge term, the non-ergodic
reading of the frozen end and the band readings are paper level. The
proof imports claim 042's proof module, and the axiom audit reports
only standard axioms. An independent paper-to-formal fidelity review
of this result has not yet been recorded.

Proposition 50 corresponds to
\(\texttt{claims/044-m7-two-reviews-binding-budget.md}\), the first result of the
direction on dynamics with a binding budget. Red passed it and PM
approved; experiment 047 agrees with its proved parts and found the
joint hoarding and front-loading reading failing by substitution in 12
of 82 cases, so math narrowed that reading to one instrument with the
other held fixed, and this write-up follows PM's instruction to present
the dynamic cash price and the incumbent values as the result. The
statement and proof modules in the proof map machine check, in the
claim's two-review coordinates for any finite instrument set and state
set, with each covariance only positive semidefinite and finite caps:
- (i): existence, the concavity of the whole problem, of tomorrow's
  value and of the root objective, and monotonicity in cash;
- (ii): sufficiency of the lines by a direct Lagrangian bound,
  unconditionally; necessity, with one tomorrow slope in both sets of
  lines, conditional on AX-13; and the readings of \(s_i(z')\);
- (iii): the slack-tomorrow case and the bounds (163) with the weak
  purchase and sale conditions;
- (iv): the myopic-optimality test, conditional on AX-13; the pinned
  multiplier; the slack-tomorrow condition and the held-today band;
  \(\beta\mathbb E[g_it_{1,i}]=0\) for an interior trade with today's budget slack; the
  residual identity; and the tangent-line bounds of slope \(r\) along one
  instrument;
- (v): each review's holdings as its one-review Lagrangian's maximizer,
  the band in the marginal with its width, and the costless instrument's
  line.
Paper level are the exact value of the one-sided derivative (equal to
\(r\) only for a given choice of tomorrow's multipliers), strict improvement
in the opposite direction, the interval case of the multiplier set, the
joint comparative static, the width in holdings, the link to
Proposition 47's coordinates, and the uncapped ETF. Two readings in the
claim hold formally only as stated here: the zero condition in (iv)
needs today's budget slack, and a purchase today with some state
buying again tomorrow is not myopically optimal only if no other state
sells. The proof imports claim 104's statement and proof module, with
the two-review lifting proved here, and the axiom audit reports only
standard axioms. An independent paper-to-formal fidelity review of
this result has not yet been recorded.

Proposition 51 corresponds to
\(\texttt{claims/046-m7-two-reviews-bounds-in-the-inputs.md}\), the refile of claim
045, which red refuted because its (iii) failed when today's budget
binds at the myopic root, where today's cash price is free, and for a
costless instrument with a slack budget tomorrow, where the equation is
an identity. The refile states (iii) with today's budget slack and
names both cases; red's review required one more correction (the
identity needs the instrument costless on both sides), which math made;
red's recheck passed it and PM approved. Experiments 049 and 047
illustrate it. The statement and proof modules in the proof map machine
check, reusing claim 044's objects:
- (i): the admissible selection below \(\bar\eta\), the zero multiplier when the
  cash covers \(\mathrm{need}\), the bound for any tomorrow family in states that
  trade or keep cash, the bracket on \(\hat\eta_0\), and \(\hat\eta_0=\eta_0\) when every state
  is covered and some cash is carried;
- (ii): (165), the residual's bracket and the two sufficient sign
  conditions;
- (iii): the root line's value at an interior trade with today's budget
  slack, the costless identity, and (166) with today's budget binding;
- (iv): the hedge-term identity at the reduced point and the
  one-variable concave step.
Nonnegative off-diagonal covariances tomorrow are stated for any finite
set of instruments. Paper level are the link from (iv)'s two formal
ingredients to (167) (the reduced root objective's concavity and its
one-sided derivatives as extremes over tomorrow's multipliers, which
needs Danskin's theorem with AX-13 on tomorrow's value), the edge case
of (i) with no cash carried, the joint admissibility of a per-state
selection, and the reading of (iii)'s equation as nongeneric. The proof
imports claim 044's modules, and the axiom audit reports only standard
axioms. The independent paper-to-formal fidelity review matches (i)-(iii),
unconditionally given tomorrow's multipliers, and records (iv) as two
formal ingredients whose link to (167) is paper level, as stated.

Proposition 52 corresponds to
\(\texttt{claims/112-m8-worked-learning-example.md}\), on the lab's M8 (the
two-review worked model with both shock laws). Red's reviews required
six corrections, among them restricting the Gaussian-law second-review
statements to nonnegative marked holdings, the condition under which
the two means differ, and citing the filter's two meanings through
AX-17 and AX-18; mathb made them, red passed the claim and PM approved.
Experiment 050 reproduces the example independently. The statement and
proof modules in the proof map machine check, in the model's own
coordinates with its finite tree mapped into Proposition 50's:
- (i) under the finite law: the posterior variance, the positive
  definite predictive covariance and unique target, marking, the
  nonempty feasible sets and unique review optima, and the existence of
  an optimal two-review policy (through claim 044's part 1);
- (ii)'s moment content for any finite laws with the stated moments:
  the innovation's mean and variance, the error variance, the zero
  cross-block moment, the posterior mean's average, the non-coincidence
  condition, red's two-point counterexample and the example's node;
- (iii)'s slack-budget threshold;
- (iv)'s first-review numbers exactly.
Paper level are the filter's two meanings (cited, AX-17 and AX-18), the
Gaussian-law statements, the transfer in (iii), the case with no cash
today, and the example's later tables. The proof imports claim 044's
modules, and the axiom audit reports only standard axioms. The
independent paper-to-formal fidelity review matches this scope; it
notes that the claim's phrase "the exact Bayes posterior only under
Gaussian noise" should read as sufficiency after AX-17's fix, which
this write-up follows.

Proposition 53 corresponds to
\(\texttt{claims/047-m8-reserve-rule-one-fund-one-etf.md}\), the first result of the
second focused request's reserve direction. The reviews required
corrections: red's, reading the cost-channel reserve through the ETF's
expected marked slope including held marginals rather than the
probability of a trade, and the factors on the threshold errors; Lean
B's, taking the certificate at the dynamic root's own need; the claim was
also revised after experiment 053 showed that its one-shot reading
misleads, to state (169) as a fixed point. Red's rechecks passed and PM
approved. The statement and proof modules in the proof map machine
check, on Propositions 50-51's objects with the revision entering as
a hypothesis on tomorrow's means bounded by its extremes:
- (ii): the budget channel's absence at any root with positive cash
  covering its need, the certificate, (168), the finite-law bounds
  over the uncovered states for every tomorrow family, and the
  threshold errors;
- (iii): the reserve premium as the root line less the one-review line,
  its expansion by state, (169), its bound, and the no-shift case;
- (iv): (170) and the need's slope in the purchase rate on the active
  set, and the ETF unit count;
- (v): (171), given that some tomorrow family exists and every family
  prices cash somewhere.
Paper level are (i)'s definitions and readings, the direction of
(iii)'s reading (Proposition 51's one-variable step), (169)'s
uniqueness and its fixed-point computation, (ii)'s sufficient
conditions for the cost channel and the idleness bound, the Gaussian
tail moments (which need Proposition 50's lines under the Gaussian law,
proved only for the finite law), the reserve's non-monotonicity, and
the experiments' readings. No cited result or hypothesis structure is
used, and the axiom audit reports only standard axioms. An independent
paper-to-formal fidelity review of this result has not yet been
recorded.

Proposition 54 corresponds to
\(\texttt{claims/113-m7-several-funds-one-etf-reserve.md}\). Red passed it on red's
own two-fund, one-ETF solver, Lean B's three prose points were made,
and PM approved; red's two nits went to mathb. The statement and proof
modules in the proof map machine check, on Propositions 50-51's objects
for any finite set of instruments, with the model's factor structure
as a hypothesis:
- (i): each fund's marginal and its root holding as Proposition 47's
  clip with \(S_i\) added, the clip shown equal to Proposition 47's formal
  one;
- (ii): the state check with the threshold clipped at zero, the
  every-state family with \(\eta_1=0\) and Proposition 26's brackets (every
  family when cash is positive), and the pooling inequality;
- (iii): (172) on the trading pieces;
- (iv): (173), the clip's Lipschitz bound, and the relation to
  Proposition 53's reserve counted at the ETF's worst-case liquidation.
Paper level are the common cash price as Proposition 47's root with \(N\)
funds, the product-tree pooling remark, the fixed-point remark, and the
carried-over cost channel. The proof imports claims 044's and 046's
modules, and the axiom audit reports only standard axioms. An
independent paper-to-formal fidelity review of this result has not
yet been recorded.

Proposition 55 corresponds to
\(\texttt{claims/048-m7-many-funds-many-etfs-two-reviews.md}\). Red's review required
the qualification that the separation is of the lines given the
tomorrow numbers at the optimum, a fixed point of the joint root, not
of two independent problems (red's test moved the ETFs 1% and changed
the funds' incumbent values); math made it, red's recheck passed and PM
approved. The statement and proof modules in the proof map machine
check, in Proposition 50's formal model with funds and ETFs as the
instruments and the root's moments from the factor model:
- (i): sufficiency of the lines without citation, necessity conditional
  on AX-13, and the root as the one-review Lagrangian's maximizer at
  \((\mu_0+S,\hat\eta_0)\);
- (ii): necessity and sufficiency of (175) at the tilted inputs, the
  tomorrow numbers read from the same policy's multipliers;
- (iii): both identities in (176).
The ETFs' rates are review-independent in the model, so frictionless
today means frictionless tomorrow. (iv) is a reading of Proposition
41's obstruction, and the check's costly-ETF count illustrates it. The
proof imports claims 044's, 104's and 110's modules, and the axiom audit
reports only standard axioms. An independent paper-to-formal fidelity
review of this result has not yet been recorded.

Proposition 56 corresponds to
\(\texttt{claims/049-m7-quantile-flexibility-test-full-menu.md}\). Red's review
re-derived every step and tested (iii)'s bound on red's own solver at
300 of 300 instances (164 with a positive tail term, largest ratio of
loss to bound 0.61). It required one correction: the one-ETF band term
uses the ETF's variance net of the funds, not its own variance (30 of
300 instances exceeded the old form, by up to 5.9 times). Math made it,
with red's point that under the test the tail term is the plain
expectation, and PM approved. The statement and proof modules in the
proof map machine check, in Proposition 55's model with the ETFs a set
among the instruments:
- (i): \(\mathrm{need}\leq\mathrm{liq}\) at a state makes \(\eta_1=0\) admissible there, from any
  admissible multiplier, with the proceeds summed over the ETFs;
- (ii): the quantile equivalence, its state-free form, and the tail
  identity with its bound, proved directly on the finite law;
- (iii): the loss bound for every feasible policy, from today's strong
  concavity at the myopic root, the relaxed tomorrow's supergradient
  and Proposition 48's completed square, with the tail term from the
  budgeted tomorrow's Lagrangian bound; and the band term's bound in
  the inputs.
The multipliers' existence (AX-13) enters as hypotheses; the one-ETF
form of the band term is at paper level, and the ledger's tail measure
(AX-19) is cited for its reading, not used formally. The proof imports
claims 113's and 111's proof modules, and the axiom audit reports only
standard axioms. An independent paper-to-formal fidelity review
of this result has not yet been recorded.

Proposition 57 corresponds to
\(\texttt{claims/114-m9-predictable-and-unpredictable-target-move.md}\), on the lab's
M9. Red's review required four corrections, made by mathb: the width's
direction per instrument, with the positive semidefinite order only
sufficient for all instruments together (red's counterexample at M8's
inputs); the positive part kept around the whole need in (v); the
variance recursion's convergence argued block by block, with AX-10
cited for the steady state's form only; and the half-open probability
in (iii) when the innovation has atoms. PM approved. Red's recheck then
found that the threshold reading in (iv) used the myopic tomorrow's
incumbent value at the dynamic root; mathb restated it at the dynamic
root with its own incumbent value, as (180), the direction
\(a^{\rm dyn}_0\geq a^{\rm my}_0\) unchanged. Experiment 057 illustrates it: in 24 of 24 cells
meeting the myopic condition the order held, while the dynamic root's
tomorrow bought in only 4 to 14 of 16 states and the threshold lay
strictly between its ends. The statement and proof modules in the
proof map machine check, on Proposition 52's objects with scalar blocks
and Proposition 50's two-review objects for (iv):
- (i): the decomposition as an identity, and the innovation part's mean
  zero and covariance under any finite laws with the stated moments and
  independent blocks;
- (ii): the variance change, the per-instrument criterion, the cases
  where both blocks move the same way, the mixed-blocks instance, and
  the recursion's convergence to a fixed point, unique when \(q>0\) or
  \(\phi^2<1\);
- (iii): \(U-D\) as the half-open probability, the tilt's sign, and the full
  shift beyond the support;
- (iv): the tangent-plane bound, the pinned \(S_A\), the strict decrease,
  \(a^{\rm dyn}_0\geq a^{\rm my}_0\) (and its mirror) when the roots agree off the fund, the
  equality case of (180), and (180) itself with its equality condition, for a purchase.
These are one-coordinate statements; nothing is said about the joint
move, which experiment 047 showed can reverse. The case of a free ETF
and (v) rest on Propositions 54 and 51 at paper level, and so does
the mirror bound on the sale threshold; (vi) is a reading, and the
transient filter's posterior meaning is not shown.
The proof imports claim 044's module, and the axiom audit reports only
standard axioms. An independent paper-to-formal fidelity review of
this result has not yet been recorded.

Proposition 58 corresponds to
\(\texttt{claims/115-m9-quantile-flexibility-test-time-varying.md}\), on the lab's
M9. Red rederived each part and tested (ii)'s bound on its own solver
at 583 holdings (120 front-loaded points, 120 myopic roots and 343
random feasible roots; the loss at most 0.99 of the bound). Red required
one correction: the root residual must minimize over the admissible
slopes at tomorrow's bound states, since with one fixed choice the
residual at the front-loaded point was nonzero at 8 of 120 points, and
with the free choice zero at all 120. Mathb made it, red's fresh
verdict passed it, and PM approved; math's reply recorded how the
claim composes with Proposition 56. The statement and proof modules in
the proof map machine check:
- (i): the split test's equivalence and its state-free form, as exact
  rewritings, with the planned purchase from tomorrow's predictable
  mean and \(g^{\min}\);
- (ii): the bound at any feasible holding, for every admissible choice
  of line values and relaxed slope families, including the interval
  slopes at bound states, and the corollary that a zero residual leaves
  the tail term alone;
- (iii): the pinned \(S_A\) at the myopic root's relaxed tomorrow and the
  block-inverse entry.
At paper level: Proposition 56's instantiation on this tree (its formal
statement is over any finite tree with state-dependent means); the
zero residual at the front-loaded point, from the relaxed program's
optimality conditions (AX-13); the tail-measure form of the bound; the
assembly of (183) and the mirror for a fall; the reading of which
point to hold; and the Gaussian quantile, which is not shown.
The proof imports claim 049's proof module, and the axiom audit reports
only standard axioms. An independent paper-to-formal fidelity review
of this result has not yet been recorded.

The conditional parts in this draft rest on three cited theorems:
- the linear-programming vertex theorem: Proposition 24's face
  finiteness;
- the polyhedral Karush-Kuhn-Tucker theorem: Proposition 39's
  multiplier test in (i), Proposition 41 (i) and (iv)'s criterion,
  Proposition 44 (i), (ii), (iv) and (v), Proposition 45's joint
  criterion, (iii) and binding-budget case in (v), Proposition 46
  (i), Proposition 55 (i)'s necessity, Proposition 56's multipliers,
  Proposition 58's zero residual at the front-loaded point (at paper
  level),
  Proposition 47 (iii) when the
  budget binds (at paper level),
  Proposition 48 (ii)'s converse, with the existence of its
  multipliers at paper level, and Proposition 50 (ii)'s necessity and
  (iv)'s test, and Proposition 51 (iv)'s link at paper level;
- Topkis's lattice theorems: Proposition 43 (ii).

The detailed statement
comparison belongs in \(\texttt{board/FIDELITY.md}\).

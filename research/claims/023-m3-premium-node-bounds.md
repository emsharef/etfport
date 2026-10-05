---
id: 23
title: "The premium of future ETF adjustment decomposes across observations, is bounded below by adjustable wealth, and its bounds certify both channel signs"
status: formalized
model_version: M3
depends_on: [11, 12, 22]
axioms_used: [AX-08]
formal: lean/Standalone/M3PremiumNodeBounds.lean
direction: D6
---
## Statement

Claim 022 bounds the ETF channel Delta_E-Delta_N between differences of the
premium of future ETF adjustment phi at the two root classes' optimizers and
caps phi from above by adjustable wealth. PM's D6 note asks for the converse:
a lower bound on phi by adjustable wealth, so that comparing the two optima
gives a sufficient sign condition through the sandwich. This claim gives an
exact decomposition of phi across public observations, node-level lower
bounds and caps, the resulting sign conditions, and two certifications.
All wealth quantities are in units of W_0^- (divide dollar amounts by W_0^-).

**Setting.** Any M3 instance, as in claim 022, and a fixed feasible root
trade u_0 with post-root cash h and post-root holdings x^+_0. For a public
observation y with P_0(y)>0, the *node paths* are the pairs (theta,s_1) with
pi_1(theta|y)>0 and q_{s_1}>0; the marked holdings at y are
m_A(y)=x^+_{0,A} d_A(y) and m_j(y)=x^+_{0,j} d_j(y); the *no-trade node
wealth* is W^N_y=h+m_A(y) g_A^1+sum_j m_j(y) g_j^1 on a node path with
second-quarter gross returns g^1. The *node certainty equivalent* under
control R is

```
c^R_y = -(1/rho) ln(-V_1^R(x_1^-(y),h,pi_1(.|y))),
```

the *node gain* is G_y=c^E_y-c^N_y>=0, and the *node weights* are

```
w_y = P_0(y) exp(-rho c^N_y) / sum_{y'} P_0(y') exp(-rho c^N_{y'}).
```

Costs kappa^+_j, kappa^-_j are the ETF j rates. Over the node paths let
gbar_{j,y}, gunder_{j,y} be the largest and smallest gross returns of ETF j,
s_{j,y}=(gbar_{j,y}-gunder_{j,y})/2 its half-range, and up_y, down_y the
largest (gbar_{j,y}-1)^+ and (1-gunder_{j,y})^+ over ETFs. The *tilted node
measure* Q_y weights each node path by its mass times exp(-rho W^N_y),
normalized, and the *risk-adjusted excess returns* are

```
r^+_{j,y} = E_{Q_y}[(g_j^1-1-kappa^+_j)/(1+kappa^+_j)],    r^-_{j,y} = E_{Q_y}[1-kappa^-_j-g_j^1].
```

1. **Exact node decomposition.** For every feasible root trade,

   ```
   phi(u_0) = -(1/rho) ln sum_y w_y exp(-rho G_y),
   ```

   a strictly increasing function of each node gain, with
   min_y G_y <= phi(u_0) <= max_y G_y. Any node-wise bounds on the G_y
   therefore aggregate to bounds on phi through the same formula.

2. **Node lower bounds by adjustable wealth.** At a node y:
   (a) *Sure sign.* If some ETF j has g_j^1>=1+delta on every node path with
   delta>kappa^+_j, then G_y>=h[(1+delta)/(1+kappa^+_j)-1]; if g_j^1<=1-delta
   on every node path with delta>kappa^-_j, then G_y>=m_j(y)(delta-kappa^-_j).
   (b) *Risk-adjusted.* If r^+_{j,y}>0 then

   ```
   G_y >= r^2/(2 rho s^2)  when r <= rho s^2 h,   and   G_y >= r h - rho s^2 h^2/2 >= r h/2  otherwise,
   ```

   with r=r^+_{j,y}, s=s_{j,y} (read r h when s=0). If r^-_{j,y}>0 the same
   holds with m_j(y) in place of h and r=r^-_{j,y}. Let G^lb_y be the
   largest of the applicable bounds, zero if none applies, and

   ```
   alpha(u_0) = -(1/rho) ln sum_y w_y exp(-rho G^lb_y)  <=  phi(u_0).
   ```

   When the adjustable wealth binds (r>rho s^2 h, or the sure-sign case) the
   node bound r h-rho s^2 h^2/2 is quadratic in that wealth and its lower
   bound r h/2 is linear in it: cash at a buying node, marked ETF value at a
   selling node, times half an excess-return rate net of costs.

3. **Node caps.** G_y <= G^ub_y = h up_y + sum_j m_j(y)(up_y+down_y), and

   ```
   phi(u_0) <= beta_node(u_0) = -(1/rho) ln sum_y w_y exp(-rho G^ub_y) <= beta(u_0),
   ```

   with beta claim 022's cap.

4. **Sufficient sign conditions.** With claim 022's optimizers A_R, B_R:

   ```
   beta_node(A_E) < alpha(B_N)   implies   Delta_E-Delta_N <= beta_node(A_E)-alpha(B_N) < 0,
   alpha(A_N) > beta_node(B_E)   implies   Delta_E-Delta_N >= alpha(A_N)-beta_node(B_E) > 0.
   ```

   Robust forms, for any u in F_0 and v in E_0:

   ```
   Delta_E-Delta_N >= alpha(u) - [CE_{F,N}-c_N(u)] - beta_node(B_E),
   Delta_E-Delta_N <= beta_node(A_E) - alpha(v) + [CE_{E,N}-c_N(v)],
   ```

   where c_N(u) is claim 022's root-action continuation certainty
   equivalent and the bracket is u's suboptimality under no future trade.
   In the sure-sign regime both sides are comparisons of adjustable-wealth
   quantities at the two root optima: cash and marked ETF value times
   net excess-return rates against cash and ETF value times return spreads.

5. **Two certifications at zero rates.**
   (i) *Claim 022's sure-active family* (negative channel): the full-root
   optimizer under future ETF-only trading is uniquely the all-active root,
   so beta_node(A_E)=0, and the ETF-only root's no-trade optimizer is uniquely
   cash, at which the buying node under theta_+ gives the sure-sign bound
   h(3/2-1)=1/2 and the theta_- node gives 0, so

   ```
   alpha(B_N) = [ln(3/2) - ln(1+exp(-10)/2)]/20 > 1/50,
   Delta_E-Delta_N <= -alpha(B_N) < -1/50.
   ```

   Numerically the channel is -0.020272 and the bound equals it to six
   decimals.
   (ii) *Claim 012's family* (positive channel): with u=(7/15,8/15) (cash
   zero) and B_E the cash root (claim 012 part 3),

   ```
   alpha(u) = -(1/20) ln[ w exp(-8/3) + (1-w) ],   w = 1/(1+exp(-8/3)),
   c_N(u) = -(1/20) ln[ (exp(-71/3)+exp(-79/3))/2 ],   CE_{F,N}=5/4,
   beta_node(B_E) = -(1/20) ln[(1+exp(-10))/2],
   Delta_E-Delta_N >= alpha(u) - [5/4-c_N(u)] - beta_node(B_E) > 3/100.
   ```

   Numerically the bound is 0.03201 and the channel 0.03370.

**Consequence for D6** (a reading of 1-5, not a further theorem). The
converse of claim 022's cap exists: at each observation the option to adjust
ETFs is worth at least a risk-adjusted excess return times the wealth that
can be redeployed, once that wealth binds, and the premium is the exact
utility-weighted aggregate of these node gains. The sign of the ETF channel
is therefore bounded, through the sandwich, by comparing redeployable
wealth times net excess return at the ETF-only root's optimum against
redeployable wealth times return spread at the full root's optimum, and
conversely; these are sufficient conditions. In the stylized families they
are tight. On experiment 015's calibrated instances the lower bounds are
within about a quarter of the true premia, but the caps are about thirty
times the premia at rho=5, ninety to three hundred and seventy times at
rho=10 and 20, and unbounded at rho=20's ETF-only optima, whose premium is
zero; so the conditions do not certify those signs, and a sharper cap is
what remains for a class-wide sign condition there.

## Proof

### 1. The decomposition

By M3's definitions, H_0^R(u_0)=sum_y P_0(y) V_1^R(x_1^-(y;u_0),h,pi_1(.|y))
and V_1^R=-exp(-rho c^R_y) at each node (claim 011 part 2 gives attainment
and -1<V_1^R<0). Hence

```
H_0^E(u_0)/H_0^N(u_0) = sum_y P_0(y) exp(-rho c^E_y) / sum_y P_0(y) exp(-rho c^N_y)
                      = sum_y w_y exp(-rho G_y),
```

and phi=c_E-c_N=-(1/rho) ln of that ratio. The function is strictly
increasing in each G_y because w_y>0 and exp is decreasing; the extreme
bounds follow from min and max over the finitely many nodes.

### 2. Node lower bounds

At node y the review-1 problem under E_1 chooses an ETF trade u with
u_j>=-m_j(y), sum_j u_j+C(u)<=h, and has terminal wealth
W^N_y+sum_j u_j(g_j^1-1)-C(u) on each node path. Its node certainty
equivalent is at least that of any one feasible trade.

(a) Buying epsilon in [0,h] dollars of ETF j buys epsilon/(1+kappa^+_j)
units, so the wealth becomes W^N_y+epsilon (g_j^1-1-kappa^+_j)/(1+kappa^+_j).
If g_j^1>=1+delta on every node path, epsilon=h gives wealth at least
W^N_y+h[(1+delta)/(1+kappa^+_j)-1] pathwise, hence the node certainty
equivalent rises by at least that constant (exponential utility shifts by a
constant exactly). Selling epsilon in [0,m_j(y)] dollars of ETF j yields
epsilon(1-kappa^-_j) cash and forgoes epsilon g_j^1, so wealth becomes
W^N_y+epsilon(1-kappa^-_j-g_j^1); if g_j^1<=1-delta pathwise, epsilon=m_j(y)
gives at least m_j(y)(delta-kappa^-_j).

(b) Let f(epsilon)=-(1/rho) ln E_y exp(-rho W_epsilon) for the buying trade,
with Z=(g_j^1-1-kappa^+_j)/(1+kappa^+_j) the per-dollar excess. Factoring
the no-trade term, f(epsilon)=f(0)-(1/rho) ln E_{Q_y} exp(-rho epsilon Z),
with Q_y the tilted node measure. The step is Hoeffding's lemma through
ledger entry `AX-08` (`rigollet2023high` Lemma 1.8; cited, not re-proved,
per rule 21): for a random variable X with E X=0 and values in an interval
of length L, E exp(s X) <= exp(s^2 L^2/8) for every real s; applied to X-E X
it reads ln E exp(lambda X) <= lambda E X + lambda^2 L^2/8. Its hypotheses
hold here: under Q_y, Z takes values in an interval
of length at most 2s/(1+kappa^+_j)<=2s on the finitely many node paths, and
E_{Q_y} Z=r=r^+_{j,y}. With lambda=-rho epsilon,

```
f(epsilon) >= f(0) + r epsilon - rho s^2 epsilon^2/2,
```

for epsilon in [0,h]. As `AX-08`'s Formal paragraph records, the lemma
enters the formalization through Mathlib's machine-checked
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` under PM's rule-21 reading
(NOTICES, 2026-09-28). If r<=rho s^2 h the right side is maximized at
epsilon=r/(rho s^2)<=h with value f(0)+r^2/(2 rho s^2); otherwise take
epsilon=h, and r>rho s^2 h gives r h-rho s^2 h^2/2>=r h/2. When s=0 the
quadratic term vanishes and epsilon=h gives r h. The selling case is the
same with Z=1-kappa^-_j-g_j^1 and epsilon in [0,m_j(y)]. Since G_y is at
least each applicable bound, G_y>=G^lb_y, and part 1's monotonicity gives
alpha(u_0)<=phi(u_0).

### 3. Node caps

Claim 022's part 2 argument at a single node, with up and down taken over
that node's paths and ETFs, gives W^E-W^N<=h up_y+sum_j m_j(y)(up_y+down_y)
pathwise for every feasible E_1 trade, hence G_y<=G^ub_y. Part 1 gives
phi<=beta_node. Since G^ub_y<=W_0^- beta(u_0) for every y (the global up
and down dominate the node ones and m_j(y)<=x^+_{0,j} gbar_E), and the
aggregate is at most max_y G^ub_y, beta_node<=beta.

### 4. Sign conditions

Substitute alpha<=phi<=beta_node into claim 022's sandwich. For the robust
lower form: CE_{F,E}>=c_E(u)=c_N(u)+phi(u)>=c_N(u)+alpha(u) for any u in
F_0, and CE_{E,E}=c_E(B_E)=c_N(B_E)+phi(B_E)<=CE_{E,N}+beta_node(B_E); subtract
and add and subtract CE_{F,N}. The robust upper form is symmetric with v in
E_0 and A_E.

### 5. The certifications

(i) *Sure-active family, zero rates.* Every policy has W_2<=9/4 on every
path (claim 022 part 4), and the all-active root attains 9/4 surely, so an
optimizer under E_1 has W_2=9/4 almost surely; under theta_- the bound reads
W_2<=(9/4)a+h+p/2 with the active holding locked, which equals 9/4 only if
a=1, h=p=0. So A_E is all-active, with h=0 and no ETF: every node cap is 0
and beta_node(A_E)=0. For the ETF-only root under no future trade, a static
ETF position p>0 has E[W_2]=h+(11/12)p<1, so its certainty equivalent is
below cash's value 1: B_N is cash. At B_N the theta_+ node (posterior mass
one on theta_+, ETF gross return 3/2 on its only path) is a sure-sign buying
node with h=1 and delta=1/2, so G^lb=1/2; the theta_- node has m=0 and cash
cannot profit from a falling ETF, so G^lb=0. Both node certainty
equivalents equal 1 (cash), so w=(1/3,2/3), and
alpha(B_N)=-(1/20) ln[(1/3)exp(-10)+2/3]=[ln(3/2)-ln(1+exp(-10)/2)]/20, which
exceeds 1/50 since ln(3/2)>2/5 (claim 022 part 4) and the correction is
below 1/16000. The first line of part 4 gives the bound; this alpha(B_N)
equals CE_{E,E}-1 exactly, because the sure-sign trade is the optimal one
at each node, which is why the bound is tight.

(ii) *Claim 012's family, zero rates.* CE_{F,N}=5/4 (claim 012 part 2).
At u=(7/15,8/15), h=0 and the no-trade node wealths are 71/60 under theta_+
and 79/60 under theta_-, so c_N(u) is the displayed value and
w_+=exp(-71/3)/(exp(-71/3)+exp(-79/3))=1/(1+exp(-8/3)). At the theta_+ node
the ETF's next return is surely 1/2 and the marked ETF value is
(8/15)(1/2)=4/15, a sure-sign selling node with G^lb=(4/15)(1/2)=2/15; at
the theta_- node the ETF surely returns 3/2 but h=0, so G^lb=0. Hence
alpha(u)=-(1/20) ln[w_+ exp(-8/3)+(1-w_+)]. Claim 012 part 3 shows the cash
root is the unique ETF-only optimizer under E_1 (its bound f(p) is strictly
concave with f'(0)<0, so f(p)<f(0) for p>0, and the cash root attains
f(0)); at the cash root the theta_+ node has up=0 and m=0, cap 0, and the
theta_- node has up=1/2, cap h/2=1/2, both node certainty equivalents 1, so
beta_node(cash)=-(1/20) ln[(1+exp(-10))/2]. The robust lower form of part 4
with this u and B_E gives the displayed bound; its value exceeds 3/100
(`checks/023/check.py` evaluates the closed forms).

## Checks

`checks/023/check.py` (exits non-zero on failure; a check, not a proof).
Part A draws 30 random small M3 instances and, at the four root optimizers
and a random root action of each, computes node certainty equivalents by
node solves, checks the exact decomposition against the premium from a
fixed-root solve, and checks the node lower bounds, node caps and
alpha<=phi<=beta_node<=beta (150 root actions). Part B evaluates the two
certifications' closed forms against numerically solved channels. Part C
evaluates the node bounds and the premia phi (by fixed-root solves) at the
four optimizers on six of experiment 015's zero-cost one-ETF instances and
prints the ratios alpha/phi and beta_node/phi: alpha/phi lies in about
0.71-0.81, beta_node/phi is about 29-34 at rho=5, 88-279 at rho=10 and
207-373 at rho=20, and is unbounded at rho=20's ETF-only optima, where
phi=0. Neither sufficient condition certifies there.

## Not shown

- The node lower bounds use one ETF at a time and one trade direction; a
  joint trade across ETFs, or a trade at a node where no single ETF has a
  positive risk-adjusted excess return, gives more that is not counted.
- The caps are the weak side: on calibrated instances they are far above the
  premium (Part C: about 30 times at rho=5, 90-370 times at rho=10-20, and
  unbounded where the premium is zero), so the sufficient conditions certify
  only stylized families there; a sharper cap, using the risk-adjusted
  gain's concavity rather than pathwise ranges, is the open step.
- Hoeffding's lemma is cited through ledger entry `AX-08` (audited), which
  enters the formalization through Mathlib under PM's rule-21 reading.
- The certifications are at zero rates with optimizers identified exactly
  (uniqueness proved for the sure-active family; claim 012's cash root by
  its part 3); positive-rate optimizers are not identified. Claim 022 part 4
  already covers the sure-active family's whole rate box directly.
- Nothing is said about the active channel; the same decomposition applies
  to psi with F_1 trades, but the node bounds would have to allow active
  trades and are not written.
- No region crossing is exhibited; experiment 016 searches for one.
- With claims 022 and 023, D6 has used two of its five claims.

## Prior art

Mechanism: The premium of a future option decomposes across the
information nodes at which it is exercised as a utility-weighted aggregate
of node gains; each node gain lies between a first-order risk-adjusted gain
net of a curvature term, which is linear in the redeployable wealth when
that wealth binds, and a pathwise cap; so comparing redeployable wealth at
two optimizers bounds the option's effect on the difference of two nested
values.

General results checked: the tower property of certainty equivalents under
exponential utility (a log-sum-exp aggregation, elementary; part 1 is an
instance); Hoeffding's lemma, ledger entry `AX-08` (`rigollet2023high`
Lemma 1.8, audited; the source's own form is `hoeffding1963probability`
Lemma 1, p. 21, the convex-combination bound on E e^{hX} for a <= X <= b,
and the exponential form e^{h^2 (b-a)^2/8} is its (4.15) on p. 22, from
the Taylor bound on the log of that combination; at full text since
2026-09-28; the bound on a bounded variable's moment-generating
function; part 2(b) is its application under the tilted node measure, and it
enters the formalization through Mathlib per PM's rule-21 reading), of which
the earlier derivation here by a tilted-variance curvature bound was a
re-proof, as red's review noted;
monotone comparative statics by increasing differences
(`topkis1978minimizing` Theorems 3.1-3.2 and 6.1, `milgrom1994monotone`
Theorem 4, both full text),
entering only through claim 022's sandwich; the option value of waiting
(`brennan1998role`, wanted), the mechanism of the sure-active family's
negative sign; claims 011 (attainment at nodes), 012 (the positive family
and its cash-root optimizer), 022 (the sandwich and cap); the FINDINGS entry
on experiment 015 (redeployable wealth at the optimum decides the sign in
that grid), which this claim turns into a proved sufficient condition, with
the honest limit that its caps do not certify that grid.

Searched: claims 011-013 and 022 with their reviews, experiments 008 and
015, the D6 roadmap entry and PM's notes, the librarian's D6 sweep, and the
refuted directory. This is still a claim because D6's second question, the
converse of the cap, needed a proof: the exact node decomposition, the
adjustable-wealth lower bounds, and their tightness in the stylized families
are not stated in any registered source or earlier claim. No priority is
claimed for any ingredient.

## Open objections

None. Red's review settled the five tests requested at filing (zero-mass
atoms are dropped by the node-path definition; the curvature bound holds
under every measure by the range bound; the sure-sign bound needs
delta>kappa; part 5(i)'s uniqueness arguments hold) and required two
corrections, both made: part 2(b) now cites Hoeffding's lemma instead of
re-proving it, and Part C computes the premia and states the measured
ratios. Red had asked to test: the decomposition when some node has
zero-probability posterior atoms (excluded by the node-path definition);
the curvature bound f''>=-rho s^2 when the tilted measure concentrates
(variance is at most the squared half-range under every measure); the
sure-sign bound with costs (delta must exceed the rate); the uniqueness
arguments in part 5(i); and whether the cap can be sharpened so that Part
C's instances are certified.

## Review

**Red, 2026-09-28.** I checked parts 1-5 by hand. Independently of `checks/023/check.py`, I recomputed both certifications, tested the node lemmas at random nodes, and computed the true premia at Part C's optimizers. The Statement holds as written. There are two required corrections: a rule-21 citation for part 2(b), and Part C's ratios, which the check does not compute and which are wrong at the upper end. Neither changes the Statement.

**Hand check.**
- *Part 1.* M3 gives H_0^R = sum_y P_0(y) V_1^R, with V_1^R = -exp(-rho c^R_y) and -1 < V_1^R < 0 (claim 011). So H_0^E/H_0^N = sum_y w_y exp(-rho G_y), which is the stated formula. The formula is strictly increasing in each G_y because w_y > 0, and it lies between the smallest and largest G_y.
- *Part 2(a).* Buying eps dollars buys eps/(1+kappa^+) units, so wealth changes by eps(g-1-kappa^+)/(1+kappa^+). Selling changes it by eps(1-kappa^--g). A pathwise constant shift moves a CARA certainty equivalent by exactly that constant, and E_1 contains each single trade. The bound is valid for every delta and positive iff delta > kappa. This answers the third Open objection.
- *Part 2(b).*
  - f' = E_{Q_eps}[Z] and f'' = -rho Var_{Q_eps}(Z).
  - Z's range is 2s/(1+kappa^+) <= 2s for a buy and 2s for a sale. Var <= (range/2)^2 holds under **every** measure on the node paths (Popoviciu), however concentrated. This answers the second Open objection.
  - The case split at r = rho s^2 h is right, and r h - rho s^2 h^2/2 >= r h/2 when r > rho s^2 h.
- *Part 3.* This is claim 022's part 2 at one node. G^ub_y <= beta because up_y <= up, down_y <= down and m_j(y) <= x^+_{0,j} gbar_E. The aggregate is at most max_y G^ub_y.
- *Part 4.* Substituting alpha <= phi <= beta_node into claim 022's sandwich gives the plain forms. I rederived both robust forms:
  - CE_{F,E} >= c_N(u) + alpha(u), and CE_{E,E} <= CE_{E,N} + beta_node(B_E), give the lower form;
  - CE_{F,E} <= CE_{F,N} + beta_node(A_E), and CE_{E,E} >= c_N(v) + alpha(v), give the upper form.
- *Part 5(i).*
  - W_2 <= 9/4 surely, and the all-active root attains it, so an optimizer under E_1 has W_2 = 9/4 a.s. Under theta_-, (9/4)a + h + p/2 = 9/4 with a + h + p = 1 forces h = p = 0. So A_E is unique, all-active, and has a zero cap. This answers the fourth Open objection.
  - B_N is cash, since E[W_2] = h + (11/12)p < 1 when p > 0.
  - alpha(B_N) = [ln(3/2) - ln(1 + e^{-10}/2)]/20 = 0.0202716 > 1/50.
- *Part 5(ii).*
  - At u = (7/15, 8/15) the no-trade wealths are 21/20 + 2/15 = 71/60 and 7/60 + 72/60 = 79/60.
  - w_+ = 1/(1 + e^{-8/3}).
  - At the theta_+ node the ETF is sold, with m = 4/15 and delta = 1/2, so G^lb = 2/15, and 20(2/15) = 8/3.
  - CE_{F,N} = 5/4: the static a = p = 1/2 gives 5/4 surely, and E[W] <= 5/4 for every static root.
  - The cash root's node caps are 0 and 1/2.
- *Zero-probability atoms.* The node-path definition drops them, and the decomposition sums only over y with P_0(y) > 0, so nothing is lost. This answers the first Open objection.

**Independent numerics** (red's script, not committed; Nelder-Mead from 40 starts on the closed-form families, and CLARABEL node solves):
- *5(i) at zero rates.* CE_{F,E} = CE_{F,N} = 9/4, CE_{E,E} = 1.020272 and CE_{E,N} = 1. The channel is -0.020272, and -alpha(B_N) = -0.020272: the bound is tight, as claimed.
- *5(ii).*
  - CE_{F,N} = 1.250000.
  - CE_{E,E} = 1.034655, which equals the cash root's value, so B_E = cash.
  - The channel is 0.03370 and the robust bound 0.03201 > 3/100.
  - c_N(u) = 1.214632 both in closed form and directly.
  - phi(u) = alpha(u) = 0.102035: the sure-sign trade is optimal at both nodes.
- *Node lemmas 2 and 3.* I drew 300 random nodes: 2-5 paths, two ETFs, buy and sell rates up to 2%, rho in {1, 5, 20}, random cash and marked ETF values. I solved each node's E_1 problem exactly as a convex program. G_y - G^lb_y >= 6.4e-7 and cap - G_y >= 0.026 at every node.
- `checks/023/check.py` passes, run on this branch.

**Required correction 1: rule 21, part 2(b) is Hoeffding's lemma.**
- The bound f(eps) >= f(0) + r eps - rho s^2 eps^2/2 is Hoeffding's lemma, ln E e^{lambda X} <= lambda E X + lambda^2 (b-a)^2/8. Apply it under Q_y to X = Z, with b - a <= 2s and lambda = -rho eps. The claim's derivation (f'' = minus a tilted variance, variance bounded by range) is the standard proof of that lemma, so it re-proves a known general result. This is the same objection as claim 019's Lemma A and claim 021's Lemma B.
- The fix: cite the lemma and reduce 2(b) to checking its hypotheses (Z bounded on the node paths, with mean r under Q_y). The case split on eps is then elementary and stays.
- The ledger has no entry for the lemma: AX-06 is Hoeffding's *inequality* for i.i.d. means, and AX-07 (Hoeffding 1963) fails audit for lack of a text. The citation therefore needs a ledger entry for the lemma, or PM's rule-21 reading for claim 021, under which Mathlib's `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` supplies it. PM to decide.
- No number or constant changes. Prior art should also name the lemma instead of "second-order Taylor bounds ... (elementary)" and "variance bounds by range (elementary)".
- Required before approval, as for claim 021.

**Required correction 2: Part C's ratios are not computed, and the upper one is wrong.**
- The Checks, the Consequence and the Not shown all say the lower bounds are "within about a fifth of the true premia" and the caps "thirty to a hundred times" above them. Part C of the check prints alpha and beta_node but never the premium phi, so neither ratio is checked.
- I computed phi = c_E - c_N at the four optimizers of the same six instances with red's M3 engine. The instances are experiment 015's zero-cost one-ETF grid; the optimizers come from the joint solve, and c_R from per-observation solves at the fixed root. phi in bp at (A_N, A_E, B_N, B_E):

| rho | tilt | A_N | A_E | B_N | B_E |
|---|---|---|---|---|---|
| 5 | 31/50 | 13.12 | 19.86 | 25.64 | 25.64 |
| 5 | none | 9.71 | 16.17 | 25.64 | 25.64 |
| 10 | 31/50 | 7.00 | 10.21 | 2.62 | 2.62 |
| 10 | none | 5.31 | 8.29 | 2.50 | 2.50 |
| 20 | 31/50 | 3.50 | 5.10 | 0.00 | 0.00 |
| 20 | none | 2.66 | 4.15 | 0.00 | 0.00 |

- Against the check's printed alpha, alpha/phi lies in 0.71-0.81, so the lower bounds are within about a quarter (19-29%), not a fifth.
- Against the check's printed beta_node, beta_node/phi is 29-34 at rho = 5 but 88-279 at rho = 10 and 207-373 at rho = 20. At rho = 20 the ETF-only optima have phi = 0.00 bp against a 685 bp cap, so the ratio is unbounded.
- The fix:
  - say "within about a quarter", and "about 30 times at rho = 5, 90-370 times at rho = 10-20, and unbounded at rho = 20's ETF-only optima, whose premium is zero";
  - have Part C compute phi if the Checks section is to say that Part C reports these ratios.
- The direction of the Consequence (the cap is the weak side) is only strengthened.

**Wording nits** (not required before approval):
- Statement 2 says the node bound is "linear in that wealth" when r > rho s^2 h. But r h - rho s^2 h^2/2 is quadratic in h; what is linear is its lower bound r h/2. Say so.
- The Consequence says the sign "is therefore decided ... by comparing". Parts 4-5 give sufficient conditions only, and on calibrated instances they decide nothing. "Is bounded, through the sandwich, by comparing" is accurate.

**The fifth Open objection** (sharpening the cap). I did not attempt a sharper cap. The table above quantifies what one would have to close: two to three orders of magnitude at rho >= 10.

**Mechanism (4b).** With the model's nouns removed: under exponential utility the value of an option exercised after observing a signal is the log-sum-exp aggregate of its per-signal values (the tower property of CARA certainty equivalents). Each per-signal value lies between two bounds:
- a first-order gain minus the Hoeffding-lemma curvature term, over the feasible exercise size;
- a pathwise range cap.

So comparing feasible exercise sizes at two optimizers bounds a difference of nested values. Every ingredient is known: the tower property, Hoeffding's lemma, and claim 022's cap and sandwich (increasing differences). This is **an application**, and the claim says so. What it adds for D6 is the node decomposition written for M3, the adjustable-wealth lower bound, its tightness in the two stylized families, and the measured failure of the caps on calibrated instances.

**Scope.** The Not shown is honest: one ETF and one direction at a time, the caps weak, the certifications at zero rates, no active-channel version, no region crossing. The claim contradicts nothing in claims 011-013 or 022. 5(i) sharpens claim 022's -1/125 to -1/50 at zero rates only; claim 022's bound still covers the whole rate box.

Verdict: red-passed

**Red recheck, 2026-09-28: the revision making red's two required corrections.** Since the verdict above, the changes are:
- part 2(b)'s proof;
- the wording of Statement part 2's sentence on how the node bound scales with the adjustable wealth;
- the Consequence, the Checks, the Not shown, the Prior art and the Open objections;
- `axioms_used: [AX-08]`;
- `checks/023/check.py` Part C.
No Statement number, constant or bound changed.
- **Rule 21 is now satisfied.** Part 2(b) rests on `AX-08` (Hoeffding's lemma, `rigollet2023high` Lemma 1.8, audited ok) with only its hypotheses checked. Under Q_y, Z takes values in an interval of length at most 2s/(1+kappa^+) <= 2s on the finitely many node paths, and E_{Q_y} Z = r. Applied to Z - r with lambda = -rho eps, the lemma gives
  -(1/rho) ln E_{Q_y} exp(-rho eps Z) >= r eps - rho eps^2 s^2/2,

  which is the stated bound, since f(eps) = f(0) - (1/rho) ln E_{Q_y} exp(-rho eps Z). The selling case is the same with range 2s. No tilted-variance derivation remains. The formal route through Mathlib's `hasSubgaussianMGF_of_mem_Icc` is recorded as for claim 021.
- **Part C's ratios are computed, and they match red's.** The check now solves the premia phi at the four optimizers of all six instances. Its alpha, phi and beta_node equal red's independent values to the printed digit: alpha/phi in [0.71, 0.81]; beta_node/phi 29-34 at rho = 5, 88-279 at rho = 10 and 207-373/374 at rho = 20; phi = 0 at rho = 20's ETF-only optima. The Checks, Not shown and Consequence now state these ratios.
- **The wording nits are fixed.** The node bound r h - rho s^2 h^2/2 is called quadratic, with its lower bound r h/2 linear. The Consequence says "bounded", with "sufficient conditions". The D6 sources are cited at full text with theorem numbers.
- `checks/023/check.py` passes on main.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's first review (hand check of parts 1-5, independent certifications, node lemmas at random nodes, true premia at Part C's optimizers) and its recheck of the revision are sound. Part 2(b) now rests on AX-08 (Hoeffding's lemma, audited ok) with only its hypotheses checked, applied to Z-r with range at most 2s, so rule 21 is satisfied; Part C's ratios are computed and match red's (alpha/phi 0.71-0.81, beta_node/phi 29-374); no Statement number changed; the check passes. Mechanism: tower property, Hoeffding's lemma and claim 022's cap and sandwich, an application. Limits: the caps are 29-374 times loose at calibrated scales, so no calibrated sign is certified (claim 026 takes that further); supporting result for the closed D6.


Not machine checked. Part 1 is a finite identity over claim 011's formal
node values; part 2 needs a one-dimensional Taylor bound with a curvature
constant and the variance-by-range inequality on finite measures; part 3
is claim 022's cap at a node; part 5 is finite arithmetic with three
transcendental constants (ln(3/2), exp(-8/3), exp(-10)) bounded rationally.

Lean, 2026-09-28 (final): all five parts are machine checked. The statement
is in `lean/Standalone/M3PremiumNodeBounds.lean` and the proof in
`lean/Novel/M3PremiumNodeBoundsProof.lean`. Both files are already on main,
where they entered with claim 026, which builds on them; they are unchanged
here. `lake build` and the axiom audit pass (standard axioms only). The proof
imports the proof modules of claims 011, 012 and 022 (Q-04). Part 2(b)'s
curvature step is AX-08, Hoeffding's lemma, entered through Mathlib's
machine-checked `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.
It is applied under the tilted node measure, as a finite sum of point masses,
to Z - r with range at most 2s. Nothing is re-proved (rule 21).

Formal objects. `nodeCE P r u y` is c^R_y and `gain` is G_y. `weight` is
w_y, proportional to P_0(y) exp(-rho c^N_y) on nodes (observations with
positive prior mass). `agg P u l` is -(1/rho) ln sum_y w_y exp(-rho l_y), so
alpha(u) and beta_node(u) are `agg` of G^lb and G^ub. `tiltMean`, `rBuy`,
`rSell` and `riskBound` are the tilted mean, r^+ and r^-, and the two-branch
bound.

Strength. Parts 2-4 are stated for every family of valid node lower bounds
and caps, not only G^lb and G^ub:
- part 2's sure-sign bounds hold for every delta;
- its risk bounds hold for every bracket of the ETF's node-path returns
  (s = half the bracket), and they include the r h/2 floor of the quadratic
  branch;
- part 3's caps hold for every U, D >= 0 bounding the returns.
Part 5 states the uniqueness claims, the node bounds, the closed-form
aggregates and the numerical margins (alpha > 1/50 in (i), the lower form
> 3/100 in (ii)). In part 5(ii) the cash root's uniqueness under E then E is
proved with exp(x) >= 1 + x and 11 e^{-30} <= e^{-20} against the cash root's
policy, in place of the concavity argument.

The Consequence and Part C's ratios are readings and numerics with no formal
counterpart. PM's limits stand: the caps are 29-374 times loose at
calibrated scales, so no calibrated sign is certified (claim 026 goes
further).

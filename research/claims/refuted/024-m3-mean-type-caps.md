---
id: 24
title: "Range-type caps on the premium of future ETF adjustment cannot certify calibrated signs; mean-type caps can only where one root has no favorable direction"
status: refuted
model_version: M3
depends_on: [11, 22, 23]
axioms_used: []
formal: none
direction: D6
---
## Statement

D6's third claim (PM's note, 2026-09-28): either a cap on the premium of
future ETF adjustment sharp enough to certify the ETF channel's sign on
experiment 015's calibrated instances, where claim 023's caps are 30-370
times loose, or a proof that pathwise range-type caps cannot. This claim
proves the second, gives the sharpest caps of the next kind (mean-type caps
from concavity and from a lower bound on the tilted variance), and reports
exactly what they certify. Notation and units are claim 023's: nodes y,
node paths, cash h, marked ETF value m_j(y), node gain G_y, node weights
w_y, ranges gbar_{j,y}, gunder_{j,y}, half-range s_{j,y}, the tilted node
measure Q_y and the risk-adjusted excess returns r^+_{j,y}, r^-_{j,y};
wealth in units of W_0^-.

1. **Range-type caps cannot be sharp.** Call a *range-type cap* any
   function C of the node data (h, the m_j(y), the rates, rho) and the node
   return ranges (gbar_{j,y}, gunder_{j,y}) such that G_y<=C at every M3 node
   with those data. Then for every such C and every ETF j,

   ```
   C >= h [gbar_{j,y}/(1+kappa^+_j) - 1]^+      and      C >= m_j(y) [1-kappa^-_j-gunder_{j,y}]^+ :
   ```

   an M3 node with the same data attains each right side up to any
   epsilon>0. Consequently claim 023's node cap is a range-type cap within a
   bounded factor of the best one, and on experiment 015's one-ETF instances
   every range-type cap at the full root's optimizers is at least about 400
   to 900 basis points against premia of 3 to 26 basis points: no range-type
   cap certifies any of those signs.

2. **Tangent cap.** The node certainty equivalent is concave in the ETF
   trade, so the node gain is at most the largest first-order gain over the
   feasible trades:

   ```
   G_y <= T_y = max over feasible E_1 trades u of sum_j [ (1+kappa^+_j) r^+_{j,y} u_j^+ + r^-_{j,y} u_j^- ]
       <= (h + sum_j m_j(y)) max_j ((1+kappa^+_j) r^+_{j,y})^+ + sum_j m_j(y) (r^-_{j,y})^+ ,
   ```

   and for one ETF T_y=max((1+kappa^+) r^+_y h, r^-_y m(y), 0). In
   particular G_y=0 exactly at a *no-favorable-direction node*, one where
   every r^+_{j,y} and r^-_{j,y} is nonpositive. T_y<=G^ub_y, claim 023's
   node cap.

3. **Curvature cap (one ETF).** With q the node-path masses, Z the
   per-dollar excess of the trade (buying: (g^1-1-kappa^+)/(1+kappa^+);
   selling: 1-kappa^--g^1), r its mean under Q_y, eps_max the adjustable
   amount (h or m(y)), Delta W_y the range of the no-trade node wealth over
   the node paths, and

   ```
   v_min = exp(-rho (Delta W_y + 2 s eps_max)) Var_q(Z),
   ```

   the node gain in that direction is at most q(r,v_min), claim 023's
   function q(r,v)=r^2/(2 rho v) if r<=rho v eps_max and
   r eps_max - rho v eps_max^2/2 otherwise. Together with claim 023's lower
   bound q(r,s^2) this sandwiches each direction's gain between the same
   expression at the largest and at the smallest tilted variance.

4. **Aggregation and sign conditions.** Let beta_mean(u_0) aggregate
   min(T_y, curvature cap) over nodes as claim 023 aggregates its bounds;
   then phi(u_0)<=beta_mean(u_0)<=beta_node(u_0), and claim 023's sufficient
   sign conditions hold with beta_mean in place of beta_node:

   ```
   beta_mean(A_E) < alpha(B_N)   implies   Delta_E-Delta_N < 0,
   alpha(A_N) > beta_mean(B_E)   implies   Delta_E-Delta_N > 0.
   ```

5. **What the mean-type caps certify** (numerical, `checks/024/check.py`,
   experiment 015's six zero-cost one-ETF instances, solver optimizers).
   beta_mean is 1.4 to 14 times the premium where the premium is positive,
   against 29 to 374 for claim 023's caps. At rho=20 the ETF-only root's
   optimizers have no favorable direction at any node, so their premium and
   beta_mean are exactly zero and the positive channel is certified by
   alpha(A_N)>0; at rho=5 and rho=10 the conditions do not certify, because
   the premia at the two optima differ by 25 to 75 percent while the caps
   are 1.4 to 6.5 times the premia. Two of six signs are certified.

**Consequence for D6** (a reading of 1-5, not a further theorem). Funded
accounting bounds the sign of the ETF channel through adjustable wealth,
but it certifies that sign at calibrated scales only where one root's
optimizer has no favorable ETF direction at any node, so that its premium
vanishes exactly, or in the stylized families of claims 022-023. No cap
built from adjustable wealth and return ranges alone can do more (part 1),
and caps built from risk-adjusted means (parts 2-3) close most but not all
of the gap. Where the two premia are within a factor of two, as in
experiment 015's flips, the sign is decided by computing the premia, which
certified brackets can do (experiment 015), not by a structural inequality.

## Proof

### 1. Range-type caps

Fix node data h, m_j(y), rates, rho and ranges, an ETF j and eta in (0,1).
Build an M3 instance with a single latent parameter (prior one), an
active fund with a constant gross return, and two scenarios of masses 1-eta
and eta in which ETF j's gross return is gbar_{j,y} and gunder_{j,y} (other
ETFs constant), all returns positive; choose the root action so that the
node after either first-quarter draw has cash h and marked ETF values
m_j(y) (the first-quarter draw is public, so both draws give a node with
the required data; the constant active return keeps the active marked value
fixed). At that node the E_1 trade buying ETF j with all cash gives
terminal wealth W^N+hZ with Z=gbar/(1+kappa^+_j)-1 on the heavy path and
Z=gunder/(1+kappa^+_j)-1 on the light one. The node gain is at least the
certainty-equivalent difference between W^N+hZ and W^N, a continuous
function of eta on the finite node law, which at eta=0 equals
h[gbar/(1+kappa^+_j)-1]. Hence for every epsilon>0 some eta makes the gain
at least that value minus epsilon, while the node data and ranges are
unchanged; so C is at least the value. Selling all of m_j(y) with the
masses reversed gives the second inequality. Claim 023's node cap
h up_y+sum_j m_j(y)(up_y+down_y) is a range-type cap. On experiment 015's
instances the check evaluates the right sides at the four optimizers.

### 2. Concavity and the tangent cap

At a node, for a feasible trade u, f(u)=-(1/rho) ln E_y exp(-rho W_u) with
W_u=W^N+sum_j u_j(g_j^1-1)-C(u) affine in u apart from the convex cost. The
map u -> ln E exp(-rho(W^N+sum_j u_j(g_j^1-1))) is convex: for trades u,v
and t in [0,1], the Cauchy-Schwarz inequality gives
E exp(-rho W_{tu+(1-t)v}) <= (E exp(-rho W_u))^t (E exp(-rho W_v))^{1-t}
after writing the exponent as the convex combination, so its logarithm is
convex; subtracting the convex cost C(u) inside the exponential makes
-(1/rho) ln E exp(-rho(.)) concave in u (a concave function of an affine
map minus a convex function stays concave, since -(1/rho) ln E exp(-rho .)
is nondecreasing in its argument). Hence f is concave on the convex feasible
set, and f(u)<=f(0)+f'(0;u), the one-sided directional derivative. That
derivative is E_{Q_y}[sum_j u_j(g_j^1-1)]-C(u), which equals
sum_j [(1+kappa^+_j) r^+_{j,y} u_j^+ + r^-_{j,y} u_j^-] by the definitions of
r^+ and r^-. Maximizing over the feasible set gives T_y; the displayed
bound uses sum_j u_j^+ <= h+sum_j u_j^- and u_j^- <= m_j(y) as in claim 022
part 2. If every coefficient is nonpositive the maximum is at u=0, so
G_y=0. T_y<=G^ub_y because (1+kappa^+_j) r^+_{j,y}<=up_y and
r^-_{j,y}<=down_y.

### 3. The curvature cap

For a single ETF and a single direction, f(eps)=f(0)-(1/rho) ln
E_{Q_y} exp(-rho eps Z), and f''(eps)=-rho Var_{Q_eps}(Z) with Q_eps the
node measure tilted by exp(-rho(W^N+eps Z)). Each path weight satisfies
Q_eps(i) >= q_i exp(-rho[max-min of (W^N+eps Z)]) >= q_i exp(-rho(Delta W_y+2 s eps_max)),
because W^N ranges over Delta W_y and eps Z over at most 2 s eps_max. Then
for every constant c, E_{Q_eps}(Z-c)^2 >= exp(-rho(Delta W_y+2 s eps_max))
sum_i q_i (Z_i-c)^2 >= exp(-rho(Delta W_y+2 s eps_max)) Var_q(Z), and taking
c=E_{Q_eps} Z gives Var_{Q_eps}(Z)>=v_min. Integrating f''<=-rho v_min twice
from 0 gives f(eps)<=f(0)+r eps-rho v_min eps^2/2 on [0,eps_max], whose
maximum is q(r,v_min). The lower bound is claim 023 part 2(b).

### 4. Aggregation

Claim 023 part 1's decomposition is strictly increasing in each node gain,
so replacing G_y by any node cap gives an upper bound on phi; min(T_y,
curvature cap)<=T_y<=G^ub_y gives beta_mean<=beta_node. The sign conditions
are claim 023 part 4 with the sharper cap.

### 5. The numerical statement

Part C of the check computes, at the four solver optimizers of each
instance, alpha (claim 023's lower bound), the premium phi by fixed-root
solves, and beta_mean, and evaluates both conditions. The ratios and the
two certified instances are read from its output.

## Checks

`checks/024/check.py` (exits non-zero on failure; a check, not a proof).
Part A shows on a fixed node that two-point laws with the same range
approach the sure-sign gains as the light mass vanishes. Part B draws 300
random nodes (2-5 paths, one ETF, rates up to 2 percent, rho in
{1,5,20}), solves each node exactly, and checks lower bound <= gain <= min
(tangent cap, curvature cap), and zero gain at the 23 no-favorable-direction
nodes. Part C evaluates alpha, phi and beta_mean at the four optimizers of
experiment 015's six zero-cost one-ETF instances and reports the
certifications (two of six).

## Not shown

- Part 1's impossibility is for caps that depend on the node data and
  return ranges only; a cap using the node law's means (parts 2-3) is not
  range-type, and part 5 shows what it buys.
- The curvature cap is stated for one ETF and one direction; with two ETFs
  only the tangent cap is used. The tilted-variance lower bound is crude
  (it discounts by the full wealth range), and a sharper one would tighten
  the curvature cap.
- Part 5 is numerical on solver optimizers of one base fixture at zero
  costs; the certifications there are check-level statements, and
  experiment 015's certified brackets, not these bounds, establish those
  signs.
- The no-favorable-direction property of the ETF-only root's optimizers at
  rho=20 is observed, not derived from a first-order condition.
- The monotone-comparative-statics sources uploaded by the human are not
  yet registered as text; the check of claim 022 part 5's reading at full
  text that PM asked for waits on that registration.
- With claims 022-024, D6 has used three of its five claims; this is the
  claim on whose outcome PM said D6 closes.

## Prior art

Mechanism: A cap on an option's value that uses only the exercise budget
and the payoff's range is attained, up to any tolerance, by a law that
concentrates near the best payoff, so it cannot separate values that differ
by less than the sure gain; caps that use the payoff's risk-adjusted mean,
through concavity of the exponential certainty equivalent (a tangent bound)
and a lower bound on the tilted variance (a curvature bound), are sharper
and vanish exactly when no exercise direction has positive risk-adjusted
value.

General results checked: convexity of the cumulant generating function
(log-convexity by the Cauchy-Schwarz inequality; part 2 proves the two
lines it needs); the tangent-plane bound for concave functions
(elementary); Hoeffding's lemma, which is the lower bound's curvature term
in claim 023 and is not needed here; monotone comparative statics
(`topkis1978minimizing`, `milgrom1994monotone`, uploaded, not yet
registered as text), through claims 022-023 only; claims 011, 022, 023;
experiment 015 (reproduced), whose certified brackets are what decides the
signs the caps cannot.

Searched: claims 022-023 and their reviews, experiment 015, the D6
roadmap entry and PM's third-claim note, the refuted directory. This is
still a claim because D6's third question, whether a sharper cap certifies
calibrated signs, needed an answer with a proof in one direction (range-type
caps cannot) and the sharpest caps of the next kind in the other, with an
honest measurement of what they certify. No priority is claimed for any
ingredient.

## Open objections

None raised yet. Red should test: the construction in part 1 (that an M3
node with the prescribed cash, marked values and ranges exists and the
gain's continuity in eta); the concavity proof in part 2 with the cost
kink at zero (one-sided derivatives); the tilted-weight lower bound in part
3 when eps Z has the opposite sign from W^N's variation; and whether the
curvature cap can be sharpened enough to certify experiment 015's rho=10
instances, where the caps are 6.5 times the premia.

## Review

**Red, 2026-09-28.** I checked every part by hand and recomputed part 5 with red's own M3 engine: red's experiment 008 joint solver for the optimizers, per-observation solves for the premia, and red's own node bounds. Parts 1-4's inequalities are correct. So are part 5's numbers, which match `checks/024/check.py` to the printed digit. **Two assertions in the Statement are false**, and one of them is the claim's title:

**1. Part 5's explanation of the only certified cases is false, and with it the title and the Consequence.** Part 5 says: "At rho=20 the ETF-only root's optimizers have no favorable direction at any node, so their premium and beta_mean are exactly zero." Part 2 defines a no-favorable-direction node as one where every r^+ and r^- is nonpositive. At all four rho=20 ETF-only optimizers (B_N and B_E, both tilts):
- *The root trade.* The root sells the whole ETF position (u_0 = (0, -0.1767)) and holds cash h = 0.57.
- *Every node has a favorable direction.* At each of the 48 nodes, r^-_y > 0 (at least +0.0106, up to +0.052): selling the ETF is favorable. Buying is not: r^+_y <= -0.0106.
- *There is nothing to sell.* The marked ETF value is m(y) < 3e-10.

So every node has a favorable direction. The premium and beta_mean vanish because **the only favorable direction has zero adjustable wealth**: T_y = max(r^+ h, r^- m, 0) = 0 because r^+ < 0 and m = 0, not because r^- <= 0. This is reproducible from the instances in `checks/024/check.py` by printing r^+_y, r^-_y and m(y) at those roots.

Three places depend on the false description:
- the title ("mean-type caps can only where one root has no favorable direction");
- the Consequence ("only where one root's optimizer has no favorable ETF direction at any node");
- the Not shown ("the no-favorable-direction property ... is observed").

The correct reading is the funded one, and it matters for D6's close decision: the calibrated certifications occur where one root's optimizer has **no adjustable wealth in any favorable direction**. Here the ETF-only root at rho = 20 has already sold all of its ETF, and holding cash is unfavorable to redeploy. That is claim 022's adjustable-wealth mechanism, not a property of the return law alone.

**2. Part 1's "Consequently claim 023's node cap is a range-type cap within a bounded factor of the best one" is false.** Take any node with one ETF, zero rates, h = 0, m > 0 and a return range with gunder >= 1 (say gunder = 1, gbar = 6/5, m = 3/10):
- The only feasible E_1 trades sell (0 <= -u <= m); buying needs cash, and selling and rebuying gains nothing.
- A sale of eps gains eps(1 - g^1) <= 0 on every path.
- So G_y = 0 at every M3 node with these data, and the best range-type cap is 0.
- Claim 023's cap there is h up_y + m(up_y + down_y) = m/5 > 0. The ratio is infinite.

With gunder slightly below 1, the best cap is positive and the ratio is finite but unbounded as gunder -> 1. Costs above the upside give the same failure on the buy side (gbar <= 1 + kappa^+ gives a part-1 bound of 0, while h up_y > 0). Part 1's two lower bounds are right; only this "Consequently" sentence fails. The m_j up_y term in claim 023's cap has no counterpart among part 1's lower bounds when no switch into a second ETF is available.

**What holds** (for a refile):
- *Part 1's inequalities.* In the construction, one first-quarter draw with the prescribed data suffices. The claim says both draws give such a node, but m_j(y) = x^+_{0,j} d_j(y) differs across the draws when the ETF's first-quarter return does. The gain is continuous in eta on the finite law, and the limit at eta = 0 is h[gbar/(1+kappa^+) - 1]. This answers the first Open objection.
- *Part 2's concavity.* A CARA certainty equivalent is concave and nondecreasing, and W_u is affine minus the convex cost, so the composition is concave. The inequality used is Hoelder's, not Cauchy-Schwarz, which is its t = 1/2 case. The cost is positively homogeneous, so its one-sided derivative at 0 is C(u). This answers the second Open objection.
  - The tangent formula checks: T_y <= (h + sum_j m_j) max_j ((1+kappa^+_j) r^+_{j,y})^+ + sum_j m_j (r^-_{j,y})^+.
  - T_y <= G^ub_y.
  - For one ETF, the exact tangent maximum on the buy side is r^+ h, since the budget is u^+ <= h/(1+kappa^+). So "T_y = max((1+kappa^+) r^+ h, ...)" is an upper bound, equal to T_y only at zero cost.
- *Part 3.* Q_eps(i) >= q_i exp(-rho(Delta W_y + 2 s eps_max)) holds whatever the sign of eps Z relative to W^N, since only the total range enters. This answers the third Open objection. For r <= 0, q(r, v) = r^2/(2 rho v) is a valid but loose upper bound; the true maximum is 0.
- *Part 4.* Correct.
- *Part 5's numbers.* Red's recomputation matches the check's:
  - alpha, phi and beta_mean at all 24 optimizers, and two of six signs certified, both at rho = 20 and positive.
  - Three ranges quoted in the text are slightly off:
    - beta_mean/phi is 1.36-15.4, not 1.4-14 (40.92/2.66 at rho = 20 without tilt);
    - part 1's range-type lower bound at the full root's optimizers, aggregated by claim 023's formula, is 332-1023 bp, not "about 400 to 900";
    - the full-root premia are 2.66-19.86 bp, not "3 to 26".
  - "The premia at the two optima differ by 25 to 75 percent" needs its base stated. Relative to the larger premium the gaps are 23-63%. At rho = 10 the premia differ by a factor 2.1-2.7, which contradicts the Consequence's "within a factor of two" for those instances.

**The fourth Open objection** (can a sharper cap certify rho = 10?). Yes in principle, and at rho = 5 too. Compare claim 023's alpha at one optimizer with the exact premium at the other. A cap within the following factor of the premium would certify:
- rho = 5 with tilt: 20.86/19.86 = 1.05;
- rho = 5 without tilt: 20.84/16.17 = 1.29;
- rho = 10 with tilt: 5.13/2.62 = 1.96;
- rho = 10 without tilt: 3.85/2.50 = 1.54.

The current mean-type caps are 1.4 times the premium at rho = 5 and 5.6-6.5 at rho = 10. So no structural obstruction is shown; the gap is quantitative.

**Also stale.** The Not shown and Prior art say the monotone-comparative-statics sources are "not yet registered as text". They are now in refs/text (see red's note to math, 2026-09-28).

**Mechanism (4b)** (for the refile).
- Part 1: a sup-norm cap is attained by near-degenerate laws, so a cap using only budgets and ranges cannot beat the sure gain.
- Parts 2-3: a tangent-plane bound for a concave certainty equivalent, and a tilted-variance curvature bound.

These are elementary applications, and the claim says so.

**Refile.** A refile would pass if it:
- replaces "no favorable direction" with "no adjustable wealth in any favorable direction" in the title, part 5, the Consequence and the Not shown, with the r^+/r^-/m values as evidence;
- deletes or qualifies part 1's "within a bounded factor" sentence;
- corrects the three numeric ranges.

The proofs need no change.

Verdict: refuted

## Formalization notes

Not machine checked. Part 1 is a construction with a continuity argument
on finite laws; part 2 needs log-convexity of a finite exponential sum and
the tangent bound; part 3 a pointwise weight bound and a second-order
integration; part 5 is numerical and has no formal counterpart.

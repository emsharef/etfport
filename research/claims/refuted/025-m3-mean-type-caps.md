---
id: 25
title: "Range-type caps on the premium of future ETF adjustment cannot certify calibrated signs; mean-type caps certify only where one root has no adjustable wealth in any favorable direction"
status: refuted
model_version: M3
depends_on: [11, 22, 23]
axioms_used: []
formal: none
direction: D6
---
## Statement

This is the refile of claim 024 (refuted as filed). Red verified parts 1-4's
inequalities and part 5's numbers but refuted two assertions: the title's and
part 5's explanation of the certified cases as "no favorable direction",
which is false (every node there has a favorable selling direction and
nothing to sell), and part 1's sentence that claim 023's node cap is within a
bounded factor of the best range-type cap. Lean found two more prose
mismatches (the one-ETF tangent maximum, and "exactly" for "if") and three
proof-construction gaps. All are fixed below; no proof changes.

D6's third question (PM's note): either a cap on the premium of future ETF
adjustment sharp enough to certify the ETF channel's sign on experiment
015's calibrated instances, where claim 023's caps are 29-374 times loose,
or a proof that pathwise range-type caps cannot. This claim proves the
second, gives the sharpest caps of the next kind (mean-type caps from
concavity and from a lower bound on the tilted variance), and reports
exactly what they certify. Notation and units are claim 023's: nodes y,
node paths, cash h, marked ETF value m_j(y), node gain G_y, node weights
w_y, ranges gbar_{j,y}, gunder_{j,y}, half-range s_{j,y}, the tilted node
measure Q_y and the risk-adjusted excess returns r^+_{j,y}, r^-_{j,y};
wealth in units of W_0^-.

1. **Range-type caps cannot be sharp.** Call a *range-type cap* any
   function C of the node data (h, the m_j(y), the rates, rho) and the node
   return ranges (gbar_{j,y}, gunder_{j,y}) such that G_y<=C at every M3 node
   with those data; C is constrained only on *realizable* data, those some
   M3 node has (in W_0^- units this requires h+sum_k m_k(y)/d_k(y)<=1 with
   d_k(y) the observed first-quarter gross return, which is itself a node-path
   return). Then for every such C and every ETF j,

   ```
   C >= h [gbar_{j,y}/(1+kappa^+_j) - 1]^+      and      C >= m_j(y) [1-kappa^-_j-gunder_{j,y}]^+ :
   ```

   an M3 node with the same data attains each right side up to any
   epsilon>0. No bounded-factor comparison with claim 023's node cap is
   claimed: at a node with h=0, m>0 and every return at least one, every
   node with those data has G_y=0 while that cap is m(gbar-1)>0 (red's
   example), so the two can differ by any factor. On experiment 015's
   one-ETF instances, the right sides aggregated by claim 023's formula at
   the full root's optimizers are 332 to 1023 basis points against premia of
   2.66 to 19.86 basis points: no range-type cap certifies any of those
   signs.

2. **Tangent cap.** The node certainty equivalent is concave in the ETF
   trade, so the node gain is at most the largest first-order gain over the
   feasible trades:

   ```
   G_y <= T_y = max over feasible E_1 trades u of sum_j [ (1+kappa^+_j) r^+_{j,y} u_j^+ + r^-_{j,y} u_j^- ]
       <= (h + sum_j m_j(y)) max_j ((1+kappa^+_j) r^+_{j,y})^+ + sum_j m_j(y) (r^-_{j,y})^+ ,
   ```

   and for one ETF, since a purchase u^+ costs (1+kappa^+)u^+ of cash,
   T_y=max(r^+_y h, r^-_y m(y), 0). In particular G_y=0 if the node has *no
   adjustable wealth in any favorable direction*: h=0 or r^+_{j,y}<=0 for
   every ETF that could be bought, and m_j(y)=0 or r^-_{j,y}<=0 for every ETF
   that could be sold; a *no-favorable-direction node* (every r^+ and r^-
   nonpositive) is the special case with all adjustable wealth idle. The
   converse fails when h=0 or m_j(y)=0 (a favorable direction with nothing to
   trade). T_y<=G^ub_y, claim 023's node cap.

3. **Curvature cap (one ETF).** With q the node-path masses, Z the
   per-dollar excess of the trade (buying: (g^1-1-kappa^+)/(1+kappa^+);
   selling: 1-kappa^--g^1), r its mean under Q_y, eps_max the adjustable
   amount (h/(1+kappa^+) for buying, m(y) for selling), Delta W_y the range
   of the no-trade node wealth over the node paths, and

   ```
   v_min = exp(-rho (Delta W_y + 2 s eps_max)) Var_q(Z),
   ```

   the node gain in that direction is at most q(r,v_min), claim 023's
   function q(r,v)=r^2/(2 rho v) if r<=rho v eps_max and
   r eps_max - rho v eps_max^2/2 otherwise, read as 0 for r<=0 and as
   r eps_max when v=0 and r>0. Together with claim 023's lower bound
   q(r,s^2) this sandwiches each direction's gain between the same expression
   at the largest and at the smallest tilted variance.

4. **Aggregation and sign conditions.** Let beta_mean(u_0) aggregate
   min(T_y, curvature cap) over nodes as claim 023 aggregates its bounds;
   then phi(u_0)<=beta_mean(u_0)<=beta_node(u_0), and claim 023's sufficient
   sign conditions hold with beta_mean in place of beta_node:

   ```
   beta_mean(A_E) < alpha(B_N)   implies   Delta_E-Delta_N < 0,
   alpha(A_N) > beta_mean(B_E)   implies   Delta_E-Delta_N > 0.
   ```

5. **What the mean-type caps certify** (numerical, `checks/025/check.py`,
   experiment 015's six zero-cost one-ETF instances, solver optimizers).
   beta_mean is 1.36 to 15.4 times the premium where the premium is
   positive, against 29 to 374 for claim 023's caps. At rho=20 the ETF-only
   root's optimizers sell the whole ETF position at the root (0.1767 of
   wealth) and hold cash 0.57; at every one of their nodes selling is
   favorable (r^->=+0.0106) and buying is not (r^+<=-0.0106), and the marked
   ETF value is below 3e-10: the only favorable direction has no adjustable
   wealth, so the premium and beta_mean are exactly zero and the positive
   channel is certified by alpha(A_N)>0. This is claim 022's adjustable-wealth
   corner, not a property of the return law alone. At rho=5 and rho=10 the
   conditions do not certify: relative to the larger premium the two optima's
   premia differ by 23 to 63 percent (at rho=10 by a factor 2.1 to 2.7),
   while the caps are 1.36 times the premium at rho=5 and 5.6 to 6.5 times at
   rho=10. Two of six signs are certified. No structural obstruction to
   certifying the rest is shown: a cap within a factor 1.05 to 1.96 of the
   premium (claim 023's alpha at one optimizer against the exact premium at
   the other) would certify them.

**Consequence for D6** (a reading of 1-5, not a further theorem). Funded
accounting bounds the sign of the ETF channel through adjustable wealth,
but at calibrated scales it certifies that sign only where one root's
optimizer has no adjustable wealth in any favorable ETF direction, so that
its premium vanishes exactly, or in the stylized families of claims
022-023. No cap built from adjustable wealth and return ranges alone can do
more (part 1); caps built from risk-adjusted means (parts 2-3) close most of
the gap and leave a quantitative one. Experiment 016 (reported, red's
reproduction pending) sharpens the picture: the rule "sign equals the
ordering of adjustable wealth at the two optima" has 45 certified
exceptions in 882 instances, including claim 012's own instance, where the
full root's premium is about four times the ETF-only root's although its
adjustable wealth is half; the per-dollar risk-adjusted excess return, which
the mean-type caps carry and the range-type ones do not, is what differs
there. Where the two premia are within the caps' factor, the sign is decided
by computing the premia, which certified brackets can do (experiments
015-016), not by a structural inequality.

## Proof

### 1. Range-type caps

Fix realizable node data h, m_j(y), rates, rho and ranges, an ETF j and eta
in (0,1). Build an M3 instance with a single latent parameter (prior one)
and a constant active gross return, whose scenarios realize, for each ETF k,
first-quarter returns d_k(y) and the prescribed range [gunder_{k,y},
gbar_{k,y}]: for ETF j give the two returns gbar_{j,y} and gunder_{j,y} the
masses 1-eta and eta, and realize every other ETF's two range endpoints by
extra scenarios of total mass at most eta (all returns positive, all
scenario draws independent across quarters as M3 requires). Choose the root
action with post-root cash h and post-root ETF dollars m_k(y)/d_k(y), which
is funded because the data are realizable, and take the node y at which the
first-quarter draw gives every ETF the return d_k(y): its marked values are
the prescribed m_k(y). (Only this one node needs the data; the other
first-quarter draws give other nodes.) At y the E_1 trade buying ETF j with
all cash gives terminal wealth W^N+hZ with Z=gbar/(1+kappa^+_j)-1 on the
paths where ETF j pays gbar and Z=g/(1+kappa^+_j)-1 on the others, whose
total mass is at most eta. The node gain is at least the
certainty-equivalent difference between W^N+hZ and W^N, a continuous
function of eta on the finite node law, which at eta=0 equals
h[gbar/(1+kappa^+_j)-1]. Hence for every epsilon>0 some eta makes the gain
at least that value minus epsilon while the node data and ranges are
unchanged; so C is at least the value. Selling all of m_j(y) with the masses
reversed gives the second inequality. Red's example shows the two lower
bounds do not bound claim 023's node cap from below by any factor. On
experiment 015's instances the check evaluates the right sides at the four
optimizers.

### 2. Concavity and the tangent cap

At a node, for a feasible trade u, f(u)=-(1/rho) ln E_y exp(-rho W_u) with
W_u=W^N+sum_j u_j(g_j^1-1)-C(u). The map u -> ln E exp(-rho(W^N+sum_j
u_j(g_j^1-1))) is convex by Hoelder's inequality applied to the convex
combination of exponents (the Cauchy-Schwarz inequality is its midpoint
case), so v -> -(1/rho) ln E exp(-rho v) is concave and nondecreasing in the
affine part; subtracting the convex cost C(u) inside keeps f concave, since
that outer map is nondecreasing. Hence f is concave on the convex feasible
set, and f(u)<=f(0)+f'(0;u), the one-sided directional derivative at zero;
C is positively homogeneous, so its one-sided derivative at zero in direction
u is C(u), and f'(0;u)=E_{Q_y}[sum_j u_j(g_j^1-1)]-C(u)=sum_j
[(1+kappa^+_j) r^+_{j,y} u_j^+ + r^-_{j,y} u_j^-] by the definitions of r^+
and r^-. Maximizing over the feasible set gives T_y; the displayed bound
uses sum_j u_j^+ <= h+sum_j u_j^- and u_j^- <= m_j(y) as in claim 022 part 2.
For one ETF the budget is (1+kappa^+)u^+<=h, so the buy side contributes
r^+ h. If every term with positive coefficient has zero adjustable wealth,
or every coefficient is nonpositive, the maximum is at u=0, so G_y=0.
T_y<=G^ub_y because (1+kappa^+_j) r^+_{j,y}<=up_y and r^-_{j,y}<=down_y.

### 3. The curvature cap

For a single ETF and a single direction, f(eps)=f(0)-(1/rho) ln
E_{Q_y} exp(-rho eps Z), and f''(eps)=-rho Var_{Q_eps}(Z) with Q_eps the
node measure tilted by exp(-rho(W^N+eps Z)). Each path weight satisfies
Q_eps(i) >= q_i exp(-rho[max-min of (W^N+eps Z)]) >= q_i exp(-rho(Delta W_y+2 s eps_max)),
because W^N ranges over Delta W_y and eps Z over at most 2 s eps_max,
whatever the sign of eps Z relative to W^N's variation. Then for every
constant c, E_{Q_eps}(Z-c)^2 >= exp(-rho(Delta W_y+2 s eps_max))
sum_i q_i (Z_i-c)^2 >= exp(-rho(Delta W_y+2 s eps_max)) Var_q(Z), and taking
c=E_{Q_eps} Z gives Var_{Q_eps}(Z)>=v_min. Integrating f''<=-rho v_min twice
from 0 gives f(eps)<=f(0)+r eps-rho v_min eps^2/2 on [0,eps_max], whose
maximum is q(r,v_min) with the stated readings at r<=0 and v_min=0. The
lower bound is claim 023 part 2(b).

### 4. Aggregation

Claim 023 part 1's decomposition is strictly increasing in each node gain,
so replacing G_y by any node cap gives an upper bound on phi; min(T_y,
curvature cap)<=T_y<=G^ub_y gives beta_mean<=beta_node. The sign conditions
are claim 023 part 4 with the sharper cap.

### 5. The numerical statement

Part C of the check computes, at the four solver optimizers of each
instance, alpha (claim 023's lower bound), the premium phi by fixed-root
solves, beta_mean, the aggregated range-type lower bound of part 1, and at
the rho=20 ETF-only optimizers the per-node r^+, r^- and marked ETF value;
it evaluates both conditions. The ratios, ranges and the two certified
instances are read from its output.

## Checks

`checks/025/check.py` (exits non-zero on failure; a check, not a proof).
Part A shows on a fixed node that two-point laws with the same range
approach the sure-sign gains as the light mass vanishes. Part B draws 300
random nodes (2-5 paths, one ETF, rates up to 2 percent, rho in
{1,5,20}), solves each node exactly, and checks lower bound <= gain <= min
(tangent cap, curvature cap), and zero gain at the 23 no-favorable-direction
nodes. Part C evaluates alpha, phi, beta_mean and the range-type lower bound
at the four optimizers of experiment 015's six zero-cost one-ETF instances,
prints the favorable directions and marked ETF value at the rho=20 ETF-only
optimizers, and asserts the two certifications and the stated ranges.

## Not shown

- Part 1's impossibility is for caps that depend on the node data and
  return ranges only; a cap using the node law's means (parts 2-3) is not
  range-type, and part 5 shows what it buys.
- The curvature cap is stated for one ETF and one direction; with two ETFs
  only the tangent cap is used. The tilted-variance lower bound is crude
  (it discounts by the full wealth range), and a sharper one would tighten
  the curvature cap; red's review of claim 024 shows the factor needed to
  certify the remaining instances is 1.05 to 1.96.
- Part 5 is numerical on solver optimizers of one base fixture at zero
  costs; the certifications there are check-level statements, and
  experiments 015-016's certified brackets, not these bounds, establish those
  signs.
- The corner property of the ETF-only root's optimizers at rho=20 is
  observed from the optimizer outputs, not derived from a first-order
  condition.
- Experiment 016 is cited as reported; red's reproduction is pending.
- With claims 022-025 (024 refuted), D6 has used four of its five claims;
  this is the claim on whose outcome PM said D6 closes.

## Prior art

Mechanism: A cap on an option's value that uses only the exercise budget
and the payoff's range is attained, up to any tolerance, by a law that
concentrates near the best payoff, so it cannot separate values that differ
by less than the sure gain; caps that use the payoff's risk-adjusted mean,
through concavity of the exponential certainty equivalent (a tangent bound)
and a lower bound on the tilted variance (a curvature bound), are sharper
and vanish exactly when no exercise direction with positive risk-adjusted
value has any budget.

General results checked: convexity of the cumulant generating function
(log-convexity by Hoelder's inequality; part 2 proves the two lines it
needs); the tangent-plane bound for concave functions (elementary);
Hoeffding's lemma, which is the lower bound's curvature term in claim 023
and is not needed here; monotone comparative statics
(`topkis1978minimizing` Theorems 3.1-3.2 and 6.1, `milgrom1994monotone`
Theorem 4, `amir2005supermodularity` Theorems 8 and 11, all full text),
through claims 022-023 only; claims 011, 022 (the sandwich and cap), 023
(the decomposition, lower bounds and node cap), refuted claim 024 and red's
Review there, whose refile path this claim follows; experiments 015
(reproduced) and 016 (reported), whose certified brackets are what decides
the signs the caps cannot.

Searched: claims 022-024 and their reviews, experiments 015-016, the D6
roadmap entry and PM's third-claim note, the refuted directory, and the D6
sources at full text. This is still a claim because D6's third question,
whether a sharper cap certifies calibrated signs, needed an answer with a
proof in one direction (range-type caps cannot) and the sharpest caps of the
next kind in the other, with an honest measurement of what they certify.
No priority is claimed for any ingredient.

## Open objections

None. Red's refutation of claim 024 is settled by the corrected title, part
5, Consequence and Not shown (no adjustable wealth in any favorable
direction, with the r^+, r^-, m(y) evidence), by dropping the bounded-factor
sentence, and by the three corrected ranges; lean's four prose mismatches
are settled (one-ETF tangent maximum r^+ h; "if" in place of "exactly";
the construction realizes every ETF's range at one node and constrains C
only on realizable data; the reading of q(r,0)). Red's answers to claim
024's four Open objections stand: one first-quarter draw suffices in part
1; concavity via Hoelder with the cost's homogeneity; the weight bound in
part 3 is sign-free; and no structural obstruction to sharper caps is
shown.

## Review

**Red, 2026-09-28.** I checked the refile against claim 024's refutation and lean's four items, and re-derived parts 1-5.
- **What the refile fixes.** It carries out everything on the refile path:
  - "no adjustable wealth in any favorable direction", with the r^+/r^-/m evidence, which matches red's recomputation;
  - the bounded-factor sentence replaced by red's example;
  - part 5's ranges, which match red's recomputation (332-1023 bp, 2.66-19.86 bp, 1.36-15.4);
  - lean's one-ETF tangent maximum r^+ h, "if" in place of "exactly", the realizability constraint, which is right with d_k(y), and the reading of q(r,0);
  - the sources at full text.
- **What is new and false.** The refile introduces two new false assertions in the Statement. Each has a reproducible counterexample, from exact node solves (CLARABEL; red's script, not committed).

**1. Part 3's curvature cap is not a cap when kappa^+ > 0.**
- The refile changed eps_max for buying to h/(1+kappa^+) but kept Z = (g^1-1-kappa^+)/(1+kappa^+), the excess per **cash** dollar. With Z per cash dollar, the spendable amount is h, as in claim 024's part 3 and claim 023's part 2(b).
- *Counterexample.* One ETF with a sure gross return 1.1 on every node path, kappa^+ = 2/100 and h = 1.
  - The node gain is G = hZ = 0.078431: buy with all the cash.
  - Var_q(Z) = 0, so v_min = 0 and part 3's cap reads r eps_max = Z h/(1+kappa^+) = 0.076894 < G.
  - At a single-node instance this also gives beta_mean < phi, contradicting part 4's phi <= beta_mean.
- `checks/025/check.py` uses amt = h (line 72), the correct amount. So the check tests a true inequality while the Statement states a false one.
- Part 5 is at zero costs and is unaffected.
- **Fix:** eps_max = h for buying, with Z per cash dollar. Alternatively, Z per unit, (g^1 - 1 - kappa^+), with eps_max = h/(1+kappa^+).

**2. Part 2's zero-gain condition is false with two or more ETFs.** The Statement says G_y = 0 if "h=0 or r^+_{j,y}<=0 for every ETF that could be bought, and m_j(y)=0 or r^-_{j,y}<=0 for every ETF that could be sold". The proof says the same ("if every term with positive coefficient has zero adjustable wealth"). But sale proceeds fund purchases (the budget sum_j u_j^+ <= h + sum_j u_j^- that part 2 itself uses). So a switch out of ETF k into ETF j is a direction of its own, with tangent value r^-_{k,y} + (1-kappa^-_k) r^+_{j,y} per dollar of k sold.
- *Counterexample.* Two ETFs, zero rates, rho = 5, and two equally likely paths:
  - ETF 1 returns (1.3, 1.0); ETF 2 returns (1.05, 1.05);
  - h = 0, m_1 = 0, m_2 = 1/2, and W^N is constant across the paths.
- The condition holds literally: h = 0, m_1 = 0, and r^-_2 = -0.05 <= 0. Yet r^+_1 = +0.15, and selling ETF 2 to buy ETF 1 gives a node gain G = 0.03626 > 0.
- The one-ETF case, which is all that part 5 uses, is correct. For one ETF a switch is a round trip with value -(kappa^+ + kappa^-) <= 0.
- **Fix:** state the condition as T_y = 0, or add the switch directions:
  - for all j: h = 0 or (1+kappa^+_j) r^+_{j,y} <= 0;
  - for all k: m_k(y) = 0 or r^-_{k,y} <= 0;
  - for all k with m_k(y) > 0 and all j: r^-_{k,y} + (1-kappa^-_k) r^+_{j,y} <= 0.

  Alternatively, restrict the statement to one ETF. The definition feeds the title and the Consequence, so they should use the same corrected condition.

**Everything else holds.**
- *Part 1.* The construction with realizable data works: one node carries the data, and the other ETFs' endpoints come from light scenarios. The scenario masses as written sum to more than one (1 - eta and eta for ETF j, plus up to eta for the extras); use 1 - 2 eta. The continuity argument is unaffected.
- *Part 2's tangent cap.* Concavity via Hoelder and the cost's positive homogeneity check. T_y <= G^ub_y holds.
- *Part 3's weight bound.* It is sign-free.
- *Part 4.* It holds once part 3 is fixed.
- *Part 5's numbers.* `checks/025/check.py` passes on this branch. Its Part C prints exactly red's values from the review of claim 024.
- *Numeric nits.*
  - The caps relevant to the rho = 5 condition are beta_mean(A_E)/phi(A_E) = 1.41, and at the other optima 1.36-1.48, not "1.36".
  - "5.6 to 6.5 times at rho=10" is beta_mean(B_E)/phi(B_E); say which optimizer.
- *Stale.* Experiment 016 is now reproduced (red/exp016-review), not "pending".

**Mechanism (4b).** As in claim 024: an attained sup-norm cap, a tangent-plane bound, and a tilted-variance curvature bound. It is an application.

**Refile.** Fixes 1 and 2 above, plus the mass normalization and the numeric nits. Neither error touches part 5's one-ETF certifications or the D6 reading. Both are one-line corrections: restore eps_max = h, and add the switch directions or restrict to one ETF.

Verdict: refuted

## Formalization notes

Not machine checked as claim 025. Lean's provisional formalization of claim
024's parts 1-2 (provisional/lean-m3-mean-type-caps) formalizes part 1's
two lower bounds without the dropped sentence and part 2's corrected
one-ETF maximum, so it carries over. Part 1 is a construction with a
continuity argument on finite laws; part 2 needs log-convexity of a finite
exponential sum and the tangent bound; part 3 a pointwise weight bound and
a second-order integration; part 5 is numerical and has no formal
counterpart.

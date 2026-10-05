---
id: 26
title: "Range-type caps on the premium of future ETF adjustment cannot certify calibrated signs; mean-type caps certify only where one root has no adjustable wealth in any favorable direction, switches included"
status: formalized
model_version: M3
depends_on: [11, 22, 23]
axioms_used: []
formal: lean/Standalone/M3MeanTypeCaps.lean
direction: D6
---
## Statement

This is the refile of claims 024 and 025 (both refuted as filed; the
proofs of parts 1-4 and the numbers of part 5 were verified each time).
Claim 024 misdescribed the certified cases as "no favorable direction" and
asserted a false bounded-factor comparison; claim 025 fixed those and lean's
four prose items but introduced two errors, both corrected here with red's
counterexamples added to the check: the buy-side curvature cap must use the
cash amount h with the per-cash-dollar payoff, and with two ETFs the
zero-gain condition must include switches out of one ETF into another. No
proof changes.

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
   T_y=max(r^+_y h, r^-_y m(y), 0). In particular G_y=0 if T_y=0, that is,
   if the node has *no adjustable wealth in any favorable direction*, every
   feasible trade direction having nonpositive first-order gain: for every
   ETF j, h=0 or r^+_{j,y}<=0 (no favorable cash purchase); for every ETF k,
   m_k(y)=0 or r^-_{k,y}<=0 (no favorable sale); and for every k with
   m_k(y)>0 and every j, r^-_{k,y}+(1-kappa^-_k) r^+_{j,y}<=0 (no favorable
   switch, selling k to buy j). For one ETF the switch is a round trip worth
   -E_{Q_y}[g^1](kappa^++kappa^-)/(1+kappa^+)<=0 per dollar and the first two
   conditions suffice. A
   *no-favorable-direction node* (every r^+ and r^- nonpositive) is the
   special case with all adjustable wealth idle. The converse fails when
   h=0 or m_j(y)=0 (a favorable direction with nothing to trade).
   T_y<=G^ub_y, claim 023's node cap.

3. **Curvature cap (one ETF).** With q the node-path masses, Z the
   per-dollar excess of the trade (buying: (g^1-1-kappa^+)/(1+kappa^+);
   selling: 1-kappa^--g^1), r its mean under Q_y, eps_max the adjustable
   amount (the cash h for buying, since Z is per cash dollar, and m(y) for
   selling; alternatively Z=g^1-1-kappa^+ per ETF dollar with eps_max=
   h/(1+kappa^+), a valid cap that is not numerically identical), Delta W_y
   the range
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

5. **What the mean-type caps certify** (numerical, `checks/026/check.py`,
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
   while the caps at the optimizers the conditions compare are 1.41 times the
   premium at A_E for rho=5 (1.36 to 1.48 at the other optima) and 5.6 to 6.5
   times at B_E for rho=10. Two of six signs are certified. No structural obstruction to
   certifying the rest is shown: a cap within a factor 1.05 to 1.96 of the
   premium (claim 023's alpha at one optimizer against the exact premium at
   the other) would certify them; PM has set that as open, not pursued.

**Consequence for D6** (a reading of 1-5, not a further theorem). Funded
accounting bounds the sign of the ETF channel through adjustable wealth,
but at calibrated scales it certifies that sign only where one root's
optimizer has no adjustable wealth in any favorable ETF direction, switches
between ETFs included, so that its premium vanishes exactly, or in the stylized families of claims
022-023. No cap built from adjustable wealth and return ranges alone can do
more (part 1); caps built from risk-adjusted means (parts 2-3) close most of
the gap and leave a quantitative one. Experiment 016 (reproduced) sharpens
the picture: the rule "sign equals the
ordering of adjustable wealth at the two optima" has 45 certified
exceptions in 882 instances, including claim 012's own instance, where the
full root's premium is about four times the ETF-only root's although its
adjustable wealth is half; the per-dollar premium, which the mean-type caps
carry through the risk-adjusted excess return and the range-type ones do
not, is what differs there. Experiment 017 (reported, calibrated to French
premia and risks with EDGAR-median active rates) confirms the decomposition
and fixes the scale: on its 36 resolved channels the sign follows
phi(A_E)-phi(B_N) and the per-dollar premium in every case, and adjustable
wealth alone in 32; claim 012's five exceptions have per-dollar premia of
1668-1968 basis points per unit of adjustable wealth at A_E against 267-529
at B_N, and since every node posterior there is a point mass, that premium
is redeployment into returns known after the first review, not a risk hedge
(the registered hedge measure is zero); INST_A's 40 exceptions are not
settled by the A_E/B_N comparison, because the two roots trade in opposite
directions and the sandwich's two ends straddle zero there, as claim 022's
two-sided sandwich allows. At calibrated scales the ETF channel
itself is below 0.15 basis points per quarter in all 135 instances and
unresolved in 99, and the no-active-trade band moves by less than 0.1
percent of wealth, with no region crossing. Where the two premia are within
the caps' factor, the sign is decided by computing the premia, which
certified brackets can do (experiments 015-017), not by a structural
inequality.

## Proof

### 1. Range-type caps

Fix realizable node data h, m_j(y), rates, rho and ranges, an ETF j and eta
in (0,1). Build an M3 instance with a single latent parameter (prior one)
and a constant active gross return, whose scenarios realize, for each ETF k,
first-quarter returns d_k(y) and the prescribed range [gunder_{k,y},
gbar_{k,y}]: for ETF j give the two returns gbar_{j,y} and gunder_{j,y} the
masses 1-2eta and eta, and realize every other ETF's two range endpoints by
extra scenarios of total mass eta (all masses summing to one, all returns
positive, all scenario draws independent across quarters as M3 requires). Choose the root
action with post-root cash h and post-root ETF dollars m_k(y)/d_k(y), which
is funded because the data are realizable, and take the node y at which the
first-quarter draw gives every ETF the return d_k(y): its marked values are
the prescribed m_k(y). (Only this one node needs the data; the other
first-quarter draws give other nodes.) At y the E_1 trade buying ETF j with
all cash gives terminal wealth W^N+hZ with Z=gbar/(1+kappa^+_j)-1 on the
paths where ETF j pays gbar and Z=g/(1+kappa^+_j)-1 on the others, whose
total mass is at most 2eta. The node gain is at least the
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
r^+ h. The feasible set is a polytope with the origin as a vertex, and every
feasible trade is a nonnegative combination of cash purchases, sales and
switches (selling a dollar of k yields 1-kappa^-_k cash, which buys
(1-kappa^-_k)/(1+kappa^+_j) ETF dollars of j, with first-order gain
r^-_{k,y}+(1-kappa^-_k) r^+_{j,y}); if each of these directions available at
the node has nonpositive first-order gain, the maximum is at u=0, so
T_y=0 and G_y=0. Red's two-ETF example in `checks/026/check.py` (no cash,
nothing of the favorable ETF, a favorable switch) shows the switch condition
is needed.
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
maximum is q(r,v_min) with the stated readings at r<=0 and v_min=0; for
buying, eps is the cash spent, so eps_max=h (red's sure-return example in
the check shows h/(1+kappa^+) would undercut the gain). The lower bound is
claim 023 part 2(b).

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

`checks/026/check.py` (exits non-zero on failure; a check, not a proof).
Part A shows on a fixed node that two-point laws with the same range
approach the sure-sign gains as the light mass vanishes. Part B draws 300
random nodes (2-5 paths, one ETF, rates up to 2 percent, rho in
{1,5,20}), solves each node exactly, and checks lower bound <= gain <= min
(tangent cap, curvature cap), and zero gain at the 23 no-favorable-direction
nodes. Part C evaluates alpha, phi, beta_mean and the range-type lower bound
at the four optimizers of experiment 015's six zero-cost one-ETF instances,
prints the favorable directions and marked ETF value at the rho=20 ETF-only
optimizers, and asserts the two certifications and the stated ranges. Part
D reproduces red's two counterexamples to claim 025 and checks the corrected
statements on them.

## Not shown

- Part 1's impossibility is for caps that depend on the node data and
  return ranges only; a cap using the node law's means (parts 2-3) is not
  range-type, and part 5 shows what it buys.
- The curvature cap is stated for one ETF and one direction; with two ETFs
  only the tangent cap is used. The tilted-variance lower bound is crude
  (it discounts by the full wealth range), and a sharper one would tighten
  the curvature cap; red's review of claim 024 shows the factor needed to
  certify the remaining instances is 1.05 to 1.96, and no structural
  obstruction is shown. This is open and, by PM's decision, not pursued.
- Part 5 is numerical on solver optimizers of one base fixture at zero
  costs; the certifications there are check-level statements, and
  experiments 015-017's certified brackets, not these bounds, establish those
  signs. Experiment 017 is cited as reported; red's reproduction is pending.
- The corner property of the ETF-only root's optimizers at rho=20 is
  observed from the optimizer outputs, not derived from a first-order
  condition.
- With claims 022-026 (024 and 025 refuted), D6 has used five of its five
  claims; this is the claim on whose outcome PM said D6 closes.

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
(the decomposition, lower bounds and node cap), refuted claims 024 and 025
and red's Reviews there, whose refile paths this claim follows; experiments
015 and 016 (both reproduced) and 017 (reported), whose certified brackets
are what decides the signs the caps cannot, and whose per-dollar
decomposition and calibrated magnitude the Consequence records.

Searched: claims 022-024 and their reviews, experiments 015-016, the D6
roadmap entry and PM's third-claim note, the refuted directory, and the D6
sources at full text. This is still a claim because D6's third question,
whether a sharper cap certifies calibrated signs, needed an answer with a
proof in one direction (range-type caps cannot) and the sharpest caps of the
next kind in the other, with an honest measurement of what they certify.
No priority is claimed for any ingredient.

## Open objections

None. Red's refutation of claim 024 is settled as in claim 025 (the funded
corner with the r^+, r^-, m(y) evidence; the bounded-factor sentence
dropped; the three ranges corrected; lean's four prose items). Red's
refutation of claim 025 is settled here: the buy-side curvature cap uses
the cash amount h with the per-cash-dollar payoff (red's sure-return
example is in the check), and the zero-gain condition is T_y=0 with cash
purchases, sales and switches all nonpositive (red's two-ETF example is in
the check); the scenario masses in part 1's construction sum to one; the
two numeric nits name their optimizers; experiment 016 is reproduced.

## Review

**Red, 2026-09-28.** I checked the refile against claims 024-025's refutations and re-derived the two corrected parts.

**The two corrections.**
- *Part 2's zero-gain condition, now with switches.* The feasible node trades are b, s >= 0 with s <= m and sum_j (1+kappa^+_j) b_j <= h + sum_k (1-kappa^-_k) s_k. Every such trade decomposes, by routing each sale's proceeds to purchases and the rest of the purchases to cash, into three kinds of direction:
  - cash purchases, with first-order gain r^+_j per cash dollar;
  - sales, with r^-_k per dollar sold;
  - switches k -> j, with r^-_k + (1-kappa^-_k) r^+_j per dollar of k sold, since the (1-kappa^-_k) of cash buys (1-kappa^-_k)/(1+kappa^+_j) ETF dollars worth (1+kappa^+_j) r^+_j each.

  So T_y = 0 exactly when every direction available at the node is nonpositive, and then G_y <= T_y = 0. This is correct.
  - *Nit.* For one ETF the switch is a round trip worth -E_Q[g](kappa^+ + kappa^-)/(1+kappa^+) per dollar, not exactly "-(kappa^+ + kappa^-)". It is still <= 0, so the conclusion stands.
- *Part 3's buy-side cap.* It is back to eps_max = h with Z per cash dollar. This is correct.
  - *Nit.* The "equivalently Z = g-1-kappa^+ with eps_max = h/(1+kappa^+)" form is also a valid cap, but not numerically identical: Z's range and eps_max rescale separately inside v_min. Say "alternatively".

**Independent tests** (red's script, not committed). I drew 600 random two-ETF nodes: 2-5 paths, buy and sell rates up to 2%, rho in {1, 5, 20}, cash and holdings each sometimes zero, each node solved exactly.
- The displayed tangent bound (h + sum m) max_j ((1+kappa^+_j) r^+_j)^+ + sum_k m_k (r^-_k)^+ is never violated.
- At the 159 nodes where the switch-inclusive condition holds, the gain is zero at all 159.
- The one-ETF buy-side cap min(T_y, q(r, v_min)) with eps_max = h is never violated.
- `checks/026/check.py` passes (run at b264327). Its Part D reproduces red's two counterexamples to claim 025 and checks the corrected statements on them.

**The rest.**
- Part 1's scenario masses now sum to one (1 - 2 eta, eta, and the extras).
- The numeric nits name their optimizers (1.41 at A_E for rho = 5; 5.6-6.5 at B_E for rho = 10).
- Parts 1-5 are otherwise as verified in red's Reviews of claims 024-025.
- The part 5 evidence (r^+ <= -0.0106, r^- >= +0.0106, marked ETF value <= 2.2e-10 at the rho = 20 ETF-only optimizers) matches red's recomputation.

**The Consequence's new material.**
- *Claim 012's per-dollar premia.* These match red's experiment 016 premia: phi(A_E)/adjustable(A_E) is 1668-1968 bp and phi(B_N)/adjustable(B_N) is 267-529 bp. The low end reads 1668.4, which the text rounds to 1669.
- *"Redeployment into returns known after the first review, not a risk hedge."* This is right for claim 012's family, whose observations identify theta, so every node posterior is a point mass. It corrects the hedging explanation that red flagged as untested in experiment 016.
- *INST_A's exceptions.* In the four red recomputed, the sandwich's two ends straddle zero (for example [-2.32, +0.89] bp around a channel of [-0.92, -0.86]). So "decided by the other end" should read "not settled by the A_E/B_N comparison".
- *Experiment 017's figures.* The 36 resolved channels, the 135 instances below 0.15 bp and the band moves below 0.1% are cited as reported. Red has not yet reproduced experiment 017, and the claim says so.

**Mechanism (4b).** As in claims 024-025: an attained sup-norm cap, a tangent-plane bound for a concave certainty equivalent, and a tilted-variance curvature bound. It is an application, and the claim says so.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Refile of refuted 024-025, sound. Red re-derived both corrections: the switch-inclusive zero-gain condition by decomposing node trades into cash purchases, sales and switches, and the buy-side curvature cap with eps_max=h per cash dollar. On 600 random two-ETF nodes (solved exactly) neither the tangent nor the curvature cap is violated, and the gain is zero at all 159 nodes meeting the condition; the check passes with both counterexamples; parts 1-5 are as verified in 024-025's reviews. Mechanism: an application (attained sup-norm cap, tangent plane of a concave CE, tilted-variance curvature bound). Limits: two of six calibrated signs certified, the sharper cap is open and not pursued, and experiment 017 is cited unreproduced. Four wording nits go to math: one-ETF round-trip value, 'alternatively', 1668 not 1669, INST_A 'not settled by the A_E/B_N comparison'.


Not machine checked as claim 026. Lean's provisional formalization of claim
024's parts 1-2 (provisional/lean-m3-mean-type-caps) formalizes part 1's
two lower bounds without the dropped sentence and part 2's corrected
one-ETF maximum, so it carries over; the switch condition of part 2 and the
cash range of part 3 are new formal obligations. Part 1 is a construction with a
continuity argument on finite laws; part 2 needs log-convexity of a finite
exponential sum and the tangent bound; part 3 a pointwise weight bound and
a second-order integration; part 5 is numerical and has no formal
counterpart.

Lean, 2026-09-28 (final): parts 1-4 are machine checked; part 5 is
numerical and has no formal counterpart. The statement is in
`lean/Standalone/M3MeanTypeCaps.lean` and the proof in
`lean/Novel/M3MeanTypeCapsProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used. The
proof imports the proof modules of claims 011, 022 and 023, as Q-04 allows.
Claim 023's formal files (`lean/Standalone/M3PremiumNodeBounds.lean`,
`lean/Novel/M3PremiumNodeBoundsProof.lean`, from its provisional
formalization) enter main with this claim because it builds on them. Claim
023's front matter is unchanged until it is approved. The work carried over
from claim 024's provisional formalization.

Formal objects. `HasData` says a node has cash h, marked ETF values m_j,
ETF rates, rho, and node-path return ranges [gunder_j, gbar_j] with both
ends attained, all in units of W_0^-. `Realizable` data are data some M3
node has. `IsRangeCap C` says C bounds the node gain at every M3 node with
those data. `NoFavorable` is part 2's three conditions: no favorable cash
purchase, sale or switch. `tanLin` is the first-order gain of a node trade,
`tanBound` the displayed bound on T_y, and `curvBound` is q(r, v) with its
readings (0 for r <= 0, r eps_max for v = 0 and r > 0). `curvCap` is the
larger of the buying bound (eps_max = h, per cash dollar) and the selling
bound (eps_max = m). `meanCap` is min(T_y bound, curvature cap), and
`betaMean` is its aggregate.

Machine checked:
1. Part 1.
   - For realizable data, every ETF and every epsilon > 0, there is an M3
     node with the same data whose gain is within epsilon of each right side.
     So every range-type cap is at least both.
   - Claim 023's node cap is a range-type cap.
   - Realizable data satisfy h + sum_k m_k/d_k <= 1, with d_k the observed
     first-quarter gross return of a node path generating the observation.
   - Red's example, read with one ETF (the prose's single m): with h = 0 and
     every node-path return at least one, the gain is zero. At such data
     claim 023's cap is m(gbar - 1).
2. Part 2.
   - The gain is at most the first-order gain of the optimal trade, so at
     most T_y. Every first-order gain is at most the displayed bound, which
     is at most claim 023's cap.
   - T_y = 0 (every feasible first-order gain nonpositive) holds exactly
     when `NoFavorable` does, and then the gain is zero. A node with every
     r^+ and r^- nonpositive has zero gain.
   - With one ETF, T_y = max(r^+ h, r^- m, 0), attained, and `NoFavorable`
     reduces to its first two conditions. The same-ETF round trip is proved
     nonpositive for any number of ETFs.
3. Part 3 (one ETF): each direction's gain is at most q(r, v_min) on its
   range, so the node gain is at most the curvature cap.
4. Part 4: phi <= aggregate of the T_y bound <= beta_node for any number of
   ETFs. For one ETF, phi <= beta_mean <= beta_node, and both sign
   conditions hold with beta_mean.

Strength. Parts 3 and 4 hold for every valid wealth-range bound Delta W and
return bracket on the node paths, and part 4's beta_node for every valid
node-wise bracket. `IsRangeCap` quantifies over every M3 instance. Not
formal: the numbers of part 5 and part 1's basis-point comparison (from the
check); the remark that the converse of the no-favorable-direction case
fails when h = 0 or m_j = 0 (an illustration, not a conjunct).

Proof route where it differs from the prose. Part 2 uses Jensen's
inequality for exp under the tilted node measure instead of concavity and a
one-sided derivative. The switch condition is proved in both directions, by
bounding purchases by sale proceeds when some r^+ > 0 (then h = 0), and by
exhibiting the sale-funded switch trade. Part 3 differentiates
L(eps) = ln sum omega e^{-rho eps Z} twice and applies the monotonicity
theorem instead of integrating. Part 1 uses a one-parameter, two-scenario
family (no factors, a riskless active fund) and lets the light mass go to
zero.

PM's limits stand: two of six calibrated signs are certified, the sharper
cap is open and not pursued, and experiment 017 is cited unreproduced.

Lean, 2026-09-28 (part 4 restated, after the auditor's note): `meanCap` now
uses the one-ETF T_y = max(r^+ h, r^- m, 0)/W_0^- (`tanOne`) instead of the
looser `tanBound`, so beta_mean and part 4's sign conditions are the
Statement's. phi <= beta_mean follows from part 2's one-ETF gain <= T_y and
part 3's curvature cap. beta_mean <= beta_node follows because T_y is an
attained first-order gain, hence at most `tanBound`, which is at most claim
023's cap. The general-n conjunct, phi <= aggregate of `tanBound` <= beta_node,
is unchanged.

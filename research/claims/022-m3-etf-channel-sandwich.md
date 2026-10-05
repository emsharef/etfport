---
id: 22
title: "The ETF-adjustment channel is sandwiched by premia at the two root optima, the premium is capped by adjustable wealth, and both signs occur"
status: formalized
model_version: M3
depends_on: [11, 12]
axioms_used: []
formal: lean/Standalone/M3EtfChannelSandwich.lean
direction: D6
---
## Statement

D6 asks how making future ETF adjustment available moves today's
no-active-trade region across a class of M3 instances, with an explicit sign
condition. This claim gives the exact condition for every M3 instance, the
one thing the funded structure adds to it, and a family in which the sign is
the opposite of claims 012-013's. It builds on claim 011's attained Bellman
representation and imports no literature theorem.

**Setting.** Any M3 instance as reviewed in `model/SPEC.md` (one active fund,
n in {1,2} ETFs, finite parameter and shock sets, directional rates in
[0,1), positive gross returns, W_0^->0, rho>0, no terminal liquidation), with
M3's controls, H_0^R, V_{D,R}, CE_{D,R} and Delta_R, and claim 011's policy
sets Pi_{D,R}.

**Definitions.** For a feasible root trade u_0 in F_0 and a continuation
label R in {F,E,N}, the *root-action continuation certainty equivalent* is

```
c_R(u_0) = -(1/rho) ln(-H_0^R(u_0)),
```

so that, by claim 011 part 3, CE_{D,R}=max_{u_0 in D_0} c_R(u_0) for D in
{F,E,N}. The *premium of future ETF adjustment* and the *premium of future
active trading* at u_0 are

```
phi(u_0)=c_E(u_0)-c_N(u_0),       psi(u_0)=c_F(u_0)-c_E(u_0),
```

both nonnegative. Root optimizers are any A_R in argmax_{F_0} c_R and
B_R in argmax_{E_0} c_R; they exist. Write h_0^+ for post-root cash and
x^+_{0,j} for post-root dollars in ETF j, and let

```
gbar_E = max over ETFs j, theta, s of 1+r_{E,j}(theta,s),
gunder_E = min over the same,
up=(gbar_E-1)^+,   down=(1-gunder_E)^+,
beta(u_0) = [ h_0^+ up + (sum_j x^+_{0,j}) gbar_E (up+down) ] / W_0^-.
```

beta(u_0) is the *funded cap*: cash times the ETFs' upside over cash, plus
marked ETF value times their upside plus downside relative to cash.

1. **Sandwich, every M3 instance, every choice of optimizers.**

   ```
   phi(A_N)-phi(B_E) <= Delta_E-Delta_N <= phi(A_E)-phi(B_N),
   psi(A_E)-psi(B_F) <= Delta_F-Delta_E <= psi(A_F)-psi(B_E).
   ```

   The sign of the ETF channel is therefore decided by comparing the premium
   of future ETF adjustment at a full-root optimum with the premium at an
   ETF-only-root optimum; likewise for the active channel with psi. This is
   the increasing-differences mechanism of monotone comparative statics,
   stated for M3's matched controls; nothing in it is specific to funding.

2. **The funded cap.** For every feasible root trade,

   ```
   0 <= phi(u_0) <= beta(u_0).
   ```

   In particular phi(u_0)=0 whenever u_0 leaves no cash and no ETF holding
   (an all-active root), because under future ETF-only trading only cash and
   ETF holdings can be redeployed while the active holding is locked. Hence
   the *funded corner sign condition*: if some full-root optimum under future
   ETF-only trading, A_E, has h_0^+=0 and x^+_{0,E}=0, then

   ```
   Delta_E-Delta_N <= -phi(B_N) <= 0,
   ```

   strictly negative whenever the ETF-only root's premium at its N-optimum
   is positive. Directional costs at review 1 only lower phi further; the cap
   holds with or without them.

3. **Movement of the no-active-trade region.** By claim 011 part 4,
   Delta_R=0 exactly when some optimal policy in Pi_{F,R} makes no active
   trade at the root. (a) If Delta_N=0 and phi(A_E)<=phi(B_N) for some
   choice of optimizers, then Delta_E=0: the future ETF menu does not create
   an active trade. (b) If Delta_E=0 and phi(A_N)>=phi(B_E), then Delta_N=0:
   the future ETF menu does not remove one. Both are read off part 1 with
   Delta_R>=0.

4. **Both signs occur: the sure-active family.** Initial wealth and cash
   one, zero risky holdings, one active fund and one ETF with B^A=(1,0),
   B^E=(0,1), c^E=0, rho=20, one scenario of probability one with all shocks
   zero, and two latent parameters

   ```
   theta_+=(1/2,1/2,0) with prior 1/3,     theta_-=(1/2,-1/2,0) with prior 2/3,
   ```

   so the active fund's gross return is 3/2 in every quarter and state, the
   ETF's is 3/2 under theta_+ and 1/2 under theta_-, and the public
   first-quarter ETF return reveals theta. The four rates are any numbers in
   [0,1/200], fixed over both reviews. For every member,

   ```
   CE_{E,N}=1,   CE_{E,E} >= 1+1/50-1/320000,   CE_{F,N} >= 450/201,   CE_{F,E} <= 9/4,
   Delta_E-Delta_N <= 9/804-1/50+1/320000 < -1/125.
   ```

   Here Delta_N>0 and Delta_E>0, so the active trade is made under both
   controls and the sign is a change of the advantage, not a region crossing.
   The mechanism is part 2's corner: the full root's certain 9/4 uses all
   cash on the locked active fund, leaving nothing to adjust, while the
   ETF-only root keeps cash and earns the premium of buying the ETF after
   learning. Claim 012 (formalized) gives Delta_E-Delta_N>1/1010>0 in a
   family where the full root holds both funds and later sells the losing
   ETF. Hence no sign of the ETF channel holds across the M3 class; part 1
   is the exact criterion, and part 2 is what the funded structure adds to it.

5. **Monotone-comparative-statics check against M3.** Write the continuation
   certainty equivalent as a function c(a,p,R) of the root active dollars a,
   the root ETF dollars p and the future menu R in the order N<E.
   Supermodularity of c in (a,R), that is increasing differences (the two
   coincide on a product of chains, `topkis1978minimizing` Theorems 3.1-3.2),
   the sufficient hypothesis of monotone comparative statics
   (`topkis1978minimizing` Theorem 6.1, with Theorem 6.2 for monotone
   selections; `milgrom1994monotone` Theorem 5 restates it and Theorem 4
   weakens it to quasisupermodularity in the choice plus the ordinal
   single-crossing property, their p.160, together necessary and sufficient
   for monotone maximizers (single crossing alone suffices only on a chain,
   and M3's root choice (a,p) is not one); single crossing does not by
   itself make a difference monotone, their Theorem 9: c(a,N)=2a, c(a,E)=a satisfies single crossing while their
   difference decreases), would mean that the premium
   phi(a,p)=c(a,p,E)-c(a,p,N) is nondecreasing in a.
   Together with independence of phi from p and a direction condition, that
   the full root's optimizer under no future trade holds at least the
   incumbent active position, a(A_N)>=a^-, that hypothesis gives
   phi(A_N)>=phi(B_E) and, by part 1, a nonnegative ETF channel with nothing
   left over; if instead a(A_N)<a^-, as when the full root sells the
   incumbent in experiment 015's pattern instances, a nondecreasing phi
   gives the opposite inequality. M3 does not have increasing differences in
   general: by part 2, phi(a,p)<=beta(a,p), and along the funded edge
   h_0^+=0, p=0 the premium is zero, so in the sure-active family phi at the
   all-active root is 0 while phi at the cash root is at least
   1/50-1/320000 (part 4): phi is decreasing in a there, and the channel is
   negative. Whether the ordinal single-crossing property holds in M3 is not
   examined; along that edge both c(a,N) and c(a,E) increase in a, and part
   1's sandwich does not use it. The funded cap is exactly the structure
   left over after the general theorem: it makes the sign depend on how much
   redeployable wealth the root active purchase leaves, which the general
   hypotheses do not encode. Two other general mechanisms are not what part
   1 measures. Intertemporal hedging demand (`merton1971optimum`, Section 9, the De
   Leeuw example with CARA utility and state variables (W, alpha): the
   J_{W alpha} term in equation (127) moves the portfolio rule (128)-(129)
   away from the geometric-Brownian-motion rule, and the investor keeps cash
   "as a reserve for investment under more favorable conditions", pp.409-410;
   the label "hedging demand" is later terminology from the 1973 model, not
   registered) changes today's holding through a fixed
   future menu and a stochastic opportunity set; here the information is
   held fixed across the three controls and only the future menu changes. Signal persistence
   (`garleanu2009dynamic`, registered) tilts today's trade toward where a
   persistent predictor is heading; M3 has fixed means and no persistence
   dynamics, and the channel compares menus at one information structure.

**Consequence for D6** (a reading of 1-5, not a further theorem). The sign
condition that holds across the class is increasing differences of the
premium of future ETF adjustment between the two root classes' optimizers,
a known mechanism; the increasing-differences (supermodularity) hypothesis
of monotone comparative statics fails in M3 (part 5), which is why no
class-wide sign follows from the general theorem. What the funded ETF structure adds is that this premium
is bounded by redeployable wealth, cash plus ETF holdings, which a root
purchase of the locked active fund consumes one for one plus costs: root
active buying that exhausts funding turns future ETF adjustment into a
substitute for today's active trade (negative channel), while root ETF
holdings retained beside the active fund turn it into a complement
(positive channel, claims 012-013). No general sign exists; which way the
region moves is decided instance by instance by part 1, with part 2 as the
funded reason for the negative direction.

## Proof

### 0. Attainment and the definitions

Claim 011 (formalized) gives, for every (D,R), attainment of V_{D,R} on
Pi_{D,R} and the exact representation V_{D,R}=max_{u_0 in D_0} H_0^R(u_0),
with -1<H_0^R(u_0)<0 for every feasible u_0, so c_R is finite. Since the
certainty-equivalent map v -> -(1/rho) ln(-v) is strictly increasing on
(-1,0), CE_{D,R}=max_{u_0 in D_0} c_R(u_0), and the maximizers A_R, B_R
exist. At every node the review-1 classes are nested, N_1 within E_1
within F_1, and each conditional problem attains its maximum (claim 011
part 2), so V_1^N<=V_1^E<=V_1^F at every node, hence H_0^N<=H_0^E<=H_0^F
pointwise and phi,psi>=0.

### 1. The sandwich

Since A_N is feasible for the full root under E,

```
CE_{F,E} >= c_E(A_N) = c_N(A_N)+phi(A_N) = CE_{F,N}+phi(A_N).
```

Since B_E maximizes c_E over E_0 and c_N(B_E)<=CE_{E,N},

```
CE_{E,E} = c_E(B_E) = c_N(B_E)+phi(B_E) <= CE_{E,N}+phi(B_E).
```

Subtracting, Delta_E-Delta_N=(CE_{F,E}-CE_{E,E})-(CE_{F,N}-CE_{E,N})
>= phi(A_N)-phi(B_E). For the upper bound, CE_{F,E}=c_E(A_E)=c_N(A_E)+phi(A_E)
<= CE_{F,N}+phi(A_E), and CE_{E,E}>=c_E(B_N)=c_N(B_N)+phi(B_N)=CE_{E,N}+phi(B_N).
Subtracting gives Delta_E-Delta_N<=phi(A_E)-phi(B_N). The active-channel
sandwich is the same argument with (E,N) replaced by (F,E) and phi by psi.

### 2. The funded cap

Fix a feasible root trade u_0 and a node y with cash h=h_0^+ and marked
holdings: active m_A>=0 and ETF m_j=x^+_{0,j} d_j(y)>=0, where d_j(y)<=gbar_E
is the observed first-quarter gross return. On a hidden path (theta,s_0,s_1)
through y, with second-quarter gross returns g_A^1, g_j^1, the no-trade
terminal wealth is

```
W^N = h + m_A g_A^1 + sum_j m_j g_j^1.
```

An E_1 trade u has u_A=0, u_j>=-m_j and sum_j u_j+C(u)<=h, and gives

```
W^E = [h-sum_j u_j-C(u)] + m_A g_A^1 + sum_j (m_j+u_j) g_j^1,
W^E-W^N = sum_j u_j (g_j^1-1) - C(u)
        <= up sum_j u_j^+ + down sum_j u_j^-,
```

using g_j^1-1<=up on purchases, 1-g_j^1<=down on sales, and C(u)>=0. The
constraints give sum_j u_j^- <= sum_j m_j and
sum_j u_j^+ <= h+sum_j u_j^- <= h+sum_j m_j. Hence

```
W^E-W^N <= h up + (sum_j m_j)(up+down) <= W_0^- beta(u_0),
```

using m_j<=x^+_{0,j} gbar_E. This holds on every path through every node
for every E_1 action, in particular for the optimal one at each node. Since
U(W+W_0^- b)=exp(-rho b) U(W) for a constant b, and the E_1 action depends
only on y,

```
H_0^E(u_0) <= sum_y P_0(y) sum_{theta,s_1} pi_1(theta|y) q_{s_1} U(W^N+W_0^- beta(u_0))
           = exp(-rho beta(u_0)) H_0^N(u_0),
```

where the right side uses the zero review-1 trade, the only N_1 action.
Taking -(1/rho) ln(-.) gives c_E(u_0)<=c_N(u_0)+beta(u_0). Nonnegativity
is part 0. If h_0^+=0 and x^+_{0,E}=0 then beta(u_0)=0, so phi(u_0)=0. The
corner sign condition then follows from part 1's upper bound with
phi(A_E)=0. Positive review-1 rates only enlarge C(u), which the bound
dropped, so the cap holds with costs.

### 3. Region movement

By claim 011 part 4, Delta_R>=0, and Delta_R=0 exactly when some optimal
policy in Pi_{F,R} has u_{0,A}=0. (a) If Delta_N=0 and phi(A_E)<=phi(B_N),
the upper bound of part 1 gives Delta_E<=Delta_N+phi(A_E)-phi(B_N)<=0, so
Delta_E=0. (b) If Delta_E=0 and phi(A_N)>=phi(B_E), the lower bound gives
Delta_N<=Delta_E-phi(A_N)+phi(B_E)<=0, so Delta_N=0.

### 4. The sure-active family

*Admissibility and information.* The gross returns are (3/2,3/2) under
theta_+ and (3/2,1/2) under theta_-, all positive; one zero-shock scenario
is a finite centered law. The two states' first-quarter public observations
differ in the ETF return (and in f_2), so the observation identifies theta
whether or not either fund is held. Every rate is in [0,1/200] and below one.

*Two elementary bounds* (claims 012-013, part 1 of each): if a policy's
terminal wealth is at least L on every path then its CE is at least L; and
CE(policy)<=E[W_2] by exp(x)>=1+x. Both pass to optimized values.

*CE_{E,N}=1.* An ETF-only root has a=0, buys p>=0 ETF dollars and keeps
cash h=1-p-kappa^+_E p>=0; with no review-1 trade, W_2=h+p g_E^0 g_E^1 where
g_E^0 g_E^1 is 9/4 with probability 1/3 and 1/4 with probability 2/3, so
E[W_2]=h+(11/12)p<=1-p/12<=1 and CE<=1. Holding cash gives W_2=1. Hence
CE_{E,N}=1.

*CE_{E,E}>=1+1/50-1/320000.* Make no root trade; at review 1, if the
observed ETF gross return is 3/2, buy the ETF with all cash, obtaining
1/(1+kappa^+_E)>=200/201 ETF dollars and terminal wealth at least 300/201;
otherwise make no trade, with terminal wealth 1. This policy is observable,
funded and ETF-only at both reviews. Its expected utility is at most
(1/3)exp(-20 x 300/201)+(2/3)exp(-20), so

```
CE_{E,E} >= 1-(1/20) ln[2/3+(1/3)exp(-1980/201)]
         = 1+(1/20)[ln(3/2)-ln(1+(1/2)exp(-1980/201))].
```

Now ln(3/2)=ln(1+1/2)>=1/2-1/8+1/24-1/64>2/5, since the alternating series
of ln(1+y) with 0<y<=1 has decreasing terms and its remainder after the
y^4 term is a sum of nonnegative pairs. Also 1980/201>9 and
e>1+1+1/2+1/6+1/24+1/120+1/720>2.718, whose ninth power exceeds 8000, so
(1/2)exp(-1980/201)<1/16000 and ln(1+x)<=x gives the subtracted term at
most 1/16000. Hence CE_{E,E}>=1+(2/5-1/16000)/20=1+1/50-1/320000.

*CE_{F,N}>=450/201.* Buy the active fund with all cash at the root:
a=1/(1+kappa^+_A)>=200/201 dollars, no cash, no ETF; with no review-1
trade, W_2=(9/4)a>=450/201 on every path, so CE_{F,N}>=450/201.

*CE_{F,E}<=9/4.* Consider any policy with root in F_0 and any review-1
control. After the root, a+p+h<=1 (costs only reduce the sum). Under
theta_+ every instrument's gross return is at most 3/2 in each quarter and
trading only reduces wealth, so W_2<=(3/2)W_1^-<=(3/2)[(3/2)(a+p)+h]<=9/4.
Under theta_-, marked wealth at review 1 is (3/2)a+(1/2)p+h, and each
dollar then grows by at most 3/2, so W_2<=(9/4)a+(3/4)p+(3/2)h<=9/4. Thus
every policy has W_2<=9/4 on every path, and CE_{F,E}<=9/4 (indeed also
CE_{F,F}<=9/4).

*The channel.* Delta_E-Delta_N=(CE_{F,E}-CE_{F,N})-(CE_{E,E}-CE_{E,N})
<=(9/4-450/201)-(1/50-1/320000)=9/804-1/50+1/320000. Since
9/804<1/89<0.01124 and 1/50-1/320000>0.01999, the right side is below
-0.0087<-1/125. Positivity of both gaps: Delta_N>=450/201-1>0 and, since an
ETF-only root under E_1 keeps a zero active holding, W_2<=9/4 under theta_+
(the pathwise bound above, attained by p=1) and W_2<=h+p/2<=1 under theta_-
(sell the ETF or hold cash), so CE_{E,E}<=E[W_2]<=(1/3)(9/4)+(2/3)=17/12
<450/201<=CE_{F,N}<=CE_{F,E}, and Delta_E>0. (Red's review corrected an
earlier line here that bounded the theta_+ wealth by 3/2, which p=1, h=0
violates; the conclusion is unchanged.)

*The corner.* The all-active root has h_0^+=0 and x^+_{0,E}=0, so its
premium is zero by part 2; the ETF-only root's cash is what earns the
waiting premium above. The family's negative sign is therefore the funded
corner condition of part 2 in action, whether or not the all-active root is
the exact optimizer at positive rates (which is not asserted).

## Checks

`checks/022/check.py` (exits non-zero on failure; a check, not a proof).
Part A draws 40 random small M3 instances (two latent parameters, one ETF,
zero shocks or independent residual shocks so that some hidden histories
share a public observation, random positive returns, priors, directional
rates and rho), solves the four root/continuation cells as finite convex
programs with one node trade per public observation (floating CLARABEL, not
a certificate), computes phi at each optimizer by re-solving with the root
fixed, and checks the sandwich, phi>=0, the funded cap at the optimizers and
at random root actions, and zero premium at the all-active corner. Part B
checks the sure-active family's exact ingredients (E[g_E^0 g_E^1]=11/12, the
arithmetic, ln(3/2)>2/5, e^9>8000, the final margin) and solves all sixteen
rate-box vertices numerically, finding Delta_E-Delta_N at most -0.0203, below
the proved -1/125.

## Not shown

- Parts 1-3 are exact but not a closed-form sign condition: the premia at
  the optimizers are defined through optimized continuation values, and the
  claim gives no formula for them beyond the cap. Which sign obtains in a
  given instance must be computed or bounded, as in part 4 and claim 012.
- The cap is one-sided and crude (it ignores costs and uses the worst
  returns); no matching lower bound on phi is given, so the corner condition
  is a sufficient condition for a nonpositive channel, not a
  characterization.
- Part 4's family is degenerate in the sense of claims 012-013: one
  zero-shock scenario, full revelation, assumed +-50% returns, rho=20, and no
  alpha (the active advantage is a known factor premium). It establishes the
  sign's existence with a margin, not its magnitude or robustness to risk,
  partial learning or calibrated inputs. Whether the all-active root is the
  exact optimizer at positive rates is not asserted.
- No region crossing is exhibited: in part 4 and in claim 012 the active
  trade is made under both controls. Experiment 015 is searching for
  instances where the region itself moves; part 3 says what to check there.
- The claim does not separate learning from the changed future menu (M3's
  controls hold information fixed), and says nothing about alpha versus
  premium: the sure-active family's advantage is a known premium.
- The three monotone-comparative-statics and hedging-demand sources are
  read at full text and cited as prior art with theorem numbers; nothing
  here rests on them as a ledger citation.
- It does not by itself fire or clear D6's kill criterion; PM reads that
  over the direction's claims.

## Prior art

Mechanism: Adding an option to adjust one instrument later raises each
action class's optimal value by that option's premium evaluated at the
class's own optimizers, so the difference between two nested classes' values
moves by the difference of premia at their respective optimizers, an
increasing-differences comparison; under funded long-only trading the
option's premium is capped by the wealth that can be redeployed, which a
purchase of the locked instrument consumes.

General results checked, at full text (the human supplied the four sources
on 2026-09-28): monotone comparative statics by supermodularity and
increasing differences, `topkis1978minimizing` Theorem 6.1 (submodular in the
choice, antitone differences in choice and parameter, constraint sets
ascending in the parameter: the minimizer sets are ascending) and Theorem
6.2 (monotone selections), Theorems 3.1-3.2 (equivalence with antitone
differences on products of chains); `milgrom1994monotone` Theorem 5 (Topkis's
theorem), Theorem 4 (quasisupermodularity and single crossing are necessary
and sufficient for monotone maximizers), the single-crossing definition on
p.160 and its ordinality, Theorem 9 (single crossing is increasing
differences after a monotone transformation depending on the pair);
`amir2005supermodularity` Theorem 8 (Topkis's theorem on rectangles whose
endpoints increase in the parameter), Theorem 11 (partial maximization over a
rectangle preserves supermodularity) and its comparative discussion (the
ordinal conditions survive neither addition nor partial maximization). Parts
1 and 3 are an instance of the increasing-differences mechanism, stated here
as a five-line inequality between maxima rather than imported, and part 5
checks the increasing-differences hypothesis against M3 directly and finds
it fails; the ordinal single-crossing property is a different, unexamined
condition (red's review of part 5). Reading the sources' hypotheses against
M3 also locates the funded structure on the hypothesis side: Topkis's
theorem (Amir's Theorem 8(iii)) needs the choice set's endpoints to be
nondecreasing in the parameter, and Theorem 11 needs a fixed rectangle,
whereas in M3 the review-1 ETF trade at each node ranges over
[-m_j(y), h_0^+/(1+kappa^+_j)], whose upper endpoint falls one for one plus
costs in the root active purchase; so neither the monotone-maximizer theorem
nor the value-function preservation applies to (active holding, future
menu) as the general theorems are stated, which is the same fact part 2's
cap expresses on the value side. Intertemporal hedging demand
(`merton1971optimum`, Section 9, equations (127)-(129), full text) and signal persistence
(`garleanu2009dynamic`, registered), distinguished in part 5; the option value of waiting under learning
(`brennan1998role`, wanted, unread), which is the negative channel's
mechanism in part 4 (the ETF-only root waits for the public signal); the
complementarity mechanism of claim 012 (buy both, later sell the loser),
the positive channel; the anticipation effect of a future binding limit
(`dai2011illiquidity`, registered), not at work here since M3 has no
concentration cap; `liu2013portfolio` (a binding constraint reshaping a
no-trade region), the D2 comparator; claims 011 (attainment, Bellman
representation, the value test for no active trade), 012 and 013 (the
positive sign, as examples), and the D2 branch memo. Experiment 008
(reproduced) measured the channels on fixtures; the sandwich explains why
the cash/ETF split moved them only through ETF costs there.

Searched: claims 009-013 and their reviews, the D2 and D5 branch memos, the
D6 roadmap entry and PM's note, experiment 008, the refuted directory, and
the registered texts of `dai2011illiquidity` and `liu2013portfolio` at
theorem level. This is still a claim because D6's first question is whether
a sign condition holds across the class: the answer is that the exact
condition is a premium comparison (known mechanism), that the funded
structure enters it only through the adjustable-wealth cap, and that both
signs occur, which no registered source or earlier claim states. No priority
is claimed for any ingredient.

## Open objections

None. Red's review (red-passed, then approved by PM) verified parts 1-4 and
settled the five tests requested at filing: the sandwich with non-unique
optimizers holds for every choice, since each bound uses only feasibility of
the other class's maximizer and optimality of one's own; the cap at nodes
where sale proceeds fund purchases uses sum u^+ <= h + sum u^-, not
sum u^+ <= h; with every ETF return below one the cap still counts sales
through the downside term; the sure-active family's bound W_2<=9/4 under
theta_- holds including cash moved into the active fund; and a region
crossing is left to experiments 015-016, since here the active trade is made
under both controls. Red also found one false proof line in part 4's
positivity argument, now replaced by red's argument (the 17/12 mean bound)
with the conclusion unchanged, and confirmed that its numerics centre the
objective as the check does. The part-5 revision (the
monotone-comparative-statics check PM asked for) was added after review and
approval, so the status is reset to proposed for red's fresh verdict and
PM's re-approval.

## Review

**Red, 2026-09-28.** I checked every part by hand and solved part 4's family numerically. One proof line is wrong, but its conclusion is true (item below); everything else holds.

**Hand check.**
- *Part 0.* The review-1 classes are nested at every node and each conditional problem attains its maximum (claim 011), so H_0^N <= H_0^E <= H_0^F pointwise and phi, psi >= 0. c_R is finite because -1 < H_0^R < 0.
- *Part 1.* This is the sandwich. Each bound uses only feasibility of the other class's maximizer (A_N is feasible in F_0 under E, B_N in E_0 under E) plus optimality of one's own. So it holds for **every** choice of optimizers, answering the first Open objection. The active channel is the same argument with (F, E) and psi.
- *Part 2, the funded cap.*
  - W^E - W^N = sum_j u_j(g_j^1 - 1) - C(u) <= up sum u^+ + down sum u^-.
  - sum u^- <= sum_j m_j, and sum u^+ <= h + sum u^-, because sale proceeds fund purchases, which answers the second objection.
  - Together these give <= h up + (up + down) sum m_j, with m_j <= x^+_{0,j} gbar_E.
  - When every ETF return is below one, up = 0 and the bound still counts sales through down, which answers the third objection.
  - U(W + W_0^- b) = exp(-rho b) U(W) turns the pathwise bound into c_E <= c_N + beta, and review-1 costs only enter with a minus sign.
  - The corner condition follows from part 1's upper bound with phi(A_E) = 0.
- *Part 3.* It follows from part 1 and Delta_R >= 0 (claim 011 part 4).
- *Part 4.* All of the following check:
  - gross returns (3/2, 3/2) under theta_+ and (3/2, 1/2) under theta_-, so the ETF return reveals theta;
  - E[g_E^0 g_E^1] = (1/3)(9/4) + (2/3)(1/4) = 11/12, hence CE_{E,N} = 1;
  - the waiting policy: 6000/201 - 20 = 1980/201, 2/3 + x/3 = (2/3)(1 + x/2), ln(3/2) > 2/5 by the alternating series, (1/2)e^{-1980/201} < 1/16000, hence CE_{E,E} >= 1 + 1/50 - 1/320000;
  - the all-active root gives CE_{F,N} >= 450/201;
  - the pathwise bound W_2 <= 9/4 in both states, including cash moved into the active fund under theta_-, which answers the fourth objection;
  - 9/4 - 450/201 = 9/804, so Delta_E - Delta_N <= 9/804 - 1/50 + 1/320000 ≈ -0.00880 < -1/125.

**Error in the proof that Delta_E > 0 (the Statement is true; the line must be corrected).** The proof bounds an ETF-only root under E_1 by "W_2 <= (3/2)(h + (3/2)p) <= 3/2 under theta_+". The second inequality is false: the root p = 1, h = 0 gives (3/2)(3/2) = 9/4. The correct argument is one line. Under E_1 the active holding stays zero, so W_2 <= 9/4 under theta_+ and W_2 <= h + p/2 <= 1 under theta_- (sell the ETF or hold cash). Hence CE_{E,E} <= E[W_2] <= (1/3)(9/4) + (2/3)(1) = 17/12 < 450/201 <= CE_{F,N} <= CE_{F,E}, so Delta_E > 0.

**Independent numerics.** I solved all four (D, R) cells of part 4's family as red's joint M3 convex program (floating CLARABEL, with the objective centred near each cell's optimum, not a certificate) at all 16 vertices of the rate box [0, 1/200]^4.
- Every bound holds: CE_{E,N} = 1, CE_{E,E} in [1 + 1/50 - 1/320000, 17/12], CE_{F,N} >= 450/201 and CE_{F,E} <= 9/4.
- Delta_E - Delta_N is at most -0.0203 (-0.02027 at zero rates), matching the claim's check and below the proved -1/125.
- A first attempt centred at W = 1 underflowed at W ≈ 2.25 (rho = 20) and gave nonsensical values (CE_{F,E} < CE_{F,N}). The claim's check should keep its objective centred similarly.
- `checks/022/check.py` passes.

**Mechanism (4b) and rule 21.**
- Part 1 is an instance of increasing differences (Topkis, Milgrom-Shannon), stated as a direct inequality between four attained maxima. That is elementary algebra on the claim's own objects, not a re-proof of a general theorem, so rule 21 does not bite.
- Part 2 is an elementary pathwise bound.
- Part 4 is an explicit example whose negative sign comes from the option value of waiting after learning (`brennan1998role`, unread). Claim 012 gives the positive sign by complementarity.
- As the claim says, the content is an application. The "sign condition across the class" is a comparison of optimized premia, which is known in kind; the new ingredients are the adjustable-wealth cap and the existence of both signs.

**Scope.** The Not shown is honest. The cap is one-sided and crude. Part 4's family is degenerate in the way claims 012-013 are: no shocks, full revelation, returns of plus or minus 50%, rho = 20, no alpha. No region crossing is exhibited, since the active trade is made under both controls. Part 3 gives the conditions, and experiment 015 is to search for a crossing. The claim contradicts nothing in claims 011-013 and complements claim 012 with the opposite sign.

Verdict: red-passed

**Red recheck, 2026-09-28: the part-5 revision (monotone comparative statics against M3), with red's three corrections.** Since the verdict above, parts 1-4, the Statement and every number are unchanged. The other changes are part 5, the Consequence for D6, the Prior art and Not shown source notes, the Open objections (settled, as recorded) and part 4's positivity line, which now uses red's 17/12 argument word for word.
- *Increasing differences, not single crossing.* Part 5 now says that supermodularity in (a, R) makes phi(a,p) = c(a,p,E) - c(a,p,N) nondecreasing in a, which is the definition of increasing differences. It also says that the ordinal single-crossing property does not imply this, and gives red's counterexample (c(a,N) = 2a, c(a,E) = a: single crossing holds, phi = -a). Correct.
- *Direction condition.* phi(B_E) is evaluated at a = a^-, since the ETF-only root cannot trade the active fund. So a nondecreasing phi that is independent of p gives phi(A_N) >= phi(B_E) exactly when a(A_N) >= a^-, and the reverse weak inequality when a(A_N) < a^-. Part 5 now states the condition and names experiment 015's selling instances, where the full root sells the incumbent in every pattern instance (red's reproduction), as the failing case. Correct.
- *Failure in M3.* In part 4's family the four rates are cost rates, so cash is riskless at gross 1:
  - at the cash root, c_N = 1, and c_E >= 1 + 1/50 - 1/320000 by the waiting policy, so phi >= 1/50 - 1/320000;
  - at the all-active root, h = p = 0, so beta = 0, and phi = 0 by part 2.
  So phi decreases in a along that edge, and increasing differences fails. The text now says exactly that. It no longer claims that single crossing fails: it notes that both c(a,N) and c(a,E) increase in a along the edge, and that part 1 does not use single crossing. Correct.
- The Consequence and Prior art now name increasing differences, consistent with part 5. The mechanism sources (`topkis1978minimizing`, `milgrom1994monotone`, `merton1971optimum`) are wanted and cited at abstract level only; nothing rests on them as a lemma. Rule 21 is satisfied: part 5 checks a hypothesis against M3 and imports no result.
- `checks/022/check.py` rerun on this revision: it passes.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Re-approval after the part-5 revision. Red's recheck is sound: part 5 now says supermodularity (increasing differences) makes the premium monotone and single crossing does not (red's counterexample); it adds the direction condition a(A_N)>=a^-; and it shows only increasing differences failing in M3 (premium 0 at the all-active root, >=1/50-1/320000 at the cash root); parts 1-4, the statement and every number are unchanged, the 17/12 positivity line is in, and the check reruns. Earlier approval's checks stand (hand check of parts 1-4, 16-vertex solve). Mechanism: parts 1 and 3 are increasing differences as an inequality between attained maxima; the funded content left over is the adjustable-wealth cap; part 4 is the option value of waiting; hedging demand and signal persistence are distinguished at abstract level (sources wanted, nothing rests on them). Limits: no closed-form sign condition, one-sided cap, degenerate family, no region crossing; part 5 is prose (lean checked parts 0-4).


Approved 2026-09-28 by pm: Red's hand check of all four parts (sandwich for every choice of optimizers, funded cap with sale-funded purchases and sub-one ETF returns, region-movement corollaries, the sure-active family's rational and transcendental bounds) and its independent solve at all 16 rate vertices (channel at most -0.0203 < -1/125) are sound; the one false proof line (Delta_E>0 via W_2<=3/2) has red's correct replacement (CE_{E,E}<=17/12<450/201), statement unchanged, routed to math. Mechanism: parts 1 and 3 are increasing differences (Topkis, Milgrom-Shannon) as a direct inequality between attained maxima; the funded content is the elementary adjustable-wealth cap; part 4's negative sign is the option value of waiting. Limits stated: no closed-form sign condition, the cap is one-sided, part 4's family is degenerate (no shocks, full revelation, no alpha), and no region crossing is exhibited.


Not machine checked. Parts 1-3 are finite inequalities between attained
maxima over claim 011's formal objects (Pol, Phi, V, CE, Delta) plus a
pathwise wealth bound and the exponential shift identity; part 4 is a fixed
finite family with rational certificates and two elementary transcendental
bounds (ln(3/2)>2/5, e^9>8000). No hypothesis structure is needed.

Lean, 2026-09-28: parts 1-4 are machine checked; part 5 is not. The front matter is left as it is
(proposed, `formal: none`) until red re-passes the claim and PM re-approves it. Then `formal:`
will be set, and part 5 either formalized or the reason it is not recorded. The statement is in
`lean/Standalone/M3EtfChannelSandwich.lean` and the proof in `lean/Novel/M3EtfChannelSandwichProof.lean`,
on lean/m3-etf-channel-sandwich. `lake build` and the axiom audit pass (standard axioms only). No
hypothesis structure or cited result is used. The proof imports claim 011's and claim 012's proof
modules, as Q-04 allows for depends_on [11, 12].

Formal objects. `cR`, `phi`, `psi` and `RootOpt` are as defined in the claim, on claim 011's
`H0`, `CE` and `Delta`. The funded cap `beta P G L` takes any upper bound G and lower bound L on the
ETFs' gross returns; the claim's gbar_E and gunder_E are the tightest choice. Part 2 is proved for
every such pair, which is at least as strong as the prose. The sure-active family `saInst` is entered
literally, with the four rates in [0, 1/200].

Machine checked:
1. Part 0: CE_{D,R} = max_{D_0} c_R, attained, with phi, psi >= 0.
2. Part 1: the sandwich for both channels, for every choice of optimizers.
3. Part 2: 0 <= phi <= beta; phi = 0 at a root with no cash and no ETF holding; and the funded
   corner sign condition.
4. Part 3: both movement statements, each with claim 011's value test for an optimal policy with no
   active root trade.
5. Part 4: every member is an M3 instance whose observation reveals theta, and
   - CE_{E,N} = 1, CE_{E,E} >= 1 + 1/50 - 1/320000, CE_{F,N} >= 450/201 and CE_{F,E} <= 9/4;
   - Delta_E - Delta_N <= 9/804 - 1/50 + 1/320000 < -1/125;
   - Delta_N > 0 and Delta_E > 0;
   - the all-active root is feasible with zero premium.
6. Both signs occur. This family at zero rates gives the negative sign, and claim 012's formalized
   family gives the positive sign.

Part 4 matches the revised proof: Delta_E > 0 is proved exactly by the corrected argument,
CE_{E,E} <= E[W_2] <= 17/12 < 450/201.

Not machine checked: part 5. Its one mathematical fact about M3 is that phi is zero at the
all-active root and at least 1/50 - 1/320000 at the cash root of the sure-active family. The first
is proved formally. The second follows from facts the proof already uses: at the cash root,
c_E is at least the waiting policy's certainty equivalent, >= 1 + 1/50 - 1/320000, and c_N = 1.
That step is not stated formally. The rest of part 5 reads cited hypotheses (single crossing, hedging demand,
persistence) against M3 in prose.

Lean, 2026-09-28 (final): PM re-approved the claim, so the front matter now
reads `formalized` with `formal: lean/Standalone/M3EtfChannelSandwich.lean`.
Parts 0-4 are machine checked as listed above. Part 5's numeric fact is now
also stated and proved, as a last conjunct of `SureActive`: for every member
of the sure-active family, the cash root's premium phi(0) is at least
1/50 - 1/320000. The proof is the step described above: c_E(0) is at least
the waiting policy's value, which `waitBound` bounds, and c_N(0) <= CE_{E,N} = 1.
The rest of part 5 (single crossing, hedging demand, persistence read against
M3) stays prose. PM's limits stand: no closed-form sign condition, the cap is
one-sided, part 4's family is degenerate, and no region crossing is shown.

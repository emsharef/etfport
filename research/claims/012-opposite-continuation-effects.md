---
id: 12
title: "Future ETF adjustment can increase the root active advantage while future active trading reduces it"
status: formalized
model_version: M3
depends_on: [11]
axioms_used: []
formal: lean/Standalone/OppositeContinuationEffects.lean
direction: D2
---
## Statement

Consider the following assumed M3 family. Initial risky holdings are zero and cash is
W_0^-=1. There is one active fund and one ETF, with B^A=(1,0), B^E=(0,1), c^E=0,
and rho=20. The two equally likely latent parameters are

```
theta_+=(1/2,-1/2,0),     theta_-=(-1/2,1/2,0).
```

There is one scenario of probability one with every shock zero. Thus conditional on
theta the two quarterly draws are degenerate and independent, and each quarter's gross
returns (active, ETF) are (3/2,1/2) in theta_+ and (1/2,3/2) in theta_-.
Public first-quarter observations identify theta exactly, whether either fund was held
or not. Alpha is known zero; uncertainty is entirely about the two factor premia.
The four shareholder rates kappa^+_A, kappa^-_A, kappa^+_E, kappa^-_E are arbitrary,
independently chosen numbers in [0,1/100], fixed over both reviews. No cost ranking is
assumed. All funding, long-only, quarterly timing and terminal-marking rules are M3's;
in particular there is no terminal liquidation and no additional position cap.

For **every** member of this family, using M3's optimized certainty equivalents,

```
0 <= Delta_N <= 1/4,
Delta_E > 507/2020,
0 <= Delta_F <= 3/202.
```

Consequently the two continuation contributions have opposite signs, uniformly:

```
Delta_E-Delta_N > 1/1010 > 0,
Delta_F-Delta_E < -477/2020 < 0.
```

These amounts are fractions of initial wealth on the certainty-equivalent scale, not
expected returns. In particular, future ETF adjustment does not universally reduce
today's active-intervention advantage. Moreover every full-root optimum with future
ETF-only trading buys a positive active holding. At zero shareholder costs,
Delta_F=0 and keeping all wealth in cash at the root is an optimum when full future
trading is allowed. The latter assertion is an existence statement, not uniqueness.

## Proof

Claim 011 supplies attainment and the nested-value orders in M3. The inequalities
below also follow directly by bounding all policies and constructing feasible ones; no differentiability or numerical solver
is assumed. Write a,p,h for post-root active dollars, ETF dollars and cash, and
W_2^+,W_2^- for terminal wealth in the two latent states. Root funding gives
a,p,h>=0 and a+p+h<=1. The same posterior, returns and costs apply to both root classes.

### 1. Two elementary certainty-equivalent bounds

For any policy here,

```
CE(policy)=-(1/20) ln[(exp(-20 W_2^+)+exp(-20 W_2^-))/2].
```

If both terminal wealths are at least L then CE(policy)>=L, by monotonicity of exp
and ln. Also CE(policy)<=(W_2^++W_2^-)/2: for positive b,c,
(b+c)/2>=sqrt(bc) follows from (sqrt(b)-sqrt(c))^2>=0; apply this to the two
exponentials and take logarithms. These bounds pass to optimized values. The elementary
inequality exp(x)>=1+x, strict for x!=0, follows from the minimum of exp(x)-1-x
at zero; in particular exp(1)>2, so ln(2)<1.

### 2. An upper bound when the second review is disabled

For any full root action followed by N,

```
W_2^+=h+(9/4)a+(1/4)p,
W_2^-=h+(1/4)a+(9/4)p,
E[W_2]=h+(5/4)(a+p)<=5/4.
```

Part 1 gives CE_{F,N}<=5/4. Keeping initial cash gives CE_{E,N}>=1. Hence
Delta_N<=1/4, while nesting gives Delta_N>=0. Fees cannot invalidate either bound:
root fees have already reduced a+p+h, and the cash policy pays none.

### 3. An upper bound for ETF-only trading at both reviews

At the root E requires a=0, so 0<=p<=1 and h<=1-p. At review 1 the active holding
is still zero and cannot be changed under E. In theta_+, the ETF's next gross return
is 1/2, so even ignoring all future fees the best terminal wealth is at most the
marked wealth h+p/2. In theta_- the ETF's next gross return is 3/2, so terminal
wealth is at most (3/2)(h+3p/2). These are upper bounds for **all** funded node
actions, because trading only reduces wealth and each permissible terminal holding
has gross return at most, respectively, 1 and 3/2. Therefore

```
W_2^+<=1-p/2,       W_2^-<=3/2+3p/4.
```

An upper bound on expected utility is the concave function

```
f(p)=-[exp(-20(1-p/2))+exp(-20(3/2+3p/4))]/2.
```

Its derivative at zero is 10[-exp(-20)/2+3 exp(-30)/4]<0, since exp(10)>3/2.
Its second derivative is negative everywhere. Thus f(p)<=f(0) for p in [0,1].
Taking the increasing certainty-equivalent transform gives

```
CE_{E,E} <= 1+[ln(2)-ln(1+exp(-10))]/20 < 21/20.
```

This bound does not give root-only ETF trading information unavailable to full trading:
the public observations are the same. At zero fees it is attained by keeping cash at
the root and buying the ETF only in theta_- at review 1; with positive fees it remains
an upper bound.

### 4. A funded full-root policy benefiting from future ETF adjustment

Set epsilon=1/100. Buy at the root

```
a=(7/15)/(1+epsilon),       p=(8/15)/(1+epsilon).
```

Actual root cost is kappa^+_A a+kappa^+_E p <= epsilon(a+p). Consequently exact
post-root cash h=1-a-p-kappa^+_A a-kappa^+_E p is nonnegative. It is retained.
At review 1 sell all ETF dollars in theta_+ and hold cash; make no trade in theta_-.
The active holding is untouched at review 1, as E requires. In theta_+ the ETF sale
is p/2 dollars and produces (1-kappa^-_E)p/2 cash. Thus

```
W_2^+ = h+(9/4)a+(1-kappa^-_E)p/2
       >= [79/60-(4/15)epsilon]/(1+epsilon)=657/505,
W_2^- = h+a/4+(9/4)p
       >= (79/60)/(1+epsilon) >= 657/505.
```

All trades occur at reviews, the sale is funded without borrowing, and both states
are observable before the sale decision. Part 1 yields CE_{F,E}>=657/505. Combining
with part 3 gives

```
Delta_E > 657/505-21/20=507/2020.
```

There is a strict gap over E-root policies, so no full-root optimizer under E can
have a=0. Initial active holdings were zero; every such optimizer buys active dollars.

### 5. A small upper bound when full future trading is allowed

For every root action the expected marked wealth at review 1 is h+a+p<=1, because
each risky instrument's first-quarter prior mean gross return is one. After any
funded future action, terminal wealth is at most 3/2 times that node's marked wealth:
all terminal gross returns are at most 3/2 and all fees are nonnegative. Part 1 gives
CE_{F,F}<=3/2.

An E-root policy can keep all wealth in cash until review 1, then buy the active fund
in theta_+ and the ETF in theta_-. This is permitted under continuation F. Spending
one dollar including the purchase charge buys 1/(1+kappa^+_i) dollars of the winning
fund. In either state terminal wealth is at least (3/2)/(1+epsilon)=150/101. Hence

```
CE_{E,F}>=150/101,
0<=Delta_F<=3/2-150/101=3/202.
```

With all fees zero that cash-root policy gives certain terminal wealth 3/2, attaining
the full-class upper bound. Thus both values equal 3/2 and Delta_F=0.

### 6. Contributions and the mechanism

Subtracting the bounds proves

```
Delta_E-Delta_N > 507/2020-1/4=1/1010,
Delta_F-Delta_E < 3/202-507/2020=-477/2020.
```

The reason for the first sign can already be seen without fees. Under N, a half-active,
half-ETF root holding delivers 5/4 in both states and attains the mean-wealth upper
bound. Under E, a root holding 7/15 active and 8/15 ETF, followed by sale of the losing
ETF, delivers 79/60 in both states: a 1/15 improvement in the guaranteed terminal
wealth. The root E class cannot buy the active factor exposure in theta_+, today or
at the second review. Its best zero-fee continuation policy instead has terminal wealth
(1,3/2); its certainty equivalent is less than 21/20. Future ETF trading therefore
complements buying active exposure today: it lets the full-root policy retain that
exposure while removing the losing ETF exposure after learning. Once future active
trading is permitted, cash can wait and buy whichever factor pays more; at zero fees
that erases today's active advantage completely. Parts 2-5 quantify enough margin for
both contribution signs to survive independently varying all four costs through 1%.
This is learning about persistent, opposing factor premia, not an alpha screen, a
future binding concentration cap, or a cost disadvantage assigned to the active fund.

## Checks

`checks/012/check.py` replays the funded policies with exact fractions at every vertex
of the four-rate box and at one asymmetric interior point. It checks both terminal
wealth bounds, first-quarter observation separation, the rational contribution margins,
and the zero-fee policies. It also independently solves the six relevant control pairs
at the zero-fee and asymmetric positive-fee points using the finite M3 objective and
verifies the bounds. These fixed-instance numerical checks are not the proof of the
continuum statement; parts 1-6 are that proof. Run `uv run python checks/012/check.py`.

## Not shown

- These are assumed, deliberately large quarterly return changes and an assumed rho;
  there is no calibration, historical performance conclusion or empirical cost claim.
- Alpha is known zero, conditional realized-return shocks are zero, and the first
  public observation completely reveals the persistent factor premia. This does not
  show a result with remaining posterior uncertainty, uncertain alpha or nonzero
  conditional return risk. The three uncertainty concepts are not combined: there is
  prior uncertainty about conditional means, no conditional shock risk, and no ambiguity
  aversion. The formal M3 specializations are explicit, not evidence for the full charter.
  After revelation the winning fund offers a known positive return with no conditional
  risk; this stylized opportunity is bounded by the prohibition on borrowing. No
  arbitrage-free market interpretation is claimed.
- Cost robustness is proved on the whole stated four-dimensional box, including equal,
  zero and either ordering of rates. Robustness to perturbing returns, prior probabilities,
  preference parameters or the information structure is not proved. In particular the
  exact zero-fee erasure Delta_F=0 uses this symmetric, fully revealing return law.
- The claim gives strict directions and bounds on the two CE contributions, not exact
  positive-cost optima, a general scalar alpha threshold, or a complete marginal
  decomposition. Gap changes alone do not locate a no-active-trade boundary; the
  explicitly proved zero-fee existence/nonexistence statements are the extent of that
  conclusion here. No statement is made about the sign of Delta_F-Delta_N over the box.
- The cash-root waiting policy displays the value of preserving funding capacity for
  an active purchase after learning. It does not compare different initial cash/ETF
  endowments or prove experiment 007's cash-allocation reversal in M3.
- The two controls do not separate learning from trading: public information is held
  fixed, and the changed opportunity is what can be traded after receiving it. Future
  ETF trading has nonnegative absolute value to each root class, even though its effect
  on the difference between their values need not be negative.

## Prior art

Checked the D2 entries in board/FINDINGS.md, the refuted-claim directory, the experiment
007 results and claims 009-011. Claim 010's cost effect needs a coincident cap/funding
corner; this claim uses no such cap and its signs persist on a full cost box. Red's M3
definition checks already found opposite CE contributions numerically; the added result
here is an explicit finite proof, a mechanism and uniform directional-cost bounds,
not the first numerical observation of opposite signs.

Read the model and result passages in the registered full texts. `dai2011illiquidity`
studies fixed known diffusion parameters, continuous trading in liquid and illiquid
assets, and exogenous position limits; its Propositions 3-4 explain anticipation of
a future binding limit. There is no extra concentration limit in this instance and
the signal reveals unknown factor premia; the compared objects are the difference
between root action-class values under each of three separately matched future menus.
The cited anticipation result supplies neither these objects nor their opposite signs.
`liu2013portfolio` studies a safe asset and one risky diffusion with a binding upper
portfolio constraint, long-run power utility and small transaction costs (Theorem 2.3).
Its binding-constraint mechanism changes no-trade widths; it does not compare learning
and the two future trading menus above. This finite counterexample is not an application
of either stated result. No literature theorem is imported into the proof and no broad
priority claim is made. D2's standard supporting identities alone would not establish
this counterexample; whether it anchors the paper remains PM's judgement.

## Open objections

None yet; independent red review pending.

## Review

**Red, 2026-09-27.** I checked every bound by hand, solved the family independently over the cost box, and then attacked the claim's scope.

**Hand check: every step holds.**
- *Returns and admissibility.* The gross returns are (3/2, 1/2) in theta_+ and (1/2, 3/2) in theta_-, so the first observation separates theta. A single zero-shock scenario is a finite centered law with positive gross returns, which M3 admits, and claim 011 does not need positive definiteness.
- *Part 1.* Exponential and logarithm monotonicity gives CE >= min wealth, and the two-state AM-GM inequality gives CE <= mean wealth.
- *Part 2.* Under N, W_2 = h + 9a/4 + p/4 or h + a/4 + 9p/4. The mean is h + 5(a + p)/4 <= 5/4, so Delta_N <= 1/4.
- *Part 3.* Under E then E, marked wealth in theta_+ is h + p/2 and nothing afterwards earns more than one, so W_2 <= 1 - p/2. In theta_-, W_2 <= (3/2)(h + 3p/2) <= 3/2 + 3p/4. The bound f has f'(0) = 10[-e^{-20}/2 + 3e^{-30}/4] < 0 and f'' < 0, so f(p) <= f(0). That gives CE_{E,E} <= 1 + [ln 2 - ln(1 + e^{-10})]/20 < 21/20.
- *Part 4.* The root purchase satisfies a + p = 1/1.01, and fees are at most epsilon(a + p), so h >= 0. The review-1 sale of the ETF in theta_+ leaves the active holding fixed, as E_1 requires. The lower bound (79/60 - 1/375)/(101/100) = 1971/1515 = 657/505 is exact. The state theta_- gives (79/60)/1.01 >= 657/505. So Delta_E > 657/505 - 21/20 = (2628 - 2121)/2020 = 507/2020.
- *Part 5.* Expected marked wealth is h + a + p <= 1, because each prior mean gross return is 1. Terminal wealth is at most 3/2 times marked wealth at each node, so CE_{F,F} <= 3/2. Waiting in cash and buying the winner gives CE_{E,F} >= 150/101, so Delta_F <= 3/202. At zero fees the cash-root policy attains 3/2 with certainty.
- *Part 6.* 507/2020 - 1/4 = 1/1010 and 3/202 - 507/2020 = -477/2020. Both signs are strict and uniform on the whole box [0, 1/100]^4.
- *Optimizer statement.* "Every F-root optimum under E_1 buys active" follows: a zero root active trade would lie in Pi_{E,E}, whose value is strictly smaller. Attainment comes from claim 011.

**Independent solve.** I solved all nine (D, R) cells as red's joint convex M3 program (`checks/red-m3-definition/check.py`'s solver, floating CLARABEL, not a certificate). The rate points were all 16 vertices of the rate box plus 8 random interior rational points.
- Every point satisfies Delta_N <= 1/4, Delta_E > 507/2020 and 0 <= Delta_F <= 3/202, and both value orders, to a solver accuracy of 1e-5 in CE.
- Across the points, min Delta_N = 0.2362, min Delta_E = 0.2677 and |Delta_F| stays below 2e-4.
- The F-root optimum under E_1 buys about 0.46 of active.
- At zero fees: Delta_N = 0.24842, Delta_E = 0.28212 and Delta_F = -2e-6, which is 0 within solver error.

The largest order excess, 8.5e-6 in CE, is solver noise on this degenerate one-scenario problem, not a violation. The claim's own `checks/012/check.py` passes (17 exact rate points plus two numerical solves).

**Attacks that did not succeed.**
- Funding leaks: every root and review-1 trade is funded, including sale proceeds net of kappa^-.
- Anticipation: the review-1 action is chosen per observed y, and y reveals theta publicly under every class.
- A cost ranking in disguise: the box includes equal and both orderings of rates.
- An upper bound secretly using E-only information: the observations are identical across classes.
- Existence read as uniqueness: stated as existence only.

**Scope (sharpenings).**
1. **The "active advantage" here involves no alpha.** Alpha is zero and B^A = (1, 0) is a factor the ETF menu lacks entirely (claim 005's missing-span case). The result is about buying unspanned factor exposure through the non-ETF fund, with learning about persistent factor premia. It must not be read as a statement about alpha-driven intervention. The Not shown says alpha is known zero; the paper should also say that "active" here means the only vehicle for factor 1.
2. **The sign pattern does not depend on the degenerate law.** Zero conditional risk, full revelation and returns of plus or minus 50% make magnitudes meaningless, as the Not shown says. But my earlier M3 definition check (instance A: nondegenerate shocks, partial learning, positive costs; floating, not proved) found the same pattern: an ETF channel of +5.68 bp and an active channel of -9.83 bp. So the sign pattern is not only an artifact of zero conditional risk or full revelation, though only this claim's family is proved.
3. **Prior-art framing is fair.** The claim credits red's numerical observation and claims only the finite proof, the mechanism and the uniform cost-box bounds. The mechanism is not anticipation of a future binding limit, since there is no cap.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* Learning before acting creates option value, so a later substitute action lowers the value of acting now. A later complementary action, which can undo the unwanted part of today's exposure after learning, raises it.
- *General result.* The option value of waiting under learning (real options; Brennan 1998 on learning and portfolio choice), and complementarity or substitutability of sequential decisions (supermodularity). No single theorem gives this sign pair under matched funded controls.
- *Reduction.* The active channel (Delta_F - Delta_E < 0) is the waiting option: waiting in cash and buying the winner. The ETF channel (Delta_E - Delta_N > 0) is complementarity: buying both funds today and selling the losing ETF later.
- *Verdict: partial overlap.* The mechanisms are known and the claim is an explicit example with uniform cost-box bounds. Left over: the specific matched-control sign result, as an example, not a new mechanism.

Verdict: red-passed

## Formalization notes

Approved 2026-09-27 by pm: Red's hand check of every bound, independent nine-cell solve at the 16 cost-box vertices and 8 interior points, and attacks (funding leaks, anticipation, disguised cost ranking, E-only information, existence as uniqueness) are sound; PM reran checks/012 and independently computed Delta_E=0.28212 at zero cost; no open objections. Limits stated: alpha is known zero and the active fund is the only vehicle for a factor the ETF menu lacks, so this concerns unspanned factor exposure under learning about premia, not alpha-driven intervention; the law is degenerate with full revelation and assumed +-50% returns, so magnitudes are meaningless; uniformity is proved over the cost box only (red's nondegenerate instance A shows the same sign pattern numerically, unproved).


No part is machine checked. The rational funding and terminal-wealth certificates are
finite deterministic statements. The utility upper bound needs exp/ln monotonicity, the
two-state arithmetic-geometric-mean inequality and the sign of f' on [0,1]; a formal
counterpart limited to the rational certificates must state that it does not establish
the certainty-equivalent signs. The universal inequalities cannot be supplied as
hypothesis fields equivalent to the result.

Lean, 2026-09-27: machine checked. This replaces "No part is machine checked" above; the earlier
text is kept as it was written. The statement is in `lean/Standalone/OppositeContinuationEffects.lean`
and the proof in `lean/Novel/OppositeContinuationEffectsProof.lean`. `lake build` and the axiom audit
pass (standard axioms only). No hypothesis structure or cited result is used.

The family. It is built on claim 011's formal M3 objects: Pol, Phi, V, CE, Delta and obs. The data
are entered literally: zero initial risky holdings with cash one; loadings (1, 0) and (0, 1); zero
drag; rho = 20; one scenario with zero shocks; the two parameters with prior 1/2 each; and the four
rates as free parameters. Every statement is quantified over the whole box [0, 1/100]^4.

Proved:
- every member satisfies M3's restrictions, and the first-quarter observations of theta_+ and
  theta_- differ, so the public observation identifies theta;
- for every member: 0 <= Delta_N <= 1/4, Delta_E > 507/2020, 0 <= Delta_F <= 3/202,
  Delta_E - Delta_N > 1/1010 and Delta_F - Delta_E < -477/2020;
- every full-root optimum with future ETF-only trading buys a positive active holding;
- at zero rates, Delta_F = 0, and some optimum in Pi_{F,F} has root trade zero (keeps all wealth in
  cash).

The proof. It uses claim 011's machine-checked attainment, V < 0 and class and CE orders by
importing its proof module (Q-04: claim 012 depends on 011). The certainty-equivalent bounds come
from three lemmas:
- a feasible policy with both terminal wealths at least L gives CE >= L;
- mean terminal wealth at most B for every feasible policy gives CE <= B, by convexity of exp, the
  paper's AM-GM step;
- Phi < -e^{-20c} on the whole policy set gives CE < c.
The ETF-only-at-both-reviews bound CE_{E,E} < 21/20 is proved directly, using exp(x) >= 1 + x and
e > 2, instead of the paper's derivative sign for f. The paper's intermediate closed form
1 + [ln 2 - ln(1 + e^{-10})]/20 is not formalized; only the strict bound 21/20 that the claim uses
is. The explicit policies are the paper's own: cash throughout; root (7/15, 8/15)/(101/100) with
the losing ETF sold under theta_+; and cash at the root, then buying the revealed winner.

Relation to the prose. The mechanism narrative in part 6 is explanation and has no formal
counterpart. No gap was found between the formal statement and the Statement. The limits PM
recorded at approval apply unchanged. Alpha is known zero. The return law is degenerate with full
revelation, so magnitudes are not meaningful. Uniformity is proved over the cost box only; the
formal result is exactly that box.

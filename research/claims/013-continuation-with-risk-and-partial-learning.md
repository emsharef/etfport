---
id: 13
title: "Opposite continuation effects persist with conditional risk, partial learning and uncertain alpha"
status: formalized
model_version: M3
depends_on: [11, 12]
axioms_used: []
formal: lean/Standalone/ContinuationRobustness.lean
direction: D2
---
## Statement

Fix any delta in (0,1/1000]. Use the following assumed M3 family, extending claim 012.
Initially W_0^-=h_0^-=1 and both risky holdings are zero. There is one active fund and
one ETF, B^A=(1,0), B^E=(0,1), c^E=0, and rho=20. The four parameters

```
theta_{sigma,xi}=(sigma/2,-sigma/2,xi delta),   sigma,xi in {-1,1},
```

have prior mass 1/4 each and remain fixed for both quarters. There are four equally
likely scenarios indexed by independent signs (s_A,s_E), with
z^f=(0,0), z^A=delta s_A and z^E=delta s_E. Quarterly scenarios are independent
conditional on theta, with this same law. Thus gross returns in each quarter are

```
g_A=1+sigma/2+delta(xi+s_A),    g_E=1-sigma/2+delta s_E.
```

Each of the four directional shareholder rates is any number in [0,1/100], fixed
over the two reviews, independently of the other rates. All other M3 funding,
observation, information, control and terminal-marking rules apply without change.

This family has all three properties absent from claim 012's instance:

1. Conditional on each theta, the risky-return covariance matrix is delta^2 I_2,
   so both conditional variances are strictly positive and the matrix is positive
   definite. Every specified gross return is strictly positive.
2. Alpha takes the two nonzero values -delta and delta with equal prior probability,
   independently of the factor-premium regime sigma.
3. At first-review observations with r_A-lambda_1=0, the posterior puts mass 1/2 on
   each of the two possible alpha values. This event has probability 1/2. Factor
   premia are revealed, but the full parameter is not always revealed.

For every delta and every cost vector in these ranges, the optimized M3 gaps satisfy

```
0 <= Delta_N <= 1/4+delta^2,
Delta_E > 2129/8080-9 delta-delta^2,
0 <= Delta_F <= 3/202+(402/101)delta.
```

In particular,

```
Delta_E-Delta_N > 1/250 > 0,
Delta_F-Delta_E < -23/100 < 0.
```

These are certainty-equivalent fractions of initial wealth, not expected returns.
Every full-root optimizer with future ETF-only control buys a strictly positive
active holding. No uniqueness or zero root gap under future full trading is asserted.

## Proof

The proof bounds every competing policy and supplies feasible observable policies.
It does not assume that optimal policies or posterior partitions vary continuously
with delta. Claim 011 gives attainment and nested-value orders. The funded witness
from the reviewed claim 012 motivates the construction, but all required bounds are
derived below for this family.

### 1. Admissibility, risk and the posterior

The shocks have zero means and independent signs. Given theta, their only random
risky-return components are delta s_A and delta s_E, giving covariance delta^2 I_2.
The smallest gross return is at least 1/2-2 delta>=249/500>0. The fixed costs lie
below one. Thus these are M3 inputs, including independent quarterly shock draws;
shared theta makes the two quarters dependent before conditioning.

Public f=(sigma/2,-sigma/2) identifies sigma. The ETF return identifies s_E, and
the remaining active observation is delta(xi+s_A). When that equals zero, the two
possibilities are (xi,s_A)=(1,-1) and (-1,1). They have equal prior joint masses,
and the ETF sign is independent of them. Bayes' rule therefore assigns posterior
mass 1/2 to each theta with that sigma. The two cancelling sign pairs have total
probability 1/2. More explicitly, for each fixed sigma and ETF sign the ambiguous
observation has mass 1/8; there are four such observations. The other eight
observations each have mass 1/16 and reveal alpha. There are twelve positive-mass
observations in total. No policy below uses the unobserved alpha or next shock.

### 2. Utility bounds used throughout

For any policy define CE(policy)=-(1/20)ln E[exp(-20 W_2)]. If W_2>=L on every
path, then CE(policy)>=L. Also CE(policy)<=E[W_2]: writing m=E[W_2], the elementary
inequality exp(x)>=1+x gives

```
E[exp(-20 W_2)]
 = exp(-20m) E[exp(-20(W_2-m))] >= exp(-20m).
```

For any constant b, CE(W_2+b)=CE(W_2)+b. All sums are finite, and these bounds
hold for optimized values whenever their hypotheses hold for all policies.

We will use ln(2)<3/4. For x>0, exp(x)>1+x+x^2/2: subtract the quadratic,
differentiate twice, and use exp(x)-1>0 and zero value and first derivative at
zero. At x=3/4 the quadratic equals 65/32>2. Monotonicity of ln proves the bound.

Write a,p,h for post-root active dollars, ETF dollars and cash. Under either root
class, funding gives a,p,h>=0 and a+p+h<=1. They are chosen before theta is observed.

### 3. Disabled second review

With no second trade, terminal wealth is h+a g_A^0 g_A^1+p g_E^0 g_E^1.
Conditional independence of the two shock draws gives

```
E[g_A^0 g_A^1 | sigma,xi]=(1+sigma/2+xi delta)^2,
E[g_E^0 g_E^1 | sigma,xi]=(1-sigma/2)^2.
```

The independent, symmetric prior on sigma and xi therefore gives
E[g_A^0 g_A^1]=5/4+delta^2 and E[g_E^0 g_E^1]=5/4. In particular, the extra
delta^2 term is the effect of the persistent uncertain alpha, not an extra
variance penalty appended to utility. Hence CE_{F,N}<=5/4+delta^2 by part 2 and
funding. Root cash held throughout gives CE_{E,N}>=1, proving the stated bound
on Delta_N. Its nonnegativity follows from nesting.

### 4. Upper bound with ETF-only controls at both reviews

Here a=0, 0<=p<=1 and h<=1-p. Let e=3 delta+delta^2 for this paragraph.
In regime sigma=1, every ETF gross return is below one, so terminal wealth under
any funded E continuation is at most the marked wealth

```
h+p(1/2+delta) <= 1-p/2+delta p <= 1-p/2+e.
```

In regime sigma=-1, every ETF gross return is at most 3/2+delta. Nonnegative
fees and long-only funding imply the pathwise upper bound

```
(3/2+delta)[h+p(3/2+delta)]
 <= 3/2+3p/4+delta(1+2p)+delta^2 p
 <= 3/2+3p/4+e.
```

These remain upper bounds even when the node action depends on all available
observations. The two regimes have equal probability. After removing the common
upper shift e, expected utility is bounded by

```
f(p)=-[exp(-20(1-p/2))+exp(-20(3/2+3p/4))]/2.
```

As in the explicit calculation of claim 012, f''<0 and
f'(0)=10[-exp(-20)/2+3 exp(-30)/4]<0 since exp(10)>3/2. Thus f(p)<=f(0).
Monotonicity of the CE transform, the shift identity and part 2 give

```
CE_{E,E} <= 1+[ln(2)-ln(1+exp(-10))]/20+3 delta+delta^2
          < 83/80+3 delta+delta^2.
```

### 5. A full-root policy with future ETF adjustment

Put epsilon=1/100 and buy

```
a=(7/15)/(1+epsilon),    p=(8/15)/(1+epsilon).
```

The root fee is at most epsilon(a+p), so exact remaining cash h is nonnegative.
After observing sigma=1, sell all marked ETF dollars; after observing sigma=-1,
make no trade. Never change the active holding at the second review. These are
observable E actions regardless of the posterior over alpha, and ETF sale proceeds
net of fees are nonnegative.

In regime sigma=1, using lower bounds on both quarterly active returns and on
the ETF's first return,

```
W_2 >= h+a(3/2-2 delta)^2+(1-epsilon)p(1/2-delta)
    >= (9/4)a+(1-epsilon)p/2-6 delta a-delta p
    >= 657/505-6 delta.
```

Here a+p=1/(1+epsilon)<=1, and
(9/4)a+(1-epsilon)p/2=[79/60-(4/15)epsilon]/(1+epsilon)=657/505.
In regime sigma=-1, with no trade,

```
W_2 >= h+a(1/2-2 delta)^2+p(3/2-delta)^2
    >= a/4+(9/4)p-2 delta a-3 delta p
    >= [79/60]/(1+epsilon)-3 delta
    >= 657/505-6 delta.
```

These inequalities are pathwise and do not replace unknown future returns by
their posterior means. Thus CE_{F,E}>=657/505-6 delta, and part 4 yields

```
Delta_E > 657/505-83/80-9 delta-delta^2
        = 2129/8080-9 delta-delta^2.
```

### 6. Full future trading

Each instrument's first-quarter prior mean gross return is one, so the expected
marked wealth after any root action is h+a+p<=1. Every possible second-quarter
gross return is at most 3/2+2 delta. Trading only reduces wealth; therefore every
full policy has E[W_2]<=3/2+2 delta and CE_{F,F}<=3/2+2 delta.

An E-root policy can keep cash until review 1 and then buy only the active fund
if sigma=1, or only the ETF if sigma=-1. This is permitted under F continuation
and uses public sigma, not the unresolved alpha. Spending all cash including the
purchase fee gives terminal wealth at least

```
(3/2-2 delta)/(1+epsilon).
```

So CE_{E,F} is at least this amount. Subtraction gives

```
0 <= Delta_F <= 3/2+2 delta-(3/2-2 delta)/(1+epsilon)
             = 3/202+(402/101)delta.
```

### 7. Uniform signs and active purchase

Subtract the preceding bounds. Since delta<=1/1000 and all error coefficients
are nonnegative,

```
Delta_E-Delta_N
 > 2129/8080-1/4-9 delta-2 delta^2
 >= 226649/50500000 > 1/250,

Delta_F-Delta_E
 < 3/202-2129/8080+(1311/101)delta+delta^2
 <= -23801399/101000000 < -23/100.
```

In particular Delta_E>0. By attainment, every full-root optimum under E must
have nonzero active trade; otherwise it would also be an E-root policy. Initial
active holdings are zero and shorting is prohibited, so this trade is a purchase.

## Checks

`checks/013/check.py` constructs the four-parameter, four-scenario M3 law from
the displayed primitives. With exact fractions it checks positive returns,
conditional covariance, the twelve public observations and their posteriors,
the persistent-alpha product moment, the two funded policies on every hidden
two-quarter path at all cost-box vertices, and the final rational margins. It
also solves the six relevant control pairs at delta=1/1000 and common 1% rates,
sharing one continuation action across each observation's hidden histories.
Run `uv run python checks/013/check.py`. These are fixed checks, not a numerical
proof for all real delta and cost vectors; that proof is above.

## Not shown

- The magnitudes are not calibrated or economically representative. The opposing
  factor premia are still +/-50% per quarter, rho=20 is assumed, and alpha and
  shocks are bounded by 0.1% in absolute value. This establishes existence with
  nonzero risk and uncertainty, not material uncertainty or a realistic market.
- Factor premia are exactly revealed. Partial learning here concerns alpha only,
  on an event of probability 1/2; it does not establish robustness to imprecise
  observation of the factors or to uncertain exposure loadings.
  Both witness policies use only the revealed regime sigma and ignore the
  posterior over alpha. Partial learning is present in the family, but the
  proof does not identify a contribution from unresolved alpha to either sign.
- In either regime the identified higher-return instrument still has a known
  strictly positive excess return on every remaining path. Its payoff varies,
  but buying it produces a sure positive gain even after the allowed purchase
  charges. Borrowing is prohibited. No arbitrage-free interpretation is claimed.
- The active fund remains the only vehicle for factor 1. Uncertain nonzero alpha
  is now present and sometimes unresolved, but the mechanism is still dominated
  by the unspanned factor exposure. This is not proof of an alpha-driven effect.
- The law couples the alpha-support spacing to the residual-shock spacing so
  that observations overlap. Robustness to arbitrary perturbations of that
  information structure is not established. No differentiability of optimized
  values across delta=0 is asserted; the observation partition changes there.
- Conditional realized-return covariance, uncertainty about fixed means, and
  ambiguity aversion remain distinct: the first is delta^2 I_2, the second is
  the specified prior and posterior, and no ambiguity preference is imposed.
- These signs do not imply exact optimizer magnitudes, uniqueness, Delta_F=0,
  a general scalar threshold, or a cash-endowment comparative static. The same
  funded budget, information and return law are used across each matched control.
  There is no terminal liquidation or extra position cap.

## Prior art

Checked claim 012, its red review, the D2 entries in board/FINDINGS.md, the
refuted-claim directory, and the existing experiment 007 and M3 definition-check
scope. Red's instance A already supplies numerical evidence with conditional
shocks and partial learning. The added result is a uniform paper proof for an
explicit noisy, uncertain-alpha family, not the first observation of the signs.

The registered full-text comparisons in claim 012 remain applicable:
`dai2011illiquidity` studies anticipation of binding position limits under known
diffusion parameters, while `liu2013portfolio` studies the effect of a binding
constraint and small transaction costs on a long-run no-trade region. Neither
stated result supplies the two matched continuation contributions with the
posterior overlap exhibited here. This is robustness of the same finite
counterexample, not a new mechanism or a claim of broad priority. No literature
result is imported into the proof.

## Open objections

None yet; independent red review pending.

## Review

**Red, 2026-09-27.** I checked every bound by hand, solved the family independently, and probed the claim's scope.

**Hand check: every bound holds.**
- *Returns and properties 1-3.* The gross returns are g_A = 1 + sigma/2 + delta(xi + s_A) and g_E = 1 - sigma/2 + delta s_E, all at least 1/2 - 2 delta > 0. The conditional covariance is delta^2 I_2. Public f reveals sigma and the ETF return reveals s_E. The active residual delta(xi + s_A) is ambiguous exactly when it is zero, with (xi, s_A) = (1, -1) or (-1, 1) and posterior 1/2 on each. That gives 12 positive-mass observations: 4 ambiguous of mass 1/8, total 1/2, and 8 revealing of mass 1/16.
- *Part 2.* CE <= E[W_2] by Jensen, and the shift identity holds. e^{3/4} > 65/32 > 2 gives ln 2 < 3/4.
- *Part 3.* E[(1 + sigma/2 + xi delta)^2] = 5/4 + delta^2, since the cross term vanishes because xi is independent of sigma. For the ETF, E[(1 - sigma/2)^2] = 5/4. So Delta_N <= 1/4 + delta^2.
- *Part 4.* With sigma = 1, the ETF gross return is below 1 and terminal wealth is at most 1 - p/2 + delta p. With sigma = -1, (3/2 + delta)(1 + p/2 + delta p) = 3/2 + 3p/4 + delta(1 + 2p) + delta^2 p. Both are at most the claim's bounds with e = 3 delta + delta^2. The pathwise bounds turn into an expected-utility bound through e^{-20e} f(p). This gives CE_{E,E} < 1 + 3/80 + e = 83/80 + 3 delta + delta^2.
- *Part 5.* (3/2 - 2 delta)^2 >= 9/4 - 6 delta, (1/2 - 2 delta)^2 >= 1/4 - 2 delta and (3/2 - delta)^2 >= 9/4 - 3 delta. With a + p <= 1 this gives 657/505 - 6 delta in both regimes, and 657/505 - 83/80 = (10512 - 8383)/8080 = 2129/8080.
- *Part 6.* Both first-quarter prior mean gross returns equal 1, and second-quarter gross returns are at most 3/2 + 2 delta. The waiting policy gives (3/2 - 2 delta)/1.01, so the Delta_F bound is 3/202 + (402/101) delta.
- *Part 7.* The margin 109/8080 - 9 delta - 2 delta^2 is decreasing in delta, and at delta = 1/1000 it equals 226649/50500000 > 1/250. The expression -2009/8080 + (1311/101) delta + delta^2 is increasing, and at delta = 1/1000 it equals -23801399/101000000 < -23/100. The active-purchase conclusion follows from Delta_E > 0 and claim 011's attainment.
- *Witness policies.* Both use only sigma, which is public, never the unresolved alpha. Sale proceeds are net of kappa^-.

**Independent checks** (floating CLARABEL, not certificates).
- *Bayes structure.* I built the family from the Statement's primitives. Exact Bayes gives 12 positive-mass observations, 4 of them ambiguous with mass 1/8, posteriors 1/2 and total probability 1/2.
- *Bounds.* I solved the six relevant (D, R) cells with red's joint M3 program at delta = 1/1000 and 1/4000. At both, I used all 16 vertices of the rate box and 4 random interior rate vectors: 40 solved points and no violations of the three stated bounds at tolerance 1e-4. The F-root optimum under E_1 buys about 0.465 of active.
- *Zero fees, delta = 1/1000.* Delta_N = 0.2484, Delta_E = 0.2821 and Delta_F = 0 within solver error. The channels are +0.0337 and -0.2821.
- *Claim's own check.* `checks/013/check.py` passes.

**Attacks that did not succeed.**
- Witness policies using hidden alpha or shocks: they use sigma only.
- Posterior means substituted for returns: all bounds are pathwise.
- Unfunded or shorting trades.
- A hidden cost ranking: the full rate box is covered.
- Existence read as uniqueness.

**Scope (sharpenings).**
1. **The proved family is a small perturbation of claim 012.** With delta <= 1/1000, alpha and conditional shocks are at most 0.1% per quarter against factor premia of plus or minus 50%. The margins 1/250 and -23/100 are claim 012's slack less O(delta). So the proof establishes that claim 012's signs are not knife-edge in the absence of risk; it does not establish them under material risk. The title's "persist" should be read that way, and the Not shown says so.
2. **Numerically, the signs survive far outside the proved range.** This is a fragility probe, not a proof. Solving the same family at delta = 1/100, 1/20, 1/10 and 1/5, each at zero rates and at all rates 1%:
   - the ETF channel is +0.031 to +0.079;
   - the active channel is -0.077 to -0.280;
   - at delta = 1/5 (alpha and shocks of plus or minus 20% per quarter) they are still +0.079 and -0.081.

   The restriction delta <= 1/1000 is a feature of the proof, not where the effect stops in this family.
3. **Partial learning does no work in the mechanism.** The unresolved alpha is too small to matter, and both witness policies ignore it. Only sigma, which is fully revealed, drives the signs. As with claim 012, the active fund is the only factor-1 vehicle, so this is still the unspanned-exposure channel, not an alpha-driven effect. The Not shown's fourth bullet states this correctly.

**Red mechanism check (agents/red.md 4b), 2026-09-28.** This check was done independently of the librarian's "Mechanism audit: claims 001-018", which was not yet on main when it was written. It will be reconciled when that entry merges. The general result is stated in self-contained form, so the reduction can be checked without the source. Literature names are pointers for the librarian to register; no theorem numbers are asserted, and no status changes.
- *Mechanism.* That of claim 012, persisting under small perturbations of the return law and beliefs.
- *General result.* Claim 012's known mechanisms, plus continuity of optimal values under small data perturbations (Berge's maximum theorem). The claim proves explicit O(delta) margins instead of appealing to continuity.
- *Reduction.* The family is claim 012's, with delta-sized alpha and shocks, and the bounds are claim 012's slack less O(delta).
- *Verdict: partial overlap,* exactly as for claim 012. Left over: the explicit margins.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's hand check of every bound (returns, Bayes structure with 4 ambiguous observations of total mass 1/2, Jensen and pathwise bounds, margins at delta=1/1000), independent solve at 40 cost-box points for two deltas and attacks (hidden alpha in witnesses, posterior-mean substitution, unfunded trades, disguised cost ranking, existence as uniqueness) are sound, and PM reran checks/013; no open objections. Limits stated: a small perturbation of claim 012 (alpha and shocks at most 0.1% per quarter against +-50% premia), so it shows the signs are not a zero-risk knife-edge, not that they hold under material risk (red finds them numerically to delta=1/5, unproved); partial learning does no work in the mechanism, which remains the unspanned-factor channel, not alpha.


Not machine checked. A faithful formal counterpart needs the actual four-state
prior and four-scenario law, the nontrivial Bayes calculation, the positive
conditional covariance, pathwise funding bounds, finite expected-utility upper
bounds and CE inequalities. Rational margins alone would be strictly weaker.
The uniform utility bounds must be proved, not supplied as hypothesis fields.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/ContinuationRobustness.lean` and the
proof in `lean/Novel/ContinuationRobustnessProof.lean`. `lake build` and the axiom audit pass
(standard axioms only). No hypothesis structure or cited result is used, and no utility bound is a
hypothesis field.

The family. It is built on claim 011's formal M3 objects (Pol, Phi, V, CE, Delta, obs, P0, post).
The data are entered literally:
- four parameters (sigma, xi) with prior 1/4 each and theta = (sigma/2, -sigma/2, xi delta);
- four scenarios (s_A, s_E) with mass 1/4 each, and shocks z^f = 0, z^A = delta s_A, z^E = delta s_E;
- loadings (1, 0) and (0, 1), zero drag, rho = 20, zero initial risky holdings and cash one;
- the four rates as free parameters.
Every part is quantified over all delta in (0, 1/1000] and all rates in [0, 1/100]^4.

Proved:
1. Every member satisfies M3's restrictions and every gross return is strictly positive. Claim
   003's return covariance equals delta^2 I_2 and is positive definite. That covariance comes from
   the scenario shocks alone, because theta shifts only the means, so it is the conditional
   covariance for every theta.
2. alpha = xi delta with delta != 0, and the prior of each (sigma, xi) is 1/2 * 1/2 (equal masses,
   and alpha independent of sigma).
3. This is keyed on the observation, not on the latent path. At every first-review observation
   with r_A - f_1 = 0 (the prose's r_A - lambda_1), the observation has probability 1/8 and the
   posterior puts 1/2 on each alpha value for the revealed sigma. The event r_A - f_1 = 0 has
   probability 1/2. The proof shows r_A - f_1 = delta(xi + s_A) and that two paths give the same
   observation exactly when they share sigma, s_E and xi + s_A.
4. The three gap bounds with the stated constants, and the two sign margins 1/250 and -23/100.
5. Every full-root optimum with future ETF-only control has a positive root active trade.

The proof. It imports claim 011's proof module (attainment, V < 0, class and CE orders; Q-04) and
claim 012's `exp_facts`. The certainty-equivalent lemmas of claim 012 are reproved for any M3
instance with rho = 20 and W_0^- = 1 over the nested prior/scenario/scenario sum, with Jensen for
exp at each level. Each gap bound comes from a pathwise terminal-wealth bound on the paper's
explicit policies:
- cash only (W_2 = 1);
- the root (7/15, 8/15)/(101/100), with the node selling the whole ETF position when sigma = +1
  (W_2 >= 657/505 - 6 delta);
- cash at the root, then buying the revealed regime's winning fund with all cash
  (W_2 >= (100/101)(3/2 - 2 delta)).
Both node rules read only the public sigma, as red noted. The two upper bounds on means are
CE_{F,N} <= 5/4 + delta^2 (exact mean of the no-trade wealth) and CE_{F,F} <= 3/2 + 2 delta. The
CE_{E,E} bound uses the paper's pathwise regime bounds 1 - p/2 + e and 3/2 + 3p/4 + e. It then
replaces the paper's f(p) <= f(0) and ln 2 - ln(1 + e^{-10}) step with a cruder margin: claim
012's bracket exp(-20) < exp(-20(1 - p/2)) + exp(-20(3/2 + 3p/4)) together with exp(3/4) >= 2.
That gives CE_{E,E} < 83/80 + 3 delta + delta^2 directly; the paper's intermediate closed form is
not formalized. Active purchase is claim 012's argument: a zero active root lies in Pi_{E,E}, so
Delta_E <= 0, which contradicts part 4.

Relation to the prose. No gap was found between the formal statement and the Statement. The
limits PM recorded at approval apply unchanged. This is a small perturbation of claim 012 (alpha
and shocks at most 0.1% per quarter against +-50% premia). It shows the signs are not a zero-risk
knife-edge, not that they hold under material risk; red's evidence to delta = 1/5 is numerical and
has no formal counterpart. Partial learning is present in the family (part 3 above), but no formal
statement attributes either sign to unresolved alpha. The mechanism remains the unspanned-factor
channel, not alpha. Uniformity is proved over the stated delta and rate ranges only; the formal
result is exactly those ranges.

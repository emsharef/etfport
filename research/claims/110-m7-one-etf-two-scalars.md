---
id: 110
title: "One ETF and any number of funds, with the ETF at zero or costly, fees on and a possibly binding budget: the whole optimum is decided by two scalars, the exposure price (the ETF's factor marginal) and the cash price, each the root of a monotone piecewise-linear equation in the inputs; every fund's trade is its one-fund clip at those two prices; and the ETF's status (at zero, bought, sold, idle) is read by comparing the idle exposure price with the ETF's scaled cost band"
status: formalized
model_version: M7
depends_on: [040, 102, 109]
axioms_used: [AX-13]
formal: lean/Standalone/M7OneEtfTwoScalars.lean
direction: D15f
---
## Statement

D15f's second claim. Claim 109 gives the criterion and, given the ETFs' statuses, the explicit
forms; with several ETFs the statuses are decided by a finite complementarity. With one ETF the
whole problem collapses: every fund's marginal depends on the ETF only through one number, the
*exposure price* m (the ETF's factor marginal, the premium net of fee less the risk charge of
the total exposure held), and on the budget only through the cash price eta; given (m, eta) the
funds decouple into one-fund clips, and m and eta are the roots of monotone scalar equations
whose pieces are linear in the inputs. This is the practical rule for a manager with one
broad ETF: it needs no solver, and it says in the inputs which regime the ETF is in.

**Setting.** Claim 109's with M = K = 1 and V diagonal: N funds with holdings x_i in [0, bar x_i],
incumbents x^-_i, rates kappa^+_i, kappa^-_i, net alpha alpha_hat_i, residual variances v_i; one
ETF with holding p >= 0 (no cap), incumbent p^-, rates kappa^+_E, kappa^-_E, fee c^E, factor
loading b_E > 0, premium belief lambda_hat and predictive factor variance sigma~_f, residual
variance sigma_E (zero in parts 1-4); gamma; the funded budget k(x) = h^- - 1'(x - x^-) - C(x - x^-) >= 0
with h^- > 0 and multiplier eta. Write

```
r_i = b_{A,i}/b_E   (fund i's netting weight),   q = sum_i r_i x_i   (the funds' by-product),   w = p + q   (the total exposure in ETF units),
mu_E = b_E lambda_hat - c^E,   sigma_EE = b_E^2 sigma~_f,   alpha~_i = alpha_hat_i + r_i c^E,
m(w) = mu_E - gamma sigma_EE w                       (the exposure price at exposure w),   w(m) = (mu_E - m)/(gamma sigma_EE),
theta_b(eta) = eta + (1 + eta) kappa^+_E,   theta_s(eta) = eta - (1 + eta) kappa^-_E     (the ETF's scaled purchase and sale thresholds),
```

and the one-fund clip at prices (m, eta)

```
x_i(m, eta) = clip( x^-_i, lo_i(m, eta), hi_i(m, eta) ) clipped to [0, bar x_i],
lo_i(m, eta) = [ alpha~_i + r_i m - eta - (1 + eta) kappa^+_i ]/(gamma v_i),   hi_i(m, eta) = [ alpha~_i + r_i m - eta + (1 + eta) kappa^-_i ]/(gamma v_i),
q(m, eta) = sum_i r_i x_i(m, eta),     p(m, eta) = w(m) - q(m, eta).
```

### Part 1. Every fund sees the ETF through one price

At the optimum x* with multiplier eta* and exposure price m* = m(w*), every fund's smooth
marginal is

```
g_i(x*) = alpha~_i + r_i m* - gamma v_i x*_i,
```

so x*_i = x_i(m*, eta*): each fund's trade is its own one-fund band decision (claim 102's part
3 form) with the ETF's factor marginal added at the fund's netting weight and the budget's
shadow price and scaling. The funds interact with each other and with the ETF only through m*
and eta*. The map m -> r_i x_i(m, eta) is nondecreasing, so q(m, eta) is nondecreasing in m,
piecewise linear with finitely many pieces and bounded; x_i(m, eta) is nonincreasing in eta
(kappa^-_i < 1); and p(m, eta) is strictly decreasing in m.

### Part 2. The ETF's status and the exposure price, given the cash price (sigma_E = 0)

Fix eta >= 0. Define the *at-zero candidate* m_0(eta), the unique root of p(m, eta) = 0 (the
exposure price when the ETF holds nothing and the funds' by-product is the whole exposure),
and, when p^- > 0, the *idle candidate* m_I(eta), the unique root of p(m, eta) = p^- (the
exposure price when the ETF stays at its incumbent). Then at the optimum for this eta:

```
p^- > 0:   bought  iff  m_I > theta_b,        then  m* = theta_b,   p* = p(theta_b, eta) > p^-;
           idle    iff  theta_s <= m_I <= theta_b,   then  m* = m_I,   p* = p^-;
           sold    iff  m_I < theta_s:   to p* = p(theta_s, eta) > 0 with m* = theta_s if m_0 > theta_s,
                                          to zero with m* = m_0 if m_0 <= theta_s;
p^- = 0:   at zero iff  m_0 <= theta_b,      then  m* = m_0,   p* = 0;
           bought  iff  m_0 > theta_b,       then  m* = theta_b,   p* = p(theta_b, eta) > 0;
```

and in every case x*_i = x_i(m*, eta). In words: the ETF is bought iff the exposure price at
which it would stay put, after the funds have responded to that price, exceeds its scaled
purchase threshold; it is sold iff that price falls below its scaled sale threshold, and sold
out when even the exposure the funds alone would carry prices the factor below that threshold.
When the ETF trades, m* is pinned at a threshold and the funds decouple completely (claim 109's
part 3 traded form: own curvature, the ETF's pinned slope at weight r_i, net cash 1 - r_i); when
it is fixed, m* is the fixed point of the funds' by-product (claim 109's fixed form: curvature
v_i + r_i^2 sigma_EE and coupling r_i r_j sigma_EE, resolved by the one scalar m*).

### Part 3. The cash price

The cash slack of the part 2 solution, k(x(eta)), is nondecreasing in eta. The optimum's
multiplier is eta* = 0 if k(x(0)) >= 0, and otherwise any eta > 0 with k(x(eta)) = 0, which
exists; every such eta gives the same holdings. So eta* is found by one monotone scalar
search, inside which m* is found by another, and both are exact on the finitely many linear
pieces of q.

### Part 4. Readings

(a) *Direction from the incumbent.* At the optimum's prices, fund i is bought iff
alpha~_i + r_i m* - gamma v_i x^-_i > eta* + (1 + eta*) kappa^+_i and x^-_i < bar x_i, sold iff
alpha~_i + r_i m* - gamma v_i x^-_i < eta* - (1 + eta*) kappa^-_i and x^-_i > 0, held otherwise:
claim 102's part 3 rule with the exposure price added, exact for every N (claim 040's part 3
caveat, that funds interact through the by-product's risk charge, is absorbed by m*).
(b) *Comparative statics in the price.* A higher exposure price (a larger premium net of fee,
or less exposure already held) raises the holdings of positively loaded funds and lowers those
of negatively loaded ones, by at most |r_i|/(gamma v_i) per unit of price on a fund's trading
piece; at a fixed exposure price, a higher cash price lowers every holding.
(c) *Against the benchmark.* Claim 109's criterion (the composition) says which slacks, slopes
and cash terms enter; it does not say which regime holds or how the funds' responses feed back
into the ETF's decision. Here the regime is decided by two roots in the inputs, and the
feedback is the single number m*: the manager computes m_0 and m_I from the inputs (finitely
many linear pieces), reads the ETF's status off the thresholds, and clips every fund. Claim
040's part 5(a) (frictionless, slack budget) is the case theta_b = theta_s = 0.

### Part 5. ETF residual risk

With sigma_E > 0 the funds' identity of part 1 holds unchanged (m* defined as before), and
the ETF's own marginal is m* - gamma sigma_E p*. Part 2 holds with the ETF's marginal in place
of m in the status tests (m_I - gamma sigma_E p^- against the thresholds; m_0 unchanged since
p = 0 there) and, in the traded regimes, with m* the unique root of
m - gamma sigma_E p(m, eta) = theta (theta = theta_b or theta_s) in place of the pinned value;
part 3 is unchanged.

**One sentence without model nouns.** With one hedging instrument, every position's decision
is its own band at two prices, the instrument's marginal value of exposure and the price of
cash; the instrument's own decision compares the exposure price at which it would stay put,
after the positions have responded to that price, with its cost band; and both prices are roots
of monotone equations with finitely many linear pieces in the inputs.

## Proof

### 1. One price

Claim 109's part 1 with M = 1 (claim 102's part 1 criterion, AX-13, and the identity
g_i = A_i + r_i g_E) gives g_i = alpha~_i - gamma v_i x_i + gamma r_i sigma_E p + r_i g_E with
g_E = mu_E - gamma sigma_EE w - gamma sigma_E p, so the sigma_E terms cancel and
g_i = alpha~_i + r_i m(w) - gamma v_i x_i. The fund's own line g_i = eta + (1 + eta) t_i with the
box signs is, for fixed (m, eta), claim 102's part 3 one-fund problem with target
(alpha~_i + r_i m - eta)/(gamma v_i) and rates (1 + eta) kappa^{+-}_i, whose solution is the clip
x_i(m, eta) (claim 029's 1a at T-1). Monotonicity: lo_i and hi_i are affine in m with slope
r_i/(gamma v_i), so x_i is nondecreasing in m when r_i > 0, nonincreasing when r_i < 0, and
r_i x_i nondecreasing in both cases; lo_i and hi_i have slope -(1 + kappa^+_i)/(gamma v_i) and
-(1 - kappa^-_i)/(gamma v_i) < 0 in eta, so x_i is nonincreasing in eta. q is a finite sum of
clips of affine functions: piecewise linear, bounded by sum_i |r_i| bar x_i. w(m) is strictly
decreasing, so p(m, eta) = w(m) - q(m, eta) is strictly decreasing in m, from +infinity to
-infinity; hence the roots m_0 and m_I of part 2 exist and are unique.

### 2. The ETF's status

Fix eta. The optimum is unique, and by claim 109's part 1 it is characterized by: the funds'
lines (x_i = x_i(m*, eta) with m* = m(w*), part 1), the ETF's line
m* = eta + (1 + eta) t_E - zeta, t_E in T_E(x*), zeta >= 0 only at p* = 0, and p* = w(m*) - q(m*, eta) = p(m*, eta).
Conversely any (m, p) satisfying these with the clips is the optimum. Case p^- > 0.
- If m_I > theta_b: take m* = theta_b, p* = p(theta_b, eta). Since p(., eta) is strictly
  decreasing and p(m_I, eta) = p^-, p* > p^- > 0: the ETF is bought, t_E = kappa^+_E, and the
  ETF's line holds with zeta = 0. Conversely if the ETF is bought then m* = theta_b and
  p(theta_b, eta) > p^- = p(m_I, eta) forces theta_b < m_I.
- If theta_s <= m_I <= theta_b: take m* = m_I, p* = p^-: the ETF is untraded and its marginal
  m_I lies in [theta_s, theta_b] = eta + (1 + eta) T_E, so the line holds. Conversely an idle
  ETF has p* = p^-, hence m* = m_I, and its line puts m_I in the band.
- If m_I < theta_s: the ETF is sold (the other two regimes are excluded by the converses). If
  m_0 > theta_s, take m* = theta_s and p* = p(theta_s, eta), which lies strictly between
  p(m_0) = 0 and p(m_I) = p^-: an interior sale, t_E = -kappa^-_E, zeta = 0. If m_0 <= theta_s,
  take m* = m_0, p* = 0: the ETF is sold to zero, t_E = -kappa^-_E, and the line holds with
  zeta = theta_s - m_0 >= 0. The two sub-cases are exclusive and exhaustive, and each converse
  follows from the monotonicity of p(., eta) as above.
Case p^- = 0: the ETF is at zero or bought. At zero means p* = 0, m* = m_0 and the line
m_0 <= theta_b (t_E = kappa^+_E, zeta >= 0); bought means m* = theta_b with p* = p(theta_b, eta) > 0 = p(m_0, eta),
hence theta_b < m_0. The two are exclusive and exhaustive.

### 3. The cash price

Let L(x, eta) = Q(x) + eta k(x), concave in x (Q strictly concave, k concave), and x(eta) its
maximizer over the box and p >= 0, which is the part 1-2 solution (claim 102's part 1 with eta
given is the maximizer's characterization). For eta_1 < eta_2, L(x(eta_1), eta_1) >= L(x(eta_2), eta_1)
and L(x(eta_2), eta_2) >= L(x(eta_1), eta_2); adding, (eta_2 - eta_1)(k(x(eta_2)) - k(x(eta_1))) >= 0,
so k(x(eta)) is nondecreasing. The constrained optimum x* has a multiplier eta* >= 0 with
eta* k(x*) = 0 (claim 102's part 1; x^- is a Slater point since h^- > 0), and x* = x(eta*): if
k(x(0)) >= 0 then x(0) is feasible and optimal, eta* = 0; otherwise eta* > 0 and k(x(eta*)) = 0.
Any eta with k(x(eta)) = 0 makes x(eta) feasible with a valid multiplier, hence x(eta) = x*.

### 4. Readings

(a) is part 1's clip read at x^-_i. (b): on a piece where x_i is interior and trading,
x_i = lo_i or hi_i, affine in m with slope r_i/(gamma v_i), and the clips are nondecreasing
functions of lo_i, hi_i; the eta statement is part 1's. (c) is a comparison, not a theorem;
claim 040's 5(a) is the case kappa_E = 0, eta = 0, where theta_b = theta_s = 0 and "at zero iff
mu_E <= gamma sigma_EE q" is m_0 <= 0.

### 5. Residual risk

Part 1's cancellation holds for any sigma_E. The ETF's line is m - gamma sigma_E p = eta + (1 + eta) t_E - zeta;
with p = p(m, eta) strictly decreasing in m, the map m -> m - gamma sigma_E p(m, eta) is strictly
increasing, so each traded regime's equation has a unique root, and the case analysis of part
2 goes through with the ETF's marginal m - gamma sigma_E p in place of m at the incumbent
(idle) and at zero (where it is m_0).

## Checks

`uv run python checks/110/check.py` (exits non-zero on failure; a check, not a proof). Random
one-review instances (2-5 funds, one ETF; random loadings, beliefs with the premium sometimes
negative, fees, ETF rates up to 20 bp or 60 bp, fund rates up to 100 bp, the ETF starting at
zero on about half, the budget tight on half, ETF residual risk on a third; all assumed): the
claim's rule (bisection on m per regime, then on eta, 70 steps each) is compared with
cvxpy/CLARABEL on the joint problem. On 360 instances the holdings agree to 1.5e-3 (grid of
the solver's tolerance), the exposure price to 5e-4, the ETF's status is read correctly in
every case (216 at zero, 74 bought, 54 sold, 16 idle; 75 with a binding budget; 120 with
residual risk), every fund's marginal at the solver's optimum equals alpha~_i + r_i m - gamma v_i x_i
to 1e-6, and part 4(a)'s direction from the incumbent holds at 801 fund decisions.

## Not shown

- Several ETFs: the funds see M exposure prices m_j and the statuses are claim 109's finite
  complementarity; a monotone structure in several prices needs a sign pattern (claim 108's
  Not shown) and is not claimed.
- An ETF cap (the mirror of the zero bound).
- The number of linear pieces of q and the exact algebra on each piece (an explicit finite
  computation, not written out).
- Multi-review: one review only; the dynamic version is claim 107-108's territory.
- No calibration or magnitude; the analyst has the rule by note.

## Prior art

Mechanism: with one hedging instrument, partial elimination of every position given the
instrument's marginal reduces a constrained quadratic program with piecewise-linear charges
to a fixed point in one scalar (the instrument's marginal, decreasing in the positions'
response) and one more for the cash constraint, so the whole solution is two monotone scalar
searches and the instrument's regime is read from thresholds on the first scalar.

General results checked: claim 109 (approved): the criterion and the status-wise forms, of
which this is the one-ETF closed form; claim 040 (approved): part 5(a)'s one-ETF at-zero
condition, the frictionless slack-budget case; claim 102 (approved): the one-fund clip and the
budget scaling; claim 029 (formalized): the last-review clip. `liu2013portfolio` (full text):
per-asset no-trade regions under independence, where no exposure price couples the assets;
`jagannathan2003risk` (named): the fold-in, here the scalar m* folding the ETF's bound and
band into every fund's marginal. The monotone-fixed-point structure is elementary (a strictly
decreasing function crossing a nondecreasing one); no general result is cited for it, and the
budget's monotonicity is the two-line exchange argument of part 3. Searched: claims 040, 041,
102, 104, 106, 109; the D15f roadmap entry. No web search. This is a claim because D15f asks
for the decision in the inputs for the practical manager, and the one-ETF case reduces it to
two scalar roots, which no cited claim states.

## Open objections

none

## Review

**Red, 2026-09-29** (on 557fb97e). Red-passed. Red re-derived parts 1-3 and 5 by hand and implemented the claim's rule independently, without reading checks/110. The rule is bisection on the cash price, and inside it the at-zero and idle roots and the traded roots of m - gamma sigma_E p(m, eta) = theta, 200 steps each. Red compared it with its own bp-scaled cvxpy/CLARABEL solve of the joint problem.

**By hand.**
- *Part 1.* With M = 1, g_E = m - gamma sigma_E p, and the identity g_i = A_i + r_i g_E gives g_i = alpha~_i + r_i m - gamma v_i x_i, the sigma_E terms cancelling. At fixed (m, eta) each fund's line is claim 102's part 3 one-fund problem, so x_i(m, eta) is the displayed clip. r_i x_i is nondecreasing in m, so p(m, eta) = w(m) - q(m, eta) is strictly decreasing and the roots m_0 and m_I exist uniquely.
- *Part 2's case analysis* follows from that monotonicity and the ETF's line. A sale to zero has zeta = theta_s - m_0 >= 0.
- *Part 3.*
  - x(eta) maximizes L = Q + eta k: its lines are part 1's at fixed eta.
  - The exchange argument makes k(x(eta)) nondecreasing.
  - When k(x(0)) < 0, a root exists: x(eta) is continuous, and as eta grows it tends to the maximizer of k, the incumbent, where k = h^- > 0.
- *Part 5.* m - gamma sigma_E p(m, eta) is strictly increasing, so each traded regime has a unique root.

**Numerically.** The rule and the solver agree on 400 random instances:
- 2-5 funds; fees; ETF and fund rates; the ETF starting at zero on about half; the budget tight on half (91 binding); ETF residual risk on a third (134);
- every status occurs: 129 at zero, 125 bought, 33 sold, 103 sold to zero, 10 idle.
Holdings agree to 3.7e-9 (median 2e-13), with none beyond 1e-6, and the cash price to 4.8e-12. That is far tighter than the Checks' 1.5e-3, which is the solver tolerance of the claim's own check, not a property of the rule.

**Nit** (not required). Reading 4(b)'s "a higher cash price lowers every holding" is proved at fixed m (x_i is nonincreasing in eta for fixed m). Across the optimum m* moves with eta, so the overall effect on a fund is not signed by the proof. Please say "at a fixed exposure price".

**Mechanism (4b).** Partial elimination given the one ETF's marginal reduces the problem to two monotone scalar roots, with the ETF's regime read off thresholds on the first. It is new in the inputs as the one-ETF closed form of claim 109's criterion.

Verdict: red-passed

## Formalization notes

Approved 2026-09-29 by pm: Red's review is sound: parts 1-3 and 5 re-derived by hand (the sigma_E terms cancel in the fund line, p(m, eta) strictly decreasing so m_0 and m_I are unique, k(x(eta)) nondecreasing by exchange, a traded regime's root unique) and red's independent implementation of the two-scalar rule matches its own joint solve on 400 instances with every status, holdings to 3.7e-9 and the cash price to 4.8e-12; experiment 045 agrees at 600 of 600. Mechanism: partial elimination given one hedge instrument's marginal reduces the problem to two monotone scalar roots, the one-ETF closed form of claim 109, an application. Limit: one ETF; reading 4(b) holds at a fixed exposure price (red's nit, routed).


mathb, 2026-09-29 (red's nit, after approval): 4(b)'s "a higher cash price lowers every
holding" holds at a fixed exposure price m (part 1's monotonicity in eta), and now says so; the
optimum's m* moves with eta too. No result changed.

Not machine checked. Parts 1-3 and 5 are finite convex-analysis statements about one
quadratic program with polyhedral costs and a scalar coupling; part 4 reads them.

Lean, 2026-09-29 (final): parts 1, 2, 3 (without the existence of eta), 4(a)-(b) and 5 are machine
checked. The statement is in `lean/Standalone/M7OneEtfTwoScalars.lean` and the proof in
`lean/Novel/M7OneEtfTwoScalarsProof.lean`.
- Model: the claim's own one-ETF coordinates (`One`): the funds' alpha~_i, r_i, v_i, rates, caps and
  incumbents; the ETF's mu_E, sigma_EE, sigma_E, rates and incumbent, with p >= 0 and no cap; gamma
  and h^-. The objective Q and the budget k are written out in these coordinates. They are not linked
  formally to claim 027's `Data` with a budget (PM's scope note, for the fidelity row).
- Imports: Mathlib only. The one-fund clip and the Lagrangian bound are proved here. AX-13 enters
  only through the paper-level existence of eta (below).
- Checks: `lake build`, the axiom audit (standard axioms only) and `checks/110/check.py` pass.
- Scope: PM confirmed it (lean/claim110-scope-note).

Machine checked:
- Part 1:
  - the clip x_i(m, eta) is the unique maximizer of fund i's one-fund problem at prices (m, eta),
    with a strong-concavity margin;
  - r_i x_i is nondecreasing in m, and x_i is nonincreasing in eta >= 0 at a fixed m;
  - q(., eta) is continuous, nondecreasing and bounded by sum_i |r_i| bar x_i;
  - p(., eta) is continuous, strictly decreasing and onto, so m_0 and m_I exist and are unique;
  - m - gamma sigma_E p(m, eta) is strictly increasing and onto, so the traded prices exist and are
    unique;
  - the fund marginal alpha~_i + r_i m(w) - gamma v_i x_i is the derivative of the smooth objective
    along coordinate i, whatever sigma_E.
- Parts 2 and 5, for each eta >= 0 and any sigma_E >= 0:
  - the Lagrangian Q + eta k has exactly one maximizer over the funds' boxes and p >= 0;
  - at it every fund holds its clip at (m(w), eta), and p = p(m(w), eta);
  - the ETF's status is the table, with the ETF's marginal e(m) = m - gamma sigma_E p(m, eta) in the
    tests. For p^- > 0: bought iff e(m_I) > theta_b; idle iff theta_s <= e(m_I) <= theta_b; sold iff
    e(m_I) < theta_s, sold to p in (0, p^-) when m_0 > theta_s and to zero when m_0 <= theta_s. For
    p^- = 0: at zero iff m_0 <= theta_b, else bought. In each regime m is the stated price;
  - with sigma_E = 0 the traded prices are theta_b and theta_s (part 2's table).
- Part 3:
  - k(x(eta)) is nondecreasing in eta >= 0;
  - x(0) is the constrained optimum when k(x(0)) >= 0;
  - any eta > 0 with k(x(eta)) = 0 gives the constrained optimum, and it is unique, so all such eta
    give the same holdings.
- Part 4:
  - (a) fund i is bought iff alpha~_i + r_i m - gamma v_i x^-_i > eta + (1 + eta) kappa^+_i and
    x^-_i < bar x_i, and sold iff the mirror holds with x^-_i > 0;
  - (b) a fund's holding moves by at most |r_i|/(gamma v_i) per unit of exposure price, and it is
    nonincreasing in the cash price at a fixed exposure price (red's nit).

Paper-level:
- the existence of eta > 0 with k(x(eta)) = 0 when k(x(0)) < 0: the KKT multiplier, cited through
  AX-13 via claim 102's part 1 (rule 21, PM). Part 3's constrained-optimum statement is conditional
  on it;
- part 4(c) and the Checks.

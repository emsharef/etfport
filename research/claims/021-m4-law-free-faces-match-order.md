---
id: 21
title: "Law-free certification against the two-face ETF comparator: face-by-face range bounds already match the known-law order, and joint constructions gain at most the union-bound level"
status: formalized
model_version: M4
depends_on: [16]
axioms_used: [AX-06]
formal: lean/Standalone/M4LawFreeFacesMatchOrder.lean
direction: D5
---
## Statement

D5 asks whether the funded whole-class structure lets a law-free rule do
better than applying general confidence tools to the comparator faces one by
one (PM's note on experiment 013). In claim 016's two-face family this claim
answers: no, in order. A rule that knows only a range bound for each face
contrast, and nothing else about the law, certifies against the whole
optimized ETF class with worst-case history length of the same order as the
known-law lower bound; any joint construction over the faces is the minimum of
implied per-face bounds and can gain at most the union-bound level factor.

**Setting: claim 016's family with a bounded law class.** One active fund and
one ETF, initial wealth and cash one, zero risky incumbent, caps one, zero
shareholder costs and ETF drag, gamma=0, B^A=(1,0), B^E=(0,1). A known real
3-by-3 matrix J with Euclidean operator norm at most 1/100, and claim 016's
c_0, c_1, Theta_4, d_0=(1,0,1), d_1=(1,-1,1), m_j(theta)=d_j'theta, and
witness w_A=(1,0). The bounded law class is

```
L(J) = { known finite laws of U in R^3 : E U=0, ||U||_2<=9 },
(z^f_1,z^f_2,z^A)=J U,  z^E=0,
```

with no restriction on the covariance, skew or higher moments of U. It
contains claim 016's K_J, which adds E U U'=I_3. Put

```
sigma_bar_j=||J'd_j||,   sigma_bar=max_j sigma_bar_j,
R_j=9 sigma_bar_j,       R=max_j R_j.
```

Under every law in L(J), |d_j'J U|<=R_j, and on K_J, sigma_bar_j equals claim
016's sigma_j. A **law-free rule** is a full-history rule, possibly using an
independent coin, that is a fixed function of the public history and does not
depend on the law of U. Claim 016's two requirements (eta=epsilon,
delta_econ=delta/4),

```
for all theta in Theta_4:
  P_theta(certify and Adv(certified action;theta)<=delta/4) <= epsilon;
for all theta in Theta_4 with G_*(theta)>=delta:
  P_theta(certify and Adv(certified action;theta)>delta/4) >= 1-epsilon,
```

are imposed at every law in L(J). Every law in L(J) gives an admissible M4
instance, and Adv(w_A;theta)=min_j m_j(theta), G_*=max(0,min_j m_j)
(claim 016, part 1, whose admissibility proof uses only ||U||<=9).

1. **Joint constructions are face-by-face in disguise.** For every nonempty
   C in R^3,

   ```
   inf_{theta in C} Adv(w_A;theta) = min_j inf_{theta in C} m_j(theta).
   ```

   Consequently any rule that certifies w_A when inf_{C_N} Adv(w_A;.) >
   delta_e for a data-dependent set C_N with P_theta(theta in C_N)>=1-eta at
   every theta and every law (a joint confidence construction of any kind,
   at any review) has certificate min_j ell_j with ell_j=inf_{C_N} m_j, and
   each implied face bound is a marginal lower confidence bound at the full
   level: P_theta(m_j(theta)<ell_j)<=eta for each j. Conversely marginal
   lower bounds valid at levels eta_0,eta_1 give, by the union bound, a set
   C_D={theta: m_j(theta)>=ell_j for both j} with coverage at least
   1-eta_0-eta_1. So the whole-class certificate of every joint construction
   is a minimum of two per-face lower bounds, and the only room between a
   joint and a face-by-face construction is the level of each face bound, eta
   against eta/2. For any family of face bounds whose width at level a is
   proportional to sqrt(log(1/a)), the width ratio is at most
   sqrt(1+log 2/log(1/eta)) and the history-length ratio at most
   1+log 2/log(1/eta): 1.23 at eta=1/20. Exploiting the faces' shared premium
   error by decomposition cannot help either: since d_1=d_0-e_2 with
   e_2=(0,1,0), a bound on the ETF face through the cash face and a premium
   bound has range R_0+9||J'e_2||>=R_1, never tighter than the direct face
   bound, and it needs a union over three statements instead of two.

2. **A law-free face-by-face range rule.** For N_obs>=3 log(2/eta) put

   ```
   r_j=R_j sqrt(3 log(2/eta)/N_obs),   ell_j=d_j'theta_hat_N-r_j,
   ```

   certify w_A if min_j ell_j>delta_econ, and otherwise implement the
   plug-in ETF-only action (the ETF if lambda_hat_2>0, else cash). This rule
   uses J and nothing else about the law. For every law in L(J), every theta
   in Theta_4 and every delta_econ>=0,

   ```
   P_theta(certify and Adv(w_A;theta)<=delta_econ) <= eta.
   ```

   For delta>0, eta=epsilon in (0,1) and delta_econ=delta/4, both requirements
   hold for every law in L(J) whenever

   ```
   N_obs >= max(3, 22 R^2/delta^2) log(2/epsilon),
   ```

   which with R=9 sigma_bar reads N_obs >= 1782 (sigma_bar^2/delta^2) log(2/epsilon)
   when sigma_bar/delta>=1.

3. **Law-free certification matches the known-law order.** Fix delta in
   (0,sigma_bar/8] and epsilon in (0,1/16], and assume (J J')_11>0 and
   sigma_bar>0. Every law-free rule that meets both requirements at every law
   in L(J) satisfies

   ```
   N_obs >= [1/(16 pi^2)] (sigma_bar^2/delta^2) log(1/epsilon),
   ```

   because L(J) contains K_J and claim 016's part 2 applies. The rule in part
   2 meets both requirements at every law in L(J) whenever
   N_obs>=1782 (sigma_bar^2/delta^2) log(6/epsilon). The worst-case order of
   law-free certification over L(J) is therefore (sigma_bar^2/delta^2)
   log(1/epsilon), the same as the known-law order over K_J in claim 016,
   with loose constants. In particular no law-free rule, joint,
   variance-adaptive or otherwise, improves that order; the funded whole-class
   structure enters only through the faces' ranges R_j (the ETF face carries
   the market premium's error, R_1 against R_0) and the maximum over faces,
   exactly as in the known-law case. Variance adaptation and joint
   constructions can change constants only, the latter by at most the level
   factor of part 1; the largest factor by which any law-free rule can shorten
   the range rule's sufficient length is the ratio of the two constants,
   1782 x 16 pi^2 x log(6/epsilon)/log(1/epsilon), which is loose.

**Consequence for D5** (a reading of 1-3, not a further theorem). Over a
bounded law class the whole-class comparator with a linear score is its two
faces, and law-free certification against it is face-by-face scalar mean
certification at the known-law order. What remains open for D5 is constants
(range against variance, and the level factor), which experiment 014 measures,
and the time-uniform version over repeated reviews, which needs the cited
sequential tools once their ledger entries pass audit.

## Proof

### The tail bound: Hoeffding's inequality through ledger entry AX-06

The only probabilistic input is Hoeffding's inequality through ledger entry
`AX-06` (`maurer2009empirical`, Theorem 1): for n iid random variables with
values in [0,1] and delta>0, with probability at least 1-delta the true mean
exceeds the sample mean by at most sqrt(ln(1/delta)/(2n)); the lower-tail
form follows by replacing Z with 1-Z, as the entry records. It is not
re-proved here; the proof below only checks its hypotheses and rescales.

Let Y be a real random variable with E Y=0 and |Y|<=R almost surely, and let
Y_bar be the mean of N iid copies. If R=0 then Y=0 almost surely, Y_bar=0,
and every bound below is trivial; so let R>0. Then Z=(R-Y)/(2R) takes values
in [0,1], its N copies are iid, and E Z-Z_bar=Y_bar/(2R). Applying `AX-06`
with delta=exp(-N a^2/(2R^2)), which lies in (0,1) for a>0, gives
sqrt(ln(1/delta)/(2N))=a/(2R), hence for a>0 the strict-event form

```
P(Y_bar>a) <= exp(-N a^2/(2 R^2)) <= exp(-N a^2/(3 R^2)),
```

and the same for the lower tail with Z=(R+Y)/(2R). The non-strict form
P(Y_bar>=a) follows by applying this at a'<a and letting a' increase to a,
by continuity of the exponential; Part 2 uses only the strict events
{e_bar_j>r_j} and {e_bar_j<-r_j}. The claim keeps the
looser constant 3 in every formula below, so no number changes; Hoeffding's
constant 2 only improves each bound. The hypotheses are checked at each use:
the summands are iid across quarters under M4's law, centered, and bounded by
the face range R_j.

### Part 1

For each theta, Adv(w_A;theta)=min_j m_j(theta) (claim 016, part 1). The
infimum over C of a minimum of two functions is the minimum of their infima.
For a joint construction, on the coverage event theta in C_N every point of
C_N includes theta, so m_j(theta)>=inf_{C_N} m_j=ell_j for both j; hence
{m_j(theta)<ell_j} is contained in {theta not in C_N}, whose probability is
at most eta. Conversely, if P(m_j(theta)<ell_j)<=eta_j for each j, then
P(theta not in C_D)<=eta_0+eta_1 by the union bound, and by the identity the
certificate built from C_D is min_j ell_j. For a family with width
w(a)=kappa sqrt(log(1/a)), w(eta/2)/w(eta)=sqrt(log(2/eta)/log(1/eta))
=sqrt(1+log 2/log(1/eta)), and a history length proportional to w^2 scales
by the square. The decomposition remark is the triangle inequality
||J'd_1||=||J'd_0-J'e_2||<=||J'd_0||+||J'e_2||, multiplied by 9.

### Part 2: validity and power of the range rule

Under any law in L(J), the estimation error of face j is
e_bar_j=d_j'(theta_hat_N-theta)=Y_bar_j, the mean of N iid copies of
Y_j=d_j'J U, which is centered with |Y_j|<=||J'd_j|| ||U||<=R_j. Since
ell_j=m_j(theta)+e_bar_j-r_j, the event {ell_j>m_j(theta)} is {e_bar_j>r_j},
and by the tail bound (`AX-06`) with a=r_j (the claim keeps the condition
r_j<=R_j, that is N_obs>=3 log(2/eta), under which the looser constant was
originally derived; the cited bound needs only a>0),

```
P_theta(e_bar_j>r_j) <= exp(-N r_j^2/(3R_j^2)) = eta/2.
```

By the union bound, with probability at least 1-eta both ell_j<=m_j(theta),
so min_j ell_j<=min_j m_j(theta)=Adv(w_A;theta). On that event a
certification, which needs min_j ell_j>delta_econ, forces
Adv(w_A;theta)>delta_econ. This proves the false-certification bound for
every law, theta and delta_econ. The certified action is the funded active
witness w_A, and the fallback is a funded ETF-only action, as claim 016's
rule class requires.

For power, fix theta with G_*(theta)>=delta, so both m_j(theta)>=delta. By
the tail bound's lower-tail form and the union bound, with probability at least
1-eta both e_bar_j>=-r_j, and then ell_j>=m_j(theta)-2r_j>=delta-2r_j. If
r_j<3 delta/8 for both j, that is

```
N_obs > (64/3)(R_j^2/delta^2) log(2/eta)   for both j,
```

then ell_j>delta/4=delta_econ for both j, the rule certifies, and
Adv(w_A;theta)=min_j m_j(theta)>=delta>delta/4. Since 64/3<22, the displayed
length N_obs>=max(3,22R^2/delta^2) log(2/epsilon) with eta=epsilon suffices for
both events, and it also ensures N_obs>=3 log(2/eta). With R=9 sigma_bar,
22 x 81=1782, and 22 R^2/delta^2>=3 whenever sigma_bar/delta>=1.

### Part 3: matching order

Claim 016 (formalized) part 2 assumes, for its lower bound, that for every
known law in K_J there is a full-history rule, allowed to depend on that law,
meeting both requirements at every theta in Theta_4, with delta in
(0,sigma/8], epsilon in (0,1/16], Omega_11>0 and sigma>0, where Omega=J J'
and sigma=max_j sqrt(d_j'Omega d_j)=sigma_bar. A single law-free rule meeting
both requirements at every law in L(J) meets them at every law in K_J, since
K_J is a subset of L(J), and serves as the rule for each of those laws.
Claim 016's conclusion N_obs>=sigma^2 log(1/epsilon)/(16 pi^2 delta^2)
follows. The sufficient length is part 2 with epsilon<=1/16, using
log(2/epsilon)<=log(6/epsilon) and sigma_bar/delta>=8>=1. The two bounds
share the factor (sigma_bar^2/delta^2) and differ in the constant and in
log(1/epsilon) against log(6/epsilon), which is matching order as in claims
015-018. The remaining sentences of part 3 restate the two bounds: a lower
bound that binds every law-free rule, joint or adaptive, and an upper bound
attained by the face-by-face range rule, so no rule improves the order, and
the ratio of the constants bounds any constant-factor improvement.

## Checks

`checks/021/check.py` (exits non-zero on failure; a check, not a proof).
It verifies the tail bound, in the looser constant 3 the claim uses, exactly
by lattice convolution for four bounded centered laws (symmetric, skewed,
three-point, asymmetric) at every N up to 60 on a grid of thresholds, and a
moment-generating bound that implies it, on a grid of t. In claim
016's family with J=s I_3 it computes the face contrasts' exact laws for three
members of L(J) with different covariances and shapes (independent signs, a
correlated three-point law, a skewed law), and checks the range rule's
false-certification bound at N=12, 40, 80 and its power margin at the
sufficient length, by exact convolution. It also checks the decomposition
inequality on 500 random J, the constants 22 x 81=1782 and 64/3<22, the
level factor, and that claim 016's hard laws lie in L(J) (||U||^2<=66).

## Not shown

- The class L(J) is bounded (||U||<=9) with a known J. The librarian's D5
  sweep records that over an unrestricted law class no such rule can exist
  (`bahadur1956nonexistence`, wanted, unread); nothing here concerns
  unbounded or unknown-range laws, or laws with an unknown J.
- One family: claim 016's two-face geometry with gamma=0, zero costs, a zero
  incumbent and a fixed witness w_A. The rule certifies only w_A, which is
  what claim 016's requirements measure; it is not the general M4 plug-in
  gate over data-selected candidates, though part 1 applies to any joint
  construction.
- Single review and fixed N_obs, as in M4. The identity of part 1 holds at
  every review for any confidence sequence, but no time-uniform upper bound
  and no sequential lower bound is proved: those are the cited tools
  (`howard2021time`, `garivier2016optimal`, `kaufmann2014complexity`), whose
  ledger entries AX-01 to AX-04 are under audit, and nothing here uses them.
- Order only. The constants are about 2.8 x 10^5 apart. Per-law rates are
  not addressed: at a particular law a variance-adaptive or known-law rule
  can beat the range rule by a constant, up to the range-to-deviation ratio
  (81 in sample length here, 16 in experiment 013's calibrated class), and
  experiment 014 measures this; empirical-Bernstein constants
  (`maurer2009empirical`, `howard2021time` Theorem 4) are not analyzed.
- Part 1's level-factor bound is for families whose width is proportional
  to sqrt(log(1/level)); it is not a minimax statement about the best possible
  marginal bound at a given level.
- `AX-06` is audited on main. The earlier self-contained Lemma B (a loose
  Hoeffding bound, red-verified) was removed at red's rule-21 request; its
  constant 3 is what every formula still uses.
- The lower bound needs ||J||<=1/100, delta<=sigma_bar/8, epsilon<=1/16,
  (J J')_11>0 and sigma_bar>0, inherited from claim 016.
- This claim does not by itself fire or clear D5's kill criterion; PM reads
  that over the direction's claims. With refuted claim 019 and the refile 020
  it is the third D5 claim of five.

## Prior art

Mechanism: Certifying from bounded iid observations that the minimum of
finitely many linear functionals of an unknown mean exceeds a margin needs
order max_j R_j^2/Delta^2 log(1/epsilon) samples with range-based bounds, and
at least order sigma^2/Delta^2 log(1/epsilon) samples for any rule, so the
law's shape beyond its range, a joint construction over the functionals, and
variance adaptation change constants only.

General results checked: Hoeffding's inequality through ledger entry
`AX-06` (`maurer2009empirical` Theorem 1; its statement is Hoeffding's own
Theorem 1, inequality (2.3), with the [a,b] rescaling remark that follows it,
`hoeffding1963probability` p. 15-16, at full text since 2026-09-28), of which
this claim's upper bound is a special case, used with only its hypotheses
checked; the Le Cam two-point lower bound, entering only through claim 016's
formalized part 2, of which part 3 is a corollary; the fixed-confidence
best-arm lower bounds `garivier2016optimal` Theorem 1 and
`kaufmann2014complexity` Theorem 4, the sequential analogue of part 3's
maximum over faces, not used; `howard2021time` Theorem 1 (stitched
time-uniform boundaries) and Theorem 4 (empirical-Bernstein confidence
sequence) and `maurer2009empirical` Theorem 4 and Corollary 5 (empirical
Bernstein bound and its finite-class union), the variance-adaptive tools
whose constants part 3 says are the only remaining question, not used;
`petrik2016safe`, `esfahani2017data`, `olivaresnadal2018technical`,
`manski1999statistical`, the coverage and penalty precedents already recorded
in claims 016-018; claim 016 (the family, the faces, the lower bound);
experiment 013 (reproduced), whose finding that the union over faces costs
only log 2 inside the boundary is part 1's level factor, and whose
range-based half-widths are the R_j of part 2; refuted claim 019 and its
refile 020, whose finite-face identity part 1 instantiates for two faces.

Searched: claims 014-020 and their reviews, experiments 012-013 and their
reviews, the D5 roadmap entry, the librarian's D5 literature entry, PM's
experiment 013 and 014 notes, and the registered texts of the D5 sources at
theorem level. This is still a claim because D5's question, whether the
funded whole-class structure lets a law-free rule beat face-by-face
application, needed an answer with a proof: it does not, in order, over a
bounded class, and the reason is that the whole class is its faces and the
known-law lower bound already binds every law-free rule. No priority is
claimed for any ingredient.

## Open objections

None. Red's Review answered the five points raised at filing; the fifth, that
the rule-21 objection applies to the self-contained Lemma B, is settled by
this edit, which cites Hoeffding's inequality through ledger entry `AX-06`
and reduces the proof to checking its hypotheses (iid, centered, bounded by
R_j) with every number unchanged.

## Review

**Red, 2026-09-28.** I checked every part by hand, ran my own numerical checks, and went through each point in the claim's Open objections.

**Hand check: every part holds.**
- *Lemma B.* E exp(tY) <= e^{|t|R} - |t|R, and (e^x - 1 - x)/x^2 increases on [0, 1] to e - 2 < 0.72. With t = a/(1.44 R^2), |t|R = a/(1.44R) < 1 for a <= R, so the constant at the boundary a = R is admissible. The exponent -Na^2/(1.44R^2) + 0.72 N a^2/(1.44^2 R^2) = -Na^2/(2.88R^2) is a valid, looser Hoeffding bound.
- *Part 1.* The infimum of a finite minimum is the minimum of the infima. On the coverage event every face bound inf_{C_N} m_j is below m_j(theta), so each is a marginal bound at the full level eta; the union bound gives the converse. The level factor sqrt(log(2/eta)/log(1/eta)) equals sqrt(1 + log 2/log(1/eta)), and the length ratio is 1.231 at eta = 1/20. The width statement is correctly conditional on a sqrt(log(1/a)) family, as the Not shown says. The decomposition remark is the triangle inequality ||J'd_1|| <= ||J'd_0|| + ||J'e_2||.
- *Part 2.* |d_j'J U| <= ||J'd_j|| ||U|| <= R_j. r_j gives exactly eta/2 per face, and r_j <= R_j iff N_obs >= 3 log(2/eta). **Only the union bound is used, so dependence between the two faces' errors is irrelevant.** Power needs r_j < 3 delta/8, that is N > (64/3)(R_j/delta)^2 log(2/eta), and 22 > 64/3 and 22 x 81 = 1782 check.
- *Part 3.* K_J is contained in L(J), and a single law-free rule meeting both requirements for all of L(J) serves as the per-law rule in claim 016's quantifier, so claim 016's formalized lower bound applies with sigma = sigma_bar. The hypotheses it needs (||J|| <= 1/100, delta <= sigma_bar/8, epsilon <= 1/16, Omega_11 > 0) are carried over, and so is the sufficient length.
- *Admissibility.* It uses only ||U|| <= 9 and ||J|| <= 1/100, so laws in L(J) with any covariance, including singular ones, are admissible M4 instances.

**Independent numerics** (red's own script, written without reading `checks/021/check.py`).
- *Lemma B.* I computed exact binomial tails for two-point laws with rare-outcome probability 0.5, 0.2, 0.05 and 0.01, the Hoeffding-extremal shape, for N <= 60 and 60 thresholds in (0, R]. Both tails stay below exp(-N a^2/(3R^2)); the largest ratio is 0.990. The largest value of (e^x - 1 - x)/x^2 on (0, 1] is 0.7183.
- *Range rule.* I ran the rule in claim 016's family (J = s I, s = 1/100) under three members of L(J) outside K_J: a singular correlated three-point law, a skewed law, and signs of size 5 with ||U|| ≈ 8.7. At eta = 1/20 and 1/4 and N = 12, 40 and 200, false certification at the null was 0 in all 20,000 histories, and power at the matched delta was 1.
- *Decomposition.* The inequality holds on 500 random J.
- *Claim's own check.* `checks/021/check.py` passes.

**The Open objections, answered.**
1. Lemma B's constant at a = R is admissible (|t|R = 1/1.44).
2. The faces' dependence does not matter: only the union bound is used.
3. Laws with covariance other than I are admissible, since positivity uses ||U|| <= 9 alone.
4. A single rule for all laws is what makes claim 016's lower bound apply, and the proof uses exactly that.
5. **The rule-21 objection does apply to Lemma B,** as it did to claim 019's Lemma A: it re-proves, in weaker form, Hoeffding's inequality, a known general theorem. It must be replaced by a citation, through a ledger entry for Hoeffding's inequality (the claim requests one), with the proof reduced to checking the hypotheses: iid, centered, |Y_j| <= R_j. No number changes, since Hoeffding's constant 2R^2 improves on 3R^2. This is required before approval or formalization, and Lean should take it as an Upstream hypothesis, not a Novel proof.

**Mechanism (4b).** Certifying that the minimum of finitely many linear functionals of a bounded-noise mean exceeds a margin takes order max_j R_j^2/Delta^2 log(1/epsilon) samples with range bounds, and at least order sigma^2/Delta^2 log(1/epsilon) for any rule. This is Hoeffding plus the union bound for the upper side, and the Le Cam two-point bound (through claim 016) for the lower side. The finite-minimum identity is claim 020's for two faces. It is **a special case of known results, an application**, and the claim says so. What it adds for D5 is the answer to PM's question: over a bounded law class the whole-class comparator gives a law-free rule no advantage in order over face-by-face application, and the remaining gaps are constants.

**Scope.** "Matches the known-law order" is a worst-case statement over L(J), whose hard laws are claim 016's. Per law, the range rule can be worse by up to (R_j/sigma_j)^2 = 81 in length, and 16-39 in experiments 013-014's calibrated class. That constant is what makes law-free certification powerless at calibrated scales, as experiments 013-014 show. The Not shown states this honestly, and the claim does not contradict the paper or claims 015-020.

Verdict: red-passed

**Red recheck, 2026-09-28: the revision replacing Lemma B by `AX-06`.** Only the tail-bound section changed, plus consequential edits to the Checks, Not shown, Prior art, Open objections and Formalization notes and to axioms_used. No Statement, constant or number changed.

- **Affine rescaling, as PM asked.** For centered Y with |Y| <= R and R > 0:
  - Z = (R - Y)/(2R) takes values in [0, 1], and N iid copies of Y give N iid copies of Z.
  - E Z = 1/2 and E Z - Z_bar = Y_bar/(2R).
  - AX-06 (`maurer2009empirical` Theorem 1, audited ok on main) at delta = exp(-N a^2/(2R^2)), which lies in (0, 1) for a > 0 as AX-06's audit clarification requires, gives sqrt(ln(1/delta)/(2N)) = a/(2R). Hence P(Y_bar > a) <= exp(-N a^2/(2R^2)) <= exp(-N a^2/(3R^2)).
  - Z = (R + Y)/(2R) gives the lower tail.
  - The hypotheses hold as stated: Y_j = d_j'J U is iid across quarters under M4's law, centered because E U = 0, and bounded because |Y_j| <= ||J'd_j|| ||U|| <= R_j.
  - Keeping the constant 3 is a valid weakening, so every sufficient length stands.
- **Nits (no change of substance).**
  1. AX-06 gives the strict event, P(Y_bar > a) <= delta, while the display writes P(Y_bar >= a). The latter follows by letting a' increase to a and using continuity of exp, and Part 2 uses only the strict events {e_bar_j > r_j} and {e_bar_j < -r_j} anyway.
  2. The rescaling needs R_j > 0. For a face with R_j = 0, Y_j ≡ 0 and the bound is trivial; one clause would cover it.
  3. The Not shown still says AX-06 is "not yet audited", but it is audited ok on main.
  4. The Formalization notes say Hoeffding enters as an Upstream hypothesis. The provisional formalization (`provisional/lean-m4-law-free-faces-match-order`) instead applies Mathlib's machine-checked Hoeffding lemma, `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, with no Upstream structure. Either satisfies rule 21; the notes should match what lean does.
- **Rule 21 is now satisfied.** Nothing known is re-proved; the claim cites and checks hypotheses. The rest of red's Review stands unchanged: the hand check, the numerics, and answers 1-4 to the Open objections.

Verdict: red-passed

## Formalization notes

Approved 2026-09-28 by pm: Red's full hand check and numerics (Lemma B's replacement, the union bound over faces with dependent contrasts, admissibility of laws with any covariance, the single-law-free-rule quantifier) and its recheck of the revision (AX-06, audited, via the affine rescaling PM asked about, constant 3 a valid weakening, no number changed) are sound; rule 21 is now satisfied; no open objections. Limits stated: an application of Hoeffding, the union bound and the Le Cam two-point bound through claim 016; the known-law order match is worst case over the bounded class, per law the range rule can be up to (R_j/sigma_j)^2 worse (16-39 at calibrated scales), which is why law-free certification is powerless in experiments 013-014; four wording nits (strict event, a zero-range clause, stale 'not yet audited', formalization notes naming Upstream where lean uses Mathlib) routed to math.


Not machine checked. The core is finite: a minimum-of-infima identity, a
union bound, Hoeffding's inequality taken as an Upstream hypothesis structure
(`AX-06`, per red's Review) with its hypotheses discharged on finite laws,
and the application of claim 016's formalized lower bound to a larger law
class. No sequential or measure-theoretic object appears.

Lean, 2026-09-28: machine checked. This replaces "Not machine checked" above; the earlier text is
kept as it was written. The statement is in `lean/Standalone/M4LawFreeFacesMatchOrder.lean` and the
proof in `lean/Novel/M4LawFreeFacesMatchOrderProof.lean`. `lake build` and the axiom audit pass
(standard axioms only).

Hoeffding. The paragraph above says Hoeffding enters as an Upstream hypothesis structure. The
formalization instead uses Mathlib's machine-checked Hoeffding lemma,
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, which follows PM's rule-21
reading (a cited result already proved in the pinned Mathlib enters through Mathlib). It applies the
lemma to each finite law as a measure. A Chernoff step on the finite iid histories then gives
P(Y_bar >= a) <= exp(-N a^2/(2R^2)), including the zero-range case. Every formula keeps the claim's
constant 3, so no number changes. Nothing is re-proved and no hypothesis structure is assumed. The
cited `AX-06` has its own Upstream file on lean/d5-upstream, whose instance is proved from Mathlib's
Hoeffding inequality.

Formal objects. The family, faces, witness, domain, `SmallJ`, `sigma`, `InKJ` and `AdmitsJ` are
claim 016's; the requirement predicates are claim 015's; `Rule`, `prob` and the M4 objects are
claim 014's. `InLJ` is L(J): finite laws with E U = 0 and ||U|| <= 9. A law-free rule is a single
`Rule N`, fixed before the law is quantified. The range rule reads only the public history and J,
and its estimate `thHat`, M4's sample mean, is shown equal to `thetaHat` under every law.

Proved:
1. Setting: every law in L(J) gives an admissible M4 instance (with ||J|| <= 1/100), with the face
   formulas for Adv(w_A) and G_*, the bounds |d_j'J U| <= R_j, K_J contained in L(J), and
   sigma_bar_j = sigma_j.
2. Part 1:
   - the infimum over any set of the whole-class advantage is the minimum of the face infima;
   - a joint confidence set implies each face bound at the full level;
   - marginal bounds give, by the union bound, a joint set whose certificate is their minimum;
   - the level-factor identities, with 1.23 < 1 + log 2/log 20 < 1.24;
   - d_1 = d_0 - e_2 and R_1 <= R_0 + 9 ||J'e_2||.
3. Part 2: the range rule stays in claim 016's rule class and falsely certifies with probability at
   most eta at every theta and every delta_econ. It meets both requirements for
   N_obs >= max(3, 22 R^2/delta^2) log(2/epsilon), which is the 1782 (sigma_bar^2/delta^2) form
   when sigma_bar/delta >= 1.
4. Part 3: every single law-free rule in claim 016's class that meets both requirements at every
   law in L(J) needs N_obs >= (1/(16 pi^2)) (sigma_bar^2/delta^2) log(1/epsilon), through claim
   016's formalized lower bound. The range rule meets both at
   N_obs >= 1782 (sigma_bar^2/delta^2) log(6/epsilon).

Relation to the prose. No gap was found between the formal statement and the Statement.
- Part 3's lower bound is stated for rules in claim 016's rule class, since that is the class
  claim 016's lower bound covers and the prose applies it. It needs neither (J J')_11 > 0 nor
  N_obs >= 3 log(2/eta).
- Some formal parts are stronger than the prose: validity holds at every theta; Part 1's joint and
  union statements hold for any data-dependent sets and bounds under any finite law; and Part 2
  needs only epsilon < 1.
- Infima over parameter sets are in EReal.

The limits PM recorded at approval apply unchanged. This is an application of Hoeffding, the union
bound and the Le Cam two-point bound through claim 016. The known-law order match is worst case over
the bounded class: per law the range rule can be up to (R_j/sigma_j)^2 worse (16-39 at calibrated
scales), which is why law-free certification is powerless in experiments 013-014.

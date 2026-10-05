# Ledger of cited results

Everything the project takes from the literature instead of proving. One entry per result.

A ledger entry needs no human approval: it is usable once its source text is in `refs/text/` and the
auditor has checked it against that text on the same branch, leaving a line in `AUDIT_LOG.md`.

Each entry carries:

- **Source:** bibliography key, the exact theorem/section, and where in `refs/text/` it is.
- **Statement (source notation):** quoted verbatim. Quote, do not paraphrase.
- **Statement (our notation):** the form the project uses, with every specialization named.
- **Assumptions in the source:** including any the project silently relies on.
- **Simplifications we impose:** each one, and why it does not strengthen the conclusion.
- **Formal:** how it enters the formalization — a hypothesis structure and its instance, or, for a
  closed algebraic proposition, the lemma that proves it. See rule 6.
- **Audit:** the `AUDIT_LOG.md` line that passed it.

Entries are headed `### AX-NN  <short name>` and numbered in order. The heading below is deliberately
not a real number, so the queue does not offer it for audit; copy it for the first entry.

    ### AX-NN  <short name>
    Source:
    Statement (source notation):
    Statement (our notation):
    Assumptions in the source:
    Simplifications we impose:
    Formal:
    Audit: none yet

### AX-01  Best-arm-identification sample-complexity lower bound (garivier2016optimal Theorem 1)
Source: `garivier2016optimal`, Theorem 1, pp.3-4 of `refs/text/garivier2016optimal.md`.
Statement (source notation): "Let δ ∈ (0, 1). For any δ-PAC strategy and any bandit model µ ∈ S,
E_µ[τ_δ] ≥ T*(µ) kl(δ, 1 − δ), where T*(µ)^{-1} := sup_{w∈Σ_K} inf_{λ∈Alt(µ)} (Σ_{a=1}^K w_a d(µ_a, λ_a))."
Here S is a set of exponential-family bandit models each with a unique optimal arm a*(µ), a
δ-PAC strategy satisfies P_µ(τ_δ<∞)=1 and P_µ(â_{τ_δ}≠a*)≤δ for every µ∈S, Alt(µ)={λ∈S: a*(λ)≠a*(µ)},
Σ_K is the probability simplex on the K arms, and d is the KL divergence between the arms'
exponential-family laws.
Statement (our notation): none is given. Auditor's fail (ledger/AUDIT_LOG.md, 2026-09-28, commit
49f4dbf) found the earlier draft's reading — "the expected history length is at least T*(µ)
kl(eta,1-eta)" — false for M4: the source's τ_δ counts single-arm draws under a bandit protocol
where one arm is sampled per round (p.1), while M4's history reveals every comparator each quarter
as correlated linear functionals of one joint draw, full information rather than bandit feedback.
The auditor's counterexample (two unit-variance Gaussian arms, µ=(1,0), T*=8): a period revealing
both arms is two draws, so full-information rounds meet Theorem 1's own bound at 4 kl(delta,1-delta)
rounds, not 8 — half the bandit-draw count, refuting a literal history-length reading. This entry
therefore cites Theorem 1 only for the bandit sample-complexity lower bound it actually proves,
above; no translation to M4's history length is given. A future D5 claim connecting the two needs
its own reduction step (e.g. a full-information analogue of the same KL argument, or a data-
processing bound from bandit feedback to full information), proved on its own, not read off here.
Assumptions in the source: the arms form a one-parameter canonical exponential family parameterized
by their mean (p.3); a bandit protocol where the strategy's sampling rule selects one arm A_t per
round and observes one independent draw from that arm's law, with τ_δ counting those single-arm
draws (p.1-2); each bandit model in S has a unique optimal arm; the strategy is δ-PAC on the whole
class S, not just at one model.
Simplifications we impose: none — no M4-specific reading is asserted by this entry.
Formal: enters `lean/Upstream` as a hypothesis structure for Garivier-Kaufmann's own δ-PAC K-armed
bandit lower bound (arms, their one-parameter exponential-family laws, a δ-PAC strategy, T*(µ), the
conclusion). Per rule 6, a faithful M2/M4 instance is out of reach without proving the theorem for
correlated full-information data, which rule 6 forbids reconstructing; M2/M4's joint categorical
scenario law is not a model of K independent one-parameter arms and is not claimed as one. The
instance is instead K=2, arm 1 Bernoulli(3/4), arm 2 Bernoulli(1/4): µ=(3/4,1/4) has a unique
optimal arm a*(µ)=1 (3/4 > 1/4), so µ∈S (the auditor's fail, 915b2a9, gives S's own definition,
p.4: a µ with a strict maximizer); Alt(µ)={λ∈S: a*(λ)=2} is nonempty (e.g. λ=(1/4,3/4)∈S);
Bernoulli's KL divergence is finite and well-defined between any two points of (0,1); so T*(µ) is a
genuine finite positive number by the stated sup-inf formula. Its numeric value is not computed
here, since that would exercise the theorem's content rather than merely instantiate its hypotheses.
This is a genuine, non-degenerate model of the source's own setting — not a model of M2/M4, and no
claim currently derives an M4 consequence from it.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-01 line); usable only for the bandit statement quoted, with no M4 reading; the Upstream instance must still pass rule 6 at the Upstream audit.

### AX-02  Track-and-Stop asymptotic sample complexity (garivier2016optimal Theorem 14)
Source: `garivier2016optimal`, Theorem 14, p.13 of `refs/text/garivier2016optimal.md`.
Statement (source notation): "Let µ be an exponential family bandit model. Let α ∈ [1, e/2] and
r(t) = O(t^α). Using Chernoff's stopping rule with β(t, δ) = log(r(t)/δ), and the sampling rule
C-Tracking or D-Tracking, limsup_{δ→0} E_µ[τ_δ]/log(1/δ) ≤ α T*(µ)."
Statement (our notation): none is given, for the same reason as AX-01 (auditor's fail on
ledger/AUDIT_LOG.md, 2026-09-28, commit a9b7849): Theorem 14 bounds a bandit sampling-and-stopping
procedure's draw count, and the auditor's counterexample (AX-01's Statement above) shows a
full-information reading of the bound is not matched but undercut. This entry cites Theorem 14 only
for the bandit upper bound it proves. It does not by itself state that Track-and-Stop is δ-PAC: that
requires Theorem 10 (Bernoulli arms) or Proposition 12 (general exponential families, α>1, an
unspecified constant C(α,K)), neither quoted here; "asymptotically sample-optimal as α→1" is the
source's own combined summary (p.13) of Theorems 1, 10/12 and 14 together, not a consequence of
Theorem 14 alone, and this entry does not assert it.
Assumptions in the source: exponential family bandit model, the same one-arm-per-round protocol as
AX-01; a sequential (data-dependent stopping time) procedure with the stated tracking sampling rule
and Chernoff stopping rule; asymptotic in δ→0.
Simplifications we impose: none — no M4-specific reading is asserted.
Formal: enters `lean/Upstream` as a further field of AX-01's hypothesis structure (an achievability
statement for the same bandit setting), with AX-01's revised genuine instance (K=2, Bernoulli(3/4)
versus Bernoulli(1/4)), for the same reason: a faithful M2/M4 instance would require proving the
theorem for full-information data.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-02 line); usable only for the bandit upper bound, not delta-PAC or optimality; Upstream instance subject to rule 6 at the Upstream audit.

### AX-03  Sample-complexity lower bound for identifying the top m arms (kaufmann2014complexity Theorem 4)
Source: `kaufmann2014complexity`, Theorem 4, p.8 of `refs/text/kaufmann2014complexity.md`.
Statement (source notation): "Let ν ∈ M_m, where M_m is defined by (4) [M_m = {ν=(ν_1,...,ν_K):
ν_i∈P, µ_[m]>µ_[m+1]}], and assume that P satisfies Assumption 3; any algorithm that is δ-PAC on
M_m satisfies, for δ ≤ 0.15, E_ν[τ] ≥ (Σ_{a∈S*_m} 1/KL(ν_a,ν_[m+1]) + Σ_{a∉S*_m} 1/KL(ν_a,ν_[m]))
log(1/(2.4δ))," where S*_m is the set of the m best arms, Assumption 3 is a continuity condition
on the family P of arm laws (met by exponential families parameterized by their mean), and δ-PAC
means the algorithm identifies S*_m with error probability at most δ.
Statement (our notation): none is given, on the same grounds as AX-01: this is again a bandit
sample-complexity lower bound, on a stopping time τ that counts single-arm draws under the same
one-arm-per-round protocol, stated in this source's own Section 1 (pp.1-2: at each time t an agent
chooses one arm A_t and receives one independent draw Z_t from it), not on M4's full-information
quarterly records.
Assumptions in the source: P satisfies Assumption 3 (a continuity/richness condition on the arm-law
family, met by exponential families continuously parameterized by their mean); δ ≤ 0.15 (a stated
numeric threshold, not all δ∈(0,1)); a δ-PAC algorithm on the whole class M_m; the same bandit
protocol as AX-01/AX-02 (one arm sampled per round, τ the number of rounds).
Simplifications we impose: none — no M4-specific reading is asserted.
Formal: enters `lean/Upstream` as a further hypothesis-structure instance alongside AX-01/AX-02
(the additive-KL top-m lower bound form). The instance is K=2, m=1, arm 1 Bernoulli(3/4), arm 2
Bernoulli(1/4) — the same laws as AX-01's genuine instance, but note this is not the same bound:
at K=2, m=1, Theorem 4 gives (1/KL(ν_1,ν_2)+1/KL(ν_2,ν_1)) log(1/(2.4δ)), a different expression
from AX-01's T*(µ) kl(δ,1-δ) (the source itself notes, p.12, that its two-armed Theorem 6 bound is
always tighter than Theorem 4's; the auditor's fail, 915b2a9, gives the unit-variance-Gaussian
numeric gap, 4 log(1/(2.4δ)) against 8 kl(δ,1-δ)). ν=(3/4,1/4) satisfies µ_[1]=3/4>1/4=µ_[2], so
ν∈M_1 and S*_1={1} is well-defined; P is taken to be all Bernoulli(p), p∈(0,1), which satisfies
Assumption 3 by continuity of the Bernoulli KL divergence in p (not proved here); KL(ν_1,ν_2) and
KL(ν_2,ν_1) are then finite positive numbers, so the right-hand side is a genuine finite positive
bound. This is a genuine, non-degenerate model of the source's own setting — not a model of M2/M4's
correlated full-information data, and no claim currently derives an M4 consequence from it.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-03 line); usable only for the bandit statement quoted; Upstream instance subject to rule 6 at the Upstream audit.

### AX-04  Time-uniform sub-ψ uniform boundary via a stitched construction (howard2021time Theorem 1)
Source: `howard2021time`, Definitions 1-2 (p.4-5) and Theorem 1 ("Stitched boundary", p.8) of
`refs/text/howard2021time.md`; equation (8) (the stitching function S_α) is on p.7.
Statement (source notation): Definition 1 (sub-ψ condition, p.4): "Let (S_t)_{t=0}^∞, (V_t)_{t=0}^∞
be real-valued processes adapted to an underlying filtration (F_t)_{t=0}^∞ with S_0=V_0=0 and
V_t≥0 for all t. For a function ψ:[0,λ_max)→R and a scalar l_0∈[1,∞), we say (S_t) is l_0-sub-ψ
with variance process (V_t) if, for each λ∈[0,λ_max), there exists a supermartingale (L_t(λ))_{t=0}^∞
w.r.t. (F_t) such that EL_0(λ)≤l_0 and exp{λS_t−ψ(λ)V_t}≤L_t(λ) a.s. for all t." Definition 2
(uniform boundary, p.5): "Given ψ:[0,λ_max)→R and l_0≥1, a function u:R→R is called an l_0-sub-ψ
uniform boundary with crossing probability α if sup_{(S_t,V_t)∈S^{l_0}_ψ} P(∃t≥1: S_t≥u(V_t))≤α."
Theorem 1 (p.8): "For any c≥0, α∈(0,1), η>1, m>0, and h:R≥0→R≥0 increasing such that
Σ_{k=0}^∞ 1/h(k)≤1, the function v↦S_α(v∨m) is a sub-gamma uniform boundary with crossing
probability α. Further, for any sub-ψ_G process (S_t) with variance process (V_t) and any v_0≥m,
P(∃t≥1: V_t≥v_0 and S_t≥S_α(V_t)) ≤ Σ_{k=⌊log_η(v_0/m)⌋}^∞ α/h(k)," (9) where S_α is the
closed-form stitching function of equation (8), built from k_1, k_2 (functions of η) and the
intrinsic-time function 𝓁(v).
Statement (our notation): none is given. The earlier draft (aaa7ede) had two defects the auditor's
fail (ledger/AUDIT_LOG.md, 2026-09-28, commit 467bc9b) found decisive, on the same pattern as
AX-01 through AX-03. (1) Misquote: the tail sum in (9) is Σ α/h(k), not Σ α — the entry had dropped
the "/h(k)" factor, an infinite sum. Fixed above, quoted correctly. (2) The source is a *one-sided*
boundary: Definition 2 bounds only P(∃t: S_t≥u(V_t)), and the paper restricts to λ≥0 "to derive
one-sided bounds" (p.4); a two-sided confidence sequence needs a separate union bound over both
(S_t) and (−S_t) (p.4), each at half the crossing probability, giving 1−2α overall coverage at
crossing probability α per side, not the earlier draft's claimed "1−alpha simultaneously." The
earlier draft's reading — a two-sided [estimate ± u(N)/N] confidence sequence covering the true
parameter at 1−alpha — does not follow from Theorem 1 alone. This entry, like AX-01 through AX-03,
therefore cites the theorem only for the one-sided uniform boundary it proves, above; no M4 reading
is given. A future D5 claim needing a two-sided or vector-valued (M4's θ_hat_N is 3-dimensional,
and a score gap is a nonlinear functional of it, not itself a scalar sub-ψ process) time-uniform
guarantee needs its own construction (a union bound over both tails, and a per-direction or matrix
argument for the vector case), proved on its own, not read off here.
Assumptions in the source: (S_t),(V_t) are real-valued, adapted to a common filtration, S_0=V_0=0,
V_t≥0; (S_t) is l_0-sub-ψ with variance process (V_t) in Definition 1's precise sense — a
supermartingale (L_t(λ)) dominates exp{λS_t−ψ(λ)V_t} for every λ∈[0,λ_max), with EL_0(λ)≤l_0 — not
merely "sub-gamma with a known or bounded variance process" as the earlier draft's looser paraphrase
had it. λ is restricted to λ≥0 (one-sided). Theorem 1 additionally needs ψ=ψ_G (the sub-gamma CGF
bound with scale c) and the stated η, m, h conditions.
Simplifications we impose: none — no M4-specific reading is asserted. Whether M4's running
estimator error is sub-gamma with an explicit scale and variance process in Definition 1's sense is
a claim obligation for a future D5 claim, not an assumption this entry treats as already satisfied
(the earlier draft's "an easy consequence of M4's bounded finite shock support" belonged there, not
among the source's own assumptions, and is removed).
Formal: enters `lean/Upstream/StitchedBoundary.lean` as a hypothesis structure for Definitions 1-2
and Theorem 1 (ψ, l_0, an l_0-sub-ψ process pair (S_t,V_t), the stitching parameters c,α,η,m,h, and
the boundary S_α with its crossing-probability conclusion). Per rule 6, a faithful M4 instance (M4's
running estimator or score-gap process shown sub-gamma) is a claim obligation, not available now,
and is not deferred into this entry. The instance given now is the identically-zero process:
S_t=0, V_t=0 for all t (so S_0=V_0=0 and V_t≥0 hold trivially), adapted to the trivial filtration,
with c=0, l_0=1, α=1/2, η=2, m=1 and h(x)=2^(x+1) (so Σ_{k=0}^∞ 1/h(k) = Σ 2^{-(k+1)} = 1, meeting
Theorem 1's own requirement exactly): the constant supermartingale L_t(λ)=1 satisfies EL_0(λ)=1≤l_0
and dominates exp{λ·0−ψ(λ)·0}=1≤1 for every λ≥0, so (S_t,V_t) is genuinely 1-sub-ψ_G, not vacuously
— no hypothesis of Definition 1 is violated or discharged by contradiction. This is a genuine,
degenerate model of the source's own setting (disclosed as such): it exercises every field but is
unrelated to M4, and Theorem 1's conclusion for it is the trivial statement that S_α(V_t∨m)≥0≥S_t
always holds, carrying no M4 consequence.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-04 line); usable only for the one-sided scalar uniform boundary quoted; degenerate zero-process instance disclosed; minor: Definition 1 and the lambda>=0 remark are on p.5, not p.4.

### AX-05  Linear-programming vertex theorem (Bertsimas-Tsitsiklis / Schrijver, standard result)
Source: `bertsimas1997introduction` (Bertsimas and Tsitsiklis, *Introduction to Linear
Optimization*, 1997, Theorem 2.3, Corollary 2.1, Theorems 2.7-2.8, per math's original note) and
`schrijver1986theory` (Schrijver, *Theory of Linear and Integer Programming*, 1986, section 8).
Requested by math (board/inbox/librarian/2026-09-28-lp-vertex-ledger.md, red's review of claim
019) for D5 claims to cite rather than re-prove (AGENTS.md rule 21) the fact that a nonempty
bounded polyhedron has finitely many extreme points, each cut out by m linearly independent active
constraints, and that a linear objective attains its maximum at one of them. Both textbooks are
now status `cited` in `refs/BIBLIOGRAPHY.md` (the human's decision, 2026-09-28): standard results
cited by theorem number, no full text needed — the earlier search for an open copy of either book
(none found; no DOI in Crossref for either, only journal reviews of them) is now moot.
Statement (source notation): not quoted verbatim, per the `cited` convention (no full text is
kept in `refs/text/` to quote from); cited by theorem number as textbook-standard instead.
Statement (our notation), per math's original request and the theorem numbers above (not
independently re-derived from the books' own pages, since no full text is held): for a nonempty
bounded polyhedron P = {x in R^m: g_l'x <= h_l, l=1..L}, (i) P has finitely many extreme points,
each the unique solution of some m linearly independent active constraints among the L, hence at
most C(L,m) of them (Bertsimas-Tsitsiklis Theorem 2.3, Corollary 2.1; Schrijver section 8); (ii)
any affine function on R^m attains its maximum over P at one of these extreme points; this also
relies on P having an extreme point at all when nonempty and bounded (Bertsimas-Tsitsiklis
Theorem 2.6, Corollary 2.2, alongside Theorems 2.7-2.8 for the attainment step itself).
Assumptions in the source: standard LP theory hypotheses — P nonempty and bounded (so that a
maximum exists at all) and the L constraints a finite list of linear inequalities in R^m. Whether
either book states additional regularity conditions (e.g. non-degeneracy) is not independently
checked here, consistent with the `cited` convention of citing by theorem number rather than
verifying every hypothesis against the page.
Simplifications we impose: none stated.
Formal: corrected per the auditor's fail (ledger/AUDIT_LOG.md, 2026-09-28, commit 2505313). The
general theorem quantifies over all m, L and every choice of g_l, h_l, so it is not itself a closed
algebraic proposition in rule 6's sense; math's original framing overstated this. Each concrete
application — once a claim fixes specific m, L, g_l, h_l from M2/M4's action-class geometry — is a
closed algebraic proposition for that instance, and could be proved directly for that instance
without invoking the general theorem at all. The Mathlib check (per the auditor's note, 2026-09-28,
and AGENTS.md rule 21, "never re-proved or re-formalized from scratch") now has an answer: Mathlib
has Krein-Milman (`IsCompact.extremePoints_nonempty`, `closure_convexHull_extremePoints`), from
which part (ii)'s extreme-point-exists-and-attains-the-maximum content follows directly for compact
convex P — no reconstruction needed there. Part (i), the finite basic-solution count
(C(L,m) extreme points, each cut out by m active constraints), is not in Mathlib and has no
Krein-Milman analogue; it is genuinely polyhedron-specific combinatorics. So the route is: cite
Mathlib's Krein-Milman lemmas directly for part (ii)'s existence-and-attainment content (this entry
becomes moot for that half), and for part (i) the choice remains between (a) a general Upstream
hypothesis structure with a genuine instance, similar to AX-01's approach, or (b) proving only the
specific finite instance each claim needs as its own closed algebraic proposition, citing this
entry's general statement as prior art. Left to whichever claim uses it, since under `cited` no
source text will land to resolve it independently of that choice. Claim 020
(provisional/math-finite-faces-iff, per math's note) depends on this entry.
Audit: ok (re-audit), 2026-09-28, under the `cited` convention (ledger/AUDIT_LOG.md, AX-05 lines): the statement is the textbook one at the cited numbers, the assumptions are complete, and no field is stronger than the textbook result. Rule 6 is met through Mathlib or per-instance proofs; an Upstream structure (route (a)) would need its own instance audited when written. Checked from knowledge of the books, not against a registered text. Fixed this turn: part (ii)'s "our notation" now also cites Theorem 2.6/Corollary 2.2 (extreme point existence), and the Formal paragraph's stale "decided once a source lands" is replaced with the Mathlib check's actual answer (Krein-Milman covers (ii); (i)'s basic-solution count does not).

### AX-06  Hoeffding's inequality for bounded iid variables (maurer2009empirical Theorem 1)
Source: `maurer2009empirical`, Theorem 1 ("Hoeffding's inequality"), p.1 (Section 1) of
`refs/text/maurer2009empirical.md`. Registered full text; math's note names this as the source for
D5 claims needing Hoeffding's inequality directly, citing rather than re-proving it (claim 021,
math/claim021-law-free-faces, proves its own loose form and does not depend on this entry, but will
cite it at review). Primary location, now `hoeffding1963probability` is full text (checked against
`refs/papers/hoeffding1963probability.pdf` directly): Theorem 1, inequality (2.3), p.15 (journal
pagination) — the precise iid, common-range `[0,1]` match to this entry's statement: "If X_1,
X_2, ..., X_n are independent and 0 ≦ X_i ≦ 1 for i=1,...,n, then for 0<t<1−μ, Pr{X̄−μ≥t} ≦
... ≦ e^{−2nt²}" (2.1)-(2.3), where μ=EX̄. Setting δ=e^{−2nt²} and solving for t recovers this
entry's confidence-parameterized form exactly. Theorem 2, inequality (2.6), p.16 (checked, math's
earlier location note) generalizes Theorem 1 to independent-not-identically-distributed variables
with per-variable ranges [a_i,b_i]; at a_i=0, b_i=1 for all i it reduces to (2.3), so both are
consistent, but Theorem 1 is the exact match for this entry's iid common-range hypothesis.
Statement (source notation): "Let Z, Z_1, . . . , Z_n be i.i.d. random variables with values in
[0, 1] and let δ > 0. Then with probability at least 1 − δ in (Z_1, . . . , Z_n) we have
EZ − (1/n) Σ_{i=1}^n Z_i ≤ sqrt(ln(1/δ) / (2n))." The paper notes (same page) that this is stated
as a confidence-dependent bound on the deviation (rather than a deviation-dependent bound on the
confidence) because that form is more convenient for its own discussion, that it appears in a
stronger, more general form in Hoeffding's 1963 paper, and that replacing Z by 1−Z gives the
matching lower-tail bound.
Statement (our notation): for any n bounded [0,1]-valued iid random variables (in D5's use: any
[0,1]-valued or affinely rescaled bounded functional of one quarter's observable data, sampled
iid across quarters under M4's law), with probability at least 1−δ the sample mean is within
sqrt(ln(1/δ)/(2n)) of the true mean, one-sided (upper); the lower-tail form follows by the same
substitution the source notes.
Assumptions in the source: Z, Z_1,...,Z_n are i.i.d. and take values in [0,1]; δ>0 (no upper bound
on δ stated, though only δ∈(0,1) gives a nontrivial 1−δ probability); no independence beyond the
iid assumption, no further moment or continuity condition — no parametric family is assumed, unlike
AX-01 through AX-03.
Simplifications we impose: none — the statement above is the source's own, applied verbatim to
n draws; no M4-specific reading beyond substituting M4's observable in place of the source's Z.
Formal: enters `lean/Upstream/HoeffdingIID.lean` as a hypothesis structure (`HoeffdingIID`: the
probability space, `n`, the iid family, `δ`, the one-sided deviation bound), proved for *every*
probability space, every `n ≥ 1`, every iid `[0,1]`-valued family and every `δ ∈ (0,1)` from
Mathlib's own machine-checked Hoeffding inequality (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`
for the sub-Gaussian variance proxy on `[0,1]`-valued variables, and
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` for the tail bound), not
reconstructed from scratch (AGENTS.md rule 21). Since Mathlib supplies the general theorem, the
instance is the faithful model of every field, not a degenerate one; claim 021's provisional
formalization uses this file directly, plus the Chernoff step on iid histories that proof supplies.
The earlier disclosed degenerate instance (n=1, Z=0) is now a special case of `hoeffdingIID`, not
the instance itself, and is no longer needed as the entry's witness.
Audit: ok, 2026-09-28 (ledger/AUDIT_LOG.md, AX-06 lines). The primary-source addition (Hoeffding 1963 Theorem 1, (2.1)-(2.3), p.15; Theorem 2, (2.6), p.16) was re-audited against the scanned PDF and is ok. Clarification: Theorem 1 bounds Pr{X-bar - mu >= t}, so this entry's EZ - mean form needs the Z -> 1 - Z substitution, and Theorem 1 needs only independence, not identical distribution.

### AX-08  Hoeffding's lemma (MGF bound for a bounded random variable)
Source: `rigollet2023high` (Philippe Rigollet and Jan-Christian Hütter, *High-Dimensional
Statistics*, arXiv:2310.19244, 2023), Lemma 1.8 ("Hoeffding's lemma (1963)"), p.21 of
`refs/text/rigollet2023high.md`, with its proof on the same page. Requested by math
(board/inbox/librarian/2026-09-28-hoeffding-lemma-ledger.md, red's rule-21 review of claim 023
(red-passed; correction on math/claim023-corrections)) for the lemma itself, distinct from AX-06
(Hoeffding's inequality for iid sums, from `maurer2009empirical`). Primary location, now
`hoeffding1963probability` is full text (checked against
`refs/papers/hoeffding1963probability.pdf` directly, red's location note 2026-09-28): the lemma is
not a separately numbered result there — it is the intermediate steps (4.15)-(4.16) inside the
proof of Theorem 2, section 4, p.22 (journal pagination): "by Taylor's formula, L(h_i) ≦ L(0) +
L'(0)h_i + (1/8)h_i² = (1/8)h²(b_i−a_i)² (4.15). Hence by (4.12), Ee^{h(X_i−μ_i)} ≦
e^{(1/8)h²(b_i−a_i)²} (4.16)," using L''(h)≤1/4. This matches `rigollet2023high`'s form exactly
(s²(b−a)²/8). `rigollet2023high` remains the cited `refs/text/` source for the verbatim quote
below; `hoeffding1963probability` supplies this corroborating primary location, not a replacement
quote, since it states the bound as an unlabeled proof step rather than a standalone lemma.
Statement (source notation): "Lemma 1.8 (Hoeffding's lemma (1963)). Let X be a random variable such
that E(X) = 0 and X ∈ [a,b] almost surely. Then, for any s ∈ R, it holds E[e^{sX}] ≤ e^{s²(b−a)²/8}.
In particular, X ∼ subG((b−a)²/4)." The proof (same page) defines ψ(s)=log E[e^{sX}], computes
ψ'(s), ψ''(s), observes ψ''(s) is a variance under the exponentially tilted measure dQ=e^{sX}/E[e^{sX}]dP,
bounds that variance by (b−a)²/4 using X∈[a,b] a.s. (via var(X)=var(X−(a+b)/2)≤E[(X−(a+b)/2)²]≤(b−a)²/4),
and integrates twice using ψ(0)=0, ψ'(0)=E[X]=0.
Statement (our notation): for a random variable X with E(X)=0 and X∈[a,b] almost surely (interval
length L=b−a), and any s∈R, E[e^{sX}] ≤ e^{s²L²/8}, i.e. X is sub-Gaussian with variance proxy
L²/4. Claim 023 uses this to bound a centered bounded variable's moment generating function.
Assumptions in the source: X a random variable with E(X)=0 (centered) and X∈[a,b] almost surely for
known a,b; no independence, no iid family (unlike AX-06/AX-07, this is a single-variable statement,
the building block their sums are assembled from). Mathlib's formalization (see Formal) adds the
measure-theoretic scaffolding the source's prose leaves implicit: a probability measure and X
almost-everywhere measurable — genuine hypotheses of the machine-checked statement, not additional
mathematical content, per the auditor's point (a).
Simplifications we impose: none — the statement above is the source's own, applied verbatim.
Formal: per PM's rule-21 reading (board/NOTICES.md, 2026-09-28, "a cited result already proved in
Mathlib enters through Mathlib"), it enters through Mathlib's own machine-checked lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (the same lemma AX-06's `HoeffdingIID.lean`
already cites for the `[0,1]` case; here used at its stated general interval-length form), not
through a project-authored hypothesis structure or a fresh Upstream instance. Claim 023's
formalization uses this Mathlib lemma directly. The lemma is machine-checked regardless of whether
the paper citation above is ever confirmed against Hoeffding's own text; the paper citation exists
so the paper's prose can name a source, per rule 3, not because the formalization depends on it.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-08 line): rigollet2023high Lemma 1.8 quoted verbatim (p.21); Mathlib's hasSubgaussianMGF_of_mem_Icc states the same bound. Fixed the stale "hoeffding1963probability stays unavailable" text this turn and added the primary-source location ((4.15)-(4.16), p.22) now that it is full text; verbatim quote and existing content otherwise unchanged — re-audit of the addition pending.

### AX-09  Le Cam's two-point testing bound (affinity inequalities and Lemma 1 on n-fold products)
Source: `lecam1973convergence` (Lucien Le Cam, *Convergence of Estimates Under Dimensionality
Restrictions*, Annals of Statistics 1(1), 1973), Section 2 ("Testing against remote alternatives"),
p.39-40 of `refs/text/lecam1973convergence.md`; Lemma 1 and its proof are on p.40. Requested by pm
(board/inbox/librarian/2026-09-28-lecam-ledger.md, forwarding red's check) because claims 014-017
and 021 and experiment 012 cite "Le Cam" by name with no ledger entry, which rule 21 wants. Checked
against `refs/papers/lecam1973convergence.pdf` directly (rendered to images and read), not the OCR
text, per pm's instruction that the OCR equations are unreliable.
Statement (source notation): p.39, general definition: for a test function φ and two sets of
probability measures A, B, "π(A, B; φ) = sup{[∫(1−φ)dP + ∫φ dQ]; P∈A, Q∈B}... π(A,B) = inf_φ π(A,B;φ)"
(the least total error probability over all tests), and "D(P,Q) = (1/2)∫|dP−dQ|" (variation
distance). p.40: "It has been shown in [2] that when A and B are dominated families of measures
the number π(A,B) is precisely equal to π(A,B) = 1 − inf{D(P,Q); P∈Ã, Q∈B̃}", where Ã, B̃ are the
convex hulls of A, B — for singletons A={P}, B={Q} this gives π(P,Q) = 1 − D(P,Q). p.40, the
affinity inequalities: "This is related to the affinity ρ = ρ(P,Q) by the inequalities
π² ≦ ρ² ≦ 1 − (1−π)² = π(2−π)." p.40, "LEMMA 1. Let P and Q be two probability measures on
{X,A}. If n^(1/2) H(P,Q) ≦ y ≦ 1 then D(P^n,Q^n) ≦ y(2−y²)^(1/2). Similarly, if nH²(P,Q) ≧ β ≧ 0
then D(P^n,Q^n) ≧ 1−e^(−β)." The proof of the first inequality derives, as a general intermediate
step before substituting the y-bound: "D²(P^n,Q^n) ≦ (1−ρ^(2n)) ≦ 1−(1−y²)² = y²(2−y²)" — i.e.
D²(P^n,Q^n) ≦ 1−ρ^(2n)(P,Q) holds for any n, not only via the stated y-parameterization.
Statement (our notation): for two probability measures P, Q with affinity ρ = ρ(P,Q), and any test
based on n iid draws from either P or Q, the total error probability is at least
π(P^n,Q^n) = 1 − D(P^n,Q^n) ≧ 1 − sqrt(1 − ρ^(2n)) — the two-point testing lower bound: no test
using n observations can separate P from Q with total error below this floor, decaying only
through ρ^(2n), the affinity raised to the sample size. This is the general mechanism claims
014-017 and 021 and experiment 012 use under the name "Le Cam" (a hardness/indistinguishability
result, the negative counterpart to the positive best-arm-identification bounds of AX-01-AX-03).
Assumptions in the source: P, Q probability measures on a common measurable space; for the
π(A,B)=1−D convex-hull identity, A and B dominated families (singletons trivially are); Lemma 1
needs no further structure (no exponential family, no independence beyond the n iid draws it
already specifies via P^n, Q^n).
Simplifications we impose: the "our notation" line above restates D²≦1−ρ^(2n) (the proof's general
intermediate fact) as a one-sided bound on the total error probability via π=1−D; this is a direct
algebraic consequence of the quoted statements, not an added assumption, and does not strengthen
the source's conclusion.
Formal: enters `lean/Upstream` as a hypothesis structure (two probability measures, their
Hellinger distance H or affinity ρ, the sample size n, and the D(P^n,Q^n) bound), parallel to
AX-01's bandit-lower-bound structure but for the hardness/two-point side. Per rule 6, a genuine
instance is two distinct point masses (Bernoulli(1) at two different points, or two distinct
Dirac measures on a two-point space) — trivially probability measures with affinity ρ=0 (disjoint
support), giving the degenerate but genuine case D(P^n,Q^n)=1 for all n (the bound holds with room
to spare); a nontrivial instance (e.g. two Bernoulli(p) laws with p∈(0,1)) is not computed here,
since doing so is the content of whatever claim eventually uses this entry, not this entry's own
obligation. Disclosed as unrelated to M2-M4's specific objects.
Audit: ok, 2026-09-28 (ledger/AUDIT_LOG.md, AX-09 line): quotes checked against the scanned PDF, pp.39-40; minor notes there.

`lecam1973convergence` is otherwise unused beyond this entry, and `roll1978ambiguity` is not cited
by any claim or ledger entry yet (red's check, 2026-09-28), so no further entry is drafted for it.

### AX-10  Discrete-time LQ control with an exogenous Gauss-Markov state (Kalman/LQR separation and Riccati recursion)
Source: `abeille2016lqg` (Abeille, Serie, Lazaric, Brokmann, registered full text): Assumption 1
(Separation Principle, p.9), Theorems 2.1 (Kalman filter, p.6) and 2.2 (LQR/Riccati law, p.7, both
citing Lancaster and Rodman 1995, th.17.5.3 and th.16.6.4 respectively) for the general stationary
average-cost statement, and Theorem 3.1 (p.10) for the relaxation the source proves specifically for
its own portfolio cost matrix (16) (built from Π_Q, Π_dec, Π_exe and risk parameter λ), used when
Theorem 2.2's positive-definiteness hypothesis fails on that model. `garleanu2009dynamic`
(registered full text) Propositions 1-2 (p.9-10) for the closest applied instance, under stationary
predictors and *discounting* rather than Theorem 2.2's undiscounted average-cost criterion — the
two are different objectives, not restated as the same result here.
Requested by math (board/inbox/librarian/2026-09-28-d12-lq-ledger-entry.md) because D12's claims
030-032 (provisional, on separate branches under rule 8) cite this in kind with no ledger entry,
blocking their promotion. Revised twice after the auditor's fails (ledger/AUDIT_LOG.md, 2026-09-28,
commits 3aeb7ec/6a13149 and 8b2aba8/610ea46): (1) the original Formal instance failed Theorem 2.2's
positive-definiteness hypothesis (Gârleanu-Pedersen's example has B≠0, so the state block of its
cost matrix has determinant −(1−ρ)²B²/4 < 0, making the matrix *indefinite*, not merely positive
semi-definite as an earlier revision of this entry wrongly said) — fixed by giving a genuine
positive-definite instance for Theorem 2.2 directly, unrelated to any economic model, and citing
Theorem 3.1 as the tool that applies specifically to `abeille2016lqg`'s own portfolio model (16),
not asserted for general indefinite costs or for Gârleanu-Pedersen's model (which the source does
not itself analyze via Theorem 3.1); (2) "our notation" wrongly asserted a finite-horizon,
time-varying, discounted result neither source states — fixed by restricting to the stationary,
undiscounted, average-cost statement only; (3) `ljungqvist2004recursive` carried no section or
theorem number — dropped, since a wrong or unverifiable page number is worse than no citation
(rule 4).
Statement (source notation): Assumption 1: "The sequence of noises {ϵ^x_t}_{t≥1} and {ϵ^y_t}_{t≥1}
are martingale difference sequences with respect to F_t, conditionally Gaussian with respective
variances Σ_x and Σ_y and mutually independent." Theorem 2.1 (Kalman, steady-state): "Assume that
the noise sequences {ϵ^x_{t+1}}_{t≥1} and {ϵ^y_t}_{t≥1} are conditionally Gaussian and mutually
independent. Assume that the pair (A, Σ_x) is stabilizable and that the pair (C,A) is detectable,
then, the steady-state solution of the Kalman filter is given by: x̃_{t+1} = A(I−LC)x̃_t + Bq_t +
ALy_t, x̂_t = (I−LC)x̃_t + Ly_t, where Ω̃_x = Σ_x + AΩ̃_xA^T − AΩ̃_xC^T(Σ_y + CΩ̃_xC^T)^{−1}CΩ̃_xA^T,
Ω_x = Ω̃_x − LCΩ̃_x, L = Ω̃_xC^T(Σ_y + CΩ̃_xC^T)^{−1}." Theorem 2.2 (LQR, average-cost, undiscounted):
"Let {ϵ^x_t}_{t≥1} be a F_t-martingale difference sequence. Assume that (A,B) is a stabilizable
pair. Assume that the cost matrix [[Q,N],[N^T,R]] is symmetric positive definite, the optimal
solution ... is given by q_t = Kx_t, K = −(R+B^TPB)^{−1}(B^TPA+N^T), P = Q+A^TPA−(A^TPB+N)
(R+B^TPB)^{−1}(B^TPA+N^T), and A+BK is asymptotically stable." Both theorems note "the separation
principle" lets the Kalman and LQR filters "be solved separately." Theorem 3.1: "Assume that the
pair (A,B) is stabilizable and consider the non-stochastic PnL_{t,t+1} = ... then for any risk
parameter λ∈(0,∞) there exists a (necessarily) unique symmetric stabilizing solution P satisfying
(11) if and only if Σ PnL_{t,t+1} ≤ 0 for any q∈RT" (RT the admissible round-trip trade sequences,
Definition 4) — mapping existence of a stabilizing Riccati solution to a non-arbitrage criterion on
round-trip trades, in place of Theorem 2.2's positive-definiteness hypothesis. `garleanu2009dynamic`
Proposition 1: "The model has a unique solution and the value function is given by V(x_t,f_{t+1}) =
−(1/2)x_t'A_xx x_t + x_t'A_xf f_{t+1} + (1/2)f_{t+1}'A_ff f_{t+1} + A_0," with A_xx, A_xf, A_ff
stated explicitly and A_xx positive definite. Proposition 2: "The optimal portfolio is x_t =
x_{t−1} + Λ^{−1}A_xx(aim_t − x_{t−1})," trading at rate Λ^{−1}A_xx toward aim_t = A_xx^{−1}A_xf f_t.
Statement (our notation): for a stationary, undiscounted, average-cost discrete-time control
problem with an exogenous stationary Gauss-Markov state m_t observed through a Kalman filter: (i)
by the separation principle (Assumption 1's hypotheses), the Kalman filter estimating m_t and the
LQR control choosing x_t given the filtered estimate may be solved separately, with no dual effect
(cf. `barshalom1974dual`, registered but not itself ledgered, since no claim cites it directly —
see the D12 FINDINGS entry); (ii) when the LQ cost matrix is strictly positive definite, the
optimal policy is affine in (x_{t−1}, m̂_t) with gain matrix K from a Riccati equation (Theorem
2.2); specifically for `abeille2016lqg`'s own portfolio cost matrix (16) — built from the
state-space output maps Π_Q, Π_dec, Π_exe and a risk parameter λ, not any indefinite or
positive-semi-definite cost matrix in general — Theorem 3.1 instead characterizes existence of the
same kind of stabilizing Riccati solution by a round-trip non-arbitrage criterion. This entry does
not extend Theorem 3.1 beyond that specific model; a claim needing it for a different cost
structure (e.g. `garleanu2009dynamic`'s, whose state block is indefinite, or any other
non-positive-definite cost) must establish its own existence result, not cite Theorem 3.1 as
already covering it. This entry states only the
stationary, undiscounted building block; D12's claims 030-032 need a *finite-horizon, time-varying,
discounted* recursion (A_t = Λ − Λ(Λ+γΣ_t+ρA_{t+1})^{−1}Λ), which is not stated by any source cited
here and is those claims' own new work to justify — including relating a discounted criterion to
the undiscounted average-cost objective these theorems use, which needs its own argument (e.g. a
discount-rate rescaling of the state), not asserted by this entry.
Assumptions in the source: `abeille2016lqg`'s Theorem 2.1 needs (A,Σ_x) stabilizable and (C,A)
detectable, conditionally Gaussian mutually independent martingale-difference noises. Theorem 2.2
additionally needs (A,B) stabilizable and the LQ cost matrix [[Q,N],[N^T,R]] *strictly* positive
definite — not automatically satisfied by portfolio-cost structures (the source's own remark, p.9);
`garleanu2009dynamic`'s cost matrix in particular is indefinite (its state block has determinant
−(1−ρ)²B²/4 < 0 whenever B≠0), not merely positive semi-definite. Theorem 3.1 needs only (A,B)
stabilizable and applies to the source's own portfolio cost matrix (16) specifically — built from
Π_Q, Π_dec, Π_exe and risk parameter λ — replacing positive-definiteness with the round-trip
non-arbitrage condition on that model; the source does not state or prove Theorem 3.1 for any
other indefinite cost matrix. `garleanu2009dynamic`'s Propositions 1-2 assume the same
infinite-horizon, constant-parameter, mean-reverting-factor, *discounted* setting used throughout
that paper — a different objective from Theorem 2.2's undiscounted average cost, not
interchangeable without its own reduction argument.
Simplifications we impose: none stated as source content; the entry now states only what the cited
theorems themselves give, with the finite-horizon/discounted specialization explicitly marked as
left to the claims, not asserted as covered here.
Formal: enters `lean/Upstream` as a hypothesis structure (the state-space (A,B,C,Σ_x,Σ_y), the
stabilizability/detectability hypotheses, the Kalman gain L and Riccati solution Ω̃_x, and either
Theorem 2.2's positive-definite branch with gain K and Riccati solution P, or Theorem 3.1's
non-arbitrage branch restricted to cost matrix (16)), citing `abeille2016lqg` rather than
re-deriving the separation principle or either Riccati/existence result from scratch (AGENTS.md
rule 21). Per rule 6, a genuine instance for Theorem 2.2 (disclosed as unrelated to any economic
model, since no cited source's own economic instance satisfies its strict-positive-definiteness
hypothesis): A=B=1, C=1, Σ_x=Σ_y=1, Q=R=1, N=0, so [[Q,N],[N^T,R]]=I is strictly positive definite
and (A,B)=(1,1) is stabilizable; this is a genuine, non-vacuous instance of Theorem 2.2 exercising
every field. No instance of Theorem 3.1 is given: neither `abeille2016lqg`'s own portfolio model
nor any other cost matrix (16) instance is worked out here, so no claim may cite this entry's
Theorem 3.1 branch as usable until one is given. `garleanu2009dynamic`'s worked example is *not*
used as this entry's Formal instance for either branch, since it satisfies neither Theorem 2.2's
hypothesis (its cost matrix is indefinite) nor is it stated as an instance of cost matrix (16)
(it is a different model, not derived from `abeille2016lqg`'s Π_Q/Π_dec/Π_exe construction).
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, third AX-10 line): quotes, pages and hypotheses match `abeille2016lqg` and `garleanu2009dynamic`. The statement is limited to the stationary average-cost result. Theorem 3.1 is scoped to the source's model (16) and has no instance, so it is unusable by claims until one is given. The Theorem 2.2 instance (A=B=C=1, Σ_x=Σ_y=1, Q=R=1, N=0) is genuine and non-degenerate. The finite-horizon discounted recursion that claims 030-032 need is not covered here.

### AX-11  Perturbation analysis of the discrete algebraic Riccati equation
Source: `konstantinov1993perturbation` (Konstantinov, Petkov, Christov, registered full text):
Theorem 2.1 (existence, uniqueness and analyticity of the perturbed solution near the unperturbed
one, via the implicit function theorem, p.19), Theorem 3.1 (the local linear perturbation estimate
and the absolute/relative condition numbers K_Q, K_A, K_S, K_Σ, valid for ||Δ|| asymptotically
small, p.22), Theorem 3.2 (a non-local, non-linear estimate for symmetric non-negative-definite
perturbations of Q and S, valid on an explicit convex domain D given by inequality (35), p.24) and
Theorem 3.3 (the analogous non-local estimate without the symmetric/non-negative-definite
restriction, valid on an explicit domain given by (40) and (46), p.25-26).
Requested by math (board/inbox/librarian/2026-09-28-d14-konstantinov-ledger-entry.md): claim 033
(D14, provisional/math-m5-plug-in-loss) cites Theorem 2.1's existence/analyticity guarantee and
Theorem 3.1's local linear bound for the stationary discrete Riccati equation that D12/D14's
plug-in policy solves; the claim proves the finite-horizon, time-varying analogue itself and uses
this entry only for the stationary equation (AGENTS.md rule 21).
Statement (source notation): the discrete algebraic matrix Riccati equation (DAMRE) is
X - A^T X A + A^T X B(I_m + B^T X B)^{-1} B^T X A - C^T C = 0, written equivalently as
X - A^T X(I_n + SX)^{-1} A - Q = 0 with S = BB^T, Q = C^T C. "We suppose that the triple (C,A,B)
is regular, i.e. that (C,A) is detectable and (A,B) is stabilizable. This guarantees the existence
of a unique non-negative solution X = P" with closed-loop matrix A_c = A - B(I_m+B^TPB)^{-1}B^TPA
convergent (spectral radius < 1); P is positive definite if (C,A) is observable. For a perturbation
Δ = (ΔQ,ΔA,ΔS) of (Q,A,S) (Frobenius or spectral norm), "since the Frechet derivative of the
left-hand side of (2) in X at X=P is invertible ... then according to the implicit function theorem
we get: Theorem 2.1. The perturbed equation (3) has a unique solution Y = P + ΔP = P(ΔΣ),
ΔΣ=(ΔQ,ΔA,ΔS), in the neighbourhood of P, such that P(0)=P, whose elements are analytic functions
of the elements of the perturbations ΔQ,ΔA,ΔS, at least in certain neighbourhood of the origin
(e.g. for ||Δ|| sufficiently small)." "Theorem 3.1. For small ||Δ|| the estimates (11)-(14) and
(23) are valid, where the condition numbers relative to Q,A,S,Σ are determined or estimated from
(15)-(22)" — (11): ΔP ≤ K_Q ΔQ + K_A ΔA + K_S ΔS + O(||Δ||^2), Δ→0; (23): ΔP ≤
K_Q(1+||PA_c||)^2 Δmax, Δmax = max{ΔQ,ΔA,ΔS}. "Theorem 3.2. Let the matrices Q+ΔQ and S+ΔS be
symmetric and non-negative definite and let the condition (35) be fulfilled. Then the perturbed
equation (3) has a unique solution Y=P+ΔP in the neighbourhood of P such that the estimate (4)
holds" — (35): Δ ∈ D = {Δ : a_1(Δ) + 2[a_0(Δ)a_2(Δ)]^{1/2} < 1}, with a_0,a_1,a_2 given by (33) in
terms of K_Q, ||A||, ||A_c||, ||S||, ||P|| and Δ. "Theorem 3.3. Let the conditions (40) and [b_2(Δ)
> 0, b_1(Δ) + 2[b_0(Δ)b_2(Δ)]^{1/2} < 1, φ(Δ) ≤ ρ_0] be fulfilled ... Then the perturbed equation
(3) has an unique solution Y=P+ΔP in the neighbourhood of P such that the estimate ΔP ≤ φ(Δ)
holds," the non-symmetric analogue of Theorem 3.2, with b_0,b_1,b_2 given by (43)-(45).
Statement (our notation): for the stationary discrete algebraic Riccati equation solved by a
Kalman filter or an LQR/LQG control law with data (A,B,C) (or (A,S,Q) directly) satisfying the
source's regularity condition (detectability of the observation pair, stabilizability of the
control pair): (i) the solution P is well defined, unique and non-negative, and, as an analytic
function of the data, remains well defined and unique (not necessarily non-negative — Theorem 2.1
gives no such guarantee, and it is false in general: at Q=0, A=1/2, S=1 the unperturbed solution is
P=0, and the perturbation ΔQ=-ε gives a local solution Y≈-4ε/3<0) under a sufficiently small
perturbation of any of A, B/S or C/Q (Theorem 2.1). The regularity hypothesis resembles AX-10's
Kalman/LQR hypothesis only in kind (both need a detectability/stabilizability pair), not exactly:
Konstantinov et al.'s DAMRE (1) is itself the LQR (control) Riccati equation, arising, on p.19,
"in the linear-quadratic optimization," normalized to control weight R=I and cross term N=0 (the
Kalman filter's equation is its dual, using A^T, C^T in place of A, B, a reduction the claim must
state, not this entry), and AX-10's Theorem 2.2 branch additionally needs the cost matrix
[[Q,N],[N^T,R]] strictly positive definite — a hypothesis this entry's regularity condition does
not impose (Q=0, A=1/2, B=1 is regular here but has Q not positive definite at all); relating the
two requires the claim's own reduction, not asserted by this entry. An estimated-parameter Riccati
solution built on a consistent plug-in estimate of (A,B,C) is well-defined (not shown non-negative)
near the true P once the estimation error is small enough; (ii) for small enough
estimation error, the perturbation in P is bounded, to first order, by a linear combination of the
perturbations in A, S=BB^T and Q=C^TC with explicit (computable) condition-number coefficients
(Theorem 3.1); this is the "stability of the Riccati solution" step D14 asks for, giving a bound on
||P̂-P|| but not yet on the resulting policy's value loss, which is D14's own claim to derive (by
the standard second-order expansion of the LQR cost in the gain-matrix mismatch, or by citing
`mania2019certainty`'s sharper, directly value-loss-shaped bound built on the same technique). (iii)
Theorems 3.2-3.3 sharpen (ii) to explicit, non-asymptotic domains and bounds, at the cost of
checking an extra scalar inequality on the perturbation size; this entry states them for
completeness but gives no instance, so no claim may cite that branch as usable (rule 6) until one
is worked out.
Assumptions in the source: the base triple (Q,A,S) (equivalently (C,A,B)) must be regular: (C,A)
detectable and (A,B) stabilizable; the source states only that this guarantees a unique
non-negative solution P with convergent closed loop, not that it is necessary — it is not:
A=2, B=1, C=0 has (C,A) not detectable, yet P=3 is the unique non-negative solution with a
convergent closed loop (the other root, P=0, is not stabilizing). Theorem 2.1 needs only this
regularity and ||Δ|| small enough for the implicit function theorem's neighbourhood. Theorem 3.1's
estimate is asymptotic in ||Δ||→0, with no explicit numeric threshold stated for how small is
"small enough" — it is a first-order (linearized) bound, valid without assuming ΔQ, ΔS symmetric or
Q+ΔQ, S+ΔS non-negative definite. Theorems 3.2 and 3.3 give explicit, checkable, non-asymptotic
domains ((35), respectively (40) and (46)) built from K_Q, ||A||, ||A_c||, ||S||, ||P|| and the
perturbation sizes; Theorem 3.2 additionally requires Q+ΔQ and S+ΔS symmetric non-negative
definite (true whenever the DAMRE arises from a state-space (A,B,C) as here), while Theorem 3.3
drops that requirement at the cost of the more complex domain (40),(46).
Simplifications we impose: none; the entry states the source's own hypotheses and conclusions.
Formal: enters `lean/Upstream` as a hypothesis structure (the base data (A,S,Q) or (A,B,C), the
detectability/stabilizability regularity hypothesis, the unperturbed solution P, a perturbation
Δ=(ΔQ,ΔA,ΔS), and the Theorem 2.1 existence/analyticity conclusion together with Theorem 3.1's
linear bound and condition numbers), citing `konstantinov1993perturbation` rather than re-deriving
the implicit-function-theorem argument or the condition-number bound from scratch (AGENTS.md rule
21). Per rule 6, a genuine instance for Theorems 2.1 and 3.1 (disclosed as unrelated to any
economic model, textbook-style degenerate data exercising every field): scalar (n=m=r=1) data
A=0.5, S=1, Q=1 (so B=C=1); (C,A)=(1,0.5) is trivially detectable (A itself is already stable) and
(A,B)=(0.5,1) is trivially stabilizable, so the triple is regular and P is the unique non-negative
root of P - 0.25P/(1+P) - 1 = 0, i.e. P = [0.25+√(0.0625+4)]/2 ≈ 1.133 > 0; a genuine, non-zero
perturbation Δ=(ΔQ,ΔA,ΔS)=(ε,ε,ε) for small ε>0 exercises Theorem 2.1's existence/analyticity
conclusion and Theorem 3.1's asymptotic linear bound (11), with condition numbers K_Q,K_A,K_S
computable from (15)-(22) at this P and A_c. No instance is given for Theorem 3.2 or Theorem 3.3:
checking domain (35) or (40),(46) at specific numeric values is not worked out here, so no claim
may cite either non-local branch as usable until one is given.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-11 line): quotes, pages, the scalar instance and the our-notation statement match `konstantinov1993perturbation`, and the three counterexample points and the DAMRE (1) description are corrected. Theorems 3.2-3.3 have no instance and are unusable until one is given.
### AX-12  Certainty-equivalent LQG control: sub-optimality quadratic in parameter estimation error
Source: `mania2019certainty` (Mania, Tu, Recht, registered full text): Assumption 1 (the cost
matrices Q, R are positive definite, with the WLOG normalization σ_min(R)≥1, p.3), Theorem 3
(stability of the certainty-equivalent LQG interconnection and its sub-optimality gap, quadratic in
the parameter estimation error, p.10), Theorem 4 (the same, specialized using the paper's own
Riccati-perturbation bound, p.10), and Proposition 2 (the Riccati perturbation bound used by
Theorem 4, allowing the cost matrix Q to be perturbed as well as A, B, p.11).
Requested by math (board/inbox/librarian/2026-09-28-d14-mania-ledger-entry.md): claim 033 (D14,
provisional/math-m5-plug-in-loss) cites Theorem 3, Theorem 4 and Proposition 2 in kind for the
stationary limit and the epsilon^2 sub-optimality shape of the plug-in policy; the claim proves its
own finite-horizon identity and bounds inline (AGENTS.md rule 21).
Statement (source notation): the partially observed system is x_{t+1}=A⋆x_t+B⋆u_t+w_t,
w_t~N(0,σ_w²I), y_t=C⋆x_t+v_t, v_t~N(0,σ_v²I), with the LQG objective
min lim_{T→∞} E[(1/T)Σ_{t=0}^T y_t^T Q y_t + u_t^T R u_t]. The optimal solution sets u_t=K⋆x̂_t,
K⋆ the optimal LQR solution to (A⋆,B⋆,C⋆^T Q C⋆,R), x̂_t the Kalman filter estimate with gain L⋆.
Given estimates (Â,B̂,Ĉ,L̂) with max{‖Â-TA⋆T^{-1}‖,‖B̂-TB⋆‖,‖Ĉ-C⋆T^{-1}‖,‖L̂-TL⋆‖}≤ε for some
unitary T, the certainty-equivalent controller is x̂_{t+1}=Âx̂_t+B̂u_t+L̂(y_t-Ĉx̂_t), u_t=K̂x̂_t,
K̂=LQR(Â,B̂,Ĉ^T Q Ĉ,R). "Assumption 1. The cost matrices Q and R are positive definite. Since
scaling both Q and R does not change the optimal controller K⋆, we can assume without loss of
generality that σ(R)≥1" (σ(·) the smallest singular value). "Theorem 3. Suppose that (A⋆,B⋆) is
stabilizable, (C⋆,A⋆) is observable, and that Assumption 1 holds. Let ε be an upper bound on
‖Â-TA⋆T^{-1}‖, ‖B̂-TB⋆‖, ‖Ĉ-C⋆T^{-1}‖, and ‖L̂-TL⋆‖ for some unitary transformation T. Suppose that
assumption (14) holds with parameters TA⋆T^{-1}, TB⋆, T^{-T}C⋆^T Q C⋆T^{-1}, and R and that ε is
sufficiently small so that 3‖C⋆‖_+‖Q‖_+ε≤γ_0 and ε̄≤1, where ε̄:=(7Γ⋆³/σ(R)) f(3‖C⋆‖²_+‖Q‖_+ε). Let
K̂ be defined as in (13), and define N⋆ as N⋆:=[[A⋆+B⋆K⋆, B⋆K⋆],[0, A⋆-L⋆C⋆]], where the pair
(K⋆,L⋆) is optimal for the LQG problem defined by (A⋆,B⋆,C⋆,Q,R). Let γ>0 be such that ρ(N⋆)<γ<1.
Then as long as ε̄≤(1-γ)/(20Γ⋆τ(N⋆,γ)), the interconnection ... using (Â,B̂,Ĉ,K̂,L̂) is stable.
Furthermore, the cost J(Â,B̂,Ĉ,K̂,L̂) satisfies: J(Â,B̂,Ĉ,K̂,L̂)-J⋆ ≤ O(1) max{σ_w²,σ_v²}
(tr(C⋆^T Q C⋆)+tr(R)) τ^6(N⋆,γ)/(1-γ²)³ Γ⋆^6 ε̄²." "Theorem 4. Suppose that (A⋆,B⋆) is
stabilizable, (C⋆,A⋆) is observable, and that Assumption 1 holds. ... Let P⋆=dare(A⋆,B⋆,C⋆^T Q
C⋆,R) and suppose that σ(P⋆)≥1. Let N⋆ be as in (15) and fix γ such that ρ(N⋆)<γ<1. As long as ε
satisfies ε≤(1-γ²)²/τ⁴(N⋆,γ) · 1/(Γ⋆¹¹‖Q‖), we have the following sub-optimality bound:
J(Â,B̂,Ĉ,K̂,L̂)-J⋆ ≤ O(1) max{σ_w²,σ_v²} (tr(C⋆^T Q C⋆)+tr(R)) ‖Q‖²/σ(R)² Γ⋆²⁶ τ¹⁰(N⋆,γ)/(1-γ²)⁵
ε²." "Proposition 2. Let γ≥ρ(L⋆) and also let ε such that ‖Â-A⋆‖, ‖B̂-B⋆‖, and ‖Q̂-Q⋆‖ are at most
ε. Let ‖·‖_+=‖·‖+1. We assume that R≻0, (A⋆,B⋆) is stabilizable, (Q^{1/2},A⋆) observable, and
σ(P⋆)≥1. ‖P̂-P⋆‖ ≤ O(1) ε τ(L⋆,γ)²/(1-γ²) ‖A⋆‖²_+ ‖P⋆‖²_+ ‖B⋆‖_+ ‖R^{-1}‖_+, as long as ε ≤ O(1)
(1-γ²)²/τ(L⋆,γ)⁴ ‖A⋆‖^{-2}_+ ‖P⋆‖^{-2}_+ ‖B⋆‖^{-3}_+ ‖R^{-1}‖^{-2}_+ min{‖L⋆‖^{-2}_+, ‖P⋆‖^{-1}_+}." In
Proposition 2, L⋆ := A⋆+B⋆K⋆ (Section 2's LQR closed-loop matrix, source l.145), *not* the Kalman
gain of Section 3 that also happens to be called L⋆ there — the two uses of "L⋆" are the source's
own overload across sections, not this entry's.
Statement (our notation): for a stationary, partially observed, discrete-time LQG control problem
with unknown (A⋆,B⋆,C⋆) and known cost matrices (Q,R) satisfying Assumption 1 (both positive
definite), where (A⋆,B⋆) is stabilizable and (C⋆,A⋆) is observable: (i) given a plug-in estimate
(Â,B̂,Ĉ,L̂) of the true (A⋆,B⋆,C⋆,L⋆) accurate to within ε (in the sense of (12), up to an unknown
unitary change of basis), the certainty-equivalent controller built from that estimate is stable
and its long-run average cost exceeds the optimal cost by an amount that scales as O(ε²) once ε is
small enough (Theorem 3, and Theorem 4's more explicit specialization using Proposition 2's Riccati
perturbation bound); this is the plug-in policy's value-loss bound D14 asks for, directly in the
shape D14 needs (a bound on realized cost minus optimal cost, not merely on the Riccati solution's
own perturbation). (ii) The bound requires ε small enough that an explicit, stated (though
algebraically involved) threshold holds — the theorems do not claim the O(ε²) rate for all ε, only
once ε is below a problem-dependent size — and its constant depends on Γ⋆ and τ(N⋆,γ) (quantities
that measure how close the closed-loop and observer dynamics are to instability), so the bound can
be loose or require very small ε when those quantities are large; this "how small is small enough,
and how large is the resulting bound at calibrated scale" question is D14's own evaluation to run,
not settled by this entry. (iii) Theorem 3/4's ε is a single, already-fixed bound on parameter
error (holding with certainty, or with high probability from an outside estimation guarantee); nothing
in this entry makes ε itself a time-uniform, shrinking, martingale-dependent quantity tied to a
Kalman posterior that keeps updating across quarters — supplying and justifying such an ε, and
combining the result with a time-uniform confidence sequence (`howard2021time`, AX-04), is D14's
own new content, not given here (matching the D14 literature sweep's conclusion, board/FINDINGS.md).
Assumptions in the source: Theorem 3 needs (A⋆,B⋆) stabilizable, (C⋆,A⋆) observable, Assumption 1
(Q,R positive definite, σ_min(R)≥1 WLOG), and an outside Riccati-perturbation guarantee of the form
(14) (a function f with ‖P̂-P⋆‖≤f(γ') whenever the perturbation is at most γ', for perturbations
that may also move Q); Theorem 4 additionally needs P⋆=dare(A⋆,B⋆,C⋆^T Q C⋆,R) with σ_min(P⋆)≥1
(stated as WLOG achievable by rescaling Q,R when R≻0 and (Q^{1/2},A⋆) is observable) and uses
Proposition 2 to supply (14) explicitly. Proposition 2 needs R≻0, (A⋆,B⋆) stabilizable,
(Q^{1/2},A⋆) observable, and σ_min(P⋆)≥1; unlike AX-11's Theorem 3.1 (which bounds only the
Riccati solution's own perturbation and needs stabilizability/detectability of the base triple),
Proposition 2 needs the stronger pair (Q^{1/2},A⋆) observable and gives a bound with an explicit,
checkable (not merely asymptotic) threshold on ε.
Simplifications we impose: none; the entry states the source's own hypotheses and conclusions.
Formal: enters `lean/Upstream` as a hypothesis structure (the true data (A⋆,B⋆,C⋆,Q,R,σ_w²,σ_v²),
the stabilizability/observability/Assumption-1 hypotheses, the optimal (K⋆,L⋆,P⋆,Σ⋆), the matrix
N⋆ and a γ with ρ(N⋆)<γ<1, a perturbation bound ε and the Theorem 3/Theorem 4 sub-optimality
conclusion), citing `mania2019certainty` rather than re-deriving the certainty-equivalence
sub-optimality argument or the Riccati perturbation bound from scratch (AGENTS.md rule 21). Per
rule 6, a genuine instance (disclosed as unrelated to any economic model): scalar (n=m=r=1) data
A⋆=0.5, B⋆=1, C⋆=1, Q=1, R=1, σ_w²=1, σ_v²=1; (A⋆,B⋆)=(0.5,1) is trivially stabilizable and
(C⋆,A⋆)=(1,0.5) trivially observable (both scalar, nonzero), and Assumption 1 holds with σ(R)=1≥1.
Solving the scalar DARE P=A⋆²PR/(R+B⋆²P)+C⋆²Q gives P⋆² -0.25P⋆ -1=0, so
P⋆=[0.25+√(0.0625+4)]/2≈1.1328>0, and σ(P⋆)=P⋆≈1.1328≥1 (no rescaling needed). K⋆=
-(R+B⋆²P⋆)^{-1}B⋆P⋆A⋆≈-0.2656, giving A⋆+B⋆K⋆≈0.2344 (stable). By the same scalar equation with
(A⋆,C⋆,σ_w²,σ_v²) in place of (A⋆,B⋆,R,Q) — self-dual at these numbers — the filter covariance
Σ⋆≈1.1328 and L⋆=-A⋆Σ⋆C⋆(C⋆²Σ⋆+σ_v²)^{-1}≈-0.2656, giving A⋆-L⋆C⋆≈0.7656 (stable). Hence
N⋆=[[A⋆+B⋆K⋆,B⋆K⋆],[0,A⋆-L⋆C⋆]]≈[[0.2344,-0.2656],[0,0.7656]] is upper triangular with eigenvalues
0.2344 and 0.7656, so ρ(N⋆)≈0.7656<1; γ=0.8 satisfies ρ(N⋆)<γ<1. (The filter update here follows
the source's own (11a), x̂_{t+1}=Âx̂_t+B̂u_t+L̂(y_t-Ĉx̂_t), giving A⋆-L⋆C⋆≈0.7656; the other, standard-
predictor sign convention for the same numbers would instead give ≈0.2344 — γ=0.8 dominates either
way.) Proposition 2's own γ≥ρ(L⋆) uses Section 2's L⋆:=A⋆+B⋆K⋆≈0.2344 (not the Kalman gain of
Section 3, which the entry's Statement also calls L⋆, following the source's own overload), and
γ=0.8≥0.2344 satisfies it. With T=1 (the only unitary scalar) and a genuine, non-zero perturbation
ε>0 taken small enough for the stated thresholds (3‖C⋆‖_+‖Q‖_+ε≤γ_0 for Theorem 3; the explicit
rational bound in Γ⋆,τ(N⋆,γ),‖Q‖,σ(R) for Theorem 4; the explicit rational bound in Proposition 2
using Section 2's L⋆), this instance exercises every field of Theorem 3,
Theorem 4 and Proposition 2: a regular LQG instance, a computed N⋆ and admissible γ, and a genuine
small perturbation. The exact numeric value of the smallness threshold is not computed here (as
with AX-11's asymptotic branch), since the theorems' own conclusions are conditional on it, not on
any specific numeric ε this entry must supply.
Audit: ok (re-audit), 2026-09-28 (ledger/AUDIT_LOG.md, AX-12 line): quotes, pages and the scalar instance match `mania2019certainty`. Proposition 2's L⋆ is now Section 2's A⋆+B⋆K⋆, and the source's (11b) sign convention is disclosed. Stationary average-cost result only, for a fixed ε below a problem-dependent threshold that contains unspecified O(1) constants.

### AX-13  Polyhedral KKT: optimality of a concave objective over a polyhedron via the normal cone
Source: `rockafellar1970convex` (Rockafellar, *Convex Analysis*, Princeton, 1970): Theorem 27.4
(a point maximizes a concave function over a convex set iff zero lies in the sum of the function's
superdifferential at that point and the set's normal cone there — sufficiency holds unconditionally,
but necessity, that an optimal point always admits such a multiplier, needs a constraint
qualification: the relative interior of f's effective domain must meet the convex set's relative
interior) and Theorems 28.2-28.3 (specializing this to a polyhedral convex set, giving the
condition as an explicit finite system of sign and complementary-slackness conditions on the active
linear constraints' multipliers; polyhedrality weakens the qualification needed for necessity to
the relative interior of f's domain meeting the polyhedron itself, not its relative interior, but
some such condition is still needed — it is not dispensed with entirely). Status `cited` in
`refs/BIBLIOGRAPHY.md` (this session,
per PM's note): a standard textbook result, cited by theorem number, no full text held.
Requested by pm (board/inbox/librarian/2026-09-29-polyhedral-kkt-entry.md) for claim 104's part 0
(D15's criterion (c)), which proves inline a multiplier characterization of the joint optimum of a
concave (quadratic-minus-piecewise-linear-cost) objective over a box-and-budget polyhedron; per
AGENTS.md rule 21 and lean's note (board/inbox/lean/2026-09-29-claim104-option-a.md, PM's option
(a)), this is a known general theorem and claim 104 (and claim 102's part 1, per mathb's note) is
to cite this entry and check only its hypotheses, rather than re-derive the normal-cone argument.
Statement (source notation): not quoted verbatim, per the `cited` convention (no full text is held
to quote from); cited by theorem number as textbook-standard, following the same convention already
used for AX-05 (`bertsimas1997introduction`/`schrijver1986theory`).
Statement (our notation), per the standard convex-analysis content of the cited theorem numbers
(not independently re-derived from the book's own pages, since no full text is held, exactly as
AX-05 states for its own textbook sources): for a concave function f (possibly non-differentiable,
e.g. smooth-minus-a-convex-piecewise-linear-cost) on R^n and a nonempty polyhedron
F = {x in R^n : Ax <= b} (box bounds and any further linear inequalities, such as a funded-cash
constraint, are both instances of this form), a point x* in F maximizes f over F if and only if
there exist multipliers eta_l >= 0 for each constraint l, with eta_l = 0 whenever the l-th
constraint is slack (complementary slackness), such that 0 is in the superdifferential of f at x*
minus the sum of eta_l times the l-th constraint's gradient (i.e., zero lies in ∂f(x*) - A'eta, the
sum of the function's supergradient and the polyhedron's normal cone at x*, per Theorem 27.4) —
provided the relative interior of f's effective domain meets F (Theorem 28.2's polyhedral
relaxation of the general qualification, which needs the relative interior of F). When f is finite
everywhere on R^n (dom f = R^n, so its relative interior is all of R^n), this condition holds
automatically for any nonempty F, which is claim 104's and claim 102's own case; the sqrt(x)-type
example where a boundary point of dom f has an empty superdifferential, and so no multiplier can
exist there even though the point is optimal, does not arise for such an f. For a separable box
constraint 0 <= x_i <= barx_i on each coordinate, this specializes coordinate by
coordinate to: the i-th supergradient component is zero when 0 < x_i < barx_i, at most zero when
x_i = 0, and at least zero when x_i = barx_i (the standard box-KKT sign pattern) — this is exactly
claim 104 part 0's R_i sign conditions, with T_i(x) supplying the piecewise-linear cost's own
subdifferential (a nonempty interval at a kink, a single point elsewhere) as the non-smooth part of
∂f(x*), and eta as the funded-cash constraint's own multiplier.
Assumptions in the source: f concave (possibly non-smooth, possibly taking the value -infinity
outside its effective domain) on R^n; F a nonempty polyhedron (finitely many linear inequalities);
and, for the necessity direction (an optimal point admits a multiplier), the relative interior of
f's effective domain must meet F — this is the constraint qualification Theorem 28.2's polyhedral
case needs, weaker than the general Theorem 27.4's (which needs the relative interior of F, not F
itself), but not absent. When dom f = R^n (f finite everywhere, as in claim 104's and claim 102's
own use), this condition is automatic. Whether the book states further conditions not used here is
not independently checked, consistent with the `cited` convention of citing by theorem number
rather than verifying every hypothesis against the page.
Simplifications we impose: none stated.
Formal: enters `lean/Upstream` as a hypothesis structure (a concave f given as a supergradient
correspondence, or a smooth part plus a convex piecewise-linear cost's subdifferential; the
polyhedron F's defining inequalities; a candidate x* and multipliers eta; the zero-in-normal-cone
conclusion), citing `rockafellar1970convex` rather than re-deriving the normal-cone/KKT argument
from scratch (AGENTS.md rule 21). Per rule 6, a genuine instance (disclosed as unrelated to any
economic model, though it borrows claim 104's own notation): scalar (n=1) f(x) = mu*x -
(gamma/2)x^2 - C(x - x^-) with mu=gamma=1, x^-=1, kappa^+=0.3, kappa^-=0.2 (so
C(u) = 0.3 u^+ + 0.2 u^-), and box F_1=[0,2]. The unconstrained-in-x^- kink sits at x*=1: for
x>1, f'(x)=0.7-x<0 near x=1 (decreasing); for x<1, f'(x)=1.2-x>0 near x=1 (increasing); so x*=1 is
optimal, with supergradient interval [-0.3,0.2] containing 0. In claim 104's own notation,
g(1)=mu-gamma*1=0, T(1)=[-kappa^-,kappa^+]=[-0.2,0.3], and with the cash multiplier eta=0 (taken
slack, a genuine non-binding value of that field, not a degenerate skip), R=g(1)-0-1*t=-t=0 for
t=0 in T(1) — the interior case (0<x*<2), matching claim 104's own R_i=0 sign exactly. A second
instance, same data but F_2=[0,0.8] (the cap now binds below the kink): f is increasing throughout
[0,0.8] (f'(x)=1.2-x>0.4>0 there), so x*=0.8, T(0.8)={-0.2} (single-valued, since 0.8<x^-), and
with eta=0, R=g(0.8)-0-1*(-0.2)=(1-0.8)+0.2=0.4>=0, matching claim 104's own "at least zero when
x_i=barx_i" boundary case exactly. Together the two instances exercise the interior-kink case (a
genuine non-vacuous supergradient interval, not a single differentiable point) and the
upper-boundary case of the box-KKT sign pattern; the cash constraint's own multiplier eta is
exercised only at its slack value eta=0 here (a genuine, not vacuous, instance of that field, since
eta=0 with a slack constraint is a real case the theorem covers, not a degenerate one) — a fuller
instance with eta>0 (the cash constraint actually binding) is left to whichever claim needs it,
per the same practice already used for AX-05's own textbook entry.

Fixed this revision: the title and the Source, our-notation and Assumptions paragraphs now state
the actual constraint qualification (ri(dom f) meets ri F in general, or F itself when F is
polyhedral, per Theorem 28.2) instead of claiming none is needed; each notes that f finite
everywhere on R^n (claim 104's and claim 102's own case) supplies it automatically, and gives the
auditor's sqrt(x)/F={x<=0} counterexample as the case where it fails. Re-audit pending.
Audit: ok (re-audit), 2026-09-29 (ledger/AUDIT_LOG.md, second AX-13 line), `cited` convention (no text compared): the theorem numbers, the constraint qualification (ri(dom f) meets F for polyhedral F, automatic for f finite on R^n), the our-notation statement and both instances are right. Claims 104 and 102's finite f satisfies the qualification.

### AX-14  Submodularity on products of chains and its preservation under partial minimization (topkis1978minimizing Theorems 3.1-3.2 and 4.3)
Source: `topkis1978minimizing` (Donald M. Topkis, Minimizing a Submodular Function on a Lattice,
Operations Research 26(2), 1978, 305-321; status `text`, full text at
`refs/text/topkis1978minimizing.md`, converted from the PDF with OCR glyph errors noted below):
Section 3 (definitions, refs/text lines 225-246, pp. 309-310), Theorem 3.1 (line 248, p. 309),
Theorem 3.2 (line 259, p. 310) and Theorem 4.3 (line 432, p. 314, Section 4). Drafted by mathb
per PM's revision note on claim 108 (rule 21): claim 108's proof of part 2 used these results
as its Lemmas A and C, proved inline; it now cites this entry and checks only the hypotheses.
Statement (source notation): quoted verbatim from the OCR text, with "?" standing for the
inequality sign of the PDF and "A", "v" for the lattice meet and join, "X" for the product.
- Definition, lines 226-229: "Suppose f is a real-valued function on a lattice S. If f(x A Y) +f(x v y) ?f(X) +f(y) (3) for all x and y in S, then f is submodular on S. If f(x A y) +f(x v y) < f(x) +f(y) for all unordered x and y in S, then f is strictly submodular on S."
- Definition, lines 232-235: "Suppose X and T are posets and f is a real-valued function on S C X X T. If f(x, z) -f(x, t) is isotone, antitone, strictly isotone, or strictly antitone in x on S_z ∩ S_t for each t<z in T, then f has, respectively, isotone differences, antitone differences, strictly isotone differences, or strictly antitone differences in (x, t) on S."
- Definition, lines 240-246: "[S a sublattice of a product of lattices S_1 x ... x S_n,] f is a real-valued function on S. If, on S, f has isotone differences, antitone differences, strictly isotone differences, or strictly antitone differences in (x_j, x_k) for all j != k with each x_i fixed for i != j and i != k, then f has, respectively, isotone differences, antitone differences, strictly isotone differences, or strictly antitone differences on S. Multiplication by a positive scalar and the addition of functions preserve each of the properties defined above."
- Theorem 3.1 (line 248): "If S_i is a lattice for i = 1, ..., n, S is a sublattice of X_{i=1}^n S_i, and f is (strictly) submodular on S, then f has (strictly) antitone differences on S."
- Theorem 3.2 (line 259): "If S_i is a chain for i = 1, ..., n and f has (strictly) antitone differences on X_{i=1}^n S_i, then f is (strictly) submodular on X_{i=1}^n S_i." (The source adds, line 274, that the result is not valid for the product of a countable collection of chains.)
- Theorem 4.3 (line 432): "If X and T are lattices, S is a sublattice of X X T, f is submodular on S, S_t is the section of S at t ∈ T, and g(t) = inf_{x ∈ S_t} f(x, t) is finite on the projection Π_T S, then g(t) is submodular on Π_T S." Its proof (lines 436-441) is the three-line lattice argument: (x v y, t v b) and (x A y, t A b) lie in S, so g(t v b) + g(t A b) <= f(x v y, t v b) + f(x A y, t A b) <= f(x, t) + f(y, b), then take infima.
Statement (our notation): a *product of intervals* D = I_1 x ... x I_m (each I_i a real interval) with the coordinatewise order is a sublattice of R^m, x ^ y and x v y the coordinatewise minimum and maximum; each I_i is a chain. A function F on D is *submodular* if F(x ^ y) + F(x v y) <= F(x) + F(y) for all x, y in D, and has *decreasing differences* in the pair (i, j) if, with the other coordinates fixed, F(s_2, t_2) - F(s_1, t_2) <= F(s_2, t_1) - F(s_1, t_1) whenever s_1 <= s_2 and t_1 <= t_2 (the source's "antitone differences in (x_i, x_j)"). Then: (i) (Theorem 3.2) if F has decreasing differences in every pair of coordinates on D, F is submodular on D; in particular a function of one coordinate is submodular, a function of two coordinates with decreasing differences in them is submodular, and sums of such functions (and nonnegative multiples) are submodular (the source's closing sentence of the definitions). (ii) (Theorem 3.1) if F is submodular on D, it has decreasing differences in every pair of coordinates. (iii) (Theorem 4.3) if X and Y are products of intervals, F is submodular on X x Y and V(x) = inf_{y in Y} F(x, y) is finite for every x in X, then V is submodular on X; when Y is compact and F continuous the infimum is attained, so finiteness is automatic.
Assumptions in the source: Theorems 3.1 and 3.2 need each factor a lattice, respectively a chain, and finitely many factors (n finite; the source's countable-product counterexample); Theorem 3.1 needs S a sublattice of the product; Theorem 4.3 needs X and T lattices, S a sublattice of X x T, f submodular on S and the infimum finite on the projection. All functions are real-valued. Nothing else is assumed (no continuity, convexity or compactness in the source).
Simplifications we impose: finitely many real intervals as the chains (Theorem 3.2's hypothesis) and products of intervals as the lattices, sublattices being the products themselves (S = X x T in Theorem 4.3, so the projection is X and every section is Y); the infimum attained by continuity on a compact Y, which gives the source's finiteness; only the non-strict versions. Each is a special case of the source's hypotheses and does not strengthen the conclusion.
Formal: an Upstream hypothesis structure (rule 6, rule 21) with two fields, for functions on products of real intervals given by index type and bounds: `pairwise_submodular` (Theorem 3.2: decreasing differences in every pair of coordinates implies submodular, with Theorem 3.1's converse as a further field if a claim needs it) and `min_submodular` (Theorem 4.3: F submodular on X x Y with the infimum over Y attained for every x gives V submodular on X). Genuine instance: X = Y = [0, 1] and F(x, y) = -x y. Decreasing differences: the increment F(x_2, y) - F(x_1, y) = -(x_2 - x_1) y is nonincreasing in y, so F is submodular by the first field (and directly: for x = (s_2, t_1), y = (s_1, t_2), -s_1 t_1 - s_2 t_2 <= -s_2 t_1 - s_1 t_2 since (s_2 - s_1)(t_2 - t_1) >= 0). The infimum over y in [0, 1] is attained at y = 1, V(x) = -x, a function of one chain variable, submodular. The instance is non-degenerate (a nonzero cross term) and exercises both fields. Use: claim 108's proof of part 2 takes the entry for Lemma A (ii) and (iv) and Lemma C; its Lemma B (a convex function of a difference has decreasing differences) and the induction stay proved in the claim.
Audit: ok, 2026-09-29 (ledger/AUDIT_LOG.md, AX-14 line for ef742763), against `refs/text/topkis1978minimizing.md`: the definitions, Theorems 3.1, 3.2 and 4.3, and the countable-product remark are quoted correctly with the right line and page numbers. The our-notation specializations to finite products of real intervals are special cases of the source's hypotheses. The instance -xy on [0,1]² is genuine and exercises both fields.

### AX-15  The one-instrument small-cost band: the first corrector equation's explicit solution (cube-root half-width, centred on the target)
Source: `soner2013homogenization` (Soner, Touzi, *Homogenization and asymptotics for small transaction costs*, SIAM J. Control Optim. 51(4), 2013; full text at refs/text/soner2013homogenization.md), Section 4, equations (4.3)-(4.5) and Lemma 8.2: the first corrector equation of the one-risky-asset problem is solved explicitly by a quartic in the fast variable rho with a symmetric no-trade interval [-rho_0, rho_0]; and `muhlekarbe2017primer` (Muhle-Karbe, Reppen, Soner, *A primer on portfolio choice with small transaction costs*, 2017, arXiv:1612.01302; full text at refs/text/muhlekarbe2017primer.md), Section 4.4, equations (4.10)-(4.13): the same explicit solution in the primer's notation, with the asymptotically optimal no-trade region (4.13). Both texts held in full; status `text` in `refs/BIBLIOGRAPHY.md`.
Requested by math (this entry drafted by math per PM's note board/inbox/math/2026-09-29-claim042-hold.md, rule 21) for claim 042 part 3, which had proved the law inline; the sources state the constant, so the claim cites this entry and checks its hypotheses.
Statement (source notation, `soner2013homogenization`): with the candidate corrector w-bar(rho) = k_4 rho^4 + k_2 rho^2 + k_1 rho on [rho_1, rho_0] and linear outside, "k_4 = -sigma^2/(12 alpha-bar^2) and k_2 = a-bar/alpha-bar^2"; smooth pasting (C^2 at rho_0 and rho_1) gives "rho_0^2 = rho_1^2 = 2 a-bar/sigma^2 implying that a-bar >= 0 and rho_0 = -rho_1 = (2 a-bar/sigma^2)^{1/2}" (4.3); continuity of the first derivatives gives "4 k_4 rho_0^3 + 2 k_2 rho_0 + k_1 = -lambda_{0,1}, 4 k_4 rho_1^3 + 2 k_2 rho_1 + k_1 = lambda_{1,0}", hence "k_1 = (lambda_{1,0} - lambda_{0,1})/2"; and "a-bar = (sigma^2/2) rho_0^2 and rho_0 = (3 alpha-bar^2 (lambda_{1,0} + lambda_{0,1})/(4 sigma^2))^{1/3}" (4.4), with the gradient constraint "-lambda_{1,0} <= w-bar_rho <= lambda_{0,1}" (4.5) verified. Lemma 8.2 restates the transaction region's width for power utility as 2 xi_0 = ((6/gamma)(lambda_{0,1} + lambda_{1,0}))^{1/3} (pi_M (1 - pi_M))^{2/3} (the rates in the numerator; the auditor read the PDF, p. 26, the OCR's stacked fraction having misled the first quote), "exactly the same as equation (3.13) in Janecek and Shreve". Remark 3.3 gives the first corrector equation its stochastic representation as an ergodic (long-run average) control problem, which is the reading used here. Orientation: the source's gradient constraint (4.5), -lambda_{1,0} <= w-bar_rho <= lambda_{0,1}, is oriented opposite to its (4.1) (the fast variable's sign convention differs between the two displays); the mapping below follows (4.1), so that kappa^+ <-> lambda_{0,1} and the constraint reads -kappa^+ <= w' <= kappa^- in our orientation. (`muhlekarbe2017primer` (4.10)-(4.12): "c_4 = sigma_S^2 v_zz/(12 alpha^2) and c_2 = -a/alpha^2", "a = (sigma_S^2 v_zz/2) Delta xi^2" (4.11), "Delta xi = (-(v_z/v_zz) 3 alpha^2/(2 sigma_S^2))^{1/3}" (4.12) for the symmetric interval (-Delta xi, Delta xi) with unit rates lambda on each side, i.e. round trip 2 lambda; the asymptotic no-trade region is |y - theta| <= lambda^{1/3} Delta xi (4.13).)
Statement (our notation): for the ergodic (first-corrector) problem of a scalar gap y driven by a Brownian innovation of variance v per unit time, holding cost (c/2) y^2 per unit time, and proportional rates kappa^+ for pushing y up and kappa^- for pushing it down, a solution of the first corrector equation is the quartic w(y) = -(c/(12 v)) y^4 + (lambda/v) y^2 + ((kappa^- - kappa^+)/2) y on the band, extended linearly outside (Soner-Touzi construct it and verify (4.5); they do not study uniqueness, which `possamai2015homogenization` Theorem 3.1 / Corollary 6.1 supplies, named here, no entry), with

    Delta^3 = 3 (kappa^+ + kappa^-) v / (4 c),    lambda = c Delta^2 / 2,    band [-Delta, Delta] centred on the target,    -kappa^+ <= w' <= kappa^-,

the average cost lambda and the band being independent of the split of the round-trip rate between the two sides (only w's odd term carries the asymmetry). The mapping: sigma^2 <-> c (the holding cost's curvature), alpha-bar^2 <-> v (the fast variable's variance), lambda_{1,0} + lambda_{0,1} <-> kappa^+ + kappa^-, a-bar <-> lambda, rho_0 <-> Delta; in the primer, (4.12) reads Delta xi^3 = (-v_z/v_zz)(3 alpha^2/(2 sigma_S^2)) for unit rates on each side (round trip 2 lambda), so with the quadratic tracking problem's curvature c in place of sigma_S^2 (-v_zz)/(-v_z) and the fast variable's variance v in place of alpha^2 it is Delta^3 = 3 (2 lambda) v/(4 c), the same constant 3/4 per unit of round-trip rate.
Assumptions (to check in an instance): the holding cost is exactly quadratic in the gap with constant curvature c; the innovation is Brownian with constant variance v per unit time; the rates are constant; the problem is the corrector (ergodic, long-run average) problem, not the finite-horizon discrete one. What the entry does not give: the identification of a discrete-review, finite-horizon band with this Delta (the sources' expansion theorems concern their continuous-time value functions; the discrete-to-corrector step is a separate, uncited claim), the band's centre at the next order, or the multidimensional case (`possamai2015homogenization`, a separate entry if needed).
Instances: claim 042 part 3 (three one-instrument reductions of the fund's problem with one ETF, each with a quadratic tracking loss and a constant-variance innovation, at the corrector level); refuted claim 101's constant (8c) is corrected to 4c by (4.4).
Audit: ok, 2026-09-29 (ledger/AUDIT_LOG.md, the AX-15 line for 2fc9b304; the draft f74f30be failed on the Lemma 8.2 quote, now fixed). The quotes of Soner-Touzi (4.3)-(4.5), (4.4) and Lemma 8.2 (rates in the numerator, as in the PDF) and of the primer's (4.10)-(4.13) are verbatim. The our-notation law and mapping are right (σ² ↔ c, ᾱ² ↔ v, κ⁺ ↔ λ0,1, following (4.1) and Remark 3.3). "A solution", with uniqueness from Possamaï-Soner-Touzi (audited as AX-16), and the (4.5) orientation note are correct. The explicit solution is proved as claim 042's own algebraic lemma (rule 6).
Fixed this revision (math, same day): Lemma 8.2 re-quoted with the rates in the numerator; "the corrector" weakened to "a solution" with the uniqueness source named; the orientation sentence on (4.5) against (4.1) added; Remark 3.3 cited for the ergodic reading; the explicit solution is now also proved as claim 042's own algebraic lemma (rule 6), the entry carrying the sources' framework. Re-audit pending.

### AX-16  Small-cost correctors in several dimensions: existence and comparison for the first corrector equation (possamai2015homogenization)
Source: `possamai2015homogenization` (Possamaï, Soner, Touzi, registered full text): Theorem 3.1
(comparison for the first corrector equation, in any dimension), Corollary 6.1 (uniqueness of the
eigenvalue a that follows from Theorem 3.1), Theorem 3.2 (existence of a convex, C^{1,1} corrector
solution w, whose non-contact set O0 = {rho : Dw(rho) in int(C)} is open and bounded, C the
polytope of admissible one-sided rates), Theorem 3.3 (the rescaled value difference
u-bar^epsilon := (v-v^epsilon)/epsilon^2 converges locally uniformly to u, the solution of the
*second* corrector equation (2.6) — the leading-order O(epsilon^2) correction to the frictionless
value, not a statement that v^epsilon itself converges to v). Equation (4.1), in the paper's
numerical Section 4, *recalls* (a formal first-order approximation, recalled from the formal
asymptotics of Section 2, not proved as a theorem in this paper) a first-order approximation of the
no-transaction region as the frictionless target plus an epsilon-scaled copy of O0, used to drive
the numerical scheme — presented as a recollection, not proved by Theorem 3.3 or anywhere else in
this paper. The paper itself is explicit that O0's reading as the optimal control problem's actual
no-trade region is *not established*: Remark 3.1 defines the associated ergodic control problem
J(M) and states "it is not clear whether the corresponding potential function... satisfies the
growth condition... For this reason, we cannot use this probabilistic representation," and Remark
6.2 says the paper cannot identify an optimal control from the regularity it obtains. Example 3.1 /
equation (3.1) gives the special case lambda^{i,j} = infinity for i, j both different from 0 (only
cash trades allowed), reducing the corrector to a sum of one-dimensional solutions from [44]
(Soner-Touzi, i.e. AX-15's own source). The one-dimensional explicit half-width formula
(soner2013homogenization (4.4), muhlekarbe2017primer (4.10)-(4.12)) is AX-15's entry, not restated
here; this entry is cut to the multidimensional part, per PM's note
(board/inbox/librarian/2026-09-29-ax-number-d15e.md).
Requested by math (board/inbox/librarian/2026-09-29-d15e-corrector-entry.md) for D15e's second
claim (the multidimensional bundling-band order with a costly ETF), which will cite the
multidimensional existence/characterization result rather than re-derive it (AGENTS.md rule 21).
Statement (source notation): "Suppose w1 is a viscosity subsolution of (2.5) with eigenvalue a1 and
that w2 is a viscosity supersolution of (2.5) with eigenvalue a2. Assume further that
lim_{|rho|->infinity} w1(rho)/delta_C(rho) <= 1 <= lim_{|rho|->infinity} w2(rho)/delta_C(rho). Then,
a1 <= a2" (Theorem 3.1). "There is at most one a in R such that (2.5) has a viscosity solution w
satisfying the growth condition w(rho)/delta_C(rho) -> 1, as |rho| -> infinity" (Corollary 6.1,
"an immediate consequence" of Theorem 3.1). "There exists a solution w in C^{1,1} of the equation
(2.5) with eigenvalue a, satisfying the growth condition ... Moreover, w is convex and positive.
The set O0 := {rho in R^d, Dw(rho) in int(C)} is open and bounded, w in C^infty(O0) and
w(rho) = inf_{y in O0} {w(y) + delta_C(rho-y)}, for all rho in R^d" (Theorem 3.2). With
u-bar^epsilon(s,x,y) := (v(s,z)-v^epsilon(s,x,y))/epsilon^2 (equation (3.2)), "the sequence
{u^epsilon}_{epsilon>0} ... converges locally uniformly to the function u" defined in (2.6), the
second corrector equation (Theorem 3.3) — i.e. v^epsilon = v - epsilon^2 u + o(epsilon^2), u itself
the object characterized, not v^epsilon converging to v. "We recall that a first order approximation
of the no-transaction region, for fixed s ... is deduced from the free boundary set O0 of
Proposition 3.2 by: NT-hat^epsilon(s) := {(x,y) in R^{d+1} : y = theta(s,z) + epsilon eta(s,z) O0}"
(equation (4.1), Section 4.1, "we recall" — a formal first-order approximation recalled from the
formal asymptotics of Section 2, not proved as a theorem in this paper), theta the frictionless
optimal policy, eta an auxiliary scale factor. "It is not clear whether the corresponding potential
function, which is the candidate for a solution to (2.5), satisfies the growth condition
w_infinity ~ delta_C. For this reason, we cannot use this probabilistic representation" (Remark
3.1, on the ergodic control problem J(M) it defines just before).
Statement (our notation): in any dimension, the first corrector equation of an ergodic
singular-control problem of the kind these sources solve — tracking a diffusion state against a
curved (locally quadratic) frictionless target under one-sided proportional costs on each
coordinate — has at most one eigenvalue a admitting a solution with the stated growth (Theorem 3.1,
Corollary 6.1) and an existing, convex, C^{1,1} corrector solution w (Theorem 3.2) whose
*non-contact set* O0 = {Dw in int C} — the region where the PDE's obstacle constraints are not
active — is open, bounded and characterized as the interior-gradient set against the polytope of
one-sided rates. The paper does *not* establish that O0 is the optimal no-trade region of any
actual control problem: it defines a natural candidate ergodic control problem (Remark 3.1) but
states explicitly that it cannot verify the growth condition needed to connect the corrector to
that problem's own value, and (Remark 6.2) cannot identify an optimal control from the regularity
it proves. A claim wishing to read O0 as this lab's own no-trade region must establish that
connection itself, not cite Theorem 3.2 for it. The paper's Theorem 3.3 characterizes only the
leading-order *value* correction (v^epsilon = v - epsilon^2 u + o(epsilon^2), u the second
corrector), not the no-trade region's own shape or its control-theoretic meaning. The claim that
the leading-order no-trade region is the frictionless target plus an epsilon-scaled copy of O0 is
equation (4.1), introduced in the paper's numerical section as a *recollection* from the paper's
own Section 2 formal asymptotics, not proved as a theorem anywhere in this paper; a claim citing
that shape must attribute it to (4.1) as an unproved recollection, not to Theorem 3.2, Theorem 3.3,
or as this paper's own established result. No closed form is available in general (the paper's own
numerical Section 4 is needed for explicit multidimensional examples; AX-15 is the one-dimensional
closed form). This is the "multidimensional corrector... explicit only in special cases" content
D15e's second claim is to cite (Theorems 3.1-3.2/Corollary 6.1 for the proved
existence/uniqueness/non-contact-set-shape content, (4.1) and the O0-as-no-trade-region reading
only as unproved recollections if used at all) rather than re-derive; whether this lab's own
two-instrument (fund, ETF) case admits a closed form, an established no-trade-region reading, and
what either is, is that claim's own content, not given here.
Assumptions in the source: Theorem 3.1 (comparison) and Theorem 3.2 (existence) are stated for the
corrector equation (2.5) itself, whose own standing hypotheses are ellipticity of the diffusion
coefficient (alpha-bar alpha-bar^T >= c1 I_d, from Assumption 3.1 applied to alpha) and
lambda^{i,j} >= 0, lambda^{i,i} = 0 (the cost structure's own definition, general setup preceding
(2.5)); they do not themselves invoke the full bundle of Assumptions 3.1-3.4. Only Theorem 3.3 (the
value expansion) is stated "under Assumptions 3.1, 3.2, 3.3, and 3.4" explicitly — the Merton value
function's smoothness and the corrector's own comparison/local-boundedness/regular-dependence
conditions — not independently re-verified here since D15e's second claim states its own hypotheses
when it applies this machinery.
Simplifications we impose: cash-only trading (lambda^{i,j} = infinity for all i, j both different
from the cash index 0, i.e. transfers are allowed only to and from cash, not between the d risky
positions directly) is the source's own special case, Example 3.1 / equation (3.1), under which the
corrector reduces to a sum of one-dimensional solutions (AX-15's own case); it is not this entry's
own simplification and is not assumed unless a claim invokes Example 3.1 specifically. Otherwise
none stated. Note on sign: the registered text's printed equation (2.5) has the running-cost term
as +|sigma rho|^2/2 (positive sign), the opposite sign from Soner-Touzi's one-dimensional corrector
equation (4.1) (AX-15's source), which has -(1/2)sigma^2 rho^2 (negative sign); this entry does not
resolve which orientation is a typographical slip in one of the two papers, and, since it gives no
specific numeric instance (below), it does not need to. Any claim instantiating this entry's
machinery with concrete numbers must state and verify its own sign convention directly against
equation (2.5) as printed in refs/text/possamai2015homogenization.md, not assume it matches AX-15's.
Formal: enters `lean/Upstream` as a hypothesis structure (the corrector equation's data: dimension
d, the diffusion coefficient alpha-bar satisfying ellipticity, the cost polytope C with
lambda^{i,j} >= 0; the eigenvalue a, its uniqueness, and the corrector w; the non-contact set O0,
disclosed as not established to be any control problem's own no-trade region), citing
`possamai2015homogenization` rather than re-deriving the corrector/homogenization argument from
scratch (AGENTS.md rule 21). Per rule 6: the corrector equation's existence and uniqueness are
guaranteed abstractly by Theorem 3.2 and Corollary 6.1 for any admissible instance data of
dimension d >= 1 satisfying the ellipticity and lambda >= 0 hypotheses, but no specific d >= 2
numeric example is worked out here, and this entry gives no instance for equation (2.5) at all
(disclosed above as unrelated to AX-15's own d=1 instance, given the unresolved sign question); the
paper's own Section 4 numerical example (d=2, CRRA utility) is not reproduced or independently
verified, so no claim may cite a specific multidimensional closed form, or a specific numeric
instance, from this entry — only the qualitative existence/uniqueness/non-contact-set-shape content
of Theorem 3.2 and Corollary 6.1, which is what D15e's second claim is to use, together with the
explicit disclosure that O0's reading as an actual no-trade region is this lab's own claim to
establish, not the source's.
Audit: ok, 2026-09-29 (ledger/AUDIT_LOG.md, the AX-16 line for 8f1ba509; earlier drafts e35f5f45 and 5f29fc5c failed and are fixed). The quotes of Theorems 3.1-3.3, Corollary 6.1, (3.2), (4.1) and Remark 3.1 are verbatim. O0 is correctly stated as the non-contact set of (2.5), not an established no-trade region (Remarks 3.1, 6.2). The hypotheses of Theorems 3.1-3.2 versus Theorem 3.3 are split correctly, and cash-only trading is identified as Example 3.1. The Upstream structure still needs an instance of every field (rule 6), with its sign convention stated against (2.5).

### AX-17  The Kalman recursion is the best linear (MMSE) predictor generally, the exact Bayes posterior only under Gaussian noise (Kalman's Corollary 1, via uhlmann2022gaussianity)
Source: `uhlmann2022gaussianity` (Uhlmann, Julier, registered full text), tracing and quoting
Kalman's own original paper's Corollary 1, and Ho and Lee's alternate Bayesian derivation.
Requested by pm (board/inbox/librarian/2026-09-29-ax-filter-entries.md) for claim 112 part 2 (D17),
which resolves the difference between M5's exact Gaussian Bayesian law and M7's finite-law linear
filter; per AGENTS.md rule 21 (red's correction), the claim is to cite this entry rather than assert
the distinction unsourced.
Statement (source notation): "In Kalman's original paper he derived his now-eponymous filter from
the perspective of l2-norm error minimization via othogonal [sic] projections. He also noted (his
Corollary 1) that if all errors are assumed Gaussian then the system mean-and-covariance estimate
can be interpreted as parameterizing a Gaussian distribution that represents the exact error
distribution conditioned on the sequence of observations. In more contemporary parlance, Kalman
derived a minimum-mean-squared error (MMSE) optimal filter. What is critical to note, however, is
that the MMSE optimality of the filter does not in any way depend on such an assumption." "From
this Ho and Lee provided an alternate proof of Kalman's corollary that the Kalman filter is
Bayes-optimal with all mean and covariance estimates interpreted as parameters for Gaussian
densities corresponding to assumed-Gaussian error processes. Under these assumptions a mean and
covariance estimate from the Kalman filter does not just represent the first two moments of an
otherwise unknown probability distribution, it can be interpreted as the exact uncertainty
distribution for the state."
Statement (our notation): for the standard linear-Gaussian-form state/observation recursion (state
transition and observation both linear, noises zero-mean with finite, known first and second
moments), the Kalman recursion's mean-and-covariance sequence (i) is the minimum-mean-squared-error
estimator among *affine* (linear) functions of the observations, for any noise laws with the stated
finite moments, Gaussian or not — this holds by the least-squares/orthogonal-projection derivation
alone, needing no distributional assumption beyond the moments. This is the source's own looser
statement, "the Kalman Filter is MMSE-optimal without any assumptions of Gaussianity," restricted
to affine estimators: unrestricted (MMSE over *all* estimators, not just affine ones), the claim is
false in general — the entry's own instance below has a nonlinear estimator (tanh(y)) with strictly
lower mean-squared error than the affine one. (ii) Sufficiency: if the noises and any non-degenerate
prior on the initial state are genuinely Gaussian, the recursion's mean and covariance are exactly
the Bayesian posterior mean and covariance — the full conditional law of the state given the
observations is exactly Gaussian with that mean and covariance (Kalman's Corollary 1, Ho-Lee's
Bayesian re-derivation). This entry does *not* assert the converse: Gaussianity is not shown to be
necessary for the affine estimate to equal the exact posterior mean, and it is not necessary in
general — with theta ~ Gamma(a,1) and centred-Gamma noise (epsilon = G - b, G ~ Gamma(b,1)
independent of theta), the exact posterior mean E[theta|y] = a(y+b)/(a+b) equals the affine
(Kalman-form) estimate exactly, with neither theta nor epsilon Gaussian (the posterior *variance*
in that example is not the recursion's constant value, so the full-distribution statement is
untouched, but that is not sourced either and is not claimed here). What the entry does give,
non-vacuously (Formal, below): a genuine instance — a symmetric two-point (non-Gaussian) prior on
theta with Gaussian observation noise — where the affine estimate and the exact posterior mean
*do* differ, showing sufficiency is not vacuous and that equality is not automatic in general. So
claim 112 part 2a may say m_t *can* differ from the exact posterior theta_hat^B_t at some histories
under a non-Gaussian law (witnessed by this entry's instance), not that it must differ whenever the
law is non-Gaussian (the gamma example shows it need not).
Assumptions in the source: (i) needs only that the noises have finite, known first and second
moments (zero mean is the standard normalization); no independence beyond uncorrelatedness, no
distributional family; "MMSE-optimal" here means optimal among affine estimators only. (ii) is
stated by the source only as a sufficient condition: "if all errors are assumed Gaussian then" the
estimate parameterizes the exact conditional law (Corollary 1); Ho and Lee's re-derivation likewise
proves the filter "Bayes-optimal ... corresponding to assumed-Gaussian error processes." Neither
passage states or is used here to assert necessity.
Simplifications we impose: none stated.
Formal: enters `lean/Upstream` as a hypothesis structure (the state/observation model's linear
maps and noise moments; a boolean or prior-law field distinguishing the Gaussian and general
cases; the linear-MMSE recursion as always available; the exact-posterior conclusion gated on the
Gaussian case), citing `uhlmann2022gaussianity` (and, through it, Kalman's original paper and
Ho-Lee) rather than re-deriving either the orthogonal-projection or the Bayesian argument from
scratch (AGENTS.md rule 21). Per rule 6, a genuine instance (disclosed as unrelated to any economic
model) exercising both branches: scalar state theta with a symmetric two-point prior
theta in {-1, +1} each with probability 1/2 (mean 0, variance 1, *not* Gaussian), one observation
y = theta + epsilon, epsilon ~ N(0, 1) independent of theta. (i) The linear MMSE estimate needs
only the first two moments of theta (mean 0, variance 1) and of epsilon (mean 0, variance 1):
m_lin(y) = Cov(theta,y)/Var(y) * y = (1/(1+1)) y = y/2, e.g. m_lin(1) = 0.5. (ii) The exact Bayes
posterior mean, computed directly from the two-point prior and the Gaussian likelihood ratio
p(y|theta=1)/p(y|theta=-1) = exp(2y) (from completing the square in the two Gaussian densities),
is theta_hat^B(y) = tanh(y), e.g. theta_hat^B(1) = tanh(1) ≈ 0.7616 != 0.5 = m_lin(1) — a genuine,
verified numeric instance in which the linear estimate and the exact posterior mean differ, because
the state's own prior is not Gaussian even though the observation noise is. A companion instance in
which the two agree exactly is AX-18's own instance (Gaussian prior, Gaussian noise).
Audit: ok, 2026-09-29 (ledger/AUDIT_LOG.md on main, commit 0b4c6315, AX-17 line).

### AX-18  The conjugate scalar Gaussian update is the exact posterior for a static state under Gaussian noise (murphy2007conjugate)
Source: `murphy2007conjugate` (Murphy, registered full text), Sections 2.1-2.3: the Bayesian
derivation (likelihood times prior, completing the square) of the exact posterior for a Gaussian
prior on an unknown, static (non-time-varying) mean, given Gaussian observations of it.
Requested by pm (board/inbox/librarian/2026-09-29-ax-filter-entries.md) for claim 112 part 2 (D17):
AX-10 covers only the steady-state Kalman filter under stabilizability, which fails for a static
state (A=1, no process noise, since there is no decaying dynamics to reach a steady state); this
entry supplies the exact finite-horizon/sequential posterior for that static case instead.
Statement (source notation): "Let D = (x_1,...,x_n) be the data. The likelihood is
p(D|mu,sigma^2) = prod_i p(x_i|mu,sigma^2) = (2 pi sigma^2)^{-n/2} exp{-1/(2 sigma^2) sum_i
(x_i-mu)^2}" (eq. 1), reduced to "p(D|mu) prop exp{-n/(2 sigma^2)(xbar-mu)^2} prop
N(xbar|mu,sigma^2/n)" (eq. 10, "n observations with variance sigma^2 and mean xbar is equivalent to
1 observation x_1=xbar with variance sigma^2/n"). "The natural conjugate prior has the form
p(mu) prop exp{-1/(2 sigma_0^2)(mu-mu_0)^2} prop N(mu|mu_0,sigma_0^2)" (eq. 12). "Hence the
posterior is given by p(mu|D) prop p(D|mu,sigma) p(mu|mu_0,sigma_0^2)... Since the product of two
Gaussians is a Gaussian, we will rewrite this in the form... = exp{-1/(2 sigma_n^2)(mu-mu_n)^2}"
(eqs. 13-17), with, working in precisions lambda=1/sigma^2, lambda_0=1/sigma_0^2, lambda_n=1/sigma_n^2,
"p(mu|D,lambda) = N(mu|mu_n,lambda_n), lambda_n = lambda_0 + n lambda, mu_n = (xbar n lambda +
mu_0 lambda_0)/lambda_n = w mu_ML + (1-w) mu_0" (eqs. 28-30).
Statement (our notation): for a *static* (time-invariant) unknown state theta with Gaussian prior
N(m_0, P_0), observed through a sequence of conditionally independent Gaussian observations
y_i = theta + epsilon_i, epsilon_i ~ N(0, sigma^2) i.i.d. (no process noise, no state transition:
theta itself does not evolve between observations), the posterior after n observations is exactly
Gaussian, N(m_n, P_n), with P_n^{-1} = P_0^{-1} + n/sigma^2 and
m_n = P_n (m_0/P_0 + n ybar/sigma^2), ybar the sample mean of y_1,...,y_n — precision simply adds
with each observation, and this holds exactly (not merely as a linear-MMSE approximation) because
both the prior and the likelihood are genuinely Gaussian (AX-17's exact-posterior branch). Applied
one observation at a time (n=1 at each step, ybar=y_1), this is the sequential/finite-horizon
update claim 112's M8 uses for its diagonal blocks: P_1 = (P_0^{-1} + diag(1/sigma_f^2,
1/sigma_A^2))^{-1} is exactly this formula applied coordinatewise (each diagonal block an
independent scalar instance of this entry).
Assumptions in the source: the prior on the unknown mean is Gaussian, the observation noise is
Gaussian and independent (both across observations and of the prior), and the observation variance
sigma^2 is known (the source treats the unknown-variance case separately, not used here). The state
being estimated is static — the source's model has no dynamics or process noise at all, matching
PM's "fixed means, A=1, no process noise" request exactly, and is a different (simpler) setting
than AX-10's stationary, dynamically-evolving state.
Simplifications we impose: none stated; the vector, diagonal-covariance case (independent scalar
coordinates) used by claim 112 is the direct coordinatewise product of this scalar entry, not a
further simplification of the source's own (scalar) content.
Formal: enters `lean/Upstream` as a hypothesis structure (the static state, its Gaussian prior
(m_0,P_0), the i.i.d. Gaussian observation noise variance sigma^2, a sequence of n observations;
the exact posterior (m_n,P_n) via the precision-addition recursion), citing `murphy2007conjugate`
rather than re-deriving the Gaussian conjugacy argument from scratch (AGENTS.md rule 21). Per rule
6, a genuine instance (disclosed as unrelated to any economic model): scalar theta, m_0=0, P_0=1,
sigma^2=1, one observation y_1=2 (n=1, ybar=2). Then P_1^{-1} = 1/1 + 1/1 = 2, so P_1 = 0.5, and
m_1 = 0.5*(0/1 + 1*2/1) = 0.5*2 = 1 — a genuine, non-degenerate posterior (P_1 < P_0, m_1 strictly
between m_0=0 and the observation y_1=2, as the precision-weighted average requires), exercising
every field of the formula. This instance is the Gaussian-prior companion to AX-17's non-Gaussian
counterexample: here the linear estimate and the exact posterior mean coincide exactly, since both
the prior and the noise are genuinely Gaussian.
Audit: ok, 2026-09-29 (ledger/AUDIT_LOG.md on main, AX-18 line).

### AX-19  The Rockafellar-Uryasev tail measure: VaR as the left quantile and CVaR as the minimum of F_beta(alpha) = alpha + E[(loss - alpha)^+]/(1 - beta) (rockafellar2000optimization)
Source: `rockafellar2000optimization` (Rockafellar, Uryasev, registered full text): definitions (2)-(4)
and Theorem 1 (with (5)-(8)), and the sample formula (9).
Requested by math for claim 049 (D25): the quantile flexibility test pairs a quantile of the
shortfall with a tail-expectation loss bound, and the claim uses the minimization formula as the
tail measure's definition on a finite law rather than re-deriving a tail bound (AGENTS.md rule 21).
Statement (source notation): "The underlying probability distribution of y in R^m will be assumed
for convenience to have density, which we denote by p(y)" and "We assume however in what follows
that the probability distributions are such that no jumps occur, or in other words, that Psi(x,
alpha) is everywhere continuous with respect to alpha. This assumption, like the previous one about
density in y, is made for simplicity. Without it there are mathematical complications, even in the
definition of CVaR, which would need more explanation." The beta-VaR is "alpha_beta(x) = min {alpha
in R : Psi(x, alpha) >= beta}" (2) and the beta-CVaR is the conditional expectation of the loss at or
above alpha_beta(x) (3). "F_beta(x, alpha) = alpha + (1 - beta)^{-1} integral [f(x, y) - alpha]^+ p(y)
dy" (4). "Theorem 1. As a function of alpha, F_beta(x, alpha) is convex and continuously
differentiable. The beta-CVaR of the loss associated with any x in X can be determined from the
formula phi_beta(x) = min_alpha F_beta(x, alpha) (5). In this formula the set consisting of the
values of alpha for which the minimum is attained, namely A_beta(x) = argmin_alpha F_beta(x, alpha)
(6), is a nonempty, closed, bounded interval (perhaps reducing to a single point), and the beta-VaR
of the loss is given by alpha_beta(x) = left endpoint of A_beta(x) (7)." The sampled form "F~_beta(x,
alpha) = alpha + (1/(q(1 - beta))) sum_{k=1}^q [f(x, y_k) - alpha]^+" (9) "is convex and piecewise
linear with respect to alpha". The paper notes that "the assumption that there is a joint density of
instrument returns can be relaxed" and leaves it "for a subsequent paper".
Statement (our notation): for a loss Y and a level 1 - eps in (0, 1), the tail measure T_eps(Y) =
min_c [c + E(Y - c)^+/eps] is the minimum of a convex function of c; under a continuous law it
equals the conditional expectation of Y above its (1 - eps)-quantile, the quantile being the left
endpoint of the minimizing interval (Theorem 1). On a finite law (this lab's revision states) the
expectation is the atoms' weighted sum, the sampled form (9) with the atoms' probabilities in
place of 1/q; Theorem 1's identification with the conditional tail expectation is proved in the
source only under its continuity assumption, so a claim on a finite law may use the formula as
the tail measure's definition (as claim 049 does) but not the conditional-expectation reading
without further citation (the source defers the general case). Registered from the full text.
Assumptions in the source: the loss's law has a density and its distribution function is
continuous in the threshold (no atoms), assumed "for simplicity" and used in the proof of Theorem
1; the loss f(x, y) is a deterministic function of the decision x and the uncertainty y; the level
beta lies in (0, 1). The source states that the density assumption "can be relaxed" and defers the
general case to a subsequent paper, which is not registered.
Simplifications we impose: none of the source's content is simplified; the lab restricts itself to
the formula F_beta (4), in its finite-law form (9) with the states' probabilities, and does not
invoke Theorem 1's conditional-expectation identification, whose continuity hypothesis a finite
law violates.
Formal: does not enter any Lean statement. Claim 049 defines T_eps by the formula and evaluates it
directly under its quantile condition (a two-line computation on the finite law), so no
`lean/Upstream` hypothesis structure is needed; Theorem 1 is cited for the pairing of the quantile
with the tail measure only.
Audit: ok, 2026-09-30 (ledger/AUDIT_LOG.md on main, AX-19 line; re-keyed after these paragraphs were added).

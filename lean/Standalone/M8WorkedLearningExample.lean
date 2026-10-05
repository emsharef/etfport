import Standalone.M7TwoReviewsBindingBudget

/-!
# Claim 112: one consistent worked learning example (M8)

Statement only; the proof is `Novel/M8WorkedLearningExampleProof.lean`.

The model is M8 (`model/SPEC.md`) in its own coordinates.
- The filter is scalar by block: prior variance `p`, noise variance `s`, gain `k = p/(p + s)`, posterior
  variance `(1 - k) p` and update `m + k (y - m)`.
- The predictive moments are `mu_t` and `Sigma_t` from the loadings `b_A, b_E`, the drag `c^E`, the
  shock variances and the belief `(lambda_hat, alpha_hat, p^lambda, p^alpha)`.
- A finite law for one block is a finite prior on `theta` with weights `w` and a finite centred noise
  law with weights `v`.
- The two-review problem on M8's finite tree is claim 044's program (`Two`). The review-1 nodes are
  the states, with their probabilities, the gross returns `1 + r` as marking, the filtered
  predictive moments at each node, and the deterministic `Sigma_1`.

Scope (PM, rule 6b: lean's split confirmed, with option (i) for 1d, i.e. claim 044 in depends_on). Formal: 1a, 1b, 1c, 1d under the finite law (the
two-review existence through claim 044 with `h⁻_0 > 0`), 2a's moment content and non-coincidence
condition with red's counterexample and node A's alpha block as exact instances, part 3's
slack-budget threshold, and Table 2's exact values. Paper-level:
- 2a's two meanings, AX-17 and AX-18, which are cited;
- 2b-2c and part 3's transfer table, which are readings;
- the Gaussian-law statements;
- part 4's tree computations (Tables 3-6) and the Checks.
1d is stated as a nonempty feasible set: a marked holding above its cap is sold down to it, as in the
approved text.
-/

namespace Standalone.M8WorkedLearningExample

open Standalone.M7TwoReviewsBindingBudget

noncomputable section

/-! ### The filter, by block -/

/-- The gain `k = p/(p + s)`. -/
def gain (p s : ℝ) : ℝ := p / (p + s)

/-- The posterior variance `(1 - k) p`. -/
def postVar (p s : ℝ) : ℝ := (1 - gain p s) * p

/-- The filter's update `m + k (y - m)`. -/
def filt (m p s y : ℝ) : ℝ := m + gain p s * (y - m)

/-- Part 1a: the posterior variance is positive, depends on `(p, s)` only, and satisfies the
information form `1/p_1 = 1/p_0 + 1/s`. -/
def Beliefs : Prop :=
  ∀ p s : ℝ, 0 < p → 0 < s → 0 < postVar p s ∧ 1 / postVar p s = 1 / p + 1 / s

/-! ### Predictive moments -/

/-- M8's known inputs: loadings, drag and the shock variances. -/
structure Inputs where
  bA : ℝ
  bE : ℝ
  cE : ℝ
  sf2 : ℝ
  sA2 : ℝ
  sE2 : ℝ

/-- The predictive mean `mu_t = (b_A lambda_hat + alpha_hat, b_E lambda_hat - c^E)`. -/
def muP (I : Inputs) (lh ah : ℝ) : Fin 2 → ℝ := ![I.bA * lh + ah, I.bE * lh - I.cE]

/-- The predictive covariance `Sigma_t = G P_t G' + Sigma_r`. -/
def SigP (I : Inputs) (pl pa : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![I.bA ^ 2 * (I.sf2 + pl) + I.sA2 + pa, I.bA * I.bE * (I.sf2 + pl)],
    ![I.bA * I.bE * (I.sf2 + pl), I.bE ^ 2 * (I.sf2 + pl) + I.sE2]]

/-- Positive definiteness of a quadratic form. -/
def PosDefQ {ι : Type} [Fintype ι] (S : ι → ι → ℝ) : Prop := ∀ v : ι → ℝ, v ≠ 0 → 0 < quad S v

/-- Part 1b: `Sigma_t` is symmetric and positive definite whenever the belief variances and
`sigma_f^2` are nonnegative and `sigma_A^2, sigma_E^2 > 0`. The frictionless target
`x* = (gamma Sigma_t)^{-1} mu_t` is well defined: `gamma Sigma_t x = mu_t` has exactly one solution. -/
def PredRisk : Prop :=
  ∀ (I : Inputs) (pl pa lh ah γ : ℝ), 0 ≤ I.sf2 → 0 < I.sA2 → 0 < I.sE2 → 0 ≤ pl → 0 ≤ pa → 0 < γ →
    PSD (SigP I pl pa) ∧ PosDefQ (SigP I pl pa) ∧
      ∃! x : Fin 2 → ℝ, ∀ i, γ * ∑ j, SigP I pl pa i j * x j = muP I lh ah i

/-! ### Marking and funding under the finite law -/

/-- Part 1c: with positive gross returns, marking maps nonnegative holdings to nonnegative
holdings (cash is unchanged by definition). -/
def Marking : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), (∀ z i, 0 < P.g z i) →
    ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → ∀ z i, 0 ≤ carry P z x i

/-- A review's feasible set from pre-trade holdings `c` and cash `k`. -/
def RevSet {ι Z : Type} [Fintype ι] (P : Two ι Z) (c : ι → ℝ) (k : ℝ) : Set (ι → ℝ) :=
  {x | Box P x ∧ 0 ≤ k - ∑ i, (x i - c i) - cost P (x - c)}

/-- A review's objective with predictive moments `(mu, S)`. -/
def revObj {ι Z : Type} [Fintype ι] (P : Two ι Z) (mu : ι → ℝ) (S : ι → ι → ℝ) (c : ι → ℝ)
    (x : ι → ℝ) : ℝ :=
  Qv mu S P.gamma x - cost P (x - c)

/-- Part 1d, one review under the finite law. From any nonnegative pre-trade holdings (possibly above
a cap after marking) and nonnegative cash, the feasible set is nonempty. With a positive definite
predictive covariance, the review problem has exactly one optimum. -/
def ReviewFunding : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (c : ι → ℝ) (k : ℝ), (∀ i, 0 ≤ c i) → 0 ≤ k →
      (RevSet P c k).Nonempty ∧
      ∀ (mu : ι → ℝ) (S : ι → ι → ℝ), PSD S → PosDefQ S →
        ∃! x, x ∈ RevSet P c k ∧ IsMaxOn (revObj P mu S c) (RevSet P c k) x

/-- M8's finite public tree at review 1: node probabilities and the first quarter's returns. -/
structure Nodes (Z : Type) where
  q : Z → ℝ
  f : Z → ℝ
  rA : Z → ℝ
  rE : Z → ℝ

/-- M8's review data: prior beliefs, preferences, rates, caps, incumbents and cash. -/
structure Setup where
  lh0 : ℝ
  ah0 : ℝ
  pl0 : ℝ
  pa0 : ℝ
  gamma : ℝ
  beta : ℝ
  kp : Fin 2 → ℝ
  km : Fin 2 → ℝ
  xbar : Fin 2 → ℝ
  xm : Fin 2 → ℝ
  h : ℝ

/-- M8's finite-law two-review problem as claim 044's program. The states are the review-1 nodes,
marking is by the gross returns, the review-1 moments are the filter's at each node, and `Sigma_1`
is deterministic. -/
def toTwo {Z : Type} (I : Inputs) (U : Setup) (T : Nodes Z) : Two (Fin 2) Z where
  q := T.q
  g := fun z => ![1 + T.rA z, 1 + T.rE z]
  mu0 := muP I U.lh0 U.ah0
  S0 := SigP I U.pl0 U.pa0
  mu1 := fun z => muP I (filt U.lh0 U.pl0 I.sf2 (T.f z))
    (filt U.ah0 U.pa0 I.sA2 (T.rA z - I.bA * T.f z))
  S1 := fun _ => SigP I (postVar U.pl0 I.sf2) (postVar U.pa0 I.sA2)
  gamma := U.gamma
  beta := U.beta
  kp := U.kp
  km := U.km
  xbar := U.xbar
  xm := U.xm
  h := U.h

/-- M8's finite-law standing assumptions. -/
def FiniteLaw {Z : Type} (I : Inputs) (U : Setup) (T : Nodes Z) : Prop :=
  0 ≤ I.sf2 ∧ 0 < I.sA2 ∧ 0 < I.sE2 ∧ 0 < U.pl0 ∧ 0 < U.pa0 ∧ 0 < U.gamma ∧ 0 < U.beta ∧
    U.beta ≤ 1 ∧ 0 < U.h ∧ (∀ z, 0 < T.q z) ∧ (∀ z, 0 < 1 + T.rA z ∧ 0 < 1 + T.rE z) ∧
    ∀ i, 0 ≤ U.kp i ∧ 0 ≤ U.km i ∧ U.km i < 1 ∧ 0 ≤ U.xm i ∧ U.xm i ≤ U.xbar i

/-- Part 1d, two reviews under the finite law. M8's tree satisfies claim 044's hypotheses (with
`h⁻_0 > 0`), so an optimal policy exists, and the root problem with the continuation `β E V_1` is a
concave maximization over the root polyhedron. The review-1 predictive covariance is positive
definite. -/
def TreeFunding : Prop :=
  ∀ (Z : Type) [Fintype Z] (I : Inputs) (U : Setup) (T : Nodes Z), FiniteLaw I U T →
    Hyp (toTwo I U T) ∧ (∃ X, Optimal (toTwo I U T) X) ∧
      ConcaveOn ℝ (RootSet (toTwo I U T)) (RootObj (toTwo I U T)) ∧
      PosDefQ (SigP I U.pl0 U.pa0) ∧ PosDefQ (SigP I (postVar U.pl0 I.sf2) (postVar U.pa0 I.sA2))

/-! ### Part 2a: the moment content under the finite law -/

/-- A finite law for one block: prior weights `w` on values `θ` with mean `m` and variance `p`,
and noise weights `v` on values `z` with mean zero and variance `s`. -/
def BlockLaw {Θ E : Type} [Fintype Θ] [Fintype E] (w : Θ → ℝ) (θ : Θ → ℝ) (v : E → ℝ) (z : E → ℝ)
    (m p s : ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧ ∑ a, w a * θ a = m ∧ ∑ a, w a * (θ a - m) ^ 2 = p ∧
    (∀ e, 0 ≤ v e) ∧ ∑ e, v e = 1 ∧ ∑ e, v e * z e = 0 ∧ ∑ e, v e * z e ^ 2 = s

/-- Part 2a's moment content, per block and for any finite laws with the stated moments.
- At `t = 0` the innovation `m_1 - m_0` has mean zero and variance `p_0 - p_1`.
- At `t = 1` the error `theta - m_1` has variance `p_1`, and the innovation `m_2 - m_1` has mean zero
  and variance `p_1 - p_2`.
- The innovations of two independent blocks are uncorrelated. -/
def Moments : Prop :=
  ∀ (Θ E : Type) [Fintype Θ] [Fintype E] (w : Θ → ℝ) (θ : Θ → ℝ) (v : E → ℝ) (z : E → ℝ) (m p s : ℝ),
    0 < p → 0 < s → BlockLaw w θ v z m p s →
      (∑ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) = 0) ∧
      (∑ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) ^ 2 = p - postVar p s) ∧
      (∑ a, ∑ e, w a * v e * (θ a - filt m p s (θ a + z e)) ^ 2 = postVar p s) ∧
      (∑ a, ∑ e₁, ∑ e₂, w a * v e₁ * v e₂ *
        (filt (filt m p s (θ a + z e₁)) (postVar p s) s (θ a + z e₂) - filt m p s (θ a + z e₁)) = 0) ∧
      (∑ a, ∑ e₁, ∑ e₂, w a * v e₁ * v e₂ *
        (filt (filt m p s (θ a + z e₁)) (postVar p s) s (θ a + z e₂) - filt m p s (θ a + z e₁)) ^ 2 =
          postVar p s - postVar (postVar p s) s)

/-- Part 2a: the innovations of two independent blocks are uncorrelated. -/
def CrossMoment : Prop :=
  ∀ (Θ E Θ' E' : Type) [Fintype Θ] [Fintype E] [Fintype Θ'] [Fintype E'] (w : Θ → ℝ) (θ : Θ → ℝ)
    (v : E → ℝ) (z : E → ℝ) (w' : Θ' → ℝ) (θ' : Θ' → ℝ) (v' : E' → ℝ) (z' : E' → ℝ) (m p s m' p' s' : ℝ),
    0 < p → 0 < s → 0 < p' → 0 < s' → BlockLaw w θ v z m p s → BlockLaw w' θ' v' z' m' p' s' →
      ∑ a, ∑ e, ∑ a', ∑ e', w a * v e * w' a' * v' e' *
        ((filt m p s (θ a + z e) - m) * (filt m' p' s' (θ' a' + z' e') - m')) = 0

/-- The exact posterior mean at observation `y` under a finite joint law `π(θ, y)` (zero where `y` has
probability zero). -/
def postMean {Θ Y : Type} [Fintype Θ] (π : Θ → Y → ℝ) (θ : Θ → ℝ) (y : Y) : ℝ :=
  (∑ a, π a y * θ a) / ∑ a, π a y

/-- Part 2a, the tower property on a finite law: the exact posterior mean averages to the prior
mean. -/
def Tower : Prop :=
  ∀ (Θ Y : Type) [Fintype Θ] [Fintype Y] (π : Θ → Y → ℝ) (θ : Θ → ℝ) (w : Θ → ℝ) (m : ℝ),
    (∀ a y, 0 ≤ π a y) → (∀ a, ∑ y, π a y = w a) → ∑ a, w a * θ a = m →
      ∑ y, (∑ a, π a y) * postMean π θ y = m

/-- The joint law of `(theta, y)` for one block with `y = theta + z`. -/
def joint {Θ E : Type} [Fintype E] (w : Θ → ℝ) (θ : Θ → ℝ) (v : E → ℝ) (z : E → ℝ) (a : Θ) (y : ℝ) : ℝ :=
  w a * ∑ e, if θ a + z e = y then v e else 0

/-- Part 2a's sufficient condition for non-coincidence. Take a two-point prior `m ± d` with equal
weights, and an observation reached from both branches with equal likelihood. Then the exact
posterior mean there is `m`, while the filter moves whenever the innovation `y - m` is nonzero. -/
def NonCoincidence : Prop :=
  ∀ (E : Type) [Fintype E] (v : E → ℝ) (z : E → ℝ) (m d s y : ℝ), 0 < d → 0 < s →
    let θ : Bool → ℝ := fun b => if b then m + d else m - d
    let w : Bool → ℝ := fun _ => 1 / 2
    joint w θ v z true y = joint w θ v z false y → 0 < joint w θ v z true y →
      (∑ b, joint w θ v z b y * θ b) / (∑ b, joint w θ v z b y) = m ∧
      (y ≠ m → filt m (d ^ 2) s y ≠ m)

/-- Red's counterexample: with `theta` and the noise both in `{-1, +1}`, equiprobable and independent,
the exact posterior mean equals the filter's at every observation `y ∈ {-2, 0, 2}`. -/
def RedCounterexample : Prop :=
  let θ : Bool → ℝ := fun b => if b then 1 else -1
  let w : Bool → ℝ := fun _ => 1 / 2
  ∀ y ∈ ({-2, 0, 2} : Set ℝ),
    (∑ b, joint w θ w θ b y * θ b) / (∑ b, joint w θ w θ b y) = filt 0 1 1 y

/-- Part 4's node A, the alpha block. The prior is `{-1.6%, 2.4%}` with equal weights, the residual
shock `{±4%, ±8%}` equiprobable, and the observed residual 6.4%. The exact posterior mean returns to
the prior's 0.4%, while the filter moves it to `0.4% + 6%/11`, with gain `1/11`. -/
def NodeA : Prop :=
  let θ : Bool → ℝ := fun b => if b then 0.024 else -0.016
  let w : Bool → ℝ := fun _ => 1 / 2
  let z : Fin 4 → ℝ := ![-0.08, -0.04, 0.04, 0.08]
  let v : Fin 4 → ℝ := fun _ => 1 / 4
  BlockLaw w θ v z 0.004 0.0004 0.004 ∧
    (∑ b, joint w θ v z b 0.064 * θ b) / (∑ b, joint w θ v z b 0.064) = 0.004 ∧
    gain 0.0004 0.004 = 1 / 11 ∧ filt 0.004 0.0004 0.004 0.064 = 0.004 + 0.06 / 11

/-! ### Part 3: the slack-budget threshold -/

/-- Part 3: with `h⁻_0 ≥ 2 (1 + κ) Σ_i x̄_i` and every purchase rate at most `κ`, both funded
budgets hold at every pair of in-box holdings. So the budget never binds, and M8 is then M6's
slack-budget instance. -/
def SlackThreshold : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ κ : ℝ, (∀ i, P.kp i ≤ κ) →
    2 * (1 + κ) * ∑ i, P.xbar i ≤ P.h → ∀ X : (ι → ℝ) × (Z → ι → ℝ), Box P X.1 →
      (∀ z, Box P (X.2 z)) → 0 ≤ h0 P X.1 ∧ ∀ z, 0 ≤ h1 P X.1 X.2 z

/-! ### Part 4: Table 2 -/

/-- The example's inputs: `b_A = 0.9`, `b_E = 1`, `c^E = 5` bp, `sigma_f^2 = (7.6%² + 8.4%²)/2`,
`sigma_A^2 = (4%² + 8%²)/2` and `sigma_E^2 = 0.5%²`. -/
def exInputs : Inputs where
  bA := 0.9
  bE := 1
  cE := 0.0005
  sf2 := (0.076 ^ 2 + 0.084 ^ 2) / 2
  sA2 := (0.04 ^ 2 + 0.08 ^ 2) / 2
  sE2 := 0.005 ^ 2

/-- Part 4's Table 2, exactly: the gains `1/402` and `1/11`, `P_1`, `mu_0` and `Sigma_0`, and the
target within `5e-4` of `(0.406, 0.225)`. -/
def TableTwo : Prop :=
  gain 0.000016 exInputs.sf2 = 1 / 402 ∧ gain 0.0004 exInputs.sA2 = 1 / 11 ∧
    postVar 0.000016 exInputs.sf2 = 0.000016 * 401 / 402 ∧ postVar 0.0004 exInputs.sA2 = 0.004 / 11 ∧
    muP exInputs 0.01 0.004 = ![0.013, 0.0095] ∧
    SigP exInputs 0.000016 0.0004 = ![![0.00960992, 0.0057888], ![0.0057888, 0.006457]] ∧
    ∀ x : Fin 2 → ℝ, (∀ i, 2.5 * ∑ j, SigP exInputs 0.000016 0.0004 i j * x j = muP exInputs 0.01 0.004 i) →
      |x 0 - 0.406| < 0.0005 ∧ |x 1 - 0.225| < 0.0005

/-- Claim 112 (within the scope above). -/
def statement : Prop :=
  Beliefs ∧ PredRisk ∧ Marking ∧ ReviewFunding ∧ TreeFunding ∧ Moments ∧ CrossMoment ∧ Tower ∧
    NonCoincidence ∧ RedCounterexample ∧ NodeA ∧ SlackThreshold ∧ TableTwo

end

end Standalone.M8WorkedLearningExample

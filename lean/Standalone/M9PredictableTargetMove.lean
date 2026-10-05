import Standalone.M8WorkedLearningExample
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Claim 114: time-varying premia and alphas (M9), the predictable and unpredictable target move

Statement only; the proof is `Novel/M9PredictableTargetMoveProof.lean`.

The model is M9 (`model/SPEC.md`), built on claim 112's M8 coordinates. The filter is scalar by block,
with persistence `φ`, state noise `q` and long-run mean `θ̄`.
- update: `m + k(y - m)`, with gain `k = p/(p + s)`;
- posterior variance: `p^u = (1 - k)p`;
- predict: `m_1 = φ(m + k(y - m)) + (1 - φ)θ̄` and `p_1 = φ² p^u + q`.
- The target at review `t` is `A_t μ_t` for any matrix `A_t`. M9's is `A_t = (γ Σ_t)⁻¹`.
The two-review objects (`Two`, `Myopic`, `Tomorrow`, `Sinc`, `RootObj`) are claim 044's.

Scope (PM, rule 6b, and the claim as approved). Formal:
- 1a;
- 1b: per instrument, and the scalar blocks' convergence argued in the approved text;
- part 2's probability identity, with the no-atom form;
- 3a-3b, with the hypothesis at the myopic root as approved.
Paper-level: 3c, 3d, part 4's transfer table, the transient Kalman filter's meaning, AX-10's
steady-state form and the Checks.
For the fidelity row (PM): 3a and 3b are one-coordinate statements. They hold with the other
holdings fixed, or with the two roots agreeing off the fund, and say nothing about the dynamic
policy's joint move, which experiment 047 showed can reverse. The sale side needs no separate
tangent bound: with tomorrow's budget slack, the myopic root's tangent plane (`Loading`) covers
both directions at once.
-/

namespace Standalone.M9PredictableTargetMove

open Standalone.M7TwoReviewsBindingBudget Standalone.M8WorkedLearningExample Matrix

noncomputable section

/-! ### The M9 filter, by block -/

/-- The predicted mean `m_1 = φ(m + k(y - m)) + (1 - φ)θ̄`. -/
def mNext (φ θb m p s y : ℝ) : ℝ := φ * filt m p s y + (1 - φ) * θb

/-- The predicted variance `p_1 = φ² p^u + q`. -/
def pNext (φ q p s : ℝ) : ℝ := φ ^ 2 * postVar p s + q

/-- M9's persistence, state noise and long-run means. -/
structure Nine where
  φl : ℝ
  φa : ℝ
  ql : ℝ
  qa : ℝ
  lb : ℝ
  ab : ℝ

/-- `G(Φ - I)(m_0 - θ̄)`, the predictable move of the mean. -/
def predVec (I : Inputs) (T : Nine) (lh ah : ℝ) : Fin 2 → ℝ :=
  ![I.bA * ((T.φl - 1) * (lh - T.lb)) + (T.φa - 1) * (ah - T.ab), I.bE * ((T.φl - 1) * (lh - T.lb))]

/-- `G ε` with the belief innovation `ε = Φ K ν`. -/
def innovVec (I : Inputs) (el ea : ℝ) : Fin 2 → ℝ := ![I.bA * el + ea, I.bE * el]

/-- Part 1a, the decomposition, an identity for any targets `A_t μ_t` (M9's `A_t = (γΣ_t)⁻¹`).
With the belief innovation `ε = Φ K ν` of an observation `y`,
`x*_1 - x*_0 = [A_1 G(Φ - I)(m_0 - θ̄) + (A_1 - A_0) μ_0] + A_1 G ε`. -/
def Decomposition : Prop :=
  ∀ (I : Inputs) (T : Nine) (lh ah pl pa yl ya : ℝ) (A0 A1 : Matrix (Fin 2) (Fin 2) ℝ),
    let el := T.φl * (filt lh pl I.sf2 yl - lh)
    let ea := T.φa * (filt ah pa I.sA2 ya - ah)
    A1 *ᵥ muP I (mNext T.φl T.lb lh pl I.sf2 yl) (mNext T.φa T.ab ah pa I.sA2 ya) - A0 *ᵥ muP I lh ah =
      (A1 *ᵥ predVec I T lh ah + (A1 - A0) *ᵥ muP I lh ah) + A1 *ᵥ innovVec I el ea

/-- Part 1a, the innovation's moments under any finite laws with the stated moments, the two blocks
independent. For any linear image `M ε` (M9's `M = (γΣ_1)⁻¹ G`), the mean is zero and the covariance
is `M V_0 M'`, with `V_0 = diag(φ_λ²(p^λ - p^{u,λ}), φ_α²(p^α - p^{u,α}))`. -/
def InnovMoments : Prop :=
  ∀ (Θ E Θ' E' : Type) [Fintype Θ] [Fintype E] [Fintype Θ'] [Fintype E'] (w : Θ → ℝ) (θ : Θ → ℝ)
    (v : E → ℝ) (z : E → ℝ) (w' : Θ' → ℝ) (θ' : Θ' → ℝ) (v' : E' → ℝ) (z' : E' → ℝ)
    (m p s m' p' s' φ φ' : ℝ) (M : Fin 2 → Fin 2 → ℝ),
    0 < p → 0 < s → 0 < p' → 0 < s' → BlockLaw w θ v z m p s → BlockLaw w' θ' v' z' m' p' s' →
      let ε : Θ → E → Θ' → E' → Fin 2 → ℝ := fun a e a' e' =>
        ![φ * (filt m p s (θ a + z e) - m), φ' * (filt m' p' s' (θ' a' + z' e') - m')]
      (∀ i, ∑ a, ∑ e, ∑ a', ∑ e', w a * v e * w' a' * v' e' * ∑ k, M i k * ε a e a' e' k = 0) ∧
      ∀ i j, ∑ a, ∑ e, ∑ a', ∑ e', w a * v e * w' a' * v' e' *
        ((∑ k, M i k * ε a e a' e' k) * (∑ k, M j k * ε a e a' e' k)) =
          M i 0 * M j 0 * (φ ^ 2 * (p - postVar p s)) + M i 1 * M j 1 * (φ' ^ 2 * (p' - postVar p' s'))

/-- Part 1b. The predicted variance's change is `q - (p - φ² p^u)` per block, and `Σ_1 - Σ_0` is
`G diag(Δ^λ, Δ^α) G'` entrywise. So both blocks learning-dominant (`Δ ≤ 0`) lower every curvature,
and so widen every static width `(κ⁺ + κ⁻)/c_t`. Both noise-dominant raise every curvature. Equal
variances give a constant `Σ`. The ETF's curvature falls iff the λ block's variance does. -/
def Width : Prop :=
  ∀ (I : Inputs) (φ q p s : ℝ), pNext φ q p s - p = q - (p - φ ^ 2 * postVar p s) ∧
    ∀ pl pa pl' pa' : ℝ,
      (SigP I pl' pa' 0 0 - SigP I pl pa 0 0 = I.bA ^ 2 * (pl' - pl) + (pa' - pa) ∧
        SigP I pl' pa' 0 1 - SigP I pl pa 0 1 = I.bA * I.bE * (pl' - pl) ∧
        SigP I pl' pa' 1 0 - SigP I pl pa 1 0 = I.bA * I.bE * (pl' - pl) ∧
        SigP I pl' pa' 1 1 - SigP I pl pa 1 1 = I.bE ^ 2 * (pl' - pl)) ∧
      (pl' ≤ pl → pa' ≤ pa → SigP I pl' pa' 0 0 ≤ SigP I pl pa 0 0 ∧ SigP I pl' pa' 1 1 ≤ SigP I pl pa 1 1) ∧
      (pl ≤ pl' → pa ≤ pa' → SigP I pl pa 0 0 ≤ SigP I pl' pa' 0 0 ∧ SigP I pl pa 1 1 ≤ SigP I pl' pa' 1 1) ∧
      (pl' = pl → pa' = pa → SigP I pl' pa' = SigP I pl pa) ∧
      (I.bE ≠ 0 → (SigP I pl' pa' 1 1 < SigP I pl pa 1 1 ↔ pl' < pl))

/-- Part 1b per instrument: an instrument's curvature falls (its width rises) iff its loadings'
combination of the block changes is negative, `(G diag(Δ) G')_{ii} < 0`. -/
def PerInstrument : Prop :=
  ∀ (I : Inputs) (pl pa pl' pa' : ℝ),
    (SigP I pl' pa' 0 0 < SigP I pl pa 0 0 ↔ I.bA ^ 2 * (pl' - pl) + (pa' - pa) < 0) ∧
      (SigP I pl' pa' 1 1 < SigP I pl pa 1 1 ↔ I.bE ^ 2 * (pl' - pl) < 0)

/-- Part 1b, the convergence of each block's variance. The map `T(p) = φ² p s/(p + s) + q`, with
`s > 0` and `q ≥ 0`, has iterates from any `p_0 ≥ 0` that converge to a nonnegative fixed point.
The nonnegative fixed point is unique when `q > 0` or `φ² < 1`. -/
def Convergence : Prop :=
  ∀ (φ q s p0 : ℝ), 0 < s → 0 ≤ q → 0 ≤ p0 →
    (∃ pst : ℝ, 0 ≤ pst ∧ pNext φ q pst s = pst ∧
      Filter.Tendsto (fun n => (fun p => pNext φ q p s)^[n] p0) Filter.atTop (nhds pst)) ∧
    ((0 < q ∨ φ ^ 2 < 1) → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → pNext φ q a s = a → pNext φ q b s = b → a = b)

/-- Part 1b's "iff" fails when the blocks move oppositely. With `b_A = 0.9` and `b_E = 1`, the λ
block's variance rises by `1e-6` while the α block's falls by `1e-4`. The fund's curvature falls,
so its width rises, although the λ block is not learning-dominant. -/
def MixedBlocks : Prop :=
  ∀ I : Inputs, I.bA = 0.9 → I.bE = 1 → ∀ pl pa : ℝ,
    SigP I (pl + 0.000001) (pa - 0.0001) 0 0 < SigP I pl pa 0 0 ∧
      SigP I pl pa 1 1 < SigP I (pl + 0.000001) (pa - 0.0001) 1 1

/-! ### Part 2: the tilt's probabilities -/

/-- `P(u ∈ S)` under a finite law. -/
def prob {Ω : Type} [Fintype Ω] (π : Ω → ℝ) (u : Ω → ℝ) (S : ℝ → Prop) [DecidablePred S] : ℝ :=
  ∑ ω, if S (u ω) then π ω else 0

/-- Part 2. Take a finite law of the innovation `u = Δ^u_{t+1,i}`, symmetric through an involution
`σ`, and a predictable move `δ = Δ^p_{t,i}`. Write `U = P(u > -δ)` and `D = P(u < -δ)`.
- `U - D = sign(δ) P(-|δ| < u ≤ |δ|)`, which equals `P(|u| ≤ |δ|) - P(u = -|δ|)` in magnitude.
- The tilt `β κ (U - D)/c` has `δ`'s sign (weakly).
- If `|δ|` exceeds the support, `U = 1` (`δ > 0`) or `D = 1` (`δ < 0`). -/
def Tilt : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (π : Ω → ℝ) (u : Ω → ℝ) (σ : Ω → Ω), (∀ ω, 0 ≤ π ω) → ∑ ω, π ω = 1 →
    (∀ ω, σ (σ ω) = ω) → (∀ ω, π (σ ω) = π ω) → (∀ ω, u (σ ω) = -u ω) → ∀ δ : ℝ,
      let U := prob π u (fun x => -δ < x)
      let D := prob π u (fun x => x < -δ)
      let W := prob π u (fun x => -|δ| < x ∧ x ≤ |δ|)
      (0 ≤ δ → U - D = W) ∧ (δ ≤ 0 → U - D = -W) ∧
      W = prob π u (fun x => |x| ≤ |δ|) - prob π u (fun x => x = -|δ|) ∧ 0 ≤ W ∧
      ((∀ ω, u ω ≠ -|δ|) → W = prob π u (fun x => |x| ≤ |δ|)) ∧
      (∀ β κ c : ℝ, 0 ≤ β → 0 ≤ κ → 0 < c →
        (0 ≤ δ → 0 ≤ β * κ * (U - D) / c) ∧ (δ ≤ 0 → β * κ * (U - D) / c ≤ 0)) ∧
      ((∀ ω, |u ω| < δ) → U = 1) ∧ ((∀ ω, |u ω| < -δ) → D = 1)

/-! ### Part 3: front-loading and back-loading -/

/-- 3a-3b. The myopic policy's root, with tomorrow's budget slack in every state, and `t_1` the slopes
of the myopic tomorrow. The root objective lies below the myopic root's tangent plane of slopes
`S_j` over the whole root polyhedron. If the myopic tomorrow buys (sells) instrument `i` in every
state, `S_i = β Σ q g_i κ⁺_i` (`-β Σ q g_i κ⁻_i`). Every smaller (larger) holding of `i`, with the
others fixed, strictly lowers the root objective. An optimal policy whose root agrees with the
myopic root off `i` then holds at least (at most) as much of `i`: front-loading (back-loading). -/
def Loading : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Nonempty Z → ∀ X η1 t1, Myopic P X →
    Tomorrow P X η1 t1 → (∀ z, 0 < h1 P X.1 X.2 z) →
      (∀ y ∈ RootSet P, RootObj P y ≤ RootObj P X.1 + ∑ j, Sinc P η1 t1 j * (y j - X.1 j)) ∧
      ∀ i,
        ((∀ z, carry P z X.1 i < X.2 z i) → 0 < P.kp i →
          Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * P.kp i ∧
          (∀ y ∈ RootSet P, (∀ j, j ≠ i → y j = X.1 j) → y i < X.1 i → RootObj P y < RootObj P X.1) ∧
          ∀ Xd, Optimal P Xd → (∀ j, j ≠ i → Xd.1 j = X.1 j) → X.1 i ≤ Xd.1 i) ∧
        ((∀ z, X.2 z i < carry P z X.1 i) → 0 < P.km i →
          Sinc P η1 t1 i = -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ∧
          (∀ y ∈ RootSet P, (∀ j, j ≠ i → y j = X.1 j) → X.1 i < y i → RootObj P y < RootObj P X.1) ∧
          ∀ Xd, Optimal P Xd → (∀ j, j ≠ i → Xd.1 j = X.1 j) → Xd.1 i ≤ X.1 i)

/-- 3a's threshold reading at the dynamic root. Take both budgets slack, the dynamic tomorrow
buying `i` in every state, and a purchase of `i` strictly inside its box today. Then
`g_{0,i} = (1 - β Σ q g_i) κ⁺_i`: the purchase threshold is lowered by the rate tomorrow would pay. -/
def Threshold : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X η0 η1 t0 t1,
    Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → 0 < h0 P X.1 → (∀ z, 0 < h1 P X.1 X.2 z) → ∀ i,
      (∀ z, carry P z X.1 i < X.2 z i) → P.xm i < X.1 i → X.1 i < P.xbar i →
        g0 P X.1 i = (1 - P.beta * ∑ z, P.q z * P.g z i) * P.kp i

/-- 3a's threshold as an inequality at the dynamic root, with both budgets slack. The dynamic
root's own incumbent value is at most its bracket's end, `S^dyn_i ≤ β Σ q g_i κ⁺_i`. On a purchase
strictly inside the box, the threshold `κ⁺_i - S^dyn_i = g_{0,i}` is at least
`(1 - β Σ q g_i) κ⁺_i`. Equality holds iff every state's slope tomorrow is `κ⁺_i`: bought, or held
at the purchase edge. -/
def ThresholdBound : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X η0 η1 t0 t1,
    Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → 0 < h0 P X.1 → (∀ z, 0 < h1 P X.1 X.2 z) → ∀ i,
      Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * P.kp i ∧
      (P.xm i < X.1 i → X.1 i < P.xbar i →
        (1 - P.beta * ∑ z, P.q z * P.g z i) * P.kp i ≤ g0 P X.1 i ∧
        (g0 P X.1 i = (1 - P.beta * ∑ z, P.q z * P.g z i) * P.kp i ↔ ∀ z, t1 z i = P.kp i))

/-- An optimal policy's root maximizes the root objective over the root polyhedron (backward
induction, used by 3a-3b). -/
def RootOpt : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X, Optimal P X →
    X.1 ∈ RootSet P ∧ IsMaxOn (RootObj P) (RootSet P) X.1

/-- Claim 114 (within the scope above). -/
def statement : Prop :=
  Decomposition ∧ InnovMoments ∧ Width ∧ PerInstrument ∧ Convergence ∧ MixedBlocks ∧ Tilt ∧ Loading ∧
    Threshold ∧ ThresholdBound ∧ RootOpt

end

end Standalone.M9PredictableTargetMove

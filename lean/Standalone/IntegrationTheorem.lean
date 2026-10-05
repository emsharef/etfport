import Standalone.M2NoActiveTradeBand
import Standalone.M2TwoStageSeparation
import Standalone.M2SoftTargetTwoStage
import Standalone.M6QuarterlyBandStaticCeiling
import Standalone.M5PartialAdjustmentSplit
import Standalone.M5MissingDirectionLeak
import Standalone.M5LearningAimTwoSpeeds
import Standalone.M5PlugInValueLoss
import Standalone.M5PlugInLossInputs
import Standalone.M5ReestimationGuarantee
import Standalone.M5WhenAnticipationMatters
import Standalone.M7LearningBandTransfer

/-!
# Claim 038: the integration theorem

Statement only; the proof is `Novel/IntegrationTheoremProof.lean`.

The claim composes claims 009 and 027-036 and 100. Their formal statements enter as conjuncts
(`Components`). They supply:
- A1 and A2, the target's split, leak and motion;
- B1 and B2, M5's aim and rate, and M7's band;
- C2 and C3's M5 side, the plug-in loss and the re-estimation guarantee;
- D's M7 side, the last-review band and the one-quarter theory.

The new steps are stated here:
- Part 0, the tracking identity: the stage reward without cost is `-(γ/2)` times the tracking loss
  against `x* = (γΣ)⁻¹μ`, plus a term free of `x`.
- A3: on the constant-state scalar Kalman path, the target's cumulative relative drift and its
  bound `(s - t)(κ_t/(1 - κ_t))²`, the one-step form, and `V_t = p_t κ_t`.
- B3, quadratic side: `L_t - 1 ≤ (κ_t/(1 - κ_t))² Dur_t`, with the aim's look-ahead duration
  `Dur_t = Σ_s w_{t,s}(s - t)` in `[0, T - 1 - t]`, tending to `0` as `λ_A → 0`.
- C1: the Bellman-residual identity `V* - V^π = Σ_t ρ^t E Δ_t` with `Δ_t ≥ 0`, on a finite-law
  decision problem. With stage rewards bounded by `c` and stochastic transitions, `Δ_t ≤ 2c H_t`,
  where `H_t = Σ_{s ≥ t} ρ^{s-t}`.
- C3's M7 devices: the stage-reward bound from the caps, and the one-review on-event bound.
- D's M5 side: the one-review rule `x₀ = (Λ + γΣ)⁻¹(Λx⁻ + μ)` is the unique maximizer. It trades unless
  `μ = γΣx⁻`.

Paper-level: B3's proportional-cost side (the coarse-regime tilt is claim 100's statement; the
fine-regime displacement is `martin2012optimal`, cited at leading order), C3's off-event expectation
step, A3's innovation standard deviation as a distributional reading, and Part E.
-/

namespace Standalone.IntegrationTheorem

open Matrix Filter Topology Standalone.M5WhenAnticipationMatters

noncomputable section

/-- Part 0, the tracking identity: `μ'x - (γ/2)x'Σx = -(γ/2)(x - x*)'Σ(x - x*) + μ'Σ⁻¹μ/(2γ)` with
`x* = (γΣ)⁻¹μ`. -/
def Tracking : Prop :=
  ∀ (n : ℕ) (Sg : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) (mu x : Fin n → ℝ), Sg.PosDef → 0 < γ →
    mu ⬝ᵥ x - γ / 2 * (x ⬝ᵥ (Sg *ᵥ x)) =
      -(γ / 2) * ((x - (γ • Sg)⁻¹ *ᵥ mu) ⬝ᵥ (Sg *ᵥ (x - (γ • Sg)⁻¹ *ᵥ mu))) +
        1 / (2 * γ) * (mu ⬝ᵥ (Sg⁻¹ *ᵥ mu))

/-- A3: on the constant-state scalar Kalman path `p_{s+1} = p_s σ²/(σ² + p_s)`, with the gain
`κ_t = p_t/(σ² + p_t)`:
- `1/p_{t+k} = 1/p_t + k/σ²`;
- the cumulative relative drift of the target is `(σ² + p_t)/(σ² + p_{t+k}) - 1 = (p_t - p_{t+k})/(σ² + p_{t+k})`,
  at most `k (κ_t/(1 - κ_t))²`;
- the innovation variance is `V_t = p_t - p_{t+1} = p_t κ_t`;
- the one-step relative drift is `κ_t p_t/(σ² + p_{t+1}) ≤ (κ_t/(1 - κ_t))²`. -/
def KalmanDrift : Prop :=
  ∀ (sig2 : ℝ) (p : ℕ → ℝ), 0 < sig2 → (∀ s, 0 < p s) →
    (∀ s, p (s + 1) = p s * sig2 / (sig2 + p s)) → ∀ t k : ℕ,
    let kap := p t / (sig2 + p t)
    1 / p (t + k) = 1 / p t + k / sig2 ∧
    (sig2 + p t) / (sig2 + p (t + k)) - 1 = (p t - p (t + k)) / (sig2 + p (t + k)) ∧
    (p t - p (t + k)) / (sig2 + p (t + k)) ≤ k * (kap / (1 - kap)) ^ 2 ∧
    p t - p (t + 1) = p t * kap ∧
    (sig2 + p t) / (sig2 + p (t + 1)) - 1 = kap * p t / (sig2 + p (t + 1)) ∧
    kap * p t / (sig2 + p (t + 1)) ≤ (kap / (1 - kap)) ^ 2

/-- The aim's look-ahead duration `Dur_t = Σ_s w_{t,s}(s - t)`. -/
def Dur (B : Blk) (t : ℕ) : ℝ := ∑ k ∈ Finset.range (B.T - t), B.w k t * k

/-- B3, the quadratic-cost side. On the constant-state Kalman path:
- `0 < L_t - 1 ≤ (κ_t/(1 - κ_t))² Dur_t` before the last review;
- `0 ≤ Dur_t ≤ T - 1 - t`, and `Dur_t → 0` as `λ_A → 0`;
- anticipation changes the aim by a fraction `θ` or more only if `(κ_t/(1 - κ_t))² Dur_t ≥ θ`. -/
def AnticipationOrder : Prop :=
  ∀ B : Blk, B.Setting → (∀ s, B.p (s + 1) = B.p s * B.sig2 / (B.sig2 + B.p s)) → ∀ t, t < B.T →
    B.L t - 1 ≤ (B.kap t / (1 - B.kap t)) ^ 2 * Dur B t ∧
    (t + 1 < B.T → 0 < B.L t - 1) ∧
    0 ≤ Dur B t ∧ Dur B t ≤ ((B.T - t : ℕ) : ℝ) - 1 ∧
    Tendsto (fun lam => Dur (B.withLam lam) t) (𝓝[>] 0) (𝓝 0) ∧
    ∀ θ : ℝ, θ ≤ B.L t - 1 → θ ≤ (B.kap t / (1 - B.kap t)) ^ 2 * Dur B t

/-- A finite-law decision problem: finite states `Z`, actions `X`, feasible sets, rewards and
transition weights, horizon `T` and discount `ρ`. -/
structure FDP (Z X : Type) where
  T : ℕ
  rho : ℝ
  feas : ℕ → Z → Set X
  r : ℕ → Z → X → ℝ
  P : ℕ → Z → X → Z → ℝ

namespace FDP

variable {Z X : Type} [Fintype Z] (Q : FDP Z X)

/-- `J` solves the Bellman equation: `J_T = 0`, and `J_t(z)` is the maximum over feasible `x` of
`r_t(z, x) + ρ Σ_{z'} P_t(z, x, z') J_{t+1}(z')`. -/
def Bellman (J : ℕ → Z → ℝ) : Prop :=
  (∀ z, J Q.T z = 0) ∧ ∀ t, t < Q.T → ∀ z,
    (∀ x ∈ Q.feas t z, Q.r t z x + Q.rho * ∑ z', Q.P t z x z' * J (t + 1) z' ≤ J t z) ∧
    ∃ x ∈ Q.feas t z, Q.r t z x + Q.rho * ∑ z', Q.P t z x z' * J (t + 1) z' = J t z

/-- The state law under a policy `π` from the initial law `μ₀`. -/
def law (pol : ℕ → Z → X) (mu0 : Z → ℝ) : ℕ → Z → ℝ
  | 0 => mu0
  | t + 1 => fun z' => ∑ z, law pol mu0 t z * Q.P t z (pol t z) z'

/-- The policy's value `E Σ_t ρ^t r_t`. -/
def value (pol : ℕ → Z → X) (mu0 : Z → ℝ) : ℝ :=
  ∑ t ∈ Finset.range Q.T, Q.rho ^ t * ∑ z, Q.law pol mu0 t z * Q.r t z (pol t z)

/-- The policy's Bellman residual at state `z`. -/
def resid (J : ℕ → Z → ℝ) (pol : ℕ → Z → X) (t : ℕ) (z : Z) : ℝ :=
  J t z - (Q.r t z (pol t z) + Q.rho * ∑ z', Q.P t z (pol t z) z' * J (t + 1) z')

/-- The discounted remaining horizon `H_t = Σ_{s=t}^{T-1} ρ^{s-t}`. -/
def H (t : ℕ) : ℝ := ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k

end FDP

/-- C1, the Bellman-residual identity. For any feasible policy and any initial law,
`Σ_z μ₀(z)J_0(z) - V^π = Σ_t ρ^t E Δ_t`, and every residual is nonnegative. If the stage rewards are
bounded by `c` on feasible actions, the transitions are stochastic and `ρ ∈ [0, 1]`, then
`|J_t| ≤ c H_t` and `Δ_t ≤ 2c H_t` pathwise. -/
def ResidualIdentity : Prop :=
  ∀ (Z X : Type) [Fintype Z] (Q : FDP Z X) (J : ℕ → Z → ℝ) (pol : ℕ → Z → X) (mu0 : Z → ℝ),
    Q.Bellman J → (∀ t z, t < Q.T → pol t z ∈ Q.feas t z) →
    (∑ z, mu0 z * J 0 z - Q.value pol mu0 =
      ∑ t ∈ Finset.range Q.T, Q.rho ^ t * ∑ z, Q.law pol mu0 t z * Q.resid J pol t z) ∧
    (∀ t z, t < Q.T → 0 ≤ Q.resid J pol t z) ∧
    ∀ c : ℝ, (∀ t z x, t < Q.T → x ∈ Q.feas t z → |Q.r t z x| ≤ c) →
      (∀ t z x z', 0 ≤ Q.P t z x z') → (∀ t z x, ∑ z', Q.P t z x z' = 1) →
      0 ≤ Q.rho → Q.rho ≤ 1 →
      (∀ t z, t ≤ Q.T → |J t z| ≤ c * Q.H t) ∧ ∀ t z, t < Q.T → Q.resid J pol t z ≤ 2 * c * Q.H t

/-- C3's M7 device: for post-trade holdings in the box `[0, x̄]` and nonnegative marked pre-trade
holdings, the stage reward `μ'x - (γ/2)x'Σx - C(x - x⁻)` is bounded by
`|μ|'x̄ + (γ/2) σ ‖x̄‖² + Σ_i (κ⁺_i + κ⁻_i) max(x̄_i, x⁻_i)`. Here `σ` bounds `‖Σ‖` and `Σ` is positive
semidefinite. -/
def CapBound : Prop :=
  ∀ (n : ℕ) (Sg : Matrix (Fin n) (Fin n) ℝ) (γ σ : ℝ) (mu kp km xbar xm x : Fin n → ℝ),
    (∀ v, 0 ≤ v ⬝ᵥ (Sg *ᵥ v)) → (∀ v, v ⬝ᵥ (Sg *ᵥ v) ≤ σ * (v ⬝ᵥ v)) → 0 ≤ γ →
    (∀ i, 0 ≤ kp i ∧ 0 ≤ km i ∧ 0 ≤ xm i ∧ 0 ≤ x i ∧ x i ≤ xbar i) →
    |mu ⬝ᵥ x - γ / 2 * (x ⬝ᵥ (Sg *ᵥ x)) -
        ∑ i, (kp i * max (x i - xm i) 0 + km i * max (xm i - x i) 0)| ≤
      ∑ i, |mu i| * xbar i + γ / 2 * σ * (xbar ⬝ᵥ xbar) + ∑ i, (kp i + km i) * max (xbar i) (xm i)

/-- The clip `clip(v, a, b) = max a (min b v)`. -/
def clip (v a b : ℝ) : ℝ := max a (min b v)

/-- C3's one-review M7 on-event bound, with one instrument and a slack budget. The true band has edges
`lo = clip(x* - κ⁺/c, 0, x̄)` and `hi = clip(x* + κ⁻/c, 0, x̄)`, and the plug-in band uses `(x~*, c~)`. Then:
- the edges move by at most `|x~* - x*| + κ^±|1/c~ - 1/c|`;
- the post-trade holdings `clip(x⁻, lo, hi)` differ by at most the larger edge shift;
- the one-review objective `μx - (c/2)x² - C(x - x⁻)` loses at most
  `(|μ| + c x̄ + max(κ⁺, κ⁻))` times that shift. -/
def OnEvent : Prop :=
  ∀ (mu c ct xs xst kp km xm xbar : ℝ), 0 < c → 0 < ct → 0 ≤ kp → 0 ≤ km → 0 ≤ xbar →
    0 ≤ xm → xm ≤ xbar →
    let lo := clip (xs - kp / c) 0 xbar
    let hi := clip (xs + km / c) 0 xbar
    let lot := clip (xst - kp / ct) 0 xbar
    let hit := clip (xst + km / ct) 0 xbar
    let psi := fun x => mu * x - c / 2 * x ^ 2 - (kp * max (x - xm) 0 + km * max (xm - x) 0)
    |lot - lo| ≤ |xst - xs| + kp * |1 / ct - 1 / c| ∧
    |hit - hi| ≤ |xst - xs| + km * |1 / ct - 1 / c| ∧
    |clip xm lot hit - clip xm lo hi| ≤ max |lot - lo| |hit - hi| ∧
    psi (clip xm lo hi) - psi (clip xm lot hit) ≤
      (|mu| + c * xbar + max kp km) * max |lot - lo| |hit - hi|

/-- D, M5's one-review rule: `x₀ = (Λ + γΣ)⁻¹(Λx⁻ + μ)` is the unique maximizer of
`μ'x - (γ/2)x'Σx - (1/2)(x - x⁻)'Λ(x - x⁻)` over `ℝⁿ`. It trades (`x₀ ≠ x⁻`) unless `μ = γΣx⁻`. -/
def OneReviewM5 : Prop :=
  ∀ (n : ℕ) (Sg Lam : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) (mu xm : Fin n → ℝ),
    Sg.PosDef → Lam.PosSemidef → 0 < γ →
    let f := fun x : Fin n → ℝ => mu ⬝ᵥ x - γ / 2 * (x ⬝ᵥ (Sg *ᵥ x)) -
      1 / 2 * ((x - xm) ⬝ᵥ (Lam *ᵥ (x - xm)))
    let x0 := (Lam + γ • Sg)⁻¹ *ᵥ (Lam *ᵥ xm + mu)
    (Lam + γ • Sg) *ᵥ x0 = Lam *ᵥ xm + mu ∧ (∀ x, f x ≤ f x0) ∧ (∀ x, f x = f x0 → x = x0) ∧
    (x0 = xm ↔ mu = γ • (Sg *ᵥ xm))

/-- The component claims' results, as formalized. -/
def Components : Prop :=
  Standalone.M2NoActiveTradeBand.statement ∧ Standalone.M2TwoStageSeparation.statement ∧
    Standalone.M2SoftTargetTwoStage.statement ∧ Standalone.M6QuarterlyBandStaticCeiling.statement ∧
    Standalone.M5PartialAdjustmentSplit.statement ∧ Standalone.M5MissingDirectionLeak.statement ∧
    Standalone.M5LearningAimTwoSpeeds.statement ∧ Standalone.M5PlugInValueLoss.statement ∧
    Standalone.M5PlugInLossInputs.statement ∧ Standalone.M5ReestimationGuarantee.statement ∧
    Standalone.M5WhenAnticipationMatters.statement ∧ Standalone.M7LearningBandTransfer.statement

/-- Claim 038, the formal parts. -/
def statement : Prop :=
  Components ∧ Tracking ∧ KalmanDrift ∧ AnticipationOrder ∧ ResidualIdentity ∧ CapBound ∧ OnEvent ∧
    OneReviewM5

end

end Standalone.IntegrationTheorem

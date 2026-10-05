import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M3FiniteContinuation

/-!
# Claim 013: opposite continuation effects persist with conditional risk, partial learning and
uncertain alpha

Statement only; the proof is `Novel/ContinuationRobustnessProof.lean`.

The assumed M3 family `rbInst δ bA bE sA sE` is built on claim 011's formal M3 objects
(`Standalone/M3FiniteContinuation.lean`). It has one active fund and one ETF with loadings
`B^A = (1, 0)` and `B^E = (0, 1)`, zero drag, `ρ = 20`, zero initial risky holdings and cash one.
- Parameters: `t = (σ, ξ) : Bool × Bool` (true = +1) with mass `1/4` each, and
  `θ_{σ,ξ} = (σ/2, -σ/2, ξ δ)`.
- Scenarios: `s = (s_A, s_E) : Bool × Bool` with mass `1/4` each, with shocks `z^f = 0`,
  `z^A = δ s_A` and `z^E = δ s_E`.
`bA, bE` are the purchase rates and `sA, sE` the sale rates; all results hold for every
`δ ∈ (0, 1/1000]` and every rate in `[0, 1/100]`.
-/

namespace Standalone.ContinuationRobustness

open Matrix Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation

/-- A sign `±1`. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

/-- The data at noise/alpha scale `δ` and rates `bA, bE, sA, sE`. -/
noncomputable def rbData (δ bA bE sA sE : ℝ) : Data 1 1 2 (Bool × Bool) where
  BA := !![1, 0]
  BE := !![0, 1]
  cE := 0
  kplus := Sum.elim (fun _ => bA) (fun _ => bE)
  kminus := Sum.elim (fun _ => sA) (fun _ => sE)
  gamma := 0
  q := fun _ => 1 / 4
  zf := 0
  zA := fun s => ![δ * sg s.1]
  zE := fun s => ![δ * sg s.2]
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- `θ_{σ,ξ} = (σ/2, -σ/2, ξ δ)`. -/
noncomputable def rbPar (δ : ℝ) : Bool × Bool → Params 1 2 :=
  fun t => ⟨![sg t.1 / 2, -(sg t.1 / 2)], ![sg t.2 * δ]⟩

/-- The instance: prior mass `1/4` on each parameter and `ρ = 20`. -/
noncomputable def rbInst (δ bA bE sA sE : ℝ) : M3 1 2 (Bool × Bool) (Bool × Bool) :=
  ⟨rbData δ bA bE sA sE, rbPar δ, fun _ => 1 / 4, 20⟩

/-- The admissible range: `0 < δ ≤ 1/1000` and every rate in `[0, 1/100]`. -/
def InRange (δ bA bE sA sE : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 / 1000 ∧
  0 ≤ bA ∧ bA ≤ 1 / 100 ∧ 0 ≤ bE ∧ bE ≤ 1 / 100 ∧ 0 ≤ sA ∧ sA ≤ 1 / 100 ∧ 0 ≤ sE ∧ sE ≤ 1 / 100

/-- Property 1 and M3 validity: every member is an M3 instance with strictly positive gross
returns, and the conditional return covariance is `δ² I₂` (positive definite). -/
def RiskAndValidity : Prop :=
  ∀ δ bA bE sA sE, InRange δ bA bE sA sE →
    M3Setting (rbInst δ bA bE sA sE) ∧
    (∀ t s i, 0 < 1 + ret (rbInst δ bA bE sA sE).D ((rbInst δ bA bE sA sE).par t) s i) ∧
    covariance (rbInst δ bA bE sA sE).D = δ ^ 2 • (1 : Matrix (Inst 1 1) (Inst 1 1) ℝ) ∧
    ∀ v : Inst 1 1 → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (covariance (rbInst δ bA bE sA sE).D *ᵥ v)

/-- Property 2: alpha takes the nonzero values `±δ`, and the prior makes the alpha sign
independent of the factor regime (each `(σ, ξ)` has mass `1/4`). -/
def UncertainAlpha : Prop :=
  ∀ δ bA bE sA sE, InRange δ bA bE sA sE →
    (∀ t, ((rbInst δ bA bE sA sE).par t).alpha 0 = sg t.2 * δ) ∧ δ ≠ 0 ∧
    ∀ t, (rbInst δ bA bE sA sE).pi0 t = 1 / 2 * (1 / 2)

/-- Property 3: at every first-review observation `y` with `r_A - f₁ = 0` (the prose's
`r_A - λ₁ = 0`), `y` has probability `1/8` and the posterior puts mass `1/2` on each alpha value
for the revealed factor regime; the event `r_A - f₁ = 0` has probability `1/2`. -/
def PartialLearning : Prop :=
  ∀ δ bA bE sA sE, InRange δ bA bE sA sE →
    (∀ t s,
      let y := obs (rbInst δ bA bE sA sE) t s
      y.2 (Sum.inl 0) - y.1 0 = 0 →
        P0 (rbInst δ bA bE sA sE) y = 1 / 8 ∧
        post (rbInst δ bA bE sA sE) y (t.1, true) = 1 / 2 ∧
        post (rbInst δ bA bE sA sE) y (t.1, false) = 1 / 2) ∧
    ∑ t : Bool × Bool, ∑ s : Bool × Bool,
      (if (obs (rbInst δ bA bE sA sE) t s).2 (Sum.inl 0) - (obs (rbInst δ bA bE sA sE) t s).1 0 = 0
        then (rbInst δ bA bE sA sE).pi0 t * (rbInst δ bA bE sA sE).D.q s else 0) = 1 / 2

/-- The uniform bounds and the opposite-sign contributions. -/
def Bounds : Prop :=
  ∀ δ bA bE sA sE, InRange δ bA bE sA sE →
    let P := rbInst δ bA bE sA sE
    0 ≤ Delta P .N ∧ Delta P .N ≤ 1 / 4 + δ ^ 2 ∧
    2129 / 8080 - 9 * δ - δ ^ 2 < Delta P .E ∧
    0 ≤ Delta P .F ∧ Delta P .F ≤ 3 / 202 + 402 / 101 * δ ∧
    1 / 250 < Delta P .E - Delta P .N ∧ Delta P .F - Delta P .E < -23 / 100

/-- Every full-root optimum with future ETF-only control buys a positive active holding. -/
def ActivePurchase : Prop :=
  ∀ δ bA bE sA sE, InRange δ bA bE sA sE →
    ∀ π ∈ Pol (rbInst δ bA bE sA sE) .F .E,
      IsMaxOn (Phi (rbInst δ bA bE sA sE)) (Pol (rbInst δ bA bE sA sE) .F .E) π →
        0 < π.1 (Sum.inl 0)

/-- Claim 013, all parts. -/
def statement : Prop :=
  RiskAndValidity ∧ UncertainAlpha ∧ PartialLearning ∧ Bounds ∧ ActivePurchase

end Standalone.ContinuationRobustness

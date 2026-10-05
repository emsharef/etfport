import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M2NoActiveTradeBand

/-!
# Claim 010: a higher common switching-cost rate can strictly narrow the M2 no-active-trade band

Statement only; the proof is `Novel/M2HigherCostNarrowerBandProof.lean`.

One assumed instance family `data10 κ` (one active fund, one ETF, two factors), identical except
for the common purchase/sale rate `κ`, compared at `κ = 0` and `κ = 1/2000`. The band and all its
ingredients (`Qx`, `Jset`, `Cset`, `Iset`, `alphaC`) are claim 009's formal definitions
(`Standalone/M2NoActiveTradeBand.lean`). Scenarios are the 32 sign vectors `Bool⁵` with mass
`1/32` (the fifth sign unused); the support is `Fin 2 × Fin 2` (`λ₁ ∈ {3/200, 1/40}`,
`α ∈ {-1/400, 1/400}`, `λ₂ = 1/200`) with mass `1/4` each.
-/

namespace Standalone.M2HigherCostNarrowerBand

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2NoActiveTradeBand

/-- Scenarios: five independent signs. -/
abbrev Scen := Bool × Bool × Bool × Bool × Bool

/-- A sign `±1`. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

/-- The instance with common rate `κ`: `W⁻ = 1`, `γ = 1`, `B^A = (1, 1/2)`, `B^E = (1, 0)`,
`c^E = -1/10000`, `(a⁻, p⁻, k⁻) = (1/2, 0, 1/2)`, limits `(1, 1/2)`, shocks
`z^f = (3 s₁/50, s₂/50)`, `z^A = 3 s₃/100`, `z^E = s₄/200`. -/
noncomputable def data10 (κ : ℝ) : Data 1 1 2 Scen where
  BA := !![1, 1 / 2]
  BE := !![1, 0]
  cE := ![-1 / 10000]
  kplus := fun _ => κ
  kminus := fun _ => κ
  gamma := 1
  q := fun _ => 1 / 32
  zf := fun s => ![3 / 50 * sg s.1, 1 / 50 * sg s.2.1]
  zA := fun s => ![3 / 100 * sg s.2.2.1]
  zE := fun s => ![1 / 200 * sg s.2.2.2.1]
  x0 := Sum.elim (fun _ => 1 / 2) (fun _ => 0)
  h0 := 1 / 2
  wbar := Sum.elim (fun _ => 1) (fun _ => 1 / 2)

/-- The four support points: `λ₁ ∈ {3/200, 1/40}`, `λ₂ = 1/200`, `α ∈ {-1/400, 1/400}`. -/
noncomputable def par10 : Fin 2 × Fin 2 → Params 1 2 :=
  fun h => ⟨![![3 / 200, 1 / 40] h.1, 1 / 200], ![![-1 / 400, 1 / 400] h.2]⟩

/-- Equal masses `1/4`. -/
noncomputable def pi10 : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

/-- The holding `(a, p)`. -/
def hold (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- The instance at either rate satisfies claim 009's setting, has positive gross returns at the
original prior (`x = 0`) and centered shocks; `J = (-183/200, ∞)`; `Σ` is positive definite;
every full-class maximizer is unique for every real `x`. -/
def Valid : Prop :=
  ∀ κ ∈ ({0, 1 / 2000} : Set ℝ),
    BandSetting (data10 κ) pi10 ∧ (∀ i, (data10 κ).kplus i < 1 ∧ (data10 κ).kminus i < 1) ∧
    CenteredShocks (data10 κ) ∧ (∀ h s i, 0 < 1 + ret (data10 κ) (par10 h) s i) ∧
    Jset (data10 κ) par10 pi10 = Set.Ioi (-183 / 200) ∧
    (∀ v : Inst 1 1 → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (covariance (data10 κ) *ᵥ v)) ∧
    ∀ x w w', w ∈ maximizers (Qx (data10 κ) par10 pi10 x) (F (data10 κ)) →
      w' ∈ maximizers (Qx (data10 κ) par10 pi10 x) (F (data10 κ)) → w = w'

/-- The rows of the tables at rate `κ`: for every `x` the unique ETF-only optimum is
`(1/2, p_E)` with zero cash; `I`, `α_c` and `C_κ = [L, U]` are as given; `C_κ ⊆ J`. -/
def Row (κ pE : ℝ) (I : Set ℝ) (αc L U : ℝ) : Prop :=
  (∀ x, hold (1 / 2) pE ∈ maximizers (Qx (data10 κ) par10 pi10 x) (E (data10 κ)) ∧
    ∀ w ∈ maximizers (Qx (data10 κ) par10 pi10 x) (E (data10 κ)), w = hold (1 / 2) pE) ∧
  cash (data10 κ) (hold (1 / 2) pE) = 0 ∧
  Iset (data10 κ) par10 pi10 (hold (1 / 2) pE) = I ∧
  alphaC (data10 κ) par10 pi10 (hold (1 / 2) pE) = αc ∧
  Cset (data10 κ) par10 pi10 = Set.Icc L U ∧
  Cset (data10 κ) par10 pi10 ⊆ Jset (data10 κ) par10 pi10

/-- The two rows and the strict narrowing. -/
def Tables : Prop :=
  Row 0 (1 / 2) (Set.Icc 0 (1319 / 80000)) (-23 / 1250) (-23 / 1250) (-153 / 80000) ∧
  Row (1 / 2000) (1000 / 2001) {11032 / 690345} (-61367 / 3335000)
    (-808663 / 276138000) (-38269 / 20010000) ∧
  (-153 / 80000 : ℝ) - (-23 / 1250) = 1319 / 80000 ∧
  (-38269 / 20010000 : ℝ) - (-808663 / 276138000) = 701377 / 690345000 ∧
  (1319 / 80000 : ℝ) - 701377 / 690345000 = 170890979 / 11045520000 ∧
  (0 : ℝ) < 170890979 / 11045520000

/-- Corrected scope: with `lo` and `hi` fixed, claim 009's interior width increases in each
active rate with slopes `1 + hi` and `1 + lo`. -/
def Scope : Prop :=
  ∀ b₁ b₂ s₁ s₂ lo hi : ℝ,
    (b₂ * (1 + hi) + s₁ * (1 + lo) + (hi - lo)) - (b₁ * (1 + hi) + s₁ * (1 + lo) + (hi - lo))
      = (b₂ - b₁) * (1 + hi) ∧
    (b₁ * (1 + hi) + s₂ * (1 + lo) + (hi - lo)) - (b₁ * (1 + hi) + s₁ * (1 + lo) + (hi - lo))
      = (s₂ - s₁) * (1 + lo)

/-- Claim 010, all parts. -/
def statement : Prop := Valid ∧ Tables ∧ Scope

end Standalone.M2HigherCostNarrowerBand

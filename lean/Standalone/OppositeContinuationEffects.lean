import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M3FiniteContinuation

/-!
# Claim 012: future ETF adjustment can increase the root active advantage while future active
trading reduces it

Statement only; the proof is `Novel/OppositeContinuationEffectsProof.lean`.

The assumed M3 family `ocInst bA bE sA sE` is built on claim 011's formal M3 objects
(`Standalone/M3FiniteContinuation.lean`): `Pol`, `Phi`, `V`, `CE`, `Delta` and `obs`. It has one
active fund and one ETF with loadings `B^A = (1, 0)`, `B^E = (0, 1)`, zero drag, `ρ = 20`, zero
initial risky holdings and initial cash `W₀⁻ = 1`, one scenario of mass one with zero shocks, and
two equally likely parameters `θ₊ = (1/2, -1/2, 0)` (`true`) and `θ₋ = (-1/2, 1/2, 0)` (`false`).
`bA, bE` are the active and ETF purchase rates, and `sA, sE` the sale rates; the claim holds for
every choice of the four in `[0, 1/100]`.
-/

namespace Standalone.OppositeContinuationEffects

open Matrix Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation

/-- The data: loadings `(1, 0)` and `(0, 1)`, zero drag, rates, zero shocks, initial cash one. -/
noncomputable def ocData (bA bE sA sE : ℝ) : Data 1 1 2 (Fin 1) where
  BA := !![1, 0]
  BE := !![0, 1]
  cE := 0
  kplus := Sum.elim (fun _ => bA) (fun _ => bE)
  kminus := Sum.elim (fun _ => sA) (fun _ => sE)
  gamma := 0
  q := fun _ => 1
  zf := 0
  zA := 0
  zE := 0
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- `θ₊ = (1/2, -1/2, 0)` for `true`, `θ₋ = (-1/2, 1/2, 0)` for `false`. -/
noncomputable def ocPar : Bool → Params 1 2
  | true => ⟨![1 / 2, -1 / 2], ![0]⟩
  | false => ⟨![-1 / 2, 1 / 2], ![0]⟩

/-- The instance: equal prior masses and `ρ = 20`. -/
noncomputable def ocInst (bA bE sA sE : ℝ) : M3 1 2 (Fin 1) Bool :=
  ⟨ocData bA bE sA sE, ocPar, fun _ => 1 / 2, 20⟩

/-- The rate box `[0, 1/100]⁴`. -/
def InBox (bA bE sA sE : ℝ) : Prop :=
  0 ≤ bA ∧ bA ≤ 1 / 100 ∧ 0 ≤ bE ∧ bE ≤ 1 / 100 ∧ 0 ≤ sA ∧ sA ≤ 1 / 100 ∧ 0 ≤ sE ∧ sE ≤ 1 / 100

/-- Every member is an M3 instance; the first-quarter observations of `θ₊` and `θ₋` differ, so
the public observation identifies the parameter. -/
def ValidFamily : Prop :=
  ∀ bA bE sA sE, InBox bA bE sA sE →
    M3Setting (ocInst bA bE sA sE) ∧
      obs (ocInst bA bE sA sE) true (0 : Fin 1) ≠ obs (ocInst bA bE sA sE) false (0 : Fin 1)

/-- The uniform bounds and the opposite-sign contributions, for every member. -/
def Bounds : Prop :=
  ∀ bA bE sA sE, InBox bA bE sA sE →
    let P := ocInst bA bE sA sE
    0 ≤ Delta P .N ∧ Delta P .N ≤ 1 / 4 ∧ 507 / 2020 < Delta P .E ∧
    0 ≤ Delta P .F ∧ Delta P .F ≤ 3 / 202 ∧
    1 / 1010 < Delta P .E - Delta P .N ∧ Delta P .F - Delta P .E < -477 / 2020

/-- Every full-root optimum with future ETF-only trading buys a positive active holding. -/
def ActivePurchase : Prop :=
  ∀ bA bE sA sE, InBox bA bE sA sE →
    ∀ π ∈ Pol (ocInst bA bE sA sE) .F .E,
      IsMaxOn (Phi (ocInst bA bE sA sE)) (Pol (ocInst bA bE sA sE) .F .E) π → 0 < π.1 (Sum.inl 0)

/-- At zero rates, `Δ_F = 0` and keeping all wealth in cash at the root (root trade zero) is an
optimum with full future trading (existence, not uniqueness). -/
def ZeroFee : Prop :=
  Delta (ocInst 0 0 0 0) .F = 0 ∧
  ∃ π ∈ Pol (ocInst 0 0 0 0) .F .F, IsMaxOn (Phi (ocInst 0 0 0 0)) (Pol (ocInst 0 0 0 0) .F .F) π ∧
    π.1 = 0

/-- Claim 012, all parts. -/
def statement : Prop := ValidFamily ∧ Bounds ∧ ActivePurchase ∧ ZeroFee

end Standalone.OppositeContinuationEffects

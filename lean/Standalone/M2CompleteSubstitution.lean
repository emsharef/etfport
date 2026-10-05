import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M2EtfExposureGeometry

/-!
# Claim 006: complete feasible exposure substitution need not eliminate an active-trading advantage

Statement only; the proof is `Novel/M2CompleteSubstitutionProof.lean`.

One fully specified, assumed M2 instance, built from the M2 objects of claim 003
(`Standalone/M2ScoreAccounting.lean`), claim 004's hypotheses and claim 005's exposure sets. One
active fund and one ETF (m = n = 1), K = 2, two scenarios (`Fin 2`) and two support points
(`Fin 2`). A holding `(a, p)` is `hold a p`; every holding has this form (`hold_surjective`).
-/

namespace Standalone.M2CompleteSubstitution

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry

/-- The example's M2 data: `W⁻ = 1` (all cash), loadings `B^A = B^E = (1, 0)`, zero drag, every
purchase and sale rate `1/100`, `γ = 1`, scenario masses `1/2`, factor shocks `(±1/10, 0)`, zero
residuals, both limits one. -/
noncomputable def exData : Data 1 1 2 (Fin 2) where
  BA := !![1, 0]
  BE := !![1, 0]
  cE := 0
  kplus := fun _ => 1 / 100
  kminus := fun _ => 1 / 100
  gamma := 1
  q := fun _ => 1 / 2
  zf := ![![1 / 10, 0], ![-1 / 10, 0]]
  zA := 0
  zE := 0
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- The two support points `(λ₁, λ₂, α)`: `(1/100, 0, 0)` and `(3/100, 0, 1/50)`. -/
noncomputable def exPar : Fin 2 → Params 1 2 :=
  ![⟨![1 / 100, 0], ![0]⟩, ⟨![3 / 100, 0], ![1 / 50]⟩]

/-- Belief mass `1/2` on each support point. -/
noncomputable def exPi : Fin 2 → ℝ := fun _ => 1 / 2

/-- The holding `(a, p)`. -/
def hold (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- The criterion `Q̄_0` of the example. -/
noncomputable def Qbar : (Inst 1 1 → ℝ) → ℝ := beliefScore exData exPar exPi

/-- The largest feasible total risky holding, `100/101`. -/
noncomputable def tmax : ℝ := 100 / 101

/-- `w` is the unique maximizer of `f` on `A`. -/
def UniqueMax (f : (Inst 1 1 → ℝ) → ℝ) (A : Set (Inst 1 1 → ℝ)) (w : Inst 1 1 → ℝ) : Prop :=
  w ∈ A ∧ ∀ w' ∈ A, w' ≠ w → f w' < f w

/-- The data satisfy every M2 restriction. -/
def ValidInstance : Prop :=
  W0 exData = 1 ∧ InitialPosition exData ∧ RatesNonneg exData ∧
  (∀ i, exData.kplus i < 1 ∧ exData.kminus i < 1) ∧ (∀ i, exData.wbar i ≤ 1) ∧
  0 ≤ exData.gamma ∧ (∀ s, 0 ≤ exData.q s) ∧ MassesSumToOne exData ∧ CenteredShocks exData ∧
  (∀ t, 0 ≤ exPi t) ∧ ∑ t, exPi t = 1 ∧ (∀ t s i, 0 < 1 + ret exData (exPar t) s i)

/-- Every holding is some `(a, p)`; the classes F, E, N, the exposure `b(a, p) = (a + p, 0)` and
`B_E = D_E = {(t, 0) : 0 ≤ t ≤ 100/101}`. -/
def ClassesAndExposure : Prop :=
  (∀ w, w = hold (w (Sum.inl 0)) (w (Sum.inr 0))) ∧
  (∀ a p, hold a p ∈ F exData ↔ 0 ≤ a ∧ 0 ≤ p ∧ a + p ≤ tmax) ∧
  (∀ a p, hold a p ∈ E exData ↔ a = 0 ∧ 0 ≤ p ∧ p ≤ tmax) ∧
  N exData = {hold 0 0} ∧
  (∀ a p, exposure exData (hold a p) = ![a + p, 0]) ∧
  BEset exData = (fun t : ℝ => ![t, 0]) '' Set.Icc 0 tmax ∧
  DE exData = (fun t : ℝ => ![t, 0]) '' Set.Icc 0 tmax

/-- Complete feasible substitution: for every `(a, p) ∈ F`, the ETF-only `(0, a + p)` is in E with
the same exposure, conditional variance `w'Σw`, review cost and cash. The second-factor direction
is outside the span of both the ETF and the active loadings. -/
def CompleteSubstitution : Prop :=
  (∀ a p, hold a p ∈ F exData →
    hold 0 (a + p) ∈ E exData ∧
    exposure exData (hold 0 (a + p)) = exposure exData (hold a p) ∧
    hold 0 (a + p) ⬝ᵥ (covariance exData *ᵥ hold 0 (a + p))
      = hold a p ⬝ᵥ (covariance exData *ᵥ hold a p) ∧
    tau exData (hold 0 (a + p) - w0 exData) = tau exData (hold a p - w0 exData) ∧
    cash exData (hold 0 (a + p)) = cash exData (hold a p)) ∧
  (![0, 1] : Fin 2 → ℝ) ∉ LE exData ∧
  (![0, 1] : Fin 2 → ℝ) ∉ Set.range fun a : Fin 1 → ℝ => exData.BAᵀ *ᵥ a

/-- For nonnegative holdings: `w'Σw = t²/100`, `τ = t/100`, `k = 1 - (101/100) t`,
`Q̄_0(a, p) = t/100 + a/100 - t²/200` and the matched difference `Q̄_0(a, p) - Q̄_0(0, t) = a/100`,
which is `0` at the first support point and `a/50` at the second (t = a + p). -/
def ScoreFormulas : Prop :=
  ∀ a p : ℝ, 0 ≤ a → 0 ≤ p →
    hold a p ⬝ᵥ (covariance exData *ᵥ hold a p) = (a + p) ^ 2 / 100 ∧
    tau exData (hold a p - w0 exData) = (a + p) / 100 ∧
    cash exData (hold a p) = 1 - 101 / 100 * (a + p) ∧
    Qbar (hold a p) = (a + p) / 100 + a / 100 - (a + p) ^ 2 / 200 ∧
    Qbar (hold a p) - Qbar (hold 0 (a + p)) = a / 100 ∧
    score exData (hold a p) (exPar 0) - score exData (hold 0 (a + p)) (exPar 0) = 0 ∧
    score exData (hold a p) (exPar 1) - score exData (hold 0 (a + p)) (exPar 1) = a / 50

/-- The unique maximizers, their cash, review cost and scores, the equal exposures of the E and
F optima, and the optimized gap `1/101 > 0`. -/
def OptimaAndGap : Prop :=
  UniqueMax Qbar (N exData) (hold 0 0) ∧
  UniqueMax Qbar (E exData) (hold 0 tmax) ∧
  UniqueMax Qbar (F exData) (hold tmax 0) ∧
  cash exData (hold 0 0) = 1 ∧ cash exData (hold 0 tmax) = 0 ∧ cash exData (hold tmax 0) = 0 ∧
  tau exData (hold 0 0 - w0 exData) = 0 ∧ tau exData (hold 0 tmax - w0 exData) = 1 / 101 ∧
  tau exData (hold tmax 0 - w0 exData) = 1 / 101 ∧
  Qbar (hold 0 0) = 0 ∧ Qbar (hold 0 tmax) = 51 / 10201 ∧ Qbar (hold tmax 0) = 152 / 10201 ∧
  exposure exData (hold 0 tmax) = exposure exData (hold tmax 0) ∧
  Qbar (hold tmax 0) - Qbar (hold 0 tmax) = 1 / 101 ∧ (0 : ℝ) < 1 / 101

/-- Claim 006, all parts. -/
def statement : Prop :=
  ValidInstance ∧ ClassesAndExposure ∧ CompleteSubstitution ∧ ScoreFormulas ∧ OptimaAndGap

end Standalone.M2CompleteSubstitution

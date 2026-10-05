import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Standalone.M4JointDirectionalRate

/-!
# Claim 017: quadratic entry changes the history rate in economic advantage

Statement only; the proof is `Novel/M4CurvedEntryRateProof.lean`.

The formal M4 objects are those of `Standalone/M4InformationObstruction.lean`: `Rule`, `Cset`,
`LN`, `wHatF`, `vHatE`, `tcrit`, `Omega`, `thetaHat`, `hist`, `mass`, `Adv`, `Gstar` and
`etfSup`. Claim 015 supplies the requirement predicates `falseP`, `powerP` and `Meets`. Claim 016
supplies the law class `InKJ` (finite laws with `E U = 0`, `E U U' = I₃` and `‖U‖ ≤ 9`) and the
rule restriction `AdmitsJ` (certify a funded active action or fall back to a funded ETF-only
action).

**The family.** One active fund and one ETF, `B^A = (1, 0)`, `B^E = (0, 1)`, zero costs and drag,
caps one, zero risky holdings with cash one, and risk aversion `γ = 1/s²` with `s ∈ (0, 1/100]`.
The domain is `Θ₄ = c + s[-1, 1]³` with `c = (0, 1/4, 0)`, and the M4 shocks are
`(z^f₁, z^f₂, z^A) = s U` with `z^E = 0`. The active mean signal is `x = λ₁ + α`.

**The certificate.** On the estimate `θ̂`, `x̂ = λ̂₁ + α̂`, `â = max(x̂, 0)/2`, `p̂ = λ̂₂` and
`ρ_N = s √(t_{N,ε}/N)`. The bound is
`ℓ_N = â x̂ - â² - √2 â ρ_N - ρ_N²/2`. The gate implements M4's plug-in full optimizer when
`C_N` (with `η = ε`) is nonempty, that optimizer is funded, `â > 0` and `ℓ_N > δ/4`; otherwise it
implements M4's plug-in fallback.
-/

namespace Standalone.M4CurvedEntryRate

open Matrix MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
open Standalone.M4BoundedLawRate (falseP powerP Meets)
open Standalone.M4JointDirectionalRate (InKJ AdmitsJ)
open scoped Classical

noncomputable section

/-- The centre `c = (0, 1/4, 0)`. -/
def cC : Fin 3 → ℝ := ![0, 1 / 4, 0]

/-- The vertices `c + s v`, `v ∈ {±1}³`. -/
def V4 (s : ℝ) : Finset (Fin 3 → ℝ) :=
  Finset.univ.image fun b : Fin 3 → Bool => cC + s • fun i => if b i then 1 else -1

/-- The M4 data for the law `(q, U)`: `(z^f₁, z^f₂, z^A) = s U`, `z^E = 0`, `γ = 1/s²`. -/
def data (s : ℝ) {S : Type} (q : S → ℝ) (U : S → Fin 3 → ℝ) : Data 1 1 2 S where
  BA := !![1, 0]
  BE := !![0, 1]
  cE := 0
  kplus := 0
  kminus := 0
  gamma := 1 / s ^ 2
  q := q
  zf := fun x => ![s * U x 0, s * U x 1]
  zA := fun x => ![s * U x 2]
  zE := 0
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- The active mean signal `x = λ₁ + α`. -/
def xs (θ : Fin 3 → ℝ) : ℝ := θ 0 + θ 2

/-- The holding `(a, p)`. -/
def act (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- `ρ_N = s √(t_{N,ε}/N)`. -/
def rho (s : ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) (N : ℕ) (ε : ℝ) : ℝ :=
  s * Real.sqrt (tcrit D N ε / N)

/-- `â = max(x̂, 0)/2`. -/
def ahat {S : Type} (D : Data 1 1 2 S) {N : ℕ} (H : Fin N → Record 1) : ℝ :=
  max (xs (thetaHat D H)) 0 / 2

/-- `ℓ_N = â x̂ - â² - √2 â ρ_N - ρ_N²/2`. -/
def ellC (s : ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ} (ε : ℝ)
    (H : Fin N → Record 1) : ℝ :=
  ahat D H * xs (thetaHat D H) - ahat D H ^ 2 - Real.sqrt 2 * ahat D H * rho s D N ε
    - rho s D N ε ^ 2 / 2

/-- The gate certifies: `C_N` nonempty, the plug-in optimizer funded, `â > 0` and `ℓ_N > δ/4`. -/
def certC (s : ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ} (δ ε : ℝ)
    (H : Fin N → Record 1) : Prop :=
  (Cset D (V4 s) N ε (thetaHat D H)).Nonempty ∧ wHatF D (thetaHat D H) ∈ F D ∧ 0 < ahat D H ∧
    δ / 4 < ellC s D ε H

/-- M4's plug-in rule with the conservative certificate. -/
def gateC (s : ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) (N : ℕ) (δ ε : ℝ) : Rule N where
  kernel H := Measure.dirac
    (if certC s D δ ε H then wHatF D (thetaHat D H) else vHatE D (thetaHat D H))
  isProb _ := inferInstance

/-- Part 1: admissibility, `Ω`, `Σ`, the classes and the quadratic score, and on `Θ₄` the unique
optimizers, `sup_E Q`, `G_*`, strict funding slack, the whole-class advantage of every holding,
negative advantage below entry, and the entry scale `2√δ` with holding `√δ`. -/
def Geometry : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 100 →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      M4Admissible (data s q U) (V4 s) ∧
      Theta4 (V4 s) = {θ | ∀ i, |θ i - cC i| ≤ s} ∧
      Omega (data s q U) = s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
      covariance (data s q U) = Matrix.diagonal (act (2 * s ^ 2) (s ^ 2)) ∧
      F (data s q U) = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧
        w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} ∧
      E (data s q U) = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} ∧
      (∀ θ w, score (data s q U) w (toPar θ) = w (Sum.inl 0) * xs θ + w (Sum.inr 0) * θ 1
        - w (Sum.inl 0) ^ 2 - w (Sum.inr 0) ^ 2 / 2) ∧
      ∀ θ ∈ Theta4 (V4 s),
        maximizers (fun v => score (data s q U) v (toPar θ)) (E (data s q U)) = {act 0 (θ 1)} ∧
        maximizers (fun w => score (data s q U) w (toPar θ)) (F (data s q U))
          = {act (max (xs θ) 0 / 2) (θ 1)} ∧
        etfSup (data s q U) θ = θ 1 ^ 2 / 2 ∧
        Gstar (data s q U) θ = max (xs θ) 0 ^ 2 / 4 ∧
        0 < θ 1 ∧ max (xs θ) 0 / 2 + θ 1 < 1 ∧
        (∀ a p : ℝ, Adv (data s q U) (act a p) θ = a * xs θ - a ^ 2 - (p - θ 1) ^ 2 / 2) ∧
        (xs θ < 0 → ∀ w ∈ F (data s q U), 0 < w (Sum.inl 0) → Adv (data s q U) w θ < 0) ∧
        ∀ δ : ℝ, 0 < δ → (δ ≤ Gstar (data s q U) θ ↔ 2 * Real.sqrt δ ≤ xs θ) ∧
          (Gstar (data s q U) θ = δ → max (xs θ) 0 / 2 = Real.sqrt δ)

/-- Part 2, lower bound: if at length `N_obs` every law in `K_s` admits a rule meeting both
requirements, then `N_obs ≥ s² log(1/ε)/(32π² δ)`. -/
def LowerBound : Prop :=
  ∀ s δ ε : ℝ, 0 < s → s ≤ 1 / 100 → 0 < δ → δ ≤ s ^ 2 / 128 → 0 < ε → ε ≤ 1 / 16 →
    ∀ N : ℕ, 0 < N →
      (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
        ∃ ρ : Rule N, AdmitsJ (data s q U) ρ ∧ Meets (data s q U) (V4 s) δ ε ρ) →
      s ^ 2 / (32 * Real.pi ^ 2 * δ) * Real.log (1 / ε) ≤ N

/-- Part 2, upper bound: for every law in `K_s` and `N_obs ≥ 768 (s²/δ) log(6/ε)`, the gate meets
both requirements. -/
def UpperBound : Prop :=
  ∀ s δ ε : ℝ, 0 < s → s ≤ 1 / 100 → 0 < δ → δ ≤ s ^ 2 / 128 → 0 < ε → ε ≤ 1 / 16 →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      ∀ N : ℕ, 768 * (s ^ 2 / δ) * Real.log (6 / ε) ≤ N →
        AdmitsJ (data s q U) (gateC s (data s q U) N δ ε) ∧
        Meets (data s q U) (V4 s) δ ε (gateC s (data s q U) N δ ε)

/-- Part 3: on every history from the domain the plug-in optimizer is the funded `(â, p̂)` and the
fallback is the funded `(0, p̂)`; for nonempty `C_N`, `ℓ_N ≤ L_N(â, p̂)`; and on coverage at an
alternative with `G_* ≥ δ` and `ρ_N ≤ √δ/8`, `ℓ_N ≥ 5δ/8`. -/
def CurvedCertificate : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 100 →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      ∀ (N : ℕ) (ε : ℝ), 0 < N →
        (∀ θ ∈ Theta4 (V4 s), ∀ σ : Fin N → S,
          let th := thetaHat (data s q U) (hist (data s q U) θ σ)
          wHatF (data s q U) th = act (ahat (data s q U) (hist (data s q U) θ σ)) (th 1) ∧
          vHatE (data s q U) th = act 0 (th 1) ∧
          act (ahat (data s q U) (hist (data s q U) θ σ)) (th 1) ∈ F (data s q U) ∧
          act 0 (th 1) ∈ E (data s q U)) ∧
        (∀ H : Fin N → Record 1,
          (Cset (data s q U) (V4 s) N ε (thetaHat (data s q U) H)).Nonempty →
          ((ellC s (data s q U) ε H : ℝ) : EReal) ≤ LN (data s q U) (V4 s) N ε
            (thetaHat (data s q U) H)
            (act (ahat (data s q U) H) (thetaHat (data s q U) H 1))) ∧
        ∀ δ : ℝ, 0 < δ → ∀ θ ∈ Theta4 (V4 s), δ ≤ Gstar (data s q U) θ →
          rho s (data s q U) N ε ≤ Real.sqrt δ / 8 → ∀ σ : Fin N → S,
          θ ∈ Cset (data s q U) (V4 s) N ε (thetaHat (data s q U) (hist (data s q U) θ σ)) →
          5 * δ / 8 ≤ ellC s (data s q U) ε (hist (data s q U) θ σ)

/-- Claim 017, all parts. -/
def statement : Prop := Geometry ∧ LowerBound ∧ UpperBound ∧ CurvedCertificate

end

end Standalone.M4CurvedEntryRate

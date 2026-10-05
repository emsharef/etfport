import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Standalone.M4InformationObstruction

/-!
# Claim 015: a worst-case history-length rate for a funded unspanned-factor trade

Statement only; the proof is `Novel/M4BoundedLawRateProof.lean`.

The formal M4 objects are those of `Standalone/M4InformationObstruction.lean`, built on claim 003's
M2 objects: histories, `mass`, `hist`, `θ̂_N`, `Ω`, `t_{N,η}`, `C_N`, `Adv`, `G_*`, `L_N`, the
plug-in maximizers `ŵ_F` and `v̂_E`, and `Rule` (a probability measure on actions for each full
history). Only the definitions are used here, not claim 014's results.

**The family.**
- One active fund and one ETF, with `B^A = (d, 0)`, `B^E = (0, 1)`, `γ = 0`, zero drag, purchase
  rates `κ_A, κ_E`, zero sale rates, zero risky holdings with cash one, and caps `(ā, 1)`.
- A parameter is `θ = (λ, μ, 0)` with `Θ₄ = conv{(λ₀ ± H, μ, 0)}`.
- A law in `K_H` is a finite scenario type with masses `q ≥ 0` summing to one and a centered
  shock `Z` with `|Z| ≤ H` at every scenario. The M4 shocks are `z^f = (Z, 0)` and `z^A = z^E = 0`.
- `Inputs` collects `d, μ, H, κ_A, κ_E, ā, δ, ε`, with the derived `q_E`, `λ₀`, `A`, `D`, `w_A`
  and `v_E`.

**Requirements.** A rule is carried by `v_E` and the feasible actions with `a > 0`, and
certifying means choosing `a > 0`. It meets the requirements if, for every `θ ∈ Θ₄`,
`P_θ(certify and Adv ≤ δ/4) ≤ ε`, and, for every `θ ∈ Θ₄` with `G_*(θ) ≥ δ`,
`P_θ(certify and Adv > δ/4) ≥ 1 - ε`.
-/

namespace Standalone.M4BoundedLawRate

open Matrix MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
open scoped Classical

noncomputable section

/-- The fixed inputs: loading `d`, second premium `μ`, domain half-width `H`, purchase rates
`κ_A, κ_E`, active cap `ā`, score margin `δ` and error allowance `ε`. -/
structure Inputs where
  d : ℝ
  mu : ℝ
  H : ℝ
  kA : ℝ
  kE : ℝ
  abar : ℝ
  delta : ℝ
  eps : ℝ

namespace Inputs

variable (P : Inputs)

/-- `q_E = (μ - κ_E)/(1 + κ_E)`. -/
def qE : ℝ := (P.mu - P.kE) / (1 + P.kE)

/-- `λ₀ = [κ_A + (1 + κ_A) q_E]/d`. -/
def lam0 : ℝ := (P.kA + (1 + P.kA) * P.qE) / P.d

/-- The maximum funded active holding `A = min(ā, 1/(1 + κ_A))`. -/
def A : ℝ := min P.abar (1 / (1 + P.kA))

/-- The exposure mismatch `D = d A`. -/
def Dm : ℝ := P.d * P.A

/-- `w_A = (A, [1 - (1 + κ_A) A]/(1 + κ_E))`. -/
def wA : Inst 1 1 → ℝ :=
  Sum.elim (fun _ => P.A) (fun _ => (1 - (1 + P.kA) * P.A) / (1 + P.kE))

/-- `v_E = (0, 1/(1 + κ_E))`. -/
def vE : Inst 1 1 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1 / (1 + P.kE))

/-- The parameter `(λ, μ, 0)`. -/
def par (lam : ℝ) : Fin 3 → ℝ := ![lam, P.mu, 0]

/-- The two domain endpoints. -/
def V4 : Finset (Fin 3 → ℝ) := {P.par (P.lam0 - P.H), P.par (P.lam0 + P.H)}

/-- The stated ranges. -/
def InRange : Prop :=
  0 < P.d ∧ P.kE < P.mu ∧ 0 < P.H ∧ P.d * P.H ≤ 1 / 4 ∧
  0 ≤ P.kA ∧ P.kA < 1 ∧ 0 ≤ P.kE ∧ P.kE < 1 ∧ 0 < P.abar ∧ P.abar ≤ 1 ∧
  0 < P.delta ∧ P.delta ≤ P.Dm * P.H / 2 ∧ 0 < P.eps ∧ P.eps ≤ 1 / 16

end Inputs

/-- A law in `K_H`: masses `q ≥ 0` summing to one, `E Z = 0` and `|Z| ≤ H`. -/
def InKH {S : Type} [Fintype S] (H : ℝ) (q Z : S → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧ ∑ s, q s * Z s = 0 ∧ ∀ s, |Z s| ≤ H

/-- The M4 data of the family for the law `(q, Z)`. -/
def data (P : Inputs) {S : Type} (q Z : S → ℝ) : Data 1 1 2 S where
  BA := !![P.d, 0]
  BE := !![0, 1]
  cE := 0
  kplus := Sum.elim (fun _ => P.kA) (fun _ => P.kE)
  kminus := 0
  gamma := 0
  q := q
  zf := fun s => ![Z s, 0]
  zA := 0
  zE := 0
  x0 := 0
  h0 := 1
  wbar := Sum.elim (fun _ => P.abar) (fun _ => 1)

section Rules

variable {S : Type} [Fintype S] {N : ℕ}

/-- The rule either certifies a feasible action with `a > 0` or falls back to `v`. -/
def AdmitsV (D : Data 1 1 2 S) (v : Inst 1 1 → ℝ) (ρ : Rule N) : Prop :=
  ∀ H, ρ.kernel H {w | w ≠ v ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} = 0

/-- `P_θ(certify and Adv ≤ δ/4)`. -/
def falseP (D : Data 1 1 2 S) (δ : ℝ) (θ : Fin 3 → ℝ) (ρ : Rule N) : ℝ :=
  ∑ σ : Fin N → S, mass D σ *
    (ρ.kernel (hist D θ σ) {w | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δ / 4}).toReal

/-- `P_θ(certify and Adv > δ/4)`. -/
def powerP (D : Data 1 1 2 S) (δ : ℝ) (θ : Fin 3 → ℝ) (ρ : Rule N) : ℝ :=
  ∑ σ : Fin N → S, mass D σ *
    (ρ.kernel (hist D θ σ) {w | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv D w θ}).toReal

/-- Both requirements of part 2, uniformly over `Θ₄`. -/
def Meets (D : Data 1 1 2 S) (V : Finset (Fin 3 → ℝ)) (δ ε : ℝ) (ρ : Rule N) : Prop :=
  (∀ θ ∈ Theta4 V, falseP D δ θ ρ ≤ ε) ∧
  (∀ θ ∈ Theta4 V, δ ≤ Gstar D θ → 1 - ε ≤ powerP D δ θ ρ)

end Rules

/-- `r_B = H √(2 log(2/ε)/N_obs)`. -/
def rB (P : Inputs) (N : ℕ) : ℝ := P.H * Real.sqrt (2 * Real.log (2 / P.eps) / N)

/-- The conservative lower certificate `ℓ_N(w_A) = D(λ̂_N - r_B - λ₀)`. -/
def ell (P : Inputs) {S : Type} (D : Data 1 1 2 S) {N : ℕ} (H : Fin N → Record 1) : ℝ :=
  P.Dm * (thetaHat D H 0 - rB P N - P.lam0)

/-- The gate: `C_N` (with `η = ε`) nonempty, plug-in optimizer `w_A`, and `ℓ_N > δ/4`. -/
def certU (P : Inputs) {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ}
    (H : Fin N → Record 1) : Prop :=
  (Cset D P.V4 N P.eps (thetaHat D H)).Nonempty ∧ wHatF D (thetaHat D H) = P.wA ∧
    P.delta / 4 < ell P D H

/-- The conservative gate as a rule: certify `w_A` or fall back to `v_E`. -/
def gateRule (P : Inputs) {S : Type} [Fintype S] (D : Data 1 1 2 S) (N : ℕ) : Rule N where
  kernel H := Measure.dirac (if certU P D H then P.wA else P.vE)
  isProb _ := inferInstance

/-- Part 1: admissibility, the funded classes and score, the whole ETF-class optimum, the target
and gap formulas, and the exposure mismatch `D` against every ETF-only action. -/
def Geometry : Prop :=
  ∀ P : Inputs, P.InRange → ∀ (S : Type) [Fintype S] (q Z : S → ℝ), InKH P.H q Z →
    M4Admissible (data P q Z) P.V4 ∧
    Theta4 P.V4 = {θ | P.lam0 - P.H ≤ θ 0 ∧ θ 0 ≤ P.lam0 + P.H ∧ θ 1 = P.mu ∧ θ 2 = 0} ∧
    F (data P q Z) = {w | 0 ≤ w (Sum.inl 0) ∧ w (Sum.inl 0) ≤ P.abar ∧ 0 ≤ w (Sum.inr 0) ∧
      w (Sum.inr 0) ≤ 1 ∧ (1 + P.kA) * w (Sum.inl 0) + (1 + P.kE) * w (Sum.inr 0) ≤ 1} ∧
    E (data P q Z) = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1 / (1 + P.kE)} ∧
    (∀ θ, ∀ w ∈ F (data P q Z), score (data P q Z) w (toPar θ)
      = w (Sum.inl 0) * (P.d * θ 0 + θ 2 - P.kA) + w (Sum.inr 0) * (θ 1 - P.kE)) ∧
    0 < P.Dm ∧
    (∀ lam, maximizers (fun v => score (data P q Z) v (toPar (P.par lam))) (E (data P q Z))
      = {P.vE} ∧ etfSup (data P q Z) (P.par lam) = P.qE) ∧
    (∀ lam, Adv (data P q Z) P.wA (P.par lam) = P.Dm * (lam - P.lam0) ∧
      Gstar (data P q Z) (P.par lam) = P.Dm * max (lam - P.lam0) 0) ∧
    (∀ lam, lam < P.lam0 → ∀ w ∈ F (data P q Z), 0 < w (Sum.inl 0) →
      Adv (data P q Z) w (P.par lam) < 0) ∧
    (∀ lam, P.lam0 < lam →
      maximizers (fun w => score (data P q Z) w (toPar (P.par lam))) (F (data P q Z)) = {P.wA}) ∧
    ∀ v ∈ E (data P q Z), exposure (data P q Z) P.wA 0 - exposure (data P q Z) v 0 = P.Dm

/-- Part 2: if for every known law in `K_H` some full-history rule meets both requirements at
length `N_obs`, then `N_obs ≥ (DH/δ)² log(1/ε)/(4π²)`. -/
def LowerBound : Prop :=
  ∀ P : Inputs, P.InRange → ∀ N : ℕ, 0 < N →
    (∀ (S : Type) [Fintype S] (q Z : S → ℝ), InKH P.H q Z →
      ∃ ρ : Rule N, AdmitsV (data P q Z) P.vE ρ ∧ Meets (data P q Z) P.V4 P.delta P.eps ρ) →
    1 / (4 * Real.pi ^ 2) * (P.Dm * P.H / P.delta) ^ 2 * Real.log (1 / P.eps) ≤ N

/-- Part 3: for every law in `K_H` and `N_obs ≥ 32 (DH/δ)² log(2/ε)`, the conservative M4 gate
meets both requirements. `ℓ_N(w_A)` is a lower bound on M4's original `L_N(w_A)`, and it is at
least `δ/2` on the coverage event at every alternative with `G_* ≥ δ`. M4's plug-in fallback is
`v_E` on every possible history. -/
def Certificate : Prop :=
  ∀ P : Inputs, P.InRange → ∀ (S : Type) [Fintype S] (q Z : S → ℝ), InKH P.H q Z →
    ∀ N : ℕ, 32 * (P.Dm * P.H / P.delta) ^ 2 * Real.log (2 / P.eps) ≤ N →
      AdmitsV (data P q Z) P.vE (gateRule P (data P q Z) N) ∧
      Meets (data P q Z) P.V4 P.delta P.eps (gateRule P (data P q Z) N) ∧
      (∀ H : Fin N → Record 1,
        (Cset (data P q Z) P.V4 N P.eps (thetaHat (data P q Z) H)).Nonempty →
        wHatF (data P q Z) (thetaHat (data P q Z) H) = P.wA →
        ((ell P (data P q Z) H : ℝ) : EReal)
          ≤ LN (data P q Z) P.V4 N P.eps (thetaHat (data P q Z) H) P.wA) ∧
      (∀ θ ∈ Theta4 P.V4, P.delta ≤ Gstar (data P q Z) θ → ∀ σ : Fin N → S,
        θ ∈ Cset (data P q Z) P.V4 N P.eps (thetaHat (data P q Z) (hist (data P q Z) θ σ)) →
        P.delta / 2 ≤ ell P (data P q Z) (hist (data P q Z) θ σ)) ∧
      ∀ θ ∈ Theta4 P.V4, ∀ σ : Fin N → S,
        vHatE (data P q Z) (thetaHat (data P q Z) (hist (data P q Z) θ σ)) = P.vE

/-- The two lengths have the same order: `log(2/ε) ≤ (5/4) log(1/ε)` for `ε ∈ (0, 1/16]`. -/
def SameOrder : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → Real.log (2 / ε) ≤ 5 / 4 * Real.log (1 / ε)

/-- Claim 015, all parts. -/
def statement : Prop := Geometry ∧ LowerBound ∧ Certificate ∧ SameOrder

end

end Standalone.M4BoundedLawRate

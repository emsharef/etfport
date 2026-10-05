import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Standalone.M4CurvedEntryRate

/-!
# Claim 018: curvature controls certification with costs and binding constraints

Statement only; the proof is `Novel/M4CurvatureCertificateProof.lean`.

The formal M4 objects are those of `Standalone/M4InformationObstruction.lean`: `M4Admissible`,
`Theta4`, `Record`, `hist`, `mass`, `thetaHat`, `zeta`, `tcrit`, `Cset`, `LN`, `wHatF`, `vHatE`,
`Adv`, `Gstar` and `toPar`. Claim 016 supplies the law class `InKJ`. The M2 objects are claim
003's: `F`, `E`, `score`, `covariance` (`Σ`), `exposure`, `w0` and `maximizers`.

**The setting (`CurvSetting`).** Any admissible M4 instance, with any number `n` of ETFs,
directional costs, caps, drag and incumbent. It requires `γ > 0`, a positive-definite `Σ`, and a
known finite law with `ζ = (z^f₁, z^f₂, z^A) = J U`, where `U` satisfies `E U = 0`,
`E U U' = I₃` and `‖U‖ ≤ 9`. The ETF residuals are unrestricted beyond M4 admissibility.
- `A w = (b(w), a)`; `K = (1/γ) sup_{z ≠ 0} ‖J'Az‖²/(z'Σz)`.
- `Ĝ = Q(ŵ_F; θ̂) - Q(v̂_E; θ̂)`, `r_N = √(t_{N,η}/N_obs)`, `u_N = K r_N²`, and
  `ℓ_N = Ĝ - √(2 u_N Ĝ) - u_N/2`.
- The gate implements `ŵ_F` when `C_N` is nonempty and `ℓ_N > δ_econ`; otherwise it implements
  `v̂_E`.

**Rules.** A rule maps each full history to a probability measure on holdings. It either
certifies a funded holding with `a ≠ a⁻` or falls back to a funded ETF-only holding. Certifying
means `a ≠ a⁻`.
-/

namespace Standalone.M4CurvatureCertificate

open Matrix MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
open Standalone.M4JointDirectionalRate (InKJ)
open scoped Classical

noncomputable section

variable {n : ℕ} {S : Type} [Fintype S]

/-- The mean-exposure map `A w = (b(w), a)`. -/
def Aw (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) : Fin 3 → ℝ :=
  ![exposure D w 0, exposure D w 1, w (Sum.inl 0)]

/-- The setting: M4 admissibility, `γ > 0`, positive-definite `Σ`, and `ζ = J U` with `U` in
`K_J`. -/
def CurvSetting (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (J : Matrix (Fin 3) (Fin 3) ℝ)
    (U : S → Fin 3 → ℝ) : Prop :=
  M4Admissible D V ∧ 0 < D.gamma ∧
  (∀ z : Inst 1 n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (covariance D *ᵥ z)) ∧
  InKJ D.q U ∧ ∀ s, zeta D s = J *ᵥ U s

/-- `K = (1/γ) sup_{z ≠ 0} ‖J'Az‖²/(z'Σz)`. -/
def Kc (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (1 / D.gamma) * sSup {r | ∃ z : Inst 1 n → ℝ, z ≠ 0 ∧
    r = (Jᵀ *ᵥ Aw D z) ⬝ᵥ (Jᵀ *ᵥ Aw D z) / (z ⬝ᵥ (covariance D *ᵥ z))}

/-- The estimated whole-class gap `Ĝ`. -/
def Ghat (D : Data 1 n 2 S) (th : Fin 3 → ℝ) : ℝ :=
  score D (wHatF D th) (toPar th) - score D (vHatE D th) (toPar th)

/-- `r_N = √(t_{N,η}/N_obs)`. -/
def rN (D : Data 1 n 2 S) (N : ℕ) (η : ℝ) : ℝ := Real.sqrt (tcrit D N η / N)

/-- `u_N = K r_N²`. -/
def uN (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ) (η : ℝ) : ℝ :=
  Kc D J * rN D N η ^ 2

/-- `ℓ_N = Ĝ - √(2 u_N Ĝ) - u_N/2`. -/
def ellG (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ) (η : ℝ)
    (th : Fin 3 → ℝ) : ℝ :=
  Ghat D th - Real.sqrt (2 * uN D J N η * Ghat D th) - uN D J N η / 2

/-- A randomized rule for any number of ETFs: a probability measure on holdings per history. -/
structure RuleG (n N : ℕ) where
  kernel : (Fin N → Record n) → Measure (Inst 1 n → ℝ)
  isProb : ∀ H, IsProbabilityMeasure (kernel H)

/-- The gate certifies: `C_N` nonempty and `ℓ_N > δ_econ`. -/
def certG (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (J : Matrix (Fin 3) (Fin 3) ℝ) {N : ℕ}
    (η δe : ℝ) (H : Fin N → Record n) : Prop :=
  (Cset D V N η (thetaHat D H)).Nonempty ∧ δe < ellG D J N η (thetaHat D H)

/-- The gate: M4's funded full optimizer when certified, M4's ETF-only optimizer otherwise. -/
def gateG (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (J : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ)
    (η δe : ℝ) : RuleG n N where
  kernel H := Measure.dirac
    (if certG D V J η δe H then wHatF D (thetaHat D H) else vHatE D (thetaHat D H))
  isProb _ := inferInstance

/-- The rule certifies a funded holding with `a ≠ a⁻` or falls back to a funded ETF-only one. -/
def AdmitsG (D : Data 1 n 2 S) {N : ℕ} (ρ : RuleG n N) : Prop :=
  ∀ H, ρ.kernel H {w | ¬ (w ∈ F D ∧ w (Sum.inl 0) ≠ w0 D (Sum.inl 0)) ∧ w ∉ E D} = 0

/-- `P_θ(certify and Adv ≤ δ_econ)`. -/
def falseG (D : Data 1 n 2 S) (δe : ℝ) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : RuleG n N) : ℝ :=
  ∑ σ : Fin N → S, mass D σ * (ρ.kernel (hist D θ σ)
    {w | w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧ Adv D w θ ≤ δe}).toReal

/-- `P_θ(certify and Adv > δ_econ)`. -/
def powerG (D : Data 1 n 2 S) (δe : ℝ) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : RuleG n N) : ℝ :=
  ∑ σ : Fin N → S, mass D σ * (ρ.kernel (hist D θ σ)
    {w | w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧ δe < Adv D w θ}).toReal

/-- Both requirements with `δ_econ = δ/4`, uniformly over `Θ₄`. -/
def MeetsG (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (δ ε : ℝ) {N : ℕ} (ρ : RuleG n N) :
    Prop :=
  (∀ θ ∈ Theta4 V, falseG D (δ / 4) θ ρ ≤ ε) ∧
  (∀ θ ∈ Theta4 V, δ ≤ Gstar D θ → 1 - ε ≤ powerG D (δ / 4) θ ρ)

/-- Part 1, for every design and law in the setting:
- `K` is finite, bounds every direction and is attained on `z'Σz = 1`;
- both plug-in maxima are unique, and `Ĝ ≥ 0`;
- `ℓ_N ≤ L_N(ŵ_F)` for nonempty `C_N` at every positive length;
- `ℓ_N > δ_econ ≥ 0` forces `a ≠ a⁻`;
- the gate's false-certification probability is at most `η` at every `θ ∈ Θ₄` (any `δ_econ`). -/
def Certificate : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ))
    (J : Matrix (Fin 3) (Fin 3) ℝ) (U : S → Fin 3 → ℝ), CurvSetting D V J U →
    (0 ≤ Kc D J ∧
      (∀ z, (Jᵀ *ᵥ Aw D z) ⬝ᵥ (Jᵀ *ᵥ Aw D z) ≤ D.gamma * Kc D J * (z ⬝ᵥ (covariance D *ᵥ z))) ∧
      ∃ z, z ⬝ᵥ (covariance D *ᵥ z) = 1 ∧
        (Jᵀ *ᵥ Aw D z) ⬝ᵥ (Jᵀ *ᵥ Aw D z) = D.gamma * Kc D J) ∧
    (∀ th, maximizers (fun w => score D w (toPar th)) (F D) = {wHatF D th} ∧
      maximizers (fun w => score D w (toPar th)) (E D) = {vHatE D th} ∧ 0 ≤ Ghat D th) ∧
    (∀ (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ), 0 < N → (Cset D V N η th).Nonempty →
      ((ellG D J N η th : ℝ) : EReal) ≤ LN D V N η th (wHatF D th)) ∧
    (∀ (N : ℕ) (η δe : ℝ) (th : Fin 3 → ℝ), 0 ≤ δe → δe < ellG D J N η th →
      wHatF D th (Sum.inl 0) ≠ w0 D (Sum.inl 0)) ∧
    ∀ (N : ℕ) (η δe : ℝ), 0 < N → 0 ≤ η → ∀ θ ∈ Theta4 V,
      falseG D δe θ (gateG D V J N η δe) ≤ η

/-- Part 2: for every estimate, `u_N ≤ δ/128` and `G_*(θ) ≥ δ` at a `θ` in its `C_N` give
`ℓ_N > δ/2`; both requirements hold for `N_obs ≥ max(324, 1536 K/δ) log(6/ε)`; and if `K = 0`
then `ℓ_N = G_*(θ_*)` on every history at every positive length. -/
def Power : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ))
    (J : Matrix (Fin 3) (Fin 3) ℝ) (U : S → Fin 3 → ℝ), CurvSetting D V J U →
    (∀ δ : ℝ, 0 < δ → ∀ (N : ℕ) (η : ℝ), 0 < N → uN D J N η ≤ δ / 128 →
      ∀ th θ : Fin 3 → ℝ, θ ∈ Cset D V N η th → δ ≤ Gstar D θ → δ / 2 < ellG D J N η th) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ε < 1 →
      ∀ N : ℕ, max 324 (1536 * Kc D J / δ) * Real.log (6 / ε) ≤ N →
        AdmitsG D (gateG D V J N ε (δ / 4)) ∧ MeetsG D V δ ε (gateG D V J N ε (δ / 4))) ∧
    (Kc D J = 0 → ∀ N : ℕ, 0 < N → ∀ (η : ℝ) (θ : Fin 3 → ℝ) (σ : Fin N → S),
      ellG D J N η (thetaHat D (hist D θ σ)) = Gstar D θ)

/-- Part 3: over all designs and laws in the setting with `K ≤ κ`, a common length admitting
law-specific full-history rules must satisfy `N_obs ≥ κ log(1/ε)/(32π² δ)`;
`N_obs ≥ 1536 (κ/δ) log(6/ε)` suffices for the gate; and the class is nonempty with `K = κ`. -/
def ClassRate : Prop :=
  (∀ κ δ ε : ℝ, 0 < κ → κ ≤ 1 / 10000 → 0 < δ → δ ≤ κ / 128 → 0 < ε → ε ≤ 1 / 16 →
    ∀ N : ℕ, 0 < N →
      (∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ))
        (J : Matrix (Fin 3) (Fin 3) ℝ) (U : S → Fin 3 → ℝ), CurvSetting D V J U → Kc D J ≤ κ →
        ∃ ρ : RuleG n N, AdmitsG D ρ ∧ MeetsG D V δ ε ρ) →
      κ / (32 * Real.pi ^ 2 * δ) * Real.log (1 / ε) ≤ N) ∧
  (∀ κ δ ε : ℝ, 0 < δ → δ ≤ κ / 128 → 0 < ε → ε < 1 →
    ∀ N : ℕ, 1536 * (κ / δ) * Real.log (6 / ε) ≤ N →
      ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ))
        (J : Matrix (Fin 3) (Fin 3) ℝ) (U : S → Fin 3 → ℝ), CurvSetting D V J U → Kc D J ≤ κ →
        AdmitsG D (gateG D V J N ε (δ / 4)) ∧ MeetsG D V δ ε (gateG D V J N ε (δ / 4))) ∧
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 10000 →
    ∃ (S : Type) (_ : Fintype S) (D : Data 1 1 2 S) (V : Finset (Fin 3 → ℝ))
      (J : Matrix (Fin 3) (Fin 3) ℝ) (U : S → Fin 3 → ℝ), CurvSetting D V J U ∧ Kc D J = κ

/-- Claim 018, all parts. -/
def statement : Prop := Certificate ∧ Power ∧ ClassRate

end

end Standalone.M4CurvatureCertificate

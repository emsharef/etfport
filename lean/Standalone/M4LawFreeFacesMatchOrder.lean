import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Standalone.M4JointDirectionalRate

/-!
# Claim 021: law-free certification against the two-face ETF comparator

Statement only; the proof is `Novel/M4LawFreeFacesMatchOrderProof.lean`.

The family, the faces `d₀ = (1, 0, 1)` (against cash) and `d₁ = (1, -1, 1)` (against the ETF), the
witness `w_A`, the domain `V4 J`, `SmallJ`, `σ` (`sigma`), `K_J` (`InKJ`) and the rule restriction
`AdmitsJ` are claim 016's; the requirement predicates `falseP`, `powerP` and `Meets` are claim
015's; `Rule`, `prob`, `hist`, `mass`, `thetaHat`, `Adv` and `Gstar` are claim 014's M4 objects.

- `InLJ` is the bounded law class `L(J)`: finite laws with `E U = 0` and `‖U‖ ≤ 9`, with no
  covariance restriction.
- `sbar J d = ‖J'd‖`, `sbarMax = max_j ‖J'd_j‖` and `Rj J d = 9 ‖J'd‖`, so the face errors lie in
  `[-R_j, R_j]`.
- `rangeRule` is the law-free face-by-face range rule. It sees only the public history and uses
  only `J`. The estimate `thHat` is M4's sample mean of `X = (f, r^A - f₁)`, written without
  reference to the law.
-/

namespace Standalone.M4LawFreeFacesMatchOrder

open Matrix MeasureTheory Standalone.M2ScoreAccounting
open Standalone.M4InformationObstruction (Rule Record M4Admissible prob hist mass Adv Gstar)
open Standalone.M4JointDirectionalRate (SmallJ d0 d1 V4 sig2 sigma InKJ data wA etf1 AdmitsJ)
open Standalone.M4BoundedLawRate (falseP powerP Meets)
open scoped Classical

noncomputable section

/-- The bounded law class `L(J)`: `E U = 0`, `‖U‖ ≤ 9`. -/
def InLJ {S : Type} [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧ (∀ i, ∑ s, q s * U s i = 0) ∧ ∀ s, U s ⬝ᵥ U s ≤ 81

/-- `σ̄_d = ‖J'd‖`. -/
def sbar (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) : ℝ :=
  Real.sqrt ((Jᵀ *ᵥ d) ⬝ᵥ (Jᵀ *ᵥ d))

/-- `σ̄ = max_j σ̄_j`. -/
def sbarMax (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := max (sbar J d0) (sbar J d1)

/-- The range `R_d = 9 σ̄_d`. -/
def Rj (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) : ℝ := 9 * sbar J d

/-- `e₂ = (0, 1, 0)`, the premium direction with `d₁ = d₀ - e₂`. -/
def e2 : Fin 3 → ℝ := ![0, 1, 0]

/-- M4's estimate `θ̂_N` for this family, as a function of the public history alone. -/
def thHat {N : ℕ} (H : Fin N → Record 1) : Fin 3 → ℝ :=
  (1 / (N : ℝ)) • ∑ l, ![(H l).f 0, (H l).f 1, (H l).rA - (H l).f 0]

/-- The half-width `r_j = R_j √(3 log(2/η)/N_obs)`. -/
def rj (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) (N : ℕ) (η : ℝ) : ℝ :=
  Rj J d * Real.sqrt (3 * Real.log (2 / η) / N)

/-- The face bound `ℓ_j = d_j'θ̂_N - r_j`. -/
def ellR (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) {N : ℕ} (η : ℝ) (H : Fin N → Record 1) :
    ℝ :=
  d ⬝ᵥ thHat H - rj J d N η

/-- The law-free range rule: certify `w_A` if `min_j ℓ_j > δ_econ`; otherwise the plug-in
ETF-only action (the ETF if `λ̂₂ > 0`, else cash). -/
def rangeRule (J : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ) (η δe : ℝ) : Rule N where
  kernel H := Measure.dirac (if δe < min (ellR J d0 η H) (ellR J d1 η H) then wA
    else if 0 < thHat H 1 then etf1 else 0)
  isProb _ := inferInstance

/-- `P_θ(certify and Adv ≤ δ_econ)` for a general economic margin. -/
def falseAt {S : Type} [Fintype S] (D : Data 1 1 2 S) (δe : ℝ) (θ : Fin 3 → ℝ) {N : ℕ}
    (ρ : Rule N) : ℝ :=
  ∑ σ : Fin N → S, mass D σ *
    (ρ.kernel (hist D θ σ) {w | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δe}).toReal

/-- The setting: every law in `L(J)` gives an admissible M4 instance; `Adv(w_A; ·)` and `G_*` are
the face formulas for every law; each face error is bounded by `R_j`; `K_J ⊆ L(J)`; and
`σ̄_j = σ_j`. -/
def Setting : Prop :=
  (∀ J : Matrix (Fin 3) (Fin 3) ℝ, SmallJ J → ∀ (S : Type) [Fintype S] (q : S → ℝ)
    (U : S → Fin 3 → ℝ), InLJ q U → M4Admissible (data J q U) (V4 J)) ∧
  (∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ)
    (θ : Fin 3 → ℝ), Adv (data J q U) wA θ = min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) ∧
      Gstar (data J q U) θ = max 0 (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ))) ∧
  (∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ),
    InLJ q U → ∀ s, |d0 ⬝ᵥ (J *ᵥ U s)| ≤ Rj J d0 ∧ |d1 ⬝ᵥ (J *ᵥ U s)| ≤ Rj J d1) ∧
  (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U → InLJ q U) ∧
  ∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ), sbar J d = Real.sqrt (sig2 J d)

/-- Part 1: the whole-class infimum over any set is the minimum of the two face infima; a joint
confidence set implies each face bound at the full level; marginal face bounds give by the union
bound a joint set whose certificate is their minimum; the level factor of a `√log(1/level)` family
(with its value `1.23` at `η = 1/20`); and the decomposition through the cash face is never
tighter. -/
def Joint : Prop :=
  (∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ)
    (C : Set (Fin 3 → ℝ)),
    ⨅ θ ∈ C, ((Adv (data J q U) wA θ : ℝ) : EReal)
      = min (⨅ θ ∈ C, ((d0 ⬝ᵥ θ : ℝ) : EReal)) (⨅ θ ∈ C, ((d1 ⬝ᵥ θ : ℝ) : EReal))) ∧
  (∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ),
    (∀ s, 0 ≤ q s) → ∑ s, q s = 1 → ∀ (N : ℕ) (θ : Fin 3 → ℝ) (η : ℝ)
    (CN : (Fin N → Record 1) → Set (Fin 3 → ℝ)),
    1 - η ≤ prob (data J q U) θ N {H | θ ∈ CN H} →
    ∀ d ∈ ({d0, d1} : Set (Fin 3 → ℝ)),
      prob (data J q U) θ N {H | ((d ⬝ᵥ θ : ℝ) : EReal) < ⨅ θ' ∈ CN H, ((d ⬝ᵥ θ' : ℝ) : EReal)}
        ≤ η) ∧
  (∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ),
    (∀ s, 0 ≤ q s) → ∀ (N : ℕ) (θ : Fin 3 → ℝ) (ℓ0 ℓ1 : (Fin N → Record 1) → ℝ) (η0 η1 : ℝ),
    prob (data J q U) θ N {H | d0 ⬝ᵥ θ < ℓ0 H} ≤ η0 →
    prob (data J q U) θ N {H | d1 ⬝ᵥ θ < ℓ1 H} ≤ η1 →
    prob (data J q U) θ N {H | θ ∉ {θ' | ℓ0 H ≤ d0 ⬝ᵥ θ' ∧ ℓ1 H ≤ d1 ⬝ᵥ θ'}} ≤ η0 + η1 ∧
    ∀ H, ⨅ θ' ∈ {θ' | ℓ0 H ≤ d0 ⬝ᵥ θ' ∧ ℓ1 H ≤ d1 ⬝ᵥ θ'}, ((Adv (data J q U) wA θ' : ℝ) : EReal)
      = ((min (ℓ0 H) (ℓ1 H) : ℝ) : EReal)) ∧
  (∀ κ η : ℝ, 0 < κ → 0 < η → η < 1 →
    κ * Real.sqrt (Real.log (1 / (η / 2))) / (κ * Real.sqrt (Real.log (1 / η)))
      = Real.sqrt (1 + Real.log 2 / Real.log (1 / η)) ∧
    (κ * Real.sqrt (Real.log (1 / (η / 2)))) ^ 2 / (κ * Real.sqrt (Real.log (1 / η))) ^ 2
      = 1 + Real.log 2 / Real.log (1 / η)) ∧
  (1.23 < 1 + Real.log 2 / Real.log (1 / (1 / 20)) ∧
    1 + Real.log 2 / Real.log (1 / (1 / 20)) < 1.24) ∧
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, d1 = d0 - e2 ∧ Rj J d1 ≤ Rj J d0 + 9 * sbar J e2

/-- Part 2: for every law in `L(J)`, the range rule stays in claim 016's rule class; its
false-certification probability is at most `η` at every `θ` and every `δ_econ`; and both
requirements hold once `N_obs ≥ max(3, 22 R²/δ²) log(2/ε)`, which is
`N_obs ≥ 1782 (σ̄²/δ²) log(2/ε)` when `σ̄/δ ≥ 1`. -/
def RangeRule : Prop :=
  ∀ (J : Matrix (Fin 3) (Fin 3) ℝ) (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ),
    InLJ q U →
    (∀ (N : ℕ) (η δe : ℝ), AdmitsJ (data J q U) (rangeRule J N η δe)) ∧
    (∀ (N : ℕ) (η δe : ℝ), 0 < N → 0 < η → η < 1 → ∀ θ : Fin 3 → ℝ,
      falseAt (data J q U) δe θ (rangeRule J N η δe) ≤ η) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ε < 1 → ∀ N : ℕ,
      max 3 (22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2) * Real.log (2 / ε) ≤ N →
      Meets (data J q U) (V4 J) δ ε (rangeRule J N ε (δ / 4))) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ε < 1 → 1 ≤ sbarMax J / δ → ∀ N : ℕ,
      1782 * (sbarMax J ^ 2 / δ ^ 2) * Real.log (2 / ε) ≤ N →
      Meets (data J q U) (V4 J) δ ε (rangeRule J N ε (δ / 4)))

/-- Part 3: every single law-free rule in claim 016's rule class that meets both requirements at
every law in `L(J)` needs `N_obs ≥ (1/(16π²)) (σ̄²/δ²) log(1/ε)`; and the range rule meets them
at every law in `L(J)` once `N_obs ≥ 1782 (σ̄²/δ²) log(6/ε)`. -/
def MatchOrder : Prop :=
  (∀ J : Matrix (Fin 3) (Fin 3) ℝ, SmallJ J → ∀ δ ε : ℝ, 0 < δ → δ ≤ sbarMax J / 8 → 0 < ε →
    ε ≤ 1 / 16 → ∀ N : ℕ, 0 < N → ∀ ρ : Rule N,
    (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InLJ q U →
      AdmitsJ (data J q U) ρ ∧ Meets (data J q U) (V4 J) δ ε ρ) →
    1 / (16 * Real.pi ^ 2) * (sbarMax J ^ 2 / δ ^ 2) * Real.log (1 / ε) ≤ N) ∧
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, ∀ δ ε : ℝ, 0 < δ → δ ≤ sbarMax J / 8 → 0 < ε → ε ≤ 1 / 16 →
    ∀ N : ℕ, 1782 * (sbarMax J ^ 2 / δ ^ 2) * Real.log (6 / ε) ≤ N →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InLJ q U →
      AdmitsJ (data J q U) (rangeRule J N ε (δ / 4)) ∧
      Meets (data J q U) (V4 J) δ ε (rangeRule J N ε (δ / 4))

/-- Claim 021, all parts. -/
def statement : Prop := Setting ∧ Joint ∧ RangeRule ∧ MatchOrder

end

end Standalone.M4LawFreeFacesMatchOrder

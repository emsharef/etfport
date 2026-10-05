import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Standalone.M2ActionClasses

/-!
# Claim 028: the soft-target two-stage procedure in M2

Statement only; the proof is `Novel/M2SoftTargetTwoStageProof.lean`.

M2 is claim 003's formalization (`score`, `exposure`, `F`, `tau`, `covariance`, `w0`), with claim
004's setting predicates. The criterion is the score at a parameter `θ`; claim 003 shows
`Q̄₀ = Q₀(·; θ̄)` at the belief mean. Counts are general: `m` active funds, `n` ETFs, `K` factors.
The objects are restated here; nothing rests on claim 027.

- `sigF = Σ_s q_s z^f_s z^f_s'`, `rres`, `crossM` and `resM` (the residual shock and the cross and
  residual second moments), `sqN x = x'Σ_f x`, and `Gf θ b = b'λ - (γ/2) b'Σ_f b`.
- `R0 = {B'w : w ≥ 0, Σ w ≤ 1}`, stage 1's default exposure set.
- `nu θ b* = λ - γ Σ_f b*`, the multiplier vector; `lamHat = γ Σ_f b*`, the target-implied premia.
- `Ssoft θ b* w = a'α - p'c^E - τ(w - w⁻) - (γ/2)[‖b(w) - b*‖²_{Σ_f} + 2 b(w)'C(w) + R(w)]`.
- `Dplus x y` is the right derivative of `t ↦ max(x + t y, 0)` at `0`; `tauD v d` is `τ`'s
  directional derivative `τ'(v; d)`; `SD` is `S`'s directional derivative `S'(w; d)`.

`T_s = Q(w₂)` for a maximizer `w₂` of `S` on `F`, and `J = Q(w_J)` for a joint maximizer `w_J`.
Part 3's slack is `s = -S'(w₂; Δw) + k`.
-/

namespace Standalone.M2SoftTargetTwoStage

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses

noncomputable section

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- Factor shock second moment `Σ_f`. -/
def sigF (D : Data m n K S) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑ s, D.q s * (D.zf s k * D.zf s l)

/-- Residual shock `a'z^A_s + p'z^E_s`. -/
def rres (D : Data m n K S) (w : Inst m n → ℝ) (s : S) : ℝ :=
  active w ⬝ᵥ D.zA s + etf w ⬝ᵥ D.zE s

/-- Cross moment `C(w)`. -/
def crossM (D : Data m n K S) (w : Inst m n → ℝ) : Fin K → ℝ :=
  fun k => ∑ s, D.q s * (D.zf s k * rres D w s)

/-- Residual second moment `R(w)`. -/
def resM (D : Data m n K S) (w : Inst m n → ℝ) : ℝ := ∑ s, D.q s * rres D w s ^ 2

/-- `x'Σ_f x`. -/
def sqN (D : Data m n K S) (x : Fin K → ℝ) : ℝ := x ⬝ᵥ (sigF D *ᵥ x)

/-- Factor objective `G(b) = b'λ - (γ/2) b'Σ_f b`. -/
def Gf (D : Data m n K S) (θ : Params m K) (b : Fin K → ℝ) : ℝ :=
  b ⬝ᵥ θ.lam - D.gamma / 2 * sqN D b

/-- `R₀ = {B'w : w ≥ 0, Σ w ≤ 1}`. -/
def R0 (D : Data m n K S) : Set (Fin K → ℝ) :=
  {b | ∃ w : Inst m n → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ 1 ∧ exposure D w = b}

/-- Stage 1's multiplier vector `ν = ∇G(b*) = λ - γ Σ_f b*`. -/
def nu (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) : Fin K → ℝ :=
  θ.lam - D.gamma • (sigF D *ᵥ bs)

/-- The target-implied parameters: premia `γ Σ_f b*`, the same `α`. -/
def thetaHat (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) : Params m K :=
  ⟨D.gamma • (sigF D *ᵥ bs), θ.alpha⟩

/-- The soft-target objective `S`. -/
def Ssoft (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) (w : Inst m n → ℝ) : ℝ :=
  active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE - tau D (w - w0 D)
    - D.gamma / 2 * (sqN D (exposure D w - bs) + 2 * (exposure D w ⬝ᵥ crossM D w) + resM D w)

/-- Right derivative of `t ↦ max(x + t y, 0)` at `t = 0`. -/
def Dplus (x y : ℝ) : ℝ := if 0 < x then y else if x < 0 then 0 else max y 0

/-- `τ'(v; d)`. -/
def tauD (D : Data m n K S) (v d : Inst m n → ℝ) : ℝ :=
  ∑ i, (D.kplus i * Dplus (v i) (d i) + D.kminus i * Dplus (-v i) (-d i))

/-- `S'(w; d)`: the target-implied linear part, minus `γ w'Σ d`, minus `τ'(w - w⁻; d)`. -/
def SD (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) (w d : Inst m n → ℝ) : ℝ :=
  exposure D d ⬝ᵥ (D.gamma • (sigF D *ᵥ bs)) + active d ⬝ᵥ θ.alpha - etf d ⬝ᵥ D.cE
    - D.gamma * (w ⬝ᵥ (covariance D *ᵥ d)) - tauD D (w - w0 D) d

/-- Model inputs: an initial position, nonnegative rates, masses and `γ`. -/
def Inputs (D : Data m n K S) : Prop :=
  InitialPosition D ∧ RatesNonneg D ∧ (∀ s, 0 ≤ D.q s) ∧ 0 ≤ D.gamma

/-- Setting: `b(F) ⊆ R₀`, `R₀` convex and compact, and stage 1 (on `R₀`), stage 2 and the joint
problem attain their maxima. -/
def Setting : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    exposure D '' F D ⊆ R0 D ∧ Convex ℝ (R0 D) ∧ IsCompact (R0 D) ∧
    (∃ bs ∈ R0 D, IsMaxOn (Gf D θ) (R0 D) bs) ∧
    (∃ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ) ∧
    ∀ bs : Fin K → ℝ, ∃ w₂ ∈ F D, IsMaxOn (Ssoft D θ bs) (F D) w₂

/-- Part 1: `S = Q - ν'b - (γ/2) b*'Σ_f b*`, equivalently the score at the target-implied premia
less a constant; and if `ν = 0`, every stage-2 maximizer is a joint maximizer. -/
def Identification : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ),
    (∀ w, Ssoft D θ bs w = score D w θ - nu D θ bs ⬝ᵥ exposure D w - D.gamma / 2 * sqN D bs) ∧
    (∀ w, Ssoft D θ bs w = score D w (thetaHat D θ bs) - D.gamma / 2 * sqN D bs) ∧
    ∀ A : Set (Inst m n → ℝ), nu D θ bs = 0 → ∀ w₂ ∈ A, IsMaxOn (Ssoft D θ bs) A w₂ →
      IsMaxOn (fun w => score D w θ) A w₂

/-- Part 2: for any holding set `A` (no convexity), maximizers `w_J` of the score and `w₂` of `S`
on `A`: `0 ≤ Λ_s ≤ ν'Δe`, with equality iff `w_J` also maximizes `S`; for a convex `R ⊇ b(A)`
and a maximizer `b*` of `G` on `R`, `ν'Δe ≤ ν'(b* - b₂)`, so `Λ_s = 0` when `Δe = 0` or
`b₂ = b*`; and `Λ_s ≤ |ν| |Δe|` (Euclidean). -/
def MultiplierBound : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ (A : Set (Inst m n → ℝ)) (bs : Fin K → ℝ) (wJ w₂ : Inst m n → ℝ),
      wJ ∈ A → IsMaxOn (fun w => score D w θ) A wJ → w₂ ∈ A → IsMaxOn (Ssoft D θ bs) A w₂ →
      0 ≤ score D wJ θ - score D w₂ θ ∧
      score D wJ θ - score D w₂ θ ≤ nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂) ∧
      (score D wJ θ - score D w₂ θ = nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂) ↔
        IsMaxOn (Ssoft D θ bs) A wJ) ∧
      score D wJ θ - score D w₂ θ
        ≤ Real.sqrt (∑ k, nu D θ bs k ^ 2)
          * Real.sqrt (∑ k, (exposure D wJ - exposure D w₂) k ^ 2) ∧
      (exposure D wJ = exposure D w₂ → score D wJ θ = score D w₂ θ) ∧
      ∀ R : Set (Fin K → ℝ), Convex ℝ R → exposure D '' A ⊆ R → bs ∈ R → IsMaxOn (Gf D θ) R bs →
        nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂) ≤ nu D θ bs ⬝ᵥ (bs - exposure D w₂) ∧
        (exposure D w₂ = bs → score D wJ θ = score D w₂ θ)

/-- Part 3: on the convex `F`, with `Δw = w_J - w₂`, the directional derivatives `S'(w₂; Δw)` and
`τ'(w₂ - w⁻; Δw)` exist (as right derivatives along the segment), `S'(w₂; Δw) ≤ 0`, the kink
term `k = τ(w_J - w⁻) - τ(w₂ - w⁻) - τ'(w₂ - w⁻; Δw)` is nonnegative and zero when no trade
changes sign, and `Λ_s = ν'Δe - (γ/2) Δw'ΣΔw - s` with `s = -S'(w₂; Δw) + k ≥ 0`. -/
def ExactForm : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ (bs : Fin K → ℝ) (wJ w₂ : Inst m n → ℝ),
      wJ ∈ F D → IsMaxOn (fun w => score D w θ) (F D) wJ → w₂ ∈ F D → IsMaxOn (Ssoft D θ bs) (F D) w₂ →
      HasDerivWithinAt (fun t : ℝ => tau D (w₂ - w0 D + t • (wJ - w₂)))
        (tauD D (w₂ - w0 D) (wJ - w₂)) (Set.Ici 0) 0 ∧
      HasDerivWithinAt (fun t : ℝ => Ssoft D θ bs (w₂ + t • (wJ - w₂)))
        (SD D θ bs w₂ (wJ - w₂)) (Set.Ici 0) 0 ∧
      SD D θ bs w₂ (wJ - w₂) ≤ 0 ∧
      0 ≤ tau D (wJ - w0 D) - tau D (w₂ - w0 D) - tauD D (w₂ - w0 D) (wJ - w₂) ∧
      ((∀ i, 0 ≤ (w₂ - w0 D) i * (wJ - w0 D) i) →
        tau D (wJ - w0 D) - tau D (w₂ - w0 D) - tauD D (w₂ - w0 D) (wJ - w₂) = 0) ∧
      score D wJ θ - score D w₂ θ
        = nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂)
          - D.gamma / 2 * ((wJ - w₂) ⬝ᵥ (covariance D *ᵥ (wJ - w₂)))
          - (-SD D θ bs w₂ (wJ - w₂)
            + (tau D (wJ - w0 D) - tau D (w₂ - w0 D) - tauD D (w₂ - w0 D) (wJ - w₂))) ∧
      score D wJ θ - score D w₂ θ
        ≤ nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂)
          - D.gamma / 2 * ((wJ - w₂) ⬝ᵥ (covariance D *ᵥ (wJ - w₂)))

/-- Part 4: any holding `w_T ∈ F` with exposure `b*` gives `T_s ≥ Q(w_T) - ν'(b* - b₂)`, hence
`Λ_s ≤ (J - Q(w_T)) + ν'(b* - b₂)`. -/
def FibreRelation : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ)
    (wJ w₂ wT : Inst m n → ℝ), w₂ ∈ F D → IsMaxOn (Ssoft D θ bs) (F D) w₂ → wT ∈ F D →
    exposure D wT = bs →
      score D wT θ - nu D θ bs ⬝ᵥ (bs - exposure D w₂) ≤ score D w₂ θ ∧
      score D wJ θ - score D w₂ θ
        ≤ (score D wJ θ - score D wT θ) + nu D θ bs ⬝ᵥ (bs - exposure D w₂)

/-- Part 5: `ν = λ - λ̂` lies in the normal cone of `R` at `b*` for any convex `R` on which `b*`
maximizes `G`, and `ν = 0` when `b*` is interior to `R`. -/
def Multiplier : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ (R : Set (Fin K → ℝ)) (bs : Fin K → ℝ), Convex ℝ R → bs ∈ R → IsMaxOn (Gf D θ) R bs →
      nu D θ bs = θ.lam - (thetaHat D θ bs).lam ∧
      (∀ b ∈ R, nu D θ bs ⬝ᵥ (b - bs) ≤ 0) ∧
      (bs ∈ interior R → nu D θ bs = 0)

/-- Claim 028, parts 1-5 with the setting. -/
def statement : Prop :=
  Setting ∧ Identification ∧ MultiplierBound ∧ ExactForm ∧ FibreRelation ∧ Multiplier

end

end Standalone.M2SoftTargetTwoStage

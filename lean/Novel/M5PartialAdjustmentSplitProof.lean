import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Standalone.M5PartialAdjustmentSplit

/-!
# Proof of claim 030

No other claim's proof module is used (`depends_on: []`), and AX-10 is not used: the
finite-horizon policy is verified directly.

* **One Bellman step.** With `b = Λ xm + (G + ρC')m + ρc' - e`, the objective is
  `-(1/2) x'Dx + x'b + k` with `k` free of `x`. So `F(x̂) - F(x) = (1/2)(x - x̂)'D(x - x̂)` at
  `x̂ = D⁻¹b`, which is positive for `x ≠ x̂` since `D = Λ + S + ρA'` is positive definite. The value
  `(1/2) b'D⁻¹b + k` expands, with `D⁻¹` symmetric, into the Riccati form.
* **The recursion.** Backward induction keeps `0 ⪯ A_t ⪯ Λ`: with `y = D⁻¹Λx`,
  `x'(Λ - ΛD⁻¹Λ)x = (x - y)'Λ(x - y) + y'(γΣ + ρA')y`. The conditional expectation of `J_{t+1}`
  is `J_{t+1}` at the current mean plus `E_t q_{t+1}`, by linearity and the martingale property.
* **Γ_t.** With `R = D_t^{1/2}` (from the spectral theorem), `Γ_t = D_t⁻¹(γΣ_t + ρA_{t+1})` is
  `R⁻¹ M R` with `M = R⁻¹(γΣ_t + ρA_{t+1})R⁻¹ ≻ 0` and `I - M = R⁻¹ΛR⁻¹ ⪰ 0`.
* **The aim.** `A_s aim_s = C_s m + c_s` by backward induction, which turns the first-order
  condition into partial adjustment; the weights telescope to `I`.
-/

namespace Novel.M5PartialAdjustmentSplitProof

open Matrix Standalone.M5PartialAdjustmentSplit

set_option linter.unusedSectionVars false

noncomputable section

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π]

/-! ### Symmetric matrices -/

/-- A symmetric matrix moves across the dot product. -/
lemma sym_dot {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (x y : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

lemma move_left {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (y w : ι → ℝ) :
    (M *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (M *ᵥ w) := by
  rw [dotProduct_comm, sym_dot hM]

lemma transpose_of_psd {M : Matrix ι ι ℝ} (hM : M.PosSemidef) : Mᵀ = M := by
  have := hM.isHermitian.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma herm_of {M : Matrix ι ι ℝ} (h : Mᵀ = M) : M.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, h]

lemma psd_of {M : Matrix ι ι ℝ} (h : Mᵀ = M) (hq : ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x)) :
    M.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (herm_of h) fun x => by simpa using hq x

lemma inv_sym {D : Matrix ι ι ℝ} (hD : Dᵀ = D) : (D⁻¹)ᵀ = D⁻¹ := by
  rw [transpose_nonsing_inv, hD]

lemma pd_unit {D : Matrix ι ι ℝ} (hD : D.PosDef) : IsUnit D.det :=
  (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit

/-! ### One Bellman step -/

/-- The Bellman objective at one review, as a function of the post-trade position `x`, with the
expected continuation `-(1/2) x'A'x + x'(C'm + c') + κ`. -/
def bellObj (Λ S A' : Matrix ι ι ℝ) (G C' : Matrix ι π ℝ)
    (c' e : ι → ℝ) (ρ κ : ℝ) (xm : ι → ℝ) (m : π → ℝ) (x : ι → ℝ) : ℝ :=
  -(1 / 2) * ((x - xm) ⬝ᵥ (Λ *ᵥ (x - xm))) + x ⬝ᵥ (G *ᵥ m - e) - (1 / 2) * (x ⬝ᵥ (S *ᵥ x)) +
    ρ * (-(1 / 2) * (x ⬝ᵥ (A' *ᵥ x)) + x ⬝ᵥ (C' *ᵥ m + c') + κ)

lemma bellObj_eq (Λ S A' : Matrix ι ι ℝ) (hΛ : Λᵀ = Λ) (G C' : Matrix ι π ℝ)
    (c' e : ι → ℝ) (ρ κ : ℝ) (xm : ι → ℝ) (m : π → ℝ) (x : ι → ℝ) :
    bellObj Λ S A' G C' c' e ρ κ xm m x =
      -(1 / 2) * (x ⬝ᵥ ((Λ + S + ρ • A') *ᵥ x)) +
        x ⬝ᵥ (Λ *ᵥ xm + ((G + ρ • C') *ᵥ m + (ρ • c' - e))) +
        (-(1 / 2) * (xm ⬝ᵥ (Λ *ᵥ xm)) + ρ * κ) := by
  unfold bellObj
  have h := sym_dot hΛ x xm
  simp only [add_mulVec, smul_mulVec, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_add,
    dotProduct_smul, smul_eq_mul] at h ⊢
  rw [h]
  ring

/-- Completing the square for a symmetric `D` with `D x̂ = b`. -/
lemma quad_gap {D : Matrix ι ι ℝ} (hD : Dᵀ = D) {b xs : ι → ℝ} (hxs : D *ᵥ xs = b)
    (x : ι → ℝ) :
    (-(1 / 2) * (xs ⬝ᵥ (D *ᵥ xs)) + xs ⬝ᵥ b) - (-(1 / 2) * (x ⬝ᵥ (D *ᵥ x)) + x ⬝ᵥ b) =
      (1 / 2) * ((x - xs) ⬝ᵥ (D *ᵥ (x - xs))) := by
  have h := sym_dot hD x xs
  rw [← hxs]
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [h]
  ring

/-- One Bellman step: the unique affine maximizer and the quadratic value. -/
theorem bellmanStep (Λ S A' : Matrix ι ι ℝ) (G C' : Matrix ι π ℝ)
    (c' e : ι → ℝ) (ρ κ : ℝ) (m : π → ℝ)
    (hΛ : Λ.PosSemidef) (hS : S.PosDef) (hA : A'.PosSemidef) (hρ : 0 ≤ ρ) :
    let D := Λ + S + ρ • A'
    let v := (G + ρ • C') *ᵥ m + (ρ • c' - e)
    (∀ xm x, x ≠ (D⁻¹ * Λ) *ᵥ xm + (D⁻¹ * (G + ρ • C')) *ᵥ m + D⁻¹ *ᵥ (ρ • c' - e) →
      bellObj Λ S A' G C' c' e ρ κ xm m x < bellObj Λ S A' G C' c' e ρ κ xm m
        ((D⁻¹ * Λ) *ᵥ xm + (D⁻¹ * (G + ρ • C')) *ᵥ m + D⁻¹ *ᵥ (ρ • c' - e))) ∧
    ∀ xm, bellObj Λ S A' G C' c' e ρ κ xm m
        ((D⁻¹ * Λ) *ᵥ xm + (D⁻¹ * (G + ρ • C')) *ᵥ m + D⁻¹ *ᵥ (ρ • c' - e)) =
      -(1 / 2) * (xm ⬝ᵥ ((Λ - Λ * D⁻¹ * Λ) *ᵥ xm)) +
        xm ⬝ᵥ ((Λ * D⁻¹ * (G + ρ • C')) *ᵥ m + (Λ * D⁻¹) *ᵥ (ρ • c' - e)) +
        ((1 / 2) * ((D⁻¹ *ᵥ v) ⬝ᵥ v) + ρ * κ) := by
  intro D v
  have hDpd : D.PosDef := (Matrix.PosDef.posSemidef_add hΛ hS).add_posSemidef (hA.smul hρ)
  have hDsym : Dᵀ = D := transpose_of_psd hDpd.posSemidef
  have hΛsym : Λᵀ = Λ := transpose_of_psd hΛ
  have hDinv : D * D⁻¹ = 1 := mul_nonsing_inv D (pd_unit hDpd)
  have hinvsym : (D⁻¹)ᵀ = D⁻¹ := inv_sym hDsym
  have hv : v = (G + ρ • C') *ᵥ m + (ρ • c' - e) := rfl
  clear_value v
  have hxs : ∀ xm, (D⁻¹ * Λ) *ᵥ xm + (D⁻¹ * (G + ρ • C')) *ᵥ m + D⁻¹ *ᵥ (ρ • c' - e) =
      D⁻¹ *ᵥ (Λ *ᵥ xm + v) := fun xm => by
    rw [hv, mulVec_add, mulVec_add, mulVec_mulVec, mulVec_mulVec, add_assoc]
  have hDxs : ∀ xm, D *ᵥ (D⁻¹ *ᵥ (Λ *ᵥ xm + v)) = Λ *ᵥ xm + v := fun xm => by
    rw [mulVec_mulVec, hDinv, one_mulVec]
  refine ⟨fun xm x hx => ?_, fun xm => ?_⟩
  · rw [hxs] at hx ⊢
    rw [bellObj_eq Λ S A' hΛsym, bellObj_eq Λ S A' hΛsym, ← hv]
    have hgap := quad_gap hDsym (hDxs xm) x
    have hpos := hDpd.dotProduct_mulVec_pos (sub_ne_zero.mpr hx)
    simp only [star_trivial] at hpos
    linarith
  · rw [hxs, bellObj_eq Λ S A' hΛsym, ← hv]
    set xs := D⁻¹ *ᵥ (Λ *ᵥ xm + v)
    have h1 : xs ⬝ᵥ (D *ᵥ xs) = xs ⬝ᵥ (Λ *ᵥ xm + v) := by rw [hDxs]
    rw [h1]
    have e1 : xs = D⁻¹ *ᵥ (Λ *ᵥ xm) + D⁻¹ *ᵥ v := by simp only [xs, mulVec_add]
    have a1 : (D⁻¹ *ᵥ (Λ *ᵥ xm)) ⬝ᵥ (Λ *ᵥ xm) = xm ⬝ᵥ ((Λ * D⁻¹ * Λ) *ᵥ xm) := by
      rw [move_left hinvsym, move_left hΛsym, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have a2 : (D⁻¹ *ᵥ (Λ *ᵥ xm)) ⬝ᵥ v = xm ⬝ᵥ ((Λ * D⁻¹) *ᵥ v) := by
      rw [move_left hinvsym, move_left hΛsym, mulVec_mulVec]
    have a3 : (D⁻¹ *ᵥ v) ⬝ᵥ (Λ *ᵥ xm) = xm ⬝ᵥ ((Λ * D⁻¹) *ᵥ v) := by
      rw [sym_dot hΛsym, mulVec_mulVec]
    have f1 : xs ⬝ᵥ (Λ *ᵥ xm + v) = xm ⬝ᵥ ((Λ * D⁻¹ * Λ) *ᵥ xm) + 2 * (xm ⬝ᵥ ((Λ * D⁻¹) *ᵥ v)) +
        (D⁻¹ *ᵥ v) ⬝ᵥ v := by
      rw [e1, add_dotProduct, dotProduct_add, dotProduct_add, a1, a2, a3]; ring
    have f2 : (Λ * D⁻¹ * (G + ρ • C')) *ᵥ m + (Λ * D⁻¹) *ᵥ (ρ • c' - e) = (Λ * D⁻¹) *ᵥ v := by
      rw [hv, mulVec_add, ← mulVec_mulVec]
    have f3 : xm ⬝ᵥ ((Λ - Λ * D⁻¹ * Λ) *ᵥ xm) = xm ⬝ᵥ (Λ *ᵥ xm) - xm ⬝ᵥ ((Λ * D⁻¹ * Λ) *ᵥ xm) := by
      rw [sub_mulVec, dotProduct_sub]
    rw [f1, f2, f3]
    ring

/-! ### The Riccati map keeps `0 ⪯ A ⪯ Λ` -/

lemma ric_psd {Λ E' : Matrix ι ι ℝ} (hΛ : Λ.PosSemidef) (hE : E'.PosDef) :
    (Λ - Λ * (Λ + E')⁻¹ * Λ).PosSemidef ∧ (Λ * (Λ + E')⁻¹ * Λ).PosSemidef := by
  set D := Λ + E'
  have hD : D.PosDef := Matrix.PosDef.posSemidef_add hΛ hE
  have hDsym : Dᵀ = D := transpose_of_psd hD.posSemidef
  have hΛsym : Λᵀ = Λ := transpose_of_psd hΛ
  have hinvsym := inv_sym hDsym
  have hDinv : D * D⁻¹ = 1 := mul_nonsing_inv D (pd_unit hD)
  have hsym2 : (Λ * D⁻¹ * Λ)ᵀ = Λ * D⁻¹ * Λ := by
    rw [transpose_mul, transpose_mul, hΛsym, hinvsym, Matrix.mul_assoc]
  have hq2 : ∀ x, x ⬝ᵥ ((Λ * D⁻¹ * Λ) *ᵥ x) = (Λ *ᵥ x) ⬝ᵥ (D⁻¹ *ᵥ (Λ *ᵥ x)) := fun x => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← move_left hΛsym]
  refine ⟨psd_of (by rw [transpose_sub, hΛsym, hsym2]) fun x => ?_,
    psd_of hsym2 fun x => by
      rw [hq2]
      simpa using hD.inv.posSemidef.dotProduct_mulVec_nonneg (Λ *ᵥ x)⟩
  set y := D⁻¹ *ᵥ (Λ *ᵥ x)
  have hDy : D *ᵥ y = Λ *ᵥ x := by
    simp only [y, mulVec_mulVec, ← Matrix.mul_assoc, hDinv, Matrix.one_mul]
  have h1 := hΛ.dotProduct_mulVec_nonneg (x - y)
  have h2 := hE.posSemidef.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at h1 h2
  have hyD : y ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ (Λ *ᵥ y) + y ⬝ᵥ (E' *ᵥ y) := by
    simp only [D, add_mulVec, dotProduct_add]
  rw [hDy] at hyD
  have hxy := sym_dot hΛsym x y
  rw [sub_mulVec, dotProduct_sub, hq2]
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h1
  have hyx : (Λ *ᵥ x) ⬝ᵥ y = y ⬝ᵥ (Λ *ᵥ x) := dotProduct_comm _ _
  rw [hyx]
  linarith

/-! ### The recursion -/

namespace LQ

variable (Q : LQ ι π)

lemma A_ge {t : ℕ} (ht : Q.T ≤ t) : Q.A t = 0 := by
  simp [LQ.A, Nat.sub_eq_zero_of_le ht, LQ.ricK]

lemma C_ge {t : ℕ} (ht : Q.T ≤ t) : Q.C t = 0 := by
  simp [LQ.C, Nat.sub_eq_zero_of_le ht, LQ.ricK]

lemma c_ge {t : ℕ} (ht : Q.T ≤ t) : Q.c t = 0 := by
  simp [LQ.c, Nat.sub_eq_zero_of_le ht, LQ.ricK]

lemma aim_ge {t : ℕ} (ht : Q.T ≤ t) (m : π → ℝ) : Q.aim t m = 0 := by
  simp [LQ.aim, Nat.sub_eq_zero_of_le ht, LQ.aimK]

lemma ric_lt {t : ℕ} (ht : t < Q.T) :
    Q.A t = Q.Lam - Q.Lam * (Q.D t)⁻¹ * Q.Lam ∧
    Q.C t = Q.Lam * (Q.D t)⁻¹ * (Q.G t + Q.rho • Q.C (t + 1)) ∧
    Q.c t = (Q.Lam * (Q.D t)⁻¹) *ᵥ (Q.rho • Q.c (t + 1) - Q.e) := by
  have h1 : Q.T - t = (Q.T - (t + 1)) + 1 := by omega
  have h2 : Q.T - (Q.T - (t + 1) + 1) = t := by omega
  simp only [LQ.A, LQ.C, LQ.c, LQ.D, h1, LQ.ricK, h2, and_self]

lemma aim_lt {t : ℕ} (ht : t < Q.T) (m : π → ℝ) :
    Q.aim t m = (Q.S t + Q.rho • Q.A (t + 1))⁻¹ *ᵥ
      (Q.S t *ᵥ Q.mkw t m + Q.rho • (Q.A (t + 1) *ᵥ Q.aim (t + 1) m)) := by
  have h1 : Q.T - t = (Q.T - (t + 1)) + 1 := by omega
  have h2 : Q.T - (Q.T - (t + 1) + 1) = t := by omega
  simp only [LQ.aim, h1, LQ.aimK, h2]

variable {Q}

lemma E_pd (hS : Q.Setting) {t : ℕ} (hA : (Q.A (t + 1)).PosSemidef) :
    (Q.S t + Q.rho • Q.A (t + 1)).PosDef :=
  (hS.2.1 t).add_posSemidef (hA.smul hS.2.2)

lemma D_split (t : ℕ) : Q.D t = Q.Lam + (Q.S t + Q.rho • Q.A (t + 1)) := by
  simp only [LQ.D, add_assoc]

/-- Backward induction: `0 ⪯ A_t ⪯ Λ` at every review. -/
lemma A_bounds (hS : Q.Setting) : ∀ t, (Q.A t).PosSemidef ∧ (Q.Lam - Q.A t).PosSemidef := by
  suffices h : ∀ k t, Q.T - t = k → (Q.A t).PosSemidef ∧ (Q.Lam - Q.A t).PosSemidef from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [LQ.A_ge Q (by omega), sub_zero]
    exact ⟨PosSemidef.zero, hS.1⟩
  | succ k ih =>
    intro t ht
    have htT : t < Q.T := by omega
    have hE := E_pd hS (ih (t + 1) (by omega)).1
    obtain ⟨hA, -, -⟩ := LQ.ric_lt Q htT
    rw [hA, D_split]
    obtain ⟨h1, h2⟩ := ric_psd hS.1 hE
    refine ⟨h1, ?_⟩
    rwa [sub_sub_cancel]

lemma D_pd (hS : Q.Setting) (t : ℕ) : (Q.D t).PosDef := by
  rw [D_split]
  exact Matrix.PosDef.posSemidef_add hS.1 (E_pd hS (A_bounds hS (t + 1)).1)

end LQ

/-! ### Part 3: verification -/

/-- `q_t`, with `k` reviews left. -/
def qK (Q : LQ ι π) (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) :
    ℕ → (π → ℝ) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun m =>
    let t := Q.T - (k + 1)
    let v := (Q.G t + Q.rho • Q.C (t + 1)) *ᵥ m + (Q.rho • Q.c (t + 1) - Q.e)
    (1 / 2) * (((Q.D t)⁻¹ *ᵥ v) ⬝ᵥ v) + Q.rho * E t (qK Q E k) m

/-- `q_t`. -/
def qq (Q : LQ ι π) (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) (t : ℕ) :
    (π → ℝ) → ℝ := qK Q E (Q.T - t)

lemma qq_ge (Q : LQ ι π) (E) {t : ℕ} (ht : Q.T ≤ t) (m : π → ℝ) : qq Q E t m = 0 := by
  simp [qq, Nat.sub_eq_zero_of_le ht, qK]

lemma qq_lt (Q : LQ ι π) (E) {t : ℕ} (ht : t < Q.T) (m : π → ℝ) :
    qq Q E t m = (1 / 2) * (((Q.D t)⁻¹ *ᵥ ((Q.G t + Q.rho • Q.C (t + 1)) *ᵥ m +
      (Q.rho • Q.c (t + 1) - Q.e))) ⬝ᵥ ((Q.G t + Q.rho • Q.C (t + 1)) *ᵥ m +
      (Q.rho • Q.c (t + 1) - Q.e))) + Q.rho * E t (qq Q E (t + 1)) m := by
  have h1 : Q.T - t = (Q.T - (t + 1)) + 1 := by omega
  have h2 : Q.T - (Q.T - (t + 1) + 1) = t := by omega
  simp only [qq, h1, qK, h2]

/-- The expected continuation, by linearity and the martingale property. -/
lemma exp_J (Q : LQ ι π) {E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)} (hE : Martingale E)
    (q : ℕ → (π → ℝ) → ℝ) (t : ℕ) (x : ι → ℝ) (m : π → ℝ) :
    E t (fun m' => Q.J q (t + 1) x m') m =
      -(1 / 2) * (x ⬝ᵥ (Q.A (t + 1) *ᵥ x)) + x ⬝ᵥ (Q.C (t + 1) *ᵥ m + Q.c (t + 1)) +
        E t (q (t + 1)) m := by
  set a := -(1 / 2) * (x ⬝ᵥ (Q.A (t + 1) *ᵥ x)) + x ⬝ᵥ Q.c (t + 1)
  set w := x ᵥ* Q.C (t + 1)
  have hf : (fun m' => Q.J q (t + 1) x m') =
      (fun _ => a) + (∑ i, w i • (fun m' : π → ℝ => m' i)) + q (t + 1) := by
    funext m'
    simp only [LQ.J, a, w, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      dotProduct_add, dotProduct_mulVec]
    simp only [dotProduct]
    ring
  rw [hf, map_add, map_add, map_sum]
  simp only [map_smul, hE.1, hE.2, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [dotProduct_add, dotProduct_mulVec x (Q.C (t + 1)) m]
  simp only [a, w, dotProduct]
  ring

theorem bellmanVerif : BellmanVerif := by
  intro ι π _ _ _ Q hS E hE
  refine ⟨qq Q E, fun m => qq_ge Q E le_rfl m, fun t ht xm m => ?_⟩
  have hA := (LQ.A_bounds hS (t + 1)).1
  have hobj : ∀ x, Q.obj E (qq Q E) t xm m x =
      bellObj Q.Lam (Q.S t) (Q.A (t + 1)) (Q.G t) (Q.C (t + 1)) (Q.c (t + 1)) Q.e Q.rho
        (E t (qq Q E (t + 1)) m) xm m x := fun x => by
    rw [LQ.obj, exp_J Q hE, bellObj]
  have hpol : Q.policy t xm m = ((Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ * Q.Lam) *ᵥ xm +
      ((Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ * (Q.G t + Q.rho • Q.C (t + 1))) *ᵥ m +
      (Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ *ᵥ (Q.rho • Q.c (t + 1) - Q.e) := rfl
  obtain ⟨h1, h2⟩ := bellmanStep Q.Lam (Q.S t) (Q.A (t + 1)) (Q.G t) (Q.C (t + 1)) (Q.c (t + 1)) Q.e
    Q.rho (E t (qq Q E (t + 1)) m) m hS.1 (hS.2.1 t) hA hS.2.2
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hobj, hobj, hpol]
    exact h1 xm x (by rw [← hpol]; exact hx)
  · rw [hobj, hpol, h2 xm]
    obtain ⟨eA, eC, ec⟩ := LQ.ric_lt Q ht
    rw [LQ.J, eA, eC, ec, qq_lt Q E ht]
    rfl

/-! ### Part 3: the matrices -/

/-- A positive definite matrix has a symmetric invertible square root. -/
lemma sqrt_exists {D : Matrix ι ι ℝ} (hD : D.PosDef) :
    ∃ R : Matrix ι ι ℝ, Rᵀ = R ∧ R * R = D ∧ IsUnit R := by
  set U : Matrix ι ι ℝ := (hD.1.eigenvectorUnitary : Matrix ι ι ℝ)
  set ev := hD.1.eigenvalues
  have hspec := hD.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hev : ∀ i, 0 < ev i := hD.eigenvalues_pos
  set R := U * diagonal (fun i => Real.sqrt (ev i)) * star U
  set R' := U * diagonal (fun i => (Real.sqrt (ev i))⁻¹) * star U
  have hmul : ∀ f g : ι → ℝ, (U * diagonal f * star U) * (U * diagonal g * star U) =
      U * diagonal (fun i => f i * g i) * star U := fun f g => by
    calc (U * diagonal f * star U) * (U * diagonal g * star U)
        = U * diagonal f * (star U * U) * diagonal g * star U := by simp only [Matrix.mul_assoc]
      _ = U * (diagonal f * diagonal g) * star U := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc U (diagonal f)]
      _ = U * diagonal (fun i => f i * g i) * star U := by rw [diagonal_mul_diagonal]
  refine ⟨R, ?_, ?_, ?_⟩
  · simp only [R, hstar, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  · have hf : (fun i => Real.sqrt (ev i) * Real.sqrt (ev i)) = RCLike.ofReal ∘ ev :=
      funext fun i => by simp [Real.mul_self_sqrt (hev i).le]
    rw [hmul, hf]
    exact hspec.symm
  · have h1 : R * R' = 1 := by
      rw [hmul]
      have : (fun i => Real.sqrt (ev i) * (Real.sqrt (ev i))⁻¹) = fun _ => 1 := funext fun i =>
        mul_inv_cancel₀ (Real.sqrt_pos.mpr (hev i)).ne'
      rw [this, diagonal_one, Matrix.mul_one, hUU']
    have h2 : R' * R = 1 := by
      rw [hmul]
      have : (fun i => (Real.sqrt (ev i))⁻¹ * Real.sqrt (ev i)) = fun _ => 1 := funext fun i =>
        inv_mul_cancel₀ (Real.sqrt_pos.mpr (hev i)).ne'
      rw [this, diagonal_one, Matrix.mul_one, hUU']
    exact ⟨⟨R, R', h1, h2⟩, rfl⟩

theorem matrices : Matrices := by
  intro ι π _ _ _ Q hS t ht
  have hD := LQ.D_pd hS t
  have hAb := LQ.A_bounds hS t
  have hA1 := (LQ.A_bounds hS (t + 1)).1
  have hE := LQ.E_pd hS hA1
  set E' := Q.S t + Q.rho • Q.A (t + 1)
  have hDE : Q.D t = Q.Lam + E' := LQ.D_split t
  have hdet := pd_unit hD
  have hDinv : (Q.D t)⁻¹ * Q.D t = 1 := nonsing_inv_mul _ hdet
  have hGam : Q.Gam t = (Q.D t)⁻¹ * E' := by
    have : E' = Q.D t - Q.Lam := by rw [hDE]; abel
    rw [this, Matrix.mul_sub, hDinv]
    rfl
  refine ⟨hD, hAb.1, hAb.2, hGam, ?_, fun v => ?_, fun hL => ?_⟩
  · obtain ⟨R, hRsym, hRR, hRu⟩ := sqrt_exists hD
    have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRu
    have hRi : R⁻¹ * R = 1 := nonsing_inv_mul R hRdet
    have hRi' : R * R⁻¹ = 1 := mul_nonsing_inv R hRdet
    have hRisym : (R⁻¹)ᴴ = R⁻¹ := by
      rw [conjTranspose_eq_transpose_of_trivial, inv_sym hRsym]
    have hinj : Function.Injective (R⁻¹).mulVec := by
      intro a b hab
      have := congrArg (R *ᵥ ·) hab
      simpa only [mulVec_mulVec, hRi', one_mulVec] using this
    have e : 1 - R⁻¹ * E' * R⁻¹ = R⁻¹ * Q.Lam * R⁻¹ := by
      have h1 : (1 : Matrix ι ι ℝ) = R⁻¹ * Q.D t * R⁻¹ := by
        rw [← hRR, ← Matrix.mul_assoc, hRi, Matrix.one_mul, hRi']
      rw [h1, hDE, Matrix.mul_add, Matrix.add_mul]
      abel
    refine ⟨R, R⁻¹ * E' * R⁻¹, hRu, ?_, ?_, ?_, ?_⟩
    · rw [hGam, ← hRR, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    · have := hE.conjTranspose_mul_mul_same hinj
      rwa [hRisym] at this
    · rw [e]
      have := hS.1.conjTranspose_mul_mul_same R⁻¹
      rwa [hRisym] at this
    · intro hLpd
      rw [e]
      have := hLpd.conjTranspose_mul_mul_same hinj
      rwa [hRisym] at this
  · have hG : Q.Gam t *ᵥ v = v - (Q.D t)⁻¹ *ᵥ (Q.Lam *ᵥ v) := by
      simp only [LQ.Gam, sub_mulVec, one_mulVec, mulVec_mulVec]
    rw [hG, sub_eq_self]
    constructor
    · intro h
      have := congrArg (Q.D t *ᵥ ·) h
      simp only [mulVec_mulVec, mulVec_zero] at this
      rwa [← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul] at this
    · intro h; rw [h, mulVec_zero]
  · have hLdet : IsUnit Q.Lam.det := (Matrix.isUnit_iff_isUnit_det _).mp hL
    obtain ⟨eA, -, -⟩ := LQ.ric_lt Q ht
    rw [eA, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hLdet,
      Matrix.one_mul]
    rfl

/-! ### Part 3: the aim -/

/-- `A_s aim_s = C_s m + c_s`, by backward induction. -/
lemma A_aim {Q : LQ ι π} (hS : Q.Setting) (m : π → ℝ) :
    ∀ s, Q.A s *ᵥ Q.aim s m = Q.C s *ᵥ m + Q.c s := by
  suffices h : ∀ k s, Q.T - s = k → Q.A s *ᵥ Q.aim s m = Q.C s *ᵥ m + Q.c s from
    fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [LQ.A_ge Q (by omega), LQ.C_ge Q (by omega), LQ.c_ge Q (by omega)]
    simp
  | succ k ih =>
    intro s hs
    have hsT : s < Q.T := by omega
    have hih := ih (s + 1) (by omega)
    have hE := LQ.E_pd hS (LQ.A_bounds hS (s + 1)).1
    set E' := Q.S s + Q.rho • Q.A (s + 1)
    have hEdet := pd_unit hE
    obtain ⟨eA, eC, ec⟩ := LQ.ric_lt Q hsT
    have hDE : Q.D s = Q.Lam + E' := LQ.D_split s
    have hDdet := pd_unit (LQ.D_pd hS s)
    have hA' : Q.A s = Q.Lam * (Q.D s)⁻¹ * E' := by
      rw [eA]
      have : E' = Q.D s - Q.Lam := by rw [hDE]; abel
      rw [this, Matrix.mul_sub, Matrix.mul_assoc Q.Lam _ (Q.D s), nonsing_inv_mul _ hDdet,
        Matrix.mul_one]
    have hSm : Q.S s *ᵥ Q.mkw s m = Q.G s *ᵥ m - Q.e := by
      simp only [LQ.mkw, mulVec_mulVec, mul_nonsing_inv _ (pd_unit (hS.2.1 s)), one_mulVec]
    have hc : ∀ w, (Q.Lam * (Q.D s)⁻¹ * E') *ᵥ (E'⁻¹ *ᵥ w) = (Q.Lam * (Q.D s)⁻¹) *ᵥ w := fun w => by
      rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hEdet, Matrix.mul_one]
    rw [hA', LQ.aim_lt Q hsT, hc, hSm, hih, eC, ec, ← mulVec_mulVec m (Q.Lam * (Q.D s)⁻¹),
      ← mulVec_add]
    congr 1
    simp only [add_mulVec, smul_mulVec, smul_add]
    abel

/-- The weights sum to `I`. -/
lemma W_sum {Q : LQ ι π} (hS : Q.Setting) :
    ∀ t, t < Q.T → ∑ d ∈ Finset.range (Q.T - t), Q.W d t = 1 := by
  suffices h : ∀ k t, Q.T - t = k + 1 → ∑ d ∈ Finset.range (Q.T - t), Q.W d t = 1 from
    fun t ht => h (Q.T - t - 1) t (by omega)
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [ht, Finset.sum_range_one]
    simp only [LQ.W]
    rw [LQ.A_ge Q (by omega), smul_zero, add_zero]
    exact nonsing_inv_mul _ (pd_unit (hS.2.1 t))
  | succ k ih =>
    intro t ht
    have hE := LQ.E_pd hS (LQ.A_bounds hS (t + 1)).1
    have hEdet := pd_unit hE
    have htail := ih (t + 1) (by omega)
    rw [show Q.T - (t + 1) = k + 1 by omega] at htail
    rw [ht, Finset.sum_range_succ']
    simp only [LQ.W]
    rw [← Finset.mul_sum, htail, Matrix.mul_one, add_comm, ← Matrix.mul_add]
    exact nonsing_inv_mul _ hEdet

/-- The aim as a weighted sum of the future Markowitz portfolios at the current mean. -/
lemma aim_sum {Q : LQ ι π} (m : π → ℝ) :
    ∀ t, Q.aim t m = ∑ d ∈ Finset.range (Q.T - t), Q.W d t *ᵥ Q.mkw (t + d) m := by
  suffices h : ∀ k t, Q.T - t = k →
      Q.aim t m = ∑ d ∈ Finset.range (Q.T - t), Q.W d t *ᵥ Q.mkw (t + d) m from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [LQ.aim_ge Q (by omega), ht, Finset.sum_range_zero]
  | succ k ih =>
    intro t ht
    have htT : t < Q.T := by omega
    have hih := ih (t + 1) (by omega)
    rw [LQ.aim_lt Q htT, hih, ht, Finset.sum_range_succ', show Q.T - (t + 1) = k by omega]
    set E' := Q.S t + Q.rho • Q.A (t + 1)
    have h1 : ∀ d, Q.W (d + 1) t *ᵥ Q.mkw (t + (d + 1)) m =
        (E'⁻¹ * (Q.rho • Q.A (t + 1))) *ᵥ (Q.W d (t + 1) *ᵥ Q.mkw (t + 1 + d) m) := fun d => by
      rw [show t + (d + 1) = t + 1 + d by omega]
      simp only [LQ.W, mulVec_mulVec, E']
    simp only [h1]
    rw [← mulVec_sum, add_zero]
    simp only [LQ.W, E', mulVec_add, ← mulVec_mulVec, smul_mulVec, mulVec_smul]
    abel

theorem aimThm : Aim := by
  intro ι π _ _ _ Q hS t ht
  have hE := LQ.E_pd hS (LQ.A_bounds hS (t + 1)).1
  set E' := Q.S t + Q.rho • Q.A (t + 1)
  have hEdet := pd_unit hE
  have hDdet := pd_unit (LQ.D_pd hS t)
  have hDE : Q.D t = Q.Lam + E' := LQ.D_split t
  refine ⟨fun xm m => ?_, fun m => ?_, ?_, fun m => ?_⟩
  · have hGam : Q.Gam t = (Q.D t)⁻¹ * E' := by
      have : E' = Q.D t - Q.Lam := by rw [hDE]; abel
      rw [this, Matrix.mul_sub, nonsing_inv_mul _ hDdet]
      rfl
    have hEaim : E' *ᵥ Q.aim t m = (Q.G t + Q.rho • Q.C (t + 1)) *ᵥ m +
        (Q.rho • Q.c (t + 1) - Q.e) := by
      rw [LQ.aim_lt Q ht, mulVec_mulVec, mul_nonsing_inv _ hEdet, one_mulVec, A_aim hS m]
      simp only [LQ.mkw, mulVec_mulVec, mul_nonsing_inv _ (pd_unit (hS.2.1 t)), one_mulVec,
        add_mulVec, smul_mulVec, smul_add]
      abel
    have hid : Q.Gam t = 1 - (Q.D t)⁻¹ * Q.Lam := rfl
    calc Q.policy t xm m
        = ((Q.D t)⁻¹ * Q.Lam) *ᵥ xm + (Q.D t)⁻¹ *ᵥ (E' *ᵥ Q.aim t m) := by
          rw [hEaim]
          simp only [LQ.policy, LQ.K, LQ.L, LQ.l, ← mulVec_mulVec, mulVec_add, add_assoc]
      _ = xm + Q.Gam t *ᵥ (Q.aim t m - xm) := by
          rw [mulVec_mulVec, ← hGam, hid]
          simp only [sub_mulVec, one_mulVec, mulVec_sub]
          abel
  · have hT : Q.T - 1 < Q.T := by omega
    rw [LQ.aim_lt Q hT, show Q.T - 1 + 1 = Q.T by omega, LQ.A_ge Q le_rfl]
    simp only [zero_mulVec, smul_zero, add_zero]
    simp only [LQ.mkw, mulVec_mulVec, mul_nonsing_inv _ (pd_unit (hS.2.1 _)), Matrix.mul_one]
  · rw [Fin.sum_univ_eq_sum_range (fun d => Q.W d t)]
    exact W_sum hS t ht
  · rw [aim_sum m t, Fin.sum_univ_eq_sum_range (fun d => Q.W d t *ᵥ Q.mkw (t + d) m)]


/-! ### Part 5: the scalar fund block -/

lemma inv_scal {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix ι ι ℝ))⁻¹ = c⁻¹ • 1 :=
  Matrix.inv_eq_left_inv (by rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ hc, one_smul])

lemma pvar_pos {s2 sig2 : ℝ} (hs : 0 < s2) (hg : 0 < sig2) (t : ℕ) : 0 < pvar s2 sig2 t := by
  unfold pvar; positivity

lemma pvar_succ {s2 sig2 : ℝ} (hs : 0 < s2) (hg : 0 < sig2) (t : ℕ) :
    pvar s2 sig2 (t + 1) = pvar s2 sig2 t - pvar s2 sig2 t * (pvar s2 sig2 t + sig2)⁻¹ * pvar s2 sig2 t := by
  have hp := pvar_pos hs hg t
  have h1 : pvar s2 sig2 t - pvar s2 sig2 t * (pvar s2 sig2 t + sig2)⁻¹ * pvar s2 sig2 t =
      pvar s2 sig2 t * sig2 / (pvar s2 sig2 t + sig2) := by
    field_simp; ring
  rw [h1]
  unfold pvar
  push_cast
  field_simp
  ring

lemma pvar_anti {s2 sig2 : ℝ} (hs : 0 < s2) (hg : 0 < sig2) {t u : ℕ} (htu : t ≤ u) :
    pvar s2 sig2 u ≤ pvar s2 sig2 t := by
  unfold pvar
  apply one_div_le_one_div_of_le (by positivity)
  have : (t : ℝ) ≤ u := by exact_mod_cast htu
  have := div_le_div_of_nonneg_right this hg.le
  linarith

lemma pvar_le {s2 sig2 : ℝ} (hs : 0 < s2) (hg : 0 < sig2) {t : ℕ} (ht : 0 < t) :
    pvar s2 sig2 t ≤ sig2 / t := by
  unfold pvar
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have h : (t : ℝ) / sig2 ≤ 1 / s2 + t / sig2 := by have : 0 < 1 / s2 := by positivity
                                                    linarith
  calc 1 / (1 / s2 + t / sig2) ≤ 1 / (t / sig2) := one_div_le_one_div_of_le (by positivity) h
    _ = sig2 / t := one_div_div _ _

lemma gseq_ge (lam gam sig2 s2 rho : ℝ) {T t : ℕ} (ht : T ≤ t) : gseq lam gam sig2 s2 rho T t = 0 := by
  simp [gseq, Nat.sub_eq_zero_of_le ht, gK]

lemma gseq_lt (lam gam sig2 s2 rho : ℝ) {T t : ℕ} (ht : t < T) :
    gseq lam gam sig2 s2 rho T t = 1 - 1 / (1 + gam * (sig2 + pvar s2 sig2 t) / lam +
      rho * gseq lam gam sig2 s2 rho T (t + 1)) := by
  have h1 : T - t = (T - (t + 1)) + 1 := by omega
  have h2 : T - (T - (t + 1) + 1) = t := by omega
  simp only [gseq, h1, gK, h2]

lemma gseq_bounds {lam gam sig2 s2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hs : 0 < s2) (hr : 0 ≤ rho) (T : ℕ) :
    ∀ t, 0 ≤ gseq lam gam sig2 s2 rho T t ∧ (t < T → 0 < gseq lam gam sig2 s2 rho T t ∧
      gseq lam gam sig2 s2 rho T t < 1) := by
  suffices h : ∀ k t, T - t = k → 0 ≤ gseq lam gam sig2 s2 rho T t ∧
      (t < T → 0 < gseq lam gam sig2 s2 rho T t ∧ gseq lam gam sig2 s2 rho T t < 1) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [gseq_ge _ _ _ _ _ (by omega)]
    exact ⟨le_rfl, fun h => by omega⟩
  | succ k ih =>
    intro t ht
    have htT : t < T := by omega
    have h0 := (ih (t + 1) (by omega)).1
    have hp := pvar_pos hs hg t
    have hu : 0 < gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) := by
      have : 0 < gam * (sig2 + pvar s2 sig2 t) / lam := by positivity
      nlinarith [mul_nonneg hr h0]
    rw [gseq_lt _ _ _ _ _ htT]
    set u := gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1)
    have e : 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) =
        1 + u := by simp only [u]; ring
    rw [e]
    have h1 : 1 / (1 + u) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h2 : 0 < 1 / (1 + u) := by positivity
    refine ⟨by linarith, fun _ => ⟨by linarith, by linarith⟩⟩

/-- Strict monotonicity in `γ/λ_A`. -/
lemma gseq_mono {lam₁ gam₁ lam₂ gam₂ sig2 s2 rho : ℝ} (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂)
    (hg₁ : 0 < gam₁) (hg₂ : 0 < gam₂) (hg : 0 < sig2) (hs : 0 < s2) (hr : 0 ≤ rho)
    (hk : gam₁ / lam₁ < gam₂ / lam₂) (T : ℕ) :
    ∀ t, gseq lam₁ gam₁ sig2 s2 rho T t ≤ gseq lam₂ gam₂ sig2 s2 rho T t ∧
      (t < T → gseq lam₁ gam₁ sig2 s2 rho T t < gseq lam₂ gam₂ sig2 s2 rho T t) := by
  suffices h : ∀ k t, T - t = k → gseq lam₁ gam₁ sig2 s2 rho T t ≤ gseq lam₂ gam₂ sig2 s2 rho T t ∧
      (t < T → gseq lam₁ gam₁ sig2 s2 rho T t < gseq lam₂ gam₂ sig2 s2 rho T t) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [gseq_ge _ _ _ _ _ (by omega), gseq_ge _ _ _ _ _ (by omega)]
    exact ⟨le_rfl, fun h => by omega⟩
  | succ k ih =>
    intro t ht
    have htT : t < T := by omega
    have hih := (ih (t + 1) (by omega)).1
    have hp := pvar_pos hs hg t
    have b₁ := (gseq_bounds hl₁ hg₁ hg hs hr T (t + 1)).1
    have b₂ := (gseq_bounds hl₂ hg₂ hg hs hr T (t + 1)).1
    rw [gseq_lt _ _ _ _ _ htT, gseq_lt _ _ _ _ _ htT]
    have e₁ : gam₁ * (sig2 + pvar s2 sig2 t) / lam₁ = gam₁ / lam₁ * (sig2 + pvar s2 sig2 t) := by ring
    have e₂ : gam₂ * (sig2 + pvar s2 sig2 t) / lam₂ = gam₂ / lam₂ * (sig2 + pvar s2 sig2 t) := by ring
    rw [e₁, e₂]
    have hlt : gam₁ / lam₁ * (sig2 + pvar s2 sig2 t) < gam₂ / lam₂ * (sig2 + pvar s2 sig2 t) :=
      mul_lt_mul_of_pos_right hk (by linarith)
    have hk₁ : 0 < gam₁ / lam₁ := by positivity
    have hA : 0 < 1 + gam₁ / lam₁ * (sig2 + pvar s2 sig2 t) + rho * gseq lam₁ gam₁ sig2 s2 rho T (t + 1) := by
      nlinarith [mul_nonneg hr b₁, mul_pos hk₁ (by linarith : (0 : ℝ) < sig2 + pvar s2 sig2 t)]
    have hB : 1 + gam₁ / lam₁ * (sig2 + pvar s2 sig2 t) + rho * gseq lam₁ gam₁ sig2 s2 rho T (t + 1) <
        1 + gam₂ / lam₂ * (sig2 + pvar s2 sig2 t) + rho * gseq lam₂ gam₂ sig2 s2 rho T (t + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hih hr]
    have : 1 / (1 + gam₂ / lam₂ * (sig2 + pvar s2 sig2 t) + rho * gseq lam₂ gam₂ sig2 s2 rho T (t + 1)) <
        1 / (1 + gam₁ / lam₁ * (sig2 + pvar s2 sig2 t) + rho * gseq lam₁ gam₁ sig2 s2 rho T (t + 1)) :=
      one_div_lt_one_div_of_lt hA hB
    exact ⟨by linarith, fun _ => by linarith⟩

/-- The scalar Riccati map on the fund block. -/
lemma fund_scalar {N : ℕ} {π : Type} [Fintype π] {Q : LQ (Fin N) π} {lam gam sig2 s2 : ℝ} (hl : 0 < lam) (hgm : 0 < gam)
    (hg : 0 < sig2) (hs : 0 < s2) (hr : 0 ≤ Q.rho) (hL : Q.Lam = lam • 1)
    (hS : ∀ t, Q.S t = (gam * (sig2 + pvar s2 sig2 t)) • 1) :
    ∀ t, Q.A t = (lam * gseq lam gam sig2 s2 Q.rho Q.T t) • 1 ∧
      (t < Q.T → Q.Gam t = gseq lam gam sig2 s2 Q.rho Q.T t • 1) := by
  suffices h : ∀ k t, Q.T - t = k → Q.A t = (lam * gseq lam gam sig2 s2 Q.rho Q.T t) • 1 ∧
      (t < Q.T → Q.Gam t = gseq lam gam sig2 s2 Q.rho Q.T t • 1) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [LQ.A_ge Q (by omega), gseq_ge _ _ _ _ _ (by omega), mul_zero, zero_smul]
    exact ⟨rfl, fun h => by omega⟩
  | succ k ih =>
    intro t ht
    have htT : t < Q.T := by omega
    have hA1 := (ih (t + 1) (by omega)).1
    set g' := gseq lam gam sig2 s2 Q.rho Q.T (t + 1)
    have hg' := (gseq_bounds hl hgm hg hs hr Q.T (t + 1)).1
    have hp := pvar_pos hs hg t
    set d := lam + gam * (sig2 + pvar s2 sig2 t) + Q.rho * (lam * g')
    have hd : 0 < d := by
      have : 0 ≤ Q.rho * (lam * g') := mul_nonneg hr (mul_nonneg hl.le hg')
      have : 0 < gam * (sig2 + pvar s2 sig2 t) := by positivity
      simp only [d]; linarith
    have hD : Q.D t = d • 1 := by
      simp only [LQ.D, hL, hS, hA1, smul_smul, ← add_smul, d]
    have hDi : (Q.D t)⁻¹ = d⁻¹ • 1 := by rw [hD, inv_scal hd.ne']
    have hgt : gseq lam gam sig2 s2 Q.rho Q.T t = 1 - lam / d := by
      rw [gseq_lt _ _ _ _ _ htT]
      have e : 1 + gam * (sig2 + pvar s2 sig2 t) / lam + Q.rho * g' = d / lam := by
        simp only [d]; field_simp
      rw [e, one_div_div]
    obtain ⟨eA, -, -⟩ := LQ.ric_lt Q htT
    refine ⟨?_, fun _ => ?_⟩
    · rw [eA, hDi, hL, hgt]
      simp only [smul_mul_smul_comm, Matrix.one_mul, ← sub_smul]
      congr 1
      field_simp
    · show 1 - (Q.D t)⁻¹ * Q.Lam = _
      rw [hDi, hL, hgt, smul_mul_smul_comm, Matrix.one_mul, ← one_smul ℝ (1 : Matrix (Fin N) (Fin N) ℝ),
        smul_smul, ← sub_smul, one_smul]
      congr 1
      field_simp

/-- The closed form of the stationary rate for `ρ > 0`, in `g = a/λ_A` terms, with `c = γσ²/λ_A`. -/
def gcl (lam gam sig2 rho : ℝ) : ℝ :=
  let c := gam * sig2 / lam
  (-(1 + c - rho) + Real.sqrt ((1 + c - rho) ^ 2 + 4 * rho * c)) / (2 * rho)

/-- For `ρ ∈ (0, 1]` the closed form is a nonnegative fixed point; it matches
`garleanu2009dynamic`'s rate, and `a_∞ = λ_A` times it. -/
lemma gcl_facts {lam gam sig2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    0 ≤ gcl lam gam sig2 rho ∧
    gcl lam gam sig2 rho = 1 - 1 / (1 + gam * sig2 / lam + rho * gcl lam gam sig2 rho) ∧
    gcl lam gam sig2 rho = aGP (gam / rho) (lam / sig2) (1 - rho) / (lam / sig2) ∧
    astar lam gam sig2 rho = lam * gcl lam gam sig2 rho := by
  set c := gam * sig2 / lam with hc
  have hc0 : 0 < c := by positivity
  set b := 1 + c - rho
  have hb : 0 < b := by simp only [b]; linarith
  set Δ := b ^ 2 + 4 * rho * c
  have hΔ : 0 ≤ Δ := by positivity
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hsb : b ≤ Real.sqrt Δ := by
    rw [show b = Real.sqrt (b ^ 2) from (Real.sqrt_sq hb.le).symm]
    exact Real.sqrt_le_sqrt (by simp only [Δ]; nlinarith)
  have hgs : gcl lam gam sig2 rho = (-b + Real.sqrt Δ) / (2 * rho) := rfl
  have h0 : 0 ≤ gcl lam gam sig2 rho := by rw [hgs]; apply div_nonneg <;> linarith
  have hquad : rho * gcl lam gam sig2 rho ^ 2 + b * gcl lam gam sig2 rho - c = 0 := by
    rw [hgs]; field_simp; nlinarith [hsq]
  refine ⟨h0, ?_, ?_, ?_⟩
  · set g := gcl lam gam sig2 rho
    have hpos : 0 < 1 + c + rho * g := by nlinarith [mul_nonneg hr.le h0]
    have e : 1 / (1 + c + rho * g) = 1 - g := by
      rw [div_eq_iff hpos.ne']
      simp only [b] at hquad
      linear_combination hquad
    linarith
  · set k := lam / sig2 with hk
    have hk0 : 0 < k := by positivity
    have hck : gam = c * k := by simp only [c, k]; field_simp
    unfold aGP
    have e1 : gam / rho * (1 - (1 - rho)) + k * (1 - rho) = k * b := by
      rw [hck]; simp only [b]; field_simp; ring
    have e2 : 4 * (gam / rho) * k * (1 - (1 - rho)) ^ 2 = k ^ 2 * (4 * rho * c) := by
      rw [hck]; field_simp; ring
    rw [e1, e2, show (k * b) ^ 2 + k ^ 2 * (4 * rho * c) = k ^ 2 * Δ by simp only [Δ]; ring,
      Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk0.le, hgs, show 1 - (1 - rho) = rho by ring]
    field_simp
  · have hcl : gam * sig2 = c * lam := by simp only [c]; field_simp
    unfold astar
    rw [ite_eq_right hr.ne', hgs, hcl]
    have e1 : c * lam + (1 - rho) * lam = lam * b := by simp only [b]; ring
    have e2 : (c * lam + (1 - rho) * lam) ^ 2 + 4 * rho * (c * lam) * lam = lam ^ 2 * Δ := by
      simp only [Δ, b]; ring
    rw [e2, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hl.le, e1]
    field_simp

/-- `g_∞ = a_∞/λ_A` is a fixed point in `(0, 1)`, for every `ρ ∈ [0, 1]`. -/
lemma gs_fix {lam gam sig2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1) :
    0 < astar lam gam sig2 rho / lam ∧ astar lam gam sig2 rho / lam < 1 ∧
    astar lam gam sig2 rho / lam =
      1 - 1 / (1 + gam * sig2 / lam + rho * (astar lam gam sig2 rho / lam)) := by
  have hc0 : 0 < gam * sig2 / lam := by positivity
  have hfix : astar lam gam sig2 rho / lam =
      1 - 1 / (1 + gam * sig2 / lam + rho * (astar lam gam sig2 rho / lam)) ∧
      0 ≤ astar lam gam sig2 rho / lam := by
    rcases eq_or_lt_of_le hr with h0 | h0
    · subst h0
      have : astar lam gam sig2 0 / lam = (gam * sig2 / lam) / (1 + gam * sig2 / lam) := by
        unfold astar; rw [ite_eq_left rfl]; field_simp
      rw [this]
      refine ⟨?_, by positivity⟩
      field_simp
      ring
    · obtain ⟨g0, gfix, -, hast⟩ := gcl_facts hl hgm hg h0 hr1
      rw [hast, mul_div_cancel_left₀ _ hl.ne']
      exact ⟨gfix, g0⟩
  obtain ⟨hf, h0⟩ := hfix
  set g := astar lam gam sig2 rho / lam
  have hpos : 0 < 1 + gam * sig2 / lam + rho * g := by nlinarith [mul_nonneg hr h0]
  have hlt : 1 < 1 + gam * sig2 / lam + rho * g := by nlinarith [mul_nonneg hr h0]
  refine ⟨?_, ?_, hf⟩
  · rw [hf]
    have : 1 / (1 + gam * sig2 / lam + rho * g) < 1 := by rw [div_lt_one hpos]; exact hlt
    linarith
  · rw [hf]; have := one_div_pos.mpr hpos; linarith

/-- The contraction bound `|g_t - g_∞| ≤ q^{T-t} + κ p_t/(m²(1-q))` with `m = 1 + γσ²/λ_A` and
`q = ρ/m² < 1`, for `ρ ∈ [0, 1]`. -/
lemma gseq_close {lam gam sig2 s2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hs : 0 < s2) (hr : 0 ≤ rho) (hr1 : rho ≤ 1) (T : ℕ) :
    let m := 1 + gam * sig2 / lam
    let q := rho / m ^ 2
    ∀ t, t ≤ T → |gseq lam gam sig2 s2 rho T t - astar lam gam sig2 rho / lam| ≤
      q ^ (T - t) + gam / lam * pvar s2 sig2 t / (m ^ 2 * (1 - q)) := by
  intro m q
  obtain ⟨hg0, hg1, hfix⟩ := gs_fix hl hgm hg hr hr1
  set g := astar lam gam sig2 rho / lam
  have hm : 1 < m := by have : 0 < gam * sig2 / lam := by positivity
                        simp only [m]; linarith
  have hm2 : 1 < m ^ 2 := by nlinarith
  have hq0 : 0 ≤ q := div_nonneg hr (by positivity)
  have hq1 : q < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h1q : 0 < 1 - q := by linarith
  set κ := gam / lam
  have hκ : 0 < κ := by positivity
  suffices h : ∀ k t, T - t = k → t ≤ T → |gseq lam gam sig2 s2 rho T t - g| ≤
      q ^ (T - t) + κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht htT
    have htT' : t = T := by omega
    subst htT'
    rw [gseq_ge _ _ _ _ _ le_rfl, Nat.sub_self, pow_zero, zero_sub, abs_neg, abs_of_nonneg hg0.le]
    have : 0 ≤ κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) := by
      have := pvar_pos hs hg t
      positivity
    linarith
  | succ k ih =>
    intro t ht htT
    have hlt : t < T := by omega
    have hih := ih (t + 1) (by omega) (by omega)
    have hb := (gseq_bounds hl hgm hg hs hr T (t + 1)).1
    have hp := pvar_pos hs hg t
    have hp' := pvar_anti hs hg (Nat.le_succ t)
    set g' := gseq lam gam sig2 s2 rho T (t + 1)
    set a := 1 + gam * sig2 / lam + rho * g
    set b := 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * g'
    have hma : m ≤ a := by simp only [a, m]; nlinarith [mul_nonneg hr hg0.le]
    have hmb : m ≤ b := by
      have : gam * sig2 / lam ≤ gam * (sig2 + pvar s2 sig2 t) / lam := by
        apply div_le_div_of_nonneg_right _ hl.le; nlinarith
      simp only [b, m]; nlinarith [mul_nonneg hr hb]
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hdiff : gseq lam gam sig2 s2 rho T t - g = (b - a) / (a * b) := by
      have hgt : gseq lam gam sig2 s2 rho T t = 1 - 1 / b := gseq_lt _ _ _ _ _ hlt
      have hga : g = 1 - 1 / a := hfix
      rw [hgt, hga]
      field_simp
      ring
    have hba : b - a = κ * pvar s2 sig2 t + rho * (g' - g) := by
      simp only [a, b, κ]; field_simp; ring
    have hab : m ^ 2 ≤ a * b := by nlinarith
    have habs : |gseq lam gam sig2 s2 rho T t - g| ≤ κ * pvar s2 sig2 t / m ^ 2 + q * |g' - g| := by
      rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < a * b), hba]
      calc |κ * pvar s2 sig2 t + rho * (g' - g)| / (a * b)
          ≤ |κ * pvar s2 sig2 t + rho * (g' - g)| / m ^ 2 :=
            div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hab
        _ ≤ (κ * pvar s2 sig2 t + rho * |g' - g|) / m ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            calc |κ * pvar s2 sig2 t + rho * (g' - g)| ≤ |κ * pvar s2 sig2 t| + |rho * (g' - g)| :=
                  abs_add_le _ _
              _ = κ * pvar s2 sig2 t + rho * |g' - g| := by
                  rw [abs_of_pos (by positivity), abs_mul, abs_of_nonneg hr]
        _ = κ * pvar s2 sig2 t / m ^ 2 + q * |g' - g| := by simp only [q]; ring
    have hpow : q ^ (T - t) = q * q ^ (T - (t + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hE : κ * pvar s2 sig2 (t + 1) / (m ^ 2 * (1 - q)) ≤ κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp' hκ.le) (by positivity)
    have hkey : κ * pvar s2 sig2 t / m ^ 2 + q * (κ * pvar s2 sig2 t / (m ^ 2 * (1 - q))) =
        κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) := by
      field_simp; ring
    have hih' : |g' - g| ≤ q ^ (T - (t + 1)) + κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) := by
      linarith
    calc |gseq lam gam sig2 s2 rho T t - g|
        ≤ κ * pvar s2 sig2 t / m ^ 2 + q * |g' - g| := habs
      _ ≤ κ * pvar s2 sig2 t / m ^ 2 + q * (q ^ (T - (t + 1)) + κ * pvar s2 sig2 t / (m ^ 2 * (1 - q))) := by
          have := mul_le_mul_of_nonneg_left hih' hq0
          linarith
      _ = q ^ (T - t) + κ * pvar s2 sig2 t / (m ^ 2 * (1 - q)) := by rw [hpow]; linarith [hkey]

/-- A longer horizon raises every trading rate. -/
lemma gseq_monoT {lam gam sig2 s2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hs : 0 < s2) (hr : 0 ≤ rho) (T : ℕ) :
    ∀ t, gseq lam gam sig2 s2 rho T t ≤ gseq lam gam sig2 s2 rho (T + 1) t := by
  suffices h : ∀ k t, T - t = k → gseq lam gam sig2 s2 rho T t ≤ gseq lam gam sig2 s2 rho (T + 1) t from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [gseq_ge _ _ _ _ _ (by omega : T ≤ t)]
    exact (gseq_bounds hl hgm hg hs hr (T + 1) t).1
  | succ k ih =>
    intro t ht
    have htT : t < T := by omega
    have hih := ih (t + 1) (by omega)
    have hb := (gseq_bounds hl hgm hg hs hr T (t + 1)).1
    have hp := pvar_pos hs hg t
    rw [gseq_lt _ _ _ _ _ htT, gseq_lt _ _ _ _ _ (by omega : t < T + 1)]
    have hA : 0 < 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) := by
      have : 0 < gam * (sig2 + pvar s2 sig2 t) / lam := by positivity
      nlinarith [mul_nonneg hr hb]
    have hB : 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) ≤
        1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho (T + 1) (t + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hih hr]
    have := one_div_le_one_div_of_le hA hB
    linarith

/-- The stationary limit, in the claim's order: `T → ∞` at fixed `t`, then `t → ∞`. -/
lemma stationary {lam gam sig2 s2 rho : ℝ} (hl : 0 < lam) (hgm : 0 < gam) (hg : 0 < sig2)
    (hs : 0 < s2) (hr : 0 ≤ rho) (hr1 : rho ≤ 1) :
    ∃ ainf : ℕ → ℝ,
      (∀ t, Filter.Tendsto (fun T => lam * gseq lam gam sig2 s2 rho T t) Filter.atTop
        (nhds (ainf t))) ∧
      Filter.Tendsto ainf Filter.atTop (nhds (astar lam gam sig2 rho)) := by
  set m := 1 + gam * sig2 / lam
  set q := rho / m ^ 2
  set g := astar lam gam sig2 rho / lam
  set κ := gam / lam
  have hm : 1 < m := by have : 0 < gam * sig2 / lam := by positivity
                        simp only [m]; linarith
  have hq0 : 0 ≤ q := div_nonneg hr (by positivity)
  have hq1 : q < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have h1q : 0 < 1 - q := by linarith
  -- the limit in `T` exists: monotone and bounded
  have hmono : ∀ t, Monotone (fun T => gseq lam gam sig2 s2 rho T t) :=
    fun t => monotone_nat_of_le_succ fun T => gseq_monoT hl hgm hg hs hr T t
  have hbdd : ∀ t, BddAbove (Set.range (fun T => gseq lam gam sig2 s2 rho T t)) := by
    intro t
    refine ⟨1, ?_⟩
    rintro _ ⟨T, rfl⟩
    rcases lt_or_ge t T with h | h
    · exact ((gseq_bounds hl hgm hg hs hr T t).2 h).2.le
    · show gseq lam gam sig2 s2 rho T t ≤ 1
      rw [gseq_ge _ _ _ _ _ h]; norm_num
  set gl : ℕ → ℝ := fun t => ⨆ T, gseq lam gam sig2 s2 rho T t
  have hlimT : ∀ t, Filter.Tendsto (fun T => gseq lam gam sig2 s2 rho T t) Filter.atTop (nhds (gl t)) :=
    fun t => tendsto_atTop_ciSup (hmono t) (hbdd t)
  -- the error bound survives `T → ∞`
  set E : ℕ → ℝ := fun t => κ * pvar s2 sig2 t / (m ^ 2 * (1 - q))
  have hclose : ∀ t, |gl t - g| ≤ E t := by
    intro t
    have hq : Filter.Tendsto (fun T : ℕ => q ^ (T - t) + E t) Filter.atTop (nhds (0 + E t)) := by
      refine Filter.Tendsto.add_const _ ?_
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (Filter.tendsto_sub_atTop_nat t)
    rw [zero_add] at hq
    refine le_of_tendsto_of_tendsto ((hlimT t).sub_const g).abs hq ?_
    filter_upwards [Filter.eventually_ge_atTop t] with T hT
    exact gseq_close hl hgm hg hs hr hr1 T t hT
  have hE0 : Filter.Tendsto E Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun t : ℕ => pvar s2 sig2 t) Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat sig2) ?_ ?_
      · exact Filter.Eventually.of_forall fun t => (pvar_pos hs hg t).le
      · filter_upwards [Filter.eventually_gt_atTop 0] with t ht
        exact pvar_le hs hg ht
    have := (hp.const_mul κ).div_const (m ^ 2 * (1 - q))
    simpa [E, mul_zero, zero_div] using this
  have hgl : Filter.Tendsto gl Filter.atTop (nhds g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hE0
    rw [Real.norm_eq_abs]
    exact hclose t
  refine ⟨fun t => lam * gl t, fun t => (hlimT t).const_mul lam, ?_⟩
  have := hgl.const_mul lam
  rwa [show lam * g = astar lam gam sig2 rho by simp only [g]; field_simp] at this

theorem speeds : Speeds := by
  refine ⟨fun N s2 sig2 hs hg t => ?_, fun N π _ Q lam gam sig2 s2 hl hgm hg hs hr hL hS t ht => ?_,
    fun lam gam sig2 s2 rho T t hl hgm hg hs hr ht => (gseq_bounds hl hgm hg hs hr T t).2 ht,
    fun lam₁ lam₂ gam sig2 s2 rho T t hl₁ hl hgm hg hs hr ht => ?_,
    fun lam gam₁ gam₂ sig2 s2 rho T t hl hg₁ hgg hg hs hr ht => ?_,
    fun lam gam sig2 s2 rho hl hgm hg hs hr hr1 => ?_,
    fun lam gam sig2 rho hl hgm hg hr hr1 => ?_⟩
  · induction t with
    | zero => simp [kal, pvar]
    | succ t ih =>
      have hp := pvar_pos hs hg t
      simp only [kal, ih, transpose_one, Matrix.mul_one, Matrix.one_mul]
      rw [← add_smul, inv_scal (by linarith : pvar s2 sig2 t + sig2 ≠ 0), smul_mul_smul_comm,
        Matrix.one_mul, smul_mul_smul_comm, Matrix.one_mul, ← sub_smul, pvar_succ hs hg t]
  · obtain ⟨h1, h2⟩ := fund_scalar hl hgm hg hs hr hL hS t
    exact ⟨h1, h2 ht⟩
  · have hk : gam / lam₂ < gam / lam₁ := div_lt_div_of_pos_left hgm hl₁ hl
    exact (gseq_mono (by linarith) hl₁ hgm hgm hg hs hr hk T t).2 ht
  · have hk : gam₁ / lam < gam₂ / lam := div_lt_div_of_pos_right hgg hl
    exact (gseq_mono hl hl hg₁ (by linarith) hg hs hr hk T t).2 ht
  · obtain ⟨hg0, hg1, hfix⟩ := gs_fix hl hgm hg hr hr1
    set a := astar lam gam sig2 rho
    have ha : a = lam * (a / lam) := by field_simp
    have hafix : a = lam - lam ^ 2 / (lam + gam * sig2 + rho * a) := by
      have hpos : 0 < 1 + gam * sig2 / lam + rho * (a / lam) := by
        have : 0 < gam * sig2 / lam := by positivity
        nlinarith [mul_nonneg hr hg0.le]
      have e : lam + gam * sig2 + rho * a = lam * (1 + gam * sig2 / lam + rho * (a / lam)) := by
        field_simp
      rw [e]
      conv_lhs => rw [ha, hfix]
      field_simp
    refine ⟨⟨by nlinarith [mul_pos hl hg0], by nlinarith [mul_lt_mul_of_pos_left hg1 hl], hafix,
      fun b hb0 hbl hbfix => ?_⟩, hg0, hg1, stationary hl hgm hg hs hr hr1⟩
    -- uniqueness: the map `b ↦ λ - λ²/(λ + γσ² + ρb)` is a contraction on `[0, λ]`
    have hden : ∀ x, 0 ≤ x → lam + gam * sig2 ≤ lam + gam * sig2 + rho * x := fun x hx => by
      nlinarith [mul_nonneg hr hx]
    have hc : 0 < gam * sig2 := by positivity
    have hA : 0 < lam + gam * sig2 + rho * a := by nlinarith [mul_nonneg hr (by nlinarith [mul_pos hl hg0] : 0 ≤ a)]
    have hB : 0 < lam + gam * sig2 + rho * b := by nlinarith [mul_nonneg hr hb0]
    have ha0 : 0 ≤ a := by nlinarith [mul_pos hl hg0]
    set A := lam + gam * sig2 + rho * a
    set B := lam + gam * sig2 + rho * b
    have hlt : lam ^ 2 * rho < A * B := by
      have e1 := hden a ha0
      have e2 := hden b hb0
      have : lam ^ 2 < (lam + gam * sig2) * (lam + gam * sig2) := by nlinarith
      nlinarith [mul_le_mul e1 e2 (by positivity) (by positivity)]
    have hba : b - a = lam ^ 2 / A - lam ^ 2 / B := by
      have h1 : b = lam - lam ^ 2 / B := hbfix
      have h2 : a = lam - lam ^ 2 / A := hafix
      linarith
    have key : (b - a) * (A * B - lam ^ 2 * rho) = 0 := by
      have hA0 : 0 < A := by nlinarith [hden a ha0]
      have hB0 : 0 < B := by nlinarith [hden b hb0]
      have hBA : B - A = rho * (b - a) := by simp only [A, B]; ring
      have : (b - a) * (A * B) = (b - a) * (lam ^ 2 * rho) :=
        calc (b - a) * (A * B) = (lam ^ 2 / A - lam ^ 2 / B) * (A * B) := by rw [hba]
          _ = lam ^ 2 * (B - A) := by field_simp
          _ = (b - a) * (lam ^ 2 * rho) := by rw [hBA]; ring
      linarith
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · linarith
  · obtain ⟨-, -, hgp, hast⟩ := gcl_facts hl hgm hg hr hr1.le
    rw [hast, mul_div_cancel_left₀ _ hl.ne', hgp]

/-! ### Part 1: the filter -/

section Filter

variable {θ ω : Type} [Fintype θ] [DecidableEq θ] [Fintype ω] [DecidableEq ω]

lemma ct_eq {α β : Type} (A : Matrix α β ℝ) : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A

lemma kal_succ (P0 : Matrix θ θ ℝ) (H : Matrix ω θ ℝ) (R : Matrix ω ω ℝ) (t : ℕ) :
    kal P0 H R (t + 1) = kal P0 H R t -
      kal P0 H R t * Hᵀ * (H * kal P0 H R t * Hᵀ + R)⁻¹ * H * kal P0 H R t := rfl

lemma innov_pd {P : Matrix θ θ ℝ} {H : Matrix ω θ ℝ} {R : Matrix ω ω ℝ} (hP : P.PosDef)
    (hR : R.PosDef) : (H * P * Hᵀ + R).PosDef := by
  have h := hP.posSemidef.mul_mul_conjTranspose_same H
  rw [ct_eq] at h
  exact Matrix.PosDef.posSemidef_add h hR

/-- One Kalman step is the Woodbury inverse `(P⁻¹ + H'R⁻¹H)⁻¹`. -/
lemma kal_step_inv {P : Matrix θ θ ℝ} {H : Matrix ω θ ℝ} {R : Matrix ω ω ℝ} (hP : P.PosDef)
    (hR : R.PosDef) : P - P * Hᵀ * (H * P * Hᵀ + R)⁻¹ * H * P = (P⁻¹ + Hᵀ * R⁻¹ * H)⁻¹ := by
  have hAC : IsUnit (R⁻¹⁻¹ + H * P⁻¹⁻¹ * Hᵀ) := by
    rw [nonsing_inv_nonsing_inv _ (pd_unit hR), nonsing_inv_nonsing_inv _ (pd_unit hP), add_comm]
    exact (innov_pd hP hR).isUnit
  rw [add_mul_mul_inv_eq_sub P⁻¹ Hᵀ R⁻¹ H hP.inv.isUnit hR.inv.isUnit hAC,
    nonsing_inv_nonsing_inv _ (pd_unit hR), nonsing_inv_nonsing_inv _ (pd_unit hP), add_comm R]

lemma kal_pd_info {P0 : Matrix θ θ ℝ} {H : Matrix ω θ ℝ} {R : Matrix ω ω ℝ} (hP0 : P0.PosDef)
    (hR : R.PosDef) : ∀ t : ℕ, (kal P0 H R t).PosDef ∧
      (kal P0 H R t)⁻¹ = P0⁻¹ + (t : ℝ) • (Hᵀ * R⁻¹ * H) := by
  have hJ : (Hᵀ * R⁻¹ * H).PosSemidef := by
    have := hR.inv.posSemidef.conjTranspose_mul_mul_same H
    rwa [ct_eq] at this
  intro t
  induction t with
  | zero => exact ⟨hP0, by simp [kal]⟩
  | succ t ih =>
    obtain ⟨hP, hinv⟩ := ih
    rw [kal_succ, kal_step_inv hP hR]
    have hsum : ((kal P0 H R t)⁻¹ + Hᵀ * R⁻¹ * H).PosDef := hP.inv.add_posSemidef hJ
    refine ⟨hsum.inv, ?_⟩
    rw [nonsing_inv_nonsing_inv _ (pd_unit hsum), hinv]
    push_cast
    rw [add_smul, one_smul, add_assoc]

lemma kal_psd_step {P0 : Matrix θ θ ℝ} {H : Matrix ω θ ℝ} {R : Matrix ω ω ℝ} (hP0 : P0.PosDef)
    (hR : R.PosDef) (t : ℕ) : (kal P0 H R t - kal P0 H R (t + 1)).PosSemidef := by
  have hP := (kal_pd_info (H := H) hP0 hR t).1
  have hPsym := transpose_of_psd hP.posSemidef
  have hS := innov_pd (H := H) hP hR
  rw [kal_succ, sub_sub_cancel]
  have := hS.inv.posSemidef.conjTranspose_mul_mul_same (H * kal P0 H R t)
  rw [ct_eq, transpose_mul, hPsym] at this
  convert this using 1
  simp only [Matrix.mul_assoc]

lemma kal_mono {P0 : Matrix θ θ ℝ} {H : Matrix ω θ ℝ} {R : Matrix ω ω ℝ} (hP0 : P0.PosDef)
    (hR : R.PosDef) (t : ℕ) : ∀ s, t ≤ s → (kal P0 H R t - kal P0 H R s).PosSemidef := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rw [sub_self]; exact PosSemidef.zero
  | succ s _ ih =>
    have e : kal P0 H R t - kal P0 H R (s + 1) =
        (kal P0 H R t - kal P0 H R s) + (kal P0 H R s - kal P0 H R (s + 1)) := by abel
    rw [e]
    exact ih.add (kal_psd_step hP0 hR s)

end Filter

theorem filterFacts : FilterFacts := by
  intro θ ω _ _ _ _ P0 H R hP0 hR
  have hpd := kal_pd_info (H := H) hP0 hR
  refine ⟨fun t => (hpd t).1, fun t => (hpd t).2, kal_psd_step hP0 hR, fun t => ?_,
    fun ι _ G Sr hSr t => ⟨?_, fun s hs => ?_⟩⟩
  · have hP := (hpd t).1
    have hPsym := transpose_of_psd hP.posSemidef
    have hS := innov_pd (H := H) hP hR
    have hSsym := transpose_of_psd hS.posSemidef
    have hSi : (H * kal P0 H R t * Hᵀ + R)⁻¹ * (H * kal P0 H R t * Hᵀ + R) = 1 :=
      nonsing_inv_mul _ (pd_unit hS)
    rw [kal_succ, sub_sub_cancel, transpose_mul, transpose_mul, inv_sym hSsym, transpose_transpose,
      hPsym]
    set S := H * kal P0 H R t * Hᵀ + R
    clear_value S
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, hSi, Matrix.one_mul]
  · have h := (hpd t).1.posSemidef.mul_mul_conjTranspose_same G
    rw [ct_eq] at h
    exact Matrix.PosDef.posSemidef_add h hSr
  · have e : (G * kal P0 H R t * Gᵀ + Sr) - (G * kal P0 H R s * Gᵀ + Sr) =
        G * (kal P0 H R t - kal P0 H R s) * Gᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]
    have := (kal_mono (H := H) hP0 hR t s hs).mul_mul_conjTranspose_same G
    rwa [ct_eq] at this

/-! ### Part 1: the reference-case decoupling -/

section Blocks

lemma fromCols_add' {m n₁ n₂ : Type} (A₁ B₁ : Matrix m n₁ ℝ) (A₂ B₂ : Matrix m n₂ ℝ) :
    Matrix.fromCols A₁ A₂ + Matrix.fromCols B₁ B₂ = Matrix.fromCols (A₁ + B₁) (A₂ + B₂) := by
  ext i (j | j) <;> simp

lemma fromBlocks_sub' {l m n o : Type} (A A' : Matrix n l ℝ) (B B' : Matrix n m ℝ)
    (C C' : Matrix o l ℝ) (D D' : Matrix o m ℝ) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> simp

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma inv_blockdiag {A : Matrix α α ℝ} {D : Matrix β β ℝ} (hA : IsUnit A.det) (hD : IsUnit D.det) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ :=
  Matrix.inv_eq_left_inv (by
    rw [fromBlocks_multiply]
    simp [nonsing_inv_mul _ hA, nonsing_inv_mul _ hD, fromBlocks_one])

lemma pd_blockdiag {A : Matrix α α ℝ} {D : Matrix β β ℝ} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D).PosDef := by
  have := (Matrix.posDef_diagonal_iff (d := fun _ : Unit => (1 : ℝ))).mpr (fun _ => one_pos)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (herm_of ?_) fun x hx => ?_
  · rw [fromBlocks_transpose, transpose_of_psd hA.posSemidef, transpose_of_psd hD.posSemidef,
      transpose_zero, transpose_zero]
  · set a : α → ℝ := fun i => x (Sum.inl i)
    set d : β → ℝ := fun i => x (Sum.inr i)
    have hx' : x = Sum.elim a d := by funext i; cases i <;> rfl
    rw [hx', fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add, star_trivial, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [sumElim_dotProduct_sumElim]
    have ha := hA.posSemidef.dotProduct_mulVec_nonneg a
    have hd := hD.posSemidef.dotProduct_mulVec_nonneg d
    simp only [star_trivial] at ha hd
    by_cases h0 : a = 0
    · have hd0 : d ≠ 0 := by
        intro hd0
        apply hx
        funext i
        cases i with
        | inl i => exact congrFun h0 i
        | inr i => exact congrFun hd0 i
      have := hD.dotProduct_mulVec_pos hd0
      simp only [star_trivial] at this
      linarith
    · have := hA.dotProduct_mulVec_pos h0
      simp only [star_trivial] at this
      linarith

end Blocks

/-- A Kalman step with a block-diagonal state covariance and the transformed observation. -/
lemma kal_block_step {K N M : ℕ} {Pl Sf : Matrix (Fin K) (Fin K) ℝ} {Pa SA : Matrix (Fin N) (Fin N) ℝ}
    {SE : Matrix (Fin M) (Fin M) ℝ} (hPl : Pl.PosDef) (hPa : Pa.PosDef) (hSf : Sf.PosDef)
    (hSA : SA.PosDef) (hSE : SE.PosDef) :
    let P := Matrix.fromBlocks Pl 0 0 Pa
    P * (Htil K N M)ᵀ * (Htil K N M * P * (Htil K N M)ᵀ + Sz Sf SA SE)⁻¹ =
        Matrix.fromCols (Matrix.fromBlocks (Pl * (Pl + Sf)⁻¹) 0 0 (Pa * (Pa + SA)⁻¹)) 0 ∧
      P - P * (Htil K N M)ᵀ * (Htil K N M * P * (Htil K N M)ᵀ + Sz Sf SA SE)⁻¹ * Htil K N M * P =
        Matrix.fromBlocks (Pl - Pl * (Pl + Sf)⁻¹ * Pl) 0 0 (Pa - Pa * (Pa + SA)⁻¹ * Pa) := by
  intro P
  have hl := pd_unit (Matrix.PosDef.posSemidef_add hPl.posSemidef hSf)
  have ha := pd_unit (Matrix.PosDef.posSemidef_add hPa.posSemidef hSA)
  have hX : IsUnit (Matrix.fromBlocks (Pl + Sf) 0 0 (Pa + SA)).det :=
    pd_unit (pd_blockdiag (Matrix.PosDef.posSemidef_add hPl.posSemidef hSf)
      (Matrix.PosDef.posSemidef_add hPa.posSemidef hSA))
  have hHt : (Htil K N M)ᵀ = Matrix.fromCols 1 0 := by
    simp [Htil, transpose_fromRows]
  have hin : Htil K N M * P * (Htil K N M)ᵀ + Sz Sf SA SE =
      Matrix.fromBlocks (Matrix.fromBlocks (Pl + Sf) 0 0 (Pa + SA)) 0 0 SE := by
    rw [hHt]
    simp only [Htil]
    rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul, fromRows_mul_fromCols]
    simp only [Sz, Matrix.mul_one, Matrix.mul_zero, fromBlocks_add, add_zero, zero_add,
      P]
  have hinv : (Htil K N M * P * (Htil K N M)ᵀ + Sz Sf SA SE)⁻¹ =
      Matrix.fromBlocks (Matrix.fromBlocks ((Pl + Sf)⁻¹) 0 0 ((Pa + SA)⁻¹)) 0 0 SE⁻¹ := by
    rw [hin, inv_blockdiag hX (pd_unit hSE), inv_blockdiag hl ha]
  have hgain : P * (Htil K N M)ᵀ * (Htil K N M * P * (Htil K N M)ᵀ + Sz Sf SA SE)⁻¹ =
      Matrix.fromCols (Matrix.fromBlocks (Pl * (Pl + Sf)⁻¹) 0 0 (Pa * (Pa + SA)⁻¹)) 0 := by
    rw [hinv, hHt, mul_fromCols, fromCols_mul_fromBlocks]
    simp only [P, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      fromBlocks_multiply]
  refine ⟨hgain, ?_⟩
  rw [hgain]
  simp only [Htil, P, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero,
    fromBlocks_multiply, Matrix.zero_mul, zero_add, fromBlocks_sub', sub_zero]

/-- The observation transform `L` drops out of the filter. -/
lemma kal_transform {θ' ω' : Type} [Fintype θ'] [DecidableEq θ'] [Fintype ω'] [DecidableEq ω']
    {P0 : Matrix θ' θ' ℝ} {Ht : Matrix ω' θ' ℝ} {Szz L : Matrix ω' ω' ℝ} (hL : IsUnit L) : ∀ t, kal P0 (L * Ht) (L * Szz * Lᵀ) t = kal P0 Ht Szz t := by
  have hLd : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hL
  have hLtd : IsUnit Lᵀ.det := by rw [det_transpose]; exact hLd
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [kal_succ, kal_succ, ih]
    set P := kal P0 Ht Szz t
    have e : L * Ht * P * (L * Ht)ᵀ + L * Szz * Lᵀ = L * (Ht * P * Htᵀ + Szz) * Lᵀ := by
      rw [transpose_mul]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, transpose_mul]
    have h1 : Lᵀ * (Lᵀ)⁻¹ = 1 := mul_nonsing_inv _ hLtd
    have h2 : L⁻¹ * L = 1 := nonsing_inv_mul _ hLd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᵀ (Lᵀ)⁻¹, h1, Matrix.one_mul, ← Matrix.mul_assoc L⁻¹ L, h2, Matrix.one_mul]

theorem decouple : Decouple := by
  refine ⟨fun K N M BA BE => ?_, fun K N M Pl Sf Pa SA SE L hPl hPa hSf hSA hSE hL t => ?_, ?_⟩
  · set Li : Matrix ((Fin K ⊕ Fin N) ⊕ Fin M) ((Fin K ⊕ Fin N) ⊕ Fin M) ℝ :=
      Matrix.fromBlocks (Matrix.fromBlocks 1 0 (-BA) 1) 0 (Matrix.fromCols (-BE) 0) 1
    have h1 : Lobs BA BE * Li = 1 := by
      simp only [Lobs, Li, fromBlocks_multiply, fromCols_mul_fromBlocks, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
        fromCols_add', neg_zero, add_neg_cancel, fromCols_zero, fromBlocks_one]
    have h2 : Li * Lobs BA BE = 1 := by
      simp only [Lobs, Li, fromBlocks_multiply, fromCols_mul_fromBlocks, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, 
        fromCols_add', neg_add_cancel, fromCols_zero, fromBlocks_one]
    refine ⟨⟨⟨_, Li, h1, h2⟩, rfl⟩, fun f rA rE => ?_⟩
    rw [Matrix.inv_eq_right_inv h1]
    simp only [Li, fromBlocks_mulVec, fromCols_mulVec_sumElim, one_mulVec, zero_mulVec, add_zero,
      neg_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · congr 1; abel
    · abel
  · have hpdl := fun s => (kal_pd_info (H := (1 : Matrix (Fin K) (Fin K) ℝ)) hPl hSf s).1
    have hpda := fun s => (kal_pd_info (H := (1 : Matrix (Fin N) (Fin N) ℝ)) hPa hSA s).1
    have hSz : (Sz Sf SA SE).PosDef := pd_blockdiag (pd_blockdiag hSf hSA) hSE
    have hP0 := pd_blockdiag hPl hPa
    have hblk : ∀ s, kal (Matrix.fromBlocks Pl 0 0 Pa) (Htil K N M) (Sz Sf SA SE) s =
        Matrix.fromBlocks (kal Pl 1 Sf s) 0 0 (kal Pa 1 SA s) := by
      intro s
      induction s with
      | zero => rfl
      | succ s ih =>
        rw [kal_succ, ih, (kal_block_step (hpdl s) (hpda s) hSf hSA hSE).2, kal_succ, kal_succ]
        simp only [transpose_one, Matrix.mul_one, Matrix.one_mul]
    refine ⟨?_, ?_⟩
    · rw [kal_transform hL, hblk]
    · exact (kal_block_step (hpdl t) (hpda t) hSf hSA hSE).1
  · intro K N M BA BE Sf Pl SA Pa SE
    have hB : ∀ X : Matrix (Fin K) (Fin K) ℝ, Matrix.fromRows BA BE * X * (Matrix.fromRows BA BE)ᵀ =
        Matrix.fromBlocks (BA * X * BAᵀ) (BA * X * BEᵀ) (BE * X * BAᵀ) (BE * X * BEᵀ) := fun X => by
      rw [transpose_fromRows, fromRows_mul, fromRows_mul_fromCols]
    have hG : Matrix.fromBlocks BA 1 BE 0 * Matrix.fromBlocks Pl 0 0 Pa *
        (Matrix.fromBlocks BA (1 : Matrix (Fin N) (Fin N) ℝ) BE (0 : Matrix (Fin M) (Fin N) ℝ))ᵀ =
        Matrix.fromBlocks (BA * Pl * BAᵀ + Pa) (BA * Pl * BEᵀ) (BE * Pl * BAᵀ) (BE * Pl * BEᵀ) := by
      rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one,
        transpose_one, transpose_zero]
    rw [hG, hB, hB, fromBlocks_add, fromBlocks_add, fromBlocks_add]
    congr 1 <;> simp only [Matrix.mul_add, Matrix.add_mul, add_zero] <;> abel


/-! ### Part 4: coordinates -/

theorem coords : Coords := by
  intro K N BA BE hBE
  have hRB : BE⁻¹ * BE = 1 := nonsing_inv_mul _ hBE
  have hBR : BE * BE⁻¹ = 1 := mul_nonsing_inv _ hBE
  have hRBt : BEᵀ * (BE⁻¹)ᵀ = 1 := by rw [← transpose_mul, hRB, transpose_one]
  have hBRt : (BE⁻¹)ᵀ * BEᵀ = 1 := by rw [← transpose_mul, hBR, transpose_one]
  have h1 : Smap BA BE * Sinv BA BE = 1 := by
    simp only [Smap, Sinv, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
      Matrix.zero_mul, zero_add, add_zero, Matrix.mul_neg, ← Matrix.mul_assoc, hRBt, add_neg_cancel,
      neg_zero]
    exact fromBlocks_one
  have h2 : Sinv BA BE * Smap BA BE = 1 := by
    simp only [Smap, Sinv, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, 
      Matrix.zero_mul, zero_add, add_zero, hBRt, add_neg_cancel, fromBlocks_one]
  have hT : (Smap BA BE)ᵀ = Gmat BA BE := by
    simp only [Smap, Gmat, fromBlocks_transpose, transpose_transpose, transpose_one, transpose_zero]
  have hSiT : (Sinv BA BE)ᵀ = Matrix.fromBlocks 0 BE⁻¹ 1 (-(BA * BE⁻¹)) := by
    simp only [Sinv, fromBlocks_transpose, transpose_zero, transpose_one, transpose_transpose,
      transpose_neg, transpose_mul]
  refine ⟨h1, h2, hT, ?_, fun cE => ?_, fun y xA => ?_⟩
  · rw [← hT, ← transpose_mul, h1, transpose_one]
  · rw [hSiT, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_add, 
      neg_mulVec, ← mulVec_mulVec, mulVec_zero]
  · simp only [Sinv, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, one_mulVec,
      zero_add, neg_mulVec, ← mulVec_mulVec, sub_eq_add_neg, mulVec_add, mulVec_neg]

/-! ### Part 4: the change of coordinates -/

section Trans

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The coordinate change moves `D_t` by congruence. -/
lemma trans_D {Q : LQ ι π} {Si : Matrix ι κ ℝ} {t : ℕ}
    (hA : (Q.trans Si).A (t + 1) = Siᵀ * Q.A (t + 1) * Si) :
    (Q.trans Si).D t = Siᵀ * Q.D t * Si := by
  rw [LQ.D, hA]
  show Siᵀ * Q.Lam * Si + Siᵀ * Q.S t * Si + Q.rho • (Siᵀ * Q.A (t + 1) * Si) =
    Siᵀ * (Q.Lam + Q.S t + Q.rho • Q.A (t + 1)) * Si
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma trans_Dinv {Q : LQ ι π} (hS : Q.Setting) {Sm : Matrix κ ι ℝ} {Si : Matrix ι κ ℝ}
    (h1 : Sm * Si = 1) (h2 : Si * Sm = 1) {t : ℕ}
    (hA : (Q.trans Si).A (t + 1) = Siᵀ * Q.A (t + 1) * Si) :
    ((Q.trans Si).D t)⁻¹ = Sm * (Q.D t)⁻¹ * Smᵀ := by
  rw [trans_D hA]
  refine Matrix.inv_eq_left_inv ?_
  have hT : Smᵀ * Siᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have hDu := pd_unit (LQ.D_pd hS t)
  calc Sm * (Q.D t)⁻¹ * Smᵀ * (Siᵀ * Q.D t * Si)
      = Sm * (Q.D t)⁻¹ * (Smᵀ * Siᵀ) * Q.D t * Si := by simp only [Matrix.mul_assoc]
    _ = Sm * ((Q.D t)⁻¹ * Q.D t) * Si := by rw [hT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul _ hDu, Matrix.mul_one, h1]

lemma trans_ric {Q : LQ ι π} (hS : Q.Setting) {Sm : Matrix κ ι ℝ} {Si : Matrix ι κ ℝ}
    (h1 : Sm * Si = 1) (h2 : Si * Sm = 1) :
    ∀ t, (Q.trans Si).A t = Siᵀ * Q.A t * Si ∧ (Q.trans Si).C t = Siᵀ * Q.C t ∧
      (Q.trans Si).c t = Siᵀ *ᵥ Q.c t := by
  have hT : Smᵀ * Siᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  suffices h : ∀ k t, Q.T - t = k → (Q.trans Si).A t = Siᵀ * Q.A t * Si ∧
      (Q.trans Si).C t = Siᵀ * Q.C t ∧ (Q.trans Si).c t = Siᵀ *ᵥ Q.c t from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    have hTt : (Q.trans Si).T ≤ t := by simp only [LQ.trans]; omega
    rw [LQ.A_ge _ hTt, LQ.C_ge _ hTt, LQ.c_ge _ hTt, LQ.A_ge Q (by omega), LQ.C_ge Q (by omega),
      LQ.c_ge Q (by omega)]
    simp
  | succ k ih =>
    intro t ht
    have htT : t < Q.T := by omega
    have htT' : t < (Q.trans Si).T := htT
    obtain ⟨iA, iC, ic⟩ := ih (t + 1) (by omega)
    have hDi := trans_Dinv hS h1 h2 iA
    obtain ⟨eA, eC, ec⟩ := LQ.ric_lt (Q.trans Si) htT'
    obtain ⟨fA, fC, fc⟩ := LQ.ric_lt Q htT
    -- the middle factor `Si * Sm * D⁻¹ * Smᵀ * Siᵀ` collapses to `D⁻¹`
    have hmid : Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * Siᵀ = (Q.D t)⁻¹ := by
      rw [← Matrix.mul_assoc Si, ← Matrix.mul_assoc Si, h2, Matrix.one_mul, Matrix.mul_assoc, hT,
        Matrix.mul_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [eA, hDi, fA]
      show Siᵀ * Q.Lam * Si - Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * (Siᵀ * Q.Lam * Si) = _
      rw [show Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * (Siᵀ * Q.Lam * Si) =
          Siᵀ * Q.Lam * (Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * Siᵀ) * Q.Lam * Si by
        simp only [Matrix.mul_assoc], hmid]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    · rw [eC, hDi, fC, iC]
      show Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * (Siᵀ * Q.G t + Q.rho • (Siᵀ * Q.C (t + 1))) = _
      rw [show Siᵀ * Q.G t + Q.rho • (Siᵀ * Q.C (t + 1)) = Siᵀ * (Q.G t + Q.rho • Q.C (t + 1)) by
        rw [Matrix.mul_add, Matrix.mul_smul],
        show Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * (Siᵀ * (Q.G t + Q.rho • Q.C (t + 1))) =
          Siᵀ * Q.Lam * (Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * Siᵀ) * (Q.G t + Q.rho • Q.C (t + 1)) by
        simp only [Matrix.mul_assoc], hmid]
      simp only [Matrix.mul_assoc]
    · rw [ec, hDi, fc, ic]
      show (Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ)) *ᵥ (Q.rho • (Siᵀ *ᵥ Q.c (t + 1)) - Siᵀ *ᵥ Q.e) = _
      rw [← mulVec_smul, ← mulVec_sub, mulVec_mulVec,
        show Siᵀ * Q.Lam * Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * Siᵀ =
          Siᵀ * Q.Lam * (Si * (Sm * (Q.D t)⁻¹ * Smᵀ) * Siᵀ) by simp only [Matrix.mul_assoc], hmid,
        mulVec_mulVec, Matrix.mul_assoc]

end Trans

theorem transform : Transform := by
  intro ι κ π _ _ _ _ _ Q Sm Si hS h1 h2
  have hinj : Function.Injective Si.mulVec := by
    intro a b hab
    have := congrArg (Sm *ᵥ ·) hab
    simpa only [mulVec_mulVec, h1, one_mulVec] using this
  have hS' : (Q.trans Si).Setting := by
    refine ⟨?_, fun t => ?_, hS.2.2⟩
    · have := hS.1.conjTranspose_mul_mul_same Si
      rwa [ct_eq] at this
    · have := (hS.2.1 t).conjTranspose_mul_mul_same hinj
      rwa [ct_eq] at this
  refine ⟨hS', fun t ht xm m => ?_⟩
  have hT : Smᵀ * Siᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  obtain ⟨iA, iC, ic⟩ := trans_ric hS h1 h2 (t + 1)
  have hDi := trans_Dinv hS h1 h2 iA
  have hK : (Q.trans Si).K t * Sm = Sm * Q.K t := by
    show ((Q.trans Si).D t)⁻¹ * (Siᵀ * Q.Lam * Si) * Sm = _
    rw [hDi]
    calc Sm * (Q.D t)⁻¹ * Smᵀ * (Siᵀ * Q.Lam * Si) * Sm
        = Sm * (Q.D t)⁻¹ * (Smᵀ * Siᵀ) * Q.Lam * (Si * Sm) := by simp only [Matrix.mul_assoc]
      _ = Sm * Q.K t := by rw [hT, h2]; simp only [Matrix.mul_one, LQ.K, Matrix.mul_assoc]
  have hL : (Q.trans Si).L t = Sm * Q.L t := by
    show ((Q.trans Si).D t)⁻¹ * (Siᵀ * Q.G t + Q.rho • (Q.trans Si).C (t + 1)) = _
    rw [hDi, iC, ← Matrix.mul_smul, ← Matrix.mul_add]
    calc Sm * (Q.D t)⁻¹ * Smᵀ * (Siᵀ * (Q.G t + Q.rho • Q.C (t + 1)))
        = Sm * (Q.D t)⁻¹ * (Smᵀ * Siᵀ) * (Q.G t + Q.rho • Q.C (t + 1)) := by simp only [Matrix.mul_assoc]
      _ = Sm * Q.L t := by rw [hT, Matrix.mul_one]; simp only [LQ.L, Matrix.mul_assoc]
  have hl : (Q.trans Si).l t = Sm *ᵥ Q.l t := by
    show ((Q.trans Si).D t)⁻¹ *ᵥ (Q.rho • (Q.trans Si).c (t + 1) - Siᵀ *ᵥ Q.e) = _
    rw [hDi, ic, ← mulVec_smul, ← mulVec_sub, mulVec_mulVec,
      show Sm * (Q.D t)⁻¹ * Smᵀ * Siᵀ = Sm * (Q.D t)⁻¹ by
        rw [Matrix.mul_assoc, hT, Matrix.mul_one], ← mulVec_mulVec]
    rfl
  simp only [LQ.policy]
  rw [mulVec_mulVec, hK, ← mulVec_mulVec, hL, ← mulVec_mulVec, hl, mulVec_add, mulVec_add]

/-! ### Part 4: the reference-case blocks -/

theorem refBlocks : RefBlocks := by
  intro K N BA BE SfP SAP LA SE LE hBE
  have hRB : BE⁻¹ * BE = 1 := nonsing_inv_mul _ hBE
  have hSiT : (Sinv BA BE)ᵀ = Matrix.fromBlocks 0 BE⁻¹ 1 (-(BA * BE⁻¹)) := by
    simp only [Sinv, fromBlocks_transpose, transpose_zero, transpose_one, transpose_transpose,
      transpose_neg, transpose_mul]
  have hSB : (Sinv BA BE)ᵀ * Matrix.fromRows BA BE = Matrix.fromRows 1 0 := by
    rw [hSiT, fromBlocks_mul_fromRows]
    simp only [Matrix.zero_mul, zero_add, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, hRB,
      Matrix.mul_one, add_neg_cancel]
  have hBS : (Matrix.fromRows BA BE)ᵀ * Sinv BA BE = Matrix.fromCols 1 0 := by
    rw [← transpose_transpose (Sinv BA BE), ← transpose_mul, hSB, transpose_fromRows, transpose_one,
      transpose_zero]
  have hdiag : ∀ (X : Matrix (Fin N) (Fin N) ℝ) (Y : Matrix (Fin K) (Fin K) ℝ),
      (Sinv BA BE)ᵀ * Matrix.fromBlocks X 0 0 Y * Sinv BA BE =
        Matrix.fromBlocks (BE⁻¹ * Y * (BE⁻¹)ᵀ) (-(BE⁻¹ * Y * (BE⁻¹)ᵀ * BAᵀ))
          (-(BA * (BE⁻¹ * Y * (BE⁻¹)ᵀ))) (X + BA * (BE⁻¹ * Y * (BE⁻¹)ᵀ) * BAᵀ) := by
    intro X Y
    rw [hSiT]
    simp only [Sinv, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.add_mul, hdiag]
    rw [show (Sinv BA BE)ᵀ * (Matrix.fromRows BA BE * SfP * (Matrix.fromRows BA BE)ᵀ) * Sinv BA BE =
        ((Sinv BA BE)ᵀ * Matrix.fromRows BA BE) * SfP * ((Matrix.fromRows BA BE)ᵀ * Sinv BA BE) by
      simp only [Matrix.mul_assoc], hSB, hBS, fromRows_mul, fromRows_mul_fromCols]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, fromBlocks_add,
      zero_add]
  · rw [hdiag]

/-! ### Part 4(a): exact separation -/

lemma sub_inl {α β : Type} (A : Matrix α α ℝ) (B : Matrix α β ℝ) (C : Matrix β α ℝ) (D : Matrix β β ℝ) :
    (Matrix.fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext i j; simp

lemma sub_inr {α β : Type} (A : Matrix α α ℝ) (B : Matrix α β ℝ) (C : Matrix β α ℝ) (D : Matrix β β ℝ) :
    (Matrix.fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext i j; simp

theorem separation : Separation := by
  intro K N Q LA Sy SA hS hL hSt hG he QA t ht
  have hLA : LA.PosSemidef := by
    have := hS.1.submatrix Sum.inr
    rwa [hL, sub_inr] at this
  have hSA : ∀ t, (SA t).PosDef := fun t => by
    have := (hS.2.1 t).submatrix Sum.inr_injective
    rwa [hSt, sub_inr] at this
  have hSy : ∀ t, (Sy t).PosDef := fun t => by
    have := (hS.2.1 t).submatrix Sum.inl_injective
    rwa [hSt, sub_inl] at this
  have hQA : QA.Setting := ⟨hLA, hSA, hS.2.2⟩
  have hT : QA.T = Q.T := rfl
  -- the recursion is block diagonal
  have hric : ∀ s, Q.A s = Matrix.fromBlocks 0 0 0 (QA.A s) ∧ Q.C s = Matrix.fromBlocks 0 0 0 (QA.C s) ∧
      Q.c s = 0 ∧ QA.c s = 0 := by
    suffices h : ∀ k s, Q.T - s = k → Q.A s = Matrix.fromBlocks 0 0 0 (QA.A s) ∧
        Q.C s = Matrix.fromBlocks 0 0 0 (QA.C s) ∧ Q.c s = 0 ∧ QA.c s = 0 from fun s => h _ s rfl
    intro k
    induction k with
    | zero =>
      intro s hs
      rw [LQ.A_ge Q (by omega), LQ.C_ge Q (by omega), LQ.c_ge Q (by omega), LQ.A_ge QA (by omega),
        LQ.C_ge QA (by omega), LQ.c_ge QA (by omega), fromBlocks_zero]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | succ k ih =>
      intro s hs
      have hsT : s < Q.T := by omega
      obtain ⟨iA, iC, ic, icA⟩ := ih (s + 1) (by omega)
      have hD : Q.D s = Matrix.fromBlocks (Sy s) 0 0 (QA.D s) := by
        simp only [LQ.D, hL, hSt, iA, fromBlocks_smul, smul_zero, fromBlocks_add, zero_add, add_zero]
        rfl
      have hDi : (Q.D s)⁻¹ = Matrix.fromBlocks (Sy s)⁻¹ 0 0 (QA.D s)⁻¹ := by
        rw [hD, inv_blockdiag (pd_unit (hSy s)) (pd_unit (LQ.D_pd hQA s))]
      obtain ⟨eA, eC, ec⟩ := LQ.ric_lt Q hsT
      obtain ⟨fA, fC, fc⟩ := LQ.ric_lt QA hsT
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eA, fA, hDi, hL]
        simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
          fromBlocks_sub', sub_zero]
        rfl
      · rw [eC, fC, hDi, hL, iC, hG s, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
        simp only [smul_zero, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
          Matrix.mul_one]
        rfl
      · rw [ec, ic, he, smul_zero, sub_zero, mulVec_zero]
      · rw [fc, icA]
        show (QA.Lam * (QA.D s)⁻¹) *ᵥ (QA.rho • (0 : Fin N → ℝ) - 0) = 0
        rw [smul_zero, sub_zero, mulVec_zero]
  obtain ⟨iA, iC, ic, icA⟩ := hric (t + 1)
  have hD : Q.D t = Matrix.fromBlocks (Sy t) 0 0 (QA.D t) := by
    simp only [LQ.D, hL, hSt, iA, fromBlocks_smul, smul_zero, fromBlocks_add, zero_add, add_zero]
    rfl
  have hDi : (Q.D t)⁻¹ = Matrix.fromBlocks (Sy t)⁻¹ 0 0 (QA.D t)⁻¹ := by
    rw [hD, inv_blockdiag (pd_unit (hSy t)) (pd_unit (LQ.D_pd hQA t))]
  have hQl : QA.l t = 0 := by
    show (QA.D t)⁻¹ *ᵥ (QA.rho • QA.c (t + 1) - (0 : Fin N → ℝ)) = 0
    rw [icA, smul_zero, sub_zero, mulVec_zero]
  have hK : Q.K t = Matrix.fromBlocks 0 0 0 (QA.K t) := by
    rw [LQ.K, hDi, hL, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rfl
  have hLm : Q.L t = Matrix.fromBlocks (Sy t)⁻¹ 0 0 (QA.L t) := by
    rw [LQ.L, hDi, iC, hG t, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add, fromBlocks_multiply]
    simp only [smul_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rfl
  have hl : Q.l t = 0 := by rw [LQ.l, ic, he, smul_zero, sub_zero, mulVec_zero]
  refine ⟨fun y xA lh ah => ?_, ?_⟩
  · simp only [LQ.policy, hK, hLm, hl, hQl, add_zero, fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, zero_mulVec, zero_add]
    funext i
    cases i <;> simp
  · show 1 - (Q.D t)⁻¹ * Q.Lam = Matrix.fromBlocks 1 0 0 (1 - (QA.D t)⁻¹ * QA.Lam)
    rw [hDi, hL, ← fromBlocks_one, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, fromBlocks_sub', sub_zero]
    rfl

/-- Claim 030, parts 1-5. -/
theorem proof : Standalone.M5PartialAdjustmentSplit.statement :=
  ⟨filterFacts, decouple, bellmanVerif, matrices, aimThm, coords, transform, refBlocks, separation,
    speeds⟩

end

end Novel.M5PartialAdjustmentSplitProof

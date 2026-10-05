import Mathlib.Analysis.CStarAlgebra.Matrix
import Novel.M5PartialAdjustmentSplitProof
import Standalone.M5PlugInValueLoss

/-!
# Proof of claim 033

Uses claim 030's proof module (`depends_on: [30]`, Q-04): the recursion, the Bellman verification
and its completed square. Neither AX-11 nor AX-12 is used: the finite-horizon bounds are proved
directly.

* **Norms.** The spectral norm bounds `‖A v‖ ≤ ‖A‖ ‖v‖`. For `R ⪰ 0`, `‖(I + R)⁻¹‖ ≤ 1`, since
  `‖(I + R)u‖² ≥ ‖u‖²`. The one-step map is 1-Lipschitz:
  `(I + R₁)⁻¹ - (I + R₂)⁻¹ = (I + R₁)⁻¹(R₂ - R₁)(I + R₂)⁻¹`.
* **Normalization.** `D_t = W(I + R_t)W`, `W⁻¹A_tW⁻¹ = I - (I + R_t)⁻¹` and `W K_t W⁻¹ = (I + R_t)⁻¹`.
  Also `W L_t = (I + R_t)⁻¹(W⁻¹G + ρ W⁻¹C_{t+1})` with `W⁻¹C_s = W L_s`, and likewise for `l`.
* **Unrolling.** `a_t ≤ b_t + ρ a_{t+1}` with `a = 0` from `T` on gives
  `a_t ≤ Σ_{s ≥ t} ρ^{s-t} b_s`.
-/

namespace Novel.M5PlugInValueLossProof

open Matrix Standalone.M5PartialAdjustmentSplit Standalone.M5PlugInValueLoss
open Novel.M5PartialAdjustmentSplitProof
open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Norms -/

section Norms

variable {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

lemma vnorm_eq (v : κ → ℝ) : ‖(EuclideanSpace.equiv κ ℝ).symm v‖ = vnorm v := by
  rw [vnorm, EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

lemma vnorm_nonneg (v : κ → ℝ) : 0 ≤ vnorm v := Real.sqrt_nonneg _

lemma dot_self_nonneg (v : κ → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma vnorm_sq (v : κ → ℝ) : vnorm v ^ 2 = v ⬝ᵥ v := Real.sq_sqrt (dot_self_nonneg v)

lemma mulVec_le (A : Matrix κ μ ℝ) (v : μ → ℝ) : vnorm (A *ᵥ v) ≤ ‖A‖ * vnorm v := by
  have h := A.l2_opNorm_mulVec ((EuclideanSpace.equiv μ ℝ).symm v)
  rw [← vnorm_eq, ← vnorm_eq]
  exact h

lemma opnorm_le {A : Matrix κ μ ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ v, vnorm (A *ᵥ v) ≤ c * vnorm v) :
    ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have := h (EuclideanSpace.equiv μ ℝ x)
  rw [← vnorm_eq, ← vnorm_eq] at this
  exact this

lemma vnorm_add (u v : κ → ℝ) : vnorm (u + v) ≤ vnorm u + vnorm v := by
  rw [← vnorm_eq, ← vnorm_eq, ← vnorm_eq, map_add]
  exact norm_add_le _ _

lemma vnorm_sub (u v : κ → ℝ) : vnorm (u - v) ≤ vnorm u + vnorm v := by
  rw [← vnorm_eq, ← vnorm_eq, ← vnorm_eq, map_sub]
  exact norm_sub_le _ _

lemma vnorm_smul (c : ℝ) (v : κ → ℝ) : vnorm (c • v) = |c| * vnorm v := by
  rw [← vnorm_eq, ← vnorm_eq, map_smul, norm_smul, Real.norm_eq_abs]

lemma dot_le (u v : κ → ℝ) : u ⬝ᵥ v ≤ vnorm u * vnorm v := by
  have h := real_inner_le_norm ((EuclideanSpace.equiv κ ℝ).symm u) ((EuclideanSpace.equiv κ ℝ).symm v)
  rw [vnorm_eq, vnorm_eq] at h
  convert h using 1
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma one_norm_le : ‖(1 : Matrix κ κ ℝ)‖ ≤ 1 :=
  opnorm_le zero_le_one fun v => by rw [one_mulVec, one_mul]

lemma one_add_pd {R : Matrix κ κ ℝ} (hR : R.PosSemidef) : (1 + R).PosDef :=
  PosDef.one.add_posSemidef hR

/-- `‖(I + R)⁻¹‖ ≤ 1` for `R ⪰ 0`. -/
lemma inv_norm_le {R : Matrix κ κ ℝ} (hR : R.PosSemidef) : ‖(1 + R)⁻¹‖ ≤ 1 := by
  have hu := pd_unit (one_add_pd hR)
  refine opnorm_le zero_le_one fun v => ?_
  set u := (1 + R)⁻¹ *ᵥ v
  have hv : v = u + R *ᵥ u := by
    have h : (1 + R) *ᵥ u = v := by simp only [u, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
    rw [add_mulVec, one_mulVec] at h
    exact h.symm
  have h1 := hR.dotProduct_mulVec_nonneg u
  simp only [star_trivial] at h1
  have h2 := dot_self_nonneg (R *ᵥ u)
  have hsq : vnorm u ^ 2 ≤ vnorm v ^ 2 := by
    rw [vnorm_sq, vnorm_sq, hv]
    simp only [add_dotProduct, dotProduct_add]
    rw [dotProduct_comm (R *ᵥ u) u]
    linarith
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (vnorm_nonneg u) (vnorm_nonneg v) two_ne_zero).mp hsq

/-- The one-step map is 1-Lipschitz on positive semidefinite matrices. -/
lemma inv_lip {R₁ R₂ : Matrix κ κ ℝ} (h₁ : R₁.PosSemidef) (h₂ : R₂.PosSemidef) :
    ‖(1 + R₁)⁻¹ - (1 + R₂)⁻¹‖ ≤ ‖R₁ - R₂‖ := by
  have hu₁ := pd_unit (one_add_pd h₁)
  have hu₂ := pd_unit (one_add_pd h₂)
  have e : (1 + R₁)⁻¹ - (1 + R₂)⁻¹ = (1 + R₁)⁻¹ * (R₂ - R₁) * (1 + R₂)⁻¹ := by
    rw [show R₂ - R₁ = (1 + R₂) - (1 + R₁) by abel, Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul _ hu₁,
      Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu₂, Matrix.mul_one]
  rw [e, norm_sub_rev R₁ R₂]
  calc ‖(1 + R₁)⁻¹ * (R₂ - R₁) * (1 + R₂)⁻¹‖ ≤ ‖(1 + R₁)⁻¹‖ * ‖R₂ - R₁‖ * ‖(1 + R₂)⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖R₂ - R₁‖ * 1 := by
        gcongr
        · exact inv_norm_le h₁
        · exact inv_norm_le h₂
    _ = ‖R₂ - R₁‖ := by ring

lemma one_sub_inv_psd {R : Matrix κ κ ℝ} (hR : R.PosSemidef) : (1 - (1 + R)⁻¹).PosSemidef := by
  have hu := pd_unit (one_add_pd hR)
  have hRs := transpose_of_psd hR
  refine psd_of ?_ fun x => ?_
  · rw [transpose_sub, transpose_one, transpose_nonsing_inv, transpose_add, transpose_one, hRs]
  · set y := (1 + R)⁻¹ *ᵥ x
    have hx : x = y + R *ᵥ y := by
      have h : (1 + R) *ᵥ y = x := by simp only [y, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
      rw [add_mulVec, one_mulVec] at h
      exact h.symm
    have h1 := hR.dotProduct_mulVec_nonneg y
    simp only [star_trivial] at h1
    have h2 := dot_self_nonneg (R *ᵥ y)
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
    change 0 ≤ x ⬝ᵥ x - x ⬝ᵥ y
    rw [hx]
    simp only [add_dotProduct, dotProduct_add]
    rw [dotProduct_comm (R *ᵥ y) y]
    linarith

end Norms

/-! ### Unrolling -/

lemma unroll {T : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℕ → ℝ} (h0 : ∀ s, T ≤ s → a s = 0)
    (hstep : ∀ s, s < T → a s ≤ b s + ρ * a (s + 1)) :
    ∀ t, a t ≤ ∑ k ∈ Finset.range (T - t), ρ ^ k * b (t + k) := by
  suffices h : ∀ n t, T - t = n → a t ≤ ∑ k ∈ Finset.range (T - t), ρ ^ k * b (t + k) from
    fun t => h _ t rfl
  intro n
  induction n with
  | zero => intro t ht; rw [h0 t (by omega), ht, Finset.sum_range_zero]
  | succ n ih =>
    intro t ht
    have hih := ih (t + 1) (by omega)
    rw [ht, Finset.sum_range_succ', pow_zero, one_mul, add_zero, add_comm]
    rw [show T - (t + 1) = n by omega] at hih
    calc a t ≤ b t + ρ * a (t + 1) := hstep t (by omega)
      _ ≤ b t + ρ * ∑ k ∈ Finset.range n, ρ ^ k * b (t + 1 + k) := by gcongr
      _ = b t + ∑ k ∈ Finset.range n, ρ ^ (k + 1) * b (t + (k + 1)) := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_succ, show t + 1 + k = t + (k + 1) by omega]
          ring

/-! ### The normalized recursion -/

section Normal

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]
  {P : LQ ι π} {W : Matrix ι ι ℝ} (hWs : Wᵀ = W) (hWW : W * W = P.Lam) (hWu : IsUnit W)
include hWs hWW hWu

/-- `R_t = W⁻¹(S_t + ρA_{t+1})W⁻¹`. -/
def Rn (P : LQ ι π) (W : Matrix ι ι ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  W⁻¹ * (P.S t + P.rho • P.A (t + 1)) * W⁻¹

lemma wd : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hWu
lemma wiw : W⁻¹ * W = 1 := nonsing_inv_mul W (wd hWs hWW hWu)
lemma wwi : W * W⁻¹ = 1 := mul_nonsing_inv W (wd hWs hWW hWu)
lemma wi_sym : (W⁻¹)ᵀ = W⁻¹ := inv_sym hWs

lemma canc1 {κ : Type} [Fintype κ] (Y : Matrix ι κ ℝ) : W⁻¹ * (W * Y) = Y := by
  rw [← Matrix.mul_assoc, wiw hWs hWW hWu, Matrix.one_mul]
lemma canc2 {κ : Type} [Fintype κ] (Y : Matrix ι κ ℝ) : W * (W⁻¹ * Y) = Y := by
  rw [← Matrix.mul_assoc, wwi hWs hWW hWu, Matrix.one_mul]

lemma D_eq (t : ℕ) : P.D t = W * (1 + Rn P W t) * W := by
  show P.Lam + P.S t + P.rho • P.A (t + 1) = _
  rw [Rn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hWW, add_assoc]
  congr 1
  simp only [Matrix.mul_assoc, canc2 hWs hWW hWu, wiw hWs hWW hWu, Matrix.mul_one]

lemma Dinv_eq (t : ℕ) : (P.D t)⁻¹ = W⁻¹ * (1 + Rn P W t)⁻¹ * W⁻¹ := by
  rw [D_eq hWs hWW hWu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

lemma M_eq {t : ℕ} (ht : t < P.T) : W⁻¹ * P.A t * W⁻¹ = 1 - (1 + Rn P W t)⁻¹ := by
  obtain ⟨eA, -, -⟩ := LQ.ric_lt P ht
  rw [eA, Dinv_eq hWs hWW hWu, ← hWW]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, canc1 hWs hWW hWu, canc2 hWs hWW hWu]
  rw [wwi hWs hWW hWu]
  simp only [Matrix.mul_one]

lemma K_eq (t : ℕ) : W * P.K t * W⁻¹ = (1 + Rn P W t)⁻¹ := by
  rw [LQ.K, Dinv_eq hWs hWW hWu, ← hWW]
  simp only [Matrix.mul_assoc, canc2 hWs hWW hWu, wwi hWs hWW hWu, wiw hWs hWW hWu, Matrix.mul_one]

lemma C_eq {s : ℕ} (hs : s < P.T) : W⁻¹ * P.C s = W * P.L s := by
  obtain ⟨-, eC, -⟩ := LQ.ric_lt P hs
  rw [eC, LQ.L, ← hWW]
  simp only [Matrix.mul_assoc, canc1 hWs hWW hWu]

lemma L_eq (t : ℕ) : W * P.L t = (1 + Rn P W t)⁻¹ * (W⁻¹ * P.G t + P.rho • (W⁻¹ * P.C (t + 1))) := by
  rw [LQ.L, Dinv_eq hWs hWW hWu]
  simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul, canc2 hWs hWW hWu]

lemma c_eq {s : ℕ} (hs : s < P.T) : W⁻¹ *ᵥ P.c s = W *ᵥ P.l s := by
  obtain ⟨-, -, ec⟩ := LQ.ric_lt P hs
  rw [ec, LQ.l, ← hWW, mulVec_mulVec, mulVec_mulVec]
  simp only [Matrix.mul_assoc, canc1 hWs hWW hWu]

lemma l_eq (t : ℕ) : W *ᵥ P.l t = (1 + Rn P W t)⁻¹ *ᵥ (P.rho • (W⁻¹ *ᵥ P.c (t + 1)) - W⁻¹ *ᵥ P.e) := by
  rw [LQ.l, Dinv_eq hWs hWW hWu, mulVec_mulVec, ← mulVec_smul, ← mulVec_sub, mulVec_mulVec]
  simp only [Matrix.mul_assoc, canc2 hWs hWW hWu]

variable (hL : P.Lam.PosDef) (hS : ∀ t, (P.S t).PosSemidef) (hr : 0 ≤ P.rho)
include hL hS hr

/-- Backward induction: every `A_t` and every `R_t` is positive semidefinite. -/
lemma A_psd : ∀ t, (P.A t).PosSemidef := by
  suffices h : ∀ k t, P.T - t = k → (P.A t).PosSemidef from fun t => h _ t rfl
  intro k
  induction k with
  | zero => intro t ht; rw [LQ.A_ge P (by omega)]; exact PosSemidef.zero
  | succ k ih =>
    intro t ht
    have htT : t < P.T := by omega
    have hR : (Rn P W t).PosSemidef := by
      have := ((hS t).add ((ih (t + 1) (by omega)).smul hr)).conjTranspose_mul_mul_same W⁻¹
      rwa [ct_eq, wi_sym hWs hWW hWu] at this
    have hM := one_sub_inv_psd hR
    rw [← M_eq hWs hWW hWu htT] at hM
    have := hM.conjTranspose_mul_mul_same W
    rwa [ct_eq, hWs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, wwi hWs hWW hWu, Matrix.one_mul,
      Matrix.mul_assoc, wiw hWs hWW hWu, Matrix.mul_one] at this

lemma R_psd (t : ℕ) : (Rn P W t).PosSemidef := by
  have := ((hS t).add ((A_psd hWs hWW hWu hL hS hr (t + 1)).smul hr)).conjTranspose_mul_mul_same W⁻¹
  rwa [ct_eq, wi_sym hWs hWW hWu] at this

/-- `‖W⁻¹ C_s‖ ≤ (T - s)‖W⁻¹G‖` for a constant mean map. -/
lemma C_bound {G : Matrix ι π ℝ} (hG : ∀ t, P.G t = G) (hr1 : P.rho ≤ 1) :
    ∀ s, ‖W⁻¹ * P.C s‖ ≤ ((P.T - s : ℕ) : ℝ) * ‖W⁻¹ * G‖ := by
  suffices h : ∀ k s, P.T - s = k → ‖W⁻¹ * P.C s‖ ≤ ((P.T - s : ℕ) : ℝ) * ‖W⁻¹ * G‖ from
    fun s => h _ s rfl
  intro k
  induction k with
  | zero => intro s hs; rw [LQ.C_ge P (by omega), Matrix.mul_zero, norm_zero, hs]; simp
  | succ k ih =>
    intro s hs
    have hsT : s < P.T := by omega
    have hih := ih (s + 1) (by omega)
    rw [C_eq hWs hWW hWu hsT, L_eq hWs hWW hWu, hG, hs]
    rw [show P.T - (s + 1) = k by omega] at hih
    calc ‖(1 + Rn P W s)⁻¹ * (W⁻¹ * G + P.rho • (W⁻¹ * P.C (s + 1)))‖
        ≤ ‖(1 + Rn P W s)⁻¹‖ * ‖W⁻¹ * G + P.rho • (W⁻¹ * P.C (s + 1))‖ := l2_opNorm_mul _ _
      _ ≤ 1 * (‖W⁻¹ * G‖ + P.rho * ‖W⁻¹ * P.C (s + 1)‖) := by
          refine mul_le_mul (inv_norm_le (R_psd hWs hWW hWu hL hS hr s)) ?_ (norm_nonneg _) zero_le_one
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      _ ≤ ((k + 1 : ℕ) : ℝ) * ‖W⁻¹ * G‖ := by
          have hg := norm_nonneg (W⁻¹ * G)
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hih hr, mul_le_mul_of_nonneg_right hr1 (mul_nonneg
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hg)]

/-- `‖W⁻¹ c_s‖ ≤ (T - s)‖W⁻¹e‖`. -/
lemma c_bound (hr1 : P.rho ≤ 1) : ∀ s, vnorm (W⁻¹ *ᵥ P.c s) ≤ ((P.T - s : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ P.e) := by
  suffices h : ∀ k s, P.T - s = k → vnorm (W⁻¹ *ᵥ P.c s) ≤ ((P.T - s : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ P.e) from
    fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [LQ.c_ge P (by omega), mulVec_zero, hs]
    simp [vnorm]
  | succ k ih =>
    intro s hs
    have hsT : s < P.T := by omega
    have hih := ih (s + 1) (by omega)
    rw [c_eq hWs hWW hWu hsT, l_eq hWs hWW hWu, hs]
    rw [show P.T - (s + 1) = k by omega] at hih
    have hv := vnorm_nonneg (W⁻¹ *ᵥ P.e)
    calc vnorm ((1 + Rn P W s)⁻¹ *ᵥ (P.rho • (W⁻¹ *ᵥ P.c (s + 1)) - W⁻¹ *ᵥ P.e))
        ≤ ‖(1 + Rn P W s)⁻¹‖ * vnorm (P.rho • (W⁻¹ *ᵥ P.c (s + 1)) - W⁻¹ *ᵥ P.e) := mulVec_le _ _
      _ ≤ 1 * (P.rho * vnorm (W⁻¹ *ᵥ P.c (s + 1)) + vnorm (W⁻¹ *ᵥ P.e)) := by
          refine mul_le_mul (inv_norm_le (R_psd hWs hWW hWu hL hS hr s)) ?_ (vnorm_nonneg _) zero_le_one
          refine (vnorm_sub _ _).trans ?_
          rw [vnorm_smul, abs_of_nonneg hr]
      _ ≤ ((k + 1 : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ P.e) := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hih hr, mul_le_mul_of_nonneg_right hr1 (mul_nonneg
            (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hv)]

end Normal

/-! ### The true and plug-in recursions side by side -/

section Pair

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]
variable {P P' : LQ ι π} {W : Matrix ι ι ℝ} (hWs : Wᵀ = W) (hWW : W * W = P.Lam) (hWu : IsUnit W)
  (hLam : P'.Lam = P.Lam) (hT : P'.T = P.T) (hrho : P'.rho = P.rho)
include hWs hWW hWu hLam hT hrho

lemma R_diff_norm (hr : 0 ≤ P.rho) (t : ℕ) : ‖Rn P' W t - Rn P W t‖ ≤
    ‖W⁻¹ * (P'.S t - P.S t) * W⁻¹‖ + P.rho * ‖W⁻¹ * (P'.A (t + 1) - P.A (t + 1)) * W⁻¹‖ := by
  have e : Rn P' W t - Rn P W t = W⁻¹ * (P'.S t - P.S t) * W⁻¹ +
      P.rho • (W⁻¹ * (P'.A (t + 1) - P.A (t + 1)) * W⁻¹) := by
    simp only [Rn, hrho, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

lemma M_diff_zero {s : ℕ} (hs : P.T ≤ s) : ‖W⁻¹ * (P'.A s - P.A s) * W⁻¹‖ = 0 := by
  rw [LQ.A_ge P hs, LQ.A_ge P' (hT ▸ hs), sub_zero, Matrix.mul_zero, Matrix.zero_mul, norm_zero]

lemma M_diff_le (hRp : ∀ t, (Rn P W t).PosSemidef) (hRp' : ∀ t, (Rn P' W t).PosSemidef) {s : ℕ}
    (hs : s < P.T) : ‖W⁻¹ * (P'.A s - P.A s) * W⁻¹‖ ≤ ‖Rn P' W s - Rn P W s‖ := by
  have hWW' : W * W = P'.Lam := hWW.trans hLam.symm
  rw [Matrix.mul_sub, Matrix.sub_mul, M_eq hWs hWW hWu hs, M_eq hWs hWW' hWu (hT ▸ hs),
    sub_sub_sub_cancel_left, norm_sub_rev]
  exact inv_lip (hRp' s) (hRp s)

lemma K_diff_le (hRp : ∀ t, (Rn P W t).PosSemidef) (hRp' : ∀ t, (Rn P' W t).PosSemidef) (t : ℕ) :
    ‖W * (P'.K t - P.K t) * W⁻¹‖ ≤ ‖Rn P' W t - Rn P W t‖ := by
  have hWW' : W * W = P'.Lam := hWW.trans hLam.symm
  rw [Matrix.mul_sub, Matrix.sub_mul, K_eq hWs hWW' hWu, K_eq hWs hWW hWu]
  exact inv_lip (hRp' t) (hRp t)

lemma C_diff_eq (hG : P'.G = P.G) {s : ℕ} (hs : s < P.T) : W⁻¹ * (P'.C s - P.C s) =
    ((1 + Rn P' W s)⁻¹ - (1 + Rn P W s)⁻¹) * (W⁻¹ * P.G s + P.rho • (W⁻¹ * P.C (s + 1))) +
      (1 + Rn P' W s)⁻¹ * (P.rho • (W⁻¹ * (P'.C (s + 1) - P.C (s + 1)))) := by
  have hWW' : W * W = P'.Lam := hWW.trans hLam.symm
  rw [Matrix.mul_sub, C_eq hWs hWW' hWu (hT ▸ hs), C_eq hWs hWW hWu hs, L_eq hWs hWW' hWu, L_eq hWs hWW hWu,
    hG, hrho]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, smul_sub]
  abel

lemma c_diff_eq (he : P'.e = P.e) {s : ℕ} (hs : s < P.T) : W⁻¹ *ᵥ (P'.c s - P.c s) =
    ((1 + Rn P' W s)⁻¹ - (1 + Rn P W s)⁻¹) *ᵥ (P.rho • (W⁻¹ *ᵥ P.c (s + 1)) - W⁻¹ *ᵥ P.e) +
      (1 + Rn P' W s)⁻¹ *ᵥ (P.rho • (W⁻¹ *ᵥ (P'.c (s + 1) - P.c (s + 1)))) := by
  have hWW' : W * W = P'.Lam := hWW.trans hLam.symm
  rw [mulVec_sub, c_eq hWs hWW' hWu (hT ▸ hs), c_eq hWs hWW hWu hs, l_eq hWs hWW' hWu, l_eq hWs hWW hWu,
    he, hrho]
  simp only [sub_mulVec, mulVec_smul, mulVec_sub, smul_sub]
  abel

end Pair

section Steps

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]

/-- A one-step bound in the form `unroll` takes: `‖(X' - X) u + X' (ρ v)‖ ≤ ‖R' - R‖ n + ρ ‖v‖`. -/
lemma step_mat {κ : Type} [Fintype κ] [DecidableEq κ] {R R' : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (hR' : R'.PosSemidef) {ρ n : ℝ} (hρ : 0 ≤ ρ) (u v : Matrix ι κ ℝ) (hu : ‖u‖ ≤ n) :
    ‖((1 + R')⁻¹ - (1 + R)⁻¹) * u + (1 + R')⁻¹ * (ρ • v)‖ ≤ ‖R' - R‖ * n + ρ * ‖v‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (l2_opNorm_mul _ _).trans (mul_le_mul (inv_lip hR' hR) hu (norm_nonneg _) (norm_nonneg _))
  · refine (l2_opNorm_mul _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
    calc ‖(1 + R')⁻¹‖ * (ρ * ‖v‖) ≤ 1 * (ρ * ‖v‖) :=
          mul_le_mul_of_nonneg_right (inv_norm_le hR') (mul_nonneg hρ (norm_nonneg _))
      _ = ρ * ‖v‖ := one_mul _

lemma step_vec {R R' : Matrix ι ι ℝ} (hR : R.PosSemidef) (hR' : R'.PosSemidef) {ρ n : ℝ} (hρ : 0 ≤ ρ)
    (u v : ι → ℝ) (hu : vnorm u ≤ n) :
    vnorm (((1 + R')⁻¹ - (1 + R)⁻¹) *ᵥ u + (1 + R')⁻¹ *ᵥ (ρ • v)) ≤ ‖R' - R‖ * n + ρ * vnorm v := by
  refine (vnorm_add _ _).trans (add_le_add ?_ ?_)
  · exact (mulVec_le _ _).trans (mul_le_mul (inv_lip hR' hR) hu (vnorm_nonneg _) (norm_nonneg _))
  · refine (mulVec_le _ _).trans ?_
    rw [vnorm_smul, abs_of_nonneg hρ]
    calc ‖(1 + R')⁻¹‖ * (ρ * vnorm v) ≤ 1 * (ρ * vnorm v) :=
          mul_le_mul_of_nonneg_right (inv_norm_le hR') (mul_nonneg hρ (vnorm_nonneg _))
      _ = ρ * vnorm v := one_mul _

/-- `(T - (s+1)) x + x = (T - s) x` below the horizon. -/
lemma horizon_step {T s : ℕ} (hs : s < T) (x : ℝ) :
    ((T - (s + 1) : ℕ) : ℝ) * x + x = ((T - s : ℕ) : ℝ) * x := by
  rw [show T - s = (T - (s + 1)) + 1 by omega]; push_cast; ring

end Steps

/-! ### Part 3 -/

theorem stability : Stability := by
  intro ι π _ _ _ _ Q S' W G hL hS hS' hr hr1 hG hWs hWW hWu
  have hLam : (plugIn Q S').Lam = Q.Lam := rfl
  have hT : (plugIn Q S').T = Q.T := rfl
  have hrho : (plugIn Q S').rho = Q.rho := rfl
  have hGG : (plugIn Q S').G = Q.G := rfl
  have he : (plugIn Q S').e = Q.e := rfl
  have hSS : (plugIn Q S').S = S' := rfl
  have hRp := R_psd hWs hWW hWu hL hS hr
  have hRp' := R_psd (P := plugIn Q S') hWs hWW hWu hL hS' hr
  have hRd := fun t => R_diff_norm hWs hWW hWu hLam hT hrho hr t
  rw [hSS] at hRd
  have hMb : ∀ t, ‖W⁻¹ * ((plugIn Q S').A t - Q.A t) * W⁻¹‖ ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * ‖W⁻¹ * (S' (t + k) - Q.S (t + k)) * W⁻¹‖ :=
    unroll hr (fun s hs => M_diff_zero hWs hWW hWu hLam hT hrho hs)
      (fun s hs => (M_diff_le hWs hWW hWu hLam hT hrho hRp hRp' hs).trans (hRd s))
  refine ⟨hMb, fun t _ => (K_diff_le hWs hWW hWu hLam hT hrho hRp hRp' t).trans (hRd t), fun t ht => ?_,
    fun t ht => ?_⟩
  · -- `L`
    have hCb := C_bound hWs hWW hWu hL hS hr hG hr1
    have hu := unroll (a := fun s => ‖W⁻¹ * ((plugIn Q S').C s - Q.C s)‖)
      (b := fun s => (‖W⁻¹ * (S' s - Q.S s) * W⁻¹‖ +
        Q.rho * ‖W⁻¹ * ((plugIn Q S').A (s + 1) - Q.A (s + 1)) * W⁻¹‖) * ‖W⁻¹ * G‖ * ((Q.T - s : ℕ) : ℝ)) hr
      (fun s hs => by
        show ‖_‖ = 0
        rw [LQ.C_ge Q hs, LQ.C_ge (plugIn Q S') hs, sub_zero, Matrix.mul_zero, norm_zero])
      (fun s hs => by
        show ‖_‖ ≤ _
        rw [C_diff_eq hWs hWW hWu hLam hT hrho hGG hs]
        refine (step_mat (hRp s) (hRp' s) hr _ _ (n := ((Q.T - s : ℕ) : ℝ) * ‖W⁻¹ * G‖) ?_).trans ?_
        · refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hG, ← horizon_step hs]
          have := hCb (s + 1)
          have := norm_nonneg (W⁻¹ * Q.C (s + 1))
          nlinarith
        · have := hRd s
          have := norm_nonneg (W⁻¹ * G)
          have : (0 : ℝ) ≤ ((Q.T - s : ℕ) : ℝ) := Nat.cast_nonneg _
          have h := mul_le_mul_of_nonneg_right (hRd s) (mul_nonneg this (norm_nonneg (W⁻¹ * G)))
          linarith) t
    have haL : ‖W⁻¹ * ((plugIn Q S').C t - Q.C t)‖ = ‖W * ((plugIn Q S').L t - Q.L t)‖ := by
      rw [Matrix.mul_sub, Matrix.mul_sub, C_eq hWs hWW hWu (P := plugIn Q S') ht, C_eq hWs hWW hWu ht]
    rw [← haL]
    exact hu.trans (le_of_eq (Finset.sum_congr rfl fun k _ => by ring))
  · -- `l`
    have hcb := c_bound hWs hWW hWu hL hS hr hr1
    have hu := unroll (a := fun s => vnorm (W⁻¹ *ᵥ ((plugIn Q S').c s - Q.c s)))
      (b := fun s => (‖W⁻¹ * (S' s - Q.S s) * W⁻¹‖ +
        Q.rho * ‖W⁻¹ * ((plugIn Q S').A (s + 1) - Q.A (s + 1)) * W⁻¹‖) * vnorm (W⁻¹ *ᵥ Q.e) *
          ((Q.T - s : ℕ) : ℝ)) hr
      (fun s hs => by
        show vnorm _ = 0
        rw [LQ.c_ge Q hs, LQ.c_ge (plugIn Q S') hs, sub_zero, mulVec_zero]
        simp [vnorm])
      (fun s hs => by
        show vnorm _ ≤ _
        rw [c_diff_eq hWs hWW hWu hLam hT hrho he hs]
        refine (step_vec (hRp s) (hRp' s) hr _ _ (n := ((Q.T - s : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ Q.e)) ?_).trans ?_
        · refine (vnorm_sub _ _).trans ?_
          rw [vnorm_smul, abs_of_nonneg hr, ← horizon_step hs]
          have := hcb (s + 1)
          have := vnorm_nonneg (W⁻¹ *ᵥ Q.c (s + 1))
          nlinarith
        · have : (0 : ℝ) ≤ ((Q.T - s : ℕ) : ℝ) := Nat.cast_nonneg _
          have h := mul_le_mul_of_nonneg_right (hRd s) (mul_nonneg this (vnorm_nonneg (W⁻¹ *ᵥ Q.e)))
          linarith) t
    have hal : vnorm (W⁻¹ *ᵥ ((plugIn Q S').c t - Q.c t)) = vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) := by
      rw [mulVec_sub, mulVec_sub, c_eq hWs hWW hWu (P := plugIn Q S') ht, c_eq hWs hWW hWu ht]
    rw [← hal]
    exact hu.trans (le_of_eq (Finset.sum_congr rfl fun k _ => by ring))

/-! ### Part 2 -/

theorem pathwise : Pathwise := by
  intro ι π _ _ _ _ Q S' W hWs hWW hWu t xm m
  have hWi := wiw hWs hWW hWu
  have hX : W⁻¹ * Q.D t * W⁻¹ = 1 + Rn Q W t := by
    rw [D_eq hWs hWW hWu]
    simp only [Matrix.mul_assoc, wwi hWs hWW hWu, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hWi, Matrix.one_mul]
  have hdiff : (plugIn Q S').policy t xm m - Q.policy t xm m = ((plugIn Q S').K t - Q.K t) *ᵥ xm +
      ((plugIn Q S').L t - Q.L t) *ᵥ m + ((plugIn Q S').l t - Q.l t) := by
    simp only [LQ.policy, sub_mulVec]; abel
  refine ⟨hdiff, fun e => ?_, ?_, ?_⟩
  · have e1 : e ⬝ᵥ (Q.D t *ᵥ e) = (W *ᵥ e) ⬝ᵥ ((1 + Rn Q W t) *ᵥ (W *ᵥ e)) := by
      rw [D_eq hWs hWW hWu, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hWs]
    rw [e1, hX]
    refine (dot_le _ _).trans ?_
    calc vnorm (W *ᵥ e) * vnorm ((1 + Rn Q W t) *ᵥ (W *ᵥ e)) ≤
        vnorm (W *ᵥ e) * (‖1 + Rn Q W t‖ * vnorm (W *ᵥ e)) :=
          mul_le_mul_of_nonneg_left (mulVec_le _ _) (vnorm_nonneg _)
      _ = _ := by ring
  · rw [hdiff, mulVec_add, mulVec_add]
    have e2 : W *ᵥ (((plugIn Q S').K t - Q.K t) *ᵥ xm) =
        (W * ((plugIn Q S').K t - Q.K t) * W⁻¹) *ᵥ (W *ᵥ xm) := by
      rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hWi, Matrix.mul_one]
    rw [e2, mulVec_mulVec m W]
    exact (vnorm_add _ _).trans (add_le_add ((vnorm_add _ _).trans
      (add_le_add (mulVec_le _ _) (mulVec_le _ _))) le_rfl)
  · rw [hX]
    show ‖1 + Rn Q W t‖ ≤ 1 + ‖Rn Q W t‖
    have := norm_add_le (1 : Matrix ι ι ℝ) (Rn Q W t)
    linarith [one_norm_le (κ := ι)]

/-! ### Part 1 -/

theorem oneStep : OneStep := by
  intro ι π _ _ _ _ Q hS E hE
  obtain ⟨q, hq0, hq⟩ := bellmanVerif ι π Q hS E hE
  refine ⟨q, hq0, fun t ht xm m x => ?_⟩
  have hJ := (hq t ht xm m).2
  have hΛsym := transpose_of_psd hS.1
  have hDpd := LQ.D_pd hS t
  have hDsym := transpose_of_psd hDpd.posSemidef
  have hobj : ∀ y, Q.obj E q t xm m y =
      bellObj Q.Lam (Q.S t) (Q.A (t + 1)) (Q.G t) (Q.C (t + 1)) (Q.c (t + 1)) Q.e Q.rho
        (E t (q (t + 1)) m) xm m y := fun y => by
    rw [LQ.obj, exp_J Q hE, bellObj]
  set b := Q.Lam *ᵥ xm + ((Q.G t + Q.rho • Q.C (t + 1)) *ᵥ m + (Q.rho • Q.c (t + 1) - Q.e))
  have hpol : Q.policy t xm m = (Q.D t)⁻¹ *ᵥ b := by
    simp only [b, LQ.policy, LQ.K, LQ.L, LQ.l, ← mulVec_mulVec, mulVec_add, add_assoc]
  have hDb : Q.D t *ᵥ Q.policy t xm m = b := by
    rw [hpol, mulVec_mulVec, mul_nonsing_inv _ (pd_unit hDpd), one_mulVec]
  have hgap := quad_gap hDsym hDb x
  rw [← hJ, hobj, hobj, bellObj_eq _ _ _ hΛsym, bellObj_eq _ _ _ hΛsym]
  change -(1 / 2) * (x ⬝ᵥ (Q.D t *ᵥ x)) + x ⬝ᵥ b + _ =
    -(1 / 2) * (Q.policy t xm m ⬝ᵥ (Q.D t *ᵥ Q.policy t xm m)) + Q.policy t xm m ⬝ᵥ b + _ - _
  linarith

/-! ### Part 4 -/

theorem guarantee : Guarantee := by
  intro ι π _ _ _ _ Q S' W G r hL hS hS' hr hr1 hG hWs hWW hWu hdr
  obtain ⟨h1, h2, h3, h4⟩ := stability ι π Q S' W G hL hS hS' hr hr1 hG hWs hWW hWu
  have hM : ∀ t, ‖W⁻¹ * ((plugIn Q S').A t - Q.A t) * W⁻¹‖ ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * r := fun t =>
    (h1 t).trans (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hdr _) (pow_nonneg hr k))
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hdr 0)
  have hterm : ∀ s, ‖W⁻¹ * (S' s - Q.S s) * W⁻¹‖ + Q.rho * ‖W⁻¹ * ((plugIn Q S').A (s + 1) - Q.A (s + 1)) * W⁻¹‖ ≤
      r + Q.rho * ∑ j ∈ Finset.range (Q.T - (s + 1)), Q.rho ^ j * r := fun s =>
    add_le_add (hdr s) (mul_le_mul_of_nonneg_left (hM (s + 1)) hr)
  refine ⟨hM, fun t ht => (h2 t ht).trans (hterm t), fun t ht => (h3 t ht).trans ?_,
    fun t ht => (h4 t ht).trans ?_⟩
  · refine Finset.sum_le_sum fun k _ => ?_
    have := hterm (t + k)
    gcongr
  · refine Finset.sum_le_sum fun k _ => ?_
    have := hterm (t + k)
    have := vnorm_nonneg (W⁻¹ *ᵥ Q.e)
    gcongr

/-- Claim 033, parts 1-4. -/
theorem proof : Standalone.M5PlugInValueLoss.statement := ⟨oneStep, pathwise, stability, guarantee⟩

end

end Novel.M5PlugInValueLossProof

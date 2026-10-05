import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Novel.M6QuarterlyBandStaticCeilingProof
import Standalone.M7LearningBandTransfer

/-!
# Claim 100: proof

Part 1: `instance_` builds M7's finite-law variant as an M6 instance; claim 029's proofs, read for
`Σ(t, z)`, give 1b-1d; `decouple` is the diagonal case. Part 2: the filter's information form and
Woodbury's identity give `learning`, `drift` and `driftOne`; claim 029's brackets and first-order
equalities give `tiltSign` and `landing`; and `eventual` bounds the target's moves uniformly over
histories by limits of the filter.
-/

namespace Novel.M7LearningBandTransferProof

open Matrix Filter Topology Standalone.M6QuarterlyBandStaticCeiling Standalone.M7LearningBandTransfer
open Novel.M6QuarterlyBandStaticCeilingProof

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Matrix facts -/

section Mat

variable {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

lemma ct (B : Matrix κ μ ℝ) : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B

lemma tr_pd {A : Matrix κ κ ℝ} (h : A.PosDef) : Aᵀ = A := by rw [← ct]; exact h.1.eq

lemma tr_psd {A : Matrix κ κ ℝ} (h : A.PosSemidef) : Aᵀ = A := by rw [← ct]; exact h.1.eq

lemma unit_pd {A : Matrix κ κ ℝ} (h : A.PosDef) : IsUnit A :=
  (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h.det_pos.ne')

lemma det_pd {A : Matrix κ κ ℝ} (h : A.PosDef) : IsUnit A.det := isUnit_iff_ne_zero.mpr h.det_pos.ne'

lemma inv_tr {A : Matrix κ κ ℝ} (h : Aᵀ = A) : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, h]

lemma tendsto_minv {α : Type} {l : Filter α} {f : α → Matrix κ κ ℝ} {a : Matrix κ κ ℝ}
    (hf : Tendsto f l (𝓝 a)) (ha : IsUnit a.det) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹) := by
  have hc : ContinuousAt Inv.inv a := continuousAt_matrix_inv a (by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero)
  exact hc.tendsto.comp hf

lemma tendsto_mmul {α ν : Type} [Fintype ν] {l : Filter α} {f : α → Matrix κ μ ℝ} {g : α → Matrix μ ν ℝ}
    {a : Matrix κ μ ℝ} {b : Matrix μ ν ℝ} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => f x * g x) l (𝓝 (a * b)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

/-- `(A B A')ᵢᵢ = Aᵢ ⬝ B Aᵢ`. -/
lemma sandwich_diag {ι : Type} [Fintype ι] (A : Matrix ι κ ℝ) (B : Matrix κ κ ℝ) (i : ι) :
    (A * B * Aᵀ) i i = A i ⬝ᵥ (B *ᵥ A i) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- For `B ≻ 0`, `(A B A')ᵢᵢ > 0` iff the row `Aᵢ` is nonzero, and it is zero otherwise. -/
lemma sandwich_pos {ι : Type} [Fintype ι] (A : Matrix ι κ ℝ) {B : Matrix κ κ ℝ} (hB : B.PosDef)
    (i : ι) : (0 < (A * B * Aᵀ) i i ↔ A i ≠ 0) ∧ (A i = 0 → (A * B * Aᵀ) i i = 0) := by
  rw [sandwich_diag]
  refine ⟨⟨fun h h0 => by simp [h0] at h, fun h => ?_⟩, fun h0 => by simp [h0]⟩
  simpa using hB.dotProduct_mulVec_pos h

end Mat

/-! ### The filter -/

section Filter

variable {κ ο ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ι]
  [DecidableEq ι] {F : Filt κ ο ι} (hF : F.Good)
include hF

lemma P0_pd : F.P0.PosDef := hF.1
lemma R_pd : F.R.PosDef := hF.2.1
lemma Sr_pd : F.Sr.PosDef := hF.2.2.2.1
lemma gam_pos : 0 < F.gamma := hF.2.2.2.2

lemma H_inj : Function.Injective F.H.mulVec := fun u v h =>
  sub_eq_zero.mp (hF.2.2.1 _ (by rw [mulVec_sub, h, sub_self]))

lemma J_pd : F.J.PosDef := by
  have := (R_pd hF).inv.conjTranspose_mul_mul_same (H_inj hF)
  rwa [ct] at this

/-- `Q_t = P₀⁻¹ + t J`, the information. -/
lemma Q_pd (t : ℕ) : (F.P0⁻¹ + (t : ℝ) • F.J).PosDef :=
  (P0_pd hF).inv.add_posSemidef ((J_pd hF).posSemidef.smul (Nat.cast_nonneg t))

/-- The covariance is the inverse information. -/
lemma P_eq : ∀ t, F.P t = (F.P0⁻¹ + (t : ℝ) • F.J)⁻¹
  | 0 => by
    simp only [Filt.P, Nat.cast_zero, zero_smul, add_zero]
    rw [nonsing_inv_nonsing_inv _ (det_pd (P0_pd hF))]
  | t + 1 => by
    have hA := Q_pd hF t
    set A := F.P0⁻¹ + (t : ℝ) • F.J
    have hQ : F.P0⁻¹ + ((t + 1 : ℕ) : ℝ) • F.J = A + F.Hᵀ * F.R⁻¹ * F.H := by
      simp only [A, Filt.J]; push_cast; rw [add_smul, one_smul, add_assoc]
    have hAi : IsUnit A⁻¹ := unit_pd hA.inv
    have hW := add_mul_mul_inv_eq_sub (A := A) (U := F.Hᵀ) (C := F.R⁻¹) (V := F.H) (unit_pd hA)
      (unit_pd (R_pd hF).inv) (by
        rw [nonsing_inv_nonsing_inv _ (det_pd (R_pd hF)), add_comm]
        have := PosDef.posSemidef_add (hA.inv.posSemidef.mul_mul_conjTranspose_same F.H) (R_pd hF)
        rw [ct] at this
        exact unit_pd this)
    rw [hQ, hW, nonsing_inv_nonsing_inv _ (det_pd (R_pd hF)), add_comm F.R, Filt.P, P_eq t]

lemma P_pd (t : ℕ) : (F.P t).PosDef := by rw [P_eq hF]; exact (Q_pd hF t).inv

lemma P_inv (t : ℕ) : (F.P t)⁻¹ = F.P0⁻¹ + (t : ℝ) • F.J := by
  rw [P_eq hF, nonsing_inv_nonsing_inv _ (det_pd (Q_pd hF t))]

lemma P_sym (t : ℕ) : (F.P t)ᵀ = F.P t := tr_pd (P_pd hF t)

/-- `S_t = H P_t H' + R`. -/
lemma S_pd (t : ℕ) : (F.H * F.P t * F.Hᵀ + F.R).PosDef := by
  have := PosDef.posSemidef_add ((P_pd hF t).posSemidef.mul_mul_conjTranspose_same F.H) (R_pd hF)
  rwa [ct] at this

lemma V_eq (t : ℕ) : F.V t = F.P t * F.Hᵀ * (F.H * F.P t * F.Hᵀ + F.R)⁻¹ * F.H * F.P t := by
  simp only [Filt.V, Filt.P, sub_sub_cancel]

lemma V_gain (t : ℕ) : F.V t = F.gain t * (F.H * F.P t * F.Hᵀ + F.R) * (F.gain t)ᵀ := by
  have hS := S_pd hF t
  rw [V_eq hF, Filt.gain, transpose_mul, transpose_mul, inv_tr (tr_pd hS), transpose_transpose,
    P_sym hF]
  have hS2 : IsUnit (F.H * (F.P t * F.Hᵀ) + F.R).det := by rw [← Matrix.mul_assoc]; exact det_pd hS
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hS2]

lemma V_pd (t : ℕ) : (F.V t).PosDef := by
  have hP := P_pd hF t
  have hinj : Function.Injective (F.H * F.P t).mulVec := by
    intro u v h
    rw [← mulVec_mulVec, ← mulVec_mulVec] at h
    have h1 := H_inj hF h
    by_contra hne
    have := hP.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    rw [mulVec_sub, h1, sub_self, dotProduct_zero] at this
    exact lt_irrefl _ this
  have := (S_pd hF t).inv.conjTranspose_mul_mul_same hinj
  rw [ct, transpose_mul, P_sym hF] at this
  rw [V_eq hF]
  simpa only [Matrix.mul_assoc] using this

/-- `V_t = P_t J P_{t+1}`. -/
lemma V_PJP (t : ℕ) : F.V t = F.P t * F.J * F.P (t + 1) := by
  have hJ : F.J = (F.P (t + 1))⁻¹ - (F.P t)⁻¹ := by
    rw [P_inv hF, P_inv hF]; push_cast; rw [add_smul, one_smul]; abel
  rw [hJ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul _ (det_pd (P_pd hF _)),
    mul_nonsing_inv _ (det_pd (P_pd hF _)), Matrix.mul_one, Matrix.one_mul, Filt.V]

lemma Sig_pd (t : ℕ) : (F.Sig t).PosDef := by
  have := PosDef.posSemidef_add ((P_pd hF t).posSemidef.mul_mul_conjTranspose_same F.G) (Sr_pd hF)
  rwa [ct] at this

lemma P_sym' (t : ℕ) : (F.Sig t)ᵀ = F.Sig t := tr_pd (Sig_pd hF t)

lemma Sig_diff (t : ℕ) : F.Sig t - F.Sig (t + 1) = F.G * F.V t * F.Gᵀ := by
  simp only [Filt.Sig, Filt.V, Matrix.mul_sub, Matrix.sub_mul]; abel

/-- `Σ_{t+1}⁻¹ - Σ_t⁻¹ = Σ_{t+1}⁻¹ (G V_t G') Σ_t⁻¹`. -/
lemma br_eq (t : ℕ) : (F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹ =
    (F.Sig (t + 1))⁻¹ * (F.G * F.V t * F.Gᵀ) * (F.Sig t)⁻¹ := by
  rw [← Sig_diff hF, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, mul_nonsing_inv _ (det_pd (Sig_pd hF t)),
    Matrix.mul_one, nonsing_inv_mul _ (det_pd (Sig_pd hF _)), Matrix.one_mul]

lemma br_psd (t : ℕ) : ((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹).PosSemidef := by
  have hA := Sig_pd hF (t + 1)
  have hV := V_pd hF t
  set A := F.Sig (t + 1)
  have hW := add_mul_mul_inv_eq_sub (A := A) (U := F.G) (C := F.V t) (V := F.Gᵀ) (unit_pd hA)
    (unit_pd hV) (by
      have := hV.inv.add_posSemidef (hA.inv.posSemidef.conjTranspose_mul_mul_same F.G)
      rw [ct] at this
      exact unit_pd this)
  have hS : F.Sig t = A + F.G * F.V t * F.Gᵀ := by rw [← Sig_diff hF]; abel
  rw [hS, hW, sub_sub_cancel]
  have := ((hV.inv.add_posSemidef (hA.inv.posSemidef.conjTranspose_mul_mul_same F.G)).inv.posSemidef
    |>.conjTranspose_mul_mul_same (F.Gᵀ * A⁻¹))
  rw [ct, ct, transpose_mul, transpose_transpose, inv_tr (tr_pd hA)] at this
  simpa only [Matrix.mul_assoc] using this

/-! #### Limits -/

lemma tP_eq {t : ℕ} (ht : 1 ≤ t) : (t : ℝ) • F.P t = ((1 / (t : ℝ)) • F.P0⁻¹ + F.J)⁻¹ := by
  have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hQ : F.P0⁻¹ + (t : ℝ) • F.J = (t : ℝ) • ((1 / (t : ℝ)) • F.P0⁻¹ + F.J) := by
    rw [smul_add, smul_smul, mul_one_div_cancel ht0, one_smul]
  rw [P_eq hF]
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [Matrix.smul_mul, ← Matrix.mul_smul, ← hQ, nonsing_inv_mul _ (det_pd (Q_pd hF t))]

lemma tP_lim : Tendsto (fun t : ℕ => (t : ℝ) • F.P t) atTop (𝓝 F.J⁻¹) := by
  have h1 : Tendsto (fun t : ℕ => (1 / (t : ℝ)) • F.P0⁻¹ + F.J) atTop (𝓝 F.J) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const F.P0⁻¹).add_const F.J
    simpa using this
  refine (tendsto_minv h1 (det_pd (J_pd hF))).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact (tP_eq hF ht).symm

lemma P_lim : Tendsto F.P atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).smul (tP_lim hF)
  rw [zero_smul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [smul_smul, one_div_mul_cancel ht0, one_smul]

lemma Sig_lim : Tendsto F.Sig atTop (𝓝 F.Sr) := by
  have hc : Continuous (fun X : Matrix κ κ ℝ => F.G * X * F.Gᵀ + F.Sr) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const
  have := (hc.tendsto 0).comp (P_lim hF)
  have e : F.Sig = fun t => F.G * F.P t * F.Gᵀ + F.Sr := rfl
  rw [e]
  simpa [Function.comp_def] using this

lemma V_lim : Tendsto (fun t : ℕ => ((t : ℝ) * (t + 1)) • F.V t) atTop (𝓝 F.J⁻¹) := by
  have e : ∀ t : ℕ, ((t : ℝ) * (t + 1)) • F.V t =
      ((t : ℝ) • F.P t) * F.J * (((t + 1 : ℕ) : ℝ) • F.P (t + 1)) := by
    intro t
    rw [V_PJP hF, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    push_cast; ring_nf
  have h2 : Tendsto (fun t : ℕ => ((t + 1 : ℕ) : ℝ) • F.P (t + 1)) atTop (𝓝 F.J⁻¹) :=
    (tP_lim hF).comp (tendsto_add_atTop_nat 1)
  have := tendsto_mmul (tendsto_mmul (tP_lim hF) (tendsto_const_nhds (x := F.J))) h2
  rw [nonsing_inv_mul _ (det_pd (J_pd hF)), Matrix.one_mul] at this
  simpa only [e] using this

lemma br_lim : Tendsto (fun t : ℕ => ((t : ℝ) * (t + 1)) • ((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹)) atTop
    (𝓝 (F.Sr⁻¹ * F.G * F.J⁻¹ * F.Gᵀ * F.Sr⁻¹)) := by
  have e : ∀ t : ℕ, ((t : ℝ) * (t + 1)) • ((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹) =
      (F.Sig (t + 1))⁻¹ * F.G * (((t : ℝ) * (t + 1)) • F.V t) * F.Gᵀ * (F.Sig t)⁻¹ := by
    intro t
    rw [br_eq hF]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hS := tendsto_minv (Sig_lim hF) (det_pd (Sr_pd hF))
  have hS1 := hS.comp (tendsto_add_atTop_nat 1)
  have := tendsto_mmul (tendsto_mmul (tendsto_mmul (tendsto_mmul hS1 (tendsto_const_nhds (x := F.G)))
    (V_lim hF)) (tendsto_const_nhds (x := F.Gᵀ))) hS
  simpa only [e, Function.comp_def] using this

/-! #### The mean -/

omit hF in
lemma meanFrom_append (y : ο → ℝ) : ∀ (zs : List (ο → ℝ)) (t : ℕ) (m : κ → ℝ),
    F.meanFrom t m (zs ++ [y]) = F.step (t + zs.length) (F.meanFrom t m zs) y
  | [], t, m => by simp [Filt.meanFrom]
  | w :: ws, t, m => by
    simp only [List.cons_append, Filt.meanFrom, List.length_cons]
    rw [meanFrom_append y ws (t + 1)]
    congr 1; omega

omit hF in
lemma mean_append (z : List (ο → ℝ)) (y : ο → ℝ) :
    F.mean (z ++ [y]) = F.step z.length (F.mean z) y := by
  rw [Filt.mean, meanFrom_append, zero_add]; rfl

end Filter

/-! ### Part 2a and 2b -/

theorem learning : Learning := by
  intro κ ο ι _ _ _ _ _ _ F hF
  have hSd : ∀ t, (F.Sig t - F.Sig (t + 1)).PosSemidef := fun t => by
    have := (V_pd hF t).posSemidef.mul_mul_conjTranspose_same F.G
    rwa [ct, ← Sig_diff hF] at this
  have hg := gam_pos hF
  have hdp : ∀ t i, 0 < F.gamma * F.Sig t i i := fun t i => mul_pos hg ((Sig_pd hF t).diag_pos)
  have hanti : ∀ i, Antitone (fun t => F.gamma * F.Sig t i i) := fun i =>
    antitone_nat_of_succ_le fun t => by
      have := (hSd t).diag_nonneg (i := i)
      rw [Matrix.sub_apply] at this
      exact mul_le_mul_of_nonneg_left (by linarith) hg.le
  have hlim : ∀ i, Tendsto (fun t => F.gamma * F.Sig t i i) atTop (𝓝 (F.gamma * F.Sr i i)) := fun i =>
    (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (Sig_lim hF) i) i).const_mul F.gamma
  refine ⟨fun t => ⟨P_pd hF t, P_inv hF t⟩, fun t => (V_pd hF t).posSemidef, P_lim hF, hSd,
    Sig_lim hF, fun i => ⟨hanti i, hlim i, fun k hk => ⟨?_, ?_⟩⟩⟩
  · exact monotone_nat_of_le_succ fun t =>
      div_le_div_of_nonneg_left hk (hdp (t + 1) i) (hanti i (Nat.le_succ t))
  · exact tendsto_const_nhds.div (hlim i) (mul_pos hg (Sr_pd hF).diag_pos).ne'

theorem drift : Drift := by
  intro κ ο ι _ _ _ _ _ _ F hF
  refine ⟨fun z y => ⟨mean_append z y, ?_⟩, br_psd hF, fun t => ⟨V_gain hF t, V_pd hF t⟩,
    fun t i => ?_, V_lim hF, br_lim hF⟩
  · simp only [Filt.xstar, Filt.mu]
    rw [← smul_sub, ← smul_add]
    congr 1
    simp only [mulVec_sub, sub_mulVec]
    abel
  · rw [← sub_pos, ← Matrix.sub_apply, Sig_diff hF]
    exact (sandwich_pos F.G (V_pd hF t) i).1

lemma inv11 {A : Matrix (Fin 1) (Fin 1) ℝ} (h : IsUnit A.det) : A⁻¹ 0 0 = 1 / A 0 0 := by
  have e := congrFun (congrFun (mul_nonsing_inv A h) 0) 0
  simp only [mul_apply, Fin.sum_univ_one, one_apply_eq] at e
  have h0 : A 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at e; exact zero_ne_one e
  field_simp; linarith

theorem driftOne : DriftOne := by
  intro κ ο _ _ _ _ F hF z
  set t := z.length
  have hg := gam_pos hF
  have hA := Sig_pd hF (t + 1)
  have hB := Sig_pd hF t
  have hA0 : 0 < F.Sig (t + 1) 0 0 := hA.diag_pos
  have hB0 : 0 < F.Sig t 0 0 := hB.diag_pos
  have hd := fun i => (sandwich_pos F.G (V_pd hF t) i)
  have hdiff : F.Sig t 0 0 - F.Sig (t + 1) 0 0 = (F.G * F.V t * F.Gᵀ) 0 0 := by
    rw [← Matrix.sub_apply, Sig_diff hF]
  refine ⟨?_, fun hG => ?_, fun hG => ?_⟩
  · simp only [mulVec, dotProduct, Fin.sum_univ_one, Matrix.sub_apply, inv11 (det_pd hA), inv11 (det_pd hB)]
    ring
  · have hlt : F.Sig (t + 1) 0 0 < F.Sig t 0 0 := by
      have := (hd 0).1.mpr hG; linarith
    have hc : 0 < 1 / F.gamma * (1 / F.Sig (t + 1) 0 0 - 1 / F.Sig t 0 0) :=
      mul_pos (by positivity) (sub_pos.mpr (one_div_lt_one_div_of_lt hA0 hlt))
    have e : 1 / F.gamma * ((1 / F.Sig (t + 1) 0 0 - 1 / F.Sig t 0 0) * F.mu z 0) =
        1 / F.gamma * (1 / F.Sig (t + 1) 0 0 - 1 / F.Sig t 0 0) * F.mu z 0 := by ring
    refine ⟨hlt, ?_, ?_⟩ <;> rw [e]
    · exact mul_pos_iff_of_pos_left hc
    · constructor
      · intro h; by_contra h'; have := not_lt.mp h'; nlinarith
      · intro h; nlinarith
  · have heq : F.Sig (t + 1) 0 0 = F.Sig t 0 0 := by
      have := (hd 0).2 hG; linarith
    refine ⟨heq, ?_⟩
    rw [heq, sub_self, zero_mul, mul_zero]

/-! ### Part 1a: the instance -/

section Inst

variable {κ ο ζ Θ S : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ζ]
  [Fintype Θ] [Fintype S] [DecidableEq S] {n : ℕ} {M : M7 κ ο ζ Θ S n}

omit [DecidableEq S] in
lemma hist_succ {T : ℕ} (a : Θ) (w : Fin T → S) {t : ℕ} (ht : t < T) :
    M.hist a w (t + 1) = M.hist a w t ++ [M.obs a (w ⟨t, ht⟩)] := by
  rw [M7.hist, dite_eq_left ht]

omit [DecidableEq S] in
lemma hist_length {T : ℕ} (a : Θ) (w : Fin T → S) : ∀ t, (M.hist a w t).length = min t T
  | 0 => by simp [M7.hist]
  | t + 1 => by
    rw [M7.hist]
    split_ifs with h
    · rw [List.length_append, hist_length a w t]; simp; omega
    · rw [hist_length a w t]; omega

variable (hM : M.Setting)
include hM

lemma joint_nonneg {T : ℕ} (a : Θ) (w : Fin T → S) : 0 ≤ M.joint a w :=
  mul_nonneg (hM.2.2.2.2.2.1 a) (Finset.prod_nonneg fun j _ => hM.2.2.2.2.2.2.2.1 (w j))

lemma sum_joint (T : ℕ) : ∑ a, ∑ w : Fin T → S, M.joint a w = 1 := by
  simp only [M7.joint, ← Finset.mul_sum]
  have : ∑ w : Fin T → S, ∏ j, M.psh (w j) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin T) s => M.psh s), hM.2.2.2.2.2.2.2.2.1, Finset.prod_const_one]
  rw [this]; simp only [mul_one]; exact hM.2.2.2.2.2.2.1

lemma marg_nonneg (T t : ℕ) (z : List (ο → ℝ)) : 0 ≤ M.marg T t z := by
  classical
  unfold M7.marg
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun w _ => by
    split_ifs
    · exact joint_nonneg hM a w
    · exact le_refl 0

omit hM in
lemma fin_sum_ite {T k : ℕ} (hk : k ≤ T) (c : ℝ) :
    ∑ s : Fin (T + 1), (if (s : ℕ) = k then c else 0) = c := by
  rw [Finset.sum_eq_single ⟨k, by omega⟩]
  · simp
  · intro b _ hb; rw [ite_eq_right]; exact fun h => hb (Fin.ext h)
  · simp

lemma prob_nonneg (T t : ℕ) (z : List (ο → ℝ)) (ω : M7.Out Θ S T) : 0 ≤ (M.inst T).prob t z ω := by
  classical
  simp only [M7.inst]
  split_ifs with h1 h2 h3
  · exact div_nonneg (joint_nonneg hM _ _) h1.2.le
  · exact le_refl 0
  · exact joint_nonneg hM _ _
  · exact le_refl 0

lemma prob_sum (T t : ℕ) (z : List (ο → ℝ)) : ∑ ω, (M.inst T).prob t z ω = 1 := by
  classical
  simp only [M7.inst]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  split_ifs with h1
  · have e : ∀ (s : Fin (T + 1)) (a : Θ) (w : Fin T → S),
        (if (s : ℕ) = t + 1 ∧ M.hist a w t = z then M.joint a w / M.marg T t z else 0) =
          if (s : ℕ) = t + 1 then (if M.hist a w t = z then M.joint a w else 0) / M.marg T t z else 0 := by
      intro s a w; split_ifs <;> simp_all
    simp_rw [e]
    have e2 : ∀ s : Fin (T + 1), (∑ a, ∑ w : Fin T → S,
        if (s : ℕ) = t + 1 then (if M.hist a w t = z then M.joint a w else 0) / M.marg T t z else 0) =
        if (s : ℕ) = t + 1 then M.marg T t z / M.marg T t z else 0 := by
      intro s
      split_ifs
      · rw [M7.marg, Finset.sum_div]; exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_div]
      · simp
    simp_rw [e2]
    rw [fin_sum_ite h1.1, div_self h1.2.ne']
  · have e2 : ∀ s : Fin (T + 1), (∑ a, ∑ w : Fin T → S,
        if (s : ℕ) = 0 then M.joint a w else 0) = if (s : ℕ) = 0 then 1 else 0 := by
      intro s
      split_ifs
      · exact sum_joint hM T
      · simp
    simp_rw [e2]
    exact fin_sum_ite (Nat.zero_le _) 1

lemma inst_setting {T : ℕ} (hT : 1 ≤ T) : Setting (M.inst T) := by
  have ⟨hF, hb0, hb1, hk, hc, _, _, _, _, hg⟩ := hM
  refine ⟨hT, fun t _ => P_sym' hF t, fun t _ v hv => ?_, gam_pos hF, hb0, hb1, hk, hc,
    fun t z ω => prob_nonneg hM T t z ω, fun t z => prob_sum hM T t z, fun ω i => ?_⟩
  · have h := (Sig_pd hF t).dotProduct_mulVec_pos hv
    rw [star_trivial] at h
    exact h
  · simp only [M7.inst]
    split_ifs
    · exact hg _ i
    · exact one_pos

/-- From a history of positive mass, a positive-mass outcome is `(t + 1, a, w)` with history `z`. -/
lemma pos_out {T t : ℕ} {z : List (ο → ℝ)} (ht : t + 1 ≤ T) (hz : 0 < M.marg T t z)
    {ω : M7.Out Θ S T} (hω : 0 < (M.inst T).prob t z ω) :
    (ω.1 : ℕ) = t + 1 ∧ M.hist ω.2.1 ω.2.2 t = z := by
  classical
  simp only [M7.inst, ite_eq_left (And.intro ht hz)] at hω
  split_ifs at hω with h
  · exact h
  · exact absurd hω (lt_irrefl 0)

lemma pos_next {T t : ℕ} {z : List (ο → ℝ)} (ht : t + 1 ≤ T) (hz : 0 < M.marg T t z)
    {ω : M7.Out Θ S T} (hω : 0 < (M.inst T).prob t z ω) :
    (M.inst T).next ω = z ++ [M.obs ω.2.1 (ω.2.2 ⟨t, by omega⟩)] ∧
      (M.inst T).gross ω = M.gross (M.obs ω.2.1 (ω.2.2 ⟨t, by omega⟩)) := by
  obtain ⟨h1, h2⟩ := pos_out hM ht hz hω
  refine ⟨?_, ?_⟩
  · show M.hist ω.2.1 ω.2.2 ω.1 = _
    rw [h1, hist_succ _ _ (by omega), h2]
  · show (if h : 0 < (ω.1 : ℕ) then _ else _) = _
    rw [dite_eq_left (by omega)]
    have e : ∀ (i j : Fin T), (i : ℕ) = j → ω.2.2 i = ω.2.2 j := fun i j h => by rw [Fin.ext h]
    exact congrArg _ (congrArg _ (e _ _ (show (ω.1 : ℕ) - 1 = t by omega)))

end Inst

theorem instance_ : Instance := by
  intro κ ο ζ Θ S _ _ _ _ _ _ _ _ n M hM T hT
  refine ⟨inst_setting hM hT, fun _ _ => rfl, fun _ _ => rfl, fun t z ht hz ω hω => ?_⟩
  exact ⟨ω.2.1, ω.2.2 ⟨t, by omega⟩, pos_next hM ht hz hω⟩

/-! ### Parts 2c and 2d on one instrument -/

section Band1

variable {Z Ω : Type} [Fintype Ω] {P : M6 1 Z Ω} (hS : Setting P)
include hS

lemma psum (t : ℕ) (z : Z) : ∑ ω, P.prob t z ω = 1 := hS.2.2.2.2.2.2.2.2.2.1 t z

lemma gbar1 (hg : ∀ ω, P.gross ω 0 = 1) (t : ℕ) (z : Z) : gbar P t z = 1 := by
  simp only [gbar, hg, mul_one]; exact psum hS t z

/-- With no marking, `lo_{t+1} > 0` puts the next target at or above `lo_{t+1}`. -/
lemma lo_le_xs (hg : ∀ ω, P.gross ω 0 = 1) {t : ℕ} {z : Z} (h : 0 < lo P t z) :
    lo P t z ≤ xs P t z := by
  have X := ld_lo hS t z h
  rw [ld_G1 hS] at X
  have Y := ld_phi_ge hS t z (lo P t z)
  rw [gbar1 hS hg, mul_one] at Y
  have hb1 : P.beta ≤ 1 := hS.2.2.2.2.2.1
  have hk := kp0 hS
  have : curv P t z * (lo P t z - xs P t z) ≤ 0 := by nlinarith
  have hc := curv_pos hS t z
  by_contra hne
  push Not at hne
  nlinarith

/-- With no marking, `hi_{t+1} < x̄` puts the next target at or below `hi_{t+1}`. -/
lemma xs_le_hi (hg : ∀ ω, P.gross ω 0 = 1) {t : ℕ} {z : Z} (h : hi P t z < P.cap 0) :
    xs P t z ≤ hi P t z := by
  have X := rd_hi hS t z h
  rw [rd_G1 hS] at X
  have Y := rd_phi_le hS t z (hi P t z)
  rw [gbar1 hS hg, mul_one] at Y
  have hb1 : P.beta ≤ 1 := hS.2.2.2.2.2.1
  have hk := km0 hS
  have : 0 ≤ curv P t z * (hi P t z - xs P t z) := by nlinarith
  have hc := curv_pos hS t z
  by_contra hne
  push Not at hne
  nlinarith

/-- A sum over outcomes, split by a two-way classification of the positive-mass outcomes. -/
lemma split_sum {t : ℕ} {z : Z} (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ ω, 0 < P.prob t z ω → (p ω ∨ q ω) ∧ ¬ (p ω ∧ q ω)) (a b : ℝ) :
    ∑ ω, P.prob t z ω * (if p ω then a else b) =
      a * (∑ ω, if p ω then P.prob t z ω else 0) + b * (∑ ω, if q ω then P.prob t z ω else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases eq_or_lt_of_le (prob0 hS t z ω) with hq0 | hq0
  · rw [← hq0]; simp
  obtain ⟨h1, h2⟩ := hpq ω hq0
  by_cases hp : p ω
  · have hnq : ¬ q ω := fun hq => h2 ⟨hp, hq⟩
    simp [hp, hnq]; ring
  · have hq : q ω := h1.resolve_left hp
    simp [hp, hq]; ring

lemma mass_le_one {t : ℕ} {z : Z} (p : Ω → Prop) [DecidablePred p] :
    (∑ ω, if p ω then P.prob t z ω else 0) ≤ 1 := by
  rw [← psum hS t z]
  exact Finset.sum_le_sum fun ω _ => by split_ifs <;> [exact le_rfl; exact prob0 hS t z ω]

lemma mass_nonneg {t : ℕ} {z : Z} (p : Ω → Prop) [DecidablePred p] :
    0 ≤ ∑ ω, if p ω then P.prob t z ω else 0 :=
  Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact prob0 hS t z ω; exact le_rfl]

lemma mass_ge {t : ℕ} {z : Z} (p : Ω → Prop) [DecidablePred p] {ω : Ω} (hp : p ω) :
    P.prob t z ω ≤ ∑ ω, if p ω then P.prob t z ω else 0 := by
  have := Finset.single_le_sum (f := fun ω => if p ω then P.prob t z ω else 0)
    (fun ω _ => by split_ifs <;> [exact prob0 hS t z ω; exact le_rfl]) (Finset.mem_univ ω)
  simpa [hp] using this

end Band1

theorem landing : Landing := by
  intro Z Ω _ P hS hk t z hT hg hw
  classical
  have ht : t < P.T := by omega
  have hc := curv_pos hS t z
  have hβ0 : 0 < P.beta := hS.2.2.2.2.1
  have hβ1 : P.beta ≤ 1 := hS.2.2.2.2.2.1
  have hkp := kp0 hS
  have hkm := km0 hS
  obtain ⟨⟨hA, -⟩, -⟩ := attained_mid hS hk z hT
  obtain ⟨hH, hL, hland⟩ := hA hw
  have hlt : lo P t z < hi P t z := by
    have : 0 < (P.kp 0 + P.km 0) / curv P t z := div_pos hk hc
    linarith
  simp only [hg, mul_one] at hland
  set U := Uland P t z
  set D := Dland P t z
  have hcl : ∀ ω, 0 < P.prob t z ω →
      (hi P t z ≤ lo P (t + 1) (P.next ω) ∨ hi P (t + 1) (P.next ω) ≤ lo P t z) ∧
        ¬ (hi P t z ≤ lo P (t + 1) (P.next ω) ∧ hi P (t + 1) (P.next ω) ≤ lo P t z) :=
    fun ω hq => ⟨hland ω hq, fun ⟨h1, h2⟩ => by
      have := lo_le_hi hS (t + 1) (P.next ω); linarith⟩
  have hUD : U + D = 1 := by
    have := split_sum hS _ _ hcl 1 1
    simp only [ite_self, mul_one, one_mul] at this
    rw [psum hS] at this
    exact this.symm
  -- the continuation's one-sided slopes at the edges
  have hld : ld (phi1 P t z) (hi P t z) = P.beta * (-P.kp 0 * U + P.km 0 * D) := by
    rw [ld_phi hS]
    congr 1
    rw [show -P.kp 0 * U + P.km 0 * D = ∑ ω, P.prob t z ω *
      (if hi P t z ≤ lo P (t + 1) (P.next ω) then -P.kp 0 else P.km 0) from (split_sum hS _ _ hcl _ _).symm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rcases eq_or_lt_of_le (prob0 hS t z ω) with hq | hq
    · rw [← hq]; simp
    rw [hg, mul_one, mul_one]
    split_ifs with hu
    · rw [V1_ld_le_lo hS _ hT hu]
    · have hd := (hland ω hq).resolve_left hu
      rw [V1_ld_above hS _ hT (lt_of_le_of_lt hd hlt)]
  have hrd : rd (phi1 P t z) (lo P t z) = P.beta * (-P.kp 0 * U + P.km 0 * D) := by
    rw [rd_phi hS]
    congr 1
    rw [show -P.kp 0 * U + P.km 0 * D = ∑ ω, P.prob t z ω *
      (if hi P t z ≤ lo P (t + 1) (P.next ω) then -P.kp 0 else P.km 0) from (split_sum hS _ _ hcl _ _).symm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rcases eq_or_lt_of_le (prob0 hS t z ω) with hq | hq
    · rw [← hq]; simp
    rw [hg, mul_one, mul_one]
    split_ifs with hu
    · rw [V1_rd_below hS _ hT (lt_of_lt_of_le hlt hu)]
    · have hd := (hland ω hq).resolve_left hu
      rw [V1_rd_ge_hi hS _ hT hd]
  rw [ld_G1 hS, hld] at hH
  rw [rd_G1 hS, hrd] at hL
  have hU0 := mass_nonneg hS (t := t) (z := z) (fun ω => hi P t z ≤ lo P (t + 1) (P.next ω))
  have hD0 := mass_nonneg hS (t := t) (z := z) (fun ω => hi P (t + 1) (P.next ω) ≤ lo P t z)
  have hup : ∀ ω, 0 < P.prob t z ω → hi P t z ≤ lo P (t + 1) (P.next ω) →
      (P.km 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * U) / curv P t z ≤
        xs P (t + 1) (P.next ω) - xs P t z := by
    intro ω _ hu
    have h0 : 0 < lo P (t + 1) (P.next ω) := lt_of_le_of_lt (lo_bounds hS t z).1 (hlt.trans_le hu)
    have key := mul_le_mul_of_nonneg_left (hu.trans (lo_le_xs hS hg h0)) hc.le
    rw [show D = 1 - U by linarith] at hH
    rw [div_le_iff₀ hc]
    linarith
  have hdown : ∀ ω, 0 < P.prob t z ω → hi P (t + 1) (P.next ω) ≤ lo P t z →
      (P.kp 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * D) / curv P t z ≤
        xs P t z - xs P (t + 1) (P.next ω) := by
    intro ω _ hd
    have h0 : hi P (t + 1) (P.next ω) < P.cap 0 := lt_of_le_of_lt hd (hlt.trans_le (hi_bounds hS t z).2)
    have key := mul_le_mul_of_nonneg_left (hd.trans' (xs_le_hi hS hg h0)) hc.le
    rw [show U = 1 - D by linarith] at hL
    rw [div_le_iff₀ hc]
    linarith
  refine ⟨hland, hUD, fun ω hq => ?_, hup, hdown⟩
  rcases hland ω hq with hu | hd
  · have hUp : P.prob t z ω ≤ U := mass_ge hS _ hu
    have h1 := hup ω hq hu
    have : 0 < (P.km 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * U) / curv P t z :=
      div_pos (by nlinarith [mul_pos (mul_pos hβ0 hk) (hq.trans_le hUp)]) hc
    linarith
  · have hDp : P.prob t z ω ≤ D := mass_ge hS _ hd
    have h1 := hdown ω hq hd
    have : 0 < (P.kp 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * D) / curv P t z :=
      div_pos (by nlinarith [mul_pos (mul_pos hβ0 hk) (hq.trans_le hDp)]) hc
    linarith

/-- The odd part of the tilt's integrand vanishes off `±δ`. -/
lemma godd (e δ : ℝ) (h1 : e + δ ≠ 0) (h2 : e ≠ δ) :
    ((if 0 < e + δ then (1 : ℝ) else 0) - (if e + δ < 0 then 1 else 0) -
        (SignType.sign δ : ℝ) * (if |e| ≤ |δ| then 1 else 0)) +
      ((if 0 < -e + δ then (1 : ℝ) else 0) - (if -e + δ < 0 then 1 else 0) -
        (SignType.sign δ : ℝ) * (if |-e| ≤ |δ| then 1 else 0)) = 0 := by
  have h1' : e ≠ -δ := fun h => h1 (by rw [h]; ring)
  rw [abs_neg]
  rcases lt_trichotomy δ 0 with hδ | hδ | hδ
  · rw [sign_neg hδ, abs_of_neg hδ]
    have := lt_or_gt_of_ne h1; have := lt_or_gt_of_ne h2
    split_ifs with a b c d e' f <;> simp only [abs_le] at * <;> norm_num <;>
      try (exfalso; linarith)
    all_goals (exfalso; rcases (lt_or_gt_of_ne h1) with h | h <;> rcases (lt_or_gt_of_ne h2) with h' | h' <;>
      first | linarith | (simp_all; linarith))
  · subst hδ
    simp only [sign_zero, SignType.coe_zero, zero_mul, sub_zero, add_zero]
    rcases lt_or_gt_of_ne h2 with h | h
    · simp [h, not_lt.mpr h.le, neg_pos.mpr h]
    · simp [h, not_lt.mpr h.le]
  · rw [sign_pos hδ, abs_of_pos hδ]
    split_ifs with a b c d e' f <;> simp only [abs_le] at * <;> norm_num <;>
      try (exfalso; linarith)
    all_goals (exfalso; rcases (lt_or_gt_of_ne h1) with h | h <;> rcases (lt_or_gt_of_ne h2) with h' | h' <;>
      first | linarith | (simp_all; linarith))

theorem tiltSign : TiltSign := by
  intro Z Ω _ P hS t z hT hg hlo hhi hUD
  classical
  obtain ⟨hc1, -, -⟩ := coarse Z Ω P hS t z hT
  obtain ⟨hH, hL, -, -⟩ := hc1 hlo hhi hUD
  have hc := curv_pos hS t z
  have hβ0 : 0 < P.beta := hS.2.2.2.2.1
  have hβ1 : P.beta ≤ 1 := hS.2.2.2.2.2.1
  have hkp := kp0 hS
  have hkm := km0 hS
  have hU1 : Umass P t z = ∑ ω, if Up P t z ω then P.prob t z ω else 0 := by
    simp only [Umass, hg, mul_one]
  have hD1 : Dmass P t z = ∑ ω, if Down P t z ω then P.prob t z ω else 0 := by
    simp only [Dmass, hg, mul_one]
  have hUle := mass_le_one hS (t := t) (z := z) (Up P t z)
  have hDle := mass_le_one hS (t := t) (z := z) (Down P t z)
  have hU0 := mass_nonneg hS (t := t) (z := z) (Up P t z)
  have hD0 := mass_nonneg hS (t := t) (z := z) (Down P t z)
  rw [← hU1] at hUle hU0
  rw [← hD1] at hDle hD0
  have htc : tilt P t z * curv P t z = P.beta * (P.kp 0 * Umass P t z - P.km 0 * Dmass P t z) := by
    rw [tilt, div_mul_cancel₀ _ hc.ne']
  have hxh : xs P t z ≤ hi P t z := by
    have e : curv P t z * (hi P t z - xs P t z) = P.km 0 + tilt P t z * curv P t z := by
      rw [hH]; field_simp; ring
    rw [htc] at e
    nlinarith [mul_le_mul_of_nonneg_left hDle (mul_nonneg hβ0.le hkm), mul_nonneg (mul_nonneg hβ0.le hkp) hU0]
  have hlx : lo P t z ≤ xs P t z := by
    have e : curv P t z * (lo P t z - xs P t z) = -P.kp 0 + tilt P t z * curv P t z := by
      rw [hL]; field_simp; ring
    rw [htc] at e
    nlinarith [mul_le_mul_of_nonneg_left hUle (mul_nonneg hβ0.le hkp), mul_nonneg (mul_nonneg hβ0.le hkm) hD0]
  have hup : ∀ ω, Up P t z ω → xs P t z < xs P (t + 1) (P.next ω) := fun ω hu => by
    unfold Up at hu
    rw [hg, mul_one] at hu
    have h0 : 0 < lo P (t + 1) (P.next ω) := lt_of_le_of_lt (hlo.le.trans (lo_le_hi hS t z)) hu
    linarith [lo_le_xs hS hg h0]
  have hdown : ∀ ω, Down P t z ω → xs P (t + 1) (P.next ω) < xs P t z := fun ω hd => by
    unfold Down at hd
    rw [hg, mul_one] at hd
    have h0 : hi P (t + 1) (P.next ω) < P.cap 0 := lt_of_lt_of_le hd (lo_bounds hS t z).2
    linarith [xs_le_hi hS hg h0]
  have part1 : ∀ ω, 0 < P.prob t z ω →
      (Up P t z ω ↔ xs P t z < xs P (t + 1) (P.next ω)) ∧
      (Down P t z ω ↔ xs P (t + 1) (P.next ω) < xs P t z) := fun ω hq =>
    ⟨⟨hup ω, fun h => (hUD ω hq).resolve_right fun hd => by linarith [hdown ω hd]⟩,
      ⟨hdown ω, fun h => (hUD ω hq).resolve_left fun hu => by linarith [hup ω hu]⟩⟩
  refine ⟨part1, fun η δ hdec hsym hk => ?_⟩
  -- masses of `η`
  set q := P.prob t z
  have hq0 : ∀ ω, 0 ≤ q ω := prob0 hS t z
  have msym : ∀ p : ℝ → Prop, [DecidablePred p] →
      (∑ ω, if p (η ω) then q ω else 0) = ∑ ω, if p (-η ω) then q ω else 0 := by
    intro p _
    have := hsym fun e => if p e then 1 else 0
    simpa only [mul_ite, mul_one, mul_zero] using this
  have hmove : ∀ ω, 0 < q ω → η ω + δ ≠ 0 := fun ω hq h => by
    rcases hUD ω hq with hu | hd
    · have := hup ω hu; rw [← sub_pos, hdec ω hq, h] at this; exact lt_irrefl _ this
    · have := hdown ω hd; rw [← sub_neg, hdec ω hq, h] at this; exact lt_irrefl _ this
  have hnd : ∀ ω, 0 < q ω → η ω ≠ δ := by
    have hz : (∑ ω, if η ω = δ then q ω else 0) = 0 := by
      rw [msym (fun e => e = δ)]
      refine Finset.sum_eq_zero fun ω _ => ?_
      rcases eq_or_lt_of_le (hq0 ω) with h | h
      · simp [← h]
      · rw [ite_eq_right]; intro h'; exact hmove ω h (by linarith)
    intro ω hq h
    have := Finset.single_le_sum (f := fun ω => if η ω = δ then q ω else 0)
      (fun ω _ => by split_ifs <;> [exact hq0 ω; exact le_rfl]) (Finset.mem_univ ω)
    simp only [h, ite_true] at this
    linarith
  set M := ∑ ω, if |η ω| ≤ |δ| then q ω else 0
  have hUe : Umass P t z = ∑ ω, if 0 < η ω + δ then q ω else 0 := by
    rw [hU1]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rcases eq_or_lt_of_le (hq0 ω) with h | h
    · simp [← h]
    · have e : Up P t z ω ↔ 0 < η ω + δ := by rw [← hdec ω h, sub_pos]; exact (part1 ω h).1
      exact if_congr e rfl rfl
  have hDe : Dmass P t z = ∑ ω, if η ω + δ < 0 then q ω else 0 := by
    rw [hD1]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rcases eq_or_lt_of_le (hq0 ω) with h | h
    · simp [← h]
    · have e : Down P t z ω ↔ η ω + δ < 0 := by rw [← hdec ω h, sub_neg]; exact (part1 ω h).2
      exact if_congr e rfl rfl
  -- `U - D = sign(δ) M`
  set g : ℝ → ℝ := fun e => (if 0 < e + δ then (1 : ℝ) else 0) - (if e + δ < 0 then 1 else 0) -
    (SignType.sign δ : ℝ) * (if |e| ≤ |δ| then 1 else 0)
  have hS0 : ∑ ω, q ω * g (η ω) = 0 := by
    have h2 : ∑ ω, q ω * g (η ω) = ∑ ω, q ω * g (-η ω) := hsym g
    have h3 : ∑ ω, q ω * g (η ω) + ∑ ω, q ω * g (-η ω) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun ω _ => ?_
      rcases eq_or_lt_of_le (hq0 ω) with h | h
      · rw [← h]; ring
      · rw [← mul_add]
        have := godd (η ω) δ (hmove ω h) (hnd ω h)
        simp only [g]
        rw [this, mul_zero]
    linarith
  have hUD' : Umass P t z - Dmass P t z = (SignType.sign δ : ℝ) * M := by
    have e : ∑ ω, q ω * g (η ω) =
        Umass P t z - Dmass P t z - (SignType.sign δ : ℝ) * M := by
      rw [hUe, hDe, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [g]
      split_ifs <;> ring
    linarith
  have htilt : tilt P t z = (SignType.sign δ : ℝ) * (P.beta * P.kp 0 * M) / curv P t z := by
    rw [tilt, ← hk, ← mul_sub, hUD']; ring
  refine ⟨htilt, fun hkpos => ?_⟩
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun ω _ => by split_ifs <;> [exact hq0 ω; exact le_rfl]
  -- positive-mass values avoid `±δ`, so `(-|δ|, |δ|]` and `[-|δ|, |δ|]` carry the same mass
  have hin : ∀ ω, 0 < q ω → (|η ω| ≤ |δ| ↔ -|δ| < η ω ∧ η ω ≤ |δ|) := fun ω hq => by
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne h1 fun h => ?_, h2⟩
      rcases abs_choice δ with hd | hd <;> rw [hd] at h
      · exact hmove ω hq (by linarith)
      · exact hnd ω hq (by linarith)
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
  rcases eq_or_ne δ 0 with hδ | hδ
  · subst hδ
    rw [htilt, sign_zero, SignType.coe_zero, zero_mul, zero_div]
    simp only [abs_zero, neg_zero, true_iff]
    intro ω _ ⟨h1, h2⟩; linarith
  have hsne : (SignType.sign δ : ℝ) ≠ 0 := by
    rcases lt_or_gt_of_ne hδ with h | h
    · rw [sign_neg h]; norm_num
    · rw [sign_pos h]; norm_num
  rw [htilt, div_eq_zero_iff, or_iff_left hc.ne', mul_eq_zero, or_iff_right hsne,
    mul_eq_zero, or_iff_right (mul_pos hβ0 hkpos).ne']
  constructor
  · intro hM ω hq hω
    have := Finset.single_le_sum (f := fun ω => if |η ω| ≤ |δ| then q ω else 0)
      (fun ω _ => by split_ifs <;> [exact hq0 ω; exact le_rfl]) (Finset.mem_univ ω)
    simp only [(hin ω hq).mpr hω, ite_true] at this
    change q ω ≤ M at this
    linarith
  · intro h
    refine Finset.sum_eq_zero fun ω _ => ?_
    rcases eq_or_lt_of_le (hq0 ω) with h0 | h0
    · simp [← h0]
    · rw [ite_eq_right]; exact fun hω => h ω h0 ((hin ω h0).mp hω)

/-! ### Part 2d: eventual strict narrowing -/

section Ev

open scoped Matrix.Norms.Operator

section FilterMean

variable {κ ο ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ι]
  [DecidableEq ι] {F : Filt κ ο ι} (hF : F.Good)
include hF

/-- `K_t = P_{t+1} H' R⁻¹`. -/
lemma gain_eq (t : ℕ) : F.gain t = F.P (t + 1) * F.Hᵀ * F.R⁻¹ := by
  have hS := det_pd (S_pd hF t)
  have hR := det_pd (R_pd hF)
  rw [Filt.gain, Filt.P]
  set S := F.H * F.P t * F.Hᵀ + F.R with hSd
  have eR : S - F.H * F.P t * F.Hᵀ = F.R := by rw [hSd]; abel
  calc F.P t * F.Hᵀ * S⁻¹ = F.P t * F.Hᵀ * S⁻¹ * ((S - F.H * F.P t * F.Hᵀ) * F.R⁻¹) := by
        rw [eR, mul_nonsing_inv _ hR, Matrix.mul_one]
    _ = _ := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
        simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hS]

/-- One step in information form: `P_{t+1}⁻¹ m_{t+1} = P_t⁻¹ m_t + H'R⁻¹(y - d)`. -/
lemma step_info (t : ℕ) (m : κ → ℝ) (y : ο → ℝ) :
    (F.P (t + 1))⁻¹ *ᵥ F.step t m y = (F.P t)⁻¹ *ᵥ m + (F.Hᵀ * F.R⁻¹) *ᵥ (y - F.d) := by
  have hJ : (F.P (t + 1))⁻¹ = (F.P t)⁻¹ + F.Hᵀ * F.R⁻¹ * F.H := by
    rw [P_inv hF, P_inv hF]; push_cast; rw [add_smul, one_smul, add_assoc]; rfl
  rw [Filt.step, gain_eq hF, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    nonsing_inv_mul _ (det_pd (P_pd hF _)), Matrix.one_mul, hJ, add_mulVec]
  simp only [mulVec_sub, ← mulVec_mulVec]
  abel

lemma meanFrom_info : ∀ (zs : List (ο → ℝ)) (t : ℕ) (m : κ → ℝ),
    (F.P (t + zs.length))⁻¹ *ᵥ F.meanFrom t m zs =
      (F.P t)⁻¹ *ᵥ m + (zs.map fun y => (F.Hᵀ * F.R⁻¹) *ᵥ (y - F.d)).sum
  | [], t, m => by simp [Filt.meanFrom]
  | y :: ys, t, m => by
    simp only [Filt.meanFrom, List.length_cons, List.map_cons, List.sum_cons]
    rw [show t + (ys.length + 1) = t + 1 + ys.length by omega, meanFrom_info ys (t + 1), step_info hF]
    abel

lemma mean_eq (z : List (ο → ℝ)) : F.mean z =
    F.P z.length *ᵥ (F.P0⁻¹ *ᵥ F.m0 + (z.map fun y => (F.Hᵀ * F.R⁻¹) *ᵥ (y - F.d)).sum) := by
  have h := meanFrom_info hF z 0 F.m0
  rw [zero_add] at h
  rw [show F.P0⁻¹ = (F.P 0)⁻¹ from rfl, ← h, mulVec_mulVec, mul_nonsing_inv _ (det_pd (P_pd hF _)),
    one_mulVec]
  rfl

omit hF in
lemma list_sum_le {α E : Type} [SeminormedAddCommGroup E] (f : α → E) {C : ℝ} :
    ∀ zs : List α, (∀ y ∈ zs, ‖f y‖ ≤ C) → ‖(zs.map f).sum‖ ≤ zs.length * C
  | [], _ => by simp
  | y :: ys, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h y (List.mem_cons_self ..)
    have h2 := list_sum_le f ys fun x hx => h x (List.mem_cons_of_mem _ hx)
    calc ‖f y + (ys.map f).sum‖ ≤ ‖f y‖ + ‖(ys.map f).sum‖ := norm_add_le _ _
      _ ≤ C + ys.length * C := add_le_add h1 h2
      _ = _ := by push_cast; ring

/-- `M_t = ‖t P_t‖ (‖P₀⁻¹ m₀‖/t + ‖H'R⁻¹‖ B)`, the bound on the mean after `t ≥ 1` observations. -/
def Mb (F : Filt κ ο ι) (B : ℝ) (t : ℕ) : ℝ :=
  ‖(t : ℝ) • F.P t‖ * (‖F.P0⁻¹ *ᵥ F.m0‖ / t + ‖F.Hᵀ * F.R⁻¹‖ * B)

lemma mean_bound {B : ℝ} (z : List (ο → ℝ)) (hz : ∀ y ∈ z, ‖y - F.d‖ ≤ B) (ht : 1 ≤ z.length) :
    ‖F.mean z‖ ≤ Mb F B z.length := by
  have ht0 : (0 : ℝ) < z.length := by exact_mod_cast ht
  rw [mean_eq hF]
  refine (linfty_opNorm_mulVec _ _).trans ?_
  have hs : ‖(z.map fun y => (F.Hᵀ * F.R⁻¹) *ᵥ (y - F.d)).sum‖ ≤ z.length * (‖F.Hᵀ * F.R⁻¹‖ * B) :=
    list_sum_le _ z fun y hy =>
      (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left (hz y hy) (norm_nonneg _))
  have hP : ‖F.P z.length‖ = ‖(z.length : ℝ) • F.P z.length‖ / z.length := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_div_cancel_left₀ _ ht0.ne']
  calc ‖F.P z.length‖ * ‖F.P0⁻¹ *ᵥ F.m0 + (z.map fun y => (F.Hᵀ * F.R⁻¹) *ᵥ (y - F.d)).sum‖
      ≤ ‖F.P z.length‖ * (‖F.P0⁻¹ *ᵥ F.m0‖ + z.length * (‖F.Hᵀ * F.R⁻¹‖ * B)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl hs)) (norm_nonneg _)
    _ = Mb F B z.length := by
        rw [hP, Mb]; field_simp

lemma Mb_lim (B : ℝ) : Tendsto (Mb F B) atTop (𝓝 (‖F.J⁻¹‖ * (0 + ‖F.Hᵀ * F.R⁻¹‖ * B))) :=
  (tP_lim hF).norm.mul ((tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds)

end FilterMean

section Move

variable {κ ο : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο]
  {F : Filt κ ο (Fin 1)} (hF : F.Good)

/-- The bound on the target's move from date `t`, for data within `B` of `d`. -/
def bnd (F : Filt κ ο (Fin 1)) (B : ℝ) (t : ℕ) : ℝ :=
  1 / F.gamma * (‖(F.Sig (t + 1))⁻¹‖ * ‖F.G‖ * (‖F.gain t‖ * (B + ‖F.H‖ * Mb F B t)) +
    ‖(F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹‖ * (‖F.G‖ * Mb F B t + ‖F.cE‖))

include hF

lemma move_bound {B : ℝ} (z : List (ο → ℝ)) (y : ο → ℝ) (hz : ∀ x ∈ z, ‖x - F.d‖ ≤ B)
    (hy : ‖y - F.d‖ ≤ B) (ht : 1 ≤ z.length) :
    |F.xstar (z.length + 1) (z ++ [y]) 0 - F.xstar z.length z 0| ≤ bnd F B z.length := by
  obtain ⟨hmean, hdec⟩ := (drift κ ο (Fin 1) F hF).1 z y
  have hm := mean_bound hF z hz ht
  have hg := gam_pos hF
  set t := z.length
  set m := F.mean z
  have hε : F.mean (z ++ [y]) - m = F.gain t *ᵥ ((y - F.d) - F.H *ᵥ m) := by
    rw [hmean, Filt.step, add_sub_cancel_left]; congr 1; abel
  have hεb : ‖F.mean (z ++ [y]) - m‖ ≤ ‖F.gain t‖ * (B + ‖F.H‖ * Mb F B t) := by
    rw [hε]
    refine (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_sub_le _ _).trans (add_le_add hy ?_)
    exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
  have hμ : ‖F.mu z‖ ≤ ‖F.G‖ * Mb F B t + ‖F.cE‖ :=
    (norm_sub_le _ _).trans (add_le_add ((linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left hm (norm_nonneg _))) le_rfl)
  rw [← Pi.sub_apply, hdec]
  refine ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ (0 : Fin 1))).trans ?_
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hg), bnd, mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hg).le)
    (mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hg).le)
  · refine (linfty_opNorm_mulVec _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left hεb (norm_nonneg _))
  · exact (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left hμ (norm_nonneg _))

lemma bnd_lim (B : ℝ) : Tendsto (bnd F B) atTop (𝓝 0) := by
  have hS := tendsto_minv (Sig_lim hF) (det_pd (Sr_pd hF))
  have hS1 := hS.comp (tendsto_add_atTop_nat 1)
  have hK : Tendsto (fun t => ‖F.gain t‖) atTop (𝓝 0) := by
    have h := tendsto_mmul (tendsto_mmul ((P_lim hF).comp (tendsto_add_atTop_nat 1))
      (tendsto_const_nhds (x := F.Hᵀ))) (tendsto_const_nhds (x := F.R⁻¹))
    simp only [Matrix.zero_mul] at h
    have := h.norm
    rw [norm_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp_def, gain_eq hF]
  have hBr : Tendsto (fun t => ‖(F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹‖) atTop (𝓝 0) := by
    have := (hS1.sub hS).norm
    rwa [sub_self, norm_zero] at this
  have hM := Mb_lim hF B
  have := ((((hS1.norm.mul (tendsto_const_nhds (x := ‖F.G‖))).mul (hK.mul
    ((tendsto_const_nhds (x := B)).add ((tendsto_const_nhds (x := ‖F.H‖)).mul hM)))).add
      (hBr.mul (((tendsto_const_nhds (x := ‖F.G‖)).mul hM).add
        (tendsto_const_nhds (x := ‖F.cE‖))))).const_mul (1 / F.gamma))
  simp only [zero_mul, mul_zero, add_zero] at this
  exact this

end Move

section Ev7

variable {κ ο ζ Θ S : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ζ]
  [Fintype Θ] [Fintype S] [DecidableEq S] {n : ℕ} {M : M7 κ ο ζ Θ S n}

omit [DecidableEq S] in
lemma hist_mem {T : ℕ} (a : Θ) (w : Fin T → S) : ∀ t, ∀ y ∈ M.hist a w t, ∃ s, y = M.obs a s
  | 0 => by simp [M7.hist]
  | t + 1 => by
    rw [M7.hist]
    split_ifs
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hist_mem a w t y h
      · exact ⟨_, List.mem_singleton.mp h⟩
    · exact hist_mem a w t

omit [DecidableEq S] in
lemma obs_le (a : Θ) (s : S) :
    ‖M.obs a s - M.F.d‖ ≤ ∑ a, ∑ s, ‖M.obs a s - M.F.d‖ :=
  (Finset.single_le_sum (f := fun s => ‖M.obs a s - M.F.d‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ s)).trans (Finset.single_le_sum (f := fun a => ∑ s, ‖M.obs a s - M.F.d‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))

end Ev7

end Ev

theorem eventual : Eventual := by
  intro κ ο ζ Θ S _ _ _ _ _ _ _ _ M hM hg1 hk
  classical
  have hF : M.F.Good := hM.1
  set B := ∑ a, ∑ s, ‖M.obs a s - M.F.d‖
  have hβ0 : 0 < M.beta := hM.2.1
  have hc0 : 0 < M.F.gamma * M.F.Sig 0 0 0 := mul_pos (gam_pos hF) (Sig_pd hF 0).diag_pos
  set ε0 := M.beta * (M.kp 0 + M.km 0) / (2 * (M.F.gamma * M.F.Sig 0 0 0))
  have hε0 : 0 < ε0 := div_pos (mul_pos hβ0 hk) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((bnd_lim hF B).eventually (gt_mem_nhds hε0))
  have hanti := ((learning κ ο (Fin 1) M.F hF).2.2.2.2.2 0).1
  refine ⟨max N 1, fun T t z ht0 htT hz => ?_⟩
  have hT1 : 1 ≤ T := by omega
  have hS := inst_setting hM hT1
  have hgr : ∀ ω, (M.inst T).gross ω 0 = 1 := fun ω => by
    simp only [M7.inst]
    split_ifs
    · exact hg1 _
    · rfl
  refine lt_of_le_of_ne ((ceiling _ _ _ hS).1 t z (show t < T by omega)) fun hw => ?_
  obtain ⟨-, hUD, -, hup, hdown⟩ := landing _ _ _ hS hk t z htT hgr hw
  -- the moves out of `z` are small
  have hmove : ∀ ω, 0 < (M.inst T).prob t z ω →
      |xs (M.inst T) (t + 1) ((M.inst T).next ω) - xs (M.inst T) t z| < ε0 := fun ω hq => by
    obtain ⟨-, hh⟩ := pos_out hM (by omega) hz hq
    obtain ⟨hnx, -⟩ := pos_next hM (by omega) hz hq
    have hlen : z.length = t := by rw [← hh, hist_length]; omega
    have hzb : ∀ x ∈ z, ‖x - M.F.d‖ ≤ B := fun x hx => by
      rw [← hh] at hx
      obtain ⟨s, rfl⟩ := hist_mem _ _ t x hx
      exact obs_le _ _
    have hb := move_bound hF z (M.obs ω.2.1 (ω.2.2 ⟨t, by omega⟩)) hzb (obs_le _ _) (by omega)
    rw [hlen] at hb
    rw [hnx]
    have e1 : xs (M.inst T) (t + 1) (z ++ [M.obs ω.2.1 (ω.2.2 ⟨t, by omega⟩)]) =
        M.F.xstar (t + 1) (z ++ [M.obs ω.2.1 (ω.2.2 ⟨t, by omega⟩)]) 0 := rfl
    have e2 : xs (M.inst T) t z = M.F.xstar t z 0 := rfl
    rw [e1, e2]
    exact lt_of_le_of_lt hb (hN t (by omega))
  have hct : curv (M.inst T) t z ≤ M.F.gamma * M.F.Sig 0 0 0 := hanti (Nat.zero_le t)
  have hcpos := curv_pos hS t z
  have hlow : ∀ X : ℝ, M.beta * (M.kp 0 + M.km 0) * (1 / 2) ≤ X → ε0 ≤ X / curv (M.inst T) t z :=
    fun X hX => by
      rw [le_div_iff₀ hcpos]
      calc ε0 * curv (M.inst T) t z ≤ ε0 * (M.F.gamma * M.F.Sig 0 0 0) :=
            mul_le_mul_of_nonneg_left hct hε0.le
        _ = M.beta * (M.kp 0 + M.km 0) * (1 / 2) := by
            have := hc0.ne'
            simp only [ε0]; field_simp
            exact div_self this
        _ ≤ X := hX
  have hβ1 : M.beta ≤ 1 := hM.2.2.1
  have hkp : 0 ≤ M.kp 0 := (hM.2.2.2.1 0).1
  have hkm : 0 ≤ M.km 0 := (hM.2.2.2.1 0).2.2.1
  have hex : ∀ (p : M7.Out Θ S T → Prop) [DecidablePred p],
      0 < (∑ ω, if p ω then (M.inst T).prob t z ω else 0) → ∃ ω, 0 < (M.inst T).prob t z ω ∧ p ω := by
    intro p _ h
    by_contra hn
    push Not at hn
    refine lt_irrefl (0 : ℝ) (h.trans_le (le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)))
    split_ifs with hp
    · exact le_antisymm (not_lt.mp fun hq => hn ω hq hp) (prob0 hS t z ω)
    · rfl
  rcases le_or_gt (1 / 2) (Uland (M.inst T) t z) with hU | hU
  · obtain ⟨ω, hq, hω⟩ := hex (fun ω => hi (M.inst T) t z ≤ lo (M.inst T) (t + 1) ((M.inst T).next ω))
      (lt_of_lt_of_le (by norm_num) hU : (0 : ℝ) < Uland (M.inst T) t z)
    have h1 := hup ω hq hω
    have h2 : ε0 ≤ ((M.inst T).km 0 * (1 - (M.inst T).beta) + (M.inst T).beta *
        ((M.inst T).kp 0 + (M.inst T).km 0) * Uland (M.inst T) t z) / curv (M.inst T) t z :=
      hlow _ (by
        show M.beta * (M.kp 0 + M.km 0) * (1 / 2) ≤ M.km 0 * (1 - M.beta) + M.beta *
          (M.kp 0 + M.km 0) * Uland (M.inst T) t z
        nlinarith [mul_nonneg hkm (sub_nonneg.mpr hβ1),
        mul_le_mul_of_nonneg_left hU (mul_pos hβ0 hk).le])
    obtain ⟨-, h3⟩ := abs_lt.mp (hmove ω hq)
    linarith
  · have hD : 1 / 2 ≤ Dland (M.inst T) t z := by linarith
    obtain ⟨ω, hq, hω⟩ := hex (fun ω => hi (M.inst T) (t + 1) ((M.inst T).next ω) ≤ lo (M.inst T) t z)
      (lt_of_lt_of_le (by norm_num) hD : (0 : ℝ) < Dland (M.inst T) t z)
    have h1 := hdown ω hq hω
    have h2 : ε0 ≤ ((M.inst T).kp 0 * (1 - (M.inst T).beta) + (M.inst T).beta *
        ((M.inst T).kp 0 + (M.inst T).km 0) * Dland (M.inst T) t z) / curv (M.inst T) t z :=
      hlow _ (by
        show M.beta * (M.kp 0 + M.km 0) * (1 / 2) ≤ M.kp 0 * (1 - M.beta) + M.beta *
          (M.kp 0 + M.km 0) * Dland (M.inst T) t z
        nlinarith [mul_nonneg hkp (sub_nonneg.mpr hβ1),
        mul_le_mul_of_nonneg_left hD (mul_pos hβ0 hk).le])
    obtain ⟨h3, -⟩ := abs_lt.mp (hmove ω hq)
    linarith

/-! ### Part 1b: diagonal decoupling -/

section Dec

variable {n : ℕ} {Z Ω : Type} [Fintype Ω] {P : M6 n Z Ω} (hS : Setting P)
  (hd : ∀ t z i j, i ≠ j → P.Sigma t z i j = 0)

include hS in
lemma one_setting (i : Fin n) : Setting (oneInst P i) := by
  have ⟨hT, _, _, hg, hb0, hb1, hk, hc, hq0, hq1, hgr⟩ := hS
  refine ⟨hT, fun t z => ?_, fun t z v hv => ?_, hg, hb0, hb1, fun _ => hk i, fun _ => hc i, hq0, hq1,
    fun ω _ => hgr ω i⟩
  · ext a b; rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; rfl
  · have hv0 : v 0 ≠ 0 := fun h => hv (by funext j; rw [Subsingleton.elim j 0, h]; rfl)
    have := diag_pos hS t z i
    simp only [dotProduct, mulVec, Fin.sum_univ_one, oneInst]
    have := mul_pos this (pow_pos (abs_pos.mpr hv0) 2)
    rw [sq_abs] at this
    nlinarith

include hS hd

lemma diag_mulVec (t : ℕ) (z : Z) (w : Fin n → ℝ) (i : Fin n) :
    (P.Sigma t z *ᵥ w) i = P.Sigma t z i i * w i := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hd t z i j (Ne.symm hj), zero_mul]) (by simp)]

lemma xstar_diag (t : ℕ) (z : Z) (i : Fin n) :
    xstar P t z i = xs (oneInst P i) t z := by
  have hpos := diag_pos hS t z i
  have hdet : IsUnit (P.Sigma t z).det := by
    have hpd : (P.Sigma t z).PosDef := by
      refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
      · rw [IsHermitian, ct]; exact hS.2.1 t z
      · rw [star_trivial]; exact hS.2.2.1 t z v hv
    exact det_pd hpd
  have e := congrFun (show P.Sigma t z *ᵥ ((P.Sigma t z)⁻¹ *ᵥ P.mu t z) = P.mu t z by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]) i
  rw [diag_mulVec hS hd] at e
  have h1 : ((P.Sigma t z)⁻¹ *ᵥ P.mu t z) i = P.mu t z i / P.Sigma t z i i := by
    field_simp; linarith
  have hdet1 : IsUnit ((oneInst P i).Sigma t z).det := by
    rw [det_unique]; exact isUnit_iff_ne_zero.mpr hpos.ne'
  calc xstar P t z i = 1 / P.gamma * (P.mu t z i / P.Sigma t z i i) := by
        simp only [xstar, Pi.smul_apply, smul_eq_mul, h1]
    _ = xs (oneInst P i) t z := by
        rw [xs, xstar, Pi.smul_apply, smul_eq_mul]
        simp only [mulVec, dotProduct, Fin.sum_univ_one]
        rw [inv11 hdet1]
        simp only [oneInst]
        ring

lemma track_dec (t : ℕ) (z : Z) (x : Fin n → ℝ) :
    track P t z x = ∑ i, track (oneInst P i) t z (cst (x i)) := by
  simp only [track1, curv, ← xstar_diag hS hd]
  simp only [track, dotProduct, diag_mulVec hS hd, Pi.sub_apply, Finset.mul_sum, oneInst]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit hS hd in
lemma cost_dec (u : Fin n → ℝ) : cost P u = ∑ i, cost (oneInst P i) (cst (u i)) := by
  simp only [cost, Fin.sum_univ_one, cst, oneInst]

lemma G_dec {t : ℕ} (hV : ∀ z' x, V P (t + 1) z' x = ∑ i, V (oneInst P i) (t + 1) z' (cst (x i)))
    (z : Z) (x : Fin n → ℝ) : G P t z x = ∑ i, G (oneInst P i) t z (cst (x i)) := by
  simp only [G, track_dec hS hd, hV, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ω _ => ?_
  simp only [mark_cst, mark, oneInst]

lemma Fobj_dec {t : ℕ} (hV : ∀ z' x, V P (t + 1) z' x = ∑ i, V (oneInst P i) (t + 1) z' (cst (x i)))
    (z : Z) (x x' : Fin n → ℝ) :
    Fobj P t z x x' = ∑ i, Fobj (oneInst P i) t z (cst (x i)) (cst (x' i)) := by
  simp only [Fobj, cost_dec (u := x' - x), G_dec hS hd hV, Finset.sum_add_distrib, cst_sub,
    Pi.sub_apply]

lemma V_dec : ∀ t z x, V P t z x = ∑ i, V (oneInst P i) t z (cst (x i)) := by
  suffices h : ∀ k t, P.T - t = k → ∀ z x, V P t z x = ∑ i, V (oneInst P i) t z (cst (x i)) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht z x
    rw [V_ge P (by omega)]
    exact (Finset.sum_eq_zero fun i _ => V_ge (oneInst P i) (show P.T ≤ t by omega) z _).symm
  | succ k ih =>
    intro t ht z x
    have htT : t < P.T := by omega
    have hV := ih (t + 1) (by omega)
    have hFd := Fobj_dec hS hd hV z x
    have hSi := one_setting hS
    choose p hp hmin hVi using fun i =>
      V_attain (hSi i) (show t < (oneInst P i).T from htT) z (G_facts (hSi i) t z).2.2 (cst (x i))
    have hpb : (fun i => p i 0) ∈ box P := fun i => (mem_box1 (oneInst P i) (p i 0)).mp
      (by rw [← cst_eta]; exact hp i)
    have hmin' : IsMinOn (Fobj P t z x) (box P) (fun i => p i 0) := fun y hy => by
      show Fobj P t z x (fun i => p i 0) ≤ Fobj P t z x y
      rw [hFd, hFd]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← cst_eta]
      exact hmin i ((mem_box1 (oneInst P i) (y i)).mpr (hy i))
    rw [V_lt P htT]
    show sInf (Fobj P t z x '' box P) = _
    rw [isLeast_sInf hpb hmin', hFd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hVi i, ← cst_eta]

end Dec

theorem decouple : Decouple := by
  intro n Z Ω _ P hS hd
  refine ⟨one_setting hS, fun t z x => ⟨V_dec hS hd t z x, fun x' => ?_⟩⟩
  have hV := fun z' y => V_dec hS hd (t + 1) z' y
  have hFd := Fobj_dec hS hd hV z x
  constructor
  · rintro ⟨hx', hmin⟩ i
    refine ⟨(mem_box1 _ _).mpr (hx' i), fun y hy => ?_⟩
    have hy' := (mem_box1 _ _).mp (cst_eta y ▸ hy)
    set y' := Function.update x' i (y 0)
    have hmem : y' ∈ box P := fun j => by
      by_cases h : j = i
      · subst h; simp only [y', Function.update_self]; exact hy'
      · simp only [y', Function.update_of_ne h]; exact hx' j
    have h := hmin y' hmem
    change Fobj P t z x x' ≤ Fobj P t z x y' at h
    rw [hFd, hFd, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    have e : ∑ j ∈ Finset.univ.erase i, Fobj (oneInst P j) t z (cst (x j)) (cst (y' j)) =
        ∑ j ∈ Finset.univ.erase i, Fobj (oneInst P j) t z (cst (x j)) (cst (x' j)) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [y', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [e] at h
    simp only [y', Function.update_self] at h
    show Fobj (oneInst P i) t z (cst (x i)) (cst (x' i)) ≤ Fobj (oneInst P i) t z (cst (x i)) y
    rw [cst_eta y]
    linarith
  · intro h
    refine ⟨fun i => (mem_box1 _ _).mp (h i).1, fun y hy => ?_⟩
    change Fobj P t z x x' ≤ Fobj P t z x y
    rw [hFd, hFd]
    exact Finset.sum_le_sum fun i _ => (h i).2 _ ((mem_box1 _ _).mpr (hy i))

/-! ### The claim -/

theorem proof : Standalone.M7LearningBandTransfer.statement :=
  ⟨instance_, Novel.M6QuarterlyBandStaticCeilingProof.proof, decouple, learning, drift, driftOne,
    tiltSign, landing, eventual⟩

end

end Novel.M7LearningBandTransferProof

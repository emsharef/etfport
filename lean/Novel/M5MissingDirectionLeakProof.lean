import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import Novel.M5PartialAdjustmentSplitProof
import Standalone.M5MissingDirectionLeak

/-!
# Proof of claim 031

Uses claim 030's proof module (`depends_on: [30]`, Q-04) for part 3's recursion and its matrix
lemmas.

* **Projections.** `Π_R = B^E'(B^E B^E')⁻¹B^E` satisfies `B^E Π_R = B^E`. With `Σ~_RR⁻¹` realized as
  `B^E'(B^E Σ~ B^E')⁻¹B^E`, `Σ~_RR⁻¹ Σ~ Π_R = Π_R`. Hence `Σ~ - Σ~ Σ~_RR⁻¹ Σ~` vanishes against `Π_R` and
  equals the Schur complement `Σ~_{U.R}`, and `J' = I - Σ~ Σ~_RR⁻¹`.
* **Reduction.** The joint problem's `D_t` has the ETF block `γB^EΣ~B^E'`, whose Schur complement
  is the reduced `D_t`. By backward induction the joint recursion is the reduced one on the fund
  block and zero on the ETF rows, and the block inverse gives both the fund and the ETF positions.
* **Leak.** `J'v = v` on `L_E^⊥` gives the recursion for `M_t`. The symmetric-part lemma and the
  stationary inverse are elementary quadratic-form arguments. The risk term changes `K_t` because
  the Riccati map is Loewner-monotone.
* **Learning.** `P^λ_t = t⁻¹(t⁻¹P_0⁻¹ + Σ_f⁻¹)⁻¹ → 0`. The Schur complement is a minimum over
  hedges, hence Loewner-monotone, and it and `J` are continuous at `Σ_f`.
-/

namespace Novel.M5MissingDirectionLeakProof

open Matrix Standalone.M5PartialAdjustmentSplit Standalone.M5MissingDirectionLeak
open Novel.M5PartialAdjustmentSplitProof

set_option linter.unusedSectionVars false

noncomputable section

variable {K N M : ℕ}

/-! ### Projections and the hedge -/

section Proj

variable {BE : Matrix (Fin M) (Fin K) ℝ} (hBE : IsUnit (BE * BEᵀ).det)
include hBE

lemma bbt_sym : (BE * BEᵀ)ᵀ = BE * BEᵀ := by rw [transpose_mul, transpose_transpose]

lemma pr_symm : (PiR BE)ᵀ = PiR BE := by
  rw [PiR, transpose_mul, transpose_mul, transpose_transpose, inv_sym (bbt_sym hBE), Matrix.mul_assoc]

lemma be_pr : BE * PiR BE = BE := by
  simp only [PiR, ← Matrix.mul_assoc, mul_nonsing_inv _ hBE, Matrix.one_mul]

lemma pr_bet : PiR BE * BEᵀ = BEᵀ := by
  have := congrArg transpose (be_pr hBE)
  rwa [transpose_mul, pr_symm hBE] at this

lemma pr_idem : PiR BE * PiR BE = PiR BE := by
  calc PiR BE * PiR BE = BEᵀ * (BE * BEᵀ)⁻¹ * (BE * PiR BE) := by
        simp only [PiR, Matrix.mul_assoc]
    _ = PiR BE := by rw [be_pr hBE]; rfl

lemma be_pu : BE * PiU BE = 0 := by
  rw [PiU, Matrix.mul_sub, Matrix.mul_one, be_pr hBE, sub_self]

lemma pu_symm : (PiU BE)ᵀ = PiU BE := by rw [PiU, transpose_sub, transpose_one, pr_symm hBE]

lemma pr_pu : PiR BE * PiU BE = 0 := by
  rw [PiU, Matrix.mul_sub, Matrix.mul_one, pr_idem hBE, sub_self]

lemma pu_pr : PiU BE * PiR BE = 0 := by
  rw [PiU, Matrix.sub_mul, Matrix.one_mul, pr_idem hBE, sub_self]

lemma pr_add_pu : PiR BE + PiU BE = 1 := by rw [PiU]; abel

lemma bet_inj : Function.Injective BEᵀ.mulVec := by
  intro a b hab
  have := congrArg ((BE * BEᵀ)⁻¹ * BE).mulVec hab
  simpa only [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBE, one_mulVec] using this

variable {Sg : Matrix (Fin K) (Fin K) ℝ} (hSg : Sg.PosDef)
include hSg

lemma bsb_pd : (BE * Sg * BEᵀ).PosDef := by
  have := hSg.conjTranspose_mul_mul_same (bet_inj hBE)
  rwa [ct_eq, transpose_transpose] at this

lemma bsb_unit : IsUnit (BE * Sg * BEᵀ).det := pd_unit (bsb_pd hBE hSg)

lemma sg_sym : Sgᵀ = Sg := transpose_of_psd hSg.posSemidef

lemma rr_sym : (RRinv BE Sg)ᵀ = RRinv BE Sg := by
  have hs : (BE * Sg * BEᵀ)ᵀ = BE * Sg * BEᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, sg_sym hBE hSg, Matrix.mul_assoc]
  rw [RRinv, transpose_mul, transpose_mul, transpose_transpose, inv_sym hs]
  simp only [Matrix.mul_assoc]

lemma rr_pr : RRinv BE Sg * PiR BE = RRinv BE Sg := by
  rw [RRinv, Matrix.mul_assoc, be_pr hBE]

lemma pr_rr : PiR BE * RRinv BE Sg = RRinv BE Sg := by
  rw [RRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, pr_bet hBE]

lemma rr_sg_pr : RRinv BE Sg * Sg * PiR BE = PiR BE := by
  simp only [RRinv, PiR, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Sg BEᵀ, ← Matrix.mul_assoc BE (Sg * BEᵀ), ← Matrix.mul_assoc BE Sg,
    ← Matrix.mul_assoc (BE * Sg * BEᵀ)⁻¹, nonsing_inv_mul _ (bsb_unit hBE hSg), Matrix.one_mul]

lemma pr_sg_rr : PiR BE * Sg * RRinv BE Sg = PiR BE := by
  have := congrArg transpose (rr_sg_pr hBE hSg)
  rwa [transpose_mul, transpose_mul, rr_sym hBE hSg, sg_sym hBE hSg, pr_symm hBE,
    ← Matrix.mul_assoc] at this

/-- `Σ~_RR⁻¹` inverts `Σ~_RR` on `L_E`. -/
lemma rr_inv : RRinv BE Sg * (PiR BE * Sg * PiR BE) = PiR BE := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rr_pr hBE hSg, rr_sg_pr hBE hSg]

/-- `Σ~ - Σ~ Σ~_RR⁻¹ Σ~` is the Schur complement. -/
lemma schur_eq : Sg - Sg * RRinv BE Sg * Sg = Schur BE Sg := by
  set X := Sg - Sg * RRinv BE Sg * Sg
  have hXR : X * PiR BE = 0 := by
    simp only [X, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (RRinv BE Sg), rr_sg_pr hBE hSg, sub_self]
  have hRX : PiR BE * X = 0 := by
    simp only [X, Matrix.mul_sub, ← Matrix.mul_assoc]
    rw [pr_sg_rr hBE hSg, sub_self]
  have hX : X = PiU BE * X * PiU BE := by
    conv_lhs => rw [← Matrix.one_mul X, ← Matrix.mul_one (1 * X), ← pr_add_pu hBE]
    simp only [Matrix.add_mul, Matrix.mul_add, hRX, zero_add, Matrix.mul_assoc, hXR,
      Matrix.mul_zero]
  rw [hX]
  simp only [X, Schur, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc (PiR BE) (RRinv BE Sg), pr_rr hBE hSg, ← Matrix.mul_assoc (RRinv BE Sg) (PiR BE),
    rr_pr hBE hSg]

/-- `J' = I - Σ~ Σ~_RR⁻¹`. -/
lemma jt_eq : (Jmap BE Sg)ᵀ = 1 - Sg * RRinv BE Sg := by
  simp only [Jmap, transpose_sub, transpose_mul, pu_symm hBE, pr_symm hBE, rr_sym hBE hSg,
    sg_sym hBE hSg]
  rw [rr_pr hBE hSg, Matrix.mul_assoc, Matrix.mul_assoc, pr_rr hBE hSg]
  have hp : PiR BE * (Sg * RRinv BE Sg) = PiR BE := by rw [← Matrix.mul_assoc]; exact pr_sg_rr hBE hSg
  rw [PiU, Matrix.sub_mul, Matrix.one_mul, hp]
  abel

lemma jt_on_u {v : Fin K → ℝ} (hv : PiR BE *ᵥ v = 0) : (Jmap BE Sg)ᵀ *ᵥ v = v := by
  rw [jt_eq hBE hSg, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← rr_pr hBE hSg, ← mulVec_mulVec, hv,
    mulVec_zero, mulVec_zero, sub_zero]

/-- The minimum-variance hedge: `x'Σ~_{U.R}x ≤ (x - B^E'z)'Σ~(x - B^E'z)` for every `z`, with
equality at `z* = (B^EΣ~B^E')⁻¹B^EΣ~x`. -/
lemma schur_min (x : Fin K → ℝ) (z : Fin M → ℝ) :
    x ⬝ᵥ (Schur BE Sg *ᵥ x) ≤ (x - BEᵀ *ᵥ z) ⬝ᵥ (Sg *ᵥ (x - BEᵀ *ᵥ z)) ∧
    x ⬝ᵥ (Schur BE Sg *ᵥ x) = (x - BEᵀ *ᵥ ((BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x)))) ⬝ᵥ
      (Sg *ᵥ (x - BEᵀ *ᵥ ((BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x))))) := by
  have hSsym := sg_sym hBE hSg
  set V := BE * Sg * BEᵀ
  have hV := bsb_pd hBE hSg
  have hVsym : Vᵀ = V := transpose_of_psd hV.posSemidef
  have hVi : V * V⁻¹ = 1 := mul_nonsing_inv _ (pd_unit hV)
  set w := BE *ᵥ (Sg *ᵥ x)
  set zs := V⁻¹ *ᵥ w
  have hVz : V *ᵥ zs = w := by simp only [zs]; rw [mulVec_mulVec, hVi, one_mulVec]
  have dt : ∀ {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (a : m → ℝ) (b : n → ℝ),
      a ⬝ᵥ (A *ᵥ b) = (Aᵀ *ᵥ a) ⬝ᵥ b := fun A a b => by rw [dotProduct_mulVec, mulVec_transpose]
  -- the quadratic form of the Schur complement
  have hq : x ⬝ᵥ (Schur BE Sg *ᵥ x) = x ⬝ᵥ (Sg *ᵥ x) - zs ⬝ᵥ w := by
    rw [← schur_eq hBE hSg, sub_mulVec, dotProduct_sub]
    congr 1
    simp only [RRinv, ← mulVec_mulVec]
    rw [dt Sg, hSsym, dt BEᵀ, transpose_transpose, dotProduct_comm]
  -- expand `f(z) = (x - B^E'z)'Σ~(x - B^E'z)`
  have hf : ∀ u : Fin M → ℝ, (x - BEᵀ *ᵥ u) ⬝ᵥ (Sg *ᵥ (x - BEᵀ *ᵥ u)) =
      x ⬝ᵥ (Sg *ᵥ x) - 2 * (u ⬝ᵥ w) + u ⬝ᵥ (V *ᵥ u) := by
    intro u
    have e1 : x ⬝ᵥ (Sg *ᵥ (BEᵀ *ᵥ u)) = u ⬝ᵥ w := by
      rw [dt Sg, hSsym, dt BEᵀ, transpose_transpose, dotProduct_comm]
    have e2 : (BEᵀ *ᵥ u) ⬝ᵥ (Sg *ᵥ x) = u ⬝ᵥ w := by
      rw [← dt BE]
    have e3 : (BEᵀ *ᵥ u) ⬝ᵥ (Sg *ᵥ (BEᵀ *ᵥ u)) = u ⬝ᵥ (V *ᵥ u) := by
      rw [← dt BE]
      simp only [V, ← mulVec_mulVec]
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [e1, e2, e3]
    ring
  have hVzs : zs ⬝ᵥ (V *ᵥ zs) = zs ⬝ᵥ w := by rw [hVz]
  refine ⟨?_, ?_⟩
  · rw [hq, hf]
    have hnn := hV.posSemidef.dotProduct_mulVec_nonneg (z - zs)
    simp only [star_trivial, mulVec_sub, sub_dotProduct, dotProduct_sub] at hnn
    have hzz : zs ⬝ᵥ (V *ᵥ z) = z ⬝ᵥ (V *ᵥ zs) := sym_dot hVsym zs z
    rw [hVz] at hzz hnn
    linarith
  · rw [hq, hf]
    linarith

lemma schur_psd : (Schur BE Sg).PosSemidef := by
  refine psd_of ?_ fun x => ?_
  · rw [← schur_eq hBE hSg, transpose_sub, transpose_mul, transpose_mul, rr_sym hBE hSg,
      sg_sym hBE hSg, Matrix.mul_assoc]
  · rw [(schur_min hBE hSg x 0).2]
    have := hSg.posSemidef.dotProduct_mulVec_nonneg
      (x - BEᵀ *ᵥ ((BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x))))
    simpa using this

lemma schur_pd_u {x : Fin K → ℝ} (hx : PiR BE *ᵥ x = 0) (hx0 : x ≠ 0) :
    0 < x ⬝ᵥ (Schur BE Sg *ᵥ x) := by
  rw [(schur_min hBE hSg x 0).2]
  set w := x - BEᵀ *ᵥ ((BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x)))
  have hw : w ≠ 0 := by
    intro h
    apply hx0
    have hx' : x = BEᵀ *ᵥ ((BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x))) := sub_eq_zero.mp h
    rw [hx', mulVec_mulVec, pr_bet hBE] at hx
    rw [hx', hx]
  have := hSg.dotProduct_mulVec_pos hw
  simpa using this

/-- The Schur complement is Loewner-monotone in `Σ~`. -/
lemma schur_mono {Sg2 : Matrix (Fin K) (Fin K) ℝ} (hSg2 : Sg2.PosDef) (hle : (Sg - Sg2).PosSemidef) :
    (Schur BE Sg - Schur BE Sg2).PosSemidef := by
  refine psd_of ?_ fun x => ?_
  · have h1 := transpose_of_psd (schur_psd hBE hSg)
    have h2 := transpose_of_psd (schur_psd hBE hSg2)
    rw [transpose_sub, h1, h2]
  · rw [sub_mulVec, dotProduct_sub, sub_nonneg]
    set z := (BE * Sg * BEᵀ)⁻¹ *ᵥ (BE *ᵥ (Sg *ᵥ x))
    have h1 := (schur_min hBE hSg2 x z).1
    have h2 := (schur_min hBE hSg x 0).2
    have h3 := hle.dotProduct_mulVec_nonneg (x - BEᵀ *ᵥ z)
    simp only [star_trivial, sub_mulVec, dotProduct_sub] at h3
    linarith

end Proj

/-! ### Part 1 -/

theorem coordinates : Coordinates := by
  intro K N M BA BE hBE
  have hB : ∀ (xA : Fin N → ℝ) (xE : Fin M → ℝ),
      (Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE = BAᵀ *ᵥ xA + BEᵀ *ᵥ xE := fun xA xE => by
    simp only [Bmat, transpose_fromRows, fromCols_mulVec_sumElim]
  have hPBE : ∀ u : Fin M → ℝ, PiR BE *ᵥ (BEᵀ *ᵥ u) = BEᵀ *ᵥ u := fun u => by
    rw [mulVec_mulVec, pr_bet hBE]
  have hplus : ∀ u : Fin M → ℝ, BEplus BE *ᵥ (BEᵀ *ᵥ u) = u := fun u => by
    rw [BEplus, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBE, one_mulVec]
  have hBEplus : ∀ u : Fin K → ℝ, BEᵀ *ᵥ (BEplus BE *ᵥ u) = PiR BE *ᵥ u := fun u => by
    rw [BEplus, mulVec_mulVec, PiR, Matrix.mul_assoc]
  refine ⟨pr_symm hBE, pr_idem hBE, pr_bet hBE, be_pu hBE, fun xA xE => ?_, fun yR xA hy => ?_,
    fun Sg hSg => ⟨rr_inv hBE hSg, pr_rr hBE hSg, rr_pr hBE hSg⟩⟩
  · have hPB : PiR BE *ᵥ ((Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE) = PiR BE *ᵥ (BAᵀ *ᵥ xA) + BEᵀ *ᵥ xE := by
      rw [hB, mulVec_add, hPBE]
    refine ⟨hPB, ?_, ?_⟩
    · rw [hPB, add_sub_cancel_left, hplus]
    · have e : BAᵀ *ᵥ xA = PiR BE *ᵥ (BAᵀ *ᵥ xA) + PiU BE *ᵥ (BAᵀ *ᵥ xA) := by
        rw [← add_mulVec, pr_add_pu hBE, one_mulVec]
      rw [hPB, hB]
      conv_lhs => rw [e]
      abel
  · have hPP : ∀ u : Fin K → ℝ, PiR BE *ᵥ (PiR BE *ᵥ u) = PiR BE *ᵥ u := fun u => by
      rw [mulVec_mulVec, pr_idem hBE]
    rw [hB, mulVec_add, hBEplus, hPP, mulVec_sub, hy, hPP]
    abel

/-! ### Part 4, the stationary case -/

theorem stationary : Stationary := by
  intro N K LA D BA rho hL hDL hr hr1
  have hD : D.PosDef := by
    have := hDL.add_posSemidef hL.posSemidef
    rwa [sub_add_cancel] at this
  have hDu := pd_unit hD
  set X := 1 - rho • (LA * D⁻¹)
  have hinj : Function.Injective X.mulVec := by
    intro a b hab
    rw [← sub_eq_zero]
    set v := a - b
    have hv : X *ᵥ v = 0 := by simp only [v, mulVec_sub, hab, sub_self]
    set w := D⁻¹ *ᵥ v
    have hDw : D *ᵥ w = v := by simp only [w, mulVec_mulVec, mul_nonsing_inv _ hDu, one_mulVec]
    have hvw : v = rho • (LA *ᵥ w) := by
      have : v - rho • ((LA * D⁻¹) *ᵥ v) = 0 := by
        simpa only [X, sub_mulVec, one_mulVec, smul_mulVec] using hv
      rw [sub_eq_zero] at this
      rw [this, ← mulVec_mulVec]
    have h1 := hDL.posSemidef.dotProduct_mulVec_nonneg w
    have h2 := hL.posSemidef.dotProduct_mulVec_nonneg w
    simp only [star_trivial, sub_mulVec, dotProduct_sub] at h1 h2
    have h3 : w ⬝ᵥ (D *ᵥ w) = rho * (w ⬝ᵥ (LA *ᵥ w)) := by
      rw [hDw, hvw, dotProduct_smul, smul_eq_mul]
    by_contra hne
    have hw0 : w ≠ 0 := by
      intro h; apply hne; rw [← hDw, h, mulVec_zero]
    have := hDL.dotProduct_mulVec_pos hw0
    simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
    nlinarith
  have hXu : IsUnit X := (Matrix.mulVec_injective_iff_isUnit).mp hinj
  have hXd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hXu
  refine ⟨hXd, ?_, ?_, fun v hv => ?_⟩
  · have h := mul_nonsing_inv X hXd
    calc X⁻¹ = 1 * X⁻¹ := (Matrix.one_mul _).symm
      _ = (X + rho • (LA * D⁻¹)) * X⁻¹ := by simp only [X, sub_add_cancel]
      _ = 1 + rho • (LA * D⁻¹) * X⁻¹ := by rw [Matrix.add_mul, h]
  · exact Matrix.isUnit_nonsing_inv_det X hXd
  · intro h
    apply hv
    have hDi : Function.Injective (D⁻¹).mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det D hDu))
    have hXi : Function.Injective (X⁻¹).mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det X hXd))
    exact hXi ((hDi (h.trans (mulVec_zero _).symm)).trans (mulVec_zero _).symm)

/-! ### Block inverses -/

lemma blk_inv {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ) (hD : IsUnit D.det)
    (hS : IsUnit (A - B * D⁻¹ * C).det) :
    (Matrix.fromBlocks A B C D)⁻¹ =
      Matrix.fromBlocks (A - B * D⁻¹ * C)⁻¹ (-((A - B * D⁻¹ * C)⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹)) (D⁻¹ + D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹ * B * D⁻¹) := by
  let := D.invertibleOfIsUnitDet hD
  have e : ⅟D = D⁻¹ := invOf_eq_nonsing_inv D
  let _ : Invertible (A - B * ⅟D * C) := (A - B * ⅟D * C).invertibleOfIsUnitDet (by rw [e]; exact hS)
  let := fromBlocks₂₂Invertible A B C D
  have h := invOf_fromBlocks₂₂_eq A B C D
  simp only [invOf_eq_nonsing_inv] at h
  exact h

lemma inv_gsmul {α : Type} [Fintype α] [DecidableEq α] {V : Matrix α α ℝ} {g : ℝ} (hg : g ≠ 0)
    (hV : IsUnit V.det) : (g • V)⁻¹ = g⁻¹ • V⁻¹ :=
  Matrix.inv_eq_left_inv (by rw [smul_mul_smul_comm, inv_mul_cancel₀ hg, nonsing_inv_mul _ hV, one_smul])

lemma bmat_sand (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ)
    (Sg : Matrix (Fin K) (Fin K) ℝ) :
    Bmat BA BE * Sg * (Bmat BA BE)ᵀ =
      Matrix.fromBlocks (BA * Sg * BAᵀ) (BA * Sg * BEᵀ) (BE * Sg * BAᵀ) (BE * Sg * BEᵀ) := by
  rw [Bmat, transpose_fromRows, fromRows_mul, fromRows_mul_fromCols]

/-! ### The joint problem reduces to the fund problem -/

section Joint

variable {P : Leak K N M} (hS : P.Setting)
include hS

lemma hgam : 0 < P.gam := hS.1
lemma hLA : P.LA.PosDef := hS.2.2.2.1
lemma hSt (t : ℕ) : (P.St t).PosDef := hS.2.2.2.2.1 t
lemma hSAt (t : ℕ) : (P.SAt t).PosDef := hS.2.2.2.2.2.1 t
lemma hBE : IsUnit (P.BE * P.BEᵀ).det := hS.2.2.2.2.2.2

lemma sigred_pd (t : ℕ) : (SigRed P.BA P.BE (P.St t) (P.SAt t)).PosDef := by
  have h := (schur_psd (hBE hS) (hSt hS t)).mul_mul_conjTranspose_same P.BA
  rw [ct_eq] at h
  exact (hSAt hS t).add_posSemidef h

lemma red_setting : P.red.Setting :=
  ⟨(hLA hS).posSemidef, fun t => (sigred_pd hS t).smul (hgam hS), hS.2.1⟩

lemma red0_setting : P.red0.Setting :=
  ⟨(hLA hS).posSemidef, fun t => (hSAt hS t).smul (hgam hS), hS.2.1⟩

/-- The joint `D_t`, given the joint `A_{t+1}` on the fund block. -/
lemma joint_D {t : ℕ} (hA : P.joint.A (t + 1) = Matrix.fromBlocks (P.red.A (t + 1)) 0 0 0) :
    P.joint.D t = Matrix.fromBlocks
      (P.LA + P.gam • (P.BA * P.St t * P.BAᵀ + P.SAt t) + P.rho • P.red.A (t + 1))
      (P.gam • (P.BA * P.St t * P.BEᵀ)) (P.gam • (P.BE * P.St t * P.BAᵀ))
      (P.gam • (P.BE * P.St t * P.BEᵀ)) := by
  simp only [LQ.D, hA]
  show Matrix.fromBlocks P.LA 0 0 0 + P.gam • (Bmat P.BA P.BE * P.St t * (Bmat P.BA P.BE)ᵀ +
    Matrix.fromBlocks (P.SAt t) 0 0 0) + P.rho • Matrix.fromBlocks (P.red.A (t + 1)) 0 0 0 = _
  rw [bmat_sand, fromBlocks_add, fromBlocks_smul, fromBlocks_smul, fromBlocks_add, fromBlocks_add]
  simp only [add_zero, smul_zero, zero_add]

/-- The Schur complement of the joint `D_t` over the ETF block is the reduced `D_t`. -/
lemma joint_schur (t : ℕ) :
    P.LA + P.gam • (P.BA * P.St t * P.BAᵀ + P.SAt t) + P.rho • P.red.A (t + 1) -
      P.gam • (P.BA * P.St t * P.BEᵀ) * (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ *
        (P.gam • (P.BE * P.St t * P.BAᵀ)) = P.red.D t := by
  have hg := (hgam hS).ne'
  rw [inv_gsmul hg (bsb_unit (hBE hS) (hSt hS t))]
  have e : P.gam • (P.BA * P.St t * P.BEᵀ) * (P.gam⁻¹ • (P.BE * P.St t * P.BEᵀ)⁻¹) *
      (P.gam • (P.BE * P.St t * P.BAᵀ)) =
      P.gam • (P.BA * (P.St t * RRinv P.BE (P.St t) * P.St t) * P.BAᵀ) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, RRinv, Matrix.mul_assoc]
    rw [show P.gam * (P.gam⁻¹ * P.gam) = P.gam by field_simp]
  rw [e]
  show _ = P.LA + P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t) + P.rho • P.red.A (t + 1)
  rw [SigRed, ← schur_eq (hBE hS) (hSt hS t)]
  simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
  abel

end Joint

lemma fromRows_add' {m₁ m₂ n : Type} (A₁ B₁ : Matrix m₁ n ℝ) (A₂ B₂ : Matrix m₂ n ℝ) :
    Matrix.fromRows A₁ A₂ + Matrix.fromRows B₁ B₂ = Matrix.fromRows (A₁ + B₁) (A₂ + B₂) := by
  ext (i | i) j <;> simp

lemma fromRows_smul' {m₁ m₂ n : Type} (c : ℝ) (A₁ : Matrix m₁ n ℝ) (A₂ : Matrix m₂ n ℝ) :
    c • Matrix.fromRows A₁ A₂ = Matrix.fromRows (c • A₁) (c • A₂) := by
  ext (i | i) j <;> simp

section Joint2

variable {P : Leak K N M} (hS : P.Setting)
include hS

/-- The four blocks of the joint `D_t`, and its inverse through the Schur complement. -/
lemma joint_Dinv {t : ℕ} (hA : P.joint.A (t + 1) = Matrix.fromBlocks (P.red.A (t + 1)) 0 0 0) :
    (P.joint.D t)⁻¹ = Matrix.fromBlocks (P.red.D t)⁻¹
      (-((P.red.D t)⁻¹ * (P.gam • (P.BA * P.St t * P.BEᵀ)) * (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹))
      (-((P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ * (P.gam • (P.BE * P.St t * P.BAᵀ)) * (P.red.D t)⁻¹))
      ((P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ + (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ *
        (P.gam • (P.BE * P.St t * P.BAᵀ)) * (P.red.D t)⁻¹ * (P.gam • (P.BA * P.St t * P.BEᵀ)) *
        (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹) := by
  have h22 : IsUnit (P.gam • (P.BE * P.St t * P.BEᵀ)).det :=
    pd_unit ((bsb_pd (hBE hS) (hSt hS t)).smul (hgam hS))
  have hSd : IsUnit (P.red.D t).det := pd_unit (LQ.D_pd (red_setting hS) t)
  rw [joint_D hS hA, blk_inv _ _ _ _ h22 (by rw [joint_schur hS t]; exact hSd), joint_schur hS t]

/-- `P_{12} P_{22}⁻¹ = B^A Σ~ B^E'(B^E Σ~ B^E')⁻¹`, so `P_{12} P_{22}⁻¹ B^E = B^A Σ~ Σ~_RR⁻¹`. -/
lemma p12_p22 (t : ℕ) :
    P.gam • (P.BA * P.St t * P.BEᵀ) * (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ =
      P.BA * P.St t * P.BEᵀ * (P.BE * P.St t * P.BEᵀ)⁻¹ := by
  rw [inv_gsmul (hgam hS).ne' (bsb_unit (hBE hS) (hSt hS t))]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (hgam hS).ne', one_smul]

/-- The joint recursion is the reduced one on the fund block and zero on the ETF rows. -/
lemma joint_ric : ∀ s, P.joint.A s = Matrix.fromBlocks (P.red.A s) 0 0 0 ∧
    P.joint.C s = Matrix.fromRows (P.red.C s) 0 ∧ P.joint.c s = 0 ∧ P.red.c s = 0 := by
  suffices h : ∀ k s, P.T - s = k → P.joint.A s = Matrix.fromBlocks (P.red.A s) 0 0 0 ∧
      P.joint.C s = Matrix.fromRows (P.red.C s) 0 ∧ P.joint.c s = 0 ∧ P.red.c s = 0 from
    fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs
    have h1 : P.joint.T ≤ s := by show P.T ≤ s; omega
    have h2 : P.red.T ≤ s := by show P.T ≤ s; omega
    rw [LQ.A_ge _ h1, LQ.C_ge _ h1, LQ.c_ge _ h1, LQ.A_ge _ h2, LQ.C_ge _ h2, LQ.c_ge _ h2,
      fromBlocks_zero, fromRows_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s hs
    have hsT : s < P.T := by omega
    obtain ⟨iA, iC, ic, icr⟩ := ih (s + 1) (by omega)
    have hDi := joint_Dinv hS iA
    obtain ⟨eA, eC, ec⟩ := LQ.ric_lt P.joint (show s < P.joint.T from hsT)
    obtain ⟨fA, fC, fc⟩ := LQ.ric_lt P.red (show s < P.red.T from hsT)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [eA, fA, hDi]
      show Matrix.fromBlocks P.LA 0 0 0 - Matrix.fromBlocks P.LA 0 0 0 * _ * Matrix.fromBlocks P.LA 0 0 0 = _
      simp only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, fromBlocks_sub',
        sub_zero]
      rfl
    · rw [eC, fC, hDi, iC]
      show Matrix.fromBlocks P.LA 0 0 0 * _ * (Matrix.fromBlocks P.BA 1 P.BE 0 + P.rho •
        Matrix.fromRows (P.red.C (s + 1)) 0) = _
      rw [← fromRows_fromCols_eq_fromBlocks P.BA (1 : Matrix (Fin N) (Fin N) ℝ) P.BE
          (0 : Matrix (Fin M) (Fin N) ℝ), fromRows_smul', fromRows_add', fromBlocks_multiply,
        fromBlocks_mul_fromRows]
      simp only [Matrix.zero_mul, add_zero, smul_zero]
      congr 1
      -- the fund rows
      show P.LA * (P.red.D s)⁻¹ * (Matrix.fromCols P.BA 1 + P.rho • P.red.C (s + 1)) +
        P.LA * -((P.red.D s)⁻¹ * (P.gam • (P.BA * P.St s * P.BEᵀ)) *
          (P.gam • (P.BE * P.St s * P.BEᵀ))⁻¹) * Matrix.fromCols P.BE (0 : Matrix (Fin M) (Fin N) ℝ) =
        P.LA * (P.red.D s)⁻¹ * (Gred P.BA P.BE (P.St s) + P.rho • P.red.C (s + 1))
      have hq : (P.red.D s)⁻¹ * (P.gam • (P.BA * P.St s * P.BEᵀ)) * (P.gam • (P.BE * P.St s * P.BEᵀ))⁻¹ *
          Matrix.fromCols P.BE (0 : Matrix (Fin M) (Fin N) ℝ) = (P.red.D s)⁻¹ * Matrix.fromCols (P.BA * P.St s * RRinv P.BE (P.St s)) (0 : Matrix (Fin N) (Fin N) ℝ) := by
        rw [Matrix.mul_assoc (P.red.D s)⁻¹, p12_p22 hS s, Matrix.mul_assoc, mul_fromCols, Matrix.mul_zero]
        simp only [RRinv, Matrix.mul_assoc]
      rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc P.LA _ (Matrix.fromCols P.BE (0 : Matrix (Fin M) (Fin N) ℝ))]
      rw [show (P.red.D s)⁻¹ * (P.gam • (P.BA * P.St s * P.BEᵀ)) * (P.gam • (P.BE * P.St s * P.BEᵀ))⁻¹ *
          Matrix.fromCols P.BE (0 : Matrix (Fin M) (Fin N) ℝ) = _ from hq] at *
      simp only [Matrix.mul_assoc]
      rw [← sub_eq_add_neg, ← Matrix.mul_sub, ← Matrix.mul_sub]
      congr 2
      rw [Gred, jt_eq (hBE hS) (hSt hS s), Matrix.mul_sub, Matrix.mul_one]
      ext i (j | j) <;> simp; ring
    · rw [ec, ic]
      show _ *ᵥ (P.rho • (0 : Fin N ⊕ Fin M → ℝ) - 0) = 0
      rw [smul_zero, sub_zero, mulVec_zero]
    · rw [fc, icr]
      show _ *ᵥ (P.rho • (0 : Fin N → ℝ) - 0) = 0
      rw [smul_zero, sub_zero, mulVec_zero]

end Joint2

section Joint3

variable {P : Leak K N M} (hS : P.Setting)
include hS

/-- The joint policy: the fund positions are the reduced policy, and the ETF positions solve the
ETF rows of the first-order condition. -/
lemma joint_policy {t : ℕ} (_ht : t < P.T) (xm : Fin N ⊕ Fin M → ℝ) (m : Fin K ⊕ Fin N → ℝ) :
    P.joint.policy t xm m = Sum.elim (P.red.policy t (fun i => xm (Sum.inl i)) m)
      ((P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ *ᵥ (P.BE *ᵥ (fun k => m (Sum.inl k)) -
        (P.gam • (P.BE * P.St t * P.BAᵀ)) *ᵥ P.red.policy t (fun i => xm (Sum.inl i)) m)) := by
  obtain ⟨iA, iC, ic, icr⟩ := joint_ric hS (t + 1)
  have hDi := joint_Dinv hS iA
  set lh : Fin K → ℝ := fun k => m (Sum.inl k)
  set ah : Fin N → ℝ := fun i => m (Sum.inr i)
  set xmA : Fin N → ℝ := fun i => xm (Sum.inl i)
  have hm : m = Sum.elim lh ah := by funext i; cases i <;> rfl
  set S := P.red.D t
  set P12 := P.gam • (P.BA * P.St t * P.BEᵀ)
  set P21 := P.gam • (P.BE * P.St t * P.BAᵀ)
  set P22 := P.gam • (P.BE * P.St t * P.BEᵀ)
  set X1 : Matrix (Fin N) (Fin K ⊕ Fin N) ℝ := Matrix.fromCols P.BA 1 + P.rho • P.red.C (t + 1)
  -- the joint policy is `D⁻¹ b` with `b = (Λ_A x^A_{t-1} + X1 m, B^E λ̂)`
  have hb : P.joint.policy t xm m = (P.joint.D t)⁻¹ *ᵥ Sum.elim (P.LA *ᵥ xmA + X1 *ᵥ m) (P.BE *ᵥ lh) := by
    simp only [LQ.policy, LQ.K, LQ.L, LQ.l, ← mulVec_mulVec, ← mulVec_add, ic]
    congr 1
    show Matrix.fromBlocks P.LA 0 0 0 *ᵥ xm + (Matrix.fromBlocks P.BA 1 P.BE 0 +
      P.rho • P.joint.C (t + 1)) *ᵥ m + (P.rho • (0 : Fin N ⊕ Fin M → ℝ) - 0) = _
    rw [iC, ← fromRows_fromCols_eq_fromBlocks P.BA (1 : Matrix (Fin N) (Fin N) ℝ) P.BE
      (0 : Matrix (Fin M) (Fin N) ℝ), fromRows_smul', fromRows_add', fromRows_mulVec, smul_zero, sub_zero,
      add_zero, smul_zero, add_zero, hm]
    have hx : xm = Sum.elim xmA (fun j => xm (Sum.inr j)) := by funext i; cases i <;> rfl
    rw [hx, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero]
    funext i
    cases i <;> simp [X1]
  -- the reduced policy is `S⁻¹(Λ_A x^A_{t-1} + (G^red + ρC') m)`
  have hred : P.red.policy t xmA m = S⁻¹ *ᵥ (P.LA *ᵥ xmA + X1 *ᵥ m -
      P12 *ᵥ (P22⁻¹ *ᵥ (P.BE *ᵥ lh))) := by
    simp only [LQ.policy, LQ.K, LQ.L, LQ.l, ← mulVec_mulVec, ← mulVec_add, icr]
    congr 1
    show P.LA *ᵥ xmA + (Gred P.BA P.BE (P.St t) + P.rho • P.red.C (t + 1)) *ᵥ m +
      (P.rho • (0 : Fin N → ℝ) - 0) = _
    rw [smul_zero, sub_zero, add_zero, add_sub_assoc]
    congr 1
    rw [mulVec_mulVec, mulVec_mulVec, p12_p22 hS t, Gred, jt_eq (hBE hS) (hSt hS t), Matrix.mul_sub,
      Matrix.mul_one]
    simp only [X1, add_mulVec, hm, fromCols_mulVec_sumElim, sub_mulVec, RRinv, 
      Matrix.mul_assoc]
    abel
  rw [hb, hDi, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hA' : S⁻¹ *ᵥ (P.LA *ᵥ xmA + X1 *ᵥ m) + (-(S⁻¹ * P12 * P22⁻¹)) *ᵥ (P.BE *ᵥ lh) =
      P.red.policy t xmA m := by
    rw [hred, mulVec_sub, neg_mulVec, ← sub_eq_add_neg]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [hA']
  congr 1
  rw [hred]
  simp only [mulVec_sub, mulVec_add, add_mulVec, neg_mulVec, mulVec_mulVec, Matrix.mul_assoc,
    Matrix.add_mul, Matrix.neg_mul]
  abel

end Joint3

/-! ### Parts 2 and 3 -/

theorem etfExposure : EtfExposure := by
  intro K N M P hS t ht xm m x xA yR
  have hBEu := hBE hS
  have hSg := hSt hS t
  set lh : Fin K → ℝ := fun k => m (Sum.inl k)
  have hx : x = Sum.elim xA (fun j => x (Sum.inr j)) := by funext i; cases i <;> rfl
  set xE : Fin M → ℝ := fun j => x (Sum.inr j)
  have hpol := joint_policy hS ht xm m
  have hxA : xA = P.red.policy t (fun i => xm (Sum.inl i)) m := by
    simp only [xA, x, hpol, Sum.elim_inl]
  have hxE : xE = (P.gam • (P.BE * P.St t * P.BEᵀ))⁻¹ *ᵥ (P.BE *ᵥ lh -
      (P.gam • (P.BE * P.St t * P.BAᵀ)) *ᵥ xA) := by
    funext j; simp only [xE, x, hpol, Sum.elim_inr, hxA]; rfl
  obtain ⟨-, -, -, -, hco, -, -⟩ := coordinates K N M P.BA P.BE hBEu
  obtain ⟨hPB, hback, -⟩ := hco xA xE
  have hyR : yR = PiR P.BE *ᵥ (P.BAᵀ *ᵥ xA) + P.BEᵀ *ᵥ xE := by
    show PiR P.BE *ᵥ ((Bmat P.BA P.BE)ᵀ *ᵥ x) = _
    rw [hx]; exact hPB
  -- `B^E' x^E = Σ~_RR⁻¹((1/γ)λ̂ - Σ~ B^A' x^A)`
  have hBx : P.BEᵀ *ᵥ xE = RRinv P.BE (P.St t) *ᵥ ((1 / P.gam) • lh - P.St t *ᵥ (P.BAᵀ *ᵥ xA)) := by
    have hne := (hgam hS).ne'
    rw [hxE, inv_gsmul hne (bsb_unit hBEu hSg)]
    simp only [RRinv, smul_mulVec, mulVec_smul, mulVec_sub, ← mulVec_mulVec, smul_smul,
      mul_inv_cancel₀ hne, one_smul, one_div]
  have hyR' : yR = RRinv P.BE (P.St t) *ᵥ ((1 / P.gam) • (PiR P.BE *ᵥ lh) -
      (PiR P.BE * P.St t * PiU P.BE) *ᵥ (P.BAᵀ *ᵥ xA)) := by
    rw [hyR, hBx]
    have e1 : RRinv P.BE (P.St t) *ᵥ (PiR P.BE *ᵥ lh) = RRinv P.BE (P.St t) *ᵥ lh := by
      rw [mulVec_mulVec, rr_pr hBEu hSg]
    have m1 : RRinv P.BE (P.St t) * P.St t =
        PiR P.BE + RRinv P.BE (P.St t) * (PiR P.BE * P.St t * PiU P.BE) := by
      calc RRinv P.BE (P.St t) * P.St t = RRinv P.BE (P.St t) * P.St t * (PiR P.BE + PiU P.BE) := by
            rw [pr_add_pu hBEu, Matrix.mul_one]
        _ = RRinv P.BE (P.St t) * P.St t * PiR P.BE + RRinv P.BE (P.St t) * P.St t * PiU P.BE :=
            Matrix.mul_add _ _ _
        _ = _ := by
            rw [rr_sg_pr hBEu hSg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, rr_pr hBEu hSg]
    have e2 : RRinv P.BE (P.St t) *ᵥ (P.St t *ᵥ (P.BAᵀ *ᵥ xA)) =
        PiR P.BE *ᵥ (P.BAᵀ *ᵥ xA) + RRinv P.BE (P.St t) *ᵥ ((PiR P.BE * P.St t * PiU P.BE) *ᵥ (P.BAᵀ *ᵥ xA)) := by
      rw [mulVec_mulVec, m1, add_mulVec, mulVec_mulVec (P.BAᵀ *ᵥ xA)]
    rw [mulVec_sub, mulVec_sub, mulVec_smul, mulVec_smul, e1, e2]
    abel
  refine ⟨hyR', ?_, fun h0 => ?_⟩
  · show xE = _
    rw [hyR, add_sub_cancel_left]
    simp only [BEplus, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBEu, 
      one_mulVec]
  · rw [hyR', h0, zero_mulVec, sub_zero, mulVec_smul]

theorem fundProblem : FundProblem := by
  intro K N M P hS
  refine ⟨red_setting hS, fun t ht => ⟨fun xm m => ?_, fun xA m => ?_, fun m => ?_⟩⟩
  · funext i
    rw [joint_policy hS ht xm m, Sum.elim_inl]
  · exact (aimThm (Fin N) (Fin K ⊕ Fin N) P.red (red_setting hS) t ht).1 xA m
  · show (P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t))⁻¹ *ᵥ (Gred P.BA P.BE (P.St t) *ᵥ m - 0) = _
    rw [sub_zero, Gred]
    congr 1
    have hm : m = Sum.elim (fun k => m (Sum.inl k)) (fun i => m (Sum.inr i)) := by
      funext i; cases i <;> rfl
    conv_lhs => rw [hm]
    rw [fromCols_mulVec_sumElim, one_mulVec, ← mulVec_mulVec, add_comm]

/-! ### Part 4: the leak -/

section LeakSec

variable {BE : Matrix (Fin M) (Fin K) ℝ} (hBE' : IsUnit (BE * BEᵀ).det)
  {Sg : Matrix (Fin K) (Fin K) ℝ} (hSg' : Sg.PosDef)
include hBE' hSg'

/-- `J' = Π_U(I - Σ~Σ~_RR⁻¹)`. -/
lemma jt_pu : (Jmap BE Sg)ᵀ = PiU BE * (1 - Sg * RRinv BE Sg) := by
  simp only [Jmap, transpose_sub, transpose_mul, pu_symm hBE', pr_symm hBE', rr_sym hBE' hSg',
    sg_sym hBE' hSg']
  rw [rr_pr hBE' hSg', Matrix.mul_assoc, Matrix.mul_assoc, pr_rr hBE' hSg', Matrix.mul_sub,
    Matrix.mul_one]

/-- `Σ~_{U.R} = Π_U X Π_U`. -/
lemma schur_pu : Schur BE Sg =
    PiU BE * (Sg - Sg * PiR BE * RRinv BE Sg * PiR BE * Sg) * PiU BE := by
  simp only [Schur, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

end LeakSec

section LeakP

variable {P : Leak K N M} (hS : P.Setting)
include hS

lemma gred_u {s : ℕ} {v : Fin K → ℝ} (hv : PiR P.BE *ᵥ v = 0) :
    Gred P.BA P.BE (P.St s) *ᵥ Sum.elim v 0 = P.BA *ᵥ v := by
  rw [Gred, fromCols_mulVec_sumElim, mulVec_zero, add_zero, ← mulVec_mulVec,
    jt_on_u (hBE hS) (hSt hS s) hv]

lemma red_C_L {s : ℕ} (hs : s < P.T) : P.red.C s = P.LA * P.red.L s := by
  obtain ⟨-, eC, -⟩ := LQ.ric_lt P.red (show s < P.red.T from hs)
  rw [eC, LQ.L, Matrix.mul_assoc]
  rfl

lemma mseq_last (_hT : 1 ≤ P.T) : P.Mseq (P.T - 1) = 1 := by
  simp [Leak.Mseq, Leak.MK]

lemma mseq_step {t : ℕ} (ht : t + 1 < P.T) :
    P.Mseq t = 1 + P.rho • (P.LA * (P.red.D (t + 1))⁻¹ * P.Mseq (t + 1)) := by
  have h1 : P.T - 1 - t = (P.T - 1 - (t + 1)) + 1 := by omega
  have h2 : P.T - 1 - (P.T - 1 - (t + 1)) = t + 1 := by omega
  simp only [Leak.Mseq, h1, Leak.MK, h2]

/-- The sensitivity to `λ̂` along `v ∈ L_E^⊥` is `D_t⁻¹ M_t B^A v`. -/
lemma sens {v : Fin K → ℝ} (hv : PiR P.BE *ᵥ v = 0) :
    ∀ t, t < P.T → P.red.L t *ᵥ Sum.elim v 0 = (P.red.D t)⁻¹ *ᵥ (P.Mseq t *ᵥ (P.BA *ᵥ v)) := by
  suffices h : ∀ k t, P.T - 1 - t = k → t < P.T →
      P.red.L t *ᵥ Sum.elim v 0 = (P.red.D t)⁻¹ *ᵥ (P.Mseq t *ᵥ (P.BA *ᵥ v)) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t hk ht
    have htT : t = P.T - 1 := by omega
    have hC : P.red.C (t + 1) = 0 := LQ.C_ge P.red (show P.red.T ≤ t + 1 by show P.T ≤ t + 1; omega)
    have hG : P.red.G t = Gred P.BA P.BE (P.St t) := rfl
    rw [LQ.L, hC, smul_zero, add_zero, ← mulVec_mulVec, hG, gred_u hS hv, htT, mseq_last hS (by omega),
      one_mulVec]
  | succ k ih =>
    intro t hk ht
    have ht1 : t + 1 < P.T := by omega
    have hih := ih (t + 1) (by omega) ht1
    have hG : P.red.G t = Gred P.BA P.BE (P.St t) := rfl
    rw [LQ.L, ← mulVec_mulVec, add_mulVec, hG, gred_u hS hv, smul_mulVec, red_C_L hS ht1,
      ← mulVec_mulVec, hih, mseq_step hS ht1]
    simp only [mulVec_mulVec, mulVec_add, mulVec_smul, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, add_mulVec, smul_mulVec, Matrix.mul_assoc]
    rfl

/-- The symmetric-part lemma. -/
lemma msym {t : ℕ} (ht : t + 1 < P.T) {R : Matrix (Fin N) (Fin N) ℝ} (hRs : Rᵀ = R)
    (hRR : R * R = P.LA) (hRu : IsUnit R)
    (hpd : (R⁻¹ * P.Mseq (t + 1) * R + (R⁻¹ * P.Mseq (t + 1) * R)ᵀ).PosDef) :
    IsUnit (P.Mseq t).det := by
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRu
  have hRi : R⁻¹ * R = 1 := nonsing_inv_mul R hRd
  have hRi' : R * R⁻¹ = 1 := mul_nonsing_inv R hRd
  have hDpd := LQ.D_pd (red_setting hS) (t + 1)
  set Mp := P.Mseq (t + 1)
  set D := P.red.D (t + 1)
  set S := R * D⁻¹ * R
  have hSpsd : S.PosSemidef := by
    have := hDpd.inv.posSemidef.conjTranspose_mul_mul_same R
    rwa [ct_eq, hRs] at this
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  rw [← sub_eq_zero]
  set v := a - b
  have hv : P.Mseq t *ᵥ v = 0 := by simp only [v, mulVec_sub, hab, sub_self]
  set u := R⁻¹ *ᵥ v
  set w := (R⁻¹ * Mp * R) *ᵥ u
  -- `u + ρ S w = 0`
  have huw : u + P.rho • (S *ᵥ w) = 0 := by
    have h := congrArg (R⁻¹ *ᵥ ·) hv
    simp only [mulVec_zero] at h
    rw [mseq_step hS ht, add_mulVec, one_mulVec, smul_mulVec, mulVec_add, mulVec_smul] at h
    rw [← h]
    congr 2
    have hRRi : ∀ X : Matrix (Fin N) (Fin N) ℝ, R * (R⁻¹ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hRi', Matrix.one_mul]
    have hRiR : ∀ X : Matrix (Fin N) (Fin N) ℝ, R⁻¹ * (R * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hRi, Matrix.one_mul]
    simp only [w, u, S, mulVec_mulVec, Matrix.mul_assoc]
    rw [← hRR]
    simp only [Matrix.mul_assoc, hRRi, hRiR, hRi', Matrix.mul_one]
    rfl
  have hwS := hSpsd.dotProduct_mulVec_nonneg w
  simp only [star_trivial] at hwS
  have hwu : w ⬝ᵥ u = -(P.rho * (w ⬝ᵥ (S *ᵥ w))) := by
    have : u = -(P.rho • (S *ᵥ w)) := eq_neg_of_add_eq_zero_left huw
    rw [this, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have hle : w ⬝ᵥ u ≤ 0 := by rw [hwu]; have := mul_nonneg hS.2.1 hwS; linarith
  by_contra hne
  have hu0 : u ≠ 0 := by
    intro h0
    apply hne
    have : R *ᵥ u = v := by simp only [u, mulVec_mulVec, hRi', one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hpos := hpd.dotProduct_mulVec_pos hu0
  simp only [star_trivial, add_mulVec, dotProduct_add] at hpos
  have e : u ⬝ᵥ ((R⁻¹ * Mp * R)ᵀ *ᵥ u) = u ⬝ᵥ ((R⁻¹ * Mp * R) *ᵥ u) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  rw [e] at hpos
  have : u ⬝ᵥ ((R⁻¹ * Mp * R) *ᵥ u) = w ⬝ᵥ u := dotProduct_comm _ _
  linarith

/-- Loewner-antitone inverse. -/
lemma inv_anti {n : ℕ} {D1 D2 : Matrix (Fin n) (Fin n) ℝ} (h1 : D1.PosDef) (h2 : D2.PosDef)
    (h : (D1 - D2).PosSemidef) : (D2⁻¹ - D1⁻¹).PosSemidef := by
  have s1 := transpose_of_psd h1.posSemidef
  have s2 := transpose_of_psd h2.posSemidef
  refine psd_of (by rw [transpose_sub, inv_sym s1, inv_sym s2]) fun x => ?_
  set y := D1⁻¹ *ᵥ x
  have hy : D1 *ᵥ y = x := by simp only [y, mulVec_mulVec, mul_nonsing_inv _ (pd_unit h1), one_mulVec]
  set z := D2⁻¹ *ᵥ x
  have hz : D2 *ᵥ z = x := by simp only [z, mulVec_mulVec, mul_nonsing_inv _ (pd_unit h2), one_mulVec]
  have q1 := h2.posSemidef.dotProduct_mulVec_nonneg (y - z)
  have q2 := h.dotProduct_mulVec_nonneg y
  simp only [star_trivial, mulVec_sub, sub_dotProduct, dotProduct_sub, sub_mulVec] at q1 q2
  rw [hz] at q1
  have e1 : x ⬝ᵥ y = y ⬝ᵥ (D1 *ᵥ y) := by rw [hy, dotProduct_comm]
  have e2 : z ⬝ᵥ (D2 *ᵥ y) = y ⬝ᵥ x := by rw [← hz, sym_dot s2 z y, hz]
  have e3 : z ⬝ᵥ x = x ⬝ᵥ z := dotProduct_comm _ _
  have e4 : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm _ _
  rw [sub_mulVec, dotProduct_sub]
  change 0 ≤ x ⬝ᵥ z - x ⬝ᵥ y
  have e5 : y ⬝ᵥ (D2 *ᵥ z) = y ⬝ᵥ x := by rw [hz]
  linarith

/-- The difference of the two `D_t`: the risk term plus the difference of the continuations. -/
lemma D_diff (s : ℕ) :
    P.red.D s - P.red0.D s =
      P.gam • (P.BA * Schur P.BE (P.St s) * P.BAᵀ) + P.rho • (P.red.A (s + 1) - P.red0.A (s + 1)) := by
  show (P.LA + P.gam • SigRed P.BA P.BE (P.St s) (P.SAt s) + P.rho • P.red.A (s + 1)) -
    (P.LA + P.gam • P.SAt s + P.rho • P.red0.A (s + 1)) = _
  rw [SigRed, smul_add, smul_sub]
  abel

lemma delta_psd (s : ℕ) : (P.BA * Schur P.BE (P.St s) * P.BAᵀ).PosSemidef := by
  have := (schur_psd (hBE hS) (hSt hS s)).mul_mul_conjTranspose_same P.BA
  rwa [ct_eq] at this

/-- The risk term makes the reduced `A_t` larger in the Loewner order at every review. -/
lemma red_A_mono : ∀ s, (P.red.A s - P.red0.A s).PosSemidef := by
  have hR := red_setting hS
  have hR0 := red0_setting hS
  suffices h : ∀ k s, P.T - s = k → (P.red.A s - P.red0.A s).PosSemidef from fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [LQ.A_ge P.red (show P.red.T ≤ s by show P.T ≤ s; omega),
      LQ.A_ge P.red0 (show P.red0.T ≤ s by show P.T ≤ s; omega), sub_zero]
    exact PosSemidef.zero
  | succ k ih =>
    intro s hs
    have hsT : s < P.T := by omega
    have hih := ih (s + 1) (by omega)
    obtain ⟨eA, -, -⟩ := LQ.ric_lt P.red (show s < P.red.T from hsT)
    obtain ⟨fA, -, -⟩ := LQ.ric_lt P.red0 (show s < P.red0.T from hsT)
    have hDpsd : (P.red.D s - P.red0.D s).PosSemidef := by
      rw [D_diff hS s]
      exact ((delta_psd hS s).smul (hgam hS).le).add (hih.smul hS.2.1)
    have hinv := inv_anti hS (LQ.D_pd hR s) (LQ.D_pd hR0 s) hDpsd
    rw [eA, fA]
    have e : P.red.Lam - P.red.Lam * (P.red.D s)⁻¹ * P.red.Lam -
        (P.red0.Lam - P.red0.Lam * (P.red0.D s)⁻¹ * P.red0.Lam) =
        P.LAᴴ * ((P.red0.D s)⁻¹ - (P.red.D s)⁻¹) * P.LA := by
      rw [ct_eq, transpose_of_psd (hLA hS).posSemidef]
      show P.LA - P.LA * (P.red.D s)⁻¹ * P.LA - (P.LA - P.LA * (P.red0.D s)⁻¹ * P.LA) = _
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e]
    exact hinv.conjTranspose_mul_mul_same P.LA

end LeakP

lemma dot_sand {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (B : Matrix n n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((A * B * Aᵀ) *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (B *ᵥ (Aᵀ *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

section LeakP2

variable {P : Leak K N M} (hS : P.Setting)
include hS

lemma pu_idem : PiU P.BE * PiU P.BE = PiU P.BE := by
  rw [PiU, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, pr_idem (hBE hS)]
  abel

lemma ba_pu (h : PiU P.BE * P.BAᵀ = 0) : P.BA * PiU P.BE = 0 := by
  have := congrArg transpose h
  rwa [transpose_mul, transpose_transpose, pu_symm (hBE hS), transpose_zero] at this

/-- Some direction carries a positive risk term when a fund loading is unreachable. -/
lemma delta_pos (h : PiU P.BE * P.BAᵀ ≠ 0) (s : ℕ) :
    ∃ x : Fin N → ℝ, 0 < x ⬝ᵥ ((P.BA * Schur P.BE (P.St s) * P.BAᵀ) *ᵥ x) := by
  have hBEu := hBE hS
  have hSg := hSt hS s
  obtain ⟨x, hx⟩ : ∃ x, PiU P.BE *ᵥ (P.BAᵀ *ᵥ x) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply h
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨x, ?_⟩
  set y := PiU P.BE *ᵥ (P.BAᵀ *ᵥ x)
  have hy : PiR P.BE *ᵥ y = 0 := by
    simp only [y, mulVec_mulVec, ← Matrix.mul_assoc, pr_pu hBEu, Matrix.zero_mul, zero_mulVec]
  have hpos := schur_pd_u hBEu hSg hy hx
  set X := P.St s - P.St s * PiR P.BE * RRinv P.BE (P.St s) * PiR P.BE * P.St s
  have hsch := schur_pu hBEu hSg
  have hPUy : PiU P.BE *ᵥ y = y := by simp only [y, mulVec_mulVec, ← Matrix.mul_assoc, pu_idem hS]
  have e1 : x ⬝ᵥ ((P.BA * Schur P.BE (P.St s) * P.BAᵀ) *ᵥ x) = y ⬝ᵥ (X *ᵥ y) := by
    rw [dot_sand, hsch]
    conv_lhs => rw [show PiU P.BE * X * PiU P.BE = PiU P.BE * X * (PiU P.BE)ᵀ by rw [pu_symm hBEu]]
    rw [dot_sand, pu_symm hBEu]
  have e2 : y ⬝ᵥ (Schur P.BE (P.St s) *ᵥ y) = y ⬝ᵥ (X *ᵥ y) := by
    rw [hsch, show PiU P.BE * X * PiU P.BE = PiU P.BE * X * (PiU P.BE)ᵀ by rw [pu_symm hBEu], dot_sand,
      pu_symm hBEu, hPUy]
  linarith

/-- The fund policy does not respond to `λ̂` when every fund loading is replicable. -/
lemma sens_zero (h : PiU P.BE * P.BAᵀ = 0) (v : Fin K → ℝ) :
    ∀ t, t < P.T → P.red.L t *ᵥ Sum.elim v 0 = 0 := by
  have hG0 : ∀ s, Gred P.BA P.BE (P.St s) *ᵥ Sum.elim v 0 = 0 := fun s => by
    rw [Gred, fromCols_mulVec_sumElim, mulVec_zero, add_zero, jt_pu (hBE hS) (hSt hS s),
      ← Matrix.mul_assoc, ba_pu hS h, Matrix.zero_mul, zero_mulVec]
  suffices hh : ∀ k t, P.T - 1 - t = k → t < P.T → P.red.L t *ᵥ Sum.elim v 0 = 0 from
    fun t => hh _ t rfl
  intro k
  induction k with
  | zero =>
    intro t hk ht
    have hC : P.red.C (t + 1) = 0 := LQ.C_ge P.red (show P.red.T ≤ t + 1 by show P.T ≤ t + 1; omega)
    have hG : P.red.G t = Gred P.BA P.BE (P.St t) := rfl
    rw [LQ.L, hC, smul_zero, add_zero, ← mulVec_mulVec, hG, hG0, mulVec_zero]
  | succ k ih =>
    intro t hk ht
    have ht1 : t + 1 < P.T := by omega
    have hG : P.red.G t = Gred P.BA P.BE (P.St t) := rfl
    rw [LQ.L, ← mulVec_mulVec, add_mulVec, hG, hG0, smul_mulVec, red_C_L hS ht1, ← mulVec_mulVec,
      ih (t + 1) (by omega) ht1, mulVec_zero, smul_zero, add_zero, mulVec_zero]

end LeakP2

theorem theLeak : TheLeak := by
  refine ⟨fun K M BE Sg v hBE' hSg hv => jt_on_u hBE' hSg hv, fun K N M P hS => ?_⟩
  have hBEu := hBE hS
  have hR := red_setting hS
  obtain ⟨R, hRs, hRR, hRu⟩ := sqrt_exists (hLA hS)
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRu
  have hRi : R⁻¹ * R = 1 := nonsing_inv_mul R hRd
  have hRi' : R * R⁻¹ = 1 := mul_nonsing_inv R hRd
  -- symmetric parts for `M_{T-1} = I` and `M_{T-2} = I + ρΛ_A D⁻¹`
  have hpd1 : (R⁻¹ * 1 * R + (R⁻¹ * 1 * R)ᵀ).PosDef := by
    rw [Matrix.mul_one, hRi, transpose_one]
    exact PosDef.one.add PosDef.one
  have hpd2 : ∀ s, (R⁻¹ * (1 + P.rho • (P.LA * (P.red.D s)⁻¹ * 1)) * R +
      (R⁻¹ * (1 + P.rho • (P.LA * (P.red.D s)⁻¹ * 1)) * R)ᵀ).PosDef := by
    intro s
    have hD := LQ.D_pd hR s
    have hDs := inv_sym (transpose_of_psd hD.posSemidef)
    have e : R⁻¹ * (1 + P.rho • (P.LA * (P.red.D s)⁻¹ * 1)) * R = 1 + P.rho • (R * (P.red.D s)⁻¹ * R) := by
      rw [← hRR, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRi, Matrix.mul_smul,
        Matrix.smul_mul]
      congr 2
      simp only [← Matrix.mul_assoc, hRi, Matrix.one_mul]
    have hSp : (R * (P.red.D s)⁻¹ * R).PosSemidef := by
      have := hD.inv.posSemidef.conjTranspose_mul_mul_same R
      rwa [ct_eq, hRs] at this
    have hSs : (R * (P.red.D s)⁻¹ * R)ᵀ = R * (P.red.D s)⁻¹ * R := transpose_of_psd hSp
    rw [e, transpose_add, transpose_one, transpose_smul, hSs]
    exact (PosDef.one.add_posSemidef (hSp.smul hS.2.1)).add (PosDef.one.add_posSemidef (hSp.smul hS.2.1))
  refine ⟨fun t ht v hv => sens hS hv t ht, fun h => ⟨fun Sg hSg => ?_, fun t => ?_,
      fun t ht v => sens_zero hS h v t ht⟩, fun t ht v hv hBv hMu => ?_, mseq_last hS,
    fun hT t ht => ?_, fun t ht R' hRs' hRR' hRu' hpd => msym hS ht hRs' hRR' hRu' hpd,
    fun t => ⟨delta_psd hS t, fun x hx hx0 => schur_pd_u hBEu (hSt hS t) hx hx0, fun h hz => ?_⟩,
    fun h t ht => ?_⟩
  · rw [jt_pu hBEu hSg, ← Matrix.mul_assoc, ba_pu hS h, Matrix.zero_mul]
  · rw [SigRed, schur_pu hBEu (hSt hS t), ← Matrix.mul_assoc, ← Matrix.mul_assoc, ba_pu hS h]
    simp only [Matrix.zero_mul, add_zero]
  · rw [sens hS hv t ht]
    have hD := LQ.D_pd hR t
    have hDi : Function.Injective ((P.red.D t)⁻¹).mulVec := (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ (pd_unit hD)))
    have hMi : Function.Injective (P.Mseq t).mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hMu)
    intro h0
    exact hBv (hMi ((hDi (h0.trans (mulVec_zero _).symm)).trans (mulVec_zero _).symm))
  · -- `T ≤ 3`
    rcases Nat.lt_or_ge (t + 1) P.T with h1 | h1
    · refine msym hS h1 hRs hRR hRu ?_
      rcases Nat.lt_or_ge (t + 2) P.T with h2 | h2
      · have hlast : P.Mseq (t + 2) = 1 := by
          rw [show t + 2 = P.T - 1 by omega]; exact mseq_last hS (by omega)
        rw [mseq_step hS h2, hlast]
        exact hpd2 (t + 1 + 1)
      · have hlast : P.Mseq (t + 1) = 1 := by
          rw [show t + 1 = P.T - 1 by omega]; exact mseq_last hS (by omega)
        rw [hlast]
        exact hpd1
    · rw [show t = P.T - 1 by omega, mseq_last hS (by omega), det_one]
      exact isUnit_one
  · obtain ⟨x, hx⟩ := delta_pos hS h t
    rw [hz, zero_mulVec, dotProduct_zero] at hx
    exact lt_irrefl _ hx
  · -- the risk term changes `K_t`
    have hR0 := red0_setting hS
    intro hK
    obtain ⟨x, hx⟩ := delta_pos hS h t
    have hLAu : IsUnit P.LA.det := pd_unit (hLA hS)
    have hDeq : P.red.D t = P.red0.D t := by
      have h1 : (P.red.D t)⁻¹ = (P.red0.D t)⁻¹ := by
        have := congrArg (· * P.LA⁻¹) hK
        have e1 : P.red.Lam = P.LA := rfl
        have e2 : P.red0.Lam = P.LA := rfl
        simpa only [LQ.K, e1, e2, Matrix.mul_assoc, mul_nonsing_inv _ hLAu, Matrix.mul_one] using this
      have := congrArg (·⁻¹) h1
      simpa only [nonsing_inv_nonsing_inv _ (pd_unit (LQ.D_pd hR t)),
        nonsing_inv_nonsing_inv _ (pd_unit (LQ.D_pd hR0 t))] using this
    have hdiff := D_diff hS t
    rw [hDeq, sub_self] at hdiff
    have hA := red_A_mono hS (t + 1)
    have q := hA.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at q
    have := congrArg (fun Z => x ⬝ᵥ (Z *ᵥ x)) hdiff
    simp only [zero_mulVec, dotProduct_zero, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul] at this
    nlinarith [hgam hS, hS.2.1, mul_nonneg hS.2.1 q, mul_pos (hgam hS) hx]

/-! ### Part 5: learning -/

section Lim

lemma tendsto_mmul {α m n p : Type} [Fintype n] {l : Filter α} {f : α → Matrix m n ℝ}
    {g : α → Matrix n p ℝ} {a : Matrix m n ℝ} {b : Matrix n p ℝ} (hf : Filter.Tendsto f l (nhds a))
    (hg : Filter.Tendsto g l (nhds b)) : Filter.Tendsto (fun x => f x * g x) l (nhds (a * b)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

lemma tendsto_minv {α n : Type} [Fintype n] [DecidableEq n] {l : Filter α} {f : α → Matrix n n ℝ}
    {a : Matrix n n ℝ} (hf : Filter.Tendsto f l (nhds a)) (ha : IsUnit a.det) :
    Filter.Tendsto (fun x => (f x)⁻¹) l (nhds a⁻¹) := by
  have hc : ContinuousAt Inv.inv a := continuousAt_matrix_inv a (by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero)
  exact hc.tendsto.comp hf

end Lim

theorem learning : Learning := by
  intro K M BE Sf P0 hBEu hSf hP0
  have hpd := fun t => (kal_pd_info (H := (1 : Matrix (Fin K) (Fin K) ℝ)) hP0 hSf t)
  have hSt : ∀ t, (Sf + kal P0 1 Sf t).PosDef := fun t => hSf.add_posSemidef (hpd t).1.posSemidef
  -- `P^λ_t → 0`
  have hPt : Filter.Tendsto (fun t : ℕ => kal P0 1 Sf t) Filter.atTop (nhds 0) := by
    have hinv0 : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hX : Filter.Tendsto (fun t : ℕ => (t : ℝ)⁻¹ • P0⁻¹ + Sf⁻¹) Filter.atTop (nhds (Sf⁻¹)) := by
      have := (hinv0.smul_const P0⁻¹).add_const Sf⁻¹
      simpa using this
    have hXi := tendsto_minv hX (pd_unit hSf.inv)
    rw [nonsing_inv_nonsing_inv _ (pd_unit hSf)] at hXi
    have hlim := hinv0.smul hXi
    rw [zero_smul] at hlim
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have htr : (0 : ℝ) < t := by exact_mod_cast ht
    have hXpd : ((t : ℝ)⁻¹ • P0⁻¹ + Sf⁻¹).PosDef :=
      (hP0.inv.smul (inv_pos.mpr htr)).add hSf.inv
    have e : (kal P0 1 Sf t)⁻¹ = (t : ℝ) • ((t : ℝ)⁻¹ • P0⁻¹ + Sf⁻¹) := by
      rw [(hpd t).2, transpose_one, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul,
        mul_inv_cancel₀ htr.ne', one_smul]
    have := congrArg (fun Z => Z⁻¹) e
    rw [nonsing_inv_nonsing_inv _ (pd_unit (hpd t).1), inv_gsmul htr.ne' (pd_unit hXpd)] at this
    exact this.symm
  have hS' : Filter.Tendsto (fun t : ℕ => Sf + kal P0 1 Sf t) Filter.atTop (nhds Sf) := by
    simpa using hPt.const_add Sf
  -- continuity of `Σ~_RR⁻¹`, the Schur complement and `J`
  have hRR : Filter.Tendsto (fun t : ℕ => RRinv BE (Sf + kal P0 1 Sf t)) Filter.atTop
      (nhds (RRinv BE Sf)) := by
    unfold RRinv
    refine tendsto_mmul (tendsto_mmul tendsto_const_nhds ?_) tendsto_const_nhds
    exact tendsto_minv (tendsto_mmul (tendsto_mmul tendsto_const_nhds hS') tendsto_const_nhds)
      (bsb_unit hBEu hSf)
  refine ⟨fun t => ?_, ?_, ?_, fun v hv => jt_on_u hBEu hSf hv⟩
  · refine schur_mono hBEu (hSt t) (hSt (t + 1)) ?_
    have := kal_psd_step (H := (1 : Matrix (Fin K) (Fin K) ℝ)) hP0 hSf t
    rwa [add_sub_add_left_eq_sub]
  · unfold Schur
    refine Filter.Tendsto.sub (tendsto_mmul (tendsto_mmul tendsto_const_nhds hS') tendsto_const_nhds) ?_
    exact tendsto_mmul (tendsto_mmul (tendsto_mmul (tendsto_mmul tendsto_const_nhds hS')
      tendsto_const_nhds) hRR) (tendsto_mmul (tendsto_mmul tendsto_const_nhds hS') tendsto_const_nhds)
  · unfold Jmap
    refine Filter.Tendsto.sub tendsto_const_nhds ?_
    exact tendsto_mmul (tendsto_mmul tendsto_const_nhds hRR)
      (tendsto_mmul (tendsto_mmul tendsto_const_nhds hS') tendsto_const_nhds)

/-- Claim 031, parts 1-5. -/
theorem proof : Standalone.M5MissingDirectionLeak.statement :=
  ⟨coordinates, etfExposure, fundProblem, theLeak, stationary, learning⟩

end

end Novel.M5MissingDirectionLeakProof

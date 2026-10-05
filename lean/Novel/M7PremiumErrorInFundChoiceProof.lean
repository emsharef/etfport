import Novel.M7TwoStageExactnessLossProof
import Standalone.M7PremiumErrorInFundChoice

/-!
# Claim 105: proof

Parts 1 and 2's joint optima are claim 104's 2a (`spanning`) and 2c (`unreach_joint`). The
learning limits are claim 031's part 5 read through a continuous map. Parts 2b-2d and part 3's
readings are one-variable facts about the clipped band holding. The clip is `1`-Lipschitz, and the
band edges move with the reduced alpha at rate `1/c`. The loss bracket is claim 104's 3b. The naive
rule's loss uses the spanning split `Q = G(b) + Σ ψ_i`. Re-optimizing the ETFs reaches `b_TB`, because
the ETF bounds and the budget are slack, so the exposure term cancels.
-/

namespace Novel.M7PremiumErrorInFundChoiceProof

open Filter Topology Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M7PremiumErrorInFundChoice Novel.M7TwoStageExactnessLossProof
open Standalone.M2TwoStageSeparation (Gf Inputs sigF sqN)
open Standalone.M5MissingDirectionLeak (PiR Jmap Schur)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Part 1 -/

theorem noLeak : NoLeak := by
  intro m K S₁ S₂ _ _ D₁ D₂ θ₁ θ₂ Sf₁ Sf₂ v hI₁ hI₂ hF₁ hF₂ hα hγ hk w₁ hw₁ hm₁ hc₁ hE₁ w₂ hw₂ hm₂
    hc₂ hE₂ k
  obtain ⟨-, h₁, -⟩ := spanning m K S₁ D₁ θ₁ Sf₁ v hI₁ hF₁ w₁ hw₁ hm₁ hc₁ hE₁
  obtain ⟨-, h₂, -⟩ := spanning m K S₂ D₂ θ₂ Sf₂ v hI₂ hF₂ w₂ hw₂ hm₂ hc₂ hE₂
  obtain ⟨e1, e2, e3, e4⟩ := hk k
  refine ⟨?_, h₁ k⟩
  rw [h₁ k, h₂ k, hα, hγ, e1, e2, e3, e4]

theorem markowitzLoss : MarkowitzLoss := by
  intro K Sg γ lam lamHat hSg hγ
  have hU := Novel.M5PartialAdjustmentSplitProof.pd_unit hSg
  have hsym : (Sg⁻¹)ᵀ = Sg⁻¹ := Novel.M5PartialAdjustmentSplitProof.inv_sym
    (Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hSg.posSemidef)
  rw [Novel.M5MissingDirectionLeakProof.inv_gsmul hγ.ne' hU]
  have h1 : ∀ x, Sg *ᵥ ((γ⁻¹ • Sg⁻¹) *ᵥ x) = γ⁻¹ • x := fun x => by
    rw [smul_mulVec, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  rw [h1, h1]
  have hs := Novel.M5PartialAdjustmentSplitProof.sym_dot hsym lam lamHat
  simp only [smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul, mulVec_sub, dotProduct_sub,
    sub_dotProduct]
  rw [dotProduct_comm (Sg⁻¹ *ᵥ lam) lam, dotProduct_comm (Sg⁻¹ *ᵥ lamHat) lamHat, hs]
  field_simp
  ring

/-! ### Part 2: the joint optimum -/

theorem unreachJoint : UnreachJoint := by
  intro m n K S _ D θ Sf v i hI hOU wJ hwJ hmaxJ hsJ
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ := hOU
  have hsig : sigF D = Sf := hR.1
  have hkp : ∀ l, 0 ≤ D.kplus l := fun l => (hI.2.1 l).1
  have hkm : ∀ l, 0 ≤ D.kminus l := fun l => (hI.2.1 l).2
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  obtain ⟨b0, hb0⟩ : ∃ b0, D.gamma • (sigF D *ᵥ b0) = θ.lam :=
    ⟨(D.gamma • Sf)⁻¹ *ᵥ θ.lam, by
      rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]⟩
  have hsU : 0 < D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i) := sU_pos hBE hSf hu
  obtain ⟨hJ1, hJ2, -, hETF⟩ :=
    unreach_joint θ hI ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ hwJ hmaxJ hsJ hb0
  refine ⟨eq_bandHold (mul_pos hγ (add_pos (hv i) hsU)) (hkp _) (hkm _) (hwJ.1 _) hJ1,
    fun k hk => eq_bandHold (mul_pos hγ (hv k)) (hkp _) (hkm _) (hwJ.1 _) fun y _ => hJ2 k hk y, hETF⟩

theorem sameShift : SameShift := by
  intro m n K S _ D θ θ' Sf v i hI hOU hα hp w hw hm hs w' hw' hm' hs'
  rw [(unreachJoint m n K S D θ Sf v i hI hOU w hw hm hs).1,
    (unreachJoint m n K S D θ' Sf v i hI hOU w' hw' hm' hs').1, hp, hα]

/-! ### Part 2a: narrowing and learning -/

theorem narrowing : Narrowing := by
  intro K M BE Sg β alpha v γ kp km hBE hSg hv hγ
  have h0 : 0 ≤ β ⬝ᵥ (Schur BE Sg *ᵥ β) := by
    have := (Novel.M5MissingDirectionLeakProof.schur_psd hBE hSg).dotProduct_mulVec_nonneg β
    simpa using this
  refine ⟨by linarith, ?_⟩
  have hs : 0 < v + β ⬝ᵥ (Schur BE Sg *ᵥ β) := by linarith
  field_simp
  ring

theorem learningLeak : LearningLeak := by
  intro K M BE Sf P0 β lamHat v hBE hSf hP0
  obtain ⟨hmono, hS, hJ, hid⟩ := Novel.M5MissingDirectionLeakProof.learning K M BE Sf P0 hBE hSf hP0
  have hc1 : Continuous (fun Z : Matrix (Fin K) (Fin K) ℝ => v + β ⬝ᵥ (Z *ᵥ β)) := by
    simp only [dotProduct, mulVec]; fun_prop
  have hc2 : Continuous (fun Z : Matrix (Fin K) (Fin K) ℝ => β ⬝ᵥ (Zᵀ *ᵥ lamHat)) := by
    simp only [dotProduct, mulVec, transpose_apply]; fun_prop
  refine ⟨fun t => ?_, (hc1.tendsto _).comp hS, (hc2.tendsto _).comp hJ, hid⟩
  have := (hmono t).dotProduct_mulVec_nonneg β
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
  linarith

/-! ### The clipped band holding -/

section Clip

variable {c kp km xm xbar : ℝ}

/-- The unclipped holding `u = clip(x⁻, lo, hi)`. -/
lemma lo_le_hi (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (alpha : ℝ) :
    (alpha - kp) / c ≤ (alpha + km) / c :=
  div_le_div_of_nonneg_right (by linarith) hc.le

lemma u_lip (hc : 0 < c) (alpha alpha' : ℝ) :
    |max ((alpha' - kp) / c) (min ((alpha' + km) / c) xm) - max ((alpha - kp) / c) (min ((alpha + km) / c) xm)|
      ≤ |alpha' - alpha| / c := by
  have e1 : |(alpha' - kp) / c - (alpha - kp) / c| = |alpha' - alpha| / c := by
    rw [← sub_div, abs_div, abs_of_pos hc]; ring_nf
  have e2 : |(alpha' + km) / c - (alpha + km) / c| = |alpha' - alpha| / c := by
    rw [← sub_div, abs_div, abs_of_pos hc]; ring_nf
  have h2 := abs_min_sub_min_le_max ((alpha' + km) / c) xm ((alpha + km) / c) xm
  rw [e2, sub_self, abs_zero, max_eq_left (by positivity)] at h2
  have h1 := abs_max_sub_max_le_max ((alpha' - kp) / c) (min ((alpha' + km) / c) xm) ((alpha - kp) / c)
    (min ((alpha + km) / c) xm)
  rw [e1] at h1
  exact h1.trans (max_le le_rfl h2)

lemma clip_lip (u u' : ℝ) : |max 0 (min xbar u') - max 0 (min xbar u)| ≤ |u' - u| := by
  have h1 := abs_max_sub_max_le_max 0 (min xbar u') 0 (min xbar u)
  have h2 := abs_min_sub_min_le_max xbar u' xbar u
  rw [sub_self, abs_zero] at h1 h2
  exact h1.trans (max_le (abs_nonneg _) (h2.trans (max_le (abs_nonneg _) le_rfl)))

lemma band_lip (hc : 0 < c) (alpha alpha' : ℝ) :
    |bandHold alpha' c kp km xm xbar - bandHold alpha c kp km xm xbar| ≤ |alpha' - alpha| / c :=
  (clip_lip _ _).trans (u_lip hc alpha alpha')

lemma u_buy {alpha : ℝ} (h : xm < (alpha - kp) / c) :
    max ((alpha - kp) / c) (min ((alpha + km) / c) xm) = (alpha - kp) / c :=
  max_eq_left ((min_le_right _ _).trans h.le)

lemma u_sell (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) {alpha : ℝ} (h : (alpha + km) / c < xm) :
    max ((alpha - kp) / c) (min ((alpha + km) / c) xm) = (alpha + km) / c := by
  rw [min_eq_left h.le, max_eq_right (lo_le_hi hc hkp hkm alpha)]

lemma u_hold {alpha : ℝ} (h1 : (alpha - kp) / c ≤ xm) (h2 : xm ≤ (alpha + km) / c) :
    max ((alpha - kp) / c) (min ((alpha + km) / c) xm) = xm := by
  rw [min_eq_right h2, max_eq_right h1]

lemma clip_in {u : ℝ} (h0 : 0 < u) (h1 : u < xbar) : max 0 (min xbar u) = u := by
  rw [min_eq_right h1.le, max_eq_right h0.le]

theorem move : Move := by
  intro alpha alpha' c kp km xm xbar hc hkp hkm hx
  refine ⟨band_lip hc alpha alpha', fun h1 h2 h3 h4 h5 h6 => ?_, fun h1 h2 h3 h4 h5 h6 => ?_,
    fun h1 h2 h3 h4 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp only [bandHold]
    rw [u_buy h1, u_buy h2, clip_in h3 h5, clip_in h4 h6]
    ring
  · simp only [bandHold]
    rw [u_sell hc hkp hkm h1, u_sell hc hkp hkm h2, clip_in h3 h5, clip_in h4 h6]
    ring
  · simp only [bandHold]
    rw [u_hold h1 h2, u_hold h3 h4]
  · simp only [bandHold]
    rw [max_eq_left ((min_le_right _ _).trans h1), max_eq_left ((min_le_right _ _).trans h2)]
  · simp only [bandHold]
    rw [min_eq_left h1, min_eq_left h2]

lemma continuous_band (c kp km xm xbar : ℝ) : Continuous (fun al => bandHold al c kp km xm xbar) := by
  unfold bandHold; fun_prop

theorem moveVec : MoveVec := by
  intro K β Jm alpha c kp km xm xbar hc hkp hkm hx
  refine ⟨(continuous_band c kp km xm xbar).comp ?_, fun lam lamHat => ?_⟩
  · simp only [dotProduct, mulVec]; fun_prop
  · have := band_lip (kp := kp) (km := km) (xm := xm) (xbar := xbar) hc (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lam))
      (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lamHat))
    rwa [show alpha + β ⬝ᵥ (Jmᵀ *ᵥ lamHat) - (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lam)) =
      β ⬝ᵥ (Jmᵀ *ᵥ (lamHat - lam)) by rw [mulVec_sub, dotProduct_sub]; ring] at this

/-- Above the incumbent iff the band's lower edge is, and the cap leaves room. -/
lemma above_iff (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) (al : ℝ) :
    xm < bandHold al c kp km xm xbar ↔ xm < (al - kp) / c ∧ xm < xbar := by
  constructor
  · intro h
    refine ⟨?_, h.trans_le (bandHold_mem (h0.trans h1)).2⟩
    by_contra hle
    push Not at hle
    have hu : max ((al - kp) / c) (min ((al + km) / c) xm) ≤ xm := max_le hle (min_le_right _ _)
    have : bandHold al c kp km xm xbar ≤ xm := by
      unfold bandHold
      exact max_le h0 ((min_le_right _ _).trans hu)
    linarith
  · rintro ⟨hlo, hx⟩
    unfold bandHold
    rw [u_buy hlo]
    exact lt_of_lt_of_le (lt_min hx hlo) (le_max_right _ _)

lemma below_iff (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) (al : ℝ) :
    bandHold al c kp km xm xbar < xm ↔ (al + km) / c < xm ∧ 0 < xm := by
  constructor
  · intro h
    refine ⟨?_, (bandHold_mem (h0.trans h1)).1.trans_lt h⟩
    by_contra hle
    push Not at hle
    have hu : xm ≤ max ((al - kp) / c) (min ((al + km) / c) xm) :=
      (le_min hle le_rfl).trans (le_max_right _ _)
    have : xm ≤ bandHold al c kp km xm xbar := by
      unfold bandHold
      exact (le_min h1 hu).trans (le_max_right _ _)
    linarith
  · rintro ⟨hhi, hx⟩
    unfold bandHold
    rw [u_sell hc hkp hkm hhi]
    exact max_lt hx (lt_of_le_of_lt (min_le_right _ _) hhi)

end Clip

theorem flip : Flip := by
  intro alpha delta c kp km xm xbar hc hkp hkm h0 h1
  have e1 : ∀ al, xm < (al - kp) / c ↔ kp < al - c * xm := fun al => by
    rw [lt_div_iff₀ hc]; constructor <;> intro h <;> linarith
  have e2 : ∀ al, (al + km) / c < xm ↔ al - c * xm < -km := fun al => by
    rw [div_lt_iff₀ hc]; constructor <;> intro h <;> linarith
  have hA : ∀ d, xm < bandHold (alpha + d) c kp km xm xbar ↔ kp < alpha - c * xm + d ∧ xm < xbar :=
    fun d => by
      rw [above_iff h0 h1, e1]
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩
  have hB : ∀ d, bandHold (alpha + d) c kp km xm xbar < xm ↔ alpha - c * xm + d < -km ∧ 0 < xm :=
    fun d => by
      rw [below_iff hc hkp hkm h0 h1, e2]
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩
  refine ⟨hA delta, hB delta, fun hm1 hm2 hd => ?_, fun hb => ?_⟩
  · have hd1 := (abs_le.mp (hd.trans (min_le_left _ _)))
    have hd2 := (abs_le.mp (hd.trans (min_le_right _ _)))
    apply le_antisymm
    · by_contra h; push Not at h
      have := ((hA delta).mp h).1; linarith
    · by_contra h; push Not at h
      have := ((hB delta).mp h).1; linarith
  · have hb' := (hA 0).mp (by rwa [add_zero])
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, by linarith [hb'.1]⟩
    · by_contra hlt; push Not at hlt
      exact absurd ((hA delta).mpr ⟨by linarith, hb'.2⟩) (not_lt.mpr h)
    · by_contra hlt; push Not at hlt
      have := ((hA delta).mp hlt).1; linarith

/-! ### Part 2d -/

theorem cost : Cost := by
  intro alpha delta c kp km xm xbar hc hkp hkm hx
  have hmem := bandHold_mem (alpha := alpha) (c := c) (kp := kp) (km := km) (xm := xm) hx
  have hmem' := bandHold_mem (alpha := alpha + delta) (c := c) (kp := kp) (km := km) (xm := xm) hx
  have hmax := bandHold_max (alpha := alpha) (xm := xm) hc hkp hkm hx
  have hb := bracket alpha c kp km xm xbar _ _ hc hkp hkm hmem hmax hmem'
  dsimp only at hb ⊢
  obtain ⟨h1, h2, h3⟩ := hb
  have hsq : (bandHold alpha c kp km xm xbar - bandHold (alpha + delta) c kp km xm xbar) ^ 2 =
      (bandHold (alpha + delta) c kp km xm xbar - bandHold alpha c kp km xm xbar) ^ 2 := by ring
  rw [hsq, abs_sub_comm] at h2
  rw [hsq] at h1
  refine ⟨by nlinarith [sq_nonneg (bandHold (alpha + delta) c kp km xm xbar -
    bandHold alpha c kp km xm xbar)], h2, ?_, h3⟩
  have := band_lip (kp := kp) (km := km) (xm := xm) (xbar := xbar) hc alpha (alpha + delta)
  rwa [add_sub_cancel_left] at this

/-! ### Part 3 -/

theorem naiveLoss : NaiveLoss := by
  intro m K S _ D θ Sf v hI hFS wJ hwJ hmaxJ hkJ hEJ wa hwa hmaxa hka hEa
  obtain ⟨hbJ, hfund, -⟩ := spanning m K S D θ Sf v hI hFS wJ hwJ hmaxJ hkJ hEJ
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ⟩ := hFS
  have hsig : sigF D = Sf := hR.1
  have hkp : ∀ l, 0 ≤ D.kplus l := fun l => (hI.2.1 l).1
  have hkm : ∀ l, 0 ≤ D.kminus l := fun l => (hI.2.1 l).2
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  set bTB := (D.gamma • Sf)⁻¹ *ᵥ θ.lam with hbTB
  have hTB : D.gamma • (sigF D *ᵥ bTB) = θ.lam := by
    rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hG := G_TB θ hTB
  have hGmax : ∀ b, Gf D θ b ≤ Gf D θ bTB := fun b => by
    rw [hG b]
    have := Novel.M2TwoStageSeparationProof.sqN_nonneg D hI.2.2.1 (b - bTB)
    nlinarith [hγ]
  have dec := score_span θ hR hcE hkE
  -- re-optimizing the ETFs reaches `b_TB`
  have hAconv : Convex ℝ {w : Inst m K → ℝ | active w = active wa} := by
    intro x hx y hy a b _ _ hab
    show active (a • x + b • y) = active wa
    have e : active (a • x + b • y) = a • active x + b • active y := rfl
    rw [e, show active x = active wa from hx, show active y = active wa from hy, ← add_smul, hab,
      one_smul]
  have hP : ∀ l : Inst m K, l.isRight = true → 0 < wa l ∧ wa l < D.wbar l := by
    rintro (l | l) hl
    · simp at hl
    · exact hEa l
  let z : Inst m K → ℝ := Sum.elim (active wa) ((D.BEᵀ)⁻¹ *ᵥ (bTB - D.BAᵀ *ᵥ active wa))
  have hz : score D z θ ≤ score D wa θ := by
    refine drop_slack_gen _ (fun w => score D w θ) (score_ineq θ hI) hAconv hwa rfl
      (fun w hw hA => hmaxa ⟨hw, hA⟩) hka hP rfl ?_
    rintro (l | l) hl
    · exact hwa.1 (Sum.inl l)
    · simp at hl
  rw [dec, dec wa, realize D hBE] at hz
  have hGa : Gf D θ (exposure D wa) = Gf D θ bTB := by
    apply le_antisymm (hGmax _)
    simp only [z, Sum.elim_inl, active] at hz
    linarith
  have hdiff : score D wJ θ - score D wa θ = ∑ k, (psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (wJ (Sum.inl k)) -
      psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
        (w0 D (Sum.inl k)) (wa (Sum.inl k))) := by
    rw [dec, dec wa, hbJ, hGa, Finset.sum_sub_distrib]; ring
  have hc : ∀ k, 0 < D.gamma * v k := fun k => mul_pos hγ (hv k)
  have hmaxk : ∀ k, IsMaxOn (psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k))) (Set.Icc 0 (D.wbar (Sum.inl k))) (wJ (Sum.inl k)) :=
    fun k => by
      rw [hfund k]
      exact bandHold_max (hc k) (hkp _) (hkm _) ((hwJ.1 (Sum.inl k)).1.trans (hwJ.1 (Sum.inl k)).2)
  have hnn : ∀ k, 0 ≤ psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
      (w0 D (Sum.inl k)) (wJ (Sum.inl k)) - psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (wa (Sum.inl k)) := fun k => by
    have := hmaxk k (hwa.1 (Sum.inl k))
    simp only [Set.mem_ofPred_eq] at this
    linarith
  refine ⟨hdiff, hnn, ⟨fun h => fun k => ?_, fun h => ?_⟩⟩
  · rw [h, sub_self, eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)] at hdiff
    have hk := hdiff k (Finset.mem_univ k)
    rw [← hfund k]
    refine max_unique (hc k) (hkp _) (hkm _) (hwa.1 (Sum.inl k)) (hwJ.1 (Sum.inl k)) (fun y hy => ?_)
      (hmaxk k)
    have := hmaxk k hy
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  · have : ∀ k, wa (Sum.inl k) = wJ (Sum.inl k) := fun k => by rw [h k, hfund k]
    rw [sub_eq_zero.mp (hdiff.trans (Finset.sum_eq_zero fun k _ => by rw [this k, sub_self]))]

theorem zeroIncumbent : ZeroIncumbent := by
  intro alpha c kp km xbar hc hkp hkm hx
  refine ⟨?_, fun a ha => ?_, fun hpos => ?_⟩
  · have := (flip alpha 0 c kp km 0 xbar hc hkp hkm le_rfl hx.le).1
    rw [add_zero, mul_zero, sub_zero, add_zero] at this
    rw [this]
    exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  · have e : psi alpha c kp km 0 0 - psi alpha c kp km 0 a = -(alpha * a - c / 2 * a ^ 2 - kp * a) := by
      simp only [psi, sub_zero, zero_sub, max_self, max_eq_left ha.le,
        max_eq_right (neg_nonpos.mpr ha.le)]
      ring
    refine ⟨e, ?_⟩
    rw [e]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · have hmem := bandHold_mem (alpha := alpha) (c := c) (kp := kp) (km := km) (xm := 0) hx.le
    have h := lower_end hc hkp hkm hmem (bandHold_max hc hkp hkm hx.le) ⟨le_rfl, hx.le⟩
    nlinarith [sq_pos_of_pos hpos]

/-- Claim 105, parts 1-3 (the expectations paper-level). -/
theorem proof : Standalone.M7PremiumErrorInFundChoice.statement :=
  ⟨noLeak, markowitzLoss, unreachJoint, sameShift, narrowing, learningLeak, move, moveVec, flip, cost,
    naiveLoss, zeroIncumbent⟩

end

end Novel.M7PremiumErrorInFundChoiceProof

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.M4BoundedLawRate

/-!
# Proof of claim 015: a worst-case history-length rate for a funded unspanned-factor trade

Self-contained (no claim dependencies; the M4 definitions come from claim 014's statement file).
* **Part 1:** on `F`, `Q(a, p) ≤ q_E + a d(λ - λ₀)`, with equality exactly when the funding
  constraint binds, which gives every optimizer and gap formula.
* **Part 2:** the hard law is the sine-weighted grid. Its common atoms at `λ₀ ± Δ` pair scenario
  `j + 1` with `j`, and the one-record affinity is `cos φ`. The testing inequality
  `2ε ≥ Σ min(P, Q) ≥ aff²/2` (Cauchy–Schwarz) gives `cos(φ)^(2N) ≤ 4ε`. Then
  `-log cos φ ≤ φ²` (from `cos x ≥ 1 - x²/2`) and `4ε ≤ √ε` finish.
* **Part 3:** the finite-sum Chernoff bound comes from the chord bound for `exp` and
  `cosh x ≤ exp(x²/2)`. It puts M4's discrete quantile radius below `r_B`, and the quantile's own
  definition gives coverage `≥ 1 - ε`.
-/

namespace Novel.M4BoundedLawRateProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
  Standalone.M4BoundedLawRate
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

lemma inst_ext (w : Inst 1 1 → ℝ) :
    w = Sum.elim (fun _ => w (Sum.inl 0)) (fun _ => w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

/-! ### Consequences of the ranges -/

lemma A_le_abar {P : Inputs} : P.A ≤ P.abar := min_le_left _ _

section Ranges

variable {P : Inputs} (hP : P.InRange)
include hP

lemma kA1 : 0 < 1 + P.kA := by linarith [hP.2.2.2.2.1]

lemma kE1 : 0 < 1 + P.kE := by linarith [hP.2.2.2.2.2.2.1]

lemma qE_pos : 0 < P.qE := by
  unfold Inputs.qE; exact div_pos (by linarith [hP.2.1]) (kE1 hP)

lemma d_lam0 : P.d * P.lam0 = P.kA + (1 + P.kA) * P.qE := by
  unfold Inputs.lam0; field_simp [hP.1.ne']

lemma lam0_pos : 0 < P.lam0 := by
  unfold Inputs.lam0
  exact div_pos (by nlinarith [hP.2.2.2.2.1, qE_pos hP, kA1 hP]) hP.1

lemma A_pos : 0 < P.A := by
  unfold Inputs.A; exact lt_min hP.2.2.2.2.2.2.2.2.1 (by have := kA1 hP; positivity)

lemma A_fund : (1 + P.kA) * P.A ≤ 1 := by
  have h := min_le_right P.abar (1 / (1 + P.kA))
  have := kA1 hP
  calc (1 + P.kA) * P.A ≤ (1 + P.kA) * (1 / (1 + P.kA)) := mul_le_mul_of_nonneg_left h this.le
    _ = 1 := by field_simp

lemma Dm_pos : 0 < P.Dm := mul_pos hP.1 (A_pos hP)

end Ranges

/-! ### The data -/

section Data

variable (P : Inputs) {S : Type} [Fintype S] (q Z : S → ℝ)

lemma W0_d : W0 (data P q Z) = 1 := by simp [W0, data]

lemma w0_d : w0 (data P q Z) = 0 := by funext i; simp [w0, data]

lemma tau_d (v : Inst 1 1 → ℝ) :
    tau (data P q Z) v = P.kA * max (v (Sum.inl 0)) 0 + P.kE * max (v (Sum.inr 0)) 0 := by
  simp [tau, data, Fintype.sum_sum_type]

lemma cash_d (w : Inst 1 1 → ℝ) : cash (data P q Z) w
    = 1 - (w (Sum.inl 0) + w (Sum.inr 0))
      - (P.kA * max (w (Sum.inl 0)) 0 + P.kE * max (w (Sum.inr 0)) 0) := by
  rw [cash, w0_d, sub_zero, tau_d]
  simp [k0, W0_d, Fintype.sum_sum_type]
  simp [data]

lemma score_d (w : Inst 1 1 → ℝ) (θ : Fin 3 → ℝ) : score (data P q Z) w (toPar θ)
    = w (Sum.inl 0) * (P.d * θ 0) + w (Sum.inr 0) * θ 1 + w (Sum.inl 0) * θ 2
      - (P.kA * max (w (Sum.inl 0)) 0 + P.kE * max (w (Sum.inr 0)) 0) := by
  rw [score, w0_d, sub_zero, tau_d]
  simp [exposure, active, etf, data, toPar, dotProduct, mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  ring

lemma F_d : F (data P q Z) = {w | 0 ≤ w (Sum.inl 0) ∧ w (Sum.inl 0) ≤ P.abar ∧
    0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1 ∧
    (1 + P.kA) * w (Sum.inl 0) + (1 + P.kE) * w (Sum.inr 0) ≤ 1} := by
  ext w
  simp only [F, Set.mem_ofPred_eq, cash_d]
  constructor
  · rintro ⟨h, hc⟩
    have ha := h (Sum.inl 0)
    have hp := h (Sum.inr 0)
    simp only [data, Sum.elim_inl, Sum.elim_inr] at ha hp
    rw [max_eq_left ha.1, max_eq_left hp.1] at hc
    exact ⟨ha.1, ha.2, hp.1, hp.2, by linarith⟩
  · rintro ⟨ha, ha', hp, hp', hs⟩
    refine ⟨fun i => ?_, ?_⟩
    · rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
        simp only [data, Sum.elim_inl, Sum.elim_inr] <;> exact ⟨by assumption, by assumption⟩
    · rw [max_eq_left ha, max_eq_left hp]; linarith

lemma score_F {w : Inst 1 1 → ℝ} (hw : w ∈ F (data P q Z)) (θ : Fin 3 → ℝ) :
    score (data P q Z) w (toPar θ)
      = w (Sum.inl 0) * (P.d * θ 0 + θ 2 - P.kA) + w (Sum.inr 0) * (θ 1 - P.kE) := by
  rw [F_d] at hw
  rw [score_d, max_eq_left hw.1, max_eq_left hw.2.2.1]
  ring

end Data

section Opt

variable {P : Inputs} (hP : P.InRange) {S : Type} [Fintype S] (q Z : S → ℝ)
include hP

lemma E_d : E (data P q Z)
    = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1 / (1 + P.kE)} := by
  have hk := kE1 hP
  have hk0 := hP.2.2.2.2.2.2.1
  ext w
  simp only [E, F_d, w0_d, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨ha, -, hp, -, hs⟩, h⟩
    have h0 : w (Sum.inl 0) = 0 := by simpa [active] using congrFun h 0
    refine ⟨h0, hp, ?_⟩
    rw [h0] at hs
    rw [le_div_iff₀ hk]; linarith
  · rintro ⟨ha, hp, hp'⟩
    rw [le_div_iff₀ hk] at hp'
    refine ⟨⟨by rw [ha], by rw [ha]; exact hP.2.2.2.2.2.2.2.2.1.le, hp, by nlinarith, by
      rw [ha]; linarith⟩, ?_⟩
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [active, ha]

lemma vE_mem_E : P.vE ∈ E (data P q Z) := by
  rw [E_d hP]
  have := kE1 hP
  refine ⟨rfl, by simp [Inputs.vE]; positivity, by simp [Inputs.vE]⟩

lemma vE_mem_F : P.vE ∈ F (data P q Z) := (vE_mem_E hP q Z).1

lemma wA_mem_F : P.wA ∈ F (data P q Z) := by
  rw [F_d]
  have hk := kE1 hP
  have hf := A_fund hP
  simp only [Inputs.wA, Sum.elim_inl, Sum.elim_inr, Set.mem_ofPred_eq]
  refine ⟨(A_pos hP).le, A_le_abar, div_nonneg (by linarith) hk.le, ?_, ?_⟩
  · rw [div_le_one hk]
    nlinarith [hP.2.2.2.2.2.2.1, mul_nonneg (kA1 hP).le (A_pos hP).le]
  · rw [mul_div_cancel₀ _ hk.ne']; linarith

lemma score_wA (θ : Fin 3 → ℝ) : score (data P q Z) P.wA (toPar θ)
    = P.A * (P.d * θ 0 + θ 2 - P.kA) + (1 - (1 + P.kA) * P.A) / (1 + P.kE) * (θ 1 - P.kE) := by
  rw [score_F P q Z (wA_mem_F hP q Z)]; rfl

lemma score_vE (θ : Fin 3 → ℝ) : score (data P q Z) P.vE (toPar θ)
    = 1 / (1 + P.kE) * (θ 1 - P.kE) := by
  rw [score_F P q Z (vE_mem_F hP q Z)]; simp [Inputs.vE]

/-- On `F`, `Q((a, p); (λ, μ, 0)) ≤ q_E + a d(λ - λ₀)`, with the slack `(p* - p)(μ - κ_E)`. -/
lemma score_bound {w : Inst 1 1 → ℝ} (hw : w ∈ F (data P q Z)) (lam : ℝ) :
    score (data P q Z) w (toPar (P.par lam))
      = P.qE + w (Sum.inl 0) * P.d * (lam - P.lam0)
        - ((1 - (1 + P.kA) * w (Sum.inl 0)) / (1 + P.kE) - w (Sum.inr 0)) * (P.mu - P.kE) := by
  rw [score_F P q Z hw]
  have hk := kE1 hP
  have hd := d_lam0 hP
  have e : (1 - (1 + P.kA) * w (Sum.inl 0)) / (1 + P.kE) * (P.mu - P.kE)
      = (1 - (1 + P.kA) * w (Sum.inl 0)) * P.qE := by
    unfold Inputs.qE; field_simp
  simp only [Inputs.par, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [sub_mul, e]
  linear_combination (w (Sum.inl 0)) * hd

lemma slack_nonneg {w : Inst 1 1 → ℝ} (hw : w ∈ F (data P q Z)) :
    0 ≤ ((1 - (1 + P.kA) * w (Sum.inl 0)) / (1 + P.kE) - w (Sum.inr 0)) * (P.mu - P.kE) := by
  rw [F_d] at hw
  have hk := kE1 hP
  refine mul_nonneg ?_ (by linarith [hP.2.1])
  rw [sub_nonneg, le_div_iff₀ hk]; linarith [hw.2.2.2.2]

lemma a_le_A {w : Inst 1 1 → ℝ} (hw : w ∈ F (data P q Z)) : w (Sum.inl 0) ≤ P.A := by
  rw [F_d] at hw
  have hk := kA1 hP
  have hk' := kE1 hP
  refine le_min hw.2.1 ?_
  rw [le_div_iff₀ hk]; nlinarith [hw.2.2.1, hw.2.2.2.2]

lemma maxE (lam : ℝ) :
    maximizers (fun v => score (data P q Z) v (toPar (P.par lam))) (E (data P q Z)) = {P.vE} := by
  have hk := kE1 hP
  have hm : 0 < P.mu - P.kE := by linarith [hP.2.1]
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have h := hmax _ (vE_mem_E hP q Z)
    have hwF := hw.1
    rw [score_bound hP q Z hwF, score_bound hP q Z (vE_mem_F hP q Z)] at h
    rw [E_d hP] at hw
    obtain ⟨ha, hp, hp'⟩ := hw
    simp only [Inputs.vE, Sum.elim_inl, Sum.elim_inr, ha] at h
    have hp2 : w (Sum.inr 0) = 1 / (1 + P.kE) := by
      have : (1 / (1 + P.kE) - w (Sum.inr 0)) * (P.mu - P.kE) ≤ 0 := by
        simp only [mul_zero, zero_mul, add_zero, sub_self, sub_zero] at h; linarith
      have := nonpos_of_mul_nonpos_left this hm
      linarith
    rw [inst_ext w, ha, hp2]; rfl
  · rintro rfl
    refine ⟨vE_mem_E hP q Z, fun v hv => ?_⟩
    rw [score_bound hP q Z hv.1, score_bound hP q Z (vE_mem_F hP q Z)]
    have hs := slack_nonneg hP q Z hv.1
    rw [E_d hP] at hv
    simp only [Inputs.vE, Sum.elim_inl, Sum.elim_inr, hv.1]
    simp only [mul_zero, zero_mul, add_zero, sub_self, sub_zero, hv.1] at hs ⊢
    linarith

lemma score_vE_par (lam : ℝ) : score (data P q Z) P.vE (toPar (P.par lam)) = P.qE := by
  rw [score_bound hP q Z (vE_mem_F hP q Z)]; simp [Inputs.vE]

lemma score_wA_par (lam : ℝ) :
    score (data P q Z) P.wA (toPar (P.par lam)) = P.qE + P.Dm * (lam - P.lam0) := by
  rw [score_bound hP q Z (wA_mem_F hP q Z)]
  simp only [Inputs.wA, Sum.elim_inl, Sum.elim_inr, sub_self, zero_mul, sub_zero]
  unfold Inputs.Dm; ring

lemma etfSup_eq (lam : ℝ) : etfSup (data P q Z) (P.par lam) = P.qE := by
  have h : P.vE ∈ maximizers (fun v => score (data P q Z) v (toPar (P.par lam))) (E (data P q Z)) := by
    rw [maxE hP q Z lam]; rfl
  have hg : IsGreatest ((fun v => score (data P q Z) v (toPar (P.par lam))) '' E (data P q Z))
      (score (data P q Z) P.vE (toPar (P.par lam))) :=
    ⟨⟨P.vE, h.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h.2 v hv⟩
  rw [etfSup, hg.csSup_eq, score_vE_par hP q Z]

lemma Adv_wA (lam : ℝ) : Adv (data P q Z) P.wA (P.par lam) = P.Dm * (lam - P.lam0) := by
  rw [Adv, etfSup_eq hP q Z, score_wA_par hP q Z]; ring

lemma Adv_neg {lam : ℝ} (hl : lam < P.lam0) {w : Inst 1 1 → ℝ} (hw : w ∈ F (data P q Z))
    (ha : 0 < w (Sum.inl 0)) : Adv (data P q Z) w (P.par lam) < 0 := by
  rw [Adv, etfSup_eq hP q Z, score_bound hP q Z hw]
  have hs := slack_nonneg hP q Z hw
  have : w (Sum.inl 0) * P.d * (lam - P.lam0) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos ha hP.1) (by linarith)
  linarith

lemma maxF_high {lam : ℝ} (hl : P.lam0 < lam) :
    maximizers (fun w => score (data P q Z) w (toPar (P.par lam))) (F (data P q Z)) = {P.wA} := by
  have hk := kE1 hP
  have hm : 0 < P.mu - P.kE := by linarith [hP.2.1]
  have hd : 0 < P.d * (lam - P.lam0) := mul_pos hP.1 (by linarith)
  have hwA := score_wA_par hP q Z lam
  have hDm : P.Dm * (lam - P.lam0) = P.A * P.d * (lam - P.lam0) := by unfold Inputs.Dm; ring
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have h := hmax _ (wA_mem_F hP q Z)
    have hs := slack_nonneg hP q Z hw
    have haA := a_le_A hP q Z hw
    rw [score_bound hP q Z hw, hwA, hDm] at h
    have ha : w (Sum.inl 0) = P.A := by
      by_contra hne
      have hlt : w (Sum.inl 0) < P.A := lt_of_le_of_ne haA hne
      have : w (Sum.inl 0) * P.d * (lam - P.lam0) < P.A * P.d * (lam - P.lam0) := by
        rw [mul_assoc, mul_assoc]; exact mul_lt_mul_of_pos_right hlt hd
      linarith
    have hsl : ((1 - (1 + P.kA) * w (Sum.inl 0)) / (1 + P.kE) - w (Sum.inr 0)) * (P.mu - P.kE)
        = 0 := by
      rw [ha] at h hs ⊢; linarith
    have hp : w (Sum.inr 0) = (1 - (1 + P.kA) * P.A) / (1 + P.kE) := by
      rcases mul_eq_zero.mp hsl with h1 | h1
      · rw [ha] at h1; linarith
      · linarith
    rw [inst_ext w, ha, hp]; rfl
  · rintro rfl
    refine ⟨wA_mem_F hP q Z, fun v hv => ?_⟩
    show score (data P q Z) v (toPar (P.par lam)) ≤ score (data P q Z) P.wA (toPar (P.par lam))
    rw [score_bound hP q Z hv, hwA, hDm]
    have hs := slack_nonneg hP q Z hv
    have haA := a_le_A hP q Z hv
    have : v (Sum.inl 0) * P.d * (lam - P.lam0) ≤ P.A * P.d * (lam - P.lam0) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right haA hd.le
    linarith

lemma Gstar_eq (lam : ℝ) : Gstar (data P q Z) (P.par lam) = P.Dm * max (lam - P.lam0) 0 := by
  rw [Gstar, etfSup_eq hP q Z]
  rcases le_or_gt lam P.lam0 with hl | hl
  · rw [max_eq_right (by linarith), mul_zero, sub_eq_zero]
    refine IsGreatest.csSup_eq ⟨⟨P.vE, vE_mem_F hP q Z, score_vE_par hP q Z lam⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    show score (data P q Z) v (toPar (P.par lam)) ≤ P.qE
    rw [score_bound hP q Z hv]
    have hs := slack_nonneg hP q Z hv
    have : v (Sum.inl 0) * P.d * (lam - P.lam0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by rw [F_d] at hv; exact hv.1) hP.1.le)
        (by linarith)
    linarith
  · rw [max_eq_left (by linarith)]
    have hm : P.wA ∈ maximizers (fun w => score (data P q Z) w (toPar (P.par lam)))
        (F (data P q Z)) := by
      rw [maxF_high hP q Z hl]; rfl
    have hg : IsGreatest ((fun w => score (data P q Z) w (toPar (P.par lam))) '' F (data P q Z))
        (score (data P q Z) P.wA (toPar (P.par lam))) :=
      ⟨⟨P.wA, hm.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hm.2 v hv⟩
    rw [hg.csSup_eq, score_wA_par hP q Z]
    ring

lemma exposure_gap {v : Inst 1 1 → ℝ} (hv : v ∈ E (data P q Z)) :
    exposure (data P q Z) P.wA 0 - exposure (data P q Z) v 0 = P.Dm := by
  rw [E_d hP] at hv
  simp [exposure, active, etf, data, mulVec, dotProduct, Inputs.wA, Inputs.Dm, hv.1]

end Opt

/-! ### Part 1 -/

lemma ret_inl (P : Inputs) {S : Type} (q Z : S → ℝ) (θ : Fin 3 → ℝ) (s : S) :
    ret (data P q Z) (toPar θ) s (Sum.inl 0) = P.d * (θ 0 + Z s) + θ 2 := by
  simp [ret, data, toPar, Matrix.vecHead, Matrix.vecTail]
  ring

lemma ret_inr (P : Inputs) {S : Type} (q Z : S → ℝ) (θ : Fin 3 → ℝ) (s : S) :
    ret (data P q Z) (toPar θ) s (Sum.inr 0) = θ 1 := by
  simp [ret, data, toPar]

lemma theta4_eq {P : Inputs} (hH : 0 < P.H) :
    Theta4 P.V4 = {θ | P.lam0 - P.H ≤ θ 0 ∧ θ 0 ≤ P.lam0 + P.H ∧ θ 1 = P.mu ∧ θ 2 = 0} := by
  ext θ
  simp only [Theta4, Inputs.V4, Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl : a = 1 - b := by linarith
    simp only [Inputs.par, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    refine ⟨by nlinarith [mul_nonneg hb hH.le], by nlinarith [mul_nonneg ha hH.le], by ring,
      by ring⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨(P.lam0 + P.H - θ 0) / (2 * P.H), (θ 0 - P.lam0 + P.H) / (2 * P.H),
      div_nonneg (by linarith) (by linarith), div_nonneg (by linarith) (by linarith),
      by field_simp; ring, ?_⟩
    funext i
    fin_cases i <;> simp [Inputs.par, h2, h3] <;> field_simp <;> ring

lemma mem_theta4 {P : Inputs} (hH : 0 < P.H) {θ : Fin 3 → ℝ} (h : θ ∈ Theta4 P.V4) :
    P.lam0 - P.H ≤ θ 0 ∧ θ 0 ≤ P.lam0 + P.H ∧ θ 1 = P.mu ∧ θ 2 = 0 := by
  rw [theta4_eq hH] at h; exact h

lemma eq_par (P : Inputs) {θ : Fin 3 → ℝ} (h1 : θ 1 = P.mu) (h2 : θ 2 = 0) : θ = P.par (θ 0) := by
  funext i; fin_cases i <;> simp [Inputs.par, h1, h2]

lemma admissible {P : Inputs} (hP : P.InRange) {S : Type} [Fintype S] {q Z : S → ℝ}
    (hK : InKH P.H q Z) : M4Admissible (data P q Z) P.V4 := by
  obtain ⟨hd, hmu, hH, hdH, hkA, hkA1, hkE, hkE1, ha, ha1, -⟩ := id hP
  obtain ⟨hq, hq1, hZ0, hZ⟩ := hK
  have hl0 := lam0_pos hP
  refine ⟨Or.inl rfl, ⟨P.par (P.lam0 - P.H), by simp [Inputs.V4]⟩, hq, hq1, fun k => ?_,
    fun j => by simp [data], fun j => by simp [data], by simp [data], fun i => by simp [data],
    by simp [data], by rw [W0_d]; norm_num, ?_, fun i => ?_, ?_⟩
  · fin_cases k
    · simpa [data] using hZ0
    · simp [data]
  · rw [w0_d, F_d]; simp only [Set.mem_ofPred_eq, Pi.zero_apply]; refine ⟨le_rfl, ha.le, le_rfl,
      by norm_num, by norm_num⟩
  · rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
      simp only [data, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] <;>
      exact ⟨by assumption, by assumption, le_rfl, by norm_num⟩
  · intro θ hθ s i
    simp only [Inputs.V4, Finset.mem_insert, Finset.mem_singleton] at hθ
    have hz := abs_le.mp (hZ s)
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
    · rw [ret_inl]
      rcases hθ with rfl | rfl <;> simp only [Inputs.par, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, add_zero] <;>
        nlinarith [mul_le_mul_of_nonneg_left hz.1 hd.le]
    · rw [ret_inr]
      rcases hθ with rfl | rfl <;> simp [Inputs.par] <;> linarith

theorem geometry : Geometry := by
  intro P hP S _ q Z hK
  have hH := hP.2.2.1
  refine ⟨admissible hP hK, theta4_eq hH, F_d P q Z, E_d hP q Z,
    fun θ w hw => score_F P q Z hw θ, Dm_pos hP,
    fun lam => ⟨maxE hP q Z lam, etfSup_eq hP q Z lam⟩,
    fun lam => ⟨Adv_wA hP q Z lam, Gstar_eq hP q Z lam⟩,
    fun lam hl w hw ha => Adv_neg hP q Z hl hw ha, fun lam hl => maxF_high hP q Z hl,
    fun v hv => exposure_gap hP q Z hv⟩

/-! ### Part 2: the hard law -/

section Hard

variable (k : ℕ)

/-- `φ = π/(m + 1)` with `m = k + 1` support points. -/
def phi : ℝ := Real.pi / (k + 2)

/-- `u_n = sin(n φ)`. -/
def u (n : ℕ) : ℝ := Real.sin (n * phi k)

/-- `S_m = Σ_{i=1}^m u_i²`. -/
def Sm : ℝ := ∑ i : Fin (k + 1), u k (i + 1) ^ 2

/-- The hard masses `q_i = u_i²/S_m`. -/
def qh (i : Fin (k + 1)) : ℝ := u k (i + 1) ^ 2 / Sm k

/-- The hard grid `Z_i = Δ(2i - k)`, `i = 0, …, k` (the paper's `2Δ[i - (m+1)/2]`). -/
def Zh (Δ : ℝ) (i : Fin (k + 1)) : ℝ := Δ * (2 * (i : ℝ) - k)

lemma phi_pos : 0 < phi k := by unfold phi; positivity

lemma phi_mul : ((k : ℝ) + 2) * phi k = Real.pi := by
  unfold phi; field_simp

lemma u_zero : u k 0 = 0 := by simp [u]

lemma u_top : u k (k + 2) = 0 := by
  simp only [u]; push_cast; rw [phi_mul]; exact Real.sin_pi

lemma u_pos {n : ℕ} (h0 : 0 < n) (h1 : n < k + 2) : 0 < u k n := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos (by exact_mod_cast h0) (phi_pos k))
  rw [← phi_mul k]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h1) (phi_pos k)

lemma u_rec (n : ℕ) : u k n + u k (n + 2) = 2 * Real.cos (phi k) * u k (n + 1) := by
  simp only [u]
  have h1 : (n : ℝ) * phi k = ((n + 1 : ℕ) : ℝ) * phi k - phi k := by push_cast; ring
  have h2 : ((n + 2 : ℕ) : ℝ) * phi k = ((n + 1 : ℕ) : ℝ) * phi k + phi k := by push_cast; ring
  rw [h1, h2, Real.sin_sub, Real.sin_add]
  ring

lemma u_refl {n : ℕ} (h : n ≤ k + 2) : u k (k + 2 - n) = u k n := by
  simp only [u]
  rw [Nat.cast_sub h]
  push_cast
  rw [sub_mul, phi_mul, Real.sin_pi_sub]

lemma Sm_pos : 0 < Sm k := by
  unfold Sm
  exact Finset.sum_pos (fun i _ => pow_pos (u_pos k (by omega) (by omega)) 2) Finset.univ_nonempty

lemma qh_pos (i : Fin (k + 1)) : 0 < qh k i :=
  div_pos (pow_pos (u_pos k (by omega) (by omega)) 2) (Sm_pos k)

lemma qh_sum : ∑ i, qh k i = 1 := by
  simp only [qh, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (Sm_pos k).ne'

lemma qh_rev (i : Fin (k + 1)) : qh k (Fin.rev i) = qh k i := by
  simp only [qh, Fin.val_rev]
  have hi := i.isLt
  have : k + 1 - (i + 1) + 1 = k + 2 - (i + 1) := by omega
  rw [this, u_refl k (by omega)]

lemma Zh_rev (Δ : ℝ) (i : Fin (k + 1)) : Zh k Δ (Fin.rev i) = -Zh k Δ i := by
  simp only [Zh, Fin.val_rev]
  have hi := i.isLt
  rw [show k + 1 - (i + 1) = k - (i : ℕ) by omega, Nat.cast_sub (by omega)]
  ring

lemma qh_centered (Δ : ℝ) : ∑ i, qh k i * Zh k Δ i = 0 := by
  have h := Equiv.sum_comp Fin.revPerm (fun i => qh k i * Zh k Δ i)
  simp only [Fin.revPerm_apply, qh_rev, Zh_rev, mul_neg, Finset.sum_neg_distrib] at h
  linarith

lemma Zh_abs {Δ : ℝ} (hΔ : 0 ≤ Δ) (i : Fin (k + 1)) : |Zh k Δ i| ≤ k * Δ := by
  simp only [Zh]
  have hi : (i : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

/-- The one-record affinity identity `Σ_j u_{j+1} u_{j+2} = cos φ · S_m`. -/
lemma affinity_sum : ∑ j ∈ Finset.range k, u k (j + 1) * u k (j + 2)
    = Real.cos (phi k) * Sm k := by
  have hrec : ∑ i ∈ Finset.range (k + 1), u k (i + 1) * (u k i + u k (i + 2))
      = 2 * Real.cos (phi k) * ∑ i ∈ Finset.range (k + 1), u k (i + 1) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [u_rec]; ring
  have hsplit : ∑ i ∈ Finset.range (k + 1), u k (i + 1) * (u k i + u k (i + 2))
      = 2 * ∑ j ∈ Finset.range k, u k (j + 1) * u k (j + 2) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [u_zero, mul_zero, add_zero, u_top]
    rw [two_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring_nf
  have hS : Sm k = ∑ i ∈ Finset.range (k + 1), u k (i + 1) ^ 2 := by
    unfold Sm
    exact Fin.sum_univ_eq_sum_range (fun i => u k (i + 1) ^ 2) (k + 1)
  rw [hS]
  linarith

end Hard

/-! ### Part 2: the testing bound -/

/-- Le Cam's testing inequality on a finite set: if `Σ p c ≤ ε` and `Σ r (1 - c) ≤ ε`, then the
affinity `Σ √(p r)` satisfies `(Σ √(p r))² ≤ 4ε`. -/
lemma lecam {T : Type} [Fintype T] (p r c a : T → ℝ) (ε : ℝ)
    (hp : ∀ t, 0 ≤ p t) (hr : ∀ t, 0 ≤ r t) (hps : ∑ t, p t ≤ 1) (hrs : ∑ t, r t ≤ 1)
    (hc : ∀ t, 0 ≤ c t ∧ c t ≤ 1) (h1 : ∑ t, p t * c t ≤ ε) (h2 : ∑ t, r t * (1 - c t) ≤ ε)
    (ha : ∀ t, 0 ≤ a t) (ha2 : ∀ t, a t ^ 2 = p t * r t) : (∑ t, a t) ^ 2 ≤ 4 * ε := by
  have hmin : ∑ t, min (p t) (r t) ≤ 2 * ε := by
    calc ∑ t, min (p t) (r t) ≤ ∑ t, (p t * c t + r t * (1 - c t)) := by
          refine Finset.sum_le_sum fun t _ => ?_
          have := hc t
          rcases le_total (p t) (r t) with h | h
          · rw [min_eq_left h]; nlinarith [hp t]
          · rw [min_eq_right h]; nlinarith [hr t]
      _ ≤ 2 * ε := by rw [Finset.sum_add_distrib]; linarith
  have hmax : ∑ t, max (p t) (r t) ≤ 2 := by
    calc _ ≤ ∑ t, (p t + r t) :=
          Finset.sum_le_sum fun t _ => max_le (by linarith [hr t]) (by linarith [hp t])
      _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith
  have hmin0 : 0 ≤ ∑ t, min (p t) (r t) := Finset.sum_nonneg fun t _ => le_min (hp t) (hr t)
  have e : ∀ t, Real.sqrt (min (p t) (r t)) * Real.sqrt (max (p t) (r t)) = a t := fun t => by
    rw [← Real.sqrt_mul (le_min (hp t) (hr t)), min_mul_max, ← ha2 t, Real.sqrt_sq (ha t)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun t => Real.sqrt (min (p t) (r t)))
    (fun t => Real.sqrt (max (p t) (r t)))
  simp only [e, Real.sq_sqrt (le_min (hp _) (hr _)),
    Real.sq_sqrt (le_trans (hp _) (le_max_left _ _))] at hcs
  nlinarith

/-- `cos φ > 0` and `log cos φ ≥ -φ²` for `0 < φ ≤ 1`. -/
lemma log_cos_ge {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 1) :
    0 < Real.cos φ ∧ -φ ^ 2 ≤ Real.log (Real.cos φ) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hsq : φ ^ 2 ≤ 1 := by nlinarith
  have hy : 0 < 1 - φ ^ 2 / 2 := by linarith
  have hcpos : 0 < Real.cos φ := lt_of_lt_of_le hy hc
  refine ⟨hcpos, ?_⟩
  have hl := Real.one_sub_inv_le_log_of_pos hy
  have hm := Real.log_le_log hy hc
  have hinv : (1 - φ ^ 2 / 2)⁻¹ ≤ 1 + φ ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hy]; nlinarith [sq_nonneg φ]
  linarith

lemma sum_inj_le {α β : Type} [Fintype α] [Fintype β] (e : α → β) (he : Function.Injective e)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) : ∑ x, f (e x) ≤ ∑ b, f b := by
  rw [← Finset.sum_image (fun x _ y _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)

lemma record_d (P : Inputs) {S : Type} (q Z : S → ℝ) (θ : Fin 3 → ℝ) (s : S) :
    record (data P q Z) θ s = ⟨![θ 0 + Z s, θ 1], P.d * (θ 0 + Z s) + θ 2, fun _ => θ 1⟩ := by
  have h1 := ret_inl P q Z θ s
  have h2 := ret_inr P q Z θ s
  simp only [record, h1]
  congr 1
  · funext k; fin_cases k <;> simp [data, toPar]
  · funext j; obtain rfl : j = 0 := Subsingleton.elim _ _; exact h2

lemma mass_sum {S : Type} [Fintype S] (D : Data 1 1 2 S) (hq : ∑ s, D.q s = 1) (N : ℕ) :
    ∑ σ : Fin N → S, mass D σ = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum (fun _ : Fin N => fun s => D.q s)]
  simp [hq]

lemma kernel_bounds {N : ℕ} (ρ : Rule N) (H : Fin N → Record 1) (T : Set (Inst 1 1 → ℝ)) :
    0 ≤ (ρ.kernel H T).toReal ∧ (ρ.kernel H T).toReal ≤ 1 := by
  have := ρ.isProb H
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩

theorem lowerBound : LowerBound := by
  intro P hP N hN hyp
  obtain ⟨hd, hmu, hH, hdH, hkA, hkA1, hkE, hkE1, ha, ha1, hδ, hδD, hε, hε1⟩ := id hP
  have hD := Dm_pos hP
  set Δ := P.delta / P.Dm with hΔdef
  have hΔ : 0 < Δ := div_pos hδ hD
  have hHΔ : P.H / Δ = P.Dm * P.H / P.delta := by rw [hΔdef]; field_simp
  have hHΔ2 : 2 ≤ P.H / Δ := by rw [hHΔ, le_div_iff₀ hδ]; linarith
  have hΔH : Δ ≤ P.H := by
    have := hHΔ2; rw [le_div_iff₀ hΔ] at this; linarith
  set k := ⌊P.H / Δ⌋₊ with hk
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hHΔ2)
  have hkH : (k : ℝ) * Δ ≤ P.H := by
    have := Nat.floor_le (div_nonneg hH.le hΔ.le); rw [← hk, le_div_iff₀ hΔ] at this; exact this
  have hkH' : P.H / Δ < k + 1 := by rw [hk]; exact Nat.lt_floor_add_one _
  -- the hard law and its rule
  have hK : InKH P.H (qh k) (Zh k Δ) :=
    ⟨fun i => (qh_pos k i).le, qh_sum k, qh_centered k Δ,
      fun i => (Zh_abs k hΔ.le i).trans hkH⟩
  obtain ⟨ρ, hA, hfalse, hpow⟩ := hyp (Fin (k + 1)) (qh k) (Zh k Δ) hK
  set D := data P (qh k) (Zh k Δ) with hDdef
  have hθm : P.par (P.lam0 - Δ) ∈ Theta4 P.V4 := by
    rw [theta4_eq hH]; simp only [Inputs.par, Set.mem_ofPred_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    exact ⟨by linarith, by linarith, by simp, by simp⟩
  have hθp : P.par (P.lam0 + Δ) ∈ Theta4 P.V4 := by
    rw [theta4_eq hH]; simp only [Inputs.par, Set.mem_ofPred_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    exact ⟨by linarith, by linarith, by simp, by simp⟩
  have hGp : P.delta ≤ Gstar D (P.par (P.lam0 + Δ)) := by
    rw [Gstar_eq hP, max_eq_left (by linarith), add_sub_cancel_left, hΔdef]
    field_simp; rfl
  -- certification probabilities at the two parameters
  let c : (Fin N → Record 1) → ℝ := fun H => (ρ.kernel H {w | 0 < w (Sum.inl 0)}).toReal
  have hc01 : ∀ H, 0 ≤ c H ∧ c H ≤ 1 := fun H => kernel_bounds ρ H _
  have hmass : ∀ σ : Fin N → Fin (k + 1), 0 ≤ mass D σ := fun σ =>
    Finset.prod_nonneg fun l _ => (qh_pos k (σ l)).le
  have hm : ∑ σ, mass D σ * c (hist D (P.par (P.lam0 - Δ)) σ) ≤ P.eps := by
    refine le_trans (Finset.sum_le_sum fun σ _ => ?_) (hfalse _ hθm)
    refine mul_le_mul_of_nonneg_left ?_ (hmass σ)
    have := ρ.isProb (hist D (P.par (P.lam0 - Δ)) σ)
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    calc ρ.kernel _ {w | 0 < w (Sum.inl 0)}
        ≤ ρ.kernel _ ({w | 0 < w (Sum.inl 0) ∧ Adv D w (P.par (P.lam0 - Δ)) ≤ P.delta / 4}
            ∪ {w | w ≠ P.vE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))}) := by
          apply measure_mono
          intro w hw
          simp only [Set.mem_ofPred_eq] at hw
          by_cases hF : w ∈ F D
          · exact Or.inl ⟨hw, by
              linarith [Adv_neg hP (qh k) (Zh k Δ) (by linarith : P.lam0 - Δ < P.lam0) hF hw]⟩
          · refine Or.inr ⟨?_, fun h => hF h.1⟩
            rintro rfl
            simp [Inputs.vE] at hw
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hA, add_zero]
  have hp : 1 - P.eps ≤ ∑ σ, mass D σ * c (hist D (P.par (P.lam0 + Δ)) σ) := by
    refine le_trans (hpow _ hθp hGp) (Finset.sum_le_sum fun σ _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hmass σ)
    have := ρ.isProb (hist D (P.par (P.lam0 + Δ)) σ)
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun w hw => hw.1)
  have hsum1 : ∑ σ : Fin N → Fin (k + 1), mass D σ = 1 := mass_sum D (qh_sum k) N
  -- restriction to the common atoms
  let sm : (Fin N → Fin k) → (Fin N → Fin (k + 1)) := fun τ l => (τ l).succ
  let sp : (Fin N → Fin k) → (Fin N → Fin (k + 1)) := fun τ l => (τ l).castSucc
  have hsm : Function.Injective sm := fun τ τ' h => funext fun l =>
    Fin.succ_injective _ (congrFun h l)
  have hsp : Function.Injective sp := fun τ τ' h => funext fun l =>
    Fin.castSucc_injective _ (congrFun h l)
  have hhist : ∀ τ, hist D (P.par (P.lam0 - Δ)) (sm τ) = hist D (P.par (P.lam0 + Δ)) (sp τ) := by
    intro τ
    funext l
    simp only [hist, sm, sp, hDdef, record_d, Inputs.par, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Zh, Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring_nf
  have h1 : ∑ τ, mass D (sm τ) * c (hist D (P.par (P.lam0 + Δ)) (sp τ)) ≤ P.eps := by
    refine le_trans (le_of_eq ?_) (le_trans (sum_inj_le sm hsm
      (fun σ => mass D σ * c (hist D (P.par (P.lam0 - Δ)) σ))
      (fun σ => mul_nonneg (hmass σ) (hc01 _).1)) hm)
    exact Finset.sum_congr rfl fun τ _ => by rw [hhist]
  have h2 : ∑ τ, mass D (sp τ) * (1 - c (hist D (P.par (P.lam0 + Δ)) (sp τ))) ≤ P.eps := by
    refine le_trans (sum_inj_le sp hsp
      (fun σ => mass D σ * (1 - c (hist D (P.par (P.lam0 + Δ)) σ)))
      (fun σ => mul_nonneg (hmass σ) (by linarith [(hc01 (hist D (P.par (P.lam0 + Δ)) σ)).2])))
      ?_
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum1]
    linarith
  -- the affinity
  let s : Fin k → ℝ := fun j => u k (j + 2) * u k (j + 1) / Sm k
  let a : (Fin N → Fin k) → ℝ := fun τ => ∏ l, s (τ l)
  have hs0 : ∀ j, 0 ≤ s j := fun j =>
    div_nonneg (mul_nonneg (u_pos k (by omega) (by omega)).le (u_pos k (by omega) (by omega)).le)
      (Sm_pos k).le
  have ha2 : ∀ τ, a τ ^ 2 = mass D (sm τ) * mass D (sp τ) := by
    intro τ
    simp only [a, mass, sm, sp, hDdef, data, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp only [s, qh, Fin.val_succ, Fin.val_castSucc]
    rw [div_pow, mul_pow, div_mul_div_comm, sq (Sm k)]
  have hsa : ∑ τ, a τ = Real.cos (phi k) ^ N := by
    simp only [a]
    rw [← Fintype.prod_sum (fun _ : Fin N => s), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    simp only [s, div_eq_mul_inv, ← Finset.sum_mul]
    have := Fin.sum_univ_eq_sum_range (fun j => u k (j + 2) * u k (j + 1)) k
    rw [this]
    have haf := affinity_sum k
    rw [show ∑ j ∈ Finset.range k, u k (j + 2) * u k (j + 1)
        = ∑ j ∈ Finset.range k, u k (j + 1) * u k (j + 2) from
      Finset.sum_congr rfl fun j _ => mul_comm _ _, haf, mul_assoc,
      mul_inv_cancel₀ (Sm_pos k).ne', mul_one]
  have hps : ∑ τ, mass D (sm τ) ≤ 1 := by
    refine le_trans (sum_inj_le sm hsm (mass D) hmass) (le_of_eq hsum1)
  have hrs : ∑ τ, mass D (sp τ) ≤ 1 := by
    refine le_trans (sum_inj_le sp hsp (mass D) hmass) (le_of_eq hsum1)
  have hle := lecam (fun τ => mass D (sm τ)) (fun τ => mass D (sp τ))
    (fun τ => c (hist D (P.par (P.lam0 + Δ)) (sp τ))) a P.eps (fun τ => hmass _) (fun τ => hmass _)
    hps hrs (fun τ => hc01 _) h1 h2 (fun τ => Finset.prod_nonneg fun l _ => hs0 _) ha2
  rw [hsa] at hle
  -- logarithms
  have hφ0 := phi_pos k
  have hφ1 : phi k ≤ 1 := by
    unfold phi
    rw [div_le_one (by positivity)]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith [Real.pi_le_four]
  obtain ⟨hcos, hlog⟩ := log_cos_ge hφ0 hφ1
  have hlog2 := Real.log_le_log (by positivity) hle
  rw [← pow_mul, Real.log_pow, Real.log_mul (by norm_num) hε.ne'] at hlog2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : -(Real.log 4 + Real.log P.eps) ≤ 2 * N * phi k ^ 2 := by
    push_cast at hlog2
    nlinarith
  have hphi2 : phi k ^ 2 * ((k : ℝ) + 2) ^ 2 = Real.pi ^ 2 := by rw [← mul_pow, mul_comm, phi_mul]
  have hlogε : Real.log P.eps ≤ -(2 * Real.log 4) := by
    have := Real.log_le_log hε hε1
    rw [show (1 : ℝ) / 16 = (4 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow] at this
    push_cast at this; linarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hX : P.Dm * P.H / P.delta ≤ k + 2 := by rw [← hHΔ]; linarith
  have hX0 : 0 ≤ P.Dm * P.H / P.delta := by positivity
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hsq : (P.Dm * P.H / P.delta) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  rw [show Real.log (1 / P.eps) = -Real.log P.eps by rw [one_div, Real.log_inv]]
  have hL : 0 ≤ -Real.log P.eps := by linarith
  have hL4 : -Real.log P.eps ≤ 4 * N * phi k ^ 2 := by linarith
  have h5 : ((k : ℝ) + 2) ^ 2 * (-Real.log P.eps) ≤ ((k : ℝ) + 2) ^ 2 * (4 * N * phi k ^ 2) :=
    mul_le_mul_of_nonneg_left hL4 (by positivity)
  have h6 : ((k : ℝ) + 2) ^ 2 * (4 * N * phi k ^ 2) = 4 * N * Real.pi ^ 2 := by
    rw [← hphi2]; ring
  have h7 := mul_le_mul_of_nonneg_right hsq hL
  calc 1 / (4 * Real.pi ^ 2) * (P.Dm * P.H / P.delta) ^ 2 * -Real.log P.eps
      = (P.Dm * P.H / P.delta) ^ 2 * -Real.log P.eps / (4 * Real.pi ^ 2) := by ring
    _ ≤ (N : ℝ) := by rw [div_le_iff₀ (by positivity)]; linarith

/-! ### Part 3: bounded-mean tail bounds on finite sums -/

section Tail

variable {S : Type} [Fintype S] {H : ℝ} {q Z : S → ℝ}

/-- Hoeffding's lemma on a finite law: `E exp(tZ) ≤ cosh(tH) ≤ exp(t²H²/2)`. -/
lemma mgf_le (hK : InKH H q Z) (hH : 0 < H) (t : ℝ) :
    ∑ s, q s * Real.exp (t * Z s) ≤ Real.exp (t ^ 2 * H ^ 2 / 2) := by
  obtain ⟨hq, hq1, hZ0, hZ⟩ := hK
  have chord : ∀ s, Real.exp (t * Z s) ≤ (H - Z s) / (2 * H) * Real.exp (-(t * H))
      + (H + Z s) / (2 * H) * Real.exp (t * H) := by
    intro s
    have hz := abs_le.mp (hZ s)
    have ha : 0 ≤ (H - Z s) / (2 * H) := div_nonneg (by linarith) (by linarith)
    have hb : 0 ≤ (H + Z s) / (2 * H) := div_nonneg (by linarith) (by linarith)
    have hab : (H - Z s) / (2 * H) + (H + Z s) / (2 * H) = 1 := by field_simp; ring
    have := convexOn_exp.2 (Set.mem_univ (-(t * H))) (Set.mem_univ (t * H)) ha hb hab
    simp only [smul_eq_mul] at this
    convert this using 2
    field_simp
    ring
  calc ∑ s, q s * Real.exp (t * Z s)
      ≤ ∑ s, q s * ((H - Z s) / (2 * H) * Real.exp (-(t * H))
          + (H + Z s) / (2 * H) * Real.exp (t * H)) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (chord s) (hq s)
    _ = (Real.exp (t * H) + Real.exp (-(t * H))) / 2 := by
        have e : ∀ s, q s * ((H - Z s) / (2 * H) * Real.exp (-(t * H))
            + (H + Z s) / (2 * H) * Real.exp (t * H))
            = q s * ((Real.exp (t * H) + Real.exp (-(t * H))) / 2)
              + (q s * Z s) * ((Real.exp (t * H) - Real.exp (-(t * H))) / (2 * H)) := by
          intro s; field_simp; ring
        simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, hZ0]
        ring
    _ = Real.cosh (t * H) := by rw [Real.cosh_eq]
    _ ≤ Real.exp ((t * H) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = Real.exp (t ^ 2 * H ^ 2 / 2) := by ring_nf

/-- The upper tail on finite histories: `P(Σ_l Z ≥ N a) ≤ exp(-N a²/(2H²))`. -/
lemma chernoff (hK : InKH H q Z) (hH : 0 < H) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑ σ : Fin N → S, (if (N : ℝ) * a ≤ ∑ l, Z (σ l) then ∏ l, q (σ l) else 0)
      ≤ Real.exp (-(N * a ^ 2) / (2 * H ^ 2)) := by
  set t := a / H ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hq := hK.1
  calc ∑ σ : Fin N → S, (if (N : ℝ) * a ≤ ∑ l, Z (σ l) then ∏ l, q (σ l) else 0)
      ≤ ∑ σ : Fin N → S, (∏ l, q (σ l)) * Real.exp (t * (∑ l, Z (σ l) - N * a)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun l _ => hq _
        split_ifs with h
        · have : 1 ≤ Real.exp (t * (∑ l, Z (σ l) - N * a)) :=
            Real.one_le_exp (mul_nonneg ht0.le (by linarith))
          nlinarith
        · positivity
    _ = Real.exp (-(t * N * a)) * ∏ _l : Fin N, ∑ s, q s * Real.exp (t * Z s) := by
        rw [Fintype.prod_sum (fun _ : Fin N => fun s => q s * Real.exp (t * Z s)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_mul_distrib, mul_sub, Finset.mul_sum, Real.exp_sub, Real.exp_sum,
          div_eq_mul_inv, ← Real.exp_neg]
        ring_nf
    _ ≤ Real.exp (-(t * N * a)) * ∏ _l : Fin N, Real.exp (t ^ 2 * H ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun l _ => Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (Real.exp_pos _).le)
          (fun l _ => mgf_le hK hH t)) (Real.exp_pos _).le
    _ = Real.exp (-(N * a ^ 2) / (2 * H ^ 2)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul,
          ← Real.exp_add]
        congr 1
        rw [ht]
        field_simp
        ring

lemma inKH_neg (hK : InKH H q Z) : InKH H q (fun s => -Z s) := by
  obtain ⟨hq, hq1, hZ0, hZ⟩ := hK
  refine ⟨hq, hq1, ?_, fun s => by rw [abs_neg]; exact hZ s⟩
  simp only [mul_neg, Finset.sum_neg_distrib, hZ0, neg_zero]

/-- The two-sided tail of the sample mean. -/
lemma tail2 (hK : InKH H q Z) (hH : 0 < H) {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    ∑ σ : Fin N → S, (if a ≤ |(1 / (N : ℝ)) * ∑ l, Z (σ l)| then ∏ l, q (σ l) else 0)
      ≤ 2 * Real.exp (-(N * a ^ 2) / (2 * H ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := hK.1
  have h1 := chernoff hK hH N ha
  have h2 := chernoff (inKH_neg hK) hH N ha
  calc _ ≤ ∑ σ : Fin N → S, ((if (N : ℝ) * a ≤ ∑ l, Z (σ l) then ∏ l, q (σ l) else 0)
          + (if (N : ℝ) * a ≤ ∑ l, -Z (σ l) then ∏ l, q (σ l) else 0)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun l _ => hq _
        rw [Finset.sum_neg_distrib]
        by_cases h : a ≤ |(1 / (N : ℝ)) * ∑ l, Z (σ l)|
        · simp only [h, ↓reduceIte]
          rcases le_abs'.mp h with h' | h'
          · have : (N : ℝ) * a ≤ -∑ l, Z (σ l) := by
              rw [one_div, inv_mul_le_iff₀ hNr] at h'; linarith
            simp only [this, ↓reduceIte]; split_ifs <;> linarith
          · have : (N : ℝ) * a ≤ ∑ l, Z (σ l) := by rw [one_div, le_inv_mul_iff₀ hNr] at h'; linarith
            simp only [this, ↓reduceIte]; split_ifs <;> linarith
        · simp only [h, ↓reduceIte]; split_ifs <;> linarith
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

end Tail

/-! ### Part 3: M4's calibration objects in this family -/

section Calib

variable {P : Inputs} {S : Type} [Fintype S] {q Z : S → ℝ}

/-- The sample mean of the shocks. -/
def ebar {N : ℕ} (Z : S → ℝ) (σ : Fin N → S) : ℝ := (1 / (N : ℝ)) * ∑ l, Z (σ l)

/-- `Var Z = Σ q Z²`. -/
def varZ (q Z : S → ℝ) : ℝ := ∑ s, q s * Z s ^ 2

omit [Fintype S] in
lemma zeta_d (s : S) : zeta (data P q Z) s = ![Z s, 0, 0] := by
  funext i; fin_cases i <;> simp [zeta, data]

omit [Fintype S] in
lemma errN_d {N : ℕ} (σ : Fin N → S) : errN (data P q Z) σ = ![ebar Z σ, 0, 0] := by
  funext i; fin_cases i <;> simp [errN, zeta_d, ebar, Finset.sum_apply]

omit [Fintype S] in
lemma X_d (θ : Fin 3 → ℝ) (s : S) :
    X (data P q Z) (record (data P q Z) θ s) = ![θ 0 + Z s, θ 1, θ 2] := by
  funext i
  simp only [X, record_d]
  fin_cases i <;> simp [data, mulVec, dotProduct, Fin.sum_univ_two]

omit [Fintype S] in
lemma thetaHat_hist {N : ℕ} (hN : 0 < N) (θ : Fin 3 → ℝ) (σ : Fin N → S) :
    thetaHat (data P q Z) (hist (data P q Z) θ σ) = θ + errN (data P q Z) σ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  fin_cases i <;> simp [thetaHat, hist, X_d, errN_d, ebar, Finset.sum_apply,
    Finset.sum_add_distrib] <;> field_simp

lemma omega_d : Omega (data P q Z) = !![varZ q Z, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j
  simp only [Omega, zeta_d]
  fin_cases i <;> fin_cases j <;> simp [varZ, sq, data]

lemma pinv_d (hV : 0 < varZ q Z) :
    Omega (data P q Z) * pinv (Omega (data P q Z)) * Omega (data P q Z) = Omega (data P q Z) := by
  have hex : IsMoorePenrose (Omega (data P q Z)) !![1 / varZ q Z, 0, 0; 0, 0, 0; 0, 0, 0] := by
    rw [omega_d]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hV.ne']
  exact (Classical.epsilon_spec ⟨_, hex⟩).1

lemma omega_symm : (Omega (data P q Z))ᵀ = Omega (data P q Z) := by
  rw [omega_d]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- On `Im Ω`, the quadratic form of any `G` with `ΩGΩ = Ω` is that of `Ω⁻¹`. -/
lemma quad_range {Ω G : Matrix (Fin 3) (Fin 3) ℝ} (hΩ : Ωᵀ = Ω) (hG : Ω * G * Ω = Ω)
    (x : Fin 3 → ℝ) : (Ω *ᵥ x) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) = x ⬝ᵥ (Ω *ᵥ x) := by
  calc (Ω *ᵥ x) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) = (x ᵥ* Ωᵀ) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) := by rw [Matrix.vecMul_transpose]
    _ = x ⬝ᵥ (Ωᵀ *ᵥ (G *ᵥ (Ω *ᵥ x))) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = x ⬝ᵥ ((Ω * G * Ω) *ᵥ x) := by rw [hΩ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    _ = x ⬝ᵥ (Ω *ᵥ x) := by rw [hG]

lemma omega_mulVec (x : Fin 3 → ℝ) : Omega (data P q Z) *ᵥ x = ![varZ q Z * x 0, 0, 0] := by
  rw [omega_d]; funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

lemma range_iff (hV : 0 < varZ q Z) (e : Fin 3 → ℝ) :
    e ∈ Set.range (Omega (data P q Z)).mulVec ↔ e 1 = 0 ∧ e 2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩; rw [omega_mulVec]; simp
  · rintro ⟨h1, h2⟩
    refine ⟨![e 0 / varZ q Z, 0, 0], ?_⟩
    rw [omega_mulVec]; funext i; fin_cases i <;> (simp [h1, h2]; try field_simp)

lemma quad_e (hV : 0 < varZ q Z) {e : Fin 3 → ℝ} (h1 : e 1 = 0) (h2 : e 2 = 0) :
    e ⬝ᵥ (pinv (Omega (data P q Z)) *ᵥ e) = e 0 ^ 2 / varZ q Z := by
  have he : e = Omega (data P q Z) *ᵥ ![e 0 / varZ q Z, 0, 0] := by
    rw [omega_mulVec]; funext i; fin_cases i <;> (simp [h1, h2]; try field_simp)
  rw [he, quad_range omega_symm (pinv_d hV), omega_mulVec]
  simp [dotProduct, Fin.sum_univ_three]
  field_simp

lemma varZ_nonneg (hq : ∀ s, 0 ≤ q s) : 0 ≤ varZ q Z :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)

lemma Z_zero (hq : ∀ s, 0 ≤ q s) (hV : varZ q Z = 0) {s : S} (hs : 0 < q s) : Z s = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hq s) (sq_nonneg (Z s)))).mp
    hV s (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hs.ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

lemma mass_pos_each (hq : ∀ s, 0 ≤ q s) {N : ℕ} {σ : Fin N → S}
    (hm : 0 < mass (data P q Z) σ) (l : Fin N) : 0 < q (σ l) := by
  rcases (hq (σ l)).lt_or_eq with h | h
  · exact h
  · exfalso
    have : mass (data P q Z) σ = 0 := Finset.prod_eq_zero (Finset.mem_univ l) h.symm
    linarith

lemma errN_range (hq : ∀ s, 0 ≤ q s) {N : ℕ} {σ : Fin N → S} (hm : 0 < mass (data P q Z) σ) :
    errN (data P q Z) σ ∈ Set.range (Omega (data P q Z)).mulVec := by
  rcases (varZ_nonneg (Z := Z) hq).lt_or_eq with hV | hV
  · rw [range_iff hV, errN_d]; simp
  · refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero, errN_d]
    have : ebar Z σ = 0 := by
      simp only [ebar]
      rw [Finset.sum_eq_zero fun l _ => Z_zero hq hV.symm (mass_pos_each hq hm l), mul_zero]
    rw [this]; funext i; fin_cases i <;> rfl

/-- The discrete quantile belongs to its own defining set, so it has coverage `≥ 1 - ε`. -/
lemma tcrit_mem (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 - ε ≤ ∑ σ : Fin N → S, if TN (data P q Z) σ ≤ tcrit (data P q Z) N ε
      then mass (data P q Z) σ else 0 := by
  set D := data P q Z
  set T := {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
    1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} with hT
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := mass_sum D hq1 N
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun l _ => hq _
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 := by
    by_contra h
    have : ∑ σ : Fin N → S, mass D σ ≤ 0 :=
      Finset.sum_nonpos fun σ _ => not_lt.mp fun hp => h ⟨σ, hp⟩
    linarith
  have hfin : T.Finite := (Set.finite_range (TN D)).subset fun t ht => by
    obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ) (TN D) ⟨σ0, by simp [hσ0]⟩
  have hne : T.Nonempty := by
    refine ⟨TN D σm, ⟨σm, (Finset.mem_filter.mp hσm).2, rfl⟩, ?_⟩
    have e : ∑ σ : Fin N → S, (if TN D σ ≤ TN D σm then mass D σ else 0) = 1 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rcases (hmass σ).lt_or_eq with h | h
      · have := hmax σ (by simp [h])
        split_ifs with hc
        · rfl
        · exact absurd this hc
      · rw [← h]; split_ifs <;> rfl
    linarith
  exact (hne.csInf_mem hfin).2

end Calib

/-! ### Part 3: the certificate -/

lemma lexSel_singleton (x : Inst 1 1 → ℝ) : lexSel ({x} : Set (Inst 1 1 → ℝ)) = x := by
  have h : ∃ w, w ∈ ({x} : Set (Inst 1 1 → ℝ)) ∧ ∀ v ∈ ({x} : Set (Inst 1 1 → ℝ)), LexLE w v :=
    ⟨x, rfl, fun v hv => Or.inl hv.symm⟩
  exact (Classical.epsilon_spec h).1

lemma dirac_toReal (w : Inst 1 1 → ℝ) (T : Set (Inst 1 1 → ℝ)) :
    (Measure.dirac w T).toReal = if w ∈ T then 1 else 0 := by
  by_cases h : w ∈ T <;> simp [h]

section Cert

variable {P : Inputs} (hP : P.InRange) {S : Type} [Fintype S] {q Z : S → ℝ} (hK : InKH P.H q Z)
  {N : ℕ} (hNb : 32 * (P.Dm * P.H / P.delta) ^ 2 * Real.log (2 / P.eps) ≤ N)
include hP hK hNb

lemma logpos : 0 < Real.log (2 / P.eps) :=
  Real.log_pos (by rw [lt_div_iff₀ hP.2.2.2.2.2.2.2.2.2.2.2.2.1]; linarith [hP.2.2.2.2.2.2.2.2.2.2.2.2.2])

lemma N_pos : (0 : ℝ) < N := by
  have := logpos hP hK hNb
  have hD := Dm_pos hP
  have hH := hP.2.2.1
  have hδ := hP.2.2.2.2.2.2.2.2.2.2.1
  exact lt_of_lt_of_le (by positivity) hNb

lemma rB_sq : rB P N ^ 2 = P.H ^ 2 * (2 * Real.log (2 / P.eps) / N) := by
  have := logpos hP hK hNb
  have := N_pos hP hK hNb
  rw [rB, mul_pow, Real.sq_sqrt (by positivity)]

lemma rB_pos : 0 < rB P N := by
  have := logpos hP hK hNb
  have := N_pos hP hK hNb
  have hH := hP.2.2.1
  rw [rB]; positivity

lemma rB_le : P.Dm * rB P N ≤ P.delta / 4 := by
  have hL := logpos hP hK hNb
  have hNr := N_pos hP hK hNb
  have hD := Dm_pos hP
  have hH := hP.2.2.1
  have hδ := hP.2.2.2.2.2.2.2.2.2.2.1
  have hr0 := rB_pos hP hK hNb
  have hsq := rB_sq hP hK hNb
  have e : 32 * (P.Dm * P.H / P.delta) ^ 2 * Real.log (2 / P.eps) * P.delta ^ 2
      = 32 * P.Dm ^ 2 * P.H ^ 2 * Real.log (2 / P.eps) := by field_simp
  have h1 : 32 * P.Dm ^ 2 * P.H ^ 2 * Real.log (2 / P.eps) ≤ N * P.delta ^ 2 := by
    rw [← e]; exact mul_le_mul_of_nonneg_right hNb (sq_nonneg _)
  have h2 : rB P N ^ 2 * N = P.H ^ 2 * (2 * Real.log (2 / P.eps)) := by
    rw [hsq]; field_simp
  have h3 : (P.Dm * rB P N) ^ 2 ≤ (P.delta / 4) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by norm_num), mul_pow]
    have : (P.Dm ^ 2 * rB P N ^ 2 * 4 ^ 2) * N ≤ P.delta ^ 2 * N := by nlinarith
    exact le_of_mul_le_mul_right this hNr
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h3

lemma tail_rB : ∑ σ : Fin N → S, (if rB P N ≤ |ebar Z σ| then mass (data P q Z) σ else 0)
    ≤ P.eps := by
  have hNr := N_pos hP hK hNb
  have hN : 0 < N := by exact_mod_cast hNr
  have hL := logpos hP hK hNb
  have hH := hP.2.2.1
  have hε := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h := tail2 hK hH hN (rB_pos hP hK hNb)
  have e : 2 * Real.exp (-(N * rB P N ^ 2) / (2 * P.H ^ 2)) = P.eps := by
    rw [rB_sq hP hK hNb]
    have : -(N * (P.H ^ 2 * (2 * Real.log (2 / P.eps) / N))) / (2 * P.H ^ 2)
        = -Real.log (2 / P.eps) := by field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [← e]
  exact h

lemma tcrit_le (hV : 0 < varZ q Z) :
    tcrit (data P q Z) N P.eps ≤ N * (rB P N ^ 2 / varZ q Z) := by
  set D := data P q Z
  have hq := hK.1
  have hε1 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := mass_sum D hK.2.1 N
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun l _ => hq _
  have hTN : ∀ σ : Fin N → S, TN D σ = N * (ebar Z σ ^ 2 / varZ q Z) := fun σ => by
    rw [TN, errN_d, quad_e hV (by simp) (by simp)]; simp
  have htail := tail_rB hP hK hNb
  have hin : 1 - P.eps ≤ ∑ σ : Fin N → S, (if |ebar Z σ| < rB P N then mass D σ else 0) := by
    have e : ∀ σ : Fin N → S, (if |ebar Z σ| < rB P N then mass D σ else 0)
        = mass D σ - (if rB P N ≤ |ebar Z σ| then mass D σ else 0) := fun σ => by
      by_cases h : |ebar Z σ| < rB P N
      · simp only [h, ↓reduceIte, not_le.mpr h]; ring
      · simp only [h, ↓reduceIte, not_lt.mp h]; ring
    simp only [e, Finset.sum_sub_distrib, hsum]
    linarith
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 ∧ |ebar Z σ0| < rB P N := by
    by_contra h
    have : ∑ σ : Fin N → S, (if |ebar Z σ| < rB P N then mass D σ else 0) ≤ 0 :=
      Finset.sum_nonpos fun σ _ => by
        split_ifs with h'
        · exact not_lt.mp fun hp => h ⟨σ, hp, h'⟩
        · exact le_rfl
    linarith
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ ∧ |ebar Z σ| < rB P N) (TN D)
    ⟨σ0, by simp [hσ0]⟩
  have hσm' := (Finset.mem_filter.mp hσm).2
  have hmemT : TN D σm ∈ {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - P.eps ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} := by
    refine ⟨⟨σm, hσm'.1, rfl⟩, le_trans hin (Finset.sum_le_sum fun σ _ => ?_)⟩
    by_cases h : |ebar Z σ| < rB P N
    · rcases (hmass σ).lt_or_eq with hp | hp
      · have := hmax σ (by simp [hp, h])
        simp only [h, this, ↓reduceIte, le_refl]
      · rw [← hp]; split_ifs <;> exact le_rfl
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith [hmass σ]
  have hbdd : BddBelow {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - P.eps ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} :=
    ((Set.finite_range (TN D)).subset fun t ht => by
      obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩).bddBelow
  calc tcrit D N P.eps ≤ TN D σm := csInf_le hbdd hmemT
    _ = N * (ebar Z σm ^ 2 / varZ q Z) := hTN σm
    _ ≤ N * (rB P N ^ 2 / varZ q Z) := by
        have h2 : ebar Z σm ^ 2 ≤ rB P N ^ 2 := by
          rw [sq_le_sq, abs_of_pos (rB_pos hP hK hNb)]; exact hσm'.2.le
        have := N_pos hP hK hNb
        gcongr

/-- Every error in `A_{N,ε}` lies on the first axis with size at most `r_B`. -/
lemma A_bound {e : Fin 3 → ℝ} (he : e ∈ Aset (data P q Z) N P.eps) :
    e 1 = 0 ∧ e 2 = 0 ∧ |e 0| ≤ rB P N := by
  obtain ⟨hr, hq⟩ := he
  rcases (varZ_nonneg (Z := Z) hK.1).lt_or_eq with hV | hV
  · obtain ⟨h1, h2⟩ := (range_iff hV e).mp hr
    refine ⟨h1, h2, ?_⟩
    rw [quad_e hV h1 h2] at hq
    have ht := tcrit_le hP hK hNb hV
    have hNr := N_pos hP hK hNb
    have : e 0 ^ 2 / varZ q Z ≤ rB P N ^ 2 / varZ q Z := le_of_mul_le_mul_left (hq.trans ht) hNr
    have : e 0 ^ 2 ≤ rB P N ^ 2 := by rwa [div_le_div_iff_of_pos_right hV] at this
    rw [sq_le_sq, abs_of_pos (rB_pos hP hK hNb)] at this
    exact this
  · obtain ⟨x, rfl⟩ := hr
    rw [omega_mulVec, ← hV]
    simp [(rB_pos hP hK hNb).le]

lemma coverage : 1 - P.eps ≤ ∑ σ : Fin N → S,
    (if errN (data P q Z) σ ∈ Aset (data P q Z) N P.eps then mass (data P q Z) σ else 0) := by
  have hq := hK.1
  refine le_trans (tcrit_mem (P := P) (Z := Z) hq hK.2.1 N hP.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (Finset.sum_le_sum fun σ _ => ?_)
  have hm : 0 ≤ mass (data P q Z) σ := Finset.prod_nonneg fun l _ => hq _
  rcases hm.lt_or_eq with hp | hp
  · by_cases h : TN (data P q Z) σ ≤ tcrit (data P q Z) N P.eps
    · have hA : errN (data P q Z) σ ∈ Aset (data P q Z) N P.eps := ⟨errN_range hq hp, h⟩
      simp only [h, hA, ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith
  · rw [← hp]; split_ifs <;> exact le_rfl

end Cert

theorem certificate : Certificate := by
  intro P hP S _ q Z hK N hNb
  have hH := hP.2.2.1
  have hδ := hP.2.2.2.2.2.2.2.2.2.2.1
  have hD := Dm_pos hP
  have hNr := N_pos hP hK hNb
  have hN : 0 < N := by exact_mod_cast hNr
  have hr0 := rB_pos hP hK hNb
  have hrle := rB_le hP hK hNb
  set D := data P q Z with hDdef
  have hq := hK.1
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := mass_sum D hK.2.1 N
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun l _ => hq _
  have hcov : 1 - P.eps ≤ ∑ σ : Fin N → S,
      (if errN D σ ∈ Aset D N P.eps then mass D σ else 0) := coverage hP hK hNb
  -- membership in `C_N`
  have hCmem : ∀ θ ∈ Theta4 P.V4, ∀ σ : Fin N → S, errN D σ ∈ Aset D N P.eps →
      θ ∈ Cset D P.V4 N P.eps (thetaHat D (hist D θ σ)) := fun θ hθ σ he =>
    ⟨hθ, errN D σ, he, by rw [thetaHat_hist hN, add_sub_cancel_right]⟩
  have hClow : ∀ th θ, θ ∈ Cset D P.V4 N P.eps th →
      θ 1 = P.mu ∧ θ 2 = 0 ∧ th 0 - rB P N ≤ θ 0 ∧ θ 0 ≤ th 0 + rB P N := by
    rintro th θ ⟨hθ, e, he, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := mem_theta4 hH hθ
    obtain ⟨-, -, hb⟩ := A_bound hP hK hNb he
    have := abs_le.mp hb
    simp only [Pi.sub_apply] at h1 h2 ⊢
    exact ⟨h1, h2, by linarith, by linarith⟩
  have hAdv_ge : ∀ (H : Fin N → Record 1) θ, θ ∈ Cset D P.V4 N P.eps (thetaHat D H) →
      ell P D H ≤ Adv D P.wA θ := by
    intro H θ hθ
    obtain ⟨h1, h2, h3, -⟩ := hClow _ θ hθ
    rw [eq_par P h1 h2, Adv_wA hP q Z, ell]
    exact mul_le_mul_of_nonneg_left (by linarith) hD.le
  have hGap : ∀ θ ∈ Theta4 P.V4, P.delta ≤ Gstar D θ → P.delta ≤ P.Dm * (θ 0 - P.lam0) := by
    intro θ hθ hG
    obtain ⟨-, -, h1, h2⟩ := mem_theta4 hH hθ
    rw [eq_par P h1 h2, Gstar_eq hP q Z] at hG
    rcases le_total (θ 0 - P.lam0) 0 with h | h
    · rw [max_eq_right h, mul_zero] at hG; linarith
    · rwa [max_eq_left h] at hG
  have hth : ∀ θ ∈ Theta4 P.V4, ∀ σ : Fin N → S,
      thetaHat D (hist D θ σ) = P.par (θ 0 + ebar Z σ) := by
    intro θ hθ σ
    obtain ⟨-, -, h1, h2⟩ := mem_theta4 hH hθ
    rw [thetaHat_hist hN, errN_d]
    funext i; fin_cases i <;> simp [Inputs.par, h1, h2]
  have hcertU : ∀ θ ∈ Theta4 P.V4, P.delta ≤ Gstar D θ → ∀ σ : Fin N → S,
      errN D σ ∈ Aset D N P.eps → certU P D (hist D θ σ) := by
    intro θ hθ hG σ he
    have hg := hGap θ hθ hG
    obtain ⟨-, -, hb⟩ := A_bound hP hK hNb he
    rw [errN_d] at hb
    simp only [Matrix.cons_val_zero] at hb
    have hb' := abs_le.mp hb
    have hmem := hCmem θ hθ σ he
    refine ⟨⟨θ, hmem⟩, ?_, ?_⟩
    · rw [wHatF, hth θ hθ σ, maxF_high hP q Z, lexSel_singleton]
      nlinarith
    · rw [ell, hth θ hθ σ]
      simp only [Inputs.par, Matrix.cons_val_zero]
      nlinarith
  refine ⟨fun H => ?_, ⟨fun θ hθ => ?_, fun θ hθ hG => ?_⟩, fun H hne _ => ?_,
    fun θ hθ hG σ hC => ?_, fun θ hθ σ => ?_⟩
  · -- the rule certifies `w_A` or falls back to `v_E`
    show Measure.dirac (if certU P D H then P.wA else P.vE) _ = 0
    have hA : P.wA ∉ {w : Inst 1 1 → ℝ | w ≠ P.vE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} :=
      fun h => h.2 ⟨wA_mem_F hP q Z, by simp [Inputs.wA, A_pos hP]⟩
    have hE : P.vE ∉ {w : Inst 1 1 → ℝ | w ≠ P.vE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} :=
      fun h => h.1 rfl
    rw [Measure.dirac_apply]
    by_cases hc : certU P D H
    · simp only [hc, ↓reduceIte]; exact Set.indicator_of_notMem hA _
    · simp only [hc, ↓reduceIte]; exact Set.indicator_of_notMem hE _
  · -- uniform false-certification control
    have hEf : P.vE ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ P.delta / 4} := by
      simp [Inputs.vE]
    calc falseP D P.delta θ (gateRule P D N)
        ≤ ∑ σ : Fin N → S, (if errN D σ ∈ Aset D N P.eps then 0 else mass D σ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          show mass D σ * (Measure.dirac (if certU P D (hist D θ σ) then P.wA else P.vE) _).toReal
            ≤ _
          rw [dirac_toReal]
          by_cases he : errN D σ ∈ Aset D N P.eps
          · by_cases hc : certU P D (hist D θ σ)
            · have hA : P.wA ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ P.delta / 4} :=
                fun h => by
                  have := hAdv_ge _ θ (hCmem θ hθ σ he)
                  linarith [h.2, hc.2.2]
              simp [hc, hA, he]
            · simp [hc, hEf, he]
          · simp only [he, ↓reduceIte]
            split_ifs <;> linarith [hmass σ]
      _ ≤ P.eps := by
          have e : ∀ σ : Fin N → S, (if errN D σ ∈ Aset D N P.eps then 0 else mass D σ)
              = mass D σ - (if errN D σ ∈ Aset D N P.eps then mass D σ else 0) := fun σ => by
            split_ifs <;> ring
          simp only [e, Finset.sum_sub_distrib, hsum]
          linarith
  · -- uniform power
    have hg := hGap θ hθ hG
    refine le_trans hcov (Finset.sum_le_sum fun σ _ => ?_)
    show _ ≤ mass D σ * (Measure.dirac (if certU P D (hist D θ σ) then P.wA else P.vE) _).toReal
    rw [dirac_toReal]
    by_cases he : errN D σ ∈ Aset D N P.eps
    · have hc := hcertU θ hθ hG σ he
      obtain ⟨-, -, h1, h2⟩ := mem_theta4 hH hθ
      have hA : P.wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ P.delta / 4 < Adv D w θ} := by
        refine ⟨by simp [Inputs.wA, A_pos hP], ?_⟩
        rw [eq_par P h1 h2, Adv_wA hP q Z]
        linarith
      simp [hc, hA, he]
    · simp only [he, ↓reduceIte]
      split_ifs <;> linarith [hmass σ]
  · -- `ℓ_N ≤ L_N`
    rw [LN]
    simp only [hne.ne_empty, ↓reduceIte]
    exact le_iInf₂ fun θ hθ => EReal.coe_le_coe_iff.mpr (hAdv_ge H θ hθ)
  · -- `ℓ_N ≥ δ/2` on coverage
    have hg := hGap θ hθ hG
    obtain ⟨-, -, -, h4⟩ := hClow _ θ hC
    rw [ell]
    nlinarith
  · -- the plug-in fallback is `v_E`
    rw [vHatE, hth θ hθ σ, maxE hP q Z, lexSel_singleton]

theorem sameOrder : SameOrder := by
  intro ε hε hε1
  have h16 : (16 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have hl := Real.log_le_log (by norm_num) h16
  have e16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have e2 : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [show 2 / ε = 2 * (1 / ε) by ring, Real.log_mul (by norm_num) (by positivity)]
  rw [e2]
  linarith

theorem proof : Standalone.M4BoundedLawRate.statement :=
  ⟨geometry, lowerBound, certificate, sameOrder⟩

end

end Novel.M4BoundedLawRateProof

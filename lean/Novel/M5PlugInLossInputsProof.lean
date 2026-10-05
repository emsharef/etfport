import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Novel.M5MissingDirectionLeakProof
import Novel.M5PartialAdjustmentSplitProof
import Standalone.M5PlugInLossInputs

/-!
# Claim 034: proof

Part 1 unrolls the plug-in path and swaps the double sum over reviews and innovations. The loss
expression vanishes only at zero `μ` and `W`, by square roots of `D_t` and `V_u` (claim 030's
`sqrt_exists`). 2(a) is symmetric-matrix algebra. The fund's scalar recursion is claim 030's
recursion read on `1 × 1` matrices. Part 3 expands every recursion quantity to second order in the
error (3(i)), follows it to zero cost by continuity (3(ii)), and bounds it at large cost (3(iii)).
-/

namespace Novel.M5PlugInLossInputsProof

open Matrix Filter Topology Asymptotics Standalone.M5PartialAdjustmentSplit
open Standalone.M5PlugInLossInputs Novel.M5PartialAdjustmentSplitProof

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Part 1 -/

section General

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π]

lemma prodK_succ (K : ℕ → Matrix ι ι ℝ) {t s : ℕ} (h : s ≤ t) :
    prodK K (t + 1) s = K t * prodK K t s := by
  simp [prodK, h]

lemma prodK_self (K : ℕ → Matrix ι ι ℝ) (t : ℕ) : prodK K t t = 1 := by
  cases t with
  | zero => rfl
  | succ t => simp [prodK]

lemma path_eq (K : ℕ → Matrix ι ι ℝ) (L : ℕ → Matrix ι π ℝ) (l : ℕ → ι → ℝ) (x0 : ι → ℝ)
    (m : ℕ → π → ℝ) : ∀ t, path K L l x0 m t = prodK K t 0 *ᵥ x0 +
      ∑ s ∈ Finset.range t, prodK K t (s + 1) *ᵥ (L s *ᵥ m s + l s)
  | 0 => by simp [path, prodK]
  | t + 1 => by
    rw [path, path_eq K L l x0 m t, Finset.sum_range_succ, prodK_self, one_mulVec,
      prodK_succ K (Nat.zero_le t), mulVec_add, mulVec_sum, ← mulVec_mulVec]
    have e : ∀ s ∈ Finset.range t, K t *ᵥ (prodK K t (s + 1) *ᵥ (L s *ᵥ m s + l s)) =
        prodK K (t + 1) (s + 1) *ᵥ (L s *ᵥ m s + l s) := fun s hs => by
      rw [prodK_succ K (by simp at hs; omega), mulVec_mulVec]
    rw [Finset.sum_congr rfl e]
    abel

lemma pathwise_err (K : ℕ → Matrix ι ι ℝ) (L : ℕ → Matrix ι π ℝ) (l : ℕ → ι → ℝ)
    (dK : ℕ → Matrix ι ι ℝ) (dL : ℕ → Matrix ι π ℝ) (dl : ℕ → ι → ℝ) (x0 : ι → ℝ) (m0 : π → ℝ)
    (η : ℕ → π → ℝ) (t : ℕ) :
    dK t *ᵥ path K L l x0 (means m0 η) t + dL t *ᵥ means m0 η t + dl t =
      mu K L l dK dL dl x0 m0 t + ∑ u ∈ Finset.range t, W K L dK dL t u *ᵥ η u := by
  rw [path_eq]
  have hsw : ∑ s ∈ Finset.range t, ∑ u ∈ Finset.range s,
      dK t *ᵥ (prodK K t (s + 1) *ᵥ (L s *ᵥ η u)) =
      ∑ u ∈ Finset.range t, ∑ s ∈ Finset.Ico (u + 1) t, dK t *ᵥ (prodK K t (s + 1) *ᵥ (L s *ᵥ η u)) :=
    Finset.sum_comm' (fun s u => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  simp only [mu, W, means, mulVec_add, mulVec_sum, add_mulVec, Finset.sum_add_distrib, sum_mulVec,
    ← mulVec_mulVec]
  rw [hsw]
  abel

/-- `tr(D W V W') ≥ 0`, with equality iff `W = 0`, for `D, V ≻ 0`. -/
lemma trace_term {D : Matrix ι ι ℝ} {V : Matrix π π ℝ} [DecidableEq π] (hD : D.PosDef)
    (hV : V.PosDef) (Wm : Matrix ι π ℝ) :
    0 ≤ (D * Wm * V * Wmᵀ).trace ∧ ((D * Wm * V * Wmᵀ).trace = 0 ↔ Wm = 0) := by
  obtain ⟨R, hRs, hRR, hRu⟩ := sqrt_exists hD
  obtain ⟨Q, hQs, hQQ, hQu⟩ := sqrt_exists hV
  set M := R * Wm * Q
  have e : (D * Wm * V * Wmᵀ).trace = (M * Mᴴ).trace := by
    have h1 : M * Mᴴ = R * (Wm * Q * Q * Wmᵀ * R) := by
      simp only [M, conjTranspose_eq_transpose_of_trivial, transpose_mul, hRs, hQs, Matrix.mul_assoc]
    rw [h1, ← hRR, ← hQQ, show R * R * Wm * (Q * Q) * Wmᵀ = R * (R * Wm * Q * Q * Wmᵀ) by
      simp only [Matrix.mul_assoc], trace_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [trace]; exact Finset.sum_nonneg fun i _ => (posSemidef_self_mul_conjTranspose M).diag_nonneg
  · rw [trace_mul_conjTranspose_self_eq_zero_iff]
    constructor
    · intro h
      have hR := (isUnit_iff_isUnit_det R).mp hRu
      have hQ := (isUnit_iff_isUnit_det Q).mp hQu
      have : Wm = R⁻¹ * M * Q⁻¹ := by
        rw [show R⁻¹ * M * Q⁻¹ = (R⁻¹ * R) * Wm * (Q * Q⁻¹) by simp only [M, Matrix.mul_assoc],
          nonsing_inv_mul _ hR, mul_nonsing_inv _ hQ, Matrix.one_mul, Matrix.mul_one]
      rw [this, h, Matrix.mul_zero, Matrix.zero_mul]
    · intro h; simp [M, h]

end General

theorem pathwise : Pathwise := by
  intro ι π _ _ _ K L l dK dL dl x0 m0 η
  classical
  refine ⟨path_eq K L l x0 _, pathwise_err K L l dK dL dl x0 m0 η, fun T rho D V hr hD hV => ?_,
    fun h t => ⟨?_, fun u => ?_⟩⟩
  · have hq : ∀ t, 0 ≤ mu K L l dK dL dl x0 m0 t ⬝ᵥ (D t *ᵥ mu K L l dK dL dl x0 m0 t) ∧
        (mu K L l dK dL dl x0 m0 t ⬝ᵥ (D t *ᵥ mu K L l dK dL dl x0 m0 t) = 0 ↔
          mu K L l dK dL dl x0 m0 t = 0) := fun t => by
      refine ⟨?_, ⟨fun h0 => ?_, fun h0 => by simp [h0]⟩⟩
      · by_cases h0 : mu K L l dK dL dl x0 m0 t = 0
        · simp [h0]
        · have := (hD t).dotProduct_mulVec_pos h0; rw [star_trivial] at this; exact this.le
      · by_contra hne
        have := (hD t).dotProduct_mulVec_pos hne
        rw [star_trivial, h0] at this
        exact lt_irrefl _ this
    have hterm : ∀ t, 0 ≤ rho ^ t * (mu K L l dK dL dl x0 m0 t ⬝ᵥ (D t *ᵥ mu K L l dK dL dl x0 m0 t) +
        ∑ u ∈ Finset.range t, (D t * W K L dK dL t u * V u * (W K L dK dL t u)ᵀ).trace) := fun t =>
      mul_nonneg (pow_nonneg hr.le t) (add_nonneg (hq t).1
        (Finset.sum_nonneg fun u _ => (trace_term (hD t) (hV u) _).1))
    rw [lossF, mul_eq_zero, or_iff_right (by norm_num),
      Finset.sum_eq_zero_iff_of_nonneg fun t _ => hterm t]
    refine ⟨fun h t ht => ?_, fun h t ht => ?_⟩
    · have h1 := h t (Finset.mem_range.mpr ht)
      rw [mul_eq_zero, or_iff_right (pow_ne_zero _ hr.ne'),
        add_eq_zero_iff_of_nonneg (hq t).1 (Finset.sum_nonneg fun u _ => (trace_term (hD t) (hV u) _).1),
        Finset.sum_eq_zero_iff_of_nonneg fun u _ => (trace_term (hD t) (hV u) _).1] at h1
      exact ⟨(hq t).2.mp h1.1, fun u hu => (trace_term (hD t) (hV u) _).2.mp
        (h1.2 u (Finset.mem_range.mpr hu))⟩
    · obtain ⟨h1, h2⟩ := h t (Finset.mem_range.mp ht)
      rw [h1]
      simp only [zero_dotProduct, zero_add]
      rw [Finset.sum_eq_zero fun u hu => by rw [h2 u (Finset.mem_range.mp hu)]; simp, mul_zero]
  · simp [mu, (h t).1, (h t).2.1, (h t).2.2]
  · simp [W, (h t).1, (h t).2.1]

/-! ### Part 2(a) -/

theorem exposure : Exposure := by
  intro κ _ _ Sig Sig' gamma lh hS hS' hg
  have hA : (Sig'⁻¹ - Sig⁻¹)ᵀ = Sig'⁻¹ - Sig⁻¹ := by
    rw [transpose_sub, transpose_nonsing_inv, transpose_nonsing_inv, hS, hS']
  refine ⟨?_, ?_⟩
  · have e : (1 / gamma) • (Sig'⁻¹ *ᵥ lh) - (1 / gamma) • (Sig⁻¹ *ᵥ lh) =
        (1 / gamma) • ((Sig'⁻¹ - Sig⁻¹) *ᵥ lh) := by rw [← smul_sub, sub_mulVec]
    have core : ((Sig'⁻¹ - Sig⁻¹) *ᵥ lh) ⬝ᵥ (Sig *ᵥ ((Sig'⁻¹ - Sig⁻¹) *ᵥ lh)) =
        lh ⬝ᵥ (((Sig'⁻¹ - Sig⁻¹) * Sig * (Sig'⁻¹ - Sig⁻¹)) *ᵥ lh) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec lh (Sig'⁻¹ - Sig⁻¹), ← mulVec_transpose,
        hA]
    show gamma / 2 * (((1 / gamma) • (Sig'⁻¹ *ᵥ lh) - (1 / gamma) • (Sig⁻¹ *ᵥ lh)) ⬝ᵥ
      (Sig *ᵥ ((1 / gamma) • (Sig'⁻¹ *ᵥ lh) - (1 / gamma) • (Sig⁻¹ *ᵥ lh)))) = _
    rw [e, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, core]
    field_simp
  · generalize (Sig'⁻¹ - Sig⁻¹) * Sig * (Sig'⁻¹ - Sig⁻¹) = Δ
    simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### Part 3(v) -/

theorem precision : Precision := by
  intro sig2 t hs a ha b hb hab
  simp only [pvar]
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := lt_trans ha' hab
  have hc : 0 ≤ (t : ℝ) / sig2 := div_nonneg (Nat.cast_nonneg t) hs.le
  exact one_div_lt_one_div_of_lt (by positivity) (by
    have := one_div_lt_one_div_of_lt ha' hab; linarith)

/-! ### The fund's scalar recursion -/

section FundLemmas

variable (F : Fund)

lemma aS_lt {v : ℝ} {t : ℕ} (ht : t < F.T) : F.aS v t = F.lam - F.lam ^ 2 / F.dS v t := by
  rw [Fund.aS, ite_eq_left ht]; rfl

lemma aS_ge {v : ℝ} {t : ℕ} (ht : F.T ≤ t) : F.aS v t = 0 := by
  rw [Fund.aS, ite_eq_right (by omega)]

lemma qS_lt {v : ℝ} {t : ℕ} (ht : t < F.T) :
    F.qS v t = (1 + F.rho * F.lam * F.qS v (t + 1)) / F.dS v t := by
  rw [Fund.qS, ite_eq_left ht]

lemma qS_ge {v : ℝ} {t : ℕ} (ht : F.T ≤ t) : F.qS v t = 0 := by
  rw [Fund.qS, ite_eq_right (by omega)]

lemma aP_lt {t : ℕ} (ht : t < F.T) :
    F.aP t = F.lam ^ 2 * F.dP t / F.dS F.sig2 t ^ 2 := by
  rw [Fund.aP, ite_eq_left ht]; rfl

lemma aP_ge {t : ℕ} (ht : F.T ≤ t) : F.aP t = 0 := by
  rw [Fund.aP, ite_eq_right (by omega)]

lemma qP_lt {t : ℕ} (ht : t < F.T) : F.qP t = (F.rho * F.lam * F.qP (t + 1) * F.dS F.sig2 t -
    (1 + F.rho * F.lam * F.qS F.sig2 (t + 1)) * F.dP t) / F.dS F.sig2 t ^ 2 := by
  rw [Fund.qP, ite_eq_left ht]

lemma qP_ge {t : ℕ} (ht : F.T ≤ t) : F.qP t = 0 := by
  rw [Fund.qP, ite_eq_right (by omega)]

lemma pk_succ (v : ℝ) {t s : ℕ} (h : s ≤ t) : F.pk v (t + 1) s = F.kS v t * F.pk v t s := by
  rw [Fund.pk, Finset.prod_Ico_succ_top h, mul_comm]; rfl

lemma pk_self (v : ℝ) (t : ℕ) : F.pk v t t = 1 := by simp [Fund.pk]

end FundLemmas

lemma m11 (M N : Matrix (Fin 1) (Fin 1) ℝ) : (M * N) 0 0 = M 0 0 * N 0 0 := by
  simp [mul_apply]

lemma inv11' (M : Matrix (Fin 1) (Fin 1) ℝ) : M⁻¹ 0 0 = (M 0 0)⁻¹ := by
  rw [inv_def, adjugate_fin_one, det_unique, Ring.inverse_eq_inv']
  simp

theorem recursion : Recursion := by
  intro F v
  set Q := F.lq v
  have hD : ∀ t, Q.D t 0 0 = F.lam + F.gam * (v + F.p t) + F.rho * Q.A (t + 1) 0 0 := fun t => by
    simp [Q, LQ.D, Fund.lq]
  suffices h : ∀ k t, F.T - t = k → Q.A t 0 0 = F.aS v t ∧ Q.C t 0 0 = F.lam * F.qS v t by
    intro t ht
    have h1 := h _ (t + 1) rfl
    have hDt : Q.D t 0 0 = F.dS v t := by rw [hD, h1.1]; rfl
    refine ⟨(h _ t rfl).1, hDt, ?_, ?_⟩
    · rw [LQ.K, m11, inv11', hDt]
      simp [Q, Fund.lq, Fund.kS, div_eq_inv_mul]
    · rw [LQ.L, m11, inv11', hDt, Matrix.add_apply, Matrix.smul_apply, h1.2, (qS_lt F) ht]
      simp [Q, Fund.lq]; ring
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [LQ.A_ge Q (by simp [Q, Fund.lq]; omega), LQ.C_ge Q (by simp [Q, Fund.lq]; omega),
      (aS_ge F) (by omega), (qS_ge F) (by omega)]
    simp
  | succ k ih =>
    intro t ht
    have htT : t < Q.T := by simp [Q, Fund.lq]; omega
    obtain ⟨eA, eC, -⟩ := LQ.ric_lt Q htT
    obtain ⟨h1, h2⟩ := ih (t + 1) (by omega)
    have hDt : Q.D t 0 0 = F.dS v t := by rw [hD, h1]; rfl
    refine ⟨?_, ?_⟩
    · rw [eA, Matrix.sub_apply, m11, m11, inv11', hDt, (aS_lt F (t := t)) (by simpa [Q, Fund.lq] using htT)]
      simp [Q, Fund.lq]; ring
    · rw [eC, m11, m11, inv11', hDt, Matrix.add_apply, Matrix.smul_apply, h2,
        (qS_lt F (t := t)) (by simpa [Q, Fund.lq] using htT)]
      simp [Q, Fund.lq]; ring

theorem fundPath : FundPath := by
  intro F v' x0 a0 η x hx0 hx t
  set al : ℕ → ℝ := fun s => a0 + ∑ u ∈ Finset.range s, η u
  have hxe : ∀ t, x t = F.pk v' t 0 * x0 +
      ∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s * al s := by
    intro t
    induction t with
    | zero => simp [hx0, Fund.pk]
    | succ t ih =>
      rw [hx, ih, Finset.sum_range_succ, (pk_self F), (pk_succ F) v' (Nat.zero_le t), mul_add,
        Finset.mul_sum]
      have e : ∀ s ∈ Finset.range t, F.kS v' t * (F.pk v' t (s + 1) * F.qS v' s * al s) =
          F.pk v' (t + 1) (s + 1) * F.qS v' s * al s := fun s hs => by
        rw [(pk_succ F) v' (by simp at hs; omega)]; ring
      rw [Finset.sum_congr rfl e]
      simp only [al]; ring
  rw [hxe]
  have hsw : ∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s * (∑ u ∈ Finset.range s, η u) =
      ∑ u ∈ Finset.range t, (∑ s ∈ Finset.Ico (u + 1) t, F.pk v' t (s + 1) * F.qS v' s) * η u := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm' (fun s u => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  have h1 : ∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s * al s =
      (∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s) * a0 +
        ∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s * (∑ u ∈ Finset.range s, η u) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [al]; ring
  have h2 : ∑ u ∈ Finset.range t, F.wA v' t u * η u =
      (F.kS v' t - F.kS F.sig2 t) *
        ∑ u ∈ Finset.range t, (∑ s ∈ Finset.Ico (u + 1) t, F.pk v' t (s + 1) * F.qS v' s) * η u +
      (F.qS v' t - F.qS F.sig2 t) * ∑ u ∈ Finset.range t, η u := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by simp only [Fund.wA]; ring
  rw [h1, hsw, h2, Fund.muA]
  ring

/-! ### Part 3(iv): one review -/

lemma one_formula (F : Fund) (hT : F.T = 1) (v' x0 a0 : ℝ) :
    F.LossA v' x0 a0 = 1 / 2 * (F.lam + F.gam * (F.sig2 + F.p 0)) *
      ((F.lam * x0 + a0) * (1 / (F.lam + F.gam * (v' + F.p 0)) -
        1 / (F.lam + F.gam * (F.sig2 + F.p 0)))) ^ 2 := by
  have hd : ∀ v, F.dS v 0 = F.lam + F.gam * (v + F.p 0) := fun v => by
    rw [Fund.dS, aS_ge F (by omega), mul_zero, add_zero]
  have hl : ∀ v, F.qS v 0 = 1 / (F.lam + F.gam * (v + F.p 0)) := fun v => by
    rw [qS_lt F (by omega), qS_ge F (by omega), hd, mul_zero, add_zero]
  simp only [Fund.LossA, Fund.muA, hT, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, mul_zero, zero_add, add_zero, pk_self, mul_one, Fund.kS, hd, hl]
  ring

theorem oneReview : OneReview := by
  intro F hS hT v' x0 a0 hv
  obtain ⟨hl, hg, hr0, hr1, hs, hp⟩ := hS
  refine ⟨one_formula F hT v' x0 a0, fun ha hx hne => ?_⟩
  set r := F.gam * (F.sig2 + F.p 0) with hrd
  set r' := F.gam * (v' + F.p 0) with hrd'
  have hr : 0 < r := mul_pos hg (by linarith [hp 0])
  have hr' : 0 < r' := mul_pos hg (by linarith [hp 0])
  have hrr : r ≠ r' := fun h => hne (by
    have := mul_left_cancel₀ hg.ne' h; linarith)
  have hval : ∀ lam, 0 < lam → (F.withLam lam).LossA v' x0 a0 =
      1 / 2 * x0 ^ 2 * (r - r') ^ 2 * (lam ^ 2 / ((lam + r') ^ 2 * (lam + r))) := fun lam hlam => by
    rw [one_formula (F.withLam lam) hT v' x0 a0]
    simp only [Fund.withLam, ha, add_zero]
    rw [← hrd, ← hrd']
    have h1 : lam + r ≠ 0 := by positivity
    have h2 : lam + r' ≠ 0 := by positivity
    field_simp
    ring
  refine ⟨fun lam hlam => ?_, ?_, ?_⟩
  · rw [hval lam hlam]
    have : 0 < (r - r') ^ 2 := by positivity
    have : 0 < x0 ^ 2 := by positivity
    positivity
  · have hc : ContinuousAt (fun lam : ℝ => 1 / 2 * x0 ^ 2 * (r - r') ^ 2 *
        (lam ^ 2 / ((lam + r') ^ 2 * (lam + r)))) 0 := by
      refine continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
      simp only [zero_add]; positivity
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact (hval lam hlam).symm
  · have hK : 0 ≤ 1 / 2 * x0 ^ 2 * (r - r') ^ 2 := by positivity
    have hup : Tendsto (fun lam : ℝ => 1 / 2 * x0 ^ 2 * (r - r') ^ 2 * lam⁻¹) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (1 / 2 * x0 ^ 2 * (r - r') ^ 2)
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with lam hlam
      rw [hval lam hlam]; positivity
    · filter_upwards [eventually_gt_atTop 0] with lam hlam
      rw [hval lam hlam]
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hlam]
      nlinarith [sq_nonneg lam, mul_pos hlam hr, mul_pos hlam hr', sq_nonneg r', mul_pos hr hr',
        mul_pos (mul_pos hlam hlam) hr']

/-! ### Part 3(ii): the costless limit -/

section WL

variable (F : Fund) (lam : ℝ)

@[simp] lemma wl_lam : (F.withLam lam).lam = lam := rfl
@[simp] lemma wl_rho : (F.withLam lam).rho = F.rho := rfl
@[simp] lemma wl_gam : (F.withLam lam).gam = F.gam := rfl
@[simp] lemma wl_sig2 : (F.withLam lam).sig2 = F.sig2 := rfl
@[simp] lemma wl_p : (F.withLam lam).p = F.p := rfl
@[simp] lemma wl_T : (F.withLam lam).T = F.T := rfl

end WL

section Costless0

variable (F : Fund) (v : ℝ)

lemma wl_a (lam : ℝ) (t : ℕ) (ht : t < F.T) : (F.withLam lam).aS v t =
    lam - lam ^ 2 / (lam + F.gam * (v + F.p t) + F.rho * (F.withLam lam).aS v (t + 1)) := by
  rw [aS_lt (F.withLam lam) ht]; rfl

lemma wl_d (lam : ℝ) (t : ℕ) : (F.withLam lam).dS v t =
    lam + F.gam * (v + F.p t) + F.rho * (F.withLam lam).aS v (t + 1) := rfl

lemma wl_l (lam : ℝ) (t : ℕ) (ht : t < F.T) : (F.withLam lam).qS v t =
    (1 + F.rho * lam * (F.withLam lam).qS v (t + 1)) / (F.withLam lam).dS v t := by
  rw [qS_lt (F.withLam lam) ht]; rfl

variable {F v} (hr : ∀ t, 0 < F.gam * (v + F.p t))
include hr

lemma lim_a : ∀ t, Tendsto (fun lam => (F.withLam lam).aS v t) (𝓝[>] 0) (𝓝 0) := by
  suffices h : ∀ k t, F.T - t = k → Tendsto (fun lam => (F.withLam lam).aS v t) (𝓝[>] 0) (𝓝 0) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    simp only [aS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega)]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    have hi := ih (t + 1) (by omega)
    have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hd : Tendsto (fun lam => lam + F.gam * (v + F.p t) + F.rho * (F.withLam lam).aS v (t + 1))
        (𝓝[>] 0) (𝓝 (0 + F.gam * (v + F.p t) + F.rho * 0)) :=
      (hid.add (tendsto_const_nhds (x := F.gam * (v + F.p t)))).add
        ((tendsto_const_nhds (x := F.rho)).mul hi)
    have := hid.sub ((hid.pow 2).div hd (by rw [zero_add, mul_zero, add_zero]; exact (hr t).ne'))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at this
    exact this.congr fun lam => (wl_a F v lam t htT).symm

lemma lim_d (t : ℕ) : Tendsto (fun lam => (F.withLam lam).dS v t) (𝓝[>] 0)
    (𝓝 (F.gam * (v + F.p t))) := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have := (hid.add (tendsto_const_nhds (x := F.gam * (v + F.p t)))).add
    ((tendsto_const_nhds (x := F.rho)).mul (lim_a hr (t + 1)))
  simp only [zero_add, mul_zero, add_zero] at this
  exact this.congr fun lam => (wl_d F v lam t).symm

lemma lim_k (t : ℕ) : Tendsto (fun lam => (F.withLam lam).kS v t) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have := hid.div (lim_d hr t) (hr t).ne'
  rw [zero_div] at this
  exact this

lemma lim_l : ∀ t, Tendsto (fun lam => (F.withLam lam).qS v t) (𝓝[>] 0)
    (𝓝 (if t < F.T then 1 / (F.gam * (v + F.p t)) else 0)) := by
  suffices h : ∀ k t, F.T - t = k → Tendsto (fun lam => (F.withLam lam).qS v t) (𝓝[>] 0)
      (𝓝 (if t < F.T then 1 / (F.gam * (v + F.p t)) else 0)) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [ite_eq_right (by omega)]
    simp only [qS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega)]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    rw [ite_eq_left htT]
    have hi := ih (t + 1) (by omega)
    have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add (((tendsto_const_nhds (x := F.rho)).mul hid).mul
      hi)).div (lim_d hr t) (hr t).ne'
    simp only [mul_zero, zero_mul, add_zero] at this
    exact this.congr fun lam => (wl_l F v lam t htT).symm

end Costless0

theorem costless : Costless := by
  intro F hS v' x0 a0 hv
  obtain ⟨hl, hg, hr0, hr1, hs, hp⟩ := hS
  have hr' : ∀ t, 0 < F.gam * (v' + F.p t) := fun t => mul_pos hg (by linarith [hp t])
  have hr : ∀ t, 0 < F.gam * (F.sig2 + F.p t) := fun t => mul_pos hg (by linarith [hp t])
  set Lp : ℕ → ℝ := fun t => if t < F.T then 1 / (F.gam * (v' + F.p t)) else 0
  set Lt : ℕ → ℝ := fun t => if t < F.T then 1 / (F.gam * (F.sig2 + F.p t)) else 0
  have hk' := lim_k hr' (F := F)
  have hk := lim_k hr (F := F)
  have hl' := lim_l hr' (F := F)
  have hlt := lim_l hr (F := F)
  have hpk : ∀ t s, Tendsto (fun lam => (F.withLam lam).pk v' t s) (𝓝[>] 0)
      (𝓝 (∏ j ∈ Finset.Ico s t, (0 : ℝ))) := fun t s =>
    tendsto_finsetProd _ fun j _ => hk' j
  have hmu : ∀ t, Tendsto (fun lam => (F.withLam lam).muA v' x0 a0 t) (𝓝[>] 0)
      (𝓝 ((Lp t - Lt t) * a0)) := fun t => by
    have := (((hk' t).sub (hk t)).mul (hpk t 0)).mul (tendsto_const_nhds (x := x0)) |>.add
      ((((hk' t).sub (hk t)).mul (tendsto_finsetSum (Finset.range t) fun s _ =>
        (hpk t (s + 1)).mul (hl' s))).add
        ((hl' t).sub (hlt t)) |>.mul (tendsto_const_nhds (x := a0)))
    simp only [sub_self, zero_mul, zero_add] at this
    exact this
  have hw : ∀ t u, Tendsto (fun lam => (F.withLam lam).wA v' t u) (𝓝[>] 0) (𝓝 (Lp t - Lt t)) :=
    fun t u => by
      have := (((hk' t).sub (hk t)).mul (tendsto_finsetSum (Finset.Ico (u + 1) t) fun s _ =>
        (hpk t (s + 1)).mul (hl' s))).add ((hl' t).sub (hlt t))
      simp only [sub_self, zero_mul, zero_add] at this
      exact this
  have hL := (tendsto_finsetSum (Finset.range F.T) fun t _ =>
    ((tendsto_const_nhds (x := F.rho ^ t)).mul (lim_d hr t (F := F))).mul (((hmu t).pow 2).add
      (tendsto_finsetSum (Finset.range t) fun u _ => ((hw t u).pow 2).mul
        (tendsto_const_nhds (x := F.p u - F.p (u + 1)))))).const_mul (1 / 2)
  have hval : 1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * (F.gam * (F.sig2 + F.p t)) *
      (((Lp t - Lt t) * a0) ^ 2 + ∑ u ∈ Finset.range t, (Lp t - Lt t) ^ 2 * (F.p u - F.p (u + 1))) =
      1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * (F.gam * (F.sig2 + F.p t)) *
        (1 / (F.gam * (v' + F.p t)) - 1 / (F.gam * (F.sig2 + F.p t))) ^ 2 *
          (a0 ^ 2 + (F.p 0 - F.p t)) := by
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have htT := Finset.mem_range.mp ht
    simp only [Lp, Lt, ite_eq_left htT]
    rw [← Finset.mul_sum, Finset.sum_range_sub' F.p t]
    ring
  rw [← hval]
  exact hL

/-! ### Part 3(iii): the infinite-cost limit -/

lemma ratio_lim {X : ℝ → ℝ} {x : ℝ} (hX : Tendsto X atTop (𝓝 x)) :
    Tendsto (fun lam => lam / (lam + X lam)) atTop (𝓝 1) ∧
      ∀ᶠ lam in atTop, 0 < lam ∧ 0 < lam + X lam := by
  have h0 : Tendsto (fun lam => X lam * lam⁻¹) atTop (𝓝 0) := by
    simpa using hX.mul tendsto_inv_atTop_zero
  have h1 : Tendsto (fun lam => 1 + X lam * lam⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  have hev : ∀ᶠ lam in atTop, 0 < lam ∧ 0 < lam + X lam := by
    filter_upwards [eventually_gt_atTop 0, h1.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with lam hl h
    refine ⟨hl, ?_⟩
    have : lam + X lam = lam * (1 + X lam * lam⁻¹) := by field_simp
    rw [this]; exact mul_pos hl (by linarith)
  refine ⟨?_, hev⟩
  have := (tendsto_const_nhds (x := (1 : ℝ))).div h1 one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [hev] with lam hl
  show 1 / (1 + X lam * lam⁻¹) = lam / (lam + X lam)
  have h2 := hl.2.ne'
  field_simp [hl.1.ne']

section Costly0

variable (F : Fund)

/-- `λ/d_t` tends to `1`, and `d_t > 0` eventually. -/
lemma costly_a : ∀ v t, ∃ α, Tendsto (fun lam => (F.withLam lam).aS v t) atTop (𝓝 α) := by
  intro v
  suffices h : ∀ k t, F.T - t = k → ∃ α, Tendsto (fun lam => (F.withLam lam).aS v t) atTop (𝓝 α) from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨0, ?_⟩
    simp only [aS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega)]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    obtain ⟨α, hα⟩ := ih (t + 1) (by omega)
    have hX : Tendsto (fun lam => F.gam * (v + F.p t) + F.rho * (F.withLam lam).aS v (t + 1)) atTop
        (𝓝 (F.gam * (v + F.p t) + F.rho * α)) :=
      (tendsto_const_nhds).add ((tendsto_const_nhds (x := F.rho)).mul hα)
    obtain ⟨hr, hev⟩ := ratio_lim hX
    refine ⟨(F.gam * (v + F.p t) + F.rho * α) * 1, (hX.mul hr).congr' ?_⟩
    filter_upwards [hev] with lam hl
    have h2 := hl.2.ne'
    rw [wl_a F v lam t htT, add_assoc]
    field_simp
    ring

lemma costly_ratio (v : ℝ) (t : ℕ) : Tendsto (fun lam => lam / (F.withLam lam).dS v t) atTop (𝓝 1) ∧
    ∀ᶠ lam in atTop, 0 < lam ∧ 0 < (F.withLam lam).dS v t := by
  obtain ⟨α, hα⟩ := costly_a F v (t + 1)
  have hX : Tendsto (fun lam => F.gam * (v + F.p t) + F.rho * (F.withLam lam).aS v (t + 1)) atTop
      (𝓝 (F.gam * (v + F.p t) + F.rho * α)) :=
    (tendsto_const_nhds).add ((tendsto_const_nhds (x := F.rho)).mul hα)
  obtain ⟨hr, hev⟩ := ratio_lim hX
  refine ⟨hr.congr fun lam => ?_, hev.mono fun lam h => ⟨h.1, ?_⟩⟩
  · rw [wl_d, add_assoc]
  · rw [wl_d, add_assoc]; exact h.2

lemma costly_l (v : ℝ) : ∀ t, ∃ c, Tendsto (fun lam => lam * (F.withLam lam).qS v t) atTop (𝓝 c) := by
  suffices h : ∀ k t, F.T - t = k →
      ∃ c, Tendsto (fun lam => lam * (F.withLam lam).qS v t) atTop (𝓝 c) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨0, ?_⟩
    simp only [qS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega),
      mul_zero]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    obtain ⟨c, hc⟩ := ih (t + 1) (by omega)
    obtain ⟨hr, -⟩ := costly_ratio F v t
    refine ⟨_, (((tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := F.rho)).mul hc)).mul
      hr).congr fun lam => ?_⟩
    rw [wl_l F v lam t htT]
    ring

end Costly0

section Costly1

variable (F : Fund) (v v' : ℝ)

lemma costly_dinv (t : ℕ) : Tendsto (fun lam => (F.withLam lam).dS v t / lam) atTop (𝓝 1) := by
  obtain ⟨hr, hev⟩ := costly_ratio F v t
  have := hr.inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr' ?_
  filter_upwards [hev] with lam _
  rw [inv_div]

lemma costly_Dd (t : ℕ) : ∃ c, Tendsto (fun lam => (F.withLam lam).dS v t - (F.withLam lam).dS v' t)
    atTop (𝓝 c) := by
  obtain ⟨α, hα⟩ := costly_a F v (t + 1)
  obtain ⟨α', hα'⟩ := costly_a F v' (t + 1)
  refine ⟨_, ((tendsto_const_nhds (x := F.gam * (v - v'))).add
    ((tendsto_const_nhds (x := F.rho)).mul (hα.sub hα'))).congr fun lam => ?_⟩
  rw [wl_d, wl_d]; ring

lemma costly_dk (t : ℕ) : ∃ c, Tendsto (fun lam => lam * ((F.withLam lam).kS v' t -
    (F.withLam lam).kS v t)) atTop (𝓝 c) := by
  obtain ⟨hr, hev⟩ := costly_ratio F v t
  obtain ⟨hr', hev'⟩ := costly_ratio F v' t
  obtain ⟨c, hc⟩ := costly_Dd F v v' t
  refine ⟨_, ((hr'.mul hr).mul hc).congr' ?_⟩
  filter_upwards [hev, hev'] with lam h h'
  simp only [Fund.kS, wl_lam]
  have := h.2.ne'; have := h'.2.ne'; have := h.1.ne'
  field_simp

lemma costly_dl : ∀ t, ∃ c, Tendsto (fun lam => lam ^ 2 * ((F.withLam lam).qS v' t -
    (F.withLam lam).qS v t)) atTop (𝓝 c) := by
  suffices h : ∀ k t, F.T - t = k → ∃ c, Tendsto (fun lam => lam ^ 2 * ((F.withLam lam).qS v' t -
      (F.withLam lam).qS v t)) atTop (𝓝 c) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨0, ?_⟩
    simp only [qS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega),
      sub_self, mul_zero]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    obtain ⟨c, hc⟩ := ih (t + 1) (by omega)
    obtain ⟨hr, hev⟩ := costly_ratio F v t
    obtain ⟨hr', hev'⟩ := costly_ratio F v' t
    obtain ⟨e, he⟩ := costly_Dd F v v' t
    obtain ⟨l', hl'⟩ := costly_l F v' (t + 1)
    have hdi := costly_dinv F v' t
    refine ⟨_, ((hr'.mul hr).mul (he.add ((tendsto_const_nhds (x := F.rho)).mul
      ((hl'.mul he).add (hc.mul hdi))))).congr' ?_⟩
    filter_upwards [hev, hev'] with lam h h'
    rw [wl_l F v' lam t htT, wl_l F v lam t htT]
    have := h.2.ne'; have := h'.2.ne'; have := h.1.ne'
    field_simp
    ring

lemma costly_pk (t s : ℕ) : Tendsto (fun lam => (F.withLam lam).pk v' t s) atTop (𝓝 1) := by
  have := tendsto_finsetProd (Finset.Ico s t) fun j _ => (costly_ratio F v' j).1
  simp only [Finset.prod_const_one] at this
  exact this

end Costly1

lemma sum_scale (f g : ℕ → ℝ) (c : ℝ) (A : Finset ℕ) :
    ∑ s ∈ A, f s * (c * g s) = c * ∑ s ∈ A, f s * g s := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem costly : Costly := by
  intro F hS v' x0 a0 hv
  set v := F.sig2
  have hpk := costly_pk F v'
  choose cl hcl using costly_l F v'
  choose ck hck using costly_dk F v v'
  choose cd hcd using costly_dl F v v'
  have hinv : Tendsto (fun lam : ℝ => lam⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hS : ∀ t (A : Finset ℕ), Tendsto (fun lam => ∑ s ∈ A,
      (F.withLam lam).pk v' t (s + 1) * (lam * (F.withLam lam).qS v' s)) atTop
      (𝓝 (∑ s ∈ A, 1 * cl s)) := fun t A =>
    tendsto_finsetSum _ fun s _ => (hpk t (s + 1)).mul (hcl s)
  have hmu : ∀ t, ∃ c, Tendsto (fun lam => lam * (F.withLam lam).muA v' x0 a0 t) atTop (𝓝 c) :=
    fun t => ⟨_, ((((hck t).mul (hpk t 0)).mul (tendsto_const_nhds (x := x0))).add
      (((((hck t).mul (hS t (Finset.range t))).add (hcd t)).mul hinv).mul
        (tendsto_const_nhds (x := a0)))).congr' (by
        filter_upwards [eventually_gt_atTop 0] with lam hl
        simp only [Fund.muA, sum_scale, wl_sig2]
        field_simp
        ring)⟩
  have hw : ∀ t u, ∃ c, Tendsto (fun lam => lam ^ 2 * (F.withLam lam).wA v' t u) atTop (𝓝 c) :=
    fun t u => ⟨_, (((hck t).mul (hS t (Finset.Ico (u + 1) t))).add (hcd t)).congr (fun lam => by
      simp only [Fund.wA, sum_scale, wl_sig2]; ring)⟩
  choose m hm using hmu
  choose w hw using hw
  have hL := (tendsto_finsetSum (Finset.range F.T) fun t _ =>
    ((tendsto_const_nhds (x := F.rho ^ t)).mul (costly_dinv F v t)).mul (((hm t).pow 2).add
      ((hinv.pow 2).mul (tendsto_finsetSum (Finset.range t) fun u _ => ((hw t u).pow 2).mul
        (tendsto_const_nhds (x := F.p u - F.p (u + 1))))))).const_mul (1 / 2)
  have key : ∀ᶠ lam in atTop, (1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t *
      ((F.withLam lam).dS v t / lam) * ((lam * (F.withLam lam).muA v' x0 a0 t) ^ 2 + lam⁻¹ ^ 2 *
        ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1)))) *
      (1 / lam) = (F.withLam lam).LossA v' x0 a0 := by
    filter_upwards [eventually_gt_atTop 0] with lam hl
    rw [Fund.LossA, mul_assoc, Finset.sum_mul]
    simp only [wl_T, wl_rho, wl_sig2, wl_p]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1)) =
        lam ^ 4 * ∑ u ∈ Finset.range t, (F.withLam lam).wA v' t u ^ 2 * (F.p u - F.p (u + 1)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have : F.withLam lam = F.withLam lam := rfl
    field_simp
    ring
  exact ((hL.isBigO_one ℝ).mul (isBigO_refl (fun lam : ℝ => 1 / lam) atTop)).congr' key
    (Eventually.of_forall fun _ => one_mul _)

/-! #### The exact order -/

section Order

variable (F : Fund) (v v' : ℝ)

/-- The limits of `a_t` at two residual variances are ordered like the variances. -/
lemma costly_a2 (hg : 0 ≤ F.gam) (hr : 0 ≤ F.rho) : ∀ t, ∃ α α' : ℝ,
    Tendsto (fun lam => (F.withLam lam).aS v t) atTop (𝓝 α) ∧
    Tendsto (fun lam => (F.withLam lam).aS v' t) atTop (𝓝 α') ∧ 0 ≤ (α - α') * (v - v') := by
  suffices h : ∀ k t, F.T - t = k → ∃ α α' : ℝ,
      Tendsto (fun lam => (F.withLam lam).aS v t) atTop (𝓝 α) ∧
      Tendsto (fun lam => (F.withLam lam).aS v' t) atTop (𝓝 α') ∧ 0 ≤ (α - α') * (v - v') from
    fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    refine ⟨0, 0, ?_, ?_, by simp⟩ <;>
    · simp only [aS_ge (F.withLam _) (show (F.withLam _).T ≤ t from by simp [Fund.withLam]; omega)]
      exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    obtain ⟨α, α', hα, hα', hs⟩ := ih (t + 1) (by omega)
    have lim : ∀ (u : ℝ) (β : ℝ), Tendsto (fun lam => (F.withLam lam).aS u (t + 1)) atTop (𝓝 β) →
        Tendsto (fun lam => (F.withLam lam).aS u t) atTop (𝓝 ((F.gam * (u + F.p t) + F.rho * β) * 1)) := by
      intro u β hβ
      have hX : Tendsto (fun lam => F.gam * (u + F.p t) + F.rho * (F.withLam lam).aS u (t + 1)) atTop
          (𝓝 (F.gam * (u + F.p t) + F.rho * β)) :=
        (tendsto_const_nhds).add ((tendsto_const_nhds (x := F.rho)).mul hβ)
      obtain ⟨hrat, hev⟩ := ratio_lim hX
      refine (hX.mul hrat).congr' ?_
      filter_upwards [hev] with lam hl
      have h2 := hl.2.ne'
      rw [wl_a F u lam t htT, add_assoc]
      field_simp
      ring
    refine ⟨_, _, lim v α hα, lim v' α' hα', ?_⟩
    have e : ((F.gam * (v + F.p t) + F.rho * α) * 1 - (F.gam * (v' + F.p t) + F.rho * α') * 1) *
        (v - v') = F.gam * (v - v') ^ 2 + F.rho * ((α - α') * (v - v')) := by ring
    rw [e]
    positivity

lemma costly_dk2 (hg : 0 < F.gam) (hr : 0 ≤ F.rho) (t : ℕ) : ∃ c, Tendsto (fun lam => lam *
    ((F.withLam lam).kS v' t - (F.withLam lam).kS v t)) atTop (𝓝 c) ∧ (v ≠ v' → c ≠ 0) := by
  obtain ⟨hr1, hev⟩ := costly_ratio F v t
  obtain ⟨hr1', hev'⟩ := costly_ratio F v' t
  obtain ⟨α, α', hα, hα', hs⟩ := costly_a2 F v v' hg.le hr (t + 1)
  have hc : Tendsto (fun lam => (F.withLam lam).dS v t - (F.withLam lam).dS v' t) atTop
      (𝓝 (F.gam * (v - v') + F.rho * (α - α'))) :=
    ((tendsto_const_nhds (x := F.gam * (v - v'))).add
      ((tendsto_const_nhds (x := F.rho)).mul (hα.sub hα'))).congr fun lam => by rw [wl_d, wl_d]; ring
  refine ⟨_, ((hr1'.mul hr1).mul hc).congr' ?_, fun hne => ?_⟩
  · filter_upwards [hev, hev'] with lam h h'
    simp only [Fund.kS, wl_lam]
    have := h.2.ne'; have := h'.2.ne'; have := h.1.ne'
    field_simp
  · have hpos : 0 < (F.gam * (v - v') + F.rho * (α - α')) * (v - v') := by
      have h1 : 0 < F.gam * (v - v') ^ 2 := mul_pos hg (by positivity [sub_ne_zero.mpr hne])
      nlinarith [mul_nonneg hr hs]
    intro h0
    have h1 : F.gam * (v - v') + F.rho * (α - α') = 0 := by simpa using h0
    rw [h1, zero_mul] at hpos
    exact lt_irrefl _ hpos

end Order

theorem costlyOrder : CostlyOrder := by
  intro F hS v' x0 a0 hv
  obtain ⟨hl0, hg, hr0, hr1, hs0, hp⟩ := hS
  set v := F.sig2
  have hpk := costly_pk F v'
  choose cl hcl using costly_l F v'
  choose ck hck hck0 using costly_dk2 F v v' hg hr0
  choose cd hcd using costly_dl F v v'
  have hinv : Tendsto (fun lam : ℝ => lam⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hSum : ∀ t (A : Finset ℕ), Tendsto (fun lam => ∑ s ∈ A,
      (F.withLam lam).pk v' t (s + 1) * (lam * (F.withLam lam).qS v' s)) atTop
      (𝓝 (∑ s ∈ A, 1 * cl s)) := fun t A =>
    tendsto_finsetSum _ fun s _ => (hpk t (s + 1)).mul (hcl s)
  have hw : ∀ t u, ∃ c, Tendsto (fun lam => lam ^ 2 * (F.withLam lam).wA v' t u) atTop (𝓝 c) :=
    fun t u => ⟨_, (((hck t).mul (hSum t (Finset.Ico (u + 1) t))).add (hcd t)).congr (fun lam => by
      simp only [Fund.wA, sum_scale, wl_sig2]; ring)⟩
  choose w hw using hw
  have hwsum : ∀ t (f : ℕ → ℝ), Tendsto (fun lam => ∑ u ∈ Finset.range t,
      (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1))) atTop
      (𝓝 (∑ u ∈ Finset.range t, w t u ^ 2 * (F.p u - F.p (u + 1)))) := fun t _ =>
    tendsto_finsetSum _ fun u _ => ((hw t u).pow 2).mul tendsto_const_nhds
  refine ⟨fun hx hne hT => ?_, fun hx => ?_⟩
  · -- `λ μ_t → ck_t x_0`
    have hmu : ∀ t, Tendsto (fun lam => lam * (F.withLam lam).muA v' x0 a0 t) atTop (𝓝 (ck t * x0)) :=
      fun t => by
        have := ((((hck t).mul (hpk t 0)).mul (tendsto_const_nhds (x := x0))).add
          (((((hck t).mul (hSum t (Finset.range t))).add (hcd t)).mul hinv).mul
            (tendsto_const_nhds (x := a0)))).congr' (f₂ := fun lam => lam * (F.withLam lam).muA v' x0 a0 t)
          (by
            filter_upwards [eventually_gt_atTop 0] with lam hl
            simp only [Fund.muA, sum_scale, wl_sig2]
            field_simp
            ring)
        simpa using this
    have hL := (tendsto_finsetSum (Finset.range F.T) fun t _ =>
      ((tendsto_const_nhds (x := F.rho ^ t)).mul (costly_dinv F v t)).mul (((hmu t).pow 2).add
        ((hinv.pow 2).mul (hwsum t 0)))).const_mul (1 / 2)
    simp only [mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      add_zero] at hL
    set L := 1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * (ck t * x0) ^ 2
    have hLpos : 0 < L := by
      have h0 : 0 < (ck 0 * x0) ^ 2 := by positivity [hck0 0 (Ne.symm hne), hx]
      have := Finset.single_le_sum (f := fun t => F.rho ^ t * (ck t * x0) ^ 2)
        (fun t _ => by positivity) (Finset.mem_range.mpr (by omega : 0 < F.T))
      simp only [pow_zero, one_mul] at this
      simp only [L]; linarith
    have key : ∀ᶠ lam in atTop, lam * (F.withLam lam).LossA v' x0 a0 = 1 / 2 * ∑ t ∈ Finset.range F.T,
        F.rho ^ t * ((F.withLam lam).dS v t / lam) * ((lam * (F.withLam lam).muA v' x0 a0 t) ^ 2 +
          lam⁻¹ ^ 2 * ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 *
            (F.p u - F.p (u + 1))) := by
      filter_upwards [eventually_gt_atTop 0] with lam hl
      rw [Fund.LossA, ← mul_assoc, mul_comm lam, mul_assoc, Finset.mul_sum]
      simp only [wl_T, wl_rho, wl_sig2, wl_p]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      have e : ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1)) =
          lam ^ 4 * ∑ u ∈ Finset.range t, (F.withLam lam).wA v' t u ^ 2 * (F.p u - F.p (u + 1)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      field_simp
      ring
    have hlim := hL.congr' (key.mono fun _ h => h.symm)
    refine ⟨L / 2, by positivity, ?_⟩
    filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : L / 2 < L)), eventually_gt_atTop 0]
      with lam h hl
    rw [div_le_iff₀ hl]
    linarith
  · -- `x_0 = 0`: `λ² μ_t` converges
    subst hx
    have hmu : ∀ t, ∃ c, Tendsto (fun lam => lam ^ 2 * (F.withLam lam).muA v' 0 a0 t) atTop (𝓝 c) :=
      fun t => ⟨_, ((((hck t).mul (hSum t (Finset.range t))).add (hcd t)).mul
        (tendsto_const_nhds (x := a0))).congr (fun lam => by
          simp only [Fund.muA, sum_scale, wl_sig2]; ring)⟩
    choose m hm using hmu
    have hL := (tendsto_finsetSum (Finset.range F.T) fun t _ =>
      ((tendsto_const_nhds (x := F.rho ^ t)).mul (costly_dinv F v t)).mul (((hm t).pow 2).add
        (hwsum t 0))).const_mul (1 / 2)
    have key : ∀ᶠ lam in atTop, (1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t *
        ((F.withLam lam).dS v t / lam) * ((lam ^ 2 * (F.withLam lam).muA v' 0 a0 t) ^ 2 +
          ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1)))) *
        (1 / lam ^ 3) = (F.withLam lam).LossA v' 0 a0 := by
      filter_upwards [eventually_gt_atTop 0] with lam hl
      rw [Fund.LossA, mul_assoc, Finset.sum_mul]
      simp only [wl_T, wl_rho, wl_sig2, wl_p]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      have e : ∑ u ∈ Finset.range t, (lam ^ 2 * (F.withLam lam).wA v' t u) ^ 2 * (F.p u - F.p (u + 1)) =
          lam ^ 4 * ∑ u ∈ Finset.range t, (F.withLam lam).wA v' t u ^ 2 * (F.p u - F.p (u + 1)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      field_simp
      ring
    exact ((hL.isBigO_one ℝ).mul (isBigO_refl (fun lam : ℝ => 1 / lam ^ 3) atTop)).congr' key
      (Eventually.of_forall fun _ => one_mul _)

/-! ### Part 3(i): second-order expansion in the error -/

section Expand

/-- `f(ε) = c₀ + c₁ ε + O(ε²)` at `0`. -/
def E2 (f : ℝ → ℝ) (c0 c1 : ℝ) : Prop := (fun e => f e - c0 - c1 * e) =O[𝓝 0] fun e => e ^ 2

/-- `f(ε) = c₀ + O(ε)` at `0`. -/
def E1 (f : ℝ → ℝ) (c0 : ℝ) : Prop := (fun e => f e - c0) =O[𝓝 0] fun e => e

lemma sq_O : (fun e : ℝ => e ^ 2) =O[𝓝 0] fun e => e := (isLittleO_pow_id one_lt_two).isBigO

lemma id_O1 : (fun e : ℝ => e) =O[𝓝 (0 : ℝ)] fun _ => (1 : ℝ) :=
  (continuous_id.tendsto (0 : ℝ)).isBigO_one ℝ

lemma e1_of_e2 {f : ℝ → ℝ} {c0 c1 : ℝ} (h : E2 f c0 c1) : E1 f c0 :=
  (h.trans sq_O).add ((isBigO_refl (fun e : ℝ => e) _).const_mul_left c1) |>.congr_left
    fun e => by ring

lemma e1_bdd {f : ℝ → ℝ} {c0 : ℝ} (h : E1 f c0) : f =O[𝓝 0] fun _ => (1 : ℝ) :=
  ((h.trans id_O1).add (isBigO_const_const c0 one_ne_zero _)).congr_left fun e => by ring

lemma e1_tendsto {f : ℝ → ℝ} {c0 : ℝ} (h : E1 f c0) : Tendsto f (𝓝 0) (𝓝 c0) := by
  have := h.trans_tendsto (continuous_id.tendsto (0 : ℝ))
  simpa using this.add_const c0

lemma e1_const (c : ℝ) : E1 (fun _ => c) c := by
  simp only [E1, sub_self]; exact isBigO_zero _ _

lemma e1_add {f g : ℝ → ℝ} {a b : ℝ} (hf : E1 f a) (hg : E1 g b) : E1 (fun e => f e + g e) (a + b) :=
  (hf.add hg).congr_left fun e => by ring

lemma e1_mul {f g : ℝ → ℝ} {a b : ℝ} (hf : E1 f a) (hg : E1 g b) : E1 (fun e => f e * g e) (a * b) := by
  unfold E1
  have h1 : (fun e => (f e - a) * g e) =O[𝓝 0] fun e => e * 1 := hf.mul (e1_bdd hg)
  have h2 : (fun e => a * (g e - b)) =O[𝓝 0] fun e => e := hg.const_mul_left a
  exact ((h1.congr_right fun e => mul_one e).add h2).congr_left fun e => by ring

lemma e1_sum {ι : Type} (A : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ} (h : ∀ i ∈ A, E1 (f i) (a i)) :
    E1 (fun e => ∑ i ∈ A, f i e) (∑ i ∈ A, a i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using e1_const 0
  | insert j A hj ih =>
    simp only [Finset.sum_insert hj]
    exact e1_add (h j (Finset.mem_insert_self j A)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma e1_prod {ι : Type} (A : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ} (h : ∀ i ∈ A, E1 (f i) (a i)) :
    E1 (fun e => ∏ i ∈ A, f i e) (∏ i ∈ A, a i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using e1_const 1
  | insert j A hj ih =>
    simp only [Finset.prod_insert hj]
    exact e1_mul (h j (Finset.mem_insert_self j A)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma e2_congr {f : ℝ → ℝ} {c0 c1 d0 d1 : ℝ} (h : E2 f c0 c1) (h0 : c0 = d0) (h1 : c1 = d1) :
    E2 f d0 d1 := by subst h0 h1; exact h

lemma e2_const (c : ℝ) : E2 (fun _ => c) c 0 := by
  simp only [E2, sub_self, zero_mul]; exact isBigO_zero _ _

lemma e2_affine (a b : ℝ) : E2 (fun e => a + b * e) a b := by
  simp only [E2]
  exact (isBigO_zero _ _).congr_left fun e => by ring

lemma e2_add {f g : ℝ → ℝ} {a0 a1 b0 b1 : ℝ} (hf : E2 f a0 a1) (hg : E2 g b0 b1) :
    E2 (fun e => f e + g e) (a0 + b0) (a1 + b1) :=
  (hf.add hg).congr_left fun e => by ring

lemma e2_sub {f g : ℝ → ℝ} {a0 a1 b0 b1 : ℝ} (hf : E2 f a0 a1) (hg : E2 g b0 b1) :
    E2 (fun e => f e - g e) (a0 - b0) (a1 - b1) :=
  (hf.sub hg).congr_left fun e => by ring

lemma e2_mul {f g : ℝ → ℝ} {a0 a1 b0 b1 : ℝ} (hf : E2 f a0 a1) (hg : E2 g b0 b1) :
    E2 (fun e => f e * g e) (a0 * b0) (a0 * b1 + a1 * b0) := by
  have hg1 := e1_of_e2 hg
  have t1 : (fun e => (f e - a0 - a1 * e) * g e) =O[𝓝 0] fun e => e ^ 2 :=
    (hf.mul (e1_bdd hg1)).congr_right fun e => mul_one _
  have t2 : (fun e => a0 * (g e - b0 - b1 * e)) =O[𝓝 0] fun e => e ^ 2 := hg.const_mul_left a0
  have t3 : (fun e => (a1 * e) * (g e - b0)) =O[𝓝 0] fun e => e ^ 2 :=
    (((isBigO_refl (fun e : ℝ => e) _).const_mul_left a1).mul hg1).congr_right fun e => by ring
  unfold E2
  exact ((t1.add t2).add t3).congr_left fun e => by ring

lemma e2_inv {g : ℝ → ℝ} {b0 b1 : ℝ} (hg : E2 g b0 b1) (hb : b0 ≠ 0) :
    E2 (fun e => 1 / g e) (1 / b0) (-b1 / b0 ^ 2) := by
  have hg1 := e1_of_e2 hg
  have hT := e1_tendsto hg1
  have hinv : (fun e => 1 / g e) =O[𝓝 0] fun _ => (1 : ℝ) :=
    (hT.div (tendsto_const_nhds (x := (1 : ℝ))) one_ne_zero |>.inv₀ (by simpa using hb)
      |>.congr fun e => by simp) |>.isBigO_one ℝ
  have hne : ∀ᶠ e in 𝓝 0, g e ≠ 0 := hT.eventually_ne hb
  have s1 : (fun e => -b0 * (g e - b0 - b1 * e) + b1 * e * (g e - b0)) =O[𝓝 0] fun e => e ^ 2 :=
    (hg.const_mul_left (-b0)).add ((((isBigO_refl (fun e : ℝ => e) _).const_mul_left b1).mul
      hg1).congr_right fun e => by ring)
  have s2 := (s1.mul hinv).const_mul_left (1 / b0 ^ 2)
  unfold E2
  refine s2.congr' ?_ (Eventually.of_forall fun e => mul_one _)
  filter_upwards [hne] with e he
  field_simp
  ring

lemma e2_div {f g : ℝ → ℝ} {a0 a1 b0 b1 : ℝ} (hf : E2 f a0 a1) (hg : E2 g b0 b1) (hb : b0 ≠ 0) :
    E2 (fun e => f e / g e) (a0 / b0) ((a1 * b0 - a0 * b1) / b0 ^ 2) := by
  have := e2_mul hf (e2_inv hg hb)
  have h2 : E2 (fun e => f e / g e) (a0 * (1 / b0)) (a0 * (-b1 / b0 ^ 2) + a1 * (1 / b0)) := by
    unfold E2 at this ⊢; exact this.congr_left fun e => by simp only [mul_one_div]
  exact e2_congr h2 (by ring) (by field_simp; ring)

lemma e2_sq0 {f : ℝ → ℝ} {c1 : ℝ} (h : E2 f 0 c1) :
    (fun e => f e ^ 2 - c1 ^ 2 * e ^ 2) =O[𝓝 0] fun e => e ^ 3 := by
  have h1 : (fun e => f e + c1 * e) =O[𝓝 0] fun e => e :=
    ((e1_of_e2 h).congr_left fun e => by ring).add ((isBigO_refl (fun e : ℝ => e) _).const_mul_left c1)
  exact (h.mul h1).congr (fun e => by ring) (fun e => by ring)

lemma e2_deriv {f : ℝ → ℝ} {c1 : ℝ} (h : E2 f (f 0) c1) : HasDerivAt f c1 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine (h.trans_isLittleO (isLittleO_pow_id one_lt_two)).congr (fun e => by simp; ring)
    (fun e => by simp)

end Expand

lemma e2_ext {f g : ℝ → ℝ} {c0 c1 : ℝ} (h : E2 f c0 c1) (hfg : ∀ e, f e = g e) : E2 g c0 c1 := by
  unfold E2 at h ⊢; exact h.congr_left fun e => by rw [hfg]

lemma e2_mul0 {f g : ℝ → ℝ} {a1 b0 : ℝ} (hf : E2 f 0 a1) (hg : E1 g b0) :
    E2 (fun e => f e * g e) 0 (a1 * b0) := by
  have t1 : (fun e => (f e - 0 - a1 * e) * g e) =O[𝓝 0] fun e => e ^ 2 :=
    (hf.mul (e1_bdd hg)).congr_right fun e => mul_one _
  have t2 : (fun e => (a1 * e) * (g e - b0)) =O[𝓝 0] fun e => e ^ 2 :=
    (((isBigO_refl (fun e : ℝ => e) _).const_mul_left a1).mul hg).congr_right fun e => by ring
  unfold E2
  exact (t1.add t2).congr_left fun e => by ring

section Quad

variable (F : Fund)

lemma a_nonneg (hS : F.Setting) {v : ℝ} (hv : ∀ t, 0 ≤ v + F.p t) : ∀ t, 0 ≤ F.aS v t := by
  obtain ⟨hl, hg, hr0, -, -, -⟩ := hS
  suffices h : ∀ k t, F.T - t = k → 0 ≤ F.aS v t from fun t => h _ t rfl
  intro k
  induction k with
  | zero => intro t ht; rw [aS_ge F (by omega)]
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    have h1 := ih (t + 1) (by omega)
    rw [aS_lt F htT]
    have hd : F.lam ≤ F.dS v t := by
      rw [Fund.dS]; nlinarith [mul_nonneg hg.le (hv t), mul_nonneg hr0 h1]
    have hdp : 0 < F.dS v t := lt_of_lt_of_le hl hd
    rw [sub_nonneg, div_le_iff₀ hdp]
    nlinarith

lemma d_pos (hS : F.Setting) {v : ℝ} (hv : ∀ t, 0 ≤ v + F.p t) (t : ℕ) : 0 < F.dS v t := by
  have h1 := a_nonneg F hS hv (t + 1)
  obtain ⟨hl, hg, hr0, -, -, -⟩ := hS
  rw [Fund.dS]; nlinarith [mul_nonneg hg.le (hv t), mul_nonneg hr0 h1]

variable {F} (hS : F.Setting)
include hS

lemma hv0 : ∀ t, 0 ≤ F.sig2 + F.p t := fun t => by
  obtain ⟨-, -, -, -, hs, hp⟩ := hS; linarith [hp t]

lemma exp_rec : ∀ t, E2 (fun e => F.aS (F.sig2 + e) t) (F.aS F.sig2 t) (F.aP t) ∧
    E2 (fun e => F.qS (F.sig2 + e) t) (F.qS F.sig2 t) (F.qP t) := by
  suffices h : ∀ k t, F.T - t = k → E2 (fun e => F.aS (F.sig2 + e) t) (F.aS F.sig2 t) (F.aP t) ∧
      E2 (fun e => F.qS (F.sig2 + e) t) (F.qS F.sig2 t) (F.qP t) from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    have hT : F.T ≤ t := by omega
    rw [aS_ge F hT, aP_ge F hT, qS_ge F hT, qP_ge F hT]
    exact ⟨e2_ext (e2_const 0) fun e => (aS_ge F hT).symm, e2_ext (e2_const 0) fun e => (qS_ge F hT).symm⟩
  | succ k ih =>
    intro t ht
    have htT : t < F.T := by omega
    obtain ⟨ha', hl'⟩ := ih (t + 1) (by omega)
    have hd0 := d_pos F hS (hv0 hS) t
    have hd : E2 (fun e => F.dS (F.sig2 + e) t) (F.dS F.sig2 t) (F.dP t) :=
      e2_ext (e2_congr (e2_add (e2_affine (F.lam + F.gam * (F.sig2 + F.p t)) F.gam)
        (e2_mul (e2_const F.rho) ha')) (by rw [Fund.dS]) (by rw [Fund.dP]; ring))
        fun e => by rw [Fund.dS]; ring
    refine ⟨?_, ?_⟩
    · refine e2_ext (e2_congr (e2_sub (e2_const F.lam) (e2_div (e2_const (F.lam ^ 2)) hd hd0.ne'))
        (aS_lt F htT).symm ?_) fun e => (aS_lt F htT).symm
      rw [aP_lt F htT]; ring
    · refine e2_ext (e2_congr (e2_div (e2_add (e2_const 1) (e2_mul (e2_const (F.rho * F.lam)) hl'))
        hd hd0.ne') (by rw [qS_lt F htT, mul_assoc]) ?_) fun e => by rw [qS_lt F htT, mul_assoc]
      rw [qP_lt F htT]; ring

lemma exp_k (t : ℕ) : E2 (fun e => F.kS (F.sig2 + e) t) (F.kS F.sig2 t) (F.kP t) := by
  have hd0 := d_pos F hS (hv0 hS) t
  have ha' := (exp_rec hS (t + 1)).1
  have hd : E2 (fun e => F.dS (F.sig2 + e) t) (F.dS F.sig2 t) (F.dP t) :=
    e2_ext (e2_congr (e2_add (e2_affine (F.lam + F.gam * (F.sig2 + F.p t)) F.gam)
      (e2_mul (e2_const F.rho) ha')) (by rw [Fund.dS]) (by rw [Fund.dP]; ring))
      fun e => by rw [Fund.dS]; ring
  exact e2_congr (e2_div (e2_const F.lam) hd hd0.ne') rfl (by rw [Fund.kP]; ring)

lemma deriv_of_e2 {f : ℝ → ℝ} {c1 : ℝ} (h : E2 (fun e => f (F.sig2 + e)) (f F.sig2) c1) :
    HasDerivAt f c1 F.sig2 := by
  have h0 : E2 (fun e => f (F.sig2 + e)) ((fun e => f (F.sig2 + e)) 0) c1 := by
    simpa only [add_zero] using h
  have h1 : HasDerivAt (fun e => f (F.sig2 + e)) c1 (F.sig2 - F.sig2) := by
    rw [sub_self]; exact e2_deriv h0
  have h2 : HasDerivAt (fun v : ℝ => v - F.sig2) 1 F.sig2 := (hasDerivAt_id' F.sig2).sub_const F.sig2
  simpa [Function.comp_def] using HasDerivAt.comp (h := fun v : ℝ => v - F.sig2) F.sig2 h1 h2

end Quad

/-- The derivative forms of `μ_t` and `w_{t,u}` in 3(i)'s constant. -/
def muD (F : Fund) (x0 a0 : ℝ) (t : ℕ) : ℝ :=
  F.kP t * F.pk F.sig2 t 0 * x0 +
    (F.kP t * ∑ s ∈ Finset.range t, F.pk F.sig2 t (s + 1) * F.qS F.sig2 s + F.qP t) * a0

def wD (F : Fund) (t u : ℕ) : ℝ :=
  F.kP t * ∑ s ∈ Finset.Ico (u + 1) t, F.pk F.sig2 t (s + 1) * F.qS F.sig2 s + F.qP t

theorem quadratic : Quadratic := by
  intro F hS x0 a0
  have hk := exp_k hS
  have hl := fun t => (exp_rec hS t).2
  refine ⟨fun t _ => ⟨deriv_of_e2 hS (hk t), deriv_of_e2 hS (hl t)⟩, ?_⟩
  have hdk : ∀ t, E2 (fun e => F.kS (F.sig2 + e) t - F.kS F.sig2 t) 0 (F.kP t) := fun t =>
    e2_congr (e2_sub (hk t) (e2_const _)) (sub_self _) (sub_zero _)
  have hdl : ∀ t, E2 (fun e => F.qS (F.sig2 + e) t - F.qS F.sig2 t) 0 (F.qP t) := fun t =>
    e2_congr (e2_sub (hl t) (e2_const _)) (sub_self _) (sub_zero _)
  have hpk : ∀ t s, E1 (fun e => F.pk (F.sig2 + e) t s) (F.pk F.sig2 t s) := fun t s =>
    e1_prod _ fun j _ => e1_of_e2 (hk j)
  have hsum : ∀ t (A : Finset ℕ), E1 (fun e => ∑ s ∈ A, F.pk (F.sig2 + e) t (s + 1) * F.qS (F.sig2 + e) s)
      (∑ s ∈ A, F.pk F.sig2 t (s + 1) * F.qS F.sig2 s) := fun t A =>
    e1_sum _ fun s _ => e1_mul (hpk t (s + 1)) (e1_of_e2 (hl s))
  have hmu : ∀ t, E2 (fun e => F.muA (F.sig2 + e) x0 a0 t) 0 (muD F x0 a0 t) := fun t =>
    e2_ext (e2_congr (e2_add (e2_mul0 (e2_mul0 (hdk t) (hpk t 0)) (e1_const x0))
      (e2_mul0 (e2_congr (e2_add (e2_mul0 (hdk t) (hsum t (Finset.range t))) (hdl t)) (add_zero 0) rfl)
        (e1_const a0))) (add_zero 0) (by simp only [muD]))
      fun e => by simp only [Fund.muA]
  have hw : ∀ t u, E2 (fun e => F.wA (F.sig2 + e) t u) 0 (wD F t u) := fun t u =>
    e2_ext (e2_congr (e2_add (e2_mul0 (hdk t) (hsum t (Finset.Ico (u + 1) t))) (hdl t)) (add_zero 0)
      (by simp only [wD])) fun e => by simp only [Fund.wA]
  have hin : ∀ t, (fun e => ∑ u ∈ Finset.range t, (F.p u - F.p (u + 1)) *
      (F.wA (F.sig2 + e) t u ^ 2 - wD F t u ^ 2 * e ^ 2)) =O[𝓝 0] fun e => e ^ 3 := fun t =>
    (IsBigO.sum (s := Finset.range t) fun u _ =>
      (e2_sq0 (hw t u)).const_mul_left (F.p u - F.p (u + 1))).congr_left fun e => by
        simp only [Finset.sum_apply]
  have main : (fun e => ∑ t ∈ Finset.range F.T, F.rho ^ t * F.dS F.sig2 t *
      ((F.muA (F.sig2 + e) x0 a0 t ^ 2 - muD F x0 a0 t ^ 2 * e ^ 2) +
        ∑ u ∈ Finset.range t, (F.p u - F.p (u + 1)) *
          (F.wA (F.sig2 + e) t u ^ 2 - wD F t u ^ 2 * e ^ 2))) =O[𝓝 0] fun e => e ^ 3 :=
    (IsBigO.sum (s := Finset.range F.T) fun t _ => ((e2_sq0 (hmu t)).add
      (hin t)).const_mul_left (F.rho ^ t * F.dS F.sig2 t)).congr_left
      fun e => by simp only [Finset.sum_apply]
  refine (main.const_mul_left (1 / 2)).congr_left fun e => ?_
  have hC : F.C x0 a0 = 1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * F.dS F.sig2 t *
      (muD F x0 a0 t ^ 2 + ∑ u ∈ Finset.range t, wD F t u ^ 2 * (F.p u - F.p (u + 1))) := rfl
  rw [hC, Fund.LossA, mul_assoc (1 / 2 : ℝ), Finset.sum_mul, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hin : ∑ u ∈ Finset.range t, (F.p u - F.p (u + 1)) *
      (F.wA (F.sig2 + e) t u ^ 2 - wD F t u ^ 2 * e ^ 2) =
      ∑ u ∈ Finset.range t, F.wA (F.sig2 + e) t u ^ 2 * (F.p u - F.p (u + 1)) -
        (∑ u ∈ Finset.range t, wD F t u ^ 2 * (F.p u - F.p (u + 1))) * e ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hin]
  ring

/-! ### Part 4 -/

theorem blockSep : BlockSep := by
  intro K N Q Q' LA Sy Sy' SA SA' hQ hQ' hT hr hL hL' hS hS' hG hG' he he' t ht y xA lh ah
  have h := (separation K N Q LA Sy SA hQ hL hS hG he t ht).1 y xA lh ah
  have h' := (separation K N Q' LA Sy' SA' hQ' hL' hS' hG' he' t (hT ▸ ht)).1 y xA lh ah
  refine ⟨fun hA i => ?_, fun hy k => ?_⟩
  · rw [h, h']
    simp only [Sum.elim_inr]
    rw [hA, hT, hr]
  · rw [h, h']
    simp only [Sum.elim_inl]
    rw [hy]

section Span

open Standalone.M5MissingDirectionLeak Novel.M5MissingDirectionLeakProof

variable {K N M : ℕ}

lemma leak_setting {P : Leak K N M} (hS : P.Setting) {St' : ℕ → Matrix (Fin K) (Fin K) ℝ}
    (h' : ∀ t, (St' t).PosDef) : ({ P with St := St' } : Leak K N M).Setting :=
  ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, h', hS.2.2.2.2.2.1, hS.2.2.2.2.2.2⟩

theorem spanning : Spanning := by
  intro K N M P St' hS h' hU
  have hS' : ({ P with St := St' } : Leak K N M).Setting := leak_setting hS h'
  obtain ⟨-, hL⟩ := theLeak
  obtain ⟨-, hsp, -⟩ := hL K N M P hS
  obtain ⟨hJ, hR, -⟩ := hsp hU
  obtain ⟨-, hsp', -⟩ := hL K N M _ hS'
  obtain ⟨-, hR', -⟩ := hsp' hU
  have hSig : (fun t => P.gam • SigRed P.BA P.BE (St' t) (P.SAt t)) =
      fun t => P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t) :=
    funext fun t => congrArg _ ((hR' t).trans (hR t).symm)
  have hG : (fun t => Gred P.BA P.BE (St' t)) = fun t => Gred P.BA P.BE (P.St t) := funext fun t => by
    simp only [Gred]
    rw [hJ (St' t) (h' t), hJ (P.St t) (hS.2.2.2.2.1 t)]
  have hred : ({ P with St := St' } : Leak K N M).red = P.red := by
    show (⟨P.T, P.LA, fun t => P.gam • SigRed P.BA P.BE (St' t) (P.SAt t), P.rho,
      fun t => Gred P.BA P.BE (St' t), 0⟩ : LQ (Fin N) (Fin K ⊕ Fin N)) =
      ⟨P.T, P.LA, fun t => P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t), P.rho,
        fun t => Gred P.BA P.BE (P.St t), 0⟩
    rw [hSig, hG]
  refine ⟨hred, fun t ht xm m i => ?_⟩
  have e := ((fundProblem K N M P hS).2 t ht).1 xm m
  have e' := ((fundProblem K N M _ hS').2 t ht).1 xm m
  rw [hred] at e'
  exact (congrFun e' i).trans (congrFun e i).symm

lemma schur_two {BE : Matrix (Fin M) (Fin K) ℝ} (hBE : IsUnit (BE * BEᵀ).det)
    {Sg : Matrix (Fin K) (Fin K) ℝ} (hSg : Sg.PosDef) : Schur BE ((2 : ℝ) • Sg) = (2 : ℝ) • Schur BE Sg := by
  have hrr : RRinv BE ((2 : ℝ) • Sg) = (2 : ℝ)⁻¹ • RRinv BE Sg := by
    simp only [RRinv, Matrix.mul_smul, Matrix.smul_mul]
    rw [inv_gsmul two_ne_zero (bsb_unit hBE hSg)]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp only [Schur, hrr, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_sub]
  norm_num

theorem noSpanning : NoSpanning := by
  intro K N M P hS hU hT
  set P' : Leak K N M := { P with St := fun t => (2 : ℝ) • P.St t }
  have h2 : ∀ t, (P'.St t).PosDef := fun t => (hS.2.2.2.2.1 t).smul (two_pos : (0 : ℝ) < 2)
  have hS' : P'.Setting := leak_setting hS h2
  obtain ⟨-, hL⟩ := theLeak
  have hnz := ((hL K N M P hS).2.2.2.2.2.2.1 (P.T - 1)).2.2 hU
  have hA : ∀ Q : Leak K N M, 1 ≤ Q.T → Q.red.A (Q.T - 1 + 1) = 0 := fun Q hQ =>
    LQ.A_ge _ (by simp only [Leak.red]; omega)
  have hDf : ∀ Q : Leak K N M, 1 ≤ Q.T → Q.red.D (Q.T - 1) =
      Q.LA + Q.gam • SigRed Q.BA Q.BE (Q.St (Q.T - 1)) (Q.SAt (Q.T - 1)) := fun Q h1 => by
    rw [LQ.D, hA Q h1, smul_zero, add_zero]; rfl
  have hD : ∀ Q : Leak K N M, 1 ≤ Q.T → Q.Setting → (Q.red.D (Q.T - 1)).PosDef := fun Q h1 hQ => by
    rw [hDf Q h1]
    exact hQ.2.2.2.1.add ((sigred_pd hQ (Q.T - 1)).smul hQ.1)
  intro hK
  have hDe : P'.red.D (P.T - 1) = P.red.D (P.T - 1) := by
    have hLu := (isUnit_iff_isUnit_det _).mp (hS.2.2.2.1).isUnit
    have h1 : (P'.red.D (P.T - 1))⁻¹ = (P.red.D (P.T - 1))⁻¹ := by
      have := congrArg (· * P.LA⁻¹) hK
      simp only [LQ.K, Matrix.mul_assoc] at this
      rwa [show P'.red.Lam = P.LA from rfl, show P.red.Lam = P.LA from rfl,
        mul_nonsing_inv _ hLu, Matrix.mul_one, Matrix.mul_one] at this
    have hD' : (P'.red.D (P.T - 1)).PosDef := hD P' hT hS'
    have := congrArg (·⁻¹) h1
    rwa [nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hD'.isUnit),
      nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hD P hT hS).isUnit)] at this
  rw [hDf P' hT, hDf P hT] at hDe
  have e1 := smul_right_injective _ hS.1.ne' (add_left_cancel hDe)
  simp only [SigRed, P', schur_two hS.2.2.2.2.2.2 (hS.2.2.2.2.1 _)] at e1
  have e2 := add_left_cancel e1
  rw [Matrix.mul_smul, Matrix.smul_mul, two_smul] at e2
  exact hnz (by simpa using e2)

end Span

/-! ### The claim -/

theorem proof : Standalone.M5PlugInLossInputs.statement :=
  ⟨pathwise, exposure, recursion, fundPath, quadratic, costless, costly, costlyOrder, oneReview,
    precision, blockSep, spanning, noSpanning⟩

end

end Novel.M5PlugInLossInputsProof

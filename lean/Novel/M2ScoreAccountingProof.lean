import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Standalone.M2ScoreAccounting

/-!
# Proof of claim 003: M2 score accounting and dependence on the belief mean

Finite real algebra throughout. Positive homogeneity of the trade parts gives the cost
normalization; the funding equations divided by `W⁻` give the normalized self-financing
identity (proved directly here, in M2's index type, rather than by importing claim 001's
lemma over `Fin (m + n)`); the conditional moments follow from `r_s = μ + ξ_s` and the zero
q-mean of `ξ_s`; the belief average uses that the score is affine in `θ`.
-/

namespace Novel.M2ScoreAccountingProof

open Matrix Finset Standalone.M2ScoreAccounting

variable {m n K : ℕ} {S : Type} [Fintype S]

/-! ### Cost normalization and funding -/

lemma max_mul_pos {W : ℝ} (hW : 0 < W) (y : ℝ) : max (W * y) 0 = W * max y 0 := by
  rw [mul_max_of_nonneg _ _ hW.le, mul_zero]

omit [Fintype S] in
lemma cost_smul (D : Data m n K S) (hW : 0 < W0 D) (v : Inst m n → ℝ) :
    cost D (W0 D • v) = W0 D * tau D v := by
  simp only [cost, tau, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show -(W0 D * v i) = W0 D * (-v i) by ring, max_mul_pos hW, max_mul_pos hW]
  ring

omit [Fintype S] in
lemma costNormalization (D : Data m n K S) (hW : 0 < W0 D) (v : Inst m n → ℝ) :
    cost D (W0 D • v) / W0 D = tau D v := by
  rw [cost_smul D hW, mul_div_cancel_left₀ _ hW.ne']

omit [Fintype S] in
lemma sum_w0_add_k0 (D : Data m n K S) (hW : 0 < W0 D) : ∑ i, w0 D i + k0 D = 1 := by
  have hW0 : D.h0 + ∑ i, D.x0 i = W0 D := rfl
  simp only [w0, k0]
  rw [← Finset.sum_div, ← add_div, add_comm, hW0, div_self hW.ne']

omit [Fintype S] in
lemma sum_add_cash (D : Data m n K S) (hW : 0 < W0 D) (w : Inst m n → ℝ) :
    ∑ i, w i + cash D w + tau D (w - w0 D) = 1 := by
  have h := sum_w0_add_k0 D hW
  simp only [cash, sum_sub_distrib]
  linarith

omit [Fintype S] in
lemma fundingTransfer (D : Data m n K S) (hW : 0 < W0 D) (w : Inst m n → ℝ) :
    postHoldings D (W0 D • (w - w0 D)) = W0 D • w ∧
    postCash D (W0 D • (w - w0 D)) = W0 D * cash D w ∧
    ∑ i, w i + cash D w + tau D (w - w0 D) = 1 := by
  refine ⟨?_, ?_, sum_add_cash D hW w⟩
  · funext i
    simp only [postHoldings, w0, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · have hk : D.h0 = W0 D * k0 D := by
      rw [k0, mul_div_cancel₀ _ hW.ne']
    have hs : ∑ i, (W0 D • (w - w0 D)) i = W0 D * ∑ i, (w i - w0 D i) := by
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sum]
    rw [postCash, cost_smul D hW, hs, hk, cash]
    ring

/-! ### Gain and conditional moments -/

omit [Fintype S] in
lemma gainIdentity (D : Data m n K S) (hW : 0 < W0 D) (w : Inst m n → ℝ) (θ : Params m K)
    (s : S) : gain D w θ s = w ⬝ᵥ ret D θ s - tau D (w - w0 D) := by
  have h := sum_add_cash D hW w
  have hsum : ∑ i, w i * (1 + ret D θ s i) = ∑ i, w i + w ⬝ᵥ ret D θ s := by
    simp only [dotProduct, mul_add, mul_one, sum_add_distrib]
  rw [gain, W1, mul_div_cancel_left₀ _ hW.ne', hsum]
  linarith

omit [Fintype S] in
lemma ret_eq (D : Data m n K S) (θ : Params m K) (s : S) : ret D θ s = mu D θ + xi D s := by
  funext i
  cases i with
  | inl j => simp only [ret, mu, xi, mulVec_add, Sum.elim_inl, Pi.add_apply]; ring
  | inr j => simp only [ret, mu, xi, mulVec_add, Sum.elim_inr, Pi.add_apply, Pi.sub_apply]; ring

/-- `(M *ᵥ Σ_s q_s z_s)` coordinatewise, for the centered-shock hypotheses. -/
lemma sum_q_mulVec {ι : Type} [Fintype ι] (D : Data m n K S) (M : Matrix ι (Fin K) ℝ)
    (hz : ∑ s, D.q s • D.zf s = 0) (j : ι) : ∑ s, D.q s * (M *ᵥ D.zf s) j = 0 := by
  have h : M *ᵥ (∑ s, D.q s • D.zf s) = 0 := by rw [hz, mulVec_zero]
  rw [mulVec_sum] at h
  have := congrFun h j
  simpa [Finset.sum_apply, mulVec_smul] using this

lemma sum_q_apply {ι : Type} (D : Data m n K S) (z : S → ι → ℝ) (hz : ∑ s, D.q s • z s = 0)
    (j : ι) : ∑ s, D.q s * z s j = 0 := by
  have := congrFun hz j
  simpa [Finset.sum_apply] using this

lemma sum_q_xi (D : Data m n K S) (hc : CenteredShocks D) (i : Inst m n) :
    ∑ s, D.q s * xi D s i = 0 := by
  obtain ⟨hf, hA, hE⟩ := hc
  cases i with
  | inl j =>
    simp only [xi, Sum.elim_inl, Pi.add_apply, mul_add, sum_add_distrib]
    rw [sum_q_mulVec D D.BA hf j, sum_q_apply D D.zA hA j, add_zero]
  | inr j =>
    simp only [xi, Sum.elim_inr, Pi.add_apply, mul_add, sum_add_distrib]
    rw [sum_q_mulVec D D.BE hf j, sum_q_apply D D.zE hE j, add_zero]

lemma sum_q_dot_xi (D : Data m n K S) (hc : CenteredShocks D) (w : Inst m n → ℝ) :
    ∑ s, D.q s * (w ⬝ᵥ xi D s) = 0 := by
  simp only [dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  have : ∑ s, D.q s * (w i * xi D s i) = w i * ∑ s, D.q s * xi D s i := by
    rw [mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [this, sum_q_xi D hc i, mul_zero]

omit [Fintype S] in
lemma gain_eq (D : Data m n K S) (hW : 0 < W0 D) (w : Inst m n → ℝ) (θ : Params m K)
    (s : S) : gain D w θ s = (w ⬝ᵥ mu D θ - tau D (w - w0 D)) + w ⬝ᵥ xi D s := by
  rw [gainIdentity D hW, ret_eq, dotProduct_add]
  ring

lemma condMean_gain (D : Data m n K S) (hW : 0 < W0 D) (hq : MassesSumToOne D)
    (hc : CenteredShocks D) (w : Inst m n → ℝ) (θ : Params m K) :
    condMean D (gain D w θ) = w ⬝ᵥ mu D θ - tau D (w - w0 D) := by
  simp only [condMean, gain_eq D hW, mul_add, sum_add_distrib, sum_q_dot_xi D hc, add_zero,
    ← sum_mul]
  rw [hq, one_mul]

lemma quad_eq (D : Data m n K S) (w : Inst m n → ℝ) :
    ∑ s, D.q s * (w ⬝ᵥ xi D s) ^ 2 = w ⬝ᵥ (covariance D *ᵥ w) := by
  calc ∑ s, D.q s * (w ⬝ᵥ xi D s) ^ 2
      = ∑ s, ∑ i, ∑ j, D.q s * (w i * xi D s i * (w j * xi D s j)) := by
        simp only [dotProduct, sq]
        simp only [Finset.sum_mul_sum]
        simp only [mul_sum]
    _ = ∑ i, ∑ j, ∑ s, D.q s * (w i * xi D s i * (w j * xi D s j)) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ = w ⬝ᵥ (covariance D *ᵥ w) := by
        simp only [dotProduct, mulVec, covariance, mul_sum, sum_mul]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring

lemma condVar_gain (D : Data m n K S) (hW : 0 < W0 D) (hq : MassesSumToOne D)
    (hc : CenteredShocks D) (w : Inst m n → ℝ) (θ : Params m K) :
    condVar D (gain D w θ) = w ⬝ᵥ (covariance D *ᵥ w) := by
  rw [condVar, condMean_gain D hW hq hc, ← quad_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [gain_eq D hW]
  ring

omit [Fintype S] in
lemma meanReturnFormula (D : Data m n K S) (w : Inst m n → ℝ) (θ : Params m K) :
    w ⬝ᵥ mu D θ = exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE := by
  have hsplit : w ⬝ᵥ mu D θ
      = active w ⬝ᵥ (D.BA *ᵥ θ.lam + θ.alpha) + etf w ⬝ᵥ (D.BE *ᵥ θ.lam - D.cE) := by
    simp only [dotProduct, Fintype.sum_sum_type, mu, active, etf, Sum.elim_inl, Sum.elim_inr]
  rw [hsplit, exposure, add_dotProduct, mulVec_transpose, mulVec_transpose,
    ← dotProduct_mulVec, ← dotProduct_mulVec, dotProduct_add, dotProduct_sub]
  ring

lemma momentIdentities (D : Data m n K S) (hW : 0 < W0 D) (hq : MassesSumToOne D)
    (hc : CenteredShocks D) (w : Inst m n → ℝ) (θ : Params m K) :
    condMean D (gain D w θ) = w ⬝ᵥ mu D θ - tau D (w - w0 D) ∧
    condVar D (gain D w θ) = w ⬝ᵥ (covariance D *ᵥ w) ∧
    score D w θ = condMean D (gain D w θ) - D.gamma / 2 * condVar D (gain D w θ) := by
  refine ⟨condMean_gain D hW hq hc w θ, condVar_gain D hW hq hc w θ, ?_⟩
  rw [condMean_gain D hW hq hc, condVar_gain D hW hq hc, meanReturnFormula, score]
  ring

/-! ### Belief average -/

lemma dot_wsum {ι T : Type} [Fintype ι] [Fintype T] (e : ι → ℝ) (pi : T → ℝ)
    (l : T → ι → ℝ) : e ⬝ᵥ (∑ t, pi t • l t) = ∑ t, pi t * (e ⬝ᵥ l t) := by
  rw [dotProduct_sum]
  exact sum_congr rfl fun t _ => by rw [dotProduct_smul, smul_eq_mul]

lemma beliefAverage (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi : T → ℝ) (hpi : ∑ t, pi t = 1) (w : Inst m n → ℝ) :
    beliefScore D par pi w = score D w (beliefMean par pi) := by
  set c := -(etf w ⬝ᵥ D.cE) - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D)
  have hs : ∀ θ : Params m K, score D w θ = exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha + c :=
    fun θ => by simp only [score, c]; ring
  simp only [beliefScore, beliefMean, hs, dot_wsum, mul_add, sum_add_distrib, ← sum_mul, hpi,
    one_mul]

omit [Fintype S] in
lemma ret_beliefMean (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi : T → ℝ) (hpi : ∑ t, pi t = 1) (s : S) (i : Inst m n) :
    1 + ret D (beliefMean par pi) s i = ∑ t, pi t * (1 + ret D (par t) s i) := by
  have hmv : ∀ {ι : Type} [Fintype ι] (M : Matrix ι (Fin K) ℝ) (j : ι),
      (M *ᵥ ∑ t, pi t • (par t).lam) j = ∑ t, pi t * (M *ᵥ (par t).lam) j := by
    intro ι _ M j
    rw [mulVec_sum, Finset.sum_apply]
    exact sum_congr rfl fun t _ => by rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hmu : mu D (beliefMean par pi) i = ∑ t, pi t * mu D (par t) i := by
    cases i with
    | inl j =>
      simp only [mu, beliefMean, Sum.elim_inl, Pi.add_apply, hmv, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
    | inr j =>
      simp only [mu, beliefMean, Sum.elim_inr, Pi.sub_apply, hmv, mul_sub, sum_sub_distrib,
        ← sum_mul, hpi, one_mul]
  have hsum : ∑ t, pi t * (1 + (mu D (par t) i + xi D s i))
      = ∑ t, pi t * mu D (par t) i + (1 + xi D s i) * ∑ t, pi t := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  simp only [ret_eq, Pi.add_apply]
  rw [hmu, hsum, hpi]
  ring

omit [Fintype S] in
lemma beliefMeanPositive (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi : T → ℝ) (hnn : ∀ t, 0 ≤ pi t) (hpi : ∑ t, pi t = 1)
    (hpos : ∀ t s i, 0 < 1 + ret D (par t) s i) (s : S) (i : Inst m n) :
    0 < 1 + ret D (beliefMean par pi) s i := by
  rw [ret_beliefMean D par pi hpi]
  obtain ⟨t, ht⟩ : ∃ t, 0 < pi t := by
    by_contra h
    push Not at h
    have : ∑ t, pi t = 0 := sum_eq_zero fun t _ => le_antisymm (h t) (hnn t)
    rw [hpi] at this
    exact one_ne_zero this
  exact sum_pos' (fun t _ => mul_nonneg (hnn t) (hpos t s i).le)
    ⟨t, mem_univ t, mul_pos ht (hpos t s i)⟩

lemma sameMeanSameDecisions (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi pi' : T → ℝ) (h1 : ∑ t, pi t = 1) (h2 : ∑ t, pi' t = 1)
    (hm : beliefMean par pi = beliefMean par pi') :
    (∀ w, beliefScore D par pi w = beliefScore D par pi' w) ∧
    (∀ w w', beliefScore D par pi w ≤ beliefScore D par pi w' ↔
      beliefScore D par pi' w ≤ beliefScore D par pi' w') ∧
    maximizers (beliefScore D par pi) (F D) = maximizers (beliefScore D par pi') (F D) ∧
    maximizers (beliefScore D par pi) (E D) = maximizers (beliefScore D par pi') (E D) ∧
    maximizers (beliefScore D par pi) (N D) = maximizers (beliefScore D par pi') (N D) := by
  have heq : beliefScore D par pi = beliefScore D par pi' := by
    funext w
    rw [beliefAverage D par pi h1, beliefAverage D par pi' h2, hm]
  refine ⟨fun w => by rw [heq], fun w w' => by rw [heq], ?_, ?_, ?_⟩ <;> rw [heq]

theorem proof : Standalone.M2ScoreAccounting.statement :=
  ⟨fun _ _ _ _ _ D hW v => costNormalization D hW v,
   fun _ _ _ _ _ D hW w => fundingTransfer D hW w,
   fun _ _ _ _ _ D hW w θ s => gainIdentity D hW w θ s,
   fun _ _ _ _ _ D w θ => meanReturnFormula D w θ,
   fun _ _ _ _ _ D hW hq hc w θ => momentIdentities D hW hq hc w θ,
   fun _ _ _ _ _ D _ _ par pi hpi w => beliefAverage D par pi hpi w,
   fun _ _ _ _ _ D _ _ par pi hnn hpi hpos s i => beliefMeanPositive D par pi hnn hpi hpos s i,
   fun _ _ _ _ _ D _ _ par pi pi' h1 h2 hm => sameMeanSameDecisions D par pi pi' h1 h2 hm⟩

end Novel.M2ScoreAccountingProof

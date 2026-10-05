import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M2ZeroAlphaLimitingCase

/-!
# Proof of claim 008: zero-alpha non-participation under feasible, costless ETF replacement

General part: with the ETF free to trade and the active cost at the replacement zero (case (A) or
(B)), `T(w) = (0, a + p)` is funded whenever `w` is, keeps the exposure (equal loadings), and its
score gain is `τ(w - w⁻) + (γ/2) a² v_ε - a ᾱ`, with `ᾱ = 0`. The quadratic term comes from
`a ξ_A + p ξ_E = t ξ_E + a ε` and the zero cross-moment. Attainment on F is re-proved here
(compact F, continuous criterion) rather than imported from claim 004's proof module.

Examples: direct computation, with `H(t) = t/50 - t²/200` strictly increasing on `[0, 1]`.
-/

namespace Novel.M2ZeroAlphaLimitingCaseProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry Standalone.M2ZeroAlphaLimitingCase

variable {K : ℕ} {S : Type} [Fintype S]

/-! ### Accounting in the one-fund, one-ETF case -/

omit [Fintype S] in
lemma sum_inst (f : Inst 1 1 → ℝ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

omit [Fintype S] in
lemma w0_add_k0 (D : Data 1 1 K S) (hW : 0 < W0 D) :
    w0 D (Sum.inl 0) + w0 D (Sum.inr 0) + k0 D = 1 := by
  have hW0 : D.h0 + (D.x0 (Sum.inl 0) + D.x0 (Sum.inr 0)) = W0 D := by
    rw [W0, sum_inst]
  simp only [w0, k0]
  rw [← add_div, ← add_div, add_comm, hW0, div_self hW.ne']

omit [Fintype S] in
lemma tau_free (D : Data 1 1 K S) (h1 : D.kplus (Sum.inr 0) = 0) (h2 : D.kminus (Sum.inr 0) = 0)
    (v : Inst 1 1 → ℝ) :
    tau D v = D.kplus (Sum.inl 0) * max (v (Sum.inl 0)) 0
      + D.kminus (Sum.inl 0) * max (-v (Sum.inl 0)) 0 := by
  rw [tau, sum_inst, h1, h2]
  ring

omit [Fintype S] in
lemma cash_eq (D : Data 1 1 K S) (hW : 0 < W0 D) (w : Inst 1 1 → ℝ) :
    cash D w = 1 - w (Sum.inl 0) - w (Sum.inr 0) - tau D (w - w0 D) := by
  have := w0_add_k0 D hW
  rw [cash, sum_inst]
  linarith

omit [Fintype S] in
lemma w0_nonneg (D : Data 1 1 K S) (h : InitialPosition D) (i : Inst 1 1) : 0 ≤ w0 D i :=
  div_nonneg (h.2.1 i) h.1.le

omit [Fintype S] in
lemma tau_nonneg (D : Data 1 1 K S) (h1 : D.kplus (Sum.inr 0) = 0)
    (h2 : D.kminus (Sum.inr 0) = 0) (hp : 0 ≤ D.kplus (Sum.inl 0)) (hm : 0 ≤ D.kminus (Sum.inl 0))
    (v : Inst 1 1 → ℝ) : 0 ≤ tau D v := by
  rw [tau_free D h1 h2]
  have := le_max_right (v (Sum.inl 0)) 0
  have := le_max_right (-v (Sum.inl 0)) 0
  positivity

omit [Fintype S] in
lemma replace_inl (w : Inst 1 1 → ℝ) : replace w (Sum.inl 0) = 0 := rfl

omit [Fintype S] in
lemma replace_inr (w : Inst 1 1 → ℝ) :
    replace w (Sum.inr 0) = w (Sum.inl 0) + w (Sum.inr 0) := rfl

omit [Fintype S] in
lemma tau_replace (D : Data 1 1 K S) (h : InitialPosition D) (h1 : D.kplus (Sum.inr 0) = 0)
    (h2 : D.kminus (Sum.inr 0) = 0) (hab : CaseAB D) (w : Inst 1 1 → ℝ) :
    tau D (replace w - w0 D) = 0 := by
  rw [tau_free D h1 h2]
  simp only [Pi.sub_apply, replace_inl, zero_sub, neg_neg]
  have ha0 := w0_nonneg D h (Sum.inl 0)
  rw [max_eq_right (by linarith)]
  rcases hab with hA | hB
  · rw [hA, max_self]; ring
  · rw [hB]; ring

omit [Fintype S] in
lemma exposure_eq (D : Data 1 1 K S) (hB : D.BA = D.BE) (w : Inst 1 1 → ℝ) :
    exposure D w = D.BEᵀ *ᵥ (fun _ => w (Sum.inl 0) + w (Sum.inr 0)) := by
  funext k
  simp [exposure, active, etf, hB, mulVec, dotProduct]
  ring

/-! ### The quadratic term -/

lemma quad_eq (D : Data 1 1 K S) (w : Inst 1 1 → ℝ) :
    w ⬝ᵥ (covariance D *ᵥ w) = ∑ s, D.q s * (w ⬝ᵥ xi D s) ^ 2 := by
  symm
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

lemma quad_diff (D : Data 1 1 K S) (hc : ∑ s, D.q s * (xi D s (Sum.inr 0) * eps D s) = 0)
    (w : Inst 1 1 → ℝ) :
    w ⬝ᵥ (covariance D *ᵥ w) - replace w ⬝ᵥ (covariance D *ᵥ replace w)
      = w (Sum.inl 0) ^ 2 * vEps D := by
  rw [quad_eq, quad_eq, ← sum_sub_distrib, vEps, mul_sum]
  have key : ∀ s, D.q s * (w ⬝ᵥ xi D s) ^ 2 - D.q s * (replace w ⬝ᵥ xi D s) ^ 2
      = 2 * (w (Sum.inl 0) * (w (Sum.inl 0) + w (Sum.inr 0)))
          * (D.q s * (xi D s (Sum.inr 0) * eps D s))
        + w (Sum.inl 0) ^ 2 * (D.q s * eps D s ^ 2) := by
    intro s
    simp only [dotProduct, sum_inst, replace_inl, replace_inr, eps]
    ring
  simp only [key, sum_add_distrib, ← mul_sum, hc, mul_zero, zero_add]

/-! ### The replacement -/

lemma score_diff (D : Data 1 1 K S) (hB : D.BA = D.BE) (hcE : D.cE = 0)
    (hc : ∑ s, D.q s * (xi D s (Sum.inr 0) * eps D s) = 0) (w : Inst 1 1 → ℝ)
    (htau : tau D (replace w - w0 D) = 0) (θ : Params 1 K) :
    score D (replace w) θ - score D w θ
      = -(w (Sum.inl 0) * θ.alpha 0) + D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D
        + tau D (w - w0 D) := by
  have hq := quad_diff D hc w
  have hexp : exposure D (replace w) = exposure D w := by
    rw [exposure_eq D hB, exposure_eq D hB, replace_inl, replace_inr, zero_add]
  have ha1 : active (replace w) ⬝ᵥ θ.alpha = 0 := by
    simp [dotProduct, active, replace]
  have ha2 : active w ⬝ᵥ θ.alpha = w (Sum.inl 0) * θ.alpha 0 := by
    simp [dotProduct, active]
  simp only [score, hexp, htau, hcE, dotProduct_zero, ha1, ha2]
  linear_combination (D.gamma / 2) * hq

lemma belief_diff (D : Data 1 1 K S) {T : Type} [Fintype T] (par : T → Params 1 K)
    (pi : T → ℝ) (hB : D.BA = D.BE) (hcE : D.cE = 0)
    (hc : ∑ s, D.q s * (xi D s (Sum.inr 0) * eps D s) = 0) (hpi : ∑ t, pi t = 1)
    (hα : (beliefMean par pi).alpha = 0) (w : Inst 1 1 → ℝ)
    (htau : tau D (replace w - w0 D) = 0) :
    beliefScore D par pi (replace w) - beliefScore D par pi w
      = tau D (w - w0 D) + D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D := by
  have hbar : ∑ t, pi t * (par t).alpha 0 = 0 := by
    have := congrFun hα 0
    simpa [beliefMean, Finset.sum_apply] using this
  rw [beliefScore, beliefScore, ← sum_sub_distrib]
  have : ∀ t, pi t * score D (replace w) (par t) - pi t * score D w (par t)
      = -(w (Sum.inl 0)) * (pi t * (par t).alpha 0)
        + pi t * (D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D + tau D (w - w0 D)) := by
    intro t
    rw [← mul_sub, score_diff D hB hcE hc w htau]
    ring
  simp only [this, sum_add_distrib, ← mul_sum, ← sum_mul, hbar, hpi]
  ring

/-- Unpacked setting. -/
lemma setting_parts {D : Data 1 1 K S} {T : Type} [Fintype T] {par : T → Params 1 K}
    {pi : T → ℝ} (h : ZeroAlphaSetting D par pi) :
    InitialPosition D ∧ D.BA = D.BE ∧ D.cE = 0 ∧
    D.kplus (Sum.inr 0) = 0 ∧ D.kminus (Sum.inr 0) = 0 ∧ D.wbar (Sum.inr 0) = 1 ∧
    0 ≤ D.kplus (Sum.inl 0) ∧ 0 ≤ D.kminus (Sum.inl 0) ∧ 0 ≤ D.gamma ∧
    (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧ ∑ t, pi t = 1 ∧
    (beliefMean par pi).alpha = 0 ∧ ∑ s, D.q s * (xi D s (Sum.inr 0) * eps D s) = 0 := h

lemma vEps_nonneg (D : Data 1 1 K S) (hq : ∀ s, 0 ≤ D.q s) : 0 ≤ vEps D :=
  sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)

lemma replacement (D : Data 1 1 K S) {T : Type} [Fintype T] (par : T → Params 1 K)
    (pi : T → ℝ) (h : ZeroAlphaSetting D par pi) (hab : CaseAB D) (w : Inst 1 1 → ℝ)
    (hw : w ∈ F D) :
    replace w ∈ F D ∧ exposure D (replace w) = exposure D w ∧
      tau D (replace w - w0 D) = 0 ∧
      cash D (replace w) - cash D w = tau D (w - w0 D) ∧
      beliefScore D par pi (replace w) - beliefScore D par pi w
        = tau D (w - w0 D) + D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D ∧
      0 ≤ beliefScore D par pi (replace w) - beliefScore D par pi w := by
  obtain ⟨hIP, hB, hcE, hkp, hkm, hbar1, hpA, hmA, hg, hq, _, hpi, hα, hc⟩ := setting_parts h
  have hW := hIP.1
  have htauR := tau_replace D hIP hkp hkm hab w
  have htau := tau_nonneg D hkp hkm hpA hmA (w - w0 D)
  have ha := (hw.1 (Sum.inl 0)).1
  have hp := (hw.1 (Sum.inr 0)).1
  have hcw := hw.2
  rw [cash_eq D hW] at hcw
  have hdiff := belief_diff D par pi hB hcE hc hpi hα w htauR
  refine ⟨⟨fun i => ?_, ?_⟩, ?_, htauR, ?_, hdiff, ?_⟩
  · rcases i with j | j <;> obtain rfl : j = 0 := Subsingleton.elim _ _
    · exact ⟨le_rfl, le_trans (w0_nonneg D hIP _) (hIP.2.2.2 _)⟩
    · refine ⟨by rw [replace_inr]; linarith, ?_⟩
      rw [replace_inr, hbar1]
      linarith
  · rw [cash_eq D hW, htauR, replace_inl, replace_inr]
    linarith
  · rw [exposure_eq D hB, exposure_eq D hB, replace_inl, replace_inr, zero_add]
  · rw [cash_eq D hW, cash_eq D hW, htauR, replace_inl, replace_inr]
    ring
  · rw [hdiff]
    have := vEps_nonneg D hq
    positivity

/-! ### Attainment on F -/

omit [Fintype S] in
lemma continuous_tau (D : Data 1 1 K S) : Continuous (tau D) := by
  unfold tau
  fun_prop

omit [Fintype S] in
lemma continuous_cash (D : Data 1 1 K S) : Continuous (cash D) := by
  have := continuous_tau D
  unfold cash
  fun_prop

lemma continuous_beliefScore (D : Data 1 1 K S) {T : Type} [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ) : Continuous (beliefScore D par pi) := by
  have := continuous_tau D
  unfold beliefScore score exposure active etf covariance
  simp only [Pi.add_apply, mulVec, dotProduct]
  fun_prop

omit [Fintype S] in
lemma isCompact_F (D : Data 1 1 K S) : IsCompact (F D) := by
  have h1 : IsClosed {w : Inst 1 1 → ℝ | ∀ i, 0 ≤ w i ∧ w i ≤ D.wbar i} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  have hF : IsClosed (F D) := h1.inter (isClosed_le continuous_const (continuous_cash D))
  exact isCompact_Icc.of_isClosed_subset hF fun _ hw => ⟨fun i => (hw.1 i).1, fun i => (hw.1 i).2⟩

omit [Fintype S] in
lemma w0_mem_F (D : Data 1 1 K S) (h : InitialPosition D) : w0 D ∈ F D := by
  refine ⟨fun i => ⟨w0_nonneg D h i, h.2.2.2 i⟩, ?_⟩
  have : cash D (w0 D) = k0 D := by simp [cash, tau]
  rw [this]
  exact div_nonneg h.2.2.1 h.1.le

/-! ### Non-participation -/

lemma nonParticipation (D : Data 1 1 K S) {T : Type} [Fintype T] (par : T → Params 1 K)
    (pi : T → ℝ) (h : ZeroAlphaSetting D par pi) (hab : CaseAB D) :
    (∃ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w ∧ w (Sum.inl 0) = 0) ∧
    (w0 D (Sum.inl 0) = 0 →
      (∀ w ∈ F D, replace w ∈ E D) ∧
      (∀ wF wE, wF ∈ F D → IsMaxOn (beliefScore D par pi) (F D) wF →
        wE ∈ E D → IsMaxOn (beliefScore D par pi) (E D) wE →
        beliefScore D par pi wF = beliefScore D par pi wE) ∧
      (0 < D.kplus (Sum.inl 0) ∨ 0 < D.gamma * vEps D →
        ∀ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w → w (Sum.inl 0) = 0)) ∧
    (D.kminus (Sum.inl 0) = 0 →
      (0 < D.gamma * vEps D →
        ∀ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w → w (Sum.inl 0) = 0) ∧
      (0 < w0 D (Sum.inl 0) → ∀ w ∈ E D, w (Sum.inl 0) ≠ 0)) := by
  obtain ⟨hIP, _, _, hkp, hkm, _, hpA, _, hg, hq, _, _, _, _⟩ := setting_parts h
  set f := beliefScore D par pi
  have hrep := replacement D par pi h hab
  -- a maximizer with a > 0 is impossible once the replacement gain is strictly positive
  have strict : ∀ w ∈ F D, IsMaxOn f (F D) w →
      (0 < w (Sum.inl 0) → 0 < tau D (w - w0 D) + D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D) →
      w (Sum.inl 0) = 0 := by
    intro w hw hmax hpos
    obtain ⟨hF', _, _, _, hd, _⟩ := hrep w hw
    have hle : f (replace w) ≤ f w := hmax hF'
    have ha := (hw.1 (Sum.inl 0)).1
    by_contra hne
    have := hpos (lt_of_le_of_ne ha (Ne.symm hne))
    linarith
  have hE : w0 D (Sum.inl 0) = 0 → ∀ w ∈ F D, replace w ∈ E D := by
    intro hA w hw
    refine ⟨(hrep w hw).1, ?_⟩
    funext j
    fin_cases j
    simp [active, replace, hA]
  refine ⟨?_, fun hA => ⟨hE hA, ?_, ?_⟩, fun hB => ⟨?_, ?_⟩⟩
  · obtain ⟨w, hw, hmax⟩ :=
      (isCompact_F D).exists_isMaxOn ⟨_, w0_mem_F D hIP⟩ (continuous_beliefScore D par pi).continuousOn
    obtain ⟨hF', _, _, _, _, hge⟩ := hrep w hw
    refine ⟨replace w, hF', fun z hz => ?_, replace_inl w⟩
    have := hmax hz
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  · intro wF wE hwF hmF hwE hmE
    have h1 : f wE ≤ f wF := hmF hwE.1
    obtain ⟨_, _, _, _, _, hge⟩ := hrep wF hwF
    have h2 : f (replace wF) ≤ f wE := hmE (hE hA wF hwF)
    linarith
  · intro hcond w hw hmax
    refine strict w hw hmax fun ha => ?_
    have htw : tau D (w - w0 D) = D.kplus (Sum.inl 0) * w (Sum.inl 0) := by
      rw [tau_free D hkp hkm]
      simp only [Pi.sub_apply, hA, sub_zero]
      rw [max_eq_left ha.le, max_eq_right (by linarith)]
      ring
    rw [htw]
    have hv := vEps_nonneg D hq
    rcases hcond with hk | hgv
    · have : 0 ≤ D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D := by positivity
      nlinarith [mul_pos hk ha]
    · have : 0 < D.gamma * vEps D * w (Sum.inl 0) ^ 2 := mul_pos hgv (by positivity)
      nlinarith [mul_nonneg hpA ha.le]
  · intro hgv w hw hmax
    refine strict w hw hmax fun ha => ?_
    have ht := tau_nonneg D hkp hkm hpA (by rw [hB]) (w - w0 D)
    have : 0 < D.gamma * vEps D * w (Sum.inl 0) ^ 2 := mul_pos hgv (by positivity)
    nlinarith
  · intro hpos w hw hzero
    have := congrFun hw.2 0
    simp only [active] at this
    rw [this] at hzero
    linarith

/-! ### Exact replication -/

omit [Fintype S] in
lemma exactReplication (D : Data 1 1 K S) {T : Type} (par : T → Params 1 K)
    (hIP : InitialPosition D) (hB : D.BA = D.BE) (hcE : D.cE = 0) (hα : ∀ t, (par t).alpha = 0)
    (heps : ∀ s, eps D s = 0) (hkp : D.kplus (Sum.inr 0) = 0) (hkm : D.kminus (Sum.inr 0) = 0)
    (hab : CaseAB D) :
    (∀ t s, ret D (par t) s (Sum.inl 0) = ret D (par t) s (Sum.inr 0)) ∧
    ∀ (w : Inst 1 1 → ℝ) t s,
      W1 D (replace w) (par t) s - W1 D w (par t) s = W0 D * tau D (w - w0 D) := by
  have hret : ∀ t s, ret D (par t) s (Sum.inl 0) = ret D (par t) s (Sum.inr 0) := by
    intro t s
    have he := heps s
    simp only [eps, xi, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, hB] at he
    simp only [ret, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply, hB, hcE, hα t,
      Pi.zero_apply]
    linarith
  refine ⟨hret, fun w t s => ?_⟩
  have htauR := tau_replace D hIP hkp hkm hab w
  have hsum : ∑ i, (replace w i - w0 D i) = ∑ i, (w i - w0 D i) := by
    rw [sum_inst, sum_inst, replace_inl, replace_inr]
    ring
  simp only [W1, cash, hsum, htauR, sum_inst, replace_inl, replace_inr, hret t s]
  ring

theorem proof_general : Replacement ∧ NonParticipation ∧ ExactReplication :=
  ⟨fun _ _ _ D _ _ par pi h hab w hw => replacement D par pi h hab w hw,
   fun _ _ _ D _ _ par pi h hab => nonParticipation D par pi h hab,
   fun _ _ _ D _ par hIP hB hcE hα heps hkp hkm hab =>
     exactReplication D par hIP hB hcE hα heps hkp hkm hab⟩

/-! ### The examples -/

section Examples

variable (a₀ p₀ h₀ κ pb : ℝ)

/-- Common-return score before costs. -/
noncomputable def H (t : ℝ) : ℝ := t / 50 - t ^ 2 / 200

lemma H_mono {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 1) : H u ≤ H v := by
  unfold H; nlinarith [mul_nonneg (sub_nonneg.mpr huv) (by linarith : (0 : ℝ) ≤ 2 - u - v)]

lemma H_strict {u v : ℝ} (huv : u < v) (hv : v ≤ 1) : H u < H v := by
  unfold H; nlinarith [mul_pos (sub_pos.mpr huv) (by linarith : (0 : ℝ) < 2 - u - v)]

lemma hold_surj (w : Inst 1 1 → ℝ) : w = hold (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with j | j <;> obtain rfl : j = 0 := Subsingleton.elim _ _ <;> rfl

lemma hold_inj {a p a' p' : ℝ} : hold a p = hold a' p' ↔ a = a' ∧ p = p' :=
  ⟨fun h => ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0)⟩, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

variable {a₀ p₀ h₀ κ pb}

lemma W0_ex (hW : h₀ + (a₀ + p₀) = 1) : W0 (exData a₀ p₀ h₀ κ pb) = 1 := by
  rw [W0, sum_inst]; simpa [exData] using hW

lemma w0_ex (hW : h₀ + (a₀ + p₀) = 1) : w0 (exData a₀ p₀ h₀ κ pb) = hold a₀ p₀ := by
  funext i
  rcases i with j | j <;> simp only [w0, W0_ex hW, div_one] <;> simp [exData, hold]

lemma tau_ex (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    tau (exData a₀ p₀ h₀ κ pb) (hold a p - w0 (exData a₀ p₀ h₀ κ pb))
      = κ * (max (a - a₀) 0 + max (-(a - a₀)) 0) := by
  rw [w0_ex hW, tau, sum_inst]
  simp [exData, hold]
  ring

lemma cash_ex (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    cash (exData a₀ p₀ h₀ κ pb) (hold a p)
      = 1 - a - p - κ * (max (a - a₀) 0 + max (-(a - a₀)) 0) := by
  have hW' : 0 < W0 (exData a₀ p₀ h₀ κ pb) := by rw [W0_ex hW]; norm_num
  rw [cash_eq _ hW', ← tau_ex hW]
  rfl

lemma Q_ex (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    Qex a₀ p₀ h₀ κ pb (hold a p) = H (a + p) - κ * (max (a - a₀) 0 + max (-(a - a₀)) 0) := by
  have hq : hold a p ⬝ᵥ (covariance (exData a₀ p₀ h₀ κ pb) *ᵥ hold a p) = (a + p) ^ 2 / 100 := by
    rw [quad_eq]
    simp [exData, xi, hold, dotProduct, Fin.sum_univ_two]
    ring
  simp only [Qex, beliefScore, Fin.sum_univ_one, exPi, one_mul, score, hq, tau_ex hW]
  simp [exposure, active, etf, hold, exData, exPar, dotProduct, mulVec, H]
  ring

lemma mem_F_ex (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    hold a p ∈ F (exData a₀ p₀ h₀ κ pb) ↔ (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ p ∧ p ≤ pb) ∧
      0 ≤ 1 - a - p - κ * (max (a - a₀) 0 + max (-(a - a₀)) 0) := by
  rw [← cash_ex (pb := pb) hW]
  simp [F, Sum.forall, hold, exData, and_assoc]

lemma mem_E_ex (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    hold a p ∈ E (exData a₀ p₀ h₀ κ pb) ↔ hold a p ∈ F (exData a₀ p₀ h₀ κ pb) ∧ a = a₀ := by
  refine and_congr Iff.rfl ?_
  rw [w0_ex hW]
  exact ⟨fun h => congrFun h 0, fun h => by funext j; simp [active, hold, h]⟩

lemma valid_ex (hW : h₀ + (a₀ + p₀) = 1) (ha : 0 ≤ a₀) (hp : 0 ≤ p₀) (hh : 0 ≤ h₀)
    (ha1 : a₀ ≤ 1) (hk : 0 ≤ κ) (hk1 : κ < 1) (hpb : p₀ ≤ pb) (hpb1 : pb ≤ 1) :
    ExampleValid a₀ p₀ h₀ κ pb := by
  refine ⟨W0_ex hW, ⟨by rw [W0_ex hW]; norm_num, fun i => ?_, hh, fun i => ?_⟩, fun i => ?_,
    fun i => ?_, fun i => ?_, by norm_num [exData], fun s => by norm_num [exData],
    by norm_num [MassesSumToOne, exData], ⟨?_, ?_, ?_⟩, fun t => by norm_num [exPi],
    by norm_num [exPi], ?_⟩
  · rcases i with j | j <;> simpa [exData]
  · rw [w0_ex hW]; rcases i with j | j <;> simpa [hold, exData]
  · rcases i with j | j <;> simp [exData, hk]
  · rcases i with j | j <;> simp [exData, hk1]
  · rcases i with j | j <;> simp [exData, hpb1]
  · funext k; fin_cases k <;> norm_num [exData, Fin.sum_univ_two]
  · funext k; simp [exData]
  · funext k; simp [exData]
  · intro t s i
    rcases i with j | j <;> fin_cases s <;>
      norm_num [ret, exData, exPar, mulVec, dotProduct, Matrix.vecHead, Matrix.vecTail]

lemma H_one : H 1 = 3 / 200 := by norm_num [H]

/-- Zero active costs: the F maximizers are exactly the feasible holdings with `a + p = 1`. -/
lemma maxset_free (hpb : 0 ≤ pb) :
    maximizers (Qex 0 0 1 0 pb) (F (exData 0 0 1 0 pb))
      = {w | w ∈ F (exData 0 0 1 0 pb) ∧ w (Sum.inl 0) + w (Sum.inr 0) = 1} := by
  have hW : (1 : ℝ) + (0 + 0) = 1 := by norm_num
  have hQ : ∀ a p, Qex 0 0 1 0 pb (hold a p) = H (a + p) := fun a p => by
    rw [Q_ex hW]; ring
  have hF : ∀ a p, hold a p ∈ F (exData 0 0 1 0 pb) ↔
      (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ p ∧ p ≤ pb) ∧ a + p ≤ 1 := fun a p => by
    rw [mem_F_ex hW]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by linarith⟩
  have h10 : hold 1 0 ∈ F (exData 0 0 1 0 pb) := (hF 1 0).mpr ⟨by norm_num, ⟨le_rfl, hpb⟩, by norm_num⟩
  ext w
  rw [hold_surj w]
  simp only [maximizers, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hw, hmax⟩
    refine ⟨hw, ?_⟩
    obtain ⟨⟨ha, _⟩, ⟨hp, _⟩, ht⟩ := (hF _ _).mp hw
    have := hmax _ h10
    rw [hQ, hQ] at this
    by_contra hne
    have := H_strict (lt_of_le_of_ne ht hne) (le_refl (1 : ℝ))
    simp only [add_zero] at *
    linarith
  · rintro ⟨hw, ht⟩
    refine ⟨hw, fun w' hw' => ?_⟩
    rw [hold_surj w'] at hw' ⊢
    obtain ⟨_, _, ht'⟩ := (hF _ _).mp hw'
    have ht1 : w (Sum.inl 0) + w (Sum.inr 0) = 1 := ht
    rw [hQ, hQ, ht1]
    exact H_mono ht' le_rfl

lemma examples : Examples := by
  have hW1 : (1 : ℝ) + (0 + 0) = 1 := by norm_num
  have hW2 : (0 : ℝ) + (1 + 0) = 1 := by norm_num
  refine ⟨valid_ex hW1 le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) le_rfl,
    valid_ex hW2 (by norm_num) le_rfl le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl,
    valid_ex hW1 le_rfl le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl,
    valid_ex hW1 le_rfl le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_, maxset_free (by norm_num), ?_, ?_, ?_,
    maxset_free (by norm_num), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- case 1: positive purchase cost
  · refine ⟨(mem_F_ex hW1 0 1).mpr ⟨by norm_num, by norm_num, by norm_num⟩, fun w hw hne => ?_⟩
    rw [hold_surj w] at hw hne ⊢
    obtain ⟨⟨ha, _⟩, ⟨hp, hp1⟩, hc⟩ := (mem_F_ex hW1 _ _).mp hw
    rw [Q_ex hW1, Q_ex hW1]
    simp only [sub_zero] at hc ⊢
    rw [max_eq_left ha, max_eq_right (by linarith)] at hc ⊢
    norm_num
    have h1 := H_one
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have := H_mono (by linarith : w (Sum.inl 0) + w (Sum.inr 0) ≤ 1) (le_refl (1 : ℝ))
      rw [H_one] at this; nlinarith
    · have hp' : w (Sum.inr 0) < 1 := lt_of_le_of_ne hp1 fun h => hne (by rw [← ha', h])
      have := H_strict (by rw [← ha']; linarith : w (Sum.inl 0) + w (Sum.inr 0) < 1) le_rfl
      rw [H_one] at this; rw [← ha'] at this ⊢; linarith
  · rw [Q_ex hW1]; norm_num [H]
  -- case 2: costly incumbent
  · refine ⟨(mem_F_ex hW2 1 0).mpr ⟨by norm_num, by norm_num, by norm_num⟩, fun w hw hne => ?_⟩
    rw [hold_surj w] at hw hne ⊢
    obtain ⟨⟨ha, ha1⟩, ⟨hp, _⟩, hc⟩ := (mem_F_ex hW2 _ _).mp hw
    rw [Q_ex hW2, Q_ex hW2]
    rw [max_eq_right (by linarith), max_eq_left (by linarith)] at hc ⊢
    norm_num
    have h1 := H_one
    have ht : w (Sum.inl 0) + w (Sum.inr 0) ≤ 1 := by linarith
    have hH := H_mono ht (le_refl (1 : ℝ))
    rw [H_one] at hH
    rcases lt_or_eq_of_le ha1 with ha' | ha'
    · linarith
    · exfalso
      apply hne
      rw [hold_inj]
      exact ⟨ha', by linarith⟩
  · rw [Q_ex hW2]; norm_num [H]
  · refine ⟨⟨(mem_F_ex hW2 0 (99 / 100)).mpr ⟨by norm_num, by norm_num, ?_⟩, rfl⟩,
      fun w hw hne => ?_⟩
    · rw [max_eq_right (by norm_num), max_eq_left (by norm_num)]; norm_num
    obtain ⟨hwF, ha⟩ := hw
    rw [hold_surj w, ha] at hwF hne ⊢
    obtain ⟨_, ⟨hp, _⟩, hc⟩ := (mem_F_ex hW2 _ _).mp hwF
    rw [Q_ex hW2, Q_ex hW2]
    rw [max_eq_right (by norm_num), max_eq_left (by norm_num)] at hc ⊢
    norm_num at hc ⊢
    have hp' : w (Sum.inr 0) < 99 / 100 := lt_of_le_of_ne (by linarith) fun h => hne (by rw [h])
    have := H_strict (by simpa using hp' : 0 + w (Sum.inr 0) < 0 + 99 / 100) (by norm_num)
    simp only [zero_add] at this
    linarith
  · rw [Q_ex hW2]; norm_num [H]
  · rw [CaseAB, w0_ex hW2]; norm_num [hold, exData]
  -- case 3: tie under exact replication
  · rw [maxset_free (by norm_num)]
    exact ⟨(mem_F_ex hW1 0 1).mpr ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num [hold]⟩
  · rw [maxset_free (by norm_num)]
    exact ⟨(mem_F_ex hW1 1 0).mpr ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num [hold]⟩
  · rw [Q_ex hW1]; norm_num [H]
  -- case 4: ETF cap 1/4
  · rw [Q_ex hW1]; norm_num [H]
  · refine ⟨(mem_E_ex hW1 0 (1 / 4)).mpr ⟨(mem_F_ex hW1 0 (1 / 4)).mpr
      ⟨by norm_num, by norm_num, by norm_num⟩, rfl⟩, fun w hw hne => ?_⟩
    rw [hold_surj w] at hw hne ⊢
    obtain ⟨hwF, ha⟩ := (mem_E_ex hW1 _ _).mp hw
    rw [ha] at hwF hne ⊢
    obtain ⟨_, ⟨hp, hp1⟩, _⟩ := (mem_F_ex hW1 _ _).mp hwF
    rw [Q_ex hW1, Q_ex hW1]
    have hp' : w (Sum.inr 0) < 1 / 4 := lt_of_le_of_ne hp1 fun h => hne (by rw [h])
    have := H_strict (by simpa using hp' : 0 + w (Sum.inr 0) < 0 + 1 / 4) (by norm_num)
    norm_num at this ⊢
    linarith
  · rw [Q_ex hW1]; norm_num [H]
  · rw [Q_ex hW1, Q_ex hW1]; norm_num [H]
  · exact (mem_F_ex hW1 _ _).mpr ⟨by norm_num, by norm_num, by norm_num⟩
  · have : replace (hold (3 / 4) (1 / 4)) = hold 0 1 := by
      funext i
      rcases i with j | j
      · simp [replace, hold]
      · simp [replace, hold]; norm_num
    rw [this, mem_F_ex hW1]
    norm_num

end Examples

theorem proof : Standalone.M2ZeroAlphaLimitingCase.statement :=
  ⟨proof_general.1, proof_general.2.1, proof_general.2.2, examples⟩

end Novel.M2ZeroAlphaLimitingCaseProof

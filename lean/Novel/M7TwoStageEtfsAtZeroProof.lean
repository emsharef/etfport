import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Convex.Function
import Standalone.M7TwoStageEtfsAtZero

/-!
# Proof of claim 041

No other claim's proof module is used. Claim 040's objects are defined in the statement.

* **Quadratic facts.** `G_E(w + t d) = G_E(w) - t ζ(w)'d - t²(γ/2) d'Σ_EE d`, and
  `G_E(w) = G_E(w_TB) - (γ/2)(w - w_TB)'Σ_EE(w - w_TB)`.
* **Existence.** `w'Σ_EE w ≥ c‖w‖²` with `c > 0` (the minimum on the unit sphere). So `G_E`, plus
  anything bounded above on the box, is maximized on a compact piece of any closed feasible set.
* **Part 1.** Coordinate moves give `ζ* ≥ 0` and complementarity. The fund lines hold iff `x₂`
  maximizes `H(x) - ζ*'Qx` over the box, by coordinate moves and a supergradient. That holds iff
  `(w*, x₂)` is jointly optimal: a saddle argument one way, and a move along
  `(Q(y - x₂), y - x₂)` the other.
* **Part 2.** On the fibre interval `V_E(rx) = G_E(w*)`, so `Φ` is `H` plus a constant there. The
  unique maximizer of the one-fund `H` on an interval is the clipped band solution.
* **Part 3.** Completing the square: the soft stage 2 is the joint objective less `G_E(w_s)` and
  `ν'(w - w_s)`.
-/

namespace Novel.M7TwoStageEtfsAtZeroProof

open Matrix Finset Standalone.M7TwoStageEtfsAtZero Standalone.M7TwoStageEtfsAtZero.TS
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {M N : ℕ} {P : TS M N}

/-! ### Quadratic facts -/

section Quad

variable (hS : P.Setting)
include hS

lemma S_symm (u v : Fin M → ℝ) : u ⬝ᵥ (P.Sig *ᵥ v) = v ⬝ᵥ (P.Sig *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.2.1, dotProduct_comm]

lemma V_symm (u v : Fin N → ℝ) : u ⬝ᵥ (P.V *ᵥ v) = v ⬝ᵥ (P.V *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.2.2.2.1, dotProduct_comm]

lemma S_nonneg (v : Fin M → ℝ) : 0 ≤ v ⬝ᵥ (P.Sig *ᵥ v) := by
  by_cases h : v = 0
  · simp [h]
  · exact (hS.2.2.1 v h).le

/-- `G_E` along a line. -/
lemma GE_line (w d : Fin M → ℝ) (t : ℝ) :
    P.GE (w + t • d) = P.GE w - t * (P.zeta w ⬝ᵥ d) - t ^ 2 * (P.gamma / 2 * (d ⬝ᵥ (P.Sig *ᵥ d))) := by
  simp only [GE, Standalone.M7FundDecisionEtfsAtZero.GE, zeta, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, sub_dotProduct]
  rw [dotProduct_comm (P.Sig *ᵥ w) d, S_symm hS d w]
  ring

lemma S_det : IsUnit P.Sig.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hmv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have := hS.2.2.1 v hv
  rw [hmv, dotProduct_zero] at this
  exact lt_irrefl _ this

lemma S_wTB : P.gamma • (P.Sig *ᵥ P.wTB) = P.mu := by
  have hγ : P.gamma ≠ 0 := hS.1.ne'
  have hdet : IsUnit (P.gamma • P.Sig).det := by
    rw [det_smul, IsUnit.mul_iff]; exact ⟨(isUnit_iff_ne_zero.2 (pow_ne_zero _ hγ)), S_det hS⟩
  rw [← smul_mulVec, wTB, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

lemma zeta_wTB : P.zeta P.wTB = 0 := by rw [zeta, S_wTB hS, sub_self]

/-- Completing the square around `w_TB`. -/
lemma GE_square (w : Fin M → ℝ) :
    P.GE w = P.GE P.wTB - P.gamma / 2 * ((w - P.wTB) ⬝ᵥ (P.Sig *ᵥ (w - P.wTB))) := by
  have h := GE_line hS P.wTB (w - P.wTB) 1
  rw [one_smul, add_sub_cancel, zeta_wTB hS, zero_dotProduct] at h
  rw [h]; ring

lemma GE_le_wTB (w : Fin M → ℝ) : P.GE w ≤ P.GE P.wTB := by
  rw [GE_square hS w]
  have := S_nonneg hS (w - P.wTB)
  have := hS.1
  nlinarith

lemma GE_eq_wTB_iff (w : Fin M → ℝ) : P.GE w = P.GE P.wTB ↔ w = P.wTB := by
  constructor
  · intro h
    by_contra hne
    have hpos := hS.2.2.1 (w - P.wTB) (sub_ne_zero.2 hne)
    rw [GE_square hS w] at h
    have := hS.1
    nlinarith
  · rintro rfl; rfl

/-- `G_E` is strictly concave. -/
lemma GE_mid {w v : Fin M → ℝ} (hne : w ≠ v) :
    (P.GE w + P.GE v) / 2 < P.GE ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • v) := by
  have e : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • v = w + (1 / 2 : ℝ) • (v - w) := by module
  rw [e, GE_line hS]
  have h2 := GE_line hS w (v - w) 1
  rw [one_smul, add_sub_cancel] at h2
  have hpos := hS.2.2.1 (v - w) (sub_ne_zero.2 hne.symm)
  have := hS.1
  nlinarith

end Quad

/-! ### Existence -/

section Exist

variable (hS : P.Setting)
include hS

/-- `w'Σ_EE w ≥ c‖w‖²` for some `c > 0`. -/
lemma quad_lower : ∃ c > 0, ∀ w : Fin M → ℝ, c * ‖w‖ ^ 2 ≤ w ⬝ᵥ (P.Sig *ᵥ w) := by
  rcases isEmpty_or_nonempty (Fin M) with hM | hM
  · refine ⟨1, one_pos, fun w => ?_⟩
    have : w = 0 := Subsingleton.elim _ _
    simp [this]
  have hsph : IsCompact (Metric.sphere (0 : Fin M → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : Fin M → ℝ) 1).Nonempty := by
    obtain ⟨j⟩ := hM
    refine ⟨Pi.single j 1, ?_⟩
    simp [Pi.norm_single]
  have hc : Continuous (fun w : Fin M → ℝ => w ⬝ᵥ (P.Sig *ᵥ w)) := by fun_prop
  obtain ⟨u, hu, hmin⟩ := hsph.exists_isMinOn hne hc.continuousOn
  have hu0 : u ≠ 0 := by
    intro h; rw [h, Metric.mem_sphere, dist_self] at hu; norm_num at hu
  refine ⟨u ⬝ᵥ (P.Sig *ᵥ u), hS.2.2.1 u hu0, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hmem : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : Fin M → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := hmin hmem
  simp only [Set.mem_ofPred_eq, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  have e : ‖w‖⁻¹ * (‖w‖⁻¹ * (w ⬝ᵥ (P.Sig *ᵥ w))) * ‖w‖ ^ 2 = w ⬝ᵥ (P.Sig *ᵥ w) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖w‖)]

omit hS in
lemma dot_le_norm (a w : Fin M → ℝ) : a ⬝ᵥ w ≤ (∑ j, |a j|) * ‖w‖ := by
  rw [dotProduct, sum_mul]
  exact sum_le_sum fun j _ => by
    calc a j * w j ≤ |a j * w j| := le_abs_self _
      _ = |a j| * |w j| := abs_mul _ _
      _ ≤ |a j| * ‖w‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (abs_nonneg _)

/-- Far out, `G_E` is below any given level. -/
lemma GE_far (L : ℝ) : ∃ R0 : ℝ, ∀ w : Fin M → ℝ, R0 < ‖w‖ → P.GE w < L := by
  obtain ⟨c, hc, hq⟩ := quad_lower hS
  set A := ∑ j, |P.mu j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hγ := hS.1
  refine ⟨(A + |L| + 1) * 2 / (P.gamma * c) + 1, fun w hw => ?_⟩
  have h1 : P.mu ⬝ᵥ w ≤ A * ‖w‖ := dot_le_norm P.mu w
  have h2 := hq w
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have hk : 0 < P.gamma * c := mul_pos hγ hc
  have hd0 : 0 ≤ (A + |L| + 1) * 2 / (P.gamma * c) := by positivity
  have hw1 : 1 ≤ ‖w‖ := by linarith
  have hbig : (A + |L| + 1) * 2 ≤ P.gamma * c * ‖w‖ := by
    have : (A + |L| + 1) * 2 / (P.gamma * c) < ‖w‖ := by linarith
    rw [div_lt_iff₀ hk] at this; linarith
  have h3 : (A + |L| + 1) * ‖w‖ ≤ P.gamma / 2 * (w ⬝ᵥ (P.Sig *ᵥ w)) := by
    have h4 : P.gamma / 2 * (c * ‖w‖ ^ 2) ≤ P.gamma / 2 * (w ⬝ᵥ (P.Sig *ᵥ w)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hbig hn]
  simp only [GE, Standalone.M7FundDecisionEtfsAtZero.GE]
  have hL := neg_abs_le L
  have h5 : |L| + 1 ≤ (|L| + 1) * ‖w‖ := by nlinarith [abs_nonneg L]
  nlinarith

/-- `G_E` plus a function bounded above on a compact set of second coordinates attains its maximum
on any closed nonempty set whose second coordinates lie there. -/
lemma exists_max_prod {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) {g : E → ℝ} (hg : Continuous g) {C : Set ((Fin M → ℝ) × E)}
    (hC : IsClosed C) (hCK : ∀ p ∈ C, p.2 ∈ K) {p0 : (Fin M → ℝ) × E} (hp0 : p0 ∈ C) :
    ∃ p ∈ C, IsMaxOn (fun p => P.GE p.1 + g p.2) C p := by
  obtain ⟨gmax, hgmax⟩ : ∃ gmax, ∀ y ∈ K, g y ≤ gmax := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    obtain ⟨y0, hy0, hy⟩ := hK.exists_isMaxOn h hg.continuousOn
    exact ⟨g y0, fun y hy' => hy hy'⟩
  obtain ⟨R0, hR0⟩ := GE_far hS (P.GE p0.1 + g p0.2 - gmax)
  set R := max R0 ‖p0.1‖
  have hKc : IsCompact (C ∩ (Metric.closedBall (0 : Fin M → ℝ) R ×ˢ K)) :=
    (isCompact_closedBall 0 R |>.prod hK).inter_left hC
  have hp0' : p0 ∈ C ∩ (Metric.closedBall (0 : Fin M → ℝ) R ×ˢ K) :=
    ⟨hp0, by simp [R], hCK p0 hp0⟩
  have hf : Continuous (fun p : (Fin M → ℝ) × E => P.GE p.1 + g p.2) := by
    simp only [GE, Standalone.M7FundDecisionEtfsAtZero.GE]; fun_prop
  obtain ⟨p, hp, hmax⟩ := hKc.exists_isMaxOn ⟨p0, hp0'⟩ hf.continuousOn
  refine ⟨p, hp.1, fun q hq => ?_⟩
  by_cases hin : ‖q.1‖ ≤ R
  · exact hmax ⟨hq, by simpa [mem_closedBall_zero_iff] using hin, hCK q hq⟩
  · push Not at hin
    have h1 := hR0 q.1 (lt_of_le_of_lt (le_max_left _ _) hin)
    have h2 := hgmax q.2 (hCK q hq)
    have h3 := hmax hp0'
    simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
    linarith

end Exist


/-! ### Sets -/

section Sets

variable (hS : P.Setting)
include hS

omit hS in
lemma box_closed : IsClosed P.box := by
  have : P.box = Set.Icc 0 P.xbar := by ext x; simp [box, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this]; exact isClosed_Icc

omit hS in
lemma box_compact : IsCompact P.box := by
  have : P.box = Set.Icc 0 P.xbar := by ext x; simp [box, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this]; exact isCompact_Icc

omit hS in
lemma box_convex : Convex ℝ P.box := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith [(hx i).1, (hy i).1]
  · have hc : P.xbar i = a * P.xbar i + b * P.xbar i := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hx i).2 ha, mul_le_mul_of_nonneg_left (hy i).2 hb]

lemma zero_mem_box : (0 : Fin N → ℝ) ∈ P.box := fun i => ⟨le_rfl, (hS.2.2.2.2.2 i).2.2.1.le⟩

omit hS in
lemma Feas_closed : IsClosed P.Feas := by
  have h1 : IsClosed {p : (Fin M → ℝ) × (Fin N → ℝ) | p.2 ∈ P.box} :=
    box_closed.preimage continuous_snd
  have h2 : IsClosed {p : (Fin M → ℝ) × (Fin N → ℝ) | P.Q *ᵥ p.2 ≤ p.1} :=
    isClosed_le (by fun_prop) continuous_fst
  exact h1.inter h2

omit hS in
lemma WF_convex : Convex ℝ P.WF := by
  rintro w ⟨x, hx, hxw⟩ v ⟨y, hy, hyv⟩ a b ha hb hab
  refine ⟨a • x + b • y, box_convex hx hy ha hb hab, ?_⟩
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hxw j) ha, mul_le_mul_of_nonneg_left (hyv j) hb]

omit hS in
lemma WF_up {w d : Fin M → ℝ} (hw : w ∈ P.WF) (hd : 0 ≤ d) : w + d ∈ P.WF := by
  obtain ⟨x, hx, hxw⟩ := hw
  exact ⟨x, hx, fun j => by have := hd j; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; linarith [hxw j]⟩

omit hS in
lemma mem_Feas {w : Fin M → ℝ} {x : Fin N → ℝ} (hx : x ∈ P.box) (hw : P.Q *ᵥ x ≤ w) :
    (w, x) ∈ P.Feas := ⟨hx, hw⟩

theorem existence_of : (∃ ws ∈ P.WF, IsMaxOn P.GE P.WF ws ∧ ∀ w ∈ P.WF, IsMaxOn P.GE P.WF w → w = ws) ∧
    (∀ ws ∈ P.WF, ∃ x ∈ P.fibre ws, IsMaxOn P.H (P.fibre ws) x) ∧
    (∃ p ∈ P.Feas, IsMaxOn P.Jobj P.Feas p) := by
  have h00 : ((0 : Fin M → ℝ), (0 : Fin N → ℝ)) ∈ P.Feas :=
    ⟨zero_mem_box hS, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp, hmax⟩ := exists_max_prod hS box_compact (g := fun _ => (0 : ℝ)) continuous_const
      Feas_closed (fun p hp => hp.1) h00
    refine ⟨p.1, ⟨p.2, hp.1, hp.2⟩, fun w ⟨x, hx, hxw⟩ => ?_, fun w hw hwmax => ?_⟩
    · have := hmax (show (w, x) ∈ P.Feas from ⟨hx, hxw⟩)
      simpa using this
    · by_contra hne
      have hmid := GE_mid hS hne
      have hmem : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • p.1 ∈ P.WF :=
        WF_convex hw ⟨p.2, hp.1, hp.2⟩ (by norm_num) (by norm_num) (by norm_num)
      have h1 := hwmax hmem
      have h2 := hwmax ⟨p.2, hp.1, hp.2⟩
      have h3 : P.GE w ≤ P.GE p.1 := by
        have := hmax (show (w, Classical.choose hw) ∈ P.Feas from
          ⟨(Classical.choose_spec hw).1, (Classical.choose_spec hw).2⟩)
        simpa using this
      simp only [Set.mem_ofPred_eq] at h1 h2
      linarith
  · intro ws ⟨x0, hx0, hx0w⟩
    have hK : IsCompact (P.fibre ws) := by
      have : P.fibre ws = P.box ∩ {x | P.Q *ᵥ x ≤ ws} := rfl
      rw [this]
      exact box_compact.inter_right (isClosed_le (by fun_prop) continuous_const)
    have hc : Continuous P.H := by unfold H cA; fun_prop
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn ⟨x0, hx0, hx0w⟩ hc.continuousOn
    exact ⟨x, hx, hmax⟩
  · have hc : Continuous P.H := by unfold H cA; fun_prop
    obtain ⟨p, hp, hmax⟩ := exists_max_prod hS box_compact hc Feas_closed (fun p hp => hp.1) h00
    exact ⟨p, hp, hmax⟩

end Sets

theorem existence : Existence := fun _ _ _ hS => existence_of hS

/-! ### Part 1 -/

/-- If `A ≤ B + K t` for every `t > 0`, then `A ≤ B`. -/
lemma le_of_lin {A B K : ℝ} (h : ∀ t : ℝ, 0 < t → A ≤ B + K * t) : A ≤ B := by
  by_contra hlt; push Not at hlt
  set t := (A - B) / (2 * (|K| + 1))
  have ht : 0 < t := div_pos (by linarith) (by positivity)
  have h1 := h t ht
  have h2 : K * t ≤ |K| * t := mul_le_mul_of_nonneg_right (le_abs_self K) ht.le
  have h3 : |K| * t < A - B := by
    have e : |K| * t = (A - B) * (|K| / (2 * (|K| + 1))) := by simp only [t]; ring
    rw [e]
    have : |K| / (2 * (|K| + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [abs_nonneg K]
    nlinarith
  linarith

/-- The same with the bound holding only for small `t`. -/
lemma le_of_lin' {A B K δ : ℝ} (hδ : 0 < δ) (h : ∀ t : ℝ, 0 < t → t < δ → A ≤ B + K * t) : A ≤ B := by
  refine le_of_lin (K := |K| + (|A| + |B|) / δ + 1) fun t ht => ?_
  rcases lt_or_ge t δ with hlt | hge
  · have := h t ht hlt
    have : K * t ≤ (|K| + (|A| + |B|) / δ + 1) * t :=
      mul_le_mul_of_nonneg_right (by have := le_abs_self K; have : 0 ≤ (|A| + |B|) / δ := by positivity
                                     linarith) ht.le
    linarith
  · have h1 : (|A| + |B|) / δ * t ≥ |A| + |B| := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hδ]
      nlinarith [abs_nonneg A, abs_nonneg B]
    have := le_abs_self A; have := neg_abs_le B
    nlinarith [abs_nonneg K]

section Part1

variable (hS : P.Setting)
include hS

lemma zeta_nonneg {ws : Fin M → ℝ} (hws : ws ∈ P.WF) (hmax : IsMaxOn P.GE P.WF ws) (j : Fin M) :
    0 ≤ P.zeta ws j := by
  refine le_of_lin (K := P.gamma / 2 * P.Sig j j) fun t ht => ?_
  have hmem := WF_up (d := t • Pi.single j 1) hws (fun i => by
    by_cases h : i = j <;> simp [h, ht.le])
  have h1 := hmax hmem
  simp only [Set.mem_ofPred_eq] at h1
  rw [GE_line hS] at h1
  have e1 : P.zeta ws ⬝ᵥ Pi.single j 1 = P.zeta ws j := by simp [dotProduct_single]
  have e2 : (Pi.single j (1 : ℝ)) ⬝ᵥ (P.Sig *ᵥ Pi.single j 1) = P.Sig j j := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [e1, e2] at h1
  have : 0 ≤ t * (P.zeta ws j + P.gamma / 2 * P.Sig j j * t) := by nlinarith
  have := nonneg_of_mul_nonneg_right (by linarith [this] : 0 ≤ t * (P.zeta ws j + P.gamma / 2 * P.Sig j j * t)) ht
  linarith

end Part1

/-- The fund marginals `g_i = α̂_i - γ(Vx)_i - r_i'z`. -/
def gv (P : TS M N) (x : Fin N → ℝ) (z : Fin M → ℝ) : Fin N → ℝ :=
  fun i => P.alt i - P.gamma * (P.V *ᵥ x) i - (P.Qᵀ *ᵥ z) i

/-- `L_z(x) = H(x) - z'Qx`. -/
def Lf (P : TS M N) (z : Fin M → ℝ) (x : Fin N → ℝ) : ℝ := P.H x - z ⬝ᵥ (P.Q *ᵥ x)

/-- One fund's trade cost. -/
def ci (P : TS M N) (i : Fin N) (u : ℝ) : ℝ := P.kp i * max u 0 + P.km i * max (-u) 0

lemma cA_eq (u : Fin N → ℝ) : P.cA u = ∑ i, ci P i (u i) := rfl

lemma cA_single (u : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    P.cA (u + t • Pi.single i 1) = P.cA u + (ci P i (u i + t) - ci P i (u i)) := by
  rw [cA_eq, cA_eq, ← sub_eq_iff_eq_add', ← sum_sub_distrib,
    sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma dot_Q (z : Fin M → ℝ) (x : Fin N → ℝ) : z ⬝ᵥ (P.Q *ᵥ x) = (P.Qᵀ *ᵥ z) ⬝ᵥ x := by
  rw [dotProduct_mulVec, mulVec_transpose]

section Moves

variable (hS : P.Setting)
include hS

lemma Lf_move (z : Fin M → ℝ) (x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    Lf P z (x + t • Pi.single i 1) = Lf P z x + t * gv P x z i - t ^ 2 * (P.gamma / 2 * P.V i i) -
      (ci P i (x i - P.xm i + t) - ci P i (x i - P.xm i)) := by
  have hc : x + t • Pi.single i 1 - P.xm = (x - P.xm) + t • Pi.single i 1 := by abel
  simp only [Lf, H, hc, cA_single, Pi.sub_apply, dot_Q]
  have hq : (x + t • Pi.single i 1) ⬝ᵥ (P.V *ᵥ (x + t • Pi.single i 1)) =
      x ⬝ᵥ (P.V *ᵥ x) + 2 * t * (P.V *ᵥ x) i + t ^ 2 * P.V i i := by
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [V_symm hS x (Pi.single i 1)]
    simp only [single_dotProduct, one_mul]
    have : (P.V *ᵥ Pi.single i 1) i = P.V i i := by simp [mulVec, dotProduct, Pi.single_apply]
    rw [this]; ring
  rw [hq]
  simp only [gv, dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
  ring

/-- `H` is concave. -/
lemma H_concave (x y : Fin N → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.H x + t * (P.H y - P.H x) ≤ P.H (x + t • (y - x)) := by
  have hV := hS.2.2.2.2.1 (y - x)
  have hsym := V_symm hS x (y - x)
  have hcost : P.cA (x + t • (y - x) - P.xm) ≤ P.cA (x - P.xm) + t * (P.cA (y - P.xm) - P.cA (x - P.xm)) := by
    simp only [cA_eq, mul_sub, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    have hk := (hS.2.2.2.2.2 i).1
    have hm := (hS.2.2.2.2.2 i).2.1
    simp only [ci, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    set a := x i - P.xm i
    set b := y i - P.xm i
    have e : x i + t * (y i - x i) - P.xm i = (1 - t) * a + t * b := by simp only [a, b]; ring
    rw [e]
    have h1 : max ((1 - t) * a + t * b) 0 ≤ (1 - t) * max a 0 + t * max b 0 :=
      max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0))
        (add_nonneg (mul_nonneg (by linarith) (le_max_right _ _)) (mul_nonneg ht0 (le_max_right _ _)))
    have h2 : max (-((1 - t) * a + t * b)) 0 ≤ (1 - t) * max (-a) 0 + t * max (-b) 0 := by
      have e2 : -((1 - t) * a + t * b) = (1 - t) * (-a) + t * (-b) := by ring
      rw [e2]
      exact max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0))
        (add_nonneg (mul_nonneg (by linarith) (le_max_right _ _)) (mul_nonneg ht0 (le_max_right _ _)))
    nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hm]
  simp only [H] at *
  have hq : (x + t • (y - x)) ⬝ᵥ (P.V *ᵥ (x + t • (y - x))) =
      x ⬝ᵥ (P.V *ᵥ x) + 2 * t * (x ⬝ᵥ (P.V *ᵥ (y - x))) + t ^ 2 * ((y - x) ⬝ᵥ (P.V *ᵥ (y - x))) := by
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← hsym]; ring
  have hy : y = x + (y - x) := by abel
  have hq2 : y ⬝ᵥ (P.V *ᵥ y) = x ⬝ᵥ (P.V *ᵥ x) + 2 * (x ⬝ᵥ (P.V *ᵥ (y - x))) +
      (y - x) ⬝ᵥ (P.V *ᵥ (y - x)) := by
    conv_lhs => rw [hy]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    rw [← hsym]; ring
  have hl : P.alt ⬝ᵥ (x + t • (y - x)) = P.alt ⬝ᵥ x + t * (P.alt ⬝ᵥ y - P.alt ⬝ᵥ x) := by
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  rw [hq, hl, hq2]
  have hγ := hS.1
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - t)) hV) hγ.le]

/-- Coordinate moves from a maximizer of `L_z` over the box give the fund lines. -/
lemma FL_of_max (z : Fin M → ℝ) {x : Fin N → ℝ} (hx : x ∈ P.box)
    (hmax : ∀ y ∈ P.box, Lf P z y ≤ Lf P z x) : P.FundLines x z := by
  intro i
  set g := gv P x z i with hg
  have hk := (hS.2.2.2.2.2 i).1
  have hm := (hS.2.2.2.2.2 i).2.1
  have hcap := (hS.2.2.2.2.2 i).2.2.1
  have hxm0 := (hS.2.2.2.2.2 i).2.2.2.1
  have hxmc := (hS.2.2.2.2.2 i).2.2.2.2
  set K := P.gamma / 2 * P.V i i
  set u := x i - P.xm i
  have hmem : ∀ t : ℝ, 0 ≤ x i + t → x i + t ≤ P.xbar i → x + t • Pi.single i 1 ∈ P.box := by
    intro t h0 h1 j
    by_cases h : j = i
    · subst h; simpa using ⟨h0, h1⟩
    · simp [h]; exact hx j
  have base : ∀ t : ℝ, 0 ≤ x i + t → x i + t ≤ P.xbar i →
      t * g - t ^ 2 * K - (ci P i (u + t) - ci P i u) ≤ 0 := by
    intro t h0 h1
    have := hmax _ (hmem t h0 h1)
    rw [Lf_move hS] at this
    dsimp only [g, K, u]
    linarith
  have ci_pos : ∀ v, 0 ≤ v → ci P i v = P.kp i * v := fun v hv => by
    simp [ci, max_eq_left hv, max_eq_right (by linarith : -v ≤ 0)]
  have ci_neg : ∀ v, v ≤ 0 → ci P i v = P.km i * (-v) := fun v hv => by
    simp [ci, max_eq_right hv, max_eq_left (by linarith : 0 ≤ -v)]
  -- up moves
  have up_pos : x i < P.xbar i → 0 ≤ u → g ≤ P.kp i := fun hc hu =>
    le_of_lin' (K := K) (δ := P.xbar i - x i) (by linarith) fun t ht htd => by
      have hb := base t (by linarith [(hx i).1]) (by linarith)
      rw [ci_pos (u + t) (by linarith), ci_pos u hu] at hb
      have : t * (g - (P.kp i + K * t)) ≤ 0 := by nlinarith
      nlinarith [(mul_nonpos_iff.1 this)]
  have up_neg : x i < P.xbar i → u < 0 → g ≤ -P.km i := fun hc hu =>
    le_of_lin' (K := K) (δ := min (P.xbar i - x i) (-u)) (lt_min (by linarith) (by linarith))
      fun t ht htd => by
      have h1 := lt_of_lt_of_le htd (min_le_left _ _)
      have h2 := lt_of_lt_of_le htd (min_le_right _ _)
      have hb := base t (by linarith [(hx i).1]) (by linarith)
      rw [ci_neg (u + t) (by linarith), ci_neg u hu.le] at hb
      have : t * (g - (-P.km i + K * t)) ≤ 0 := by nlinarith
      nlinarith [(mul_nonpos_iff.1 this)]
  -- down moves
  have dn_neg : 0 < x i → u ≤ 0 → -P.km i ≤ g := fun hc hu =>
    le_of_lin' (K := K) (δ := x i) hc fun t ht htd => by
      have hb := base (-t) (by linarith) (by linarith [(hx i).2])
      rw [ci_neg (u + -t) (by linarith), ci_neg u hu] at hb
      have : t * (-P.km i - (g + K * t)) ≤ 0 := by nlinarith
      nlinarith [(mul_nonpos_iff.1 this)]
  have dn_pos : 0 < x i → 0 < u → P.kp i ≤ g := fun hc hu =>
    le_of_lin' (K := K) (δ := min (x i) u) (lt_min hc hu) fun t ht htd => by
      have h1 := lt_of_lt_of_le htd (min_le_left _ _)
      have h2 := lt_of_lt_of_le htd (min_le_right _ _)
      have hb := base (-t) (by linarith) (by linarith [(hx i).2])
      rw [ci_pos (u + -t) (by linarith), ci_pos u hu.le] at hb
      have : t * (P.kp i - (g + K * t)) ≤ 0 := by nlinarith
      nlinarith [(mul_nonpos_iff.1 this)]
  refine ⟨fun h => ⟨fun hc => le_antisymm (up_pos hc (by linarith)) (dn_pos (by linarith) (by linarith)),
      fun hc => dn_pos (by linarith) (by linarith)⟩,
    fun h => ⟨fun h0 => le_antisymm (up_neg (by linarith) (by linarith)) (dn_neg h0 (by linarith)),
      fun h0 => up_neg (by linarith) (by linarith)⟩,
    fun h => ⟨fun h0 => dn_neg h0 (by linarith), fun hc => up_pos hc (by linarith)⟩⟩

/-- The fund lines make `x` a maximizer of `L_z` over the box (a supergradient argument). -/
lemma max_of_FL (z : Fin M → ℝ) {x : Fin N → ℝ} (hx : x ∈ P.box) (hFL : P.FundLines x z) :
    ∀ y ∈ P.box, Lf P z y ≤ Lf P z x := by
  intro y hy
  set g := gv P x z
  set s : Fin N → ℝ := fun i => if P.xm i < x i then P.kp i else if x i < P.xm i then -P.km i
    else max (-P.km i) (min (g i) (P.kp i))
  have hsub : ∀ i, ci P i (x i - P.xm i) + s i * (y i - x i) ≤ ci P i (y i - P.xm i) := by
    intro i
    have hk := (hS.2.2.2.2.2 i).1
    have hm := (hS.2.2.2.2.2 i).2.1
    have lb1 : ∀ v, P.kp i * v ≤ ci P i v := fun v => by
      simp only [ci]; nlinarith [le_max_left v 0, mul_nonneg hm (le_max_right (-v) 0),
        mul_le_mul_of_nonneg_left (le_max_left v 0) hk]
    have lb2 : ∀ v, -P.km i * v ≤ ci P i v := fun v => by
      simp only [ci]; nlinarith [le_max_left (-v) 0, mul_nonneg hk (le_max_right v 0),
        mul_le_mul_of_nonneg_left (le_max_left (-v) 0) hm]
    simp only [s]
    split_ifs with h1 h2
    · have : ci P i (x i - P.xm i) = P.kp i * (x i - P.xm i) := by
        simp [ci, max_eq_left (by linarith : 0 ≤ x i - P.xm i), max_eq_right (by linarith : P.xm i - x i ≤ 0)]
      rw [this]; have := lb1 (y i - P.xm i); nlinarith
    · have : ci P i (x i - P.xm i) = -P.km i * (x i - P.xm i) := by
        simp [ci, max_eq_right (by linarith : x i - P.xm i ≤ 0), max_eq_left (by linarith : 0 ≤ P.xm i - x i)]
        ring
      rw [this]; have := lb2 (y i - P.xm i); nlinarith
    · have he : x i = P.xm i := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
      rw [he, sub_self, show ci P i 0 = 0 by simp [ci], zero_add]
      set c := max (-P.km i) (min (g i) (P.kp i))
      have hc1 : -P.km i ≤ c := le_max_left _ _
      have hc2 : c ≤ P.kp i := max_le (by linarith) (min_le_right _ _)
      rcases le_total 0 (y i - P.xm i) with hv | hv
      · have := lb1 (y i - P.xm i); nlinarith
      · have := lb2 (y i - P.xm i); nlinarith
  have hsign : ∀ i, (g i - s i) * (y i - x i) ≤ 0 := by
    intro i
    have hk := (hS.2.2.2.2.2 i).1
    have hm := (hS.2.2.2.2.2 i).2.1
    obtain ⟨hA, hB, hC⟩ := hFL i
    have hgi : g i = P.alt i - P.gamma * (P.V *ᵥ x) i - (P.Qᵀ *ᵥ z) i := rfl
    rw [← hgi] at hA hB hC
    have hy0 := (hy i).1; have hyc := (hy i).2; have hx0 := (hx i).1; have hxc := (hx i).2
    simp only [s]
    split_ifs with h1 h2
    · rcases lt_or_eq_of_le hxc with hc | hc
      · rw [(hA h1).1 hc, sub_self, zero_mul]
      · have := (hA h1).2 hc; nlinarith
    · rcases lt_or_eq_of_le hx0 with hc | hc
      · rw [(hB h2).1 hc, sub_self, zero_mul]
      · have := (hB h2).2 hc.symm; nlinarith
    · have he : x i = P.xm i := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
      obtain ⟨hC1, hC2⟩ := hC he
      rcases lt_or_eq_of_le hx0 with h0 | h0
      · rcases lt_or_eq_of_le hxc with hc | hc
        · have e : max (-P.km i) (min (g i) (P.kp i)) = g i := by
            rw [min_eq_left (hC2 hc), max_eq_right (hC1 h0)]
          rw [e, sub_self, zero_mul]
        · have e : max (-P.km i) (min (g i) (P.kp i)) = min (g i) (P.kp i) :=
            max_eq_right (le_min (hC1 h0) (by linarith))
          rw [e]
          have : 0 ≤ g i - min (g i) (P.kp i) := by linarith [min_le_left (g i) (P.kp i)]
          nlinarith
      · have hcap := (hS.2.2.2.2.2 i).2.2.1
        have hlt : x i < P.xbar i := by linarith
        have e : max (-P.km i) (min (g i) (P.kp i)) = max (-P.km i) (g i) := by
          rw [min_eq_left (hC2 hlt)]
        rw [e]
        have : g i - max (-P.km i) (g i) ≤ 0 := by linarith [le_max_right (-P.km i) (g i)]
        nlinarith
  -- the smooth part
  have hsmooth : Lf P z y - Lf P z x ≤ ∑ i, g i * (y i - x i) -
      (P.cA (y - P.xm) - P.cA (x - P.xm)) := by
    have hV := hS.2.2.2.2.1 (y - x)
    have hsym := V_symm hS x (y - x)
    have hy : y = x + (y - x) := by abel
    have hq : y ⬝ᵥ (P.V *ᵥ y) = x ⬝ᵥ (P.V *ᵥ x) + 2 * (x ⬝ᵥ (P.V *ᵥ (y - x))) +
        (y - x) ⬝ᵥ (P.V *ᵥ (y - x)) := by
      conv_lhs => rw [hy]
      simp only [mulVec_add, dotProduct_add, add_dotProduct]
      rw [← hsym]; ring
    have hg : ∑ i, g i * (y i - x i) = P.alt ⬝ᵥ (y - x) - P.gamma * (x ⬝ᵥ (P.V *ᵥ (y - x))) -
        (P.Qᵀ *ᵥ z) ⬝ᵥ (y - x) := by
      simp only [g, gv, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      rw [hsym, dotProduct_comm (y - x) (P.V *ᵥ x)]
      simp only [dotProduct, Pi.sub_apply]
    simp only [Lf, H, dot_Q]
    rw [hq, hg]
    simp only [dotProduct_sub]
    have hγ := hS.1
    nlinarith [mul_nonneg hγ.le hV]
  have hcost : P.cA (y - P.xm) - P.cA (x - P.xm) ≥ ∑ i, s i * (y i - x i) := by
    simp only [cA_eq, ← sum_sub_distrib, Pi.sub_apply]
    exact sum_le_sum fun i _ => by linarith [hsub i]
  have hsum : ∑ i, (g i - s i) * (y i - x i) ≤ 0 := sum_nonpos fun i _ => hsign i
  simp only [sub_mul, sum_sub_distrib] at hsum
  linarith

lemma zeta_comp {ws : Fin M → ℝ} (hws : ws ∈ P.WF) (hmax : IsMaxOn P.GE P.WF ws) {x2 : Fin N → ℝ}
    (hx2 : x2 ∈ P.fibre ws) (j : Fin M) (hlt : (P.Q *ᵥ x2) j < ws j) : P.zeta ws j = 0 := by
  refine le_antisymm ?_ (zeta_nonneg hS hws hmax j)
  refine le_of_lin' (K := P.gamma / 2 * P.Sig j j) (δ := ws j - (P.Q *ᵥ x2) j) (by linarith)
    fun t ht htd => ?_
  have hmem : ws + (-t) • Pi.single j 1 ∈ P.WF := ⟨x2, hx2.1, fun i => by
    by_cases h : i = j
    · subst h; simp; linarith
    · simp [h]; exact hx2.2 i⟩
  have h1 := hmax hmem
  simp only [Set.mem_ofPred_eq] at h1
  rw [GE_line hS] at h1
  have e1 : P.zeta ws ⬝ᵥ Pi.single j 1 = P.zeta ws j := by simp [dotProduct_single]
  have e2 : (Pi.single j (1 : ℝ)) ⬝ᵥ (P.Sig *ᵥ Pi.single j 1) = P.Sig j j := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [e1, e2] at h1
  have : t * (P.zeta ws j - (0 + P.gamma / 2 * P.Sig j j * t)) ≤ 0 := by nlinarith
  nlinarith [(mul_nonpos_iff.1 this)]

/-- Exactness iff `x₂` maximizes `L_{ζ*}` over the box. -/
lemma exact_iff {ws : Fin M → ℝ} (hws : ws ∈ P.WF) (hmax : IsMaxOn P.GE P.WF ws) {x2 : Fin N → ℝ}
    (hx2 : x2 ∈ P.fibre ws) {pJ : (Fin M → ℝ) × (Fin N → ℝ)} (hpJ : pJ ∈ P.Feas)
    (hJ : IsMaxOn P.Jobj P.Feas pJ) :
    P.GE ws + P.H x2 = P.Jobj pJ ↔ ∀ y ∈ P.box, Lf P (P.zeta ws) y ≤ Lf P (P.zeta ws) x2 := by
  set ζ := P.zeta ws
  have hT : P.GE ws + P.H x2 ≤ P.Jobj pJ := hJ (show (ws, x2) ∈ P.Feas from ⟨hx2.1, hx2.2⟩)
  constructor
  · intro heq y hy
    set d := y - x2
    refine le_of_lin' (K := P.gamma / 2 * ((P.Q *ᵥ d) ⬝ᵥ (P.Sig *ᵥ (P.Q *ᵥ d)))) one_pos fun t ht ht1 => ?_
    have hxt : x2 + t • d ∈ P.box := by
      have := box_convex hx2.1 hy (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
      have e : (1 - t) • x2 + t • y = x2 + t • d := by simp only [d]; module
      rwa [e] at this
    have hfe : (ws + t • (P.Q *ᵥ d), x2 + t • d) ∈ P.Feas := ⟨hxt, by
      rw [mulVec_add, mulVec_smul]; intro j; simp only [Pi.add_apply, Pi.smul_apply]
      linarith [hx2.2 j]⟩
    have h1 := hJ hfe
    simp only [Set.mem_ofPred_eq] at h1
    rw [← heq] at h1
    simp only [Jobj] at h1
    rw [GE_line hS] at h1
    have h2 := H_concave hS x2 y ht.le ht1.le
    have hQ : ζ ⬝ᵥ (P.Q *ᵥ d) = ζ ⬝ᵥ (P.Q *ᵥ y) - ζ ⬝ᵥ (P.Q *ᵥ x2) := by
      simp only [d, mulVec_sub, dotProduct_sub]
    simp only [Lf]
    have : t * (P.H y - ζ ⬝ᵥ (P.Q *ᵥ y) - (P.H x2 - ζ ⬝ᵥ (P.Q *ᵥ x2)) -
        (P.gamma / 2 * ((P.Q *ᵥ d) ⬝ᵥ (P.Sig *ᵥ (P.Q *ᵥ d))) * t)) ≤ 0 := by
      nlinarith
    nlinarith [(mul_nonpos_iff.1 this)]
  · intro hL
    refine le_antisymm hT ?_
    have hz0 := zeta_nonneg hS hws hmax
    have hcomp : ζ ⬝ᵥ (ws - P.Q *ᵥ x2) = 0 := by
      refine sum_eq_zero fun j _ => ?_
      rcases lt_or_eq_of_le (hx2.2 j) with h | h
      · rw [show ζ j = 0 from zeta_comp hS hws hmax hx2 j h, zero_mul]
      · simp [h]
    obtain ⟨hpx, hpw⟩ := hpJ
    have h1 : 0 ≤ ζ ⬝ᵥ (pJ.1 - P.Q *ᵥ pJ.2) :=
      sum_nonneg fun j _ => mul_nonneg (hz0 j) (by simp only [Pi.sub_apply]; linarith [hpw j])
    have h2 := GE_line hS ws (pJ.1 - ws) 1
    rw [one_smul, add_sub_cancel] at h2
    have h3 := hL pJ.2 hpx
    have hSn := S_nonneg hS (pJ.1 - ws)
    have hγ := hS.1
    simp only [Lf] at h3
    simp only [Jobj, dotProduct_sub] at *
    nlinarith

omit hS in
/-- Stage 1's exposure is optimal for stage 2's by-product: `V_E(Qx₂) = G_E(w*)`. -/
lemma VE_fibre {ws : Fin M → ℝ} (hmax : IsMaxOn P.GE P.WF ws) {x2 : Fin N → ℝ}
    (hx2 : x2 ∈ P.fibre ws) : P.VE (P.Q *ᵥ x2) = P.GE ws :=
  IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ hx2.2, by
    rintro _ ⟨w, hw, rfl⟩; exact hmax ⟨x2, hx2.1, hw⟩⟩

theorem stageSlacks_of {ws : Fin M → ℝ} {x2 : Fin N → ℝ} {pJ : (Fin M → ℝ) × (Fin N → ℝ)}
    (hws : ws ∈ P.WF) (hmax : IsMaxOn P.GE P.WF ws) (hx2 : x2 ∈ P.fibre ws)
    (hpJ : pJ ∈ P.Feas) (hJ : IsMaxOn P.Jobj P.Feas pJ) :
    (∀ j, 0 ≤ P.zeta ws j) ∧ (∀ j, (P.Q *ᵥ x2) j < ws j → P.zeta ws j = 0) ∧
      (P.GE ws + P.H x2 = P.Jobj pJ ↔ P.FundLines x2 (P.zeta ws)) ∧ P.VE (P.Q *ᵥ x2) = P.GE ws :=
  ⟨zeta_nonneg hS hws hmax, zeta_comp hS hws hmax hx2, (exact_iff hS hws hmax hx2 hpJ hJ).trans
    ⟨fun h => FL_of_max hS _ hx2.1 h, fun h => max_of_FL hS _ hx2.1 h⟩, VE_fibre hmax hx2⟩

end Moves

theorem stageSlacks : StageSlacks := fun _ _ _ hS _ _ _ hws hmax hx2 _ hpJ hJ =>
  stageSlacks_of hS hws hmax hx2 hpJ hJ



/-! ### Part 3 -/

section Part3

variable (hS : P.Setting)
include hS

lemma S_inj {u v : Fin M → ℝ} (h : P.gamma • (P.Sig *ᵥ u) = P.gamma • (P.Sig *ᵥ v)) : u = v := by
  by_contra hne
  have hpos := hS.2.2.1 (u - v) (sub_ne_zero.2 hne)
  have h0 : P.Sig *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    have hγ : P.gamma ≠ 0 := hS.1.ne'
    have := congrArg (fun w => P.gamma⁻¹ • w) h
    simp only [smul_smul, inv_mul_cancel₀ hγ, one_smul] at this
    rw [this, sub_self]
  rw [h0, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

lemma normal_cone {ws : Fin M → ℝ} (hws : ws ∈ P.WF) (hmax : IsMaxOn P.GE P.WF ws) :
    ∀ w ∈ P.WF, (P.mu - P.gamma • (P.Sig *ᵥ ws)) ⬝ᵥ (w - ws) ≤ 0 := by
  intro w hw
  have hnu : P.mu - P.gamma • (P.Sig *ᵥ ws) = -P.zeta ws := by simp [zeta]
  rw [hnu, neg_dotProduct, neg_nonpos]
  refine le_of_lin' (K := P.gamma / 2 * ((w - ws) ⬝ᵥ (P.Sig *ᵥ (w - ws)))) one_pos fun t ht ht1 => ?_
  have hmem : ws + t • (w - ws) ∈ P.WF := by
    have := WF_convex hws hw (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
    have e : (1 - t) • ws + t • w = ws + t • (w - ws) := by module
    rwa [e] at this
  have h1 := hmax hmem
  simp only [Set.mem_ofPred_eq] at h1
  rw [GE_line hS] at h1
  have : t * (0 - (P.zeta ws ⬝ᵥ (w - ws) + P.gamma / 2 * ((w - ws) ⬝ᵥ (P.Sig *ᵥ (w - ws))) * t)) ≤ 0 := by
    nlinarith
  nlinarith [(mul_nonpos_iff.1 this)]

omit hS in
lemma Feas_convex : Convex ℝ P.Feas := by
  rintro p ⟨hpx, hpw⟩ q ⟨hqx, hqw⟩ a b ha hb hab
  refine ⟨box_convex hpx hqx ha hb hab, ?_⟩
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add, mulVec_smul]
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hpw j) ha, mul_le_mul_of_nonneg_left (hqw j) hb]

/-- The joint objective is strictly concave in the exposure. -/
lemma Jobj_mid {p q : (Fin M → ℝ) × (Fin N → ℝ)} (hne : p.1 ≠ q.1) :
    (P.Jobj p + P.Jobj q) / 2 < P.Jobj ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) := by
  have h1 := GE_mid hS hne
  have h2 := H_concave hS p.2 q.2 (t := 1 / 2) (by norm_num) (by norm_num)
  have e : p.2 + (1 / 2 : ℝ) • (q.2 - p.2) = (1 / 2 : ℝ) • p.2 + (1 / 2 : ℝ) • q.2 := by module
  rw [e] at h2
  simp only [Jobj, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  linarith

end Part3


/-! ### Part 2: one fund -/

section OneFund

variable {P : TS M 1} (hS : P.Setting)
include hS

omit hS in
lemma Q_one (x : Fin 1 → ℝ) : P.Q *ᵥ x = x 0 • P.r := by
  funext j; simp [mulVec, dotProduct, r, mul_comm]

omit hS in
lemma cst_eta (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
  funext i; rw [Subsingleton.elim i 0]

omit hS in
lemma mem_box1 (y : ℝ) : (fun _ => y : Fin 1 → ℝ) ∈ P.box ↔ 0 ≤ y ∧ y ≤ P.xbar 0 := by
  constructor
  · intro h; exact h 0
  · intro h i; rw [Subsingleton.elim i 0]; exact h

/-- `G_E` attains its maximum on any nonempty closed set. -/
lemma exists_max_set {C : Set (Fin M → ℝ)} (hC : IsClosed C) {w0 : Fin M → ℝ} (h0 : w0 ∈ C) :
    ∃ w ∈ C, IsMaxOn P.GE C w := by
  have hC' : IsClosed {p : (Fin M → ℝ) × ℝ | p.1 ∈ C ∧ p.2 = 0} :=
    (hC.preimage continuous_fst).inter (isClosed_eq continuous_snd continuous_const)
  obtain ⟨p, hp, hmax⟩ := exists_max_prod hS (isCompact_singleton (x := (0 : ℝ)))
    (g := fun _ => (0 : ℝ)) continuous_const hC' (fun p hp => hp.2) (p0 := (w0, 0)) ⟨h0, rfl⟩
  refine ⟨p.1, hp.1, fun w hw => ?_⟩
  have := hmax (show (w, (0 : ℝ)) ∈ {p : (Fin M → ℝ) × ℝ | p.1 ∈ C ∧ p.2 = 0} from ⟨hw, rfl⟩)
  simpa using this

/-- `V_E(q)` is attained. -/
lemma VE_attain (q : Fin M → ℝ) : ∃ w, q ≤ w ∧ IsMaxOn P.GE {w | q ≤ w} w ∧ P.VE q = P.GE w := by
  obtain ⟨w, hw, hmax⟩ := exists_max_set hS (isClosed_le continuous_const continuous_id)
    (le_refl q)
  refine ⟨w, hw, hmax, ?_⟩
  exact (IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ hw, by rintro _ ⟨v, hv, rfl⟩; exact hmax hv⟩)

lemma VE_ge (q : Fin M → ℝ) {w : Fin M → ℝ} (hw : q ≤ w) : P.GE w ≤ P.VE q := by
  obtain ⟨v, -, hmax, hV⟩ := VE_attain hS q
  rw [hV]; exact hmax hw

/-- `G_E` is concave along segments. -/
lemma GE_concave (w v : Fin M → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.GE w + t * (P.GE v - P.GE w) ≤ P.GE (w + t • (v - w)) := by
  have h1 := GE_line hS w (v - w) t
  have h2 := GE_line hS w (v - w) 1
  rw [one_smul, add_sub_cancel] at h2
  have hn := S_nonneg hS (v - w)
  have hγ := hS.1
  rw [h1, h2]
  nlinarith [mul_nonneg (mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - t)) (mul_nonneg hγ.le hn)]

omit hS in
lemma xlo_le_iff (w : Fin M → ℝ) (y : ℝ) :
    P.xlo w ≤ y ↔ 0 ≤ y ∧ ∀ j, P.r j < 0 → P.r j * y ≤ w j := by
  simp only [xlo, Finset.max'_le_iff, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨h 0 (Or.inl rfl), fun j hj => ?_⟩
    have := h (w j / P.r j) (Or.inr ⟨j, hj, rfl⟩)
    rwa [div_le_iff_of_neg hj, mul_comm] at this
  · rintro ⟨h0, h⟩ z (rfl | ⟨j, hj, rfl⟩)
    · exact h0
    · rw [div_le_iff_of_neg hj, mul_comm]; exact h j hj

omit hS in
lemma le_xhi_iff (w : Fin M → ℝ) (y : ℝ) :
    y ≤ P.xhi w ↔ y ≤ P.xbar 0 ∧ ∀ j, 0 < P.r j → P.r j * y ≤ w j := by
  simp only [xhi, Finset.le_min'_iff, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨h _ (Or.inl rfl), fun j hj => ?_⟩
    have := h (w j / P.r j) (Or.inr ⟨j, hj, rfl⟩)
    rwa [le_div_iff₀ hj, mul_comm] at this
  · rintro ⟨h0, h⟩ z (rfl | ⟨j, hj, rfl⟩)
    · exact h0
    · rw [le_div_iff₀ hj, mul_comm]; exact h j hj

omit hS in
/-- The interval form of `x r ≤ w` on the box. -/
lemma interval_iff (w : Fin M → ℝ) (hw0 : ∀ j, P.r j = 0 → 0 ≤ w j) (y : ℝ) :
    (0 ≤ y ∧ y ≤ P.xbar 0 ∧ y • P.r ≤ w) ↔ P.xlo w ≤ y ∧ y ≤ P.xhi w := by
  rw [xlo_le_iff, le_xhi_iff]
  constructor
  · rintro ⟨h0, hc, hw⟩
    exact ⟨⟨h0, fun j _ => by have := hw j; simpa [mul_comm] using this⟩,
      ⟨hc, fun j _ => by have := hw j; simpa [mul_comm] using this⟩⟩
  · rintro ⟨⟨h0, hlo⟩, ⟨hc, hhi⟩⟩
    refine ⟨h0, hc, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases lt_trichotomy (P.r j) 0 with h | h | h
    · rw [mul_comm]; exact hlo j h
    · rw [h, mul_zero]; exact hw0 j h
    · rw [mul_comm]; exact hhi j h

omit hS in
lemma WF_r0 {w : Fin M → ℝ} (hw : w ∈ P.WF) : ∀ j, P.r j = 0 → 0 ≤ w j := by
  obtain ⟨x, -, hx⟩ := hw
  intro j hj
  have := hx j
  rw [Q_one] at this
  simpa [hj] using this

omit hS in
lemma fibre_iff {w : Fin M → ℝ} (hw : w ∈ P.WF) (x : Fin 1 → ℝ) :
    x ∈ P.fibre w ↔ P.xlo w ≤ x 0 ∧ x 0 ≤ P.xhi w := by
  rw [← interval_iff w (WF_r0 hw)]
  constructor
  · rintro ⟨hb, hq⟩; rw [Q_one] at hq; exact ⟨(hb 0).1, (hb 0).2, hq⟩
  · rintro ⟨h0, hc, hq⟩
    refine ⟨?_, by rw [Q_one]; exact hq⟩
    rw [cst_eta x]; exact (mem_box1 _).2 ⟨h0, hc⟩

omit hS in
/-- The one-fund `H`. -/
lemma H1 (y : ℝ) : P.H (fun _ => y) = P.alt 0 * y - P.gamma / 2 * P.V 0 0 * y ^ 2 -
    (P.kp 0 * max (y - P.xm 0) 0 + P.km 0 * max (-(y - P.xm 0)) 0) := by
  simp [H, cA, dotProduct, mulVec]; ring

/-- The clipped band solution is the unique maximizer of the one-fund `H` on `[a, b]`. -/
lemma H1_clip (hv : 0 < P.V 0 0) {a b : ℝ} (hab : a ≤ b) :
    (a ≤ clip P.xf a b ∧ clip P.xf a b ≤ b) ∧
    (∀ y, a ≤ y → y ≤ b → P.H (fun _ => y) ≤ P.H (fun _ => clip P.xf a b)) ∧
    ∀ c, a ≤ c → c ≤ b → (∀ y, a ≤ y → y ≤ b → P.H (fun _ => y) ≤ P.H (fun _ => c)) →
      c = clip P.xf a b := by
  have hγ := hS.1
  have hk := (hS.2.2.2.2.2 0).1
  have hm := (hS.2.2.2.2.2 0).2.1
  set k := P.gamma * P.V 0 0 with hkdef
  have hkpos : 0 < k := mul_pos hγ hv
  set lo' := (P.alt 0 - P.kp 0) / k
  set hi' := (P.alt 0 + P.km 0) / k
  have hlh : lo' ≤ hi' := div_le_div_of_nonneg_right (by linarith) hkpos.le
  set c := clip P.xf a b
  have hc1 : a ≤ c := le_min (le_max_right _ _) hab
  have hc2 : c ≤ b := min_le_right _ _
  have hcb : c < b → P.xf ≤ c := fun h => by
    show P.xf ≤ min (max P.xf a) b
    rcases le_total (max P.xf a) b with h' | h'
    · rw [min_eq_left h']; exact le_max_left _ _
    · have : c = b := min_eq_right h'
      linarith
  have hca : a < c → c ≤ P.xf := fun h => by
    show min (max P.xf a) b ≤ P.xf
    rcases le_total a P.xf with h' | h'
    · rw [max_eq_left h']; exact min_le_left _ _
    · have : c ≤ a := by
        show min (max P.xf a) b ≤ a
        rw [max_eq_right h']; exact min_le_left _ _
      linarith
  -- the supergradient `s` at `c`, with `s(y - c) ≤ 0` on `[a, b]`
  set q' := P.alt 0 - k * c
  set σ := if P.xm 0 < c then P.kp 0 else if c < P.xm 0 then -P.km 0 else max (-P.km 0) (min q' (P.kp 0))
  have hxf : P.xf = min (max (P.xm 0) lo') hi' := rfl
  have hsign1 : c < b → q' - σ ≤ 0 := by
    intro hlt
    have hf := hcb hlt
    simp only [σ]
    split_ifs with h1 h2
    · -- `c > x⁻`: `xf ≤ c` forces `lo' ≤ c`
      have : lo' ≤ c := by
        by_contra hh; push Not at hh
        have : P.xf = lo' ∨ P.xf = hi' := by
          rw [hxf, max_eq_right (by linarith)]; rcases le_total lo' hi' with h | h
          · left; exact min_eq_left h
          · right; exact min_eq_right h
        rcases this with h | h <;> linarith
      have : q' - P.kp 0 = k * (lo' - c) := by simp only [q', lo']; field_simp; ring
      nlinarith
    · have : hi' ≤ c ∨ True := Or.inr trivial
      have hxfc : P.xf ≤ c := hf
      have hhi : hi' ≤ c := by
        by_contra hh; push Not at hh
        have : c < P.xf := by
          rw [hxf]; exact lt_min (lt_of_lt_of_le h2 (le_max_left _ _)) hh
        linarith
      have : q' + P.km 0 = k * (hi' - c) := by simp only [q', hi']; field_simp; ring
      nlinarith
    · have : max (-P.km 0) (min q' (P.kp 0)) ≥ min q' (P.kp 0) := le_max_right _ _
      have hq : q' ≤ P.kp 0 := by
        have he : c = P.xm 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
        have : lo' ≤ c := by
          by_contra hh; push Not at hh
          have : c < P.xf := by
            rw [hxf, he]
            exact lt_min (lt_max_of_lt_right (he ▸ hh)) (lt_of_lt_of_le (he ▸ hh) hlh)
          linarith
        have : q' - P.kp 0 = k * (lo' - c) := by simp only [q', lo']; field_simp; ring
        nlinarith
      rw [min_eq_left hq] at this ⊢
      linarith
  have hsign2 : a < c → 0 ≤ q' - σ := by
    intro hlt
    have hf := hca hlt
    simp only [σ]
    split_ifs with h1 h2
    · have : c ≤ lo' := by
        have : c ≤ max (P.xm 0) lo' := le_trans hf (min_le_left _ _)
        rcases le_total (P.xm 0) lo' with h | h
        · rwa [max_eq_right h] at this
        · rw [max_eq_left h] at this; linarith
      have : q' - P.kp 0 = k * (lo' - c) := by simp only [q', lo']; field_simp; ring
      nlinarith
    · have : c ≤ hi' := le_trans hf (min_le_right _ _)
      have : q' + P.km 0 = k * (hi' - c) := by simp only [q', hi']; field_simp; ring
      nlinarith
    · have he : c = P.xm 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
      have : c ≤ hi' := le_trans hf (min_le_right _ _)
      have hq : -P.km 0 ≤ q' := by
        have : q' + P.km 0 = k * (hi' - c) := by simp only [q', hi']; field_simp; ring
        nlinarith
      have : max (-P.km 0) (min q' (P.kp 0)) ≤ q' := max_le hq (min_le_left _ _)
      linarith
  -- the supergradient inequality
  have hsup : ∀ y, P.H (fun _ => y) ≤ P.H (fun _ => c) + (q' - σ) * (y - c) := by
    intro y
    rw [H1, H1]
    have hq : P.alt 0 * y - P.gamma / 2 * P.V 0 0 * y ^ 2 ≤
        P.alt 0 * c - P.gamma / 2 * P.V 0 0 * c ^ 2 + q' * (y - c) := by
      simp only [q', k]; nlinarith [sq_nonneg (y - c), mul_pos hγ hv]
    have hcost : P.kp 0 * max (c - P.xm 0) 0 + P.km 0 * max (-(c - P.xm 0)) 0 + σ * (y - c) ≤
        P.kp 0 * max (y - P.xm 0) 0 + P.km 0 * max (-(y - P.xm 0)) 0 := by
      have lb1 : ∀ v, P.kp 0 * v ≤ P.kp 0 * max v 0 + P.km 0 * max (-v) 0 := fun v => by
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left v 0) hk, mul_nonneg hm (le_max_right (-v) 0)]
      have lb2 : ∀ v, -P.km 0 * v ≤ P.kp 0 * max v 0 + P.km 0 * max (-v) 0 := fun v => by
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-v) 0) hm, mul_nonneg hk (le_max_right v 0)]
      simp only [σ]
      split_ifs with h1 h2
      · rw [max_eq_left (by linarith : 0 ≤ c - P.xm 0), max_eq_right (by linarith : -(c - P.xm 0) ≤ 0)]
        have := lb1 (y - P.xm 0); nlinarith
      · rw [max_eq_right (by linarith : c - P.xm 0 ≤ 0), max_eq_left (by linarith : 0 ≤ -(c - P.xm 0))]
        have := lb2 (y - P.xm 0); nlinarith
      · have he : c = P.xm 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
        rw [he, sub_self, neg_zero, max_self, mul_zero, mul_zero, add_zero, zero_add]
        set s0 := max (-P.km 0) (min q' (P.kp 0))
        have hs1 : -P.km 0 ≤ s0 := le_max_left _ _
        have hs2 : s0 ≤ P.kp 0 := max_le (by linarith) (min_le_right _ _)
        rcases le_total 0 (y - P.xm 0) with hv' | hv'
        · have := lb1 (y - P.xm 0); nlinarith
        · have := lb2 (y - P.xm 0); nlinarith
    linarith
  have hmaxc : ∀ y, a ≤ y → y ≤ b → P.H (fun _ => y) ≤ P.H (fun _ => c) := by
    intro y hy1 hy2
    have h := hsup y
    have : (q' - σ) * (y - c) ≤ 0 := by
      rcases lt_trichotomy y c with hy | hy | hy
      · have := hsign2 (lt_of_le_of_lt hy1 hy); nlinarith
      · rw [hy, sub_self, mul_zero]
      · have := hsign1 (lt_of_lt_of_le hy hy2); nlinarith
    linarith
  refine ⟨⟨hc1, hc2⟩, hmaxc, fun d hd1 hd2 hdmax => ?_⟩
  by_contra hne
  -- strict concavity at the midpoint
  have hmid := hdmax ((d + c) / 2) (by linarith) (by linarith)
  have h1 := hmaxc d hd1 hd2
  have h2 := hdmax c hc1 hc2
  rw [H1, H1] at hmid h1 h2
  have hsq : 0 < (d - c) ^ 2 := by have := sub_ne_zero.2 hne; positivity
  have hmx : max ((d + c) / 2 - P.xm 0) 0 ≤ (max (d - P.xm 0) 0 + max (c - P.xm 0) 0) / 2 :=
    max_le (by linarith [le_max_left (d - P.xm 0) 0, le_max_left (c - P.xm 0) 0])
      (by linarith [le_max_right (d - P.xm 0) 0, le_max_right (c - P.xm 0) 0])
  have hmn : max (-((d + c) / 2 - P.xm 0)) 0 ≤ (max (-(d - P.xm 0)) 0 + max (-(c - P.xm 0)) 0) / 2 :=
    max_le (by linarith [le_max_left (-(d - P.xm 0)) 0, le_max_left (-(c - P.xm 0)) 0])
      (by linarith [le_max_right (-(d - P.xm 0)) 0, le_max_right (-(c - P.xm 0)) 0])
  nlinarith [mul_le_mul_of_nonneg_left hmx hk, mul_le_mul_of_nonneg_left hmn hm, mul_pos hγ hv]

omit hS in
lemma H1_mid (hS : P.Setting) (hv : 0 < P.V 0 0) {y z : ℝ} (hne : y ≠ z) :
    (P.H (fun _ => y) + P.H (fun _ => z)) / 2 < P.H (fun _ => (y + z) / 2) := by
  have hγ := hS.1
  have hk := (hS.2.2.2.2.2 0).1
  have hm := (hS.2.2.2.2.2 0).2.1
  rw [H1, H1, H1]
  have hsq : 0 < (y - z) ^ 2 := by have := sub_ne_zero.2 hne; positivity
  have hmx : max ((y + z) / 2 - P.xm 0) 0 ≤ (max (y - P.xm 0) 0 + max (z - P.xm 0) 0) / 2 :=
    max_le (by linarith [le_max_left (y - P.xm 0) 0, le_max_left (z - P.xm 0) 0])
      (by linarith [le_max_right (y - P.xm 0) 0, le_max_right (z - P.xm 0) 0])
  have hmn : max (-((y + z) / 2 - P.xm 0)) 0 ≤ (max (-(y - P.xm 0)) 0 + max (-(z - P.xm 0)) 0) / 2 :=
    max_le (by linarith [le_max_left (-(y - P.xm 0)) 0, le_max_left (-(z - P.xm 0)) 0])
      (by linarith [le_max_right (-(y - P.xm 0)) 0, le_max_right (-(z - P.xm 0)) 0])
  nlinarith [mul_le_mul_of_nonneg_left hmx hk, mul_le_mul_of_nonneg_left hmn hm, mul_pos hγ hv]

omit hS in
theorem oneFund : OneFund := by
  intro M P hS hv ws x2 pJ hws hmax hx2 hmax2 hpJ hJ xJ Lam
  have hcap := (hS.2.2.2.2.2 0).2.2.1
  have hfib := fibre_iff hws
  have hxJbox : 0 ≤ xJ ∧ xJ ≤ P.xbar 0 := hpJ.1 0
  have hJx : pJ.2 = fun _ => xJ := cst_eta pJ.2
  have hx2e : x2 = fun _ => x2 0 := cst_eta x2
  have mk : ∀ {x : ℝ} {w : Fin M → ℝ}, 0 ≤ x → x ≤ P.xbar 0 → x • P.r ≤ w → w ∈ P.WF :=
    fun h0 hc hw => ⟨fun _ => _, (mem_box1 _).2 ⟨h0, hc⟩, by rw [Q_one]; exact hw⟩
  have hVle : ∀ x, 0 ≤ x → x ≤ P.xbar 0 → P.VE (x • P.r) ≤ P.GE ws := by
    intro x h0 hc
    obtain ⟨w, hw, -, hV⟩ := VE_attain hS (x • P.r)
    rw [hV]; exact hmax (mk h0 hc hw)
  have hPhi_le : ∀ x, 0 ≤ x → x ≤ P.xbar 0 → P.Phi x ≤ P.Jobj pJ := by
    intro x h0 hc
    obtain ⟨w, hw, -, hV⟩ := VE_attain hS (x • P.r)
    have := hJ (show (w, fun _ => x) ∈ P.Feas from ⟨(mem_box1 x).2 ⟨h0, hc⟩, by rw [Q_one]; exact hw⟩)
    simp only [Set.mem_ofPred_eq, Jobj] at this
    rw [Phi, hV]; simp only [Jobj]; linarith
  have hJPhi : P.Jobj pJ = P.Phi xJ := by
    refine le_antisymm ?_ (hPhi_le xJ hxJbox.1 hxJbox.2)
    have hle : P.GE pJ.1 ≤ P.VE (xJ • P.r) := VE_ge hS _ (by
      have := hpJ.2; rw [Q_one] at this; exact this)
    simp only [Jobj, Phi]
    rw [hJx] at *
    linarith
  -- stage 2's holding is the clipped band solution
  have hx2int := (hfib x2).1 hx2
  have hab : P.xlo ws ≤ P.xhi ws := le_trans hx2int.1 hx2int.2
  obtain ⟨-, -, hcluniq⟩ := H1_clip hS hv hab
  have hHmax : ∀ c, P.xlo ws ≤ c → c ≤ P.xhi ws →
      (∀ y, P.xlo ws ≤ y → y ≤ P.xhi ws → P.H (fun _ => y) ≤ P.H (fun _ => c)) →
      c = clip P.xf (P.xlo ws) (P.xhi ws) := hcluniq
  have hx2clip : x2 0 = clip P.xf (P.xlo ws) (P.xhi ws) := hHmax (x2 0) hx2int.1 hx2int.2
    (fun y hy1 hy2 => by
      have := hmax2 ((hfib (fun _ => y)).2 ⟨hy1, hy2⟩)
      simp only [Set.mem_ofPred_eq] at this
      rwa [hx2e] at this)
  -- on the fibre interval `V_E(r y) = G_E(w*)`
  have hVint : ∀ y, P.xlo ws ≤ y → y ≤ P.xhi ws → P.VE (y • P.r) = P.GE ws := by
    intro y h1 h2
    obtain ⟨h0, hc, hy⟩ := (interval_iff ws (WF_r0 hws) y).2 ⟨h1, h2⟩
    exact le_antisymm (hVle y h0 hc) (VE_ge hS _ hy)
  -- uniqueness of the joint holding
  have huniq : ∀ y, 0 ≤ y → y ≤ P.xbar 0 → P.Phi y = P.Jobj pJ → y = xJ := by
    intro y h0 hc hy
    by_contra hne
    obtain ⟨wa, hwa, -, hVa⟩ := VE_attain hS (y • P.r)
    have hwb : xJ • P.r ≤ pJ.1 := by have := hpJ.2; rw [Q_one] at this; exact this
    have hmem : ((1 / 2 : ℝ) • wa + (1 / 2 : ℝ) • pJ.1, fun _ => (y + xJ) / 2) ∈ P.Feas := by
      have hb1 : 0 ≤ (y + xJ) / 2 := by linarith [hxJbox.1]
      have hb2 : (y + xJ) / 2 ≤ P.xbar 0 := by linarith [hxJbox.2]
      refine ⟨(mem_box1 ((y + xJ) / 2)).2 ⟨hb1, hb2⟩, ?_⟩
      rw [Q_one]; intro j
      have h1 := hwa j; have h2 := hwb j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 h2 ⊢
      nlinarith
    have h1 : P.Jobj ((1 / 2 : ℝ) • wa + (1 / 2 : ℝ) • pJ.1, fun _ => (y + xJ) / 2) ≤ P.Jobj pJ :=
      hJ hmem
    simp only [Jobj] at h1
    rw [hJx] at h1
    have hGc := GE_concave hS wa pJ.1 (t := 1 / 2) (by norm_num) (by norm_num)
    have e : wa + (1 / 2 : ℝ) • (pJ.1 - wa) = (1 / 2 : ℝ) • wa + (1 / 2 : ℝ) • pJ.1 := by module
    rw [e] at hGc
    have hHm := H1_mid hS hv hne
    rw [Phi, hVa] at hy
    simp only [Jobj] at hy
    rw [hJx] at hy
    linarith
  -- exactness iff `x_J` lies in the fibre interval
  have hint_suff : P.xlo ws ≤ xJ → xJ ≤ P.xhi ws → x2 0 = xJ := by
    intro h1 h2
    rw [hx2clip]
    refine (hHmax xJ h1 h2 fun y hy1 hy2 => ?_).symm
    have hy0 : 0 ≤ y ∧ y ≤ P.xbar 0 :=
      let h := (interval_iff ws (WF_r0 hws) y).2 ⟨hy1, hy2⟩; ⟨h.1, h.2.1⟩
    have := hPhi_le y hy0.1 hy0.2
    rw [hJPhi, Phi, Phi, hVint y hy1 hy2, hVint xJ h1 h2] at this
    linarith
  -- the loss is the misplacement: `T = Φ(x₂)`
  have hT : P.GE ws + P.H x2 = P.Phi (x2 0) := by
    have h := VE_fibre hmax hx2
    rw [Q_one] at h
    rw [Phi, h, ← hx2e]; ring
  have hLam : Lam = P.Phi xJ - P.Phi (x2 0) := by simp only [Lam]; rw [hJPhi, hT]
  have hmis0 : 0 ≤ P.Phi xJ - P.Phi (x2 0) := by
    have := hPhi_le (x2 0) (hx2.1 0).1 (hx2.1 0).2; linarith
  have hmis_iff : P.Phi xJ - P.Phi (x2 0) = 0 ↔ x2 0 = xJ := by
    constructor
    · intro h; exact huniq (x2 0) (hx2.1 0).1 (hx2.1 0).2 (by rw [hJPhi]; linarith)
    · intro h; rw [h, sub_self]
  have hLam_iff : Lam = 0 ↔ x2 0 = xJ := by rw [hLam]; exact hmis_iff
  refine ⟨?_, hVle, ?_, ?_, fun x => hfib x, ?_, hx2clip, hLam_iff,
    fun h1 h2 => hint_suff h1.le h2.le, fun h => by rw [← h]; exact hx2int, hJPhi, hT, hLam,
    hLam ▸ hmis0, ?_, ?_⟩
  · -- a stage-1 holding
    obtain ⟨x, hx, hxw⟩ := hws
    rw [Q_one] at hxw
    exact ⟨x 0, (hx 0).1, (hx 0).2, hxw, fun w hw => hmax (mk (hx 0).1 (hx 0).2 hw)⟩
  · -- the maximizing holdings form an interval
    refine ⟨fun a ha b hb c hc => ?_⟩
    obtain ⟨ha0, hac, haV⟩ := ha
    obtain ⟨hb0, hbc, hbV⟩ := hb
    have hc0 : 0 ≤ c := le_trans ha0 hc.1
    have hcc : c ≤ P.xbar 0 := le_trans hc.2 hbc
    refine ⟨hc0, hcc, le_antisymm (hVle c hc0 hcc) ?_⟩
    rcases eq_or_lt_of_le (le_trans hc.1 hc.2) with hab' | hab'
    · have : c = a := le_antisymm (hab' ▸ hc.2) hc.1
      rw [this, haV]
    set θ := (c - a) / (b - a)
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hc.1]) (by linarith)
    have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith [hc.2]
    have hcθ : c = a + θ * (b - a) := by simp only [θ]; field_simp; ring
    obtain ⟨wa, hwa, -, hVa⟩ := VE_attain hS (a • P.r)
    obtain ⟨wb, hwb, -, hVb⟩ := VE_attain hS (b • P.r)
    have hwc : c • P.r ≤ wa + θ • (wb - wa) := by
      intro j
      have h1 := hwa j; have h2 := hwb j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      rw [hcθ]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - θ),
        mul_le_mul_of_nonneg_left h2 hθ0]
    have hG := GE_concave hS wa wb hθ0 hθ1
    have := VE_ge hS _ hwc
    rw [hVa] at haV; rw [hVb] at hbV
    rw [haV, hbV, sub_self, mul_zero, add_zero] at hG
    linarith
  · -- with `w_TB` reachable
    intro hTB
    have hwsTB : ws = P.wTB := (GE_eq_wTB_iff hS ws).1
      (le_antisymm (GE_le_wTB hS ws) (by have := hmax hTB; simpa using this))
    have hVTB : ∀ x, 0 ≤ x → x ≤ P.xbar 0 → x • P.r ≤ P.wTB → P.VE (x • P.r) = P.GE P.wTB := by
      intro x h0 hc hx
      obtain ⟨w, hw, -, hV⟩ := VE_attain hS (x • P.r)
      rw [hV]
      exact le_antisymm (GE_le_wTB hS w) (by rw [← hV]; exact VE_ge hS _ hx)
    refine ⟨Set.ext fun x => ⟨fun ⟨h0, hc, hV⟩ => ⟨h0, hc, ?_⟩, fun ⟨h0, hc, hx⟩ => ⟨h0, hc, ?_⟩⟩, hVTB⟩
    · obtain ⟨w, hw, -, hVw⟩ := VE_attain hS (x • P.r)
      rw [hVw, hwsTB, GE_eq_wTB_iff hS] at hV
      rw [← hV]; exact hw
    · rw [hVTB x h0 hc hx, hwsTB]
  · -- the stage-1 holding's endpoints
    intro x1 h0 hc hx1 _
    have hint := (interval_iff ws (WF_r0 hws) x1).1 ⟨h0, hc, hx1⟩
    refine ⟨hint.1, hint.2, fun j hj he => le_antisymm hint.2 ?_, fun j hj he => le_antisymm ?_ hint.1⟩
    · have := (le_xhi_iff ws (P.xhi ws)).1 le_rfl
      have h := this.2 j hj
      rw [he] at h
      exact le_of_mul_le_mul_left h hj
    · have := (xlo_le_iff ws (P.xlo ws)).1 le_rfl
      have h := this.2 j hj
      rw [he] at h
      exact (mul_le_mul_left_of_neg hj).1 h
  · -- exactness iff `x_J` in the interval
    rw [hLam_iff]
    exact ⟨fun h => by rw [← h]; exact hx2int, fun h => hint_suff h.1 h.2⟩
  · -- reachability of `w_TB`
    constructor
    · intro hTB
      obtain ⟨x, hx, hxw⟩ := hTB
      rw [Q_one] at hxw
      have := (interval_iff P.wTB (WF_r0 ⟨x, hx, by rw [Q_one]; exact hxw⟩) (x 0)).1 ⟨(hx 0).1, (hx 0).2, hxw⟩
      exact ⟨le_trans this.1 this.2, WF_r0 ⟨x, hx, by rw [Q_one]; exact hxw⟩⟩
    · rintro ⟨hle, h0⟩
      obtain ⟨hy0, hyc, hy⟩ := (interval_iff P.wTB h0 (P.xlo P.wTB)).2 ⟨le_rfl, hle⟩
      exact mk hy0 hyc hy

end OneFund

theorem soft : Soft := by
  intro M N P hS RE ws p2 pJ hws hmax hp2 hmax2 hpJ hJ nu Ls
  have hnu : nu = -P.zeta ws := by simp [nu, zeta]
  have hid : ∀ q : (Fin M → ℝ) × (Fin N → ℝ), P.Jobj q = P.softObj ws q + P.GE ws + nu ⬝ᵥ (q.1 - ws) := by
    intro q
    have h := GE_line hS ws (q.1 - ws) 1
    rw [one_smul, add_sub_cancel] at h
    simp only [Jobj, softObj, h, hnu, neg_dotProduct]
    ring
  have hLs0 : 0 ≤ Ls := sub_nonneg.2 (hJ hp2)
  have hLsle : Ls ≤ nu ⬝ᵥ (pJ.1 - p2.1) := by
    have h1 := hmax2 hpJ
    simp only [Set.mem_ofPred_eq] at h1
    have e1 := hid pJ
    have e2 := hid p2
    have e3 : nu ⬝ᵥ (pJ.1 - ws) - nu ⬝ᵥ (p2.1 - ws) = nu ⬝ᵥ (pJ.1 - p2.1) := by
      rw [← dotProduct_sub]; congr 1; abel
    simp only [Ls]
    linarith
  have hA : P.wTB ∈ RE → nu = 0 ∧ Ls = 0 := by
    intro hTB
    have h1 := hmax hTB
    simp only [Set.mem_ofPred_eq] at h1
    have heq : ws = P.wTB := (GE_eq_wTB_iff hS ws).1 (le_antisymm (GE_le_wTB hS ws) h1)
    have hnu0 : nu = 0 := by rw [hnu, heq, zeta_wTB hS, neg_zero]
    refine ⟨hnu0, le_antisymm ?_ hLs0⟩
    rw [hnu0, zero_dotProduct] at hLsle; exact hLsle
  refine ⟨hA, fun hRE => ?_⟩
  subst hRE
  have hiff : nu = 0 ↔ P.wTB ∈ P.WF := by
    constructor
    · intro h0
      have : P.gamma • (P.Sig *ᵥ ws) = P.gamma • (P.Sig *ᵥ P.wTB) := by
        rw [S_wTB hS]; simp only [nu] at h0; exact (sub_eq_zero.1 h0).symm
      rw [← S_inj hS this]; exact hws
    · intro h; exact (hA h).1
  -- exactness iff the joint optimum solves the tilted stage 2
  have hcrit : Ls = 0 ↔ IsMaxOn (P.softObj ws) P.Feas pJ := by
    have hsoft : ∀ q, P.softObj ws q = P.Jobj q - P.GE ws - nu ⬝ᵥ (q.1 - ws) := fun q => by
      rw [hid q]; ring
    have hmidJ : P.Jobj ((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • p2) ≤ P.Jobj pJ :=
      hJ (Feas_convex hpJ hp2 (by norm_num) (by norm_num) (by norm_num))
    have hmid2 : P.softObj ws ((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • p2) ≤ P.softObj ws p2 :=
      hmax2 (Feas_convex hpJ hp2 (by norm_num) (by norm_num) (by norm_num))
    have hlin : nu ⬝ᵥ (((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • p2).1 - ws) =
        (nu ⬝ᵥ (pJ.1 - ws) + nu ⬝ᵥ (p2.1 - ws)) / 2 := by
      simp only [Prod.fst_add, Prod.smul_fst]
      rw [show (1 / 2 : ℝ) • pJ.1 + (1 / 2 : ℝ) • p2.1 - ws =
        (1 / 2 : ℝ) • (pJ.1 - ws) + (1 / 2 : ℝ) • (p2.1 - ws) by module]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    have eJ := hsoft pJ
    have e2 := hsoft p2
    have em := hsoft ((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • p2)
    constructor
    · intro h0
      simp only [Ls] at h0
      have hw : pJ.1 = p2.1 := by
        by_contra hne
        have := Jobj_mid hS hne
        linarith
      have hs : P.softObj ws pJ = P.softObj ws p2 := by rw [eJ, e2, hw]; linarith
      intro q hq
      have h1 := hmax2 hq
      simp only [Set.mem_ofPred_eq] at h1 ⊢
      linarith
    · intro hsJ
      have h1 := hsJ hp2
      have h2 := hmax2 hpJ
      simp only [Set.mem_ofPred_eq] at h1 h2
      have hw : pJ.1 = p2.1 := by
        by_contra hne
        have hm := Jobj_mid hS hne
        rw [hlin] at em
        linarith
      have hd : nu ⬝ᵥ (pJ.1 - ws) = nu ⬝ᵥ (p2.1 - ws) := by rw [hw]
      simp only [Ls]
      linarith
  refine ⟨hiff, fun hn => ⟨fun h0 => hn (hiff.1 h0), normal_cone hS hws hmax, hLs0, hLsle, hcrit⟩⟩

/-- Claim 041, parts 1-3. -/
theorem proof : Standalone.M7TwoStageEtfsAtZero.statement :=
  ⟨existence, stageSlacks, oneFund, soft⟩

end

end Novel.M7TwoStageEtfsAtZeroProof

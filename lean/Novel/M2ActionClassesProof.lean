import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M2ActionClasses

/-!
# Proof of claim 004: nested M2 action classes have optimal one-quarter actions

`w⁻` lies in every class because `τ(0) = 0`. Convexity of the classes and concavity of the
criterion come from the positive-part inequality `max(ty + (1-t)z, 0) ≤ t max(y,0) + (1-t) max(z,0)`
and from `w' Σ w = Σ_s q_s (w' ξ_s)²`. Closedness and continuity are coordinatewise. Each class
lies in the box `[0, w̄]`, so it is compact, and the extreme value theorem gives attainment.
The paper proof's explicit bisection argument is replaced by Mathlib's compactness of closed
boxes and `IsCompact.exists_isMaxOn`.
-/

namespace Novel.M2ActionClassesProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses

variable {m n K : ℕ} {S : Type} [Fintype S]

/-! ### The initial holding and nesting -/

omit [Fintype S] in
lemma tau_zero (D : Data m n K S) : tau D 0 = 0 := by
  simp [tau]

omit [Fintype S] in
lemma cash_w0 (D : Data m n K S) : cash D (w0 D) = k0 D := by
  simp [cash, tau_zero]

omit [Fintype S] in
lemma w0_mem_F (D : Data m n K S) (h : InitialPosition D) : w0 D ∈ F D := by
  obtain ⟨hW, hx, hh, hlim⟩ := h
  refine ⟨fun i => ⟨div_nonneg (hx i) hW.le, hlim i⟩, ?_⟩
  rw [cash_w0]
  exact div_nonneg hh hW.le

omit [Fintype S] in
lemma nestedNonempty (D : Data m n K S) (h : InitialPosition D) :
    N D ⊆ E D ∧ E D ⊆ F D ∧ (N D).Nonempty ∧ (E D).Nonempty ∧ (F D).Nonempty := by
  have hN : N D ⊆ E D := by
    intro w hw
    rw [N, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨w0_mem_F D h, rfl⟩
  have hE : E D ⊆ F D := fun w hw => hw.1
  have h0 : (N D).Nonempty := ⟨w0 D, rfl⟩
  exact ⟨hN, hE, h0, h0.mono hN, (h0.mono hN).mono hE⟩

/-! ### Continuity and closedness -/

omit [Fintype S] in
lemma continuous_tau (D : Data m n K S) : Continuous (tau D) := by
  unfold tau
  fun_prop

omit [Fintype S] in
lemma continuous_cash (D : Data m n K S) : Continuous (cash D) := by
  have := continuous_tau D
  unfold cash
  fun_prop

omit [Fintype S] in
lemma continuous_active : Continuous (active : (Inst m n → ℝ) → Fin m → ℝ) := by
  unfold active
  fun_prop

lemma continuous_beliefScore (D : Data m n K S) {T : Type} [Fintype T]
    (par : T → Params m K) (pi : T → ℝ) : Continuous (beliefScore D par pi) := by
  have := continuous_tau D
  unfold beliefScore score exposure active etf covariance
  simp only [Pi.add_apply, mulVec, dotProduct]
  fun_prop

omit [Fintype S] in
lemma isClosed_F (D : Data m n K S) : IsClosed (F D) := by
  have h1 : IsClosed {w : Inst m n → ℝ | ∀ i, 0 ≤ w i ∧ w i ≤ D.wbar i} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  exact h1.inter (isClosed_le continuous_const (continuous_cash D))

omit [Fintype S] in
lemma isClosed_E (D : Data m n K S) : IsClosed (E D) :=
  (isClosed_F D).inter (isClosed_eq continuous_active continuous_const)

omit [Fintype S] in
lemma F_subset_box (D : Data m n K S) : F D ⊆ Set.Icc 0 D.wbar :=
  fun _ hw => ⟨fun i => (hw.1 i).1, fun i => (hw.1 i).2⟩

omit [Fintype S] in
lemma closedBounded (D : Data m n K S) :
    IsClosed (F D) ∧ IsClosed (E D) ∧ IsClosed (N D) ∧
    Bornology.IsBounded (F D) ∧ Bornology.IsBounded (E D) ∧ Bornology.IsBounded (N D) := by
  have hF : Bornology.IsBounded (F D) := (Metric.isBounded_Icc 0 D.wbar).subset (F_subset_box D)
  exact ⟨isClosed_F D, isClosed_E D, isClosed_singleton, hF, hF.subset fun _ hw => hw.1,
    Bornology.isBounded_singleton⟩

/-! ### Convexity -/

lemma max_convex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y z : ℝ) :
    max (a * y + b * z) 0 ≤ a * max y 0 + b * max z 0 := by
  have hy := le_max_left y 0
  have hz := le_max_left z 0
  have hy0 := le_max_right y 0
  have hz0 := le_max_right z 0
  refine max_le ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hy ha, mul_le_mul_of_nonneg_left hz hb]

omit [Fintype S] in
/-- Convexity inequality for `τ`. -/
lemma tau_convex (D : Data m n K S) (hr : RatesNonneg D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x y : Inst m n → ℝ) : tau D (a • x + b • y) ≤ a * tau D x + b * tau D y := by
  simp only [tau, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have h1 := max_convex ha hb (x i) (y i)
  have h2 := max_convex ha hb (-x i) (-y i)
  have e : -(a * x i + b * y i) = a * -x i + b * -y i := by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
  nlinarith [mul_le_mul_of_nonneg_left h1 (hr i).1, mul_le_mul_of_nonneg_left h2 (hr i).2]

omit [Fintype S] in
lemma comb_sub (x y c : Inst m n → ℝ) {a b : ℝ} (hab : a + b = 1) :
    a • x + b • y - c = a • (x - c) + b • (y - c) := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (c i) * hab

omit [Fintype S] in
/-- Concavity inequality for the cash function. -/
lemma cash_concave (D : Data m n K S) (hr : RatesNonneg D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (x y : Inst m n → ℝ) :
    a * cash D x + b * cash D y ≤ cash D (a • x + b • y) := by
  have ht := tau_convex D hr ha hb (x - w0 D) (y - w0 D)
  rw [← comb_sub x y (w0 D) hab] at ht
  have hs : ∑ i, ((a • x + b • y) i - w0 D i)
      = a * ∑ i, (x i - w0 D i) + b * ∑ i, (y i - w0 D i) := by
    simp only [mul_sum, ← sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun i _ => by linear_combination (w0 D i) * hab
  simp only [cash, hs]
  have hk : k0 D = a * k0 D + b * k0 D := by linear_combination (-(k0 D)) * hab
  nlinarith

omit [Fintype S] in
lemma classesConvex (D : Data m n K S) (hr : RatesNonneg D) :
    Convex ℝ (F D) ∧ Convex ℝ (E D) ∧ Convex ℝ (N D) := by
  have hF : Convex ℝ (F D) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [(hx.1 i).1, (hy.1 i).1]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hw : D.wbar i = a * D.wbar i + b * D.wbar i := by
        linear_combination (-(D.wbar i)) * hab
      nlinarith [mul_le_mul_of_nonneg_left (hx.1 i).2 ha, mul_le_mul_of_nonneg_left (hy.1 i).2 hb]
    · have := cash_concave D hr ha hb hab x y
      nlinarith [hx.2, hy.2]
  refine ⟨hF, ?_, convex_singleton _⟩
  intro x hx y hy a b ha hb hab
  refine ⟨hF hx.1 hy.1 ha hb hab, ?_⟩
  funext j
  have hxj := congrFun hx.2 j
  have hyj := congrFun hy.2 j
  simp only [active] at hxj hyj
  show a * x (Sum.inl j) + b * y (Sum.inl j) = w0 D (Sum.inl j)
  rw [hxj, hyj]
  linear_combination (w0 D (Sum.inl j)) * hab

/-! ### Concavity of the criterion -/

lemma quad_eq (D : Data m n K S) (w : Inst m n → ℝ) :
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

omit [Fintype S] in
lemma dot_comb {ι : Type} [Fintype ι] (x y l : ι → ℝ) (a b : ℝ) :
    (a • x + b • y) ⬝ᵥ l = a * (x ⬝ᵥ l) + b * (y ⬝ᵥ l) := by
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

omit [Fintype S] in
lemma exposure_comb (D : Data m n K S) (x y : Inst m n → ℝ) (a b : ℝ) :
    exposure D (a • x + b • y) = a • exposure D x + b • exposure D y := by
  have ha : active (a • x + b • y) = a • active x + b • active y := rfl
  have he : etf (a • x + b • y) = a • etf x + b • etf y := rfl
  simp only [exposure, ha, he, mulVec_add, mulVec_smul, smul_add]
  abel

lemma quad_convex (D : Data m n K S) (hq : ∀ s, 0 ≤ D.q s) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (x y : Inst m n → ℝ) :
    (a • x + b • y) ⬝ᵥ (covariance D *ᵥ (a • x + b • y))
      ≤ a * (x ⬝ᵥ (covariance D *ᵥ x)) + b * (y ⬝ᵥ (covariance D *ᵥ y)) := by
  simp only [quad_eq, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun s _ => ?_
  rw [dot_comb]
  set X := x ⬝ᵥ xi D s
  set Y := y ⬝ᵥ xi D s
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : (a * X + (1 - a) * Y) ^ 2 ≤ a * X ^ 2 + (1 - a) * Y ^ 2 := by
    nlinarith [mul_nonneg ha hb, sq_nonneg (X - Y)]
  nlinarith [mul_le_mul_of_nonneg_left key (hq s)]

lemma score_concave (D : Data m n K S) (hg : 0 ≤ D.gamma) (hr : RatesNonneg D)
    (hq : ∀ s, 0 ≤ D.q s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y : Inst m n → ℝ) (θ : Params m K) :
    a * score D x θ + b * score D y θ ≤ score D (a • x + b • y) θ := by
  have hQ := quad_convex D hq ha hb hab x y
  have ht := tau_convex D hr ha hb (x - w0 D) (y - w0 D)
  rw [← comb_sub x y (w0 D) hab] at ht
  have hact : active (a • x + b • y) = a • active x + b • active y := rfl
  have hetf : etf (a • x + b • y) = a • etf x + b • etf y := rfl
  simp only [dot_comb] at hQ
  simp only [score, exposure_comb, hact, hetf, dot_comb]
  nlinarith [mul_le_mul_of_nonneg_left hQ (div_nonneg hg (by norm_num : (0 : ℝ) ≤ 2))]

lemma criterionContinuousConcave (D : Data m n K S) {T : Type} [Fintype T]
    (par : T → Params m K) (pi : T → ℝ) :
    Continuous (beliefScore D par pi) ∧
    (ConcavityInputs D pi → ConcaveOn ℝ Set.univ (beliefScore D par pi)) := by
  refine ⟨continuous_beliefScore D par pi, fun ⟨hg, hr, hq, hpi⟩ => ?_⟩
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [beliefScore, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  have := mul_le_mul_of_nonneg_left (score_concave D hg hr hq ha hb hab x y (par t)) (hpi t)
  nlinarith

/-! ### Attainment and the value chain -/

lemma attainmentAndValueChain (D : Data m n K S) {T : Type} [Fintype T]
    (par : T → Params m K) (pi : T → ℝ) (h : InitialPosition D) :
    (∃ w ∈ N D, IsMaxOn (beliefScore D par pi) (N D) w) ∧
    (∃ w ∈ E D, IsMaxOn (beliefScore D par pi) (E D) w) ∧
    (∃ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w) ∧
    ∀ wN wE wF, wN ∈ N D → IsMaxOn (beliefScore D par pi) (N D) wN →
      wE ∈ E D → IsMaxOn (beliefScore D par pi) (E D) wE →
      wF ∈ F D → IsMaxOn (beliefScore D par pi) (F D) wF →
        beliefScore D par pi wN ≤ beliefScore D par pi wE ∧
        beliefScore D par pi wE ≤ beliefScore D par pi wF := by
  obtain ⟨hNE, hEF, hN, hE, hF⟩ := nestedNonempty D h
  have hc : ∀ s, ContinuousOn (beliefScore D par pi) s :=
    fun _ => (continuous_beliefScore D par pi).continuousOn
  have hKF : IsCompact (F D) := isCompact_Icc.of_isClosed_subset (isClosed_F D) (F_subset_box D)
  have hKE : IsCompact (E D) := hKF.of_isClosed_subset (isClosed_E D) hEF
  refine ⟨isCompact_singleton.exists_isMaxOn hN (hc _), hKE.exists_isMaxOn hE (hc _),
    hKF.exists_isMaxOn hF (hc _), fun _ _ _ hwN _ hwE hmE _ hmF =>
      ⟨hmE (hNE hwN), hmF (hEF hwE)⟩⟩

theorem proof : Standalone.M2ActionClasses.statement :=
  ⟨fun _ _ _ _ _ D h => nestedNonempty D h,
   fun _ _ _ _ _ D => closedBounded D,
   fun _ _ _ _ _ D hr => classesConvex D hr,
   fun _ _ _ _ _ D _ _ par pi => criterionContinuousConcave D par pi,
   fun _ _ _ _ _ D _ _ par pi h => attainmentAndValueChain D par pi h⟩

end Novel.M2ActionClassesProof

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M3FiniteContinuation

/-!
# Proof of claim 011: M3 admits optimal finite policies and an attained continuation representation

Finite-dimensional throughout.

* **Policy set:** `Π_{D,R}` is cut out by finitely many affine and concave-superlevel constraints,
  and lies in a coordinate box. So it is convex and compact, and `Φ` attains its maximum by the
  extreme value theorem.
* **Concavity of `Φ`:** terminal wealth is affine minus convex costs, and `U(z) = -exp(-ρz)` is
  increasing and concave, so `Φ` is concave.
* **Conditional problem:** the same arguments give attainment and joint concavity of `V₁^R`; it is
  monotone in cash.
* **Continuation representation:** grouping the finite path sum by public observation (Bayes)
  expresses `Φ` through the conditional objectives, which gives `V_{D,R} = max H₀^R`.
* **Class comparison:** it follows from nesting of the policy sets and monotonicity of the
  certainty equivalent.

The funding identity is claim 001's (`depends_on: [001]`); it is re-derived here in M3's index
type.
-/

namespace Novel.M3FiniteContinuationProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
open scoped Classical

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-! ### Costs -/

section Cost

variable (P : M3 n K S T)

lemma sum_inst (f : Inst 1 n → ℝ) : ∑ i, f i = f (Sum.inl 0) + ∑ j, f (Sum.inr j) := by
  simp [Fintype.sum_sum_type]

omit [Fintype S] [Fintype T] in
lemma cost_nonneg (hr : ∀ i, 0 ≤ P.D.kplus i ∧ P.D.kminus i ≥ 0) (u : Inst 1 n → ℝ) :
    0 ≤ cost P.D u :=
  sum_nonneg fun i _ => add_nonneg (mul_nonneg (hr i).1 (le_max_right _ _))
    (mul_nonneg (hr i).2 (le_max_right _ _))

omit [Fintype S] [Fintype T] in
lemma cost_zero : cost P.D 0 = 0 := by simp [cost]

omit [Fintype S] [Fintype T] in
lemma continuous_cost : Continuous (cost P.D) := by
  unfold cost
  fun_prop

lemma max_conv {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y z : ℝ) :
    max (a * y + b * z) 0 ≤ a * max y 0 + b * max z 0 := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_left y 0) ha
  have h2 := mul_le_mul_of_nonneg_left (le_max_left z 0) hb
  have h3 := mul_nonneg ha (le_max_right y 0)
  have h4 := mul_nonneg hb (le_max_right z 0)
  exact max_le (by linarith) (by linarith)

omit [Fintype S] [Fintype T] in
lemma cost_convex (hr : ∀ i, 0 ≤ P.D.kplus i ∧ P.D.kminus i ≥ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (u v : Inst 1 n → ℝ) :
    cost P.D (a • u + b • v) ≤ a * cost P.D u + b * cost P.D v := by
  simp only [cost, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have h1 := max_conv ha hb (u i) (v i)
  have h2 := max_conv ha hb (-u i) (-v i)
  have e : -(a * u i + b * v i) = a * -u i + b * -v i := by ring
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
  nlinarith [mul_le_mul_of_nonneg_left h1 (hr i).1, mul_le_mul_of_nonneg_left h2 (hr i).2]

end Cost

/-! ### Unpacking the setting -/

lemma setting_parts {P : M3 n K S T} (h : M3Setting P) :
    0 < P.rho ∧ (∀ s, 0 ≤ P.D.q s) ∧ ∑ s, P.D.q s = 1 ∧ (∀ t, 0 ≤ P.pi0 t) ∧ ∑ t, P.pi0 t = 1 ∧
    (∀ i, 0 ≤ P.D.kplus i ∧ P.D.kplus i < 1 ∧ 0 ≤ P.D.kminus i ∧ P.D.kminus i < 1) ∧
    (∀ i, 0 ≤ P.D.x0 i) ∧ 0 ≤ P.D.h0 ∧ 0 < W0 P.D ∧ ∀ t s i, 0 < 1 + ret P.D (P.par t) s i := h

lemma rates_nonneg {P : M3 n K S T} (h : M3Setting P) :
    ∀ i, 0 ≤ P.D.kplus i ∧ P.D.kminus i ≥ 0 :=
  fun i => ⟨((setting_parts h).2.2.2.2.2.1 i).1, ((setting_parts h).2.2.2.2.2.1 i).2.2.1⟩

/-! ### One funded review -/

section OneReview

variable {P : M3 n K S T}

omit [Fintype S] [Fintype T] in
/-- The accounting identity (claim 001, in M3's index type). -/
lemma post_wealth (x : Inst 1 n → ℝ) (h : ℝ) (u : Inst 1 n → ℝ) :
    ∑ i, (x i + u i) + (h - ∑ i, u i - cost P.D u) = (h + ∑ i, x i) - cost P.D u := by
  rw [sum_add_distrib]; ring

lemma feas_upper (hS : M3Setting P) {c : Cls} {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ}
    (hu : Feas1 P c x h u) (i : Inst 1 n) : x i + u i ≤ h + ∑ j, x j := by
  have hid := post_wealth (P := P) x h u
  have hc := cost_nonneg P (rates_nonneg hS) u
  have hsum : x i + u i ≤ ∑ j, (x j + u j) :=
    single_le_sum (f := fun j => x j + u j) (fun j _ => hu.1 j) (mem_univ i)
  linarith [hu.2.1]

omit [Fintype S] [Fintype T] in
lemma feas_zero (c : Cls) {x : Inst 1 n → ℝ} {h : ℝ} (hx : ∀ i, 0 ≤ x i) (hh : 0 ≤ h) :
    Feas1 P c x h 0 := by
  refine ⟨fun i => by simpa using hx i, by simp [cost_zero, hh], ?_⟩
  cases c <;> simp [Allowed]

/-- After a funded trade from positive wealth, post-trade wealth is positive. -/
lemma post_pos (hS : M3Setting P) {c : Cls} {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hh : 0 ≤ h) (hW : 0 < h + ∑ i, x i) (hu : Feas1 P c x h u) :
    0 < ∑ i, (x i + u i) + (h - ∑ i, u i - cost P.D u) := by
  obtain ⟨_, _, _, _, _, hk, _⟩ := setting_parts hS
  by_contra hle
  push Not at hle
  have hnn : ∀ i, 0 ≤ x i + u i := hu.1
  have hc0 : 0 ≤ h - ∑ i, u i - cost P.D u := hu.2.1
  have hsum0 : ∑ i, (x i + u i) = 0 :=
    le_antisymm (by linarith) (sum_nonneg fun i _ => hnn i)
  have hzero : ∀ i, x i + u i = 0 := fun i =>
    (sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp hsum0 i (mem_univ i)
  have hcash0 : h - ∑ i, u i - cost P.D u = 0 := by linarith
  -- with u = -x the cash is h + Σ (1 - κ⁻) x > 0
  have hu' : ∀ i, u i = -x i := fun i => by linarith [hzero i]
  have hcost : cost P.D u = ∑ i, P.D.kminus i * x i := by
    simp only [cost]
    refine sum_congr rfl fun i _ => ?_
    rw [hu' i, max_eq_right (by linarith [hx i]), neg_neg, max_eq_left (hx i)]
    ring
  have hsu : ∑ i, u i = -∑ i, x i := by rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => hu' i
  rw [hcost, hsu] at hcash0
  have hpos : 0 < h + ∑ i, (1 - P.D.kminus i) * x i := by
    by_cases hh0 : 0 < h
    · have : 0 ≤ ∑ i, (1 - P.D.kminus i) * x i :=
        sum_nonneg fun i _ => mul_nonneg (by linarith [(hk i).2.2.2]) (hx i)
      linarith
    · have hh' : h = 0 := le_antisymm (not_lt.mp hh0) hh
      rw [hh'] at hW ⊢
      rw [zero_add] at hW ⊢
      obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
        by_contra hne
        push Not at hne
        have : ∑ i, x i ≤ 0 := sum_nonpos fun i _ => hne i
        linarith
      exact lt_of_lt_of_le (mul_pos (by linarith [(hk i).2.2.2]) hi)
        (single_le_sum (f := fun i => (1 - P.D.kminus i) * x i)
          (fun j _ => mul_nonneg (by linarith [(hk j).2.2.2]) (hx j)) (mem_univ i))
  have e : ∑ i, (1 - P.D.kminus i) * x i = ∑ i, x i - ∑ i, P.D.kminus i * x i := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  linarith

end OneReview

/-! ### Utility -/

section Utility

variable (P : M3 n K S T)

omit [Fintype S] [Fintype T] in
lemma U_mono (hρ : 0 < P.rho) {z z' : ℝ} (h : z ≤ z') : U P z ≤ U P z' := by
  unfold U
  have : Real.exp (-P.rho * z') ≤ Real.exp (-P.rho * z) := Real.exp_le_exp.mpr (by nlinarith)
  linarith

omit [Fintype S] [Fintype T] in
lemma U_concave {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z z' : ℝ) :
    a * U P z + b * U P z' ≤ U P (a * z + b * z') := by
  unfold U
  have := convexOn_exp.2 (Set.mem_univ (-P.rho * z)) (Set.mem_univ (-P.rho * z')) ha hb hab
  simp only [smul_eq_mul] at this
  have e : -P.rho * (a * z + b * z') = a * (-P.rho * z) + b * (-P.rho * z') := by ring
  rw [e]
  linarith

omit [Fintype S] [Fintype T] in
/-- The pathwise utility inequality: a wealth at least the mixture has utility at least the
mixture of utilities. -/
lemma U_mix (hρ : 0 < P.rho) {W : ℝ} (hW : 0 < W) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {z z' w : ℝ} (hw : a * z + b * z' ≤ w) :
    a * U P (z / W) + b * U P (z' / W) ≤ U P (w / W) := by
  have h1 := U_concave P ha hb hab (z / W) (z' / W)
  have h2 : a * (z / W) + b * (z' / W) ≤ w / W := by
    rw [show a * (z / W) + b * (z' / W) = (a * z + b * z') / W by ring]
    exact div_le_div_of_nonneg_right hw hW.le
  exact h1.trans (U_mono P hρ h2)

omit [Fintype S] [Fintype T] in
lemma U_gt (hρ : 0 < P.rho) {z : ℝ} (hz : 0 < z) : -1 < U P z := by
  unfold U
  have : Real.exp (-P.rho * z) < 1 := by
    have := Real.exp_lt_exp.mpr (show -P.rho * z < 0 by nlinarith)
    rwa [Real.exp_zero] at this
  linarith

omit [Fintype S] [Fintype T] in
lemma continuous_U : Continuous (U P) := by
  unfold U
  fun_prop

end Utility

/-! ### Marking -/

section Marking

omit [Fintype S] [Fintype T] in
/-- Marking nonnegative positions and cash with positive gross returns keeps wealth positive. -/
lemma marked_pos {c : ℝ} {v g : Inst 1 n → ℝ} (hc : 0 ≤ c) (hv : ∀ i, 0 ≤ v i)
    (hg : ∀ i, 0 < g i) (hpos : 0 < c + ∑ i, v i) : 0 < c + ∑ i, v i * g i := by
  by_contra hle
  push Not at hle
  have hterm : ∀ i, 0 ≤ v i * g i := fun i => mul_nonneg (hv i) (hg i).le
  have hsn : 0 ≤ ∑ i, v i * g i := sum_nonneg fun i _ => hterm i
  have hs : ∑ i, v i * g i = 0 := le_antisymm (by linarith) hsn
  have hc0 : c = 0 := by linarith
  have hv0 : ∀ i, v i = 0 := fun i => by
    have := (sum_eq_zero_iff_of_nonneg fun i _ => hterm i).mp hs i (mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (hg i).ne'
  have : ∑ i, v i = 0 := sum_eq_zero fun i _ => hv0 i
  linarith

omit [Fintype S] [Fintype T] in
/-- Marking multiplies wealth by at most `M ≥ 1`. -/
lemma marked_le {c M : ℝ} {v g : Inst 1 n → ℝ} (hc : 0 ≤ c) (hv : ∀ i, 0 ≤ v i) (hM : 1 ≤ M)
    (hg : ∀ i, g i ≤ M) : c + ∑ i, v i * g i ≤ M * (c + ∑ i, v i) := by
  have : ∑ i, v i * g i ≤ M * ∑ i, v i := by
    rw [mul_sum]; exact sum_le_sum fun i _ => by nlinarith [hv i, hg i]
  nlinarith

end Marking

/-! ### Observations -/

section Obs

variable {P : M3 n K S T}

lemma obs_mem (y : Yset P) : ∃ t s, obs P t s = (y : Obs n K) := by
  obtain ⟨⟨t, s⟩, _, h⟩ := Finset.mem_image.mp y.2
  exact ⟨t, s, h⟩

lemma gross_pos (hS : M3Setting P) (y : Yset P) (i : Inst 1 n) : 0 < 1 + (y : Obs n K).2 i := by
  obtain ⟨t, s, h⟩ := obs_mem y
  rw [← h]
  exact (setting_parts hS).2.2.2.2.2.2.2.2.2 t s i

lemma gross_le {M : ℝ} (hM : ∀ t s i, 1 + ret P.D (P.par t) s i ≤ M) (y : Yset P) (i : Inst 1 n) :
    1 + (y : Obs n K).2 i ≤ M := by
  obtain ⟨t, s, h⟩ := obs_mem y
  rw [← h]
  exact hM t s i

end Obs

/-! ### The policy set -/

section Policies

variable {P : M3 n K S T}

lemma x1_nonneg (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : ∀ i, 0 ≤ P.D.x0 i + u₀ i)
    (y : Yset P) (i : Inst 1 n) : 0 ≤ x1 P y u₀ i :=
  mul_nonneg (gross_pos hS y i).le (hu i)

omit [Fintype S] [Fintype T] in
/-- Root post-trade wealth identity. -/
lemma root_wealth (u₀ : Inst 1 n → ℝ) :
    ∑ i, (P.D.x0 i + u₀ i) + h1 P u₀ = W0 P.D - cost P.D u₀ := by
  have := post_wealth (P := P) P.D.x0 P.D.h0 u₀
  simp only [h1, W0] at this ⊢
  linarith

lemma h1_le (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : ∀ i, 0 ≤ P.D.x0 i + u₀ i) :
    h1 P u₀ ≤ W0 P.D := by
  have := root_wealth (P := P) u₀
  have := cost_nonneg P (rates_nonneg hS) u₀
  have := sum_nonneg fun i (_ : i ∈ univ) => hu i
  linarith

lemma W1m_eq (π : Policy P) (t : T) (s₀ : S) :
    W1m P π t s₀ = h1 P π.1 + ∑ i, (P.D.x0 i + π.1 i) * (1 + ret P.D (P.par t) s₀ i) := by
  simp only [W1m, x1, obs]
  congr 1
  exact sum_congr rfl fun i _ => by ring

lemma W2_eq (π : Policy P) (t : T) (s₀ s₁ : S) :
    W2 P π t s₀ s₁ = (h1 P π.1 - ∑ i, π.2 (obsY P t s₀) i - cost P.D (π.2 (obsY P t s₀)))
      + ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i) * (1 + ret P.D (P.par t) s₁ i) := by
  simp only [W2, condW]

lemma wealth_pos (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) (t : T)
    (s₀ s₁ : S) : 0 < W1m P π t s₀ ∧ 0 < W2 P π t s₀ s₁ := by
  obtain ⟨_, _, _, _, _, _, hx0, hh0, hW0, hg⟩ := setting_parts hS
  have hroot := hπ.1
  have hpost := post_pos hS hx0 hh0 hW0 hroot
  have hh1 : h1 P π.1 = P.D.h0 - ∑ i, π.1 i - cost P.D π.1 := rfl
  have hW1 : 0 < W1m P π t s₀ := by
    rw [W1m_eq]
    exact marked_pos hroot.2.1 hroot.1 (hg t s₀) (by linarith)
  refine ⟨hW1, ?_⟩
  have hnode : Feas1 P r (x1 P (obs P t s₀) π.1) (h1 P π.1) (π.2 (obsY P t s₀)) :=
    hπ.2 (obsY P t s₀)
  have hx1 : ∀ i, 0 ≤ x1 P (obs P t s₀) π.1 i := x1_nonneg hS hroot.1 (obsY P t s₀)
  have hpost2 := post_pos hS hx1 hroot.2.1
    (hW1 : 0 < h1 P π.1 + ∑ i, x1 P (obs P t s₀) π.1 i) hnode
  rw [W2_eq]
  exact marked_pos hnode.2.1 hnode.1 (hg t s₁) (by linarith)

lemma wealth_le (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ t s i, 1 + ret P.D (P.par t) s i ≤ M) (t : T) (s₀ s₁ : S) :
    W1m P π t s₀ ≤ M * W0 P.D ∧ W2 P π t s₀ s₁ ≤ M ^ 2 * W0 P.D := by
  have hroot := hπ.1
  have hc0 := cost_nonneg P (rates_nonneg hS) π.1
  have hrw := root_wealth (P := P) π.1
  have hW1 : W1m P π t s₀ ≤ M * W0 P.D := by
    rw [W1m_eq]
    have := marked_le hroot.2.1 hroot.1 hM1 (hM t s₀)
    have hle : h1 P π.1 + ∑ i, (P.D.x0 i + π.1 i) ≤ W0 P.D := by linarith
    calc _ ≤ M * (h1 P π.1 + ∑ i, (P.D.x0 i + π.1 i)) := this
      _ ≤ M * W0 P.D := mul_le_mul_of_nonneg_left hle (by linarith)
  refine ⟨hW1, ?_⟩
  have hnode : Feas1 P r (x1 P (obs P t s₀) π.1) (h1 P π.1) (π.2 (obsY P t s₀)) :=
    hπ.2 (obsY P t s₀)
  have hx1 : ∀ i, 0 ≤ x1 P (obs P t s₀) π.1 i := x1_nonneg hS hroot.1 (obsY P t s₀)
  have hc1 := cost_nonneg P (rates_nonneg hS) (π.2 (obsY P t s₀))
  have hpw := post_wealth (P := P) (x1 P (obs P t s₀) π.1) (h1 P π.1) (π.2 (obsY P t s₀))
  rw [W2_eq]
  have := marked_le hnode.2.1 hnode.1 hM1 (hM t s₁)
  have hle : (h1 P π.1 - ∑ i, π.2 (obsY P t s₀) i - cost P.D (π.2 (obsY P t s₀)))
      + ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i) ≤ W1m P π t s₀ := by
    simp only [W1m]; linarith
  calc _ ≤ M * ((h1 P π.1 - ∑ i, π.2 (obsY P t s₀) i - cost P.D (π.2 (obsY P t s₀)))
        + ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i)) := this
    _ ≤ M * W1m P π t s₀ := mul_le_mul_of_nonneg_left hle (by linarith)
    _ ≤ M * (M * W0 P.D) := mul_le_mul_of_nonneg_left hW1 (by linarith)
    _ = M ^ 2 * W0 P.D := by ring

end Policies

/-! ### Mixing feasible trades -/

section Mixing

variable {P : M3 n K S T}

omit [Fintype S] [Fintype T] in
lemma sum_mix (a b : ℝ) (u u' : Inst 1 n → ℝ) :
    ∑ i, (a • u + b • u') i = a * ∑ i, u i + b * ∑ i, u' i := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, mul_sum]

omit [Fintype S] [Fintype T] in
lemma allowed_mix {c : Cls} {u u' : Inst 1 n → ℝ} (hu : Allowed c u) (hu' : Allowed c u')
    (a b : ℝ) : Allowed c (a • u + b • u') := by
  cases c
  · trivial
  · simp only [Allowed] at hu hu' ⊢
    simp [hu, hu']
  · simp only [Allowed] at hu hu' ⊢
    rw [hu, hu']; simp

lemma feas_mix (hS : M3Setting P) {c : Cls} {x x' xm : Inst 1 n → ℝ} {h h' hm : ℝ}
    {u u' : Inst 1 n → ℝ} (hu : Feas1 P c x h u) (hu' : Feas1 P c x' h' u') {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : xm = a • x + b • x') (hh : a * h + b * h' ≤ hm) :
    Feas1 P c xm hm (a • u + b • u') := by
  have hc := cost_convex P (rates_nonneg hS) ha hb u u'
  refine ⟨fun i => ?_, ?_, allowed_mix hu.2.2 hu'.2.2 a b⟩
  · rw [hx]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hu.1 i), mul_nonneg hb (hu'.1 i)]
  · rw [sum_mix]
    nlinarith [mul_nonneg ha hu.2.1, mul_nonneg hb hu'.2.1]

omit [Fintype S] [Fintype T] in
lemma x1_mix (y : Obs n K) (u u' : Inst 1 n → ℝ) {a b : ℝ} (hab : a + b = 1) :
    x1 P y (a • u + b • u') = a • x1 P y u + b • x1 P y u' := by
  funext i
  simp only [x1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(1 + y.2 i) * P.D.x0 i) * hab

lemma h1_mix (hS : M3Setting P) (u u' : Inst 1 n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * h1 P u + b * h1 P u' ≤ h1 P (a • u + b • u') := by
  have hc := cost_convex P (rates_nonneg hS) ha hb u u'
  simp only [h1, sum_mix]
  have : P.D.h0 = a * P.D.h0 + b * P.D.h0 := by linear_combination (-P.D.h0) * hab
  nlinarith

lemma pol_mix_fst (π π' : Policy P) (a b : ℝ) : (a • π + b • π').1 = a • π.1 + b • π'.1 := rfl

lemma pol_mix_snd (π π' : Policy P) (a b : ℝ) (y : Yset P) :
    (a • π + b • π').2 y = a • π.2 y + b • π'.2 y := rfl

lemma convex_Pol (hS : M3Setting P) (d r : Cls) : Convex ℝ (Pol P d r) := by
  intro π hπ π' hπ' a b ha hb hab
  refine ⟨feas_mix hS hπ.1 hπ'.1 ha hb ?_ ?_, fun y => ?_⟩
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-P.D.x0 i) * hab
  · linear_combination P.D.h0 * hab
  · rw [pol_mix_snd, pol_mix_fst]
    exact feas_mix hS (hπ.2 y) (hπ'.2 y) ha hb (x1_mix _ _ _ hab) (h1_mix hS _ _ ha hb hab)

lemma W2_mix (hS : M3Setting P) (π π' : Policy P) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (t : T) (s₀ s₁ : S) :
    a * W2 P π t s₀ s₁ + b * W2 P π' t s₀ s₁ ≤ W2 P (a • π + b • π') t s₀ s₁ := by
  rw [W2_eq, W2_eq, W2_eq, pol_mix_snd, pol_mix_fst, x1_mix _ _ _ hab]
  have hh := h1_mix hS π.1 π'.1 ha hb hab
  have hc := cost_convex P (rates_nonneg hS) ha hb (π.2 (obsY P t s₀)) (π'.2 (obsY P t s₀))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsu : ∑ i, (a * π.2 (obsY P t s₀) i + b * π'.2 (obsY P t s₀) i)
      = a * ∑ i, π.2 (obsY P t s₀) i + b * ∑ i, π'.2 (obsY P t s₀) i := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  have hlin : ∑ i, (a * x1 P (obs P t s₀) π.1 i + b * x1 P (obs P t s₀) π'.1 i
        + (a * π.2 (obsY P t s₀) i + b * π'.2 (obsY P t s₀) i)) * (1 + ret P.D (P.par t) s₁ i)
      = a * ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i) * (1 + ret P.D (P.par t) s₁ i)
        + b * ∑ i, (x1 P (obs P t s₀) π'.1 i + π'.2 (obsY P t s₀) i)
            * (1 + ret P.D (P.par t) s₁ i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hlin, hsu]
  nlinarith

end Mixing

/-! ### Topology of the policy set -/

section Topology

variable {P : M3 n K S T}

omit [Fintype S] [Fintype T] in
lemma isClosed_feas {α : Type} [TopologicalSpace α] {c : Cls} {X Uu : α → Inst 1 n → ℝ}
    {Hc : α → ℝ} (hX : Continuous X) (hH : Continuous Hc) (hU : Continuous Uu) :
    IsClosed {π | Feas1 P c (X π) (Hc π) (Uu π)} := by
  have h1 : IsClosed {π : α | ∀ i, 0 ≤ X π i + Uu π i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (((continuous_apply i).comp hX).add ((continuous_apply i).comp hU))
  have h2 : IsClosed {π : α | 0 ≤ Hc π - ∑ i, Uu π i - cost P.D (Uu π)} :=
    isClosed_le continuous_const ((hH.sub (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).comp hU)).sub ((continuous_cost P).comp hU))
  have h3 : IsClosed {π : α | Allowed c (Uu π)} := by
    cases c
    · simp [Allowed]
    · exact isClosed_eq ((continuous_apply _).comp hU) continuous_const
    · exact isClosed_eq hU continuous_const
  simp only [Feas1, Set.ofPred_and]
  exact h1.inter (h2.inter h3)

lemma continuous_x1 (y : Obs n K) : Continuous fun π : Policy P => x1 P y π.1 := by
  unfold x1
  fun_prop

lemma continuous_h1 : Continuous fun π : Policy P => h1 P π.1 := by
  have := continuous_cost P
  unfold h1
  fun_prop

lemma isClosed_Pol (d r : Cls) : IsClosed (Pol P d r) := by
  have hroot : IsClosed {π : Policy P | Feas1 P d P.D.x0 P.D.h0 π.1} :=
    isClosed_feas continuous_const continuous_const continuous_fst
  have hnode : IsClosed {π : Policy P | ∀ y : Yset P,
      Feas1 P r (x1 P y π.1) (h1 P π.1) (π.2 y)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y =>
      isClosed_feas (continuous_x1 _) continuous_h1 ((continuous_apply y).comp continuous_snd)
  simp only [Pol, Set.ofPred_and]
  exact hroot.inter hnode

/-- The review-1 trade bound at observation `y`. -/
noncomputable def bnd (P : M3 n K S T) (y : Yset P) : ℝ :=
  W0 P.D * (1 + ∑ j, (1 + (y : Obs n K).2 j))

lemma Pol_subset_box (hS : M3Setting P) (d r : Cls) :
    Pol P d r ⊆ Set.Icc (fun i => -P.D.x0 i) (fun _ => W0 P.D) ×ˢ
      Set.Icc (fun y _ => -bnd P y) (fun y _ => bnd P y) := by
  obtain ⟨_, _, _, _, _, _, hx0, hh0, hW0, _⟩ := setting_parts hS
  intro π hπ
  have hroot := hπ.1
  have hup0 : ∀ i, P.D.x0 i + π.1 i ≤ W0 P.D := fun i => by
    have := feas_upper hS hroot i; simpa [W0] using this
  have hh1 := h1_le hS hroot.1
  refine ⟨⟨fun i => by linarith [hroot.1 i], fun i => by linarith [hup0 i, hx0 i]⟩,
    ⟨fun y i => ?_, fun y i => ?_⟩⟩
  · have hnode := hπ.2 y
    have hd := gross_pos hS y i
    have hx1 : x1 P y π.1 i ≤ (1 + (y : Obs n K).2 i) * W0 P.D :=
      mul_le_mul_of_nonneg_left (hup0 i) hd.le
    have hsum : (1 + (y : Obs n K).2 i) ≤ ∑ j, (1 + (y : Obs n K).2 j) :=
      single_le_sum (f := fun j => 1 + (y : Obs n K).2 j) (fun j _ => (gross_pos hS y j).le)
        (mem_univ i)
    have := hnode.1 i
    simp only [bnd]
    nlinarith
  · have hnode := hπ.2 y
    have hx1nn := x1_nonneg hS hroot.1 y
    have hup := feas_upper hS hnode i
    have hsx : ∑ j, x1 P y π.1 j ≤ ∑ j, (1 + (y : Obs n K).2 j) * W0 P.D :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hup0 j) (gross_pos hS y j).le
    rw [← sum_mul] at hsx
    simp only [bnd]
    nlinarith [hx1nn i]

lemma isCompact_Pol (hS : M3Setting P) (d r : Cls) : IsCompact (Pol P d r) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_Pol d r) (Pol_subset_box hS d r)

lemma Pol_nonempty (hS : M3Setting P) (d r : Cls) : (Pol P d r).Nonempty := by
  obtain ⟨_, _, _, _, _, _, hx0, hh0, _⟩ := setting_parts hS
  refine ⟨(0, fun _ => 0), feas_zero d hx0 hh0, fun y => ?_⟩
  exact feas_zero r (x1_nonneg hS (fun i => by simpa using hx0 i) y) (by simpa [h1, cost_zero] using hh0)

lemma continuous_Phi : Continuous (Phi P) := by
  have hc := continuous_cost P
  have hU := continuous_U P
  unfold Phi W2 condW x1 h1
  fun_prop

end Topology

/-! ### Weighted averages -/

lemma wavg_gt {ι : Type} [Fintype ι] {w f : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (hf : ∀ i, c < f i) : c < ∑ i, w i * f i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra hne
    push Not at hne
    have : ∑ i, w i = 0 := sum_eq_zero fun i _ => le_antisymm (hne i) (hw i)
    linarith
  have hpos : 0 < ∑ i, w i * (f i - c) :=
    sum_pos' (fun i _ => mul_nonneg (hw i) (by linarith [hf i]))
      ⟨j, mem_univ j, mul_pos hj (by linarith [hf j])⟩
  have e : ∑ i, w i * (f i - c) = ∑ i, w i * f i - c := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, h1, one_mul]
  linarith

lemma wavg_le {ι : Type} [Fintype ι] {w f : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (hf : ∀ i, f i ≤ c) : ∑ i, w i * f i ≤ c := by
  calc ∑ i, w i * f i ≤ ∑ i, w i * c := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i)
    _ = c := by rw [← sum_mul, h1, one_mul]

/-! ### Part 1: policies, attainment and bounds -/

section Part1

variable {P : M3 n K S T}

lemma Phi_nested (π : Policy P) :
    Phi P π = ∑ t, P.pi0 t * ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * U P (W2 P π t s₀ s₁ / W0 P.D) := by
  simp only [Phi, mul_sum]
  exact sum_congr rfl fun t _ => sum_congr rfl fun s₀ _ => sum_congr rfl fun s₁ _ => by ring

lemma Phi_concave (hS : M3Setting P) (d r : Cls) : ConcaveOn ℝ (Pol P d r) (Phi P) := by
  obtain ⟨hρ, hq, _, hpi, _, _, _, _, hW0, _⟩ := setting_parts hS
  refine ⟨convex_Pol hS d r, fun π _ π' _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Phi, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t _ => sum_le_sum fun s₀ _ => sum_le_sum fun s₁ _ => ?_
  have hw : 0 ≤ P.pi0 t * P.D.q s₀ * P.D.q s₁ := mul_nonneg (mul_nonneg (hpi t) (hq s₀)) (hq s₁)
  have := mul_le_mul_of_nonneg_left
    (U_mix P hρ hW0 ha hb hab (W2_mix hS π π' ha hb hab t s₀ s₁)) hw
  nlinarith

lemma Vmax (hS : M3Setting P) (d r : Cls) :
    ∃ π ∈ Pol P d r, IsMaxOn (Phi P) (Pol P d r) π ∧ Phi P π = V P d r := by
  obtain ⟨π, hπ, hmax⟩ := (isCompact_Pol hS d r).exists_isMaxOn (Pol_nonempty hS d r)
    continuous_Phi.continuousOn
  refine ⟨π, hπ, hmax, ?_⟩
  have hG : IsGreatest (Phi P '' Pol P d r) (Phi P π) :=
    ⟨Set.mem_image_of_mem _ hπ, fun z ⟨π', hπ', hz⟩ => hz ▸ hmax hπ'⟩
  exact hG.csSup_eq.symm

lemma V_eq_of_max {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r)
    (hmax : IsMaxOn (Phi P) (Pol P d r) π) : V P d r = Phi P π := by
  have hG : IsGreatest (Phi P '' Pol P d r) (Phi P π) :=
    ⟨Set.mem_image_of_mem _ hπ, fun z ⟨π', hπ', hz⟩ => hz ▸ hmax hπ'⟩
  exact hG.csSup_eq

lemma Phi_gt (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) : -1 < Phi P π := by
  obtain ⟨hρ, hq, hq1, hpi, hpi1, _, _, _, hW0, _⟩ := setting_parts hS
  rw [Phi_nested]
  refine wavg_gt hpi hpi1 fun t => wavg_gt hq hq1 fun s₀ => wavg_gt hq hq1 fun s₁ => ?_
  exact U_gt P hρ (div_pos (wealth_pos hS hπ t s₀ s₁).2 hW0)

lemma Phi_le (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ t s i, 1 + ret P.D (P.par t) s i ≤ M) :
    Phi P π ≤ -Real.exp (-P.rho * M ^ 2) := by
  obtain ⟨hρ, hq, hq1, hpi, hpi1, _, _, _, hW0, _⟩ := setting_parts hS
  rw [Phi_nested]
  refine wavg_le hpi hpi1 fun t => wavg_le hq hq1 fun s₀ => wavg_le hq hq1 fun s₁ => ?_
  have hle := (wealth_le hS hπ hM1 hM t s₀ s₁).2
  have : W2 P π t s₀ s₁ / W0 P.D ≤ M ^ 2 := by rw [div_le_iff₀ hW0]; exact hle
  exact U_mono P hρ this

lemma policyAttainment (hS : M3Setting P) (d r : Cls) :
    (Pol P d r).Nonempty ∧ Convex ℝ (Pol P d r) ∧ IsCompact (Pol P d r) ∧
    Continuous (Phi P) ∧ ConcaveOn ℝ (Pol P d r) (Phi P) ∧
    (∃ π ∈ Pol P d r, IsMaxOn (Phi P) (Pol P d r) π ∧ Phi P π = V P d r) ∧
    (∀ π ∈ Pol P d r, ∀ t s₀ s₁, 0 < W1m P π t s₀ ∧ 0 < W2 P π t s₀ s₁) ∧
    (∀ M : ℝ, 1 ≤ M → (∀ t s i, 1 + ret P.D (P.par t) s i ≤ M) →
      (∀ π ∈ Pol P d r, ∀ t s₀ s₁, W1m P π t s₀ ≤ M * W0 P.D ∧ W2 P π t s₀ s₁ ≤ M ^ 2 * W0 P.D) ∧
      -1 < V P d r ∧ V P d r ≤ -Real.exp (-P.rho * M ^ 2)) := by
  obtain ⟨π, hπ, hmax, hV⟩ := Vmax hS d r
  refine ⟨Pol_nonempty hS d r, convex_Pol hS d r, isCompact_Pol hS d r, continuous_Phi,
    Phi_concave hS d r, ⟨π, hπ, hmax, hV⟩, fun π' hπ' t s₀ s₁ => wealth_pos hS hπ' t s₀ s₁,
    fun M hM1 hM => ⟨fun π' hπ' t s₀ s₁ => wealth_le hS hπ' hM1 hM t s₀ s₁, ?_, ?_⟩⟩
  · rw [← hV]; exact Phi_gt hS hπ
  · rw [← hV]; exact Phi_le hS hπ hM1 hM

end Part1

/-! ### Part 2: the conditional problem -/

section Part2

variable {P : M3 n K S T}

lemma continuous_condObj (pi : T → ℝ) (x : Inst 1 n → ℝ) (h : ℝ) :
    Continuous (condObj P pi x h) := by
  have hc := continuous_cost P
  have hU := continuous_U P
  unfold condObj condW
  fun_prop

lemma isCompact_feas1 (hS : M3Setting P) (c : Cls) {x : Inst 1 n → ℝ} {h : ℝ}
    (hx : ∀ i, 0 ≤ x i) : IsCompact {u | Feas1 P c x h u} := by
  refine (isCompact_Icc (a := fun i => -x i) (b := fun _ => h + ∑ i, x i)).of_isClosed_subset
    (isClosed_feas continuous_const continuous_const continuous_id) fun u hu => ⟨fun i => ?_, fun i => ?_⟩
  · linarith [hu.1 i]
  · linarith [feas_upper hS hu i, hx i]

lemma cond_attain (hS : M3Setting P) (c : Cls) (pi : T → ℝ) {x : Inst 1 n → ℝ} {h : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hh : 0 ≤ h) :
    ∃ u, Feas1 P c x h u ∧ (∀ u', Feas1 P c x h u' → condObj P pi x h u' ≤ condObj P pi x h u) ∧
      V1 P c x h pi = condObj P pi x h u := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_feas1 hS c (h := h) hx).exists_isMaxOn
    ⟨0, feas_zero (P := P) c hx hh⟩
    (continuous_condObj (P := P) pi x h).continuousOn
  refine ⟨u, hu, fun u' hu' => hmax hu', ?_⟩
  have hG : IsGreatest (condObj P pi x h '' {u | Feas1 P c x h u}) (condObj P pi x h u) :=
    ⟨Set.mem_image_of_mem _ hu, fun z ⟨u', hu', hz⟩ => hz ▸ hmax hu'⟩
  exact hG.csSup_eq

lemma condW_mix (hS : M3Setting P) {x x' : Inst 1 n → ℝ} {h h' : ℝ} (u u' : Inst 1 n → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : T) (s : S) :
    a * condW P x h u t s + b * condW P x' h' u' t s
      ≤ condW P (a • x + b • x') (a * h + b * h') (a • u + b • u') t s := by
  have hc := cost_convex P (rates_nonneg hS) ha hb u u'
  simp only [condW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsu : ∑ i, (a * u i + b * u' i) = a * ∑ i, u i + b * ∑ i, u' i := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  have hlin : ∑ i, (a * x i + b * x' i + (a * u i + b * u' i)) * (1 + ret P.D (P.par t) s i)
      = a * ∑ i, (x i + u i) * (1 + ret P.D (P.par t) s i)
        + b * ∑ i, (x' i + u' i) * (1 + ret P.D (P.par t) s i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hlin, hsu]
  nlinarith

lemma condObj_mix (hS : M3Setting P) {pi : T → ℝ} (hpi : ∀ t, 0 ≤ pi t) {x x' : Inst 1 n → ℝ}
    {h h' : ℝ} (u u' : Inst 1 n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * condObj P pi x h u + b * condObj P pi x' h' u'
      ≤ condObj P pi (a • x + b • x') (a * h + b * h') (a • u + b • u') := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  simp only [condObj, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t _ => sum_le_sum fun s _ => ?_
  have hw : 0 ≤ pi t * P.D.q s := mul_nonneg (hpi t) (hq s)
  have := mul_le_mul_of_nonneg_left (U_mix P hρ hW0 ha hb hab
    (condW_mix hS (x := x) (x' := x') (h := h) (h' := h') u u' ha hb t s)) hw
  nlinarith

lemma condObj_mono_h (hS : M3Setting P) {pi : T → ℝ} (hpi : ∀ t, 0 ≤ pi t) (x : Inst 1 n → ℝ)
    {h h' : ℝ} (hhh : h ≤ h') (u : Inst 1 n → ℝ) : condObj P pi x h u ≤ condObj P pi x h' u := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  refine sum_le_sum fun t _ => sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (hpi t) (hq s))
  refine U_mono P hρ (div_le_div_of_nonneg_right ?_ hW0.le)
  simp only [condW]; linarith

lemma V1_mono_h (hS : M3Setting P) (r : Cls) {pi : T → ℝ} (hpi : ∀ t, 0 ≤ pi t)
    {x : Inst 1 n → ℝ} {h h' : ℝ} (hx : ∀ i, 0 ≤ x i) (hh : 0 ≤ h) (hhh : h ≤ h') :
    V1 P r x h pi ≤ V1 P r x h' pi := by
  obtain ⟨u, hu, _, hV⟩ := cond_attain hS r pi hx hh
  obtain ⟨u', _, hmax', hV'⟩ := cond_attain hS r pi hx (hh.trans hhh)
  have hu' : Feas1 P r x h' u := ⟨hu.1, by linarith [hu.2.1], hu.2.2⟩
  rw [hV, hV']
  exact (condObj_mono_h hS hpi x hhh u).trans (hmax' u hu')

lemma V1_concave (hS : M3Setting P) (r : Cls) {pi : T → ℝ} (hpi : ∀ t, 0 ≤ pi t) :
    ConcaveOn ℝ {p : (Inst 1 n → ℝ) × ℝ | (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2}
      (fun p => V1 P r p.1 p.2 pi) := by
  refine ⟨fun p hp p' hp' a b ha hb hab => ⟨fun i => ?_, ?_⟩, fun p hp p' hp' a b ha hb hab => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hp.1 i), mul_nonneg hb (hp'.1 i)]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_nonneg ha hp.2, mul_nonneg hb hp'.2]
  · obtain ⟨u, hu, _, hV⟩ := cond_attain hS r pi hp.1 hp.2
    obtain ⟨u', hu', _, hV'⟩ := cond_attain hS r pi hp'.1 hp'.2
    have hxm : ∀ i, 0 ≤ (a • p.1 + b • p'.1) i := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha (hp.1 i), mul_nonneg hb (hp'.1 i)]
    have hhm : 0 ≤ a * p.2 + b * p'.2 := by nlinarith [mul_nonneg ha hp.2, mul_nonneg hb hp'.2]
    obtain ⟨_, _, hmaxm, hVm⟩ := cond_attain hS r pi hxm hhm
    have hfeas : Feas1 P r (a • p.1 + b • p'.1) (a * p.2 + b * p'.2) (a • u + b • u') :=
      feas_mix hS hu hu' ha hb rfl le_rfl
    simp only [smul_eq_mul, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
    rw [hV, hV', hVm]
    exact (condObj_mix hS hpi u u' ha hb hab).trans (hmaxm _ hfeas)

lemma feas_zero_state (hS : M3Setting P) (r : Cls) (u : Inst 1 n → ℝ) :
    Feas1 P r 0 0 u ↔ u = 0 := by
  constructor
  · intro hu
    have hnn : ∀ i, 0 ≤ u i := fun i => by simpa using hu.1 i
    have hc := cost_nonneg P (rates_nonneg hS) u
    have hs : ∑ i, u i = 0 :=
      le_antisymm (by linarith [hu.2.1]) (sum_nonneg fun i _ => hnn i)
    funext i
    exact (sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp hs i (mem_univ i)
  · rintro rfl
    exact feas_zero r (fun _ => le_rfl) le_rfl

lemma V1_zero (hS : M3Setting P) (r : Cls) {pi : T → ℝ} (h1 : ∑ t, pi t = 1) : V1 P r 0 0 pi = -1 := by
  obtain ⟨_, _, hq1, _⟩ := setting_parts hS
  obtain ⟨u, hu, _, hV⟩ := cond_attain hS r pi (x := 0) (fun _ => le_rfl) le_rfl
  rw [(feas_zero_state hS r u).mp hu] at hV
  rw [hV]
  simp only [condObj, condW, U, cost_zero]
  simp [← mul_sum, hq1, h1]

end Part2

/-! ### Part 3: Bayes regrouping and the continuation representation -/

section Part3

variable {P : M3 n K S T}

lemma lik_nonneg (hS : M3Setting P) (t : T) (y : Obs n K) : 0 ≤ lik P t y :=
  sum_nonneg fun s _ => by split_ifs <;> simp [(setting_parts hS).2.1 s]

lemma P0_nonneg (hS : M3Setting P) (y : Obs n K) : 0 ≤ P0 P y :=
  sum_nonneg fun t _ => mul_nonneg ((setting_parts hS).2.2.2.1 t) (lik_nonneg hS t y)

lemma post_nonneg (hS : M3Setting P) (y : Obs n K) (t : T) : 0 ≤ post P y t := by
  unfold post
  split_ifs with h
  · exact div_nonneg (mul_nonneg ((setting_parts hS).2.2.2.1 t) (lik_nonneg hS t y)) h.le
  · exact (setting_parts hS).2.2.2.1 t

lemma bayes (y : Obs n K) (t : T) (h : 0 < P0 P y) : P.pi0 t * lik P t y = P0 P y * post P y t := by
  simp only [post, h, ↓reduceIte]
  rw [mul_div_cancel₀ _ h.ne']

/-- The inner second-quarter sum at observation `y`. -/
noncomputable def G (P : M3 n K S T) (π : Policy P) (t : T) (y : Yset P) : ℝ :=
  ∑ s₁, P.D.q s₁ * U P (condW P (x1 P y π.1) (h1 P π.1) (π.2 y) t s₁ / W0 P.D)

lemma Phi_group (π : Policy P) :
    Phi P π = ∑ y : Yset P, ∑ t, P.pi0 t * lik P t y * G P π t y := by
  have h1 : Phi P π = ∑ t, ∑ s₀, P.pi0 t * P.D.q s₀ * G P π t (obsY P t s₀) := by
    simp only [Phi, G, W2, mul_sum]
    exact sum_congr rfl fun t _ => sum_congr rfl fun s₀ _ => sum_congr rfl fun s₁ _ => by
      rw [mul_assoc (P.pi0 t * P.D.q s₀)]; rfl
  have h2 : ∀ t s₀, P.pi0 t * P.D.q s₀ * G P π t (obsY P t s₀)
      = ∑ y : Yset P, if obsY P t s₀ = y then P.pi0 t * P.D.q s₀ * G P π t y else 0 := by
    intro t s₀
    rw [Fintype.sum_ite_eq]
  have h3 : ∀ t (y : Yset P),
      ∑ s₀, (if obsY P t s₀ = y then P.pi0 t * P.D.q s₀ * G P π t y else 0)
        = P.pi0 t * lik P t y * G P π t y := by
    intro t y
    simp only [lik, mul_sum, sum_mul]
    refine sum_congr rfl fun s₀ _ => ?_
    by_cases hy : obsY P t s₀ = y
    · have : obs P t s₀ = (y : Obs n K) := by rw [← hy]; rfl
      simp only [hy, this, ↓reduceIte]
    · have : obs P t s₀ ≠ (y : Obs n K) := fun h => hy (Subtype.ext h)
      simp only [hy, this, ↓reduceIte, mul_zero, zero_mul]
  calc Phi P π
      = ∑ t, ∑ s₀, ∑ y : Yset P,
          (if obsY P t s₀ = y then P.pi0 t * P.D.q s₀ * G P π t y else 0) := by
        rw [h1]; simp only [h2]
    _ = ∑ t, ∑ y : Yset P, ∑ s₀,
          (if obsY P t s₀ = y then P.pi0 t * P.D.q s₀ * G P π t y else 0) :=
        sum_congr rfl fun t _ => sum_comm
    _ = ∑ y : Yset P, ∑ t, ∑ s₀,
          (if obsY P t s₀ = y then P.pi0 t * P.D.q s₀ * G P π t y else 0) := sum_comm
    _ = ∑ y : Yset P, ∑ t, P.pi0 t * lik P t y * G P π t y := by simp only [h3]

lemma Phi_regroup (hS : M3Setting P) (π : Policy P) :
    Phi P π = ∑ y : Yset P,
      if 0 < P0 P y then P0 P y * condObj P (post P y) (x1 P y π.1) (h1 P π.1) (π.2 y) else 0 := by
  rw [Phi_group]
  refine sum_congr rfl fun y _ => ?_
  split_ifs with hP
  · simp only [bayes (y : Obs n K) _ hP, condObj, mul_sum, G]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring
  · have hz : P0 P y = 0 := le_antisymm (not_lt.mp hP) (P0_nonneg hS y)
    have hterm : ∀ t, P.pi0 t * lik P t y = 0 := fun t =>
      (sum_eq_zero_iff_of_nonneg fun t _ => mul_nonneg ((setting_parts hS).2.2.2.1 t)
        (lik_nonneg hS t y)).mp hz t (mem_univ t)
    exact sum_eq_zero fun t _ => by rw [hterm t, zero_mul]

lemma H0_eq (r : Cls) (u₀ : Inst 1 n → ℝ) :
    H0 P r u₀ = ∑ y : Yset P,
      if 0 < P0 P y then P0 P y * V1 P r (x1 P y u₀) (h1 P u₀) (post P y) else 0 := by
  rw [H0, ← Finset.sum_coe_sort]

/-- Node states after a funded root trade are nonnegative. -/
lemma node_state (hS : M3Setting P) {d : Cls} {u₀ : Inst 1 n → ℝ}
    (hu : Feas1 P d P.D.x0 P.D.h0 u₀) (y : Yset P) :
    (∀ i, 0 ≤ x1 P y u₀ i) ∧ 0 ≤ h1 P u₀ :=
  ⟨x1_nonneg hS hu.1 y, hu.2.1⟩

lemma Phi_le_H0 (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) :
    Phi P π ≤ H0 P r π.1 := by
  rw [Phi_regroup hS, H0_eq]
  refine sum_le_sum fun y _ => ?_
  split_ifs with hP
  · refine mul_le_mul_of_nonneg_left ?_ hP.le
    obtain ⟨hx, hh⟩ := node_state hS hπ.1 y
    obtain ⟨_, _, hmax, hV⟩ := cond_attain hS r (post P y) hx hh
    rw [hV]
    exact hmax _ (hπ.2 y)
  · exact le_rfl

lemma H0_attain (hS : M3Setting P) {d r : Cls} {u₀ : Inst 1 n → ℝ}
    (hu : Feas1 P d P.D.x0 P.D.h0 u₀) :
    ∃ u₁, (u₀, u₁) ∈ Pol P d r ∧ Phi P (u₀, u₁) = H0 P r u₀ := by
  have hex : ∀ y : Yset P, ∃ v, Feas1 P r (x1 P y u₀) (h1 P u₀) v ∧
      V1 P r (x1 P y u₀) (h1 P u₀) (post P y) = condObj P (post P y) (x1 P y u₀) (h1 P u₀) v :=
    fun y => by
      obtain ⟨hx, hh⟩ := node_state hS hu y
      obtain ⟨v, hv, _, hV⟩ := cond_attain hS r (post P y) hx hh
      exact ⟨v, hv, hV⟩
  choose u₁ hu₁ hV using hex
  refine ⟨u₁, ⟨hu, hu₁⟩, ?_⟩
  rw [Phi_regroup hS, H0_eq]
  refine sum_congr rfl fun y _ => ?_
  rw [hV y]

lemma V_rep (hS : M3Setting P) (d r : Cls) :
    ∃ u₀, Feas1 P d P.D.x0 P.D.h0 u₀ ∧ H0 P r u₀ = V P d r ∧
      ∀ u₀', Feas1 P d P.D.x0 P.D.h0 u₀' → H0 P r u₀' ≤ V P d r := by
  obtain ⟨π, hπ, hmax, hV⟩ := Vmax hS d r
  have hle : ∀ u₀', Feas1 P d P.D.x0 P.D.h0 u₀' → H0 P r u₀' ≤ V P d r := by
    intro u₀' hu'
    obtain ⟨u₁, hmem, hPhi⟩ := H0_attain hS (r := r) hu'
    rw [← hPhi, ← hV]
    exact hmax hmem
  refine ⟨π.1, hπ.1, le_antisymm (hle _ hπ.1) ?_, hle⟩
  rw [← hV]
  exact Phi_le_H0 hS hπ

lemma H0_concave (hS : M3Setting P) (r : Cls) :
    ConcaveOn ℝ {u₀ | Feas1 P .F P.D.x0 P.D.h0 u₀} (H0 P r) := by
  have hconv : Convex ℝ {u₀ | Feas1 P .F P.D.x0 P.D.h0 u₀} := by
    intro u hu u' hu' a b ha hb hab
    refine feas_mix hS hu hu' ha hb ?_ (by linear_combination P.D.h0 * hab)
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-P.D.x0 i) * hab
  refine ⟨hconv, fun u hu u' hu' a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, H0_eq, mul_sum]
  rw [← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  split_ifs with hP
  · have hpost := post_nonneg hS (y : Obs n K)
    obtain ⟨hx, hh⟩ := node_state hS hu y
    obtain ⟨hx', hh'⟩ := node_state hS hu' y
    have hmixh := h1_mix hS u u' ha hb hab
    have hxm : ∀ i, 0 ≤ (a • x1 P y u + b • x1 P y u') i := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha (hx i), mul_nonneg hb (hx' i)]
    have hhm : 0 ≤ a * h1 P u + b * h1 P u' := by nlinarith [mul_nonneg ha hh, mul_nonneg hb hh']
    have hconc := (V1_concave hS r hpost).2 (x := (x1 P y u, h1 P u)) (y := (x1 P y u', h1 P u'))
      ⟨hx, hh⟩ ⟨hx', hh'⟩ ha hb hab
    simp only [smul_eq_mul, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd] at hconc
    have hmono := V1_mono_h hS r hpost hxm hhm hmixh
    rw [x1_mix _ _ _ hab]
    nlinarith [mul_le_mul_of_nonneg_left (hconc.trans hmono) hP.le]
  · simp

lemma continuationRep (hS : M3Setting P) :
    (∀ y t, 0 < P0 P y → P.pi0 t * lik P t y = P0 P y * post P y t) ∧
    ∀ d r : Cls,
      (∀ π ∈ Pol P d r, Phi P π = ∑ y : Yset P,
        if 0 < P0 P y then P0 P y * condObj P (post P y) (x1 P y π.1) (h1 P π.1) (π.2 y) else 0) ∧
      ConcaveOn ℝ {u₀ | Feas1 P .F P.D.x0 P.D.h0 u₀} (H0 P r) ∧
      (∀ u₀, Feas1 P d P.D.x0 P.D.h0 u₀ →
        (∃ u₁, (u₀, u₁) ∈ Pol P d r ∧ Phi P (u₀, u₁) = H0 P r u₀) ∧
        ∀ u₁, (u₀, u₁) ∈ Pol P d r → Phi P (u₀, u₁) ≤ H0 P r u₀) ∧
      (∃ u₀, Feas1 P d P.D.x0 P.D.h0 u₀ ∧ H0 P r u₀ = V P d r ∧
        ∀ u₀', Feas1 P d P.D.x0 P.D.h0 u₀' → H0 P r u₀' ≤ V P d r) :=
  ⟨fun y t h => bayes y t h, fun d r => ⟨fun π _ => Phi_regroup hS π, H0_concave hS r,
    fun _ hu => ⟨H0_attain hS hu, fun _ hmem => Phi_le_H0 hS hmem⟩, V_rep hS d r⟩⟩

end Part3

/-! ### Part 4: class comparison -/

section Part4

variable {P : M3 n K S T}

lemma wavg_lt {ι : Type} [Fintype ι] {w f : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (hf : ∀ i, f i < c) : ∑ i, w i * f i < c := by
  have := wavg_gt (c := -c) (f := fun i => -f i) hw h1 fun i => by linarith [hf i]
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

lemma V_neg (hS : M3Setting P) (d r : Cls) : V P d r < 0 := by
  obtain ⟨hρ, hq, hq1, hpi, hpi1, _⟩ := setting_parts hS
  obtain ⟨π, _, _, hV⟩ := Vmax hS d r
  rw [← hV, Phi_nested]
  refine wavg_lt hpi hpi1 fun t => wavg_lt hq hq1 fun s₀ => wavg_lt hq hq1 fun s₁ => ?_
  unfold U
  linarith [Real.exp_pos (-P.rho * (W2 P π t s₀ s₁ / W0 P.D))]

lemma V_mono (hS : M3Setting P) {d r d' r' : Cls} (hsub : Pol P d r ⊆ Pol P d' r') :
    V P d r ≤ V P d' r' := by
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  obtain ⟨π', _, hmax', hV'⟩ := Vmax hS d' r'
  rw [← hV, ← hV']
  exact hmax' (hsub hπ)

lemma CE_mono (hS : M3Setting P) {d r d' r' : Cls} (h : V P d r ≤ V P d' r') :
    CE P d r ≤ CE P d' r' := by
  have hρ := (setting_parts hS).1
  have h1 := V_neg hS d' r'
  have hlog : Real.log (-V P d' r') ≤ Real.log (-V P d r) :=
    Real.log_le_log (by linarith) (by linarith)
  simp only [CE]
  have : 0 < 1 / P.rho := by positivity
  nlinarith

lemma allowed_NE {u : Inst 1 n → ℝ} (h : Allowed .N u) : Allowed .E u := by
  simp only [Allowed] at h ⊢; rw [h]; rfl

omit [Fintype S] [Fintype T] in
lemma feas_NE {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ} (hu : Feas1 P .N x h u) :
    Feas1 P .E x h u := ⟨hu.1, hu.2.1, allowed_NE hu.2.2⟩

omit [Fintype S] [Fintype T] in
lemma feas_EF {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ} (hu : Feas1 P .E x h u) :
    Feas1 P .F x h u := ⟨hu.1, hu.2.1, trivial⟩

lemma classComparison (hS : M3Setting P) :
    (∀ r, V P .N r ≤ V P .E r ∧ V P .E r ≤ V P .F r ∧ CE P .N r ≤ CE P .E r ∧ CE P .E r ≤ CE P .F r) ∧
    (∀ d, V P d .N ≤ V P d .E ∧ V P d .E ≤ V P d .F ∧ CE P d .N ≤ CE P d .E ∧ CE P d .E ≤ CE P d .F) ∧
    ∀ r, 0 ≤ Delta P r ∧
      (Delta P r = 0 ↔ ∃ π ∈ Pol P .F r, IsMaxOn (Phi P) (Pol P .F r) π ∧ π.1 (Sum.inl 0) = 0) := by
  have hNE : ∀ r, Pol P .N r ⊆ Pol P .E r := fun r π hπ => ⟨feas_NE hπ.1, hπ.2⟩
  have hEF : ∀ r, Pol P .E r ⊆ Pol P .F r := fun r π hπ => ⟨feas_EF hπ.1, hπ.2⟩
  have hNE' : ∀ d, Pol P d .N ⊆ Pol P d .E := fun d π hπ => ⟨hπ.1, fun y => feas_NE (hπ.2 y)⟩
  have hEF' : ∀ d, Pol P d .E ⊆ Pol P d .F := fun d π hπ => ⟨hπ.1, fun y => feas_EF (hπ.2 y)⟩
  refine ⟨fun r => ⟨V_mono hS (hNE r), V_mono hS (hEF r), CE_mono hS (V_mono hS (hNE r)),
      CE_mono hS (V_mono hS (hEF r))⟩,
    fun d => ⟨V_mono hS (hNE' d), V_mono hS (hEF' d), CE_mono hS (V_mono hS (hNE' d)),
      CE_mono hS (V_mono hS (hEF' d))⟩, fun r => ⟨?_, ?_⟩⟩
  · simp only [Delta]
    linarith [CE_mono hS (V_mono hS (hEF r))]
  · have hρ := (setting_parts hS).1
    have hVE := V_neg hS .E r
    have hVF := V_neg hS .F r
    have hEFv := V_mono hS (hEF r)
    constructor
    · intro hD
      have hlog : Real.log (-V P .F r) = Real.log (-V P .E r) := by
        simp only [Delta, CE] at hD
        have : 1 / P.rho ≠ 0 := by positivity
        have := mul_left_cancel₀ (neg_ne_zero.mpr this) (by linarith : -(1 / P.rho) * Real.log (-V P .F r)
          = -(1 / P.rho) * Real.log (-V P .E r))
        exact this
      have hVeq : V P .F r = V P .E r := by
        have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) hlog
        linarith
      obtain ⟨πE, hπE, _, hV⟩ := Vmax hS .E r
      obtain ⟨πF, _, hmaxF, hVF'⟩ := Vmax hS .F r
      refine ⟨πE, hEF r hπE, fun π hπ => ?_, hπE.1.2.2⟩
      have := hmaxF hπ
      simp only [Set.mem_ofPred_eq] at this ⊢
      linarith
    · rintro ⟨π, hπ, hmax, hA⟩
      have hπE : π ∈ Pol P .E r := ⟨⟨hπ.1.1, hπ.1.2.1, hA⟩, hπ.2⟩
      obtain ⟨πE, _, hmaxE, hV⟩ := Vmax hS .E r
      have h1 : Phi P π ≤ V P .E r := by rw [← hV]; exact hmaxE hπE
      have h2 : V P .F r = Phi P π := V_eq_of_max hπ hmax
      have hVeq : V P .F r = V P .E r := le_antisymm (by linarith) hEFv
      simp only [Delta, CE, hVeq, sub_self]

end Part4

theorem proof : Standalone.M3FiniteContinuation.statement :=
  ⟨fun _ _ _ _ _ _ _ hS d r => policyAttainment hS d r,
   fun _ _ _ _ _ _ _ hS r pi hpi => ⟨fun _ _ hx hh => cond_attain hS r pi hx hh,
     V1_concave hS r hpi, fun _ _ _ hx hh hhh => V1_mono_h hS r hpi hx hh hhh,
     feas_zero_state hS r, fun h1 => V1_zero hS r h1⟩,
   fun _ _ _ _ _ _ _ hS => continuationRep hS,
   fun _ _ _ _ _ _ _ hS => classComparison hS⟩

end Novel.M3FiniteContinuationProof

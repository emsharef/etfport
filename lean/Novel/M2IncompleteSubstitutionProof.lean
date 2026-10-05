import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M2IncompleteSubstitution

/-!
# Proof of claim 007: an added ETF can enlarge active trading while its full-span menu still
cannot match the optimum

Each menu's criterion is written explicitly: mean term, minus half the conditional quadratic
form (expanded over the 32 sign scenarios), minus `1/2000` times the positive and negative parts
of every trade. Unique optimality of each candidate is the paper's certificate inequality:
the score gap to any feasible comparator `z` is at least half the quadratic form of `z - w`,
by linear arithmetic over the trade parts, the funded budget and the position bounds (the
multipliers are found by `linarith` rather than copied from the claim's table). The residual
variance terms make that quadratic form positive whenever `z ≠ w`.
-/

namespace Novel.M2IncompleteSubstitutionProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry Standalone.M2IncompleteSubstitution

variable {n : ℕ}

/-! ### Generic facts -/

lemma quad_eq (D : Data 1 n 2 Scen) (w : Inst 1 n → ℝ) :
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

lemma sum_scen (f : Scen → ℝ) :
    ∑ s, f s = ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool, ∑ b₄ : Bool, ∑ b₅ : Bool,
      f (b₁, b₂, b₃, b₄, b₅) := by
  simp only [Fintype.sum_prod_type]

lemma max_parts (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-! ### Menu 1 -/

lemma W0_1 : W0 data1 = 1 := by
  simp [W0, data1, Fintype.sum_sum_type]; norm_num

lemma w0_1 : w0 data1 = hold1 (1 / 2) (1 / 3) := by
  funext i
  rcases i with j | j <;> fin_cases j <;> simp only [w0, W0_1, div_one] <;> simp [data1, hold1]

lemma k0_1 : k0 data1 = 1 / 6 := by simp only [k0, W0_1, div_one]; simp [data1]

lemma hold1_surj (w : Inst 1 1 → ℝ) : w = hold1 (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with j | j <;> fin_cases j <;> rfl

/-- Quadratic form of menu 1. -/
noncomputable def Qf1 (a p : ℝ) : ℝ :=
  (3 / 50) ^ 2 * (a + p) ^ 2 + (1 / 50) ^ 2 * (a / 2) ^ 2 + (3 / 100) ^ 2 * a ^ 2
    + (1 / 200) ^ 2 * p ^ 2

/-- Trade parts of menu 1. -/
noncomputable def T1 (a p : ℝ) : ℝ :=
  max (a - 1 / 2) 0 + max (-(a - 1 / 2)) 0 + max (p - 1 / 3) 0 + max (-(p - 1 / 3)) 0

lemma quad1 (a p : ℝ) :
    hold1 a p ⬝ᵥ (covariance data1 *ᵥ hold1 a p) = Qf1 a p := by
  rw [quad_eq, sum_scen]
  simp [data1, xi, hold1, dotProduct, Fintype.sum_sum_type, sg, Qf1,
    Matrix.vecHead, Matrix.vecTail]
  ring

lemma tau1 (a p : ℝ) : tau data1 (hold1 a p - w0 data1) = T1 a p / 2000 := by
  rw [w0_1]
  simp [tau, data1, hold1, Fintype.sum_sum_type, T1]
  ring

lemma cash1 (a p : ℝ) : cash data1 (hold1 a p) = 1 / 6 - (a - 1 / 2) - (p - 1 / 3) - T1 a p / 2000 := by
  have := tau1 a p
  rw [cash, this, k0_1, w0_1]
  simp [hold1, Fintype.sum_sum_type]
  try ring

lemma Q1_eq (a p : ℝ) :
    Q1 (hold1 a p) = a / 50 + 201 / 10000 * p - Qf1 a p / 2 - T1 a p / 2000 := by
  simp only [Q1, beliefScore, Fin.sum_univ_one, pi1, one_mul, score, quad1, tau1]
  simp [exposure, active, etf, hold1, data1, par, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-! ### Menu 2 -/

lemma W0_2 : W0 data2 = 1 := by
  simp [W0, data2, Fintype.sum_sum_type, Fin.sum_univ_two]; norm_num

lemma w0_2 : w0 data2 = hold2 (1 / 2) (1 / 3) 0 := by
  funext i
  rcases i with j | j <;> fin_cases j <;> simp only [w0, W0_2, div_one] <;> simp [data2, hold2]

lemma k0_2 : k0 data2 = 1 / 6 := by simp only [k0, W0_2, div_one]; simp [data2]

lemma hold2_surj (w : Inst 1 2 → ℝ) :
    w = hold2 (w (Sum.inl 0)) (w (Sum.inr 0)) (w (Sum.inr 1)) := by
  funext i
  rcases i with j | j <;> fin_cases j <;> rfl

/-- Quadratic form of menu 2. -/
noncomputable def Qf2 (a p₁ p₂ : ℝ) : ℝ :=
  (3 / 50) ^ 2 * (a + p₁ + p₂) ^ 2 + (1 / 50) ^ 2 * (a / 2 + p₂ / 4) ^ 2
    + (3 / 100) ^ 2 * a ^ 2 + (1 / 200) ^ 2 * p₁ ^ 2 + (1 / 100) ^ 2 * p₂ ^ 2

/-- Trade parts of menu 2. -/
noncomputable def T2 (a p₁ p₂ : ℝ) : ℝ :=
  max (a - 1 / 2) 0 + max (-(a - 1 / 2)) 0 + max (p₁ - 1 / 3) 0 + max (-(p₁ - 1 / 3)) 0
    + max p₂ 0 + max (-p₂) 0

lemma quad2 (a p₁ p₂ : ℝ) :
    hold2 a p₁ p₂ ⬝ᵥ (covariance data2 *ᵥ hold2 a p₁ p₂) = Qf2 a p₁ p₂ := by
  rw [quad_eq, sum_scen]
  simp [data2, xi, hold2, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, sg, Qf2,
    Matrix.vecHead, Matrix.vecTail]
  ring

lemma tau2 (a p₁ p₂ : ℝ) : tau data2 (hold2 a p₁ p₂ - w0 data2) = T2 a p₁ p₂ / 2000 := by
  rw [w0_2]
  simp [tau, data2, hold2, Fintype.sum_sum_type, Fin.sum_univ_two, T2]
  ring

lemma cash2 (a p₁ p₂ : ℝ) :
    cash data2 (hold2 a p₁ p₂) = 1 / 6 - (a - 1 / 2) - (p₁ - 1 / 3) - p₂ - T2 a p₁ p₂ / 2000 := by
  have := tau2 a p₁ p₂
  rw [cash, this, k0_2, w0_2]
  simp [hold2, Fintype.sum_sum_type, Fin.sum_univ_two]
  try ring

lemma Q2_eq (a p₁ p₂ : ℝ) :
    Q2 (hold2 a p₁ p₂)
      = a / 50 + 201 / 10000 * p₁ + 17 / 800 * p₂ - Qf2 a p₁ p₂ / 2 - T2 a p₁ p₂ / 2000 := by
  simp only [Q2, beliefScore, Fin.sum_univ_one, pi1, one_mul, score, quad2, tau2]
  simp [exposure, active, etf, hold2, data2, par, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-! ### Certificates -/

lemma Qf2_pos {x y z : ℝ} (h : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < Qf2 x y z := by
  have hlow : (3 / 100) ^ 2 * x ^ 2 + (1 / 200) ^ 2 * y ^ 2 + (1 / 100) ^ 2 * z ^ 2 ≤ Qf2 x y z := by
    unfold Qf2
    nlinarith [sq_nonneg (x + y + z), sq_nonneg (x / 2 + z / 4)]
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  have hz := sq_nonneg z
  rcases h with h | h | h
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    nlinarith
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    nlinarith
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    nlinarith

lemma T2_F : T2 0 0 (11995 / 12006) = 1 / 2 + 1 / 3 + 11995 / 12006 := by
  unfold T2
  rw [max_eq_right (by norm_num), max_eq_left (by norm_num), max_eq_right (by norm_num),
    max_eq_left (by norm_num), max_eq_left (by norm_num), max_eq_right (by norm_num)]
  ring

lemma opt2F (a p₁ p₂ : ℝ) (ha : 0 ≤ a) (hp₁ : 0 ≤ p₁) (hc : 0 ≤ cash data2 (hold2 a p₁ p₂)) :
    Q2 (hold2 a p₁ p₂) ≤ Q2 (hold2 0 0 (11995 / 12006)) - Qf2 a p₁ (p₂ - 11995 / 12006) / 2 := by
  rw [Q2_eq, Q2_eq, T2_F]
  rw [cash2] at hc
  have e1 := max_parts (a - 1 / 2)
  have e2 := max_parts (p₁ - 1 / 3)
  have e3 := max_parts p₂
  have n1 := le_max_right (a - 1 / 2) 0
  have n2 := le_max_right (-(a - 1 / 2)) 0
  have n3 := le_max_right (p₁ - 1 / 3) 0
  have n4 := le_max_right (-(p₁ - 1 / 3)) 0
  have n5 := le_max_right p₂ 0
  have n6 := le_max_right (-p₂) 0
  unfold T2 at hc ⊢
  unfold Qf2
  linarith

lemma T2_E : T2 (1 / 2) 0 (2999 / 6003) = 1 / 3 + 2999 / 6003 := by
  unfold T2
  rw [sub_self, neg_zero, max_self, max_eq_right (by norm_num), max_eq_left (by norm_num),
    max_eq_left (by norm_num), max_eq_right (by norm_num)]
  ring

lemma opt2E (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hc : 0 ≤ cash data2 (hold2 (1 / 2) p₁ p₂)) :
    Q2 (hold2 (1 / 2) p₁ p₂)
      ≤ Q2 (hold2 (1 / 2) 0 (2999 / 6003)) - Qf2 0 p₁ (p₂ - 2999 / 6003) / 2 := by
  rw [Q2_eq, Q2_eq, T2_E]
  rw [cash2] at hc
  have e2 := max_parts (p₁ - 1 / 3)
  have e3 := max_parts p₂
  have n3 := le_max_right (p₁ - 1 / 3) 0
  have n4 := le_max_right (-(p₁ - 1 / 3)) 0
  have n5 := le_max_right p₂ 0
  have n6 := le_max_right (-p₂) 0
  unfold T2 at hc ⊢
  rw [sub_self, neg_zero, max_self] at hc ⊢
  unfold Qf2
  linarith

lemma Qf1_pos {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) : 0 < Qf1 x y := by
  have hlow : (3 / 100) ^ 2 * x ^ 2 + (1 / 200) ^ 2 * y ^ 2 ≤ Qf1 x y := by
    unfold Qf1
    nlinarith [sq_nonneg (x + y), sq_nonneg (x / 2)]
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  rcases h with h | h
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    nlinarith
  · have := pow_pos (abs_pos.mpr h) 2
    rw [sq_abs] at this
    nlinarith

lemma T1_F : T1 (1 / 2) (3001 / 6003) = 1000 / 6003 := by
  unfold T1
  rw [sub_self, neg_zero, max_self, max_eq_left (by norm_num), max_eq_right (by norm_num)]
  norm_num

lemma opt1F (a p : ℝ) (hc : 0 ≤ cash data1 (hold1 a p)) :
    Q1 (hold1 a p) ≤ Q1 (hold1 (1 / 2) (3001 / 6003)) - Qf1 (a - 1 / 2) (p - 3001 / 6003) / 2 := by
  rw [Q1_eq, Q1_eq, T1_F]
  rw [cash1] at hc
  have e1 := max_parts (a - 1 / 2)
  have e2 := max_parts (p - 1 / 3)
  have n1 := le_max_right (a - 1 / 2) 0
  have n2 := le_max_right (-(a - 1 / 2)) 0
  have n3 := le_max_right (p - 1 / 3) 0
  have n4 := le_max_right (-(p - 1 / 3)) 0
  unfold T1 at hc ⊢
  unfold Qf1
  linarith

/-! ### Class membership -/

lemma mem_F1 (a p : ℝ) : hold1 a p ∈ F data1 ↔
    (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ p ∧ p ≤ 1) ∧ 0 ≤ cash data1 (hold1 a p) := by
  simp [F, Sum.forall, Fin.forall_fin_one, hold1, data1, and_assoc]

lemma mem_E1 (a p : ℝ) : hold1 a p ∈ E data1 ↔ hold1 a p ∈ F data1 ∧ a = 1 / 2 := by
  refine and_congr Iff.rfl ?_
  rw [w0_1]
  constructor
  · intro h
    simpa [active, hold1] using congrFun h 0
  · intro h
    funext j
    fin_cases j
    simp [active, hold1, h]

lemma mem_F2 (a p₁ p₂ : ℝ) : hold2 a p₁ p₂ ∈ F data2 ↔
    (0 ≤ a ∧ a ≤ 1) ∧ ((0 ≤ p₁ ∧ p₁ ≤ 1) ∧ (0 ≤ p₂ ∧ p₂ ≤ 1)) ∧
      0 ≤ cash data2 (hold2 a p₁ p₂) := by
  simp [F, Sum.forall, Fin.forall_fin_one, Fin.forall_fin_two, hold2, data2, and_assoc]

lemma mem_E2 (a p₁ p₂ : ℝ) : hold2 a p₁ p₂ ∈ E data2 ↔ hold2 a p₁ p₂ ∈ F data2 ∧ a = 1 / 2 := by
  refine and_congr Iff.rfl ?_
  rw [w0_2]
  constructor
  · intro h
    simpa [active, hold2] using congrFun h 0
  · intro h
    funext j
    fin_cases j
    simp [active, hold2, h]

lemma N1 : N data1 = {hold1 (1 / 2) (1 / 3)} := by rw [N, w0_1]
lemma N2 : N data2 = {hold2 (1 / 2) (1 / 3) 0} := by rw [N, w0_2]

/-! ### Values at the candidates -/

lemma T1_N : T1 (1 / 2) (1 / 3) = 0 := by simp [T1]
lemma T2_N : T2 (1 / 2) (1 / 3) 0 = 0 := by simp [T2]

lemma cash1_F : cash data1 (hold1 (1 / 2) (3001 / 6003)) = 0 := by
  rw [cash1, T1_F]; norm_num
lemma cash2_E : cash data2 (hold2 (1 / 2) 0 (2999 / 6003)) = 0 := by
  rw [cash2, T2_E]; norm_num
lemma cash2_F : cash data2 (hold2 0 0 (11995 / 12006)) = 0 := by
  rw [cash2, T2_F]; norm_num

lemma Q1_F : Q1 (hold1 (1 / 2) (3001 / 6003)) = 61830113 / 3427920000 := by
  rw [Q1_eq, T1_F]; norm_num [Qf1]
lemma Q1_N : Q1 (hold1 (1 / 2) (1 / 3)) = 11033 / 720000 := by
  rw [Q1_eq, T1_N]; norm_num [Qf1]
lemma Q2_N : Q2 (hold2 (1 / 2) (1 / 3) 0) = 11033 / 720000 := by
  rw [Q2_eq, T2_N]; norm_num [Qf2]
lemma Q2_E : Q2 (hold2 (1 / 2) 0 (2999 / 6003)) = 2104284079 / 115315228800 := by
  rw [Q2_eq, T2_E]; norm_num [Qf2]
lemma Q2_F : Q2 (hold2 0 0 (11995 / 12006)) = 8512677811 / 461260915200 := by
  rw [Q2_eq, T2_F]; norm_num [Qf2]

/-! ### Unique optima -/

lemma F1_mem : hold1 (1 / 2) (3001 / 6003) ∈ F data1 :=
  (mem_F1 _ _).mpr ⟨by norm_num, by norm_num, by rw [cash1_F]⟩

lemma E1_mem : hold1 (1 / 2) (3001 / 6003) ∈ E data1 := (mem_E1 _ _).mpr ⟨F1_mem, rfl⟩

lemma unique1F : UniqueMax Q1 (F data1) (hold1 (1 / 2) (3001 / 6003)) := by
  refine ⟨F1_mem, fun w hw hne => ?_⟩
  rw [hold1_surj w] at hw hne ⊢
  obtain ⟨_, _, hc⟩ := (mem_F1 _ _).mp hw
  have hle := opt1F _ _ hc
  have hpos : 0 < Qf1 (w (Sum.inl 0) - 1 / 2) (w (Sum.inr 0) - 3001 / 6003) := by
    apply Qf1_pos
    by_contra h
    push Not at h
    apply hne
    rw [sub_eq_zero.mp h.1, sub_eq_zero.mp h.2]
  linarith

lemma unique1E : UniqueMax Q1 (E data1) (hold1 (1 / 2) (3001 / 6003)) :=
  ⟨E1_mem, fun w hw hne => unique1F.2 w hw.1 hne⟩

lemma E2_mem : hold2 (1 / 2) 0 (2999 / 6003) ∈ E data2 :=
  (mem_E2 _ _ _).mpr ⟨(mem_F2 _ _ _).mpr ⟨by norm_num, by norm_num, by rw [cash2_E]⟩, rfl⟩

lemma F2_mem : hold2 0 0 (11995 / 12006) ∈ F data2 :=
  (mem_F2 _ _ _).mpr ⟨by norm_num, by norm_num, by rw [cash2_F]⟩

lemma unique2F : UniqueMax Q2 (F data2) (hold2 0 0 (11995 / 12006)) := by
  refine ⟨F2_mem, fun w hw hne => ?_⟩
  rw [hold2_surj w] at hw hne ⊢
  obtain ⟨⟨ha, _⟩, ⟨⟨hp₁, _⟩, _⟩, hc⟩ := (mem_F2 _ _ _).mp hw
  have hle := opt2F _ _ _ ha hp₁ hc
  have hpos : 0 < Qf2 (w (Sum.inl 0)) (w (Sum.inr 0)) (w (Sum.inr 1) - 11995 / 12006) := by
    apply Qf2_pos
    by_contra h
    push Not at h
    apply hne
    rw [h.1, h.2.1, sub_eq_zero.mp h.2.2]
  linarith

lemma unique2E : UniqueMax Q2 (E data2) (hold2 (1 / 2) 0 (2999 / 6003)) := by
  refine ⟨E2_mem, fun w hw hne => ?_⟩
  rw [hold2_surj w] at hw hne ⊢
  obtain ⟨hF, ha⟩ := (mem_E2 _ _ _).mp hw
  obtain ⟨_, ⟨⟨hp₁, _⟩, _⟩, hc⟩ := (mem_F2 _ _ _).mp hF
  rw [ha] at hc hne ⊢
  have hle := opt2E _ _ hp₁ hc
  have hpos : 0 < Qf2 0 (w (Sum.inr 0)) (w (Sum.inr 1) - 2999 / 6003) := by
    apply Qf2_pos
    right
    by_contra h
    push Not at h
    apply hne
    rw [h.1, sub_eq_zero.mp h.2]
  linarith

lemma uniqueN {ι : Type} (f : (ι → ℝ) → ℝ) (w : ι → ℝ) : UniqueMax f {w} w :=
  ⟨rfl, fun _ hw hne => absurd hw hne⟩

lemma optimaTable : OptimaTable := by
  refine ⟨by rw [N1]; exact uniqueN _ _, unique1E, unique1F, by rw [N2]; exact uniqueN _ _,
    unique2E, unique2F, ?_, ?_, Q1_N, cash1_F, ?_, Q1_F, ?_, ?_, Q2_N, cash2_E, ?_, Q2_E,
    cash2_F, ?_, Q2_F⟩
  · rw [cash1, T1_N]; norm_num
  · rw [tau1, T1_N]; norm_num
  · rw [tau1, T1_F]; norm_num
  · rw [cash2, T2_N]; norm_num
  · rw [tau2, T2_N]; norm_num
  · rw [tau2, T2_E]; norm_num
  · rw [tau2, T2_F]; norm_num

lemma gaps : Gaps := by
  refine ⟨sub_self _, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Q2_F, Q2_E]; norm_num
  · rw [Q1_N, Q1_F]; norm_num
  · rw [Q2_N, Q2_E]; norm_num
  · rw [Q2_N, Q2_F]; norm_num
  · rw [w0_1]; simp [hold1]
  · rw [w0_2]; simp [hold2]; norm_num
  · rw [w0_1]; simp [hold1]; norm_num

/-! ### Exposure obstructions -/

lemma exposure1 (a p : ℝ) : exposure data1 (hold1 a p) = ![a + p, a / 2] := by
  funext k
  fin_cases k
  · simp [exposure, active, etf, hold1, data1, mulVec, dotProduct]
  · simp [exposure, active, etf, hold1, data1, mulVec, dotProduct]
    ring

lemma exposure2 (a p₁ p₂ : ℝ) :
    exposure data2 (hold2 a p₁ p₂) = ![a + p₁ + p₂, a / 2 + p₂ / 4] := by
  funext k
  fin_cases k <;> simp [exposure, active, etf, hold2, data2, mulVec, dotProduct, Fin.sum_univ_two]
    <;> ring

lemma vec2_eq {x y u v : ℝ} : (![x, y] : Fin 2 → ℝ) = ![u, v] ↔ x = u ∧ y = v := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma obstructions : Obstructions := by
  refine ⟨⟨(mem_F1 0 0).mpr ⟨by norm_num, by norm_num, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [cash1]
    unfold T1
    rw [max_eq_right (by norm_num), max_eq_left (by norm_num), max_eq_right (by norm_num),
      max_eq_left (by norm_num)]
    norm_num
  · rw [w0_1, exposure1, exposure1]
    funext k
    fin_cases k <;> simp <;> norm_num
  · rintro ⟨d, hd⟩
    have := congrFun hd 1
    simp [data1, mulVec, dotProduct] at this
    norm_num at this
  · refine Set.eq_univ_of_forall fun δ => ⟨![δ 0 - 4 * δ 1, 4 * δ 1], ?_⟩
    funext k
    fin_cases k <;> simp [data2, mulVec, dotProduct, Fin.sum_univ_two]
  · intro p₁ p₂
    rw [exposure2, exposure2, vec2_eq]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨rfl, rfl⟩
      constructor <;> norm_num
  · intro w hw
    rw [hold2_surj w] at hw ⊢
    obtain ⟨hF, ha⟩ := (mem_E2 _ _ _).mp hw
    obtain ⟨_, ⟨_, ⟨hp₂, _⟩⟩, _⟩ := (mem_F2 _ _ _).mp hF
    rw [exposure2, exposure2, ha]
    intro h
    rw [vec2_eq] at h
    linarith [h.2]

/-! ### Validity of the instances -/

lemma sg_bounds (b : Bool) : -1 ≤ sg b ∧ sg b ≤ 1 := by
  cases b <;> norm_num [sg]

lemma valid1 : ValidM2 data1 := by
  refine ⟨W0_1, ⟨by rw [W0_1]; norm_num, ?_, by norm_num [data1], ?_⟩, ?_, ?_, ?_,
    by norm_num [data1], fun s => by norm_num [data1], ?_, ⟨?_, ?_, ?_⟩,
    fun t => by norm_num [pi1], by simp [pi1], ?_⟩
  · intro i; rcases i with j | j <;> fin_cases j <;> norm_num [data1]
  · intro i; rw [w0_1]; rcases i with j | j <;> fin_cases j <;> norm_num [data1, hold1]
  · intro i; norm_num [data1]
  · intro i; norm_num [data1]
  · intro i; norm_num [data1]
  · norm_num [MassesSumToOne, data1]
  · funext k; fin_cases k <;> norm_num [data1, sum_scen, sg]
  · funext k; fin_cases k; norm_num [data1, sum_scen, sg]
  · funext k; fin_cases k; norm_num [data1, sum_scen, sg]
  · rintro t ⟨b₁, b₂, b₃, b₄, b₅⟩ i
    have h1 := sg_bounds b₁
    have h2 := sg_bounds b₂
    have h3 := sg_bounds b₃
    have h4 := sg_bounds b₄
    rcases i with j | j <;> fin_cases j <;>
      simp [ret, data1, par, Matrix.vecHead, Matrix.vecTail] <;> linarith

lemma valid2 : ValidM2 data2 := by
  refine ⟨W0_2, ⟨by rw [W0_2]; norm_num, ?_, by norm_num [data2], ?_⟩, ?_, ?_, ?_,
    by norm_num [data2], fun s => by norm_num [data2], ?_, ⟨?_, ?_, ?_⟩,
    fun t => by norm_num [pi1], by simp [pi1], ?_⟩
  · intro i; rcases i with j | j <;> fin_cases j <;> norm_num [data2]
  · intro i; rw [w0_2]; rcases i with j | j <;> fin_cases j <;> norm_num [data2, hold2]
  · intro i; norm_num [data2]
  · intro i; norm_num [data2]
  · intro i; norm_num [data2]
  · norm_num [MassesSumToOne, data2]
  · funext k; fin_cases k <;> norm_num [data2, sum_scen, sg]
  · funext k; fin_cases k; norm_num [data2, sum_scen, sg]
  · funext k; fin_cases k <;> norm_num [data2, sum_scen, sg]
  · rintro t ⟨b₁, b₂, b₃, b₄, b₅⟩ i
    have h1 := sg_bounds b₁
    have h2 := sg_bounds b₂
    have h3 := sg_bounds b₃
    have h4 := sg_bounds b₄
    have h5 := sg_bounds b₅
    rcases i with j | j <;> fin_cases j <;>
      simp [ret, data2, par, Matrix.vecHead, Matrix.vecTail] <;> linarith

lemma validInstances : ValidInstances := by
  refine ⟨valid1, valid2, fun s => ⟨?_, ?_⟩⟩ <;>
    simp [ret, data1, data2, par, Matrix.vecHead, Matrix.vecTail]

theorem proof : Standalone.M2IncompleteSubstitution.statement :=
  ⟨validInstances, optimaTable, gaps, obstructions⟩

end Novel.M2IncompleteSubstitutionProof

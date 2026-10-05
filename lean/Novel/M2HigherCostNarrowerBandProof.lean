import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Standalone.M2HigherCostNarrowerBand
import Novel.M2NoActiveTradeBandProof

/-!
# Proof of claim 010: a higher common switching-cost rate can strictly narrow the band

This proof uses claim 009's machine-checked results (band table, multiplier interval, uniqueness,
alpha family) by importing `Novel.M2NoActiveTradeBandProof`, matching the claim's dependence on
claim 009. What is proved here is instance-specific: the covariance, the criterion, the unique
ETF-only optimum `(1/2, 1/(2(1 + κ)))`, the values of `I`, `α_c`, `L`, `U`, the domain `J`, and
M2 validity.
-/

namespace Novel.M2HigherCostNarrowerBandProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2HigherCostNarrowerBand Novel.M2NoActiveTradeBandProof
open Standalone.M2NoActiveTradeBand hiding hold

variable {κ : ℝ}

/-! ### Basic computations -/

lemma sum_scen (f : Scen → ℝ) :
    ∑ s, f s = ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool, ∑ b₄ : Bool, ∑ b₅ : Bool,
      f (b₁, b₂, b₃, b₄, b₅) := by
  simp only [Fintype.sum_prod_type]

lemma sg_bounds (b : Bool) : -1 ≤ sg b ∧ sg b ≤ 1 := by cases b <;> norm_num [sg]

lemma hold_surj (w : Inst 1 1 → ℝ) : w = hold (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

lemma W0_10 : W0 (data10 κ) = 1 := by
  rw [W0, sum_inst]; simp [data10]; norm_num

lemma w0_10 : w0 (data10 κ) = hold (1 / 2) 0 := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
    simp only [w0, W0_10, div_one] <;> simp [data10, hold]

lemma k0_10 : k0 (data10 κ) = 1 / 2 := by
  simp only [k0, W0_10, div_one]; simp [data10]

lemma cov_AA : covariance (data10 κ) (Sum.inl 0) (Sum.inl 0) = 23 / 5000 := by
  simp only [covariance, sum_scen]
  simp [data10, xi, sg, Matrix.vecHead, Matrix.vecTail]
  norm_num

lemma cov_AE : covariance (data10 κ) (Sum.inl 0) (Sum.inr 0) = 9 / 2500 := by
  simp only [covariance, sum_scen]
  simp [data10, xi, sg, Matrix.vecHead, Matrix.vecTail]
  norm_num

lemma cov_EA : covariance (data10 κ) (Sum.inr 0) (Sum.inl 0) = 9 / 2500 := by
  simp only [covariance, sum_scen]
  simp [data10, xi, sg, Matrix.vecHead, Matrix.vecTail]
  norm_num

lemma cov_EE : covariance (data10 κ) (Sum.inr 0) (Sum.inr 0) = 29 / 8000 := by
  simp only [covariance, sum_scen]
  simp [data10, xi, sg, Matrix.vecHead, Matrix.vecTail]
  norm_num

lemma cov_mulVec (a p : ℝ) :
    (covariance (data10 κ) *ᵥ hold a p) (Sum.inl 0) = 23 / 5000 * a + 9 / 2500 * p ∧
    (covariance (data10 κ) *ᵥ hold a p) (Sum.inr 0) = 9 / 2500 * a + 29 / 8000 * p := by
  simp only [mulVec, dotProduct, sum_inst, Fin.sum_univ_one, hold, Sum.elim_inl, Sum.elim_inr,
    cov_AA, cov_AE, cov_EA, cov_EE]
  exact ⟨trivial, trivial⟩

lemma quad10 (a p : ℝ) :
    hold a p ⬝ᵥ (covariance (data10 κ) *ᵥ hold a p)
      = 23 / 5000 * a ^ 2 + 9 / 1250 * a * p + 29 / 8000 * p ^ 2 := by
  rw [dotProduct, sum_inst, Fin.sum_univ_one, (cov_mulVec a p).1, (cov_mulVec a p).2]
  simp only [hold, Sum.elim_inl, Sum.elim_inr]
  ring

lemma tau10 (a p : ℝ) :
    tau (data10 κ) (hold a p - w0 (data10 κ))
      = κ * (max (a - 1 / 2) 0 + max (-(a - 1 / 2)) 0 + max p 0 + max (-p) 0) := by
  rw [w0_10, tau_eq_sum, sum_inst, Fin.sum_univ_one]
  simp only [cst, data10, hold, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, sub_zero]
  ring

lemma cash10 (a p : ℝ) :
    cash (data10 κ) (hold a p) = 1 - a - p - tau (data10 κ) (hold a p - w0 (data10 κ)) := by
  rw [cash, k0_10, sum_inst, Fin.sum_univ_one, w0_10]
  simp only [hold, Sum.elim_inl, Sum.elim_inr]
  ring

lemma lamBar10 : lamBar par10 pi10 = ![1 / 50, 1 / 200] := by
  funext k
  fin_cases k <;>
    simp [lamBar, beliefMean, par10, pi10, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

lemma pi10_sum : ∑ h, pi10 h = 1 := by
  norm_num [pi10]

lemma Qx10 (x a p : ℝ) :
    Qx (data10 κ) par10 pi10 x (hold a p)
      = (9 / 400 + x) * a + 201 / 10000 * p
        - (23 / 5000 * a ^ 2 + 9 / 1250 * a * p + 29 / 8000 * p ^ 2) / 2
        - tau (data10 κ) (hold a p - w0 (data10 κ)) := by
  rw [Qx_eq _ _ _ pi10_sum, quad10]
  simp [meanVec, lamBar10, data10, dotProduct, mulVec, Fin.sum_univ_two, hold]
  ring

/-! ### The ETF-only optimum -/

lemma mem_E10 (a p : ℝ) :
    hold a p ∈ E (data10 κ) ↔ (0 ≤ p ∧ p ≤ 1 / 2) ∧ 0 ≤ cash (data10 κ) (hold a p) ∧ a = 1 / 2 := by
  constructor
  · rintro ⟨⟨hb, hc⟩, ha⟩
    have := congrFun ha 0
    rw [w0_10] at this
    have hp := hb (Sum.inr 0)
    simp only [hold, data10, Sum.elim_inr] at hp
    exact ⟨hp, hc, by simpa [active, hold] using this⟩
  · rintro ⟨hp, hc, rfl⟩
    refine ⟨⟨fun i => ?_, hc⟩, by rw [w0_10]; rfl⟩
    rcases i with k | k
    · simp [hold, data10]; norm_num
    · simp only [hold, data10, Sum.elim_inr]; exact hp

/-- The unique ETF-only optimum `p_E = 1/(2(1 + κ))` for `0 ≤ κ ≤ 1/2000`. -/
lemma Eopt (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2000) {pE : ℝ} (hpE : pE * (2 * (1 + κ)) = 1) (x : ℝ) :
    hold (1 / 2) pE ∈ maximizers (Qx (data10 κ) par10 pi10 x) (E (data10 κ)) ∧
    ∀ w ∈ maximizers (Qx (data10 κ) par10 pi10 x) (E (data10 κ)), w = hold (1 / 2) pE := by
  have hpE0 : 0 < pE := by nlinarith
  have hpE1 : pE ≤ 1 / 2 := by nlinarith
  have htauE : ∀ p, 0 ≤ p → tau (data10 κ) (hold (1 / 2) p - w0 (data10 κ)) = κ * p := by
    intro p hp
    rw [tau10, sub_self, neg_zero, max_self, max_eq_left hp, max_eq_right (by linarith)]
    ring
  have hcashE : ∀ p, 0 ≤ p → cash (data10 κ) (hold (1 / 2) p) = 1 / 2 - (1 + κ) * p := by
    intro p hp; rw [cash10, htauE p hp]; ring
  have hQ : ∀ p, 0 ≤ p → Qx (data10 κ) par10 pi10 x (hold (1 / 2) p)
      = (9 / 400 + x) / 2 + (201 / 10000 - 9 / 2500 / 2 - κ) * p - 23 / 5000 / 8
        - 29 / 16000 * p ^ 2 := by
    intro p hp; rw [Qx10, htauE p hp]; ring
  have hmemE : hold (1 / 2) pE ∈ E (data10 κ) :=
    (mem_E10 _ _).mpr ⟨⟨hpE0.le, hpE1⟩, by rw [hcashE _ hpE0.le]; nlinarith, rfl⟩
  have hbetter : ∀ w ∈ E (data10 κ), w ≠ hold (1 / 2) pE →
      Qx (data10 κ) par10 pi10 x w < Qx (data10 κ) par10 pi10 x (hold (1 / 2) pE) := by
    intro w hw hne
    rw [hold_surj w] at hw hne ⊢
    obtain ⟨⟨hp0, hp1⟩, hc, ha⟩ := (mem_E10 _ _).mp hw
    rw [ha] at hc hne ⊢
    rw [hcashE _ hp0] at hc
    have hle : w (Sum.inr 0) ≤ pE := by nlinarith
    have hlt : w (Sum.inr 0) < pE := lt_of_le_of_ne hle fun h => hne (by rw [h])
    rw [hQ _ hp0, hQ _ hpE0.le]
    nlinarith [mul_pos (sub_pos.mpr hlt)
      (by nlinarith : (0 : ℝ) < 201 / 10000 - 9 / 2500 / 2 - κ - 29 / 16000 * (pE + w (Sum.inr 0)))]
  refine ⟨⟨hmemE, fun w hw => ?_⟩, fun w hw => ?_⟩
  · by_cases h : w = hold (1 / 2) pE
    · rw [h]
    · exact (hbetter w hw h).le
  · by_contra h
    exact absurd (hw.2 _ hmemE) (not_le.mpr (hbetter w hw.1 h))

/-! ### Validity -/

lemma setting10 (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) : BandSetting (data10 κ) pi10 := by
  refine ⟨⟨by rw [W0_10]; norm_num, fun i => ?_, by simp [data10], fun i => ?_⟩, fun i => ?_,
    fun i => ?_, fun i => ?_, by simp [data10], fun s => by simp [data10], ?_, pi10_sum⟩
  · rcases i with k | k <;> simp [data10]
  · rw [w0_10]; rcases i with k | k <;> norm_num [hold, data10]
  · exact ⟨hκ0, hκ0⟩
  · exact ⟨hκ1, hκ1⟩
  · rcases i with k | k <;> norm_num [data10]
  · norm_num [MassesSumToOne, data10]

lemma centered10 : CenteredShocks (data10 κ) := by
  refine ⟨?_, ?_, ?_⟩
  · funext k; fin_cases k <;> norm_num [data10, sum_scen, sg]
  · funext k; fin_cases k; norm_num [data10, sum_scen, sg]
  · funext k; fin_cases k; norm_num [data10, sum_scen, sg]

lemma pos10 : ∀ h s i, 0 < 1 + ret (data10 κ) (par10 h) s i := by
  rintro ⟨h₁, h₂⟩ ⟨b₁, b₂, b₃, b₄, b₅⟩ i
  have := sg_bounds b₁
  have := sg_bounds b₂
  have := sg_bounds b₃
  have := sg_bounds b₄
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> fin_cases h₁ <;>
    fin_cases h₂ <;> simp [ret, data10, par10, Matrix.vecHead, Matrix.vecTail] <;> linarith

lemma abar10 : abar0 par10 pi10 = 0 := by
  simp [abar0, par10, pi10, Fintype.sum_prod_type]; norm_num

/-- The active gross return along the family at `(h, s)`, written out. -/
lemma retA10 (x : ℝ) (h : Fin 2 × Fin 2) (s : Scen) :
    1 + ret (data10 κ) (famPar par10 pi10 x h) s (Sum.inl 0)
      = 1 + ![3 / 200, 1 / 40] h.1 + 1 / 400 + 3 / 50 * sg s.1 + 1 / 100 * sg s.2.1
        + ![-1 / 400, 1 / 400] h.2 + x + 3 / 100 * sg s.2.2.1 := by
  simp only [ret, famPar, abar10, Sum.elim_inl, Pi.add_apply, data10, par10, mulVec, dotProduct,
    Fin.sum_univ_two]
  simp
  ring

lemma J10 : Jset (data10 κ) par10 pi10 = Set.Ioi (-183 / 200) := by
  ext x
  simp only [Jset, Set.mem_ofPred_eq, Set.mem_Ioi, retA10]
  constructor
  · intro H
    have := H (0, 0) (false, false, false, false, false)
    simp [sg] at this
    linarith
  · rintro hx ⟨h₁, h₂⟩ ⟨b₁, b₂, b₃, b₄, b₅⟩
    have := sg_bounds b₁
    have := sg_bounds b₂
    have := sg_bounds b₃
    fin_cases h₁ <;> fin_cases h₂ <;> simp <;> linarith

/-! ### Positive definiteness and uniqueness -/

lemma pd10 (v : Inst 1 1 → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (covariance (data10 κ) *ᵥ v) := by
  rw [hold_surj v, quad10]
  set a := v (Sum.inl 0)
  set p := v (Sum.inr 0)
  have key : 23 / 5000 * a ^ 2 + 9 / 1250 * a * p + 29 / 8000 * p ^ 2
      = 23 / 5000 * (a + 18 / 23 * p) ^ 2 + 743 / 920000 * p ^ 2 := by ring
  rw [key]
  by_contra h
  push Not at h
  have hp : p = 0 := by nlinarith [sq_nonneg (a + 18 / 23 * p), sq_nonneg p]
  have ha : a = 0 := by rw [hp] at h; nlinarith [sq_nonneg a]
  apply hv
  rw [hold_surj v]
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> simp [hold, a, p, ha, hp]

/-! ### Values at the ETF-only optimum -/

lemma gE10 (p : ℝ) :
    gE (data10 κ) par10 pi10 (hold (1 / 2) p) 0 = 201 / 10000 - (9 / 2500 * (1 / 2) + 29 / 8000 * p) := by
  rw [gE, (cov_mulVec (1 / 2) p).2, lamBar10]
  simp [data10, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

lemma alphaC10 (p : ℝ) :
    alphaC (data10 κ) par10 pi10 (hold (1 / 2) p) = 23 / 5000 * (1 / 2) + 9 / 2500 * p - 9 / 400 := by
  rw [alphaC, (cov_mulVec (1 / 2) p).1, lamBar10]
  simp [data10, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

lemma ell10 {p : ℝ} (hp : 0 < p) : ellE (data10 κ) (hold (1 / 2) p) 0 = κ := by
  unfold ellE
  rw [w0_10]
  simp [hold, hp, data10]

lemma u10 {p : ℝ} (hp : 0 ≤ p) : uE (data10 κ) (hold (1 / 2) p) 0 = κ := by
  unfold uE
  rw [w0_10]
  simp [hold, not_lt.mpr hp, data10]

lemma cash_opt (hκ : 0 ≤ κ) {pE : ℝ} (hpE : pE * (2 * (1 + κ)) = 1) :
    cash (data10 κ) (hold (1 / 2) pE) = 0 := by
  have hp0 : 0 ≤ pE := by nlinarith
  rw [cash10, tau10, sub_self, neg_zero, max_self, max_eq_left hp0, max_eq_right (by linarith)]
  nlinarith

lemma filter_univ1 (P : Fin 1 → Prop) [DecidablePred P] (h : P 0) :
    (Finset.univ.filter P) = {0} := by
  ext j; obtain rfl : j = 0 := Subsingleton.elim _ _; simp [h]

lemma filter_empty1 (P : Fin 1 → Prop) [DecidablePred P] (h : ¬ P 0) :
    (Finset.univ.filter P) = ∅ := by
  ext j; obtain rfl : j = 0 := Subsingleton.elim _ _; simp [h]

/-- The generic row: from claim 009, with `lo`, `hi` supplied. -/
lemma row_of (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2000) {pE : ℝ} (hpE : pE * (2 * (1 + κ)) = 1) {lo' hi' : ℝ}
    (hlo : lo (data10 κ) par10 pi10 (hold (1 / 2) pE) = lo')
    (hhi : hi (data10 κ) par10 pi10 (hold (1 / 2) pE) = hi')
    (hLJ : -183 / 200 < 23 / 5000 * (1 / 2) + 9 / 2500 * pE - 9 / 400 - κ
      + (1 - κ) * lo') :
    Row κ pE (Set.Icc lo' hi')
      (23 / 5000 * (1 / 2) + 9 / 2500 * pE - 9 / 400)
      (23 / 5000 * (1 / 2) + 9 / 2500 * pE - 9 / 400 - κ + (1 - κ) * lo')
      (23 / 5000 * (1 / 2) + 9 / 2500 * pE - 9 / 400 + κ + (1 + κ) * hi') := by
  have hS := setting10 hκ0 (by linarith : κ < 1)
  have hE := Eopt hκ0 hκ1 hpE
  have hwE := (hE 0).1
  have hall := Emax_all (data10 κ) par10 pi10 pi10_sum hwE
  obtain ⟨hI1, _, _, _, hfin⟩ := interval hS hall hwE.1
  have hF : HiFinite (data10 κ) par10 pi10 (hold (1 / 2) pE) :=
    hfin (by rw [w0_10]; simp [hold]; norm_num)
  have hC := (bandTable hS hwE).1 (by rw [w0_10]; simp [hold])
    (by rw [w0_10]; simp [hold, data10]; norm_num)
  refine ⟨hE, cash_opt hκ0 hpE, by rw [hI1 hF, hlo, hhi], alphaC10 _, ?_, ?_⟩
  · rw [hC, Lb, Ub, alphaC10, hlo, hhi]
    simp [data10]
  · rw [hC, J10]
    intro x hx
    simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢
    rw [Lb, alphaC10, hlo] at hx
    simp only [data10] at hx
    linarith [hx.1]

/-! ### `lo` and `hi` at the optimum -/

/-- The common ETF bound value `(g_E - κ)/(1 + κ)` at `p`. -/
noncomputable def vE (κ p : ℝ) : ℝ := (201 / 10000 - (9 / 2500 * (1 / 2) + 29 / 8000 * p) - κ) / (1 + κ)

lemma hiSet10 {p : ℝ} (hp : 0 < p) : hiSet (data10 κ) par10 pi10 (hold (1 / 2) p) = {vE κ p} := by
  ext y
  simp only [hiSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨j, _, rfl⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [gE10, ell10 hp, vE]
  · rintro rfl
    exact ⟨0, by simpa [hold] using hp, by rw [gE10, ell10 hp, vE]⟩

lemma loSet10_int {p : ℝ} (hp : 0 ≤ p) (hlt : p < 1 / 2) :
    loSet (data10 κ) par10 pi10 (hold (1 / 2) p) = {0, vE κ p} := by
  ext y
  simp only [loSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨j, _, rfl⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [gE10, u10 hp, vE]
  · rintro rfl
    exact ⟨0, by simpa [hold, data10] using hlt, by rw [gE10, u10 hp, vE]⟩

lemma loSet10_cap : loSet (data10 κ) par10 pi10 (hold (1 / 2) (1 / 2)) = {0} := by
  ext y
  simp only [loSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨j, hj, _⟩)
    · exact h
    · simp [hold, data10] at hj
  · exact Or.inl

lemma max'_eq {s : Finset ℝ} (hs : s.Nonempty) {v : ℝ} (hv : v ∈ s) (hle : ∀ y ∈ s, y ≤ v) :
    s.max' hs = v :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hv)

lemma min'_eq {s : Finset ℝ} (hs : s.Nonempty) {v : ℝ} (hv : v ∈ s) (hle : ∀ y ∈ s, v ≤ y) :
    s.min' hs = v :=
  le_antisymm (Finset.min'_le _ _ hv) (Finset.le_min' _ _ _ hle)

lemma hi10 {p : ℝ} (hp : 0 < p) (hc : cash (data10 κ) (hold (1 / 2) p) = 0) :
    hi (data10 κ) par10 pi10 (hold (1 / 2) p) = vE κ p := by
  have hc' : ¬ 0 < cash (data10 κ) (hold (1 / 2) p) := by rw [hc]; exact lt_irrefl 0
  have hne : (hiSet (data10 κ) par10 pi10 (hold (1 / 2) p)).Nonempty := by
    rw [hiSet10 hp]; exact Finset.singleton_nonempty _
  simp only [hi, hc', ↓reduceIte, hne, ↓reduceDIte]
  exact min'_eq hne (by rw [hiSet10 hp]; exact Finset.mem_singleton_self _)
    (fun y hy => by rw [hiSet10 hp, Finset.mem_singleton] at hy; rw [hy])

lemma lo10_cap (hc : cash (data10 κ) (hold (1 / 2) (1 / 2)) = 0) :
    lo (data10 κ) par10 pi10 (hold (1 / 2) (1 / 2)) = 0 := by
  have hc' : ¬ 0 < cash (data10 κ) (hold (1 / 2) (1 / 2)) := by rw [hc]; exact lt_irrefl 0
  simp only [lo, hc', ↓reduceIte]
  exact max'_eq _ (by rw [loSet10_cap]; exact Finset.mem_singleton_self _)
    (fun y hy => by rw [loSet10_cap, Finset.mem_singleton] at hy; rw [hy])

lemma lo10_int {p : ℝ} (hp : 0 ≤ p) (hlt : p < 1 / 2) (hv : 0 ≤ vE κ p)
    (hc : cash (data10 κ) (hold (1 / 2) p) = 0) :
    lo (data10 κ) par10 pi10 (hold (1 / 2) p) = vE κ p := by
  have hc' : ¬ 0 < cash (data10 κ) (hold (1 / 2) p) := by rw [hc]; exact lt_irrefl 0
  simp only [lo, hc', ↓reduceIte]
  refine max'_eq _ (by rw [loSet10_int hp hlt]; simp) (fun y hy => ?_)
  rw [loSet10_int hp hlt, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact hv
  · exact le_rfl

/-! ### The two rows and the theorem -/

lemma row0 : Row 0 (1 / 2) (Set.Icc 0 (1319 / 80000)) (-23 / 1250) (-23 / 1250) (-153 / 80000) := by
  have hpE : (1 / 2 : ℝ) * (2 * (1 + 0)) = 1 := by norm_num
  have hc := cash_opt (κ := 0) le_rfl hpE
  have hlo := lo10_cap hc
  have hhi := hi10 (κ := 0) (by norm_num : (0 : ℝ) < 1 / 2) hc
  have := row_of (κ := 0) le_rfl (by norm_num) hpE hlo hhi (by norm_num)
  convert this using 2 <;> norm_num [vE]

lemma row1 : Row (1 / 2000) (1000 / 2001) {11032 / 690345} (-61367 / 3335000)
    (-808663 / 276138000) (-38269 / 20010000) := by
  have hpE : (1000 / 2001 : ℝ) * (2 * (1 + 1 / 2000)) = 1 := by norm_num
  have hc := cash_opt (κ := 1 / 2000) (by norm_num) hpE
  have hv : vE (1 / 2000) (1000 / 2001) = 11032 / 690345 := by norm_num [vE]
  have hlo := lo10_int (κ := 1 / 2000) (by norm_num : (0 : ℝ) ≤ 1000 / 2001) (by norm_num)
    (by rw [hv]; norm_num) hc
  have hhi := hi10 (κ := 1 / 2000) (by norm_num : (0 : ℝ) < 1000 / 2001) hc
  rw [hv] at hlo hhi
  have := row_of (κ := 1 / 2000) (by norm_num) le_rfl hpE hlo hhi (by norm_num)
  rw [Set.Icc_self] at this
  convert this using 2 <;> norm_num

theorem proof : Standalone.M2HigherCostNarrowerBand.statement := by
  refine ⟨fun κ hκ => ?_, ⟨row0, row1, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    fun b₁ b₂ s₁ s₂ lo hi => ⟨by ring, by ring⟩⟩
  have hκ' : 0 ≤ κ ∧ κ ≤ 1 / 2000 := by
    rcases hκ with rfl | h
    · norm_num
    · rw [Set.mem_singleton_iff] at h; rw [h]; norm_num
  have hS := setting10 hκ'.1 (by linarith [hκ'.2])
  refine ⟨hS, fun i => ⟨by simp [data10]; linarith [hκ'.2], by simp [data10]; linarith [hκ'.2]⟩,
    centered10, pos10, J10, pd10, fun x w w' hw hw' =>
      (uniqueness hS (by simp [data10]) pd10 x).1 w w' hw hw'⟩

end Novel.M2HigherCostNarrowerBandProof

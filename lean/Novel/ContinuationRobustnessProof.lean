import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.ContinuationRobustness
import Novel.M3FiniteContinuationProof
import Novel.OppositeContinuationEffectsProof

/-!
# Proof of claim 013: opposite continuation effects with risk, partial learning and uncertain alpha

This proof uses claim 011's machine-checked results (attainment, `V < 0`, class and CE orders) and
claim 012's positive-part and cost bookkeeping ideas, importing both proof modules (`depends_on:
[11, 12]`; Q-04).
* **CE bounds:** a policy with every path's wealth at least `L` gives `CE ≥ L`. `CE ≤ E[W₂]` by
  Jensen for `exp`, proved from `exp x ≥ e^m (1 + x - m)`. A uniform strict `Φ` bound gives a
  strict CE bound.
* **The instance:** the finite 4 × 4 × 4 path sums are expanded exactly for the needed moments.
* **The `83/80` bound:** `exp(3/4) > 2` comes from `1 + x + x²/2 ≤ exp x`.
-/

namespace Novel.ContinuationRobustnessProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
  Standalone.ContinuationRobustness Novel.M3FiniteContinuationProof
open Novel.OppositeContinuationEffectsProof (aS pS aS_pos pS_pos exp_facts)

variable {δ bA bE sA sE : ℝ}

/-! ### Signs and gross returns -/

lemma sg_cases (b : Bool) : sg b = 1 ∨ sg b = -1 := by cases b <;> simp [sg]

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by cases b <;> norm_num [sg]

lemma sg_bounds (b : Bool) : -1 ≤ sg b ∧ sg b ≤ 1 := by cases b <;> norm_num [sg]

/-- Shorthand for the instance. -/
noncomputable abbrev R (δ bA bE sA sE : ℝ) : M3 1 2 (Bool × Bool) (Bool × Bool) :=
  rbInst δ bA bE sA sE

/-- Active gross return `1 + σ/2 + δ(ξ + s_A)`. -/
noncomputable def gA (δ : ℝ) (t s : Bool × Bool) : ℝ := 1 + sg t.1 / 2 + δ * (sg t.2 + sg s.1)

/-- ETF gross return `1 - σ/2 + δ s_E`. -/
noncomputable def gE (δ : ℝ) (t s : Bool × Bool) : ℝ := 1 - sg t.1 / 2 + δ * sg s.2

lemma ret_A (t s : Bool × Bool) :
    1 + ret (R δ bA bE sA sE).D ((R δ bA bE sA sE).par t) s (Sum.inl 0) = gA δ t s := by
  simp [ret, rbInst, rbData, rbPar, gA, Matrix.vecHead, Matrix.vecTail]
  ring

lemma ret_E (t s : Bool × Bool) :
    1 + ret (R δ bA bE sA sE).D ((R δ bA bE sA sE).par t) s (Sum.inr 0) = gE δ t s := by
  simp [ret, rbInst, rbData, rbPar, gE, Matrix.vecHead, Matrix.vecTail]
  ring

lemma W0_rb : W0 (R δ bA bE sA sE).D = 1 := by simp [W0, rbInst, rbData]

lemma sum_inst1 (f : Inst 1 1 → ℝ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

lemma gA_bounds (hδ : 0 ≤ δ) (t s : Bool × Bool) :
    1 + sg t.1 / 2 - 2 * δ ≤ gA δ t s ∧ gA δ t s ≤ 1 + sg t.1 / 2 + 2 * δ := by
  have h1 := sg_bounds t.2
  have h2 := sg_bounds s.1
  unfold gA
  constructor <;> nlinarith

lemma gE_bounds (hδ : 0 ≤ δ) (t s : Bool × Bool) :
    1 - sg t.1 / 2 - δ ≤ gE δ t s ∧ gE δ t s ≤ 1 - sg t.1 / 2 + δ := by
  have h1 := sg_bounds s.2
  unfold gE
  constructor <;> nlinarith

/-! ### Validity, risk and uncertain alpha -/

lemma gross_pos (hr : InRange δ bA bE sA sE) (t s : Bool × Bool) (i : Inst 1 1) :
    0 < 1 + ret (R δ bA bE sA sE).D ((R δ bA bE sA sE).par t) s i := by
  obtain ⟨hδ0, hδ1, _⟩ := hr
  have hs := sg_bounds t.1
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
  · rw [ret_A]; have := (gA_bounds hδ0.le t s).1; linarith
  · rw [ret_E]; have := (gE_bounds hδ0.le t s).1; linarith

lemma setting (hr : InRange δ bA bE sA sE) : M3Setting (R δ bA bE sA sE) := by
  obtain ⟨hδ0, hδ1, h1, h2, h3, h4, h5, h6, h7, h8⟩ := id hr
  refine ⟨by norm_num [rbInst], fun s => by norm_num [rbInst, rbData],
    by norm_num [rbInst, rbData], fun t => by norm_num [rbInst], by norm_num [rbInst],
    fun i => ?_, fun i => by simp [rbInst, rbData], by norm_num [rbInst, rbData],
    by rw [W0_rb]; norm_num, gross_pos hr⟩
  rcases i with k | k <;> simp [rbInst, rbData] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma xi_rb (s : Bool × Bool) :
    xi (R δ bA bE sA sE).D s = Sum.elim (fun _ => δ * sg s.1) (fun _ => δ * sg s.2) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
    simp [xi, rbInst, rbData]

lemma cov_rb : covariance (R δ bA bE sA sE).D = δ ^ 2 • (1 : Matrix (Inst 1 1) (Inst 1 1) ℝ) := by
  ext i j
  simp only [covariance, xi_rb]
  rcases i with k | k <;> rcases j with l | l <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
    obtain rfl : l = 0 := Subsingleton.elim _ _ <;>
    simp [rbInst, rbData, Fintype.sum_prod_type, sg] <;> ring

lemma pd_rb (hr : InRange δ bA bE sA sE) (v : Inst 1 1 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (covariance (R δ bA bE sA sE).D *ᵥ v) := by
  rw [cov_rb, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  have hδ := hr.1
  have : 0 < v ⬝ᵥ v := by
    rw [dotProduct, sum_inst1]
    by_contra h
    push Not at h
    have h1 := mul_self_nonneg (v (Sum.inl 0))
    have h2 := mul_self_nonneg (v (Sum.inr 0))
    have a0 : v (Sum.inl 0) = 0 := by nlinarith
    have b0 : v (Sum.inr 0) = 0 := by nlinarith
    apply hv
    funext i
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> simp [a0, b0]
  positivity

/-! ### Partial learning -/

lemma sg_inj {b b' : Bool} (h : sg b = sg b') : b = b' := by
  cases b <;> cases b' <;> first | rfl | (norm_num [sg] at h)

lemma obs_eq_iff (hδ : δ ≠ 0) (t t' s s' : Bool × Bool) :
    obs (R δ bA bE sA sE) t' s' = obs (R δ bA bE sA sE) t s ↔
      t'.1 = t.1 ∧ s'.2 = s.2 ∧ sg t'.2 + sg s'.1 = sg t.2 + sg s.1 := by
  have hA : ∀ t s, ret (R δ bA bE sA sE).D ((R δ bA bE sA sE).par t) s (Sum.inl 0)
      = sg t.1 / 2 + δ * (sg t.2 + sg s.1) := fun t s => by
    have := ret_A (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE) t s; unfold gA at this; linarith
  have hE : ∀ t s, ret (R δ bA bE sA sE).D ((R δ bA bE sA sE).par t) s (Sum.inr 0)
      = -(sg t.1 / 2) + δ * sg s.2 := fun t s => by
    have := ret_E (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE) t s; unfold gE at this; linarith
  have hf : ∀ t s, (obs (R δ bA bE sA sE) t s).1 0 = sg t.1 / 2 := fun t s => by
    simp [obs, rbInst, rbData, rbPar]
  constructor
  · intro h
    have h1 := congrArg (fun y : Obs 1 2 => y.1 0) h
    have h2 := congrArg (fun y : Obs 1 2 => y.2 (Sum.inl 0)) h
    have h3 := congrArg (fun y : Obs 1 2 => y.2 (Sum.inr 0)) h
    simp only [hf] at h1
    simp only [obs, hA, hE] at h2 h3
    have e1 : t'.1 = t.1 := sg_inj (by linarith)
    rw [e1] at h2 h3
    refine ⟨e1, sg_inj ?_, ?_⟩
    · have : δ * (sg s'.2 - sg s.2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hδ
      · linarith
    · have : δ * ((sg t'.2 + sg s'.1) - (sg t.2 + sg s.1)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hδ
      · linarith
  · rintro ⟨e1, e2, e3⟩
    refine Prod.ext ?_ ?_
    · simp [obs, rbInst, rbData, rbPar, e1]
    · funext i
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
      · simp only [obs, hA, e1, e3]
      · simp only [obs, hE, e1, e2]

lemma sg_add_zero_iff (a b : Bool) : sg a + sg b = 0 ↔ a ≠ b := by
  cases a <;> cases b <;> norm_num [sg]

lemma lik_amb (hδ : δ ≠ 0) {t s : Bool × Bool} (h : sg t.2 + sg s.1 = 0) (t' : Bool × Bool) :
    lik (R δ bA bE sA sE) t' (obs (R δ bA bE sA sE) t s) = if t'.1 = t.1 then 1 / 4 else 0 := by
  simp only [lik, obs_eq_iff hδ, h, sg_add_zero_iff]
  obtain ⟨σ, ξ⟩ := t
  obtain ⟨a1, a2⟩ := s
  obtain ⟨σ', ξ'⟩ := t'
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases σ <;> cases σ' <;> cases ξ' <;> cases a2 <;> simp [rbInst, rbData]

lemma P0_amb (hδ : δ ≠ 0) {t s : Bool × Bool} (h : sg t.2 + sg s.1 = 0) :
    P0 (R δ bA bE sA sE) (obs (R δ bA bE sA sE) t s) = 1 / 8 := by
  simp only [P0, lik_amb hδ h]
  obtain ⟨σ, ξ⟩ := t
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases σ <;> simp [rbInst] <;> norm_num

/-- The observed active residual is `r_A - f₁ = δ(ξ + s_A)`. -/
lemma resid (t s : Bool × Bool) :
    (obs (R δ bA bE sA sE) t s).2 (Sum.inl 0) - (obs (R δ bA bE sA sE) t s).1 0
      = δ * (sg t.2 + sg s.1) := by
  have := ret_A (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE) t s
  simp only [gA] at this
  simp only [obs]
  simp [rbInst, rbData, rbPar] at this ⊢
  linarith

lemma resid_zero (hδ : δ ≠ 0) (t s : Bool × Bool) :
    (obs (R δ bA bE sA sE) t s).2 (Sum.inl 0) - (obs (R δ bA bE sA sE) t s).1 0 = 0
      ↔ sg t.2 + sg s.1 = 0 := by
  rw [resid, mul_eq_zero]
  simp [hδ]

lemma partialLearning (hr : InRange δ bA bE sA sE) :
    (∀ t s,
      let y := obs (R δ bA bE sA sE) t s
      y.2 (Sum.inl 0) - y.1 0 = 0 →
        P0 (R δ bA bE sA sE) y = 1 / 8 ∧
        post (R δ bA bE sA sE) y (t.1, true) = 1 / 2 ∧
        post (R δ bA bE sA sE) y (t.1, false) = 1 / 2) ∧
    ∑ t : Bool × Bool, ∑ s : Bool × Bool,
      (if (obs (R δ bA bE sA sE) t s).2 (Sum.inl 0) - (obs (R δ bA bE sA sE) t s).1 0 = 0
        then (R δ bA bE sA sE).pi0 t * (R δ bA bE sA sE).D.q s else 0) = 1 / 2 := by
  have hδ : δ ≠ 0 := hr.1.ne'
  refine ⟨fun t s hy => ?_, ?_⟩
  · have h : sg t.2 + sg s.1 = 0 := (resid_zero hδ t s).mp hy
    refine ⟨P0_amb hδ h, ?_, ?_⟩
    · simp only [post, P0_amb hδ h, lik_amb hδ h]
      norm_num [rbInst]
    · simp only [post, P0_amb hδ h, lik_amb hδ h]
      norm_num [rbInst]
  · simp only [resid_zero hδ]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sg]
    norm_num [rbInst, rbData]

/-! ### General certainty-equivalent lemmas (any M3 instance with `ρ = 20`, `W₀⁻ = 1`) -/

section CEGeneral

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T] {P : M3 n K S T}

/-- Jensen for `exp` with probability weights. -/
lemma jensen {ι : Type} [Fintype ι] {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
    Real.exp (∑ i, w i * x i) ≤ ∑ i, w i * Real.exp (x i) := by
  set m := ∑ i, w i * x i
  have key : ∀ i, Real.exp m * (1 + (x i - m)) ≤ Real.exp (x i) := fun i => by
    have := Real.add_one_le_exp (x i - m)
    have e : Real.exp (x i) = Real.exp m * Real.exp (x i - m) := by rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos m]
  calc Real.exp m = ∑ i, w i * (Real.exp m * (1 + (x i - m))) := by
        have : ∑ i, w i * (x i - m) = 0 := by
          simp only [mul_sub, sum_sub_distrib, ← sum_mul, h1, one_mul, m, sub_self]
        rw [show ∑ i, w i * (Real.exp m * (1 + (x i - m)))
          = Real.exp m * (∑ i, w i + ∑ i, w i * (x i - m)) by
            rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
            exact sum_congr rfl fun i _ => by ring]
        rw [h1, this]; ring
    _ ≤ ∑ i, w i * Real.exp (x i) := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (key i) (hw i)

/-- Mean terminal wealth. -/
noncomputable def meanW (P : M3 n K S T) (π : Policy P) : ℝ :=
  ∑ t, P.pi0 t * ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * W2 P π t s₀ s₁

lemma CE_eq (hρ : P.rho = 20) (d r : Cls) : CE P d r = -(1 / 20) * Real.log (-V P d r) := by
  simp [CE, hρ]

lemma Phi_eq (hρ : P.rho = 20) (hW : W0 P.D = 1) (π : Policy P) :
    Phi P π = -∑ t, P.pi0 t * ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ *
      Real.exp (-20 * W2 P π t s₀ s₁) := by
  rw [Phi_nested]
  simp only [U, hρ, hW, div_one, mul_neg, sum_neg_distrib]

lemma Phi_le_mean (hS : M3Setting P) (hρ : P.rho = 20) (hW : W0 P.D = 1) (π : Policy P) :
    Phi P π ≤ -Real.exp (-20 * meanW P π) := by
  obtain ⟨_, hq, hq1, hpi, hpi1, _⟩ := setting_parts hS
  rw [Phi_eq hρ hW, neg_le_neg_iff]
  -- nested Jensen
  have inner : ∀ t s₀, Real.exp (∑ s₁, P.D.q s₁ * (-20 * W2 P π t s₀ s₁))
      ≤ ∑ s₁, P.D.q s₁ * Real.exp (-20 * W2 P π t s₀ s₁) := fun t s₀ => jensen hq hq1
  have mid : ∀ t, Real.exp (∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * (-20 * W2 P π t s₀ s₁))
      ≤ ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * Real.exp (-20 * W2 P π t s₀ s₁) := fun t =>
    (jensen hq hq1).trans (sum_le_sum fun s₀ _ => mul_le_mul_of_nonneg_left (inner t s₀) (hq s₀))
  have outer := (jensen (x := fun t => ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * (-20 * W2 P π t s₀ s₁))
    hpi hpi1).trans (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (mid t) (hpi t))
  have e : -20 * meanW P π
      = ∑ t, P.pi0 t * ∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * (-20 * W2 P π t s₀ s₁) := by
    simp only [meanW, mul_sum]
    exact sum_congr rfl fun t _ => sum_congr rfl fun s₀ _ => sum_congr rfl fun s₁ _ => by ring
  rw [e]
  exact outer

lemma CE_ge (hS : M3Setting P) (hρ : P.rho = 20) (hW : W0 P.D = 1) {d r : Cls} {L : ℝ}
    {π : Policy P} (hπ : π ∈ Pol P d r) (hL : ∀ t s₀ s₁, L ≤ W2 P π t s₀ s₁) : L ≤ CE P d r := by
  obtain ⟨_, hq, hq1, hpi, hpi1, _⟩ := setting_parts hS
  obtain ⟨π', _, hmax, hV⟩ := Vmax hS d r
  have hle : Phi P π ≤ V P d r := by rw [← hV]; exact hmax hπ
  have hPhi : -Real.exp (-20 * L) ≤ Phi P π := by
    rw [Phi_nested]
    have : ∀ t s₀ s₁, -Real.exp (-20 * L) ≤ U P (W2 P π t s₀ s₁ / W0 P.D) := fun t s₀ s₁ => by
      simp only [U, hρ, hW, div_one, neg_le_neg_iff]
      exact Real.exp_le_exp.mpr (by linarith [hL t s₀ s₁])
    have w := wavg_le (c := Real.exp (-20 * L)) hpi hpi1 (f := fun t =>
      -∑ s₀, P.D.q s₀ * ∑ s₁, P.D.q s₁ * U P (W2 P π t s₀ s₁ / W0 P.D)) fun t => by
        have := wavg_le (c := Real.exp (-20 * L)) hq hq1 (f := fun s₀ =>
          -∑ s₁, P.D.q s₁ * U P (W2 P π t s₀ s₁ / W0 P.D)) fun s₀ => by
            have := wavg_le (c := Real.exp (-20 * L)) hq hq1 (f := fun s₁ =>
              -U P (W2 P π t s₀ s₁ / W0 P.D)) fun s₁ => by linarith [this t s₀ s₁]
            simp only [mul_neg, sum_neg_distrib] at this ⊢
            linarith
        simp only [mul_neg, sum_neg_distrib] at this ⊢
        linarith
    simp only [mul_neg, sum_neg_distrib] at w
    linarith
  have hneg : -V P d r ≤ Real.exp (-20 * L) := by linarith
  have hVn := V_neg hS d r
  have hlog := Real.log_le_log (by linarith) hneg
  rw [Real.log_exp] at hlog
  rw [CE_eq hρ]
  linarith

lemma CE_le (hS : M3Setting P) (hρ : P.rho = 20) (hW : W0 P.D = 1) {d r : Cls} {B : ℝ}
    (hB : ∀ π ∈ Pol P d r, meanW P π ≤ B) : CE P d r ≤ B := by
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  have h1 := Phi_le_mean hS hρ hW π
  have h2 : Real.exp (-20 * B) ≤ Real.exp (-20 * meanW P π) :=
    Real.exp_le_exp.mpr (by linarith [hB π hπ])
  have hneg : Real.exp (-20 * B) ≤ -V P d r := by rw [← hV]; linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hneg
  rw [Real.log_exp] at hlog
  rw [CE_eq hρ]
  linarith

lemma CE_lt (hS : M3Setting P) (hρ : P.rho = 20) {d r : Cls} {c : ℝ}
    (hc : ∀ π ∈ Pol P d r, Phi P π < -Real.exp (-20 * c)) : CE P d r < c := by
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  have hneg : Real.exp (-20 * c) < -V P d r := by rw [← hV]; linarith [hc π hπ]
  have hlog := Real.log_lt_log (Real.exp_pos _) hneg
  rw [Real.log_exp] at hlog
  rw [CE_eq hρ]
  linarith

end CEGeneral

/-- `W₂ ≤ M W₁⁻` when every second-quarter gross return is at most `M ≥ 1` (any M3 instance). -/
lemma W2_le_W1m {n K : ℕ} {S T : Type} [Fintype S] [Fintype T] {P : M3 n K S T}
    (hS : M3Setting P) {d r : Cls} {π : Policy P} (hπ : π ∈ Pol P d r) (t : T) (s₀ s₁ : S)
    {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ i, 1 + ret P.D (P.par t) s₁ i ≤ M) :
    W2 P π t s₀ s₁ ≤ M * W1m P π t s₀ := by
  have hnode : Feas1 P r (x1 P (obs P t s₀) π.1) (h1 P π.1) (π.2 (obsY P t s₀)) := hπ.2 (obsY P t s₀)
  have hpw := post_wealth (P := P) (x1 P (obs P t s₀) π.1) (h1 P π.1) (π.2 (obsY P t s₀))
  have hc1 := cost_nonneg P (rates_nonneg hS) (π.2 (obsY P t s₀))
  have hml := marked_le hnode.2.1 hnode.1 hM1 hM
  rw [W2_eq]
  have hle : (h1 P π.1 - ∑ i, π.2 (obsY P t s₀) i - cost P.D (π.2 (obsY P t s₀)))
      + ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i) ≤ W1m P π t s₀ := by
    simp only [W1m]; linarith
  calc _ ≤ M * ((h1 P π.1 - ∑ i, π.2 (obsY P t s₀) i - cost P.D (π.2 (obsY P t s₀)))
        + ∑ i, (x1 P (obs P t s₀) π.1 i + π.2 (obsY P t s₀) i)) := hml
    _ ≤ M * W1m P π t s₀ := mul_le_mul_of_nonneg_left hle (by linarith)

/-! ### Wealth on the instance -/

section Wealth

lemma x0_rb : (R δ bA bE sA sE).D.x0 = 0 := rfl

lemma x1_obs (t s : Bool × Bool) (u : Inst 1 1 → ℝ) :
    x1 (R δ bA bE sA sE) (obs (R δ bA bE sA sE) t s) u (Sum.inl 0) = gA δ t s * u (Sum.inl 0) ∧
    x1 (R δ bA bE sA sE) (obs (R δ bA bE sA sE) t s) u (Sum.inr 0) = gE δ t s * u (Sum.inr 0) := by
  constructor <;> simp only [x1, x0_rb, Pi.zero_apply, zero_add, obs] <;>
    first | rw [ret_A] | rw [ret_E]

lemma W1m_rb (π : Policy (R δ bA bE sA sE)) (t s₀ : Bool × Bool) :
    W1m (R δ bA bE sA sE) π t s₀
      = h1 (R δ bA bE sA sE) π.1 + π.1 (Sum.inl 0) * gA δ t s₀ + π.1 (Sum.inr 0) * gE δ t s₀ := by
  rw [W1m_eq, sum_inst1, ret_A, ret_E, x0_rb]
  simp only [Pi.zero_apply, zero_add]
  ring

lemma W2_rb (π : Policy (R δ bA bE sA sE)) (t s₀ s₁ : Bool × Bool) :
    W2 (R δ bA bE sA sE) π t s₀ s₁
      = (h1 (R δ bA bE sA sE) π.1 - (π.2 (obsY _ t s₀) (Sum.inl 0) + π.2 (obsY _ t s₀) (Sum.inr 0))
          - cost (R δ bA bE sA sE).D (π.2 (obsY _ t s₀)))
        + (gA δ t s₀ * π.1 (Sum.inl 0) + π.2 (obsY _ t s₀) (Sum.inl 0)) * gA δ t s₁
        + (gE δ t s₀ * π.1 (Sum.inr 0) + π.2 (obsY _ t s₀) (Sum.inr 0)) * gE δ t s₁ := by
  rw [W2_eq]
  simp only [sum_inst1]
  rw [(x1_obs t s₀ π.1).1, (x1_obs t s₀ π.1).2, ret_A, ret_E]
  ring

lemma root_budget (hr : InRange δ bA bE sA sE) {d r : Cls} {π : Policy (R δ bA bE sA sE)}
    (hπ : π ∈ Pol (R δ bA bE sA sE) d r) :
    0 ≤ π.1 (Sum.inl 0) ∧ 0 ≤ π.1 (Sum.inr 0) ∧ 0 ≤ h1 (R δ bA bE sA sE) π.1 ∧
      π.1 (Sum.inl 0) + π.1 (Sum.inr 0) + h1 (R δ bA bE sA sE) π.1 ≤ 1 := by
  have hS := setting hr
  have hrw := root_wealth (P := R δ bA bE sA sE) π.1
  have hc := cost_nonneg (R δ bA bE sA sE) (rates_nonneg hS) π.1
  rw [sum_inst1, W0_rb, x0_rb] at hrw
  simp only [Pi.zero_apply, zero_add] at hrw
  have ha := hπ.1.1 (Sum.inl 0)
  have hp := hπ.1.1 (Sum.inr 0)
  simp only [x0_rb, Pi.zero_apply, zero_add] at ha hp
  exact ⟨ha, hp, hπ.1.2.1, by linarith⟩

/-- Expanding a path expectation of an expression in the gross returns. -/
lemma mean_eq (f : Bool × Bool → Bool × Bool → Bool × Bool → ℝ) :
    ∑ t, (R δ bA bE sA sE).pi0 t * ∑ s₀, (R δ bA bE sA sE).D.q s₀ * ∑ s₁, (R δ bA bE sA sE).D.q s₁ * f t s₀ s₁
      = ∑ t, ∑ s₀, ∑ s₁, (1 / 64 : ℝ) * f t s₀ s₁ := by
  simp only [mul_sum]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s₀ _ => sum_congr rfl fun s₁ _ => ?_
  simp [rbInst, rbData]
  ring

lemma E_gAgA : ∑ t : Bool × Bool, ∑ s₀ : Bool × Bool, ∑ s₁ : Bool × Bool,
    (1 / 64 : ℝ) * (gA δ t s₀ * gA δ t s₁) = 5 / 4 + δ ^ 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, gA, sg, ↓reduceIte, Bool.false_eq_true]
  ring

lemma E_gEgE : ∑ t : Bool × Bool, ∑ s₀ : Bool × Bool, ∑ s₁ : Bool × Bool,
    (1 / 64 : ℝ) * (gE δ t s₀ * gE δ t s₁) = 5 / 4 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, gE, sg, ↓reduceIte, Bool.false_eq_true]
  ring

lemma E_W1 (h a p : ℝ) : ∑ t : Bool × Bool, ∑ s₀ : Bool × Bool, ∑ _s₁ : Bool × Bool,
    (1 / 64 : ℝ) * (h + a * gA δ t s₀ + p * gE δ t s₀) = h + a + p := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, gA, gE, sg, ↓reduceIte, Bool.false_eq_true]
  ring

end Wealth

/-! ### Policies -/

section Policies

lemma obs_f (t s : Bool × Bool) : (obs (R δ bA bE sA sE) t s).1 0 = sg t.1 / 2 := by
  simp [obs, rbInst, rbData, rbPar]

lemma obs_E (t s : Bool × Bool) : 1 + (obs (R δ bA bE sA sE) t s).2 (Sum.inr 0) = gE δ t s := ret_E t s

lemma half_iff (b : Bool) : sg b / 2 = 1 / 2 ↔ b = true := by cases b <;> norm_num [sg]

lemma h1_zero : h1 (R δ bA bE sA sE) (0 : Inst 1 1 → ℝ) = 1 := by
  simp only [h1, cost_zero]; simp [rbInst, rbData]

lemma x1_zero (y : Obs 1 2) : x1 (R δ bA bE sA sE) y 0 = 0 := by funext i; simp [x1, x0_rb]

lemma cost_rb (u : Inst 1 1 → ℝ) :
    cost (R δ bA bE sA sE).D u = bA * max (u (Sum.inl 0)) 0 + sA * max (-u (Sum.inl 0)) 0
      + (bE * max (u (Sum.inr 0)) 0 + sE * max (-u (Sum.inr 0)) 0) := by
  simp [cost, rbInst, rbData]

noncomputable def cashPol : Policy (R δ bA bE sA sE) := (0, fun _ => 0)

lemma cashPol_mem (d r : Cls) : (cashPol : Policy (R δ bA bE sA sE)) ∈ Pol (R δ bA bE sA sE) d r := by
  refine ⟨feas_zero d (fun i => le_rfl) (by norm_num [rbInst, rbData]), fun y => ?_⟩
  show Feas1 _ r (x1 _ (y : Obs 1 2) (0 : Inst 1 1 → ℝ)) (h1 _ (0 : Inst 1 1 → ℝ)) 0
  rw [x1_zero, h1_zero]
  exact feas_zero r (fun i => le_rfl) zero_le_one

lemma cashPol_W2 (t s₀ s₁ : Bool × Bool) : W2 (R δ bA bE sA sE) cashPol t s₀ s₁ = 1 := by
  rw [W2_rb]
  show h1 _ (0 : Inst 1 1 → ℝ) - _ - cost _ (0 : Inst 1 1 → ℝ) + _ + _ = 1
  rw [h1_zero, cost_zero]
  simp [cashPol]

noncomputable def rootFE : Inst 1 1 → ℝ := Sum.elim (fun _ => aS) (fun _ => pS)

variable (δ bA bE sA sE) in
noncomputable def uFE (y : Yset (R δ bA bE sA sE)) : Inst 1 1 → ℝ :=
  if (y : Obs 1 2).1 0 = 1 / 2 then
    Sum.elim (fun _ => 0) (fun _ => -((1 + (y : Obs 1 2).2 (Sum.inr 0)) * pS)) else 0

variable (δ bA bE sA sE) in
noncomputable def polFE : Policy (R δ bA bE sA sE) := (rootFE, uFE δ bA bE sA sE)

lemma uFE_obs (t s : Bool × Bool) :
    uFE δ bA bE sA sE (obsY (R δ bA bE sA sE) t s)
      = if t.1 = true then Sum.elim (fun _ => 0) (fun _ => -(gE δ t s * pS)) else 0 := by
  simp only [uFE, obsY, obs_f, half_iff, obs_E]

lemma h1_FE : h1 (R δ bA bE sA sE) rootFE = 1 - aS - pS - bA * aS - bE * pS := by
  simp only [h1, rootFE, cost_rb, sum_inst1, Sum.elim_inl, Sum.elim_inr]
  rw [max_eq_left aS_pos.le, max_eq_right (by linarith [aS_pos]), max_eq_left pS_pos.le,
    max_eq_right (by linarith [pS_pos])]
  simp [rbInst, rbData]
  ring

lemma gE_pos (hr : InRange δ bA bE sA sE) (t s : Bool × Bool) : 0 < gE δ t s := by
  have := (gE_bounds hr.1.le t s).1; have := sg_bounds t.1; linarith [hr.2.1]

lemma gA_pos (hr : InRange δ bA bE sA sE) (t s : Bool × Bool) : 0 < gA δ t s := by
  have := (gA_bounds hr.1.le t s).1; have := sg_bounds t.1; linarith [hr.2.1]

lemma polFE_mem (hr : InRange δ bA bE sA sE) : polFE δ bA bE sA sE ∈ Pol (R δ bA bE sA sE) .F .E := by
  obtain ⟨hδ0, hδ1, h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hr
  have hh := h1_FE (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE)
  have hh0 : 0 ≤ h1 (R δ bA bE sA sE) rootFE := by
    rw [hh]; norm_num [aS, pS]; nlinarith
  refine ⟨⟨fun i => ?_, hh0, trivial⟩, fun y => ?_⟩
  · rcases i with k | k <;> simp [polFE, rootFE, x0_rb, aS_pos.le, pS_pos.le]
  · obtain ⟨t, s, hy⟩ := obs_mem y
    obtain rfl : y = obsY (R δ bA bE sA sE) t s := Subtype.ext hy.symm
    show Feas1 _ .E (x1 _ (obs (R δ bA bE sA sE) t s) rootFE) (h1 _ rootFE)
      (uFE δ bA bE sA sE (obsY (R δ bA bE sA sE) t s))
    have hxA := (x1_obs (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE) t s rootFE).1
    have hxE := (x1_obs (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE) t s rootFE).2
    have hgA := gA_pos hr t s
    have hgE := gE_pos hr t s
    rw [uFE_obs]
    split_ifs with ht
    · refine ⟨fun i => ?_, ?_, rfl⟩
      · rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
        · rw [hxA]; simp [rootFE]; nlinarith [aS_pos]
        · rw [hxE]; simp [rootFE]
      · rw [cost_rb, sum_inst1, hh]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [max_self, neg_zero, max_self, max_eq_right (by nlinarith [pS_pos]),
          max_eq_left (by nlinarith [pS_pos])]
        norm_num [aS, pS]
        nlinarith
    · refine feas_zero .E (fun i => ?_) hh0
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
      · rw [hxA]; simp [rootFE]; nlinarith [aS_pos]
      · rw [hxE]; simp [rootFE]; nlinarith [pS_pos]

lemma polFE_W2 (hr : InRange δ bA bE sA sE) (t s₀ s₁ : Bool × Bool) :
    657 / 505 - 6 * δ ≤ W2 (R δ bA bE sA sE) (polFE δ bA bE sA sE) t s₀ s₁ := by
  obtain ⟨hδ0, hδ1, h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hr
  rw [W2_rb]
  show 657 / 505 - 6 * δ ≤ h1 _ rootFE - _ - _ + _ + _
  rw [h1_FE]
  simp only [polFE]
  rw [uFE_obs]
  have hs := sg_bounds t.1
  have gA0 := gA_bounds hδ0.le t s₀
  have gA1 := gA_bounds hδ0.le t s₁
  have gE0 := gE_bounds hδ0.le t s₀
  have gE1 := gE_bounds hδ0.le t s₁
  have ha := aS_pos
  have hp := pS_pos
  obtain ⟨σ, ξ⟩ := t
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply, cost_zero, rootFE, Sum.elim_inl,
      Sum.elim_inr, add_zero, sub_zero]
    simp only [sg, Bool.false_eq_true, ↓reduceIte] at gA0 gA1 gE0 gE1
    have hAA : (1 / 2 - 2 * δ) * (1 / 2 - 2 * δ) ≤ gA δ (false, ξ) s₀ * gA δ (false, ξ) s₁ :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hEE : (3 / 2 - δ) * (3 / 2 - δ) ≤ gE δ (false, ξ) s₀ * gE δ (false, ξ) s₁ :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    norm_num [aS, pS] at hAA hEE ⊢
    nlinarith
  · simp only [↓reduceIte, rootFE, Sum.elim_inl, Sum.elim_inr, add_zero]
    rw [cost_rb]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hgE0 : 0 < gE δ (true, ξ) s₀ := gE_pos hr _ _
    rw [max_self, neg_zero, max_self, max_eq_right (by nlinarith [pS_pos]),
      max_eq_left (by nlinarith [pS_pos])]
    simp only [sg, ↓reduceIte] at gA0 gA1 gE0 gE1
    have hAA : (3 / 2 - 2 * δ) * (3 / 2 - 2 * δ) ≤ gA δ (true, ξ) s₀ * gA δ (true, ξ) s₁ :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hE' : (99 / 100) * (1 / 2 - δ) ≤ (1 - sE) * gE δ (true, ξ) s₀ :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    norm_num [aS, pS] at hAA hE' ⊢
    nlinarith

variable (δ bA bE sA sE) in
noncomputable def uEF (y : Yset (R δ bA bE sA sE)) : Inst 1 1 → ℝ :=
  if (y : Obs 1 2).1 0 = 1 / 2 then Sum.elim (fun _ => 1 / (1 + bA)) (fun _ => 0)
  else Sum.elim (fun _ => 0) (fun _ => 1 / (1 + bE))

variable (δ bA bE sA sE) in
noncomputable def polEF : Policy (R δ bA bE sA sE) := (0, uEF δ bA bE sA sE)

lemma uEF_obs (t s : Bool × Bool) :
    uEF δ bA bE sA sE (obsY (R δ bA bE sA sE) t s)
      = if t.1 = true then Sum.elim (fun _ => 1 / (1 + bA)) (fun _ => 0)
        else Sum.elim (fun _ => 0) (fun _ => 1 / (1 + bE)) := by
  simp only [uEF, obsY, obs_f, half_iff]

lemma buy_all {b : ℝ} (hb : 0 ≤ b) : 1 - 1 / (1 + b) - b * (1 / (1 + b)) = 0 := by
  field_simp; ring

lemma polEF_mem (hr : InRange δ bA bE sA sE) : polEF δ bA bE sA sE ∈ Pol (R δ bA bE sA sE) .E .F := by
  obtain ⟨hδ0, hδ1, h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hr
  refine ⟨feas_zero .E (fun i => le_rfl) (by norm_num [rbInst, rbData]), fun y => ?_⟩
  obtain ⟨t, s, hy⟩ := obs_mem y
  obtain rfl : y = obsY (R δ bA bE sA sE) t s := Subtype.ext hy.symm
  show Feas1 _ .F (x1 _ (obs (R δ bA bE sA sE) t s) (0 : Inst 1 1 → ℝ)) (h1 _ (0 : Inst 1 1 → ℝ))
    (uEF δ bA bE sA sE (obsY (R δ bA bE sA sE) t s))
  rw [x1_zero, h1_zero, uEF_obs]
  have hA : 0 < 1 / (1 + bA) := by positivity
  have hE : 0 < 1 / (1 + bE) := by positivity
  split_ifs
  · refine ⟨fun i => ?_, ?_, trivial⟩
    · rcases i with k | k
      · simp; positivity
      · simp
    · rw [cost_rb, sum_inst1]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
      have := buy_all h1'
      linarith
  · refine ⟨fun i => ?_, ?_, trivial⟩
    · rcases i with k | k
      · simp
      · simp; positivity
    · rw [cost_rb, sum_inst1]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
      have := buy_all h3'
      linarith

lemma polEF_W2 (hr : InRange δ bA bE sA sE) (t s₀ s₁ : Bool × Bool) :
    (3 / 2 - 2 * δ) * (100 / 101) ≤ W2 (R δ bA bE sA sE) (polEF δ bA bE sA sE) t s₀ s₁ := by
  obtain ⟨hδ0, hδ1, h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hr
  have hA : 0 < 1 / (1 + bA) := by positivity
  have hE : 0 < 1 / (1 + bE) := by positivity
  have hA' : 100 / 101 ≤ 1 / (1 + bA) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  have hE' : 100 / 101 ≤ 1 / (1 + bE) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  rw [W2_rb]
  show _ ≤ h1 _ (0 : Inst 1 1 → ℝ) - _ - _ + _ + _
  rw [h1_zero]
  simp only [polEF]
  rw [uEF_obs]
  have gA1 := gA_bounds hδ0.le t s₁
  have gE1 := gE_bounds hδ0.le t s₁
  obtain ⟨σ, ξ⟩ := t
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, zero_add]
    rw [cost_rb]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
    have := buy_all h3'
    simp only [sg, Bool.false_eq_true, ↓reduceIte] at gE1
    nlinarith [mul_le_mul hE' (show 3 / 2 - 2 * δ ≤ gE δ (false, ξ) s₁ by linarith)
      (by linarith) hE.le]
  · simp only [↓reduceIte, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, zero_add]
    rw [cost_rb]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
    have := buy_all h1'
    simp only [sg, ↓reduceIte] at gA1
    nlinarith [mul_le_mul hA' (show 3 / 2 - 2 * δ ≤ gA δ (true, ξ) s₁ by linarith)
      (by linarith) hA.le]

end Policies

/-! ### The bounds -/

section Main

lemma E_lin (h a p : ℝ) : ∑ t : Bool × Bool, ∑ s₀ : Bool × Bool, ∑ s₁ : Bool × Bool,
    (1 / 64 : ℝ) * (h + a * (gA δ t s₀ * gA δ t s₁) + p * (gE δ t s₀ * gE δ t s₁))
      = h + a * (5 / 4 + δ ^ 2) + p * (5 / 4) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, gA, gE, sg, ↓reduceIte, Bool.false_eq_true]
  ring

lemma E_W1M (M h a p : ℝ) : ∑ t : Bool × Bool, ∑ s₀ : Bool × Bool, ∑ _s₁ : Bool × Bool,
    (1 / 64 : ℝ) * (M * (h + a * gA δ t s₀ + p * gE δ t s₀)) = M * (h + a + p) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, gA, gE, sg, ↓reduceIte, Bool.false_eq_true]
  ring

lemma E_regime (b₁ b₂ : ℝ) : ∑ t : Bool × Bool, ∑ _s₀ : Bool × Bool, ∑ _s₁ : Bool × Bool,
    (1 / 64 : ℝ) * Real.exp (-20 * (if t.1 then b₁ else b₂))
      = (Real.exp (-20 * b₁) + Real.exp (-20 * b₂)) / 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  ring

lemma exp34 : 2 ≤ Real.exp (3 / 4) := by
  have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
  norm_num at this
  linarith

/-- ETF-only trading at both reviews: with `e = 3δ + δ²`, terminal wealth is at most `1 - p/2 + e`
when `σ = +1` and `3/2 + 3p/4 + e` when `σ = -1`, so `Φ < -e^{-20(83/80 + e)}`. -/
lemma Phi_EE (hr : InRange δ bA bE sA sE) {π : Policy (R δ bA bE sA sE)}
    (hπ : π ∈ Pol (R δ bA bE sA sE) .E .E) :
    Phi (R δ bA bE sA sE) π < -Real.exp (-20 * (83 / 80 + (3 * δ + δ ^ 2))) := by
  obtain ⟨hδ0, hδ1, _⟩ := id hr
  have hS := setting hr
  obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hr hπ
  have hA : π.1 (Sum.inl 0) = 0 := hπ.1.2.2
  set p := π.1 (Sum.inr 0)
  set h := h1 (R δ bA bE sA sE) π.1
  set e := 3 * δ + δ ^ 2
  have hp1 : p ≤ 1 := by linarith
  have hB : ∀ t s₀ s₁, W2 (R δ bA bE sA sE) π t s₀ s₁ ≤
      (if t.1 then 1 - p / 2 + e else 3 / 2 + 3 * p / 4 + e) := by
    rintro ⟨σ, ξ⟩ s₀ s₁
    cases σ
    · have gA1 := (gA_bounds hδ0.le (false, ξ) s₁).2
      have gE1 := (gE_bounds hδ0.le (false, ξ) s₁).2
      have gE0 := (gE_bounds hδ0.le (false, ξ) s₀).2
      simp only [sg, Bool.false_eq_true, ↓reduceIte] at gA1 gE1 gE0
      have w := W2_le_W1m hS hπ (false, ξ) s₀ s₁ (M := 3 / 2 + δ) (by linarith) (fun i => by
        rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
        · rw [ret_A]; linarith
        · rw [ret_E]; linarith)
      rw [W1m_rb, hA] at w
      have hX : h + 0 * gA δ (false, ξ) s₀ + p * gE δ (false, ξ) s₀ ≤ 1 + p / 2 + p * δ := by
        nlinarith [mul_le_mul_of_nonneg_left gE0 hp0]
      have := mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ 3 / 2 + δ)
      simp only [Bool.false_eq_true, ↓reduceIte]
      nlinarith [mul_nonneg hδ0.le (by linarith : (0 : ℝ) ≤ 1 - p),
        mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 - p)]
    · have hnode : Feas1 (R δ bA bE sA sE) .E (x1 (R δ bA bE sA sE) (obs (R δ bA bE sA sE) (true, ξ) s₀) π.1)
          h (π.2 (obsY (R δ bA bE sA sE) (true, ξ) s₀)) := hπ.2 (obsY (R δ bA bE sA sE) (true, ξ) s₀)
      have huA : π.2 (obsY (R δ bA bE sA sE) (true, ξ) s₀) (Sum.inl 0) = 0 := hnode.2.2
      have huE := hnode.1 (Sum.inr 0)
      rw [(x1_obs _ _ _).2] at huE
      have hc1 := cost_nonneg (R δ bA bE sA sE) (rates_nonneg hS) (π.2 (obsY (R δ bA bE sA sE) (true, ξ) s₀))
      have gE1 := gE_bounds hδ0.le (true, ξ) s₁
      have gE0 := (gE_bounds hδ0.le (true, ξ) s₀).2
      simp only [sg, ↓reduceIte] at gE1 gE0
      rw [W2_rb, huA, hA]
      simp only [↓reduceIte]
      nlinarith [mul_nonneg huE (by linarith : (0 : ℝ) ≤ 1 - gE δ (true, ξ) s₁),
        mul_le_mul_of_nonneg_right gE0 hp0, mul_le_mul_of_nonneg_right hp1 hδ0.le]
  -- sum the pathwise bounds
  have hmean : (Real.exp (-20 * (1 - p / 2 + e)) + Real.exp (-20 * (3 / 2 + 3 * p / 4 + e))) / 2
      ≤ ∑ t, ∑ s₀, ∑ s₁, (1 / 64 : ℝ) * Real.exp (-20 * W2 (R δ bA bE sA sE) π t s₀ s₁) := by
    rw [← E_regime]
    exact sum_le_sum fun t _ => sum_le_sum fun s₀ _ => sum_le_sum fun s₁ _ =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hB t s₀ s₁])) (by norm_num)
  have hm := mean_eq (δ := δ) (bA := bA) (bE := bE) (sA := sA) (sE := sE)
    (fun t s₀ s₁ => Real.exp (-20 * W2 (R δ bA bE sA sE) π t s₀ s₁))
  rw [Phi_eq rfl W0_rb, hm]
  -- exponential bounds (as in claim 012)
  obtain ⟨hf1, hf2⟩ := exp_facts
  set E := Real.exp (-20 * e)
  have hE : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-20 * (1 - p / 2 + e)) = Real.exp (-20) * Real.exp (10 * p) * E := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-20 * (3 / 2 + 3 * p / 4 + e)) = Real.exp (-30) * Real.exp (-(15 * p)) * E := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-20 * (83 / 80 + e)) * Real.exp (3 / 4) = Real.exp (-20) * E := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have b1 := Real.add_one_le_exp (10 * p)
  have b2 := Real.add_one_le_exp (-(15 * p))
  have p20 := Real.exp_pos (-20)
  have p30 := Real.exp_pos (-30)
  have hsum : Real.exp (-20) < Real.exp (-20) * Real.exp (10 * p) + Real.exp (-30) * Real.exp (-(15 * p)) := by
    nlinarith [mul_le_mul_of_nonneg_left b1 p20.le, mul_le_mul_of_nonneg_left b2 p30.le,
      mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 10 * Real.exp (-20) - 15 * Real.exp (-30))]
  have k1 := mul_lt_mul_of_pos_right hsum hE
  have k2 := mul_le_mul_of_nonneg_left exp34 (Real.exp_pos (-20 * (83 / 80 + e))).le
  rw [e1, e2] at hmean
  linarith

lemma bounds (hr : InRange δ bA bE sA sE) :
    let P := rbInst δ bA bE sA sE
    0 ≤ Delta P .N ∧ Delta P .N ≤ 1 / 4 + δ ^ 2 ∧
    2129 / 8080 - 9 * δ - δ ^ 2 < Delta P .E ∧
    0 ≤ Delta P .F ∧ Delta P .F ≤ 3 / 202 + 402 / 101 * δ ∧
    1 / 250 < Delta P .E - Delta P .N ∧ Delta P .F - Delta P .E < -23 / 100 := by
  intro P
  obtain ⟨hδ0, hδ1, _⟩ := id hr
  have hS := setting hr
  have hcomp := classComparison hS
  -- future no trade
  have hFN : CE P .F .N ≤ 5 / 4 + δ ^ 2 := CE_le hS rfl W0_rb fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hr hπ
    have hw : ∀ t s₀ s₁, W2 (R δ bA bE sA sE) π t s₀ s₁ = h1 (R δ bA bE sA sE) π.1
        + π.1 (Sum.inl 0) * (gA δ t s₀ * gA δ t s₁) + π.1 (Sum.inr 0) * (gE δ t s₀ * gE δ t s₁) := by
      intro t s₀ s₁
      have z : π.2 (obsY (R δ bA bE sA sE) t s₀) = 0 := (hπ.2 _).2.2
      rw [W2_rb, z, cost_zero]
      simp only [Pi.zero_apply]
      ring
    rw [meanW, mean_eq (W2 (R δ bA bE sA sE) π)]
    simp only [hw]
    rw [E_lin]
    nlinarith [mul_le_mul_of_nonneg_left hbud (by positivity : (0 : ℝ) ≤ 5 / 4 + δ ^ 2),
      mul_nonneg hh0 (sq_nonneg δ), mul_nonneg hp0 (sq_nonneg δ)]
  have hEN : 1 ≤ CE P .E .N :=
    CE_ge hS rfl W0_rb (cashPol_mem .E .N) fun t s₀ s₁ => (cashPol_W2 t s₀ s₁).ge
  -- future ETF-only trading
  have hFE : 657 / 505 - 6 * δ ≤ CE P .F .E := CE_ge hS rfl W0_rb (polFE_mem hr) (polFE_W2 hr)
  have hEE : CE P .E .E < 83 / 80 + (3 * δ + δ ^ 2) := CE_lt hS rfl fun π hπ => Phi_EE hr hπ
  -- future full trading
  have hFF : CE P .F .F ≤ 3 / 2 + 2 * δ := CE_le hS rfl W0_rb fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hr hπ
    have hM : ∀ t s₀ s₁, W2 (R δ bA bE sA sE) π t s₀ s₁ ≤ (3 / 2 + 2 * δ) *
        (h1 (R δ bA bE sA sE) π.1 + π.1 (Sum.inl 0) * gA δ t s₀ + π.1 (Sum.inr 0) * gE δ t s₀) := by
      intro t s₀ s₁
      have := sg_bounds t.1
      have w := W2_le_W1m hS hπ t s₀ s₁ (M := 3 / 2 + 2 * δ) (by linarith) (fun i => by
        rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
        · rw [ret_A]; linarith [(gA_bounds hδ0.le t s₁).2]
        · rw [ret_E]; linarith [(gE_bounds hδ0.le t s₁).2])
      rwa [W1m_rb] at w
    rw [meanW, mean_eq (W2 (R δ bA bE sA sE) π)]
    calc _ ≤ ∑ t, ∑ s₀, ∑ s₁, (1 / 64 : ℝ) * ((3 / 2 + 2 * δ) *
          (h1 (R δ bA bE sA sE) π.1 + π.1 (Sum.inl 0) * gA δ t s₀ + π.1 (Sum.inr 0) * gE δ t s₀)) :=
          sum_le_sum fun t _ => sum_le_sum fun s₀ _ => sum_le_sum fun s₁ _ =>
            mul_le_mul_of_nonneg_left (hM t s₀ s₁) (by norm_num)
      _ = (3 / 2 + 2 * δ) * (h1 (R δ bA bE sA sE) π.1 + π.1 (Sum.inl 0) + π.1 (Sum.inr 0)) := E_W1M _ _ _ _
      _ ≤ 3 / 2 + 2 * δ := by nlinarith
  have hEF : (3 / 2 - 2 * δ) * (100 / 101) ≤ CE P .E .F :=
    CE_ge hS rfl W0_rb (polEF_mem hr) (polEF_W2 hr)
  have hN0 := (hcomp.2.2 .N).1
  have hF0 := (hcomp.2.2 .F).1
  have hδ2 : δ ^ 2 ≤ δ / 1000 := by nlinarith
  simp only [Delta] at hN0 hF0 ⊢
  refine ⟨hN0, by linarith, by linarith, hF0, by linarith, by linarith, by linarith⟩

lemma activePurchase (hr : InRange δ bA bE sA sE) (π : Policy (R δ bA bE sA sE))
    (hπ : π ∈ Pol (R δ bA bE sA sE) .F .E)
    (hmax : IsMaxOn (Phi (R δ bA bE sA sE)) (Pol (R δ bA bE sA sE) .F .E) π) :
    0 < π.1 (Sum.inl 0) := by
  obtain ⟨hδ0, hδ1, _⟩ := id hr
  have hS := setting hr
  obtain ⟨ha0, _, _, _⟩ := root_budget hr hπ
  by_contra hle
  have hA : π.1 (Sum.inl 0) = 0 := le_antisymm (not_lt.mp hle) ha0
  have hπE : π ∈ Pol (R δ bA bE sA sE) .E .E := ⟨⟨hπ.1.1, hπ.1.2.1, hA⟩, hπ.2⟩
  obtain ⟨πE, _, hmaxE, hVE⟩ := Vmax hS .E .E
  have hV : V (R δ bA bE sA sE) .F .E ≤ V (R δ bA bE sA sE) .E .E := by
    rw [V_eq_of_max hπ hmax, ← hVE]; exact hmaxE hπE
  have hCE := CE_mono hS hV
  have := (bounds hr).2.2.1
  have hδ2 : δ ^ 2 ≤ δ / 1000 := by nlinarith
  simp only [Delta] at this
  linarith

end Main

theorem proof : Standalone.ContinuationRobustness.statement :=
  ⟨fun _ _ _ _ _ hr => ⟨setting hr, gross_pos hr, cov_rb, pd_rb hr⟩,
   fun _ _ _ _ _ hr => ⟨fun t => by simp [rbInst, rbPar], hr.1.ne', fun t => by norm_num [rbInst]⟩,
   fun _ _ _ _ _ hr => partialLearning hr, fun _ _ _ _ _ hr => bounds hr,
   fun _ _ _ _ _ hr π hπ hmax => activePurchase hr π hπ hmax⟩

end Novel.ContinuationRobustnessProof

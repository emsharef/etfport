import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.M4InformationObstruction

/-!
# Proof of claim 014: equal portfolio geometry and covariances can hide certification information

Self-contained (no claim dependencies).
* **Part 1:** the two laws are expanded over the eight scenarios. The ETF marginal of R is that of
  I under the relabelling `(s, t, u) ↦ (u, t, s)`, and `θ̂_N` never reads the ETF return.
* **Part 2:**
  - Upper bound for I: every certification at `θ₋` is false. On histories whose active returns
    are all zero, `θ₊` and `θ₋` give the same history under the relabelling `s ↦ ¬s`, so those
    histories carry at most `η` of `θ₊`'s certification mass.
  - Attaining rules: they identify `α` from any nonzero active return (I) or from the first ETF
    residual's magnitude (R), and use a coin only on the all-zero histories.
* **Part 3:** the gate depends on the data only through `θ̂_N`, `Ω`, `Σ` and the shared classes.
  At `N_obs = 1`, `T_N = 1` surely, `Ω†` acts on `Im Ω` as the inverse of `Ω` (first Penrose
  equation), `C_N` is `{θ₊}` at `α̂ = 1/5`, and the plug-in optimum at `α̂ = 0` has no active
  holding.
-/

namespace Novel.M4InformationObstructionProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
open scoped Classical

noncomputable section

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by cases b <;> norm_num [sg]

lemma sg_bounds (b : Bool) : -1 ≤ sg b ∧ sg b ≤ 1 := by cases b <;> norm_num [sg]

lemma inst_ext (w : Inst 1 1 → ℝ) : w = act (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

/-! ### The common data -/

section Common

variable (zE : Sc → Fin 1 → ℝ)

lemma W0_base : W0 (baseData zE) = 1 := by simp [W0, baseData]

lemma w0_base : w0 (baseData zE) = 0 := by funext i; simp [w0, baseData]

lemma tau_base (v : Inst 1 1 → ℝ) : tau (baseData zE) v = 0 := by simp [tau, baseData]

lemma cash_base (w : Inst 1 1 → ℝ) :
    cash (baseData zE) w = 1 - (w (Sum.inl 0) + w (Sum.inr 0)) := by
  simp [cash, k0, W0_base, w0_base, tau_base, Fintype.sum_sum_type]
  simp [baseData]

lemma F_base : F (baseData zE)
    = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} := by
  ext w
  simp only [F, Set.mem_ofPred_eq, cash_base]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨(h _).1, (h _).1, by linarith⟩
  · rintro ⟨ha, hp, hs⟩
    refine ⟨fun i => ?_, by linarith⟩
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
      simp only [baseData] <;> constructor <;> linarith

lemma E_base : E (baseData zE)
    = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} := by
  ext w
  simp only [E, F_base, w0_base, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨ha, hp, hs⟩, h⟩
    have h0 : w (Sum.inl 0) = 0 := by simpa [active] using congrFun h 0
    exact ⟨h0, hp, by linarith⟩
  · rintro ⟨ha, hp, hs⟩
    refine ⟨⟨by linarith, hp, by linarith⟩, ?_⟩
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [active, ha]

lemma score_base (hc : covariance (baseData zE) = Matrix.diagonal (act (1 / 100) (1 / 40)))
    (w : Inst 1 1 → ℝ) (θ : Params 1 2) :
    score (baseData zE) w θ = w (Sum.inl 0) * θ.alpha 0 + w (Sum.inr 0) * θ.lam 0
      - w (Sum.inl 0) ^ 2 / 200 - w (Sum.inr 0) ^ 2 / 80 := by
  simp only [score, hc, tau_base]
  simp [exposure, active, etf, baseData, dotProduct, mulVec, Fintype.sum_sum_type, diagonal, act,
    Fin.sum_univ_two]
  ring

lemma ret_inl (θ : Fin 3 → ℝ) (x : Sc) :
    ret (baseData zE) (toPar θ) x (Sum.inl 0) = θ 2 + sg x.1 / 10 := by
  simp [ret, baseData, toPar]

lemma ret_inr (θ : Fin 3 → ℝ) (x : Sc) :
    ret (baseData zE) (toPar θ) x (Sum.inr 0) = θ 0 + zE x 0 := by
  simp [ret, baseData, toPar]

lemma X_rec (θ : Fin 3 → ℝ) (x : Sc) :
    X (baseData zE) (record (baseData zE) θ x) = ![θ 0, θ 1, θ 2 + sg x.1 / 10] := by
  have h := ret_inl zE θ x
  funext i
  fin_cases i
  · simp [X, record, baseData, toPar]
  · simp [X, record, baseData, toPar]
  · simp only [X, record]
    rw [h]
    simp [baseData]

lemma rec_rA (θ : Fin 3 → ℝ) (x : Sc) : (record (baseData zE) θ x).rA = θ 2 + sg x.1 / 10 :=
  ret_inl zE θ x

lemma rec_rE (θ : Fin 3 → ℝ) (x : Sc) : (record (baseData zE) θ x).rE 0 = θ 0 + zE x 0 :=
  ret_inr zE θ x

lemma mass_base {N : ℕ} (σ : Fin N → Sc) : mass (baseData zE) σ = (1 / 8) ^ N := by
  simp [mass, baseData]

end Common

lemma cov_I : covariance dataI = Matrix.diagonal (act (1 / 100) (1 / 40)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [covariance, xi, dataI, baseData, diagonal, act, Fintype.sum_prod_type,
      sg] <;> norm_num

lemma cov_R : covariance dataR = Matrix.diagonal (act (1 / 100) (1 / 40)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [covariance, xi, dataR, baseData, diagonal, act, Fintype.sum_prod_type,
      sg] <;> norm_num

/-! ### The shared economics -/

/-- The objects both laws share: `F`, `E` and `Q`. -/
def Good (D : Data 1 1 2 Sc) : Prop :=
  F D = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} ∧
  E D = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} ∧
  ∀ w (θ : Params 1 2), score D w θ = w (Sum.inl 0) * θ.alpha 0 + w (Sum.inr 0) * θ.lam 0
    - w (Sum.inl 0) ^ 2 / 200 - w (Sum.inr 0) ^ 2 / 80

lemma good_I : Good dataI := ⟨F_base _, E_base _, score_base _ cov_I⟩

lemma good_R : Good dataR := ⟨F_base _, E_base _, score_base _ cov_R⟩

lemma sSup_of_max {f : (Inst 1 1 → ℝ) → ℝ} {A : Set (Inst 1 1 → ℝ)} {w : Inst 1 1 → ℝ}
    (h : w ∈ maximizers f A) : sSup (f '' A) = f w :=
  IsGreatest.csSup_eq ⟨⟨w, h.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h.2 v hv⟩

lemma wE_mem_E {D : Data 1 1 2 Sc} (hD : Good D) : wE ∈ E D := by
  rw [hD.2.1]; norm_num [wE, act]

lemma wE_mem_F {D : Data 1 1 2 Sc} (hD : Good D) : wE ∈ F D := by
  rw [hD.1]; norm_num [wE, act]

lemma wA_mem_F {D : Data 1 1 2 Sc} (hD : Good D) : wA ∈ F D := by
  rw [hD.1]; norm_num [wA, act]

section Opt

variable {D : Data 1 1 2 Sc} (hD : Good D)
include hD

lemma score_toPar (w : Inst 1 1 → ℝ) (θ : Fin 3 → ℝ) :
    score D w (toPar θ) = w (Sum.inl 0) * θ 2 + w (Sum.inr 0) * θ 0
      - w (Sum.inl 0) ^ 2 / 200 - w (Sum.inr 0) ^ 2 / 80 := by
  rw [hD.2.2]; simp [toPar]

lemma maxE {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) :
    maximizers (fun v => score D v (toPar θ)) (E D) = {wE} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff, hD.2.1, score_toPar hD, hθ]
  constructor
  · rintro ⟨⟨ha, hp, hp1⟩, hmax⟩
    have h := hmax wE ⟨by norm_num [wE, act], by norm_num [wE, act], by norm_num [wE, act]⟩
    simp only [wE, act, Sum.elim_inl, Sum.elim_inr, ha] at h
    have hsq : (2 * w (Sum.inr 0) - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * w (Sum.inr 0) - 1)]
    have hp' : w (Sum.inr 0) = 1 / 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
    rw [inst_ext w, ha, hp']; rfl
  · rintro rfl
    refine ⟨⟨by norm_num [wE, act], by norm_num [wE, act], by norm_num [wE, act]⟩, ?_⟩
    rintro v ⟨ha, hp, hp1⟩
    simp only [wE, act, Sum.elim_inl, Sum.elim_inr, ha]
    nlinarith [sq_nonneg (2 * v (Sum.inr 0) - 1)]

lemma etfSup_eq {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) : etfSup D θ = 1 / 320 := by
  have h : wE ∈ maximizers (fun v => score D v (toPar θ)) (E D) := by rw [maxE hD hθ]; rfl
  rw [etfSup, sSup_of_max h, score_toPar hD, hθ]
  norm_num [wE, act]

lemma Adv_eq {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) (w : Inst 1 1 → ℝ) :
    Adv D w θ = score D w (toPar θ) - 1 / 320 := by
  rw [Adv, etfSup_eq hD hθ]

/-- For `α ≤ 0` the full optimum is the ETF optimum `(0, 1/2)`. -/
lemma maxF_low {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) (hα : θ 2 ≤ 0) :
    maximizers (fun w => score D w (toPar θ)) (F D) = {wE} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff, hD.1, score_toPar hD, hθ]
  constructor
  · rintro ⟨⟨ha, hp, hs⟩, hmax⟩
    have h := hmax wE ⟨by norm_num [wE, act], by norm_num [wE, act], by norm_num [wE, act]⟩
    simp only [wE, act, Sum.elim_inl, Sum.elim_inr] at h
    have hαa : w (Sum.inl 0) * θ 2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hα
    have ha0 : w (Sum.inl 0) = 0 := by
      nlinarith [sq_nonneg (2 * w (Sum.inr 0) - 1), sq_nonneg (w (Sum.inl 0))]
    rw [ha0] at h
    have hsq : (2 * w (Sum.inr 0) - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * w (Sum.inr 0) - 1)]
    have hp' : w (Sum.inr 0) = 1 / 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
    rw [inst_ext w, ha0, hp']; rfl
  · rintro rfl
    refine ⟨⟨by norm_num [wE, act], by norm_num [wE, act], by norm_num [wE, act]⟩, ?_⟩
    rintro v ⟨ha, hp, hs⟩
    simp only [wE, act, Sum.elim_inl, Sum.elim_inr]
    nlinarith [sq_nonneg (2 * v (Sum.inr 0) - 1), mul_nonpos_of_nonneg_of_nonpos ha hα]

/-- For `α ≥ 1/10` the unique full optimum is `w_A = (1, 0)`. -/
lemma maxF_high {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) (hα : 1 / 10 ≤ θ 2) :
    maximizers (fun w => score D w (toPar θ)) (F D) = {wA} := by
  have key : ∀ a p : ℝ, 0 ≤ a → 0 ≤ p → a + p ≤ 1 →
      31 / 400 * (1 - a) ≤ (1 * θ 2 + 0 * (1 / 80) - 1 ^ 2 / 200 - 0 ^ 2 / 80)
        - (a * θ 2 + p * (1 / 80) - a ^ 2 / 200 - p ^ 2 / 80) := by
    intro a p ha hp hs
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) (by linarith : (0 : ℝ) ≤ θ 2 - 1 / 10),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) ha, mul_nonneg hp hp]
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff, hD.1, score_toPar hD, hθ]
  constructor
  · rintro ⟨⟨ha, hp, hs⟩, hmax⟩
    have h := hmax wA ⟨by norm_num [wA, act], by norm_num [wA, act], by norm_num [wA, act]⟩
    simp only [wA, act, Sum.elim_inl, Sum.elim_inr] at h
    have k := key _ _ ha hp hs
    have ha1 : w (Sum.inl 0) = 1 := by linarith
    have hp0 : w (Sum.inr 0) = 0 := by linarith
    rw [inst_ext w, ha1, hp0]; rfl
  · rintro rfl
    refine ⟨⟨by norm_num [wA, act], by norm_num [wA, act], by norm_num [wA, act]⟩, ?_⟩
    rintro v ⟨ha, hp, hs⟩
    have k := key _ _ ha hp hs
    simp only [wA, act, Sum.elim_inl, Sum.elim_inr]
    linarith

lemma Adv_minus {w : Inst 1 1 → ℝ} (hw : w ∈ F D) (ha : 0 < w (Sum.inl 0)) :
    Adv D w thetaMinus < 0 := by
  rw [Adv_eq hD (by norm_num [thetaMinus]), score_toPar hD]
  rw [hD.1] at hw
  obtain ⟨_, hp, hs⟩ := hw
  norm_num [thetaMinus]
  nlinarith [sq_nonneg (2 * w (Sum.inr 0) - 1), sq_nonneg (w (Sum.inl 0))]

lemma Gstar_of_max {θ : Fin 3 → ℝ} (hθ : θ 0 = 1 / 80) {w : Inst 1 1 → ℝ}
    (h : maximizers (fun w => score D w (toPar θ)) (F D) = {w}) :
    Gstar D θ = score D w (toPar θ) - 1 / 320 := by
  have hm : w ∈ maximizers (fun w => score D w (toPar θ)) (F D) := by rw [h]; rfl
  rw [Gstar, sSup_of_max hm, etfSup_eq hD hθ]

lemma Gstar_minus : Gstar D thetaMinus = 0 := by
  rw [Gstar_of_max hD (by norm_num [thetaMinus]) (maxF_low hD (by norm_num [thetaMinus])
    (by norm_num [thetaMinus])), score_toPar hD]
  norm_num [wE, act, thetaMinus]

lemma Adv_wA (α : ℝ) : Adv D wA ![1 / 80, 0, α] = α - 13 / 1600 := by
  rw [Adv_eq hD (by norm_num), score_toPar hD]
  norm_num [wA, act]
  ring

lemma Adv_wA_plus : Adv D wA thetaPlus = 147 / 1600 := by
  rw [show thetaPlus = ![1 / 80, 0, 1 / 10] from rfl, Adv_wA hD]; norm_num

lemma Gstar_plus : Gstar D thetaPlus = 147 / 1600 := by
  rw [Gstar_of_max hD (by norm_num [thetaPlus]) (maxF_high hD (by norm_num [thetaPlus])
    (by norm_num [thetaPlus])), score_toPar hD]
  norm_num [wA, act, thetaPlus]

end Opt

/-! ### The parameter domain -/

lemma theta4_eq : Theta4 V4 = {θ | θ 0 = 1 / 80 ∧ θ 1 = 0 ∧ -1 / 10 ≤ θ 2 ∧ θ 2 ≤ 1 / 10} := by
  ext θ
  simp only [Theta4, V4, Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    simp [thetaPlus, thetaMinus]
    refine ⟨by linear_combination (1 / 80 : ℝ) * hab, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨(1 + 10 * θ 2) / 2, (1 - 10 * θ 2) / 2, by linarith, by linarith, by ring, ?_⟩
    funext i
    fin_cases i <;> simp [thetaPlus, thetaMinus, h0, h1] <;> ring

lemma mem_theta4 {θ : Fin 3 → ℝ} (h : θ ∈ Theta4 V4) :
    θ 0 = 1 / 80 ∧ θ 1 = 0 ∧ -1 / 10 ≤ θ 2 ∧ θ 2 ≤ 1 / 10 := by
  rw [theta4_eq] at h; exact h

lemma plus_mem : thetaPlus ∈ Theta4 V4 := by rw [theta4_eq]; norm_num [thetaPlus]

lemma minus_mem : thetaMinus ∈ Theta4 V4 := by rw [theta4_eq]; norm_num [thetaMinus]

/-! ### Part 1 -/

/-- The ETF shock of law I. -/
abbrev zEI : Sc → Fin 1 → ℝ := fun x => ![sg x.2.1 * (3 - sg x.2.2) / 20]

/-- The ETF shock of law R. -/
abbrev zER : Sc → Fin 1 → ℝ := fun x => ![sg x.2.1 * (3 - sg x.1) / 20]

lemma dataI_eq : dataI = baseData zEI := rfl

lemma dataR_eq : dataR = baseData zER := rfl

lemma admissible (zE : Sc → Fin 1 → ℝ) (hc : ∀ j, ∑ s, (1 / 8 : ℝ) * zE s j = 0)
    (hpos : ∀ s, 0 < 1 + (1 / 80 + zE s 0)) : M4Admissible (baseData zE) V4 := by
  refine ⟨Or.inl rfl, ⟨thetaPlus, by simp [V4]⟩, fun _ => by norm_num [baseData], ?_,
    fun k => by simp [baseData], fun j => ?_, fun j => by simpa [baseData] using hc j,
    by norm_num [baseData], fun i => by simp [baseData], by norm_num [baseData],
    by rw [W0_base]; norm_num, ?_, fun i => by simp [baseData], ?_⟩
  · simp [baseData]
  · fin_cases j
    simp [baseData, Fintype.sum_prod_type, sg]
    norm_num
  · rw [w0_base, F_base]; simp
  · intro θ hθ x i
    simp only [V4, Finset.mem_insert, Finset.mem_singleton] at hθ
    have hs := sg_bounds x.1
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
    · rw [ret_inl]
      rcases hθ with rfl | rfl <;> norm_num [thetaPlus, thetaMinus] <;> linarith
    · rw [ret_inr]
      rcases hθ with rfl | rfl <;> simpa [thetaPlus, thetaMinus] using hpos x

lemma adm_I : M4Admissible dataI V4 :=
  admissible zEI (fun j => by fin_cases j; simp [Fintype.sum_prod_type, sg]; norm_num)
    (by rintro ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> norm_num [sg])

lemma adm_R : M4Admissible dataR V4 :=
  admissible zER (fun j => by fin_cases j; simp [Fintype.sum_prod_type, sg]; norm_num)
    (by rintro ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> norm_num [sg])

lemma omega_I : Omega dataI = !![0, 0, 0; 0, 0, 0; 0, 0, 1 / 100] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Omega, zeta, dataI, baseData, Fintype.sum_prod_type, sg]; try norm_num)

lemma omega_R : Omega dataR = Omega dataI := rfl

lemma marg (θ : Fin 3 → ℝ) (i : Inst 1 1) (x : ℝ) :
    (∑ s, if ret dataI (toPar θ) s i = x then dataI.q s else 0)
      = ∑ s, if ret dataR (toPar θ) s i = x then dataR.q s else 0 := by
  rw [dataI_eq, dataR_eq]
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
  · simp only [ret_inl]; rfl
  · let e : Sc ≃ Sc :=
      ⟨fun y => (y.2.2, y.2.1, y.1), fun y => (y.2.2, y.2.1, y.1), fun _ => rfl, fun _ => rfl⟩
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [ret_inr]
    rfl

/-- The record vector of the common data, coordinate by coordinate. -/
def recV (zE : Sc → Fin 1 → ℝ) (θ : Fin 3 → ℝ) (x : Sc) : Fin 2 ⊕ Inst 1 1 → ℝ :=
  Sum.elim ![θ 0, θ 1] (act (θ 2 + sg x.1 / 10) (θ 0 + zE x 0))

lemma obsCov_base (zE : Sc → Fin 1 → ℝ) (θ : Fin 3 → ℝ) (i j : Fin 2 ⊕ Inst 1 1) :
    obsCov (baseData zE) θ i j = ∑ x, 1 / 8 * ((recV zE θ x i - ∑ y, 1 / 8 * recV zE θ y i)
      * (recV zE θ x j - ∑ y, 1 / 8 * recV zE θ y j)) := by
  have hv : ∀ x, Sum.elim (record (baseData zE) θ x).f (ret (baseData zE) (toPar θ) x)
      = recV zE θ x := fun x => by
    funext k
    rcases k with k | k | k
    · fin_cases k <;> simp [recV, record, baseData, toPar]
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simp [recV, act, ret_inl]
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simp [recV, act, ret_inr]
  simp only [obsCov, hv]
  rfl

lemma obsCov_eq (θ : Fin 3 → ℝ) : obsCov dataI θ = obsCov dataR θ := by
  ext i j
  rw [dataI_eq, dataR_eq, obsCov_base, obsCov_base]
  rcases i with i | i | i <;> rcases j with j | j | j <;> fin_cases i <;> fin_cases j <;>
    simp [recV, act, Fintype.sum_prod_type, sg] <;> ring

lemma thetaHat_hist (θ : Fin 3 → ℝ) {N : ℕ} (σ : Fin N → Sc) :
    thetaHat dataI (hist dataI θ σ) = thetaHat dataR (hist dataR θ σ) := by
  simp only [thetaHat, hist, dataI_eq, dataR_eq, X_rec]

lemma score_IR (w : Inst 1 1 → ℝ) (θ : Params 1 2) : score dataI w θ = score dataR w θ := by
  rw [good_I.2.2, good_R.2.2]

lemma F_IR : F dataI = F dataR := by rw [good_I.1, good_R.1]

lemma E_IR : E dataI = E dataR := by rw [good_I.2.1, good_R.2.1]

lemma etfSup_IR (θ : Fin 3 → ℝ) : etfSup dataI θ = etfSup dataR θ := by
  simp only [etfSup, E_IR, score_IR]

lemma Adv_IR (w : Inst 1 1 → ℝ) (θ : Fin 3 → ℝ) : Adv dataI w θ = Adv dataR w θ := by
  simp only [Adv, etfSup_IR, score_IR]

lemma part1_explicit {D : Data 1 1 2 Sc} (hD : Good D) :
    F D = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} ∧
    E D = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} ∧
    (∀ θ ∈ Theta4 V4, ∀ w, score D w (toPar θ) = w (Sum.inl 0) * θ 2 + w (Sum.inr 0) / 80
      - w (Sum.inl 0) ^ 2 / 200 - w (Sum.inr 0) ^ 2 / 80) ∧
    (∀ θ ∈ Theta4 V4, etfSup D θ = 1 / 320 ∧
      maximizers (fun v => score D v (toPar θ)) (E D) = {wE}) ∧
    (∀ w ∈ F D, 0 < w (Sum.inl 0) → Adv D w thetaMinus < 0) ∧ Gstar D thetaMinus = 0 ∧
    maximizers (fun w => score D w (toPar thetaPlus)) (F D) = {wA} ∧
    Adv D wA thetaPlus = 147 / 1600 ∧ Gstar D thetaPlus = 147 / 1600 ∧
    ∀ α : ℝ, Adv D wA ![1 / 80, 0, α] = α - 13 / 1600 := by
  refine ⟨hD.1, hD.2.1, fun θ hθ w => ?_, fun θ hθ => ⟨etfSup_eq hD (mem_theta4 hθ).1,
    maxE hD (mem_theta4 hθ).1⟩, fun w hw ha => Adv_minus hD hw ha, Gstar_minus hD,
    maxF_high hD (by norm_num [thetaPlus]) (by norm_num [thetaPlus]), Adv_wA_plus hD,
    Gstar_plus hD, Adv_wA hD⟩
  rw [score_toPar hD, (mem_theta4 hθ).1]
  ring

theorem sameEconomics : SameEconomics := by
  refine ⟨adm_I, adm_R, theta4_eq, omega_I, omega_R, cov_I, cov_R.trans cov_I.symm, marg,
    obsCov_eq, F_IR, E_IR, fun w => rfl, score_IR, fun θ => ?_, fun θ N A => ?_, ?_⟩
  · simp only [Gstar, etfSup_IR, F_IR, score_IR]
  · simp only [prob, Set.mem_ofPred_eq, thetaHat_hist]
    rfl
  · rintro D (rfl | rfl)
    · exact part1_explicit good_I
    · exact part1_explicit good_R

/-! ### Part 2: counting, records and the upper bound -/

lemma sum_mass (N : ℕ) : ∑ _σ : Fin N → Sc, ((1 : ℝ) / 8) ^ N = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  simp only [Sc, Fintype.card_prod, Fintype.card_bool]
  push_cast
  rw [← mul_pow]
  norm_num

lemma sum_all (N : ℕ) (b : Bool) :
    ∑ σ : Fin N → Sc, (if ∀ l, (σ l).1 = b then ((1 : ℝ) / 8) ^ N else 0) = (1 / 2) ^ N := by
  have h : ∀ σ : Fin N → Sc, (if ∀ l, (σ l).1 = b then ((1 : ℝ) / 8) ^ N else 0)
      = ∏ l, (if (σ l).1 = b then (1 : ℝ) / 8 else 0) := by
    intro σ
    rw [Fintype.prod_ite_zero]
    simp
  simp only [h]
  rw [← Fintype.prod_sum (fun _ : Fin N => fun x : Sc => if x.1 = b then (1 : ℝ) / 8 else 0)]
  have : ∑ x : Sc, (if x.1 = b then (1 : ℝ) / 8 else 0) = 1 / 2 := by
    cases b <;> simp [Fintype.sum_prod_type] <;> norm_num
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma record_base (zE : Sc → Fin 1 → ℝ) (θ : Fin 3 → ℝ) (x : Sc) :
    record (baseData zE) θ x = ⟨![θ 0, θ 1], θ 2 + sg x.1 / 10, fun _ => θ 0 + zE x 0⟩ := by
  have h1 := ret_inl zE θ x
  have h2 := ret_inr zE θ x
  simp only [record, h1]
  congr 1
  · funext k; fin_cases k <;> simp [baseData, toPar]
  · funext j; obtain rfl : j = 0 := Subsingleton.elim _ _; exact h2

lemma hist_rA (zE : Sc → Fin 1 → ℝ) (θ : Fin 3 → ℝ) {N : ℕ} (σ : Fin N → Sc) (l : Fin N) :
    (hist (baseData zE) θ σ l).rA = θ 2 + sg (σ l).1 / 10 := by
  simp only [hist, record_base]

/-- Flip the active sign `s`. -/
def flip : Sc ≃ Sc := ⟨fun x => (!x.1, x.2), fun x => (!x.1, x.2), fun x => by simp, fun x => by simp⟩

/-- On histories with every active return zero, `θ₊` and `θ₋` agree after flipping `s`. -/
lemma hist_flip {N : ℕ} (σ : Fin N → Sc) (h : ∀ l, (σ l).1 = false) :
    hist dataI thetaPlus σ = hist dataI thetaMinus (fun l => flip (σ l)) := by
  funext l
  have hl := h l
  simp only [hist, dataI_eq, record_base, flip, Equiv.coe_fn_mk, hl]
  norm_num [thetaPlus, thetaMinus, sg]

lemma kernel_toReal_le_one {N : ℕ} (ρ : Rule N) (H : Fin N → Record 1) (T : Set (Inst 1 1 → ℝ)) :
    0 ≤ (ρ.kernel H T).toReal ∧ (ρ.kernel H T).toReal ≤ 1 := by
  have := ρ.isProb H
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩

/-- At `θ₋` every certification is false. -/
lemma cert_le_false {N : ℕ} {ρ : Rule N} (hA : Admits dataI ρ) (H : Fin N → Record 1) :
    (ρ.kernel H {w | 0 < w (Sum.inl 0)}).toReal
      ≤ (ρ.kernel H {w | 0 < w (Sum.inl 0) ∧ Adv dataI w thetaMinus ≤ 0}).toReal := by
  have := ρ.isProb H
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  calc ρ.kernel H {w | 0 < w (Sum.inl 0)}
      ≤ ρ.kernel H ({w | 0 < w (Sum.inl 0) ∧ Adv dataI w thetaMinus ≤ 0}
          ∪ {w | w ≠ wE ∧ ¬ (w ∈ F dataI ∧ 0 < w (Sum.inl 0))}) := by
        apply measure_mono
        intro w hw
        simp only [Set.mem_ofPred_eq] at hw
        by_cases hF : w ∈ F dataI
        · exact Or.inl ⟨hw, (Adv_minus good_I hF hw).le⟩
        · refine Or.inr ⟨?_, fun h => hF h.1⟩
          rintro rfl
          simp [wE, act] at hw
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hA H, add_zero]

lemma certProb_le_one (zE : Sc → Fin 1 → ℝ) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : Rule N) :
    certProb (baseData zE) θ ρ ≤ 1 := by
  rw [certProb, ← sum_mass N]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [mass_base]
  have := kernel_toReal_le_one ρ (hist (baseData zE) θ σ) {w | 0 < w (Sum.inl 0)}
  have : (0 : ℝ) ≤ (1 / 8) ^ N := by positivity
  nlinarith

/-- The certification probability of a rule at a history. -/
def cv {N : ℕ} (ρ : Rule N) (H : Fin N → Record 1) : ℝ :=
  (ρ.kernel H {w | 0 < w (Sum.inl 0)}).toReal

lemma certProb_cv (D : Data 1 1 2 Sc) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : Rule N) :
    certProb D θ ρ = ∑ σ : Fin N → Sc, mass D σ * cv ρ (hist D θ σ) := rfl

/-- The upper bound for law I. -/
lemma upper_I {N : ℕ} {η : ℝ} {ρ : Rule N} (hA : Admits dataI ρ) (hV : Valid dataI N η ρ) :
    certProb dataI thetaPlus ρ ≤ 1 - (1 / 2) ^ N + η := by
  set m : ℝ := (1 / 8) ^ N
  have hm : 0 ≤ m := by positivity
  let fl : (Fin N → Sc) ≃ (Fin N → Sc) := Equiv.arrowCongr (Equiv.refl _) flip
  have hfl : ∀ σ l, fl σ l = flip (σ l) := fun _ _ => rfl
  -- split into histories with a nonzero active return and those without
  have split : certProb dataI thetaPlus ρ
      ≤ ∑ σ : Fin N → Sc, (if ∀ l, (σ l).1 = false then 0 else m)
        + ∑ σ : Fin N → Sc,
          (if ∀ l, (σ l).1 = false then m * cv ρ (hist dataI thetaPlus σ) else 0) := by
    rw [certProb_cv, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [show mass dataI σ = m from mass_base _ σ]
    have := kernel_toReal_le_one ρ (hist dataI thetaPlus σ) {w | 0 < w (Sum.inl 0)}
    rw [← cv] at this
    split_ifs <;> nlinarith
  have first : ∑ σ : Fin N → Sc, (if ∀ l, (σ l).1 = false then 0 else m) = 1 - (1 / 2) ^ N := by
    have e : ∀ σ : Fin N → Sc, (if ∀ l, (σ l).1 = false then 0 else m)
        = m - (if ∀ l, (σ l).1 = false then m else 0) := fun σ => by split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, m, sum_mass, sum_all]
  have second : ∑ σ : Fin N → Sc,
      (if ∀ l, (σ l).1 = false then m * cv ρ (hist dataI thetaPlus σ) else 0) ≤ η := by
    calc _ = ∑ σ : Fin N → Sc,
          (if ∀ l, (fl σ l).1 = true then m * cv ρ (hist dataI thetaMinus (fl σ)) else 0) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          split_ifs with h h'
          · rw [hist_flip σ h]; rfl
          · exact absurd (fun l => by simp [hfl, flip, h l]) h'
          · rename_i h'
            exact absurd (fun l => by
              have := h' l; simp only [hfl, flip, Equiv.coe_fn_mk] at this; simpa using this) h
          · rfl
      _ = ∑ σ : Fin N → Sc,
          (if ∀ l, (σ l).1 = true then m * cv ρ (hist dataI thetaMinus σ) else 0) :=
          Equiv.sum_comp fl (fun σ => if ∀ l, (σ l).1 = true then m * cv ρ (hist dataI thetaMinus σ)
            else 0)
      _ ≤ ∑ σ : Fin N → Sc, mass dataI σ *
            (ρ.kernel (hist dataI thetaMinus σ)
              {w | 0 < w (Sum.inl 0) ∧ Adv dataI w thetaMinus ≤ 0}).toReal := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [show mass dataI σ = m from mass_base _ σ]
          have h1 := cert_le_false hA (hist dataI thetaMinus σ)
          have h0 := kernel_toReal_le_one ρ (hist dataI thetaMinus σ) {w | 0 < w (Sum.inl 0)}
          rw [← cv] at h1 h0
          split_ifs
          · exact mul_le_mul_of_nonneg_left h1 hm
          · exact mul_nonneg hm (le_trans h0.1 h1)
      _ ≤ η := hV _ minus_mem
  linarith

/-! ### Part 2: attaining rules -/

lemma wA_ne_wE : wA ≠ wE := fun h => by simpa [wA, wE, act] using congrFun h (Sum.inl 0)

lemma dirac_toReal (w : Inst 1 1 → ℝ) (T : Set (Inst 1 1 → ℝ)) :
    (Measure.dirac w T).toReal = if w ∈ T then 1 else 0 := by
  by_cases h : w ∈ T <;> simp [h]

/-- The coin mixture: `w_A` with probability `c`, else the fallback. -/
def mixA (c : ℝ) : Measure (Inst 1 1 → ℝ) :=
  ENNReal.ofReal c • Measure.dirac wA + ENNReal.ofReal (1 - c) • Measure.dirac wE

lemma mixA_prob {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : IsProbabilityMeasure (mixA c) := by
  constructor
  simp only [mixA, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hc0 (by linarith)]
  simp

lemma mixA_toReal {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (T : Set (Inst 1 1 → ℝ)) :
    (mixA c T).toReal = (if wA ∈ T then c else 0) + (if wE ∈ T then 1 - c else 0) := by
  have h1 : 0 ≤ 1 - c := by linarith
  by_cases hA : wA ∈ T <;> by_cases hE : wE ∈ T <;>
    simp [mixA, hA, hE, ENNReal.toReal_add, hc0, h1]

lemma mixA_zero {c : ℝ} {T : Set (Inst 1 1 → ℝ)} (hA : wA ∉ T) (hE : wE ∉ T) : mixA c T = 0 := by
  simp [mixA, hA, hE]

lemma dirac_zero {w : Inst 1 1 → ℝ} {T : Set (Inst 1 1 → ℝ)} (hw : w = wA ∨ w = wE) (hA : wA ∉ T)
    (hE : wE ∉ T) : Measure.dirac w T = 0 := by
  rcases hw with rfl | rfl <;> simp [hA, hE]

lemma bad_A (D : Data 1 1 2 Sc) (hD : Good D) :
    wA ∉ {w : Inst 1 1 → ℝ | w ≠ wE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} := by
  rintro ⟨-, h⟩; exact h ⟨wA_mem_F hD, by norm_num [wA, act]⟩

lemma bad_E (D : Data 1 1 2 Sc) :
    wE ∉ {w : Inst 1 1 → ℝ | w ≠ wE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} := by
  rintro ⟨h, -⟩; exact h rfl

lemma other_A : wA ∉ {w : Inst 1 1 → ℝ | w ≠ wA ∧ w ≠ wE} := by rintro ⟨h, -⟩; exact h rfl

lemma other_E : wE ∉ {w : Inst 1 1 → ℝ | w ≠ wA ∧ w ≠ wE} := by rintro ⟨-, h⟩; exact h rfl

lemma cert_A : wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0)} := by norm_num [wA, act]

lemma cert_E : wE ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0)} := by norm_num [wE, act]

lemma false_E (D : Data 1 1 2 Sc) (θ : Fin 3 → ℝ) :
    wE ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ 0} := by norm_num [wE, act]

lemma false_A {D : Data 1 1 2 Sc} (hD : Good D) {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) :
    wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ 0} ↔ θ 2 ≤ 13 / 1600 := by
  obtain ⟨h0, h1, -, -⟩ := mem_theta4 hθ
  have e : θ = ![1 / 80, 0, θ 2] := by funext i; fin_cases i <;> simp [h0, h1]
  rw [e]
  simp only [Set.mem_ofPred_eq, Adv_wA hD]
  norm_num [wA, act]

/-- The value of `α` identified by a nonzero active return `x` (the other sign leaves `Θ₄`). -/
def a1 (x : ℝ) : ℝ := if 0 < x then x - 1 / 10 else x + 1 / 10

lemma sg_cases (b : Bool) : sg b = 1 ∨ sg b = -1 := by cases b <;> simp [sg]

lemma a1_hist (zE : Sc → Fin 1 → ℝ) {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) {N : ℕ}
    (σ : Fin N → Sc) (l : Fin N) (h : (hist (baseData zE) θ σ l).rA ≠ 0) :
    a1 (hist (baseData zE) θ σ l).rA = θ 2 := by
  obtain ⟨-, -, h2, h3⟩ := mem_theta4 hθ
  have hx := hist_rA zE θ σ l
  rw [hx] at h ⊢
  rcases sg_cases (σ l).1 with hs | hs <;> rw [hs] at h ⊢
  · have : 0 < θ 2 + 1 / 10 := lt_of_le_of_ne (by linarith) (Ne.symm h)
    simp only [a1, this, ↓reduceIte]; ring
  · have : ¬ 0 < θ 2 + -1 / 10 := by linarith [lt_of_le_of_ne (by linarith : θ 2 + -1 / 10 ≤ 0) h]
    simp only [a1, this, ↓reduceIte]; ring

/-- Law I's rule certifies `w_A` when some nonzero active return identifies `α > 13/1600`. -/
def certI {N : ℕ} (H : Fin N → Record 1) : Prop := ∃ l, (H l).rA ≠ 0 ∧ 13 / 1600 < a1 (H l).rA

lemma certI_iff (zE : Sc → Fin 1 → ℝ) {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) {N : ℕ}
    (σ : Fin N → Sc) (hn : ∃ l, (hist (baseData zE) θ σ l).rA ≠ 0) :
    certI (hist (baseData zE) θ σ) ↔ 13 / 1600 < θ 2 := by
  constructor
  · rintro ⟨l, hl, hc⟩; rwa [a1_hist zE hθ σ l hl] at hc
  · intro hc
    obtain ⟨l, hl⟩ := hn
    exact ⟨l, hl, by rwa [a1_hist zE hθ σ l hl]⟩

/-- The coin probability `min(1, η 2^N)`. -/
def coin (N : ℕ) (η : ℝ) : ℝ := min 1 (η * 2 ^ N)

lemma coin_bounds {N : ℕ} {η : ℝ} (hη : 0 ≤ η) : 0 ≤ coin N η ∧ coin N η ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

/-- Law I's attaining rule. -/
def ruleI (N : ℕ) (η : ℝ) (hη : 0 ≤ η) : Rule N where
  kernel H := if ∃ l, (H l).rA ≠ 0 then Measure.dirac (if certI H then wA else wE)
    else mixA (coin N η)
  isProb H := by
    by_cases h : ∃ l, (H l).rA ≠ 0
    · simp only [h, ↓reduceIte]; infer_instance
    · simp only [h, ↓reduceIte]; exact mixA_prob (coin_bounds hη).1 (coin_bounds hη).2

lemma ruleI_toReal {N : ℕ} {η : ℝ} (hη : 0 ≤ η) (H : Fin N → Record 1) (T : Set (Inst 1 1 → ℝ)) :
    ((ruleI N η hη).kernel H T).toReal = if ∃ l, (H l).rA ≠ 0 then
      (if (if certI H then wA else wE) ∈ T then 1 else 0)
      else (if wA ∈ T then coin N η else 0) + (if wE ∈ T then 1 - coin N η else 0) := by
  by_cases h : ∃ l, (H l).rA ≠ 0
  · simp only [ruleI, h, ↓reduceIte]; exact dirac_toReal _ _
  · simp only [ruleI, h, ↓reduceIte]; exact mixA_toReal (coin_bounds hη).1 (coin_bounds hη).2 T

lemma ruleI_zero {N : ℕ} {η : ℝ} (hη : 0 ≤ η) (H : Fin N → Record 1) {T : Set (Inst 1 1 → ℝ)}
    (hA : wA ∉ T) (hE : wE ∉ T) : (ruleI N η hη).kernel H T = 0 := by
  by_cases h : ∃ l, (H l).rA ≠ 0
  · simp only [ruleI, h, ↓reduceIte]
    exact dirac_zero (by by_cases hc : certI H <;> simp [hc]) hA hE
  · simp only [ruleI, h, ↓reduceIte]; exact mixA_zero hA hE

lemma allZero_iff (zE : Sc → Fin 1 → ℝ) {N : ℕ} (σ : Fin N → Sc) :
    (∃ l, (hist (baseData zE) thetaPlus σ l).rA ≠ 0) ↔ ¬ ∀ l, (σ l).1 = false := by
  simp only [hist_rA, thetaPlus]
  constructor
  · rintro ⟨l, hl⟩ h
    apply hl
    rw [h l]; norm_num [sg]
  · intro h
    obtain ⟨l, hl⟩ := not_forall.mp h
    have hl' : (σ l).1 = true := by simpa using hl
    refine ⟨l, ?_⟩
    rw [hl']; norm_num [sg]

lemma certProb_ruleI {N : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    certProb dataI thetaPlus (ruleI N η hη) = 1 - (1 / 2) ^ N + coin N η * (1 / 2) ^ N := by
  have hv : ∀ σ : Fin N → Sc, mass dataI σ * cv (ruleI N η hη) (hist dataI thetaPlus σ)
      = (1 / 8) ^ N - (if ∀ l, (σ l).1 = false then (1 / 8) ^ N else 0)
        + coin N η * (if ∀ l, (σ l).1 = false then (1 / 8) ^ N else 0) := by
    intro σ
    rw [show mass dataI σ = (1 / 8) ^ N from mass_base _ σ, cv, ruleI_toReal]
    have hz := allZero_iff zEI σ
    rw [← dataI_eq] at hz
    by_cases h : ∀ l, (σ l).1 = false
    · have hn : ¬ ∃ l, (hist dataI thetaPlus σ l).rA ≠ 0 := fun h' => hz.mp h' h
      simp only [hn, h, ↓reduceIte, cert_A, cert_E, implies_true]
      ring
    · have hn : ∃ l, (hist dataI thetaPlus σ l).rA ≠ 0 := hz.mpr h
      have hc := (certI_iff zEI plus_mem σ (by rw [← dataI_eq]; exact hn)).mpr
        (by norm_num [thetaPlus])
      rw [← dataI_eq] at hc
      simp only [hn, h, hc, ↓reduceIte, cert_A]
      ring
  rw [certProb_cv, Finset.sum_congr rfl fun σ _ => hv σ, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mass, sum_all]

lemma falseProb_ruleI {N : ℕ} {η : ℝ} (hη : 0 ≤ η) {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) :
    falseProb dataI θ (ruleI N η hη) ≤ coin N η * (1 / 2) ^ N := by
  obtain ⟨-, -, h2, h3⟩ := mem_theta4 hθ
  have hc := coin_bounds (N := N) hη
  have hv : ∀ σ : Fin N → Sc, mass dataI σ * ((ruleI N η hη).kernel (hist dataI θ σ)
        {w | 0 < w (Sum.inl 0) ∧ Adv dataI w θ ≤ 0}).toReal
      ≤ coin N η * (if ∀ l, (σ l).1 = true then (1 / 8) ^ N else 0) := by
    intro σ
    have hEf := false_E dataI θ
    rw [show mass dataI σ = (1 / 8) ^ N from mass_base _ σ, ruleI_toReal]
    simp only [hEf, ↓reduceIte, add_zero]
    have hpos : (0 : ℝ) ≤ (1 / 8) ^ N := by positivity
    by_cases hn : ∃ l, (hist dataI θ σ l).rA ≠ 0
    · have hci := certI_iff zEI hθ σ (by rw [← dataI_eq]; exact hn)
      rw [← dataI_eq] at hci
      by_cases hce : certI (hist dataI θ σ)
      · have hA : wA ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv dataI w θ ≤ 0} :=
          fun h' => absurd ((false_A good_I hθ).mp h') (by linarith [hci.mp hce])
        simp only [hn, hce, hA, ↓reduceIte, mul_zero]
        split_ifs <;> nlinarith [hc.1]
      · simp only [hn, hce, hEf, ↓reduceIte, mul_zero]
        split_ifs <;> nlinarith [hc.1]
    · simp only [hn, ↓reduceIte]
      have hn : ∀ l, (hist dataI θ σ l).rA = 0 := fun l => by
        by_contra h'; exact hn ⟨l, h'⟩
      by_cases hA : wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv dataI w θ ≤ 0}
      · have hα := (false_A good_I hθ).mp hA
        have hall : ∀ l, (σ l).1 = true := fun l => by
          have := hn l
          rw [dataI_eq, hist_rA] at this
          cases hs : (σ l).1
          · rw [hs] at this; norm_num [sg] at this; linarith
          · rfl
        simp only [hA, hall, ↓reduceIte, implies_true]
        nlinarith
      · simp only [hA, ↓reduceIte, mul_zero]
        split_ifs <;> nlinarith
  calc falseProb dataI θ (ruleI N η hη)
      ≤ ∑ σ : Fin N → Sc, coin N η * (if ∀ l, (σ l).1 = true then (1 / 8) ^ N else 0) :=
        Finset.sum_le_sum fun σ _ => hv σ
    _ = coin N η * (1 / 2) ^ N := by rw [← Finset.mul_sum, sum_all]

lemma pow_half_mul (N : ℕ) : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num

lemma coin_mul_le {N : ℕ} {η : ℝ} : coin N η * (1 / 2) ^ N ≤ η := by
  have h := pow_half_mul N
  have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
  calc coin N η * (1 / 2) ^ N ≤ η * 2 ^ N * (1 / 2) ^ N :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hp
    _ = η := by rw [mul_assoc, h, mul_one]

lemma attained_I {N : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    1 - (1 / 2) ^ N + coin N η * (1 / 2) ^ N = min 1 (1 - (1 / 2) ^ N + η) := by
  have h := pow_half_mul N
  have hp : (0 : ℝ) < (1 / 2) ^ N := by positivity
  rcases le_total (η * 2 ^ N) 1 with hle | hle
  · have hc : coin N η = η * 2 ^ N := min_eq_right hle
    have : η ≤ (1 / 2) ^ N := by nlinarith
    rw [hc, mul_assoc, h, mul_one, min_eq_right (by linarith)]
  · have hc : coin N η = 1 := min_eq_left hle
    have : (1 / 2) ^ N ≤ η := by nlinarith
    rw [hc, one_mul, min_eq_left (by linarith)]
    ring

lemma admits_I {N : ℕ} {η : ℝ} (hη : 0 ≤ η) : Admits dataI (ruleI N η hη) :=
  fun H => ruleI_zero hη H (bad_A _ good_I) (bad_E _)

lemma onlyWA_I {N : ℕ} {η : ℝ} (hη : 0 ≤ η) : CertifiesOnlyWA (ruleI N η hη) :=
  fun H => ruleI_zero hη H other_A other_E

lemma valid_I {N : ℕ} {η : ℝ} (hη : 0 ≤ η) : Valid dataI N η (ruleI N η hη) :=
  fun _ hθ => (falseProb_ruleI hη hθ).trans coin_mul_le

/-- The sign of `s` read from the first ETF residual's magnitude (law R). -/
def sR (r : Record 1) : ℝ := if |r.rE 0 - 1 / 80| = 1 / 10 then 1 else -1

/-- Law R's rule: identify `α = r^A - s/10` from record `l0`. -/
def ruleR (N : ℕ) (l0 : Fin N) : Rule N where
  kernel H := Measure.dirac (if 13 / 1600 < (H l0).rA - sR (H l0) / 10 then wA else wE)
  isProb _ := inferInstance

lemma alphaR_hist {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) {N : ℕ} (σ : Fin N → Sc) (l0 : Fin N) :
    (hist dataR θ σ l0).rA - sR (hist dataR θ σ l0) / 10 = θ 2 := by
  obtain ⟨h0, -, -, -⟩ := mem_theta4 hθ
  simp only [hist, dataR_eq, record_base, sR, h0]
  obtain ⟨a, b, c⟩ := σ l0
  cases a <;> cases b <;> norm_num [sg, abs_of_pos, abs_of_neg]

lemma ruleR_zero {N : ℕ} (l0 : Fin N) (H : Fin N → Record 1) {T : Set (Inst 1 1 → ℝ)}
    (hA : wA ∉ T) (hE : wE ∉ T) : (ruleR N l0).kernel H T = 0 :=
  dirac_zero (by
    by_cases hc : 13 / 1600 < (H l0).rA - sR (H l0) / 10 <;> simp [hc]) hA hE

lemma falseProb_ruleR {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V4) {N : ℕ} (l0 : Fin N) :
    falseProb dataR θ (ruleR N l0) = 0 := by
  refine Finset.sum_eq_zero fun σ _ => ?_
  simp only [ruleR, alphaR_hist hθ]
  by_cases h : 13 / 1600 < θ 2
  · have : wA ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv dataR w θ ≤ 0} := fun h' =>
      absurd ((false_A good_R hθ).mp h') (by linarith)
    simp [h, this]
  · have := false_E dataR θ
    simp [h, this]

lemma certProb_ruleR {N : ℕ} (l0 : Fin N) : certProb dataR thetaPlus (ruleR N l0) = 1 := by
  rw [certProb_cv, ← sum_mass N]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show mass dataR σ = (1 / 8) ^ N from mass_base _ σ, cv]
  have h : (13 : ℝ) / 1600 < thetaPlus 2 := by norm_num [thetaPlus]
  simp only [ruleR, alphaR_hist plus_mem, h, ↓reduceIte]
  simp [Set.indicator_of_mem cert_A]

theorem sharpBenchmark : SharpBenchmark := by
  intro N hN η hη0 hη1
  have hη := hη0.le
  set l0 : Fin N := ⟨0, hN⟩
  have hI : certProb dataI thetaPlus (ruleI N η hη) = min 1 (1 - (1 / 2) ^ N + η) := by
    rw [certProb_ruleI, attained_I hη]
  have memI : min 1 (1 - (1 / 2) ^ N + η) ∈ Powers dataI N η :=
    ⟨ruleI N η hη, admits_I hη, valid_I hη, hI.symm⟩
  have upI : ∀ c ∈ Powers dataI N η, c ≤ min 1 (1 - (1 / 2) ^ N + η) := by
    rintro c ⟨ρ, hA, hV, rfl⟩
    exact le_min (by rw [dataI_eq]; exact certProb_le_one _ _ _) (upper_I hA hV)
  refine ⟨⟨memI, upI⟩, ⟨⟨ruleR N l0, fun H => ruleR_zero l0 H (bad_A _ good_R) (bad_E _),
    fun θ hθ => by rw [falseProb_ruleR hθ]; exact hη, (certProb_ruleR l0).symm⟩, ?_⟩,
    ⟨ruleI N η hη, admits_I hη, valid_I hη, onlyWA_I hη, hI⟩,
    ⟨ruleR N l0, fun H => ruleR_zero l0 H (bad_A _ good_R) (bad_E _),
      fun H => ruleR_zero l0 H other_A other_E, fun θ hθ => falseProb_ruleR hθ l0,
      certProb_ruleR l0⟩, fun β hβ0 hβ1 => ⟨?_, ?_⟩⟩
  · rintro c ⟨ρ, -, -, rfl⟩
    rw [dataR_eq]; exact certProb_le_one _ _ _
  · rintro ⟨c, hc, hle⟩
    have := (upI c hc).trans (min_le_right _ _)
    linarith
  · intro h
    exact ⟨_, memI, le_min (by linarith) (by linarith)⟩

/-! ### Part 3: the prescribed gate -/

lemma Cset_IR (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ) : Cset dataI V4 N η th = Cset dataR V4 N η th := rfl

lemma LN_IR (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ) (w : Inst 1 1 → ℝ) :
    LN dataI V4 N η th w = LN dataR V4 N η th w := by
  simp only [LN, Cset_IR, Adv_IR]

lemma wHatF_IR (th : Fin 3 → ℝ) : wHatF dataI th = wHatF dataR th := by
  simp only [wHatF, F_IR, score_IR]

lemma vHatE_IR (th : Fin 3 → ℝ) : vHatE dataI th = vHatE dataR th := by
  simp only [vHatE, E_IR, score_IR]

lemma gateCert_IR (N : ℕ) (η δ : ℝ) (th : Fin 3 → ℝ) :
    gateCert dataI V4 N η δ th = gateCert dataR V4 N η δ th := by
  simp only [gateCert, Cset_IR, wHatF_IR, F_IR, LN_IR]
  rfl

lemma gateAct_IR (N : ℕ) (η δ : ℝ) (th : Fin 3 → ℝ) :
    gateAct dataI V4 N η δ th = gateAct dataR V4 N η δ th := by
  simp only [gateAct, gateCert_IR, wHatF_IR, vHatE_IR]

lemma lexSel_singleton (x : Inst 1 1 → ℝ) : lexSel ({x} : Set (Inst 1 1 → ℝ)) = x := by
  have h : ∃ w, w ∈ ({x} : Set (Inst 1 1 → ℝ)) ∧ ∀ v ∈ ({x} : Set (Inst 1 1 → ℝ)), LexLE w v :=
    ⟨x, rfl, fun v hv => Or.inl hv.symm⟩
  exact (Classical.epsilon_spec h).1

/-- `Ω† = diag(0, 0, 100)` satisfies the Penrose equations. -/
lemma pinv_exists : IsMoorePenrose (Omega dataI) !![0, 0, 0; 0, 0, 0; 0, 0, 100] := by
  rw [omega_I]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three]

lemma pinv_spec : Omega dataI * pinv (Omega dataI) * Omega dataI = Omega dataI :=
  (Classical.epsilon_spec ⟨_, pinv_exists⟩).1

lemma omega_symm : (Omega dataI)ᵀ = Omega dataI := by
  rw [omega_I]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- On `Im Ω`, the quadratic form of any `G` with `ΩGΩ = Ω` is that of `Ω⁻¹`. -/
lemma quad_range {Ω G : Matrix (Fin 3) (Fin 3) ℝ} (hΩ : Ωᵀ = Ω) (hG : Ω * G * Ω = Ω)
    (x : Fin 3 → ℝ) : (Ω *ᵥ x) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) = x ⬝ᵥ (Ω *ᵥ x) := by
  calc (Ω *ᵥ x) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) = (x ᵥ* Ωᵀ) ⬝ᵥ (G *ᵥ (Ω *ᵥ x)) := by rw [Matrix.vecMul_transpose]
    _ = x ⬝ᵥ (Ωᵀ *ᵥ (G *ᵥ (Ω *ᵥ x))) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = x ⬝ᵥ ((Ω * G * Ω) *ᵥ x) := by rw [hΩ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    _ = x ⬝ᵥ (Ω *ᵥ x) := by rw [hG]

lemma omega_mulVec (x : Fin 3 → ℝ) : Omega dataI *ᵥ x = ![0, 0, x 2 / 100] := by
  rw [omega_I]; funext i; fin_cases i <;> (simp [mulVec, dotProduct, Fin.sum_univ_three]; try ring)

lemma quad_omega (x : Fin 3 → ℝ) :
    (Omega dataI *ᵥ x) ⬝ᵥ (pinv (Omega dataI) *ᵥ (Omega dataI *ᵥ x)) = x 2 ^ 2 / 100 := by
  rw [quad_range omega_symm pinv_spec, omega_mulVec]
  simp [dotProduct, Fin.sum_univ_three]
  ring

lemma TN_one (σ : Fin 1 → Sc) : TN dataI σ = 1 := by
  have he : errN dataI σ = Omega dataI *ᵥ ![0, 0, 10 * sg (σ 0).1] := by
    rw [omega_mulVec]
    funext i
    fin_cases i <;> (simp [errN, zeta, dataI, baseData]; try ring)
  rw [TN, he, quad_omega]
  have := sg_sq (σ 0).1
  simp
  nlinarith

lemma tcrit_one {η : ℝ} (hη : 0 < η) : tcrit dataI 1 η = 1 := by
  have hset : {t | (∃ σ : Fin 1 → Sc, 0 < mass dataI σ ∧ TN dataI σ = t) ∧
      1 - η ≤ ∑ σ : Fin 1 → Sc, if TN dataI σ ≤ t then mass dataI σ else 0} = {1} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨σ, -, hσ⟩, -⟩
      rw [← hσ, TN_one]
    · rintro rfl
      refine ⟨⟨fun _ => (true, true, true), by rw [dataI_eq, mass_base]; norm_num, TN_one _⟩, ?_⟩
      simp only [TN_one, le_refl, ↓reduceIte]
      have := sum_mass 1
      simp only [show ∀ σ : Fin 1 → Sc, mass dataI σ = (1 / 8) ^ 1 from fun σ => mass_base _ σ]
      linarith
  rw [tcrit, hset, csInf_singleton]

lemma mem_Aset {η : ℝ} (hη : 0 < η) (e : Fin 3 → ℝ) :
    e ∈ Aset dataI 1 η ↔ e 0 = 0 ∧ e 1 = 0 ∧ -1 / 10 ≤ e 2 ∧ e 2 ≤ 1 / 10 := by
  simp only [Aset, Set.mem_ofPred_eq, Set.mem_range, tcrit_one hη]
  constructor
  · rintro ⟨⟨x, rfl⟩, hq⟩
    rw [quad_omega] at hq
    have hq' : x 2 ^ 2 / 100 ≤ 1 := by simpa using hq
    rw [omega_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, true_and]
    constructor <;> nlinarith [sq_nonneg (x 2 + 10), sq_nonneg (x 2 - 10)]
  · rintro ⟨h0, h1, h2, h3⟩
    have hx : Omega dataI *ᵥ ![0, 0, 100 * e 2] = e := by
      rw [omega_mulVec]; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨⟨_, hx⟩, ?_⟩
    rw [← hx, quad_omega]
    norm_num
    nlinarith

/-- `th₁ = θ̂ = (1/80, 0, 1/5)`. -/
lemma Cset_fifth {η : ℝ} (hη : 0 < η) : Cset dataI V4 1 η ![1 / 80, 0, 1 / 5] = {thetaPlus} := by
  ext θ
  simp only [Cset, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, theta4_eq]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, e, he, rfl⟩
    rw [mem_Aset hη] at he
    obtain ⟨e0, e1, e2, e3⟩ := he
    simp only [Pi.sub_apply] at h0 h1 h2 h3 ⊢
    have : e 2 = 1 / 10 := by
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h3; linarith
    funext i
    fin_cases i <;> (simp [thetaPlus, e0, e1, this]; try norm_num)
  · rintro rfl
    refine ⟨by norm_num [thetaPlus], ![0, 0, 1 / 10], (mem_Aset hη _).mpr (by norm_num), ?_⟩
    funext i
    fin_cases i <;> (simp [thetaPlus]; try norm_num)

lemma gate_fifth {η : ℝ} (hη : 0 < η) : gateCert dataI V4 1 η 0 ![1 / 80, 0, 1 / 5] := by
  have hw : wHatF dataI ![1 / 80, 0, 1 / 5] = wA := by
    rw [wHatF, maxF_high good_I (by norm_num) (by norm_num), lexSel_singleton]
  refine ⟨by rw [Cset_fifth hη]; exact Set.singleton_nonempty _, by rw [hw]; exact wA_mem_F good_I,
    by rw [hw, dataI_eq, w0_base]; norm_num [wA, act], ?_⟩
  rw [hw, LN, Cset_fifth hη]
  simp only [Set.singleton_ne_empty, ↓reduceIte, _root_.iInf_singleton, Adv_wA_plus good_I]
  exact EReal.coe_lt_coe_iff.mpr (by norm_num)

lemma gate_zero {η : ℝ} : ¬ gateCert dataI V4 1 η 0 ![1 / 80, 0, 0] := by
  have hw : wHatF dataI ![1 / 80, 0, 0] = wE := by
    rw [wHatF, maxF_low good_I (by norm_num) (by norm_num), lexSel_singleton]
  rintro ⟨-, -, h, -⟩
  rw [hw, dataI_eq, w0_base] at h
  exact h (by simp [wE, act])

lemma thetaHat_one (σ : Fin 1 → Sc) :
    thetaHat dataI (hist dataI thetaPlus σ) = ![1 / 80, 0, 1 / 10 + sg (σ 0).1 / 10] := by
  simp only [thetaHat, hist, dataI_eq, X_rec, Fin.sum_univ_one]
  norm_num [thetaPlus]

lemma gate_prob {η : ℝ} (hη : 0 < η) :
    prob dataI thetaPlus 1 {H | gateCert dataI V4 1 η 0 (thetaHat dataI H)} = 1 / 2 := by
  have hc : ∀ σ : Fin 1 → Sc, gateCert dataI V4 1 η 0 (thetaHat dataI (hist dataI thetaPlus σ))
      ↔ ∀ l, (σ l).1 = true := by
    intro σ
    rw [thetaHat_one, Fin.forall_fin_one]
    cases (σ 0).1
    · simp only [sg, Bool.false_eq_true, ↓reduceIte, iff_false]
      norm_num
      exact gate_zero
    · simp only [sg, ↓reduceIte, iff_true]
      norm_num
      exact gate_fifth hη
  have := sum_all 1 true
  simp only [prob, Set.mem_ofPred_eq, hc, show ∀ σ : Fin 1 → Sc, mass dataI σ = (1 / 8) ^ 1 from
    fun σ => mass_base _ σ]
  rw [this]; norm_num

theorem gateDiscards : GateDiscards := by
  have hlaw : ∀ N η θ (g : Prop → (Inst 1 1 → ℝ) → Prop),
      prob dataI θ N {H | g (gateCert dataI V4 N η 0 (thetaHat dataI H))
        (gateAct dataI V4 N η 0 (thetaHat dataI H))}
      = prob dataR θ N {H | g (gateCert dataR V4 N η 0 (thetaHat dataR H))
        (gateAct dataR V4 N η 0 (thetaHat dataR H))} := by
    intro N η θ g
    simp only [prob, Set.mem_ofPred_eq, thetaHat_hist, gateCert_IR, gateAct_IR]
    rfl
  refine ⟨fun N η th => ⟨Cset_IR N η th, LN_IR N η th, wHatF_IR th, vHatE_IR th,
    by rw [gateCert_IR], gateAct_IR N η 0 th⟩, fun N H => rfl, hlaw,
    fun η hη0 _ => ⟨gate_prob hη0, ?_⟩, ?_, ?_⟩
  · have := hlaw 1 η thetaPlus (fun c _ => c)
    rw [← this, gate_prob hη0]
  · have := (sharpBenchmark 1 le_rfl (1 / 4) (by norm_num) (by norm_num)).1
    norm_num at this
    exact this
  · exact (sharpBenchmark 1 le_rfl (1 / 4) (by norm_num) (by norm_num)).2.1

theorem proof : Standalone.M4InformationObstruction.statement :=
  ⟨sameEconomics, sharpBenchmark, gateDiscards⟩

end

end Novel.M4InformationObstructionProof

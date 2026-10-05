import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Standalone.M2CompleteSubstitution

/-!
# Proof of claim 006: complete feasible exposure substitution need not eliminate an
active-trading advantage

Direct computation on the finite instance. Every holding is `(a, p)`; for nonnegative holdings
both trades are purchases, so `τ = t/100` with `t = a + p`, and the singular covariance has every
entry `1/100`, so `w'Σw = t²/100`. Uniqueness of the maxima is proved from the composition term
`a/100` and strict increase in `t` on `[0, 100/101]`, as in the paper proof.
-/

namespace Novel.M2CompleteSubstitutionProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry Standalone.M2CompleteSubstitution

/-! ### Basic values -/

lemma W0_ex : W0 exData = 1 := by simp [W0, exData]

lemma w0_ex : w0 exData = 0 := by
  funext i
  simp [w0, W0, exData]

lemma k0_ex : k0 exData = 1 := by simp [k0, W0, exData]

lemma hold_surj (w : Inst 1 1 → ℝ) : w = hold (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with j | j <;> fin_cases j <;> rfl

lemma hold_inj {a p a' p' : ℝ} : hold a p = hold a' p' ↔ a = a' ∧ p = p' := by
  constructor
  · intro h
    exact ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma hold_sub_w0 (a p : ℝ) : hold a p - w0 exData = hold a p := by
  rw [w0_ex, sub_zero]

lemma tau_hold_nonneg {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) :
    tau exData (hold a p - w0 exData) = (a + p) / 100 := by
  rw [hold_sub_w0]
  simp only [tau, Fintype.sum_sum_type, Fin.sum_univ_one, hold, Sum.elim_inl, Sum.elim_inr,
    exData]
  rw [max_eq_left ha, max_eq_left hp, max_eq_right (neg_nonpos.mpr ha),
    max_eq_right (neg_nonpos.mpr hp)]
  ring

lemma sum_hold (a p : ℝ) : ∑ i, (hold a p i - w0 exData i) = a + p := by
  simp [w0_ex, hold, Fintype.sum_sum_type]

lemma cash_hold {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) :
    cash exData (hold a p) = 1 - 101 / 100 * (a + p) := by
  rw [cash, sum_hold, tau_hold_nonneg ha hp, k0_ex]
  ring

lemma exposure_hold (a p : ℝ) : exposure exData (hold a p) = ![a + p, 0] := by
  funext k
  fin_cases k <;> simp [exposure, active, etf, hold, exData, mulVec, dotProduct]

lemma xi_ex (s : Fin 2) (i : Inst 1 1) : xi exData s i = exData.zf s 0 := by
  rcases i with j | j <;> fin_cases j <;> fin_cases s <;>
    simp [xi, exData]

lemma zf_sq (s : Fin 2) : exData.zf s 0 * exData.zf s 0 = 1 / 100 := by
  fin_cases s <;> simp [exData] <;> norm_num

lemma covariance_ex (i j : Inst 1 1) : covariance exData i j = 1 / 100 := by
  simp only [covariance, xi_ex, zf_sq, Fin.sum_univ_two]
  simp [exData]
  norm_num

lemma quad_hold (a p : ℝ) :
    hold a p ⬝ᵥ (covariance exData *ᵥ hold a p) = (a + p) ^ 2 / 100 := by
  simp [dotProduct, mulVec, covariance_ex, hold, Fintype.sum_sum_type]
  ring

lemma score_hold {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (θ : Params 1 2) :
    score exData (hold a p) θ
      = (a + p) * θ.lam 0 + a * θ.alpha 0 - (a + p) ^ 2 / 200 - (a + p) / 100 := by
  rw [score, quad_hold, tau_hold_nonneg ha hp, exposure_hold]
  simp [dotProduct, Fin.sum_univ_two, active, etf, hold, exData]
  ring

lemma Qbar_hold {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) :
    Qbar (hold a p) = (a + p) / 100 + a / 100 - (a + p) ^ 2 / 200 := by
  simp only [Qbar, beliefScore, Fin.sum_univ_two, score_hold ha hp]
  simp [exPi, exPar]
  ring

/-! ### Validity of the instance -/

lemma validInstance : ValidInstance := by
  refine ⟨W0_ex, ⟨by rw [W0_ex]; norm_num, fun i => by simp [exData], by simp [exData],
      fun i => by rw [w0_ex]; simp [exData]⟩,
    fun i => ⟨by simp [exData], by simp [exData]⟩,
    fun i => ⟨by norm_num [exData], by norm_num [exData]⟩,
    fun i => by simp [exData], by simp [exData], fun s => by simp [exData],
    by norm_num [MassesSumToOne, exData], ⟨?_, ?_, ?_⟩,
    fun t => by simp [exPi], by norm_num [exPi], ?_⟩
  · funext k
    fin_cases k <;> norm_num [exData, Fin.sum_univ_two]
  · funext k
    simp [exData]
  · funext k
    simp [exData]
  · intro t s i
    rcases i with j | j <;> fin_cases j <;> fin_cases t <;> fin_cases s <;>
      norm_num [ret, exData, exPar, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.vecHead, Matrix.vecTail]

/-! ### Classes and exposure -/

lemma mem_F (a p : ℝ) : hold a p ∈ F exData ↔ 0 ≤ a ∧ 0 ≤ p ∧ a + p ≤ tmax := by
  simp only [F, Set.mem_ofPred_eq, tmax]
  constructor
  · rintro ⟨hb, hc⟩
    have ha := (hb (Sum.inl 0)).1
    have hp := (hb (Sum.inr 0)).1
    simp only [hold, Sum.elim_inl, Sum.elim_inr] at ha hp
    rw [cash_hold ha hp] at hc
    refine ⟨ha, hp, by linarith⟩
  · rintro ⟨ha, hp, ht⟩
    refine ⟨fun i => ?_, by rw [cash_hold ha hp]; linarith⟩
    rcases i with j | j <;> simp [hold, exData] <;> constructor <;> linarith

lemma mem_E (a p : ℝ) : hold a p ∈ E exData ↔ a = 0 ∧ 0 ≤ p ∧ p ≤ tmax := by
  have hact : active (hold a p) = active (w0 exData) ↔ a = 0 := by
    rw [w0_ex]
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext j
      simp [active, hold, h]
  simp only [E, Set.mem_ofPred_eq, mem_F, hact]
  constructor
  · rintro ⟨⟨_, hp, ht⟩, rfl⟩
    exact ⟨rfl, hp, by linarith⟩
  · rintro ⟨rfl, hp, ht⟩
    exact ⟨⟨le_rfl, hp, by linarith⟩, rfl⟩

lemma N_ex : N exData = {hold 0 0} := by
  rw [N, w0_ex]
  congr 1
  funext i
  rcases i with j | j <;> rfl

lemma image_E (f : (Inst 1 1 → ℝ) → Fin 2 → ℝ) (hf : ∀ a p, f (hold a p) = ![a + p, 0]) :
    f '' E exData = (fun t : ℝ => ![t, 0]) '' Set.Icc 0 tmax := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hold_surj w] at hw ⊢
    obtain ⟨ha, hp, ht⟩ := (mem_E _ _).mp hw
    refine ⟨w (Sum.inr 0), ⟨hp, ht⟩, ?_⟩
    rw [hf, ha, zero_add]
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨hold 0 t, (mem_E 0 t).mpr ⟨rfl, h0, h1⟩, by rw [hf, zero_add]⟩

lemma classesAndExposure : ClassesAndExposure := by
  refine ⟨hold_surj, mem_F, mem_E, N_ex, exposure_hold, ?_, ?_⟩
  · exact image_E _ exposure_hold
  · refine image_E _ fun a p => ?_
    rw [exposure_hold, show w0 exData = hold 0 0 by rw [w0_ex]; funext i; rcases i with j | j <;> rfl,
      exposure_hold]
    funext k
    fin_cases k <;> simp

/-! ### Complete substitution -/

lemma BEt_ex (d : Fin 1 → ℝ) : exData.BEᵀ *ᵥ d = ![d 0, 0] := by
  funext k
  fin_cases k <;> simp [exData, mulVec, dotProduct]

lemma BAt_ex (d : Fin 1 → ℝ) : exData.BAᵀ *ᵥ d = ![d 0, 0] := by
  funext k
  fin_cases k <;> simp [exData, mulVec, dotProduct]

lemma completeSubstitution : CompleteSubstitution := by
  refine ⟨fun a p hF => ?_, ?_, ?_⟩
  · obtain ⟨ha, hp, ht⟩ := (mem_F a p).mp hF
    refine ⟨(mem_E 0 (a + p)).mpr ⟨rfl, by linarith, ht⟩, ?_, ?_, ?_, ?_⟩
    · rw [exposure_hold, exposure_hold, zero_add]
    · rw [quad_hold, quad_hold, zero_add]
    · rw [tau_hold_nonneg le_rfl (by linarith), tau_hold_nonneg ha hp, zero_add]
    · rw [cash_hold le_rfl (by linarith), cash_hold ha hp, zero_add]
  · rintro ⟨d, hd⟩
    change exData.BEᵀ *ᵥ d = _ at hd
    rw [BEt_ex] at hd
    have := congrFun hd 1
    simp at this
  · rintro ⟨d, hd⟩
    change exData.BAᵀ *ᵥ d = _ at hd
    rw [BAt_ex] at hd
    have := congrFun hd 1
    simp at this

/-! ### Score formulas -/

lemma scoreFormulas : ScoreFormulas := by
  intro a p ha hp
  have ht : 0 ≤ a + p := by linarith
  refine ⟨quad_hold a p, tau_hold_nonneg ha hp, cash_hold ha hp, Qbar_hold ha hp, ?_, ?_, ?_⟩
  · rw [Qbar_hold ha hp, Qbar_hold le_rfl ht]
    ring
  · rw [score_hold ha hp, score_hold le_rfl ht]
    simp [exPar]
  · rw [score_hold ha hp, score_hold le_rfl ht]
    simp [exPar]
    ring

/-! ### Optima and the gap -/

lemma optimaAndGap : OptimaAndGap := by
  have hc : (0 : ℝ) ≤ tmax := by norm_num [tmax]
  have hE : hold 0 tmax ∈ E exData := (mem_E 0 tmax).mpr ⟨rfl, hc, le_rfl⟩
  have hF : hold tmax 0 ∈ F exData := (mem_F tmax 0).mpr ⟨hc, le_rfl, by simp⟩
  refine ⟨⟨by rw [N_ex]; rfl, fun w hw hne => ?_⟩, ⟨hE, fun w hw hne => ?_⟩,
    ⟨hF, fun w hw hne => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [N_ex] at hw
    exact absurd hw hne
  · rw [hold_surj w] at hw hne ⊢
    obtain ⟨ha, hp, ht⟩ := (mem_E _ _).mp hw
    set p := w (Sum.inr 0)
    rw [ha] at hne ⊢
    have hlt : p < tmax := lt_of_le_of_ne ht fun h => hne (by rw [h])
    rw [Qbar_hold le_rfl hp, Qbar_hold le_rfl hc]
    simp only [tmax] at hlt ⊢
    nlinarith [mul_pos (sub_pos.mpr hlt) (by linarith : (0 : ℝ) < 1 / 100 - (100 / 101 + p) / 200)]
  · rw [hold_surj w] at hw hne ⊢
    obtain ⟨ha, hp, ht⟩ := (mem_F _ _).mp hw
    set a := w (Sum.inl 0)
    set p := w (Sum.inr 0)
    rw [Qbar_hold ha hp, Qbar_hold hc le_rfl]
    simp only [tmax] at ht ⊢
    have hkey : 0 ≤ (100 / 101 - (a + p)) * (1 / 50 - (100 / 101 + (a + p)) / 200) :=
      mul_nonneg (by linarith) (by linarith)
    rcases lt_or_eq_of_le hp with hp' | hp'
    · nlinarith
    · have hlt : a + p < 100 / 101 := by
        refine lt_of_le_of_ne ht fun h => hne ?_
        rw [hold_inj]
        refine ⟨?_, hp'.symm⟩
        simp only [tmax]
        linarith
      nlinarith [mul_pos (sub_pos.mpr hlt)
        (by linarith : (0 : ℝ) < 1 / 50 - (100 / 101 + (a + p)) / 200)]
  · rw [cash_hold le_rfl le_rfl]; norm_num
  · rw [cash_hold le_rfl hc]; norm_num [tmax]
  · rw [cash_hold hc le_rfl]; norm_num [tmax]
  · rw [tau_hold_nonneg le_rfl le_rfl]; norm_num
  · rw [tau_hold_nonneg le_rfl hc]; norm_num [tmax]
  · rw [tau_hold_nonneg hc le_rfl]; norm_num [tmax]
  · rw [Qbar_hold le_rfl le_rfl]; norm_num
  · rw [Qbar_hold le_rfl hc]; norm_num [tmax]
  · rw [Qbar_hold hc le_rfl]; norm_num [tmax]
  · rw [exposure_hold, exposure_hold, zero_add, add_zero]
  · rw [Qbar_hold hc le_rfl, Qbar_hold le_rfl hc]; norm_num [tmax]

theorem proof : Standalone.M2CompleteSubstitution.statement :=
  ⟨validInstance, classesAndExposure, completeSubstitution, scoreFormulas, optimaAndGap⟩

end Novel.M2CompleteSubstitutionProof

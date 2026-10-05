import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.M4CurvedEntryRate
import Novel.M4JointDirectionalRateProof

/-!
# Proof of claim 017: quadratic entry changes the history rate in economic advantage

This proof imports claim 016's proof module (`depends_on: [16]`; Q-04). From it come:
- the latent sine-grid law and its orthogonal (Householder) embedding;
- the finite testing inequality and the logarithm conversion;
- the generic quantile lemmas and the variance-based tail bound;
- the moment identities for laws in `K_J`.
* **Part 1:** with `Σ = diag(2s², s²)` and `γ = 1/s²` the score is `a x + p λ₂ - a² - p²/2`, so
  both coordinates are maximized separately (`a = x₊/2`, `p = λ₂`), with funding slack on `Θ₄`.
* **Lower bound:** claim 016's hard grid along `h = (1, 0, 1)/√2` gives the active signal
  `±√2 a s`. So `G_*(θ₊) = a² s²/2`, and claim 016's logarithm step with `σ = s` and
  `δ' = √(2δ)` gives `s²/(32π² δ)`.
* **Certificate:** `Ω = s² I`, so `C_N` is a Euclidean ball of radius `ρ_N`. Then `|x - x̂| ≤ √2 ρ_N`,
  `|λ₂ - p̂| ≤ ρ_N`, and the exact advantage formula gives `ℓ_N ≤ Adv` on `C_N`.
-/

namespace Novel.M4CurvedEntryRateProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4CurvedEntryRate
open Standalone.M4InformationObstruction (toPar Theta4 M4Admissible Record record hist mass X
  thetaHat zeta Omega IsMoorePenrose pinv errN TN tcrit Aset Cset etfSup Adv Gstar LN LexLE lexSel
  wHatF vHatE Rule)
open Standalone.M4BoundedLawRate (falseP powerP Meets)
open Standalone.M4JointDirectionalRate (InKJ AdmitsJ)
open Novel.M4JointDirectionalRateProof (dot3 coord_sq_le ge_of_sq_le dot_self_nonneg cs3 mean_dot
  second_dot sgv bw bw_nonneg bw_sum bw_mean inst_ext)
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

lemma act_ext (w : Inst 1 1 → ℝ) : w = act (w (Sum.inl 0)) (w (Sum.inr 0)) := inst_ext w

/-! ### The data -/

section Data

variable (s : ℝ) {S : Type} [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ)

lemma W0_d : W0 (data s q U) = 1 := by simp [W0, data]

lemma w0_d : w0 (data s q U) = 0 := by funext i; simp [w0, data]

lemma tau_d (v : Inst 1 1 → ℝ) : tau (data s q U) v = 0 := by simp [tau, data]

lemma cash_d (w : Inst 1 1 → ℝ) :
    cash (data s q U) w = 1 - (w (Sum.inl 0) + w (Sum.inr 0)) := by
  rw [cash, w0_d, tau_d]
  simp [k0, W0_d, Fintype.sum_sum_type]
  simp [data]

lemma F_d : F (data s q U)
    = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} := by
  ext w
  simp only [F, Set.mem_ofPred_eq, cash_d]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨(h _).1, (h _).1, by linarith⟩
  · rintro ⟨ha, hp, hs⟩
    refine ⟨fun i => ?_, by linarith⟩
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
      simp only [data] <;> constructor <;> linarith

lemma E_d : E (data s q U) = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} := by
  ext w
  simp only [E, F_d, w0_d, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨ha, hp, hs⟩, h⟩
    have h0 : w (Sum.inl 0) = 0 := by simpa [active] using congrFun h 0
    exact ⟨h0, hp, by linarith⟩
  · rintro ⟨ha, hp, hs⟩
    refine ⟨⟨by linarith, hp, by linarith⟩, ?_⟩
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [active, ha]

lemma ret_inl (θ : Fin 3 → ℝ) (x : S) : ret (data s q U) (toPar θ) x (Sum.inl 0)
    = θ 0 + s * U x 0 + θ 2 + s * U x 2 := by
  simp [ret, data, toPar, Matrix.vecHead, Matrix.vecTail]

lemma ret_inr (θ : Fin 3 → ℝ) (x : S) :
    ret (data s q U) (toPar θ) x (Sum.inr 0) = θ 1 + s * U x 1 := by
  simp [ret, data, toPar, Matrix.vecHead, Matrix.vecTail]

lemma record_d (θ : Fin 3 → ℝ) (x : S) : record (data s q U) θ x
    = ⟨![θ 0 + s * U x 0, θ 1 + s * U x 1], θ 0 + s * U x 0 + θ 2 + s * U x 2,
      fun _ => θ 1 + s * U x 1⟩ := by
  have h1 := ret_inl s q U θ x
  have h2 := ret_inr s q U θ x
  simp only [record, h1]
  congr 1
  · funext k; fin_cases k <;> simp [data, toPar]
  · funext j; obtain rfl : j = 0 := Subsingleton.elim _ _; exact h2

lemma X_d (θ : Fin 3 → ℝ) (x : S) :
    X (data s q U) (record (data s q U) θ x) = θ + s • U x := by
  rw [record_d]
  funext i
  fin_cases i <;> (simp [X, data, mulVec, dotProduct, Fin.sum_univ_two]; try ring)

lemma zeta_d (x : S) : zeta (data s q U) x = s • U x := by
  funext i; fin_cases i <;> simp [zeta, data]

end Data

/-! ### Second moments: `Ω = s² I` and `Σ = diag(2s², s²)` -/

section Moments

variable {s : ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ} (hK : InKJ q U)
include hK

lemma omega_d : Omega (data s q U) = s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  simp only [Omega, zeta_d, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  show ∑ x, q x * (s * U x i * (s * U x j)) = s ^ 2 * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  rw [← hK.2.2.2.1 i j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma xi_d (x : S) : xi (data s q U) x
    = act (s * (![1, 0, 1] ⬝ᵥ U x)) (s * (![0, 1, 0] ⬝ᵥ U x)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
    (simp [xi, data, act, dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]; try ring)

lemma cov_d : covariance (data s q U) = Matrix.diagonal (act (2 * s ^ 2) (s ^ 2)) := by
  have key : ∀ A B : Fin 3 → ℝ, ∑ x, (data s q U).q x * (s * (A ⬝ᵥ U x) * (s * (B ⬝ᵥ U x)))
      = s ^ 2 * (A ⬝ᵥ B) := fun A B => by
    rw [← second_dot hK A B, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by simp only [data]; ring
  ext i j
  simp only [covariance, xi_d hK]
  rcases i with i | i <;> rcases j with j | j <;> obtain rfl : i = 0 := Subsingleton.elim _ _ <;>
    obtain rfl : j = 0 := Subsingleton.elim _ _ <;>
    simp only [act, Sum.elim_inl, Sum.elim_inr, key, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, Matrix.diagonal_apply_ne _ Sum.inr_ne_inl] <;>
    (rw [dot3]; simp; try ring)

lemma score_d (hs : s ≠ 0) (w : Inst 1 1 → ℝ) (θ : Fin 3 → ℝ) :
    score (data s q U) w (toPar θ) = w (Sum.inl 0) * xs θ + w (Sum.inr 0) * θ 1
      - w (Sum.inl 0) ^ 2 - w (Sum.inr 0) ^ 2 / 2 := by
  rw [score, tau_d, cov_d hK]
  simp [exposure, active, etf, data, toPar, dotProduct, mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_two, diagonal, act, xs]
  field_simp
  ring

end Moments

/-! ### The domain is the box `c + s[-1, 1]³` -/

lemma box_mem {s : ℝ} {v : Fin 3 → ℝ} (hv : ∀ i, |v i| ≤ 1) :
    cC + s • v ∈ Theta4 (V4 s) := by
  have hmem : ∀ b : Fin 3 → Bool, cC + s • sgv b ∈ (V4 s : Set _) :=
    fun b => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  have hsum := (convex_convexHull ℝ (V4 s : Set (Fin 3 → ℝ))).sum_mem (t := Finset.univ)
    (w := bw v) (z := fun b => cC + s • sgv b)
    (fun b _ => bw_nonneg hv b) (bw_sum v) (fun b _ => subset_convexHull ℝ _ (hmem b))
  have hv' : ∑ b, bw v b • sgv b = v := by
    funext k; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; exact bw_mean v k
  have heq : cC + s • v = ∑ b, bw v b • (cC + s • sgv b) := by
    rw [Finset.sum_congr rfl fun b _ => smul_add (bw v b) _ _, Finset.sum_add_distrib,
      ← Finset.sum_smul, bw_sum, one_smul]
    congr 1
    conv_lhs => rw [← hv']
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _
  rw [heq]
  exact hsum

lemma theta4_eq {s : ℝ} (hs : 0 < s) : Theta4 (V4 s) = {θ | ∀ i, |θ i - cC i| ≤ s} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro θ hθ
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hθ)
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul,
        abs_of_pos hs]
      split_ifs <;> simp
    · intro x hx y hy a b ha hb hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : a * x i + b * y i - cC i = a * (x i - cC i) + b * (y i - cC i) := by
        linear_combination (cC i) * hab
      rw [e]
      calc |a * (x i - cC i) + b * (y i - cC i)| ≤ a * |x i - cC i| + b * |y i - cC i| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * s + b * s := by gcongr <;> [exact hx i; exact hy i]
        _ = s := by rw [← add_mul, hab, one_mul]
  · intro θ hθ
    have e : θ = cC + s • ((1 / s) • (θ - cC)) := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp
      ring
    rw [e]
    refine box_mem fun i => ?_
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos (one_div_pos.mpr hs)]
    rw [one_div, inv_mul_le_iff₀ hs, mul_one]
    exact hθ i

lemma mem_box {s : ℝ} (hs : 0 < s) {θ : Fin 3 → ℝ} (h : θ ∈ Theta4 (V4 s)) :
    1 / 4 - s ≤ θ 1 ∧ θ 1 ≤ 1 / 4 + s ∧ -(2 * s) ≤ xs θ ∧ xs θ ≤ 2 * s := by
  rw [theta4_eq hs] at h
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  have h2 := abs_le.mp (h 2)
  simp [cC] at h0 h1 h2
  refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> simp only [xs] <;> linarith

/-! ### Part 1: the quadratic optimization -/

lemma entry_le (x a : ℝ) (ha : 0 ≤ a) : a * x - a ^ 2 ≤ max x 0 ^ 2 / 4 ∧
    (a * x - a ^ 2 = max x 0 ^ 2 / 4 → a = max x 0 / 2) := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx]
    refine ⟨by nlinarith, fun h => ?_⟩
    have : a ^ 2 ≤ 0 := by nlinarith
    have : a = 0 := by nlinarith [sq_nonneg a]
    rw [this]; ring
  · rw [max_eq_left hx]
    refine ⟨by nlinarith [sq_nonneg (a - x / 2)], fun h => ?_⟩
    have : (a - x / 2) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith


section Opt

variable {s : ℝ} (hs : 0 < s) {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}
  (hK : InKJ q U)
include hs hK

lemma act_mem_E {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : act 0 p ∈ E (data s q U) := by
  rw [E_d]; simp [act, h0, h1]

lemma act_mem_F {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (h1 : a + p ≤ 1) :
    act a p ∈ F (data s q U) := by
  rw [F_d]; simp [act, ha, hp, h1]

lemma maxE_d {θ : Fin 3 → ℝ} (h0 : 0 ≤ θ 1) (h1 : θ 1 ≤ 1) :
    maximizers (fun v => score (data s q U) v (toPar θ)) (E (data s q U)) = {act 0 (θ 1)} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax _ (act_mem_E hs hK h0 h1)
    rw [E_d] at hw
    obtain ⟨ha, hp, hp1⟩ := hw
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, ha] at hm
    have : (w (Sum.inr 0) - θ 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w (Sum.inr 0) - θ 1)]
    have hp' : w (Sum.inr 0) = θ 1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this; linarith
    rw [act_ext w, ha, hp']
  · rintro rfl
    refine ⟨act_mem_E hs hK h0 h1, fun v hv => ?_⟩
    rw [E_d] at hv
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, hv.1]
    nlinarith [sq_nonneg (v (Sum.inr 0) - θ 1)]

lemma etfSup_d {θ : Fin 3 → ℝ} (h0 : 0 ≤ θ 1) (h1 : θ 1 ≤ 1) :
    etfSup (data s q U) θ = θ 1 ^ 2 / 2 := by
  have h : act 0 (θ 1) ∈ maximizers (fun v => score (data s q U) v (toPar θ)) (E (data s q U)) := by
    rw [maxE_d hs hK h0 h1]; rfl
  have hg : IsGreatest ((fun v => score (data s q U) v (toPar θ)) '' E (data s q U))
      (score (data s q U) (act 0 (θ 1)) (toPar θ)) :=
    ⟨⟨_, h.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h.2 v hv⟩
  rw [etfSup, hg.csSup_eq, score_d hK hs.ne']
  simp [act]; ring

lemma Adv_d {θ : Fin 3 → ℝ} (h0 : 0 ≤ θ 1) (h1 : θ 1 ≤ 1) (a p : ℝ) :
    Adv (data s q U) (act a p) θ = a * xs θ - a ^ 2 - (p - θ 1) ^ 2 / 2 := by
  rw [Adv, etfSup_d hs hK h0 h1, score_d hK hs.ne']
  simp [act]; ring

lemma maxF_d {θ : Fin 3 → ℝ} (h0 : 0 ≤ θ 1) (h1 : max (xs θ) 0 / 2 + θ 1 ≤ 1) :
    maximizers (fun w => score (data s q U) w (toPar θ)) (F (data s q U))
      = {act (max (xs θ) 0 / 2) (θ 1)} := by
  have hx0 : 0 ≤ max (xs θ) 0 / 2 := by positivity
  have hmemF := act_mem_F hs hK hx0 h0 h1
  have hval : score (data s q U) (act (max (xs θ) 0 / 2) (θ 1)) (toPar θ)
      = max (xs θ) 0 ^ 2 / 4 + θ 1 ^ 2 / 2 := by
    rw [score_d hK hs.ne']; simp only [act, Sum.elim_inl, Sum.elim_inr]
    rcases le_total (xs θ) 0 with hx | hx
    · rw [max_eq_right hx]; ring
    · rw [max_eq_left hx]; ring
  have hle : ∀ w ∈ F (data s q U), score (data s q U) w (toPar θ)
      = (w (Sum.inl 0) * xs θ - w (Sum.inl 0) ^ 2) + θ 1 ^ 2 / 2 - (w (Sum.inr 0) - θ 1) ^ 2 / 2 :=
    fun w _ => by rw [score_d hK hs.ne']; ring
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax _ hmemF
    rw [hval, hle w hw] at hm
    have ha := (by rw [F_d] at hw; exact hw.1 : 0 ≤ w (Sum.inl 0))
    obtain ⟨e1, e2⟩ := entry_le (xs θ) (w (Sum.inl 0)) ha
    have hsq : (w (Sum.inr 0) - θ 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w (Sum.inr 0) - θ 1)]
    have hp : w (Sum.inr 0) = θ 1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq; linarith
    have ha' : w (Sum.inl 0) = max (xs θ) 0 / 2 := e2 (by nlinarith [sq_nonneg (w (Sum.inr 0) - θ 1)])
    rw [act_ext w, ha', hp]
  · rintro rfl
    refine ⟨hmemF, fun v hv => ?_⟩
    show score (data s q U) v (toPar θ) ≤ score (data s q U) _ (toPar θ)
    rw [hval, hle v hv]
    have ha := (by rw [F_d] at hv; exact hv.1 : 0 ≤ v (Sum.inl 0))
    have := (entry_le (xs θ) (v (Sum.inl 0)) ha).1
    nlinarith [sq_nonneg (v (Sum.inr 0) - θ 1)]

lemma Gstar_d {θ : Fin 3 → ℝ} (h0 : 0 ≤ θ 1) (h1 : max (xs θ) 0 / 2 + θ 1 ≤ 1) :
    Gstar (data s q U) θ = max (xs θ) 0 ^ 2 / 4 := by
  have hm : act (max (xs θ) 0 / 2) (θ 1) ∈
      maximizers (fun w => score (data s q U) w (toPar θ)) (F (data s q U)) := by
    rw [maxF_d hs hK h0 h1]; rfl
  have hg : IsGreatest ((fun w => score (data s q U) w (toPar θ)) '' F (data s q U))
      (score (data s q U) (act (max (xs θ) 0 / 2) (θ 1)) (toPar θ)) :=
    ⟨⟨_, hm.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hm.2 v hv⟩
  have hx0 : (0 : ℝ) ≤ max (xs θ) 0 / 2 := by positivity
  rw [Gstar, hg.csSup_eq, etfSup_d hs hK h0 (by linarith), score_d hK hs.ne']
  simp only [act, Sum.elim_inl, Sum.elim_inr]
  rcases le_total (xs θ) 0 with hx | hx
  · rw [max_eq_right hx]; ring
  · rw [max_eq_left hx]; ring

end Opt

/-- Pure algebra of the entry scale. -/
lemma entry_iff (x δ : ℝ) (hδ : 0 < δ) :
    (δ ≤ max x 0 ^ 2 / 4 ↔ 2 * Real.sqrt δ ≤ x) ∧
      (max x 0 ^ 2 / 4 = δ → max x 0 / 2 = Real.sqrt δ) := by
  have hsd := Real.sqrt_pos.mpr hδ
  have hsq := Real.sq_sqrt hδ.le
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx] at h; linarith
    · rw [max_eq_left hx] at h
      nlinarith [sq_nonneg (x - 2 * Real.sqrt δ)]
  · have hx : 0 ≤ x := by linarith
    rw [max_eq_left hx]
    nlinarith
  · have h0 : 0 ≤ max x 0 / 2 := by positivity
    rw [← Real.sqrt_sq h0, ← h]; congr 1; ring

lemma U_coord {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ} (hK : InKJ q U) (x : S)
    (i : Fin 3) : -9 ≤ U x i ∧ U x i ≤ 9 := by
  have h := (coord_sq_le (U x) i).trans (hK.2.2.2.2 x)
  constructor
  · exact ge_of_sq_le (by norm_num) (by linarith)
  · have := ge_of_sq_le (x := -U x i) (by norm_num : (0 : ℝ) ≤ 9) (by rw [neg_sq]; linarith)
    linarith

lemma admissible {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 100) {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} (hK : InKJ q U) : M4Admissible (data s q U) (V4 s) := by
  obtain ⟨hq, hq1, h0, h2, hU⟩ := hK
  have hc : ∀ i, ∑ x, q x * (s * U x i) = 0 := fun i => by
    rw [show ∑ x, q x * (s * U x i) = s * ∑ x, q x * U x i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring, h0 i, mul_zero]
  refine ⟨Or.inl rfl, Finset.univ_nonempty.image _, hq, hq1, fun k => ?_, fun j => ?_,
    fun j => by simp [data], by simp [data]; positivity, fun i => by simp [data],
    by simp [data], by rw [W0_d]; norm_num, ?_, fun i => by simp [data], ?_⟩
  · fin_cases k
    · simpa [data] using hc 0
    · simpa [data] using hc 1
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [data] using hc 2
  · rw [w0_d, F_d]; simp
  · intro θ hθ x i
    simp only [V4, Finset.mem_image, Finset.mem_univ, true_and] at hθ
    obtain ⟨b, rfl⟩ := hθ
    have hu := U_coord ⟨hq, hq1, h0, h2, hU⟩ x
    have hsb : ∀ k, -1 ≤ (fun i => if b i then (1 : ℝ) else -1) k := fun k => by
      simp only; split_ifs <;> norm_num
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
    · rw [ret_inl]
      have := hsb 0; have := hsb 2; have := hu 0; have := hu 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cC, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      nlinarith
    · rw [ret_inr]
      have hb1 : -1 ≤ (if b 1 = true then (1 : ℝ) else -1) := by split_ifs <;> norm_num
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cC, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      nlinarith [mul_le_mul_of_nonneg_left hb1 hs.le, mul_le_mul_of_nonneg_left (hu 1).1 hs.le]

theorem geometry : Geometry := by
  intro s hs hs1 S _ q U hK
  refine ⟨admissible hs hs1 hK, theta4_eq hs, omega_d hK, cov_d hK, F_d s q U, E_d s q U,
    fun θ w => score_d hK hs.ne' w θ, fun θ hθ => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := mem_box hs hθ
  have h0 : 0 ≤ θ 1 := by linarith
  have h1 : θ 1 ≤ 1 := by linarith
  have hmx : max (xs θ) 0 / 2 ≤ s := by
    rcases le_total (xs θ) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hsl : max (xs θ) 0 / 2 + θ 1 < 1 := by linarith
  refine ⟨maxE_d hs hK h0 h1, maxF_d hs hK h0 hsl.le, etfSup_d hs hK h0 h1,
    Gstar_d hs hK h0 hsl.le, by linarith, hsl, Adv_d hs hK h0 h1, fun hx w hw ha => ?_,
    fun δ hδ => ?_⟩
  · rw [act_ext w, Adv_d hs hK h0 h1]
    nlinarith [sq_nonneg (w (Sum.inr 0) - θ 1), mul_neg_of_pos_of_neg ha hx]
  · rw [Gstar_d hs hK h0 hsl.le]
    exact entry_iff (xs θ) δ hδ

/-! ### Part 3: histories, plug-in optimizers and the Euclidean calibration -/

section Hist

variable {s : ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

/-- The sample mean of the latent shocks. -/
def Ubar {N : ℕ} (U : S → Fin 3 → ℝ) (σ : Fin N → S) : Fin 3 → ℝ :=
  (1 / (N : ℝ)) • ∑ l, U (σ l)

lemma errN_d {N : ℕ} (σ : Fin N → S) : errN (data s q U) σ = s • Ubar U σ := by
  funext i
  simp only [errN, zeta_d, Ubar, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma thetaHat_hist {N : ℕ} (hN : 0 < N) (θ : Fin 3 → ℝ) (σ : Fin N → S) :
    thetaHat (data s q U) (hist (data s q U) θ σ) = θ + errN (data s q U) σ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [errN_d]
  funext i
  simp only [thetaHat, hist, X_d, Ubar, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  rw [Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum]
  congr 1
  · field_simp
  · exact Finset.sum_congr rfl fun x _ => by field_simp

lemma avg_abs {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) {B : ℝ} (hf : ∀ l, |f l| ≤ B) :
    |(1 / (N : ℝ)) * ∑ l, f l| ≤ B := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hNr]
  calc |∑ l, f l| ≤ ∑ l, |f l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin N, B := Finset.sum_le_sum fun l _ => hf l
    _ = N * B := by simp

lemma Ubar_bounds (hK : InKJ q U) {N : ℕ} (hN : 0 < N) (σ : Fin N → S) :
    |Ubar U σ 1| ≤ 9 ∧ |Ubar U σ 0 + Ubar U σ 2| ≤ 13 := by
  constructor
  · simp only [Ubar, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact avg_abs hN _ fun l => abs_le.mpr (U_coord hK _ 1)
  · have e : Ubar U σ 0 + Ubar U σ 2 = (1 / (N : ℝ)) * ∑ l, (U (σ l) 0 + U (σ l) 2) := by
      simp only [Ubar, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.sum_add_distrib]; ring
    rw [e]
    refine avg_abs hN _ fun l => ?_
    have h := hK.2.2.2.2 (σ l)
    rw [dot3] at h
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (U (σ l) 0 - U (σ l) 2), sq_nonneg (U (σ l) 1)]

/-- On every history from the domain the plug-in estimate stays in the funded region. -/
lemma plug_bounds (hs : 0 < s) (hs1 : s ≤ 1 / 100) (hK : InKJ q U) {N : ℕ} (hN : 0 < N)
    {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 (V4 s)) (σ : Fin N → S) :
    let th := thetaHat (data s q U) (hist (data s q U) θ σ)
    3 / 20 ≤ th 1 ∧ th 1 ≤ 7 / 20 ∧ max (xs th) 0 / 2 ≤ 2 / 25 := by
  intro th
  obtain ⟨b1, b2, b3, b4⟩ := mem_box hs hθ
  obtain ⟨u1, u2⟩ := Ubar_bounds hK hN σ
  have hth : th = θ + s • Ubar U σ := by simp only [th]; rw [thetaHat_hist hN, errN_d]
  have e1 : th 1 = θ 1 + s * Ubar U σ 1 := by rw [hth]; rfl
  have e2 : xs th = xs θ + s * (Ubar U σ 0 + Ubar U σ 2) := by
    rw [hth]; simp only [xs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have a1 := abs_le.mp u1
  have a2 := abs_le.mp u2
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; nlinarith [mul_le_mul_of_nonneg_left a1.1 hs.le]
  · rw [e1]; nlinarith [mul_le_mul_of_nonneg_left a1.2 hs.le]
  · have hx : xs th ≤ 15 * s := by rw [e2]; nlinarith [mul_le_mul_of_nonneg_left a2.2 hs.le]
    rcases le_total (xs th) 0 with h | h
    · rw [max_eq_right h]; norm_num
    · rw [max_eq_left h]; linarith

lemma plugin (hs : 0 < s) (hs1 : s ≤ 1 / 100) (hK : InKJ q U) {N : ℕ} (hN : 0 < N)
    {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 (V4 s)) (σ : Fin N → S) :
    let th := thetaHat (data s q U) (hist (data s q U) θ σ)
    wHatF (data s q U) th = act (ahat (data s q U) (hist (data s q U) θ σ)) (th 1) ∧
    vHatE (data s q U) th = act 0 (th 1) ∧
    act (ahat (data s q U) (hist (data s q U) θ σ)) (th 1) ∈ F (data s q U) ∧
    act 0 (th 1) ∈ E (data s q U) := by
  intro th
  obtain ⟨p1, p2, p3⟩ := plug_bounds hs hs1 hK hN hθ σ
  have h0 : 0 ≤ th 1 := by linarith
  have hF : max (xs th) 0 / 2 + th 1 ≤ 1 := by linarith
  have hx0 : 0 ≤ max (xs th) 0 / 2 := by have := le_max_right (xs th) 0; linarith
  refine ⟨?_, ?_, act_mem_F hs hK hx0 h0 hF, act_mem_E hs hK h0 (by linarith)⟩
  · rw [wHatF, maxF_d hs hK h0 hF, Novel.M4BoundedLawRateProof.lexSel_singleton]; rfl
  · rw [vHatE, maxE_d hs hK h0 (by linarith), Novel.M4BoundedLawRateProof.lexSel_singleton]

end Hist

section Calib

variable {s : ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

lemma pinv_d (hs : s ≠ 0) (hK : InKJ q U) :
    pinv (Omega (data s q U)) = (1 / s ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hex : IsMoorePenrose (s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      ((1 / s ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.mul_smul, Matrix.mul_one,
      smul_smul, Matrix.transpose_smul, Matrix.transpose_one] <;> congr 1 <;> field_simp
  have h1 := (Classical.epsilon_spec (p := IsMoorePenrose (s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ)))
    ⟨_, hex⟩).1
  rw [omega_d hK]
  set G := pinv (s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ))
  have : (s ^ 2 * s ^ 2) • G = s ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    have := h1
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at this
    exact this
  calc G = (1 / (s ^ 2 * s ^ 2)) • ((s ^ 2 * s ^ 2) • G) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ (mul_ne_zero hs2 hs2), one_smul]
    _ = (1 / s ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [this, smul_smul]; congr 1; field_simp

lemma quad_d (hs : s ≠ 0) (hK : InKJ q U) (e : Fin 3 → ℝ) :
    e ⬝ᵥ (pinv (Omega (data s q U)) *ᵥ e) = (e ⬝ᵥ e) / s ^ 2 := by
  rw [pinv_d hs hK, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]; ring

lemma range_d (hs : s ≠ 0) (hK : InKJ q U) (e : Fin 3 → ℝ) :
    e ∈ Set.range (Omega (data s q U)).mulVec := by
  refine ⟨(1 / s ^ 2) • e, ?_⟩
  rw [omega_d hK, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  have : s ^ 2 * (1 / s ^ 2) = 1 := by field_simp
  rw [this, one_smul]

/-- Every error in `A_{N,ε}` lies in the Euclidean ball of radius `ρ_N`. -/
lemma A_ball (hs : 0 < s) (hK : InKJ q U) {N : ℕ} (hN : 0 < N) {ε : ℝ} {e : Fin 3 → ℝ}
    (he : e ∈ Aset (data s q U) N ε) : e ⬝ᵥ e ≤ rho s (data s q U) N ε ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := he.2
  rw [quad_d hs.ne' hK] at hq
  have h0 := dot_self_nonneg e
  have ht : 0 ≤ tcrit (data s q U) N ε / N := by
    rw [le_div_iff₀ hNr]; nlinarith [div_nonneg h0 (sq_nonneg s)]
  rw [rho, mul_pow, Real.sq_sqrt ht]
  rw [le_div_iff₀ hNr] at ht
  have : e ⬝ᵥ e / s ^ 2 ≤ tcrit (data s q U) N ε / N := by
    rw [le_div_iff₀ hNr]; linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

lemma sqrt2_facts : Real.sqrt 2 ^ 2 = 2 ∧ 0 < Real.sqrt 2 ∧ Real.sqrt 2 ≤ 3 / 2 := by
  refine ⟨Real.sq_sqrt (by norm_num), Real.sqrt_pos.mpr (by norm_num), ?_⟩
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- On `C_N`, the signal and the premium are within `√2 ρ_N` and `ρ_N` of their estimates. -/
lemma C_close (hs : 0 < s) (hK : InKJ q U) {N : ℕ} (hN : 0 < N) {ε : ℝ} {th θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset (data s q U) (V4 s) N ε th) :
    |xs th - xs θ| ≤ Real.sqrt 2 * rho s (data s q U) N ε ∧
      (th 1 - θ 1) ^ 2 ≤ rho s (data s q U) N ε ^ 2 := by
  obtain ⟨-, e, he, rfl⟩ := hθ
  have hb := A_ball hs hK hN he
  rw [dot3] at hb
  set r := rho s (data s q U) N ε
  have hr : 0 ≤ r := mul_nonneg hs.le (Real.sqrt_nonneg _)
  obtain ⟨h2, h2p, -⟩ := sqrt2_facts
  refine ⟨?_, ?_⟩
  · simp only [xs, Pi.sub_apply]
    have hd : (e 0 + e 2) ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, h2]; nlinarith [sq_nonneg (e 0 - e 2), sq_nonneg (e 1)]
    have hsq := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at hsq
    rw [show th 0 + th 2 - (th 0 - e 0 + (th 2 - e 2)) = e 0 + e 2 by ring]
    exact hsq
  · simp only [Pi.sub_apply, sub_sub_cancel]
    nlinarith [sq_nonneg (e 0), sq_nonneg (e 2)]

end Calib

/-! ### Part 3: the certificate -/

section Cert

variable {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 100) {S : Type} [Fintype S] {q : S → ℝ}
  {U : S → Fin 3 → ℝ} (hK : InKJ q U)
include hs hs1 hK

lemma ahat_nonneg {N : ℕ} (H : Fin N → Record 1) : 0 ≤ ahat (data s q U) H := by
  have := le_max_right (xs (thetaHat (data s q U) H)) 0; unfold ahat; linarith

lemma ell_le_Adv {N : ℕ} (hN : 0 < N) {ε : ℝ} {H : Fin N → Record 1} {θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset (data s q U) (V4 s) N ε (thetaHat (data s q U) H)) :
    ellC s (data s q U) ε H
      ≤ Adv (data s q U) (act (ahat (data s q U) H) (thetaHat (data s q U) H 1)) θ := by
  obtain ⟨b1, b2, -, -⟩ := mem_box hs hθ.1
  obtain ⟨c1, c2⟩ := C_close hs hK hN hθ
  have ha := ahat_nonneg hs hs1 hK H
  rw [Adv_d hs hK (by linarith) (by linarith), ellC]
  have h1 := mul_le_mul_of_nonneg_left (show xs (thetaHat (data s q U) H)
    - Real.sqrt 2 * rho s (data s q U) N ε ≤ xs θ by linarith [(abs_le.mp c1).2]) ha
  nlinarith

lemma ell_ge {N : ℕ} (hN : 0 < N) {ε δ : ℝ} (hδ : 0 < δ) {θ : Fin 3 → ℝ}
    (hθ4 : θ ∈ Theta4 (V4 s)) (hG : δ ≤ Gstar (data s q U) θ)
    (hρ : rho s (data s q U) N ε ≤ Real.sqrt δ / 8) {H : Fin N → Record 1}
    (hθ : θ ∈ Cset (data s q U) (V4 s) N ε (thetaHat (data s q U) H)) :
    5 * δ / 8 ≤ ellC s (data s q U) ε H := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_box hs hθ4
  have hmx : max (xs θ) 0 / 2 + θ 1 ≤ 1 := by
    rcases le_total (xs θ) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rw [Gstar_d hs hK (by linarith) hmx] at hG
  have hx := (entry_iff (xs θ) δ hδ).1.mp hG
  obtain ⟨c1, -⟩ := C_close hs hK hN hθ
  obtain ⟨r2sq, r2pos, r2le⟩ := sqrt2_facts
  set r := rho s (data s q U) N ε with hr
  have hr0 : 0 ≤ r := mul_nonneg hs.le (Real.sqrt_nonneg _)
  set d := Real.sqrt δ with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr hδ
  have hdd : d ^ 2 = δ := Real.sq_sqrt hδ.le
  set xh := xs (thetaHat (data s q U) H) with hxh
  have hxh1 : 2 * d - Real.sqrt 2 * r ≤ xh := by linarith [(abs_le.mp c1).1]
  have hxpos : 0 < xh := by nlinarith
  have hA : ahat (data s q U) H = xh / 2 := by rw [ahat, ← hxh, max_eq_left hxpos.le]
  rw [ellC, hA, ← hxh, ← hr]
  set A := xh / 2
  set B := d - Real.sqrt 2 * r / 2
  have hAB : B ≤ A := by simp only [A, B]; linarith
  have hB : Real.sqrt 2 * r / 2 ≤ B := by simp only [B]; nlinarith
  have hfAB : (A - B) * (A + B - Real.sqrt 2 * r) ≥ 0 :=
    mul_nonneg (by linarith) (by linarith)
  have hfB : B ^ 2 - Real.sqrt 2 * r * B - r ^ 2 / 2 = δ - 2 * Real.sqrt 2 * r * d + r ^ 2 := by
    simp only [B]; nlinarith [r2sq, hdd]
  have hxA : xh = 2 * A := by simp only [A]; ring
  rw [hxA]
  have h3 : 2 * Real.sqrt 2 * r * d ≤ 3 * r * d := by nlinarith [mul_nonneg hr0 hd0.le]
  have h4 : 3 * r * d ≤ 3 * δ / 8 := by nlinarith
  nlinarith

end Cert

theorem curvedCertificate : CurvedCertificate := by
  intro s hs hs1 S _ q U hK N ε hN
  refine ⟨fun θ hθ σ => plugin hs hs1 hK hN hθ σ, fun H hne => ?_,
    fun δ hδ θ hθ hG hρ σ hC => ell_ge hs hs1 hK hN hδ hθ hG hρ hC⟩
  rw [LN]
  simp only [hne.ne_empty, ↓reduceIte]
  exact le_iInf₂ fun θ hθ => EReal.coe_le_coe_iff.mpr (ell_le_Adv hs hs1 hK hN hθ)

/-! ### Part 2: the upper bound -/

section Upper

variable {s : ℝ} (hs : 0 < s) {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}
  (hK : InKJ q U)
include hs hK

lemma maxE_low {th : Fin 3 → ℝ} (h : th 1 ≤ 0) :
    maximizers (fun v => score (data s q U) v (toPar th)) (E (data s q U)) = {act 0 0} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax _ (act_mem_E hs hK le_rfl zero_le_one)
    rw [E_d] at hw
    obtain ⟨ha, hp, hp1⟩ := hw
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, ha] at hm
    have : w (Sum.inr 0) = 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hp h]
    rw [act_ext w, ha, this]
  · rintro rfl
    refine ⟨act_mem_E hs hK le_rfl zero_le_one, fun v hv => ?_⟩
    rw [E_d] at hv
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, hv.1]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hv.2.1 h]

lemma maxE_high {th : Fin 3 → ℝ} (h : 1 ≤ th 1) :
    maximizers (fun v => score (data s q U) v (toPar th)) (E (data s q U)) = {act 0 1} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax _ (act_mem_E hs hK zero_le_one le_rfl)
    rw [E_d] at hw
    obtain ⟨ha, hp, hp1⟩ := hw
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, ha] at hm
    have : w (Sum.inr 0) = 1 := by
      by_contra hne
      have hlt : w (Sum.inr 0) < 1 := lt_of_le_of_ne hp1 hne
      nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt)]
    rw [act_ext w, ha, this]
  · rintro rfl
    refine ⟨act_mem_E hs hK zero_le_one le_rfl, fun v hv => ?_⟩
    rw [E_d] at hv
    simp only [score_d hK hs.ne', act, Sum.elim_inl, Sum.elim_inr, hv.1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2.2) (sub_nonneg.mpr hv.2.2),
      mul_nonneg (sub_nonneg.mpr hv.2.2) (sub_nonneg.mpr h)]

/-- M4's plug-in fallback is always ETF-only. -/
lemma vHatE_mem_any (th : Fin 3 → ℝ) : vHatE (data s q U) th ∈ E (data s q U) := by
  rcases le_total (th 1) 0 with h | h
  · rw [vHatE, maxE_low hs hK h, Novel.M4BoundedLawRateProof.lexSel_singleton]
    exact act_mem_E hs hK le_rfl zero_le_one
  · rcases le_total (th 1) 1 with h' | h'
    · rw [vHatE, maxE_d hs hK h h', Novel.M4BoundedLawRateProof.lexSel_singleton]
      exact act_mem_E hs hK h h'
    · rw [vHatE, maxE_high hs hK h', Novel.M4BoundedLawRateProof.lexSel_singleton]
      exact act_mem_E hs hK zero_le_one le_rfl

/-- `t_{N,ε} ≤ 12 log(6/ε)` once `N ≥ 81 log(6/ε)`. -/
lemma tcrit_12 {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hNb : 81 * Real.log (6 / ε) ≤ N) : tcrit (data s q U) N ε ≤ 12 * Real.log (6 / ε) := by
  obtain ⟨hq, hq1, hU0, hU2, hU⟩ := id hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Real.log (6 / ε) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  set a := 2 * Real.sqrt (L / N) with hadef
  have ha : 0 < a := by positivity
  have ha2 : a ^ 2 = 4 * L / N := by
    rw [hadef, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have ha29 : a ≤ 2 / 9 := by
    have : a ^ 2 ≤ (2 / 9) ^ 2 := by
      rw [ha2, div_le_iff₀ hNr]; nlinarith
    exact (pow_le_pow_iff_left₀ ha.le (by norm_num) two_ne_zero).mp this
  set D := data s q U
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun _ _ => hq _
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := Novel.M4BoundedLawRateProof.mass_sum D hq1 N
  have hUb : ∀ (σ : Fin N → S) c, Ubar U σ c = (1 / (N : ℝ)) * ∑ l, U (σ l) c := fun σ c => by
    simp [Ubar, Finset.sum_apply]
  have htail : ∀ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ubar U σ c| then mass D σ else 0) ≤ ε / 3 := by
    intro c
    have h := Novel.M4JointDirectionalRateProof.tailV (Y := fun x => U x c) hq hq1 (hU0 c)
      (by simpa [sq] using hU2 c c) (fun x => (coord_sq_le (U x) c).trans (hU x)) hN ha ha29
    have e : 2 * Real.exp (-(N * a ^ 2) / 4) = ε / 3 := by
      rw [ha2]
      have : -((N : ℝ) * (4 * L / N)) / 4 = -L := by field_simp
      rw [this, Real.exp_neg, hLdef, Real.exp_log (by positivity)]
      field_simp
      norm_num
    simp only [hUb]
    rw [← e]
    exact h
  have hP : 1 - ε ≤ ∑ σ : Fin N → S, (if ∀ c, |Ubar U σ c| < a then mass D σ else 0) := by
    have hle : ∀ σ : Fin N → S, mass D σ - (if ∀ c, |Ubar U σ c| < a then mass D σ else 0)
        ≤ ∑ c : Fin 3, (if a ≤ |Ubar U σ c| then mass D σ else 0) := by
      intro σ
      split_ifs with h
      · rw [sub_self]
        exact Finset.sum_nonneg fun c _ => by split_ifs <;> linarith [hmass σ]
      · rw [sub_zero]
        obtain ⟨c, hc⟩ := not_forall.mp h
        have hc' : a ≤ |Ubar U σ c| := not_lt.mp hc
        calc mass D σ = (if a ≤ |Ubar U σ c| then mass D σ else 0) := by simp [hc']
          _ ≤ _ := Finset.single_le_sum (f := fun c => if a ≤ |Ubar U σ c| then mass D σ else 0)
              (fun c _ => by split_ifs <;> linarith [hmass σ]) (Finset.mem_univ c)
    have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hle σ
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_comm] at this
    have h3 : ∑ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ubar U σ c| then mass D σ else 0) ≤ ε := by
      calc _ ≤ ∑ _c : Fin 3, ε / 3 := Finset.sum_le_sum fun c _ => htail c
        _ = ε := by simp; ring
    linarith
  refine Novel.M4JointDirectionalRateProof.tq_le D hq hq1 N hε1 _ _ hP fun σ hσ => ?_
  have hTN : TN D σ = N * (Ubar U σ ⬝ᵥ Ubar U σ) := by
    rw [TN, quad_d hs.ne' hK, errN_d, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [hTN]
  have hU3 : Ubar U σ ⬝ᵥ Ubar U σ ≤ 3 * a ^ 2 := by
    rw [dot3]
    have := fun c => (sq_lt_sq' (abs_lt.mp (hσ c)).1 (abs_lt.mp (hσ c)).2).le
    nlinarith [this 0, this 1, this 2]
  calc (N : ℝ) * (Ubar U σ ⬝ᵥ Ubar U σ) ≤ N * (3 * a ^ 2) :=
        mul_le_mul_of_nonneg_left hU3 hNr.le
    _ = 12 * L := by rw [ha2]; field_simp; ring

lemma rho_small {δ ε : ℝ} (hδ : 0 < δ) (hδs : δ ≤ s ^ 2 / 128) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    {N : ℕ} (hNb : 768 * (s ^ 2 / δ) * Real.log (6 / ε) ≤ N) :
    0 < N ∧ rho s (data s q U) N ε ≤ Real.sqrt δ / 8 := by
  have hL : 0 < Real.log (6 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have h128 : 128 ≤ s ^ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hN81 : 81 * Real.log (6 / ε) ≤ N := le_trans (by nlinarith) hNb
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN81
  have hN : 0 < N := by exact_mod_cast hNr
  refine ⟨hN, ?_⟩
  have ht := tcrit_12 hs hK hN hε (by linarith) hN81
  have h1 : Real.sqrt (tcrit (data s q U) N ε / N) ≤ Real.sqrt (12 * Real.log (6 / ε) / N) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht hNr.le)
  have h2 : s * Real.sqrt (12 * Real.log (6 / ε) / N) ≤ Real.sqrt δ / 8 := by
    rw [show s * Real.sqrt (12 * Real.log (6 / ε) / N)
        = Real.sqrt (s ^ 2 * (12 * Real.log (6 / ε) / N)) by
      rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le],
      show Real.sqrt δ / 8 = Real.sqrt (δ / 64) by
      rw [Real.sqrt_div hδ.le, show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc', div_le_div_iff₀ hNr (by norm_num)]
    have e : 768 * (s ^ 2 / δ) * Real.log (6 / ε) * δ = 768 * s ^ 2 * Real.log (6 / ε) := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hNb hδ.le]
  calc rho s (data s q U) N ε = s * Real.sqrt (tcrit (data s q U) N ε / N) := rfl
    _ ≤ s * Real.sqrt (12 * Real.log (6 / ε) / N) := mul_le_mul_of_nonneg_left h1 hs.le
    _ ≤ Real.sqrt δ / 8 := h2

end Upper

theorem upperBound : UpperBound := by
  intro s δ ε hs hs1 hδ hδs hε hε1 S _ q U hK N hNb
  obtain ⟨hN, hρ⟩ := rho_small hs hK hδ hδs hε hε1 hNb
  set D := data s q U with hD
  have hq := hK.1
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun _ _ => hq _
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := Novel.M4BoundedLawRateProof.mass_sum D hK.2.1 N
  have hcov : 1 - ε ≤ ∑ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then mass D σ else 0) := by
    refine le_trans (Novel.M4JointDirectionalRateProof.tq_mem D hq hK.2.1 N hε.le)
      (Finset.sum_le_sum fun σ _ => ?_)
    by_cases h : TN D σ ≤ tcrit D N ε
    · have hA : errN D σ ∈ Aset D N ε := ⟨range_d hs.ne' hK _, h⟩
      simp only [h, hA, ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith [hmass σ]
  have hCmem : ∀ θ, ∀ σ : Fin N → S, errN D σ ∈ Aset D N ε → θ ∈ Theta4 (V4 s) →
      θ ∈ Cset D (V4 s) N ε (thetaHat D (hist D θ σ)) := fun θ σ he hθ =>
    ⟨hθ, errN D σ, he, by rw [thetaHat_hist hN, add_sub_cancel_right]⟩
  refine ⟨fun H => ?_, fun θ hθ => ?_, fun θ hθ hG => ?_⟩
  · show Measure.dirac (if certC s D δ ε H then wHatF D (thetaHat D H)
      else vHatE D (thetaHat D H)) _ = 0
    rw [Measure.dirac_apply]
    by_cases hc : certC s D δ ε H
    · simp only [hc, ↓reduceIte]
      refine Set.indicator_of_notMem (fun h => ?_) _
      have hF := hc.2.1
      rcases (show 0 ≤ wHatF D (thetaHat D H) (Sum.inl 0) by rw [F_d] at hF; exact hF.1).lt_or_eq
        with ha | ha
      · exact h.1 ⟨hF, ha⟩
      · refine h.2 ?_
        rw [E_d]; rw [F_d] at hF
        exact ⟨ha.symm, hF.2.1, by linarith [hF.2.2]⟩
    · simp only [hc, ↓reduceIte]
      exact Set.indicator_of_notMem (fun h => h.2 (vHatE_mem_any hs hK _)) _
  · calc falseP D δ θ (gateC s D N δ ε)
        ≤ ∑ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then 0 else mass D σ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          show mass D σ * (Measure.dirac (if certC s D δ ε (hist D θ σ)
            then wHatF D (thetaHat D (hist D θ σ)) else vHatE D (thetaHat D (hist D θ σ))) _).toReal
            ≤ _
          rw [Novel.M4BoundedLawRateProof.dirac_toReal]
          by_cases he : errN D σ ∈ Aset D N ε
          · by_cases hc : certC s D δ ε (hist D θ σ)
            · have hw := (plugin hs hs1 hK hN hθ σ).1
              have hA : wHatF D (thetaHat D (hist D θ σ)) ∉
                  {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δ / 4} := fun h => by
                have := ell_le_Adv hs hs1 hK hN (hCmem θ σ he hθ)
                rw [hw] at h
                linarith [h.2, hc.2.2.2]
              simp [hc, hA, he]
            · have hE : vHatE D (thetaHat D (hist D θ σ)) ∉
                  {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δ / 4} := fun h => by
                have := vHatE_mem_any hs hK (thetaHat D (hist D θ σ))
                rw [E_d] at this
                linarith [h.1, this.1]
              simp [hc, hE, he]
          · simp only [he, ↓reduceIte]
            split_ifs <;> linarith [hmass σ]
      _ ≤ ε := by
          have e : ∀ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then 0 else mass D σ)
              = mass D σ - (if errN D σ ∈ Aset D N ε then mass D σ else 0) := fun σ => by
            split_ifs <;> ring
          simp only [e, Finset.sum_sub_distrib, hsum]
          linarith
  · refine le_trans hcov (Finset.sum_le_sum fun σ _ => ?_)
    show _ ≤ mass D σ * (Measure.dirac (if certC s D δ ε (hist D θ σ)
      then wHatF D (thetaHat D (hist D θ σ)) else vHatE D (thetaHat D (hist D θ σ))) _).toReal
    rw [Novel.M4BoundedLawRateProof.dirac_toReal]
    by_cases he : errN D σ ∈ Aset D N ε
    · have hC := hCmem θ σ he hθ
      have hh := ell_ge hs hs1 hK hN hδ hθ hG hρ hC
      have hpl := plugin hs hs1 hK hN hθ σ
      have hapos : 0 < ahat D (hist D θ σ) := by
        rcases (ahat_nonneg hs hs1 hK (hist D θ σ)).lt_or_eq with h | h
        · exact h
        · exfalso
          have : ellC s D ε (hist D θ σ) ≤ 0 := by
            rw [ellC, ← h]; nlinarith [sq_nonneg (rho s D N ε)]
          linarith
      have hc : certC s D δ ε (hist D θ σ) :=
        ⟨⟨θ, hC⟩, by rw [hpl.1]; exact hpl.2.2.1, hapos, by linarith⟩
      have hA : wHatF D (thetaHat D (hist D θ σ)) ∈
          {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv D w θ} := by
        rw [hpl.1]
        refine ⟨by simp only [act, Sum.elim_inl]; exact hapos, ?_⟩
        have := ell_le_Adv hs hs1 hK hN hC
        linarith
      simp [hc, hA, he]
    · simp only [he, ↓reduceIte]
      split_ifs <;> linarith [hmass σ]

/-! ### Part 2: the lower bound -/

lemma record_congr {s : ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ} {θ θ' : Fin 3 → ℝ} {x x' : S}
    (h : θ + s • U x = θ' + s • U x') : record (data s q U) θ x = record (data s q U) θ' x' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  rw [record_d, record_d, h0, h1]
  congr 1
  linarith

theorem lowerBound : LowerBound := by
  intro s δ ε hs hs1 hδ hδs hε hε1 N hN hyp
  obtain ⟨r2sq, r2pos, r2le⟩ := sqrt2_facts
  -- the scale
  set δ' := Real.sqrt (2 * δ) with hδ'def
  have hδ' : 0 < δ' := Real.sqrt_pos.mpr (by positivity)
  have hδ'sq : δ' ^ 2 = 2 * δ := Real.sq_sqrt (by positivity)
  have hδ's : δ' ≤ s / 8 := by
    rw [hδ'def, Real.sqrt_le_left (by positivity)]; linarith
  have hx2 : 2 ≤ s / (4 * δ') := by rw [le_div_iff₀ (by positivity)]; linarith
  set k := ⌊s / (4 * δ')⌋₊ with hkdef
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hx2)
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkσ : (k : ℝ) ≤ s / (4 * δ') := Nat.floor_le (by positivity)
  have hk8 : s / (8 * δ') ≤ k := by
    have := Nat.lt_floor_add_one (s / (4 * δ'))
    rw [← hkdef] at this
    have e : s / (8 * δ') = (s / (4 * δ')) / 2 := by field_simp; ring
    rw [e]; linarith
  set V := Novel.M4JointDirectionalRateProof.Vg k
  have hV := Novel.M4JointDirectionalRateProof.Vg_ge hk2
  have hVu := Novel.M4JointDirectionalRateProof.Vg_le hk2
  have hV0 := Novel.M4JointDirectionalRateProof.Vg_pos hk2
  set a := 1 / (2 * Real.sqrt V) with hadef
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have ha0 : 0 < a := by positivity
  have hsV1 : 1 / 2 ≤ Real.sqrt V := by
    rw [Real.le_sqrt (by norm_num) hV0.le]; nlinarith
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one (by positivity)]; linarith
  have hsV2 : Real.sqrt V ≤ 2 * k := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have has : δ' ≤ a * s := by
    have : 1 / (4 * (k : ℝ)) ≤ a := by
      rw [hadef]; apply one_div_le_one_div_of_le (by positivity); linarith
    have h4 : δ' ≤ s / (4 * k) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at hkσ; linarith
    calc δ' ≤ s / (4 * k) := h4
      _ = 1 / (4 * k) * s := by ring
      _ ≤ a * s := mul_le_mul_of_nonneg_right this hs.le
  -- the direction h = (1, 0, 1)/√2 and its orthogonal completion
  set h : Fin 3 → ℝ := (1 / Real.sqrt 2) • ![1, 0, 1] with hhdef
  have hu : h ⬝ᵥ h = 1 := by
    rw [hhdef, dot3]; simp; field_simp; linarith
  have hxh : h 0 + h 2 = Real.sqrt 2 := by
    rw [hhdef]; simp; field_simp; linarith
  have hhi : ∀ i, |h i| ≤ 1 := fun i => by
    rw [← sq_le_one_iff_abs_le_one]; exact (coord_sq_le h i).trans (le_of_eq hu)
  clear_value h
  set H := Novel.M4JointDirectionalRateProof.hhm h
  have hHH : H * Hᵀ = 1 := by
    rw [Novel.M4JointDirectionalRateProof.hhm_symm hu, Novel.M4JointDirectionalRateProof.hhm_sq hu]
  have hHH' : Hᵀ * H = 1 := by
    rw [Novel.M4JointDirectionalRateProof.hhm_symm hu, Novel.M4JointDirectionalRateProof.hhm_sq hu]
  -- the hard law and the hypothesized rule
  set U : Fin (4 * k - 2 + 1) × Bool × Bool → Fin 3 → ℝ :=
    fun x => H *ᵥ Novel.M4JointDirectionalRateProof.wv k x with hUdef
  have hK : InKJ (Novel.M4JointDirectionalRateProof.qw k) U :=
    Novel.M4JointDirectionalRateProof.inKJ_orth
      (Novel.M4JointDirectionalRateProof.latent_inKJ hk2) hHH hHH'
  obtain ⟨ρ, hA, hfalse, hpow⟩ := hyp _ (Novel.M4JointDirectionalRateProof.qw k) U hK
  set D := data s (Novel.M4JointDirectionalRateProof.qw k) U with hDdef
  set θm := cC + s • ((-a) • h) with hθmdef
  set θp := cC + s • (a • h) with hθpdef
  have hθm : θm ∈ Theta4 (V4 s) := box_mem fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos ha0]
    nlinarith [hhi i, abs_nonneg (h i)]
  have hθp : θp ∈ Theta4 (V4 s) := box_mem fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ha0]
    nlinarith [hhi i, abs_nonneg (h i)]
  have hxm : xs θm = -(a * s * Real.sqrt 2) := by
    simp only [hθmdef, xs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cC]
    simp; rw [← hxh]; ring
  have hxp : xs θp = a * s * Real.sqrt 2 := by
    simp only [hθpdef, xs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cC]
    simp; rw [← hxh]; ring
  have hneg : xs θm < 0 := by rw [hxm]; have := mul_pos (mul_pos ha0 hs) r2pos; linarith
  have hGp : δ ≤ Gstar D θp := by
    obtain ⟨b1, b2, b3, b4⟩ := mem_box hs hθp
    have hmx : max (xs θp) 0 / 2 + θp 1 ≤ 1 := by
      rcases le_total (xs θp) 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    rw [Gstar_d hs hK (by linarith) hmx, hxp, max_eq_left (by positivity)]
    have : (a * s) ^ 2 ≥ δ' ^ 2 := pow_le_pow_left₀ hδ'.le has 2
    nlinarith
  -- certification probabilities at the two parameters
  let c : (Fin N → Record 1) → ℝ := fun Hs => (ρ.kernel Hs {w | 0 < w (Sum.inl 0)}).toReal
  have hc01 : ∀ Hs, 0 ≤ c Hs ∧ c Hs ≤ 1 := fun Hs =>
    Novel.M4BoundedLawRateProof.kernel_bounds ρ Hs _
  have hmass : ∀ σ : Fin N → Fin (4 * k - 2 + 1) × Bool × Bool, 0 ≤ mass D σ := fun σ =>
    Finset.prod_nonneg fun _ _ => hK.1 _
  have hm : ∑ σ, mass D σ * c (hist D θm σ) ≤ ε := by
    refine le_trans (Finset.sum_le_sum fun σ _ => ?_) (hfalse _ hθm)
    refine mul_le_mul_of_nonneg_left ?_ (hmass σ)
    have := ρ.isProb (hist D θm σ)
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    obtain ⟨b1, b2, -, -⟩ := mem_box hs hθm
    calc ρ.kernel _ {w | 0 < w (Sum.inl 0)}
        ≤ ρ.kernel _ ({w | 0 < w (Sum.inl 0) ∧ Adv D w θm ≤ δ / 4}
            ∪ {w | ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0)) ∧ w ∉ E D}) := by
          apply measure_mono
          intro w hw
          simp only [Set.mem_ofPred_eq] at hw
          by_cases hF : w ∈ F D
          · refine Or.inl ⟨hw, ?_⟩
            rw [act_ext w, Adv_d hs hK (by linarith) (by linarith)]
            have e1 := mul_neg_of_pos_of_neg hw hneg
            have e2 := sq_nonneg (w (Sum.inl 0))
            have e3 := sq_nonneg (w (Sum.inr 0) - θm 1)
            linarith
          · refine Or.inr ⟨fun h' => hF h'.1, fun hE => ?_⟩
            rw [E_d] at hE; linarith [hE.1]
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hA, add_zero]
  have hp : 1 - ε ≤ ∑ σ, mass D σ * c (hist D θp σ) := by
    refine le_trans (hpow _ hθp hGp) (Finset.sum_le_sum fun σ _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hmass σ)
    have := ρ.isProb (hist D θp σ)
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun w hw => hw.1)
  have hsum1 : ∑ σ : Fin N → Fin (4 * k - 2 + 1) × Bool × Bool, mass D σ = 1 :=
    Novel.M4BoundedLawRateProof.mass_sum D hK.2.1 N
  -- the common atoms
  let sm : (Fin N → Fin (4 * k - 2) × Bool × Bool) → (Fin N → Fin (4 * k - 2 + 1) × Bool × Bool) :=
    fun τ l => ((τ l).1.succ, (τ l).2)
  let sp : (Fin N → Fin (4 * k - 2) × Bool × Bool) → (Fin N → Fin (4 * k - 2 + 1) × Bool × Bool) :=
    fun τ l => ((τ l).1.castSucc, (τ l).2)
  have hsm : Function.Injective sm := fun τ τ' h' => funext fun l => by
    have := congrFun h' l
    simp only [sm, Prod.mk.injEq] at this
    exact Prod.ext (Fin.succ_injective _ this.1) this.2
  have hsp : Function.Injective sp := fun τ τ' h' => funext fun l => by
    have := congrFun h' l
    simp only [sp, Prod.mk.injEq] at this
    exact Prod.ext (Fin.castSucc_injective _ this.1) this.2
  have hstep : ∀ (j : Fin (4 * k - 2)) (b : Bool × Bool),
      Novel.M4JointDirectionalRateProof.wv k (j.succ, b)
        = Novel.M4JointDirectionalRateProof.wv k (j.castSucc, b)
          + (2 * a) • Novel.M4JointDirectionalRateProof.e0 := by
    intro j b
    funext i
    fin_cases i
    · simp only [Novel.M4JointDirectionalRateProof.wv, Novel.M4JointDirectionalRateProof.Wg,
        Novel.M4JointDirectionalRateProof.zv, Novel.M4JointDirectionalRateProof.e0, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Fin.val_succ, Fin.val_castSucc, hadef]
      push_cast
      field_simp
      ring
    · simp [Novel.M4JointDirectionalRateProof.wv, Novel.M4JointDirectionalRateProof.e0]
    · simp [Novel.M4JointDirectionalRateProof.wv, Novel.M4JointDirectionalRateProof.e0]
  have hhist : ∀ τ, hist D θm (sm τ) = hist D θp (sp τ) := by
    intro τ
    funext l
    apply record_congr
    simp only [sm, sp, hUdef]
    rw [hstep, Matrix.mulVec_add, Matrix.mulVec_smul, Novel.M4JointDirectionalRateProof.hhm_col hu]
    funext i
    simp only [hθmdef, hθpdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : ∑ τ, mass D (sm τ) * c (hist D θp (sp τ)) ≤ ε := by
    refine le_trans (le_of_eq ?_) (le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sm hsm
      (fun σ => mass D σ * c (hist D θm σ))
      (fun σ => mul_nonneg (hmass σ) (hc01 _).1)) hm)
    exact Finset.sum_congr rfl fun τ _ => by rw [hhist]
  have h2 : ∑ τ, mass D (sp τ) * (1 - c (hist D θp (sp τ))) ≤ ε := by
    refine le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sp hsp
      (fun σ => mass D σ * (1 - c (hist D θp σ)))
      (fun σ => mul_nonneg (hmass σ) (by linarith [(hc01 (hist D θp σ)).2]))) ?_
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum1]
    linarith
  have ha2 : ∀ τ, (∏ l, Novel.M4JointDirectionalRateProof.sa k (τ l)) ^ 2
      = mass D (sm τ) * mass D (sp τ) := by
    intro τ
    simp only [mass, sm, sp, hDdef, data, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      Novel.M4JointDirectionalRateProof.sa_sq]
  have hps : ∑ τ, mass D (sm τ) ≤ 1 :=
    le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sm hsm (mass D) hmass) (le_of_eq hsum1)
  have hrs : ∑ τ, mass D (sp τ) ≤ 1 :=
    le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sp hsp (mass D) hmass) (le_of_eq hsum1)
  have hle := Novel.M4BoundedLawRateProof.lecam (fun τ => mass D (sm τ)) (fun τ => mass D (sp τ))
    (fun τ => c (hist D θp (sp τ))) (fun τ => ∏ l, Novel.M4JointDirectionalRateProof.sa k (τ l)) ε
    (fun τ => hmass _) (fun τ => hmass _) hps hrs (fun τ => hc01 _) h1 h2
    (fun τ => Finset.prod_nonneg fun l _ => Novel.M4JointDirectionalRateProof.sa_nonneg _) ha2
  rw [Novel.M4JointDirectionalRateProof.sa_total, Novel.M4JointDirectionalRateProof.phi_kk hk2]
    at hle
  have hfin := Novel.M4JointDirectionalRateProof.final_log hk2 hN hδ' hε hε1 hk8 hs hle
  rw [hδ'sq] at hfin
  have e : 1 / (16 * Real.pi ^ 2) * (s ^ 2 / (2 * δ)) = s ^ 2 / (32 * Real.pi ^ 2 * δ) := by
    field_simp; ring
  rw [e] at hfin
  exact hfin

theorem proof : Standalone.M4CurvedEntryRate.statement :=
  ⟨geometry, lowerBound, upperBound, curvedCertificate⟩

end

end Novel.M4CurvedEntryRateProof

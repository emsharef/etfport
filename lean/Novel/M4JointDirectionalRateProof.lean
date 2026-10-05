import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.M4JointDirectionalRate
import Novel.M4BoundedLawRateProof

/-!
# Proof of claim 016: joint directional information against a moving ETF comparator

This proof imports claim 015's proof module (`depends_on: [2, 15]`; Q-04) for its hard sine-weight
law, affinity identity, finite testing inequality and logarithm bound. The paired-contrast identity
of claim 002 is re-derived directly for this score.
* **Part 1:** `Q = a(λ₁ + α) + p λ₂` on the funded triangle, so the ETF-class supremum is
  `max(0, λ₂)` and `Adv(w_A) = min(d₀'θ, d₁'θ)`.
* **Moore–Penrose:** `Ω = J J'` is symmetric, and the spectral theorem gives a Moore–Penrose inverse.
  From the first Penrose equation, `J = Ω G J`, so every error `J Ū` lies in `Im Ω` with
  `e'Ω†e ≤ ‖Ū‖²`, and `|d'e| ≤ σ_d √(e'Ω†e)` on `Im Ω`.
* **Part 2, lower bound:** claim 015's hard law on `4k - 1` points is embedded along
  `h = J'd_j/σ` by an orthogonal (Householder) completion. This keeps `E U U' = I`, and the two
  hard parameters give identical histories on the common atoms.
* **Part 2, upper bound:** `E exp(tY) ≤ 1 + t² ≤ exp(t²)` for `|tY| ≤ 1`, from
  `|e^x - 1 - x| ≤ x²`. With a finite product expansion and a union bound over the three
  coordinates this gives `t_{N,ε} ≤ 12 log(6/ε)`.
-/

namespace Novel.M4JointDirectionalRateProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4JointDirectionalRate
open Standalone.M4InformationObstruction (toPar Theta4 M4Admissible Record record hist mass prob X
  thetaHat zeta Omega IsMoorePenrose pinv errN TN tcrit Aset Cset etfSup Adv Gstar LN LexLE lexSel
  wHatF vHatE Rule)
open Standalone.M4BoundedLawRate (falseP powerP Meets)
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

lemma inst_ext (w : Inst 1 1 → ℝ) :
    w = Sum.elim (fun _ => w (Sum.inl 0)) (fun _ => w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

lemma dot3 (a b : Fin 3 → ℝ) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_three]

lemma d0_dot (θ : Fin 3 → ℝ) : d0 ⬝ᵥ θ = θ 0 + θ 2 := by rw [dot3]; simp [d0]

lemma d1_dot (θ : Fin 3 → ℝ) : d1 ⬝ᵥ θ = θ 0 - θ 1 + θ 2 := by rw [dot3]; simp [d1]; ring

/-! ### The data -/

section Data

variable (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ)

lemma W0_d : W0 (data J q U) = 1 := by simp [W0, data]

lemma w0_d : w0 (data J q U) = 0 := by funext i; simp [w0, data]

lemma tau_d (v : Inst 1 1 → ℝ) : tau (data J q U) v = 0 := by simp [tau, data]

lemma cash_d (w : Inst 1 1 → ℝ) :
    cash (data J q U) w = 1 - (w (Sum.inl 0) + w (Sum.inr 0)) := by
  rw [cash, w0_d, tau_d]
  simp [k0, W0_d, Fintype.sum_sum_type]
  simp [data]

lemma F_d : F (data J q U)
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

lemma E_d : E (data J q U) = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} := by
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

lemma score_d (w : Inst 1 1 → ℝ) (θ : Fin 3 → ℝ) :
    score (data J q U) w (toPar θ) = w (Sum.inl 0) * (θ 0 + θ 2) + w (Sum.inr 0) * θ 1 := by
  rw [score, tau_d]
  simp [exposure, active, etf, data, toPar, dotProduct, mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  ring

lemma ret_inl (θ : Fin 3 → ℝ) (s : S) : ret (data J q U) (toPar θ) s (Sum.inl 0)
    = θ 0 + (J *ᵥ U s) 0 + θ 2 + (J *ᵥ U s) 2 := by
  simp [ret, data, toPar, Matrix.vecHead, Matrix.vecTail]

lemma ret_inr (θ : Fin 3 → ℝ) (s : S) :
    ret (data J q U) (toPar θ) s (Sum.inr 0) = θ 1 + (J *ᵥ U s) 1 := by
  simp [ret, data, toPar, Matrix.vecHead, Matrix.vecTail]

lemma record_d (θ : Fin 3 → ℝ) (s : S) : record (data J q U) θ s
    = ⟨![θ 0 + (J *ᵥ U s) 0, θ 1 + (J *ᵥ U s) 1], θ 0 + (J *ᵥ U s) 0 + θ 2 + (J *ᵥ U s) 2,
      fun _ => θ 1 + (J *ᵥ U s) 1⟩ := by
  have h1 := ret_inl J q U θ s
  have h2 := ret_inr J q U θ s
  simp only [record, h1]
  congr 1
  · funext k; fin_cases k <;> simp [data, toPar]
  · funext j; obtain rfl : j = 0 := Subsingleton.elim _ _; exact h2

lemma X_d (θ : Fin 3 → ℝ) (s : S) :
    X (data J q U) (record (data J q U) θ s) = θ + J *ᵥ U s := by
  rw [record_d]
  funext i
  fin_cases i <;> (simp [X, data, mulVec, dotProduct, Fin.sum_univ_two]; try ring)

lemma zeta_d (s : S) : zeta (data J q U) s = J *ᵥ U s := by
  funext i; fin_cases i <;> simp [zeta, data]

end Data

/-! ### Part 1: the moving comparator -/

section Opt

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

lemma zero_mem_E : (0 : Inst 1 1 → ℝ) ∈ E (data J q U) := by rw [E_d]; simp

lemma etf1_mem_E : etf1 ∈ E (data J q U) := by rw [E_d]; simp [etf1]

lemma wA_mem_F : wA ∈ F (data J q U) := by rw [F_d]; simp [wA]

lemma etfSup_d (θ : Fin 3 → ℝ) : etfSup (data J q U) θ = max 0 (θ 1) := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · rcases le_total (θ 1) 0 with h | h
    · refine ⟨0, zero_mem_E, ?_⟩
      simp only [score_d, Pi.zero_apply, zero_mul, add_zero]; exact (max_eq_left h).symm
    · refine ⟨etf1, etf1_mem_E, ?_⟩
      simp only [score_d, etf1, Sum.elim_inl, Sum.elim_inr]; rw [max_eq_right h]; ring
  · rintro _ ⟨v, hv, rfl⟩
    rw [E_d] at hv
    obtain ⟨ha, hp, hp1⟩ := hv
    simp only [score_d, ha, zero_mul, zero_add]
    rcases le_total (θ 1) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith

lemma maxE_neg {θ : Fin 3 → ℝ} (h : θ 1 < 0) :
    maximizers (fun v => score (data J q U) v (toPar θ)) (E (data J q U)) = {0} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax 0 zero_mem_E
    rw [E_d] at hw
    obtain ⟨ha, hp, hp1⟩ := hw
    simp only [score_d, ha, Pi.zero_apply, zero_mul, add_zero, zero_add] at hm
    have : w (Sum.inr 0) = 0 := by nlinarith
    rw [inst_ext w, ha, this]; funext i; rcases i with k | k <;> rfl
  · rintro rfl
    refine ⟨zero_mem_E, fun v hv => ?_⟩
    rw [E_d] at hv
    simp only [score_d, hv.1, Pi.zero_apply, zero_mul, add_zero, zero_add]
    nlinarith [hv.2.1]

lemma maxE_pos {θ : Fin 3 → ℝ} (h : 0 < θ 1) :
    maximizers (fun v => score (data J q U) v (toPar θ)) (E (data J q U)) = {etf1} := by
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax etf1 etf1_mem_E
    rw [E_d] at hw
    obtain ⟨ha, hp, hp1⟩ := hw
    simp only [score_d, ha, etf1, Sum.elim_inl, Sum.elim_inr, zero_mul, zero_add] at hm
    have : w (Sum.inr 0) = 1 := by nlinarith
    rw [inst_ext w, ha, this]; rfl
  · rintro rfl
    refine ⟨etf1_mem_E, fun v hv => ?_⟩
    rw [E_d] at hv
    simp only [score_d, hv.1, etf1, Sum.elim_inl, Sum.elim_inr, zero_mul, zero_add]
    nlinarith [hv.2.2]

lemma Adv_wA (θ : Fin 3 → ℝ) : Adv (data J q U) wA θ = min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := by
  rw [Adv, etfSup_d, score_d, d0_dot, d1_dot]
  simp only [wA, Sum.elim_inl, Sum.elim_inr, one_mul, zero_mul, add_zero]
  rcases le_total (θ 1) 0 with h | h
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring

lemma score_le_F {w : Inst 1 1 → ℝ} (hw : w ∈ F (data J q U)) (θ : Fin 3 → ℝ) :
    score (data J q U) w (toPar θ) ≤ max 0 (max (θ 1) (θ 0 + θ 2)) := by
  rw [F_d] at hw
  obtain ⟨ha, hp, hs⟩ := hw
  rw [score_d]
  have h1 : θ 0 + θ 2 ≤ max 0 (max (θ 1) (θ 0 + θ 2)) := le_max_of_le_right (le_max_right _ _)
  have h2 : θ 1 ≤ max 0 (max (θ 1) (θ 0 + θ 2)) := le_max_of_le_right (le_max_left _ _)
  have h0 : 0 ≤ max 0 (max (θ 1) (θ 0 + θ 2)) := le_max_left _ _
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hp]

lemma Gstar_d (θ : Fin 3 → ℝ) : Gstar (data J q U) θ = max 0 (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) := by
  have hsup : sSup ((fun w => score (data J q U) w (toPar θ)) '' F (data J q U))
      = max 0 (max (θ 1) (θ 0 + θ 2)) := by
    apply IsGreatest.csSup_eq
    refine ⟨?_, by rintro _ ⟨v, hv, rfl⟩; exact score_le_F hv θ⟩
    rcases le_total (max (θ 1) (θ 0 + θ 2)) 0 with h | h
    · refine ⟨0, (zero_mem_E (J := J) (q := q) (U := U)).1, ?_⟩
      simp only [score_d, Pi.zero_apply, zero_mul, add_zero]; exact (max_eq_left h).symm
    · rw [max_eq_right h]
      rcases le_total (θ 1) (θ 0 + θ 2) with h' | h'
      · refine ⟨wA, wA_mem_F, ?_⟩
        simp only [score_d, wA, Sum.elim_inl, Sum.elim_inr]; rw [max_eq_right h']; ring
      · refine ⟨etf1, (etf1_mem_E (J := J) (q := q) (U := U)).1, ?_⟩
        simp only [score_d, etf1, Sum.elim_inl, Sum.elim_inr]; rw [max_eq_left h']; ring
  rw [Gstar, hsup, etfSup_d, d0_dot, d1_dot]
  rcases le_total (θ 1) 0 with h | h <;> rcases le_total (θ 1) (θ 0 + θ 2) with h' | h' <;>
    rcases le_total (θ 0 + θ 2) 0 with h'' | h'' <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

lemma maxF_pos {θ : Fin 3 → ℝ} (h : 0 < min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) :
    maximizers (fun w => score (data J q U) w (toPar θ)) (F (data J q U)) = {wA} := by
  rw [d0_dot, d1_dot, lt_min_iff] at h
  obtain ⟨hA, hB⟩ := h
  have key : ∀ w ∈ F (data J q U), score (data J q U) w (toPar θ)
      = (θ 0 + θ 2) - ((1 - w (Sum.inl 0) - w (Sum.inr 0)) * (θ 0 + θ 2)
        + w (Sum.inr 0) * (θ 0 + θ 2 - θ 1)) := fun w _ => by rw [score_d]; ring
  ext w
  simp only [maximizers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmax⟩
    have hm := hmax wA wA_mem_F
    rw [key w hw, key wA wA_mem_F] at hm
    rw [F_d] at hw
    obtain ⟨ha, hp, hs⟩ := hw
    simp only [wA, Sum.elim_inl, Sum.elim_inr] at hm
    have h1 : 0 ≤ (1 - w (Sum.inl 0) - w (Sum.inr 0)) * (θ 0 + θ 2) :=
      mul_nonneg (by linarith) hA.le
    have h2 : 0 ≤ w (Sum.inr 0) * (θ 0 + θ 2 - θ 1) := mul_nonneg hp (by linarith)
    have hp0 : w (Sum.inr 0) = 0 := by
      by_contra hne
      have : 0 < w (Sum.inr 0) * (θ 0 + θ 2 - θ 1) :=
        mul_pos (lt_of_le_of_ne hp (Ne.symm hne)) (by linarith)
      linarith
    have ha1 : w (Sum.inl 0) = 1 := by
      by_contra hne
      have : 0 < (1 - w (Sum.inl 0) - w (Sum.inr 0)) * (θ 0 + θ 2) :=
        mul_pos (by rw [hp0]; exact lt_of_le_of_ne (by linarith) (fun h' => hne (by linarith)))
          hA
      linarith
    rw [inst_ext w, ha1, hp0]; rfl
  · rintro rfl
    refine ⟨wA_mem_F, fun v hv => ?_⟩
    show score (data J q U) v (toPar θ) ≤ score (data J q U) wA (toPar θ)
    rw [key v hv, key wA wA_mem_F]
    rw [F_d] at hv
    obtain ⟨ha, hp, hs⟩ := hv
    simp only [wA, Sum.elim_inl, Sum.elim_inr]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - v (Sum.inl 0) - v (Sum.inr 0)) hA.le,
      mul_nonneg hp (by linarith : (0 : ℝ) ≤ θ 0 + θ 2 - θ 1)]

lemma Adv_neg {θ : Fin 3 → ℝ} (h : min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) < 0) {w : Inst 1 1 → ℝ}
    (hw : w ∈ F (data J q U)) (ha : 0 < w (Sum.inl 0)) : Adv (data J q U) w θ < 0 := by
  rw [Adv, etfSup_d, score_d]
  rw [d0_dot, d1_dot] at h
  rw [F_d] at hw
  obtain ⟨-, hp, hs⟩ := hw
  have hM : θ 0 + θ 2 < max 0 (θ 1) := by
    rcases le_total (θ 1) 0 with h' | h'
    · rw [max_eq_left h']; rw [min_eq_left (by linarith)] at h; linarith
    · rw [max_eq_right h']
      rcases le_total (θ 0 + θ 2) (θ 0 - θ 1 + θ 2) with h'' | h''
      · rw [min_eq_left h''] at h; linarith
      · rw [min_eq_right h''] at h; linarith
  have hB : θ 1 ≤ max 0 (θ 1) := le_max_right _ _
  have h0 : 0 ≤ max 0 (θ 1) := le_max_left _ _
  nlinarith [mul_le_mul_of_nonneg_left hB hp, mul_lt_mul_of_pos_left hM ha]

lemma paired0 (θ θ' : Fin 3 → ℝ) :
    (score (data J q U) wA (toPar θ') - score (data J q U) 0 (toPar θ'))
      - (score (data J q U) wA (toPar θ) - score (data J q U) 0 (toPar θ)) = d0 ⬝ᵥ (θ' - θ) := by
  simp only [score_d, wA, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, d0_dot, Pi.sub_apply]; ring

lemma paired1 (θ θ' : Fin 3 → ℝ) :
    (score (data J q U) wA (toPar θ') - score (data J q U) etf1 (toPar θ'))
      - (score (data J q U) wA (toPar θ) - score (data J q U) etf1 (toPar θ))
      = d1 ⬝ᵥ (θ' - θ) := by
  simp only [score_d, wA, etf1, Sum.elim_inl, Sum.elim_inr, d1_dot, Pi.sub_apply]; ring

end Opt

/-! ### The domain: box points belong to `Θ₄` -/

/-- The sign vector of `b`. -/
def sgv (b : Fin 3 → Bool) : Fin 3 → ℝ := fun i => if b i then 1 else -1

/-- One factor of the multilinear weight. -/
def bf (v : Fin 3 → ℝ) (i : Fin 3) (c : Bool) : ℝ := (1 + (if c then 1 else -1) * v i) / 2

/-- The multilinear weight of vertex `b` for the box point `v`. -/
def bw (v : Fin 3 → ℝ) (b : Fin 3 → Bool) : ℝ := ∏ i, bf v i (b i)

lemma bw_nonneg {v : Fin 3 → ℝ} (hv : ∀ i, |v i| ≤ 1) (b : Fin 3 → Bool) : 0 ≤ bw v b := by
  refine Finset.prod_nonneg fun i _ => div_nonneg ?_ (by norm_num)
  have := abs_le.mp (hv i)
  split_ifs <;> linarith

lemma bw_sum (v : Fin 3 → ℝ) : ∑ b, bw v b = 1 := by
  rw [show ∑ b, bw v b = ∑ b : Fin 3 → Bool, ∏ i, bf v i (b i) from rfl, ← Fintype.prod_sum]
  simp only [bf, Fintype.sum_bool]
  exact Finset.prod_eq_one fun i _ => by simp; ring

lemma bw_mean (v : Fin 3 → ℝ) (k : Fin 3) : ∑ b, bw v b * sgv b k = v k := by
  let g : Fin 3 → Bool → ℝ := fun i c => bf v i c * (if i = k then (if c then 1 else -1) else 1)
  have h : ∀ b : Fin 3 → Bool, bw v b * sgv b k = ∏ i, g i (b i) := fun b => by
    simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  rw [Finset.sum_congr rfl fun b _ => h b, ← Fintype.prod_sum]
  rw [Finset.prod_eq_single k (fun i _ hi => by simp [g, hi, bf]; ring)
    (fun h => absurd (Finset.mem_univ k) h)]
  simp [g, bf]
  ring

lemma box_mem (J : Matrix (Fin 3) (Fin 3) ℝ) (j : Bool) {v : Fin 3 → ℝ} (hv : ∀ i, |v i| ≤ 1) :
    (if j then c1 else c0) + J *ᵥ v ∈ Theta4 (V4 J) := by
  have hmem : ∀ b : Fin 3 → Bool, (if j then c1 else c0) + J *ᵥ sgv b ∈ (V4 J : Set _) :=
    fun b => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(j, b), Finset.mem_univ _, rfl⟩)
  have hsum := (convex_convexHull ℝ (V4 J : Set (Fin 3 → ℝ))).sum_mem (t := Finset.univ)
    (w := bw v) (z := fun b => (if j then c1 else c0) + J *ᵥ sgv b)
    (fun b _ => bw_nonneg hv b) (bw_sum v) (fun b _ => subset_convexHull ℝ _ (hmem b))
  have hv' : ∑ b, bw v b • sgv b = v := by
    funext k; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; exact bw_mean v k
  have heq : (if j then c1 else c0) + J *ᵥ v
      = ∑ b, bw v b • ((if j then c1 else c0) + J *ᵥ sgv b) := by
    rw [Finset.sum_congr rfl fun b _ => smul_add (bw v b) _ _, Finset.sum_add_distrib,
      ← Finset.sum_smul, bw_sum, one_smul]
    congr 1
    conv_lhs => rw [← hv']
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  rw [heq]
  exact hsum

/-! ### Second moments of the law and `Ω = J J'` -/

section Moments

variable {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

lemma mean_dot (hK : InKJ q U) (A : Fin 3 → ℝ) : ∑ s, q s * (A ⬝ᵥ U s) = 0 := by
  obtain ⟨-, -, h0, -, -⟩ := hK
  have e : ∀ s, q s * (A ⬝ᵥ U s)
      = A 0 * (q s * U s 0) + A 1 * (q s * U s 1) + A 2 * (q s * U s 2) := fun s => by
    rw [dot3]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h0, mul_zero, add_zero]

lemma second_dot (hK : InKJ q U) (A B : Fin 3 → ℝ) :
    ∑ s, q s * ((A ⬝ᵥ U s) * (B ⬝ᵥ U s)) = A ⬝ᵥ B := by
  obtain ⟨-, -, -, h2, -⟩ := hK
  have e : ∀ s, q s * ((A ⬝ᵥ U s) * (B ⬝ᵥ U s))
      = ∑ a : Fin 3, ∑ b : Fin 3, A a * B b * (q s * (U s a * U s b)) := fun s => by
    simp only [dot3, Fin.sum_univ_three]; ring
  rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_comm]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  simp only [← Finset.mul_sum, h2]
  simp [dot3, Fin.sum_univ_three, Matrix.one_apply]

lemma mulVec_row (J : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) (i : Fin 3) :
    (J *ᵥ u) i = J i ⬝ᵥ u := rfl

lemma omega_eq (J : Matrix (Fin 3) (Fin 3) ℝ) (hK : InKJ q U) :
    Omega (data J q U) = J * Jᵀ := by
  ext i k
  simp only [Omega, zeta_d]
  show ∑ s, q s * ((J *ᵥ U s) i * (J *ᵥ U s) k) = (J * Jᵀ) i k
  simp only [mulVec_row]
  rw [second_dot hK]
  simp [Matrix.mul_apply, dotProduct]

end Moments

/-! ### Admissibility -/

lemma coord_sq_le (w : Fin 3 → ℝ) (i : Fin 3) : w i ^ 2 ≤ w ⬝ᵥ w := by
  rw [dot3]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]

lemma ge_of_sq_le {x b : ℝ} (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : -b ≤ x := by nlinarith

lemma J_coord {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : SmallJ J) {v : Fin 3 → ℝ} {B : ℝ}
    (hv : v ⬝ᵥ v ≤ B) (i : Fin 3) : (J *ᵥ v) i ^ 2 ≤ (1 / 100) ^ 2 * B :=
  (coord_sq_le _ i).trans ((hJ v).trans (by nlinarith))

lemma sgv_dot (b : Fin 3 → Bool) : sgv b ⬝ᵥ sgv b = 3 := by
  rw [dot3]; simp only [sgv]; split_ifs <;> norm_num

lemma admissible {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : SmallJ J) {S : Type} [Fintype S]
    {q : S → ℝ} {U : S → Fin 3 → ℝ} (hK : InKJ q U) : M4Admissible (data J q U) (V4 J) := by
  obtain ⟨hq, hq1, h0, h2, hU⟩ := hK
  have hc : ∀ i, ∑ s, q s * (J *ᵥ U s) i = 0 := fun i => by
    simp only [mulVec_row]; exact mean_dot ⟨hq, hq1, h0, h2, hU⟩ (J i)
  refine ⟨Or.inl rfl, Finset.univ_nonempty.image _, hq, hq1, fun k => ?_, fun j => ?_,
    fun j => by simp [data], by simp [data], fun i => by simp [data], by simp [data],
    by rw [W0_d]; norm_num, ?_, fun i => by simp [data], ?_⟩
  · fin_cases k
    · simpa [data] using hc 0
    · simpa [data] using hc 1
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [data] using hc 2
  · rw [w0_d, F_d]; simp
  · intro θ hθ s i
    simp only [V4, Finset.mem_image, Finset.mem_univ, true_and] at hθ
    obtain ⟨⟨j, b⟩, rfl⟩ := hθ
    have hb : ∀ k, -(1 / 50) ≤ (J *ᵥ fun i => if b i then (1 : ℝ) else -1) k := fun k =>
      ge_of_sq_le (by norm_num) ((J_coord hJ (le_of_eq (sgv_dot b)) k).trans (by norm_num))
    have hu : ∀ k, -(9 / 100) ≤ (J *ᵥ U s) k := fun k =>
      ge_of_sq_le (by norm_num) ((J_coord hJ (hU s) k).trans (by norm_num))
    rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
    · rw [ret_inl]
      have := hb 0; have := hb 2; have := hu 0; have := hu 2
      cases j <;> simp [c0, c1] <;> linarith
    · rw [ret_inr]
      have := hb 1; have := hu 1
      cases j <;> simp [c0, c1] <;> linarith

/-! ### iid marginals and the estimation covariance -/

section Iid

variable {S : Type} [Fintype S] {q : S → ℝ}

lemma marg1 (hq1 : ∑ s, q s = 1) {N : ℕ} (f : S → ℝ) (l : Fin N) :
    ∑ σ : Fin N → S, (∏ m, q (σ m)) * f (σ l) = ∑ s, q s * f s := by
  let G : Fin N → S → ℝ := fun m s => q s * (if m = l then f s else 1)
  have h : ∀ σ : Fin N → S, (∏ m, q (σ m)) * f (σ l) = ∏ m, G m (σ m) := fun σ => by
    simp only [G, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_congr rfl fun σ _ => h σ, ← Fintype.prod_sum]
  rw [Finset.prod_eq_single l (fun m _ hm => by simp [G, hm, hq1]) (by simp)]
  simp [G]

lemma marg2 (hq1 : ∑ s, q s = 1) {N : ℕ} (f g : S → ℝ) {l l' : Fin N} (hne : l ≠ l') :
    ∑ σ : Fin N → S, (∏ m, q (σ m)) * (f (σ l) * g (σ l'))
      = (∑ s, q s * f s) * (∑ s, q s * g s) := by
  let G : Fin N → S → ℝ := fun m s =>
    q s * ((if m = l then f s else 1) * (if m = l' then g s else 1))
  have h : ∀ σ : Fin N → S, (∏ m, q (σ m)) * (f (σ l) * g (σ l')) = ∏ m, G m (σ m) := fun σ => by
    simp only [G, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_congr rfl fun σ _ => h σ, ← Fintype.prod_sum]
  have hG : ∀ m, ∑ s, G m s
      = (if m = l then ∑ s, q s * f s else 1) * (if m = l' then ∑ s, q s * g s else 1) := by
    intro m
    by_cases h1 : m = l
    · subst h1; simp [G, hne]
    · by_cases h2 : m = l'
      · subst h2; simp [G, h1]
      · simp [G, h1, h2, hq1]
  simp only [hG, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

end Iid

lemma thetaHat_hist {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} {N : ℕ} (hN : 0 < N) (θ : Fin 3 → ℝ) (σ : Fin N → S) :
    thetaHat (data J q U) (hist (data J q U) θ σ) = θ + errN (data J q U) σ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  simp only [thetaHat, hist, X_d, errN, zeta_d, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  field_simp

lemma errN_d {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ} {N : ℕ}
    (σ : Fin N → S) (i : Fin 3) :
    errN (data J q U) σ i = (1 / (N : ℝ)) * ∑ l, (J *ᵥ U (σ l)) i := by
  simp only [errN, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, zeta_d]

lemma cov_hat {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} (hK : InKJ q U) (θ : Fin 3 → ℝ) {N : ℕ} (hN : 0 < N) (i k : Fin 3) :
    ∑ σ : Fin N → S, mass (data J q U) σ *
      ((thetaHat (data J q U) (hist (data J q U) θ σ) - θ) i *
        (thetaHat (data J q U) (hist (data J q U) θ σ) - θ) k) = (J * Jᵀ) i k / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq1 := hK.2.1
  have hΩ : ∑ s, q s * ((J *ᵥ U s) i * (J *ᵥ U s) k) = (J * Jᵀ) i k := by
    simp only [mulVec_row]; rw [second_dot hK]; simp [Matrix.mul_apply, dotProduct]
  have hm : ∀ a, ∑ s, q s * (J *ᵥ U s) a = 0 := fun a => by
    simp only [mulVec_row]; exact mean_dot hK (J a)
  have e : ∀ σ : Fin N → S, mass (data J q U) σ *
      ((thetaHat (data J q U) (hist (data J q U) θ σ) - θ) i *
        (thetaHat (data J q U) (hist (data J q U) θ σ) - θ) k)
      = (1 / (N : ℝ)) ^ 2 * ∑ l, ∑ l', (∏ m, q (σ m)) *
          ((J *ᵥ U (σ l)) i * (J *ᵥ U (σ l')) k) := by
    intro σ
    rw [thetaHat_hist hN]
    simp only [add_sub_cancel_left, errN_d]
    have hmass : mass (data J q U) σ = ∏ m, q (σ m) := rfl
    rw [hmass]
    calc (∏ m, q (σ m)) * ((1 / (N : ℝ) * ∑ l, (J *ᵥ U (σ l)) i) *
          (1 / (N : ℝ) * ∑ l, (J *ᵥ U (σ l)) k))
        = (1 / (N : ℝ)) ^ 2 * ((∏ m, q (σ m)) *
            ((∑ l, (J *ᵥ U (σ l)) i) * (∑ l, (J *ᵥ U (σ l)) k))) := by ring
      _ = _ := by rw [Finset.sum_mul_sum, Finset.mul_sum]; simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, Finset.sum_comm]
  simp only [fun l => Finset.sum_comm (s := (Finset.univ : Finset (Fin N → S)))
    (t := (Finset.univ : Finset (Fin N)))
    (f := fun σ l' => (∏ m, q (σ m)) * ((J *ᵥ U (σ l)) i * (J *ᵥ U (σ l')) k))]
  have hin : ∀ l l' : Fin N, ∑ σ : Fin N → S, (∏ m, q (σ m)) *
      ((J *ᵥ U (σ l)) i * (J *ᵥ U (σ l')) k) = if l = l' then (J * Jᵀ) i k else 0 := by
    intro l l'
    by_cases h : l = l'
    · subst h
      rw [marg1 hq1 (fun s => (J *ᵥ U s) i * (J *ᵥ U s) k) l]
      simp only [↓reduceIte]
      exact hΩ
    · rw [marg2 hq1 (fun s => (J *ᵥ U s) i) (fun s => (J *ᵥ U s) k) h, hm, zero_mul]
      simp only [h, ↓reduceIte]
  simp only [hin, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ### Part 1 -/

theorem contrasts : Contrasts := by
  intro J hJ S _ q U hK
  refine ⟨admissible hJ hK, omega_eq J hK, F_d J q U, E_d J q U, fun w θ => score_d J q U w θ,
    etfSup_d, fun θ h => maxE_neg h, fun θ h => maxE_pos h,
    ⟨_, box_mem J false (v := 0) (by simp), by norm_num [c0]⟩,
    ⟨_, box_mem J true (v := 0) (by simp), by simp [c1]⟩, Adv_wA, Gstar_d,
    fun θ h => maxF_pos h, fun θ h w hw ha => Adv_neg h hw ha, by simp [d0], by simp [d0],
    by simp [d1], by simp [d1], paired0, paired1, fun θ N hN i k => cov_hat hK θ hN i k⟩

/-! ### The Moore–Penrose inverse of `Ω = J J'` -/

section MP

variable (J : Matrix (Fin 3) (Fin 3) ℝ)

lemma ct_eq (A : Matrix (Fin 3) (Fin 3) ℝ) : Aᴴ = Aᵀ := Matrix.conjTranspose_eq_transpose_of_trivial A

lemma omega_herm : (J * Jᵀ).IsHermitian := by
  have := Matrix.isHermitian_mul_conjTranspose_self J
  rwa [ct_eq] at this

lemma omega_symm : (J * Jᵀ)ᵀ = J * Jᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]

lemma diag_mid (e : Fin 3 → ℝ) (i : Fin 3) : e i * (e i)⁻¹ * e i = e i := by
  by_cases h : e i = 0
  · simp [h]
  · field_simp

lemma mp_exists : ∃ G, IsMoorePenrose (J * Jᵀ) G := by
  have hA := omega_herm J
  have hs := hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  set W : Matrix (Fin 3) (Fin 3) ℝ := (hA.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ) with hW
  have h2 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hst : star W = Wᵀ := by rw [Matrix.star_eq_conjTranspose, ct_eq]
  set e : Fin 3 → ℝ := RCLike.ofReal ∘ hA.eigenvalues
  set D := diagonal e
  set Dp := diagonal fun i => (e i)⁻¹
  have hΩ : J * Jᵀ = W * D * star W := hs
  have cm : ∀ X Y : Matrix (Fin 3) (Fin 3) ℝ,
      (W * X * star W) * (W * Y * star W) = W * (X * Y) * star W := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star W) W, h2, Matrix.one_mul]
  have ct : ∀ X : Matrix (Fin 3) (Fin 3) ℝ, Xᵀ = X → (W * X * star W)ᵀ = W * X * star W := by
    intro X hX
    rw [hst, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX,
      Matrix.mul_assoc]
  have dT : ∀ f : Fin 3 → ℝ, (diagonal f)ᵀ = diagonal f := fun f => Matrix.diagonal_transpose f
  refine ⟨W * Dp * star W, ?_, ?_, ?_, ?_⟩
  · rw [hΩ, cm, cm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      show (fun i => e i * (e i)⁻¹ * e i) = e from funext (diag_mid e)]
  · rw [hΩ, cm, cm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      show (fun i => (e i)⁻¹ * e i * (e i)⁻¹) = fun i => (e i)⁻¹ from funext fun i => by
        by_cases h : e i = 0
        · simp [h]
        · field_simp]
  · rw [hΩ, cm, Matrix.diagonal_mul_diagonal]; exact ct _ (dT _)
  · rw [hΩ, cm, Matrix.diagonal_mul_diagonal]; exact ct _ (dT _)

lemma pinv_spec : (J * Jᵀ) * pinv (J * Jᵀ) * (J * Jᵀ) = J * Jᵀ :=
  (Classical.epsilon_spec (mp_exists J)).1

lemma eq_zero_of_mul_transpose (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M * Mᵀ = 0) : M = 0 := by
  ext i j
  have hi := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Matrix.zero_apply] at hi
  fin_cases j <;> simp <;> nlinarith [sq_nonneg (M i 0), sq_nonneg (M i 1), sq_nonneg (M i 2)]

/-- `J = Ω (Ω† J)`, so the range of `J` lies in the range of `Ω`. -/
lemma J_factor : (J * Jᵀ) * (pinv (J * Jᵀ) * J) = J := by
  have h1 := pinv_spec J
  have hs := omega_symm J
  set G := pinv (J * Jᵀ)
  have h1' : J * Jᵀ * Gᵀ * (J * Jᵀ) = J * Jᵀ := by
    have := congrArg Matrix.transpose h1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    simpa [Matrix.mul_assoc] using this
  have hT : (J * Jᵀ * (G * J) - J)ᵀ = Jᵀ * Gᵀ * (J * Jᵀ) - Jᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.mul_assoc]
  have hM : (J * Jᵀ * (G * J) - J) * (J * Jᵀ * (G * J) - J)ᵀ = 0 := by
    rw [hT]
    have e : (J * Jᵀ * (G * J) - J) * (Jᵀ * Gᵀ * (J * Jᵀ) - Jᵀ)
        = J * Jᵀ * G * (J * Jᵀ) * Gᵀ * (J * Jᵀ) - J * Jᵀ * G * (J * Jᵀ)
          - J * Jᵀ * Gᵀ * (J * Jᵀ) + J * Jᵀ := by noncomm_ring
    rw [e, h1, h1']
    abel
  exact sub_eq_zero.mp (eq_zero_of_mul_transpose _ hM)

lemma dot_self_nonneg (w : Fin 3 → ℝ) : 0 ≤ w ⬝ᵥ w := by
  rw [dot3]; nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]

lemma dot_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma quad_omega (x : Fin 3 → ℝ) :
    ((J * Jᵀ) *ᵥ x) ⬝ᵥ (pinv (J * Jᵀ) *ᵥ ((J * Jᵀ) *ᵥ x)) = (Jᵀ *ᵥ x) ⬝ᵥ (Jᵀ *ᵥ x) := by
  rw [Novel.M4BoundedLawRateProof.quad_range (omega_symm J) (pinv_spec J), ← Matrix.mulVec_mulVec,
    dot_mulVec, Matrix.transpose_transpose]

/-- Every `J u` lies in `Im Ω`, with `e' Ω† e ≤ ‖u‖²`. -/
lemma J_range (u : Fin 3 → ℝ) : ∃ x, J *ᵥ u = (J * Jᵀ) *ᵥ x ∧
    (Jᵀ *ᵥ x) ⬝ᵥ (Jᵀ *ᵥ x) ≤ u ⬝ᵥ u := by
  set x := (pinv (J * Jᵀ) * J) *ᵥ u
  have hx : J *ᵥ u = (J * Jᵀ) *ᵥ x := by
    rw [Matrix.mulVec_mulVec, J_factor]
  refine ⟨x, hx, ?_⟩
  set y := Jᵀ *ᵥ x
  have hz : J *ᵥ (u - y) = 0 := by
    rw [Matrix.mulVec_sub, hx, show J *ᵥ y = (J * Jᵀ) *ᵥ x from Matrix.mulVec_mulVec _ _ _,
      sub_self]
  have hcross : y ⬝ᵥ (u - y) = 0 := by
    rw [show y = Jᵀ *ᵥ x from rfl, dot_mulVec, Matrix.transpose_transpose, hz, dotProduct_zero]
  have : u ⬝ᵥ u = y ⬝ᵥ y + 2 * (y ⬝ᵥ (u - y)) + (u - y) ⬝ᵥ (u - y) := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm y u]; ring
  rw [this, hcross]
  nlinarith [dot_self_nonneg (u - y)]

lemma cs3 (a b : Fin 3 → ℝ) : (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  simp only [dotProduct]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simpa [sq] using this

/-- `|d' e| ≤ σ_d √(e' Ω† e)` for `e = Ω x`. -/
lemma dir_bound (d x : Fin 3 → ℝ) :
    |d ⬝ᵥ ((J * Jᵀ) *ᵥ x)| ≤ Real.sqrt (sig2 J d) *
      Real.sqrt (((J * Jᵀ) *ᵥ x) ⬝ᵥ (pinv (J * Jᵀ) *ᵥ ((J * Jᵀ) *ᵥ x))) := by
  have e1 : d ⬝ᵥ ((J * Jᵀ) *ᵥ x) = (Jᵀ *ᵥ d) ⬝ᵥ (Jᵀ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_comm, dot_mulVec, dotProduct_comm]
  have e2 : sig2 J d = (Jᵀ *ᵥ d) ⬝ᵥ (Jᵀ *ᵥ d) := by
    rw [sig2, ← Matrix.mulVec_mulVec, dotProduct_comm, dot_mulVec]
  rw [e1, e2, quad_omega, ← Real.sqrt_mul (dot_self_nonneg _)]
  exact Real.abs_le_sqrt (cs3 _ _)

end MP

/-! ### M4's discrete quantile (generic) -/

section Quantile

variable {S : Type} [Fintype S] (D : Data 1 1 2 S) (hq : ∀ s, 0 ≤ D.q s) (hq1 : ∑ s, D.q s = 1)
include hq hq1

lemma mass_nonneg {N : ℕ} (σ : Fin N → S) : 0 ≤ mass D σ := Finset.prod_nonneg fun _ _ => hq _

lemma tq_mem (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ tcrit D N ε then mass D σ else 0 := by
  set T := {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
    1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} with hT
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := Novel.M4BoundedLawRateProof.mass_sum D hq1 N
  have hmass := mass_nonneg D hq hq1 (N := N)
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 := by
    by_contra h
    have : ∑ σ : Fin N → S, mass D σ ≤ 0 :=
      Finset.sum_nonpos fun σ _ => not_lt.mp fun hp => h ⟨σ, hp⟩
    linarith
  have hfin : T.Finite := (Set.finite_range (TN D)).subset fun t ht => by
    obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ) (TN D) ⟨σ0, by simp [hσ0]⟩
  have hne : T.Nonempty := by
    refine ⟨TN D σm, ⟨σm, (Finset.mem_filter.mp hσm).2, rfl⟩, ?_⟩
    have e : ∑ σ : Fin N → S, (if TN D σ ≤ TN D σm then mass D σ else 0) = 1 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rcases (hmass σ).lt_or_eq with h | h
      · have := hmax σ (by simp [h])
        split_ifs with hc
        · rfl
        · exact absurd this hc
      · rw [← h]; split_ifs <;> rfl
    linarith
  exact (hne.csInf_mem hfin).2

lemma tq_le (N : ℕ) {ε : ℝ} (hε1 : ε < 1) (Pσ : (Fin N → S) → Prop) [DecidablePred Pσ] (T0 : ℝ)
    (hP : 1 - ε ≤ ∑ σ : Fin N → S, if Pσ σ then mass D σ else 0)
    (hPT : ∀ σ, Pσ σ → TN D σ ≤ T0) : tcrit D N ε ≤ T0 := by
  have hmass := mass_nonneg D hq hq1 (N := N)
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 ∧ Pσ σ0 := by
    by_contra h
    have : ∑ σ : Fin N → S, (if Pσ σ then mass D σ else 0) ≤ 0 :=
      Finset.sum_nonpos fun σ _ => by
        split_ifs with h'
        · exact not_lt.mp fun hp => h ⟨σ, hp, h'⟩
        · exact le_rfl
    linarith
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ ∧ Pσ σ) (TN D) ⟨σ0, by simp [hσ0]⟩
  have hσm' := (Finset.mem_filter.mp hσm).2
  have hmemT : TN D σm ∈ {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} := by
    refine ⟨⟨σm, hσm'.1, rfl⟩, le_trans hP (Finset.sum_le_sum fun σ _ => ?_)⟩
    by_cases h : Pσ σ
    · rcases (hmass σ).lt_or_eq with hp | hp
      · have := hmax σ (by simp [hp, h])
        simp only [h, this, ↓reduceIte, le_refl]
      · rw [← hp]; split_ifs <;> exact le_rfl
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith [hmass σ]
  have hbdd : BddBelow {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} :=
    ((Set.finite_range (TN D)).subset fun t ht => by
      obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩).bddBelow
  exact (csInf_le hbdd hmemT).trans (hPT σm hσm'.2)

end Quantile

/-! ### A variance-based tail bound on finite histories -/

section TailV

variable {S : Type} [Fintype S] {q : S → ℝ} {Y : S → ℝ}

lemma mgfV (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0)
    (h2 : ∑ s, q s * Y s ^ 2 = 1) (hb : ∀ s, Y s ^ 2 ≤ 81) {t : ℝ} (ht : |t| ≤ 1 / 9) :
    ∑ s, q s * Real.exp (t * Y s) ≤ Real.exp (t ^ 2) := by
  have ht2 : t ^ 2 ≤ 1 / 81 := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have each : ∀ s, Real.exp (t * Y s) ≤ 1 + t * Y s + t ^ 2 * Y s ^ 2 := by
    intro s
    have hx : |t * Y s| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one, mul_pow]; nlinarith [hb s, sq_nonneg t, sq_nonneg (Y s)]
    have := Real.abs_exp_sub_one_sub_id_le hx
    rw [mul_pow] at this
    linarith [(abs_le.mp this).2]
  calc ∑ s, q s * Real.exp (t * Y s) ≤ ∑ s, q s * (1 + t * Y s + t ^ 2 * Y s ^ 2) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (each s) (hq s)
    _ = 1 + t ^ 2 := by
        have e : ∀ s, q s * (1 + t * Y s + t ^ 2 * Y s ^ 2)
            = q s + t * (q s * Y s) + t ^ 2 * (q s * Y s ^ 2) := fun s => by ring
        simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hq1, h0, h2]; ring
    _ ≤ Real.exp (t ^ 2) := by linarith [Real.add_one_le_exp (t ^ 2)]

lemma chernoffV (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0)
    (h2 : ∑ s, q s * Y s ^ 2 = 1) (hb : ∀ s, Y s ^ 2 ≤ 81) (N : ℕ) {a : ℝ} (ha : 0 < a)
    (ha2 : a ≤ 2 / 9) :
    ∑ σ : Fin N → S, (if (N : ℝ) * a ≤ ∑ l, Y (σ l) then ∏ l, q (σ l) else 0)
      ≤ Real.exp (-(N * a ^ 2) / 4) := by
  set t := a / 2 with ht
  have ht0 : 0 < t := by positivity
  have htb : |t| ≤ 1 / 9 := by rw [abs_of_pos ht0]; linarith
  calc ∑ σ : Fin N → S, (if (N : ℝ) * a ≤ ∑ l, Y (σ l) then ∏ l, q (σ l) else 0)
      ≤ ∑ σ : Fin N → S, (∏ l, q (σ l)) * Real.exp (t * (∑ l, Y (σ l) - N * a)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun l _ => hq _
        split_ifs with h
        · have : 1 ≤ Real.exp (t * (∑ l, Y (σ l) - N * a)) :=
            Real.one_le_exp (mul_nonneg ht0.le (by linarith))
          nlinarith
        · positivity
    _ = Real.exp (-(t * N * a)) * ∏ _l : Fin N, ∑ s, q s * Real.exp (t * Y s) := by
        rw [Fintype.prod_sum (fun _ : Fin N => fun s => q s * Real.exp (t * Y s)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_mul_distrib, mul_sub, Finset.mul_sum, Real.exp_sub, Real.exp_sum,
          div_eq_mul_inv, ← Real.exp_neg]
        ring_nf
    _ ≤ Real.exp (-(t * N * a)) * ∏ _l : Fin N, Real.exp (t ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun l _ => Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (Real.exp_pos _).le)
          (fun l _ => mgfV hq hq1 h0 h2 hb htb)) (Real.exp_pos _).le
    _ = Real.exp (-(N * a ^ 2) / 4) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul,
          ← Real.exp_add]
        congr 1
        rw [ht]
        ring

lemma tailV (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0)
    (h2 : ∑ s, q s * Y s ^ 2 = 1) (hb : ∀ s, Y s ^ 2 ≤ 81) {N : ℕ} (hN : 0 < N) {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2 / 9) :
    ∑ σ : Fin N → S, (if a ≤ |(1 / (N : ℝ)) * ∑ l, Y (σ l)| then ∏ l, q (σ l) else 0)
      ≤ 2 * Real.exp (-(N * a ^ 2) / 4) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := chernoffV hq hq1 h0 h2 hb N ha ha2
  have h2' := chernoffV (Y := fun s => -Y s) hq hq1 (by simp [h0])
    (by simpa using h2) (fun s => by simpa using hb s) N ha ha2
  calc _ ≤ ∑ σ : Fin N → S, ((if (N : ℝ) * a ≤ ∑ l, Y (σ l) then ∏ l, q (σ l) else 0)
          + (if (N : ℝ) * a ≤ ∑ l, -Y (σ l) then ∏ l, q (σ l) else 0)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun l _ => hq _
        rw [Finset.sum_neg_distrib]
        by_cases h : a ≤ |(1 / (N : ℝ)) * ∑ l, Y (σ l)|
        · simp only [h, ↓reduceIte]
          rcases le_abs'.mp h with h' | h'
          · have : (N : ℝ) * a ≤ -∑ l, Y (σ l) := by
              rw [one_div, inv_mul_le_iff₀ hNr] at h'; linarith
            simp only [this, ↓reduceIte]; split_ifs <;> linarith
          · have : (N : ℝ) * a ≤ ∑ l, Y (σ l) := by rw [one_div, le_inv_mul_iff₀ hNr] at h'; linarith
            simp only [this, ↓reduceIte]; split_ifs <;> linarith
        · simp only [h, ↓reduceIte]; split_ifs <;> linarith
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

end TailV

/-! ### Parts 2 (upper) and 3: the directional certificate -/

section Cert

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}
  (hK : InKJ q U)
include hK

lemma rN_nonneg {N : ℕ} {ε : ℝ} : 0 ≤ rN (data J q U) N ε := Real.sqrt_nonneg _

/-- Every error in `A_{N,ε}` satisfies `|d'e| ≤ σ_d r_N`. -/
lemma A_dir {N : ℕ} (hN : 0 < N) {ε : ℝ} {e : Fin 3 → ℝ} (he : e ∈ Aset (data J q U) N ε)
    (d : Fin 3 → ℝ) : |d ⬝ᵥ e| ≤ Real.sqrt (sig2 J d) * rN (data J q U) N ε := by
  obtain ⟨⟨x, rfl⟩, hq⟩ := he
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [omega_eq J hK] at hq ⊢
  refine (dir_bound J d x).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [rN]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hNr]
  linarith

lemma C_lower {N : ℕ} (hN : 0 < N) {ε : ℝ} {th θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset (data J q U) (V4 J) N ε th) (d : Fin 3 → ℝ) :
    d ⬝ᵥ th - Real.sqrt (sig2 J d) * rN (data J q U) N ε ≤ d ⬝ᵥ θ := by
  obtain ⟨-, e, he, rfl⟩ := hθ
  rw [dotProduct_sub]
  linarith [(abs_le.mp (A_dir hK hN he d)).2]

lemma ell_le_Adv {N : ℕ} (hN : 0 < N) {ε : ℝ} {H : Fin N → Record 1} {θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) H)) :
    ellJ J (data J q U) ε H ≤ Adv (data J q U) wA θ := by
  rw [Adv_wA, ellJ]
  have h0 := C_lower hK hN hθ d0
  have h1 := C_lower hK hN hθ d1
  exact min_le_min (by linarith) (by linarith)

lemma ell_cov {N : ℕ} (hN : 0 < N) {ε : ℝ} {H : Fin N → Record 1} {θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) H)) :
    min (d0 ⬝ᵥ θ - 2 * rN (data J q U) N ε * Real.sqrt (sig2 J d0))
        (d1 ⬝ᵥ θ - 2 * rN (data J q U) N ε * Real.sqrt (sig2 J d1))
      ≤ ellJ J (data J q U) ε H := by
  obtain ⟨-, e, he, hθe⟩ := hθ
  have hth : thetaHat (data J q U) H = θ + e := by rw [hθe]; abel
  rw [ellJ, hth]
  have b0 := (abs_le.mp (A_dir hK hN he d0)).1
  have b1 := (abs_le.mp (A_dir hK hN he d1)).1
  rw [dotProduct_add, dotProduct_add]
  exact min_le_min (by linarith) (by linarith)

lemma plugin_wA {N : ℕ} {ε δ : ℝ} (hδ : 0 ≤ δ) {H : Fin N → Record 1}
    (h : δ / 4 < ellJ J (data J q U) ε H) : wHatF (data J q U) (thetaHat (data J q U) H) = wA := by
  have hr := rN_nonneg (J := J) hK (N := N) (ε := ε)
  have h0 := mul_nonneg hr (Real.sqrt_nonneg (sig2 J d0))
  have h1 := mul_nonneg hr (Real.sqrt_nonneg (sig2 J d1))
  rw [ellJ, lt_min_iff] at h
  rw [wHatF, maxF_pos (lt_min (by rw [mul_comm] at h0; linarith [h.1])
    (by rw [mul_comm] at h1; linarith [h.2])), Novel.M4BoundedLawRateProof.lexSel_singleton]

omit hK in
lemma errN_J {N : ℕ} (σ : Fin N → S) :
    errN (data J q U) σ = J *ᵥ fun c => (1 / (N : ℝ)) * ∑ l, U (σ l) c := by
  funext i
  rw [errN_d]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- `t_{N,ε} ≤ 12 log(6/ε)` once `N ≥ 81 log(6/ε)`. -/
lemma tcrit_12 {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hNb : 81 * Real.log (6 / ε) ≤ N) : tcrit (data J q U) N ε ≤ 12 * Real.log (6 / ε) := by
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
  set D := data J q U
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun _ _ => hq _
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := Novel.M4BoundedLawRateProof.mass_sum D hq1 N
  let Ub : (Fin N → S) → Fin 3 → ℝ := fun σ c => (1 / (N : ℝ)) * ∑ l, U (σ l) c
  have htail : ∀ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ub σ c| then mass D σ else 0) ≤ ε / 3 := by
    intro c
    have h := tailV (Y := fun s => U s c) hq hq1 (hU0 c)
      (by simpa [sq] using hU2 c c) (fun s => (coord_sq_le (U s) c).trans (hU s)) hN ha ha29
    have e : 2 * Real.exp (-(N * a ^ 2) / 4) = ε / 3 := by
      rw [ha2]
      have : -((N : ℝ) * (4 * L / N)) / 4 = -L := by field_simp
      rw [this, Real.exp_neg, hLdef, Real.exp_log (by positivity)]
      field_simp
      norm_num
    rw [← e]
    exact h
  have hP : 1 - ε ≤ ∑ σ : Fin N → S, (if ∀ c, |Ub σ c| < a then mass D σ else 0) := by
    have hle : ∀ σ : Fin N → S, mass D σ - (if ∀ c, |Ub σ c| < a then mass D σ else 0)
        ≤ ∑ c : Fin 3, (if a ≤ |Ub σ c| then mass D σ else 0) := by
      intro σ
      split_ifs with h
      · rw [sub_self]
        exact Finset.sum_nonneg fun c _ => by split_ifs <;> linarith [hmass σ]
      · rw [sub_zero]
        obtain ⟨c, hc⟩ := not_forall.mp h
        have hc' : a ≤ |Ub σ c| := not_lt.mp hc
        calc mass D σ = (if a ≤ |Ub σ c| then mass D σ else 0) := by simp [hc']
          _ ≤ _ := Finset.single_le_sum (f := fun c => if a ≤ |Ub σ c| then mass D σ else 0)
              (fun c _ => by split_ifs <;> linarith [hmass σ]) (Finset.mem_univ c)
    have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hle σ
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_comm] at this
    have h3 : ∑ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ub σ c| then mass D σ else 0) ≤ ε := by
      calc _ ≤ ∑ _c : Fin 3, ε / 3 := Finset.sum_le_sum fun c _ => htail c
        _ = ε := by simp; ring
    linarith
  refine tq_le D hq hq1 N hε1 _ _ hP fun σ hσ => ?_
  obtain ⟨x, hx, hxb⟩ := J_range J (Ub σ)
  have hTN : TN D σ = N * ((J * Jᵀ) *ᵥ x ⬝ᵥ (pinv (J * Jᵀ) *ᵥ ((J * Jᵀ) *ᵥ x))) := by
    rw [TN, errN_J, show (fun c => (1 / (N : ℝ)) * ∑ l, U (σ l) c) = Ub σ from rfl, hx,
      omega_eq J hK]
  rw [hTN, quad_omega]
  have hUb : Ub σ ⬝ᵥ Ub σ ≤ 3 * a ^ 2 := by
    rw [dot3]
    have := fun c => (sq_lt_sq' (abs_lt.mp (hσ c)).1 (abs_lt.mp (hσ c)).2).le
    nlinarith [this 0, this 1, this 2]
  calc (N : ℝ) * ((Jᵀ *ᵥ x) ⬝ᵥ (Jᵀ *ᵥ x)) ≤ N * (3 * a ^ 2) :=
        mul_le_mul_of_nonneg_left (hxb.trans hUb) hNr.le
    _ = 12 * L := by rw [ha2]; field_simp; ring

/-- Under the sufficient length, `2 r_N σ ≤ δ/2`. -/
lemma rN_small {δ ε : ℝ} (hδ : 0 < δ) (hδσ : δ ≤ sigma J / 8) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    {N : ℕ} (hNb : 192 * (sigma J ^ 2 / δ ^ 2) * Real.log (6 / ε) ≤ N) :
    0 < N ∧ 81 * Real.log (6 / ε) ≤ N ∧ 2 * rN (data J q U) N ε * sigma J ≤ δ / 2 := by
  have hσ : 0 < sigma J := by linarith
  have hL : 0 < Real.log (6 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have h64 : 64 ≤ sigma J ^ 2 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hN81 : 81 * Real.log (6 / ε) ≤ N := le_trans (by nlinarith) hNb
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN81
  have hN : 0 < N := by exact_mod_cast hNr
  refine ⟨hN, hN81, ?_⟩
  have ht := tcrit_12 (J := J) hK hN hε (by linarith) hN81
  have hr : rN (data J q U) N ε ≤ δ / (4 * sigma J) := by
    rw [rN]
    calc Real.sqrt (tcrit (data J q U) N ε / N) ≤ Real.sqrt ((δ / (4 * sigma J)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ hNr]
          have e : (δ / (4 * sigma J)) ^ 2 * (192 * (sigma J ^ 2 / δ ^ 2) * Real.log (6 / ε))
              = 12 * Real.log (6 / ε) := by field_simp; ring
          nlinarith [mul_le_mul_of_nonneg_left hNb (sq_nonneg (δ / (4 * sigma J)))]
      _ = δ / (4 * sigma J) := Real.sqrt_sq (by positivity)
  have : rN (data J q U) N ε * sigma J ≤ δ / 4 := by
    calc rN (data J q U) N ε * sigma J ≤ δ / (4 * sigma J) * sigma J :=
          mul_le_mul_of_nonneg_right hr hσ.le
      _ = δ / 4 := by field_simp
  linarith

lemma ell_half {δ ε : ℝ} (hδ : 0 < δ) (hδσ : δ ≤ sigma J / 8) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    {N : ℕ} (hNb : 192 * (sigma J ^ 2 / δ ^ 2) * Real.log (6 / ε) ≤ N) {H : Fin N → Record 1}
    {θ : Fin 3 → ℝ} (hθ : θ ∈ Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) H))
    (hG : δ ≤ Gstar (data J q U) θ) : δ / 2 ≤ ellJ J (data J q U) ε H := by
  obtain ⟨hN, -, hsmall⟩ := rN_small hK hδ hδσ hε hε1 hNb
  have hc := ell_cov hK hN hθ
  rw [Gstar_d] at hG
  have hm : δ ≤ min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := by
    rcases le_total (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) 0 with h | h
    · rw [max_eq_left h] at hG; linarith
    · rwa [max_eq_right h] at hG
  have hr := rN_nonneg (J := J) hK (N := N) (ε := ε)
  have s0 : Real.sqrt (sig2 J d0) ≤ sigma J := le_max_left _ _
  have s1 : Real.sqrt (sig2 J d1) ≤ sigma J := le_max_right _ _
  have k0 := mul_le_mul_of_nonneg_left s0 (by positivity : (0 : ℝ) ≤ 2 * rN (data J q U) N ε)
  have k1 := mul_le_mul_of_nonneg_left s1 (by positivity : (0 : ℝ) ≤ 2 * rN (data J q U) N ε)
  have hm0 := (le_min_iff.mp hm).1
  have hm1 := (le_min_iff.mp hm).2
  refine le_trans (le_min ?_ ?_) hc <;> linarith

end Cert

/-- M4's plug-in fallback always lies in the ETF-only class. -/
lemma vHatE_mem {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} (th : Fin 3 → ℝ) : vHatE (data J q U) th ∈ E (data J q U) := by
  rcases lt_trichotomy (th 1) 0 with h | h | h
  · rw [vHatE, maxE_neg h, Novel.M4BoundedLawRateProof.lexSel_singleton]; exact zero_mem_E
  · have hM : maximizers (fun v => score (data J q U) v (toPar th)) (E (data J q U))
        = E (data J q U) := by
      ext w
      simp only [maximizers, Set.mem_ofPred_eq]
      refine ⟨fun hw => hw.1, fun hw => ⟨hw, fun v hv => ?_⟩⟩
      rw [E_d] at hv hw
      simp only [score_d, hv.1, hw.1, h]; simp
    have hex : ∃ w, w ∈ E (data J q U) ∧ ∀ v ∈ E (data J q U), LexLE w v := by
      refine ⟨0, zero_mem_E, fun v hv => ?_⟩
      rw [E_d] at hv
      obtain ⟨ha, hp, -⟩ := hv
      rcases hp.lt_or_eq with hp | hp
      · refine Or.inr ⟨Sum.inr 0, fun j hj => ?_, by simpa using hp⟩
        rcases j with k | k
        · obtain rfl : k = 0 := Subsingleton.elim _ _; simp [ha]
        · simp [Standalone.M4InformationObstruction.lexIdx] at hj
      · refine Or.inl ?_
        rw [inst_ext v, ha, ← hp]; funext i; rcases i with k | k <;> rfl
    rw [vHatE, hM]
    exact (Classical.epsilon_spec hex).1
  · rw [vHatE, maxE_pos h, Novel.M4BoundedLawRateProof.lexSel_singleton]; exact etf1_mem_E

lemma errN_range {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} (hK : InKJ q U) {N : ℕ} (σ : Fin N → S) :
    errN (data J q U) σ ∈ Set.range (Omega (data J q U)).mulVec := by
  obtain ⟨x, hx, -⟩ := J_range J (fun c => (1 / (N : ℝ)) * ∑ l, U (σ l) c)
  rw [omega_eq J hK, errN_J, hx]
  exact ⟨x, rfl⟩

theorem directionalCertificate : DirectionalCertificate := by
  intro J S _ q U hK N ε δ hN hε hδ
  refine ⟨fun H hne => ?_, fun H h => plugin_wA hK hδ h, fun θ hθ σ hC => ell_cov hK hN hC,
    fun hδ' hδσ hε16 hNb θ hθ hG σ hC => ell_half hK hδ' hδσ hε hε16 hNb hC hG⟩
  rw [LN]
  simp only [hne.ne_empty, ↓reduceIte]
  exact le_iInf₂ fun θ hθ => EReal.coe_le_coe_iff.mpr (ell_le_Adv hK hN hθ)

theorem upperBound : UpperBound := by
  intro J δ ε hδ hδσ hε hε1 S _ q U hK N hNb
  obtain ⟨hN, -, -⟩ := rN_small hK hδ hδσ hε hε1 hNb
  set D := data J q U with hD
  have hq := hK.1
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => mass_nonneg D hq hK.2.1 σ
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := Novel.M4BoundedLawRateProof.mass_sum D hK.2.1 N
  have hcov : 1 - ε ≤ ∑ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then mass D σ else 0) := by
    refine le_trans (tq_mem D hq hK.2.1 N hε.le) (Finset.sum_le_sum fun σ _ => ?_)
    by_cases h : TN D σ ≤ tcrit D N ε
    · have hA : errN D σ ∈ Aset D N ε := ⟨errN_range hK σ, h⟩
      simp only [h, hA, ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith [hmass σ]
  have hCmem : ∀ θ, ∀ σ : Fin N → S, errN D σ ∈ Aset D N ε → θ ∈ Theta4 (V4 J) →
      θ ∈ Cset D (V4 J) N ε (thetaHat D (hist D θ σ)) := fun θ σ he hθ =>
    ⟨hθ, errN D σ, he, by rw [thetaHat_hist hN, add_sub_cancel_right]⟩
  have hvE : ∀ th, vHatE D th (Sum.inl 0) = 0 := fun th => by
    have := vHatE_mem (J := J) (q := q) (U := U) th
    rw [E_d] at this; exact this.1
  refine ⟨fun H => ?_, fun θ hθ => ?_, fun θ hθ hG => ?_⟩
  · -- the rule certifies `w_A` or falls back to an ETF-only action
    show Measure.dirac (if certJ J D δ ε H then wA else vHatE D (thetaHat D H)) _ = 0
    rw [Measure.dirac_apply]
    by_cases hc : certJ J D δ ε H
    · simp only [hc, ↓reduceIte]
      exact Set.indicator_of_notMem (fun h => h.1 ⟨wA_mem_F, by simp [wA]⟩) _
    · simp only [hc, ↓reduceIte]
      exact Set.indicator_of_notMem (fun h => h.2 (vHatE_mem _)) _
  · -- uniform false-certification control
    calc falseP D δ θ (gateJ J D N δ ε)
        ≤ ∑ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then 0 else mass D σ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          show mass D σ * (Measure.dirac (if certJ J D δ ε (hist D θ σ) then wA
            else vHatE D (thetaHat D (hist D θ σ))) _).toReal ≤ _
          rw [Novel.M4BoundedLawRateProof.dirac_toReal]
          by_cases he : errN D σ ∈ Aset D N ε
          · by_cases hc : certJ J D δ ε (hist D θ σ)
            · have hA : wA ∉ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δ / 4} :=
                fun h => by
                  have := ell_le_Adv hK hN (hCmem θ σ he hθ)
                  linarith [h.2, hc.2.2]
              simp [hc, hA, he]
            · have hE : vHatE D (thetaHat D (hist D θ σ)) ∉
                  {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ δ / 4} :=
                fun h => by have := h.1; rw [hvE] at this; exact lt_irrefl _ this
              simp [hc, hE, he]
          · simp only [he, ↓reduceIte]
            split_ifs <;> linarith [hmass σ]
      _ ≤ ε := by
          have e : ∀ σ : Fin N → S, (if errN D σ ∈ Aset D N ε then 0 else mass D σ)
              = mass D σ - (if errN D σ ∈ Aset D N ε then mass D σ else 0) := fun σ => by
            split_ifs <;> ring
          simp only [e, Finset.sum_sub_distrib, hsum]
          linarith
  · -- uniform power
    refine le_trans hcov (Finset.sum_le_sum fun σ _ => ?_)
    show _ ≤ mass D σ * (Measure.dirac (if certJ J D δ ε (hist D θ σ) then wA
      else vHatE D (thetaHat D (hist D θ σ))) _).toReal
    rw [Novel.M4BoundedLawRateProof.dirac_toReal]
    by_cases he : errN D σ ∈ Aset D N ε
    · have hC := hCmem θ σ he hθ
      have hh := ell_half hK hδ hδσ hε hε1 hNb hC hG
      have hc : certJ J D δ ε (hist D θ σ) :=
        ⟨⟨θ, hC⟩, plugin_wA (ε := ε) hK hδ.le (by linarith), by linarith⟩
      have hA : wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv D w θ} := by
        refine ⟨by simp [wA], ?_⟩
        rw [Adv_wA]
        rw [Gstar_d] at hG
        rcases le_total (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) 0 with h | h
        · rw [max_eq_left h] at hG; linarith
        · rw [max_eq_right h] at hG; linarith
      simp [hc, hA, he]
    · simp only [he, ↓reduceIte]
      split_ifs <;> linarith [hmass σ]

/-! ### Part 2, lower bound: the hard grid's variance -/

section Grid

open Novel.M4BoundedLawRateProof (phi Sm qh Zh qh_pos qh_sum qh_centered u_pos u_refl phi_pos
  phi_mul Sm_pos)

local notation "uu" => Novel.M4BoundedLawRateProof.u

lemma sum_range_real (n : ℕ) : ∑ m ∈ Finset.range n, (m : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_sq_range (n : ℕ) : ∑ m ∈ Finset.range n, (m : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_centered_sq (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), ((m : ℝ) - k) ^ 2 = k * (k + 1) * (2 * k + 1) / 3 := by
  have e : ∀ m : ℕ, ((m : ℝ) - k) ^ 2 = (m : ℝ) ^ 2 - 2 * k * m + (k : ℝ) ^ 2 := fun m => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sq_range,
    sum_range_real, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

variable {k : ℕ} (hk : 2 ≤ k)
include hk

lemma kk_add : 4 * k - 2 + 2 = 4 * k := by omega

lemma phi_kk : phi (4 * k - 2) = Real.pi / (4 * k) := by
  unfold phi; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma u_sq_half {n : ℕ} (h1 : k ≤ n) (h2 : n ≤ 3 * k) : 1 / 2 ≤ uu (4 * k - 2) n ^ 2 := by
  have hpi := Real.pi_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have key : ∀ m : ℕ, k ≤ m → m ≤ 2 * k → 1 / 2 ≤ uu (4 * k - 2) m ^ 2 := by
    intro m hm1 hm2
    simp only [Novel.M4BoundedLawRateProof.u, phi_kk hk]
    have hx1 : Real.pi / 4 ≤ m * (Real.pi / (4 * k)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have : (k : ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith
    have hx2 : m * (Real.pi / (4 * k)) ≤ Real.pi / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm2
      nlinarith
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx2 hx1
    rw [Real.sin_pi_div_four] at hs
    have hs0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [← h2]
    exact pow_le_pow_left₀ hs0 hs 2
  by_cases hn : n ≤ 2 * k
  · exact key n h1 hn
  · have hr := u_refl (4 * k - 2) (n := n) (by omega)
    rw [← hr]
    exact key _ (by omega) (by omega)

/-- The centered grid `z_i = i + 1 - 2k`. -/
def zv (k : ℕ) (i : Fin (4 * k - 2 + 1)) : ℝ := (i : ℝ) + 1 - 2 * k

omit hk in
/-- The grid variance `V = Σ q_i z_i²`. -/
def Vg (k : ℕ) : ℝ := ∑ i, qh (4 * k - 2) i * zv k i ^ 2

lemma zv_abs (i : Fin (4 * k - 2 + 1)) : zv k i ^ 2 ≤ (2 * k) ^ 2 := by
  have hi : (i : ℝ) ≤ 4 * k - 2 := by
    have := Nat.lt_succ_iff.mp i.isLt
    have : ((i : ℕ) : ℝ) ≤ ((4 * k - 2 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  simp only [zv]
  nlinarith

lemma Vg_le : Vg k ≤ 4 * k ^ 2 := by
  calc Vg k ≤ ∑ i, qh (4 * k - 2) i * (2 * k) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (zv_abs hk i) (qh_pos _ i).le
    _ = 4 * k ^ 2 := by rw [← Finset.sum_mul, qh_sum]; ring

lemma Vg_ge : (k : ℝ) ^ 2 / 12 ≤ Vg k := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set K := 4 * k - 2
  have hSm : Sm K ≤ 4 * k - 1 := by
    calc Sm K ≤ ∑ _i : Fin (K + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            rw [Novel.M4BoundedLawRateProof.u, sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
      _ = 4 * k - 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [show K + 1 = 4 * k - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
  have hSm0 := Sm_pos K
  -- the weighted sum over the middle band
  let f : ℕ → ℝ := fun i => uu K (i + 1) ^ 2 * ((i : ℝ) + 1 - 2 * k) ^ 2
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsum : ∑ i : Fin (K + 1), f i = Vg k * Sm K := by
    simp only [Vg, qh, zv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Sm (4 * k - 2) = Sm K from rfl]
    simp only [f]
    field_simp
    exact mul_comm _ _
  have hband : ∑ m ∈ Finset.range (2 * k + 1), (1 / 2) * ((m : ℝ) - k) ^ 2
      ≤ ∑ i : Fin (K + 1), f i := by
    rw [Fin.sum_univ_eq_sum_range f (K + 1)]
    calc ∑ m ∈ Finset.range (2 * k + 1), (1 / 2) * ((m : ℝ) - k) ^ 2
        ≤ ∑ m ∈ Finset.range (2 * k + 1), f (m + (k - 1)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_range.mp hm
          simp only [f]
          have hcast : ((m + (k - 1) : ℕ) : ℝ) + 1 - 2 * k = (m : ℝ) - k := by
            rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
          rw [hcast, show m + (k - 1) + 1 = m + k by omega]
          exact mul_le_mul_of_nonneg_right (u_sq_half hk (by omega) (by omega)) (sq_nonneg _)
      _ = ∑ i ∈ (Finset.range (2 * k + 1)).image (· + (k - 1)), f i := by
          rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
      _ ≤ ∑ i ∈ Finset.range (K + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hi
            have := Finset.mem_range.mp hm
            exact Finset.mem_range.mpr (by omega)) (fun i _ _ => hf0 i)
  rw [← Finset.mul_sum, sum_centered_sq] at hband
  rw [hsum] at hband
  have h3 : (k : ℝ) ^ 3 / 3 ≤ Vg k * Sm K := by nlinarith
  have hV0 : 0 ≤ Vg k := Finset.sum_nonneg fun i _ => mul_nonneg (qh_pos _ i).le (sq_nonneg _)
  have : (k : ℝ) ^ 3 / 3 ≤ Vg k * (4 * k - 1) := h3.trans (mul_le_mul_of_nonneg_left hSm hV0)
  nlinarith

end Grid

/-! ### Part 2, lower bound: an orthogonal completion and the latent law -/

section Orth

/-- `e₀ = (1, 0, 0)`. -/
def e0 : Fin 3 → ℝ := ![1, 0, 0]

/-- The Householder reflection sending `e₀` to the unit vector `h`. -/
def hhm (h : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if h 0 = 1 then 1 else 1 - (2 / ((e0 - h) ⬝ᵥ (e0 - h))) • vecMulVec (e0 - h) (e0 - h)

variable {h : Fin 3 → ℝ} (hu : h ⬝ᵥ h = 1)
include hu

lemma unit_e0 (h0 : h 0 = 1) : h = e0 := by
  rw [dot3] at hu
  have h1 : h 1 = 0 := by nlinarith [sq_nonneg (h 1), sq_nonneg (h 2)]
  have h2 : h 2 = 0 := by nlinarith [sq_nonneg (h 1), sq_nonneg (h 2)]
  funext i; fin_cases i <;> simp [e0, h0, h1, h2]

lemma vv_pos (h0 : h 0 ≠ 1) : 0 < (e0 - h) ⬝ᵥ (e0 - h) := by
  rw [dot3] at hu ⊢
  simp only [e0, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  have hle : h 0 ≤ 1 := by nlinarith [sq_nonneg (h 1), sq_nonneg (h 2), sq_nonneg (h 0 - 1)]
  have hlt : 0 < 1 - h 0 := sub_pos.mpr (lt_of_le_of_ne hle h0)
  nlinarith [mul_pos hlt hlt, sq_nonneg (h 1), sq_nonneg (h 2)]

lemma vv_eq : (e0 - h) ⬝ᵥ (e0 - h) = 2 * (1 - h 0) := by
  rw [dot3] at hu ⊢; simp [e0]; nlinarith

lemma hhm_col : hhm h *ᵥ e0 = h := by
  by_cases h0 : h 0 = 1
  · simp [hhm, unit_e0 hu h0]
  · have h1 : (1 : ℝ) - h 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
    have hc : 2 / ((e0 - h) ⬝ᵥ (e0 - h)) * ((e0 - h) ⬝ᵥ e0) = 1 := by
      rw [vv_eq hu, dot3]; simp [e0]; field_simp
    simp only [hhm, h0, ↓reduceIte, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec]
    funext i
    have hvi : (e0 - h) i = e0 i - h i := rfl
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    linear_combination (-((e0 - h) i)) * hc
      + (2 / ((e0 - h) ⬝ᵥ (e0 - h)) * ((e0 - h) ⬝ᵥ e0) - 1) * hvi

lemma hhm_symm : (hhm h)ᵀ = hhm h := by
  by_cases h0 : h 0 = 1
  · simp [hhm, h0]
  · simp only [hhm, h0, ↓reduceIte, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_smul, Matrix.transpose_vecMulVec]

lemma hhm_sq : hhm h * hhm h = 1 := by
  by_cases h0 : h 0 = 1
  · simp [hhm, h0]
  · have hv := vv_pos hu h0
    set v := e0 - h
    set c := 2 / (v ⬝ᵥ v)
    have hc : c * (v ⬝ᵥ v) = 2 := by simp only [c]; field_simp
    have hMM : vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    simp only [hhm, h0, ↓reduceIte]
    rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hMM, smul_smul, smul_smul, show c * c * (v ⬝ᵥ v) = 2 * c by
        rw [mul_assoc, hc]; ring]
    module

end Orth

/-- An orthogonal image of a law in `K_J` is in `K_J`. -/
lemma inKJ_orth {S : Type} [Fintype S] {q : S → ℝ} {w : S → Fin 3 → ℝ} (hw : InKJ q w)
    {H : Matrix (Fin 3) (Fin 3) ℝ} (hH : H * Hᵀ = 1) (hH' : Hᵀ * H = 1) :
    InKJ q (fun s => H *ᵥ w s) := by
  refine ⟨hw.1, hw.2.1, fun i => ?_, fun i k => ?_, fun s => ?_⟩
  · simp only [mulVec_row]; exact mean_dot hw (H i)
  · simp only [mulVec_row]
    rw [second_dot hw, ← hH]
    simp [Matrix.mul_apply, dotProduct]
  · rw [dot_mulVec, Matrix.mulVec_mulVec, hH', Matrix.one_mulVec]
    exact hw.2.2.2.2 s

/-! ### Part 2, lower bound: the latent law `w = (W, S₁, S₂)` -/

section Latent

open Novel.M4BoundedLawRateProof (Sm qh Zh qh_pos qh_sum qh_centered)

/-- A sign `±1`. -/
def sgb (b : Bool) : ℝ := if b then 1 else -1

/-- The normalized grid `W_i = z_i/√V`. -/
def Wg (k : ℕ) (i : Fin (4 * k - 2 + 1)) : ℝ := zv k i / Real.sqrt (Vg k)

/-- The latent masses: the sine weights times two fair signs. -/
def qw (k : ℕ) (x : Fin (4 * k - 2 + 1) × Bool × Bool) : ℝ := qh (4 * k - 2) x.1 / 4

/-- The latent vector `(W, S₁, S₂)`. -/
def wv (k : ℕ) (x : Fin (4 * k - 2 + 1) × Bool × Bool) : Fin 3 → ℝ :=
  ![Wg k x.1, sgb x.2.1, sgb x.2.2]

lemma sum_S {k : ℕ} (g : Fin (4 * k - 2 + 1) → Bool → Bool → ℝ) :
    ∑ x, qw k x * g x.1 x.2.1 x.2.2
      = ∑ i, qh (4 * k - 2) i * ((g i true true + g i true false + g i false true
          + g i false false) / 4) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, qw]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {k : ℕ} (hk : 2 ≤ k)
include hk

lemma Vg_pos : 0 < Vg k := by
  have := Vg_ge hk
  have : (0 : ℝ) < (k : ℝ) ^ 2 / 12 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  linarith

lemma zv_centered : ∑ i, qh (4 * k - 2) i * zv k i = 0 := by
  have h := qh_centered (4 * k - 2) (1 / 2)
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [zv, Zh]
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

lemma W_moments : ∑ i, qh (4 * k - 2) i * Wg k i = 0 ∧
    ∑ i, qh (4 * k - 2) i * (Wg k i * Wg k i) = 1 := by
  have hV := Vg_pos hk
  have hs : Real.sqrt (Vg k) ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  constructor
  · simp only [Wg, mul_div_assoc', ← Finset.sum_div, zv_centered hk, zero_div]
  · have e : ∀ i, qh (4 * k - 2) i * (Wg k i * Wg k i) = qh (4 * k - 2) i * zv k i ^ 2 / Vg k :=
      fun i => by
        simp only [Wg]
        rw [div_mul_div_comm, ← sq (Real.sqrt _), Real.sq_sqrt hV.le]; ring
    simp only [e, ← Finset.sum_div]
    exact div_self hV.ne'

lemma W_sq_le (i : Fin (4 * k - 2 + 1)) : Wg k i ^ 2 ≤ 48 := by
  have hV := Vg_pos hk
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Wg, div_pow, Real.sq_sqrt hV.le, div_le_iff₀ hV]
  have h1 := zv_abs hk i
  have h2 := Vg_ge hk
  nlinarith

omit hk in
/-- Coordinate `c` of the latent vector, as a function of the grid index and the two signs. -/
def Gw (k : ℕ) (c : Fin 3) (i : Fin (4 * k - 2 + 1)) (b₁ b₂ : Bool) : ℝ :=
  ![Wg k i, sgb b₁, sgb b₂] c

lemma latent_inKJ : InKJ (qw k) (wv k) := by
  obtain ⟨hW0, hW2⟩ := W_moments hk
  have hq1 := qh_sum (4 * k - 2)
  have hw : ∀ x c, wv k x c = Gw k c x.1 x.2.1 x.2.2 := fun x c => rfl
  refine ⟨fun x => div_nonneg (qh_pos _ _).le (by norm_num), ?_, fun c => ?_, fun c d => ?_,
    fun x => ?_⟩
  · have := sum_S (k := k) (fun _ _ _ => 1)
    simp only [mul_one] at this
    rw [this]; simp only [show ((1 : ℝ) + 1 + 1 + 1) / 4 = 1 by norm_num, mul_one, hq1]
  · simp only [hw]
    rw [sum_S (k := k) (Gw k c)]
    have hb : ∀ i, (Gw k c i true true + Gw k c i true false + Gw k c i false true
        + Gw k c i false false) / 4 = if c = 0 then Wg k i else 0 := fun i => by
      fin_cases c <;> (simp [Gw, sgb]; try ring)
    simp only [hb]
    by_cases hc : c = 0
    · simp only [hc, ↓reduceIte, hW0]
    · simp [hc]
  · simp only [hw]
    rw [sum_S (k := k) (fun i b₁ b₂ => Gw k c i b₁ b₂ * Gw k d i b₁ b₂)]
    have hb : ∀ i, (Gw k c i true true * Gw k d i true true + Gw k c i true false * Gw k d i true false
        + Gw k c i false true * Gw k d i false true + Gw k c i false false * Gw k d i false false) / 4
        = if c = d then (if c = 0 then Wg k i * Wg k i else 1) else 0 := fun i => by
      fin_cases c <;> fin_cases d <;> simp [Gw, sgb] <;> ring
    simp only [hb]
    by_cases hcd : c = d
    · subst hcd
      by_cases hc : c = 0
      · simp only [hc, ↓reduceIte, hW2, Matrix.one_apply_eq]
      · simp only [hc, ↓reduceIte, mul_one, hq1, Matrix.one_apply_eq]
    · simp [hcd, Matrix.one_apply_ne hcd]
  · rw [dot3]
    simp only [wv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have := W_sq_le hk x.1
    have h1 : sgb x.2.1 * sgb x.2.1 = 1 := by simp only [sgb]; split_ifs <;> norm_num
    have h2 : sgb x.2.2 * sgb x.2.2 = 1 := by simp only [sgb]; split_ifs <;> norm_num
    nlinarith

end Latent

/-! ### Part 2: the lower bound -/

lemma Jt_small {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : SmallJ J) (d : Fin 3 → ℝ) :
    (Jᵀ *ᵥ d) ⬝ᵥ (Jᵀ *ᵥ d) ≤ (1 / 100) ^ 2 * (d ⬝ᵥ d) := by
  set y := Jᵀ *ᵥ d
  have e : y ⬝ᵥ y = d ⬝ᵥ (J *ᵥ y) := by
    rw [show y ⬝ᵥ y = (Jᵀ *ᵥ d) ⬝ᵥ y from rfl, dot_mulVec, Matrix.transpose_transpose]
  have hcs := cs3 d (J *ᵥ y)
  have hJy := hJ y
  have hy0 := dot_self_nonneg y
  have hd0 := dot_self_nonneg d
  rw [← e] at hcs
  have : (y ⬝ᵥ y) ^ 2 ≤ (d ⬝ᵥ d) * ((1 / 100) ^ 2 * (y ⬝ᵥ y)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hJy hd0)
  nlinarith

lemma sig2_eq (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) :
    sig2 J d = (Jᵀ *ᵥ d) ⬝ᵥ (Jᵀ *ᵥ d) := by
  rw [sig2, ← Matrix.mulVec_mulVec, dotProduct_comm, dot_mulVec]

lemma sigma_small {J : Matrix (Fin 3) (Fin 3) ℝ} (hJ : SmallJ J) : sigma J ≤ 1 / 50 := by
  have b : ∀ d : Fin 3 → ℝ, d ⬝ᵥ d ≤ 3 → Real.sqrt (sig2 J d) ≤ 1 / 50 := fun d hd => by
    rw [Real.sqrt_le_left (by norm_num), sig2_eq]
    exact (Jt_small hJ d).trans (by nlinarith)
  exact max_le (b d0 (by rw [dot3]; simp [d0]; norm_num)) (b d1 (by rw [dot3]; simp [d1]; norm_num))

lemma record_congr {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ}
    {U : S → Fin 3 → ℝ} {θ θ' : Fin 3 → ℝ} {s s' : S}
    (h : θ + J *ᵥ U s = θ' + J *ᵥ U s') : record (data J q U) θ s = record (data J q U) θ' s' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Pi.add_apply] at h0 h1 h2
  rw [record_d, record_d, h0, h1]
  congr 1
  linarith

/-- The paired square-root masses of the common atoms, `√(q_{j+1} q_j)`, with the two signs. -/
def sa (k : ℕ) (x : Fin (4 * k - 2) × Bool × Bool) : ℝ :=
  Novel.M4BoundedLawRateProof.u (4 * k - 2) (x.1 + 2) *
    Novel.M4BoundedLawRateProof.u (4 * k - 2) (x.1 + 1) /
    Novel.M4BoundedLawRateProof.Sm (4 * k - 2) / 4

lemma sa_nonneg {k : ℕ} (x : Fin (4 * k - 2) × Bool × Bool) : 0 ≤ sa k x := by
  refine div_nonneg (div_nonneg (mul_nonneg ?_ ?_) (Novel.M4BoundedLawRateProof.Sm_pos _).le)
    (by norm_num)
  · exact (Novel.M4BoundedLawRateProof.u_pos _ (by omega) (by have := x.1.isLt; omega)).le
  · exact (Novel.M4BoundedLawRateProof.u_pos _ (by omega) (by have := x.1.isLt; omega)).le

lemma sa_sq {k : ℕ} (x : Fin (4 * k - 2) × Bool × Bool) :
    sa k x ^ 2 = qw k (x.1.succ, x.2) * qw k (x.1.castSucc, x.2) := by
  simp only [sa, qw, Novel.M4BoundedLawRateProof.qh, Fin.val_succ, Fin.val_castSucc]
  ring

lemma sa_total (k : ℕ) (N : ℕ) : ∑ τ : Fin N → Fin (4 * k - 2) × Bool × Bool, ∏ l, sa k (τ l)
    = Real.cos (Novel.M4BoundedLawRateProof.phi (4 * k - 2)) ^ N := by
  rw [← Fintype.prod_sum (fun _ : Fin N => sa k), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  have hS := Novel.M4BoundedLawRateProof.Sm_pos (4 * k - 2)
  have haf := Novel.M4BoundedLawRateProof.affinity_sum (4 * k - 2)
  have hr := Fin.sum_univ_eq_sum_range (fun j => Novel.M4BoundedLawRateProof.u (4 * k - 2) (j + 1) *
    Novel.M4BoundedLawRateProof.u (4 * k - 2) (j + 2)) (4 * k - 2)
  have e : ∀ j : Fin (4 * k - 2), ∑ b : Bool × Bool, sa k (j, b)
      = Novel.M4BoundedLawRateProof.u (4 * k - 2) (j + 1) *
        Novel.M4BoundedLawRateProof.u (4 * k - 2) (j + 2) /
        Novel.M4BoundedLawRateProof.Sm (4 * k - 2) := fun j => by
    simp only [sa, Fintype.sum_prod_type, Fintype.sum_bool]; ring
  rw [Fintype.sum_prod_type]
  simp only [e, ← Finset.sum_div, hr, haf]
  field_simp

lemma final_log {k N : ℕ} {σ δ ε : ℝ} (hk2 : 2 ≤ k) (hN : 0 < N) (hδ : 0 < δ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 16) (hk8 : σ / (8 * δ) ≤ k) (hσ : 0 < σ)
    (hle : (Real.cos (Real.pi / (4 * k)) ^ N) ^ 2 ≤ 4 * ε) :
    1 / (16 * Real.pi ^ 2) * (σ ^ 2 / δ ^ 2) * Real.log (1 / ε) ≤ N := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hφ0 : 0 < Real.pi / (4 * k) := by positivity
  have hφ1 : Real.pi / (4 * k) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_le_four]
  obtain ⟨hcos, hlog⟩ := Novel.M4BoundedLawRateProof.log_cos_ge hφ0 hφ1
  have hlog2 := Real.log_le_log (by positivity) hle
  rw [← pow_mul, Real.log_pow, Real.log_mul (by norm_num) hε.ne'] at hlog2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : -(Real.log 4 + Real.log ε) ≤ 2 * N * (Real.pi / (4 * k)) ^ 2 := by
    push_cast at hlog2
    nlinarith
  have hlogε : Real.log ε ≤ -(2 * Real.log 4) := by
    have := Real.log_le_log hε hε1
    rw [show (1 : ℝ) / 16 = (4 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow] at this
    push_cast at this; linarith
  have hL4 : -Real.log ε ≤ 4 * N * (Real.pi / (4 * k)) ^ 2 := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [show Real.log (1 / ε) = -Real.log ε by rw [one_div, Real.log_inv]]
  have hL : 0 ≤ -Real.log ε := by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith
  have hsd : σ ^ 2 / δ ^ 2 ≤ 64 * (k : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : σ ≤ 8 * δ * k := by rw [div_le_iff₀ (by positivity)] at hk8; linarith
    nlinarith
  have e : 4 * (N : ℝ) * (Real.pi / (4 * k)) ^ 2 = N * Real.pi ^ 2 / (4 * k ^ 2) := by
    field_simp
  rw [e] at hL4
  have hL4' : -Real.log ε * (4 * k ^ 2) ≤ N * Real.pi ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at hL4
  calc 1 / (16 * Real.pi ^ 2) * (σ ^ 2 / δ ^ 2) * -Real.log ε
      ≤ 1 / (16 * Real.pi ^ 2) * (64 * k ^ 2) * -Real.log ε := by gcongr
    _ = (-Real.log ε * (4 * k ^ 2)) / Real.pi ^ 2 := by field_simp; ring
    _ ≤ N := by rw [div_le_iff₀ (by positivity)]; linarith

/-- If `Ω₃₃ = 0`, the third row of `J` vanishes, so alpha carries no noise. -/
lemma J_row2 {J : Matrix (Fin 3) (Fin 3) ℝ} (h0 : (J * Jᵀ) 2 2 = 0) (y : Fin 3 → ℝ) :
    (J *ᵥ y) 2 = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at h0
  have e0 : J 2 0 = 0 := by nlinarith [sq_nonneg (J 2 0), sq_nonneg (J 2 1), sq_nonneg (J 2 2)]
  have e1 : J 2 1 = 0 := by nlinarith [sq_nonneg (J 2 0), sq_nonneg (J 2 1), sq_nonneg (J 2 2)]
  have e2 : J 2 2 = 0 := by nlinarith [sq_nonneg (J 2 0), sq_nonneg (J 2 1), sq_nonneg (J 2 2)]
  simp [mulVec, dotProduct, Fin.sum_univ_three, e0, e1, e2]

/-- The lower bound from a rule that is correct at the hard pair only. The hard pair is fixed
before `N_obs` and the law, and shares its alpha when `Ω₃₃ = 0`. -/
lemma lower_core (J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : SmallJ J) {δ ε : ℝ} (hδ : 0 < δ)
    (hδσ : δ ≤ sigma J / 8) (hε : 0 < ε) (hε1 : ε ≤ 1 / 16) :
    ∃ θm θp : Fin 3 → ℝ, θm ∈ Theta4 (V4 J) ∧ θp ∈ Theta4 (V4 J) ∧
      ((J * Jᵀ) 2 2 = 0 → θm 2 = θp 2) ∧
      ∀ N : ℕ, 0 < N →
        (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
          ∃ ρ : Rule N, AdmitsJ (data J q U) ρ ∧ falseP (data J q U) δ θm ρ ≤ ε ∧
            (δ ≤ Gstar (data J q U) θp → 1 - ε ≤ powerP (data J q U) δ θp ρ)) →
        1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε) ≤ N := by
  have hσ : 0 < sigma J := by linarith
  have hσs := sigma_small hJ
  -- the harder comparison direction
  obtain ⟨jb, hsel⟩ : ∃ jb : Bool, Real.sqrt (sig2 J (if jb then d1 else d0)) = sigma J := by
    by_cases h : Real.sqrt (sig2 J d1) ≤ Real.sqrt (sig2 J d0)
    · exact ⟨false, by simp [sigma, max_eq_left h]⟩
    · exact ⟨true, by simp [sigma, max_eq_right (le_of_not_ge h)]⟩
  set dj : Fin 3 → ℝ := if jb then d1 else d0 with hdj
  set dq : Fin 3 → ℝ := if jb then d0 else d1 with hdq
  set cj : Fin 3 → ℝ := if jb then c1 else c0 with hcj
  have hdc : dj ⬝ᵥ cj = 0 := by cases jb <;> simp [dj, cj, d0, d1, c0, c1]
  have hoc : dq ⬝ᵥ cj = 1 / 4 := by cases jb <;> (simp [dq, cj, d0, d1, c0, c1]; try norm_num)
  have hmin : ∀ θ, min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) = min (dj ⬝ᵥ θ) (dq ⬝ᵥ θ) := fun θ => by
    cases jb <;> simp [dj, dq, min_comm]
  have hsq : sig2 J dj = sigma J ^ 2 := by
    rw [← hsel, Real.sq_sqrt (by rw [sig2_eq]; exact dot_self_nonneg _)]
  -- the scale
  have hx2 : 2 ≤ sigma J / (4 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
  set k := ⌊sigma J / (4 * δ)⌋₊ with hkdef
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hx2)
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkσ : (k : ℝ) ≤ sigma J / (4 * δ) := Nat.floor_le (by positivity)
  have hk8 : sigma J / (8 * δ) ≤ k := by
    have := Nat.lt_floor_add_one (sigma J / (4 * δ))
    rw [← hkdef] at this
    have e : sigma J / (8 * δ) = (sigma J / (4 * δ)) / 2 := by field_simp; ring
    rw [e]; linarith
  set V := Vg k
  have hV := Vg_ge hk2
  have hVu := Vg_le hk2
  have hV0 := Vg_pos hk2
  set a := 1 / (2 * Real.sqrt V) with hadef
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
  have ha0 : 0 < a := by positivity
  have hsV1 : 1 / 2 ≤ Real.sqrt V := by
    rw [Real.le_sqrt (by norm_num) hV0.le]; nlinarith
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one (by positivity)]; linarith
  have hsV2 : Real.sqrt V ≤ 2 * k := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have haσ : δ ≤ a * sigma J := by
    have : 1 / (4 * (k : ℝ)) ≤ a := by
      rw [hadef]; apply one_div_le_one_div_of_le (by positivity); linarith
    have h4 : δ ≤ sigma J / (4 * k) := by
      rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at hkσ; linarith
    calc δ ≤ sigma J / (4 * k) := h4
      _ = 1 / (4 * k) * sigma J := by ring
      _ ≤ a * sigma J := mul_le_mul_of_nonneg_right this hσ.le
  -- the unit direction and its orthogonal completion
  set h : Fin 3 → ℝ := (1 / sigma J) • (Jᵀ *ᵥ dj) with hhdef
  have hσne : sigma J ≠ 0 := hσ.ne'
  have hu : h ⬝ᵥ h = 1 := by
    rw [hhdef, smul_dotProduct, dotProduct_smul, ← sig2_eq, hsq, smul_eq_mul, smul_eq_mul]
    field_simp
  have hJh : dj ⬝ᵥ (J *ᵥ h) = sigma J := by
    rw [dotProduct_comm, dot_mulVec, hhdef, smul_dotProduct, dotProduct_comm, ← sig2_eq, hsq,
      smul_eq_mul]
    field_simp
  have hJo : |dq ⬝ᵥ (J *ᵥ h)| ≤ sigma J := by
    rw [dotProduct_comm, dot_mulVec, dotProduct_comm]
    have hc := cs3 (Jᵀ *ᵥ dq) h
    rw [hu, mul_one, ← sig2_eq] at hc
    have hq' : Real.sqrt (sig2 J dq) ≤ sigma J := by cases jb <;> simp [dq, sigma]
    calc |(Jᵀ *ᵥ dq) ⬝ᵥ h| ≤ Real.sqrt (sig2 J dq) := Real.abs_le_sqrt hc
      _ ≤ sigma J := hq'
  have hhi : ∀ i, |h i| ≤ 1 := fun i => by
    rw [← sq_le_one_iff_abs_le_one]; exact (coord_sq_le h i).trans (le_of_eq hu)
  have hJh2 : (J * Jᵀ) 2 2 = 0 → (J *ᵥ h) 2 = 0 := fun h0 => J_row2 h0 h
  clear_value h
  set H := hhm h
  have hHH : H * Hᵀ = 1 := by rw [hhm_symm hu, hhm_sq hu]
  have hHH' : Hᵀ * H = 1 := by rw [hhm_symm hu, hhm_sq hu]
  -- the hard law and the hypothesized rule
  set U : Fin (4 * k - 2 + 1) × Bool × Bool → Fin 3 → ℝ := fun x => H *ᵥ wv k x with hUdef
  have hK : InKJ (qw k) U := inKJ_orth (latent_inKJ hk2) hHH hHH'
  set θm := cj + J *ᵥ ((-a) • h) with hθmdef
  set θp := cj + J *ᵥ (a • h) with hθpdef
  have hθm : θm ∈ Theta4 (V4 J) := box_mem J jb fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos ha0]
    nlinarith [hhi i, abs_nonneg (h i)]
  have hθp : θp ∈ Theta4 (V4 J) := box_mem J jb fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ha0]
    nlinarith [hhi i, abs_nonneg (h i)]
  refine ⟨θm, θp, hθm, hθp, fun h0 => ?_, fun N hN hyp => ?_⟩
  · simp only [hθmdef, hθpdef, Pi.add_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      hJh2 h0, mul_zero]
  obtain ⟨ρ, hA, hfalse, hpow⟩ := hyp _ (qw k) U hK
  set D := data J (qw k) U with hDdef
  have hjm : dj ⬝ᵥ θm = -(a * sigma J) := by
    rw [hθmdef, dotProduct_add, hdc, Matrix.mulVec_smul, dotProduct_smul, hJh]; simp
  have hjp : dj ⬝ᵥ θp = a * sigma J := by
    rw [hθpdef, dotProduct_add, hdc, Matrix.mulVec_smul, dotProduct_smul, hJh]; simp
  have hop : a * sigma J < dq ⬝ᵥ θp := by
    rw [hθpdef, dotProduct_add, hoc, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    have := (abs_le.mp hJo).1
    nlinarith
  have hneg : min (d0 ⬝ᵥ θm) (d1 ⬝ᵥ θm) < 0 := by
    rw [hmin, hjm]; exact min_lt_of_left_lt (by nlinarith)
  have hGp : δ ≤ Gstar D θp := by
    rw [Gstar_d, hmin, hjp, min_eq_left hop.le, max_eq_right (by positivity)]; exact haσ
  -- certification probabilities at the two parameters
  let c : (Fin N → Record 1) → ℝ := fun Hs => (ρ.kernel Hs {w | 0 < w (Sum.inl 0)}).toReal
  have hc01 : ∀ Hs, 0 ≤ c Hs ∧ c Hs ≤ 1 := fun Hs =>
    Novel.M4BoundedLawRateProof.kernel_bounds ρ Hs _
  have hmass : ∀ σ : Fin N → Fin (4 * k - 2 + 1) × Bool × Bool, 0 ≤ mass D σ := fun σ =>
    Finset.prod_nonneg fun _ _ => hK.1 _
  have hm : ∑ σ, mass D σ * c (hist D θm σ) ≤ ε := by
    refine le_trans (Finset.sum_le_sum fun σ _ => ?_) hfalse
    refine mul_le_mul_of_nonneg_left ?_ (hmass σ)
    have := ρ.isProb (hist D θm σ)
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    calc ρ.kernel _ {w | 0 < w (Sum.inl 0)}
        ≤ ρ.kernel _ ({w | 0 < w (Sum.inl 0) ∧ Adv D w θm ≤ δ / 4}
            ∪ {w | ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0)) ∧ w ∉ E D}) := by
          apply measure_mono
          intro w hw
          simp only [Set.mem_ofPred_eq] at hw
          by_cases hF : w ∈ F D
          · exact Or.inl ⟨hw, by linarith [Adv_neg hneg hF hw]⟩
          · refine Or.inr ⟨fun h' => hF h'.1, fun hE => ?_⟩
            rw [E_d] at hE; linarith [hE.1]
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hA, add_zero]
  have hp : 1 - ε ≤ ∑ σ, mass D σ * c (hist D θp σ) := by
    refine le_trans (hpow hGp) (Finset.sum_le_sum fun σ _ => ?_)
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
      wv k (j.succ, b) = wv k (j.castSucc, b) + (2 * a) • e0 := by
    intro j b
    funext i
    fin_cases i
    · simp only [wv, Wg, zv, e0, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Fin.val_succ, Fin.val_castSucc, hadef]
      push_cast
      field_simp
      ring
    · simp [wv, e0]
    · simp [wv, e0]
  have hhist : ∀ τ, hist D θm (sm τ) = hist D θp (sp τ) := by
    intro τ
    funext l
    apply record_congr
    simp only [sm, sp, hUdef]
    rw [hstep, Matrix.mulVec_add, Matrix.mulVec_smul, hhm_col hu]
    funext i
    simp only [hθmdef, hθpdef, Pi.add_apply, Matrix.mulVec_add, Matrix.mulVec_smul,
      Pi.smul_apply, smul_eq_mul]
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
  -- the affinity
  have ha2 : ∀ τ, (∏ l, sa k (τ l)) ^ 2 = mass D (sm τ) * mass D (sp τ) := by
    intro τ
    simp only [mass, sm, sp, hDdef, data, ← Finset.prod_pow, ← Finset.prod_mul_distrib, sa_sq]
  have hps : ∑ τ, mass D (sm τ) ≤ 1 :=
    le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sm hsm (mass D) hmass) (le_of_eq hsum1)
  have hrs : ∑ τ, mass D (sp τ) ≤ 1 :=
    le_trans (Novel.M4BoundedLawRateProof.sum_inj_le sp hsp (mass D) hmass) (le_of_eq hsum1)
  have hle := Novel.M4BoundedLawRateProof.lecam (fun τ => mass D (sm τ)) (fun τ => mass D (sp τ))
    (fun τ => c (hist D θp (sp τ))) (fun τ => ∏ l, sa k (τ l)) ε (fun τ => hmass _)
    (fun τ => hmass _) hps hrs (fun τ => hc01 _) h1 h2
    (fun τ => Finset.prod_nonneg fun l _ => sa_nonneg _) ha2
  rw [sa_total, phi_kk hk2] at hle
  exact final_log hk2 hN hδ hε hε1 hk8 hσ hle

theorem lowerBound : LowerBound := by
  intro J hJ δ ε hδ hδσ hε hε1 N hN hyp
  obtain ⟨θm, θp, hθm, hθp, -, hcore⟩ := lower_core J hJ hδ hδσ hε hε1
  refine hcore N hN fun S _ q U hK => ?_
  obtain ⟨ρ, hA, hf, hp⟩ := hyp S q U hK
  exact ⟨ρ, hA, hf θm hθm, hp θp hθp⟩

/-- With `Ω₃₃ = 0` the hard pair shares alpha, so a rule told alpha faces the same bound. -/
theorem knownAlphaLower : KnownAlphaLower := by
  intro J hJ h0 δ ε hδ hδσ hε hε1
  obtain ⟨θm, θp, hθm, hθp, hα, hcore⟩ := lower_core J hJ hδ hδσ hε hε1
  refine ⟨θm 2, fun N hN hyp => hcore N hN fun S _ q U hK => ?_⟩
  obtain ⟨ρ, hA, hf, hp⟩ := hyp S q U hK
  exact ⟨ρ, hA, hf θm ⟨hθm, rfl⟩, hp θp ⟨hθp, (hα h0).symm⟩⟩

/-! ### Part 4: alpha precision and the second comparator -/

lemma omega_comm (J : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : (J * Jᵀ) i j = (J * Jᵀ) j i := by
  simp [Matrix.mul_apply, mul_comm]

lemma omega_entry (J : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : (J * Jᵀ) i j = J i ⬝ᵥ J j := by
  simp [Matrix.mul_apply, dotProduct]

lemma sig2_d0 (J : Matrix (Fin 3) (Fin 3) ℝ) :
    sig2 J d0 = (J * Jᵀ) 0 0 + 2 * (J * Jᵀ) 0 2 + (J * Jᵀ) 2 2 := by
  have h := omega_comm J 2 0
  simp only [sig2, mulVec, dotProduct, Fin.sum_univ_three, d0] at h ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h ⊢
  linear_combination h

lemma sig2_d1 (J : Matrix (Fin 3) (Fin 3) ℝ) :
    sig2 J d1 = (J * Jᵀ) 0 0 + (J * Jᵀ) 1 1 + (J * Jᵀ) 2 2
      - 2 * (J * Jᵀ) 0 1 + 2 * (J * Jᵀ) 0 2 - 2 * (J * Jᵀ) 1 2 := by
  have h1 := omega_comm J 1 0
  have h2 := omega_comm J 2 0
  have h3 := omega_comm J 2 1
  simp only [sig2, mulVec, dotProduct, Fin.sum_univ_three, d1] at h1 h2 h3 ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h1 h2 h3 ⊢
  linear_combination -h1 + h2 - h3

lemma omega_cs (J : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (J * Jᵀ) i j ^ 2 ≤ (J * Jᵀ) i i * (J * Jᵀ) j j := by
  simp only [omega_entry]; exact cs3 _ _

lemma sigma_sq_ge (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) (hd : d = d0 ∨ d = d1) :
    sig2 J d ≤ sigma J ^ 2 := by
  have h0 : 0 ≤ sig2 J d := by rw [sig2_eq]; exact dot_self_nonneg _
  have hs : Real.sqrt (sig2 J d) ≤ sigma J := by
    rcases hd with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rwa [Real.sq_sqrt h0] at this

lemma alpha_part (J : Matrix (Fin 3) (Fin 3) ℝ) :
    sig2 J d0 = (J * Jᵀ) 0 0 + 2 * (J * Jᵀ) 0 2 + (J * Jᵀ) 2 2 ∧
    sig2 J d1 = (J * Jᵀ) 0 0 + (J * Jᵀ) 1 1 + (J * Jᵀ) 2 2
      - 2 * (J * Jᵀ) 0 1 + 2 * (J * Jᵀ) 0 2 - 2 * (J * Jᵀ) 1 2 ∧
    (Real.sqrt ((J * Jᵀ) 0 0) - Real.sqrt ((J * Jᵀ) 2 2)) ^ 2 ≤ sigma J ^ 2 ∧
    (Real.sqrt ((J * Jᵀ) 2 2) ≤ Real.sqrt ((J * Jᵀ) 0 0) / 2 → ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 1 →
      (J * Jᵀ) 0 0 * Real.log (1 / ε) / (64 * Real.pi ^ 2 * δ ^ 2)
        ≤ 1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε)) ∧
    ((J * Jᵀ) 2 2 = 0 → (J * Jᵀ) 0 2 = 0 ∧ (J * Jᵀ) 1 2 = 0 ∧ (J * Jᵀ) 0 0 ≤ sigma J ^ 2 ∧
      ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
        ∀ θ s, 0 < q s → X (data J q U) (record (data J q U) θ s) 2 = θ 2) := by
  have h00 : 0 ≤ (J * Jᵀ) 0 0 := by rw [omega_entry]; exact dot_self_nonneg _
  have h22 : 0 ≤ (J * Jᵀ) 2 2 := by rw [omega_entry]; exact dot_self_nonneg _
  have hs0 := sigma_sq_ge J d0 (Or.inl rfl)
  have hsq : (Real.sqrt ((J * Jᵀ) 0 0) - Real.sqrt ((J * Jᵀ) 2 2)) ^ 2 ≤ sigma J ^ 2 := by
    have hcs := omega_cs J 0 2
    have hm : -(Real.sqrt ((J * Jᵀ) 0 0) * Real.sqrt ((J * Jᵀ) 2 2)) ≤ (J * Jᵀ) 0 2 := by
      rw [← Real.sqrt_mul h00]
      exact neg_le_of_abs_le (Real.abs_le_sqrt hcs)
    have e : (Real.sqrt ((J * Jᵀ) 0 0) - Real.sqrt ((J * Jᵀ) 2 2)) ^ 2
        = (J * Jᵀ) 0 0 - 2 * (Real.sqrt ((J * Jᵀ) 0 0) * Real.sqrt ((J * Jᵀ) 2 2))
          + (J * Jᵀ) 2 2 := by
      rw [sub_sq, Real.sq_sqrt h00, Real.sq_sqrt h22]; ring
    rw [e]; rw [sig2_d0] at hs0; linarith
  refine ⟨sig2_d0 J, sig2_d1 J, hsq, fun hle δ ε hδ hε hε1 => ?_, fun h0 => ?_⟩
  · have hq : (J * Jᵀ) 0 0 / 4 ≤ sigma J ^ 2 := by
      have hs := Real.sqrt_nonneg ((J * Jᵀ) 0 0)
      have : Real.sqrt ((J * Jᵀ) 0 0) / 2 ≤ Real.sqrt ((J * Jᵀ) 0 0) - Real.sqrt ((J * Jᵀ) 2 2) := by
        linarith
      have h2 := pow_le_pow_left₀ (by positivity) this 2
      rw [div_pow, Real.sq_sqrt h00] at h2
      linarith
    have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have hpi := Real.pi_pos
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε)
        * (64 * Real.pi ^ 2 * δ ^ 2) = 4 * sigma J ^ 2 * Real.log (1 / ε) := by
      field_simp; ring
    rw [e]
    nlinarith
  · have h02 : (J * Jᵀ) 0 2 = 0 := by
      have := omega_cs J 0 2; rw [h0, mul_zero] at this; nlinarith [sq_nonneg ((J * Jᵀ) 0 2)]
    have h12 : (J * Jᵀ) 1 2 = 0 := by
      have := omega_cs J 1 2; rw [h0, mul_zero] at this; nlinarith [sq_nonneg ((J * Jᵀ) 1 2)]
    refine ⟨h02, h12, by rw [sig2_d0, h02, h0] at hs0; linarith, fun S _ q U hK θ s hs => ?_⟩
    rw [X_d]
    simp only [Pi.add_apply, mulVec_row]
    have h2 := second_dot hK (J 2) (J 2)
    rw [← omega_entry, h0] at h2
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      mul_nonneg (hK.1 s) (mul_self_nonneg (J 2 ⬝ᵥ U s)))).mp h2 s (Finset.mem_univ _)
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hs.ne'
    · rw [mul_self_eq_zero.mp h, add_zero]

lemma example_part (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    SmallJ (Jex τ) ∧ sig2 (Jex τ) d1 = 0 ∧ sig2 (Jex τ) d0 = (1 / 1000) ^ 2 * (1 + τ ^ 2) ∧
      0 < (Jex τ * (Jex τ)ᵀ) 0 0 ∧ 0 < sigma (Jex τ) := by
  have hd1 : sig2 (Jex τ) d1 = 0 := by
    simp [sig2, Jex, d1, dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_three]
  have hd0 : sig2 (Jex τ) d0 = (1 / 1000) ^ 2 * (1 + τ ^ 2) := by
    simp [sig2, Jex, d0, dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_three]; ring
  refine ⟨fun v => ?_, hd1, hd0, by simp [Jex, Matrix.mul_apply, Fin.sum_univ_three], ?_⟩
  · simp only [Jex, mulVec, dotProduct, Fin.sum_univ_three]
    simp
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith
    have key : v 0 * v 0 + (v 0 + τ * v 1) * (v 0 + τ * v 1) + τ * v 1 * (τ * v 1)
        ≤ 3 * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) := by
      nlinarith [sq_nonneg (v 0 - τ * v 1), mul_le_mul_of_nonneg_right hτ2 (sq_nonneg (v 1)),
        sq_nonneg (v 2)]
    nlinarith [key, sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · have : 0 < Real.sqrt (sig2 (Jex τ) d0) := Real.sqrt_pos.mpr (by rw [hd0]; positivity)
    exact lt_of_lt_of_le this (le_max_left _ _)

/-- The doubly degenerate benchmark: both contrasts are observed exactly. -/
def exactRule (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} (q : S → ℝ) (U : S → Fin 3 → ℝ) {N : ℕ}
    (l0 : Fin N) (δ : ℝ) : Rule N where
  kernel H := Measure.dirac (if δ / 4 < min (d0 ⬝ᵥ X (data J q U) (H l0))
      (d1 ⬝ᵥ X (data J q U) (H l0)) then wA else 0)
  isProb _ := inferInstance

lemma degenerate_part (J : Matrix (Fin 3) (Fin 3) ℝ) (h0 : sig2 J d0 = 0) (h1 : sig2 J d1 = 0)
    (δ : ℝ) (hδ : 0 < δ) {S : Type} [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ) (hK : InKJ q U)
    (N : ℕ) (hN : 0 < N) :
    ∃ ρ : Rule N, AdmitsJ (data J q U) ρ ∧
      (∀ θ ∈ Theta4 (V4 J), falseP (data J q U) δ θ ρ = 0) ∧
      ∀ θ ∈ Theta4 (V4 J), δ ≤ Gstar (data J q U) θ → powerP (data J q U) δ θ ρ = 1 := by
  set l0 : Fin N := ⟨0, hN⟩
  have hz : ∀ d, sig2 J d = 0 → ∀ u : Fin 3 → ℝ, d ⬝ᵥ (J *ᵥ u) = 0 := by
    intro d hd u
    rw [sig2_eq] at hd
    have hJd : Jᵀ *ᵥ d = 0 := by
      funext i
      have := coord_sq_le (Jᵀ *ᵥ d) i
      rw [hd] at this
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
    rw [dotProduct_comm, dot_mulVec, hJd, dotProduct_zero]
  have hobs : ∀ θ (σ : Fin N → S) (d : Fin 3 → ℝ), sig2 J d = 0 →
      d ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0) = d ⬝ᵥ θ := by
    intro θ σ d hd
    simp only [hist, X_d, dotProduct_add, hz d hd, add_zero]
  have hmin : ∀ θ (σ : Fin N → S), min (d0 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0)) (d1 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0))
      = min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := fun θ σ => by rw [hobs θ σ d0 h0, hobs θ σ d1 h1]
  refine ⟨exactRule J q U l0 δ, fun H => ?_, fun θ hθ => ?_, fun θ hθ hG => ?_⟩
  · show Measure.dirac (if δ / 4 < min (d0 ⬝ᵥ X (data J q U) (H l0)) (d1 ⬝ᵥ X (data J q U) (H l0)) then wA else 0) _ = 0
    rw [Measure.dirac_apply]
    split_ifs
    · exact Set.indicator_of_notMem (fun h => h.1 ⟨wA_mem_F, by simp [wA]⟩) _
    · exact Set.indicator_of_notMem (fun h => h.2 zero_mem_E) _
  · refine Finset.sum_eq_zero fun σ _ => ?_
    show mass (data J q U) σ * (Measure.dirac (if δ / 4 < min (d0 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0))
      (d1 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0)) then wA else 0) _).toReal = 0
    rw [hmin, Novel.M4BoundedLawRateProof.dirac_toReal]
    split_ifs with hc hT hT
    · exact absurd hT.2 (by rw [Adv_wA]; linarith)
    · simp
    · exact absurd hT.1 (by simp)
    · simp
  · have hsum := Novel.M4BoundedLawRateProof.mass_sum (data J q U) hK.2.1 N
    rw [Gstar_d] at hG
    have hm : δ ≤ min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := by
      rcases le_total (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) 0 with h | h
      · rw [max_eq_left h] at hG; linarith
      · rwa [max_eq_right h] at hG
    rw [← hsum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    show mass (data J q U) σ * (Measure.dirac (if δ / 4 < min (d0 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0))
      (d1 ⬝ᵥ X (data J q U) (hist (data J q U) θ σ l0)) then wA else 0) _).toReal = mass (data J q U) σ
    have hc : δ / 4 < min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := by linarith
    rw [hmin, Novel.M4BoundedLawRateProof.dirac_toReal]
    simp only [hc, ↓reduceIte]
    have hA : wA ∈ {w : Inst 1 1 → ℝ | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv (data J q U) w θ} :=
      ⟨by simp [wA], by rw [Adv_wA]; linarith⟩
    simp [hA]

theorem alphaAndComparator : AlphaAndComparator :=
  ⟨alpha_part, example_part, fun J h0 h1 δ hδ _ _ q U hK N hN =>
    degenerate_part J h0 h1 δ hδ q U hK N hN⟩

theorem proof : Standalone.M4JointDirectionalRate.statement :=
  ⟨contrasts, lowerBound, upperBound, directionalCertificate, alphaAndComparator,
    knownAlphaLower⟩

end

end Novel.M4JointDirectionalRateProof

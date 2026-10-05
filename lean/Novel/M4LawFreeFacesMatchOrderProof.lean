import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Standalone.M4LawFreeFacesMatchOrder
import Novel.M4JointDirectionalRateProof

/-!
# Proof of claim 021: law-free certification against the two-face ETF comparator

This proof imports claim 016's proof module (`depends_on: [16]`; Q-04).

* **Hoeffding.** The claim cites Hoeffding's inequality through ledger entry `AX-06`. Following
  PM's rule-21 reading (a cited result already proved in the pinned Mathlib enters through Mathlib),
  the tail bound comes from Mathlib's Hoeffding lemma,
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, applied to each finite law
  as a measure. With the Chernoff step on finite iid histories it gives
  `P(Ȳ ≥ a) ≤ exp(-N a²/(2R²))`, Hoeffding's constant. The claim keeps the looser `3R²`, so every
  number holds. Nothing is re-proved and no Upstream hypothesis is assumed.
* **The rule.** A union bound over the two faces gives validity and power.
* **The lower bound.** Claim 016's formalized lower bound applies, because `K_J ⊆ L(J)`.
-/

namespace Novel.M4LawFreeFacesMatchOrderProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4LawFreeFacesMatchOrder
open Standalone.M4InformationObstruction (Rule Record M4Admissible prob hist mass Adv Gstar
  thetaHat errN X record)
open Standalone.M4JointDirectionalRate (SmallJ d0 d1 V4 sig2 sigma InKJ data wA etf1 AdmitsJ)
open Standalone.M4BoundedLawRate (falseP powerP Meets)
open Novel.M4JointDirectionalRateProof (W0_d w0_d F_d ret_inl ret_inr J_coord ge_of_sq_le sgv_dot
  mulVec_row coord_sq_le dot3 cs3 dot_mulVec dot_self_nonneg Adv_wA Gstar_d thetaHat_hist errN_J
  wA_mem_F etf1_mem_E zero_mem_E)
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Hoeffding's inequality on finite laws, from Mathlib's Hoeffding lemma -/

section Hoeffding

variable {S : Type} [Fintype S] {q : S → ℝ} {Y : S → ℝ}

/-- Hoeffding's lemma for a finite law: `E e^{tY} ≤ e^{R² t²/2}` when `E Y = 0`, `|Y| ≤ R`. -/
lemma mgf_fin (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0) {R : ℝ}
    (hR : ∀ s, |Y s| ≤ R) (t : ℝ) :
    ∑ s, q s * Real.exp (t * Y s) ≤ Real.exp (R ^ 2 * t ^ 2 / 2) := by
  let _ : MeasurableSpace S := ⊤
  have : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  set μ : Measure S := ∑ s, ENNReal.ofReal (q s) • Measure.dirac s with hμ
  have hsing : ∀ x, μ {x} = ENNReal.ofReal (q x) := by
    intro x
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb])
      (by simp)]
    simp
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hq s), hq1, ENNReal.ofReal_one]
  have hreal : ∀ x, μ.real {x} = q x := fun x => by
    rw [measureReal_def, hsing, ENNReal.toReal_ofReal (hq x)]
  have hint : ∀ f : S → ℝ, ∫ x, f x ∂μ = ∑ x, q x * f x := fun f => by
    rw [integral_fintype Integrable.of_finite]; simp [hreal]
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hq1
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR (Classical.arbitrary S))
  have hH := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := Y)
    (a := -R) (b := R) (Measurable.of_discrete.aemeasurable)
    (ae_of_all _ fun s => abs_le.mp (hR s)) (by rw [hint]; exact h0)
  have hm := hH.mgf_le t
  rw [ProbabilityTheory.mgf, hint] at hm
  have hc : (((‖R - -R‖₊ / 2) ^ 2 : NNReal) : ℝ) = R ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R - -R)]
    ring
  rwa [hc] at hm

/-- The Chernoff step on finite iid histories: `P(Ȳ ≥ a) ≤ exp(-N a²/(2R²))`. -/
lemma tail_up (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0) {R : ℝ}
    (hR0 : 0 < R) (hR : ∀ s, |Y s| ≤ R) {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    ∑ σ : Fin N → S, (if a ≤ (1 / (N : ℝ)) * ∑ l, Y (σ l) then ∏ l, q (σ l) else 0)
      ≤ Real.exp (-(N * a ^ 2) / (2 * R ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t := a / R ^ 2 with ht
  have ht0 : 0 < t := by positivity
  calc ∑ σ : Fin N → S, (if a ≤ (1 / (N : ℝ)) * ∑ l, Y (σ l) then ∏ l, q (σ l) else 0)
      ≤ ∑ σ : Fin N → S, (∏ l, q (σ l)) * Real.exp (t * (∑ l, Y (σ l) - N * a)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun l _ => hq _
        split_ifs with h
        · have h' : (N : ℝ) * a ≤ ∑ l, Y (σ l) := by
            rw [one_div, le_inv_mul_iff₀ hNr] at h; linarith
          have : 1 ≤ Real.exp (t * (∑ l, Y (σ l) - N * a)) :=
            Real.one_le_exp (mul_nonneg ht0.le (by linarith))
          nlinarith
        · positivity
    _ = Real.exp (-(t * N * a)) * ∏ _l : Fin N, ∑ s, q s * Real.exp (t * Y s) := by
        rw [Fintype.prod_sum (fun _ : Fin N => fun s => q s * Real.exp (t * Y s)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_mul_distrib, mul_sub, Finset.mul_sum, Real.exp_sub, Real.exp_sum,
          div_eq_mul_inv, ← Real.exp_neg]
        ring_nf
    _ ≤ Real.exp (-(t * N * a)) * ∏ _l : Fin N, Real.exp (R ^ 2 * t ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun l _ => Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (Real.exp_pos _).le)
          (fun l _ => mgf_fin hq hq1 h0 hR t)) (Real.exp_pos _).le
    _ = Real.exp (-(N * a ^ 2) / (2 * R ^ 2)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul,
          ← Real.exp_add]
        congr 1
        rw [ht]
        field_simp
        ring

/-- The range half-width: `P(Ȳ > R √(3L/N)) ≤ e^{-L}` for `L > 0`, including `R = 0`. -/
lemma tail_range (hq : ∀ s, 0 ≤ q s) (hq1 : ∑ s, q s = 1) (h0 : ∑ s, q s * Y s = 0) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ s, |Y s| ≤ R) {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L) :
    ∑ σ : Fin N → S, (if R * Real.sqrt (3 * L / N) < (1 / (N : ℝ)) * ∑ l, Y (σ l)
      then ∏ l, q (σ l) else 0) ≤ Real.exp (-L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases hR0.lt_or_eq with hRp | hRz
  · set r := R * Real.sqrt (3 * L / N) with hr
    have hr0 : 0 < r := by positivity
    have hr2 : r ^ 2 = R ^ 2 * (3 * L / N) := by
      rw [hr, mul_pow, Real.sq_sqrt (by positivity)]
    refine le_trans (Finset.sum_le_sum fun σ _ => ?_) ((tail_up hq hq1 h0 hRp hR hN hr0).trans ?_)
    · split_ifs with h1 h2 <;> first | exact le_rfl | exact Finset.prod_nonneg fun l _ => hq _ |
        exact absurd h1.le h2
    · apply Real.exp_le_exp.mpr
      rw [hr2]
      have : -((N : ℝ) * (R ^ 2 * (3 * L / N))) / (2 * R ^ 2) = -(3 * L / 2) := by
        field_simp
      rw [this]; linarith
  · have hY : ∀ s, Y s = 0 := fun s => abs_nonpos_iff.mp (hRz ▸ hR s)
    have : ∀ σ : Fin N → S, ¬ (R * Real.sqrt (3 * L / N) < (1 / (N : ℝ)) * ∑ l, Y (σ l)) :=
      fun σ => by simp [hY, ← hRz]
    simp only [this, ↓reduceIte, Finset.sum_const_zero]
    exact (Real.exp_pos _).le

end Hoeffding

/-! ### The family under laws in `L(J)` -/

section Family

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

lemma mean_dotL (h0 : ∀ i, ∑ s, q s * U s i = 0) (A : Fin 3 → ℝ) :
    ∑ s, q s * (A ⬝ᵥ U s) = 0 := by
  have e : ∀ s, q s * (A ⬝ᵥ U s)
      = A 0 * (q s * U s 0) + A 1 * (q s * U s 1) + A 2 * (q s * U s 2) := fun s => by
    rw [dot3]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h0, mul_zero, add_zero]

lemma dot_JU (d u : Fin 3 → ℝ) : d ⬝ᵥ (J *ᵥ u) = (Jᵀ *ᵥ d) ⬝ᵥ u := by
  rw [dotProduct_comm, dot_mulVec, dotProduct_comm]

lemma abs_face (hU : ∀ s, U s ⬝ᵥ U s ≤ 81) (d : Fin 3 → ℝ) (s : S) :
    |(Jᵀ *ᵥ d) ⬝ᵥ U s| ≤ Rj J d := by
  have h1 := Real.abs_le_sqrt (cs3 (Jᵀ *ᵥ d) (U s))
  rw [Real.sqrt_mul (dot_self_nonneg _)] at h1
  have h2 : Real.sqrt (U s ⬝ᵥ U s) ≤ 9 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [hU s]
  calc _ ≤ _ := h1
    _ ≤ sbar J d * 9 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = Rj J d := by rw [Rj]; ring

lemma admissibleL (hJ : SmallJ J) (hL : InLJ q U) : M4Admissible (data J q U) (V4 J) := by
  obtain ⟨hq, hq1, h0, hU⟩ := hL
  have hc : ∀ i, ∑ s, q s * (J *ᵥ U s) i = 0 := fun i => by
    simp only [mulVec_row]; exact mean_dotL h0 (J i)
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
      cases j <;> simp [Standalone.M4JointDirectionalRate.c0,
        Standalone.M4JointDirectionalRate.c1] <;> linarith
    · rw [ret_inr]
      have := hb 1; have := hu 1
      cases j <;> simp [Standalone.M4JointDirectionalRate.c0,
        Standalone.M4JointDirectionalRate.c1] <;> linarith

lemma thHat_eq {N : ℕ} (H : Fin N → Record 1) : thetaHat (data J q U) H = thHat H := by
  have hX : ∀ r : Record 1, X (data J q U) r = ![r.f 0, r.f 1, r.rA - r.f 0] := fun r => by
    funext i; fin_cases i <;> simp [X, data, mulVec, dotProduct]
  simp only [thetaHat, thHat, hX]

/-- The face error: `d'θ̂_N = d'θ + Ȳ_d` with `Y_d = (J'd)'U`. -/
lemma face_err {N : ℕ} (hN : 0 < N) (θ : Fin 3 → ℝ) (σ : Fin N → S) (d : Fin 3 → ℝ) :
    d ⬝ᵥ thHat (hist (data J q U) θ σ)
      = d ⬝ᵥ θ + (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l) := by
  rw [← thHat_eq (J := J) (q := q) (U := U), thetaHat_hist hN, errN_J, dotProduct_add, dot_JU]
  congr 1
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => by ring

lemma sbar_eq (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) : sbar J d = Real.sqrt (sig2 J d) := by
  rw [sbar, sig2, ← Matrix.mulVec_mulVec, dotProduct_comm, dot_mulVec]
  simp [Matrix.transpose_transpose]

lemma sbarMax_eq (J : Matrix (Fin 3) (Fin 3) ℝ) : sbarMax J = sigma J := by
  rw [sbarMax, sigma, sbar_eq, sbar_eq]

end Family

theorem setting : Setting := by
  refine ⟨fun J hJ S _ q U hL => admissibleL hJ hL,
    fun J S _ q U θ => ⟨Adv_wA θ, Gstar_d θ⟩, fun J S _ q U hL s => ?_,
    fun S _ q U hK => ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.2⟩, sbar_eq⟩
  rw [dot_JU, dot_JU]
  exact ⟨abs_face hL.2.2.2 d0 s, abs_face hL.2.2.2 d1 s⟩

/-! ### Part 1: joint constructions are face-by-face -/

section Joint

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}

lemma mass_nn (hq : ∀ s, 0 ≤ q s) {N : ℕ} (σ : Fin N → S) : 0 ≤ mass (data J q U) σ :=
  Finset.prod_nonneg fun _ _ => hq _

lemma prob_mono (hq : ∀ s, 0 ≤ q s) {N : ℕ} {θ : Fin 3 → ℝ} {A B : Set (Fin N → Record 1)}
    (h : A ⊆ B) : prob (data J q U) θ N A ≤ prob (data J q U) θ N B := by
  refine Finset.sum_le_sum fun σ _ => ?_
  by_cases h1 : hist (data J q U) θ σ ∈ A
  · simp [h1, h h1]
  · simp only [h1, ↓reduceIte]; split_ifs <;> [exact mass_nn hq σ; exact le_rfl]

lemma prob_compl (hq1 : ∑ s, q s = 1) {N : ℕ} {θ : Fin 3 → ℝ} (A : Set (Fin N → Record 1)) :
    prob (data J q U) θ N Aᶜ = 1 - prob (data J q U) θ N A := by
  have hs := Novel.M4BoundedLawRateProof.mass_sum (data J q U) hq1 N
  rw [← hs, Standalone.M4InformationObstruction.prob, Standalone.M4InformationObstruction.prob,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : hist (data J q U) θ σ ∈ A <;> simp [h]

lemma prob_union (hq : ∀ s, 0 ≤ q s) {N : ℕ} {θ : Fin 3 → ℝ} (A B : Set (Fin N → Record 1)) :
    prob (data J q U) θ N (A ∪ B) ≤ prob (data J q U) θ N A + prob (data J q U) θ N B := by
  rw [Standalone.M4InformationObstruction.prob, Standalone.M4InformationObstruction.prob,
    Standalone.M4InformationObstruction.prob, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun σ _ => ?_
  have := mass_nn (J := J) (U := U) hq σ
  by_cases hA : hist (data J q U) θ σ ∈ A <;> by_cases hB : hist (data J q U) θ σ ∈ B <;>
    (simp [hA, hB]; try linarith)

lemma coe_min' (a b : ℝ) : ((min a b : ℝ) : EReal) = min (a : EReal) (b : EReal) :=
  (EReal.coe_strictMono.monotone).map_min

lemma inf_min (C : Set (Fin 3 → ℝ)) :
    ⨅ θ ∈ C, ((Adv (data J q U) wA θ : ℝ) : EReal)
      = min (⨅ θ ∈ C, ((d0 ⬝ᵥ θ : ℝ) : EReal)) (⨅ θ ∈ C, ((d1 ⬝ᵥ θ : ℝ) : EReal)) := by
  simp only [Adv_wA, coe_min']
  refine le_antisymm (le_min (iInf₂_mono fun θ _ => min_le_left _ _)
    (iInf₂_mono fun θ _ => min_le_right _ _)) (le_iInf₂ fun θ hθ => ?_)
  exact min_le_min (iInf₂_le θ hθ) (iInf₂_le θ hθ)

lemma level_numerics : 1.23 < 1 + Real.log 2 / Real.log (1 / (1 / 20)) ∧
    1 + Real.log 2 / Real.log (1 / (1 / 20)) < 1.24 := by
  have h20 : (1 : ℝ) / (1 / 20) = 20 := by norm_num
  rw [h20]
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hup : Real.log 20 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    rw [this]; norm_num at h3; linarith
  have hlow : 4 * Real.log 2 + 1 / 5 ≤ Real.log 20 := by
    have h1 : Real.log 20 = Real.log (2 ^ 4) + Real.log (5 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h2 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
    rw [h1, Real.log_pow]; push_cast; norm_num at h2 ⊢; linarith
  have hpos : 0 < Real.log 20 := by linarith
  constructor
  · rw [← sub_lt_iff_lt_add', lt_div_iff₀ hpos]; norm_num; nlinarith
  · rw [← lt_sub_iff_add_lt', div_lt_iff₀ hpos]; norm_num; nlinarith

lemma tri (a b : Fin 3 → ℝ) :
    Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  have ha := Real.sq_sqrt (dot_self_nonneg a)
  have hb := Real.sq_sqrt (dot_self_nonneg b)
  have hab : |a ⬝ᵥ b| ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt (b ⬝ᵥ b) := by
    rw [← Real.sqrt_mul (dot_self_nonneg a)]; exact Real.abs_le_sqrt (cs3 a b)
  rw [Real.sqrt_le_left (by positivity)]
  have e : (a - b) ⬝ᵥ (a - b) = a ⬝ᵥ a - 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm b a]; ring
  rw [e]
  nlinarith [neg_abs_le (a ⬝ᵥ b)]

end Joint

theorem joint : Joint := by
  refine ⟨fun J S _ q U C => inf_min C, fun J S _ q U hq hq1 N θ η CN hcov d _ => ?_,
    fun J S _ q U hq N θ ℓ0 ℓ1 η0 η1 h0 h1 => ⟨?_, fun H => ?_⟩, fun κ η hκ hη hη1 => ?_,
    level_numerics, fun J => ⟨?_, ?_⟩⟩
  · have hsub : {H : Fin N → Record 1 | ((d ⬝ᵥ θ : ℝ) : EReal) < ⨅ θ' ∈ CN H,
        ((d ⬝ᵥ θ' : ℝ) : EReal)} ⊆ {H | θ ∈ CN H}ᶜ := by
      intro H hH hmem
      have hH' : ((d ⬝ᵥ θ : ℝ) : EReal) < ⨅ θ' ∈ CN H, ((d ⬝ᵥ θ' : ℝ) : EReal) := hH
      exact lt_irrefl _ (lt_of_lt_of_le hH' (iInf₂_le (f := fun θ' _ => ((d ⬝ᵥ θ' : ℝ) : EReal))
        θ hmem))
    refine (prob_mono hq hsub).trans ?_
    rw [prob_compl hq1]; linarith
  · have hsub : {H : Fin N → Record 1 | θ ∉ {θ' | ℓ0 H ≤ d0 ⬝ᵥ θ' ∧ ℓ1 H ≤ d1 ⬝ᵥ θ'}} ⊆
        {H | d0 ⬝ᵥ θ < ℓ0 H} ∪ {H | d1 ⬝ᵥ θ < ℓ1 H} := by
      intro H hH
      simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hH
      exact hH
    exact (prob_mono hq hsub).trans ((prob_union hq _ _).trans (add_le_add h0 h1))
  · simp only [Adv_wA]
    set θs : Fin 3 → ℝ := ![ℓ0 H, ℓ0 H - ℓ1 H, 0]
    have e0 : d0 ⬝ᵥ θs = ℓ0 H := by
      simp [θs, Standalone.M4JointDirectionalRate.d0]
    have e1 : d1 ⬝ᵥ θs = ℓ1 H := by
      simp [θs, Standalone.M4JointDirectionalRate.d1]
    refine le_antisymm ?_ (le_iInf₂ fun θ' h => EReal.coe_le_coe_iff.mpr (min_le_min h.1 h.2))
    exact iInf₂_le_of_le θs ⟨e0.ge, e1.ge⟩ (by rw [e0, e1])
  · have hB : 0 < Real.log (1 / η) := Real.log_pos (by rw [lt_div_iff₀ hη]; linarith)
    have hsplit : Real.log (1 / (η / 2)) = Real.log 2 + Real.log (1 / η) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
    have hA : 0 ≤ Real.log (1 / (η / 2)) := by rw [hsplit]; positivity
    have hq : 1 + Real.log 2 / Real.log (1 / η) = Real.log (1 / (η / 2)) / Real.log (1 / η) := by
      rw [hsplit]; field_simp; ring
    constructor
    · rw [mul_div_mul_left _ _ hκ.ne', hq, Real.sqrt_div hA]
    · rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB.le, hq]
      field_simp
  · funext i; fin_cases i <;> simp [Standalone.M4JointDirectionalRate.d0,
      Standalone.M4JointDirectionalRate.d1, e2]
  · have hd : d1 = d0 - e2 := by
      funext i; fin_cases i <;> simp [Standalone.M4JointDirectionalRate.d0,
        Standalone.M4JointDirectionalRate.d1, e2]
    simp only [Rj, sbar, hd, Matrix.mulVec_sub]
    have := tri (Jᵀ *ᵥ d0) (Jᵀ *ᵥ e2)
    linarith

/-! ### Part 2: the law-free range rule -/

/-- The action the range rule implements. -/
def actR (J : Matrix (Fin 3) (Fin 3) ℝ) {N : ℕ} (η δe : ℝ) (H : Fin N → Record 1) :
    Inst 1 1 → ℝ :=
  if δe < min (ellR J d0 η H) (ellR J d1 η H) then wA else if 0 < thHat H 1 then etf1 else 0

lemma kernel_R (J : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ) (η δe : ℝ) (H : Fin N → Record 1) :
    (rangeRule J N η δe).kernel H = Measure.dirac (actR J η δe H) := rfl

lemma act_fallback {J : Matrix (Fin 3) (Fin 3) ℝ} {N : ℕ} {η δe : ℝ} {H : Fin N → Record 1}
    (h : ¬ δe < min (ellR J d0 η H) (ellR J d1 η H)) : actR J η δe H (Sum.inl 0) = 0 := by
  simp only [actR, h, ↓reduceIte]; split_ifs <;> rfl

lemma Rj_nonneg (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) : 0 ≤ Rj J d := by
  unfold Rj sbar; positivity

section Rule

variable {J : Matrix (Fin 3) (Fin 3) ℝ} {S : Type} [Fintype S] {q : S → ℝ} {U : S → Fin 3 → ℝ}
  (hL : InLJ q U)
include hL

lemma admits (N : ℕ) (η δe : ℝ) : AdmitsJ (data J q U) (rangeRule J N η δe) := by
  intro H
  rw [kernel_R, Measure.dirac_apply]
  apply Set.indicator_of_notMem
  rintro ⟨h1, h2⟩
  simp only [actR] at h1 h2
  split_ifs at h1 h2
  · exact h1 ⟨wA_mem_F, by simp [wA]⟩
  · exact h2 etf1_mem_E
  · exact h2 zero_mem_E

lemma up_tail {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (d : Fin 3 → ℝ) :
    ∑ σ : Fin N → S, (if rj J d N η < (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l)
      then ∏ l, q (σ l) else 0) ≤ η / 2 := by
  have hL' : 0 < Real.log (2 / η) := Real.log_pos (by rw [lt_div_iff₀ hη]; linarith)
  have := tail_range hL.1 hL.2.1 (mean_dotL hL.2.2.1 _) (Rj_nonneg J d) (abs_face hL.2.2.2 d)
    hN hL'
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at this
  exact this

lemma lo_tail {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (d : Fin 3 → ℝ) :
    ∑ σ : Fin N → S, (if (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l) < -rj J d N η
      then ∏ l, q (σ l) else 0) ≤ η / 2 := by
  have hL' : 0 < Real.log (2 / η) := Real.log_pos (by rw [lt_div_iff₀ hη]; linarith)
  have := tail_range (Y := fun s => -((Jᵀ *ᵥ d) ⬝ᵥ U s)) hL.1 hL.2.1
    (by simp only [mul_neg, Finset.sum_neg_distrib, mean_dotL hL.2.2.1, neg_zero])
    (Rj_nonneg J d) (fun s => by rw [abs_neg]; exact abs_face hL.2.2.2 d s) hN hL'
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at this
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun σ _ => ?_)) this
  simp only [Finset.sum_neg_distrib, mul_neg]
  unfold rj
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)

lemma ell_eq {N : ℕ} (hN : 0 < N) (η : ℝ) (θ : Fin 3 → ℝ) (σ : Fin N → S) (d : Fin 3 → ℝ) :
    ellR J d η (hist (data J q U) θ σ)
      = d ⬝ᵥ θ + (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l) - rj J d N η := by
  rw [ellR, face_err hN]

lemma valid {N : ℕ} (hN : 0 < N) {η δe : ℝ} (hη : 0 < η) (hη1 : η < 1) (θ : Fin 3 → ℝ) :
    falseAt (data J q U) δe θ (rangeRule J N η δe) ≤ η := by
  have h0 := up_tail (J := J) hL hN hη hη1 d0
  have h1 := up_tail (J := J) hL hN hη hη1 d1
  set e : (Fin 3 → ℝ) → (Fin N → S) → ℝ := fun d σ => (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l)
  have each : ∀ σ : Fin N → S, mass (data J q U) σ * ((rangeRule J N η δe).kernel
      (hist (data J q U) θ σ) {w | 0 < w (Sum.inl 0) ∧ Adv (data J q U) w θ ≤ δe}).toReal
      ≤ (if rj J d0 N η < e d0 σ then ∏ l, q (σ l) else 0) +
        (if rj J d1 N η < e d1 σ then ∏ l, q (σ l) else 0) := by
    intro σ
    have hm : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun _ _ => hL.1 _
    rw [kernel_R, Novel.M4BoundedLawRateProof.dirac_toReal]
    by_cases hin : actR J η δe (hist (data J q U) θ σ) ∈
        {w | 0 < w (Sum.inl 0) ∧ Adv (data J q U) w θ ≤ δe}
    · have hin' := hin
      obtain ⟨ha, hadv⟩ := hin
      have hc : δe < min (ellR J d0 η (hist (data J q U) θ σ)) (ellR J d1 η (hist (data J q U) θ σ)) := by
        by_contra hc; rw [act_fallback hc] at ha; exact lt_irrefl _ ha
      simp only [actR, hc, ↓reduceIte] at hadv
      rw [Adv_wA] at hadv
      rw [ell_eq hL hN, ell_eq hL hN] at hc
      have hbad : rj J d0 N η < e d0 σ ∨ rj J d1 N η < e d1 σ := by
        by_contra hb
        rw [not_or, not_lt, not_lt] at hb
        have : min (d0 ⬝ᵥ θ + e d0 σ - rj J d0 N η) (d1 ⬝ᵥ θ + e d1 σ - rj J d1 N η)
            ≤ min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := min_le_min (by linarith) (by linarith)
        exact absurd (hc.trans_le (this.trans hadv)) (lt_irrefl _)
      simp only [hin', ↓reduceIte, mul_one]
      rcases hbad with hb | hb
      · simp only [hb, ↓reduceIte]; split_ifs <;> [exact le_add_of_nonneg_right hm; exact
          le_of_eq (add_zero _).symm]
      · simp only [hb, ↓reduceIte]; split_ifs <;> [exact le_add_of_nonneg_left hm; exact
          le_of_eq (zero_add _).symm]
    · simp only [hin, ↓reduceIte, mul_zero]
      exact add_nonneg (by split_ifs <;> [exact hm; exact le_rfl])
        (by split_ifs <;> [exact hm; exact le_rfl])
  calc falseAt (data J q U) δe θ (rangeRule J N η δe) ≤ ∑ σ : Fin N → S,
        ((if rj J d0 N η < e d0 σ then ∏ l, q (σ l) else 0) +
          (if rj J d1 N η < e d1 σ then ∏ l, q (σ l) else 0)) :=
        Finset.sum_le_sum fun σ _ => each σ
    _ ≤ η := by rw [Finset.sum_add_distrib]; linarith

lemma power {N : ℕ} (hN : 0 < N) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1)
    (hr0 : rj J d0 N ε < 3 * δ / 8) (hr1 : rj J d1 N ε < 3 * δ / 8) (θ : Fin 3 → ℝ)
    (hG : δ ≤ Gstar (data J q U) θ) : 1 - ε ≤ powerP (data J q U) δ θ (rangeRule J N ε (δ / 4)) := by
  have h0 := lo_tail (J := J) hL hN hε hε1 d0
  have h1 := lo_tail (J := J) hL hN hε hε1 d1
  have hsum := Novel.M4BoundedLawRateProof.mass_sum (data J q U) hL.2.1 N
  rw [Gstar_d] at hG
  have hm : δ ≤ min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) := by
    rcases le_total (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) 0 with h | h
    · rw [max_eq_left h] at hG; linarith
    · rwa [max_eq_right h] at hG
  have hm0 := (le_min_iff.mp hm).1
  have hm1 := (le_min_iff.mp hm).2
  set e : (Fin 3 → ℝ) → (Fin N → S) → ℝ := fun d σ => (1 / (N : ℝ)) * ∑ l, (Jᵀ *ᵥ d) ⬝ᵥ U (σ l)
  have each : ∀ σ : Fin N → S, mass (data J q U) σ
      - (if e d0 σ < -rj J d0 N ε then ∏ l, q (σ l) else 0)
      - (if e d1 σ < -rj J d1 N ε then ∏ l, q (σ l) else 0)
      ≤ mass (data J q U) σ * ((rangeRule J N ε (δ / 4)).kernel (hist (data J q U) θ σ)
        {w | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv (data J q U) w θ}).toReal := by
    intro σ
    have hmass : 0 ≤ ∏ l, q (σ l) := Finset.prod_nonneg fun _ _ => hL.1 _
    have hmd : mass (data J q U) σ = ∏ l, q (σ l) := rfl
    rw [kernel_R, Novel.M4BoundedLawRateProof.dirac_toReal]
    by_cases hg : ¬ e d0 σ < -rj J d0 N ε ∧ ¬ e d1 σ < -rj J d1 N ε
    · obtain ⟨g0, g1⟩ := hg
      rw [not_lt] at g0 g1
      have hc : δ / 4 < min (ellR J d0 ε (hist (data J q U) θ σ))
          (ellR J d1 ε (hist (data J q U) θ σ)) := by
        rw [ell_eq hL hN, ell_eq hL hN]
        exact lt_min (by linarith) (by linarith)
      have hin : actR J ε (δ / 4) (hist (data J q U) θ σ) ∈
          {w | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv (data J q U) w θ} := by
        simp only [actR, hc, ↓reduceIte]
        refine ⟨by simp [wA], ?_⟩
        rw [Adv_wA]; linarith
      have n0 : ¬ e d0 σ < -rj J d0 N ε := not_lt.mpr g0
      have n1 : ¬ e d1 σ < -rj J d1 N ε := not_lt.mpr g1
      simp only [hin, n0, n1, ↓reduceIte, sub_zero, mul_one, le_refl]
    · rw [not_and_or, not_not, not_not] at hg
      have hk : 0 ≤ mass (data J q U) σ * (if actR J ε (δ / 4) (hist (data J q U) θ σ) ∈
          {w | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv (data J q U) w θ} then (1 : ℝ) else 0) :=
        mul_nonneg (by rw [hmd]; exact hmass) (by split_ifs <;> norm_num)
      rcases hg with hb | hb
      · simp only [hb, ↓reduceIte]; rw [hmd]
        split_ifs <;> linarith
      · simp only [hb, ↓reduceIte]; rw [hmd]
        split_ifs <;> linarith
  calc 1 - ε ≤ ∑ σ : Fin N → S, (mass (data J q U) σ
        - (if e d0 σ < -rj J d0 N ε then ∏ l, q (σ l) else 0)
        - (if e d1 σ < -rj J d1 N ε then ∏ l, q (σ l) else 0)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]; linarith
    _ ≤ _ := Finset.sum_le_sum fun σ _ => each σ

lemma r_small {N : ℕ} (hN : 0 < N) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1)
    (hNb : 22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2 * Real.log (2 / ε) ≤ N) (d : Fin 3 → ℝ)
    (hd : Rj J d ≤ max (Rj J d0) (Rj J d1)) : rj J d N ε < 3 * δ / 8 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < Real.log (2 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  set M := max (Rj J d0) (Rj J d1)
  have hR0 := Rj_nonneg J d
  have hr0 : 0 ≤ rj J d N ε := mul_nonneg hR0 (Real.sqrt_nonneg _)
  have hr2 : rj J d N ε ^ 2 = Rj J d ^ 2 * (3 * Real.log (2 / ε) / N) := by
    rw [rj, mul_pow, Real.sq_sqrt (by positivity)]
  have hM : 22 * M ^ 2 * Real.log (2 / ε) ≤ N * δ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hNb (sq_nonneg δ)
    rw [show 22 * M ^ 2 / δ ^ 2 * Real.log (2 / ε) * δ ^ 2 = 22 * M ^ 2 * Real.log (2 / ε) by
      field_simp] at this
    linarith
  have hRM : Rj J d ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hR0 hd 2
  have : rj J d N ε ^ 2 < (3 * δ / 8) ^ 2 := by
    rw [hr2, mul_div_assoc', div_lt_iff₀ hNr]
    have h1 := mul_le_mul_of_nonneg_right hRM hL.le
    have hNd : 0 < (N : ℝ) * δ ^ 2 := by positivity
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this

lemma meets {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1) {N : ℕ}
    (hNb : max 3 (22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2) * Real.log (2 / ε) ≤ N) :
    Meets (data J q U) (V4 J) δ ε (rangeRule J N ε (δ / 4)) := by
  have hLog : 0 < Real.log (2 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hN3 : 3 * Real.log (2 / ε) ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hLog.le) hNb
  have hN22 : 22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2 * Real.log (2 / ε) ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hLog.le) hNb
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  exact ⟨fun θ _ => valid hL hN hε hε1 θ, fun θ _ hG => power hL hN hδ hε hε1
    (r_small hL hN hδ hε hε1 hN22 d0 (le_max_left _ _)) (r_small hL hN hδ hε hε1 hN22 d1
      (le_max_right _ _)) θ hG⟩

end Rule

lemma Rmax_eq (J : Matrix (Fin 3) (Fin 3) ℝ) : max (Rj J d0) (Rj J d1) = 9 * sbarMax J := by
  rw [Rj, Rj, sbarMax, mul_max_of_nonneg _ _ (by norm_num)]

lemma len_conv {J : Matrix (Fin 3) (Fin 3) ℝ} {δ ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hsd : 1 ≤ sbarMax J / δ) {N : ℕ} (hNb : 1782 * (sbarMax J ^ 2 / δ ^ 2) * Real.log (2 / ε) ≤ N) :
    max 3 (22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2) * Real.log (2 / ε) ≤ N := by
  have hL : 0 < Real.log (2 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have h1 : 1 ≤ sbarMax J ^ 2 / δ ^ 2 := by
    rw [← div_pow]; nlinarith
  have e : 22 * max (Rj J d0) (Rj J d1) ^ 2 / δ ^ 2 = 1782 * (sbarMax J ^ 2 / δ ^ 2) := by
    rw [Rmax_eq]; ring
  rw [e, max_eq_right (by linarith)]
  exact hNb

theorem rangeRuleThm : RangeRule := by
  intro J S _ q U hL
  exact ⟨fun N η δe => admits hL N η δe, fun N η δe hN hη hη1 θ => valid hL hN hη hη1 θ,
    fun δ ε hδ hε hε1 N hNb => meets hL hδ hε hε1 hNb,
    fun δ ε hδ hε hε1 hsd N hNb => meets hL hδ hε hε1 (len_conv hε hε1 hsd hNb)⟩

/-! ### Part 3: the order matches claim 016's lower bound -/

theorem matchOrder : MatchOrder := by
  refine ⟨fun J hJ δ ε hδ hδσ hε hε1 N hN ρ hyp => ?_, fun J δ ε hδ hδσ hε hε1 N hNb S _ q U hL =>
    ⟨admits hL N ε (δ / 4), meets hL hδ hε (by linarith) (len_conv hε (by linarith) ?_ ?_)⟩⟩
  · have := Novel.M4JointDirectionalRateProof.lowerBound J hJ δ ε hδ
      (by rw [← sbarMax_eq]; exact hδσ) hε hε1 N hN
      (fun S _ q U hK => ⟨ρ, hyp S q U (setting.2.2.2.1 S q U hK)⟩)
    rwa [← sbarMax_eq] at this
  · rw [le_div_iff₀ hδ]; linarith
  · refine le_trans ?_ hNb
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right (by norm_num) hε.le)) (by positivity)

/-- Claim 021, all parts. -/
theorem proof : Standalone.M4LawFreeFacesMatchOrder.statement :=
  ⟨setting, joint, rangeRuleThm, matchOrder⟩

end

end Novel.M4LawFreeFacesMatchOrderProof

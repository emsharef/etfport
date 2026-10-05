import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.Order.Compact
import Novel.M5LearningAimTwoSpeedsProof
import Novel.M4BoundedLawRateProof
import Standalone.M7DataSupportActiveChange

/-!
# Proof of claim 039

Uses claim 032's proof module for the pooled posterior and claim 015's for its finite Le Cam lemma
(`depends_on` lists 15 and 32, Q-04).

* **Part 1.** On each side of `x⁻` the objective's gain over `x⁻` is a concave quadratic in the
  distance, with slope `Δ_i` above and `Δ^s_i` below. The optimum exists by compactness and is
  unique by strict concavity.
* **Gaussian rules (parts 2, 6, 7).** A sum of independent Gaussians is Gaussian, so the sample
  mean is `N(m, v/n)`; its standardization is `N(0, 1)`, whose tails at `z` and `-z` are both `ε`.
* **Part 2's order.** `N(0,1)(z, ∞) ≥ e^{-z²}/(2√2)` for `z ≥ 0`, from `(z+u)² ≤ 2z² + 2u²`.
* **Part 3.** Mathlib's Hoeffding inequality (`AX-06`) for each tail.
* **Part 3's lower bound.** Two laws on the same two observation points `b + δ/2 ± R'`,
  `R' = R - δ/2`, with alphas `b` and `b + δ` and success probabilities `(1 ∓ x)/2`, `x = δ/(2R')`.
  Their per-observation affinity is `√(1 - x²)`, and claim 015's finite Le Cam lemma gives
  `(1 - x²)^n ≤ 4ε`.
* **Part 5.** `f` is increasing with `f(p) - p` of the sign of `p_∞ - p`; the iterates are
  monotone and bounded, and their limit is a fixed point.
-/

namespace Novel.M7DataSupportActiveChangeProof

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open Standalone.M7DataSupportActiveChange
open scoped NNReal

noncomputable section

/-! ### Part 1 -/

section Part1

variable {ah gam v kp km xm : ℝ}

lemma obj_up {y : ℝ} (hy : xm ≤ y) :
    obj ah gam v kp km xm y - obj ah gam v kp km xm xm
      = (ah - bThr gam v kp xm) * (y - xm) - gam / 2 * v * (y - xm) ^ 2 := by
  simp only [obj, bThr, sub_self, max_self, max_eq_left (sub_nonneg.2 hy),
    max_eq_right (sub_nonpos.2 hy)]
  ring

lemma obj_dn {y : ℝ} (hy : y ≤ xm) :
    obj ah gam v kp km xm y - obj ah gam v kp km xm xm
      = (sThr gam v km xm - ah) * (xm - y) - gam / 2 * v * (xm - y) ^ 2 := by
  simp only [obj, sThr, sub_self, max_self, max_eq_right (sub_nonpos.2 hy),
    max_eq_left (sub_nonneg.2 hy)]
  ring

lemma max_mid (x y c : ℝ) : max ((x + y) / 2 - c) 0 ≤ (max (x - c) 0 + max (y - c) 0) / 2 := by
  apply max_le
  · have := le_max_left (x - c) 0; have := le_max_left (y - c) 0; linarith
  · have := le_max_right (x - c) 0; have := le_max_right (y - c) 0; linarith

lemma obj_mid (hg : 0 < gam) (hv : 0 < v) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) {x y : ℝ} (hxy : x ≠ y) :
    (obj ah gam v kp km xm x + obj ah gam v kp km xm y) / 2
      < obj ah gam v kp km xm ((x + y) / 2) := by
  have h1 := max_mid x y xm
  have h2 : max (xm - (x + y) / 2) 0 ≤ (max (xm - x) 0 + max (xm - y) 0) / 2 := by
    have := max_mid (-x) (-y) (-xm)
    have e : (-x + -y) / 2 - -xm = xm - (x + y) / 2 := by ring
    rw [e] at this; simpa [sub_eq_add_neg, add_comm] using this
  have hq : 0 < gam * v * (x - y) ^ 2 := by
    have := sq_pos_of_ne_zero (sub_ne_zero.2 hxy); positivity
  simp only [obj]
  nlinarith [mul_le_mul_of_nonneg_left h1 hkp, mul_le_mul_of_nonneg_left h2 hkm]

lemma continuous_obj : Continuous (obj ah gam v kp km xm) := by
  unfold obj; fun_prop

theorem decision : Decision := by
  intro ah gam v kp km xm xbar hg hv hkp hkm hxm0 hxmb
  have hmem : xm ∈ Set.Icc 0 xbar := ⟨hxm0, hxmb⟩
  have hc : 0 < gam * v := mul_pos hg hv
  -- existence
  obtain ⟨x0, hx0, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := xbar)).exists_isMaxOn
    ⟨xm, hmem⟩ continuous_obj.continuousOn
  have hopt0 : IsOpt ah gam v kp km xm xbar x0 := ⟨hx0, fun y hy => hmax hy⟩
  -- characterization
  have hchar : ∀ x, IsOpt ah gam v kp km xm xbar x →
      (xm < x ↔ xm < xbar ∧ 0 < ah - bThr gam v kp xm) ∧
      (x < xm ↔ 0 < xm ∧ 0 < sThr gam v km xm - ah) := by
    intro x ⟨hx, hxo⟩
    have hsb : sThr gam v km xm ≤ bThr gam v kp xm := by simp only [sThr, bThr]; linarith
    have hopt := hxo xm hmem
    refine ⟨⟨fun h => ⟨lt_of_lt_of_le h hx.2, ?_⟩, fun ⟨hb, hd⟩ => ?_⟩,
      ⟨fun h => ⟨lt_of_le_of_lt hx.1 h, ?_⟩, fun ⟨hb, hd⟩ => ?_⟩⟩
    · by_contra hn
      have e := obj_up (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km) h.le
      have : 0 < gam / 2 * v * (x - xm) ^ 2 := by
        have := sq_pos_of_pos (sub_pos.2 h); positivity
      nlinarith [mul_nonneg (le_of_not_gt hn |>.trans (le_refl _) |> fun h' => by linarith : (0:ℝ) ≤ -(ah - bThr gam v kp xm)) (sub_pos.2 h).le]
    · by_contra hn
      have hle := le_of_not_gt hn
      set d := min (xbar - xm) ((ah - bThr gam v kp xm) / (gam * v)) with hd_def
      have hdpos : 0 < d := lt_min (sub_pos.2 hb) (div_pos hd hc)
      have hdle : gam * v * d ≤ ah - bThr gam v kp xm := by
        have := min_le_right (xbar - xm) ((ah - bThr gam v kp xm) / (gam * v))
        rw [← hd_def] at this
        calc gam * v * d ≤ gam * v * ((ah - bThr gam v kp xm) / (gam * v)) :=
              mul_le_mul_of_nonneg_left this hc.le
          _ = _ := by field_simp
      have hy : xm + d ∈ Set.Icc 0 xbar :=
        ⟨by linarith, by linarith [min_le_left (xbar - xm) ((ah - bThr gam v kp xm) / (gam * v))]⟩
      have e1 := obj_up (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km)
        (show xm ≤ xm + d by linarith)
      have e2 := obj_dn (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km) hle
      have h3 := hxo (xm + d) hy
      simp only [add_sub_cancel_left] at e1
      have : 0 ≤ (bThr gam v kp xm - sThr gam v km xm + (ah - bThr gam v kp xm)) * (xm - x) := by
        nlinarith [sub_nonneg.2 hle]
      nlinarith [sq_nonneg (xm - x), mul_pos hdpos hd]
    · by_contra hn
      have e := obj_dn (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km) h.le
      have : 0 < gam / 2 * v * (xm - x) ^ 2 := by
        have := sq_pos_of_pos (sub_pos.2 h); positivity
      nlinarith [mul_nonneg (show (0:ℝ) ≤ -(sThr gam v km xm - ah) by linarith [le_of_not_gt hn])
        (sub_pos.2 h).le]
    · by_contra hn
      have hle := le_of_not_gt hn
      set d := min xm ((sThr gam v km xm - ah) / (gam * v)) with hd_def
      have hdpos : 0 < d := lt_min hb (div_pos hd hc)
      have hdle : gam * v * d ≤ sThr gam v km xm - ah := by
        have := min_le_right xm ((sThr gam v km xm - ah) / (gam * v))
        rw [← hd_def] at this
        calc gam * v * d ≤ gam * v * ((sThr gam v km xm - ah) / (gam * v)) :=
              mul_le_mul_of_nonneg_left this hc.le
          _ = _ := by field_simp
      have hy : xm - d ∈ Set.Icc 0 xbar :=
        ⟨by linarith [min_le_left xm ((sThr gam v km xm - ah) / (gam * v))], by linarith⟩
      have e1 := obj_dn (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km)
        (show xm - d ≤ xm by linarith)
      have e2 := obj_up (ah := ah) (gam := gam) (v := v) (kp := kp) (km := km) hle
      have h3 := hxo (xm - d) hy
      simp only [sub_sub_cancel] at e1
      have : 0 ≤ (bThr gam v kp xm - sThr gam v km xm + (sThr gam v km xm - ah)) * (x - xm) := by
        nlinarith [sub_nonneg.2 hle]
      nlinarith [sq_nonneg (x - xm), mul_pos hdpos hd]
  refine ⟨⟨x0, hopt0, fun y hy => ?_⟩, hchar⟩
  by_contra hne
  have hm : (y + x0) / 2 ∈ Set.Icc 0 xbar :=
    ⟨by linarith [hy.1.1, hx0.1], by linarith [hy.1.2, hx0.2]⟩
  have h1 := hy.2 x0 hx0
  have h2 := hopt0.2 y hy.1
  have h3 := hopt0.2 _ hm
  have := obj_mid (ah := ah) (xm := xm) hg hv hkp hkm hne
  linarith

end Part1

/-! ### Gaussian tails, standardization and sums -/

section Gauss

/-- The standard normal tail `Q(t) = N(0,1)(t, ∞)`. -/
def Q (t : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Ioi t)

lemma Q_antitone : Antitone Q := fun _ _ h => measureReal_mono (Set.Ioi_subset_Ioi h)

lemma Q_neg (t : ℝ) : Q (-t) = 1 - Q t := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h1 : (gaussianReal 0 1).real (Set.Ioi (-t)) = (gaussianReal 0 1).real (Set.Iio t) := by
    have hm := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rw [neg_zero] at hm
    conv_lhs => rw [← hm]
    rw [map_measureReal_apply measurable_neg measurableSet_Ioi]
    congr 1; ext x; simp
  have h2 : (gaussianReal 0 1).real (Set.Iio t) = 1 - (gaussianReal 0 1).real (Set.Ici t) := by
    rw [← Set.compl_Ici, measureReal_compl measurableSet_Ici, probReal_univ]
  have h3 : (gaussianReal 0 1).real (Set.Ici t) = (gaussianReal 0 1).real (Set.Ioi t) := by
    simp only [measureReal_def]; rw [measure_congr Ioi_ae_eq_Ici.symm]
  simp only [Q]; rw [h1, h2, h3]

lemma sqrt_nn_pos {w : ℝ≥0} (hw : w ≠ 0) : 0 < Real.sqrt (w : ℝ) :=
  Real.sqrt_pos.2 (lt_of_le_of_ne w.2 (by simpa [eq_comm] using hw))

/-- Standardization: for `X ~ N(m, w)`, `P(X > c) = Q((c - m)/√w)`. -/
lemma prob_gt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {w : ℝ≥0}
    (hw : w ≠ 0) (hX : HasLaw X (gaussianReal m w) P) (c : ℝ) :
    P.real {ω | c < X ω} = Q ((c - m) / Real.sqrt w) := by
  have hs := sqrt_nn_pos hw
  have h1 := gaussianReal_sub_const hX m
  rw [sub_self] at h1
  have h2 : HasLaw (fun x : ℝ => x / Real.sqrt w) (gaussianReal 0 1) (gaussianReal 0 w) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_div_const, zero_div]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt w.coe_nonneg]
    exact div_self (by simpa using hw)
  have hY := h2.comp h1
  have e : {ω | c < X ω} = {ω | (c - m) / Real.sqrt w < ((fun x : ℝ => x / Real.sqrt w) ∘
      (fun ω => X ω - m)) ω} := by
    ext ω; simp only [Set.mem_ofPred_eq, Function.comp, div_lt_div_iff_of_pos_right hs]
    constructor <;> intro h <;> linarith
  rw [e, hY.measureReal_eq (p := fun y => (c - m) / Real.sqrt w < y) measurableSet_Ioi]
  rfl

/-- A finite sum of independent Gaussians is Gaussian. -/
lemma hasLaw_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (e : ι → Ω → ℝ) (m : ι → ℝ) (v : ι → ℝ≥0) (hind : iIndepFun e P)
    (hl : ∀ j, HasLaw (e j) (gaussianReal (m j) (v j)) P) (s : Finset ι) :
    HasLaw (fun ω => ∑ j ∈ s, e j ω) (gaussianReal (∑ j ∈ s, m j) (∑ j ∈ s, v j)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, gaussianReal_zero_var]
    exact hasLaw_dirac_of_ae_eq (ae_of_all _ fun _ => rfl)
  | insert a s ha ih =>
    have hi : IndepFun (∑ j ∈ s, e j) (e a) P :=
      hind.indepFun_finsetSum_of_notMem₀ (fun j => (hl j).aemeasurable) ha
    have hi' : IndepFun (fun ω => ∑ j ∈ s, e j ω) (e a) P := by
      convert hi using 1; ext ω; simp [Finset.sum_apply]
    have h := hi'.hasLaw_add ih (hl a)
    rw [gaussianReal_conv_gaussianReal] at h
    simp only [Finset.sum_insert ha]
    convert h using 2
    · simp [add_comm]
    · rw [add_comm]
    · rw [add_comm]

/-- The sample mean of `n` independent `N(m, v)` variables is `N(m, v/n)`. -/
lemma hasLaw_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (e : Fin n → Ω → ℝ) (m : ℝ) (v : ℝ≥0) (hind : iIndepFun e P)
    (hl : ∀ j, HasLaw (e j) (gaussianReal m v) P) :
    HasLaw (fun ω => mean (fun j => e j ω)) (gaussianReal m (v / (n : ℝ≥0))) P := by
  have hs := hasLaw_sum e (fun _ => m) (fun _ => v) hind hl Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : HasLaw (fun x : ℝ => x / n) (gaussianReal m (v / (n : ℝ≥0)))
      (gaussianReal (n * m) (n * v)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_div_const]
    congr 1
    · field_simp
    · apply NNReal.eq
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
      field_simp
  exact h2.comp hs

/-- Part 2's rule for independent `N(m, v)` observations. -/
lemma gauss_rule {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (e : Fin n → Ω → ℝ) (m b δ ε z : ℝ) (v : ℝ≥0) (hn : 0 < n) (hv : v ≠ 0)
    (hz : IsUpperQuantile ε z) (hind : iIndepFun e P) (hl : ∀ j, HasLaw (e j) (gaussianReal m v) P) :
    (m ≤ b → P.real (gaussBuy e v z b) ≤ ε) ∧
    (0 < δ → b + δ ≤ m → 4 * v * z ^ 2 / δ ^ 2 ≤ n → 1 - ε ≤ P.real (gaussBuy e v z b)) := by
  have hQz : Q z = ε := hz
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hsv := sqrt_nn_pos hv
  have hM := hasLaw_mean hn e m v hind hl
  have hvn : ((v / (n : ℝ≥0) : ℝ≥0) : ℝ) = v / n := by simp
  have hsq : Real.sqrt ((v / (n : ℝ≥0) : ℝ≥0) : ℝ) = Real.sqrt v / Real.sqrt n := by
    rw [hvn, Real.sqrt_div' _ hnr.le]
  have hP : P.real (gaussBuy e v z b) = Q (z + (b - m) * Real.sqrt n / Real.sqrt v) := by
    have e1 : gaussBuy e v z b = {ω | b + Real.sqrt v * z / Real.sqrt n < mean (fun j => e j ω)} := by
      ext ω; simp only [gaussBuy, Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
    rw [e1, prob_gt (by simpa [hn.ne'] using hv) hM, hsq]
    congr 1
    field_simp
    ring
  rw [hP]
  refine ⟨fun hmb => ?_, fun hδ hmb hlen => ?_⟩
  · rw [← hQz]; apply Q_antitone
    have : 0 ≤ (b - m) * Real.sqrt n / Real.sqrt v := by
      apply div_nonneg (mul_nonneg (by linarith) hsn.le) hsv.le
    linarith
  · -- `δ √n ≥ 2 √v |z|`
    have hkey : 2 * Real.sqrt v * |z| ≤ δ * Real.sqrt n := by
      have h1 : (2 * Real.sqrt v * |z|) ^ 2 ≤ (δ * Real.sqrt n) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt v.coe_nonneg, Real.sq_sqrt hnr.le, sq_abs]
        rw [div_le_iff₀ (by positivity)] at hlen
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
    have hge : 2 * |z| ≤ (m - b) * Real.sqrt n / Real.sqrt v := by
      rw [le_div_iff₀ hsv]
      nlinarith [mul_le_mul_of_nonneg_right (show δ ≤ m - b by linarith) hsn.le]
    have ht : z + (b - m) * Real.sqrt n / Real.sqrt v ≤ -z := by
      have : (b - m) * Real.sqrt n / Real.sqrt v = -((m - b) * Real.sqrt n / Real.sqrt v) := by ring
      rw [this]; linarith [le_abs_self z]
    have := Q_antitone ht
    rw [Q_neg, hQz] at this
    exact this

theorem gaussSufficient : GaussSufficient := by
  intro Ω _ P _ n e α b δ ε z v hn hv hz hind hl
  exact gauss_rule P n e α b δ ε z v hn hv hz hind hl

end Gauss

/-! ### Part 2: strictness of the tail, the order of `z_ε`, the lower bound's arithmetic, Bayes -/

section Part2

lemma Q_zero : Q 0 = 1 / 2 := by
  have := Q_neg 0; rw [neg_zero] at this; linarith

lemma Q_strictAnti : StrictAnti Q := by
  intro a b hab
  have hsplit : Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := (Set.Ioc_union_Ioi_eq_Ioi hab.le).symm
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioi b) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx')
  have hpos : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
        fun x _ => gaussianPDFReal_nonneg _ _ _),
      ← intervalIntegral.integral_of_le hab.le]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (integrable_gaussianPDFReal 0 1).intervalIntegrable
      (fun x _ => gaussianPDFReal_pos _ _ _ one_ne_zero) hab
  show Q b < Q a
  simp only [Q]
  rw [hsplit, measureReal_union hdisj measurableSet_Ioi]
  linarith

lemma Q_le_iff {a b : ℝ} : Q a ≤ Q b ↔ b ≤ a := Q_strictAnti.le_iff_ge

lemma quantile_nonneg {ε z : ℝ} (hz : IsUpperQuantile ε z) (hε : ε ≤ 1 / 2) : 0 ≤ z := by
  by_contra h
  have := Q_strictAnti (lt_of_not_ge h)
  have hQ : Q z = ε := hz
  rw [Q_zero, hQ] at this
  linarith

/-- The Bhattacharyya integrand is `exp(-δ²/(8v))` times the midpoint density. -/
lemma aff_point (b δ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.sqrt (gaussianPDFReal b v x * gaussianPDFReal (b + δ) v x)
      = Real.exp (-δ ^ 2 / (8 * v)) * gaussianPDFReal (b + δ / 2) v x := by
  have hvp : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by simpa [eq_comm] using hv)
  rw [← Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _))]
  congr 1
  simp only [gaussianPDFReal]
  have e : ∀ A u₁ u₂ c u₃ : ℝ, u₁ + u₂ = 2 * c + 2 * u₃ →
      A * Real.exp u₁ * (A * Real.exp u₂) = (Real.exp c * (A * Real.exp u₃)) ^ 2 := by
    intro A u₁ u₂ c u₃ h
    have : Real.exp u₁ * Real.exp u₂ = (Real.exp c * Real.exp u₃) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, h]; push_cast; ring_nf
    calc A * Real.exp u₁ * (A * Real.exp u₂) = A ^ 2 * (Real.exp u₁ * Real.exp u₂) := by ring
      _ = _ := by rw [this]; ring
  apply e
  field_simp
  ring

lemma affinity_eq (b δ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    affinity b (b + δ) v = Real.exp (-δ ^ 2 / (8 * v)) := by
  simp only [affinity, aff_point b δ hv, integral_const_mul, integral_gaussianPDFReal_eq_one _ hv,
    mul_one]

lemma lower_arith (δ ε : ℝ) (v : ℝ≥0) (n : ℕ) (hv : v ≠ 0) (hδ : 0 < δ) (hε : 0 < ε)
    (hε4 : ε < 1 / 4) (h : 1 - Real.sqrt (1 - Real.exp (-δ ^ 2 / (8 * v)) ^ (2 * n)) ≤ 2 * ε) :
    4 * v / δ ^ 2 * Real.log (1 / (4 * ε)) ≤ n := by
  have hvp : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by simpa [eq_comm] using hv)
  set r := Real.exp (-δ ^ 2 / (8 * v)) ^ (2 * n) with hr
  have hr' : r = Real.exp (-(n * δ ^ 2 / (4 * v))) := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; field_simp; ring
  have h1 : (1 - 2 * ε) ^ 2 ≤ 1 - r := by
    have h0 : 0 ≤ 1 - 2 * ε := by linarith
    have hneg : -δ ^ 2 / (8 * v) ≤ 0 := by
      rw [neg_div]; have : 0 < δ ^ 2 / (8 * v) := by positivity
      linarith
    have hr1 : r ≤ 1 := pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.2 hneg)
    have := pow_le_pow_left₀ h0 (show 1 - 2 * ε ≤ Real.sqrt (1 - r) by linarith) 2
    rwa [Real.sq_sqrt (by linarith)] at this
  have h2 : r ≤ 4 * ε := by nlinarith
  rw [hr'] at h2
  have h3 : -(n * δ ^ 2 / (4 * v)) ≤ Real.log (4 * ε) := (Real.le_log_iff_exp_le (by linarith)).2 h2
  rw [one_div, Real.log_inv]
  have : 4 * (v : ℝ) / δ ^ 2 * -Real.log (4 * ε) ≤ 4 * v / δ ^ 2 * (n * δ ^ 2 / (4 * v)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc _ ≤ _ := this
    _ = n := by field_simp

theorem lowerBoundArithmetic : LowerBoundArithmetic :=
  ⟨fun b δ _ hv => affinity_eq b δ hv, fun δ ε v n hv hδ hε hε4 h => lower_arith δ ε v n hv hδ hε hε4 h⟩

/-- `Q(z) ≥ e^{-z²}/(2√2)`, from `x² ≤ 2z² + 2(x - z)²` and `N(z, 1/2)(z, ∞) = 1/2`. -/
lemma Q_lower (z : ℝ) : Real.exp (-z ^ 2) / 4 ≤ Q z := by
  have h12 : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  set c : ℝ := Real.exp (-z ^ 2) / Real.sqrt 2 with hc
  have hcpos : 0 ≤ c := by positivity
  have hpt : ∀ x, ENNReal.ofReal c * gaussianPDF z (1 / 2) x ≤ gaussianPDF 0 1 x := by
    intro x
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul hcpos]
    apply ENNReal.ofReal_le_ofReal
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, one_div, NNReal.coe_inv, NNReal.coe_ofNat]
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have e1 : Real.sqrt (2 * Real.pi * 2⁻¹) = Real.sqrt Real.pi := by congr 1; ring
    have e2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
    rw [e1, e2, hc]
    have hexp : Real.exp (-z ^ 2) * Real.exp (-(x - z) ^ 2 / (2 * 2⁻¹)) ≤ Real.exp (-(x - 0) ^ 2 / 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [sq_nonneg (x - 2 * z)]
    have : Real.exp (-z ^ 2) / Real.sqrt 2 * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(x - z) ^ 2 / (2 * 2⁻¹)))
        = (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ * (Real.exp (-z ^ 2) * Real.exp (-(x - z) ^ 2 / (2 * 2⁻¹))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hN : (gaussianReal z (1 / 2)).real (Set.Ioi z) = 1 / 2 := by
    have hX : HasLaw (fun x : ℝ => x) (gaussianReal z (1 / 2)) (gaussianReal z (1 / 2)) :=
      ⟨by fun_prop, Measure.map_id⟩
    have := prob_gt h12 hX z
    rw [sub_self, zero_div, Q_zero] at this
    exact this
  have hle : ENNReal.ofReal c * gaussianReal z (1 / 2) (Set.Ioi z)
      ≤ gaussianReal 0 1 (Set.Ioi z) := by
    rw [gaussianReal_apply _ one_ne_zero, gaussianReal_apply _ h12,
      ← lintegral_const_mul _ (measurable_gaussianPDF _ _)]
    exact lintegral_mono fun x => hpt x
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos] at hr
  change c * (gaussianReal z (1 / 2)).real (Set.Ioi z) ≤ Q z at hr
  rw [hN] at hr
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have : Real.exp (-z ^ 2) / 4 ≤ c * (1 / 2) := by
    rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    have := Real.exp_pos (-z ^ 2)
    nlinarith
  linarith

theorem quantileOrder : QuantileOrder := by
  intro ε z hε _ hz
  have hQ : Q z = ε := hz
  have h := Q_lower z
  rw [hQ] at h
  have h4 : Real.exp (-z ^ 2) ≤ 4 * ε := by linarith
  have := (Real.le_log_iff_exp_le (by linarith)).2 h4
  rw [one_div, Real.log_inv]
  linarith

/-- `P(N(m, w) > b) = Q((b - m)/√w)`. -/
lemma gauss_gt (m b : ℝ) {w : ℝ≥0} (hw : w ≠ 0) :
    (gaussianReal m w).real (Set.Ioi b) = Q ((b - m) / Real.sqrt w) := by
  have hX : HasLaw (fun x : ℝ => x) (gaussianReal m w) (gaussianReal m w) :=
    ⟨by fun_prop, Measure.map_id⟩
  exact prob_gt hw hX b

lemma bayes_iff (m b ε z : ℝ) {w : ℝ≥0} (hw : w ≠ 0) (hz : IsUpperQuantile ε z) :
    1 - ε ≤ (gaussianReal m w).real (Set.Ioi b) ↔ z * Real.sqrt w ≤ m - b := by
  have hQ : Q z = ε := hz
  have hs := sqrt_nn_pos hw
  rw [gauss_gt m b hw, ← hQ, ← Q_neg, Q_le_iff, div_le_iff₀ hs]
  constructor <;> intro h <;> linarith

theorem bayes : Bayes := by
  refine ⟨fun m b ε z w hw hz => bayes_iff m b ε z hw hz, fun s2 sig2 n hs hsig => ?_⟩
  field_simp
  ring

theorem floor : Floor := by
  intro m b ε z pinf p hpinf hp hz hε
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; simp at hp; linarith
  have hpi0 : pinf.toNNReal ≠ 0 := by simpa using hpinf
  have hcoe : ((pinf.toNNReal : ℝ≥0) : ℝ) = pinf := Real.coe_toNNReal _ hpinf.le
  have hsp := sqrt_nn_pos hp0
  have hspi : 0 < Real.sqrt pinf := Real.sqrt_pos.2 hpinf
  have hsle : Real.sqrt pinf ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
  refine ⟨fun hbm => ?_, fun h => ?_⟩
  · rw [gauss_gt m b hp0, gauss_gt m b hpi0, hcoe]
    apply Q_antitone
    rw [div_le_div_iff₀ hspi hsp]
    nlinarith
  · have h1 := (bayes_iff m b ε z hp0 hz).1 h
    have hz0 := quantile_nonneg hz hε
    nlinarith [mul_le_mul_of_nonneg_left hsle hz0]

end Part2

/-! ### Parts 3 and 4 -/

section Part34

/-- One tail of Hoeffding's inequality (`AX-06`, Mathlib) at `t = R √(2 log(1/ε)/n)`. -/
lemma hoeff_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (R ε : ℝ) (hn : 0 < n) (hR : 0 < R) (hε : 0 < ε) (hε1 : ε < 1)
    (hind : iIndepFun X P) (hm : ∀ j, Measurable (X j)) (hb : ∀ j ω, |X j ω| ≤ R)
    (h0 : ∀ j, P[X j] = 0) :
    P.real {ω | n * (R * Real.sqrt (2 * Real.log (1 / ε) / n)) ≤ ∑ j, X j ω} ≤ ε := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  set t := R * Real.sqrt (2 * Real.log (1 / ε) / n) with ht
  have ht2 : t ^ 2 = R ^ 2 * (2 * Real.log (1 / ε) / n) := by
    rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
  have hsub : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (X j) ((‖R - (-R)‖₊ / 2) ^ 2) P := fun j _ =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm j).aemeasurable
      (ae_of_all _ fun ω => abs_le.1 (hb j ω)) (h0 j)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := n * t) (by positivity)
  have hc : ((∑ _j : Fin n, ((‖R - (-R)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ) = n * R ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [sub_neg_eq_add, ← two_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  have hexp : Real.exp (-((n : ℝ) * t) ^ 2 / (2 * ((∑ _j : Fin n,
      ((‖R - (-R)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ))) = ε := by
    rw [hc, mul_pow, ht2]
    have : -((n : ℝ) ^ 2 * (R ^ 2 * (2 * Real.log (1 / ε) / n))) / (2 * (n * R ^ 2))
        = -Real.log (1 / ε) := by field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    simp
  rw [hexp] at hH
  exact hH

lemma prob_compl_ge {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) : 1 - P.real Aᶜ ≤ P.real A := by
  have := measureReal_union_le A Aᶜ (μ := P)
  rw [Set.union_compl_self, probReal_univ] at this
  linarith

theorem hoeffSufficient : HoeffSufficient := by
  intro Ω _ P _ n zA α R b δ ε hn hR hε hε1 hind hm hb h0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set t := R * Real.sqrt (2 * Real.log (1 / ε) / n) with ht
  have htn : 0 ≤ t := by positivity
  have hmean : ∀ ω, mean (fun j => α + zA j ω) = α + (∑ j, zA j ω) / n := by
    intro ω; simp only [mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; field_simp
  refine ⟨fun hab => ?_, fun hδ hab hlen => ?_⟩
  · refine le_trans (measureReal_mono ?_) (hoeff_tail P zA R ε hn hR hε hε1 hind hm hb h0)
    intro ω hω
    simp only [hoeffBuy, Set.mem_ofPred_eq, hmean] at hω ⊢
    rw [← ht] at hω
    have : t < (∑ j, zA j ω) / n := by linarith
    rw [lt_div_iff₀ hnr] at this
    linarith
  · -- `δ ≥ 2t`
    have hL : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
    have h2t : 2 * t ≤ δ := by
      have ht2 : t ^ 2 = R ^ 2 * (2 * Real.log (1 / ε) / n) := by
        rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
      have : (2 * t) ^ 2 ≤ δ ^ 2 := by
        rw [mul_pow, ht2]
        rw [div_le_iff₀ (by positivity)] at hlen
        have : R ^ 2 * (2 * Real.log (1 / ε) / n) * n = R ^ 2 * (2 * Real.log (1 / ε)) := by
          field_simp
        have h4 : 2 ^ 2 * (R ^ 2 * (2 * Real.log (1 / ε) / n)) * n ≤ δ ^ 2 * n := by
          nlinarith
        exact le_of_mul_le_mul_right h4 hnr
      exact (pow_le_pow_iff_left₀ (by positivity) hδ.le two_ne_zero).1 this
    have hind' : iIndepFun (fun j ω => -zA j ω) P :=
      hind.comp (fun _ x => -x) (fun _ => measurable_neg)
    have htail := hoeff_tail P (fun j ω => -zA j ω) R ε hn hR hε hε1 hind'
      (fun j => (hm j).neg) (fun j ω => by rw [abs_neg]; exact hb j ω)
      (fun j => by rw [integral_neg, h0 j, neg_zero])
    rw [← ht] at htail
    refine le_trans ?_ (prob_compl_ge P _)
    have : P.real (hoeffBuy (fun j ω => α + zA j ω) R ε b)ᶜ ≤ ε := by
      refine le_trans (measureReal_mono ?_) htail
      intro ω hω
      simp only [hoeffBuy, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, hmean] at hω ⊢
      rw [← ht] at hω
      have : (∑ j, zA j ω) / n ≤ -t := by linarith
      rw [div_le_iff₀ hnr] at this
      simp only [Finset.sum_neg_distrib]
      linarith
    linarith

theorem mixingCertificate : MixingCertificate := by
  refine ⟨fun C cs cB s2 B neff δ ε hC hε hδ hD => ?_, ?_⟩
  · set D := cs * s2 + cB * (δ / 2) * B
    rw [← le_div_iff₀' hC, ← Real.le_log_iff_exp_le (by positivity), Real.log_div hε.ne' hC.ne',
      Real.log_div hC.ne' hε.ne', neg_le, neg_sub, le_div_iff₀ hD, div_le_iff₀ (by positivity)]
    have e : 4 * cs * s2 + 2 * cB * δ * B = 4 * D := by simp only [D]; ring
    rw [e]
    constructor <;> intro h <;> nlinarith
  · intro Ω _ P _ zbar α b C cs cB s2 B neff r δ ε hr hrδ hB hbound
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · refine le_trans (measureReal_mono ?_) (hB.1.trans hbound)
      intro ω hω; simp only [Set.mem_ofPred_eq] at hω ⊢; linarith
    · refine le_trans ?_ (prob_compl_ge P _)
      have : P.real {ω | b < α + zbar ω - r}ᶜ ≤ ε := by
        refine le_trans (measureReal_mono ?_) (hB.2.trans hbound)
        intro ω hω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢; linarith
      linarith

end Part34

/-! ### Part 5 -/

section Part5

variable {phi q s2 : ℝ}

/-- The other root `p₋ = [(q - σ²(1-φ²)) - √(...)]/2`. -/
def pMinus (phi q s2 : ℝ) : ℝ :=
  ((q - s2 * (1 - phi ^ 2)) - Real.sqrt ((q - s2 * (1 - phi ^ 2)) ^ 2 + 4 * q * s2)) / 2

lemma phi_sq_lt (hphi : |phi| < 1) : phi ^ 2 < 1 := by
  have := sq_abs phi
  nlinarith [abs_nonneg phi]

lemma roots_sign (hq : 0 < q) (hs : 0 < s2) : 0 < pInf phi q s2 ∧ pMinus phi q s2 < 0 := by
  set A := q - s2 * (1 - phi ^ 2)
  set D := Real.sqrt (A ^ 2 + 4 * q * s2)
  have hD2 : D ^ 2 = A ^ 2 + 4 * q * s2 := Real.sq_sqrt (by positivity)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hlt : |A| < D := by
    have : |A| ^ 2 < D ^ 2 := by rw [sq_abs, hD2]; nlinarith [mul_pos hq hs]
    exact (pow_lt_pow_iff_left₀ (abs_nonneg A) hD0 two_ne_zero).1 this
  constructor
  · show 0 < (A + D) / 2; linarith [neg_abs_le A]
  · show (A - D) / 2 < 0; linarith [le_abs_self A]

/-- `p² - A p - q σ² = (p - p_∞)(p - p₋)`. -/
lemma quad_factor (hq : 0 < q) (hs : 0 < s2) (p : ℝ) :
    p ^ 2 - (q - s2 * (1 - phi ^ 2)) * p - q * s2 = (p - pInf phi q s2) * (p - pMinus phi q s2) := by
  have hD2 : Real.sqrt ((q - s2 * (1 - phi ^ 2)) ^ 2 + 4 * q * s2) ^ 2
      = (q - s2 * (1 - phi ^ 2)) ^ 2 + 4 * q * s2 := Real.sq_sqrt (by positivity)
  simp only [pInf, pMinus]
  nlinarith [hD2]

/-- `f(p) - p = -(p - p_∞)(p - p₋)/(σ² + p)`. -/
lemma f_sub (hq : 0 < q) (hs : 0 < s2) {p : ℝ} (hp : 0 ≤ p) :
    fR phi q s2 p - p = -((p - pInf phi q s2) * (p - pMinus phi q s2)) / (s2 + p) := by
  rw [← quad_factor hq hs p]
  simp only [fR]
  field_simp
  ring

lemma f_le_iff (hq : 0 < q) (hs : 0 < s2) {p : ℝ} (hp : 0 ≤ p) :
    fR phi q s2 p ≤ p ↔ pInf phi q s2 ≤ p := by
  have hm := (roots_sign (phi := phi) hq hs).2
  have hsp : 0 < s2 + p := by linarith
  have hpm : 0 < p - pMinus phi q s2 := by linarith
  rw [← sub_nonpos, f_sub hq hs hp, div_nonpos_iff]
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · linarith
    · by_contra hc
      have : (p - pInf phi q s2) * (p - pMinus phi q s2) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hpm
      linarith
  · intro h
    right
    exact ⟨by nlinarith, hsp.le⟩

lemma f_eq_iff (hq : 0 < q) (hs : 0 < s2) {p : ℝ} (hp : 0 ≤ p) :
    fR phi q s2 p = p ↔ p = pInf phi q s2 := by
  have hm := (roots_sign (phi := phi) hq hs).2
  have hsp : 0 < s2 + p := by linarith
  have hpm : 0 < p - pMinus phi q s2 := by linarith
  rw [← sub_eq_zero, f_sub hq hs hp, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, sub_eq_zero,
    sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact h
    · linarith
    · linarith
  · intro h; exact Or.inl (Or.inl h)

lemma f_mono (hs : 0 < s2) {p p' : ℝ} (hp : 0 ≤ p) (hpp : p ≤ p') :
    fR phi q s2 p ≤ fR phi q s2 p' := by
  simp only [fR]
  have h1 : p * s2 / (s2 + p) ≤ p' * s2 / (s2 + p') := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hs.le hs.le) (sub_nonneg.2 hpp)]
  have := mul_le_mul_of_nonneg_left h1 (sq_nonneg phi)
  simp only [mul_div_assoc] at this ⊢
  nlinarith

theorem riccati : Riccati := by
  intro phi q s2 hphi hq hs
  have ⟨hpos, _⟩ := roots_sign (phi := phi) hq hs
  have hp2 := phi_sq_lt hphi
  have hfix : fR phi q s2 (pInf phi q s2) = pInf phi q s2 := (f_eq_iff hq hs hpos.le).2 rfl
  refine ⟨hpos, hfix, fun p hp h => (f_eq_iff hq hs hp).1 h, ?_, fun p0 hp0 => ?_⟩
  · -- `f(q/(1-φ²)) ≤ q/(1-φ²)`
    set M := q / (1 - phi ^ 2)
    have hM : 0 < M := div_pos hq (by linarith)
    rw [← f_le_iff hq hs hM.le]
    simp only [fR]
    have h1 : M * s2 / (s2 + M) ≤ M := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hne : (1 - phi ^ 2) ≠ 0 := (by linarith : (0 : ℝ) < 1 - phi ^ 2).ne'
    have h2 : phi ^ 2 * M + q = M := by simp only [M]; field_simp; ring
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg phi)
    rw [mul_div_assoc] at this ⊢
    nlinarith
  · have hge : ∀ t, pInf phi q s2 ≤ pIter phi q s2 p0 t := by
      intro t
      induction t with
      | zero => exact hp0
      | succ t ih =>
        show pInf phi q s2 ≤ fR phi q s2 (pIter phi q s2 p0 t)
        calc pInf phi q s2 = fR phi q s2 (pInf phi q s2) := hfix.symm
          _ ≤ _ := f_mono hs hpos.le ih
    have hanti : Antitone (pIter phi q s2 p0) := by
      refine antitone_nat_of_succ_le fun t => ?_
      show fR phi q s2 (pIter phi q s2 p0 t) ≤ pIter phi q s2 p0 t
      exact (f_le_iff hq hs (hpos.le.trans (hge t))).2 (hge t)
    refine ⟨hanti, hge, ?_⟩
    have hbdd : BddBelow (Set.range (pIter phi q s2 p0)) :=
      ⟨pInf phi q s2, by rintro _ ⟨t, rfl⟩; exact hge t⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    set L := ⨅ t, pIter phi q s2 p0 t
    have hL : pInf phi q s2 ≤ L := le_ciInf hge
    have hcont : ContinuousAt (fR phi q s2) L := by
      unfold fR
      have : s2 + L ≠ 0 := by linarith
      fun_prop (disch := assumption)
    have h1 : Tendsto (fun t => pIter phi q s2 p0 (t + 1)) atTop (𝓝 (fR phi q s2 L)) :=
      hcont.tendsto.comp hlim
    have h2 : Tendsto (fun t => pIter phi q s2 p0 (t + 1)) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat 1).2 hlim
    have hfL : fR phi q s2 L = L := tendsto_nhds_unique h1 h2
    rw [(f_eq_iff hq hs (hpos.le.trans hL)).1 hfL] at hlim
    exact hlim

lemma pInf_le_of (hq : 0 < q) (hs : 0 < s2) {p : ℝ} (hp : 0 ≤ p) (h : fR phi q s2 p ≤ p) :
    pInf phi q s2 ≤ p := (f_le_iff hq hs hp).1 h

theorem limits : Limits := by
  intro phi hphi
  have hp2 := phi_sq_lt hphi
  refine ⟨fun s2 hs => ?_, fun q hq => ⟨?_, ?_⟩⟩
  · have hc : Continuous (fun q => pInf phi q s2) := by unfold pInf; fun_prop
    have h0 : pInf phi 0 s2 = 0 := by
      have ha : 0 < s2 * (1 - phi ^ 2) := mul_pos hs (by linarith)
      simp only [pInf, zero_sub, zero_mul, mul_zero, add_zero, neg_sq,
        Real.sqrt_sq ha.le]
      ring
    have := hc.tendsto 0
    rwa [h0] at this
  · intro s hs t ht hst
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < t := ht
    have hpt := (roots_sign (phi := phi) hq ht').1
    apply pInf_le_of hq hs' hpt.le
    have hfix : fR phi q t (pInf phi q t) = pInf phi q t := (f_eq_iff hq ht' hpt.le).2 rfl
    calc fR phi q s (pInf phi q t) ≤ fR phi q t (pInf phi q t) := by
          simp only [fR]
          have : phi ^ 2 * pInf phi q t * s / (s + pInf phi q t)
              ≤ phi ^ 2 * pInf phi q t * t / (t + pInf phi q t) := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith [mul_nonneg (mul_nonneg (sq_nonneg phi) (sq_nonneg (pInf phi q t)))
              (sub_nonneg.2 hst)]
          linarith
      _ = pInf phi q t := hfix
  · set M := q / (1 - phi ^ 2) with hMdef
    have h1p : 0 < 1 - phi ^ 2 := by linarith
    have hM : 0 < M := div_pos hq h1p
    set c := phi ^ 2 * M ^ 2 / (1 - phi ^ 2)
    have hlow : Tendsto (fun s2 : ℝ => M - c / s2) atTop (𝓝 M) := by
      have := (tendsto_const_nhds (x := c)).div_atTop tendsto_id
      simpa using (tendsto_const_nhds (x := M)).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s2 hs
      have ⟨hpos, _⟩ := roots_sign (phi := phi) hq hs
      have hup := (riccati phi q s2 hphi hq hs).2.2.2.1
      have hfix : fR phi q s2 (pInf phi q s2) = pInf phi q s2 := (f_eq_iff hq hs hpos.le).2 rfl
      set p := pInf phi q s2
      -- `s2/(s2 + p) ≥ 1 - p/s2`
      have hfr : p - p ^ 2 / s2 ≤ p * s2 / (s2 + p) := by
        rw [le_div_iff₀ (by linarith)]
        have : (p - p ^ 2 / s2) * (s2 + p) = p * s2 - p ^ 3 / s2 := by field_simp; ring
        rw [this]
        have : 0 ≤ p ^ 3 / s2 := by positivity
        linarith
      simp only [fR] at hfix
      have e : phi ^ 2 * (p * s2 / (s2 + p)) = phi ^ 2 * p * s2 / (s2 + p) := by ring
      have h3 : phi ^ 2 * (p - p ^ 2 / s2) + q ≤ p := by
        have := mul_le_mul_of_nonneg_left hfr (sq_nonneg phi)
        linarith
      have hpM : p ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hpos.le hup 2
      have h4 : phi ^ 2 * (p ^ 2 / s2) ≤ phi ^ 2 * (M ^ 2 / s2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpM hs.le) (sq_nonneg phi)
      show M - c / s2 ≤ p
      have hne : (1 - phi ^ 2) ≠ 0 := h1p.ne'
      have hc : M - c / s2 = (q - phi ^ 2 * (M ^ 2 / s2)) / (1 - phi ^ 2) := by
        simp only [c, hMdef]; field_simp
      rw [hc, div_le_iff₀ h1p]
      have : phi ^ 2 * (p - p ^ 2 / s2) = phi ^ 2 * p - phi ^ 2 * (p ^ 2 / s2) := by ring
      nlinarith
    · filter_upwards [eventually_gt_atTop 0] with s2 hs
      exact (riccati phi q s2 hphi hq hs).2.2.2.1

end Part5

/-! ### Part 6 -/

section Part6

/-- `w'f` for `f ~ N(λ, Σ)` is `N(w'λ, w'Σw)`. -/
lemma inner_law {K : ℕ} (lam w : EuclideanSpace ℝ (Fin K)) {Sf : Matrix (Fin K) (Fin K) ℝ}
    (hS : Sf.PosSemidef) :
    (multivariateGaussian lam Sf).map (fun x => inner ℝ w x)
      = gaussianReal (inner ℝ w lam) (w ⬝ᵥ Sf *ᵥ w).toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian lam Sf) (innerSL ℝ w)
  have hmem : MemLp id 2 (multivariateGaussian lam Sf) := IsGaussian.memLp_two_id
  have hmean : (multivariateGaussian lam Sf)[innerSL ℝ w] = inner ℝ w lam := by
    simp only [innerSL_apply_apply]
    have := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id (μ := multivariateGaussian lam Sf)) w
    simp only [id] at this
    rw [this, integral_id_multivariateGaussian]
  have hvar : Var[innerSL ℝ w; multivariateGaussian lam Sf] = w ⬝ᵥ Sf *ᵥ w := by
    rw [← covarianceBilin_multivariateGaussian hS w w, covarianceBilin_self hmem]
    rfl
  rw [hmean, hvar] at h
  exact h

theorem spanning : Spanning := by
  intro K Ω _ P _ n zA f lam w Sf α b δ ε z s2 hn hs2 hS hz hind hpair hzl hfl tau u vU
  have htau : 0 ≤ tau := by
    have := hS.dotProduct_mulVec_nonneg (WithLp.ofLp w)
    simpa [tau] using this
  have hvU : (vU : ℝ) = s2 + tau := by
    simp only [vU, NNReal.coe_add, Real.coe_toNNReal _ htau]
  have hvU0 : vU ≠ 0 := by
    intro h
    have : (vU : ℝ) = 0 := by rw [h]; rfl
    rw [hvU] at this
    have : (0 : ℝ) < s2 := lt_of_le_of_ne s2.coe_nonneg (by simpa [eq_comm] using hs2)
    linarith
  have hlaw : ∀ j, HasLaw (u j) (gaussianReal (α + inner ℝ w lam) vU) P := by
    intro j
    have hY : HasLaw (fun ω => inner ℝ w (f j ω)) (gaussianReal (inner ℝ w lam) tau.toNNReal) P :=
      HasLaw.fun_comp ⟨by fun_prop, inner_law lam w hS⟩ (hfl j)
    have hI : IndepFun (zA j) (fun ω => inner ℝ w (f j ω)) P :=
      (hpair j).comp (φ := id) (ψ := fun x => inner ℝ w x) measurable_id (by fun_prop)
    have hsum := hI.hasLaw_add (hzl j) hY
    rw [gaussianReal_conv_gaussianReal, zero_add] at hsum
    have h2 := gaussianReal_const_add hsum α
    convert h2 using 2
    · simp only [u, Pi.add_apply]; ring
    · ring
  have hindU : iIndepFun u P := by
    have := hind.comp (fun _ (p : ℝ × EuclideanSpace ℝ (Fin K)) => α + p.1 + inner ℝ w p.2)
      (fun _ => by fun_prop)
    exact this
  have hR := gauss_rule P n u (α + inner ℝ w lam) b δ ε z vU hn hvU0 hz hindU hlaw
  refine ⟨htau, hlaw, hR.1, fun hδ hab hlen => hR.2 hδ hab ?_, fun hw => ?_⟩
  · have hs : (0 : ℝ) < s2 := lt_of_le_of_ne s2.coe_nonneg (by simpa [eq_comm] using hs2)
    rw [hvU]
    have : (1 + tau / s2) * (4 * s2 * z ^ 2 / δ ^ 2) = 4 * (s2 + tau) * z ^ 2 / δ ^ 2 := by
      field_simp
    rw [← this]; exact hlen
  · have : tau = 0 := by simp [tau, hw]
    rw [this, zero_div, add_zero]

end Part6

/-! ### Part 7 -/

section Part7

open Standalone.M5LearningAimTwoSpeeds in
theorem pooledVariance : PooledVariance := by
  intro N s2 sb2 sig2 t hN hs hsb hsig
  have hdec := (Novel.M5LearningAimTwoSpeedsProof.twoVariances N s2 sb2 sig2 hN hs hsb hsig).1 t
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hones : ∀ u : Fin N → ℝ, ones N *ᵥ u = fun _ => 1 ⬝ᵥ u := by
    intro u; ext i; simp [ones, mulVec, dotProduct]
  have hPc : ∀ u : Fin N → ℝ, Pc N *ᵥ u = (N : ℝ)⁻¹ • fun _ => 1 ⬝ᵥ u := by
    intro u; rw [Pc, smul_mulVec, hones]
  have hPr : ∀ u : Fin N → ℝ, Pr N *ᵥ u = u - (N : ℝ)⁻¹ • fun _ => 1 ⬝ᵥ u := by
    intro u; rw [Pr, sub_mulVec, one_mulVec, hPc]
  have h11 : (1 : Fin N → ℝ) ⬝ᵥ 1 = N := by simp [dotProduct]
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · rw [hdec, add_mulVec, smul_mulVec, smul_mulVec, hPc, hPr, h11]
    have : (1 : Fin N → ℝ) - (N : ℝ)⁻¹ • (fun _ => (N : ℝ)) = 0 := by
      ext i; simp [hNr]
    rw [this, smul_zero, add_zero, dotProduct_smul, dotProduct_smul]
    have : (1 : Fin N → ℝ) ⬝ᵥ (fun _ => (N : ℝ)) = N * N := by simp [dotProduct]
    rw [this]
    simp only [smul_eq_mul]
    field_simp
  · simp only [pc, Standalone.M5PartialAdjustmentSplit.pvar, one_div]
  · rw [hdec, add_mulVec, smul_mulVec, smul_mulVec, hPc, hPr, hu]
    have : (fun _ : Fin N => (0 : ℝ)) = 0 := rfl
    simp [this, dotProduct_smul]

/-- The average of independent `N(m_i, v)` variables is `N(Σ m_i/N, v/N)`. -/
lemma hasLaw_avg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (X : Fin N → Ω → ℝ) (m : Fin N → ℝ) (v : ℝ≥0) (hind : iIndepFun X P)
    (hl : ∀ i, HasLaw (X i) (gaussianReal (m i) v) P) :
    HasLaw (fun ω => (∑ i, X i ω) / N) (gaussianReal ((∑ i, m i) / N) (v / (N : ℝ≥0))) P := by
  have hs := hasLaw_sum X m (fun _ => v) hind hl Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : HasLaw (fun x : ℝ => x / N) (gaussianReal ((∑ i, m i) / N) (v / (N : ℝ≥0)))
      (gaussianReal (∑ i, m i) (N * v)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_div_const]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
    field_simp
  exact h2.comp hs

theorem commonTilt : CommonTilt := by
  intro N Ω _ P _ n e α b δ ε z s2 hN hn hs2 hz hind hcoord hl ebar abar vbar
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlaw : ∀ j, HasLaw (ebar j) (gaussianReal abar vbar) P := fun j =>
    hasLaw_avg hN (fun i ω => e j ω i) α s2 (hcoord j) (hl j)
  have hind' : iIndepFun ebar P :=
    hind.comp (fun _ (x : Fin N → ℝ) => (∑ i, x i) / N) (fun _ => by fun_prop)
  have hvb : vbar ≠ 0 := by
    simp only [vbar, ne_eq, div_eq_zero_iff, hs2, Nat.cast_eq_zero, false_or]; omega
  have hR := gauss_rule P n ebar abar b δ ε z vbar hn hvb hz hind' hlaw
  refine ⟨hlaw, hR.1, fun hδ hab hlen => hR.2 hδ hab ?_⟩
  have : ((vbar : ℝ≥0) : ℝ) = s2 / N := by simp [vbar]
  rw [this]
  have e2 : 4 * (s2 / N : ℝ) * z ^ 2 / δ ^ 2 = 1 / (N : ℝ) * (4 * s2 * z ^ 2 / δ ^ 2) := by ring
  rw [e2]; exact hlen

end Part7


/-! ### Part 3's lower bound -/

section TwoPoint

open Finset in
theorem twoPointLower : TwoPointLower := by
  intro n R b δ ε φ hδ hδR hε hε16 hφ hcert
  have hR : 0 < R := by linarith
  set R' := R - δ / 2 with hR'
  have hR'3 : 3 * R / 4 ≤ R' := by linarith
  have hR'pos : 0 < R' := by linarith
  set x := δ / (2 * R') with hx
  have hx0 : 0 < x := by positivity
  have hx3 : x ≤ 1 / 3 := by rw [hx, div_le_iff₀ (by positivity)]; linarith
  set q0 : Bool → ℝ := fun s => if s then (1 - x) / 2 else (1 + x) / 2
  set q1 : Bool → ℝ := fun s => if s then (1 + x) / 2 else (1 - x) / 2
  set Z0 : Bool → ℝ := fun s => if s then δ / 2 + R' else δ / 2 - R'
  set Z1 : Bool → ℝ := fun s => if s then R' - δ / 2 else -R' - δ / 2
  have hxR : x * R' = δ / 2 := by rw [hx]; field_simp
  have h0 : InBR R q0 Z0 := by
    refine ⟨fun s => ?_, ?_, ?_, fun s => ?_⟩
    · cases s <;> simp only [q0] <;> simp <;> linarith
    · simp [q0]; ring
    · simp [q0, Z0]; linear_combination (-1 : ℝ) * hxR
    · cases s <;> simp only [Z0] <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  have h1 : InBR R q1 Z1 := by
    refine ⟨fun s => ?_, ?_, ?_, fun s => ?_⟩
    · cases s <;> simp only [q1] <;> simp <;> linarith
    · simp [q1]; ring
    · simp [q1, Z1]; linear_combination hxR
    · cases s <;> simp only [Z1] <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  have hc0 := (hcert Bool q0 Z0 h0 b).1 le_rfl
  have hc1 := (hcert Bool q1 Z1 h1 (b + δ)).2 le_rfl
  have hobs : ∀ σ : Fin n → Bool, (fun j => b + δ + Z1 (σ j)) = fun j => b + Z0 (σ j) := by
    intro σ; funext j; cases σ j <;> simp [Z0, Z1] <;> ring
  set c : (Fin n → Bool) → ℝ := fun σ => φ (fun j => b + Z0 (σ j))
  have hprod : ∀ f : Bool → ℝ, ∑ σ : Fin n → Bool, ∏ j, f (σ j) = (∑ s, f s) ^ n := by
    intro f
    rw [← Fintype.prod_sum (fun _ : Fin n => f)]
    simp
  have hsum0 : ∑ σ : Fin n → Bool, ∏ j, q0 (σ j) = 1 := by rw [hprod]; simp [q0]; ring_nf
  have hsum1 : ∑ σ : Fin n → Bool, ∏ j, q1 (σ j) = 1 := by rw [hprod]; simp [q1]; ring_nf
  have hq0 : ∀ s, 0 ≤ q0 s := h0.1
  have hq1 : ∀ s, 0 ≤ q1 s := h1.1
  have hle := Novel.M4BoundedLawRateProof.lecam (fun σ : Fin n → Bool => ∏ j, q0 (σ j))
    (fun σ => ∏ j, q1 (σ j)) c (fun σ => ∏ j, Real.sqrt (q0 (σ j) * q1 (σ j))) ε
    (fun σ => prod_nonneg fun j _ => hq0 _) (fun σ => prod_nonneg fun j _ => hq1 _)
    hsum0.le hsum1.le (fun σ => hφ _)
    (by simpa [buyProb, c] using hc0)
    (by
      have : buyProb n q1 Z1 (b + δ) φ = ∑ σ : Fin n → Bool, (∏ j, q1 (σ j)) * c σ := by
        simp only [buyProb, c, hobs]
      rw [this] at hc1
      simp only [mul_sub, mul_one, sum_sub_distrib, hsum1]
      linarith)
    (fun σ => prod_nonneg fun j _ => Real.sqrt_nonneg _)
    (fun σ => by
      rw [← prod_pow, ← prod_mul_distrib]
      exact prod_congr rfl fun j _ => Real.sq_sqrt (mul_nonneg (hq0 _) (hq1 _)))
  -- the affinity is `√(1 - x²)` per observation
  have haff : ∑ s, Real.sqrt (q0 s * q1 s) = Real.sqrt (1 - x ^ 2) := by
    rw [Fintype.sum_bool]
    simp only [q0, q1, ↓reduceIte, Bool.false_eq_true]
    have e1 : (1 - x) / 2 * ((1 + x) / 2) = (1 - x ^ 2) / 4 := by ring
    have e2 : (1 + x) / 2 * ((1 - x) / 2) = (1 - x ^ 2) / 4 := by ring
    rw [e1, e2, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [hprod (fun s => Real.sqrt (q0 s * q1 s)), haff, ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by nlinarith)] at hle
  -- logarithms
  set y := x ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy9 : y ≤ 1 / 9 := by rw [hy]; nlinarith
  have hpos : 0 < 1 - y := by linarith
  have hL := Real.log_le_log (pow_pos hpos n) hle
  rw [Real.log_pow] at hL
  have hlog1 := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 - y)⁻¹ ≤ 9 / 8 := by rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have hlog4 : Real.log (4 * ε) = -Real.log (1 / (4 * ε)) := by
    rw [one_div, Real.log_inv, neg_neg]
  -- `n y (9/8) ≥ log(1/(4ε))`
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : Real.log (1 / (4 * ε)) ≤ n * y * (9 / 8) := by
    have h1 : 1 - (1 - y)⁻¹ ≥ -(y * (9 / 8)) := by
      have : (1 - y)⁻¹ = 1 + y * (1 - y)⁻¹ := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left hinv hy0.le]
    have h2 : -(y * (9 / 8)) ≤ Real.log (1 - y) := hlog1.trans' h1
    nlinarith [mul_le_mul_of_nonneg_left h2 hn0]
  -- `log(1/(4ε)) ≥ log(1/ε)/2`
  have hL16 : Real.log 16 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have h16 : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hsplit : Real.log (1 / (4 * ε)) = Real.log (1 / ε) - Real.log 4 := by
    rw [show 1 / (4 * ε) = (1 / ε) / 4 by field_simp, Real.log_div (by positivity) (by norm_num)]
  -- `y ≤ 4δ²/(9R²)`
  have hyR : y * (9 * R ^ 2) ≤ 4 * δ ^ 2 := by
    have : y = δ ^ 2 / (4 * R' ^ 2) := by rw [hy, hx]; field_simp; ring
    rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hR'3 hR'3 (by positivity) hR'pos.le]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hLpos : 0 ≤ Real.log (1 / ε) := le_trans (by positivity) hL16
  nlinarith [mul_le_mul_of_nonneg_left hyR hn0]

end TwoPoint

/-- Claim 039. -/
theorem proof : Standalone.M7DataSupportActiveChange.statement :=
  ⟨decision, gaussSufficient, lowerBoundArithmetic, quantileOrder, bayes, hoeffSufficient,
    mixingCertificate, riccati, floor, limits, spanning, pooledVariance, commonTilt, twoPointLower⟩

end

end Novel.M7DataSupportActiveChangeProof

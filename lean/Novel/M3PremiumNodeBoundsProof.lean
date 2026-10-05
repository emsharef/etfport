import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Standalone.M3PremiumNodeBounds
import Novel.M3EtfChannelSandwichProof

/-!
# Proof of claim 023: the premium of future ETF adjustment decomposes across observations

This proof uses claim 011's, claim 012's and claim 022's proof modules
(`depends_on: [11, 12, 22]`; Q-04).

* **Decomposition.** At each node `V₁^R = -exp(-ρ c^R_y)`, and
  `H₀^R = Σ_y P₀(y) V₁^R`. So `H₀^E/H₀^N = Σ_y w_y exp(-ρ G_y)`, and `φ` is the aggregate. The
  aggregate is monotone in each node value because the weights are positive on nodes.
* **Node lower bounds.** Any feasible ETF-only trade lower-bounds the node certainty equivalent.
  - Sure-sign bounds take the full trade and shift wealth by a constant.
  - Risk-adjusted bounds take a partial trade `ε` and apply Mathlib's Hoeffding lemma
    (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) under the tilted node
    measure. This gives `f(ε) ≥ f(0) + r ε - ρ s² ε²/2` without differentiating, and nothing is
    re-proved (AGENTS.md rule 21).
* **Node caps.** These are claim 022's pathwise bound, restricted to node paths.
-/

namespace Novel.M3PremiumNodeBoundsProof

open Matrix Finset MeasureTheory Standalone.M3FiniteContinuation Standalone.M3PremiumNodeBounds
  Novel.M3FiniteContinuationProof
open Standalone.M2ScoreAccounting hiding gain
open Standalone.M3EtfChannelSandwich (cR phi RootOpt beta saInst allActive)
open scoped Classical

set_option linter.unusedSectionVars false

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T] {P : M3 n K S T}

/-! ### Weighted averages with conditions only on positive weights -/

lemma wlt {ι : Type} [Fintype ι] {w f : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (hf : ∀ i, 0 < w i → f i < c) : ∑ i, w i * f i < c := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra hne
    push Not at hne
    have : ∑ i, w i = 0 := sum_eq_zero fun i _ => le_antisymm (hne i) (hw i)
    linarith
  have hpos : 0 < ∑ i, w i * (c - f i) :=
    sum_pos' (fun i _ => by
      rcases (hw i).lt_or_eq with h | h
      · exact mul_nonneg h.le (by linarith [hf i h])
      · rw [← h, zero_mul])
      ⟨j, mem_univ j, mul_pos hj (by linarith [hf j hj])⟩
  have e : ∑ i, w i * (c - f i) = c - ∑ i, w i * f i := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, h1, one_mul]
  linarith

lemma wgt {ι : Type} [Fintype ι] {w f : ι → ℝ} {c : ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (hf : ∀ i, 0 < w i → c < f i) : c < ∑ i, w i * f i := by
  have := wlt (f := fun i => -f i) (c := -c) hw h1 fun i hi => by linarith [hf i hi]
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

lemma wlt2 {a : T → ℝ} {b : S → ℝ} (ha : ∀ t, 0 ≤ a t) (ha1 : ∑ t, a t = 1) (hb : ∀ s, 0 ≤ b s)
    (hb1 : ∑ s, b s = 1) {f : T → S → ℝ} {c : ℝ} (hf : ∀ t s, 0 < a t → 0 < b s → f t s < c) :
    ∑ t, ∑ s, a t * b s * f t s < c := by
  have e : ∑ t, ∑ s, a t * b s * f t s = ∑ t, a t * ∑ s, b s * f t s := by
    simp only [mul_sum]; exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring
  rw [e]
  exact wlt ha ha1 fun t ht => wlt hb hb1 fun s hs => hf t s ht hs

lemma wgt2 {a : T → ℝ} {b : S → ℝ} (ha : ∀ t, 0 ≤ a t) (ha1 : ∑ t, a t = 1) (hb : ∀ s, 0 ≤ b s)
    (hb1 : ∑ s, b s = 1) {f : T → S → ℝ} {c : ℝ} (hf : ∀ t s, 0 < a t → 0 < b s → c < f t s) :
    c < ∑ t, ∑ s, a t * b s * f t s := by
  have e : ∑ t, ∑ s, a t * b s * f t s = ∑ t, a t * ∑ s, b s * f t s := by
    simp only [mul_sum]; exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by ring
  rw [e]
  exact wgt ha ha1 fun t ht => wgt hb hb1 fun s hs => hf t s ht hs

/-! ### Nodes -/

section Node

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
include hS hu

lemma node_nn {y : Obs n K} (hy : y ∈ Yset P) : (∀ i, 0 ≤ x1 P y u₀ i) ∧ 0 ≤ h1 P u₀ :=
  node_state hS hu ⟨y, hy⟩

lemma node_wealth_pos {y : Obs n K} (hy : y ∈ Yset P) : 0 < h1 P u₀ + ∑ i, x1 P y u₀ i := by
  obtain ⟨_, _, _, _, _, _, hx0, hh0, hW0, _⟩ := setting_parts hS
  have hroot := post_pos hS hx0 hh0 (by simpa [W0] using hW0) hu
  have hsx : 0 ≤ ∑ i, x1 P y u₀ i := sum_nonneg fun i _ => (node_nn hS hu hy).1 i
  by_cases hh : 0 < h1 P u₀
  · linarith
  · have hh' : h1 P u₀ = 0 := le_antisymm (not_lt.mp hh) (node_nn hS hu hy).2
    have hsum : 0 < ∑ i, (P.D.x0 i + u₀ i) := by
      have e : h1 P u₀ = P.D.h0 - ∑ i, u₀ i - cost P.D u₀ := rfl
      linarith
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ))
      (g := fun i => P.D.x0 i + u₀ i) (by simpa using hsum)
    have hxi : 0 < x1 P y u₀ i := mul_pos (gross_pos hS ⟨y, hy⟩ i) hi
    have := single_le_sum (f := fun i => x1 P y u₀ i) (fun j _ => (node_nn hS hu hy).1 j)
      (mem_univ i)
    rw [hh']; linarith

lemma condW_pos {y : Obs n K} (hy : y ∈ Yset P) {r : Cls} {u : Inst 1 n → ℝ}
    (hfe : Feas1 P r (x1 P y u₀) (h1 P u₀) u) (t : T) (s : S) :
    0 < condW P (x1 P y u₀) (h1 P u₀) u t s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hg⟩ := setting_parts hS
  have hp := post_pos hS (node_nn hS hu hy).1 (node_nn hS hu hy).2 (node_wealth_pos hS hu hy) hfe
  have hcash := hfe.2.1
  have hxu := hfe.1
  unfold condW
  have hsum : 0 ≤ ∑ i, (x1 P y u₀ i + u i) * (1 + ret P.D (P.par t) s i) :=
    sum_nonneg fun i _ => mul_nonneg (hxu i) (hg t s i).le
  by_cases hc : 0 < h1 P u₀ - ∑ i, u i - cost P.D u
  · linarith
  · have hc0 : h1 P u₀ - ∑ i, u i - cost P.D u = 0 := le_antisymm (not_lt.mp hc) hcash
    have hpos : 0 < ∑ i, (x1 P y u₀ i + u i) := by linarith
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ))
      (g := fun i => x1 P y u₀ i + u i) (by simpa using hpos)
    have := single_le_sum (f := fun i => (x1 P y u₀ i + u i) * (1 + ret P.D (P.par t) s i))
      (fun j _ => mul_nonneg (hxu j) (hg t s j).le) (mem_univ i)
    have := mul_pos hi (hg t s i)
    linarith

omit hu in
lemma post_sum {y : Obs n K} (hP : 0 < P0 P y) : ∑ t, post P y t = 1 := by
  simp only [post, hP, ↓reduceIte]
  rw [← Finset.sum_div, div_eq_one_iff_eq hP.ne']
  rfl

lemma V1_node {y : Obs n K} (hy : IsNode P y) (r : Cls) :
    -1 < V1 P r (x1 P y u₀) (h1 P u₀) (post P y) ∧ V1 P r (x1 P y u₀) (h1 P u₀) (post P y) < 0 := by
  obtain ⟨hρ, hq, hq1, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  obtain ⟨u, hfe, -, hV⟩ := cond_attain hS r (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  rw [hV]
  have hps := post_sum hS hy.2
  refine ⟨wgt2 (post_nonneg hS y) hps hq hq1 fun t s _ _ => ?_,
    wlt2 (post_nonneg hS y) hps hq hq1 fun t s _ _ => ?_⟩
  · exact U_gt P hρ (div_pos (condW_pos hS hu hy.1 hfe t s) hW0)
  · unfold U; linarith [Real.exp_pos (-P.rho * (condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D))]

lemma exp_nodeCE {y : Obs n K} (hy : IsNode P y) (r : Cls) :
    Real.exp (-P.rho * nodeCE P r u₀ y) = -V1 P r (x1 P y u₀) (h1 P u₀) (post P y) := by
  have hρ := hS.1
  have hV := (V1_node hS hu hy r).2
  unfold nodeCE
  rw [show -P.rho * (-(1 / P.rho) * Real.log (-V1 P r (x1 P y u₀) (h1 P u₀) (post P y)))
    = Real.log (-V1 P r (x1 P y u₀) (h1 P u₀) (post P y)) by field_simp, Real.exp_log (by linarith)]

lemma gain_nonneg {y : Obs n K} (hy : IsNode P y) : 0 ≤ gain P u₀ y := by
  have h := Novel.M3EtfChannelSandwichProof.V1_mono hS (r := .N) (r' := .E)
    (fun u h => Novel.M3EtfChannelSandwichProof.feas_NE h) (post P y)
    (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  have := Novel.M3EtfChannelSandwichProof.cmono hS (V1_node hS hu hy .E).2 h
  unfold gain nodeCE; linarith

/-! The decomposition. -/

lemma nodeMass_eq (r : Cls) (y : Obs n K) (hy : y ∈ Yset P) :
    (if 0 < P0 P y then P0 P y * Real.exp (-P.rho * nodeCE P r u₀ y) else 0)
      = -(if 0 < P0 P y then P0 P y * V1 P r (x1 P y u₀) (h1 P u₀) (post P y) else 0) := by
  split_ifs with hP
  · rw [exp_nodeCE hS hu ⟨hy, hP⟩]; ring
  · simp

lemma H0_eq' (r : Cls) : H0 P r u₀ = -∑ y ∈ Yset P,
    (if 0 < P0 P y then P0 P y * Real.exp (-P.rho * nodeCE P r u₀ y) else 0) := by
  rw [H0, ← sum_neg_distrib]
  exact sum_congr rfl fun y hy => by rw [nodeMass_eq hS hu r y hy, neg_neg]

lemma mass_sum_pos : 0 < ∑ y ∈ Yset P, nodeMass P u₀ y := by
  have h := (Novel.M3EtfChannelSandwichProof.H0_range hS .N hu).2
  rw [H0_eq' hS hu .N] at h
  simp only [nodeMass]; linarith

lemma weight_nonneg (y : Obs n K) : 0 ≤ weight P u₀ y := by
  unfold weight nodeMass
  refine div_nonneg ?_ (mass_sum_pos hS hu).le
  split_ifs with h
  · exact mul_nonneg h.le (Real.exp_pos _).le
  · exact le_rfl

lemma weight_pos {y : Obs n K} (hy : IsNode P y) : 0 < weight P u₀ y := by
  unfold weight nodeMass
  simp only [hy.2, ↓reduceIte]
  exact div_pos (mul_pos hy.2 (Real.exp_pos _)) (mass_sum_pos hS hu)

lemma weight_sum : ∑ y ∈ Yset P, weight P u₀ y = 1 := by
  unfold weight
  rw [← Finset.sum_div, div_self (mass_sum_pos hS hu).ne']

lemma weight_zero {y : Obs n K} (hy : ¬ 0 < P0 P y) : weight P u₀ y = 0 := by
  unfold weight nodeMass; simp only [hy, ↓reduceIte, zero_div]

lemma exists_node : ∃ y, IsNode P y := by
  by_contra h
  have := mass_sum_pos hS hu
  have hz : ∑ y ∈ Yset P, nodeMass P u₀ y = 0 :=
    sum_eq_zero fun y hy => by
      have hp : ¬ 0 < P0 P y := fun hp => h ⟨y, hy, hp⟩
      unfold nodeMass; simp only [hp, ↓reduceIte]
  linarith

lemma wsum_pos (ℓ : Obs n K → ℝ) : 0 < ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ y) := by
  obtain ⟨y0, hy0⟩ := exists_node hS hu
  exact lt_of_lt_of_le (mul_pos (weight_pos hS hu hy0) (Real.exp_pos _))
    (single_le_sum (f := fun y => weight P u₀ y * Real.exp (-P.rho * ℓ y))
      (fun y _ => mul_nonneg (weight_nonneg hS hu y) (Real.exp_pos _).le) hy0.1)

lemma agg_mono {ℓ ℓ' : Obs n K → ℝ} (h : ∀ y, IsNode P y → ℓ y ≤ ℓ' y) :
    agg P u₀ ℓ ≤ agg P u₀ ℓ' := by
  have hρ := hS.1
  have hsum : ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ' y)
      ≤ ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ y) := by
    refine sum_le_sum fun y hy => ?_
    by_cases hp : 0 < P0 P y
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [h y ⟨hy, hp⟩]))
        (weight_nonneg hS hu y)
    · simp [weight_zero hS hu hp]
  have hlog := Real.log_le_log (wsum_pos hS hu ℓ') hsum
  unfold agg
  have : 0 < 1 / P.rho := by positivity
  nlinarith

lemma agg_strict {ℓ ℓ' : Obs n K → ℝ} (h : ∀ y, IsNode P y → ℓ y ≤ ℓ' y)
    (hs : ∃ y, IsNode P y ∧ ℓ y < ℓ' y) : agg P u₀ ℓ < agg P u₀ ℓ' := by
  have hρ := hS.1
  obtain ⟨y0, hy0, hlt⟩ := hs
  have hsum : ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ' y)
      < ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ y) := by
    refine sum_lt_sum (fun y hy => ?_) ⟨y0, hy0.1, ?_⟩
    · by_cases hp : 0 < P0 P y
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [h y ⟨hy, hp⟩]))
          (weight_nonneg hS hu y)
      · simp [weight_zero hS hu hp]
    · exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by nlinarith)) (weight_pos hS hu hy0)
  have hlog := Real.log_lt_log (wsum_pos hS hu ℓ') hsum
  unfold agg
  have : 0 < 1 / P.rho := by positivity
  nlinarith

lemma agg_const (c : ℝ) : agg P u₀ (fun _ => c) = c := by
  have hρ := hS.1
  unfold agg
  rw [← Finset.sum_mul, weight_sum hS hu, one_mul, Real.log_exp]
  field_simp

lemma phi_agg : phi P u₀ = agg P u₀ (gain P u₀) := by
  have hρ := hS.1
  have hN := (Novel.M3EtfChannelSandwichProof.H0_range hS .N hu).2
  have hE := (Novel.M3EtfChannelSandwichProof.H0_range hS .E hu).2
  set Z := ∑ y ∈ Yset P, nodeMass P u₀ y
  have hZ : Z = -H0 P .N u₀ := by rw [H0_eq' hS hu .N, neg_neg]; rfl
  have hsum : ∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * gain P u₀ y) = -H0 P .E u₀ / Z := by
    rw [H0_eq' hS hu .E, neg_neg, Finset.sum_div]
    refine sum_congr rfl fun y hy => ?_
    unfold weight nodeMass gain
    split_ifs with hp
    · rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
      congr 2; ring
    · simp
  unfold phi agg cR
  rw [hsum, Real.log_div (by linarith) (by rw [hZ]; linarith), hZ]
  ring

lemma exists_min_max : ∃ y₁ y₂, IsNode P y₁ ∧ IsNode P y₂ ∧
    gain P u₀ y₁ ≤ phi P u₀ ∧ phi P u₀ ≤ gain P u₀ y₂ := by
  set Nd := (Yset P).filter fun y => 0 < P0 P y
  obtain ⟨y0, hy0⟩ := exists_node hS hu
  have hne : Nd.Nonempty := ⟨y0, mem_filter.mpr hy0⟩
  obtain ⟨y1, hy1, hmin⟩ := Nd.exists_min_image (gain P u₀) hne
  obtain ⟨y2, hy2, hmax⟩ := Nd.exists_max_image (gain P u₀) hne
  have n1 : IsNode P y1 := mem_filter.mp hy1
  have n2 : IsNode P y2 := mem_filter.mp hy2
  refine ⟨y1, y2, n1, n2, ?_, ?_⟩
  · rw [phi_agg hS hu, ← agg_const hS hu (gain P u₀ y1)]
    exact agg_mono hS hu fun y hy => hmin y (mem_filter.mpr hy)
  · rw [phi_agg hS hu, ← agg_const hS hu (gain P u₀ y2)]
    exact agg_mono hS hu fun y hy => hmax y (mem_filter.mpr hy)

end Node

/-! ### Hoeffding's lemma for a finite weighted law (from Mathlib) -/

lemma hoeff_fin {ι : Type} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {Y : ι → ℝ} (h0 : ∑ i, p i * Y i = 0) {a b : ℝ} (hab : ∀ i, 0 < p i → a ≤ Y i ∧ Y i ≤ b)
    (t : ℝ) : ∑ i, p i * Real.exp (t * Y i) ≤ Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < p j := by
    by_contra hne
    push Not at hne
    have : ∑ i, p i = 0 := sum_eq_zero fun i _ => le_antisymm (hne i) (hp i)
    linarith
  have hab' : a ≤ b := (hab j hj).1.trans (hab j hj).2
  -- clamp `Y` off the support
  set Y' : ι → ℝ := fun i => if 0 < p i then Y i else a
  have hY'p : ∀ i, p i * Y' i = p i * Y i := fun i => by
    simp only [Y']; split_ifs with h
    · rfl
    · rw [le_antisymm (not_lt.mp h) (hp i), zero_mul, zero_mul]
  have hY'e : ∀ i, p i * Real.exp (t * Y' i) = p i * Real.exp (t * Y i) := fun i => by
    simp only [Y']; split_ifs with h
    · rfl
    · rw [le_antisymm (not_lt.mp h) (hp i), zero_mul, zero_mul]
  have hY'in : ∀ i, Y' i ∈ Set.Icc a b := fun i => by
    simp only [Y']; split_ifs with h
    · exact hab i h
    · exact ⟨le_rfl, hab'⟩
  have h0' : ∑ i, p i * Y' i = 0 := by rw [← h0]; exact sum_congr rfl fun i _ => hY'p i
  rw [← sum_congr rfl fun i _ => hY'e i]
  let _ : MeasurableSpace ι := ⊤
  have : DiscreteMeasurableSpace ι := ⟨fun _ => trivial⟩
  set μ : Measure ι := ∑ i, ENNReal.ofReal (p i) • Measure.dirac i with hμ
  have hsing : ∀ x, μ {x} = ENNReal.ofReal (p x) := by
    intro x
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hp1, ENNReal.ofReal_one]
  have hreal : ∀ x, μ.real {x} = p x := fun x => by
    rw [measureReal_def, hsing, ENNReal.toReal_ofReal (hp x)]
  have hint : ∀ f : ι → ℝ, ∫ x, f x ∂μ = ∑ x, p x * f x := fun f => by
    rw [integral_fintype Integrable.of_finite]; simp [hreal]
  have hH := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := Y')
    (a := a) (b := b) (Measurable.of_discrete.aemeasurable) (ae_of_all _ hY'in)
    (by rw [hint]; exact h0')
  have hm := hH.mgf_le t
  rw [ProbabilityTheory.mgf, hint] at hm
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = ((b - a) / 2) ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rwa [hc] at hm

/-! ### Node trades -/

lemma cost_single (P : M3 n K S T) (i : Inst 1 n) (v : ℝ) :
    cost P.D (Pi.single i v) = P.D.kplus i * max v 0 + P.D.kminus i * max (-v) 0 := by
  unfold cost
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp

lemma condW_single (P : M3 n K S T) (x : Inst 1 n → ℝ) (h : ℝ) (i : Inst 1 n) (v : ℝ) (t : T) (s : S) :
    condW P x h (Pi.single i v) t s
      = condW P x h 0 t s - v - cost P.D (Pi.single i v) + v * (1 + ret P.D (P.par t) s i) := by
  unfold condW
  simp only [cost_zero, Pi.zero_apply, sum_const_zero, sub_zero, add_zero]
  have e1 : ∑ k, (Pi.single i v : Inst 1 n → ℝ) k = v := by simp
  have e3 : ∑ k, (Pi.single i v : Inst 1 n → ℝ) k * (1 + ret P.D (P.par t) s k)
      = v * (1 + ret P.D (P.par t) s i) := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]; simp
  have e2 : ∑ k, (x k + (Pi.single i v : Inst 1 n → ℝ) k) * (1 + ret P.D (P.par t) s k)
      = ∑ k, x k * (1 + ret P.D (P.par t) s k) + v * (1 + ret P.D (P.par t) s i) := by
    rw [← e3, ← Finset.sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
  rw [e1, e2]; ring

section NodeTrade

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y)
include hS hu hy

lemma V1N_eq : V1 P .N (x1 P y u₀) (h1 P u₀) (post P y)
    = condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0 := by
  obtain ⟨u, hfe, -, hV⟩ := cond_attain hS .N (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  have : u = 0 := hfe.2.2
  rw [hV, this]

lemma nodeCE_ge {u : Inst 1 n → ℝ} (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) :
    -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) u) ≤ nodeCE P .E u₀ y := by
  obtain ⟨u', -, hmax, hV⟩ := cond_attain hS .E (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  have hle : condObj P (post P y) (x1 P y u₀) (h1 P u₀) u ≤ V1 P .E (x1 P y u₀) (h1 P u₀) (post P y) :=
    hV ▸ hmax u hfe
  exact Novel.M3EtfChannelSandwichProof.cmono hS (V1_node hS hu hy .E).2 hle

/-- A pathwise gain of at least `c` (normalized) on node paths gives `G_y ≥ c`. -/
lemma gain_ge_shift {u : Inst 1 n → ℝ} (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) (c : ℝ)
    (hpath : ∀ t s, NodePath P y t s →
      condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D + c ≤ condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D) :
    c ≤ gain P u₀ y := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  have hN := (V1_node hS hu hy .N).2
  rw [V1N_eq hS hu hy] at hN
  have hcmp : Real.exp (-P.rho * c) * condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0
      ≤ condObj P (post P y) (x1 P y u₀) (h1 P u₀) u := by
    unfold condObj
    rw [Finset.mul_sum]
    refine sum_le_sum fun t _ => ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun s _ => ?_
    by_cases hp : NodePath P y t s
    · have hU := U_mono P hρ (hpath t s hp)
      rw [Novel.M3EtfChannelSandwichProof.U_shift] at hU
      have hw := mul_nonneg (post_nonneg hS y t) (hq s)
      have := mul_le_mul_of_nonneg_left hU hw
      linarith
    · have hz : post P y t * P.D.q s = 0 := by
        rcases not_and_or.mp hp with h | h
        · rw [le_antisymm (not_lt.mp h) (post_nonneg hS y t), zero_mul]
        · rw [le_antisymm (not_lt.mp h) (hq s), mul_zero]
      rw [hz]; simp
  have hE := nodeCE_ge hS hu hy hfe
  have hneg : condObj P (post P y) (x1 P y u₀) (h1 P u₀) u < 0 := by
    obtain ⟨u', -, hmax, hV⟩ := cond_attain hS .E (post P y) (node_nn hS hu hy.1).1
      (node_nn hS hu hy.1).2
    have hle := hmax u hfe
    have hVE := (V1_node hS hu hy .E).2
    rw [hV] at hVE
    linarith
  have hlog := Real.log_le_log (by linarith)
    (by linarith : -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
      ≤ Real.exp (-P.rho * c) * -condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0)
  rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at hlog
  have hNce : nodeCE P .N u₀ y = -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0) := by
    unfold nodeCE; rw [V1N_eq hS hu hy]
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  unfold gain
  rw [hNce]
  have : -(1 / P.rho) * (-P.rho * c + Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0))
      ≤ -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) u) := by nlinarith
  rw [show -(1 / P.rho) * (-P.rho * c + Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0))
    = c + -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0) by
      field_simp; ring] at this
  linarith

/-- If every feasible ETF-only trade gains at most `c` (normalized) on node paths, `G_y ≤ c`. -/
lemma gain_le_shift (c : ℝ)
    (hpath : ∀ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u → ∀ t s, NodePath P y t s →
      condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D ≤ condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D + c) :
    gain P u₀ y ≤ c := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  obtain ⟨u, hfe, -, hV⟩ := cond_attain hS .E (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  have hN := (V1_node hS hu hy .N).2
  rw [V1N_eq hS hu hy] at hN
  have hcmp : condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
      ≤ Real.exp (-P.rho * c) * condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0 := by
    unfold condObj
    rw [Finset.mul_sum]
    refine sum_le_sum fun t _ => ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun s _ => ?_
    by_cases hp : NodePath P y t s
    · have hU := U_mono P hρ (hpath u hfe t s hp)
      rw [Novel.M3EtfChannelSandwichProof.U_shift] at hU
      have hw := mul_nonneg (post_nonneg hS y t) (hq s)
      have := mul_le_mul_of_nonneg_left hU hw
      linarith
    · have hz : post P y t * P.D.q s = 0 := by
        rcases not_and_or.mp hp with h | h
        · rw [le_antisymm (not_lt.mp h) (post_nonneg hS y t), zero_mul]
        · rw [le_antisymm (not_lt.mp h) (hq s), mul_zero]
      rw [hz]; simp
  have hE := (V1_node hS hu hy .E).2
  rw [hV] at hE
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) (by linarith))
    (by linarith : Real.exp (-P.rho * c) * -condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0
      ≤ -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u)
  rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at hlog
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  unfold gain nodeCE
  rw [hV, V1N_eq hS hu hy]
  have : -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) u)
      ≤ -(1 / P.rho) * (-P.rho * c + Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0)) := by
    nlinarith
  rw [show -(1 / P.rho) * (-P.rho * c + Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0))
    = c + -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0) by
      field_simp; ring] at this
  linarith

/-- The tilted-measure bound: an ETF-only trade whose normalized wealth change is `ε Z` gains at
least `ε r - ρ ε² σ²/2`, with `r` the tilted mean of `Z` and `2σ` a bracket of `Z` on node paths. -/
lemma gain_ge_tilt {u : Inst 1 n → ℝ} (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) (ε : ℝ)
    (Z : T → S → ℝ) (hZ : ∀ t s, condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D
      = condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D + ε * Z t s)
    {zl zu : ℝ} (hbr : ∀ t s, NodePath P y t s → zl ≤ Z t s ∧ Z t s ≤ zu) :
    ε * tiltMean P u₀ y Z - P.rho * ε ^ 2 * ((zu - zl) / 2) ^ 2 / 2 ≤ gain P u₀ y := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  set W := fun t s => condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D
  set om : T × S → ℝ := fun p => post P y p.1 * P.D.q p.2 * Real.exp (-P.rho * W p.1 p.2)
  have hom : ∀ p, 0 ≤ om p := fun p =>
    mul_nonneg (mul_nonneg (post_nonneg hS y p.1) (hq p.2)) (Real.exp_pos _).le
  set Om := ∑ p, om p
  have hcond0 : condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0 = -Om := by
    simp only [condObj, U, Om, om, Fintype.sum_prod_type, ← sum_neg_distrib]
    exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by simp only [W]; ring
  have hN := (V1_node hS hu hy .N).2
  rw [V1N_eq hS hu hy, hcond0] at hN
  have hOm : 0 < Om := by linarith
  set pw : T × S → ℝ := fun p => om p / Om
  have hpw : ∀ p, 0 ≤ pw p := fun p => div_nonneg (hom p) hOm.le
  have hpw1 : ∑ p, pw p = 1 := by simp only [pw]; rw [← Finset.sum_div, div_self hOm.ne']
  set r := tiltMean P u₀ y Z
  have hr : r = ∑ p, pw p * Z p.1 p.2 := by
    simp only [r, tiltMean, pw, om, W, Fintype.sum_prod_type, Om]
    rw [Finset.sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [Finset.sum_div]
    exact sum_congr rfl fun s _ => by ring
  have hcent : ∑ p, pw p * (Z p.1 p.2 - r) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hpw1, one_mul, ← hr, sub_self]
  have hsupp : ∀ p, 0 < pw p → zl - r ≤ Z p.1 p.2 - r ∧ Z p.1 p.2 - r ≤ zu - r := fun p hp => by
    have hom' : 0 < om p := (div_pos_iff_of_pos_right hOm).mp hp
    have h1 : 0 < post P y p.1 * P.D.q p.2 := (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hom'
    have ha : 0 < post P y p.1 := lt_of_le_of_ne (post_nonneg hS y p.1) (fun h => by
      rw [← h, zero_mul] at h1; exact lt_irrefl _ h1)
    have hb : 0 < P.D.q p.2 := lt_of_le_of_ne (hq p.2) (fun h => by
      rw [← h, mul_zero] at h1; exact lt_irrefl _ h1)
    have := hbr p.1 p.2 ⟨ha, hb⟩
    constructor <;> linarith [this.1, this.2]
  have hh := hoeff_fin hpw hpw1 hcent hsupp (-P.rho * ε)
  have hcondu : -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
      = ∑ p, om p * Real.exp (-P.rho * ε * r) * Real.exp (-P.rho * ε * (Z p.1 p.2 - r)) := by
    simp only [condObj, U, hZ, Fintype.sum_prod_type, ← sum_neg_distrib]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    simp only [om]
    rw [show -P.rho * (W t s + ε * Z t s)
      = -P.rho * W t s + -P.rho * ε * r + -P.rho * ε * (Z t s - r) by ring, Real.exp_add,
      Real.exp_add]
    ring
  have hsplit : ∑ p, om p * Real.exp (-P.rho * ε * r) * Real.exp (-P.rho * ε * (Z p.1 p.2 - r))
      = Om * Real.exp (-P.rho * ε * r) * ∑ p, pw p * Real.exp (-P.rho * ε * (Z p.1 p.2 - r)) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp only [pw]; field_simp
  rw [hsplit] at hcondu
  have hub : -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
      ≤ Om * Real.exp (-P.rho * ε * r) * Real.exp (((zu - r - (zl - r)) / 2) ^ 2 * (-P.rho * ε) ^ 2 / 2) := by
    rw [hcondu]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hE := nodeCE_ge hS hu hy hfe
  have hsum_pos : 0 < ∑ p, pw p * Real.exp (-P.rho * ε * (Z p.1 p.2 - r)) := by
    obtain ⟨p0, hp0⟩ : ∃ p, 0 < pw p := by
      by_contra hne; push Not at hne
      have : ∑ p, pw p = 0 := sum_eq_zero fun p _ => le_antisymm (hne p) (hpw p)
      linarith
    exact lt_of_lt_of_le (mul_pos hp0 (Real.exp_pos _))
      (single_le_sum (f := fun p => pw p * Real.exp (-P.rho * ε * (Z p.1 p.2 - r)))
        (fun p _ => mul_nonneg (hpw p) (Real.exp_pos _).le) (mem_univ p0))
  have hlpos : 0 < -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u := by
    rw [hcondu]; positivity
  have hlog := Real.log_le_log hlpos hub
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hOm.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp] at hlog
  have hNce : nodeCE P .N u₀ y = -(1 / P.rho) * Real.log Om := by
    unfold nodeCE; rw [V1N_eq hS hu hy, hcond0, neg_neg]
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  unfold gain
  rw [hNce]
  have key : -(1 / P.rho) * (Real.log Om + -P.rho * ε * r
      + ((zu - r - (zl - r)) / 2) ^ 2 * (-P.rho * ε) ^ 2 / 2)
      ≤ -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) u) := by nlinarith
  have e : -(1 / P.rho) * (Real.log Om + -P.rho * ε * r
      + ((zu - r - (zl - r)) / 2) ^ 2 * (-P.rho * ε) ^ 2 / 2)
      = -(1 / P.rho) * Real.log Om + (ε * r - P.rho * ε ^ 2 * ((zu - zl) / 2) ^ 2 / 2) := by
    field_simp; ring
  rw [e] at key
  linarith

end NodeTrade

lemma riskBound_opt {ρ r s H g : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hH : 0 ≤ H)
    (hg : ∀ ε, 0 ≤ ε → ε ≤ H → ε * r - ρ * ε ^ 2 * s ^ 2 / 2 ≤ g) :
    riskBound ρ r s H ≤ g ∧ (¬ r ≤ ρ * s ^ 2 * H → r * H / 2 ≤ riskBound ρ r s H) := by
  unfold riskBound
  split_ifs with h
  · have hs : 0 < s ^ 2 := by
      by_contra hs; push Not at hs
      have : ρ * s ^ 2 * H ≤ 0 := by
        have := sq_nonneg s
        have h0 : s ^ 2 = 0 := le_antisymm hs this
        rw [h0]; simp
      linarith
    have hε : 0 ≤ r / (ρ * s ^ 2) := by positivity
    have hεH : r / (ρ * s ^ 2) ≤ H := by rw [div_le_iff₀ (by positivity)]; linarith
    have := hg _ hε hεH
    refine ⟨?_, fun hn => absurd h hn⟩
    have e : r / (ρ * s ^ 2) * r - ρ * (r / (ρ * s ^ 2)) ^ 2 * s ^ 2 / 2 = r ^ 2 / (2 * ρ * s ^ 2) := by
      field_simp; ring
    linarith
  · refine ⟨by have := hg H hH le_rfl; linarith, fun _ => ?_⟩
    push Not at h
    nlinarith

theorem decomposition : Decomposition := by
  intro n K S T _ _ P hS u₀ hu
  exact ⟨fun y hy => gain_nonneg hS hu hy, fun y _ => weight_nonneg hS hu y,
    fun y hy => weight_pos hS hu hy, weight_sum hS hu, phi_agg hS hu,
    fun ℓ ℓ' h => agg_mono hS hu h, fun ℓ ℓ' h hs => agg_strict hS hu h hs, exists_min_max hS hu⟩

/-! ### Part 2: node lower bounds -/

section Lower

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y) (j : Fin n)
include hS hu hy

lemma single_inl (v : ℝ) : (Pi.single (Sum.inr j) v : Inst 1 n → ℝ) (Sum.inl 0) = 0 := by
  simp [Pi.single_apply]

/-- Spending `c ∈ [0, h]` dollars of cash on ETF `j`. -/
lemma buy_feas {c : ℝ} (hc0 : 0 ≤ c) (hch : c ≤ h1 P u₀) :
    Feas1 P .E (x1 P y u₀) (h1 P u₀)
      (Pi.single (Sum.inr j) (c / (1 + P.D.kplus (Sum.inr j)))) := by
  obtain ⟨_, _, _, _, _, hk, _⟩ := setting_parts hS
  have hk0 := (hk (Sum.inr j)).1
  have hv : 0 ≤ c / (1 + P.D.kplus (Sum.inr j)) := div_nonneg hc0 (by linarith)
  refine ⟨fun i => ?_, ?_, single_inl hS hu hy j _⟩
  · have := (node_nn hS hu hy.1).1 i
    by_cases hi : i = Sum.inr j
    · subst hi; simp; linarith
    · simp [Pi.single_apply, hi]; exact this
  · rw [cost_single, max_eq_left hv, max_eq_right (by linarith)]
    simp only [Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte]
    have e : c / (1 + P.D.kplus (Sum.inr j)) + P.D.kplus (Sum.inr j) * (c / (1 + P.D.kplus (Sum.inr j)))
        + P.D.kminus (Sum.inr j) * 0 = c := by field_simp; ring
    linarith

lemma buy_W {c : ℝ} (hc : 0 ≤ c) (t : T) (s : S) :
    condW P (x1 P y u₀) (h1 P u₀) (Pi.single (Sum.inr j) (c / (1 + P.D.kplus (Sum.inr j)))) t s
      = condW P (x1 P y u₀) (h1 P u₀) 0 t s
        + c * ((gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))) := by
  obtain ⟨_, _, _, _, _, hk, _⟩ := setting_parts hS
  have hk0 := (hk (Sum.inr j)).1
  have hv : 0 ≤ c / (1 + P.D.kplus (Sum.inr j)) := div_nonneg hc (by linarith)
  rw [condW_single, cost_single, max_eq_left hv, max_eq_right (by linarith)]
  unfold gE; field_simp; ring

/-- Selling `c ∈ [0, m_j]` dollars of ETF `j`. -/
lemma sell_feas {c : ℝ} (hc0 : 0 ≤ c) (hcm : c ≤ x1 P y u₀ (Sum.inr j)) :
    Feas1 P .E (x1 P y u₀) (h1 P u₀) (Pi.single (Sum.inr j) (-c)) := by
  obtain ⟨_, _, _, _, _, hk, _⟩ := setting_parts hS
  have hk1 := (hk (Sum.inr j)).2.2.2
  refine ⟨fun i => ?_, ?_, single_inl hS hu hy j _⟩
  · have := (node_nn hS hu hy.1).1 i
    by_cases hi : i = Sum.inr j
    · subst hi; simp; linarith
    · simp [Pi.single_apply, hi]; exact this
  · rw [cost_single, max_eq_right (by linarith), neg_neg, max_eq_left hc0]
    simp only [Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte]
    have hh := (node_nn hS hu hy.1).2
    nlinarith [(hk (Sum.inr j)).2.2.1]

lemma sell_W {c : ℝ} (hc0 : 0 ≤ c) (t : T) (s : S) :
    condW P (x1 P y u₀) (h1 P u₀) (Pi.single (Sum.inr j) (-c)) t s
      = condW P (x1 P y u₀) (h1 P u₀) 0 t s + c * (1 - P.D.kminus (Sum.inr j) - gE P j t s) := by
  rw [condW_single, cost_single, max_eq_right (by linarith), neg_neg, max_eq_left hc0]
  unfold gE; ring

theorem nodeLower_at :
    (∀ δ, (∀ t s, NodePath P y t s → 1 + δ ≤ gE P j t s) →
      h1 P u₀ / W0 P.D * ((1 + δ) / (1 + P.D.kplus (Sum.inr j)) - 1) ≤ gain P u₀ y) ∧
    (∀ δ, (∀ t s, NodePath P y t s → gE P j t s ≤ 1 - δ) →
      x1 P y u₀ (Sum.inr j) / W0 P.D * (δ - P.D.kminus (Sum.inr j)) ≤ gain P u₀ y) ∧
    (∀ gl gu, (∀ t s, NodePath P y t s → gl ≤ gE P j t s ∧ gE P j t s ≤ gu) →
      (0 < rBuy P u₀ y j →
        riskBound P.rho (rBuy P u₀ y j) ((gu - gl) / 2) (h1 P u₀ / W0 P.D) ≤ gain P u₀ y ∧
        (¬ rBuy P u₀ y j ≤ P.rho * ((gu - gl) / 2) ^ 2 * (h1 P u₀ / W0 P.D) →
          rBuy P u₀ y j * (h1 P u₀ / W0 P.D) / 2 ≤
            riskBound P.rho (rBuy P u₀ y j) ((gu - gl) / 2) (h1 P u₀ / W0 P.D))) ∧
      (0 < rSell P u₀ y j →
        riskBound P.rho (rSell P u₀ y j) ((gu - gl) / 2) (x1 P y u₀ (Sum.inr j) / W0 P.D)
          ≤ gain P u₀ y ∧
        (¬ rSell P u₀ y j ≤ P.rho * ((gu - gl) / 2) ^ 2 * (x1 P y u₀ (Sum.inr j) / W0 P.D) →
          rSell P u₀ y j * (x1 P y u₀ (Sum.inr j) / W0 P.D) / 2 ≤
            riskBound P.rho (rSell P u₀ y j) ((gu - gl) / 2) (x1 P y u₀ (Sum.inr j) / W0 P.D)))) := by
  obtain ⟨hρ, _, _, _, _, hk, _, _, hW0, _⟩ := setting_parts hS
  have hk0 := (hk (Sum.inr j)).1
  have hk1 := (hk (Sum.inr j)).2.2.1
  have hh := (node_nn hS hu hy.1).2
  have hm := (node_nn hS hu hy.1).1 (Sum.inr j)
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_, fun gl gu hbr => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · refine gain_ge_shift hS hu hy (buy_feas hS hu hy j hh le_rfl) _ fun t s hp => ?_
    rw [buy_W hS hu hy j hh, add_div (condW P (x1 P y u₀) (h1 P u₀) 0 t s)]
    have hg1 := hδ t s hp
    have : h1 P u₀ / W0 P.D * ((1 + δ) / (1 + P.D.kplus (Sum.inr j)) - 1)
        ≤ h1 P u₀ * ((gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))) / W0 P.D := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hW0.le
      apply mul_le_mul_of_nonneg_left _ hh
      rw [div_sub_one (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  · refine gain_ge_shift hS hu hy (sell_feas hS hu hy j hm le_rfl) _ fun t s hp => ?_
    rw [sell_W hS hu hy j hm, add_div (condW P (x1 P y u₀) (h1 P u₀) 0 t s)]
    have hg1 := hδ t s hp
    have : x1 P y u₀ (Sum.inr j) / W0 P.D * (δ - P.D.kminus (Sum.inr j))
        ≤ x1 P y u₀ (Sum.inr j) * (1 - P.D.kminus (Sum.inr j) - gE P j t s) / W0 P.D := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm) hW0.le
    linarith
  · -- risk-adjusted buying
    have hZ : ∀ ε, 0 ≤ ε → ε ≤ h1 P u₀ / W0 P.D →
        ε * rBuy P u₀ y j - P.rho * ε ^ 2 * ((gu - gl) / 2) ^ 2 / 2 ≤ gain P u₀ y := by
      intro ε hε0 hεH
      have hc0 : 0 ≤ ε * W0 P.D := mul_nonneg hε0 hW0.le
      have hcH : ε * W0 P.D ≤ h1 P u₀ := by rwa [le_div_iff₀ hW0] at hεH
      have hg := gain_ge_tilt hS hu hy (buy_feas hS hu hy j hc0 hcH) ε
        (fun t s => (gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j)))
        (fun t s => by rw [buy_W hS hu hy j hc0, add_div]; field_simp)
        (zl := (gl - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j)))
        (zu := (gu - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j)))
        (fun t s hp => ⟨div_le_div_of_nonneg_right (by linarith [(hbr t s hp).1]) (by linarith),
          div_le_div_of_nonneg_right (by linarith [(hbr t s hp).2]) (by linarith)⟩)
      have hsq : (((gu - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))
          - (gl - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))) / 2) ^ 2
          ≤ ((gu - gl) / 2) ^ 2 := by
        rw [← sub_div, div_div, div_pow, div_pow]
        have h1k : (1 : ℝ) ≤ (1 + P.D.kplus (Sum.inr j)) ^ 2 := by nlinarith
        rw [show (gu - 1 - P.D.kplus (Sum.inr j) - (gl - 1 - P.D.kplus (Sum.inr j))) = gu - gl by ring,
          show ((1 + P.D.kplus (Sum.inr j)) * 2) ^ 2 = (1 + P.D.kplus (Sum.inr j)) ^ 2 * 2 ^ 2 by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (gu - gl)]
      have : P.rho * ε ^ 2 * (((gu - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))
          - (gl - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))) / 2) ^ 2 / 2
          ≤ P.rho * ε ^ 2 * ((gu - gl) / 2) ^ 2 / 2 := by
        have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ P.rho * ε ^ 2)
        linarith
      unfold rBuy; linarith
    exact riskBound_opt hρ hr (div_nonneg hh hW0.le) hZ
  · -- risk-adjusted selling
    have hZ : ∀ ε, 0 ≤ ε → ε ≤ x1 P y u₀ (Sum.inr j) / W0 P.D →
        ε * rSell P u₀ y j - P.rho * ε ^ 2 * ((gu - gl) / 2) ^ 2 / 2 ≤ gain P u₀ y := by
      intro ε hε0 hεH
      have hc0 : 0 ≤ ε * W0 P.D := mul_nonneg hε0 hW0.le
      have hcm : ε * W0 P.D ≤ x1 P y u₀ (Sum.inr j) := by rwa [le_div_iff₀ hW0] at hεH
      have hg := gain_ge_tilt hS hu hy (sell_feas hS hu hy j hc0 hcm) ε
        (fun t s => 1 - P.D.kminus (Sum.inr j) - gE P j t s)
        (fun t s => by rw [sell_W hS hu hy j hc0, add_div]; field_simp)
        (zl := 1 - P.D.kminus (Sum.inr j) - gu) (zu := 1 - P.D.kminus (Sum.inr j) - gl)
        (fun t s hp => ⟨by linarith [(hbr t s hp).2], by linarith [(hbr t s hp).1]⟩)
      have e : (1 - P.D.kminus (Sum.inr j) - gl - (1 - P.D.kminus (Sum.inr j) - gu)) / 2
          = (gu - gl) / 2 := by ring
      rw [e] at hg
      unfold rSell; linarith
    exact riskBound_opt hρ hr (div_nonneg hm hW0.le) hZ

end Lower

theorem nodeLower : NodeLower := by
  intro n K S T _ _ P hS u₀ hu
  refine ⟨fun y hy j => nodeLower_at hS hu hy j, fun ℓ hℓ => ?_⟩
  rw [phi_agg hS hu]
  exact agg_mono hS hu hℓ

/-! ### Part 3: node caps -/

section Cap

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
include hS hu

/-- The pathwise cap at one path, with brackets on that path's ETF returns. -/
lemma path_cap {y : Obs n K} (hy : y ∈ Yset P) {u : Inst 1 n → ℝ}
    (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) {U D : ℝ} (hU : 0 ≤ U) (hD : 0 ≤ D) (t : T) (s : S)
    (hb : ∀ j, gE P j t s - 1 ≤ U ∧ 1 - gE P j t s ≤ D) :
    condW P (x1 P y u₀) (h1 P u₀) u t s
      ≤ condW P (x1 P y u₀) (h1 P u₀) 0 t s + (h1 P u₀ * U + (∑ j, x1 P y u₀ (Sum.inr j)) * (U + D)) := by
  set x := x1 P y u₀
  set h := h1 P u₀
  have huA : u (Sum.inl 0) = 0 := hfe.2.2
  have hC := cost_nonneg P (rates_nonneg hS) u
  have hcash := hfe.2.1
  have hx0 : ∀ j, 0 ≤ x (Sum.inr j) := fun j => (node_nn hS hu hy).1 _
  have hper : ∀ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1)
      ≤ U * max (u (Sum.inr j)) 0 + D * max (-u (Sum.inr j)) 0 := fun j => by
    have g1 := (hb j).1
    have g2 := (hb j).2
    unfold gE at g1 g2
    rcases le_total 0 (u (Sum.inr j)) with hj | hj
    · rw [max_eq_left hj, max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_right hj, max_eq_left (by linarith)]; nlinarith
  have hneg : ∀ j, max (-u (Sum.inr j)) 0 ≤ x (Sum.inr j) := fun j => by
    have := hfe.1 (Sum.inr j); exact max_le (by linarith) (hx0 j)
  have hsplit : ∑ j, u (Sum.inr j) = ∑ j, max (u (Sum.inr j)) 0 - ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rcases le_total 0 (u (Sum.inr j)) with hj | hj
      · rw [max_eq_left hj, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hj, max_eq_left (by linarith)]; ring
  have hsumU : ∑ i, u i = ∑ j, u (Sum.inr j) := by rw [sum_inst, huA, zero_add]
  have hpos : ∑ j, max (u (Sum.inr j)) 0 ≤ h + ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [hsumU, hsplit] at hcash; linarith
  have hnegx : ∑ j, max (-u (Sum.inr j)) 0 ≤ ∑ j, x (Sum.inr j) :=
    Finset.sum_le_sum fun j _ => hneg j
  have hdiff : condW P x h u t s - condW P x h 0 t s
      = ∑ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1) - cost P.D u := by
    simp only [condW, cost_zero, Pi.zero_apply, sum_const_zero, sub_zero, add_zero]
    rw [sum_inst (fun i => (x i + u i) * (1 + ret P.D (P.par t) s i)),
      sum_inst (fun i => x i * (1 + ret P.D (P.par t) s i)), hsumU, huA, add_zero]
    have e1 : ∑ j, (x (Sum.inr j) + u (Sum.inr j)) * (1 + ret P.D (P.par t) s (Sum.inr j))
        = ∑ j, x (Sum.inr j) * (1 + ret P.D (P.par t) s (Sum.inr j))
          + ∑ j, u (Sum.inr j) * (1 + ret P.D (P.par t) s (Sum.inr j)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1)
        = ∑ j, u (Sum.inr j) * (1 + ret P.D (P.par t) s (Sum.inr j)) - ∑ j, u (Sum.inr j) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]; ring
  have hstep : ∑ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1)
      ≤ U * ∑ j, max (u (Sum.inr j)) 0 + D * ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hper j
  have hA := mul_le_mul_of_nonneg_left hpos hU
  have hB := mul_le_mul_of_nonneg_left hnegx (add_nonneg hU hD)
  nlinarith

theorem nodeCap_at {y : Obs n K} (hy : IsNode P y) {U D : ℝ} (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hb : ∀ j t s, NodePath P y t s → gE P j t s - 1 ≤ U ∧ 1 - gE P j t s ≤ D) :
    gain P u₀ y ≤ (h1 P u₀ * U + (∑ j, x1 P y u₀ (Sum.inr j)) * (U + D)) / W0 P.D := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  refine gain_le_shift hS hu hy _ fun u hfe t s hp => ?_
  have := path_cap hS hu hy.1 hfe hU hD t s fun j => hb j t s hp
  rw [← add_div]
  exact div_le_div_of_nonneg_right this hW0.le

lemma cap_le_beta {G L : ℝ} (hG : ∀ j t s, gE P j t s ≤ G) {y : Obs n K} (hy : y ∈ Yset P) :
    (h1 P u₀ * max (G - 1) 0 + (∑ j, x1 P y u₀ (Sum.inr j)) * (max (G - 1) 0 + max (1 - L) 0))
      / W0 P.D ≤ beta P G L u₀ := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  unfold beta
  apply div_le_div_of_nonneg_right _ hW0.le
  have hxj : ∀ j, x1 P y u₀ (Sum.inr j) ≤ G * (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j)) := fun j => by
    obtain ⟨t', s', hyo⟩ := obs_mem (⟨y, hy⟩ : Yset P)
    have hyo' : obs P t' s' = y := hyo
    simp only [x1]
    rw [← hyo']
    exact mul_le_mul_of_nonneg_right (hG j t' s') (hu.1 _)
  have hsum : ∑ j, x1 P y u₀ (Sum.inr j) ≤ (∑ j, (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j))) * G := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => by linarith [hxj j]
  have := mul_le_mul_of_nonneg_right hsum (add_nonneg (le_max_right (G - 1) 0) (le_max_right (1 - L) 0))
  linarith

end Cap

theorem nodeCap : NodeCap := by
  intro n K S T _ _ P hS u₀ hu
  refine ⟨fun y hy U D hU hD hb => nodeCap_at hS hu hy hU hD hb, fun ℓ' hℓ => ?_,
    fun G L hG hL => ⟨fun y hy => cap_le_beta hS hu hG hy, fun ℓ' hℓ => ?_⟩⟩
  · rw [phi_agg hS hu]; exact agg_mono hS hu hℓ
  · rw [← agg_const hS hu (beta P G L u₀)]; exact agg_mono hS hu hℓ

/-! ### Part 4: sign conditions -/

section Signs

variable (hS : M3Setting P)
include hS

lemma phi_ge {u : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u) {ℓ : Obs n K → ℝ}
    (h : ∀ y, IsNode P y → ℓ y ≤ gain P u y) : agg P u ℓ ≤ phi P u := by
  rw [phi_agg hS hu]; exact agg_mono hS hu h

lemma phi_le {u : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u) {ℓ' : Obs n K → ℝ}
    (h : ∀ y, IsNode P y → gain P u y ≤ ℓ' y) : phi P u ≤ agg P u ℓ' := by
  rw [phi_agg hS hu]; exact agg_mono hS hu h

end Signs

theorem signConditions : SignConditions := by
  intro n K S T _ _ P hS
  have fE : ∀ {v : Inst 1 n → ℝ}, Feas1 P .E P.D.x0 P.D.h0 v → Feas1 P .F P.D.x0 P.D.h0 v :=
    fun h => Novel.M3EtfChannelSandwichProof.feas_EF h
  refine ⟨fun AE BN hAE hBN ℓ' ℓ h' h hlt => ?_, fun AN BE hAN hBE ℓ ℓ' h h' hlt => ?_,
    fun u BE hu hBE ℓ ℓ' h h' => ?_, fun AE v hAE hv ℓ' ℓ h' h => ?_⟩
  · have := Novel.M3EtfChannelSandwichProof.etf_upper hS hAE hBN
    have a := phi_le hS hAE.1 h'
    have b := phi_ge hS (fE hBN.1) h
    exact ⟨by linarith, by linarith⟩
  · have := Novel.M3EtfChannelSandwichProof.etf_lower hS hAN hBE
    have a := phi_ge hS hAN.1 h
    have b := phi_le hS (fE hBE.1) h'
    exact ⟨by linarith, by linarith⟩
  · -- CE_{F,E} ≥ c_E(u) = c_N(u) + φ(u), CE_{E,E} = c_E(B_E) ≤ CE_{E,N} + φ(B_E)
    have h1 := Novel.M3EtfChannelSandwichProof.cR_le_CE hS (r := .E) hu
    have h2 := Novel.M3EtfChannelSandwichProof.rootOpt_CE hS hBE
    have h3 := Novel.M3EtfChannelSandwichProof.cR_le_CE hS (r := .N) hBE.1
    have a := phi_ge hS hu h
    have b := phi_le hS (fE hBE.1) h'
    simp only [phi] at a b
    unfold Delta; linarith
  · have h1 := Novel.M3EtfChannelSandwichProof.rootOpt_CE hS hAE
    have h2 := Novel.M3EtfChannelSandwichProof.cR_le_CE hS (r := .N) hAE.1
    have h3 := Novel.M3EtfChannelSandwichProof.cR_le_CE hS (r := .E) hv
    have a := phi_le hS hAE.1 h'
    have b := phi_ge hS (fE hv) h
    simp only [phi] at a b
    unfold Delta; linarith

/-! ### Two-state families whose observation reveals `θ` -/

section Reveal

variable {Q : M3 1 2 (Fin 1) Bool} (hq : ∀ s, Q.D.q s = 1)
  (hne : obs Q true (0 : Fin 1) ≠ obs Q false 0)
include hq hne

omit hq in
lemma obs_eq_iff (t t' : Bool) : obs Q t (0 : Fin 1) = obs Q t' 0 ↔ t = t' := by
  cases t <;> cases t' <;> simp [hne, Ne.symm hne]

lemma lik_obs (t t' : Bool) : lik Q t (obs Q t' 0) = if t = t' then 1 else 0 := by
  simp only [lik, Fin.sum_univ_one, hq]
  have : ∀ s : Fin 1, s = 0 := fun s => Subsingleton.elim _ _
  rw [this 0]
  by_cases h : t = t'
  · simp [h]
  · simp [h, (obs_eq_iff hne t t').not.mpr h]

lemma P0_obs (t' : Bool) : P0 Q (obs Q t' 0) = Q.pi0 t' := by
  simp only [P0, lik_obs hq hne, Fintype.sum_bool]
  cases t' <;> simp

lemma post_obs (hpi : ∀ t, 0 < Q.pi0 t) (t' t : Bool) :
    post Q (obs Q t' 0) t = if t = t' then 1 else 0 := by
  simp only [post, P0_obs hq hne, hpi t', ↓reduceIte, lik_obs hq hne]
  by_cases h : t = t'
  · subst h; simp [(hpi t).ne']
  · simp [h]

omit hq in
lemma sum_Yset (f : Obs 1 2 → ℝ) : ∑ y ∈ Yset Q, f y = f (obs Q true 0) + f (obs Q false 0) := by
  unfold Yset
  rw [Finset.sum_image]
  · simp [Fintype.sum_prod_type, Fintype.sum_bool]
  · rintro ⟨t, s⟩ - ⟨t', s'⟩ - h
    have hs : s = 0 := Subsingleton.elim _ _
    have hs' : s' = 0 := Subsingleton.elim _ _
    subst hs hs'
    simp only at h
    rw [(obs_eq_iff hne t t').mp h]

lemma node_obs (hpi : ∀ t, 0 < Q.pi0 t) (t : Bool) : IsNode Q (obs Q t 0) :=
  ⟨Finset.mem_image.mpr ⟨(t, 0), Finset.mem_univ _, rfl⟩, by rw [P0_obs hq hne]; exact hpi t⟩

omit hne in
lemma node_cases {y : Obs 1 2} (hy : IsNode Q y) : y = obs Q true 0 ∨ y = obs Q false 0 := by
  obtain ⟨⟨t, s⟩, -, h⟩ := Finset.mem_image.mp hy.1
  have hs : s = 0 := Subsingleton.elim _ _
  subst hs
  cases t
  · exact Or.inr h.symm
  · exact Or.inl h.symm

lemma nodePath_obs (hpi : ∀ t, 0 < Q.pi0 t) {t' t : Bool} {s : Fin 1}
    (h : NodePath Q (obs Q t' 0) t s) : t = t' := by
  have := h.1
  rw [post_obs hq hne hpi] at this
  by_contra hne'
  simp [hne'] at this

lemma condObj_obs (hpi : ∀ t, 0 < Q.pi0 t) (t' : Bool) (x : Inst 1 1 → ℝ) (h : ℝ)
    (u : Inst 1 1 → ℝ) :
    condObj Q (post Q (obs Q t' 0)) x h u = U Q (condW Q x h u t' 0 / W0 Q.D) := by
  simp only [condObj, post_obs hq hne hpi, Fintype.sum_bool, Fin.sum_univ_one, hq]
  cases t' <;> simp

lemma nodeCEN_obs (hS : M3Setting Q) (hpi : ∀ t, 0 < Q.pi0 t) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 Q .F Q.D.x0 Q.D.h0 u₀) (t : Bool) :
    nodeCE Q .N u₀ (obs Q t 0) = condW Q (x1 Q (obs Q t 0) u₀) (h1 Q u₀) 0 t 0 / W0 Q.D := by
  have hρ := hS.1
  unfold nodeCE
  rw [V1N_eq hS hu (node_obs hq hne hpi t), condObj_obs hq hne hpi]
  unfold U
  rw [neg_neg, Real.log_exp]
  field_simp

lemma agg_obs (hS : M3Setting Q) (hpi : ∀ t, 0 < Q.pi0 t) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 Q .F Q.D.x0 Q.D.h0 u₀) (ℓ : Obs 1 2 → ℝ) :
    agg Q u₀ ℓ = -(1 / Q.rho) * Real.log
      ((Q.pi0 true * Real.exp (-Q.rho * nodeCE Q .N u₀ (obs Q true 0)) * Real.exp (-Q.rho * ℓ (obs Q true 0))
        + Q.pi0 false * Real.exp (-Q.rho * nodeCE Q .N u₀ (obs Q false 0))
          * Real.exp (-Q.rho * ℓ (obs Q false 0))) /
       (Q.pi0 true * Real.exp (-Q.rho * nodeCE Q .N u₀ (obs Q true 0))
        + Q.pi0 false * Real.exp (-Q.rho * nodeCE Q .N u₀ (obs Q false 0)))) := by
  unfold agg weight nodeMass
  rw [sum_Yset hne, sum_Yset hne]
  simp only [P0_obs hq hne, hpi, ↓reduceIte]
  congr 2
  field_simp

end Reveal

/-! ### Part 5 (i): the sure-active family -/

section SureActive

open Standalone.M3EtfChannelSandwich (saData)
open Novel.M3EtfChannelSandwichProof (setting_sa obs_ne_sa Phi_sa W2_sa root_budget W0_sa x0_sa
  actPol actPol_mem actPol_W2 allActive_feas h1_allActive cashPol cashPol_mem cashPol_W2 exp_w
  log32 exp9 gr h1_zero x1_zero)

local notation "PS" => saInst 0 0 0 0

lemma box0 : Standalone.M3EtfChannelSandwich.InBox 0 0 0 0 := by
  norm_num [Standalone.M3EtfChannelSandwich.InBox]

lemma hS_sa : M3Setting PS := setting_sa box0

lemma hq_sa : ∀ s, (PS).D.q s = 1 := fun _ => rfl

lemma hpi_sa : ∀ t, 0 < (PS).pi0 t := fun t => by
  cases t <;> norm_num [saInst]

lemma hfe0_sa : Feas1 PS .F (PS).D.x0 (PS).D.h0 0 :=
  feas_zero .F (fun i => le_rfl) (by norm_num [saInst, saData])

lemma pol_mem_H0 {d r : Cls} {π : Policy PS} (hπ : π ∈ Pol PS d r) : Phi PS π ≤ H0 PS r π.1 :=
  Phi_le_H0 hS_sa hπ

lemma cR_sa (r : Cls) (u : Inst 1 1 → ℝ) : cR PS r u = -(1 / 20) * Real.log (-H0 PS r u) := rfl

/-- `c_E(all-active) ≥ 9/4`. -/
lemma cE_allActive : 9 / 4 ≤ cR PS .E (allActive 0) := by
  have hmem : (actPol : Policy PS) ∈ Pol PS .F .E := by
    obtain ⟨h1, h2⟩ := actPol_mem (kA := 0) (kE := 0) (sA := 0) (sE := 0) box0
    exact ⟨h1, fun y => Novel.M3EtfChannelSandwichProof.feas_NE (h2 y)⟩
  have hΦ := pol_mem_H0 hmem
  rw [Phi_sa, actPol_W2 box0, actPol_W2 box0] at hΦ
  have hH := (Novel.M3EtfChannelSandwichProof.H0_range hS_sa .E (allActive_feas box0)).2
  have e : Real.exp (-20 * (9 / 4 * (1 / (1 + 0)))) = Real.exp (-45) := by norm_num
  rw [e] at hΦ
  have hact : (actPol : Policy PS).1 = allActive 0 := rfl
  rw [hact] at hΦ
  have hlog := Real.log_le_log (by linarith) (by linarith : -H0 PS .E (allActive 0) ≤ Real.exp (-45))
  rw [Real.log_exp] at hlog
  show 9 / 4 ≤ -(1 / 20) * Real.log (-H0 PS .E (allActive 0))
  linarith

lemma AE_unique {AE : Inst 1 1 → ℝ} (hAE : RootOpt PS .F .E AE) : AE = allActive 0 := by
  have hS := hS_sa
  have hc := (hAE.2 _ (allActive_feas box0)).trans' cE_allActive
  obtain ⟨u₁, hπ, hΦ⟩ := H0_attain hS (r := .E) hAE.1
  have hle : 9 / 4 ≤ -(1 / 20) * Real.log (-Phi PS (AE, u₁)) := by rw [hΦ]; exact hc
  obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget box0 hπ
  set a := AE (Sum.inl 0)
  set p := AE (Sum.inr 0)
  set h := h1 PS AE
  -- W₂ ≤ 9/4 on both paths
  have hM : ∀ t s i, 1 + ret (PS).D ((PS).par t) s i ≤ 3 / 2 := fun t s i => by
    rw [Novel.M3EtfChannelSandwichProof.gross_sa]; rcases i with k | k <;> cases t <;> norm_num [gr]
  have hWt := (wealth_le hS hπ (by norm_num : (1 : ℝ) ≤ 3 / 2) hM true 0 0).2
  rw [W0_sa] at hWt
  -- under θ₋ the active holding is locked: W₂ ≤ 9a/4 + h + p/2
  have hnode : Feas1 PS .E (x1 PS (obsY PS false 0 : Obs 1 2) AE) h (u₁ (obsY PS false 0)) := hπ.2 _
  have huA : u₁ (obsY PS false 0) (Sum.inl 0) = 0 := hnode.2.2
  have huE := hnode.1 (Sum.inr 0)
  simp only [x1, x0_sa, Pi.zero_apply, zero_add] at huE
  rw [Novel.M3EtfChannelSandwichProof.obs_gross] at huE
  simp only [gr, Sum.elim_inr] at huE
  have hc1 := cost_nonneg PS (rates_nonneg hS) (u₁ (obsY PS false 0))
  have hWf : W2 PS (AE, u₁) false 0 0 ≤ 9 * a / 4 + h + p / 2 := by
    rw [W2_sa, Novel.M3EtfChannelSandwichProof.sum_inst1]
    dsimp only
    rw [huA]
    simp only [gr, Sum.elim_inl, Sum.elim_inr]
    nlinarith
  -- both paths must reach 9/4
  have hΦeq := Phi_sa (kA := 0) (kE := 0) (sA := 0) (sE := 0) (AE, u₁)
  have hWf' : 9 / 4 ≤ W2 PS (AE, u₁) false 0 0 := by
    by_contra hlt
    push Not at hlt
    have e1 : Real.exp (-20 * (9 / 4)) ≤ Real.exp (-20 * W2 PS (AE, u₁) true 0 0) :=
      Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp (-20 * (9 / 4)) < Real.exp (-20 * W2 PS (AE, u₁) false 0 0) :=
      Real.exp_lt_exp.mpr (by linarith)
    have hlt' : Real.exp (-20 * (9 / 4)) < -Phi PS (AE, u₁) := by rw [hΦeq]; linarith
    have hlog := Real.log_lt_log (Real.exp_pos _) hlt'
    rw [Real.log_exp] at hlog
    linarith
  have hp : p = 0 := by nlinarith
  have hh : h = 0 := by nlinarith
  have ha : a = 1 := by nlinarith
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
  · show a = _; rw [ha]; simp [allActive]
  · show p = _; rw [hp]; simp [allActive]

lemma BN_unique {BN : Inst 1 1 → ℝ} (hBN : RootOpt PS .E .N BN) : BN = 0 := by
  have hS := hS_sa
  -- c_N(0) ≥ 1
  have hc0 : 1 ≤ cR PS .N 0 := by
    have hΦ := pol_mem_H0 (cashPol_mem (kA := 0) (kE := 0) (sA := 0) (sE := 0) .E .N)
    rw [Phi_sa, cashPol_W2, cashPol_W2] at hΦ
    have hcash : (cashPol : Policy PS).1 = 0 := rfl
    rw [hcash] at hΦ
    have hH := (Novel.M3EtfChannelSandwichProof.H0_range hS .N hfe0_sa).2
    have hΦ' : -H0 PS .N 0 ≤ Real.exp (-20) := by norm_num at hΦ; linarith
    have hlog := Real.log_le_log (by linarith) hΦ'
    rw [Real.log_exp] at hlog
    show 1 ≤ -(1 / 20) * Real.log (-H0 PS .N 0)
    linarith
  have hc := hc0.trans (hBN.2 0 (feas_zero .E (fun i => le_rfl) (by norm_num [saInst, saData])))
  obtain ⟨u₁, hπ, hΦ⟩ := H0_attain hS (r := .N) hBN.1
  obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget box0 hπ
  have hA : BN (Sum.inl 0) = 0 := hBN.1.2.2
  have z1 : u₁ (obsY PS true 0) = 0 := (hπ.2 _).2.2
  have z2 : u₁ (obsY PS false 0) = 0 := (hπ.2 _).2.2
  have hcost : cost (PS).D BN = 0 := by simp [cost, saInst, saData]
  have hh : h1 PS BN = 1 - BN (Sum.inr 0) := by
    simp only [h1, hcost, Novel.M3EtfChannelSandwichProof.sum_inst1, hA]; simp [saInst, saData]
  have hWt : W2 PS (BN, u₁) true 0 0 = h1 PS BN + 9 / 4 * BN (Sum.inr 0) := by
    rw [W2_sa]; dsimp only; rw [z1, cost_zero]; simp [gr, hA]; ring
  have hWf : W2 PS (BN, u₁) false 0 0 = h1 PS BN + 1 / 4 * BN (Sum.inr 0) := by
    rw [W2_sa]; dsimp only; rw [z2, cost_zero]; simp [gr, hA]; ring
  have hmean := exp_w (-20 * W2 PS (BN, u₁) true 0 0) (-20 * W2 PS (BN, u₁) false 0 0)
  have hΦeq := Phi_sa (kA := 0) (kE := 0) (sA := 0) (sE := 0) (BN, u₁)
  have hle : Real.exp (-20 * (1 - BN (Sum.inr 0) / 12)) ≤ -H0 PS .N BN := by
    rw [← hΦ, hΦeq]
    have : 1 / 3 * (-20 * W2 PS (BN, u₁) true 0 0) + 2 / 3 * (-20 * W2 PS (BN, u₁) false 0 0)
        = -20 * (1 - BN (Sum.inr 0) / 12) := by rw [hWt, hWf, hh]; ring
    rw [this] at hmean; linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp] at hlog
  have hcN : cR PS .N BN ≤ 1 - BN (Sum.inr 0) / 12 := by rw [cR_sa]; linarith
  have hp : BN (Sum.inr 0) = 0 := by linarith
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
  · exact hA
  · exact hp

lemma exp10 : Real.exp (-10) ≤ 1 / 8000 := by
  have h1 : Real.exp (-10) ≤ Real.exp (-9) := Real.exp_le_exp.mpr (by norm_num)
  have h2 : Real.exp (-9) = (Real.exp 9)⁻¹ := Real.exp_neg 9
  have h3 := exp9
  have : (Real.exp 9)⁻¹ ≤ 1 / 8000 := by
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; linarith
  linarith

lemma log32_strong : 201 / 500 ≤ Real.log (3 / 2) := by
  have he := Real.exp_one_lt_d9
  have e1 : Real.exp (201 / 500) ^ 5 = Real.exp 2 * Real.exp (1 / 100) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq := pow_lt_pow_left₀ he (Real.exp_pos 1).le (two_ne_zero)
  have hsmall := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 100) (by norm_num) (by norm_num)
  have hprod := mul_lt_mul'' hsq hsmall (by positivity) (Real.exp_pos _).le
  have h5 : Real.exp (201 / 500) ^ 5 < (3 / 2) ^ 5 := by
    rw [e1, e2]
    norm_num at hprod ⊢
    linarith
  have h3 : Real.exp (201 / 500) < 3 / 2 := lt_of_pow_lt_pow_left₀ 5 (by norm_num) h5
  rw [Real.le_log_iff_exp_le (by norm_num)]; exact h3.le

theorem sureActiveCert : SureActiveCert := by
  unfold SureActiveCert
  intro P a
  have hS : M3Setting P := hS_sa
  have hq : ∀ s, P.D.q s = 1 := hq_sa
  have hne : obs P true (0 : Fin 1) ≠ obs P false 0 := obs_ne_sa
  have hpi : ∀ t, 0 < P.pi0 t := hpi_sa
  have hfeA := allActive_feas (kA := 0) (kE := 0) (sA := 0) (sE := 0) box0
  have hfe0 : Feas1 P .F P.D.x0 P.D.h0 0 := hfe0_sa
  -- node gains at the all-active root are zero
  have hgA : ∀ y, IsNode P y → gain P (allActive 0) y ≤ 0 := fun y hy => by
    have := nodeCap_at hS hfeA hy (U := 1 / 2) (D := 1 / 2) (by norm_num) (by norm_num)
      fun j t s _ => by
        obtain rfl : j = 0 := Subsingleton.elim _ _
        unfold gE; rw [Novel.M3EtfChannelSandwichProof.gross_sa]; cases t <;> norm_num [gr]
    rw [h1_allActive box0] at this
    have hx : x1 P y (allActive 0) (Sum.inr 0) = 0 := by
      simp only [x1, allActive, Sum.elim_inr]
      rw [show P.D.x0 (Sum.inr 0) = 0 from rfl]; ring
    simpa [hx] using this
  -- node bounds at the cash root
  have hlb : ∀ y, IsNode P y → (if y = obs P true 0 then (1 / 2 : ℝ) else 0) ≤ gain P 0 y := by
    intro y hy
    split_ifs with hyt
    · subst hyt
      have := (nodeLower_at hS hfe0 hy 0).1 (1 / 2) fun t s hp => by
        rw [nodePath_obs hq hne hpi hp]; unfold gE
        rw [Novel.M3EtfChannelSandwichProof.gross_sa]; norm_num [gr]
      rw [h1_zero, W0_sa, show P.D.kplus (Sum.inr 0) = 0 from rfl] at this
      norm_num at this ⊢
      linarith
    · exact gain_nonneg hS hfe0 hy
  -- the aggregate at the cash root
  have hagg : agg P 0 (fun y => if y = obs P true 0 then 1 / 2 else 0) = a := by
    have hW : ∀ t, nodeCE P .N 0 (obs P t 0) = 1 := fun t => by
      rw [nodeCEN_obs hq hne hS hpi hfe0, x1_zero, h1_zero, W0_sa]
      simp [condW, cost_zero]
    rw [agg_obs hq hne hS hpi hfe0, hW, hW, ite_eq_left rfl, ite_eq_right (Ne.symm hne)]
    rw [show P.rho = 20 from rfl, show P.pi0 true = 1 / 3 from rfl, show P.pi0 false = 2 / 3 from rfl]
    have hp := Real.exp_pos (-20 * (1 : ℝ))
    have hX : (1 / 3 * Real.exp (-20 * 1) * Real.exp (-20 * (1 / 2)) + 2 / 3 * Real.exp (-20 * 1)
        * Real.exp (-20 * 0)) / (1 / 3 * Real.exp (-20 * 1) + 2 / 3 * Real.exp (-20 * 1))
        = (2 / 3) * (1 + Real.exp (-10) / 2) := by
      rw [show (-20 * (1 / 2) : ℝ) = -10 by norm_num, show (-20 * 0 : ℝ) = 0 by norm_num,
        Real.exp_zero]
      field_simp; ring
    rw [hX, Real.log_mul (by norm_num) (by positivity),
      show Real.log (2 / 3) = -Real.log (3 / 2) by rw [← Real.log_inv]; norm_num]
    simp only [a]; ring
  have ha : 1 / 50 < a := by
    have h1 := log32_strong
    have h2 := exp10
    have h3 : Real.log (1 + Real.exp (-10) / 2) ≤ Real.exp (-10) / 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + Real.exp (-10) / 2)
      linarith
    simp only [a]; linarith
  -- the channel
  obtain ⟨AE, hAE⟩ := Novel.M3EtfChannelSandwichProof.rootOpt_exists hS .F .E
  obtain ⟨BN, hBN⟩ := Novel.M3EtfChannelSandwichProof.rootOpt_exists hS .E .N
  have hAE' := AE_unique hAE
  have hBN' := BN_unique hBN
  have hup := Novel.M3EtfChannelSandwichProof.etf_upper hS hAE hBN
  have hphiA : phi P AE ≤ 0 := by
    rw [hAE']
    have := phi_le hS hfeA hgA
    rwa [agg_const hS hfeA] at this
  have hphiB : a ≤ phi P BN := by
    rw [hBN', ← hagg]; exact phi_ge hS hfe0 hlb
  refine ⟨fun _ h => AE_unique h, fun _ h => BN_unique h, hgA, agg_const hS hfeA 0, hlb, hagg, ha,
    by linarith⟩

end SureActive

/-! ### Part 5 (ii): claim 012's family -/

section Complement

open Standalone.OppositeContinuationEffects (ocInst ocData InBox)
open Novel.OppositeContinuationEffectsProof (setting obs_ne Phi_oc CE_le CE_ge W2_oc root_budget
  W2_le_W1m W1m_oc W0_oc x0_oc x1_obs obsA gr gr_tA gr_tE gr_fA gr_fE gross_eq sum_inst1
  cashPol cashPol_mem cashPol_W2 h1_zero x1_zero exp_facts)

local notation "PO" => ocInst 0 0 0 0

lemma boxO : InBox 0 0 0 0 := by norm_num [InBox]

lemma hS_oc : M3Setting PO := setting boxO

lemma hq_oc : ∀ s, (PO).D.q s = 1 := fun _ => rfl

lemma hpi_oc : ∀ t, 0 < (PO).pi0 t := fun t => by norm_num [ocInst]

lemma hfe0_oc (c : Cls) : Feas1 PO c (PO).D.x0 (PO).D.h0 0 :=
  feas_zero c (fun i => le_rfl) (by norm_num [ocInst, ocData])

/-- A fully invested root `(a, p)` with `a + p = 1`. -/
noncomputable def inv (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

lemma inv_feas {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (h : a + p = 1) :
    Feas1 PO .F (PO).D.x0 (PO).D.h0 (inv a p) := by
  refine ⟨fun i => ?_, ?_, trivial⟩
  · rcases i with k | k <;> simp [inv, x0_oc, ha, hp]
  · simp only [sum_inst1, inv, Sum.elim_inl, Sum.elim_inr]
    simp [cost, ocInst, ocData]
    linarith

lemma h1_inv {a p : ℝ} (h : a + p = 1) : h1 PO (inv a p) = 0 := by
  simp only [h1, sum_inst1, inv, Sum.elim_inl, Sum.elim_inr]
  simp [cost, ocInst, ocData]
  linarith

lemma x1_oc (t : Bool) (u : Inst 1 1 → ℝ) (i : Inst 1 1) :
    x1 PO (obs PO t 0) u i = gr t i * u i := x1_obs t u i

/-- Never trade at review 1. -/
lemma noTrade_mem {u : Inst 1 1 → ℝ} (hu : Feas1 PO .F (PO).D.x0 (PO).D.h0 u) :
    ((u, fun _ => 0) : Policy PO) ∈ Pol PO .F .N :=
  ⟨hu, fun y => feas_zero .N (node_nn hS_oc hu y.2).1 (node_nn hS_oc hu y.2).2⟩

lemma W2_inv (a p : ℝ) (h : a + p = 1) (t : Bool) :
    W2 PO ((inv a p, fun _ => 0) : Policy PO) t 0 0
      = gr t (Sum.inl 0) ^ 2 * a + gr t (Sum.inr 0) ^ 2 * p := by
  rw [W2_oc]
  dsimp only
  rw [h1_inv h, cost_zero]
  simp [inv]
  ring

/-- `CE_{F,N} = 5/4`. -/
lemma CE_FN : CE PO .F .N = 5 / 4 := by
  refine le_antisymm (CE_le boxO fun π hπ => ?_) ?_
  · obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget boxO hπ
    have z1 : π.2 (obsY PO true 0) = 0 := (hπ.2 _).2.2
    have z2 : π.2 (obsY PO false 0) = 0 := (hπ.2 _).2.2
    rw [W2_oc, W2_oc, z1, z2, cost_zero]
    simp only [Pi.zero_apply, Finset.sum_const_zero, gr_tA, gr_tE, gr_fA, gr_fE]
    nlinarith
  · have hm := noTrade_mem (inv_feas (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num))
    refine CE_ge boxO hm ?_ ?_
    · rw [W2_inv _ _ (by norm_num)]; norm_num [gr]
    · rw [W2_inv _ _ (by norm_num)]; norm_num [gr]

/-- The cash root with ETF-only trading at review 1: hold cash under `θ₊`, buy the ETF under
`θ₋`. -/
noncomputable def cashE : Policy PO :=
  (0, fun y => if (y : Obs 1 2).2 (Sum.inl 0) = 1 / 2 then 0 else inv 0 1)

lemma cashE_true : cashE.2 (obsY PO true 0) = 0 := by simp [cashE, obsA]

lemma cashE_false : cashE.2 (obsY PO false 0) = inv 0 1 := by
  simp only [cashE, obsA]; norm_num

lemma cashE_mem : cashE ∈ Pol PO .E .E := by
  refine ⟨hfe0_oc .E, fun y => ?_⟩
  obtain ⟨t, rfl⟩ := Novel.OppositeContinuationEffectsProof.yset_eq y
  show Feas1 PO .E (x1 PO (obs PO t 0) 0) (h1 PO 0) (cashE.2 (obsY PO t 0))
  rw [x1_zero, h1_zero]
  cases t
  · rw [cashE_false]
    refine ⟨fun i => ?_, ?_, rfl⟩
    · rcases i with k | k <;> simp [inv]
    · simp only [sum_inst1, inv, Sum.elim_inl, Sum.elim_inr]
      simp [cost, ocInst, ocData]
  · rw [cashE_true]; exact feas_zero .E (fun i => le_rfl) zero_le_one

lemma cashE_W2 (t : Bool) : W2 PO cashE t 0 0 = if t then 1 else 3 / 2 := by
  rw [W2_oc]
  cases t
  · rw [cashE_false]
    show h1 PO 0 - _ - _ + (_ * (0 : Inst 1 1 → ℝ) (Sum.inl 0) + _) * _
      + (_ * (0 : Inst 1 1 → ℝ) (Sum.inr 0) + _) * _ = _
    rw [h1_zero]
    simp only [sum_inst1, inv, Sum.elim_inl, Sum.elim_inr, gr_fA, gr_fE]
    simp [cost, ocInst, ocData]
  · rw [cashE_true]
    show h1 PO 0 - _ - _ + (_ * (0 : Inst 1 1 → ℝ) (Sum.inl 0) + _) * _
      + (_ * (0 : Inst 1 1 → ℝ) (Sum.inr 0) + _) * _ = _
    rw [h1_zero, cost_zero]
    simp

/-- The ETF-only root optimizer under future ETF-only trading is the cash root. -/
lemma BE_unique {BE : Inst 1 1 → ℝ} (hBE : RootOpt PO .E .E BE) : BE = 0 := by
  have hS := hS_oc
  obtain ⟨u₁, hπ, hΦ⟩ := H0_attain hS (r := .E) hBE.1
  obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget boxO hπ
  have hA : BE (Sum.inl 0) = 0 := hBE.1.2.2
  set p := BE (Sum.inr 0)
  set h := h1 PO BE
  have hnode : Feas1 PO .E (x1 PO (obsY PO true 0 : Obs 1 2) BE) h (u₁ (obsY PO true 0)) := hπ.2 _
  have huA : u₁ (obsY PO true 0) (Sum.inl 0) = 0 := hnode.2.2
  have huE := hnode.1 (Sum.inr 0)
  rw [x1_obs, gr_tE] at huE
  have hc1 := cost_nonneg PO (rates_nonneg hS) (u₁ (obsY PO true 0))
  have hWp : W2 PO (BE, u₁) true 0 0 ≤ 1 - p / 2 := by
    rw [W2_oc, sum_inst1, gr_tA, gr_tE]
    dsimp only
    rw [huA, hA]
    nlinarith
  have hWm : W2 PO (BE, u₁) false 0 0 ≤ 3 / 2 + 3 * p / 4 := by
    have := W2_le_W1m boxO hπ false (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    rw [W1m_oc, gr_fA, gr_fE] at this
    dsimp only at this
    rw [hA] at this
    nlinarith
  by_contra hne
  have hp0' : 0 ≤ p := hp0
  have hp : 0 < p := by
    rcases hp0'.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hne
      funext i
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
      · exact hA
      · exact h'.symm
  obtain ⟨hf1, -⟩ := exp_facts
  have e1 : Real.exp (-20 * (1 - p / 2)) = Real.exp (-20) * Real.exp (10 * p) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-20 * (3 / 2 + 3 * p / 4)) = Real.exp (-30) * Real.exp (-(15 * p)) := by
    rw [← Real.exp_add]; ring_nf
  have b1 := Real.add_one_le_exp (10 * p)
  have b2 := Real.add_one_le_exp (-(15 * p))
  have m1 : Real.exp (-20 * (1 - p / 2)) ≤ Real.exp (-20 * W2 PO (BE, u₁) true 0 0) :=
    Real.exp_le_exp.mpr (by linarith)
  have m2 : Real.exp (-20 * (3 / 2 + 3 * p / 4)) ≤ Real.exp (-20 * W2 PO (BE, u₁) false 0 0) :=
    Real.exp_le_exp.mpr (by linarith)
  have p20 := Real.exp_pos (-20)
  have p30 := Real.exp_pos (-30)
  have hsum : Real.exp (-20) + Real.exp (-30)
      < Real.exp (-20 * (1 - p / 2)) + Real.exp (-20 * (3 / 2 + 3 * p / 4)) := by
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left b1 p20.le, mul_le_mul_of_nonneg_left b2 p30.le,
      mul_pos hp (by linarith : (0 : ℝ) < 10 * Real.exp (-20) - 15 * Real.exp (-30))]
  -- the cash root does strictly better
  have hcash := Phi_le_H0 hS cashE_mem
  rw [Phi_oc, cashE_W2, cashE_W2] at hcash
  have hcash' : -(Real.exp (-20) + Real.exp (-30)) / 2 ≤ H0 PO .E 0 := by
    have : (cashE : Policy PO).1 = 0 := rfl
    rw [this] at hcash; norm_num at hcash ⊢; linarith
  have hlt : H0 PO .E BE < H0 PO .E 0 := by
    rw [← hΦ, Phi_oc]; linarith
  have hH := (Novel.M3EtfChannelSandwichProof.H0_range hS .E
    (Novel.M3EtfChannelSandwichProof.feas_EF hBE.1)).2
  have hH0 := (Novel.M3EtfChannelSandwichProof.H0_range hS .E (hfe0_oc .F)).2
  have hlog := Real.log_lt_log (by linarith) (by linarith : -H0 PO .E 0 < -H0 PO .E BE)
  have hopt := hBE.2 0 (hfe0_oc .E)
  simp only [cR, show (PO).rho = 20 from rfl] at hopt
  linarith

lemma hne_oc : obs PO true (0 : Fin 1) ≠ obs PO false 0 := obs_ne

lemma uC_feas : Feas1 PO .F (PO).D.x0 (PO).D.h0 (inv (7 / 15) (8 / 15)) :=
  inv_feas (by norm_num) (by norm_num) (by norm_num)

/-- With no review-1 trade, `H₀` is `Φ` of the no-trade policy. -/
lemma H0N_inv {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (h : a + p = 1) :
    H0 PO .N (inv a p) = Phi PO ((inv a p, fun _ => 0) : Policy PO) := by
  obtain ⟨u₁, hπ, hΦ⟩ := H0_attain hS_oc (r := .N) (inv_feas ha hp h)
  have : u₁ = fun _ => 0 := funext fun y => (hπ.2 y).2.2
  rw [← hΦ, this]

lemma cN_uC : cR PO .N (inv (7 / 15) (8 / 15))
    = -(1 / 20) * Real.log ((Real.exp (-(71 / 3)) + Real.exp (-(79 / 3))) / 2) := by
  simp only [cR, show (PO).rho = 20 from rfl]
  rw [H0N_inv (by norm_num) (by norm_num) (by norm_num), Phi_oc, W2_inv _ _ (by norm_num),
    W2_inv _ _ (by norm_num)]
  congr 2
  have e1 : (-20 * (gr true (Sum.inl 0) ^ 2 * (7 / 15) + gr true (Sum.inr 0) ^ 2 * (8 / 15)) : ℝ)
      = -(71 / 3) := by norm_num [gr]
  have e2 : (-20 * (gr false (Sum.inl 0) ^ 2 * (7 / 15) + gr false (Sum.inr 0) ^ 2 * (8 / 15)) : ℝ)
      = -(79 / 3) := by norm_num [gr]
  rw [e1, e2]
  ring

lemma nodeCE_uC (t : Bool) : nodeCE PO .N (inv (7 / 15) (8 / 15)) (obs PO t 0)
    = if t then 71 / 60 else 79 / 60 := by
  rw [nodeCEN_obs hq_oc hne_oc hS_oc hpi_oc uC_feas, h1_inv (by norm_num), W0_oc, div_one]
  simp only [condW, sum_inst1, cost_zero, Pi.zero_apply, Finset.sum_const_zero, add_zero,
    sub_zero, x1_oc, gross_eq]
  cases t <;> norm_num [gr, inv]

lemma nodeCE_zero (t : Bool) : nodeCE PO .N 0 (obs PO t 0) = 1 := by
  rw [nodeCEN_obs hq_oc hne_oc hS_oc hpi_oc (hfe0_oc .F), x1_zero, h1_zero, W0_oc]
  simp [condW, cost_zero]

/-- At `u`, the `θ₊` node is a sure selling node worth `2/15`; other nodes are worth `0`. -/
lemma lower_uC {y : Obs 1 2} (hy : IsNode PO y) :
    (if y = obs PO true 0 then (2 / 15 : ℝ) else 0) ≤ gain PO (inv (7 / 15) (8 / 15)) y := by
  split_ifs with hyt
  · subst hyt
    have := (nodeLower_at hS_oc uC_feas hy 0).2.1 (1 / 2) fun t s hp => by
      rw [nodePath_obs hq_oc hne_oc hpi_oc hp]; unfold gE; rw [gross_eq]; norm_num [gr]
    rw [x1_oc, W0_oc, show (PO).D.kminus (Sum.inr 0) = 0 from rfl] at this
    norm_num [gr, inv] at this ⊢
    linarith
  · exact gain_nonneg hS_oc uC_feas hy

/-- At the cash root, the `θ₊` node's cap is `0` and the `θ₋` node's is `1/2`. -/
lemma cap_zero {y : Obs 1 2} (hy : IsNode PO y) :
    gain PO 0 y ≤ if y = obs PO true 0 then 0 else 1 / 2 := by
  have key : ∀ U D : ℝ, 0 ≤ U → 0 ≤ D →
      (∀ j t s, NodePath PO y t s → gE PO j t s - 1 ≤ U ∧ 1 - gE PO j t s ≤ D) →
      gain PO 0 y ≤ U := fun U D hU hD hb => by
    have := nodeCap_at hS_oc (hfe0_oc .F) hy hU hD hb
    rw [h1_zero, W0_oc] at this
    simpa [x1_zero] using this
  split_ifs with hyt
  · subst hyt
    exact key 0 (1 / 2) le_rfl (by norm_num) fun j t s hp => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [nodePath_obs hq_oc hne_oc hpi_oc hp]; unfold gE; rw [gross_eq]; norm_num [gr]
  · obtain rfl : y = obs PO false 0 := (node_cases hq_oc hy).resolve_left hyt
    exact key (1 / 2) 0 (by norm_num) le_rfl fun j t s hp => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [nodePath_obs hq_oc hne_oc hpi_oc hp]; unfold gE; rw [gross_eq]; norm_num [gr]

lemma agg_uC : agg PO (inv (7 / 15) (8 / 15)) (fun y => if y = obs PO true 0 then 2 / 15 else 0)
    = -(1 / 20) * Real.log (1 / (1 + Real.exp (-(8 / 3))) * Real.exp (-(8 / 3))
      + (1 - 1 / (1 + Real.exp (-(8 / 3))))) := by
  rw [agg_obs hq_oc hne_oc hS_oc hpi_oc uC_feas, nodeCE_uC, nodeCE_uC, ite_eq_left rfl,
    ite_eq_right (Ne.symm hne_oc)]
  simp only [show (PO).rho = 20 from rfl, show (PO).pi0 true = 1 / 2 from rfl,
    show (PO).pi0 false = 1 / 2 from rfl, ↓reduceIte, Bool.false_eq_true]
  congr 2
  have e : Real.exp (-20 * (79 / 60)) = Real.exp (-20 * (71 / 60)) * Real.exp (-(8 / 3)) := by
    rw [← Real.exp_add]; norm_num
  have e' : Real.exp (-20 * (2 / 15)) = Real.exp (-(8 / 3)) := by norm_num
  rw [e, e', show (-20 * 0 : ℝ) = 0 by norm_num, Real.exp_zero]
  have := Real.exp_pos (-20 * (71 / 60))
  have := Real.exp_pos (-(8 / 3))
  field_simp
  ring

lemma agg_zero : agg PO 0 (fun y => if y = obs PO true 0 then 0 else 1 / 2)
    = -(1 / 20) * Real.log ((1 + Real.exp (-10)) / 2) := by
  rw [agg_obs hq_oc hne_oc hS_oc hpi_oc (hfe0_oc .F), nodeCE_zero, nodeCE_zero, ite_eq_left rfl,
    ite_eq_right (Ne.symm hne_oc)]
  simp only [show (PO).rho = 20 from rfl, show (PO).pi0 true = 1 / 2 from rfl,
    show (PO).pi0 false = 1 / 2 from rfl]
  congr 2
  rw [show (-20 * (1 / 2) : ℝ) = -10 by norm_num, show (-20 * 0 : ℝ) = 0 by norm_num,
    Real.exp_zero]
  have := Real.exp_pos (-20 * 1)
  field_simp
  ring

/-- The certified value: `1/15 - ln 2/20 + ln(1 + e^{-10})/20 > 3/100`. -/
lemma complement_value :
    3 / 100 < -(1 / 20) * Real.log (1 / (1 + Real.exp (-(8 / 3))) * Real.exp (-(8 / 3))
      + (1 - 1 / (1 + Real.exp (-(8 / 3)))))
      - (5 / 4 - -(1 / 20) * Real.log ((Real.exp (-(71 / 3)) + Real.exp (-(79 / 3))) / 2))
      - -(1 / 20) * Real.log ((1 + Real.exp (-10)) / 2) := by
  set E := Real.exp (-(8 / 3)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h1 : 1 / (1 + E) * E + (1 - 1 / (1 + E)) = 2 * E / (1 + E) := by field_simp; ring
  have h2 : (Real.exp (-(71 / 3)) + Real.exp (-(79 / 3))) / 2 = Real.exp (-(71 / 3)) * (1 + E) / 2 := by
    rw [hE, show (-(79 / 3) : ℝ) = -(71 / 3) + -(8 / 3) by norm_num, Real.exp_add]; ring
  rw [h1, h2, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hE0.ne',
    Real.log_div (by positivity) (by norm_num), Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_div (by positivity) (by norm_num), hE, Real.log_exp, Real.log_exp]
  have hl2 := Real.log_two_lt_d9
  have hl10 : 0 ≤ Real.log (1 + Real.exp (-10)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (-10)])
  linarith

theorem complementCert : ComplementCert := by
  unfold ComplementCert
  intro P u w al cN bn
  have hS : M3Setting P := hS_oc
  obtain ⟨BE, hBE⟩ := Novel.M3EtfChannelSandwichProof.rootOpt_exists hS .E .E
  have hBE0 : BE = 0 := BE_unique hBE
  subst hBE0
  have hlb : ∀ y, IsNode P y → (if y = obs P true 0 then (2 / 15 : ℝ) else 0) ≤ gain P u y :=
    fun y hy => lower_uC hy
  have hub : ∀ y, IsNode P y → gain P 0 y ≤ if y = obs P true 0 then 0 else 1 / 2 :=
    fun y hy => cap_zero hy
  have hsc := (signConditions 1 2 (Fin 1) Bool P hS).2.2.1 u 0 uC_feas hBE _ _ hlb hub
  rw [CE_FN, show cR P .N u = cN from cN_uC, show agg P u _ = al from agg_uC,
    show agg P 0 _ = bn from agg_zero] at hsc
  exact ⟨uC_feas, fun _ h => BE_unique h, CE_FN, cN_uC, hlb, agg_uC, hub, agg_zero, hsc,
    complement_value⟩

end Complement

theorem proof : Standalone.M3PremiumNodeBounds.statement :=
  ⟨decomposition, nodeLower, nodeCap, signConditions, sureActiveCert, complementCert⟩

end Novel.M3PremiumNodeBoundsProof

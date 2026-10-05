import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M2EtfExposureGeometry

/-!
# Proof of claim 005: ETF-only exposure geometry under M2's funded directional costs

Per ETF, the net outlay is `max((1 + κ⁺) d, (1 - κ⁻) d)` when `κ⁺ + κ⁻ ≥ 0`, so the sum of
the per-ETF maxima is the maximum over purchase/sale assignments. An ETF-only holding is
`(a⁻, p⁻ + d)` with cash `k⁻ - Ψ_E(d)`, and its exposure change is `(B^E)' d`. Closedness of the
exposure image uses compactness of `P_E` (closed, inside a box) in place of the paper's explicit
bisection argument.
-/

namespace Novel.M2EtfExposureGeometryProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry

variable {m n K : ℕ} {S : Type}

/-! ### The cash representation -/

/-- Per-ETF net outlay. -/
def term (kp km d : ℝ) : ℝ := d + kp * max d 0 + km * max (-d) 0

lemma coef_le_term {kp km : ℝ} (h : 0 ≤ kp + km) (b : Bool) (d : ℝ) :
    (if b then 1 + kp else 1 - km) * d ≤ term kp km d := by
  unfold term
  rcases le_or_gt 0 d with hd | hd
  · rw [max_eq_left hd, max_eq_right (by linarith)]
    cases b <;> simp <;> nlinarith
  · rw [max_eq_right hd.le, max_eq_left (by linarith)]
    cases b <;> simp <;> nlinarith

lemma coef_eq_term (kp km d : ℝ) :
    (if decide (0 ≤ d) then 1 + kp else 1 - km) * d = term kp km d := by
  unfold term
  rcases le_or_gt 0 d with hd | hd
  · rw [max_eq_left hd, max_eq_right (by linarith)]
    simp [hd]
    ring
  · rw [max_eq_right hd.le, max_eq_left (by linarith)]
    simp [not_le.mpr hd]
    ring

lemma PsiE_eq (D : Data m n K S) (d : Fin n → ℝ) :
    PsiE D d = ∑ j, term (kplusE D j) (kminusE D j) (d j) := rfl

lemma cSigma_dot (D : Data m n K S) (σ : Fin n → Bool) (d : Fin n → ℝ) :
    cSigma D σ ⬝ᵥ d = ∑ j, (if σ j then 1 + kplusE D j else 1 - kminusE D j) * d j := rfl

lemma cSigma_le (D : Data m n K S) (hr : RatesNonneg D) (σ : Fin n → Bool) (d : Fin n → ℝ) :
    cSigma D σ ⬝ᵥ d ≤ PsiE D d := by
  rw [cSigma_dot, PsiE_eq]
  exact sum_le_sum fun j _ =>
    coef_le_term (add_nonneg (hr (Sum.inr j)).1 (hr (Sum.inr j)).2) (σ j) (d j)

lemma cSigma_attains (D : Data m n K S) (d : Fin n → ℝ) :
    cSigma D (fun j => decide (0 ≤ d j)) ⬝ᵥ d = PsiE D d := by
  rw [cSigma_dot, PsiE_eq]
  exact sum_congr rfl fun j _ => coef_eq_term _ _ _

lemma PE_eq (D : Data m n K S) (hr : RatesNonneg D) :
    PE D = {d | InBounds D d ∧ ∀ σ, cSigma D σ ⬝ᵥ d ≤ k0 D} := by
  ext d
  refine and_congr Iff.rfl ⟨fun h σ => (cSigma_le D hr σ d).trans h, fun h => ?_⟩
  rw [← cSigma_attains]
  exact h _

lemma cashRepresentation (D : Data m n K S) (hr : RatesNonneg D) :
    (∀ d, (∀ σ, cSigma D σ ⬝ᵥ d ≤ PsiE D d) ∧ ∃ σ, cSigma D σ ⬝ᵥ d = PsiE D d) ∧
    PE D = {d | InBounds D d ∧ ∀ σ, cSigma D σ ⬝ᵥ d ≤ k0 D} :=
  ⟨fun d => ⟨fun σ => cSigma_le D hr σ d, _, cSigma_attains D d⟩, PE_eq D hr⟩

/-! ### The ETF-only class -/

lemma etfAction_sub (D : Data m n K S) (d : Fin n → ℝ) :
    etfAction D d - w0 D = Sum.elim (0 : Fin m → ℝ) d := by
  funext i
  simp [etfAction]

lemma cash_etfAction (D : Data m n K S) (d : Fin n → ℝ) :
    cash D (etfAction D d) = k0 D - PsiE D d := by
  have h := etfAction_sub D d
  have hs : ∑ i, (etfAction D d i - w0 D i) = ∑ j, d j := by
    have : ∀ i, etfAction D d i - w0 D i = Sum.elim (0 : Fin m → ℝ) d i :=
      fun i => congrFun h i
    simp only [this, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      sum_const_zero, zero_add]
  rw [cash, hs, h]
  simp only [tau, PsiE, kplusE, kminusE, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, neg_zero, max_self, mul_zero, sum_const_zero, zero_add, sum_add_distrib]
  ring

lemma active_etfAction (D : Data m n K S) (d : Fin n → ℝ) :
    active (etfAction D d) = active (w0 D) := by
  funext j
  simp [active, etfAction]

lemma etf_etfAction (D : Data m n K S) (d : Fin n → ℝ) :
    etf (etfAction D d) = p0 D + d := by
  funext j
  simp [etf, etfAction, p0]

lemma w0_nonneg (D : Data m n K S) (h : InitialPosition D) (i : Inst m n) : 0 ≤ w0 D i :=
  div_nonneg (h.2.1 i) h.1.le

lemma k0_nonneg (D : Data m n K S) (h : InitialPosition D) : 0 ≤ k0 D :=
  div_nonneg h.2.2.1 h.1.le

lemma E_eq (D : Data m n K S) (h : InitialPosition D) : E D = etfAction D '' PE D := by
  ext w
  constructor
  · rintro ⟨⟨hb, hc⟩, ha⟩
    refine ⟨etf w - p0 D, ⟨fun j => ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have := (hb (Sum.inr j)).1
      simp only [Pi.sub_apply, p0, etf]
      linarith
    · have := (hb (Sum.inr j)).2
      simp only [Pi.sub_apply, p0, pbar, etf]
      linarith
    · have hw : etfAction D (etf w - p0 D) = w := by
        funext i
        cases i with
        | inl j => simpa [etfAction, active] using (congrFun ha j).symm
        | inr j => simp [etfAction, etf, p0]
      have := cash_etfAction D (etf w - p0 D)
      rw [hw] at this
      linarith
    · funext i
      cases i with
      | inl j => simpa [etfAction, active] using (congrFun ha j).symm
      | inr j => simp [etfAction, etf, p0]
  · rintro ⟨d, ⟨hb, hc⟩, rfl⟩
    refine ⟨⟨fun i => ?_, ?_⟩, active_etfAction D d⟩
    · cases i with
      | inl j =>
        simp only [etfAction, Pi.add_apply, Sum.elim_inl, Pi.zero_apply, add_zero]
        exact ⟨w0_nonneg D h _, h.2.2.2 _⟩
      | inr j =>
        simp only [etfAction, Pi.add_apply, Sum.elim_inr]
        have := hb j
        simp only [p0, pbar, etf] at this
        constructor <;> linarith [this.1, this.2]
    · rw [cash_etfAction]
      linarith

lemma etfClass (D : Data m n K S) :
    (∀ d, cash D (etfAction D d) = k0 D - PsiE D d) ∧
    (InitialPosition D → E D = etfAction D '' PE D) :=
  ⟨cash_etfAction D, E_eq D⟩

/-! ### Exposure sets -/

lemma exposure_sub_of_active (D : Data m n K S) (w : Inst m n → ℝ)
    (ha : active w = active (w0 D)) :
    exposure D w - exposure D (w0 D) = D.BEᵀ *ᵥ (etf w - etf (w0 D)) := by
  simp only [exposure, ha, mulVec_sub]
  abel

lemma exposure_etfAction (D : Data m n K S) (d : Fin n → ℝ) :
    exposure D (etfAction D d) - exposure D (w0 D) = D.BEᵀ *ᵥ d := by
  rw [exposure_sub_of_active D _ (active_etfAction D d), etf_etfAction]
  congr 1
  simp [p0]

lemma DE_eq (D : Data m n K S) (h : InitialPosition D) :
    DE D = (fun d => D.BEᵀ *ᵥ d) '' PE D := by
  rw [DE, E_eq D h, Set.image_image]
  exact Set.image_congr fun d _ => exposure_etfAction D d

lemma BEset_eq (D : Data m n K S) :
    BEset D = (fun y => exposure D (w0 D) + y) '' DE D := by
  rw [BEset, DE, Set.image_image]
  exact Set.image_congr fun w _ => by abel

lemma DE_subset_LE (D : Data m n K S) : DE D ⊆ LE D := by
  rintro y ⟨w, ⟨_, ha⟩, rfl⟩
  exact ⟨_, (exposure_sub_of_active D w ha).symm⟩

lemma exposureSets (D : Data m n K S) :
    (InitialPosition D → DE D = (fun d => D.BEᵀ *ᵥ d) '' PE D) ∧
    BEset D = (fun y => exposure D (w0 D) + y) '' DE D ∧ DE D ⊆ LE D :=
  ⟨DE_eq D, BEset_eq D, DE_subset_LE D⟩

/-! ### Topological and convexity properties -/

lemma continuous_PsiE (D : Data m n K S) : Continuous (PsiE D) := by
  unfold PsiE
  fun_prop

lemma continuous_BEt (D : Data m n K S) : Continuous fun d : Fin n → ℝ => D.BEᵀ *ᵥ d := by
  refine continuous_pi fun k => ?_
  simp only [mulVec, dotProduct]
  fun_prop

lemma isClosed_PE (D : Data m n K S) : IsClosed (PE D) := by
  have h1 : IsClosed {d : Fin n → ℝ | InBounds D d} := by
    simp only [InBounds, Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun j =>
      (isClosed_le continuous_const (continuous_apply j)).inter
        (isClosed_le (continuous_apply j) continuous_const)
  exact h1.inter (isClosed_le (continuous_PsiE D) continuous_const)

lemma PE_subset_box (D : Data m n K S) : PE D ⊆ Set.Icc (-p0 D) (pbar D - p0 D) :=
  fun _ hd => ⟨fun j => (hd.1 j).1, fun j => (hd.1 j).2⟩

lemma isCompact_PE (D : Data m n K S) : IsCompact (PE D) :=
  isCompact_Icc.of_isClosed_subset (isClosed_PE D) (PE_subset_box D)

lemma isCompact_DE (D : Data m n K S) (h : InitialPosition D) : IsCompact (DE D) := by
  rw [DE_eq D h]
  exact (isCompact_PE D).image (continuous_BEt D)

lemma isCompact_BEset (D : Data m n K S) (h : InitialPosition D) : IsCompact (BEset D) := by
  rw [BEset_eq D]
  exact (isCompact_DE D h).image (continuous_const.add continuous_id)

lemma zero_mem_PE (D : Data m n K S) (h : InitialPosition D) : (0 : Fin n → ℝ) ∈ PE D := by
  refine ⟨fun j => ⟨?_, ?_⟩, ?_⟩
  · have := w0_nonneg D h (Sum.inr j)
    simp only [p0, etf, Pi.zero_apply]
    linarith
  · have := h.2.2.2 (Sum.inr j)
    simp only [p0, pbar, etf, Pi.zero_apply]
    linarith
  · have : PsiE D 0 = 0 := by simp [PsiE]
    rw [this]
    exact k0_nonneg D h

lemma convex_PE (D : Data m n K S) (hr : RatesNonneg D) : Convex ℝ (PE D) := by
  rw [PE_eq D hr]
  intro x hx y hy a b ha hb hab
  refine ⟨fun j => ⟨?_, ?_⟩, fun σ => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hp : -p0 D j = a * -p0 D j + b * -p0 D j := by linear_combination (p0 D j) * hab
    nlinarith [mul_le_mul_of_nonneg_left (hx.1 j).1 ha, mul_le_mul_of_nonneg_left (hy.1 j).1 hb]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hp : pbar D j - p0 D j = a * (pbar D j - p0 D j) + b * (pbar D j - p0 D j) := by
      linear_combination (-(pbar D j - p0 D j)) * hab
    nlinarith [mul_le_mul_of_nonneg_left (hx.1 j).2 ha, mul_le_mul_of_nonneg_left (hy.1 j).2 hb]
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hk : k0 D = a * k0 D + b * k0 D := by linear_combination (-(k0 D)) * hab
    nlinarith [mul_le_mul_of_nonneg_left (hx.2 σ) ha, mul_le_mul_of_nonneg_left (hy.2 σ) hb]

lemma convex_DE (D : Data m n K S) (h : InitialPosition D) (hr : RatesNonneg D) :
    Convex ℝ (DE D) := by
  rw [DE_eq D h]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, convex_PE D hr hx hy ha hb hab, by
    simp only [mulVec_add, mulVec_smul]⟩

lemma convex_BEset (D : Data m n K S) (h : InitialPosition D) (hr : RatesNonneg D) :
    Convex ℝ (BEset D) := by
  rw [BEset_eq D]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, convex_DE D h hr hx hy ha hb hab, ?_⟩
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(exposure D (w0 D) k)) * hab

lemma setProperties (D : Data m n K S) :
    (IsClosed (PE D) ∧ Bornology.IsBounded (PE D)) ∧
    (InitialPosition D →
      (0 : Fin n → ℝ) ∈ PE D ∧ (0 : Fin K → ℝ) ∈ DE D ∧ exposure D (w0 D) ∈ BEset D ∧
      IsClosed (DE D) ∧ IsClosed (BEset D) ∧
      Bornology.IsBounded (DE D) ∧ Bornology.IsBounded (BEset D)) ∧
    (InitialPosition D → RatesNonneg D →
      Convex ℝ (PE D) ∧ Convex ℝ (DE D) ∧ Convex ℝ (BEset D)) := by
  refine ⟨⟨isClosed_PE D, (isCompact_PE D).isBounded⟩, fun h => ?_,
    fun h hr => ⟨convex_PE D hr, convex_DE D h hr, convex_BEset D h hr⟩⟩
  have h0 := zero_mem_PE D h
  have hD0 : (0 : Fin K → ℝ) ∈ DE D := by
    rw [DE_eq D h]
    exact ⟨0, h0, mulVec_zero _⟩
  refine ⟨h0, hD0, ?_, (isCompact_DE D h).isClosed, (isCompact_BEset D h).isClosed,
    (isCompact_DE D h).isBounded, (isCompact_BEset D h).isBounded⟩
  rw [BEset_eq D]
  exact ⟨0, hD0, add_zero _⟩

/-! ### Matching -/

lemma matches_iff (D : Data m n K S) (h : InitialPosition D) (hr : RatesNonneg D)
    (δ : Fin K → ℝ) : Matches D δ ↔ ∃ d, MatchSystem D δ d := by
  have : Matches D δ ↔ δ ∈ DE D := Iff.rfl
  rw [this, DE_eq D h, PE_eq D hr]
  constructor
  · rintro ⟨d, ⟨hb, hc⟩, rfl⟩
    exact ⟨d, rfl, hb, hc⟩
  · rintro ⟨d, rfl, hb, hc⟩
    exact ⟨d, ⟨hb, hc⟩, rfl⟩

lemma matchingCriterion (D : Data m n K S) (h : InitialPosition D) (hr : RatesNonneg D)
    (δ : Fin K → ℝ) :
    (Matches D δ ↔ ∃ d, MatchSystem D δ d) ∧
    (¬ Matches D δ ↔
      δ ∉ LE D ∨
      (δ ∈ LE D ∧ ¬ ∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d) ∨
      ((∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d) ∧ ¬ ∃ d, MatchSystem D δ d)) := by
  refine ⟨matches_iff D h hr δ, ?_⟩
  rw [matches_iff D h hr δ]
  have hLE : δ ∈ LE D ↔ ∃ d, D.BEᵀ *ᵥ d = δ := Iff.rfl
  have hsys : (∃ d, MatchSystem D δ d) → ∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d :=
    fun ⟨d, h1, h2, _⟩ => ⟨d, h1, h2⟩
  have hb : (∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d) → δ ∈ LE D :=
    fun ⟨d, h1, _⟩ => ⟨d, h1⟩
  by_cases h1 : δ ∈ LE D <;> by_cases h2 : ∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d <;>
    by_cases h3 : ∃ d, MatchSystem D δ d <;> simp_all

/-! ### One ETF -/

lemma BEt_one (D : Data m 1 K S) (d : Fin 1 → ℝ) :
    D.BEᵀ *ᵥ d = d 0 • fun k => D.BE 0 k := by
  funext k
  simp [mulVec, dotProduct, mul_comm]

lemma PE_one (D : Data m 1 K S) (hp : 0 ≤ kplusE D 0) (hm : kminusE D 0 ≤ 1) (hk : 0 ≤ k0 D)
    (d : Fin 1 → ℝ) :
    d ∈ PE D ↔ -p0 D 0 ≤ d 0 ∧ d 0 ≤ min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0)) := by
  have hpos : 0 < 1 + kplusE D 0 := by linarith
  have hPsi : PsiE D d = d 0 + kplusE D 0 * max (d 0) 0 + kminusE D 0 * max (-d 0) 0 := by
    simp [PsiE]
  simp only [PE, Set.mem_ofPred_eq, InBounds, Fin.forall_fin_one, hPsi, le_min_iff,
    le_div_iff₀ hpos]
  rcases le_or_gt 0 (d 0) with hd | hd
  · rw [max_eq_left hd, max_eq_right (by linarith)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, by nlinarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, by nlinarith⟩
  · rw [max_eq_right hd.le, max_eq_left (by linarith)]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨h1, h2, by nlinarith⟩
    · rintro ⟨h1, h2, _⟩
      exact ⟨⟨h1, h2⟩, by nlinarith⟩

lemma oneEtf (D : Data m 1 K S) (hp : 0 ≤ kplusE D 0) (hm : kminusE D 0 ≤ 1) :
    (0 ≤ k0 D → ∀ d : Fin 1 → ℝ,
      d ∈ PE D ↔ -p0 D 0 ≤ d 0 ∧ d 0 ≤ min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0))) ∧
    (InitialPosition D →
      DE D = (fun t : ℝ => t • fun k => D.BE 0 k) ''
        Set.Icc (-p0 D 0) (min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0))) ∧
      ((∀ k, D.BE 0 k = 0) → DE D = {0})) := by
  refine ⟨fun hk => PE_one D hp hm hk, fun h => ?_⟩
  have hk := k0_nonneg D h
  have hDE : DE D = (fun t : ℝ => t • fun k => D.BE 0 k) ''
      Set.Icc (-p0 D 0) (min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0))) := by
    rw [DE_eq D h]
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d 0, (PE_one D hp hm hk d).mp hd, (BEt_one D d).symm⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨fun _ => t, (PE_one D hp hm hk _).mpr ht, ?_⟩
      show D.BEᵀ *ᵥ (fun _ => t) = t • fun k => D.BE 0 k
      rw [BEt_one]
  refine ⟨hDE, fun hz => ?_⟩
  have hne : (0 : Fin 1 → ℝ) ∈ PE D := zero_mem_PE D h
  have h0 := (PE_one D hp hm hk 0).mp hne
  rw [hDE]
  ext y
  simp only [Set.mem_image, Set.mem_singleton_iff]
  have hrow : (fun k => D.BE 0 k) = 0 := funext hz
  constructor
  · rintro ⟨t, _, rfl⟩
    rw [hrow, smul_zero]
  · rintro rfl
    exact ⟨0, h0, by rw [hrow, smul_zero]⟩

/-! ### Full span -/

lemma fullSpan (D : Data m n n S) (hdet : IsUnit (D.BEᵀ).det) :
    LE D = Set.univ ∧
    ∀ δ : Fin n → ℝ, (∀ d, D.BEᵀ *ᵥ d = δ ↔ d = (D.BEᵀ)⁻¹ *ᵥ δ) ∧
      (InitialPosition D → RatesNonneg D →
        (Matches D δ ↔ InBounds D ((D.BEᵀ)⁻¹ *ᵥ δ) ∧
          ∀ σ, cSigma D σ ⬝ᵥ ((D.BEᵀ)⁻¹ *ᵥ δ) ≤ k0 D)) := by
  have hright : ∀ δ, D.BEᵀ *ᵥ ((D.BEᵀ)⁻¹ *ᵥ δ) = δ := fun δ => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have huniq : ∀ δ d, D.BEᵀ *ᵥ d = δ ↔ d = (D.BEᵀ)⁻¹ *ᵥ δ := fun δ d => by
    constructor
    · rintro rfl
      rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    · rintro rfl
      exact hright δ
  refine ⟨Set.eq_univ_of_forall fun δ => ⟨_, hright δ⟩, fun δ => ⟨huniq δ, fun h hr => ?_⟩⟩
  rw [matches_iff D h hr]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    rw [(huniq δ d).mp h1] at h2 h3
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨_, hright δ, h2, h3⟩

/-! ### Missing direction -/

lemma missingDirection_one (D : Data 1 n K S) (w : Inst 1 n → ℝ)
    (ha : active w ≠ active (w0 D)) :
    exposure D w - exposure D (w0 D) ∈ LE D ↔ (fun k => D.BA 0 k) ∈ LE D := by
  set c := active w 0 - active (w0 D) 0
  have hc : c ≠ 0 := by
    intro h0
    apply ha
    funext j
    rw [Fin.fin_one_eq_zero j]
    linarith
  set e := etf w - etf (w0 D)
  set col : Fin K → ℝ := fun k => D.BA 0 k
  have hdiff : exposure D w - exposure D (w0 D) = c • col + D.BEᵀ *ᵥ e := by
    funext k
    simp only [exposure, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec,
      dotProduct, Fin.sum_univ_one, transpose_apply, c, col, e, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  constructor
  · rintro ⟨d, hd⟩
    replace hd : D.BEᵀ *ᵥ d = c • col + D.BEᵀ *ᵥ e := hd
    refine ⟨c⁻¹ • (d - e), ?_⟩
    show D.BEᵀ *ᵥ (c⁻¹ • (d - e)) = col
    rw [mulVec_smul, mulVec_sub, hd, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  · rintro ⟨d, hd⟩
    replace hd : D.BEᵀ *ᵥ d = col := hd
    refine ⟨c • d + e, ?_⟩
    show D.BEᵀ *ᵥ (c • d + e) = c • col + D.BEᵀ *ᵥ e
    rw [mulVec_add, mulVec_smul, hd]

theorem proof : Standalone.M2EtfExposureGeometry.statement :=
  ⟨fun _ _ _ _ D hr => cashRepresentation D hr,
   fun _ _ _ _ D => etfClass D,
   fun _ _ _ _ D => exposureSets D,
   fun _ _ _ _ D => setProperties D,
   fun _ _ _ _ D h hr δ => matchingCriterion D h hr δ,
   fun _ _ _ D hp hm => oneEtf D hp hm,
   fun _ _ _ D hdet => fullSpan D hdet,
   ⟨fun _ _ _ D w ha => missingDirection_one D w ha, fun _ _ _ _ _ _ hF ha => ⟨hF, ha⟩⟩⟩

end Novel.M2EtfExposureGeometryProof

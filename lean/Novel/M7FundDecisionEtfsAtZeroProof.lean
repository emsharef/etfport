import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.IntermediateValue
import Standalone.M7FundDecisionEtfsAtZero
import Novel.M7TwoStageExactnessLossProof

/-!
# Claim 040: proof

Parts 0 and 1 reuse claim 104's proof: the score split, the reference-case marginals and the AX-13
criterion `jointOptimality`. Parts 2-5 work in the claim's coordinates. The exposure problem is a
strictly concave quadratic under bound constraints; its KKT conditions are proved directly by
one-coordinate perturbations, and existence by coercivity. The one estimate behind continuity and
differentiability is the complementarity inequality `(ζ' - ζ)'(w' - w) ≤ (ζ' - ζ)'(q' - q)`. It gives
`‖w' - w‖_Σ ≤ ‖q' - q‖_Σ`, so the remainder of `V_E` is at most `γ ‖q' - q‖²_Σ`.
-/

namespace Novel.M7FundDecisionEtfsAtZeroProof

open Matrix Standalone.M7FundDecisionEtfsAtZero Filter Topology

noncomputable section

/-! ### Quadratic forms -/

section Quad

variable {ι : Type*} [Fintype ι]

/-- `u'Au`. -/
def qf (A : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u)

omit [Fintype ι] in
lemma symm_of_posDef {A : Matrix ι ι ℝ} (h : A.PosDef) : Aᵀ = A := by
  have := h.isHermitian.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma dot_symm {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]

lemma qf_add {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    qf A (u + v) = qf A u + 2 * (u ⬝ᵥ (A *ᵥ v)) + qf A v := by
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct]
  rw [dot_symm hs v u]; ring

lemma qf_smul (A : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) : qf A (c • u) = c ^ 2 * qf A u := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

lemma qf_sub {A : Matrix ι ι ℝ} (u v : ι → ℝ) : qf A (u - v) = qf A (v - u) := by
  rw [show u - v = (-1 : ℝ) • (v - u) by simp, qf_smul]; ring

lemma qf_nonneg {A : Matrix ι ι ℝ} (h : A.PosDef) (u : ι → ℝ) : 0 ≤ qf A u := by
  by_cases hu : u = 0
  · simp [qf, hu]
  · have := h.dotProduct_mulVec_pos hu
    simp only [star_trivial] at this
    exact this.le

lemma eq_of_qf {A : Matrix ι ι ℝ} (h : A.PosDef) {u : ι → ℝ} (hu : qf A u ≤ 0) : u = 0 := by
  by_contra h0
  have := h.dotProduct_mulVec_pos h0
  simp only [star_trivial] at this
  exact absurd hu (not_le.mpr this)

/-- Cauchy-Schwarz for a positive definite form. -/
lemma cs {A : Matrix ι ι ℝ} (h : A.PosDef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ qf A u * qf A v := by
  have hs := symm_of_posDef h
  by_cases hv : v = 0
  · simp [qf, hv]
  have hpv : 0 < qf A v := by
    have := h.dotProduct_mulVec_pos hv
    simpa only [star_trivial, qf] using this
  have key := qf_nonneg h (qf A v • u - (u ⬝ᵥ (A *ᵥ v)) • v)
  rw [sub_eq_add_neg, qf_add hs, ← neg_smul, qf_smul, qf_smul] at key
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  nlinarith

lemma le_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

lemma abs_le_of_sq_le' {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b :=
  abs_le.mpr ⟨by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)], le_of_sq_le h hb⟩

lemma continuous_qf (A : Matrix ι ι ℝ) : Continuous (qf A) := by
  unfold qf; fun_prop

/-- An upper bound `u'Au ≤ C ‖u‖²` in the sup norm. -/
lemma qf_le_norm (A : Matrix ι ι ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : ι → ℝ, qf A u ≤ C * ‖u‖ ^ 2 := by
  refine ⟨∑ i, ∑ j, |A i j|, by positivity, fun u => ?_⟩
  have hu : ∀ i, |u i| ≤ ‖u‖ := fun i => by
    have := norm_le_pi_norm u i; rwa [Real.norm_eq_abs] at this
  simp only [qf, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := hu i; have h2 := hu j
  have : u i * (A i j * u j) ≤ |u i| * |A i j| * |u j| := by
    rw [← abs_mul, ← abs_mul, ← mul_assoc]; exact le_abs_self _
  have h3 : |u i| * |u j| ≤ ‖u‖ ^ 2 := by
    rw [sq]; exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [abs_nonneg (A i j), abs_nonneg (u i), abs_nonneg (u j)]

/-- Coercivity: `ε ‖u‖² ≤ u'Au` for a positive definite `A`. -/
lemma coercive {A : Matrix ι ι ℝ} (h : A.PosDef) :
    ∃ ε, 0 < ε ∧ ∀ u : ι → ℝ, ε * ‖u‖ ^ 2 ≤ qf A u := by
  by_cases hS : (Metric.sphere (0 : ι → ℝ) 1).Nonempty
  · obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hS
      (continuous_qf A).continuousOn
    have hv0 : v ≠ 0 := by
      intro h0; rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hv; exact zero_ne_one hv
    refine ⟨qf A v, by
      have := h.dotProduct_mulVec_pos hv0; simpa only [star_trivial, qf] using this, fun u => ?_⟩
    by_cases hu : u = 0
    · simp [hu, qf]
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmem : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hmin hmem
    simp only [Set.mem_ofPred_eq] at h1
    rw [qf_smul] at h1
    have e : u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc qf A v * ‖u‖ ^ 2 ≤ ‖u‖⁻¹ ^ 2 * qf A u * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = qf A u := by field_simp
  · refine ⟨1, one_pos, fun u => ?_⟩
    by_cases hu : u = 0
    · simp [hu, qf]
    exact absurd ⟨‖u‖⁻¹ • u, by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.mpr hu).ne']⟩ hS

end Quad

lemma dotCLM_apply {k : ℕ} (g d : Fin k → ℝ) : dotCLM g d = g ⬝ᵥ d := by
  simp [dotCLM, dotProduct]

/-- A quadratic remainder gives the derivative. -/
lemma hasFDerivAt_of_sq {k : ℕ} {f : (Fin k → ℝ) → ℝ} {L : (Fin k → ℝ) →L[ℝ] ℝ} {x : Fin k → ℝ} {C : ℝ}
    (h : ∀ y, |f y - f x - L (y - x)| ≤ C * ‖y - x‖ ^ 2) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun d : Fin k → ℝ => f (x + d) - f x - L d) =O[𝓝 0] fun d => ‖d‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun d => ?_)
    have := h (x + d)
    simp only [add_sub_cancel_left] at this
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    exact this
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- `a ≤ b s` for all small `s > 0` gives `a ≤ 0`. -/
lemma nonpos_of_small {a b δ : ℝ} (hδ : 0 < δ) (h : ∀ s, 0 < s → s < δ → a ≤ b * s) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  set s := min (δ / 2) (a / (2 * (|b| + 1))) with hs
  have hb1 : 0 < |b| + 1 := by positivity
  have s0 : 0 < s := lt_min (by linarith) (by positivity)
  have s1 : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have s2 : s ≤ a / (2 * (|b| + 1)) := min_le_right _ _
  have h1 := h s s0 s1
  have h2 : b * s ≤ (|b| + 1) * s := by nlinarith [le_abs_self b]
  have h3 : (|b| + 1) * s ≤ a / 2 := by
    calc (|b| + 1) * s ≤ (|b| + 1) * (a / (2 * (|b| + 1))) := mul_le_mul_of_nonneg_left s2 hb1.le
      _ = a / 2 := by field_simp
  linarith

/-! ### Part 2: the exposure problem -/

section Exposure

variable {M N : ℕ} (P : Coord M N)

/-- The smooth ETF marginal's negative, `γ Σ w - μ`. -/
def zof (w : Fin M → ℝ) : Fin M → ℝ := P.gamma • (P.Sig *ᵥ w) - P.mu

variable {P}

lemma zeta_eq (q : Fin M → ℝ) : zeta P q = zof P (wopt P q) := rfl

lemma GE_add (hs : P.Sigᵀ = P.Sig) (w d : Fin M → ℝ) :
    GE P (w + d) = GE P w - zof P w ⬝ᵥ d - P.gamma / 2 * qf P.Sig d := by
  have := qf_add hs w d
  simp only [qf] at this
  simp only [GE, zof, qf, dotProduct_add, this, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (P.Sig *ᵥ w) d, dot_symm hs d w]; ring

lemma isClosed_Wset (q : Fin M → ℝ) : IsClosed (Wset q) := by
  have : Wset q = ⋂ j, {w : Fin M → ℝ | q j ≤ w j} := by ext w; simp [Wset]
  rw [this]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)

lemma continuous_GE : Continuous (GE P) := by
  unfold GE; fun_prop

/-- KKT sufficiency, with the strong-concavity margin. -/
lemma kkt_suff (hs : P.Sigᵀ = P.Sig) {q w : Fin M → ℝ}
    (hz : ∀ j, 0 ≤ zof P w j ∧ zof P w j * (w j - q j) = 0) :
    ∀ w' ∈ Wset q, GE P w' ≤ GE P w - P.gamma / 2 * qf P.Sig (w' - w) := by
  intro w' hw'
  have e := GE_add hs w (w' - w)
  rw [add_sub_cancel] at e
  have : 0 ≤ zof P w ⬝ᵥ (w' - w) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have h1 := (hz j).1; have h2 := (hz j).2; have h3 := hw' j
    simp only [Pi.sub_apply]
    nlinarith
  linarith

lemma single_dot (z : Fin M → ℝ) (j : Fin M) (s : ℝ) : z ⬝ᵥ (s • Pi.single j 1) = s * z j := by
  simp [dotProduct_smul]

lemma qf_single (A : Matrix (Fin M) (Fin M) ℝ) (j : Fin M) (s : ℝ) :
    qf A (s • Pi.single j 1) = s ^ 2 * A j j := by
  rw [qf_smul]; simp [qf]

/-- KKT necessity by one-coordinate perturbations. -/
lemma kkt_nec (hs : P.Sigᵀ = P.Sig) {q w : Fin M → ℝ} (hw : w ∈ Wset q)
    (hmax : IsMaxOn (GE P) (Wset q) w) : ∀ j, 0 ≤ zof P w j ∧ zof P w j * (w j - q j) = 0 := by
  intro j
  have up : ∀ s : ℝ, 0 < s → -zof P w j ≤ P.gamma / 2 * P.Sig j j * s := fun s hs0 => by
    have hmem : w + s • Pi.single j 1 ∈ Wset q := fun l => by
      by_cases h : l = j
      · subst h; simp; linarith [hw l]
      · simp [h, hw l]
    have := hmax hmem
    simp only [Set.mem_ofPred_eq] at this
    rw [GE_add hs, single_dot, qf_single] at this
    nlinarith
  have h0 : 0 ≤ zof P w j := by
    have := nonpos_of_small one_pos fun s hs0 _ => up s hs0
    linarith
  refine ⟨h0, ?_⟩
  rcases (hw j).lt_or_eq with hlt | heq
  · have dn : ∀ s : ℝ, 0 < s → s < w j - q j → zof P w j ≤ P.gamma / 2 * P.Sig j j * s := fun s hs0 hs1 => by
      have hmem : w + (-s) • Pi.single j 1 ∈ Wset q := fun l => by
        by_cases h : l = j
        · subst h; simp; linarith
        · simp [h, hw l]
      have := hmax hmem
      simp only [Set.mem_ofPred_eq] at this
      rw [GE_add hs, single_dot, qf_single] at this
      nlinarith
    have := nonpos_of_small (by linarith) dn
    have : zof P w j = 0 := le_antisymm this h0
    rw [this, zero_mul]
  · rw [← heq, sub_self, mul_zero]

lemma exists_max (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    ∃ w, w ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) w := by
  obtain ⟨ε, hε, hco⟩ := coercive hS
  set g := GE P q
  set B := ∑ i, |P.mu i|
  set K := Wset q ∩ {w | g ≤ GE P w}
  have hB : ∀ w : Fin M → ℝ, P.mu ⬝ᵥ w ≤ B * ‖w‖ := fun w => by
    simp only [dotProduct, B, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have := norm_le_pi_norm w i; rw [Real.norm_eq_abs] at this
    calc P.mu i * w i ≤ |P.mu i * w i| := le_abs_self _
      _ = |P.mu i| * |w i| := abs_mul _ _
      _ ≤ |P.mu i| * ‖w‖ := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  set c := 2 / (P.gamma * ε)
  have hc : 0 < c := by positivity
  have hbd : ∀ w ∈ K, ‖w‖ ≤ max 1 (c * (B + |g|)) := fun w hw => by
    have h1 := hw.2
    simp only [Set.mem_ofPred_eq, GE] at h1
    have h2 := hco w
    have h3 := hB w
    simp only [qf] at h2
    by_contra hlt
    push Not at hlt
    have t1 : 1 < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hlt
    have t2 : c * (B + |g|) < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hlt
    have hg : -|g| ≤ g := neg_abs_le g
    have k1 : P.gamma / 2 * (ε * ‖w‖ ^ 2) ≤ P.gamma / 2 * (w ⬝ᵥ (P.Sig *ᵥ w)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have k2 : |g| ≤ |g| * ‖w‖ := le_mul_of_one_le_right (abs_nonneg g) t1.le
    have key : P.gamma * ε / 2 * ‖w‖ ^ 2 ≤ (B + |g|) * ‖w‖ := by nlinarith
    have : ‖w‖ ≤ c * (B + |g|) := by
      have hn : 0 < ‖w‖ := by linarith
      have : P.gamma * ε / 2 * ‖w‖ ≤ B + |g| := by nlinarith
      calc ‖w‖ = c * (P.gamma * ε / 2 * ‖w‖) := by simp only [c]; field_simp
        _ ≤ c * (B + |g|) := mul_le_mul_of_nonneg_left this hc.le
    linarith
  have hK : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ((isClosed_Wset q).inter
      (isClosed_le continuous_const continuous_GE)) ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨_, fun w hw => by rw [Metric.mem_closedBall, dist_zero_right]; exact hbd w hw⟩
  have hqK : q ∈ K := ⟨fun j => le_rfl, show g ≤ GE P q from le_rfl⟩
  obtain ⟨w, hwK, hmax⟩ := hK.exists_isMaxOn ⟨q, hqK⟩ continuous_GE.continuousOn
  refine ⟨w, hwK.1, fun w' hw' => ?_⟩
  by_cases h : g ≤ GE P w'
  · exact hmax ⟨hw', h⟩
  · push Not at h
    have := hmax hqK
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith

lemma max_unique (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) {q w w' : Fin M → ℝ}
    (hw : w ∈ Wset q) (hm : IsMaxOn (GE P) (Wset q) w) (hw' : w' ∈ Wset q)
    (hm' : IsMaxOn (GE P) (Wset q) w') : w' = w := by
  have hs := symm_of_posDef hS
  have h1 := kkt_suff hs (kkt_nec hs hw hm) w' hw'
  have h2 := hm' hw
  simp only [Set.mem_ofPred_eq] at h2
  have : qf P.Sig (w' - w) ≤ 0 := by
    have := qf_nonneg hS (w' - w)
    nlinarith
  exact sub_eq_zero.mp (eq_of_qf hS this)

lemma wopt_spec (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    wopt P q ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) (wopt P q) :=
  Classical.epsilon_spec (exists_max hγ hS q)

lemma zeta_kkt (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    ∀ j, 0 ≤ zeta P q j ∧ zeta P q j * (wopt P q j - q j) = 0 :=
  kkt_nec (symm_of_posDef hS) (wopt_spec hγ hS q).1 (wopt_spec hγ hS q).2

lemma VE_eq (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) : VE P q = GE P (wopt P q) := by
  obtain ⟨h1, h2⟩ := wopt_spec hγ hS q
  exact IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ h1, by
    rintro _ ⟨w, hw, rfl⟩; exact h2 hw⟩

lemma kkt_iff (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q w ζ : Fin M → ℝ) :
    (w ∈ Wset q ∧ (∀ j, 0 ≤ ζ j ∧ ζ j * (w j - q j) = 0) ∧ P.gamma • (P.Sig *ᵥ w) - P.mu = ζ) ↔
      (w = wopt P q ∧ ζ = zeta P q) := by
  have hs := symm_of_posDef hS
  constructor
  · rintro ⟨hw, hz, rfl⟩
    have hm : IsMaxOn (GE P) (Wset q) w := fun w' hw' => by
      have := kkt_suff hs hz w' hw'
      have := qf_nonneg hS (w' - w)
      simp only [Set.mem_ofPred_eq]; nlinarith
    have := max_unique hγ hS (wopt_spec hγ hS q).1 (wopt_spec hγ hS q).2 hw hm
    exact ⟨this, by rw [this]; rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(wopt_spec hγ hS q).1, zeta_kkt hγ hS q, rfl⟩

/-- The complementarity estimate: `γ ‖w' - w‖²_Σ ≤ (ζ' - ζ)'(q' - q)`. -/
lemma compl (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q q' : Fin M → ℝ) :
    P.gamma * qf P.Sig (wopt P q' - wopt P q) ≤ (zeta P q' - zeta P q) ⬝ᵥ (q' - q) := by
  have hk := zeta_kkt hγ hS q
  have hk' := zeta_kkt hγ hS q'
  have hw := (wopt_spec hγ hS q).1
  have hw' := (wopt_spec hγ hS q').1
  have e : (zeta P q' - zeta P q) ⬝ᵥ (wopt P q' - wopt P q) = P.gamma * qf P.Sig (wopt P q' - wopt P q) := by
    simp only [zeta, qf, sub_sub_sub_cancel_right, ← smul_sub, ← mulVec_sub, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm]
  rw [← e]
  simp only [dotProduct]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Pi.sub_apply]
  have a1 := (hk j).1; have a2 := (hk j).2; have a3 := (hk' j).1; have a4 := (hk' j).2
  have b1 := hw j; have b2 := hw' j
  nlinarith

lemma zeta_sub (q q' : Fin M → ℝ) :
    zeta P q' - zeta P q = P.gamma • (P.Sig *ᵥ (wopt P q' - wopt P q)) := by
  simp only [zeta, mulVec_sub, smul_sub]; abel

/-- `‖w' - w‖_Σ ≤ ‖q' - q‖_Σ`, and the cross term `(ζ' - ζ)'(q' - q) ≤ γ ‖q' - q‖²_Σ`. -/
lemma lip (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q q' : Fin M → ℝ) :
    qf P.Sig (wopt P q' - wopt P q) ≤ qf P.Sig (q' - q) ∧
      0 ≤ (zeta P q' - zeta P q) ⬝ᵥ (q' - q) ∧
      (zeta P q' - zeta P q) ⬝ᵥ (q' - q) ≤ P.gamma * qf P.Sig (q' - q) := by
  set d := wopt P q' - wopt P q
  set e := q' - q
  have h1 := compl hγ hS q q'
  have hx : (zeta P q' - zeta P q) ⬝ᵥ e = P.gamma * (d ⬝ᵥ (P.Sig *ᵥ e)) := by
    rw [zeta_sub, smul_dotProduct, smul_eq_mul, dotProduct_comm, dot_symm (symm_of_posDef hS)]
  rw [hx] at h1 ⊢
  have hd := qf_nonneg hS d
  have he := qf_nonneg hS e
  have hc := cs hS d e
  have h2 : qf P.Sig d ≤ d ⬝ᵥ (P.Sig *ᵥ e) := by
    have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hγ.le)
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul, one_mul] at this
  have h3 : qf P.Sig d ≤ qf P.Sig e := by
    rcases hd.lt_or_eq with hlt | heq
    · nlinarith
    · rw [← heq]; exact he
  refine ⟨h3, by nlinarith, ?_⟩
  have : (d ⬝ᵥ (P.Sig *ᵥ e)) ^ 2 ≤ (qf P.Sig e) ^ 2 := by nlinarith
  have := le_of_sq_le this he
  nlinarith

/-- The supergradient inequality `V_E(q') ≤ V_E(q) - ζ(q)'(q' - q)`. -/
lemma VE_le (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q q' : Fin M → ℝ) :
    VE P q' ≤ VE P q - zeta P q ⬝ᵥ (q' - q) := by
  have hs := symm_of_posDef hS
  rw [VE_eq hγ hS, VE_eq hγ hS]
  have e := GE_add hs (wopt P q) (wopt P q' - wopt P q)
  rw [add_sub_cancel] at e
  have hk := zeta_kkt hγ hS q
  have hw' := (wopt_spec hγ hS q').1
  have h1 : zeta P q ⬝ᵥ (q' - q) ≤ zof P (wopt P q) ⬝ᵥ (wopt P q' - wopt P q) := by
    simp only [← zeta_eq, dotProduct]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [Pi.sub_apply]
    have a1 := (hk j).1; have a2 := (hk j).2; have b := hw' j
    nlinarith
  have := qf_nonneg hS (wopt P q' - wopt P q)
  nlinarith

lemma VE_rem (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q q' : Fin M → ℝ) :
    |VE P q' - VE P q + zeta P q ⬝ᵥ (q' - q)| ≤ P.gamma * qf P.Sig (q' - q) := by
  have h1 := VE_le hγ hS q q'
  have h2 := VE_le hγ hS q' q
  have h3 := (lip hγ hS q q').2.2
  have e : zeta P q' ⬝ᵥ (q - q') = -(zeta P q' ⬝ᵥ (q' - q)) := by
    rw [← dotProduct_neg, neg_sub]
  have e2 : (zeta P q' - zeta P q) ⬝ᵥ (q' - q) = zeta P q' ⬝ᵥ (q' - q) - zeta P q ⬝ᵥ (q' - q) :=
    sub_dotProduct _ _ _
  have hn := (lip hγ hS q q').2.1
  rw [abs_le]; constructor <;> nlinarith

theorem atZero_core (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    (∃! w, w ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) w) ∧
    (wopt P q ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) (wopt P q)) ∧ VE P q = GE P (wopt P q) :=
  ⟨⟨wopt P q, wopt_spec hγ hS q, fun _ hw =>
    max_unique hγ hS (wopt_spec hγ hS q).1 (wopt_spec hγ hS q).2 hw.1 hw.2⟩,
    wopt_spec hγ hS q, VE_eq hγ hS q⟩

theorem valueFn (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) :
    ConcaveOn ℝ Set.univ (VE P) ∧ ∀ q, HasFDerivAt (VE P) (dotCLM (-zeta P q)) q := by
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun q => ?_⟩
  · set z := a • x + b • y
    have h1 := VE_le hγ hS z x
    have h2 := VE_le hγ hS z y
    have e : a * (zeta P z ⬝ᵥ (x - z)) + b * (zeta P z ⬝ᵥ (y - z)) = 0 := by
      simp only [z, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hb' : b = 1 - a := by linarith
      subst hb'; ring
    simp only [smul_eq_mul]
    have k1 := mul_le_mul_of_nonneg_left h1 ha
    have k2 := mul_le_mul_of_nonneg_left h2 hb
    have k3 : VE P z = a * VE P z + b * VE P z := by rw [← add_mul, hab, one_mul]
    rw [mul_sub] at k1 k2
    linarith
  · obtain ⟨C, hC0, hC⟩ := qf_le_norm P.Sig
    refine hasFDerivAt_of_sq (C := P.gamma * C) fun y => ?_
    rw [dotCLM_apply, neg_dotProduct, sub_neg_eq_add]
    calc _ ≤ P.gamma * qf P.Sig (y - q) := VE_rem hγ hS q y
      _ ≤ P.gamma * (C * ‖y - q‖ ^ 2) := mul_le_mul_of_nonneg_left (hC _) hγ.le
      _ = _ := by ring

end Exposure

/-! ### Part 2: the Schur-block candidate -/

section Blocks

variable {M N : ℕ} {P : Coord M N}

lemma split_sum {n : ℕ} (Z : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ j, f j = ∑ j : In Z, f j + ∑ j : Out Z, f j := by
  convert (Fintype.sum_subtype_add_sum_subtype (· ∈ Z) f).symm using 3
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

lemma split_mulVec (Z : Finset (Fin M)) (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) (j : Fin M) :
    (A *ᵥ v) j = ∑ k : In Z, A j k * v k + ∑ k : Out Z, A j k * v k :=
  split_sum Z _

lemma scc_posDef (hS : P.Sig.PosDef) (Z : Finset (Fin M)) : (Scc P Z).PosDef :=
  hS.submatrix Subtype.val_injective

lemma scc_unit (hS : P.Sig.PosDef) (Z : Finset (Fin M)) : IsUnit (Scc P Z).det :=
  (isUnit_iff_isUnit_det _).mp (scc_posDef hS Z).isUnit

/-- The candidate's free block `w_c = Σ_cc⁻¹(μ_c/γ - Σ_cZ q_Z)`. -/
def wc (P : Coord M N) (Z : Finset (Fin M)) (q : Fin M → ℝ) : Out Z → ℝ :=
  (Scc P Z)⁻¹ *ᵥ ((fun k : Out Z => P.mu k / P.gamma) - ScZ P Z *ᵥ fun k : In Z => q k)

lemma wcand_in {Z : Finset (Fin M)} {q : Fin M → ℝ} (j : In Z) : wcand P Z q j = q j := by
  simp [wcand, j.2]

lemma wcand_out {Z : Finset (Fin M)} {q : Fin M → ℝ} (j : Out Z) : wcand P Z q j = wc P Z q j := by
  simp [wcand, j.2, wc]

/-- Rows of `Σ w` for `w = (q_Z, v)`, on `c` and on `Z`. -/
lemma rows_out (Z : Finset (Fin M)) (w : Fin M → ℝ) (j : Out Z) :
    (P.Sig *ᵥ w) j = (ScZ P Z *ᵥ fun k : In Z => w k) j + (Scc P Z *ᵥ fun k : Out Z => w k) j := by
  rw [split_mulVec Z]; rfl

lemma rows_in (Z : Finset (Fin M)) (w : Fin M → ℝ) (j : In Z) :
    (P.Sig *ᵥ w) j = (SZZ P Z *ᵥ fun k : In Z => w k) j + (SZc P Z *ᵥ fun k : Out Z => w k) j := by
  rw [split_mulVec Z]; rfl

lemma inZ_wcand {Z : Finset (Fin M)} {q : Fin M → ℝ} :
    (fun k : In Z => wcand P Z q k) = fun k : In Z => q k := funext fun k => wcand_in k

lemma outZ_wcand {Z : Finset (Fin M)} {q : Fin M → ℝ} :
    (fun k : Out Z => wcand P Z q k) = wc P Z q := funext fun k => wcand_out k

lemma mu_div (Z : Finset (Fin M)) :
    (fun k : Out Z => P.mu k / P.gamma) = P.gamma⁻¹ • fun k : Out Z => P.mu k := by
  funext k; simp [div_eq_inv_mul]

/-- The candidate's gradient: `γ Σ w^Z - μ` is `ζ_Z` on `Z` and `0` on `c`. -/
lemma cand_out (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (Z : Finset (Fin M)) (q : Fin M → ℝ) (j : Out Z) :
    zof P (wcand P Z q) j = 0 := by
  have hU := scc_unit hS Z
  simp only [zof, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [rows_out Z, inZ_wcand, outZ_wcand, wc, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  simp only [Pi.sub_apply]
  field_simp
  ring

lemma cand_in (hγ : 0 < P.gamma) (Z : Finset (Fin M)) (q : Fin M → ℝ) (j : In Z) :
    zof P (wcand P Z q) j = zcand P Z q j := by
  simp only [zof, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [rows_in Z, inZ_wcand, outZ_wcand, wc, mu_div]
  simp only [zcand, schur, muZc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_sub, mulVec_smul,
    sub_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  field_simp
  ring

/-- A `w` with `w_Z = q_Z` and a vanishing gradient on `c` is the candidate. -/
lemma eq_wcand (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) {Z : Finset (Fin M)} {q w : Fin M → ℝ}
    (hZ : ∀ j ∈ Z, w j = q j) (hc : ∀ j, j ∉ Z → zof P w j = 0) : w = wcand P Z q := by
  have hU := scc_unit hS Z
  have hwZ : (fun k : In Z => w k) = fun k : In Z => q k := funext fun k => hZ k k.2
  have hrow : Scc P Z *ᵥ (fun k : Out Z => w k) =
      (fun k : Out Z => P.mu k / P.gamma) - ScZ P Z *ᵥ fun k : In Z => q k := by
    funext j
    have h := hc j j.2
    simp only [zof, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [rows_out Z, hwZ] at h
    simp only [Pi.sub_apply]
    field_simp
    linarith
  have hwc : (fun k : Out Z => w k) = wc P Z q := by
    rw [wc, ← hrow, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  funext j
  by_cases h : j ∈ Z
  · rw [hZ j h, wcand_in (Z := Z) ⟨j, h⟩]
  · rw [wcand_out (Z := Z) ⟨j, h⟩, ← hwc]

theorem cand_iff (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) (Z : Finset (Fin M)) :
    ((∀ j, 0 ≤ zcand P Z q j) ∧ ∀ j, j ∉ Z → q j ≤ wcand P Z q j) ↔
      (wcand P Z q = wopt P q ∧ (∀ j : In Z, zeta P q j = zcand P Z q j) ∧
        ∀ j, j ∉ Z → zeta P q j = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hfeas : wcand P Z q ∈ Wset q := fun j => by
      by_cases h : j ∈ Z
      · rw [wcand_in (Z := Z) ⟨j, h⟩]
      · exact h2 j h
    have hk : ∀ j, 0 ≤ zof P (wcand P Z q) j ∧ zof P (wcand P Z q) j * (wcand P Z q j - q j) = 0 :=
      fun j => by
        by_cases h : j ∈ Z
        · have e1 := cand_in hγ Z q ⟨j, h⟩
          have e2 := wcand_in (P := P) (q := q) (Z := Z) ⟨j, h⟩
          simp only at e1 e2
          rw [e1, e2]; exact ⟨h1 _, by ring⟩
        · have e1 := cand_out hγ hS Z q ⟨j, h⟩
          simp only at e1
          rw [e1]; exact ⟨le_rfl, by ring⟩
    obtain ⟨hw, hz⟩ := (kkt_iff hγ hS q _ _).mp ⟨hfeas, hk, rfl⟩
    refine ⟨hw, fun j => ?_, fun j hj => ?_⟩
    · rw [← hz]; exact cand_in hγ Z q j
    · rw [← hz]; exact cand_out hγ hS Z q ⟨j, hj⟩
  · rintro ⟨hw, hz, -⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rw [← hz]; exact (zeta_kkt hγ hS q j).1
    · rw [hw]; exact (wopt_spec hγ hS q).1 j

lemma wopt_eq_cand (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    wopt P q = wcand P (Zset P q) q := by
  refine eq_wcand hγ hS (fun j hj => (Finset.mem_filter.mp hj).2) fun j hj => ?_
  have hne : wopt P q j ≠ q j := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hk := zeta_kkt hγ hS q j
  have hpos : wopt P q j - q j ≠ 0 := sub_ne_zero.mpr hne
  exact (mul_eq_zero.mp hk.2).resolve_right hpos

theorem zset_cond (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    (∀ j, 0 ≤ zcand P (Zset P q) q j) ∧ ∀ j, j ∉ Zset P q → q j ≤ wcand P (Zset P q) q j := by
  have hw := wopt_eq_cand hγ hS q
  refine (cand_iff hγ hS q _).mpr ⟨hw.symm, fun j => ?_, fun j hj => ?_⟩
  · rw [zeta_eq, hw]; exact cand_in hγ _ q j
  · rw [zeta_eq, hw]; exact cand_out hγ hS _ q ⟨j, hj⟩

/-- `ζ(q)` on `Z(q)` is `ζ_Z`, and `0` off it. -/
lemma zeta_blocks (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) :
    (∀ j : In (Zset P q), zeta P q j = zcand P (Zset P q) q j) ∧ ∀ j, j ∉ Zset P q → zeta P q j = 0 :=
  ((cand_iff hγ hS q _).mp (zset_cond hγ hS q)).2

theorem atZero : AtZero := by
  intro M N P hγ hS q
  obtain ⟨h1, h2, h3⟩ := atZero_core hγ hS q
  exact ⟨h1, h2, h3, kkt_iff hγ hS q, cand_iff hγ hS q, zset_cond hγ hS q⟩

theorem valueFn' : ValueFn := fun _ _ _ hγ hS => valueFn hγ hS

end Blocks

/-! ### Part 3: the fund problem -/

section Fund

variable {M N : ℕ} {P : Coord M N}

lemma hyp_gamma (h : Hyp P) : 0 < P.gamma := h.1
lemma hyp_sig (h : Hyp P) : P.Sig.PosDef := h.2.1
lemma hyp_V (h : Hyp P) : P.V.PosDef := h.2.2.1

lemma dot_Qt (ζ : Fin M → ℝ) (d : Fin N → ℝ) : ζ ⬝ᵥ (P.Q *ᵥ d) = (P.Qᵀ *ᵥ ζ) ⬝ᵥ d := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma qf_Q (d : Fin N → ℝ) : qf P.Sig (P.Q *ᵥ d) = qf (P.Qᵀ * P.Sig * P.Q) d := by
  simp only [qf]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec d, vecMul_transpose]

/-- The exact expansion of the smooth part, with the `V_E` remainder. -/
lemma smooth_expand (hV : P.Vᵀ = P.V) (x x' : Fin N → ℝ) :
    smooth P x' - smooth P x - Gm P x ⬝ᵥ (x' - x) =
      -(P.gamma / 2 * qf P.V (x' - x)) +
        (VE P (P.Q *ᵥ x') - VE P (P.Q *ᵥ x) + zeta P (P.Q *ᵥ x) ⬝ᵥ (P.Q *ᵥ x' - P.Q *ᵥ x)) := by
  have e := qf_add hV x (x' - x)
  rw [add_sub_cancel] at e
  simp only [qf] at e
  simp only [smooth, Gm, qf, e, sub_dotProduct, smul_dotProduct, smul_eq_mul, ← mulVec_sub, dot_Qt,
    dotProduct_sub (P.alt)]
  rw [dotProduct_comm (P.V *ᵥ x) (x' - x), dot_symm hV (x' - x) x]
  ring

lemma smooth_le (h : Hyp P) (x x' : Fin N → ℝ) :
    smooth P x' ≤ smooth P x + Gm P x ⬝ᵥ (x' - x) - P.gamma / 2 * qf P.V (x' - x) := by
  have e := smooth_expand (symm_of_posDef (hyp_V h)) x x'
  have h1 := VE_le (hyp_gamma h) (hyp_sig h) (P.Q *ᵥ x) (P.Q *ᵥ x')
  linarith

lemma smooth_ge (h : Hyp P) (x x' : Fin N → ℝ) :
    smooth P x + Gm P x ⬝ᵥ (x' - x) - P.gamma / 2 * qf P.V (x' - x) -
      P.gamma * qf (P.Qᵀ * P.Sig * P.Q) (x' - x) ≤ smooth P x' := by
  have e := smooth_expand (symm_of_posDef (hyp_V h)) x x'
  have h1 := VE_rem (hyp_gamma h) (hyp_sig h) (P.Q *ᵥ x) (P.Q *ᵥ x')
  rw [← mulVec_sub, qf_Q] at h1
  rw [← mulVec_sub] at e
  have := (abs_le.mp h1).1
  linarith

theorem smooth_deriv (h : Hyp P) (x : Fin N → ℝ) : HasFDerivAt (smooth P) (dotCLM (Gm P x)) x := by
  obtain ⟨C1, hC1, hq1⟩ := qf_le_norm P.V
  obtain ⟨C2, hC2, hq2⟩ := qf_le_norm (P.Qᵀ * P.Sig * P.Q)
  have hγ := hyp_gamma h
  refine hasFDerivAt_of_sq (C := P.gamma / 2 * C1 + P.gamma * C2) fun y => ?_
  rw [dotCLM_apply]
  have a1 := smooth_le h x y
  have a2 := smooth_ge h x y
  have b1 := qf_nonneg (hyp_V h) (y - x)
  have b2 := hq1 (y - x)
  have b3 := hq2 (y - x)
  have b4 : 0 ≤ qf (P.Qᵀ * P.Sig * P.Q) (y - x) := by rw [← qf_Q]; exact qf_nonneg (hyp_sig h) _
  rw [abs_le]; constructor <;> nlinarith

/-- `Q'ζ(Q x) = Q_Z' ζ_Z` on `Z = Z(Q x)`, and `G = α^Z - γ V^Z x`. -/
theorem Gm_eq (h : Hyp P) (x : Fin N → ℝ) : Gm P x = Gcand P (Zset P (P.Q *ᵥ x)) x := by
  set Z := Zset P (P.Q *ᵥ x)
  obtain ⟨hz1, hz2⟩ := zeta_blocks (hyp_gamma h) (hyp_sig h) (P.Q *ᵥ x)
  have hQ : P.Qᵀ *ᵥ zeta P (P.Q *ᵥ x) = (QZ P Z)ᵀ *ᵥ zcand P Z (P.Q *ᵥ x) := by
    funext i
    simp only [mulVec, dotProduct, transpose_apply]
    rw [split_sum Z]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Out Z => P.Q j i * zeta P (P.Q *ᵥ x) j)
      fun j _ => by rw [hz2 j j.2, mul_zero], add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz1 j]; rfl
  have hqZ : (fun k : In Z => (P.Q *ᵥ x) k) = QZ P Z *ᵥ x := rfl
  rw [Gm, hQ, Gcand, alphaZ, VZ, zcand, hqZ]
  simp only [mulVec_sub, mulVec_smul, add_mulVec, mulVec_mulVec, smul_add, Matrix.mul_assoc]
  abel

/-- The coordinate cost of fund `i`. -/
def costi (P : Coord M N) (i : Fin N) (y : ℝ) : ℝ :=
  P.kp i * max (y - P.xm i) 0 + P.km i * max (P.xm i - y) 0

lemma cost_eq (x : Fin N → ℝ) : cost P x = ∑ i, costi P i (x i) := rfl

lemma costi_above {i : Fin N} {y : ℝ} (hy : P.xm i ≤ y) : costi P i y = P.kp i * (y - P.xm i) := by
  simp [costi, max_eq_left (sub_nonneg.mpr hy), max_eq_right (sub_nonpos.mpr hy)]

lemma costi_below {i : Fin N} {y : ℝ} (hy : y ≤ P.xm i) : costi P i y = P.km i * (P.xm i - y) := by
  simp [costi, max_eq_right (sub_nonpos.mpr hy), max_eq_left (sub_nonneg.mpr hy)]

/-- Subgradients of the coordinate cost. -/
lemma costi_sub (h : Hyp P) {i : Fin N} {y y' t : ℝ} (ht1 : -P.km i ≤ t) (ht2 : t ≤ P.kp i)
    (htp : P.xm i < y → t = P.kp i) (htm : y < P.xm i → t = -P.km i) :
    t * (y' - y) ≤ costi P i y' - costi P i y := by
  have hk := h.2.2.2.1 i
  have l1 : P.kp i * (y' - P.xm i) ≤ costi P i y' := by
    have := le_max_left (y' - P.xm i) 0
    have := le_max_right (P.xm i - y') 0
    simp only [costi]; nlinarith [hk.1, hk.2]
  have l2 : P.km i * (P.xm i - y') ≤ costi P i y' := by
    have := le_max_left (P.xm i - y') 0
    have := le_max_right (y' - P.xm i) 0
    simp only [costi]; nlinarith [hk.1, hk.2]
  rcases lt_trichotomy (P.xm i) y with hy | hy | hy
  · rw [htp hy, costi_above hy.le]; linarith
  · subst hy
    rw [costi_above le_rfl]
    rcases le_total (P.xm i) y' with h' | h'
    · nlinarith
    · nlinarith
  · rw [htm hy, costi_below hy.le]; linarith

lemma Box_eq : Box P = Set.Icc 0 P.xbar := by
  ext x; simp [Box, Set.mem_Icc, Pi.le_def, forall_and]

lemma continuous_smooth (h : Hyp P) : Continuous (smooth P) :=
  continuous_iff_continuousAt.mpr fun x => (smooth_deriv h x).continuousAt

lemma continuous_cost : Continuous (cost P) := by
  unfold cost; fun_prop

lemma continuous_Phi (h : Hyp P) : Continuous (Phi P) := (continuous_smooth h).sub continuous_cost

lemma xm_mem (h : Hyp P) : P.xm ∈ Box P := fun i => h.2.2.2.2 i

/-- The first-order bound: with subgradients `t` and the box signs of `G - t` at `y`,
`G(y)'(x - y) ≤ C_A(x) - C_A(y)` on the box. -/
lemma fo_bound (h : Hyp P) {y t : Fin N → ℝ}
    (ht : ∀ i, -P.km i ≤ t i ∧ t i ≤ P.kp i ∧ (P.xm i < y i → t i = P.kp i) ∧ (y i < P.xm i → t i = -P.km i))
    (hb : ∀ i, (y i < P.xbar i → Gm P y i - t i ≤ 0) ∧ (0 < y i → 0 ≤ Gm P y i - t i))
    {x : Fin N → ℝ} (hx : x ∈ Box P) : Gm P y ⬝ᵥ (x - y) ≤ cost P x - cost P y := by
  have hc : ∑ i, t i * (x i - y i) ≤ cost P x - cost P y := by
    rw [cost_eq, cost_eq, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => costi_sub h (ht i).1 (ht i).2.1 (ht i).2.2.1 (ht i).2.2.2
  have hs : Gm P y ⬝ᵥ (x - y) ≤ ∑ i, t i * (x i - y i) := by
    simp only [dotProduct, Pi.sub_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    rcases lt_trichotomy (x i) (y i) with hl | he | hg
    · have := (hb i).2 (lt_of_le_of_lt (hx i).1 hl); nlinarith
    · rw [he]; ring_nf; rfl
    · have := (hb i).1 (lt_of_lt_of_le hg (hx i).2); nlinarith
  linarith

/-- Sufficiency: subgradients `t` of the cost and the box signs of `G - t` at `y` make `y` maximize
`Φ` on the box. -/
theorem suff_opt (h : Hyp P) {y t : Fin N → ℝ}
    (ht : ∀ i, -P.km i ≤ t i ∧ t i ≤ P.kp i ∧ (P.xm i < y i → t i = P.kp i) ∧ (y i < P.xm i → t i = -P.km i))
    (hb : ∀ i, (y i < P.xbar i → Gm P y i - t i ≤ 0) ∧ (0 < y i → 0 ≤ Gm P y i - t i)) :
    IsMaxOn (Phi P) (Box P) y := by
  intro x hx
  simp only [Set.mem_ofPred_eq]
  have h1 := smooth_le h y x
  have h2 := qf_nonneg (hyp_V h) (x - y)
  have h3 := fo_bound h ht hb hx
  simp only [Phi]
  nlinarith [hyp_gamma h]

lemma update_eq (x : Fin N → ℝ) (i : Fin N) (s : ℝ) :
    x + s • Pi.single i 1 = Function.update x i (x i + s) := by
  funext k; by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

lemma cost_update (x : Fin N → ℝ) (i : Fin N) (s : ℝ) :
    cost P (x + s • Pi.single i 1) - cost P x = costi P i (x i + s) - costi P i (x i) := by
  rw [update_eq, cost_eq, cost_eq, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Function.update_of_ne hk]
  · simp

/-- The one-coordinate lower bound at a maximizer. -/
lemma coord_nec (h : Hyp P) {x : Fin N → ℝ} (hmax : IsMaxOn (Phi P) (Box P) x) (hx : x ∈ Box P)
    (i : Fin N) (s : ℝ) (hs : 0 ≤ x i + s ∧ x i + s ≤ P.xbar i) :
    s * Gm P x i - (P.gamma / 2 * P.V i i + P.gamma * (P.Qᵀ * P.Sig * P.Q) i i) * s ^ 2 -
      (costi P i (x i + s) - costi P i (x i)) ≤ 0 := by
  have hmem : x + s • Pi.single i 1 ∈ Box P := by
    rw [update_eq]; intro k
    by_cases hk : k = i
    · subst hk; simpa using hs
    · simpa [Function.update_of_ne hk] using hx k
  have h1 := hmax hmem
  simp only [Set.mem_ofPred_eq, Phi] at h1
  have h2 := smooth_ge h x (x + s • Pi.single i 1)
  rw [add_sub_cancel_left, single_dot, qf_single, qf_single] at h2
  have h3 := cost_update (P := P) x i s
  nlinarith

lemma slope_nonpos {a c δ : ℝ} (hδ : 0 < δ) (h : ∀ s, 0 < s → s < δ → s * a - c * s ^ 2 ≤ 0) : a ≤ 0 :=
  nonpos_of_small hδ fun s hs0 hs1 => by
    have := h s hs0 hs1
    have : s * a ≤ s * (c * s) := by nlinarith
    exact le_of_mul_le_mul_left this hs0

theorem atOptimum_core (h : Hyp P) {x : Fin N → ℝ} (hx : x ∈ Box P) (hmax : IsMaxOn (Phi P) (Box P) x)
    (i : Fin N) :
    (P.xm i < x i → x i < P.xbar i → Gm P x i = P.kp i) ∧
    (P.xm i < x i → x i = P.xbar i → P.kp i ≤ Gm P x i) ∧
    (x i < P.xm i → 0 < x i → Gm P x i = -P.km i) ∧
    (x i < P.xm i → x i = 0 → Gm P x i ≤ -P.km i) ∧
    (x i = P.xm i → (x i < P.xbar i → Gm P x i ≤ P.kp i) ∧ (0 < x i → -P.km i ≤ Gm P x i)) := by
  obtain ⟨c, hcd⟩ : ∃ c, c = P.gamma / 2 * P.V i i + P.gamma * (P.Qᵀ * P.Sig * P.Q) i i := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, G = Gm P x i := ⟨_, rfl⟩
  have hxm := (h.2.2.2.2 i).1
  have nec := coord_nec h hmax hx i
  rw [← hcd, ← hGd] at nec
  rw [← hGd]
  -- moving up by `s`, above the incumbent
  have up_above : P.xm i ≤ x i → x i < P.xbar i → G - P.kp i ≤ 0 := fun h1 h2 =>
    slope_nonpos (c := c) (sub_pos.mpr h2) fun s hs0 hs1 => by
      have := nec s ⟨by linarith [(hx i).1], by linarith⟩
      rw [costi_above (by linarith), costi_above h1] at this
      nlinarith
  have down_above : P.xm i < x i → P.kp i - G ≤ 0 := fun h1 =>
    slope_nonpos (c := c) (sub_pos.mpr h1) fun s hs0 hs1 => by
      have := nec (-s) ⟨by linarith, by linarith [(hx i).2]⟩
      rw [costi_above (by linarith), costi_above h1.le] at this
      nlinarith
  have up_below : x i < P.xm i → G + P.km i ≤ 0 := fun h1 =>
    slope_nonpos (c := c) (sub_pos.mpr h1) fun s hs0 hs1 => by
      have := nec s ⟨by linarith [(hx i).1], by linarith [(h.2.2.2.2 i).2]⟩
      rw [costi_below (by linarith), costi_below h1.le] at this
      nlinarith
  have down_below : x i ≤ P.xm i → 0 < x i → -(G + P.km i) ≤ 0 := fun h1 h2 =>
    slope_nonpos (c := c) h2 fun s hs0 hs1 => by
      have := nec (-s) ⟨by linarith, by linarith [(hx i).2]⟩
      rw [costi_below (by linarith), costi_below h1] at this
      nlinarith
  refine ⟨fun h1 h2 => ?_, fun h1 _ => ?_, fun h1 h2 => ?_, fun h1 _ => ?_, fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩⟩
  · linarith [up_above h1.le h2, down_above h1]
  · linarith [down_above h1]
  · linarith [up_below h1, down_below h1.le h2]
  · linarith [up_below h1]
  · linarith [up_above h1.ge h2]
  · linarith [down_below h1.le h2]

theorem atOptimum : AtOptimum := fun _ _ _ h _ hx hmax i => atOptimum_core h hx hmax i

/-- The review's objective is at most `Φ`, with equality at `w(Q a)`. -/
lemma J_le (h : Hyp P) {a : Fin N → ℝ} {w : Fin M → ℝ} (hw : w ∈ Wset (P.Q *ᵥ a)) :
    J P (a, w) ≤ Phi P a := by
  have := (wopt_spec (hyp_gamma h) (hyp_sig h) (P.Q *ᵥ a)).2 hw
  simp only [Set.mem_ofPred_eq] at this
  simp only [J, Phi, smooth, VE_eq (hyp_gamma h) (hyp_sig h)]
  linarith

lemma J_eq (h : Hyp P) (a : Fin N → ℝ) : J P (a, wopt P (P.Q *ᵥ a)) = Phi P a := by
  simp only [J, Phi, smooth, VE_eq (hyp_gamma h) (hyp_sig h)]; ring

theorem optimize_out (h : Hyp P) (p : (Fin N → ℝ) × (Fin M → ℝ)) (hp : p ∈ Jset P) :
    IsMaxOn (J P) (Jset P) p ↔ IsMaxOn (Phi P) (Box P) p.1 ∧ p.2 = wopt P (P.Q *ᵥ p.1) := by
  obtain ⟨a, w⟩ := p
  obtain ⟨ha, hw⟩ := hp
  have hγ := hyp_gamma h; have hS := hyp_sig h
  constructor
  · intro hmax
    have hwo : w = wopt P (P.Q *ᵥ a) := by
      have h1 := hmax (show (a, wopt P (P.Q *ᵥ a)) ∈ Jset P from ⟨ha, (wopt_spec hγ hS _).1⟩)
      simp only [Set.mem_ofPred_eq, J] at h1
      refine max_unique hγ hS (wopt_spec hγ hS _).1 (wopt_spec hγ hS _).2 hw fun w' hw' => ?_
      have := (wopt_spec hγ hS (P.Q *ᵥ a)).2 hw'
      simp only [Set.mem_ofPred_eq] at this ⊢
      linarith
    refine ⟨fun a' ha' => ?_, hwo⟩
    have := hmax (show (a', wopt P (P.Q *ᵥ a')) ∈ Jset P from ⟨ha', (wopt_spec hγ hS _).1⟩)
    simp only [Set.mem_ofPred_eq] at this ⊢
    rw [J_eq h, hwo, J_eq h] at this
    exact this
  · rintro ⟨hmax, hwe⟩ ⟨a', w'⟩ ⟨ha', hw'⟩
    simp only at hmax hwe
    subst hwe
    simp only [Set.mem_ofPred_eq]
    rw [J_eq h]
    exact (J_le h hw').trans (hmax ha')

lemma cost_mid (x y : Fin N → ℝ) (h : Hyp P) :
    cost P ((1 / 2 : ℝ) • (x + y)) ≤ (cost P x + cost P y) / 2 := by
  rw [cost_eq, cost_eq, cost_eq, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hk := h.2.2.2.1 i
  simp only [costi, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have e1 : 1 / 2 * (x i + y i) - P.xm i = (x i - P.xm i) / 2 + (y i - P.xm i) / 2 := by ring
  have e2 : P.xm i - 1 / 2 * (x i + y i) = (P.xm i - x i) / 2 + (P.xm i - y i) / 2 := by ring
  rw [e1, e2]
  have m1 : max ((x i - P.xm i) / 2 + (y i - P.xm i) / 2) 0 ≤
      max (x i - P.xm i) 0 / 2 + max (y i - P.xm i) 0 / 2 :=
    max_le (by linarith [le_max_left (x i - P.xm i) 0, le_max_left (y i - P.xm i) 0])
      (by positivity)
  have m2 : max ((P.xm i - x i) / 2 + (P.xm i - y i) / 2) 0 ≤
      max (P.xm i - x i) 0 / 2 + max (P.xm i - y i) 0 / 2 :=
    max_le (by linarith [le_max_left (P.xm i - x i) 0, le_max_left (P.xm i - y i) 0])
      (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left m1 hk.1, mul_le_mul_of_nonneg_left m2 hk.2]

theorem phi_unique (h : Hyp P) {x y : Fin N → ℝ} (hx : x ∈ Box P) (hmx : IsMaxOn (Phi P) (Box P) x)
    (hy : y ∈ Box P) (hmy : IsMaxOn (Phi P) (Box P) y) : x = y := by
  set m := (1 / 2 : ℝ) • (x + y)
  have hm : m ∈ Box P := fun i => by
    simp only [m, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  have a1 := smooth_le h m x
  have a2 := smooth_le h m y
  have e1 : x - m = (1 / 2 : ℝ) • (x - y) := by
    simp only [m, smul_sub, smul_add]; module
  have e2 : y - m = (-(1 / 2) : ℝ) • (x - y) := by
    simp only [m, smul_sub, smul_add]; module
  rw [e1, qf_smul, dotProduct_smul, smul_eq_mul] at a1
  rw [e2, qf_smul, dotProduct_smul, smul_eq_mul] at a2
  have c1 := cost_mid x y h
  have h1 := hmx hm; have h2 := hmy hm
  simp only [Set.mem_ofPred_eq, Phi] at h1 h2
  have hq : qf P.V (x - y) ≤ 0 := by nlinarith [hyp_gamma h]
  exact sub_eq_zero.mp (eq_of_qf (hyp_V h) hq)

theorem phi_exists (h : Hyp P) : ∃ x ∈ Box P, IsMaxOn (Phi P) (Box P) x := by
  rw [Box_eq]
  exact isCompact_Icc.exists_isMaxOn ⟨P.xm, by rw [← Box_eq]; exact xm_mem h⟩
    (continuous_Phi h).continuousOn

theorem fundMarginal : FundMarginal := by
  intro M N P h
  refine ⟨smooth_deriv h, Gm_eq h, optimize_out h, ?_⟩
  obtain ⟨x, hx, hm⟩ := phi_exists h
  exact ⟨x, ⟨hx, hm⟩, fun y hy => phi_unique h hy.1 hy.2 hx hm⟩

lemma xm_opt (h : Hyp P)
    (hc : ∀ i, (P.xm i < P.xbar i → Gm P P.xm i ≤ P.kp i) ∧ (0 < P.xm i → -P.km i ≤ Gm P P.xm i)) :
    IsMaxOn (Phi P) (Box P) P.xm := by
  refine suff_opt h (t := fun i => max (-P.km i) (min (P.kp i) (Gm P P.xm i))) (fun i => ?_)
    fun i => ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hk := h.2.2.2.1 i
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _), fun h => absurd h (lt_irrefl _),
      fun h => absurd h (lt_irrefl _)⟩
  · have := (hc i).1 h1
    rw [min_eq_right this]; linarith [le_max_right (-P.km i) (Gm P P.xm i)]
  · have := (hc i).2 h1
    exact sub_nonneg.mpr (max_le this (min_le_right _ _))

theorem holdTest : HoldTest := by
  intro M N P h
  have hγ := hyp_gamma h; have hS := hyp_sig h
  rw [optimize_out h _ ⟨xm_mem h, (wopt_spec hγ hS _).1⟩]
  simp only [and_true]
  constructor
  · intro hmax i
    exact (atOptimum_core h (xm_mem h) hmax i).2.2.2.2 rfl
  · exact xm_opt h

/-- Monotonicity of the marginal: `(G(y) - G(x))'(y - x) ≤ -γ ‖y - x‖²_V`. -/
lemma Gm_mono (h : Hyp P) (x y : Fin N → ℝ) :
    (Gm P y - Gm P x) ⬝ᵥ (y - x) ≤ -(P.gamma * qf P.V (y - x)) := by
  have hl := (lip (hyp_gamma h) (hyp_sig h) (P.Q *ᵥ x) (P.Q *ᵥ y)).2.1
  rw [← mulVec_sub, dot_Qt] at hl
  have e : Gm P y - Gm P x = -(P.gamma • (P.V *ᵥ (y - x))) -
      P.Qᵀ *ᵥ (zeta P (P.Q *ᵥ y) - zeta P (P.Q *ᵥ x)) := by
    simp only [Gm, mulVec_sub, smul_sub]; abel
  rw [e, sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul, qf, dotProduct_comm (P.V *ᵥ _)]
  linarith

lemma one_eq (x : Fin 1 → ℝ) : x = fun _ => x 0 := funext fun i => by rw [Subsingleton.elim i 0]

lemma Gm_strict {P : Coord M 1} (h : Hyp P) {x y : Fin 1 → ℝ} (hxy : x 0 < y 0) : Gm P y 0 < Gm P x 0 := by
  have hm := Gm_mono h x y
  have hv : 0 < P.V 0 0 := (hyp_V h).diag_pos
  have e1 : (Gm P y - Gm P x) ⬝ᵥ (y - x) = (Gm P y 0 - Gm P x 0) * (y 0 - x 0) := by
    simp [dotProduct]
  have e2 : qf P.V (y - x) = P.V 0 0 * (y 0 - x 0) ^ 2 := by
    simp [qf, dotProduct, mulVec]; ring
  rw [e1, e2] at hm
  have hγ := hyp_gamma h
  by_contra hc
  push Not at hc
  have : 0 < P.gamma * (P.V 0 0 * (y 0 - x 0) ^ 2) := by
    have : 0 < (y 0 - x 0) ^ 2 := by nlinarith
    positivity
  nlinarith

theorem oneFund : OneFund := by
  intro M P h x hx hmax
  have hc := atOptimum_core h hx hmax 0
  have hxm := h.2.2.2.2 0
  have hk := h.2.2.2.1 0
  have hmx : P.xm = fun _ => P.xm 0 := one_eq _
  have hxx : x = fun _ => x 0 := one_eq _
  refine ⟨⟨fun hlt => ?_, fun ⟨hG, hlt⟩ => ?_⟩, ⟨fun hlt => ?_, fun ⟨hG, hlt⟩ => ?_⟩, ?_⟩
  · have hge : P.kp 0 ≤ Gm P x 0 := by
      rcases (hx 0).2.lt_or_eq with h2 | h2
      · exact (hc.1 hlt h2).ge
      · exact hc.2.1 hlt h2
    exact ⟨lt_of_le_of_lt hge (Gm_strict h hlt), lt_of_lt_of_le hlt (hx 0).2⟩
  · by_contra hn
    push Not at hn
    rcases hn.lt_or_eq with h2 | h2
    · have hle : Gm P x 0 ≤ -P.km 0 := by
        rcases (hx 0).1.lt_or_eq with h3 | h3
        · exact (hc.2.2.1 h2 h3).le
        · exact hc.2.2.2.1 h2 h3.symm
      have := Gm_strict h h2
      linarith
    · have e : x = P.xm := by rw [hxx, hmx, h2]
      have := (hc.2.2.2.2 h2).1 (by rw [h2]; exact hlt)
      rw [e] at this; linarith
  · have hle : Gm P x 0 ≤ -P.km 0 := by
      rcases (hx 0).1.lt_or_eq with h3 | h3
      · exact (hc.2.2.1 hlt h3).le
      · exact hc.2.2.2.1 hlt h3.symm
    exact ⟨lt_of_lt_of_le (Gm_strict h hlt) hle, lt_of_le_of_lt (hx 0).1 hlt⟩
  · by_contra hn
    push Not at hn
    rcases hn.lt_or_eq with h2 | h2
    · have hge : P.kp 0 ≤ Gm P x 0 := by
        rcases (hx 0).2.lt_or_eq with h3 | h3
        · exact (hc.1 h2 h3).ge
        · exact hc.2.1 h2 h3
      have := Gm_strict h h2
      linarith
    · have e : x = P.xm := by rw [hxx, hmx, h2]
      have := (hc.2.2.2.2 h2.symm).2 (by rw [← h2]; exact hlt)
      rw [e] at this; linarith
  · rw [Gm_eq h, Gcand]
    simp [mulVec, dotProduct]
    ring

end Fund

/-! ### The Schur complement: curvature, the premium shift and the fold-in -/

section Schur

variable {M N : ℕ} {P : Coord M N}

lemma sub_T (Z : Finset (Fin M)) (hs : P.Sigᵀ = P.Sig) : (SZc P Z)ᵀ = ScZ P Z := by
  simp only [SZc, ScZ, transpose_submatrix, hs]

lemma scc_T (Z : Finset (Fin M)) (hs : P.Sigᵀ = P.Sig) : (Scc P Z)ᵀ = Scc P Z := by
  simp only [Scc, transpose_submatrix, hs]

lemma szz_T (Z : Finset (Fin M)) (hs : P.Sigᵀ = P.Sig) : (SZZ P Z)ᵀ = SZZ P Z := by
  simp only [SZZ, transpose_submatrix, hs]

lemma schur_T (Z : Finset (Fin M)) (hs : P.Sigᵀ = P.Sig) : (schur P Z)ᵀ = schur P Z := by
  rw [schur, transpose_sub, transpose_mul, transpose_mul, transpose_nonsing_inv, scc_T Z hs, szz_T Z hs,
    ← sub_T Z hs, transpose_transpose, Matrix.mul_assoc]

/-- The Schur identity: for `v` with `v_Z = u`,
`v'Σv = u'Σ_{ZZ.c}u + (v_c + Σ_cc⁻¹Σ_cZ u)'Σ_cc(v_c + Σ_cc⁻¹Σ_cZ u)`. -/
lemma schur_id (hS : P.Sig.PosDef) (Z : Finset (Fin M)) (v : Fin M → ℝ) :
    qf P.Sig v = (fun k : In Z => v k) ⬝ᵥ (schur P Z *ᵥ fun k : In Z => v k) +
      qf (Scc P Z) ((fun k : Out Z => v k) + (Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ fun k : In Z => v k)) := by
  have hs := symm_of_posDef hS
  have hU := scc_unit hS Z
  set u : In Z → ℝ := fun k => v k
  set vc : Out Z → ℝ := fun k => v k
  set L := (Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ u)
  have hsym : ∀ (a : In Z → ℝ) (b : Out Z → ℝ), a ⬝ᵥ (SZc P Z *ᵥ b) = b ⬝ᵥ (ScZ P Z *ᵥ a) := by
    intro a b; rw [dotProduct_mulVec, ← mulVec_transpose, sub_T Z hs, dotProduct_comm]
  have hq : qf P.Sig v = u ⬝ᵥ (SZZ P Z *ᵥ u) + u ⬝ᵥ (SZc P Z *ᵥ vc) + vc ⬝ᵥ (ScZ P Z *ᵥ u) +
      vc ⬝ᵥ (Scc P Z *ᵥ vc) := by
    simp only [qf, dotProduct]
    rw [split_sum Z]
    simp only [fun j : In Z => rows_in (P := P) Z v j, fun j : Out Z => rows_out (P := P) Z v j,
      mul_add, Finset.sum_add_distrib]
    ring
  have hL : Scc P Z *ᵥ L = ScZ P Z *ᵥ u := by
    simp only [L]; rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have a1 : qf (Scc P Z) L = L ⬝ᵥ (ScZ P Z *ᵥ u) := by rw [qf, hL]
  have a2 : u ⬝ᵥ (SZc P Z *ᵥ L) = L ⬝ᵥ (ScZ P Z *ᵥ u) := hsym u L
  have a3 := hsym u vc
  have a4 : vc ⬝ᵥ (Scc P Z *ᵥ L) = vc ⬝ᵥ (ScZ P Z *ᵥ u) := by rw [hL]
  have a5 : u ⬝ᵥ (schur P Z *ᵥ u) = u ⬝ᵥ (SZZ P Z *ᵥ u) - L ⬝ᵥ (ScZ P Z *ᵥ u) := by
    rw [schur, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, ← a2]
  have a6 : qf (Scc P Z) vc = vc ⬝ᵥ (Scc P Z *ᵥ vc) := rfl
  rw [hq, qf_add (scc_T Z hs)]
  linarith

/-- The Schur lift: `v_Z = u`, `v_c = -Σ_cc⁻¹Σ_cZ u`. -/
def lift (P : Coord M N) (Z : Finset (Fin M)) (u : In Z → ℝ) : Fin M → ℝ := fun j =>
  if h : j ∈ Z then u ⟨j, h⟩ else (-((Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ u))) ⟨j, h⟩

lemma lift_in (Z : Finset (Fin M)) (u : In Z → ℝ) : (fun k : In Z => lift P Z u k) = u := by
  funext k; simp [lift, k.2]

lemma lift_out (Z : Finset (Fin M)) (u : In Z → ℝ) :
    (fun k : Out Z => lift P Z u k) = -((Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ u)) := by
  funext k; simp [lift, k.2]

lemma schur_qf (hS : P.Sig.PosDef) (Z : Finset (Fin M)) (u : In Z → ℝ) :
    u ⬝ᵥ (schur P Z *ᵥ u) = qf P.Sig (lift P Z u) := by
  rw [schur_id hS Z, lift_in, lift_out, neg_add_cancel]
  simp [qf]

lemma schur_nonneg (hS : P.Sig.PosDef) (Z : Finset (Fin M)) (u : In Z → ℝ) :
    0 ≤ u ⬝ᵥ (schur P Z *ᵥ u) := by
  rw [schur_qf hS]; exact qf_nonneg hS _

/-- `v'Σv ≥ v_Z'Σ_{ZZ.c}v_Z`. -/
lemma schur_le (hS : P.Sig.PosDef) (Z : Finset (Fin M)) (v : Fin M → ℝ) :
    (fun k : In Z => v k) ⬝ᵥ (schur P Z *ᵥ fun k : In Z => v k) ≤ qf P.Sig v := by
  rw [schur_id hS Z v]
  have := qf_nonneg (scc_posDef hS Z) ((fun k : Out Z => v k) + (Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ fun k : In Z => v k))
  linarith

lemma VZ_qf (Z : Finset (Fin M)) (x : Fin N → ℝ) :
    x ⬝ᵥ (VZ P Z *ᵥ x) = x ⬝ᵥ (P.V *ᵥ x) + (QZ P Z *ᵥ x) ⬝ᵥ (schur P Z *ᵥ (QZ P Z *ᵥ x)) := by
  rw [VZ, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x (QZ P Z)ᵀ,
    vecMul_transpose]

theorem curvature : Curvature := by
  intro M N P h Z Z' hZ x
  have hS := hyp_sig h
  rw [VZ_qf, VZ_qf]
  have e1 : QZ P Z' *ᵥ x = fun k : In Z' => lift P Z' (QZ P Z' *ᵥ x) k := (lift_in Z' _).symm
  have e2 : QZ P Z *ᵥ x = fun k : In Z => lift P Z' (QZ P Z' *ᵥ x) k := by
    funext k
    have := congrFun e1 ⟨k, hZ k.2⟩
    exact this
  have := schur_le hS Z (lift P Z' (QZ P Z' *ᵥ x))
  rw [← e2, ← schur_qf hS] at this
  linarith

lemma VZ_sub (Z : Finset (Fin M)) : VZ P Z - P.V = (QZ P Z)ᵀ * schur P Z * QZ P Z := by
  rw [VZ]; abel

theorem VZ_psd (h : Hyp P) (Z : Finset (Fin M)) : (VZ P Z - P.V).PosSemidef := by
  have hS := hyp_sig h
  rw [VZ_sub, posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul,
      transpose_transpose, schur_T Z (symm_of_posDef hS), Matrix.mul_assoc]
  · simp only [star_trivial]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
    exact schur_nonneg hS Z _

theorem VZ_rank (Z : Finset (Fin M)) : (VZ P Z - P.V).rank ≤ Z.card := by
  rw [VZ_sub]
  calc _ ≤ (QZ P Z).rank := rank_mul_le_right _ _
    _ ≤ Fintype.card (In Z) := rank_le_card_height _
    _ = Z.card := Fintype.card_coe Z

theorem VZ_posDef (h : Hyp P) (Z : Finset (Fin M)) : (VZ P Z).PosDef := by
  have hS := hyp_sig h
  have hV := hyp_V h
  rw [posDef_iff_dotProduct_mulVec]
  have hsub := VZ_psd h Z
  refine ⟨?_, fun x hx => ?_⟩
  · have e : VZ P Z = P.V + (VZ P Z - P.V) := by abel
    rw [e]; exact hV.isHermitian.add hsub.isHermitian
  · simp only [star_trivial]
    rw [VZ_qf]
    have h1 := hV.dotProduct_mulVec_pos hx
    simp only [star_trivial] at h1
    have := schur_nonneg hS Z (QZ P Z *ᵥ x)
    linarith

/-- At the optimum, subgradients `t` of the cost with the box signs of `G - t` exist. -/
lemma opt_mult (h : Hyp P) {x : Fin N → ℝ} (hx : x ∈ Box P) (hmax : IsMaxOn (Phi P) (Box P) x) :
    ∃ t : Fin N → ℝ, (∀ i, -P.km i ≤ t i ∧ t i ≤ P.kp i ∧ (P.xm i < x i → t i = P.kp i) ∧
      (x i < P.xm i → t i = -P.km i)) ∧
      ∀ i, (x i < P.xbar i → Gm P x i - t i ≤ 0) ∧ (0 < x i → 0 ≤ Gm P x i - t i) := by
  refine ⟨fun i => if P.xm i < x i then P.kp i else if x i < P.xm i then -P.km i
    else max (-P.km i) (min (P.kp i) (Gm P x i)), fun i => ?_, fun i => ?_⟩
  · have hk := h.2.2.2.1 i
    dsimp only
    split_ifs with h1 h2
    · exact ⟨by linarith, le_rfl, fun _ => rfl, fun h2 => absurd h2 (not_lt.mpr h1.le)⟩
    · exact ⟨le_rfl, by linarith, fun h => absurd h h1, fun _ => rfl⟩
    · exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _), fun h => absurd h h1,
        fun h => absurd h h2⟩
  · have hc := atOptimum_core h hx hmax i
    dsimp only
    split_ifs with h1 h2
    · refine ⟨fun h2 => by rw [hc.1 h1 h2]; simp, fun _ => ?_⟩
      rcases (hx i).2.lt_or_eq with h2 | h2
      · rw [hc.1 h1 h2]; simp
      · linarith [hc.2.1 h1 h2]
    · refine ⟨fun _ => ?_, fun h3 => by rw [hc.2.2.1 h2 h3]; simp⟩
      rcases (hx i).1.lt_or_eq with h3 | h3
      · rw [hc.2.2.1 h2 h3]; simp
      · linarith [hc.2.2.2.1 h2 h3.symm]
    · have he : x i = P.xm i := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      refine ⟨fun h3 => ?_, fun h3 => ?_⟩
      · have := (hc.2.2.2.2 he).1 h3
        rw [min_eq_right this]; linarith [le_max_right (-P.km i) (Gm P x i)]
      · have := (hc.2.2.2.2 he).2 h3
        exact sub_nonneg.mpr (max_le this (min_le_right _ _))

theorem foldIn : FoldIn := by
  intro M N P h
  have hγ := hyp_gamma h; have hS := hyp_sig h
  refine ⟨fun x hx hmax => ?_, fun Z => ⟨VZ_psd h Z, VZ_rank Z⟩⟩
  intro ζ Pf
  set ws := wopt P (P.Q *ᵥ x)
  have hz : P.gamma • (P.Sig *ᵥ ws) = P.mu + ζ := by
    simp only [ζ, zeta]; abel
  have hU : IsUnit (P.gamma • P.Sig).det := by
    rw [det_smul]
    exact (mul_ne_zero (pow_ne_zero _ hγ.ne') ((isUnit_iff_isUnit_det _).mp hS.isUnit).ne_zero).isUnit
  refine ⟨?_, (zeta_blocks hγ hS _).2, ?_⟩
  · rw [← hz, ← smul_mulVec, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  · rintro ⟨a, w⟩ ⟨ha, -⟩
    simp only [Set.mem_ofPred_eq]
    have hPf : Pf.Sigᵀ = Pf.Sig := symm_of_posDef hS
    have hzf : zof Pf ws = 0 := by
      simp only [zof, Pf]; rw [hz]; abel
    have g1 := GE_add hPf ws (w - ws)
    rw [add_sub_cancel, hzf, zero_dotProduct, sub_zero] at g1
    have g2 : 0 ≤ qf Pf.Sig (w - ws) := qf_nonneg hS _
    have g2' : 0 ≤ Pf.gamma / 2 * qf Pf.Sig (w - ws) := mul_nonneg (by simp only [Pf]; linarith) g2
    obtain ⟨t, ht, hb⟩ := opt_mult h hx hmax
    have f1 := fo_bound h ht hb ha
    have hV := symm_of_posDef (hyp_V h)
    have e := qf_add hV x (a - x)
    rw [add_sub_cancel] at e
    have g3 := qf_nonneg (hyp_V h) (a - x)
    simp only [qf] at e g3
    have eG : Gm P x ⬝ᵥ (a - x) = (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ (a - x) - P.gamma * (x ⬝ᵥ (P.V *ᵥ (a - x))) := by
      simp only [Gm, ζ, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [dotProduct_comm (P.V *ᵥ x), dot_symm hV (a - x) x]; ring
    have ea : (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ (a - x) = (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ a - (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ x :=
      dotProduct_sub _ _ _
    have j1 : J Pf (a, w) = GE Pf w + (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ a - P.gamma / 2 * (a ⬝ᵥ (P.V *ᵥ a)) -
        cost P a := rfl
    have j2 : J Pf (x, ws) = GE Pf ws + (P.alt - P.Qᵀ *ᵥ ζ) ⬝ᵥ x - P.gamma / 2 * (x ⬝ᵥ (P.V *ᵥ x)) -
        cost P x := rfl
    rw [j1, j2]
    nlinarith [hγ]

theorem premiumShift : PremiumShift := by
  intro M N P h B e Z P' dG
  have hS := hyp_sig h
  have hγ := hyp_gamma h
  have hB : ∀ e' : Fin M → ℝ, BZc P Z B *ᵥ e' = (fun j : In Z => (B *ᵥ e') j) -
      SZc P Z *ᵥ ((Scc P Z)⁻¹ *ᵥ fun j : Out Z => (B *ᵥ e') j) := fun e' => by
    rw [BZc, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]; rfl
  have hmu : muZc P' Z = muZc P Z + BZc P Z B *ᵥ e := by
    rw [hB]
    show (fun j : In Z => P.mu j + (B *ᵥ e) j) - SZc P Z *ᵥ ((Scc P Z)⁻¹ *ᵥ
      fun j : Out Z => P.mu j + (B *ᵥ e) j) = _
    rw [show (fun j : Out Z => P.mu j + (B *ᵥ e) j) =
      (fun j : Out Z => P.mu j) + fun j : Out Z => (B *ᵥ e) j from rfl, mulVec_add, mulVec_add]
    funext j
    simp only [muZc, Pi.sub_apply, Pi.add_apply]
    ring
  have hshift : ∀ x, Gcand P' Z x = Gcand P Z x + dG := fun x => by
    show P.alt + (QZ P Z)ᵀ *ᵥ muZc P' Z - P.gamma • (VZ P Z *ᵥ x) = _
    rw [hmu, mulVec_add, Gcand, alphaZ]
    abel
  refine ⟨fun x => by rw [hshift]; abel, fun hB' i => ⟨fun hall j hj => ?_, fun h0 e' => ?_⟩,
    fun T x x' k hoff hk hk' => ?_⟩
  · set e' := B⁻¹ *ᵥ Pi.single j 1
    have hBe : B *ᵥ e' = Pi.single j 1 := by
      simp only [e']; rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
    have hz := hall e'
    have h3 : (fun k : Out Z => (Pi.single j (1 : ℝ) : Fin M → ℝ) k) = 0 := by
      funext k; simp [show (k : Fin M) ≠ j from fun h => k.2 (h ▸ hj)]
    have hBZ : BZc P Z B *ᵥ e' = Pi.single ⟨j, hj⟩ 1 := by
      rw [hB, hBe, h3, mulVec_zero, mulVec_zero, sub_zero]
      funext k
      by_cases hk : k = ⟨j, hj⟩
      · subst hk; simp
      · have : (k : Fin M) ≠ j := fun h => hk (Subtype.ext h)
        simp [this, hk]
    rw [hBZ] at hz
    simpa [mulVec, dotProduct, QZ, Pi.single_apply] using hz
  · simp only [mulVec, dotProduct, transpose_apply, QZ, submatrix_apply, id]
    exact Finset.sum_eq_zero fun k _ => by rw [h0 k k.2, zero_mul]
  · set VT := (VZ P Z).submatrix (Subtype.val : {i // i ∈ T} → Fin N) Subtype.val
    have hVT : VT.PosDef := (VZ_posDef h Z).submatrix Subtype.val_injective
    have hU : IsUnit (P.gamma • VT).det := by
      rw [det_smul]
      exact (mul_ne_zero (pow_ne_zero _ hγ.ne') ((isUnit_iff_isUnit_det _).mp hVT.isUnit).ne_zero).isUnit
    have hmv : (P.gamma • VT) *ᵥ (fun i : {i // i ∈ T} => x' i - x i) = fun i : {i // i ∈ T} => dG i := by
      funext i
      have e1 := hk i i.2
      have e2 := hk' i i.2
      rw [hshift] at e2
      simp only [Gcand, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
      have hsum : (VZ P Z *ᵥ x') i - (VZ P Z *ᵥ x) i = (VT *ᵥ fun i : {i // i ∈ T} => x' i - x i) i := by
        rw [← Pi.sub_apply, ← mulVec_sub]
        simp only [mulVec, dotProduct]
        rw [split_sum T]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun k : Out T => VZ P Z i k * (x' - x) k)
          fun k _ => by simp [hoff k k.2], add_zero]
        rfl
      rw [smul_mulVec, Pi.smul_apply, smul_eq_mul, ← hsum]
      linarith
    rw [← hmv, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]

theorem oneEtf : OneEtf := by
  intro N P h x
  have hγ := hyp_gamma h; have hS := hyp_sig h
  have hσ : 0 < P.Sig 0 0 := hS.diag_pos
  set q := (P.Q *ᵥ x) 0
  have hmem : (0 : Fin 1) ∈ Zset P (P.Q *ᵥ x) ↔ wopt P (P.Q *ᵥ x) 0 = q := by
    simp [Zset, q]
  have hz0 : zeta P (P.Q *ᵥ x) 0 = P.gamma * (P.Sig 0 0 * wopt P (P.Q *ᵥ x) 0) - P.mu 0 := by
    simp [zeta, mulVec, dotProduct]
  have iff1 : (0 : Fin 1) ∈ Zset P (P.Q *ᵥ x) ↔ P.mu 0 ≤ P.gamma * P.Sig 0 0 * q := by
    rw [hmem]
    constructor
    · intro hw
      have := (zeta_kkt hγ hS (P.Q *ᵥ x) 0).1
      rw [hz0, hw] at this; linarith
    · intro hle
      have := (kkt_iff hγ hS (P.Q *ᵥ x) (P.Q *ᵥ x) (fun _ => P.gamma * P.Sig 0 0 * q - P.mu 0)).mp
        ⟨fun j => le_rfl, fun j => ⟨by linarith, by ring⟩, by
          funext j
          rw [Subsingleton.elim j 0]
          have : (P.Sig *ᵥ (P.Q *ᵥ x)) 0 = P.Sig 0 0 * q := by
            simp only [mulVec, dotProduct, Fin.sum_univ_one]; rfl
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, this]
          ring⟩
      rw [← this.1]
  have hGm : ∀ i, Gm P x i = P.alt i - P.gamma * (P.V *ᵥ x) i - P.Q 0 i * zeta P (P.Q *ᵥ x) 0 := by
    intro i; simp [Gm, mulVec, dotProduct]
  refine ⟨iff1, fun h0 i => ?_, fun h0 i => ?_⟩
  · rw [hGm, hz0, (hmem.mp h0)]; ring
  · rw [hGm, (zeta_blocks hγ hS _).2 0 h0]; ring

end Schur

/-! ### Part 4: along one fund's trade -/

section Pieces

/-- A function continuous on `[a, b]` and antitone on each of finitely many sets covering it is
antitone on `[a, b]`. -/
lemma antitoneOn_of_pieces {ι : Type} [Finite ι] {S : ι → Set ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hcov : ∀ y ∈ Set.Icc a b, ∃ i, y ∈ S i)
    (hf : ContinuousOn f (Set.Icc a b)) (hanti : ∀ i, AntitoneOn f (S i ∩ Set.Icc a b)) :
    AntitoneOn f (Set.Icc a b) := by
  intro x hx y hy hxy
  set T := {z | f z ≤ f x}
  have hcl : IsClosed (T ∩ Set.Icc x b) := by
    have := (hf.mono (Set.Icc_subset_Icc_left hx.1)).preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_Iic (a := f x))
    rwa [Set.inter_comm] at this
  have key : Set.Icc x b ⊆ T := by
    refine IsClosed.Icc_subset_of_forall_exists_gt hcl (show f x ≤ f x from le_rfl) ?_
    rintro y' ⟨hy'T, hy'1, hy'2⟩ z hz
    have hz' : y' < min z b := lt_min hz hy'2
    set d := min z b - y'
    have hd : 0 < d := sub_pos.mpr hz'
    set p : ℕ → ℝ := fun n => y' + d / (n + 2)
    have hp1 : ∀ n, y' < p n := fun n => by
      have : (0 : ℝ) < d / ((n : ℝ) + 2) := by positivity
      simp only [p]; linarith
    have hp2 : ∀ n, p n ≤ min z b := fun n => by
      simp only [p, d]
      have : (1 : ℝ) ≤ n + 2 := by have := n.cast_nonneg (α := ℝ); linarith
      have : (min z b - y') / (n + 2) ≤ min z b - y' := div_le_self hd.le this
      linarith
    have hpI : ∀ n, p n ∈ Set.Icc a b := fun n =>
      ⟨by linarith [hp1 n, hx.1, hy'1], (hp2 n).trans (min_le_right _ _)⟩
    choose g hg using fun n => hcov (p n) (hpI n)
    obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber g
    have hinf : Set.Infinite {n | g n = i} := Set.infinite_coe_iff.mp hi
    obtain ⟨n0, hn0⟩ := hinf.nonempty
    have hpy : Tendsto p atTop (𝓝 y') := by
      have : Tendsto (fun n : ℕ => d / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        exact h1.const_div_atTop d
      simpa using this.const_add y'
    have hy'I : y' ∈ Set.Icc a b := ⟨le_trans hx.1 hy'1, hy'2.le⟩
    have hfp : Tendsto (fun n => f (p n)) atTop (𝓝 (f y')) :=
      ((hf y' hy'I).tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hpy, Eventually.of_forall hpI⟩)
    have hfreq : ∃ᶠ n in atTop, f (p n0) ≤ f (p n) := by
      have : ∃ᶠ n in atTop, g n = i := Nat.frequently_atTop_iff_infinite.mpr hinf
      refine (this.and_eventually (eventually_ge_atTop n0)).mono fun n ⟨hn, hnn⟩ => ?_
      have hle : p n ≤ p n0 := by
        simp only [p]
        have : (n0 : ℝ) ≤ n := by exact_mod_cast hnn
        have : (0 : ℝ) < n0 + 2 := by positivity
        gcongr
      have h1 : p n ∈ S i ∩ Set.Icc a b := ⟨hn ▸ hg n, hpI n⟩
      have h2 : p n0 ∈ S i ∩ Set.Icc a b := ⟨hn0 ▸ hg n0, hpI n0⟩
      exact hanti i h1 h2 hle
    have hlim : f (p n0) ≤ f y' := isClosed_Ici.mem_of_frequently_of_tendsto hfreq hfp
    exact ⟨p n0, show f (p n0) ≤ f x from hlim.trans hy'T, hp1 n0, (hp2 n0).trans (min_le_left _ _)⟩
  exact key ⟨hxy, hy.2⟩

lemma monotoneOn_of_pieces {ι : Type} [Finite ι] {S : ι → Set ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hcov : ∀ y ∈ Set.Icc a b, ∃ i, y ∈ S i)
    (hf : ContinuousOn f (Set.Icc a b)) (hmono : ∀ i, MonotoneOn f (S i ∩ Set.Icc a b)) :
    MonotoneOn f (Set.Icc a b) := by
  have := antitoneOn_of_pieces (f := fun x => -f x) hcov hf.neg fun i => (hmono i).neg
  exact fun x hx y hy hxy => neg_le_neg_iff.mp (this hx hy hxy)

lemma affine_ordConnected {a b : ℝ} {x y z : ℝ} (hxz : x ≤ z) (hzy : z ≤ y) :
    min (a + b * x) (a + b * y) ≤ a + b * z := by
  rcases le_total 0 b with hb | hb
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

end Pieces

section Path

variable {M : ℕ} {P : Coord M 1}

lemma Q_const (x : ℝ) : P.Q *ᵥ (fun _ => x) = x • fun j => P.Q j 0 := by
  funext j; simp [mulVec, dotProduct, mul_comm]

lemma zset_eq_iff (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (q : Fin M → ℝ) (Z : Finset (Fin M)) :
    Zset P q = Z ↔ (∀ j, 0 ≤ zcand P Z q j) ∧ ∀ j, j ∉ Z → q j < wcand P Z q j := by
  constructor
  · rintro rfl
    refine ⟨(zset_cond hγ hS q).1, fun j hj => ?_⟩
    have hne : wopt P q j ≠ q j := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [← wopt_eq_cand hγ hS]
    exact lt_of_le_of_ne ((wopt_spec hγ hS q).1 j) (Ne.symm hne)
  · rintro ⟨h1, h2⟩
    have hw := ((cand_iff hγ hS q Z).mp ⟨h1, fun j hj => (h2 j hj).le⟩).1
    ext j
    simp only [Zset, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ Z
    · simp only [hj, iff_true]; rw [← hw]; exact wcand_in (Z := Z) ⟨j, hj⟩
    · simp only [hj, iff_false]; rw [← hw]; exact (h2 j hj).ne'

lemma mOne_def (x : ℝ) : mOne P x = P.alt 0 - P.gamma * (P.V 0 0 * x) -
    (fun j => P.Q j 0) ⬝ᵥ zeta P (x • fun j => P.Q j 0) := by
  simp only [mOne, Gm, ← Q_const]
  simp [mulVec, dotProduct]

lemma mOne_piece (h : Hyp P) {x : ℝ} {Z : Finset (Fin M)} (hZ : Zpath P x = Z) :
    mOne P x = alphaZ P Z 0 - P.gamma * sZ P Z * x := by
  simp only [mOne]
  rw [Gm_eq h, show Zset P (P.Q *ᵥ fun _ => x) = Z from hZ, Gcand]
  simp [mulVec, dotProduct, sZ]; ring

lemma sZ_ge (h : Hyp P) (Z : Finset (Fin M)) : P.V 0 0 ≤ sZ P Z := by
  have := VZ_qf (P := P) Z (fun _ => 1)
  have h2 := schur_nonneg (hyp_sig h) Z (QZ P Z *ᵥ fun _ => 1)
  simp only [dotProduct, mulVec, Fin.sum_univ_one, one_mul, mul_one] at this h2
  simp only [sZ]
  linarith

lemma sZ_pos (h : Hyp P) (Z : Finset (Fin M)) : 0 < sZ P Z :=
  lt_of_lt_of_le (hyp_V h).diag_pos (sZ_ge h Z)

lemma mOne_strict (h : Hyp P) : StrictAnti (mOne P) := fun x y hxy =>
  Gm_strict h (x := fun _ => x) (y := fun _ => y) hxy

/-- The slope bound `m(y) - m(x) ≤ -γ v (y - x)` for `x ≤ y`. -/
lemma mOne_slope (h : Hyp P) {x y : ℝ} (hxy : x ≤ y) :
    mOne P y - mOne P x ≤ -(P.gamma * P.V 0 0 * (y - x)) := by
  have hm := Gm_mono h (fun _ => x) (fun _ => y)
  have e1 : (Gm P (fun _ => y) - Gm P fun _ => x) ⬝ᵥ ((fun _ => y) - fun _ => x) =
      (mOne P y - mOne P x) * (y - x) := by simp [dotProduct, mOne]
  have e2 : qf P.V ((fun _ => y) - fun _ => x) = P.V 0 0 * (y - x) ^ 2 := by
    simp [qf, dotProduct, mulVec]; ring
  rw [e1, e2] at hm
  rcases hxy.lt_or_eq with hlt | heq
  · have hpos : 0 < y - x := sub_pos.mpr hlt
    have : (mOne P y - mOne P x) * (y - x) ≤ -(P.gamma * P.V 0 0 * (y - x)) * (y - x) := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · subst heq; simp

lemma mOne_lip (h : Hyp P) : ∃ L, ∀ x y, |mOne P x - mOne P y| ≤ L * |x - y| := by
  have hγ := hyp_gamma h; have hS := hyp_sig h
  set r : Fin M → ℝ := fun j => P.Q j 0
  refine ⟨P.gamma * P.V 0 0 + P.gamma * qf P.Sig r, fun x y => ?_⟩
  have hl := lip hγ hS (x • r) (y • r)
  have e : y • r - x • r = (y - x) • r := (sub_smul _ _ _).symm
  rw [e, dotProduct_smul, smul_eq_mul, qf_smul] at hl
  obtain ⟨-, l1, l2⟩ := hl
  set D := (zeta P (y • r) - zeta P (x • r)) ⬝ᵥ r
  have hD : |D| * |x - y| ≤ P.gamma * qf P.Sig r * |x - y| ^ 2 := by
    rw [← abs_mul, show D * (x - y) = -((y - x) * D) by ring, abs_neg, abs_of_nonneg l1, sq_abs,
      show (x - y) ^ 2 = (y - x) ^ 2 by ring]
    linarith
  have hDl : |D| ≤ P.gamma * qf P.Sig r * |x - y| := by
    rcases (abs_nonneg (x - y)).lt_or_eq with hp | hp
    · have : |D| * |x - y| ≤ (P.gamma * qf P.Sig r * |x - y|) * |x - y| := by nlinarith
      exact le_of_mul_le_mul_right this hp
    · have hxy : x = y := by rw [eq_comm, abs_eq_zero, sub_eq_zero] at hp; exact hp
      subst hxy; simp [D]
  have em : mOne P x - mOne P y = P.gamma * P.V 0 0 * (y - x) + D := by
    rw [mOne_def, mOne_def]
    simp only [D, sub_dotProduct]
    rw [dotProduct_comm r, dotProduct_comm r]; ring
  rw [em]
  have hV := (hyp_V h).diag_pos (i := 0)
  calc |P.gamma * P.V 0 0 * (y - x) + D| ≤ |P.gamma * P.V 0 0 * (y - x)| + |D| := abs_add_le _ _
    _ ≤ P.gamma * P.V 0 0 * |x - y| + P.gamma * qf P.Sig r * |x - y| := by
        rw [abs_mul, abs_of_pos (by positivity), abs_sub_comm]; linarith
    _ = _ := by ring

lemma mOne_cont (h : Hyp P) : Continuous (mOne P) := by
  obtain ⟨L, hL⟩ := mOne_lip h
  refine Metric.continuous_iff.mpr fun x ε hε => ⟨ε / (|L| + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |mOne P y - mOne P x| ≤ L * |y - x| := hL y x
    _ ≤ (|L| + 1) * |y - x| := by nlinarith [le_abs_self L, abs_nonneg (y - x)]
    _ < (|L| + 1) * (ε / (|L| + 1)) := by gcongr
    _ = ε := by field_simp

theorem roots : Roots := by
  intro M P h k
  have hγ := hyp_gamma h
  have hv := (hyp_V h).diag_pos (i := 0)
  set c := P.gamma * P.V 0 0
  have hc : 0 < c := by positivity
  set R := |k - mOne P 0| / c
  have hR : 0 ≤ R := by positivity
  have ha : k ≤ mOne P (-R) := by
    have := mOne_slope h (show -R ≤ 0 by linarith)
    have e : c * R = |k - mOne P 0| := by simp only [R]; field_simp
    have : k - mOne P 0 ≤ |k - mOne P 0| := le_abs_self _
    nlinarith
  have hb : mOne P R ≤ k := by
    have := mOne_slope h hR
    have e : c * R = |k - mOne P 0| := by simp only [R]; field_simp
    have : mOne P 0 - k ≤ |k - mOne P 0| := by rw [abs_sub_comm]; exact le_abs_self _
    nlinarith
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc' (show -R ≤ R by linarith) (mOne_cont h).continuousOn
    ⟨hb, ha⟩
  exact ⟨u, hu, fun u' hu' => (mOne_strict h).injective (hu'.trans hu.symm)⟩

lemma box_one {x : ℝ} : (fun _ => x : Fin 1 → ℝ) ∈ Box P ↔ x ∈ Set.Icc 0 (P.xbar 0) := by
  constructor
  · intro hx; exact ⟨(hx 0).1, (hx 0).2⟩
  · intro hx i; rw [Subsingleton.elim i 0]; exact hx

lemma phi_max_one {xs : ℝ} (hmax : IsMaxOn (phiOne P) (Set.Icc 0 (P.xbar 0)) xs) :
    IsMaxOn (Phi P) (Box P) fun _ => xs := by
  intro y hy
  have := hmax (show y 0 ∈ Set.Icc 0 (P.xbar 0) from ⟨(hy 0).1, (hy 0).2⟩)
  simp only [Set.mem_ofPred_eq, phiOne] at this ⊢
  rwa [one_eq y]

lemma min_min_iff {a u v : ℝ} : min a u = min a v ↔ u = v ∨ (a ≤ u ∧ a ≤ v) := by
  constructor
  · intro h
    rcases le_total a u with h1 | h1 <;> rcases le_total a v with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · rw [min_eq_left h1, min_eq_right h2] at h; exact Or.inr ⟨h1, by linarith⟩
    · rw [min_eq_right h1, min_eq_left h2] at h; exact Or.inr ⟨by linarith, h2⟩
    · rw [min_eq_right h1, min_eq_right h2] at h; exact Or.inl h
  · rintro (rfl | ⟨h1, h2⟩)
    · rfl
    · rw [min_eq_left h1, min_eq_left h2]

lemma max_max_iff {u v : ℝ} : max 0 u = max 0 v ↔ u = v ∨ (u ≤ 0 ∧ v ≤ 0) := by
  constructor
  · intro h
    rcases le_total u 0 with h1 | h1 <;> rcases le_total v 0 with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · rw [max_eq_left h1, max_eq_right h2] at h; exact Or.inr ⟨h1, by linarith⟩
    · rw [max_eq_right h1, max_eq_left h2] at h; exact Or.inr ⟨by linarith, h2⟩
    · rw [max_eq_right h1, max_eq_right h2] at h; exact Or.inl h
  · rintro (rfl | ⟨h1, h2⟩)
    · rfl
    · rw [max_eq_left h1, max_eq_left h2]

/-- The pieces are intervals. -/
lemma piece_ordConnected (h : Hyp P) (Z : Finset (Fin M)) : Set.OrdConnected {x | Zpath P x = Z} := by
  have hγ := hyp_gamma h; have hS := hyp_sig h
  set r : Fin M → ℝ := fun j => P.Q j 0
  have hset : {x | Zpath P x = Z} = {x | (∀ j, 0 ≤ zcand P Z (x • r) j) ∧ ∀ j, j ∉ Z → x * r j < wcand P Z (x • r) j} := by
    ext x; simp only [Set.mem_ofPred_eq, Zpath, Q_const]; rw [zset_eq_iff hγ hS]; simp [r]
  rw [hset]
  refine ⟨fun x hx y hy z hz => ⟨fun j => ?_, fun j hj => ?_⟩⟩
  · have ez : ∀ t : ℝ, zcand P Z (t • r) j = -(muZc P Z j) + (P.gamma * (schur P Z *ᵥ fun k : In Z => r k) j) * t := by
      intro t
      rw [zcand, show (fun k : In Z => (t • r) k) = t • fun k : In Z => r k from rfl, mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have := affine_ordConnected (a := -(muZc P Z j)) (b := P.gamma * (schur P Z *ᵥ fun k : In Z => r k) j) hz.1 hz.2
    rw [← ez, ← ez, ← ez] at this
    exact le_trans (le_min (hx.1 j) (hy.1 j)) this
  · set L := (Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ fun k : In Z => r k)
    have ew : ∀ t : ℝ, wcand P Z (t • r) j - t * r j = wcand P Z 0 j + (-(L ⟨j, hj⟩) - r j) * t := by
      intro t
      rw [wcand_out (Z := Z) ⟨j, hj⟩, wcand_out (Z := Z) ⟨j, hj⟩, wc, wc]
      simp only [L]
      rw [show (fun k : In Z => (t • r) k) = t • fun k : In Z => r k from rfl,
        show (fun k : In Z => (0 : Fin M → ℝ) k) = 0 from rfl, mulVec_smul, mulVec_zero, sub_zero,
        mulVec_sub, mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have := affine_ordConnected (a := wcand P Z 0 j) (b := -(L ⟨j, hj⟩) - r j) hz.1 hz.2
    rw [← ew, ← ew, ← ew] at this
    have h1 := hx.2 j hj; have h2 := hy.2 j hj
    have : 0 < min (wcand P Z (x • r) j - x * r j) (wcand P Z (y • r) j - y * r j) :=
      lt_min (by linarith) (by linarith)
    linarith

/-- Where every at-zero set has `s^Z ≥ s^{Z0}`, `m(x) + γ s^{Z0} x` is antitone. -/
lemma h_anti' (h : Hyp P) {Z0 : Finset (Fin M)} {a b δ : ℝ}
    (hsub : ∀ y ∈ Set.Icc a b, sZ P Z0 + δ ≤ sZ P (Zpath P y)) :
    AntitoneOn (fun x => mOne P x + P.gamma * (sZ P Z0 + δ) * x) (Set.Icc a b) := by
  refine antitoneOn_of_pieces (S := fun Z : Finset (Fin M) => {x | Zpath P x = Z})
    (fun y _ => ⟨Zpath P y, rfl⟩)
    ((mOne_cont h).add (continuous_const.mul continuous_id)).continuousOn fun Z => ?_
  intro x hx y hy hxy
  have hs : sZ P Z0 + δ ≤ sZ P Z := hx.1 ▸ hsub x hx.2
  simp only
  rw [mOne_piece h hx.1, mOne_piece h hy.1]
  have hγ := hyp_gamma h
  have : P.gamma * (sZ P Z0 + δ) ≤ P.gamma * sZ P Z := mul_le_mul_of_nonneg_left hs hγ.le
  nlinarith

/-- Where every at-zero set has `s^Z ≤ s^{Z0}`, `m(x) + γ s^{Z0} x` is monotone. -/
lemma h_mono' (h : Hyp P) {Z0 : Finset (Fin M)} {a b δ : ℝ}
    (hsub : ∀ y ∈ Set.Icc a b, sZ P (Zpath P y) + δ ≤ sZ P Z0) :
    MonotoneOn (fun x => mOne P x + P.gamma * (sZ P Z0 - δ) * x) (Set.Icc a b) := by
  refine monotoneOn_of_pieces (S := fun Z : Finset (Fin M) => {x | Zpath P x = Z})
    (fun y _ => ⟨Zpath P y, rfl⟩)
    ((mOne_cont h).add (continuous_const.mul continuous_id)).continuousOn fun Z => ?_
  intro x hx y hy hxy
  have hs : sZ P Z + δ ≤ sZ P Z0 := hx.1 ▸ hsub x hx.2
  simp only
  rw [mOne_piece h hx.1, mOne_piece h hy.1]
  have hγ := hyp_gamma h
  have : P.gamma * sZ P Z ≤ P.gamma * (sZ P Z0 - δ) := mul_le_mul_of_nonneg_left (by linarith) hγ.le
  nlinarith

lemma h_anti (h : Hyp P) {Z0 : Finset (Fin M)} {a b : ℝ} (hsub : ∀ y ∈ Set.Icc a b, Z0 ⊆ Zpath P y) :
    AntitoneOn (fun x => mOne P x + P.gamma * sZ P Z0 * x) (Set.Icc a b) := by
  have := h_anti' h (δ := 0) fun y hy => by
    rw [add_zero]
    have hs := curvature _ _ P h Z0 _ (hsub y hy) (fun _ => 1)
    simpa [dotProduct, mulVec, sZ] using hs
  simpa only [add_zero] using this

lemma h_mono (h : Hyp P) {Z0 : Finset (Fin M)} {a b : ℝ} (hsub : ∀ y ∈ Set.Icc a b, Zpath P y ⊆ Z0) :
    MonotoneOn (fun x => mOne P x + P.gamma * sZ P Z0 * x) (Set.Icc a b) := by
  have := h_mono' h (δ := 0) fun y hy => by
    rw [add_zero]
    have hs := curvature _ _ P h _ Z0 (hsub y hy) (fun _ => 1)
    simpa [dotProduct, mulVec, sZ] using hs
  simpa only [sub_zero] using this

lemma exists_pos_lb {ι : Type} [Fintype ι] (f : ι → ℝ) : ∃ ε > 0, ∀ i, 0 < f i → ε ≤ f i := by
  by_cases hne : (Finset.univ.filter fun i => 0 < f i).Nonempty
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ f hne
    exact ⟨f i0, (Finset.mem_filter.mp hi0).2,
      fun i hi => hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)⟩
  · exact ⟨1, one_pos, fun i hi => absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩ hne⟩

/-- Off the piece, with every at-zero set steeper, `m(x) + γ s^{Z0} x` strictly decreases. -/
lemma h_strict_anti (h : Hyp P) {Z0 : Finset (Fin M)} {a b : ℝ} (hab : a < b)
    (hs : ∀ y ∈ Set.Icc a b, sZ P Z0 < sZ P (Zpath P y)) :
    mOne P b + P.gamma * sZ P Z0 * b < mOne P a + P.gamma * sZ P Z0 * a := by
  obtain ⟨ε, hε, hlb⟩ := exists_pos_lb fun Z => sZ P Z - sZ P Z0
  have hA := h_anti' h (δ := ε) (Z0 := Z0) (a := a) (b := b) fun y hy => by
    have := hlb (Zpath P y) (sub_pos.mpr (hs y hy)); linarith
  have := hA ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  simp only at this
  have hγ := hyp_gamma h
  nlinarith [mul_pos (mul_pos hγ hε) (sub_pos.mpr hab)]

lemma h_strict_mono (h : Hyp P) {Z0 : Finset (Fin M)} {a b : ℝ} (hab : a < b)
    (hs : ∀ y ∈ Set.Icc a b, sZ P (Zpath P y) < sZ P Z0) :
    mOne P a + P.gamma * sZ P Z0 * a < mOne P b + P.gamma * sZ P Z0 * b := by
  obtain ⟨ε, hε, hlb⟩ := exists_pos_lb fun Z => sZ P Z0 - sZ P Z
  have hM := h_mono' h (δ := ε) (Z0 := Z0) (a := a) (b := b) fun y hy => by
    have := hlb (Zpath P y) (sub_pos.mpr (hs y hy)); linarith
  have := hM ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  simp only at this
  have hγ := hyp_gamma h
  nlinarith [mul_pos (mul_pos hγ hε) (sub_pos.mpr hab)]

/-- Once the path has left the piece at `y0`, it does not return. -/
lemma off_piece_right (h : Hyp P) {xm y0 y : ℝ} (hy0 : xm ≤ y0) (hy : y0 ≤ y)
    (hne : Zpath P y0 ≠ Zpath P xm) : Zpath P y ≠ Zpath P xm := fun he =>
  hne ((piece_ordConnected h (Zpath P xm)).out rfl he ⟨hy0, hy⟩)

lemma off_piece_left (h : Hyp P) {xm y0 y : ℝ} (hy0 : y0 ≤ xm) (hy : y ≤ y0)
    (hne : Zpath P y0 ≠ Zpath P xm) : Zpath P y ≠ Zpath P xm := fun he =>
  hne ((piece_ordConnected h (Zpath P xm)).out he rfl ⟨hy, hy0⟩)

theorem path : Path := by
  intro M P h r
  have hγ := hyp_gamma h; have hS := hyp_sig h
  have hcurv : ∀ Z Z' : Finset (Fin M), Z ⊆ Z' → sZ P Z ≤ sZ P Z' := fun Z Z' hZ => by
    have hs := curvature _ _ P h Z Z' hZ (fun _ => 1)
    simpa [dotProduct, mulVec, sZ] using hs
  refine ⟨mOne_lip h, mOne_strict h, fun Z => ⟨piece_ordConnected h Z, fun x hx => mOne_piece h hx, ?_,
    fun x => ?_, fun x j hj => ?_⟩, hcurv, ?_⟩
  · ext x; simp only [Set.mem_ofPred_eq, Zpath, Q_const]; rw [zset_eq_iff hγ hS]; simp [r]
  · rw [zcand, show (fun k : In Z => (x • r) k) = x • fun k : In Z => r k from rfl, mulVec_smul,
      smul_comm]
  · rw [wcand_out (Z := Z) ⟨j, hj⟩, wcand_out (Z := Z) ⟨j, hj⟩, wc, wc,
      show (fun k : In Z => (x • r) k) = x • fun k : In Z => r k from rfl,
      show (fun k : In Z => (0 : Fin M → ℝ) k) = 0 from rfl, mulVec_smul, mulVec_zero, sub_zero,
      mulVec_sub, mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  intro xs hxs hmax xm Z0 c a xt
  have hbox : (fun _ => xs : Fin 1 → ℝ) ∈ Box P := box_one.mpr hxs
  have hmaxP := phi_max_one hmax
  have hPxm : P.xm = fun _ => xm := one_eq _
  have hc : 0 < c := mul_pos hγ (sZ_pos h Z0)
  have hmxm : mOne P xm = a - c * xm := mOne_piece h rfl
  have hGxm : Gm P P.xm 0 = mOne P xm := by rw [hPxm]; rfl
  have hxm0 : 0 ≤ xm := (h.2.2.2.2 0).1
  have hxmb : xm ≤ P.xbar 0 := (h.2.2.2.2 0).2
  have hkp : 0 ≤ P.kp 0 := (h.2.2.2.1 0).1
  have hkm : 0 ≤ P.km 0 := (h.2.2.2.1 0).2
  have huniq : ∀ y, (fun _ => y : Fin 1 → ℝ) ∈ Box P → IsMaxOn (Phi P) (Box P) (fun _ => y) → xs = y :=
    fun y hy hm => congrFun (phi_unique h hbox hmaxP hy hm) 0
  have hanti : StrictAnti (mOne P) := mOne_strict h
  refine ⟨fun hlo hhi => ?_, fun hbuy u hu => ?_, fun hsell u hu => ?_⟩
  · -- held
    have hopt : IsMaxOn (Phi P) (Box P) P.xm := xm_opt h fun i => by
      rw [Subsingleton.elim i 0, hGxm]; exact ⟨fun _ => hhi, fun _ => hlo⟩
    refine ⟨huniq xm (by rw [← hPxm]; exact xm_mem h) (by rw [← hPxm]; exact hopt), ?_⟩
    have h1 : (a - P.kp 0) / c ≤ xm := by rw [div_le_iff₀ hc]; linarith
    have h2 : xm ≤ (a + P.km 0) / c := by rw [le_div_iff₀ hc]; linarith
    simp only [xt, Standalone.M7TwoStageExactnessLoss.bandHold, min_eq_right h2, max_eq_right h1, min_eq_right hxmb, max_eq_right hxm0]
  · -- purchase
    intro ut
    have hxu : xm < u := (StrictAnti.lt_iff_gt hanti).mp (by rw [hu]; exact hbuy)
    have hut : c * ut = a - P.kp 0 := by simp only [ut]; field_simp
    have hxut : xm < ut := by
      have : xm * c < a - P.kp 0 := by linarith
      simp only [ut]; rw [lt_div_iff₀ hc]; exact this
    -- the optimum
    set y := min (P.xbar 0) u
    have hy0 : xm ≤ y := le_min hxmb hxu.le
    have hyb : (fun _ => y : Fin 1 → ℝ) ∈ Box P := box_one.mpr ⟨hxm0.trans hy0, min_le_left _ _⟩
    have hyopt : IsMaxOn (Phi P) (Box P) (fun _ => y) := by
      refine suff_opt h (t := fun _ => P.kp 0) (fun i => ?_) fun i => ?_
      · rw [Subsingleton.elim i 0]
        refine ⟨by linarith, le_rfl, fun _ => rfl, fun h' => ?_⟩
        rw [hPxm] at h'; exact absurd h' (not_lt.mpr hy0)
      · rw [Subsingleton.elim i 0]
        have hG : Gm P (fun _ => y) 0 = mOne P y := rfl
        rw [hG]
        refine ⟨fun h' => ?_, fun _ => ?_⟩
        · have : y = u := by
            simp only [y] at h' ⊢
            rcases le_total (P.xbar 0) u with h3 | h3
            · rw [min_eq_left h3] at h'; exact absurd h' (lt_irrefl _)
            · exact min_eq_right h3
          rw [this, hu]; simp
        · have : mOne P u ≤ mOne P y := hanti.antitone (min_le_right _ _)
          rw [hu] at this; linarith
    have hxs : xs = min (P.xbar 0) u := huniq y hyb hyopt
    have hxt : xt = min (P.xbar 0) ut := by
      have h1 : min ((a + P.km 0) / c) xm < (a - P.kp 0) / c := lt_of_le_of_lt (min_le_right _ _) hxut
      simp only [xt, Standalone.M7TwoStageExactnessLoss.bandHold, max_eq_left h1.le]
      exact max_eq_right (le_min (hxm0.trans hxmb) (hxm0.trans hxut.le))
    have k1 : Zpath P ut = Z0 → u = ut := fun hZ =>
      hanti.injective (by rw [hu, mOne_piece h hZ]; linarith)
    have k2 : Zpath P u = Z0 → u = ut := fun hZ => by
      have := mOne_piece h hZ
      rw [hu] at this
      simp only [ut]; rw [eq_div_iff hc.ne']; linarith
    refine ⟨hxu, hxs, hxt, ⟨fun hZ => (k1 hZ) ▸ hZ, fun hZ => (k2 hZ) ▸ hZ⟩, k1,
      by rw [hxs, hxt]; exact min_min_iff, fun hsub => ?_, fun hsub => ?_, ?_⟩
    · have hA := h_anti h hsub (show xm ∈ Set.Icc xm ut from ⟨le_rfl, hxut.le⟩)
        (show ut ∈ Set.Icc xm ut from ⟨hxut.le, le_rfl⟩) hxut.le
      simp only at hA
      have : mOne P ut ≤ mOne P u := by rw [hu]; linarith
      have hle : u ≤ ut := (StrictAnti.le_iff_ge hanti).mp this
      exact ⟨hle, by rw [hxs, hxt]; exact min_le_min_left _ hle⟩
    · have hM := h_mono h hsub (show xm ∈ Set.Icc xm ut from ⟨le_rfl, hxut.le⟩)
        (show ut ∈ Set.Icc xm ut from ⟨hxut.le, le_rfl⟩) hxut.le
      simp only at hM
      have : mOne P u ≤ mOne P ut := by rw [hu]; linarith
      have hle : ut ≤ u := (StrictAnti.le_iff_ge hanti).mp this
      exact ⟨hle, by rw [hxs, hxt]; exact min_le_min_left _ hle⟩
    · rintro ⟨y0, hy0, hne⟩
      have hoff : ∀ y ∈ Set.Icc y0 ut, Zpath P y ≠ Z0 := fun y hy => off_piece_right h hy0.1 hy.1 hne
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · have hA := h_anti' h (δ := 0) (Z0 := Z0) (a := xm) (b := ut) fun y hy => by
          rw [add_zero]
          by_cases he : Zpath P y = Z0
          · rw [he]
          · exact (hs y hy he).le
        have h1 := hA ⟨le_rfl, hxut.le⟩ ⟨hy0.1, hy0.2.le⟩ hy0.1
        have h2 := h_strict_anti h hy0.2 fun y hy => hs y ⟨hy0.1.trans hy.1, hy.2⟩ (hoff y hy)
        simp only [add_zero] at h1
        have : mOne P ut < mOne P u := by rw [hu]; linarith
        exact (StrictAnti.lt_iff_gt hanti).mp this
      · have hM := h_mono' h (δ := 0) (Z0 := Z0) (a := xm) (b := ut) fun y hy => by
          rw [add_zero]
          by_cases he : Zpath P y = Z0
          · rw [he]
          · exact (hs y hy he).le
        have h1 := hM ⟨le_rfl, hxut.le⟩ ⟨hy0.1, hy0.2.le⟩ hy0.1
        have h2 := h_strict_mono h hy0.2 fun y hy => hs y ⟨hy0.1.trans hy.1, hy.2⟩ (hoff y hy)
        simp only [sub_zero] at h1
        have : mOne P u < mOne P ut := by rw [hu]; linarith
        exact (StrictAnti.lt_iff_gt hanti).mp this
  · -- sale
    intro ut
    have hux : u < xm := (StrictAnti.lt_iff_gt hanti).mp (by rw [hu]; exact hsell)
    have hut : c * ut = a + P.km 0 := by simp only [ut]; field_simp
    have hutx : ut < xm := by
      have : a + P.km 0 < xm * c := by linarith
      simp only [ut]; rw [div_lt_iff₀ hc]; exact this
    set y := max 0 u
    have hy0 : y ≤ xm := max_le hxm0 hux.le
    have hyb : (fun _ => y : Fin 1 → ℝ) ∈ Box P := box_one.mpr ⟨le_max_left _ _, hy0.trans hxmb⟩
    have hyopt : IsMaxOn (Phi P) (Box P) (fun _ => y) := by
      refine suff_opt h (t := fun _ => -P.km 0) (fun i => ?_) fun i => ?_
      · rw [Subsingleton.elim i 0]
        refine ⟨le_rfl, by linarith, fun h' => ?_, fun _ => rfl⟩
        rw [hPxm] at h'; exact absurd h' (not_lt.mpr hy0)
      · rw [Subsingleton.elim i 0]
        have hG : Gm P (fun _ => y) 0 = mOne P y := rfl
        rw [hG]
        refine ⟨fun _ => ?_, fun h' => ?_⟩
        · have : mOne P y ≤ mOne P u := hanti.antitone (le_max_right _ _)
          rw [hu] at this; linarith
        · have : y = u := by
            simp only [y] at h' ⊢
            rcases le_total u 0 with h3 | h3
            · rw [max_eq_left h3] at h'; exact absurd h' (lt_irrefl _)
            · exact max_eq_right h3
          rw [this, hu]; simp
    have hxs : xs = max 0 u := huniq y hyb hyopt
    have hxt : xt = max 0 ut := by
      have h1 : (a + P.km 0) / c < xm := hutx
      have h2 : (a - P.kp 0) / c ≤ (a + P.km 0) / c := div_le_div_of_nonneg_right (by linarith) hc.le
      simp only [xt, Standalone.M7TwoStageExactnessLoss.bandHold, min_eq_left h1.le, max_eq_right h2,
        min_eq_right (h1.le.trans hxmb)]
      rfl
    have k1 : Zpath P ut = Z0 → u = ut := fun hZ =>
      hanti.injective (by rw [hu, mOne_piece h hZ]; linarith)
    have k2 : Zpath P u = Z0 → u = ut := fun hZ => by
      have := mOne_piece h hZ
      rw [hu] at this
      simp only [ut]; rw [eq_div_iff hc.ne']; linarith
    refine ⟨hux, hxs, hxt, ⟨fun hZ => (k1 hZ) ▸ hZ, fun hZ => (k2 hZ) ▸ hZ⟩, k1,
      by rw [hxs, hxt]; exact max_max_iff, fun hsub => ?_, fun hsub => ?_, ?_⟩
    · have hA := h_anti h hsub (show ut ∈ Set.Icc ut xm from ⟨le_rfl, hutx.le⟩)
        (show xm ∈ Set.Icc ut xm from ⟨hutx.le, le_rfl⟩) hutx.le
      simp only at hA
      have : mOne P u ≤ mOne P ut := by rw [hu]; linarith
      have hle : ut ≤ u := (StrictAnti.le_iff_ge hanti).mp this
      exact ⟨hle, by rw [hxs, hxt]; exact max_le_max_left _ hle⟩
    · have hM := h_mono h hsub (show ut ∈ Set.Icc ut xm from ⟨le_rfl, hutx.le⟩)
        (show xm ∈ Set.Icc ut xm from ⟨hutx.le, le_rfl⟩) hutx.le
      simp only at hM
      have : mOne P ut ≤ mOne P u := by rw [hu]; linarith
      have hle : u ≤ ut := (StrictAnti.le_iff_ge hanti).mp this
      exact ⟨hle, by rw [hxs, hxt]; exact max_le_max_left _ hle⟩
    · rintro ⟨y0, hy0, hne⟩
      have hoff : ∀ y ∈ Set.Icc ut y0, Zpath P y ≠ Z0 := fun y hy => off_piece_left h hy0.2 hy.2 hne
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · have hA := h_anti' h (δ := 0) (Z0 := Z0) (a := ut) (b := xm) fun y hy => by
          rw [add_zero]
          by_cases he : Zpath P y = Z0
          · rw [he]
          · exact (hs y hy he).le
        have h1 := hA ⟨hy0.1.le, hy0.2⟩ ⟨hutx.le, le_rfl⟩ hy0.2
        have h2 := h_strict_anti h hy0.1 fun y hy => hs y ⟨hy.1, hy.2.trans hy0.2⟩ (hoff y hy)
        simp only [add_zero] at h1
        have : mOne P u < mOne P ut := by rw [hu]; linarith
        exact (StrictAnti.lt_iff_gt hanti).mp this
      · have hM := h_mono' h (δ := 0) (Z0 := Z0) (a := ut) (b := xm) fun y hy => by
          rw [add_zero]
          by_cases he : Zpath P y = Z0
          · rw [he]
          · exact (hs y hy he).le
        have h1 := hM ⟨hy0.1.le, hy0.2⟩ ⟨hutx.le, le_rfl⟩ hy0.2
        have h2 := h_strict_mono h hy0.1 fun y hy => hs y ⟨hy.1, hy.2.trans hy0.2⟩ (hoff y hy)
        simp only [sub_zero] at h1
        have : mOne P ut < mOne P u := by rw [hu]; linarith
        exact (StrictAnti.lt_iff_gt hanti).mp this

end Path

/-! ### Parts 0 and 1, on claim 027's `Data` -/

section DataModel

open Standalone.M2ScoreAccounting Standalone.M2ActionClasses Standalone.M7TwoStageExactnessLoss
  Novel.M7TwoStageExactnessLossProof

variable {S : Type} [Fintype S]

lemma Q_eq {m K : ℕ} (D : Data m K K S) (θ : Params m K) (Sf : Matrix (Fin K) (Fin K) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) : (coord D θ Sf V).Q = (D.BE⁻¹)ᵀ * D.BAᵀ := by
  ext j i
  simp [coord, rvec, mulVec, dotProduct, mul_apply, mul_comm]

lemma BE_Q {m K : ℕ} {D : Data m K K S} (θ : Params m K) (Sf : Matrix (Fin K) (Fin K) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (hBE : IsUnit D.BE.det) (a : Fin m → ℝ) :
    D.BEᵀ *ᵥ ((coord D θ Sf V).Q *ᵥ a) = D.BAᵀ *ᵥ a := by
  rw [Q_eq, mulVec_mulVec, ← Matrix.mul_assoc, ← transpose_mul, nonsing_inv_mul _ hBE, transpose_one,
    Matrix.one_mul]

lemma rvec_dot {m K : ℕ} {D : Data m K K S} (hBE : IsUnit D.BE.det) (i : Fin m) (y : Fin K → ℝ) :
    (D.BA *ᵥ y) i = rvec D i ⬝ᵥ (D.BE *ᵥ y) := by
  rw [rvec, dotProduct_comm, dotProduct_mulVec (D.BE *ᵥ y), vecMul_transpose, mulVec_mulVec,
    nonsing_inv_mul _ hBE, one_mulVec, dotProduct_comm]
  rfl

omit [Fintype S] in
lemma w0_nonneg {m n K : ℕ} {D : Data m n K S} (hI : Standalone.M2TwoStageSeparation.Inputs D)
    (l : Inst m n) : 0 ≤ w0 D l :=
  div_nonneg (hI.1.2.1 l) hI.1.1.le

theorem coords : Coords := by
  intro m K S _ D θ Sf V hR hBE hkE P
  have hQ := BE_Q (D := D) θ Sf V hBE
  have hexp : ∀ x : Inst m K → ℝ, exposure D x = D.BEᵀ *ᵥ (toCoord D θ Sf V x).2 := fun x => by
    simp only [toCoord, exposure, mulVec_add, hQ]; abel
  have hwset : ∀ x : Inst m K → ℝ, (∀ j, 0 ≤ x (Sum.inr j)) ↔
      (toCoord D θ Sf V x).2 ∈ Wset (P.Q *ᵥ active x) := fun x => by
    simp only [toCoord, Wset, Set.mem_ofPred_eq, Pi.add_apply, etf]
    exact forall_congr' fun j => (le_add_iff_nonneg_left _).symm
  have hscore : ∀ x, score D x θ = J P (toCoord D θ Sf V x) := fun x => by
    have hsig : Standalone.M2TwoStageSeparation.sigF D = Sf := hR.1
    set w := (toCoord D θ Sf V x).2 with hw
    have hwd : w = etf x + P.Q *ᵥ active x := rfl
    rw [Novel.M2TwoStageSeparationProof.split, Hr_ref θ hR, hexp, ← hw]
    simp only [Standalone.M2TwoStageSeparation.Gf, hsig, zero_mulVec, dotProduct_zero, add_zero]
    have e1 : (D.BEᵀ *ᵥ w) ⬝ᵥ θ.lam = (D.BE *ᵥ θ.lam) ⬝ᵥ w := by
      rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
    have e2 : (D.BEᵀ *ᵥ w) ⬝ᵥ (Sf *ᵥ (D.BEᵀ *ᵥ w)) = w ⬝ᵥ ((D.BE * Sf * D.BEᵀ) *ᵥ w) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec w D.BE, ← mulVec_transpose]
    have e3a : (P.Q *ᵥ active x) ⬝ᵥ D.cE = (fun i => rvec D i ⬝ᵥ D.cE) ⬝ᵥ active x := by
      rw [dotProduct_comm, dotProduct_mulVec]
      congr 1; funext i; simp [vecMul, dotProduct, P, coord, mul_comm]
    have e3 : etf x ⬝ᵥ D.cE = w ⬝ᵥ D.cE - (fun i => rvec D i ⬝ᵥ D.cE) ⬝ᵥ active x := by
      rw [hwd, add_dotProduct, e3a]; ring
    have e4 : tau D (x - w0 D) = Standalone.M7FundDecisionEtfsAtZero.cost P (active x) := by
      simp only [tau, Fintype.sum_sum_type, hkE, zero_mul, add_zero, Finset.sum_const_zero,
        Standalone.M7FundDecisionEtfsAtZero.cost, P, coord, active, Pi.sub_apply, neg_sub]
    have j1 : J P (active x, w) = (D.BE *ᵥ θ.lam) ⬝ᵥ w - D.cE ⬝ᵥ w -
        D.gamma / 2 * (w ⬝ᵥ ((D.BE * Sf * D.BEᵀ) *ᵥ w)) + θ.alpha ⬝ᵥ active x +
        (fun i => rvec D i ⬝ᵥ D.cE) ⬝ᵥ active x - D.gamma / 2 * (active x ⬝ᵥ (V *ᵥ active x)) -
        Standalone.M7FundDecisionEtfsAtZero.cost P (active x) := by
      simp only [J, GE, P, coord, sub_dotProduct, add_dotProduct]; ring
    have ht : toCoord D θ Sf V x = (active x, w) := rfl
    rw [ht, j1, e1, e2, e3, e4, dotProduct_comm (active x) θ.alpha, dotProduct_comm w D.cE]
    ring
  refine ⟨hscore, hwset, fun hSf => ?_, fun x hx hmax y hy => ?_⟩
  · have hinj : Function.Injective D.BE.vecMul := fun v1 v2 h => by
      have := congrArg (fun v => v ᵥ* D.BE⁻¹) h
      simpa [vecMul_vecMul, mul_nonsing_inv _ hBE] using this
    have := hSf.mul_mul_conjTranspose_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  · simp only [Set.mem_ofPred_eq]
    rw [hscore, hscore]
    refine hmax ⟨fun i => ⟨hy.1 (Sum.inl i) |>.1, hy.1 (Sum.inl i) |>.2⟩, (hwset y).mp fun j => (hy.1 (Sum.inr j)).1⟩

theorem oneSided : OneSided := by
  intro hAX m K S _ D θ Sf V SE hI hR hBE x hx hmax hcap
  obtain ⟨η, t, hη, hηk, ht, hRb⟩ := (jointOptimality hAX m K K S D θ hI x hx).mp hmax
  have hr := hI.2.1
  set t' : Inst m K → ℝ := fun l => Sum.elim (fun i => t (Sum.inl i))
    (fun j => if x (Sum.inr j) = 0 then tconv D j else t (Sum.inr j)) l with ht'
  set ζ : Fin K → ℝ := fun j => if x (Sum.inr j) = 0 then
    η + (1 + η) * tconv D j - grad D θ x (Sum.inr j) else 0 with hζ
  have h1η : 0 < 1 + η := by linarith
  -- ETF lines
  have hEt : ∀ j, grad D θ x (Sum.inr j) = η + (1 + η) * t' (Sum.inr j) - ζ j := fun j => by
    by_cases h0 : x (Sum.inr j) = 0
    · simp only [ht', hζ, Sum.elim_inr, h0, ↓reduceIte]; ring
    · have hpos : 0 < x (Sum.inr j) := lt_of_le_of_ne (hx.1 (Sum.inr j)).1 (Ne.symm h0)
      have e1 := (hRb (Sum.inr j)).1 (hcap j)
      have e2 := (hRb (Sum.inr j)).2 hpos
      simp only [ht', hζ, Sum.elim_inr, h0, ↓reduceIte]; linarith
  refine ⟨η, t', ζ, hη, hηk, fun l => ?_, fun j hj => by simp [ht', hj], fun j => ⟨?_, fun hj => ?_, hEt j⟩,
    fun j hj hw t'' ht'' => ?_, fun i => ?_, fun i => ?_⟩
  · rcases l with i | j
    · exact ht (Sum.inl i)
    · by_cases h0 : x (Sum.inr j) = 0
      · simp only [ht', Sum.elim_inr, h0, ↓reduceIte, tconv]
        have hw := w0_nonneg hI (Sum.inr j)
        have hk := hr (Sum.inr j)
        by_cases hw0 : w0 D (Sum.inr j) = 0
        · simp only [hw0, ↓reduceIte]
          exact ⟨by linarith, le_rfl, fun _ => rfl, fun h => by rw [h0, hw0] at h; exact absurd h (lt_irrefl _)⟩
        · simp only [hw0, ↓reduceIte]
          exact ⟨le_rfl, by linarith, fun h => by rw [h0] at h; linarith, fun _ => rfl⟩
      · simp only [ht', Sum.elim_inr, h0, ↓reduceIte]; exact ht (Sum.inr j)
  · by_cases h0 : x (Sum.inr j) = 0
    · simp only [hζ, h0, ↓reduceIte]
      have e1 := (hRb (Sum.inr j)).1 (hcap j)
      obtain ⟨a1, a2, -, a4⟩ := ht (Sum.inr j)
      simp only [tconv]
      by_cases hw0 : w0 D (Sum.inr j) = 0
      · simp only [hw0, ↓reduceIte]; nlinarith
      · simp only [hw0, ↓reduceIte]
        have hlt : x (Sum.inr j) < w0 D (Sum.inr j) := by
          rw [h0]; exact lt_of_le_of_ne (w0_nonneg hI _) (Ne.symm hw0)
        rw [a4 hlt] at e1; linarith
    · simp [hζ, h0]
  · simp [hζ, hj.ne']
  · simp only [hζ, hj, ↓reduceIte, tconv, hw]
    nlinarith [ht''.2]
  · rw [grad_fund θ hR, rvec_dot hBE]
    have hg : D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D x)) =
        (fun j => η + (1 + η) * t' (Sum.inr j)) - ζ + D.cE + D.gamma • (SE *ᵥ etf x) := by
      funext j
      have := hEt j
      rw [grad_etf θ hR] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith
    rw [hg, Ared, show ∑ j, rvec D i j * ζ j = rvec D i ⬝ᵥ ζ from rfl]
    simp only [dotProduct_add, dotProduct_sub]
    ring
  · exact hRb (Sum.inl i)

end DataModel

theorem proof : Standalone.M7FundDecisionEtfsAtZero.statement :=
  ⟨coords, oneSided, atZero, valueFn', fundMarginal, holdTest, atOptimum, oneFund, premiumShift, roots,
    curvature, path, oneEtf, foldIn⟩

end

end Novel.M7FundDecisionEtfsAtZeroProof

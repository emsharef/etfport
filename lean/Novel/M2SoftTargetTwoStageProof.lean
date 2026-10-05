import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Standalone.M2SoftTargetTwoStage
import Novel.M2ActionClassesProof

/-!
# Proof of claim 028: the soft-target two-stage procedure in M2

This proof uses claim 004's proof module (compactness, convexity, concavity; `depends_on: [4]`;
Q-04).

* **Identification.** `‖b - b*‖²_{Σ_f} = ‖b‖² - 2 b'Σ_f b* + ‖b*‖²` and
  `w'Σw = ‖b(w)‖² + 2 b'C + R` give `S = Q - ν'b - (γ/2)‖b*‖²`.
* **Bounds.** `S(w_J) ≤ S(w₂)` is the multiplier bound; the first-order condition for `b*` on a
  convex `R` (`G` is an exact quadratic) gives `ν'(b - b*) ≤ 0`.
* **Exact form.** Along `w₂ + tΔw`, `S` is a quadratic in `t` minus `τ`, whose right derivative is
  computed coordinatewise from `max(x + t y, 0)`.
-/

namespace Novel.M2SoftTargetTwoStageProof

open Matrix Finset Filter Topology Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2SoftTargetTwoStage Novel.M2ActionClassesProof

set_option linter.unusedSectionVars false

variable {m n K : ℕ} {S : Type} [Fintype S]

/-! ### Algebra -/

lemma bilinF (D : Data m n K S) (x y : Fin K → ℝ) :
    x ⬝ᵥ (sigF D *ᵥ y) = ∑ s, D.q s * ((x ⬝ᵥ D.zf s) * (y ⬝ᵥ D.zf s)) := by
  simp only [dotProduct, mulVec, sigF, mul_sum, sum_mul]
  calc ∑ k, ∑ l, ∑ s, x k * (D.q s * (D.zf s k * D.zf s l) * y l)
      = ∑ k, ∑ s, ∑ l, x k * (D.q s * (D.zf s k * D.zf s l) * y l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ s, ∑ k, ∑ l, x k * (D.q s * (D.zf s k * D.zf s l) * y l) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun s _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma sqN_eq (D : Data m n K S) (x : Fin K → ℝ) : sqN D x = ∑ s, D.q s * (x ⬝ᵥ D.zf s) ^ 2 := by
  rw [sqN, bilinF]; exact Finset.sum_congr rfl fun s _ => by ring

lemma sqN_nonneg (D : Data m n K S) (hq : ∀ s, 0 ≤ D.q s) (x : Fin K → ℝ) : 0 ≤ sqN D x := by
  rw [sqN_eq]; exact sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)

lemma sqN_sub (D : Data m n K S) (b c : Fin K → ℝ) :
    sqN D (b - c) = sqN D b - 2 * (b ⬝ᵥ (sigF D *ᵥ c)) + sqN D c := by
  simp only [sqN_eq, bilinF, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [sub_dotProduct]; ring

lemma sqN_smul (D : Data m n K S) (t : ℝ) (x : Fin K → ℝ) : sqN D (t • x) = t ^ 2 * sqN D x := by
  simp only [sqN_eq, smul_dotProduct, smul_eq_mul, mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype S] in
lemma wxi (D : Data m n K S) (w : Inst m n → ℝ) (s : S) :
    w ⬝ᵥ xi D s = exposure D w ⬝ᵥ D.zf s + rres D w s := by
  simp only [dotProduct, Fintype.sum_sum_type, xi, Sum.elim_inl, Sum.elim_inr, exposure, rres,
    active, etf, mulVec, transpose_apply, Pi.add_apply, mul_add, sum_add_distrib, add_mul, mul_sum,
    sum_mul]
  have e1 : ∑ x, ∑ x_1, w (Sum.inl x) * (D.BA x x_1 * D.zf s x_1)
      = ∑ x, ∑ x_1, D.BA x_1 x * w (Sum.inl x_1) * D.zf s x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, ∑ x_1, w (Sum.inr x) * (D.BE x x_1 * D.zf s x_1)
      = ∑ x, ∑ x_1, D.BE x_1 x * w (Sum.inr x_1) * D.zf s x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]; ring

lemma crossM_dot (D : Data m n K S) (x : Fin K → ℝ) (w : Inst m n → ℝ) :
    x ⬝ᵥ crossM D w = ∑ s, D.q s * ((x ⬝ᵥ D.zf s) * rres D w s) := by
  simp only [dotProduct, crossM, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

lemma quad_split (D : Data m n K S) (w : Inst m n → ℝ) :
    w ⬝ᵥ (covariance D *ᵥ w)
      = sqN D (exposure D w) + (2 * (exposure D w ⬝ᵥ crossM D w) + resM D w) := by
  rw [quad_eq, sqN_eq, crossM_dot, resM, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [wxi]; ring

/-- Part 1's identity. -/
lemma S_eq (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) (w : Inst m n → ℝ) :
    Ssoft D θ bs w = score D w θ - nu D θ bs ⬝ᵥ exposure D w - D.gamma / 2 * sqN D bs := by
  have hq := quad_split D w
  have hs := sqN_sub D (exposure D w) bs
  have hsym : nu D θ bs ⬝ᵥ exposure D w
      = exposure D w ⬝ᵥ θ.lam - D.gamma * (exposure D w ⬝ᵥ (sigF D *ᵥ bs)) := by
    rw [nu, dotProduct_comm, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  simp only [Ssoft, score, hs, hq, hsym]
  ring

lemma S_eq_hat (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) (w : Inst m n → ℝ) :
    Ssoft D θ bs w = score D w (thetaHat D θ bs) - D.gamma / 2 * sqN D bs := by
  rw [S_eq]
  have h1 : nu D θ bs ⬝ᵥ exposure D w
      = exposure D w ⬝ᵥ θ.lam - exposure D w ⬝ᵥ (D.gamma • (sigF D *ᵥ bs)) := by
    rw [nu, sub_dotProduct, dotProduct_comm θ.lam, dotProduct_comm (D.gamma • _)]
  have : score D w (thetaHat D θ bs) = score D w θ - nu D θ bs ⬝ᵥ exposure D w := by
    rw [h1]; simp only [score, thetaHat]; ring
  rw [this]

theorem identification : Identification := by
  refine fun _ _ _ _ _ D θ bs => ⟨S_eq D θ bs, S_eq_hat D θ bs, fun A h0 w₂ hw₂ hmax w hw => ?_⟩
  have := hmax hw
  simp only [Set.mem_ofPred_eq, S_eq, h0, zero_dotProduct, sub_zero] at this ⊢
  linarith

/-! ### Continuity and the setting -/

omit [Fintype S] in
lemma continuous_exposure (D : Data m n K S) : Continuous (exposure D) := by
  have ha : Continuous (active : (Inst m n → ℝ) → Fin m → ℝ) :=
    continuous_pi fun j => continuous_apply (Sum.inl j)
  have he : Continuous (etf : (Inst m n → ℝ) → Fin n → ℝ) :=
    continuous_pi fun j => continuous_apply (Sum.inr j)
  unfold exposure
  exact (continuous_const.matrix_mulVec ha).add (continuous_const.matrix_mulVec he)

lemma continuous_score (D : Data m n K S) (θ : Params m K) : Continuous (fun w => score D w θ) := by
  have e : (fun w => score D w θ) = beliefScore D (fun _ : Unit => θ) (fun _ => 1) := by
    funext w; simp [beliefScore]
  rw [e]; exact continuous_beliefScore D _ _

lemma continuous_S (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) :
    Continuous (Ssoft D θ bs) := by
  have e : Ssoft D θ bs = fun w => score D w θ - nu D θ bs ⬝ᵥ exposure D w - D.gamma / 2 * sqN D bs :=
    funext (S_eq D θ bs)
  rw [e]
  exact ((continuous_score D θ).sub (continuous_const.dotProduct (continuous_exposure D))).sub
    continuous_const

lemma continuous_Gf (D : Data m n K S) (θ : Params m K) : Continuous (Gf D θ) := by
  unfold Gf sqN
  exact (continuous_id.dotProduct continuous_const).sub
    (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))

/-- The simplex-like set `{w ≥ 0, Σ w ≤ 1}`. -/
def Wset (m n : ℕ) : Set (Inst m n → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ 1}

omit [Fintype S] in
lemma R0_eq (D : Data m n K S) : R0 D = exposure D '' Wset m n := by
  ext b; constructor
  · rintro ⟨w, h0, h1, rfl⟩; exact ⟨w, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨w, ⟨h0, h1⟩, rfl⟩; exact ⟨w, h0, h1, rfl⟩

lemma Wset_compact : IsCompact (Wset m n) := by
  have he : Wset m n = (⋂ i, {w : Inst m n → ℝ | 0 ≤ w i}) ∩ {w | ∑ i, w i ≤ 1} := by
    ext w; simp [Wset]
  have hc : IsClosed (Wset m n) := by
    rw [he]
    exact IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
      (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  refine (isCompact_Icc (a := (0 : Inst m n → ℝ)) (b := 1)).of_isClosed_subset hc
    fun w hw => ⟨fun i => hw.1 i, fun i => ?_⟩
  have := single_le_sum (f := w) (fun j _ => hw.1 j) (mem_univ i)
  simp only [Pi.one_apply]; linarith [hw.2]

lemma setting : Setting := by
  intro _ _ _ _ _ D θ hI
  obtain ⟨hIP, hr, hq, hγ⟩ := hI
  have hF : IsCompact (F D) := isCompact_Icc.of_isClosed_subset (isClosed_F D) (F_subset_box D)
  have hsub : exposure D '' F D ⊆ R0 D := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, fun i => (hw.1 i).1, ?_, rfl⟩
    have hsum : k0 D + ∑ i, w0 D i = 1 := by
      simp only [k0, w0]
      rw [← Finset.sum_div, ← add_div]
      exact div_self hIP.1.ne'
    have htau : 0 ≤ tau D (w - w0 D) := sum_nonneg fun i _ =>
      add_nonneg (mul_nonneg (hr i).1 (le_max_right _ _)) (mul_nonneg (hr i).2 (le_max_right _ _))
    have hc := hw.2
    simp only [cash, sum_sub_distrib] at hc
    linarith
  have hR0 : IsCompact (R0 D) := by rw [R0_eq]; exact Wset_compact.image (continuous_exposure D)
  have hconv : Convex ℝ (R0 D) := by
    rintro _ ⟨x, hx0, hx1, rfl⟩ _ ⟨y, hy0, hy1, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, fun i => ?_, ?_, exposure_comb D x y a b⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith [hx0 i, hy0 i]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]; nlinarith
  have hne : (R0 D).Nonempty := by
    refine ⟨exposure D 0, 0, fun _ => le_rfl, by simp, rfl⟩
  refine ⟨hsub, hconv, hR0, hR0.exists_isMaxOn hne (continuous_Gf D θ).continuousOn,
    hF.exists_isMaxOn ⟨_, w0_mem_F D hIP⟩ (continuous_score D θ).continuousOn,
    fun bs => hF.exists_isMaxOn ⟨_, w0_mem_F D hIP⟩ (continuous_S D θ bs).continuousOn⟩

/-! ### The factor objective near a maximizer -/

lemma G_expand (D : Data m n K S) (θ : Params m K) (b c : Fin K → ℝ) :
    Gf D θ b = Gf D θ c + (b - c) ⬝ᵥ nu D θ c - D.gamma / 2 * sqN D (b - c) := by
  have hsym : c ⬝ᵥ (sigF D *ᵥ c) = sqN D c := rfl
  simp only [Gf, nu, sqN_sub, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_eq_mul, hsym]
  ring

lemma G_seg (D : Data m n K S) (θ : Params m K) (c d : Fin K → ℝ) (t : ℝ) :
    Gf D θ (c + t • d) = Gf D θ c + t * (d ⬝ᵥ nu D θ c) - D.gamma / 2 * (t ^ 2 * sqN D d) := by
  rw [G_expand D θ (c + t • d) c, add_sub_cancel_left, smul_dotProduct, smul_eq_mul, sqN_smul]

/-- First-order condition: `ν'(b - b*) ≤ 0` on a convex set where `b*` maximizes `G`. -/
lemma foc (D : Data m n K S) (θ : Params m K) (hq : ∀ s, 0 ≤ D.q s) (hγ : 0 ≤ D.gamma)
    {A : Set (Fin K → ℝ)} (hA : Convex ℝ A) {bs : Fin K → ℝ} (hbs : bs ∈ A)
    (hmax : IsMaxOn (Gf D θ) A bs) {b : Fin K → ℝ} (hb : b ∈ A) :
    nu D θ bs ⬝ᵥ (b - bs) ≤ 0 := by
  rw [dotProduct_comm]
  set g := (b - bs) ⬝ᵥ nu D θ bs
  set Q := sqN D (b - bs)
  have hQ : 0 ≤ Q := sqN_nonneg D hq _
  by_contra hg; push Not at hg
  set t := min 1 (g / (D.gamma * Q + 1))
  have ht0 : 0 < t := lt_min one_pos (div_pos hg (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hmem : bs + t • (b - bs) ∈ A := hA.add_smul_sub_mem hbs hb ⟨ht0.le, ht1⟩
  have hle := hmax hmem
  simp only [Set.mem_ofPred_eq] at hle
  rw [G_seg] at hle
  have htg : t * (D.gamma * Q + 1) ≤ g := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  nlinarith [mul_nonneg (mul_nonneg ht0.le ht0.le) (mul_nonneg hγ hQ), mul_nonneg hγ hQ]

/-! ### Parts 2, 4 and 5 -/

theorem multiplierBound : MultiplierBound := by
  intro _ _ _ _ _ D θ hI A bs wJ w₂ hwJ hJ hw₂ h2
  have hS := h2 hwJ
  have hQ := hJ hw₂
  simp only [Set.mem_ofPred_eq, S_eq] at hS hQ
  have hsub : nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂)
      = nu D θ bs ⬝ᵥ exposure D wJ - nu D θ bs ⬝ᵥ exposure D w₂ := dotProduct_sub _ _ _
  have hle : score D wJ θ - score D w₂ θ ≤ nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂) := by
    rw [hsub]; linarith
  refine ⟨by linarith, hle, ⟨fun heq w hw => ?_, fun hmax => ?_⟩,
    hle.trans (Real.sum_mul_le_sqrt_mul_sqrt univ _ _), fun he => ?_, fun R hR hsubR hbs hG => ?_⟩
  · have := h2 hw
    simp only [Set.mem_ofPred_eq, S_eq] at this ⊢
    rw [hsub] at heq; linarith
  · have := hmax hw₂
    simp only [Set.mem_ofPred_eq, S_eq] at this
    rw [hsub]; linarith
  · rw [he, sub_self, dotProduct_zero] at hle; linarith
  · have hf := foc D θ hI.2.2.1 hI.2.2.2 hR hbs hG (hsubR ⟨wJ, hwJ, rfl⟩)
    have hsplit : nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂)
        = nu D θ bs ⬝ᵥ (exposure D wJ - bs) + nu D θ bs ⬝ᵥ (bs - exposure D w₂) := by
      rw [← dotProduct_add]; congr 1; abel
    refine ⟨by linarith, fun he => ?_⟩
    rw [he] at hle
    linarith

theorem fibreRelation : FibreRelation := by
  intro _ _ _ _ _ D θ bs wJ w₂ wT hw₂ h2 hwT hbT
  have := h2 hwT
  simp only [Set.mem_ofPred_eq, S_eq, hbT] at this
  rw [dotProduct_sub]
  constructor <;> linarith

theorem multiplier : Multiplier := by
  intro _ _ _ _ _ D θ hI R bs hR hbs hG
  refine ⟨rfl, fun b hb => foc D θ hI.2.2.1 hI.2.2.2 hR hbs hG hb, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hdir : ∀ k, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      nu D θ bs ⬝ᵥ ((σ * (ε / 2)) • Pi.single k (1 : ℝ)) ≤ 0 := fun k σ hσ => by
    have hmem : bs + (σ * (ε / 2)) • Pi.single k (1 : ℝ) ∈ R := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_) (half_lt_self hε)
      rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      have hε2 : |ε / 2| = ε / 2 := abs_of_pos (half_pos hε)
      rcases hσ with rfl | rfl <;> by_cases hi : i = k <;>
        simp [hi, hε2, (half_pos hε).le]
    have := foc D θ hI.2.2.1 hI.2.2.2 hR hbs hG hmem
    rwa [add_sub_cancel_left] at this
  funext k
  have h1 := hdir k 1 (Or.inl rfl)
  have h2 := hdir k (-1) (Or.inr rfl)
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at h1 h2
  simp only [Pi.zero_apply]
  nlinarith

/-! ### Part 3: directional derivatives along the segment -/

lemma hasDeriv_max (x y : ℝ) :
    HasDerivWithinAt (fun t : ℝ => max (x + t * y) 0) (Dplus x y) (Set.Ici 0) 0 := by
  unfold Dplus
  have hlin : HasDerivAt (fun t : ℝ => x + t * y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x
  split_ifs with h1 h2
  · have hev : (fun t : ℝ => max (x + t * y) 0) =ᶠ[𝓝 0] fun t => x + t * y := by
      have : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < x + t * y :=
        (hlin.continuousAt).eventually (lt_mem_nhds (by simpa using h1))
      filter_upwards [this] with t ht using max_eq_left ht.le
    exact (hlin.congr_of_eventuallyEq hev).hasDerivWithinAt
  · have hev : (fun t : ℝ => max (x + t * y) 0) =ᶠ[𝓝 0] fun _ => 0 := by
      have : ∀ᶠ t in 𝓝 (0 : ℝ), x + t * y < 0 :=
        (hlin.continuousAt).eventually (gt_mem_nhds (by simpa using h2))
      filter_upwards [this] with t ht using max_eq_right ht.le
    exact ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev).hasDerivWithinAt
  · have hx : x = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hx
    have hd : HasDerivWithinAt (fun t : ℝ => t * max y 0) (max y 0) (Set.Ici 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (max y 0)).hasDerivWithinAt
    refine hd.congr (fun t (ht : 0 ≤ t) => ?_) (by simp)
    rw [zero_add]
    rcases le_total y 0 with hy | hy
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ht hy), max_eq_right hy, mul_zero]
    · rw [max_eq_left (mul_nonneg ht hy), max_eq_left hy]

/-- The kink inequality and its equality case. -/
lemma kink (x y : ℝ) : Dplus x y ≤ max (x + y) 0 - max x 0 ∧
    (0 ≤ x * (x + y) → Dplus x y = max (x + y) 0 - max x 0) := by
  unfold Dplus
  split_ifs with h1 h2
  · refine ⟨by rw [max_eq_left h1.le]; linarith [le_max_left (x + y) 0], fun h => ?_⟩
    have : 0 ≤ x + y := by
      by_contra hn; push Not at hn; nlinarith
    rw [max_eq_left h1.le, max_eq_left this]; ring
  · refine ⟨by rw [max_eq_right h2.le]; linarith [le_max_right (x + y) 0], fun h => ?_⟩
    have : x + y ≤ 0 := by
      by_contra hn; push Not at hn; nlinarith
    rw [max_eq_right h2.le, max_eq_right this]; ring
  · have hx : x = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hx
    simp

lemma tau_seg (D : Data m n K S) (v d : Inst m n → ℝ) (t : ℝ) :
    tau D (v + t • d) = ∑ i, (D.kplus i * max (v i + t * d i) 0
      + D.kminus i * max (-v i + t * -d i) 0) := by
  simp only [tau, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

lemma hasDeriv_tau (D : Data m n K S) (v d : Inst m n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => tau D (v + t • d)) (tauD D v d) (Set.Ici 0) 0 := by
  have e : (fun t : ℝ => tau D (v + t • d)) = fun t => ∑ i, (D.kplus i * max (v i + t * d i) 0
      + D.kminus i * max (-v i + t * -d i) 0) := funext (tau_seg D v d)
  rw [e]
  have := HasDerivWithinAt.sum (u := univ) fun i _ =>
    ((hasDeriv_max (v i) (d i)).const_mul (D.kplus i)).add
      ((hasDeriv_max (-v i) (-d i)).const_mul (D.kminus i))
  convert this using 1
  · funext t
    simp [Finset.sum_apply]
  · simp only [tauD]

lemma kink_tau (D : Data m n K S) (hr : RatesNonneg D) (v d : Inst m n → ℝ) :
    0 ≤ tau D (v + d) - tau D v - tauD D v d ∧
    ((∀ i, 0 ≤ v i * (v + d) i) → tau D (v + d) - tau D v - tauD D v d = 0) := by
  have e1 : tau D (v + d) - tau D v - tauD D v d = ∑ i, (D.kplus i * (max (v i + d i) 0 - max (v i) 0
      - Dplus (v i) (d i)) + D.kminus i * (max (-v i + -d i) 0 - max (-v i) 0 - Dplus (-v i) (-d i))) := by
    simp only [tau, tauD, Pi.add_apply, ← sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [neg_add]; ring
  rw [e1]
  refine ⟨sum_nonneg fun i _ => add_nonneg (mul_nonneg (hr i).1 (by linarith [(kink (v i) (d i)).1]))
    (mul_nonneg (hr i).2 (by linarith [(kink (-v i) (-d i)).1])), fun h => sum_eq_zero fun i _ => ?_⟩
  have h1 := (kink (v i) (d i)).2 (by simpa using h i)
  have h2 := (kink (-v i) (-d i)).2 (by have := h i; simp only [Pi.add_apply] at this; nlinarith)
  rw [h1, h2]; ring

lemma cov_bilin (D : Data m n K S) (x y : Inst m n → ℝ) :
    x ⬝ᵥ (covariance D *ᵥ y) = ∑ s, D.q s * ((x ⬝ᵥ xi D s) * (y ⬝ᵥ xi D s)) := by
  simp only [dotProduct, mulVec, covariance, mul_sum, sum_mul]
  calc ∑ i, ∑ j, ∑ s, x i * (D.q s * (xi D s i * xi D s j) * y j)
      = ∑ i, ∑ s, ∑ j, x i * (D.q s * (xi D s i * xi D s j) * y j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ j, x i * (D.q s * (xi D s i * xi D s j) * y j) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun s _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma quad_seg (D : Data m n K S) (w d : Inst m n → ℝ) (t : ℝ) :
    (w + t • d) ⬝ᵥ (covariance D *ᵥ (w + t • d))
      = w ⬝ᵥ (covariance D *ᵥ w) + 2 * t * (w ⬝ᵥ (covariance D *ᵥ d))
        + t ^ 2 * (d ⬝ᵥ (covariance D *ᵥ d)) := by
  simp only [cov_bilin, add_dotProduct, smul_dotProduct, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype S] in
lemma exposure_seg (D : Data m n K S) (w d : Inst m n → ℝ) (t : ℝ) :
    exposure D (w + t • d) = exposure D w + t • exposure D d := by
  have := exposure_comb D w d 1 t
  rwa [one_smul, one_smul] at this

/-- `S` along the segment is a quadratic in `t` minus `τ`. -/
lemma S_seg (D : Data m n K S) (θ : Params m K) (bs : Fin K → ℝ) (w d : Inst m n → ℝ) (t : ℝ) :
    Ssoft D θ bs (w + t • d) = Ssoft D θ bs w + tau D (w - w0 D)
      + t * (SD D θ bs w d + tauD D (w - w0 D) d)
      - D.gamma / 2 * (t ^ 2 * (d ⬝ᵥ (covariance D *ᵥ d))) - tau D (w - w0 D + t • d) := by
  have hact : active (w + t • d) = active w + t • active d := rfl
  have hetf : etf (w + t • d) = etf w + t • etf d := rfl
  have hw : w + t • d - w0 D = w - w0 D + t • d := by abel
  have hnu : ∀ b, b ⬝ᵥ θ.lam - nu D θ bs ⬝ᵥ b = b ⬝ᵥ (D.gamma • (sigF D *ᵥ bs)) := fun b => by
    rw [nu, sub_dotProduct, dotProduct_comm θ.lam, dotProduct_comm (D.gamma • _)]; ring
  rw [S_eq, S_eq]
  simp only [score, exposure_seg, hact, hetf, hw, quad_seg, SD]
  have h1 := hnu (exposure D w + t • exposure D d)
  have h2 := hnu (exposure D w)
  have h3 := hnu (exposure D d)
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1 h2 h3 ⊢
  linear_combination t * h3

theorem exactForm : ExactForm := by
  intro _ _ _ _ _ D θ hI bs wJ w₂ hwJ hJ hw₂ h2
  set d := wJ - w₂
  have hτ := hasDeriv_tau D (w₂ - w0 D) d
  -- the derivative of S along the segment
  have hP : HasDerivWithinAt (fun t : ℝ => Ssoft D θ bs w₂ + tau D (w₂ - w0 D)
      + t * (SD D θ bs w₂ d + tauD D (w₂ - w0 D) d)
      - D.gamma / 2 * (t ^ 2 * (d ⬝ᵥ (covariance D *ᵥ d))))
      (SD D θ bs w₂ d + tauD D (w₂ - w0 D) d) (Set.Ici 0) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (SD D θ bs w₂ d + tauD D (w₂ - w0 D) d)).const_add
      (Ssoft D θ bs w₂ + tau D (w₂ - w0 D))).sub
      ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (d ⬝ᵥ (covariance D *ᵥ d))).const_mul (D.gamma / 2))
    convert this.hasDerivWithinAt using 1
    · funext t; simp only [id, Pi.sub_apply, Pi.pow_apply]
    · simp
  have hS : HasDerivWithinAt (fun t : ℝ => Ssoft D θ bs (w₂ + t • d)) (SD D θ bs w₂ d) (Set.Ici 0) 0 := by
    have := hP.sub hτ
    rw [add_sub_cancel_right] at this
    exact this.congr (fun t _ => S_seg D θ bs w₂ d t) (S_seg D θ bs w₂ d 0)
  -- optimality along the segment
  have hSD : SD D θ bs w₂ d ≤ 0 := by
    have hconv := (classesConvex D hI.2.1).1
    have hT := hasDerivWithinAt_iff_tendsto_slope.mp hS
    have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
      ext t; simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨h, hne⟩; exact lt_of_le_of_ne h (Ne.symm hne)
      · intro h; exact ⟨h.le, h.ne'⟩
    rw [hset] at hT
    refine le_of_tendsto hT ?_
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi 0 := self_mem_nhdsWithin
    filter_upwards [h1, hev] with t ht1 ht0'
    have ht0 : 0 < t := ht0'
    have hmem : w₂ + t • d ∈ F D := by
      have := hconv hw₂ hwJ (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      funext i; simp only [d, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hle := h2 hmem
    simp only [Set.mem_ofPred_eq] at hle
    rw [slope_def_field]
    simp only [zero_smul, add_zero, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
  -- the exact form at t = 1
  have hk := kink_tau D hI.2.1 (w₂ - w0 D) d
  have hvJ : w₂ - w0 D + d = wJ - w0 D := by simp only [d]; abel
  rw [hvJ] at hk
  have hw2d : w₂ + d = wJ := by simp only [d]; abel
  have h1 := S_seg D θ bs w₂ d 1
  rw [one_smul, hw2d, hvJ] at h1
  have hSJ := S_eq D θ bs wJ
  have hS2 := S_eq D θ bs w₂
  have hsub : nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂)
      = nu D θ bs ⬝ᵥ exposure D wJ - nu D θ bs ⬝ᵥ exposure D w₂ := dotProduct_sub _ _ _
  have hγ := hI.2.2.2
  have hQd : 0 ≤ d ⬝ᵥ (covariance D *ᵥ d) := by
    rw [quad_eq]; exact sum_nonneg fun s _ => mul_nonneg (hI.2.2.1 s) (sq_nonneg _)
  have hid : score D wJ θ - score D w₂ θ
      = nu D θ bs ⬝ᵥ (exposure D wJ - exposure D w₂) - D.gamma / 2 * (d ⬝ᵥ (covariance D *ᵥ d))
        - (-SD D θ bs w₂ d + (tau D (wJ - w0 D) - tau D (w₂ - w0 D) - tauD D (w₂ - w0 D) d)) := by
    rw [hsub]; linarith
  refine ⟨hτ, hS, hSD, hk.1, fun h => hk.2 (by simpa [hvJ] using h), hid, ?_⟩
  rw [hid]; linarith [hk.1]

/-- Claim 028, all parts. -/
theorem proof : Standalone.M2SoftTargetTwoStage.statement :=
  ⟨setting, identification, multiplierBound, exactForm, fibreRelation, multiplier⟩

end Novel.M2SoftTargetTwoStageProof

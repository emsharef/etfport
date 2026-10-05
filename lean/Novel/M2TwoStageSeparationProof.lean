import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Standalone.M2TwoStageSeparation
import Novel.M2ActionClassesProof

/-!
# Proof of claim 027: the two-stage factor-then-manager procedure in M2

This proof uses claim 004's proof module (compactness, convexity and concavity; `depends_on: [4, 5]`;
Q-04). Claim 003's belief-average identity is re-derived here in three lines.

* **Split.** `w'Σw = Σ_s q_s (b(w)'z^f_s + rres_s)²`, expanded.
* **Value function.** Fibres are compact, so `V` is attained; `G + V` is the fibre maximum of the
  score, hence concave. `H` (so `V`) is concave when the cross moments vanish.
* **Separation and bounds.** `G` is an exact quadratic, `G(b) = G(c) + g'(b - c) - (γ/2)‖b - c‖²`
  with `g = λ - γ Σ_f c`, and a maximizer of `G` on the convex `B_F` has `g'(b - b*) ≤ 0` there.
-/

namespace Novel.M2TwoStageSeparationProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2TwoStageSeparation Novel.M2ActionClassesProof
open scoped Topology

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

/-- The exact split `Q = G(b(w)) + H(w)`. -/
lemma split (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ) :
    score D w θ = Gf D θ (exposure D w) + Hr D θ w := by
  have hq : w ⬝ᵥ (covariance D *ᵥ w)
      = sqN D (exposure D w) + (2 * (exposure D w ⬝ᵥ crossM D w) + resM D w) := by
    rw [quad_eq, sqN_eq, crossM_dot, resM, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [wxi]; ring
  simp only [score, Gf, Hr, hq, sqN]
  ring

/-- `G` is an exact quadratic around any point. -/
lemma G_expand (D : Data m n K S) (θ : Params m K) (b c : Fin K → ℝ) :
    Gf D θ b = Gf D θ c + (b - c) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ c))
      - D.gamma / 2 * sqN D (b - c) := by
  have key : sqN D b = sqN D c + 2 * ((b - c) ⬝ᵥ (sigF D *ᵥ c)) + sqN D (b - c) := by
    simp only [sqN_eq, bilinF, mul_sum, ← sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [sub_dotProduct]; ring
  simp only [Gf, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_dotProduct]
  rw [show b ⬝ᵥ (sigF D *ᵥ b) = sqN D b from rfl, show c ⬝ᵥ (sigF D *ᵥ c) = sqN D c from rfl, key,
    sub_dotProduct, show c ⬝ᵥ (sigF D *ᵥ c) = sqN D c from rfl]
  ring

/-! ### Continuity -/

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

lemma continuous_Gf (D : Data m n K S) (θ : Params m K) : Continuous (Gf D θ) := by
  unfold Gf
  simp only [mulVec, dotProduct]
  fun_prop

lemma continuous_Hr (D : Data m n K S) (θ : Params m K) : Continuous (Hr D θ) := by
  have e : Hr D θ = fun w => score D w θ - Gf D θ (exposure D w) := by
    funext w; rw [split]; ring
  rw [e]
  exact (continuous_score D θ).sub ((continuous_Gf D θ).comp (continuous_exposure D))

/-! ### Part 0 -/

section Main

variable {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
include hI

omit θ in
lemma F_compact : IsCompact (F D) :=
  isCompact_Icc.of_isClosed_subset (isClosed_F D) (F_subset_box D)

omit θ in
lemma F_convex : Convex ℝ (F D) := (classesConvex D hI.2.1).1

omit θ in
lemma BF_nonempty : (BF D).Nonempty := ⟨_, Set.mem_image_of_mem _ (w0_mem_F D hI.1)⟩

omit θ in
lemma BF_convex : Convex ℝ (BF D) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, F_convex hI hx hy ha hb hab, exposure_comb D x y a b⟩

omit θ in
lemma BF_compact : IsCompact (BF D) := (F_compact hI).image (continuous_exposure D)

omit θ in
lemma fibre_compact (b : Fin K → ℝ) : IsCompact (fibre D b) :=
  (F_compact hI).inter_right (isClosed_eq (continuous_exposure D) continuous_const)

lemma V_attain {b : Fin K → ℝ} (hb : b ∈ BF D) :
    ∃ w ∈ fibre D b, IsMaxOn (Hr D θ) (fibre D b) w ∧ Vr D θ b = Hr D θ w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hb
  obtain ⟨w, hw, hmax⟩ := (fibre_compact hI (exposure D w₀)).exists_isMaxOn ⟨w₀, hw₀, rfl⟩
    (continuous_Hr D θ).continuousOn
  refine ⟨w, hw, hmax, ?_⟩
  have hg : IsGreatest (Hr D θ '' fibre D (exposure D w₀)) (Hr D θ w) :=
    ⟨Set.mem_image_of_mem _ hw, by rintro _ ⟨v, hv, rfl⟩; exact hmax hv⟩
  exact hg.csSup_eq

lemma H_le_V {b : Fin K → ℝ} {w : Inst m n → ℝ} (hw : w ∈ fibre D b) : Hr D θ w ≤ Vr D θ b := by
  obtain ⟨v, -, hmax, hV⟩ := V_attain θ hI ⟨w, hw.1, hw.2⟩
  rw [hV]; exact hmax hw

/-- `G + V` is the fibre maximum of the score. -/
lemma score_le_GV {b : Fin K → ℝ} {w : Inst m n → ℝ} (hw : w ∈ fibre D b) :
    score D w θ ≤ Gf D θ b + Vr D θ b := by
  rw [split, hw.2]; linarith [H_le_V θ hI hw]

lemma GV_attain {b : Fin K → ℝ} (hb : b ∈ BF D) :
    ∃ w ∈ fibre D b, score D w θ = Gf D θ b + Vr D θ b := by
  obtain ⟨w, hw, -, hV⟩ := V_attain θ hI hb
  exact ⟨w, hw, by rw [split, hw.2, hV]⟩

lemma GV_concave : ConcaveOn ℝ (BF D) (fun b => Gf D θ b + Vr D θ b) := by
  refine ⟨BF_convex hI, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨wx, hwx, ex⟩ := GV_attain θ hI hx
  obtain ⟨wy, hwy, ey⟩ := GV_attain θ hI hy
  have hmem : a • wx + b • wy ∈ fibre D (a • x + b • y) :=
    ⟨F_convex hI hwx.1 hwy.1 ha hb hab, by rw [exposure_comb, hwx.2, hwy.2]⟩
  have hc := score_concave D hI.2.2.2 hI.2.1 hI.2.2.1 ha hb hab wx wy θ
  have hle := score_le_GV θ hI hmem
  simp only [smul_eq_mul]
  rw [← ex, ← ey]
  linarith

omit hI in
lemma rres_comb (w w' : Inst m n → ℝ) (a b : ℝ) (s : S) :
    rres D (a • w + b • w') s = a * rres D w s + b * rres D w' s := by
  have hact : active (a • w + b • w') = a • active w + b • active w' := rfl
  have hetf : etf (a • w + b • w') = a • etf w + b • etf w' := rfl
  simp only [rres, hact, hetf, dot_comb]
  ring

/-- `H` is concave along segments of `F` when the cross moments vanish on `F`. -/
lemma H_concave (hC : ∀ w ∈ F D, crossM D w = 0) {x y : Inst m n → ℝ} (hx : x ∈ F D) (hy : y ∈ F D)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Hr D θ x + b * Hr D θ y ≤ Hr D θ (a • x + b • y) := by
  have hz := F_convex hI hx hy ha hb hab
  have hR : resM D (a • x + b • y) ≤ a * resM D x + b * resM D y := by
    simp only [resM, rres_comb, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun s _ => ?_
    have hb' : b = 1 - a := by linarith
    subst hb'
    have key : (a * rres D x s + (1 - a) * rres D y s) ^ 2 ≤ a * rres D x s ^ 2 + (1 - a) * rres D y s ^ 2 := by
      nlinarith [mul_nonneg ha hb, sq_nonneg (rres D x s - rres D y s)]
    nlinarith [mul_le_mul_of_nonneg_left key (hI.2.2.1 s)]
  have ht := tau_convex D hI.2.1 ha hb (x - w0 D) (y - w0 D)
  rw [← comb_sub x y (w0 D) hab] at ht
  have hact : active (a • x + b • y) = a • active x + b • active y := rfl
  have hetf : etf (a • x + b • y) = a • etf x + b • etf y := rfl
  simp only [Hr, hC _ hx, hC _ hy, hC _ hz, dotProduct_zero, mul_zero, zero_add, hact, hetf, dot_comb]
  nlinarith [mul_le_mul_of_nonneg_left hR (div_nonneg hI.2.2.2 (by norm_num : (0 : ℝ) ≤ 2))]

lemma V_concave (hC : ∀ w ∈ F D, crossM D w = 0) : ConcaveOn ℝ (BF D) (Vr D θ) := by
  refine ⟨BF_convex hI, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨wx, hwx, -, ex⟩ := V_attain θ hI hx
  obtain ⟨wy, hwy, -, ey⟩ := V_attain θ hI hy
  have hmem : a • wx + b • wy ∈ fibre D (a • x + b • y) :=
    ⟨F_convex hI hwx.1 hwy.1 ha hb hab, by rw [exposure_comb, hwx.2, hwy.2]⟩
  have hc := H_concave θ hI hC hwx.1 hwy.1 ha hb hab
  have hle := H_le_V θ hI hmem
  simp only [smul_eq_mul]
  rw [ex, ey]
  linarith

lemma J_attain : ∃ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ :=
  (F_compact hI).exists_isMaxOn ⟨_, w0_mem_F D hI.1⟩ (continuous_score D θ).continuousOn

lemma J_eq {wJ : Inst m n → ℝ} (hwJ : wJ ∈ F D) (hmax : IsMaxOn (fun w => score D w θ) (F D) wJ) :
    score D wJ θ = Gf D θ (exposure D wJ) + Vr D θ (exposure D wJ) ∧
    ∀ b ∈ BF D, Gf D θ b + Vr D θ b ≤ score D wJ θ := by
  refine ⟨le_antisymm (score_le_GV θ hI ⟨hwJ, rfl⟩) ?_, fun b hb => ?_⟩
  · obtain ⟨w, hw, hs⟩ := GV_attain θ hI (⟨wJ, hwJ, rfl⟩ : exposure D wJ ∈ BF D)
    rw [← hs]; exact hmax hw.1
  · obtain ⟨w, hw, hs⟩ := GV_attain θ hI hb
    rw [← hs]; exact hmax hw.1

end Main

lemma dot_wsum {ι T : Type} [Fintype ι] [Fintype T] (e : ι → ℝ) (pi : T → ℝ)
    (l : T → ι → ℝ) : e ⬝ᵥ (∑ t, pi t • l t) = ∑ t, pi t * (e ⬝ᵥ l t) := by
  rw [dotProduct_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [dotProduct_smul, smul_eq_mul]

/-- `Q̄₀ = Q₀(·; θ̄)` (claim 003's identity, re-derived). -/
lemma beliefAverage (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi : T → ℝ) (hpi : ∑ t, pi t = 1) (w : Inst m n → ℝ) :
    beliefScore D par pi w = score D w (beliefMean par pi) := by
  set c := -(etf w ⬝ᵥ D.cE) - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D)
  have hs : ∀ θ : Params m K, score D w θ = exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha + c :=
    fun θ => by simp only [score, c]; ring
  simp only [beliefScore, beliefMean, hs, dot_wsum, mul_add, sum_add_distrib, ← sum_mul, hpi,
    one_mul]

theorem splitThm : Split := by
  refine ⟨fun _ _ _ _ _ D θ w => split D θ w, fun _ _ _ _ _ D _ _ par pi hpi w => ?_,
    fun _ _ _ _ _ D θ hI => ⟨BF_nonempty hI, BF_convex hI, BF_compact hI, fun b hb => V_attain θ hI hb,
      GV_concave θ hI, fun hC => V_concave θ hI hC, J_attain θ hI, fun wJ hwJ hmax => J_eq θ hI hwJ hmax⟩⟩
  rw [beliefAverage D par pi hpi w, split]

/-! ### The factor objective near a maximizer -/

lemma sqN_smul (D : Data m n K S) (t : ℝ) (x : Fin K → ℝ) : sqN D (t • x) = t ^ 2 * sqN D x := by
  simp only [sqN_eq, smul_dotProduct, smul_eq_mul, mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `G` along a segment from `c`. -/
lemma G_seg (D : Data m n K S) (θ : Params m K) (c d : Fin K → ℝ) (t : ℝ) :
    Gf D θ (c + t • d) = Gf D θ c + t * (d ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ c)))
      - D.gamma / 2 * (t ^ 2 * sqN D d) := by
  rw [G_expand D θ (c + t • d) c, add_sub_cancel_left, smul_dotProduct, smul_eq_mul, sqN_smul]

/-- First-order condition for a maximizer of `G` on a convex set. -/
lemma foc (D : Data m n K S) (θ : Params m K) (hq : ∀ s, 0 ≤ D.q s) (hγ : 0 ≤ D.gamma)
    {A : Set (Fin K → ℝ)} (hA : Convex ℝ A) {bs : Fin K → ℝ} (hbs : bs ∈ A)
    (hmax : IsMaxOn (Gf D θ) A bs) {b : Fin K → ℝ} (hb : b ∈ A) :
    (b - bs) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs)) ≤ 0 := by
  set g := (b - bs) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs))
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

/-- From a point of the relative interior one can step beyond it, away from any point of the set. -/
lemma relint_ext {A : Set (Fin K → ℝ)} {bs : Fin K → ℝ} (h : bs ∈ intrinsicInterior ℝ A)
    {b : Fin K → ℝ} (hb : b ∈ A) : ∃ t : ℝ, 0 < t ∧ bs + t • (bs - b) ∈ A := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp h
  have hbspan : b ∈ affineSpan ℝ A := subset_affineSpan ℝ A hb
  have hmem : ∀ t : ℝ, (y : Fin K → ℝ) + t • ((y : Fin K → ℝ) - b) ∈ affineSpan ℝ A := fun t => by
    have := AffineMap.lineMap_mem (-t) y.2 hbspan
    convert this using 1
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    funext k; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  set path : ℝ → affineSpan ℝ A := fun t => ⟨(y : Fin K → ℝ) + t • ((y : Fin K → ℝ) - b), hmem t⟩
  have hcont : Continuous path :=
    (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
  have h0 : path 0 = y := Subtype.ext (by simp [path])
  have hnhds : path ⁻¹' interior ((↑) ⁻¹' A : Set (affineSpan ℝ A)) ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact isOpen_interior.mem_nhds hy)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ε / 2, half_pos hε, ?_⟩
  have hin := hball (show ε / 2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; exact half_lt_self hε)
  have : path (ε / 2) ∈ ((↑) ⁻¹' A : Set (affineSpan ℝ A)) := interior_subset hin
  exact this

/-! ### Parts 1-3 -/

section Parts

variable {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
include hI

lemma targets : (∃ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs) ∧
    ∀ bTB : Fin K → ℝ, D.gamma • (sigF D *ᵥ bTB) = θ.lam →
      (∀ b, Gf D θ b ≤ Gf D θ bTB) ∧
      (bTB ∈ BF D → IsMaxOn (Gf D θ) (BF D) bTB ∧
        (PosDefF D → 0 < D.gamma → ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs → bs = bTB)) := by
  refine ⟨(BF_compact hI).exists_isMaxOn (BF_nonempty hI) (continuous_Gf D θ).continuousOn,
    fun bTB hTB => ?_⟩
  have hexp : ∀ b, Gf D θ b = Gf D θ bTB - D.gamma / 2 * sqN D (b - bTB) := fun b => by
    rw [G_expand D θ b bTB, hTB, sub_self, dotProduct_zero, add_zero]
  have hall : ∀ b, Gf D θ b ≤ Gf D θ bTB := fun b => by
    rw [hexp b]
    nlinarith [sqN_nonneg D hI.2.2.1 (b - bTB), hI.2.2.2]
  refine ⟨hall, fun hmem => ⟨fun b _ => hall b, fun hPD hγ bs hbs hmax => ?_⟩⟩
  have h1 := hmax hmem
  simp only [Set.mem_ofPred_eq] at h1
  rw [hexp bs] at h1
  have hz : sqN D (bs - bTB) ≤ 0 := by nlinarith
  by_contra hne
  exact absurd (hPD _ (sub_ne_zero.mpr hne)) (not_lt.mpr hz)

variable {wJ : Inst m n → ℝ} (hwJ : wJ ∈ F D) (hJ : IsMaxOn (fun w => score D w θ) (F D) wJ)
  {bs : Fin K → ℝ} (hbs : bs ∈ BF D) (hG : IsMaxOn (Gf D θ) (BF D) bs)
include hwJ hJ hbs hG

lemma lossIdentity :
    score D wJ θ - (Gf D θ bs + Vr D θ bs)
      = (Vr D θ (exposure D wJ) - Vr D θ bs) - (Gf D θ bs - Gf D θ (exposure D wJ)) ∧
    0 ≤ Gf D θ bs - Gf D θ (exposure D wJ) ∧
    Gf D θ bs - Gf D θ (exposure D wJ) ≤ Vr D θ (exposure D wJ) - Vr D θ bs ∧
    0 ≤ score D wJ θ - (Gf D θ bs + Vr D θ bs) := by
  obtain ⟨hJe, hJle⟩ := J_eq θ hI hwJ hJ
  have h1 := hG (⟨wJ, hwJ, rfl⟩ : exposure D wJ ∈ BF D)
  have h2 := hJle bs hbs
  simp only [Set.mem_ofPred_eq] at h1
  refine ⟨by rw [hJe]; ring, by linarith, by linarith, by linarith⟩

lemma sep_iff : Gf D θ bs + Vr D θ bs = score D wJ θ ↔
    IsMaxOn (fun b => Gf D θ b + Vr D θ b) (BF D) bs := by
  obtain ⟨hJe, hJle⟩ := J_eq θ hI hwJ hJ
  constructor
  · intro h b hb
    simp only [Set.mem_ofPred_eq]
    rw [h]; exact hJle b hb
  · intro h
    have := h (⟨wJ, hwJ, rfl⟩ : exposure D wJ ∈ BF D)
    simp only [Set.mem_ofPred_eq] at this
    exact le_antisymm (hJle bs hbs) (by rw [hJe]; exact this)

lemma sep_sup (hV : ∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs) : Gf D θ bs + Vr D θ bs = score D wJ θ :=
  (sep_iff θ hI hwJ hJ hbs hG).mpr fun b hb => by
    have := hG hb
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith [hV b hb]

lemma sep_const (hc : ∃ c, ∀ b ∈ BF D, Vr D θ b = c) : Gf D θ bs + Vr D θ bs = score D wJ θ := by
  obtain ⟨c, hc⟩ := hc
  exact sep_sup θ hI hwJ hJ hbs hG fun b hb => by rw [hc b hb, hc bs hbs]

lemma grad_zero (hint : bs ∈ interior (BF D)) :
    D.gamma • (sigF D *ᵥ bs) = θ.lam := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set g := θ.lam - D.gamma • (sigF D *ᵥ bs)
  have hdir : ∀ k : Fin K, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (σ * (ε / 2)) • (Pi.single k (1 : ℝ)) ⬝ᵥ g ≤ 0 := fun k σ hσ => by
    have hmem : bs + (σ * (ε / 2)) • Pi.single k (1 : ℝ) ∈ BF D := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_) (half_lt_self hε)
      rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      have hε2 : |ε / 2| = ε / 2 := abs_of_pos (half_pos hε)
      rcases hσ with rfl | rfl <;> by_cases hi : i = k <;>
        simp [hi, hε2, (half_pos hε).le]
    have := foc D θ hI.2.2.1 hI.2.2.2 (BF_convex hI) hbs hG hmem
    rwa [add_sub_cancel_left] at this
  have hk : ∀ k, g k = 0 := fun k => by
    have h1 := hdir k 1 (Or.inl rfl)
    have h2 := hdir k (-1) (Or.inr rfl)
    simp only [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul] at h1 h2
    nlinarith
  funext k
  have := hk k
  simp only [g, Pi.sub_apply] at this
  linarith

/-- At a relative-interior maximizer the gradient of `G` vanishes along `B_F`. -/
lemma tangent_zero (hri : bs ∈ intrinsicInterior ℝ (BF D)) :
    ∀ b ∈ BF D, (b - bs) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs)) = 0 := by
  intro b hb
  have h1 := foc D θ hI.2.2.1 hI.2.2.2 (BF_convex hI) hbs hG hb
  obtain ⟨t, ht, hmem⟩ := relint_ext hri hb
  have h2 := foc D θ hI.2.2.1 hI.2.2.2 (BF_convex hI) hbs hG hmem
  rw [add_sub_cancel_left, smul_dotProduct, smul_eq_mul] at h2
  have h3 : (bs - b) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs))
      = -((b - bs) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs))) := by
    rw [← neg_sub, neg_dotProduct]
  rw [h3] at h2
  nlinarith

lemma sep_supergrad : Gf D θ bs + Vr D θ bs = score D wJ θ ↔ ∀ b ∈ BF D,
    Gf D θ b + Vr D θ b ≤ Gf D θ bs + Vr D θ bs + (0 : Fin K → ℝ) ⬝ᵥ (b - bs) := by
  rw [sep_iff θ hI hwJ hJ hbs hG]
  simp only [zero_dotProduct, add_zero]
  exact ⟨fun h b hb => h hb, fun h b hb => h b hb⟩

lemma sep_concave (hγ : 0 < D.gamma) (hri : bs ∈ intrinsicInterior ℝ (BF D))
    (hVc : ConcaveOn ℝ (BF D) (Vr D θ)) :
    Gf D θ bs + Vr D θ bs = score D wJ θ ↔ ∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs := by
  refine ⟨fun h b hb => ?_, sep_sup θ hI hwJ hJ hbs hG⟩
  have hmax := (sep_iff θ hI hwJ hJ hbs hG).mp h
  have hg0 := tangent_zero θ hI hwJ hJ hbs hG hri b hb
  by_contra hlt; push Not at hlt
  set Δ := Vr D θ b - Vr D θ bs
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  set Q := sqN D (b - bs)
  have hQ : 0 ≤ Q := sqN_nonneg D hI.2.2.1 _
  set t := min 1 (Δ / (D.gamma * Q + 1))
  have ht0 : 0 < t := lt_min one_pos (div_pos hΔ (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htg : t * (D.gamma * Q + 1) ≤ Δ := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  have hmem : bs + t • (b - bs) ∈ BF D := (BF_convex hI).add_smul_sub_mem hbs hb ⟨ht0.le, ht1⟩
  have hcomb : (1 - t) • bs + t • b = bs + t • (b - bs) := by
    funext k; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hV := hVc.2 hbs hb (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
  rw [hcomb] at hV
  simp only [smul_eq_mul] at hV
  have hGt := G_seg D θ bs (b - bs) t
  rw [hg0, mul_zero, add_zero] at hGt
  have := hmax hmem
  simp only [Set.mem_ofPred_eq] at this
  nlinarith [mul_nonneg (mul_nonneg ht0.le ht0.le) (mul_nonneg hγ.le hQ)]

lemma lossBound :
    score D wJ θ - (Gf D θ bs + Vr D θ bs)
      ≤ Vr D θ (exposure D wJ) - Vr D θ bs - D.gamma / 2 * sqN D (exposure D wJ - bs) ∧
    ∀ L : ℝ, (∀ b ∈ BF D, ∀ b' ∈ BF D, |Vr D θ b - Vr D θ b'| ≤ L * Real.sqrt (sqN D (b - b'))) →
      0 < D.gamma →
      score D wJ θ - (Gf D θ bs + Vr D θ bs)
        ≤ min (L ^ 2 / (2 * D.gamma)) (L * Real.sqrt (sqN D (exposure D wJ - bs))) := by
  have hbJ : exposure D wJ ∈ BF D := ⟨wJ, hwJ, rfl⟩
  have hf := foc D θ hI.2.2.1 hI.2.2.2 (BF_convex hI) hbs hG hbJ
  have hexp := G_expand D θ (exposure D wJ) bs
  obtain ⟨hid, -, -, -⟩ := lossIdentity θ hI hwJ hJ hbs hG
  have h1 : score D wJ θ - (Gf D θ bs + Vr D θ bs)
      ≤ Vr D θ (exposure D wJ) - Vr D θ bs - D.gamma / 2 * sqN D (exposure D wJ - bs) := by
    rw [hid]; linarith
  refine ⟨h1, fun L hL hγ => ?_⟩
  set x := Real.sqrt (sqN D (exposure D wJ - bs))
  have hQ := sqN_nonneg D hI.2.2.1 (exposure D wJ - bs)
  have hx2 : x ^ 2 = sqN D (exposure D wJ - bs) := Real.sq_sqrt hQ
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hLip := (abs_le.mp (hL _ hbJ _ hbs)).2
  rw [← hx2] at h1
  refine le_min ?_ (by nlinarith [mul_nonneg hγ.le (sq_nonneg x)])
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (L - D.gamma * x)]

end Parts

theorem targetsThm : Targets := fun _ _ _ _ _ _ θ hI => targets θ hI

theorem lossIdentityThm : LossIdentity := fun _ _ _ _ _ _ θ hI _ hwJ hJ _ hbs hG =>
  lossIdentity θ hI hwJ hJ hbs hG

theorem exactSeparation : ExactSeparation := fun _ _ _ _ _ _ θ hI _ hwJ hJ _ hbs hG =>
  ⟨sep_iff θ hI hwJ hJ hbs hG, sep_supergrad θ hI hwJ hJ hbs hG, sep_const θ hI hwJ hJ hbs hG,
    sep_sup θ hI hwJ hJ hbs hG, fun hri => ⟨tangent_zero θ hI hwJ hJ hbs hG hri,
      fun hVc _ hγ => sep_concave θ hI hwJ hJ hbs hG hγ hri hVc⟩,
    fun _ _ hint => grad_zero θ hI hwJ hJ hbs hG hint⟩

theorem lossBoundThm : LossBound := fun _ _ _ _ _ _ θ hI _ hwJ hJ _ hbs hG =>
  lossBound θ hI hwJ hJ hbs hG

/-! ### Part 4 -/

/-- Under the flat-case hypotheses `H` depends on the active position alone. -/
lemma H_flat (D : Data m n K S) (θ : Params m K) (hzE : ∀ s, D.zE s = 0) (hcE : D.cE = 0)
    (hk : ∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) {w : Inst m n → ℝ}
    (hC : crossM D w = 0) : Hr D θ w = hA D θ (active w) := by
  have hr : ∀ s, rres D w s = active w ⬝ᵥ D.zA s := fun s => by simp [rres, hzE]
  have ht : tau D (w - w0 D) = ∑ i, (D.kplus (Sum.inl i) * max (active w i - active (w0 D) i) 0
      + D.kminus (Sum.inl i) * max (-(active w i - active (w0 D) i)) 0) := by
    simp [tau, Fintype.sum_sum_type, hk, active]
  simp only [Hr, hA, hC, dotProduct_zero, mul_zero, zero_add, hcE, resM, hr, ht]
  ring

theorem flatCase : FlatCase := by
  refine ⟨fun _ _ _ _ _ D θ hI hzE hcE hk hC aH haH hmax hfib => ?_, fun _ _ _ _ D hβ w w' h => ?_⟩
  · have hV : ∀ b ∈ BF D, Vr D θ b = hA D θ aH := fun b hb => by
      obtain ⟨v, hv, -, hVv⟩ := V_attain θ hI hb
      obtain ⟨w, hw, hwa⟩ := hfib b hb
      have hle := H_le_V θ hI hw
      rw [H_flat D θ hzE hcE hk (hC w hw.1), hwa] at hle
      rw [hVv, H_flat D θ hzE hcE hk (hC v hv.1)] at hle ⊢
      exact le_antisymm (hmax _ fun i => hv.1.1 (Sum.inl i)) hle
    exact ⟨hV, fun wJ hwJ hJ bs hbs hG => sep_const θ hI hwJ hJ hbs hG ⟨_, hV⟩⟩
  · have key : ∀ k, D.BA 0 k * (active w 0 - active w' 0)
        = (D.BEᵀ *ᵥ (etf w' - etf w)) k := fun k => by
      have := congrFun h k
      simp only [exposure, Pi.add_apply, mulVec, dotProduct, Fin.sum_univ_one, transpose_apply,
        Pi.sub_apply, mul_sub, sum_sub_distrib] at this ⊢
      linarith
    have h0 : active w 0 = active w' 0 := by
      by_contra hne
      have hd : active w 0 - active w' 0 ≠ 0 := sub_ne_zero.mpr hne
      apply hβ ((active w 0 - active w' 0)⁻¹ • (etf w' - etf w))
      funext k
      rw [mulVec_smul, Pi.smul_apply, ← key k, smul_eq_mul]
      field_simp
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact h0

/-- Claim 027, parts 0-4. -/
theorem proof : Standalone.M2TwoStageSeparation.statement :=
  ⟨splitThm, targetsThm, lossIdentityThm, exactSeparation, lossBoundThm, flatCase⟩

end Novel.M2TwoStageSeparationProof

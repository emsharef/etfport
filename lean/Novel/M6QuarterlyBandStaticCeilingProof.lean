import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Standalone.M6QuarterlyBandStaticCeiling

/-!
# Proof of claim 029: quarterly no-trade bands around a moving target

No other claim's proof module is used (`depends_on: []`).

* **The recursion.** For `t < T`, `V_t(x) = min_{x' ∈ X} [C(x' - x) + G_t(x')]`, and `V_t = 0` for
  `t ≥ T`. By backward induction every `V_t` is convex and continuous on all holdings. `G_t` is the
  strictly convex tracking loss plus a convex continuation, and `V_t` is a partial minimum of a
  jointly convex continuous function over the compact convex box.
* **One instrument.** A one-dimensional convex toolkit on Mathlib's one-sided derivatives. `lo`
  minimizes `G + κ⁺x` and `hi` minimizes `G - κ⁻x` over `[0, x̄]`, which gives optimality of the
  projection onto `[lo, hi]` from every pre-trade holding and the three affine or `G` pieces of
  `V_t`. With `G_t = (c/2)(x - x*)² + φ` and `φ` convex, the one-sided derivatives of `G_t` split
  and those of `φ` are sums over outcomes by the chain rule. That gives the ceiling, the brackets,
  the coarse-regime band (where `φ` is differentiable across the band) and the equality
  characterization (with strict convexity of `G_{t+1}` between the next review's edges).
* **Many instruments.** The `Σ`-diameter inequality compares a no-trade holding with the feasible
  point `x + s(y - x)`, uses strong convexity of `G_t` with modulus `γΣ` and lets `s → 0`, with no
  subdifferential calculus. The static shape at `T - 1` uses coordinate perturbations for necessity
  and a direct comparison for sufficiency.
-/

namespace Novel.M6QuarterlyBandStaticCeilingProof

open Matrix Finset Standalone.M6QuarterlyBandStaticCeiling
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {n : ℕ} {Z Ω : Type} [Fintype Ω] {P : M6 n Z Ω}

/-! ### The recursion -/

lemma V_ge (P : M6 n Z Ω) {t : ℕ} (ht : P.T ≤ t) (z : Z) (x : Fin n → ℝ) : V P t z x = 0 := by
  simp [V, Nat.sub_eq_zero_of_le ht, Vk]

lemma V_lt (P : M6 n Z Ω) {t : ℕ} (ht : t < P.T) (z : Z) (x : Fin n → ℝ) :
    V P t z x = sInf ((fun x' => cost P (x' - x) + G P t z x') '' box P) := by
  have h1 : P.T - t = (P.T - (t + 1)) + 1 := by omega
  have h2 : P.T - (P.T - (t + 1) + 1) = t := by omega
  rw [V, h1]
  simp only [Vk, h2]
  rfl

/-! ### Cost, box, tracking and marking -/

lemma cost_nonneg (hS : Setting P) (u : Fin n → ℝ) : 0 ≤ cost P u :=
  sum_nonneg fun i _ => add_nonneg
    (mul_nonneg (hS.2.2.2.2.2.2.1 i).1 (le_max_right _ _))
    (mul_nonneg (hS.2.2.2.2.2.2.1 i).2.2.1 (le_max_right _ _))

lemma cost_zero (P : M6 n Z Ω) : cost P 0 = 0 := by simp [cost]

lemma max_smul0 {s : ℝ} (hs : 0 ≤ s) (a : ℝ) : max (s * a) 0 = s * max a 0 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left (mul_nonneg hs h), max_eq_left h]
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hs h), max_eq_right h, mul_zero]

lemma cost_smul (P : M6 n Z Ω) {s : ℝ} (hs : 0 ≤ s) (u : Fin n → ℝ) :
    cost P (s • u) = s * cost P u := by
  simp only [cost, mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_neg]
  rw [max_smul0 hs, max_smul0 hs]
  ring

lemma cost_pm (P : M6 n Z Ω) (u : Fin n → ℝ) :
    cost P u + cost P (-u) = ∑ i, (P.kp i + P.km i) * |u i| := by
  simp only [cost, ← sum_add_distrib, Pi.neg_apply, neg_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (u i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -u i ≤ 0), abs_of_nonneg h]; ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -u i), abs_of_nonpos h]; ring

lemma max_convex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y z : ℝ) :
    max (a * y + b * z) 0 ≤ a * max y 0 + b * max z 0 :=
  max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
    (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))

lemma cost_convex (hS : Setting P) : ConvexOn ℝ Set.univ (cost P) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
  simp only [cost, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have hk := hS.2.2.2.2.2.2.1 i
  have h1 := max_convex ha hb (u i) (v i)
  have h2 := max_convex ha hb (-u i) (-v i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [show -(a * u i + b * v i) = a * -u i + b * -v i by ring]
  nlinarith [mul_le_mul_of_nonneg_left h1 hk.1, mul_le_mul_of_nonneg_left h2 hk.2.2.1]

lemma continuous_cost (P : M6 n Z Ω) : Continuous (cost P) := by
  unfold cost; fun_prop

lemma box_compact (P : M6 n Z Ω) : IsCompact (box P) := by
  have : box P = Set.Icc 0 P.cap := by
    ext x; simp [box, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this]; exact isCompact_Icc

lemma box_convex (P : M6 n Z Ω) : Convex ℝ (box P) := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith [(hx i).1, (hy i).1]
  · have hc : P.cap i = a * P.cap i + b * P.cap i := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hx i).2 ha, mul_le_mul_of_nonneg_left (hy i).2 hb]

lemma zero_mem_box (hS : Setting P) : (0 : Fin n → ℝ) ∈ box P :=
  fun i => ⟨le_rfl, (hS.2.2.2.2.2.2.2.1 i).le⟩

/-- The quadratic form along a segment. -/
lemma quad_seg (hS : Setting P) (t : ℕ) (z : Z) (x y : Fin n → ℝ) (s : ℝ) :
    (x + s • (y - x)) ⬝ᵥ (P.Sigma t z *ᵥ (x + s • (y - x)))
      = (1 - s) * (x ⬝ᵥ (P.Sigma t z *ᵥ x)) + s * (y ⬝ᵥ (P.Sigma t z *ᵥ y))
        - s * (1 - s) * ((y - x) ⬝ᵥ (P.Sigma t z *ᵥ (y - x))) := by
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (P.Sigma t z *ᵥ v) = v ⬝ᵥ (P.Sigma t z *ᵥ u) := fun u v => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS.2.1 t z, dotProduct_comm]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsym y x]
  ring

lemma track_seg (hS : Setting P) (t : ℕ) (z : Z) (x y : Fin n → ℝ) (s : ℝ) :
    track P t z (x + s • (y - x)) = (1 - s) * track P t z x + s * track P t z y
      - P.gamma / 2 * (s * (1 - s)) * ((y - x) ⬝ᵥ (P.Sigma t z *ᵥ (y - x))) := by
  have e : x + s • (y - x) - xstar P t z
      = (x - xstar P t z) + s • ((y - xstar P t z) - (x - xstar P t z)) := by module
  have e2 : (y - xstar P t z) - (x - xstar P t z) = y - x := by abel
  simp only [track]
  rw [e, quad_seg hS t z, e2]
  ring

lemma quad_nonneg (hS : Setting P) (t : ℕ) (z : Z) (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (P.Sigma t z *ᵥ v) := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (hS.2.2.1 t z v hv).le

lemma track_strict (hS : Setting P) (t : ℕ) (z : Z) :
    StrictConvexOn ℝ Set.univ (track P t z) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hb' : a = 1 - b := by linarith
  subst hb'
  have e : (1 - b) • x + b • y = x + b • (y - x) := by module
  rw [e, track_seg hS]
  have hq := hS.2.2.1 t z (y - x) (sub_ne_zero.mpr (Ne.symm hxy))
  have hγ := hS.2.2.2.1
  simp only [smul_eq_mul]
  have : 0 < P.gamma / 2 * (b * (1 - b)) * ((y - x) ⬝ᵥ (P.Sigma t z *ᵥ (y - x))) := by
    apply mul_pos (mul_pos (by linarith) (mul_pos hb ha)) hq
  linarith

lemma continuous_track (P : M6 n Z Ω) (t : ℕ) (z : Z) : Continuous (track P t z) := by
  unfold track
  exact continuous_const.mul ((continuous_id.sub continuous_const).dotProduct
    (continuous_const.matrix_mulVec (continuous_id.sub continuous_const)))

lemma mark_comb (x y g : Fin n → ℝ) (a b : ℝ) :
    mark (a • x + b • y) g = a • mark x g + b • mark y g := by
  funext i; simp only [mark, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma continuous_mark (g : Fin n → ℝ) : Continuous (fun x : Fin n → ℝ => mark x g) := by
  unfold mark; fun_prop

/-! ### Backward induction: convexity and continuity -/

/-- The objective of the review-`t` minimization. -/
def Fobj (P : M6 n Z Ω) (t : ℕ) (z : Z) (x x' : Fin n → ℝ) : ℝ := cost P (x' - x) + G P t z x'

lemma isLeast_sInf {K : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {p : Fin n → ℝ} (hp : p ∈ K)
    (hmin : IsMinOn f K p) : sInf (f '' K) = f p :=
  (IsLeast.csInf_eq ⟨Set.mem_image_of_mem _ hp, by rintro _ ⟨q, hq, rfl⟩; exact hmin hq⟩)

/-- The continuation `β Σ q V_{t+1}(x ∘ g')`. -/
def cont (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : ℝ :=
  P.beta * ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark x (P.gross ω))

lemma G_eq (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : G P t z x = track P t z x + cont P t z x :=
  rfl

/-- Given convex continuous `V_{t+1}`, the continuation is convex and continuous. -/
lemma cont_props (hS : Setting P) (t : ℕ) (z : Z)
    (hV : ∀ z', ConvexOn ℝ Set.univ (V P (t + 1) z') ∧ Continuous (V P (t + 1) z')) :
    ConvexOn ℝ Set.univ (cont P t z) ∧ Continuous (cont P t z) := by
  have hβ := hS.2.2.2.2.1
  have hq := hS.2.2.2.2.2.2.2.2.1 t z
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_⟩
  · simp only [cont, smul_eq_mul, mark_comb]
    have hle : ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (a • mark x (P.gross ω) + b • mark y (P.gross ω))
        ≤ a * ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark x (P.gross ω))
          + b * ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark y (P.gross ω)) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun ω _ => ?_
      have h := (hV (P.next ω)).1.2 (Set.mem_univ (mark x (P.gross ω)))
        (Set.mem_univ (mark y (P.gross ω))) ha hb hab
      simp only [smul_eq_mul] at h
      nlinarith [mul_le_mul_of_nonneg_left h (hq ω)]
    nlinarith [mul_le_mul_of_nonneg_left hle hβ.le]
  · unfold cont
    exact continuous_const.mul (continuous_finsetSum _ fun ω _ =>
      continuous_const.mul ((hV (P.next ω)).2.comp (continuous_mark _)))

lemma G_props (hS : Setting P) (t : ℕ) (z : Z)
    (hV : ∀ z', ConvexOn ℝ Set.univ (V P (t + 1) z') ∧ Continuous (V P (t + 1) z')) :
    StrictConvexOn ℝ Set.univ (G P t z) ∧ ConvexOn ℝ Set.univ (fun x => G P t z x - track P t z x) ∧
      Continuous (G P t z) := by
  obtain ⟨hc1, hc2⟩ := cont_props hS t z hV
  have e : G P t z = fun x => track P t z x + cont P t z x := funext (G_eq P t z)
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; exact (track_strict hS t z).add_convexOn hc1
  · simp only [G_eq, add_sub_cancel_left]; exact hc1
  · rw [e]; exact (continuous_track P t z).add hc2

/-- The review-`t` objective is jointly continuous. -/
lemma Fobj_cont (hG : Continuous (G P t z)) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Fobj P t z p.1 p.2) := by
  unfold Fobj
  exact ((continuous_cost P).comp (continuous_snd.sub continuous_fst)).add (hG.comp continuous_snd)

/-- A minimizer of the review-`t` objective exists, and `V_t` is its value. -/
lemma V_attain (hS : Setting P) {t : ℕ} (ht : t < P.T) (z : Z) (hG : Continuous (G P t z))
    (x : Fin n → ℝ) : ∃ p ∈ box P, IsMinOn (Fobj P t z x) (box P) p ∧ V P t z x = Fobj P t z x p := by
  obtain ⟨p, hp, hmin⟩ := (box_compact P).exists_isMinOn ⟨0, zero_mem_box hS⟩
    (((continuous_cost P).comp (continuous_id.sub continuous_const)).add hG).continuousOn
  refine ⟨p, hp, hmin, ?_⟩
  rw [V_lt P ht]
  exact isLeast_sInf hp hmin

lemma V_le (hS : Setting P) {t : ℕ} (ht : t < P.T) (z : Z) (hG : Continuous (G P t z))
    (x : Fin n → ℝ) {p : Fin n → ℝ} (hp : p ∈ box P) : V P t z x ≤ Fobj P t z x p := by
  obtain ⟨q, hq, hmin, hV⟩ := V_attain hS ht z hG x
  rw [hV]; exact hmin hp

/-- Backward induction: every `V_t` is convex and continuous. -/
lemma V_props (hS : Setting P) : ∀ t z, ConvexOn ℝ Set.univ (V P t z) ∧ Continuous (V P t z) := by
  suffices h : ∀ k t, P.T - t = k → ∀ z, ConvexOn ℝ Set.univ (V P t z) ∧ Continuous (V P t z) from
    fun t z => h _ t rfl z
  intro k
  induction k with
  | zero =>
    intro t ht z
    have : V P t z = fun _ => 0 := funext fun x => V_ge P (by omega) z x
    rw [this]; exact ⟨convexOn_const 0 convex_univ, continuous_const⟩
  | succ k ih =>
    intro t ht z
    have htT : t < P.T := by omega
    have hV1 := ih (t + 1) (by omega)
    obtain ⟨-, -, hGc⟩ := G_props hS t z hV1
    obtain ⟨hGs, -, -⟩ := G_props hS t z hV1
    refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_⟩
    · obtain ⟨px, hpx, -, hVx⟩ := V_attain hS htT z hGc x
      obtain ⟨py, hpy, -, hVy⟩ := V_attain hS htT z hGc y
      have hmem : a • px + b • py ∈ box P := box_convex P hpx hpy ha hb hab
      have h1 := V_le hS htT z hGc (a • x + b • y) hmem
      have hc := (cost_convex hS).2 (Set.mem_univ (px - x)) (Set.mem_univ (py - y)) ha hb hab
      have hg := hGs.convexOn.2 (Set.mem_univ px) (Set.mem_univ py) ha hb hab
      have e : a • px + b • py - (a • x + b • y) = a • (px - x) + b • (py - y) := by module
      simp only [Fobj, e, smul_eq_mul] at h1 hVx hVy hc hg ⊢
      rw [hVx, hVy]
      linarith
    · have e : V P t z = fun x => sInf ((fun x' => Fobj P t z x x') '' box P) :=
        funext fun x => V_lt P htT z x
      rw [e]
      exact (box_compact P).continuous_sInf (Fobj_cont hGc)

/-! ### Part 2: many instruments -/

lemma G_facts (hS : Setting P) (t : ℕ) (z : Z) :
    StrictConvexOn ℝ Set.univ (G P t z) ∧ ConvexOn ℝ Set.univ (fun x => G P t z x - track P t z x) ∧
      Continuous (G P t z) :=
  G_props hS t z fun z' => V_props hS (t + 1) z'

lemma cont_convex (hS : Setting P) (t : ℕ) (z : Z) : ConvexOn ℝ Set.univ (cont P t z) :=
  (cont_props hS t z fun z' => V_props hS (t + 1) z').1

lemma cost_subadd (hS : Setting P) (u v : Fin n → ℝ) : cost P (u + v) ≤ cost P u + cost P v := by
  have h := (cost_convex hS).2 (Set.mem_univ u) (Set.mem_univ v)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • (u + v) := by module
  rw [e, cost_smul P (by norm_num)] at h
  simp only [smul_eq_mul] at h
  linarith

lemma isOpt_iff (P : M6 n Z Ω) (t : ℕ) (z : Z) (x x' : Fin n → ℝ) :
    IsOpt P t z x x' ↔ x' ∈ box P ∧ IsMinOn (Fobj P t z x) (box P) x' :=
  ⟨fun h => ⟨h.1, fun y hy => h.2 y hy⟩, fun h => ⟨h.1, fun _ hy => h.2 hy⟩⟩

lemma opt_unique (hS : Setting P) (t : ℕ) (z : Z) (x : Fin n → ℝ) {p q : Fin n → ℝ}
    (hp : IsOpt P t z x p) (hq : IsOpt P t z x q) : p = q := by
  by_contra hne
  have hs : StrictConvexOn ℝ Set.univ (Fobj P t z x) := by
    have hc : ConvexOn ℝ Set.univ (fun x' => cost P (x' - x)) := by
      refine ⟨convex_univ, fun a _ b _ u v hu hv huv => ?_⟩
      have e : u • a + v • b - x = u • (a - x) + v • (b - x) := by
        calc u • a + v • b - x = u • a + v • b - (u + v) • x := by rw [huv, one_smul]
          _ = _ := by module
      show cost P (u • a + v • b - x) ≤ u • cost P (a - x) + v • cost P (b - x)
      rw [e]; exact (cost_convex hS).2 (Set.mem_univ _) (Set.mem_univ _) hu hv huv
    exact hc.add_strictConvexOn (G_facts hS t z).1
  have hm := hs.2 (Set.mem_univ p) (Set.mem_univ q) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmem : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ box P :=
    box_convex P hp.1 hq.1 (by norm_num) (by norm_num) (by norm_num)
  have h1 := hp.2 _ hmem
  have h2 := hq.2 _ hmem
  simp only [Fobj, smul_eq_mul] at hm h1 h2
  linarith

lemma opt_exists (hS : Setting P) {t : ℕ} (ht : t < P.T) (z : Z) (x : Fin n → ℝ) :
    ∃ p, IsOpt P t z x p := by
  obtain ⟨p, hp, hmin, -⟩ := V_attain hS ht z (G_facts hS t z).2.2 x
  exact ⟨p, (isOpt_iff P t z x p).mpr ⟨hp, hmin⟩⟩

lemma opt_NT (hS : Setting P) (t : ℕ) (z : Z) {x p : Fin n → ℝ} (h : IsOpt P t z x p) :
    p ∈ NT P t z := by
  refine ⟨h.1, h.1, fun y hy => ?_⟩
  have h1 := h.2 y hy
  have h2 := cost_subadd hS (p - x) (y - p)
  rw [show p - x + (y - p) = y - x by abel] at h2
  rw [sub_self, cost_zero]
  linarith

theorem manyConvex : ManyConvex := by
  intro n Z Ω _ P hS t z ht
  obtain ⟨hGs, hGt, -⟩ := G_facts hS t z
  refine ⟨hGs.convexOn, hGt, (V_props hS t z).1, fun x => ?_, ?_, fun x x' h => opt_NT hS t z h⟩
  · obtain ⟨p, hp⟩ := opt_exists hS ht z x
    exact ⟨p, hp, fun q hq => opt_unique hS t z x hq hp⟩
  · obtain ⟨p, hp⟩ := opt_exists hS ht z 0
    exact ⟨p, opt_NT hS t z hp⟩

/-- One side of the diameter inequality: for `x ∈ NT` and `y ∈ X`,
`G(x) - G(y) ≤ C(y - x) - (γ/2)(y - x)'Σ(y - x)`. -/
lemma half_ineq (hS : Setting P) (t : ℕ) (z : Z) {x y : Fin n → ℝ} (hx : x ∈ NT P t z)
    (hy : y ∈ box P) :
    G P t z x - G P t z y
      ≤ cost P (y - x) - P.gamma / 2 * ((y - x) ⬝ᵥ (P.Sigma t z *ᵥ (y - x))) := by
  set Q := (y - x) ⬝ᵥ (P.Sigma t z *ᵥ (y - x))
  have hQ : 0 ≤ Q := quad_nonneg hS t z _
  have hγ := hS.2.2.2.1
  have hc := cost_nonneg hS (y - x)
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      G P t z x - G P t z y ≤ cost P (y - x) - P.gamma / 2 * (1 - s) * Q := by
    intro s hs0 hs1
    have hmem : x + s • (y - x) ∈ box P := by
      have := box_convex P hx.1 hy (by linarith : (0 : ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1; module
    have h1 := hx.2.2 _ hmem
    rw [sub_self, cost_zero, show x + s • (y - x) - x = s • (y - x) by abel,
      cost_smul P hs0.le] at h1
    have hcv := (cont_convex hS t z).2 (Set.mem_univ x) (Set.mem_univ y)
      (by linarith : (0 : ℝ) ≤ 1 - s) hs0.le (by ring)
    have e : (1 - s) • x + s • y = x + s • (y - x) := by module
    rw [e] at hcv
    simp only [smul_eq_mul] at hcv
    have htr := track_seg hS t z x y s
    simp only [G_eq] at h1 ⊢
    have h2 : s * (G P t z x - G P t z y) ≤ s * (cost P (y - x) - P.gamma / 2 * (1 - s) * Q) := by
      simp only [G_eq]; nlinarith
    exact le_of_mul_le_mul_left h2 hs0
  by_contra hlt
  push Not at hlt
  set gap := G P t z x - G P t z y - (cost P (y - x) - P.gamma / 2 * Q)
  have hgap : 0 < gap := by simp only [gap]; linarith
  set s := min 1 (gap / (P.gamma * Q + 1))
  have hs0 : 0 < s := lt_min one_pos (div_pos hgap (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsg : s * (P.gamma * Q + 1) ≤ gap := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  have hk := key s hs0 hs1
  have h3 : gap ≤ P.gamma / 2 * s * Q := by
    simp only [gap]
    linarith [show P.gamma / 2 * (1 - s) * Q = P.gamma / 2 * Q - P.gamma / 2 * s * Q by ring]
  have h4 : P.gamma / 2 * s * Q ≤ gap / 2 := by nlinarith
  linarith

lemma quad_neg (P : M6 n Z Ω) (t : ℕ) (z : Z) (v : Fin n → ℝ) :
    (-v) ⬝ᵥ (P.Sigma t z *ᵥ (-v)) = v ⬝ᵥ (P.Sigma t z *ᵥ v) := by
  simp [mulVec_neg]

theorem diameter : Diameter := by
  intro n Z Ω _ P hS t z ht x hx y hy
  have hγ := hS.2.2.2.1
  have hmain : P.gamma * ((x - y) ⬝ᵥ (P.Sigma t z *ᵥ (x - y))) ≤ ∑ i, (P.kp i + P.km i) * |x i - y i| := by
    have h1 := half_ineq hS t z hx hy.1
    have h2 := half_ineq hS t z hy hx.1
    have hpm := cost_pm P (x - y)
    rw [show -(x - y) = y - x by abel] at hpm
    rw [show x - y = -(y - x) by abel, quad_neg] at *
    have e : ∀ i, (P.kp i + P.km i) * |(-(y - x)) i| = (P.kp i + P.km i) * |x i - y i| := fun i => by
      simp only [Pi.neg_apply, Pi.sub_apply, neg_sub]
    simp only [e] at hpm ⊢
    linarith
  refine ⟨hmain, fun i w hw => ?_, fun lam K hlam hl hK => ?_⟩
  · have hSii : 0 < P.Sigma t z i i := by
      have := hS.2.2.1 t z (Pi.single i 1) (by simp)
      simpa [mulVec, dotProduct, Pi.single_apply] using this
    rw [hw] at hmain
    have hq : (Pi.single i w : Fin n → ℝ) ⬝ᵥ (P.Sigma t z *ᵥ Pi.single i w) = P.Sigma t z i i * w ^ 2 := by
      simp [mulVec, dotProduct, Pi.single_apply]; ring
    have hs : ∑ j, (P.kp j + P.km j) * |(Pi.single i w : Fin n → ℝ) j| = (P.kp i + P.km i) * |w| := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]; simp
    have hsub : ∀ j, x j - y j = (Pi.single i w : Fin n → ℝ) j := fun j => by rw [← hw]; rfl
    simp only [hsub, hs, hq] at hmain
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, abs_zero]; exact div_nonneg (by linarith [(hS.2.2.2.2.2.2.1 i).1,
        (hS.2.2.2.2.2.2.1 i).2.2.1]) (by positivity)
    · have hw0 : 0 < |w| := abs_pos.mpr h0
      rw [le_div_iff₀ (by positivity)]
      have : P.gamma * (P.Sigma t z i i * w ^ 2) = |w| * (|w| * (P.gamma * P.Sigma t z i i)) := by
        rw [← sq_abs]; ring
      rw [this] at hmain
      nlinarith
  · set d := x - y
    show Real.sqrt (∑ i, d i ^ 2) ≤ Real.sqrt n * K / (P.gamma * lam)
    have hQ := hl d
    have h1 : P.gamma * lam * ∑ i, d i ^ 2 ≤ K * ∑ i, |d i| := by
      calc P.gamma * lam * ∑ i, d i ^ 2 ≤ P.gamma * (d ⬝ᵥ (P.Sigma t z *ᵥ d)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hQ hγ.le
        _ ≤ ∑ i, (P.kp i + P.km i) * |x i - y i| := hmain
        _ ≤ ∑ i, K * |d i| := sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hK i) (abs_nonneg _)
        _ = K * ∑ i, |d i| := by rw [mul_sum]
    have hcs : ∑ i, |d i| ≤ Real.sqrt n * Real.sqrt (∑ i, d i ^ 2) := by
      have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1 : ℝ)) (fun i => |d i|)
      simpa [sq_abs] using this
    set r := Real.sqrt (∑ i, d i ^ 2)
    have hr : r ^ 2 = ∑ i, d i ^ 2 := Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    rcases eq_or_lt_of_le hr0 with h0 | hpos
    · rw [← h0]
      rcases isEmpty_or_nonempty (Fin n) with he | hne
      · have hn : n = 0 := by
          have h := (Fintype.card_eq_zero_iff (α := Fin n)).mpr he
          rwa [Fintype.card_fin] at h
        subst hn; simp
      · obtain ⟨i⟩ := hne
        have hK0 : 0 ≤ K := le_trans (by linarith [(hS.2.2.2.2.2.2.1 i).1,
          (hS.2.2.2.2.2.2.1 i).2.2.1]) (hK i)
        positivity
    · rw [le_div_iff₀ (by positivity)]
      have hK0 : 0 ≤ K := by
        by_contra hK0; push Not at hK0
        have : P.gamma * lam * r ^ 2 ≤ K * ∑ i, |d i| := by rw [hr]; exact h1
        have hs : 0 ≤ ∑ i, |d i| := sum_nonneg fun i _ => abs_nonneg _
        nlinarith [mul_pos (mul_pos hγ hlam) (pow_pos hpos 2), mul_nonpos_of_nonpos_of_nonneg hK0.le hs]
      have h2 : P.gamma * lam * r ^ 2 ≤ K * (Real.sqrt n * r) := by
        rw [hr]; exact h1.trans (mul_le_mul_of_nonneg_left hcs hK0)
      have h3 : (r * (P.gamma * lam)) * r ≤ (Real.sqrt n * K) * r := by nlinarith
      exact le_of_mul_le_mul_right h3 hpos

/-! ### Part 2c: the static shape at the last review -/

lemma G_last (hS : Setting P) (z : Z) (x : Fin n → ℝ) :
    G P (P.T - 1) z x = track P (P.T - 1) z x := by
  have hT := hS.1
  simp only [G_eq, cont]
  rw [Finset.sum_eq_zero fun ω _ => by rw [V_ge P (by omega) _ _, mul_zero], mul_zero, add_zero]

/-- The gradient `γΣ(x - x*)`. -/
def grad (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : Fin n → ℝ :=
  P.gamma • (P.Sigma t z *ᵥ (x - xstar P t z))

lemma track_add (hS : Setting P) (t : ℕ) (z : Z) (x d : Fin n → ℝ) :
    track P t z (x + d) = track P t z x + d ⬝ᵥ grad P t z x
      + P.gamma / 2 * (d ⬝ᵥ (P.Sigma t z *ᵥ d)) := by
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (P.Sigma t z *ᵥ v) = v ⬝ᵥ (P.Sigma t z *ᵥ u) := fun u v => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hS.2.1 t z, dotProduct_comm]
  have e : x + d - xstar P t z = (x - xstar P t z) + d := by abel
  simp only [track, grad, e, mulVec_add, dotProduct_add, add_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym d (x - xstar P t z)]
  ring

lemma cost_single (P : M6 n Z Ω) (i : Fin n) (e : ℝ) :
    cost P (Pi.single i e) = P.kp i * max e 0 + P.km i * max (-e) 0 := by
  unfold cost
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma quad_single (P : M6 n Z Ω) (t : ℕ) (z : Z) (i : Fin n) (e : ℝ) :
    (Pi.single i e : Fin n → ℝ) ⬝ᵥ (P.Sigma t z *ᵥ Pi.single i e) = P.Sigma t z i i * e ^ 2 := by
  simp [mulVec, dotProduct, Pi.single_apply]; ring

lemma diag_pos (hS : Setting P) (t : ℕ) (z : Z) (i : Fin n) : 0 < P.Sigma t z i i := by
  have := hS.2.2.1 t z (Pi.single i 1) (by simp)
  simpa [quad_single] using this

/-- A small step that would lower `a ε + b ε²` below zero exists when `a < 0`. -/
lemma small_step {a b c : ℝ} (ha : a < 0) (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ e, 0 < e ∧ e ≤ c ∧ e * a + b * e ^ 2 < 0 := by
  refine ⟨min c (-a / (2 * b + 1)), lt_min hc (div_pos (by linarith) (by positivity)),
    min_le_left _ _, ?_⟩
  set e := min c (-a / (2 * b + 1))
  have he : 0 < e := lt_min hc (div_pos (by linarith) (by positivity))
  have h1 : e * (2 * b + 1) ≤ -a := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  nlinarith

lemma nt_plus (hS : Setting P) (z : Z) {x : Fin n → ℝ} (hx : x ∈ NT P (P.T - 1) z) (i : Fin n)
    (hi : x i < P.cap i) : -P.kp i ≤ grad P (P.T - 1) z x i := by
  by_contra hlt; push Not at hlt
  have hb : 0 ≤ P.gamma / 2 * P.Sigma (P.T - 1) z i i := by
    have := diag_pos hS (P.T - 1) z i; have := hS.2.2.2.1; positivity
  obtain ⟨e, he0, hec, hneg⟩ := small_step (a := P.kp i + grad P (P.T - 1) z x i)
    (by linarith) hb (by linarith : 0 < P.cap i - x i)
  have hmem : x + Pi.single i e ∈ box P := fun j => by
    by_cases hj : j = i
    · subst hj; simp; constructor <;> linarith [(hx.1 j).1]
    · simp [hj]; exact hx.1 j
  have h := hx.2.2 _ hmem
  rw [sub_self, cost_zero, add_sub_cancel_left, cost_single, G_last hS, G_last hS, track_add hS,
    quad_single] at h
  rw [max_eq_left he0.le, max_eq_right (by linarith : -e ≤ 0)] at h
  have hdot : (Pi.single i e : Fin n → ℝ) ⬝ᵥ grad P (P.T - 1) z x = e * grad P (P.T - 1) z x i := by
    simp [single_dotProduct]
  rw [hdot] at h
  nlinarith

lemma nt_minus (hS : Setting P) (z : Z) {x : Fin n → ℝ} (hx : x ∈ NT P (P.T - 1) z) (i : Fin n)
    (hi : 0 < x i) : grad P (P.T - 1) z x i ≤ P.km i := by
  by_contra hlt; push Not at hlt
  have hb : 0 ≤ P.gamma / 2 * P.Sigma (P.T - 1) z i i := by
    have := diag_pos hS (P.T - 1) z i; have := hS.2.2.2.1; positivity
  obtain ⟨e, he0, hec, hneg⟩ := small_step (a := P.km i - grad P (P.T - 1) z x i)
    (by linarith) hb hi
  have hmem : x + Pi.single i (-e) ∈ box P := fun j => by
    by_cases hj : j = i
    · subst hj; simp; constructor <;> linarith [(hx.1 j).2]
    · simp [hj]; exact hx.1 j
  have h := hx.2.2 _ hmem
  rw [sub_self, cost_zero, add_sub_cancel_left, cost_single, G_last hS, G_last hS, track_add hS,
    quad_single] at h
  rw [max_eq_right (by linarith : -e ≤ 0), neg_neg, max_eq_left he0.le] at h
  have hdot : (Pi.single i (-e) : Fin n → ℝ) ⬝ᵥ grad P (P.T - 1) z x
      = -e * grad P (P.T - 1) z x i := by
    simp [single_dotProduct]
  rw [hdot] at h
  nlinarith

lemma nt_suff (hS : Setting P) (z : Z) {x : Fin n → ℝ} (hx : x ∈ box P)
    (hc : ∀ i, (0 < x i → x i < P.cap i → -P.kp i ≤ grad P (P.T - 1) z x i ∧
        grad P (P.T - 1) z x i ≤ P.km i) ∧
      (x i = 0 → -P.kp i ≤ grad P (P.T - 1) z x i) ∧
      (x i = P.cap i → grad P (P.T - 1) z x i ≤ P.km i)) :
    x ∈ NT P (P.T - 1) z := by
  refine ⟨hx, hx, fun y hy => ?_⟩
  rw [sub_self, cost_zero, zero_add, G_last hS, G_last hS]
  have e : y = x + (y - x) := by abel
  rw [e, track_add hS, ← e]
  have hQ := quad_nonneg hS (P.T - 1) z (y - x)
  have hγ := hS.2.2.2.1
  have hsum : 0 ≤ cost P (y - x) + (y - x) ⬝ᵥ grad P (P.T - 1) z x := by
    simp only [cost, dotProduct, ← sum_add_distrib]
    refine sum_nonneg fun i _ => ?_
    have hk := hS.2.2.2.2.2.2.1 i
    have hcap := hS.2.2.2.2.2.2.2.1 i
    obtain ⟨h1, h2, h3⟩ := hc i
    simp only [Pi.sub_apply]
    rcases lt_trichotomy (y i - x i) 0 with hd | hd | hd
    · have hxpos : 0 < x i := by linarith [(hy i).1]
      have hg : grad P (P.T - 1) z x i ≤ P.km i := by
        rcases lt_or_eq_of_le (hx i).2 with hlt | heq
        · exact (h1 hxpos hlt).2
        · exact h3 heq
      rw [max_eq_right hd.le, max_eq_left (by linarith)]
      nlinarith
    · rw [hd]; simp
    · have hxlt : x i < P.cap i := by linarith [(hy i).2]
      have hg : -P.kp i ≤ grad P (P.T - 1) z x i := by
        rcases lt_or_eq_of_le (hx i).1 with hlt | heq
        · exact (h1 hlt hxlt).1
        · exact h2 heq.symm
      rw [max_eq_left hd.le, max_eq_right (by linarith)]
      nlinarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P.gamma / 2) hQ]

theorem staticShape : StaticShape := by
  intro n Z Ω _ P hS z
  have hg : ∀ x, P.gamma • (P.Sigma (P.T - 1) z *ᵥ (x - xstar P (P.T - 1) z)) =
      grad P (P.T - 1) z x :=
    fun x => rfl
  have hchar : ∀ x, x ∈ NT P (P.T - 1) z ↔ x ∈ box P ∧ ∀ i,
      (0 < x i → x i < P.cap i → -P.kp i ≤ grad P (P.T - 1) z x i ∧ grad P (P.T - 1) z x i ≤ P.km i) ∧
      (x i = 0 → -P.kp i ≤ grad P (P.T - 1) z x i) ∧
      (x i = P.cap i → grad P (P.T - 1) z x i ≤ P.km i) := by
    intro x
    refine ⟨fun hx => ⟨hx.1, fun i => ⟨fun h0 hc => ⟨nt_plus hS z hx i hc, nt_minus hS z hx i h0⟩,
      fun h0 => nt_plus hS z hx i (by rw [h0]; exact hS.2.2.2.2.2.2.2.1 i),
      fun hc => nt_minus hS z hx i (by rw [hc]; exact hS.2.2.2.2.2.2.2.1 i)⟩⟩,
      fun h => nt_suff hS z h.1 h.2⟩
  refine ⟨fun x => by simpa only [hg] using hchar x, fun x hint => ?_, fun d A => ?_⟩
  · simp only [hg]
    rw [hchar x]
    constructor
    · rintro ⟨-, h⟩ i; exact (h i).1 (hint i).1 (hint i).2
    · intro h
      refine ⟨fun i => ⟨(hint i).1.le, (hint i).2.le⟩, fun i => ⟨fun _ _ => h i, fun h0 => ?_, fun hc => ?_⟩⟩
      · exact absurd h0 (hint i).1.ne'
      · exact absurd hc (hint i).2.ne
  · have hA := diag_pos hS (P.T - 1) z A
    have hγ := hS.2.2.2.1
    have hsplit : (P.Sigma (P.T - 1) z *ᵥ d) A = P.Sigma (P.T - 1) z A A * d A + ∑ j, if j = A then 0 else P.Sigma (P.T - 1) z A j * d j := by
      simp only [mulVec, dotProduct]
      rw [← Finset.add_sum_erase _ _ (mem_univ A)]
      congr 1
      rw [← Finset.sum_erase_add _ _ (mem_univ A)]
      simp only [↓reduceIte, add_zero]
      exact Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    set R := ∑ j, if j = A then 0 else P.Sigma (P.T - 1) z A j * d j
    have hgS : 0 < P.gamma * P.Sigma (P.T - 1) z A A := mul_pos hγ hA
    have e : d A + R / P.Sigma (P.T - 1) z A A = (P.gamma * (P.Sigma (P.T - 1) z *ᵥ d) A) / (P.gamma * P.Sigma (P.T - 1) z A A) := by
      rw [hsplit]; field_simp
    rw [e, div_le_div_iff_of_pos_right hgS, div_le_div_iff_of_pos_right hgS]

/-! ### One-dimensional convex analysis -/

section Conv1

variable {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
include hf

omit [Fintype Ω] in
lemma hasRd (x : ℝ) : HasDerivWithinAt f (rd f x) (Set.Ioi x) x :=
  hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

omit [Fintype Ω] in
lemma hasLd (x : ℝ) : HasDerivWithinAt f (ld f x) (Set.Iio x) x :=
  hf.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)

omit [Fintype Ω] in
lemma rd_le_slope {x y : ℝ} (hxy : x < y) : rd f x * (y - x) ≤ f y - f x := by
  have h := hf.rightDeriv_le_slope_of_mem_interior (by simp : x ∈ interior Set.univ)
    (Set.mem_univ y) hxy
  rw [slope_def_field, le_div_iff₀ (by linarith)] at h
  exact h

omit [Fintype Ω] in
lemma slope_le_ld {x y : ℝ} (hxy : x < y) : f y - f x ≤ ld f y * (y - x) := by
  have h := hf.slope_le_leftDeriv_of_mem_interior (Set.mem_univ x) (by simp : y ∈ interior Set.univ) hxy
  rw [slope_def_field, div_le_iff₀ (by linarith)] at h
  exact h

omit [Fintype Ω] in
lemma ld_le_rd (x : ℝ) : ld f x ≤ rd f x :=
  hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

omit [Fintype Ω] in
lemma rd_le_ld {x y : ℝ} (hxy : x < y) : rd f x ≤ ld f y := by
  have h1 := rd_le_slope hf hxy
  have h2 := slope_le_ld hf hxy
  have : rd f x * (y - x) ≤ ld f y * (y - x) := h1.trans h2
  exact le_of_mul_le_mul_right this (by linarith)

omit [Fintype Ω] in
lemma rd_mono {x y : ℝ} (hxy : x ≤ y) : rd f x ≤ rd f y := by
  rcases eq_or_lt_of_le hxy with rfl | h
  · rfl
  · exact (rd_le_ld hf h).trans (ld_le_rd hf y)

omit [Fintype Ω] in
lemma ld_mono {x y : ℝ} (hxy : x ≤ y) : ld f x ≤ ld f y := by
  rcases eq_or_lt_of_le hxy with rfl | h
  · rfl
  · exact (ld_le_rd hf x).trans (rd_le_ld hf h)

omit [Fintype Ω] in
omit hf in
/-- If `A ≤ B + |K| δ` for every small `δ > 0`, then `A ≤ B`. -/
lemma le_of_small {A B K δ0 : ℝ} (hδ0 : 0 < δ0) (h : ∀ δ, 0 < δ → δ < δ0 → A ≤ B + |K| * δ) :
    A ≤ B := by
  by_contra hlt; push Not at hlt
  set δ := min (δ0 / 2) ((A - B) / (2 * (|K| + 1)))
  have hd : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hd1 : δ < δ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd2 : δ * (2 * (|K| + 1)) ≤ A - B := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  have := h δ hd hd1
  nlinarith [abs_nonneg K]

omit [Fintype Ω] in
/-- Right-continuity from the right: a lower bound on `rd f` just right of `x` holds at `x`. -/
lemma rd_of_right {x b m : ℝ} (hxb : x < b) (h : ∀ u, x < u → u < b → m ≤ rd f u) : m ≤ rd f x := by
  rw [rd, hf.rightDeriv_eq_sInf_slope_of_mem_interior (by simp)]
  refine le_csInf ⟨_, (x + 1), ⟨Set.mem_univ _, by linarith⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨-, hxy⟩, rfl⟩
  rw [slope_def_field, le_div_iff₀ (by linarith)]
  refine le_of_small (K := m - rd f x) (δ0 := min (b - x) (y - x)) (lt_min (by linarith) (by linarith))
    fun δ hδ hδ0 => ?_
  have hδb : δ < b - x := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hδy : δ < y - x := lt_of_lt_of_le hδ0 (min_le_right _ _)
  have hu1 := h (x + δ) (by linarith) (by linarith)
  have h1 := rd_le_slope hf (show x < x + δ by linarith)
  have h2 := rd_le_slope hf (show x + δ < y by linarith)
  rw [show x + δ - x = δ by ring] at h1
  have hab : m - rd f x ≤ |m - rd f x| := le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_right hu1 (by linarith : (0 : ℝ) ≤ y - (x + δ))]

omit [Fintype Ω] in
/-- Left-continuity from the left: an upper bound on `ld f` just left of `x` holds at `x`. -/
lemma ld_of_left {x a m : ℝ} (hax : a < x) (h : ∀ u, a < u → u < x → ld f u ≤ m) : ld f x ≤ m := by
  rw [ld, hf.leftDeriv_eq_sSup_slope_of_mem_interior (by simp)]
  refine csSup_le ⟨_, (x - 1), ⟨Set.mem_univ _, by linarith⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨-, hyx⟩, rfl⟩
  rw [slope_def_field, div_le_iff_of_neg (by linarith)]
  -- `m (y - x) ≤ f y - f x`, i.e. `f x - f y ≤ m (x - y)`
  have key : f x - f y ≤ m * (x - y) := by
    refine le_of_small (K := ld f x - m) (δ0 := min (x - a) (x - y)) (lt_min (by linarith) (by linarith))
      fun δ hδ hδ0 => ?_
    have hδa : δ < x - a := lt_of_lt_of_le hδ0 (min_le_left _ _)
    have hδy : δ < x - y := lt_of_lt_of_le hδ0 (min_le_right _ _)
    have hu1 := h (x - δ) (by linarith) (by linarith)
    have h1 := slope_le_ld hf (show x - δ < x by linarith)
    have h2 := slope_le_ld hf (show y < x - δ by linarith)
    rw [show x - (x - δ) = δ by ring] at h1
    have hab : ld f x - m ≤ |ld f x - m| := le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_right hu1 (by linarith : (0 : ℝ) ≤ x - δ - y)]
  linarith

omit [Fintype Ω] in
/-- A convex function that is affine with slope `k` on `[x, x + δ)` has right derivative `k`. -/
lemma rd_affine {x δ k : ℝ} (hδ : 0 < δ) (h : ∀ y, x ≤ y → y < x + δ → f y = f x + k * (y - x)) :
    rd f x = k := by
  have hd : HasDerivWithinAt (fun y => f x + k * (y - x)) k (Set.Ioi x) x := by
    simpa using (((hasDerivAt_id x).sub_const x).const_mul k).const_add (f x) |>.hasDerivWithinAt
  have hd' : HasDerivWithinAt f k (Set.Ioi x) x := by
    refine hd.congr_of_eventuallyEq ?_ (by simp)
    filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with y hy
    exact h y hy.1.le hy.2
  exact hd'.derivWithin (uniqueDiffWithinAt_Ioi x)

omit [Fintype Ω] in
/-- A convex function that is affine with slope `k` on `(x - δ, x]` has left derivative `k`. -/
lemma ld_affine {x δ k : ℝ} (hδ : 0 < δ) (h : ∀ y, x - δ < y → y ≤ x → f y = f x + k * (y - x)) :
    ld f x = k := by
  have hd : HasDerivWithinAt (fun y => f x + k * (y - x)) k (Set.Iio x) x := by
    simpa using (((hasDerivAt_id x).sub_const x).const_mul k).const_add (f x) |>.hasDerivWithinAt
  have hd' : HasDerivWithinAt f k (Set.Iio x) x := by
    refine hd.congr_of_eventuallyEq ?_ (by simp)
    filter_upwards [Ioo_mem_nhdsLT (show x - δ < x by linarith)] with y hy
    exact h y hy.1 hy.2.le
  exact hd'.derivWithin (uniqueDiffWithinAt_Iio x)

omit [Fintype Ω] in
/-- A slope bound on the right bounds `rd f` above. -/
lemma rd_le_of {x M : ℝ} (h : ∀ y, x < y → f y - f x ≤ M * (y - x)) : rd f x ≤ M := by
  have h1 := rd_le_slope hf (show x < x + 1 by linarith)
  have h2 := h (x + 1) (by linarith)
  rw [show x + 1 - x = 1 by ring] at h1 h2
  linarith

omit [Fintype Ω] in
/-- A slope bound on the left bounds `ld f` below. -/
lemma ld_ge_of {x M : ℝ} (h : ∀ y, y < x → M * (x - y) ≤ f x - f y) : M ≤ ld f x := by
  have h1 := slope_le_ld hf (show x - 1 < x by linarith)
  have h2 := h (x - 1) (by linarith)
  rw [show x - (x - 1) = 1 by ring] at h1 h2
  linarith

omit [Fintype Ω] in
/-- A slope bound on the right bounds `rd f` below. -/
lemma rd_ge_of {x m : ℝ} (h : ∀ y, x < y → m * (y - x) ≤ f y - f x) : m ≤ rd f x := by
  rw [rd, hf.rightDeriv_eq_sInf_slope_of_mem_interior (by simp)]
  refine le_csInf ⟨_, (x + 1), ⟨Set.mem_univ _, by linarith⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨-, hxy⟩, rfl⟩
  rw [slope_def_field, le_div_iff₀ (by linarith)]
  exact h y hxy

omit [Fintype Ω] in
/-- Between a point and a point of no larger value, a convex function stays below the latter. -/
lemma le_right_of {m x y : ℝ} (hm : f m ≤ f y) (hmx : m ≤ x) (hxy : x ≤ y) : f x ≤ f y := by
  have h := hf.le_max_of_mem_segment (Set.mem_univ m) (Set.mem_univ y)
    (by rw [segment_eq_Icc (hmx.trans hxy)]; exact ⟨hmx, hxy⟩)
  exact h.trans (max_le hm le_rfl)

omit [Fintype Ω] in
lemma le_left_of {m x y : ℝ} (hm : f m ≤ f y) (hyx : y ≤ x) (hxm : x ≤ m) : f x ≤ f y := by
  have h := hf.le_max_of_mem_segment (Set.mem_univ y) (Set.mem_univ m)
    (by rw [segment_eq_Icc (hyx.trans hxm)]; exact ⟨hyx, hxm⟩)
  exact h.trans (max_le le_rfl hm)

omit [Fintype Ω] in
/-- The one-sided derivatives of `x ↦ f (x g)`, `g > 0`. -/
lemma hasRd_comp {g : ℝ} (hg : 0 < g) (x : ℝ) :
    HasDerivWithinAt (fun y => f (y * g)) (rd f (x * g) * g) (Set.Ioi x) x :=
  (hasRd hf (x * g)).comp x (hasDerivAt_mul_const g).hasDerivWithinAt
    fun y (hy : x < y) => show x * g < y * g from mul_lt_mul_of_pos_right hy hg

omit [Fintype Ω] in
lemma hasLd_comp {g : ℝ} (hg : 0 < g) (x : ℝ) :
    HasDerivWithinAt (fun y => f (y * g)) (ld f (x * g) * g) (Set.Iio x) x :=
  (hasLd hf (x * g)).comp x (hasDerivAt_mul_const g).hasDerivWithinAt
    fun y (hy : y < x) => show y * g < x * g from mul_lt_mul_of_pos_right hy hg

end Conv1

/-! ### Pure one-sided derivative facts -/

lemma rd_congr {f g : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ) (h : ∀ y, x ≤ y → y < x + δ → f y = g y) :
    rd f x = rd g x := by
  unfold rd
  refine Filter.EventuallyEq.derivWithin_eq ?_ (h x le_rfl (by linarith))
  filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with y hy
  exact h y hy.1.le hy.2

lemma ld_congr {f g : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ) (h : ∀ y, x - δ < y → y ≤ x → f y = g y) :
    ld f x = ld g x := by
  unfold ld
  refine Filter.EventuallyEq.derivWithin_eq ?_ (h x (by linarith) le_rfl)
  filter_upwards [Ioo_mem_nhdsLT (show x - δ < x by linarith)] with y hy
  exact h y hy.1 hy.2.le

lemma rd_of_deriv {f : ℝ → ℝ} {x d : ℝ} (h : HasDerivAt f d x) : rd f x = d :=
  h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

lemma ld_of_deriv {f : ℝ → ℝ} {x d : ℝ} (h : HasDerivAt f d x) : ld f x = d :=
  h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

lemma hasDerivAt_quad (c a x : ℝ) : HasDerivAt (fun y => c / 2 * (y - a) ^ 2) (c * (x - a)) x := by
  have h1 : HasDerivAt (fun y => y - a) 1 x := (hasDerivAt_id' x).sub_const a
  have h := (h1.mul h1).const_mul (c / 2)
  convert h using 1
  · funext y; simp only [Pi.mul_apply]; ring
  · ring

/-! ### One instrument: embedding -/

section OneInst

variable {P : M6 1 Z Ω}

/-- The constant holding. -/
def cst (x : ℝ) : Fin 1 → ℝ := fun _ => x

omit [Fintype Ω] in
lemma cst_comb (x y a b : ℝ) : a • cst x + b • cst y = cst (a * x + b * y) := by
  funext i; simp [cst]

omit [Fintype Ω] in
lemma cst_eta (v : Fin 1 → ℝ) : v = cst (v 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

omit [Fintype Ω] in
lemma mark_cst (x : ℝ) (g : Fin 1 → ℝ) : mark (cst x) g = cst (x * g 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

lemma G1_eq (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) : G1 P t z x = G P t z (cst x) := rfl

lemma V1_eq (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) : V1 P t z x = V P t z (cst x) := rfl

lemma track1 (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) :
    track P t z (cst x) = curv P t z / 2 * (x - xs P t z) ^ 2 := by
  simp only [track, curv, xs, dotProduct, mulVec, Fin.sum_univ_one, Pi.sub_apply, cst]
  ring

/-- The continuation on holdings in `ℝ`. -/
def phi1 (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) : ℝ :=
  P.beta * ∑ ω, P.prob t z ω * V1 P (t + 1) (P.next ω) (x * P.gross ω 0)

lemma G1_split (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) :
    G1 P t z x = curv P t z / 2 * (x - xs P t z) ^ 2 + phi1 P t z x := by
  simp only [G1_eq, G_eq, cont, track1, phi1, mark_cst, V1_eq]

lemma V1_convex (hS : Setting P) (t : ℕ) (z : Z) : ConvexOn ℝ Set.univ (V1 P t z) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := (V_props hS t z).1.2 (Set.mem_univ (cst x)) (Set.mem_univ (cst y)) ha hb hab
  simp only [cst_comb] at h
  exact h

lemma V1_cont (hS : Setting P) (t : ℕ) (z : Z) : Continuous (V1 P t z) :=
  (V_props hS t z).2.comp (continuous_pi fun _ => continuous_id)

lemma G1_strict (hS : Setting P) (t : ℕ) (z : Z) : StrictConvexOn ℝ Set.univ (G1 P t z) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hne : cst x ≠ cst y := fun h => hxy (congrFun h 0)
  have h := (G_facts hS t z).1.2 (Set.mem_univ (cst x)) (Set.mem_univ (cst y)) hne ha hb hab
  simp only [cst_comb] at h
  exact h

lemma G1_convex (hS : Setting P) (t : ℕ) (z : Z) : ConvexOn ℝ Set.univ (G1 P t z) :=
  (G1_strict hS t z).convexOn

lemma G1_cont (hS : Setting P) (t : ℕ) (z : Z) : Continuous (G1 P t z) :=
  (G_facts hS t z).2.2.comp (continuous_pi fun _ => continuous_id)

lemma phi1_convex (hS : Setting P) (t : ℕ) (z : Z) : ConvexOn ℝ Set.univ (phi1 P t z) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := (cont_convex hS t z).2 (Set.mem_univ (cst x)) (Set.mem_univ (cst y)) ha hb hab
  simp only [cst_comb, cont, mark_cst] at h
  simpa only [phi1, V1_eq, smul_eq_mul] using h

lemma cost1 (P : M6 1 Z Ω) (a : ℝ) : cost P (cst a) = P.kp 0 * max a 0 + P.km 0 * max (-a) 0 := by
  simp [cost, cst]

lemma cst_sub (a b : ℝ) : cst a - cst b = cst (a - b) := by funext i; simp [cst]

lemma mem_box1 (P : M6 1 Z Ω) (y : ℝ) : cst y ∈ box P ↔ 0 ≤ y ∧ y ≤ P.cap 0 := by
  constructor
  · intro h; exact h 0
  · intro h i; rw [Subsingleton.elim i 0]; exact h

/-! ### One instrument: the band edges -/

section Edges

variable (hS : Setting P) (t : ℕ) (z : Z)
include hS

lemma cap0 : 0 < P.cap 0 := hS.2.2.2.2.2.2.2.1 0

lemma kp0 : 0 ≤ P.kp 0 := (hS.2.2.2.2.2.2.1 0).1

lemma km0 : 0 ≤ P.km 0 := (hS.2.2.2.2.2.2.1 0).2.2.1

lemma lo_bounds : 0 ≤ lo P t z ∧ lo P t z ≤ P.cap 0 := by
  unfold lo
  split_ifs with hne
  · obtain ⟨x0, hx0⟩ := hne
    have hbdd : BddBelow {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} := ⟨0, fun x hx => hx.1⟩
    exact ⟨le_csInf ⟨x0, hx0⟩ fun x hx => hx.1, (csInf_le hbdd hx0).trans hx0.2.1.le⟩
  · exact ⟨(cap0 hS).le, le_rfl⟩

lemma hi_bounds : 0 ≤ hi P t z ∧ hi P t z ≤ P.cap 0 := by
  unfold hi
  split_ifs with hne
  · obtain ⟨x0, hx0⟩ := hne
    have hbdd : BddAbove {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} :=
      ⟨P.cap 0, fun x hx => hx.2.1⟩
    exact ⟨hx0.1.le.trans (le_csSup hbdd hx0), csSup_le ⟨x0, hx0⟩ fun x hx => hx.2.1⟩
  · exact ⟨le_rfl, (cap0 hS).le⟩

/-- Below `lo`, the right derivative of `G` is below `-κ⁺`. -/
lemma below_lo {x : ℝ} (hx0 : 0 ≤ x) (hx : x < lo P t z) : rd (G1 P t z) x < -P.kp 0 := by
  by_contra hge; push Not at hge
  have hxc : x < P.cap 0 := lt_of_lt_of_le hx (lo_bounds hS t z).2
  have hmem : x ∈ {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} := ⟨hx0, hxc, hge⟩
  have : lo P t z ≤ x := by
    unfold lo; rw [ite_eq_left ⟨x, hmem⟩]; exact csInf_le ⟨0, fun y hy => hy.1⟩ hmem
  linarith

/-- Above `hi` (within the cap), the left derivative of `G` is above `κ⁻`. -/
lemma above_hi {x : ℝ} (hxc : x ≤ P.cap 0) (hx : hi P t z < x) : P.km 0 < ld (G1 P t z) x := by
  by_contra hle; push Not at hle
  have hx0 : 0 < x := lt_of_le_of_lt (hi_bounds hS t z).1 hx
  have hmem : x ∈ {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} := ⟨hx0, hxc, hle⟩
  have : x ≤ hi P t z := by
    unfold hi; rw [ite_eq_left ⟨x, hmem⟩]; exact le_csSup ⟨P.cap 0, fun y hy => hy.2.1⟩ hmem
  linarith

lemma rd_lo (h : lo P t z < P.cap 0) : -P.kp 0 ≤ rd (G1 P t z) (lo P t z) := by
  have hne : ({x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} : Set ℝ).Nonempty := by
    by_contra hne; unfold lo at h; rw [ite_eq_right hne] at h; exact lt_irrefl _ h
  refine rd_of_right (G1_convex hS t z) h fun u hu _ => ?_
  have hlo : lo P t z = sInf {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} := by
    unfold lo; rw [ite_eq_left hne]
  rw [hlo] at hu
  obtain ⟨s0, hs0, hs0u⟩ := exists_lt_of_csInf_lt hne hu
  exact hs0.2.2.trans (rd_mono (G1_convex hS t z) hs0u.le)

lemma ld_lo (h : 0 < lo P t z) : ld (G1 P t z) (lo P t z) ≤ -P.kp 0 :=
  ld_of_left (G1_convex hS t z) h fun u hu hul =>
    ((ld_le_rd (G1_convex hS t z) u).trans (below_lo hS t z hu.le hul).le)

lemma ld_hi (h : 0 < hi P t z) : ld (G1 P t z) (hi P t z) ≤ P.km 0 := by
  have hne : ({x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} : Set ℝ).Nonempty := by
    by_contra hne; unfold hi at h; rw [ite_eq_right hne] at h; exact lt_irrefl _ h
  refine ld_of_left (G1_convex hS t z) h fun u _ hu => ?_
  have hhi : hi P t z = sSup {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} := by
    unfold hi; rw [ite_eq_left hne]
  rw [hhi] at hu
  obtain ⟨s0, hs0, hus0⟩ := exists_lt_of_lt_csSup hne hu
  exact (ld_mono (G1_convex hS t z) hus0.le).trans hs0.2.2

lemma rd_hi (h : hi P t z < P.cap 0) : P.km 0 ≤ rd (G1 P t z) (hi P t z) :=
  rd_of_right (G1_convex hS t z) h fun u hu huc =>
    ((above_hi hS t z huc.le hu).le.trans (ld_le_rd (G1_convex hS t z) u))

lemma lo_le_hi : lo P t z ≤ hi P t z := by
  by_contra hlt; push Not at hlt
  obtain ⟨x, hx1, hx2⟩ := exists_between hlt
  have hx0 : 0 ≤ x := (hi_bounds hS t z).1.trans hx1.le
  have hxc : x ≤ P.cap 0 := hx2.le.trans (lo_bounds hS t z).2
  have h1 := below_lo hS t z hx0 hx2
  have h2 := above_hi hS t z hxc hx1
  have h3 := ld_le_rd (G1_convex hS t z) x
  linarith [kp0 hS, km0 hS]

/-- `lo` minimizes `G + κ⁺ x` over `[0, x̄]`. -/
lemma lo_min {y : ℝ} (hy0 : 0 ≤ y) (hyc : y ≤ P.cap 0) :
    G1 P t z (lo P t z) + P.kp 0 * lo P t z ≤ G1 P t z y + P.kp 0 * y := by
  have hc := G1_convex hS t z
  rcases lt_trichotomy y (lo P t z) with h | h | h
  · have h1 := slope_le_ld hc h
    have h2 := mul_le_mul_of_nonneg_right (ld_lo hS t z (lt_of_le_of_lt hy0 h)) (by linarith : (0 : ℝ) ≤ lo P t z - y)
    linarith
  · rw [h]
  · have h1 := rd_le_slope hc h
    have h2 := mul_le_mul_of_nonneg_right (rd_lo hS t z (lt_of_lt_of_le h hyc)) (by linarith : (0 : ℝ) ≤ y - lo P t z)
    linarith

/-- `hi` minimizes `G - κ⁻ x` over `[0, x̄]`. -/
lemma hi_min {y : ℝ} (hy0 : 0 ≤ y) (hyc : y ≤ P.cap 0) :
    G1 P t z (hi P t z) - P.km 0 * hi P t z ≤ G1 P t z y - P.km 0 * y := by
  have hc := G1_convex hS t z
  rcases lt_trichotomy y (hi P t z) with h | h | h
  · have h1 := slope_le_ld hc h
    have h2 := mul_le_mul_of_nonneg_right (ld_hi hS t z (lt_of_le_of_lt hy0 h)) (by linarith : (0 : ℝ) ≤ hi P t z - y)
    linarith
  · rw [h]
  · have h1 := rd_le_slope hc h
    have h2 := mul_le_mul_of_nonneg_right (rd_hi hS t z (lt_of_lt_of_le h hyc)) (by linarith : (0 : ℝ) ≤ y - hi P t z)
    linarith

/-- The projection of `x` onto the band. -/
def proj (P : M6 1 Z Ω) (t : ℕ) (z : Z) (x : ℝ) : ℝ := min (max x (lo P t z)) (hi P t z)

lemma cost_ge (a : ℝ) : P.kp 0 * a ≤ P.kp 0 * max a 0 + P.km 0 * max (-a) 0 ∧
    -(P.km 0 * a) ≤ P.kp 0 * max a 0 + P.km 0 * max (-a) 0 := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_left a 0) (kp0 hS)
  have h2 := mul_le_mul_of_nonneg_left (le_max_left (-a) 0) (km0 hS)
  have h3 := mul_nonneg (kp0 hS) (le_max_right a 0)
  have h4 := mul_nonneg (km0 hS) (le_max_right (-a) 0)
  constructor <;> nlinarith

/-- Trade to the nearer edge of the band: the projection is optimal, from every `x ∈ ℝ`. -/
lemma opt_proj (x : ℝ) : IsOpt P t z (cst x) (cst (proj P t z x)) := by
  have hlo := lo_bounds hS t z
  have hhi := hi_bounds hS t z
  have hlh := lo_le_hi hS t z
  have hp1 : lo P t z ≤ proj P t z x := le_min (le_max_right _ _) hlh
  have hp2 : proj P t z x ≤ hi P t z := min_le_right _ _
  refine ⟨(mem_box1 P _).mpr ⟨hlo.1.trans hp1, hp2.trans hhi.2⟩, fun y hy => ?_⟩
  rw [cst_eta y] at hy ⊢
  obtain ⟨hy0, hyc⟩ := (mem_box1 P _).mp hy
  rw [cst_sub, cst_sub, cost1, cost1]
  change _ + G1 P t z (proj P t z x) ≤ _ + G1 P t z (y 0)
  set w := y 0
  obtain ⟨hc1, hc2⟩ := cost_ge hS (w - x)
  have hk := kp0 hS
  have hm := km0 hS
  rcases lt_or_ge x (lo P t z) with hx | hx
  · have e : proj P t z x = lo P t z := by
      unfold proj; rw [max_eq_right hx.le, min_eq_left hlh]
    rw [e, max_eq_left (by linarith), max_eq_right (by linarith)]
    have := lo_min hS t z hy0 hyc
    nlinarith
  rcases lt_or_ge (hi P t z) x with hx' | hx'
  · have e : proj P t z x = hi P t z := by
      unfold proj; rw [max_eq_left hx, min_eq_right hx'.le]
    rw [e, max_eq_right (by linarith), max_eq_left (by linarith)]
    have := hi_min hS t z hy0 hyc
    nlinarith
  · have e : proj P t z x = x := by
      unfold proj; rw [max_eq_left hx, min_eq_left hx']
    rw [e, sub_self, neg_zero, max_self, mul_zero, mul_zero, add_zero, zero_add]
    rcases le_or_gt x w with hxw | hxw
    · have hcv : ConvexOn ℝ Set.univ (fun u => G1 P t z u + P.kp 0 * u) :=
        (G1_convex hS t z).add ((convexOn_id convex_univ).smul hk)
      have : G1 P t z x + P.kp 0 * x ≤ G1 P t z w + P.kp 0 * w :=
        le_right_of hcv (lo_min hS t z hy0 hyc) hx hxw
      nlinarith
    · have hcv : ConvexOn ℝ Set.univ (fun u => G1 P t z u - P.km 0 * u) := by
        have := (G1_convex hS t z).add ((concaveOn_id convex_univ).smul hm).neg
        refine this.congr fun u _ => ?_
        simp [smul_eq_mul]; ring
      have : G1 P t z x - P.km 0 * x ≤ G1 P t z w - P.km 0 * w :=
        le_left_of hcv (hi_min hS t z hy0 hyc) hxw.le hx'
      nlinarith

variable {t} in
/-- `V_t` is the cost of trading to the band plus `G_t` at the edge reached. -/
lemma V1_val (ht : t < P.T) (x : ℝ) :
    V1 P t z x = P.kp 0 * max (proj P t z x - x) 0 + P.km 0 * max (-(proj P t z x - x)) 0 +
      G1 P t z (proj P t z x) := by
  have h := (isOpt_iff P t z _ _).mp (opt_proj hS t z x)
  rw [V1_eq, V_lt P ht]
  change sInf (Fobj P t z (cst x) '' box P) = _
  rw [isLeast_sInf h.1 h.2, Fobj, cst_sub, cost1]
  rfl

variable {t} in
lemma V1_below (ht : t < P.T) {x : ℝ} (hx : x ≤ lo P t z) :
    V1 P t z x = P.kp 0 * (lo P t z - x) + G1 P t z (lo P t z) := by
  have e : proj P t z x = lo P t z := by
    unfold proj; rw [max_eq_right hx, min_eq_left (lo_le_hi hS t z)]
  rw [V1_val hS z ht, e, max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

variable {t} in
lemma V1_above (ht : t < P.T) {x : ℝ} (hx : hi P t z ≤ x) :
    V1 P t z x = P.km 0 * (x - hi P t z) + G1 P t z (hi P t z) := by
  have e : proj P t z x = hi P t z := by
    unfold proj; rw [max_eq_left ((lo_le_hi hS t z).trans hx), min_eq_right hx]
  rw [V1_val hS z ht, e, max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

variable {t} in
lemma V1_mid (ht : t < P.T) {x : ℝ} (hx : lo P t z ≤ x) (hx' : x ≤ hi P t z) :
    V1 P t z x = G1 P t z x := by
  have e : proj P t z x = x := by unfold proj; rw [max_eq_left hx, min_eq_left hx']
  rw [V1_val hS z ht, e]
  simp

variable {t} in
/-- `V_t a - V_t b ≤ C(b - a)`. -/
lemma V1_lip (ht : t < P.T) (a b : ℝ) :
    V1 P t z a - V1 P t z b ≤ P.kp 0 * max (b - a) 0 + P.km 0 * max (-(b - a)) 0 := by
  have hb := (isOpt_iff P t z _ _).mp (opt_proj hS t z b)
  have h1 := V_le hS ht z (G_facts hS t z).2.2 (cst a) hb.1
  have hVb : V1 P t z b = Fobj P t z (cst b) (cst (proj P t z b)) := by
    rw [V1_eq, V_lt P ht]
    exact isLeast_sInf hb.1 hb.2
  have h2 := cost_subadd hS (cst (proj P t z b) - cst b) (cst b - cst a)
  rw [sub_add_sub_cancel] at h2
  rw [V1_eq, hVb]
  simp only [Fobj] at h1 ⊢
  rw [cst_sub b a, cost1] at h2
  linarith

variable {t} in
lemma V1_rd_bounds (ht : t < P.T) (x : ℝ) :
    -P.kp 0 ≤ rd (V1 P t z) x ∧ rd (V1 P t z) x ≤ P.km 0 := by
  have hc := V1_convex hS t z
  constructor
  · refine rd_ge_of hc fun y hy => ?_
    have := V1_lip hS z ht x y
    rw [max_eq_left (by linarith), max_eq_right (by linarith)] at this
    linarith
  · refine rd_le_of hc fun y hy => ?_
    have := V1_lip hS z ht y x
    rw [max_eq_right (by linarith), max_eq_left (by linarith)] at this
    linarith

variable {t} in
lemma V1_ld_ge (ht : t < P.T) (x : ℝ) : -P.kp 0 ≤ ld (V1 P t z) x := by
  refine ld_ge_of (V1_convex hS t z) fun y hy => ?_
  have := V1_lip hS z ht y x
  rw [max_eq_left (by linarith), max_eq_right (by linarith)] at this
  linarith

variable {t} in
/-- `V_t` is affine with slope `-κ⁺` below `lo`: a derivative at every point there. -/
lemma V1_deriv_below (ht : t < P.T) {x : ℝ} (hx : x < lo P t z) :
    HasDerivAt (V1 P t z) (-P.kp 0) x := by
  have h : HasDerivAt (fun y => P.kp 0 * (lo P t z - y) + G1 P t z (lo P t z)) (-P.kp 0) x := by
    simpa using (((hasDerivAt_id x).const_sub (lo P t z)).const_mul (P.kp 0)).add_const
      (G1 P t z (lo P t z))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact V1_below hS z ht (le_of_lt hy)

variable {t} in
lemma V1_deriv_above (ht : t < P.T) {x : ℝ} (hx : hi P t z < x) :
    HasDerivAt (V1 P t z) (P.km 0) x := by
  have h : HasDerivAt (fun y => P.km 0 * (y - hi P t z) + G1 P t z (hi P t z)) (P.km 0) x := by
    simpa using (((hasDerivAt_id x).sub_const (hi P t z)).const_mul (P.km 0)).add_const
      (G1 P t z (hi P t z))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact V1_above hS z ht (le_of_lt hy)

variable {t} in
lemma V1_ld_le_lo (ht : t < P.T) {x : ℝ} (hx : x ≤ lo P t z) : ld (V1 P t z) x = -P.kp 0 := by
  refine (ld_affine (V1_convex hS t z) (δ := 1) one_pos fun y _ hyx => ?_)
  rw [V1_below hS z ht hx, V1_below hS z ht (hyx.trans hx)]; ring

variable {t} in
lemma V1_rd_ge_hi (ht : t < P.T) {x : ℝ} (hx : hi P t z ≤ x) : rd (V1 P t z) x = P.km 0 := by
  refine (rd_affine (V1_convex hS t z) (δ := 1) one_pos fun y hxy _ => ?_)
  rw [V1_above hS z ht hx, V1_above hS z ht (hx.trans hxy)]; ring

variable {t} in
lemma V1_rd_below (ht : t < P.T) {x : ℝ} (hx : x < lo P t z) : rd (V1 P t z) x = -P.kp 0 :=
  rd_of_deriv (V1_deriv_below hS z ht hx)

variable {t} in
lemma V1_ld_above (ht : t < P.T) {x : ℝ} (hx : hi P t z < x) : ld (V1 P t z) x = P.km 0 :=
  ld_of_deriv (V1_deriv_above hS z ht hx)

end Edges

end OneInst

/-! ### Part 1a -/

theorem band : Band := by
  intro Z Ω _ P hS t z ht
  have hc := V1_convex hS t z
  refine ⟨G1_strict hS t z, G1_cont hS t z, hc, V1_cont hS t z,
    fun x _ => V1_rd_bounds hS z ht x, fun x _ => ⟨V1_ld_ge hS z ht x, ld_le_rd hc x⟩,
    (lo_bounds hS t z).1, lo_le_hi hS t z, (hi_bounds hS t z).2,
    fun x _ => ⟨cst (proj P t z x), opt_proj hS t z x,
      fun y hy => opt_unique hS t z _ hy (opt_proj hS t z x)⟩,
    fun x _ => opt_proj hS t z x,
    fun x _ hx => ⟨V1_rd_below hS z ht hx, fun _ => V1_ld_le_lo hS z ht hx.le⟩,
    fun x hx => ⟨V1_rd_ge_hi hS z ht hx.le, V1_ld_above hS z ht hx⟩,
    fun x hx hx' => ⟨?_, ?_⟩⟩
  · exact rd_congr (δ := hi P t z - x) (by linarith) fun y hxy hy =>
      V1_mid hS z ht (by linarith) (by linarith)
  · exact ld_congr (δ := x - lo P t z) (by linarith) fun y hy hyx =>
      V1_mid hS z ht (by linarith) (by linarith)

/-! ### Derivatives of `G_t` and the continuation -/

section Split

variable {P : M6 1 Z Ω} (hS : Setting P)
include hS

lemma curv_pos (t : ℕ) (z : Z) : 0 < curv P t z := mul_pos hS.2.2.2.1 (diag_pos hS t z 0)

lemma prob0 (t : ℕ) (z : Z) (ω : Ω) : 0 ≤ P.prob t z ω := hS.2.2.2.2.2.2.2.2.1 t z ω

lemma gross0 (ω : Ω) : 0 < P.gross ω 0 := hS.2.2.2.2.2.2.2.2.2.2 ω 0

lemma rd_G1 (t : ℕ) (z : Z) (x : ℝ) :
    rd (G1 P t z) x = curv P t z * (x - xs P t z) + rd (phi1 P t z) x := by
  have e : G1 P t z = fun y => curv P t z / 2 * (y - xs P t z) ^ 2 + phi1 P t z y :=
    funext (G1_split P t z)
  rw [e]
  exact ((hasDerivAt_quad _ _ x).hasDerivWithinAt.add (hasRd (phi1_convex hS t z) x)).derivWithin
    (uniqueDiffWithinAt_Ioi x)

lemma ld_G1 (t : ℕ) (z : Z) (x : ℝ) :
    ld (G1 P t z) x = curv P t z * (x - xs P t z) + ld (phi1 P t z) x := by
  have e : G1 P t z = fun y => curv P t z / 2 * (y - xs P t z) ^ 2 + phi1 P t z y :=
    funext (G1_split P t z)
  rw [e]
  exact ((hasDerivAt_quad _ _ x).hasDerivWithinAt.add (hasLd (phi1_convex hS t z) x)).derivWithin
    (uniqueDiffWithinAt_Iio x)

lemma rd_phi (t : ℕ) (z : Z) (x : ℝ) : rd (phi1 P t z) x = P.beta *
    ∑ ω, P.prob t z ω * (rd (V1 P (t + 1) (P.next ω)) (x * P.gross ω 0) * P.gross ω 0) := by
  have h : HasDerivWithinAt (phi1 P t z) (P.beta *
      ∑ ω, P.prob t z ω * (rd (V1 P (t + 1) (P.next ω)) (x * P.gross ω 0) * P.gross ω 0))
      (Set.Ioi x) x := by
    unfold phi1
    exact (HasDerivWithinAt.fun_sum fun ω _ =>
      (hasRd_comp (V1_convex hS (t + 1) (P.next ω)) (gross0 hS ω) x).const_mul (P.prob t z ω)).const_mul
      P.beta
  exact h.derivWithin (uniqueDiffWithinAt_Ioi x)

lemma ld_phi (t : ℕ) (z : Z) (x : ℝ) : ld (phi1 P t z) x = P.beta *
    ∑ ω, P.prob t z ω * (ld (V1 P (t + 1) (P.next ω)) (x * P.gross ω 0) * P.gross ω 0) := by
  have h : HasDerivWithinAt (phi1 P t z) (P.beta *
      ∑ ω, P.prob t z ω * (ld (V1 P (t + 1) (P.next ω)) (x * P.gross ω 0) * P.gross ω 0))
      (Set.Iio x) x := by
    unfold phi1
    exact (HasDerivWithinAt.fun_sum fun ω _ =>
      (hasLd_comp (V1_convex hS (t + 1) (P.next ω)) (gross0 hS ω) x).const_mul (P.prob t z ω)).const_mul
      P.beta
  exact h.derivWithin (uniqueDiffWithinAt_Iio x)

/-- The slope bounds on `V_t` hold at every review, including the terminal one. -/
lemma V1_bounds_all (t : ℕ) (z : Z) (x : ℝ) :
    -P.kp 0 ≤ rd (V1 P t z) x ∧ rd (V1 P t z) x ≤ P.km 0 ∧ -P.kp 0 ≤ ld (V1 P t z) x := by
  rcases lt_or_ge t P.T with ht | ht
  · exact ⟨(V1_rd_bounds hS z ht x).1, (V1_rd_bounds hS z ht x).2, V1_ld_ge hS z ht x⟩
  · have e : V1 P t z = fun _ => 0 := funext fun y => V_ge P ht z _
    rw [e, rd_of_deriv (hasDerivAt_const x (0 : ℝ)), ld_of_deriv (hasDerivAt_const x (0 : ℝ))]
    exact ⟨by linarith [kp0 hS], km0 hS, by linarith [kp0 hS]⟩

lemma rd_phi_le (t : ℕ) (z : Z) (x : ℝ) :
    rd (phi1 P t z) x ≤ P.beta * P.km 0 * gbar P t z := by
  rw [rd_phi hS, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hS.2.2.2.2.1.le
  rw [gbar, Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hq := prob0 hS t z ω
  have hg := gross0 hS ω
  have h := (V1_bounds_all hS (t + 1) (P.next ω) (x * P.gross ω 0)).2.1
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hq hg.le)]

lemma ld_phi_ge (t : ℕ) (z : Z) (x : ℝ) :
    -(P.beta * P.kp 0 * gbar P t z) ≤ ld (phi1 P t z) x := by
  rw [ld_phi hS, mul_assoc, ← mul_neg]
  refine mul_le_mul_of_nonneg_left ?_ hS.2.2.2.2.1.le
  rw [gbar, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hq := prob0 hS t z ω
  have hg := gross0 hS ω
  have h := (V1_bounds_all hS (t + 1) (P.next ω) (x * P.gross ω 0)).2.2
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hq hg.le)]

/-- At the last review `G` is the tracking penalty alone. -/
lemma G1_last (z : Z) :
    G1 P (P.T - 1) z = fun y => curv P (P.T - 1) z / 2 * (y - xs P (P.T - 1) z) ^ 2 := by
  funext y
  rw [G1_split]
  have : phi1 P (P.T - 1) z y = 0 := by
    have hT : P.T ≤ P.T - 1 + 1 := by omega
    simp only [phi1, V1_eq, V_ge P hT, mul_zero, Finset.sum_const_zero]
  rw [this, add_zero]

end Split

/-! ### Part 1b -/

theorem ceiling : Ceiling := by
  intro Z Ω _ P hS
  have hk := kp0 hS
  have hm := km0 hS
  refine ⟨fun t z _ => ?_, fun z => ?_⟩
  · have hc := curv_pos hS t z
    rcases eq_or_lt_of_le (lo_le_hi hS t z) with h | h
    · rw [h, sub_self]; positivity
    have h1 := rd_lo hS t z (lt_of_lt_of_le h (hi_bounds hS t z).2)
    have h2 := ld_hi hS t z (lt_of_le_of_lt (lo_bounds hS t z).1 h)
    have h3 := rd_le_ld (phi1_convex hS t z) h
    rw [rd_G1 hS] at h1
    rw [ld_G1 hS] at h2
    rw [le_div_iff₀ hc]
    nlinarith
  · set T1 := P.T - 1
    have hc := curv_pos hS T1 z
    have hrd : ∀ x, rd (G1 P T1 z) x = curv P T1 z * (x - xs P T1 z) := fun x => by
      rw [G1_last hS]; exact rd_of_deriv (hasDerivAt_quad _ _ x)
    have hld : ∀ x, ld (G1 P T1 z) x = curv P T1 z * (x - xs P T1 z) := fun x => by
      rw [G1_last hS]; exact ld_of_deriv (hasDerivAt_quad _ _ x)
    have hcap := cap0 hS
    set a := xs P T1 z - P.kp 0 / curv P T1 z
    set b := xs P T1 z + P.km 0 / curv P T1 z
    have hkc : 0 ≤ P.kp 0 / curv P T1 z := div_nonneg hk hc.le
    have hmc : 0 ≤ P.km 0 / curv P T1 z := div_nonneg hm hc.le
    have hlo : lo P T1 z = clip P a := by
      have hset : {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P T1 z) x} =
          Set.Ico (max a 0) (P.cap 0) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_Ico, max_le_iff, hrd]
        have : a ≤ x ↔ -P.kp 0 ≤ curv P T1 z * (x - xs P T1 z) := by
          rw [show a ≤ x ↔ xs P T1 z - x ≤ P.kp 0 / curv P T1 z by constructor <;> intro <;> linarith,
            le_div_iff₀ hc]
          constructor <;> intro <;> linarith
        rw [← this]; tauto
      unfold lo clip
      rw [hset]
      rcases lt_or_ge (max a 0) (P.cap 0) with h | h
      · rw [ite_eq_left (Set.nonempty_Ico.mpr h), csInf_Ico h, min_eq_left h.le]
      · rw [ite_eq_right (by rw [Set.Ico_eq_empty (not_lt.mpr h)]; exact Set.not_nonempty_empty),
          min_eq_right h]
    have hhi : hi P T1 z = clip P b := by
      have hset : {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P T1 z) x ≤ P.km 0} =
          Set.Ioc 0 (min b (P.cap 0)) := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc, le_min_iff, hld]
        have : x ≤ b ↔ curv P T1 z * (x - xs P T1 z) ≤ P.km 0 := by
          rw [show x ≤ b ↔ x - xs P T1 z ≤ P.km 0 / curv P T1 z by constructor <;> intro <;> linarith,
            le_div_iff₀ hc]
          constructor <;> intro <;> linarith
        rw [← this]; tauto
      unfold hi clip
      rw [hset]
      rcases lt_or_ge 0 (min b (P.cap 0)) with h | h
      · rw [ite_eq_left (Set.nonempty_Ioc.mpr h), csSup_Ioc h,
          max_eq_left (lt_of_lt_of_le h (min_le_left _ _)).le]
      · rw [ite_eq_right (by rw [Set.Ioc_eq_empty (not_lt.mpr h)]; exact Set.not_nonempty_empty)]
        have hb : b ≤ 0 := by
          rcases min_le_iff.mp h with h' | h'
          · exact h'
          · linarith
        rw [max_eq_right hb, min_eq_left hcap.le]
    refine ⟨hlo, hhi, fun ha hb => ?_⟩
    have hab : a ≤ b := by linarith
    rw [hlo, hhi, clip, clip, max_eq_left ha, max_eq_left (ha.trans hab), min_eq_left (hab.trans hb),
      min_eq_left hb, add_div]
    ring

/-! ### Part 1c -/

lemma lo_bracket {P : M6 1 Z Ω} (hS : Setting P) (t : ℕ) (z : Z) :
    min (P.cap 0) (xs P t z - (P.kp 0 + P.beta * P.km 0 * gbar P t z) / curv P t z) ≤ lo P t z := by
  rcases eq_or_lt_of_le (lo_bounds hS t z).2 with h | h
  · rw [h]; exact min_le_left _ _
  refine min_le_of_right_le ?_
  have h1 := rd_lo hS t z h
  rw [rd_G1 hS] at h1
  have h2 := rd_phi_le hS t z (lo P t z)
  have : xs P t z - lo P t z ≤ (P.kp 0 + P.beta * P.km 0 * gbar P t z) / curv P t z := by
    rw [le_div_iff₀ (curv_pos hS t z)]; nlinarith
  linarith

lemma hi_bracket {P : M6 1 Z Ω} (hS : Setting P) (t : ℕ) (z : Z) :
    hi P t z ≤ max 0 (xs P t z + (P.km 0 + P.beta * P.kp 0 * gbar P t z) / curv P t z) := by
  rcases eq_or_lt_of_le (hi_bounds hS t z).1 with h | h
  · rw [← h]; exact le_max_left _ _
  refine le_max_of_le_right ?_
  have h1 := ld_hi hS t z h
  rw [ld_G1 hS] at h1
  have h2 := ld_phi_ge hS t z (hi P t z)
  have : hi P t z - xs P t z ≤ (P.km 0 + P.beta * P.kp 0 * gbar P t z) / curv P t z := by
    rw [le_div_iff₀ (curv_pos hS t z)]; nlinarith
  linarith

theorem brackets : Brackets := fun _ _ _ _ hS t z _ => ⟨lo_bracket hS t z, hi_bracket hS t z⟩

/-! ### Part 1d -/

section Coarse1

variable {P : M6 1 Z Ω} (hS : Setting P)
include hS

lemma not_up_of_down {t : ℕ} {z : Z} {ω : Ω} (hD : Down P t z ω) : ¬ Up P t z ω := by
  intro hU
  unfold Up at hU
  unfold Down at hD
  have h1 := lo_le_hi hS t z
  have h2 := lo_le_hi hS (t + 1) (P.next ω)
  have h3 := mul_le_mul_of_nonneg_right h1 (gross0 hS ω).le
  linarith

lemma not_down_of_up {t : ℕ} {z : Z} {ω : Ω} (hU : Up P t z ω) : ¬ Down P t z ω :=
  fun hD => not_up_of_down hS hD hU

/-- In the coarse-innovation regime the continuation is differentiable across the band. -/
lemma phi_hasDeriv {t : ℕ} {z : Z} (hT : t + 1 < P.T)
    (hUD : ∀ ω, 0 < P.prob t z ω → Up P t z ω ∨ Down P t z ω) {x : ℝ} (hx : lo P t z ≤ x)
    (hx' : x ≤ hi P t z) :
    HasDerivAt (phi1 P t z) (P.beta * ∑ ω, P.prob t z ω *
      ((if Up P t z ω then -P.kp 0 else P.km 0) * P.gross ω 0)) x := by
  unfold phi1
  refine (HasDerivAt.fun_sum fun ω _ => ?_).const_mul P.beta
  rcases eq_or_lt_of_le (prob0 hS t z ω) with hq | hq
  · rw [← hq]; simp only [zero_mul]; exact hasDerivAt_const x 0
  have hg := gross0 hS ω
  refine HasDerivAt.const_mul _ ?_
  rcases hUD ω hq with hU | hD
  · rw [ite_eq_left hU]
    have hlt : x * P.gross ω 0 < lo P (t + 1) (P.next ω) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hx' hg.le) hU
    exact (V1_deriv_below hS (P.next ω) hT hlt).comp x (hasDerivAt_mul_const _)
  · rw [ite_eq_right (not_up_of_down hS hD)]
    have hlt : hi P (t + 1) (P.next ω) < x * P.gross ω 0 :=
      lt_of_lt_of_le hD (mul_le_mul_of_nonneg_right hx hg.le)
    exact (V1_deriv_above hS (P.next ω) hT hlt).comp x (hasDerivAt_mul_const _)

lemma d_eq {t : ℕ} {z : Z} (hUD : ∀ ω, 0 < P.prob t z ω → Up P t z ω ∨ Down P t z ω) :
    ∑ ω, P.prob t z ω * ((if Up P t z ω then -P.kp 0 else P.km 0) * P.gross ω 0) =
      -P.kp 0 * Umass P t z + P.km 0 * Dmass P t z := by
  unfold Umass Dmass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases eq_or_lt_of_le (prob0 hS t z ω) with hq | hq
  · rw [← hq]; simp
  rcases hUD ω hq with hU | hD
  · rw [ite_eq_left hU, ite_eq_left hU, ite_eq_right (not_down_of_up hS hU)]; ring
  · rw [ite_eq_right (not_up_of_down hS hD), ite_eq_right (not_up_of_down hS hD), ite_eq_left hD]; ring

end Coarse1

theorem coarse : Coarse := by
  intro Z Ω _ P hS t z hT
  have hc := curv_pos hS t z
  have hcne := hc.ne'
  refine ⟨fun hlo hhi hUD => ?_, fun ω _ => ⟨fun h => ?_, fun h => ?_⟩, fun hg1 hlo hhi ω _ => ?_⟩
  · set d := P.beta * ∑ ω, P.prob t z ω * ((if Up P t z ω then -P.kp 0 else P.km 0) * P.gross ω 0)
      with hd
    have hdd : d = P.beta * (-P.kp 0 * Umass P t z + P.km 0 * Dmass P t z) := by
      rw [hd, d_eq hS hUD]
    have hlh := lo_le_hi hS t z
    have hG : ∀ x, lo P t z ≤ x → x ≤ hi P t z →
        HasDerivAt (G1 P t z) (curv P t z * (x - xs P t z) + d) x := fun x h1 h2 => by
      have e : G1 P t z = fun y => curv P t z / 2 * (y - xs P t z) ^ 2 + phi1 P t z y :=
        funext (G1_split P t z)
      rw [e]
      exact (hasDerivAt_quad _ _ x).add (phi_hasDeriv hS hT hUD h1 h2)
    have l1 := rd_lo hS t z (lt_of_le_of_lt hlh hhi)
    have l2 := ld_lo hS t z hlo
    rw [rd_of_deriv (hG _ le_rfl hlh)] at l1
    rw [ld_of_deriv (hG _ le_rfl hlh)] at l2
    have h1 := ld_hi hS t z (lt_of_lt_of_le hlo hlh)
    have h2 := rd_hi hS t z hhi
    rw [ld_of_deriv (hG _ hlh le_rfl)] at h1
    rw [rd_of_deriv (hG _ hlh le_rfl)] at h2
    have eL : curv P t z * (lo P t z - xs P t z) + d = -P.kp 0 := le_antisymm l2 l1
    have eH : curv P t z * (hi P t z - xs P t z) + d = P.km 0 := le_antisymm h1 h2
    have e1 : P.km 0 / curv P t z * curv P t z = P.km 0 := div_mul_cancel₀ _ hcne
    have e2 : P.kp 0 / curv P t z * curv P t z = P.kp 0 := div_mul_cancel₀ _ hcne
    have e3 : tilt P t z * curv P t z = P.beta * (P.kp 0 * Umass P t z - P.km 0 * Dmass P t z) := by
      rw [tilt, div_mul_cancel₀ _ hcne]
    have hH : hi P t z = xs P t z + P.km 0 / curv P t z + tilt P t z := by
      apply mul_right_cancel₀ hcne
      rw [add_mul, add_mul, e1, e3]
      linear_combination eH - hdd
    have hL : lo P t z = xs P t z - P.kp 0 / curv P t z + tilt P t z := by
      apply mul_right_cancel₀ hcne
      rw [add_mul, sub_mul, e2, e3]
      linear_combination eL - hdd
    refine ⟨hH, hL, by rw [hH, hL]; ring, fun hUD' hk => ?_⟩
    rw [tilt, hUD', hk, sub_self, mul_zero, zero_div]
  · unfold Up
    calc hi P t z * P.gross ω 0
        ≤ P.gross ω 0 * max 0 (xs P t z + (P.km 0 + P.beta * P.kp 0 * gbar P t z) / curv P t z) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hi_bracket hS t z) (gross0 hS ω).le
      _ < _ := h
      _ ≤ lo P (t + 1) (P.next ω) := lo_bracket hS (t + 1) (P.next ω)
  · unfold Down
    calc hi P (t + 1) (P.next ω) ≤ _ := hi_bracket hS (t + 1) (P.next ω)
      _ < _ := h
      _ ≤ lo P t z * P.gross ω 0 := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right (lo_bracket hS t z) (gross0 hS ω).le
  · have hgb : ∀ t z, gbar P t z = 1 := fun t z => by
      simp only [gbar, hg1, mul_one]; exact hS.2.2.2.2.2.2.2.2.2.1 t z
    have hB := hi_bracket hS t z
    have hL := lo_bracket hS (t + 1) (P.next ω)
    have hB' := hi_bracket hS (t + 1) (P.next ω)
    have hLt := lo_bracket hS t z
    rw [hgb, mul_one] at hB hL hB' hLt
    have hlh := lo_le_hi hS t z
    constructor
    · intro h
      unfold Up
      rw [hg1, mul_one]
      have hA : hi P t z ≤ xs P t z + (P.km 0 + P.beta * P.kp 0) / curv P t z := by
        rcases le_max_iff.mp hB with h' | h'
        · linarith
        · exact h'
      exact lt_of_lt_of_le (lt_min hhi (by linarith)) hL
    · intro h
      unfold Down
      rw [hg1, mul_one]
      have hA : xs P t z - (P.kp 0 + P.beta * P.km 0) / curv P t z ≤ lo P t z := by
        rcases min_le_iff.mp hLt with h' | h'
        · linarith
        · exact h'
      exact lt_of_le_of_lt hB' (max_lt hlo (by linarith))

/-! ### Part 1e -/

/-- The left derivative of `V_t` at `b` equals its right derivative at `a < b` exactly when
`[a, b]` lies in one affine piece. -/
lemma edge_iff {P : M6 1 Z Ω} (hS : Setting P) {t : ℕ} (z : Z) (hT : t < P.T)
    (hk : 0 < P.kp 0 + P.km 0) {a b : ℝ} (hab : a < b) :
    ld (V1 P t z) b = rd (V1 P t z) a ↔ b ≤ lo P t z ∨ hi P t z ≤ a := by
  have hVc := V1_convex hS t z
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨h1, h2⟩ := hn
    have hlt : rd (V1 P t z) a < ld (V1 P t z) b := by
      rcases eq_or_lt_of_le (lo_le_hi hS t z) with he | hlh
      · rw [V1_rd_below hS z hT (by rw [he]; exact h2), V1_ld_above hS z hT (by rw [← he]; exact h1)]
        linarith
      · set p := max a (lo P t z)
        set q := min b (hi P t z)
        have hpq : p < q := max_lt (lt_min hab h2) (lt_min h1 hlh)
        set m := (p + q) / 2
        have hpm : p < m := by simp only [m]; linarith
        have hmq : m < q := by simp only [m]; linarith
        have hlop : lo P t z ≤ p := le_max_right _ _
        have hqhi : q ≤ hi P t z := min_le_right _ _
        have hVp := V1_mid hS z hT hlop (hpq.le.trans hqhi)
        have hVq := V1_mid hS z hT (hlop.trans hpq.le) hqhi
        have hVm := V1_mid hS z hT (hlop.trans hpm.le) (hmq.le.trans hqhi)
        have hs := (G1_strict hS t z).2 (Set.mem_univ p) (Set.mem_univ q) hpq.ne
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        simp only [smul_eq_mul] at hs
        rw [show (1 / 2 : ℝ) * p + 1 / 2 * q = m by simp only [m]; ring] at hs
        have r1 := rd_mono hVc (le_max_left a (lo P t z) : a ≤ p)
        have r2 := rd_le_slope hVc hpm
        have l1 := ld_mono hVc (min_le_left b (hi P t z) : q ≤ b)
        have l2 := slope_le_ld hVc hmq
        rw [show m - p = (q - p) / 2 by simp only [m]; ring] at r2
        rw [show q - m = (q - p) / 2 by simp only [m]; ring] at l2
        have hh : 0 < (q - p) / 2 := by linarith
        have A1 := mul_le_mul_of_nonneg_right r1 hh.le
        have A2 := mul_le_mul_of_nonneg_right l1 hh.le
        have : rd (V1 P t z) a * ((q - p) / 2) < ld (V1 P t z) b * ((q - p) / 2) := by
          linarith
        exact lt_of_mul_lt_mul_right this hh.le
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · rintro (hb | ha)
    · rw [V1_ld_le_lo hS z hT hb, V1_rd_below hS z hT (lt_of_lt_of_le hab hb)]
    · rw [V1_rd_ge_hi hS z hT ha, V1_ld_above hS z hT (lt_of_le_of_lt ha hab)]

lemma attained_mid {P : M6 1 Z Ω} (hS : Setting P) (hk : 0 < P.kp 0 + P.km 0) {t : ℕ} (z : Z)
    (hT : t + 1 < P.T) :
    (hi P t z - lo P t z = (P.kp 0 + P.km 0) / curv P t z ↔
      ld (G1 P t z) (hi P t z) = P.km 0 ∧ rd (G1 P t z) (lo P t z) = -P.kp 0 ∧
      ∀ ω, 0 < P.prob t z ω →
        hi P t z * P.gross ω 0 ≤ lo P (t + 1) (P.next ω) ∨
          hi P (t + 1) (P.next ω) ≤ lo P t z * P.gross ω 0) ∧
    (hi P t z - lo P t z ≠ (P.kp 0 + P.km 0) / curv P t z →
      hi P t z - lo P t z < (P.kp 0 + P.km 0) / curv P t z) := by
  have ht : t < P.T := by omega
  have hc := curv_pos hS t z
  have hcne := hc.ne'
  have hβ : 0 < P.beta := hS.2.2.2.2.1
  have hlh := lo_le_hi hS t z
  have hceil := (ceiling Z Ω P hS).1 t z ht
  refine ⟨?_, fun hne => lt_of_le_of_ne hceil hne⟩
  rcases eq_or_lt_of_le hlh with he | hlt
  · have hpos : 0 < (P.kp 0 + P.km 0) / curv P t z := div_pos hk hc
    constructor
    · intro h
      rw [he, sub_self] at h
      linarith
    · rintro ⟨h1, h2, -⟩
      have h3 := ld_le_rd (G1_convex hS t z) (hi P t z)
      rw [he] at h2
      linarith
  have hlc : lo P t z < P.cap 0 := lt_of_lt_of_le hlt (hi_bounds hS t z).2
  have h0h : 0 < hi P t z := lt_of_le_of_lt (lo_bounds hS t z).1 hlt
  have X := ld_hi hS t z h0h
  have Y := rd_lo hS t z hlc
  rw [ld_G1 hS] at X
  rw [rd_G1 hS] at Y
  have hab : ∀ ω, lo P t z * P.gross ω 0 < hi P t z * P.gross ω 0 := fun ω =>
    mul_lt_mul_of_pos_right hlt (gross0 hS ω)
  have hW : ld (phi1 P t z) (hi P t z) - rd (phi1 P t z) (lo P t z) = P.beta *
      ∑ ω, P.prob t z ω * ((ld (V1 P (t + 1) (P.next ω)) (hi P t z * P.gross ω 0) -
        rd (V1 P (t + 1) (P.next ω)) (lo P t z * P.gross ω 0)) * P.gross ω 0) := by
    rw [ld_phi hS, rd_phi hS, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun ω _ => by ring
  have hterm : ∀ ω, 0 ≤ P.prob t z ω * ((ld (V1 P (t + 1) (P.next ω)) (hi P t z * P.gross ω 0) -
      rd (V1 P (t + 1) (P.next ω)) (lo P t z * P.gross ω 0)) * P.gross ω 0) := fun ω =>
    mul_nonneg (prob0 hS t z ω) (mul_nonneg
      (sub_nonneg.mpr (rd_le_ld (V1_convex hS (t + 1) (P.next ω)) (hab ω))) (gross0 hS ω).le)
  have hWnn : 0 ≤ ld (phi1 P t z) (hi P t z) - rd (phi1 P t z) (lo P t z) := by
    rw [hW]; exact mul_nonneg hβ.le (Finset.sum_nonneg fun ω _ => hterm ω)
  have key : ld (phi1 P t z) (hi P t z) - rd (phi1 P t z) (lo P t z) = 0 ↔
      ∀ ω, 0 < P.prob t z ω →
        hi P t z * P.gross ω 0 ≤ lo P (t + 1) (P.next ω) ∨
          hi P (t + 1) (P.next ω) ≤ lo P t z * P.gross ω 0 := by
    rw [hW, mul_eq_zero, or_iff_right hβ.ne', Finset.sum_eq_zero_iff_of_nonneg fun ω _ => hterm ω]
    refine ⟨fun h ω hq => ?_, fun h ω _ => ?_⟩
    · have h1 := h ω (Finset.mem_univ ω)
      rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, or_iff_left (gross0 hS ω).ne'] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hq.ne'
      · exact (edge_iff hS (P.next ω) hT hk (hab ω)).mp h1
    · rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, or_iff_left (gross0 hS ω).ne']
      rcases eq_or_lt_of_le (prob0 hS t z ω) with hq | hq
      · exact Or.inl hq.symm
      · exact Or.inr ((edge_iff hS (P.next ω) hT hk (hab ω)).mpr (h ω hq))
  constructor
  · intro h
    have hw : curv P t z * (hi P t z - lo P t z) = P.kp 0 + P.km 0 := by rw [h]; field_simp
    have h0 : ld (phi1 P t z) (hi P t z) - rd (phi1 P t z) (lo P t z) = 0 := by linarith
    refine ⟨?_, ?_, key.mp h0⟩
    · rw [ld_G1 hS]; linarith
    · rw [rd_G1 hS]; linarith
  · rintro ⟨h1, h2, h3⟩
    have h0 := key.mpr h3
    rw [ld_G1 hS] at h1
    rw [rd_G1 hS] at h2
    rw [eq_div_iff hcne]
    linarith

/-- At the last review the continuation vanishes, so the ceiling is attained exactly when both
edges are first-order points. -/
lemma attained_last {P : M6 1 Z Ω} (hS : Setting P) (hk : 0 < P.kp 0 + P.km 0) (z : Z) :
    hi P (P.T - 1) z - lo P (P.T - 1) z = (P.kp 0 + P.km 0) / curv P (P.T - 1) z ↔
      ld (G1 P (P.T - 1) z) (hi P (P.T - 1) z) = P.km 0 ∧
        rd (G1 P (P.T - 1) z) (lo P (P.T - 1) z) = -P.kp 0 := by
  set T1 := P.T - 1
  have hc := curv_pos hS T1 z
  have hcne := hc.ne'
  have hrd : ∀ x, rd (G1 P T1 z) x = curv P T1 z * (x - xs P T1 z) := fun x => by
    rw [G1_last hS]; exact rd_of_deriv (hasDerivAt_quad _ _ x)
  have hld : ∀ x, ld (G1 P T1 z) x = curv P T1 z * (x - xs P T1 z) := fun x => by
    rw [G1_last hS]; exact ld_of_deriv (hasDerivAt_quad _ _ x)
  rw [hrd, hld]
  constructor
  · intro h
    have hpos : 0 < (P.kp 0 + P.km 0) / curv P T1 z := div_pos hk hc
    have hlt : lo P T1 z < hi P T1 z := by linarith
    have X := ld_hi hS T1 z (lt_of_le_of_lt (lo_bounds hS T1 z).1 hlt)
    have Y := rd_lo hS T1 z (lt_of_lt_of_le hlt (hi_bounds hS T1 z).2)
    rw [hld] at X
    rw [hrd] at Y
    have hw : curv P T1 z * (hi P T1 z - lo P T1 z) = P.kp 0 + P.km 0 := by rw [h]; field_simp
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [eq_div_iff hcne]
    linarith

theorem attained : Attained := fun _ _ _ _ hS hk =>
  ⟨fun _ z hT => attained_mid hS hk z hT, fun z => attained_last hS hk z⟩

/-! ### The claim -/

theorem proof : Standalone.M6QuarterlyBandStaticCeiling.statement :=
  ⟨band, ceiling, brackets, coarse, attained, manyConvex, diameter, staticShape⟩

end

end Novel.M6QuarterlyBandStaticCeilingProof

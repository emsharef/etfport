import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Standalone.M3MeanTypeCaps
import Novel.M3PremiumNodeBoundsProof

/-!
# Proof of claim 026: range-type caps cannot be sharp; mean-type caps

This proof uses claim 011's, claim 022's and claim 023's proof modules
(`depends_on: [11, 22, 23]`; Q-04).

* **Tilted measure.** At a node, `-V₁^N = Σ ω` with `ω = π₁ q e^{-ρ W^N}`. After a trade with
  normalized wealth change `D`, `-condObj = Σ ω e^{-ρ D}`.
* **Tangent cap.** Jensen's inequality for `exp` under the tilted measure gives
  `CE(trade) ≤ c^N + E_Q[D]`, and `E_Q[D]` is the first-order gain `tanLin / W₀⁻`.
* **Curvature cap.** `L(ε) = ln Σ ω e^{-ρ ε Z}` has `L'' = ρ² Var_{Q_ε}(Z)`. Each tilted weight is at
  least its node-path mass times `e^{-ρ(ΔW + 2 s ε_max)}`, so `Var_{Q_ε} ≥ v_min` on `[0, ε_max]`.
  Two monotonicity steps then give `L(ε) ≥ L(0) - ρ r ε + ρ² v_min ε²/2`.
* **Range-type caps.** A one-parameter, two-scenario M3 family realizes the data. As the light
  mass vanishes, the gain of the all-in trade tends to the sure value.
-/

namespace Novel.M3MeanTypeCapsProof

open Matrix Finset Standalone.M3FiniteContinuation Standalone.M3PremiumNodeBounds
  Standalone.M3MeanTypeCaps Novel.M3FiniteContinuationProof Novel.M3PremiumNodeBoundsProof
open Standalone.M2ScoreAccounting hiding gain
open Standalone.M3EtfChannelSandwich (cR phi RootOpt)
open scoped Classical

set_option linter.unusedSectionVars false

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T] {P : M3 n K S T}

/-! ### The tilted node measure -/

/-- Tilt weight `ω(θ, s) = π₁(θ | y) q_s e^{-ρ W^N}`. -/
noncomputable def tw (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (p : T × S) : ℝ :=
  post P y p.1 * P.D.q p.2 * Real.exp (-P.rho * WN P u₀ y p.1 p.2)

section Tilt

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y)
include hS hu hy

omit hu hy in
lemma tw_nonneg (p : T × S) : 0 ≤ tw P u₀ y p :=
  mul_nonneg (mul_nonneg (post_nonneg hS y p.1) ((setting_parts hS).2.1 p.2)) (Real.exp_pos _).le

omit hu hy in
lemma tw_path {p : T × S} (h : 0 < tw P u₀ y p) : NodePath P y p.1 p.2 := by
  have h1 : 0 < post P y p.1 * P.D.q p.2 := (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp h
  have ha : 0 < post P y p.1 := lt_of_le_of_ne (post_nonneg hS y p.1) (fun h => by
    rw [← h, zero_mul] at h1; exact lt_irrefl _ h1)
  have hb : 0 < P.D.q p.2 := lt_of_le_of_ne ((setting_parts hS).2.1 p.2) (fun h => by
    rw [← h, mul_zero] at h1; exact lt_irrefl _ h1)
  exact ⟨ha, hb⟩

omit hu hy in
/-- `-condObj` after a trade, through the tilt weights. -/
lemma condObj_tw (u : Inst 1 n → ℝ) :
    -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
      = ∑ p, tw P u₀ y p * Real.exp (-P.rho * (condW P (x1 P y u₀) (h1 P u₀) u p.1 p.2 / W0 P.D
          - WN P u₀ y p.1 p.2)) := by
  simp only [condObj, U, tw, Fintype.sum_prod_type, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  rw [mul_assoc (post P y t * P.D.q s), ← Real.exp_add]
  rw [show -P.rho * WN P u₀ y t s + -P.rho * (condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D
    - WN P u₀ y t s) = -P.rho * (condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D) by ring]
  ring

lemma tw_sum_pos : 0 < ∑ p, tw P u₀ y p := by
  have hN := (V1_node hS hu hy .N).2
  rw [V1N_eq hS hu hy] at hN
  have := condObj_tw hS (u₀ := u₀) (y := y) 0
  simp only [WN, sub_self, mul_zero, Real.exp_zero, mul_one] at this
  linarith

lemma nodeCEN_tw : nodeCE P .N u₀ y = -(1 / P.rho) * Real.log (∑ p, tw P u₀ y p) := by
  unfold nodeCE
  rw [V1N_eq hS hu hy, condObj_tw hS 0]
  simp [WN]

lemma tilt_eq (Z : T → S → ℝ) :
    tiltMean P u₀ y Z = ∑ p, tw P u₀ y p / (∑ q, tw P u₀ y q) * Z p.1 p.2 := by
  have hpos := tw_sum_pos hS hu hy
  have hden : (∑ t, ∑ s, post P y t * P.D.q s *
      Real.exp (-P.rho * (condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D))) = ∑ q, tw P u₀ y q := by
    rw [Fintype.sum_prod_type]; rfl
  unfold tiltMean
  rw [hden, Finset.sum_div,
    Fintype.sum_prod_type (f := fun p => tw P u₀ y p / (∑ q, tw P u₀ y q) * Z p.1 p.2)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by simp only [tw, WN]; ring

lemma tw_norm : ∑ p, tw P u₀ y p / (∑ q, tw P u₀ y q) = 1 := by
  rw [← Finset.sum_div, div_self (tw_sum_pos hS hu hy).ne']

lemma tilt_affine (Z : T → S → ℝ) (a b : ℝ) :
    tiltMean P u₀ y (fun t s => a * Z t s + b) = a * tiltMean P u₀ y Z + b := by
  rw [tilt_eq hS hu hy, tilt_eq hS hu hy]
  have h1 := tw_norm hS hu hy
  simp only [mul_add, sum_add_distrib, ← sum_mul, h1, one_mul, mul_sum]
  congr 1
  exact sum_congr rfl fun p _ => by ring

lemma tilt_le (Z : T → S → ℝ) {c : ℝ} (h : ∀ t s, NodePath P y t s → Z t s ≤ c) :
    tiltMean P u₀ y Z ≤ c := by
  rw [tilt_eq hS hu hy]
  have hpos := tw_sum_pos hS hu hy
  have e : c = ∑ p, tw P u₀ y p / (∑ q, tw P u₀ y q) * c := by
    rw [← sum_mul, tw_norm hS hu hy, one_mul]
  rw [e]
  refine sum_le_sum fun p _ => ?_
  rcases (tw_nonneg hS (u₀ := u₀) (y := y) p).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h p.1 p.2 (tw_path hS hp)) (div_nonneg hp.le hpos.le)
  · rw [← hp]; simp

lemma tilt_ge (Z : T → S → ℝ) {c : ℝ} (h : ∀ t s, NodePath P y t s → c ≤ Z t s) :
    c ≤ tiltMean P u₀ y Z := by
  have := tilt_le hS hu hy (fun t s => -1 * Z t s + 0) (c := -c) fun t s hp => by
    linarith [h t s hp]
  rw [tilt_affine hS hu hy] at this
  linarith

/-- Jensen under the tilted measure: `CE(u) ≤ c^N + E_Q[D_u]`. -/
lemma jensen (u : Inst 1 n → ℝ) :
    tradeCE P u₀ y u - nodeCE P .N u₀ y
      ≤ tiltMean P u₀ y (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s) := by
  have hρ := hS.1
  have hpos := tw_sum_pos hS hu hy
  set Om := ∑ q, tw P u₀ y q
  set D : T × S → ℝ := fun p => condW P (x1 P y u₀) (h1 P u₀) u p.1 p.2 / W0 P.D - WN P u₀ y p.1 p.2
  have hw : ∀ p ∈ (univ : Finset (T × S)), 0 ≤ tw P u₀ y p / Om := fun p _ =>
    div_nonneg (tw_nonneg hS p) hpos.le
  have hj := convexOn_exp.map_sum_le (t := univ) (w := fun p => tw P u₀ y p / Om)
    (p := fun p => -P.rho * D p) hw (by simpa using tw_norm hS hu hy) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hc := condObj_tw hS (u₀ := u₀) (y := y) u
  have hsplit : ∑ p, tw P u₀ y p * Real.exp (-P.rho * D p)
      = Om * ∑ p, tw P u₀ y p / Om * Real.exp (-P.rho * D p) := by
    rw [mul_sum]; exact sum_congr rfl fun p _ => by field_simp
  have hmean : ∑ p, tw P u₀ y p / Om * (-P.rho * D p) = -P.rho * tiltMean P u₀ y
      (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s) := by
    rw [tilt_eq hS hu hy, mul_sum]; exact sum_congr rfl fun p _ => by ring
  rw [hmean] at hj
  have hge : Om * Real.exp (-P.rho * tiltMean P u₀ y
      (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s))
      ≤ -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u := by
    rw [hc, hsplit]; exact mul_le_mul_of_nonneg_left hj hpos.le
  have hlog := Real.log_le_log (by positivity) hge
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [nodeCEN_tw hS hu hy]
  unfold tradeCE
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  have key := mul_le_mul_of_nonneg_left hlog hρi.le
  have e : 1 / P.rho * (Real.log Om + -P.rho * tiltMean P u₀ y
      (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s))
      = 1 / P.rho * Real.log Om - tiltMean P u₀ y
      (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s) := by
    field_simp; ring
  rw [e] at key
  linarith

/-- Linearity of the tilted mean. -/
lemma tilt_lin {ι : Type} [Fintype ι] (a : ι → ℝ) (Z : ι → T → S → ℝ) (b : ℝ) :
    tiltMean P u₀ y (fun t s => ∑ j, a j * Z j t s + b) = ∑ j, a j * tiltMean P u₀ y (Z j) + b := by
  simp only [tilt_eq hS hu hy]
  have h1 := tw_norm hS hu hy
  simp only [mul_add, sum_add_distrib, ← sum_mul, h1, one_mul, mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun p _ => by ring

lemma rBuy_eq (j : Fin n) :
    (1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j
      = tiltMean P u₀ y (gE P j) - 1 - P.D.kplus (Sum.inr j) := by
  have hk := ((setting_parts hS).2.2.2.2.2.1 (Sum.inr j)).1
  have e : (fun t s => (gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j)))
      = fun t s => 1 / (1 + P.D.kplus (Sum.inr j)) * gE P j t s
        + (-(1 + P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))) := by
    funext t s; field_simp; ring
  unfold rBuy
  rw [e, tilt_affine hS hu hy]
  field_simp
  ring

lemma rSell_eq (j : Fin n) :
    rSell P u₀ y j = 1 - P.D.kminus (Sum.inr j) - tiltMean P u₀ y (gE P j) := by
  have e : (fun t s => 1 - P.D.kminus (Sum.inr j) - gE P j t s)
      = fun t s => -1 * gE P j t s + (1 - P.D.kminus (Sum.inr j)) := by funext t s; ring
  unfold rSell
  rw [e, tilt_affine hS hu hy]
  ring

end Tilt

omit [Fintype T] in
lemma sum_inst {n : ℕ} (f : Inst 1 n → ℝ) : ∑ i, f i = f (Sum.inl 0) + ∑ j, f (Sum.inr j) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]

omit [Fintype T] in
lemma cost_E {D : Data 1 n K S} {u : Inst 1 n → ℝ} (hA : u (Sum.inl 0) = 0) :
    cost D u = ∑ j, (D.kplus (Sum.inr j) * max (u (Sum.inr j)) 0
      + D.kminus (Sum.inr j) * max (-u (Sum.inr j)) 0) := by
  unfold cost; rw [sum_inst, hA]; simp

/-- The normalized wealth change of an ETF-only node trade. -/
lemma condW_diff {u : Inst 1 n → ℝ} (hA : u (Sum.inl 0) = 0) (x : Inst 1 n → ℝ) (h : ℝ)
    (t : T) (s : S) :
    condW P x h u t s = condW P x h 0 t s + ∑ j, u (Sum.inr j) * (gE P j t s - 1) - cost P.D u := by
  unfold condW gE
  simp only [cost_zero, Pi.zero_apply, sum_const_zero, sub_zero, add_zero]
  rw [sum_inst u, sum_inst (fun i => (x i + u i) * (1 + ret P.D (P.par t) s i)),
    sum_inst (fun i => x i * (1 + ret P.D (P.par t) s i)), hA]
  simp only [add_zero, zero_add, add_mul, sum_add_distrib, mul_sub, mul_one, sum_sub_distrib]
  ring_nf

section TangentSec

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y)
include hS hu hy

/-- `E_Q[D_u] = tanLin u / W₀⁻` for an ETF-only trade. -/
lemma tilt_D {u : Inst 1 n → ℝ} (hA : u (Sum.inl 0) = 0) :
    tiltMean P u₀ y (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s)
      = tanLin P u₀ y u / W0 P.D := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have e : (fun t s => condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s)
      = fun t s => ∑ j, u (Sum.inr j) / W0 P.D * gE P j t s
        + (-(∑ j, u (Sum.inr j)) - cost P.D u) / W0 P.D := by
    funext t s
    rw [condW_diff hA, WN]
    have h1 : ∑ j, u (Sum.inr j) * (gE P j t s - 1)
        = ∑ j, u (Sum.inr j) * gE P j t s - ∑ j, u (Sum.inr j) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    have h2 : ∑ j, u (Sum.inr j) / W0 P.D * gE P j t s = (∑ j, u (Sum.inr j) * gE P j t s) / W0 P.D := by
      rw [sum_div]; exact sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    field_simp
    ring
  rw [e, tilt_lin hS hu hy, cost_E hA]
  have h3 : ∑ j, u (Sum.inr j) / W0 P.D * tiltMean P u₀ y (gE P j)
      = (∑ j, u (Sum.inr j) * tiltMean P u₀ y (gE P j)) / W0 P.D := by
    rw [sum_div]; exact sum_congr rfl fun j _ => by ring
  unfold tanLin
  rw [h3, ← add_div]
  congr 1
  rw [← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [rBuy_eq hS hu hy, rSell_eq hS hu hy]
  have hsplit := max_zero_sub_eq_self (u (Sum.inr j))
  linear_combination (1 - tiltMean P u₀ y (gE P j)) * hsplit

/-- Part 2 (a): the gain is at most the first-order gain of the optimal trade. -/
lemma gain_le_tan : ∃ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u ∧
    gain P u₀ y ≤ tanLin P u₀ y u / W0 P.D := by
  obtain ⟨u, hfe, -, hV⟩ := cond_attain hS .E (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  refine ⟨u, hfe, ?_⟩
  have hj := jensen hS hu hy u
  rw [tilt_D hS hu hy hfe.2.2] at hj
  have : nodeCE P .E u₀ y = tradeCE P u₀ y u := by unfold nodeCE tradeCE; rw [hV]
  unfold gain; rw [this]; exact hj

/-- `M⁺ = max_j ((1 + κ⁺_j) r⁺_j)⁺`. -/
lemma Mplus_ge (j : Fin n) : (1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j
    ≤ ⨆ k, max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0 :=
  (le_max_left _ _).trans (le_ciSup (f := fun k => max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0)
    (Set.finite_range _).bddAbove j)

omit hS hu hy in
lemma Mplus_nonneg : 0 ≤ ⨆ k, max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0 :=
  Real.iSup_nonneg fun _ => le_max_right _ _

/-- Part 2 (b): every first-order gain is at most `tanBound`. -/
lemma tan_le_bound {u : Inst 1 n → ℝ} (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) :
    tanLin P u₀ y u / W0 P.D ≤ tanBound P u₀ y := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hA : u (Sum.inl 0) = 0 := hfe.2.2
  set M := ⨆ k, max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0
  have hM := Mplus_nonneg (P := P) (u₀ := u₀) (y := y)
  have hbud := hfe.2.1
  have hc := cost_nonneg P (rates_nonneg hS) u
  rw [sum_inst, hA, zero_add] at hbud
  have hx : ∀ j, max (-u (Sum.inr j)) 0 ≤ x1 P y u₀ (Sum.inr j) := fun j =>
    max_le (by linarith [hfe.1 (Sum.inr j)]) ((node_nn hS hu hy.1).1 _)
  have hsplit : ∀ j, u (Sum.inr j) = max (u (Sum.inr j)) 0 - max (-u (Sum.inr j)) 0 := fun j =>
    (max_zero_sub_eq_self _).symm
  have hpos : ∑ j, max (u (Sum.inr j)) 0 ≤ h1 P u₀ + ∑ j, x1 P y u₀ (Sum.inr j) := by
    have e : ∑ j, u (Sum.inr j) = ∑ j, max (u (Sum.inr j)) 0 - ∑ j, max (-u (Sum.inr j)) 0 := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => hsplit j
    have := sum_le_sum fun j (_ : j ∈ univ) => hx j
    linarith
  have hlin : tanLin P u₀ y u ≤ M * ∑ j, max (u (Sum.inr j)) 0
      + ∑ j, x1 P y u₀ (Sum.inr j) * max (rSell P u₀ y j) 0 := by
    unfold tanLin
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have h1 := mul_le_mul_of_nonneg_right (Mplus_ge hS hu hy j) (le_max_right (u (Sum.inr j)) 0)
    have h2 : rSell P u₀ y j * max (-u (Sum.inr j)) 0
        ≤ max (rSell P u₀ y j) 0 * x1 P y u₀ (Sum.inr j) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_right _ _)).trans
        (mul_le_mul_of_nonneg_left (hx j) (le_max_right _ _))
    linarith
  unfold tanBound
  rw [div_le_div_iff_of_pos_right hW0]
  nlinarith [mul_le_mul_of_nonneg_left hpos hM]

lemma gain_le_tanBound : gain P u₀ y ≤ tanBound P u₀ y := by
  obtain ⟨u, hfe, hg⟩ := gain_le_tan hS hu hy
  exact hg.trans (tan_le_bound hS hu hy hfe)

/-- Part 2 (d): no favorable direction, no gain. -/
lemma gain_zero (h : ∀ j, rBuy P u₀ y j ≤ 0 ∧ rSell P u₀ y j ≤ 0) : gain P u₀ y = 0 := by
  have hk := (setting_parts hS).2.2.2.2.2.1
  have hM : (⨆ k, max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0) = 0 :=
    le_antisymm (Real.iSup_nonpos fun k => max_le (mul_nonpos_of_nonneg_of_nonpos
      (by linarith [(hk (Sum.inr k)).1]) (h k).1) le_rfl) Mplus_nonneg
  have hb : tanBound P u₀ y = 0 := by
    unfold tanBound
    rw [hM]
    simp [max_eq_right (h _).2]
  exact le_antisymm (hb ▸ gain_le_tanBound hS hu hy) (gain_nonneg hS hu hy)

/-- Part 2 (e): `tanBound` is at most claim 023's cap. -/
lemma tanBound_le_cap {U D : ℝ} (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hb : ∀ j t s, NodePath P y t s → gE P j t s - 1 ≤ U ∧ 1 - gE P j t s ≤ D) :
    tanBound P u₀ y ≤ (h1 P u₀ * U + (∑ j, x1 P y u₀ (Sum.inr j)) * (U + D)) / W0 P.D := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hk := (setting_parts hS).2.2.2.2.2.1
  have hxn := (node_nn hS hu hy.1).1
  have hhn := (node_nn hS hu hy.1).2
  have hM : (⨆ k, max ((1 + P.D.kplus (Sum.inr k)) * rBuy P u₀ y k) 0) ≤ U :=
    Real.iSup_le (fun k => max_le (by
      rw [rBuy_eq hS hu hy]
      have := tilt_le hS hu hy (gE P k) (c := 1 + U) fun t s hp => by linarith [(hb k t s hp).1]
      linarith [(hk (Sum.inr k)).1]) hU) hU
  have hS' : ∀ j, max (rSell P u₀ y j) 0 ≤ D := fun j => max_le (by
      rw [rSell_eq hS hu hy]
      have := tilt_ge hS hu hy (gE P j) (c := 1 - D) fun t s hp => by linarith [(hb j t s hp).2]
      linarith [(hk (Sum.inr j)).2.2.1]) hD
  unfold tanBound
  rw [div_le_div_iff_of_pos_right hW0]
  have h1 : (h1 P u₀ + ∑ j, x1 P y u₀ (Sum.inr j)) * (⨆ k, max ((1 + P.D.kplus (Sum.inr k)) *
      rBuy P u₀ y k) 0) ≤ (h1 P u₀ + ∑ j, x1 P y u₀ (Sum.inr j)) * U :=
    mul_le_mul_of_nonneg_left hM (add_nonneg hhn (sum_nonneg fun j _ => hxn _))
  have h2 : ∑ j, x1 P y u₀ (Sum.inr j) * max (rSell P u₀ y j) 0 ≤ (∑ j, x1 P y u₀ (Sum.inr j)) * D := by
    rw [sum_mul]; exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hS' j) (hxn _)
  nlinarith

end TangentSec


section One

variable {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
  (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {y : Obs 1 K} (hy : IsNode P y)
include hS hu hy

omit hS hu hy in
lemma tanLin_one (u : Inst 1 1 → ℝ) :
    tanLin P u₀ y u = (1 + P.D.kplus (Sum.inr 0)) * rBuy P u₀ y 0 * max (u (Sum.inr 0)) 0
      + rSell P u₀ y 0 * max (-u (Sum.inr 0)) 0 := by
  simp [tanLin]

lemma tan_one_le {u : Inst 1 1 → ℝ} (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) :
    tanLin P u₀ y u
      ≤ max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0 := by
  have hA : u (Sum.inl 0) = 0 := hfe.2.2
  have hk := (setting_parts hS).2.2.2.2.2.1 (Sum.inr 0)
  have hbud := hfe.2.1
  rw [sum_inst, hA, cost_E hA] at hbud
  simp only [Fin.sum_univ_one, zero_add] at hbud
  have hx := hfe.1 (Sum.inr 0)
  rw [tanLin_one]
  set v := u (Sum.inr 0)
  set rB := rBuy P u₀ y 0
  set rS := rSell P u₀ y 0
  set h := h1 P u₀
  set x := x1 P y u₀ (Sum.inr 0)
  have hm1 := le_max_left (max (rB * h) (rS * x)) 0
  have hm2 := le_max_right (max (rB * h) (rS * x)) 0
  have hb1 := le_max_left (rB * h) (rS * x)
  have hb2 := le_max_right (rB * h) (rS * x)
  rcases le_or_gt 0 v with hv | hv
  · rw [max_eq_left hv, max_eq_right (by linarith : -v ≤ 0)] at *
    have hvh : (1 + P.D.kplus (Sum.inr 0)) * v ≤ h := by linarith
    rcases le_or_gt 0 rB with hr | hr
    · nlinarith [mul_le_mul_of_nonneg_left hvh hr]
    · nlinarith [mul_nonneg (by linarith [hk.1] : (0 : ℝ) ≤ 1 + P.D.kplus (Sum.inr 0)) hv]
  · rw [max_eq_right hv.le, max_eq_left (by linarith : 0 ≤ -v)] at *
    rcases le_or_gt 0 rS with hr | hr
    · nlinarith [mul_le_mul_of_nonneg_left (by linarith : -v ≤ x) hr]
    · nlinarith

lemma tan_one_attain : ∃ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u ∧ tanLin P u₀ y u
    = max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0 := by
  have hk := (setting_parts hS).2.2.2.2.2.1 (Sum.inr 0)
  have hk1 : 0 < 1 + P.D.kplus (Sum.inr 0) := by linarith [hk.1]
  have hh := (node_nn hS hu hy.1).2
  have hx := (node_nn hS hu hy.1).1 (Sum.inr 0)
  set rB := rBuy P u₀ y 0
  set rS := rSell P u₀ y 0
  by_cases h1c : 0 ≤ rB * h1 P u₀ ∧ rS * x1 P y u₀ (Sum.inr 0) ≤ rB * h1 P u₀
  · refine ⟨_, buy_feas hS hu hy 0 hh le_rfl, ?_⟩
    rw [tanLin_one, Pi.single_eq_same, max_eq_left (div_nonneg hh hk1.le),
      max_eq_left h1c.2, max_eq_left h1c.1]
    simp only [neg_nonpos.mpr (div_nonneg hh hk1.le), max_eq_right, mul_zero, add_zero]
    field_simp
    exact mul_comm _ _
  · by_cases h2c : 0 ≤ rS * x1 P y u₀ (Sum.inr 0)
    · have hlt : rB * h1 P u₀ ≤ rS * x1 P y u₀ (Sum.inr 0) := by
        by_contra hc; push Not at hc; exact h1c ⟨by linarith, hc.le⟩
      refine ⟨_, sell_feas hS hu hy 0 hx le_rfl, ?_⟩
      rw [tanLin_one, Pi.single_eq_same, max_eq_right hlt, max_eq_left h2c,
        max_eq_right (by linarith : -x1 P y u₀ (Sum.inr 0) ≤ 0), neg_neg, max_eq_left hx]
      ring
    · push Not at h2c
      have hlt : rB * h1 P u₀ < 0 := by
        by_contra hc; push Not at hc; exact h1c ⟨hc, by linarith⟩
      refine ⟨0, feas_zero .E (node_nn hS hu hy.1).1 hh, ?_⟩
      rw [tanLin_one, max_eq_right (max_le hlt.le h2c.le)]
      simp

end One

omit [Fintype S] [Fintype T] in
/-- A sum over ETFs of a function vanishing at zero, evaluated at a two-ETF trade. -/
lemma sum_two {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (f : Fin n → ℝ → ℝ) (hf : ∀ i, f i 0 = 0) (a b : ℝ) :
    ∑ i, f i ((Pi.single (Sum.inr k) a + Pi.single (Sum.inr j) b : Inst 1 n → ℝ) (Sum.inr i))
      = f k a + f j b := by
  rw [Finset.sum_eq_add_of_mem k j (mem_univ _) (mem_univ _) (Ne.symm hjk) fun c _ hc => by
    simp [hc.1, hc.2, hf]]
  simp [hjk, Ne.symm hjk]

section NoFav

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y)
include hS hu hy

omit hS hu hy in
lemma tanLin_single (j : Fin n) (v : ℝ) :
    tanLin P u₀ y (Pi.single (Sum.inr j) v) = (1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j * max v 0
      + rSell P u₀ y j * max (-v) 0 := by
  unfold tanLin
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- Selling ETF `k` to buy it back is never favorable. -/
lemma round_trip (k : Fin n) :
    rSell P u₀ y k + (1 - P.D.kminus (Sum.inr k)) * rBuy P u₀ y k ≤ 0 := by
  obtain ⟨_, _, _, _, _, hk, _, _, _, hg⟩ := setting_parts hS
  have hk1 : 0 < 1 + P.D.kplus (Sum.inr k) := by linarith [(hk (Sum.inr k)).1]
  have htm : 0 ≤ tiltMean P u₀ y (gE P k) :=
    tilt_ge hS hu hy _ fun t s _ => (hg t s (Sum.inr k)).le
  have hb : rBuy P u₀ y k
      = (tiltMean P u₀ y (gE P k) - 1 - P.D.kplus (Sum.inr k)) / (1 + P.D.kplus (Sum.inr k)) := by
    rw [← rBuy_eq hS hu hy k]; field_simp
  rw [rSell_eq hS hu hy, hb]
  have key : (1 - P.D.kminus (Sum.inr k) - tiltMean P u₀ y (gE P k) + (1 - P.D.kminus (Sum.inr k)) *
      ((tiltMean P u₀ y (gE P k) - 1 - P.D.kplus (Sum.inr k)) / (1 + P.D.kplus (Sum.inr k))))
      * (1 + P.D.kplus (Sum.inr k))
      = -(tiltMean P u₀ y (gE P k) * (P.D.kminus (Sum.inr k) + P.D.kplus (Sum.inr k))) := by
    field_simp; ring
  nlinarith [mul_nonneg htm (add_nonneg (hk (Sum.inr k)).2.2.1 (hk (Sum.inr k)).1)]

/-- No adjustable wealth in a favorable direction makes every first-order gain nonpositive. -/
lemma noFav_tan (hN : NoFavorable P u₀ y) {u : Inst 1 n → ℝ}
    (hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) : tanLin P u₀ y u ≤ 0 := by
  obtain ⟨h1c, h2c, h3c⟩ := hN
  have hk := (setting_parts hS).2.2.2.2.2.1
  have hA : u (Sum.inl 0) = 0 := hfe.2.2
  have hbud := hfe.2.1
  rw [sum_inst, hA, zero_add, cost_E hA] at hbud
  have hx : ∀ k, max (-u (Sum.inr k)) 0 ≤ x1 P y u₀ (Sum.inr k) := fun k =>
    max_le (by linarith [hfe.1 (Sum.inr k)]) ((node_nn hS hu hy.1).1 _)
  have hsplit : ∀ j, u (Sum.inr j) = max (u (Sum.inr j)) 0 - max (-u (Sum.inr j)) 0 := fun j =>
    (max_zero_sub_eq_self _).symm
  by_cases hpos : ∃ j, 0 < rBuy P u₀ y j
  · obtain ⟨j0, hj0⟩ := hpos
    have hh0 : h1 P u₀ = 0 := (h1c j0).resolve_right (not_le.mpr hj0)
    obtain ⟨js, -, hjs⟩ := Finset.exists_max_image univ (rBuy P u₀ y) ⟨j0, mem_univ _⟩
    have hR : 0 < rBuy P u₀ y js := lt_of_lt_of_le hj0 (hjs j0 (mem_univ _))
    have hb2 : ∑ j, (1 + P.D.kplus (Sum.inr j)) * max (u (Sum.inr j)) 0
        ≤ ∑ k, (1 - P.D.kminus (Sum.inr k)) * max (-u (Sum.inr k)) 0 := by
      rw [hh0] at hbud
      have e : ∀ j, (1 + P.D.kplus (Sum.inr j)) * max (u (Sum.inr j)) 0
          - (1 - P.D.kminus (Sum.inr j)) * max (-u (Sum.inr j)) 0
          = u (Sum.inr j) + (P.D.kplus (Sum.inr j) * max (u (Sum.inr j)) 0
            + P.D.kminus (Sum.inr j) * max (-u (Sum.inr j)) 0) := fun j => by
        linear_combination (-1 : ℝ) * hsplit j
      have hs := sum_congr (s₁ := (univ : Finset (Fin n))) rfl fun j (_ : j ∈ univ) => e j
      rw [sum_sub_distrib, sum_add_distrib] at hs
      linarith
    have t1 : tanLin P u₀ y u ≤ rBuy P u₀ y js * ∑ j, (1 + P.D.kplus (Sum.inr j)) * max (u (Sum.inr j)) 0
        + ∑ k, rSell P u₀ y k * max (-u (Sum.inr k)) 0 := by
      unfold tanLin
      rw [mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_right (hjs j (mem_univ _))
        (mul_nonneg (by linarith [(hk (Sum.inr j)).1] : (0 : ℝ) ≤ 1 + P.D.kplus (Sum.inr j))
          (le_max_right (u (Sum.inr j)) 0))
      nlinarith
    have t2 : rBuy P u₀ y js * ∑ k, (1 - P.D.kminus (Sum.inr k)) * max (-u (Sum.inr k)) 0
        + ∑ k, rSell P u₀ y k * max (-u (Sum.inr k)) 0 ≤ 0 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_nonpos fun k _ => ?_
      rcases (le_max_right (-u (Sum.inr k)) 0).lt_or_eq with hv | hv
      · have hsw := h3c k (lt_of_lt_of_le hv (hx k)) js
        nlinarith
      · rw [← hv]; simp
    nlinarith [mul_le_mul_of_nonneg_left hb2 hR.le]
  · push Not at hpos
    unfold tanLin
    refine sum_nonpos fun j _ => ?_
    have t1 : (1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j * max (u (Sum.inr j)) 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
        (by linarith [(hk (Sum.inr j)).1]) (hpos j)) (le_max_right _ _)
    have t2 : rSell P u₀ y j * max (-u (Sum.inr j)) 0 ≤ 0 := by
      rcases h2c j with h0 | h0
      · have := hx j; rw [h0] at this
        rw [le_antisymm this (le_max_right _ _), mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg h0 (le_max_right _ _)
    linarith

/-- If every first-order gain is nonpositive, the node has no adjustable wealth in a favorable
direction. -/
lemma tan_noFav (hT : ∀ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u → tanLin P u₀ y u ≤ 0) :
    NoFavorable P u₀ y := by
  have hk := (setting_parts hS).2.2.2.2.2.1
  have hh := (node_nn hS hu hy.1).2
  have hxn := (node_nn hS hu hy.1).1
  refine ⟨fun j => ?_, fun k => ?_, fun k hk0 j => ?_⟩
  · by_contra hc; push Not at hc
    have hh' : 0 < h1 P u₀ := lt_of_le_of_ne hh (Ne.symm hc.1)
    have hk1 : 0 < 1 + P.D.kplus (Sum.inr j) := by linarith [(hk (Sum.inr j)).1]
    have := hT _ (buy_feas hS hu hy j hh le_rfl)
    rw [tanLin_single, max_eq_left (div_nonneg hh hk1.le),
      max_eq_right (neg_nonpos.mpr (div_nonneg hh hk1.le))] at this
    have e : (1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j * (h1 P u₀ / (1 + P.D.kplus (Sum.inr j)))
        = rBuy P u₀ y j * h1 P u₀ := by field_simp
    nlinarith [mul_pos hc.2 hh']
  · by_contra hc; push Not at hc
    have hx' : 0 < x1 P y u₀ (Sum.inr k) := lt_of_le_of_ne (hxn _) (Ne.symm hc.1)
    have := hT _ (sell_feas hS hu hy k (hxn _) le_rfl)
    rw [tanLin_single, max_eq_right (neg_nonpos.mpr (hxn _)), neg_neg, max_eq_left (hxn _)] at this
    nlinarith [mul_pos hc.2 hx']
  · by_cases hjk : j = k
    · subst hjk; exact round_trip hS hu hy j
    by_contra hc; push Not at hc
    set x := x1 P y u₀ (Sum.inr k)
    have hkj1 : 0 < 1 + P.D.kplus (Sum.inr j) := by linarith [(hk (Sum.inr j)).1]
    have hkm : 0 ≤ 1 - P.D.kminus (Sum.inr k) := by linarith [(hk (Sum.inr k)).2.2.2]
    set w := (1 - P.D.kminus (Sum.inr k)) * x / (1 + P.D.kplus (Sum.inr j))
    have hw : 0 ≤ w := div_nonneg (mul_nonneg hkm hk0.le) hkj1.le
    set u : Inst 1 n → ℝ := Pi.single (Sum.inr k) (-x) + Pi.single (Sum.inr j) w
    have hA : u (Sum.inl 0) = 0 := by simp [u]
    have hsum : ∑ i, u (Sum.inr i) = -x + w := sum_two hjk (fun _ v => v) (fun _ => rfl) (-x) w
    have hcost : cost P.D u = P.D.kminus (Sum.inr k) * x + P.D.kplus (Sum.inr j) * w := by
      rw [cost_E hA]
      rw [sum_two hjk (fun i v => P.D.kplus (Sum.inr i) * max v 0 + P.D.kminus (Sum.inr i) * max (-v) 0)
        (fun _ => by simp) (-x) w]
      rw [max_eq_right (neg_nonpos.mpr hk0.le), neg_neg, max_eq_left hk0.le, max_eq_left hw,
        max_eq_right (neg_nonpos.mpr hw)]
      ring
    have hfe : Feas1 P .E (x1 P y u₀) (h1 P u₀) u := by
      refine ⟨fun i => ?_, ?_, hA⟩
      · rcases i with i | i
        · simpa [u] using hxn (Sum.inl i)
        · by_cases hik : i = k
          · subst hik; simp [u, Ne.symm hjk, x]
          · by_cases hij : i = j
            · subst hij; simp [u, hik]; linarith [hxn (Sum.inr i)]
            · simp [u, hik, hij]; exact hxn _
      · rw [sum_inst, hA, zero_add, hsum, hcost]
        have : w * (1 + P.D.kplus (Sum.inr j)) = (1 - P.D.kminus (Sum.inr k)) * x := by
          simp only [w]; field_simp
        nlinarith
    have hT' := hT u hfe
    have hlin : tanLin P u₀ y u
        = x * (rSell P u₀ y k + (1 - P.D.kminus (Sum.inr k)) * rBuy P u₀ y j) := by
      unfold tanLin
      rw [sum_two hjk (fun i v => (1 + P.D.kplus (Sum.inr i)) * rBuy P u₀ y i * max v 0
        + rSell P u₀ y i * max (-v) 0) (fun _ => by simp) (-x) w]
      rw [max_eq_right (neg_nonpos.mpr hk0.le), neg_neg, max_eq_left hk0.le, max_eq_left hw,
        max_eq_right (neg_nonpos.mpr hw)]
      simp only [w]
      field_simp
      ring
    rw [hlin] at hT'
    nlinarith [mul_pos hk0 hc]

lemma noFav_gain (hN : NoFavorable P u₀ y) : gain P u₀ y = 0 := by
  obtain ⟨u, hfe, hg⟩ := gain_le_tan hS hu hy
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have := div_nonpos_of_nonpos_of_nonneg (noFav_tan hS hu hy hN hfe) hW0.le
  exact le_antisymm (hg.trans this) (gain_nonneg hS hu hy)

end NoFav

lemma noFav_one {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {y : Obs 1 K} (hy : IsNode P y) :
    NoFavorable P u₀ y ↔ (h1 P u₀ = 0 ∨ rBuy P u₀ y 0 ≤ 0) ∧
      (x1 P y u₀ (Sum.inr 0) = 0 ∨ rSell P u₀ y 0 ≤ 0) := by
  refine ⟨fun h => ⟨h.1 0, h.2.1 0⟩, fun h => ⟨fun j => ?_, fun k => ?_, fun k _ j => ?_⟩⟩
  · obtain rfl : j = 0 := Subsingleton.elim _ _; exact h.1
  · obtain rfl : k = 0 := Subsingleton.elim _ _; exact h.2
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact round_trip hS hu hy 0

theorem tangentCap : TangentCap := by
  refine ⟨fun n K S T _ _ P hS u₀ hu y hy => ⟨gain_le_tan hS hu hy,
    fun u hfe => tan_le_bound hS hu hy hfe, gain_le_tanBound hS hu hy,
    ⟨fun hN u hfe => noFav_tan hS hu hy hN hfe, tan_noFav hS hu hy⟩, noFav_gain hS hu hy,
    gain_zero hS hu hy,
    fun U D hU hD hb => tanBound_le_cap hS hu hy hU hD hb⟩, fun K S T _ _ P hS u₀ hu y hy =>
    ⟨fun u hfe => tan_one_le hS hu hy hfe, tan_one_attain hS hu hy, ?_⟩⟩
  obtain ⟨u, hfe, hg⟩ := gain_le_tan hS hu hy
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  exact ⟨hg.trans (div_le_div_of_nonneg_right (tan_one_le hS hu hy hfe) hW0.le), noFav_one hS hu hy⟩

/-! ### Part 3: the curvature cap -/

section Core

variable {ι : Type} [Fintype ι]

omit [Fintype T] [Fintype S] in
lemma wsum_expand (b Z : ι → ℝ) (m : ℝ) :
    ∑ i, b i * (Z i - m) ^ 2 = ∑ i, b i * Z i ^ 2 - 2 * m * ∑ i, b i * Z i + m ^ 2 * ∑ i, b i := by
  have e : ∀ i, b i * (Z i - m) ^ 2 = b i * Z i ^ 2 - 2 * m * (b i * Z i) + m ^ 2 * b i := fun i => by
    ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum]

omit [Fintype T] [Fintype S] in
/-- A variance lower bound from a pointwise weight lower bound. -/
lemma var_lower {b pm Z : ι → ℝ} (hpm1 : ∑ i, pm i = 1)
    {c : ℝ} (hc : 0 ≤ c) (hF : 0 < ∑ i, b i) (hbl : ∀ i, c * (∑ k, b k) * pm i ≤ b i) :
    c * (∑ i, pm i * Z i ^ 2 - (∑ i, pm i * Z i) ^ 2) * (∑ i, b i) ^ 2
      ≤ (∑ i, b i) * ∑ i, b i * Z i ^ 2 - (∑ i, b i * Z i) ^ 2 := by
  set F := ∑ i, b i
  set m := (∑ i, b i * Z i) / F
  have h1 : F * ∑ i, b i * Z i ^ 2 - (∑ i, b i * Z i) ^ 2 = F * ∑ i, b i * (Z i - m) ^ 2 := by
    rw [wsum_expand]; simp only [m]; field_simp; ring
  have h2 : c * F * ∑ i, pm i * (Z i - m) ^ 2 ≤ ∑ i, b i * (Z i - m) ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hbl i) (sq_nonneg _)
  have h3 : ∑ i, pm i * Z i ^ 2 - (∑ i, pm i * Z i) ^ 2 ≤ ∑ i, pm i * (Z i - m) ^ 2 := by
    rw [wsum_expand, hpm1]
    nlinarith [sq_nonneg (∑ i, pm i * Z i - m)]
  rw [h1]
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hc hF.le)
  nlinarith

omit [Fintype T] [Fintype S] in
lemma expsum_pos {a Z : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i) (ρ x : ℝ) :
    0 < ∑ i, a i * Real.exp (-ρ * x * Z i) := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
    by_contra h; push Not at h
    have : ∑ i, a i = 0 := sum_eq_zero fun i _ => le_antisymm (h i) (ha i)
    linarith
  exact lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
    (single_le_sum (f := fun i => a i * Real.exp (-ρ * x * Z i))
      (fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le) (mem_univ i))

omit [Fintype T] [Fintype S] in
lemma hasDeriv_F (a Z : ι → ℝ) (ρ x : ℝ) :
    HasDerivAt (fun x => ∑ i, a i * Real.exp (-ρ * x * Z i))
      (-ρ * ∑ i, a i * Z i * Real.exp (-ρ * x * Z i)) x := by
  have := HasDerivAt.sum (u := univ) (A := fun i x => a i * Real.exp (-ρ * x * Z i))
    (A' := fun i => a i * (Real.exp (-ρ * x * Z i) * (-ρ * 1 * Z i))) (x := x) fun i _ =>
      ((((hasDerivAt_id x).const_mul (-ρ)).mul_const (Z i)).exp).const_mul (a i)
  convert this using 1
  · funext x; simp
  · rw [mul_sum]; exact sum_congr rfl fun i _ => by ring

omit [Fintype T] [Fintype S] in
lemma hasDeriv_F1 (a Z : ι → ℝ) (ρ x : ℝ) :
    HasDerivAt (fun x => -ρ * ∑ i, a i * Z i * Real.exp (-ρ * x * Z i))
      (ρ ^ 2 * ∑ i, a i * Z i ^ 2 * Real.exp (-ρ * x * Z i)) x := by
  have := (hasDeriv_F (fun i => a i * Z i) Z ρ x).const_mul (-ρ)
  convert this using 1
  rw [mul_sum, mul_sum, mul_sum]; exact sum_congr rfl fun i _ => by ring

omit [Fintype T] [Fintype S] in
/-- The second-order core: if the tilted variance of `Z` is at least `v` on `[0, E]`, then
`ln Σ a e^{-ρεZ} ≥ ln Σ a - ρ ε r + ρ² v ε²/2` there, with `r` the `a`-weighted mean of `Z`. -/
lemma curv_core {a Z : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i) {ρ v E : ℝ}
    (hv : ∀ ε ∈ Set.Icc 0 E,
      v * (∑ i, a i * Real.exp (-ρ * ε * Z i)) ^ 2 ≤
        (∑ i, a i * Real.exp (-ρ * ε * Z i)) * (∑ i, a i * Z i ^ 2 * Real.exp (-ρ * ε * Z i))
        - (∑ i, a i * Z i * Real.exp (-ρ * ε * Z i)) ^ 2)
    {ε : ℝ} (hε : ε ∈ Set.Icc 0 E) :
    Real.log (∑ i, a i) - ρ * ε * ((∑ i, a i * Z i) / ∑ i, a i) + ρ ^ 2 * v * ε ^ 2 / 2
      ≤ Real.log (∑ i, a i * Real.exp (-ρ * ε * Z i)) := by
  set F := fun x => ∑ i, a i * Real.exp (-ρ * x * Z i)
  set F1 := fun x => -ρ * ∑ i, a i * Z i * Real.exp (-ρ * x * Z i)
  set F2 := fun x => ρ ^ 2 * ∑ i, a i * Z i ^ 2 * Real.exp (-ρ * x * Z i)
  set r := (∑ i, a i * Z i) / ∑ i, a i
  have hFp : ∀ x, 0 < F x := fun x => expsum_pos ha hpos ρ x
  have dF : ∀ x, HasDerivAt F (F1 x) x := fun x => hasDeriv_F a Z ρ x
  have dF1 : ∀ x, HasDerivAt F1 (F2 x) x := fun x => hasDeriv_F1 a Z ρ x
  set g1 := fun x => F1 x / F x + ρ * r - ρ ^ 2 * v * x
  set G := fun x => Real.log (F x) - Real.log (F 0) + ρ * r * x - ρ ^ 2 * v * x ^ 2 / 2
  have dg1 : ∀ x, HasDerivAt g1 ((F2 x * F x - F1 x * F1 x) / F x ^ 2 - ρ ^ 2 * v) x := fun x => by
    have := (((dF1 x).div (dF x) (hFp x).ne').add_const (ρ * r)).sub
      ((hasDerivAt_id x).const_mul (ρ ^ 2 * v))
    convert this using 1
    · funext y; simp only [g1, Pi.sub_apply, Pi.div_apply, id]
    · ring
  have dG : ∀ x, HasDerivAt G (g1 x) x := fun x => by
    have := ((((dF x).log (hFp x).ne').sub_const (Real.log (F 0))).add
      ((hasDerivAt_id x).const_mul (ρ * r))).sub
      (((hasDerivAt_id x).pow 2).const_mul (ρ ^ 2 * v / 2))
    convert this using 1
    · funext y; simp only [G, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]; ring
    · simp only [g1, id]; ring
  have hD : Convex ℝ (Set.Icc (0 : ℝ) E) := convex_Icc 0 E
  have hint : interior (Set.Icc (0 : ℝ) E) ⊆ Set.Icc 0 E := interior_subset
  have hmono1 : MonotoneOn g1 (Set.Icc 0 E) :=
    monotoneOn_of_hasDerivWithinAt_nonneg hD (fun x _ => (dg1 x).continuousAt.continuousWithinAt)
      (fun x _ => (dg1 x).hasDerivWithinAt) fun x hx => by
        have hvx := hv x (hint hx)
        have hF2 : F2 x * F x - F1 x * F1 x = ρ ^ 2 * ((∑ i, a i * Real.exp (-ρ * x * Z i)) *
            (∑ i, a i * Z i ^ 2 * Real.exp (-ρ * x * Z i))
            - (∑ i, a i * Z i * Real.exp (-ρ * x * Z i)) ^ 2) := by simp only [F, F1, F2]; ring
        rw [hF2, sub_nonneg, le_div_iff₀ (pow_pos (hFp x) 2)]
        simp only [F]
        nlinarith [sq_nonneg ρ]
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 E := ⟨le_rfl, hε.1.trans hε.2⟩
  have hg10 : g1 0 = 0 := by
    simp only [g1, F1, F, r, mul_zero, zero_mul, Real.exp_zero, mul_one, sub_zero]
    field_simp
    ring
  have hmonoG : MonotoneOn G (Set.Icc 0 E) :=
    monotoneOn_of_hasDerivWithinAt_nonneg hD (fun x _ => (dG x).continuousAt.continuousWithinAt)
      (fun x _ => (dG x).hasDerivWithinAt) fun x hx => by
        have := hmono1 h0mem (hint hx) (hint hx).1
        rw [hg10] at this; exact this
  have hG := hmonoG h0mem hε hε.1
  have hF0 : F 0 = ∑ i, a i := by simp [F]
  simp only [G, sub_self, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at hG
  rw [hF0] at hG
  simp only [F] at hG
  nlinarith

/-- `ε r - ρ v ε²/2 ≤ q(r, v)` on `[0, H]`. -/
lemma le_curvBound {ρ r v H ε : ℝ} (hρ : 0 < ρ) (hv : 0 ≤ v) (hε : 0 ≤ ε) (hεH : ε ≤ H) :
    ε * r - ρ * v * ε ^ 2 / 2 ≤ curvBound ρ r v H := by
  unfold curvBound
  split_ifs with h0 h
  · nlinarith [mul_nonneg (mul_nonneg hρ.le hv) (sq_nonneg ε)]
  · rcases hv.lt_or_eq with hv' | hv'
    · rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (r - ρ * v * ε)]
    · subst hv'
      simp only [mul_zero, zero_mul] at h ⊢
      simp only [zero_div, div_zero]
      nlinarith
  · push Not at h
    nlinarith [mul_nonneg (by linarith : 0 ≤ H - ε) (mul_nonneg hρ.le hv),
      mul_nonneg (mul_nonneg hρ.le hv) (by linarith : (0 : ℝ) ≤ H - ε)]

end Core

section Curv

variable (hS : M3Setting P) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀)
  {y : Obs n K} (hy : IsNode P y)
include hS hu hy

lemma pmass_sum : ∑ p : T × S, pmass P y p.1 p.2 = 1 := by
  obtain ⟨_, _, hq1, _⟩ := setting_parts hS
  rw [Fintype.sum_prod_type]
  simp only [pmass, ← mul_sum, hq1, mul_one]
  exact post_sum hS hy.2

omit hu hy in
lemma pmass_nonneg (p : T × S) : 0 ≤ pmass P y p.1 p.2 :=
  mul_nonneg (post_nonneg hS y p.1) ((setting_parts hS).2.1 p.2)

omit hu hy in
lemma pmass_path {p : T × S} (h : 0 < pmass P y p.1 p.2) : NodePath P y p.1 p.2 :=
  tw_path hS (u₀ := (0 : Inst 1 n → ℝ)) (mul_pos h (Real.exp_pos _))

lemma varQ_eq (Z : T → S → ℝ) : varQ P y Z
    = ∑ p : T × S, pmass P y p.1 p.2 * Z p.1 p.2 ^ 2 - (∑ p : T × S, pmass P y p.1 p.2 * Z p.1 p.2) ^ 2 := by
  unfold varQ; rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

lemma varQ_nonneg (Z : T → S → ℝ) : 0 ≤ varQ P y Z := by
  rw [varQ_eq hS hu hy]
  have h := wsum_expand (fun p : T × S => pmass P y p.1 p.2) (fun p => Z p.1 p.2)
    (∑ p : T × S, pmass P y p.1 p.2 * Z p.1 p.2)
  rw [pmass_sum hS hu hy] at h
  have : 0 ≤ ∑ p : T × S, pmass P y p.1 p.2 * (Z p.1 p.2 - ∑ p : T × S, pmass P y p.1 p.2 * Z p.1 p.2) ^ 2 :=
    sum_nonneg fun p _ => mul_nonneg (pmass_nonneg hS p) (sq_nonneg _)
  nlinarith

/-- The curvature bound at a node for a trade whose normalized wealth change is `ε Z`. -/
lemma node_curv {Z : T → S → ℝ} {dW σ H : ℝ} (hσ : 0 ≤ σ)
    (hW : ∀ t s t' s', NodePath P y t s → NodePath P y t' s' → WN P u₀ y t s - WN P u₀ y t' s' ≤ dW)
    (hZ : ∀ t s t' s', NodePath P y t s → NodePath P y t' s' → Z t s - Z t' s' ≤ 2 * σ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεH : ε ≤ H) {u : Inst 1 n → ℝ}
    (hD : ∀ t s, condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D - WN P u₀ y t s = ε * Z t s) :
    tradeCE P u₀ y u - nodeCE P .N u₀ y
      ≤ curvBound P.rho (tiltMean P u₀ y Z) (Real.exp (-P.rho * (dW + 2 * σ * H)) * varQ P y Z) H := by
  have hρ := hS.1
  have hpos := tw_sum_pos hS hu hy
  set a : T × S → ℝ := tw P u₀ y
  set Zp : T × S → ℝ := fun p => Z p.1 p.2
  set c := Real.exp (-P.rho * (dW + 2 * σ * H))
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  -- the tilted-variance lower bound on [0, H]
  have hv : ∀ e ∈ Set.Icc 0 H,
      c * varQ P y Z * (∑ p, a p * Real.exp (-P.rho * e * Zp p)) ^ 2 ≤
        (∑ p, a p * Real.exp (-P.rho * e * Zp p)) * (∑ p, a p * Zp p ^ 2 * Real.exp (-P.rho * e * Zp p))
        - (∑ p, a p * Zp p * Real.exp (-P.rho * e * Zp p)) ^ 2 := by
    intro e he
    set b : T × S → ℝ := fun p => a p * Real.exp (-P.rho * e * Zp p)
    have hb : ∀ p, 0 ≤ b p := fun p => mul_nonneg (tw_nonneg hS p) (Real.exp_pos _).le
    have hF : 0 < ∑ p, b p := expsum_pos (tw_nonneg hS) hpos _ _
    have hbl : ∀ p, c * (∑ k, b k) * pmass P y p.1 p.2 ≤ b p := by
      intro p
      rcases (pmass_nonneg hS p).lt_or_eq with hp | hp
      · have hpp := pmass_path hS hp
        set X := fun k : T × S => WN P u₀ y k.1 k.2 + e * Zp k
        have hbX : ∀ k, b k = pmass P y k.1 k.2 * Real.exp (-P.rho * X k) := fun k => by
          simp only [b, a, tw, pmass, X, Zp]
          rw [mul_assoc (post P y k.1 * P.D.q k.2), ← Real.exp_add]; ring_nf
        have hFle : ∑ k, b k ≤ Real.exp (-P.rho * X p) * Real.exp (P.rho * (dW + 2 * σ * e)) := by
          have : ∀ k, b k ≤ pmass P y k.1 k.2 * (Real.exp (-P.rho * X p) *
              Real.exp (P.rho * (dW + 2 * σ * e))) := fun k => by
            rw [hbX]
            rcases (pmass_nonneg hS k).lt_or_eq with hk | hk
            · have hkp := pmass_path hS hk
              refine mul_le_mul_of_nonneg_left ?_ hk.le
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have h1 := hW p.1 p.2 k.1 k.2 hpp hkp
              have h2 := mul_le_mul_of_nonneg_left (hZ p.1 p.2 k.1 k.2 hpp hkp) he.1
              simp only [X, Zp] at h2 ⊢
              nlinarith
            · rw [← hk]; simp
          calc ∑ k, b k ≤ ∑ k, pmass P y k.1 k.2 * (Real.exp (-P.rho * X p) *
                Real.exp (P.rho * (dW + 2 * σ * e))) := sum_le_sum fun k _ => this k
            _ = _ := by rw [← sum_mul, pmass_sum hS hu hy, one_mul]
        have hce : c * Real.exp (P.rho * (dW + 2 * σ * e)) ≤ 1 := by
          simp only [c]
          rw [← Real.exp_add, Real.exp_le_one_iff]
          nlinarith [mul_le_mul_of_nonneg_left he.2 (mul_nonneg hρ.le hσ)]
        rw [hbX p]
        calc c * (∑ k, b k) * pmass P y p.1 p.2
            ≤ c * (Real.exp (-P.rho * X p) * Real.exp (P.rho * (dW + 2 * σ * e))) * pmass P y p.1 p.2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFle hc0) hp.le
          _ = (c * Real.exp (P.rho * (dW + 2 * σ * e))) * (pmass P y p.1 p.2 * Real.exp (-P.rho * X p)) := by
              ring
          _ ≤ 1 * (pmass P y p.1 p.2 * Real.exp (-P.rho * X p)) :=
              mul_le_mul_of_nonneg_right hce (mul_nonneg hp.le (Real.exp_pos _).le)
          _ = _ := one_mul _
      · rw [← hp, mul_zero]; exact hb p
    have hvl := var_lower (Z := Zp) (pmass_sum hS hu hy) hc0 hF hbl
    rw [← varQ_eq hS hu hy] at hvl
    have e1 : ∑ p, b p * Zp p ^ 2 = ∑ p, a p * Zp p ^ 2 * Real.exp (-P.rho * e * Zp p) :=
      sum_congr rfl fun p _ => by simp only [b]; ring
    have e2 : ∑ p, b p * Zp p = ∑ p, a p * Zp p * Real.exp (-P.rho * e * Zp p) :=
      sum_congr rfl fun p _ => by simp only [b]; ring
    rw [e1, e2] at hvl
    linarith
  have hcore := curv_core (tw_nonneg hS) hpos hv ⟨hε0, hεH⟩
  have hcond : -condObj P (post P y) (x1 P y u₀) (h1 P u₀) u = ∑ p, a p * Real.exp (-P.rho * ε * Zp p) := by
    rw [condObj_tw hS u]
    exact sum_congr rfl fun p _ => by rw [hD]; simp only [Zp, a]; ring_nf
  have hr : (∑ p, a p * Zp p) / ∑ p, a p = tiltMean P u₀ y Z := by
    rw [tilt_eq hS hu hy, sum_div]; exact sum_congr rfl fun p _ => by ring
  rw [hr] at hcore
  have hlogs := hcore
  have hbound := le_curvBound (r := tiltMean P u₀ y Z) hρ
    (mul_nonneg hc0 (varQ_nonneg hS hu hy Z)) hε0 hεH
  unfold tradeCE
  rw [hcond, nodeCEN_tw hS hu hy]
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  have key := mul_le_mul_of_nonneg_left hlogs hρi.le
  have e : 1 / P.rho * (Real.log (∑ p, a p) - P.rho * ε * tiltMean P u₀ y Z
      + P.rho ^ 2 * (c * varQ P y Z) * ε ^ 2 / 2)
      = 1 / P.rho * Real.log (∑ p, a p) - (ε * tiltMean P u₀ y Z - P.rho * (c * varQ P y Z) * ε ^ 2 / 2) := by
    field_simp; ring
  rw [e] at key
  linarith

end Curv

lemma exists_path (hS : M3Setting P) {y : Obs n K} (hy : IsNode P y) :
    ∃ t s, NodePath P y t s := by
  obtain ⟨p, hp⟩ : ∃ p : T × S, 0 < pmass P y p.1 p.2 := by
    by_contra h; push Not at h
    have h0 : ∑ p : T × S, pmass P y p.1 p.2 = 0 :=
      sum_eq_zero fun p _ => le_antisymm (h p) (pmass_nonneg hS p)
    have h1 := pmass_sum hS (u₀ := (0 : Inst 1 n → ℝ)) (by
      exact feas_zero .F (fun i => (setting_parts hS).2.2.2.2.2.2.1 i) (setting_parts hS).2.2.2.2.2.2.2.1) hy
    linarith
  exact ⟨p.1, p.2, pmass_path hS hp⟩

omit [Fintype S] [Fintype T] in
lemma single_one {u : Inst 1 1 → ℝ} (hA : u (Sum.inl 0) = 0) :
    u = Pi.single (Sum.inr 0) (u (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
  · simp [hA]
  · simp

section CurvOne

variable {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
  (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {y : Obs 1 K} (hy : IsNode P y) {dW gl gu : ℝ}
  (hV : ValidAt P u₀ y 0 dW gl gu)
include hS hu hy hV

lemma gl_le_gu : 0 ≤ (gu - gl) / 2 := by
  obtain ⟨t, s, hp⟩ := exists_path hS hy
  have := hV.2 t s hp
  linarith [this.1, this.2]

lemma curv_buy {ε : ℝ} (hε0 : 0 ≤ ε) (hεH : ε ≤ h1 P u₀ / W0 P.D) :
    tradeCE P u₀ y (Pi.single (Sum.inr 0) (ε * W0 P.D / (1 + P.D.kplus (Sum.inr 0))))
      - nodeCE P .N u₀ y
    ≤ curvBound P.rho (rBuy P u₀ y 0)
        (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (h1 P u₀ / W0 P.D)))
          * varQ P y (ZBuy P 0)) (h1 P u₀ / W0 P.D) := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hk := ((setting_parts hS).2.2.2.2.2.1 (Sum.inr 0)).1
  have hσ := gl_le_gu hS hu hy hV
  refine node_curv hS hu hy hσ hV.1 (fun t s t' s' hp hp' => ?_) hε0 hεH fun t s => ?_
  · have h1 := hV.2 t s hp
    have h2 := hV.2 t' s' hp'
    rw [← sub_div, div_le_iff₀ (by linarith)]
    nlinarith
  · rw [buy_W hS hu hy 0 (mul_nonneg hε0 hW0.le), WN]
    field_simp
    ring

lemma curv_sell {ε : ℝ} (hε0 : 0 ≤ ε) (hεH : ε ≤ x1 P y u₀ (Sum.inr 0) / W0 P.D) :
    tradeCE P u₀ y (Pi.single (Sum.inr 0) (-(ε * W0 P.D))) - nodeCE P .N u₀ y
    ≤ curvBound P.rho (rSell P u₀ y 0)
        (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (x1 P y u₀ (Sum.inr 0) / W0 P.D)))
          * varQ P y (ZSell P 0)) (x1 P y u₀ (Sum.inr 0) / W0 P.D) := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hσ := gl_le_gu hS hu hy hV
  refine node_curv hS hu hy hσ hV.1 (fun t s t' s' hp hp' => ?_) hε0 hεH fun t s => ?_
  · have h1 := hV.2 t s hp
    have h2 := hV.2 t' s' hp'
    linarith
  · rw [sell_W hS hu hy 0 (mul_nonneg hε0 hW0.le), WN]
    field_simp
    ring

lemma gain_le_curv : gain P u₀ y ≤ curvCap P u₀ y dW gl gu := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hk := ((setting_parts hS).2.2.2.2.2.1 (Sum.inr 0)).1
  obtain ⟨u, hfe, -, hV1⟩ := cond_attain hS .E (post P y) (node_nn hS hu hy.1).1 (node_nn hS hu hy.1).2
  have hE : nodeCE P .E u₀ y = tradeCE P u₀ y u := by unfold nodeCE tradeCE; rw [hV1]
  have hA : u (Sum.inl 0) = 0 := hfe.2.2
  have hsu := single_one hA
  have hbud := hfe.2.1
  rw [sum_inst, hA, cost_E hA] at hbud
  simp only [Fin.sum_univ_one, zero_add] at hbud
  have hx := hfe.1 (Sum.inr 0)
  unfold gain curvCap
  rw [hE]
  set v := u (Sum.inr 0)
  rcases le_or_gt 0 v with hv | hv
  · rw [max_eq_left hv, max_eq_right (by linarith : -v ≤ 0)] at hbud
    set ε := v * (1 + P.D.kplus (Sum.inr 0)) / W0 P.D
    have hε0 : 0 ≤ ε := by positivity
    have hεH : ε ≤ h1 P u₀ / W0 P.D := by
      rw [div_le_div_iff_of_pos_right hW0]; linarith
    have hveq : u = Pi.single (Sum.inr 0) (ε * W0 P.D / (1 + P.D.kplus (Sum.inr 0))) := by
      rw [hsu]; congr 1; simp only [ε]; field_simp
    rw [hveq]
    exact (curv_buy hS hu hy hV hε0 hεH).trans (le_max_left _ _)
  · set ε := -v / W0 P.D
    have hε0 : 0 ≤ ε := div_nonneg (by linarith) hW0.le
    have hεH : ε ≤ x1 P y u₀ (Sum.inr 0) / W0 P.D := by
      rw [div_le_div_iff_of_pos_right hW0]; linarith
    have hveq : u = Pi.single (Sum.inr 0) (-(ε * W0 P.D)) := by
      rw [hsu]; congr 1; simp only [ε]; field_simp
    rw [hveq]
    exact (curv_sell hS hu hy hV hε0 hεH).trans (le_max_right _ _)

end CurvOne

theorem curvatureCap : CurvatureCap := fun _ _ _ _ _ _ hS _ hu _ hy _ _ _ hV =>
  ⟨fun _ h0 h1 => curv_buy hS hu hy hV h0 h1, fun _ h0 h1 => curv_sell hS hu hy hV h0 h1,
    gain_le_curv hS hu hy hV⟩

/-! ### Part 4: aggregation and sign conditions -/

lemma gain_le_mean {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {dW gl gu : Obs 1 K → ℝ}
    (hV : ∀ y, IsNode P y → ValidAt P u₀ y 0 (dW y) (gl y) (gu y)) {y : Obs 1 K} (hy : IsNode P y) :
    gain P u₀ y ≤ meanCap P u₀ dW gl gu y :=
  le_min ((tangentCap.2 K S T P hS u₀ hu y hy).2.2.1) (gain_le_curv hS hu hy (hV y hy))

/-- The one-ETF `T_y` is at most `tanBound`: it is a feasible first-order gain. -/
lemma tanOne_le {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {y : Obs 1 K} (hy : IsNode P y) :
    tanOne P u₀ y ≤ tanBound P u₀ y := by
  obtain ⟨u, hfe, he⟩ := tan_one_attain hS hu hy
  unfold tanOne
  rw [← he]
  exact tan_le_bound hS hu hy hfe

theorem aggregation : Aggregation := by
  refine ⟨fun n K S T _ _ P hS u₀ hu => ⟨phi_le hS hu fun y hy => gain_le_tanBound hS hu hy,
    fun U D hUD => agg_mono hS hu fun y hy =>
      tanBound_le_cap hS hu hy (hUD y hy).1 (hUD y hy).2.1 (hUD y hy).2.2⟩,
    fun K S T _ _ P hS => ⟨fun u₀ hu dW gl gu hV => ⟨phi_le hS hu fun y hy => gain_le_mean hS hu hV hy,
      fun U D hUD => agg_mono hS hu fun y hy => ((min_le_left _ _).trans (tanOne_le hS hu hy)).trans
        (tanBound_le_cap hS hu hy (hUD y hy).1 (hUD y hy).2.1 (hUD y hy).2.2)⟩,
    fun AE BN hAE hBN dW gl gu hV ℓ hℓ hlt => ?_, fun AN BE hAN hBE dW gl gu hV ℓ hℓ hlt => ?_⟩⟩
  · have := (signConditions 1 K S T P hS).1 AE BN hAE hBN _ ℓ
      (fun y hy => gain_le_mean hS hAE.1 hV hy) hℓ hlt
    linarith [this.1, this.2]
  · have hBEF := Novel.M3EtfChannelSandwichProof.feas_EF hBE.1
    have := (signConditions 1 K S T P hS).2.1 AN BE hAN hBE ℓ _ hℓ
      (fun y hy => gain_le_mean hS hBEF hV hy) hlt
    linarith [this.1, this.2]

/-! ### Part 1: range-type caps -/

omit [Fintype S] in
lemma exists_pos_sum {ι : Type} [Fintype ι] {f : ι → ℝ} (h : 0 < ∑ i, f i) : ∃ i, 0 < f i := by
  by_contra hn; push Not at hn
  have := sum_nonpos (s := univ) fun i _ => hn i
  linarith

/-- What realizable data satisfy. -/
lemma data_facts {u₀ : Inst 1 n → ℝ} {y : Obs n K} {h ρ : ℝ} {m kp km gb gu : Fin n → ℝ}
    (hd : HasData P u₀ y h m kp km ρ gb gu) :
    0 < ρ ∧ (∀ j, 0 ≤ kp j ∧ kp j < 1 ∧ 0 ≤ km j ∧ km j < 1) ∧ 0 ≤ h ∧ (∀ j, 0 ≤ m j) ∧
      (∀ j, 0 < gu j ∧ gu j ≤ gb j) ∧ h + ∑ j, m j / gb j ≤ 1 := by
  obtain ⟨hS, hu, hy, hh, hm, hk, hρ, hg⟩ := hd
  obtain ⟨hρ0, hq, hq1, hpi, hpi1, hrates, hx0, hh0, hW0, hgross⟩ := setting_parts hS
  have hnn := node_nn hS hu hy.1
  have hgu : ∀ j, 0 < gu j ∧ gu j ≤ gb j := fun j => by
    obtain ⟨t, s, hp, he⟩ := (hg j).2.2
    have h1 := hgross t s (Sum.inr j)
    have hb := (hg j).1 t s hp
    unfold gE at he hb
    exact ⟨by linarith, by linarith [hb.2]⟩
  refine ⟨hρ ▸ hρ0, fun j => by rw [← (hk j).1, ← (hk j).2]; exact hrates _, ?_, fun j => ?_, hgu, ?_⟩
  · rw [← hh]; exact div_nonneg hnn.2 hW0.le
  · rw [← hm j]; exact div_nonneg (hnn.1 _) hW0.le
  -- the observed first-quarter path is a node path
  obtain ⟨t, ht⟩ := exists_pos_sum hy.2
  have hpt : 0 < P.pi0 t := lt_of_le_of_ne (hpi t) fun e => by rw [← e, zero_mul] at ht; exact lt_irrefl _ ht
  have hlik : 0 < lik P t y := by
    by_contra hl; push Not at hl; nlinarith [mul_le_mul_of_nonneg_left hl (hpi t)]
  obtain ⟨s₀, hs₀⟩ := exists_pos_sum hlik
  have hobs : obs P t s₀ = y := by by_contra hne; simp [hne] at hs₀
  have hqs : 0 < P.D.q s₀ := by simpa [hobs] using hs₀
  have hpath : NodePath P y t s₀ := by
    refine ⟨?_, hqs⟩
    simp only [post, hy.2, ↓reduceIte]
    exact div_pos (mul_pos hpt hlik) hy.2
  have hz : ∀ j, 0 ≤ P.D.x0 (Sum.inr j) + u₀ (Sum.inr j) := fun j => hu.1 _
  have hmj : ∀ j, m j / gb j ≤ (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j)) / W0 P.D := fun j => by
    have hgb : 0 < gb j := lt_of_lt_of_le (hgu j).1 (hgu j).2
    have hge := ((hg j).1 t s₀ hpath).2
    have hx1 : x1 P y u₀ (Sum.inr j) = gE P j t s₀ * (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j)) := by
      rw [← hobs]; rfl
    rw [← hm j, hx1, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hge (hz j), hW0]
  have hrw := root_wealth (P := P) u₀
  have hc := cost_nonneg P (rates_nonneg hS) u₀
  rw [sum_inst] at hrw
  have hA : 0 ≤ P.D.x0 (Sum.inl 0) + u₀ (Sum.inl 0) := hu.1 _
  have hsum := sum_le_sum fun j (_ : j ∈ univ) => hmj j
  rw [← sum_div] at hsum
  rw [← hh]
  have : (h1 P u₀ + ∑ j, (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j))) / W0 P.D ≤ 1 := by
    rw [div_le_one hW0]; linarith
  rw [add_div] at this
  linarith

/-- The two-scenario family: one parameter, a riskless active fund, and scenario `true` (mass
`p`) where each ETF returns `gb` and `false` (mass `1 - p`) where it returns `gu`. Cash is `h`,
ETF holdings `m / gb`, the rest in the active fund. -/
noncomputable def famData {n : ℕ} (h : ℝ) (m kp km gb gu : Fin n → ℝ) (p : ℝ) : Data 1 n 0 Bool where
  BA := 0
  BE := 0
  cE := 0
  kplus := Sum.elim 0 kp
  kminus := Sum.elim 0 km
  gamma := 0
  q := fun s => if s then p else 1 - p
  zf := 0
  zA := 0
  zE := fun s j => if s then gb j - 1 else gu j - 1
  x0 := Sum.elim (fun _ => 1 - h - ∑ j, m j / gb j) (fun j => m j / gb j)
  h0 := h
  wbar := 0

/-- The family's instance. -/
noncomputable def fam {n : ℕ} (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ) (p : ℝ) :
    M3 n 0 Bool Unit :=
  ⟨famData h m kp km gb gu p, fun _ => ⟨0, 0⟩, fun _ => 1, ρ⟩

section Family

variable {h ρ : ℝ} {m kp km gb gu : Fin n → ℝ} {p : ℝ}

/-- ETF gross return in scenario `s`. -/
noncomputable def gs (gb gu : Fin n → ℝ) (j : Fin n) (s : Bool) : ℝ := if s then gb j else gu j

lemma fam_ret (s : Bool) : ret (fam h m kp km ρ gb gu p).D ((fam h m kp km ρ gb gu p).par ()) s
    = Sum.elim (fun _ => 0) (fun j => gs gb gu j s - 1) := by
  funext i
  rcases i with k | k
  · simp [ret, fam, famData]
  · cases s <;> simp [ret, fam, famData, gs]

lemma fam_gE (j : Fin n) (s : Bool) : gE (fam h m kp km ρ gb gu p) j () s = gs gb gu j s := by
  unfold gE; rw [fam_ret]; simp

lemma fam_W0 : W0 (fam h m kp km ρ gb gu p).D = 1 := by
  simp only [W0, fam, famData, sum_inst, Sum.elim_inl, Sum.elim_inr]
  ring

variable (hρ : 0 < ρ) (hk : ∀ j, 0 ≤ kp j ∧ kp j < 1 ∧ 0 ≤ km j ∧ km j < 1) (hh : 0 ≤ h)
  (hm : ∀ j, 0 ≤ m j) (hg : ∀ j, 0 < gu j ∧ gu j ≤ gb j) (hb : h + ∑ j, m j / gb j ≤ 1)
  (hp0 : 0 < p) (hp1 : p < 1)

include hρ hk hh hm hg hb hp0 hp1 in
lemma fam_setting : M3Setting (fam h m kp km ρ gb gu p) := by
  refine ⟨hρ, fun s => ?_, ?_, fun t => by simp [fam], by simp [fam], fun i => ?_, fun i => ?_,
    hh, by rw [fam_W0]; norm_num, fun t s i => ?_⟩
  · cases s <;> simp [fam, famData] <;> linarith
  · simp [fam, famData]
  · rcases i with k | k <;> simp [fam, famData, hk]
  · rcases i with k | k
    · simp [fam, famData]; linarith
    · simp only [fam, famData, Sum.elim_inr]
      exact div_nonneg (hm k) (lt_of_lt_of_le (hg k).1 (hg k).2).le
  · obtain rfl : t = () := rfl
    rw [fam_ret]
    rcases i with k | k
    · simp
    · cases s <;> simp [gs, (hg k).1, lt_of_lt_of_le (hg k).1 (hg k).2]

/-- The node: the observation after scenario `true`. -/
noncomputable abbrev famY (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ) (p : ℝ) : Obs n 0 :=
  obs (fam h m kp km ρ gb gu p) () true

include hp0 hp1 in
lemma fam_P0 : 0 < P0 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) := by
  simp only [P0, lik, Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton]
  simp only [fam, famData, one_mul, ↓reduceIte, Bool.false_eq_true]
  split_ifs <;> linarith

include hp0 hp1 in
lemma fam_post (t : Unit) : post (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) t = 1 := by
  have h0 := fam_P0 (h := h) (m := m) (kp := kp) (km := km) (ρ := ρ) (gb := gb) (gu := gu) hp0 hp1
  simp only [post, h0, ↓reduceIte]
  have : P0 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p)
      = (fam h m kp km ρ gb gu p).pi0 t * lik (fam h m kp km ρ gb gu p) t (famY h m kp km ρ gb gu p) := by
    simp [P0]
  rw [this] at h0 ⊢
  exact div_self h0.ne'

include hp0 hp1 in
lemma fam_node : IsNode (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) :=
  ⟨Finset.mem_image.mpr ⟨((), true), Finset.mem_univ _, rfl⟩, fam_P0 hp0 hp1⟩

include hp0 hp1 in
lemma fam_path (t : Unit) (s : Bool) : NodePath (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) t s :=
  ⟨by rw [fam_post hp0 hp1]; norm_num, by cases s <;> simp [fam, famData] <;> linarith⟩

lemma fam_h1 : h1 (fam h m kp km ρ gb gu p) 0 = h := by
  simp only [h1, cost_zero, Pi.zero_apply, sum_const_zero, sub_zero]
  rfl

include hg in
lemma fam_x1 (j : Fin n) : x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0 (Sum.inr j) = m j := by
  have hgb : 0 < gb j := lt_of_lt_of_le (hg j).1 (hg j).2
  simp only [x1, famY, obs, fam_ret, Sum.elim_inr, gs, ↓reduceIte, Pi.zero_apply, add_zero]
  simp only [fam, famData, Sum.elim_inr]
  field_simp
  ring

include hρ hk hh hm hg hb hp0 hp1 in
lemma fam_data : HasData (fam h m kp km ρ gb gu p) 0 (famY h m kp km ρ gb gu p) h m kp km ρ gb gu := by
  have hS := fam_setting hρ hk hh hm hg hb hp0 hp1
  refine ⟨hS, feas_zero .F (fun i => (setting_parts hS).2.2.2.2.2.2.1 i) hh, fam_node hp0 hp1,
    by rw [fam_h1, fam_W0, div_one], fun j => by rw [fam_x1 hg, fam_W0, div_one],
    fun j => by simp [fam, famData], rfl, fun j => ⟨fun t s _ => ?_, ⟨(), true, fam_path hp0 hp1 _ _, ?_⟩,
      ⟨(), false, fam_path hp0 hp1 _ _, ?_⟩⟩⟩
  · rw [fam_gE]; cases s <;> simp [gs, (hg j).2]
  · rw [fam_gE]; simp [gs]
  · rw [fam_gE]; simp [gs]

include hg in
/-- No-trade node wealth in scenario `s`. -/
lemma fam_B (s : Bool) :
    condW (fam h m kp km ρ gb gu p) (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0)
      (h1 (fam h m kp km ρ gb gu p) 0) 0 () s
      = h + (1 - h - ∑ j, m j / gb j) + ∑ j, m j * gs gb gu j s := by
  have hx : ∀ j, x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0 (Sum.inr j) = m j :=
    fam_x1 hg
  have hxA : x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0 (Sum.inl 0)
      = 1 - h - ∑ j, m j / gb j := by
    simp only [x1, famY, obs, fam_ret, Sum.elim_inl, Pi.zero_apply, add_zero]
    simp [fam, famData]
  unfold condW
  rw [fam_h1, cost_zero, sum_inst, sum_inst, hxA, fam_ret]
  simp only [Pi.zero_apply, add_zero, sum_const_zero, sub_zero, Sum.elim_inl, Sum.elim_inr, hx]
  ring_nf

include hρ hk hh hm hg hb hp0 hp1 in
/-- The gain is at least the two-point certainty-equivalent change of any feasible trade. -/
lemma fam_gain {u : Inst 1 n → ℝ}
    (hfe : Feas1 (fam h m kp km ρ gb gu p) .E
      (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0) (h1 (fam h m kp km ρ gb gu p) 0) u)
    (δ : Bool → ℝ)
    (hδ : ∀ s, condW (fam h m kp km ρ gb gu p) (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0)
      (h1 (fam h m kp km ρ gb gu p) 0) u () s
      = h + (1 - h - ∑ j, m j / gb j) + ∑ j, m j * gs gb gu j s + δ s) :
    -(1 / ρ) * Real.log (p * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j) + ∑ j, m j * gs gb gu j true
        + δ true)) + (1 - p) * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j)
        + ∑ j, m j * gs gb gu j false + δ false)))
      + (1 / ρ) * Real.log (p * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j)
        + ∑ j, m j * gs gb gu j true)) + (1 - p) * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j)
        + ∑ j, m j * gs gb gu j false)))
      ≤ gain (fam h m kp km ρ gb gu p) 0 (famY h m kp km ρ gb gu p) := by
  have hS := fam_setting hρ hk hh hm hg hb hp0 hp1
  have hu : Feas1 (fam h m kp km ρ gb gu p) .F (fam h m kp km ρ gb gu p).D.x0
      (fam h m kp km ρ gb gu p).D.h0 0 := feas_zero .F (fun i => (setting_parts hS).2.2.2.2.2.2.1 i) hh
  have hy := fam_node (h := h) (m := m) (kp := kp) (km := km) (ρ := ρ) (gb := gb) (gu := gu) hp0 hp1
  have hE := nodeCE_ge hS hu hy hfe
  have hcond : ∀ v : Inst 1 n → ℝ, condObj (fam h m kp km ρ gb gu p)
      (post (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p))
      (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0) (h1 (fam h m kp km ρ gb gu p) 0) v
      = -(p * Real.exp (-ρ * condW (fam h m kp km ρ gb gu p)
          (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0) (h1 (fam h m kp km ρ gb gu p) 0) v () true)
        + (1 - p) * Real.exp (-ρ * condW (fam h m kp km ρ gb gu p)
          (x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0) (h1 (fam h m kp km ρ gb gu p) 0) v () false)) := by
    intro v
    simp only [condObj, Finset.univ_unique, Finset.sum_singleton, Fintype.sum_bool, fam_post hp0 hp1,
      fam_W0, div_one, U, one_mul]
    simp only [fam, famData, ↓reduceIte, Bool.false_eq_true]
    ring
  have hN : nodeCE (fam h m kp km ρ gb gu p) .N 0 (famY h m kp km ρ gb gu p)
      = -(1 / ρ) * Real.log (p * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j)
        + ∑ j, m j * gs gb gu j true)) + (1 - p) * Real.exp (-ρ * (h + (1 - h - ∑ j, m j / gb j)
        + ∑ j, m j * gs gb gu j false))) := by
    unfold nodeCE
    rw [V1N_eq hS hu hy, hcond, neg_neg, fam_B hg, fam_B hg]
    rfl
  rw [hcond, neg_neg, hδ, hδ] at hE
  unfold gain
  rw [hN]
  have : (fam h m kp km ρ gb gu p).rho = ρ := rfl
  rw [this] at hE
  linarith

end Family

/-- Values near a continuity point. -/
lemma approx_at {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContinuousAt f x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → f x₀ - ε < f x := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hf ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := h (by rw [Real.dist_eq]; exact hx)
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

/-- The two-point change is continuous in the mass. -/
lemma cont_two (ρ a1 a2 b1 b2 x₀ : ℝ) (hx₀ : x₀ = 0 ∨ x₀ = 1) :
    ContinuousAt (fun p => -(1 / ρ) * Real.log (p * Real.exp a1 + (1 - p) * Real.exp a2)
      + (1 / ρ) * Real.log (p * Real.exp b1 + (1 - p) * Real.exp b2)) x₀ := by
  have hA : x₀ * Real.exp a1 + (1 - x₀) * Real.exp a2 ≠ 0 := by
    rcases hx₀ with rfl | rfl <;> simp [(Real.exp_pos _).ne']
  have hB : x₀ * Real.exp b1 + (1 - x₀) * Real.exp b2 ≠ 0 := by
    rcases hx₀ with rfl | rfl <;> simp [(Real.exp_pos _).ne']
  have c1 : ContinuousAt (fun p : ℝ => p * Real.exp a1 + (1 - p) * Real.exp a2) x₀ := by fun_prop
  have c2 : ContinuousAt (fun p : ℝ => p * Real.exp b1 + (1 - p) * Real.exp b2) x₀ := by fun_prop
  exact (continuousAt_const.mul (c1.log hA)).add (continuousAt_const.mul (c2.log hB))


/-- A point of `(0, 1)` within `δ` of `1`, and one within `δ` of `0`. -/
lemma near_one {δ : ℝ} (hδ : 0 < δ) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ |p - 1| < δ :=
  ⟨1 - min δ 1 / 2, by have := min_le_right δ 1; linarith, by have := lt_min hδ one_pos; linarith,
    by rw [abs_lt]; constructor <;> nlinarith [min_le_left δ 1, lt_min hδ one_pos]⟩

lemma near_zero {δ : ℝ} (hδ : 0 < δ) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ |p - 0| < δ :=
  ⟨min δ 1 / 2, by have := lt_min hδ one_pos; linarith, by have := min_le_right δ 1; linarith,
    by rw [abs_lt]; constructor <;> nlinarith [min_le_left δ 1, lt_min hδ one_pos]⟩

/-- Part 1 (a), both directions. -/
lemma attain {n : ℕ} {h ρ : ℝ} {m kp km gb gu : Fin n → ℝ} (hd : Realizable n h m kp km ρ gb gu)
    (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    (∃ (K : ℕ) (S T : Type) (_ : Fintype S) (_ : Fintype T) (P : M3 n K S T)
        (u₀ : Inst 1 n → ℝ) (y : Obs n K), HasData P u₀ y h m kp km ρ gb gu ∧
          h * max (gb j / (1 + kp j) - 1) 0 - ε ≤ gain P u₀ y) ∧
    (∃ (K : ℕ) (S T : Type) (_ : Fintype S) (_ : Fintype T) (P : M3 n K S T)
        (u₀ : Inst 1 n → ℝ) (y : Obs n K), HasData P u₀ y h m kp km ρ gb gu ∧
          m j * max (1 - km j - gu j) 0 - ε ≤ gain P u₀ y) := by
  obtain ⟨_, _, _, _, _, _, _, _, hd⟩ := hd
  obtain ⟨hρ, hk, hh, hm, hg, hb⟩ := data_facts hd
  have hk1 : 0 < 1 + kp j := by linarith [(hk j).1]
  set B : Bool → ℝ := fun s => h + (1 - h - ∑ j, m j / gb j) + ∑ j, m j * gs gb gu j s
  -- the instance at mass `p` and its basic facts
  have inst : ∀ p : ℝ, 0 < p → p < 1 → M3Setting (fam h m kp km ρ gb gu p) ∧
      Feas1 (fam h m kp km ρ gb gu p) .F (fam h m kp km ρ gb gu p).D.x0 (fam h m kp km ρ gb gu p).D.h0 0 ∧
      IsNode (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) := fun p h0 h1 => by
    have hS := fam_setting hρ hk hh hm hg hb h0 h1
    exact ⟨hS, feas_zero .F (fun i => (setting_parts hS).2.2.2.2.2.2.1 i) hh, fam_node h0 h1⟩
  -- buying with all cash
  have buyG : ∀ p : ℝ, (hp0 : 0 < p) → (hp1 : p < 1) →
      -(1 / ρ) * Real.log (p * Real.exp (-ρ * (B true + h * ((gb j - 1 - kp j) / (1 + kp j))))
        + (1 - p) * Real.exp (-ρ * (B false + h * ((gu j - 1 - kp j) / (1 + kp j)))))
      + (1 / ρ) * Real.log (p * Real.exp (-ρ * B true) + (1 - p) * Real.exp (-ρ * B false))
      ≤ gain (fam h m kp km ρ gb gu p) 0 (famY h m kp km ρ gb gu p) := fun p hp0 hp1 => by
    obtain ⟨hS, hu, hy⟩ := inst p hp0 hp1
    have hh1 : 0 ≤ h1 (fam h m kp km ρ gb gu p) 0 := by rw [fam_h1]; exact hh
    have := fam_gain hρ hk hh hm hg hb hp0 hp1 (buy_feas hS hu hy j hh1 le_rfl)
      (fun s => h * ((gs gb gu j s - 1 - kp j) / (1 + kp j))) fun s => by
        rw [buy_W hS hu hy j hh1, fam_B hg, fam_h1, fam_gE]; rfl
    simpa [gs, B] using this
  -- selling all of ETF `j`
  have sellG : ∀ p : ℝ, (hp0 : 0 < p) → (hp1 : p < 1) →
      -(1 / ρ) * Real.log (p * Real.exp (-ρ * (B true + m j * (1 - km j - gb j)))
        + (1 - p) * Real.exp (-ρ * (B false + m j * (1 - km j - gu j))))
      + (1 / ρ) * Real.log (p * Real.exp (-ρ * B true) + (1 - p) * Real.exp (-ρ * B false))
      ≤ gain (fam h m kp km ρ gb gu p) 0 (famY h m kp km ρ gb gu p) := fun p hp0 hp1 => by
    obtain ⟨hS, hu, hy⟩ := inst p hp0 hp1
    have hx : 0 ≤ x1 (fam h m kp km ρ gb gu p) (famY h m kp km ρ gb gu p) 0 (Sum.inr j) := by
      rw [fam_x1 hg]; exact hm j
    have := fam_gain hρ hk hh hm hg hb hp0 hp1 (sell_feas hS hu hy j hx le_rfl)
      (fun s => m j * (1 - km j - gs gb gu j s)) fun s => by
        rw [sell_W hS hu hy j hx, fam_B hg, fam_x1 hg, fam_gE]; rfl
    simpa [gs, B] using this
  have hdata : ∀ p : ℝ, 0 < p → p < 1 → HasData (fam h m kp km ρ gb gu p) 0
      (famY h m kp km ρ gb gu p) h m kp km ρ gb gu := fun p h0 h1 =>
    fam_data hρ hk hh hm hg hb h0 h1
  have hρi : (1 / ρ) * ρ = 1 := by field_simp
  constructor
  · by_cases hpos : gb j / (1 + kp j) - 1 ≤ 0
    · obtain ⟨hS, hu, hy⟩ := inst (1 / 2) (by norm_num) (by norm_num)
      refine ⟨0, Bool, Unit, inferInstance, inferInstance, _, 0, _, hdata (1 / 2) (by norm_num) (by norm_num), ?_⟩
      rw [max_eq_right hpos, mul_zero]
      linarith [gain_nonneg hS hu hy]
    · push Not at hpos
      obtain ⟨δ, hδ, hnear⟩ := approx_at (cont_two ρ (-ρ * (B true + h * ((gb j - 1 - kp j) / (1 + kp j))))
        (-ρ * (B false + h * ((gu j - 1 - kp j) / (1 + kp j)))) (-ρ * B true) (-ρ * B false) 1
        (Or.inr rfl)) hε
      obtain ⟨p, hp0, hp1, hpd⟩ := near_one hδ
      refine ⟨0, Bool, Unit, inferInstance, inferInstance, _, 0, _, hdata p hp0 hp1, ?_⟩
      have hn := hnear p hpd
      simp only [one_mul, sub_self, zero_mul, add_zero, Real.log_exp] at hn
      have hv : -(1 / ρ) * (-ρ * (B true + h * ((gb j - 1 - kp j) / (1 + kp j)))) + 1 / ρ * (-ρ * B true)
          = h * (gb j / (1 + kp j) - 1) := by field_simp; ring
      rw [hv] at hn
      rw [max_eq_left hpos.le]
      linarith [buyG p hp0 hp1]
  · by_cases hpos : 1 - km j - gu j ≤ 0
    · obtain ⟨hS, hu, hy⟩ := inst (1 / 2) (by norm_num) (by norm_num)
      refine ⟨0, Bool, Unit, inferInstance, inferInstance, _, 0, _, hdata (1 / 2) (by norm_num) (by norm_num), ?_⟩
      rw [max_eq_right hpos, mul_zero]
      linarith [gain_nonneg hS hu hy]
    · push Not at hpos
      obtain ⟨δ, hδ, hnear⟩ := approx_at (cont_two ρ (-ρ * (B true + m j * (1 - km j - gb j)))
        (-ρ * (B false + m j * (1 - km j - gu j))) (-ρ * B true) (-ρ * B false) 0 (Or.inl rfl)) hε
      obtain ⟨p, hp0, hp1, hpd⟩ := near_zero hδ
      refine ⟨0, Bool, Unit, inferInstance, inferInstance, _, 0, _, hdata p hp0 hp1, ?_⟩
      have hn := hnear p hpd
      simp only [zero_mul, sub_zero, one_mul, zero_add, Real.log_exp] at hn
      have hv : -(1 / ρ) * (-ρ * (B false + m j * (1 - km j - gu j))) + 1 / ρ * (-ρ * B false)
          = m j * (1 - km j - gu j) := by field_simp; ring
      rw [hv] at hn
      rw [max_eq_left hpos.le]
      linarith [sellG p hp0 hp1]

/-- Claim 023's node cap is a range-type cap. -/
lemma cap023_range (n : ℕ) : IsRangeCap n cap023 := by
  intro K S T _ _ P u₀ y h m kp km ρ gb gu hd
  obtain ⟨hS, hu, hy, hh, hm, _, _, hg⟩ := hd
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  have hU : 0 ≤ upOf gb := Real.iSup_nonneg fun _ => le_max_right _ _
  have hD : 0 ≤ downOf gu := Real.iSup_nonneg fun _ => le_max_right _ _
  have := nodeCap_at hS hu hy hU hD fun j t s hp => by
    have hb := (hg j).1 t s hp
    exact ⟨((le_max_left _ _).trans (le_ciSup (f := fun k => max (gb k - 1) 0)
      (Set.finite_range _).bddAbove j)).trans' (by linarith [hb.2]),
      ((le_max_left _ _).trans (le_ciSup (f := fun k => max (1 - gu k) 0)
      (Set.finite_range _).bddAbove j)).trans' (by linarith [hb.1])⟩
  refine this.trans (le_of_eq ?_)
  unfold cap023
  rw [← hh]
  have hsm : ∑ j, m j = (∑ j, x1 P y u₀ (Sum.inr j)) / W0 P.D := by
    rw [sum_div]; exact sum_congr rfl fun j _ => (hm j).symm
  rw [hsm]
  field_simp

/-- Realizable data satisfy the budget with the observed first-quarter returns. -/
lemma observed {u₀ : Inst 1 n → ℝ} {y : Obs n K} {h ρ : ℝ} {m kp km gb gu : Fin n → ℝ}
    (hd : HasData P u₀ y h m kp km ρ gb gu) :
    ∃ t s, obs P t s = y ∧ NodePath P y t s ∧ h + ∑ k, m k / gE P k t s ≤ 1 := by
  obtain ⟨hS, hu, hy, hh, hm, -, -, -⟩ := hd
  obtain ⟨-, hq, -, hpi, -, -, -, -, hW0, hgross⟩ := setting_parts hS
  obtain ⟨t, ht⟩ := exists_pos_sum hy.2
  have hpt : 0 < P.pi0 t := lt_of_le_of_ne (hpi t) fun e => by rw [← e, zero_mul] at ht; exact lt_irrefl _ ht
  have hlik : 0 < lik P t y := by
    by_contra hl; push Not at hl; nlinarith [mul_le_mul_of_nonneg_left hl (hpi t)]
  obtain ⟨s₀, hs₀⟩ := exists_pos_sum hlik
  have hobs : obs P t s₀ = y := by by_contra hne; simp [hne] at hs₀
  have hqs : 0 < P.D.q s₀ := by simpa [hobs] using hs₀
  have hpath : NodePath P y t s₀ := by
    refine ⟨?_, hqs⟩
    simp only [post, hy.2, ↓reduceIte]
    exact div_pos (mul_pos hpt hlik) hy.2
  refine ⟨t, s₀, hobs, hpath, ?_⟩
  have hmk : ∀ k, m k / gE P k t s₀ = (P.D.x0 (Sum.inr k) + u₀ (Sum.inr k)) / W0 P.D := fun k => by
    have hg : 0 < gE P k t s₀ := hgross t s₀ (Sum.inr k)
    have hx1 : x1 P y u₀ (Sum.inr k) = gE P k t s₀ * (P.D.x0 (Sum.inr k) + u₀ (Sum.inr k)) := by
      rw [← hobs]; rfl
    rw [← hm k, hx1]
    field_simp
  simp only [hmk]
  have hrw := root_wealth (P := P) u₀
  have hc := cost_nonneg P (rates_nonneg hS) u₀
  rw [sum_inst] at hrw
  have hA : 0 ≤ P.D.x0 (Sum.inl 0) + u₀ (Sum.inl 0) := hu.1 _
  rw [← hh, ← sum_div, ← add_div, div_le_one hW0]
  linarith

/-- Red's example: one ETF, no cash, every node-path return at least one: zero gain. -/
lemma red_example {P : M3 1 K S T} (hS : M3Setting P) {u₀ : Inst 1 1 → ℝ}
    (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) {y : Obs 1 K} (hy : IsNode P y) (hh : h1 P u₀ = 0)
    (hg : ∀ t s, NodePath P y t s → 1 ≤ gE P 0 t s) : gain P u₀ y = 0 := by
  refine noFav_gain hS hu hy ((noFav_one hS hu hy).mpr ⟨Or.inl hh, Or.inr ?_⟩)
  rw [rSell_eq hS hu hy]
  have := tilt_ge hS hu hy (gE P 0) (c := 1) hg
  linarith [((setting_parts hS).2.2.2.2.2.1 (Sum.inr 0)).2.2.1]

lemma cap023_one (m kp km : Fin 1 → ℝ) (ρ : ℝ) (gb gu : Fin 1 → ℝ) (h1 : 1 ≤ gu 0)
    (h2 : gu 0 ≤ gb 0) : cap023 0 m kp km ρ gb gu = m 0 * (gb 0 - 1) := by
  simp only [cap023, upOf, downOf, ciSup_unique, Fin.default_eq_zero, Fin.sum_univ_one]
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

theorem rangeTypeCaps : RangeTypeCaps := by
  refine ⟨fun n h m kp km ρ gb gu hd j ε hε => attain hd j hε,
    fun n C hC h m kp km ρ gb gu hd j => ⟨?_, ?_⟩, cap023_range,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => observed hd,
    fun _ _ _ _ _ _ hS _ hu _ hy hh hg => red_example hS hu hy hh hg, cap023_one⟩
  · by_contra hlt; push Not at hlt
    obtain ⟨K, S, T, _, _, P, u₀, y, hdat, hg⟩ :=
      (attain hd j (ε := (h * max (gb j / (1 + kp j) - 1) 0 - C h m kp km ρ gb gu) / 2)
        (by linarith)).1
    have := hC K S T P u₀ y h m kp km ρ gb gu hdat
    linarith
  · by_contra hlt; push Not at hlt
    obtain ⟨K, S, T, _, _, P, u₀, y, hdat, hg⟩ :=
      (attain hd j (ε := (m j * max (1 - km j - gu j) 0 - C h m kp km ρ gb gu) / 2)
        (by linarith)).2
    have := hC K S T P u₀ y h m kp km ρ gb gu hdat
    linarith

/-- Claim 026, parts 1-4. -/
theorem proof : Standalone.M3MeanTypeCaps.statement :=
  ⟨rangeTypeCaps, tangentCap, curvatureCap, aggregation⟩

end Novel.M3MeanTypeCapsProof

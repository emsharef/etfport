import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.M3EtfChannelSandwich
import Novel.M3FiniteContinuationProof
import Novel.OppositeContinuationEffectsProof

/-!
# Proof of claim 022: the ETF-adjustment channel is sandwiched by premia at the two root optima

This proof uses claim 011's machine-checked results by importing its proof module, and claim
012's for the opposite sign (`depends_on: [11, 12]`; Q-04). From claim 011 it takes attainment
(`Vmax`, `cond_attain`, `H0_attain`), the representation `V_{D,R} = max_{D₀} H₀^R` (`V_rep`),
`-1 < Φ` and `V < 0`, and the value test for no active trade.

* **Premia.** The review-1 classes are nested and attained at every node, so
  `H₀^N ≤ H₀^E ≤ H₀^F`. The map `v ↦ -(1/ρ) ln(-v)` is increasing on `(-1, 0)`, so the premia are
  nonnegative and `CE_{D,R} = max_{D₀} c_R`.
* **Sandwich.** Each bound compares one class's optimizer with the other class's maximum.
* **Funded cap.** Along every path, an ETF-only review-1 trade changes terminal wealth by
  `Σ_j u_j (g_j - 1) - C(u) ≤ up Σu⁺ + down Σu⁻ ≤ W₀⁻ β`. The shift identity
  `U(z + β) = e^{-ρβ} U(z)` then gives `H₀^E ≤ e^{-ρβ} H₀^N`, that is `c_E ≤ c_N + β`.
* **Sure-active family.** Certainty-equivalent bounds come from explicit policies (lower) and
  from mean wealth, by convexity of `exp`, or claim 011's `W₂ ≤ M² W₀⁻` (upper). Two
  transcendental facts are used: `ln(3/2) ≥ 2/5` (from `(3/2)^5 > e²`) and `e⁹ ≥ 8000`.
-/

namespace Novel.M3EtfChannelSandwichProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
  Standalone.M3EtfChannelSandwich Novel.M3FiniteContinuationProof
open scoped Classical

set_option linter.unusedSectionVars false

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T] {P : M3 n K S T}

/-! ### Parts 0-3 for every M3 instance -/

section General

variable (hS : M3Setting P)
include hS

lemma feas_F {d : Cls} {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ} (hu : Feas1 P d x h u) :
    Feas1 P .F x h u := ⟨hu.1, hu.2.1, trivial⟩

omit hS in
lemma feas_NE {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ} (hu : Feas1 P .N x h u) :
    Feas1 P .E x h u := by
  refine ⟨hu.1, hu.2.1, ?_⟩
  have h0 : u = 0 := hu.2.2
  show u (Sum.inl 0) = 0
  rw [h0]; rfl

omit hS in
lemma feas_EF {x : Inst 1 n → ℝ} {h : ℝ} {u : Inst 1 n → ℝ} (hu : Feas1 P .E x h u) :
    Feas1 P .F x h u := ⟨hu.1, hu.2.1, trivial⟩

lemma H0_range (r : Cls) {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) :
    -1 < H0 P r u₀ ∧ H0 P r u₀ < 0 := by
  obtain ⟨u₁, hπ, hΦ⟩ := H0_attain hS (r := r) hu
  obtain ⟨π', _, hmax, hV⟩ := Vmax hS .F r
  have h1 := Phi_gt hS hπ
  have h2 : Phi P (u₀, u₁) ≤ V P .F r := hV ▸ hmax hπ
  have := V_neg hS .F r
  rw [hΦ] at h1 h2
  exact ⟨h1, by linarith⟩

/-- `v ↦ -(1/ρ) ln(-v)` is monotone on negative values. -/
lemma cmono {a b : ℝ} (hb : b < 0) (hab : a ≤ b) :
    -(1 / P.rho) * Real.log (-a) ≤ -(1 / P.rho) * Real.log (-b) := by
  have hρ : 0 < 1 / P.rho := one_div_pos.mpr hS.1
  have hlog := Real.log_le_log (by linarith) (by linarith : -b ≤ -a)
  nlinarith

lemma V1_mono {r r' : Cls} {x : Inst 1 n → ℝ} {h : ℝ}
    (hsub : ∀ u, Feas1 P r x h u → Feas1 P r' x h u) (pi : T → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hh : 0 ≤ h) : V1 P r x h pi ≤ V1 P r' x h pi := by
  obtain ⟨u, hu, -, hV⟩ := cond_attain hS r pi hx hh
  obtain ⟨u', -, hmax', hV'⟩ := cond_attain hS r' pi hx hh
  rw [hV, hV']
  exact hmax' u (hsub u hu)

lemma H0_mono {r r' : Cls} (hsub : ∀ x h u, Feas1 P r x h u → Feas1 P r' x h u)
    {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) : H0 P r u₀ ≤ H0 P r' u₀ := by
  rw [H0_eq, H0_eq]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs with hp
  · obtain ⟨hx, hh⟩ := node_state hS hu y
    exact mul_le_mul_of_nonneg_left (V1_mono hS (hsub _ _) (post P y) hx hh) hp.le
  · exact le_rfl

lemma cR_mono {r r' : Cls} (hsub : ∀ x h u, Feas1 P r x h u → Feas1 P r' x h u)
    {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) : cR P r u₀ ≤ cR P r' u₀ :=
  cmono hS (H0_range hS r' hu).2 (H0_mono hS hsub hu)

lemma phi_nonneg {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) : 0 ≤ phi P u₀ := by
  have := cR_mono hS (fun _ _ _ h => feas_NE h) hu
  unfold phi; linarith

lemma psi_nonneg {u₀ : Inst 1 n → ℝ} (hu : Feas1 P .F P.D.x0 P.D.h0 u₀) : 0 ≤ psi P u₀ := by
  have := cR_mono hS (fun _ _ _ h => feas_EF h) hu
  unfold psi; linarith

lemma cR_le_CE {d r : Cls} {u₀ : Inst 1 n → ℝ} (hu : Feas1 P d P.D.x0 P.D.h0 u₀) :
    cR P r u₀ ≤ CE P d r := by
  obtain ⟨_, _, _, hle⟩ := V_rep hS d r
  exact cmono hS (V_neg hS d r) (hle u₀ hu)

lemma rootOpt_exists (d r : Cls) : ∃ u₀, RootOpt P d r u₀ := by
  obtain ⟨u₀, hu, hH, hle⟩ := V_rep hS d r
  refine ⟨u₀, hu, fun u₀' hu' => ?_⟩
  have := cR_le_CE hS (r := r) hu'
  unfold cR; rw [hH]; exact this

lemma rootOpt_CE {d r : Cls} {u₀ : Inst 1 n → ℝ} (h : RootOpt P d r u₀) : cR P r u₀ = CE P d r := by
  obtain ⟨u', hu', hH, _⟩ := V_rep hS d r
  have h1 : cR P r u' = CE P d r := by unfold cR CE; rw [hH]
  exact le_antisymm (cR_le_CE hS h.1) (h1 ▸ h.2 u' hu')

theorem premia : ∀ d r : Cls, (∃ u₀, RootOpt P d r u₀) ∧ ∀ u₀, RootOpt P d r u₀ → cR P r u₀ = CE P d r :=
  fun d r => ⟨rootOpt_exists hS d r, fun _ h => rootOpt_CE hS h⟩

/-! The sandwich, one inequality at a time. -/

lemma etf_lower {AN BE : Inst 1 n → ℝ} (hAN : RootOpt P .F .N AN) (hBE : RootOpt P .E .E BE) :
    phi P AN - phi P BE ≤ Delta P .E - Delta P .N := by
  have h1 := cR_le_CE hS (r := .E) hAN.1
  have h2 := rootOpt_CE hS hAN
  have h3 := rootOpt_CE hS hBE
  have h4 := cR_le_CE hS (r := .N) hBE.1
  unfold phi Delta; linarith

lemma etf_upper {AE BN : Inst 1 n → ℝ} (hAE : RootOpt P .F .E AE) (hBN : RootOpt P .E .N BN) :
    Delta P .E - Delta P .N ≤ phi P AE - phi P BN := by
  have h1 := rootOpt_CE hS hAE
  have h2 := cR_le_CE hS (r := .N) hAE.1
  have h3 := cR_le_CE hS (r := .E) hBN.1
  have h4 := rootOpt_CE hS hBN
  unfold phi Delta; linarith

lemma act_lower {AE BF : Inst 1 n → ℝ} (hAE : RootOpt P .F .E AE) (hBF : RootOpt P .E .F BF) :
    psi P AE - psi P BF ≤ Delta P .F - Delta P .E := by
  have h1 := cR_le_CE hS (r := .F) hAE.1
  have h2 := rootOpt_CE hS hAE
  have h3 := rootOpt_CE hS hBF
  have h4 := cR_le_CE hS (r := .E) hBF.1
  unfold psi Delta; linarith

lemma act_upper {AF BE : Inst 1 n → ℝ} (hAF : RootOpt P .F .F AF) (hBE : RootOpt P .E .E BE) :
    Delta P .F - Delta P .E ≤ psi P AF - psi P BE := by
  have h1 := rootOpt_CE hS hAF
  have h2 := cR_le_CE hS (r := .E) hAF.1
  have h3 := cR_le_CE hS (r := .F) hBE.1
  have h4 := rootOpt_CE hS hBE
  unfold psi Delta; linarith

/-! The funded cap. -/

omit hS in
lemma U_shift (z b : ℝ) : U P (z + b) = Real.exp (-P.rho * b) * U P z := by
  unfold U
  rw [show -P.rho * (z + b) = -P.rho * b + -P.rho * z by ring, Real.exp_add]
  ring

/-- The pathwise bound: an ETF-only review-1 trade adds at most `W₀⁻ β` to terminal wealth. -/
lemma path_bound {G L : ℝ} (hG : ∀ j t s, 1 + ret P.D (P.par t) s (Sum.inr j) ≤ G)
    (hL : ∀ j t s, L ≤ 1 + ret P.D (P.par t) s (Sum.inr j)) {u₀ : Inst 1 n → ℝ}
    (hu₀ : Feas1 P .F P.D.x0 P.D.h0 u₀) (y : Yset P) {u : Inst 1 n → ℝ}
    (hu : Feas1 P .E (x1 P y u₀) (h1 P u₀) u) (t : T) (s : S) :
    condW P (x1 P y u₀) (h1 P u₀) u t s
      ≤ condW P (x1 P y u₀) (h1 P u₀) 0 t s + W0 P.D * beta P G L u₀ := by
  have hW0 := (setting_parts hS).2.2.2.2.2.2.2.2.1
  set up := max (G - 1) 0
  set dn := max (1 - L) 0
  set x := x1 P y u₀
  set h := h1 P u₀
  have hup : 0 ≤ up := le_max_right _ _
  have hdn : 0 ≤ dn := le_max_right _ _
  have huA : u (Sum.inl 0) = 0 := hu.2.2
  have hC := cost_nonneg P (rates_nonneg hS) u
  have hcash := hu.2.1
  have hxj : ∀ j, x (Sum.inr j) ≤ G * (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j)) := fun j => by
    obtain ⟨t', s', hy⟩ := obs_mem y
    simp only [x, x1]
    rw [← hy]
    exact mul_le_mul_of_nonneg_right (hG j t' s') (hu₀.1 _)
  have hx0 : ∀ j, 0 ≤ x (Sum.inr j) := fun j => (node_state hS hu₀ y).1 _
  -- per-ETF bound on `u_j (g_j - 1)`
  have hper : ∀ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1)
      ≤ up * max (u (Sum.inr j)) 0 + dn * max (-u (Sum.inr j)) 0 := fun j => by
    have g1 := hG j t s
    have g2 := hL j t s
    have hu1 : G - 1 ≤ up := le_max_left _ _
    have hd1 : 1 - L ≤ dn := le_max_left _ _
    rcases le_total 0 (u (Sum.inr j)) with hj | hj
    · rw [max_eq_left hj, max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_right hj, max_eq_left (by linarith)]
      nlinarith
  have hneg : ∀ j, max (-u (Sum.inr j)) 0 ≤ x (Sum.inr j) := fun j => by
    have := hu.1 (Sum.inr j)
    exact max_le (by linarith) (hx0 j)
  have hsum_split : ∑ j, u (Sum.inr j) = ∑ j, max (u (Sum.inr j)) 0 - ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rcases le_total 0 (u (Sum.inr j)) with hj | hj
      · rw [max_eq_left hj, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hj, max_eq_left (by linarith)]; ring
  have hsumU : ∑ i, u i = ∑ j, u (Sum.inr j) := by rw [sum_inst, huA, zero_add]
  have hpos : ∑ j, max (u (Sum.inr j)) 0 ≤ h + ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [hsumU, hsum_split] at hcash; linarith
  have hnegx : ∑ j, max (-u (Sum.inr j)) 0 ≤ ∑ j, x (Sum.inr j) :=
    Finset.sum_le_sum fun j _ => hneg j
  have hxG : ∑ j, x (Sum.inr j) ≤ G * ∑ j, (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j)) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => hxj j
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
  have hbeta : W0 P.D * beta P G L u₀
      = h * up + (∑ j, (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j))) * G * (up + dn) := by
    unfold beta; rw [← mul_div_assoc, mul_div_cancel_left₀ _ hW0.ne']
  have hstep : ∑ j, u (Sum.inr j) * ((1 + ret P.D (P.par t) s (Sum.inr j)) - 1)
      ≤ up * ∑ j, max (u (Sum.inr j)) 0 + dn * ∑ j, max (-u (Sum.inr j)) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hper j
  have hA := mul_le_mul_of_nonneg_left hpos hup
  have hB := mul_le_mul_of_nonneg_left hnegx (add_nonneg hup hdn)
  have hC' := mul_le_mul_of_nonneg_left hxG (add_nonneg hup hdn)
  rw [hbeta]
  nlinarith

lemma H0_cap {G L : ℝ} (hG : ∀ j t s, 1 + ret P.D (P.par t) s (Sum.inr j) ≤ G)
    (hL : ∀ j t s, L ≤ 1 + ret P.D (P.par t) s (Sum.inr j)) {u₀ : Inst 1 n → ℝ}
    (hu₀ : Feas1 P .F P.D.x0 P.D.h0 u₀) :
    H0 P .E u₀ ≤ Real.exp (-P.rho * beta P G L u₀) * H0 P .N u₀ := by
  obtain ⟨hρ, hq, _, _, _, _, _, _, hW0, _⟩ := setting_parts hS
  rw [H0_eq, H0_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs with hp
  · obtain ⟨hx, hh⟩ := node_state hS hu₀ y
    obtain ⟨u, hu, -, hV⟩ := cond_attain hS .E (post P y) hx hh
    obtain ⟨u0, hu0, -, hV0⟩ := cond_attain hS .N (post P y) hx hh
    have hz : u0 = 0 := hu0.2.2
    rw [hz] at hV0
    rw [hV, hV0]
    have key : condObj P (post P y) (x1 P y u₀) (h1 P u₀) u
        ≤ Real.exp (-P.rho * beta P G L u₀) * condObj P (post P y) (x1 P y u₀) (h1 P u₀) 0 := by
      simp only [condObj, Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => ?_
      have hb := path_bound hS hG hL hu₀ y hu t s
      have hU : U P (condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D)
          ≤ U P (condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D + beta P G L u₀) := by
        apply U_mono P hρ
        rw [div_le_iff₀ hW0, add_mul, div_mul_cancel₀ _ hW0.ne']
        linarith
      rw [U_shift] at hU
      have hw := mul_nonneg (post_nonneg hS (y : Obs n K) t) (hq s)
      calc post P y t * P.D.q s * U P (condW P (x1 P y u₀) (h1 P u₀) u t s / W0 P.D)
          ≤ post P y t * P.D.q s * (Real.exp (-P.rho * beta P G L u₀)
            * U P (condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D)) :=
            mul_le_mul_of_nonneg_left hU hw
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left key hp.le
    linarith
  · simp

lemma phi_le_beta {G L : ℝ} (hG : ∀ j t s, 1 + ret P.D (P.par t) s (Sum.inr j) ≤ G)
    (hL : ∀ j t s, L ≤ 1 + ret P.D (P.par t) s (Sum.inr j)) {u₀ : Inst 1 n → ℝ}
    (hu₀ : Feas1 P .F P.D.x0 P.D.h0 u₀) : phi P u₀ ≤ beta P G L u₀ := by
  have hρ := hS.1
  have hcap := H0_cap hS hG hL hu₀
  have hN := (H0_range hS .N hu₀).2
  have hE := (H0_range hS .E hu₀).2
  have hmul : Real.exp (-P.rho * beta P G L u₀) * -H0 P .N u₀ ≤ -H0 P .E u₀ := by linarith
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) (by linarith)) hmul
  rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at hlog
  unfold phi cR
  have hρi : 0 < 1 / P.rho := one_div_pos.mpr hρ
  have : -(1 / P.rho) * Real.log (-H0 P .E u₀)
      ≤ -(1 / P.rho) * (-P.rho * beta P G L u₀ + Real.log (-H0 P .N u₀)) := by nlinarith
  rw [show -(1 / P.rho) * (-P.rho * beta P G L u₀ + Real.log (-H0 P .N u₀))
    = beta P G L u₀ + -(1 / P.rho) * Real.log (-H0 P .N u₀) by field_simp; ring] at this
  linarith

omit hS in
lemma bounds_exist : ∃ G L : ℝ, (∀ j t s, 1 + ret P.D (P.par t) s (Sum.inr j) ≤ G) ∧
    ∀ j t s, L ≤ 1 + ret P.D (P.par t) s (Sum.inr j) := by
  set G := ∑ j, ∑ t, ∑ s, |1 + ret P.D (P.par t) s (Sum.inr j)|
  have hle : ∀ j t s, |1 + ret P.D (P.par t) s (Sum.inr j)| ≤ G := fun j t s => by
    have h1 : |1 + ret P.D (P.par t) s (Sum.inr j)| ≤ ∑ s', |1 + ret P.D (P.par t) s' (Sum.inr j)| :=
      Finset.single_le_sum (f := fun s' => |1 + ret P.D (P.par t) s' (Sum.inr j)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have h2 : ∑ s', |1 + ret P.D (P.par t) s' (Sum.inr j)|
        ≤ ∑ t', ∑ s', |1 + ret P.D (P.par t') s' (Sum.inr j)| :=
      Finset.single_le_sum (f := fun t' => ∑ s', |1 + ret P.D (P.par t') s' (Sum.inr j)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ t)
    have h3 : ∑ t', ∑ s', |1 + ret P.D (P.par t') s' (Sum.inr j)| ≤ G :=
      Finset.single_le_sum (f := fun j' => ∑ t', ∑ s', |1 + ret P.D (P.par t') s' (Sum.inr j')|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    linarith
  exact ⟨G, -G, fun j t s => (le_abs_self _).trans (hle j t s),
    fun j t s => by have := neg_abs_le (1 + ret P.D (P.par t) s (Sum.inr j)); linarith [hle j t s]⟩

lemma phi_corner {u₀ : Inst 1 n → ℝ} (hu₀ : Feas1 P .F P.D.x0 P.D.h0 u₀) (hh : h1 P u₀ = 0)
    (hx : ∀ j, P.D.x0 (Sum.inr j) + u₀ (Sum.inr j) = 0) : phi P u₀ = 0 := by
  obtain ⟨G, L, hG, hL⟩ := bounds_exist (P := P)
  have hb : beta P G L u₀ = 0 := by
    simp only [beta, hh, hx, Finset.sum_const_zero]; ring
  have := phi_le_beta hS hG hL hu₀
  rw [hb] at this
  exact le_antisymm this (phi_nonneg hS hu₀)

end General

theorem premiaThm : Premia := fun _ _ _ _ _ _ _ hS =>
  ⟨premia hS, fun _ hu => ⟨phi_nonneg hS hu, psi_nonneg hS hu⟩⟩

theorem sandwich : Sandwich := fun _ _ _ _ _ _ _ hS _ _ _ _ _ _ hAN hAE hAF hBN hBE hBF =>
  ⟨etf_lower hS hAN hBE, etf_upper hS hAE hBN, act_lower hS hAE hBF, act_upper hS hAF hBE⟩

theorem fundedCap : FundedCap := by
  intro n K S T _ _ P hS
  refine ⟨fun G L hG hL u₀ hu => ⟨phi_nonneg hS hu, phi_le_beta hS hG hL hu⟩,
    fun u₀ hu hh hx => phi_corner hS hu hh hx, fun AE BN hAE hBN hh hx => ?_⟩
  have h1 := etf_upper hS hAE hBN
  rw [phi_corner hS hAE.1 hh hx] at h1
  exact ⟨by linarith, by linarith [phi_nonneg hS (feas_EF hBN.1)]⟩

theorem regionMovement : RegionMovement := by
  intro n K S T _ _ P hS AN AE BN BE hAN hAE hBN hBE
  have hcomp := classComparison hS
  refine ⟨fun hN hle => ?_, fun hE hle => ?_⟩
  · have h1 := etf_upper hS hAE hBN
    have h0 := (hcomp.2.2 .E).1
    have hE : Delta P .E = 0 := by linarith
    exact ⟨hE, ((hcomp.2.2 .E).2).mp hE⟩
  · have h1 := etf_lower hS hAN hBE
    have h0 := (hcomp.2.2 .N).1
    have hN : Delta P .N = 0 := by linarith
    exact ⟨hN, ((hcomp.2.2 .N).2).mp hN⟩

/-! ### Part 4: the sure-active family -/

section Family

variable {kA kE sA sE : ℝ}

/-- Gross returns `(3/2, 3/2)` under `θ₊` and `(3/2, 1/2)` under `θ₋`, in both quarters. -/
noncomputable def gr : Bool → Inst 1 1 → ℝ
  | true => Sum.elim (fun _ => 3 / 2) (fun _ => 3 / 2)
  | false => Sum.elim (fun _ => 3 / 2) (fun _ => 1 / 2)

/-- Shorthand for the instance. -/
noncomputable abbrev Q (kA kE sA sE : ℝ) : M3 1 2 (Fin 1) Bool := saInst kA kE sA sE

lemma gross_sa (t : Bool) (s : Fin 1) (i : Inst 1 1) :
    1 + ret (Q kA kE sA sE).D ((Q kA kE sA sE).par t) s i = gr t i := by
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> cases t <;>
    simp [ret, saInst, saData, saPar, gr, Matrix.vecHead, Matrix.vecTail] <;> norm_num

lemma W0_sa : W0 (Q kA kE sA sE).D = 1 := by simp [W0, saInst, saData]

lemma x0_sa : (Q kA kE sA sE).D.x0 = 0 := rfl

lemma setting_sa (hb : InBox kA kE sA sE) : M3Setting (Q kA kE sA sE) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  refine ⟨by norm_num [saInst], fun s => by simp [saInst, saData], by simp [saInst, saData],
    fun t => by cases t <;> norm_num [saInst], by simp [saInst]; norm_num, fun i => ?_,
    fun i => by simp [saInst, saData], by norm_num [saInst, saData], by rw [W0_sa]; norm_num,
    fun t s i => ?_⟩
  · rcases i with k | k <;> simp [saInst, saData] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rw [gross_sa]
    rcases i with k | k <;> cases t <;> norm_num [gr]

lemma obs_ne_sa : obs (Q kA kE sA sE) true (0 : Fin 1) ≠ obs (Q kA kE sA sE) false 0 := by
  intro h
  have := congrFun (congrArg Prod.snd h) (Sum.inr 0)
  have e1 := gross_sa (kA := kA) (kE := kE) (sA := sA) (sE := sE) true 0 (Sum.inr 0)
  have e2 := gross_sa (kA := kA) (kE := kE) (sA := sA) (sE := sE) false 0 (Sum.inr 0)
  simp only [obs] at this
  simp only [gr, Sum.elim_inr] at e1 e2
  linarith

lemma Phi_sa (π : Policy (Q kA kE sA sE)) :
    Phi (Q kA kE sA sE) π
      = -(1 / 3 * Real.exp (-20 * W2 (Q kA kE sA sE) π true 0 0)
          + 2 / 3 * Real.exp (-20 * W2 (Q kA kE sA sE) π false 0 0)) := by
  simp only [Phi, U, W0_sa, div_one, Fintype.sum_bool, Fin.sum_univ_one]
  simp [saInst, saData]
  ring

lemma CE_sa (d r : Cls) :
    CE (Q kA kE sA sE) d r = -(1 / 20) * Real.log (-V (Q kA kE sA sE) d r) := rfl

lemma exp_w (x y : ℝ) :
    Real.exp (1 / 3 * x + 2 / 3 * y) ≤ 1 / 3 * Real.exp x + 2 / 3 * Real.exp y := by
  have := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
  simpa [smul_eq_mul] using this

section CEBounds

variable (hb : InBox kA kE sA sE)
include hb

lemma CE_ge_mix {d r : Cls} {a b : ℝ} {π : Policy (Q kA kE sA sE)}
    (hπ : π ∈ Pol (Q kA kE sA sE) d r) (h1 : a ≤ W2 (Q kA kE sA sE) π true 0 0)
    (h2 : b ≤ W2 (Q kA kE sA sE) π false 0 0) :
    -(1 / 20) * Real.log (1 / 3 * Real.exp (-20 * a) + 2 / 3 * Real.exp (-20 * b))
      ≤ CE (Q kA kE sA sE) d r := by
  have hS := setting_sa hb
  obtain ⟨π', _, hmax, hV⟩ := Vmax hS d r
  have hle : Phi (Q kA kE sA sE) π ≤ V (Q kA kE sA sE) d r := by rw [← hV]; exact hmax hπ
  rw [Phi_sa] at hle
  have e1 : Real.exp (-20 * W2 (Q kA kE sA sE) π true 0 0) ≤ Real.exp (-20 * a) :=
    Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-20 * W2 (Q kA kE sA sE) π false 0 0) ≤ Real.exp (-20 * b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hneg : -V (Q kA kE sA sE) d r ≤ 1 / 3 * Real.exp (-20 * a) + 2 / 3 * Real.exp (-20 * b) := by
    linarith
  have hVn := V_neg hS d r
  have hlog := Real.log_le_log (by linarith) hneg
  rw [CE_sa]
  linarith

lemma CE_ge {d r : Cls} {L : ℝ} {π : Policy (Q kA kE sA sE)}
    (hπ : π ∈ Pol (Q kA kE sA sE) d r) (h1 : L ≤ W2 (Q kA kE sA sE) π true 0 0)
    (h2 : L ≤ W2 (Q kA kE sA sE) π false 0 0) : L ≤ CE (Q kA kE sA sE) d r := by
  have := CE_ge_mix hb hπ h1 h2
  rwa [show 1 / 3 * Real.exp (-20 * L) + 2 / 3 * Real.exp (-20 * L) = Real.exp (-20 * L) by ring,
    Real.log_exp, show -(1 / 20) * (-20 * L) = L by ring] at this

lemma CE_le {d r : Cls} {B : ℝ}
    (hB : ∀ π ∈ Pol (Q kA kE sA sE) d r,
      1 / 3 * W2 (Q kA kE sA sE) π true 0 0 + 2 / 3 * W2 (Q kA kE sA sE) π false 0 0 ≤ B) :
    CE (Q kA kE sA sE) d r ≤ B := by
  have hS := setting_sa hb
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  have hw := exp_w (-20 * W2 (Q kA kE sA sE) π true 0 0) (-20 * W2 (Q kA kE sA sE) π false 0 0)
  have h2 : Real.exp (-20 * B) ≤ Real.exp (1 / 3 * (-20 * W2 (Q kA kE sA sE) π true 0 0)
      + 2 / 3 * (-20 * W2 (Q kA kE sA sE) π false 0 0)) :=
    Real.exp_le_exp.mpr (by linarith [hB π hπ])
  have hneg : Real.exp (-20 * B) ≤ -V (Q kA kE sA sE) d r := by rw [← hV, Phi_sa]; linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hneg
  rw [Real.log_exp] at hlog
  rw [CE_sa]
  linarith

end CEBounds

/-! Wealth formulas. -/

lemma sum_inst1 (f : Inst 1 1 → ℝ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

lemma obs_gross (t : Bool) (i : Inst 1 1) :
    1 + ((obsY (Q kA kE sA sE) t 0 : Yset (Q kA kE sA sE)) : Obs 1 2).2 i = gr t i :=
  gross_sa t 0 i

lemma W2_sa (π : Policy (Q kA kE sA sE)) (t : Bool) :
    W2 (Q kA kE sA sE) π t 0 0
      = (h1 (Q kA kE sA sE) π.1 - ∑ i, π.2 (obsY (Q kA kE sA sE) t 0) i
          - cost (Q kA kE sA sE).D (π.2 (obsY (Q kA kE sA sE) t 0)))
        + (gr t (Sum.inl 0) * π.1 (Sum.inl 0) + π.2 (obsY (Q kA kE sA sE) t 0) (Sum.inl 0))
            * gr t (Sum.inl 0)
        + (gr t (Sum.inr 0) * π.1 (Sum.inr 0) + π.2 (obsY (Q kA kE sA sE) t 0) (Sum.inr 0))
            * gr t (Sum.inr 0) := by
  rw [W2_eq]
  simp only [sum_inst1, x1, x0_sa, Pi.zero_apply, zero_add]
  have e1 := obs_gross (kA := kA) (kE := kE) (sA := sA) (sE := sE) t (Sum.inl 0)
  have e2 := obs_gross (kA := kA) (kE := kE) (sA := sA) (sE := sE) t (Sum.inr 0)
  simp only [obsY] at e1 e2
  rw [e1, e2, gross_sa, gross_sa]
  ring

lemma root_budget (hb : InBox kA kE sA sE) {d r : Cls} {π : Policy (Q kA kE sA sE)}
    (hπ : π ∈ Pol (Q kA kE sA sE) d r) :
    0 ≤ π.1 (Sum.inl 0) ∧ 0 ≤ π.1 (Sum.inr 0) ∧ 0 ≤ h1 (Q kA kE sA sE) π.1 ∧
      π.1 (Sum.inl 0) + π.1 (Sum.inr 0) + h1 (Q kA kE sA sE) π.1 ≤ 1 := by
  have hS := setting_sa hb
  have hrw := root_wealth (P := Q kA kE sA sE) π.1
  have hc := cost_nonneg (Q kA kE sA sE) (rates_nonneg hS) π.1
  rw [sum_inst1, W0_sa, x0_sa] at hrw
  simp only [Pi.zero_apply, zero_add] at hrw
  have ha := hπ.1.1 (Sum.inl 0)
  have hp := hπ.1.1 (Sum.inr 0)
  simp only [x0_sa, Pi.zero_apply, zero_add] at ha hp
  exact ⟨ha, hp, hπ.1.2.1, by linarith⟩

lemma obsE (t : Bool) :
    ((obsY (Q kA kE sA sE) t 0 : Yset (Q kA kE sA sE)) : Obs 1 2).2 (Sum.inr 0)
      = if t then 1 / 2 else -1 / 2 := by
  have := obs_gross (kA := kA) (kE := kE) (sA := sA) (sE := sE) t (Sum.inr 0)
  cases t <;> simp only [gr, Sum.elim_inr] at this <;> simp <;> linarith

lemma cost_sa (u : Inst 1 1 → ℝ) :
    cost (Q kA kE sA sE).D u = kA * max (u (Sum.inl 0)) 0 + sA * max (-u (Sum.inl 0)) 0
      + (kE * max (u (Sum.inr 0)) 0 + sE * max (-u (Sum.inr 0)) 0) := by
  simp [cost, saInst, saData]

lemma h1_zero : h1 (Q kA kE sA sE) (0 : Inst 1 1 → ℝ) = 1 := by
  simp only [h1, cost_zero]; simp [saInst, saData]

lemma x1_zero (y : Obs 1 2) : x1 (Q kA kE sA sE) y 0 = 0 := by
  funext i; simp [x1, x0_sa]

lemma buy_all {b : ℝ} (hb : 0 ≤ b) : 1 - 1 / (1 + b) - b * (1 / (1 + b)) = 0 := by
  field_simp; ring

/-! Policies. -/

/-- Hold cash at both reviews. -/
noncomputable def cashPol : Policy (Q kA kE sA sE) := (0, fun _ => 0)

lemma cashPol_mem (d r : Cls) : (cashPol : Policy (Q kA kE sA sE)) ∈ Pol (Q kA kE sA sE) d r := by
  refine ⟨feas_zero d (fun i => le_rfl) (by norm_num [saInst, saData]), fun y => ?_⟩
  show Feas1 _ r (x1 _ (y : Obs 1 2) (0 : Inst 1 1 → ℝ)) (h1 _ (0 : Inst 1 1 → ℝ)) 0
  rw [x1_zero, h1_zero]
  exact feas_zero r (fun i => le_rfl) zero_le_one

lemma cashPol_W2 (t : Bool) : W2 (Q kA kE sA sE) cashPol t 0 0 = 1 := by
  rw [W2_sa]
  show h1 _ (0 : Inst 1 1 → ℝ) - _ - cost _ (0 : Inst 1 1 → ℝ) + _ + _ = 1
  rw [h1_zero, cost_zero]
  simp [cashPol]

/-- Wait at the root; after the good ETF observation, buy the ETF with all cash. -/
noncomputable def uW (kE : ℝ) {kA sA sE : ℝ} (y : Yset (Q kA kE sA sE)) : Inst 1 1 → ℝ :=
  if (y : Obs 1 2).2 (Sum.inr 0) = 1 / 2 then Sum.elim (fun _ => 0) (fun _ => 1 / (1 + kE)) else 0

noncomputable def waitPol : Policy (Q kA kE sA sE) := (0, uW kE)

lemma uW_true : uW kE (obsY (Q kA kE sA sE) true 0) = Sum.elim (fun _ => 0) (fun _ => 1 / (1 + kE)) := by
  simp [uW, obsE]

lemma uW_false : uW kE (obsY (Q kA kE sA sE) false 0) = 0 := by
  simp only [uW, obsE]; norm_num

lemma yset_eq (y : Yset (Q kA kE sA sE)) : ∃ t, y = obsY (Q kA kE sA sE) t 0 := by
  obtain ⟨t, s, h⟩ := obs_mem y
  obtain rfl : s = 0 := Subsingleton.elim _ _
  exact ⟨t, Subtype.ext h.symm⟩

lemma waitPol_mem (hb : InBox kA kE sA sE) : waitPol ∈ Pol (Q kA kE sA sE) .E .E := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  refine ⟨feas_zero .E (fun i => le_rfl) (by norm_num [saInst, saData]), fun y => ?_⟩
  obtain ⟨t, rfl⟩ := yset_eq y
  show Feas1 _ .E (x1 _ (obsY (Q kA kE sA sE) t 0 : Obs 1 2) (0 : Inst 1 1 → ℝ))
    (h1 _ (0 : Inst 1 1 → ℝ)) (uW kE (obsY (Q kA kE sA sE) t 0))
  rw [x1_zero, h1_zero]
  have hE : 0 < 1 / (1 + kE) := by positivity
  cases t
  · rw [uW_false]; exact feas_zero .E (fun i => le_rfl) zero_le_one
  · rw [uW_true]
    refine ⟨fun i => ?_, ?_, rfl⟩
    · rcases i with k | k
      · simp
      · simp; positivity
    · rw [cost_sa, sum_inst1]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
      have := buy_all h3'
      linarith

lemma waitPol_W2 (hb : InBox kA kE sA sE) (t : Bool) :
    W2 (Q kA kE sA sE) waitPol t 0 0 = if t then 3 / 2 * (1 / (1 + kE)) else 1 := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  have hE : 0 < 1 / (1 + kE) := by positivity
  rw [W2_sa]
  show h1 _ (0 : Inst 1 1 → ℝ) - _ - _ + _ + _ = _
  rw [h1_zero]
  cases t
  · show 1 - ∑ i, uW kE (obsY (Q kA kE sA sE) false 0) i - cost _ (uW kE (obsY (Q kA kE sA sE) false 0))
      + (gr false (Sum.inl 0) * (0 : Inst 1 1 → ℝ) (Sum.inl 0)
          + uW kE (obsY (Q kA kE sA sE) false 0) (Sum.inl 0)) * gr false (Sum.inl 0)
      + (gr false (Sum.inr 0) * (0 : Inst 1 1 → ℝ) (Sum.inr 0)
          + uW kE (obsY (Q kA kE sA sE) false 0) (Sum.inr 0)) * gr false (Sum.inr 0) = _
    rw [uW_false, cost_zero]
    simp
  · show 1 - ∑ i, uW kE (obsY (Q kA kE sA sE) true 0) i - cost _ (uW kE (obsY (Q kA kE sA sE) true 0))
      + (gr true (Sum.inl 0) * (0 : Inst 1 1 → ℝ) (Sum.inl 0)
          + uW kE (obsY (Q kA kE sA sE) true 0) (Sum.inl 0)) * gr true (Sum.inl 0)
      + (gr true (Sum.inr 0) * (0 : Inst 1 1 → ℝ) (Sum.inr 0)
          + uW kE (obsY (Q kA kE sA sE) true 0) (Sum.inr 0)) * gr true (Sum.inr 0) = _
    rw [uW_true, cost_sa, sum_inst1]
    simp only [Sum.elim_inl, Sum.elim_inr, gr, Pi.zero_apply, mul_zero, zero_add]
    rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
    have := buy_all h3'
    simp only [↓reduceIte]
    linarith

/-- The all-active root with no later trade. -/
noncomputable def actPol : Policy (Q kA kE sA sE) := (allActive kA, fun _ => 0)

lemma allActive_feas (hb : InBox kA kE sA sE) :
    Feas1 (Q kA kE sA sE) .F (Q kA kE sA sE).D.x0 (Q kA kE sA sE).D.h0 (allActive kA) := by
  obtain ⟨h1', h2', _⟩ := hb
  have hA : 0 < 1 / (1 + kA) := by positivity
  refine ⟨fun i => ?_, ?_, trivial⟩
  · rcases i with k | k <;> (simp [allActive, x0_sa]; try positivity)
  · rw [show (Q kA kE sA sE).D.h0 = 1 from rfl, cost_sa, sum_inst1]
    simp only [allActive, Sum.elim_inl, Sum.elim_inr]
    rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
    have := buy_all h1'
    linarith

lemma h1_allActive (hb : InBox kA kE sA sE) : h1 (Q kA kE sA sE) (allActive kA) = 0 := by
  obtain ⟨h1', h2', _⟩ := hb
  have hA : 0 < 1 / (1 + kA) := by positivity
  simp only [h1]
  rw [show (Q kA kE sA sE).D.h0 = 1 from rfl, cost_sa, sum_inst1]
  simp only [allActive, Sum.elim_inl, Sum.elim_inr]
  rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
  have := buy_all h1'
  linarith

lemma actPol_mem (hb : InBox kA kE sA sE) : actPol ∈ Pol (Q kA kE sA sE) .F .N := by
  refine ⟨allActive_feas hb, fun y => ?_⟩
  exact feas_zero .N (node_state (setting_sa hb) (allActive_feas hb) y).1
    (node_state (setting_sa hb) (allActive_feas hb) y).2

lemma actPol_W2 (hb : InBox kA kE sA sE) (t : Bool) :
    W2 (Q kA kE sA sE) actPol t 0 0 = 9 / 4 * (1 / (1 + kA)) := by
  rw [W2_sa]
  show h1 _ (allActive kA) - ∑ i, (0 : Inst 1 1 → ℝ) i - cost _ (0 : Inst 1 1 → ℝ) + _ + _ = _
  rw [h1_allActive hb, cost_zero]
  cases t <;> simp [actPol, allActive, gr] <;> ring

/-! Numerical facts. -/

lemma log32 : 2 / 5 ≤ Real.log (3 / 2) := by
  have he := Real.exp_one_lt_d9
  have e2 : Real.exp (2 / 5) ^ 5 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq := pow_lt_pow_left₀ he (Real.exp_pos 1).le (two_ne_zero)
  have h2 : Real.exp (2 / 5) ^ 5 < (3 / 2) ^ 5 := by
    rw [e2, e3]; norm_num at hsq ⊢; linarith
  have h3 : Real.exp (2 / 5) < 3 / 2 := lt_of_pow_lt_pow_left₀ 5 (by norm_num) h2
  rw [Real.le_log_iff_exp_le (by norm_num)]; exact h3.le

lemma exp9 : 8000 ≤ Real.exp 9 := by
  have he := Real.exp_one_gt_d9
  have : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have := pow_le_pow_left₀ (by norm_num) he.le 9
  norm_num at this ⊢; linarith

lemma waitBound : 1 + 1 / 50 - 1 / 320000 ≤
    -(1 / 20) * Real.log (1 / 3 * Real.exp (-20 * (300 / 201)) + 2 / 3 * Real.exp (-20 * 1)) := by
  set X := 1 / 3 * Real.exp (-20 * (300 / 201)) + 2 / 3 * Real.exp (-20 * 1)
  have hX : 0 < X := by positivity
  have hsmall : Real.exp (-(1980 / 201)) ≤ 1 / 8000 := by
    have h1 : Real.exp (-(1980 / 201)) ≤ Real.exp (-9) := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp (-9) = (Real.exp 9)⁻¹ := Real.exp_neg 9
    have h3 := exp9
    have : (Real.exp 9)⁻¹ ≤ 1 / 8000 := by
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; linarith
    linarith
  have hsplit : Real.exp (-20 * (300 / 201)) = Real.exp (-20) * Real.exp (-(1980 / 201)) := by
    rw [← Real.exp_add]; norm_num
  have hexp25 : 2 / 3 ≤ Real.exp (-(2 / 5)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    have := log32
    have h := Real.exp_le_exp.mpr this
    rw [Real.exp_log (by norm_num)] at h
    norm_num at h ⊢; exact h
  have hexps : 1 + 1 / 16000 ≤ Real.exp (1 / 16000) := by
    have := Real.add_one_le_exp (1 / 16000 : ℝ); linarith
  have hkey : X ≤ Real.exp (-20 - 2 / 5 + 1 / 16000) := by
    rw [show (-20 - 2 / 5 + 1 / 16000 : ℝ) = -20 + -(2 / 5) + 1 / 16000 by ring, Real.exp_add,
      Real.exp_add]
    have p20 := Real.exp_pos (-20)
    have hX' : X ≤ Real.exp (-20) * (2 / 3) * (1 + 1 / 16000) := by
      simp only [X]
      rw [hsplit, show -20 * (1 : ℝ) = -20 by ring]
      nlinarith [mul_le_mul_of_nonneg_left hsmall p20.le]
    calc X ≤ Real.exp (-20) * (2 / 3) * (1 + 1 / 16000) := hX'
      _ ≤ Real.exp (-20) * Real.exp (-(2 / 5)) * Real.exp (1 / 16000) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp25 p20.le) hexps (by norm_num)
        positivity
  have hlog := Real.log_le_log hX hkey
  rw [Real.log_exp] at hlog
  linarith

lemma sureActive (hb : InBox kA kE sA sE) :
    let P := saInst kA kE sA sE
    M3Setting P ∧ obs P true (0 : Fin 1) ≠ obs P false 0 ∧
    CE P .E .N = 1 ∧ 1 + 1 / 50 - 1 / 320000 ≤ CE P .E .E ∧ 450 / 201 ≤ CE P .F .N ∧
    CE P .F .E ≤ 9 / 4 ∧
    Delta P .E - Delta P .N ≤ 9 / 804 - 1 / 50 + 1 / 320000 ∧
    (9 / 804 - 1 / 50 + 1 / 320000 : ℝ) < -1 / 125 ∧
    0 < Delta P .N ∧ 0 < Delta P .E ∧
    Feas1 P .F P.D.x0 P.D.h0 (allActive kA) ∧ phi P (allActive kA) = 0 ∧
    1 / 50 - 1 / 320000 ≤ phi P 0 := by
  intro P
  have hS := setting_sa hb
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hb
  have hcomp := classComparison hS
  -- CE_{E,N} = 1
  have hEN1 : CE P .E .N ≤ 1 := CE_le hb fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hb hπ
    have hA : π.1 (Sum.inl 0) = 0 := hπ.1.2.2
    have z1 : π.2 (obsY (Q kA kE sA sE) true 0) = 0 := (hπ.2 _).2.2
    have z2 : π.2 (obsY (Q kA kE sA sE) false 0) = 0 := (hπ.2 _).2.2
    rw [W2_sa, W2_sa, z1, z2, cost_zero]
    simp only [Pi.zero_apply, sum_const_zero, gr, Sum.elim_inl, Sum.elim_inr, hA]
    nlinarith
  have hEN2 : 1 ≤ CE P .E .N := CE_ge hb (cashPol_mem .E .N) (by rw [cashPol_W2]) (by rw [cashPol_W2])
  -- CE_{E,E} lower bound by waiting
  have hEE : 1 + 1 / 50 - 1 / 320000 ≤ CE P .E .E := by
    have hw1 : 300 / 201 ≤ W2 (Q kA kE sA sE) waitPol true 0 0 := by
      rw [waitPol_W2 hb]; simp only [↓reduceIte]
      rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
    have hw2 : (1 : ℝ) ≤ W2 (Q kA kE sA sE) waitPol false 0 0 := by
      rw [waitPol_W2 hb]; simp
    exact waitBound.trans (CE_ge_mix hb (waitPol_mem hb) hw1 hw2)
  -- CE_{F,N} by the all-active root
  have hFN : 450 / 201 ≤ CE P .F .N := by
    have hA : 450 / 201 ≤ 9 / 4 * (1 / (1 + kA)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
    exact CE_ge hb (actPol_mem hb) (by rw [actPol_W2 hb]; exact hA) (by rw [actPol_W2 hb]; exact hA)
  -- CE_{F,E} ≤ 9/4 from claim 011's bound with M = 3/2
  have hFE : CE P .F .E ≤ 9 / 4 := by
    have hM : ∀ t s i, 1 + ret P.D (P.par t) s i ≤ 3 / 2 := fun t s i => by
      rw [gross_sa]; rcases i with k | k <;> cases t <;> norm_num [gr]
    have hV := ((policyAttainment hS .F .E).2.2.2.2.2.2.2 (3 / 2) (by norm_num) hM).2.2
    have hlog := Real.log_le_log (Real.exp_pos _) (by linarith : Real.exp (-P.rho * (3 / 2) ^ 2)
      ≤ -V P .F .E)
    rw [Real.log_exp] at hlog
    rw [CE_sa]
    have : P.rho = 20 := rfl
    rw [this] at hlog
    linarith
  -- CE_{E,E} ≤ 17/12 by mean wealth
  have hEEu : CE P .E .E ≤ 17 / 12 := CE_le hb fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hb hπ
    have hA : π.1 (Sum.inl 0) = 0 := hπ.1.2.2
    have hM : ∀ t s i, 1 + ret P.D (P.par t) s i ≤ 3 / 2 := fun t s i => by
      rw [gross_sa]; rcases i with k | k <;> cases t <;> norm_num [gr]
    have hW1 := (wealth_le hS hπ (by norm_num : (1 : ℝ) ≤ 3 / 2) hM true 0 0).2
    rw [W0_sa] at hW1
    have hnode : Feas1 (Q kA kE sA sE) .E (x1 (Q kA kE sA sE) (obsY (Q kA kE sA sE) false 0 : Obs 1 2) π.1)
        (h1 (Q kA kE sA sE) π.1) (π.2 (obsY (Q kA kE sA sE) false 0)) := hπ.2 _
    have huA : π.2 (obsY (Q kA kE sA sE) false 0) (Sum.inl 0) = 0 := hnode.2.2
    have huE := hnode.1 (Sum.inr 0)
    simp only [x1, x0_sa, Pi.zero_apply, zero_add] at huE
    rw [obs_gross] at huE
    simp only [gr, Sum.elim_inr] at huE
    have hc1 := cost_nonneg (Q kA kE sA sE) (rates_nonneg hS) (π.2 (obsY (Q kA kE sA sE) false 0))
    have hW2 : W2 (Q kA kE sA sE) π false 0 0 ≤ 1 := by
      rw [W2_sa, sum_inst1, huA, hA]
      simp only [gr, Sum.elim_inl, Sum.elim_inr]
      nlinarith
    nlinarith
  -- the cash root's premium: c_E(0) ≥ the waiting policy's value, c_N(0) ≤ CE_{E,N} = 1
  have hcash : 1 / 50 - 1 / 320000 ≤ phi P 0 := by
    show 1 / 50 - 1 / 320000 ≤ phi (Q kA kE sA sE) 0
    have hfe : Feas1 (Q kA kE sA sE) .E (Q kA kE sA sE).D.x0 (Q kA kE sA sE).D.h0 0 :=
      feas_zero .E (fun i => le_rfl) (by norm_num [saInst, saData])
    have hN := cR_le_CE hS (r := .N) hfe
    have hΦ := Phi_le_H0 hS (waitPol_mem hb)
    have h0 : (waitPol : Policy (Q kA kE sA sE)).1 = 0 := rfl
    rw [h0, Phi_sa] at hΦ
    have hw1 : 300 / 201 ≤ W2 (Q kA kE sA sE) waitPol true 0 0 := by
      rw [waitPol_W2 hb]; simp only [↓reduceIte]
      rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
    have hw2 : (1 : ℝ) ≤ W2 (Q kA kE sA sE) waitPol false 0 0 := by
      rw [waitPol_W2 hb]; simp
    have e1 : Real.exp (-20 * W2 (Q kA kE sA sE) waitPol true 0 0) ≤ Real.exp (-20 * (300 / 201)) :=
      Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp (-20 * W2 (Q kA kE sA sE) waitPol false 0 0) ≤ Real.exp (-20 * 1) :=
      Real.exp_le_exp.mpr (by linarith)
    have hH := (H0_range hS .E (feas_EF hfe)).2
    have hle : -H0 (Q kA kE sA sE) .E 0
        ≤ 1 / 3 * Real.exp (-20 * (300 / 201)) + 2 / 3 * Real.exp (-20 * 1) :=
      calc -H0 (Q kA kE sA sE) .E 0
          ≤ 1 / 3 * Real.exp (-20 * W2 (Q kA kE sA sE) waitPol true 0 0)
            + 2 / 3 * Real.exp (-20 * W2 (Q kA kE sA sE) waitPol false 0 0) := by linarith
        _ ≤ _ := by gcongr
    have hlog := Real.log_le_log (by linarith) hle
    have hwb := waitBound
    have hcE : cR (Q kA kE sA sE) .E 0 = -(1 / 20) * Real.log (-H0 (Q kA kE sA sE) .E 0) := rfl
    unfold phi
    linarith
  have hcompF := (hcomp.2.1 .F)
  refine ⟨hS, obs_ne_sa, le_antisymm hEN1 hEN2, hEE, hFN, hFE, ?_, by norm_num, ?_, ?_,
    allActive_feas hb, phi_corner hS (allActive_feas hb) (h1_allActive hb) (fun j => ?_), hcash⟩
  · simp only [Delta]; linarith
  · simp only [Delta]; linarith
  · simp only [Delta]; linarith [hcompF.2.2.1]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [allActive, x0_sa]

end Family

theorem sureActiveThm : SureActive := fun _ _ _ _ hb => sureActive hb

theorem bothSigns : BothSigns := by
  have hb : InBox 0 0 0 0 := by norm_num [InBox]
  have h := sureActive hb
  have hb' : Standalone.OppositeContinuationEffects.InBox 0 0 0 0 := by
    norm_num [Standalone.OppositeContinuationEffects.InBox]
  have h' := Novel.OppositeContinuationEffectsProof.bounds hb'
  refine ⟨⟨saInst 0 0 0 0, h.1, by linarith [h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1]⟩,
    ⟨Standalone.OppositeContinuationEffects.ocInst 0 0 0 0,
      Novel.OppositeContinuationEffectsProof.setting hb', by linarith [h'.2.2.2.2.2.1]⟩⟩

/-- Claim 022, all parts. -/
theorem proof : Standalone.M3EtfChannelSandwich.statement :=
  ⟨premiaThm, sandwich, fundedCap, regionMovement, sureActiveThm, bothSigns⟩

end Novel.M3EtfChannelSandwichProof

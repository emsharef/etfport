import Novel.M6QuarterlyBandStaticCeilingProof
import Standalone.M7DynamicBundlingBand

/-!
# Proof of claim 107

Uses claim 029's proof module (`depends_on` lists 29, Q-04): the value recursion, convexity and
continuity of `V_t` and `G_t`, and the one-dimensional convex toolkit.

* **Schur.** With `w = d_E + d_A ρ`, `d'Σd = σ²_{A.E} d_A² + w'Σ_EE w`, and `(1, -ρ)'Σd = σ²_{A.E} d_A`.
* **Part 1a.** `U_t - (c^res/2)(a - a*)²` is a partial minimum over the convex compact ETF box of a
  jointly convex function. Claim 029's one-instrument edge argument runs for any convex `f` in
  place of `G_1`.
* **Part 1c.** Moving along the hedge direction `(1, -ρ)` changes the tracking loss by
  `c^res d_A` to first order, the ETF costs by at most the hedge-weighted rates, and the
  continuation by at most `β` times the rates times the expected gross returns (`V_{t+1}` is
  `C`-Lipschitz). The edge's one-sided derivative condition then bounds the edge.
* **Part 1d.** At `T - 1`, `U` is differentiable at every point with derivative `γ(Σd)_A` at the
  ETF optimizer (moving `a` alone at fixed `p`). Coordinate moves of an interior optimizer put
  `-γ(Σd)_E` in the trade-sign sets.
* **Part 2.** Coordinate moves from a no-trade point, with the same Lipschitz bound.
* **Part 3.** With zero ETF rates `V_{t+1}` ignores the ETF coordinates, the minimum over the
  ETFs is the Schur term at the hedge, and backward induction gives `V_t = V^A_t + K_t`.
-/

namespace Novel.M7DynamicBundlingBandProof

open Matrix Finset Standalone.M6QuarterlyBandStaticCeiling Standalone.M7DynamicBundlingBand
open Novel.M6QuarterlyBandStaticCeilingProof
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {M : ℕ} {Z Ω : Type} [Fintype Ω]

/-! ### Joins, costs and boxes -/

section Join

omit [Fintype Ω]

@[simp] lemma join_zero (a : ℝ) (p : Fin M → ℝ) : join a p 0 = a := rfl

@[simp] lemma join_succ (a : ℝ) (p : Fin M → ℝ) (j : Fin M) : join a p j.succ = p j := rfl

lemma join_eta (x : Fin (M + 1) → ℝ) : x = join (x 0) (fun j => x j.succ) :=
  (Fin.cons_self_tail x).symm

lemma join_add (a b : ℝ) (p q : Fin M → ℝ) : join a p + join b q = join (a + b) (p + q) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma join_sub (a b : ℝ) (p q : Fin M → ℝ) : join a p - join b q = join (a - b) (p - q) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma join_smul (s a : ℝ) (p : Fin M → ℝ) : s • join a p = join (s * a) (s • p) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma join_neg (a : ℝ) (p : Fin M → ℝ) : -join a p = join (-a) (-p) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma sum_join (f : Fin (M + 1) → ℝ) : ∑ i, f i = f 0 + ∑ j : Fin M, f j.succ := Fin.sum_univ_succ f

lemma cost_join (P : M6 (M + 1) Z Ω) (a : ℝ) (p : Fin M → ℝ) :
    cost P (join a p) = costA P a + costE P p := by
  simp only [cost, sum_join, join_zero, join_succ, costA, costE]

lemma mem_box_join (P : M6 (M + 1) Z Ω) (a : ℝ) (p : Fin M → ℝ) :
    join a p ∈ box P ↔ (0 ≤ a ∧ a ≤ P.cap 0) ∧ p ∈ ebox P := by
  constructor
  · intro h; exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨h0, h1⟩ i; refine Fin.cases h0 (fun j => h1 j) i

lemma dot_join (a b : ℝ) (p q : Fin M → ℝ) : join a p ⬝ᵥ join b q = a * b + p ⬝ᵥ q := by
  simp [dotProduct, sum_join]

end Join

/-! ### Schur complement -/

section Schur

variable {P : M6 (M + 1) Z Ω} (hS : Setting P) (t : ℕ) (z : Z)
include hS

lemma sig_symm (i j : Fin (M + 1)) : P.Sigma t z i j = P.Sigma t z j i := by
  have := congrFun (congrFun (hS.2.1 t z) j) i
  simpa [transpose_apply] using this

lemma SEE_symm : (SEE P t z)ᵀ = SEE P t z := by
  funext i j; simp [SEE, transpose_apply, sig_symm hS t z]

/-- The bilinear form on joins. -/
lemma bil_join (a b : ℝ) (p q : Fin M → ℝ) :
    join a p ⬝ᵥ (P.Sigma t z *ᵥ join b q) =
      P.Sigma t z 0 0 * a * b + a * (SEA P t z ⬝ᵥ q) + b * (SEA P t z ⬝ᵥ p) + p ⬝ᵥ (SEE P t z *ᵥ q) := by
  simp only [dotProduct, mulVec, sum_join, join_zero, join_succ, SEA, SEE, mul_sum]
  simp only [sig_symm hS t z 0 (Fin.succ _)]
  ring_nf
  simp only [mul_sum, mul_comm, mul_left_comm, mul_assoc, sum_add_distrib]
  ring

lemma SEE_quad_pos (v : Fin M → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (SEE P t z *ᵥ v) := by
  have hne : join 0 v ≠ 0 := by
    intro h; apply hv; funext j; have := congrFun h j.succ; simpa using this
  have := hS.2.2.1 t z _ hne
  rw [bil_join hS] at this
  simpa using this

lemma SEE_det : IsUnit (SEE P t z).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hmv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have := SEE_quad_pos hS t z v hv
  rw [hmv, dotProduct_zero] at this
  exact lt_irrefl _ this

lemma SEE_rho : SEE P t z *ᵥ rho P t z = SEA P t z := by
  rw [rho, mulVec_mulVec, mul_nonsing_inv _ (SEE_det hS t z), one_mulVec]

/-- `ρ'Σ_EE w = Σ_AE w`. -/
lemma rho_SEE (w : Fin M → ℝ) : rho P t z ⬝ᵥ (SEE P t z *ᵥ w) = SEA P t z ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, SEE_symm hS t z, dotProduct_comm, SEE_rho hS t z,
    dotProduct_comm]

/-- The Schur identity: `d'Σd = σ²_{A.E} d_A² + w'Σ_EE w`, `w = d_E + d_A ρ`. -/
lemma schur (dA : ℝ) (dE : Fin M → ℝ) :
    join dA dE ⬝ᵥ (P.Sigma t z *ᵥ join dA dE) =
      s2res P t z * dA ^ 2 + (dE + dA • rho P t z) ⬝ᵥ (SEE P t z *ᵥ (dE + dA • rho P t z)) := by
  rw [bil_join hS]
  have h1 := rho_SEE hS t z dE
  have h2 := rho_SEE hS t z (rho P t z)
  have h3 : dE ⬝ᵥ (SEE P t z *ᵥ rho P t z) = SEA P t z ⬝ᵥ dE := by
    rw [SEE_rho hS t z, dotProduct_comm]
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h1, h2, h3, s2res]
  ring

/-- `(1, -ρ)'Σ(d_A, d_E) = σ²_{A.E} d_A`. -/
lemma hedge_dir (dA : ℝ) (dE : Fin M → ℝ) :
    join 1 (-rho P t z) ⬝ᵥ (P.Sigma t z *ᵥ join dA dE) = s2res P t z * dA := by
  rw [bil_join hS]
  have h1 := rho_SEE hS t z dE
  simp only [neg_dotProduct, h1, dotProduct_neg, s2res]
  ring

lemma s2res_pos : 0 < s2res P t z := by
  have hne : join (1 : ℝ) (-rho P t z) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have := hS.2.2.1 t z _ hne
  have e : join (1 : ℝ) (-rho P t z) = join 1 (-rho P t z) := rfl
  rw [schur hS t z] at this
  simpa using this

lemma cres_pos : 0 < cres P t z := mul_pos hS.2.2.2.1 (s2res_pos hS t z)

end Schur

/-! ### Claim 029's edge argument for any convex function -/

section Generic

/-- The one-instrument trade cost. -/
def c1 (kp km u : ℝ) : ℝ := kp * max u 0 + km * max (-u) 0

variable {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {kp km cap : ℝ} (hk : 0 ≤ kp) (hm : 0 ≤ km)
  (hcap : 0 < cap)

include hcap in
lemma loF_bounds : 0 ≤ loF f kp cap ∧ loF f kp cap ≤ cap := by
  unfold loF
  split_ifs with hne
  · obtain ⟨x0, hx0⟩ := hne
    have hbdd : BddBelow {x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} := ⟨0, fun x hx => hx.1⟩
    exact ⟨le_csInf ⟨x0, hx0⟩ fun x hx => hx.1, (csInf_le hbdd hx0).trans hx0.2.1.le⟩
  · exact ⟨hcap.le, le_rfl⟩

include hcap in
lemma hiF_bounds : 0 ≤ hiF f km cap ∧ hiF f km cap ≤ cap := by
  unfold hiF
  split_ifs with hne
  · obtain ⟨x0, hx0⟩ := hne
    have hbdd : BddAbove {x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} := ⟨cap, fun x hx => hx.2.1⟩
    exact ⟨hx0.1.le.trans (le_csSup hbdd hx0), csSup_le ⟨x0, hx0⟩ fun x hx => hx.2.1⟩
  · exact ⟨le_rfl, hcap.le⟩

include hcap in
lemma below_loF {x : ℝ} (hx0 : 0 ≤ x) (hx : x < loF f kp cap) : rd f x < -kp := by
  by_contra hge; push Not at hge
  have hxc : x < cap := lt_of_lt_of_le hx (loF_bounds hcap).2
  have hmem : x ∈ {x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} := ⟨hx0, hxc, hge⟩
  have : loF f kp cap ≤ x := by
    unfold loF; rw [ite_eq_left ⟨x, hmem⟩]; exact csInf_le ⟨0, fun y hy => hy.1⟩ hmem
  linarith

include hcap in
lemma above_hiF {x : ℝ} (hxc : x ≤ cap) (hx : hiF f km cap < x) : km < ld f x := by
  by_contra hle; push Not at hle
  have hx0 : 0 < x := lt_of_le_of_lt (hiF_bounds hcap).1 hx
  have hmem : x ∈ {x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} := ⟨hx0, hxc, hle⟩
  have : x ≤ hiF f km cap := by
    unfold hiF; rw [ite_eq_left ⟨x, hmem⟩]; exact le_csSup ⟨cap, fun y hy => hy.2.1⟩ hmem
  linarith

include hf in
lemma rd_loF (h : loF f kp cap < cap) : -kp ≤ rd f (loF f kp cap) := by
  have hne : ({x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} : Set ℝ).Nonempty := by
    by_contra hne; unfold loF at h; rw [ite_eq_right hne] at h; exact lt_irrefl _ h
  refine rd_of_right hf h fun u hu _ => ?_
  have hlo : loF f kp cap = sInf {x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} := by
    unfold loF; rw [ite_eq_left hne]
  rw [hlo] at hu
  obtain ⟨s0, hs0, hs0u⟩ := exists_lt_of_csInf_lt hne hu
  exact hs0.2.2.trans (rd_mono hf hs0u.le)

include hf hcap in
lemma ld_loF (h : 0 < loF f kp cap) : ld f (loF f kp cap) ≤ -kp :=
  ld_of_left hf h fun u hu hul => ((ld_le_rd hf u).trans (below_loF hcap hu.le hul).le)

include hf in
lemma ld_hiF (h : 0 < hiF f km cap) : ld f (hiF f km cap) ≤ km := by
  have hne : ({x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} : Set ℝ).Nonempty := by
    by_contra hne; unfold hiF at h; rw [ite_eq_right hne] at h; exact lt_irrefl _ h
  refine ld_of_left hf h fun u _ hu => ?_
  have hhi : hiF f km cap = sSup {x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} := by
    unfold hiF; rw [ite_eq_left hne]
  rw [hhi] at hu
  obtain ⟨s0, hs0, hus0⟩ := exists_lt_of_lt_csSup hne hu
  exact (ld_mono hf hus0.le).trans hs0.2.2

include hf hcap in
lemma rd_hiF (h : hiF f km cap < cap) : km ≤ rd f (hiF f km cap) :=
  rd_of_right hf h fun u hu huc => ((above_hiF hcap huc.le hu).le.trans (ld_le_rd hf u))

include hf hk hm hcap in
lemma loF_le_hiF : loF f kp cap ≤ hiF f km cap := by
  by_contra hlt; push Not at hlt
  obtain ⟨x, hx1, hx2⟩ := exists_between hlt
  have hx0 : 0 ≤ x := (hiF_bounds hcap).1.trans hx1.le
  have hxc : x ≤ cap := hx2.le.trans (loF_bounds hcap).2
  have h1 := below_loF hcap hx0 hx2
  have h2 := above_hiF hcap hxc hx1
  have h3 := ld_le_rd hf x
  linarith

include hf hcap in
lemma loF_min {y : ℝ} (hy0 : 0 ≤ y) (hyc : y ≤ cap) :
    f (loF f kp cap) + kp * loF f kp cap ≤ f y + kp * y := by
  rcases lt_trichotomy y (loF f kp cap) with h | h | h
  · have h1 := slope_le_ld hf h
    have h2 := mul_le_mul_of_nonneg_right (ld_loF hf hcap (lt_of_le_of_lt hy0 h))
      (by linarith : (0 : ℝ) ≤ loF f kp cap - y)
    linarith
  · rw [h]
  · have h1 := rd_le_slope hf h
    have h2 := mul_le_mul_of_nonneg_right (rd_loF hf (lt_of_lt_of_le h hyc))
      (by linarith : (0 : ℝ) ≤ y - loF f kp cap)
    linarith

include hf hcap in
lemma hiF_min {y : ℝ} (hy0 : 0 ≤ y) (hyc : y ≤ cap) :
    f (hiF f km cap) - km * hiF f km cap ≤ f y - km * y := by
  rcases lt_trichotomy y (hiF f km cap) with h | h | h
  · have h1 := slope_le_ld hf h
    have h2 := mul_le_mul_of_nonneg_right (ld_hiF hf (lt_of_le_of_lt hy0 h))
      (by linarith : (0 : ℝ) ≤ hiF f km cap - y)
    linarith
  · rw [h]
  · have h1 := rd_le_slope hf h
    have h2 := mul_le_mul_of_nonneg_right (rd_hiF hf hcap (lt_of_lt_of_le h hyc))
      (by linarith : (0 : ℝ) ≤ y - hiF f km cap)
    linarith

/-- The clip onto the band. -/
def projF (f : ℝ → ℝ) (kp km cap x : ℝ) : ℝ := min (max x (loF f kp cap)) (hiF f km cap)

include hf hk hm hcap in
lemma projF_mem (x : ℝ) : 0 ≤ projF f kp km cap x ∧ projF f kp km cap x ≤ cap := by
  have hlh := loF_le_hiF hf hk hm hcap
  exact ⟨(loF_bounds hcap).1.trans (le_min (le_max_right _ _) hlh),
    (min_le_right _ _).trans (hiF_bounds hcap).2⟩

include hf hk hm hcap in
/-- Trade to the nearer edge: the clip minimizes `c1(y - x) + f y` over `[0, x̄]`. -/
lemma optF (x : ℝ) {y : ℝ} (hy0 : 0 ≤ y) (hyc : y ≤ cap) :
    c1 kp km (projF f kp km cap x - x) + f (projF f kp km cap x) ≤ c1 kp km (y - x) + f y := by
  have hlh := loF_le_hiF hf hk hm hcap
  have hc1 : kp * (y - x) ≤ c1 kp km (y - x) := by
    unfold c1; nlinarith [mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) hk,
      mul_nonneg hm (le_max_right (-(y - x)) 0)]
  have hc2 : -(km * (y - x)) ≤ c1 kp km (y - x) := by
    unfold c1; nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-(y - x)) 0) hm,
      mul_nonneg hk (le_max_right (y - x) 0)]
  unfold c1 at *
  rcases lt_or_ge x (loF f kp cap) with hx | hx
  · have e : projF f kp km cap x = loF f kp cap := by
      unfold projF; rw [max_eq_right hx.le, min_eq_left hlh]
    rw [e, max_eq_left (by linarith), max_eq_right (by linarith)]
    have := loF_min hf hcap (kp := kp) hy0 hyc
    nlinarith
  rcases lt_or_ge (hiF f km cap) x with hx' | hx'
  · have e : projF f kp km cap x = hiF f km cap := by
      unfold projF; rw [max_eq_left hx, min_eq_right hx'.le]
    rw [e, max_eq_right (by linarith), max_eq_left (by linarith)]
    have := hiF_min hf hcap (km := km) hy0 hyc
    nlinarith
  · have e : projF f kp km cap x = x := by
      unfold projF; rw [max_eq_left hx, min_eq_left hx']
    rw [e, sub_self, neg_zero, max_self, mul_zero, mul_zero, add_zero, zero_add]
    rcases le_or_gt x y with hxw | hxw
    · have hcv : ConvexOn ℝ Set.univ (fun u => f u + kp * u) :=
        hf.add ((convexOn_id convex_univ).smul hk)
      have : f x + kp * x ≤ f y + kp * y := le_right_of hcv (loF_min hf hcap hy0 hyc) hx hxw
      nlinarith
    · have hcv : ConvexOn ℝ Set.univ (fun u => f u - km * u) := by
        have := hf.add ((concaveOn_id convex_univ).smul hm).neg
        refine this.congr fun u _ => ?_
        simp [smul_eq_mul]; ring
      have : f x - km * x ≤ f y - km * y := le_left_of hcv (hiF_min hf hcap hy0 hyc) hxw.le hx'
      nlinarith

include hk hm in
lemma c1_convex (x : ℝ) : ConvexOn ℝ Set.univ (fun y => c1 kp km (y - x)) := by
  refine ⟨convex_univ, fun a _ b _ u v hu hv huv => ?_⟩
  simp only [c1, smul_eq_mul]
  have e : u * a + v * b - x = u * (a - x) + v * (b - x) := by
    have : x = (u + v) * x := by rw [huv, one_mul]
    linear_combination (-1 : ℝ) * this
  rw [e, show -(u * (a - x) + v * (b - x)) = u * -(a - x) + v * -(b - x) by ring]
  have h1 := max_convex hu hv (a - x) (b - x)
  have h2 := max_convex hu hv (-(a - x)) (-(b - x))
  nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hm]

include hk hm in
/-- With `f` strictly convex the minimizer over `[0, x̄]` is unique. -/
lemma min_unique (hs : StrictConvexOn ℝ Set.univ f) (x : ℝ) {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ cap)
    (hb : 0 ≤ b ∧ b ≤ cap)
    (hamin : ∀ y, 0 ≤ y → y ≤ cap → c1 kp km (a - x) + f a ≤ c1 kp km (y - x) + f y)
    (hbmin : ∀ y, 0 ≤ y → y ≤ cap → c1 kp km (b - x) + f b ≤ c1 kp km (y - x) + f y) : a = b := by
  by_contra hne
  have hs' := (c1_convex hk hm x).add_strictConvexOn hs
  have h := hs'.2 (Set.mem_univ a) (Set.mem_univ b) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have h1 := hamin ((1 / 2) * a + (1 / 2) * b) (by linarith) (by linarith)
  have h2 := hbmin a ha.1 ha.2
  simp only [smul_eq_mul, Pi.add_apply] at h
  linarith

/-- The ceiling for any `f` with `f - (c/2) y²` convex. -/
lemma ceilingF (hg : ConvexOn ℝ Set.univ (fun y => f y - c / 2 * y ^ 2)) (hc : 0 < c)
    (hf : ConvexOn ℝ Set.univ f) (hk : 0 ≤ kp) (hm : 0 ≤ km) (hcap : 0 < cap) :
    hiF f km cap - loF f kp cap ≤ (kp + km) / c := by
  rcases eq_or_lt_of_le (loF_le_hiF hf hk hm hcap) with h | h
  · rw [h, sub_self]; positivity
  have h1 := rd_loF hf (lt_of_lt_of_le h (hiF_bounds hcap).2)
  have h2 := ld_hiF hf (lt_of_le_of_lt (loF_bounds hcap).1 h)
  have h3 := rd_le_ld hg h
  have e : f = (fun y => c / 2 * (y - 0) ^ 2) + (fun y => f y - c / 2 * y ^ 2) := by
    funext y; simp only [Pi.add_apply]; ring
  have hr : ∀ x, rd f x = c * (x - 0) + rd (fun y => f y - c / 2 * y ^ 2) x := fun x => by
    have hd := (hasDerivAt_quad c 0 x).hasDerivWithinAt.add (hasRd hg x) (s := Set.Ioi x)
    rw [← e] at hd
    exact hd.derivWithin (uniqueDiffWithinAt_Ioi x)
  have hl : ∀ x, ld f x = c * (x - 0) + ld (fun y => f y - c / 2 * y ^ 2) x := fun x => by
    have hd := (hasDerivAt_quad c 0 x).hasDerivWithinAt.add (hasLd hg x) (s := Set.Iio x)
    rw [← e] at hd
    exact hd.derivWithin (uniqueDiffWithinAt_Iio x)
  rw [hr] at h1; rw [hl] at h2
  rw [le_div_iff₀ hc]
  nlinarith

end Generic

/-! ### `V` is `C`-Lipschitz; one-step bounds on `G` -/

section Value

variable {n : ℕ} {P : M6 n Z Ω} (hS : Setting P)
include hS

lemma V_lip (t : ℕ) (z : Z) (a b : Fin n → ℝ) : V P t z a ≤ V P t z b + cost P (b - a) := by
  rcases lt_or_ge t P.T with ht | ht
  · obtain ⟨p, hp, -, hV⟩ := V_attain hS ht z (G_facts hS t z).2.2 b
    have h1 := V_le hS ht z (G_facts hS t z).2.2 a hp
    have h2 := cost_subadd hS (p - b) (b - a)
    rw [show p - b + (b - a) = p - a by abel] at h2
    simp only [Fobj] at h1 hV
    linarith
  · rw [V_ge P ht, V_ge P ht]; linarith [cost_nonneg hS (b - a)]

/-- The continuation's slope bound along `v`. -/
def slopeB (P : M6 n Z Ω) (t : ℕ) (z : Z) (v : Fin n → ℝ) : ℝ :=
  P.beta * ∑ ω, P.prob t z ω * cost P (-(mark v (P.gross ω)))

lemma cont_step (t : ℕ) (z : Z) (x v : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    cont P t z (x + h • v) ≤ cont P t z x + h * slopeB P t z v := by
  have hq := hS.2.2.2.2.2.2.2.2.1 t z
  have hβ := hS.2.2.2.2.1
  have hω : ∀ ω, V P (t + 1) (P.next ω) (mark (x + h • v) (P.gross ω)) ≤
      V P (t + 1) (P.next ω) (mark x (P.gross ω)) + h * cost P (-(mark v (P.gross ω))) := by
    intro ω
    have e : mark (x + h • v) (P.gross ω) = mark x (P.gross ω) + h • mark v (P.gross ω) := by
      simpa using mark_comb x v (P.gross ω) 1 h
    have := V_lip hS (t + 1) (P.next ω) (mark (x + h • v) (P.gross ω)) (mark x (P.gross ω))
    rw [e, show mark x (P.gross ω) - (mark x (P.gross ω) + h • mark v (P.gross ω)) =
      h • (-(mark v (P.gross ω))) by module, cost_smul P hh] at this
    rwa [e]
  simp only [cont, slopeB]
  have : ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark (x + h • v) (P.gross ω)) ≤
      ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark x (P.gross ω)) +
        h * ∑ ω, P.prob t z ω * cost P (-(mark v (P.gross ω))) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun ω _ => by nlinarith [mul_le_mul_of_nonneg_left (hω ω) (hq ω)]
  nlinarith [mul_le_mul_of_nonneg_left this hβ.le]

/-- `G(x + h v) ≤ G(x) + h v'∇ + h²(γ/2) v'Σv + h · slope bound`. -/
lemma G_step (t : ℕ) (z : Z) (x v : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    G P t z (x + h • v) ≤ G P t z x + h * (v ⬝ᵥ grad P t z x) +
      h ^ 2 * (P.gamma / 2 * (v ⬝ᵥ (P.Sigma t z *ᵥ v))) + h * slopeB P t z v := by
  rw [G_eq, G_eq, track_add hS]
  have := cont_step hS t z x v hh
  simp only [dotProduct_smul, smul_dotProduct, mulVec_smul, smul_eq_mul] at *
  nlinarith

omit hS in
lemma mark_single (i : Fin n) (s : ℝ) (g : Fin n → ℝ) :
    mark (Pi.single i s) g = Pi.single i (s * g i) := by
  funext j; by_cases h : j = i
  · subst h; simp [mark]
  · simp [mark, h]

lemma slopeB_up (t : ℕ) (z : Z) (i : Fin n) :
    slopeB P t z (Pi.single i 1) = P.beta * P.km i * gb P t z i := by
  have hω : ∀ ω, cost P (-(mark (Pi.single i 1) (P.gross ω))) = P.km i * P.gross ω i := by
    intro ω
    have hg := hS.2.2.2.2.2.2.2.2.2.2 ω i
    rw [mark_single, one_mul, ← Pi.single_neg, cost_single, max_eq_right (by linarith), neg_neg,
      max_eq_left hg.le]
    ring
  simp only [slopeB, hω, gb, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

lemma slopeB_dn (t : ℕ) (z : Z) (i : Fin n) :
    slopeB P t z (Pi.single i (-1)) = P.beta * P.kp i * gb P t z i := by
  have hω : ∀ ω, cost P (-(mark (Pi.single i (-1)) (P.gross ω))) = P.kp i * P.gross ω i := by
    intro ω
    have hg := hS.2.2.2.2.2.2.2.2.2.2 ω i
    rw [mark_single, neg_one_mul, ← Pi.single_neg, neg_neg, cost_single, max_eq_left hg.le,
      max_eq_right (by linarith)]
    ring
  simp only [slopeB, hω, gb, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

end Value

/-! ### Part 2 -/

theorem outerParallelotope : OuterParallelotope := by
  intro n Z Ω _ P hS t z _ x hx hint i
  have hopt := hx.2.2
  have hk := hS.2.2.2.2.2.2.1 i
  have hd := diag_pos hS t z i
  have hγ := hS.2.2.2.1
  set δ0 := min (x i) (P.cap i - x i)
  have hδ0 : 0 < δ0 := lt_min (hint i).1 (by linarith [(hint i).2])
  have hmem : ∀ h : ℝ, 0 < h → h < δ0 → ∀ s : ℝ, (s = 1 ∨ s = -1) →
      x + h • Pi.single i s ∈ box P := by
    intro h hh hlt s hs j
    by_cases hj : j = i
    · subst hj
      have h1 : h < x j := lt_of_lt_of_le hlt (min_le_left _ _)
      have h2 : h < P.cap j - x j := lt_of_lt_of_le hlt (min_le_right _ _)
      rcases hs with rfl | rfl <;> simp <;> constructor <;> linarith
    · simp [hj]; exact hx.1 j
  have hgi : ∀ s : ℝ, Pi.single i s ⬝ᵥ grad P t z x = s * P.gamma * (P.Sigma t z *ᵥ (x - xstar P t z)) i := by
    intro s; simp [single_dotProduct, grad]; ring
  have hq : ∀ s : ℝ, Pi.single i s ⬝ᵥ (P.Sigma t z *ᵥ Pi.single i s) = P.Sigma t z i i * s ^ 2 :=
    quad_single P t z i
  have hcs : ∀ h : ℝ, 0 ≤ h → ∀ s : ℝ, cost P (x + h • Pi.single i s - x) = cost P (Pi.single i (h * s)) := by
    intro h _ s; congr 1; rw [add_sub_cancel_left, ← Pi.single_smul']; simp
  constructor
  · refine le_of_small (K := P.gamma / 2 * P.Sigma t z i i) hδ0 fun h hh hlt => ?_
    have h1 := hopt _ (hmem h hh hlt 1 (Or.inl rfl))
    have h2 := G_step hS t z x (Pi.single i 1) hh.le
    rw [sub_self, cost_zero, zero_add, hcs h hh.le, cost_single, slopeB_up hS, hgi, hq] at *
    rw [mul_one, max_eq_left hh.le, max_eq_right (by linarith)] at h1
    rw [abs_of_nonneg (by positivity)]
    have : 0 < h := hh
    nlinarith
  · refine le_of_small (K := P.gamma / 2 * P.Sigma t z i i) hδ0 fun h hh hlt => ?_
    have h1 := hopt _ (hmem h hh hlt (-1) (Or.inr rfl))
    have h2 := G_step hS t z x (Pi.single i (-1)) hh.le
    rw [sub_self, cost_zero, zero_add, hcs h hh.le, cost_single, slopeB_dn hS, hgi, hq] at *
    rw [mul_neg_one, max_eq_right (by linarith), neg_neg, max_eq_left hh.le] at h1
    rw [abs_of_nonneg (by positivity)]
    nlinarith


/-! ### Part 1a: the ETF-optimized value -/

section Ufun

variable {P : M6 (M + 1) Z Ω} (hS : Setting P) (t : ℕ) (z : Z) (pm : Fin M → ℝ)

omit [Fintype Ω] in
lemma ebox_compact : IsCompact (ebox P) := by
  have : ebox P = Set.Icc 0 (fun j => P.cap j.succ) := by
    ext p; simp [ebox, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this]; exact isCompact_Icc

omit [Fintype Ω] in
lemma ebox_convex : Convex ℝ (ebox P) := by
  intro x hx y hy a b ha hb hab j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith [(hx j).1, (hy j).1]
  · have hc : P.cap j.succ = a * P.cap j.succ + b * P.cap j.succ := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hx j).2 ha, mul_le_mul_of_nonneg_left (hy j).2 hb]

include hS

lemma zero_mem_ebox : (0 : Fin M → ℝ) ∈ ebox P := fun j => ⟨le_rfl, (hS.2.2.2.2.2.2.2.1 j.succ).le⟩

omit hS in
lemma costE_eq (u : Fin M → ℝ) : costE P u = cost P (join 0 u) := by
  rw [cost_join]; simp [costA]

lemma Fe_cont : Continuous (fun q : ℝ × (Fin M → ℝ) => Fe P t z pm q.1 q.2) := by
  have hj : Continuous (fun q : ℝ × (Fin M → ℝ) => join q.1 q.2) := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  have hc : Continuous (fun q : ℝ × (Fin M → ℝ) => costE P (q.2 - pm)) := by
    unfold costE; fun_prop
  exact ((G_facts hS t z).2.2.comp hj).add hc

lemma U_attain (a : ℝ) :
    ∃ p ∈ ebox P, (∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) ∧ U P t z pm a = Fe P t z pm a p := by
  have hc : Continuous (Fe P t z pm a) :=
    (Fe_cont hS t z pm).comp (continuous_const.prodMk continuous_id)
  obtain ⟨p, hp, hmin⟩ := (ebox_compact (P := P)).exists_isMinOn ⟨0, zero_mem_ebox hS⟩ hc.continuousOn
  refine ⟨p, hp, fun q hq => hmin hq, ?_⟩
  exact (IsLeast.csInf_eq ⟨Set.mem_image_of_mem _ hp, by rintro _ ⟨q, hq, rfl⟩; exact hmin hq⟩)

lemma U_le (a : ℝ) {q : Fin M → ℝ} (hq : q ∈ ebox P) : U P t z pm a ≤ Fe P t z pm a q := by
  obtain ⟨p, -, hmin, hU⟩ := U_attain hS t z pm a
  rw [hU]; exact hmin q hq

lemma U_eq_of_min (a : ℝ) {p : Fin M → ℝ} (hp : p ∈ ebox P)
    (hmin : ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) : U P t z pm a = Fe P t z pm a p :=
  le_antisymm (U_le hS t z pm a hp) (by
    obtain ⟨q, hq, -, hU⟩ := U_attain hS t z pm a; rw [hU]; exact hmin q hq)

lemma U_cont : Continuous (U P t z pm) :=
  (ebox_compact (P := P)).continuous_sInf (Fe_cont hS t z pm)

/-- The Schur remainder `w'Σ_EE w` is convex along segments. -/
lemma quadE_convex (u v : Fin M → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • u + b • v) ⬝ᵥ (SEE P t z *ᵥ (a • u + b • v)) ≤
      a * (u ⬝ᵥ (SEE P t z *ᵥ u)) + b * (v ⬝ᵥ (SEE P t z *ᵥ v)) := by
  have hsym : ∀ x y : Fin M → ℝ, x ⬝ᵥ (SEE P t z *ᵥ y) = y ⬝ᵥ (SEE P t z *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← mulVec_transpose, SEE_symm hS t z, dotProduct_comm]
  have hnn : 0 ≤ (u - v) ⬝ᵥ (SEE P t z *ᵥ (u - v)) := by
    by_cases h : u - v = 0
    · simp [h]
    · exact (SEE_quad_pos hS t z _ h).le
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [mulVec_add, mulVec_smul, mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul] at hnn ⊢
  rw [hsym v u] at hnn ⊢
  nlinarith [mul_nonneg ha hb]

/-- `Fe - (c^res/2)(a - a*)²` is jointly convex. -/
lemma H_convex (a1 a2 : ℝ) (p1 p2 : Fin M → ℝ) (θ φ : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    Fe P t z pm (θ * a1 + φ * a2) (θ • p1 + φ • p2) - cres P t z / 2 * (θ * a1 + φ * a2 - xstar P t z 0) ^ 2 ≤
      θ * (Fe P t z pm a1 p1 - cres P t z / 2 * (a1 - xstar P t z 0) ^ 2) +
        φ * (Fe P t z pm a2 p2 - cres P t z / 2 * (a2 - xstar P t z 0) ^ 2) := by
  set xs := xstar P t z
  have hxs : xs = join (xs 0) (fun j : Fin M => xs j.succ) := join_eta xs
  -- the tracking part through Schur
  have htr : ∀ a p, track P t z (join a p) - cres P t z / 2 * (a - xs 0) ^ 2 =
      P.gamma / 2 * (((p - fun j : Fin M => xs j.succ) + (a - xs 0) • rho P t z) ⬝ᵥ
        (SEE P t z *ᵥ ((p - fun j : Fin M => xs j.succ) + (a - xs 0) • rho P t z))) := by
    intro a p
    simp only [track]
    rw [show join a p - xstar P t z = join (a - xs 0) (p - fun j : Fin M => xs j.succ) by
      conv_lhs => rw [show xstar P t z = xs from rfl, hxs]
      rw [join_sub]]
    rw [schur hS t z, cres]; ring
  have hmix : ∀ a1 a2 : ℝ, ∀ p1 p2 : Fin M → ℝ,
      ((θ • p1 + φ • p2) - fun j : Fin M => xs j.succ) + (θ * a1 + φ * a2 - xs 0) • rho P t z =
        θ • ((p1 - fun j : Fin M => xs j.succ) + (a1 - xs 0) • rho P t z) +
          φ • ((p2 - fun j : Fin M => xs j.succ) + (a2 - xs 0) • rho P t z) := by
    intro a1 a2 p1 p2
    have e1 : (fun j : Fin M => xs j.succ) = θ • (fun j : Fin M => xs j.succ) + φ • (fun j : Fin M => xs j.succ) := by
      rw [← add_smul, hθφ, one_smul]
    have e2 : xs 0 = θ * xs 0 + φ * xs 0 := by rw [← add_mul, hθφ, one_mul]
    conv_lhs => rw [e1, e2]
    funext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hq := quadE_convex hS t z ((p1 - fun j : Fin M => xs j.succ) + (a1 - xs 0) • rho P t z)
    ((p2 - fun j : Fin M => xs j.succ) + (a2 - xs 0) • rho P t z) θ φ hθ hφ hθφ
  rw [← hmix] at hq
  -- the continuation and cost parts
  have hj : join (θ * a1 + φ * a2) (θ • p1 + φ • p2) = θ • join a1 p1 + φ • join a2 p2 := by
    rw [join_smul, join_smul, join_add]
  have hcont := (cont_convex hS t z).2 (Set.mem_univ (join a1 p1)) (Set.mem_univ (join a2 p2)) hθ hφ hθφ
  have hce : costE P ((θ • p1 + φ • p2) - pm) ≤ θ * costE P (p1 - pm) + φ * costE P (p2 - pm) := by
    rw [costE_eq, costE_eq, costE_eq]
    have e : join 0 ((θ • p1 + φ • p2) - pm) = θ • join 0 (p1 - pm) + φ • join 0 (p2 - pm) := by
      rw [join_smul, join_smul, join_add]
      congr 1
      · ring
      · have : pm = θ • pm + φ • pm := by rw [← add_smul, hθφ, one_smul]
        conv_lhs => rw [this]
        funext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact (cost_convex hS).2 (Set.mem_univ _) (Set.mem_univ _) hθ hφ hθφ
  have hγ := hS.2.2.2.1
  simp only [Fe, G_eq]
  have t1 := htr (θ * a1 + φ * a2) (θ • p1 + φ • p2)
  have t2 := htr a1 p1
  have t3 := htr a2 p2
  rw [hj] at t1 ⊢
  simp only [smul_eq_mul] at hcont
  nlinarith [mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ P.gamma / 2)]

lemma U_strong : ConvexOn ℝ Set.univ (fun a => U P t z pm a - cres P t z / 2 * (a - xstar P t z 0) ^ 2) := by
  refine ⟨convex_univ, fun a1 _ a2 _ θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨p1, hp1, -, hU1⟩ := U_attain hS t z pm a1
  obtain ⟨p2, hp2, -, hU2⟩ := U_attain hS t z pm a2
  have hmem := ebox_convex hp1 hp2 hθ hφ hθφ
  have h1 := U_le hS t z pm (θ * a1 + φ * a2) hmem
  have h2 := H_convex hS t z pm a1 a2 p1 p2 θ φ hθ hφ hθφ
  simp only [smul_eq_mul] at *
  rw [hU1, hU2]
  linarith

lemma U_strong0 : ConvexOn ℝ Set.univ (fun a => U P t z pm a - cres P t z / 2 * a ^ 2) := by
  refine ⟨convex_univ, fun a1 _ a2 _ θ φ hθ hφ hθφ => ?_⟩
  have h := (U_strong hS t z pm).2 (Set.mem_univ a1) (Set.mem_univ a2) hθ hφ hθφ
  simp only [smul_eq_mul] at h ⊢
  have hφ' : φ = 1 - θ := by linarith
  subst hφ'
  set c := cres P t z
  set x := xstar P t z 0
  have e : (-(c / 2 * (θ * a1 + (1 - θ) * a2) ^ 2)) - (-(c / 2 * (θ * a1 + (1 - θ) * a2 - x) ^ 2)) =
      θ * (-(c / 2 * a1 ^ 2) - -(c / 2 * (a1 - x) ^ 2)) + (1 - θ) * (-(c / 2 * a2 ^ 2) - -(c / 2 * (a2 - x) ^ 2)) := by
    ring
  linarith

lemma U_strict : StrictConvexOn ℝ Set.univ (U P t z pm) := by
  have hc := cres_pos hS t z
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have h := (U_strong0 hS t z pm).2 (Set.mem_univ x) (Set.mem_univ y) ha.le hb.le hab
  simp only [smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hq : 0 < a * (1 - a) * (x - y) ^ 2 :=
    mul_pos (mul_pos ha hb) (by have := sub_ne_zero.2 hxy; positivity)
  have e : a * x ^ 2 + (1 - a) * y ^ 2 - (a * x + (1 - a) * y) ^ 2 = a * (1 - a) * (x - y) ^ 2 := by ring
  nlinarith [mul_lt_mul_of_pos_left hq (by linarith : (0 : ℝ) < cres P t z / 2)]

lemma U_convex : ConvexOn ℝ Set.univ (U P t z pm) := (U_strict hS t z pm).convexOn

end Ufun



/-! ### Parts 1a and 1b -/

section Part1ab

variable {P : M6 (M + 1) Z Ω} (hS : Setting P)
include hS

lemma kpA : 0 ≤ P.kp 0 := (hS.2.2.2.2.2.2.1 0).1
lemma kmA : 0 ≤ P.km 0 := (hS.2.2.2.2.2.2.1 0).2.2.1
lemma capA : 0 < P.cap 0 := hS.2.2.2.2.2.2.2.1 0

omit hS in
lemma Fobj_join (t : ℕ) (z : Z) (am a : ℝ) (pm p : Fin M → ℝ) :
    cost P (join a p - join am pm) + G P t z (join a p) = costA P (a - am) + Fe P t z pm a p := by
  rw [join_sub, cost_join, Fe]; ring

lemma opt_iff (t : ℕ) (z : Z) (pm : Fin M → ℝ) (am a : ℝ) (p : Fin M → ℝ) :
    IsOpt P t z (join am pm) (join a p) ↔
      (0 ≤ a ∧ a ≤ P.cap 0 ∧
        ∀ b, 0 ≤ b → b ≤ P.cap 0 → costA P (a - am) + U P t z pm a ≤ costA P (b - am) + U P t z pm b) ∧
      p ∈ ebox P ∧ ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q := by
  constructor
  · rintro ⟨hbox, hmin⟩
    obtain ⟨⟨ha0, hac⟩, hp⟩ := (mem_box_join P a p).1 hbox
    have hFa : ∀ y ∈ box P, costA P (a - am) + Fe P t z pm a p ≤
        cost P (y - join am pm) + G P t z y := by
      intro y hy; rw [← Fobj_join]; exact hmin y hy
    refine ⟨⟨ha0, hac, fun b hb0 hbc => ?_⟩, hp, fun q hq => ?_⟩
    · obtain ⟨pb, hpb, -, hUb⟩ := U_attain hS t z pm b
      have h1 := hFa (join b pb) ((mem_box_join P b pb).2 ⟨⟨hb0, hbc⟩, hpb⟩)
      rw [Fobj_join] at h1
      have h2 := U_le hS t z pm a hp
      rw [hUb]; linarith
    · have h1 := hFa (join a q) ((mem_box_join P a q).2 ⟨⟨ha0, hac⟩, hq⟩)
      rw [Fobj_join] at h1; linarith
  · rintro ⟨⟨ha0, hac, hamin⟩, hp, hpmin⟩
    refine ⟨(mem_box_join P a p).2 ⟨⟨ha0, hac⟩, hp⟩, fun y hy => ?_⟩
    rw [join_eta y] at hy ⊢
    obtain ⟨⟨hy0, hyc⟩, hyE⟩ := (mem_box_join P _ _).1 hy
    rw [Fobj_join, Fobj_join]
    have h1 := hamin (y 0) hy0 hyc
    have h2 := U_le hS t z pm (y 0) hyE
    have h3 := U_eq_of_min hS t z pm a hp hpmin
    linarith

omit hS in
theorem effectiveBand : EffectiveBand := by
  intro M Z Ω _ P hS t z _ pm
  have hk := kpA hS; have hm := kmA hS; have hcap := capA hS
  have hU := U_convex hS t z pm
  refine ⟨cres_pos hS t z, U_cont hS t z pm, U_strong0 hS t z pm, (loF_bounds hcap).1,
    loF_le_hiF hU hk hm hcap, (hiF_bounds hcap).2, fun am a p => ⟨opt_iff hS t z pm am a p, fun h => ?_⟩⟩
  obtain ⟨⟨ha0, hac, hamin⟩, -, -⟩ := (opt_iff hS t z pm am a p).1 h
  have hpm := projF_mem hU hk hm hcap am
  have heq : a = projF (U P t z pm) (P.kp 0) (P.km 0) (P.cap 0) am :=
    min_unique hk hm (U_strict hS t z pm) am ⟨ha0, hac⟩ hpm
      (fun y hy0 hyc => hamin y hy0 hyc)
      (fun y hy0 hyc => optF hU hk hm hcap am hy0 hyc)
  have hlh : loU P t z pm ≤ hiU P t z pm := loF_le_hiF hU hk hm hcap
  refine ⟨heq, ?_⟩
  rw [heq]
  change min (max am (loU P t z pm)) (hiU P t z pm) = am ↔ _
  constructor
  · intro h
    constructor
    · by_contra hlt; push Not at hlt
      rw [max_eq_right hlt.le, min_eq_left hlh] at h; linarith
    · rw [← h]; exact min_le_right _ _
  · rintro ⟨h1, h2⟩; rw [max_eq_left h1, min_eq_left h2]

omit hS in
theorem residualCeiling : ResidualCeiling := by
  intro M Z Ω _ P hS t z _ pm
  exact ceilingF (U_strong0 hS t z pm) (cres_pos hS t z) (U_convex hS t z pm) (kpA hS) (kmA hS) (capA hS)

end Part1ab


/-! ### Part 1c -/

section Part1c

variable {P : M6 (M + 1) Z Ω} (hS : Setting P)
include hS

lemma costE_add (u v : Fin M → ℝ) : costE P (u + v) ≤ costE P u + costE P v := by
  rw [costE_eq, costE_eq, costE_eq, ← show join (0 : ℝ) u + join 0 v = join 0 (u + v) by
    rw [join_add, add_zero]]
  exact cost_subadd hS _ _

omit hS in
lemma costE_smul {h : ℝ} (hh : 0 ≤ h) (v : Fin M → ℝ) : costE P (h • v) = h * costE P v := by
  rw [costE_eq, costE_eq, ← cost_smul P hh, join_smul, mul_zero]

omit hS [Fintype Ω] in
/-- Small moves from an interior ETF holding stay in the box. -/
lemma interior_shift {p : Fin M → ℝ} (hp : Interior P p) (w : Fin M → ℝ) :
    ∃ δ0 > 0, ∀ h : ℝ, |h| < δ0 → p + h • w ∈ ebox P := by
  have hopen : IsOpen (Set.pi Set.univ fun j : Fin M => Set.Ioo (0 : ℝ) (P.cap j.succ)) :=
    isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo
  have hmem : p ∈ Set.pi Set.univ fun j : Fin M => Set.Ioo (0 : ℝ) (P.cap j.succ) :=
    fun j _ => ⟨(hp j).1, (hp j).2⟩
  have hc : Continuous (fun h : ℝ => p + h • w) := by fun_prop
  have hmem0 : (fun h : ℝ => p + h • w) 0 ∈ Set.pi Set.univ fun j : Fin M => Set.Ioo (0 : ℝ) (P.cap j.succ) := by
    simpa using hmem
  have hev := (hc.continuousAt (x := 0)).eventually (hopen.mem_nhds hmem0)
  obtain ⟨δ0, hδ0, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ0, hδ0, fun h hh j => ?_⟩
  have := hball (by simpa [Real.dist_eq] using hh) j (Set.mem_univ j)
  exact ⟨this.1.le, this.2.le⟩

/-- The gradient along a join: `(u_A, u_E)'∇ = γ (u_A, u_E)'Σ d`. -/
lemma grad_hedge (t : ℕ) (z : Z) (a : ℝ) (p : Fin M → ℝ) (s : ℝ) :
    join s (-(s • rho P t z)) ⬝ᵥ grad P t z (join a p) = s * (cres P t z * (a - xstar P t z 0)) := by
  have hx : xstar P t z = join (xstar P t z 0) (fun j : Fin M => xstar P t z j.succ) := join_eta _
  have e : join s (-(s • rho P t z)) = s • join 1 (-rho P t z) := by
    rw [join_smul, mul_one, smul_neg]
  simp only [grad, dotProduct_smul, smul_eq_mul]
  rw [hx, join_sub, e, smul_dotProduct, hedge_dir hS, ← hx, cres, smul_eq_mul]
  ring

omit hS in
lemma max_mul_pos {g : ℝ} (hg : 0 < g) (a : ℝ) : max (a * g) 0 = g * max a 0 := by
  rw [mul_comm, max_smul0 hg.le]

/-- The continuation-plus-ETF-cost slope along `(-1, ρ)` is `β κ⁺_A ḡ_A + H⁺`. -/
lemma slope_up (t : ℕ) (z : Z) :
    slopeB P t z (join (-1) (rho P t z)) + costE P (rho P t z) =
      P.beta * P.kp 0 * gb P t z 0 + Hplus P t z := by
  have hω : ∀ ω, cost P (-(mark (join (-1) (rho P t z)) (P.gross ω))) =
      P.kp 0 * P.gross ω 0 + ∑ j, P.gross ω j.succ *
        (P.kp j.succ * max (-rho P t z j) 0 + P.km j.succ * max (rho P t z j) 0) := by
    intro ω
    have hg0 := hS.2.2.2.2.2.2.2.2.2.2 ω 0
    simp only [cost, sum_join, mark, Pi.neg_apply, join_zero, join_succ]
    rw [show -(-1 * P.gross ω 0) = P.gross ω 0 by ring, max_eq_left hg0.le,
      show -(P.gross ω 0) = -1 * P.gross ω 0 by ring, max_eq_right (by nlinarith)]
    congr 1
    · ring
    · refine sum_congr rfl fun j _ => ?_
      have hg := hS.2.2.2.2.2.2.2.2.2.2 ω j.succ
      rw [show -(rho P t z j * P.gross ω j.succ) = -rho P t z j * P.gross ω j.succ by ring,
        max_mul_pos hg, neg_mul, neg_neg, max_mul_pos hg]
      ring
  have e1 : ∑ ω, P.prob t z ω * cost P (-(mark (join (-1) (rho P t z)) (P.gross ω))) =
      P.kp 0 * gb P t z 0 + ∑ j, (P.kp j.succ * max (-rho P t z j) 0 +
        P.km j.succ * max (rho P t z j) 0) * gb P t z j.succ := by
    set c : Fin M → ℝ := fun j => P.kp j.succ * max (-rho P t z j) 0 + P.km j.succ * max (rho P t z j) 0
    calc ∑ ω, P.prob t z ω * cost P (-(mark (join (-1) (rho P t z)) (P.gross ω)))
        = ∑ ω, (P.prob t z ω * (P.kp 0 * P.gross ω 0) +
            ∑ j, P.prob t z ω * (P.gross ω j.succ * c j)) :=
          sum_congr rfl fun ω _ => by rw [hω, mul_add, mul_sum]
      _ = P.kp 0 * ∑ ω, P.prob t z ω * P.gross ω 0 +
            ∑ ω, ∑ j, P.prob t z ω * (P.gross ω j.succ * c j) := by
          rw [sum_add_distrib, mul_sum]; congr 1; exact sum_congr rfl fun _ _ => by ring
      _ = P.kp 0 * gb P t z 0 + ∑ j, c j * gb P t z j.succ := by
          rw [sum_comm]; congr 1
          exact sum_congr rfl fun j _ => by
            rw [gb, mul_sum]; exact sum_congr rfl fun ω _ => by ring
  simp only [slopeB, e1, Hplus, costE]
  rw [mul_add, mul_sum, add_assoc, ← sum_add_distrib]
  congr 1
  · ring
  · exact sum_congr rfl fun j _ => by ring

/-- The slope along `(1, -ρ)` is `β κ⁻_A ḡ_A + H⁻`. -/
lemma slope_dn (t : ℕ) (z : Z) :
    slopeB P t z (join 1 (-rho P t z)) + costE P (-rho P t z) =
      P.beta * P.km 0 * gb P t z 0 + Hminus P t z := by
  set c : Fin M → ℝ := fun j => P.kp j.succ * max (rho P t z j) 0 + P.km j.succ * max (-rho P t z j) 0
  have hω : ∀ ω, cost P (-(mark (join 1 (-rho P t z)) (P.gross ω))) =
      P.km 0 * P.gross ω 0 + ∑ j, P.gross ω j.succ * c j := by
    intro ω
    have hg0 := hS.2.2.2.2.2.2.2.2.2.2 ω 0
    simp only [cost, sum_join, mark, Pi.neg_apply, join_zero, join_succ]
    rw [show -(1 * P.gross ω 0) = -P.gross ω 0 by ring, max_eq_right (by linarith), neg_neg,
      max_eq_left hg0.le]
    congr 1
    · ring
    · refine sum_congr rfl fun j _ => ?_
      have hg := hS.2.2.2.2.2.2.2.2.2.2 ω j.succ
      rw [show -(-rho P t z j * P.gross ω j.succ) = rho P t z j * P.gross ω j.succ by ring,
        show -(rho P t z j * P.gross ω j.succ) = -rho P t z j * P.gross ω j.succ by ring,
        max_mul_pos hg, max_mul_pos hg]
      simp only [c]; ring
  have e1 : ∑ ω, P.prob t z ω * cost P (-(mark (join 1 (-rho P t z)) (P.gross ω))) =
      P.km 0 * gb P t z 0 + ∑ j, c j * gb P t z j.succ := by
    calc ∑ ω, P.prob t z ω * cost P (-(mark (join 1 (-rho P t z)) (P.gross ω)))
        = ∑ ω, (P.prob t z ω * (P.km 0 * P.gross ω 0) +
            ∑ j, P.prob t z ω * (P.gross ω j.succ * c j)) :=
          sum_congr rfl fun ω _ => by rw [hω, mul_add, mul_sum]
      _ = P.km 0 * ∑ ω, P.prob t z ω * P.gross ω 0 +
            ∑ ω, ∑ j, P.prob t z ω * (P.gross ω j.succ * c j) := by
          rw [sum_add_distrib, mul_sum]; congr 1; exact sum_congr rfl fun _ _ => by ring
      _ = P.km 0 * gb P t z 0 + ∑ j, c j * gb P t z j.succ := by
          rw [sum_comm]; congr 1
          exact sum_congr rfl fun j _ => by
            rw [gb, mul_sum]; exact sum_congr rfl fun ω _ => by ring
  simp only [slopeB, e1, Hminus, costE, Pi.neg_apply, neg_neg]
  rw [mul_add, mul_sum, add_assoc, ← sum_add_distrib]
  congr 1
  · ring
  · exact sum_congr rfl fun j _ => by simp only [c]; ring

omit hS in
lemma join_hedge (a h : ℝ) (p r : Fin M → ℝ) (s : ℝ) :
    join (a + h * s) (p + h • (-(s • r))) = join a p + h • join s (-(s • r)) := by
  rw [join_smul, join_add]

/-- The quadratic coefficient along `(s, -sρ)`. -/
def Kq (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (s : ℝ) : ℝ :=
  P.gamma / 2 * (join s (-(s • rho P t z)) ⬝ᵥ (P.Sigma t z *ᵥ join s (-(s • rho P t z))))

/-- The slope bound along `(s, -sρ)`. -/
def Sl (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (s : ℝ) : ℝ :=
  slopeB P t z (join s (-(s • rho P t z))) + costE P (-(s • rho P t z))

lemma Sl_up (t : ℕ) (z : Z) : Sl P t z (-1) = P.beta * P.kp 0 * gb P t z 0 + Hplus P t z := by
  rw [Sl, neg_smul, one_smul, neg_neg]; exact slope_up hS t z

lemma Sl_dn (t : ℕ) (z : Z) : Sl P t z 1 = P.beta * P.km 0 * gb P t z 0 + Hminus P t z := by
  rw [Sl, one_smul]; exact slope_dn hS t z

/-- One step along `(s, -sρ)` from an ETF optimizer. -/
lemma U_step (t : ℕ) (z : Z) (pm p : Fin M → ℝ) (a s h : ℝ) (hp : p ∈ ebox P) (hh : 0 ≤ h)
    (hmin : ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) (hq : p + h • (-(s • rho P t z)) ∈ ebox P) :
    U P t z pm (a + h * s) ≤ U P t z pm a + h * (s * (cres P t z * (a - xstar P t z 0))) +
      h ^ 2 * Kq P t z s + h * Sl P t z s := by
  have h1 := U_le hS t z pm (a + h * s) hq
  have h2 := G_step hS t z (join a p) (join s (-(s • rho P t z))) hh
  have h3 : costE P (p + h • (-(s • rho P t z)) - pm) ≤ costE P (p - pm) + h * costE P (-(s • rho P t z)) := by
    rw [show p + h • (-(s • rho P t z)) - pm = (p - pm) + h • (-(s • rho P t z)) by abel,
      ← costE_smul hh]
    exact costE_add hS _ _
  have hU0 := U_eq_of_min hS t z pm a hp hmin
  rw [grad_hedge hS] at h2
  simp only [Fe] at h1 hU0
  rw [join_hedge] at h1
  simp only [Kq, Sl]
  nlinarith

omit hS in
theorem outerBracket : OuterBracket := by
  intro M Z Ω _ P hS t z _ pm p
  have hU := U_convex hS t z pm
  have hc := cres_pos hS t z
  constructor
  · intro hhi hp hint hmin
    set hi := hiU P t z pm
    have hld : ld (U P t z pm) hi ≤ P.km 0 := ld_hiF hU hhi
    obtain ⟨δ0, hδ0, hshift⟩ := interior_shift hint (-((-1 : ℝ) • rho P t z))
    have key := le_of_small (A := cres P t z * (hi - xstar P t z 0))
      (B := P.km 0 + Sl P t z (-1)) (K := Kq P t z (-1)) hδ0 fun h hh hlt => by
      have hq := hshift h (by rw [abs_of_pos hh]; exact hlt)
      have h1 := U_step hS t z pm p hi (-1) h hp hh.le hmin hq
      have h4 := slope_le_ld hU (show hi + h * (-1) < hi by linarith)
      rw [show hi - (hi + h * -1) = h by ring] at h4
      have h5 : h * (cres P t z * (hi - xstar P t z 0)) ≤ h * (P.km 0 + Sl P t z (-1) + Kq P t z (-1) * h) := by
        nlinarith [mul_le_mul_of_nonneg_right hld hh.le]
      have h6 := le_of_mul_le_mul_left h5 hh
      nlinarith [le_abs_self (Kq P t z (-1))]
    rw [Sl_up hS] at key
    rw [← sub_le_iff_le_add', le_div_iff₀ hc]
    linarith
  · intro hlo hp hint hmin
    set lo := loU P t z pm
    have hrd : -P.kp 0 ≤ rd (U P t z pm) lo := rd_loF hU hlo
    obtain ⟨δ0, hδ0, hshift⟩ := interior_shift hint (-((1 : ℝ) • rho P t z))
    have key := le_of_small (A := -(P.kp 0 + Sl P t z 1))
      (B := cres P t z * (lo - xstar P t z 0)) (K := Kq P t z 1) hδ0 fun h hh hlt => by
      have hq := hshift h (by rw [abs_of_pos hh]; exact hlt)
      have h1 := U_step hS t z pm p lo 1 h hp hh.le hmin hq
      have h4 := rd_le_slope hU (show lo < lo + h * 1 by linarith)
      rw [show lo + h * 1 - lo = h by ring] at h4
      have h5 : h * (-(P.kp 0 + Sl P t z 1) - Kq P t z 1 * h) ≤ h * (cres P t z * (lo - xstar P t z 0)) := by
        nlinarith [mul_le_mul_of_nonneg_right hrd hh.le]
      have h6 := le_of_mul_le_mul_left h5 hh
      nlinarith [le_abs_self (Kq P t z 1)]
    rw [Sl_dn hS] at key
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hc]
    linarith

end Part1c


/-! ### Part 1d -/

section Part1d

variable {P : M6 (M + 1) Z Ω} (hS : Setting P)
include hS

/-- At the last review `G` is the tracking loss. -/
lemma G_lastT {t : ℕ} (ht : P.T ≤ t + 1) (z : Z) (x : Fin (M + 1) → ℝ) : G P t z x = track P t z x := by
  rw [G_eq]
  have : cont P t z x = 0 := by
    simp only [cont]
    rw [sum_eq_zero fun ω _ => by rw [V_ge P ht, mul_zero], mul_zero]
  rw [this, add_zero]

/-- A move along one coordinate changes the tracking loss exactly. -/
lemma track_move (t : ℕ) (z : Z) (x : Fin (M + 1) → ℝ) (i : Fin (M + 1)) (s : ℝ) :
    track P t z (x + s • Pi.single i 1) = track P t z x + s * grad P t z x i +
      P.gamma / 2 * P.Sigma t z i i * s ^ 2 := by
  rw [track_add hS, smul_dotProduct, single_dotProduct, ← Pi.single_smul, quad_single]
  simp; ring

omit hS in
lemma join_single0 (a s : ℝ) (p : Fin M → ℝ) : join (a + s) p = join a p + s • Pi.single 0 1 := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [join, Fin.succ_ne_zero]

omit hS in
lemma join_singleE (a s : ℝ) (p : Fin M → ℝ) (j : Fin M) :
    join a (p + s • Pi.single j 1) = join a p + s • Pi.single j.succ 1 := by
  funext i; refine Fin.cases ?_ (fun j' => ?_) i
  · simp [join, (Fin.succ_ne_zero j).symm]
  · by_cases h : j' = j
    · subst h; simp [join]
    · simp [join, h, Fin.succ_inj]

/-- At the last review `U` is differentiable at `a` with derivative `γ(Σd)_A` at an ETF optimizer. -/
lemma U_deriv_last {t : ℕ} (ht : P.T ≤ t + 1) (z : Z) (pm p : Fin M → ℝ) (a : ℝ) (hp : p ∈ ebox P)
    (hmin : ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) :
    grad P t z (join a p) 0 ≤ ld (U P t z pm) a ∧ rd (U P t z pm) a ≤ grad P t z (join a p) 0 := by
  have hU := U_convex hS t z pm
  have hU0 := U_eq_of_min hS t z pm a hp hmin
  set g := grad P t z (join a p) 0
  set K := P.gamma / 2 * P.Sigma t z 0 0
  have hC : ∀ s : ℝ, U P t z pm (a + s) ≤ U P t z pm a + s * g + K * s ^ 2 := by
    intro s
    have h1 := U_le hS t z pm (a + s) hp
    simp only [Fe, G_lastT hS ht] at h1 hU0
    rw [join_single0, track_move hS] at h1
    dsimp only [g, K]
    linarith
  constructor
  · refine le_of_small (A := g) (B := ld (U P t z pm) a) (K := K) one_pos fun h hh _ => ?_
    have h1 := hC (-h)
    have h2 := slope_le_ld hU (show a + -h < a by linarith)
    rw [show a - (a + -h) = h by ring] at h2
    have h3 : h * g ≤ h * (ld (U P t z pm) a + |K| * h) := by
      nlinarith [le_abs_self K, sq_nonneg h]
    exact le_of_mul_le_mul_left h3 hh
  · refine le_of_small (A := rd (U P t z pm) a) (B := g) (K := K) one_pos fun h hh _ => ?_
    have h1 := hC h
    have h2 := rd_le_slope hU (show a < a + h by linarith)
    rw [show a + h - a = h by ring] at h2
    have h3 : h * rd (U P t z pm) a ≤ h * (g + |K| * h) := by
      nlinarith [le_abs_self K, sq_nonneg h]
    exact le_of_mul_le_mul_left h3 hh

omit hS in
/-- One coordinate of the ETF cost. -/
lemma costE_single (v : Fin M → ℝ) (j : Fin M) (s : ℝ) :
    costE P (v + s • Pi.single j 1) = costE P v + (c1 (P.kp j.succ) (P.km j.succ) (v j + s) -
      c1 (P.kp j.succ) (P.km j.succ) (v j)) := by
  unfold costE c1
  rw [← sub_eq_iff_eq_add', ← sum_sub_distrib]
  rw [sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  simp

omit hS in
lemma c1_subadd {kp km : ℝ} (hk : 0 ≤ kp) (hm : 0 ≤ km) (u s : ℝ) :
    c1 kp km (u + s) ≤ c1 kp km u + c1 kp km s := by
  unfold c1
  have h1 : max (u + s) 0 ≤ max u 0 + max s 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have h2 : max (-(u + s)) 0 ≤ max (-u) 0 + max (-s) 0 :=
    max_le (by rw [neg_add]; exact add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hm]

/-- At the last review an interior ETF optimizer's slopes `-γ(Σd)_E` lie in the trade-sign sets. -/
lemma tradeSign_of_min {t : ℕ} (ht : P.T ≤ t + 1) (z : Z) (pm p : Fin M → ℝ) (a : ℝ) (_hp : p ∈ ebox P)
    (hint : Interior P p) (hmin : ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) (j : Fin M) :
    TradeSign (P.kp j.succ) (P.km j.succ) (p j - pm j) (-grad P t z (join a p) j.succ) := by
  obtain ⟨δ0, hδ0, hshift⟩ := interior_shift hint (Pi.single j 1)
  have hk := (hS.2.2.2.2.2.2.1 j.succ).1
  have hm := (hS.2.2.2.2.2.2.1 j.succ).2.2.1
  set g := grad P t z (join a p) j.succ
  set K := P.gamma / 2 * P.Sigma t z j.succ j.succ
  set u := p j - pm j
  set kp := P.kp j.succ
  set km := P.km j.succ
  have base : ∀ s : ℝ, |s| < δ0 → 0 ≤ s * g + K * s ^ 2 + (c1 kp km (u + s) - c1 kp km u) := by
    intro s hs
    have h1 := hmin _ (hshift s hs)
    simp only [Fe, G_lastT hS ht] at h1
    rw [show p + s • Pi.single j 1 - pm = (p - pm) + s • Pi.single j 1 by abel, costE_single,
      join_singleE, track_move hS] at h1
    simp only [Pi.sub_apply] at h1
    dsimp only [g, K, u, kp, km]
    linarith
  -- `δ ↦ h < δ0` small moves
  have small : ∀ h, 0 < h → h < δ0 → |h| < δ0 ∧ |-h| < δ0 := fun h hh hlt =>
    ⟨by rw [abs_of_pos hh]; exact hlt, by rw [abs_neg, abs_of_pos hh]; exact hlt⟩
  have c1_pos : ∀ v, 0 ≤ v → c1 kp km v = kp * v := fun v hv => by
    simp [c1, max_eq_left hv, max_eq_right (by linarith : -v ≤ 0)]
  have c1_neg : ∀ v, v ≤ 0 → c1 kp km v = km * (-v) := fun v hv => by
    simp [c1, max_eq_right hv, max_eq_left (by linarith : 0 ≤ -v)]
  -- `-g ≤ κ⁺`
  have up : -g ≤ kp := le_of_small (K := K) hδ0 fun h hh hlt => by
    have hb := base h (small h hh hlt).1
    have hsub := c1_subadd hk hm u h
    rw [c1_pos h hh.le] at hsub
    have : h * (-g) ≤ h * (kp + |K| * h) := by nlinarith [le_abs_self K]
    exact le_of_mul_le_mul_left this hh
  -- `-κ⁻ ≤ -g`
  have dn : -km ≤ -g := le_of_small (K := K) hδ0 fun h hh hlt => by
    have hb := base (-h) (small h hh hlt).2
    have hsub := c1_subadd hk hm u (-h)
    rw [c1_neg (-h) (by linarith), neg_neg] at hsub
    have : h * (-km) ≤ h * (-g + |K| * h) := by nlinarith [le_abs_self K]
    exact le_of_mul_le_mul_left this hh
  refine ⟨fun hu => le_antisymm up ?_, fun hu => le_antisymm ?_ dn, dn, up⟩
  · refine le_of_small (K := K) (lt_min hδ0 hu) fun h hh hlt => ?_
    have hlt0 := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt1 := lt_of_lt_of_le hlt (min_le_right _ _)
    have hb := base (-h) (small h hh hlt0).2
    rw [c1_pos (u + -h) (by linarith), c1_pos u hu.le] at hb
    have : h * kp ≤ h * (-g + |K| * h) := by nlinarith [le_abs_self K]
    exact le_of_mul_le_mul_left this hh
  · refine le_of_small (K := K) (lt_min hδ0 (neg_pos.2 hu)) fun h hh hlt => ?_
    have hlt0 := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt1 := lt_of_lt_of_le hlt (min_le_right _ _)
    have hb := base h (small h hh hlt0).1
    rw [c1_neg (u + h) (by linarith), c1_neg u hu.le] at hb
    have : h * (-g) ≤ h * (-km + |K| * h) := by nlinarith [le_abs_self K]
    exact le_of_mul_le_mul_left this hh

/-- `c^res (a - a*) = γ(Σd)_A + ρ'c` with `c = -γ(Σd)_E`. -/
lemma edge_identity (t : ℕ) (z : Z) (a : ℝ) (p : Fin M → ℝ) :
    cres P t z * (a - xstar P t z 0) =
      grad P t z (join a p) 0 + rho P t z ⬝ᵥ (fun j => -grad P t z (join a p) j.succ) := by
  have h := grad_hedge hS t z a p 1
  rw [one_smul, one_mul, join_eta (grad P t z (join a p)), dot_join, neg_dotProduct] at h
  have e2 : (rho P t z ⬝ᵥ fun j => -grad P t z (join a p) j.succ) =
      -(rho P t z ⬝ᵥ fun j => grad P t z (join a p) j.succ) := by
    simp only [dotProduct, mul_neg, sum_neg_distrib]
  rw [e2]; linarith

/-- `(∇_x)_A = γ(Σ_AA (a - a*) + Σ_AE (p - x*_E))`. -/
lemma grad0_join (t : ℕ) (z : Z) (a : ℝ) (p : Fin M → ℝ) :
    grad P t z (join a p) 0 = P.gamma * (P.Sigma t z 0 0 * (a - xstar P t z 0) +
      SEA P t z ⬝ᵥ (p - fun j : Fin M => xstar P t z j.succ)) := by
  have hx : xstar P t z = join (xstar P t z 0) (fun j : Fin M => xstar P t z j.succ) := join_eta _
  simp only [grad, Pi.smul_apply, smul_eq_mul]
  rw [hx, join_sub, ← hx]
  simp only [mulVec, dotProduct, sum_join, join_zero, join_succ, SEA, sig_symm hS t z 0 (Fin.succ _)]

/-- Optimality at two fund holdings: the cross term `γ (a - b) Σ_AE (p_a - p_b) ≤ 0`. -/
lemma cross_le {t : ℕ} (ht : P.T ≤ t + 1) (z : Z) (pm pa pb : Fin M → ℝ) (a b : ℝ) (hpa : pa ∈ ebox P)
    (hpb : pb ∈ ebox P) (ha : ∀ q ∈ ebox P, Fe P t z pm a pa ≤ Fe P t z pm a q)
    (hb : ∀ q ∈ ebox P, Fe P t z pm b pb ≤ Fe P t z pm b q) :
    P.gamma * (a - b) * (SEA P t z ⬝ᵥ (pa - pb)) ≤ 0 := by
  have h1 := ha pb hpb
  have h2 := hb pa hpa
  simp only [Fe, G_lastT hS ht, track] at h1 h2
  have hx : xstar P t z = join (xstar P t z 0) (fun j : Fin M => xstar P t z j.succ) := join_eta _
  rw [hx] at h1 h2
  simp only [join_sub, bil_join hS] at h1 h2
  have e : ∀ u v : Fin M → ℝ, SEA P t z ⬝ᵥ (u - v) = SEA P t z ⬝ᵥ u - SEA P t z ⬝ᵥ v := fun u v =>
    dotProduct_sub _ _ _
  have e2 : pa - pb = (pa - fun j : Fin M => xstar P t z j.succ) - (pb - fun j : Fin M => xstar P t z j.succ) := by
    abel
  rw [e2, e]
  nlinarith

lemma grad_diff0 (t : ℕ) (z : Z) (a b : ℝ) (p : Fin M → ℝ) :
    grad P t z (join a p) 0 - grad P t z (join b p) 0 = P.gamma * P.Sigma t z 0 0 * (a - b) := by
  have e : join a p = join b p + (a - b) • Pi.single 0 1 := by rw [← join_single0]; ring_nf
  rw [e, grad, grad, add_sub_right_comm, mulVec_add, mulVec_smul]
  simp [mulVec, dotProduct]
  ring

omit hS in
theorem lastReview : LastReview := by
  intro M Z Ω _ P hS z pm t IsEOpt
  have hT1 : P.T ≤ t + 1 := by have := hS.1; simp only [t]; omega
  have hU := U_convex hS t z pm
  have hk := kpA hS; have hm := kmA hS; have hcap := capA hS
  have hc := cres_pos hS t z
  -- the first-order conditions at the edges
  have fhi : ∀ p, 0 < hiU P t z pm → hiU P t z pm < P.cap 0 → IsEOpt (hiU P t z pm) p →
      grad P t z (join (hiU P t z pm) p) 0 = P.km 0 := by
    intro p h0 hc' ⟨hp, hmin⟩
    have hd := U_deriv_last hS hT1 z pm p _ hp hmin
    have h1 : ld (U P t z pm) (hiU P t z pm) ≤ P.km 0 := ld_hiF hU h0
    have h2 : P.km 0 ≤ rd (U P t z pm) (hiU P t z pm) := rd_hiF hU hcap hc'
    linarith [hd.1, hd.2]
  have flo : ∀ p, 0 < loU P t z pm → loU P t z pm < P.cap 0 → IsEOpt (loU P t z pm) p →
      grad P t z (join (loU P t z pm) p) 0 = -P.kp 0 := by
    intro p h0 hc' ⟨hp, hmin⟩
    have hd := U_deriv_last hS hT1 z pm p _ hp hmin
    have h1 : ld (U P t z pm) (loU P t z pm) ≤ -P.kp 0 := ld_loF hU hcap h0
    have h2 : -P.kp 0 ≤ rd (U P t z pm) (loU P t z pm) := rd_loF hU hc'
    linarith [hd.1, hd.2]
  have hA : ∀ p, 0 < hiU P t z pm → hiU P t z pm < P.cap 0 → IsEOpt (hiU P t z pm) p → Interior P p →
      ∃ c : Fin M → ℝ, (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (p j - pm j) (c j)) ∧
        cres P t z * (hiU P t z pm - xstar P t z 0) = P.km 0 + rho P t z ⬝ᵥ c := by
    intro p h0 hc' hopt hint
    refine ⟨fun j => -grad P t z (join (hiU P t z pm) p) j.succ,
      fun j => tradeSign_of_min hS hT1 z pm p _ hopt.1 hint hopt.2 j, ?_⟩
    rw [edge_identity hS, fhi p h0 hc' hopt]
  have hB : ∀ p, 0 < loU P t z pm → loU P t z pm < P.cap 0 → IsEOpt (loU P t z pm) p → Interior P p →
      ∃ c : Fin M → ℝ, (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (p j - pm j) (c j)) ∧
        cres P t z * (loU P t z pm - xstar P t z 0) = -P.kp 0 + rho P t z ⬝ᵥ c := by
    intro p h0 hc' hopt hint
    refine ⟨fun j => -grad P t z (join (loU P t z pm) p) j.succ,
      fun j => tradeSign_of_min hS hT1 z pm p _ hopt.1 hint hopt.2 j, ?_⟩
    rw [edge_identity hS, flo p h0 hc' hopt]
  have hlh : loU P t z pm ≤ hiU P t z pm := loF_le_hiF hU hk hm hcap
  refine ⟨hA, hB, fun ph pl hlo hhi hoh hol hih hil => ?_, fun hlo hhi hoh hol => ?_,
    fun ph pl hlo hhi hoh hol => ?_⟩
  · obtain ⟨ch, hch, ehi⟩ := hA ph (lt_of_lt_of_le hlo hlh) hhi hoh hih
    obtain ⟨cl, hcl, elo⟩ := hB pl hlo (lt_of_le_of_lt hlh hhi) hol hil
    have hw : cres P t z * (hiU P t z pm - loU P t z pm) = P.kp 0 + P.km 0 + rho P t z ⬝ᵥ (ch - cl) := by
      rw [dotProduct_sub]; linarith
    refine ⟨ch, cl, hch, hcl, hw, fun he => ?_, fun hopp => ?_⟩
    · rw [he, sub_self, dotProduct_zero, add_zero] at hw
      rw [eq_div_iff hc.ne']; linarith
    · have hsum : rho P t z ⬝ᵥ (ch - cl) = -∑ j, |rho P t z j| * (P.kp j.succ + P.km j.succ) := by
        rw [dotProduct, ← sum_neg_distrib]
        refine sum_congr rfl fun j _ => ?_
        simp only [Pi.sub_apply]
        obtain ⟨hpos, hneg⟩ := hopp j
        rcases lt_trichotomy (rho P t z j) 0 with hr | hr | hr
        · obtain ⟨h1, h2⟩ := hneg hr
          rw [(hch j).1 (by linarith), (hcl j).2.1 (by linarith), abs_of_neg hr]
          ring
        · rw [hr]; simp
        · obtain ⟨h1, h2⟩ := hpos hr
          rw [(hch j).2.1 (by linarith), (hcl j).1 (by linarith), abs_of_pos hr]
          ring
      rw [hsum] at hw
      rw [eq_div_iff hc.ne']; linarith
  · have h1 := fhi pm (lt_of_lt_of_le hlo hlh) hhi hoh
    have h2 := flo pm hlo (lt_of_le_of_lt hlh hhi) hol
    have h3 := grad_diff0 hS t z (hiU P t z pm) (loU P t z pm) pm
    have hd : 0 < P.gamma * P.Sigma t z 0 0 := mul_pos hS.2.2.2.1 (diag_pos hS t z 0)
    rw [eq_div_iff hd.ne']; linarith
  · have hd : 0 < P.gamma * P.Sigma t z 0 0 := mul_pos hS.2.2.2.1 (diag_pos hS t z 0)
    have h1 := fhi ph (lt_of_lt_of_le hlo hlh) hhi hoh
    have h2 := flo pl hlo (lt_of_le_of_lt hlh hhi) hol
    rw [div_le_iff₀ hd]
    rcases eq_or_lt_of_le hlh with heq | hlt
    · -- one fund holding, two ETF optimizers: `U` is differentiable there, so both slopes agree
      have d1 := U_deriv_last hS hT1 z pm ph _ hoh.1 hoh.2
      have d2 := U_deriv_last hS hT1 z pm pl (hiU P t z pm) hol.1 (heq ▸ hol.2)
      have h3 := ld_le_rd hU (hiU P t z pm)
      rw [heq] at h2
      rw [heq, sub_self, zero_mul]
      linarith [d1.1, d1.2, d2.1, d2.2]
    · have hc := cross_le hS hT1 z pm ph pl _ _ hoh.1 hol.1 hoh.2 hol.2
      have hγ := hS.2.2.2.1
      have hs : SEA P t z ⬝ᵥ (ph - pl) ≤ 0 := by
        by_contra hpos; push Not at hpos
        have : 0 < P.gamma * (hiU P t z pm - loU P t z pm) * (SEA P t z ⬝ᵥ (ph - pl)) :=
          mul_pos (mul_pos hγ (by linarith)) hpos
        linarith
      rw [grad0_join hS] at h1 h2
      have e : SEA P t z ⬝ᵥ (ph - fun j : Fin M => xstar P t z j.succ) -
          SEA P t z ⬝ᵥ (pl - fun j : Fin M => xstar P t z j.succ) = SEA P t z ⬝ᵥ (ph - pl) := by
        rw [← dotProduct_sub]; congr 1; abel
      nlinarith [mul_le_mul_of_nonneg_left hs hγ.le]

end Part1d

/-! ### Part 3 -/

section Part3

variable {P : M6 (M + 1) Z Ω} (hS : Setting P)
include hS

lemma reduced_setting : Setting (reduced P) := by
  have hs := s2res_pos hS
  obtain ⟨hT, -, -, hγ, hβ, hβ1, hk, hcap, hq, hq1, hg⟩ := hS
  refine ⟨hT, fun t z => ?_, fun t z v hv => ?_, hγ, hβ, hβ1, fun _ => hk 0, fun _ => hcap 0, hq, hq1,
    fun ω _ => hg ω 0⟩
  · funext i j; rfl
  · have hv0 : v 0 ≠ 0 := by
      intro h; apply hv; funext i; rw [Subsingleton.elim i 0, h]; rfl
    simp only [reduced, dotProduct, mulVec, Fin.sum_univ_one]
    have := hs t z
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith

omit hS in
lemma reduced_xstar_of (t : ℕ) (z : Z) (hs : 0 < s2res P t z) (hγ : 0 < P.gamma) :
    xstar (reduced P) t z 0 = xstar P t z 0 := by
  have hinv : ((reduced P).Sigma t z)⁻¹ = Matrix.of fun _ _ => (s2res P t z)⁻¹ := by
    apply inv_eq_left_inv
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.mul_apply]
    simp [reduced, hs.ne']
  change ((1 / P.gamma) • (((reduced P).Sigma t z)⁻¹ *ᵥ (reduced P).mu t z)) 0 = xstar P t z 0
  rw [hinv]
  simp only [Pi.smul_apply, mulVec, dotProduct, Fin.sum_univ_one, reduced, smul_eq_mul, Matrix.of_apply]
  field_simp

lemma reduced_xstar (t : ℕ) (z : Z) : xstar (reduced P) t z 0 = xstar P t z 0 :=
  reduced_xstar_of t z (s2res_pos hS t z) hS.2.2.2.1

omit hS in
lemma cost_zeroE (hE : ∀ j : Fin M, P.kp j.succ = 0 ∧ P.km j.succ = 0) (u : Fin M → ℝ) : costE P u = 0 := by
  simp [costE, (hE _).1, (hE _).2]

/-- The Schur remainder vanishes at the hedge. -/
lemma track_hedge (t : ℕ) (z : Z) (a : ℝ) (p : Fin M → ℝ) :
    cres P t z / 2 * (a - xstar P t z 0) ^ 2 ≤ track P t z (join a p) ∧
      track P t z (join a (hedge P t z a)) = cres P t z / 2 * (a - xstar P t z 0) ^ 2 := by
  have hx : xstar P t z = join (xstar P t z 0) (fun j : Fin M => xstar P t z j.succ) := join_eta _
  have hγ := hS.2.2.2.1
  have htr : ∀ q : Fin M → ℝ, track P t z (join a q) = cres P t z / 2 * (a - xstar P t z 0) ^ 2 +
      P.gamma / 2 * (((q - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z) ⬝ᵥ
        (SEE P t z *ᵥ ((q - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z))) := by
    intro q
    simp only [track]
    conv_lhs => rw [hx, join_sub, schur hS t z]
    rw [cres]; ring
  constructor
  · rw [htr]
    have : 0 ≤ ((p - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z) ⬝ᵥ
        (SEE P t z *ᵥ ((p - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z)) := by
      by_cases h : (p - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z = 0
      · rw [h]; simp
      · exact (SEE_quad_pos hS t z _ h).le
    nlinarith
  · rw [htr]
    have : (hedge P t z a - fun j : Fin M => xstar P t z j.succ) + (a - xstar P t z 0) • rho P t z = 0 := by
      funext j; simp [hedge]; ring
    rw [this]; simp

omit hS in
theorem frictionless : Frictionless := by
  intro M Z Ω _ P hS hE hbox
  have hSA : Setting (reduced P) := reduced_setting hS
  have hxs := reduced_xstar hS
  have hcap := capA hS
  have hcost : ∀ u : Fin (M + 1) → ℝ, cost P u = costA P (u 0) := fun u => by
    conv_lhs => rw [join_eta u]
    rw [cost_join, cost_zeroE hE, add_zero]
  have hcostA : ∀ v : ℝ, cost (reduced P) (cst v) = costA P v := fun v => by
    rw [cost1]; rfl
  have hGA : ∀ t z a, G (reduced P) t z (cst a) = G1 (reduced P) t z a := fun _ _ _ => rfl
  -- `G` through the reduced instance, given the next review's reduction
  have hG : ∀ t z (K' : Z → ℝ), (∀ z' x, V P (t + 1) z' x = V1 (reduced P) (t + 1) z' (x 0) + K' z') →
      ∀ a p, G P t z (join a p) = track P t z (join a p) - cres P t z / 2 * (a - xstar P t z 0) ^ 2 +
        G1 (reduced P) t z a + P.beta * ∑ ω, P.prob t z ω * K' (P.next ω) := by
    intro t z K' hK' a p
    rw [G1_split, G_eq]
    simp only [cont, phi1, hK']
    have hm : ∀ ω, mark (join a p) (P.gross ω) 0 = a * (reduced P).gross ω 0 := fun ω => rfl
    simp only [hm, mul_add, sum_add_distrib]
    have hc : curv (reduced P) t z = cres P t z := rfl
    have hx : xs (reduced P) t z = xstar P t z 0 := hxs t z
    have eβ : (reduced P).beta = P.beta := rfl
    have eq : (reduced P).prob = P.prob := rfl
    have en : (reduced P).next = P.next := rfl
    rw [hc, hx, eβ, eq, en]
    ring
  -- `V_t = V^A_t + K_t`
  have hV : ∀ k t, P.T - t = k → ∀ z, ∃ K, ∀ x, V P t z x = V1 (reduced P) t z (x 0) + K := by
    intro k
    induction k with
    | zero =>
      intro t ht z
      refine ⟨0, fun x => ?_⟩
      rw [V_ge P (by omega), V1_eq, V_ge (reduced P) (show (reduced P).T ≤ t by simp only [reduced]; omega)]
      ring
    | succ k ih =>
      intro t ht z
      have htT : t < P.T := by omega
      have htA : t < (reduced P).T := htT
      choose K' hK' using ih (t + 1) (by omega)
      have hGt := hG t z K' hK'
      set Kt := P.beta * ∑ ω, P.prob t z ω * K' (P.next ω)
      refine ⟨Kt, fun x => le_antisymm ?_ ?_⟩
      · set aA := proj (reduced P) t z (x 0)
        have hlo := lo_bounds hSA t z
        have hhi := hi_bounds hSA t z
        have hlh := lo_le_hi hSA t z
        have ha0 : 0 ≤ aA := hlo.1.trans (le_min (le_max_right _ _) hlh)
        have hac : aA ≤ P.cap 0 := (min_le_right _ _).trans hhi.2
        have hh := hbox t z htT aA ha0 hac
        have hmem : join aA (hedge P t z aA) ∈ box P := (mem_box_join P _ _).2 ⟨⟨ha0, hac⟩, hh⟩
        have h1 := V_le hS htT z (G_facts hS t z).2.2 x hmem
        have h2 := V1_val hSA z htA (x 0)
        rw [Fobj, hcost, hGt, (track_hedge hS t z aA (hedge P t z aA)).2] at h1
        simp only [Pi.sub_apply, join_zero] at h1
        rw [h2]
        have e : costA P (aA - x 0) = (reduced P).kp 0 * max (aA - x 0) 0 +
            (reduced P).km 0 * max (-(aA - x 0)) 0 := rfl
        linarith
      · obtain ⟨x', hx', -, hVx⟩ := V_attain hS htT z (G_facts hS t z).2.2 x
        rw [hVx, Fobj, hcost, join_eta x', hGt]
        simp only [Pi.sub_apply, join_zero]
        have hb := (mem_box_join P _ _).1 (join_eta x' ▸ hx')
        have h1 := (track_hedge hS t z (x' 0) (fun j => x' j.succ)).1
        have h2 := V_le hSA htA z (G_facts hSA t z).2.2 (cst (x 0))
          ((mem_box1 (reduced P) (x' 0)).2 hb.1)
        rw [Fobj, cst_sub, hcostA, hGA] at h2
        rw [V1_eq]
        linarith
  refine ⟨hSA, hxs, fun t z ht => ?_⟩
  obtain ⟨K, hK⟩ := hV _ t rfl z
  choose K' hK' using hV _ (t + 1) rfl
  have hGt := hG t z K' hK'
  set Kt := P.beta * ∑ ω, P.prob t z ω * K' (P.next ω)
  have hU : ∀ pm : Fin M → ℝ, ∀ a, 0 ≤ a → a ≤ P.cap 0 → U P t z pm a = G1 (reduced P) t z a + Kt := by
    intro pm a ha0 hac
    apply le_antisymm
    · have hh := hbox t z ht a ha0 hac
      have h1 := U_le hS t z pm a hh
      rw [Fe, hGt, (track_hedge hS t z a 0).2, cost_zeroE hE] at h1
      linarith
    · obtain ⟨p, hp, -, hUp⟩ := U_attain hS t z pm a
      rw [hUp, Fe, hGt, cost_zeroE hE]
      have := (track_hedge hS t z a p).1
      linarith
  refine ⟨⟨K, hK⟩, ⟨Kt, hU⟩, fun pm => ?_⟩
  -- equal one-sided derivatives on the box give equal edges
  have hrd : ∀ x, 0 ≤ x → x < P.cap 0 → rd (U P t z pm) x = rd (G1 (reduced P) t z) x := by
    intro x hx0 hxc
    rw [rd_congr (g := fun y => G1 (reduced P) t z y + Kt) (δ := P.cap 0 - x) (by linarith)
      fun y hxy hy => hU pm y (by linarith) (by linarith)]
    exact derivWithin_add_const _
  have hld : ∀ x, 0 < x → x ≤ P.cap 0 → ld (U P t z pm) x = ld (G1 (reduced P) t z) x := by
    intro x hx0 hxc
    rw [ld_congr (g := fun y => G1 (reduced P) t z y + Kt) (δ := x) hx0
      fun y hy hyx => hU pm y (by linarith) (by linarith)]
    exact derivWithin_add_const _
  have hs1 : {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (U P t z pm) x} =
      {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 (reduced P) t z) x} := by
    ext x; simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, hrd x h0 h1 ▸ h2⟩
    · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, (hrd x h0 h1).symm ▸ h2⟩
  have hs2 : {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (U P t z pm) x ≤ P.km 0} =
      {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 (reduced P) t z) x ≤ P.km 0} := by
    ext x; simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, hld x h0 h1 ▸ h2⟩
    · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, (hld x h0 h1).symm ▸ h2⟩
  constructor
  · show loF (U P t z pm) (P.kp 0) (P.cap 0) = lo (reduced P) t z
    unfold loF lo
    rw [hs1]; rfl
  · show hiF (U P t z pm) (P.km 0) (P.cap 0) = hi (reduced P) t z
    unfold hiF hi
    rw [hs2]; rfl

end Part3

/-- Claim 107, parts 1-3. -/
theorem proof : Standalone.M7DynamicBundlingBand.statement :=
  ⟨effectiveBand, residualCeiling, outerBracket, lastReview, outerParallelotope, frictionless⟩

end

end Novel.M7DynamicBundlingBandProof

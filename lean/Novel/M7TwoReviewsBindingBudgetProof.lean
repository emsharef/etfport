import Novel.M7TwoStageExactnessLossProof
import Standalone.M7TwoReviewsBindingBudget

/-!
# Claim 044: proof

Sufficiency (part 2) is a Lagrangian bound. With `L = J + η_0 h⁺_0 + β Σ q η_1 h⁺_1`, concavity of the
quadratics and the slope inequalities of the costs give
`L(Y) ≤ L(X) + Σ_i v_{0,i} (Y_0 - X_0)_i + β Σ_z q Σ_i v_{1,i}(z) (Y_1 - X_1)_i(z)`, with `v` the lines'
values. The box signs make the sum nonpositive, and complementary slackness gives `L(X) = J(X)` and
`J(Y) ≤ L(Y)` on the feasible set. Part 4(a) is the same bound for a single review. Necessity lifts
the costs, as in claim 104's part 0, now at both reviews, and applies AX-13. Part 3(c)'s signs use
the supergradient `(s(z), η_1(z))` of `V_1` that tomorrow's lines give, a small move of the traded
coordinate (the myopic root's first-order condition), and the concavity of the root objective
along the line. The other parts are readings of the lines.
-/

namespace Novel.M7TwoReviewsBindingBudgetProof

open Standalone.M7TwoReviewsBindingBudget Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-! ### Tools -/

lemma pc_ge {kp km u t : ℝ} (h : Slope kp km u t) (v : ℝ) : pc kp km u + t * (v - u) ≤ pc kp km v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : pc kp km u = t * u := by
    unfold pc
    rcases lt_trichotomy u 0 with hu | hu | hu
    · rw [max_eq_right hu.le, max_eq_left (by linarith), h4 hu]; ring
    · subst hu; simp
    · rw [max_eq_left hu.le, max_eq_right (by linarith), h3 hu]; ring
  have : t * v ≤ pc kp km v := by
    unfold pc
    rcases le_total v 0 with hv | hv
    · rw [max_eq_right hv, max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_left hv, max_eq_right (by linarith)]; nlinarith
  linarith

lemma pc_nonneg {kp km : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (u : ℝ) : 0 ≤ pc kp km u :=
  add_nonneg (mul_nonneg hkp (le_max_right _ _)) (mul_nonneg hkm (le_max_right _ _))

lemma pc_convex {kp km : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u v : ℝ) : pc kp km (a * u + b * v) ≤ a * pc kp km u + b * pc kp km v := by
  have m1 : max (a * u + b * v) 0 ≤ a * max u 0 + b * max v 0 :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left (le_max_left u 0) ha,
      mul_le_mul_of_nonneg_left (le_max_left v 0) hb])
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  have m2 : max (-(a * u + b * v)) 0 ≤ a * max (-u) 0 + b * max (-v) 0 :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-u) 0) ha,
      mul_le_mul_of_nonneg_left (le_max_left (-v) 0) hb])
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  unfold pc
  nlinarith [mul_le_mul_of_nonneg_left m1 hkp, mul_le_mul_of_nonneg_left m2 hkm]

lemma cost_ge {P : Two ι Z} {u t : ι → ℝ} (h : ∀ i, Slope (P.kp i) (P.km i) (u i) (t i))
    (v : ι → ℝ) : cost P u + ∑ i, t i * (v i - u i) ≤ cost P v := by
  unfold cost; rw [← sum_add_distrib]; exact sum_le_sum fun i _ => pc_ge (h i) (v i)

lemma cost_nonneg {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) (u : ι → ℝ) : 0 ≤ cost P u :=
  sum_nonneg fun i _ => pc_nonneg (hr i).1 (hr i).2 _

lemma cost_convex {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (u v : ι → ℝ) : cost P (a • u + b • v) ≤ a * cost P u + b * cost P v := by
  unfold cost
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun i _ => pc_convex (hr i).1 (hr i).2 ha hb (u i) (v i)

lemma quad_expand {S : ι → ι → ℝ} (hS : ∀ i j, S i j = S j i) (x d : ι → ℝ) (ε : ℝ) :
    quad S (x + ε • d) = quad S x + 2 * ε * ∑ i, d i * ∑ j, S i j * x j + ε ^ 2 * quad S d := by
  unfold quad
  have swap : ∑ i, ∑ j, x i * S i j * d j = ∑ i, ∑ j, d i * S i j * x j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hS]; ring
  have e1 : ∑ i, ∑ j, (x + ε • d) i * S i j * (x + ε • d) j = ∑ i, ∑ j, x i * S i j * x j +
      ε * ∑ i, ∑ j, x i * S i j * d j + ε * ∑ i, ∑ j, d i * S i j * x j +
        ε ^ 2 * ∑ i, ∑ j, d i * S i j * d j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, d i * ∑ j, S i j * x j = ∑ i, ∑ j, d i * S i j * x j := by
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [e1, swap, e2]; ring

lemma Qv_expand {mu : ι → ℝ} {S : ι → ι → ℝ} (hS : ∀ i j, S i j = S j i) (γ : ℝ) (x d : ι → ℝ)
    (ε : ℝ) : Qv mu S γ (x + ε • d) =
      Qv mu S γ x + ε * ∑ i, marg mu S γ x i * d i - ε ^ 2 * (γ / 2 * quad S d) := by
  unfold Qv
  rw [quad_expand hS]
  have e1 : ∑ i, mu i * (x + ε • d) i = ∑ i, mu i * x i + ε * ∑ i, mu i * d i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, marg mu S γ x i * d i = ∑ i, mu i * d i - γ * ∑ i, d i * ∑ j, S i j * x j := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by simp only [marg]; ring
  rw [e1, e2]; ring

lemma Qv_le {mu : ι → ℝ} {S : ι → ι → ℝ} (hS : PSD S) {γ : ℝ} (hγ : 0 ≤ γ) (x y : ι → ℝ) :
    Qv mu S γ y ≤ Qv mu S γ x + ∑ i, marg mu S γ x i * (y i - x i) := by
  have e := Qv_expand (mu := mu) hS.1 γ x (y - x) 1
  rw [one_smul, add_sub_cancel] at e
  rw [e]
  simp only [Pi.sub_apply, one_mul, one_pow]
  nlinarith [hS.2 (y - x)]

lemma bs_le {xbar x R y : ℝ} (h : BoxSign xbar x R) (hx0 : 0 ≤ x) (hx1 : x ≤ xbar) (hy0 : 0 ≤ y)
    (hy1 : y ≤ xbar) : R * (y - x) ≤ 0 := by
  rcases lt_trichotomy R 0 with hR | hR | hR
  · have hx : x = 0 := by
      by_contra hne
      have := h.2 (lt_of_le_of_ne hx0 (Ne.symm hne)); linarith
    rw [hx]; nlinarith
  · rw [hR, zero_mul]
  · have hx : x = xbar := by
      by_contra hne
      have := h.1 (lt_of_le_of_ne hx1 hne); linarith
    rw [hx]; nlinarith

lemma sum_line (m t y x : ι → ℝ) (η : ℝ) :
    ∑ i, (m i - η - (1 + η) * t i) * (y i - x i) =
      ∑ i, m i * (y i - x i) - η * ∑ i, (y i - x i) - (1 + η) * ∑ i, t i * (y i - x i) := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

lemma sum_diff (y x c : ι → ℝ) : ∑ i, (y i - c i) - ∑ i, (x i - c i) = ∑ i, (y i - x i) := by
  rw [← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring

/-- The one-review Lagrangian bound. -/
lemma lag_bound {P : Two ι Z} {mu : ι → ℝ} {S : ι → ι → ℝ} {c t x : ι → ℝ} {η : ℝ} (hS : PSD S)
    (hγ : 0 ≤ P.gamma) (hη : 0 ≤ η) (hsl : ∀ i, Slope (P.kp i) (P.km i) (x i - c i) (t i))
    (y : ι → ℝ) : lagOne P mu S c η y ≤ lagOne P mu S c η x +
      ∑ i, (marg mu S P.gamma x i - η - (1 + η) * t i) * (y i - x i) := by
  have hQ := Qv_le (mu := mu) hS hγ x y
  have hC := cost_ge (P := P) (u := x - c) hsl (y - c)
  simp only [Pi.sub_apply] at hC
  have e : ∑ i, t i * (y i - c i - (x i - c i)) = ∑ i, t i * (y i - x i) :=
    sum_congr rfl fun i _ => by ring
  rw [e] at hC
  unfold lagOne
  rw [sum_line]
  have hd := sum_diff y x c
  nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 + η)]

lemma lag_max {P : Two ι Z} {mu : ι → ℝ} {S : ι → ι → ℝ} {c t x : ι → ℝ} {η : ℝ} (hS : PSD S)
    (hγ : 0 ≤ P.gamma) (hη : 0 ≤ η) (hx : Box P x)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (x i - c i) (t i) ∧
      BoxSign (P.xbar i) (x i) (marg mu S P.gamma x i - η - (1 + η) * t i)) :
    IsMaxOn (lagOne P mu S c η) {y | Box P y} x := by
  intro y hy
  have hb := lag_bound (mu := mu) hS hγ hη (fun i => (hl i).1) y
  have : ∑ i, (marg mu S P.gamma x i - η - (1 + η) * t i) * (y i - x i) ≤ 0 :=
    sum_nonpos fun i _ => bs_le (hl i).2 (hx i).1 (hx i).2 (hy i).1 (hy i).2
  show lagOne P mu S c η y ≤ lagOne P mu S c η x
  linarith

/-! ### Part 4(a) -/

lemma etaHat_nonneg {P : Two ι Z} (hP : Hyp P) {η0 : ℝ} {η1 : Z → ℝ} (h0 : 0 ≤ η0)
    (h1 : ∀ z, 0 ≤ η1 z) : 0 ≤ etaHat P η0 η1 :=
  add_nonneg h0 (mul_nonneg hP.2.1.le (sum_nonneg fun z _ => mul_nonneg (hP.2.2.2.2.2.2.1 z).le (h1 z)))

theorem twoScalar : TwoScalar := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR hX0 hX1
  refine ⟨lag_max (t := t0) hP.2.2.2.2.1 hP.1.le (etaHat_nonneg hP hR.1 fun z => (hT z).1) hX0 fun i => ?_,
    fun z => lag_max (hP.2.2.2.2.2.1 z) hP.1.le (hT z).1 (hX1 z) fun i => (hT z).2.2 i⟩
  obtain ⟨h1, h2⟩ := hR.2.2 i
  refine ⟨h1, ?_⟩
  have e : marg (P.mu0 + Sinc P η1 t1) P.S0 P.gamma X.1 i = g0 P X.1 i + Sinc P η1 t1 i := by
    simp only [marg, g0, Pi.add_apply]; ring
  rw [e]; exact h2

/-! ### Part 2: sufficiency -/

lemma h0_diff (P : Two ι Z) (x y : ι → ℝ) :
    h0 P x - h0 P y = ∑ i, (y i - x i) + (cost P (y - P.xm) - cost P (x - P.xm)) := by
  unfold h0
  have := sum_diff y x P.xm
  linarith

/-- One state's share of the Lagrangian bound. -/
lemma perz {P : Two ι Z} (hP : Hyp P) {X Y : (ι → ℝ) × (Z → ι → ℝ)} {η1 : Z → ℝ} {t1 : Z → ι → ℝ}
    (hT : Tomorrow P X η1 t1) (z : Z) :
    (Q1 P z (Y.2 z) - cost P (Y.2 z - carry P z Y.1) + η1 z * h1 P Y.1 Y.2 z) -
      (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1) + η1 z * h1 P X.1 X.2 z) ≤
    ∑ i, (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i) * (Y.2 z i - X.2 z i) +
      ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) - η1 z * (h0 P X.1 - h0 P Y.1) := by
  have hη := (hT z).1
  have C : Q1 P z (Y.2 z) ≤ Q1 P z (X.2 z) + ∑ i, g1 P z (X.2 z) i * (Y.2 z i - X.2 z i) :=
    Qv_le (hP.2.2.2.2.2.1 z) hP.1.le (X.2 z) (Y.2 z)
  have D := cost_ge (P := P) (u := X.2 z - carry P z X.1) (fun i => ((hT z).2.2 i).1)
    (Y.2 z - carry P z Y.1)
  have eD : ∑ i, t1 z i * ((Y.2 z - carry P z Y.1) i - (X.2 z - carry P z X.1) i) =
      ∑ i, t1 z i * (Y.2 z i - X.2 z i) - ∑ i, P.g z i * t1 z i * (Y.1 i - X.1 i) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by simp only [Pi.sub_apply, carry]; ring
  rw [eD] at D
  have F : ∑ i, (Y.2 z i - carry P z Y.1 i) - ∑ i, (X.2 z i - carry P z X.1 i) =
      ∑ i, (Y.2 z i - X.2 z i) - ∑ i, P.g z i * (Y.1 i - X.1 i) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by simp only [carry]; ring
  have eS : ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) =
      η1 z * ∑ i, P.g z i * (Y.1 i - X.1 i) + (1 + η1 z) * ∑ i, P.g z i * t1 z i * (Y.1 i - X.1 i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by simp only [sval]; ring
  have eL := sum_line (fun i => g1 P z (X.2 z) i) (t1 z) (Y.2 z) (X.2 z) (η1 z)
  unfold h1
  nlinarith [mul_le_mul_of_nonneg_left D (by linarith : (0 : ℝ) ≤ 1 + η1 z)]

theorem sufficient : Sufficient := by
  intro ι Z _ _ P hP X hX ⟨η0, η1, t0, t1, hT, hR⟩
  refine ⟨hX, fun Y hY => ?_⟩
  show J P Y ≤ J P X
  have hβ := hP.2.1
  have hq := hP.2.2.2.2.2.2.1
  -- today
  have A : Q0 P Y.1 ≤ Q0 P X.1 + ∑ i, g0 P X.1 i * (Y.1 i - X.1 i) :=
    Qv_le hP.2.2.2.2.1 hP.1.le X.1 Y.1
  have B := cost_ge (P := P) (u := X.1 - P.xm) (fun i => (hR.2.2 i).1) (Y.1 - P.xm)
  have eB : ∑ i, t0 i * ((Y.1 - P.xm) i - (X.1 - P.xm) i) = ∑ i, t0 i * (Y.1 i - X.1 i) :=
    sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [eB] at B
  have hid := h0_diff P X.1 Y.1
  -- the root lines
  have hroot : ∑ i, (g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i) *
      (Y.1 i - X.1 i) ≤ 0 :=
    sum_nonpos fun i _ => bs_le (hR.2.2 i).2 (hX.1 i).1 (hX.1 i).2 (hY.1 i).1 (hY.1 i).2
  rw [sum_line (fun i => g0 P X.1 i + Sinc P η1 t1 i)] at hroot
  have eG : ∑ i, (g0 P X.1 i + Sinc P η1 t1 i) * (Y.1 i - X.1 i) = ∑ i, g0 P X.1 i * (Y.1 i - X.1 i) +
      P.beta * ∑ z, P.q z * ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) := by
    simp only [add_mul, sum_add_distrib, Sinc, sum_mul, mul_sum]
    rw [sum_comm (γ := Z)]
    congr 1
    exact sum_congr rfl fun z _ => sum_congr rfl fun i _ => by ring
  rw [eG] at hroot
  simp only [etaHat] at hroot
  -- tomorrow
  have htom : ∑ z, P.q z * ∑ i, (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i) *
      (Y.2 z i - X.2 z i) ≤ 0 :=
    sum_nonpos fun z _ => mul_nonpos_of_nonneg_of_nonpos (hq z).le (sum_nonpos fun i _ =>
      bs_le ((hT z).2.2 i).2 ((hX.2.1 z) i).1 ((hX.2.1 z) i).2 ((hY.2.1 z) i).1 ((hY.2.1 z) i).2)
  have agg : ∑ z, P.q z * (Q1 P z (Y.2 z) - cost P (Y.2 z - carry P z Y.1)) +
      ∑ z, P.q z * η1 z * h1 P Y.1 Y.2 z -
      (∑ z, P.q z * (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1)) +
        ∑ z, P.q z * η1 z * h1 P X.1 X.2 z) ≤
      ∑ z, P.q z * ∑ i, (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i) * (Y.2 z i - X.2 z i) +
      ∑ z, P.q z * ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) -
        (∑ z, P.q z * η1 z) * (h0 P X.1 - h0 P Y.1) := by
    have hs := sum_le_sum fun z (_ : z ∈ univ) =>
      mul_le_mul_of_nonneg_left (perz hP (Y := Y) hT z) (hq z).le
    have e1 : ∑ z, P.q z * (Q1 P z (Y.2 z) - cost P (Y.2 z - carry P z Y.1)) +
        ∑ z, P.q z * η1 z * h1 P Y.1 Y.2 z -
        (∑ z, P.q z * (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1)) +
          ∑ z, P.q z * η1 z * h1 P X.1 X.2 z) =
        ∑ z, P.q z * ((Q1 P z (Y.2 z) - cost P (Y.2 z - carry P z Y.1) + η1 z * h1 P Y.1 Y.2 z) -
          (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1) + η1 z * h1 P X.1 X.2 z)) := by
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun z _ => by ring
    have e2 : ∑ z, P.q z * ∑ i, (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i) * (Y.2 z i - X.2 z i) +
        ∑ z, P.q z * ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) -
          (∑ z, P.q z * η1 z) * (h0 P X.1 - h0 P Y.1) =
        ∑ z, P.q z * (∑ i, (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i) * (Y.2 z i - X.2 z i) +
          ∑ i, P.g z i * sval η1 t1 z i * (Y.1 i - X.1 i) - η1 z * (h0 P X.1 - h0 P Y.1)) := by
      rw [sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun z _ => by ring
    rw [e1, e2]; exact hs
  -- complementary slackness
  have hX0 : ∑ z, P.q z * η1 z * h1 P X.1 X.2 z = 0 :=
    sum_eq_zero fun z _ => by rw [mul_assoc, (hT z).2.1, mul_zero]
  have hY0 : 0 ≤ ∑ z, P.q z * η1 z * h1 P Y.1 Y.2 z :=
    sum_nonneg fun z _ => mul_nonneg (mul_nonneg (hq z).le (hT z).1) (hY.2.2.2 z)
  have hE : 0 ≤ ∑ z, P.q z * η1 z := sum_nonneg fun z _ => mul_nonneg (hq z).le (hT z).1
  have hη0Y : 0 ≤ η0 * h0 P Y.1 := mul_nonneg hR.1 hY.2.2.1
  have i1 := congrArg (fun r => η0 * r) hid
  have i2 := congrArg (fun r => P.beta * (∑ z, P.q z * η1 z) * r) hid
  have hJ : ∀ W : (ι → ℝ) × (Z → ι → ℝ), J P W = Q0 P W.1 - cost P (W.1 - P.xm) +
      P.beta * ∑ z, P.q z * (Q1 P z (W.2 z) - cost P (W.2 z - carry P z W.1)) := fun W => rfl
  rw [hJ, hJ]
  nlinarith [mul_le_mul_of_nonneg_left agg hβ.le, mul_nonneg hβ.le hY0,
    mul_nonpos_of_nonneg_of_nonpos hβ.le htom, hR.2.1,
    mul_le_mul_of_nonneg_left B (by linarith [mul_nonneg hβ.le hE, hR.1] :
      (0 : ℝ) ≤ 1 + (η0 + P.beta * ∑ z, P.q z * η1 z))]

/-! ### Part 2: readings -/

theorem readings : Readings := by
  intro ι Z _ _ P X η1 t1 hT z i
  obtain ⟨hη, -, hl⟩ := hT z
  obtain ⟨⟨t1a, t1b, tp, tm⟩, b1, b2⟩ := hl i
  have h1η : 0 ≤ 1 + η1 z := by linarith
  refine ⟨fun h0 h1 => ?_, fun h => ?_, fun h => ?_, ⟨?_, ?_⟩, fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · have := b1 h1; have := b2 h0; simp only [sval]; linarith
  · simp only [sval, tp (by linarith)]
  · simp only [sval, tm (by linarith)]; ring
  · simp only [sval]; nlinarith [mul_le_mul_of_nonneg_left t1a h1η]
  · simp only [sval]; nlinarith [mul_le_mul_of_nonneg_left t1b h1η]
  · have := b1 (by rw [h0]; exact h1); simp only [sval]; linarith
  · have := b2 (by rw [h0]; exact h1); simp only [sval]; linarith

/-! ### Part 3(a)-(b) -/

lemma Sinc_bounds {P : Two ι Z} (hP : Hyp P) {X : (ι → ℝ) × (Z → ι → ℝ)} {η1 : Z → ℝ}
    {t1 : Z → ι → ℝ} (hT : Tomorrow P X η1 t1) (i : ι) :
    P.beta * ∑ z, P.q z * P.g z i * (η1 z - (1 + η1 z) * P.km i) ≤ Sinc P η1 t1 i ∧
      Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * (η1 z + (1 + η1 z) * P.kp i) := by
  have hw : ∀ z, 0 ≤ P.q z * P.g z i :=
    fun z => mul_nonneg (hP.2.2.2.2.2.2.1 z).le (hP.2.2.2.2.2.2.2.1 z i).le
  have hr := fun z => (readings ι Z P X η1 t1 hT z i).2.2.2.1
  exact ⟨mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hr z).1 (hw z))
      hP.2.1.le,
    mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hr z).2 (hw z))
      hP.2.1.le⟩

theorem slackTomorrow : SlackTomorrow := by
  intro ι Z _ _ P hP X η0 η1 t1 hT hslack
  have hz : ∀ z, η1 z = 0 := fun z => by
    rcases mul_eq_zero.mp (hT z).2.1 with h | h
    · exact h
    · linarith [hslack z]
  have hs : ∀ z i, sval η1 t1 z i = t1 z i := fun z i => by simp [sval, hz]
  have hw : ∀ z i, 0 ≤ P.q z * P.g z i :=
    fun z i => mul_nonneg (hP.2.2.2.2.2.2.1 z).le (hP.2.2.2.2.2.2.2.1 z i).le
  refine ⟨hz, by simp [etaHat, hz], fun z i => ⟨hs z i, ((hT z).2.2 i).1.1, ((hT z).2.2 i).1.2.1⟩,
    fun i => ⟨?_, ?_⟩⟩
  · have e : -(P.beta * ∑ z, P.q z * P.g z i * P.km i) = P.beta * ∑ z, P.q z * P.g z i * (-P.km i) := by
      simp only [mul_neg, sum_neg_distrib]
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
      (by rw [hs]; exact ((hT z).2.2 i).1.1) (hw z i)) hP.2.1.le
  · exact mul_le_mul_of_nonneg_left (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
      (by rw [hs]; exact ((hT z).2.2 i).1.2.1) (hw z i)) hP.2.1.le

theorem bounds : Bounds := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR i
  dsimp only
  obtain ⟨lo, hi⟩ := Sinc_bounds hP hT i
  obtain ⟨⟨ta, tb, tp, tm⟩, b1, b2⟩ := hR.2.2 i
  have hxm := (hP.2.2.2.2.2.2.2.2 i)
  refine ⟨lo, hi, fun h => ?_, fun h => ?_⟩
  · have e := b2 (by linarith)
    rw [tp (by linarith)] at e
    linarith
  · have e := b1 (by linarith)
    rw [tm (by linarith)] at e
    linarith

/-! ### Part 4(b) and 4(d) -/

lemma marg_update [DecidableEq ι] (mu : ι → ℝ) (S : ι → ι → ℝ) (γ : ℝ) (x : ι → ℝ) (i : ι) (s : ℝ) :
    marg mu S γ (Function.update x i s) i = marg mu S γ x i - γ * S i i * (s - x i) := by
  have h : ∀ j, S i j * Function.update x i s j =
      S i j * x j + if j = i then S i j * (s - x j) else 0 := fun j => by
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, ite_true]; ring
    · simp only [Function.update_of_ne hj, hj, ite_false, add_zero]
  simp only [marg, h, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  ring

theorem band : Band := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR i
  dsimp only
  obtain ⟨⟨ta, tb, tp, tm⟩, b1, b2⟩ := hR.2.2 i
  have he := etaHat_nonneg hP hR.1 fun z => (hT z).1
  have h1e : 0 ≤ 1 + etaHat P η0 η1 := by linarith
  refine ⟨fun h0 h1 => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, by ring, fun s => marg_update _ _ _ _ _ _⟩
  · have e1 := b1 h1; have e2 := b2 h0
    rw [tp (by linarith)] at e1 e2; linarith
  · have e1 := b1 h1; have e2 := b2 h0
    rw [tm (by linarith)] at e1 e2; linarith
  · have e1 := b1 h1; have e2 := b2 h0
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ta h1e]
    · nlinarith [mul_le_mul_of_nonneg_left tb h1e]

theorem costless : Costless := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR i hkp hkm
  have ht1 : ∀ z, t1 z i = 0 := fun z => by
    obtain ⟨⟨a, b, -, -⟩, -⟩ := (hT z).2.2 i
    rw [hkp] at b; rw [hkm] at a; linarith
  obtain ⟨⟨ta, tb, -, -⟩, b1, b2⟩ := hR.2.2 i
  have ht0 : t0 i = 0 := by rw [hkp] at tb; rw [hkm] at ta; linarith
  have hS : Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * η1 z := by
    simp only [Sinc, sval, ht1, mul_zero, add_zero]
  refine ⟨hS, fun h0 h1 => ?_⟩
  have e1 := b1 h1; have e2 := b2 h0
  rw [ht0, hS] at e1 e2
  linarith

/-! ### Part 3(c): the myopic root's first-order condition -/

lemma foc_zero {a c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (h : ∀ ε, |ε| < δ → ε * a ≤ c * ε ^ 2) :
    a = 0 := by
  have hab : ∀ ε, 0 < ε → ε < δ → |a| ≤ c * ε := fun ε h0 h1 => by
    have e1 := h ε (by rw [abs_of_pos h0]; exact h1)
    have e2 := h (-ε) (by rw [abs_neg, abs_of_pos h0]; exact h1)
    have f1 : a ≤ c * ε := le_of_mul_le_mul_left (by nlinarith) h0
    have f2 : -a ≤ c * ε := le_of_mul_le_mul_left (by nlinarith) h0
    exact abs_le.mpr ⟨by linarith, f1⟩
  by_contra ha
  have hpos : 0 < |a| := abs_pos.mpr ha
  have hm : 0 < min (δ / 2) (|a| / (2 * (c + 1))) := lt_min (by linarith) (by positivity)
  have h1 := hab _ hm (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h2 : c * min (δ / 2) (|a| / (2 * (c + 1))) ≤ c * (|a| / (2 * (c + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hc
  have h3 : c * (|a| / (2 * (c + 1))) < |a| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- A small move of a traded coordinate: it stays feasible, and the cost, the cash and the score
move by the rate `ρ` (`κ⁺` after a purchase, `-κ⁻` after a sale). -/
lemma bump {P : Two ι Z} [DecidableEq ι] (hP : Hyp P) {x : ι → ℝ} (hx : x ∈ Feas0 P) {i : ι}
    (hh : 0 < h0 P x) (h0i : 0 < x i) (hci : x i < P.xbar i) {ρ : ℝ}
    (hρ : (P.xm i < x i ∧ ρ = P.kp i) ∨ (x i < P.xm i ∧ ρ = -P.km i)) :
    ∃ δ > 0, ∀ ε, |ε| < δ → x + ε • Pi.single i 1 ∈ Feas0 P ∧
      cost P (x + ε • Pi.single i 1 - P.xm) = cost P (x - P.xm) + ρ * ε ∧
      h0 P (x + ε • Pi.single i 1) = h0 P x - (1 + ρ) * ε ∧
      Q0 P (x + ε • Pi.single i 1) = Q0 P x + ε * g0 P x i - ε ^ 2 * (P.gamma / 2 * P.S0 i i) := by
  have hxne : x i ≠ P.xm i := by
    rcases hρ with ⟨h, -⟩ | ⟨h, -⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hne : 0 < |x i - P.xm i| := abs_pos.mpr (sub_ne_zero.mpr hxne)
  refine ⟨min (min (|x i - P.xm i|) (x i)) (min (P.xbar i - x i) (h0 P x / (1 + |ρ|))),
    lt_min (lt_min hne h0i) (lt_min (by linarith) (by positivity)), fun ε hε => ?_⟩
  have hε1 : |ε| < |x i - P.xm i| := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : |ε| < x i := lt_of_lt_of_le hε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : |ε| < P.xbar i - x i := lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε4 : |ε| < h0 P x / (1 + |ρ|) := lt_of_lt_of_le hε (le_trans (min_le_right _ _) (min_le_right _ _))
  have hy : ∀ j, (x + ε • (Pi.single i 1 : ι → ℝ)) j = if j = i then x i + ε else x j := fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hpc : pc (P.kp i) (P.km i) (x i + ε - P.xm i) = pc (P.kp i) (P.km i) (x i - P.xm i) + ρ * ε := by
    have ha := abs_lt.mp hε1
    rcases hρ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [abs_of_pos (by linarith)] at ha
      simp only [pc]
      rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_right (by linarith)]; ring
    · rw [abs_of_neg (by linarith)] at ha
      simp only [pc]
      rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]; ring
  have hcost : cost P (x + ε • Pi.single i 1 - P.xm) = cost P (x - P.xm) + ρ * ε := by
    unfold cost
    rw [← sub_eq_iff_eq_add', ← sum_sub_distrib, sum_eq_single i]
    · simp only [Pi.sub_apply, hy, ite_true, hpc]; ring
    · intro j _ hj; simp [hy, hj]
    · simp
  have hsum : ∑ j, ((x + ε • (Pi.single i 1 : ι → ℝ)) j - P.xm j) = ∑ j, (x j - P.xm j) + ε := by
    rw [← sub_eq_iff_eq_add', ← sum_sub_distrib, sum_eq_single i]
    · simp [hy]
    · intro j _ hj; simp [hy, hj]
    · simp
  have hh0 : h0 P (x + ε • Pi.single i 1) = h0 P x - (1 + ρ) * ε := by
    unfold h0; rw [hsum, hcost]; ring
  refine ⟨⟨fun j => ?_, ?_⟩, hcost, hh0, ?_⟩
  · rw [hy]
    split_ifs with hj
    · subst hj; have := abs_lt.mp hε2; have := abs_lt.mp hε3; constructor <;> linarith
    · exact hx.1 j
  · rw [hh0]
    have h4 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + |ρ|)).mp hε4
    have : (1 + ρ) * ε ≤ (1 + |ρ|) * |ε| := by
      calc (1 + ρ) * ε ≤ |(1 + ρ) * ε| := le_abs_self _
        _ = |1 + ρ| * |ε| := abs_mul _ _
        _ ≤ (1 + |ρ|) * |ε| := mul_le_mul_of_nonneg_right
            (by have := abs_add_le (1 : ℝ) ρ; rwa [abs_one] at this) (abs_nonneg _)
    nlinarith
  · have e := Qv_expand (mu := P.mu0) hP.2.2.2.2.1.1 P.gamma x (Pi.single i 1) ε
    have hm : ∑ j, marg P.mu0 P.S0 P.gamma x j * (Pi.single i 1 : ι → ℝ) j = g0 P x i := by
      simp [Pi.single_apply, g0]
    have hq : quad P.S0 (Pi.single i 1) = P.S0 i i := by simp [quad, Pi.single_apply]
    change Q0 P (x + ε • Pi.single i 1) = Q0 P x + ε * _ - _ at e
    rw [hm, hq] at e
    exact e

/-- The myopic root's first-order condition in a coordinate traded strictly inside its box, with
today's budget slack: `g_{0,i} = ρ`. -/
lemma foc_gen {P : Two ι Z} (hP : Hyp P) {x : ι → ℝ} (hx : x ∈ Feas0 P)
    (hmax : IsMaxOn (fun x => Q0 P x - cost P (x - P.xm)) (Feas0 P) x) {i : ι} (hh : 0 < h0 P x)
    (h0i : 0 < x i) (hci : x i < P.xbar i) {ρ : ℝ}
    (hρ : (P.xm i < x i ∧ ρ = P.kp i) ∨ (x i < P.xm i ∧ ρ = -P.km i)) : g0 P x i = ρ := by
  classical
  obtain ⟨δ, hδ, hb⟩ := bump hP hx hh h0i hci hρ
  refine sub_eq_zero.mp (foc_zero (c := P.gamma / 2 * P.S0 i i)
    (mul_nonneg (by linarith [hP.1]) ?_) hδ fun ε hε => ?_)
  · have := hP.2.2.2.2.1.2 (Pi.single i 1)
    simpa [quad, Pi.single_apply] using this
  obtain ⟨hf, hc, -, hq⟩ := hb ε hε
  have hle := hmax hf
  simp only [Set.mem_ofPred_eq] at hle
  rw [hc, hq] at hle
  nlinarith

lemma foc {P : Two ι Z} (hP : Hyp P) {x : ι → ℝ} (hx : x ∈ Feas0 P)
    (hmax : IsMaxOn (fun x => Q0 P x - cost P (x - P.xm)) (Feas0 P) x) {i : ι} (hh : 0 < h0 P x)
    (hb : P.xm i < x i) (hc : x i < P.xbar i) : g0 P x i = P.kp i :=
  foc_gen hP hx hmax hh (by linarith [(hP.2.2.2.2.2.2.2.2 i).2.2.2.1]) hc (Or.inl ⟨hb, rfl⟩)

/-! ### Part 1 -/

/-- The cash left after moving from `c` to `x` with cash `k`. -/
def cashF (P : Two ι Z) (k : ℝ) (x c : ι → ℝ) : ℝ := k - ∑ i, (x i - c i) - cost P (x - c)

lemma cashF_concave {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (k1 k2 : ℝ) (x1 x2 c1 c2 : ι → ℝ) :
    a * cashF P k1 x1 c1 + b * cashF P k2 x2 c2 ≤
      cashF P (a * k1 + b * k2) (a • x1 + b • x2) (a • c1 + b • c2) := by
  have hc := cost_convex hr ha hb (x1 - c1) (x2 - c2)
  have e : a • x1 + b • x2 - (a • c1 + b • c2) = a • (x1 - c1) + b • (x2 - c2) := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have es : ∑ i, ((a • x1 + b • x2) i - (a • c1 + b • c2) i) =
      a * ∑ i, (x1 i - c1 i) + b * ∑ i, (x2 i - c2 i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold cashF
  rw [e, es]
  nlinarith

lemma cashF_mono (P : Two ι Z) {k k' : ℝ} (h : k ≤ k') (x c : ι → ℝ) : cashF P k x c ≤ cashF P k' x c := by
  unfold cashF; linarith

lemma comb_sub {a b : ℝ} (hab : a + b = 1) (x y c : ι → ℝ) :
    a • x + b • y - c = a • (x - c) + b • (y - c) := by
  ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have : c i = (a + b) * c i := by rw [hab, one_mul]
  linarith

lemma carry_comb (P : Two ι Z) (z : Z) (a b : ℝ) (x y : ι → ℝ) :
    carry P z (a • x + b • y) = a • carry P z x + b • carry P z y := by
  ext i; simp only [carry, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma quad_comb (S : ι → ι → ℝ) (a : ℝ) (x y : ι → ℝ) :
    quad S (a • x + (1 - a) • y) = a * quad S x + (1 - a) * quad S y - a * (1 - a) * quad S (x - y) := by
  unfold quad
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma Qv_concave {mu : ι → ℝ} {S : ι → ι → ℝ} (hS : PSD S) {γ : ℝ} (hγ : 0 ≤ γ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x y : ι → ℝ) :
    a * Qv mu S γ x + b * Qv mu S γ y ≤ Qv mu S γ (a • x + b • y) := by
  obtain rfl : b = 1 - a := by linarith
  unfold Qv
  rw [quad_comb]
  have el : ∑ i, mu i * (a • x + (1 - a) • y) i = a * ∑ i, mu i * x i + (1 - a) * ∑ i, mu i * y i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [el]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (hS.2 (x - y)), mul_nonneg hγ (mul_nonneg (mul_nonneg ha hb) (hS.2 (x - y)))]

/-- Selling down to the cap is always funded. -/
lemma sell_feas {P : Two ι Z} (hP : Hyp P) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {k : ℝ} (hk : 0 ≤ k) :
    Box P (fun i => min (c i) (P.xbar i)) ∧ 0 ≤ cashF P k (fun i => min (c i) (P.xbar i)) c := by
  have hr := hP.2.2.2.2.2.2.2.2
  refine ⟨fun i => ⟨le_min (hc i) (by linarith [(hr i).2.2.2.1, (hr i).2.2.2.2]), min_le_right _ _⟩, ?_⟩
  unfold cashF cost
  rw [sub_sub, ← sum_add_distrib]
  have : ∀ i, (min (c i) (P.xbar i) - c i) + pc (P.kp i) (P.km i) (((fun i => min (c i) (P.xbar i)) - c) i) ≤ 0 := by
    intro i
    have h1 : min (c i) (P.xbar i) - c i ≤ 0 := by linarith [min_le_left (c i) (P.xbar i)]
    simp only [Pi.sub_apply, pc]
    rw [max_eq_right h1, max_eq_left (by linarith)]
    nlinarith [(hr i).2.2.1]
  linarith [sum_nonpos fun i (_ : i ∈ univ) => this i]

lemma feas_nonempty {P : Two ι Z} (hP : Hyp P) : (Feas P).Nonempty := by
  have hr := hP.2.2.2.2.2.2.2.2
  have hxm : ∀ i, 0 ≤ P.xm i := fun i => (hr i).2.2.2.1
  have h0m : h0 P P.xm = P.h := by
    simp [h0, cost, pc]
  refine ⟨(P.xm, fun z i => min (carry P z P.xm i) (P.xbar i)), fun i => ⟨hxm i, (hr i).2.2.2.2⟩,
    fun z => (sell_feas hP (c := carry P z P.xm) (fun i => mul_nonneg (hP.2.2.2.2.2.2.2.1 z i).le (hxm i))
      (k := h0 P P.xm) (by rw [h0m]; exact hP.2.2.2.1.le)).1, by rw [h0m]; exact hP.2.2.2.1.le,
    fun z => (sell_feas hP (c := carry P z P.xm) (fun i => mul_nonneg (hP.2.2.2.2.2.2.2.1 z i).le (hxm i))
      (k := h0 P P.xm) (by rw [h0m]; exact hP.2.2.2.1.le)).2⟩

lemma box_comb {P : Two ι Z} {x y : ι → ℝ} (hx : Box P x) (hy : Box P y) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : Box P (a • x + b • y) := fun i => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨x0, x1⟩ := hx i; obtain ⟨y0, y1⟩ := hy i
  constructor
  · positivity
  · nlinarith

lemma h0_concave {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (x y : ι → ℝ) :
    a * h0 P x + b * h0 P y ≤ h0 P (a • x + b • y) := by
  have := cashF_concave hr ha hb P.h P.h x y P.xm P.xm
  have e : a • P.xm + b • P.xm = P.xm := by rw [← add_smul, hab, one_smul]
  rw [e, ← add_mul, hab, one_mul] at this
  exact this

lemma h1_concave {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (X Y : (ι → ℝ) × (Z → ι → ℝ)) (z : Z) :
    a * h1 P X.1 X.2 z + b * h1 P Y.1 Y.2 z ≤ h1 P (a • X + b • Y).1 (a • X + b • Y).2 z := by
  have hA := cashF_concave hr ha hb (h0 P X.1) (h0 P Y.1) (X.2 z) (Y.2 z) (carry P z X.1) (carry P z Y.1)
  have hB := cashF_mono P (h0_concave hr ha hb hab X.1 Y.1) (a • X.2 z + b • Y.2 z)
    (a • carry P z X.1 + b • carry P z Y.1)
  have e : h1 P (a • X + b • Y).1 (a • X + b • Y).2 z =
      cashF P (h0 P (a • X.1 + b • Y.1)) (a • X.2 z + b • Y.2 z) (a • carry P z X.1 + b • carry P z Y.1) := by
    rw [← carry_comb]; rfl
  rw [e]
  exact hA.trans hB

lemma feas_convex {P : Two ι Z} (hP : Hyp P) : Convex ℝ (Feas P) := by
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  intro X hX Y hY a b ha hb hab
  refine ⟨box_comb hX.1 hY.1 ha hb hab, fun z => box_comb (hX.2.1 z) (hY.2.1 z) ha hb hab, ?_, fun z => ?_⟩
  · have := h0_concave hr ha hb hab X.1 Y.1
    have := mul_nonneg ha hX.2.2.1; have := mul_nonneg hb hY.2.2.1
    show 0 ≤ h0 P (a • X.1 + b • Y.1); linarith
  · have := h1_concave hr ha hb hab X Y z
    have := mul_nonneg ha (hX.2.2.2 z); have := mul_nonneg hb (hY.2.2.2 z)
    linarith

/-- The review value `Q - C(x - c)` is concave in `(x, c)`. -/
lemma val_concave {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {mu : ι → ℝ} {S : ι → ι → ℝ}
    (hS : PSD S) (hγ : 0 ≤ P.gamma) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y c d : ι → ℝ) :
    a * (Qv mu S P.gamma x - cost P (x - c)) + b * (Qv mu S P.gamma y - cost P (y - d)) ≤
      Qv mu S P.gamma (a • x + b • y) - cost P (a • x + b • y - (a • c + b • d)) := by
  have hq := Qv_concave (mu := mu) hS hγ ha hb hab x y
  have e : a • x + b • y - (a • c + b • d) = a • (x - c) + b • (y - d) := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have := cost_convex hr ha hb (x - c) (y - d)
  linarith

lemma J_concave {P : Two ι Z} (hP : Hyp P) : ConcaveOn ℝ (Feas P) (J P) := by
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  refine ⟨feas_convex hP, fun X _ Y _ a b ha hb hab => ?_⟩
  have e0 : a • P.xm + b • P.xm = P.xm := by rw [← add_smul, hab, one_smul]
  have h0c := val_concave (mu := P.mu0) hr hP.2.2.2.2.1 hP.1.le ha hb hab X.1 Y.1 P.xm P.xm
  rw [e0] at h0c
  have hz : ∀ z, a * (P.q z * (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1))) +
      b * (P.q z * (Q1 P z (Y.2 z) - cost P (Y.2 z - carry P z Y.1))) ≤
      P.q z * (Q1 P z ((a • X + b • Y).2 z) - cost P ((a • X + b • Y).2 z - carry P z (a • X + b • Y).1)) := by
    intro z
    have := val_concave (mu := P.mu1 z) hr (hP.2.2.2.2.2.1 z) hP.1.le ha hb hab (X.2 z) (Y.2 z)
      (carry P z X.1) (carry P z Y.1)
    have e : (a • X + b • Y).2 z - carry P z (a • X + b • Y).1 =
        a • X.2 z + b • Y.2 z - (a • carry P z X.1 + b • carry P z Y.1) := by
      rw [← carry_comb]; rfl
    have e2 : (a • X + b • Y).2 z = a • X.2 z + b • Y.2 z := rfl
    rw [e, e2]
    unfold Q1
    nlinarith [mul_le_mul_of_nonneg_left this (hP.2.2.2.2.2.2.1 z).le]
  have hs := sum_le_sum fun z (_ : z ∈ univ) => hz z
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  show a * J P X + b * J P Y ≤ J P (a • X + b • Y)
  unfold J
  have e1 : (a • X + b • Y).1 = a • X.1 + b • Y.1 := rfl
  rw [e1]
  rw [e1] at hs
  change a * (Qv P.mu0 P.S0 P.gamma X.1 - _ + _) + b * (Qv P.mu0 P.S0 P.gamma Y.1 - _ + _) ≤
    Qv P.mu0 P.S0 P.gamma _ - _ + _
  nlinarith [mul_le_mul_of_nonneg_left hs hP.2.1.le]

lemma feas_compact {P : Two ι Z} : IsCompact (Feas P) := by
  have hK : IsCompact ((Set.univ.pi fun i => Set.Icc 0 (P.xbar i)) ×ˢ
      (Set.univ.pi fun _ : Z => Set.univ.pi fun i => Set.Icc 0 (P.xbar i))) :=
    (isCompact_univ_pi fun i => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun i => isCompact_Icc)
  refine hK.of_isClosed_subset ?_ fun X hX => ⟨fun i _ => hX.1 i, fun z _ i _ => hX.2.1 z i⟩
  have e : Feas P = (⋂ i, ({X : (ι → ℝ) × (Z → ι → ℝ) | 0 ≤ X.1 i} ∩ {X | X.1 i ≤ P.xbar i})) ∩
      ((⋂ z, ⋂ i, ({X : (ι → ℝ) × (Z → ι → ℝ) | 0 ≤ X.2 z i} ∩ {X | X.2 z i ≤ P.xbar i})) ∩
      ({X | 0 ≤ h0 P X.1} ∩ ⋂ z, {X | 0 ≤ h1 P X.1 X.2 z})) := by
    ext X; simp [Feas, Box]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop))
    (isClosed_le (by fun_prop) (by fun_prop))) (IsClosed.inter (isClosed_iInter fun z => isClosed_iInter
    fun i => IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop)) (isClosed_le (by fun_prop)
    (by fun_prop))) (IsClosed.inter (isClosed_le (by fun_prop) (by unfold h0 cost pc; fun_prop))
    (isClosed_iInter fun z => isClosed_le (by fun_prop) (by unfold h1 h0 cost pc carry; fun_prop))))

/-- The last review's feasible set from `p = (x⁻, h⁻)`. -/
def F1 (P : Two ι Z) (p : (ι → ℝ) × ℝ) : Set (ι → ℝ) := {x | Box P x ∧ 0 ≤ cashF P p.2 x p.1}

/-- The last review's value at `x` from `p`. -/
def f1 (P : Two ι Z) (z : Z) (p : (ι → ℝ) × ℝ) (x : ι → ℝ) : ℝ := Q1 P z x - cost P (x - p.1)

lemma F1_compact (P : Two ι Z) (p : (ι → ℝ) × ℝ) : IsCompact (F1 P p) := by
  refine (isCompact_univ_pi fun i => isCompact_Icc (a := (0 : ℝ)) (b := P.xbar i)).of_isClosed_subset
    ?_ fun x hx i _ => hx.1 i
  have e : F1 P p = (⋂ i, ({x : ι → ℝ | 0 ≤ x i} ∩ {x | x i ≤ P.xbar i})) ∩ {x | 0 ≤ cashF P p.2 x p.1} := by
    ext x; simp [F1, Box]
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun i => IsClosed.inter (isClosed_le (by fun_prop) (by fun_prop))
    (isClosed_le (by fun_prop) (by fun_prop))) (isClosed_le (by fun_prop) (by unfold cashF cost pc; fun_prop))

lemma V1_attain (P : Two ι Z) (z : Z) {p : (ι → ℝ) × ℝ} (hp : p ∈ Dom P) :
    ∃ x ∈ F1 P p, IsMaxOn (f1 P z p) (F1 P p) x ∧ V1 P z p = f1 P z p x := by
  obtain ⟨x, hx, hmax⟩ := (F1_compact P p).exists_isMaxOn hp
    (by unfold f1 Q1 Qv quad cost pc; fun_prop : Continuous (f1 P z p)).continuousOn
  exact ⟨x, hx, hmax, IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ hx, by
    rintro _ ⟨w, hw, rfl⟩; exact hmax hw⟩⟩

lemma le_V1 (P : Two ι Z) (z : Z) {p : (ι → ℝ) × ℝ} (hp : p ∈ Dom P) {x : ι → ℝ} (hx : x ∈ F1 P p) :
    f1 P z p x ≤ V1 P z p := by
  obtain ⟨x', -, hm, he⟩ := V1_attain P z hp
  rw [he]; exact hm hx

lemma F1_comb {P : Two ι Z} (hP : Hyp P) {p p' : (ι → ℝ) × ℝ} {x x' : ι → ℝ} (hx : x ∈ F1 P p)
    (hx' : x' ∈ F1 P p') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • x' ∈ F1 P (a • p + b • p') := by
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  refine ⟨box_comb hx.1 hx'.1 ha hb hab, ?_⟩
  have := cashF_concave hr ha hb p.2 p'.2 x x' p.1 p'.1
  have := mul_nonneg ha hx.2; have := mul_nonneg hb hx'.2
  show 0 ≤ cashF P (a * p.2 + b * p'.2) (a • x + b • x') (a • p.1 + b • p'.1)
  linarith

lemma dom_convex {P : Two ι Z} (hP : Hyp P) : Convex ℝ (Dom P) := by
  rintro p ⟨x, hx⟩ p' ⟨x', hx'⟩ a b ha hb hab
  exact ⟨_, F1_comb hP hx hx' ha hb hab⟩

lemma V1_concave {P : Two ι Z} (hP : Hyp P) (z : Z) : ConcaveOn ℝ (Dom P) (V1 P z) := by
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  refine ⟨dom_convex hP, fun p hp p' hp' a b ha hb hab => ?_⟩
  obtain ⟨x, hx, -, hex⟩ := V1_attain P z hp
  obtain ⟨x', hx', -, hex'⟩ := V1_attain P z hp'
  have hle := le_V1 P z (dom_convex hP hp hp' ha hb hab) (F1_comb hP hx hx' ha hb hab)
  have hv := val_concave (mu := P.mu1 z) hr (hP.2.2.2.2.2.1 z) hP.1.le ha hb hab x x' p.1 p'.1
  rw [smul_eq_mul, smul_eq_mul, hex, hex']
  exact hv.trans hle

lemma V1_mono (P : Two ι Z) (z : Z) (x : ι → ℝ) {a b : ℝ} (hd : (x, a) ∈ Dom P) (hab : a ≤ b) :
    V1 P z (x, a) ≤ V1 P z (x, b) := by
  obtain ⟨w, hw, -, he⟩ := V1_attain P z hd
  have hw' : w ∈ F1 P (x, b) := ⟨hw.1, (hw.2.trans (cashF_mono P hab w x))⟩
  rw [he]
  exact le_V1 P z ⟨w, hw'⟩ hw'

lemma dom_mem {P : Two ι Z} (hP : Hyp P) {x0 : ι → ℝ} (hx : x0 ∈ RootSet P) (z : Z) :
    (carry P z x0, h0 P x0) ∈ Dom P :=
  ⟨_, sell_feas hP (fun i => mul_nonneg (hP.2.2.2.2.2.2.2.1 z i).le (hx.1 i).1) hx.2⟩

lemma root_concave {P : Two ι Z} (hP : Hyp P) : ConcaveOn ℝ (RootSet P) (RootObj P) := by
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  have hconv : Convex ℝ (RootSet P) := by
    intro x hx y hy a b ha hb hab
    refine ⟨box_comb hx.1 hy.1 ha hb hab, ?_⟩
    have := h0_concave hr ha hb hab x y
    have := mul_nonneg ha hx.2; have := mul_nonneg hb hy.2
    linarith
  refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
  have e0 : a • P.xm + b • P.xm = P.xm := by rw [← add_smul, hab, one_smul]
  have h0c := val_concave (mu := P.mu0) hr hP.2.2.2.2.1 hP.1.le ha hb hab x y P.xm P.xm
  rw [e0] at h0c
  have hz : ∀ z, a * (P.q z * V1 P z (carry P z x, h0 P x)) + b * (P.q z * V1 P z (carry P z y, h0 P y)) ≤
      P.q z * V1 P z (carry P z (a • x + b • y), h0 P (a • x + b • y)) := by
    intro z
    have hc := (V1_concave hP z).2 (dom_mem hP hx z) (dom_mem hP hy z) ha hb hab
    have hdom := dom_convex hP (dom_mem hP hx z) (dom_mem hP hy z) ha hb hab
    have ep : a • (carry P z x, h0 P x) + b • (carry P z y, h0 P y) =
        (carry P z (a • x + b • y), a * h0 P x + b * h0 P y) := by
      rw [carry_comb]; rfl
    rw [ep] at hc hdom
    have hm := V1_mono P z _ hdom (h0_concave hr ha hb hab x y)
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left (hc.trans hm) (hP.2.2.2.2.2.2.1 z).le]
  have hs := sum_le_sum fun z (_ : z ∈ univ) => hz z
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  show a * RootObj P x + b * RootObj P y ≤ RootObj P (a • x + b • y)
  unfold RootObj
  change a * (Qv P.mu0 P.S0 P.gamma x - _ + _) + b * (Qv P.mu0 P.S0 P.gamma y - _ + _) ≤
    Qv P.mu0 P.S0 P.gamma _ - _ + _
  nlinarith [mul_le_mul_of_nonneg_left hs hP.2.1.le]

theorem structure_ : Structure := by
  intro ι Z _ _ P hP
  obtain ⟨X, hX, hmax⟩ := feas_compact.exists_isMaxOn (feas_nonempty hP)
    (by unfold J Q0 Q1 Qv quad cost pc carry; fun_prop : Continuous (J P)).continuousOn
  exact ⟨⟨X, hX, hmax⟩, J_concave hP, fun z => ⟨V1_concave hP z, fun x a b hd hab => V1_mono P z x hd hab⟩,
    fun x0 hx z => dom_mem hP hx z, root_concave hP⟩

/-! ### Part 2: necessity (the lifted program and AX-13) -/

section Lift

open Classical Matrix

/-- Lifted variables: `x_0`, today's cost bounds `y_0`, `x_1`, tomorrow's cost bounds `y_1`. -/
abbrev Vr (ι Z : Type) := (ι ⊕ ι) ⊕ ((Z × ι) ⊕ (Z × ι))

/-- Lifted constraints: today's upper and lower box, two cost pieces and budget; the same tomorrow
per state. -/
abbrev Lc (ι Z : Type) := (ι ⊕ ι ⊕ ι ⊕ ι ⊕ Unit) ⊕ ((Z × ι) ⊕ (Z × ι) ⊕ (Z × ι) ⊕ (Z × ι) ⊕ Z)

def X0 (w : Vr ι Z → ℝ) (i : ι) : ℝ := w (Sum.inl (Sum.inl i))
def Y0 (w : Vr ι Z → ℝ) (i : ι) : ℝ := w (Sum.inl (Sum.inr i))
def X1 (w : Vr ι Z → ℝ) (z : Z) (i : ι) : ℝ := w (Sum.inr (Sum.inl (z, i)))
def Y1 (w : Vr ι Z → ℝ) (z : Z) (i : ι) : ℝ := w (Sum.inr (Sum.inr (z, i)))

/-- A lifted vector from its four blocks. -/
def mk (a b : ι → ℝ) (c d : Z → ι → ℝ) : Vr ι Z → ℝ :=
  Sum.elim (Sum.elim a b) (Sum.elim (fun p => c p.1 p.2) (fun p => d p.1 p.2))

lemma dot_mk (a b : ι → ℝ) (c d : Z → ι → ℝ) (w : Vr ι Z → ℝ) :
    mk a b c d ⬝ᵥ w = ∑ i, a i * X0 w i + ∑ i, b i * Y0 w i + ∑ z, ∑ i, c z i * X1 w z i +
      ∑ z, ∑ i, d z i * Y1 w z i := by
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, mk, Sum.elim_inl, Sum.elim_inr,
    X0, Y0, X1, Y1]
  ring

def cA (P : Two ι Z) : Lc ι Z → Vr ι Z → ℝ
  | Sum.inl (Sum.inl i) => mk (Pi.single i 1) 0 0 0
  | Sum.inl (Sum.inr (Sum.inl i)) => mk (Pi.single i (-1)) 0 0 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl i))) => mk (Pi.single i (P.kp i)) (Pi.single i (-1)) 0 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) =>
      mk (Pi.single i (-P.km i)) (Pi.single i (-1)) 0 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => mk 1 1 0 0
  | Sum.inr (Sum.inl (z, i)) => mk 0 0 (Pi.single z (Pi.single i 1)) 0
  | Sum.inr (Sum.inr (Sum.inl (z, i))) => mk 0 0 (Pi.single z (Pi.single i (-1))) 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (z, i)))) =>
      mk (Pi.single i (-(P.kp i * P.g z i))) 0 (Pi.single z (Pi.single i (P.kp i)))
        (Pi.single z (Pi.single i (-1)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (z, i))))) =>
      mk (Pi.single i (P.km i * P.g z i)) 0 (Pi.single z (Pi.single i (-P.km i)))
        (Pi.single z (Pi.single i (-1)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr z)))) =>
      mk (fun i => 1 - P.g z i) 1 (Pi.single z 1) (Pi.single z 1)

def cB (P : Two ι Z) : Lc ι Z → ℝ
  | Sum.inl (Sum.inl i) => P.xbar i
  | Sum.inl (Sum.inr (Sum.inl _)) => 0
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl i))) => P.kp i * P.xm i
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => -(P.km i * P.xm i)
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => P.h + ∑ i, P.xm i
  | Sum.inr (Sum.inl (_, i)) => P.xbar i
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => P.h + ∑ i, P.xm i

/-! The constraint names. -/
def up0 (i : ι) : Lc ι Z := Sum.inl (Sum.inl i)
def lo0 (i : ι) : Lc ι Z := Sum.inl (Sum.inr (Sum.inl i))
def cp0 (i : ι) : Lc ι Z := Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))
def cm0 (i : ι) : Lc ι Z := Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
def bud0 : Lc ι Z := Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
def up1 (z : Z) (i : ι) : Lc ι Z := Sum.inr (Sum.inl (z, i))
def lo1 (z : Z) (i : ι) : Lc ι Z := Sum.inr (Sum.inr (Sum.inl (z, i)))
def cp1 (z : Z) (i : ι) : Lc ι Z := Sum.inr (Sum.inr (Sum.inr (Sum.inl (z, i))))
def cm1 (z : Z) (i : ι) : Lc ι Z := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (z, i)))))
def bud1 (z : Z) : Lc ι Z := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr z))))

section Dots

variable (P : Two ι Z) (w : Vr ι Z → ℝ) (z : Z) (i : ι)

lemma d_up0 : cA P (up0 i) ⬝ᵥ w = X0 w i := by simp [up0, cA, dot_mk, Pi.single_apply]
lemma d_lo0 : cA P (lo0 i) ⬝ᵥ w = -X0 w i := by simp [lo0, cA, dot_mk, Pi.single_apply]
lemma d_cp0 : cA P (cp0 i) ⬝ᵥ w = P.kp i * X0 w i - Y0 w i := by
  simp [cp0, cA, dot_mk, Pi.single_apply]; ring
lemma d_cm0 : cA P (cm0 i) ⬝ᵥ w = -P.km i * X0 w i - Y0 w i := by
  simp [cm0, cA, dot_mk, Pi.single_apply]; ring
lemma d_bud0 : cA P bud0 ⬝ᵥ w = ∑ i, X0 w i + ∑ i, Y0 w i := by simp [bud0, cA, dot_mk]
lemma d_up1 : cA P (up1 z i) ⬝ᵥ w = X1 w z i := by simp [up1, cA, dot_mk, Pi.single_apply, ite_apply]
lemma d_lo1 : cA P (lo1 z i) ⬝ᵥ w = -X1 w z i := by simp [lo1, cA, dot_mk, Pi.single_apply, ite_apply]
lemma d_cp1 : cA P (cp1 z i) ⬝ᵥ w = P.kp i * (X1 w z i - P.g z i * X0 w i) - Y1 w z i := by
  simp [cp1, cA, dot_mk, Pi.single_apply, ite_apply]; ring
lemma d_cm1 : cA P (cm1 z i) ⬝ᵥ w = -P.km i * (X1 w z i - P.g z i * X0 w i) - Y1 w z i := by
  simp [cm1, cA, dot_mk, Pi.single_apply, ite_apply]; ring
lemma d_bud1 : cA P (bud1 z) ⬝ᵥ w = ∑ i, (1 - P.g z i) * X0 w i + ∑ i, Y0 w i + ∑ i, X1 w z i +
    ∑ i, Y1 w z i := by
  simp [bud1, cA, dot_mk, Pi.single_apply, ite_apply]

end Dots

end Lift


section Comp

open Classical Matrix

variable (P : Two ι Z) (η : Lc ι Z → ℝ) (z : Z) (j : ι)

lemma comp_x0 : ∑ l, η l * cA P l (Sum.inl (Sum.inl j)) =
    η (up0 j) - η (lo0 j) + η (cp0 j) * P.kp j - η (cm0 j) * P.km j + η bud0 -
      ∑ z, η (cp1 z j) * (P.kp j * P.g z j) + ∑ z, η (cm1 z j) * (P.km j * P.g z j) +
      ∑ z, η (bud1 z) * (1 - P.g z j) := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, cA, mk, Pi.single_apply, ite_apply, up0, lo0,
    cp0, cm0, bud0, cp1, cm1, bud1]
  ring

lemma comp_y0 : ∑ l, η l * cA P l (Sum.inl (Sum.inr j)) =
    -η (cp0 j) - η (cm0 j) + η bud0 + ∑ z, η (bud1 z) := by
  simp [Fintype.sum_sum_type, cA, mk, Pi.single_apply, ite_apply, cp0, cm0, bud0, bud1]
  ring

lemma comp_x1 : ∑ l, η l * cA P l (Sum.inr (Sum.inl (z, j))) =
    η (up1 z j) - η (lo1 z j) + η (cp1 z j) * P.kp j - η (cm1 z j) * P.km j + η (bud1 z) := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, cA, mk, Pi.single_apply, ite_apply, up1, lo1,
    cp1, cm1, bud1]
  ring

lemma comp_y1 : ∑ l, η l * cA P l (Sum.inr (Sum.inr (z, j))) =
    -η (cp1 z j) - η (cm1 z j) + η (bud1 z) := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, cA, mk, Pi.single_apply, ite_apply, cp1, cm1,
    bud1]
  ring

end Comp

section Lifted

open Classical Matrix

/-- The lifted point of a policy: the costs as the bounds. -/
def liftX (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : Vr ι Z → ℝ :=
  mk X.1 (fun i => pc (P.kp i) (P.km i) (X.1 i - P.xm i)) X.2
    (fun z i => pc (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i))

/-- The lifted objective. -/
def fL (P : Two ι Z) (w : Vr ι Z → ℝ) : ℝ :=
  Q0 P (X0 w) - ∑ i, Y0 w i + P.beta * ∑ z, P.q z * (Q1 P z (X1 w z) - ∑ i, Y1 w z i)

lemma fL_lift (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : fL P (liftX P X) = J P X := rfl

lemma pc_ge_lin {kp km : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (u : ℝ) :
    kp * u ≤ pc kp km u ∧ -km * u ≤ pc kp km u := by
  unfold pc
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; constructor <;> nlinarith
  · rw [max_eq_left h, max_eq_right (by linarith)]; constructor <;> nlinarith

lemma pc_le_of {kp km u y : ℝ} (h1 : kp * u ≤ y) (h2 : -km * u ≤ y) : pc kp km u ≤ y := by
  unfold pc
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; linarith
  · rw [max_eq_left h, max_eq_right (by linarith)]; linarith

lemma h0_eq (P : Two ι Z) (x : ι → ℝ) :
    h0 P x = P.h + ∑ i, P.xm i - ∑ i, x i - ∑ i, pc (P.kp i) (P.km i) (x i - P.xm i) := by
  simp only [h0, cost, Pi.sub_apply, sum_sub_distrib]; ring

lemma h1_eq (P : Two ι Z) (x0 : ι → ℝ) (x1 : Z → ι → ℝ) (z : Z) :
    h1 P x0 x1 z = P.h + ∑ i, P.xm i - (∑ i, (1 - P.g z i) * x0 i +
      ∑ i, pc (P.kp i) (P.km i) (x0 i - P.xm i) + ∑ i, x1 z i +
      ∑ i, pc (P.kp i) (P.km i) (x1 z i - carry P z x0 i)) := by
  simp only [h1, h0_eq, cost, Pi.sub_apply, sum_sub_distrib, carry, sub_mul, one_mul]; ring

lemma lift_feas {P : Two ι Z} (hP : Hyp P) {X : (ι → ℝ) × (Z → ι → ℝ)} (hX : X ∈ Feas P) :
    ∀ l, cA P l ⬝ᵥ liftX P X ≤ cB P l := by
  have hr := hP.2.2.2.2.2.2.2.2
  rintro ((i | i | i | i | u) | (⟨z, i⟩ | ⟨z, i⟩ | ⟨z, i⟩ | ⟨z, i⟩ | z))
  · show cA P (up0 i) ⬝ᵥ _ ≤ _; rw [d_up0]; exact (hX.1 i).2
  · show cA P (lo0 i) ⬝ᵥ _ ≤ _; rw [d_lo0]; simp only [cB]; linarith [(hX.1 i).1, show X0 (liftX P X) i = X.1 i from rfl]
  · show cA P (cp0 i) ⬝ᵥ _ ≤ _; rw [d_cp0]
    have := (pc_ge_lin (hr i).1 (hr i).2.1 (X.1 i - P.xm i)).1
    simp only [cB, X0, Y0, liftX, mk, Sum.elim_inl, Sum.elim_inr]; linarith
  · show cA P (cm0 i) ⬝ᵥ _ ≤ _; rw [d_cm0]
    have := (pc_ge_lin (hr i).1 (hr i).2.1 (X.1 i - P.xm i)).2
    simp only [cB, X0, Y0, liftX, mk, Sum.elim_inl, Sum.elim_inr]; linarith
  · show cA P bud0 ⬝ᵥ _ ≤ _; rw [d_bud0]
    have := hX.2.2.1; rw [h0_eq] at this
    simp only [cB, X0, Y0, liftX, mk, Sum.elim_inl, Sum.elim_inr]; linarith
  · show cA P (up1 z i) ⬝ᵥ _ ≤ _; rw [d_up1]; exact (hX.2.1 z i).2
  · show cA P (lo1 z i) ⬝ᵥ _ ≤ _; rw [d_lo1]; simp only [cB]
    linarith [(hX.2.1 z i).1, show X1 (liftX P X) z i = X.2 z i from rfl]
  · show cA P (cp1 z i) ⬝ᵥ _ ≤ _; rw [d_cp1]
    have := (pc_ge_lin (hr i).1 (hr i).2.1 (X.2 z i - carry P z X.1 i)).1
    simp only [cB, X0, X1, Y1, liftX, mk, Sum.elim_inl, Sum.elim_inr, carry] at this ⊢; linarith
  · show cA P (cm1 z i) ⬝ᵥ _ ≤ _; rw [d_cm1]
    have := (pc_ge_lin (hr i).1 (hr i).2.1 (X.2 z i - carry P z X.1 i)).2
    simp only [cB, X0, X1, Y1, liftX, mk, Sum.elim_inl, Sum.elim_inr, carry] at this ⊢; linarith
  · show cA P (bud1 z) ⬝ᵥ _ ≤ _; rw [d_bud1]
    have := hX.2.2.2 z; rw [h1_eq] at this
    simp only [cB, X0, Y0, X1, Y1, liftX, mk, Sum.elim_inl, Sum.elim_inr]; linarith

/-- A lifted feasible point projects to a feasible policy, with the bounds above the costs. -/
lemma lift_proj {P : Two ι Z} {w : Vr ι Z → ℝ} (hw : ∀ l, cA P l ⬝ᵥ w ≤ cB P l) :
    (X0 w, X1 w) ∈ Feas P ∧ (∀ i, pc (P.kp i) (P.km i) (X0 w i - P.xm i) ≤ Y0 w i) ∧
      ∀ z i, pc (P.kp i) (P.km i) (X1 w z i - carry P z (X0 w) i) ≤ Y1 w z i := by
  have c0 : ∀ i, pc (P.kp i) (P.km i) (X0 w i - P.xm i) ≤ Y0 w i := fun i => by
    have h1 := hw (cp0 i); have h2 := hw (cm0 i)
    rw [d_cp0] at h1; rw [d_cm0] at h2
    simp only [cB, cp0, cm0] at h1 h2
    exact pc_le_of (by linarith) (by linarith)
  have c1 : ∀ z i, pc (P.kp i) (P.km i) (X1 w z i - carry P z (X0 w) i) ≤ Y1 w z i := fun z i => by
    have h1 := hw (cp1 z i); have h2 := hw (cm1 z i)
    rw [d_cp1] at h1; rw [d_cm1] at h2
    simp only [cB, cp1, cm1] at h1 h2
    exact pc_le_of (by simp only [carry]; linarith) (by simp only [carry]; linarith)
  refine ⟨⟨fun i => ⟨?_, ?_⟩, fun z i => ⟨?_, ?_⟩, ?_, fun z => ?_⟩, c0, c1⟩
  · have := hw (lo0 i); rw [d_lo0] at this; simp only [cB, lo0] at this; show 0 ≤ X0 w i; linarith
  · have := hw (up0 i); rw [d_up0] at this; exact this
  · have := hw (lo1 z i); rw [d_lo1] at this; simp only [cB, lo1] at this; show 0 ≤ X1 w z i; linarith
  · have := hw (up1 z i); rw [d_up1] at this; exact this
  · have h := hw bud0; rw [d_bud0] at h; simp only [cB, bud0] at h
    have := sum_le_sum fun i (_ : i ∈ univ) => c0 i
    show 0 ≤ h0 P (X0 w); rw [h0_eq]; linarith
  · have h := hw (bud1 z); rw [d_bud1] at h; simp only [cB, bud1] at h
    have := sum_le_sum fun i (_ : i ∈ univ) => c0 i
    have := sum_le_sum fun i (_ : i ∈ univ) => c1 z i
    show 0 ≤ h1 P (X0 w) (X1 w) z; rw [h1_eq]; linarith

lemma fL_le {P : Two ι Z} (hP : Hyp P) {w : Vr ι Z → ℝ} (hw : ∀ l, cA P l ⬝ᵥ w ≤ cB P l) :
    fL P w ≤ J P (X0 w, X1 w) := by
  obtain ⟨-, c0, c1⟩ := lift_proj hw
  have s0 := sum_le_sum fun i (_ : i ∈ univ) => c0 i
  have hz : ∀ z, P.q z * (Q1 P z (X1 w z) - ∑ i, Y1 w z i) ≤
      P.q z * (Q1 P z (X1 w z) - cost P (X1 w z - carry P z (X0 w))) := fun z => by
    have := sum_le_sum fun i (_ : i ∈ univ) => c1 z i
    exact mul_le_mul_of_nonneg_left (by simp only [cost, Pi.sub_apply]; linarith)
      (hP.2.2.2.2.2.2.1 z).le
  have := mul_le_mul_of_nonneg_left (sum_le_sum fun z (_ : z ∈ univ) => hz z) hP.2.1.le
  simp only [fL, J, cost, Pi.sub_apply] at this ⊢
  linarith

lemma lift_max {P : Two ι Z} (hP : Hyp P) {X : (ι → ℝ) × (Z → ι → ℝ)}
    (hmax : IsMaxOn (J P) (Feas P) X) :
    IsMaxOn (fL P) {w | ∀ l, cA P l ⬝ᵥ w ≤ cB P l} (liftX P X) := by
  intro w hw
  show fL P w ≤ fL P (liftX P X)
  rw [fL_lift]
  exact (fL_le hP hw).trans (hmax (lift_proj hw).1)

lemma fL_concave {P : Two ι Z} (hP : Hyp P) : ConcaveOn ℝ Set.univ (fL P) := by
  refine ⟨convex_univ, fun w _ w' _ a b ha hb hab => ?_⟩
  have e0 : X0 (a • w + b • w') = a • X0 w + b • X0 w' := rfl
  have e1 : ∀ z, X1 (a • w + b • w') z = a • X1 w z + b • X1 w' z := fun z => rfl
  have ey0 : ∑ i, Y0 (a • w + b • w') i = a * ∑ i, Y0 w i + b * ∑ i, Y0 w' i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; rfl
  have ey1 : ∀ z, ∑ i, Y1 (a • w + b • w') z i = a * ∑ i, Y1 w z i + b * ∑ i, Y1 w' z i := fun z => by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; rfl
  have hq0 := Qv_concave (mu := P.mu0) hP.2.2.2.2.1 hP.1.le ha hb hab (X0 w) (X0 w')
  have hz : ∀ z, a * (P.q z * (Q1 P z (X1 w z) - ∑ i, Y1 w z i)) +
      b * (P.q z * (Q1 P z (X1 w' z) - ∑ i, Y1 w' z i)) ≤
      P.q z * (Q1 P z (X1 (a • w + b • w') z) - ∑ i, Y1 (a • w + b • w') z i) := fun z => by
    have := Qv_concave (mu := P.mu1 z) (hP.2.2.2.2.2.1 z) hP.1.le ha hb hab (X1 w z) (X1 w' z)
    rw [e1, ey1]; unfold Q1
    nlinarith [mul_le_mul_of_nonneg_left this (hP.2.2.2.2.2.2.1 z).le]
  have hs := sum_le_sum fun z (_ : z ∈ univ) => hz z
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  show a * fL P w + b * fL P w' ≤ fL P (a • w + b • w')
  unfold fL
  rw [e0, ey0]; unfold Q0
  nlinarith [mul_le_mul_of_nonneg_left hs hP.2.1.le]

/-- The lifted objective's directional derivative. -/
def Dd (P : Two ι Z) (w d : Vr ι Z → ℝ) : ℝ :=
  ∑ i, g0 P (X0 w) i * X0 d i - ∑ i, Y0 d i +
    P.beta * ∑ z, P.q z * (∑ i, g1 P z (X1 w z) i * X1 d z i - ∑ i, Y1 d z i)

/-- Its curvature term. -/
def Nd (P : Two ι Z) (d : Vr ι Z → ℝ) : ℝ :=
  P.gamma / 2 * quad P.S0 (X0 d) + P.beta * ∑ z, P.q z * (P.gamma / 2 * quad (P.S1 z) (X1 d z))

lemma fL_expand {P : Two ι Z} (hP : Hyp P) (w d : Vr ι Z → ℝ) (ε : ℝ) :
    fL P (w + ε • d) = fL P w + ε * Dd P w d - ε ^ 2 * Nd P d := by
  have e0 : X0 (w + ε • d) = X0 w + ε • X0 d := rfl
  have e1 : ∀ z, X1 (w + ε • d) z = X1 w z + ε • X1 d z := fun z => rfl
  have ey0 : ∑ i, Y0 (w + ε • d) i = ∑ i, Y0 w i + ε * ∑ i, Y0 d i := by
    rw [mul_sum, ← sum_add_distrib]; rfl
  have ey1 : ∀ z, ∑ i, Y1 (w + ε • d) z i = ∑ i, Y1 w z i + ε * ∑ i, Y1 d z i := fun z => by
    rw [mul_sum, ← sum_add_distrib]; rfl
  have hz : ∀ z, P.q z * (Q1 P z (X1 (w + ε • d) z) - ∑ i, Y1 (w + ε • d) z i) =
      P.q z * (Q1 P z (X1 w z) - ∑ i, Y1 w z i) +
        ε * (P.q z * (∑ i, g1 P z (X1 w z) i * X1 d z i - ∑ i, Y1 d z i)) -
        ε ^ 2 * (P.q z * (P.gamma / 2 * quad (P.S1 z) (X1 d z))) := fun z => by
    rw [e1, ey1]
    have := Qv_expand (mu := P.mu1 z) (hP.2.2.2.2.2.1 z).1 P.gamma (X1 w z) (X1 d z) ε
    unfold Q1 g1; rw [this]; ring
  unfold fL
  rw [e0, ey0, sum_congr rfl fun z _ => hz z, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  have := Qv_expand (mu := P.mu0) hP.2.2.2.2.1.1 P.gamma (X0 w) (X0 d) ε
  unfold Q0 Dd Nd g0; rw [this]; ring

/-- A supergradient of a function with an exact second-order expansion is its derivative. -/
lemma super_dir {V : Type} [Fintype V] {f : (V → ℝ) → ℝ} {w s : V → ℝ} {D N : (V → ℝ) → ℝ}
    (hsup : ∀ y, f y ≤ f w + s ⬝ᵥ (y - w))
    (hexp : ∀ (ε : ℝ) d, f (w + ε • d) = f w + ε * D d - ε ^ 2 * N d) (hN : ∀ d, 0 ≤ N d)
    (hD : ∀ d, D (-d) = -D d) (d : V → ℝ) : D d = s ⬝ᵥ d := by
  have half : ∀ d, D d - s ⬝ᵥ d ≤ 0 := fun d => by
    refine Novel.M7TwoStageExactnessLossProof.le_of_forall_eps (hN d) fun ε hε => ?_
    have h1 := hsup (w + ε • d)
    rw [hexp, add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at h1
    have h2 : ε * (D d - s ⬝ᵥ d) ≤ ε * (ε * N d) := by nlinarith
    exact le_of_mul_le_mul_left h2 hε
  have h1 := half d
  have h2 := half (-d)
  rw [hD, dotProduct_neg] at h2
  linarith

lemma Dd_neg (P : Two ι Z) (w d : Vr ι Z → ℝ) : Dd P w (-d) = -Dd P w d := by
  have e0 : ∀ i, X0 (-d) i = -X0 d i := fun i => rfl
  have e1 : ∀ z i, X1 (-d) z i = -X1 d z i := fun z i => rfl
  have e2 : ∀ i, Y0 (-d) i = -Y0 d i := fun i => rfl
  have e3 : ∀ z i, Y1 (-d) z i = -Y1 d z i := fun z i => rfl
  have hz : ∀ z, P.q z * (∑ i, g1 P z (X1 w z) i * X1 (-d) z i - ∑ i, Y1 (-d) z i) =
      -(P.q z * (∑ i, g1 P z (X1 w z) i * X1 d z i - ∑ i, Y1 d z i)) := fun z => by
    simp only [e1, e3, mul_neg, sum_neg_distrib]; ring
  unfold Dd
  rw [sum_congr rfl fun z _ => hz z, sum_neg_distrib]
  simp only [e0, e2, mul_neg, sum_neg_distrib]; ring

lemma Nd_nonneg {P : Two ι Z} (hP : Hyp P) (d : Vr ι Z → ℝ) : 0 ≤ Nd P d :=
  add_nonneg (mul_nonneg (by linarith [hP.1]) (hP.2.2.2.2.1.2 _))
    (mul_nonneg hP.2.1.le (sum_nonneg fun z _ => mul_nonneg (hP.2.2.2.2.2.2.1 z).le
      (mul_nonneg (by linarith [hP.1]) ((hP.2.2.2.2.2.1 z).2 _))))

/-- The derivative's value on each coordinate. -/
lemma Dd_x0 (P : Two ι Z) (w : Vr ι Z → ℝ) (j : ι) :
    Dd P w (Pi.single (Sum.inl (Sum.inl j)) 1) = g0 P (X0 w) j := by
  simp [Dd, X0, Y0, X1, Y1, Pi.single_apply]
lemma Dd_y0 (P : Two ι Z) (w : Vr ι Z → ℝ) (j : ι) :
    Dd P w (Pi.single (Sum.inl (Sum.inr j)) 1) = -1 := by
  simp [Dd, X0, Y0, X1, Y1, Pi.single_apply]
lemma Dd_x1 (P : Two ι Z) (w : Vr ι Z → ℝ) (z : Z) (j : ι) :
    Dd P w (Pi.single (Sum.inr (Sum.inl (z, j))) 1) = P.beta * (P.q z * g1 P z (X1 w z) j) := by
  have h1 : ∀ x i, X1 (Pi.single (Sum.inr (Sum.inl (z, j))) (1 : ℝ) : Vr ι Z → ℝ) x i =
      if x = z then (if i = j then 1 else 0) else 0 := fun x i => by
    simp only [X1, Pi.single_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases hx : x = z <;> by_cases hi : i = j <;> simp [hx, hi]
  simp [Dd, X0, Y0, Y1, h1]
lemma Dd_y1 (P : Two ι Z) (w : Vr ι Z → ℝ) (z : Z) (j : ι) :
    Dd P w (Pi.single (Sum.inr (Sum.inr (z, j))) 1) = -(P.beta * P.q z) := by
  have h1 : ∀ x i, Y1 (Pi.single (Sum.inr (Sum.inr (z, j))) (1 : ℝ) : Vr ι Z → ℝ) x i =
      if x = z then (if i = j then 1 else 0) else 0 := fun x i => by
    simp only [Y1, Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
    by_cases hx : x = z <;> by_cases hi : i = j <;> simp [hx, hi]
  simp [Dd, X0, Y0, X1, h1]

end Lifted

/-! ### Part 2: necessity, the multipliers -/

lemma slope_of {kp km ap am A u : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (hap : 0 ≤ ap) (ham : 0 ≤ am)
    (hA : ap + am = A) (hApos : 0 < A) (hup : 0 < u → am * (kp + km) = 0)
    (hdn : u < 0 → ap * (kp + km) = 0) : Slope kp km u ((ap * kp - am * km) / A) := by
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_⟩
  · rw [le_div_iff₀ hApos]; nlinarith [mul_nonneg hap (add_nonneg hkp hkm)]
  · rw [div_le_iff₀ hApos]; nlinarith [mul_nonneg ham (add_nonneg hkp hkm)]
  · rw [div_eq_iff hApos.ne']; nlinarith [hup h]
  · rw [div_eq_iff hApos.ne']; nlinarith [hdn h]

lemma bs_of {xbar x R nu nl c : ℝ} (hc : 0 < c) (hR : c * R = nu - nl) (hnu : 0 ≤ nu) (hnl : 0 ≤ nl)
    (h1 : x < xbar → nu = 0) (h2 : 0 < x → nl = 0) : BoxSign xbar x R := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : c * R ≤ 0 := by rw [hR, h1 h]; linarith
    by_contra hc'; push Not at hc'; nlinarith [mul_pos hc hc']
  · have : 0 ≤ c * R := by rw [hR, h2 h]; linarith
    by_contra hc'; push Not at hc'; nlinarith [mul_pos hc (neg_pos.mpr hc')]

/-- A cost piece's multiplier vanishes after a trade the other way (unless both rates vanish). -/
lemma piece_zero {η u kp km : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km)
    (hsl : 0 < (kp + km) * u → η = 0) (hu : 0 < u) : η * (kp + km) = 0 := by
  rcases (add_nonneg hkp hkm).lt_or_eq with h | h
  · rw [hsl (mul_pos h hu), zero_mul]
  · rw [← h, mul_zero]

open Classical Matrix in
theorem necessary : Necessary := by
  intro hAX ι Z _ _ P hP X ⟨hX, hmax⟩
  have hr := hP.2.2.2.2.2.2.2.2
  have hβ := hP.2.1
  have hq := hP.2.2.2.2.2.2.1
  have hfeas := lift_feas hP hX
  obtain ⟨η, hη0, hsl, hsup⟩ := (hAX (Vr ι Z) (Lc ι Z) (fL P) (cA P) (cB P) (fL_concave hP)
    (liftX P X) hfeas).mp (lift_max hP hmax)
  have key : ∀ d, Dd P (liftX P X) d = (∑ l, η l • cA P l) ⬝ᵥ d :=
    super_dir hsup (fun ε d => fL_expand hP _ d ε) (Nd_nonneg hP) (Dd_neg P _)
  have comp : ∀ v, Dd P (liftX P X) (Pi.single v 1) = ∑ l, η l * cA P l v := fun v => by
    rw [key, dotProduct_single, mul_one, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hx0 : ∀ j, g0 P X.1 j = η (up0 j) - η (lo0 j) + η (cp0 j) * P.kp j - η (cm0 j) * P.km j +
      η bud0 - ∑ z, η (cp1 z j) * (P.kp j * P.g z j) + ∑ z, η (cm1 z j) * (P.km j * P.g z j) +
      ∑ z, η (bud1 z) * (1 - P.g z j) := fun j => by
    have := comp (Sum.inl (Sum.inl j)); rw [Dd_x0, comp_x0] at this; exact this
  have hy0 : ∀ j, (-1 : ℝ) = -η (cp0 j) - η (cm0 j) + η bud0 + ∑ z, η (bud1 z) := fun j => by
    have := comp (Sum.inl (Sum.inr j)); rw [Dd_y0, comp_y0] at this; exact this
  have hx1 : ∀ z j, P.beta * (P.q z * g1 P z (X.2 z) j) = η (up1 z j) - η (lo1 z j) +
      η (cp1 z j) * P.kp j - η (cm1 z j) * P.km j + η (bud1 z) := fun z j => by
    have := comp (Sum.inr (Sum.inl (z, j))); rw [Dd_x1, comp_x1] at this; exact this
  have hy1 : ∀ z j, -(P.beta * P.q z) = -η (cp1 z j) - η (cm1 z j) + η (bud1 z) := fun z j => by
    have := comp (Sum.inr (Sum.inr (z, j))); rw [Dd_y1, comp_y1] at this; exact this
  -- the multipliers
  have hbq : ∀ z, 0 < P.beta * P.q z := fun z => mul_pos hβ (hq z)
  let η1 : Z → ℝ := fun z => η (bud1 z) / (P.beta * P.q z)
  have hη1 : ∀ z, P.beta * P.q z * η1 z = η (bud1 z) := fun z => by
    simp only [η1]; rw [mul_div_cancel₀ _ (hbq z).ne']
  have hη1n : ∀ z, 0 ≤ η1 z := fun z => div_nonneg (hη0 _) (hbq z).le
  have hA1 : ∀ z j, η (cp1 z j) + η (cm1 z j) = P.beta * P.q z * (1 + η1 z) := fun z j => by
    have := hy1 z j; rw [mul_add, mul_one, hη1]; linarith
  have hA1pos : ∀ z, 0 < P.beta * P.q z * (1 + η1 z) :=
    fun z => mul_pos (hbq z) (by linarith [hη1n z])
  let t1 : Z → ι → ℝ := fun z j =>
    (η (cp1 z j) * P.kp j - η (cm1 z j) * P.km j) / (P.beta * P.q z * (1 + η1 z))
  have ht1 : ∀ z j, P.beta * P.q z * (1 + η1 z) * t1 z j = η (cp1 z j) * P.kp j - η (cm1 z j) * P.km j :=
    fun z j => by simp only [t1]; rw [mul_div_assoc', mul_div_cancel_left₀ _ (hA1pos z).ne']
  have hsumE : P.beta * ∑ z, P.q z * η1 z = ∑ z, η (bud1 z) := by
    rw [mul_sum]; exact sum_congr rfl fun z _ => by rw [← mul_assoc, hη1]
  have hA0 : ∀ j, η (cp0 j) + η (cm0 j) = 1 + etaHat P (η bud0) η1 := fun j => by
    have := hy0 j; simp only [etaHat]; rw [hsumE]; linarith
  have he : 0 ≤ etaHat P (η bud0) η1 := etaHat_nonneg hP (hη0 _) hη1n
  let t0 : ι → ℝ := fun j => (η (cp0 j) * P.kp j - η (cm0 j) * P.km j) / (1 + etaHat P (η bud0) η1)
  have ht0 : ∀ j, (1 + etaHat P (η bud0) η1) * t0 j = η (cp0 j) * P.kp j - η (cm0 j) * P.km j :=
    fun j => by simp only [t0]; field_simp
  -- values of the lifted point
  have lx0 : X0 (liftX P X) = X.1 := rfl
  have ly0 : ∀ j, Y0 (liftX P X) j = pc (P.kp j) (P.km j) (X.1 j - P.xm j) := fun j => rfl
  have lx1 : ∀ z j, X1 (liftX P X) z j = X.2 z j := fun z j => rfl
  have ly1 : ∀ z j, Y1 (liftX P X) z j = pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j) :=
    fun z j => rfl
  have pc_pos : ∀ j (u : ℝ), 0 < u → pc (P.kp j) (P.km j) u = P.kp j * u := fun j u hu => by
    simp only [pc]; rw [max_eq_left hu.le, max_eq_right (by linarith)]; ring
  have pc_neg : ∀ j (u : ℝ), u < 0 → pc (P.kp j) (P.km j) u = -P.km j * u := fun j u hu => by
    simp only [pc]; rw [max_eq_right hu.le, max_eq_left (by linarith)]; ring
  refine ⟨η bud0, η1, t0, t1, fun z => ⟨hη1n z, ?_, fun j => ⟨?_, ?_⟩⟩, ⟨hη0 _, ?_, fun j => ⟨?_, ?_⟩⟩⟩
  · -- tomorrow's complementary slackness
    by_cases h0 : η (bud1 z) = 0
    · simp only [η1, h0, zero_div, zero_mul]
    · have ht : cA P (bud1 z) ⬝ᵥ liftX P X = cB P (bud1 z) :=
        le_antisymm (hfeas _) (not_lt.mp fun hlt => h0 (hsl _ hlt))
      rw [d_bud1] at ht
      simp only [cB, bud1, lx0, ly0, lx1, ly1] at ht
      rw [h1_eq]; simp only [ht]; ring
  · -- tomorrow's slopes
    refine slope_of (hr j).1 (hr j).2.1 (hη0 _) (hη0 _) (hA1 z j) (hA1pos z) (fun hu => ?_) (fun hu => ?_)
    · refine piece_zero (hr j).1 (hr j).2.1 (fun hlt => hsl _ ?_) hu
      rw [d_cm1, lx0, lx1, ly1, pc_pos j _ hu]; simp only [cB, cm1, carry] at hlt ⊢; nlinarith
    · have := piece_zero (u := -(X.2 z j - carry P z X.1 j)) (hr j).1 (hr j).2.1
        (fun hlt => hsl (cp1 z j) ?_) (by linarith)
      · exact this
      · rw [d_cp1, lx0, lx1, ly1, pc_neg j _ hu]; simp only [cB, cp1, carry] at hlt ⊢; nlinarith
  · -- tomorrow's box signs
    refine bs_of (hbq z) ?_ (hη0 (up1 z j)) (hη0 (lo1 z j)) (fun h => hsl _ ?_) (fun h => hsl _ ?_)
    · have e := hx1 z j
      have e2 := ht1 z j
      have e3 := hη1 z
      nlinarith
    · rw [d_up1, lx1]; exact h
    · rw [d_lo1, lx1]; simp only [cB, lo1]; linarith
  · -- today's complementary slackness
    by_cases h0 : η bud0 = 0
    · rw [h0, zero_mul]
    · have ht : cA P bud0 ⬝ᵥ liftX P X = cB P bud0 :=
        le_antisymm (hfeas _) (not_lt.mp fun hlt => h0 (hsl _ hlt))
      rw [d_bud0] at ht
      simp only [cB, bud0, lx0, ly0] at ht
      rw [h0_eq, show P.h + ∑ i, P.xm i - ∑ i, X.1 i - ∑ i, pc (P.kp i) (P.km i) (X.1 i - P.xm i) = 0 by
        linarith, mul_zero]
  · -- today's slopes
    refine slope_of (hr j).1 (hr j).2.1 (hη0 _) (hη0 _) (hA0 j) (by linarith) (fun hu => ?_) (fun hu => ?_)
    · refine piece_zero (hr j).1 (hr j).2.1 (fun hlt => hsl _ ?_) hu
      rw [d_cm0, lx0, ly0, pc_pos j _ hu]; simp only [cB, cm0] at hlt ⊢; nlinarith
    · have := piece_zero (u := -(X.1 j - P.xm j)) (hr j).1 (hr j).2.1
        (fun hlt => hsl (cp0 j) ?_) (by linarith)
      · exact this
      · rw [d_cp0, lx0, ly0, pc_neg j _ hu]; simp only [cB, cp0] at hlt ⊢; nlinarith
  · -- today's box signs
    have hS : Sinc P η1 t1 j = ∑ z, η (bud1 z) * P.g z j + ∑ z, η (cp1 z j) * (P.kp j * P.g z j) -
        ∑ z, η (cm1 z j) * (P.km j * P.g z j) := by
      simp only [Sinc, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun z _ => ?_
      have e2 := ht1 z j
      have e3 := hη1 z
      simp only [sval]
      linear_combination P.g z j * e2 + P.g z j * e3
    have hE : ∑ z, η (bud1 z) * (1 - P.g z j) = ∑ z, η (bud1 z) - ∑ z, η (bud1 z) * P.g z j := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun z _ => by ring
    refine bs_of one_pos ?_ (hη0 (up0 j)) (hη0 (lo0 j)) (fun h => hsl _ ?_) (fun h => hsl _ ?_)
    · have e := hx0 j
      have e2 := ht0 j
      rw [hS]
      simp only [etaHat] at e2 ⊢
      rw [hsumE] at e2 ⊢
      linarith
    · rw [d_up0, lx0]; exact h
    · rw [d_lo0, lx0]; simp only [cB, lo0]; linarith

/-! ### Part 3(c) -/

lemma Sinc_zero {P : Two ι Z} {η1 : Z → ℝ} (t1 : Z → ι → ℝ) (h : ∀ z, η1 z = 0) (i : ι) :
    Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * t1 z i := by
  simp [Sinc, sval, h]

lemma eta1_zero {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {η1 : Z → ℝ} {t1 : Z → ι → ℝ}
    (hT : Tomorrow P X η1 t1) (hs : ∀ z, 0 < h1 P X.1 X.2 z) (z : Z) : η1 z = 0 := by
  rcases mul_eq_zero.mp (hT z).2.1 with h | h
  · exact h
  · linarith [hs z]

theorem myopicTest : MyopicTest := by
  intro ι Z _ _ P hP X hM
  have hXF : X ∈ Feas P := ⟨hM.1.1, fun z => (hM.2.2 z).1.1, hM.1.2, fun z => (hM.2.2 z).1.2⟩
  refine ⟨fun hAX => ⟨fun hO => necessary hAX ι Z P hP X hO, fun hL => sufficient ι Z P hP X hXF hL⟩,
    fun i hh hb hc => ?_, fun i hh h0i hci hne η0 η1 t0 t1 hT hR hs => ?_⟩
  · have hfoc := foc hP hM.1 hM.2.1 hh hb hc
    have hxm := (hP.2.2.2.2.2.2.2.2 i).2.2.2.1
    have hres : ∀ (η0 : ℝ) (η1 : Z → ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ), 0 ≤ η0 → η0 * h0 P X.1 = 0 →
        Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) →
        g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i =
          Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i) := by
      intro η0 η1 t0 t1 _ hcs hsl
      have h0 : η0 = 0 := by
        rcases mul_eq_zero.mp hcs with h | h
        · exact h
        · linarith
      rw [hsl.2.2.1 (by linarith), hfoc, etaHat, h0]
      ring
    refine ⟨hfoc, hres, fun η0 η1 t0 t1 hT hR => ?_, fun η1 t1 hT hin => ?_⟩
    · obtain ⟨b1, b2⟩ := (hR.2.2 i).2
      have e := hres η0 η1 t0 t1 hR.1 hR.2.1 (hR.2.2 i).1
      have e1 := b1 hc
      have e2 := b2 (by linarith)
      linarith
    · unfold Sinc
      congr 1
      exact sum_congr rfl fun z _ => by
        rw [(readings ι Z P X η1 t1 hT z i).1 (hin z).1 (hin z).2]
  · have hz := eta1_zero hT hs
    have h0 : η0 = 0 := by
      rcases mul_eq_zero.mp hR.2.1 with h | h
      · exact h
      · linarith
    have he : etaHat P η0 η1 = 0 := by simp [etaHat, h0, hz]
    obtain ⟨hsl, b1, b2⟩ := hR.2.2 i
    have e1 := b1 hci
    have e2 := b2 h0i
    rw [he, Sinc_zero t1 hz] at e1 e2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hf := foc_gen hP hM.1 hM.2.1 hh h0i hci (Or.inr ⟨hlt, rfl⟩)
      rw [hsl.2.2.2 (by linarith), hf] at e1 e2
      linarith
    · have hf := foc_gen hP hM.1 hM.2.1 hh h0i hci (Or.inl ⟨hgt, rfl⟩)
      rw [hsl.2.2.1 (by linarith), hf] at e1 e2
      linarith

theorem pinned : Pinned := by
  intro ι Z _ _ P hP X η1 t1 η1' t1' hT hT' z i hne h0i hci
  have hr := hP.2.2.2.2.2.2.2.2 i
  obtain ⟨⟨-, -, tp, tm⟩, b1, b2⟩ := (hT z).2.2 i
  obtain ⟨⟨-, -, tp', tm'⟩, b1', b2'⟩ := (hT' z).2.2 i
  have e1 := b1 hci; have e2 := b2 h0i; have e1' := b1' hci; have e2' := b2' h0i
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [tm (by linarith)] at e1 e2
    rw [tm' (by linarith)] at e1' e2'
    have : (η1 z - η1' z) * (1 - P.km i) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith [hr.2.2.1]
  · rw [tp (by linarith)] at e1 e2
    rw [tp' (by linarith)] at e1' e2'
    have : (η1 z - η1' z) * (1 + P.kp i) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith [hr.1]

theorem slackTest : SlackTest := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hs
  have hz := eta1_zero hT hs
  have he : etaHat P η0 η1 = η0 := by simp [etaHat, hz]
  have hS := Sinc_zero (P := P) t1 hz
  refine ⟨by simp only [Root, he, hS], fun hR i h0i hci heq => ?_⟩
  obtain ⟨⟨ta, tb, -, -⟩, b1, b2⟩ := hR.2.2 i
  have e1 := b1 hci; have e2 := b2 h0i
  rw [he, hS] at e1 e2
  have h1e : 0 ≤ 1 + η0 := by linarith [hR.1]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ta h1e]
  · nlinarith [mul_le_mul_of_nonneg_left tb h1e]

/-! ### Part 3(c): the two signs -/

/-- Tomorrow's lines give a supergradient of `V_1` in `(x⁻, h⁻)`: the incumbent values and the cash
price. -/
lemma V1_super {P : Two ι Z} (hP : Hyp P) (z : Z) {p : (ι → ℝ) × ℝ} {x1 : ι → ℝ} (hx : x1 ∈ F1 P p)
    {η : ℝ} {t : ι → ℝ} (hη : 0 ≤ η) (hcs : η * cashF P p.2 x1 p.1 = 0)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (x1 i - p.1 i) (t i) ∧
      BoxSign (P.xbar i) (x1 i) (g1 P z x1 i - η - (1 + η) * t i))
    {p' : (ι → ℝ) × ℝ} (hp' : p' ∈ Dom P) :
    V1 P z p' ≤ f1 P z p x1 + ∑ i, (η + (1 + η) * t i) * (p'.1 i - p.1 i) + η * (p'.2 - p.2) := by
  obtain ⟨x, hxF, -, he⟩ := V1_attain P z hp'
  rw [he]
  have hQ : Q1 P z x ≤ Q1 P z x1 + ∑ i, g1 P z x1 i * (x i - x1 i) :=
    Qv_le (hP.2.2.2.2.2.1 z) hP.1.le x1 x
  have hC := cost_ge (P := P) (u := x1 - p.1) (fun i => (hl i).1) (x - p'.1)
  have eC : ∑ i, t i * ((x - p'.1) i - (x1 - p.1) i) =
      ∑ i, t i * (x i - x1 i) - ∑ i, t i * (p'.1 i - p.1 i) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [eC] at hC
  have hbox : ∑ i, (g1 P z x1 i - η - (1 + η) * t i) * (x i - x1 i) ≤ 0 :=
    sum_nonpos fun i _ => bs_le (hl i).2 (hx.1 i).1 (hx.1 i).2 (hxF.1 i).1 (hxF.1 i).2
  rw [sum_line (fun i => g1 P z x1 i)] at hbox
  have hcash := mul_nonneg hη hxF.2
  have es : ∑ i, (η + (1 + η) * t i) * (p'.1 i - p.1 i) =
      η * ∑ i, (p'.1 i - p.1 i) + (1 + η) * ∑ i, t i * (p'.1 i - p.1 i) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  have ed : ∑ i, (x i - p'.1 i) = ∑ i, (x1 i - p.1 i) + ∑ i, (x i - x1 i) - ∑ i, (p'.1 i - p.1 i) := by
    rw [← sum_add_distrib, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  simp only [cashF] at hcs hcash
  rw [ed] at hcash
  rw [es]
  simp only [f1]
  nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 + η)]

lemma update_eq [DecidableEq ι] (x : ι → ℝ) (i : ι) (t : ℝ) :
    Function.update x i (x i + t) = x + t • (Pi.single i 1 : ι → ℝ) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem signs : Signs := by
  intro ι Z _ _ _ P hP X hM η1 t1 hT i hh hb hc
  dsimp only
  set r := Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i) with hr
  have hxm := (hP.2.2.2.2.2.2.2.2 i).2.2.2.1
  have hq := hP.2.2.2.2.2.2.1
  have hfoc := foc hP hM.1 hM.2.1 hh hb hc
  obtain ⟨δ, hδ, hbmp⟩ := bump hP hM.1 hh (by linarith) hc (Or.inl ⟨hb, rfl⟩)
  -- the local bound
  have local_ : ∀ ε, |ε| < δ → RootObj P (X.1 + ε • (Pi.single i 1 : ι → ℝ)) ≤ RootObj P X.1 + ε * r := by
    intro ε hε
    obtain ⟨hf, hcost, hh0, hQ⟩ := hbmp ε hε
    have hz : ∀ z, V1 P z (carry P z (X.1 + ε • (Pi.single i 1 : ι → ℝ)), h0 P (X.1 + ε • (Pi.single i 1 : ι → ℝ))) ≤
        V1 P z (carry P z X.1, h0 P X.1) + ε * (P.g z i * sval η1 t1 z i - η1 z * (1 + P.kp i)) := by
      intro z
      have hx1 : X.2 z ∈ F1 P (carry P z X.1, h0 P X.1) := (hM.2.2 z).1
      have hsup := V1_super hP z hx1 (hT z).1 (hT z).2.1 (hT z).2.2 (dom_mem hP hf z)
      have hsupp := V1_super hP z hx1 (hT z).1 (hT z).2.1 (hT z).2.2 (dom_mem hP hM.1 z)
      have hlow := le_V1 P z (dom_mem hP hM.1 z) hx1
      have ec : ∑ j, (η1 z + (1 + η1 z) * t1 z j) *
          (carry P z (X.1 + ε • (Pi.single i 1 : ι → ℝ)) j - carry P z X.1 j) =
          ε * (P.g z i * sval η1 t1 z i) := by
        rw [sum_eq_single i]
        · simp [carry, sval]; ring
        · intro j _ hj; simp [carry, hj]
        · simp
      simp only [sub_self, mul_zero, sum_const_zero, add_zero] at hsupp
      rw [ec, hh0] at hsup
      simp only at hsup
      rw [hh0]
      nlinarith
    have hs := sum_le_sum fun z (_ : z ∈ univ) => mul_le_mul_of_nonneg_left (hz z) (hq z).le
    have eS : ∑ z, P.q z * (V1 P z (carry P z X.1, h0 P X.1) +
        ε * (P.g z i * sval η1 t1 z i - η1 z * (1 + P.kp i))) =
        ∑ z, P.q z * V1 P z (carry P z X.1, h0 P X.1) +
          ε * (∑ z, P.q z * P.g z i * sval η1 t1 z i - (∑ z, P.q z * η1 z) * (1 + P.kp i)) := by
      rw [sum_mul, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun z _ => by ring
    rw [eS] at hs
    have hSi : Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * sval η1 t1 z i := rfl
    unfold RootObj
    rw [hcost, hQ, hfoc]
    have hgS : 0 ≤ P.gamma / 2 * P.S0 i i := by
      have := hP.2.2.2.2.1.2 (Pi.single i 1)
      exact mul_nonneg (by linarith [hP.1]) (by simpa [quad, Pi.single_apply] using this)
    have er : ε * r = P.beta * (ε * (∑ z, P.q z * P.g z i * sval η1 t1 z i -
        (∑ z, P.q z * η1 z) * (1 + P.kp i))) := by rw [hr, hSi]; ring
    have h2 := mul_nonneg (sq_nonneg ε) hgS
    have h3 := mul_le_mul_of_nonneg_left hs hP.2.1.le
    rw [mul_add] at h3
    linarith
  -- concavity along the line extends it
  have hconc := root_concave hP
  have line : ∀ (σ t : ℝ), 0 < t → X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ) ∈ RootSet P → σ = 1 ∨ σ = -1 →
      RootObj P (X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ)) ≤ RootObj P X.1 + σ * t * r := by
    intro σ t ht hmem hσ
    have hσ2 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    set ε := min t (δ / 2) with hεd
    have hε0 : 0 < ε := lt_min ht (by linarith)
    have hεt : ε ≤ t := min_le_left _ _
    have hεδ : |σ * ε| < δ := by
      rw [abs_mul, hσ2, one_mul, abs_of_pos hε0]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    set lam := ε / t with hlam
    have hl0 : 0 < lam := div_pos hε0 ht
    have hl1 : lam ≤ 1 := (div_le_one ht).mpr hεt
    have hcomb : (1 - lam) • X.1 + lam • (X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ)) =
        X.1 + (σ * ε) • (Pi.single i 1 : ι → ℝ) := by
      have : lam * (σ * t) = σ * ε := by rw [hlam]; field_simp
      ext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((Pi.single i 1 : ι → ℝ) j) * this
    have hc : (1 - lam) • RootObj P X.1 + lam • RootObj P (X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ)) ≤
        RootObj P ((1 - lam) • X.1 + lam • (X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ))) :=
      hconc.2 hM.1 hmem (by linarith) hl0.le (by ring)
    rw [hcomb] at hc
    have hloc := local_ (σ * ε) hεδ
    simp only [smul_eq_mul] at hc
    have : lam * (RootObj P (X.1 + (σ * t) • (Pi.single i 1 : ι → ℝ)) - RootObj P X.1) ≤
        lam * (σ * t * r) := by
      have e : σ * ε * r = lam * (σ * t * r) := by rw [hlam]; field_simp
      nlinarith
    have := le_of_mul_le_mul_left this hl0
    linarith
  intro t ht
  rcases ht.lt_or_eq with htp | rfl
  · refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · rw [update_eq] at hmem ⊢
      have := line 1 t htp (by simpa using hmem) (Or.inl rfl)
      simpa using this
    · rw [show X.1 i - t = X.1 i + -t by ring, update_eq] at hmem ⊢
      have := line (-1) t htp (by simpa using hmem) (Or.inr rfl)
      rw [show (-1 : ℝ) * t = -t by ring] at this
      linarith
  · simp
/-! ### The statement -/

theorem proof : Standalone.M7TwoReviewsBindingBudget.statement :=
  ⟨structure_, sufficient, necessary, readings, slackTomorrow, bounds, myopicTest, pinned, slackTest,
    signs, twoScalar, band, costless⟩

end

end Novel.M7TwoReviewsBindingBudgetProof

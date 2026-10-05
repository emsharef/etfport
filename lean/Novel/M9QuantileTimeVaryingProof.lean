import Standalone.M9QuantileTimeVarying
import Novel.M7QuantileFlexibilityProof

/-!
# Claim 115: proof

2a is claim 049's loss bound at any feasible holding. Today's strong bound keeps the residual
`g_0 - η - (1 + η) t - n` instead of dropping it by the box signs. The relaxed and budgeted tomorrows
are claim 049's lemmas (`relaxed_bound`, `budget_tail`), and claim 111's completed square gives the
residual's form.
-/

namespace Novel.M9QuantileTimeVaryingProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds
  Standalone.M7SeveralFundsReserve Standalone.M7QuantileFlexibility Standalone.M9QuantileTimeVarying
  Novel.M7QuantileFlexibilityProof Matrix

noncomputable section

variable {ι Z : Type} [Fintype ι]

/-! ### 1b -/

theorem splitTest : SplitTest := by
  intro ι Z _ _ P Es muP sig gmin x0 ε
  have e : (Pr P.q fun z => 0 < short P z Es x0) =
      Pr P.q fun z => liqM P z Es x0 - PP P muP sig gmin x0 < Delta P muP sig gmin x0 z :=
    Pr_congr P.q fun z => by
      simp only [short, Delta, lt_max_iff, lt_irrefl, or_false]
      constructor <;> intro h <;> linarith
  rw [e]

theorem stateFreeSplit : StateFreeSplit := by
  intro ι Z _ _ P muP sig gmin x0 L ε hq h1 hε0 hε1
  rw [var_le_iff hq h1 hε0 hε1]
  have hc := Pr_compl P.q fun z => Delta P muP sig gmin x0 z ≤ L - PP P muP sig gmin x0
  rw [h1] at hc
  have e : (Pr P.q fun z => ¬ Delta P muP sig gmin x0 z ≤ L - PP P muP sig gmin x0) =
      Pr P.q fun z => L - PP P muP sig gmin x0 < Delta P muP sig gmin x0 z :=
    Pr_congr P.q fun z => not_le
  rw [e] at hc
  constructor <;> intro h <;> linarith

/-! ### 2a -/

section General

variable [Fintype Z] {P : Two ι Z}

/-- Today's bound at any feasible holding with an admissible `(η, t, n)`: every root-feasible `y` has
`f_0(y) ≤ f_0(x) + Σ_i r_i (y_i - x_i) - (γ/2)(y - x)'Σ_0(y - x)`, with
`r = g_0 - η - (1 + η) t - n`. -/
lemma today_general (hP : Hyp P) {x y : ι → ℝ} {η : ℝ} {t n : ι → ℝ} (hη : 0 ≤ η)
    (hc0 : η * h0 P x = 0) (hx : Box P x) (hy : Box P y) (hhy : 0 ≤ h0 P y)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (x i - P.xm i) (t i) ∧ BoxSign (P.xbar i) (x i) (n i)) :
    Q0 P y - cost P (y - P.xm) ≤ Q0 P x - cost P (x - P.xm) +
      ∑ i, (g0 P x i - η - (1 + η) * t i - n i) * (y i - x i) - P.gamma / 2 * quad P.S0 (y - x) := by
  have hQ := Novel.M7TwoReviewsBindingBudgetProof.Qv_expand (mu := P.mu0) hP.2.2.2.2.1.1 P.gamma x
    (y - x) 1
  rw [one_smul, add_sub_cancel] at hQ
  simp only [one_mul, one_pow, Pi.sub_apply] at hQ
  have hC := Novel.M7TwoReviewsBindingBudgetProof.cost_ge (P := P) (u := x - P.xm) (fun i => (hl i).1)
    (y - P.xm)
  have e1 : ∑ i, t i * ((y - P.xm) i - (x - P.xm) i) = ∑ i, t i * (y i - x i) :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [e1] at hC
  have hn : ∑ i, n i * (y i - x i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Novel.M7TwoReviewsBindingBudgetProof.bs_le (hl i).2 (hx i).1 (hx i).2
      (hy i).1 (hy i).2
  have hsum : ∑ i, (g0 P x i - η - (1 + η) * t i - n i) * (y i - x i) =
      ∑ i, g0 P x i * (y i - x i) - η * ∑ i, (y i - x i) - (1 + η) * ∑ i, t i * (y i - x i) -
        ∑ i, n i * (y i - x i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hh : h0 P y - h0 P x = -∑ i, (y i - x i) - (cost P (y - P.xm) - cost P (x - P.xm)) := by
    simp only [h0]
    have : ∑ i, (y i - P.xm i) - ∑ i, (x i - P.xm i) = ∑ i, (y i - x i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hηy : 0 ≤ η * h0 P y := mul_nonneg hη hhy
  have hmarg : ∑ i, marg P.mu0 P.S0 P.gamma x i * (y i - x i) = ∑ i, g0 P x i * (y i - x i) := rfl
  have hQ0 : ∀ w, Q0 P w = Qv P.mu0 P.S0 P.gamma w := fun w => rfl
  rw [hQ0, hQ0, hQ, hmarg, hsum]
  nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 + η)]

end General

theorem generalBound : GeneralBound := by
  intro ι Z _ _ _ P Es hP hC hSig X0 hX0 η t n η1 t1 xu tu hη hc0 hl0 hT hrel S ρ Xd hXd
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hβ : 0 < P.beta := hP.2.1
  have hγ : 0 < P.gamma := hP.1
  set d := Xd.1 - X0.1 with hd
  have hJ : ∀ X : (ι → ℝ) × (Z → ι → ℝ), J P X = (Q0 P X.1 - cost P (X.1 - P.xm)) +
      P.beta * ∑ z, P.q z * f1 P z (carry P z X.1) (X.2 z) := fun X => rfl
  have h1 := today_general hP hη hc0 hX0.1 hXd.1 hXd.2.2.1 hl0
  have h2 : ∀ z, f1 P z (carry P z Xd.1) (Xd.2 z) ≤
      f1 P z (carry P z X0.1) (xu z) + ∑ i, tu z i * (P.g z i * d i) := fun z => by
    have := relaxed_bound (c := carry P z X0.1) (c' := carry P z Xd.1) hP z (hrel z).1 (hXd.2.1 z)
      (hrel z).2
    convert this using 2
    exact Finset.sum_congr rfl fun i _ => by simp only [carry, hd, Pi.sub_apply]; ring
  have h3 : ∀ z, f1 P z (carry P z X0.1) (xu z) - f1 P z (carry P z X0.1) (X0.2 z) ≤
      etaBar P z * short P z Es X0.1 := fun z => budget_tail hP hC Es hX0 (hT z) (hrel z).1 (hrel z).2
  have hSd : P.beta * ∑ z, P.q z * ∑ i, tu z i * (P.g z i * d i) = S ⬝ᵥ d := by
    simp only [S, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => by ring
  have hρd : ∑ i, (g0 P X0.1 i - η - (1 + η) * t i - n i) * (Xd.1 i - X0.1 i) + S ⬝ᵥ d = ρ ⬝ᵥ d := by
    simp only [ρ, dotProduct, ← Finset.sum_add_distrib, hd, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcsq := Novel.M7IncumbentAwareFirstStageProof.csq hSig hγ ρ d
  rw [← quad_eq] at hcsq
  have hsum2 : ∑ z, P.q z * f1 P z (carry P z Xd.1) (Xd.2 z) ≤
      ∑ z, P.q z * f1 P z (carry P z X0.1) (xu z) + ∑ z, P.q z * ∑ i, tu z i * (P.g z i * d i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (h2 z) (hq z).le
  have hsum3 : ∑ z, P.q z * f1 P z (carry P z X0.1) (xu z) ≤
      ∑ z, P.q z * f1 P z (carry P z X0.1) (X0.2 z) + ∑ z, P.q z * (etaBar P z * short P z Es X0.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [h3 z]) (hq z).le
  rw [hJ, hJ]
  have hb2 := mul_le_mul_of_nonneg_left hsum2 hβ.le
  have hb3 := mul_le_mul_of_nonneg_left hsum3 hβ.le
  rw [mul_add] at hb2 hb3
  nlinarith

theorem frontLoaded : FrontLoaded := by
  intro ι Z _ _ _ P Es hP hC hSig X0 hX0 η t n η1 t1 xu tu hη hc0 hl0 hT hrel hzero Xd hXd
  have h := generalBound ι Z P Es hP hC hSig X0 hX0 η t n η1 t1 xu tu hη hc0 hl0 hT hrel Xd hXd
  have hρ : (fun i => g0 P X0.1 i + P.beta * ∑ z, P.q z * (P.g z i * tu z i) - η - (1 + η) * t i - n i) =
      0 := funext hzero
  simp only [hρ, mulVec_zero, dotProduct_zero, zero_div, add_zero] at h
  exact h

/-! ### Part 3 -/

theorem pinnedS : PinnedS := by
  intro ι Z _ _ P x0 xu tu i hsl hb
  have ht : ∀ z, tu z i = P.kp i := fun z => (hsl z).2.2.1 (by linarith [hb z])
  simp only [ht, Finset.sum_mul, mul_assoc]

theorem blockInverse : BlockInverse := by
  intro M hsym h11 hdet
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Ring.inverse_eq_inv']
  rw [Matrix.det_fin_two] at hdet ⊢
  rw [hsym] at hdet ⊢
  field_simp

theorem proof : Standalone.M9QuantileTimeVarying.statement :=
  ⟨splitTest, stateFreeSplit, generalBound, frontLoaded, pinnedS, blockInverse⟩

end

end Novel.M9QuantileTimeVaryingProof

import Novel.M5PlugInValueLossProof
import Standalone.M5ReestimationGuarantee

/-!
# Claim 035: proof

Part 2 is claim 033's normalization: `W K W⁻¹ = (I + R)⁻¹` with `R ⪰ 0` for any positive
semidefinite estimate, and the backward bounds on `W⁻¹C_s` and `W⁻¹c_s`. The position bound
follows by induction. Parts 3-4 combine claim 033's pathwise inequalities with either the a priori
bounds (off the event) or claim 033's guarantee at the radius (on it).
-/

namespace Novel.M5ReestimationGuaranteeProof

open Matrix Standalone.M5PartialAdjustmentSplit Standalone.M5PlugInValueLoss
open Standalone.M5ReestimationGuarantee Novel.M5PlugInValueLossProof
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option linter.unusedSectionVars false

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]

/-- Part 2 for one estimate path. -/
lemma apriori_one {Q : LQ ι π} {S' : ℕ → Matrix ι ι ℝ} {W : Matrix ι ι ℝ} {G : Matrix ι π ℝ}
    (hL : Q.Lam.PosDef) (hS' : ∀ s, (S' s).PosSemidef) (hr : 0 ≤ Q.rho) (hr1 : Q.rho ≤ 1)
    (hG : ∀ t, Q.G t = G) (hWs : Wᵀ = W) (hWW : W * W = Q.Lam) (hWu : IsUnit W) {t : ℕ}
    (ht : t < Q.T) :
    ‖W * (plugIn Q S').K t * W⁻¹‖ ≤ 1 ∧
    ‖W * (plugIn Q S').L t‖ ≤ ((Q.T - t : ℕ) : ℝ) * ‖W⁻¹ * G‖ ∧
    vnorm (W *ᵥ (plugIn Q S').l t) ≤ ((Q.T - t : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ Q.e) := by
  set Q' := plugIn Q S'
  have hWW' : W * W = Q'.Lam := hWW
  have hL' : Q'.Lam.PosDef := hL
  have hr' : 0 ≤ Q'.rho := hr
  have hr1' : Q'.rho ≤ 1 := hr1
  have hG' : ∀ t, Q'.G t = G := hG
  have ht' : t < Q'.T := ht
  refine ⟨?_, ?_, ?_⟩
  · rw [K_eq hWs hWW' hWu]
    exact inv_norm_le (R_psd hWs hWW' hWu hL' hS' hr' t)
  · rw [← C_eq hWs hWW' hWu ht']
    exact C_bound hWs hWW' hWu hL' hS' hr' hG' hr1' t
  · rw [← c_eq hWs hWW' hWu ht']
    exact c_bound hWs hWW' hWu hL' hS' hr' hr1' t

/-- The true coefficients satisfy the same bounds. -/
lemma plugIn_self (Q : LQ ι π) : plugIn Q Q.S = Q := rfl

lemma apriori_diff {Q : LQ ι π} {S' : ℕ → Matrix ι ι ℝ} {W : Matrix ι ι ℝ} {G : Matrix ι π ℝ}
    (hL : Q.Lam.PosDef) (hS : ∀ s, (Q.S s).PosSemidef) (hS' : ∀ s, (S' s).PosSemidef)
    (hr : 0 ≤ Q.rho) (hr1 : Q.rho ≤ 1) (hG : ∀ t, Q.G t = G) (hWs : Wᵀ = W) (hWW : W * W = Q.Lam)
    (hWu : IsUnit W) {t : ℕ} (ht : t < Q.T) :
    ‖W * ((plugIn Q S').K t - Q.K t) * W⁻¹‖ ≤ 2 ∧
    ‖W * ((plugIn Q S').L t - Q.L t)‖ ≤ 2 * ((Q.T - t : ℕ) : ℝ) * ‖W⁻¹ * G‖ ∧
    vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) ≤ 2 * ((Q.T - t : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ Q.e) := by
  obtain ⟨k1, l1, c1⟩ := apriori_one hL hS' hr hr1 hG hWs hWW hWu ht
  obtain ⟨k2, l2, c2⟩ := apriori_one (S' := Q.S) hL hS hr hr1 hG hWs hWW hWu ht
  rw [plugIn_self] at k2 l2 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.sub_mul]
    linarith [norm_sub_le (W * (plugIn Q S').K t * W⁻¹) (W * Q.K t * W⁻¹)]
  · rw [Matrix.mul_sub]
    linarith [norm_sub_le (W * (plugIn Q S').L t) (W * Q.L t)]
  · rw [mulVec_sub]
    linarith [vnorm_sub (W *ᵥ (plugIn Q S').l t) (W *ᵥ Q.l t)]

theorem apriori : APriori := by
  intro ι π _ _ _ _ Q S' W G hH t ht
  obtain ⟨hL, hS, hS', hr, hr1, hG, hWs, hWW, hWu⟩ := hH
  exact ⟨(apriori_one hL (hS' 0) hr hr1 hG hWs hWW hWu ht).1,
    (apriori_one hL (hS' 0) hr hr1 hG hWs hWW hWu ht).2.1,
    (apriori_one hL (hS' 0) hr hr1 hG hWs hWW hWu ht).2.2,
    apriori_diff hL hS (hS' 0) hr hr1 hG hWs hWW hWu ht⟩

/-- `r + ρ Σ_{j < T-(s+1)} ρ^j r = bR_s(r)` below the horizon. -/
lemma bR_eq {T s : ℕ} (hs : s < T) (rho r : ℝ) :
    r + rho * ∑ j ∈ Finset.range (T - (s + 1)), rho ^ j * r = bR T rho r s := by
  rw [bR, show T - s = (T - (s + 1)) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem reestimation : Reestimation := by
  intro ι π _ _ _ _ Q S' W G m Mst x hH hm hx
  obtain ⟨hL, hS, hS', hr, hr1, hG, hWs, hWW, hWu⟩ := hH
  intro g e X
  have hM0 : 0 ≤ Mst := (vnorm_nonneg _).trans (hm 0)
  have hg0 : 0 ≤ g := norm_nonneg _
  have he0 : 0 ≤ e := vnorm_nonneg _
  have hpos : ∀ t, t ≤ Q.T → vnorm (W *ᵥ x t) ≤ X t := by
    intro t
    induction t with
    | zero => intro _; simp [X, Xb]
    | succ t ih =>
      intro ht
      have ht' : t < Q.T := by omega
      obtain ⟨k1, l1, c1⟩ := apriori_one (S' := S' t) hL (hS' t) hr hr1 hG hWs hWW hWu ht'
      have hWi := wiw hWs hWW hWu
      have e2 : W *ᵥ x (t + 1) = (W * (plugIn Q (S' t)).K t * W⁻¹) *ᵥ (W *ᵥ x t) +
          (W * (plugIn Q (S' t)).L t) *ᵥ m t + W *ᵥ (plugIn Q (S' t)).l t := by
        rw [hx, LQ.policy, mulVec_add, mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
          Matrix.mul_assoc (W * _), hWi, Matrix.mul_one]
      rw [e2]
      have b1 := (mulVec_le (W * (plugIn Q (S' t)).K t * W⁻¹) (W *ᵥ x t)).trans
        (mul_le_mul k1 (ih (by omega)) (vnorm_nonneg _) zero_le_one)
      have b2 := (mulVec_le (W * (plugIn Q (S' t)).L t) (m t)).trans
        (mul_le_mul l1 (hm t) (vnorm_nonneg _) (by positivity))
      have hX : X (t + 1) = X t + (((Q.T - t : ℕ) : ℝ) * g * Mst + ((Q.T - t : ℕ) : ℝ) * e) := by
        simp only [X, Xb, Finset.sum_range_succ]; ring
      rw [hX]
      refine (vnorm_add _ _).trans ?_
      have := vnorm_add ((W * (plugIn Q (S' t)).K t * W⁻¹) *ᵥ (W *ᵥ x t))
        ((W * (plugIn Q (S' t)).L t) *ᵥ m t)
      nlinarith
  refine ⟨hpos, fun t ht => ?_⟩
  intro err Rt
  obtain ⟨hdiff, hDe, hWe, hDR⟩ := pathwise ι π Q (S' t) W hWs hWW hWu t (x t) (m t)
  have herr : err = (plugIn Q (S' t)).policy t (x t) (m t) - Q.policy t (x t) (m t) := by
    simp only [err, hx]
  have hX := hpos t ht.le
  have hquad : ∀ B : ℝ, vnorm (W *ᵥ err) ≤ B →
      1 / 2 * (err ⬝ᵥ (Q.D t *ᵥ err)) ≤ 1 / 2 * (1 + Rt) * B ^ 2 := fun B hB => by
    have h1 := hDe err
    have h0 : 0 ≤ ‖W⁻¹ * Q.D t * W⁻¹‖ := norm_nonneg _
    have h2 : vnorm (W *ᵥ err) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (vnorm_nonneg _) hB 2
    have h3 : ‖W⁻¹ * Q.D t * W⁻¹‖ * vnorm (W *ᵥ err) ^ 2 ≤ (1 + Rt) * B ^ 2 :=
      mul_le_mul hDR h2 (sq_nonneg _) (h0.trans hDR)
    linarith
  rw [herr] at hquad ⊢
  refine ⟨hquad _ (hWe.trans ?_), fun r hdr => hquad _ (hWe.trans ?_)⟩
  · obtain ⟨d1, d2, d3⟩ := apriori_diff hL hS (hS' t) hr hr1 hG hWs hWW hWu ht
    have := mul_le_mul d1 hX (vnorm_nonneg _) (by norm_num)
    have := mul_le_mul d2 (hm t) (vnorm_nonneg _) (by positivity)
    linarith
  · obtain ⟨-, d1, d2, d3⟩ := guarantee ι π Q (S' t) W G r hL hS (hS' t) hr hr1 hG hWs hWW hWu hdr
    have e1 := d1 t ht
    rw [bR_eq ht] at e1
    have e2 : ‖W * ((plugIn Q (S' t)).L t - Q.L t)‖ ≤ bL Q.T Q.rho r g t :=
      (d2 t ht).trans (le_of_eq (Finset.sum_congr rfl fun k hk => by
        rw [bR_eq (by simp at hk; omega)]))
    have e3 : vnorm (W *ᵥ ((plugIn Q (S' t)).l t - Q.l t)) ≤ bL Q.T Q.rho r e t :=
      (d3 t ht).trans (le_of_eq (Finset.sum_congr rfl fun k hk => by
        rw [bR_eq (by simp at hk; omega)]))
    have := mul_le_mul e1 hX (vnorm_nonneg _) ((norm_nonneg _).trans e1)
    have := mul_le_mul e2 (hm t) (vnorm_nonneg _) ((norm_nonneg _).trans e2)
    linarith

/-- Claim 035, parts 2-4 (pathwise). -/
theorem proof : Standalone.M5ReestimationGuarantee.statement := ⟨apriori, reestimation⟩

end

end Novel.M5ReestimationGuaranteeProof

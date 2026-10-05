import Novel.M2NoActiveTradeBandProof
import Novel.M2TwoStageSeparationProof
import Novel.M2SoftTargetTwoStageProof
import Novel.M6QuarterlyBandStaticCeilingProof
import Novel.M5PartialAdjustmentSplitProof
import Novel.M5MissingDirectionLeakProof
import Novel.M5LearningAimTwoSpeedsProof
import Novel.M5PlugInValueLossProof
import Novel.M5PlugInLossInputsProof
import Novel.M5ReestimationGuaranteeProof
import Novel.M5WhenAnticipationMattersProof
import Novel.M7LearningBandTransferProof
import Standalone.IntegrationTheorem

/-!
# Claim 038: proof

- The tracking identity completes the square around `x* = (γΣ)⁻¹μ`.
- A3: the constant-state scalar filter adds `1/σ²` to the precision at each review.
- B3: claim 036's exact form bounds each cumulative drift termwise by A3. Claim 036's weights are
  nonnegative, sum to one and concentrate at `s = t` as `λ_A → 0`.
- C1 telescopes the value along the policy's state law.
- C3's M7 bounds are elementary estimates on the box, using the 1-Lipschitz clip.
- D completes the square with `Λ + γΣ`.
-/

namespace Novel.IntegrationTheoremProof

open Filter Topology Matrix Standalone.IntegrationTheorem Standalone.M5WhenAnticipationMatters

noncomputable section

/-! ### Part 0 -/

theorem tracking : Tracking := by
  intro n Sg γ mu x hSg hγ
  have hU := Novel.M5PartialAdjustmentSplitProof.pd_unit hSg
  have hsym : Sgᵀ = Sg := Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hSg.posSemidef
  rw [Novel.M5MissingDirectionLeakProof.inv_gsmul hγ.ne' hU]
  set y := (γ⁻¹ • Sg⁻¹) *ᵥ mu with hy
  have h1 : Sg *ᵥ y = γ⁻¹ • mu := by
    rw [hy, smul_mulVec, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hxy : x ⬝ᵥ (Sg *ᵥ y) = γ⁻¹ * (x ⬝ᵥ mu) := by rw [h1, dotProduct_smul, smul_eq_mul]
  have hyx : y ⬝ᵥ (Sg *ᵥ x) = γ⁻¹ * (x ⬝ᵥ mu) := by
    rw [← Novel.M5PartialAdjustmentSplitProof.sym_dot hsym x y, hxy]
  have hyy : y ⬝ᵥ (Sg *ᵥ y) = γ⁻¹ * γ⁻¹ * (mu ⬝ᵥ (Sg⁻¹ *ᵥ mu)) := by
    rw [h1, dotProduct_smul, smul_eq_mul, hy, smul_mulVec, smul_dotProduct, smul_eq_mul,
      dotProduct_comm]
    ring
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hxy, hyx, hyy, dotProduct_comm mu x]
  field_simp
  ring

/-! ### A3 -/

lemma kal_inv {sig2 : ℝ} {p : ℕ → ℝ} (hs : 0 < sig2) (hp : ∀ s, 0 < p s)
    (hk : ∀ s, p (s + 1) = p s * sig2 / (sig2 + p s)) (t : ℕ) :
    ∀ k : ℕ, 1 / p (t + k) = 1 / p t + k / sig2 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hk, Nat.cast_succ]
    have h1 := hp (t + k)
    field_simp
    field_simp at ih
    nlinarith [ih]

theorem kalmanDrift : KalmanDrift := by
  intro sig2 p hs hp hk t k kap
  have hpt := hp t
  have hpk := hp (t + k)
  have hp1 := hp (t + 1)
  have hinv := kal_inv hs hp hk t k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd1 : 0 < sig2 + p (t + k) := by linarith
  have hd2 : 0 < sig2 + p (t + 1) := by linarith
  -- `p_{t+k}(σ² + k p_t) = p_t σ²`
  have hq : p (t + k) * (sig2 + k * p t) = p t * sig2 := by
    field_simp at hinv; nlinarith [hinv]
  have h1k : 1 - kap = sig2 / (sig2 + p t) := by simp only [kap]; field_simp; ring
  have hkap : kap / (1 - kap) = p t / sig2 := by
    rw [h1k]; simp only [kap]; field_simp
  have h1 : p t - p (t + 1) = p t * kap := by
    simp only [kap]; rw [hk]; field_simp; ring
  refine ⟨hinv, by rw [div_sub_one hd1.ne']; ring_nf, ?_, h1, ?_, ?_⟩
  · have hD : (p t - p (t + k)) * (sig2 + k * p t) = k * p t ^ 2 := by nlinarith [hq]
    have hD0 : 0 ≤ p t - p (t + k) := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg hk0 (sq_nonneg (p t)), mul_nonneg hk0 hpt.le]
    have key : (p t - p (t + k)) * sig2 ^ 2 ≤ k * p t ^ 2 * (sig2 + p (t + k)) := by
      nlinarith [mul_nonneg hD0 (mul_nonneg hk0 hpt.le), mul_nonneg (mul_nonneg hk0 (sq_nonneg (p t))) hpk.le,
        mul_nonneg (mul_nonneg hD0 (mul_nonneg hk0 hpt.le)) hs.le]
    rw [hkap, div_pow, div_le_iff₀ hd1,
      show (k : ℝ) * (p t ^ 2 / sig2 ^ 2) * (sig2 + p (t + k)) = k * p t ^ 2 * (sig2 + p (t + k)) / sig2 ^ 2 by
        ring, le_div_iff₀ (by positivity)]
    exact key
  · rw [div_sub_one hd2.ne']
    congr 1
    rw [mul_comm kap]; linarith [h1]
  · rw [hkap]
    have hkp : kap ≤ p t / sig2 := div_le_div_of_nonneg_left hpt.le hs (by linarith)
    have hkap0 : 0 ≤ kap := div_nonneg hpt.le (by linarith)
    calc kap * p t / (sig2 + p (t + 1)) ≤ kap * p t / sig2 :=
          div_le_div_of_nonneg_left (mul_nonneg hkap0 hpt.le) hs (by linarith)
      _ ≤ p t / sig2 * p t / sig2 := by
          gcongr
      _ = (p t / sig2) ^ 2 := by ring

/-! ### B3 -/

theorem anticipationOrder : AnticipationOrder := by
  intro B hB hk t ht
  have hs := hB.2.2.1
  have hp := hB.2.2.2.2.2
  have hanti : StrictAnti B.p := strictAnti_nat_of_succ_lt fun s => by
    rw [hk]
    have := hp s
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨-, hL1, -, -, hexact, hstrict, -⟩ :=
    Novel.M5WhenAnticipationMattersProof.learningAim B hB hanti.antitone t ht
  have hw0 := Novel.M5WhenAnticipationMattersProof.w_nonneg hB
  have hwsum := Novel.M5WhenAnticipationMattersProof.w_sum hB t ht
  have hbound : B.L t - 1 ≤ (B.kap t / (1 - B.kap t)) ^ 2 * Dur B t := by
    rw [hexact, Dur, Finset.mul_sum]
    calc ∑ k ∈ Finset.Ico 1 (B.T - t), B.w k t * ((B.p t - B.p (t + k)) / (B.sig2 + B.p (t + k)))
        ≤ ∑ k ∈ Finset.Ico 1 (B.T - t), (B.kap t / (1 - B.kap t)) ^ 2 * (B.w k t * k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have := (kalmanDrift B.sig2 B.p hs hp hk t k).2.2.1
          have hkap : B.kap t = B.p t / (B.sig2 + B.p t) := rfl
          rw [hkap]
          nlinarith [mul_le_mul_of_nonneg_left this (hw0 k t)]
      _ ≤ ∑ k ∈ Finset.range (B.T - t), (B.kap t / (1 - B.kap t)) ^ 2 * (B.w k t * k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk'; simp only [Finset.mem_Ico, Finset.mem_range] at hk' ⊢; exact hk'.2
          · intro k _ _; exact mul_nonneg (sq_nonneg _) (mul_nonneg (hw0 k t) (Nat.cast_nonneg k))
  have hDur0 : 0 ≤ Dur B t := Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k t) (Nat.cast_nonneg k)
  refine ⟨hbound, fun h => ?_, hDur0, ?_, ?_, fun θ hθ => hθ.trans hbound⟩
  · have hne : B.L t ≠ 1 := fun h1 => by have := (hstrict hanti).mp h1; omega
    exact sub_pos.mpr (lt_of_le_of_ne hL1 (Ne.symm hne))
  · have hT : ((B.T - t : ℕ) : ℝ) - 1 = ∑ k ∈ Finset.range (B.T - t), B.w k t * (((B.T - t : ℕ) : ℝ) - 1) := by
      rw [← Finset.sum_mul, hwsum, one_mul]
    rw [hT, Dur]
    refine Finset.sum_le_sum fun k hk' => mul_le_mul_of_nonneg_left ?_ (hw0 k t)
    have := Finset.mem_range.mp hk'
    have : (k : ℝ) + 1 ≤ ((B.T - t : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  · have hlim : Tendsto (fun lam => Dur (B.withLam lam) t) (𝓝[>] 0)
        (𝓝 (∑ k ∈ Finset.range (B.T - t), (if k = 0 then (1 : ℝ) else 0) * k)) := by
      unfold Dur
      simp only [Novel.M5WhenAnticipationMattersProof.bl_T]
      exact tendsto_finsetSum _ fun k _ =>
        (Novel.M5WhenAnticipationMattersProof.zlim_w hB k t).mul tendsto_const_nhds
    have h0 : ∑ k ∈ Finset.range (B.T - t), (if k = 0 then (1 : ℝ) else 0) * k = 0 :=
      Finset.sum_eq_zero fun k _ => by by_cases h : k = 0 <;> simp [h]
    rwa [h0] at hlim

/-! ### C1 -/

section C1

variable {Z X : Type} [Fintype Z] (Q : FDP Z X)

lemma push (J : ℕ → Z → ℝ) (pol : ℕ → Z → X) (mu0 : Z → ℝ) (t : ℕ) :
    ∑ z, Q.law pol mu0 t z * ∑ z', Q.P t z (pol t z) z' * J (t + 1) z' =
      ∑ z', Q.law pol mu0 (t + 1) z' * J (t + 1) z' := by
  have e : ∀ z', Q.law pol mu0 (t + 1) z' = ∑ z, Q.law pol mu0 t z * Q.P t z (pol t z) z' :=
    fun z' => rfl
  simp only [e, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma telesc (A R : ℕ → ℝ) (ρ : ℝ) : ∀ N, ∑ t ∈ Finset.range N, ρ ^ t * (A t - R t - ρ * A (t + 1)) =
    A 0 - ρ ^ N * A N - ∑ t ∈ Finset.range N, ρ ^ t * R t := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

omit [Fintype Z] in
lemma H_succ {t : ℕ} (ht : t < Q.T) : Q.H t = 1 + Q.rho * Q.H (t + 1) := by
  simp only [FDP.H]
  rw [show Q.T - t = (Q.T - (t + 1)) + 1 by omega, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
lemma H_T : Q.H Q.T = 0 := by simp [FDP.H]

theorem residualIdentity : ResidualIdentity := by
  intro Z X _ Q J pol mu0 hB hpol
  obtain ⟨hJT, hBell⟩ := hB
  set A : ℕ → ℝ := fun t => ∑ z, Q.law pol mu0 t z * J t z with hA
  set R : ℕ → ℝ := fun t => ∑ z, Q.law pol mu0 t z * Q.r t z (pol t z) with hR
  have hrow : ∀ t, ∑ z, Q.law pol mu0 t z * Q.resid J pol t z = A t - R t - Q.rho * A (t + 1) := by
    intro t
    have e : ∀ z, Q.law pol mu0 t z * Q.resid J pol t z = Q.law pol mu0 t z * J t z -
        Q.law pol mu0 t z * Q.r t z (pol t z) -
        Q.rho * (Q.law pol mu0 t z * ∑ z', Q.P t z (pol t z) z' * J (t + 1) z') := fun z => by
      simp only [FDP.resid]; ring
    rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, push Q J pol mu0 t]
  have hAT : A Q.T = 0 := by simp only [hA, hJT, mul_zero, Finset.sum_const_zero]
  refine ⟨?_, fun t z ht => ?_, fun c hc hP0 hP1 hρ0 hρ1 => ?_⟩
  · simp only [hrow, FDP.value]
    rw [telesc A R Q.rho Q.T, hAT, mul_zero, sub_zero]
    rfl
  · have := (hBell t ht z).1 (pol t z) (hpol t z ht)
    simp only [FDP.resid]; linarith
  · -- `|Σ P J| ≤ c H` from the bound on `J`
    have hsum : ∀ t z x, (∀ z', |J (t + 1) z'| ≤ c * Q.H (t + 1)) →
        |∑ z', Q.P t z x z' * J (t + 1) z'| ≤ c * Q.H (t + 1) := by
      intro t z x h
      calc |∑ z', Q.P t z x z' * J (t + 1) z'| ≤ ∑ z', |Q.P t z x z' * J (t + 1) z'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z', Q.P t z x z' * (c * Q.H (t + 1)) := Finset.sum_le_sum fun z' _ => by
            rw [abs_mul, abs_of_nonneg (hP0 t z x z')]
            exact mul_le_mul_of_nonneg_left (h z') (hP0 t z x z')
        _ = c * Q.H (t + 1) := by rw [← Finset.sum_mul, hP1, one_mul]
    have hJ : ∀ m t z, Q.T - t = m → t ≤ Q.T → |J t z| ≤ c * Q.H t := by
      intro m
      induction m with
      | zero =>
        intro t z hm ht
        have : t = Q.T := by omega
        subst this; rw [hJT, H_T, abs_zero, mul_zero]
      | succ m ih =>
        intro t z hm ht
        have htT : t < Q.T := by omega
        have hnext := hsum t z
        have hIH : ∀ z', |J (t + 1) z'| ≤ c * Q.H (t + 1) := fun z' => ih (t + 1) z' (by omega) (by omega)
        obtain ⟨x, hx, heq⟩ := (hBell t htT z).2
        have hr := abs_le.mp (hc t z x htT hx)
        have hs := abs_le.mp (hnext x hIH)
        rw [H_succ Q htT, ← heq, abs_le]
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hs.1 hρ0, mul_le_mul_of_nonneg_left hs.2 hρ0]
    refine ⟨fun t z ht => hJ (Q.T - t) t z rfl ht, fun t z ht => ?_⟩
    have hIH : ∀ z', |J (t + 1) z'| ≤ c * Q.H (t + 1) := fun z' => hJ _ (t + 1) z' rfl (by omega)
    have h1 := abs_le.mp (hJ _ t z rfl ht.le)
    have h2 := abs_le.mp (hc t z (pol t z) ht (hpol t z ht))
    have h3 := abs_le.mp (hsum t z (pol t z) hIH)
    simp only [FDP.resid]
    rw [H_succ Q ht] at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h3.1 hρ0]

end C1

/-! ### C3's M7 devices -/

lemma cost_lip {kp km xm a b : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) :
    |(kp * max (a - xm) 0 + km * max (xm - a) 0) - (kp * max (b - xm) 0 + km * max (xm - b) 0)| ≤
      max kp km * |a - b| := by
  have m1 := le_max_left kp km
  have m2 := le_max_right kp km
  rcases le_total a xm with ha | ha <;> rcases le_total b xm with hb | hb
  · rw [max_eq_right (by linarith : a - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - a),
      max_eq_right (by linarith : b - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - b)]
    rw [show kp * 0 + km * (xm - a) - (kp * 0 + km * (xm - b)) = km * (b - a) by ring, abs_mul,
      abs_of_nonneg hkm, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right m2 (abs_nonneg _)
  · rw [max_eq_right (by linarith : a - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - a),
      max_eq_left (by linarith : 0 ≤ b - xm), max_eq_right (by linarith : xm - b ≤ 0), abs_le,
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right m1 (by linarith : 0 ≤ b - xm),
      mul_le_mul_of_nonneg_right m2 (by linarith : 0 ≤ xm - a), mul_nonneg hkp (by linarith : 0 ≤ b - xm),
      mul_nonneg hkm (by linarith : (0 : ℝ) ≤ xm - a)]
  · rw [max_eq_left (by linarith : 0 ≤ a - xm), max_eq_right (by linarith : xm - a ≤ 0),
      max_eq_right (by linarith : b - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - b), abs_le,
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right m1 (by linarith : 0 ≤ a - xm),
      mul_le_mul_of_nonneg_right m2 (by linarith : 0 ≤ xm - b), mul_nonneg hkp (by linarith : 0 ≤ a - xm),
      mul_nonneg hkm (by linarith : (0 : ℝ) ≤ xm - b)]
  · rw [max_eq_left (by linarith : 0 ≤ a - xm), max_eq_right (by linarith : xm - a ≤ 0),
      max_eq_left (by linarith : 0 ≤ b - xm), max_eq_right (by linarith : xm - b ≤ 0)]
    rw [show kp * (a - xm) + km * 0 - (kp * (b - xm) + km * 0) = kp * (a - b) by ring, abs_mul,
      abs_of_nonneg hkp]
    exact mul_le_mul_of_nonneg_right m1 (abs_nonneg _)

theorem capBound : CapBound := by
  intro n Sg γ σ mu kp km xbar xm x hpsd hσ hγ hx
  have h1 : |mu ⬝ᵥ x| ≤ ∑ i, |mu i| * xbar i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (hx i).2.2.2.1]
    exact mul_le_mul_of_nonneg_left (hx i).2.2.2.2 (abs_nonneg _)
  have hxx : x ⬝ᵥ x ≤ xbar ⬝ᵥ xbar := Finset.sum_le_sum fun i _ => by
    have := hx i; nlinarith [this.2.2.2.1, this.2.2.2.2]
  have hq0 := hpsd x
  have h2 : x ⬝ᵥ (Sg *ᵥ x) ≤ σ * (xbar ⬝ᵥ xbar) := by
    by_cases h0 : xbar ⬝ᵥ xbar = 0
    · have hx0 : x ⬝ᵥ x = 0 := le_antisymm (h0 ▸ hxx) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      have := hσ x; rw [hx0, mul_zero] at this; rw [h0, mul_zero]; exact this
    · have hpos : 0 < xbar ⬝ᵥ xbar :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm h0)
      have hσ0 : 0 ≤ σ := by
        have := (hpsd xbar).trans (hσ xbar); exact nonneg_of_mul_nonneg_left this hpos
      exact (hσ x).trans (mul_le_mul_of_nonneg_left hxx hσ0)
  have h3 : ∀ i, 0 ≤ kp i * max (x i - xm i) 0 + km i * max (xm i - x i) 0 ∧
      kp i * max (x i - xm i) 0 + km i * max (xm i - x i) 0 ≤ (kp i + km i) * max (xbar i) (xm i) := by
    intro i
    obtain ⟨hkp, hkm, hxm, hx0, hxb⟩ := hx i
    have a1 : max (x i - xm i) 0 ≤ max (xbar i) (xm i) :=
      max_le (by linarith [le_max_left (xbar i) (xm i)]) (le_trans hxm (le_max_right _ _))
    have a2 : max (xm i - x i) 0 ≤ max (xbar i) (xm i) :=
      max_le (by linarith [le_max_right (xbar i) (xm i)]) (le_trans hxm (le_max_right _ _))
    constructor
    · exact add_nonneg (mul_nonneg hkp (le_max_right _ _)) (mul_nonneg hkm (le_max_right _ _))
    · nlinarith [mul_le_mul_of_nonneg_left a1 hkp, mul_le_mul_of_nonneg_left a2 hkm]
  have hc0 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (h3 i).1
  have hc1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h3 i).2
  have hγq := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ γ / 2)
  have hγq0 := mul_nonneg (by positivity : 0 ≤ γ / 2) hq0
  rw [abs_le]
  constructor
  · have := neg_abs_le (mu ⬝ᵥ x); nlinarith
  · have := le_abs_self (mu ⬝ᵥ x); nlinarith

lemma clip_lip_v (v v' a b : ℝ) : |clip v a b - clip v' a b| ≤ |v - v'| := by
  simp only [clip]
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]

lemma clip_lip_e (v a b a' b' : ℝ) : |clip v a' b' - clip v a b| ≤ max |a' - a| |b' - b| := by
  simp only [clip]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le_max le_rfl ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]

lemma clip_mem {v xbar : ℝ} (hx : 0 ≤ xbar) : 0 ≤ clip v 0 xbar ∧ clip v 0 xbar ≤ xbar :=
  ⟨le_max_left _ _, max_le hx (min_le_left _ _)⟩

theorem onEvent : OnEvent := by
  intro mu c ct xs xst kp km xm xbar hc hct hkp hkm hx hxm0 hxm1 lo hi lot hit psi
  have e1 : |lot - lo| ≤ |xst - xs| + kp * |1 / ct - 1 / c| := by
    refine (clip_lip_v _ _ _ _).trans ?_
    rw [show xst - kp / ct - (xs - kp / c) = (xst - xs) - kp * (1 / ct - 1 / c) by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hkp]
  have e2 : |hit - hi| ≤ |xst - xs| + km * |1 / ct - 1 / c| := by
    refine (clip_lip_v _ _ _ _).trans ?_
    rw [show xst + km / ct - (xs + km / c) = (xst - xs) + km * (1 / ct - 1 / c) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hkm]
  have e3 : |clip xm lot hit - clip xm lo hi| ≤ max |lot - lo| |hit - hi| := clip_lip_e _ _ _ _ _
  refine ⟨e1, e2, e3, ?_⟩
  -- both holdings lie in `[0, x̄]`
  have hlo := clip_mem (v := xs - kp / c) hx
  have hhi := clip_mem (v := xs + km / c) hx
  have hlot := clip_mem (v := xst - kp / ct) hx
  have hhit := clip_mem (v := xst + km / ct) hx
  have hin : ∀ a b : ℝ, 0 ≤ a → a ≤ xbar → 0 ≤ b → b ≤ xbar → 0 ≤ clip xm a b ∧ clip xm a b ≤ xbar :=
    fun a b ha0 ha1 hb0 hb1 => ⟨le_trans ha0 (le_max_left _ _), max_le ha1 ((min_le_left _ _).trans hb1)⟩
  obtain ⟨u0, u1⟩ := hin lo hi hlo.1 hlo.2 hhi.1 hhi.2
  obtain ⟨v0, v1⟩ := hin lot hit hlot.1 hlot.2 hhit.1 hhit.2
  set u := clip xm lo hi
  set v := clip xm lot hit
  -- `ψ` is Lipschitz on the box
  have hlip : psi u - psi v ≤ (|mu| + c * xbar + max kp km) * |u - v| := by
    have hcost := cost_lip (xm := xm) (a := u) (b := v) hkp hkm
    have hq : |c / 2 * u ^ 2 - c / 2 * v ^ 2| ≤ c * xbar * |u - v| := by
      rw [show c / 2 * u ^ 2 - c / 2 * v ^ 2 = c / 2 * (u + v) * (u - v) by ring, abs_mul,
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
    have hm : |mu * u - mu * v| ≤ |mu| * |u - v| := by rw [← mul_sub, abs_mul]
    have hsplit : psi u - psi v = (mu * u - mu * v) - (c / 2 * u ^ 2 - c / 2 * v ^ 2) -
        ((kp * max (u - xm) 0 + km * max (xm - u) 0) - (kp * max (v - xm) 0 + km * max (xm - v) 0)) := by
      simp only [psi]; ring
    rw [hsplit]
    have := le_abs_self (mu * u - mu * v)
    have := neg_abs_le (c / 2 * u ^ 2 - c / 2 * v ^ 2)
    have := neg_abs_le ((kp * max (u - xm) 0 + km * max (xm - u) 0) - (kp * max (v - xm) 0 + km * max (xm - v) 0))
    nlinarith
  have hL : 0 ≤ |mu| + c * xbar + max kp km :=
    add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hc.le hx)) (le_trans hkp (le_max_left _ _))
  refine hlip.trans (mul_le_mul_of_nonneg_left ?_ hL)
  rw [abs_sub_comm]; exact e3

/-! ### D: M5's one-review rule -/

theorem oneReviewM5 : OneReviewM5 := by
  intro n Sg Lam γ mu xm hSg hLam hγ f x0
  have hM : (Lam + γ • Sg).PosDef := Matrix.PosDef.posSemidef_add hLam (hSg.smul hγ)
  have hU := Novel.M5PartialAdjustmentSplitProof.pd_unit hM
  have hMx0 : (Lam + γ • Sg) *ᵥ x0 = Lam *ᵥ xm + mu := by
    simp only [x0]; rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hsL : Lamᵀ = Lam := Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hLam
  have hsS : Sgᵀ = Sg := Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hSg.posSemidef
  have hsM : (Lam + γ • Sg)ᵀ = Lam + γ • Sg := by rw [transpose_add, transpose_smul, hsL, hsS]
  -- `f(x0 + d) = f(x0) - (1/2) d'(Λ + γΣ)d`
  have hexp : ∀ d, f (x0 + d) = f x0 - 1 / 2 * (d ⬝ᵥ ((Lam + γ • Sg) *ᵥ d)) := by
    intro d
    have h1 := Novel.M5PartialAdjustmentSplitProof.sym_dot hsS x0 d
    have h2 := Novel.M5PartialAdjustmentSplitProof.sym_dot hsL x0 d
    have h3 := Novel.M5PartialAdjustmentSplitProof.sym_dot hsL xm d
    have h4 := Novel.M5PartialAdjustmentSplitProof.sym_dot hsL x0 xm
    have hfoc : d ⬝ᵥ ((Lam + γ • Sg) *ᵥ x0) = d ⬝ᵥ (Lam *ᵥ xm + mu) := by rw [hMx0]
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at hfoc
    simp only [f, mulVec_add, dotProduct_add, add_dotProduct, add_mulVec,
      smul_mulVec, dotProduct_smul, smul_eq_mul, mulVec_sub, dotProduct_sub, sub_dotProduct] at *
    rw [dotProduct_comm d mu] at hfoc
    nlinarith [hfoc, h1, h2, h3, h4]
  have hq : ∀ d, 0 ≤ d ⬝ᵥ ((Lam + γ • Sg) *ᵥ d) := fun d => by
    have := hM.posSemidef.dotProduct_mulVec_nonneg d; simpa using this
  refine ⟨hMx0, fun x => ?_, fun x hx => ?_, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := hexp (x - x0); rw [add_sub_cancel] at this; rw [this]; linarith [hq (x - x0)]
  · have := hexp (x - x0)
    rw [add_sub_cancel, hx] at this
    have h0 : (x - x0) ⬝ᵥ ((Lam + γ • Sg) *ᵥ (x - x0)) = 0 := by linarith
    by_contra hne
    have := hM.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial] at this
    linarith
  · have := hMx0; rw [h, add_mulVec, smul_mulVec] at this
    exact (add_left_cancel this).symm
  · apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hU))
    rw [hMx0, add_mulVec, smul_mulVec, h]

/-! ### The claim -/

theorem components : Components :=
  ⟨Novel.M2NoActiveTradeBandProof.proof, Novel.M2TwoStageSeparationProof.proof,
    Novel.M2SoftTargetTwoStageProof.proof, Novel.M6QuarterlyBandStaticCeilingProof.proof,
    Novel.M5PartialAdjustmentSplitProof.proof, Novel.M5MissingDirectionLeakProof.proof,
    Novel.M5LearningAimTwoSpeedsProof.proof, Novel.M5PlugInValueLossProof.proof,
    Novel.M5PlugInLossInputsProof.proof, Novel.M5ReestimationGuaranteeProof.proof,
    Novel.M5WhenAnticipationMattersProof.proof, Novel.M7LearningBandTransferProof.proof⟩

/-- Claim 038, the formal parts. -/
theorem proof : Standalone.IntegrationTheorem.statement :=
  ⟨components, tracking, kalmanDrift, anticipationOrder, residualIdentity, capBound, onEvent,
    oneReviewM5⟩

end

end Novel.IntegrationTheoremProof

import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Standalone.M7FineBandOneCostlyEtf
import Novel.M7DynamicBundlingBandProof

/-!
# Claim 042: proof

Parts 1, 2(c) and 4 are algebra. Part 2(b) is claim 107's formal part 3. Part 2(a) splits the
two-instrument backward recursion into the two one-instrument recursions by induction on the number
of remaining reviews. The stage objective is a sum of a fund term and an ETF term over a product box,
and every term is nonnegative, so the infimum of the sum is the sum of the infima. Part 3's law is cited
(PM, rule 21); only its application, the end ratio, is proved here.
-/

namespace Novel.M7FineBandOneCostlyEtfProof

open Matrix Standalone.M6QuarterlyBandStaticCeiling Standalone.M7FineBandOneCostlyEtf
open scoped Pointwise

noncomputable section

/-! ### Parts 1, 2(c) and 4: algebra -/

theorem errorCoord : ErrorCoord := by
  intro gamma sAA sAE sEE ya yb h rho cres
  simp only [rho, cres]
  field_simp
  ring

theorem innovations : Innovations := by
  intro S _ q da db vA vB r rho rho' hA hB hAB
  have e1 : mom q (db + rho • da) (db + rho • da) =
      mom q db db + 2 * rho * mom q da db + rho ^ 2 * mom q da da := by
    simp only [mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : mom q da (db + rho • da) = mom q da db + rho * mom q da da := by
    simp only [mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have e3 : mom q (da + rho' • db) (da + rho' • db) =
      mom q da da + 2 * rho' * mom q da db + rho' ^ 2 * mom q db db := by
    simp only [mom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hA, hB, hAB]; ring
  · rw [e2, hA, hAB]
  · rw [e3, hA, hB, hAB]; ring

theorem frozen : Frozen := by
  intro gamma sAA sAE sEE a b as bs h rho'
  simp only [rho']
  field_simp
  ring

theorem endRatio : EndRatio := by
  intro gamma sAA rc vA vidle k hg hs hrc hv hk cres
  have h1 : 0 < 1 - rc ^ 2 := by linarith
  simp only [cres]
  field_simp

theorem weight : Weight := by
  intro gamma sEE cres vA vBeff kA kE hg hs hc hv hk
  field_simp

theorem frictionless : Frictionless :=
  Novel.M7DynamicBundlingBandProof.proof.2.2.2.2.2

/-! ### Part 3: the corrector lemma -/

section Quartic

theorem corrector : Corrector := by
  intro c v kp km lam D hc hv hD
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, ?_, fun hl => ?_, fun hl hD3 y hy => ?_, fun hl y hy => ?_⟩
  · have h := ((((hasDerivAt_pow 4 y).const_mul (-(c / (12 * v)))).add
      ((hasDerivAt_pow 2 y).const_mul (lam / v))).add ((hasDerivAt_id y).const_mul ((km - kp) / 2)))
    convert h using 1
    · funext x; simp only [wq, Pi.add_apply, id]
    · simp only [wq1]; push_cast; ring
  · have h := (((hasDerivAt_pow 3 y).const_mul (-(c / (3 * v)))).add
      ((hasDerivAt_id y).const_mul (2 * lam / v))).add_const ((km - kp) / 2)
    convert h using 1
    · funext x; simp only [wq1, Pi.add_apply, id]
    · simp only [wq2]; push_cast; field_simp; ring
  · simp only [wq2]; field_simp; ring
  · simp only [wq2]
    constructor
    · rintro ⟨h1, -⟩
      rcases div_eq_zero_iff.mp h1 with h | h
      · linarith
      · exact absurd h hv.ne'
    · intro h; rw [h]; constructor <;> ring_nf
  · simp only [wq1]
    subst hl
    constructor
    · rintro ⟨h1, -⟩
      field_simp at h1; field_simp; linarith
    · intro h
      have : c * D ^ 3 = 3 * (kp + km) * v / 4 := by rw [h]; field_simp
      constructor <;> field_simp <;> nlinarith
  · subst hl
    have hk : (kp + km) * v = 4 * c * D ^ 3 / 3 := by rw [hD3]; field_simp
    have hy1 := hy.1; have hy2 := hy.2
    simp only [wq1, wq2]
    have hy2' : y ^ 2 ≤ D ^ 2 := by nlinarith
    refine ⟨div_nonneg (by nlinarith [mul_le_mul_of_nonneg_left hy2' hc.le]) hv.le, ?_, ?_⟩
    · have e : -(c / (3 * v)) * y ^ 3 + 2 * (c * D ^ 2 / 2) / v * y + (km - kp) / 2 + kp =
          c * (y + D) ^ 2 * (2 * D - y) / (3 * v) := by
        field_simp
        have : km + kp = 4 * c * D ^ 3 / (3 * v) := by field_simp; linarith
        nlinarith
      have : 0 ≤ c * (y + D) ^ 2 * (2 * D - y) / (3 * v) :=
        div_nonneg (mul_nonneg (mul_nonneg hc.le (sq_nonneg _)) (by linarith)) (by positivity)
      linarith
    · have e : km - (-(c / (3 * v)) * y ^ 3 + 2 * (c * D ^ 2 / 2) / v * y + (km - kp) / 2) =
          c * (D - y) ^ 2 * (2 * D + y) / (3 * v) := by
        field_simp
        have : km + kp = 4 * c * D ^ 3 / (3 * v) := by field_simp; linarith
        nlinarith
      have : 0 ≤ c * (D - y) ^ 2 * (2 * D + y) / (3 * v) :=
        div_nonneg (mul_nonneg (mul_nonneg hc.le (sq_nonneg _)) (by linarith)) (by positivity)
      linarith
  · subst hl
    have : D ^ 2 ≤ y ^ 2 := by
      have := sq_abs y; rw [← this]; exact pow_le_pow_left₀ hD.le hy 2
    nlinarith

end Quartic

/-! ### Part 3: the candidate -/

section Ergodic

variable {c v kp km D : ℝ}

/-- The cubic piece of `w'`. -/
def poly (c v kp km D : ℝ) (y : ℝ) : ℝ := (km - kp) / 2 + (c * D ^ 2 * y - c * y ^ 3 / 3) / v

lemma poly_deriv (y : ℝ) : HasDerivAt (poly c v kp km D) ((c * D ^ 2 - c * y ^ 2) / v) y := by
  have h := ((((hasDerivAt_id y).const_mul (c * D ^ 2)).sub
    (((hasDerivAt_pow 3 y).const_mul c).div_const 3)).div_const v).const_add ((km - kp) / 2)
  convert h using 1
  · funext x; simp only [poly, Pi.sub_apply, id]
  · norm_num; ring

lemma poly_top (hv : 0 < v) (hD : D ^ 3 = 3 * (kp + km) * v / (4 * c)) (hc : 0 < c) :
    poly c v kp km D D = km := by
  simp only [poly]
  have : c * D ^ 2 * D - c * D ^ 3 / 3 = 2 * c * D ^ 3 / 3 := by ring
  rw [this, hD]
  field_simp
  ring

lemma poly_bot (hv : 0 < v) (hD : D ^ 3 = 3 * (kp + km) * v / (4 * c)) (hc : 0 < c) :
    poly c v kp km D (-D) = -kp := by
  simp only [poly]
  have : c * D ^ 2 * (-D) - c * (-D) ^ 3 / 3 = -(2 * c * D ^ 3 / 3) := by ring
  rw [this, hD]
  field_simp
  ring

lemma wp_eq_poly {y : ℝ} (h1 : -D ≤ y) (h2 : y ≤ D) : wp c v kp km D y = poly c v kp km D y := by
  simp only [wp, poly, not_lt.mpr h1, not_lt.mpr h2, ↓reduceIte]

lemma wpp_eq (hv : 0 < v) (hc : 0 < c) (hD : 0 < D) (y : ℝ) :
    wpp c v D y = max ((c * D ^ 2 - c * y ^ 2) / v) 0 := by
  simp only [wpp]
  split_ifs with h
  · have : y ^ 2 ≤ D ^ 2 := by
      have := sq_abs y; rw [← this]; exact pow_le_pow_left₀ (abs_nonneg y) h 2
    rw [max_eq_left (div_nonneg (by nlinarith) hv.le)]
  · push Not at h
    have : D ^ 2 < y ^ 2 := by
      have := sq_abs y; rw [← this]; exact pow_lt_pow_left₀ h hD.le (by norm_num)
    rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hv.le)]

theorem correctorC2 : CorrectorC2 := by
  intro c v kp km hc hv hkp hkm hk
  set K := 3 * (kp + km) * v / (4 * c) with hKd
  have hK : 0 < K := by positivity
  refine ⟨⟨K ^ ((3 : ℕ)⁻¹ : ℝ), ⟨Real.rpow_pos_of_pos hK _, Real.rpow_inv_natCast_pow hK.le (by norm_num)⟩,
    fun D ⟨hD, hD3⟩ => ?_⟩, fun D hD hD3 => ?_⟩
  · have h2 := Real.rpow_inv_natCast_pow hK.le (n := 3) (by norm_num)
    exact (pow_left_inj₀ hD.le (Real.rpow_pos_of_pos hK _).le (by norm_num : (3 : ℕ) ≠ 0)).mp
      (hD3.trans h2.symm)
  intro lam
  refine ⟨fun D' hD' => ?_, fun y => ?_, ?_, ?_, ?_, fun y => ?_, ?_, ?_, fun y => ?_, fun y hy => ?_,
    fun y hy => ?_, ?_⟩
  · constructor
    · intro h
      have : D' ^ 3 = D ^ 3 := by
        rw [hD3, hKd]; field_simp at h ⊢; (try linarith)
      exact (pow_left_inj₀ hD'.le hD.le (by norm_num : (3 : ℕ) ≠ 0)).mp this
    · rintro rfl
      rw [hD3, hKd]; field_simp
  · -- the derivative of `w'`
    rcases lt_trichotomy y (-D) with h1 | h1 | h1
    · have hev : wp c v kp km D =ᶠ[nhds y] fun _ => -kp :=
        (eventually_lt_nhds h1).mono fun y' hy' => by simp [wp, hy']
      have hw : wpp c v D y = 0 := by
        have : ¬ |y| ≤ D := by rw [abs_of_neg (by linarith)]; linarith
        simp only [wpp, this, ↓reduceIte]
      rw [hw]; exact (hasDerivAt_const y (-kp)).congr_of_eventuallyEq hev
    · subst h1
      have hw : wpp c v D (-D) = 0 := by simp [wpp, abs_of_pos hD]
      rw [hw]
      have hl : HasDerivWithinAt (wp c v kp km D) 0 (Set.Iic (-D)) (-D) := by
        refine (hasDerivAt_const (-D) (-kp)).hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · rcases (Set.mem_Iic.mp hy).lt_or_eq with h | h
          · simp [wp, h]
          · rw [h, wp_eq_poly le_rfl (by linarith)]; exact poly_bot hv hD3 hc
        · rw [wp_eq_poly le_rfl (by linarith)]; exact poly_bot hv hD3 hc
      have hr : HasDerivWithinAt (wp c v kp km D) 0 (Set.Ici (-D)) (-D) := by
        have := (poly_deriv (c := c) (v := v) (kp := kp) (km := km) (D := D) (-D)).hasDerivWithinAt
          (s := Set.Icc (-D) D)
        have e : (c * D ^ 2 - c * (-D) ^ 2) / v = 0 := by ring_nf
        rw [e] at this
        have h2 : HasDerivWithinAt (wp c v kp km D) 0 (Set.Icc (-D) D) (-D) :=
          this.congr (fun y hy => wp_eq_poly hy.1 hy.2) (wp_eq_poly le_rfl (by linarith))
        exact h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))
      have := hl.union hr
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · rcases lt_trichotomy y D with h2 | h2 | h2
      · have hev : wp c v kp km D =ᶠ[nhds y] poly c v kp km D :=
          Filter.eventually_of_mem (Icc_mem_nhds h1 h2) fun y' hy' => wp_eq_poly hy'.1 hy'.2
        have hw : wpp c v D y = (c * D ^ 2 - c * y ^ 2) / v := by
          simp only [wpp, abs_le.mpr ⟨h1.le, h2.le⟩, ↓reduceIte]
        rw [hw]; exact (poly_deriv y).congr_of_eventuallyEq hev
      · subst h2
        have hw : wpp c v y y = 0 := by simp [wpp, abs_of_pos hD]
        rw [hw]
        have hr : HasDerivWithinAt (wp c v kp km y) 0 (Set.Ici y) y := by
          refine (hasDerivAt_const y km).hasDerivWithinAt.congr (fun y' hy' => ?_) ?_
          · rcases (Set.mem_Ici.mp hy').lt_or_eq with h | h
            · have : ¬ y' < -y := by linarith
              simp [wp, h, this]
            · rw [← h, wp_eq_poly (by linarith) le_rfl]; exact poly_top hv hD3 hc
          · rw [wp_eq_poly (by linarith) le_rfl]; exact poly_top hv hD3 hc
        have hl : HasDerivWithinAt (wp c v kp km y) 0 (Set.Iic y) y := by
          have := (poly_deriv (c := c) (v := v) (kp := kp) (km := km) (D := y) y).hasDerivWithinAt
            (s := Set.Icc (-y) y)
          have e : (c * y ^ 2 - c * y ^ 2) / v = 0 := by simp
          rw [e] at this
          have h2 : HasDerivWithinAt (wp c v kp km y) 0 (Set.Icc (-y) y) y :=
            this.congr (fun y' hy' => wp_eq_poly hy'.1 hy'.2) (wp_eq_poly (by linarith) le_rfl)
          exact h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by linarith))
        have := hl.union hr
        rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
        exact this
      · have hev : wp c v kp km D =ᶠ[nhds y] fun _ => km :=
          (eventually_gt_nhds h2).mono fun y' hy' => by
            have : ¬ y' < -D := by linarith
            simp [wp, hy', this]
        have hw : wpp c v D y = 0 := by
          have : ¬ |y| ≤ D := by rw [abs_of_pos (by linarith)]; linarith
          simp only [wpp, this, ↓reduceIte]
        rw [hw]; exact (hasDerivAt_const y km).congr_of_eventuallyEq hev
  · rw [show wpp c v D = fun y => max ((c * D ^ 2 - c * y ^ 2) / v) 0 from funext (wpp_eq hv hc hD)]
    fun_prop
  · simp [wpp, abs_of_pos hD]
  · simp [wpp, abs_of_pos hD]
  · -- the gradient bounds
    by_cases h1 : y < -D
    · simp only [wp, h1, ↓reduceIte]; constructor <;> linarith
    by_cases h2 : D < y
    · simp only [wp, h1, h2, ↓reduceIte]; constructor <;> linarith
    push Not at h1 h2
    rw [wp_eq_poly h1 h2]
    have lo : poly c v kp km D y - poly c v kp km D (-D) = c * (y + D) ^ 2 * (2 * D - y) / (3 * v) := by
      simp only [poly]; field_simp; ring
    have hi : poly c v kp km D D - poly c v kp km D y = c * (D - y) ^ 2 * (2 * D + y) / (3 * v) := by
      simp only [poly]; field_simp; ring
    rw [poly_bot hv hD3 hc] at lo
    rw [poly_top hv hD3 hc] at hi
    have l1 : 0 ≤ c * (y + D) ^ 2 * (2 * D - y) / (3 * v) :=
      div_nonneg (mul_nonneg (mul_nonneg hc.le (sq_nonneg _)) (by linarith)) (by positivity)
    have l2 : 0 ≤ c * (D - y) ^ 2 * (2 * D + y) / (3 * v) :=
      div_nonneg (mul_nonneg (mul_nonneg hc.le (sq_nonneg _)) (by linarith)) (by positivity)
    constructor <;> linarith
  · rw [wp_eq_poly le_rfl (by linarith), poly_bot hv hD3 hc]
  · rw [wp_eq_poly (by linarith) le_rfl, poly_top hv hD3 hc]
  · -- the HJB inequality
    simp only [lam, wpp]
    split_ifs with h
    · field_simp; ring_nf; exact le_rfl
    · push Not at h
      have : D ^ 2 < y ^ 2 := by
        have := sq_abs y; rw [← this]; exact pow_lt_pow_left₀ h hD.le (by norm_num)
      nlinarith
  · simp only [lam, wpp, hy, ↓reduceIte]; field_simp; ring
  · simp only [wpp, hy, ↓reduceIte]
    constructor
    · intro h
      have : c * D ^ 2 - c * y ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp h with h | h
        · exact h
        · exact absurd h hv.ne'
      have : y ^ 2 = D ^ 2 := by
        have := mul_left_cancel₀ hc.ne' (show c * y ^ 2 = c * D ^ 2 by linarith); exact this
      rw [← sq_abs y] at this
      exact (pow_left_inj₀ (abs_nonneg y) hD.le (by norm_num : (2 : ℕ) ≠ 0)).mp this
    · intro h
      have : y ^ 2 = D ^ 2 := by rw [← sq_abs y, h]
      rw [this]; simp
  · -- attainment
    simp only [lam]
    have : (kp + km) * v = 4 * c * D ^ 3 / 3 := by rw [hD3, hKd]; field_simp
    rw [this]; field_simp; ring

end Ergodic

/-! ### Part 2(a): uncorrelated risks -/

section Split

variable {Z Ω : Type} [Fintype Ω] {P : M6 2 Z Ω}

lemma sig10 (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) :
    P.Sigma t z 1 0 = 0 := by
  have := congrFun (congrFun (hS.2.1 t z) 0) 1
  simp only [transpose_apply] at this
  rw [this]; exact h01 t z

lemma sig_diag (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) :
    P.Sigma t z = diagonal fun i => P.Sigma t z i i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, h01, sig10 hS h01]

lemma sig_pos (hS : Setting P) (t : ℕ) (z : Z) (i : Fin 2) : 0 < P.Sigma t z i i := by
  have := hS.2.2.1 t z (Pi.single i 1) (by simp)
  simpa [mulVec, dotProduct, Pi.single_apply] using this

lemma inv_diag {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (μ : Fin n → ℝ) (i : Fin n) :
    ((diagonal d)⁻¹ *ᵥ μ) i = μ i / d i := by
  have h : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ (hd _), diagonal_one]
  rw [inv_eq_right_inv h, mulVec_diagonal, div_eq_mul_inv, mul_comm]

lemma xstar_P (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) (i : Fin 2) :
    xstar P t z i = P.mu t z i / (P.gamma * P.Sigma t z i i) := by
  simp only [xstar, Pi.smul_apply, smul_eq_mul]
  rw [sig_diag hS h01 t z, inv_diag (fun i => (sig_pos hS t z i).ne')]
  simp only [diagonal_apply_eq]
  field_simp

lemma xstar_part (hS : Setting P) (t : ℕ) (z : Z) (i : Fin 2) :
    xstar (part P i) t z 0 = P.mu t z i / (P.gamma * P.Sigma t z i i) := by
  have hd : (part P i).Sigma t z = diagonal fun _ => P.Sigma t z i i := by
    ext a b; rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [part]
  simp only [xstar, Pi.smul_apply, smul_eq_mul]
  rw [hd, inv_diag (fun _ => (sig_pos hS t z i).ne')]
  simp only [part]
  field_simp

lemma setting_part (hS : Setting P) (i : Fin 2) : Setting (part P i) := by
  obtain ⟨h1, _, _, hγ, hβ, hβ1, hr, hc, hq, hq1, hg⟩ := hS
  refine ⟨h1, fun t z => ?_, fun t z w hw => ?_, hγ, hβ, hβ1, fun _ => hr i, fun _ => hc i, hq, hq1,
    fun ω _ => hg ω i⟩
  · ext a b; rfl
  · have hw0 : w 0 ≠ 0 := fun h => hw (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
    have := sig_pos ⟨h1, ‹_›, ‹_›, hγ, hβ, hβ1, hr, hc, hq, hq1, hg⟩ t z i
    simp only [mulVec, dotProduct, Fin.sum_univ_one, part]
    have : 0 < w 0 * w 0 := mul_self_pos.mpr hw0
    nlinarith

omit [Fintype Ω] in
lemma cost_split (u : Fin 2 → ℝ) :
    cost P u = cost (part P 0) (fun _ => u 0) + cost (part P 1) (fun _ => u 1) := by
  simp [cost, Fin.sum_univ_two, part]

lemma track_split (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) (x : Fin 2 → ℝ) :
    track P t z x = track (part P 0) t z (fun _ => x 0) + track (part P 1) t z (fun _ => x 1) := by
  simp only [track, dotProduct, mulVec, Fin.sum_univ_two, Fin.sum_univ_one, Pi.sub_apply,
    h01, sig10 hS h01]
  rw [xstar_part hS, xstar_part hS, xstar_P hS h01, xstar_P hS h01]
  simp only [part]
  ring

lemma track_nonneg {n : ℕ} {Q : M6 n Z Ω} (hS : Setting Q) (t : ℕ) (z : Z) (x : Fin n → ℝ) :
    0 ≤ track Q t z x := by
  unfold track
  by_cases h : x - xstar Q t z = 0
  · rw [h]; simp
  · exact mul_nonneg (by linarith [hS.2.2.2.1]) (hS.2.2.1 t z _ h).le

lemma cost_nonneg {n : ℕ} {Q : M6 n Z Ω} (hS : Setting Q) (u : Fin n → ℝ) : 0 ≤ cost Q u :=
  Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (hS.2.2.2.2.2.2.1 i).1 (le_max_right _ _))
    (mul_nonneg (hS.2.2.2.2.2.2.1 i).2.2.1 (le_max_right _ _))

lemma Vk_nonneg {n : ℕ} {Q : M6 n Z Ω} (hS : Setting Q) : ∀ k z x, 0 ≤ Vk Q k z x
  | 0, _, _ => le_rfl
  | k + 1, z, x => Real.sInf_nonneg fun y ⟨x', _, hy⟩ => by
      rw [← hy]
      refine add_nonneg (cost_nonneg hS _) (add_nonneg (track_nonneg hS _ _ _) ?_)
      exact mul_nonneg hS.2.2.2.2.1.le (Finset.sum_nonneg fun ω _ =>
        mul_nonneg (hS.2.2.2.2.2.2.2.2.1 _ _ ω) (Vk_nonneg hS k _ _))

/-- The pair built from two one-instrument holdings. -/
def pair (a b : Fin 1 → ℝ) : Fin 2 → ℝ := ![a 0, b 0]

omit [Fintype Ω] in
lemma pair_mem {a b : Fin 1 → ℝ} : pair a b ∈ box P ↔ a ∈ box (part P 0) ∧ b ∈ box (part P 1) := by
  simp only [box, pair, Set.mem_ofPred_eq, Fin.forall_fin_two, Fin.forall_fin_one, part]
  simp

omit [Fintype Ω] in
lemma mem_box {x : Fin 2 → ℝ} :
    x ∈ box P ↔ (fun _ => x 0) ∈ box (part P 0) ∧ (fun _ => x 1) ∈ box (part P 1) := by
  simp only [box, Set.mem_ofPred_eq, Fin.forall_fin_two, part, forall_const]

theorem Vk_split (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) :
    ∀ k z (x : Fin 2 → ℝ), Vk P k z x =
      Vk (part P 0) k z (fun _ => x 0) + Vk (part P 1) k z (fun _ => x 1)
  | 0, _, _ => by simp [Vk]
  | k + 1, z, x => by
    have hS0 := setting_part hS 0
    have hS1 := setting_part hS 1
    set τ := P.T - (k + 1)
    set h : (Fin 2 → ℝ) → ℝ := fun x' => cost P (x' - x) + (track P τ z x' +
      P.beta * ∑ ω, P.prob τ z ω * Vk P k (P.next ω) (mark x' (P.gross ω)))
    set h0 : (Fin 1 → ℝ) → ℝ := fun a => cost (part P 0) (a - fun _ => x 0) + (track (part P 0) τ z a +
      (part P 0).beta * ∑ ω, (part P 0).prob τ z ω * Vk (part P 0) k ((part P 0).next ω)
        (mark a ((part P 0).gross ω)))
    set h1 : (Fin 1 → ℝ) → ℝ := fun b => cost (part P 1) (b - fun _ => x 1) + (track (part P 1) τ z b +
      (part P 1).beta * ∑ ω, (part P 1).prob τ z ω * Vk (part P 1) k ((part P 1).next ω)
        (mark b ((part P 1).gross ω)))
    have hsplit : ∀ x', h x' = h0 (fun _ => x' 0) + h1 (fun _ => x' 1) := fun x' => by
      simp only [h, h0, h1]
      rw [cost_split, track_split hS h01]
      have hm : ∀ ω, Vk P k (P.next ω) (mark x' (P.gross ω)) =
          Vk (part P 0) k (P.next ω) (mark (fun _ => x' 0) ((part P 0).gross ω)) +
          Vk (part P 1) k (P.next ω) (mark (fun _ => x' 1) ((part P 1).gross ω)) := fun ω => by
        rw [Vk_split hS h01 k]; rfl
      simp only [hm, mul_add, Finset.sum_add_distrib]
      simp only [part, Pi.sub_def]
      ring
    have hT0 : (part P 0).T = P.T := rfl
    have hT1 : (part P 1).T = P.T := rfl
    show sInf (h '' box P) = sInf (h0 '' box (part P 0)) + sInf (h1 '' box (part P 1))
    have hset : h '' box P = h0 '' box (part P 0) + h1 '' box (part P 1) := by
      ext r
      simp only [Set.mem_image, Set.mem_add]
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact ⟨_, ⟨_, (mem_box.mp hx').1, rfl⟩, _, ⟨_, (mem_box.mp hx').2, rfl⟩, (hsplit x').symm⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
        refine ⟨pair a b, pair_mem.mpr ⟨ha, hb⟩, ?_⟩
        rw [hsplit]
        congr 1
        · congr 1; funext i; rw [Subsingleton.elim i 0]; rfl
        · congr 1; funext i; rw [Subsingleton.elim i 0]; rfl
    have hne : ∀ (Q : M6 1 Z Ω), Setting Q → (box Q).Nonempty := fun Q hQ =>
      ⟨fun _ => 0, fun i => ⟨le_rfl, (hQ.2.2.2.2.2.2.2.1 i).le⟩⟩
    have hbdd : ∀ (Q : M6 1 Z Ω) (f : (Fin 1 → ℝ) → ℝ), (∀ a, 0 ≤ f a) → BddBelow (f '' box Q) :=
      fun Q f hf => ⟨0, by rintro _ ⟨a, _, rfl⟩; exact hf a⟩
    have n0 : ∀ a, 0 ≤ h0 a := fun a => add_nonneg (cost_nonneg hS0 _) (add_nonneg
      (track_nonneg hS0 _ _ _) (mul_nonneg hS0.2.2.2.2.1.le (Finset.sum_nonneg fun ω _ =>
        mul_nonneg (hS0.2.2.2.2.2.2.2.2.1 _ _ ω) (Vk_nonneg hS0 k _ _))))
    have n1 : ∀ a, 0 ≤ h1 a := fun a => add_nonneg (cost_nonneg hS1 _) (add_nonneg
      (track_nonneg hS1 _ _ _) (mul_nonneg hS1.2.2.2.2.1.le (Finset.sum_nonneg fun ω _ =>
        mul_nonneg (hS1.2.2.2.2.2.2.2.2.1 _ _ ω) (Vk_nonneg hS1 k _ _))))
    rw [hset, csInf_add ((hne _ hS0).image _) (hbdd _ _ n0) ((hne _ hS1).image _) (hbdd _ _ n1)]

theorem V_split (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) (x : Fin 2 → ℝ) :
    V P t z x = V1 (part P 0) t z (x 0) + V1 (part P 1) t z (x 1) := by
  simp only [V1, V]
  exact Vk_split hS h01 _ z x

lemma G_split (hS : Setting P) (h01 : ∀ t z, P.Sigma t z 0 1 = 0) (t : ℕ) (z : Z) (x : Fin 2 → ℝ) :
    G P t z x = G (part P 0) t z (fun _ => x 0) + G (part P 1) t z (fun _ => x 1) := by
  simp only [G]
  rw [track_split hS h01]
  have hm : ∀ ω, V P (t + 1) (P.next ω) (mark x (P.gross ω)) =
      V (part P 0) (t + 1) (P.next ω) (mark (fun _ => x 0) ((part P 0).gross ω)) +
      V (part P 1) (t + 1) (P.next ω) (mark (fun _ => x 1) ((part P 1).gross ω)) := fun ω => by
    rw [V_split hS h01]; rfl
  simp only [hm, mul_add, Finset.sum_add_distrib]
  simp only [part]
  ring

theorem uncorrelated : Uncorrelated := by
  intro Z Ω _ P hS h01
  refine ⟨setting_part hS, fun t z i => by rw [xstar_part hS, xstar_P hS h01], V_split hS h01,
    fun t z x x' _ => ?_⟩
  have hF : ∀ y : Fin 2 → ℝ, cost P (y - x) + G P t z y =
      (cost (part P 0) ((fun _ => y 0) - fun _ => x 0) + G (part P 0) t z (fun _ => y 0)) +
      (cost (part P 1) ((fun _ => y 1) - fun _ => x 1) + G (part P 1) t z (fun _ => y 1)) := fun y => by
    rw [cost_split, G_split hS h01]
    simp only [Pi.sub_def]
    ring
  constructor
  · rintro ⟨hx', hopt⟩
    obtain ⟨h0, h1⟩ := mem_box.mp hx'
    refine ⟨⟨h0, fun a ha => ?_⟩, ⟨h1, fun b hb => ?_⟩⟩
    · have := hopt (pair a (fun _ => x' 1)) (pair_mem.mpr ⟨ha, h1⟩)
      rw [hF, hF] at this
      have ea : (fun _ : Fin 1 => pair a (fun _ => x' 1) 0) = a := by
        funext i; rw [Subsingleton.elim i 0]; rfl
      simp only [pair, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [show (fun _ : Fin 1 => a 0) = a from by funext i; rw [Subsingleton.elim i 0]] at this
      linarith
    · have := hopt (pair (fun _ => x' 0) b) (pair_mem.mpr ⟨h0, hb⟩)
      rw [hF, hF] at this
      simp only [pair, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [show (fun _ : Fin 1 => b 0) = b from by funext i; rw [Subsingleton.elim i 0]] at this
      linarith
  · rintro ⟨⟨h0, o0⟩, ⟨h1, o1⟩⟩
    refine ⟨mem_box.mpr ⟨h0, h1⟩, fun y hy => ?_⟩
    rw [hF, hF]
    have := o0 _ (mem_box.mp hy).1
    have := o1 _ (mem_box.mp hy).2
    linarith

end Split

theorem proof : Standalone.M7FineBandOneCostlyEtf.statement :=
  ⟨errorCoord, innovations, uncorrelated, frictionless, frozen, corrector, correctorC2, endRatio, weight⟩

end

end Novel.M7FineBandOneCostlyEtfProof

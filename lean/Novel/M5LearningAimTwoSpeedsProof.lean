import Mathlib.Analysis.SpecificLimits.Basic
import Novel.M5PartialAdjustmentSplitProof
import Standalone.M5LearningAimTwoSpeeds

/-!
# Proof of claim 032

Uses claim 030's proof module (`depends_on: [30]`, Q-04): part 3's recursion, the scalar rates
`gseq`, the variances `pvar`, and the separation of part 4(a).

* **Spectral pairs.** `Π_c` and `Π_r` are complementary orthogonal projections. Every fund-block
  matrix is `a Π_c + b Π_r`, and such pairs multiply, add and invert coefficient-wise.
* **Part 1.** The Kalman step acts on each coefficient as the scalar update.
* **Part 2.** The Riccati recursion acts coefficient-wise. `g_t` increases with the prior variance,
  strictly when the variances differ.
* **Part 3.** `ℓ_t = (γσ² + ρa_{t+1}ℓ_{t+1})/(d_t - λ_A)`, which matches the aim recursion
  coefficient-wise. The weights telescope to 1, and `ℓ_t` is a convex combination of
  `σ²/(σ² + p_s)`.
-/

namespace Novel.M5LearningAimTwoSpeedsProof

open Matrix Standalone.M5PartialAdjustmentSplit Standalone.M5LearningAimTwoSpeeds
open Novel.M5PartialAdjustmentSplitProof

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Spectral pairs -/

section Pairs

variable {N : ℕ} (hN : 0 < N)
include hN

lemma ones_mul : ones N * ones N = (N : ℝ) • ones N := by
  ext i j; simp [ones, Matrix.mul_apply]

lemma pc_idem : Pc N * Pc N = Pc N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Pc, smul_mul_smul_comm, ones_mul hN, smul_smul, mul_assoc, inv_mul_cancel₀ hN', mul_one]

lemma pc_pr : Pc N * Pr N = 0 := by rw [Pr, Matrix.mul_sub, Matrix.mul_one, pc_idem hN, sub_self]

lemma pr_pc : Pr N * Pc N = 0 := by rw [Pr, Matrix.sub_mul, Matrix.one_mul, pc_idem hN, sub_self]

lemma pr_idem : Pr N * Pr N = Pr N := by
  rw [Pr, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, pc_idem hN, sub_self, sub_zero]

lemma pc_add_pr : Pc N + Pr N = 1 := by rw [Pr]; abel

lemma one_sp : (1 : Matrix (Fin N) (Fin N) ℝ) = (1 : ℝ) • Pc N + (1 : ℝ) • Pr N := by
  rw [one_smul, one_smul, pc_add_pr hN]

lemma sp_mul (a b c d : ℝ) :
    (a • Pc N + b • Pr N) * (c • Pc N + d • Pr N) = (a * c) • Pc N + (b * d) • Pr N := by
  simp only [Matrix.add_mul, Matrix.mul_add, smul_mul_smul_comm, pc_idem hN, pc_pr hN, pr_pc hN,
    pr_idem hN, smul_zero, add_zero, zero_add]

lemma sp_add (a b c d : ℝ) :
    (a • Pc N + b • Pr N) + (c • Pc N + d • Pr N) = (a + c) • Pc N + (b + d) • Pr N := by
  rw [add_smul, add_smul]; abel

lemma sp_smul (r a b : ℝ) : r • (a • Pc N + b • Pr N) = (r * a) • Pc N + (r * b) • Pr N := by
  rw [smul_add, smul_smul, smul_smul]

lemma sp_sub (a b c d : ℝ) :
    (a • Pc N + b • Pr N) - (c • Pc N + d • Pr N) = (a - c) • Pc N + (b - d) • Pr N := by
  rw [sub_smul, sub_smul]; abel

lemma sp_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : (a • Pc N + b • Pr N)⁻¹ = a⁻¹ • Pc N + b⁻¹ • Pr N :=
  Matrix.inv_eq_left_inv (by rw [sp_mul hN, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, ← one_sp hN])

lemma sp_mulVec (a b : ℝ) (v : Fin N → ℝ) :
    (a • Pc N + b • Pr N) *ᵥ v = a • (Pc N *ᵥ v) + b • (Pr N *ᵥ v) := by
  rw [add_mulVec, smul_mulVec, smul_mulVec]

lemma pc_sp_v (a b : ℝ) (v : Fin N → ℝ) : Pc N *ᵥ ((a • Pc N + b • Pr N) *ᵥ v) = a • (Pc N *ᵥ v) := by
  rw [mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, pc_idem hN, pc_pr hN, smul_zero,
    add_zero, smul_mulVec]

lemma pr_sp_v (a b : ℝ) (v : Fin N → ℝ) : Pr N *ᵥ ((a • Pc N + b • Pr N) *ᵥ v) = b • (Pr N *ᵥ v) := by
  rw [mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, pr_pc hN, pr_idem hN, smul_zero,
    zero_add, smul_mulVec]

end Pairs

/-! ### Part 1 -/

lemma pvar_zero (s2 sig2 : ℝ) : pvar s2 sig2 0 = s2 := by simp [pvar]

lemma prec_succ {s2 sig2 : ℝ} (_hs : 0 < s2) (_hg : 0 < sig2) (t : ℕ) :
    1 / pvar s2 sig2 (t + 1) = 1 / pvar s2 sig2 t + 1 / sig2 := by
  simp only [pvar, one_div_one_div]
  push_cast
  ring

/-- `pvar` is strictly increasing in the prior variance. -/
lemma pvar_mono_s2 {s2 s2' sig2 : ℝ} (hs : 0 < s2) (hlt : s2 < s2') (hg : 0 < sig2) (t : ℕ) :
    pvar s2 sig2 t < pvar s2' sig2 t := by
  have hs' : 0 < s2' := by linarith
  unfold pvar
  apply one_div_lt_one_div_of_lt (by positivity)
  have : 1 / s2' < 1 / s2 := one_div_lt_one_div_of_lt hs hlt
  linarith

lemma pvar_strict {s2 sig2 : ℝ} (hs : 0 < s2) (hg : 0 < sig2) (t : ℕ) :
    pvar s2 sig2 (t + 1) < pvar s2 sig2 t := by
  have h := prec_succ hs hg t
  have hp := pvar_pos hs hg t
  have hp1 := pvar_pos hs hg (t + 1)
  have : 1 / pvar s2 sig2 t < 1 / pvar s2 sig2 (t + 1) := by rw [h]; have := one_div_pos.mpr hg; linarith
  exact (one_div_lt_one_div hp hp1).mp this

theorem twoVariances : TwoVariances := by
  intro N s2 sb2 sig2 hN hs hsb hg
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsc : 0 < s2 + N * sb2 := by positivity
  refine ⟨fun t => ?_, fun t => ⟨prec_succ hsc hg t, prec_succ hs hg t⟩, fun t => ⟨?_, ?_⟩, ?_, ?_⟩
  · induction t with
    | zero =>
      show s2 • (1 : Matrix (Fin N) (Fin N) ℝ) + sb2 • ones N = _
      rw [pc, pr, pvar_zero, pvar_zero]
      have hones : ones N = (N : ℝ) • Pc N := by
        rw [Pc, smul_smul, mul_inv_cancel₀ hN'.ne', one_smul]
      rw [hones, ← pc_add_pr hN, smul_add, smul_smul, add_smul, mul_comm sb2]
      abel
    | succ t ih =>
      show kal _ _ _ (t + 1) = _
      rw [kal_succ, show kal (s2 • (1 : Matrix (Fin N) (Fin N) ℝ) + sb2 • ones N) 1 (sig2 • 1) t =
        postA N s2 sb2 sig2 t from rfl, ih]
      simp only [transpose_one, Matrix.mul_one, Matrix.one_mul]
      have hpc := pvar_pos hsc hg t
      have hpr := pvar_pos hs hg t
      rw [one_sp hN, sp_smul hN, sp_add hN, sp_inv hN (by unfold pc; linarith) (by unfold pr; linarith),
        sp_mul hN, sp_mul hN, sp_sub hN]
      simp only [mul_one]
      simp only [pc, pr]
      rw [pvar_succ hsc hg t, pvar_succ hs hg t]
  · rcases eq_or_lt_of_le hsb with h0 | h0
    · simp [pc, pr, ← h0]
    · exact (pvar_mono_s2 hs (by nlinarith) hg t).le
  · constructor
    · intro h
      by_contra hne
      have hpos : 0 < sb2 := lt_of_le_of_ne hsb (Ne.symm hne)
      have := pvar_mono_s2 hs (show s2 < s2 + N * sb2 by nlinarith) hg t
      unfold pc pr at h
      linarith
    · intro h; simp [pc, pr, h]
  · -- the difference is `(b - a)/((a + t/σ²)(b + t/σ²))`
    intro t u htu
    simp only
    unfold pc pr pvar
    have ha : 0 < 1 / (s2 + N * sb2) := by positivity
    have hb : 0 < 1 / s2 := by positivity
    have hab : 1 / (s2 + N * sb2) ≤ 1 / s2 := one_div_le_one_div_of_le hs (by nlinarith)
    have htu' : (t : ℝ) / sig2 ≤ (u : ℝ) / sig2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast htu) hg.le
    rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity)]
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by positivity)
    nlinarith [mul_le_mul htu' htu' (by positivity) (by positivity)]
  · -- `t²(p^c_t - p^r_t) → (b - a)σ⁴`
    set a := 1 / (s2 + N * sb2) with ha_def
    set b := 1 / s2 with hb_def
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hlim : Filter.Tendsto (fun t : ℕ => (b - a) / ((a * (t : ℝ)⁻¹ + 1 / sig2) *
        (b * (t : ℝ)⁻¹ + 1 / sig2))) Filter.atTop (nhds ((b - a) / ((a * 0 + 1 / sig2) * (b * 0 + 1 / sig2)))) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
      refine Filter.Tendsto.div tendsto_const_nhds
        (((h0.const_mul a).add_const _).mul ((h0.const_mul b).add_const _)) ?_
      positivity
    have hval : (b - a) / ((a * 0 + 1 / sig2) * (b * 0 + 1 / sig2)) =
        N * sb2 * sig2 ^ 2 / (s2 * (s2 + N * sb2)) := by
      simp only [a, b]; field_simp; ring
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have htr : (0 : ℝ) < t := by exact_mod_cast ht
    simp only [pc, pr, pvar]
    rw [ha_def, hb_def]
    field_simp
    ring

/-! ### Directions -/

section DirLemmas

variable {D : Dir} (hD : D.Setting)
include hD

lemma dir_p_pos (u : ℕ) : 0 < D.p u := pvar_pos hD.2.2.2.1 hD.2.2.1 u

lemma dir_g_nonneg (u : ℕ) : 0 ≤ D.g u :=
  (gseq_bounds hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1.le D.T u).1

lemma dir_g_pos {u : ℕ} (hu : u < D.T) : 0 < D.g u :=
  ((gseq_bounds hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1.le D.T u).2 hu).1

lemma dir_a_nonneg (u : ℕ) : 0 ≤ D.a u := mul_nonneg hD.1.le (dir_g_nonneg hD u)

lemma dir_a_pos {u : ℕ} (hu : u < D.T) : 0 < D.a u := mul_pos hD.1 (dir_g_pos hD hu)

lemma dir_a_ge {u : ℕ} (hu : D.T ≤ u) : D.a u = 0 := by
  simp only [Dir.a, Dir.g, gseq_ge _ _ _ _ _ hu, mul_zero]

lemma dir_dl_pos (u : ℕ) : 0 < D.d u - D.lam := by
  have := dir_p_pos hD u
  have := dir_a_nonneg hD (u + 1)
  simp only [Dir.d]
  have : 0 < D.gam * (D.sig2 + D.p u) := mul_pos hD.2.1 (by linarith [hD.2.2.1])
  nlinarith [mul_nonneg hD.2.2.2.2.1.le (dir_a_nonneg hD (u + 1))]

/-- `g_t = 1 - λ_A/d_t`. -/
lemma dir_g_eq {u : ℕ} (hu : u < D.T) : D.g u = 1 - D.lam / D.d u := by
  rw [Dir.g, gseq_lt _ _ _ _ _ hu]
  have hd := dir_dl_pos hD u
  have e : 1 + D.gam * (D.sig2 + pvar D.s2 D.sig2 u) / D.lam + D.rho * gseq D.lam D.gam D.sig2 D.s2 D.rho D.T (u + 1) =
      D.d u / D.lam := by
    simp only [Dir.d, Dir.a, Dir.g, Dir.p]; field_simp [hD.1.ne']
  rw [e, one_div_div]

lemma dir_w_pos : ∀ k t, k < D.T - t → 0 < D.w k t := by
  intro k
  induction k with
  | zero =>
    intro t _
    simp only [Dir.w]
    exact div_pos (mul_pos hD.2.1 (by linarith [dir_p_pos hD t, hD.2.2.1])) (dir_dl_pos hD t)
  | succ k ih =>
    intro t hk
    simp only [Dir.w]
    exact mul_pos (div_pos (mul_pos hD.2.2.2.2.1 (dir_a_pos hD (by omega))) (dir_dl_pos hD t)) (ih (t + 1) (by omega))

lemma dir_w_sum : ∀ t, t < D.T → ∑ k ∈ Finset.range (D.T - t), D.w k t = 1 := by
  suffices h : ∀ n t, D.T - t = n + 1 → ∑ k ∈ Finset.range (D.T - t), D.w k t = 1 from
    fun t ht => h (D.T - t - 1) t (by omega)
  intro n
  induction n with
  | zero =>
    intro t ht
    rw [ht, Finset.sum_range_one]
    simp only [Dir.w, Dir.d, dir_a_ge hD (show D.T ≤ t + 1 by omega), mul_zero, add_zero]
    rw [add_sub_cancel_left, div_self (mul_pos hD.2.1 (by linarith [dir_p_pos hD t, hD.2.2.1])).ne']
  | succ n ih =>
    intro t ht
    have htail := ih (t + 1) (by omega)
    rw [show D.T - (t + 1) = n + 1 by omega] at htail
    rw [ht, Finset.sum_range_succ']
    simp only [Dir.w]
    rw [← Finset.mul_sum, htail, mul_one, ← add_div]
    rw [show D.rho * D.a (t + 1) + D.gam * (D.sig2 + D.p t) = D.d t - D.lam by simp only [Dir.d]; ring]
    exact div_self (dir_dl_pos hD t).ne'

/-- `ℓ_t = (γσ² + ρ a_{t+1} ℓ_{t+1})/(d_t - λ_A)`. -/
lemma dir_ell_rec {t : ℕ} (ht : t < D.T) :
    D.ell t = (D.gam * D.sig2 + D.rho * D.a (t + 1) * D.ell (t + 1)) / (D.d t - D.lam) := by
  have hd := dir_dl_pos hD t
  have hp := dir_p_pos hD t
  conv_lhs => unfold Dir.ell
  rw [show D.T - t = (D.T - (t + 1)) + 1 by omega, Finset.sum_range_succ']
  simp only [Dir.w, add_zero]
  have e : ∀ k, D.rho * D.a (t + 1) / (D.d t - D.lam) * D.w k (t + 1) * (D.sig2 / (D.sig2 + D.p (t + (k + 1)))) =
      D.rho * D.a (t + 1) / (D.d t - D.lam) * (D.w k (t + 1) * (D.sig2 / (D.sig2 + D.p (t + 1 + k)))) := by
    intro k; rw [show t + (k + 1) = t + 1 + k by omega]; ring
  simp only [e]
  rw [← Finset.mul_sum, show ∑ k ∈ Finset.range (D.T - (t + 1)),
    D.w k (t + 1) * (D.sig2 / (D.sig2 + D.p (t + 1 + k))) = D.ell (t + 1) from rfl]
  have hsp : D.sig2 + D.p t ≠ 0 := by linarith [hD.2.2.1]
  have hdl : D.d t - D.lam ≠ 0 := hd.ne'
  field_simp
  ring

lemma dir_ell_ge {t : ℕ} (hT : D.T ≤ t) : D.ell t = 0 := by
  simp [Dir.ell, Nat.sub_eq_zero_of_le hT]

/-- `σ²/(σ² + p_s) ≥ σ²/(σ² + p_t)` for `s ≥ t`, and `< 1`. -/
lemma dir_c_bounds (t k : ℕ) : D.sig2 / (D.sig2 + D.p t) ≤ D.sig2 / (D.sig2 + D.p (t + k)) ∧
    D.sig2 / (D.sig2 + D.p (t + k)) < 1 := by
  have hs := hD.2.2.1
  have hpk := dir_p_pos hD (t + k)
  refine ⟨div_le_div_of_nonneg_left hs.le (by linarith) ?_, by rw [div_lt_one (by linarith)]; linarith⟩
  have := pvar_anti hD.2.2.2.1 hs (Nat.le_add_right t k)
  simp only [Dir.p]
  linarith

end DirLemmas

theorem learningFactor : LearningFactor := by
  intro D hD t ht
  have hs := hD.2.2.1
  have hpt := dir_p_pos hD t
  have hc0 : 0 < D.sig2 / (D.sig2 + D.p t) := by positivity
  have hwpos := dir_w_pos hD
  have hsum := dir_w_sum hD t ht
  have hlow : D.sig2 / (D.sig2 + D.p t) ≤ D.ell t := by
    calc D.sig2 / (D.sig2 + D.p t) = ∑ k ∈ Finset.range (D.T - t), D.w k t * (D.sig2 / (D.sig2 + D.p t)) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ D.ell t := Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (dir_c_bounds hD t k).1 (hwpos k t (Finset.mem_range.mp hk)).le
  have hup : D.ell t ≤ 1 := by
    calc D.ell t ≤ ∑ k ∈ Finset.range (D.T - t), D.w k t * 1 := Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (dir_c_bounds hD t k).2.le (hwpos k t (Finset.mem_range.mp hk)).le
      _ = 1 := by simp only [mul_one, hsum]
  have hfac : D.factor t = D.ell t / (D.sig2 / (D.sig2 + D.p t)) := by
    rw [Dir.factor, div_div_eq_mul_div, mul_div_assoc]
  refine ⟨fun k hk => hwpos k t hk, hsum, hlow, hup, ?_, ?_⟩
  · rw [hfac, le_div_iff₀ hc0, one_mul]; exact hlow
  · rw [hfac, div_eq_one_iff_eq hc0.ne']
    constructor
    · intro heq
      by_contra hne
      -- the `k = 1` term is strictly larger, so `ℓ_t` exceeds the lower bound
      have h1 : 1 < D.T - t := by omega
      have hstrict : D.sig2 / (D.sig2 + D.p t) < D.sig2 / (D.sig2 + D.p (t + 1)) := by
        have := pvar_strict hD.2.2.2.1 hs t
        apply div_lt_div_of_pos_left hs (by linarith [dir_p_pos hD (t + 1)])
        simp only [Dir.p]; linarith
      have hlt : ∑ k ∈ Finset.range (D.T - t), D.w k t * (D.sig2 / (D.sig2 + D.p t)) < D.ell t := by
        apply Finset.sum_lt_sum
        · intro k hk
          exact mul_le_mul_of_nonneg_left (dir_c_bounds hD t k).1 (hwpos k t (Finset.mem_range.mp hk)).le
        · exact ⟨1, Finset.mem_range.mpr h1, mul_lt_mul_of_pos_left hstrict (hwpos 1 t h1)⟩
      rw [← Finset.sum_mul, hsum, one_mul] at hlt
      linarith
    · intro h
      subst h
      have h1 : D.T - (D.T - 1) = 1 := by omega
      rw [Dir.ell, h1, Finset.sum_range_one, add_zero]
      have := hsum
      rw [h1, Finset.sum_range_one] at this
      rw [this, one_mul]

/-! ### Parts 2 and 3 on the fund block -/

section Fund

variable {N : ℕ} {lam gam sig2 s2 sb2 rho : ℝ} {T : ℕ} (hN : 0 < N) (hl : 0 < lam) (hgm : 0 < gam)
  (hg : 0 < sig2) (hs : 0 < s2) (hsb : 0 ≤ sb2) (hr : 0 < rho) (hr1 : rho ≤ 1)
include hN hl hgm hg hs hsb hr hr1

lemma hsc : 0 < s2 + N * sb2 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity

lemma setC : (dirC N lam gam sig2 s2 sb2 rho T).Setting :=
  ⟨hl, hgm, hg, hsc hN hl hgm hg hs hsb hr hr1, hr, hr1⟩

lemma setR : (dirR lam gam sig2 s2 rho T).Setting := ⟨hl, hgm, hg, hs, hr, hr1⟩

lemma fund_S (t : ℕ) : (fundLQ N lam gam sig2 s2 sb2 rho T).S t =
    (gam * (sig2 + (dirC N lam gam sig2 s2 sb2 rho T).p t)) • Pc N +
      (gam * (sig2 + (dirR lam gam sig2 s2 rho T).p t)) • Pr N := by
  show gam • (sig2 • 1 + postA N s2 sb2 sig2 t) = _
  rw [(twoVariances N s2 sb2 sig2 hN hs hsb hg).1 t, one_sp hN, sp_smul hN, sp_add hN, sp_smul hN]
  simp only [mul_one]
  rfl

/-- The fund block's recursion is coefficient-wise. -/
lemma fund_ric : ∀ t, (fundLQ N lam gam sig2 s2 sb2 rho T).A t =
    (dirC N lam gam sig2 s2 sb2 rho T).a t • Pc N + (dirR lam gam sig2 s2 rho T).a t • Pr N := by
  set Q := fundLQ N lam gam sig2 s2 sb2 rho T
  set C := dirC N lam gam sig2 s2 sb2 rho T
  set R := dirR lam gam sig2 s2 rho T
  have hC := setC (T := T) hN hl hgm hg hs hsb hr hr1
  have hR := setR (T := T) (sb2 := sb2) (N := N) hN hl hgm hg hs hsb hr hr1
  suffices h : ∀ k t, T - t = k → Q.A t = C.a t • Pc N + R.a t • Pr N from fun t => h _ t rfl
  intro k
  induction k with
  | zero =>
    intro t ht
    rw [LQ.A_ge Q (show Q.T ≤ t by show T ≤ t; omega), dir_a_ge hC (show C.T ≤ t by show T ≤ t; omega),
      dir_a_ge hR (show R.T ≤ t by show T ≤ t; omega), zero_smul, zero_smul, add_zero]
  | succ k ih =>
    intro t ht
    have htT : t < T := by omega
    have hA1 := ih (t + 1) (by omega)
    obtain ⟨eA, -, -⟩ := LQ.ric_lt Q (show t < Q.T from htT)
    have hD : Q.D t = C.d t • Pc N + R.d t • Pr N := by
      show lam • 1 + Q.S t + rho • Q.A (t + 1) = _
      rw [fund_S hN hl hgm hg hs hsb hr hr1, hA1, one_sp hN, sp_smul hN, sp_add hN, sp_smul hN, sp_add hN]
      simp only [mul_one]
      rfl
    have hdc := dir_dl_pos hC t
    have hdr := dir_dl_pos hR t
    have hlc : C.lam = lam := rfl
    have hlr : R.lam = lam := rfl
    rw [eA, hD, sp_inv hN (by linarith) (by linarith)]
    show (lam • 1) - (lam • 1) * _ * (lam • 1) = _
    rw [one_sp hN, sp_smul hN, sp_mul hN, sp_mul hN, sp_sub hN]
    have hcd : C.d t ≠ 0 := by linarith
    have hrd : R.d t ≠ 0 := by linarith
    have ec : lam * 1 - lam * 1 * (C.d t)⁻¹ * (lam * 1) = C.a t := by
      rw [Dir.a, dir_g_eq hC (show t < C.T from htT), hlc,
        show (dirC N lam gam sig2 s2 sb2 rho T).d t = C.d t from rfl]
      field_simp
    have er : lam * 1 - lam * 1 * (R.d t)⁻¹ * (lam * 1) = R.a t := by
      rw [Dir.a, dir_g_eq hR (show t < R.T from htT), hlr,
        show (dirR lam gam sig2 s2 rho T).d t = R.d t from rfl]
      field_simp
    rw [ec, er]

lemma fund_D (t : ℕ) : (fundLQ N lam gam sig2 s2 sb2 rho T).D t =
    (dirC N lam gam sig2 s2 sb2 rho T).d t • Pc N + (dirR lam gam sig2 s2 rho T).d t • Pr N := by
  show lam • 1 + _ + rho • _ = _
  rw [fund_S hN hl hgm hg hs hsb hr hr1, fund_ric hN hl hgm hg hs hsb hr hr1, one_sp hN, sp_smul hN,
    sp_add hN, sp_smul hN, sp_add hN]
  simp only [mul_one]
  rfl

end Fund

theorem twoSpeeds : TwoSpeeds := by
  intro N lam gam sig2 s2 sb2 rho T hN hl hgm hg hs hsb hr hr1
  set C := dirC N lam gam sig2 s2 sb2 rho T
  set R := dirR lam gam sig2 s2 rho T
  have hC := setC (T := T) hN hl hgm hg hs hsb hr hr1
  have hR := setR (T := T) (sb2 := sb2) (N := N) hN hl hgm hg hs hsb hr hr1
  have hsc' := hsc hN hl hgm hg hs hsb hr hr1
  -- `g` increases with the prior variance, strictly when it is strictly larger
  have hmono : ∀ {s2' : ℝ}, s2 < s2' → ∀ t, t < T → gseq lam gam sig2 s2 rho T t < gseq lam gam sig2 s2' rho T t := by
    intro s2' hlt
    have hs' : 0 < s2' := by linarith
    suffices h : ∀ k t, T - t = k → gseq lam gam sig2 s2 rho T t ≤ gseq lam gam sig2 s2' rho T t ∧
        (t < T → gseq lam gam sig2 s2 rho T t < gseq lam gam sig2 s2' rho T t) from fun t ht => (h _ t rfl).2 ht
    intro k
    induction k with
    | zero =>
      intro t ht
      rw [gseq_ge _ _ _ _ _ (by omega), gseq_ge _ _ _ _ _ (by omega)]
      exact ⟨le_rfl, fun h => by omega⟩
    | succ k ih =>
      intro t ht
      have htT : t < T := by omega
      have hih := (ih (t + 1) (by omega)).1
      have b1 := (gseq_bounds hl hgm hg hs hr.le T (t + 1)).1
      have hp := pvar_mono_s2 hs hlt hg t
      have hp0 := pvar_pos hs hg t
      rw [gseq_lt _ _ _ _ _ htT, gseq_lt _ _ _ _ _ htT]
      have hA : 0 < 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) := by
        have : 0 < gam * (sig2 + pvar s2 sig2 t) / lam := by positivity
        nlinarith [mul_nonneg hr.le b1]
      have hB : 1 + gam * (sig2 + pvar s2 sig2 t) / lam + rho * gseq lam gam sig2 s2 rho T (t + 1) <
          1 + gam * (sig2 + pvar s2' sig2 t) / lam + rho * gseq lam gam sig2 s2' rho T (t + 1) := by
        have : gam * (sig2 + pvar s2 sig2 t) / lam < gam * (sig2 + pvar s2' sig2 t) / lam :=
          div_lt_div_of_pos_right (by nlinarith) hl
        nlinarith [mul_le_mul_of_nonneg_left hih hr.le]
      have := one_div_lt_one_div_of_lt hA hB
      exact ⟨by linarith, fun _ => by linarith⟩
  refine ⟨fun t ht => ⟨?_, fund_ric hN hl hgm hg hs hsb hr hr1 t, ?_, ?_⟩, ?_⟩
  · have hdc := dir_dl_pos hC t
    have hdr := dir_dl_pos hR t
    have hlc : C.lam = lam := rfl
    have hlr : R.lam = lam := rfl
    show 1 - ((fundLQ N lam gam sig2 s2 sb2 rho T).D t)⁻¹ * (lam • 1) = _
    rw [fund_D hN hl hgm hg hs hsb hr hr1, sp_inv hN (by linarith) (by linarith), one_sp hN, sp_smul hN,
      sp_mul hN, sp_sub hN, dir_g_eq hC (show t < C.T from ht), dir_g_eq hR (show t < R.T from ht), hlc, hlr]
    congr 2 <;> ring
  · rcases eq_or_lt_of_le hsb with h0 | h0
    · show gseq lam gam sig2 s2 rho T t ≤ gseq lam gam sig2 (s2 + N * sb2) rho T t
      rw [← h0, mul_zero, add_zero]
    · exact (hmono (show s2 < s2 + N * sb2 by
        have : (0 : ℝ) < N := by exact_mod_cast hN
        nlinarith) t ht).le
  · constructor
    · intro heq
      by_contra hne
      have h0 : 0 < sb2 := lt_of_le_of_ne hsb (Ne.symm hne)
      have := hmono (show s2 < s2 + N * sb2 by
        have : (0 : ℝ) < N := by exact_mod_cast hN
        nlinarith) t ht
      have heq' : gseq lam gam sig2 (s2 + N * sb2) rho T t = gseq lam gam sig2 s2 rho T t := heq
      linarith
    · intro h0
      show gseq lam gam sig2 (s2 + N * sb2) rho T t = gseq lam gam sig2 s2 rho T t
      rw [h0, mul_zero, add_zero]
  · obtain ⟨ac, hac, hac'⟩ := ((speeds).2.2.2.2.2.1 lam gam sig2 (s2 + N * sb2) rho hl hgm hg hsc' hr.le hr1).2.2.2
    obtain ⟨ar, har, har'⟩ := ((speeds).2.2.2.2.2.1 lam gam sig2 s2 rho hl hgm hg hs hr.le hr1).2.2.2
    exact ⟨ac, ar, hac, har, hac', har'⟩

theorem fundAim : FundAim := by
  intro N lam gam sig2 s2 sb2 rho T hN hl hgm hg hs hsb hr hr1 t ht ah
  set Q := fundLQ N lam gam sig2 s2 sb2 rho T
  set C := dirC N lam gam sig2 s2 sb2 rho T
  set R := dirR lam gam sig2 s2 rho T
  have hC := setC (T := T) hN hl hgm hg hs hsb hr hr1
  have hR := setR (T := T) (sb2 := sb2) (N := N) hN hl hgm hg hs hsb hr hr1
  have hlc : C.lam = lam := rfl
  have hlr : R.lam = lam := rfl
  have eC : dirC N lam gam sig2 s2 sb2 rho T = C := rfl
  have eR : dirR lam gam sig2 s2 rho T = R := rfl
  have hCg : C.gam = gam := rfl
  have hCs : C.sig2 = sig2 := rfl
  have hCr : C.rho = rho := rfl
  have hRg : R.gam = gam := rfl
  have hRs : R.sig2 = sig2 := rfl
  have hRr : R.rho = rho := rfl
  have hSC : ∀ u, 0 < gam * (sig2 + C.p u) := fun u => mul_pos hgm (by linarith [dir_p_pos hC u])
  have hSR : ∀ u, 0 < gam * (sig2 + R.p u) := fun u => mul_pos hgm (by linarith [dir_p_pos hR u])
  have hsv := sp_mulVec hN (v := ah)
  -- the Markowitz portfolio, as a spectral pair
  have hmkw : ∀ u, Q.mkw u ah =
      ((1 / (gam * (sig2 + C.p u))) • Pc N + (1 / (gam * (sig2 + R.p u))) • Pr N) *ᵥ ah := by
    intro u
    show (Q.S u)⁻¹ *ᵥ (1 *ᵥ ah - 0) = _
    rw [fund_S hN hl hgm hg hs hsb hr hr1, sp_inv hN (hSC u).ne' (hSR u).ne', sub_zero, one_mulVec,
      one_div, one_div]
  -- the aim, by backward induction
  have haim : ∀ u, u ≤ T → Q.aim u ah =
      ((C.ell u / (gam * sig2)) • Pc N + (R.ell u / (gam * sig2)) • Pr N) *ᵥ ah := by
    suffices h : ∀ k u, T - u = k → u ≤ T → Q.aim u ah =
        ((C.ell u / (gam * sig2)) • Pc N + (R.ell u / (gam * sig2)) • Pr N) *ᵥ ah from
      fun u => h _ u rfl
    intro k
    induction k with
    | zero =>
      intro u hu _
      rw [LQ.aim_ge Q (show Q.T ≤ u by show T ≤ u; omega), dir_ell_ge hC (show C.T ≤ u by show T ≤ u; omega),
        dir_ell_ge hR (show R.T ≤ u by show T ≤ u; omega)]
      simp
    | succ k ih =>
      intro u hu _
      have huT : u < T := by omega
      have hih := ih (u + 1) (by omega) (by omega)
      have hdc := dir_dl_pos hC u
      have hdr := dir_dl_pos hR u
      rw [LQ.aim_lt Q (show u < Q.T from huT), hmkw, hih]
      rw [show Q.rho = rho from rfl, fund_S hN hl hgm hg hs hsb hr hr1, fund_ric hN hl hgm hg hs hsb hr hr1, sp_smul hN, sp_add hN,
        mulVec_mulVec, sp_mul hN, mulVec_mulVec, sp_mul hN, ← smul_mulVec, sp_smul hN, ← add_mulVec,
        sp_add hN,
        show gam * (sig2 + C.p u) + rho * C.a (u + 1) = C.d u - C.lam by
          simp only [Dir.d, hCg, hCs, hCr, hlc]; ring,
        show gam * (sig2 + R.p u) + rho * R.a (u + 1) = R.d u - R.lam by
          simp only [Dir.d, hRg, hRs, hRr, hlr]; ring,
        sp_inv hN hdc.ne' hdr.ne', mulVec_mulVec, sp_mul hN,
        dir_ell_rec hC (show u < C.T from huT), dir_ell_rec hR (show u < R.T from huT)]
      have e1 : gam * (sig2 + C.p u) * (1 / (gam * (sig2 + C.p u))) = 1 := by
        rw [mul_one_div_cancel (hSC u).ne']
      have e2 : gam * (sig2 + R.p u) * (1 / (gam * (sig2 + R.p u))) = 1 := by
        rw [mul_one_div_cancel (hSR u).ne']
      rw [e1, e2]
      congr 3
      · simp only [eC, Dir.d, hCg, hCs, hCr, hlc] at hdc ⊢; field_simp
      · simp only [eR, Dir.d, hRg, hRs, hRr, hlr] at hdr ⊢; field_simp
  have hpc_eq : C.p t = pc N s2 sb2 sig2 t := rfl
  have hpr_eq : R.p t = pr s2 sig2 t := rfl
  have hfc : C.factor t / (gam * (sig2 + C.p t)) = C.ell t / (gam * sig2) := by
    have hne : sig2 + C.p t ≠ 0 := by linarith [dir_p_pos hC t]
    rw [Dir.factor, show C.sig2 = sig2 from rfl]; have := hSC t; field_simp
  have hfr : R.factor t / (gam * (sig2 + R.p t)) = R.ell t / (gam * sig2) := by
    have hne : sig2 + R.p t ≠ 0 := by linarith [dir_p_pos hR t]
    rw [Dir.factor, show R.sig2 = sig2 from rfl]; have := hSR t; field_simp
  refine ⟨by rw [haim t ht.le, hsv], by rw [hmkw, hsv, hpc_eq, hpr_eq], ?_, ?_⟩
  · rw [haim t ht.le, hmkw, pc_sp_v hN, pc_sp_v hN, smul_smul, ← hfc, div_eq_mul_one_div]
  · rw [haim t ht.le, hmkw, pr_sp_v hN, pr_sp_v hN, smul_smul, ← hfr, div_eq_mul_one_div]

/-- Claim 032, parts 1-4. -/
theorem proof : Standalone.M5LearningAimTwoSpeeds.statement :=
  ⟨twoVariances, twoSpeeds, learningFactor, fundAim, separation⟩

end

end Novel.M5LearningAimTwoSpeedsProof

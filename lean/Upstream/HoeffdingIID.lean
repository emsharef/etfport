import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.IdentDistrib

/-!
# AX-06: Hoeffding's inequality for bounded iid variables (maurer2009empirical Theorem 1)

This mirrors ledger entry AX-06 (`ledger/AXIOMS.md`, audited ok on 2026-09-28). The source statement
(p.1): if `Z, Z_1, ..., Z_n` are i.i.d. with values in `[0, 1]` and `δ > 0`, then with probability at
least `1 - δ`, `E Z - (1/n) Σ Z_i ≤ √(ln(1/δ)/(2n))`.

`HoeffdingIID` holds the source's one-sided statement for given data. As the auditor asked, `δ` is
restricted to `(0, 1)`, where the theorem has content. For `δ ≥ 1`, `ln(1/δ) ≤ 0` and Lean's
`Real.sqrt` returns `0`.

**Instance.** `hoeffdingIID` proves the structure for every probability space, every `n ≥ 1`, every
i.i.d. `[0,1]`-valued family and every `δ ∈ (0, 1)`. It uses Mathlib's machine-checked Hoeffding
inequality (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`), with the variance proxy from
Mathlib's Hoeffding lemma (`hasSubgaussianMGF_of_mem_Icc`). This instance is the faithful model of
every field, not a degenerate one. The theorem is taken from Mathlib, not re-proved (AGENTS.md rules
6 and 21), so the ledger's disclosed degenerate instance (`n = 1`, `Z = 0`) is a special case of it
and no longer needed.
-/

namespace Upstream.Hoeffding

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- AX-06 for given data: `Z = Z0`, `Z_1, ..., Z_n = Z i`, the level `δ`. -/
structure HoeffdingIID {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (Z : Fin n → Ω → ℝ) (Z0 : Ω → ℝ) (δ : ℝ) : Prop where
  bound : IsProbabilityMeasure P → 1 ≤ n → iIndepFun Z P → (∀ i, IdentDistrib (Z i) Z0 P P) →
    (∀ ω, Z0 ω ∈ Set.Icc (0 : ℝ) 1) → (∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1) → 0 < δ → δ < 1 →
    1 - δ ≤ P.real {ω | P[Z0] - (1 / (n : ℝ)) * ∑ i, Z i ω ≤ Real.sqrt (Real.log (1 / δ) / (2 * n))}

/-- The instance: AX-06 holds for all data, by Mathlib's Hoeffding inequality. -/
theorem hoeffdingIID {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (Z : Fin n → Ω → ℝ) (Z0 : Ω → ℝ) (δ : ℝ) : HoeffdingIID P n Z Z0 δ := by
  refine ⟨fun hP hn hind hid h0 hZ hδ hδ1 => ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set E := P[Z0]
  set t := Real.sqrt (Real.log (1 / δ) / (2 * n)) with ht
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have ht2 : t ^ 2 = Real.log (1 / δ) / (2 * n) := Real.sq_sqrt (by positivity)
  -- centred summands `E - Z_i`, each sub-Gaussian with proxy `1/4`
  set X : Fin n → Ω → ℝ := fun i ω => E - Z i ω with hX
  have hmeanZ : ∀ i, P[Z i] = E := fun i => (hid i).integral_eq
  have hsub : ∀ i, HasSubgaussianMGF (X i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := Z i) (a := 0) (b := 1)
      (hid i).aemeasurable_fst (ae_of_all _ (hZ i))
    have := h.neg
    convert this using 1
    funext ω; simp [hX, hmeanZ i]
  have hindX : iIndepFun X P := hind.comp (fun _ x => E - x) (fun _ => by fun_prop)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindX (s := Finset.univ) (fun i _ => hsub i)
    (ε := n * t) (by positivity)
  have hc : ∑ _i : Fin n, ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (n : ℝ≥0) / 4 := by
    simp [Finset.sum_const, Finset.card_univ]; ring
  have hexp : Real.exp (-((n : ℝ) * t) ^ 2 / (2 * ((∑ _i : Fin n,
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ≥0) : ℝ))) = δ := by
    rw [hc]
    push_cast
    rw [mul_pow, ht2]
    have : -((n : ℝ) ^ 2 * (Real.log (1 / δ) / (2 * n))) / (2 * (n / 4)) = -Real.log (1 / δ) := by
      field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    simp
  rw [hexp] at hH
  -- the bad event lies in `{n t ≤ Σ (E - Z_i)}`
  set good := {ω | E - (1 / (n : ℝ)) * ∑ i, Z i ω ≤ t}
  have hbad : goodᶜ ⊆ {ω | (n : ℝ) * t ≤ ∑ i, X i ω} := by
    intro ω hω
    simp only [good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_ofPred_eq, hX, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [one_div] at hω
    have := mul_lt_mul_of_pos_left hω hnr
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hnr.ne', one_mul] at this
    linarith
  have hPb : P.real goodᶜ ≤ δ := (measureReal_mono hbad).trans hH
  have hsum : P.real good + P.real goodᶜ ≥ 1 := by
    have := measureReal_union_le good goodᶜ (μ := P)
    rw [Set.union_compl_self, probReal_univ] at this
    linarith
  linarith

end Upstream.Hoeffding

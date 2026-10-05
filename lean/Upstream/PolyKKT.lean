import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# AX-13: polyhedral KKT, optimality of a concave objective over a polyhedron via the normal cone

This mirrors ledger entry AX-13 (`ledger/AXIOMS.md`, audited ok on 2026-09-29 under the `cited`
convention): `rockafellar1970convex` Theorem 27.4 and Theorems 28.2-28.3. It is a hypothesis
structure for a cited result (AGENTS.md rule 6). The theorem is not proved here, and no Novel file
re-proves it.

For `f` concave and finite on `ℝ^ι` and a polyhedron `P = {x : a_l'x ≤ b_l for all l ∈ Λ}`, a point
`x ∈ P` maximizes `f` on `P` iff there are multipliers `η_l ≥ 0`, zero on slack constraints, such that
`Σ_l η_l a_l` is a supergradient of `f` at `x` (`0 ∈ ∂f(x) - A'η`). Finiteness of `f` on `ℝ^ι`
supplies the constraint qualification (`ri(dom f)` meets `P`) that the entry records.

**Instance (genuine, disclosed, as in the entry).** `kkt_inst` is the entry's first instance:
`f(x) = x - x²/2 - C(x - 1)` with `C(u) = 0.3u⁺ + 0.2u⁻` on the box `[0, 2]`. Its maximizer is the
kink `x = 1`, where the superdifferential `[-0.3, 0.2]` contains `0`.
-/

namespace Upstream.KKT

open Matrix

/-- The polyhedron `{x : a_l'x ≤ b_l for all l}`. -/
def polyhedron {ι Λ : Type} [Fintype ι] (a : Λ → ι → ℝ) (b : Λ → ℝ) : Set (ι → ℝ) :=
  {x | ∀ l, a l ⬝ᵥ x ≤ b l}

/-- AX-13 for one concave finite `f` and one constraint system. -/
structure PolyKKT {ι Λ : Type} [Fintype ι] [Fintype Λ] (f : (ι → ℝ) → ℝ) (a : Λ → ι → ℝ)
    (b : Λ → ℝ) : Prop where
  kkt : ConcaveOn ℝ Set.univ f → ∀ x ∈ polyhedron a b,
    (IsMaxOn f (polyhedron a b) x ↔
      ∃ η : Λ → ℝ, (∀ l, 0 ≤ η l) ∧ (∀ l, a l ⬝ᵥ x < b l → η l = 0) ∧
        ∀ y, f y ≤ f x + (∑ l, η l • a l) ⬝ᵥ (y - x))

/-! ### The entry's first instance -/

/-- `f(x) = x - x²/2 - 0.3(x - 1)⁺ - 0.2(1 - x)⁺`. -/
noncomputable def f1 (x : Fin 1 → ℝ) : ℝ :=
  x 0 - x 0 ^ 2 / 2 - 3 / 10 * max (x 0 - 1) 0 - 2 / 10 * max (1 - x 0) 0

/-- The box `[0, 2]`: `-x ≤ 0` and `x ≤ 2`. -/
def a1 : Fin 2 → Fin 1 → ℝ := ![fun _ => -1, fun _ => 1]

/-- Its right-hand side. -/
def b1 : Fin 2 → ℝ := ![0, 2]

lemma f1_le (y : Fin 1 → ℝ) : f1 y ≤ f1 (fun _ => 1) := by
  simp only [f1]
  rcases le_total (y 0) 1 with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; norm_num; nlinarith [sq_nonneg (y 0 - 1)]
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; norm_num; nlinarith [sq_nonneg (y 0 - 1)]

lemma f1_lt {y : Fin 1 → ℝ} (hy : y 0 ≠ 1) : f1 y < f1 (fun _ => 1) := by
  simp only [f1]
  rcases lt_or_gt_of_ne hy with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; norm_num; nlinarith [sq_nonneg (y 0 - 1)]
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; norm_num; nlinarith [sq_nonneg (y 0 - 1)]

/-- AX-13 holds for the entry's first instance. -/
theorem kkt_inst : PolyKKT f1 a1 b1 := by
  refine ⟨fun _ x hx => ⟨fun hmax => ?_, fun ⟨η, hη, hcs, hsg⟩ => ?_⟩⟩
  · -- the maximizer is the kink; the zero multiplier works
    have h1 : (fun _ => (1 : ℝ)) ∈ polyhedron a1 b1 := fun l => by
      fin_cases l <;> simp [a1, b1, dotProduct]
    have hx1 : x 0 = 1 := by
      by_contra hne
      exact absurd (hmax h1) (not_le.mpr (f1_lt hne))
    have hxe : x = fun _ => 1 := funext fun i => by rw [Subsingleton.elim i 0, hx1]
    refine ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => rfl, fun y => ?_⟩
    simp only [zero_smul, Finset.sum_const_zero, zero_dotProduct, add_zero, hxe]
    exact f1_le y
  · -- sufficiency: the supergradient inequality and complementary slackness
    intro y hy
    show f1 y ≤ f1 x
    have hdot : (∑ l, η l • a1 l) ⬝ᵥ (y - x) ≤ 0 := by
      rw [sum_dotProduct]
      refine Finset.sum_nonpos fun l _ => ?_
      rw [smul_dotProduct, smul_eq_mul, dotProduct_sub]
      rcases eq_or_lt_of_le (hx l) with he | hlt
      · have := hy l
        nlinarith [hη l]
      · rw [hcs l hlt, zero_mul]
    have := hsg y
    linarith

end Upstream.KKT

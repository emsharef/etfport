import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# AX-05 (i): the linear-programming vertex theorem, finiteness and count

This mirrors part (i) of ledger entry AX-05 (`ledger/AXIOMS.md`, audited ok on 2026-09-28 under the
`cited` convention): `bertsimas1997introduction` Theorem 2.3 and Corollary 2.1, and
`schrijver1986theory` section 8. It is a hypothesis structure for a cited result (AGENTS.md rule 6).
The theorem is not proved here, and no Novel file re-proves it.

- `polyhedron g h` is `P = {x ∈ ℝ^ι : g_l'x ≤ h_l for all l ∈ Λ}`, with `L = |Λ|` constraints in
  dimension `m = |ι|`.
- `LPVertex g h` holds part (i) for this constraint system. If `P` is nonempty and bounded, it has
  finitely many extreme points, at most `binom(L, m)` of them. The entry states this together with
  the reason, that each extreme point is the unique solution of `m` linearly independent active
  constraints. Only the finiteness and the count are carried, which is what claim 020 uses.
- Part (ii) of the entry (a maximum of an affine function at an extreme point) is not carried. Where
  it is needed, Mathlib's Krein-Milman results supply it, as the entry's Formal paragraph records;
  claim 020 does not need it.

**Instance (degenerate, disclosed; genuine, not vacuous).** `lpVertex_zero` is the case `m = 0`,
`L = 0`: the empty constraint system in `ℝ⁰`. Its polyhedron is the one-point space, nonempty and
bounded, and its only extreme point is that point, so the count `1 ≤ binom(0, 0) = 1` holds with
equality. It is degenerate because a faithful instance, for a general constraint system, would
re-derive the theorem, which rule 6 forbids.
-/

namespace Upstream.LP

open Matrix

/-- The polyhedron `{x : g_l'x ≤ h_l for all l}`. -/
def polyhedron {ι Λ : Type} [Fintype ι] (g : Λ → ι → ℝ) (h : Λ → ℝ) : Set (ι → ℝ) :=
  {x | ∀ l, g l ⬝ᵥ x ≤ h l}

/-- AX-05 (i) for one constraint system: a nonempty bounded polyhedron has finitely many extreme
points, at most `binom(L, m)`. -/
structure LPVertex {ι Λ : Type} [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ) : Prop where
  finite_card : (polyhedron g h).Nonempty → Bornology.IsBounded (polyhedron g h) →
    (Set.extremePoints ℝ (polyhedron g h)).Finite ∧
      (Set.extremePoints ℝ (polyhedron g h)).ncard ≤ (Fintype.card Λ).choose (Fintype.card ι)

/-! ### The disclosed degenerate instance -/

/-- The empty constraint system in `ℝ⁰`. -/
def g0 : Fin 0 → Fin 0 → ℝ := fun l => l.elim0

/-- Its right-hand side. -/
def h0 : Fin 0 → ℝ := fun l => l.elim0

/-- Its polyhedron is the single point of `ℝ⁰`. -/
theorem polyhedron_zero : polyhedron g0 h0 = {0} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨fun l => Fin.elim0 l, fun _ _ => Subsingleton.elim _ _⟩

/-- The premises hold: the polyhedron is nonempty and bounded. -/
theorem premises_zero : (polyhedron g0 h0).Nonempty ∧ Bornology.IsBounded (polyhedron g0 h0) := by
  rw [polyhedron_zero]
  exact ⟨Set.singleton_nonempty _, Bornology.isBounded_singleton⟩

/-- AX-05 (i) holds for the empty system in `ℝ⁰`: one extreme point, and `1 ≤ binom(0, 0)`. -/
theorem lpVertex_zero : LPVertex g0 h0 := by
  refine ⟨fun _ _ => ?_⟩
  rw [polyhedron_zero, extremePoints_singleton]
  refine ⟨Set.finite_singleton _, ?_⟩
  simp

end Upstream.LP

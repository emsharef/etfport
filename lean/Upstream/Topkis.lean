import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# AX-14: submodularity on products of chains, and its preservation under partial minimization

This mirrors ledger entry AX-14 (`ledger/AXIOMS.md`), `topkis1978minimizing` Theorems 3.1-3.2 and
4.3, in the entry's notation. It is a hypothesis structure for a cited result (AGENTS.md rules 6 and
21). The theorems are not proved here, and no Novel file re-proves them. The entry was audited ok on
2026-09-29 (ledger/AUDIT_LOG.md, AX-14 line for ef742763).

A *product of intervals* is `Set.univ.pi I` with each `I i` an interval (`OrdConnected`) in `ℝ`, with the
coordinatewise order: a sublattice of `ι → ℝ` whose factors are chains. `F` is *submodular* on `D` if
`F(x ⊓ y) + F(x ⊔ y) ≤ F x + F y`. It has *decreasing differences* in `(i, j)` if, with the other
coordinates fixed, the increment in coordinate `i` is nonincreasing in coordinate `j` (the source's
"antitone differences").
- `Pairwise` (Theorem 3.2): decreasing differences in every pair of coordinates imply submodularity.
- `Converse` (Theorem 3.1): submodularity implies decreasing differences in every pair.
- `PartialMin` (Theorem 4.3, with the entry's simplification that the infimum is attained): if `F` is
  submodular on a product `X × Y` of intervals and `min_{y ∈ Y} F(x, y)` is attained for every
  `x ∈ X`, then `V(x) = inf_{y ∈ Y} F(x, y)` is submodular on `X`.

**Instance (genuine, as in the entry).** `X = Y = [0, 1]` and `F(x, y) = -x y`. Its increment in `x` is
`-(x₂ - x₁) y`, nonincreasing in `y`. It is submodular, the infimum over `y` is attained at `y = 1`,
and `V(x) = -x` is submodular. The instance has a nonzero cross term. `inst_dd` proves its decreasing
differences in both coordinate orders, and `inst_pairwise`, `inst_converse` and `inst_partialMin` build
the three structures for it.
-/

namespace Upstream.Topkis

open Function

/-- A product of intervals. -/
def Box {ι : Type} (I : ι → Set ℝ) : Set (ι → ℝ) := Set.univ.pi I

/-- Submodularity on `D`. -/
def Submodular {ι : Type} (F : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, F (x ⊓ y) + F (x ⊔ y) ≤ F x + F y

/-- Decreasing differences in the pair `(i, j)` on `D`. -/
def DecDiff {ι : Type} [DecidableEq ι] (F : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) (i j : ι) : Prop :=
  ∀ x : ι → ℝ, ∀ s₁ s₂ t₁ t₂ : ℝ, s₁ ≤ s₂ → t₁ ≤ t₂ →
    update (update x i s₁) j t₁ ∈ D → update (update x i s₂) j t₂ ∈ D →
    update (update x i s₁) j t₂ ∈ D → update (update x i s₂) j t₁ ∈ D →
    F (update (update x i s₂) j t₂) - F (update (update x i s₁) j t₂) ≤
      F (update (update x i s₂) j t₁) - F (update (update x i s₁) j t₁)

/-- Theorem 3.2 for one function on one product of intervals. -/
structure Pairwise {ι : Type} [Fintype ι] [DecidableEq ι] (I : ι → Set ℝ) (F : (ι → ℝ) → ℝ) :
    Prop where
  sub : (∀ i, (I i).OrdConnected) → (∀ i j, i ≠ j → DecDiff F (Box I) i j) → Submodular F (Box I)

/-- Theorem 3.1 for one function on one product of intervals. -/
structure Converse {ι : Type} [Fintype ι] [DecidableEq ι] (I : ι → Set ℝ) (F : (ι → ℝ) → ℝ) :
    Prop where
  dd : (∀ i, (I i).OrdConnected) → Submodular F (Box I) → ∀ i j, i ≠ j → DecDiff F (Box I) i j

/-- Theorem 4.3 (infimum attained) for one function on one product `X × Y`, written on `ι ⊕ κ`. -/
structure PartialMin {ι κ : Type} [Fintype ι] [Fintype κ] (I : ι → Set ℝ) (J : κ → Set ℝ)
    (F : (ι → ℝ) → (κ → ℝ) → ℝ) : Prop where
  sub : (∀ i, (I i).OrdConnected) → (∀ k, (J k).OrdConnected) →
    Submodular (fun w : ι ⊕ κ → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) (Box (Sum.elim I J)) →
    (∀ x ∈ Box I, ∃ y ∈ Box J, ∀ y' ∈ Box J, F x y ≤ F x y') →
    Submodular (fun x => sInf (F x '' Box J)) (Box I)

/-! ### The entry's instance: `X = Y = [0, 1]`, `F(x, y) = -x y` -/

/-- The instance's function on `Fin 1 ⊕ Fin 1` coordinates. -/
def Fxy (x : Fin 1 → ℝ) (y : Fin 1 → ℝ) : ℝ := -(x 0 * y 0)

/-- The unit interval. -/
def unit : Fin 1 → Set ℝ := fun _ => Set.Icc 0 1

lemma mem_unit {x : Fin 1 → ℝ} : x ∈ Box unit ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  simp only [Box, unit, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  exact ⟨fun h => h 0, fun h i => by rw [Subsingleton.elim i 0]; exact h⟩

/-- `-x y` is submodular on `[0, 1]²`, and by the entry `V(x) = min_y -x y = -x` is submodular. -/
theorem inst_sub :
    Submodular (fun w : Fin 1 ⊕ Fin 1 → ℝ => Fxy (w ∘ Sum.inl) (w ∘ Sum.inr)) (Box (Sum.elim unit unit)) := by
  intro x _ y _
  simp only [Fxy, Function.comp, Pi.inf_apply, Pi.sup_apply]
  set a := x (Sum.inl 0); set b := x (Sum.inr 0); set c := y (Sum.inl 0); set d := y (Sum.inr 0)
  rcases le_total a c with h1 | h1 <;> rcases le_total b d with h2 | h2
  · simp [min_eq_left h1, max_eq_right h1, min_eq_left h2, max_eq_right h2]
  · rw [min_eq_left h1, max_eq_right h1, min_eq_right h2, max_eq_left h2]; nlinarith
  · rw [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h2]; nlinarith
  · simp [min_eq_right h1, max_eq_left h1, min_eq_right h2, max_eq_left h2]

theorem inst_attained : ∀ x ∈ Box unit, ∃ y ∈ Box unit, ∀ y' ∈ Box unit, Fxy x y ≤ Fxy x y' :=
  fun x hx => ⟨fun _ => 1, mem_unit.mpr ⟨zero_le_one, le_rfl⟩, fun y' hy' => by
    have := mem_unit.mp hx; have := mem_unit.mp hy'
    simp only [Fxy]; nlinarith⟩

/-- The instance's partial minimum is `-x`. -/
lemma inst_V (x : Fin 1 → ℝ) (hx : x ∈ Box unit) : sInf (Fxy x '' Box unit) = -x 0 := by
  have hx' := mem_unit.mp hx
  refine IsLeast.csInf_eq ⟨⟨fun _ => 1, mem_unit.mpr ⟨zero_le_one, le_rfl⟩, by simp [Fxy]⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have := mem_unit.mp hy
  simp only [Fxy]; nlinarith

/-- The entry's instance satisfies the conclusion of `PartialMin`: `V(x) = -x` is submodular. -/
theorem inst_V_sub : Submodular (fun x => sInf (Fxy x '' Box unit)) (Box unit) := by
  intro x hx y hy
  have hxy : x ⊓ y ∈ Box unit := by
    rw [mem_unit] at *; simp only [Pi.inf_apply]; exact ⟨le_min hx.1 hy.1, (min_le_left _ _).trans hx.2⟩
  have hxy' : x ⊔ y ∈ Box unit := by
    rw [mem_unit] at *; simp only [Pi.sup_apply]; exact ⟨hx.1.trans (le_max_left _ _), max_le hx.2 hy.2⟩
  simp only
  rw [inst_V _ hx, inst_V _ hy, inst_V _ hxy, inst_V _ hxy']
  simp only [Pi.inf_apply, Pi.sup_apply]
  rcases le_total (x 0) (y 0) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; linarith

/-- The instance's function on `[0, 1]²`, written on `Fin 1 ⊕ Fin 1`. -/
def F₂ (w : Fin 1 ⊕ Fin 1 → ℝ) : ℝ := Fxy (w ∘ Sum.inl) (w ∘ Sum.inr)

/-- `-xy` has decreasing differences in both orders of its two coordinates. -/
theorem inst_dd : ∀ i j, i ≠ j → DecDiff F₂ (Box (Sum.elim unit unit)) i j := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j <;>
    rw [Subsingleton.elim i 0] at * <;> rw [Subsingleton.elim j 0] at *
  · exact absurd rfl hij
  · intro x s₁ s₂ t₁ t₂ h1 h2 _ _ _ _
    simp only [F₂, Fxy, Function.comp, update_self, ne_eq, reduceCtorEq, not_false_eq_true,
      update_of_ne]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  · intro x s₁ s₂ t₁ t₂ h1 h2 _ _ _ _
    simp only [F₂, Fxy, Function.comp, update_self, ne_eq, reduceCtorEq, not_false_eq_true,
      update_of_ne]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  · exact absurd rfl hij

/-- The three structures hold for the entry's instance. -/
theorem inst_pairwise : Pairwise (Sum.elim unit unit) F₂ := ⟨fun _ _ => inst_sub⟩

theorem inst_converse : Converse (Sum.elim unit unit) F₂ := ⟨fun _ _ => inst_dd⟩

theorem inst_partialMin : PartialMin unit unit Fxy := ⟨fun _ _ _ _ => inst_V_sub⟩

end Upstream.Topkis

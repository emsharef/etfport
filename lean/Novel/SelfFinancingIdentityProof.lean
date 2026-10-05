import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Standalone.SelfFinancingIdentity

/-!
# Proof of claim 001: self-financing identity at a quarterly review (M0)

Finite summation distributes over `x⁺ᵢ = x⁻ᵢ + uᵢ`; everything else is linear arithmetic.
The lemmas are stated for an arbitrary instrument count `N`; the statement specializes them to
`N = m + n`.
-/

namespace Novel.SelfFinancingIdentityProof

open Finset Standalone.SelfFinancingIdentity

variable {N : ℕ}

/-- Total post-trade holdings are total pre-trade holdings plus the net trade. -/
lemma sum_postHoldings (x u : Fin N → ℝ) :
    ∑ i, postHoldings x u i = ∑ i, x i + ∑ i, u i := by
  simp only [postHoldings, sum_add_distrib]

lemma identity (x : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ) :
    ∑ i, postHoldings x u i + postCash h u C + C u = ∑ i, x i + h := by
  rw [sum_postHoldings, postCash]
  ring

lemma fundingEquivalence (x : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ) :
    FundedLongOnly x h u C ↔ BudgetForm x h u C := by
  have hs : ∑ i, (x i + u i) = ∑ i, x i + ∑ i, u i := sum_add_distrib
  unfold FundedLongOnly BudgetForm postHoldings postCash
  refine and_congr Iff.rfl ?_
  constructor <;> intro H <;> linarith

lemma costBound (x : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ)
    (hC : 0 ≤ C u) (hF : FundedLongOnly x h u C) : 0 ≤ C u ∧ C u ≤ ∑ i, x i + h := by
  obtain ⟨hx, hh⟩ := hF
  have hsum : 0 ≤ ∑ i, postHoldings x u i := sum_nonneg fun i _ => hx i
  have hid := identity x h u C
  exact ⟨hC, by linarith⟩

lemma zeroTrade (x : Fin N → ℝ) (h : ℝ) (C : (Fin N → ℝ) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hh : 0 ≤ h) (hC : C 0 = 0) :
    FundedLongOnly x h 0 C ∧ postHoldings x 0 = x ∧ postCash h 0 C = h ∧
      ∑ i, postHoldings x 0 i + postCash h 0 C = ∑ i, x i + h := by
  have hx0 : postHoldings x 0 = x := by
    funext i
    simp [postHoldings]
  have hh0 : postCash h 0 C = h := by
    simp [postCash, hC]
  refine ⟨⟨fun i => ?_, ?_⟩, hx0, hh0, ?_⟩
  · rw [hx0]
    exact hx i
  · rw [hh0]
    exact hh
  · rw [hx0, hh0]

theorem proof : Standalone.SelfFinancingIdentity.statement :=
  ⟨fun _ _ x h u C => identity x h u C,
   fun _ _ x h u C => fundingEquivalence x h u C,
   fun _ _ x h u C hC hF => costBound x h u C hC hF,
   fun _ _ x h C hx hh hC => zeroTrade x h C hx hh hC⟩

end Novel.SelfFinancingIdentityProof

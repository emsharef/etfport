import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Real.Basic

/-!
# Claim 001: self-financing identity at a quarterly review (M0)

Statement only; the proof is `Novel/SelfFinancingIdentityProof.lean`.

Instruments are indexed by `Fin (m + n)` (m active funds, n ETFs). At one review, `x` is the
initial dollar holdings `x⁻`, `h` the initial cash `h⁻`, `u` the trade vector and `C` the
shareholder switching cost at that review, a real function of the trade. No property of `C` is
assumed except where a part of the statement names one.

Each part carries only the hypotheses its proof uses. The claim fixes nonnegative `x⁻`, `h⁻`
and `C_t(u)` for the whole statement; the formal parts drop those hypotheses where unused, so
the formal statement is at least as strong as the prose.
-/

namespace Standalone.SelfFinancingIdentity

open Finset

variable {N : ℕ}

/-- Post-trade risky holdings `x⁺ = x⁻ + u`. -/
def postHoldings (x u : Fin N → ℝ) : Fin N → ℝ := fun i => x i + u i

/-- Post-trade cash `h⁺ = h⁻ - Σᵢ uᵢ - C(u)`. -/
def postCash (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ) : ℝ := h - ∑ i, u i - C u

/-- The funded long-only restrictions on the post-trade position: `x⁺ᵢ ≥ 0` for every `i`
and `h⁺ ≥ 0`. -/
def FundedLongOnly (x : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ) : Prop :=
  (∀ i, 0 ≤ postHoldings x u i) ∧ 0 ≤ postCash h u C

/-- The same restrictions written in terms of the pre-trade position and the trade:
`x⁻ᵢ + uᵢ ≥ 0` for every `i` and `Σᵢ (x⁻ᵢ + uᵢ) + C(u) ≤ Σᵢ x⁻ᵢ + h⁻`. -/
def BudgetForm (x : Fin N → ℝ) (h : ℝ) (u : Fin N → ℝ) (C : (Fin N → ℝ) → ℝ) : Prop :=
  (∀ i, 0 ≤ x i + u i) ∧ ∑ i, (x i + u i) + C u ≤ ∑ i, x i + h

/-- Part 1, the self-financing identity: for every trade, with no sign or feasibility
hypothesis, `Σᵢ x⁺ᵢ + h⁺ + C(u) = Σᵢ x⁻ᵢ + h⁻`. -/
def Identity : Prop :=
  ∀ (m n : ℕ) (x : Fin (m + n) → ℝ) (h : ℝ) (u : Fin (m + n) → ℝ)
    (C : (Fin (m + n) → ℝ) → ℝ),
    ∑ i, postHoldings x u i + postCash h u C + C u = ∑ i, x i + h

/-- Part 2: for every trade, the funded long-only restrictions hold exactly when the
budget form holds. -/
def FundingEquivalence : Prop :=
  ∀ (m n : ℕ) (x : Fin (m + n) → ℝ) (h : ℝ) (u : Fin (m + n) → ℝ)
    (C : (Fin (m + n) → ℝ) → ℝ),
    FundedLongOnly x h u C ↔ BudgetForm x h u C

/-- Part 3: for every trade whose cost is nonnegative and which satisfies the funded
long-only restrictions, `0 ≤ C(u) ≤ Σᵢ x⁻ᵢ + h⁻`. -/
def CostBound : Prop :=
  ∀ (m n : ℕ) (x : Fin (m + n) → ℝ) (h : ℝ) (u : Fin (m + n) → ℝ)
    (C : (Fin (m + n) → ℝ) → ℝ),
    0 ≤ C u → FundedLongOnly x h u C → 0 ≤ C u ∧ C u ≤ ∑ i, x i + h

/-- Part 4: if the initial holdings and cash are nonnegative and `C(0) = 0`, the zero trade
satisfies the funded long-only restrictions, leaves holdings and cash unchanged, and
preserves total holdings plus cash. -/
def ZeroTrade : Prop :=
  ∀ (m n : ℕ) (x : Fin (m + n) → ℝ) (h : ℝ) (C : (Fin (m + n) → ℝ) → ℝ),
    (∀ i, 0 ≤ x i) → 0 ≤ h → C 0 = 0 →
      FundedLongOnly x h 0 C ∧ postHoldings x 0 = x ∧ postCash h 0 C = h ∧
        ∑ i, postHoldings x 0 i + postCash h 0 C = ∑ i, x i + h

/-- Claim 001, all four parts. -/
def statement : Prop :=
  Identity ∧ FundingEquivalence ∧ CostBound ∧ ZeroTrade

end Standalone.SelfFinancingIdentity

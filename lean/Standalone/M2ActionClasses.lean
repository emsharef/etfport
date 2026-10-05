import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Standalone.M2ScoreAccounting

/-!
# Claim 004: nested M2 action classes have optimal one-quarter actions

Statement only; the proof is `Novel/M2ActionClassesProof.lean`.

Uses the M2 objects of `Standalone/M2ScoreAccounting.lean`, the formal statement of claim 003:
the cash function `cash` (M2's `k(w)`), the cost `tau`, the classes `F`, `E`, `N`, and the
belief-average criterion `beliefScore` (M2's `Q̄_0`). As there, the counts m, n, K are arbitrary,
and M2's m = 1, n ∈ {1, 2}, K = 2 is a special case. Holdings `Inst m n → ℝ` carry the product
(coordinate) topology and the sup-metric bornology. Convexity, concavity, maxima and
boundedness are Mathlib's `Convex`, `ConcaveOn`, `IsMaxOn` and `Bornology.IsBounded`;
`Convex ℝ A` and `ConcaveOn ℝ univ f` unfold to exactly the claim's `t w + (1-t) z` definitions.

Every part lists only the hypotheses its proof uses. M2 hypotheses that no part needs are not
assumed: rates below one, `w̄ᵢ ≤ 1`, scenario or belief masses summing to one, centered shocks.
-/

namespace Standalone.M2ActionClasses

open Standalone.M2ScoreAccounting

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- Initial position data of an M2 instance: positive pre-trade wealth, nonnegative dollar
holdings and cash, and initial normalized holdings within the position limits. These imply
`w⁻ ≥ 0`, `k⁻ ≥ 0` and `Σᵢ w⁻ᵢ + k⁻ = 1`. -/
def InitialPosition (D : Data m n K S) : Prop :=
  0 < W0 D ∧ (∀ i, 0 ≤ D.x0 i) ∧ 0 ≤ D.h0 ∧ ∀ i, w0 D i ≤ D.wbar i

/-- Nonnegative purchase and sale rates. -/
def RatesNonneg (D : Data m n K S) : Prop := ∀ i, 0 ≤ D.kplus i ∧ 0 ≤ D.kminus i

/-- The hypotheses under which the criterion is concave: `γ ≥ 0`, nonnegative rates,
nonnegative scenario masses and nonnegative belief masses. -/
def ConcavityInputs (D : Data m n K S) {T : Type} (pi : T → ℝ) : Prop :=
  0 ≤ D.gamma ∧ RatesNonneg D ∧ (∀ s, 0 ≤ D.q s) ∧ ∀ t, 0 ≤ pi t

/-- `N ⊆ E ⊆ F`, and each class is nonempty. -/
def NestedNonempty : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S), InitialPosition D →
    N D ⊆ E D ∧ E D ⊆ F D ∧ (N D).Nonempty ∧ (E D).Nonempty ∧ (F D).Nonempty

/-- Each class is closed and bounded, with no hypothesis. -/
def ClosedBounded : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S),
    IsClosed (F D) ∧ IsClosed (E D) ∧ IsClosed (N D) ∧
    Bornology.IsBounded (F D) ∧ Bornology.IsBounded (E D) ∧ Bornology.IsBounded (N D)

/-- Each class is convex when the rates are nonnegative. -/
def ClassesConvex : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S), RatesNonneg D →
    Convex ℝ (F D) ∧ Convex ℝ (E D) ∧ Convex ℝ (N D)

/-- The criterion `Q̄_0` is continuous for any belief, and concave on all holdings under
`ConcavityInputs`. -/
def CriterionContinuousConcave : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi : T → ℝ),
    Continuous (beliefScore D par pi) ∧
    (ConcavityInputs D pi → ConcaveOn ℝ Set.univ (beliefScore D par pi))

/-- `Q̄_0` attains a maximum on each of N, E and F, for any belief (no concavity needed); every
choice of maximizers satisfies `max_N ≤ max_E ≤ max_F`. -/
def AttainmentAndValueChain : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi : T → ℝ), InitialPosition D →
    (∃ w ∈ N D, IsMaxOn (beliefScore D par pi) (N D) w) ∧
    (∃ w ∈ E D, IsMaxOn (beliefScore D par pi) (E D) w) ∧
    (∃ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w) ∧
    ∀ wN wE wF, wN ∈ N D → IsMaxOn (beliefScore D par pi) (N D) wN →
      wE ∈ E D → IsMaxOn (beliefScore D par pi) (E D) wE →
      wF ∈ F D → IsMaxOn (beliefScore D par pi) (F D) wF →
        beliefScore D par pi wN ≤ beliefScore D par pi wE ∧
        beliefScore D par pi wE ≤ beliefScore D par pi wF

/-- Claim 004, all parts. -/
def statement : Prop :=
  NestedNonempty ∧ ClosedBounded ∧ ClassesConvex ∧ CriterionContinuousConcave ∧
    AttainmentAndValueChain

end Standalone.M2ActionClasses

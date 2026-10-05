import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Instances.Real.Lemmas
import Standalone.M7TwoStageExactnessLoss

/-!
# Claim 044: two reviews, one fund, one ETF and cash with a binding budget

Statement only; the proof is `Novel/M7TwoReviewsBindingBudgetProof.lean`.

The model is the claim's own two-review coordinates (`Two ι Z`). The instruments are any finite type
`ι`; the claim's case is `ι` with two elements (the fund and the ETF). `Z` is the finite state set
tomorrow, with weights `q > 0` and gross returns `g > 0`. The data are the moments `(μ_0, Σ_0)` and
`(μ_1(z), Σ_1(z))`, with each `Σ` symmetric and positive semidefinite (the claim's positive definite
matrices are a special case). The rest are `γ`, `β ∈ (0, 1]`, the rates `κ^±_i` with `κ⁻_i < 1`,
finite caps `x̄`, the incumbents `0 ≤ x⁻ ≤ x̄` and the cash `h⁻_0 > 0`.
- `u_0 = x_0 - x⁻` and `u_1(z) = x_1(z) - g(z) ∘ x_0` are the trades.
- `h⁺_0 = h⁻_0 - 1'u_0 - C(u_0)` and `h⁺_1(z) = h⁺_0 - 1'u_1(z) - C(u_1(z))` are the cash after trading.
- `J = Q_0(x_0) - C(u_0) + β Σ_z q(z) [Q_1(x_1(z); z) - C(u_1(z))]` is the objective.

Scope (PM, rule 6b; the claim as approved). Formal: parts 1, 2, 3(a)-(c) and 4(a), 4(b), 4(d), with
the following limits.
- Part 2's sufficiency is proved directly by a Lagrangian bound, with no citation. Its necessity is
  conditional on ledger entry AX-13 (polyhedral KKT), through claim 104's hypothesis `AX13`. The
  lifting of the costs follows claim 104's part 0 and is proved here for the two-review program.
- Part 3(b) is in its weak form, as approved.
- Part 3(c):
  - The test is formal as stated, over some multipliers of the myopic policy's own tomorrow
    problems (`MyopicTest`).
  - Formal consequences: the multiplier is pinned in a state that trades some instrument strictly
    inside its box (`Pinned`); the exact slack-tomorrow condition and the held-today band
    (`SlackTest`); and `β Σ q g_i t_{1,i} = 0` for an instrument traded strictly inside its box
    today, assuming today's budget is also slack (`MyopicTest`).
  - The two signs are formal as tangent bounds (`Signs`). Along instrument `i`, with the other
    holdings fixed, the root objective lies below the line of slope
    `r = S_i - β Σ q η_1 (1 + κ⁺_i)` through the myopic root, in both directions. So the one-sided
    derivative along the purchase direction is at most `r`, and along the sale direction at most
    `-r`. For `r < 0`, no larger purchase raises the root objective; for `r > 0`, no smaller one
    does.
  - Paper-level: the exact value of the one-sided derivative (equality with `r`); strict
    improvement in the opposite direction; the multiplier-set interval case; and the joint
    comparative static (Not shown in the claim).
- Part 4(a) is formal in these coordinates: each review's holdings maximize that review's one-review
  Lagrangian. The link to claim 110's `One` coordinates is paper-level.
- Part 4(b): the band in the marginal and the marginal's slope `-γ Σ_{0,ii}` along the coordinate
  are formal. The bound "at most" on the width in holdings under a slack budget today is paper-level.
- Part 4(c), the uncapped ETF (finite caps here; PM) and the Checks are paper-level.
-/

namespace Standalone.M7TwoReviewsBindingBudget

noncomputable section

/-- The claim's two-review instance: instruments `ι`, states tomorrow `Z`. -/
structure Two (ι Z : Type) where
  q : Z → ℝ
  g : Z → ι → ℝ
  mu0 : ι → ℝ
  S0 : ι → ι → ℝ
  mu1 : Z → ι → ℝ
  S1 : Z → ι → ι → ℝ
  gamma : ℝ
  beta : ℝ
  kp : ι → ℝ
  km : ι → ℝ
  xbar : ι → ℝ
  xm : ι → ℝ
  h : ℝ

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-- The quadratic form `x'Σx`. -/
def quad (S : ι → ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * S i j * x j

/-- `Σ` symmetric and positive semidefinite. -/
def PSD (S : ι → ι → ℝ) : Prop := (∀ i j, S i j = S j i) ∧ ∀ v, 0 ≤ quad S v

/-- The standing assumptions. -/
def Hyp (P : Two ι Z) : Prop :=
  0 < P.gamma ∧ 0 < P.beta ∧ P.beta ≤ 1 ∧ 0 < P.h ∧ PSD P.S0 ∧ (∀ z, PSD (P.S1 z)) ∧
    (∀ z, 0 < P.q z) ∧ (∀ z i, 0 < P.g z i) ∧
    ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i ∧ P.km i < 1 ∧ 0 ≤ P.xm i ∧ P.xm i ≤ P.xbar i

/-- A proportional cost `κ⁺u⁺ + κ⁻u⁻`. -/
def pc (kp km u : ℝ) : ℝ := kp * max u 0 + km * max (-u) 0

/-- The trade cost `C(u) = Σ_i [κ⁺_i u_i⁺ + κ⁻_i u_i⁻]`. -/
def cost (P : Two ι Z) (u : ι → ℝ) : ℝ := ∑ i, pc (P.kp i) (P.km i) (u i)

/-- A review's objective `μ'x - (γ/2) x'Σx`. -/
def Qv (mu : ι → ℝ) (S : ι → ι → ℝ) (γ : ℝ) (x : ι → ℝ) : ℝ := ∑ i, mu i * x i - γ / 2 * quad S x

/-- A review's smooth marginal `(μ - γΣx)_i`. -/
def marg (mu : ι → ℝ) (S : ι → ι → ℝ) (γ : ℝ) (x : ι → ℝ) (i : ι) : ℝ := mu i - γ * ∑ j, S i j * x j

def Q0 (P : Two ι Z) (x : ι → ℝ) : ℝ := Qv P.mu0 P.S0 P.gamma x

def Q1 (P : Two ι Z) (z : Z) (x : ι → ℝ) : ℝ := Qv (P.mu1 z) (P.S1 z) P.gamma x

/-- Today's marginal `g_{0,i}`. -/
def g0 (P : Two ι Z) (x : ι → ℝ) (i : ι) : ℝ := marg P.mu0 P.S0 P.gamma x i

/-- Tomorrow's marginal `g_{1,i}` in state `z`. -/
def g1 (P : Two ι Z) (z : Z) (x : ι → ℝ) (i : ι) : ℝ := marg (P.mu1 z) (P.S1 z) P.gamma x i

/-- The holdings carried into state `z`: `g(z) ∘ x_0`. -/
def carry (P : Two ι Z) (z : Z) (x0 : ι → ℝ) : ι → ℝ := fun i => P.g z i * x0 i

/-- Cash after today's trade, `h⁺_0`. -/
def h0 (P : Two ι Z) (x0 : ι → ℝ) : ℝ := P.h - ∑ i, (x0 i - P.xm i) - cost P (x0 - P.xm)

/-- Cash after tomorrow's trade in state `z`, `h⁺_1(z)`. -/
def h1 (P : Two ι Z) (x0 : ι → ℝ) (x1 : Z → ι → ℝ) (z : Z) : ℝ :=
  h0 P x0 - ∑ i, (x1 z i - carry P z x0 i) - cost P (x1 z - carry P z x0)

/-- The long-only caps `0 ≤ x ≤ x̄`. -/
def Box (P : Two ι Z) (x : ι → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ P.xbar i

/-- The feasible policies `(x_0, {x_1(z)})`: both boxes and both funded budgets. -/
def Feas (P : Two ι Z) : Set ((ι → ℝ) × (Z → ι → ℝ)) :=
  {X | Box P X.1 ∧ (∀ z, Box P (X.2 z)) ∧ 0 ≤ h0 P X.1 ∧ ∀ z, 0 ≤ h1 P X.1 X.2 z}

/-- The two-review objective. -/
def J (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : ℝ :=
  Q0 P X.1 - cost P (X.1 - P.xm) +
    P.beta * ∑ z, P.q z * (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1))

/-- An optimal policy. -/
def Optimal (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : Prop := X ∈ Feas P ∧ IsMaxOn (J P) (Feas P) X

/-! ### Part 1 -/

/-- The last review's value `V_1(x⁻, h⁻; z)`, the supremum over its feasible set. -/
def V1 (P : Two ι Z) (z : Z) (p : (ι → ℝ) × ℝ) : ℝ :=
  sSup ((fun x => Q1 P z x - cost P (x - p.1)) ''
    {x | Box P x ∧ 0 ≤ p.2 - ∑ i, (x i - p.1 i) - cost P (x - p.1)})

/-- The pairs `(x⁻, h⁻)` from which the last review is feasible. -/
def Dom (P : Two ι Z) : Set ((ι → ℝ) × ℝ) :=
  {p | ∃ x, Box P x ∧ 0 ≤ p.2 - ∑ i, (x i - p.1 i) - cost P (x - p.1)}

/-- The root objective `Q_0(x_0) - C(u_0) + β E V_1(g ∘ x_0, h⁺_0(x_0); z)`. -/
def RootObj (P : Two ι Z) (x0 : ι → ℝ) : ℝ :=
  Q0 P x0 - cost P (x0 - P.xm) + P.beta * ∑ z, P.q z * V1 P z (carry P z x0, h0 P x0)

/-- The root's feasible set `{0 ≤ x_0 ≤ x̄, h⁺_0(x_0) ≥ 0}`. -/
def RootSet (P : Two ι Z) : Set (ι → ℝ) := {x0 | Box P x0 ∧ 0 ≤ h0 P x0}

/-- Part 1. An optimal policy exists, and the objective is concave on the (convex) feasible set.
`V_1` is concave on its domain and nondecreasing in the cash. Every root-feasible `x_0` carries into
that domain in every state, and the root objective is concave on the root's feasible set. -/
def Structure : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    (∃ X, Optimal P X) ∧ ConcaveOn ℝ (Feas P) (J P) ∧
    (∀ z, ConcaveOn ℝ (Dom P) (V1 P z) ∧
      ∀ (x : ι → ℝ) (a b : ℝ), (x, a) ∈ Dom P → a ≤ b → V1 P z (x, a) ≤ V1 P z (x, b)) ∧
    (∀ x0 ∈ RootSet P, ∀ z, (carry P z x0, h0 P x0) ∈ Dom P) ∧
    ConcaveOn ℝ (RootSet P) (RootObj P)

/-! ### Part 2 -/

/-- `t ∈ T(u)`, claim 102's trade-sign slope set at the trade `u`: `{κ⁺}` after a purchase, `{-κ⁻}`
after a sale, and `[-κ⁻, κ⁺]` with no trade. -/
def Slope (kp km u t : ℝ) : Prop := -km ≤ t ∧ t ≤ kp ∧ (0 < u → t = kp) ∧ (u < 0 → t = -km)

/-- The box signs of a line's value `R` at `x ∈ [0, x̄]`, in normal-cone form: `R ≤ 0` below the cap
and `R ≥ 0` above zero (so `R = 0` strictly inside). -/
def BoxSign (xbar x R : ℝ) : Prop := (x < xbar → R ≤ 0) ∧ (0 < x → 0 ≤ R)

/-- The dynamic cash price `η̂_0 = η_0 + β Σ_z q(z) η_1(z)`. -/
def etaHat (P : Two ι Z) (η0 : ℝ) (η1 : Z → ℝ) : ℝ := η0 + P.beta * ∑ z, P.q z * η1 z

/-- The incumbent value of a unit of `i` carried into `z`: `s_i(z) = η_1(z) + (1 + η_1(z)) t_{1,i}(z)`. -/
def sval (η1 : Z → ℝ) (t1 : Z → ι → ℝ) (z : Z) (i : ι) : ℝ := η1 z + (1 + η1 z) * t1 z i

/-- The discounted expected marked incumbent value `S_i = β Σ_z q(z) g_i(z) s_i(z)`. -/
def Sinc (P : Two ι Z) (η1 : Z → ℝ) (t1 : Z → ι → ℝ) (i : ι) : ℝ :=
  P.beta * ∑ z, P.q z * P.g z i * sval η1 t1 z i

/-- Tomorrow's lines in every state: `η_1(z) ≥ 0` with `η_1(z) h⁺_1(z) = 0`, slopes
`t_1(z) ∈ T(u_1(z))`, and the box signs of `g_{1,i} - η_1 - (1 + η_1) t_{1,i}`. -/
def Tomorrow (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) (η1 : Z → ℝ) (t1 : Z → ι → ℝ) : Prop :=
  ∀ z, 0 ≤ η1 z ∧ η1 z * h1 P X.1 X.2 z = 0 ∧
    ∀ i, Slope (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i) (t1 z i) ∧
      BoxSign (P.xbar i) (X.2 z i) (g1 P z (X.2 z) i - η1 z - (1 + η1 z) * t1 z i)

/-- Today's lines with the dynamic cash price and the incumbent values: `η_0 ≥ 0` with
`η_0 h⁺_0 = 0`, slopes `t_0 ∈ T(u_0)`, and the box signs of `g_{0,i} + S_i - η̂_0 - (1 + η̂_0) t_{0,i}`. -/
def Root (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) (η0 : ℝ) (η1 : Z → ℝ) (t0 : ι → ℝ)
    (t1 : Z → ι → ℝ) : Prop :=
  0 ≤ η0 ∧ η0 * h0 P X.1 = 0 ∧
    ∀ i, Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) ∧
      BoxSign (P.xbar i) (X.1 i)
        (g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i)

/-- Part 2's lines: multipliers and slopes, with the same `t_1(z)` in both sets of lines. -/
def Lines (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : Prop :=
  ∃ η0 η1 t0 t1, Tomorrow P X η1 t1 ∧ Root P X η0 η1 t0 t1

/-- Part 2, sufficiency (no citation): a feasible policy satisfying the lines is optimal. -/
def Sufficient : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X ∈ Feas P, Lines P X → Optimal P X

/-- Part 2, necessity (under AX-13): an optimal policy satisfies the lines. -/
def Necessary : Prop :=
  Standalone.M7TwoStageExactnessLoss.AX13 → ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X, Optimal P X → Lines P X

/-- Part 2's readings of `s_i(z)` from tomorrow's regimes: tomorrow's marginal if held strictly inside
the box, the scaled purchase threshold if bought, the scaled sale threshold if sold, always between
the two thresholds, and cut by the one-sided line at zero or at the cap. -/
def Readings : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) η1 t1,
    Tomorrow P X η1 t1 → ∀ z i,
      (0 < X.2 z i → X.2 z i < P.xbar i → sval η1 t1 z i = g1 P z (X.2 z) i) ∧
      (carry P z X.1 i < X.2 z i → sval η1 t1 z i = η1 z + (1 + η1 z) * P.kp i) ∧
      (X.2 z i < carry P z X.1 i → sval η1 t1 z i = η1 z - (1 + η1 z) * P.km i) ∧
      (η1 z - (1 + η1 z) * P.km i ≤ sval η1 t1 z i ∧ sval η1 t1 z i ≤ η1 z + (1 + η1 z) * P.kp i) ∧
      (X.2 z i = 0 → 0 < P.xbar i → g1 P z (X.2 z) i ≤ sval η1 t1 z i) ∧
      (X.2 z i = P.xbar i → 0 < P.xbar i → sval η1 t1 z i ≤ g1 P z (X.2 z) i)

/-! ### Part 3 -/

/-- Part 3(a): with a slack budget tomorrow in every state, `η_1 = 0`, `η̂_0 = η_0`, `s_i(z) = t_{1,i}(z)`
in `[-κ⁻_i, κ⁺_i]`, and `S_i` lies in `[-β Σ q g_i κ⁻_i, β Σ q g_i κ⁺_i]`. -/
def SlackTomorrow : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t1, Tomorrow P X η1 t1 → (∀ z, 0 < h1 P X.1 X.2 z) →
      (∀ z, η1 z = 0) ∧ etaHat P η0 η1 = η0 ∧
      (∀ z i, sval η1 t1 z i = t1 z i ∧ -P.km i ≤ t1 z i ∧ t1 z i ≤ P.kp i) ∧
      ∀ i, -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ≤ Sinc P η1 t1 i ∧
        Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * P.kp i

/-- Part 3(b): the bounds on `S_i` in the inputs, and the purchase and sale conditions they give
(non-strict). -/
def Bounds : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → ∀ i,
      let lo := P.beta * ∑ z, P.q z * P.g z i * (η1 z - (1 + η1 z) * P.km i)
      let hi := P.beta * ∑ z, P.q z * P.g z i * (η1 z + (1 + η1 z) * P.kp i)
      let e := etaHat P η0 η1
      lo ≤ Sinc P η1 t1 i ∧ Sinc P η1 t1 i ≤ hi ∧
      (P.xm i < X.1 i → e + (1 + e) * P.kp i - hi ≤ g0 P X.1 i) ∧
      (X.1 i < P.xm i → g0 P X.1 i ≤ e - (1 + e) * P.km i - lo)

/-- Today's one-review feasible set `{0 ≤ x ≤ x̄, h⁺_0(x) ≥ 0}` (the root's). -/
def Feas0 (P : Two ι Z) : Set (ι → ℝ) := RootSet P

/-- Tomorrow's one-review feasible set in state `z` from `(g(z) ∘ x_0, h⁺_0(x_0))`. -/
def Feas1 (P : Two ι Z) (z : Z) (x0 : ι → ℝ) : Set (ι → ℝ) :=
  {x | Box P x ∧ 0 ≤ h0 P x0 - ∑ i, (x i - carry P z x0 i) - cost P (x - carry P z x0)}

/-- The repeated one-review (myopic) policy: today's one-review optimum, then in each state the
one-review optimum from the carried holdings and today's cash. -/
def Myopic (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) : Prop :=
  X.1 ∈ Feas0 P ∧ IsMaxOn (fun x => Q0 P x - cost P (x - P.xm)) (Feas0 P) X.1 ∧
    ∀ z, X.2 z ∈ Feas1 P z X.1 ∧
      IsMaxOn (fun x => Q1 P z x - cost P (x - carry P z X.1)) (Feas1 P z X.1) (X.2 z)

/-- Part 3(c). Under AX-13, the myopic policy is dynamically optimal iff its root holdings satisfy
the root lines with some multipliers and slopes of its own tomorrow problems (tomorrow's lines at
its own tomorrow holdings) and some admissible `η_0`, `t_0`. If the myopic root buys `i` strictly
inside its box with today's budget slack, its own line is `g_{0,i} = κ⁺_i`. The root line's value at
`i`, for every admissible `η_0, t_0` and any tomorrow multipliers, is then the residual
`S_i - β Σ q η_1 (1 + κ⁺_i)`, so the lines force it to vanish. When `i` is held strictly inside its
box tomorrow in every state, `S_i = β Σ q g_i g_{1,i}`. With today's budget slack and tomorrow's slack
in every state, an instrument traded strictly inside its box today needs `β Σ q g_i t_{1,i} = 0`. -/
def MyopicTest : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → ∀ X, Myopic P X →
    (Standalone.M7TwoStageExactnessLoss.AX13 →
      (Optimal P X ↔ ∃ η0 η1 t0 t1, Tomorrow P X η1 t1 ∧ Root P X η0 η1 t0 t1)) ∧
    (∀ i, 0 < h0 P X.1 → P.xm i < X.1 i → X.1 i < P.xbar i →
      g0 P X.1 i = P.kp i ∧
      (∀ (η0 : ℝ) (η1 : Z → ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ), 0 ≤ η0 → η0 * h0 P X.1 = 0 →
        Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) →
        g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i =
          Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i)) ∧
      (∀ η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 →
        Sinc P η1 t1 i = P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i)) ∧
      (∀ η1 t1, Tomorrow P X η1 t1 → (∀ z, 0 < X.2 z i ∧ X.2 z i < P.xbar i) →
        Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * g1 P z (X.2 z) i)) ∧
    ∀ i, 0 < h0 P X.1 → 0 < X.1 i → X.1 i < P.xbar i → X.1 i ≠ P.xm i →
      ∀ η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → (∀ z, 0 < h1 P X.1 X.2 z) →
        P.beta * ∑ z, P.q z * P.g z i * t1 z i = 0

/-- Part 3(c): tomorrow's cash price is pinned in a state where some instrument is traded strictly
inside its box: any two sets of tomorrow's multipliers agree there. -/
def Pinned : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η1 t1 η1' t1', Tomorrow P X η1 t1 → Tomorrow P X η1' t1' →
      ∀ z i, X.2 z i ≠ carry P z X.1 i → 0 < X.2 z i → X.2 z i < P.xbar i → η1 z = η1' z

/-- Part 3(c), the exact slack-tomorrow condition: with a slack budget tomorrow in every state, the
root lines read with `η_1 = 0`, `S_i = β Σ q g_i t_{1,i}` and `η̂_0 = η_0`. An instrument held today
strictly inside its box then has `g_{0,i} + β Σ q g_i t_{1,i}` in its scaled band. -/
def SlackTest : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 → (∀ z, 0 < h1 P X.1 X.2 z) →
      (Root P X η0 η1 t0 t1 ↔ 0 ≤ η0 ∧ η0 * h0 P X.1 = 0 ∧
        ∀ i, Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) ∧
          BoxSign (P.xbar i) (X.1 i)
            (g0 P X.1 i + P.beta * ∑ z, P.q z * P.g z i * t1 z i - η0 - (1 + η0) * t0 i)) ∧
      (Root P X η0 η1 t0 t1 → ∀ i, 0 < X.1 i → X.1 i < P.xbar i → X.1 i = P.xm i →
        η0 - (1 + η0) * P.km i ≤ g0 P X.1 i + P.beta * ∑ z, P.q z * P.g z i * t1 z i ∧
          g0 P X.1 i + P.beta * ∑ z, P.q z * P.g z i * t1 z i ≤ η0 + (1 + η0) * P.kp i)

/-- Part 3(c), the two signs, along instrument `i` with the other holdings fixed. Today's budget is
slack at the myopic root, which buys `i` strictly inside its box. For any multipliers of its own
tomorrow problems, with `r = S_i - β Σ q η_1 (1 + κ⁺_i)`, the root objective lies below the line of
slope `r` through the myopic root along coordinate `i`, in both directions. So `r < 0` means any
larger purchase lowers the root objective (hoarding), and `r > 0` means any smaller purchase lowers
it (front-loading). -/
def Signs : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z), Hyp P → ∀ X, Myopic P X →
    ∀ η1 t1, Tomorrow P X η1 t1 → ∀ i, 0 < h0 P X.1 → P.xm i < X.1 i → X.1 i < P.xbar i →
      let r := Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i)
      ∀ t, 0 ≤ t →
        (Function.update X.1 i (X.1 i + t) ∈ RootSet P →
          RootObj P (Function.update X.1 i (X.1 i + t)) ≤ RootObj P X.1 + t * r) ∧
        (Function.update X.1 i (X.1 i - t) ∈ RootSet P →
          RootObj P (Function.update X.1 i (X.1 i - t)) ≤ RootObj P X.1 - t * r)

/-! ### Part 4 -/

/-- A one-review Lagrangian `μ'x - (γ/2) x'Σx - (1 + η) C(x - c) - η 1'(x - c)`. -/
def lagOne (P : Two ι Z) (mu : ι → ℝ) (S : ι → ι → ℝ) (c : ι → ℝ) (η : ℝ) (x : ι → ℝ) : ℝ :=
  Qv mu S P.gamma x - (1 + η) * cost P (x - c) - η * ∑ i, (x i - c i)

/-- Part 4(a): the two-scalar rule at both reviews. Today's holdings maximize the one-review
Lagrangian with `μ_0 + S` and the dynamic cash price `η̂_0` over the box. Tomorrow's maximize the
state's own one-review Lagrangian at `η_1(z)` from the carried holdings. -/
def TwoScalar : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 →
      Box P X.1 → (∀ z, Box P (X.2 z)) →
      IsMaxOn (lagOne P (P.mu0 + Sinc P η1 t1) P.S0 P.xm (etaHat P η0 η1)) {x | Box P x} X.1 ∧
      ∀ z, IsMaxOn (lagOne P (P.mu1 z) (P.S1 z) (carry P z X.1) (η1 z)) {x | Box P x} (X.2 z)

/-- Part 4(b): claim 029's band at the root in the marginal `g_{0,i} + S_i`. Strictly inside the
box it equals the scaled purchase threshold after a purchase and the scaled sale threshold after a
sale, and lies between them without trade, an interval of width `(1 + η̂_0)(κ⁺_i + κ⁻_i)`. Along
coordinate `i` the marginal has slope `-γ Σ_{0,ii}`, which gives the width in holdings. -/
def Band : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → ∀ i,
      let e := etaHat P η0 η1
      let G := g0 P X.1 i + Sinc P η1 t1 i
      (0 < X.1 i → X.1 i < P.xbar i →
        (P.xm i < X.1 i → G = e + (1 + e) * P.kp i) ∧
        (X.1 i < P.xm i → G = e - (1 + e) * P.km i) ∧
        (X.1 i = P.xm i → e - (1 + e) * P.km i ≤ G ∧ G ≤ e + (1 + e) * P.kp i)) ∧
      (e + (1 + e) * P.kp i) - (e - (1 + e) * P.km i) = (1 + e) * (P.kp i + P.km i) ∧
      ∀ [DecidableEq ι] (s : ℝ),
        g0 P (Function.update X.1 i s) i = g0 P X.1 i - P.gamma * P.S0 i i * (s - X.1 i)

/-- Part 4(d): an instrument with `κ⁺_i = κ⁻_i = 0` has `S_i = β Σ q g_i η_1`. Strictly inside its box
its line reads `g_{0,i} = η̂_0 - β Σ q g_i η_1`: it anticipates the budget through the cash price
alone. -/
def Costless : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → ∀ i,
      P.kp i = 0 → P.km i = 0 →
      Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * η1 z ∧
      (0 < X.1 i → X.1 i < P.xbar i →
        g0 P X.1 i = etaHat P η0 η1 - P.beta * ∑ z, P.q z * P.g z i * η1 z)

/-- Claim 044 (parts 1-4, within the scope above). -/
def statement : Prop :=
  Structure ∧ Sufficient ∧ Necessary ∧ Readings ∧ SlackTomorrow ∧ Bounds ∧ MyopicTest ∧ Pinned ∧
    SlackTest ∧ Signs ∧ TwoScalar ∧ Band ∧ Costless

end

end Standalone.M7TwoReviewsBindingBudget

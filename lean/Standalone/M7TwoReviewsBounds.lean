import Standalone.M7TwoReviewsBindingBudget
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Claim 046 (claim 045 refiled): the two-review criterion with a binding budget, bounded in the inputs

Statement only; the proof is `Novel/M7TwoReviewsBoundsProof.lean`.

The model and the lines are claim 044's (`Two ι Z`, `Tomorrow`, `Root`, `Sinc`, `etaHat`; Q-04). The
claim's `Σ_AE ≥ 0` is `Cov`: nonnegative off-diagonal covariances tomorrow, with positive variances
(the claim's `Σ` positive definite). It covers the claim's two instruments and any finite set.
Expectations are `Σ_z q(z)(·)`.

- Part 1:
  - (a) `CashPriceBound`: in every state, from any admissible multiplier `η`, the multiplier
    `min(η, η̄)` is admissible with some slopes;
  - (b) `SlackWhenCovered`: when `h⁺_0 ≥ need(z)`, the multiplier `0` is admissible in state `z` at any
    point with tomorrow's lines;
  - (c) `DynamicCashPrice`, for any tomorrow family, the AX-13 joint family among them:
    - `η_1(z) ≤ η̄(z)` in every state that trades something or whose budget is slack;
    - hence `η_0 ≤ η̂_0 ≤ η_0 + β E[η̄]` when no state trades nothing with all cash spent;
    - `η̂_0 = η_0` when every state is covered and `h⁺_0 > 0`.
    For the per-state selection `min(η_1, η̄)`, which is admissible state by state, the bound holds
    without the restriction, and a zero selection exists whenever every state is covered.
- Part 2 (`Brackets`): the brackets on `S_i` and `R_i = S_i - β E[η_1](1 + κ⁺_i)`, and the two
  sufficient sign conditions, for any admissible multipliers and slopes.
- Part 3:
  - `InteriorTrade`, today's budget slack: at a root whose own one-review line at `i` holds as an
    equality (`g_{0,i} = κ⁺_i` after a purchase, `-κ⁻_i` after a sale; claim 044's `foc_gen`), the root
    line at `i` is `R_i` for a purchase and `S_i - β E[η_1](1 - κ⁻_i)` for a sale. So an interior trade
    is consistent iff that one equation holds.
  - `CostlessIdentity`: for an instrument costless on both sides with a slack budget tomorrow,
    `S_i = 0 = β E[η_1]`, so the equation holds identically.
  - `InteriorTradeBinding`, today's budget binding at the myopic root with cash price `η_0^my`: the
    root line at an interior purchase is `S_i - (η_0 - η_0^my + β E[η_1])(1 + κ⁺_i)`. It vanishes iff
    `S_i` equals that, which with `η_0 ≥ 0` needs `S_i ≥ (β E[η_1] - η_0^my)(1 + κ⁺_i)`, an inequality.
    The sale form uses `1 - κ⁻_i`.
- Part 4, in math's revised form (919441d4):
  - `HedgeTerm`: at the reduced point `(a^my, p^red)` (the ETF coordinate moved, the rest as at the
    myopic root), take the myopic lines `g_{0,A} = κ⁺_A`, `g_{0,E} = 0`, a frictionless ETF, today's
    budget slack, and the ETF's root line. Then the fund's root line value with its purchase slope is
    `R^red_A - ρ_0 R^red_E`, with `ρ_0 = Σ_{0,AE}/Σ_{0,EE}`.
  - `ConcaveSign`, the one-variable step: take `J^red` concave on the fund's box with maximizer
    `a^dyn`, and a lower function `φ` equal to it at `a^my`. A positive right derivative of `φ` at
    `a^my` gives `a^dyn > a^my`, and a negative left derivative gives `a^dyn < a^my`. These are the
    revision's one-sided-derivative inequalities, with no envelope equality.

Paper-level:
- part 4's link between `ConcaveSign`'s objects and claim 044's root problem. There `J^red(a)` is the
  maximum of the root objective over the ETF at fund holding `a`, and it is concave (partial
  maximization). `φ = J(·, p^red)`, and its one-sided derivatives at `a^my` are the root line's
  values over tomorrow's admissible multipliers (the extremes; `V_1` is concave, not differentiable).
  Claim 044's Lagrangian bound (a supergradient inequality) gives only `D⁺ ≤ s ≤ D⁻`, the opposite of
  the needed direction. The needed direction is the characterization of `V_1`'s one-sided
  derivatives as extremes over its multipliers (Danskin with AX-13), so this link is paper-level (PM's
  scope note);
- 1(c)'s "`η̂_0 = η_0` whenever `h⁺_0 ≥ need`" for the joint family in the edge `h⁺_0 = 0 = need`. There a
  state that trades nothing with all cash spent can carry a positive joint multiplier. It is formal for
  `h⁺_0 > 0`, and for a per-state selection in every case (leanb's note to math and red);
- the joint (AX-13) family's existence (claim 044's `Necessary`), and the not-shown joint admissibility
  of the per-state selection;
- part 3's "essentially only" (non-genericity);
- the readings of the brackets;
- the Checks.
-/

namespace Standalone.M7TwoReviewsBounds

open Standalone.M7TwoReviewsBindingBudget Set

noncomputable section

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-- State `z`'s lines at `X` with multiplier `e` and slopes `t`: the body of claim 044's `Tomorrow`. -/
def LinesAt (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) (z : Z) (e : ℝ) (t : ι → ℝ) : Prop :=
  0 ≤ e ∧ e * h1 P X.1 X.2 z = 0 ∧
    ∀ i, Slope (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i) (t i) ∧
      BoxSign (P.xbar i) (X.2 z i) (g1 P z (X.2 z) i - e - (1 + e) * t i)

/-- The claim's `Σ_AE ≥ 0` tomorrow, with positive variances: nonnegative off-diagonal covariances
and a positive diagonal in every state. -/
def Cov (P : Two ι Z) : Prop := (∀ z i j, i ≠ j → 0 ≤ P.S1 z i j) ∧ ∀ z i, 0 < P.S1 z i i

/-- `η̄(z) = max_i (μ_{1,i}(z) - κ⁺_i)⁺/(1 + κ⁺_i)`: the best expected return tomorrow net of its
purchase rate, scaled. -/
def etaBar (P : Two ι Z) (z : Z) : ℝ := ⨆ i, max (P.mu1 z i - P.kp i) 0 / (1 + P.kp i)

/-- Instrument `i`'s solo target tomorrow, `x̂_i(z) = (μ_{1,i}(z) - κ⁺_i)⁺/(γ Σ_{1,ii}(z))`. -/
def xhat (P : Two ι Z) (z : Z) (i : ι) : ℝ := max (P.mu1 z i - P.kp i) 0 / (P.gamma * P.S1 z i i)

/-- The cash the solo targets would need from the marked holdings,
`need(z) = Σ_i (1 + κ⁺_i)(x̂_i(z) - g_i(z) x_{0,i})⁺`. -/
def need (P : Two ι Z) (z : Z) (x0 : ι → ℝ) : ℝ :=
  ∑ i, (1 + P.kp i) * max (xhat P z i - carry P z x0 i) 0

/-- The residual `R_i = S_i - β E[η_1](1 + κ⁺_i)` (claim 044 part 3(c)). -/
def Resid (P : Two ι Z) (η1 : Z → ℝ) (t1 : Z → ι → ℝ) (i : ι) : ℝ :=
  Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + P.kp i)

/-- Part 1(a): at a feasible policy, in every state, from any admissible multiplier `e` with slopes,
`min(e, η̄(z))` is admissible with some slopes. -/
def CashPriceBound : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ z e t, LinesAt P X z e t →
      ∃ e' t', LinesAt P X z e' t' ∧ e' ≤ etaBar P z ∧ e' ≤ e

/-- Part 1(b): if the cash carried covers the solo-target purchases, `h⁺_0 ≥ need(z)`, then from any
admissible multiplier in state `z` the multiplier `0` is admissible with some slopes: the state's
budget does not bind. -/
def SlackWhenCovered : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ z e t, LinesAt P X z e t → need P z X.1 ≤ h0 P X.1 →
      ∃ t', LinesAt P X z 0 t'

/-- Part 1(c). Take any tomorrow family, the AX-13 joint family among them.
- `η_1(z) ≤ η̄(z)` in every state that trades something or whose budget is slack.
- If that holds in every state, then `η_0 ≤ η̂_0 ≤ η_0 + β E[η̄]`.
- With `h⁺_0 > 0` and every state covered, `η_1 = 0` and `η̂_0 = η_0`.
- There is always an admissible per-state selection with `η_1 ≤ η̄`, which obeys the bound on `η̂_0`.
- When every state is covered, a selection with `η_1 = 0` exists (`h⁺_0 = 0` allowed). -/
def DynamicCashPrice : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ (η0 : ℝ) η1 t1, 0 ≤ η0 → Tomorrow P X η1 t1 →
      (∀ z, (¬ (∀ i, X.2 z i = carry P z X.1 i) ∨ 0 < h1 P X.1 X.2 z) → η1 z ≤ etaBar P z) ∧
      ((∀ z, ¬ (∀ i, X.2 z i = carry P z X.1 i) ∨ 0 < h1 P X.1 X.2 z) →
        η0 ≤ etaHat P η0 η1 ∧ etaHat P η0 η1 ≤ η0 + P.beta * ∑ z, P.q z * etaBar P z) ∧
      (0 < h0 P X.1 → (∀ z, need P z X.1 ≤ h0 P X.1) → (∀ z, η1 z = 0) ∧ etaHat P η0 η1 = η0) ∧
      (∃ η1' t1', Tomorrow P X η1' t1' ∧ (∀ z, η1' z ≤ etaBar P z ∧ η1' z ≤ η1 z) ∧
        η0 ≤ etaHat P η0 η1' ∧ etaHat P η0 η1' ≤ η0 + P.beta * ∑ z, P.q z * etaBar P z) ∧
      ((∀ z, need P z X.1 ≤ h0 P X.1) →
        ∃ t1', Tomorrow P X (fun _ => 0) t1' ∧ etaHat P η0 (fun _ => 0) = η0)

/-- Part 2: for any admissible tomorrow multipliers and slopes,
- `S_i ≤ β E[g_i (η_1 + (1 + η_1) κ⁺_i)]` and `-β E[g_i] κ⁻_i ≤ S_i`;
- `R_i` lies in `β [E[η_1 (g_i (1 - κ⁻_i) - 1 - κ⁺_i)] - κ⁻_i E[g_i], E[η_1 (g_i - 1)](1 + κ⁺_i) + κ⁺_i E[g_i]]`;
- so `R_i < 0` (hoarding) when the upper end is negative, and `R_i > 0` (front-loading) when the lower
  end is positive. -/
def Brackets : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η1 t1, Tomorrow P X η1 t1 → ∀ i,
      let lo := P.beta * (∑ z, P.q z * (η1 z * (P.g z i * (1 - P.km i) - 1 - P.kp i)) -
        P.km i * ∑ z, P.q z * P.g z i)
      let hi := P.beta * ((∑ z, P.q z * (η1 z * (P.g z i - 1))) * (1 + P.kp i) +
        P.kp i * ∑ z, P.q z * P.g z i)
      Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * (η1 z + (1 + η1 z) * P.kp i) ∧
      -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ≤ Sinc P η1 t1 i ∧
      lo ≤ Resid P η1 t1 i ∧ Resid P η1 t1 i ≤ hi ∧
      (hi < 0 → Resid P η1 t1 i < 0) ∧ (0 < lo → 0 < Resid P η1 t1 i)

/-- Part 3: take a root `x_0` with today's budget slack, an instrument `i` traded strictly inside its
box, and its own one-review line an equality (`g_{0,i} = κ⁺_i` after a purchase, `g_{0,i} = -κ⁻_i` after
a sale). Then for any admissible `η_0` and today's slope, and any tomorrow multipliers:
- after a purchase, the root line's value at `i` is `R_i = S_i - β E[η_1](1 + κ⁺_i)`;
- after a sale, it is `S_i - β E[η_1](1 - κ⁻_i)`.
So the root lines hold at `i` iff that one equation does. -/
def InteriorTrade : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) (i : ι), 0 < h0 P X.1 → 0 < X.1 i → X.1 i < P.xbar i →
    ∀ (η0 : ℝ) (η1 : Z → ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ), 0 ≤ η0 → η0 * h0 P X.1 = 0 →
      Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) →
      let v := g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i
      (P.xm i < X.1 i → g0 P X.1 i = P.kp i →
        v = Resid P η1 t1 i ∧ (BoxSign (P.xbar i) (X.1 i) v ↔ Resid P η1 t1 i = 0)) ∧
      (X.1 i < P.xm i → g0 P X.1 i = -P.km i →
        v = Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 - P.km i) ∧
        (BoxSign (P.xbar i) (X.1 i) v ↔
          Sinc P η1 t1 i = P.beta * (∑ z, P.q z * η1 z) * (1 - P.km i)))

/-- Part 4's hedge term. Let the reduced point `xr` differ from the myopic root `xm` only in the ETF
coordinate `E`. Assume:
- the myopic lines hold: `g_{0,A}(xm) = κ⁺_A` (the fund bought) and `g_{0,E}(xm) = 0`;
- the ETF is frictionless (`κ⁺_E = 0`) with `Σ_{0,EE} > 0`;
- the ETF's root line holds at `xr` with today's budget slack, `g_{0,E}(xr) + S_E - η̂ = 0` with
  `η̂ = β E[η_1]`.
Then the fund's root line value at `xr` with its purchase slope,
`g_{0,A}(xr) + S_A - η̂ - (1 + η̂) κ⁺_A`, equals `R_A - ρ_0 R_E` with `ρ_0 = Σ_{0,AE}/Σ_{0,EE}`. -/
def HedgeTerm : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (xm xr : ι → ℝ) (A E : ι), A ≠ E → (∀ j, j ≠ E → xr j = xm j) → 0 < P.S0 E E →
    g0 P xm A = P.kp A → g0 P xm E = 0 → P.kp E = 0 →
    ∀ (η1 : Z → ℝ) (t1 : Z → ι → ℝ),
      g0 P xr E + Sinc P η1 t1 E - etaHat P 0 η1 = 0 →
      g0 P xr A + Sinc P η1 t1 A - etaHat P 0 η1 - (1 + etaHat P 0 η1) * P.kp A =
        Resid P η1 t1 A - P.S0 A E / P.S0 E E * Resid P η1 t1 E

/-- Part 4's one-variable step (the one-sided-derivative inequalities, no envelope equality). Take
`J^red` concave on `[lo, hi]` with maximizer `a^dyn`, and `a^my` strictly inside. Let `φ ≤ J^red` on
`[lo, hi]` with `φ(a^my) = J^red(a^my)`. A positive right derivative of `φ` at `a^my` gives
`a^dyn > a^my`, and a negative left derivative gives `a^dyn < a^my`. -/
def ConcaveSign : Prop :=
  ∀ (Jred φ : ℝ → ℝ) (lo hi am ad : ℝ), ConcaveOn ℝ (Icc lo hi) Jred → ad ∈ Icc lo hi →
    IsMaxOn Jred (Icc lo hi) ad → am ∈ Ioo lo hi → (∀ a ∈ Icc lo hi, φ a ≤ Jred a) →
    φ am = Jred am →
    (∀ v, HasDerivWithinAt φ v (Ici am) am → 0 < v → am < ad) ∧
    (∀ v, HasDerivWithinAt φ v (Iic am) am → v < 0 → ad < am)

/-- Part 3, the costless identity: for an instrument costless on both sides with tomorrow's budget
slack in every state, `S_i = 0 = β E[η_1]`, so part 3's equation holds whatever tomorrow does. -/
def CostlessIdentity : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) η1 t1 (i : ι), Tomorrow P X η1 t1 → P.kp i = 0 → P.km i = 0 →
      (∀ z, 0 < h1 P X.1 X.2 z) → Sinc P η1 t1 i = 0 ∧ P.beta * ∑ z, P.q z * η1 z = 0

/-- Part 3 with today's budget binding at the myopic root, whose own line at an interior trade is
`g_{0,i} = η_0^my + (1 + η_0^my) κ⁺_i` (purchase) or `η_0^my - (1 + η_0^my) κ⁻_i` (sale).
- The root line at `i` is `S_i - (η_0 - η_0^my + β E[η_1])(1 + κ⁺_i)` for a purchase, and the same
  with `1 - κ⁻_i` for a sale. It vanishes iff `S_i` equals that.
- With `η_0 ≥ 0`, the root line's vanishing needs `S_i ≥ (β E[η_1] - η_0^my)(1 + κ⁺_i)` (resp.
  `(1 - κ⁻_i)`), an inequality. -/
def InteriorTradeBinding : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (X : (ι → ℝ) × (Z → ι → ℝ)) (i : ι), 0 < X.1 i → X.1 i < P.xbar i →
    ∀ (η0 emy : ℝ) (η1 : Z → ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ),
      Slope (P.kp i) (P.km i) (X.1 i - P.xm i) (t0 i) →
      let v := g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i
      let c := η0 - emy + P.beta * ∑ z, P.q z * η1 z
      (P.xm i < X.1 i → g0 P X.1 i = emy + (1 + emy) * P.kp i →
        v = Sinc P η1 t1 i - c * (1 + P.kp i) ∧
        (BoxSign (P.xbar i) (X.1 i) v ↔ Sinc P η1 t1 i = c * (1 + P.kp i)) ∧
        (0 ≤ η0 → BoxSign (P.xbar i) (X.1 i) v →
          (P.beta * ∑ z, P.q z * η1 z - emy) * (1 + P.kp i) ≤ Sinc P η1 t1 i)) ∧
      (X.1 i < P.xm i → g0 P X.1 i = emy - (1 + emy) * P.km i →
        v = Sinc P η1 t1 i - c * (1 - P.km i) ∧
        (BoxSign (P.xbar i) (X.1 i) v ↔ Sinc P η1 t1 i = c * (1 - P.km i)) ∧
        (0 ≤ η0 → BoxSign (P.xbar i) (X.1 i) v →
          (P.beta * ∑ z, P.q z * η1 z - emy) * (1 - P.km i) ≤ Sinc P η1 t1 i))

/-- Claim 046 (paper-level parts in the module note). -/
def statement : Prop :=
  CashPriceBound ∧ SlackWhenCovered ∧ DynamicCashPrice ∧ Brackets ∧ InteriorTrade ∧
    CostlessIdentity ∧ InteriorTradeBinding ∧ HedgeTerm ∧ ConcaveSign

end

end Standalone.M7TwoReviewsBounds

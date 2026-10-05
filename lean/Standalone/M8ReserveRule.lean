import Standalone.M7TwoReviewsBounds

/-!
# Claim 047: the reserve rule with one fund and one ETF (M8), in the inputs

Statement only; the proof is `Novel/M8ReserveRuleProof.lean`.

The model and the lines are claim 044's (`Two ι Z`, `Tomorrow`, `Root`, `Sinc`, `etaHat`). The solo
targets, the need and the cash-price bound are claim 046's (`xhat`, `need`, `etaBar`, `Cov`); Q-04.
M8 is the two-instrument case. Its `Σ_AE = b_A b_E(σ_f² + p^λ) > 0` satisfies `Cov`. Its predictive
variances are deterministic, and tomorrow's means are affine in the revision
(`μ_{1,A} = μ_{0,A} + b_A ε^λ + ε^α`, `μ_{1,E} = μ_{0,E} + b_E ε^λ`, `b > 0`). The largest need is
`N(x_0) = max_z need(z; x_0)`.

- Part 2:
  - `NoReserve`: at any root `x_0` with `h⁺_0 > 0` and `h⁺_0 ≥ N(x_0)`, every tomorrow family has
    `η_1 = 0`. At the myopic root, this is "no reserve is needed". At the dynamic root, it is the
    budget channel's vanishing, in leanb's corrected form (prose note of 2026-09-30).
  - `NeedBound`: `N` is bounded in the revision's extremes and the smallest gross returns.
    `RevisionMax`: M8's means are bounded by the revision's extremes.
  - `BudgetChannel` (finite law, `h⁺_0 > 0`): `E[η_1] ≤ E[η̄ 1{need > h⁺_0}]`, and each incumbent value is
    bounded by `β E[g_i t_{1,i} 1{covered}] + β E[g_i (η̄ + (1 + η̄) κ⁺_i) 1{need > h⁺_0}]`.
- Part 2(b)'s certificate (`Certificate`): a feasible policy satisfying claim 044's lines with
  `η_1 = 0` in every state, with `h⁺_0 > 0` and `h⁺_0 ≥ N(x_0)`, is the dynamic optimum (claim 044's
  `Sufficient`), and every tomorrow family at it has `η_1 = 0`.
- Part 2's threshold errors (`ThresholdError`): with `0 ≤ η̂_0 - η_0 ≤ B`, a purchase threshold moves
  by at most `(1 + κ⁺)B` and a sale threshold by at most `(1 - κ⁻)B`. `BudgetChannel` gives `B`.
- Part 3(b), the cost-channel shift with slack budgets (`CostShift`):
  - `p^fix - p^my = [S_E - (t^fix - t^my)]/(γ Σ_{0,EE})`;
  - its bound `(β max(κ⁺_E, κ⁻_E) E[g_E] + κ⁺_E + κ⁻_E)/(γ Σ_{0,EE})`;
  - the no-shift pair `p^my` with slope `t^my + S_E` satisfies the joint line.
- Part 3 (`ReservePremium`): the root line minus the one-review line at the same holding is
  `Π = S_i - β E[η_1](1 + t_{0,i})`, and `Π = β E[g_i s_i - η_1 (1 + t_{0,i})]`. If the instrument is
  sold in every state and was bought today, `Π = β(E[η_1 (g_i (1 - κ⁻_i) - 1 - κ⁺_i)] - κ⁻_i E[g_i])`.
- Part 4 (`Growth`): on the fund's active set the need is affine in the alpha revision with slope
  `(1 + κ⁺)/(γ Σ)`. In the purchase rate its slope is `(x̂ - g a_0) - (1 + κ⁺)/(γ Σ)`. An ETF liquidation
  of `n/((1 - κ⁻) g^min)` units raises at least `n`.
- Part 5 (`CashMax`): if some family exists and every family prices cash in some state, then
  `h⁺_0 ≤ N(x_0)`, strictly when `h⁺_0 > 0` (leanb's form of "never exceeds").

Paper-level:
- part 1's definitions and readings (the two channels, `F`, `Res`);
- 3(a)'s direction, read at the dynamic root with the fund fixed. It is claim 046 part 4's
  one-variable step (`ConcaveSign`) once the one-review objective's derivative in `p` is identified
  with its line's value `-Π`. That identification is left paper-level, as in claim 046;
- 3(b)'s uniqueness (`p^fix = p^my` in the no-shift case) and its fixed-point computation;
- 2(a)'s sufficient conditions and idleness bound (readings of `E[g_E t_{1,E}]`);
- the Gaussian law's explicit tail moment (claim 044's program is the finite-law one);
- `Res`'s non-monotonicity;
- the readings;
- the Checks.
-/

namespace Standalone.M8ReserveRule

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds

noncomputable section

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-- The largest funding need tomorrow, `N(x_0) = max_z need(z; x_0)`. -/
def NN (P : Two ι Z) (x0 : ι → ℝ) : ℝ := ⨆ z, need P z x0

/-- Part 2: at any root with `h⁺_0 > 0` and `h⁺_0 ≥ N(x_0)`, every tomorrow family has `η_1 = 0`, so
`η̂_0 = η_0` and the budget channel vanishes. -/
def NoReserve : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ (η0 : ℝ) η1 t1, Tomorrow P X η1 t1 → 0 < h0 P X.1 → NN P X.1 ≤ h0 P X.1 →
      (∀ z, η1 z = 0) ∧ etaHat P η0 η1 = η0

/-- M8's means are bounded by the revision's extremes: with `b ≥ 0`, `ε^λ ≤ ε^λ_max` and
`ε^α ≤ ε^α_max`, both `μ_0 + b ε^λ + ε^α ≤ μ_0 + b ε^λ_max + ε^α_max` and
`μ_0 + b ε^λ ≤ μ_0 + b ε^λ_max`. -/
def RevisionMax : Prop :=
  ∀ (mu0 b el ea elmax eamax : ℝ), 0 ≤ b → el ≤ elmax → ea ≤ eamax →
    mu0 + b * el + ea ≤ mu0 + b * elmax + eamax ∧ mu0 + b * el ≤ mu0 + b * elmax

/-- Part 2's bound on `N` in the inputs: if every state's means are at most `μ^max_i`, every gross
return is at least `g^min_i > 0`, the variances tomorrow are `Σ_i` in every state, and `x_0 ≥ 0`, then
`N(x_0) ≤ Σ_i (1 + κ⁺_i)((μ^max_i - κ⁺_i)⁺/(γ Σ_i) - g^min_i x_{0,i})⁺`. -/
def NeedBound : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (muMax gmin sig : ι → ℝ) (x0 : ι → ℝ), (∀ z i, P.mu1 z i ≤ muMax i) →
      (∀ z i, gmin i ≤ P.g z i) → (∀ z i, P.S1 z i i = sig i) → (∀ i, 0 < sig i) → (∀ i, 0 ≤ x0 i) →
      NN P x0 ≤ ∑ i, (1 + P.kp i) *
        max (max (muMax i - P.kp i) 0 / (P.gamma * sig i) - gmin i * x0 i) 0

/-- Part 2's budget channel on a finite law, at any root with `h⁺_0 > 0` and for every tomorrow
family:
- `E[η_1] ≤ E[η̄ 1{need > h⁺_0}]`;
- each incumbent value is at most `β E[g_i t_{1,i} 1{covered}] + β E[g_i (η̄ + (1 + η̄) κ⁺_i) 1{need > h⁺_0}]`. -/
def BudgetChannel : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ η1 t1, Tomorrow P X η1 t1 → 0 < h0 P X.1 →
      ∑ z, P.q z * η1 z ≤ ∑ z, P.q z * (if h0 P X.1 < need P z X.1 then etaBar P z else 0) ∧
      ∀ i, Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i *
        (if h0 P X.1 < need P z X.1 then etaBar P z + (1 + etaBar P z) * P.kp i else t1 z i)

/-- Part 3, the reserve premium. At the same holding and `η_0`, the root line minus the one-review
line is `Π = S_i - β E[η_1](1 + t_{0,i})`, and `Π = β E[g_i s_i - η_1(1 + t_{0,i})]`. If the instrument
is sold in every state tomorrow and `t_{0,i} = κ⁺_i` (bought today), then
`Π = β(E[η_1 (g_i (1 - κ⁻_i) - 1 - κ⁺_i)] - κ⁻_i E[g_i])`. -/
def ReservePremium : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) (η0 : ℝ)
    (η1 : Z → ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ) (i : ι), Tomorrow P X η1 t1 →
    let prem := Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 + t0 i)
    (g0 P X.1 i + Sinc P η1 t1 i - etaHat P η0 η1 - (1 + etaHat P η0 η1) * t0 i) -
        (g0 P X.1 i - η0 - (1 + η0) * t0 i) = prem ∧
      prem = P.beta * ∑ z, P.q z * (P.g z i * sval η1 t1 z i - η1 z * (1 + t0 i)) ∧
      ((∀ z, X.2 z i < carry P z X.1 i) → t0 i = P.kp i →
        prem = P.beta * (∑ z, P.q z * (η1 z * (P.g z i * (1 - P.km i) - 1 - P.kp i)) -
          P.km i * ∑ z, P.q z * P.g z i))

/-- Part 4, the need's growth. The fund's need with rate `k`, curvature `c = γΣ > 0`, marked holding
`m = g a_0` and mean `μ_0 + ε` is `(1 + k)((μ_0 + ε - k)⁺/c - m)⁺`. Where the purchase is active
(`μ_0 + ε - k > 0` and `(μ_0 + ε - k)/c > m`):
- its derivative in `ε` is `(1 + k)/c`;
- its derivative in `k` is `(x̂ - m) - (1 + k)/c` with `x̂ = (μ_0 + ε - k)/c`.
An ETF liquidation of `n/((1 - κ⁻) g^min)` units at marked price at least `g^min > 0`, with `κ⁻ < 1`,
raises at least `n`. -/
def Growth : Prop :=
  (∀ (mu0 c m k e : ℝ), 0 < c → 0 < mu0 + e - k → m < (mu0 + e - k) / c →
    HasDerivAt (fun ε => (1 + k) * max (max (mu0 + ε - k) 0 / c - m) 0) ((1 + k) / c) e ∧
    HasDerivAt (fun κ => (1 + κ) * max (max (mu0 + e - κ) 0 / c - m) 0)
      (((mu0 + e - k) / c - m) - (1 + k) / c) k) ∧
  ∀ (n km gmin g : ℝ), 0 ≤ n → km < 1 → 0 < gmin → gmin ≤ g →
    n ≤ (1 - km) * g * (n / ((1 - km) * gmin))

/-- Part 5: if some tomorrow family exists and every family prices cash in some state, then
`h⁺_0 ≤ N(x_0)`, strictly when `h⁺_0 > 0`. -/
def CashMax : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, (∃ η1 t1, Tomorrow P X η1 t1) →
      (∀ η1 t1, Tomorrow P X η1 t1 → ∃ z, 0 < η1 z) →
      h0 P X.1 ≤ NN P X.1 ∧ (0 < h0 P X.1 → h0 P X.1 < NN P X.1)

/-- Part 2(b)'s certificate: take a feasible policy whose lines hold with `η_1 = 0` in every state,
with `h⁺_0 > 0` and `h⁺_0 ≥ N(x_0)`. It is the dynamic optimum, and every tomorrow family at it has
`η_1 = 0`. -/
def Certificate : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ (η0 : ℝ) (t0 : ι → ℝ) (t1 : Z → ι → ℝ),
      Tomorrow P X (fun _ => 0) t1 → Root P X η0 (fun _ => 0) t0 t1 →
      0 < h0 P X.1 → NN P X.1 ≤ h0 P X.1 →
      Optimal P X ∧ ∀ η1 t1', Tomorrow P X η1 t1' → ∀ z, η1 z = 0

/-- Part 2's threshold errors: with `η_0 ≤ η̂_0 ≤ η_0 + B`, the purchase threshold
`η + (1 + η) κ⁺` moves by between `0` and `(1 + κ⁺) B`, and the sale threshold `η - (1 + η) κ⁻` by
between `0` and `(1 - κ⁻) B`. -/
def ThresholdError : Prop :=
  ∀ (e0 eh B kp km : ℝ), e0 ≤ eh → eh - e0 ≤ B → 0 ≤ kp → km < 1 →
    0 ≤ (eh + (1 + eh) * kp) - (e0 + (1 + e0) * kp) ∧
    (eh + (1 + eh) * kp) - (e0 + (1 + e0) * kp) ≤ (1 + kp) * B ∧
    0 ≤ (eh - (1 + eh) * km) - (e0 - (1 + e0) * km) ∧
    (eh - (1 + eh) * km) - (e0 - (1 + e0) * km) ≤ (1 - km) * B

/-- Part 3(b), the cost-channel shift with slack budgets (`η_0 = η_1 = 0`). Let the fixed-fund point
`xf` differ from the one-review root `xm` only in the ETF coordinate `E`, with `Σ_{0,EE} > 0`.
Assume the one-review ETF line `g_{0,E}(xm) = t^my` and the root ETF line at `xf`,
`g_{0,E}(xf) + S_E - t^fix = 0`, where `S_E = β E[g_E t_{1,E}]`. Then:
- `p^fix - p^my = [S_E - (t^fix - t^my)]/(γ Σ_{0,EE})`;
- with every slope in `[-κ⁻_E, κ⁺_E]`,
  `|p^fix - p^my| ≤ (β max(κ⁺_E, κ⁻_E) E[g_E] + κ⁺_E + κ⁻_E)/(γ Σ_{0,EE})`;
- the no-shift pair: at `xm`, the slope `t^my + S_E` satisfies the joint line. -/
def CostShift : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z), Hyp P →
    ∀ (xf xm : ι → ℝ) (E : ι) (tf tm : ℝ) (t1 : Z → ι → ℝ),
      (∀ j, j ≠ E → xf j = xm j) → 0 < P.S0 E E → g0 P xm E = tm →
      g0 P xf E + Sinc P (fun _ => 0) t1 E - tf = 0 →
      xf E - xm E = (Sinc P (fun _ => 0) t1 E - (tf - tm)) / (P.gamma * P.S0 E E) ∧
      ((∀ z, -P.km E ≤ t1 z E ∧ t1 z E ≤ P.kp E) → -P.km E ≤ tf → tf ≤ P.kp E →
        -P.km E ≤ tm → tm ≤ P.kp E →
        |xf E - xm E| ≤ (P.beta * max (P.kp E) (P.km E) * ∑ z, P.q z * P.g z E + P.kp E + P.km E) /
          (P.gamma * P.S0 E E)) ∧
      g0 P xm E + Sinc P (fun _ => 0) t1 E - (tm + Sinc P (fun _ => 0) t1 E) = 0

/-- Claim 047 (paper-level parts in the module note). -/
def statement : Prop :=
  NoReserve ∧ RevisionMax ∧ NeedBound ∧ BudgetChannel ∧ ReservePremium ∧ Growth ∧ CashMax ∧
    Certificate ∧ ThresholdError ∧ CostShift

end

end Standalone.M8ReserveRule

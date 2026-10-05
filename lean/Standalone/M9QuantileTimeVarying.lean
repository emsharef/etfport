import Standalone.M7QuantileFlexibility

/-!
# Claim 115: the quantile flexibility test with time-varying premia (M9)

Statement only; the proof is `Novel/M9QuantileTimeVaryingProof.lean`.

Claim 049's statements are over any `Two ι Z`, whose tomorrow's means `μ_1(z)` vary with the state.
So M9's tree is an instance, and 1a (the transfer) is claim 049's formal statement, cited and not
restated. Claim 049's objects (`liqM`, `short`, `Pr`, `VaR`) and claims 044, 046 and 113's are reused
(Q-04). M9 enters through the planned purchase:
- `μ^p` is tomorrow's predictable mean;
- `Σ_{1,ii} = σ_i` in every state;
- `g^min` is the smallest gross return;
- `PP = Σ_i (1 + κ⁺_i)((μ^p_i - κ⁺_i)⁺/(γ σ_i) - g^min_i x_{0,i})⁺`, and `Δ = need - PP`.

- 1b:
  - `SplitTest`: `P(D > 0) ≤ ε` iff `P(Δ > liq - PP) ≤ ε`;
  - `StateFreeSplit`: with a state-free reserve `L`, iff `VaR_{1-ε}(Δ) ≤ L - PP`.
- 2a (`GeneralBound`): at any feasible `x_0`, take any admissible `(η, t, n)`: `η ≥ 0` with
  `η h(x_0) = 0`, `t` in the trade-sign sets, `n` in the box's normal cone. With the residual
  `ρ = g_0(x_0) + S - η 1 - (1 + η) t - n`, every feasible policy scores at most
  `J(x_0) + ρ'Σ_0⁻¹ρ/(2γ) + β E[η̄ D]`. The relaxed slopes `tu` are any family satisfying the relaxed
  tomorrow's lines, which includes any slope in the interval a bound state's one-sided line cuts. So
  `S` ranges over the admissible incumbent values, and the bound holds for every admissible choice of
  `S` and `l`. The claim's shortest residual is the infimum over them. `FrontLoaded`: with `ρ = 0`, only the tail term remains.
- Part 3:
  - `PinnedS`: an instrument bought in every state at the relaxed tomorrow has `S_i = β E[g_i] κ⁺_i`;
  - `BlockInverse`: for two instruments, `[Σ_0⁻¹]_{AA} = 1/(Σ_AA - Σ_AE²/Σ_EE)`.

Paper-level:
- 2b's reading, and the check's illustration (rule 22);
- the Gaussian quantile;
- the existence of the multipliers (AX-13), taken as hypotheses as in claim 049.
-/

namespace Standalone.M9QuantileTimeVarying

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds
  Standalone.M7SeveralFundsReserve Standalone.M7QuantileFlexibility Matrix

noncomputable section

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-- The planned purchase: the need at zero innovation (tomorrow's predictable mean `μ^p`) with the
worst marking `g^min`, the variances tomorrow being `σ_i`. -/
def PP (P : Two ι Z) (muP sig gmin x0 : ι → ℝ) : ℝ :=
  ∑ i, (1 + P.kp i) * max (max (muP i - P.kp i) 0 / (P.gamma * sig i) - gmin i * x0 i) 0

/-- The innovation-driven part `Δ = need - PP`, of either sign. -/
def Delta (P : Two ι Z) (muP sig gmin x0 : ι → ℝ) (z : Z) : ℝ := need P z x0 - PP P muP sig gmin x0

/-- 1b: the test at level `ε` in split form: `P(D > 0) ≤ ε` iff `P(Δ > liq - PP) ≤ ε`. -/
def SplitTest : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (Es : Finset ι) (muP sig gmin x0 : ι → ℝ)
    (ε : ℝ),
    Pr P.q (fun z => 0 < short P z Es x0) ≤ ε ↔
      Pr P.q (fun z => liqM P z Es x0 - PP P muP sig gmin x0 < Delta P muP sig gmin x0 z) ≤ ε

/-- 1b with a state-free reserve `L`: for a law and `0 ≤ ε < 1`, `P(Δ > L - PP) ≤ ε` iff
`VaR_{1-ε}(Δ) ≤ L - PP`. -/
def StateFreeSplit : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (muP sig gmin x0 : ι → ℝ) (L ε : ℝ),
    (∀ z, 0 ≤ P.q z) → ∑ z, P.q z = 1 → 0 ≤ ε → ε < 1 →
    (Pr P.q (fun z => L - PP P muP sig gmin x0 < Delta P muP sig gmin x0 z) ≤ ε ↔
      VaR P.q (Delta P muP sig gmin x0) ε ≤ L - PP P muP sig gmin x0)

/-- 2a, the general bound at any feasible `x_0`. Take:
- an admissible `(η, t, n)` at `x_0`: `η ≥ 0` with `η h(x_0) = 0`, `t` in the trade-sign sets, and `n`
  in the box's normal cone (`BoxSign`);
- tomorrow's lines of its budgeted problems;
- relaxed points with their `η = 0` lines.
With `S = β E[g ∘ tu]` and `ρ = g_0(x_0) + S - η 1 - (1 + η) t - n`, every feasible policy satisfies
`J(Xd) ≤ J(X0) + ρ'Σ_0⁻¹ρ/(2γ) + β E[η̄ D]`. -/
def GeneralBound : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (Es : Finset ι), Hyp P →
    Cov P → Matrix.PosDef (Matrix.of P.S0) →
    ∀ X0 ∈ Feas P, ∀ (η : ℝ) (t n : ι → ℝ) (η1 : Z → ℝ) (t1 : Z → ι → ℝ) (xu tu : Z → ι → ℝ),
      0 ≤ η → η * h0 P X0.1 = 0 →
      (∀ i, Slope (P.kp i) (P.km i) (X0.1 i - P.xm i) (t i) ∧ BoxSign (P.xbar i) (X0.1 i) (n i)) →
      Tomorrow P X0 η1 t1 →
      (∀ z, Box P (xu z) ∧ ∀ i, Slope (P.kp i) (P.km i) (xu z i - carry P z X0.1 i) (tu z i) ∧
        BoxSign (P.xbar i) (xu z i) (g1 P z (xu z) i - tu z i)) →
      let S : ι → ℝ := fun i => P.beta * ∑ z, P.q z * (P.g z i * tu z i)
      let ρ : ι → ℝ := fun i => g0 P X0.1 i + S i - η - (1 + η) * t i - n i
      ∀ Xd ∈ Feas P,
        J P Xd ≤ J P X0 + ρ ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ ρ) / (2 * P.gamma) +
          P.beta * ∑ z, P.q z * (etaBar P z * short P z Es X0.1)

/-- 2a at the front-loaded point: where the root lines hold with the relaxed tomorrow (`ρ = 0` for
some admissible `(η, t, n)`), every feasible policy scores at most `J(X0) + β E[η̄ D]`. -/
def FrontLoaded : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (Es : Finset ι), Hyp P →
    Cov P → Matrix.PosDef (Matrix.of P.S0) →
    ∀ X0 ∈ Feas P, ∀ (η : ℝ) (t n : ι → ℝ) (η1 : Z → ℝ) (t1 : Z → ι → ℝ) (xu tu : Z → ι → ℝ),
      0 ≤ η → η * h0 P X0.1 = 0 →
      (∀ i, Slope (P.kp i) (P.km i) (X0.1 i - P.xm i) (t i) ∧ BoxSign (P.xbar i) (X0.1 i) (n i)) →
      Tomorrow P X0 η1 t1 →
      (∀ z, Box P (xu z) ∧ ∀ i, Slope (P.kp i) (P.km i) (xu z i - carry P z X0.1 i) (tu z i) ∧
        BoxSign (P.xbar i) (xu z i) (g1 P z (xu z) i - tu z i)) →
      (∀ i, g0 P X0.1 i + P.beta * ∑ z, P.q z * (P.g z i * tu z i) - η - (1 + η) * t i - n i = 0) →
      ∀ Xd ∈ Feas P, J P Xd ≤ J P X0 + P.beta * ∑ z, P.q z * (etaBar P z * short P z Es X0.1)

/-- Part 3's pinned incumbent value: if instrument `i` is bought in every state at the relaxed
tomorrow (with its slope in the trade-sign set), then `S_i = β E[g_i] κ⁺_i`. -/
def PinnedS : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (x0 : ι → ℝ) (xu tu : Z → ι → ℝ) (i : ι),
    (∀ z, Slope (P.kp i) (P.km i) (xu z i - carry P z x0 i) (tu z i)) →
    (∀ z, carry P z x0 i < xu z i) →
    P.beta * ∑ z, P.q z * (P.g z i * tu z i) = P.beta * (∑ z, P.q z * P.g z i) * P.kp i

/-- Part 3's block inverse for one fund `A = 0` and one ETF `E = 1`: for a symmetric `2 × 2` matrix
with `Σ_EE ≠ 0` and nonzero determinant, `[Σ⁻¹]_{AA} = 1/(Σ_AA - Σ_AE²/Σ_EE)`. -/
def BlockInverse : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), M 0 1 = M 1 0 → M 1 1 ≠ 0 → M.det ≠ 0 →
    M⁻¹ 0 0 = 1 / (M 0 0 - M 0 1 ^ 2 / M 1 1)

/-- Claim 115 (paper-level parts in the module note). -/
def statement : Prop :=
  SplitTest ∧ StateFreeSplit ∧ GeneralBound ∧ FrontLoaded ∧ PinnedS ∧ BlockInverse

end

end Standalone.M9QuantileTimeVarying

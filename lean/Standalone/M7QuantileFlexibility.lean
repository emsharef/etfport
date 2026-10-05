import Standalone.M7SeveralFundsReserve

/-!
# Claim 049: the quantile flexibility test for the full menu over two reviews

Statement only; the proof is `Novel/M7QuantileFlexibilityProof.lean`.

The model is claim 044's (`Two ι Z`) with any finite set of instruments, the ETFs being a finite set
`Es` among them (the full menu). The objects are claims 046's and 113's (`need`, `etaBar`, `Cov`,
`LinesAt`, `xhatS`); Q-04. Tomorrow's law is `q` on the finite state set.
- `liqM`, the liquid reserve: cash plus every ETF's sale proceeds down to its threshold clipped at
  zero.
- `short = (need - liqM)⁺`, the shortfall.

- Part 1 (`Coverage`): `need ≤ liqM` at a state makes `η_1 = 0` admissible there, from any admissible
  multiplier. This is claim 113's 2a with the proceeds summed over `Es`.
- Part 2:
  - `VarZero`: `VaR_{1-ε}(D) = 0` iff `P(D > 0) ≤ ε`, for `D ≥ 0` and `0 ≤ ε < 1`.
  - `StateFree`: with a state-free reserve `L`, `P(D > 0) ≤ ε` iff `VaR_{1-ε}(need) ≤ L`.
  - `TailIdentity`: when `P(Y > 0) ≤ ε`, the Rockafellar-Uryasev objective `c + E(Y - c)⁺/ε` has least
    value `E[Y]/ε`, so `E[Y] = ε T_ε(Y)`, and `E[Y]/ε ≤ max Y`. This is proved directly on the finite
    law, since it is elementary there (rule 21, PM's scope note). AX-19 carries only the Gaussian
    reading.
- Part 3 (`LossBound`), given the multipliers whose existence is AX-13's (cited):
  - today's one-review lines at the myopic root;
  - tomorrow's lines of the myopic policy in every state;
  - each state's relaxed optimum with its `η = 0` lines.
  Then every feasible policy, the dynamic optimum in particular, scores at most the myopic policy's
  value plus the band term `S'(γ Σ_0)⁻¹S/2` plus the tail term `β E[η̄ D]`. The assembly into
  `V^dyn - J(x^my_0)` is formal: it bounds claim 044's joint objective `J` at every feasible policy, so
  it needs no `V_1` lemma (the relaxed and budgeted tomorrows enter through their lines). `S = β E[g ∘ t]` is read from
  the relaxed tomorrow. `BandInputs` bounds the band term in the inputs,
  `≤ (L/(2γ)) Σ_i (β E[g_i] max(κ⁺_i, κ⁻_i))²` for any `L` bounding `Σ_0⁻¹`'s form.

Paper-level:
- the existence of the multipliers (AX-13);
- the one-ETF remark (leanb's note to math and red: the band term's denominator is the ETF's
  variance given the funds);
- the Gaussian reading;
- the Checks.
-/

namespace Standalone.M7QuantileFlexibility

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds
  Standalone.M7SeveralFundsReserve Matrix

noncomputable section

open Classical in
/-- The probability of an event under a finite law, `P(A) = Σ_z q(z) 1{A z}`. -/
def Pr {Z : Type} [Fintype Z] (q : Z → ℝ) (A : Z → Prop) : ℝ := ∑ z, if A z then q z else 0

/-- The value at risk at level `1 - ε`, `VaR_{1-ε}(X) = inf {c : P(X ≤ c) ≥ 1 - ε}`. -/
def VaR {Z : Type} [Fintype Z] (q : Z → ℝ) (X : Z → ℝ) (ε : ℝ) : ℝ :=
  sInf {c | 1 - ε ≤ Pr q fun z => X z ≤ c}

/-- The Rockafellar-Uryasev objective `c + E(Y - c)⁺/ε`. -/
def RU {Z : Type} [Fintype Z] (q : Z → ℝ) (Y : Z → ℝ) (ε c : ℝ) : ℝ :=
  c + (∑ z, q z * max (Y z - c) 0) / ε

variable {ι Z : Type} [Fintype ι] [Fintype Z]

/-- The liquid reserve with the ETFs `Es`:
`liq = h⁺_0 + Σ_{E ∈ Es} (1 - κ⁻_E)(g_E x_{0,E} - (x̌_E)⁺)⁺`. -/
def liqM (P : Two ι Z) (z : Z) (Es : Finset ι) (x0 : ι → ℝ) : ℝ :=
  h0 P x0 + ∑ E ∈ Es, (1 - P.km E) * max (P.g z E * x0 E - max (xhatS P z E) 0) 0

/-- The shortfall `D = (need - liq)⁺`. -/
def short (P : Two ι Z) (z : Z) (Es : Finset ι) (x0 : ι → ℝ) : ℝ :=
  max (need P z x0 - liqM P z Es x0) 0

/-- A state's one-review objective from carried holdings `c`, `f_1(x) = Q_1(x) - C(x - c)`. -/
def f1 (P : Two ι Z) (z : Z) (c x : ι → ℝ) : ℝ := Q1 P z x - cost P (x - c)

/-- Part 1: at a feasible policy, `need ≤ liqM` at state `z` makes the multiplier `0` admissible
there, from any admissible multiplier. -/
def Coverage : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] (P : Two ι Z) (Es : Finset ι), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ z e t, LinesAt P X z e t → need P z X.1 ≤ liqM P z Es X.1 →
      ∃ t', LinesAt P X z 0 t'

/-- Part 2, the test: for `D ≥ 0`, a law `q`, and `0 ≤ ε < 1`, `VaR_{1-ε}(D) = 0` iff
`P(D > 0) ≤ ε`. -/
def VarZero : Prop :=
  ∀ (Z : Type) [Fintype Z] (q D : Z → ℝ) (ε : ℝ), (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → 0 ≤ ε → ε < 1 →
    (∀ z, 0 ≤ D z) → (VaR q D ε = 0 ↔ Pr q (fun z => 0 < D z) ≤ ε)

/-- Part 2, the state-free reserve: if the reserve is `L` in every state, then
`P((need - L)⁺ > 0) ≤ ε` iff `VaR_{1-ε}(need) ≤ L`. -/
def StateFree : Prop :=
  ∀ (Z : Type) [Fintype Z] (q N : Z → ℝ) (L ε : ℝ), (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → 0 ≤ ε →
    ε < 1 → (Pr q (fun z => 0 < max (N z - L) 0) ≤ ε ↔ VaR q N ε ≤ L)

/-- Part 2, the tail identity: for `Y ≥ 0`, a law `q`, `0 < ε ≤ 1` and `P(Y > 0) ≤ ε`, the objective
`c + E(Y - c)⁺/ε` has least value `E[Y]/ε` (at `c = 0`), so `E[Y] = ε T_ε(Y)`. And `E[Y]/ε ≤ max Y`. -/
def TailIdentity : Prop :=
  ∀ (Z : Type) [Fintype Z] (q Y : Z → ℝ) (ε : ℝ), (∀ z, 0 ≤ q z) → ∑ z, q z = 1 → 0 < ε → ε ≤ 1 →
    (∀ z, 0 ≤ Y z) → Pr q (fun z => 0 < Y z) ≤ ε →
    IsLeast (Set.range (RU q Y ε)) ((∑ z, q z * Y z) / ε) ∧
    ∀ M, (∀ z, Y z ≤ M) → (∑ z, q z * Y z) / ε ≤ M

/-- Part 3, the loss bound. Take a feasible myopic policy `Xm` with:
- today's one-review lines (`η_0 ≥ 0`, `η_0 h⁺_0 = 0`, slopes, box signs);
- tomorrow's lines of its budgeted problems (`LinesAt` in every state);
- in every state a relaxed point `xu z` in the box with its `η = 0` lines from the marked holdings.
With `Σ_0` positive definite and `S = β Σ_z q(z) g(z) ∘ tu(z)`, every feasible policy `Xd` satisfies
`J(Xd) ≤ J(Xm) + S'Σ_0⁻¹S/(2γ) + β Σ_z q(z) η̄(z) D(z)`, with `D` at the myopic root. -/
def LossBound : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (Es : Finset ι), Hyp P →
    Cov P → Matrix.PosDef (Matrix.of P.S0) →
    ∀ Xm ∈ Feas P, ∀ (η0 : ℝ) (t0 : ι → ℝ) (η1 : Z → ℝ) (t1 : Z → ι → ℝ)
      (xu : Z → ι → ℝ) (tu : Z → ι → ℝ),
      0 ≤ η0 → η0 * h0 P Xm.1 = 0 →
      (∀ i, Slope (P.kp i) (P.km i) (Xm.1 i - P.xm i) (t0 i) ∧
        BoxSign (P.xbar i) (Xm.1 i) (g0 P Xm.1 i - η0 - (1 + η0) * t0 i)) →
      Tomorrow P Xm η1 t1 →
      (∀ z, Box P (xu z) ∧ ∀ i, Slope (P.kp i) (P.km i) (xu z i - carry P z Xm.1 i) (tu z i) ∧
        BoxSign (P.xbar i) (xu z i) (g1 P z (xu z) i - tu z i)) →
      let S : ι → ℝ := fun i => P.beta * ∑ z, P.q z * (P.g z i * tu z i)
      ∀ Xd ∈ Feas P,
        J P Xd ≤ J P Xm + S ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ S) / (2 * P.gamma) +
          P.beta * ∑ z, P.q z * (etaBar P z * short P z Es Xm.1)

/-- Part 3's band term in the inputs: if the relaxed slopes lie in `[-κ⁻, κ⁺]` and `L` bounds
`Σ_0⁻¹`'s form (`u'Σ_0⁻¹u ≤ L u'u`, `L ≥ 0`), then
`S'Σ_0⁻¹S/(2γ) ≤ (L/(2γ)) Σ_i (β Σ_z q g_i max(κ⁺_i, κ⁻_i))²`. -/
def BandInputs : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z), Hyp P → ∀ (tu : Z → ι → ℝ) (L : ℝ),
    (∀ z i, -P.km i ≤ tu z i ∧ tu z i ≤ P.kp i) → 0 ≤ L →
    (∀ u : ι → ℝ, u ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ u) ≤ L * (u ⬝ᵥ u)) →
    let S : ι → ℝ := fun i => P.beta * ∑ z, P.q z * (P.g z i * tu z i)
    S ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ S) / (2 * P.gamma) ≤
      L / (2 * P.gamma) * ∑ i, (P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i)) ^ 2

/-- Claim 049 (paper-level parts in the module note). -/
def statement : Prop :=
  Coverage ∧ VarZero ∧ StateFree ∧ TailIdentity ∧ LossBound ∧ BandInputs

end

end Standalone.M7QuantileFlexibility

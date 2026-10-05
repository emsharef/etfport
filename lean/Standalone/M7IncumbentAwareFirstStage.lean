import Standalone.M7TwoStageExactnessLoss
import Standalone.M7EtfsAtZeroCostsBudget

/-!
# Claim 111: the incumbent-aware first stage, and the two-stage loss through the ETF-line residual

Statement only; the proof is `Novel/M7IncumbentAwareFirstStageProof.lean`.

Setting: claim 027's `Data` in claim 104's reference case with `Σ_E = 0` (`RefCase D Sf V 0`), spanning
ETFs (`M = K`, `B^E` invertible), `Σ~_f` positive definite and `γ > 0`. The score `Q` is claim 027's, on
the full class `F` (claim 027's box, including ETF caps, and the funded budget `k ≥ 0`).

The claim's objects, reused from claim 040's coordinates (`coord`, `toCoord`, `rvec`; Q-04, PM's scope
note):
- the exposure in ETF units `w(x) = x^E + Q x^A`, with `Q_{ji} = r_ij`, so that `b(x) = B^E' w(x)`;
- `Σ_EE = B^E Σ~_f B^E'`;
- the fibre problem's multipliers `(η, t, ζ)` at `x` (`FibreMult`): `η ≥ 0` with `η k(x) = 0`; slopes
  `t_l ∈ T_l(x)`; `ζ ≥ 0` with `ζ_j x^E_j = 0`; and the fund lines, whose box signs fall on
  `g_A - η - (1 + η) t_A - Q's`;
- the ETF-line residual `s = g_E - η 1 - (1 + η) t_E + ζ` (`resid`).

The claim's fibre has no ETF caps. A fibre multiplier without cap multipliers is what `FibreMult`
states; caps enter only where the claim's "no ETF caps" is needed (part 2's converse), as caps that do
not bind.

- Part 1: the strong supergradient inequality at any point with fibre multipliers, for every
  `x' ∈ F`, which gives the claim's inequality for `V`. The loss bounds `0 ≤ Λ ≤ min(s'd, s'Σ_EE⁻¹s/(2γ))`
  and the exposure gap `γ‖d‖_{Σ_EE} ≤ ‖s‖_{Σ_EE⁻¹}` (in squared and root form) follow. So does the lower
  bound `Λ ≥ (γ/2)(d'Σ_EE d + d_A'V d_A)`, proved by strong concavity along the segment, and `Λ = 0` iff
  `x₂ = x_J` (`V` positive definite). None of this uses AX-13, where the approved proof cites AX-13's
  optimality condition at `x_J` for the lower bound.
- Part 2:
  - fibre multipliers with `s = 0` exist iff claim 109's `Criterion` (the joint criterion, part 4a) holds
    at `x₂`, unconditionally;
  - `s = 0` gives `T = J`, and `x₂ = x_J` with `V` positive definite;
  - the converse (given AX-13, ETF caps not binding);
  - the pinned residual `s_j = g_j - κ⁺_j` or `g_j + κ⁻_j` for an ETF traded to an interior holding
    under a slack budget, and hence `s_j = 0` for every valid multiplier choice at an exact split
    (given AX-13).
- Part 3:
  - 3a, every fund held;
  - 3b, every ETF traded, directions kept, budget slack;
  - 3c, fixed ETFs: `s_T = 0`; the by-product condition `Q_F(x^A₂ - x^{A-}) = 0`, which follows from the
    kept statuses (leanb's prose note); exactness under the fund-line condition.
- The marginals in the inputs, in claim 040's coordinates: `w(x)` is `toCoord`'s exposure,
  `g_E = μ_E - γ Σ_EE w(x)`, and claim 102's identity `g_A = α~ - γ V x^A + Q' g_E`.

Paper-level:
- the existence of the fibre multipliers (AX-13 on the fibre problem);
- 3d (part 2 restated);
- part 4, the comparison with claim 041's first stage.
-/

namespace Standalone.M7IncumbentAwareFirstStage

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M7TwoStageExactnessLoss Standalone.M7FundDecisionEtfsAtZero

noncomputable section

variable {m K : ℕ} {S : Type} [Fintype S]

/-- `Q_{ji} = r_ij` (claim 040's `coord`'s `Q`): the ETF units that replicate one unit of each fund's
factor exposure. -/
def Qm (D : Data m K K S) : Matrix (Fin K) (Fin m) ℝ := Matrix.of fun j i => rvec D i j

/-- The exposure in ETF units, `w(x) = x^E + Q x^A`. -/
def wexp (D : Data m K K S) (x : Inst m K → ℝ) : Fin K → ℝ := etf x + Qm D *ᵥ active x

/-- `Σ_EE = B^E Σ~_f B^E'` (claim 040's `coord`'s `Sig`). -/
def SigEE (D : Data m K K S) (Sf : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  D.BE * Sf * D.BEᵀ

/-- The ETFs' marginals `g_E(x)`. -/
def gE (D : Data m K K S) (θ : Params m K) (x : Inst m K → ℝ) : Fin K → ℝ :=
  fun j => grad D θ x (Sum.inr j)

/-- The funds' marginals `g_A(x)`. -/
def gA (D : Data m K K S) (θ : Params m K) (x : Inst m K → ℝ) : Fin m → ℝ :=
  fun i => grad D θ x (Sum.inl i)

/-- The ETF-line residual `s = g_E - η 1 - (1 + η) t_E + ζ`. -/
def resid (D : Data m K K S) (θ : Params m K) (x : Inst m K → ℝ) (η : ℝ) (t : Inst m K → ℝ)
    (ζ : Fin K → ℝ) : Fin K → ℝ :=
  fun j => gE D θ x j - η - (1 + η) * t (Sum.inr j) + ζ j

/-- The fibre problem's multipliers at `x`:
- the budget's `η ≥ 0`, with `η k(x) = 0`;
- trade-sign slopes `t_l ∈ T_l(x)`;
- the zero bound's `ζ ≥ 0`, with `ζ_j x^E_j = 0`;
- the fund lines on the fibre, `g_A - η - (1 + η) t_A - Q's`, with the box signs. -/
def FibreMult (D : Data m K K S) (θ : Params m K) (x : Inst m K → ℝ) (η : ℝ) (t : Inst m K → ℝ)
    (ζ : Fin K → ℝ) : Prop :=
  0 ≤ η ∧ η * cash D x = 0 ∧ (∀ l, InSlope D x l (t l)) ∧ (∀ j, 0 ≤ ζ j) ∧
    (∀ j, ζ j * x (Sum.inr j) = 0) ∧
    ∀ i, BoxSign (D.wbar (Sum.inl i)) (x (Sum.inl i))
      (gA D θ x i - η - (1 + η) * t (Sum.inl i) - ((Qm D)ᵀ *ᵥ resid D θ x η t ζ) i)

/-- The first stage's multipliers at `x₁` (the ETF-only problem, funds frozen): `η₁ ≥ 0` with
`η₁ k(x₁) = 0`; ETF slopes `t₁ ∈ T(x₁)`; at-zero slacks `ζ₁ ≥ 0` with `ζ₁_j x^E_{1,j} = 0`; and the ETF
lines `g_E(x₁) - η₁ - (1 + η₁) t₁ + ζ₁ = 0`. -/
def StageOneMult (D : Data m K K S) (θ : Params m K) (x : Inst m K → ℝ) (η : ℝ) (t ζ : Fin K → ℝ) :
    Prop :=
  0 ≤ η ∧ η * cash D x = 0 ∧ (∀ j, InSlope D x (Sum.inr j) (t j)) ∧ (∀ j, 0 ≤ ζ j) ∧
    (∀ j, ζ j * x (Sum.inr j) = 0) ∧ ∀ j, gE D θ x j - η - (1 + η) * t j + ζ j = 0

/-- The fibre of an exposure `w`: `{x ∈ F : w(x) = w}`. -/
def fibreW (D : Data m K K S) (w : Fin K → ℝ) : Set (Inst m K → ℝ) := {x | x ∈ F D ∧ wexp D x = w}

/-- The setting: claim 027's inputs, the reference case with `Σ_E = 0`, `B^E` invertible, `Σ~_f`
positive definite, `γ > 0`. -/
def Setting (D : Data m K K S) (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Standalone.M2TwoStageSeparation.Inputs D ∧ RefCase D Sf V 0 ∧ IsUnit D.BE.det ∧ Sf.PosDef ∧
    0 < D.gamma

/-- The quadratic form `u' M u`. -/
def qf {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) : ℝ := u ⬝ᵥ (M *ᵥ u)

/-- The marginals in the inputs, in claim 040's coordinates `P = coord D θ Sf V`: `w(x)` is
`toCoord`'s exposure, `Σ_EE = P.Sig`, `Q = P.Q`, `g_E(x) = μ_E - γ Σ_EE w(x)`, and claim 102's identity
`g_A(x) = α~ - γ V x^A + Q' g_E(x)`. -/
def Marginals : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ x : Inst m K → ℝ,
      wexp D x = (toCoord D θ Sf V x).2 ∧ SigEE D Sf = (coord D θ Sf V).Sig ∧
      Qm D = (coord D θ Sf V).Q ∧
      gE D θ x = (coord D θ Sf V).mu - D.gamma • (SigEE D Sf *ᵥ wexp D x) ∧
      gA D θ x = (coord D θ Sf V).alt - D.gamma • (V *ᵥ active x) + (Qm D)ᵀ *ᵥ gE D θ x

/-- Part 1, the strong supergradient inequality: at any `x₂ ∈ F` with fibre multipliers, every
`x ∈ F` has `Q(x) ≤ Q(x₂) + s'(w(x) - w(x₂)) - (γ/2)(w(x) - w(x₂))'Σ_EE(w(x) - w(x₂))
- (γ/2)(x^A - x^A₂)'V(x^A - x^A₂)`. Taking the sup over the fibre of `w'` gives the claim's
`V(w') ≤ V(w₁) + s'(w' - w₁) - (γ/2)‖w' - w₁‖²_{Σ_EE}`. -/
def Supergradient : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ x₂ ∈ F D, ∀ η t ζ, FibreMult D θ x₂ η t ζ → ∀ x ∈ F D,
      score D x θ ≤ score D x₂ θ + resid D θ x₂ η t ζ ⬝ᵥ (wexp D x - wexp D x₂)
        - D.gamma / 2 * qf (SigEE D Sf) (wexp D x - wexp D x₂)
        - D.gamma / 2 * qf V (active x - active x₂)

/-- Part 1's bounds. Take `x_J` the joint optimum and `x₂ ∈ F` with fibre multipliers, and write
`Λ = Q(x_J) - Q(x₂)`, `d = w(x_J) - w(x₂)`, `d_A = x^A_J - x^A₂`. Then:
- `Λ ≥ (γ/2)(d'Σ_EE d + d_A'V d_A)`, which holds for every `x₂ ∈ F`, and with `V` positive definite
  `Λ = 0` iff `x₂ = x_J`;
- `0 ≤ Λ ≤ s'd`, `Λ ≤ s'Σ_EE⁻¹s/(2γ)`;
- the exposure gap `γ² d'Σ_EE d ≤ s'Σ_EE⁻¹s`, that is `‖d‖_{Σ_EE} ≤ ‖s‖_{Σ_EE⁻¹}/γ`. -/
def LossBounds : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ xJ ∈ F D, IsMaxOn (fun x => score D x θ) (F D) xJ → ∀ x₂ ∈ F D,
      D.gamma / 2 * (qf (SigEE D Sf) (wexp D xJ - wexp D x₂) + qf V (active xJ - active x₂)) ≤
        score D xJ θ - score D x₂ θ ∧
      (V.PosDef → (score D xJ θ - score D x₂ θ = 0 ↔ x₂ = xJ)) ∧
      ∀ η t ζ, FibreMult D θ x₂ η t ζ →
        0 ≤ score D xJ θ - score D x₂ θ ∧
        score D xJ θ - score D x₂ θ ≤ resid D θ x₂ η t ζ ⬝ᵥ (wexp D xJ - wexp D x₂) ∧
        score D xJ θ - score D x₂ θ ≤ qf (SigEE D Sf)⁻¹ (resid D θ x₂ η t ζ) / (2 * D.gamma) ∧
        D.gamma ^ 2 * qf (SigEE D Sf) (wexp D xJ - wexp D x₂) ≤ qf (SigEE D Sf)⁻¹ (resid D θ x₂ η t ζ) ∧
        Real.sqrt (qf (SigEE D Sf) (wexp D xJ - wexp D x₂)) ≤
          Real.sqrt (qf (SigEE D Sf)⁻¹ (resid D θ x₂ η t ζ)) / D.gamma

/-- Part 2, exactness. Take `x_J` the joint optimum and `x₂ ∈ F`.
- Fibre multipliers with `s = 0` exist iff claim 109's criterion (part 4a's) holds at `x₂`.
- If `x₂` has fibre multipliers with `s = 0`, then `T = J` (`Q(x₂) = Q(x_J)`), and `x₂ = x_J` when
  `V` is positive definite.
- Given AX-13, if `T = J` and no ETF cap binds at `x₂`, then `x₂` has fibre multipliers with `s = 0`.
- Where the fibre multipliers are pinned (a slack budget, an ETF traded to an interior holding):
  `s_j = g_j - κ⁺_j` after a purchase and `s_j = g_j + κ⁻_j` after a sale, for every valid choice. So
  (given AX-13, no binding ETF cap) `s_j = 0` for every valid choice at an exact split. -/
def Exactness : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ xJ ∈ F D, IsMaxOn (fun x => score D x θ) (F D) xJ → ∀ x₂ ∈ F D,
      ((∃ η t ζ, FibreMult D θ x₂ η t ζ ∧ resid D θ x₂ η t ζ = 0) ↔
        Standalone.M7EtfsAtZeroCostsBudget.Criterion D θ V 0 x₂) ∧
      (∀ η t ζ, FibreMult D θ x₂ η t ζ → resid D θ x₂ η t ζ = 0 →
        score D x₂ θ = score D xJ θ ∧ (V.PosDef → x₂ = xJ)) ∧
      (AX13 → (∀ j, x₂ (Sum.inr j) < D.wbar (Sum.inr j)) → score D x₂ θ = score D xJ θ →
        ∃ η t ζ, FibreMult D θ x₂ η t ζ ∧ resid D θ x₂ η t ζ = 0) ∧
      (∀ η t ζ, FibreMult D θ x₂ η t ζ → 0 < cash D x₂ → ∀ j, 0 < x₂ (Sum.inr j) →
        (w0 D (Sum.inr j) < x₂ (Sum.inr j) →
          resid D θ x₂ η t ζ j = gE D θ x₂ j - D.kplus (Sum.inr j)) ∧
        (x₂ (Sum.inr j) < w0 D (Sum.inr j) →
          resid D θ x₂ η t ζ j = gE D θ x₂ j + D.kminus (Sum.inr j))) ∧
      (AX13 → (∀ j, x₂ (Sum.inr j) < D.wbar (Sum.inr j)) → score D x₂ θ = score D xJ θ →
        0 < cash D x₂ → ∀ η t ζ, FibreMult D θ x₂ η t ζ → ∀ j, 0 < x₂ (Sum.inr j) →
          x₂ (Sum.inr j) ≠ w0 D (Sum.inr j) → resid D θ x₂ η t ζ j = 0)

/-- Part 3a, every fund held. `x₁` is the first stage's point (funds at their incumbents, `x₁ ∈ E`)
with its multipliers. Suppose every fund's marginal satisfies
`η₁ - (1 + η₁) κ⁻_i ≤ g_i(x₁)` (dropped at zero) and `g_i(x₁) ≤ η₁ + (1 + η₁) κ⁺_i` (dropped at the
cap). Then `x₁` is the joint optimum. With `V` positive definite, every maximizer `x₂` on the fibre of
`w(x₁)` is `x₁`, so `Λ = 0`. -/
def HoldAll : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ x₁ ∈ E D, ∀ η₁ t₁ ζ₁, StageOneMult D θ x₁ η₁ t₁ ζ₁ →
      (∀ i, (0 < x₁ (Sum.inl i) → η₁ - (1 + η₁) * D.kminus (Sum.inl i) ≤ gA D θ x₁ i) ∧
        (x₁ (Sum.inl i) < D.wbar (Sum.inl i) → gA D θ x₁ i ≤ η₁ + (1 + η₁) * D.kplus (Sum.inl i))) →
      IsMaxOn (fun x => score D x θ) (F D) x₁ ∧
      (V.PosDef → ∀ x₂ ∈ fibreW D (wexp D x₁),
        IsMaxOn (fun x => score D x θ) (fibreW D (wexp D x₁)) x₂ → x₂ = x₁)

/-- Part 3b, every ETF traded with its direction kept and the budget slack. Assume:
- at `x₁`, every ETF is traded to an interior holding and the budget is slack;
- `x₂` on the fibre of `w(x₁)` has a slack budget, and every ETF is interior and traded in the same
  direction as at `x₁`.

Then every valid choice of fibre multipliers at `x₂` gives `s = 0`, and the split is exact. -/
def AllTraded : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ x₁ ∈ E D, ∀ η₁ t₁ ζ₁, StageOneMult D θ x₁ η₁ t₁ ζ₁ → 0 < cash D x₁ →
      (∀ j, 0 < x₁ (Sum.inr j) ∧ x₁ (Sum.inr j) ≠ w0 D (Sum.inr j)) →
      ∀ x₂ ∈ fibreW D (wexp D x₁), 0 < cash D x₂ →
      (∀ j, 0 < x₂ (Sum.inr j) ∧ (w0 D (Sum.inr j) < x₁ (Sum.inr j) → w0 D (Sum.inr j) < x₂ (Sum.inr j)) ∧
        (x₁ (Sum.inr j) < w0 D (Sum.inr j) → x₂ (Sum.inr j) < w0 D (Sum.inr j))) →
      ∀ η t ζ, FibreMult D θ x₂ η t ζ →
        resid D θ x₂ η t ζ = 0 ∧ IsMaxOn (fun x => score D x θ) (F D) x₂

/-- Part 3c, fixed ETFs, with the statuses kept and the budget slack. Assume:
- the ETFs in `T` are traded to interior holdings at `x₁` and at `x₂`, in the same direction;
- the others (`F`) hold at `x₂` what they hold at `x₁`.

Then:
- every valid choice of fibre multipliers at `x₂` has `s_T = 0`;
- `Q_F(x^A₂ - x^{A-}) = 0` follows (the by-product condition);
- if every fund's joint line holds at `x₂` (`g_i(x₂) - τ_i` with the box signs for some `τ_i ∈ T_i(x₂)`),
  the split is exact. By `Marginals`, `g_i(x₂) = α~_i - γ(V x^A₂)_i + r_i'g_E(x₁)`, the claim's form. -/
def FixedEtfs : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ), Setting D Sf V →
    ∀ x₁ ∈ E D, ∀ η₁ t₁ ζ₁, StageOneMult D θ x₁ η₁ t₁ ζ₁ → 0 < cash D x₁ →
      ∀ x₂ ∈ fibreW D (wexp D x₁), 0 < cash D x₂ → ∀ T : Finset (Fin K),
      (∀ j ∈ T, 0 < x₁ (Sum.inr j) ∧ 0 < x₂ (Sum.inr j) ∧
        ((w0 D (Sum.inr j) < x₁ (Sum.inr j) ∧ w0 D (Sum.inr j) < x₂ (Sum.inr j)) ∨
          (x₁ (Sum.inr j) < w0 D (Sum.inr j) ∧ x₂ (Sum.inr j) < w0 D (Sum.inr j)))) →
      (∀ j ∉ T, x₂ (Sum.inr j) = x₁ (Sum.inr j)) →
      (∀ η t ζ, FibreMult D θ x₂ η t ζ → ∀ j ∈ T, resid D θ x₂ η t ζ j = 0) ∧
      (∀ j ∉ T, (Qm D *ᵥ (active x₂ - active (w0 D))) j = 0) ∧
      ((∀ i, ∃ τ, InSlope D x₂ (Sum.inl i) τ ∧
          BoxSign (D.wbar (Sum.inl i)) (x₂ (Sum.inl i)) (gA D θ x₂ i - τ)) →
        IsMaxOn (fun x => score D x θ) (F D) x₂)

/-- Claim 111 (parts 1-3, with the paper-level parts named in the module note). -/
def statement : Prop :=
  Marginals ∧ Supergradient ∧ LossBounds ∧ Exactness ∧ HoldAll ∧ AllTraded ∧ FixedEtfs

end

end Standalone.M7IncumbentAwareFirstStage

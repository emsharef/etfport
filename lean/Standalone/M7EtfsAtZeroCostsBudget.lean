import Standalone.M7FundDecisionEtfsAtZero
import Mathlib.Analysis.Convex.Function
import Standalone.M7TwoStageEtfsAtZero

/-!
# Claim 109: ETFs at zero, costly ETFs, fees and a binding budget

Statement only; the proof is `Novel/M7EtfsAtZeroCostsBudgetProof.lean`.

Part 2 (with `Σ_E = 0`) is stated on claim 040's coordinates (`Coord`, Q-04). `mu` is `μ_E` with fees
in, `Sig` is `Σ_EE`, `alt` is `α~`, `Q` is the netting matrix (column `i` is `r_i`). The ETFs split into
a fixed set `F` (at zero or idle: holdings known) and its complement `T`, the traded ETFs (slopes
pinned). In claim 040's blocks `Z = F` and the complement `c = T`: `Scc = Σ_TT`, `ScZ = Σ_TF`,
`SZc = Σ_FT`, `schur = Σ_{FF.T}`, `muZc = μ_{F.T}`, `QZ = Q_F` and `VZ = V^{F,T}`.
- `expo xA xE = x^E + Q x^A` is the exposure `w`.
- `gE w = μ_E - γΣ_EE w` is the ETFs' smooth marginal, and `gA` the funds'
  (`α~ - γVx^A + Q'g_E`, claim 102's identity with `Σ_E = 0`).
- `piT = η 1 + (1 + η) t_T` are the traded ETFs' pinned marginals.
- `rho i = r_{iT} + Σ_TT⁻¹ Σ_TF r_{iF}` is fund `i`'s effective netting weight.
- `alphaFT i` is `α^{F,T}_i`.
Part 2's forms are identities given the traded ETFs' lines at a point, which is how the claim
states them ("given the statuses").

Parts 1 and 4a are conditional on AX-13 through the hypothesis `AX13`, as for claims 040 and 104.
They are stated on claim 027's `Data` in claim 104's reference case. Part 1's necessity is claim 040's
part 1 and its converse is claim 104's part 0. Part 4a's lines at `x₂` and 4b are stated in coordinates
on claim 041's `TS`, which extends `Coord`, with `Σ_E = 0`. Part 4c is stated for any convex feasible
set and concave remainder.

Paper-level:
- part 5, the comparison with the benchmark;
- 2d's restatement of part 1 as consistency of a status partition, and the uniqueness of the optimum;
- 4a's display with `Σ_E ≠ 0`, where the residual terms cancel;
- 2e's reading of the range as claim 102's part 4 bracket, which is formal here as the range of
  `(1 + η)ρ'_{iT} t_T`.
-/

namespace Standalone.M7EtfsAtZeroCostsBudget

open Matrix Standalone.M7FundDecisionEtfsAtZero

noncomputable section

variable {M N : ℕ}

/-- The exposure `w = x^E + Q x^A`. -/
def expo (P : Coord M N) (xA : Fin N → ℝ) (xE : Fin M → ℝ) : Fin M → ℝ := xE + P.Q *ᵥ xA

/-- The ETFs' smooth marginal `g_E(w) = μ_E - γΣ_EE w` (`Σ_E = 0`). -/
def gE (P : Coord M N) (w : Fin M → ℝ) : Fin M → ℝ := P.mu - P.gamma • (P.Sig *ᵥ w)

/-- The funds' marginal `g_A = α~ - γ V x^A + Q' g_E(w)`. -/
def gA (P : Coord M N) (xA : Fin N → ℝ) (w : Fin M → ℝ) : Fin N → ℝ :=
  P.alt - P.gamma • (P.V *ᵥ xA) + P.Qᵀ *ᵥ gE P w

/-- The fixed directions' exposure `w_F = Q_F x^A + x_F`. -/
def wF (P : Coord M N) (F : Finset (Fin M)) (xA : Fin N → ℝ) (xE : Fin M → ℝ) : In F → ℝ :=
  fun j => expo P xA xE j

/-- The fixed ETFs' holdings `x_F`. -/
def xF (F : Finset (Fin M)) (xE : Fin M → ℝ) : In F → ℝ := fun j => xE j

/-- The traded ETFs' pinned marginals `π_T = η 1 + (1 + η) t_T`. -/
def piT (F : Finset (Fin M)) (eta : ℝ) (t : Fin M → ℝ) : Out F → ℝ := fun j => eta + (1 + eta) * t j

/-- `r_{iF}`. -/
def rF (P : Coord M N) (F : Finset (Fin M)) (i : Fin N) : In F → ℝ := fun j => P.Q j i

/-- `r_{iT}`. -/
def rT (P : Coord M N) (F : Finset (Fin M)) (i : Fin N) : Out F → ℝ := fun j => P.Q j i

/-- The effective netting weight `ρ_{iT} = r_{iT} + Σ_TT⁻¹ Σ_TF r_{iF}`. -/
def rho (P : Coord M N) (F : Finset (Fin M)) (i : Fin N) : Out F → ℝ :=
  rT P F i + (Scc P F)⁻¹ *ᵥ (ScZ P F *ᵥ rF P F i)

/-- `α^{F,T}_i = α~_i + r_{iF}'μ_{F.T} - γ r_{iF}'Σ_{FF.T} x_F + ρ_{iT}'π_T`. -/
def alphaFT (P : Coord M N) (F : Finset (Fin M)) (eta : ℝ) (t : Fin M → ℝ) (xE : Fin M → ℝ)
    (i : Fin N) : ℝ :=
  P.alt i + rF P F i ⬝ᵥ muZc P F - P.gamma * (rF P F i ⬝ᵥ (schur P F *ᵥ xF F xE)) +
    rho P F i ⬝ᵥ piT F eta t

/-- Part 2, 2a-2c (`Σ_E = 0`). Given the traded ETFs' lines `g_T = π_T` at `(x^A, x^E)`:
- 2a: `w_T = Σ_TT⁻¹[(μ_T - π_T)/γ - Σ_TF w_F]`;
- 2b: `g_F = μ_{F.T} + Σ_FT Σ_TT⁻¹ π_T - γ Σ_{FF.T} w_F`;
- 2c: every fund's marginal is `α^{F,T}_i - γ(V^{F,T} x^A)_i`, and part 1's fund line
  `g_i = η + (1 + η) t_i` reads
  `α~_i + r_{iF}'μ_{F.T} - γ r_{iF}'Σ_{FF.T} x_F - γ(V^{F,T}x^A)_i + (1 + η)ρ_{iT}'t_T - η(1 - ρ_{iT}'1) = (1 + η)t_i`. -/
def Explicit : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), 0 < P.gamma → P.Sig.PosDef →
    ∀ (F : Finset (Fin M)) (xA : Fin N → ℝ) (xE : Fin M → ℝ) (eta : ℝ) (t : Fin M → ℝ),
      (∀ j : Out F, gE P (expo P xA xE) j = piT F eta t j) →
      (fun j : Out F => expo P xA xE j) =
          (Scc P F)⁻¹ *ᵥ ((1 / P.gamma) • ((fun j : Out F => P.mu j) - piT F eta t) -
            ScZ P F *ᵥ wF P F xA xE) ∧
        (∀ j : In F, gE P (expo P xA xE) j =
          (muZc P F + SZc P F *ᵥ ((Scc P F)⁻¹ *ᵥ piT F eta t) - P.gamma • (schur P F *ᵥ wF P F xA xE)) j) ∧
        (∀ i, gA P xA (expo P xA xE) i = alphaFT P F eta t xE i - P.gamma * (VZ P F *ᵥ xA) i) ∧
        ∀ i (ti : ℝ), (gA P xA (expo P xA xE) i = eta + (1 + eta) * ti ↔
          P.alt i + rF P F i ⬝ᵥ muZc P F - P.gamma * (rF P F i ⬝ᵥ (schur P F *ᵥ xF F xE)) -
            P.gamma * (VZ P F *ᵥ xA) i + (1 + eta) * (rho P F i ⬝ᵥ fun j => t j) -
            eta * (1 - rho P F i ⬝ᵥ fun _ => 1) = (1 + eta) * ti)


/-- A scaled purchase threshold `η + (1 + η) κ⁺`. -/
def thr (eta kp : ℝ) : ℝ := eta + (1 + eta) * kp

/-- Part 2d, for an ETF starting at zero, whose line at the optimum is
`g_j = η + (1 + η) κ⁺_{E,j} - ζ_j` with `ζ_j ≥ 0` and `ζ_j = 0` unless `x_j = 0`:
- at zero implies `g_j ≤` the threshold;
- bought implies `g_j =` the threshold;
- `g_j <` the threshold implies at zero;
- the one-quantity test: at zero iff `g_j + γΣ_jj x_j ≤` the threshold (part 3's form). -/
def AtZeroTests : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), 0 < P.gamma → P.Sig.PosDef →
    ∀ (xA : Fin N → ℝ) (xE : Fin M → ℝ) (j : Fin M) (eta kp ζ : ℝ), 0 ≤ xE j → 0 ≤ ζ →
      (0 < xE j → ζ = 0) → gE P (expo P xA xE) j = thr eta kp - ζ →
      (xE j = 0 → gE P (expo P xA xE) j ≤ thr eta kp) ∧
      (0 < xE j → gE P (expo P xA xE) j = thr eta kp) ∧
      (gE P (expo P xA xE) j < thr eta kp → xE j = 0) ∧
      (xE j = 0 ↔ gE P (expo P xA xE) j + P.gamma * P.Sig j j * xE j ≤ thr eta kp)

/-- Claim 102's re-hedge cost of a unit purchase over the traded ETFs, `h⁺(ρ) = Σ_j [ρ_j⁺ κ⁻_{E,j} + ρ_j⁻ κ⁺_{E,j}]`. -/
def hP (F : Finset (Fin M)) (kpE kmE : Fin M → ℝ) (ρ : Out F → ℝ) : ℝ :=
  ∑ j, (max (ρ j) 0 * kmE j + max (-ρ j) 0 * kpE j)

/-- The re-hedge cost of a unit sale, `h⁻(ρ) = Σ_j [ρ_j⁺ κ⁺_{E,j} + ρ_j⁻ κ⁻_{E,j}]`. -/
def hM (F : Finset (Fin M)) (kpE kmE : Fin M → ℝ) (ρ : Out F → ℝ) : ℝ :=
  ∑ j, (max (ρ j) 0 * kpE j + max (-ρ j) 0 * kmE j)

/-- Part 2e: over the traded ETFs' sign sets, `(1 + η) ρ'_{iT} t_T` lies in `(1 + η)[-h⁺(ρ), h⁻(ρ)]`, the
bracket of claim 102's part 4 with `ρ_{iT}` in place of `r_i`. -/
def Bracket : Prop :=
  ∀ (M : ℕ) (F : Finset (Fin M)) (kpE kmE : Fin M → ℝ) (ρ : Out F → ℝ) (t : Fin M → ℝ) (eta : ℝ),
    0 ≤ eta → (∀ j : Out F, -kmE j ≤ t j ∧ t j ≤ kpE j) →
    -((1 + eta) * hP F kpE kmE ρ) ≤ (1 + eta) * (ρ ⬝ᵥ fun j => t j) ∧
      (1 + eta) * (ρ ⬝ᵥ fun j => t j) ≤ (1 + eta) * hM F kpE kmE ρ

/-- Part 3, one fund and one ETF (`N = M = 1`), fund holding `a`, ETF holding `p`, `r = Q₀₀`,
`v = V₀₀`, `σ = Σ₀₀`:
- traded ETF (line `g_E = η + (1 + η) t_E`): the fund line is `α~ + r(η + (1 + η)t_E) - γ v a = η + (1 + η)t_A`;
- fixed ETF: the fund line is `α~ + r μ_E - γ(v + r²σ)a - γ r σ p = η + (1 + η)t_A`;
- the at-zero test for an ETF starting at zero: at zero iff `μ_E - γ σ r a ≤ η + (1 + η)κ⁺_E`. -/
def OneOne : Prop :=
  ∀ (P : Coord 1 1), 0 < P.gamma → P.Sig.PosDef → ∀ (a p eta tE tA : ℝ),
    (gE P (expo P (fun _ => a) (fun _ => p)) 0 = eta + (1 + eta) * tE →
      (gA P (fun _ => a) (expo P (fun _ => a) (fun _ => p)) 0 = eta + (1 + eta) * tA ↔
        P.alt 0 + P.Q 0 0 * (eta + (1 + eta) * tE) - P.gamma * P.V 0 0 * a = eta + (1 + eta) * tA)) ∧
    (gA P (fun _ => a) (expo P (fun _ => a) (fun _ => p)) 0 = eta + (1 + eta) * tA ↔
      P.alt 0 + P.Q 0 0 * P.mu 0 - P.gamma * (P.V 0 0 + P.Q 0 0 ^ 2 * P.Sig 0 0) * a -
        P.gamma * P.Q 0 0 * P.Sig 0 0 * p = eta + (1 + eta) * tA) ∧
    ∀ (kp ζ : ℝ), 0 ≤ p → 0 ≤ ζ → (0 < p → ζ = 0) →
      gE P (expo P (fun _ => a) (fun _ => p)) 0 = thr eta kp - ζ →
      (p = 0 ↔ P.mu 0 - P.gamma * P.Sig 0 0 * P.Q 0 0 * a ≤ thr eta kp)

/-- Part 4b, an interior ETF's line at `x_2`, `-ζ*_j = η + (1 + η) t_j` with `ζ*_j, η, κ^± ≥ 0`:
- bought (`t_j = κ⁺`) forces `η = 0`, `κ⁺ = 0` and `ζ*_j = 0`;
- sold (`t_j = -κ⁻`) is the coincidence `(1 + η)κ⁻ = η + ζ*_j`;
- untraded (`t_j ∈ [-κ⁻, κ⁺]`) forces `κ⁻ ≥ (η + ζ*_j)/(1 + η)`. -/
def EtfLines : Prop :=
  ∀ (eta ζ kp km t : ℝ), 0 ≤ eta → 0 ≤ ζ → 0 ≤ kp → 0 ≤ km → -ζ = eta + (1 + eta) * t →
    (t = kp → eta = 0 ∧ kp = 0 ∧ ζ = 0) ∧ (t = -km → (1 + eta) * km = eta + ζ) ∧
    (-km ≤ t → t ≤ kp → (eta + ζ) / (1 + eta) ≤ km)

/-- The factor Markowitz exposure `(γΣ_EE)⁻¹ μ_E`. -/
def wTB (P : Coord M N) : Fin M → ℝ := (P.gamma • P.Sig)⁻¹ *ᵥ P.mu

/-- Part 4c, the soft procedure, for any convex feasible set `Feas` of `(x^A, x^E)` and any concave
remainder `K` (fund terms, fund and ETF trading costs, ETF residual risk; the budget and the zero bound
in `Feas`). The joint objective is `G_E(w) + K` and the soft stage 2's is
`-(γ/2)(w - w_s)'Σ_EE(w - w_s) + K`, with `w = x^E + Q x^A`.
- If `w_TB ∈ R_E` then `ν_E = 0` and `Λ_s = 0`.
- Always `0 ≤ Λ_s ≤ ν_E'(w_J - w_{s2})`, which is `ζ*'(w_{s2} - w_J)` when `ν_E = -ζ*`.
- `Λ_s = 0` iff the joint optimum solves the soft stage 2. -/
def Soft : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), 0 < P.gamma → P.Sig.PosDef →
    ∀ (Feas : Set ((Fin N → ℝ) × (Fin M → ℝ))) (K : (Fin N → ℝ) × (Fin M → ℝ) → ℝ),
      Convex ℝ Feas → ConcaveOn ℝ Feas K →
      ∀ (RE : Set (Fin M → ℝ)) (ws : Fin M → ℝ) (ps pJ : (Fin N → ℝ) × (Fin M → ℝ)),
        ws ∈ RE → IsMaxOn (GE P) RE ws →
        ps ∈ Feas → IsMaxOn (fun q => -(P.gamma / 2 * ((expo P q.1 q.2 - ws) ⬝ᵥ
          (P.Sig *ᵥ (expo P q.1 q.2 - ws)))) + K q) Feas ps →
        pJ ∈ Feas → IsMaxOn (fun q => GE P (expo P q.1 q.2) + K q) Feas pJ →
        let nu := P.mu - P.gamma • (P.Sig *ᵥ ws)
        let Ls := (GE P (expo P pJ.1 pJ.2) + K pJ) - (GE P (expo P ps.1 ps.2) + K ps)
        (wTB P ∈ RE → nu = 0 ∧ Ls = 0) ∧ 0 ≤ Ls ∧
        Ls ≤ nu ⬝ᵥ (expo P pJ.1 pJ.2 - expo P ps.1 ps.2) ∧
        (Ls = 0 ↔ IsMaxOn (fun q => -(P.gamma / 2 * ((expo P q.1 q.2 - ws) ⬝ᵥ
          (P.Sig *ᵥ (expo P q.1 q.2 - ws)))) + K q) Feas pJ)


/-- Part 2c's special cases.
- Every ETF traded (`F = ∅`): `ρ_{iT} = r_i`, `V^{F,T} = V` and `α^{F,T}_i = α~_i + r_i'π`. This is claim
  102's pinned-slope threshold, with cash shift `η(1 - Σ_j r_ij)`.
- Every ETF fixed (`F` everything): `α^{F,T}_i = α~_i + r_i'μ_E - γ r_i'Σ_EE x^E` and
  `V^{F,T} x^A = V x^A + Q'Σ_EE Q x^A`.
- Frictionless traded ETFs with a slack budget (`π_T = 0`) and no idle ETF (`x_F = 0`): `α^{F,T} = α^Z`,
  claim 040's, with `Z = F`. -/
def SpecialCases : Prop :=
  ∀ (M N : ℕ) (P : Coord M N) (eta : ℝ) (t : Fin M → ℝ) (xE : Fin M → ℝ) (xA : Fin N → ℝ) (i : Fin N),
    (rho P ∅ i = (fun j : Out (∅ : Finset (Fin M)) => P.Q j i) ∧ VZ P ∅ = P.V ∧
      alphaFT P ∅ eta t xE i = P.alt i + ∑ j : Out (∅ : Finset (Fin M)), P.Q j i * (eta + (1 + eta) * t j)) ∧
    (alphaFT P Finset.univ eta t xE i =
        P.alt i + ∑ j, P.Q j i * P.mu j - P.gamma * ∑ j, P.Q j i * (P.Sig *ᵥ xE) j ∧
      (VZ P Finset.univ *ᵥ xA) i = (P.V *ᵥ xA) i + ∑ j, P.Q j i * (P.Sig *ᵥ (P.Q *ᵥ xA)) j) ∧
    ∀ F : Finset (Fin M), (∀ j : Out F, eta + (1 + eta) * t j = 0) → (∀ j ∈ F, xE j = 0) →
      alphaFT P F eta t xE i = alphaZ P F i

/-! ### Part 1 and 4a (given AX-13), on claim 027's `Data` in claim 104's reference case -/

section Criterion

open Standalone.M2ScoreAccounting Standalone.M2ActionClasses Standalone.M7TwoStageExactnessLoss

/-- Part 1's criterion at `x`: some `η ≥ 0` with `η k(x) = 0`, slopes `t` in the trade-sign sets (claim
040's convention at every ETF at zero) and slacks `ζ ≥ 0`, zero off zero, with every ETF's line
`g_j = η + (1 + η) t_j - ζ_j`, every fund's marginal `A_i + r_i'(η 1 + (1 + η) t_E) - Σ_j r_ij ζ_j`, and
every fund's line `g_i = η + (1 + η) t_i` with the box signs. -/
def Criterion {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (θ : Params m K)
    (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ) (x : Inst m K → ℝ) : Prop :=
  ∃ (η : ℝ) (t : Inst m K → ℝ) (ζ : Fin K → ℝ), 0 ≤ η ∧ η * cash D x = 0 ∧
    (∀ l, InSlope D x l (t l)) ∧ (∀ j, x (Sum.inr j) = 0 → t (Sum.inr j) = tconv D j) ∧
    (∀ j, 0 ≤ ζ j ∧ (0 < x (Sum.inr j) → ζ j = 0) ∧
      grad D θ x (Sum.inr j) = η + (1 + η) * t (Sum.inr j) - ζ j) ∧
    (∀ i, grad D θ x (Sum.inl i) = Ared D θ V SE x i +
      rvec D i ⬝ᵥ (fun j => η + (1 + η) * t (Sum.inr j)) - ∑ j, rvec D i j * ζ j) ∧
    ∀ i, BoxSign (D.wbar (Sum.inl i)) (x (Sum.inl i)) (grad D θ x (Sum.inl i) - η - (1 + η) * t (Sum.inl i))

/-- Part 1 (given AX-13): with spanning ETFs, the reference case and no binding ETF caps, a feasible
`x` is the optimum iff part 1's criterion holds at it. The necessity is claim 040's part 1, and the
converse is claim 104's part 0. -/
def Part1 : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det →
    ∀ x ∈ F D, (∀ j, x (Sum.inr j) < D.wbar (Sum.inr j)) →
      (IsMaxOn (fun w => score D w θ) (F D) x ↔ Criterion D θ V SE x)

/-- Part 4a (given AX-13): a feasible stage-2 holding `x₂` (no binding ETF cap) is exact, `T = J`, iff
part 1's criterion holds at `x₂`. -/
def ExactAtX2 : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det →
    ∀ x2 ∈ F D, (∀ j, x2 (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∀ xJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) xJ →
      (score D x2 θ = score D xJ θ ↔ Criterion D θ V SE x2)

end Criterion

/-! ### Part 4a-4b in coordinates, at the fibre-confined stage 2 (`Σ_E = 0`) -/

open Standalone.M7TwoStageEtfsAtZero in
/-- Part 4a's lines at `x₂` and 4b. Claim 041's `TS` extends claim 040's `Coord`. Take stage 1's exposure
`w*` (a maximizer over `W_F`), `x₂^A` on its fibre and `x₂^E = w* - Q x₂^A`. Then:
- `g_E = -ζ*`, and every fund's marginal is `α~_i - γ(V x₂^A)_i - r_i'ζ*`;
- every ETF interior at `x₂` has `ζ*_j = 0` (claim 041's complementarity), so its line is
  `0 = η + (1 + η) t_j`: bought gives `η = 0` and `κ⁺ = 0`; sold gives `(1 + η)κ⁻ = η`; untraded gives
  `κ⁻ ≥ η/(1 + η)`. -/
def LinesAtX2 : Prop :=
  ∀ (M N : ℕ) (P : TS M N), P.Setting →
    ∀ (ws : Fin M → ℝ) (x2 : Fin N → ℝ), ws ∈ P.WF → IsMaxOn P.GE P.WF ws → x2 ∈ P.fibre ws →
      let xE2 := ws - P.Q *ᵥ x2
      expo P.toCoord x2 xE2 = ws ∧ gE P.toCoord ws = -P.zeta ws ∧
      (∀ i, gA P.toCoord x2 ws i = P.alt i - P.gamma * (P.V *ᵥ x2) i - (P.Qᵀ *ᵥ P.zeta ws) i) ∧
      ∀ j, 0 < xE2 j → P.zeta ws j = 0 ∧
        ∀ (eta kp km t : ℝ), 0 ≤ eta → 0 ≤ kp → 0 ≤ km → gE P.toCoord ws j = eta + (1 + eta) * t →
          (t = kp → eta = 0 ∧ kp = 0) ∧ (t = -km → (1 + eta) * km = eta) ∧
          (-km ≤ t → t ≤ kp → eta / (1 + eta) ≤ km)

/-- Claim 109, parts 1-4 (part 5 is prose). -/
def statement : Prop :=
  Part1 ∧ Explicit ∧ SpecialCases ∧ AtZeroTests ∧ Bracket ∧ OneOne ∧ ExactAtX2 ∧ LinesAtX2 ∧ EtfLines ∧ Soft

end

end Standalone.M7EtfsAtZeroCostsBudget

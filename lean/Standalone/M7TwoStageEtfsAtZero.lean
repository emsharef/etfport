import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.OrdConnected
import Standalone.M7FundDecisionEtfsAtZero

/-!
# Claim 041: two-stage exactness when ETFs sit at their zero bound

Statement only; the proof is `Novel/M7TwoStageEtfsAtZeroProof.lean`.

The objects are claim 040's ETF coordinates at one review with fees off (the claim's Setting).
`TS` extends claim 040's `Coord` (`lean/Standalone/M7FundDecisionEtfsAtZero.lean`), and `GE` and `VE`
are claim 040's (Q-04; `Sig` is `Σ_EE`, `alt` is `α̂` with fees off, `xbar` the fund caps). This
claim's own objects are the slack `zeta w = γΣ_EE w - μ_E` at a given exposure (claim 040's `zeta q` is
the same slack at `w(q)`) and `wTB`. The
reduction of M7 to these coordinates (claim 040 part 0, claim 104 part 1) is prose, and so is the
Reading of part 4.
- `M` ETFs and `N` funds; `mu` is `μ_E`, `Sig` is `Σ_EE` (positive definite), `gamma > 0`, and `Q` is
  the netting matrix, with column `i` the fund's by-product `r_i`.
- The fund box `0 ≤ x ≤ x̄`, fund covariance `V` (positive semidefinite), rates `κ⁺, κ⁻ ≥ 0` and
  incumbents `x⁻` in the box.
- `GE w = μ_E'w - (γ/2) w'Σ_EE w` and `H x = α̂'x - (γ/2) x'Vx - C_A(x - x⁻)`.
- `WF = {w : w ≥ Qx for some x in the box}` and `fibre w = {x in the box : Qx ≤ w}`.
- `Feas = {(w, x) : x in the box, Qx ≤ w}` is the joint feasible set, `Jobj (w, x) = GE w + H x`.
- `zeta w = γΣ_EE w - μ_E`, so stage 1's slacks are `zeta w*`.
- `wTB = (γΣ_EE)⁻¹ μ_E` is the factor Markowitz exposure.
- Maximizers are Mathlib's `IsMaxOn` together with membership. Every result is stated for any
  maximizers, and `Existence` shows they exist.

**Forms of the approved Statement** (math's revision bde0fc3c on leanb's report, and red's 9d5c055d):
- Part 3(b)'s "only if" is false; `Soft` states the true form.
- Part 3(b)'s bound uses stage 2's exposure `w_2`. With stage 1's `w_s`, as displayed, the bound
  would force a zero loss.
- Part 2's "`Z(rx)` empty on the maximizing interval" holds on its interior only. `OneFund` states
  that `ζ(rx) = 0` there, in the form `V_E(rx) = GE(wTB)`.
- Part 3(b)'s one-fund reachability display also needs `wTB_j ≥ 0` wherever `r_j = 0`.
-/

namespace Standalone.M7TwoStageEtfsAtZero

open Matrix Finset
open scoped Classical

noncomputable section

/-- The one-review data: claim 040's coordinates. -/
structure TS (M N : ℕ) extends Standalone.M7FundDecisionEtfsAtZero.Coord M N

namespace TS

variable {M N : ℕ} (P : TS M N)

/-- The standing assumptions. -/
def Setting : Prop :=
  0 < P.gamma ∧ P.Sigᵀ = P.Sig ∧ (∀ v : Fin M → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (P.Sig *ᵥ v)) ∧ P.Vᵀ = P.V ∧
    (∀ v : Fin N → ℝ, 0 ≤ v ⬝ᵥ (P.V *ᵥ v)) ∧
    ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i ∧ 0 < P.xbar i ∧ 0 ≤ P.xm i ∧ P.xm i ≤ P.xbar i

/-- `G_E(w) = μ_E'w - (γ/2) w'Σ_EE w` (claim 040's). -/
abbrev GE (w : Fin M → ℝ) : ℝ := Standalone.M7FundDecisionEtfsAtZero.GE P.toCoord w

/-- `V_E(q) = max {G_E(w) : w ≥ q}` (claim 040's). -/
abbrev VE (q : Fin M → ℝ) : ℝ := Standalone.M7FundDecisionEtfsAtZero.VE P.toCoord q

/-- The slack `ζ(w) = γΣ_EE w - μ_E` at an exposure `w`. -/
def zeta (w : Fin M → ℝ) : Fin M → ℝ := P.gamma • (P.Sig *ᵥ w) - P.mu

/-- The factor Markowitz exposure `(γΣ_EE)⁻¹ μ_E`. -/
def wTB : Fin M → ℝ := (P.gamma • P.Sig)⁻¹ *ᵥ P.mu

/-- The funds' trade cost `C_A(u)`. -/
def cA (u : Fin N → ℝ) : ℝ := ∑ i, (P.kp i * max (u i) 0 + P.km i * max (-u i) 0)

/-- The fund terms `H(x) = α̂'x - (γ/2) x'Vx - C_A(x - x⁻)`. -/
def H (x : Fin N → ℝ) : ℝ := P.alt ⬝ᵥ x - P.gamma / 2 * (x ⬝ᵥ (P.V *ᵥ x)) - P.cA (x - P.xm)

/-- The fund box. -/
def box : Set (Fin N → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ P.xbar i}

/-- Stage 1's feasible exposures `W_F = Q(box) + ℝ^M_+`. -/
def WF : Set (Fin M → ℝ) := {w | ∃ x ∈ P.box, P.Q *ᵥ x ≤ w}

/-- The fibre of an exposure `w`: fund holdings whose by-product it covers. -/
def fibre (w : Fin M → ℝ) : Set (Fin N → ℝ) := {x | x ∈ P.box ∧ P.Q *ᵥ x ≤ w}

/-- The joint feasible set. -/
def Feas : Set ((Fin M → ℝ) × (Fin N → ℝ)) := {p | p.2 ∈ P.box ∧ P.Q *ᵥ p.2 ≤ p.1}

/-- The joint objective. -/
def Jobj (p : (Fin M → ℝ) × (Fin N → ℝ)) : ℝ := P.GE p.1 + P.H p.2

/-- Claim 040's band for every fund at `x`, with ETF prices `z`: with
`g_i = α̂_i - γ(Vx)_i - r_i'z`, `g_i = κ⁺_i` for a purchase (`≥` at the cap), `g_i = -κ⁻_i` for a sale
(`≤` at zero), and `g_i ∈ [-κ⁻_i, κ⁺_i]` for a hold, one-sided at the box. -/
def FundLines (x : Fin N → ℝ) (z : Fin M → ℝ) : Prop :=
  ∀ i, let g := P.alt i - P.gamma * (P.V *ᵥ x) i - (P.Qᵀ *ᵥ z) i
    (P.xm i < x i → (x i < P.xbar i → g = P.kp i) ∧ (x i = P.xbar i → P.kp i ≤ g)) ∧
    (x i < P.xm i → (0 < x i → g = -P.km i) ∧ (x i = 0 → g ≤ -P.km i)) ∧
    (x i = P.xm i → (0 < x i → -P.km i ≤ g) ∧ (x i < P.xbar i → g ≤ P.kp i))

/-- The soft stage 2's objective around stage 1's exposure `ws`. -/
def softObj (ws : Fin M → ℝ) (p : (Fin M → ℝ) × (Fin N → ℝ)) : ℝ :=
  P.H p.2 - P.gamma / 2 * ((p.1 - ws) ⬝ᵥ (P.Sig *ᵥ (p.1 - ws)))


end TS

/-! ### One fund -/

namespace TS

variable {M : ℕ} (P : TS M 1)

/-- The by-product vector `r`. -/
def r : Fin M → ℝ := fun j => P.Q j 0

/-- The fibre interval's lower end `max(0, max_{r_j < 0} w_j/r_j)`. -/
def xlo (w : Fin M → ℝ) : ℝ :=
  (insert 0 ((univ.filter fun j => P.r j < 0).image fun j => w j / P.r j)).max' (insert_nonempty _ _)

/-- The fibre interval's upper end `min(x̄, min_{r_j > 0} w_j/r_j)`. -/
def xhi (w : Fin M → ℝ) : ℝ :=
  (insert (P.xbar 0) ((univ.filter fun j => 0 < P.r j).image fun j => w j / P.r j)).min'
    (insert_nonempty _ _)

/-- `clip(y, a, b) = min(max(y, a), b)`. -/
def clip (y a b : ℝ) : ℝ := min (max y a) b

/-- Claim 102 part 3's frictionless band solution. -/
def xf : ℝ :=
  clip (P.xm 0) ((P.alt 0 - P.kp 0) / (P.gamma * P.V 0 0)) ((P.alt 0 + P.km 0) / (P.gamma * P.V 0 0))

/-- `Φ(x) = H(x) + V_E(rx)`. -/
def Phi (x : ℝ) : ℝ := P.H (fun _ => x) + P.VE (x • P.r)

end TS

open TS

/-- Existence and uniqueness: stage 1's exposure exists and is unique, stage 2 has a maximizer on
every nonempty fibre, and the joint problem has a maximizer. -/
def Existence : Prop :=
  ∀ (M N : ℕ) (P : TS M N), P.Setting →
    (∃ ws ∈ P.WF, IsMaxOn P.GE P.WF ws ∧ ∀ w ∈ P.WF, IsMaxOn P.GE P.WF w → w = ws) ∧
    (∀ ws ∈ P.WF, ∃ x ∈ P.fibre ws, IsMaxOn P.H (P.fibre ws) x) ∧
    (∃ p ∈ P.Feas, IsMaxOn P.Jobj P.Feas p)

/-- Part 1: stage 1's slacks are nonnegative and complementary to stage 2's fibre, and the
fibre-confined procedure is exact iff the fund lines hold at `x_2` with stage 1's slacks. Stage 1's
exposure is optimal for stage 2's by-product, `V_E(Qx₂) = G_E(w*)` (part 2's no-misfit fact, any `N`). -/
def StageSlacks : Prop :=
  ∀ (M N : ℕ) (P : TS M N), P.Setting →
    ∀ (ws : Fin M → ℝ) (x2 : Fin N → ℝ) (pJ : (Fin M → ℝ) × (Fin N → ℝ)),
      ws ∈ P.WF → IsMaxOn P.GE P.WF ws → x2 ∈ P.fibre ws → IsMaxOn P.H (P.fibre ws) x2 →
      pJ ∈ P.Feas → IsMaxOn P.Jobj P.Feas pJ →
      (∀ j, 0 ≤ P.zeta ws j) ∧ (∀ j, (P.Q *ᵥ x2) j < ws j → P.zeta ws j = 0) ∧
      (P.GE ws + P.H x2 = P.Jobj pJ ↔ P.FundLines x2 (P.zeta ws)) ∧
      P.VE (P.Q *ᵥ x2) = P.GE ws

/-- Part 2, one fund (`v = V₀₀ > 0`). The statement has six groups.
- Stage 1 as a choice of holding: some `x₁ ∈ [0, x̄]` has `w* = w(r x₁)`, and `G_E(w*)` is the
  maximum of `V_E(rx)` over the box. The maximizing holdings form an interval. When `wTB ∈ W_F`,
  they are the `x` with `rx ≤ wTB`, where `V_E(rx) = G_E(wTB)`.
- The fibre is the interval `[x_lo, x_hi]`, which contains every such `x₁`. An ETF at zero at
  stage 1 with `r_j > 0` puts `x₁` at the upper end; one with `r_j < 0` puts it at the lower end.
- Stage 2's holding is the clip of the band solution to `[x_lo, x_hi]`.
- Exactness holds iff `x₂ = x_J`. It holds if `x_J` is strictly inside the interval, and it
  requires `x_J` in the interval. In fact it holds iff `x_J` is in the interval (a strengthening).
- The loss is the misplacement `Φ(x_J) - Φ(x₂) ≥ 0`, zero iff `x₂ = x_J`: `J = Φ(x_J)` and `T = Φ(x₂)`,
  there being no exposure-misfit term (`StageSlacks` states `V_E(Qx₂) = G_E(w*)` for any `N`).
- `wTB ∈ W_F` iff `x_lo(wTB) ≤ x_hi(wTB)` and `wTB_j ≥ 0` wherever `r_j = 0` (the second condition
  is missing from the prose display). -/
def OneFund : Prop :=
  ∀ (M : ℕ) (P : TS M 1), P.Setting → 0 < P.V 0 0 →
    ∀ (ws : Fin M → ℝ) (x2 : Fin 1 → ℝ) (pJ : (Fin M → ℝ) × (Fin 1 → ℝ)),
      ws ∈ P.WF → IsMaxOn P.GE P.WF ws → x2 ∈ P.fibre ws → IsMaxOn P.H (P.fibre ws) x2 →
      pJ ∈ P.Feas → IsMaxOn P.Jobj P.Feas pJ →
      let xJ := pJ.2 0
      let Lam := P.Jobj pJ - (P.GE ws + P.H x2)
      (∃ x1, 0 ≤ x1 ∧ x1 ≤ P.xbar 0 ∧ x1 • P.r ≤ ws ∧ IsMaxOn P.GE {w | x1 • P.r ≤ w} ws) ∧
      (∀ x, 0 ≤ x → x ≤ P.xbar 0 → P.VE (x • P.r) ≤ P.GE ws) ∧
      Set.OrdConnected {x | 0 ≤ x ∧ x ≤ P.xbar 0 ∧ P.VE (x • P.r) = P.GE ws} ∧
      (P.wTB ∈ P.WF → {x | 0 ≤ x ∧ x ≤ P.xbar 0 ∧ P.VE (x • P.r) = P.GE ws} =
        {x | 0 ≤ x ∧ x ≤ P.xbar 0 ∧ x • P.r ≤ P.wTB} ∧
        ∀ x, 0 ≤ x → x ≤ P.xbar 0 → x • P.r ≤ P.wTB → P.VE (x • P.r) = P.GE P.wTB) ∧
      (∀ x : Fin 1 → ℝ, x ∈ P.fibre ws ↔ P.xlo ws ≤ x 0 ∧ x 0 ≤ P.xhi ws) ∧
      (∀ x1, 0 ≤ x1 → x1 ≤ P.xbar 0 → x1 • P.r ≤ ws → IsMaxOn P.GE {w | x1 • P.r ≤ w} ws →
        P.xlo ws ≤ x1 ∧ x1 ≤ P.xhi ws ∧
        (∀ j, 0 < P.r j → ws j = P.r j * x1 → x1 = P.xhi ws) ∧
        (∀ j, P.r j < 0 → ws j = P.r j * x1 → x1 = P.xlo ws)) ∧
      x2 0 = clip P.xf (P.xlo ws) (P.xhi ws) ∧
      (Lam = 0 ↔ x2 0 = xJ) ∧
      (P.xlo ws < xJ → xJ < P.xhi ws → x2 0 = xJ) ∧
      (x2 0 = xJ → P.xlo ws ≤ xJ ∧ xJ ≤ P.xhi ws) ∧
      P.Jobj pJ = P.Phi xJ ∧ P.GE ws + P.H x2 = P.Phi (x2 0) ∧
      Lam = P.Phi xJ - P.Phi (x2 0) ∧ 0 ≤ Lam ∧
      (Lam = 0 ↔ P.xlo ws ≤ xJ ∧ xJ ≤ P.xhi ws) ∧
      (P.wTB ∈ P.WF ↔ P.xlo P.wTB ≤ P.xhi P.wTB ∧ ∀ j, P.r j = 0 → 0 ≤ P.wTB j)

/-- Part 3. (a) If `wTB ∈ R_E`, stage 1's multiplier `ν_E = μ_E - γΣ_EE w_s` is zero and the soft
procedure is exact. (b) With `R_E = W_F`: `ν_E = 0` iff `wTB ∈ W_F`, and then the procedure is
exact. Otherwise `ν_E ≠ 0` lies in the normal cone of `W_F` at `w_s`,
`0 ≤ Λ_s ≤ ν_E'(w_J - w_2)` with `w_2` stage 2's exposure, and the procedure is exact iff the joint
optimum also solves the `ν_E`-tilted stage 2 (the soft stage 2). -/
def Soft : Prop :=
  ∀ (M N : ℕ) (P : TS M N), P.Setting →
    ∀ (RE : Set (Fin M → ℝ)) (ws : Fin M → ℝ) (p2 pJ : (Fin M → ℝ) × (Fin N → ℝ)),
      ws ∈ RE → IsMaxOn P.GE RE ws → p2 ∈ P.Feas → IsMaxOn (P.softObj ws) P.Feas p2 →
      pJ ∈ P.Feas → IsMaxOn P.Jobj P.Feas pJ →
      let nu := P.mu - P.gamma • (P.Sig *ᵥ ws)
      let Ls := P.Jobj pJ - P.Jobj p2
      (P.wTB ∈ RE → nu = 0 ∧ Ls = 0) ∧
      (RE = P.WF →
        (nu = 0 ↔ P.wTB ∈ P.WF) ∧
        (P.wTB ∉ P.WF → nu ≠ 0 ∧ (∀ w ∈ P.WF, nu ⬝ᵥ (w - ws) ≤ 0) ∧
          0 ≤ Ls ∧ Ls ≤ nu ⬝ᵥ (pJ.1 - p2.1) ∧ (Ls = 0 ↔ IsMaxOn (P.softObj ws) P.Feas pJ)))

/-- Claim 041, parts 1-3. -/
def statement : Prop := Existence ∧ StageSlacks ∧ OneFund ∧ Soft

end

end Standalone.M7TwoStageEtfsAtZero

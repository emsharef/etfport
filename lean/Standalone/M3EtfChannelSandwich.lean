import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M3FiniteContinuation

/-!
# Claim 022: the ETF-adjustment channel is sandwiched by premia at the two root optima

Statement only; the proof is `Novel/M3EtfChannelSandwichProof.lean`.

M3 is claim 011's formalization (`Standalone/M3FiniteContinuation.lean`): `M3`, `M3Setting`,
`Feas1`, `h1`, `H0`, `V`, `CE`, `Delta`, `Pol`, `Phi` and `obs`. Root classes `D₀` are
`Feas1 P d x⁻ h⁻`.

- `cR P r u₀ = -(1/ρ) ln(-H₀^R(u₀))` is the root-action continuation certainty equivalent.
- `phi = c_E - c_N` is the premium of future ETF adjustment, and `psi = c_F - c_E` that of future
  active trading.
- `RootOpt P d r u₀` means `u₀` maximizes `c_R` over the root class `d`: `A_R` for `d = F` and
  `B_R` for `d = E`.
- `beta P G L u₀` is the funded cap for any upper bound `G` and lower bound `L` on the ETFs' gross
  returns. The claim's `ḡ_E`, `g̲_E` are the tightest such bounds. `up = (G - 1)⁺`, `down = (1 - L)⁺`,
  and `β = [h₀⁺ up + (Σ_j x⁺_{0,j}) G (up + down)] / W₀⁻`.

The sure-active family `saInst` has one active fund and one ETF with `B^A = (1, 0)` and
`B^E = (0, 1)`, zero drag, `ρ = 20`, cash one, no risky holdings, and one scenario with zero shocks.
Its parameters are `θ₊ = (1/2, 1/2, 0)` (`true`) with prior `1/3` and `θ₋ = (1/2, -1/2, 0)`
(`false`) with prior `2/3`. `kA, kE` are the purchase rates and `sA, sE` the sale rates, each in
`[0, 1/200]`.
-/

namespace Standalone.M3EtfChannelSandwich

open Matrix Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation

noncomputable section

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-- `c_R(u₀) = -(1/ρ) ln(-H₀^R(u₀))`. -/
def cR (P : M3 n K S T) (r : Cls) (u₀ : Inst 1 n → ℝ) : ℝ :=
  -(1 / P.rho) * Real.log (-H0 P r u₀)

/-- The premium of future ETF adjustment `φ = c_E - c_N`. -/
def phi (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) : ℝ := cR P .E u₀ - cR P .N u₀

/-- The premium of future active trading `ψ = c_F - c_E`. -/
def psi (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) : ℝ := cR P .F u₀ - cR P .E u₀

/-- `u₀` maximizes `c_R` over the root class `d`. -/
def RootOpt (P : M3 n K S T) (d r : Cls) (u₀ : Inst 1 n → ℝ) : Prop :=
  Feas1 P d P.D.x0 P.D.h0 u₀ ∧ ∀ u₀', Feas1 P d P.D.x0 P.D.h0 u₀' → cR P r u₀' ≤ cR P r u₀

/-- The funded cap `β(u₀)` for ETF gross-return bounds `L ≤ 1 + r_E ≤ G`. -/
def beta (P : M3 n K S T) (G L : ℝ) (u₀ : Inst 1 n → ℝ) : ℝ :=
  (h1 P u₀ * max (G - 1) 0 +
    (∑ j, (P.D.x0 (Sum.inr j) + u₀ (Sum.inr j))) * G * (max (G - 1) 0 + max (1 - L) 0)) / W0 P.D

/-- Part 0: for every `(D, R)`, `CE_{D,R} = max_{D₀} c_R`, attained; the premia are nonnegative on
the full root class. -/
def Premia : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    (∀ d r : Cls, (∃ u₀, RootOpt P d r u₀) ∧
      ∀ u₀, RootOpt P d r u₀ → cR P r u₀ = CE P d r) ∧
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → 0 ≤ phi P u₀ ∧ 0 ≤ psi P u₀

/-- Part 1: the sandwich, for every choice of root optimizers. -/
def Sandwich : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ AN AE AF BN BE BF : Inst 1 n → ℝ,
      RootOpt P .F .N AN → RootOpt P .F .E AE → RootOpt P .F .F AF →
      RootOpt P .E .N BN → RootOpt P .E .E BE → RootOpt P .E .F BF →
      phi P AN - phi P BE ≤ Delta P .E - Delta P .N ∧
      Delta P .E - Delta P .N ≤ phi P AE - phi P BN ∧
      psi P AE - psi P BF ≤ Delta P .F - Delta P .E ∧
      Delta P .F - Delta P .E ≤ psi P AF - psi P BE

/-- Part 2: the funded cap `0 ≤ φ ≤ β` for every feasible root trade and any ETF gross-return
bounds; `φ = 0` at a root with no cash and no ETF holding; and the funded corner sign condition. -/
def FundedCap : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    (∀ G L : ℝ, (∀ j t s, 1 + ret P.D (P.par t) s (Sum.inr j) ≤ G) →
      (∀ j t s, L ≤ 1 + ret P.D (P.par t) s (Sum.inr j)) →
      ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → 0 ≤ phi P u₀ ∧ phi P u₀ ≤ beta P G L u₀) ∧
    (∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → h1 P u₀ = 0 →
      (∀ j, P.D.x0 (Sum.inr j) + u₀ (Sum.inr j) = 0) → phi P u₀ = 0) ∧
    ∀ AE BN : Inst 1 n → ℝ, RootOpt P .F .E AE → RootOpt P .E .N BN → h1 P AE = 0 →
      (∀ j, P.D.x0 (Sum.inr j) + AE (Sum.inr j) = 0) →
      Delta P .E - Delta P .N ≤ -phi P BN ∧ -phi P BN ≤ 0

/-- Part 3: movement of the no-active-trade region, read with claim 011's value test. -/
def RegionMovement : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ AN AE BN BE : Inst 1 n → ℝ,
      RootOpt P .F .N AN → RootOpt P .F .E AE → RootOpt P .E .N BN → RootOpt P .E .E BE →
      (Delta P .N = 0 → phi P AE ≤ phi P BN →
        Delta P .E = 0 ∧ ∃ π ∈ Pol P .F .E, IsMaxOn (Phi P) (Pol P .F .E) π ∧ π.1 (Sum.inl 0) = 0) ∧
      (Delta P .E = 0 → phi P BE ≤ phi P AN →
        Delta P .N = 0 ∧ ∃ π ∈ Pol P .F .N, IsMaxOn (Phi P) (Pol P .F .N) π ∧ π.1 (Sum.inl 0) = 0)

/-! ### The sure-active family -/

/-- The data: loadings `(1, 0)` and `(0, 1)`, zero drag and shocks, rates, cash one. -/
def saData (kA kE sA sE : ℝ) : Data 1 1 2 (Fin 1) where
  BA := !![1, 0]
  BE := !![0, 1]
  cE := 0
  kplus := Sum.elim (fun _ => kA) (fun _ => kE)
  kminus := Sum.elim (fun _ => sA) (fun _ => sE)
  gamma := 0
  q := fun _ => 1
  zf := 0
  zA := 0
  zE := 0
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- `θ₊ = (1/2, 1/2, 0)` for `true`, `θ₋ = (1/2, -1/2, 0)` for `false`. -/
def saPar : Bool → Params 1 2
  | true => ⟨![1 / 2, 1 / 2], ![0]⟩
  | false => ⟨![1 / 2, -1 / 2], ![0]⟩

/-- The instance: prior `1/3` on `θ₊`, `2/3` on `θ₋`, and `ρ = 20`. -/
def saInst (kA kE sA sE : ℝ) : M3 1 2 (Fin 1) Bool :=
  ⟨saData kA kE sA sE, saPar, fun t => if t then 1 / 3 else 2 / 3, 20⟩

/-- The rate box `[0, 1/200]⁴`. -/
def InBox (kA kE sA sE : ℝ) : Prop :=
  0 ≤ kA ∧ kA ≤ 1 / 200 ∧ 0 ≤ kE ∧ kE ≤ 1 / 200 ∧ 0 ≤ sA ∧ sA ≤ 1 / 200 ∧ 0 ≤ sE ∧ sE ≤ 1 / 200

/-- The all-active root: all cash into the active fund. -/
def allActive (kA : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => 1 / (1 + kA)) (fun _ => 0)

/-- Part 4: every member is an M3 instance whose public observation reveals `θ`; the four
certainty-equivalent bounds and the negative channel; both gaps positive; the all-active root is
feasible with zero premium, and the cash root's premium is at least `1/50 - 1/320000` (part 5's
numeric fact). -/
def SureActive : Prop :=
  ∀ kA kE sA sE, InBox kA kE sA sE →
    let P := saInst kA kE sA sE
    M3Setting P ∧ obs P true (0 : Fin 1) ≠ obs P false 0 ∧
    CE P .E .N = 1 ∧ 1 + 1 / 50 - 1 / 320000 ≤ CE P .E .E ∧ 450 / 201 ≤ CE P .F .N ∧
    CE P .F .E ≤ 9 / 4 ∧
    Delta P .E - Delta P .N ≤ 9 / 804 - 1 / 50 + 1 / 320000 ∧
    (9 / 804 - 1 / 50 + 1 / 320000 : ℝ) < -1 / 125 ∧
    0 < Delta P .N ∧ 0 < Delta P .E ∧
    Feas1 P .F P.D.x0 P.D.h0 (allActive kA) ∧ phi P (allActive kA) = 0 ∧
    1 / 50 - 1 / 320000 ≤ phi P 0

/-- Both signs of the ETF channel occur among M3 instances (with claim 012's family). -/
def BothSigns : Prop :=
  (∃ P : M3 1 2 (Fin 1) Bool, M3Setting P ∧ Delta P .E - Delta P .N < 0) ∧
  ∃ P : M3 1 2 (Fin 1) Bool, M3Setting P ∧ 0 < Delta P .E - Delta P .N

/-- Claim 022, all parts. -/
def statement : Prop :=
  Premia ∧ Sandwich ∧ FundedCap ∧ RegionMovement ∧ SureActive ∧ BothSigns

end

end Standalone.M3EtfChannelSandwich

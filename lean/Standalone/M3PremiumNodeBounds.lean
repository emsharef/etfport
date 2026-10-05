import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Standalone.M3EtfChannelSandwich
import Standalone.OppositeContinuationEffects

/-!
# Claim 023: the premium of future ETF adjustment decomposes across observations

Statement only; the proof is `Novel/M3PremiumNodeBoundsProof.lean`.

M3 is claim 011's formalization: `V1`, `post`, `P0`, `Yset`, `x1`, `h1`, `condW`, `CE`, `Delta`.
Claim 022 supplies the root-action certainty equivalent `cR`, the premium `phi`, root optimizers
`RootOpt`, the funded cap `beta` and the sure-active family `saInst`. Claim 012 supplies its family
`ocInst`.

Wealth quantities are in units of `W₀⁻`: the node certainty equivalents use `V1`, which evaluates
`U(W/W₀⁻)`, and dollar amounts (`h1`, `x1`) are divided by `W0`.

- A *node* is an observation `y ∈ Y` with `P₀(y) > 0`. A *node path* is a pair `(θ, s₁)` with
  `π₁(θ | y) > 0` and `q_{s₁} > 0`.
- `nodeCE P r u₀ y = c^R_y = -(1/ρ) ln(-V₁^R(x₁(y), h, π₁(·|y)))`, `gain = c^E_y - c^N_y` and
  `weight = w_y ∝ P₀(y) exp(-ρ c^N_y)`.
- `agg P u₀ ℓ = -(1/ρ) ln Σ_y w_y exp(-ρ ℓ_y)` aggregates node values. Thus `α(u₀) = agg G^lb`
  and `β_node(u₀) = agg G^ub`; the formal statements hold for every family of valid node lower or
  upper bounds, and the claim's `G^lb` and `G^ub` are instances.
- `tiltMean` is the mean under the tilted node measure `Q_y`, which weights each path by its mass
  times `exp(-ρ W^N_y)`. `rBuy` and `rSell` are `r^±_{j,y}`.
- `riskBound ρ r s H` is `r²/(2ρs²)` when `r ≤ ρ s² H`, and `r H - ρ s² H²/2` otherwise.
-/

namespace Standalone.M3PremiumNodeBounds

open Matrix Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
open Standalone.M3EtfChannelSandwich (cR phi RootOpt beta saInst allActive)
open Standalone.OppositeContinuationEffects (ocInst)

noncomputable section

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-- The node certainty equivalent `c^R_y`. -/
def nodeCE (P : M3 n K S T) (r : Cls) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : ℝ :=
  -(1 / P.rho) * Real.log (-V1 P r (x1 P y u₀) (h1 P u₀) (post P y))

/-- The node gain `G_y = c^E_y - c^N_y`. -/
def gain (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : ℝ :=
  nodeCE P .E u₀ y - nodeCE P .N u₀ y

/-- Unnormalized node weight `P₀(y) exp(-ρ c^N_y)` on nodes. -/
def nodeMass (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : ℝ :=
  if 0 < P0 P y then P0 P y * Real.exp (-P.rho * nodeCE P .N u₀ y) else 0

/-- The node weight `w_y`. -/
def weight (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : ℝ :=
  nodeMass P u₀ y / ∑ y' ∈ Yset P, nodeMass P u₀ y'

/-- The aggregate `-(1/ρ) ln Σ_y w_y exp(-ρ ℓ_y)`. -/
def agg (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (ℓ : Obs n K → ℝ) : ℝ :=
  -(1 / P.rho) * Real.log (∑ y ∈ Yset P, weight P u₀ y * Real.exp (-P.rho * ℓ y))

/-- A node: a possible observation with positive probability. -/
def IsNode (P : M3 n K S T) (y : Obs n K) : Prop := y ∈ Yset P ∧ 0 < P0 P y

/-- A node path `(θ, s₁)` at `y`. -/
def NodePath (P : M3 n K S T) (y : Obs n K) (t : T) (s : S) : Prop :=
  0 < post P y t ∧ 0 < P.D.q s

/-- ETF `j`'s gross return on path `(θ, s)`. -/
def gE (P : M3 n K S T) (j : Fin n) (t : T) (s : S) : ℝ := 1 + ret P.D (P.par t) s (Sum.inr j)

/-- Mean of `Z` under the tilted node measure `Q_y`. -/
def tiltMean (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (Z : T → S → ℝ) : ℝ :=
  (∑ t, ∑ s, post P y t * P.D.q s *
      Real.exp (-P.rho * (condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D)) * Z t s) /
    ∑ t, ∑ s, post P y t * P.D.q s *
      Real.exp (-P.rho * (condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D))

/-- `r^+_{j,y} = E_Q[(g_j - 1 - κ⁺_j)/(1 + κ⁺_j)]`. -/
def rBuy (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (j : Fin n) : ℝ :=
  tiltMean P u₀ y fun t s => (gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))

/-- `r^-_{j,y} = E_Q[1 - κ⁻_j - g_j]`. -/
def rSell (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (j : Fin n) : ℝ :=
  tiltMean P u₀ y fun t s => 1 - P.D.kminus (Sum.inr j) - gE P j t s

/-- The risk-adjusted node bound. -/
def riskBound (ρ r s H : ℝ) : ℝ :=
  if r ≤ ρ * s ^ 2 * H then r ^ 2 / (2 * ρ * s ^ 2) else r * H - ρ * s ^ 2 * H ^ 2 / 2

/-- Part 1: node gains are nonnegative; the weights are a probability on the nodes;
`φ = agg G`, the aggregate is monotone and strictly monotone in each node value, and
`min_y G_y ≤ φ ≤ max_y G_y`. -/
def Decomposition : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ →
      (∀ y, IsNode P y → 0 ≤ gain P u₀ y) ∧
      (∀ y ∈ Yset P, 0 ≤ weight P u₀ y) ∧ (∀ y, IsNode P y → 0 < weight P u₀ y) ∧
      ∑ y ∈ Yset P, weight P u₀ y = 1 ∧
      phi P u₀ = agg P u₀ (gain P u₀) ∧
      (∀ ℓ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → ℓ y ≤ ℓ' y) → agg P u₀ ℓ ≤ agg P u₀ ℓ') ∧
      (∀ ℓ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → ℓ y ≤ ℓ' y) → (∃ y, IsNode P y ∧ ℓ y < ℓ' y) →
        agg P u₀ ℓ < agg P u₀ ℓ') ∧
      ∃ y₁ y₂, IsNode P y₁ ∧ IsNode P y₂ ∧ gain P u₀ y₁ ≤ phi P u₀ ∧ phi P u₀ ≤ gain P u₀ y₂

/-- Part 2: the node lower bounds by adjustable wealth (sure-sign buying and selling,
risk-adjusted buying and selling, for every ETF and every bracket of its return on the node paths),
and their aggregate is at most `φ`. -/
def NodeLower : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ →
      (∀ y, IsNode P y → ∀ j : Fin n,
        (∀ δ, (∀ t s, NodePath P y t s → 1 + δ ≤ gE P j t s) →
          h1 P u₀ / W0 P.D * ((1 + δ) / (1 + P.D.kplus (Sum.inr j)) - 1) ≤ gain P u₀ y) ∧
        (∀ δ, (∀ t s, NodePath P y t s → gE P j t s ≤ 1 - δ) →
          x1 P y u₀ (Sum.inr j) / W0 P.D * (δ - P.D.kminus (Sum.inr j)) ≤ gain P u₀ y) ∧
        (∀ gl gu, (∀ t s, NodePath P y t s → gl ≤ gE P j t s ∧ gE P j t s ≤ gu) →
          (0 < rBuy P u₀ y j →
            riskBound P.rho (rBuy P u₀ y j) ((gu - gl) / 2) (h1 P u₀ / W0 P.D) ≤ gain P u₀ y ∧
            (¬ rBuy P u₀ y j ≤ P.rho * ((gu - gl) / 2) ^ 2 * (h1 P u₀ / W0 P.D) →
              rBuy P u₀ y j * (h1 P u₀ / W0 P.D) / 2 ≤
                riskBound P.rho (rBuy P u₀ y j) ((gu - gl) / 2) (h1 P u₀ / W0 P.D))) ∧
          (0 < rSell P u₀ y j →
            riskBound P.rho (rSell P u₀ y j) ((gu - gl) / 2) (x1 P y u₀ (Sum.inr j) / W0 P.D)
              ≤ gain P u₀ y ∧
            (¬ rSell P u₀ y j ≤ P.rho * ((gu - gl) / 2) ^ 2 * (x1 P y u₀ (Sum.inr j) / W0 P.D) →
              rSell P u₀ y j * (x1 P y u₀ (Sum.inr j) / W0 P.D) / 2 ≤
                riskBound P.rho (rSell P u₀ y j) ((gu - gl) / 2)
                  (x1 P y u₀ (Sum.inr j) / W0 P.D))))) ∧
      ∀ ℓ : Obs n K → ℝ, (∀ y, IsNode P y → ℓ y ≤ gain P u₀ y) → agg P u₀ ℓ ≤ phi P u₀

/-- Part 3: the node caps (for any nonnegative brackets `g - 1 ≤ U`, `1 - g ≤ D` on the node paths
of every ETF), their aggregate bounds `φ` above, and aggregates of caps at most claim 022's `β`
stay at most `β`, which the caps built from global return bounds are. -/
def NodeCap : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ →
      (∀ y, IsNode P y → ∀ U D : ℝ, 0 ≤ U → 0 ≤ D →
        (∀ j t s, NodePath P y t s → gE P j t s - 1 ≤ U ∧ 1 - gE P j t s ≤ D) →
        gain P u₀ y ≤ (h1 P u₀ * U + (∑ j, x1 P y u₀ (Sum.inr j)) * (U + D)) / W0 P.D) ∧
      (∀ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → gain P u₀ y ≤ ℓ' y) → phi P u₀ ≤ agg P u₀ ℓ') ∧
      ∀ G L : ℝ, (∀ j t s, gE P j t s ≤ G) → (∀ j t s, L ≤ gE P j t s) →
        (∀ y ∈ Yset P, (h1 P u₀ * max (G - 1) 0 +
          (∑ j, x1 P y u₀ (Sum.inr j)) * (max (G - 1) 0 + max (1 - L) 0)) / W0 P.D
            ≤ beta P G L u₀) ∧
        ∀ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → ℓ' y ≤ beta P G L u₀) →
          agg P u₀ ℓ' ≤ beta P G L u₀

/-- Part 4: the sufficient sign conditions and their robust forms, for every family of valid node
lower bounds `ℓ` and upper bounds `ℓ'` at the roots named. -/
def SignConditions : Prop :=
  ∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    (∀ AE BN : Inst 1 n → ℝ, RootOpt P .F .E AE → RootOpt P .E .N BN →
      ∀ ℓ' ℓ : Obs n K → ℝ, (∀ y, IsNode P y → gain P AE y ≤ ℓ' y) →
        (∀ y, IsNode P y → ℓ y ≤ gain P BN y) →
        agg P AE ℓ' < agg P BN ℓ → Delta P .E - Delta P .N ≤ agg P AE ℓ' - agg P BN ℓ ∧
          agg P AE ℓ' - agg P BN ℓ < 0) ∧
    (∀ AN BE : Inst 1 n → ℝ, RootOpt P .F .N AN → RootOpt P .E .E BE →
      ∀ ℓ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → ℓ y ≤ gain P AN y) →
        (∀ y, IsNode P y → gain P BE y ≤ ℓ' y) →
        agg P BE ℓ' < agg P AN ℓ → agg P AN ℓ - agg P BE ℓ' ≤ Delta P .E - Delta P .N ∧
          0 < agg P AN ℓ - agg P BE ℓ') ∧
    (∀ u BE : Inst 1 n → ℝ, Feas1 P .F P.D.x0 P.D.h0 u → RootOpt P .E .E BE →
      ∀ ℓ ℓ' : Obs n K → ℝ, (∀ y, IsNode P y → ℓ y ≤ gain P u y) →
        (∀ y, IsNode P y → gain P BE y ≤ ℓ' y) →
        agg P u ℓ - (CE P .F .N - cR P .N u) - agg P BE ℓ' ≤ Delta P .E - Delta P .N) ∧
    ∀ AE v : Inst 1 n → ℝ, RootOpt P .F .E AE → Feas1 P .E P.D.x0 P.D.h0 v →
      ∀ ℓ' ℓ : Obs n K → ℝ, (∀ y, IsNode P y → gain P AE y ≤ ℓ' y) →
        (∀ y, IsNode P y → ℓ y ≤ gain P v y) →
        Delta P .E - Delta P .N ≤ agg P AE ℓ' - agg P v ℓ + (CE P .E .N - cR P .N v)

/-- Part 5 (i): claim 022's sure-active family at zero rates. The full-root optimizer under
future ETF-only trading is uniquely the all-active root, whose node gains are all zero; the
ETF-only root's no-trade optimizer is uniquely cash, where the node bounds `1/2` (the `θ₊` buying
node) and `0` are valid. Their aggregate is `[ln(3/2) - ln(1 + e^{-10}/2)]/20 > 1/50`, and the
channel is at most its negative. -/
def SureActiveCert : Prop :=
  let P := saInst 0 0 0 0
  let a := (Real.log (3 / 2) - Real.log (1 + Real.exp (-10) / 2)) / 20
  (∀ AE, RootOpt P .F .E AE → AE = allActive 0) ∧ (∀ BN, RootOpt P .E .N BN → BN = 0) ∧
  (∀ y, IsNode P y → gain P (allActive 0) y ≤ 0) ∧ agg P (allActive 0) (fun _ => 0) = 0 ∧
  (∀ y, IsNode P y → (if y = obs P true 0 then (1 / 2 : ℝ) else 0) ≤ gain P 0 y) ∧
  agg P 0 (fun y => if y = obs P true 0 then 1 / 2 else 0) = a ∧
  1 / 50 < a ∧ Delta P .E - Delta P .N ≤ -a

/-- Part 5 (ii): claim 012's family at zero rates, with `u = (7/15, 8/15)` (no cash) and the cash
root, which is the unique ETF-only optimizer under future ETF-only trading. The node bounds
`2/15` (the `θ₊` selling node) and `0` at `u`, and the node caps `0` and `1/2` at the cash root, are
valid. With the displayed aggregates, `c_N(u)` and `CE_{F,N} = 5/4`, the robust lower form gives a
positive channel above `3/100`. -/
def ComplementCert : Prop :=
  let P := ocInst 0 0 0 0
  let u : Inst 1 1 → ℝ := Sum.elim (fun _ => 7 / 15) (fun _ => 8 / 15)
  let w := 1 / (1 + Real.exp (-(8 / 3)))
  let al := -(1 / 20) * Real.log (w * Real.exp (-(8 / 3)) + (1 - w))
  let cN := -(1 / 20) * Real.log ((Real.exp (-(71 / 3)) + Real.exp (-(79 / 3))) / 2)
  let bn := -(1 / 20) * Real.log ((1 + Real.exp (-10)) / 2)
  Feas1 P .F P.D.x0 P.D.h0 u ∧ (∀ BE, RootOpt P .E .E BE → BE = 0) ∧ CE P .F .N = 5 / 4 ∧
  cR P .N u = cN ∧
  (∀ y, IsNode P y → (if y = obs P true 0 then (2 / 15 : ℝ) else 0) ≤ gain P u y) ∧
  agg P u (fun y => if y = obs P true 0 then 2 / 15 else 0) = al ∧
  (∀ y, IsNode P y → gain P 0 y ≤ if y = obs P true 0 then 0 else 1 / 2) ∧
  agg P 0 (fun y => if y = obs P true 0 then 0 else 1 / 2) = bn ∧
  al - (5 / 4 - cN) - bn ≤ Delta P .E - Delta P .N ∧ 3 / 100 < al - (5 / 4 - cN) - bn

/-- Claim 023, all parts. -/
def statement : Prop :=
  Decomposition ∧ NodeLower ∧ NodeCap ∧ SignConditions ∧ SureActiveCert ∧ ComplementCert

end

end Standalone.M3PremiumNodeBounds

import Standalone.M3PremiumNodeBounds

/-!
# Claim 026: range-type caps cannot be sharp; mean-type caps

Statement only; the proof is `Novel/M3MeanTypeCapsProof.lean`. Claim 026 refiles refuted claims
024-025; this file formalizes claim 026.

M3 is claim 011's formalization. Claim 022 supplies `cR`, `phi` and `RootOpt`. Claim 023 supplies
the node objects: `nodeCE`, the node gain `gain`, the aggregate `agg`, nodes `IsNode`, node paths
`NodePath`, ETF gross returns `gE`, the tilted node mean `tiltMean` and the risk-adjusted excess
returns `rBuy` (`r⁺`) and `rSell` (`r⁻`). Wealth is in units of `W₀⁻`: dollar amounts (`h1`, `x1`,
`condW`) are divided by `W0`.

- *Node data* (`HasData`): cash `h`, marked ETF values `m`, ETF rates `κ⁺`, `κ⁻`, the utility
  coefficient `ρ`, and each ETF's return range `[gu j, gb j]` over the node paths, both ends
  attained. `Realizable` data are data some M3 node has. A *range-type cap* (`IsRangeCap`) is any
  function of the data that bounds the node gain at every M3 node with those data.
- `NoFavorable`: no adjustable wealth in any favorable direction (no favorable cash purchase, sale
  or switch from one ETF into another).
- `tanLin u` is the first-order gain `Σ_j [(1 + κ⁺_j) r⁺_j u_j⁺ + r⁻_j u_j⁻]` of an ETF-only node
  trade `u` (dollars); `tanBound` is the claim's explicit bound on its maximum (normalized).
- `pmass` is the node-path mass `π₁(θ|y) q_s`; `varQ` the variance under it. `ZBuy` and `ZSell` are
  the per-dollar excesses of buying and selling. `curvBound ρ r v H` is claim 023's function
  `q(r, v)`: `r²/(2ρv)` if `r ≤ ρ v H`, else `r H - ρ v H²/2`.
- `tanOne` is the one-ETF `T_y = max(r⁺ h, r⁻ m, 0)`, normalized by `W₀⁻`. `meanCap` is the
  one-ETF mean-type node cap `min(T_y, curvature cap)` for supplied wealth ranges `dW` and return
  brackets `[gl, gu]` per node; `betaMean = agg meanCap`.

Part 5 (the numerical comparison on experiment 015's instances) has no formal counterpart.
-/

namespace Standalone.M3MeanTypeCaps

open Matrix Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
open Standalone.M3EtfChannelSandwich (cR phi RootOpt)
open Standalone.M3PremiumNodeBounds (nodeCE gain agg IsNode NodePath gE tiltMean rBuy rSell)

noncomputable section

variable {n K : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-! ### Part 1: range-type caps -/

/-- Node `y` after root `u₀` has cash `h`, marked ETF values `m` (units of `W₀⁻`), ETF rates `kp`,
`km`, utility coefficient `ρ`, and ETF `j`'s node-path returns ranging over `[gu j, gb j]` with
both ends attained. -/
def HasData (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (h : ℝ) (m kp km : Fin n → ℝ)
    (ρ : ℝ) (gb gu : Fin n → ℝ) : Prop :=
  M3Setting P ∧ Feas1 P .F P.D.x0 P.D.h0 u₀ ∧ IsNode P y ∧
  h1 P u₀ / W0 P.D = h ∧ (∀ j, x1 P y u₀ (Sum.inr j) / W0 P.D = m j) ∧
  (∀ j, P.D.kplus (Sum.inr j) = kp j ∧ P.D.kminus (Sum.inr j) = km j) ∧ P.rho = ρ ∧
  ∀ j, (∀ t s, NodePath P y t s → gu j ≤ gE P j t s ∧ gE P j t s ≤ gb j) ∧
    (∃ t s, NodePath P y t s ∧ gE P j t s = gb j) ∧ (∃ t s, NodePath P y t s ∧ gE P j t s = gu j)

/-- Data realized at some M3 node with `n` ETFs. -/
def Realizable (n : ℕ) (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ) : Prop :=
  ∃ (K : ℕ) (S T : Type) (_ : Fintype S) (_ : Fintype T) (P : M3 n K S T) (u₀ : Inst 1 n → ℝ)
    (y : Obs n K), HasData P u₀ y h m kp km ρ gb gu

/-- A function of the node data. -/
abbrev CapFn (n : ℕ) :=
  ℝ → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ

/-- A range-type cap: it bounds the node gain at every M3 node with the given data. -/
def IsRangeCap (n : ℕ) (C : CapFn n) : Prop :=
  ∀ (K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T) (u₀ : Inst 1 n → ℝ)
    (y : Obs n K) (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ),
    HasData P u₀ y h m kp km ρ gb gu → gain P u₀ y ≤ C h m kp km ρ gb gu

/-- `up = max_j (gb_j - 1)⁺`. -/
def upOf (gb : Fin n → ℝ) : ℝ := ⨆ j, max (gb j - 1) 0

/-- `down = max_j (1 - gu_j)⁺`. -/
def downOf (gu : Fin n → ℝ) : ℝ := ⨆ j, max (1 - gu j) 0

/-- Claim 023's node cap `h up + Σ_j m_j (up + down)` as a function of the data. -/
def cap023 : CapFn n := fun h m _ _ _ gb gu => h * upOf gb + (∑ j, m j) * (upOf gb + downOf gu)

/-- Part 1: for realizable data, every ETF and every `ε > 0` there is an M3 node with the same data
whose gain is within `ε` of `h [gb_j/(1+κ⁺_j) - 1]⁺`, and one within `ε` of
`m_j [1 - κ⁻_j - gu_j]⁺`. So every range-type cap is at least both values, and claim 023's node cap
is a range-type cap. Realizable data satisfy `h + Σ_k m_k/d_k ≤ 1`, with `d_k` the observed
first-quarter gross return, itself a node-path return. Red's example: with one ETF, no cash and
every node-path return at least one, the gain is zero, while claim 023's cap is `m (gb - 1)`. -/
def RangeTypeCaps : Prop :=
  (∀ (n : ℕ) (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ),
    Realizable n h m kp km ρ gb gu → ∀ (j : Fin n) (ε : ℝ), 0 < ε →
      (∃ (K : ℕ) (S T : Type) (_ : Fintype S) (_ : Fintype T) (P : M3 n K S T)
        (u₀ : Inst 1 n → ℝ) (y : Obs n K), HasData P u₀ y h m kp km ρ gb gu ∧
          h * max (gb j / (1 + kp j) - 1) 0 - ε ≤ gain P u₀ y) ∧
      (∃ (K : ℕ) (S T : Type) (_ : Fintype S) (_ : Fintype T) (P : M3 n K S T)
        (u₀ : Inst 1 n → ℝ) (y : Obs n K), HasData P u₀ y h m kp km ρ gb gu ∧
          m j * max (1 - km j - gu j) 0 - ε ≤ gain P u₀ y)) ∧
  (∀ (n : ℕ) (C : CapFn n), IsRangeCap n C →
    ∀ (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ), Realizable n h m kp km ρ gb gu →
      ∀ j, h * max (gb j / (1 + kp j) - 1) 0 ≤ C h m kp km ρ gb gu ∧
        m j * max (1 - km j - gu j) 0 ≤ C h m kp km ρ gb gu) ∧
  (∀ n, IsRangeCap n cap023) ∧
  (∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T) (u₀ : Inst 1 n → ℝ)
    (y : Obs n K) (h : ℝ) (m kp km : Fin n → ℝ) (ρ : ℝ) (gb gu : Fin n → ℝ),
    HasData P u₀ y h m kp km ρ gb gu →
      ∃ t s, obs P t s = y ∧ NodePath P y t s ∧ h + ∑ k, m k / gE P k t s ≤ 1) ∧
  (∀ (K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 1 K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → ∀ y, IsNode P y → h1 P u₀ = 0 →
      (∀ t s, NodePath P y t s → 1 ≤ gE P 0 t s) → gain P u₀ y = 0) ∧
  ∀ (m kp km : Fin 1 → ℝ) (ρ : ℝ) (gb gu : Fin 1 → ℝ), 1 ≤ gu 0 → gu 0 ≤ gb 0 →
    cap023 0 m kp km ρ gb gu = m 0 * (gb 0 - 1)

/-! ### Part 2: the tangent cap -/

/-- The first-order gain `Σ_j [(1 + κ⁺_j) r⁺_j u_j⁺ + r⁻_j u_j⁻]` of a node trade (dollars). -/
def tanLin (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (u : Inst 1 n → ℝ) : ℝ :=
  ∑ j, ((1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j * max (u (Sum.inr j)) 0
    + rSell P u₀ y j * max (-u (Sum.inr j)) 0)

/-- `[(h + Σ_j m_j) max_j ((1 + κ⁺_j) r⁺_j)⁺ + Σ_j m_j (r⁻_j)⁺] / W₀⁻`. -/
def tanBound (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : ℝ :=
  ((h1 P u₀ + ∑ j, x1 P y u₀ (Sum.inr j)) *
      (⨆ j, max ((1 + P.D.kplus (Sum.inr j)) * rBuy P u₀ y j) 0)
    + ∑ j, x1 P y u₀ (Sum.inr j) * max (rSell P u₀ y j) 0) / W0 P.D

/-- No adjustable wealth in any favorable direction: for every ETF `j`, `h = 0` or `r⁺_j ≤ 0`;
for every ETF `k`, `m_k = 0` or `r⁻_k ≤ 0`; and for every `k` with `m_k > 0` and every `j`,
`r⁻_k + (1 - κ⁻_k) r⁺_j ≤ 0` (selling `k` to buy `j`). -/
def NoFavorable (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) : Prop :=
  (∀ j, h1 P u₀ = 0 ∨ rBuy P u₀ y j ≤ 0) ∧ (∀ k, x1 P y u₀ (Sum.inr k) = 0 ∨ rSell P u₀ y k ≤ 0) ∧
  ∀ k, 0 < x1 P y u₀ (Sum.inr k) → ∀ j,
    rSell P u₀ y k + (1 - P.D.kminus (Sum.inr k)) * rBuy P u₀ y j ≤ 0

/-- Part 2: the node gain is at most the first-order gain of some feasible ETF-only trade (so at
most `T_y`, the largest first-order gain); every first-order gain is at most `tanBound`; `T_y = 0`
(every feasible first-order gain nonpositive) exactly when the node has no adjustable wealth in any
favorable direction, and then the gain is zero; a node with no favorable direction at all has zero
gain; `tanBound` is at most claim 023's cap for every bracket; and with one ETF
`T_y = max(r⁺ h, r⁻ m, 0)`, attained, and the first two conditions suffice. -/
def TangentCap : Prop :=
  (∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → ∀ y, IsNode P y →
      (∃ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u ∧ gain P u₀ y ≤ tanLin P u₀ y u / W0 P.D) ∧
      (∀ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u → tanLin P u₀ y u / W0 P.D ≤ tanBound P u₀ y) ∧
      gain P u₀ y ≤ tanBound P u₀ y ∧
      (NoFavorable P u₀ y ↔
        ∀ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u → tanLin P u₀ y u ≤ 0) ∧
      (NoFavorable P u₀ y → gain P u₀ y = 0) ∧
      ((∀ j, rBuy P u₀ y j ≤ 0 ∧ rSell P u₀ y j ≤ 0) → gain P u₀ y = 0) ∧
      ∀ U D : ℝ, 0 ≤ U → 0 ≤ D →
        (∀ j t s, NodePath P y t s → gE P j t s - 1 ≤ U ∧ 1 - gE P j t s ≤ D) →
        tanBound P u₀ y ≤ (h1 P u₀ * U + (∑ j, x1 P y u₀ (Sum.inr j)) * (U + D)) / W0 P.D) ∧
  ∀ (K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 1 K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → ∀ y, IsNode P y →
      (∀ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u → tanLin P u₀ y u
        ≤ max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0) ∧
      (∃ u, Feas1 P .E (x1 P y u₀) (h1 P u₀) u ∧ tanLin P u₀ y u
        = max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0) ∧
      gain P u₀ y
        ≤ max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0 / W0 P.D ∧
      (NoFavorable P u₀ y ↔ (h1 P u₀ = 0 ∨ rBuy P u₀ y 0 ≤ 0) ∧
        (x1 P y u₀ (Sum.inr 0) = 0 ∨ rSell P u₀ y 0 ≤ 0))

/-! ### Part 3: the curvature cap (one ETF) -/

/-- Node-path mass `π₁(θ | y) q_s`. -/
def pmass (P : M3 n K S T) (y : Obs n K) (t : T) (s : S) : ℝ := post P y t * P.D.q s

/-- Variance of `Z` under the node-path masses. -/
def varQ (P : M3 n K S T) (y : Obs n K) (Z : T → S → ℝ) : ℝ :=
  ∑ t, ∑ s, pmass P y t s * Z t s ^ 2 - (∑ t, ∑ s, pmass P y t s * Z t s) ^ 2

/-- Per-dollar excess of buying ETF `j`: `(g - 1 - κ⁺)/(1 + κ⁺)`. -/
def ZBuy (P : M3 n K S T) (j : Fin n) (t : T) (s : S) : ℝ :=
  (gE P j t s - 1 - P.D.kplus (Sum.inr j)) / (1 + P.D.kplus (Sum.inr j))

/-- Per-dollar excess of selling ETF `j`: `1 - κ⁻ - g`. -/
def ZSell (P : M3 n K S T) (j : Fin n) (t : T) (s : S) : ℝ :=
  1 - P.D.kminus (Sum.inr j) - gE P j t s

/-- Claim 023's `q(r, v)` on `[0, H]`, read as `0` for `r ≤ 0`. -/
def curvBound (ρ r v H : ℝ) : ℝ :=
  if r ≤ 0 then 0 else if r ≤ ρ * v * H then r ^ 2 / (2 * ρ * v) else r * H - ρ * v * H ^ 2 / 2

/-- Normalized no-trade node wealth `W^N_y`. -/
def WN (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (t : T) (s : S) : ℝ :=
  condW P (x1 P y u₀) (h1 P u₀) 0 t s / W0 P.D

/-- Certainty equivalent at the node after trade `u`. -/
def tradeCE (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (u : Inst 1 n → ℝ) : ℝ :=
  -(1 / P.rho) * Real.log (-condObj P (post P y) (x1 P y u₀) (h1 P u₀) u)

/-- The one-ETF curvature cap with wealth range `dW` and return bracket `[gl, gu]`: the larger of
the buying bound `q(r⁺, v⁺_min)` on `[0, h]` and the selling bound `q(r⁻, v⁻_min)` on `[0, m]`. -/
def curvCap (P : M3 1 K S T) (u₀ : Inst 1 1 → ℝ) (y : Obs 1 K) (dW gl gu : ℝ) : ℝ :=
  max (curvBound P.rho (rBuy P u₀ y 0)
      (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (h1 P u₀ / W0 P.D))) * varQ P y (ZBuy P 0))
      (h1 P u₀ / W0 P.D))
    (curvBound P.rho (rSell P u₀ y 0)
      (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (x1 P y u₀ (Sum.inr 0) / W0 P.D)))
        * varQ P y (ZSell P 0))
      (x1 P y u₀ (Sum.inr 0) / W0 P.D))

/-- `dW` bounds the no-trade node wealth's range and `[gl, gu]` brackets the ETF's return on the
node paths of `y`. -/
def ValidAt (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (y : Obs n K) (j : Fin n) (dW gl gu : ℝ) :
    Prop :=
  (∀ t s t' s', NodePath P y t s → NodePath P y t' s' → WN P u₀ y t s - WN P u₀ y t' s' ≤ dW) ∧
  ∀ t s, NodePath P y t s → gl ≤ gE P j t s ∧ gE P j t s ≤ gu

/-- Part 3: for one ETF, buying `ε ≤ h` (units of `W₀⁻`) gains at most `q(r⁺, v⁺_min)` and selling
`ε ≤ m` at most `q(r⁻, v⁻_min)`, with `v_min = exp(-ρ(ΔW + 2 s ε_max)) Var_q(Z)`; hence the node
gain is at most the curvature cap. -/
def CurvatureCap : Prop :=
  ∀ (K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 1 K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → ∀ y, IsNode P y → ∀ dW gl gu : ℝ,
      ValidAt P u₀ y 0 dW gl gu →
      (∀ ε, 0 ≤ ε → ε ≤ h1 P u₀ / W0 P.D →
        tradeCE P u₀ y (Pi.single (Sum.inr 0) (ε * W0 P.D / (1 + P.D.kplus (Sum.inr 0))))
          - nodeCE P .N u₀ y
        ≤ curvBound P.rho (rBuy P u₀ y 0)
            (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (h1 P u₀ / W0 P.D)))
              * varQ P y (ZBuy P 0)) (h1 P u₀ / W0 P.D)) ∧
      (∀ ε, 0 ≤ ε → ε ≤ x1 P y u₀ (Sum.inr 0) / W0 P.D →
        tradeCE P u₀ y (Pi.single (Sum.inr 0) (-(ε * W0 P.D))) - nodeCE P .N u₀ y
        ≤ curvBound P.rho (rSell P u₀ y 0)
            (Real.exp (-P.rho * (dW + 2 * ((gu - gl) / 2) * (x1 P y u₀ (Sum.inr 0) / W0 P.D)))
              * varQ P y (ZSell P 0)) (x1 P y u₀ (Sum.inr 0) / W0 P.D)) ∧
      gain P u₀ y ≤ curvCap P u₀ y dW gl gu

/-! ### Part 4: aggregation and sign conditions -/

/-- The one-ETF `T_y = max(r⁺ h, r⁻ m, 0)`, normalized by `W₀⁻`. -/
def tanOne (P : M3 1 K S T) (u₀ : Inst 1 1 → ℝ) (y : Obs 1 K) : ℝ :=
  max (max (rBuy P u₀ y 0 * h1 P u₀) (rSell P u₀ y 0 * x1 P y u₀ (Sum.inr 0))) 0 / W0 P.D

/-- The one-ETF mean-type node cap `min(T_y, curvature cap)`. -/
def meanCap (P : M3 1 K S T) (u₀ : Inst 1 1 → ℝ) (dW gl gu : Obs 1 K → ℝ) (y : Obs 1 K) : ℝ :=
  min (tanOne P u₀ y) (curvCap P u₀ y (dW y) (gl y) (gu y))

/-- `β_mean(u₀)`. -/
def betaMean (P : M3 1 K S T) (u₀ : Inst 1 1 → ℝ) (dW gl gu : Obs 1 K → ℝ) : ℝ :=
  agg P u₀ (meanCap P u₀ dW gl gu)

/-- Claim 023's node cap with node-wise brackets `U`, `D`. -/
def capNode (P : M3 n K S T) (u₀ : Inst 1 n → ℝ) (U D : Obs n K → ℝ) (y : Obs n K) : ℝ :=
  (h1 P u₀ * U y + (∑ j, x1 P y u₀ (Sum.inr j)) * (U y + D y)) / W0 P.D

/-- Brackets `U`, `D` are valid at every node. -/
def ValidUD (P : M3 n K S T) (U D : Obs n K → ℝ) : Prop :=
  ∀ y, IsNode P y → 0 ≤ U y ∧ 0 ≤ D y ∧
    ∀ j t s, NodePath P y t s → gE P j t s - 1 ≤ U y ∧ 1 - gE P j t s ≤ D y

/-- Part 4: `φ ≤ agg T ≤ β_node` for any number of ETFs; for one ETF `φ ≤ β_mean ≤ β_node`, and
claim 023's sufficient sign conditions hold with `β_mean` in place of `β_node`. -/
def Aggregation : Prop :=
  (∀ (n K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 n K S T), M3Setting P →
    ∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ →
      phi P u₀ ≤ agg P u₀ (tanBound P u₀) ∧
      ∀ U D, ValidUD P U D → agg P u₀ (tanBound P u₀) ≤ agg P u₀ (capNode P u₀ U D)) ∧
  ∀ (K : ℕ) (S T : Type) [Fintype S] [Fintype T] (P : M3 1 K S T), M3Setting P →
    (∀ u₀, Feas1 P .F P.D.x0 P.D.h0 u₀ → ∀ dW gl gu : Obs 1 K → ℝ,
      (∀ y, IsNode P y → ValidAt P u₀ y 0 (dW y) (gl y) (gu y)) →
      phi P u₀ ≤ betaMean P u₀ dW gl gu ∧
      ∀ U D, ValidUD P U D → betaMean P u₀ dW gl gu ≤ agg P u₀ (capNode P u₀ U D)) ∧
    (∀ AE BN, RootOpt P .F .E AE → RootOpt P .E .N BN → ∀ dW gl gu : Obs 1 K → ℝ,
      (∀ y, IsNode P y → ValidAt P AE y 0 (dW y) (gl y) (gu y)) →
      ∀ ℓ : Obs 1 K → ℝ, (∀ y, IsNode P y → ℓ y ≤ gain P BN y) →
      betaMean P AE dW gl gu < agg P BN ℓ → Delta P .E - Delta P .N < 0) ∧
    ∀ AN BE, RootOpt P .F .N AN → RootOpt P .E .E BE → ∀ dW gl gu : Obs 1 K → ℝ,
      (∀ y, IsNode P y → ValidAt P BE y 0 (dW y) (gl y) (gu y)) →
      ∀ ℓ : Obs 1 K → ℝ, (∀ y, IsNode P y → ℓ y ≤ gain P AN y) →
      betaMean P BE dW gl gu < agg P AN ℓ → 0 < Delta P .E - Delta P .N

/-- Claim 026, parts 1-4. -/
def statement : Prop := RangeTypeCaps ∧ TangentCap ∧ CurvatureCap ∧ Aggregation

end

end Standalone.M3MeanTypeCaps

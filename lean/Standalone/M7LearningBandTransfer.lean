import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Standalone.M6QuarterlyBandStaticCeiling

/-!
# Claim 100: claim 029's quarterly band on M5's learning path (M7)

Statement only; the proof is `Novel/M7LearningBandTransferProof.lean`.

**The filter** (`Filt`). This is M5's fixed-means filter (Φ = I, Q = 0). It has a prior covariance
`P0`, a prior mean `m0`, an observation matrix `H`, a drift `d`, a noise covariance `R`, loadings
`G`, a return covariance `Sr` (`Σ_r`), a drag `cE` and a risk aversion `gamma`. It runs:
- `P (t+1) = P t - P t H'(H P t H' + R)⁻¹ H P t` and `gain t = P t H'(H P t H' + R)⁻¹`;
- `m_{t+1} = m_t + gain t (y_{t+1} - H m_t - d)`, where `mean z` is the mean after the history `z`,
  a list of observations, oldest first;
- `Sig t = G P t G' + Sr`, `mu z = G m - cE` and `xstar t z = (γ Sig t)⁻¹ mu z`.

`Good` collects the setting's hypotheses: `P0` and `R` positive definite, `H` of full column rank,
`Σ_r` positive definite, and `γ > 0`. `R = L Σ_z L'` and the laws' first two moments enter only
the paper-level unconditional moments of 2b, so they are not hypotheses here.

**M7's finite-law variant** (`M7`). The unknown mean `θ` takes the values `th a` with masses `pth a`,
and a quarter's shock takes the values `sh s` with masses `psh s`. The observation is
`obs a s = H θ_a + d + L z_s`, and the gross return is a positive function `gross` of it. The
horizon-`T` instance `inst T` is an M6 instance (claim 029's `M6`, generalized to a covariance
`Σ(t, z)`) whose states are observation histories:
- outcomes `(s, a, w)` are a date `s ≤ T`, a value of `θ`, and the `T` shocks;
- `next` is the history up to `s`;
- `prob t z` is the finite prior's conditional law of `(a, w)` given the history `z` at `t`,
  placed on date `t + 1`. Where the history has mass zero, or `t ≥ T`, it is the joint law placed
  on date `0`; these transitions are never used from reachable states before the horizon.

The formal objects are more general than the claim's. The masses need only be a probability law;
the prior's mean and covariance and the shocks' centring are not used outside 2b's unconditional
moments, which are paper-level.

**Formal scope.** 1a is `Instance`, 1b-1d are claim 029's `statement` (now for `Σ(t, z)`) together
with `Decouple`, 2a is `Learning`, 2b is `Drift`, 2c is `TiltSign`, and 2d is `Landing` and
`Eventual`. Paper-level: 2b's unconditional innovation moments over the finite joint law
(`E ε_{t+1} = 0`, `Cov ε_{t+1} = V_t`). Not formalized: the Consequence for D13, a reading.
-/

namespace Standalone.M7LearningBandTransfer

open Matrix Filter Topology Standalone.M6QuarterlyBandStaticCeiling

noncomputable section

/-! ### The filter -/

/-- M5's fixed-means filter and predictive moments. -/
structure Filt (κ ο ι : Type) where
  P0 : Matrix κ κ ℝ
  m0 : κ → ℝ
  H : Matrix ο κ ℝ
  d : ο → ℝ
  R : Matrix ο ο ℝ
  G : Matrix ι κ ℝ
  Sr : Matrix ι ι ℝ
  cE : ι → ℝ
  gamma : ℝ

namespace Filt

variable {κ ο ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ι]
  [DecidableEq ι] (F : Filt κ ο ι)

/-- The setting's hypotheses on the filter. -/
def Good : Prop :=
  F.P0.PosDef ∧ F.R.PosDef ∧ (∀ v, F.H *ᵥ v = 0 → v = 0) ∧ F.Sr.PosDef ∧ 0 < F.gamma

/-- The error covariance: `P_{t+1} = P_t - P_t H'(H P_t H' + R)⁻¹ H P_t`. -/
def P : ℕ → Matrix κ κ ℝ
  | 0 => F.P0
  | t + 1 => P t - P t * F.Hᵀ * (F.H * P t * F.Hᵀ + F.R)⁻¹ * F.H * P t

/-- The gain `K_t = P_t H'(H P_t H' + R)⁻¹`. -/
def gain (t : ℕ) : Matrix κ ο ℝ := F.P t * F.Hᵀ * (F.H * F.P t * F.Hᵀ + F.R)⁻¹

/-- `J = H' R⁻¹ H`, the information one observation adds. -/
def J : Matrix κ κ ℝ := F.Hᵀ * F.R⁻¹ * F.H

/-- `V_t = P_t - P_{t+1}`. -/
def V (t : ℕ) : Matrix κ κ ℝ := F.P t - F.P (t + 1)

/-- One filter step at date `t`. -/
def step (t : ℕ) (m : κ → ℝ) (y : ο → ℝ) : κ → ℝ := m + F.gain t *ᵥ (y - F.H *ᵥ m - F.d)

/-- The mean after the observations `ys`, starting at date `t` from `m`. -/
def meanFrom : ℕ → (κ → ℝ) → List (ο → ℝ) → κ → ℝ
  | _, m, [] => m
  | t, m, y :: ys => meanFrom (t + 1) (F.step t m y) ys

/-- `m_t` after the history `z = [y_1, ..., y_t]`. -/
def mean (z : List (ο → ℝ)) : κ → ℝ := F.meanFrom 0 F.m0 z

/-- `Σ_t = G P_t G' + Σ_r`. -/
def Sig (t : ℕ) : Matrix ι ι ℝ := F.G * F.P t * F.Gᵀ + F.Sr

/-- `μ_t = G m_t - (0, c^E)`. -/
def mu (z : List (ο → ℝ)) : ι → ℝ := F.G *ᵥ F.mean z - F.cE

/-- `x*_t = (γ Σ_t)⁻¹ μ_t`, written as M6's `xstar`. -/
def xstar (t : ℕ) (z : List (ο → ℝ)) : ι → ℝ := (1 / F.gamma) • ((F.Sig t)⁻¹ *ᵥ F.mu z)

end Filt

/-! ### M7's finite-law variant as an M6 instance -/

/-- M7's finite-law variant with `n` instruments. -/
structure M7 (κ ο ζ Θ S : Type) (n : ℕ) where
  F : Filt κ ο (Fin n)
  L : Matrix ο ζ ℝ
  th : Θ → κ → ℝ
  pth : Θ → ℝ
  sh : S → ζ → ℝ
  psh : S → ℝ
  beta : ℝ
  kp : Fin n → ℝ
  km : Fin n → ℝ
  cap : Fin n → ℝ
  gross : (ο → ℝ) → Fin n → ℝ

namespace M7

variable {κ ο ζ Θ S : Type} [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ζ]
  [Fintype Θ] [Fintype S] [DecidableEq S] {n : ℕ} (M : M7 κ ο ζ Θ S n)

/-- The setting's hypotheses: a good filter, M6's rates, caps and discount, finite probability
laws, and positive gross returns. -/
def Setting : Prop :=
  M.F.Good ∧ 0 < M.beta ∧ M.beta ≤ 1 ∧
  (∀ i, 0 ≤ M.kp i ∧ M.kp i < 1 ∧ 0 ≤ M.km i ∧ M.km i < 1) ∧ (∀ i, 0 < M.cap i) ∧
  (∀ a, 0 ≤ M.pth a) ∧ ∑ a, M.pth a = 1 ∧ (∀ s, 0 ≤ M.psh s) ∧ ∑ s, M.psh s = 1 ∧
  ∀ y i, 0 < M.gross y i

/-- The observation `y = H θ_a + d + L z_s`. -/
def obs (a : Θ) (s : S) : ο → ℝ := M.F.H *ᵥ M.th a + M.F.d + M.L *ᵥ M.sh s

/-- The outcomes of the horizon-`T` instance: a date `s ≤ T`, a value of `θ`, and the shocks. -/
abbrev Out (Θ S : Type) (T : ℕ) := Fin (T + 1) × Θ × (Fin T → S)

/-- The observation history of `(a, w)` up to date `min t T`, oldest first. -/
def hist {T : ℕ} (a : Θ) (w : Fin T → S) : ℕ → List (ο → ℝ)
  | 0 => []
  | t + 1 => if h : t < T then hist a w t ++ [M.obs a (w ⟨t, h⟩)] else hist a w t

/-- The joint mass of `(a, w)`. -/
def joint {T : ℕ} (a : Θ) (w : Fin T → S) : ℝ := M.pth a * ∏ j, M.psh (w j)

open Classical in
/-- The mass of the history `z` at date `t`. -/
def marg (T t : ℕ) (z : List (ο → ℝ)) : ℝ :=
  ∑ a, ∑ w : Fin T → S, if M.hist a w t = z then M.joint a w else 0

open Classical in
/-- The horizon-`T` M6 instance. -/
def inst (T : ℕ) : M6 n (List (ο → ℝ)) (Out Θ S T) where
  T := T
  mu := fun _ z => M.F.mu z
  Sigma := fun t _ => M.F.Sig t
  gamma := M.F.gamma
  beta := M.beta
  kp := M.kp
  km := M.km
  cap := M.cap
  prob := fun t z ω =>
    if t + 1 ≤ T ∧ 0 < M.marg T t z then
      (if (ω.1 : ℕ) = t + 1 ∧ M.hist ω.2.1 ω.2.2 t = z then M.joint ω.2.1 ω.2.2 / M.marg T t z else 0)
    else (if (ω.1 : ℕ) = 0 then M.joint ω.2.1 ω.2.2 else 0)
  next := fun ω => M.hist ω.2.1 ω.2.2 ω.1
  gross := fun ω =>
    if h : 0 < (ω.1 : ℕ) then M.gross (M.obs ω.2.1 (ω.2.2 ⟨(ω.1 : ℕ) - 1, by have := ω.1.2; omega⟩)) else fun _ => 1

end M7

/-! ### Part 1 -/

/-- 1a: M7's finite-law variant is an M6 instance with `Σ(t, z) = Σ_t` and `μ(t, z) = μ_t`. From a
history of positive mass, every positive-mass outcome appends one observation `obs a s` to it and
carries that observation's gross return. -/
def Instance : Prop :=
  ∀ (κ ο ζ Θ S : Type) [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ζ]
    [Fintype Θ] [Fintype S] [DecidableEq S] (n : ℕ) (M : M7 κ ο ζ Θ S n), M.Setting → ∀ T, 1 ≤ T →
    Setting (M.inst T) ∧ (∀ t z, (M.inst T).Sigma t z = M.F.Sig t) ∧
    (∀ t z, (M.inst T).mu t z = M.F.mu z) ∧
    ∀ t z, t + 1 ≤ T → 0 < M.marg T t z → ∀ ω, 0 < (M.inst T).prob t z ω →
      ∃ a s, (M.inst T).next ω = z ++ [M.obs a s] ∧ (M.inst T).gross ω = M.gross (M.obs a s)

/-- The one-instrument problem of instrument `i`. -/
def oneInst {n : ℕ} {Z Ω : Type} (P : M6 n Z Ω) (i : Fin n) : M6 1 Z Ω where
  T := P.T
  mu := fun t z _ => P.mu t z i
  Sigma := fun t z _ _ => P.Sigma t z i i
  gamma := P.gamma
  beta := P.beta
  kp := fun _ => P.kp i
  km := fun _ => P.km i
  cap := fun _ => P.cap i
  prob := P.prob
  next := P.next
  gross := fun ω _ => P.gross ω i

/-- 1b, many instruments: with `Σ(t, z)` diagonal, each instrument's problem is an M6 instance with
`c_{t,i} = γ Σ_{t,ii}`, the value is the sum of the one-instrument values, and a post-trade holding is
optimal iff each coordinate is optimal for its instrument. -/
def Decouple : Prop :=
  ∀ (n : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 n Z Ω), Setting P →
    (∀ t z i j, i ≠ j → P.Sigma t z i j = 0) →
    (∀ i, Setting (oneInst P i)) ∧
    ∀ t z (x : Fin n → ℝ), V P t z x = ∑ i, V1 (oneInst P i) t z (x i) ∧
      ∀ x', IsOpt P t z x x' ↔ ∀ i, IsOpt (oneInst P i) t z (fun _ => x i) (fun _ => x' i)

/-! ### Part 2 -/

/-- 2a: the information form, `P_{t+1} ≤ P_t`, `P_t → 0`, `Σ_{t+1} ≤ Σ_t` (so every diagonal entry
and every quadratic form, 1d's included, is nonincreasing), `Σ_t → Σ_r`, and for each instrument
`c_{t,i} = γ Σ_{t,ii}` nonincreasing with limit `γ Σ_{r,ii}`, so the static width `k/c_{t,i}` is
nondecreasing with limit `k/(γ Σ_{r,ii})`. -/
def Learning : Prop :=
  ∀ (κ ο ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ι]
    [DecidableEq ι] (F : Filt κ ο ι), F.Good →
    (∀ t, (F.P t).PosDef ∧ (F.P t)⁻¹ = F.P0⁻¹ + (t : ℝ) • F.J) ∧
    (∀ t, (F.P t - F.P (t + 1)).PosSemidef) ∧ Tendsto F.P atTop (𝓝 0) ∧
    (∀ t, (F.Sig t - F.Sig (t + 1)).PosSemidef) ∧ Tendsto F.Sig atTop (𝓝 F.Sr) ∧
    ∀ i, Antitone (fun t => F.gamma * F.Sig t i i) ∧
      Tendsto (fun t => F.gamma * F.Sig t i i) atTop (𝓝 (F.gamma * F.Sr i i)) ∧
      ∀ k : ℝ, 0 ≤ k → Monotone (fun t => k / (F.gamma * F.Sig t i i)) ∧
        Tendsto (fun t => k / (F.gamma * F.Sig t i i)) atTop (𝓝 (k / (F.gamma * F.Sr i i)))

/-- 2b, pathwise: one observation moves the mean by `ε = K_t(y - H m_t - d)`, and the target
decomposes as `(γΣ_{t+1})⁻¹ G ε + δ_t` with `δ_t = [(γΣ_{t+1})⁻¹ - (γΣ_t)⁻¹] μ_t`. The bracket is
positive semidefinite, and `V_t = K_t(H P_t H' + R)K_t'` is positive definite. `Σ_{t,ii}` falls
strictly iff the row `G_i` is nonzero, and both `V_t` and the bracket are of order `1/t²`
(`t(t+1)V_t → J⁻¹`, `t(t+1)[Σ_{t+1}⁻¹ - Σ_t⁻¹] → Σ_r⁻¹ G J⁻¹ G' Σ_r⁻¹`). For one instrument,
`δ_t = μ_t (1/Σ_{t+1} - 1/Σ_t)/γ` has the sign of `μ_t` when `G_0 ≠ 0`, and is zero, with an unmoved
risk charge, when `G_0 = 0`. -/
def Drift : Prop :=
  ∀ (κ ο ι : Type) [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ι]
    [DecidableEq ι] (F : Filt κ ο ι), F.Good →
    (∀ (z : List (ο → ℝ)) (y : ο → ℝ),
      F.mean (z ++ [y]) = F.step z.length (F.mean z) y ∧
      F.xstar (z.length + 1) (z ++ [y]) - F.xstar z.length z =
        (1 / F.gamma) • ((F.Sig (z.length + 1))⁻¹ *ᵥ (F.G *ᵥ (F.mean (z ++ [y]) - F.mean z))) +
        (1 / F.gamma) • (((F.Sig (z.length + 1))⁻¹ - (F.Sig z.length)⁻¹) *ᵥ F.mu z)) ∧
    (∀ t, ((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹).PosSemidef) ∧
    (∀ t, F.V t = F.gain t * (F.H * F.P t * F.Hᵀ + F.R) * (F.gain t)ᵀ ∧ (F.V t).PosDef) ∧
    (∀ t i, F.Sig (t + 1) i i < F.Sig t i i ↔ F.G i ≠ 0) ∧
    Tendsto (fun t : ℕ => ((t : ℝ) * (t + 1)) • F.V t) atTop (𝓝 F.J⁻¹) ∧
    Tendsto (fun t : ℕ => ((t : ℝ) * (t + 1)) • ((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹)) atTop
      (𝓝 (F.Sr⁻¹ * F.G * F.J⁻¹ * F.Gᵀ * F.Sr⁻¹))

/-- 2b for one instrument: the drift's scalar form and its sign. -/
def DriftOne : Prop :=
  ∀ (κ ο : Type) [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] (F : Filt κ ο (Fin 1)),
    F.Good → ∀ (z : List (ο → ℝ)),
    let t := z.length
    let δ := (1 / F.gamma) * ((1 / F.Sig (t + 1) 0 0 - 1 / F.Sig t 0 0) * F.mu z 0)
    (((F.Sig (t + 1))⁻¹ - (F.Sig t)⁻¹) *ᵥ F.mu z) 0 / F.gamma = δ ∧
    (F.G 0 ≠ 0 → F.Sig (t + 1) 0 0 < F.Sig t 0 0 ∧ (0 < δ ↔ 0 < F.mu z 0) ∧ (δ < 0 ↔ F.mu z 0 < 0)) ∧
    (F.G 0 = 0 → F.Sig (t + 1) 0 0 = F.Sig t 0 0 ∧ δ = 0)

/-- 2c: in the coarse regime without marking and with interior edges, an (up) outcome is exactly a
rise of the target and a (down) outcome a fall. If the target's move is `η + δ` on positive-mass
outcomes, the law of `η` is symmetric about zero, and `κ⁺ = κ⁻ = κ`, then
`τ = sign(δ) β κ P(|η| ≤ |δ|)/c_t`. So `τ` is zero or has the sign of `δ`, and for `κ > 0` it is zero
exactly when no positive-mass `η` lies in `(-|δ|, |δ|]`. -/
def TiltSign : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → ∀ t z, t + 1 < P.T →
    (∀ ω, P.gross ω 0 = 1) → 0 < lo P t z → hi P t z < P.cap 0 →
    (∀ ω, 0 < P.prob t z ω → Up P t z ω ∨ Down P t z ω) →
    (∀ ω, 0 < P.prob t z ω →
      (Up P t z ω ↔ xs P t z < xs P (t + 1) (P.next ω)) ∧
      (Down P t z ω ↔ xs P (t + 1) (P.next ω) < xs P t z)) ∧
    ∀ (η : Ω → ℝ) (δ : ℝ),
      (∀ ω, 0 < P.prob t z ω → xs P (t + 1) (P.next ω) - xs P t z = η ω + δ) →
      (∀ f : ℝ → ℝ, ∑ ω, P.prob t z ω * f (η ω) = ∑ ω, P.prob t z ω * f (-η ω)) →
      P.kp 0 = P.km 0 →
      tilt P t z = (SignType.sign δ : ℝ) *
        (P.beta * P.kp 0 * (∑ ω, if |η ω| ≤ |δ| then P.prob t z ω else 0)) / curv P t z ∧
      (0 < P.kp 0 →
        (tilt P t z = 0 ↔ ∀ ω, 0 < P.prob t z ω → ¬ (-|δ| < η ω ∧ η ω ≤ |δ|)))

/-- The closed up-landing mass `U = P(hi_t ≤ lo_{t+1})`. -/
def Uland {Z Ω : Type} [Fintype Ω] (P : M6 1 Z Ω) (t : ℕ) (z : Z) : ℝ :=
  ∑ ω, if hi P t z ≤ lo P (t + 1) (P.next ω) then P.prob t z ω else 0

/-- The closed down-landing mass `D = P(hi_{t+1} ≤ lo_t)`. -/
def Dland {Z Ω : Type} [Fintype Ω] (P : M6 1 Z Ω) (t : ℕ) (z : Z) : ℝ :=
  ∑ ω, if hi P (t + 1) (P.next ω) ≤ lo P t z then P.prob t z ω else 0

/-- 2d: without marking, if the band at `t ≤ T - 2` has the static width, every positive-mass
outcome is an up or a down landing, `U + D = 1`, every outcome moves the target, and the moves are
at least `[κ⁻(1-β) + β(κ⁺+κ⁻)U]/c_t` up and `[κ⁺(1-β) + β(κ⁺+κ⁻)D]/c_t` down. -/
def Landing : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → 0 < P.kp 0 + P.km 0 → ∀ t z, t + 1 < P.T →
    (∀ ω, P.gross ω 0 = 1) → hi P t z - lo P t z = (P.kp 0 + P.km 0) / curv P t z →
    (∀ ω, 0 < P.prob t z ω →
      hi P t z ≤ lo P (t + 1) (P.next ω) ∨ hi P (t + 1) (P.next ω) ≤ lo P t z) ∧
    Uland P t z + Dland P t z = 1 ∧
    (∀ ω, 0 < P.prob t z ω → xs P (t + 1) (P.next ω) ≠ xs P t z) ∧
    (∀ ω, 0 < P.prob t z ω → hi P t z ≤ lo P (t + 1) (P.next ω) →
      (P.km 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * Uland P t z) / curv P t z ≤
        xs P (t + 1) (P.next ω) - xs P t z) ∧
    ∀ ω, 0 < P.prob t z ω → hi P (t + 1) (P.next ω) ≤ lo P t z →
      (P.kp 0 * (1 - P.beta) + P.beta * (P.kp 0 + P.km 0) * Dland P t z) / curv P t z ≤
        xs P t z - xs P (t + 1) (P.next ω)

/-- 2d, eventual strict narrowing: for one instrument with pure-learning marking, there is a
review `t₀`, chosen before the horizon, such that for every horizon `T`, every `t` with
`t₀ ≤ t ≤ T - 2` and every history of positive mass, the band is strictly narrower than the static
width. -/
def Eventual : Prop :=
  ∀ (κ ο ζ Θ S : Type) [Fintype κ] [DecidableEq κ] [Fintype ο] [DecidableEq ο] [Fintype ζ]
    [Fintype Θ] [Fintype S] [DecidableEq S] (M : M7 κ ο ζ Θ S 1), M.Setting →
    (∀ y, M.gross y 0 = 1) → 0 < M.kp 0 + M.km 0 →
    ∃ t₀ : ℕ, ∀ T t (z : List (ο → ℝ)), t₀ ≤ t → t + 1 < T → 0 < M.marg T t z →
      hi (M.inst T) t z - lo (M.inst T) t z < (M.kp 0 + M.km 0) / curv (M.inst T) t z

/-- Claim 100: part 1 (1a, claim 029's results for `Σ(t, z)`, and the decoupling) and part 2. -/
def statement : Prop :=
  Instance ∧ Standalone.M6QuarterlyBandStaticCeiling.statement ∧ Decouple ∧ Learning ∧ Drift ∧
    DriftOne ∧ TiltSign ∧ Landing ∧ Eventual

end

end Standalone.M7LearningBandTransfer

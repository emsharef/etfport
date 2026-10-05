import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Claim 029: quarterly no-trade bands around a moving target

Statement only; the proof is `Novel/M6QuarterlyBandStaticCeilingProof.lean`.

M6 (`model/SPEC.md`) is formalized here as the claim uses it, for a slack-budget instance: the cash
constraint never binds, so cash does not appear. The covariance may depend on the review and the
state, `Sigma t z`. M6 as written fixes it, which is the constant case. Claim 100 (M7, the learning
path) uses the general case, whose proofs are claim 029's read at a fixed `(t, z)`.
- `n` instruments, a finite public state set `Z`, and the next-state/gross-return law given by a
  finite outcome set `Ω`. Outcome `ω` has next state `next ω` and gross returns `gross ω > 0`, and
  has mass `prob t z ω` at review `t` in state `z`.
- Belief means `mu t z`, positive-definite covariances `Sigma t z`, `gamma > 0`, `beta ∈ (0, 1]`,
  purchase and sale rates `kp`, `km` in `[0, 1)`, finite positive dollar caps `cap`, and horizon `T ≥ 1`.
- `xstar t z = Σ(t, z)⁻¹ μ(t, z)/γ` is the frictionless target, `cost u` is `C(u)`, and `box` is `X`.
- `G t z x` is the stay objective: the tracking loss `(γ/2)(x - x*)'Σ(x - x*)` plus the discounted
  expected value of `V_{t+1}` at the marked holding.
- `V t z x` is the value function: `V_T = 0`, and for `t < T`,
  `V_t(x) = min_{x' ∈ X} [C(x' - x) + G_t(x')]` (defined by backward recursion as an infimum).
- `IsOpt t z x x'` says `x'` is an optimal post-trade holding from `x`, and `NT t z` is the
  no-trade set.

Part 1 is for one instrument (`n = 1`), with holdings in `ℝ` via `fun _ => x`. There
`c_t(z) = γ Σ(t, z)₀₀`, and the one-sided derivatives are Mathlib's `derivWithin f (Ioi x) x` (right, `rd`) and
`derivWithin f (Iio x) x` (left, `ld`). `lo` and `hi` are the band edges as the claim defines them.
Parts 1d and 1e use the next review's band, so they are stated for `t + 1 < T`, the claim's
`t ≤ T - 2`. 1e's case `t = T - 1` is a separate conjunct, under 1e's `κ⁺ + κ⁻ > 0`. 1d's
no-marking condition is written with both curvatures, `(κ⁻ + βκ⁺)/c_t + (κ⁺ + βκ⁻)/c_{t+1}`,
which is the claim's `(1 + β)(κ⁺ + κ⁻)/c` when the covariance is constant. The Consequence is a
reading, not formalized.
-/

namespace Standalone.M6QuarterlyBandStaticCeiling

open Matrix
open scoped Classical

noncomputable section

/-- A slack-budget M6 instance with `n` instruments, states `Z` and outcomes `Ω`. -/
structure M6 (n : ℕ) (Z Ω : Type) where
  T : ℕ
  mu : ℕ → Z → Fin n → ℝ
  Sigma : ℕ → Z → Matrix (Fin n) (Fin n) ℝ
  gamma : ℝ
  beta : ℝ
  kp : Fin n → ℝ
  km : Fin n → ℝ
  cap : Fin n → ℝ
  prob : ℕ → Z → Ω → ℝ
  next : Ω → Z
  gross : Ω → Fin n → ℝ

variable {n : ℕ} {Z Ω : Type} [Fintype Ω]

/-- M6's standing assumptions for a slack-budget instance. -/
def Setting (P : M6 n Z Ω) : Prop :=
  1 ≤ P.T ∧ (∀ t z, (P.Sigma t z)ᵀ = P.Sigma t z) ∧
  (∀ t z (v : Fin n → ℝ), v ≠ 0 → 0 < v ⬝ᵥ (P.Sigma t z *ᵥ v)) ∧
  0 < P.gamma ∧ 0 < P.beta ∧ P.beta ≤ 1 ∧
  (∀ i, 0 ≤ P.kp i ∧ P.kp i < 1 ∧ 0 ≤ P.km i ∧ P.km i < 1) ∧ (∀ i, 0 < P.cap i) ∧
  (∀ t z ω, 0 ≤ P.prob t z ω) ∧ (∀ t z, ∑ ω, P.prob t z ω = 1) ∧ ∀ ω i, 0 < P.gross ω i

/-- The frictionless target `x*(t, z) = Σ⁻¹ μ(t, z)/γ`. -/
def xstar (P : M6 n Z Ω) (t : ℕ) (z : Z) : Fin n → ℝ := (1 / P.gamma) • ((P.Sigma t z)⁻¹ *ᵥ P.mu t z)

/-- The cost `C(u) = Σᵢ [κ⁺ᵢ uᵢ⁺ + κ⁻ᵢ uᵢ⁻]`. -/
def cost (P : M6 n Z Ω) (u : Fin n → ℝ) : ℝ := ∑ i, (P.kp i * max (u i) 0 + P.km i * max (-u i) 0)

/-- The cap box `X = ∏ᵢ [0, x̄ᵢ]`. -/
def box (P : M6 n Z Ω) : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ P.cap i}

/-- The tracking loss `(γ/2)(x - x*)'Σ(x - x*)`. -/
def track (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : ℝ :=
  P.gamma / 2 * ((x - xstar P t z) ⬝ᵥ (P.Sigma t z *ᵥ (x - xstar P t z)))

/-- Marking `x ∘ g`. -/
def mark (x g : Fin n → ℝ) : Fin n → ℝ := fun i => x i * g i

/-- The value `k` reviews before the horizon: `Vk 0 = 0`, and `Vk (k+1)` is the minimum over `X` of
the cost plus the stay objective at review `T - (k+1)`. -/
def Vk (P : M6 n Z Ω) : ℕ → Z → (Fin n → ℝ) → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun z x => sInf ((fun x' => cost P (x' - x) + (track P (P.T - (k + 1)) z x' +
      P.beta * ∑ ω, P.prob (P.T - (k + 1)) z ω * Vk P k (P.next ω) (mark x' (P.gross ω)))) '' box P)

/-- `V_t`, with `V_T = 0`. -/
def V (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : ℝ := Vk P (P.T - t) z x

/-- The stay objective `G_t(x, z) = (γ/2)(x - x*)'Σ(x - x*) + β Σ q V_{t+1}(x ∘ g', z')`. -/
def G (P : M6 n Z Ω) (t : ℕ) (z : Z) (x : Fin n → ℝ) : ℝ :=
  track P t z x + P.beta * ∑ ω, P.prob t z ω * V P (t + 1) (P.next ω) (mark x (P.gross ω))

/-- `x'` is an optimal post-trade holding from `x`. -/
def IsOpt (P : M6 n Z Ω) (t : ℕ) (z : Z) (x x' : Fin n → ℝ) : Prop :=
  x' ∈ box P ∧ ∀ y ∈ box P, cost P (x' - x) + G P t z x' ≤ cost P (y - x) + G P t z y

/-- The no-trade set `NT_t(z) = {x ∈ X : x⁺_t(x, z) = x}`. -/
def NT (P : M6 n Z Ω) (t : ℕ) (z : Z) : Set (Fin n → ℝ) := {x | x ∈ box P ∧ IsOpt P t z x x}

/-! ### One instrument -/

section One

variable (P : M6 1 Z Ω)

/-- `G_t` on holdings in `ℝ`. -/
def G1 (t : ℕ) (z : Z) (x : ℝ) : ℝ := G P t z (fun _ => x)

/-- `V_t` on holdings in `ℝ`. -/
def V1 (t : ℕ) (z : Z) (x : ℝ) : ℝ := V P t z (fun _ => x)

/-- Right derivative. -/
def rd (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Set.Ioi x) x

/-- Left derivative. -/
def ld (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Set.Iio x) x

/-- `c_t(z) = γ Σ(t, z)`, the per-quarter tracking curvature. -/
def curv (t : ℕ) (z : Z) : ℝ := P.gamma * P.Sigma t z 0 0

/-- `lo_t(z) = inf {x ∈ [0, x̄) : G'_{t,+}(x) ≥ -κ⁺}` (`x̄` if empty). -/
def lo (t : ℕ) (z : Z) : ℝ :=
  if ({x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} : Set ℝ).Nonempty then
    sInf {x | 0 ≤ x ∧ x < P.cap 0 ∧ -P.kp 0 ≤ rd (G1 P t z) x} else P.cap 0

/-- `hi_t(z) = sup {x ∈ (0, x̄] : G'_{t,-}(x) ≤ κ⁻}` (`0` if empty). -/
def hi (t : ℕ) (z : Z) : ℝ :=
  if ({x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} : Set ℝ).Nonempty then
    sSup {x | 0 < x ∧ x ≤ P.cap 0 ∧ ld (G1 P t z) x ≤ P.km 0} else 0

/-- `clip(v, 0, x̄)`. -/
def clip (v : ℝ) : ℝ := min (max v 0) (P.cap 0)

/-- The target in `ℝ`. -/
def xs (t : ℕ) (z : Z) : ℝ := xstar P t z 0

/-- The expected gross return `ḡ_t(z) = Σ q g'`. -/
def gbar (t : ℕ) (z : Z) : ℝ := ∑ ω, P.prob t z ω * P.gross ω 0

/-- An (up) outcome: marking carries the band strictly into the next review's buy region. -/
def Up (t : ℕ) (z : Z) (ω : Ω) : Prop := hi P t z * P.gross ω 0 < lo P (t + 1) (P.next ω)

/-- A (down) outcome: marking carries the band strictly into the next review's sell region. -/
def Down (t : ℕ) (z : Z) (ω : Ω) : Prop := hi P (t + 1) (P.next ω) < lo P t z * P.gross ω 0

/-- `U = Σ_(up) q g'`. -/
def Umass (t : ℕ) (z : Z) : ℝ :=
  ∑ ω, if Up P t z ω then P.prob t z ω * P.gross ω 0 else 0

/-- `D = Σ_(down) q g'`. -/
def Dmass (t : ℕ) (z : Z) : ℝ :=
  ∑ ω, if Down P t z ω then P.prob t z ω * P.gross ω 0 else 0

/-- The tilt `τ = β(κ⁺ U - κ⁻ D)/c`. -/
def tilt (t : ℕ) (z : Z) : ℝ :=
  P.beta * (P.kp 0 * Umass P t z - P.km 0 * Dmass P t z) / curv P t z

end One

/-- Part 1a: regularity, the band, trade to the edge, and the derivative of `V_t`. -/
def Band : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → ∀ t z, t < P.T →
    StrictConvexOn ℝ Set.univ (G1 P t z) ∧ Continuous (G1 P t z) ∧
    ConvexOn ℝ Set.univ (V1 P t z) ∧ Continuous (V1 P t z) ∧
    (∀ x, 0 ≤ x → -P.kp 0 ≤ rd (V1 P t z) x ∧ rd (V1 P t z) x ≤ P.km 0) ∧
    (∀ x, 0 < x → -P.kp 0 ≤ ld (V1 P t z) x ∧ ld (V1 P t z) x ≤ rd (V1 P t z) x) ∧
    0 ≤ lo P t z ∧ lo P t z ≤ hi P t z ∧ hi P t z ≤ P.cap 0 ∧
    (∀ x, 0 ≤ x → ∃! x' : Fin 1 → ℝ, IsOpt P t z (fun _ => x) x') ∧
    (∀ x, 0 ≤ x → IsOpt P t z (fun _ => x) (fun _ => min (max x (lo P t z)) (hi P t z))) ∧
    (∀ x, 0 ≤ x → x < lo P t z → rd (V1 P t z) x = -P.kp 0 ∧ (0 < x → ld (V1 P t z) x = -P.kp 0)) ∧
    (∀ x, hi P t z < x → rd (V1 P t z) x = P.km 0 ∧ ld (V1 P t z) x = P.km 0) ∧
    ∀ x, lo P t z < x → x < hi P t z →
      rd (V1 P t z) x = rd (G1 P t z) x ∧ ld (V1 P t z) x = ld (G1 P t z) x

/-- Part 1b: the static width ceiling, and the exact last-review band. -/
def Ceiling : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P →
    (∀ t z, t < P.T → hi P t z - lo P t z ≤ (P.kp 0 + P.km 0) / curv P t z) ∧
    ∀ z, lo P (P.T - 1) z = clip P (xs P (P.T - 1) z - P.kp 0 / curv P (P.T - 1) z) ∧
      hi P (P.T - 1) z = clip P (xs P (P.T - 1) z + P.km 0 / curv P (P.T - 1) z) ∧
      (0 ≤ xs P (P.T - 1) z - P.kp 0 / curv P (P.T - 1) z → xs P (P.T - 1) z + P.km 0 / curv P (P.T - 1) z ≤ P.cap 0 →
        hi P (P.T - 1) z - lo P (P.T - 1) z = (P.kp 0 + P.km 0) / curv P (P.T - 1) z)

/-- Part 1c: the edge brackets. -/
def Brackets : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → ∀ t z, t < P.T →
    min (P.cap 0) (xs P t z - (P.kp 0 + P.beta * P.km 0 * gbar P t z) / curv P t z) ≤ lo P t z ∧
    hi P t z ≤ max 0 (xs P t z + (P.km 0 + P.beta * P.kp 0 * gbar P t z) / curv P t z)

/-- Part 1d: in the coarse-innovation regime the band is the static band shifted by the tilt; the
primitive sufficient conditions; and zero tilt for a symmetric law and symmetric rates. -/
def Coarse : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → ∀ t z, t + 1 < P.T →
    (0 < lo P t z → hi P t z < P.cap 0 →
      (∀ ω, 0 < P.prob t z ω → Up P t z ω ∨ Down P t z ω) →
      hi P t z = xs P t z + P.km 0 / curv P t z + tilt P t z ∧
      lo P t z = xs P t z - P.kp 0 / curv P t z + tilt P t z ∧
      hi P t z - lo P t z = (P.kp 0 + P.km 0) / curv P t z ∧
      (Umass P t z = Dmass P t z → P.kp 0 = P.km 0 → tilt P t z = 0)) ∧
    (∀ ω, 0 < P.prob t z ω →
      (P.gross ω 0 * max 0 (xs P t z + (P.km 0 + P.beta * P.kp 0 * gbar P t z) / curv P t z) <
        min (P.cap 0) (xs P (t + 1) (P.next ω) -
          (P.kp 0 + P.beta * P.km 0 * gbar P (t + 1) (P.next ω)) / curv P (t + 1) (P.next ω)) → Up P t z ω) ∧
      (max 0 (xs P (t + 1) (P.next ω) +
          (P.km 0 + P.beta * P.kp 0 * gbar P (t + 1) (P.next ω)) / curv P (t + 1) (P.next ω)) <
        P.gross ω 0 * min (P.cap 0) (xs P t z - (P.kp 0 + P.beta * P.km 0 * gbar P t z) / curv P t z)
        → Down P t z ω)) ∧
    ((∀ ω, P.gross ω 0 = 1) → 0 < lo P t z → hi P t z < P.cap 0 → ∀ ω, 0 < P.prob t z ω →
      ((P.km 0 + P.beta * P.kp 0) / curv P t z +
          (P.kp 0 + P.beta * P.km 0) / curv P (t + 1) (P.next ω) < xs P (t + 1) (P.next ω) - xs P t z →
        Up P t z ω) ∧
      (xs P (t + 1) (P.next ω) - xs P t z < -((P.kp 0 + P.beta * P.km 0) / curv P t z +
          (P.km 0 + P.beta * P.kp 0) / curv P (t + 1) (P.next ω)) →
        Down P t z ω))

/-- Part 1e: for `t ≤ T - 2` the ceiling is attained exactly when both edges are first-order points
and every positive-mass outcome carries the marked band into one of the next review's affine
pieces; at `t = T - 1` exactly when both edges are first-order points. -/
def Attained : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → 0 < P.kp 0 + P.km 0 →
    (∀ t z, t + 1 < P.T →
      (hi P t z - lo P t z = (P.kp 0 + P.km 0) / curv P t z ↔
        ld (G1 P t z) (hi P t z) = P.km 0 ∧ rd (G1 P t z) (lo P t z) = -P.kp 0 ∧
        ∀ ω, 0 < P.prob t z ω →
          hi P t z * P.gross ω 0 ≤ lo P (t + 1) (P.next ω) ∨
            hi P (t + 1) (P.next ω) ≤ lo P t z * P.gross ω 0) ∧
      (hi P t z - lo P t z ≠ (P.kp 0 + P.km 0) / curv P t z →
        hi P t z - lo P t z < (P.kp 0 + P.km 0) / curv P t z)) ∧
    ∀ z, (hi P (P.T - 1) z - lo P (P.T - 1) z = (P.kp 0 + P.km 0) / curv P (P.T - 1) z ↔
      ld (G1 P (P.T - 1) z) (hi P (P.T - 1) z) = P.km 0 ∧
        rd (G1 P (P.T - 1) z) (lo P (P.T - 1) z) = -P.kp 0)

/-! ### Many instruments -/

/-- Part 2a: convexity, uniqueness of the optimal post-trade holding, and the no-trade set. -/
def ManyConvex : Prop :=
  ∀ (n : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 n Z Ω), Setting P → ∀ t z, t < P.T →
    ConvexOn ℝ Set.univ (G P t z) ∧
    ConvexOn ℝ Set.univ (fun x => G P t z x - track P t z x) ∧
    ConvexOn ℝ Set.univ (V P t z) ∧
    (∀ x, ∃! x', IsOpt P t z x x') ∧ (NT P t z).Nonempty ∧
    ∀ x x', IsOpt P t z x x' → x' ∈ NT P t z

/-- Part 2b: the `Σ`-diameter inequality, the single-coordinate width and the Euclidean bound. -/
def Diameter : Prop :=
  ∀ (n : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 n Z Ω), Setting P → ∀ t z, t < P.T →
    ∀ x ∈ NT P t z, ∀ y ∈ NT P t z,
      P.gamma * ((x - y) ⬝ᵥ (P.Sigma t z *ᵥ (x - y))) ≤ ∑ i, (P.kp i + P.km i) * |x i - y i| ∧
      (∀ i w, x - y = Pi.single i w → |w| ≤ (P.kp i + P.km i) / (P.gamma * P.Sigma t z i i)) ∧
      ∀ lam K : ℝ, 0 < lam → (∀ v, lam * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (P.Sigma t z *ᵥ v)) →
        (∀ i, P.kp i + P.km i ≤ K) →
        Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Real.sqrt n * K / (P.gamma * lam)

/-- Part 2c: the static shape of the no-trade set at the last review, the parallelotope where no
bound binds, and the bundling reading of one instrument's condition. -/
def StaticShape : Prop :=
  ∀ (n : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 n Z Ω), Setting P → ∀ z,
    let g := fun x => P.gamma • (P.Sigma (P.T - 1) z *ᵥ (x - xstar P (P.T - 1) z))
    (∀ x, x ∈ NT P (P.T - 1) z ↔ x ∈ box P ∧ ∀ i,
      (0 < x i → x i < P.cap i → -P.kp i ≤ g x i ∧ g x i ≤ P.km i) ∧
      (x i = 0 → -P.kp i ≤ g x i) ∧ (x i = P.cap i → g x i ≤ P.km i)) ∧
    (∀ x, (∀ i, 0 < x i ∧ x i < P.cap i) →
      (x ∈ NT P (P.T - 1) z ↔ ∀ i, -P.kp i ≤ g x i ∧ g x i ≤ P.km i)) ∧
    ∀ (d : Fin n → ℝ) (A : Fin n),
      (-P.kp A ≤ P.gamma * (P.Sigma (P.T - 1) z *ᵥ d) A ∧
          P.gamma * (P.Sigma (P.T - 1) z *ᵥ d) A ≤ P.km A) ↔
      (-P.kp A / (P.gamma * P.Sigma (P.T - 1) z A A) ≤
          d A + (∑ j, if j = A then 0 else P.Sigma (P.T - 1) z A j * d j) / P.Sigma (P.T - 1) z A A ∧
        d A + (∑ j, if j = A then 0 else P.Sigma (P.T - 1) z A j * d j) / P.Sigma (P.T - 1) z A A
          ≤ P.km A / (P.gamma * P.Sigma (P.T - 1) z A A))

/-- Claim 029, parts 1-2. -/
def statement : Prop :=
  Band ∧ Ceiling ∧ Brackets ∧ Coarse ∧ Attained ∧ ManyConvex ∧ Diameter ∧ StaticShape

end

end Standalone.M6QuarterlyBandStaticCeiling

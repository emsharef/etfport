import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

/-!
# Claim 043: the fine-regime cost with one costly ETF, sandwiched in the inputs

Statement only; the proof is `Novel/M7FineCostSandwichProof.lean`.

The corrector problem of the pair is stated in claim 042's coordinates `y = (y_a, e)` and built from the
inputs `γ, Σ, v_A, v_B, r, κ_A, κ_E`:
- the running cost `(c^res/2) y_a² + (c_E/2) e²`;
- the innovation covariance `W = [[v_A, w], [w, v_B^eff]]`;
- the polytope `C = {p : |p_a + ρ_h p_e| ≤ κ_A, |p_e| ≤ κ_E}` and its support function `δ_C`;
- the equation `max {a - (1/2) tr(W D²w) - cost, H_C(Dw)} = 0` (proof part 0's form).

`IsSub` and `IsSuper` are classical (`C²`) sub- and supersolutions with eigenvalue `a₁` or `a₂`. Their
growth is `w₁ ≤ δ_C + K` or `w₂ ≥ δ_C - K`, which imply AX-16's limit conditions. `IsEig P a` says that
every such subsolution's eigenvalue is at most `a`, and `a` is at most every such supersolution's.
AX-16 (`possamai2015homogenization` Theorem 3.1, applied with Theorem 3.2's corrector) gives that the
corrector's eigenvalue is such an `a`. That existence is the Prop `AX16`, as AX-13 was for claims 040
and 104 (PM's scope, 2026-09-29). The split: parts 1-4 hold for every `a` with `IsEig P a` and do not
assume `AX16`; only the eigenvalue's existence uses `AX16`.

- Part 1 (`Sandwich`), unconditional:
  - the separable test functions are sub- and supersolutions (proof part 2, the claim's argument);
  - the general lower bound holds for every admissible `(k_A', k_E')`, and its max is attained;
  - the displayed bounds hold.
- Part 1's third lower bound (`GapBound`), through the ETF's own gap `y_b = e - ρ_h y_a`: a classical
  subsolution with eigenvalue `a_b(κ_E)`, AX-15's eigenvalue with `c_b = c^res c_E/(c^res + ρ_h² c_E)`
  and `v_B`, so `a ≥ a_b(κ_E)`.
- Part 2 (`Uncorrelated`): `Σ_AE = 0` gives `a = a_A(κ_A) + a_E(κ_E)`, whatever `r`.
- Part 3 (`Gap`): the identity and the bound `2[1 - (1 - x)^{2/3}]`.
- Part 4:
  - (a) `EffectiveRate`: an effective rate `k*` in `[κ_A - |ρ_h|κ_E, κ_A + |ρ_h|κ_E]`;
  - (b) `BandRatio`: the arithmetic `Δ_A(k*)³/Δ_A(κ_A)³ ∈ [1 - x, 1 + x]`;
  - (c) `SmallEtfRate`: the end `κ_E → 0`, where `a → a_A(κ_A)`; and `FrozenEnd`: `a → ∞` as
    `κ_E → ∞`, through the third lower bound.

Paper-level:
- part 3's expansion `(4/3)x + O(x²)`;
- 4(a)'s identification with claim 107's `H`;
- 4(b)'s reading of the non-contact set as a band;
- 4(c)'s reading of the frozen end as a non-ergodic object;
- the reading of `F(ξ)` as the non-contact set along the line `e = ρ_h y_a`;
- the cited step that classical sub- and supersolutions are viscosity ones, and the uniqueness of `a`
  (AX-16);
- the hypothesis check that AX-16 applies to the pair's problem (proof part 0, red's required
  correction). The change of variables `z_A = y_a`, `z_E = e - ρ_h y_a` turns `C` into the source's
  cash-only box. The Prop `AX16` is stated in the `y` coordinates it justifies.
-/

namespace Standalone.M7FineCostSandwich

open Filter Topology Set

noncomputable section

/-- The inputs: risk aversion, the covariance entries of the fund and the ETF, the innovation
variances of the targets and their correlation, and the per-side rates. -/
structure Inputs where
  gamma : ℝ
  sAA : ℝ
  sAE : ℝ
  sEE : ℝ
  vA : ℝ
  vB : ℝ
  r : ℝ
  kA : ℝ
  kE : ℝ

namespace Inputs

variable (P : Inputs)

/-- The hedge ratio `ρ_h = Σ_AE/Σ_EE`. -/
def rho : ℝ := P.sAE / P.sEE

/-- The residual curvature `c^res = γ(Σ_AA - Σ_AE²/Σ_EE)`. -/
def cres : ℝ := P.gamma * (P.sAA - P.sAE ^ 2 / P.sEE)

/-- The ETF's curvature `c_E = γ Σ_EE`. -/
def cE : ℝ := P.gamma * P.sEE

/-- The innovation variance of the ETF's effective target, `v_B + ρ_h² v_A + 2 ρ_h r √(v_A v_B)`. -/
def vBeff : ℝ := P.vB + P.rho ^ 2 * P.vA + 2 * P.rho * P.r * Real.sqrt (P.vA * P.vB)

/-- The innovation covariance `w = r √(v_A v_B) + ρ_h v_A`. -/
def wc : ℝ := P.r * Real.sqrt (P.vA * P.vB) + P.rho * P.vA

end Inputs

/-- The standing hypotheses: `γ > 0`, `Σ` positive definite, positive rates, and `W` positive definite
(`v_A, v_B > 0`, `|r| < 1`, AX-16's ellipticity). -/
structure Setting (P : Inputs) : Prop where
  gamma_pos : 0 < P.gamma
  sEE_pos : 0 < P.sEE
  det_pos : P.sAE ^ 2 < P.sAA * P.sEE
  vA_pos : 0 < P.vA
  vB_pos : 0 < P.vB
  r_sq : P.r ^ 2 < 1
  kA_pos : 0 < P.kA
  kE_pos : 0 < P.kE

/-! ### The corrector problem of the pair -/

/-- The running cost `(c^res/2) y_a² + (c_E/2) e²`. -/
def cost (P : Inputs) (y : ℝ × ℝ) : ℝ := P.cres / 2 * y.1 ^ 2 + P.cE / 2 * y.2 ^ 2

/-- The gradient `Dw(y) = (∂_a w, ∂_e w)`. -/
def grad (f : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (fderiv ℝ f y (1, 0), fderiv ℝ f y (0, 1))

/-- The second derivative `D²w(y)(u, v)`. -/
def d2 (f : ℝ × ℝ → ℝ) (y u v : ℝ × ℝ) : ℝ := fderiv ℝ (fun z => fderiv ℝ f z u) y v

/-- The diffusion term `(1/2) tr(W D²w)`. -/
def diffusion (P : Inputs) (f : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  (P.vA * d2 f y (1, 0) (1, 0) + 2 * P.wc * d2 f y (1, 0) (0, 1) + P.vBeff * d2 f y (0, 1) (0, 1)) / 2

/-- The polytope `C` of admissible gradients: `|p_a + ρ_h p_e| ≤ κ_A` and `|p_e| ≤ κ_E`. -/
def InC (P : Inputs) (p : ℝ × ℝ) : Prop := |p.1 + P.rho * p.2| ≤ P.kA ∧ |p.2| ≤ P.kE

/-- The interior of `C`. -/
def InIntC (P : Inputs) (p : ℝ × ℝ) : Prop := |p.1 + P.rho * p.2| < P.kA ∧ |p.2| < P.kE

/-- The support function `δ_C(y) = κ_A |y_a| + κ_E |e - ρ_h y_a|`. -/
def deltaC (P : Inputs) (y : ℝ × ℝ) : ℝ := P.kA * |y.1| + P.kE * |y.2 - P.rho * y.1|

/-- A classical subsolution with eigenvalue `a₁`: `C²`, growth `w ≤ δ_C + K`, and at every point
`a₁ ≤ (1/2) tr(W D²w) + cost` and `Dw ∈ C` (both terms of the equation `≤ 0`). -/
def IsSub (P : Inputs) (w : ℝ × ℝ → ℝ) (a₁ : ℝ) : Prop :=
  ContDiff ℝ 2 w ∧ (∃ K, ∀ y, w y ≤ deltaC P y + K) ∧
    ∀ y, a₁ ≤ diffusion P w y + cost P y ∧ InC P (grad w y)

/-- A classical supersolution with eigenvalue `a₂`: `C²`, growth `w ≥ δ_C - K`, and at every point
`(1/2) tr(W D²w) + cost ≤ a₂` or `Dw ∉ int C` (the maximum of the two terms `≥ 0`). -/
def IsSuper (P : Inputs) (w : ℝ × ℝ → ℝ) (a₂ : ℝ) : Prop :=
  ContDiff ℝ 2 w ∧ (∃ K, ∀ y, deltaC P y - K ≤ w y) ∧
    ∀ y, diffusion P w y + cost P y ≤ a₂ ∨ ¬ InIntC P (grad w y)

/-- `a` lies between every classical subsolution's eigenvalue and every classical supersolution's. -/
def IsEig (P : Inputs) (a : ℝ) : Prop :=
  (∀ w a₁, IsSub P w a₁ → a₁ ≤ a) ∧ (∀ w a₂, IsSuper P w a₂ → a ≤ a₂)

/-- AX-16 (`possamai2015homogenization` Theorems 3.1-3.2), as cited. Under the standing hypotheses,
the corrector problem has an eigenvalue `a` with a convex `C^{1,1}` solution of growth `w/δ_C → 1`.
Comparison against it places `a` between classical sub- and supersolutions' eigenvalues. -/
def AX16 : Prop := ∀ P : Inputs, Setting P → ∃ a, IsEig P a

/-! ### The one-instrument eigenvalues and the bounds -/

/-- AX-15's half-width `Δ(k) = (3(2k)v/(4c))^{1/3}` at per-side rate `k`. -/
def Dl (c v k : ℝ) : ℝ := (3 * (2 * k) * v / (4 * c)) ^ ((1 : ℝ) / 3)

/-- AX-15's one-instrument eigenvalue `(c/2)(3(2k)v/(4c))^{2/3}` at per-side rate `k`. -/
def aOne (c v k : ℝ) : ℝ := c / 2 * (3 * (2 * k) * v / (4 * c)) ^ ((2 : ℝ) / 3)

/-- The fund's one-instrument eigenvalue `a_A(k)`, with `c^res` and `v_A`. -/
def aA (P : Inputs) (k : ℝ) : ℝ := aOne P.cres P.vA k

/-- The ETF's one-instrument eigenvalue `a_E(k)`, with `c_E` and `v_B^eff`. -/
def aE (P : Inputs) (k : ℝ) : ℝ := aOne P.cE P.vBeff k

/-- The re-hedge cost over the fund's rate, `x = |ρ_h| κ_E/κ_A`. -/
def x (P : Inputs) : ℝ := |P.rho| * P.kE / P.kA

/-- The displayed lower bound `a_A(κ_A - |ρ_h|κ_E) + a_E(κ_E)`. -/
def lower (P : Inputs) : ℝ := aA P (P.kA - |P.rho| * P.kE) + aE P P.kE

/-- The upper bound `a_A(κ_A + |ρ_h|κ_E) + a_E(κ_E)`. -/
def upper (P : Inputs) : ℝ := aA P (P.kA + |P.rho| * P.kE) + aE P P.kE

/-- The admissible pairs of the general lower bound: `k_A', k_E' ≥ 0`, `k_A' + |ρ_h| k_E' ≤ κ_A`,
`k_E' ≤ κ_E`. -/
def Adm (P : Inputs) (kA' kE' : ℝ) : Prop :=
  0 ≤ kA' ∧ 0 ≤ kE' ∧ kA' + |P.rho| * kE' ≤ P.kA ∧ kE' ≤ P.kE

/-! ### The claim -/

/-- Part 1, the sandwich.
- For every admissible pair there is a classical subsolution with eigenvalue `a_A(k_A') + a_E(k_E')`.
- There is a classical supersolution with eigenvalue `a_A(κ_A + |ρ_h|κ_E) + a_E(κ_E)`.
- The general lower bound's max over admissible pairs is attained.
- Every `a` with `IsEig P a` is above each admissible pair's sum and below the upper bound; with
  `|ρ_h|κ_E < κ_A`, it is above the displayed lower bound. -/
def Sandwich : Prop :=
  ∀ P : Inputs, Setting P →
    (∀ kA' kE', Adm P kA' kE' → ∃ w, IsSub P w (aA P kA' + aE P kE')) ∧
    (∃ w, IsSuper P w (upper P)) ∧
    (∃ q : ℝ × ℝ, Adm P q.1 q.2 ∧
      ∀ q' : ℝ × ℝ, Adm P q'.1 q'.2 → aA P q'.1 + aE P q'.2 ≤ aA P q.1 + aE P q.2) ∧
    ∀ a, IsEig P a →
      (∀ kA' kE', Adm P kA' kE' → aA P kA' + aE P kE' ≤ a) ∧ a ≤ upper P ∧
      (|P.rho| * P.kE < P.kA → lower P ≤ a)

/-- Part 2: with `Σ_AE = 0`, `a = a_A(κ_A) + a_E(κ_E)`, whatever the correlation `r`. -/
def Uncorrelated : Prop :=
  ∀ P : Inputs, Setting P → P.sAE = 0 → ∀ a, IsEig P a → a = aA P P.kA + aE P P.kE

/-- Part 3, with `x < 1`:
- the bounds' fund terms are `a_A(κ_A)(1 ∓ x)^{2/3}`, with `a_A(κ_A) > 0`;
- `(upper - lower)/a_A(κ_A) = (1 + x)^{2/3} - (1 - x)^{2/3} ≤ 2[1 - (1 - x)^{2/3}]`. -/
def Gap : Prop :=
  ∀ P : Inputs, Setting P → x P < 1 →
    0 < aA P P.kA ∧
    aA P (P.kA - |P.rho| * P.kE) = aA P P.kA * (1 - x P) ^ ((2 : ℝ) / 3) ∧
    aA P (P.kA + |P.rho| * P.kE) = aA P P.kA * (1 + x P) ^ ((2 : ℝ) / 3) ∧
    (upper P - lower P) / aA P P.kA = (1 + x P) ^ ((2 : ℝ) / 3) - (1 - x P) ^ ((2 : ℝ) / 3) ∧
    (1 + x P) ^ ((2 : ℝ) / 3) - (1 - x P) ^ ((2 : ℝ) / 3) ≤ 2 * (1 - (1 - x P) ^ ((2 : ℝ) / 3))

/-- Part 4(a): with `|ρ_h|κ_E ≤ κ_A`, every `a` with `IsEig P a` is `a_A(k*) + a_E(κ_E)` for an
effective rate `k*` in `[κ_A - |ρ_h|κ_E, κ_A + |ρ_h|κ_E]`. -/
def EffectiveRate : Prop :=
  ∀ P : Inputs, Setting P → |P.rho| * P.kE ≤ P.kA → ∀ a, IsEig P a →
    ∃ k ∈ Icc (P.kA - |P.rho| * P.kE) (P.kA + |P.rho| * P.kE), a = aA P k + aE P P.kE

/-- Part 4(b)'s arithmetic: with `x ≤ 1`, for every rate `k` in `[κ_A - |ρ_h|κ_E, κ_A + |ρ_h|κ_E]`
the fund's one-instrument half-widths satisfy `Δ_A(k)³/Δ_A(κ_A)³ ∈ [1 - x, 1 + x]`. -/
def BandRatio : Prop :=
  ∀ P : Inputs, Setting P → x P ≤ 1 →
    ∀ k ∈ Icc (P.kA - |P.rho| * P.kE) (P.kA + |P.rho| * P.kE),
      Dl P.cres P.vA k ^ 3 / Dl P.cres P.vA P.kA ^ 3 ∈ Icc (1 - x P) (1 + x P)

/-- The least curvature of the pair's cost at a fixed ETF gap `y_b = e - ρ_h y_a`, over the fund's
holding: `c_b = c^res c_E/(c^res + ρ_h² c_E)`. -/
def cb (P : Inputs) : ℝ := P.cres * P.cE / (P.cres + P.rho ^ 2 * P.cE)

/-- The third lower bound `a_b(k)`: AX-15's eigenvalue for the ETF's own gap, with `c_b` and `v_B`. -/
def ab (P : Inputs) (k : ℝ) : ℝ := aOne (cb P) P.vB k

/-- Part 1's third lower bound. `w_{κ_E}(e - ρ_h y_a)` is a classical subsolution with eigenvalue
`a_b(κ_E)`, so every `a` with `IsEig P a` has `a ≥ a_b(κ_E)`. -/
def GapBound : Prop :=
  ∀ P : Inputs, Setting P →
    (∃ w, IsSub P w (ab P P.kE)) ∧ ∀ a, IsEig P a → ab P P.kE ≤ a

/-- Part 4(c), the frozen-ETF end: along ETF rates `k → ∞`, eigenvalues `a(k)` (each with `IsEig`)
tend to `∞`, through the third lower bound. -/
def FrozenEnd : Prop :=
  ∀ P : Inputs, Setting P → ∀ a : ℝ → ℝ, (∀ k, 0 < k → IsEig { P with kE := k } (a k)) →
    Tendsto a atTop atTop

/-- Part 4(c), the frictionless-ETF end: along ETF rates `k → 0⁺`, eigenvalues `a(k)` (each with
`IsEig`) tend to `a_A(κ_A)`. -/
def SmallEtfRate : Prop :=
  ∀ P : Inputs, Setting P → ∀ a : ℝ → ℝ, (∀ k, 0 < k → IsEig { P with kE := k } (a k)) →
    Tendsto a (𝓝[>] 0) (𝓝 (aA P P.kA))

/-- Claim 043 (parts 1-4, with the paper-level readings named in the module note). -/
def statement : Prop :=
  Sandwich ∧ GapBound ∧ Uncorrelated ∧ Gap ∧ EffectiveRate ∧ BandRatio ∧ SmallEtfRate ∧ FrozenEnd

end

end Standalone.M7FineCostSandwich

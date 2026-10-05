import Standalone.M7TwoReviewsBounds
import Standalone.M7OneEtfTwoScalars

/-!
# Claim 113: several funds sharing one ETF and cash over two reviews

Statement only; the proof is `Novel/M7SeveralFundsReserveProof.lean`.

Claim 044's model (`Two ι Z`) is already stated for any finite set of instruments. So 1a, the
root's lines with `N` funds and the ETF, is claim 044's formal part 2 (`Sufficient`, `Necessary`),
cited and not restated. Claim 046's objects (`need`, `Cov`, `LinesAt`) are reused (Q-04). The ETF is
a designated instrument `E`. M8's factor structure, `Σ_{0,ij} = b_i b_j s + δ_ij v_i` with `v_E = σ_E²`,
is the hypothesis `Factor`. In it:
- `r_i = b_i/b_E`;
- `w = Σ_j b_j x_j / b_E`, the exposure in ETF units;
- `m = μ_{0,E} - γ b_E² s w`, the exposure price;
- `α~_i = μ_{0,i} - r_i μ_{0,E}`.

- Part 1b:
  - `FundMarginal`: `g_{0,i} = α~_i + r_i m - γ v_i x_i` for every instrument. The ETF's case is its
    own line `m - γ σ_E² p`.
  - `RootClip`: at the root lines, every fund's holding is claim 110's clip at `(m, η̂_0)` with `S_i`
    added to `α~_i`. `ClipIsXi` shows the restated `clip` is claim 110's `xi`. It is restated because
    `xi` takes claim 110's `One N` coordinates, with the ETF outside the funds' index.
- Part 2:
  - `LiqTest` (2a), in leanb's clipped form: with `liq = h⁺_0 + (1 - κ⁻_E)(g_E p_0 - (x̂^s_E)⁺)⁺`,
    `need ≤ liq` at a state makes `η_1 = 0` admissible there, from any admissible multiplier.
  - `NoReserveLiq` (2b): with every state covered by `liq`, an admissible family with `η_1 = 0`
    exists. With `h⁺_0 > 0`, every family has `η_1 = 0`. Then `η̂_0 = η_0`, and every incumbent value
    lies in claim 029's bracket.
  - `Pooling` (2c): `max_z Σ_i need_i ≤ Σ_i max_z need_i`, with equality when one state attains every
    maximum.
- Part 3b (`CorrectedSign`): at a fund trading strictly inside its box the same way at both roots,
  `a^dyn - a^my = [S_i + r_i Δm - Δη(1 + κ)]/(γ v_i)`.
- Part 4:
  - `Wealth`: the wealth identity `R = Σ_funds (a^my - a^dyn) + [C(u^my) - C(u^dyn)]`.
  - `ClipLipschitz`: the clip moves by at most the change in its band's ends, which bounds each fund's
    move by part 3b's quantity over `γ v_i` off the trading pieces too.
  - `ResR`: claim 047's `Res` and this claim's `R` differ by `[1 - (1 - κ⁻_E) g^min_E]` times the
    ETF's move.

Paper-level:
- 3a (claim 110's cash root with `N` funds; the common price is claim 044's single `η_1(z)` per state);
- 2c's product-tree remark;
- the fixed-point remark;
- the unbounded exposure-price change;
- the Checks.
-/

namespace Standalone.M7SeveralFundsReserve

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds

noncomputable section

variable {ι Z : Type} [Fintype ι] [Fintype Z] [DecidableEq ι]

/-- M8's factor structure today: `Σ_{0,ij} = b_i b_j s + δ_ij v_i`, with the ETF's loading `b_E ≠ 0`. -/
def Factor (P : Two ι Z) (E : ι) (b : ι → ℝ) (s : ℝ) (v : ι → ℝ) : Prop :=
  b E ≠ 0 ∧ ∀ i j, P.S0 i j = b i * b j * s + if i = j then v i else 0

/-- The netting weight `r_i = b_i/b_E`. -/
def rw (b : ι → ℝ) (E : ι) (i : ι) : ℝ := b i / b E

/-- The exposure price `m = μ_{0,E} - γ b_E² s w` with `w = Σ_j b_j x_j / b_E`. -/
def mx (P : Two ι Z) (E : ι) (b : ι → ℝ) (s : ℝ) (x : ι → ℝ) : ℝ :=
  P.mu0 E - P.gamma * (b E ^ 2 * s) * ((∑ j, b j * x j) / b E)

/-- The net alpha `α~_i = μ_{0,i} - r_i μ_{0,E}`. -/
def alt (P : Two ι Z) (E : ι) (b : ι → ℝ) (i : ι) : ℝ := P.mu0 i - rw b E i * P.mu0 E

/-- Claim 110's clip at `(L, η)` with curvature `c`: `clip(x⁻, lo, hi)` clipped to `[0, x̄]`, where
`lo = (L - η - (1 + η) κ⁺)/c` and `hi = (L - η + (1 + η) κ⁻)/c` (the formula of claim 110's `xi`). -/
def clip (L η c kp km xbar xm : ℝ) : ℝ :=
  max 0 (min xbar (max ((L - η - (1 + η) * kp) / c) (min ((L - η + (1 + η) * km) / c) xm)))

/-- The ETF's solo sale threshold tomorrow, `x̂^s_E = (μ_{1,E} + κ⁻_E)/(γ Σ_{1,EE})`. -/
def xhatS (P : Two ι Z) (z : Z) (E : ι) : ℝ := (P.mu1 z E + P.km E) / (P.gamma * P.S1 z E E)

/-- Today's cash plus the ETF's sale proceeds down to its solo sale threshold (clipped at zero),
`liq = h⁺_0 + (1 - κ⁻_E)(g_E p_0 - (x̂^s_E)⁺)⁺`. -/
def liq (P : Two ι Z) (z : Z) (E : ι) (x0 : ι → ℝ) : ℝ :=
  h0 P x0 + (1 - P.km E) * max (P.g z E * x0 E - max (xhatS P z E) 0) 0

/-- Instrument `i`'s part of the need, `(1 + κ⁺_i)(x̂_i - g_i x_{0,i})⁺`. -/
def needI (P : Two ι Z) (z : Z) (x0 : ι → ℝ) (i : ι) : ℝ :=
  (1 + P.kp i) * max (xhat P z i - carry P z x0 i) 0

/-- Part 1b's identity: under the factor structure, `g_{0,i} = α~_i + r_i m - γ v_i x_i` for every
instrument (for the ETF, `r_E = 1` and `α~_E = 0`). -/
def FundMarginal : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (E : ι) (b : ι → ℝ) (s : ℝ)
    (v : ι → ℝ), Factor P E b s v → ∀ (x : ι → ℝ) (i : ι),
      g0 P x i = alt P E b i + rw b E i * mx P E b s x - P.gamma * v i * x i

/-- Part 1b: at a feasible policy with the root lines (and tomorrow's lines, so that `η̂_0 ≥ 0`), every fund `i` with
`v_i > 0` holds claim 110's clip at `L = α~_i + S_i + r_i m`, the dynamic cash price `η̂_0` and
curvature `γ v_i`. -/
def RootClip : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (E : ι) (b : ι → ℝ) (s : ℝ)
    (v : ι → ℝ), Hyp P → Factor P E b s v →
    ∀ X ∈ Feas P, ∀ η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 →
    ∀ i, 0 < v i →
      X.1 i = clip (alt P E b i + Sinc P η1 t1 i + rw b E i * mx P E b s X.1) (etaHat P η0 η1)
        (P.gamma * v i) (P.kp i) (P.km i) (P.xbar i) (P.xm i)

/-- Part 2a: at a feasible policy, if `need ≤ liq` at state `z`, then from any admissible multiplier
the multiplier `0` is admissible there (with some slopes). -/
def LiqTest : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (E : ι), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ z e t, LinesAt P X z e t → need P z X.1 ≤ liq P z E X.1 →
      ∃ t', LinesAt P X z 0 t'

/-- Part 2b: take any tomorrow family, with every state covered (`need ≤ liq`) at the root.
- There is an admissible family with `η_1 = 0` in every state. For it `η̂_0 = η_0`, and every
  incumbent value lies in claim 029's bracket `[-β E[g_i] κ⁻_i, β E[g_i] κ⁺_i]`.
- With `h⁺_0 > 0`, every family has `η_1 = 0`, with the same consequences. At the edge
  `h⁺_0 = 0 = need` this can fail (claim 046's 1(c) edge). -/
def NoReserveLiq : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (E : ι), Hyp P → Cov P →
    ∀ X ∈ Feas P, ∀ (η0 : ℝ) η1 t1, Tomorrow P X η1 t1 →
      (∀ z, need P z X.1 ≤ liq P z E X.1) →
      (∃ t1', Tomorrow P X (fun _ => 0) t1' ∧ etaHat P η0 (fun _ => 0) = η0 ∧
        ∀ i, -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ≤ Sinc P (fun _ => 0) t1' i ∧
          Sinc P (fun _ => 0) t1' i ≤ P.beta * ∑ z, P.q z * P.g z i * P.kp i) ∧
      (0 < h0 P X.1 → (∀ z, η1 z = 0) ∧ etaHat P η0 η1 = η0 ∧
        ∀ i, -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ≤ Sinc P η1 t1 i ∧
          Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * P.kp i)

/-- Part 2c: the maximal aggregate need is at most the sum of the instruments' maximal needs, with
equality when one state attains every instrument's maximum. -/
def Pooling : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (x0 : ι → ℝ),
    (⨆ z, need P z x0) ≤ ∑ i, ⨆ z, needI P z x0 i ∧
    ∀ z0, (∀ i z, needI P z x0 i ≤ needI P z0 x0 i) → (⨆ z, need P z x0) = ∑ i, ⨆ z, needI P z x0 i

/-- Part 3b: take fund `i` trading strictly inside its box in the same direction at the dynamic root
(its line with `S_i`, `m^dyn`, `η̂`) and at the myopic root (with `m^my`, `η^my`), with trade slope
`κ` (`κ⁺_i` for a purchase, `-κ⁻_i` for a sale). Then
`a^dyn - a^my = [S_i + r_i (m^dyn - m^my) - (η̂ - η^my)(1 + κ)]/(γ v_i)`. -/
def CorrectedSign : Prop :=
  ∀ (al r S mdyn mmy ehat emy κ c adyn amy : ℝ), 0 < c →
    al + S + r * mdyn - c * adyn - ehat - (1 + ehat) * κ = 0 →
    al + r * mmy - c * amy - emy - (1 + emy) * κ = 0 →
    adyn - amy = (S + r * (mdyn - mmy) - (ehat - emy) * (1 + κ)) / c

/-- Part 4's wealth identity: for any two roots, the ETF-plus-cash difference is the funds' holdings
foregone plus the cost difference. -/
def Wealth : Prop :=
  ∀ (ι Z : Type) [Fintype ι] [Fintype Z] [DecidableEq ι] (P : Two ι Z) (E : ι) (xd xy : ι → ℝ),
    (xd E + h0 P xd) - (xy E + h0 P xy) =
      (∑ i ∈ Finset.univ.erase E, (xy i - xd i)) + (cost P (xy - P.xm) - cost P (xd - P.xm))

/-- Part 4's bound, for each fund: the clip is 1-Lipschitz in its band's ends, which move by
`(ΔL - Δη(1 + κ⁺))/c` and `(ΔL - Δη(1 - κ⁻))/c`. So the fund moves by at most
`[|ΔL| + |Δη|(1 + κ⁺)]/c`, with `ΔL = ΔS + r Δm` part 3b's quantity. -/
def ClipLipschitz : Prop :=
  ∀ (L L' η η' c kp km xbar xm : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → km < 1 →
    |clip L η c kp km xbar xm - clip L' η' c kp km xbar xm| ≤
      (|L - L'| + |η - η'| * (1 + kp)) / c

/-- Part 4's two reserve measures. Claim 047's signed reserve `Res`, with the ETF at its worst-case
liquidation `(1 - κ⁻_E) g^min_E`, and this claim's `R` at par differ by
`Res = R - [1 - (1 - κ⁻_E) g^min_E](p^dyn - p^my)`. -/
def ResR : Prop :=
  ∀ (pd pm hd hm km gmin : ℝ),
    (hd + (1 - km) * gmin * pd) - (hm + (1 - km) * gmin * pm) =
      ((pd + hd) - (pm + hm)) - (1 - (1 - km) * gmin) * (pd - pm)

/-- The clip is claim 110's: in claim 110's coordinates (`One N`), its `xi` is `clip` at
`L = α~_i + r_i m`. Claim 110's `xi` takes `One N`, with the funds as `Fin N` and the ETF separate,
while claim 044's `Two ι Z` holds the ETF among its instruments. So the clip is restated here with
the same formula, and this conjunct records that the two agree (PM's scope note, Q-04). -/
def ClipIsXi : Prop :=
  ∀ (N : ℕ) (Q : Standalone.M7OneEtfTwoScalars.One N) (m η : ℝ) (i : Fin N),
    Standalone.M7OneEtfTwoScalars.xi Q m η i =
      clip (Q.alt i + Q.r i * m) η (Q.gamma * Q.v i) (Q.kp i) (Q.km i) (Q.xbar i) (Q.xm i)

/-- Claim 113 (paper-level parts in the module note). -/
def statement : Prop :=
  ClipIsXi ∧ FundMarginal ∧ RootClip ∧ LiqTest ∧ NoReserveLiq ∧ Pooling ∧ CorrectedSign ∧ Wealth ∧
    ClipLipschitz ∧ ResR

end

end Standalone.M7SeveralFundsReserve

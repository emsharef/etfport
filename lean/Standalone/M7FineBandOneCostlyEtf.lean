import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Standalone.M6QuarterlyBandStaticCeiling
import Standalone.M7DynamicBundlingBand

/-!
# Claim 042: the fund's fine-regime band with one costly ETF

Statement only; the proof is `Novel/M7FineBandOneCostlyEtfProof.lean`.

- Part 1, the error coordinate: an identity in the covariance entries, and the innovation moments of
  `e`'s target as second moments of a finite law.
- Part 2(a) is stated in claim 029's model with two instruments (`M6 2`, claim 107's finite-law
  setting). With `Σ_AE(t, z) = 0` at every review and state, the instance splits into two one-instrument
  instances, `part P 0` (the fund) and `part P 1` (the ETF). The value is the sum of their values, and a
  post-trade holding is optimal iff each coordinate is optimal in its own instance, whatever the
  outcome law, so whatever the targets' innovation correlation.
- Part 2(b) is claim 107's formal part 3.
- Part 2(c) is the completed square for a fixed ETF holding. The dynamic reading, in which the ETF
  never trades, is paper-level: M6's box `[0, x̄]` with `x̄ > 0` always allows a sale.
- Part 3: the corrector framework is AX-15 (cited). The revised claim's own lemma, the quartic's
  algebra (math's note), is formal (`Corrector`), together with its C² linear continuation off the band
  (`CorrectorC2`, with red's corrected gradient signs). So is the application to part 2's reductions:
  the ratio of the frozen and free half-widths.
- Part 4 is the identity for `ξ³`. The rest of part 4, including the end readings (red's correction 2),
  is paper-level.

The law itself (AX-15) is cited, not formalized: no formal conjunct uses it beyond its displayed formula.
-/

namespace Standalone.M7FineBandOneCostlyEtf

open Matrix Standalone.M6QuarterlyBandStaticCeiling

noncomputable section

/-! ### Part 1: the error coordinate -/

/-- Part 1: with `ρ_h = Σ_AE/Σ_EE`, `c^res = γ(Σ_AA - Σ_AE²/Σ_EE)` and `e = y_b + ρ_h y_a`,
`(γ/2)(y_a, y_b)Σ(y_a, y_b)' = (c^res/2) y_a² + (γ Σ_EE/2) e²`. -/
def ErrorCoord : Prop :=
  ∀ (gamma sAA sAE sEE ya yb : ℝ), sEE ≠ 0 →
    let rho := sAE / sEE
    let cres := gamma * (sAA - sAE ^ 2 / sEE)
    gamma / 2 * (sAA * ya ^ 2 + 2 * sAE * ya * yb + sEE * yb ^ 2) =
      cres / 2 * ya ^ 2 + gamma * sEE / 2 * (yb + rho * ya) ^ 2

/-- Second moment `Σ_s q_s f_s g_s` of a finite law. -/
def mom {S : Type} [Fintype S] (q : S → ℝ) (f g : S → ℝ) : ℝ := ∑ s, q s * (f s * g s)

/-- Part 1's innovation moments. If the targets' innovations `(da*, db*)` have second moments `v_A`,
`v_B` and `r √(v_A v_B)`, then `db* + ρ_h da*` has second moment
`v_B^eff = v_B + ρ_h² v_A + 2 ρ_h r √(v_A v_B)`, and its cross moment with `da*` is
`r √(v_A v_B) + ρ_h v_A`. `da* + ρ' db*` has second moment
`v^idle = v_A + ρ'² v_B + 2 ρ' r √(v_A v_B)`. -/
def Innovations : Prop :=
  ∀ (S : Type) [Fintype S] (q da db : S → ℝ) (vA vB r rho rho' : ℝ),
    mom q da da = vA → mom q db db = vB → mom q da db = r * Real.sqrt (vA * vB) →
    mom q (db + rho • da) (db + rho • da) = vB + rho ^ 2 * vA + 2 * rho * r * Real.sqrt (vA * vB) ∧
    mom q da (db + rho • da) = r * Real.sqrt (vA * vB) + rho * vA ∧
    mom q (da + rho' • db) (da + rho' • db) = vA + rho' ^ 2 * vB + 2 * rho' * r * Real.sqrt (vA * vB)

/-! ### Part 2: three exact reductions -/

variable {Z Ω : Type} [Fintype Ω]

/-- Instrument `i` of a two-instrument instance as a one-instrument instance: its own premium,
variance, rates, cap and gross return, and the common state and outcome law. -/
def part (P : M6 2 Z Ω) (i : Fin 2) : M6 1 Z Ω where
  T := P.T
  mu t z := fun _ => P.mu t z i
  Sigma t z := fun _ _ => P.Sigma t z i i
  gamma := P.gamma
  beta := P.beta
  kp := fun _ => P.kp i
  km := fun _ => P.km i
  cap := fun _ => P.cap i
  prob := P.prob
  next := P.next
  gross ω := fun _ => P.gross ω i

/-- Part 2(a): with uncorrelated risks (`Σ_AE(t, z) = 0` at every review and state), each instrument's
instance is an M6 instance. The value is the sum of the two one-instrument values, and a post-trade
holding is optimal iff each coordinate is optimal in its own instance. So the fund's band at every
review is its own one-instrument band (`lo`, `hi` of `part P 0`), whatever the joint law of the
targets and whatever the ETF's rates. -/
def Uncorrelated : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 2 Z Ω), Setting P → (∀ t z, P.Sigma t z 0 1 = 0) →
    (∀ i, Setting (part P i)) ∧
    (∀ t z i, xstar (part P i) t z 0 = xstar P t z i) ∧
    (∀ t z (x : Fin 2 → ℝ), V P t z x = V1 (part P 0) t z (x 0) + V1 (part P 1) t z (x 1)) ∧
    ∀ t z (x x' : Fin 2 → ℝ), t < P.T →
      (IsOpt P t z x x' ↔ IsOpt (part P 0) t z (fun _ => x 0) (fun _ => x' 0) ∧
        IsOpt (part P 1) t z (fun _ => x 1) (fun _ => x' 1))

/-- Part 2(b): claim 107's part 3 (frictionless ETFs). -/
def Frictionless : Prop := Standalone.M7DynamicBundlingBand.Frictionless

/-- Part 2(c): with the ETF holding `b` fixed, the stage loss is
`(γ Σ_AA/2)(a - ã*)² + (γ/2)(Σ_EE - Σ_AE²/Σ_AA)(b - b*)²` with `ã* = a* + ρ'(b* - b)`, `ρ' = Σ_AE/Σ_AA`. The
second term is free of `a`. -/
def Frozen : Prop :=
  ∀ (gamma sAA sAE sEE a b as bs : ℝ), sAA ≠ 0 →
    let rho' := sAE / sAA
    gamma / 2 * (sAA * (a - as) ^ 2 + 2 * sAE * (a - as) * (b - bs) + sEE * (b - bs) ^ 2) =
      gamma * sAA / 2 * (a - (as + rho' * (bs - b))) ^ 2 +
        gamma / 2 * (sEE - sAE ^ 2 / sAA) * (b - bs) ^ 2

/-! ### Part 3: the one-instrument ergodic law -/

/-- The corrector quartic `w(y) = -(c/(12v)) y⁴ + (λ/v) y² + ((κ⁻ - κ⁺)/2) y`. -/
def wq (c v kp km lam : ℝ) (y : ℝ) : ℝ := -(c / (12 * v)) * y ^ 4 + lam / v * y ^ 2 + (km - kp) / 2 * y

/-- Its first derivative. -/
def wq1 (c v kp km lam : ℝ) (y : ℝ) : ℝ := -(c / (3 * v)) * y ^ 3 + 2 * lam / v * y + (km - kp) / 2

/-- Its second derivative, `(2λ - c y²)/v`. -/
def wq2 (c v lam : ℝ) (y : ℝ) : ℝ := (2 * lam - c * y ^ 2) / v

/-- Part 3's lemma (the project's own, in the revised claim; the corrector framework is AX-15, cited):
for `c, v > 0`, the quartic solves `(v/2)w'' + (c/2)y² = λ`. `w''(±Δ) = 0` iff `λ = cΔ²/2`. Then
`w'(Δ) = κ⁻` and `w'(-Δ) = -κ⁺` iff `Δ³ = 3(κ⁺ + κ⁻)v/(4c)`. Under both, `w'' ≥ 0` on the band, so `w'` runs
from `-κ⁺` to `κ⁻` (the gradient constraint), and `(c/2)y² ≥ λ` off the band. -/
def Corrector : Prop :=
  ∀ (c v kp km lam D : ℝ), 0 < c → 0 < v → 0 < D →
    (∀ y, HasDerivAt (wq c v kp km lam) (wq1 c v kp km lam y) y) ∧
    (∀ y, HasDerivAt (wq1 c v kp km lam) (wq2 c v lam y) y) ∧
    (∀ y, v / 2 * wq2 c v lam y + c / 2 * y ^ 2 = lam) ∧
    ((wq2 c v lam D = 0 ∧ wq2 c v lam (-D) = 0) ↔ lam = c * D ^ 2 / 2) ∧
    (lam = c * D ^ 2 / 2 →
      ((wq1 c v kp km lam D = km ∧ wq1 c v kp km lam (-D) = -kp) ↔ D ^ 3 = 3 * (kp + km) * v / (4 * c))) ∧
    (lam = c * D ^ 2 / 2 → D ^ 3 = 3 * (kp + km) * v / (4 * c) → ∀ y ∈ Set.Icc (-D) D,
      0 ≤ wq2 c v lam y ∧ -kp ≤ wq1 c v kp km lam y ∧ wq1 c v kp km lam y ≤ km) ∧
    (lam = c * D ^ 2 / 2 → ∀ y, D ≤ |y| → lam ≤ c / 2 * y ^ 2)

/-- The candidate's `w'`: `-κ⁺` below `-Δ`, `κ⁻` above `Δ`, and between them
`(κ⁻ - κ⁺)/2 + (2λy - c y³/3)/v`. -/
def wp (c v kp km D : ℝ) (y : ℝ) : ℝ :=
  if y < -D then -kp else if D < y then km else (km - kp) / 2 + (c * D ^ 2 * y - c * y ^ 3 / 3) / v

/-- The candidate's `w''`: `(2λ - c y²)/v` on `[-Δ, Δ]`, `0` outside, with `λ = cΔ²/2`. -/
def wpp (c v D : ℝ) (y : ℝ) : ℝ := if |y| ≤ D then (c * D ^ 2 - c * y ^ 2) / v else 0

/-- Part 3's lemma, extended off the band: the quartic's `w'`, continued linearly outside `[-Δ, Δ]`, for
`c, v > 0` and `κ⁺, κ⁻ ≥ 0` with `κ⁺ + κ⁻ > 0`:
- the law `Δ³ = 3(κ⁺ + κ⁻)v/(4c)` has exactly one positive root `Δ`; for `D > 0`, the smooth-fit
  gradient change `4cD³/(3v)` equals `κ⁺ + κ⁻` iff `D = Δ`;
- at that `Δ`, with `λ = cΔ²/2`, the candidate's `w'` has derivative `w''` everywhere, and `w''` is
  continuous. So `w` is `C²`, and smooth fit holds, `w''(±Δ) = 0`;
- `-κ⁺ ≤ w' ≤ κ⁻`, with `w'(-Δ) = -κ⁺` and `w'(Δ) = κ⁻` (red's corrected gradient constraints);
- the HJB inequality `(v/2)w'' + (c/2)y² ≥ λ`, with equality on `[-Δ, Δ]`;
- `w''` vanishes on `[-Δ, Δ]` only at `±Δ`, so the band is symmetric whatever the rate asymmetry;
- attainment: `cΔ²/6 + (κ⁺ + κ⁻)v/(4Δ) = cΔ²/2 = λ`. -/
def CorrectorC2 : Prop :=
  ∀ (c v kp km : ℝ), 0 < c → 0 < v → 0 ≤ kp → 0 ≤ km → 0 < kp + km →
    (∃! D : ℝ, 0 < D ∧ D ^ 3 = 3 * (kp + km) * v / (4 * c)) ∧
    ∀ D : ℝ, 0 < D → D ^ 3 = 3 * (kp + km) * v / (4 * c) →
      let lam := c * D ^ 2 / 2
      (∀ D' : ℝ, 0 < D' → (4 * c * D' ^ 3 / (3 * v) = kp + km ↔ D' = D)) ∧
      (∀ y, HasDerivAt (wp c v kp km D) (wpp c v D y) y) ∧ Continuous (wpp c v D) ∧
      wpp c v D D = 0 ∧ wpp c v D (-D) = 0 ∧
      (∀ y, -kp ≤ wp c v kp km D y ∧ wp c v kp km D y ≤ km) ∧
      wp c v kp km D (-D) = -kp ∧ wp c v kp km D D = km ∧
      (∀ y, lam ≤ v / 2 * wpp c v D y + c / 2 * y ^ 2) ∧
      (∀ y, |y| ≤ D → v / 2 * wpp c v D y + c / 2 * y ^ 2 = lam) ∧
      (∀ y, |y| ≤ D → (wpp c v D y = 0 ↔ |y| = D)) ∧
      c * D ^ 2 / 6 + (kp + km) * v / (4 * D) = lam

/-- Part 3 applied to part 2's reductions. With `c^res = γ Σ_AA (1 - rc²)`, the frozen and free half-widths,
`Δ_frozen³ = 3(κ⁺_A + κ⁻_A)v^idle/(4γΣ_AA)` and `Δ_free³ = 3(κ⁺_A + κ⁻_A)v_A/(4c^res)`, satisfy
`Δ_frozen³/Δ_free³ = (1 - rc²) v^idle/v_A`. -/
def EndRatio : Prop :=
  ∀ (gamma sAA rc vA vidle k : ℝ), 0 < gamma → 0 < sAA → rc ^ 2 < 1 → 0 < vA → 0 < k →
    let cres := gamma * sAA * (1 - rc ^ 2)
    (3 * k * vidle / (4 * (gamma * sAA))) / (3 * k * vA / (4 * cres)) = (1 - rc ^ 2) * vidle / vA

/-! ### Part 4: the weight -/

/-- Part 4: `ξ³ = Δ_E³/Δ_free³ = [(κ⁺_E + κ⁻_E)/(κ⁺_A + κ⁻_A)] [v_B^eff/v_A] [c^res/(γ Σ_EE)]`, with
`Δ_E³ = 3(κ⁺_E + κ⁻_E)v_B^eff/(4γΣ_EE)` and `Δ_free³ = 3(κ⁺_A + κ⁻_A)v_A/(4c^res)`. -/
def Weight : Prop :=
  ∀ (gamma sEE cres vA vBeff kA kE : ℝ), 0 < gamma → 0 < sEE → 0 < cres → 0 < vA → 0 < kA →
    (3 * kE * vBeff / (4 * (gamma * sEE))) / (3 * kA * vA / (4 * cres)) =
      (kE / kA) * (vBeff / vA) * (cres / (gamma * sEE))

/-- Claim 042 (parts 1-4, with the paper-level readings named in the claim's Lean note). -/
def statement : Prop :=
  ErrorCoord ∧ Innovations ∧ Uncorrelated ∧ Frictionless ∧ Frozen ∧ Corrector ∧ CorrectorC2 ∧ EndRatio ∧ Weight

end

end Standalone.M7FineBandOneCostlyEtf

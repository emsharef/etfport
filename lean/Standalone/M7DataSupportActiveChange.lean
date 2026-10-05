import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Standalone.M5LearningAimTwoSpeeds

/-!
# Claim 039: when data can support an active change, in the inputs

Statement only; the proof is `Novel/M7DataSupportActiveChangeProof.lean`.

Covered: parts 1, 5, 6 and 7; part 2's upper bound, Bayesian form and the arithmetic of its lower
bound; part 3's upper bound and its two-point lower bound (stage 2, through claim 015's finite Le
Cam lemma); part 4. Paper-level (PM's scope decision): the `AX-09` step of part 2's lower bound,
which is taken here as its inequality.

**Laws.** `gaussianReal m v` is `N(m, v)` with `v : ℝ≥0`. `z` is the standard normal upper
`ε`-quantile when `N(0,1)(z, ∞) = ε` (`IsUpperQuantile`). A history is `n` quarterly observations
`e_j` on a probability space; `mean` is their sample mean. Laws are given by `HasLaw`, independence
across quarters by `iIndepFun`.

**Rules.** A rule is an event "buy". It certifies at `(δ, ε)` when `P(buy) ≤ ε` whenever the gap is
at most zero and `P(buy) ≥ 1 - ε` whenever the gap is at least `δ`. Each part states this for the
named rule and law class.

**Boundary hypotheses.** These are the Statement's forms after math's revision (bbe7984d), made
on leanb's report. Part 1 assumes `γ, v_i > 0`; "bought" requires `x^-_i < x̄_i` and "sold"
requires `0 < x^-_i`. Part 4's sufficient `n_eff` is `(4 c_σ σ² + 2 c_B δ B) log(C/ε)/δ²`. Part 5's
floor assumes `ε ≤ 1/2`. Part 6's ratio is stated for part 2's Gaussian rule.

**Not formalized here.** The reduction of the full M7 review to fund `i`'s one-variable problem
(the prose cites claims 030 and 104); the Gaussian conjugate update and the Kalman posterior (the
posteriors are taken as `N(mean, variance)` with the stated variances); `hang2016learning`'s
instantiations (part 4 takes its inequality (7) as the hypothesis, as the prose does).
-/

namespace Standalone.M7DataSupportActiveChange

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal

noncomputable section

/-- `z` is the standard normal upper `ε`-quantile: `N(0,1)(z, ∞) = ε`. -/
def IsUpperQuantile (ε z : ℝ) : Prop := (gaussianReal 0 1).real (Set.Ioi z) = ε

/-- The sample mean `(1/n) Σ_j e_j`. -/
def mean {n : ℕ} (e : Fin n → ℝ) : ℝ := (∑ j, e j) / n

/-! ### Part 1: the decision is the gap's sign -/

/-- Fund `i`'s one-review objective at holding `x`: `α̂ x - (γ/2) v x² - κ⁺ (x - x⁻)⁺ - κ⁻ (x⁻ - x)⁺`. -/
def obj (ah gam v kp km xm x : ℝ) : ℝ :=
  ah * x - gam / 2 * v * x ^ 2 - kp * max (x - xm) 0 - km * max (xm - x) 0

/-- The buy threshold `b_i = κ⁺ + γ v x⁻`. -/
def bThr (gam v kp xm : ℝ) : ℝ := kp + gam * v * xm

/-- The sale threshold `s_i = -κ⁻ + γ v x⁻`. -/
def sThr (gam v km xm : ℝ) : ℝ := -km + gam * v * xm

/-- `x` is optimal on `[0, x̄]`. -/
def IsOpt (ah gam v kp km xm xbar x : ℝ) : Prop :=
  x ∈ Set.Icc 0 xbar ∧ ∀ y ∈ Set.Icc 0 xbar, obj ah gam v kp km xm y ≤ obj ah gam v kp km xm x

/-- Part 1: the optimum is unique; it is above `x⁻` iff the fund is below its cap and
`Δ_i = α̂ - b_i > 0`, and below `x⁻` iff `x⁻ > 0` and `Δ^s_i = s_i - α̂ > 0`. -/
def Decision : Prop :=
  ∀ ah gam v kp km xm xbar : ℝ, 0 < gam → 0 < v → 0 ≤ kp → 0 ≤ km → 0 ≤ xm → xm ≤ xbar →
    (∃! x, IsOpt ah gam v kp km xm xbar x) ∧
    ∀ x, IsOpt ah gam v kp km xm xbar x →
      (xm < x ↔ xm < xbar ∧ 0 < ah - bThr gam v kp xm) ∧
      (x < xm ↔ 0 < xm ∧ 0 < sThr gam v km xm - ah)

/-! ### Part 2: known Gaussian law -/

/-- The known-law rule buys iff `α̂ - √v z/√n > b`. -/
def gaussBuy {Ω : Type} {n : ℕ} (e : Fin n → Ω → ℝ) (v : ℝ≥0) (z b : ℝ) : Set Ω :=
  {ω | b < mean (fun j => e j ω) - Real.sqrt v * z / Real.sqrt n}

/-- Part 2, upper bound: with residual returns `e_j` independent `N(α, v)`, the rule certifies at
`(δ, ε)` once `n ≥ 4 v z²/δ²`. The first error bound holds at every `n`. -/
def GaussSufficient : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (e : Fin n → Ω → ℝ) (α b δ ε z : ℝ) (v : ℝ≥0), 0 < n → v ≠ 0 → IsUpperQuantile ε z →
    iIndepFun e P → (∀ j, HasLaw (e j) (gaussianReal α v) P) →
    (α ≤ b → P.real (gaussBuy e v z b) ≤ ε) ∧
    (0 < δ → b + δ ≤ α → 4 * v * z ^ 2 / δ ^ 2 ≤ n → 1 - ε ≤ P.real (gaussBuy e v z b))

/-- The Bhattacharyya affinity of `N(m₁, v)` and `N(m₂, v)`: `∫ √(φ₁ φ₂)`. -/
def affinity (m₁ m₂ : ℝ) (v : ℝ≥0) : ℝ :=
  ∫ x, Real.sqrt (gaussianPDFReal m₁ v x * gaussianPDFReal m₂ v x)

/-- Part 2, the lower bound's two ingredients. The affinity of `N(b, v)` and `N(b + δ, v)` is
`exp(-δ²/(8v))`. If `AX-09`'s total-error floor `1 - √(1 - ρ^{2n})` at that affinity is at most
`2ε` (two errors each at most `ε`), then `n ≥ (4v/δ²) log(1/(4ε))` for `ε < 1/4`. The step from
"a rule on `n` Gaussian observations certifies" to the floor is `AX-09`, not machine checked here. -/
def LowerBoundArithmetic : Prop :=
  (∀ (b δ : ℝ) (v : ℝ≥0), v ≠ 0 → affinity b (b + δ) v = Real.exp (-δ ^ 2 / (8 * v))) ∧
  ∀ (δ ε : ℝ) (v : ℝ≥0) (n : ℕ), v ≠ 0 → 0 < δ → 0 < ε → ε < 1 / 4 →
    1 - Real.sqrt (1 - Real.exp (-δ ^ 2 / (8 * v)) ^ (2 * n)) ≤ 2 * ε →
    4 * v / δ ^ 2 * Real.log (1 / (4 * ε)) ≤ n

/-- Part 2: the sufficient length is at least the necessary one, `z_ε² ≥ log(1/(4ε))` for
`ε < 1/4`. -/
def QuantileOrder : Prop :=
  ∀ ε z : ℝ, 0 < ε → ε < 1 / 4 → IsUpperQuantile ε z → Real.log (1 / (4 * ε)) ≤ z ^ 2

/-- Part 2, Bayesian form: with posterior `N(m, w)`, `P(α > b) ≥ 1 - ε` iff `m - b ≥ z √w`; with
prior variance `s²` and `n` observations of variance `σ²`, `w = (1/s² + n/σ²)⁻¹ = σ²/(n + n₀)` with
`n₀ = σ²/s²`. -/
def Bayes : Prop :=
  (∀ (m b ε z : ℝ) (w : ℝ≥0), w ≠ 0 → IsUpperQuantile ε z →
    (1 - ε ≤ (gaussianReal m w).real (Set.Ioi b) ↔ z * Real.sqrt w ≤ m - b)) ∧
  ∀ (s2 sig2 : ℝ) (n : ℕ), 0 < s2 → 0 < sig2 →
    (1 / s2 + n / sig2)⁻¹ = sig2 / (n + sig2 / s2)

/-! ### Part 3: bounded residuals, unknown law -/

/-- The Hoeffding rule buys iff `α̂ - R √(2 log(1/ε)/n) > b`. -/
def hoeffBuy {Ω : Type} {n : ℕ} (e : Fin n → Ω → ℝ) (R ε b : ℝ) : Set Ω :=
  {ω | b < mean (fun j => e j ω) - R * Real.sqrt (2 * Real.log (1 / ε) / n)}

/-- Part 3, upper bound (`AX-06`, through Mathlib's Hoeffding inequality): with `e_j = α + z_j`,
the `z_j` independent, centred and bounded by `R`, the rule certifies at `(δ, ε)` once
`n ≥ 8 R² log(1/ε)/δ²`. The law of each `z_j` is otherwise unknown and need not be the same. -/
def HoeffSufficient : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (zA : Fin n → Ω → ℝ) (α R b δ ε : ℝ), 0 < n → 0 < R → 0 < ε → ε < 1 →
    iIndepFun zA P → (∀ j, Measurable (zA j)) → (∀ j ω, |zA j ω| ≤ R) → (∀ j, P[zA j] = 0) →
    (α ≤ b → P.real (hoeffBuy (fun j ω => α + zA j ω) R ε b) ≤ ε) ∧
    (0 < δ → b + δ ≤ α → 8 * R ^ 2 * Real.log (1 / ε) / δ ^ 2 ≤ n →
      1 - ε ≤ P.real (hoeffBuy (fun j ω => α + zA j ω) R ε b))

/-! ### Part 4: persistent residuals, `hang2016learning`'s benchmark -/

/-- `hang2016learning`'s (7) for `h = z` and `h = -z` at deviation `t`, with its constants
`C, c_σ, c_B`, variance bound `σ²`, bound `B` and effective sample size `n_eff`: both tails of the
residuals' sample mean `z̄` are at most `C exp(-t² n_eff/(c_σ σ² + c_B t B))`. -/
def Bernstein7 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (zbar : Ω → ℝ)
    (C cs cB s2 B neff t : ℝ) : Prop :=
  P.real {ω | t ≤ zbar ω} ≤ C * Real.exp (-(t ^ 2 * neff / (cs * s2 + cB * t * B))) ∧
  P.real {ω | t ≤ -zbar ω} ≤ C * Real.exp (-(t ^ 2 * neff / (cs * s2 + cB * t * B)))

/-- Part 4. A rule "buy iff `α + z̄ - r > b`" whose margin `r ≤ δ/2` has (7)'s
bound at `r` at most `ε` certifies at `(δ, ε)`. At `r = δ/2` that bound is at most `ε` exactly when
`n_eff ≥ (4 c_σ σ² + 2 c_B δ B) log(C/ε)/δ²`. -/
def MixingCertificate : Prop :=
  (∀ (C cs cB s2 B neff δ ε : ℝ), 0 < C → 0 < ε → 0 < δ → 0 < cs * s2 + cB * (δ / 2) * B →
    (C * Real.exp (-((δ / 2) ^ 2 * neff / (cs * s2 + cB * (δ / 2) * B))) ≤ ε ↔
      (4 * cs * s2 + 2 * cB * δ * B) * Real.log (C / ε) / δ ^ 2 ≤ neff)) ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (zbar : Ω → ℝ)
    (α b C cs cB s2 B neff r δ ε : ℝ), 0 < r → 2 * r ≤ δ →
    Bernstein7 P zbar C cs cB s2 B neff r →
    C * Real.exp (-(r ^ 2 * neff / (cs * s2 + cB * r * B))) ≤ ε →
    (α ≤ b → P.real {ω | b < α + zbar ω - r} ≤ ε) ∧
    (b + δ ≤ α → 1 - ε ≤ P.real {ω | b < α + zbar ω - r})

/-! ### Part 5: persistent alpha, a floor no history removes -/

/-- The prediction-variance map `f(p) = φ² p σ²/(σ² + p) + q`. -/
def fR (phi q s2 p : ℝ) : ℝ := phi ^ 2 * p * s2 / (s2 + p) + q

/-- The prediction variances `p_t` from `p_0`. -/
def pIter (phi q s2 p0 : ℝ) : ℕ → ℝ
  | 0 => p0
  | t + 1 => fR phi q s2 (pIter phi q s2 p0 t)

/-- The displayed root `p_∞ = [(q - σ²(1-φ²)) + √((q - σ²(1-φ²))² + 4 q σ²)]/2`. -/
def pInf (phi q s2 : ℝ) : ℝ :=
  ((q - s2 * (1 - phi ^ 2)) + Real.sqrt ((q - s2 * (1 - phi ^ 2)) ^ 2 + 4 * q * s2)) / 2

/-- Part 5, the filter: `p_∞ > 0` is the unique nonnegative fixed point of `f`; M5's stationary
prior `q/(1 - φ²)` is at least `p_∞`; from any `p_0 ≥ p_∞` the iterates decrease to `p_∞` and never
go below it. -/
def Riccati : Prop :=
  ∀ phi q s2 : ℝ, |phi| < 1 → 0 < q → 0 < s2 →
    0 < pInf phi q s2 ∧ fR phi q s2 (pInf phi q s2) = pInf phi q s2 ∧
    (∀ p, 0 ≤ p → fR phi q s2 p = p → p = pInf phi q s2) ∧
    pInf phi q s2 ≤ q / (1 - phi ^ 2) ∧
    ∀ p0, pInf phi q s2 ≤ p0 →
      Antitone (pIter phi q s2 p0) ∧ (∀ t, pInf phi q s2 ≤ pIter phi q s2 p0 t) ∧
      Tendsto (pIter phi q s2 p0) atTop (𝓝 (pInf phi q s2))

/-- Part 5, the floor: with posterior `N(m, p)` of the current alpha and `p ≥ p_∞`, the posterior
probability of `α > b` is at most its value at `p_∞` when `m > b`, and a buy is certified at
posterior confidence `1 - ε` (`ε ≤ 1/2`) only if `m - b ≥ z_ε √p_∞`. -/
def Floor : Prop :=
  ∀ (m b ε z pinf : ℝ) (p : ℝ≥0), 0 < pinf → pinf ≤ p → IsUpperQuantile ε z → ε ≤ 1 / 2 →
    (b < m → (gaussianReal m p).real (Set.Ioi b) ≤ (gaussianReal m pinf.toNNReal).real (Set.Ioi b)) ∧
    (1 - ε ≤ (gaussianReal m p).real (Set.Ioi b) → z * Real.sqrt pinf ≤ m - b)

/-- Part 5, the limits: `p_∞ → 0` as `q → 0`; `p_∞` is nondecreasing in `σ²` and tends to
`q/(1 - φ²)` as `σ² → ∞`. -/
def Limits : Prop :=
  ∀ phi : ℝ, |phi| < 1 →
    (∀ s2 : ℝ, 0 < s2 → Tendsto (fun q => pInf phi q s2) (𝓝 0) (𝓝 0)) ∧
    ∀ q : ℝ, 0 < q →
      MonotoneOn (fun s2 => pInf phi q s2) (Set.Ioi 0) ∧
      Tendsto (fun s2 => pInf phi q s2) atTop (𝓝 (q / (1 - phi ^ 2)))

/-! ### Part 6: spanning decides whether premium error enters -/

/-- Part 6: each quarter the fund's residual `z_j ~ N(0, σ²)` and the factor return
`f_j ~ N(λ, Σ_f)` are independent, and quarters are independent. The decision quantity
`α + w'λ` (with `w = J (B^A_i)'`) is estimated from `u_j = α + z_j + w' f_j`, whose law is
`N(α + w'λ, σ² + w'Σ_f w)`. The part 2 rule with that variance certifies the gap `α + w'λ - b` at
`(δ, ε)` once `n ≥ (1 + w'Σ_f w/σ²) · 4σ² z²/δ²`. With spanning, `w = 0` and the ratio is one. -/
def Spanning : Prop :=
  ∀ (K : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (zA : Fin n → Ω → ℝ) (f : Fin n → Ω → EuclideanSpace ℝ (Fin K))
    (lam w : EuclideanSpace ℝ (Fin K)) (Sf : Matrix (Fin K) (Fin K) ℝ) (α b δ ε z : ℝ) (s2 : ℝ≥0),
    0 < n → s2 ≠ 0 → Sf.PosSemidef → IsUpperQuantile ε z →
    iIndepFun (fun j ω => (zA j ω, f j ω)) P → (∀ j, IndepFun (zA j) (f j) P) →
    (∀ j, HasLaw (zA j) (gaussianReal 0 s2) P) → (∀ j, HasLaw (f j) (multivariateGaussian lam Sf) P) →
    let tau := w ⬝ᵥ Sf *ᵥ w
    let u : Fin n → Ω → ℝ := fun j ω => α + zA j ω + inner ℝ w (f j ω)
    let vU : ℝ≥0 := s2 + tau.toNNReal
    0 ≤ tau ∧
    (∀ j, HasLaw (u j) (gaussianReal (α + inner ℝ w lam) vU) P) ∧
    (α + inner ℝ w lam ≤ b → P.real (gaussBuy u vU z b) ≤ ε) ∧
    (0 < δ → b + δ ≤ α + inner ℝ w lam → (1 + tau / s2) * (4 * s2 * z ^ 2 / δ ^ 2) ≤ n →
      1 - ε ≤ P.real (gaussBuy u vU z b)) ∧
    (w = 0 → 1 + tau / s2 = 1)

/-! ### Part 7: a pooled prior makes a common tilt cheaper by the factor `N` -/

/-- Part 7, the posterior: under claim 032's pooled posterior `P^α_t`, the average alpha
`(1/N) 1'α` has variance `(1/N²) 1' P^α_t 1 = p^c_t/N` with `1/p^c_t = 1/(s² + N s̄²) + t/σ²`, and a
relative direction `u ⊥ 1` has variance `p^r_t |u|²`, the single-fund rate. -/
def PooledVariance : Prop :=
  ∀ (N : ℕ) (s2 sb2 sig2 : ℝ) (t : ℕ), 0 < N → 0 < s2 → 0 ≤ sb2 → 0 < sig2 →
    (1 / (N : ℝ) ^ 2) * (1 ⬝ᵥ (Standalone.M5LearningAimTwoSpeeds.postA N s2 sb2 sig2 t).mulVec 1)
      = Standalone.M5LearningAimTwoSpeeds.pc N s2 sb2 sig2 t / N ∧
    Standalone.M5LearningAimTwoSpeeds.pc N s2 sb2 sig2 t = (1 / (s2 + N * sb2) + t / sig2)⁻¹ ∧
    ∀ u : Fin N → ℝ, 1 ⬝ᵥ u = 0 →
      u ⬝ᵥ (Standalone.M5LearningAimTwoSpeeds.postA N s2 sb2 sig2 t).mulVec u
        = Standalone.M5LearningAimTwoSpeeds.pr s2 sig2 t * (u ⬝ᵥ u)

/-- Part 7, the rate: with `N` funds whose residual returns `e_{j,i}` are independent `N(α_i, σ²)`
(independent across quarters `j` and funds `i`), the part 2 rule applied to the average
`ē_j = (1/N) Σ_i e_{j,i}` with variance `σ²/N` certifies the average alpha's gap
`(1/N) Σ_i α_i - b` at `(δ, ε)` once `n ≥ (1/N) · 4σ² z²/δ²`, `N` times shorter than one fund. -/
def CommonTilt : Prop :=
  ∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (e : Fin n → Ω → (Fin N → ℝ)) (α : Fin N → ℝ) (b δ ε z : ℝ) (s2 : ℝ≥0),
    0 < N → 0 < n → s2 ≠ 0 → IsUpperQuantile ε z →
    iIndepFun e P → (∀ j, iIndepFun (fun i ω => e j ω i) P) →
    (∀ j i, HasLaw (fun ω => e j ω i) (gaussianReal (α i) s2) P) →
    let ebar : Fin n → Ω → ℝ := fun j ω => (∑ i, e j ω i) / N
    let abar : ℝ := (∑ i, α i) / N
    let vbar : ℝ≥0 := s2 / (N : ℝ≥0)
    (∀ j, HasLaw (ebar j) (gaussianReal abar vbar) P) ∧
    (abar ≤ b → P.real (gaussBuy ebar vbar z b) ≤ ε) ∧
    (0 < δ → b + δ ≤ abar → (1 / (N : ℝ)) * (4 * s2 * z ^ 2 / δ ^ 2) ≤ n →
      1 - ε ≤ P.real (gaussBuy ebar vbar z b))

/-! ### Part 3's lower bound: the two-point law -/

/-- A finite law in `B_R`: masses `q ≥ 0` summing to one and residuals `Z` with `|Z| ≤ R` and mean
zero. -/
def InBR {S : Type} [Fintype S] (R : ℝ) (q Z : S → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧ ∑ s, q s * Z s = 0 ∧ ∀ s, |Z s| ≤ R

/-- The probability that a rule `φ` (a buy probability for each history) buys, when the `n`
residual returns `e_j = α + Z_{σ_j}` are iid from the law `(q, Z)`. -/
def buyProb {S : Type} [Fintype S] (n : ℕ) (q Z : S → ℝ) (α : ℝ) (φ : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ σ : Fin n → S, (∏ j, q (σ j)) * φ (fun j => α + Z (σ j))

/-- Part 3, lower bound: a rule that certifies at `(δ, ε)` for every finite law in `B_R` and every
alpha needs `n ≥ (R²/δ²) log(1/ε)`, for `0 < δ ≤ R/2` and `ε ≤ 1/16`. This is the claim's universal
constant `c`, here `c = 1`. The rule may be randomized. -/
def TwoPointLower : Prop :=
  ∀ (n : ℕ) (R b δ ε : ℝ) (φ : (Fin n → ℝ) → ℝ), 0 < δ → δ ≤ R / 2 → 0 < ε → ε ≤ 1 / 16 →
    (∀ h, 0 ≤ φ h ∧ φ h ≤ 1) →
    (∀ (S : Type) [Fintype S] (q Z : S → ℝ), InBR R q Z → ∀ α : ℝ,
      (α ≤ b → buyProb n q Z α φ ≤ ε) ∧ (b + δ ≤ α → 1 - ε ≤ buyProb n q Z α φ)) →
    R ^ 2 / δ ^ 2 * Real.log (1 / ε) ≤ n

/-- Claim 039. -/
def statement : Prop :=
  Decision ∧ GaussSufficient ∧ LowerBoundArithmetic ∧ QuantileOrder ∧ Bayes ∧ HoeffSufficient ∧
    MixingCertificate ∧ Riccati ∧ Floor ∧ Limits ∧ Spanning ∧ PooledVariance ∧ CommonTilt ∧
    TwoPointLower

end

end Standalone.M7DataSupportActiveChange

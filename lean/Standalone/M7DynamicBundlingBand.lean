import Standalone.M6QuarterlyBandStaticCeiling

/-!
# Claim 107: the dynamic bundling band

Statement only; the proof is `Novel/M7DynamicBundlingBandProof.lean`.

The objects are claim 029's slack-budget M6 instance with review- and state-dependent covariance
`Sigma t z`, which is how claim 100 reads M7 (`Standalone/M6QuarterlyBandStaticCeiling.lean`). There
are `M + 1` instruments: the fund is index `0` and ETF `j` is index `j.succ`.
- `join a p` is the holding with fund `a` and ETFs `p`. `ebox` is the ETF box, `costA` the fund's
  trade cost and `costE` the ETFs'.
- `Fe t z p⁻ a p = G_t(join a p) + C_E(p - p⁻)` and `U t z p⁻ a = inf_{p ∈ ebox} Fe`, the
  ETF-optimized value.
- `rho = Σ_EE⁻¹ Σ_EA` are the hedge ratios, `s2res = Σ_AA - Σ_AE Σ_EE⁻¹ Σ_EA` the fund's residual
  variance given the ETFs, and `cres = γ s2res`.
- `Hplus` and `Hminus` are the leak bounds, with `gb t z i = Σ_ω q g'_i` the expected gross returns.
- `loF`/`hiF` are claim 029's edge definitions for a general function. The effective band is
  `loU = loF (U ...)` and `hiU = hiF (U ...)`, and claim 029's `lo`/`hi` are `loF`/`hiF` of `G1`.
- The fund's own target coordinate `a*_t` is `xstar P t z 0`.

Part 2's diameter is claim 029's part 2b, which claim 100 reads for review-dependent covariance; it
is not restated here.

Part 3's hypothesis is the Statement's (mathb's revision, 8ad1c249): the hedge `x*_E - rho (a - a*)`
lies in the ETF box for every fund holding `a` in `[0, x̄_A]`, at every review and state, not only
at optimal holdings. That is what the prose proof uses. Frictionless, residual-free, fee-free and spanning enter the formal model only as
zero ETF rates. Reading `a*` as claim 104's reduced target is prose.
-/

namespace Standalone.M7DynamicBundlingBand

open Matrix Standalone.M6QuarterlyBandStaticCeiling
open scoped Classical

noncomputable section

variable {M : ℕ} {Z Ω : Type} [Fintype Ω]

/-- The holding with fund `a` and ETFs `p`. -/
def join (a : ℝ) (p : Fin M → ℝ) : Fin (M + 1) → ℝ := Fin.cons a p

/-- The ETF box. -/
def ebox (P : M6 (M + 1) Z Ω) : Set (Fin M → ℝ) := {p | ∀ j, 0 ≤ p j ∧ p j ≤ P.cap j.succ}

/-- The fund's trade cost `C_A(u)`. -/
def costA (P : M6 (M + 1) Z Ω) (u : ℝ) : ℝ := P.kp 0 * max u 0 + P.km 0 * max (-u) 0

/-- The ETFs' trade cost `C_E(u)`. -/
def costE (P : M6 (M + 1) Z Ω) (u : Fin M → ℝ) : ℝ :=
  ∑ j, (P.kp j.succ * max (u j) 0 + P.km j.succ * max (-u j) 0)

/-- `Fe = G_t(join a p) + C_E(p - p⁻)`. -/
def Fe (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (pm : Fin M → ℝ) (a : ℝ) (p : Fin M → ℝ) : ℝ :=
  G P t z (join a p) + costE P (p - pm)

/-- The ETF-optimized value `U_t(a; p⁻) = min_{p ∈ ebox} Fe`. -/
def U (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (pm : Fin M → ℝ) (a : ℝ) : ℝ :=
  sInf (Fe P t z pm a '' ebox P)

/-- `Σ_EE`. -/
def SEE (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => P.Sigma t z i.succ j.succ

/-- `Σ_EA`. -/
def SEA (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : Fin M → ℝ := fun j => P.Sigma t z j.succ 0

/-- The hedge ratios `ρ = Σ_EE⁻¹ Σ_EA`. -/
def rho (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : Fin M → ℝ := (SEE P t z)⁻¹ *ᵥ SEA P t z

/-- The residual variance `σ²_{A.E} = Σ_AA - Σ_AE Σ_EE⁻¹ Σ_EA`. -/
def s2res (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.Sigma t z 0 0 - SEA P t z ⬝ᵥ rho P t z

/-- The residual curvature `c^res = γ σ²_{A.E}`. -/
def cres (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.gamma * s2res P t z

/-- The expected gross return `ḡ_i = Σ_ω q g'_i`. -/
def gb {n : ℕ} (P : M6 n Z Ω) (t : ℕ) (z : Z) (i : Fin n) : ℝ := ∑ ω, P.prob t z ω * P.gross ω i

/-- `H⁺ = Σ_j [ρ_j⁺ (κ⁺_j + β κ⁻_j ḡ_j) + ρ_j⁻ (κ⁻_j + β κ⁺_j ḡ_j)]`. -/
def Hplus (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  ∑ j, (max (rho P t z j) 0 * (P.kp j.succ + P.beta * P.km j.succ * gb P t z j.succ) +
    max (-rho P t z j) 0 * (P.km j.succ + P.beta * P.kp j.succ * gb P t z j.succ))

/-- `H⁻ = Σ_j [ρ_j⁺ (κ⁻_j + β κ⁺_j ḡ_j) + ρ_j⁻ (κ⁺_j + β κ⁻_j ḡ_j)]`. -/
def Hminus (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  ∑ j, (max (rho P t z j) 0 * (P.km j.succ + P.beta * P.kp j.succ * gb P t z j.succ) +
    max (-rho P t z j) 0 * (P.kp j.succ + P.beta * P.km j.succ * gb P t z j.succ))

/-- Claim 029's lower edge for a function `f`: `inf {x ∈ [0, x̄) : f'_+(x) ≥ -κ⁺}` (`x̄` if empty). -/
def loF (f : ℝ → ℝ) (kp cap : ℝ) : ℝ :=
  if ({x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} : Set ℝ).Nonempty then
    sInf {x | 0 ≤ x ∧ x < cap ∧ -kp ≤ rd f x} else cap

/-- Claim 029's upper edge for a function `f`: `sup {x ∈ (0, x̄] : f'_-(x) ≤ κ⁻}` (`0` if empty). -/
def hiF (f : ℝ → ℝ) (km cap : ℝ) : ℝ :=
  if ({x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} : Set ℝ).Nonempty then
    sSup {x | 0 < x ∧ x ≤ cap ∧ ld f x ≤ km} else 0

/-- The fund's effective lower edge. -/
def loU (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (pm : Fin M → ℝ) : ℝ :=
  loF (U P t z pm) (P.kp 0) (P.cap 0)

/-- The fund's effective upper edge. -/
def hiU (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (pm : Fin M → ℝ) : ℝ :=
  hiF (U P t z pm) (P.km 0) (P.cap 0)

/-- `p` is interior to the ETF box. -/
def Interior (P : M6 (M + 1) Z Ω) (p : Fin M → ℝ) : Prop := ∀ j, 0 < p j ∧ p j < P.cap j.succ

/-- `c` is a cost slope in the trade-sign set of a trade `u` at rates `κ⁺, κ⁻`. -/
def TradeSign (kp km u c : ℝ) : Prop :=
  (0 < u → c = kp) ∧ (u < 0 → c = -km) ∧ -km ≤ c ∧ c ≤ kp

/-- Part 1a: `U_t` is continuous and `U_t - (c^res/2)a²` convex, with `c^res > 0`. The full
optimum is the fund problem on `U_t` followed by the ETF problem. The fund's post-trade holding is
the clip of `a⁻` to `[lo_U, hi_U] ⊆ [0, x̄_A]`, and the fund is held iff `a⁻` lies in it. -/
def EffectiveBand : Prop :=
  ∀ (M : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 (M + 1) Z Ω), Setting P → ∀ t z, t < P.T →
    ∀ pm : Fin M → ℝ,
      0 < cres P t z ∧ Continuous (U P t z pm) ∧
      ConvexOn ℝ Set.univ (fun a => U P t z pm a - cres P t z / 2 * a ^ 2) ∧
      0 ≤ loU P t z pm ∧ loU P t z pm ≤ hiU P t z pm ∧ hiU P t z pm ≤ P.cap 0 ∧
      ∀ (am : ℝ) (a : ℝ) (p : Fin M → ℝ),
        (IsOpt P t z (join am pm) (join a p) ↔
          (0 ≤ a ∧ a ≤ P.cap 0 ∧
            ∀ b, 0 ≤ b → b ≤ P.cap 0 → costA P (a - am) + U P t z pm a ≤ costA P (b - am) + U P t z pm b) ∧
          p ∈ ebox P ∧ ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q) ∧
        (IsOpt P t z (join am pm) (join a p) →
          a = min (max am (loU P t z pm)) (hiU P t z pm) ∧
          (a = am ↔ loU P t z pm ≤ am ∧ am ≤ hiU P t z pm))

/-- Part 1b: the static ceiling with the residual curvature. -/
def ResidualCeiling : Prop :=
  ∀ (M : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 (M + 1) Z Ω), Setting P → ∀ t z, t < P.T →
    ∀ pm : Fin M → ℝ, hiU P t z pm - loU P t z pm ≤ (P.kp 0 + P.km 0) / cres P t z

/-- Part 1c: the outer bracket. At an edge above zero (below the cap) whose ETF optimizer `p` is
interior to the ETF box, the edge is within `(κ⁻_A + βκ⁺_A ḡ_A + H⁺)/c^res` above (within
`(κ⁺_A + βκ⁻_A ḡ_A + H⁻)/c^res` below) the fund's target coordinate. -/
def OuterBracket : Prop :=
  ∀ (M : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 (M + 1) Z Ω), Setting P → ∀ t z, t < P.T →
    ∀ pm p : Fin M → ℝ,
      (0 < hiU P t z pm → p ∈ ebox P → Interior P p →
        (∀ q ∈ ebox P, Fe P t z pm (hiU P t z pm) p ≤ Fe P t z pm (hiU P t z pm) q) →
        hiU P t z pm ≤ xstar P t z 0 +
          (P.km 0 + P.beta * P.kp 0 * gb P t z 0 + Hplus P t z) / cres P t z) ∧
      (loU P t z pm < P.cap 0 → p ∈ ebox P → Interior P p →
        (∀ q ∈ ebox P, Fe P t z pm (loU P t z pm) p ≤ Fe P t z pm (loU P t z pm) q) →
        xstar P t z 0 - (P.kp 0 + P.beta * P.km 0 * gb P t z 0 + Hminus P t z) / cres P t z ≤
          loU P t z pm)

/-- Part 1d: at `T - 1`, with an edge interior to the fund's box and its ETF optimizer `p`
interior, the edge is exact with ETF slopes `c_E` in the trade-sign sets of `p - p⁻`:
`c^res (hi - a*) = κ⁻_A + ρ'c_E` and `c^res (lo - a*) = -κ⁺_A + ρ'c_E`. The regimes, for an interior
band: equal slopes at both edges give the ceiling width; every ETF re-hedged in opposite
directions at the two edges gives the ceiling minus the leak; ETFs untraded at both edges give the
fund-alone width `(κ⁺_A + κ⁻_A)/(γ Σ_AA)`, for any number of ETFs and with no interiority of the
ETF optimizer. For every interior band the width is at least the fund-alone width (with 1b's
ceiling, the width lies between the two). -/
def LastReview : Prop :=
  ∀ (M : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 (M + 1) Z Ω), Setting P → ∀ z pm,
    let t := P.T - 1
    let IsEOpt := fun (a : ℝ) (p : Fin M → ℝ) => p ∈ ebox P ∧ ∀ q ∈ ebox P, Fe P t z pm a p ≤ Fe P t z pm a q
    (∀ p, 0 < hiU P t z pm → hiU P t z pm < P.cap 0 → IsEOpt (hiU P t z pm) p → Interior P p →
      ∃ c : Fin M → ℝ, (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (p j - pm j) (c j)) ∧
        cres P t z * (hiU P t z pm - xstar P t z 0) = P.km 0 + rho P t z ⬝ᵥ c) ∧
    (∀ p, 0 < loU P t z pm → loU P t z pm < P.cap 0 → IsEOpt (loU P t z pm) p → Interior P p →
      ∃ c : Fin M → ℝ, (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (p j - pm j) (c j)) ∧
        cres P t z * (loU P t z pm - xstar P t z 0) = -P.kp 0 + rho P t z ⬝ᵥ c) ∧
    (∀ ph pl, 0 < loU P t z pm → hiU P t z pm < P.cap 0 →
      IsEOpt (hiU P t z pm) ph → IsEOpt (loU P t z pm) pl → Interior P ph → Interior P pl →
      ∃ ch cl : Fin M → ℝ,
        (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (ph j - pm j) (ch j)) ∧
        (∀ j, TradeSign (P.kp j.succ) (P.km j.succ) (pl j - pm j) (cl j)) ∧
        cres P t z * (hiU P t z pm - loU P t z pm) = P.kp 0 + P.km 0 + rho P t z ⬝ᵥ (ch - cl) ∧
        (ch = cl → hiU P t z pm - loU P t z pm = (P.kp 0 + P.km 0) / cres P t z) ∧
        ((∀ j, (0 < rho P t z j → ph j < pm j ∧ pm j < pl j) ∧
            (rho P t z j < 0 → pm j < ph j ∧ pl j < pm j)) →
          hiU P t z pm - loU P t z pm = (P.kp 0 + P.km 0 -
            ∑ j, |rho P t z j| * (P.kp j.succ + P.km j.succ)) / cres P t z)) ∧
    (0 < loU P t z pm → hiU P t z pm < P.cap 0 → IsEOpt (hiU P t z pm) pm → IsEOpt (loU P t z pm) pm →
      hiU P t z pm - loU P t z pm = (P.kp 0 + P.km 0) / (P.gamma * P.Sigma t z 0 0)) ∧
    (∀ ph pl, 0 < loU P t z pm → hiU P t z pm < P.cap 0 → IsEOpt (hiU P t z pm) ph →
      IsEOpt (loU P t z pm) pl →
      (P.kp 0 + P.km 0) / (P.gamma * P.Sigma t z 0 0) ≤ hiU P t z pm - loU P t z pm)

/-- Part 2: at a no-trade holding strictly inside the box,
`γ Σ_t (x - x*_t)` lies in `∏_i [-(κ⁺_i + βκ⁻_i ḡ_i), κ⁻_i + βκ⁺_i ḡ_i]`. -/
def OuterParallelotope : Prop :=
  ∀ (n : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 n Z Ω), Setting P → ∀ t z, t < P.T →
    ∀ x ∈ NT P t z, (∀ i, 0 < x i ∧ x i < P.cap i) → ∀ i,
      -(P.kp i + P.beta * P.km i * gb P t z i) ≤ P.gamma * (P.Sigma t z *ᵥ (x - xstar P t z)) i ∧
      P.gamma * (P.Sigma t z *ᵥ (x - xstar P t z)) i ≤ P.km i + P.beta * P.kp i * gb P t z i

/-- The hedge `x*_E - ρ (a - a*)`. -/
def hedge (P : M6 (M + 1) Z Ω) (t : ℕ) (z : Z) (a : ℝ) : Fin M → ℝ :=
  fun j => xstar P t z j.succ - rho P t z j * (a - xstar P t z 0)

/-- The fund's reduced one-instrument instance: curvature `γ σ²_{A.E}`, target `a*`, the fund's
rates, cap and gross returns. -/
def reduced (P : M6 (M + 1) Z Ω) : M6 1 Z Ω where
  T := P.T
  mu t z := fun _ => P.gamma * s2res P t z * xstar P t z 0
  Sigma t z := fun _ _ => s2res P t z
  gamma := P.gamma
  beta := P.beta
  kp := fun _ => P.kp 0
  km := fun _ => P.km 0
  cap := fun _ => P.cap 0
  prob := P.prob
  next := P.next
  gross ω := fun _ => P.gross ω 0

/-- Part 3: with frictionless ETFs whose hedge stays in the ETF box, the reduced instance is an
M6 instance with target `a*`. At every review `U_t` is its `G_t` plus a constant on `[0, x̄_A]`, for
every ETF incumbent. The effective band is its one-instrument band (claims 029 and 100), and
`V_t` is its value plus a constant. -/
def Frictionless : Prop :=
  ∀ (M : ℕ) (Z Ω : Type) [Fintype Ω] (P : M6 (M + 1) Z Ω), Setting P →
    (∀ j : Fin M, P.kp j.succ = 0 ∧ P.km j.succ = 0) →
    (∀ t z, t < P.T → ∀ a, 0 ≤ a → a ≤ P.cap 0 → hedge P t z a ∈ ebox P) →
    Setting (reduced P) ∧ (∀ t z, xstar (reduced P) t z 0 = xstar P t z 0) ∧
    ∀ t z, t < P.T →
      (∃ K : ℝ, ∀ x : Fin (M + 1) → ℝ, V P t z x = V1 (reduced P) t z (x 0) + K) ∧
      (∃ K : ℝ, ∀ pm : Fin M → ℝ, ∀ a, 0 ≤ a → a ≤ P.cap 0 →
        U P t z pm a = G1 (reduced P) t z a + K) ∧
      ∀ pm : Fin M → ℝ, loU P t z pm = lo (reduced P) t z ∧ hiU P t z pm = hi (reduced P) t z

/-- Claim 107, parts 1-3. -/
def statement : Prop :=
  EffectiveBand ∧ ResidualCeiling ∧ OuterBracket ∧ LastReview ∧ OuterParallelotope ∧ Frictionless

end

end Standalone.M7DynamicBundlingBand

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Standalone.M4BoundedLawRate

/-!
# Claim 016: joint directional information against a moving ETF comparator

Statement only; the proof is `Novel/M4JointDirectionalRateProof.lean`.

The formal M4 objects are those of `Standalone/M4InformationObstruction.lean`, which include
`Rule`, `Cset`, `LN`, `wHatF`, `vHatE`, `tcrit`, `Omega`, `thetaHat`, `hist` and `mass`. The
requirement predicates `falseP`, `powerP` and `Meets` (certify with `Adv ≤ δ/4` at most `ε`;
certify with `Adv > δ/4` at least `1 - ε` wherever `G_* ≥ δ`) are those of claim 015.

**The family.**
- One active fund and one ETF, `B^A = (1, 0)`, `B^E = (0, 1)`, zero costs and drag, `γ = 0`, caps
  one, and zero risky holdings with cash one.
- `θ = (λ₁, λ₂, α)`. `J` is a real `3 × 3` matrix with Euclidean operator norm at most `1/100`,
  written `SmallJ` as `‖J v‖² ≤ (1/100)² ‖v‖²` for every `v`.
- `Θ₄ = conv{c_j + J v : j ∈ {0, 1}, v ∈ {±1}³}`.
- A law in `K_J` is a finite scenario type with masses `q ≥ 0` summing to one and `U ∈ ℝ³` with
  `E U = 0`, `E U U' = I₃` and `‖U‖ ≤ 9` at every scenario. The M4 shocks are
  `(z^f₁, z^f₂, z^A) = J U` and `z^E = 0`.
- `d₀ = (1, 0, 1)`, `d₁ = (1, -1, 1)`, `σ_j² = d_j' Ω d_j` with `Ω = J J'`, and
  `σ = max(σ₀, σ₁)`.

The operator-norm bound is needed only for admissibility (Part 1) and the lower bound. The upper
bound, the directional certificate and the doubly degenerate benchmark are stated for every `J`.

**Rules.** A rule either certifies a funded active action (`a > 0`) or falls back to a funded
ETF-only action. The constructive rule is M4's gate: `C_N` with `η = ε`, the plug-in optimizer,
M4's plug-in fallback `v̂_E`, and the directional certificate
`ℓ_N = min_j [d_j' θ̂ - r_N σ_j]` with `r_N = √(t_{N,ε}/N)`, certifying above `δ/4`.
-/

namespace Standalone.M4JointDirectionalRate

open Matrix MeasureTheory Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
  Standalone.M4BoundedLawRate
open scoped Classical

noncomputable section

/-- `‖J v‖ ≤ ‖v‖/100` for every `v` (Euclidean operator norm at most `1/100`). -/
def SmallJ (J : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ v : Fin 3 → ℝ, (J *ᵥ v) ⬝ᵥ (J *ᵥ v) ≤ (1 / 100) ^ 2 * (v ⬝ᵥ v)

/-- `c₀ = (0, -1/4, 0)`. -/
def c0 : Fin 3 → ℝ := ![0, -1 / 4, 0]

/-- `c₁ = (0, 1/4, 1/4)`. -/
def c1 : Fin 3 → ℝ := ![0, 1 / 4, 1 / 4]

/-- `d₀ = (1, 0, 1)`: `w_A` against cash. -/
def d0 : Fin 3 → ℝ := ![1, 0, 1]

/-- `d₁ = (1, -1, 1)`: `w_A` against the ETF. -/
def d1 : Fin 3 → ℝ := ![1, -1, 1]

/-- The vertices `c_j + J v`, `v ∈ {±1}³`. -/
def V4 (J : Matrix (Fin 3) (Fin 3) ℝ) : Finset (Fin 3 → ℝ) :=
  Finset.univ.image fun p : Bool × (Fin 3 → Bool) =>
    (if p.1 then c1 else c0) + J *ᵥ fun i => if p.2 i then 1 else -1

/-- `σ_d² = d' Ω d`, `Ω = J J'`. -/
def sig2 (J : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) : ℝ := d ⬝ᵥ ((J * Jᵀ) *ᵥ d)

/-- `σ = max(σ₀, σ₁)`. -/
def sigma (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  max (Real.sqrt (sig2 J d0)) (Real.sqrt (sig2 J d1))

/-- A law in `K_J`: `E U = 0`, `E U U' = I₃` and `‖U‖ ≤ 9`. -/
def InKJ {S : Type} [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧ (∀ i, ∑ s, q s * U s i = 0) ∧
  (∀ i k, ∑ s, q s * (U s i * U s k) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) ∧
  ∀ s, U s ⬝ᵥ U s ≤ 81

/-- The M4 data for the law `(q, U)`: `(z^f₁, z^f₂, z^A) = J U`, `z^E = 0`. -/
def data (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} (q : S → ℝ) (U : S → Fin 3 → ℝ) :
    Data 1 1 2 S where
  BA := !![1, 0]
  BE := !![0, 1]
  cE := 0
  kplus := 0
  kminus := 0
  gamma := 0
  q := q
  zf := fun s => ![(J *ᵥ U s) 0, (J *ᵥ U s) 1]
  zA := fun s => ![(J *ᵥ U s) 2]
  zE := 0
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- `w_A = (1, 0)`. -/
def wA : Inst 1 1 → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- The all-ETF action `(0, 1)`. -/
def etf1 : Inst 1 1 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The rule either certifies a funded active action or falls back to a funded ETF-only action. -/
def AdmitsJ {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ} (ρ : Rule N) : Prop :=
  ∀ H, ρ.kernel H {w | ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0)) ∧ w ∉ E D} = 0

/-- `r_N = √(t_{N,ε}/N)`. -/
def rN {S : Type} [Fintype S] (D : Data 1 1 2 S) (N : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt (tcrit D N ε / N)

/-- The directional certificate `ℓ_N(w_A) = min_j [d_j' θ̂ - r_N σ_j]`. -/
def ellJ (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ}
    (ε : ℝ) (H : Fin N → Record 1) : ℝ :=
  min (d0 ⬝ᵥ thetaHat D H - rN D N ε * Real.sqrt (sig2 J d0))
    (d1 ⬝ᵥ thetaHat D H - rN D N ε * Real.sqrt (sig2 J d1))

/-- The gate certifies: `C_N` nonempty, plug-in optimizer `w_A`, and `ℓ_N > δ/4`. -/
def certJ (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) {N : ℕ}
    (δ ε : ℝ) (H : Fin N → Record 1) : Prop :=
  (Cset D (V4 J) N ε (thetaHat D H)).Nonempty ∧ wHatF D (thetaHat D H) = wA ∧
    δ / 4 < ellJ J D ε H

/-- The gate as a rule: certify `w_A`, else M4's plug-in fallback `v̂_E`. -/
def gateJ (J : Matrix (Fin 3) (Fin 3) ℝ) {S : Type} [Fintype S] (D : Data 1 1 2 S) (N : ℕ)
    (δ ε : ℝ) : Rule N where
  kernel H := Measure.dirac (if certJ J D δ ε H then wA else vHatE D (thetaHat D H))
  isProb _ := inferInstance

/-- Part 1: admissibility, `Ω` of M4 equals `J J'`, the classes and score, the moving ETF optimum,
the two contrasts, and the paired errors with covariance `Ω/N`. -/
def Contrasts : Prop :=
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, SmallJ J →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      M4Admissible (data J q U) (V4 J) ∧ Omega (data J q U) = J * Jᵀ ∧
      F (data J q U) = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧
        w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} ∧
      E (data J q U) = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} ∧
      (∀ w θ, score (data J q U) w (toPar θ) = w (Sum.inl 0) * (θ 0 + θ 2) + w (Sum.inr 0) * θ 1) ∧
      (∀ θ, etfSup (data J q U) θ = max 0 (θ 1)) ∧
      (∀ θ, θ 1 < 0 → maximizers (fun v => score (data J q U) v (toPar θ)) (E (data J q U)) = {0}) ∧
      (∀ θ, 0 < θ 1 →
        maximizers (fun v => score (data J q U) v (toPar θ)) (E (data J q U)) = {etf1}) ∧
      (∃ θ ∈ Theta4 (V4 J), θ 1 < 0) ∧ (∃ θ ∈ Theta4 (V4 J), 0 < θ 1) ∧
      (∀ θ, Adv (data J q U) wA θ = min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ)) ∧
      (∀ θ, Gstar (data J q U) θ = max 0 (min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ))) ∧
      (∀ θ, 0 < min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) →
        maximizers (fun w => score (data J q U) w (toPar θ)) (F (data J q U)) = {wA}) ∧
      (∀ θ, min (d0 ⬝ᵥ θ) (d1 ⬝ᵥ θ) < 0 → ∀ w ∈ F (data J q U), 0 < w (Sum.inl 0) →
        Adv (data J q U) w θ < 0) ∧
      d0 0 ≠ 0 ∧ d0 2 ≠ 0 ∧ d1 0 ≠ 0 ∧ d1 2 ≠ 0 ∧
      (∀ θ θ', (score (data J q U) wA (toPar θ') - score (data J q U) 0 (toPar θ'))
        - (score (data J q U) wA (toPar θ) - score (data J q U) 0 (toPar θ)) = d0 ⬝ᵥ (θ' - θ)) ∧
      (∀ θ θ', (score (data J q U) wA (toPar θ') - score (data J q U) etf1 (toPar θ'))
        - (score (data J q U) wA (toPar θ) - score (data J q U) etf1 (toPar θ)) = d1 ⬝ᵥ (θ' - θ)) ∧
      ∀ θ (N : ℕ), 0 < N → ∀ i k, ∑ σ : Fin N → S, mass (data J q U) σ *
        ((thetaHat (data J q U) (hist (data J q U) θ σ) - θ) i *
          (thetaHat (data J q U) (hist (data J q U) θ σ) - θ) k) = (J * Jᵀ) i k / N

/-- Part 2, lower bound: if at length `N_obs` every law in `K_J` admits a rule meeting both
requirements, then `N_obs ≥ σ² log(1/ε)/(16π² δ²)`. -/
def LowerBound : Prop :=
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, SmallJ J → ∀ δ ε : ℝ, 0 < δ → δ ≤ sigma J / 8 → 0 < ε →
    ε ≤ 1 / 16 → ∀ N : ℕ, 0 < N →
      (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
        ∃ ρ : Rule N, AdmitsJ (data J q U) ρ ∧ Meets (data J q U) (V4 J) δ ε ρ) →
      1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε) ≤ N

/-- Part 2, upper bound: for every law in `K_J` and `N_obs ≥ 192 (σ²/δ²) log(6/ε)`, the gate
meets both requirements. -/
def UpperBound : Prop :=
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, ∀ δ ε : ℝ, 0 < δ → δ ≤ sigma J / 8 → 0 < ε →
    ε ≤ 1 / 16 → ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      ∀ N : ℕ, 192 * (sigma J ^ 2 / δ ^ 2) * Real.log (6 / ε) ≤ N →
        AdmitsJ (data J q U) (gateJ J (data J q U) N δ ε) ∧
        Meets (data J q U) (V4 J) δ ε (gateJ J (data J q U) N δ ε)

/-- Part 3: `ℓ_N ≤ L_N(w_A)` for nonempty `C_N`; `ℓ_N > δ/4` makes `w_A` the plug-in optimizer;
on coverage `ℓ_N ≥ min_j [m_j(θ_*) - 2 r_N σ_j]`; and under the sufficient length with
`G_* ≥ δ` this is at least `δ/2`. -/
def DirectionalCertificate : Prop :=
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ,
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
      ∀ (N : ℕ) (ε δ : ℝ), 0 < N → 0 < ε → 0 ≤ δ →
        (∀ H : Fin N → Record 1,
          (Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) H)).Nonempty →
          ((ellJ J (data J q U) ε H : ℝ) : EReal)
            ≤ LN (data J q U) (V4 J) N ε (thetaHat (data J q U) H) wA) ∧
        (∀ H : Fin N → Record 1, δ / 4 < ellJ J (data J q U) ε H →
          wHatF (data J q U) (thetaHat (data J q U) H) = wA) ∧
        (∀ θ ∈ Theta4 (V4 J), ∀ σ : Fin N → S,
          θ ∈ Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) (hist (data J q U) θ σ)) →
          min (d0 ⬝ᵥ θ - 2 * rN (data J q U) N ε * Real.sqrt (sig2 J d0))
              (d1 ⬝ᵥ θ - 2 * rN (data J q U) N ε * Real.sqrt (sig2 J d1))
            ≤ ellJ J (data J q U) ε (hist (data J q U) θ σ)) ∧
        (0 < δ → δ ≤ sigma J / 8 → ε ≤ 1 / 16 →
          192 * (sigma J ^ 2 / δ ^ 2) * Real.log (6 / ε) ≤ N →
          ∀ θ ∈ Theta4 (V4 J), δ ≤ Gstar (data J q U) θ → ∀ σ : Fin N → S,
            θ ∈ Cset (data J q U) (V4 J) N ε (thetaHat (data J q U) (hist (data J q U) θ σ)) →
            δ / 2 ≤ ellJ J (data J q U) ε (hist (data J q U) θ σ))

/-- The example `J = s [[1, 0, 0], [1, τ, 0], [0, τ, 0]]` with `s = 1/1000`. -/
def Jex (τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (1 / 1000 : ℝ) • !![1, 0, 0; 1, τ, 0; 0, τ, 0]

/-- Part 4: the variance formulas, the alpha-precision bounds, exact alpha when `Ω₃₃ = 0`, the
example with `σ₁ = 0 < σ₀`, and the doubly degenerate benchmark. -/
def AlphaAndComparator : Prop :=
  (∀ J : Matrix (Fin 3) (Fin 3) ℝ,
    sig2 J d0 = (J * Jᵀ) 0 0 + 2 * (J * Jᵀ) 0 2 + (J * Jᵀ) 2 2 ∧
    sig2 J d1 = (J * Jᵀ) 0 0 + (J * Jᵀ) 1 1 + (J * Jᵀ) 2 2
      - 2 * (J * Jᵀ) 0 1 + 2 * (J * Jᵀ) 0 2 - 2 * (J * Jᵀ) 1 2 ∧
    (Real.sqrt ((J * Jᵀ) 0 0) - Real.sqrt ((J * Jᵀ) 2 2)) ^ 2 ≤ sigma J ^ 2 ∧
    (Real.sqrt ((J * Jᵀ) 2 2) ≤ Real.sqrt ((J * Jᵀ) 0 0) / 2 → ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 1 →
      (J * Jᵀ) 0 0 * Real.log (1 / ε) / (64 * Real.pi ^ 2 * δ ^ 2)
        ≤ 1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε)) ∧
    ((J * Jᵀ) 2 2 = 0 → (J * Jᵀ) 0 2 = 0 ∧ (J * Jᵀ) 1 2 = 0 ∧ (J * Jᵀ) 0 0 ≤ sigma J ^ 2 ∧
      ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
        ∀ θ s, 0 < q s → X (data J q U) (record (data J q U) θ s) 2 = θ 2)) ∧
  (∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    SmallJ (Jex τ) ∧ sig2 (Jex τ) d1 = 0 ∧ sig2 (Jex τ) d0 = (1 / 1000) ^ 2 * (1 + τ ^ 2) ∧
      0 < (Jex τ * (Jex τ)ᵀ) 0 0 ∧ 0 < sigma (Jex τ)) ∧
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, sig2 J d0 = 0 → sig2 J d1 = 0 → ∀ δ : ℝ, 0 < δ →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U → ∀ N : ℕ, 0 < N →
      ∃ ρ : Rule N, AdmitsJ (data J q U) ρ ∧
        (∀ θ ∈ Theta4 (V4 J), falseP (data J q U) δ θ ρ = 0) ∧
        ∀ θ ∈ Theta4 (V4 J), δ ≤ Gstar (data J q U) θ → powerP (data J q U) δ θ ρ = 1

/-- The two requirements imposed only at the parameters in `P`. -/
def MeetsOn {S : Type} [Fintype S] (D : Data 1 1 2 S) (P : Set (Fin 3 → ℝ)) (δ ε : ℝ) {N : ℕ}
    (ρ : Rule N) : Prop :=
  (∀ θ ∈ P, falseP D δ θ ρ ≤ ε) ∧ (∀ θ ∈ P, δ ≤ Gstar D θ → 1 - ε ≤ powerP D δ θ ρ)

/-- Part 4, known alpha: when `Ω₃₃ = 0` the part 2 lower bound persists for a rule told alpha
before sampling. There is a value `α₀` (the common alpha of the hard pair), fixed before
`N_obs`, such that the bound holds even when the requirements are imposed only on
`Θ₄ ∩ {α = α₀}`. -/
def KnownAlphaLower : Prop :=
  ∀ J : Matrix (Fin 3) (Fin 3) ℝ, SmallJ J → (J * Jᵀ) 2 2 = 0 → ∀ δ ε : ℝ, 0 < δ →
    δ ≤ sigma J / 8 → 0 < ε → ε ≤ 1 / 16 →
    ∃ α₀ : ℝ, ∀ N : ℕ, 0 < N →
      (∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
        ∃ ρ : Rule N, AdmitsJ (data J q U) ρ ∧
          MeetsOn (data J q U) (Theta4 (V4 J) ∩ {θ | θ 2 = α₀}) δ ε ρ) →
      1 / (16 * Real.pi ^ 2) * (sigma J ^ 2 / δ ^ 2) * Real.log (1 / ε) ≤ N

/-- Claim 016, all parts. -/
def statement : Prop :=
  Contrasts ∧ LowerBound ∧ UpperBound ∧ DirectionalCertificate ∧ AlphaAndComparator ∧
    KnownAlphaLower

end

end Standalone.M4JointDirectionalRate

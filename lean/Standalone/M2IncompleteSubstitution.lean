import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M2EtfExposureGeometry

/-!
# Claim 007: an added ETF can enlarge active trading while its full-span menu still cannot match
the optimum

Statement only; the proof is `Novel/M2IncompleteSubstitutionProof.lean`.

Two assumed M2 instances, built from the M2 objects of claim 003, claim 004's hypotheses and claim
005's exposure sets. `data1` has one active fund and one ETF; `data2` adds a second ETF held at
zero. Both use the same 32 equiprobable scenarios: a scenario is a 5-tuple of independent signs
`(b₁, …, b₅) : Bool⁵` (true = +1) multiplying the first-factor, second-factor, active-residual,
first-ETF-residual and second-ETF-residual shock sizes. In `data1` the fifth sign is unused. The
parameter support is the single point `θ = (1/50, 1/200, -1/400)` with belief mass one.
Holdings are `hold1 a p` and `hold2 a p₁ p₂`.
-/

namespace Standalone.M2IncompleteSubstitution

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry

/-- Scenarios: five independent signs. -/
abbrev Scen := Bool × Bool × Bool × Bool × Bool

/-- A sign `±1`. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

/-- The single parameter point `(λ₁, λ₂, α) = (1/50, 1/200, -1/400)`. -/
noncomputable def par : Fin 1 → Params 1 2 := fun _ => ⟨![1 / 50, 1 / 200], ![-1 / 400]⟩

/-- Belief mass one. -/
def pi1 : Fin 1 → ℝ := fun _ => 1

/-- One-ETF menu: loadings `(1, 1/2)` and `(1, 0)`, ETF drag `-1/10000`, all rates `1/2000`,
`γ = 1`, shock sizes `3/50, 1/50` (factors), `3/100` (active), `1/200` (ETF); initial holdings
`(1/2, 1/3)`, cash `1/6`, limits one. -/
noncomputable def data1 : Data 1 1 2 Scen where
  BA := !![1, 1 / 2]
  BE := !![1, 0]
  cE := ![-1 / 10000]
  kplus := fun _ => 1 / 2000
  kminus := fun _ => 1 / 2000
  gamma := 1
  q := fun _ => 1 / 32
  zf := fun s => ![3 / 50 * sg s.1, 1 / 50 * sg s.2.1]
  zA := fun s => ![3 / 100 * sg s.2.2.1]
  zE := fun s => ![1 / 200 * sg s.2.2.2.1]
  x0 := Sum.elim ![1 / 2] ![1 / 3]
  h0 := 1 / 6
  wbar := fun _ => 1

/-- Two-ETF menu: `data1` plus a second ETF with loading `(1, 1/4)`, zero drag, residual size
`1/100`, initially held at zero. -/
noncomputable def data2 : Data 1 2 2 Scen where
  BA := !![1, 1 / 2]
  BE := !![1, 0; 1, 1 / 4]
  cE := ![-1 / 10000, 0]
  kplus := fun _ => 1 / 2000
  kminus := fun _ => 1 / 2000
  gamma := 1
  q := fun _ => 1 / 32
  zf := fun s => ![3 / 50 * sg s.1, 1 / 50 * sg s.2.1]
  zA := fun s => ![3 / 100 * sg s.2.2.1]
  zE := fun s => ![1 / 200 * sg s.2.2.2.1, 1 / 100 * sg s.2.2.2.2]
  x0 := Sum.elim ![1 / 2] ![1 / 3, 0]
  h0 := 1 / 6
  wbar := fun _ => 1

/-- One-ETF holding `(a, p)`. -/
def hold1 (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim ![a] ![p]

/-- Two-ETF holding `(a, p₁, p₂)`. -/
def hold2 (a p₁ p₂ : ℝ) : Inst 1 2 → ℝ := Sum.elim ![a] ![p₁, p₂]

/-- The criteria `Q̄_0` of the two menus. -/
noncomputable def Q1 : (Inst 1 1 → ℝ) → ℝ := beliefScore data1 par pi1
noncomputable def Q2 : (Inst 1 2 → ℝ) → ℝ := beliefScore data2 par pi1

/-- `w` is the unique maximizer of `f` on `A`. -/
def UniqueMax {ι : Type} (f : (ι → ℝ) → ℝ) (A : Set (ι → ℝ)) (w : ι → ℝ) : Prop :=
  w ∈ A ∧ ∀ w' ∈ A, w' ≠ w → f w' < f w

/-- The M2 restrictions of one instance, with singleton belief `pi1` on `par`. -/
def ValidM2 {n : ℕ} (D : Data 1 n 2 Scen) : Prop :=
  W0 D = 1 ∧ InitialPosition D ∧ RatesNonneg D ∧ (∀ i, D.kplus i < 1 ∧ D.kminus i < 1) ∧
  (∀ i, D.wbar i ≤ 1) ∧ 0 ≤ D.gamma ∧ (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧ CenteredShocks D ∧
  (∀ t, 0 ≤ pi1 t) ∧ ∑ t, pi1 t = 1 ∧ ∀ t s i, 0 < 1 + ret D (par t) s i

/-- Both instances satisfy M2, and the shared instruments have identical scenario returns. -/
def ValidInstances : Prop :=
  ValidM2 data1 ∧ ValidM2 data2 ∧
  ∀ s, ret data1 (par 0) s (Sum.inl 0) = ret data2 (par 0) s (Sum.inl 0) ∧
    ret data1 (par 0) s (Sum.inr 0) = ret data2 (par 0) s (Sum.inr 0)

/-- The table: unique optima of each class in each menu, with cash, review cost and score. -/
def OptimaTable : Prop :=
  UniqueMax Q1 (N data1) (hold1 (1 / 2) (1 / 3)) ∧
  UniqueMax Q1 (E data1) (hold1 (1 / 2) (3001 / 6003)) ∧
  UniqueMax Q1 (F data1) (hold1 (1 / 2) (3001 / 6003)) ∧
  UniqueMax Q2 (N data2) (hold2 (1 / 2) (1 / 3) 0) ∧
  UniqueMax Q2 (E data2) (hold2 (1 / 2) 0 (2999 / 6003)) ∧
  UniqueMax Q2 (F data2) (hold2 0 0 (11995 / 12006)) ∧
  cash data1 (hold1 (1 / 2) (1 / 3)) = 1 / 6 ∧
  tau data1 (hold1 (1 / 2) (1 / 3) - w0 data1) = 0 ∧
  Q1 (hold1 (1 / 2) (1 / 3)) = 11033 / 720000 ∧
  cash data1 (hold1 (1 / 2) (3001 / 6003)) = 0 ∧
  tau data1 (hold1 (1 / 2) (3001 / 6003) - w0 data1) = 1 / 12006 ∧
  Q1 (hold1 (1 / 2) (3001 / 6003)) = 61830113 / 3427920000 ∧
  cash data2 (hold2 (1 / 2) (1 / 3) 0) = 1 / 6 ∧
  tau data2 (hold2 (1 / 2) (1 / 3) 0 - w0 data2) = 0 ∧
  Q2 (hold2 (1 / 2) (1 / 3) 0) = 11033 / 720000 ∧
  cash data2 (hold2 (1 / 2) 0 (2999 / 6003)) = 0 ∧
  tau data2 (hold2 (1 / 2) 0 (2999 / 6003) - w0 data2) = 5 / 12006 ∧
  Q2 (hold2 (1 / 2) 0 (2999 / 6003)) = 2104284079 / 115315228800 ∧
  cash data2 (hold2 0 0 (11995 / 12006)) = 0 ∧
  tau data2 (hold2 0 0 (11995 / 12006) - w0 data2) = 11 / 12006 ∧
  Q2 (hold2 0 0 (11995 / 12006)) = 8512677811 / 461260915200

/-- The optimized gaps (zero with one ETF, `6369433/30750727680 > 0` with two), strict
improvement of E and F over N in both menus, the active trade (none, then a sale of `1/2`) and
the one-ETF optimum's ETF purchase `1000/6003`. -/
def Gaps : Prop :=
  Q1 (hold1 (1 / 2) (3001 / 6003)) - Q1 (hold1 (1 / 2) (3001 / 6003)) = 0 ∧
  Q2 (hold2 0 0 (11995 / 12006)) - Q2 (hold2 (1 / 2) 0 (2999 / 6003)) = 6369433 / 30750727680 ∧
  (0 : ℝ) < 6369433 / 30750727680 ∧
  Q1 (hold1 (1 / 2) (1 / 3)) < Q1 (hold1 (1 / 2) (3001 / 6003)) ∧
  Q2 (hold2 (1 / 2) (1 / 3) 0) < Q2 (hold2 (1 / 2) 0 (2999 / 6003)) ∧
  Q2 (hold2 (1 / 2) (1 / 3) 0) < Q2 (hold2 0 0 (11995 / 12006)) ∧
  hold1 (1 / 2) (3001 / 6003) (Sum.inl 0) - w0 data1 (Sum.inl 0) = 0 ∧
  hold2 0 0 (11995 / 12006) (Sum.inl 0) - w0 data2 (Sum.inl 0) = -1 / 2 ∧
  hold1 (1 / 2) (3001 / 6003) (Sum.inr 0) - w0 data1 (Sum.inr 0) = 1000 / 6003

/-- Exposure obstructions. One ETF: selling everything is feasible and its exposure change
`(-5/6, -1/4)` is outside `L_E`. Two ETFs: `L_E = ℝ²`; retaining `a = 1/2`, the full optimum's
exposure is matched only by ETF holdings `(1/2, -11/12006)`; no ETF-only action matches it. -/
def Obstructions : Prop :=
  (hold1 0 0 ∈ F data1 ∧
    exposure data1 (hold1 0 0) - exposure data1 (w0 data1) = ![-5 / 6, -1 / 4] ∧
    ![-5 / 6, -1 / 4] ∉ LE data1) ∧
  (LE data2 = Set.univ ∧
    (∀ p₁ p₂, exposure data2 (hold2 (1 / 2) p₁ p₂) = exposure data2 (hold2 0 0 (11995 / 12006))
      ↔ p₁ = 1 / 2 ∧ p₂ = -11 / 12006) ∧
    ∀ w ∈ E data2, exposure data2 w ≠ exposure data2 (hold2 0 0 (11995 / 12006)))

/-- Claim 007, all parts. -/
def statement : Prop :=
  ValidInstances ∧ OptimaTable ∧ Gaps ∧ Obstructions

end Standalone.M2IncompleteSubstitution

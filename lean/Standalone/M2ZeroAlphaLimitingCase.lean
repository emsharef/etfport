import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M2EtfExposureGeometry

/-!
# Claim 008: zero-alpha non-participation under feasible, costless ETF replacement

Statement only; the proof is `Novel/M2ZeroAlphaLimitingCaseProof.lean`.

General part: any M2 instance (claim 003's formal objects) with one active fund and one ETF
(`Inst 1 1`), any number K of factors, any finite scenario type `S` and any finite belief
`(T, par, pi)`. The replacement of `w = (a, p)` is `replace w = (0, a + p)`. The ETF's centered
shock is `ξ_E,s = xi D s (inr 0)` and `ε_s = ξ_A,s - ξ_E,s`. Case (A) is `a⁻ = 0`; case (B) is a
zero active sale rate.

Examples: four assumed instances `exData a₀ p₀ h₀ κ p̄` (active holding, ETF holding, cash,
common active purchase/sale rate, ETF cap), with `W⁻ = 1`, `γ = 1`, loadings `(1, 0)`, zero drag,
zero residuals, factor shocks `(±1/10, 0)` with mass `1/2`, and the singleton belief
`θ = (1/50, 0, 0)`.
-/

namespace Standalone.M2ZeroAlphaLimitingCase

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2EtfExposureGeometry

variable {K : ℕ} {S : Type} [Fintype S]

/-- The replacement holding `T(w) = (0, a + p)`. -/
def replace (w : Inst 1 1 → ℝ) : Inst 1 1 → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => w (Sum.inl 0) + w (Sum.inr 0))

/-- Residual shock difference `ε_s = ξ_A,s - ξ_E,s`. -/
def eps (D : Data 1 1 K S) (s : S) : ℝ := xi D s (Sum.inl 0) - xi D s (Sum.inr 0)

/-- `v_ε = Σ_s q_s ε_s²`. -/
def vEps (D : Data 1 1 K S) : ℝ := ∑ s, D.q s * eps D s ^ 2

/-- The claim's hypotheses beyond M2's other restrictions, with the M2 restrictions its proof
uses: compliant start, `B^A = B^E`, `c^E = 0`, free ETF trading, ETF cap one, nonnegative active
rates, `γ ≥ 0`, nonnegative scenario masses summing to one, belief masses summing to one,
belief-mean alpha zero, and zero cross-moment `Σ_s q_s ξ_E,s ε_s = 0`. -/
def ZeroAlphaSetting (D : Data 1 1 K S) {T : Type} [Fintype T] (par : T → Params 1 K)
    (pi : T → ℝ) : Prop :=
  InitialPosition D ∧ D.BA = D.BE ∧ D.cE = 0 ∧
  D.kplus (Sum.inr 0) = 0 ∧ D.kminus (Sum.inr 0) = 0 ∧ D.wbar (Sum.inr 0) = 1 ∧
  0 ≤ D.kplus (Sum.inl 0) ∧ 0 ≤ D.kminus (Sum.inl 0) ∧ 0 ≤ D.gamma ∧
  (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧ ∑ t, pi t = 1 ∧
  (beliefMean par pi).alpha = 0 ∧ ∑ s, D.q s * (xi D s (Sum.inr 0) * eps D s) = 0

/-- Case (A) or (B). -/
def CaseAB (D : Data 1 1 K S) : Prop := w0 D (Sum.inl 0) = 0 ∨ D.kminus (Sum.inl 0) = 0

/-- For every feasible `w`: `T(w)` is feasible, has the same exposure and zero review cost,
`k(T(w)) - k(w) = τ(w - w⁻)` and `Q̄(T(w)) - Q̄(w) = τ(w - w⁻) + (γ/2) a² v_ε ≥ 0`. -/
def Replacement : Prop :=
  ∀ (K : ℕ) (S : Type) [Fintype S] (D : Data 1 1 K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), ZeroAlphaSetting D par pi → CaseAB D →
    ∀ w ∈ F D,
      replace w ∈ F D ∧ exposure D (replace w) = exposure D w ∧
      tau D (replace w - w0 D) = 0 ∧
      cash D (replace w) - cash D w = tau D (w - w0 D) ∧
      beliefScore D par pi (replace w) - beliefScore D par pi w
        = tau D (w - w0 D) + D.gamma / 2 * w (Sum.inl 0) ^ 2 * vEps D ∧
      0 ≤ beliefScore D par pi (replace w) - beliefScore D par pi w

/-- A full-class optimum with zero active holding exists. Under (A): replacements are ETF-only,
the F and E optimal values are equal, and every full optimum has `a = 0` if `κ⁺_A > 0` or
`γ v_ε > 0`. Under (B): every full optimum has `a = 0` if `γ v_ε > 0`; with an incumbent
`a⁻ > 0`, no ETF-only holding has zero active holding. -/
def NonParticipation : Prop :=
  ∀ (K : ℕ) (S : Type) [Fintype S] (D : Data 1 1 K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), ZeroAlphaSetting D par pi → CaseAB D →
    (∃ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w ∧ w (Sum.inl 0) = 0) ∧
    (w0 D (Sum.inl 0) = 0 →
      (∀ w ∈ F D, replace w ∈ E D) ∧
      (∀ wF wE, wF ∈ F D → IsMaxOn (beliefScore D par pi) (F D) wF →
        wE ∈ E D → IsMaxOn (beliefScore D par pi) (E D) wE →
        beliefScore D par pi wF = beliefScore D par pi wE) ∧
      (0 < D.kplus (Sum.inl 0) ∨ 0 < D.gamma * vEps D →
        ∀ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w → w (Sum.inl 0) = 0)) ∧
    (D.kminus (Sum.inl 0) = 0 →
      (0 < D.gamma * vEps D →
        ∀ w ∈ F D, IsMaxOn (beliefScore D par pi) (F D) w → w (Sum.inl 0) = 0) ∧
      (0 < w0 D (Sum.inl 0) → ∀ w ∈ E D, w (Sum.inl 0) ≠ 0))

/-- Exact replication: for a compliant start with `B^A = B^E`, `c^E = 0`, `α = 0` at every support point and `ε_s = 0`
at every scenario, active and ETF returns agree pointwise, and
`W_1(T(w); θ, s) - W_1(w; θ, s) = W⁻ τ(w - w⁻)` for every holding, support point and scenario. -/
def ExactReplication : Prop :=
  ∀ (K : ℕ) (S : Type) [Fintype S] (D : Data 1 1 K S) (T : Type) (par : T → Params 1 K),
    InitialPosition D → D.BA = D.BE → D.cE = 0 → (∀ t, (par t).alpha = 0) →
    (∀ s, eps D s = 0) → D.kplus (Sum.inr 0) = 0 → D.kminus (Sum.inr 0) = 0 → CaseAB D →
    (∀ t s, ret D (par t) s (Sum.inl 0) = ret D (par t) s (Sum.inr 0)) ∧
    ∀ (w : Inst 1 1 → ℝ) t s,
      W1 D (replace w) (par t) s - W1 D w (par t) s = W0 D * tau D (w - w0 D)

/-! ### The four limiting examples -/

/-- Example instance: initial active holding `a₀`, ETF holding `p₀`, cash `h₀`, common active
purchase and sale rate `κ`, ETF cap `p̄`; everything else as in the module header. -/
noncomputable def exData (a₀ p₀ h₀ κ pb : ℝ) : Data 1 1 2 (Fin 2) where
  BA := !![1, 0]
  BE := !![1, 0]
  cE := 0
  kplus := Sum.elim (fun _ => κ) (fun _ => 0)
  kminus := Sum.elim (fun _ => κ) (fun _ => 0)
  gamma := 1
  q := fun _ => 1 / 2
  zf := ![![1 / 10, 0], ![-1 / 10, 0]]
  zA := 0
  zE := 0
  x0 := Sum.elim (fun _ => a₀) (fun _ => p₀)
  h0 := h₀
  wbar := Sum.elim (fun _ => 1) (fun _ => pb)

/-- The singleton belief `θ = (1/50, 0, 0)`. -/
noncomputable def exPar : Fin 1 → Params 1 2 := fun _ => ⟨![1 / 50, 0], ![0]⟩

/-- Belief mass one. -/
def exPi : Fin 1 → ℝ := fun _ => 1

/-- The holding `(a, p)`. -/
def hold (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- The example criterion. -/
noncomputable def Qex (a₀ p₀ h₀ κ pb : ℝ) : (Inst 1 1 → ℝ) → ℝ :=
  beliefScore (exData a₀ p₀ h₀ κ pb) exPar exPi

/-- `w` is the unique maximizer of `f` on `A`. -/
def UniqueMax (f : (Inst 1 1 → ℝ) → ℝ) (A : Set (Inst 1 1 → ℝ)) (w : Inst 1 1 → ℝ) : Prop :=
  w ∈ A ∧ ∀ w' ∈ A, w' ≠ w → f w' < f w

/-- Each example satisfies the M2 restrictions (rates in `[0, 1)`, compliant start, limits at
most one, centered shocks, masses summing to one, positive gross returns). -/
def ExampleValid (a₀ p₀ h₀ κ pb : ℝ) : Prop :=
  let D := exData a₀ p₀ h₀ κ pb
  W0 D = 1 ∧ InitialPosition D ∧ RatesNonneg D ∧ (∀ i, D.kplus i < 1 ∧ D.kminus i < 1) ∧
  (∀ i, D.wbar i ≤ 1) ∧ 0 ≤ D.gamma ∧ (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧
  CenteredShocks D ∧ (∀ t, 0 ≤ exPi t) ∧ ∑ t, exPi t = 1 ∧
  ∀ t s i, 0 < 1 + ret D (exPar t) s i

/-- The four cases of the table. -/
def Examples : Prop :=
  -- validity of the four instances
  ExampleValid 0 0 1 (1 / 100) 1 ∧ ExampleValid 1 0 0 (1 / 100) 1 ∧
  ExampleValid 0 0 1 0 1 ∧ ExampleValid 0 0 1 0 (1 / 4) ∧
  -- positive purchase cost: unique F optimum (0, 1), score 3/200
  UniqueMax (Qex 0 0 1 (1 / 100) 1) (F (exData 0 0 1 (1 / 100) 1)) (hold 0 1) ∧
  Qex 0 0 1 (1 / 100) 1 (hold 0 1) = 3 / 200 ∧
  -- costly incumbent: unique F optimum (1, 0), score 3/200; best zero-active holding
  -- (0, 99/100) with score 9799/2000000 < 3/200; neither (A) nor (B) holds
  UniqueMax (Qex 1 0 0 (1 / 100) 1) (F (exData 1 0 0 (1 / 100) 1)) (hold 1 0) ∧
  Qex 1 0 0 (1 / 100) 1 (hold 1 0) = 3 / 200 ∧
  UniqueMax (Qex 1 0 0 (1 / 100) 1) {w | w ∈ F (exData 1 0 0 (1 / 100) 1) ∧ w (Sum.inl 0) = 0}
    (hold 0 (99 / 100)) ∧
  Qex 1 0 0 (1 / 100) 1 (hold 0 (99 / 100)) = 9799 / 2000000 ∧
  (9799 / 2000000 : ℝ) < 3 / 200 ∧ ¬ CaseAB (exData 1 0 0 (1 / 100) 1) ∧
  -- tie under exact replication: the F maximizers are exactly the feasible a + p = 1
  maximizers (Qex 0 0 1 0 1) (F (exData 0 0 1 0 1))
    = {w | w ∈ F (exData 0 0 1 0 1) ∧ w (Sum.inl 0) + w (Sum.inr 0) = 1} ∧
  hold 0 1 ∈ maximizers (Qex 0 0 1 0 1) (F (exData 0 0 1 0 1)) ∧
  hold 1 0 ∈ maximizers (Qex 0 0 1 0 1) (F (exData 0 0 1 0 1)) ∧
  Qex 0 0 1 0 1 (hold 0 1) = 3 / 200 ∧
  -- ETF cap 1/4: the F maximizers are exactly the feasible a + p = 1 (score 3/200);
  -- unique E optimum (0, 1/4) with score 3/640; V_F - V_E = 33/3200; T(3/4, 1/4) ∉ F
  maximizers (Qex 0 0 1 0 (1 / 4)) (F (exData 0 0 1 0 (1 / 4)))
    = {w | w ∈ F (exData 0 0 1 0 (1 / 4)) ∧ w (Sum.inl 0) + w (Sum.inr 0) = 1} ∧
  Qex 0 0 1 0 (1 / 4) (hold (3 / 4) (1 / 4)) = 3 / 200 ∧
  UniqueMax (Qex 0 0 1 0 (1 / 4)) (E (exData 0 0 1 0 (1 / 4))) (hold 0 (1 / 4)) ∧
  Qex 0 0 1 0 (1 / 4) (hold 0 (1 / 4)) = 3 / 640 ∧
  Qex 0 0 1 0 (1 / 4) (hold (3 / 4) (1 / 4)) - Qex 0 0 1 0 (1 / 4) (hold 0 (1 / 4)) = 33 / 3200 ∧
  hold (3 / 4) (1 / 4) ∈ F (exData 0 0 1 0 (1 / 4)) ∧
  replace (hold (3 / 4) (1 / 4)) ∉ F (exData 0 0 1 0 (1 / 4))

/-- Claim 008, all parts. -/
def statement : Prop :=
  Replacement ∧ NonParticipation ∧ ExactReplication ∧ Examples

end Standalone.M2ZeroAlphaLimitingCase

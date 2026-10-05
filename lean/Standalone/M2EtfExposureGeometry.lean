import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Standalone.M2ActionClasses

/-!
# Claim 005: ETF-only exposure geometry under M2's funded directional costs

Statement only; the proof is `Novel/M2EtfExposureGeometryProof.lean`.

Uses the M2 objects of `Standalone/M2ScoreAccounting.lean` (claim 003) and the hypotheses
`InitialPosition` and `RatesNonneg` of `Standalone/M2ActionClasses.lean` (claim 004). Counts are
arbitrary except where a part names them: the one-ETF interval is stated for n = 1, the full-span
case for a square invertible ETF loading matrix (n = K, which includes M2's n = K = 2), and the
missing-direction equivalence for one active fund (m = 1, as in M2).

The M1/M2 exposure sets are defined as the spec defines them: `BEset = {b(w) : w ∈ E}`,
`DE = {b(w) - b(w⁻) : w ∈ E}` and `LE = {(B^E)' d : d ∈ ℝⁿ}`. The claim's formulas for them in
terms of the trade set `P_E` are conclusions, not definitions. A purchase/sale assignment σ is a
function `Fin n → Bool` (true = purchase). Every part lists only the hypotheses its proof uses.
-/

namespace Standalone.M2EtfExposureGeometry

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses

variable {m n K : ℕ} {S : Type}

/-- ETF purchase rate `κ⁺_{E,j}`. -/
def kplusE (D : Data m n K S) (j : Fin n) : ℝ := D.kplus (Sum.inr j)

/-- ETF sale rate `κ⁻_{E,j}`. -/
def kminusE (D : Data m n K S) (j : Fin n) : ℝ := D.kminus (Sum.inr j)

/-- Initial ETF holdings `p⁻`. -/
noncomputable def p0 (D : Data m n K S) : Fin n → ℝ := etf (w0 D)

/-- ETF position limits `p̄`. -/
def pbar (D : Data m n K S) : Fin n → ℝ := etf D.wbar

/-- ETF net cash outlay
`Ψ_E(d) = Σ_j [d_j + κ⁺_{E,j} max(d_j, 0) + κ⁻_{E,j} max(-d_j, 0)]`. -/
def PsiE (D : Data m n K S) (d : Fin n → ℝ) : ℝ :=
  ∑ j, (d j + kplusE D j * max (d j) 0 + kminusE D j * max (-d j) 0)

/-- Position bounds on an ETF trade: `-p⁻ ≤ d ≤ p̄ - p⁻`. -/
def InBounds (D : Data m n K S) (d : Fin n → ℝ) : Prop :=
  ∀ j, -p0 D j ≤ d j ∧ d j ≤ pbar D j - p0 D j

/-- The feasible ETF trade set `P_E = {d : -p⁻ ≤ d ≤ p̄ - p⁻, Ψ_E(d) ≤ k⁻}`. -/
def PE (D : Data m n K S) : Set (Fin n → ℝ) := {d | InBounds D d ∧ PsiE D d ≤ k0 D}

/-- Cash coefficients `c_σ`: `1 + κ⁺_{E,j}` if σ assigns a purchase to ETF j, else `1 - κ⁻_{E,j}`. -/
def cSigma (D : Data m n K S) (σ : Fin n → Bool) : Fin n → ℝ :=
  fun j => if σ j then 1 + kplusE D j else 1 - kminusE D j

/-- The ETF-only holding reached by ETF trade `d`: `(a⁻, p⁻ + d)`. -/
noncomputable def etfAction (D : Data m n K S) (d : Fin n → ℝ) : Inst m n → ℝ :=
  w0 D + Sum.elim (0 : Fin m → ℝ) d

/-- ETF linear span `L_E = {(B^E)' d : d ∈ ℝⁿ}`. -/
def LE (D : Data m n K S) : Set (Fin K → ℝ) := Set.range fun d : Fin n → ℝ => D.BEᵀ *ᵥ d

/-- `D_E = {b(w) - b(w⁻) : w ∈ E}`. -/
def DE (D : Data m n K S) : Set (Fin K → ℝ) :=
  (fun w => exposure D w - exposure D (w0 D)) '' E D

/-- `B_E = {b(w) : w ∈ E}`. -/
def BEset (D : Data m n K S) : Set (Fin K → ℝ) := exposure D '' E D

/-- An ETF-only action matches the target exposure change `δ`. -/
def Matches (D : Data m n K S) (δ : Fin K → ℝ) : Prop :=
  ∃ w ∈ E D, exposure D w - exposure D (w0 D) = δ

/-- The finite system for matching: `(B^E)' d = δ`, the bounds, and every cash inequality. -/
def MatchSystem (D : Data m n K S) (δ : Fin K → ℝ) (d : Fin n → ℝ) : Prop :=
  D.BEᵀ *ᵥ d = δ ∧ InBounds D d ∧ ∀ σ, cSigma D σ ⬝ᵥ d ≤ k0 D

/-- Max representation: `Ψ_E(d) = max_σ c_σ' d`, and `P_E` as bounds plus the 2ⁿ cash
inequalities. Needs nonnegative rates. -/
def CashRepresentation : Prop :=
  ∀ (m n K : ℕ) (S : Type) (D : Data m n K S), RatesNonneg D →
    (∀ d, (∀ σ, cSigma D σ ⬝ᵥ d ≤ PsiE D d) ∧ ∃ σ, cSigma D σ ⬝ᵥ d = PsiE D d) ∧
    PE D = {d | InBounds D d ∧ ∀ σ, cSigma D σ ⬝ᵥ d ≤ k0 D}

/-- ETF-only cash `k(a⁻, p⁻ + d) = k⁻ - Ψ_E(d)` for every `d`, and
`E = {(a⁻, p⁻ + d) : d ∈ P_E}` for a compliant start. -/
def EtfClass : Prop :=
  ∀ (m n K : ℕ) (S : Type) (D : Data m n K S),
    (∀ d, cash D (etfAction D d) = k0 D - PsiE D d) ∧
    (InitialPosition D → E D = etfAction D '' PE D)

/-- `D_E = (B^E)' P_E` for a compliant start; `B_E = b(w⁻) + D_E` and `D_E ⊆ L_E` always. -/
def ExposureSets : Prop :=
  ∀ (m n K : ℕ) (S : Type) (D : Data m n K S),
    (InitialPosition D → DE D = (fun d => D.BEᵀ *ᵥ d) '' PE D) ∧
    BEset D = (fun y => exposure D (w0 D) + y) '' DE D ∧ DE D ⊆ LE D

/-- `P_E` is closed and bounded always. For a compliant start, `P_E`, `D_E`, `B_E` contain the
incumbent points and `D_E`, `B_E` are closed and bounded; with nonnegative rates as well, all three
are convex. -/
def SetProperties : Prop :=
  ∀ (m n K : ℕ) (S : Type) (D : Data m n K S),
    (IsClosed (PE D) ∧ Bornology.IsBounded (PE D)) ∧
    (InitialPosition D →
      (0 : Fin n → ℝ) ∈ PE D ∧ (0 : Fin K → ℝ) ∈ DE D ∧ exposure D (w0 D) ∈ BEset D ∧
      IsClosed (DE D) ∧ IsClosed (BEset D) ∧
      Bornology.IsBounded (DE D) ∧ Bornology.IsBounded (BEset D)) ∧
    (InitialPosition D → RatesNonneg D →
      Convex ℝ (PE D) ∧ Convex ℝ (DE D) ∧ Convex ℝ (BEset D))

/-- Matching criterion over all solutions, and the classification of a failure as a missing
direction, a bound obstruction, or a funding obstruction (with bounded solutions present). -/
def MatchingCriterion : Prop :=
  ∀ (m n K : ℕ) (S : Type) (D : Data m n K S), InitialPosition D → RatesNonneg D →
    ∀ δ : Fin K → ℝ,
      (Matches D δ ↔ ∃ d, MatchSystem D δ d) ∧
      (¬ Matches D δ ↔
        δ ∉ LE D ∨
        (δ ∈ LE D ∧ ¬ ∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d) ∨
        ((∃ d, D.BEᵀ *ᵥ d = δ ∧ InBounds D d) ∧ ¬ ∃ d, MatchSystem D δ d))

/-- One ETF: `P_E = [-p⁻, min(p̄ - p⁻, k⁻/(1 + κ⁺_E))]`, and `D_E` is that interval times the
ETF loading vector (so `{0}` for a zero loading). -/
def OneEtf : Prop :=
  ∀ (m K : ℕ) (S : Type) (D : Data m 1 K S), 0 ≤ kplusE D 0 → kminusE D 0 ≤ 1 →
    (0 ≤ k0 D → ∀ d : Fin 1 → ℝ,
      d ∈ PE D ↔ -p0 D 0 ≤ d 0 ∧ d 0 ≤ min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0))) ∧
    (InitialPosition D →
      DE D = (fun t : ℝ => t • fun k => D.BE 0 k) ''
        Set.Icc (-p0 D 0) (min (pbar D 0 - p0 D 0) (k0 D / (1 + kplusE D 0))) ∧
      ((∀ k, D.BE 0 k = 0) → DE D = {0}))

/-- Square invertible ETF loadings: `L_E` is everything, `d = ((B^E)')⁻¹ δ` is the only
solution, and matching holds exactly when it satisfies the bounds and cash inequalities. -/
def FullSpan : Prop :=
  ∀ (m n : ℕ) (S : Type) (D : Data m n n S), IsUnit (D.BEᵀ).det →
    LE D = Set.univ ∧
    ∀ δ : Fin n → ℝ, (∀ d, D.BEᵀ *ᵥ d = δ ↔ d = (D.BEᵀ)⁻¹ *ᵥ δ) ∧
      (InitialPosition D → RatesNonneg D →
        (Matches D δ ↔ InBounds D ((D.BEᵀ)⁻¹ *ᵥ δ) ∧
          ∀ σ, cSigma D σ ⬝ᵥ ((D.BEᵀ)⁻¹ *ᵥ δ) ≤ k0 D))

/-- One active fund: for any holding with `a ≠ a⁻`, its exposure change is in `L_E` iff the
active loading vector `(B^A)'` is; and a full action with `a = a⁻` is ETF-only. -/
def MissingDirection : Prop :=
  (∀ (n K : ℕ) (S : Type) (D : Data 1 n K S) (w : Inst 1 n → ℝ),
    active w ≠ active (w0 D) →
      (exposure D w - exposure D (w0 D) ∈ LE D ↔ (fun k => D.BA 0 k) ∈ LE D)) ∧
  (∀ (m n K : ℕ) (S : Type) (D : Data m n K S) (w : Inst m n → ℝ),
    w ∈ F D → active w = active (w0 D) → w ∈ E D)

/-- Claim 005, all parts. -/
def statement : Prop :=
  CashRepresentation ∧ EtfClass ∧ ExposureSets ∧ SetProperties ∧ MatchingCriterion ∧
    OneEtf ∧ FullSpan ∧ MissingDirection

end Standalone.M2EtfExposureGeometry

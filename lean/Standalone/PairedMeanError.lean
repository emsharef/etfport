import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

/-!
# Claim 002: paired mean-error identity with fixed loadings and risk inputs (M0)

Statement only; the proof is `Novel/PairedMeanErrorProof.lean`.

There are m active funds, n ETFs and K factors. A holding is a pair `(a, p)` of active and ETF
dollar positions in one pre-trade normalization; the full holding vector is `Sum.elim a p`,
indexed by `Fin m ⊕ Fin n`. The inputs held fixed across both score evaluations (loadings,
ETF drag, risk coefficient, covariance matrix, initial holdings and switching-cost function)
are bundled in `Inputs`. Nothing is assumed about them: `Sigma` is any real square matrix,
`gamma` any real, `C` any real function. Only the means `lambda` and `alpha` vary.
-/

namespace Standalone.PairedMeanError

open Matrix

/-- The inputs held fixed when means are replaced. -/
structure Inputs (m n K : ℕ) where
  /-- Active-fund loadings `B^A`, funds in rows, factors in columns. -/
  BA : Matrix (Fin m) (Fin K) ℝ
  /-- ETF loadings `B^E`, ETFs in rows, factors in columns. -/
  BE : Matrix (Fin n) (Fin K) ℝ
  /-- ETF fee and tracking drag `c^E`. -/
  cE : Fin n → ℝ
  /-- Risk coefficient `gamma`. -/
  gamma : ℝ
  /-- Covariance matrix `Sigma`, held fixed. -/
  Sigma : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ
  /-- Initial holdings `w^-`. -/
  w0 : Fin m ⊕ Fin n → ℝ
  /-- Switching-cost function `C_t`. -/
  C : (Fin m ⊕ Fin n → ℝ) → ℝ

variable {m n K : ℕ}

/-- Factor exposure `b(a, p) = (B^A)' a + (B^E)' p`. -/
def exposure (D : Inputs m n K) (a : Fin m → ℝ) (p : Fin n → ℝ) : Fin K → ℝ :=
  D.BAᵀ *ᵥ a + D.BEᵀ *ᵥ p

/-- The M0 one-quarter score at holding `w = (a, p)` with factor means `lam` and alphas `alpha`:
`b(w)' lam + a' alpha - p' c^E - (gamma/2) w' Sigma w - C(w - w^-)`. -/
noncomputable def score (D : Inputs m n K) (lam : Fin K → ℝ) (alpha : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) : ℝ :=
  exposure D a p ⬝ᵥ lam + a ⬝ᵥ alpha - p ⬝ᵥ D.cE
    - D.gamma / 2 * (Sum.elim a p ⬝ᵥ (D.Sigma *ᵥ Sum.elim a p))
    - D.C (Sum.elim a p - D.w0)

/-- The paired mean error: the estimated score difference between `w = (a, p)` and the
comparator `v = (av, pv)`, minus the original score difference. -/
noncomputable def pairedError (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ) (pv : Fin n → ℝ) : ℝ :=
  (score D lamHat alphaHat a p - score D lamHat alphaHat av pv)
    - (score D lam alpha a p - score D lam alpha av pv)

/-- The identity: for every pair of holdings and every pair of mean vectors, the paired error
is `d_b' e_lambda + d_a' e_alpha`. -/
def Identity : Prop :=
  ∀ (m n K : ℕ) (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ) (pv : Fin n → ℝ),
    pairedError D lam lamHat alpha alphaHat a p av pv
      = (exposure D a p - exposure D av pv) ⬝ᵥ (lamHat - lam) + (a - av) ⬝ᵥ (alphaHat - alpha)

/-- The factor-mean contribution `d_b' e` vanishes for every real `e` if and only if
`b(w) = b(v)`. -/
def UniversalCancellation : Prop :=
  ∀ (m n K : ℕ) (D : Inputs m n K) (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ)
    (pv : Fin n → ℝ),
    (∀ e : Fin K → ℝ, (exposure D a p - exposure D av pv) ⬝ᵥ e = 0)
      ↔ exposure D a p = exposure D av pv

/-- Exposure matching leaves exactly `d_a' e_alpha`; matching active holdings as well makes
the paired error zero. -/
def ExposureMatching : Prop :=
  ∀ (m n K : ℕ) (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ) (pv : Fin n → ℝ),
    exposure D a p = exposure D av pv →
      pairedError D lam lamHat alpha alphaHat a p av pv = (a - av) ⬝ᵥ (alphaHat - alpha) ∧
      (a = av → pairedError D lam lamHat alpha alphaHat a p av pv = 0)

/-- For one particular factor-mean error, with no hypothesis on `d_b`: if
`d_b' e_lambda = 0` then the paired error is `d_a' e_alpha`. -/
def ParticularCancellation : Prop :=
  ∀ (m n K : ℕ) (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ) (pv : Fin n → ℝ),
    (exposure D a p - exposure D av pv) ⬝ᵥ (lamHat - lam) = 0 →
      pairedError D lam lamHat alpha alphaHat a p av pv = (a - av) ⬝ᵥ (alphaHat - alpha)

/-- The factor contribution can vanish for a particular error while `d_b ≠ 0`: a witness with
K = 2, a nonzero exposure difference and a nonzero factor-mean error orthogonal to it. -/
def NonzeroWitness : Prop :=
  ∃ (D : Inputs 2 0 2) (lam lamHat : Fin 2 → ℝ) (a av : Fin 2 → ℝ) (p pv : Fin 0 → ℝ),
    exposure D a p ≠ exposure D av pv ∧ lamHat - lam ≠ 0 ∧
      (exposure D a p - exposure D av pv) ⬝ᵥ (lamHat - lam) = 0

/-- Claim 002, all parts. -/
def statement : Prop :=
  Identity ∧ UniversalCancellation ∧ ExposureMatching ∧ ParticularCancellation ∧ NonzeroWitness

end Standalone.PairedMeanError

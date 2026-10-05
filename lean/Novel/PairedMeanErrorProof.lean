import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Standalone.PairedMeanError

/-!
# Proof of claim 002: paired mean-error identity with fixed loadings and risk inputs (M0)

At each holding the drag, risk and cost terms are the same in the estimated and original
scores, so they cancel; linearity of the dot product gives the identity. The universal
cancellation condition takes `e = d_b` and uses that a real vector with zero dot square is zero.
-/

namespace Novel.PairedMeanErrorProof

open Matrix Standalone.PairedMeanError

variable {m n K : ℕ}

/-- Estimated minus original score at one holding. -/
lemma score_sub (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) :
    score D lamHat alphaHat a p - score D lam alpha a p
      = exposure D a p ⬝ᵥ (lamHat - lam) + a ⬝ᵥ (alphaHat - alpha) := by
  simp only [score, dotProduct_sub]
  ring

lemma identity (D : Inputs m n K) (lam lamHat : Fin K → ℝ) (alpha alphaHat : Fin m → ℝ)
    (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ) (pv : Fin n → ℝ) :
    pairedError D lam lamHat alpha alphaHat a p av pv
      = (exposure D a p - exposure D av pv) ⬝ᵥ (lamHat - lam)
        + (a - av) ⬝ᵥ (alphaHat - alpha) := by
  have hw := score_sub D lam lamHat alpha alphaHat a p
  have hv := score_sub D lam lamHat alpha alphaHat av pv
  rw [sub_dotProduct, sub_dotProduct]
  unfold pairedError
  linear_combination hw - hv

lemma universalCancellation (D : Inputs m n K) (a : Fin m → ℝ) (p : Fin n → ℝ)
    (av : Fin m → ℝ) (pv : Fin n → ℝ) :
    (∀ e : Fin K → ℝ, (exposure D a p - exposure D av pv) ⬝ᵥ e = 0)
      ↔ exposure D a p = exposure D av pv := by
  constructor
  · intro H
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp (H _))
  · intro H e
    rw [H, sub_self, zero_dotProduct]

lemma particularCancellation (D : Inputs m n K) (lam lamHat : Fin K → ℝ)
    (alpha alphaHat : Fin m → ℝ) (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ)
    (pv : Fin n → ℝ) (H : (exposure D a p - exposure D av pv) ⬝ᵥ (lamHat - lam) = 0) :
    pairedError D lam lamHat alpha alphaHat a p av pv = (a - av) ⬝ᵥ (alphaHat - alpha) := by
  rw [identity, H, zero_add]

lemma exposureMatching (D : Inputs m n K) (lam lamHat : Fin K → ℝ)
    (alpha alphaHat : Fin m → ℝ) (a : Fin m → ℝ) (p : Fin n → ℝ) (av : Fin m → ℝ)
    (pv : Fin n → ℝ) (H : exposure D a p = exposure D av pv) :
    pairedError D lam lamHat alpha alphaHat a p av pv = (a - av) ⬝ᵥ (alphaHat - alpha) ∧
      (a = av → pairedError D lam lamHat alpha alphaHat a p av pv = 0) := by
  have h1 := particularCancellation D lam lamHat alpha alphaHat a p av pv
    ((universalCancellation D a p av pv).mpr H _)
  refine ⟨h1, fun ha => ?_⟩
  rw [h1, ha, sub_self, zero_dotProduct]

/-- Witness inputs: identity active loadings, no ETFs, all other inputs zero. -/
def witnessInputs : Inputs 2 0 2 where
  BA := 1
  BE := 0
  cE := 0
  gamma := 0
  Sigma := 0
  w0 := 0
  C := fun _ => 0

lemma nonzeroWitness : NonzeroWitness := by
  refine ⟨witnessInputs, 0, ![0, 1], ![1, 0], 0, 0, 0, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [exposure, witnessInputs] at this
  · intro h
    have := congrFun h 1
    simp at this
  · simp [exposure, witnessInputs, dotProduct, Fin.sum_univ_two]

theorem proof : Standalone.PairedMeanError.statement :=
  ⟨fun _ _ _ => identity,
   fun _ _ _ => universalCancellation,
   fun _ _ _ D lam lamHat alpha alphaHat a p av pv =>
     exposureMatching D lam lamHat alpha alphaHat a p av pv,
   fun _ _ _ D lam lamHat alpha alphaHat a p av pv =>
     particularCancellation D lam lamHat alpha alphaHat a p av pv,
   nonzeroWitness⟩

end Novel.PairedMeanErrorProof

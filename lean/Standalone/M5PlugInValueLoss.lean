import Mathlib.Analysis.CStarAlgebra.Matrix
import Standalone.M5PartialAdjustmentSplit

/-!
# Claim 033: the plug-in value loss and the finite-horizon Riccati stability

Statement only; the proof is `Novel/M5PlugInValueLossProof.lean`.

This is claim 030's problem (`LQ`) with the true risk matrices `S t = γΣ_t` and a plug-in problem
`Q'` that differs only in its risk matrices `S' t = γΣ~_t`. Everything else is unchanged: `T`, `Λ`,
`ρ`, the mean map and the fee. The mean map is constant (`G_t = G`), as in claim 030.
- Norms: `‖·‖` on matrices is the spectral norm (`Matrix.Norms.L2Operator`), and `vnorm v = √(v ⬝ v)`
  on vectors.
- `W` is a symmetric invertible square root of `Λ`, standing for `Λ^{1/2}`; every bound holds for
  any such `W`.
- The cost-weighted norms are `‖X‖_Λ = ‖W X W⁻¹‖` and `‖Y‖_* = ‖W⁻¹ Y W⁻¹‖`.
- `R_t = W⁻¹(γΣ_t + ρA_{t+1})W⁻¹` and `M_t = W⁻¹ A_t W⁻¹`.

**Formal scope** (lean's note to PM on claim 033): the finite-dimensional content is formalized.
- Part 1's one-step completed-square identity; summing it over reviews under the policy's
  conditional expectations is paper-level.
- Part 2's pathwise trade error and bounds; the Minkowski step to second moments and the moment
  recursion are paper-level.
- Part 3's stability bounds.
- Part 4 as their consequence on the confidence event.
- Part 5's calibrated numbers come from `checks/033` and are not formal statements.
-/

namespace Standalone.M5PlugInValueLoss

open Matrix Standalone.M5PartialAdjustmentSplit
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]

/-- The Euclidean norm of a vector. -/
def vnorm {κ : Type} [Fintype κ] (v : κ → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The plug-in problem: `Q` with its risk matrices replaced by `S'`. -/
def plugIn (Q : LQ ι π) (S' : ℕ → Matrix ι ι ℝ) : LQ ι π := { Q with S := S' }

/-- Part 1, one step: at every review and state, the Bellman objective at any trade `x` equals
the value minus `(1/2) e'D_t e`, with `e = x - (K_t x_{t-1} + L_t m_t + l_t)`. This holds for the
value `J` of claim 030's verification, under its martingale hypothesis. Summing over reviews under
the policy's conditional expectations gives the loss identity; that step is paper-level. -/
def OneStep : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π), Q.Setting → ∀ E, Martingale E →
    ∃ q : ℕ → (π → ℝ) → ℝ, (∀ m, q Q.T m = 0) ∧ ∀ t, t < Q.T → ∀ xm m x,
      Q.obj E q t xm m x = Q.J q t xm m -
        (1 / 2) * ((x - Q.policy t xm m) ⬝ᵥ (Q.D t *ᵥ (x - Q.policy t xm m)))

/-- Part 2, pathwise: the plug-in trade error is `δK x_{t-1} + δL m_t + δl`. Then
`e'D_t e ≤ ‖D_t‖_* ‖W e‖²`, `‖W e‖ ≤ ‖δK‖_Λ ‖W x_{t-1}‖ + ‖W δL‖ ‖m_t‖ + ‖W δl‖`, and
`‖D_t‖_* ≤ 1 + ‖R_t‖`. -/
def Pathwise : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π) (S' : ℕ → Matrix ι ι ℝ)
    (W : Matrix ι ι ℝ), Wᵀ = W → W * W = Q.Lam → IsUnit W → ∀ t (xm : ι → ℝ) (m : π → ℝ),
    (plugIn Q S').policy t xm m - Q.policy t xm m =
        ((plugIn Q S').K t - Q.K t) *ᵥ xm + ((plugIn Q S').L t - Q.L t) *ᵥ m +
          ((plugIn Q S').l t - Q.l t) ∧
    (∀ e : ι → ℝ, e ⬝ᵥ (Q.D t *ᵥ e) ≤ ‖W⁻¹ * Q.D t * W⁻¹‖ * vnorm (W *ᵥ e) ^ 2) ∧
    vnorm (W *ᵥ ((plugIn Q S').policy t xm m - Q.policy t xm m)) ≤
      ‖W * ((plugIn Q S').K t - Q.K t) * W⁻¹‖ * vnorm (W *ᵥ xm) +
        ‖W * ((plugIn Q S').L t - Q.L t)‖ * vnorm m + vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) ∧
    ‖W⁻¹ * Q.D t * W⁻¹‖ ≤ 1 + ‖W⁻¹ * (Q.S t + Q.rho • Q.A (t + 1)) * W⁻¹‖

/-- Part 3: non-local stability, for positive semidefinite true and plug-in risk matrices,
`ρ ∈ [0, 1]`, `Λ ≻ 0` and a constant mean map `G`. Write `dS_s = ‖S'_s - S_s‖_*` and
`dM_s = ‖δM_s‖`:
- `dM_t ≤ Σ_{s ≥ t} ρ^{s-t} dS_s`;
- `‖δK_t‖_Λ ≤ dS_t + ρ dM_{t+1}`;
- `‖W δL_t‖ ≤ Σ_{s ≥ t} ρ^{s-t} (dS_s + ρ dM_{s+1}) ‖W⁻¹G‖ (T - s)`;
- `‖W δl_t‖ ≤ Σ_{s ≥ t} ρ^{s-t} (dS_s + ρ dM_{s+1}) ‖W⁻¹e‖ (T - s)`. -/
def Stability : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π) (S' : ℕ → Matrix ι ι ℝ)
    (W : Matrix ι ι ℝ) (G : Matrix ι π ℝ),
    Q.Lam.PosDef → (∀ t, (Q.S t).PosSemidef) → (∀ t, (S' t).PosSemidef) → 0 ≤ Q.rho → Q.rho ≤ 1 →
    (∀ t, Q.G t = G) → Wᵀ = W → W * W = Q.Lam → IsUnit W →
    let dS := fun s => ‖W⁻¹ * (S' s - Q.S s) * W⁻¹‖
    let dM := fun s => ‖W⁻¹ * ((plugIn Q S').A s - Q.A s) * W⁻¹‖
    (∀ t, dM t ≤ ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * dS (t + k)) ∧
    (∀ t, t < Q.T → ‖W * ((plugIn Q S').K t - Q.K t) * W⁻¹‖ ≤ dS t + Q.rho * dM (t + 1)) ∧
    (∀ t, t < Q.T → ‖W * ((plugIn Q S').L t - Q.L t)‖ ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * (dS (t + k) + Q.rho * dM (t + k + 1)) *
        ‖W⁻¹ * G‖ * ((Q.T - (t + k) : ℕ) : ℝ)) ∧
    (∀ t, t < Q.T → vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * (dS (t + k) + Q.rho * dM (t + k + 1)) *
        vnorm (W⁻¹ *ᵥ Q.e) * ((Q.T - (t + k) : ℕ) : ℝ))

/-- Part 4: on the confidence event, where `‖S'_s - S_s‖_* ≤ r` at every review (the estimate is
made once, before the run), the bounds hold with `r` in place of every error. -/
def Guarantee : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π) (S' : ℕ → Matrix ι ι ℝ)
    (W : Matrix ι ι ℝ) (G : Matrix ι π ℝ) (r : ℝ),
    Q.Lam.PosDef → (∀ t, (Q.S t).PosSemidef) → (∀ t, (S' t).PosSemidef) → 0 ≤ Q.rho → Q.rho ≤ 1 →
    (∀ t, Q.G t = G) → Wᵀ = W → W * W = Q.Lam → IsUnit W →
    (∀ s, ‖W⁻¹ * (S' s - Q.S s) * W⁻¹‖ ≤ r) →
    (∀ t, ‖W⁻¹ * ((plugIn Q S').A t - Q.A t) * W⁻¹‖ ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k * r) ∧
    (∀ t, t < Q.T → ‖W * ((plugIn Q S').K t - Q.K t) * W⁻¹‖ ≤
      r + Q.rho * ∑ k ∈ Finset.range (Q.T - (t + 1)), Q.rho ^ k * r) ∧
    (∀ t, t < Q.T → ‖W * ((plugIn Q S').L t - Q.L t)‖ ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k *
        (r + Q.rho * ∑ j ∈ Finset.range (Q.T - (t + k + 1)), Q.rho ^ j * r) *
        ‖W⁻¹ * G‖ * ((Q.T - (t + k) : ℕ) : ℝ)) ∧
    (∀ t, t < Q.T → vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) ≤
      ∑ k ∈ Finset.range (Q.T - t), Q.rho ^ k *
        (r + Q.rho * ∑ j ∈ Finset.range (Q.T - (t + k + 1)), Q.rho ^ j * r) *
        vnorm (W⁻¹ *ᵥ Q.e) * ((Q.T - (t + k) : ℕ) : ℝ))

/-- Claim 033, parts 1-4 (part 5 is numerical). -/
def statement : Prop := OneStep ∧ Pathwise ∧ Stability ∧ Guarantee

end

end Standalone.M5PlugInValueLoss

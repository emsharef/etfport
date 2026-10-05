import Standalone.M5PlugInValueLoss

/-!
# Claim 035: the re-estimation guarantee

Statement only; the proof is `Novel/M5ReestimationGuaranteeProof.lean`.

This is claim 033's setting, with claim 030's problem `Q` holding the true risk matrices
`S_t = γΣ_t`, and `plugIn Q S'` the problem with risk path `S'`. At review `t` the manager uses
the estimate path `S' t` (`S'_{t,s} = γΣ~^{(t)}_s`), so the re-estimating policy is
`x_{t+1} = (plugIn Q (S' t)).policy t x_t m_t`. Holdings are pre-trade: `x_0` is the starting
holding, and the trade error at review `t` is
`e_t = x_{t+1} - Q.policy t x_t m_t = δK^{(t)}_t x_t + δL^{(t)}_t m_t + δl^{(t)}_t`.
- Norms are claim 033's: the spectral norm, `vnorm`, a symmetric square root `W` of `Λ`,
  `g = ‖W⁻¹G‖` and `e = vnorm(W⁻¹e)`.
- The radius `r` bounds `‖W⁻¹(S'_{t,s} - S_s)W⁻¹‖`, that is `γ δ_t` in the claim's notation.
  So the claim's `bR_s(r)` is `bR T ρ (γ r) s`.
- `Mst` bounds `vnorm m_t` at every review: the claim's `M*`, taken pathwise.

The formal content is the pathwise core:
- part 2's a priori bounds, for any positive semidefinite estimate, and the position bound;
- part 3's per-review bound on the event where the errors are at most the radii;
- part 4's per-review bound off it.

Paper-level (as for claim 033):
- part 1's loss identity in expectation for the re-estimating policy;
- splitting the expectation over the event, Cauchy-Schwarz, and Doob's inequality for `M*`;
- the existence of the event with probability at least `1 - α` (`AX-04`, used only there).
-/

namespace Standalone.M5ReestimationGuarantee

open Matrix Standalone.M5PartialAdjustmentSplit Standalone.M5PlugInValueLoss
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `bR_s(r) = r Σ_{u=s}^{T-1} ρ^{u-s}`. -/
def bR (T : ℕ) (rho r : ℝ) (s : ℕ) : ℝ := ∑ k ∈ Finset.range (T - s), rho ^ k * r

/-- `bL_t(r) = g Σ_{s=t}^{T-1} ρ^{s-t} bR_s(r) (T - s)`; with `e` in place of `g` it is `bl_t(r)`. -/
def bL (T : ℕ) (rho r g : ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (T - t), rho ^ k * bR T rho r (t + k) * g * ((T - (t + k) : ℕ) : ℝ)

/-- The position bound `X_t = ‖W x_0‖ + Σ_{s<t} [g (T - s) M* + e (T - s)]`. -/
def Xb (T : ℕ) (x0n g e Mst : ℝ) (t : ℕ) : ℝ :=
  x0n + ∑ s ∈ Finset.range t, (((T - s : ℕ) : ℝ) * g * Mst + ((T - s : ℕ) : ℝ) * e)

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π]

/-- The standing hypotheses: `Λ ≻ 0`, true and estimated risk matrices positive semidefinite,
`ρ ∈ [0, 1]`, a constant mean map, and `W` a symmetric invertible square root of `Λ`. -/
def Hyp (Q : LQ ι π) (S' : ℕ → ℕ → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (G : Matrix ι π ℝ) : Prop :=
  Q.Lam.PosDef ∧ (∀ t, (Q.S t).PosSemidef) ∧ (∀ t s, (S' t s).PosSemidef) ∧ 0 ≤ Q.rho ∧ Q.rho ≤ 1 ∧
    (∀ t, Q.G t = G) ∧ Wᵀ = W ∧ W * W = Q.Lam ∧ IsUnit W

/-- Part 2: for any positive semidefinite estimate path `S'`, the coefficients satisfy
`‖K_t‖_Λ ≤ 1`, `‖W L_t‖ ≤ g (T - t)` and `vnorm(W l_t) ≤ e (T - t)`, whatever the estimation
error. So the errors against the true coefficients are at most `2`, `2g(T - t)` and `2e(T - t)`. -/
def APriori : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π)
    (S' : ℕ → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (G : Matrix ι π ℝ),
    Hyp Q (fun _ => S') W G → ∀ t, t < Q.T →
    ‖W * (plugIn Q S').K t * W⁻¹‖ ≤ 1 ∧
    ‖W * (plugIn Q S').L t‖ ≤ ((Q.T - t : ℕ) : ℝ) * ‖W⁻¹ * G‖ ∧
    vnorm (W *ᵥ (plugIn Q S').l t) ≤ ((Q.T - t : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ Q.e) ∧
    ‖W * ((plugIn Q S').K t - Q.K t) * W⁻¹‖ ≤ 2 ∧
    ‖W * ((plugIn Q S').L t - Q.L t)‖ ≤ 2 * ((Q.T - t : ℕ) : ℝ) * ‖W⁻¹ * G‖ ∧
    vnorm (W *ᵥ ((plugIn Q S').l t - Q.l t)) ≤ 2 * ((Q.T - t : ℕ) : ℝ) * vnorm (W⁻¹ *ᵥ Q.e)

/-- Parts 2-4, pathwise, for the re-estimating policy with belief path `m` (`vnorm m_t ≤ M*`):
- the position bound `vnorm(W x_t) ≤ X_t` for `t ≤ T`;
- at every review `t < T`, `(1/2) e_t'D_t e_t ≤ Loff_t`, with
  `Loff_t = (1/2)(1 + ‖R_t‖)(2X_t + 2g(T - t)M* + 2e(T - t))²`, for any estimates;
- on the event where review `t`'s estimate has error at most `r`,
  `(1/2) e_t'D_t e_t ≤ Lon_t(r) = (1/2)(1 + ‖R_t‖)(bK_t(r) X_t + bL_t(r) M* + bl_t(r))²`.

Here `R_t = W⁻¹(S_t + ρA_{t+1})W⁻¹`. -/
def Reestimation : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] (Q : LQ ι π)
    (S' : ℕ → ℕ → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (G : Matrix ι π ℝ) (m : ℕ → π → ℝ) (Mst : ℝ)
    (x : ℕ → ι → ℝ),
    Hyp Q S' W G → (∀ t, vnorm (m t) ≤ Mst) →
    (∀ t, x (t + 1) = (plugIn Q (S' t)).policy t (x t) (m t)) →
    let g := ‖W⁻¹ * G‖
    let e := vnorm (W⁻¹ *ᵥ Q.e)
    let X := Xb Q.T (vnorm (W *ᵥ x 0)) g e Mst
    (∀ t, t ≤ Q.T → vnorm (W *ᵥ x t) ≤ X t) ∧
    ∀ t, t < Q.T →
      let err := x (t + 1) - Q.policy t (x t) (m t)
      let Rt := ‖W⁻¹ * (Q.S t + Q.rho • Q.A (t + 1)) * W⁻¹‖
      1 / 2 * (err ⬝ᵥ (Q.D t *ᵥ err)) ≤
          1 / 2 * (1 + Rt) * (2 * X t + 2 * ((Q.T - t : ℕ) : ℝ) * g * Mst + 2 * ((Q.T - t : ℕ) : ℝ) * e) ^ 2 ∧
        ∀ r : ℝ, (∀ s, ‖W⁻¹ * (S' t s - Q.S s) * W⁻¹‖ ≤ r) →
          1 / 2 * (err ⬝ᵥ (Q.D t *ᵥ err)) ≤
            1 / 2 * (1 + Rt) * (bR Q.T Q.rho r t * X t + bL Q.T Q.rho r g t * Mst +
              bL Q.T Q.rho r e t) ^ 2

/-- Claim 035, parts 2-4 (pathwise). -/
def statement : Prop := APriori ∧ Reestimation

end

end Standalone.M5ReestimationGuarantee

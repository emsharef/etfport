import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Standalone.M5MissingDirectionLeak
import Standalone.M5PartialAdjustmentSplit

/-!
# Claim 034: the plug-in value loss as a function of the inputs

Statement only; the proof is `Novel/M5PlugInLossInputsProof.lean`.

The formal content is claim 034's finite-dimensional and deterministic core. Taking expectations
over M5's Gaussian belief innovations is paper-level, as in claims 030 and 033. This covers:
- `E e_t e_t' = μ_t μ_t' + Σ_u W_{t,u} V_u W_{t,u}'`;
- `E λ̂_t λ̂_t'` and `E α̂_t²`;
- the identification of 3(i)'s expectation form of `C` with its derivative form.

**Indexing.** Holdings are pre-trade: `x_0` is the starting holding, and review `t` trades from
`x_t` to `x_{t+1} = K~_t x_t + L~_t m_t + l~_t`. The claim's `Φ_{t-1,s}` is `prodK K~ t (s+1)`,
the product `K~_{t-1} ⋯ K~_{s+1}`, and its `Φ_{t-1,-1}` is `prodK K~ t 0`.

**Part 1** is stated for arbitrary coefficient sequences: plug-in coefficients `K~, L~, l~` and
errors `δK, δL, δl`, which is more general than claim 033's. `lossF` is part 1's loss
expression in the inputs, `(1/2) Σ_t ρ^t [μ_t' D_t μ_t + Σ_{u<t} tr(D_t W_{t,u} V_u W_{t,u}')]`.

**Part 4** uses claim 030's separated problem (`BlockSep`) and claim 031's objects (`Spanning`,
`NoSpanning`).

**Part 2(b) and part 3** use one fund, or one direction, of claim 030's fund block (`Fund`):
- cost `λ_A`, risk aversion `γ`, discount `ρ`, true residual variance `σ²`, precision path `p`
  and horizon `T`;
- `aS, dS, kS, qS` are the claim's scalar recursion at a residual variance `v`: `v = σ²` for the
  true coefficients and `v = σ~²` for the plug-in ones;
- `Recursion` shows they are claim 030's `A, D, K, L` for the one-dimensional problem;
- `LossA` is 2(b)'s closed form.

The precision path is any nonnegative sequence. This covers the homogeneous prior's `p_t` and
claim 032's two directions `p^c_t, p^r_t`.
-/

namespace Standalone.M5PlugInLossInputs

open Matrix Filter Topology Asymptotics Standalone.M5PartialAdjustmentSplit Standalone.M5MissingDirectionLeak

noncomputable section

/-! ### Part 1: the loss in the inputs -/

section General

variable {ι π : Type} [Fintype ι] [Fintype π]

/-- `prodK K t s = K_{t-1} ⋯ K_s` for `s ≤ t` (the identity when `s ≥ t`). -/
def prodK [DecidableEq ι] (K : ℕ → Matrix ι ι ℝ) : ℕ → ℕ → Matrix ι ι ℝ
  | 0, _ => 1
  | t + 1, s => if s ≤ t then K t * prodK K t s else 1

/-- The plug-in path: `x_0` given, `x_{t+1} = K~_t x_t + L~_t m_t + l~_t`. -/
def path (K : ℕ → Matrix ι ι ℝ) (L : ℕ → Matrix ι π ℝ) (l : ℕ → ι → ℝ) (x0 : ι → ℝ)
    (m : ℕ → π → ℝ) : ℕ → ι → ℝ
  | 0 => x0
  | t + 1 => K t *ᵥ path K L l x0 m t + L t *ᵥ m t + l t

/-- The belief means `m_s = m_0 + Σ_{u<s} η_u`. -/
def means (m0 : π → ℝ) (η : ℕ → π → ℝ) (s : ℕ) : π → ℝ := m0 + ∑ u ∈ Finset.range s, η u

variable [DecidableEq ι]

/-- `μ_t`, the part of the trade error fixed by `(x_0, m_0)`. -/
def mu (K : ℕ → Matrix ι ι ℝ) (L : ℕ → Matrix ι π ℝ) (l : ℕ → ι → ℝ) (dK : ℕ → Matrix ι ι ℝ)
    (dL : ℕ → Matrix ι π ℝ) (dl : ℕ → ι → ℝ) (x0 : ι → ℝ) (m0 : π → ℝ) (t : ℕ) : ι → ℝ :=
  dK t *ᵥ (prodK K t 0 *ᵥ x0 + ∑ s ∈ Finset.range t, prodK K t (s + 1) *ᵥ (L s *ᵥ m0 + l s)) +
    dL t *ᵥ m0 + dl t

/-- `W_{t,u}`, the loading of the trade error on the innovation `η_u`. -/
def W (K : ℕ → Matrix ι ι ℝ) (L : ℕ → Matrix ι π ℝ) (dK : ℕ → Matrix ι ι ℝ) (dL : ℕ → Matrix ι π ℝ)
    (t u : ℕ) : Matrix ι π ℝ :=
  dK t * ∑ s ∈ Finset.Ico (u + 1) t, prodK K t (s + 1) * L s + dL t

/-- Part 1's loss expression. -/
def lossF (T : ℕ) (rho : ℝ) (D : ℕ → Matrix ι ι ℝ) (V : ℕ → Matrix π π ℝ) (mu : ℕ → ι → ℝ)
    (W : ℕ → ℕ → Matrix ι π ℝ) : ℝ :=
  1 / 2 * ∑ t ∈ Finset.range T, rho ^ t *
    (mu t ⬝ᵥ (D t *ᵥ mu t) + ∑ u ∈ Finset.range t, (D t * W t u * V u * (W t u)ᵀ).trace)

end General

/-- Part 1, pathwise:
- the plug-in path's product form;
- `e_t = δK_t x_t + δL_t m_t + δl_t = μ_t + Σ_{u<t} W_{t,u} η_u` for every innovation sequence;
- the loss expression vanishes iff every `μ_t` and every `W_{t,u}` vanish, for `D_t` and `V_u`
  positive definite and `ρ > 0`;
- zero coefficient errors give zero `μ` and `W`. -/
def Pathwise : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (K : ℕ → Matrix ι ι ℝ)
    (L : ℕ → Matrix ι π ℝ) (l : ℕ → ι → ℝ) (dK : ℕ → Matrix ι ι ℝ) (dL : ℕ → Matrix ι π ℝ)
    (dl : ℕ → ι → ℝ) (x0 : ι → ℝ) (m0 : π → ℝ) (η : ℕ → π → ℝ),
    (∀ t, path K L l x0 (means m0 η) t = prodK K t 0 *ᵥ x0 +
      ∑ s ∈ Finset.range t, prodK K t (s + 1) *ᵥ (L s *ᵥ means m0 η s + l s)) ∧
    (∀ t, dK t *ᵥ path K L l x0 (means m0 η) t + dL t *ᵥ means m0 η t + dl t =
      mu K L l dK dL dl x0 m0 t + ∑ u ∈ Finset.range t, W K L dK dL t u *ᵥ η u) ∧
    (∀ (T : ℕ) (rho : ℝ) (D : ℕ → Matrix ι ι ℝ) (V : ℕ → Matrix π π ℝ), 0 < rho →
      (∀ t, (D t).PosDef) → (∀ u, (V u).PosDef) →
      (lossF T rho D V (mu K L l dK dL dl x0 m0) (W K L dK dL) = 0 ↔
        ∀ t < T, mu K L l dK dL dl x0 m0 t = 0 ∧ ∀ u < t, W K L dK dL t u = 0)) ∧
    ((∀ t, dK t = 0 ∧ dL t = 0 ∧ dl t = 0) →
      ∀ t, mu K L l dK dL dl x0 m0 t = 0 ∧ ∀ u, W K L dK dL t u = 0)

/-! ### Part 2(a): the exposure part -/

/-- 2(a), per review: trading the exposure `y~ = (γΣ~)⁻¹ λ̂` instead of `y = (γΣ)⁻¹ λ̂` loses
`(γ/2)(y~ - y)'Σ(y~ - y) = (1/(2γ)) λ̂'Δλ̂ = (1/(2γ)) tr(Δ λ̂λ̂')`, with
`Δ = (Σ~⁻¹ - Σ⁻¹) Σ (Σ~⁻¹ - Σ⁻¹)`. -/
def Exposure : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Sig Sig' : Matrix κ κ ℝ) (gamma : ℝ) (lh : κ → ℝ),
    Sigᵀ = Sig → Sig'ᵀ = Sig' → 0 < gamma →
    let y := (1 / gamma) • (Sig⁻¹ *ᵥ lh)
    let y' := (1 / gamma) • (Sig'⁻¹ *ᵥ lh)
    let Δ := (Sig'⁻¹ - Sig⁻¹) * Sig * (Sig'⁻¹ - Sig⁻¹)
    gamma / 2 * ((y' - y) ⬝ᵥ (Sig *ᵥ (y' - y))) = 1 / (2 * gamma) * (lh ⬝ᵥ (Δ *ᵥ lh)) ∧
      lh ⬝ᵥ (Δ *ᵥ lh) = (Δ * vecMulVec lh lh).trace

/-! ### Part 2(b) and part 3: one fund -/

/-- One fund, or one direction, of claim 030's fund block. -/
structure Fund where
  lam : ℝ
  gam : ℝ
  rho : ℝ
  sig2 : ℝ
  p : ℕ → ℝ
  T : ℕ

namespace Fund

variable (F : Fund)

/-- The setting: `λ_A, γ, σ² > 0`, `ρ ∈ [0, 1]`, and a nonnegative precision path. -/
def Setting : Prop := 0 < F.lam ∧ 0 < F.gam ∧ 0 ≤ F.rho ∧ F.rho ≤ 1 ∧ 0 < F.sig2 ∧ ∀ t, 0 ≤ F.p t

/-- `a_t` at residual variance `v`: `a_t = λ_A - λ_A²/d_t`, `a_T = 0`. -/
def aS (v : ℝ) (t : ℕ) : ℝ :=
  if t < F.T then F.lam - F.lam ^ 2 / (F.lam + F.gam * (v + F.p t) + F.rho * aS v (t + 1)) else 0
termination_by F.T - t

/-- `d_t = λ_A + γ(v + p_t) + ρ a_{t+1}`. -/
def dS (v : ℝ) (t : ℕ) : ℝ := F.lam + F.gam * (v + F.p t) + F.rho * F.aS v (t + 1)

/-- `k_t = λ_A/d_t`. -/
def kS (v : ℝ) (t : ℕ) : ℝ := F.lam / F.dS v t

/-- `q_t = (1 + ρ λ_A q_{t+1})/d_t`, `q_T = 0` (the belief coefficient). -/
def qS (v : ℝ) (t : ℕ) : ℝ :=
  if t < F.T then (1 + F.rho * F.lam * qS v (t + 1)) / F.dS v t else 0
termination_by F.T - t

/-- Claim 030's problem for this fund at residual variance `v`: cost `λ_A`, risk `γ(v + p_t)`,
mean map `1` on `α̂`, and no fee. -/
def lq (v : ℝ) : LQ (Fin 1) (Fin 1) where
  T := F.T
  Lam := F.lam • 1
  S := fun t => (F.gam * (v + F.p t)) • 1
  rho := F.rho
  G := fun _ => 1
  e := 0

/-- The scalar product `k_{t-1} ⋯ k_s` at residual variance `v`. -/
def pk (v : ℝ) (t s : ℕ) : ℝ := ∏ j ∈ Finset.Ico s t, F.kS v j

/-- 2(b)'s `μ_t` for the plug-in residual variance `v'`, starting holding `x0` and prior mean
`a0`. -/
def muA (v' x0 a0 : ℝ) (t : ℕ) : ℝ :=
  (F.kS v' t - F.kS F.sig2 t) * F.pk v' t 0 * x0 +
    ((F.kS v' t - F.kS F.sig2 t) * ∑ s ∈ Finset.range t, F.pk v' t (s + 1) * F.qS v' s +
      (F.qS v' t - F.qS F.sig2 t)) * a0

/-- 2(b)'s `w_{t,u}`. -/
def wA (v' : ℝ) (t u : ℕ) : ℝ :=
  (F.kS v' t - F.kS F.sig2 t) * ∑ s ∈ Finset.Ico (u + 1) t, F.pk v' t (s + 1) * F.qS v' s +
    (F.qS v' t - F.qS F.sig2 t)

/-- 2(b)'s fund loss, `(1/2) Σ_t ρ^t d_t [μ_t² + Σ_{u<t} w_{t,u}² v_u]` with `v_u = p_u - p_{u+1}`. -/
def LossA (v' x0 a0 : ℝ) : ℝ :=
  1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * F.dS F.sig2 t *
    (F.muA v' x0 a0 t ^ 2 + ∑ u ∈ Finset.range t, F.wA v' t u ^ 2 * (F.p u - F.p (u + 1)))

/-- `a'_t`, the derivative of `a_t` in the residual variance at `σ²`: `a'_t = λ_A² d'_t/d_t²` with
`d'_t = γ + ρ a'_{t+1}`, `a'_T = 0`. -/
def aP (t : ℕ) : ℝ :=
  if t < F.T then F.lam ^ 2 * (F.gam + F.rho * aP (t + 1)) / F.dS F.sig2 t ^ 2 else 0
termination_by F.T - t

/-- `d'_t = γ + ρ a'_{t+1}`. -/
def dP (t : ℕ) : ℝ := F.gam + F.rho * F.aP (t + 1)

/-- `k'_t = -λ_A d'_t/d_t²`. -/
def kP (t : ℕ) : ℝ := -(F.lam * F.dP t) / F.dS F.sig2 t ^ 2

/-- `q'_t = (ρ λ_A q'_{t+1} d_t - (1 + ρ λ_A q_{t+1}) d'_t)/d_t²`, `q'_T = 0`. -/
def qP (t : ℕ) : ℝ :=
  if t < F.T then (F.rho * F.lam * qP (t + 1) * F.dS F.sig2 t -
    (1 + F.rho * F.lam * F.qS F.sig2 (t + 1)) * F.dP t) / F.dS F.sig2 t ^ 2 else 0
termination_by F.T - t

/-- 3(i)'s constant, with the derivatives of `μ_t` and `w_{t,u}` at `ε = 0` on the true path. -/
def C (x0 a0 : ℝ) : ℝ :=
  1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * F.dS F.sig2 t *
    ((F.kP t * F.pk F.sig2 t 0 * x0 +
        (F.kP t * ∑ s ∈ Finset.range t, F.pk F.sig2 t (s + 1) * F.qS F.sig2 s + F.qP t) * a0) ^ 2 +
      ∑ u ∈ Finset.range t,
        (F.kP t * ∑ s ∈ Finset.Ico (u + 1) t, F.pk F.sig2 t (s + 1) * F.qS F.sig2 s + F.qP t) ^ 2 *
          (F.p u - F.p (u + 1)))

/-- The fund with cost `λ` in place of `λ_A`. -/
def withLam (lam : ℝ) : Fund := { F with lam := lam }

end Fund

/-- The recursion is claim 030's: for `t < T`, `a_t, d_t, k_t, q_t` are the entries of claim 030's
`A_t, D_t, K_t, L_t` for the one-dimensional problem, at every residual variance `v`. -/
def Recursion : Prop :=
  ∀ (F : Fund) (v : ℝ) (t : ℕ), t < F.T →
    (F.lq v).A t 0 0 = F.aS v t ∧ (F.lq v).D t 0 0 = F.dS v t ∧ (F.lq v).K t 0 0 = F.kS v t ∧
      (F.lq v).L t 0 0 = F.qS v t

/-- 2(b), pathwise: with `x_{t+1} = k~_t x_t + q~_t α̂_t` and `α̂_s = α̂_0 + Σ_{u<s} η_u`, the trade
error `δk_t x_t + δq_t α̂_t` is `μ_t + Σ_{u<t} w_{t,u} η_u`. -/
def FundPath : Prop :=
  ∀ (F : Fund) (v' x0 a0 : ℝ) (η : ℕ → ℝ) (x : ℕ → ℝ),
    x 0 = x0 → (∀ t, x (t + 1) = F.kS v' t * x t + F.qS v' t * (a0 + ∑ u ∈ Finset.range t, η u)) →
    ∀ t, (F.kS v' t - F.kS F.sig2 t) * x t +
        (F.qS v' t - F.qS F.sig2 t) * (a0 + ∑ u ∈ Finset.range t, η u) =
      F.muA v' x0 a0 t + ∑ u ∈ Finset.range t, F.wA v' t u * η u

/-- 3(i): `k'_t` and `q'_t` are the derivatives of the true coefficients in the residual
variance, and the loss is `C ε² + O(ε³)` in the error `ε = σ~² - σ²`. -/
def Quadratic : Prop :=
  ∀ F : Fund, F.Setting → ∀ x0 a0 : ℝ,
    (∀ t, t < F.T → HasDerivAt (fun v => F.kS v t) (F.kP t) F.sig2 ∧
      HasDerivAt (fun v => F.qS v t) (F.qP t) F.sig2) ∧
    (fun ε => F.LossA (F.sig2 + ε) x0 a0 - F.C x0 a0 * ε ^ 2) =O[𝓝 0] fun ε => ε ^ 3

/-- 3(ii): as the fund cost vanishes, the loss tends to the myopic loss
`(1/2) Σ_t ρ^t r_t (1/r~_t - 1/r_t)² (α̂_0² + p_0 - p_t)`, and the starting holding drops out. -/
def Costless : Prop :=
  ∀ F : Fund, F.Setting → ∀ v' x0 a0 : ℝ, 0 < v' →
    Tendsto (fun lam => (F.withLam lam).LossA v' x0 a0) (𝓝[>] 0)
      (𝓝 (1 / 2 * ∑ t ∈ Finset.range F.T, F.rho ^ t * (F.gam * (F.sig2 + F.p t)) *
        (1 / (F.gam * (v' + F.p t)) - 1 / (F.gam * (F.sig2 + F.p t))) ^ 2 *
          (a0 ^ 2 + (F.p 0 - F.p t))))

/-- 3(iii): as the fund cost grows, the loss is `O(1/λ_A)`. -/
def Costly : Prop :=
  ∀ F : Fund, F.Setting → ∀ v' x0 a0 : ℝ, 0 < v' →
    (fun lam => (F.withLam lam).LossA v' x0 a0) =O[atTop] fun lam => 1 / lam

/-- 3(iii), the order: for `x_0 ≠ 0`, a nonzero error and `T ≥ 1`, the loss is at least `c/λ_A` for large
`λ_A`, so `1/λ_A` is its exact order; for `x_0 = 0` it is `O(1/λ_A³)`. -/
def CostlyOrder : Prop :=
  ∀ F : Fund, F.Setting → ∀ v' x0 a0 : ℝ, 0 < v' →
    (x0 ≠ 0 → v' ≠ F.sig2 → 1 ≤ F.T →
      ∃ c > 0, ∀ᶠ lam in atTop, c / lam ≤ (F.withLam lam).LossA v' x0 a0) ∧
    (x0 = 0 → (fun lam => (F.withLam lam).LossA v' x0 a0) =O[atTop] fun lam => 1 / lam ^ 3)

/-- 3(iv): at `T = 1` the loss is `(1/2)(λ_A + r_0)[(λ_A x_0 + α̂_0)(1/(λ_A + r~_0) - 1/(λ_A + r_0))]²`.
With `α̂_0 = 0`, `x_0 ≠ 0` and `σ~² ≠ σ²`, it is positive for every `λ_A > 0` and tends to `0` both
as `λ_A → 0` and as `λ_A → ∞`, so it is not monotone in `λ_A`. -/
def OneReview : Prop :=
  ∀ F : Fund, F.Setting → F.T = 1 → ∀ v' x0 a0 : ℝ, 0 < v' →
    F.LossA v' x0 a0 = 1 / 2 * (F.lam + F.gam * (F.sig2 + F.p 0)) *
      ((F.lam * x0 + a0) * (1 / (F.lam + F.gam * (v' + F.p 0)) -
        1 / (F.lam + F.gam * (F.sig2 + F.p 0)))) ^ 2 ∧
    (a0 = 0 → x0 ≠ 0 → v' ≠ F.sig2 →
      (∀ lam, 0 < lam → 0 < (F.withLam lam).LossA v' x0 a0) ∧
      Tendsto (fun lam => (F.withLam lam).LossA v' x0 a0) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun lam => (F.withLam lam).LossA v' x0 a0) atTop (𝓝 0))

/-- 3(v): a more precise prior lowers every posterior variance: `p_t = 1/(1/s² + t/σ²)` is
increasing in `s²`. -/
def Precision : Prop :=
  ∀ (sig2 : ℝ) (t : ℕ), 0 < sig2 → StrictMonoOn (fun s2 => pvar s2 sig2 t) (Set.Ioi 0)

/-! ### Part 4: spanning -/

/-- Part 4, the separated case (claim 030's part 4(a), with the problems written in `(y, x^A)`):
two separated problems with the same cost, discount and horizon have the same fund positions when
their fund risk blocks agree, whatever their exposure risk blocks. They have the same exposures
when their exposure risk blocks agree, whatever their fund risk blocks. So the factor-covariance
estimate (in `Sy`) and the residual-variance estimate (in `SA`) each enter only their own block. -/
def BlockSep : Prop :=
  ∀ (K N : ℕ) (Q Q' : LQ (Fin K ⊕ Fin N) (Fin K ⊕ Fin N)) (LA : Matrix (Fin N) (Fin N) ℝ)
    (Sy Sy' : ℕ → Matrix (Fin K) (Fin K) ℝ) (SA SA' : ℕ → Matrix (Fin N) (Fin N) ℝ),
    Q.Setting → Q'.Setting → Q'.T = Q.T → Q'.rho = Q.rho →
    Q.Lam = Matrix.fromBlocks 0 0 0 LA → Q'.Lam = Matrix.fromBlocks 0 0 0 LA →
    (∀ t, Q.S t = Matrix.fromBlocks (Sy t) 0 0 (SA t)) → (∀ t, Q'.S t = Matrix.fromBlocks (Sy' t) 0 0 (SA' t)) →
    (∀ t, Q.G t = 1) → (∀ t, Q'.G t = 1) → Q.e = 0 → Q'.e = 0 →
    ∀ t, t < Q.T → ∀ (y : Fin K → ℝ) (xA : Fin N → ℝ) (lh : Fin K → ℝ) (ah : Fin N → ℝ),
      (SA' = SA → ∀ i, Q'.policy t (Sum.elim y xA) (Sum.elim lh ah) (Sum.inr i) =
        Q.policy t (Sum.elim y xA) (Sum.elim lh ah) (Sum.inr i)) ∧
      (Sy' = Sy → ∀ k, Q'.policy t (Sum.elim y xA) (Sum.elim lh ah) (Sum.inl k) =
        Q.policy t (Sum.elim y xA) (Sum.elim lh ah) (Sum.inl k))

/-- Part 4, spanning (claim 031's setting): if every fund loading is replicable (`Π_U B^A' = 0`),
replacing the predictive factor covariance by any other positive definite path leaves the reduced
fund problem, and so the joint policy's fund positions, unchanged. -/
def Spanning : Prop :=
  ∀ (K N M : ℕ) (P : Leak K N M) (St' : ℕ → Matrix (Fin K) (Fin K) ℝ), P.Setting →
    (∀ t, (St' t).PosDef) → PiU P.BE * P.BAᵀ = 0 →
    ({ P with St := St' } : Leak K N M).red = P.red ∧
      ∀ t, t < P.T → ∀ (xm : Fin N ⊕ Fin M → ℝ) (m : Fin K ⊕ Fin N → ℝ) (i : Fin N),
        ({ P with St := St' } : Leak K N M).joint.policy t xm m (Sum.inl i) = P.joint.policy t xm m (Sum.inl i)

/-- Part 4, without spanning: if some fund loading has an unreachable component, doubling the
factor covariance changes the fund coefficient `K_{T-1}`, so the fund positions depend on the
factor-covariance estimate. -/
def NoSpanning : Prop :=
  ∀ (K N M : ℕ) (P : Leak K N M), P.Setting → PiU P.BE * P.BAᵀ ≠ 0 → 1 ≤ P.T →
    ({ P with St := fun t => (2 : ℝ) • P.St t } : Leak K N M).red.K (P.T - 1) ≠ P.red.K (P.T - 1)

/-- Claim 034, parts 1-4. -/
def statement : Prop :=
  Pathwise ∧ Exposure ∧ Recursion ∧ FundPath ∧ Quadratic ∧ Costless ∧ Costly ∧ CostlyOrder ∧
    OneReview ∧ Precision ∧ BlockSep ∧ Spanning ∧ NoSpanning

end

end Standalone.M5PlugInLossInputs

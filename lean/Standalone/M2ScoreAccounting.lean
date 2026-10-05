import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

/-!
# Claim 003: M2 score accounting and dependence on the belief mean

Statement only; the proof is `Novel/M2ScoreAccountingProof.lean`.

The M2 objects of `model/SPEC.md` (with the M1 definitions M2 inherits), written for arbitrary
counts: m active funds, n ETFs, K factors. M2's instance is m = 1, n ∈ {1, 2}, K = 2, a special
case. Instruments are indexed by `Fin m ⊕ Fin n`, active funds first. Scenarios form a finite
type `S` with masses `q`; the parameter support Θ is a finite type `T` with a map `par` to
parameter values `θ = (λ, α)`, and a belief is a mass function `pi` on `T`.

Every part lists exactly the hypotheses its proof uses. The claim fixes a full M2 instance
(nonnegative rates below one, gamma ≥ 0, nonnegative masses, compliant initial holdings, positive
gross returns); the formal parts drop those hypotheses where unused, so each formal part is at
least as strong as the corresponding prose. The identities are stated for every holding `w`,
not only for `w ∈ F`.
-/

namespace Standalone.M2ScoreAccounting

open Matrix

/-- Instruments: m active funds, then n ETFs. -/
abbrev Inst (m n : ℕ) := Fin m ⊕ Fin n

/-- A parameter value `θ = (λ, α)`: factor premia and active alphas. -/
structure Params (m K : ℕ) where
  lam : Fin K → ℝ
  alpha : Fin m → ℝ

/-- The fixed data of an M2 instance other than the belief and its support. -/
structure Data (m n K : ℕ) (S : Type) where
  /-- Active loadings `B^A` (funds × factors). -/
  BA : Matrix (Fin m) (Fin K) ℝ
  /-- ETF loadings `B^E` (ETFs × factors). -/
  BE : Matrix (Fin n) (Fin K) ℝ
  /-- ETF fee and tracking drag `c^E`, of either sign. -/
  cE : Fin n → ℝ
  /-- Purchase rates `κ⁺`. -/
  kplus : Inst m n → ℝ
  /-- Sale rates `κ⁻`. -/
  kminus : Inst m n → ℝ
  /-- Risk coefficient `γ`. -/
  gamma : ℝ
  /-- Scenario masses `q_s`. -/
  q : S → ℝ
  /-- Factor shocks `z^f_s`. -/
  zf : S → Fin K → ℝ
  /-- Active residuals `z^A_s`. -/
  zA : S → Fin m → ℝ
  /-- ETF residuals `z^E_s`. -/
  zE : S → Fin n → ℝ
  /-- Initial dollar holdings `x⁻`. -/
  x0 : Inst m n → ℝ
  /-- Initial dollar cash `h⁻`. -/
  h0 : ℝ
  /-- Position limits `w̄`, fractions of pre-trade wealth. -/
  wbar : Inst m n → ℝ

noncomputable section

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- Pre-trade wealth `W⁻ = h⁻ + Σᵢ x⁻ᵢ`. -/
def W0 (D : Data m n K S) : ℝ := D.h0 + ∑ i, D.x0 i

/-- Normalized initial holdings `w⁻ = x⁻ / W⁻`. -/
def w0 (D : Data m n K S) : Inst m n → ℝ := fun i => D.x0 i / W0 D

/-- Normalized initial cash `k⁻ = h⁻ / W⁻`. -/
def k0 (D : Data m n K S) : ℝ := D.h0 / W0 D

/-- Dollar cost `C_0(u) = Σᵢ [κ⁺ᵢ max(uᵢ, 0) + κ⁻ᵢ max(-uᵢ, 0)]`. -/
def cost (D : Data m n K S) (u : Inst m n → ℝ) : ℝ :=
  ∑ i, (D.kplus i * max (u i) 0 + D.kminus i * max (-u i) 0)

/-- Normalized cost `τ(v) = Σᵢ [κ⁺ᵢ max(vᵢ, 0) + κ⁻ᵢ max(-vᵢ, 0)]`. -/
def tau (D : Data m n K S) (v : Inst m n → ℝ) : ℝ :=
  ∑ i, (D.kplus i * max (v i) 0 + D.kminus i * max (-v i) 0)

/-- Normalized post-trade cash `k(w) = k⁻ - Σᵢ (wᵢ - w⁻ᵢ) - τ(w - w⁻)`. -/
def cash (D : Data m n K S) (w : Inst m n → ℝ) : ℝ :=
  k0 D - ∑ i, (w i - w0 D i) - tau D (w - w0 D)

/-- Dollar post-trade holdings `x⁺ = x⁻ + u`. -/
def postHoldings (D : Data m n K S) (u : Inst m n → ℝ) : Inst m n → ℝ := D.x0 + u

/-- Dollar post-trade cash `h⁺ = h⁻ - Σᵢ uᵢ - C_0(u)`. -/
def postCash (D : Data m n K S) (u : Inst m n → ℝ) : ℝ := D.h0 - ∑ i, u i - cost D u

/-- Active part `a` of a holding `w = (a, p)`. -/
def active (w : Inst m n → ℝ) : Fin m → ℝ := fun j => w (Sum.inl j)

/-- ETF part `p` of a holding `w = (a, p)`. -/
def etf (w : Inst m n → ℝ) : Fin n → ℝ := fun j => w (Sum.inr j)

/-- Full action class `F = {w : 0 ≤ wᵢ ≤ w̄ᵢ, k(w) ≥ 0}`. -/
def F (D : Data m n K S) : Set (Inst m n → ℝ) :=
  {w | (∀ i, 0 ≤ w i ∧ w i ≤ D.wbar i) ∧ 0 ≤ cash D w}

/-- ETF-only class `E = {w ∈ F : a = a⁻}`. -/
def E (D : Data m n K S) : Set (Inst m n → ℝ) :=
  {w | w ∈ F D ∧ active w = active (w0 D)}

/-- No trade `N = {w⁻}`. -/
def N (D : Data m n K S) : Set (Inst m n → ℝ) := {w0 D}

/-- Factor exposure `b(w) = (B^A)' a + (B^E)' p`. -/
def exposure (D : Data m n K S) (w : Inst m n → ℝ) : Fin K → ℝ :=
  D.BAᵀ *ᵥ active w + D.BEᵀ *ᵥ etf w

/-- Scenario returns `r_s(θ)`: `r^A = B^A (λ + z^f_s) + α + z^A_s`,
`r^E = B^E (λ + z^f_s) - c^E + z^E_s`. -/
def ret (D : Data m n K S) (θ : Params m K) (s : S) : Inst m n → ℝ :=
  Sum.elim (D.BA *ᵥ (θ.lam + D.zf s) + θ.alpha + D.zA s)
    (D.BE *ᵥ (θ.lam + D.zf s) - D.cE + D.zE s)

/-- Conditional mean vector `μ(θ) = (B^A λ + α, B^E λ - c^E)`. -/
def mu (D : Data m n K S) (θ : Params m K) : Inst m n → ℝ :=
  Sum.elim (D.BA *ᵥ θ.lam + θ.alpha) (D.BE *ᵥ θ.lam - D.cE)

/-- Scenario shock vector `ξ_s = (B^A z^f_s + z^A_s, B^E z^f_s + z^E_s)`. -/
def xi (D : Data m n K S) (s : S) : Inst m n → ℝ :=
  Sum.elim (D.BA *ᵥ D.zf s + D.zA s) (D.BE *ᵥ D.zf s + D.zE s)

/-- Return covariance `Σ = Σ_s q_s ξ_s ξ_s'`. -/
def covariance (D : Data m n K S) : Matrix (Inst m n) (Inst m n) ℝ :=
  fun i j => ∑ s, D.q s * (xi D s i * xi D s j)

/-- Terminal marked wealth `W_1(w; θ, s) = W⁻ [k(w) + Σᵢ wᵢ (1 + r_{i,s}(θ))]`. -/
def W1 (D : Data m n K S) (w : Inst m n → ℝ) (θ : Params m K) (s : S) : ℝ :=
  W0 D * (cash D w + ∑ i, w i * (1 + ret D θ s i))

/-- Normalized terminal gain `G_s(w; θ) = W_1(w; θ, s) / W⁻ - 1`. -/
def gain (D : Data m n K S) (w : Inst m n → ℝ) (θ : Params m K) (s : S) : ℝ :=
  W1 D w θ s / W0 D - 1

/-- Finite conditional mean `E_q X = Σ_s q_s X_s`. -/
def condMean (D : Data m n K S) (X : S → ℝ) : ℝ := ∑ s, D.q s * X s

/-- Finite conditional variance `Var_q X = Σ_s q_s (X_s - E_q X)²`. -/
def condVar (D : Data m n K S) (X : S → ℝ) : ℝ := ∑ s, D.q s * (X s - condMean D X) ^ 2

/-- The conditional score
`Q_0(w; θ) = b(w)' λ + a' α - p' c^E - (γ/2) w' Σ w - τ(w - w⁻)`. -/
def score (D : Data m n K S) (w : Inst m n → ℝ) (θ : Params m K) : ℝ :=
  exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE
    - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D)

/-- The belief-average criterion `Q̄_0(w) = Σ_θ π_θ Q_0(w; θ)`. -/
def beliefScore (D : Data m n K S) {T : Type} [Fintype T] (par : T → Params m K)
    (pi : T → ℝ) (w : Inst m n → ℝ) : ℝ :=
  ∑ t, pi t * score D w (par t)

/-- The belief mean `θ̄ = (Σ π_θ λ, Σ π_θ α)`; not asserted to be in the support. -/
def beliefMean {T : Type} [Fintype T] (par : T → Params m K) (pi : T → ℝ) : Params m K :=
  ⟨∑ t, pi t • (par t).lam, ∑ t, pi t • (par t).alpha⟩

/-- Maximizers of `f` on `A`, whether or not any exist. -/
def maximizers (f : (Inst m n → ℝ) → ℝ) (A : Set (Inst m n → ℝ)) : Set (Inst m n → ℝ) :=
  {w | w ∈ A ∧ ∀ w' ∈ A, f w' ≤ f w}

/-- Scenario masses sum to one. -/
def MassesSumToOne (D : Data m n K S) : Prop := ∑ s, D.q s = 1

/-- Each shock has q-mean zero. -/
def CenteredShocks (D : Data m n K S) : Prop :=
  ∑ s, D.q s • D.zf s = 0 ∧ ∑ s, D.q s • D.zA s = 0 ∧ ∑ s, D.q s • D.zE s = 0

/-- `C_0(W⁻ v) / W⁻ = τ(v)` for every normalized trade `v`. -/
def CostNormalization : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S), 0 < W0 D →
    ∀ v : Inst m n → ℝ, cost D (W0 D • v) / W0 D = tau D v

/-- Transfer of the dollar funding equations to M2's normalization: with `v = w - w⁻` and
`u = W⁻ v`, `x⁺ = W⁻ w`, `h⁺ = W⁻ k(w)`, and `Σᵢ wᵢ + k(w) + τ(v) = 1`. -/
def FundingTransfer : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S), 0 < W0 D →
    ∀ w : Inst m n → ℝ,
      postHoldings D (W0 D • (w - w0 D)) = W0 D • w ∧
      postCash D (W0 D • (w - w0 D)) = W0 D * cash D w ∧
      ∑ i, w i + cash D w + tau D (w - w0 D) = 1

/-- `G_s(w; θ) = w' r_s(θ) - τ(v)` for every holding, parameter value and scenario. -/
def GainIdentity : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S), 0 < W0 D →
    ∀ (w : Inst m n → ℝ) (θ : Params m K) (s : S),
      gain D w θ s = w ⬝ᵥ ret D θ s - tau D (w - w0 D)

/-- `w' μ(θ) = b(w)' λ + a' α - p' c^E`. -/
def MeanReturnFormula : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (w : Inst m n → ℝ)
    (θ : Params m K),
    w ⬝ᵥ mu D θ = exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE

/-- Conditional moments of the gain and the score identity:
`E_q G = w' μ(θ) - τ(v)`, `Var_q G = w' Σ w`, `Q_0 = E_q G - (γ/2) Var_q G`. -/
def MomentIdentities : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S),
    0 < W0 D → MassesSumToOne D → CenteredShocks D →
    ∀ (w : Inst m n → ℝ) (θ : Params m K),
      condMean D (gain D w θ) = w ⬝ᵥ mu D θ - tau D (w - w0 D) ∧
      condVar D (gain D w θ) = w ⬝ᵥ (covariance D *ᵥ w) ∧
      score D w θ = condMean D (gain D w θ) - D.gamma / 2 * condVar D (gain D w θ)

/-- For belief masses summing to one (no sign needed), `Q̄_0(w) = Q_0(w; θ̄)` at every `w`. -/
def BeliefAverage : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi : T → ℝ),
    ∑ t, pi t = 1 → ∀ w : Inst m n → ℝ, beliefScore D par pi w = score D w (beliefMean par pi)

/-- For nonnegative belief masses summing to one, if every gross return is positive at every
support point and scenario, the affine return formula at `θ̄` has positive gross returns. -/
def BeliefMeanPositive : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi : T → ℝ),
    (∀ t, 0 ≤ pi t) → ∑ t, pi t = 1 → (∀ t s i, 0 < 1 + ret D (par t) s i) →
      ∀ s i, 0 < 1 + ret D (beliefMean par pi) s i

/-- Two beliefs on the same support with the same mean give the same criterion at every
holding, the same rankings, and the same maximizer sets on F, E and N (attained or not). -/
def SameMeanSameDecisions : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi pi' : T → ℝ),
    ∑ t, pi t = 1 → ∑ t, pi' t = 1 → beliefMean par pi = beliefMean par pi' →
      (∀ w, beliefScore D par pi w = beliefScore D par pi' w) ∧
      (∀ w w', beliefScore D par pi w ≤ beliefScore D par pi w' ↔
        beliefScore D par pi' w ≤ beliefScore D par pi' w') ∧
      maximizers (beliefScore D par pi) (F D) = maximizers (beliefScore D par pi') (F D) ∧
      maximizers (beliefScore D par pi) (E D) = maximizers (beliefScore D par pi') (E D) ∧
      maximizers (beliefScore D par pi) (N D) = maximizers (beliefScore D par pi') (N D)

end

/-- Claim 003, all parts. -/
def statement : Prop :=
  CostNormalization ∧ FundingTransfer ∧ GainIdentity ∧ MeanReturnFormula ∧
    MomentIdentities ∧ BeliefAverage ∧ BeliefMeanPositive ∧ SameMeanSameDecisions

end Standalone.M2ScoreAccounting

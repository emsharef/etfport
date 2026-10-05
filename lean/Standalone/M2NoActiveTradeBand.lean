import Mathlib.Order.Filter.Extr
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Notation
import Standalone.M2ActionClasses

/-!
# Claim 009: the M2 no-active-trade band after ETF optimization, including binding bounds

Statement only; the proof is `Novel/M2NoActiveTradeBandProof.lean`.

Setting: any M2 instance (claim 003's formal objects) with one active fund and `n` ETFs
(`Inst 1 n`), any number `K` of factors, any finite scenario type `S` and any finite parameter
support `T` with masses `pi`. M2's `n ∈ {1, 2}` is a special case.

The translated-alpha family replaces every support point `(λ_h, α_h)` by
`(λ_h, α_h - ᾱ₀ + x)`; `Qx x` is the family's criterion `Q̄_0`, defined for every real `x`
(an algebraic extension outside `J`). `C` is the set of `x` for which some F-maximizer has
`a = a⁻`. For a fixed ETF-only maximizer `w_E`, the smooth ETF marginals `g_E`, the centering
value `α_c`, the ETF cost-slope endpoints `ℓ_j`, `u_j`, the multiplier set `I`, its endpoints `lo`,
`hi` (`hi` finite exactly when `HiFinite`), and the band endpoints `L`, `U` are defined as in the
claim. `b = κ⁺_A`, `s = κ⁻_A`, `a⁻ = w⁻_A`, `ā = w̄_A`.
-/

namespace Standalone.M2NoActiveTradeBand

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses

variable {n K : ℕ} {S : Type} [Fintype S] {T : Type} [Fintype T]

/-! ### The alpha family -/

/-- `ᾱ₀ = Σ_h π_h α_h`. -/
def abar0 (par : T → Params 1 K) (pi : T → ℝ) : ℝ := ∑ h, pi h * (par h).alpha 0

/-- The translated support: `(λ_h, α_h - ᾱ₀ + x)`. -/
def famPar (par : T → Params 1 K) (pi : T → ℝ) (x : ℝ) : T → Params 1 K :=
  fun h => ⟨(par h).lam, fun _ => (par h).alpha 0 - abar0 par pi + x⟩

/-- The family's criterion at active belief mean `x`. -/
noncomputable def Qx (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (x : ℝ) :
    (Inst 1 n → ℝ) → ℝ :=
  beliefScore D (famPar par pi x) pi

/-- `J`: the `x` at which every active gross return is positive. -/
def Jset (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) : Set ℝ :=
  {x | ∀ h s, 0 < 1 + ret D (famPar par pi x h) s (Sum.inl 0)}

/-- The term whose maximum is `α_min`. -/
def alphaMinTerm (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (h : T) (s : S) : ℝ :=
  -1 - (D.BA *ᵥ (par h).lam) 0 - (par h).alpha 0 + abar0 par pi - xi D s (Sum.inl 0)

/-- `C`: some full-class maximizer has no active trade. -/
def Cset (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) : Set ℝ :=
  {x | ∃ w ∈ F D, IsMaxOn (Qx D par pi x) (F D) w ∧ w (Sum.inl 0) = w0 D (Sum.inl 0)}

/-! ### Quantities at a fixed ETF-only maximizer `w_E` -/

/-- `λ̄`, the belief-mean factor premia. -/
def lamBar (par : T → Params 1 K) (pi : T → ℝ) : Fin K → ℝ := (beliefMean par pi).lam

/-- Smooth ETF marginals `g_E,j = μ_E,j - γ (Σ w_E)_E,j`. -/
noncomputable def gE (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) (j : Fin n) : ℝ :=
  (D.BE *ᵥ lamBar par pi) j - D.cE j - D.gamma * (covariance D *ᵥ wE) (Sum.inr j)

/-- `α_c = γ (Σ w_E)_A - B^A λ̄`. -/
noncomputable def alphaC (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : ℝ :=
  D.gamma * (covariance D *ᵥ wE) (Sum.inl 0) - (D.BA *ᵥ lamBar par pi) 0

/-- Lower ETF cost-slope endpoint `ℓ_j`: `κ⁺` at a purchase, `-κ⁻` at a sale or no trade. -/
noncomputable def ellE (D : Data 1 n K S) (wE : Inst 1 n → ℝ) (j : Fin n) : ℝ :=
  if w0 D (Sum.inr j) < wE (Sum.inr j) then D.kplus (Sum.inr j) else -D.kminus (Sum.inr j)

/-- Upper ETF cost-slope endpoint `u_j`: `-κ⁻` at a sale, `κ⁺` at a purchase or no trade. -/
noncomputable def uE (D : Data 1 n K S) (wE : Inst 1 n → ℝ) (j : Fin n) : ℝ :=
  if wE (Sum.inr j) < w0 D (Sum.inr j) then -D.kminus (Sum.inr j) else D.kplus (Sum.inr j)

/-- The compatible budget multipliers `I`. -/
def Iset (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (wE : Inst 1 n → ℝ) :
    Set ℝ :=
  {η | 0 ≤ η ∧ η * cash D wE = 0 ∧
    ∀ j, (wE (Sum.inr j) < D.wbar (Sum.inr j) →
            gE D par pi wE j ≤ uE D wE j + (1 + uE D wE j) * η) ∧
         (0 < wE (Sum.inr j) →
            ellE D wE j + (1 + ellE D wE j) * η ≤ gE D par pi wE j)}

/-- The lower-bound candidates `{0} ∪ {(g_E,j - u_j)/(1 + u_j) : p_E,j < p̄_j}`. -/
noncomputable def loSet (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : Finset ℝ :=
  insert 0 ((Finset.univ.filter fun j => wE (Sum.inr j) < D.wbar (Sum.inr j)).image
    fun j => (gE D par pi wE j - uE D wE j) / (1 + uE D wE j))

/-- The upper-bound candidates `{(g_E,j - ℓ_j)/(1 + ℓ_j) : p_E,j > 0}`. -/
noncomputable def hiSet (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : Finset ℝ :=
  (Finset.univ.filter fun j => 0 < wE (Sum.inr j)).image
    fun j => (gE D par pi wE j - ellE D wE j) / (1 + ellE D wE j)

/-- `lo`: zero if `k_E > 0`, otherwise the maximum of `loSet`. -/
noncomputable def lo (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : ℝ :=
  if 0 < cash D wE then 0 else (loSet D par pi wE).max' (Finset.insert_nonempty _ _)

/-- `hi` is finite exactly when `k_E > 0` or some ETF holding at `w_E` is positive. -/
def HiFinite (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (wE : Inst 1 n → ℝ) :
    Prop :=
  0 < cash D wE ∨ (hiSet D par pi wE).Nonempty

/-- `hi`: zero if `k_E > 0`, otherwise the minimum of `hiSet` (meaningful when `HiFinite`). -/
noncomputable def hi (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : ℝ :=
  if 0 < cash D wE then 0 else
    if h : (hiSet D par pi wE).Nonempty then (hiSet D par pi wE).min' h else 0

/-- `L = α_c - s + (1 - s) lo`. -/
noncomputable def Lb (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : ℝ :=
  alphaC D par pi wE - D.kminus (Sum.inl 0) + (1 - D.kminus (Sum.inl 0)) * lo D par pi wE

/-- `U = α_c + b + (1 + b) hi`. -/
noncomputable def Ub (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)
    (wE : Inst 1 n → ℝ) : ℝ :=
  alphaC D par pi wE + D.kplus (Sum.inl 0) + (1 + D.kplus (Sum.inl 0)) * hi D par pi wE

/-- The M2 restrictions the result uses: compliant start, nonnegative rates below one, limits at
most one, `γ ≥ 0`, nonnegative scenario masses summing to one, belief masses summing to one. -/
def BandSetting (D : Data 1 n K S) (pi : T → ℝ) : Prop :=
  InitialPosition D ∧ RatesNonneg D ∧ (∀ i, D.kplus i < 1 ∧ D.kminus i < 1) ∧
  (∀ i, D.wbar i ≤ 1) ∧ 0 ≤ D.gamma ∧ (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧ ∑ h, pi h = 1

/-! ### The parts of the claim -/

/-- The family: only active returns move; the family's belief-mean alpha is `x`; `J` is
`{x > α_min}` with `α_min` the maximum of `alphaMinTerm`; `ᾱ₀ ∈ J` when the original instance
has positive active gross returns; on `J` every gross return is positive when the original ETF
gross returns are. -/
def AlphaFamily : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi →
    (∀ x, (beliefMean (famPar par pi x) pi).alpha = fun _ => x) ∧
    (∀ x h s j, ret D (famPar par pi x h) s (Sum.inr j) = ret D (par h) s (Sum.inr j)) ∧
    (∀ x, x ∈ Jset D par pi ↔ ∀ h s, alphaMinTerm D par pi h s < x) ∧
    (∃ αmin, Jset D par pi = Set.Ioi αmin ∧ (∃ h s, αmin = alphaMinTerm D par pi h s) ∧
      ∀ h s, alphaMinTerm D par pi h s ≤ αmin) ∧
    ((∀ h s, 0 < 1 + ret D (par h) s (Sum.inl 0)) → abar0 par pi ∈ Jset D par pi) ∧
    ((∀ h s j, 0 < 1 + ret D (par h) s (Sum.inr j)) →
      ∀ x ∈ Jset D par pi, ∀ h s i, 0 < 1 + ret D (famPar par pi x h) s i)

/-- E- and F-maximizers exist for every real `x`; the E-maximizers do not depend on `x`; for any
E-maximizer `w_E`, `x ∈ C` exactly when `w_E` is F-optimal at `x`. -/
def EOptima : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi →
    (∀ x, ∃ w ∈ E D, IsMaxOn (Qx D par pi x) (E D) w) ∧
    (∀ x, ∃ w ∈ F D, IsMaxOn (Qx D par pi x) (F D) w) ∧
    (∀ x y, maximizers (Qx D par pi x) (E D) = maximizers (Qx D par pi y) (E D)) ∧
    ∀ x₀ wE, wE ∈ maximizers (Qx D par pi x₀) (E D) →
      ∀ x, x ∈ Cset D par pi ↔ IsMaxOn (Qx D par pi x) (F D) wE

/-- For any E-maximizer: `I` is `[lo, hi]` when `hi` is finite and `[lo, ∞)` otherwise, `lo ∈ I`,
`I = {0}` when `k_E > 0`, and `hi` is finite when `a⁻ < 1`. -/
def MultiplierInterval : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi →
    ∀ x₀ wE, wE ∈ maximizers (Qx D par pi x₀) (E D) →
      (HiFinite D par pi wE → Iset D par pi wE = Set.Icc (lo D par pi wE) (hi D par pi wE)) ∧
      (¬ HiFinite D par pi wE → Iset D par pi wE = Set.Ici (lo D par pi wE)) ∧
      lo D par pi wE ∈ Iset D par pi wE ∧
      (0 < cash D wE → Iset D par pi wE = {0}) ∧
      (w0 D (Sum.inl 0) < 1 → HiFinite D par pi wE)

/-- The table of `C`, and the interior width `U - L = b(1 + hi) + s(1 + lo) + (hi - lo)`. -/
def BandTable : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi →
    ∀ x₀ wE, wE ∈ maximizers (Qx D par pi x₀) (E D) →
      (0 < w0 D (Sum.inl 0) → w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) →
        Cset D par pi = Set.Icc (Lb D par pi wE) (Ub D par pi wE)) ∧
      (w0 D (Sum.inl 0) = 0 → 0 < D.wbar (Sum.inl 0) →
        Cset D par pi = Set.Iic (Ub D par pi wE)) ∧
      (0 < w0 D (Sum.inl 0) → w0 D (Sum.inl 0) = D.wbar (Sum.inl 0) →
        Cset D par pi = Set.Ici (Lb D par pi wE)) ∧
      (w0 D (Sum.inl 0) = 0 → D.wbar (Sum.inl 0) = 0 → Cset D par pi = Set.univ) ∧
      Ub D par pi wE - Lb D par pi wE
        = D.kplus (Sum.inl 0) * (1 + hi D par pi wE) + D.kminus (Sum.inl 0) * (1 + lo D par pi wE)
          + (hi D par pi wE - lo D par pi wE)

/-- The marginal condition: `x ∈ C` iff some `η ∈ I` and active slope `t_A ∈ [-s, b]` make the
residual `x - α_c - η - (1 + η) t_A` nonpositive when `a⁻ < ā` and nonnegative when `a⁻ > 0`. -/
def MarginalCondition : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi →
    ∀ x₀ wE, wE ∈ maximizers (Qx D par pi x₀) (E D) → ∀ x,
      x ∈ Cset D par pi ↔
        ∃ η ∈ Iset D par pi wE, ∃ tA, -D.kminus (Sum.inl 0) ≤ tA ∧ tA ≤ D.kplus (Sum.inl 0) ∧
          (w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) →
            x - alphaC D par pi wE - η - (1 + η) * tA ≤ 0) ∧
          (0 < w0 D (Sum.inl 0) → 0 ≤ x - alphaC D par pi wE - η - (1 + η) * tA)

/-- With `γ > 0` and positive definite `Σ`, E and F each have exactly one maximizer. -/
def Uniqueness : Prop :=
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S) (T : Type) [Fintype T]
    (par : T → Params 1 K) (pi : T → ℝ), BandSetting D pi → 0 < D.gamma →
    (∀ v : Inst 1 n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (covariance D *ᵥ v)) → ∀ x,
      (∀ w w', w ∈ maximizers (Qx D par pi x) (F D) → w' ∈ maximizers (Qx D par pi x) (F D) →
        w = w') ∧
      (∀ w w', w ∈ maximizers (Qx D par pi x) (E D) → w' ∈ maximizers (Qx D par pi x) (E D) →
        w = w')

/-! ### The counterexamples -/

/-- Counterexample instances: one ETF, zero loadings, one scenario with zero shocks, `γ = 0`,
zero costs, unit limits, singleton support `(0, 0, 0)`; initial active, ETF and cash `a₀, p₀, h₀`. -/
noncomputable def cxData (a₀ p₀ h₀ : ℝ) : Data 1 1 2 (Fin 1) where
  BA := 0
  BE := 0
  cE := 0
  kplus := 0
  kminus := 0
  gamma := 0
  q := fun _ => 1
  zf := 0
  zA := 0
  zE := 0
  x0 := Sum.elim (fun _ => a₀) (fun _ => p₀)
  h0 := h₀
  wbar := fun _ => 1

/-- The singleton support `(λ₁, λ₂, α) = (0, 0, 0)`. -/
def cxPar : Fin 1 → Params 1 2 := fun _ => ⟨0, 0⟩

/-- Mass one. -/
def cxPi : Fin 1 → ℝ := fun _ => 1

/-- The holding `(a, p)`. -/
def hold (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- First counterexample, start `(1/2, 1/2, 0)`: at `x = 0` every funded holding is optimal, so
the full optimum is not unique; with `w_E = (1/2, 1/2)`, `I = {0}`, `α_c = 0` and `C = {0}`.
Second, start `(1, 0, 0)`: E is the incumbent alone, `hi` is infinite, `I = [0, ∞)` and
`C = [0, ∞)`, and for `x < 0` all cash strictly beats the incumbent. Both satisfy the setting, and
`J = (-1, ∞)` in both. -/
def Counterexamples : Prop :=
  BandSetting (cxData (1 / 2) (1 / 2) 0) cxPi ∧ BandSetting (cxData 1 0 0) cxPi ∧
  Jset (cxData (1 / 2) (1 / 2) 0) cxPar cxPi = Set.Ioi (-1) ∧
  Jset (cxData 1 0 0) cxPar cxPi = Set.Ioi (-1) ∧
  -- first counterexample
  maximizers (Qx (cxData (1 / 2) (1 / 2) 0) cxPar cxPi 0) (F (cxData (1 / 2) (1 / 2) 0))
    = F (cxData (1 / 2) (1 / 2) 0) ∧
  hold 0 1 ∈ F (cxData (1 / 2) (1 / 2) 0) ∧
  hold (1 / 2) (1 / 2) ∈ maximizers (Qx (cxData (1 / 2) (1 / 2) 0) cxPar cxPi 0)
    (E (cxData (1 / 2) (1 / 2) 0)) ∧
  Iset (cxData (1 / 2) (1 / 2) 0) cxPar cxPi (hold (1 / 2) (1 / 2)) = {0} ∧
  alphaC (cxData (1 / 2) (1 / 2) 0) cxPar cxPi (hold (1 / 2) (1 / 2)) = 0 ∧
  Cset (cxData (1 / 2) (1 / 2) 0) cxPar cxPi = {0} ∧
  -- second counterexample
  E (cxData 1 0 0) = {hold 1 0} ∧
  ¬ HiFinite (cxData 1 0 0) cxPar cxPi (hold 1 0) ∧
  Iset (cxData 1 0 0) cxPar cxPi (hold 1 0) = Set.Ici 0 ∧
  Cset (cxData 1 0 0) cxPar cxPi = Set.Ici 0 ∧
  ∀ x < 0, Qx (cxData 1 0 0) cxPar cxPi x (hold 1 0) < Qx (cxData 1 0 0) cxPar cxPi x (hold 0 0)

/-- Claim 009, all parts. -/
def statement : Prop :=
  AlphaFamily ∧ EOptima ∧ MultiplierInterval ∧ BandTable ∧ MarginalCondition ∧ Uniqueness ∧
    Counterexamples

end Standalone.M2NoActiveTradeBand

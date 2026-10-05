import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Intrinsic
import Standalone.M2ActionClasses

/-!
# Claim 027: the two-stage factor-then-manager procedure in M2

Statement only; the proof is `Novel/M2TwoStageSeparationProof.lean`.

M2 is claim 003's formalization (`score`, `beliefScore`, `beliefMean`, `exposure`, `F`, `tau`),
with claim 004's setting predicates (`InitialPosition`, `RatesNonneg`). Counts are general: `m`
active funds, `n` ETFs, `K` factors (M2's `m = 1`, `n ∈ {1, 2}`, `K = 2` are special cases). The
criterion is the score at a parameter `θ`; claim 003 shows `Q̄₀ = Q₀(·; θ̄)` at the belief mean,
restated here as the split of `beliefScore`.

- `sigF = Σ_s q_s z^f_s z^f_s'`, the residual shock `rres w s = a'z^A_s + p'z^E_s`, the cross and
  residual second moments `crossM w = Σ_s q_s z^f_s rres` and `resM w = Σ_s q_s rres²`.
- `Gf θ b = b'λ - (γ/2) b'Σ_f b` (factor objective) and
  `Hr θ w = a'α - p'c^E - (γ/2)[2 b(w)'C(w) + R(w)] - τ(w - w⁻)` (residual objective).
- `BF = b(F)` and `fibre b = {w ∈ F : b(w) = b}`; `Vr θ b = sup H` on the fibre.
- `sqN x = x'Σ_f x`, the squared factor-risk norm.

The two-stage value is `T = G(b*) + V(b*)` for a maximizer `b*` of `G` on `BF`; the joint value
is `J = Q(w_J)` for a maximizer `w_J` of the score on `F`. Part 5 (the numerical cells) has no
formal counterpart.

`V` need not be concave (red's and lean's counterexample, recorded in the claim's Not shown); `G + V` always
is, and `V` is when the cross moments vanish on `F`. Part 2's converse uses the relative interior of
`B_F` (Mathlib's `intrinsicInterior`) and the gradient of `G` along the affine hull of `B_F`.
-/

namespace Standalone.M2TwoStageSeparation

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses

noncomputable section

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- Factor shock second moment `Σ_f = Σ_s q_s z^f_s z^f_s'`. -/
def sigF (D : Data m n K S) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑ s, D.q s * (D.zf s k * D.zf s l)

/-- Residual shock of a holding, `a'z^A_s + p'z^E_s`. -/
def rres (D : Data m n K S) (w : Inst m n → ℝ) (s : S) : ℝ :=
  active w ⬝ᵥ D.zA s + etf w ⬝ᵥ D.zE s

/-- Cross moment `C(w) = Σ_s q_s z^f_s rres_s(w)`. -/
def crossM (D : Data m n K S) (w : Inst m n → ℝ) : Fin K → ℝ :=
  fun k => ∑ s, D.q s * (D.zf s k * rres D w s)

/-- Residual second moment `R(w) = Σ_s q_s rres_s(w)²`. -/
def resM (D : Data m n K S) (w : Inst m n → ℝ) : ℝ := ∑ s, D.q s * rres D w s ^ 2

/-- Factor objective `G(b) = b'λ - (γ/2) b'Σ_f b`. -/
def Gf (D : Data m n K S) (θ : Params m K) (b : Fin K → ℝ) : ℝ :=
  b ⬝ᵥ θ.lam - D.gamma / 2 * (b ⬝ᵥ (sigF D *ᵥ b))

/-- Residual objective `H(w) = a'α - p'c^E - (γ/2)[2 b(w)'C(w) + R(w)] - τ(w - w⁻)`. -/
def Hr (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ) : ℝ :=
  active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE
    - D.gamma / 2 * (2 * (exposure D w ⬝ᵥ crossM D w) + resM D w) - tau D (w - w0 D)

/-- The funded feasible exposure set `B_F = b(F)`. -/
def BF (D : Data m n K S) : Set (Fin K → ℝ) := exposure D '' F D

/-- The fibre `{w ∈ F : b(w) = b}`. -/
def fibre (D : Data m n K S) (b : Fin K → ℝ) : Set (Inst m n → ℝ) := {w | w ∈ F D ∧ exposure D w = b}

/-- The residual value function `V(b) = sup {H(w) : w ∈ F, b(w) = b}`. -/
def Vr (D : Data m n K S) (θ : Params m K) (b : Fin K → ℝ) : ℝ := sSup (Hr D θ '' fibre D b)

/-- Squared factor-risk norm `x'Σ_f x`. -/
def sqN (D : Data m n K S) (x : Fin K → ℝ) : ℝ := x ⬝ᵥ (sigF D *ᵥ x)

/-- `Σ_f` is positive definite (it is symmetric by construction): `x'Σ_f x > 0` for `x ≠ 0`. -/
def PosDefF (D : Data m n K S) : Prop := ∀ x : Fin K → ℝ, x ≠ 0 → 0 < sqN D x

/-- The model inputs used throughout: an initial position, nonnegative rates, masses and `γ`. -/
def Inputs (D : Data m n K S) : Prop :=
  InitialPosition D ∧ RatesNonneg D ∧ (∀ s, 0 ≤ D.q s) ∧ 0 ≤ D.gamma

/-- Part 0: the exact split (for the score at any `θ`, and for `Q̄₀` at the belief mean), `B_F`
nonempty, convex and compact, `V` attained on every fibre, `G + V` concave on `B_F`, `V` concave
when the cross moments vanish on `F`, and `J = max_F Q = max_{B_F} (G + V)`. -/
def Split : Prop :=
  (∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ),
    score D w θ = Gf D θ (exposure D w) + Hr D θ w) ∧
  (∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (T : Type) [Fintype T]
    (par : T → Params m K) (pi : T → ℝ), ∑ t, pi t = 1 → ∀ w : Inst m n → ℝ,
    beliefScore D par pi w
      = Gf D (beliefMean par pi) (exposure D w) + Hr D (beliefMean par pi) w) ∧
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    (BF D).Nonempty ∧ Convex ℝ (BF D) ∧ IsCompact (BF D) ∧
    (∀ b ∈ BF D, ∃ w ∈ fibre D b, IsMaxOn (Hr D θ) (fibre D b) w ∧ Vr D θ b = Hr D θ w) ∧
    ConcaveOn ℝ (BF D) (fun b => Gf D θ b + Vr D θ b) ∧
    ((∀ w ∈ F D, crossM D w = 0) → ConcaveOn ℝ (BF D) (Vr D θ)) ∧
    (∃ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ) ∧
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
      score D wJ θ = Gf D θ (exposure D wJ) + Vr D θ (exposure D wJ) ∧
      ∀ b ∈ BF D, Gf D θ b + Vr D θ b ≤ score D wJ θ

/-- Stage 1's targets: a maximizer of `G` on `B_F` exists; the unconstrained target `b_TB`
(`γ Σ_f b_TB = λ`) maximizes `G` on all exposures, so on `B_F` when it lies there, and then it is
the only maximizer on `B_F` when `Σ_f` is positive definite and `γ > 0`. -/
def Targets : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    (∃ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs) ∧
    ∀ bTB : Fin K → ℝ, D.gamma • (sigF D *ᵥ bTB) = θ.lam →
      (∀ b, Gf D θ b ≤ Gf D θ bTB) ∧
      (bTB ∈ BF D → IsMaxOn (Gf D θ) (BF D) bTB ∧
        (PosDefF D → 0 < D.gamma → ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs → bs = bTB))

/-- Part 1: the loss identity `Λ = [V(b_J) - V(b*)] - [G(b*) - G(b_J)]` with both brackets and
`Λ` nonnegative. -/
def LossIdentity : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
      score D wJ θ - (Gf D θ bs + Vr D θ bs)
        = (Vr D θ (exposure D wJ) - Vr D θ bs) - (Gf D θ bs - Gf D θ (exposure D wJ)) ∧
      0 ≤ Gf D θ bs - Gf D θ (exposure D wJ) ∧
      Gf D θ bs - Gf D θ (exposure D wJ) ≤ Vr D θ (exposure D wJ) - Vr D θ bs ∧
      0 ≤ score D wJ θ - (Gf D θ bs + Vr D θ bs)

/-- Part 2: `T = J` iff `b*` maximizes `G + V` on `B_F` (equivalently `0` is a supergradient of `G + V`
at `b*` relative to `B_F`); `T = J` when `V` is constant on `B_F`, and whenever `0` is a supergradient
of `V` at `b*` (`V ≤ V(b*)` on `B_F`), for any `V`. At a `b*` in the relative interior of `B_F` the
gradient of `G` vanishes along `B_F` (`∇G(b*)'(b - b*) = 0` for `b ∈ B_F`), and if moreover `V` is
concave on `B_F`, `Σ_f` is positive definite and `γ > 0`, then `T = J` iff `0` is a supergradient of `V`
at `b*` relative to `B_F`. At an interior `b*` (with `Σ_f` positive definite and `γ > 0`) the whole
gradient vanishes, `γ Σ_f b* = λ`. -/
def ExactSeparation : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
      (Gf D θ bs + Vr D θ bs = score D wJ θ ↔
        IsMaxOn (fun b => Gf D θ b + Vr D θ b) (BF D) bs) ∧
      (Gf D θ bs + Vr D θ bs = score D wJ θ ↔ ∀ b ∈ BF D,
        Gf D θ b + Vr D θ b ≤ Gf D θ bs + Vr D θ bs + (0 : Fin K → ℝ) ⬝ᵥ (b - bs)) ∧
      ((∃ c, ∀ b ∈ BF D, Vr D θ b = c) → Gf D θ bs + Vr D θ bs = score D wJ θ) ∧
      ((∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs) → Gf D θ bs + Vr D θ bs = score D wJ θ) ∧
      (bs ∈ intrinsicInterior ℝ (BF D) →
        (∀ b ∈ BF D, (b - bs) ⬝ᵥ (θ.lam - D.gamma • (sigF D *ᵥ bs)) = 0) ∧
        (ConcaveOn ℝ (BF D) (Vr D θ) → PosDefF D → 0 < D.gamma →
          (Gf D θ bs + Vr D θ bs = score D wJ θ ↔ ∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs))) ∧
      (PosDefF D → 0 < D.gamma → bs ∈ interior (BF D) → D.gamma • (sigF D *ᵥ bs) = θ.lam)

/-- Part 3: `Λ ≤ V(b_J) - V(b*) - (γ/2)‖b_J - b*‖²_{Σ_f}`, and if `V` is `L`-Lipschitz on `B_F`
in the factor-risk norm, `Λ ≤ min(L²/(2γ), L ‖b_J - b*‖_{Σ_f})` for `γ > 0`. (No positive
definiteness is needed; `Σ_f` is a second moment, hence positive semidefinite.) -/
def LossBound : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
      score D wJ θ - (Gf D θ bs + Vr D θ bs)
        ≤ Vr D θ (exposure D wJ) - Vr D θ bs - D.gamma / 2 * sqN D (exposure D wJ - bs) ∧
      ∀ L : ℝ, (∀ b ∈ BF D, ∀ b' ∈ BF D, |Vr D θ b - Vr D θ b'| ≤ L * Real.sqrt (sqN D (b - b'))) →
        0 < D.gamma →
        score D wJ θ - (Gf D θ bs + Vr D θ bs)
          ≤ min (L ^ 2 / (2 * D.gamma)) (L * Real.sqrt (sqN D (exposure D wJ - bs)))

/-- The active-only residual objective `a'α - (γ/2) Σ_s q_s (a'z^A_s)² - τ_A(a - a⁻)`. -/
def hA (D : Data m n K S) (θ : Params m K) (a : Fin m → ℝ) : ℝ :=
  a ⬝ᵥ θ.alpha - D.gamma / 2 * ∑ s, D.q s * (a ⬝ᵥ D.zA s) ^ 2
    - ∑ i, (D.kplus (Sum.inl i) * max (a i - active (w0 D) i) 0
      + D.kminus (Sum.inl i) * max (-(a i - active (w0 D) i)) 0)

/-- Part 4: `V` is flat, and the two-stage procedure recovers the joint optimum, when the ETFs are
residual-free, drag-free and costless, the cross moments vanish on `F`, and every fibre over
`B_F` contains a holding with an active position `a_H` maximizing `hA` over the active box. And
with one active fund whose loading is outside the ETF span `L_E`, the exposure fixes the active
position. -/
def FlatCase : Prop :=
  (∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K), Inputs D →
    (∀ s, D.zE s = 0) → D.cE = 0 → (∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) →
    (∀ w ∈ F D, crossM D w = 0) →
    ∀ aH : Fin m → ℝ, (∀ i, 0 ≤ aH i ∧ aH i ≤ D.wbar (Sum.inl i)) →
      (∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ D.wbar (Sum.inl i)) → hA D θ a ≤ hA D θ aH) →
      (∀ b ∈ BF D, ∃ w ∈ fibre D b, active w = aH) →
      (∀ b ∈ BF D, Vr D θ b = hA D θ aH) ∧
      ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
      ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs → Gf D θ bs + Vr D θ bs = score D wJ θ) ∧
  ∀ (n K : ℕ) (S : Type) [Fintype S] (D : Data 1 n K S),
    (∀ c : Fin n → ℝ, (fun k => D.BA 0 k) ≠ D.BEᵀ *ᵥ c) →
    ∀ w w' : Inst 1 n → ℝ, exposure D w = exposure D w' → active w = active w'

/-- Claim 027, parts 0-4. -/
def statement : Prop := Split ∧ Targets ∧ LossIdentity ∧ ExactSeparation ∧ LossBound ∧ FlatCase

end

end Standalone.M2TwoStageSeparation

import Standalone.M7TwoReviewsBindingBudget

/-!
# Claim 048: many funds and many ETFs over two reviews with a funded budget

Statement only; the proof is `Novel/M7ManyFundsManyEtfsTwoReviewsProof.lean`.

The model is claim 044's two-review program (`Two`) with instruments `Fin N ⊕ Fin K`: the funds, then
the ETFs. For part 2, the root's moments come from the factor model (`Fac`):
- the loadings `B^A` and `B^E`, with `R B^E = B^E R = I`;
- the factor covariance `Σ~_f`, and `V_0 = diag(v)` with `v > 0`;
- the beliefs `λ̂` and `α̂`;
- `Σ_E = 0` and `c^E = 0`.
`b = B'x` is the exposure, and `r_i = R'(B^A_i)'` the netting vector.

Scope (PM, rule 6b: lean's split confirmed). Formal:
- part 1, as corollaries of claim 044's parts 2 and 4(a) (the latter for any finite instrument set);
- part 2, both directions: necessity from the lines, and sufficiency with no citation;
- part 3.
Paper-level: part 4 (the check counts the failure; the one-ETF reduction is claim 044's 4(a)) and the
Checks. For the fidelity row: in claim 044's model the rates are the same at both reviews, so `κ_E = 0`
also holds tomorrow (PM; math and red told). Tomorrow's budget, bounds and regimes are unrestricted.
-/

namespace Standalone.M7ManyFundsManyEtfsTwoReviews

open Standalone.M7TwoReviewsBindingBudget
open Standalone.M7TwoStageExactnessLoss (bandHold)

noncomputable section

/-- The instruments: `N` funds, then `K` ETFs. -/
abbrev Ins (N K : ℕ) := Fin N ⊕ Fin K

/-- The factor model at the root. -/
structure Fac (N K : ℕ) where
  BA : Fin N → Fin K → ℝ
  BE : Fin K → Fin K → ℝ
  R : Fin K → Fin K → ℝ
  Sf : Fin K → Fin K → ℝ
  v : Fin N → ℝ
  lh : Fin K → ℝ
  ah : Fin N → ℝ

variable {N K : ℕ}

/-- The loadings of every instrument. -/
def Bf (F : Fac N K) : Ins N K → Fin K → ℝ := Sum.elim F.BA F.BE

/-- `μ_0 = (α̂ + B^A λ̂, B^E λ̂)` (`c^E = 0`). -/
def facMu (F : Fac N K) : Ins N K → ℝ :=
  Sum.elim (fun i => F.ah i + ∑ k, F.BA i k * F.lh k) (fun j => ∑ k, F.BE j k * F.lh k)

/-- `Σ_0 = B Σ~_f B' + diag(V, 0)` (`Σ_E = 0`). -/
def facSig (F : Fac N K) (a b : Ins N K) : ℝ :=
  (∑ k, ∑ l, Bf F a k * F.Sf k l * Bf F b l) +
    Sum.elim (fun i => Sum.elim (fun i' => if i = i' then F.v i else 0) (fun _ => 0)) (fun _ _ => 0) a b

/-- `R` inverts `B^E` on both sides, and `v > 0`. -/
def FacHyp (F : Fac N K) : Prop :=
  (∀ j k, ∑ l, F.R j l * F.BE l k = if j = k then 1 else 0) ∧
    (∀ j k, ∑ l, F.BE j l * F.R l k = if j = k then 1 else 0) ∧ ∀ i, 0 < F.v i

/-- The exposure `b = B'x`. -/
def expo (F : Fac N K) (x : Ins N K → ℝ) (k : Fin K) : ℝ := ∑ a, Bf F a k * x a

/-- The netting vector `r_i = R'(B^A_i)'`. -/
def netw (F : Fac N K) (i : Fin N) (j : Fin K) : ℝ := ∑ k, F.BA i k * F.R k j

/-- Part 2's spanning setting at the root: the factor moments and frictionless ETFs. -/
def Spanning {Z : Type} [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K) : Prop :=
  FacHyp F ∧ P.mu0 = facMu F ∧ P.S0 = facSig F ∧ ∀ j, P.kp (Sum.inr j) = 0 ∧ P.km (Sum.inr j) = 0

/-- The tilted premium `λ̂^res = λ̂ + R (S_E - η̂_0 1)`. -/
def lamRes {Z : Type} [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K) (e : ℝ) (η1 : Z → ℝ)
    (t1 : Z → Ins N K → ℝ) (k : Fin K) : ℝ :=
  F.lh k + ∑ j, F.R k j * (Sinc P η1 t1 (Sum.inr j) - e)

/-- The residual alpha `α^res_i = α̂_i + S_{A,i} - r_i'S_E - η̂_0 (1 - r_i'1)`. -/
def alphaRes {Z : Type} [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K) (e : ℝ) (η1 : Z → ℝ)
    (t1 : Z → Ins N K → ℝ) (i : Fin N) : ℝ :=
  F.ah i + Sinc P η1 t1 (Sum.inl i) - ∑ j, netw F i j * Sinc P η1 t1 (Sum.inr j) -
    e * (1 - ∑ j, netw F i j)

/-! ### Part 1 -/

/-- Part 1, for any `N` funds and `K` ETFs. A feasible policy satisfying claim 044's lines (one
cash price for the menu, one incumbent value per instrument) is optimal. Under AX-13 an optimal
policy satisfies them. At the root, the holdings maximize the one-review Lagrangian at
`(μ_0 + S, η̂_0)` over the box. -/
def Structure : Prop :=
  ∀ (N K : ℕ) (Z : Type) [Fintype Z] (P : Two (Ins N K) Z), Hyp P →
    (∀ X ∈ Feas P, Lines P X → Optimal P X) ∧
    (Standalone.M7TwoStageExactnessLoss.AX13 → ∀ X, Optimal P X → Lines P X) ∧
    ∀ X η0 η1 t0 t1, Tomorrow P X η1 t1 → Root P X η0 η1 t0 t1 → Box P X.1 → (∀ z, Box P (X.2 z)) →
      IsMaxOn (lagOne P (P.mu0 + Sinc P η1 t1) P.S0 P.xm (etaHat P η0 η1)) {x | Box P x} X.1

/-! ### Part 2 -/

/-- Part 2, necessity: the root's lines separate given the tomorrow numbers `(S, η̂_0)` at the
optimum. Those numbers are read from the same policy's tomorrow multipliers, so they are a fixed
point of the joint root, not inputs to two independent problems. In the spanning setting, for a
feasible policy with today's budget slack at the root and the ETFs
strictly inside their boxes, the lines give three things. The exposure solves
`γ Σ~_f b_0 = λ̂^res`. Each fund is at its one-fund clip at `α^res_i` (claim 104's `bandHold`), with curvature
`γ v_i` and thresholds scaled by `1 + η̂_0`. The ETFs are `R'(b_0 - (B^A)' x^A_0)`. -/
def Separation : Prop :=
  ∀ (N K : ℕ) (Z : Type) [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K), Hyp P → Spanning P F →
    ∀ (X : (Ins N K → ℝ) × (Z → Ins N K → ℝ)) η0 η1 t0 t1, X ∈ Feas P → Tomorrow P X η1 t1 →
      Root P X η0 η1 t0 t1 → 0 < h0 P X.1 →
      (∀ j, 0 < X.1 (Sum.inr j) ∧ X.1 (Sum.inr j) < P.xbar (Sum.inr j)) →
      let e := etaHat P η0 η1
      η0 = 0 ∧
      (∀ k, P.gamma * ∑ l, F.Sf k l * expo F X.1 l = lamRes P F e η1 t1 k) ∧
      (∀ i, X.1 (Sum.inl i) = bandHold (alphaRes P F e η1 t1 i) (P.gamma * F.v i)
        ((1 + e) * P.kp (Sum.inl i)) ((1 + e) * P.km (Sum.inl i)) (P.xm (Sum.inl i)) (P.xbar (Sum.inl i))) ∧
      ∀ j, X.1 (Sum.inr j) = ∑ k, F.R k j * (expo F X.1 k - ∑ i, F.BA i k * X.1 (Sum.inl i))

/-- Part 2, sufficiency (no citation), again with the tomorrow numbers read from the policy's own
tomorrow multipliers. In the spanning setting, take a feasible policy whose tomorrow satisfies
tomorrow's lines, whose ETFs are strictly inside their boxes, and whose root has
the displayed exposure and fund holdings at `η̂_0 = β E η_1`. Then it is optimal. -/
def SepSufficient : Prop :=
  ∀ (N K : ℕ) (Z : Type) [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K), Hyp P → Spanning P F →
    ∀ (X : (Ins N K → ℝ) × (Z → Ins N K → ℝ)) η1 t1, X ∈ Feas P → Tomorrow P X η1 t1 →
      (∀ j, 0 < X.1 (Sum.inr j) ∧ X.1 (Sum.inr j) < P.xbar (Sum.inr j)) →
      let e := etaHat P 0 η1
      (∀ k, P.gamma * ∑ l, F.Sf k l * expo F X.1 l = lamRes P F e η1 t1 k) →
      (∀ i, X.1 (Sum.inl i) = bandHold (alphaRes P F e η1 t1 i) (P.gamma * F.v i)
        ((1 + e) * P.kp (Sum.inl i)) ((1 + e) * P.km (Sum.inl i)) (P.xm (Sum.inl i)) (P.xbar (Sum.inl i))) →
      Optimal P X

/-! ### Part 3 -/

/-- Part 3. With the untilted target `γ Σ~_f b^TB = λ̂`, the exposure's departure solves
`γ Σ~_f (b_0 - b^TB) = R (S_E - η̂_0 1)`. With frictionless ETFs tomorrow as well, each ETF's
incumbent value net of the cash price is `S_{E,j} - η̂_0 = β Σ_z q (g_{E,j} - 1) η_1`. -/
def Interaction : Prop :=
  ∀ (N K : ℕ) (Z : Type) [Fintype Z] (P : Two (Ins N K) Z) (F : Fac N K), Hyp P → Spanning P F →
    ∀ (X : (Ins N K → ℝ) × (Z → Ins N K → ℝ)) η0 η1 t0 t1, Tomorrow P X η1 t1 →
      Root P X η0 η1 t0 t1 → 0 < h0 P X.1 →
      (∀ j, 0 < X.1 (Sum.inr j) ∧ X.1 (Sum.inr j) < P.xbar (Sum.inr j)) →
      ∀ bTB : Fin K → ℝ, (∀ k, P.gamma * ∑ l, F.Sf k l * bTB l = F.lh k) →
      (∀ k, P.gamma * ∑ l, F.Sf k l * (expo F X.1 l - bTB l) =
        ∑ j, F.R k j * (Sinc P η1 t1 (Sum.inr j) - etaHat P η0 η1)) ∧
      ∀ j, Sinc P η1 t1 (Sum.inr j) - etaHat P η0 η1 =
        P.beta * ∑ z, P.q z * (P.g z (Sum.inr j) - 1) * η1 z

/-- Claim 048 (parts 1-3; part 4 paper-level). -/
def statement : Prop := Structure ∧ Separation ∧ SepSufficient ∧ Interaction

end

end Standalone.M7ManyFundsManyEtfsTwoReviews

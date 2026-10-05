import Standalone.M7TwoStageExactnessLoss
import Standalone.M6QuarterlyBandStaticCeiling

/-!
# Claim 102: when a fund is held, bought or sold versus adjusted through ETFs

Statement only; the proof is `Novel/M7FundHoldBuySellCriterionProof.lean`.

One review of the general model, on claim 027's M2 `Data` (claim 104's setting), with claim 104's
smooth marginal `grad` (`g = μ - γΣx`), slope sets `InSlope`, box signs `BoxSign` (normal-cone form)
and band holding `bandHold`. Part 1's criterion is claim 104's part 0, from ledger entry AX-13 (the
Upstream structure `PolyKKT`, restated as `AX13`), which parts 1, 2, 4 and 5 take as a hypothesis.
`r_i = R'(B^A_i)'` with `R = (B^E)⁻¹` is fund `i`'s netting vector.

Part 3's readings and part 4's re-hedge readings are stated in the forms reported in lean's notes to
mathb and red:
- a purchase needs `x⁻ < x̄`, and a sale needs `x⁻ > 0`;
- the exact re-hedge values are for an interior trade, with an inequality at the cap or at zero.

Part 6's thresholds (the sure trades and the only-if thresholds) are stated in claim 029's
one-instrument model (`M6 1`), with pure-learning marking (`ḡ = 1`). Paper-level: the reduction of the
multi-review spanning problem to per-fund one-instrument problems. The static ceiling is claim 029's
`Ceiling`, transferred by claim 100.
-/

namespace Standalone.M7FundHoldBuySellCriterion

open Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M2TwoStageSeparation (Inputs)

noncomputable section

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- Part 1's per-instrument reading at `w` with cash multiplier `η`: the purchase line
`g_l = η + (1 + η)κ⁺_l`, the sale line `g_l = η - (1 + η)κ⁻_l`, the held band between them, and the
one-sided forms at `0` and `x̄`. -/
def Reading (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ) (η : ℝ) (l : Inst m n) : Prop :=
  (w0 D l < w l → w l < D.wbar l → grad D θ w l = η + (1 + η) * D.kplus l) ∧
  (w0 D l < w l → w l = D.wbar l → η + (1 + η) * D.kplus l ≤ grad D θ w l) ∧
  (w l < w0 D l → 0 < w l → grad D θ w l = η - (1 + η) * D.kminus l) ∧
  (w l < w0 D l → w l = 0 → grad D θ w l ≤ η - (1 + η) * D.kminus l) ∧
  (w l = w0 D l → 0 < w l → w l < D.wbar l →
    η - (1 + η) * D.kminus l ≤ grad D θ w l ∧ grad D θ w l ≤ η + (1 + η) * D.kplus l) ∧
  (w l = w0 D l → w l = 0 → w l < D.wbar l → grad D θ w l ≤ η + (1 + η) * D.kplus l) ∧
  (w l = w0 D l → 0 < w l → w l = D.wbar l → η - (1 + η) * D.kminus l ≤ grad D θ w l)

/-- Part 1: with `Σ` positive definite and `γ > 0`,
- an optimum exists and is unique (unconditionally);
- given AX-13, a feasible `w` is optimal iff claim 104's multiplier criterion holds;
- given AX-13, at the optimum some `η ≥ 0` with `η k = 0` gives every instrument's reading. -/
def Criterion : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K),
    Inputs D → (covariance D).PosDef → 0 < D.gamma →
    (∃ w ∈ F D, IsMaxOn (fun w => score D w θ) (F D) w) ∧
    (∀ w₁ ∈ F D, ∀ w₂ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) w₁ →
      IsMaxOn (fun w => score D w θ) (F D) w₂ → w₁ = w₂) ∧
    (AX13 → ∀ w ∈ F D, (IsMaxOn (fun w => score D w θ) (F D) w ↔ JointCriterion D θ w) ∧
      (IsMaxOn (fun w => score D w θ) (F D) w →
        ∃ η, 0 ≤ η ∧ η * cash D w = 0 ∧ ∀ l, Reading D θ w η l))

/-- The ETF-only class: every fund frozen at its incumbent. -/
def E0 (D : Data m n K S) : Set (Inst m n → ℝ) := {w | w ∈ F D ∧ active w = active (w0 D)}

/-- `I`: the `η ≥ 0` compatible with part 1 at `x_E` on the ETF coordinates and the budget. -/
def Iset (D : Data m n K S) (θ : Params m K) (xE : Inst m n → ℝ) : Set ℝ :=
  {η | 0 ≤ η ∧ η * cash D xE = 0 ∧ ∀ j, ∃ t, InSlope D xE (Sum.inr j) t ∧
    BoxSign (D.wbar (Sum.inr j)) (xE (Sum.inr j)) (grad D θ xE (Sum.inr j) - η - (1 + η) * t)}

/-- Fund `i`'s held condition at `x_E`: a zero-trade slope `t ∈ [-κ⁻, κ⁺]` with the box signs. -/
def Held (D : Data m n K S) (θ : Params m K) (xE : Inst m n → ℝ) (η : ℝ) (i : Fin m) : Prop :=
  ∃ t, -D.kminus (Sum.inl i) ≤ t ∧ t ≤ D.kplus (Sum.inl i) ∧
    BoxSign (D.wbar (Sum.inl i)) (xE (Sum.inl i)) (grad D θ xE (Sum.inl i) - η - (1 + η) * t)

/-- Part 2 (given AX-13), the ETF-optimized test: with `x_E` the ETF-only optimum and `w` the full
optimum, no fund is traded at `w` iff some `η ∈ I` makes every fund's held condition hold at `x_E`. -/
def EtfTest : Prop :=
  AX13 → ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K),
    Inputs D → (covariance D).PosDef → 0 < D.gamma →
    ∀ xE ∈ E0 D, IsMaxOn (fun w => score D w θ) (E0 D) xE →
    ∀ w ∈ F D, IsMaxOn (fun w => score D w θ) (F D) w →
      (active w = active (w0 D) ↔ ∃ η ∈ Iset D θ xE, ∀ i, Held D θ xE η i)

/-- Part 3, frictionless spanning ETFs (claim 104's 2a inputs). At a joint optimum with a slack budget
and every ETF strictly inside its box, write `m_i = α̂_i - γ v_i x⁻_i` and `r_i = R'(B^A_i)'`:
- fund `i` is at its band holding, whatever the premia, their precision and the loadings;
- it is bought iff `m_i > κ⁺_i` and `x⁻_i < x̄_i`;
- it is sold iff `m_i < -κ⁻_i` and `x⁻_i > 0`;
- from a zero incumbent it is bought iff `α̂_i > κ⁺_i` (with `x̄_i > 0`), and it stays at zero when
  `α̂_i ≤ κ⁺_i`;
- from a positive incumbent it is sold out iff `α̂_i ≤ -κ⁻_i`;
- the ETF trade is the exposure trade `R'(y* - y⁻)` less the netting trades `Σ_i r_i (x_i - x⁻_i)`. -/
def SpanningRule : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → FrictionlessSpanning D Sf v →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ → 0 < cash D wJ →
    (∀ j, 0 < wJ (Sum.inr j) ∧ wJ (Sum.inr j) < D.wbar (Sum.inr j)) →
    (∀ i, wJ (Sum.inl i) = bandHold (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
        (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i)) ∧
      (w0 D (Sum.inl i) < wJ (Sum.inl i) ↔
        D.kplus (Sum.inl i) < θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) ∧
          w0 D (Sum.inl i) < D.wbar (Sum.inl i)) ∧
      (wJ (Sum.inl i) < w0 D (Sum.inl i) ↔
        θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) < -D.kminus (Sum.inl i) ∧ 0 < w0 D (Sum.inl i)) ∧
      (w0 D (Sum.inl i) = 0 → 0 < D.wbar (Sum.inl i) →
        (0 < wJ (Sum.inl i) ↔ D.kplus (Sum.inl i) < θ.alpha i)) ∧
      (w0 D (Sum.inl i) = 0 → θ.alpha i ≤ D.kplus (Sum.inl i) → wJ (Sum.inl i) = 0) ∧
      (0 < w0 D (Sum.inl i) → (wJ (Sum.inl i) = 0 ↔ θ.alpha i ≤ -D.kminus (Sum.inl i)))) ∧
    etf wJ - etf (w0 D) = (D.BEᵀ)⁻¹ *ᵥ (exposure D wJ - exposure D (w0 D)) -
      ∑ i, (wJ (Sum.inl i) - w0 D (Sum.inl i)) • ((D.BEᵀ)⁻¹ *ᵥ D.BA i)

/-- The re-hedge cost of a unit purchase, `h⁺ = Σ_j [r_j⁺ κ⁻_{E,j} + r_j⁻ κ⁺_{E,j}]`. -/
def hPlus {m K : ℕ} (D : Data m K K S) (r : Fin K → ℝ) : ℝ :=
  ∑ j, (max (r j) 0 * D.kminus (Sum.inr j) + max (-r j) 0 * D.kplus (Sum.inr j))

/-- The re-hedge cost of a unit sale, `h⁻ = Σ_j [r_j⁺ κ⁺_{E,j} + r_j⁻ κ⁻_{E,j}]`. -/
def hMinus {m K : ℕ} (D : Data m K K S) (r : Fin K → ℝ) : ℝ :=
  ∑ j, (max (r j) 0 * D.kplus (Sum.inr j) + max (-r j) 0 * D.kminus (Sum.inr j))

/-- The netting vector `r_i = R'(B^A_i)'`. -/
def rvec {m K : ℕ} (D : Data m K K S) (i : Fin m) : Fin K → ℝ := (D.BE⁻¹)ᵀ *ᵥ D.BA i

/-- The reduced marginal `A_i(x) = α̂_i + r_i'c^E - γ v_i x_i + γ r_i'Σ_E x^E`. -/
def Ared {m K : ℕ} (D : Data m K K S) (θ : Params m K) (v : Fin m → ℝ) (SE : Matrix (Fin K) (Fin K) ℝ)
    (x : Inst m K → ℝ) (i : Fin m) : ℝ :=
  θ.alpha i + rvec D i ⬝ᵥ D.cE - D.gamma * v i * x (Sum.inl i) + D.gamma * (rvec D i ⬝ᵥ (SE *ᵥ etf x))

/-- The ETFs trade in the direction that re-hedges a purchase of fund `i`: sell those with `r_ij > 0`,
buy those with `r_ij < 0`. -/
def PurchaseHedge {m K : ℕ} (D : Data m K K S) (x : Inst m K → ℝ) (r : Fin K → ℝ) : Prop :=
  ∀ j, (0 < r j → x (Sum.inr j) < w0 D (Sum.inr j)) ∧ (r j < 0 → w0 D (Sum.inr j) < x (Sum.inr j))

/-- The ETFs trade in the direction that re-hedges a sale of fund `i`. -/
def SaleHedge {m K : ℕ} (D : Data m K K S) (x : Inst m K → ℝ) (r : Fin K → ℝ) : Prop :=
  ∀ j, (0 < r j → w0 D (Sum.inr j) < x (Sum.inr j)) ∧ (r j < 0 → x (Sum.inr j) < w0 D (Sum.inr j))

/-- Parts 4 and 5(a) (given AX-13). Take spanning ETFs, the reference case with `V = diag v`, and every
ETF strictly inside its box at the optimum `x`; the budget may bind. For some cash multiplier `η ≥ 0`
with `η k(x) = 0` (so `η = 0` when the budget is slack), write `A' = A_i - η(1 - Σ_j r_ij)`. Then:
- a purchase gives `A' ≥ (1 + η)(κ⁺ - h⁻)`, and a sale gives `A' ≤ (1 + η)(-κ⁻ + h⁺)`;
- an interior hold gives `(1 + η)(-κ⁻ - h⁻) ≤ A' ≤ (1 + η)(κ⁺ + h⁺)`;
- under the purchase re-hedge, an interior purchase gives `A' = (1 + η)(κ⁺ + h⁺)` and a purchase to the
  cap gives `≥`;
- under the sale re-hedge, an interior sale gives `A' = (1 + η)(-κ⁻ - h⁻)` and a sale to zero gives `≤`. -/
def ReHedge : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Inputs D → RefCase D Sf (diagonal v) SE → IsUnit D.BE.det →
    ∀ x ∈ F D, IsMaxOn (fun w => score D w θ) (F D) x →
    (∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∃ η, 0 ≤ η ∧ η * cash D x = 0 ∧ ∀ i,
      let r := rvec D i
      let A' := Ared D θ v SE x i - η * (1 - ∑ j, r j)
      let kp := D.kplus (Sum.inl i)
      let km := D.kminus (Sum.inl i)
      (w0 D (Sum.inl i) < x (Sum.inl i) → (1 + η) * (kp - hMinus D r) ≤ A') ∧
      (x (Sum.inl i) < w0 D (Sum.inl i) → A' ≤ (1 + η) * (-km + hPlus D r)) ∧
      (x (Sum.inl i) = w0 D (Sum.inl i) → 0 < x (Sum.inl i) → x (Sum.inl i) < D.wbar (Sum.inl i) →
        (1 + η) * (-km - hMinus D r) ≤ A' ∧ A' ≤ (1 + η) * (kp + hPlus D r)) ∧
      (PurchaseHedge D x r → w0 D (Sum.inl i) < x (Sum.inl i) →
        (x (Sum.inl i) < D.wbar (Sum.inl i) → A' = (1 + η) * (kp + hPlus D r)) ∧
        (x (Sum.inl i) = D.wbar (Sum.inl i) → (1 + η) * (kp + hPlus D r) ≤ A')) ∧
      (SaleHedge D x r → x (Sum.inl i) < w0 D (Sum.inl i) →
        (0 < x (Sum.inl i) → A' = (1 + η) * (-km - hMinus D r)) ∧
        (x (Sum.inl i) = 0 → A' ≤ (1 + η) * (-km - hMinus D r)))

/-- Part 4's sufficient conditions at the incumbent (given AX-13), with `Σ_E = 0`, a slack budget and
every ETF strictly inside its box at the optimum `x`:
- `A_i(x⁻) > κ⁺_i + h⁺_i` and `x⁻_i < x̄_i` force a purchase;
- `A_i(x⁻) < -κ⁻_i - h⁻_i` and `x⁻_i > 0` force a sale. -/
def Sufficient : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → RefCase D Sf (diagonal v) 0 → IsUnit D.BE.det → (∀ i, 0 ≤ v i) → 0 ≤ D.gamma →
    ∀ x ∈ F D, IsMaxOn (fun w => score D w θ) (F D) x → 0 < cash D x →
    (∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) → ∀ i,
      (D.kplus (Sum.inl i) + hPlus D (rvec D i) < Ared D θ v 0 (w0 D) i →
        w0 D (Sum.inl i) < D.wbar (Sum.inl i) → w0 D (Sum.inl i) < x (Sum.inl i)) ∧
      (Ared D θ v 0 (w0 D) i < -D.kminus (Sum.inl i) - hMinus D (rvec D i) →
        0 < w0 D (Sum.inl i) → x (Sum.inl i) < w0 D (Sum.inl i))

/-- Part 4's pinned slopes (with part 5(a)'s scaling), given AX-13. Take spanning ETFs, `V = diag v`,
and every ETF strictly inside its box at the optimum `x`. With the cash multiplier `η` and
`A' = A_i - η(1 - Σ_j r_ij)`:
- if every ETF `j` with `r_ij ≠ 0` is traded, its slope is pinned: `t_j = κ⁺_{E,j}` if bought and
  `-κ⁻_{E,j}` if sold. An interior purchase then has `A' = (1 + η)(κ⁺ - Σ_j r_ij t_j)` (`≥` at the
  cap), and an interior sale has `A' = (1 + η)(-κ⁻ - Σ_j r_ij t_j)` (`≤` at zero);
- the converse fails. A fund held at its band edge (`g_i = η + (1 + η)κ⁺` at `x_i = x⁻_i`, interior)
  under the purchase re-hedge has `A' = (1 + η)(κ⁺ + h⁺)` and is not bought. -/
def Pinned : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Inputs D → RefCase D Sf (diagonal v) SE → IsUnit D.BE.det →
    ∀ x ∈ F D, IsMaxOn (fun w => score D w θ) (F D) x →
    (∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∃ η, 0 ≤ η ∧ η * cash D x = 0 ∧ ∀ i,
      let r := rvec D i
      let A' := Ared D θ v SE x i - η * (1 - ∑ j, r j)
      let tE := fun j => if w0 D (Sum.inr j) < x (Sum.inr j) then D.kplus (Sum.inr j)
        else -D.kminus (Sum.inr j)
      ((∀ j, r j ≠ 0 → x (Sum.inr j) ≠ w0 D (Sum.inr j)) →
        (w0 D (Sum.inl i) < x (Sum.inl i) → x (Sum.inl i) < D.wbar (Sum.inl i) →
          A' = (1 + η) * (D.kplus (Sum.inl i) - r ⬝ᵥ tE)) ∧
        (w0 D (Sum.inl i) < x (Sum.inl i) → x (Sum.inl i) = D.wbar (Sum.inl i) →
          (1 + η) * (D.kplus (Sum.inl i) - r ⬝ᵥ tE) ≤ A') ∧
        (x (Sum.inl i) < w0 D (Sum.inl i) → 0 < x (Sum.inl i) →
          A' = (1 + η) * (-D.kminus (Sum.inl i) - r ⬝ᵥ tE)) ∧
        (x (Sum.inl i) < w0 D (Sum.inl i) → x (Sum.inl i) = 0 →
          A' ≤ (1 + η) * (-D.kminus (Sum.inl i) - r ⬝ᵥ tE))) ∧
      (PurchaseHedge D x r → x (Sum.inl i) = w0 D (Sum.inl i) → 0 < x (Sum.inl i) →
        x (Sum.inl i) < D.wbar (Sum.inl i) → grad D θ x (Sum.inl i) = η + (1 + η) * D.kplus (Sum.inl i) →
        A' = (1 + η) * (D.kplus (Sum.inl i) + hPlus D r))

/-- Part 5(a) on part 3's band (given AX-13). Take frictionless spanning ETFs (claim 104's 2a inputs)
with every ETF strictly inside its box at the optimum `x`; the budget may bind. For the cash multiplier
`η`, with `s_i = Σ_j r_ij`:
- fund `i` is at the band holding with alpha `α̂_i - η(1 - s_i)` and rates `(1 + η)κ^±`, that is, the clip
  with the shifted endpoints;
- it is bought iff `α̂_i - γ v_i x⁻_i > η(1 - s_i) + (1 + η)κ⁺_i` and `x⁻_i < x̄_i`;
- it is sold iff `α̂_i - γ v_i x⁻_i < η(1 - s_i) - (1 + η)κ⁻_i` and `x⁻_i > 0`;
- the exposure is `y*(η) = (γ Σ~_f)⁻¹(λ̂ - η R 1)`. -/
def BudgetStrip : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → FrictionlessSpanning D Sf v →
    ∀ x ∈ F D, IsMaxOn (fun w => score D w θ) (F D) x →
    (∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∃ η, 0 ≤ η ∧ η * cash D x = 0 ∧
      exposure D x = (D.gamma • Sf)⁻¹ *ᵥ (θ.lam - η • (D.BE⁻¹ *ᵥ fun _ => 1)) ∧
      ∀ i,
        let s := ∑ j, rvec D i j
        x (Sum.inl i) = bandHold (θ.alpha i - η * (1 - s)) (D.gamma * v i) ((1 + η) * D.kplus (Sum.inl i))
          ((1 + η) * D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i)) ∧
        (w0 D (Sum.inl i) < x (Sum.inl i) ↔
          η * (1 - s) + (1 + η) * D.kplus (Sum.inl i) < θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) ∧
            w0 D (Sum.inl i) < D.wbar (Sum.inl i)) ∧
        (x (Sum.inl i) < w0 D (Sum.inl i) ↔
          θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) < η * (1 - s) - (1 + η) * D.kminus (Sum.inl i) ∧
            0 < w0 D (Sum.inl i))

open Standalone.M6QuarterlyBandStaticCeiling in
/-- Part 6's sure trades, in claim 029's one-instrument model with pure-learning marking (`g' = 1`).
With curvature `c_t` and target `x*_t` (so `α̂_t = c_t x*_t`), at every review:
- a fund with no incumbent holding is bought (the optimum from `0` is `lo_t > 0`) when
  `α̂_t > κ⁺ + βκ⁻`;
- a fund at its cap is sold out (the optimum from `x̄` is `0`) when `α̂_t < -(κ⁻ + βκ⁺)`. -/
def SureTrade : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → (∀ ω, P.gross ω 0 = 1) → ∀ t z, t < P.T →
    (P.kp 0 + P.beta * P.km 0 < curv P t z * xs P t z →
      0 < lo P t z ∧ IsOpt P t z (fun _ => 0) (fun _ => lo P t z)) ∧
    (curv P t z * xs P t z < -(P.km 0 + P.beta * P.kp 0) →
      IsOpt P t z (fun _ => P.cap 0) (fun _ => 0))

open Standalone.M6QuarterlyBandStaticCeiling in
/-- Part 6's only-if thresholds, in claim 029's one-instrument model with pure-learning marking.
Looking ahead lowers the alpha a trade needs by at most the factor `1 - β` on the rate:
- from a zero holding the fund stays at zero (`lo_t = 0`) when `α̂_t ≤ (1 - β)κ⁺`;
- at the cap it stays at the cap (`hi_t = x̄`) when `α̂_t - c_t x̄ ≥ -(1 - β)κ⁻`. This is the mirror at the
  cap, with the cap's risk charge `c_t x̄`;
- it is sold out entirely from any incumbent (`hi_t = 0`) only if `α̂_t ≤ -(1 - β)κ⁻`. -/
def OnlyIf : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 1 Z Ω), Setting P → (∀ ω, P.gross ω 0 = 1) → ∀ t z, t < P.T →
    (curv P t z * xs P t z ≤ (1 - P.beta) * P.kp 0 →
      IsOpt P t z (fun _ => 0) (fun _ => 0) ∧ lo P t z = 0) ∧
    (-(1 - P.beta) * P.km 0 ≤ curv P t z * xs P t z - curv P t z * P.cap 0 →
      IsOpt P t z (fun _ => P.cap 0) (fun _ => P.cap 0) ∧ hi P t z = P.cap 0) ∧
    (hi P t z = 0 → curv P t z * xs P t z ≤ -(1 - P.beta) * P.km 0)

/-- Claim 102, parts 1-5 and part 6's thresholds. -/
def statement : Prop :=
  Criterion ∧ EtfTest ∧ SpanningRule ∧ ReHedge ∧ Pinned ∧ Sufficient ∧ BudgetStrip ∧ SureTrade ∧ OnlyIf

end

end Standalone.M7FundHoldBuySellCriterion

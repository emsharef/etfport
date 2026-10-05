import Standalone.M7TwoStageExactnessLoss

/-!
# Claim 105: how premium error enters fund choice

Statement only; the proof is `Novel/M7PremiumErrorInFundChoiceProof.lean`.

One review of claim 104's model: claim 027's M2 `Data` in the reference case, with frictionless
residual-free ETFs. `θ = (λ̂, α̂)` are the beliefs, `λ` is the true premium and `e = λ̂ - λ` is the
premium error. Fund `i` has loading `β_i = (B^A_i)'`. Claim 031's hedge map `J` and Schur complement
`Σ~_{U.R}` give the reduced moments `α^red_i = α̂_i + β_i'J'λ̂` and `s^red_i = v_i + β_i'Σ~_{U.R}β_i`.
The alpha-band holding `a_i(λ̂)` is claim 104's `bandHold` at `(α^red_i, γ s^red_i)`. Under spanning,
`J = 0` and it is `bandHold` at `(α̂_i, γ v_i)`.

Parts 2b-2d are statements about `bandHold` as a function of the reduced alpha. The premium error
shifts the reduced alpha by `δ = β_i'J'e`, and `MoveVec` states the move as a function of `λ̂`.

Paper-level: the expectations under `e ~ (0, P^λ)`. These are 2b's expected squared move, 2d's
expected loss, and part 3's expected squared error. Each is the second-moment identity
`E(u'e)² = u'P^λ u` (and Jensen) applied to a formal pointwise bound here.

Part 2c is stated in a corrected form, reported in lean's note to mathb and red:
- the fund is bought iff `m + δ > κ⁺` and `x⁻ < x̄`;
- it is sold iff `m + δ < -κ⁻` and `x⁻ > 0`;
- a bought fund is turned into a hold or a sale iff `δ ≤ -(m - κ⁺)`.
-/

namespace Standalone.M7PremiumErrorInFundChoice

open Filter Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M2TwoStageSeparation (Gf Inputs)
open Standalone.M5MissingDirectionLeak (PiR Jmap Schur)

noncomputable section

/-- Part 1a: premium error does not enter fund choice through spanning ETFs. Take two instances with
frictionless spanning ETFs that share the fund inputs: alpha, `v`, `γ`, fund rates, incumbents and caps.
At joint optima of the two, with the budget and ETF bounds slack, every fund is held at the same
position, whatever the premia, the premium uncertainty (`Σ~_f`) and the loadings. That position is
the band holding `bandHold(α̂_i, γ v_i, κ⁺_i, κ⁻_i, x⁻_i, x̄_i)`. -/
def NoLeak : Prop :=
  ∀ (m K : ℕ) (S₁ S₂ : Type) [Fintype S₁] [Fintype S₂] (D₁ : Data m K K S₁) (D₂ : Data m K K S₂)
    (θ₁ θ₂ : Params m K) (Sf₁ Sf₂ : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D₁ → Inputs D₂ → FrictionlessSpanning D₁ Sf₁ v → FrictionlessSpanning D₂ Sf₂ v →
    θ₁.alpha = θ₂.alpha → D₁.gamma = D₂.gamma →
    (∀ k, D₁.kplus (Sum.inl k) = D₂.kplus (Sum.inl k) ∧ D₁.kminus (Sum.inl k) = D₂.kminus (Sum.inl k) ∧
      w0 D₁ (Sum.inl k) = w0 D₂ (Sum.inl k) ∧ D₁.wbar (Sum.inl k) = D₂.wbar (Sum.inl k)) →
    ∀ w₁ ∈ F D₁, IsMaxOn (fun w => score D₁ w θ₁) (F D₁) w₁ → 0 < cash D₁ w₁ →
      (∀ j, 0 < w₁ (Sum.inr j) ∧ w₁ (Sum.inr j) < D₁.wbar (Sum.inr j)) →
    ∀ w₂ ∈ F D₂, IsMaxOn (fun w => score D₂ w θ₂) (F D₂) w₂ → 0 < cash D₂ w₂ →
      (∀ j, 0 < w₂ (Sum.inr j) ∧ w₂ (Sum.inr j) < D₂.wbar (Sum.inr j)) →
    ∀ k, w₁ (Sum.inl k) = w₂ (Sum.inl k) ∧
      w₁ (Sum.inl k) = bandHold (θ₁.alpha k) (D₁.gamma * v k) (D₁.kplus (Sum.inl k))
        (D₁.kminus (Sum.inl k)) (w0 D₁ (Sum.inl k)) (D₁.wbar (Sum.inl k))

/-- Part 1b: the exposure's Markowitz loss. At the true premium, `G_λ(y) = λ'y - (γ/2) y'Σ~y` and
`y*(λ) = (γΣ~)⁻¹λ`. Setting the exposure at `y*(λ̂)` costs `e'Σ~⁻¹e/(2γ)`. -/
def MarkowitzLoss : Prop :=
  ∀ (K : ℕ) (Sg : Matrix (Fin K) (Fin K) ℝ) (γ : ℝ) (lam lamHat : Fin K → ℝ), Sg.PosDef → 0 < γ →
    (lam ⬝ᵥ ((γ • Sg)⁻¹ *ᵥ lam) - γ / 2 * (((γ • Sg)⁻¹ *ᵥ lam) ⬝ᵥ (Sg *ᵥ ((γ • Sg)⁻¹ *ᵥ lam)))) -
      (lam ⬝ᵥ ((γ • Sg)⁻¹ *ᵥ lamHat) -
        γ / 2 * (((γ • Sg)⁻¹ *ᵥ lamHat) ⬝ᵥ (Sg *ᵥ ((γ • Sg)⁻¹ *ᵥ lamHat)))) =
      (lamHat - lam) ⬝ᵥ (Sg⁻¹ *ᵥ (lamHat - lam)) / (2 * γ)

/-- Part 2, the joint optimum under one unreachable fund. This is claim 104's 2c setting, with the
budget and every bound except fund `i`'s slack. Fund `i` is at the band holding of its reduced
moments. Every other fund is at its spanning band holding. The ETFs give the best hedge of the funds
held. -/
def UnreachJoint : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (i : Fin m),
    Inputs D → OneUnreachable D Sf v i →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ → SlackBut D i wJ →
    wJ (Sum.inl i) = bandHold (θ.alpha i + D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam))
      (D.gamma * (v i + D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i))) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i)) ∧
    (∀ k, k ≠ i → wJ (Sum.inl k) = bandHold (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (D.wbar (Sum.inl k))) ∧
    ∀ z, Gf D θ (D.BAᵀ *ᵥ active wJ + D.BEᵀ *ᵥ z) ≤ Gf D θ (exposure D wJ)

/-- Part 2a, where the premium enters: `λ̂` reaches fund `i`'s joint holding only through the scalar
`β_i'J'λ̂`. Two premium beliefs with the same scalar give the same holding. -/
def SameShift : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ θ' : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (i : Fin m),
    Inputs D → OneUnreachable D Sf v i → θ.alpha = θ'.alpha →
    D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam) = D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ'.lam) →
    ∀ w ∈ F D, IsMaxOn (fun w => score D w θ) (F D) w → SlackBut D i w →
    ∀ w' ∈ F D, IsMaxOn (fun w => score D w θ') (F D) w' → SlackBut D i w' →
    w (Sum.inl i) = w' (Sum.inl i)

/-- Part 2a, the narrowing:
- `s^red_i ≥ v_i`;
- the band width `(κ⁺ + κ⁻)/(γ s^red_i)` is the spanned width `(κ⁺ + κ⁻)/(γ v_i)` times
  `v_i/s^red_i`. -/
def Narrowing : Prop :=
  ∀ (K M : ℕ) (BE : Matrix (Fin M) (Fin K) ℝ) (Sg : Matrix (Fin K) (Fin K) ℝ) (β : Fin K → ℝ)
    (alpha v γ kp km : ℝ), IsUnit (BE * BEᵀ).det → Sg.PosDef → 0 < v → 0 < γ →
    v ≤ v + β ⬝ᵥ (Schur BE Sg *ᵥ β) ∧
    (alpha + km) / (γ * (v + β ⬝ᵥ (Schur BE Sg *ᵥ β))) - (alpha - kp) / (γ * (v + β ⬝ᵥ (Schur BE Sg *ᵥ β))) =
      v / (v + β ⬝ᵥ (Schur BE Sg *ᵥ β)) * ((kp + km) / (γ * v))

/-- Part 2a, learning (claim 031's part 5 read at one fund). Along the Kalman path
`Σ~_t = Σ_f + P^λ_t`:
- `s^red_{i,t}` is nonincreasing and tends to `v_i + β_i'Σ_{f,U.R}β_i`, so the estimation part of the
  risk leak learns away;
- the shift `β_i'J_t'λ̂` tends to `β_i'J_f'λ̂`, and `J_f'` is the identity on unreachable directions, so
  the mean leak persists. -/
def LearningLeak : Prop :=
  ∀ (K M : ℕ) (BE : Matrix (Fin M) (Fin K) ℝ) (Sf P0 : Matrix (Fin K) (Fin K) ℝ)
    (β lamHat : Fin K → ℝ) (v : ℝ), IsUnit (BE * BEᵀ).det → Sf.PosDef → P0.PosDef →
    (∀ t, v + β ⬝ᵥ (Schur BE (Sf + Standalone.M5PartialAdjustmentSplit.kal P0 1 Sf (t + 1)) *ᵥ β) ≤
      v + β ⬝ᵥ (Schur BE (Sf + Standalone.M5PartialAdjustmentSplit.kal P0 1 Sf t) *ᵥ β)) ∧
    Tendsto (fun t => v + β ⬝ᵥ (Schur BE (Sf + Standalone.M5PartialAdjustmentSplit.kal P0 1 Sf t) *ᵥ β))
      atTop (nhds (v + β ⬝ᵥ (Schur BE Sf *ᵥ β))) ∧
    Tendsto (fun t => β ⬝ᵥ ((Jmap BE (Sf + Standalone.M5PartialAdjustmentSplit.kal P0 1 Sf t))ᵀ *ᵥ lamHat))
      atTop (nhds (β ⬝ᵥ ((Jmap BE Sf)ᵀ *ᵥ lamHat))) ∧
    ∀ u, PiR BE *ᵥ u = 0 → (Jmap BE Sf)ᵀ *ᵥ u = u

/-- Part 2b, how much the holding moves, as a function of the reduced alpha:
- the band holding is `1/c`-Lipschitz;
- on a common buy piece (`x⁻ < lo` and `0 < lo < x̄` at both alphas) it moves by exactly `δ/c`;
- on a common sell piece (`hi < x⁻` and `0 < hi < x̄` at both) it moves by exactly `δ/c`;
- on a common hold piece it does not move;
- where the unclipped holding is at or beyond the same bound at both alphas, it does not move. -/
def Move : Prop :=
  ∀ (alpha alpha' c kp km xm xbar : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → 0 ≤ xbar →
    |bandHold alpha' c kp km xm xbar - bandHold alpha c kp km xm xbar| ≤ |alpha' - alpha| / c ∧
    (xm < (alpha - kp) / c → xm < (alpha' - kp) / c → 0 < (alpha - kp) / c → 0 < (alpha' - kp) / c →
      (alpha - kp) / c < xbar → (alpha' - kp) / c < xbar →
      bandHold alpha' c kp km xm xbar - bandHold alpha c kp km xm xbar = (alpha' - alpha) / c) ∧
    ((alpha + km) / c < xm → (alpha' + km) / c < xm → 0 < (alpha + km) / c → 0 < (alpha' + km) / c →
      (alpha + km) / c < xbar → (alpha' + km) / c < xbar →
      bandHold alpha' c kp km xm xbar - bandHold alpha c kp km xm xbar = (alpha' - alpha) / c) ∧
    ((alpha - kp) / c ≤ xm → xm ≤ (alpha + km) / c → (alpha' - kp) / c ≤ xm → xm ≤ (alpha' + km) / c →
      bandHold alpha' c kp km xm xbar = bandHold alpha c kp km xm xbar) ∧
    (max ((alpha - kp) / c) (min ((alpha + km) / c) xm) ≤ 0 →
      max ((alpha' - kp) / c) (min ((alpha' + km) / c) xm) ≤ 0 →
      bandHold alpha' c kp km xm xbar = bandHold alpha c kp km xm xbar) ∧
    (xbar ≤ max ((alpha - kp) / c) (min ((alpha + km) / c) xm) →
      xbar ≤ max ((alpha' - kp) / c) (min ((alpha' + km) / c) xm) →
      bandHold alpha' c kp km xm xbar = bandHold alpha c kp km xm xbar)

/-- Part 2b in `λ̂` (and part 3's naive holding, with `J = I`): the holding
`a(λ̂) = bandHold(α̂ + β'J'λ̂, c, …)` is continuous in `λ̂`, and `|a(λ̂) - a(λ)| ≤ |β'J'e|/c`. -/
def MoveVec : Prop :=
  ∀ (K : ℕ) (β : Fin K → ℝ) (Jm : Matrix (Fin K) (Fin K) ℝ) (alpha c kp km xm xbar : ℝ),
    0 < c → 0 ≤ kp → 0 ≤ km → 0 ≤ xbar →
    Continuous (fun lamHat : Fin K → ℝ => bandHold (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lamHat)) c kp km xm xbar) ∧
    ∀ lam lamHat : Fin K → ℝ,
      |bandHold (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lamHat)) c kp km xm xbar -
        bandHold (alpha + β ⬝ᵥ (Jmᵀ *ᵥ lam)) c kp km xm xbar| ≤ |β ⬝ᵥ (Jmᵀ *ᵥ (lamHat - lam))| / c

/-- Part 2c, when the premium error changes the decision (corrected form). Let `m = α - c x⁻` at the
true reduced alpha `α`, and let `δ` shift the reduced alpha. At `α + δ`:
- the holding is above the incumbent (a purchase) iff `m + δ > κ⁺` and `x⁻ < x̄`;
- it is below the incumbent (a sale) iff `m + δ < -κ⁻` and `0 < x⁻`.
So:
- a fund held at `α` (`m ∈ [-κ⁻, κ⁺]`) is not moved by any `δ` with `|δ| ≤ slack = min(κ⁺ - m, m + κ⁻)`;
- a fund bought at `α` is held or sold at `α + δ` iff `δ ≤ -(m - κ⁺)`, and `-(m - κ⁺) < 0`. -/
def Flip : Prop :=
  ∀ (alpha delta c kp km xm xbar : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → 0 ≤ xm → xm ≤ xbar →
    (xm < bandHold (alpha + delta) c kp km xm xbar ↔ kp < alpha - c * xm + delta ∧ xm < xbar) ∧
    (bandHold (alpha + delta) c kp km xm xbar < xm ↔ alpha - c * xm + delta < -km ∧ 0 < xm) ∧
    (-km ≤ alpha - c * xm → alpha - c * xm ≤ kp →
      |delta| ≤ min (kp - (alpha - c * xm)) (alpha - c * xm + km) →
      bandHold (alpha + delta) c kp km xm xbar = xm) ∧
    (xm < bandHold alpha c kp km xm xbar →
      (bandHold (alpha + delta) c kp km xm xbar ≤ xm ↔ delta ≤ -(alpha - c * xm - kp)) ∧
      -(alpha - c * xm - kp) < 0)

/-- Part 2d, what it costs. The fund holds `a' = bandHold(α + δ, …)` when the true reduced alpha is `α`,
whose band holding is `a`. The loss in claim 104's reduced objective `ψ` at `α` satisfies
- `0 ≤ loss ≤ (c/2)Δ² + (κ⁺ + κ⁻ + μ)|Δ|`, with `Δ = a' - a` and `|Δ| ≤ |δ|/c`;
- `μ`, the box's normal-cone term at `a`, is zero when `a` is interior. -/
def Cost : Prop :=
  ∀ (alpha delta c kp km xm xbar : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → 0 ≤ xbar →
    let a := bandHold alpha c kp km xm xbar
    let a' := bandHold (alpha + delta) c kp km xm xbar
    let mu := max 0 (max (alpha - c * a - kp) (-km - (alpha - c * a)))
    0 ≤ psi alpha c kp km xm a - psi alpha c kp km xm a' ∧
    psi alpha c kp km xm a - psi alpha c kp km xm a' ≤ c / 2 * (a' - a) ^ 2 + (kp + km + mu) * |a' - a| ∧
    |a' - a| ≤ |delta| / c ∧ (0 < a → a < xbar → mu = 0)

/-- Part 3, the naive rule's loss. Take frictionless spanning ETFs. Fix any fund vector (the naive
holdings `bandHold(α̂_i + β_i'λ̂, γσ_i², …)` are one), and re-optimize the ETFs: `w_a` maximizes the score
over the holdings in `F` with the same fund vector. The budget and ETF bounds are slack there and at the
joint optimum `w_J`. Then:
- the loss is exactly `Σ_i [ψ_i(a_i(λ̂)) - ψ_i(a_i)]`, each term nonnegative;
- it is zero iff every fund's holding is its band holding. -/
def NaiveLoss : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → FrictionlessSpanning D Sf v →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ → 0 < cash D wJ →
      (∀ j, 0 < wJ (Sum.inr j) ∧ wJ (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∀ wa ∈ F D, IsMaxOn (fun w => score D w θ) {w | w ∈ F D ∧ active w = active wa} wa →
      0 < cash D wa → (∀ j, 0 < wa (Sum.inr j) ∧ wa (Sum.inr j) < D.wbar (Sum.inr j)) →
    score D wJ θ - score D wa θ =
      ∑ k, (psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
          (w0 D (Sum.inl k)) (wJ (Sum.inl k)) -
        psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
          (w0 D (Sum.inl k)) (wa (Sum.inl k))) ∧
    (∀ k, 0 ≤ psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
          (w0 D (Sum.inl k)) (wJ (Sum.inl k)) -
        psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
          (w0 D (Sum.inl k)) (wa (Sum.inl k))) ∧
    (score D wJ θ = score D wa θ ↔ ∀ k, wa (Sum.inl k) = bandHold (θ.alpha k) (D.gamma * v k)
      (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (D.wbar (Sum.inl k)))

/-- Part 3, the zero-incumbent readings (`x⁻ = 0`, `x̄ > 0`):
- the band holding is positive iff the (reduced or naive total) alpha exceeds `κ⁺`;
- a fund held at `a > 0` where the band holding is 0 loses `ψ(0) - ψ(a) = -(α a - (c/2)a² - κ⁺ a)`,
  positive iff `α < κ⁺ + (c/2) a`;
- a fund passed over when its band holding is positive loses `ψ(a_i) - ψ(0) > 0`. -/
def ZeroIncumbent : Prop :=
  ∀ (alpha c kp km xbar : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → 0 < xbar →
    (0 < bandHold alpha c kp km 0 xbar ↔ kp < alpha) ∧
    (∀ a, 0 < a →
      psi alpha c kp km 0 0 - psi alpha c kp km 0 a = -(alpha * a - c / 2 * a ^ 2 - kp * a) ∧
      (0 < psi alpha c kp km 0 0 - psi alpha c kp km 0 a ↔ alpha < kp + c / 2 * a)) ∧
    (0 < bandHold alpha c kp km 0 xbar →
      0 < psi alpha c kp km 0 (bandHold alpha c kp km 0 xbar) - psi alpha c kp km 0 0)

/-- Claim 105, parts 1-3 (the expectations paper-level). -/
def statement : Prop :=
  NoLeak ∧ MarkowitzLoss ∧ UnreachJoint ∧ SameShift ∧ Narrowing ∧ LearningLeak ∧ Move ∧ MoveVec ∧
    Flip ∧ Cost ∧ NaiveLoss ∧ ZeroIncumbent

end

end Standalone.M7PremiumErrorInFundChoice

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Standalone.M2SoftTargetTwoStage
import Standalone.M2TwoStageSeparation
import Standalone.M5MissingDirectionLeak

/-!
# Claim 104: when two-stage implementation is exact, and what it loses

Statement only; the proof is `Novel/M7TwoStageExactnessLossProof.lean`.

The statement is complete: every part (0, 1, 2a-2c, 3a-3d) is formalized. Parts 0, 2b and 3c are
conditional on ledger entry AX-13 (polyhedral KKT), which enters as the hypothesis `AX13` (the
Upstream structure `PolyKKT`). The model is claim 027's M2 `Data` (one review: holdings as fractions of
wealth, the funded cash `k`, the box, the kinked cost `τ`, scenario moments), which claims 027 and 028
state for general counts. `RefCase` fixes claim 104's reference case: factor second moment
`Σ~_f`, fund residual moment `V`, ETF residual moment `Σ_E`, and no cross moments. `Represent`
shows every positive semidefinite triple arises from finitely many scenarios, so every claim-104
instance is such a `Data`.

Part 3b, the unreachable fund's loss bracket, is stated on the fund's
reduced objective
`ψ(a) = α a - (c/2) a² - κ⁺(a - x⁻)⁺ - κ⁻(x⁻ - a)⁺` on `[0, x̄]`, with `c = γ s^red_i > 0`.
The joint holding `a_J` maximizes `ψ` on the box; the fibre holding `a*` is any point of the box.
`m_J = α - c a_J` is the smooth marginal at `a_J`, and `μ_J = max(0, m_J - κ⁺, -κ⁻ - m_J)` is its
distance from the cost band.
-/

namespace Standalone.M7TwoStageExactnessLoss

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses

noncomputable section

/-- Scenario second moment `Σ_s q_s x_s y_s'`. -/
def mom {S : Type} [Fintype S] {a b : ℕ} (q : S → ℝ) (x : S → Fin a → ℝ) (y : S → Fin b → ℝ) :
    Matrix (Fin a) (Fin b) ℝ :=
  fun i j => ∑ s, q s * (x s i * y s j)

/-- Claim 104's reference case: factor moment `Σ~_f`, fund residual moment `V`, ETF residual
moment `Σ_E`, and no factor-residual or fund-ETF cross moments. -/
def RefCase {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S) (Sf : Matrix (Fin K) (Fin K) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  mom D.q D.zf D.zf = Sf ∧ mom D.q D.zA D.zA = V ∧ mom D.q D.zE D.zE = SE ∧
    mom D.q D.zA D.zE = 0 ∧ mom D.q D.zf D.zA = 0 ∧ mom D.q D.zf D.zE = 0

/-- Part 1, the reference case: the cross moments vanish on every holding, the residual moment is
`a'Va + p'Σ_E p`, and so `V` is concave on `B_F` (claim 027's part 0). Claims 027 and 028 hold for
every `Data`, so their parts transfer; they are conjuncts of `statement`. -/
def Transfer : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K) (Sf : Matrix (Fin K) (Fin K) ℝ)
    (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin n) (Fin n) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE →
    Standalone.M2TwoStageSeparation.sigF D = Sf ∧
    (∀ w, Standalone.M2TwoStageSeparation.crossM D w = 0) ∧
    (∀ w, Standalone.M2TwoStageSeparation.resM D w =
      active w ⬝ᵥ (V *ᵥ active w) + etf w ⬝ᵥ (SE *ᵥ etf w)) ∧
    ConcaveOn ℝ (Standalone.M2TwoStageSeparation.BF D) (Standalone.M2TwoStageSeparation.Vr D θ)

/-- Every positive semidefinite `(Σ~_f, V, Σ_E)` is the reference case of a finite scenario law with
mean-zero shocks. -/
def Represent : Prop :=
  ∀ (m n K : ℕ) (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin n) (Fin n) ℝ),
    Sf.PosSemidef → V.PosSemidef → SE.PosSemidef →
    ∃ (S : Type) (_ : Fintype S) (q : S → ℝ) (zf : S → Fin K → ℝ) (zA : S → Fin m → ℝ) (zE : S → Fin n → ℝ),
      (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧ ∑ s, q s • zf s = 0 ∧ ∑ s, q s • zA s = 0 ∧ ∑ s, q s • zE s = 0 ∧
      mom q zf zf = Sf ∧ mom q zA zA = V ∧ mom q zE zE = SE ∧
      mom q zA zE = 0 ∧ mom q zf zA = 0 ∧ mom q zf zE = 0

/-- The fund's reduced objective `ψ`. -/
def psi (alpha c kp km xm : ℝ) (a : ℝ) : ℝ :=
  alpha * a - c / 2 * a ^ 2 - kp * max (a - xm) 0 - km * max (xm - a) 0

/-- Part 3b: `(c/2)(a_J - a*)² ≤ ψ(a_J) - ψ(a*) ≤ (c/2)(a_J - a*)² + (κ⁺ + κ⁻ + μ_J)|a_J - a*|`, and
`μ_J = 0` when `a_J` is interior to the box. -/
def Bracket : Prop :=
  ∀ (alpha c kp km xm xbar aJ as : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km →
    aJ ∈ Set.Icc 0 xbar → IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) aJ → as ∈ Set.Icc 0 xbar →
    let mJ := alpha - c * aJ
    let muJ := max 0 (max (mJ - kp) (-km - mJ))
    c / 2 * (aJ - as) ^ 2 ≤ psi alpha c kp km xm aJ - psi alpha c kp km xm as ∧
    psi alpha c kp km xm aJ - psi alpha c kp km xm as ≤ c / 2 * (aJ - as) ^ 2 + (kp + km + muJ) * |aJ - as| ∧
    (0 < aJ → aJ < xbar → muJ = 0)

/-- The band holding `clip(clip(x⁻, (α - κ⁺)/c, (α + κ⁻)/c), 0, x̄)`: the incumbent clipped to the
fund's alpha band, then to its box. -/
def bandHold (alpha c kp km xm xbar : ℝ) : ℝ :=
  max 0 (min xbar (max ((alpha - kp) / c) (min ((alpha + km) / c) xm)))

/-- Part 2a's inputs: spanning frictionless ETFs (`M = K`, `B^E` invertible, `Σ_E = 0`, `c^E = 0`,
`κ_E = 0`), the reference case with `V = diag v`, `v > 0`, `Σ~_f` positive definite, and `γ > 0`. -/
def FrictionlessSpanning {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) : Prop :=
  RefCase D Sf (diagonal v) 0 ∧ IsUnit D.BE.det ∧ D.cE = 0 ∧
    (∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) ∧ (∀ i, 0 < v i) ∧ Sf.PosDef ∧
    0 < D.gamma

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr) in
/-- Part 2a: with frictionless spanning ETFs, and at a joint optimum `w_J` with a slack budget and every
ETF strictly inside its box, the exposure is `b_TB = (γ Σ~_f)⁻¹ λ`, fund `i` is at its band holding,
and the ETFs are at `R'(b_TB - (B^A)' a)`. Stage 1 chooses `b_TB`, stage 2 on its fibre returns the
same fund holdings, and `T = J`. The soft procedure is exact: for any exposure set `R ⊇ B_F`, stage 1
on `R` has `ν = 0`, and every soft stage-2 maximizer has the joint value. -/
def Spanning : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → FrictionlessSpanning D Sf v →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ → 0 < cash D wJ →
    (∀ j, 0 < wJ (Sum.inr j) ∧ wJ (Sum.inr j) < D.wbar (Sum.inr j)) →
    let bTB := (D.gamma • Sf)⁻¹ *ᵥ θ.lam
    exposure D wJ = bTB ∧
    (∀ i, wJ (Sum.inl i) = bandHold (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i))) ∧
    etf wJ = (D.BEᵀ)⁻¹ *ᵥ (bTB - D.BAᵀ *ᵥ active wJ) ∧
    (∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs → bs = bTB) ∧
    (∀ w₂ ∈ fibre D bTB, IsMaxOn (Hr D θ) (fibre D bTB) w₂ → active w₂ = active wJ) ∧
    Gf D θ bTB + Vr D θ bTB = score D wJ θ ∧
    ∀ R : Set (Fin K → ℝ), BF D ⊆ R → ∀ bs ∈ R,
      IsMaxOn (Standalone.M2SoftTargetTwoStage.Gf D θ) R bs →
      Standalone.M2SoftTargetTwoStage.nu D θ bs = 0 ∧
      ∀ w₂ ∈ F D, IsMaxOn (Standalone.M2SoftTargetTwoStage.Ssoft D θ bs) (F D) w₂ →
        score D w₂ θ = score D wJ θ

open Standalone.M5MissingDirectionLeak (PiU) in
/-- Part 2c's inputs: `B^E` of full row rank, frictionless residual-free ETFs, the reference case with
`V = diag v`, `v > 0`, `Σ~_f` positive definite, `γ > 0`; fund `i`'s loading `β_i = (B^A_i)'` has an
unreachable part `u = Π_U β_i ≠ 0`, and every other fund's loading lies in `L_E`. -/
def OneUnreachable {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (i : Fin m) : Prop :=
  RefCase D Sf (diagonal v) 0 ∧ IsUnit (D.BE * D.BEᵀ).det ∧ D.cE = 0 ∧
    (∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) ∧ (∀ k, 0 < v k) ∧ Sf.PosDef ∧
    0 < D.gamma ∧ PiU D.BE *ᵥ D.BA i ≠ 0 ∧ ∀ k, k ≠ i → PiU D.BE *ᵥ D.BA k = 0

/-- A slack budget, and every bound slack except fund `i`'s own. -/
def SlackBut {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S) (i : Fin m)
    (w : Inst m n → ℝ) : Prop :=
  0 < cash D w ∧ ∀ l, l ≠ Sum.inl i → 0 < w l ∧ w l < D.wbar l

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr) in
open Standalone.M5MissingDirectionLeak (Jmap Schur) in
/-- Part 2c: one fund with an unreachable loading, everything else frictionless, and the budget and
every bound other than fund `i`'s slack at the joint optimum `w_J` and at the stage-2 holding `w₂`.
With claim 031's hedge map `J` and Schur complement `Σ~_{U.R}`, write `p = B^A_i J'λ̂` and
`s_U = B^A_i Σ~_{U.R} (B^A_i)'` (so `α^red_i = α̂_i + p` and `s^red_i = v_i + s_U`). Then `s_U > 0`;
stage 2 holds the fund at `a*_i = clip(p/(γ s_U), 0, x̄_i)`, the joint optimum at the band holding
`a_J` of the reduced objective `ψ_i`; `Λ = ψ_i(a_J) - ψ_i(a*_i) ≥ 0`; and `T = J` iff `a*_i = a_J`,
iff `a*_i` maximizes `ψ_i` on the box. -/
def Unreachable : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (i : Fin m),
    Standalone.M2TwoStageSeparation.Inputs D → OneUnreachable D Sf v i →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ → SlackBut D i wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
    ∀ w₂ ∈ fibre D bs, IsMaxOn (Hr D θ) (fibre D bs) w₂ → SlackBut D i w₂ →
    let p := D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)
    let sU := D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)
    let aS := max 0 (min (D.wbar (Sum.inl i)) (p / (D.gamma * sU)))
    let psiR := psi (θ.alpha i + p) (D.gamma * (v i + sU)) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
    let aJ := bandHold (θ.alpha i + p) (D.gamma * (v i + sU)) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i))
    0 < sU ∧ w₂ (Sum.inl i) = aS ∧ wJ (Sum.inl i) = aJ ∧
    score D wJ θ - (Gf D θ bs + Vr D θ bs) = psiR aJ - psiR aS ∧ 0 ≤ psiR aJ - psiR aS ∧
    (Gf D θ bs + Vr D θ bs = score D wJ θ ↔ aS = aJ) ∧
    (aS = aJ ↔ IsMaxOn psiR (Set.Icc 0 (D.wbar (Sum.inl i))) aS)

/-- `AX-13`, polyhedral KKT, as cited (`rockafellar1970convex` Theorems 27.4, 28.2-28.3): for `f`
concave and finite on `ℝ^ι` and a polyhedron `P = {x : a_l'x ≤ b_l}`, a point `x ∈ P` maximizes `f`
on `P` iff some `η ≥ 0`, zero on slack constraints, makes `Σ_l η_l a_l` a supergradient of `f` at `x`.
It is not proved here. It enters as the hypothesis structure `Upstream.KKT.PolyKKT` (with its instance
in `Upstream/PolyKKT.lean`), and part 0 takes it as a hypothesis. -/
def AX13 : Prop :=
  ∀ (ι Λ : Type) [Fintype ι] [Fintype Λ] (f : (ι → ℝ) → ℝ) (a : Λ → ι → ℝ) (b : Λ → ℝ),
    ConcaveOn ℝ Set.univ f → ∀ x, (∀ l, a l ⬝ᵥ x ≤ b l) →
    (IsMaxOn f {y | ∀ l, a l ⬝ᵥ y ≤ b l} x ↔
      ∃ η : Λ → ℝ, (∀ l, 0 ≤ η l) ∧ (∀ l, a l ⬝ᵥ x < b l → η l = 0) ∧
        ∀ y, f y ≤ f x + (∑ l, η l • a l) ⬝ᵥ (y - x))

/-- The smooth marginal `g(w) = μ - γ Σ w`. -/
def grad {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S) (θ : Params m K)
    (w : Inst m n → ℝ) : Inst m n → ℝ :=
  mu D θ - D.gamma • (covariance D *ᵥ w)

/-- `t ∈ T_l(w)`, the trade-sign slope set: `{κ⁺}` after a purchase, `{-κ⁻}` after a sale, and
`[-κ⁻, κ⁺]` at the incumbent. -/
def InSlope {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S) (w : Inst m n → ℝ) (l : Inst m n)
    (t : ℝ) : Prop :=
  -D.kminus l ≤ t ∧ t ≤ D.kplus l ∧ (w0 D l < w l → t = D.kplus l) ∧ (w l < w0 D l → t = -D.kminus l)

/-- The box signs of `R` at `x ∈ [0, x̄]`, in normal-cone form: `R ≤ 0` below the cap and `R ≥ 0`
above zero. When `x̄ > 0`, these are the claim's three cases: `R = 0` strictly inside, `R ≤ 0` at `0`,
and `R ≥ 0` at `x̄`. -/
def BoxSign (xbar x R : ℝ) : Prop := (x < xbar → R ≤ 0) ∧ (0 < x → 0 ≤ R)

/-- Part 0's multiplier criterion at `w`: some `η ≥ 0` with `η k(w) = 0`, and slopes `t_l ∈ T_l(w)`,
such that every `R_l = g_l(w) - η - (1 + η) t_l` has the box signs. -/
def JointCriterion {m n K : ℕ} {S : Type} [Fintype S] (D : Data m n K S) (θ : Params m K)
    (w : Inst m n → ℝ) : Prop :=
  ∃ (η : ℝ) (t : Inst m n → ℝ), 0 ≤ η ∧ η * cash D w = 0 ∧ (∀ l, InSlope D w l (t l)) ∧
    ∀ l, BoxSign (D.wbar l) (w l) (grad D θ w l - η - (1 + η) * t l)

/-- Part 0 (AX-13 applied to the lifted problem): a feasible `w` is the joint optimum iff the
multiplier criterion holds. -/
def JointOptimality : Prop :=
  AX13 → ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K),
    Standalone.M2TwoStageSeparation.Inputs D →
    ∀ w ∈ F D, (IsMaxOn (fun w => score D w θ) (F D) w ↔ JointCriterion D θ w)

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr) in
/-- Part 2b (given AX-13). Take spanning ETFs with frictions (`M = K`, `B^E` invertible, any `c^E`,
`κ_E`, `Σ_E`), the reference case with a general `V`, `Σ~_f` positive definite and `γ > 0`. At the
stage-2 holding `x₂` the budget is slack and every ETF is strictly inside its box. Then:
- `T = J` iff `x₂` is a joint optimum;
- that holds iff two conditions hold together. The ETF self-band: `-c^E_j - γ(Σ_E x₂^E)_j ∈ T_j(x₂)` for
  every ETF. The fund bands: `α̂_i - γ(V x₂^A)_i` lies in `T_i(x₂)`, with the box signs at the fund's
  bounds, for every fund;
- with `Σ_E = 0`, exactness puts each ETF fee at `-κ⁺_j` if stage 2 buys it, at `κ⁻_j` if it sells it,
  and always in `[-κ⁺_j, κ⁻_j]`. -/
def Frictions : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det → Sf.PosDef →
    0 < D.gamma →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
    ∀ x₂ ∈ fibre D bs, IsMaxOn (Hr D θ) (fibre D bs) x₂ → 0 < cash D x₂ →
    (∀ j, 0 < x₂ (Sum.inr j) ∧ x₂ (Sum.inr j) < D.wbar (Sum.inr j)) →
    (Gf D θ bs + Vr D θ bs = score D wJ θ ↔ IsMaxOn (fun w => score D w θ) (F D) x₂) ∧
    (Gf D θ bs + Vr D θ bs = score D wJ θ ↔
      (∀ j, InSlope D x₂ (Sum.inr j) (-D.cE j - D.gamma * (SE *ᵥ etf x₂) j)) ∧
      ∀ i, ∃ t, InSlope D x₂ (Sum.inl i) t ∧
        BoxSign (D.wbar (Sum.inl i)) (x₂ (Sum.inl i)) (θ.alpha i - D.gamma * (V *ᵥ active x₂) i - t)) ∧
    (SE = 0 → Gf D θ bs + Vr D θ bs = score D wJ θ → ∀ j,
      (w0 D (Sum.inr j) < x₂ (Sum.inr j) → D.cE j = -D.kplus (Sum.inr j)) ∧
      (x₂ (Sum.inr j) < w0 D (Sum.inr j) → D.cE j = D.kminus (Sum.inr j)) ∧
      -D.kplus (Sum.inr j) ≤ D.cE j ∧ D.cE j ≤ D.kminus (Sum.inr j))

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr) in
/-- Part 3c's criterion (given AX-13). Take spanning ETFs strictly inside their boxes at `x₂`, with the
budget allowed to bind. Write `e = λ̂ - γ Σ~_f b*` and `r_i = R'(B^A_i)'` with `R = (B^E)⁻¹`. Then `T = J`
iff, for some `η ≥ 0` with `η k(x₂) = 0` and slopes `t_l ∈ T_l(x₂)`:
- the ETF lines hold: `(B^E e)_j - c^E_j - γ(Σ_E x₂^E)_j = η + (1 + η) t_j`;
- the fund lines hold: `α̂_i - γ(V x₂^A)_i + r_i'(c^E + γ Σ_E x₂^E) + η Σ_j r_ij - η - (1 + η)(t_i - r_i't_E)`
  has the box signs. -/
def BindingBudget : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, ∀ x₂ ∈ fibre D bs, IsMaxOn (Hr D θ) (fibre D bs) x₂ →
    (∀ j, 0 < x₂ (Sum.inr j) ∧ x₂ (Sum.inr j) < D.wbar (Sum.inr j)) →
    let e := θ.lam - D.gamma • (Sf *ᵥ bs)
    let r := fun i => (D.BE⁻¹)ᵀ *ᵥ D.BA i
    (Gf D θ bs + Vr D θ bs = score D wJ θ ↔
      ∃ (η : ℝ) (t : Inst m K → ℝ), 0 ≤ η ∧ η * cash D x₂ = 0 ∧ (∀ l, InSlope D x₂ l (t l)) ∧
        (∀ j, (D.BE *ᵥ e) j - D.cE j - D.gamma * (SE *ᵥ etf x₂) j = η + (1 + η) * t (Sum.inr j)) ∧
        ∀ i, BoxSign (D.wbar (Sum.inl i)) (x₂ (Sum.inl i))
          (θ.alpha i - D.gamma * (V *ᵥ active x₂) i + r i ⬝ᵥ (D.cE + D.gamma • (SE *ᵥ etf x₂)) +
            η * ∑ j, r i j - η - (1 + η) * (t (Sum.inl i) - r i ⬝ᵥ (fun j => t (Sum.inr j)))))

/-- Part 3d, the soft procedure (claim 028 read for claim 104). Stage 1 maximizes `G` over an exposure
set `R`, with multiplier `ν = λ̂ - γ Σ~_f b*`, and `Σ~_f` is positive definite with `γ > 0`. Then
- `ν = 0` iff `b_TB = (γ Σ~_f)⁻¹ λ̂` lies in `R`;
- when `R` is convex, `ν` lies in its normal cone at `b*`, so for `R = B_F` it is the shadow price of the
  funded long-only constraint.

The loss bound `0 ≤ Λ_s ≤ ν'(b_J - b_s) ≤ |ν||b_J - b_s|` is claim 028's part 2 (in `statement`). -/
def SoftMultiplier : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → Standalone.M2TwoStageSeparation.sigF D = Sf →
    Sf.PosDef → 0 < D.gamma →
    ∀ (R : Set (Fin K → ℝ)), ∀ bs ∈ R, IsMaxOn (Standalone.M2SoftTargetTwoStage.Gf D θ) R bs →
      (Standalone.M2SoftTargetTwoStage.nu D θ bs = 0 ↔ (D.gamma • Sf)⁻¹ *ᵥ θ.lam ∈ R) ∧
      (Convex ℝ R → ∀ b ∈ R, Standalone.M2SoftTargetTwoStage.nu D θ bs ⬝ᵥ (b - bs) ≤ 0)

/-- The Euclidean norm `‖v‖₂ = √(v'v)`. -/
def enorm2 {k : ℕ} (v : Fin k → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN) in
/-- Part 3a, ETF frictions (2b's setting), in the corrected form at `b*` (lean's note to mathb and red).
`L0` bounds `‖Σ~_f^{-1/2} R‖_op`, that is `(Ru)'Σ~_f⁻¹(Ru) ≤ L0²‖u‖²` with `R = (B^E)⁻¹`, and `σ_E` bounds
`‖Σ_E‖_op`. `L_E = L0 (‖c^E‖₂ + γ σ_E ‖x̄^E‖₂ + ‖κ^max_E‖₂)`. Then
- every supergradient `s` of `V` at `b*` relative to `B_F` has dual norm `s'Σ~_f⁻¹s ≤ L_E²`;
- `V(b_J) - V(b*) ≤ L_E ‖b_J - b*‖_{Σ~_f}`;
- hence `Λ ≤ min(L_E²/(2γ), L_E ‖b_J - b*‖_{Σ~_f})`. -/
def EtfFrictionBound : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ)
    (L0 σE : ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det → Sf.PosDef →
    0 < D.gamma → 0 ≤ L0 → (∀ u, (D.BE⁻¹ *ᵥ u) ⬝ᵥ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ u)) ≤ L0 ^ 2 * (u ⬝ᵥ u)) →
    0 ≤ σE → (∀ p, (SE *ᵥ p) ⬝ᵥ (SE *ᵥ p) ≤ σE ^ 2 * (p ⬝ᵥ p)) →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
    ∀ x₂ ∈ fibre D bs, IsMaxOn (Hr D θ) (fibre D bs) x₂ → 0 < cash D x₂ →
    (∀ j, 0 < x₂ (Sum.inr j) ∧ x₂ (Sum.inr j) < D.wbar (Sum.inr j)) →
    let LE := L0 * (enorm2 D.cE + D.gamma * σE * enorm2 (fun j => D.wbar (Sum.inr j)) +
      enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))))
    (∀ s : Fin K → ℝ, (∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs + s ⬝ᵥ (b - bs)) →
      s ⬝ᵥ (Sf⁻¹ *ᵥ s) ≤ LE ^ 2) ∧
    Vr D θ (exposure D wJ) - Vr D θ bs ≤ LE * Real.sqrt (sqN D (exposure D wJ - bs)) ∧
    score D wJ θ - (Gf D θ bs + Vr D θ bs) ≤
      min (LE ^ 2 / (2 * D.gamma)) (LE * Real.sqrt (sqN D (exposure D wJ - bs)))

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN) in
/-- Part 3c's bound (given AX-13), with the budget allowed to bind at `x₂` and the ETFs spanning and
strictly inside their boxes there. The stage-2 problem has a cash multiplier `η₂ ≥ 0`, with
`η₂ k(x₂) = 0`, such that `x₂` maximizes `H + η₂ k` over the fibre points inside the box. With
`L_E = L0 (‖c^E‖₂ + γ σ_E ‖x̄^E‖₂ + η₂ √M + (1 + η₂)‖κ^max_E‖₂)`:
- some supergradient of `V` at `b*` relative to `B_F` (the stage-2 exposure multiplier) has dual norm
  at most `L_E`;
- `V(b_J) - V(b*) ≤ L_E ‖b_J - b*‖_{Σ~_f}`;
- `Λ ≤ min(L_E²/(2γ), L_E ‖b_J - b*‖_{Σ~_f})`.

"Every supergradient" would fail here, since a binding budget can put `b*` on the boundary of `B_F`
(lean's note to mathb and red). -/
def BudgetBound : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ)
    (L0 σE : ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det → Sf.PosDef →
    0 < D.gamma → 0 ≤ L0 → (∀ u, (D.BE⁻¹ *ᵥ u) ⬝ᵥ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ u)) ≤ L0 ^ 2 * (u ⬝ᵥ u)) →
    0 ≤ σE → (∀ p, (SE *ᵥ p) ⬝ᵥ (SE *ᵥ p) ≤ σE ^ 2 * (p ⬝ᵥ p)) →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ bs ∈ BF D, IsMaxOn (Gf D θ) (BF D) bs →
    ∀ x₂ ∈ fibre D bs, IsMaxOn (Hr D θ) (fibre D bs) x₂ →
    (∀ j, 0 < x₂ (Sum.inr j) ∧ x₂ (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∃ η₂ : ℝ, 0 ≤ η₂ ∧ η₂ * cash D x₂ = 0 ∧
      (∀ x : Inst m K → ℝ, (∀ l, 0 ≤ x l ∧ x l ≤ D.wbar l) → exposure D x = bs →
        Hr D θ x + η₂ * cash D x ≤ Hr D θ x₂) ∧
      let LE := L0 * (enorm2 D.cE + D.gamma * σE * enorm2 (fun j => D.wbar (Sum.inr j)) +
        η₂ * Real.sqrt K + (1 + η₂) * enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))))
      (∃ s : Fin K → ℝ, (∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs + s ⬝ᵥ (b - bs)) ∧
        s ⬝ᵥ (Sf⁻¹ *ᵥ s) ≤ LE ^ 2) ∧
      Vr D θ (exposure D wJ) - Vr D θ bs ≤ LE * Real.sqrt (sqN D (exposure D wJ - bs)) ∧
      score D wJ θ - (Gf D θ bs + Vr D θ bs) ≤
        min (LE ^ 2 / (2 * D.gamma)) (LE * Real.sqrt (sqN D (exposure D wJ - bs)))

/-- Claim 104, complete: claims 027 and 028 (the transfer), the reference case, the representation,
and parts 0, 1, 2a-2c and 3a-3d. Parts 0, 2b and 3c are conditional on AX-13. 3a is stated at `b*`,
and 3c's bound for the stage-2 multiplier's supergradient. -/
def statement : Prop :=
  JointOptimality ∧ Standalone.M2TwoStageSeparation.statement ∧
    Standalone.M2SoftTargetTwoStage.statement ∧ Transfer ∧ Represent ∧ Spanning ∧ Frictions ∧
    Unreachable ∧ EtfFrictionBound ∧ Bracket ∧ BindingBudget ∧ BudgetBound ∧ SoftMultiplier

end

end Standalone.M7TwoStageExactnessLoss

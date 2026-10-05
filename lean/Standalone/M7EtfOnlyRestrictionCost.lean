import Standalone.M7TwoStageExactnessLoss

/-!
# Claim 106: the cost of the ETF-only restriction

Statement only; the proof is `Novel/M7EtfOnlyRestrictionCostProof.lean`.

One review on claim 027's M2 `Data`, in claim 104's setting. The three action classes are:
- `F`, full trading, with value `J`;
- `Em`, where funds may be sold but not bought (`E^-`), with value `J^-`;
- `E0`, where funds are frozen (`E^0`), with value `J^0`.

Values are the scores at the classes' maximizers. The restriction's cost is `C^- = J - J^-`, and the
frozen-funds cost is `C^0 = J - J^0`. Fund `i`'s one-variable objective is claim 104's `psi`. Its
maximizer on `[0, x̄]` is the band holding `bandHold`, and its maximizer on `[0, x⁻]` is `bandHold` with
cap `x⁻`.

The closed forms `buyCost` and `sellCost` are part 2's display:
- `p²/(2c)` or the cap form on the purchase side;
- `s²/(2c)` or the floor form on the sale side.

Part 3 applies the same forms to the unreachable fund's reduced moments. Part 4 uses
`g(m, d) = max_{0 ≤ δ ≤ d} [mδ - (c/2)δ²]` (`gval`) and states the room for the netting trades as the
feasibility of the netted holdings built in the proof (`move`).
-/

namespace Standalone.M7EtfOnlyRestrictionCost

open Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M2TwoStageSeparation (Inputs)
open Standalone.M5MissingDirectionLeak (Jmap Schur)

noncomputable section

variable {m n K : ℕ} {S : Type} [Fintype S]

/-- `E^-`: funds may be sold, not bought. -/
def Em (D : Data m n K S) : Set (Inst m n → ℝ) := {w | w ∈ F D ∧ ∀ i, w (Sum.inl i) ≤ w0 D (Sum.inl i)}

/-- `E^0`: funds frozen at the incumbent. -/
def E0 (D : Data m n K S) : Set (Inst m n → ℝ) := {w | w ∈ F D ∧ active w = active (w0 D)}

/-- Part 1: `J^0 ≤ J^- ≤ J`, and
- `C^- = 0` iff no fund is bought at the joint optimum;
- `C^0 = 0` iff no fund is traded there, and (given AX-13) iff claim 104's multiplier criterion holds at
  the ETF-only optimum;
- `J^- - J^0 = 0` iff no fund is sold at the `E^-` optimum;
- `C^0 = C^- + (J^- - J^0)`. -/
def Structure : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K),
    Inputs D → (covariance D).PosDef → 0 < D.gamma →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ wm ∈ Em D, IsMaxOn (fun w => score D w θ) (Em D) wm →
    ∀ wf ∈ E0 D, IsMaxOn (fun w => score D w θ) (E0 D) wf →
      score D wf θ ≤ score D wm θ ∧ score D wm θ ≤ score D wJ θ ∧
      (score D wJ θ = score D wm θ ↔ ∀ i, wJ (Sum.inl i) ≤ w0 D (Sum.inl i)) ∧
      (score D wJ θ = score D wf θ ↔ active wJ = active (w0 D)) ∧
      (AX13 → (score D wJ θ = score D wf θ ↔ JointCriterion D θ wf)) ∧
      (score D wm θ = score D wf θ ↔ active wm = active (w0 D)) ∧
      score D wJ θ - score D wf θ = (score D wJ θ - score D wm θ) + (score D wm θ - score D wf θ)

/-- Part 2's purchase-side term. With curvature `c`, purchase excess `p = α - κ⁺ - c x⁻` and
`lo = (α - κ⁺)/c`, it is `p²/(2c)` if `p > 0` and `lo ≤ x̄`, the cap form `ψ(x̄) - ψ(x⁻)` if `p > 0` and
`lo > x̄`, and `0` otherwise. -/
def buyCost (alpha c kp km xm xbar : ℝ) : ℝ :=
  if 0 < alpha - kp - c * xm then
    (if (alpha - kp) / c ≤ xbar then (alpha - kp - c * xm) ^ 2 / (2 * c)
      else psi alpha c kp km xm xbar - psi alpha c kp km xm xm)
  else 0

/-- Part 2's sale-side term. With sale excess `s = c x⁻ - α - κ⁻` and `hi = (α + κ⁻)/c`, it is `s²/(2c)` if
`s > 0` and `hi ≥ 0`, the floor form `ψ(0) - ψ(x⁻)` if `s > 0` and `hi < 0`, and `0` otherwise. -/
def sellCost (alpha c kp km xm : ℝ) : ℝ :=
  if 0 < c * xm - alpha - km then
    (if 0 ≤ (alpha + km) / c then (c * xm - alpha - km) ^ 2 / (2 * c)
      else psi alpha c kp km xm 0 - psi alpha c kp km xm xm)
  else 0

/-- The one-fund forms:
- `ψ(a) - ψ(a⁻) = buyCost`, where `a` is the band holding on `[0, x̄]` and `a⁻` on `[0, x⁻]`;
- `ψ(a⁻) - ψ(x⁻) = sellCost`;
- `a⁻ = min(x⁻, hi^box)`. -/
def OneFund : Prop :=
  ∀ (alpha c kp km xm xbar : ℝ), 0 < c → 0 ≤ kp → 0 ≤ km → 0 ≤ xm → xm ≤ xbar →
    psi alpha c kp km xm (bandHold alpha c kp km xm xbar) - psi alpha c kp km xm (bandHold alpha c kp km xm xm) =
      buyCost alpha c kp km xm xbar ∧
    psi alpha c kp km xm (bandHold alpha c kp km xm xm) - psi alpha c kp km xm xm = sellCost alpha c kp km xm ∧
    bandHold alpha c kp km xm xm = min xm (max 0 (min xbar ((alpha + km) / c)))

/-- Part 2, spanning frictionless ETFs: at the three optima, each with a slack budget and every ETF
strictly inside its box,
- `C^- = Σ_i [ψ_i(a_i) - ψ_i(a⁻_i)] = Σ_i buyCost_i`;
- `J^- - J^0 = Σ_i [ψ_i(a⁻_i) - ψ_i(x⁻_i)] = Σ_i sellCost_i`;
- from zero incumbents with every `lo_i ≤ x̄_i`, `C^- = Σ_i [(α̂_i - κ⁺_i)⁺]²/(2γv_i)` and `J^- - J^0 = 0`. -/
def Spanning2 : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → FrictionlessSpanning D Sf v →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ wm ∈ Em D, IsMaxOn (fun w => score D w θ) (Em D) wm →
    ∀ wf ∈ E0 D, IsMaxOn (fun w => score D w θ) (E0 D) wf →
    (∀ w ∈ ({wJ, wm, wf} : Set (Inst m K → ℝ)), 0 < cash D w ∧
      ∀ j, 0 < w (Sum.inr j) ∧ w (Sum.inr j) < D.wbar (Sum.inr j)) →
    let ψ := fun i => psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i))
      (w0 D (Sum.inl i))
    let a := fun i => bandHold (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i))
      (w0 D (Sum.inl i)) (D.wbar (Sum.inl i))
    let am := fun i => bandHold (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i))
      (w0 D (Sum.inl i)) (w0 D (Sum.inl i))
    score D wJ θ - score D wm θ = ∑ i, (ψ i (a i) - ψ i (am i)) ∧
    score D wJ θ - score D wm θ = ∑ i, buyCost (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (D.wbar (Sum.inl i)) ∧
    score D wm θ - score D wf θ = ∑ i, (ψ i (am i) - ψ i (w0 D (Sum.inl i))) ∧
    score D wm θ - score D wf θ = ∑ i, sellCost (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) ∧
    ((∀ i, w0 D (Sum.inl i) = 0 ∧ (θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i) ≤ D.wbar (Sum.inl i)) →
      score D wJ θ - score D wm θ = ∑ i, (max (θ.alpha i - D.kplus (Sum.inl i)) 0) ^ 2 / (2 * (D.gamma * v i)) ∧
      score D wm θ - score D wf θ = 0)

/-- Part 3, one unreachable fund `i` (claim 104's 2c inputs): at the three optima, each with a slack
budget and every ETF strictly inside its box, the same forms hold. Fund `i` uses its reduced moments
`α^red_i = α̂_i + p` and `s^red_i = v_i + s_U`; every other fund uses `(α̂_k, v_k)`. -/
def Unreach3 : Prop :=
  ∀ (m n K : ℕ) (S : Type) [Fintype S] (D : Data m n K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ) (i : Fin m),
    Inputs D → OneUnreachable D Sf v i →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ wm ∈ Em D, IsMaxOn (fun w => score D w θ) (Em D) wm →
    ∀ wf ∈ E0 D, IsMaxOn (fun w => score D w θ) (E0 D) wf →
    (∀ w ∈ ({wJ, wm, wf} : Set (Inst m n → ℝ)), 0 < cash D w ∧
      ∀ j, 0 < w (Sum.inr j) ∧ w (Sum.inr j) < D.wbar (Sum.inr j)) →
    let al := fun k => if k = i then θ.alpha i + D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam) else θ.alpha k
    let vv := fun k => if k = i then v i + D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i) else v k
    score D wJ θ - score D wm θ = ∑ k, buyCost (al k) (D.gamma * vv k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (D.wbar (Sum.inl k)) ∧
    score D wm θ - score D wf θ = ∑ k, sellCost (al k) (D.gamma * vv k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k))

/-- `g(m, d) = max_{0 ≤ δ ≤ d} [mδ - (c/2)δ²]`: `0` if `m ≤ 0`, `m²/(2c)` if `0 < m ≤ c d`, and
`m d - (c/2)d²` if `m > c d`. -/
def gval (c mm d : ℝ) : ℝ :=
  if mm ≤ 0 then 0 else if mm ≤ c * d then mm ^ 2 / (2 * c) else mm * d - c / 2 * d ^ 2

/-- Its maximizer `clip(m/c, 0, d)`. -/
def garg (c mm d : ℝ) : ℝ := max 0 (min d (mm / c))

/-- Move fund `i` by `δ_i`, and the ETFs by the netting trade `-Σ_i δ_i r_i`. -/
def move {m K : ℕ} (D : Data m K K S) (x : Inst m K → ℝ) (δ : Fin m → ℝ) : Inst m K → ℝ :=
  Sum.elim (fun i => x (Sum.inl i) + δ i)
    (fun j => x (Sum.inr j) - ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j)

/-- The re-hedge costs `h⁺` and `h⁻` of claim 102, for the netting vector `r`. -/
def hP {m K : ℕ} (D : Data m K K S) (r : Fin K → ℝ) : ℝ :=
  ∑ j, (max (r j) 0 * D.kminus (Sum.inr j) + max (-r j) 0 * D.kplus (Sum.inr j))

def hM {m K : ℕ} (D : Data m K K S) (r : Fin K → ℝ) : ℝ :=
  ∑ j, (max (r j) 0 * D.kplus (Sum.inr j) + max (-r j) 0 * D.kminus (Sum.inr j))

/-- Part 4, ETF frictions with spanning ETFs, `Σ_E = 0` and `V = diag v`. With
`A⁰_i = α̂_i + r_i'c^E - γ v_i x⁻_i` and `c_i = γ v_i`:
- `Σ_i g(A⁰_i - κ⁺_i - h⁺_i, x̄_i - x⁻_i) ≤ C^- ≤ Σ_i g(A⁰_i - κ⁺_i + h⁻_i, x̄_i - x⁻_i)`;
- `Σ_i g(-A⁰_i - κ⁻_i - h⁻_i, x⁻_i) ≤ J^- - J^0 ≤ Σ_i g(-A⁰_i - κ⁻_i + h⁺_i, x⁻_i)`.

The room for the netting trades (and their cash) is the hypothesis that the four netted holdings
built from the optima are feasible. -/
def Frictions4 : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (v : Fin m → ℝ),
    Inputs D → RefCase D Sf (diagonal v) 0 → IsUnit D.BE.det → (∀ i, 0 < v i) → 0 < D.gamma →
    ∀ wJ ∈ F D, IsMaxOn (fun w => score D w θ) (F D) wJ →
    ∀ wm ∈ Em D, IsMaxOn (fun w => score D w θ) (Em D) wm →
    ∀ wf ∈ E0 D, IsMaxOn (fun w => score D w θ) (E0 D) wf →
    let r := fun i => (D.BE⁻¹)ᵀ *ᵥ D.BA i
    let c := fun i => D.gamma * v i
    let A0 := fun i => θ.alpha i + r i ⬝ᵥ D.cE - c i * w0 D (Sum.inl i)
    let room := fun i => D.wbar (Sum.inl i) - w0 D (Sum.inl i)
    let δL := fun i => garg (c i) (A0 i - D.kplus (Sum.inl i) - hP D (r i)) (room i)
    let δU := fun i => max (wJ (Sum.inl i) - w0 D (Sum.inl i)) 0
    let δS := fun i => garg (c i) (-A0 i - D.kminus (Sum.inl i) - hM D (r i)) (w0 D (Sum.inl i))
    let δV := fun i => w0 D (Sum.inl i) - wm (Sum.inl i)
    move D wm δL ∈ F D → move D wJ (fun i => -δU i) ∈ F D → move D wf (fun i => -δS i) ∈ F D →
    move D wm δV ∈ F D →
    ∑ i, gval (c i) (A0 i - D.kplus (Sum.inl i) - hP D (r i)) (room i) ≤ score D wJ θ - score D wm θ ∧
    score D wJ θ - score D wm θ ≤ ∑ i, gval (c i) (A0 i - D.kplus (Sum.inl i) + hM D (r i)) (room i) ∧
    ∑ i, gval (c i) (-A0 i - D.kminus (Sum.inl i) - hM D (r i)) (w0 D (Sum.inl i)) ≤
      score D wm θ - score D wf θ ∧
    score D wm θ - score D wf θ ≤ ∑ i, gval (c i) (-A0 i - D.kminus (Sum.inl i) + hP D (r i)) (w0 D (Sum.inl i))

/-- Claim 106, parts 1-4. -/
def statement : Prop := Structure ∧ OneFund ∧ Spanning2 ∧ Unreach3 ∧ Frictions4

end

end Standalone.M7EtfOnlyRestrictionCost

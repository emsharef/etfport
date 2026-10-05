import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.Rank
import Standalone.M7TwoStageExactnessLoss

/-!
# Claim 040: the fund decision when ETFs sit at their zero bound

Statement only; the proof is `Novel/M7FundDecisionEtfsAtZeroProof.lean`.

Parts 0 and 1 are stated on claim 027's M2 `Data`, with claim 104's reference case, `grad`, `InSlope` and
`BoxSign`. Part 1 is conditional on ledger entry AX-13 (polyhedral KKT), through the hypothesis `AX13`
of claim 104. Parts 2-5 are stated in the claim's own coordinates (`Coord`): the ETF-coordinate
exposure `w = x^E + Q x^A`, its premium `μ_E` and second moment `Σ_EE`, the funds' `α~`, `V`, `Q` and
their box and rates. Part 0 shows every spanning frictionless instance with `Σ_E = 0` is such a
`Coord` (`coord`), and that an optimum in coordinates that lies in `F` is the review's optimum.

The exposure problem `max {G_E(w) : w ≥ q}` has the maximizer `wopt q`, the multiplier
`zeta q = γ Σ_EE w(q) - μ_E` and the at-zero set `Zset q = {j : w_j(q) = q_j}`. For a set `Z` of ETFs,
`c` its complement, the Schur-block candidate is `wcand` (`w_Z = q_Z`,
`w_c = Σ_cc⁻¹(μ_c/γ - Σ_cZ q_Z)`) with multiplier `zcand = γ Σ_{ZZ.c} q_Z - μ_{Z.c}`. The fund problem
with the exposure optimized out is `Phi`; its smooth part `smooth` has gradient `Gm`, which on
`Z = Zset (Q x)` is `α^Z - γ V^Z x`.

Part 4 is stated for one fund on the whole real line. Part 2 defines `m(x) = G(x)` for every `x`, so `m`
needs no extension beyond `[0, x̄]`, and the incumbent's piece is `{x : Z(r x) = Z⁻}`. The claim's
unclipped roots are the roots of this `m`. The stated iffs hold for this extension as they do for the
extension by end pieces.
-/

namespace Standalone.M7FundDecisionEtfsAtZero

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses Standalone.M7TwoStageExactnessLoss

noncomputable section

/-! ### Claim 040's coordinates -/

/-- An instance in claim 040's coordinates: ETF-coordinate premium `μ_E` and second moment `Σ_EE`,
risk aversion `γ`, the funds' `α~` (net alpha plus fee credit), residual moment `V`, netting matrix
`Q` (column `i` is `r_i`), rates, caps and incumbents. -/
structure Coord (M N : ℕ) where
  mu : Fin M → ℝ
  Sig : Matrix (Fin M) (Fin M) ℝ
  gamma : ℝ
  alt : Fin N → ℝ
  V : Matrix (Fin N) (Fin N) ℝ
  Q : Matrix (Fin M) (Fin N) ℝ
  kp : Fin N → ℝ
  km : Fin N → ℝ
  xbar : Fin N → ℝ
  xm : Fin N → ℝ

variable {M N : ℕ}

/-- Parts 2-5's standing hypotheses: `γ > 0`, `Σ_EE` and `V` positive definite, rates nonnegative,
and `0 ≤ x⁻ ≤ x̄`. -/
def Hyp (P : Coord M N) : Prop :=
  0 < P.gamma ∧ P.Sig.PosDef ∧ P.V.PosDef ∧ (∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) ∧
    ∀ i, 0 ≤ P.xm i ∧ P.xm i ≤ P.xbar i

/-- `G_E(w) = μ_E'w - (γ/2) w'Σ_EE w`. -/
def GE (P : Coord M N) (w : Fin M → ℝ) : ℝ := P.mu ⬝ᵥ w - P.gamma / 2 * (w ⬝ᵥ (P.Sig *ᵥ w))

/-- The exposure constraint `w ≥ q`. -/
def Wset (q : Fin M → ℝ) : Set (Fin M → ℝ) := {w | ∀ j, q j ≤ w j}

/-- `V_E(q) = sup {G_E(w) : w ≥ q}`. -/
def VE (P : Coord M N) (q : Fin M → ℝ) : ℝ := sSup (GE P '' Wset q)

/-- `w(q)`, a maximizer of `G_E` on `w ≥ q` (unique by part 2). -/
def wopt (P : Coord M N) (q : Fin M → ℝ) : Fin M → ℝ :=
  Classical.epsilon fun w => w ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) w

/-- The multiplier `ζ(q) = γ Σ_EE w(q) - μ_E`. -/
def zeta (P : Coord M N) (q : Fin M → ℝ) : Fin M → ℝ := P.gamma • (P.Sig *ᵥ wopt P q) - P.mu

/-- The at-zero set `Z(q) = {j : w_j(q) = q_j}`. -/
def Zset (P : Coord M N) (q : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun j => wopt P q j = q j

/-! ### Blocks for a set `Z` of ETFs and its complement `c` -/

/-- Indices in `Z`. -/
abbrev In (Z : Finset (Fin M)) := {j : Fin M // j ∈ Z}

/-- Indices in the complement `c`. -/
abbrev Out (Z : Finset (Fin M)) := {j : Fin M // j ∉ Z}

/-- `Σ_cc`. -/
def Scc (P : Coord M N) (Z : Finset (Fin M)) : Matrix (Out Z) (Out Z) ℝ :=
  P.Sig.submatrix Subtype.val Subtype.val

/-- `Σ_cZ`. -/
def ScZ (P : Coord M N) (Z : Finset (Fin M)) : Matrix (Out Z) (In Z) ℝ :=
  P.Sig.submatrix Subtype.val Subtype.val

/-- `Σ_Zc`. -/
def SZc (P : Coord M N) (Z : Finset (Fin M)) : Matrix (In Z) (Out Z) ℝ :=
  P.Sig.submatrix Subtype.val Subtype.val

/-- `Σ_ZZ`. -/
def SZZ (P : Coord M N) (Z : Finset (Fin M)) : Matrix (In Z) (In Z) ℝ :=
  P.Sig.submatrix Subtype.val Subtype.val

/-- The Schur complement `Σ_{ZZ.c} = Σ_ZZ - Σ_Zc Σ_cc⁻¹ Σ_cZ`. -/
def schur (P : Coord M N) (Z : Finset (Fin M)) : Matrix (In Z) (In Z) ℝ :=
  SZZ P Z - SZc P Z * (Scc P Z)⁻¹ * ScZ P Z

/-- `μ_{Z.c} = μ_Z - Σ_Zc Σ_cc⁻¹ μ_c`. -/
def muZc (P : Coord M N) (Z : Finset (Fin M)) : In Z → ℝ :=
  (fun j : In Z => P.mu j) - SZc P Z *ᵥ ((Scc P Z)⁻¹ *ᵥ fun j : Out Z => P.mu j)

/-- Part 2's candidate: `w_Z = q_Z`, `w_c = Σ_cc⁻¹(μ_c/γ - Σ_cZ q_Z)`. -/
def wcand (P : Coord M N) (Z : Finset (Fin M)) (q : Fin M → ℝ) : Fin M → ℝ := fun j =>
  if h : j ∈ Z then q j
  else ((Scc P Z)⁻¹ *ᵥ ((fun k : Out Z => P.mu k / P.gamma) - ScZ P Z *ᵥ fun k : In Z => q k)) ⟨j, h⟩

/-- Part 2's candidate multiplier `ζ_Z = γ Σ_{ZZ.c} q_Z - μ_{Z.c}`. -/
def zcand (P : Coord M N) (Z : Finset (Fin M)) (q : Fin M → ℝ) : In Z → ℝ :=
  P.gamma • (schur P Z *ᵥ fun k : In Z => q k) - muZc P Z

/-- `Q_Z`, the rows of `Q` in `Z`. -/
def QZ (P : Coord M N) (Z : Finset (Fin M)) : Matrix (In Z) (Fin N) ℝ :=
  P.Q.submatrix Subtype.val id

/-- `α^Z = α~ + Q_Z' μ_{Z.c}`. -/
def alphaZ (P : Coord M N) (Z : Finset (Fin M)) : Fin N → ℝ := P.alt + (QZ P Z)ᵀ *ᵥ muZc P Z

/-- `V^Z = V + Q_Z' Σ_{ZZ.c} Q_Z`. -/
def VZ (P : Coord M N) (Z : Finset (Fin M)) : Matrix (Fin N) (Fin N) ℝ :=
  P.V + (QZ P Z)ᵀ * schur P Z * QZ P Z

/-- The marginal on a fixed set `Z`: `α^Z - γ V^Z x`. -/
def Gcand (P : Coord M N) (Z : Finset (Fin M)) (x : Fin N → ℝ) : Fin N → ℝ :=
  alphaZ P Z - P.gamma • (VZ P Z *ᵥ x)

/-! ### The fund problem -/

/-- The funds' cost `C_A(x - x⁻)`. -/
def cost (P : Coord M N) (x : Fin N → ℝ) : ℝ :=
  ∑ i, (P.kp i * max (x i - P.xm i) 0 + P.km i * max (P.xm i - x i) 0)

/-- The fund box `0 ≤ x ≤ x̄`. -/
def Box (P : Coord M N) : Set (Fin N → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ P.xbar i}

/-- The smooth part of `Φ`: `α~'x - (γ/2) x'Vx + V_E(Q x)`. -/
def smooth (P : Coord M N) (x : Fin N → ℝ) : ℝ :=
  P.alt ⬝ᵥ x - P.gamma / 2 * (x ⬝ᵥ (P.V *ᵥ x)) + VE P (P.Q *ᵥ x)

/-- `Φ(x) = smooth(x) - C_A(x - x⁻)`, the fund problem with the exposure optimized out. -/
def Phi (P : Coord M N) (x : Fin N → ℝ) : ℝ := smooth P x - cost P x

/-- The fund marginal `G(x) = α~ - γ V x - Q' ζ(Q x)`. -/
def Gm (P : Coord M N) (x : Fin N → ℝ) : Fin N → ℝ :=
  P.alt - P.gamma • (P.V *ᵥ x) - P.Qᵀ *ᵥ zeta P (P.Q *ᵥ x)

/-- The review's objective in coordinates: `G_E(w) + α~'a - (γ/2) a'Va - C_A(a - x⁻)`. -/
def J (P : Coord M N) (p : (Fin N → ℝ) × (Fin M → ℝ)) : ℝ :=
  GE P p.2 + P.alt ⬝ᵥ p.1 - P.gamma / 2 * (p.1 ⬝ᵥ (P.V *ᵥ p.1)) - cost P p.1

/-- The review's feasible set in coordinates: funds in their box and `w ≥ Q a` (ETFs long). -/
def Jset (P : Coord M N) : Set ((Fin N → ℝ) × (Fin M → ℝ)) :=
  {p | p.1 ∈ Box P ∧ p.2 ∈ Wset (P.Q *ᵥ p.1)}

/-- The linear functional `d ↦ g'd`. -/
def dotCLM {k : ℕ} (g : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ := ∑ j, g j • ContinuousLinearMap.proj j

/-! ### Part 0: coordinates -/

/-- The netting vector `r_i = R'(B^A_i)'`, `R = (B^E)⁻¹`. -/
def rvec {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (i : Fin m) : Fin K → ℝ :=
  (D.BE⁻¹)ᵀ *ᵥ D.BA i

/-- Claim 040's coordinates of a spanning instance with reference moments `Σ~_f` and `V`:
`μ_E = B^E λ - c^E`, `Σ_EE = B^E Σ~_f (B^E)'`, `α~ = α + Q'c^E`, `Q_{ji} = r_ij`. -/
def coord {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) : Coord K m where
  mu := D.BE *ᵥ θ.lam - D.cE
  Sig := D.BE * Sf * D.BEᵀ
  gamma := D.gamma
  alt := θ.alpha + fun i => rvec D i ⬝ᵥ D.cE
  V := V
  Q := Matrix.of fun j i => rvec D i j
  kp := fun i => D.kplus (Sum.inl i)
  km := fun i => D.kminus (Sum.inl i)
  xbar := fun i => D.wbar (Sum.inl i)
  xm := fun i => w0 D (Sum.inl i)

/-- The coordinates `(a, w)` of a holding: `a = x^A`, `w = x^E + Q x^A`. -/
def toCoord {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (x : Inst m K → ℝ) :
    (Fin m → ℝ) × (Fin K → ℝ) :=
  (active x, etf x + (coord D θ Sf V).Q *ᵥ active x)

/-- Part 0: with spanning ETFs (`B^E` invertible), `Σ_E = 0`, frictionless ETFs (fees allowed) and the
reference case with a general `V`, the score is the coordinate objective `J`; `x^E ≥ 0` iff
`w ≥ Q x^A`; `Σ_EE` is positive definite when `Σ~_f` is; and a holding in `F` whose coordinates maximize
`J` on the coordinate feasible set is the review's optimum (the ex post check that ETF caps and the
budget are slack). -/
def Coords : Prop :=
  ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ),
    RefCase D Sf V 0 → IsUnit D.BE.det → (∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) →
    let P := coord D θ Sf V
    (∀ x, score D x θ = J P (toCoord D θ Sf V x)) ∧
    (∀ x, (∀ j, 0 ≤ x (Sum.inr j)) ↔ (toCoord D θ Sf V x).2 ∈ Wset (P.Q *ᵥ active x)) ∧
    (Sf.PosDef → P.Sig.PosDef) ∧
    ∀ x ∈ F D, IsMaxOn (J P) (Jset P) (toCoord D θ Sf V x) → IsMaxOn (fun w => score D w θ) (F D) x

/-! ### Part 1: one-sided ETF marginals (any frictions, AX-13) -/

/-- Claim 102 part 4's reduced marginal `A_i = α_i + r_i'(c^E + γ Σ_E x^E) - γ (V x^A)_i`. -/
def Ared {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (θ : Params m K)
    (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ) (x : Inst m K → ℝ) (i : Fin m) : ℝ :=
  θ.alpha i + rvec D i ⬝ᵥ (D.cE + D.gamma • (SE *ᵥ etf x)) - D.gamma * (V *ᵥ active x) i

/-- The slope convention for an ETF at zero: `κ⁺_{E,j}` if it was not held, `-κ⁻_{E,j}` if it was
sold out. -/
def tconv {m K : ℕ} {S : Type} [Fintype S] (D : Data m K K S) (j : Fin K) : ℝ :=
  if w0 D (Sum.inr j) = 0 then D.kplus (Sum.inr j) else -D.kminus (Sum.inr j)

/-- Part 1 (given AX-13): at the optimum, with spanning ETFs (`B^E` invertible) and every ETF below its
cap, some `η ≥ 0` with `η k(x) = 0` and slopes `t` in the trade-sign sets, with `t_j` the convention
at every ETF at zero, give each ETF `g_j = η + (1 + η) t_j - ζ_j` with slack `ζ_j ≥ 0`, zero off zero.
For an ETF at zero that was not held, `ζ_j` is the largest slack over the slope set `[-κ⁻, κ⁺]`.
Fund `i`'s marginal is `A_i + r_i'(η 1 + (1 + η) t_E) - Σ_j r_ij ζ_j`, the sum over the ETFs at zero,
and `g_i - η - (1 + η) t_i` has the box signs. That is "bought iff the display = η + (1 + η) κ⁺_i",
and likewise for sold and held, in the normal-cone form of claims 102 and 104. -/
def OneSided : Prop :=
  AX13 → ∀ (m K : ℕ) (S : Type) [Fintype S] (D : Data m K K S) (θ : Params m K)
    (Sf : Matrix (Fin K) (Fin K) ℝ) (V : Matrix (Fin m) (Fin m) ℝ) (SE : Matrix (Fin K) (Fin K) ℝ),
    Standalone.M2TwoStageSeparation.Inputs D → RefCase D Sf V SE → IsUnit D.BE.det →
    ∀ x ∈ F D, IsMaxOn (fun w => score D w θ) (F D) x → (∀ j, x (Sum.inr j) < D.wbar (Sum.inr j)) →
    ∃ (η : ℝ) (t : Inst m K → ℝ) (ζ : Fin K → ℝ), 0 ≤ η ∧ η * cash D x = 0 ∧
      (∀ l, InSlope D x l (t l)) ∧ (∀ j, x (Sum.inr j) = 0 → t (Sum.inr j) = tconv D j) ∧
      (∀ j, 0 ≤ ζ j ∧ (0 < x (Sum.inr j) → ζ j = 0) ∧
        grad D θ x (Sum.inr j) = η + (1 + η) * t (Sum.inr j) - ζ j) ∧
      (∀ j, x (Sum.inr j) = 0 → w0 D (Sum.inr j) = 0 →
        ∀ t' ∈ Set.Icc (-D.kminus (Sum.inr j)) (D.kplus (Sum.inr j)),
          η + (1 + η) * t' - grad D θ x (Sum.inr j) ≤ ζ j) ∧
      (∀ i, grad D θ x (Sum.inl i) = Ared D θ V SE x i +
        rvec D i ⬝ᵥ (fun j => η + (1 + η) * t (Sum.inr j)) - ∑ j, rvec D i j * ζ j) ∧
      ∀ i, BoxSign (D.wbar (Sum.inl i)) (x (Sum.inl i)) (grad D θ x (Sum.inl i) - η - (1 + η) * t (Sum.inl i))

/-! ### Part 2: which ETFs are at zero -/

/-- Part 2: for `γ > 0` and `Σ_EE` positive definite, and every by-product vector `q`:
- `max {G_E(w) : w ≥ q}` has a unique solution, `wopt q`, and `V_E(q) = G_E(w(q))`;
- `(w, ζ)` is feasible, with `ζ ≥ 0` complementary to `w - q` and `γ Σ_EE w - μ_E = ζ`, iff it is
  `(w(q), ζ(q))`, so the multiplier is unique;
- the Schur-block candidate for `Z` has `ζ_Z ≥ 0` and `w_c ≥ q_c` iff it is `w(q)` with multiplier
  `ζ_Z` on `Z` and `0` on `c` (every set satisfying both gives the same `w` and `ζ`);
- the at-zero set `Z(q)` satisfies both. -/
def AtZero : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), 0 < P.gamma → P.Sig.PosDef → ∀ q : Fin M → ℝ,
    (∃! w, w ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) w) ∧
    (wopt P q ∈ Wset q ∧ IsMaxOn (GE P) (Wset q) (wopt P q)) ∧ VE P q = GE P (wopt P q) ∧
    (∀ w ζ : Fin M → ℝ,
      (w ∈ Wset q ∧ (∀ j, 0 ≤ ζ j ∧ ζ j * (w j - q j) = 0) ∧ P.gamma • (P.Sig *ᵥ w) - P.mu = ζ) ↔
        (w = wopt P q ∧ ζ = zeta P q)) ∧
    (∀ Z : Finset (Fin M),
      ((∀ j, 0 ≤ zcand P Z q j) ∧ ∀ j, j ∉ Z → q j ≤ wcand P Z q j) ↔
        (wcand P Z q = wopt P q ∧ (∀ j : In Z, zeta P q j = zcand P Z q j) ∧
          ∀ j, j ∉ Z → zeta P q j = 0)) ∧
    ((∀ j, 0 ≤ zcand P (Zset P q) q j) ∧ ∀ j, j ∉ Zset P q → q j ≤ wcand P (Zset P q) q j)

/-- Part 2: `V_E` is concave and differentiable with gradient `-ζ(q)`. -/
def ValueFn : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), 0 < P.gamma → P.Sig.PosDef →
    ConcaveOn ℝ Set.univ (VE P) ∧ ∀ q, HasFDerivAt (VE P) (dotCLM (-zeta P q)) q

/-! ### Part 3: the fund marginal and the criterion -/

/-- Part 3: the smooth part of `Φ` has gradient `G(x) = α~ - γ V x - Q'ζ(Q x)`, which equals
`α^Z - γ V^Z x` on `Z = Z(Q x)`. The exposure optimizes out: a feasible point is the review's optimum
iff its funds maximize `Φ` on the box and `w = w(Q x^A)`, and `Φ` has exactly one maximizer on the box. -/
def FundMarginal : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P →
    (∀ x, HasFDerivAt (smooth P) (dotCLM (Gm P x)) x) ∧
    (∀ x, Gm P x = Gcand P (Zset P (P.Q *ᵥ x)) x) ∧
    (∀ p ∈ Jset P, IsMaxOn (J P) (Jset P) p ↔ IsMaxOn (Phi P) (Box P) p.1 ∧ p.2 = wopt P (P.Q *ᵥ p.1)) ∧
    ∃! x, x ∈ Box P ∧ IsMaxOn (Phi P) (Box P) x

/-- Part 3(a), the hold test, exact for every `N`: the incumbent with the ETFs at
`w(Q x⁻) - Q x⁻` is the review's optimum iff every fund has `-κ⁻_i ≤ G_i(x⁻) ≤ κ⁺_i`, the lower bound
dropped at `x⁻_i = 0` and the upper at `x⁻_i = x̄_i`. -/
def HoldTest : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P →
    (IsMaxOn (J P) (Jset P) (P.xm, wopt P (P.Q *ᵥ P.xm)) ↔
      ∀ i, (P.xm i < P.xbar i → Gm P P.xm i ≤ P.kp i) ∧ (0 < P.xm i → -P.km i ≤ Gm P P.xm i))

/-- Part 3(b), at the optimum `x`: a bought fund has `G_i(x) = κ⁺_i` (`≥` at the cap), a sold fund has
`G_i(x) = -κ⁻_i` (`≤` at zero), and a held fund has `G_i(x)` in the band (one-sided at its bounds);
`G = α^Z - γ V^Z x` on `Z = Z(Q x)` (`FundMarginal`). -/
def AtOptimum : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P → ∀ x ∈ Box P, IsMaxOn (Phi P) (Box P) x → ∀ i,
    (P.xm i < x i → x i < P.xbar i → Gm P x i = P.kp i) ∧
    (P.xm i < x i → x i = P.xbar i → P.kp i ≤ Gm P x i) ∧
    (x i < P.xm i → 0 < x i → Gm P x i = -P.km i) ∧
    (x i < P.xm i → x i = 0 → Gm P x i ≤ -P.km i) ∧
    (x i = P.xm i → (x i < P.xbar i → Gm P x i ≤ P.kp i) ∧ (0 < x i → -P.km i ≤ Gm P x i))

/-- Part 3(c), one fund: the optimum buys iff `G(x⁻) > κ⁺` and `x⁻ < x̄`, sells iff `G(x⁻) < -κ⁻` and
`x⁻ > 0`, and holds otherwise; `G(x⁻) = α^Z - γ s^Z x⁻` with `Z = Z(r x⁻)`, `s^Z = V^Z_{00}`. The box
conditions are the incumbent's edge cases (lean's note to math and red). -/
def OneFund : Prop :=
  ∀ (M : ℕ) (P : Coord M 1), Hyp P → ∀ x ∈ Box P, IsMaxOn (Phi P) (Box P) x →
    (P.xm 0 < x 0 ↔ P.kp 0 < Gm P P.xm 0 ∧ P.xm 0 < P.xbar 0) ∧
    (x 0 < P.xm 0 ↔ Gm P P.xm 0 < -P.km 0 ∧ 0 < P.xm 0) ∧
    Gm P P.xm 0 = alphaZ P (Zset P (P.Q *ᵥ P.xm)) 0 -
      P.gamma * VZ P (Zset P (P.Q *ᵥ P.xm)) 0 0 * P.xm 0

/-- `B_{Z.c} = B_Z - Σ_Zc Σ_cc⁻¹ B_c`: the at-zero rows of `B`, hedged by the free ETFs. -/
def BZc {K : ℕ} (P : Coord M N) (Z : Finset (Fin M)) (B : Matrix (Fin M) (Fin K) ℝ) :
    Matrix (In Z) (Fin K) ℝ :=
  B.submatrix Subtype.val id - SZc P Z * (Scc P Z)⁻¹ * B.submatrix Subtype.val id

/-- Part 3(d): a premium error `e` moves `μ_E` by `B^E e`. At a fixed at-zero set `Z` it shifts every
fund's marginal by `Q_Z' B^E_{Z.c} e`. With `B^E` invertible, the shift of fund `i` is zero for every
`e` iff `r_iZ = 0`, which includes the case of `Z` empty. For funds in a trading set `T` that are
interior with `Z` fixed, and the other funds unmoved, the response is `(γ V^Z_TT)⁻¹` times the shift;
for one fund it is the shift over `γ s^Z`. -/
def PremiumShift : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P → ∀ (B : Matrix (Fin M) (Fin M) ℝ) (e : Fin M → ℝ)
    (Z : Finset (Fin M)),
    let P' : Coord M N := { P with mu := P.mu + B *ᵥ e }
    let dG := (QZ P Z)ᵀ *ᵥ (BZc P Z B *ᵥ e)
    (∀ x, Gcand P' Z x - Gcand P Z x = dG) ∧
    (IsUnit B.det → ∀ i, (∀ e' : Fin M → ℝ, ((QZ P Z)ᵀ *ᵥ (BZc P Z B *ᵥ e')) i = 0) ↔ ∀ j ∈ Z, P.Q j i = 0) ∧
    ∀ (T : Finset (Fin N)) (x x' k : Fin N → ℝ), (∀ i, i ∉ T → x' i = x i) →
      (∀ i ∈ T, Gcand P Z x i = k i) → (∀ i ∈ T, Gcand P' Z x' i = k i) →
      (fun i : {i // i ∈ T} => x' i - x i) =
        (P.gamma • (VZ P Z).submatrix (Subtype.val : {i // i ∈ T} → Fin N) Subtype.val)⁻¹ *ᵥ
          fun i : {i // i ∈ T} => dG i

/-! ### Part 4: along one fund's trade -/

/-- One fund's marginal `m(x) = G(x)` on the whole line. -/
def mOne {M : ℕ} (P : Coord M 1) (x : ℝ) : ℝ := Gm P (fun _ => x) 0

/-- The at-zero set along one fund's trade, `Z(r x)`. -/
def Zpath {M : ℕ} (P : Coord M 1) (x : ℝ) : Finset (Fin M) := Zset P (P.Q *ᵥ fun _ => x)

/-- `s^Z = V^Z_{00} = v + r_Z' Σ_{ZZ.c} r_Z`. -/
def sZ {M : ℕ} (P : Coord M 1) (Z : Finset (Fin M)) : ℝ := VZ P Z 0 0

/-- `Φ` as a function of the one fund's holding. -/
def phiOne {M : ℕ} (P : Coord M 1) (x : ℝ) : ℝ := Phi P fun _ => x

/-- Part 4 (one fund):
- `m` is Lipschitz and strictly decreasing;
- each piece `{x : Z(r x) = Z}` is an interval. On it `m(x) = α^Z - γ s^Z x`, and it is cut out by the
  affine conditions `ζ_Z ≥ 0` and `w_c - r_c x > 0` on the candidate;
- `s^Z` is monotone in `Z` (`Curvature` for any number of funds);
- the optimum is the incumbent, or the clipped root of `m = κ⁺` (purchase) or `m = -κ⁻` (sale);
- the drop-`Z⁻` rule `x~ = bandHold(α^{Z⁻}, γ s^{Z⁻}, …)`: its unclipped root lies in the incumbent's
  piece iff the true one does, and then the two are equal. The claim's converse ("equal only if in
  the piece") fails when `m` meets the drop-`Z⁻` line again outside the piece (lean's note to math and
  red, with an instance). The holdings agree iff the roots agree or both clip to the same bound;
- if the at-zero set contains `Z⁻` on the way to the drop-`Z⁻` root, the true trade is no longer
  than the drop-`Z⁻` trade; if it is contained in `Z⁻`, it is no shorter;
- if the path leaves the incumbent's piece before the drop-`Z⁻` root, and every at-zero set off the
  piece has `s^Z > s^{Z⁻}` (or every one has `s^Z < s^{Z⁻}`), the roots differ. The Statement's
  "outside the piece the roots differ" needs the path to leave the piece before the root. At the
  piece's open end, where a free ETF reaches zero, `m = m~` by continuity, and the roots can
  coincide (lean's note to math and red). -/
def Path : Prop :=
  ∀ (M : ℕ) (P : Coord M 1), Hyp P →
    let r : Fin M → ℝ := fun j => P.Q j 0
    (∃ L, ∀ x y, |mOne P x - mOne P y| ≤ L * |x - y|) ∧ StrictAnti (mOne P) ∧
    (∀ Z : Finset (Fin M),
      Set.OrdConnected {x | Zpath P x = Z} ∧
      (∀ x, Zpath P x = Z → mOne P x = alphaZ P Z 0 - P.gamma * sZ P Z * x) ∧
      {x | Zpath P x = Z} =
        {x | (∀ j, 0 ≤ zcand P Z (x • r) j) ∧ ∀ j, j ∉ Z → x * r j < wcand P Z (x • r) j} ∧
      (∀ x : ℝ, zcand P Z (x • r) = x • (P.gamma • (schur P Z *ᵥ fun j : In Z => r j)) - muZc P Z) ∧
      ∀ (x : ℝ) j (h : j ∉ Z), wcand P Z (x • r) j = wcand P Z 0 j - x * ((Scc P Z)⁻¹ *ᵥ (ScZ P Z *ᵥ
        fun k : In Z => r k)) ⟨j, h⟩) ∧
    (∀ Z Z' : Finset (Fin M), Z ⊆ Z' → sZ P Z ≤ sZ P Z') ∧
    ∀ xs ∈ Set.Icc 0 (P.xbar 0), IsMaxOn (phiOne P) (Set.Icc 0 (P.xbar 0)) xs →
      let xm := P.xm 0
      let Z0 := Zpath P xm
      let c := P.gamma * sZ P Z0
      let a := alphaZ P Z0 0
      let xt := bandHold a c (P.kp 0) (P.km 0) xm (P.xbar 0)
      (-P.km 0 ≤ mOne P xm → mOne P xm ≤ P.kp 0 → xs = xm ∧ xt = xm) ∧
      (P.kp 0 < mOne P xm → ∀ u, mOne P u = P.kp 0 →
        let ut := (a - P.kp 0) / c
        xm < u ∧ xs = min (P.xbar 0) u ∧ xt = min (P.xbar 0) ut ∧
        (Zpath P ut = Z0 ↔ Zpath P u = Z0) ∧ (Zpath P ut = Z0 → u = ut) ∧
        (xs = xt ↔ u = ut ∨ (P.xbar 0 ≤ u ∧ P.xbar 0 ≤ ut)) ∧
        ((∀ y ∈ Set.Icc xm ut, Z0 ⊆ Zpath P y) → u ≤ ut ∧ xs ≤ xt) ∧
        ((∀ y ∈ Set.Icc xm ut, Zpath P y ⊆ Z0) → ut ≤ u ∧ xt ≤ xs) ∧
        ((∃ y ∈ Set.Ico xm ut, Zpath P y ≠ Z0) →
          ((∀ y ∈ Set.Icc xm ut, Zpath P y ≠ Z0 → sZ P Z0 < sZ P (Zpath P y)) → u < ut) ∧
          ((∀ y ∈ Set.Icc xm ut, Zpath P y ≠ Z0 → sZ P (Zpath P y) < sZ P Z0) → ut < u))) ∧
      (mOne P xm < -P.km 0 → ∀ u, mOne P u = -P.km 0 →
        let ut := (a + P.km 0) / c
        u < xm ∧ xs = max 0 u ∧ xt = max 0 ut ∧
        (Zpath P ut = Z0 ↔ Zpath P u = Z0) ∧ (Zpath P ut = Z0 → u = ut) ∧
        (xs = xt ↔ u = ut ∨ (u ≤ 0 ∧ ut ≤ 0)) ∧
        ((∀ y ∈ Set.Icc ut xm, Z0 ⊆ Zpath P y) → ut ≤ u ∧ xt ≤ xs) ∧
        ((∀ y ∈ Set.Icc ut xm, Zpath P y ⊆ Z0) → u ≤ ut ∧ xs ≤ xt) ∧
        ((∃ y ∈ Set.Ioc ut xm, Zpath P y ≠ Z0) →
          ((∀ y ∈ Set.Icc ut xm, Zpath P y ≠ Z0 → sZ P Z0 < sZ P (Zpath P y)) → ut < u) ∧
          ((∀ y ∈ Set.Icc ut xm, Zpath P y ≠ Z0 → sZ P (Zpath P y) < sZ P Z0) → u < ut)))

/-- Part 4's curvature monotonicity for any number of funds: adding ETFs to `Z` can only raise the
quadratic form of `V^Z` (the by-product loses a hedge). -/
def Curvature : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P → ∀ Z Z' : Finset (Fin M), Z ⊆ Z' → ∀ x,
    x ⬝ᵥ (VZ P Z *ᵥ x) ≤ x ⬝ᵥ (VZ P Z' *ᵥ x)

/-- Part 4: the roots exist: `m = k` has exactly one solution for every `k`. -/
def Roots : Prop :=
  ∀ (M : ℕ) (P : Coord M 1), Hyp P → ∀ k, ∃! u, mOne P u = k

/-! ### Part 5: readings -/

/-- Part 5(a), one ETF: with `q = Σ_i r_i x_i`, the ETF is at zero iff `μ_E ≤ γ σ_EE q`. Then every
fund's marginal is `α~_i + r_i μ_E - γ[(V x)_i + r_i σ_EE q]`; otherwise it is `α~_i - γ (V x)_i`. -/
def OneEtf : Prop :=
  ∀ (N : ℕ) (P : Coord 1 N), Hyp P → ∀ x : Fin N → ℝ,
    let q := (P.Q *ᵥ x) 0
    ((0 : Fin 1) ∈ Zset P (P.Q *ᵥ x) ↔ P.mu 0 ≤ P.gamma * P.Sig 0 0 * q) ∧
    ((0 : Fin 1) ∈ Zset P (P.Q *ᵥ x) → ∀ i,
      Gm P x i = P.alt i + P.Q 0 i * P.mu 0 - P.gamma * ((P.V *ᵥ x) i + P.Q 0 i * P.Sig 0 0 * q)) ∧
    ((0 : Fin 1) ∉ Zset P (P.Q *ᵥ x) → ∀ i, Gm P x i = P.alt i - P.gamma * (P.V *ᵥ x) i)

/-- Part 5(d), the fold-in: at the optimum, with `ζ = ζ(Q x)`, the ETFs are at
`w = (γ Σ_EE)⁻¹(μ_E + ζ)`, and `(x, w)` maximizes the review with the ETFs free (`w` unconstrained) at
the premiums `(α~ - Q'ζ, μ_E + ζ)`, where `Q'ζ = Q_Z'ζ_Z`. On the fund block the adjustment
`V^Z - V = Q_Z' Σ_{ZZ.c} Q_Z` is positive semidefinite of rank at most `|Z|`. -/
def FoldIn : Prop :=
  ∀ (M N : ℕ) (P : Coord M N), Hyp P →
    (∀ x ∈ Box P, IsMaxOn (Phi P) (Box P) x →
      let ζ := zeta P (P.Q *ᵥ x)
      let Pf : Coord M N := { P with mu := P.mu + ζ, alt := P.alt - P.Qᵀ *ᵥ ζ }
      wopt P (P.Q *ᵥ x) = (P.gamma • P.Sig)⁻¹ *ᵥ (P.mu + ζ) ∧
      (∀ j, j ∉ Zset P (P.Q *ᵥ x) → ζ j = 0) ∧
      IsMaxOn (J Pf) (Box P ×ˢ Set.univ) (x, wopt P (P.Q *ᵥ x))) ∧
    ∀ Z : Finset (Fin M), (VZ P Z - P.V).PosSemidef ∧ (VZ P Z - P.V).rank ≤ Z.card

/-- Claim 040 (parts 0-5, with the paper-level readings named in the claim's Lean note). -/
def statement : Prop :=
  Coords ∧ OneSided ∧ AtZero ∧ ValueFn ∧ FundMarginal ∧ HoldTest ∧ AtOptimum ∧ OneFund ∧
    PremiumShift ∧ Roots ∧ Curvature ∧ Path ∧ OneEtf ∧ FoldIn

end

end Standalone.M7FundDecisionEtfsAtZero

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Order.Basic

/-!
# Claim 030: M5's partial-adjustment policy and the exposure/alpha split

Statement only; the proof is `Novel/M5PartialAdjustmentSplitProof.lean`. Positions are indexed by a
finite type `ι` and the belief mean by `π`. Part 4 uses the blocks `(x^A, x^E)` and `w = (y, x^A)`.

- **Part 1** (`FilterFacts`, `Decouple`): the Kalman covariance recursion `kal`, its information
  form and monotonicity, the innovation covariance, `Σ_t ≻ 0` nonincreasing, and the reference-case
  decoupling.
- **Parts 2-3** (`BellmanVerif`, `Matrices`, `Aim`). The problem of part 2 is the structure `LQ`:
  - the trading-cost matrix `Λ ⪰ 0`, risk matrices `S t = γΣ_t ≻ 0`, discount `ρ ≥ 0`, and
    `μ_t = G_t m_t - e`. The mean map `G_t` is deterministic and may vary with `t`: claim 030's `G`
    is constant, and claim 031's reduced fund problem has a time-varying one (its part 3: claim
    030's part 3 extends verbatim);
  - the backward recursion for `A_t`, `C_t`, `c_t` and the affine policy.
- **Part 4** (`Coords`, `Transform`, `RefBlocks`, `Separation`), for `M = K` and invertible `B^E`.
- **Part 5** (`Speeds`): the scalar fund block and its stationary limit.

**Paper-level steps (PM, rule 6b).** Two steps are not formalized, and they discharge these
hypotheses of the formal statement:
- M5's Gaussian conditional moments. Under the manager's belief these give `E_t m_{t+1} = m_t`,
  and they make the conditional expectation linear and constant-preserving on the value
  functions. That is the hypothesis `Martingale E` of `BellmanVerif`, with `E` an abstract linear
  operator. They also give the predictive moments that make part 2's objective the `LQ` stage
  reward (`E_t[x'r] = x'μ_t`, `Var_t(x'r) = x'Σ_t x`).
- The dynamic-programming verification. It passes from `BellmanVerif`, where the stated policy
  uniquely maximizes the Bellman objective at every review and state, to optimality among all
  admissible measurable policies.
-/

namespace Standalone.M5PartialAdjustmentSplit

open Matrix

noncomputable section

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π]

/-- Part 3's data: horizon, trading cost, risk matrices `γΣ_t`, discount, and `μ_t = G_t m_t - e`. -/
structure LQ (ι π : Type) where
  T : ℕ
  Lam : Matrix ι ι ℝ
  S : ℕ → Matrix ι ι ℝ
  rho : ℝ
  G : ℕ → Matrix ι π ℝ
  e : ι → ℝ

/-- `Λ ⪰ 0`, `γΣ_t ≻ 0` and `ρ ≥ 0`. -/
def LQ.Setting (Q : LQ ι π) : Prop := Q.Lam.PosSemidef ∧ (∀ t, (Q.S t).PosDef) ∧ 0 ≤ Q.rho

namespace LQ

variable (Q : LQ ι π)

/-- The recursion with `k` reviews left: `(A, C, c)` at review `T - k`. -/
def ricK : ℕ → Matrix ι ι ℝ × Matrix ι π ℝ × (ι → ℝ)
  | 0 => (0, 0, 0)
  | k + 1 =>
    let t := Q.T - (k + 1)
    let D := Q.Lam + Q.S t + Q.rho • (ricK k).1
    (Q.Lam - Q.Lam * D⁻¹ * Q.Lam, Q.Lam * D⁻¹ * (Q.G t + Q.rho • (ricK k).2.1),
      (Q.Lam * D⁻¹) *ᵥ (Q.rho • (ricK k).2.2 - Q.e))

/-- `A_t`. -/
def A (t : ℕ) : Matrix ι ι ℝ := (Q.ricK (Q.T - t)).1
/-- `C_t`. -/
def C (t : ℕ) : Matrix ι π ℝ := (Q.ricK (Q.T - t)).2.1
/-- `c_t`. -/
def c (t : ℕ) : ι → ℝ := (Q.ricK (Q.T - t)).2.2
/-- `D_t = Λ + γΣ_t + ρ A_{t+1}`. -/
def D (t : ℕ) : Matrix ι ι ℝ := Q.Lam + Q.S t + Q.rho • Q.A (t + 1)
/-- `K_t = D_t⁻¹ Λ`. -/
def K (t : ℕ) : Matrix ι ι ℝ := (Q.D t)⁻¹ * Q.Lam
/-- `L_t = D_t⁻¹ (G + ρ C_{t+1})`. -/
def L (t : ℕ) : Matrix ι π ℝ := (Q.D t)⁻¹ * (Q.G t + Q.rho • Q.C (t + 1))
/-- `l_t = D_t⁻¹ (ρ c_{t+1} - e)`. -/
def l (t : ℕ) : ι → ℝ := (Q.D t)⁻¹ *ᵥ (Q.rho • Q.c (t + 1) - Q.e)
/-- The policy `x_t = K_t x_{t-1} + L_t m_t + l_t`. -/
def policy (t : ℕ) (xm : ι → ℝ) (m : π → ℝ) : ι → ℝ :=
  Q.K t *ᵥ xm + Q.L t *ᵥ m + Q.l t
/-- The adjustment rate `Γ_t = I - D_t⁻¹ Λ`. -/
def Gam (t : ℕ) : Matrix ι ι ℝ := 1 - (Q.D t)⁻¹ * Q.Lam
/-- `Markowitz_t = (γΣ_t)⁻¹ μ_t`. -/
def mkw (t : ℕ) (m : π → ℝ) : ι → ℝ := (Q.S t)⁻¹ *ᵥ (Q.G t *ᵥ m - Q.e)

/-- The aim with `k` reviews left, at the belief mean `m` (its conditional expectation given
`m_t = m`, by the martingale property). -/
def aimK : ℕ → (π → ℝ) → ι → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun m =>
    let t := Q.T - (k + 1)
    (Q.S t + Q.rho • Q.A (t + 1))⁻¹ *ᵥ (Q.S t *ᵥ Q.mkw t m + Q.rho • (Q.A (t + 1) *ᵥ aimK k m))

/-- `aim_t`. -/
def aim (t : ℕ) (m : π → ℝ) : ι → ℝ := Q.aimK (Q.T - t) m

/-- The weight `W_{t,t+d}`: `W_{t,t} = (γΣ_t + ρA_{t+1})⁻¹ γΣ_t` and
`W_{t,t+d+1} = (γΣ_t + ρA_{t+1})⁻¹ ρA_{t+1} W_{t+1,t+d+1}`. -/
def W : ℕ → ℕ → Matrix ι ι ℝ
  | 0, t => (Q.S t + Q.rho • Q.A (t + 1))⁻¹ * Q.S t
  | d + 1, t => (Q.S t + Q.rho • Q.A (t + 1))⁻¹ * (Q.rho • Q.A (t + 1)) * W d (t + 1)

/-- The value `J_t(x, m) = -(1/2) x'A_t x + x'(C_t m + c_t) + q_t(m)`. -/
def J (q : ℕ → (π → ℝ) → ℝ) (t : ℕ) (x : ι → ℝ) (m : π → ℝ) : ℝ :=
  -(1 / 2) * (x ⬝ᵥ (Q.A t *ᵥ x)) + x ⬝ᵥ (Q.C t *ᵥ m + Q.c t) + q t m

/-- The Bellman objective at review `t` from `(x_{t-1}, m_t) = (xm, m)`, at `x_t = x`. -/
def obj (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) (q : ℕ → (π → ℝ) → ℝ)
    (t : ℕ) (xm : ι → ℝ) (m : π → ℝ) (x : ι → ℝ) : ℝ :=
  -(1 / 2) * ((x - xm) ⬝ᵥ (Q.Lam *ᵥ (x - xm))) + x ⬝ᵥ (Q.G t *ᵥ m - Q.e)
    - (1 / 2) * (x ⬝ᵥ (Q.S t *ᵥ x)) + Q.rho * E t (fun m' => Q.J q (t + 1) x m') m

end LQ

/-- `E_t` is linear, preserves constants and satisfies `E_t m_{t+1} = m_t`. -/
def Martingale (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) : Prop :=
  (∀ t (a : ℝ), E t (fun _ => a) = fun _ => a) ∧ ∀ t (i : π), E t (fun m' => m' i) = fun m => m i

/-- Part 3, verification: for some `q` with `q_T = 0`, `J` satisfies the Bellman equation, and the
stated affine policy is its unique maximizer at every review and state. -/
def BellmanVerif : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (Q : LQ ι π), Q.Setting → ∀ E, Martingale E →
    ∃ q : ℕ → (π → ℝ) → ℝ, (∀ m, q Q.T m = 0) ∧ ∀ t, t < Q.T → ∀ xm m,
      (∀ x, x ≠ Q.policy t xm m → Q.obj E q t xm m x < Q.obj E q t xm m (Q.policy t xm m)) ∧
      Q.obj E q t xm m (Q.policy t xm m) = Q.J q t xm m

/-- Part 3, the matrices: `D_t ≻ 0`, `0 ⪯ A_t ⪯ Λ`; `Γ_t = D_t⁻¹(γΣ_t + ρA_{t+1})` is similar to a
symmetric `M` with `0 ≺ M ⪯ I` (eigenvalues in `(0, 1]`), and `M ≺ I` (eigenvalues in `(0, 1)`)
when `Λ ≻ 0`; `Γ_t v = v` exactly when `Λv = 0` (eigenvalue 1 on `Λ`'s null directions, where the
position is re-set in full); `Γ_t = Λ⁻¹A_t` when `Λ` is invertible. -/
def Matrices : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (Q : LQ ι π), Q.Setting → ∀ t, t < Q.T →
    (Q.D t).PosDef ∧ (Q.A t).PosSemidef ∧ (Q.Lam - Q.A t).PosSemidef ∧
    Q.Gam t = (Q.D t)⁻¹ * (Q.S t + Q.rho • Q.A (t + 1)) ∧
    (∃ R M : Matrix ι ι ℝ, IsUnit R ∧ Q.Gam t = R⁻¹ * M * R ∧ M.PosDef ∧
      (1 - M).PosSemidef ∧ (Q.Lam.PosDef → (1 - M).PosDef)) ∧
    (∀ v, Q.Gam t *ᵥ v = v ↔ Q.Lam *ᵥ v = 0) ∧
    (IsUnit Q.Lam → Q.Gam t = Q.Lam⁻¹ * Q.A t)

/-- Part 3, the aim: the policy is partial adjustment `x_t = x_{t-1} + Γ_t (aim_t - x_{t-1})`;
`aim_{T-1} = Markowitz_{T-1}`; and `aim_t = Σ_{s=t}^{T-1} W_{t,s} Markowitz_s` with weights summing
to `I`. -/
def Aim : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (Q : LQ ι π), Q.Setting → ∀ t, t < Q.T →
    (∀ xm m, Q.policy t xm m = xm + Q.Gam t *ᵥ (Q.aim t m - xm)) ∧
    (∀ m, Q.aim (Q.T - 1) m = Q.mkw (Q.T - 1) m) ∧
    ∑ d : Fin (Q.T - t), Q.W d t = 1 ∧
    ∀ m, Q.aim t m = ∑ d : Fin (Q.T - t), Q.W d t *ᵥ Q.mkw (t + d) m


/-! ### Part 1: the Kalman covariance recursion -/

/-- The Kalman covariance recursion for the constant state `θ` (M5's baseline `Φ = I`, `Q = 0`):
`P_{t+1} = P_t - P_t H'(H P_t H' + R)⁻¹ H P_t`. It involves only `P_0`, `H` and `R`, not positions
or trades. -/
def kal {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (P0 : Matrix ι ι ℝ) (H : Matrix κ ι ℝ)
    (R : Matrix κ κ ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => P0
  | t + 1 => kal P0 H R t - kal P0 H R t * Hᵀ * (H * kal P0 H R t * Hᵀ + R)⁻¹ * H * kal P0 H R t

/-- Part 1(a): with `P_0 ≻ 0` and `R ≻ 0`, every `P_t` is positive definite, with information form
`P_t⁻¹ = P_0⁻¹ + t H'R⁻¹H`; `P_t` is nonincreasing; the belief-mean innovation `K_t(y - Hm - d)`
has covariance `K_t(HP_tH' + R)K_t' = P_t - P_{t+1}`; and `Σ_t = GP_tG' + Σ_r` is positive definite
and nonincreasing in `t`. All of these are deterministic, and none depends on positions. -/
def FilterFacts : Prop :=
  ∀ (θ ω : Type) [Fintype θ] [DecidableEq θ] [Fintype ω] [DecidableEq ω] (P0 : Matrix θ θ ℝ)
    (H : Matrix ω θ ℝ) (R : Matrix ω ω ℝ), P0.PosDef → R.PosDef →
    (∀ t, (kal P0 H R t).PosDef) ∧
    (∀ t : ℕ, (kal P0 H R t)⁻¹ = P0⁻¹ + (t : ℝ) • (Hᵀ * R⁻¹ * H)) ∧
    (∀ t, (kal P0 H R t - kal P0 H R (t + 1)).PosSemidef) ∧
    (∀ t, (kal P0 H R t * Hᵀ * (H * kal P0 H R t * Hᵀ + R)⁻¹) * (H * kal P0 H R t * Hᵀ + R) *
      (kal P0 H R t * Hᵀ * (H * kal P0 H R t * Hᵀ + R)⁻¹)ᵀ = kal P0 H R t - kal P0 H R (t + 1)) ∧
    ∀ (ι : Type) [Fintype ι] (G : Matrix ι θ ℝ) (Sr : Matrix ι ι ℝ), Sr.PosDef → ∀ t,
      (G * kal P0 H R t * Gᵀ + Sr).PosDef ∧
      ∀ s, t ≤ s → ((G * kal P0 H R t * Gᵀ + Sr) - (G * kal P0 H R s * Gᵀ + Sr)).PosSemidef

/-- M5's observation map `L = [[I, 0, 0]; [B^A, I, 0]; [B^E, 0, I]]`, on `(f, r^A, r^E)`. -/
def Lobs {K N M : ℕ} (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ) :
    Matrix ((Fin K ⊕ Fin N) ⊕ Fin M) ((Fin K ⊕ Fin N) ⊕ Fin M) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 0 BA 1) 0 (Matrix.fromCols BE 0) 1

/-- The transformed observation matrix `H̃ = [[I_K, 0]; [0, I_N]; [0, 0]]`. -/
def Htil (K N M : ℕ) : Matrix ((Fin K ⊕ Fin N) ⊕ Fin M) (Fin K ⊕ Fin N) ℝ := Matrix.fromRows 1 0

/-- `Σ_z = diag(Σ_f, Σ_A, Σ_E)`. -/
def Sz {K N M : ℕ} (Sf : Matrix (Fin K) (Fin K) ℝ) (SA : Matrix (Fin N) (Fin N) ℝ)
    (SE : Matrix (Fin M) (Fin M) ℝ) : Matrix ((Fin K ⊕ Fin N) ⊕ Fin M) ((Fin K ⊕ Fin N) ⊕ Fin M) ℝ :=
  Matrix.fromBlocks (Matrix.fromBlocks Sf 0 0 SA) 0 0 SE

/-- Part 1(b), the reference case: `Σ_z = diag(Σ_f, Σ_A, Σ_E)` and a block-diagonal prior.
- `L` is invertible, and `L⁻¹(f, r^A, r^E) = (f, r^A - B^A f, r^E - B^E f)`.
- For any invertible `L`, the filter with `H = L H̃` and noise `L Σ_z L'`, where
  `H̃ = [[I_K, 0]; [0, I_N]; [0, 0]]`, has `P_t = diag(P^λ_t, P^α_t)`. Here `P^λ` is the filter of the
  factor block alone (observation `I`, noise `Σ_f`), and `P^α` that of the alpha block alone (noise
  `Σ_A`).
- In the transformed coordinates the gain is `diag(P^λ(P^λ + Σ_f)⁻¹, P^α(P^α + Σ_A)⁻¹)` beside a zero
  ETF column. So each block is updated from its own observation block, and the ETF block carries
  no information.
- `GP_tG' + Σ_r = B(Σ_f + P^λ_t)B' + diag(Σ_A + P^α_t, Σ_E)` for `G = [[B^A, I]; [B^E, 0]]` and
  `Σ_r = BΣ_fB' + diag(Σ_A, Σ_E)`. -/
def Decouple : Prop :=
  (∀ (K N M : ℕ) (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ),
    IsUnit (Lobs BA BE) ∧ ∀ (f : Fin K → ℝ) (rA : Fin N → ℝ) (rE : Fin M → ℝ),
      (Lobs BA BE)⁻¹ *ᵥ Sum.elim (Sum.elim f rA) rE =
        Sum.elim (Sum.elim f (rA - BA *ᵥ f)) (rE - BE *ᵥ f)) ∧
  (∀ (K N M : ℕ) (Pl Sf : Matrix (Fin K) (Fin K) ℝ) (Pa SA : Matrix (Fin N) (Fin N) ℝ)
    (SE : Matrix (Fin M) (Fin M) ℝ) (L : Matrix ((Fin K ⊕ Fin N) ⊕ Fin M) ((Fin K ⊕ Fin N) ⊕ Fin M) ℝ),
    Pl.PosDef → Pa.PosDef → Sf.PosDef → SA.PosDef → SE.PosDef → IsUnit L → ∀ t,
      kal (Matrix.fromBlocks Pl 0 0 Pa) (L * Htil K N M) (L * Sz Sf SA SE * Lᵀ) t =
        Matrix.fromBlocks (kal Pl 1 Sf t) 0 0 (kal Pa 1 SA t) ∧
      Matrix.fromBlocks (kal Pl 1 Sf t) 0 0 (kal Pa 1 SA t) * (Htil K N M)ᵀ *
          (Htil K N M * Matrix.fromBlocks (kal Pl 1 Sf t) 0 0 (kal Pa 1 SA t) * (Htil K N M)ᵀ +
            Sz Sf SA SE)⁻¹ =
        Matrix.fromCols (Matrix.fromBlocks (kal Pl 1 Sf t * (kal Pl 1 Sf t + Sf)⁻¹) 0 0
          (kal Pa 1 SA t * (kal Pa 1 SA t + SA)⁻¹)) 0) ∧
  ∀ (K N M : ℕ) (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ)
    (Sf Pl : Matrix (Fin K) (Fin K) ℝ) (SA Pa : Matrix (Fin N) (Fin N) ℝ) (SE : Matrix (Fin M) (Fin M) ℝ),
    Matrix.fromBlocks BA 1 BE 0 * Matrix.fromBlocks Pl 0 0 Pa * (Matrix.fromBlocks BA 1 BE 0)ᵀ +
        (Matrix.fromRows BA BE * Sf * (Matrix.fromRows BA BE)ᵀ + Matrix.fromBlocks SA 0 0 SE) =
      Matrix.fromRows BA BE * (Sf + Pl) * (Matrix.fromRows BA BE)ᵀ + Matrix.fromBlocks (SA + Pa) 0 0 SE

/-! ### Part 4: exposure-and-fund coordinates -/

/-- `S = [[B^A', B^E']; [I_N, 0]]`, mapping positions `x = (x^A, x^E)` to `w = (y, x^A)`, `y = B'x`
(`M = K`). -/
def Smap {K N : ℕ} (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin K ⊕ Fin N) (Fin N ⊕ Fin K) ℝ :=
  Matrix.fromBlocks BAᵀ BEᵀ 1 0

/-- M5's `G = [[B^A, I]; [B^E, 0]]` with `M = K`. -/
def Gmat {K N : ℕ} (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin N ⊕ Fin K) (Fin K ⊕ Fin N) ℝ :=
  Matrix.fromBlocks BA 1 BE 0

/-- `S⁻¹ = [[0, I]; [R', -R'B^A']]` with `R = (B^E)⁻¹`. -/
def Sinv {K N : ℕ} (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin N ⊕ Fin K) (Fin K ⊕ Fin N) ℝ :=
  Matrix.fromBlocks 0 1 (BE⁻¹)ᵀ (-((BE⁻¹)ᵀ * BAᵀ))

/-- The problem in coordinates `w = S x`: `Λ~ = S⁻ᵀΛS⁻¹`, `γΣ~_t = S⁻ᵀ γΣ_t S⁻¹`, and the mean map
`S⁻ᵀ(G m - e)`. -/
def LQ.trans {κ : Type} (Q : LQ ι π) (Si : Matrix ι κ ℝ) : LQ κ π where
  T := Q.T
  Lam := Siᵀ * Q.Lam * Si
  S := fun t => Siᵀ * Q.S t * Si
  rho := Q.rho
  G := fun t => Siᵀ * Q.G t
  e := Siᵀ *ᵥ Q.e

/-- Part 4, the coordinates, with `M = K` and `B^E` invertible.
- `S` is invertible with the stated inverse, and `S' = G`, so `S⁻ᵀG = I`: the mean in `w` is
  `m - S⁻ᵀe`, with `S⁻ᵀ(0, c^E) = (φ, -B^A φ)` and `φ = R c^E`.
- The ETF position is `x^E = R'(y - B^A' x^A)`. -/
def Coords : Prop :=
  ∀ (K N : ℕ) (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin K) (Fin K) ℝ), IsUnit BE.det →
    Smap BA BE * Sinv BA BE = 1 ∧ Sinv BA BE * Smap BA BE = 1 ∧
    (Smap BA BE)ᵀ = Gmat BA BE ∧ (Sinv BA BE)ᵀ * Gmat BA BE = 1 ∧
    (∀ cE : Fin K → ℝ, (Sinv BA BE)ᵀ *ᵥ Sum.elim 0 cE =
      Sum.elim (BE⁻¹ *ᵥ cE) (-(BA *ᵥ (BE⁻¹ *ᵥ cE)))) ∧
    ∀ (y : Fin K → ℝ) (xA : Fin N → ℝ),
      Sinv BA BE *ᵥ Sum.elim y xA = Sum.elim xA ((BE⁻¹)ᵀ *ᵥ (y - BAᵀ *ᵥ xA))

/-- Part 4, the change of coordinates: for invertible `S`, the problem in `w = Sx` satisfies part 3's
hypotheses, and its optimal policy is `S` times the optimal policy in `x`. So the general policy is
part 3 applied to `(m~_t, Σ~_t, Λ~)`, mapped back by `x = S⁻¹w`. -/
def Transform : Prop :=
  ∀ (ι κ π : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype π]
    (Q : LQ ι π) (Sm : Matrix κ ι ℝ) (Si : Matrix ι κ ℝ), Q.Setting → Sm * Si = 1 → Si * Sm = 1 →
    (Q.trans Si).Setting ∧ ∀ t, t < Q.T → ∀ xm m,
      (Q.trans Si).policy t (Sm *ᵥ xm) m = Sm *ᵥ Q.policy t xm m

/-- Part 4, the reference-case blocks: with `Σ_t = B(Σ_f + P^λ_t)B' + diag(Σ_A + P^α_t, Σ_E)` and
`Λ = diag(Λ_A, Λ_E)`, and with `Ξ = RΣ_ER'` and `Ω = RΛ_ER'`,
`Σ~_t = [[Σ_f + P^λ_t + Ξ, -ΞB^A']; [-B^AΞ, Σ_A + P^α_t + B^AΞB^A']]` and
`Λ~ = [[Ω, -ΩB^A']; [-B^AΩ, Λ_A + B^AΩB^A']]`. -/
def RefBlocks : Prop :=
  ∀ (K N : ℕ) (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin K) (Fin K) ℝ)
    (SfP : Matrix (Fin K) (Fin K) ℝ) (SAP LA : Matrix (Fin N) (Fin N) ℝ) (SE LE : Matrix (Fin K) (Fin K) ℝ),
    IsUnit BE.det →
    (Sinv BA BE)ᵀ * (Matrix.fromRows BA BE * SfP * (Matrix.fromRows BA BE)ᵀ + Matrix.fromBlocks SAP 0 0 SE) *
        Sinv BA BE =
      Matrix.fromBlocks (SfP + BE⁻¹ * SE * (BE⁻¹)ᵀ) (-(BE⁻¹ * SE * (BE⁻¹)ᵀ * BAᵀ))
        (-(BA * (BE⁻¹ * SE * (BE⁻¹)ᵀ))) (SAP + BA * (BE⁻¹ * SE * (BE⁻¹)ᵀ) * BAᵀ) ∧
    (Sinv BA BE)ᵀ * Matrix.fromBlocks LA 0 0 LE * Sinv BA BE =
      Matrix.fromBlocks (BE⁻¹ * LE * (BE⁻¹)ᵀ) (-(BE⁻¹ * LE * (BE⁻¹)ᵀ * BAᵀ))
        (-(BA * (BE⁻¹ * LE * (BE⁻¹)ᵀ))) (LA + BA * (BE⁻¹ * LE * (BE⁻¹)ᵀ) * BAᵀ)

/-- Part 4(a), exact separation: in `w = (y, x^A)`, with `Λ~ = diag(0, Λ_A)`,
`γΣ~_t = diag(Sy_t, SA_t)` (`Sy_t = γ(Σ_f + P^λ_t)`, `SA_t = γ(Σ_A + P^α_t)`), mean map the identity
and no fee (`Λ_E = 0`, `Σ_E = 0`, `c^E = 0` in the blocks above):
- the exposure is myopic, `y_t = Sy_t⁻¹ λ̂_t`, and adjusts at speed `I`;
- the fund block follows part 3 for `(Λ_A, SA_t, ρ)` and `α̂_t`. -/
def Separation : Prop :=
  ∀ (K N : ℕ) (Q : LQ (Fin K ⊕ Fin N) (Fin K ⊕ Fin N)) (LA : Matrix (Fin N) (Fin N) ℝ)
    (Sy : ℕ → Matrix (Fin K) (Fin K) ℝ) (SA : ℕ → Matrix (Fin N) (Fin N) ℝ),
    Q.Setting → Q.Lam = Matrix.fromBlocks 0 0 0 LA → (∀ t, Q.S t = Matrix.fromBlocks (Sy t) 0 0 (SA t)) →
    (∀ t, Q.G t = 1) → Q.e = 0 →
    let QA : LQ (Fin N) (Fin N) := ⟨Q.T, LA, SA, Q.rho, fun _ => 1, 0⟩
    ∀ t, t < Q.T →
      (∀ (y : Fin K → ℝ) (xA : Fin N → ℝ) (lh : Fin K → ℝ) (ah : Fin N → ℝ),
        Q.policy t (Sum.elim y xA) (Sum.elim lh ah) = Sum.elim ((Sy t)⁻¹ *ᵥ lh) (QA.policy t xA ah)) ∧
      Q.Gam t = Matrix.fromBlocks 1 0 0 (QA.Gam t)

/-! ### Part 5: the separated homogeneous fund block -/

/-- `p_t = (1/s² + t/σ²)⁻¹`. -/
def pvar (s2 sig2 : ℝ) (t : ℕ) : ℝ := 1 / (1 / s2 + t / sig2)

/-- The scalar trading rate with `k` reviews left (horizon `T`): `g_T = 0` and
`g_t = 1 - 1/(1 + γ(σ² + p_t)/λ_A + ρ g_{t+1})`. -/
def gK (lam gam sig2 s2 rho : ℝ) (T : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 1 - 1 / (1 + gam * (sig2 + pvar s2 sig2 (T - (k + 1))) / lam +
      rho * gK lam gam sig2 s2 rho T k)

/-- `g_t` at horizon `T`. -/
def gseq (lam gam sig2 s2 rho : ℝ) (T t : ℕ) : ℝ := gK lam gam sig2 s2 rho T (T - t)

/-- The stationary Riccati value `a_∞`: the root in `[0, λ_A]` of
`a = λ_A - λ_A²/(λ_A + γσ² + ρa)`, that is,
`[-(γσ² + (1-ρ)λ_A) + √((γσ² + (1-ρ)λ_A)² + 4ργσ²λ_A)]/(2ρ)` for `ρ > 0`, and `λ_Aγσ²/(λ_A + γσ²)` at
`ρ = 0`. -/
def astar (lam gam sig2 rho : ℝ) : ℝ :=
  if rho = 0 then lam * (gam * sig2) / (lam + gam * sig2) else
    (-(gam * sig2 + (1 - rho) * lam) +
      Real.sqrt ((gam * sig2 + (1 - rho) * lam) ^ 2 + 4 * rho * (gam * sig2) * lam)) / (2 * rho)

/-- `garleanu2009dynamic`'s equation (9): `a = [-(γ(1-ρ) + λρ) + √((γ(1-ρ) + λρ)² + 4γλ(1-ρ)²)]/(2(1-ρ))`,
with trading rate `a/λ`. -/
def aGP (gamG lamG rhoG : ℝ) : ℝ :=
  (-(gamG * (1 - rhoG) + lamG * rhoG) +
    Real.sqrt ((gamG * (1 - rhoG) + lamG * rhoG) ^ 2 + 4 * gamG * lamG * (1 - rhoG) ^ 2)) /
    (2 * (1 - rhoG))

/-- Part 5.
- The fund block's filter with `Σ_A = σ²I` and prior `s²I` gives `P^α_t = p_t I`.
- With `Λ_A = λ_A I`, the fund block's recursion is scalar, `A^A_t = λ_A g_t I` and `Γ^A_t = g_t I`,
  with `0 < g_t < 1` for `t < T`, strictly decreasing in `λ_A` and strictly increasing in `γ`.
- The stationary limit, for `ρ ∈ [0, 1]`: `a_∞` is the unique root in `[0, λ_A]`, with
  `a_∞/λ_A ∈ (0, 1)`. For every `t`, `a_t^{(T)} = λ_A g_t` converges as `T → ∞`, and these limits
  converge to `a_∞` as `t → ∞`.
- Remark, not part of the statement (the last conjunct): for `0 < ρ < 1`, `a_∞/λ_A` is
  `garleanu2009dynamic`'s `a/λ` under `(γ_GP, ρ_GP, λ_GP) = (γ/ρ, 1 - ρ, λ_A/σ²)`. -/
def Speeds : Prop :=
  (∀ (N : ℕ) (s2 sig2 : ℝ), 0 < s2 → 0 < sig2 → ∀ t,
    kal (s2 • (1 : Matrix (Fin N) (Fin N) ℝ)) (1 : Matrix (Fin N) (Fin N) ℝ) (sig2 • 1) t =
      pvar s2 sig2 t • 1) ∧
  (∀ (N : ℕ) (π : Type) [Fintype π] (Q : LQ (Fin N) π) (lam gam sig2 s2 : ℝ),
    0 < lam → 0 < gam → 0 < sig2 → 0 < s2 →
    0 ≤ Q.rho → Q.Lam = lam • 1 → (∀ t, Q.S t = (gam * (sig2 + pvar s2 sig2 t)) • 1) →
    ∀ t, t < Q.T →
      Q.A t = (lam * gseq lam gam sig2 s2 Q.rho Q.T t) • 1 ∧
      Q.Gam t = gseq lam gam sig2 s2 Q.rho Q.T t • 1) ∧
  (∀ (lam gam sig2 s2 rho : ℝ) (T t : ℕ), 0 < lam → 0 < gam → 0 < sig2 → 0 < s2 → 0 ≤ rho →
    t < T → 0 < gseq lam gam sig2 s2 rho T t ∧ gseq lam gam sig2 s2 rho T t < 1) ∧
  (∀ (lam₁ lam₂ gam sig2 s2 rho : ℝ) (T t : ℕ), 0 < lam₁ → lam₁ < lam₂ → 0 < gam → 0 < sig2 →
    0 < s2 → 0 ≤ rho → t < T →
      gseq lam₂ gam sig2 s2 rho T t < gseq lam₁ gam sig2 s2 rho T t) ∧
  (∀ (lam gam₁ gam₂ sig2 s2 rho : ℝ) (T t : ℕ), 0 < lam → 0 < gam₁ → gam₁ < gam₂ → 0 < sig2 →
    0 < s2 → 0 ≤ rho → t < T →
      gseq lam gam₁ sig2 s2 rho T t < gseq lam gam₂ sig2 s2 rho T t) ∧
  (∀ (lam gam sig2 s2 rho : ℝ), 0 < lam → 0 < gam → 0 < sig2 → 0 < s2 → 0 ≤ rho → rho ≤ 1 →
    (0 ≤ astar lam gam sig2 rho ∧ astar lam gam sig2 rho ≤ lam ∧
      astar lam gam sig2 rho = lam - lam ^ 2 / (lam + gam * sig2 + rho * astar lam gam sig2 rho) ∧
      ∀ b, 0 ≤ b → b ≤ lam → b = lam - lam ^ 2 / (lam + gam * sig2 + rho * b) →
        b = astar lam gam sig2 rho) ∧
    0 < astar lam gam sig2 rho / lam ∧ astar lam gam sig2 rho / lam < 1 ∧
    ∃ ainf : ℕ → ℝ,
      (∀ t, Filter.Tendsto (fun T => lam * gseq lam gam sig2 s2 rho T t) Filter.atTop
        (nhds (ainf t))) ∧
      Filter.Tendsto ainf Filter.atTop (nhds (astar lam gam sig2 rho))) ∧
  (∀ (lam gam sig2 rho : ℝ), 0 < lam → 0 < gam → 0 < sig2 → 0 < rho → rho < 1 →
    astar lam gam sig2 rho / lam = aGP (gam / rho) (lam / sig2) (1 - rho) / (lam / sig2))

/-- Claim 030, parts 1-5. -/
def statement : Prop :=
  FilterFacts ∧ Decouple ∧ BellmanVerif ∧ Matrices ∧ Aim ∧ Coords ∧ Transform ∧ RefBlocks ∧
    Separation ∧ Speeds

end

end Standalone.M5PartialAdjustmentSplit

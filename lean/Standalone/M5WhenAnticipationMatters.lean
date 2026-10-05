import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Standalone.M5LearningAimTwoSpeeds

/-!
# Claim 036: when anticipating learning or mean reversion changes today's trade

Statement only; the proof is `Novel/M5WhenAnticipationMattersProof.lean`.

This is M5's separated homogeneous fund block (claim 032's setting), one fund or direction. The
precision path `p` is a general positive sequence (`Blk`), because part 3 uses the filter's path
under persistence. `Link` shows that on the baseline path `p_t = pvar s² σ² t` every object is
claim 032's (`Dir`). So claim 032's `FundAim` (the fund aim is `ℓ_t α̂/(γσ²)`, the learning factor
times the Markowitz position) applies to the aims here.

The block's objects:
- the risk `r_t = γ(σ² + p_t)` and the recursion `d_t = λ_A + r_t + ρa_{t+1}`,
  `a_t = λ_A - λ_A²/d_t`, `a_T = 0`, with rate `g_t = a_t/λ_A`;
- claim 032's weights `w_{t,t+k}` and learning average `ℓ_t`;
- the learning factor `L_t = ℓ_t(σ² + p_t)/σ²` and the gain `κ_t = p_t/(σ² + p_t)`;
- `cg r n`, the rate of the constant-risk recursion with risk `r` and `n` reviews to go. So the
  static-belief rate is `g^S_t = cg r_t (T - t)` and the known-alpha rate is `cg (γσ²) (T - t)`.

**Paper-level:**
- part 3's aim formula `aim_t = Σ_s w_{t,s} E_t α̂_s/(γ(σ² + p_s))` under persistence (the
  tower property and the claim's lemma extending claim 030's recursion to `Φ_α = φI`);
- part 4(i)'s reading that M5's objective has no hedging demand (the definition of the
  objective).

Formal part 3 starts from that formula (`aimMR`). Part 4(ii) is claim 030's part 4(a), and
part 4(iii)'s link to claim 100 is the one-step identity `Drift`.
-/

namespace Standalone.M5WhenAnticipationMatters

open Matrix Filter Topology Standalone.M5PartialAdjustmentSplit Standalone.M5LearningAimTwoSpeeds

noncomputable section

/-- One fund, or one direction, with a general precision path `p`. -/
structure Blk where
  lam : ℝ
  gam : ℝ
  sig2 : ℝ
  rho : ℝ
  T : ℕ
  p : ℕ → ℝ

namespace Blk

variable (B : Blk)

/-- `λ_A, γ, σ² > 0`, `ρ ∈ (0, 1]`, and a positive precision path. -/
def Setting : Prop :=
  0 < B.lam ∧ 0 < B.gam ∧ 0 < B.sig2 ∧ 0 < B.rho ∧ B.rho ≤ 1 ∧ ∀ t, 0 < B.p t

/-- `r_t = γ(σ² + p_t)`. -/
def r (t : ℕ) : ℝ := B.gam * (B.sig2 + B.p t)

/-- `a_t = λ_A - λ_A²/(λ_A + r_t + ρ a_{t+1})`, `a_T = 0`. -/
def a (t : ℕ) : ℝ :=
  if t < B.T then B.lam - B.lam ^ 2 / (B.lam + B.gam * (B.sig2 + B.p t) + B.rho * a (t + 1)) else 0
termination_by B.T - t

/-- `d_t = λ_A + r_t + ρ a_{t+1}`. -/
def d (t : ℕ) : ℝ := B.lam + B.r t + B.rho * B.a (t + 1)

/-- The rate `g_t = a_t/λ_A`. -/
def g (t : ℕ) : ℝ := B.a t / B.lam

/-- Claim 032's weights: `w_{t,t} = r_t/(d_t - λ_A)`, `w_{t,t+k+1} = ρ a_{t+1}/(d_t - λ_A) · w_{t+1,t+k+1}`. -/
def w : ℕ → ℕ → ℝ
  | 0, t => B.r t / (B.d t - B.lam)
  | k + 1, t => B.rho * B.a (t + 1) / (B.d t - B.lam) * w k (t + 1)

/-- `ℓ_t = Σ_s w_{t,s} σ²/(σ² + p_s)`. -/
def ell (t : ℕ) : ℝ := ∑ k ∈ Finset.range (B.T - t), B.w k t * (B.sig2 / (B.sig2 + B.p (t + k)))

/-- The learning factor `L_t = ℓ_t(σ² + p_t)/σ²`. -/
def L (t : ℕ) : ℝ := B.ell t * ((B.sig2 + B.p t) / B.sig2)

/-- The alpha Kalman gain `κ_t = p_t/(σ² + p_t)`. -/
def kap (t : ℕ) : ℝ := B.p t / (B.sig2 + B.p t)

/-- The renormalized weights `w~_{t,t+k} = w_{t,t+k} σ²/(σ² + p_{t+k}) / ℓ_t`. -/
def wt (k t : ℕ) : ℝ := B.w k t * (B.sig2 / (B.sig2 + B.p (t + k))) / B.ell t

/-- `M_t(φ) = Σ_s w~_{t,s} φ^{s-t}`. -/
def M (t : ℕ) (phi : ℝ) : ℝ := ∑ k ∈ Finset.range (B.T - t), B.wt k t * phi ^ k

/-- The static-belief aim `α̂_t/(γ(σ² + p_t))`. -/
def aimS (ah : ℝ) (t : ℕ) : ℝ := ah / (B.gam * (B.sig2 + B.p t))

/-- The learning-aware aim `ℓ_t α̂_t/(γσ²)` (claim 032's `FundAim`). -/
def aimL (ah : ℝ) (t : ℕ) : ℝ := B.ell t * ah / (B.gam * B.sig2)

/-- Part 3's aim under persistence `φ` with long-run mean `ᾱ`:
`Σ_s w_{t,s} [ᾱ + φ^{s-t}(α̂_t - ᾱ)]/(γ(σ² + p_s))`. -/
def aimMR (abar ah phi : ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (B.T - t), B.w k t * (abar + phi ^ k * (ah - abar)) / (B.gam * (B.sig2 + B.p (t + k)))

/-- The block with cost `λ` in place of `λ_A`. -/
def withLam (lam : ℝ) : Blk := { B with lam := lam }

end Blk

/-- The constant-risk rate with risk `r` and `n` reviews to go:
`cg r (n+1) = (r + ρλ cg r n)/(λ + r + ρλ cg r n)`, `cg r 0 = 0`. -/
def cg (lam rho r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (r + rho * lam * cg lam rho r n) / (lam + r + rho * lam * cg lam rho r n)

/-- The block of claim 032's direction `D`, on its baseline precision path. -/
def ofDir (D : Dir) : Blk := ⟨D.lam, D.gam, D.sig2, D.rho, D.T, D.p⟩

/-- On the baseline path the objects are claim 032's. -/
def Link : Prop :=
  ∀ D : Dir, D.Setting → ∀ t k, (ofDir D).a t = D.a t ∧ (ofDir D).g t = D.g t ∧
    (ofDir D).w k t = D.w k t ∧ (ofDir D).ell t = D.ell t

/-- Part 1: the learning-aware aim is `L_t` times the static-belief aim, with
`1 ≤ L_t < 1 + p_t/σ² = 1/(1 - κ_t)` and the exact form `L_t - 1 = Σ_{s>t} w_{t,s}(p_t - p_s)/(σ² + p_s)`.
For a strictly decreasing path, `L_t = 1` iff `t = T - 1`. A relative change of the target above
`θ ≥ 0` needs `κ_t > θ/(1 + θ)`. -/
def LearningAim : Prop :=
  ∀ B : Blk, B.Setting → Antitone B.p → ∀ t, t < B.T →
    (∀ ah, B.aimL ah t = B.L t * B.aimS ah t) ∧ 1 ≤ B.L t ∧ B.L t < 1 / (1 - B.kap t) ∧
    1 + B.p t / B.sig2 = 1 / (1 - B.kap t) ∧
    B.L t - 1 = ∑ k ∈ Finset.Ico 1 (B.T - t), B.w k t * ((B.p t - B.p (t + k)) / (B.sig2 + B.p (t + k))) ∧
    (StrictAnti B.p → (B.L t = 1 ↔ t = B.T - 1)) ∧
    ∀ θ : ℝ, 0 ≤ θ → θ < B.L t - 1 → θ / (1 + θ) < B.kap t

/-- Part 2: `cg (γσ²) (T - t) ≤ g_t ≤ g^S_t = cg r_t (T - t)`. The constant-risk rate is
increasing in the risk and Lipschitz with constant `n λ/(λ + m)²` above `m ≥ 0`, so
`g^S_t - g_t ≤ (T - t) λ/(λ + γσ²)² γ p_t`. Today's trades `u_t = g_t(aim_t - x)` and
`u^S_t = g^S_t(aim^S_t - x)` satisfy the identity and the bound. -/
def RateTrade : Prop :=
  ∀ B : Blk, B.Setting → Antitone B.p → ∀ t, t < B.T →
    let gS := cg B.lam B.rho (B.r t) (B.T - t)
    let g0 := cg B.lam B.rho (B.gam * B.sig2) (B.T - t)
    g0 ≤ B.g t ∧ B.g t ≤ gS ∧
    (∀ n m r r', 0 ≤ m → m ≤ r → m ≤ r' →
      |cg B.lam B.rho r n - cg B.lam B.rho r' n| ≤ n * (B.lam / (B.lam + m) ^ 2) * |r - r'|) ∧
    (∀ n r r', 0 ≤ r → r < r' → 1 ≤ n → cg B.lam B.rho r n < cg B.lam B.rho r' n) ∧
    gS - B.g t ≤ ((B.T - t : ℕ) : ℝ) * (B.lam / (B.lam + B.gam * B.sig2) ^ 2) * (B.gam * B.p t) ∧
    ∀ ah x : ℝ,
      let u := B.g t * (B.aimL ah t - x)
      let uS := gS * (B.aimS ah t - x)
      u - uS = (B.g t - gS) * (B.aimS ah t - x) + B.g t * (B.L t - 1) * B.aimS ah t ∧
      |u - uS| ≤ (gS - g0) * |B.aimS ah t - x| + B.g t * (B.kap t / (1 - B.kap t)) * |B.aimS ah t|

/-- Part 3: the aim under persistence splits into a long-run part and the deviation part scaled
by `M_t(φ)`. The renormalized weights form a probability, `M_t` is nondecreasing in `φ ∈ [0, 1]`,
`M_t(1) = 1`, and `w~_{t,t} + (1 - w~_{t,t})φ^{T-1-t} ≤ M_t(φ) ≤ 1`. For a nonincreasing path the
future weight `1 - w~_{t,t}` is at least `1 - w_{t,t} = ρa_{t+1}/(r_t + ρa_{t+1})`. -/
def MeanReversion : Prop :=
  ∀ B : Blk, B.Setting → ∀ t, t < B.T →
    (∀ abar ah phi, B.aimMR abar ah phi t =
      B.ell t * abar / (B.gam * B.sig2) + B.M t phi * (B.ell t * (ah - abar) / (B.gam * B.sig2))) ∧
    (∀ k, 0 ≤ B.wt k t) ∧ ∑ k ∈ Finset.range (B.T - t), B.wt k t = 1 ∧
    B.M t 1 = 1 ∧ MonotoneOn (B.M t) (Set.Icc 0 1) ∧
    (∀ phi, 0 ≤ phi → phi ≤ 1 →
      B.wt 0 t + (1 - B.wt 0 t) * phi ^ (B.T - 1 - t) ≤ B.M t phi ∧ B.M t phi ≤ 1) ∧
    B.w 0 t = B.r t / (B.r t + B.rho * B.a (t + 1)) ∧
    (Antitone B.p → 1 - B.w 0 t ≤ 1 - B.wt 0 t)

/-- Part 4(i): both anticipation effects are cost effects. As `λ_A → 0`, `w_{t,t} → 1`,
`L_t → 1` and `M_t(φ) → 1` for every `φ`. -/
def CostEffect : Prop :=
  ∀ B : Blk, B.Setting → ∀ t, t < B.T →
    Tendsto (fun lam => (B.withLam lam).w 0 t) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun lam => (B.withLam lam).L t) (𝓝[>] 0) (𝓝 1) ∧
    ∀ phi, Tendsto (fun lam => (B.withLam lam).M t phi) (𝓝[>] 0) (𝓝 1)

/-- Part 4(iii): claim 100's drift `α̂_t[1/(σ² + p_{t+1}) - 1/(σ² + p_t)]/γ` is the one-step
increment `(σ² + p_t)/(σ² + p_{t+1}) - 1` of the learning factor's numerator times `aim^S_t`. -/
def Drift : Prop :=
  ∀ B : Blk, B.Setting → ∀ (ah : ℝ) (t : ℕ),
    ah * (1 / (B.sig2 + B.p (t + 1)) - 1 / (B.sig2 + B.p t)) / B.gam =
      ((B.sig2 + B.p t) / (B.sig2 + B.p (t + 1)) - 1) * B.aimS ah t

/-! ### The persistence lemma (part 3)

Claim 030's recursion and Bellman verification under affine mean dynamics
`E_t m_{t+1} = Φ m_t + b` (claim 036 uses `Φ = φI` on the alpha block and `b = (1 - φ)ᾱ`). The
risk recursion `A_t` is unchanged. The belief coefficients become
`C_t = Λ D_t⁻¹ (G_t + ρ C_{t+1} Φ)` and `c_t = Λ D_t⁻¹ (ρ(C_{t+1} b + c_{t+1}) - e)`. That
`E_t m_{t+1} = Φ m_t + b` holds (the tower property on the Gaussian model) is paper-level; here it
is the hypothesis `AffineMean`. -/

section Persist

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π]

/-- The recursion under persistence, with `k` reviews left: `(A, C, c)` at review `T - k`. -/
def ricP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) : ℕ → Matrix ι ι ℝ × Matrix ι π ℝ × (ι → ℝ)
  | 0 => (0, 0, 0)
  | k + 1 =>
    let t := Q.T - (k + 1)
    let D := Q.Lam + Q.S t + Q.rho • (ricP Q Phi b k).1
    (Q.Lam - Q.Lam * D⁻¹ * Q.Lam, Q.Lam * D⁻¹ * (Q.G t + Q.rho • ((ricP Q Phi b k).2.1 * Phi)),
      (Q.Lam * D⁻¹) *ᵥ (Q.rho • ((ricP Q Phi b k).2.1 *ᵥ b + (ricP Q Phi b k).2.2) - Q.e))

/-- `C_t` under persistence. -/
def CP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (t : ℕ) : Matrix ι π ℝ := (ricP Q Phi b (Q.T - t)).2.1

/-- `c_t` under persistence. -/
def cP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (t : ℕ) : ι → ℝ := (ricP Q Phi b (Q.T - t)).2.2

/-- The policy under persistence: `x_t = K_t x_{t-1} + D_t⁻¹(G_t + ρC_{t+1}Φ) m_t + D_t⁻¹(ρ(C_{t+1}b + c_{t+1}) - e)`. -/
def policyP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (t : ℕ) (xm : ι → ℝ) (m : π → ℝ) : ι → ℝ :=
  Q.K t *ᵥ xm + ((Q.D t)⁻¹ * (Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi))) *ᵥ m +
    (Q.D t)⁻¹ *ᵥ (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e)

/-- The value `J_t(x, m) = -(1/2) x'A_t x + x'(C_t m + c_t) + q_t(m)` under persistence. -/
def JP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (q : ℕ → (π → ℝ) → ℝ) (t : ℕ) (x : ι → ℝ)
    (m : π → ℝ) : ℝ :=
  -(1 / 2) * (x ⬝ᵥ (Q.A t *ᵥ x)) + x ⬝ᵥ (CP Q Phi b t *ᵥ m + cP Q Phi b t) + q t m

/-- The Bellman objective under persistence. -/
def objP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ))
    (q : ℕ → (π → ℝ) → ℝ) (t : ℕ) (xm : ι → ℝ) (m : π → ℝ) (x : ι → ℝ) : ℝ :=
  -(1 / 2) * ((x - xm) ⬝ᵥ (Q.Lam *ᵥ (x - xm))) + x ⬝ᵥ (Q.G t *ᵥ m - Q.e)
    - (1 / 2) * (x ⬝ᵥ (Q.S t *ᵥ x)) + Q.rho * E t (fun m' => JP Q Phi b q (t + 1) x m') m

/-- `E_t` is linear, preserves constants and satisfies `E_t m_{t+1} = Φ m_t + b`. -/
def AffineMean (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) (Phi : Matrix π π ℝ) (b : π → ℝ) : Prop :=
  (∀ t (a : ℝ), E t (fun _ => a) = fun _ => a) ∧
    ∀ t (i : π), E t (fun m' => m' i) = fun m => (Phi *ᵥ m + b) i

/-- The `d`-step forecast `E_t m_{t+d}`: `Φ^d m + Σ_{j<d} Φ^j b`. -/
def fc (Phi : Matrix π π ℝ) (b : π → ℝ) : ℕ → (π → ℝ) → π → ℝ
  | 0 => fun m => m
  | d + 1 => fun m => fc Phi b d (Phi *ᵥ m + b)

/-- The aim under persistence, `aim_t = Σ_{s=t}^{T-1} W_{t,s} E_t Markowitz_s`. -/
def aimP (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ) (t : ℕ) (m : π → ℝ) : ι → ℝ :=
  ∑ d ∈ Finset.range (Q.T - t), Q.W d t *ᵥ Q.mkw (t + d) (fc Phi b d m)

end Persist

/-- The persistence lemma, verification: `A_t` is claim 030's, and for some `q` with `q_T = 0`, `J`
satisfies the Bellman equation under persistence, with the stated affine policy its unique
maximizer at every review and state. -/
def Persistence : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ),
    Q.Setting → (∀ t, (ricP Q Phi b (Q.T - t)).1 = Q.A t) ∧
    ∀ E, AffineMean E Phi b →
      ∃ q : ℕ → (π → ℝ) → ℝ, (∀ m, q Q.T m = 0) ∧ ∀ t, t < Q.T → ∀ xm m,
        (∀ x, x ≠ policyP Q Phi b t xm m → objP Q Phi b E q t xm m x < objP Q Phi b E q t xm m (policyP Q Phi b t xm m)) ∧
        objP Q Phi b E q t xm m (policyP Q Phi b t xm m) = JP Q Phi b q t xm m

/-- The persistence lemma, the aim: the policy is partial adjustment at claim 030's rate toward
`aim_t = Σ_s W_{t,s} Markowitz_s(E_t m_s)`. -/
def PersistAim : Prop :=
  ∀ (ι π : Type) [Fintype ι] [DecidableEq ι] [Fintype π] (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ),
    Q.Setting → ∀ t, t < Q.T → ∀ xm m,
      policyP Q Phi b t xm m = xm + Q.Gam t *ᵥ (aimP Q Phi b t m - xm)

/-- The one-fund problem of a block (claim 030's `LQ` with cost `λ_A`, risk `r_t`, mean map `1`, no fee). -/
def Blk.lq (B : Blk) : LQ (Fin 1) (Fin 1) where
  T := B.T
  Lam := B.lam • 1
  S := fun t => B.r t • 1
  rho := B.rho
  G := fun _ => 1
  e := 0

/-- The persistence lemma in the scalar block: with `Φ = φ` and `b = (1 - φ)ᾱ`, the aim is part 3's
`Σ_s w_{t,s}[ᾱ + φ^{s-t}(α̂_t - ᾱ)]/(γ(σ² + p_s))`, the formula formal part 3 starts from. -/
def PersistLink : Prop :=
  ∀ B : Blk, B.Setting → ∀ (abar ah phi : ℝ) (t : ℕ), t < B.T →
    aimP B.lq (phi • 1) (fun _ => (1 - phi) * abar) t (fun _ => ah) 0 = B.aimMR abar ah phi t

/-- Claim 036. Part 4(ii) is claim 030's `Separation`: the costless exposure is re-set to the
myopic position every review. The persistence lemma behind part 3 is `Persistence`, `PersistAim`
and `PersistLink`. -/
def statement : Prop :=
  Link ∧ LearningAim ∧ RateTrade ∧ MeanReversion ∧ CostEffect ∧ Separation ∧ Drift ∧
    Persistence ∧ PersistAim ∧ PersistLink

end

end Standalone.M5WhenAnticipationMatters

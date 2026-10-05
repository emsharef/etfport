import Standalone.M5PartialAdjustmentSplit

/-!
# Claim 032: learning is anticipated only where trading costs; two speeds under the pooled prior

Statement only; the proof is `Novel/M5LearningAimTwoSpeedsProof.lean`.

This is claim 030's separated reference case (part 4(a)), with `N ≥ 1` homogeneous funds:
`Σ_A = σ²I`, `Λ_A = λ_A I` with `λ_A > 0`, and the pooled prior `P^α_0 = s²I + s̄² 11'` with
`s² > 0` and `s̄² ≥ 0`.
- `Π_c = 11'/N` projects on the common direction, and `Π_r = I - Π_c` on the relative directions.
- `p^c_t = (1/(s² + Ns̄²) + t/σ²)⁻¹` and `p^r_t = (1/s² + t/σ²)⁻¹` are claim 030's `pvar` at the
  prior variances `s² + Ns̄²` and `s²`.
- The scalar trading rates are claim 030's `gseq` at the same prior variances, `g^dir_t = a^dir_t/λ_A`.

The fund block is claim 030's problem (`LQ`) with cost `λ_A I`, risk `γ(σ²I + P^α_t)`, mean map
the identity on `α̂` and no fee. The paper-level steps are claim 030's.
-/

namespace Standalone.M5LearningAimTwoSpeeds

open Matrix Standalone.M5PartialAdjustmentSplit

noncomputable section

/-- The all-ones matrix `11'`. -/
def ones (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun _ _ => 1

/-- `Π_c = 11'/N`. -/
def Pc (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := (N : ℝ)⁻¹ • ones N

/-- `Π_r = I - Π_c`. -/
def Pr (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := 1 - Pc N

/-- The common-direction variance `p^c_t`. -/
def pc (N : ℕ) (s2 sb2 sig2 : ℝ) (t : ℕ) : ℝ := pvar (s2 + N * sb2) sig2 t

/-- The relative-direction variance `p^r_t`. -/
def pr (s2 sig2 : ℝ) (t : ℕ) : ℝ := pvar s2 sig2 t

/-- `P^α_t`: the alpha block's Kalman covariance (observation `I`, noise `σ²I`, prior
`s²I + s̄²11'`). -/
def postA (N : ℕ) (s2 sb2 sig2 : ℝ) (t : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  kal (s2 • (1 : Matrix (Fin N) (Fin N) ℝ) + sb2 • ones N) (1 : Matrix (Fin N) (Fin N) ℝ)
    (sig2 • (1 : Matrix (Fin N) (Fin N) ℝ)) t

/-- The data of a direction: `λ_A`, `γ`, `σ²`, the prior variance of the direction, `ρ`, `T`. -/
structure Dir where
  lam : ℝ
  gam : ℝ
  sig2 : ℝ
  s2 : ℝ
  rho : ℝ
  T : ℕ

namespace Dir

variable (D : Dir)

/-- `p_t`. -/
def p (t : ℕ) : ℝ := pvar D.s2 D.sig2 t
/-- `g_t`. -/
def g (t : ℕ) : ℝ := gseq D.lam D.gam D.sig2 D.s2 D.rho D.T t
/-- `a_t = λ_A g_t`. -/
def a (t : ℕ) : ℝ := D.lam * D.g t
/-- `d_u = λ_A + γ(σ² + p_u) + ρ a_{u+1}`. -/
def d (u : ℕ) : ℝ := D.lam + D.gam * (D.sig2 + D.p u) + D.rho * D.a (u + 1)

/-- The weight `w_{t,t+k}`: `w_{t,t} = γ(σ² + p_t)/(d_t - λ_A)` and
`w_{t,t+k+1} = ρ a_{t+1}/(d_t - λ_A) · w_{t+1,t+k+1}`. -/
def w : ℕ → ℕ → ℝ
  | 0, t => D.gam * (D.sig2 + D.p t) / (D.d t - D.lam)
  | k + 1, t => D.rho * D.a (t + 1) / (D.d t - D.lam) * w k (t + 1)

/-- The learning factor's average `ℓ_t = Σ_{s=t}^{T-1} w_{t,s} σ²/(σ² + p_s)`. -/
def ell (t : ℕ) : ℝ := ∑ k ∈ Finset.range (D.T - t), D.w k t * (D.sig2 / (D.sig2 + D.p (t + k)))

/-- The learning factor `ℓ_t (σ² + p_t)/σ²`. -/
def factor (t : ℕ) : ℝ := D.ell t * ((D.sig2 + D.p t) / D.sig2)

/-- `λ_A > 0`, `γ > 0`, `σ² > 0`, prior variance `> 0`, `ρ ∈ (0, 1]`. -/
def Setting : Prop := 0 < D.lam ∧ 0 < D.gam ∧ 0 < D.sig2 ∧ 0 < D.s2 ∧ 0 < D.rho ∧ D.rho ≤ 1

end Dir

/-- The two directions of the fund block. -/
def dirC (N : ℕ) (lam gam sig2 s2 sb2 rho : ℝ) (T : ℕ) : Dir := ⟨lam, gam, sig2, s2 + N * sb2, rho, T⟩
/-- The relative direction. -/
def dirR (lam gam sig2 s2 rho : ℝ) (T : ℕ) : Dir := ⟨lam, gam, sig2, s2, rho, T⟩

/-- The fund block of the separated case: cost `λ_A I`, risk `γ(σ²I + P^α_t)`, mean map `I`, no fee. -/
def fundLQ (N : ℕ) (lam gam sig2 s2 sb2 rho : ℝ) (T : ℕ) : LQ (Fin N) (Fin N) where
  T := T
  Lam := lam • 1
  S := fun t => gam • (sig2 • 1 + postA N s2 sb2 sig2 t)
  rho := rho
  G := fun _ => 1
  e := 0

/-- Part 1: `P^α_t = p^c_t Π_c + p^r_t Π_r`. The two precisions grow by `1/σ²` per quarter,
`p^c_t ≥ p^r_t` with equality iff `s̄² = 0`, and `p^c_t - p^r_t` decreases to zero like
`Ns̄²σ⁴/(s²(s² + Ns̄²) t²)`. -/
def TwoVariances : Prop :=
  ∀ (N : ℕ) (s2 sb2 sig2 : ℝ), 0 < N → 0 < s2 → 0 ≤ sb2 → 0 < sig2 →
    (∀ t, postA N s2 sb2 sig2 t = pc N s2 sb2 sig2 t • Pc N + pr s2 sig2 t • Pr N) ∧
    (∀ t, 1 / pc N s2 sb2 sig2 (t + 1) = 1 / pc N s2 sb2 sig2 t + 1 / sig2 ∧
      1 / pr s2 sig2 (t + 1) = 1 / pr s2 sig2 t + 1 / sig2) ∧
    (∀ t, pr s2 sig2 t ≤ pc N s2 sb2 sig2 t ∧ (pc N s2 sb2 sig2 t = pr s2 sig2 t ↔ sb2 = 0)) ∧
    Antitone (fun t => pc N s2 sb2 sig2 t - pr s2 sig2 t) ∧
    Filter.Tendsto (fun t : ℕ => (pc N s2 sb2 sig2 t - pr s2 sig2 t) * (t : ℝ) ^ 2) Filter.atTop
      (nhds (N * sb2 * sig2 ^ 2 / (s2 * (s2 + N * sb2))))

/-- Part 2: `Γ^A_t = g^c_t Π_c + g^r_t Π_r` (and `A^A_t = a^c_t Π_c + a^r_t Π_r`), with
`g^c_t ≥ g^r_t` and equality iff `s̄² = 0`. The two speeds converge to the same stationary rate:
as `T → ∞` at fixed `t`, then `t → ∞`, for `ρ ≤ 1`. -/
def TwoSpeeds : Prop :=
  ∀ (N : ℕ) (lam gam sig2 s2 sb2 rho : ℝ) (T : ℕ), 0 < N → 0 < lam → 0 < gam → 0 < sig2 → 0 < s2 →
    0 ≤ sb2 → 0 < rho → rho ≤ 1 →
    (∀ t, t < T →
      (fundLQ N lam gam sig2 s2 sb2 rho T).Gam t =
        (dirC N lam gam sig2 s2 sb2 rho T).g t • Pc N + (dirR lam gam sig2 s2 rho T).g t • Pr N ∧
      (fundLQ N lam gam sig2 s2 sb2 rho T).A t =
        (dirC N lam gam sig2 s2 sb2 rho T).a t • Pc N + (dirR lam gam sig2 s2 rho T).a t • Pr N ∧
      (dirR lam gam sig2 s2 rho T).g t ≤ (dirC N lam gam sig2 s2 sb2 rho T).g t ∧
      ((dirC N lam gam sig2 s2 sb2 rho T).g t = (dirR lam gam sig2 s2 rho T).g t ↔ sb2 = 0)) ∧
    ∃ ac ar : ℕ → ℝ,
      (∀ t, Filter.Tendsto (fun T => lam * gseq lam gam sig2 (s2 + N * sb2) rho T t) Filter.atTop
        (nhds (ac t))) ∧
      (∀ t, Filter.Tendsto (fun T => lam * gseq lam gam sig2 s2 rho T t) Filter.atTop (nhds (ar t))) ∧
      Filter.Tendsto ac Filter.atTop (nhds (astar lam gam sig2 rho)) ∧
      Filter.Tendsto ar Filter.atTop (nhds (astar lam gam sig2 rho))

/-- Part 3, one direction: the weights are positive and sum to 1, and
`σ²/(σ² + p_t) ≤ ℓ_t ≤ 1`. The learning factor is at least 1, and exactly 1 iff `t = T - 1`
(`p` strictly decreases along the filter). -/
def LearningFactor : Prop :=
  ∀ D : Dir, D.Setting → ∀ t, t < D.T →
    (∀ k, k < D.T - t → 0 < D.w k t) ∧ ∑ k ∈ Finset.range (D.T - t), D.w k t = 1 ∧
    D.sig2 / (D.sig2 + D.p t) ≤ D.ell t ∧ D.ell t ≤ 1 ∧
    1 ≤ D.factor t ∧ (D.factor t = 1 ↔ t = D.T - 1)

/-- Part 3, the fund aim, direction by direction:
`aim^A_t = (ℓ^c_t/(γσ²)) α̂^c + (ℓ^r_t/(γσ²)) α̂^r`. The fund Markowitz portfolio is
`α̂^dir/(γ(σ² + p^dir_t))` in each direction, so the aim is the learning factor times the shrunk
Markowitz position, direction by direction. -/
def FundAim : Prop :=
  ∀ (N : ℕ) (lam gam sig2 s2 sb2 rho : ℝ) (T : ℕ), 0 < N → 0 < lam → 0 < gam → 0 < sig2 →
    0 < s2 → 0 ≤ sb2 → 0 < rho → rho ≤ 1 → ∀ t, t < T → ∀ ah : Fin N → ℝ,
      (fundLQ N lam gam sig2 s2 sb2 rho T).aim t ah =
        ((dirC N lam gam sig2 s2 sb2 rho T).ell t / (gam * sig2)) • (Pc N *ᵥ ah) +
          ((dirR lam gam sig2 s2 rho T).ell t / (gam * sig2)) • (Pr N *ᵥ ah) ∧
      (fundLQ N lam gam sig2 s2 sb2 rho T).mkw t ah =
        (1 / (gam * (sig2 + pc N s2 sb2 sig2 t))) • (Pc N *ᵥ ah) +
          (1 / (gam * (sig2 + pr s2 sig2 t))) • (Pr N *ᵥ ah) ∧
      Pc N *ᵥ (fundLQ N lam gam sig2 s2 sb2 rho T).aim t ah =
        (dirC N lam gam sig2 s2 sb2 rho T).factor t • (Pc N *ᵥ (fundLQ N lam gam sig2 s2 sb2 rho T).mkw t ah) ∧
      Pr N *ᵥ (fundLQ N lam gam sig2 s2 sb2 rho T).aim t ah =
        (dirR lam gam sig2 s2 rho T).factor t • (Pr N *ᵥ (fundLQ N lam gam sig2 s2 sb2 rho T).mkw t ah)

/-- Part 4: in the same separated case the ETF exposure is `y_t = (γ(Σ_f + P^λ_t))⁻¹ λ̂_t`, re-set
at every review (speed `I`), with no forward-looking factor. This is claim 030's part 4(a). -/
def CostlessExposure : Prop := Separation

/-- Claim 032, parts 1-4. -/
def statement : Prop := TwoVariances ∧ TwoSpeeds ∧ LearningFactor ∧ FundAim ∧ CostlessExposure

end

end Standalone.M5LearningAimTwoSpeeds

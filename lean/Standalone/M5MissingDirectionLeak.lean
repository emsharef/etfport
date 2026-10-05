import Mathlib.Topology.Instances.Matrix
import Standalone.M5PartialAdjustmentSplit

/-!
# Claim 031: premium beliefs leak into fund choice through the directions ETFs do not span

Statement only; the proof is `Novel/M5MissingDirectionLeakProof.lean`.

M5 in claim 030's reference case with the ETF frictions off (`Λ_E = 0`, `Σ_E = 0`, `c^E = 0`):
`N` funds, `M` ETFs and `K` factors. The ETF loadings `B^E` (`M × K`) have full row rank
(`B^E B^E'` invertible), and their rows span the reachable subspace `L_E ⊆ ℝ^K`. The belief
mean is `m = (λ̂, α̂)`. At review `t`:
- `Σ~_t = Σ_f + P^λ_t` is the predictive factor covariance (`St t`), and `SAt t = Σ_A + P^α_t`.

The claim's objects are defined literally:
- `Π_R = B^E'(B^E B^E')⁻¹B^E` and `Π_U = I - Π_R` are the orthogonal projections onto `L_E` and
  `L_E^⊥`.
- `Σ~_RR⁻¹` is the inverse of `Σ~_RR = Π_R Σ~ Π_R` on `L_E`, `RRinv = B^E'(B^E Σ~ B^E')⁻¹B^E` (zero
  on `L_E^⊥`; the statement checks that it inverts `Σ~_RR` there).
- `Σ~_RU = Π_R Σ~ Π_U`, `Σ~_UR = Π_U Σ~ Π_R` and `Σ~_UU = Π_U Σ~ Π_U`.
- The hedge map is `J = Π_U - Π_R Σ~_RR⁻¹ Σ~_RU`, and the Schur complement is
  `Σ~_{U.R} = Σ~_UU - Σ~_UR Σ~_RR⁻¹ Σ~_RU`.
- The reduced fund moments are `α^red = α̂ + B^A J'λ̂` and `Σ^red = Σ_A + P^α + B^A Σ~_{U.R} B^A'`.

The joint problem is claim 030's problem (`LQ`) in `x = (x^A, x^E)`, with cost `diag(Λ_A, 0)`,
risk `γ(BΣ~_tB' + diag(Σ_A + P^α_t, 0))` and mean map `[[B^A, I]; [B^E, 0]]`. The reduced fund
problem is claim 030's problem in `x^A` with cost `Λ_A`, risk `γΣ^red_t` and the time-varying mean
map `G^red_t = [B^A J_t', I]`. The paper-level steps are those of claim 030: they give the
Bellman verification's martingale hypothesis, and the step to all measurable policies.
-/

namespace Standalone.M5MissingDirectionLeak

open Matrix Standalone.M5PartialAdjustmentSplit

noncomputable section

variable {K N M : ℕ}

/-- `Π_R`, the orthogonal projection onto `L_E = row(B^E)`. -/
def PiR (BE : Matrix (Fin M) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ := BEᵀ * (BE * BEᵀ)⁻¹ * BE

/-- `Π_U = I - Π_R`, onto `L_E^⊥`. -/
def PiU (BE : Matrix (Fin M) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ := 1 - PiR BE

/-- `Σ~_RR⁻¹` on `L_E`, as a `K × K` matrix vanishing on `L_E^⊥`. -/
def RRinv (BE : Matrix (Fin M) (Fin K) ℝ) (Sg : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  BEᵀ * (BE * Sg * BEᵀ)⁻¹ * BE

/-- The hedge map `J = Π_U - Π_R Σ~_RR⁻¹ Σ~_RU`. -/
def Jmap (BE : Matrix (Fin M) (Fin K) ℝ) (Sg : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  PiU BE - PiR BE * RRinv BE Sg * (PiR BE * Sg * PiU BE)

/-- The Schur complement `Σ~_{U.R} = Σ~_UU - Σ~_UR Σ~_RR⁻¹ Σ~_RU`. -/
def Schur (BE : Matrix (Fin M) (Fin K) ℝ) (Sg : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  PiU BE * Sg * PiU BE - (PiU BE * Sg * PiR BE) * RRinv BE Sg * (PiR BE * Sg * PiU BE)

/-- The ETF left inverse `(B^E')⁺ = (B^E B^E')⁻¹ B^E` on `L_E`. -/
def BEplus (BE : Matrix (Fin M) (Fin K) ℝ) : Matrix (Fin M) (Fin K) ℝ := (BE * BEᵀ)⁻¹ * BE

/-- `B = [B^A; B^E]`. -/
def Bmat (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ) :
    Matrix (Fin N ⊕ Fin M) (Fin K) ℝ :=
  Matrix.fromRows BA BE

/-- `Σ^red = Σ_A + P^α + B^A Σ~_{U.R} B^A'`. -/
def SigRed (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ)
    (Sg : Matrix (Fin K) (Fin K) ℝ) (SA : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  SA + BA * Schur BE Sg * BAᵀ

/-- `G^red = [B^A J', I]`, so `G^red m = α̂ + B^A J'λ̂ = α^red`. -/
def Gred (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ)
    (Sg : Matrix (Fin K) (Fin K) ℝ) : Matrix (Fin N) (Fin K ⊕ Fin N) ℝ :=
  Matrix.fromCols (BA * (Jmap BE Sg)ᵀ) 1

/-- The data of claim 031. -/
structure Leak (K N M : ℕ) where
  T : ℕ
  gam : ℝ
  rho : ℝ
  LA : Matrix (Fin N) (Fin N) ℝ
  BA : Matrix (Fin N) (Fin K) ℝ
  BE : Matrix (Fin M) (Fin K) ℝ
  St : ℕ → Matrix (Fin K) (Fin K) ℝ
  SAt : ℕ → Matrix (Fin N) (Fin N) ℝ

namespace Leak

variable (P : Leak K N M)

/-- `γ > 0`, `ρ ∈ [0, 1]`, `Λ_A ≻ 0`, `Σ~_t ≻ 0`, `Σ_A + P^α_t ≻ 0`, `B^E` of full row rank. -/
def Setting : Prop :=
  0 < P.gam ∧ 0 ≤ P.rho ∧ P.rho ≤ 1 ∧ P.LA.PosDef ∧ (∀ t, (P.St t).PosDef) ∧
    (∀ t, (P.SAt t).PosDef) ∧ IsUnit (P.BE * P.BEᵀ).det

/-- The joint problem in `x = (x^A, x^E)`. -/
def joint : LQ (Fin N ⊕ Fin M) (Fin K ⊕ Fin N) where
  T := P.T
  Lam := Matrix.fromBlocks P.LA 0 0 0
  S := fun t => P.gam • (Bmat P.BA P.BE * P.St t * (Bmat P.BA P.BE)ᵀ + Matrix.fromBlocks (P.SAt t) 0 0 0)
  rho := P.rho
  G := fun _ => Matrix.fromBlocks P.BA 1 P.BE 0
  e := 0

/-- The reduced fund problem. -/
def red : LQ (Fin N) (Fin K ⊕ Fin N) where
  T := P.T
  Lam := P.LA
  S := fun t => P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t)
  rho := P.rho
  G := fun t => Gred P.BA P.BE (P.St t)
  e := 0

/-- The same fund problem without the risk term `B^A Σ~_{U.R} B^A'`. -/
def red0 : LQ (Fin N) (Fin K ⊕ Fin N) where
  T := P.T
  Lam := P.LA
  S := fun t => P.gam • P.SAt t
  rho := P.rho
  G := fun t => Gred P.BA P.BE (P.St t)
  e := 0

/-- `M_t` with `k + 1` reviews left: `M_{T-1} = I`, `M_t = I + ρ Λ_A D_{t+1}⁻¹ M_{t+1}`. -/
def MK : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 1
  | k + 1 => 1 + P.rho • (P.LA * (P.red.D (P.T - 1 - k))⁻¹ * MK k)

/-- `M_t`. -/
def Mseq (t : ℕ) : Matrix (Fin N) (Fin N) ℝ := P.MK (P.T - 1 - t)

end Leak

/-- Part 1, coordinates:
- `Π_R` is the orthogonal projection onto `row(B^E)`;
- `x ↦ (y_R, x^A)`, `y_R = Π_R B'x = Π_R B^A'x^A + B^E'x^E`, is a bijection onto `L_E × ℝ^N`, with
  inverse `x^E = (B^E')⁺(y_R - Π_R B^A'x^A)`;
- the total exposure is `y = y_R + Π_U B^A'x^A`;
- `Σ~_RR⁻¹` inverts `Σ~_RR` on `L_E`. -/
def Coordinates : Prop :=
  ∀ (K N M : ℕ) (BA : Matrix (Fin N) (Fin K) ℝ) (BE : Matrix (Fin M) (Fin K) ℝ),
    IsUnit (BE * BEᵀ).det →
    (PiR BE)ᵀ = PiR BE ∧ PiR BE * PiR BE = PiR BE ∧ PiR BE * BEᵀ = BEᵀ ∧ BE * PiU BE = 0 ∧
    (∀ (xA : Fin N → ℝ) (xE : Fin M → ℝ),
      PiR BE *ᵥ ((Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE) = PiR BE *ᵥ (BAᵀ *ᵥ xA) + BEᵀ *ᵥ xE ∧
      BEplus BE *ᵥ (PiR BE *ᵥ ((Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE) - PiR BE *ᵥ (BAᵀ *ᵥ xA)) = xE ∧
      (Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE =
        PiR BE *ᵥ ((Bmat BA BE)ᵀ *ᵥ Sum.elim xA xE) + PiU BE *ᵥ (BAᵀ *ᵥ xA)) ∧
    (∀ (yR : Fin K → ℝ) (xA : Fin N → ℝ), PiR BE *ᵥ yR = yR →
      PiR BE *ᵥ ((Bmat BA BE)ᵀ *ᵥ Sum.elim xA (BEplus BE *ᵥ (yR - PiR BE *ᵥ (BAᵀ *ᵥ xA)))) = yR) ∧
    ∀ Sg : Matrix (Fin K) (Fin K) ℝ, Sg.PosDef →
      RRinv BE Sg * (PiR BE * Sg * PiR BE) = PiR BE ∧ PiR BE * RRinv BE Sg = RRinv BE Sg ∧
      RRinv BE Sg * PiR BE = RRinv BE Sg

/-- Part 2, the ETF exposure: the optimal reachable exposure is
`y_R = Σ~_RR⁻¹[(1/γ)Π_R λ̂ - Σ~_RU B^A' x^A]`, the ETF position is `x^E = (B^E')⁺(y_R - Π_R B^A'x^A)`,
and with `Σ~_RU = 0` the hedge vanishes (`y_R = (1/γ)Σ~_RR⁻¹Π_R λ̂`). -/
def EtfExposure : Prop :=
  ∀ (K N M : ℕ) (P : Leak K N M), P.Setting → ∀ t, t < P.T →
    ∀ (xm : Fin N ⊕ Fin M → ℝ) (m : Fin K ⊕ Fin N → ℝ),
      let x := P.joint.policy t xm m
      let xA : Fin N → ℝ := fun i => x (Sum.inl i)
      let yR := PiR P.BE *ᵥ ((Bmat P.BA P.BE)ᵀ *ᵥ x)
      yR = RRinv P.BE (P.St t) *ᵥ ((1 / P.gam) • (PiR P.BE *ᵥ fun k => m (Sum.inl k)) -
        (PiR P.BE * P.St t * PiU P.BE) *ᵥ (P.BAᵀ *ᵥ xA)) ∧
      (fun j => x (Sum.inr j)) = BEplus P.BE *ᵥ (yR - PiR P.BE *ᵥ (P.BAᵀ *ᵥ xA)) ∧
      (PiR P.BE * P.St t * PiU P.BE = 0 →
        yR = (1 / P.gam) • (RRinv P.BE (P.St t) *ᵥ (PiR P.BE *ᵥ fun k => m (Sum.inl k))))

/-- Part 3, the fund problem: the joint policy's fund positions are the reduced problem's policy
(claim 030's part 3 with mean `α^red_t`, risk `Σ^red_t` and cost `Λ_A`). So they partially adjust
toward the reduced aim, with the fund Markowitz portfolio `(γΣ^red_t)⁻¹(α̂ + B^A J_t'λ̂)`. -/
def FundProblem : Prop :=
  ∀ (K N M : ℕ) (P : Leak K N M), P.Setting →
    P.red.Setting ∧ ∀ t, t < P.T →
      (∀ (xm : Fin N ⊕ Fin M → ℝ) (m : Fin K ⊕ Fin N → ℝ),
        (fun i => P.joint.policy t xm m (Sum.inl i)) = P.red.policy t (fun i => xm (Sum.inl i)) m) ∧
      (∀ (xA : Fin N → ℝ) (m : Fin K ⊕ Fin N → ℝ),
        P.red.policy t xA m = xA + P.red.Gam t *ᵥ (P.red.aim t m - xA)) ∧
      ∀ m : Fin K ⊕ Fin N → ℝ, P.red.mkw t m =
        (P.gam • SigRed P.BA P.BE (P.St t) (P.SAt t))⁻¹ *ᵥ
          ((fun i => m (Sum.inr i)) + P.BA *ᵥ ((Jmap P.BE (P.St t))ᵀ *ᵥ fun k => m (Sum.inl k)))

/-- Part 4, the leak.
- On `L_E^⊥`, `J'v = v`, and the policy's sensitivity to `λ̂` along `v` is `D_t⁻¹ M_t B^A v`.
- Vanishing: if every fund loading is replicable (`Π_U B^A' = 0`), `B^A J' = 0`, the risk term
  vanishes, and the sensitivity to `λ̂` is zero along every direction.
- Converse: the sensitivity is nonzero whenever `M_t` is nonsingular and `B^A v ≠ 0`. `M_t` is
  nonsingular at `t = T - 1`, at every `t` when `T ≤ 3`, and wherever the symmetric part of
  `Λ_A^{-1/2} M_{t+1} Λ_A^{1/2}` is positive definite. In the stationary case
  `M = (I - ρΛ_A D⁻¹)⁻¹` exists and is nonsingular.
- The risk term `B^A Σ~_{U.R} B^A'` is positive semidefinite, and nonzero when some fund loading
  has an unreachable component. `Σ~_{U.R}` is positive definite on `L_E^⊥`, and the risk term
  changes `K_t` at every review. -/
def TheLeak : Prop :=
  (∀ (K M : ℕ) (BE : Matrix (Fin M) (Fin K) ℝ) (Sg : Matrix (Fin K) (Fin K) ℝ) (v : Fin K → ℝ),
    IsUnit (BE * BEᵀ).det → Sg.PosDef → PiR BE *ᵥ v = 0 → (Jmap BE Sg)ᵀ *ᵥ v = v) ∧
  ∀ (K N M : ℕ) (P : Leak K N M), P.Setting →
    (∀ t, t < P.T → ∀ v : Fin K → ℝ, PiR P.BE *ᵥ v = 0 →
      P.red.L t *ᵥ Sum.elim v 0 = (P.red.D t)⁻¹ *ᵥ (P.Mseq t *ᵥ (P.BA *ᵥ v))) ∧
    (PiU P.BE * P.BAᵀ = 0 →
      (∀ Sg : Matrix (Fin K) (Fin K) ℝ, Sg.PosDef → P.BA * (Jmap P.BE Sg)ᵀ = 0) ∧
      (∀ t, SigRed P.BA P.BE (P.St t) (P.SAt t) = P.SAt t) ∧
      ∀ t, t < P.T → ∀ v : Fin K → ℝ, P.red.L t *ᵥ Sum.elim v 0 = 0) ∧
    (∀ t, t < P.T → ∀ v : Fin K → ℝ, PiR P.BE *ᵥ v = 0 → P.BA *ᵥ v ≠ 0 →
      IsUnit (P.Mseq t).det → P.red.L t *ᵥ Sum.elim v 0 ≠ 0) ∧
    (1 ≤ P.T → P.Mseq (P.T - 1) = 1) ∧
    (P.T ≤ 3 → ∀ t, t < P.T → IsUnit (P.Mseq t).det) ∧
    (∀ t, t + 1 < P.T → ∀ R : Matrix (Fin N) (Fin N) ℝ, Rᵀ = R → R * R = P.LA → IsUnit R →
      (R⁻¹ * P.Mseq (t + 1) * R + (R⁻¹ * P.Mseq (t + 1) * R)ᵀ).PosDef → IsUnit (P.Mseq t).det) ∧
    (∀ t, (P.BA * Schur P.BE (P.St t) * P.BAᵀ).PosSemidef ∧
      (∀ x : Fin K → ℝ, PiR P.BE *ᵥ x = 0 → x ≠ 0 → 0 < x ⬝ᵥ (Schur P.BE (P.St t) *ᵥ x)) ∧
      (PiU P.BE * P.BAᵀ ≠ 0 → P.BA * Schur P.BE (P.St t) * P.BAᵀ ≠ 0)) ∧
    (PiU P.BE * P.BAᵀ ≠ 0 → ∀ t, t < P.T → P.red.K t ≠ P.red0.K t)

/-- Part 4, the stationary case: for `D ⪰ Λ_A` strictly (`D - Λ_A ≻ 0`) and `ρ ∈ [0, 1]`,
`M = (I - ρΛ_A D⁻¹)⁻¹` solves `M = I + ρΛ_A D⁻¹ M`, is nonsingular, and `D⁻¹ M B^A v ≠ 0` when
`B^A v ≠ 0`. -/
def Stationary : Prop :=
  ∀ (N K : ℕ) (LA D : Matrix (Fin N) (Fin N) ℝ) (BA : Matrix (Fin N) (Fin K) ℝ) (rho : ℝ),
    LA.PosDef → (D - LA).PosDef → 0 ≤ rho → rho ≤ 1 →
    IsUnit (1 - rho • (LA * D⁻¹)).det ∧
    (1 - rho • (LA * D⁻¹))⁻¹ = 1 + rho • (LA * D⁻¹) * (1 - rho • (LA * D⁻¹))⁻¹ ∧
    IsUnit ((1 - rho • (LA * D⁻¹))⁻¹).det ∧
    ∀ v, BA *ᵥ v ≠ 0 → D⁻¹ *ᵥ ((1 - rho • (LA * D⁻¹))⁻¹ *ᵥ (BA *ᵥ v)) ≠ 0

/-- Part 5, learning: with `Σ~_t = Σ_f + P^λ_t` along the Kalman path (identity observation, noise
`Σ_f`), `Σ~_{U.R,t}` is nonincreasing and tends to the return-only Schur complement `Σ_{f,U.R}`, and
`J_t` tends to the return-only hedge map, whose action on unreachable directions is the identity.
So the mean leak persists while the risk leak loses its estimation part. -/
def Learning : Prop :=
  ∀ (K M : ℕ) (BE : Matrix (Fin M) (Fin K) ℝ) (Sf P0 : Matrix (Fin K) (Fin K) ℝ),
    IsUnit (BE * BEᵀ).det → Sf.PosDef → P0.PosDef →
    (∀ t, (Schur BE (Sf + kal P0 1 Sf t) - Schur BE (Sf + kal P0 1 Sf (t + 1))).PosSemidef) ∧
    Filter.Tendsto (fun t => Schur BE (Sf + kal P0 1 Sf t)) Filter.atTop (nhds (Schur BE Sf)) ∧
    Filter.Tendsto (fun t => Jmap BE (Sf + kal P0 1 Sf t)) Filter.atTop (nhds (Jmap BE Sf)) ∧
    ∀ v, PiR BE *ᵥ v = 0 → (Jmap BE Sf)ᵀ *ᵥ v = v

/-- Claim 031, parts 1-5. -/
def statement : Prop :=
  Coordinates ∧ EtfExposure ∧ FundProblem ∧ TheLeak ∧ Stationary ∧ Learning

end

end Standalone.M5MissingDirectionLeak

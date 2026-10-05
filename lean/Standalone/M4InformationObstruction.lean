import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.EReal.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Standalone.M2ScoreAccounting

/-!
# Claim 014: equal portfolio geometry and covariances can hide different certification information

Statement only; the proof is `Novel/M4InformationObstructionProof.lean`.

**M4** (`model/SPEC.md`) is formalized here from its definitions, reusing claim 003's M2 objects:
`Data`, `ret`, `covariance` (`Σ`), `score` (`Q`), `F`, `E`, `w0` (the normalized incumbent),
`exposure` (`b`) and `maximizers`. It has one active fund, `n` ETFs and two factors. A parameter is
a vector `θ = (λ₁, λ₂, α) ∈ ℝ³`, read as an M2 parameter by `toPar`, and the domain is
`Θ₄ = conv V₄`.
- A public record is `(f, r^A, r^E)`. `hist θ σ` is the history for the scenario sequence
  `σ : Fin N → S`, and `prob θ N A` is its probability under iid draws from `q`.
- The estimator is `θ̂_N`, the mean of `X = (f, r^A - B^A f)`. `Ω` is the covariance of
  `ζ = (z^f, z^A)`, and `Ω†` is its Moore–Penrose inverse (the matrix satisfying the four Penrose
  equations).
- The calibration uses `T_N`, with `t_{N,η}` the first support value of `T_N` whose accumulated
  mass is at least `1 - η`. From it come `A_{N,η}` and `C_N`.
- The comparator objects are `Adv`, `G_*` and `L_N`, with `L_N = -∞` on an empty `C_N`.
- The plug-in selections `ŵ_F` and `v̂_E` are the lexicographically smallest maximizers in the
  coordinate order `(a, p₁, …, p_n)`. The exact gate (`ℓ_N = L_N`) certifies `ŵ_F` when `C_N` is
  nonempty, `ŵ_F ∈ F`, its active holding differs from `a⁻` and `L_N(ŵ_F) > δ_econ`.

**The claim's instances.** Laws I and R share every datum except the ETF shock: one active fund and
one ETF, `B^A = (0, 0)`, `B^E = (1, 0)`, `c^E = 0`, zero rates, `γ = 1`, zero incumbent with cash
one, limits one, and `Θ₄ = conv{θ₊, θ₋}` with `θ± = (1/80, 0, ±1/10)`. The scenarios are
`(s, t, u) ∈ Bool³` (true = +1), each with mass `1/8`, `z^f = 0` and `z^A = s/10`. The ETF shock is
`z^E = t(3-u)/20` in I and `t(3-s)/20` in R.

**Benchmark rules.** A rule maps each full history to a probability measure on actions. This
allows any independent randomization, including randomizing the certified action. The measure
must be carried by the fallback `(0, 1/2)` and the feasible actions with `a > 0`; certifying means
choosing `a > 0`. `certProb` is the probability of certifying, and `falseProb` the probability of
certifying an action with `Adv ≤ 0` (`δ_econ = 0`).
-/

namespace Standalone.M4InformationObstruction

open Matrix MeasureTheory Standalone.M2ScoreAccounting
open scoped Classical

noncomputable section

/-! ### M4 -/

section M4

variable {n : ℕ} {S : Type} [Fintype S]

/-- A parameter vector `θ = (λ₁, λ₂, α)` as an M2 parameter. -/
def toPar (θ : Fin 3 → ℝ) : Params 1 2 := ⟨![θ 0, θ 1], ![θ 2]⟩

/-- The parameter domain `Θ₄ = conv V₄`. -/
def Theta4 (V4 : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) := convexHull ℝ (V4 : Set (Fin 3 → ℝ))

/-- M4's primitive restrictions: `n ∈ {1, 2}`; `V₄` nonempty; a centered finite shock law;
`γ ≥ 0`; nonnegative initial holdings and cash with `W⁻ > 0`; a compliant incumbent; rates in
`[0, 1)`; strictly positive gross returns at every vertex and scenario. -/
def M4Admissible (D : Data 1 n 2 S) (V4 : Finset (Fin 3 → ℝ)) : Prop :=
  (n = 1 ∨ n = 2) ∧ V4.Nonempty ∧
  (∀ s, 0 ≤ D.q s) ∧ ∑ s, D.q s = 1 ∧
  (∀ k, ∑ s, D.q s * D.zf s k = 0) ∧ (∀ j, ∑ s, D.q s * D.zA s j = 0) ∧
  (∀ j, ∑ s, D.q s * D.zE s j = 0) ∧
  0 ≤ D.gamma ∧ (∀ i, 0 ≤ D.x0 i) ∧ 0 ≤ D.h0 ∧ 0 < W0 D ∧ w0 D ∈ F D ∧
  (∀ i, 0 ≤ D.kplus i ∧ D.kplus i < 1 ∧ 0 ≤ D.kminus i ∧ D.kminus i < 1) ∧
  ∀ θ ∈ V4, ∀ s i, 0 < 1 + ret D (toPar θ) s i

/-- One public record: factor returns, active return and ETF returns. -/
structure Record (n : ℕ) where
  f : Fin 2 → ℝ
  rA : ℝ
  rE : Fin n → ℝ

/-- The record of scenario `s` at `θ`: `f = λ + z^f`, `r^A = B^A f + α + z^A`,
`r^E = B^E f - c^E + z^E`. -/
def record (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) (s : S) : Record n :=
  ⟨fun k => (toPar θ).lam k + D.zf s k, ret D (toPar θ) s (Sum.inl 0),
    fun j => ret D (toPar θ) s (Sum.inr j)⟩

/-- The history of the scenario sequence `σ`. -/
def hist {N : ℕ} (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) (σ : Fin N → S) : Fin N → Record n :=
  fun l => record D θ (σ l)

/-- The iid mass `Π_l q_{σ_l}` of a scenario sequence. -/
def mass {N : ℕ} (D : Data 1 n 2 S) (σ : Fin N → S) : ℝ := ∏ l, D.q (σ l)

/-- `P_θ(H_N ∈ A)`. -/
def prob (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) (N : ℕ) (A : Set (Fin N → Record n)) : ℝ :=
  ∑ σ : Fin N → S, if hist D θ σ ∈ A then mass D σ else 0

/-- The observable `X = (f, r^A - B^A f)`. -/
def X (D : Data 1 n 2 S) (r : Record n) : Fin 3 → ℝ :=
  ![r.f 0, r.f 1, r.rA - (D.BA *ᵥ r.f) 0]

/-- The sample mean `θ̂_N` (not projected onto `Θ₄`). -/
def thetaHat {N : ℕ} (D : Data 1 n 2 S) (H : Fin N → Record n) : Fin 3 → ℝ :=
  (1 / (N : ℝ)) • ∑ l, X D (H l)

/-- `ζ_s = (z^f_s, z^A_s)`. -/
def zeta (D : Data 1 n 2 S) (s : S) : Fin 3 → ℝ := ![D.zf s 0, D.zf s 1, D.zA s 0]

/-- `Ω = Σ_s q_s ζ_s ζ_s'`. -/
def Omega (D : Data 1 n 2 S) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ s, D.q s * (zeta D s i * zeta D s j)

/-- The four Penrose equations. -/
def IsMoorePenrose (A G : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  A * G * A = A ∧ G * A * G = G ∧ (A * G)ᵀ = A * G ∧ (G * A)ᵀ = G * A

/-- The Moore–Penrose inverse `A†`. -/
def pinv (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Classical.epsilon (IsMoorePenrose A)

/-- The sampling error `e_N = (1/N) Σ_l ζ_{σ_l}`. -/
def errN {N : ℕ} (D : Data 1 n 2 S) (σ : Fin N → S) : Fin 3 → ℝ :=
  (1 / (N : ℝ)) • ∑ l, zeta D (σ l)

/-- `T_N = N e_N' Ω† e_N`. -/
def TN {N : ℕ} (D : Data 1 n 2 S) (σ : Fin N → S) : ℝ :=
  N * (errN D σ ⬝ᵥ (pinv (Omega D) *ᵥ errN D σ))

/-- `t_{N,η}`: the first support value of `T_N` (over positive-mass histories) whose accumulated
mass is at least `1 - η`. -/
def tcrit (D : Data 1 n 2 S) (N : ℕ) (η : ℝ) : ℝ :=
  sInf {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
    1 - η ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0}

/-- `A_{N,η} = {e ∈ Im Ω : N e' Ω† e ≤ t_{N,η}}`. -/
def Aset (D : Data 1 n 2 S) (N : ℕ) (η : ℝ) : Set (Fin 3 → ℝ) :=
  {e | e ∈ Set.range (Omega D).mulVec ∧ N * (e ⬝ᵥ (pinv (Omega D) *ᵥ e)) ≤ tcrit D N η}

/-- `C_N = Θ₄ ∩ {θ̂_N - e : e ∈ A_{N,η}}`, as a function of the estimate. -/
def Cset (D : Data 1 n 2 S) (V4 : Finset (Fin 3 → ℝ)) (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ) :
    Set (Fin 3 → ℝ) :=
  Theta4 V4 ∩ {θ | ∃ e ∈ Aset D N η, θ = th - e}

/-- `sup_{v ∈ E} Q(v; θ)`. -/
def etfSup (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) : ℝ := sSup ((fun v => score D v (toPar θ)) '' E D)

/-- `Adv(w; θ) = Q(w; θ) - sup_E Q(·; θ)`. -/
def Adv (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  score D w (toPar θ) - etfSup D θ

/-- `G_*(θ) = sup_F Q(·; θ) - sup_E Q(·; θ)`. -/
def Gstar (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) : ℝ :=
  sSup ((fun w => score D w (toPar θ)) '' F D) - etfSup D θ

/-- `L_N(w) = inf_{θ ∈ C_N} Adv(w; θ)`, and `-∞` when `C_N` is empty. -/
def LN (D : Data 1 n 2 S) (V4 : Finset (Fin 3 → ℝ)) (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ)
    (w : Inst 1 n → ℝ) : EReal :=
  if Cset D V4 N η th = ∅ then ⊥ else ⨅ θ ∈ Cset D V4 N η th, ((Adv D w θ : ℝ) : EReal)

/-- Coordinate order `(a, p₁, …, p_n)`. -/
def lexIdx : Inst 1 n → ℕ := Sum.elim (fun _ => 0) (fun j => j.val + 1)

/-- Lexicographic order on holdings in the coordinate order `(a, p₁, …, p_n)`. -/
def LexLE (w v : Inst 1 n → ℝ) : Prop :=
  w = v ∨ ∃ i, (∀ j, lexIdx j < lexIdx i → w j = v j) ∧ w i < v i

/-- The lexicographically smallest element of `M` (M4's tie-break). -/
def lexSel (M : Set (Inst 1 n → ℝ)) : Inst 1 n → ℝ :=
  Classical.epsilon (fun w => w ∈ M ∧ ∀ v ∈ M, LexLE w v)

/-- The plug-in full candidate `ŵ_F`. -/
def wHatF (D : Data 1 n 2 S) (th : Fin 3 → ℝ) : Inst 1 n → ℝ :=
  lexSel (maximizers (fun w => score D w (toPar th)) (F D))

/-- The plug-in ETF-only fallback `v̂_E`. -/
def vHatE (D : Data 1 n 2 S) (th : Fin 3 → ℝ) : Inst 1 n → ℝ :=
  lexSel (maximizers (fun w => score D w (toPar th)) (E D))

/-- The exact M4 gate (`ℓ_N = L_N`) certifies at estimate `th`. -/
def gateCert (D : Data 1 n 2 S) (V4 : Finset (Fin 3 → ℝ)) (N : ℕ) (η δ : ℝ) (th : Fin 3 → ℝ) :
    Prop :=
  (Cset D V4 N η th).Nonempty ∧ wHatF D th ∈ F D ∧ wHatF D th (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧
    ((δ : ℝ) : EReal) < LN D V4 N η th (wHatF D th)

/-- The action the gate implements: `ŵ_F` if certified, else `v̂_E`. -/
def gateAct (D : Data 1 n 2 S) (V4 : Finset (Fin 3 → ℝ)) (N : ℕ) (η δ : ℝ) (th : Fin 3 → ℝ) :
    Inst 1 n → ℝ :=
  if gateCert D V4 N η δ th then wHatF D th else vHatE D th

/-- The covariance of one public record `(f, r^A, r^E)` at `θ`. -/
def obsCov (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) : Matrix (Fin 2 ⊕ Inst 1 n) (Fin 2 ⊕ Inst 1 n) ℝ :=
  let v : S → Fin 2 ⊕ Inst 1 n → ℝ := fun s => Sum.elim (record D θ s).f (ret D (toPar θ) s)
  let m : Fin 2 ⊕ Inst 1 n → ℝ := fun i => ∑ s, D.q s * v s i
  fun i j => ∑ s, D.q s * ((v s i - m i) * (v s j - m j))

end M4

/-! ### The two laws -/

/-- A sign `±1`. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

/-- Scenario labels `(s, t, u)`. -/
abbrev Sc := Bool × Bool × Bool

/-- The common data, given the ETF shock. -/
def baseData (zE : Sc → Fin 1 → ℝ) : Data 1 1 2 Sc where
  BA := 0
  BE := !![1, 0]
  cE := 0
  kplus := 0
  kminus := 0
  gamma := 1
  q := fun _ => 1 / 8
  zf := 0
  zA := fun x => ![sg x.1 / 10]
  zE := zE
  x0 := 0
  h0 := 1
  wbar := fun _ => 1

/-- Law I: `z^E = t(3-u)/20`. -/
def dataI : Data 1 1 2 Sc := baseData fun x => ![sg x.2.1 * (3 - sg x.2.2) / 20]

/-- Law R: `z^E = t(3-s)/20`. -/
def dataR : Data 1 1 2 Sc := baseData fun x => ![sg x.2.1 * (3 - sg x.1) / 20]

/-- `θ₊ = (1/80, 0, 1/10)`. -/
def thetaPlus : Fin 3 → ℝ := ![1 / 80, 0, 1 / 10]

/-- `θ₋ = (1/80, 0, -1/10)`. -/
def thetaMinus : Fin 3 → ℝ := ![1 / 80, 0, -1 / 10]

/-- `V₄ = {θ₊, θ₋}`. -/
def V4 : Finset (Fin 3 → ℝ) := {thetaPlus, thetaMinus}

/-- The holding `(a, p)`. -/
def act (a p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => a) (fun _ => p)

/-- `w_A = (1, 0)`. -/
def wA : Inst 1 1 → ℝ := act 1 0

/-- The fallback `(0, 1/2)`. -/
def wE : Inst 1 1 → ℝ := act 0 (1 / 2)

/-! ### Benchmark rules -/

/-- A randomized rule: a probability measure on actions for each full history. -/
structure Rule (N : ℕ) where
  kernel : (Fin N → Record 1) → Measure (Inst 1 1 → ℝ)
  isProb : ∀ H, IsProbabilityMeasure (kernel H)

/-- The rule either certifies a feasible action with `a > 0` or falls back to `(0, 1/2)`. -/
def Admits (D : Data 1 1 2 Sc) {N : ℕ} (ρ : Rule N) : Prop :=
  ∀ H, ρ.kernel H {w | w ≠ wE ∧ ¬ (w ∈ F D ∧ 0 < w (Sum.inl 0))} = 0

/-- The probability of certifying at `θ`. -/
def certProb (D : Data 1 1 2 Sc) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : Rule N) : ℝ :=
  ∑ σ : Fin N → Sc, mass D σ * (ρ.kernel (hist D θ σ) {w | 0 < w (Sum.inl 0)}).toReal

/-- The probability of certifying an action with `Adv(·; θ) ≤ 0` at `θ`. -/
def falseProb (D : Data 1 1 2 Sc) (θ : Fin 3 → ℝ) {N : ℕ} (ρ : Rule N) : ℝ :=
  ∑ σ : Fin N → Sc, mass D σ *
    (ρ.kernel (hist D θ σ) {w | 0 < w (Sum.inl 0) ∧ Adv D w θ ≤ 0}).toReal

/-- Uniform validity over `Θ₄` at level `η`. -/
def Valid (D : Data 1 1 2 Sc) (N : ℕ) (η : ℝ) (ρ : Rule N) : Prop :=
  ∀ θ ∈ Theta4 V4, falseProb D θ ρ ≤ η

/-- The attainable certification probabilities at `θ₊`. -/
def Powers (D : Data 1 1 2 Sc) (N : ℕ) (η : ℝ) : Set ℝ :=
  {c | ∃ ρ : Rule N, Admits D ρ ∧ Valid D N η ρ ∧ c = certProb D thetaPlus ρ}

/-- The rule certifies only `w_A`. -/
def CertifiesOnlyWA {N : ℕ} (ρ : Rule N) : Prop :=
  ∀ H, ρ.kernel H {w | w ≠ wA ∧ w ≠ wE} = 0

/-! ### The claim -/

/-- Part 1: both laws are admissible with the same `Ω`, `Σ`, marginals, public-record
covariance, `F`, `E`, `b`, `Q`, `G_*` and `θ̂_N` law; and the explicit objects. -/
def SameEconomics : Prop :=
  M4Admissible dataI V4 ∧ M4Admissible dataR V4 ∧
  Theta4 V4 = {θ | θ 0 = 1 / 80 ∧ θ 1 = 0 ∧ -1 / 10 ≤ θ 2 ∧ θ 2 ≤ 1 / 10} ∧
  Omega dataI = !![0, 0, 0; 0, 0, 0; 0, 0, 1 / 100] ∧ Omega dataR = Omega dataI ∧
  covariance dataI = Matrix.diagonal (act (1 / 100) (1 / 40)) ∧ covariance dataR = covariance dataI ∧
  (∀ θ i x, (∑ s, if ret dataI (toPar θ) s i = x then dataI.q s else 0)
    = ∑ s, if ret dataR (toPar θ) s i = x then dataR.q s else 0) ∧
  (∀ θ, obsCov dataI θ = obsCov dataR θ) ∧
  F dataI = F dataR ∧ E dataI = E dataR ∧
  (∀ w, exposure dataI w = exposure dataR w) ∧ (∀ w θ, score dataI w θ = score dataR w θ) ∧
  (∀ θ, Gstar dataI θ = Gstar dataR θ) ∧
  (∀ θ N (A : Set (Fin 3 → ℝ)),
    prob dataI θ N {H | thetaHat dataI H ∈ A} = prob dataR θ N {H | thetaHat dataR H ∈ A}) ∧
  ∀ D ∈ ({dataI, dataR} : Set (Data 1 1 2 Sc)),
    F D = {w | 0 ≤ w (Sum.inl 0) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inl 0) + w (Sum.inr 0) ≤ 1} ∧
    E D = {w | w (Sum.inl 0) = 0 ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 1} ∧
    (∀ θ ∈ Theta4 V4, ∀ w, score D w (toPar θ) = w (Sum.inl 0) * θ 2 + w (Sum.inr 0) / 80
      - w (Sum.inl 0) ^ 2 / 200 - w (Sum.inr 0) ^ 2 / 80) ∧
    (∀ θ ∈ Theta4 V4, etfSup D θ = 1 / 320 ∧
      maximizers (fun v => score D v (toPar θ)) (E D) = {wE}) ∧
    (∀ w ∈ F D, 0 < w (Sum.inl 0) → Adv D w thetaMinus < 0) ∧ Gstar D thetaMinus = 0 ∧
    maximizers (fun w => score D w (toPar thetaPlus)) (F D) = {wA} ∧
    Adv D wA thetaPlus = 147 / 1600 ∧ Gstar D thetaPlus = 147 / 1600 ∧
    ∀ α : ℝ, Adv D wA ![1 / 80, 0, α] = α - 13 / 1600

/-- Part 2: the sharp full-history benchmark for every `N_obs ≥ 1` and `η ∈ (0, 1)`. -/
def SharpBenchmark : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ η : ℝ, 0 < η → η < 1 →
    IsGreatest (Powers dataI N η) (min 1 (1 - (1 / 2) ^ N + η)) ∧
    IsGreatest (Powers dataR N η) 1 ∧
    (∃ ρ : Rule N, Admits dataI ρ ∧ Valid dataI N η ρ ∧ CertifiesOnlyWA ρ ∧
      certProb dataI thetaPlus ρ = min 1 (1 - (1 / 2) ^ N + η)) ∧
    (∃ ρ : Rule N, Admits dataR ρ ∧ CertifiesOnlyWA ρ ∧
      (∀ θ ∈ Theta4 V4, falseProb dataR θ ρ = 0) ∧ certProb dataR thetaPlus ρ = 1) ∧
    ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ((∃ c ∈ Powers dataI N η, 1 - β ≤ c) ↔ (1 / 2 : ℝ) ^ N ≤ η + β)

/-- Part 3: the exact M4 gate (`δ_econ = 0`) is the same function of `θ̂_N` in both laws, so its
law agrees at every `θ` and `N_obs`; at `N_obs = 1` and `θ₊` it certifies with probability `1/2`
in both, against benchmarks `3/4` (I) and `1` (R) at `η = 1/4`. -/
def GateDiscards : Prop :=
  (∀ N η th, Cset dataI V4 N η th = Cset dataR V4 N η th ∧
    (∀ w, LN dataI V4 N η th w = LN dataR V4 N η th w) ∧
    wHatF dataI th = wHatF dataR th ∧ vHatE dataI th = vHatE dataR th ∧
    (gateCert dataI V4 N η 0 th ↔ gateCert dataR V4 N η 0 th) ∧
    gateAct dataI V4 N η 0 th = gateAct dataR V4 N η 0 th) ∧
  (∀ N (H : Fin N → Record 1), thetaHat dataI H = thetaHat dataR H) ∧
  (∀ N η θ (g : Prop → (Inst 1 1 → ℝ) → Prop),
    prob dataI θ N {H | g (gateCert dataI V4 N η 0 (thetaHat dataI H))
      (gateAct dataI V4 N η 0 (thetaHat dataI H))}
    = prob dataR θ N {H | g (gateCert dataR V4 N η 0 (thetaHat dataR H))
      (gateAct dataR V4 N η 0 (thetaHat dataR H))}) ∧
  (∀ η : ℝ, 0 < η → η < 1 →
    prob dataI thetaPlus 1 {H | gateCert dataI V4 1 η 0 (thetaHat dataI H)} = 1 / 2 ∧
    prob dataR thetaPlus 1 {H | gateCert dataR V4 1 η 0 (thetaHat dataR H)} = 1 / 2) ∧
  IsGreatest (Powers dataI 1 (1 / 4)) (3 / 4) ∧ IsGreatest (Powers dataR 1 (1 / 4)) 1

/-- Claim 014, all parts. -/
def statement : Prop := SameEconomics ∧ SharpBenchmark ∧ GateDiscards

end

end Standalone.M4InformationObstruction

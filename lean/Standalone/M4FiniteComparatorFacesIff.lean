import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Bounded
import Standalone.M2ActionClasses
import Standalone.M4CurvatureCertificate
import Standalone.M4CurvedEntryRate

/-!
# Claim 020: the finite comparator faces of the funded ETF class, and when they are exact

Statement only; the proof is `Novel/M4FiniteComparatorFacesIffProof.lean`.

The formal M4 objects are those of `Standalone/M4InformationObstruction.lean` (`M4Admissible`,
`Theta4`, `Omega`, `pinv`, `tcrit`, `Aset`, `Cset`, `LN`, `etfSup`, `Adv`, `Gstar`, `wHatF`,
`vHatE`, `toPar`, `sg`) and claim 003's (`F`, `E`, `score`, `covariance`, `tau`, `w0`, `k0`,
`maximizers`). The mean-exposure map `Aw` (`A w = (b(w), a)`) is claim 018's, and claim 017's
family is `Standalone.M4CurvedEntryRate.data`.

- `cellF D σ` is the cost-sign cell `F_σ = {w ∈ F : σᵢ (wᵢ - w⁻ᵢ) ≥ 0}` and `cellE D ρ` its ETF
  analogue `E_ρ`, with sign `true = +1`.
- `VertF` and `VertE` are the unions of the cells' extreme points. `mv D v w θ` is the
  single-comparator contrast `m_v(w; θ) = Q(w; θ) - Q(v; θ)`.
- `contrasts D` is the finite contrast set `{A(u - v) : u ∈ Vert(F), v ∈ Vert(E)}`.
- `cF` is the `θ`-free part `c(w) = -p'c^E - τ(w - w⁻)` of a linear (`γ = 0`) score.

Infima over parameter sets are taken in `EReal`, so they are `+∞` over an empty set and `-∞` when
unbounded below. Every part lists only the hypotheses its proof uses.
-/

namespace Standalone.M4FiniteComparatorFacesIff

open Matrix Standalone.M2ScoreAccounting Standalone.M4InformationObstruction
open Standalone.M4CurvatureCertificate (Aw)
open Standalone.M4JointDirectionalRate (InKJ)
open scoped Classical

noncomputable section

variable {n : ℕ} {S : Type} [Fintype S]

/-- The cost-sign cell `F_σ`. -/
def cellF (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) : Set (Inst 1 n → ℝ) :=
  {w | w ∈ F D ∧ ∀ i, 0 ≤ sg (σ i) * (w i - w0 D i)}

/-- The cost-sign cell `E_ρ`. -/
def cellE (D : Data 1 n 2 S) (ρ : Fin n → Bool) : Set (Inst 1 n → ℝ) :=
  {w | w ∈ E D ∧ ∀ j, 0 ≤ sg (ρ j) * (w (Sum.inr j) - w0 D (Sum.inr j))}

/-- `Vert(F)`: the extreme points of all cells of `F`. -/
def VertF (D : Data 1 n 2 S) : Set (Inst 1 n → ℝ) := ⋃ σ, Set.extremePoints ℝ (cellF D σ)

/-- `Vert(E)`: the extreme points of all cells of `E`. -/
def VertE (D : Data 1 n 2 S) : Set (Inst 1 n → ℝ) := ⋃ ρ, Set.extremePoints ℝ (cellE D ρ)

/-- The single-comparator contrast `m_v(w; θ) = Q(w; θ) - Q(v; θ)`. -/
def mv (D : Data 1 n 2 S) (v w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  score D w (toPar θ) - score D v (toPar θ)

/-- The finite contrast set `{A(u - v) : u ∈ Vert(F), v ∈ Vert(E)}`. -/
def contrasts (D : Data 1 n 2 S) : Set (Fin 3 → ℝ) :=
  {d | ∃ u ∈ VertF D, ∃ v ∈ VertE D, d = Aw D (u - v)}

/-- `c(w) = -p'c^E - τ(w - w⁻)`. -/
def cF (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) : ℝ := -(etf w ⬝ᵥ D.cE) - tau D (w - w0 D)

/-- The closed-form certificate `ℓ_N(w) = min_v [m_v(w; θ̂) - r_N √(d_v'Ω d_v)]`, `d_v = A(w - v)`. -/
def ellF (D : Data 1 n 2 S) (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ) (w : Inst 1 n → ℝ) : EReal :=
  ⨅ v ∈ VertE D, ((mv D v w th - Real.sqrt (tcrit D N η / N) *
    Real.sqrt (Aw D (w - v) ⬝ᵥ (Omega D *ᵥ Aw D (w - v))) : ℝ) : EReal)

/-- `ℓ_D(w) = min_v [inf I_{A(w - v)} + c(w) - c(v)]` for intervals (any sets) `I_d`. -/
def ellD (D : Data 1 n 2 S) (I : (Fin 3 → ℝ) → Set ℝ) (w : Inst 1 n → ℝ) : EReal :=
  ⨅ v ∈ VertE D, ((⨅ x ∈ I (Aw D (w - v)), (x : EReal)) + ((cF D w - cF D v : ℝ) : EReal))

/-- `H_{uv}(δ_e) = {θ : m_v(u; θ) ≤ δ_e}`. -/
def Hs (D : Data 1 n 2 S) (u v : Inst 1 n → ℝ) (δe : ℝ) : Set (Fin 3 → ℝ) :=
  {θ | mv D v u θ ≤ δe}

/-- `AX-05` (i), the linear-programming vertex theorem's finiteness and count, as cited
(`bertsimas1997introduction` Theorem 2.3, Corollary 2.1): a nonempty bounded polyhedron
`{x ∈ ℝ^ι : g_l'x ≤ h_l}` has finitely many extreme points, at most `binom(|Λ|, |ι|)`. It is not
proved here. It enters as the hypothesis structure `Upstream.LP.LPVertex` (with its instance in
`Upstream/LPVertex.lean`); this proposition is that structure's field for every constraint system,
and the parts that use it take it as a hypothesis. -/
def AX05i : Prop :=
  ∀ (ι Λ : Type) [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ),
    {x : ι → ℝ | ∀ l, g l ⬝ᵥ x ≤ h l}.Nonempty →
    Bornology.IsBounded {x : ι → ℝ | ∀ l, g l ⬝ᵥ x ≤ h l} →
    (Set.extremePoints ℝ {x : ι → ℝ | ∀ l, g l ⬝ᵥ x ≤ h l}).Finite ∧
      (Set.extremePoints ℝ {x : ι → ℝ | ∀ l, g l ⬝ᵥ x ≤ h l}).ncard
        ≤ (Fintype.card Λ).choose (Fintype.card ι)

/-- Part 1: every cell is a compact convex polyhedron containing `w⁻` (for `F` with `3(1+n)+1`
halfspaces, for `E`, given a compliant incumbent, `a = a⁻` and `3n+1` halfspaces in the ETF
coordinates); the cells cover
`F` and `E`; `Vert(F)` and `Vert(E)` are finite with the crude counts; they depend only on
`(w̄, w⁻, k⁻, κ⁺, κ⁻)`; and for one ETF `Vert(E)` is exactly the three listed holdings. The
finiteness and the counts are by `AX-05` (i), taken as the hypothesis `AX05i`. -/
def FacesFinite : Prop :=
  (∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S),
    (∀ σ, IsCompact (cellF D σ) ∧ Convex ℝ (cellF D σ) ∧
      ∃ (g : Fin (3 * (n + 1) + 1) → Inst 1 n → ℝ) (h : Fin (3 * (n + 1) + 1) → ℝ),
        cellF D σ = {w | ∀ l, g l ⬝ᵥ w ≤ h l}) ∧
    (∀ ρ, IsCompact (cellE D ρ) ∧ Convex ℝ (cellE D ρ) ∧
      (w0 D ∈ F D → ∃ (g : Fin (3 * n + 1) → Fin n → ℝ) (h : Fin (3 * n + 1) → ℝ),
        cellE D ρ = {w | w (Sum.inl 0) = w0 D (Sum.inl 0) ∧ ∀ l, g l ⬝ᵥ etf w ≤ h l})) ∧
    (w0 D ∈ F D → (∀ σ, w0 D ∈ cellF D σ) ∧ ∀ ρ, w0 D ∈ cellE D ρ) ∧
    F D = ⋃ σ, cellF D σ ∧ E D = ⋃ ρ, cellE D ρ ∧
    (AX05i → (VertF D).Finite ∧ (VertF D).ncard ≤ 2 ^ (n + 1) * (3 * n + 4).choose (n + 1) ∧
      (VertE D).Finite ∧ (VertE D).ncard ≤ 2 ^ n * (3 * n + 1).choose n) ∧
    ∀ D' : Data 1 n 2 S, D'.wbar = D.wbar → w0 D' = w0 D → k0 D' = k0 D →
      D'.kplus = D.kplus → D'.kminus = D.kminus → VertF D' = VertF D ∧ VertE D' = VertE D) ∧
  ∀ (S : Type) [Fintype S] (D : Data 1 1 2 S), w0 D ∈ F D →
    0 ≤ D.kplus (Sum.inr 0) → D.kminus (Sum.inr 0) ≤ 1 →
    VertE D = {Sum.elim (fun _ => w0 D (Sum.inl 0)) (fun _ => 0),
      Sum.elim (fun _ => w0 D (Sum.inl 0)) (fun _ => w0 D (Sum.inr 0)),
      Sum.elim (fun _ => w0 D (Sum.inl 0)) (fun _ => w0 D (Sum.inr 0) +
        min (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0)) (k0 D / (1 + D.kplus (Sum.inr 0))))}

/-- Part 2, `γ = 0`: the maxima of both classes are attained on their faces; `Adv = min_v m_v`
with each `m_v` affine in `θ`; `G_* = max_u Adv(u; ·)`; the exchange of infima for every parameter
set; and M4's lexicographic plug-in selections are faces at every estimate. -/
def LinearReduction : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S), D.gamma = 0 → w0 D ∈ F D →
    (∀ θ : Fin 3 → ℝ,
      IsGreatest ((fun v => score D v (toPar θ)) '' VertE D) (etfSup D θ) ∧
      IsGreatest ((fun u => score D u (toPar θ)) '' VertF D)
        (sSup ((fun w => score D w (toPar θ)) '' F D)) ∧
      IsGreatest ((fun u => Adv D u θ) '' VertF D) (Gstar D θ)) ∧
    (∀ (θ : Fin 3 → ℝ) (w : Inst 1 n → ℝ),
      IsLeast ((fun v => mv D v w θ) '' VertE D) (Adv D w θ)) ∧
    (∀ v w : Inst 1 n → ℝ, ∃ (a : Fin 3 → ℝ) (b : ℝ), ∀ θ, mv D v w θ = a ⬝ᵥ θ + b) ∧
    (∀ (C : Set (Fin 3 → ℝ)) (w : Inst 1 n → ℝ),
      ⨅ θ ∈ C, ((Adv D w θ : ℝ) : EReal) = ⨅ v ∈ VertE D, ⨅ θ ∈ C, ((mv D v w θ : ℝ) : EReal)) ∧
    (∀ th : Fin 3 → ℝ, wHatF D th ∈ VertF D ∧ vHatE D th ∈ VertE D)

/-- Part 2, the error set (any admissible M4 instance, any `γ`): the closed form of the infimum of
each contrast over `θ̂ - A_{N,η}` with its attainment, `C_N` compact and convex, and for `γ = 0`,
`L_N = min_v inf_{C_N} m_v` and `ℓ_N ≤ L_N` for nonempty `C_N`. -/
def ErrorSet : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)),
    M4Admissible D V → ∀ (N : ℕ) (η : ℝ), 0 < N →
    (∀ (th : Fin 3 → ℝ) (v w : Inst 1 n → ℝ),
      let d := Aw D (w - v)
      let r := Real.sqrt (tcrit D N η / N)
      ⨅ e ∈ Aset D N η, ((mv D v w (th - e) : ℝ) : EReal)
        = ((mv D v w th - r * Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d)) : ℝ) : EReal) ∧
      (0 < d ⬝ᵥ (Omega D *ᵥ d) →
        (r / Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) • (Omega D *ᵥ d) ∈ Aset D N η ∧
        mv D v w (th - (r / Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) • (Omega D *ᵥ d))
          = mv D v w th - r * Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) ∧
      (d ⬝ᵥ (Omega D *ᵥ d) = 0 → (0 : Fin 3 → ℝ) ∈ Aset D N η)) ∧
    (∀ th : Fin 3 → ℝ, IsCompact (Cset D V N η th) ∧ Convex ℝ (Cset D V N η th)) ∧
    (D.gamma = 0 → ∀ (th : Fin 3 → ℝ) (w : Inst 1 n → ℝ), (Cset D V N η th).Nonempty →
      LN D V N η th w = ⨅ v ∈ VertE D, ⨅ θ ∈ Cset D V N η th, ((mv D v w θ : ℝ) : EReal) ∧
      ellF D N η th w ≤ LN D V N η th w)

/-- Part 3, `γ = 0`. (a) If every contrast `d ∈ D` has `d'θ_* ∈ I_d`, then `θ_* ∈ C_D`, and for
every estimate the plug-in candidate satisfies `ℓ_D(ŵ_F) ≤ inf_{C_D} Adv(ŵ_F; ·) ≤ Adv(ŵ_F; θ_*)`;
certification (`a ≠ a⁻` and `ℓ_D > δ_econ`) implies `Adv(ŵ_F; θ_*) > δ_econ`. (b) `Null(δ_e)` is
the intersection over `Vert(F)` of unions over `Vert(E)` of the sets `H_{uv}`, each a closed
halfspace, all of `ℝ³` or empty; it is a finite union of polyhedra (given `AX-05` (i), which makes
the faces finite); and every function `ψ` obeys
`inf_{Null} ψ ≥ min_v inf_{H_{uv}} ψ` for every `u ∈ Vert(F)`. -/
def FiniteContrasts : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S), D.gamma = 0 → w0 D ∈ F D →
    (∀ (I : (Fin 3 → ℝ) → Set ℝ) (th θs : Fin 3 → ℝ) (δe : ℝ),
      (∀ d ∈ contrasts D, d ⬝ᵥ θs ∈ I d) →
      θs ∈ {θ | ∀ d ∈ contrasts D, d ⬝ᵥ θ ∈ I d} ∧
      ellD D I (wHatF D th)
        ≤ ⨅ θ ∈ {θ | ∀ d ∈ contrasts D, d ⬝ᵥ θ ∈ I d}, ((Adv D (wHatF D th) θ : ℝ) : EReal) ∧
      ⨅ θ ∈ {θ | ∀ d ∈ contrasts D, d ⬝ᵥ θ ∈ I d}, ((Adv D (wHatF D th) θ : ℝ) : EReal)
        ≤ ((Adv D (wHatF D th) θs : ℝ) : EReal) ∧
      (wHatF D th (Sum.inl 0) ≠ w0 D (Sum.inl 0) → ((δe : ℝ) : EReal) < ellD D I (wHatF D th) →
        δe < Adv D (wHatF D th) θs)) ∧
    ∀ δe : ℝ,
      {θ | Gstar D θ ≤ δe} = ⋂ u ∈ VertF D, ⋃ v ∈ VertE D, Hs D u v δe ∧
      (∀ u v, (∃ a : Fin 3 → ℝ, a ≠ 0 ∧ ∃ b, Hs D u v δe = {θ | a ⬝ᵥ θ ≤ b}) ∨
        Hs D u v δe = Set.univ ∨ Hs D u v δe = ∅) ∧
      (AX05i → ∃ (ι : Type) (_ : Finite ι) (κ : ι → Type) (_ : ∀ i, Finite (κ i))
        (a : ∀ i, κ i → Fin 3 → ℝ) (b : ∀ i, κ i → ℝ),
        {θ | Gstar D θ ≤ δe} = ⋃ i, {θ | ∀ k, a i k ⬝ᵥ θ ≤ b i k}) ∧
      ∀ (ψ : (Fin 3 → ℝ) → EReal), ∀ u ∈ VertF D,
        ⨅ v ∈ VertE D, ⨅ θ ∈ Hs D u v δe, ψ θ ≤ ⨅ θ ∈ {θ | Gstar D θ ≤ δe}, ψ θ

/-- Part 4, `γ > 0` and positive-definite `Σ`: the ETF optimizer is unique; for every nonempty
finite `S ⊆ E` the deficit `V_E - max_S Q` is at least `(γ/2) min_S ‖v - v_E‖²_Σ`; the
finite-comparator contrast exceeds `Adv` by exactly the deficit; and a deficit at most `δ_e` on
`Θ₄` forces every `v_E(θ)`, `θ ∈ Θ₄`, within `Σ`-distance `√(2δ_e/γ)` of `S`. -/
def CurvatureDeficit : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)),
    Standalone.M2ActionClasses.RatesNonneg D → (∀ s, 0 ≤ D.q s) → w0 D ∈ F D → 0 < D.gamma →
    (∀ z : Inst 1 n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (covariance D *ᵥ z)) →
    ∀ (Sf : Finset (Inst 1 n → ℝ)) (hS : Sf.Nonempty), (↑Sf : Set (Inst 1 n → ℝ)) ⊆ E D →
      (∀ θ : Fin 3 → ℝ,
        maximizers (fun v => score D v (toPar θ)) (E D) = {vHatE D θ} ∧
        D.gamma / 2 * Sf.inf' hS (fun v =>
            (v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ)))
          ≤ etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) ∧
        ∀ w, Sf.inf' hS (fun v => mv D v w θ)
          = Adv D w θ + (etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)))) ∧
      ∀ δe : ℝ, (∀ θ ∈ Theta4 V, etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) ≤ δe) →
        ∀ θ ∈ Theta4 V, ∃ v ∈ Sf,
          Real.sqrt ((v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ)))
            ≤ Real.sqrt (2 * δe / D.gamma)

/-- Part 4 in claim 017's family: for every nonempty finite `S ⊆ E` with `m` points there is
`θ = (0, λ₂, 0) ∈ Θ₄` with deficit at least `s²/(2(m+1)²)`, where the funded active action
`(s/(2(m+1)), λ₂)` has `Adv = -s²/(4(m+1)²)` while every pairwise contrast is at least
`s²/(4(m+1)²)`; and a deficit at most `δ/4` on `Θ₄` with `δ ≤ s²/128` needs
`m + 1 ≥ s √(2/δ) ≥ 16`. -/
def FamilyDeficit : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 / 100 →
    ∀ (S : Type) [Fintype S] (q : S → ℝ) (U : S → Fin 3 → ℝ), InKJ q U →
    let D := Standalone.M4CurvedEntryRate.data s q U
    ∀ (Sf : Finset (Inst 1 1 → ℝ)) (hS : Sf.Nonempty), (↑Sf : Set (Inst 1 1 → ℝ)) ⊆ E D →
      (∃ θ ∈ Theta4 (Standalone.M4CurvedEntryRate.V4 s), θ 0 = 0 ∧ θ 2 = 0 ∧
        s ^ 2 / (2 * (Sf.card + 1) ^ 2) ≤ etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) ∧
        let w := Standalone.M4CurvedEntryRate.act (s / (2 * (Sf.card + 1))) (θ 1)
        w ∈ F D ∧ w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧
        Adv D w θ = -(s ^ 2 / (4 * (Sf.card + 1) ^ 2)) ∧
        ∀ v ∈ Sf, s ^ 2 / (4 * (Sf.card + 1) ^ 2) ≤ mv D v w θ) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ s ^ 2 / 128 →
        (∀ θ ∈ Theta4 (Standalone.M4CurvedEntryRate.V4 s),
          etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) ≤ δ / 4) →
        s * Real.sqrt (2 / δ) ≤ Sf.card + 1 ∧ 16 ≤ s * Real.sqrt (2 / δ)

/-- Part 5: with `γ > 0` and positive-definite `Σ`, for a nonempty convex parameter set `T`, a
nonempty finite `S ⊆ E` is exact on `T` (`V_E = max_S Q` there) iff the ETF-only optimizer `v_E`
is constant on `T` with its value in `S`. -/
def ExactIff : Prop :=
  ∀ (n : ℕ) (S : Type) [Fintype S] (D : Data 1 n 2 S),
    Standalone.M2ActionClasses.RatesNonneg D → (∀ s, 0 ≤ D.q s) → w0 D ∈ F D → 0 < D.gamma →
    (∀ z : Inst 1 n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (covariance D *ᵥ z)) →
    ∀ (Sf : Finset (Inst 1 n → ℝ)) (hS : Sf.Nonempty), (↑Sf : Set (Inst 1 n → ℝ)) ⊆ E D →
    ∀ T : Set (Fin 3 → ℝ), Convex ℝ T → T.Nonempty →
      ((∀ θ ∈ T, etfSup D θ = Sf.sup' hS (fun v => score D v (toPar θ))) ↔
        ∃ v0 ∈ Sf, ∀ θ ∈ T, vHatE D θ = v0)

/-- Experiment 009's reviewed fixture: `γ = 2`, `B^A = (1, 1/2)`, one ETF with `B^E = (1, 0)` and
`c^E = 0`, incumbent `(3/10, 1/2)` with cash `1/5` (`W⁻ = 1`), symmetric rates `1/500` (active) and
`1/2000` (ETF), limits `1`, and eight equiprobable sign scenarios `(s, t, u)` with every shock scaled
by `1/10`: `z^f = (3s/500, t/500)`, `z^A = u/500 + s/1000`, `z^E = t/2000`. -/
def fix009 : Data 1 1 2 Sc where
  BA := !![1, 1 / 2]
  BE := !![1, 0]
  cE := 0
  kplus := Sum.elim (fun _ => 1 / 500) (fun _ => 1 / 2000)
  kminus := Sum.elim (fun _ => 1 / 500) (fun _ => 1 / 2000)
  gamma := 2
  q := fun _ => 1 / 8
  zf := fun x => ![3 * sg x.1 / 500, sg x.2.1 / 500]
  zA := fun x => ![sg x.2.2 / 500 + sg x.1 / 1000]
  zE := fun x => ![sg x.2.1 / 2000]
  x0 := Sum.elim (fun _ => 3 / 10) (fun _ => 1 / 2)
  h0 := 1 / 5
  wbar := fun _ => 1

/-- The fixture's `Θ₄ = [1/100, 3/100] × [0, 1/50] × [-1/20, 1/10]`. -/
def box009 : Set (Fin 3 → ℝ) :=
  {θ | 1 / 100 ≤ θ 0 ∧ θ 0 ≤ 3 / 100 ∧ 0 ≤ θ 1 ∧ θ 1 ≤ 1 / 50 ∧ -1 / 20 ≤ θ 2 ∧ θ 2 ≤ 1 / 10}

/-- The ETF holding `(a⁻, p)` of the fixture. -/
def hold (p : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => 3 / 10) (fun _ => p)

/-- Part 5 in experiment 009's fixture: the fixture meets part 5's hypotheses; the cash-exhausting
purchase `(3/10, 2801/4002)` is in `E` and is the ETF-only optimizer at every `θ ∈ Θ₄`, so the
single comparator has zero deficit there; the score's derivative in `p` at that point is at least
`2600957/276000000 > 0` on `Θ₄`, with equality attained; and an ETF cap of zero makes `E` the
singleton `{w⁻}` (for one ETF and a compliant incumbent). -/
def Fixture : Prop :=
  (Standalone.M2ActionClasses.RatesNonneg fix009 ∧ (∀ s, 0 ≤ fix009.q s) ∧ w0 fix009 ∈ F fix009 ∧
    0 < fix009.gamma ∧ (∀ z : Inst 1 1 → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (covariance fix009 *ᵥ z))) ∧
  hold (2801 / 4002) ∈ E fix009 ∧
  (∀ θ ∈ box009, vHatE fix009 θ = hold (2801 / 4002) ∧
    etfSup fix009 θ = score fix009 (hold (2801 / 4002)) (toPar θ)) ∧
  (∀ θ : Fin 3 → ℝ, ∃ d : ℝ,
    HasDerivAt (fun p => score fix009 (hold p) (toPar θ)) d (2801 / 4002) ∧
    (θ ∈ box009 → 2600957 / 276000000 ≤ d) ∧ (θ 0 = 1 / 100 → d = 2600957 / 276000000)) ∧
  ∀ (S : Type) [Fintype S] (D : Data 1 1 2 S), w0 D ∈ F D → D.wbar (Sum.inr 0) = 0 →
    E D = {w0 D}

/-- Claim 020, parts 1-5. -/
def statement : Prop :=
  FacesFinite ∧ LinearReduction ∧ ErrorSet ∧ FiniteContrasts ∧ CurvatureDeficit ∧ FamilyDeficit ∧
    ExactIff ∧ Fixture

end

end Standalone.M4FiniteComparatorFacesIff

import Standalone.M7DynamicBundlingBand
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Claim 108: the dynamic shape of the bundling band

Statement only; the proof is `Novel/M7DynamicBundlingShapeProof.lean`.

The model is claim 107's, with one ETF: `P : M6 (1 + 1) Z Ω`, the fund at index `0` and the ETF at index
`1`. The claim uses 107's objects: `join a p`, the ETF box `ebox`, `Fe`, the ETF-optimized value `U` and
the fund's effective band `loU`, `hiU`. An ETF holding is written `fun _ => p` for `p : ℝ`. At review
`t` and state `z`, `SAA`, `SAE` and `SEE` are the covariance entries and `as`, `ps` the targets. The hedge
ratios are `ρ = Σ_AE/Σ_EE` and `ρ_A = Σ_AE/Σ_AA`, and the residual curvatures are
`c^res = γ(Σ_AA - Σ_AE²/Σ_EE)` and `c^res_E = γ(Σ_EE - Σ_AE²/Σ_AA)`.

Part 2's Topkis step (Lemma A (ii) and (iv), Lemma C) enters through `AX14`, the universal form of
`Upstream.Topkis`'s structures (ledger entry AX-14, audited ok). Lemma B and the induction are proved.
Part 2 is stated for `Σ_AE ≥ 0` along the tree. The `Σ_AE ≤ 0` case (the same argument with the ETF
coordinate flipped) and the `Σ_AE = 0` case are paper-level (PM's scope note).
-/

namespace Standalone.M7DynamicBundlingShape

open Matrix Standalone.M6QuarterlyBandStaticCeiling Standalone.M7DynamicBundlingBand

noncomputable section

variable {Z Ω : Type} [Fintype Ω]

/-- `Σ_AA`. -/
def SAA (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.Sigma t z 0 0
/-- `Σ_AE`. -/
def SAE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.Sigma t z 0 1
/-- `Σ_EE`. -/
def SE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.Sigma t z 1 1
/-- The fund's target `a*`. -/
def as (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := xstar P t z 0
/-- The ETF's target `p*`. -/
def ps (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := xstar P t z 1
/-- `ρ = Σ_AE/Σ_EE`. -/
def rE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := SAE P t z / SE P t z
/-- `ρ_A = Σ_AE/Σ_AA`. -/
def rA (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := SAE P t z / SAA P t z
/-- `c^res = γ(Σ_AA - Σ_AE²/Σ_EE)`. -/
def cA (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.gamma * (SAA P t z - SAE P t z ^ 2 / SE P t z)
/-- `c^res_E = γ(Σ_EE - Σ_AE²/Σ_AA)`. -/
def cE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ := P.gamma * (SE P t z - SAE P t z ^ 2 / SAA P t z)

/-- The median of three numbers. -/
def med3 (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

/-- The clip to the fund's box. -/
def clipA (P : M6 (1 + 1) Z Ω) (v : ℝ) : ℝ := min (max v 0) (P.cap 0)

/-! ### Part 1's levels (at a review `t` and state `z`) -/

/-- The bought level of the lower edge, `a* - (κ⁺_A - ρ κ⁺_E)/c^res`. -/
def loB (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  as P t z - (P.kp 0 - rE P t z * P.kp 1) / cA P t z
/-- The sold level of the lower edge, `a* - (κ⁺_A + ρ κ⁻_E)/c^res`. -/
def loS (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  as P t z - (P.kp 0 + rE P t z * P.km 1) / cA P t z
/-- The idle line of the lower edge, `a* - ρ_A (p⁻ - p*) - κ⁺_A/(γ Σ_AA)`. -/
def loI (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (pm : ℝ) : ℝ :=
  as P t z - rA P t z * (pm - ps P t z) - P.kp 0 / (P.gamma * SAA P t z)
/-- The bought level of the upper edge, `a* + (κ⁻_A + ρ κ⁺_E)/c^res`. -/
def hiB (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  as P t z + (P.km 0 + rE P t z * P.kp 1) / cA P t z
/-- The sold level of the upper edge, `a* + (κ⁻_A - ρ κ⁻_E)/c^res`. -/
def hiS (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) : ℝ :=
  as P t z + (P.km 0 - rE P t z * P.km 1) / cA P t z
/-- The idle line of the upper edge, `a* - ρ_A (p⁻ - p*) + κ⁻_A/(γ Σ_AA)`. -/
def hiI (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (pm : ℝ) : ℝ :=
  as P t z - rA P t z * (pm - ps P t z) + P.km 0 / (P.gamma * SAA P t z)

/-- `p` is an ETF optimizer at the fund holding `a` against the incumbent `p⁻`. -/
def IsEOpt (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (pm a p : ℝ) : Prop :=
  (fun _ => p) ∈ ebox P ∧ ∀ q ∈ ebox P, Fe P t z (fun _ => pm) a (fun _ => p) ≤ Fe P t z (fun _ => pm) a q

/-- Part 1: at the last review, for an ETF incumbent `p⁻` whose ETF optimizer at the fund's edge is strictly
inside the ETF box, the edge is the median of its bought level, its idle line and its sold level,
clipped to the fund's box. -/
def Edges : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 (1 + 1) Z Ω), Setting P → ∀ (z : Z) (pm : ℝ),
    let t := P.T - 1
    ((∃ p, IsEOpt P t z pm (loU P t z (fun _ => pm)) p ∧ 0 < p ∧ p < P.cap 1) →
      loU P t z (fun _ => pm) = clipA P (med3 (loB P t z) (loI P t z pm) (loS P t z))) ∧
    ((∃ p, IsEOpt P t z pm (hiU P t z (fun _ => pm)) p ∧ 0 < p ∧ p < P.cap 1) →
      hiU P t z (fun _ => pm) = clipA P (med3 (hiB P t z) (hiI P t z pm) (hiS P t z)))

/-- Part 1a: for `Σ_AE > 0`, each edge's median is a continuous nonincreasing function of the ETF incumbent.
It is flat at its bought level, falls along the idle line (slope `-ρ_A`) over an interval of ETF incumbents
of length `(κ⁺_E + κ⁻_E)/c^res_E`, the ETF's residual static width, and is flat at its sold level beyond.
For `Σ_AE < 0` the median is nondecreasing, again from its bought level at small incumbents to its sold
level, over an interval of the same length. For `Σ_AE = 0` the three levels coincide. -/
def Bend : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 (1 + 1) Z Ω), Setting P → ∀ (t : ℕ) (z : Z),
    let lo := fun pm => med3 (loB P t z) (loI P t z pm) (loS P t z)
    let hi := fun pm => med3 (hiB P t z) (hiI P t z pm) (hiS P t z)
    Continuous lo ∧ Continuous hi ∧
    (0 < SAE P t z → Antitone lo ∧ Antitone hi ∧
      (∃ p₁ p₂, p₂ - p₁ = (P.kp 1 + P.km 1) / cE P t z ∧
        (∀ pm, pm ≤ p₁ → lo pm = loB P t z) ∧ (∀ pm, p₁ ≤ pm → pm ≤ p₂ → lo pm = loI P t z pm) ∧
        (∀ pm, p₂ ≤ pm → lo pm = loS P t z)) ∧
      (∃ p₁ p₂, p₂ - p₁ = (P.kp 1 + P.km 1) / cE P t z ∧
        (∀ pm, pm ≤ p₁ → hi pm = hiB P t z) ∧ (∀ pm, p₁ ≤ pm → pm ≤ p₂ → hi pm = hiI P t z pm) ∧
        (∀ pm, p₂ ≤ pm → hi pm = hiS P t z))) ∧
    (SAE P t z < 0 → Monotone lo ∧ Monotone hi ∧
      (∃ p₁ p₂, p₂ - p₁ = (P.kp 1 + P.km 1) / cE P t z ∧
        (∀ pm, pm ≤ p₁ → lo pm = loB P t z) ∧ (∀ pm, p₁ ≤ pm → pm ≤ p₂ → lo pm = loI P t z pm) ∧
        (∀ pm, p₂ ≤ pm → lo pm = loS P t z)) ∧
      (∃ p₁ p₂, p₂ - p₁ = (P.kp 1 + P.km 1) / cE P t z ∧
        (∀ pm, pm ≤ p₁ → hi pm = hiB P t z) ∧ (∀ pm, p₁ ≤ pm → pm ≤ p₂ → hi pm = hiI P t z pm) ∧
        (∀ pm, p₂ ≤ pm → hi pm = hiS P t z))) ∧
    (SAE P t z = 0 → ∀ pm, lo pm = loI P t z pm ∧ loB P t z = loI P t z pm ∧ loS P t z = loI P t z pm ∧
      hi pm = hiI P t z pm ∧ hiB P t z = hiI P t z pm ∧ hiS P t z = hiI P t z pm)

/-- Part 1b: the widths of the regimes. Both edges bought, or both sold, give the residual ceiling
`(κ⁺_A + κ⁻_A)/c^res`. Both idle give the fund-alone width `(κ⁺_A + κ⁻_A)/(γ Σ_AA)`. Lower bought and upper
sold give the ceiling minus the leak, `[κ⁺_A + κ⁻_A - ρ(κ⁺_E + κ⁻_E)]/c^res`. -/
def Widths : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 (1 + 1) Z Ω), Setting P → ∀ (t : ℕ) (z : Z) (pm : ℝ),
    hiB P t z - loB P t z = (P.kp 0 + P.km 0) / cA P t z ∧
    hiS P t z - loS P t z = (P.kp 0 + P.km 0) / cA P t z ∧
    hiI P t z pm - loI P t z pm = (P.kp 0 + P.km 0) / (P.gamma * SAA P t z) ∧
    hiS P t z - loB P t z = (P.kp 0 + P.km 0 - rE P t z * (P.kp 1 + P.km 1)) / cA P t z

/-! ### Part 2 -/

/-- Increasing differences of `f` on `S × T`. -/
def IncDiff (f : ℝ → ℝ → ℝ) (S T : Set ℝ) : Prop :=
  ∀ a₁ ∈ S, ∀ a₂ ∈ S, ∀ p₁ ∈ T, ∀ p₂ ∈ T, a₁ ≤ a₂ → p₁ ≤ p₂ →
    f a₂ p₁ - f a₁ p₁ ≤ f a₂ p₂ - f a₁ p₂

/-- The ETF's lower edge given the fund holding `a`: claim 029's edge for `p ↦ G_t(join a p)`. -/
def loE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (a : ℝ) : ℝ :=
  loF (fun p => G P t z (join a fun _ => p)) (P.kp 1) (P.cap 1)

/-- The ETF's upper edge given the fund holding `a`. -/
def hiE (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (a : ℝ) : ℝ :=
  hiF (fun p => G P t z (join a fun _ => p)) (P.km 1) (P.cap 1)

/-- A product of intervals `∏ I i` (AX-14's notation). -/
def Box {ι : Type} (I : ι → Set ℝ) : Set (ι → ℝ) := Set.univ.pi I

/-- Submodularity on `D`: `F(x ⊓ y) + F(x ⊔ y) ≤ F x + F y`. -/
def Submodular {ι : Type} (F : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, F (x ⊓ y) + F (x ⊔ y) ≤ F x + F y

/-- Decreasing differences in the pair `(i, j)` on `D` (the source's antitone differences). -/
def DecDiff {ι : Type} [DecidableEq ι] (F : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) (i j : ι) : Prop :=
  ∀ x : ι → ℝ, ∀ s₁ s₂ t₁ t₂ : ℝ, s₁ ≤ s₂ → t₁ ≤ t₂ →
    Function.update (Function.update x i s₁) j t₁ ∈ D → Function.update (Function.update x i s₂) j t₂ ∈ D →
    Function.update (Function.update x i s₁) j t₂ ∈ D → Function.update (Function.update x i s₂) j t₁ ∈ D →
    F (Function.update (Function.update x i s₂) j t₂) - F (Function.update (Function.update x i s₁) j t₂) ≤
      F (Function.update (Function.update x i s₂) j t₁) - F (Function.update (Function.update x i s₁) j t₁)

/-- Ledger entry AX-14 (`topkis1978minimizing` Theorems 3.2, 3.1 and 4.3), in its universal form. On a
product of intervals, decreasing differences in every pair imply submodularity, and conversely.
The partial minimum over a product of intervals of a submodular function, when attained, is
submodular. It is not proved here. It enters as the Upstream hypothesis structures
`Upstream.Topkis.Pairwise`, `Converse` and `PartialMin` (the proof's `ax14_iff`), and part 2 takes it
as a hypothesis. -/
def AX14 : Prop :=
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : ι → Set ℝ) (F : (ι → ℝ) → ℝ),
    ((∀ i, (I i).OrdConnected) → (∀ i j, i ≠ j → DecDiff F (Box I) i j) → Submodular F (Box I)) ∧
    ((∀ i, (I i).OrdConnected) → Submodular F (Box I) → ∀ i j, i ≠ j → DecDiff F (Box I) i j)) ∧
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (I : ι → Set ℝ) (J : κ → Set ℝ) (F : (ι → ℝ) → (κ → ℝ) → ℝ),
    (∀ i, (I i).OrdConnected) → (∀ k, (J k).OrdConnected) →
    Submodular (fun w : ι ⊕ κ → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) (Box (Sum.elim I J)) →
    (∀ x ∈ Box I, ∃ y ∈ Box J, ∀ y' ∈ Box J, F x y ≤ F x y') →
    Submodular (fun x => sInf (F x '' Box J)) (Box I)

/-- Part 2 (given AX-14), for `Σ_AE ≥ 0` along the whole tree:
- 2a: `V_t` has increasing differences on the nonnegative quadrant, `G_t` on the box, and `U_t` in
  `(a, p⁻)`, for `a` in the fund's box and `p⁻ ≥ 0`;
- 2b: the fund's edges are nonincreasing in the ETF incumbent;
- 2c: the ETF's edges are nonincreasing in the fund holding;
- 2d: the no-trade region is the intersection of the two bands. -/
def Monotone2 : Prop :=
  AX14 → ∀ (Z Ω : Type) [Fintype Ω] (P : M6 (1 + 1) Z Ω), Setting P →
    (∀ t z, 0 ≤ SAE P t z) → ∀ t z, t < P.T →
    IncDiff (fun a p => V P t z (join a fun _ => p)) (Set.Ici 0) (Set.Ici 0) ∧
    IncDiff (fun a p => G P t z (join a fun _ => p)) (Set.Icc 0 (P.cap 0)) (Set.Icc 0 (P.cap 1)) ∧
    IncDiff (fun a pm => U P t z (fun _ => pm) a) (Set.Icc 0 (P.cap 0)) (Set.Ici 0) ∧
    AntitoneOn (fun pm => loU P t z (fun _ => pm)) (Set.Ici 0) ∧
    AntitoneOn (fun pm => hiU P t z (fun _ => pm)) (Set.Ici 0) ∧
    AntitoneOn (loE P t z) (Set.Icc 0 (P.cap 0)) ∧ AntitoneOn (hiE P t z) (Set.Icc 0 (P.cap 0)) ∧
    ∀ a p, join a (fun _ => p) ∈ NT P t z ↔
      (0 ≤ a ∧ a ≤ P.cap 0 ∧ 0 ≤ p ∧ p ≤ P.cap 1) ∧
      loU P t z (fun _ => p) ≤ a ∧ a ≤ hiU P t z (fun _ => p) ∧ loE P t z a ≤ p ∧ p ≤ hiE P t z a

/-! ### Part 3: frozen ETF -/

/-- The frozen-ETF value `k` reviews before the horizon, with the ETF held at `p₀` under pure-learning
marking: `V^fr_T = 0`, and `V^fr_t(a) = min_{a' ∈ [0, x̄_A]} [C_A(a' - a) + G^fr_t(a')]`. -/
def Vfk (P : M6 (1 + 1) Z Ω) (p0 : ℝ) : ℕ → Z → ℝ → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun z a => sInf ((fun a' => costA P (a' - a) +
      (track P (P.T - (k + 1)) z (join a' fun _ => p0) +
        P.beta * ∑ ω, P.prob (P.T - (k + 1)) z ω * Vfk P p0 k (P.next ω) a')) '' Set.Icc 0 (P.cap 0))

/-- `V^fr_t`. -/
def Vfr (P : M6 (1 + 1) Z Ω) (p0 : ℝ) (t : ℕ) (z : Z) (a : ℝ) : ℝ := Vfk P p0 (P.T - t) z a

/-- `G^fr_t(a) = (γ/2)(a - a*, p₀ - p*)Σ(a - a*, p₀ - p*)' + β E[V^fr_{t+1}(a)]`. -/
def Gfr (P : M6 (1 + 1) Z Ω) (p0 : ℝ) (t : ℕ) (z : Z) (a : ℝ) : ℝ :=
  track P t z (join a fun _ => p0) + P.beta * ∑ ω, P.prob t z ω * Vfr P p0 (t + 1) (P.next ω) a

/-- The idle target `a^idle = a* - ρ_A (p₀ - p*)`. -/
def aIdle (P : M6 (1 + 1) Z Ω) (p0 : ℝ) (t : ℕ) (z : Z) : ℝ := as P t z - rA P t z * (p0 - ps P t z)

/-- The frozen-ETF one-instrument instance: curvature `γ Σ_AA`, the idle target, the fund's rates and cap,
pure-learning marking. -/
def idle (P : M6 (1 + 1) Z Ω) (p0 : ℝ) : M6 1 Z Ω where
  T := P.T
  mu t z := fun _ => P.gamma * SAA P t z * aIdle P p0 t z
  Sigma t z := fun _ _ => SAA P t z
  gamma := P.gamma
  beta := P.beta
  kp := fun _ => P.kp 0
  km := fun _ => P.km 0
  cap := fun _ => P.cap 0
  prob := P.prob
  next := P.next
  gross _ := fun _ => 1

/-- Part 3: with the ETF frozen at `p₀` under pure-learning marking, the idle instance is an M6
instance with target the idle target. `G^fr_t` is its `G_t` and `V^fr_t` its value, each plus a constant
at every review and state. So the fund's band is claim 029's band of the idle instance (`lo`, `hi`). -/
def Frozen : Prop :=
  ∀ (Z Ω : Type) [Fintype Ω] (P : M6 (1 + 1) Z Ω), Setting P → ∀ p0 : ℝ,
    Setting (idle P p0) ∧ (∀ t z, xstar (idle P p0) t z 0 = aIdle P p0 t z) ∧
    ∃ K L : ℕ → Z → ℝ, ∀ t z a,
      Vfr P p0 t z a = V1 (idle P p0) t z a + K t z ∧ Gfr P p0 t z a = G1 (idle P p0) t z a + L t z

/-- Part 3's variance: `v^idle = v_A + ρ_A² v_E + 2 ρ_A r √(v_A v_E)` is the second moment of
`Δa* + ρ_A Δp*` for any finite law of target innovations with second moments `v_A`, `v_E`, `r √(v_A v_E)`.
Its derivative in `r` is `2 ρ_A √(v_A v_E)`. -/
def IdleVariance : Prop :=
  ∀ (S : Type) [Fintype S] (q da dp : S → ℝ) (vA vE r rhoA : ℝ),
    (∑ s, q s * (da s * da s) = vA) → (∑ s, q s * (dp s * dp s) = vE) →
    (∑ s, q s * (da s * dp s) = r * Real.sqrt (vA * vE)) →
    ∑ s, q s * ((da s + rhoA * dp s) * (da s + rhoA * dp s)) =
      vA + rhoA ^ 2 * vE + 2 * rhoA * r * Real.sqrt (vA * vE)

/-! ### Part 4: the last review is free of the innovation law -/

/-- Part 4: two instances that agree on the horizon, on the targets' premia and the covariance at the
last review, and on `γ`, the rates and the caps have the same last-review bands and region,
whatever their outcome laws, discount and gross returns. -/
def LastFree : Prop :=
  ∀ (Z Ω Ω' : Type) [Fintype Ω] [Fintype Ω'] (P : M6 (1 + 1) Z Ω) (P' : M6 (1 + 1) Z Ω'),
    Setting P → Setting P' → P.T = P'.T → (∀ z, P.mu (P.T - 1) z = P'.mu (P.T - 1) z) →
    (∀ z, P.Sigma (P.T - 1) z = P'.Sigma (P.T - 1) z) → P.gamma = P'.gamma → P.kp = P'.kp →
    P.km = P'.km → P.cap = P'.cap → ∀ z,
      (∀ pm, loU P (P.T - 1) z pm = loU P' (P.T - 1) z pm ∧ hiU P (P.T - 1) z pm = hiU P' (P.T - 1) z pm) ∧
      (∀ a, loE P (P.T - 1) z a = loE P' (P.T - 1) z a ∧ hiE P (P.T - 1) z a = hiE P' (P.T - 1) z a) ∧
      NT P (P.T - 1) z = NT P' (P.T - 1) z

/-- Claim 108 (parts 1-4; part 1c is claim 029's `StaticShape`; the Reading is paper-level). -/
def statement : Prop :=
  Edges ∧ Bend ∧ Widths ∧ StaticShape ∧ Monotone2 ∧ Frozen ∧ IdleVariance ∧ LastFree

end

end Standalone.M7DynamicBundlingShape

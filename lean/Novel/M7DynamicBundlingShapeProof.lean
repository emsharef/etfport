import Standalone.M7DynamicBundlingShape
import Upstream.Topkis
import Novel.M7DynamicBundlingBandProof
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Claim 108: proof

Part 2 uses `AX14`, the universal form of ledger entry AX-14's Upstream structures (Topkis's
Theorems 3.1, 3.2 and 4.3, audited ok). Lemma B, the flipped coordinates and the backward induction
are proved here.
-/

namespace Novel.M7DynamicBundlingShapeProof

open Matrix Standalone.M6QuarterlyBandStaticCeiling Standalone.M7DynamicBundlingBand
  Standalone.M7DynamicBundlingShape

noncomputable section
open scoped Pointwise

variable {Z Ω : Type} [Fintype Ω]

/-! ### Settings facts -/

section Facts

variable {P : M6 (1 + 1) Z Ω}

lemma sig_symm (hS : Setting P) (t : ℕ) (z : Z) : P.Sigma t z 1 0 = SAE P t z := by
  have := congrFun (congrFun (hS.2.1 t z) 0) 1
  simpa [transpose_apply, SAE] using this

lemma saa_pos (hS : Setting P) (t : ℕ) (z : Z) : 0 < SAA P t z := by
  have := hS.2.2.1 t z (Pi.single 0 1) (by simp)
  simpa [mulVec, dotProduct, Pi.single_apply, SAA] using this

lemma se_pos (hS : Setting P) (t : ℕ) (z : Z) : 0 < SE P t z := by
  have := hS.2.2.1 t z (Pi.single 1 1) (by simp)
  simpa [mulVec, dotProduct, Pi.single_apply, SE] using this

/-- `Σ_AE² < Σ_AA Σ_EE`. -/
lemma det_pos (hS : Setting P) (t : ℕ) (z : Z) : SAE P t z ^ 2 < SAA P t z * SE P t z := by
  have hA := saa_pos hS t z
  have := hS.2.2.1 t z ![SE P t z, -SAE P t z] (by
    intro h; have := congrFun h 0; simp at this; linarith [se_pos hS t z])
  have h10 := sig_symm hS t z
  simp only [SAA, SAE, SE] at *
  simp [mulVec, dotProduct, Fin.sum_univ_succ, h10] at this
  have hSE := se_pos hS t z
  simp only [SE] at hSE
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left hc hSE.le]

lemma cA_pos (hS : Setting P) (t : ℕ) (z : Z) : 0 < cA P t z := by
  have h1 := det_pos hS t z; have h2 := se_pos hS t z
  have : 0 < SAA P t z - SAE P t z ^ 2 / SE P t z := by
    rw [sub_pos, div_lt_iff₀ h2]; linarith
  exact mul_pos hS.2.2.2.1 this

lemma cE_pos (hS : Setting P) (t : ℕ) (z : Z) : 0 < cE P t z := by
  have h1 := det_pos hS t z; have h2 := saa_pos hS t z
  have : 0 < SE P t z - SAE P t z ^ 2 / SAA P t z := by
    rw [sub_pos, div_lt_iff₀ h2]; linarith
  exact mul_pos hS.2.2.2.1 this

end Facts

/-- `AX14` is the universal form of the Upstream structures for AX-14. -/
theorem ax14_iff : AX14 ↔
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : ι → Set ℝ) (F : (ι → ℝ) → ℝ),
      Upstream.Topkis.Pairwise I F ∧ Upstream.Topkis.Converse I F) ∧
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (I : ι → Set ℝ) (J : κ → Set ℝ) (F : (ι → ℝ) → (κ → ℝ) → ℝ),
      Upstream.Topkis.PartialMin I J F :=
  ⟨fun h => ⟨fun ι _ _ I F => ⟨⟨(h.1 ι I F).1⟩, ⟨(h.1 ι I F).2⟩⟩, fun ι κ _ _ I J F => ⟨h.2 ι κ I J F⟩⟩,
    fun h => ⟨fun ι _ _ I F => ⟨(h.1 ι I F).1.sub, (h.1 ι I F).2.dd⟩, fun ι κ _ _ I J F => (h.2 ι κ I J F).sub⟩⟩

/-! ### Part 1b: widths -/

theorem widths : Widths := by
  intro Z Ω _ P hS t z pm
  have hc := (cA_pos hS t z).ne'
  have hA : P.gamma * SAA P t z ≠ 0 := (mul_pos hS.2.2.2.1 (saa_pos hS t z)).ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hiB, loB, hiS, loS, hiI, loI] <;> field_simp <;> ring

/-! ### Part 3's variance -/

theorem idleVariance : IdleVariance := by
  intro S _ q da dp vA vE r rhoA hA hE hAE
  have : ∀ s, q s * ((da s + rhoA * dp s) * (da s + rhoA * dp s)) =
      q s * (da s * da s) + 2 * rhoA * (q s * (da s * dp s)) + rhoA ^ 2 * (q s * (dp s * dp s)) :=
    fun s => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hE, hAE]
  ring

/-! ### Part 1c: claim 029's static shape -/

theorem staticShape : StaticShape := Novel.M6QuarterlyBandStaticCeilingProof.staticShape

/-! ### Part 4: the last review -/

theorem lastFree : LastFree := by
  intro Z Ω Ω' _ _ P P' hS hS' hT hmu hSig hγ hkp hkm hcap z
  set T0 := P.T - 1
  have hx : xstar P T0 z = xstar P' T0 z := by simp only [xstar, hmu z, hSig z, hγ]
  have hG : ∀ x, G P T0 z x = G P' T0 z x := fun x => by
    have h1 : G P T0 z x = track P T0 z x := Novel.M6QuarterlyBandStaticCeilingProof.G_last hS z x
    have h2 : G P' T0 z x = track P' T0 z x := by
      have := Novel.M6QuarterlyBandStaticCeilingProof.G_last hS' z x; rwa [← hT] at this
    rw [h1, h2]; simp only [track, hx, hSig z, hγ]
  have hcE : ∀ u, costE P u = costE P' u := fun u => by simp [costE, hkp, hkm]
  have heb : ebox P = ebox P' := by ext p; simp [ebox, hcap]
  have hFe : ∀ pm a p, Fe P T0 z pm a p = Fe P' T0 z pm a p := fun pm a p => by
    simp only [Fe, hG, hcE]
  have hU : ∀ pm, U P T0 z pm = U P' T0 z pm := fun pm => funext fun a => by
    simp only [U, heb]
    congr 1; ext r; simp only [Set.mem_image]
    exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, (hFe pm a p).symm ▸ h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, (hFe pm a p) ▸ h⟩⟩
  refine ⟨fun pm => ?_, fun a => ?_, ?_⟩
  · simp only [loU, hiU, hU, hkp, hkm, hcap]; exact ⟨trivial, trivial⟩
  · simp only [loE, hiE, hG, hkp, hkm, hcap]; exact ⟨trivial, trivial⟩
  · ext x
    simp only [NT, IsOpt, Set.mem_ofPred_eq, box, hcap, hG]
    have hc : ∀ u, cost P u = cost P' u := fun u => by simp [cost, hkp, hkm]
    simp only [hc]

/-! ### Part 1a: the bend -/

section Bend

lemma med3_le {a b c : ℝ} (h : c ≤ a) : med3 a b c = max c (min a b) := by
  simp only [med3]
  rw [min_eq_right (h.trans (le_max_left a b)), max_comm]

lemma med3_ge {a b c : ℝ} (h : a ≤ c) : med3 a b c = max a (min b c) := by
  simp only [med3]
  rcases le_total a b with h1 | h1
  · rw [min_eq_left h1, max_eq_right h1]
  · rw [min_eq_right h1, max_eq_left h1, min_eq_left h, min_eq_left (h1.trans h), max_comm]

lemma med3_cont (A C K r : ℝ) : Continuous fun pm => med3 A (K - r * pm) C := by
  unfold med3; fun_prop

/-- The median with a decreasing middle line (`r > 0`, `C ≤ A`). -/
lemma med_pos {A C K r : ℝ} (hr : 0 < r) (hCA : C ≤ A) :
    Antitone (fun pm => med3 A (K - r * pm) C) ∧
    (∀ pm, pm ≤ (K - A) / r → med3 A (K - r * pm) C = A) ∧
    (∀ pm, (K - A) / r ≤ pm → pm ≤ (K - C) / r → med3 A (K - r * pm) C = K - r * pm) ∧
    (∀ pm, (K - C) / r ≤ pm → med3 A (K - r * pm) C = C) := by
  refine ⟨fun x y hxy => ?_, fun pm h => ?_, fun pm h1 h2 => ?_, fun pm h => ?_⟩
  · simp only [med3_le hCA]
    exact max_le_max_left _ (min_le_min_left _ (by nlinarith))
  · rw [med3_le hCA, min_eq_left, max_eq_right hCA]
    rw [le_div_iff₀ hr] at h; linarith
  · rw [div_le_iff₀ hr] at h1; rw [le_div_iff₀ hr] at h2
    rw [med3_le hCA, min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff₀ hr] at h
    rw [med3_le hCA, max_eq_left ((min_le_right _ _).trans (by linarith))]

/-- The median with an increasing middle line (`r < 0`, `A ≤ C`). -/
lemma med_neg {A C K r : ℝ} (hr : r < 0) (hAC : A ≤ C) :
    Monotone (fun pm => med3 A (K - r * pm) C) ∧
    (∀ pm, pm ≤ (K - A) / r → med3 A (K - r * pm) C = A) ∧
    (∀ pm, (K - A) / r ≤ pm → pm ≤ (K - C) / r → med3 A (K - r * pm) C = K - r * pm) ∧
    (∀ pm, (K - C) / r ≤ pm → med3 A (K - r * pm) C = C) := by
  refine ⟨fun x y hxy => ?_, fun pm h => ?_, fun pm h1 h2 => ?_, fun pm h => ?_⟩
  · simp only [med3_ge hAC]
    exact max_le_max_left _ (min_le_min_right _ (by nlinarith))
  · rw [le_div_iff_of_neg hr] at h
    rw [med3_ge hAC, max_eq_left ((min_le_left _ _).trans (by linarith))]
  · rw [div_le_iff_of_neg hr] at h1; rw [le_div_iff_of_neg hr] at h2
    rw [med3_ge hAC, min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [div_le_iff_of_neg hr] at h
    rw [med3_ge hAC, min_eq_right (by linarith), max_eq_right hAC]

variable {P : M6 (1 + 1) Z Ω}

omit [Fintype Ω] in
lemma loI_eq (t : ℕ) (z : Z) (pm : ℝ) : loI P t z pm =
    (as P t z + rA P t z * ps P t z - P.kp 0 / (P.gamma * SAA P t z)) - rA P t z * pm := by
  simp only [loI]; ring

omit [Fintype Ω] in
lemma hiI_eq (t : ℕ) (z : Z) (pm : ℝ) : hiI P t z pm =
    (as P t z + rA P t z * ps P t z + P.km 0 / (P.gamma * SAA P t z)) - rA P t z * pm := by
  simp only [hiI]; ring

omit [Fintype Ω] in
lemma lo_gap (t : ℕ) (z : Z) : loB P t z - loS P t z = rE P t z * (P.kp 1 + P.km 1) / cA P t z := by
  simp only [loB, loS]; ring

omit [Fintype Ω] in
lemma hi_gap (t : ℕ) (z : Z) : hiB P t z - hiS P t z = rE P t z * (P.kp 1 + P.km 1) / cA P t z := by
  simp only [hiB, hiS]; ring

/-- The bend's length: `ρ(κ⁺_E + κ⁻_E)/(c^res ρ_A) = (κ⁺_E + κ⁻_E)/c^res_E`. -/
lemma len (hS : Setting P) (t : ℕ) (z : Z) (h : SAE P t z ≠ 0) :
    rE P t z * (P.kp 1 + P.km 1) / cA P t z / rA P t z = (P.kp 1 + P.km 1) / cE P t z := by
  have hA := (saa_pos hS t z).ne'
  have hE := (se_pos hS t z).ne'
  have hc := (cA_pos hS t z).ne'
  have hce := (cE_pos hS t z).ne'
  have hd : SAA P t z * SE P t z - SAE P t z ^ 2 ≠ 0 := by linarith [det_pos hS t z]
  have hg := hS.2.2.2.1.ne'
  simp only [rE, rA, cA, cE] at *
  field_simp

theorem bend : Bend := by
  intro Z Ω _ P hS t z lo hi
  have hk1 := hS.2.2.2.2.2.2.1 1
  have hkE : 0 ≤ P.kp 1 + P.km 1 := by linarith [hk1.1, hk1.2.2.1]
  have hc := cA_pos hS t z
  have hlo : ∀ pm, lo pm = med3 (loB P t z)
      ((as P t z + rA P t z * ps P t z - P.kp 0 / (P.gamma * SAA P t z)) - rA P t z * pm) (loS P t z) :=
    fun pm => by simp only [lo, loI_eq]
  have hhi : ∀ pm, hi pm = med3 (hiB P t z)
      ((as P t z + rA P t z * ps P t z + P.km 0 / (P.gamma * SAA P t z)) - rA P t z * pm) (hiS P t z) :=
    fun pm => by simp only [hi, hiI_eq]
  refine ⟨?_, ?_, fun hpos => ?_, fun hneg => ?_, fun hzero pm => ?_⟩
  · rw [show lo = _ from funext hlo]; exact med3_cont _ _ _ _
  · rw [show hi = _ from funext hhi]; exact med3_cont _ _ _ _
  · have hr : 0 < rA P t z := div_pos hpos (saa_pos hS t z)
    have hrE : 0 < rE P t z := div_pos hpos (se_pos hS t z)
    have g1 : loS P t z ≤ loB P t z := by
      have := lo_gap (P := P) t z; have : 0 ≤ rE P t z * (P.kp 1 + P.km 1) / cA P t z := by positivity
      linarith
    have g2 : hiS P t z ≤ hiB P t z := by
      have := hi_gap (P := P) t z; have : 0 ≤ rE P t z * (P.kp 1 + P.km 1) / cA P t z := by positivity
      linarith
    obtain ⟨a1, b1, c1, d1⟩ := med_pos (K := as P t z + rA P t z * ps P t z - P.kp 0 / (P.gamma * SAA P t z)) hr g1
    obtain ⟨a2, b2, c2, d2⟩ := med_pos (K := as P t z + rA P t z * ps P t z + P.km 0 / (P.gamma * SAA P t z)) hr g2
    refine ⟨fun x y h => by rw [hlo, hlo]; exact a1 h, fun x y h => by rw [hhi, hhi]; exact a2 h,
      ⟨_, _, ?_, fun pm h => by rw [hlo]; exact b1 pm h,
        fun pm h1 h2 => by rw [hlo, c1 pm h1 h2, loI_eq], fun pm h => by rw [hlo]; exact d1 pm h⟩,
      ⟨_, _, ?_, fun pm h => by rw [hhi]; exact b2 pm h,
        fun pm h1 h2 => by rw [hhi, c2 pm h1 h2, hiI_eq], fun pm h => by rw [hhi]; exact d2 pm h⟩⟩
    · rw [← len hS t z hpos.ne', ← lo_gap]; field_simp; ring
    · rw [← len hS t z hpos.ne', ← hi_gap]; field_simp; ring
  · have hr : rA P t z < 0 := div_neg_of_neg_of_pos hneg (saa_pos hS t z)
    have hrE : rE P t z < 0 := div_neg_of_neg_of_pos hneg (se_pos hS t z)
    have g1 : loB P t z ≤ loS P t z := by
      have := lo_gap (P := P) t z
      have : rE P t z * (P.kp 1 + P.km 1) / cA P t z ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hrE.le hkE) hc.le
      linarith
    have g2 : hiB P t z ≤ hiS P t z := by
      have := hi_gap (P := P) t z
      have : rE P t z * (P.kp 1 + P.km 1) / cA P t z ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hrE.le hkE) hc.le
      linarith
    obtain ⟨a1, b1, c1, d1⟩ := med_neg (K := as P t z + rA P t z * ps P t z - P.kp 0 / (P.gamma * SAA P t z)) hr g1
    obtain ⟨a2, b2, c2, d2⟩ := med_neg (K := as P t z + rA P t z * ps P t z + P.km 0 / (P.gamma * SAA P t z)) hr g2
    refine ⟨fun x y h => by rw [hlo, hlo]; exact a1 h, fun x y h => by rw [hhi, hhi]; exact a2 h,
      ⟨_, _, ?_, fun pm h => by rw [hlo]; exact b1 pm h,
        fun pm h1 h2 => by rw [hlo, c1 pm h1 h2, loI_eq], fun pm h => by rw [hlo]; exact d1 pm h⟩,
      ⟨_, _, ?_, fun pm h => by rw [hhi]; exact b2 pm h,
        fun pm h1 h2 => by rw [hhi, c2 pm h1 h2, hiI_eq], fun pm h => by rw [hhi]; exact d2 pm h⟩⟩
    · rw [← len hS t z hneg.ne, ← lo_gap]; field_simp; ring
    · rw [← len hS t z hneg.ne, ← hi_gap]; field_simp; ring
  · have hrE : rE P t z = 0 := by simp [rE, hzero]
    have hrA : rA P t z = 0 := by simp [rA, hzero]
    have hcA : cA P t z = P.gamma * SAA P t z := by simp [cA, hzero]
    have e1 : loB P t z = loI P t z pm := by simp [loB, loI, hrE, hrA, hcA]
    have e2 : loS P t z = loI P t z pm := by simp [loS, loI, hrE, hrA, hcA]
    have e3 : hiB P t z = hiI P t z pm := by simp [hiB, hiI, hrE, hrA, hcA]
    have e4 : hiS P t z = hiI P t z pm := by simp [hiS, hiI, hrE, hrA, hcA]
    refine ⟨?_, e1, e2, ?_, e3, e4⟩
    · simp only [lo, e1, e2, med3, min_self, max_self]
    · simp only [hi, e3, e4, med3, min_self, max_self]

end Bend

/-! ### Part 3: the frozen ETF -/

section Frozen

variable {P : M6 (1 + 1) Z Ω} {p0 : ℝ}

lemma inv_one {s : ℝ} (hs : s ≠ 0) (μ : Fin 1 → ℝ) :
    ((fun _ _ => s : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ μ) 0 = μ 0 / s := by
  have hd : (fun _ _ => s : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => s := by
    ext a b; rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp
  have h : diagonal (fun _ : Fin 1 => s) * diagonal (fun _ => s⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]; simp [mul_inv_cancel₀ hs, diagonal_one]
  rw [hd, inv_eq_right_inv h, mulVec_diagonal, div_eq_mul_inv, mul_comm]

lemma xstar_idle (hS : Setting P) (t : ℕ) (z : Z) : xstar (idle P p0) t z 0 = aIdle P p0 t z := by
  simp only [xstar, Pi.smul_apply, smul_eq_mul]
  have e : (idle P p0).Sigma t z = fun _ _ => SAA P t z := rfl
  rw [e, inv_one (saa_pos hS t z).ne']
  simp only [idle]
  field_simp [hS.2.2.2.1.ne', (saa_pos hS t z).ne']

lemma setting_idle (hS : Setting P) : Setting (idle P p0) := by
  obtain ⟨h1, _, _, hγ, hβ, hβ1, hr, hc, hq, hq1, _⟩ := hS
  refine ⟨h1, fun t z => ?_, fun t z w hw => ?_, hγ, hβ, hβ1, fun _ => hr 0, fun _ => hc 0, hq, hq1,
    fun _ _ => one_pos⟩
  · ext a b; rfl
  · have hw0 : w 0 ≠ 0 := fun h => hw (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
    have := saa_pos ⟨h1, ‹_›, ‹_›, hγ, hβ, hβ1, hr, hc, hq, hq1, ‹_›⟩ t z
    simp only [mulVec, dotProduct, Fin.sum_univ_one, idle]
    have : 0 < w 0 * w 0 := mul_self_pos.mpr hw0
    nlinarith

/-- The frozen stage loss's constant, `(γ/2)(Σ_EE - Σ_AE²/Σ_AA)(p₀ - p*)²`. -/
def cfr (P : M6 (1 + 1) Z Ω) (p0 : ℝ) (t : ℕ) (z : Z) : ℝ :=
  P.gamma / 2 * (SE P t z - SAE P t z ^ 2 / SAA P t z) * (p0 - ps P t z) ^ 2

/-- The completed square. -/
lemma track_frozen (hS : Setting P) (t : ℕ) (z : Z) (a : ℝ) :
    track P t z (join a fun _ => p0) = track (idle P p0) t z (fun _ => a) + cfr P p0 t z := by
  have hA := (saa_pos hS t z).ne'
  have h10 := sig_symm hS t z
  simp only [track, dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.sub_apply, join,
    Fin.cons_zero, Fin.cons_succ, add_zero]
  rw [xstar_idle hS]
  simp only [idle, cfr, aIdle, rA, as, ps, SAA, SAE, SE] at *
  simp only [Fin.succ_zero_eq_one, h10]
  field_simp
  ring

omit [Fintype Ω] in
lemma costA_idle (u : ℝ) : costA P u = cost (idle P p0) (fun _ => u) := by
  simp [costA, cost, idle]

lemma track_nonneg1 {Q : M6 1 Z Ω} (hS : Setting Q) (t : ℕ) (z : Z) (x : Fin 1 → ℝ) :
    0 ≤ track Q t z x := by
  unfold track
  by_cases h : x - xstar Q t z = 0
  · rw [h]; simp
  · exact mul_nonneg (by linarith [hS.2.2.2.1]) (hS.2.2.1 t z _ h).le

lemma cost_nonneg1 {Q : M6 1 Z Ω} (hS : Setting Q) (u : Fin 1 → ℝ) : 0 ≤ cost Q u :=
  Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (hS.2.2.2.2.2.2.1 i).1 (le_max_right _ _))
    (mul_nonneg (hS.2.2.2.2.2.2.1 i).2.2.1 (le_max_right _ _))

lemma Vk_nonneg1 {Q : M6 1 Z Ω} (hS : Setting Q) : ∀ k z x, 0 ≤ Vk Q k z x
  | 0, _, _ => le_rfl
  | k + 1, z, x => Real.sInf_nonneg fun y ⟨x', _, hy⟩ => by
      rw [← hy]
      refine add_nonneg (cost_nonneg1 hS _) (add_nonneg (track_nonneg1 hS _ _ _) ?_)
      exact mul_nonneg hS.2.2.2.2.1.le (Finset.sum_nonneg fun ω _ =>
        mul_nonneg (hS.2.2.2.2.2.2.2.2.1 _ _ ω) (Vk_nonneg1 hS k _ _))

/-- The constants of the frozen recursion. -/
def Kf (P : M6 (1 + 1) Z Ω) (p0 : ℝ) : ℕ → Z → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => cfr P p0 (P.T - (k + 1)) z +
      P.beta * ∑ ω, P.prob (P.T - (k + 1)) z ω * Kf P p0 k (P.next ω)

lemma sInf_add_const (S : Set ℝ) (D : ℝ) (hne : S.Nonempty) (hb : BddBelow S) :
    sInf ((fun r => r + D) '' S) = sInf S + D := by
  have : (fun r => r + D) '' S = S + {D} := by rw [Set.add_singleton]
  rw [this, csInf_add hne hb (Set.singleton_nonempty D) (bddBelow_singleton), csInf_singleton]

theorem Vfk_eq (hS : Setting P) : ∀ k z a,
    Vfk P p0 k z a = Vk (idle P p0) k z (fun _ => a) + Kf P p0 k z
  | 0, _, _ => by simp [Vfk, Vk, Kf]
  | k + 1, z, a => by
    have hSi := setting_idle (p0 := p0) hS
    set τ := P.T - (k + 1)
    set f : (Fin 1 → ℝ) → ℝ := fun x' => cost (idle P p0) (x' - fun _ => a) +
      (track (idle P p0) τ z x' + (idle P p0).beta * ∑ ω, (idle P p0).prob τ z ω *
        Vk (idle P p0) k ((idle P p0).next ω) (mark x' ((idle P p0).gross ω)))
    have hf : ∀ a', costA P (a' - a) + (track P τ z (join a' fun _ => p0) +
        P.beta * ∑ ω, P.prob τ z ω * Vfk P p0 k (P.next ω) a') = f (fun _ => a') + Kf P p0 (k + 1) z := by
      intro a'
      have hm : ∀ ω, mark (fun _ : Fin 1 => a') ((idle P p0).gross ω) = fun _ => a' := fun ω => by
        funext i; simp [mark, idle]
      simp only [f, Kf, hm, Vfk_eq hS k, costA_idle (p0 := p0), track_frozen hS]
      simp only [idle, mul_add, Finset.sum_add_distrib]
      have : (fun _ : Fin 1 => a') - (fun _ => a) = fun _ => a' - a := rfl
      rw [this]; ring
    have hset : (fun a' => costA P (a' - a) + (track P τ z (join a' fun _ => p0) +
        P.beta * ∑ ω, P.prob τ z ω * Vfk P p0 k (P.next ω) a')) '' Set.Icc 0 (P.cap 0) =
        (fun r => r + Kf P p0 (k + 1) z) '' (f '' box (idle P p0)) := by
      ext r
      simp only [Set.mem_image]
      constructor
      · rintro ⟨a', ha', rfl⟩
        exact ⟨f (fun _ => a'), ⟨fun _ => a', fun i => ha', rfl⟩, (hf a').symm⟩
      · rintro ⟨_, ⟨x', hx', rfl⟩, rfl⟩
        refine ⟨x' 0, hx' 0, ?_⟩
        rw [hf]; congr 2; funext i; rw [Subsingleton.elim i 0]
    show sInf _ = sInf (f '' box (idle P p0)) + Kf P p0 (k + 1) z
    rw [hset, sInf_add_const]
    · exact ⟨_, fun _ => 0, fun i => ⟨le_rfl, (hSi.2.2.2.2.2.2.2.1 i).le⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rintro _ ⟨x', _, rfl⟩
      exact add_nonneg (cost_nonneg1 hSi _) (add_nonneg (track_nonneg1 hSi _ _ _)
        (mul_nonneg hSi.2.2.2.2.1.le (Finset.sum_nonneg fun ω _ =>
          mul_nonneg (hSi.2.2.2.2.2.2.2.2.1 _ _ ω) (Vk_nonneg1 hSi k _ _))))

theorem frozen : Standalone.M7DynamicBundlingShape.Frozen := by
  intro Z Ω _ P hS p0
  refine ⟨setting_idle hS, fun t z => xstar_idle hS t z, fun t z => Kf P p0 (P.T - t) z,
    fun t z => cfr P p0 t z + P.beta * ∑ ω, P.prob t z ω * Kf P p0 (P.T - (t + 1)) (P.next ω),
    fun t z a => ⟨?_, ?_⟩⟩
  · simp only [Vfr, V1, V]; exact Vfk_eq hS _ z a
  · have hm : ∀ ω, mark (fun _ : Fin 1 => a) ((idle P p0).gross ω) = fun _ => a := fun ω => by
      funext i; simp [mark, idle]
    simp only [Gfr, G1, G, hm, Vfr, V, track_frozen hS, Vfk_eq hS]
    simp only [idle, mul_add, Finset.sum_add_distrib]
    ring

end Frozen

/-! ### Part 1: the last review's medians -/

section Edges

open Novel.M7DynamicBundlingBandProof

lemma med3_nonneg_iff (x y w : ℝ) :
    0 ≤ med3 x y w ↔ (0 ≤ x ∧ 0 ≤ y) ∨ (0 ≤ x ∧ 0 ≤ w) ∨ (0 ≤ y ∧ 0 ≤ w) := by
  simp only [med3, le_max_iff, le_min_iff]; tauto

lemma med3_nonpos_iff (x y w : ℝ) :
    med3 x y w ≤ 0 ↔ (x ≤ 0 ∧ y ≤ 0) ∨ (x ≤ 0 ∧ w ≤ 0) ∨ (y ≤ 0 ∧ w ≤ 0) := by
  simp only [med3, max_le_iff, min_le_iff]; tauto

lemma med3_le_iff (r1 r2 r3 a : ℝ) :
    med3 r1 r2 r3 ≤ a ↔ (r1 ≤ a ∧ r2 ≤ a) ∨ (r1 ≤ a ∧ r3 ≤ a) ∨ (r2 ≤ a ∧ r3 ≤ a) := by
  simp only [med3, max_le_iff, min_le_iff]; tauto

lemma le_med3_iff (r1 r2 r3 a : ℝ) :
    a ≤ med3 r1 r2 r3 ↔ (a ≤ r1 ∧ a ≤ r2) ∨ (a ≤ r1 ∧ a ≤ r3) ∨ (a ≤ r2 ∧ a ≤ r3) := by
  simp only [med3, le_max_iff, le_min_iff]; tauto

/-- Median of roots: for increasing affine `c_i (a - r_i)`, the median is `≥ 0` iff `a ≥ med3 r`, and
`≤ 0` iff `a ≤ med3 r`. -/
lemma med_roots {c1 c2 c3 r1 r2 r3 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (a : ℝ) :
    (0 ≤ med3 (c1 * (a - r1)) (c2 * (a - r2)) (c3 * (a - r3)) ↔ med3 r1 r2 r3 ≤ a) ∧
    (med3 (c1 * (a - r1)) (c2 * (a - r2)) (c3 * (a - r3)) ≤ 0 ↔ a ≤ med3 r1 r2 r3) := by
  have e1 : ∀ c r, 0 < c → (0 ≤ c * (a - r) ↔ r ≤ a) := fun c r hc => by
    rw [mul_nonneg_iff_of_pos_left hc, sub_nonneg]
  have e2 : ∀ c r, 0 < c → (c * (a - r) ≤ 0 ↔ a ≤ r) := fun c r hc =>
    ⟨fun h => by by_contra h'; push Not at h'; nlinarith [mul_pos hc (sub_pos.mpr h')],
      fun h => by nlinarith⟩
  rw [med3_nonneg_iff, med3_le_iff, med3_nonpos_iff, le_med3_iff, e1 _ _ h1, e1 _ _ h2, e1 _ _ h3,
    e2 _ _ h1, e2 _ _ h2, e2 _ _ h3]
  exact ⟨Iff.rfl, Iff.rfl⟩

lemma med3_mid {x y w : ℝ} (h : (x ≤ y ∧ y ≤ w) ∨ (w ≤ y ∧ y ≤ x)) : med3 x y w = y := by
  simp only [med3]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [min_eq_left h1, max_eq_right h1, min_eq_left h2, max_eq_right h1]
  · rw [min_eq_right h2, max_eq_left h2, min_eq_right (h1.trans h2), max_eq_left h1]

lemma med3_left {x y w : ℝ} (h : (y ≤ x ∧ x ≤ w) ∨ (w ≤ x ∧ x ≤ y)) : med3 x y w = x := by
  simp only [med3]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h1]
  · rw [min_eq_left h2, max_eq_right h2, min_eq_right (h1.trans h2), max_eq_left h1]

lemma med3_right {x y w : ℝ} (h : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) : med3 x y w = w := by
  simp only [med3]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [min_eq_left (h1.trans h2), max_eq_right (h1.trans h2), min_eq_right h2, max_eq_right h1]
  · rw [min_eq_right (h1.trans h2), max_eq_left (h1.trans h2), min_eq_right h2, max_eq_right h1]

variable {P : M6 (1 + 1) Z Ω}

lemma rho1 (hS : Setting P) (t : ℕ) (z : Z) : rho P t z 0 = rE P t z := by
  have hE : SEE P t z = fun _ _ => SE P t z := by
    ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; rfl
  simp only [rho, hE]
  rw [inv_one (se_pos hS t z).ne']
  simp only [SEA, rE]
  exact congrArg (fun x => x / SE P t z) (sig_symm hS t z)

lemma cres1 (hS : Setting P) (t : ℕ) (z : Z) : cres P t z = cA P t z := by
  simp only [cres, s2res, dotProduct, Fin.sum_univ_one, rho1 hS, cA, SEA, rE, SAA]
  rw [show P.Sigma t z (Fin.succ 0) 0 = SAE P t z from sig_symm hS t z]
  ring

lemma g0_eq (hS : Setting P) (t : ℕ) (z : Z) (a p : ℝ) :
    Novel.M6QuarterlyBandStaticCeilingProof.grad P t z (join a fun _ => p) 0 =
      P.gamma * (SAA P t z * (a - as P t z) + SAE P t z * (p - ps P t z)) := by
  rw [grad0_join hS]
  simp only [SEA, dotProduct, Fin.sum_univ_one, Pi.sub_apply, SAA, as, ps]
  rw [show P.Sigma t z (Fin.succ 0) 0 = SAE P t z from sig_symm hS t z]; rfl

lemma g1_eq (hS : Setting P) (t : ℕ) (z : Z) (a p : ℝ) :
    Novel.M6QuarterlyBandStaticCeilingProof.grad P t z (join a fun _ => p) (Fin.succ 0) =
      P.gamma * (SAE P t z * (a - as P t z) + SE P t z * (p - ps P t z)) := by
  simp only [Novel.M6QuarterlyBandStaticCeilingProof.grad, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Pi.sub_apply, join, Fin.cons_zero, Fin.cons_succ]
  rw [show P.Sigma t z (Fin.succ 0) 0 = SAE P t z from sig_symm hS t z]
  rfl

/-- At a fund holding `a` whose ETF optimizer `p` is interior, the fund's marginal is the median of
the bought, idle and sold lines. -/
lemma grad_med (hS : Setting P) {t : ℕ} (hT1 : P.T ≤ t + 1) (z : Z) (pm a p : ℝ)
    (hopt : IsEOpt P t z pm a p) (hp0 : 0 < p) (hp1 : p < P.cap 1) :
    Novel.M6QuarterlyBandStaticCeilingProof.grad P t z (join a fun _ => p) 0 =
      med3 (cA P t z * (a - as P t z) - rE P t z * P.kp 1)
        (P.gamma * SAA P t z * (a - as P t z) + P.gamma * SAE P t z * (pm - ps P t z))
        (cA P t z * (a - as P t z) + rE P t z * P.km 1) := by
  have hint : Interior P (fun _ => p) := fun j => by rw [Subsingleton.elim j 0]; exact ⟨hp0, hp1⟩
  have hts := tradeSign_of_min hS hT1 z (fun _ => pm) (fun _ => p) a hopt.1 hint hopt.2 0
  have hid := edge_identity hS t z a (fun _ => p)
  simp only [dotProduct, Fin.sum_univ_one, rho1 hS, cres1 hS] at hid
  rw [g0_eq hS] at hid ⊢
  rw [g1_eq hS] at hts hid
  have has : xstar P t z 0 = as P t z := rfl
  rw [has] at hid
  simp only [Fin.succ_zero_eq_one] at hts
  set A := a - as P t z
  set g0 := P.gamma * (SAA P t z * A + SAE P t z * (p - ps P t z))
  set g1 := P.gamma * (SAE P t z * A + SE P t z * (p - ps P t z))
  set X := cA P t z * A - rE P t z * P.kp 1
  set Y := P.gamma * SAA P t z * A + P.gamma * SAE P t z * (pm - ps P t z)
  set W := cA P t z * A + rE P t z * P.km 1
  have hk := hS.2.2.2.2.2.2.1 1
  have hkE : 0 ≤ P.kp 1 + P.km 1 := by linarith [hk.1, hk.2.2.1]
  have hg0 : g0 = cA P t z * A + rE P t z * g1 := by linarith
  have hY : Y = g0 + P.gamma * SAE P t z * (pm - p) := by simp only [Y, g0]; ring
  have hWX : W - X = rE P t z * (P.kp 1 + P.km 1) := by simp only [W, X]; ring
  have hγ := hS.2.2.2.1
  have hsign : 0 ≤ SAE P t z ∨ SAE P t z < 0 := le_or_gt 0 _
  have hr : 0 ≤ SAE P t z → 0 ≤ rE P t z := fun h => div_nonneg h (se_pos hS t z).le
  have hr' : SAE P t z < 0 → rE P t z < 0 := fun h => div_neg_of_neg_of_pos h (se_pos hS t z)
  obtain ⟨tp, tm, t1, t2⟩ := hts
  rcases lt_trichotomy pm p with h | h | h
  · -- bought: `g1 = -κ⁺_E`, so `g0 = X`
    have e : g1 = -P.kp 1 := by have := tp (by linarith); linarith
    have hX : g0 = X := by rw [hg0, e]; simp only [X]; ring
    rw [hX]; symm; apply med3_left
    rcases hsign with hs | hs
    · have := hr hs
      have : P.gamma * SAE P t z * (pm - p) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hγ.le hs) (by linarith)
      left; constructor
      · rw [hY, hX]; linarith
      · nlinarith
    · have := hr' hs
      have : 0 ≤ P.gamma * SAE P t z * (pm - p) :=
        mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hγ.le hs.le) (by linarith)
      right; constructor
      · nlinarith
      · rw [hY, hX]; linarith
  · -- idle: `g0 = Y`
    subst h
    have hX : Y = g0 := by rw [hY]; ring
    rw [← hX]; symm; apply med3_mid
    have hXg : X = g0 - rE P t z * (g1 + P.kp 1) := by rw [hg0]; simp only [X]; ring
    have hWg : W = g0 + rE P t z * (P.km 1 - g1) := by rw [hg0]; simp only [W]; ring
    rcases hsign with hs | hs
    · have := hr hs
      left; rw [hX, hXg, hWg]; constructor <;> nlinarith
    · have := hr' hs
      right; rw [hX, hXg, hWg]; constructor <;> nlinarith
  · -- sold: `g1 = κ⁻_E`, so `g0 = W`
    have e : g1 = P.km 1 := by have := tm (by linarith); linarith
    have hW : g0 = W := by rw [hg0, e]
    rw [hW]; symm; apply med3_right
    rcases hsign with hs | hs
    · have := hr hs
      have : 0 ≤ P.gamma * SAE P t z * (pm - p) := mul_nonneg (mul_nonneg hγ.le hs) (by linarith)
      left; constructor
      · nlinarith
      · rw [hY, hW]; linarith
    · have := hr' hs
      have : P.gamma * SAE P t z * (pm - p) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ.le hs.le) (by linarith)
      right; constructor
      · rw [hY, hW]; linarith
      · nlinarith

lemma clip_of (hS : Setting P) {e m : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ P.cap 0) (h1 : 0 < e → e ≤ m)
    (h2 : e < P.cap 0 → m ≤ e) : e = clipA P m := by
  have hc := hS.2.2.2.2.2.2.2.1 0
  simp only [clipA]
  rcases he0.lt_or_eq with h0 | h0
  · rcases he1.lt_or_eq with hl | hl
    · have := le_antisymm (h2 hl) (h1 h0)
      rw [this, max_eq_left h0.le, min_eq_left hl.le]
    · have := h1 h0
      rw [max_eq_left (h0.le.trans this), min_eq_right (hl ▸ this), hl]
  · have := h2 (h0 ▸ hc)
    rw [max_eq_right (h0 ▸ this), min_eq_left hc.le, ← h0]

theorem edges : Edges := by
  intro Z Ω _ P hS z pm t
  have hT1 : P.T ≤ t + 1 := by have := hS.1; simp only [t]; omega
  have hU := U_convex hS t z (fun _ => pm)
  have hcap := capA hS
  have hc := cA_pos hS t z
  have hA : 0 < P.gamma * SAA P t z := mul_pos hS.2.2.2.1 (saa_pos hS t z)
  obtain ⟨-, -, -, h0lo, hlh, hhi1, -⟩ := effectiveBand 1 Z Ω P hS t z
    (by have := hS.1; simp only [t]; omega) (fun _ => pm)
  -- the three lines as `c (a - r)`
  have fb : ∀ k a, cA P t z * (a - as P t z) - rE P t z * P.kp 1 + k =
      cA P t z * (a - (as P t z - (k - rE P t z * P.kp 1) / cA P t z)) := fun k a => by
    field_simp; ring
  have fs : ∀ k a, cA P t z * (a - as P t z) + rE P t z * P.km 1 + k =
      cA P t z * (a - (as P t z - (k + rE P t z * P.km 1) / cA P t z)) := fun k a => by
    field_simp; ring
  have fi : ∀ k a, P.gamma * SAA P t z * (a - as P t z) + P.gamma * SAE P t z * (pm - ps P t z) + k =
      P.gamma * SAA P t z * (a - (as P t z - rA P t z * (pm - ps P t z) - k / (P.gamma * SAA P t z))) :=
    fun k a => by
      rw [show rA P t z = SAE P t z / SAA P t z from rfl]
      have := (saa_pos hS t z).ne'; have := hS.2.2.2.1.ne'
      field_simp
      ring
  have hmed_add : ∀ x y w k : ℝ, med3 x y w + k = med3 (x + k) (y + k) (w + k) := fun x y w k => by
    simp only [med3, max_add_add_right, min_add_add_right]
  refine ⟨fun ⟨p, hopt, hp0, hp1⟩ => ?_, fun ⟨p, hopt, hp0, hp1⟩ => ?_⟩
  · set e := loU P t z (fun _ => pm)
    have hg := grad_med hS hT1 z pm e p hopt hp0 hp1
    have hd := U_deriv_last hS hT1 z (fun _ => pm) (fun _ => p) e hopt.1 hopt.2
    have key := med_roots hc hA hc (a := e) (r1 := loB P t z) (r2 := loI P t z pm) (r3 := loS P t z)
    have hF : med3 (cA P t z * (e - as P t z) - rE P t z * P.kp 1)
        (P.gamma * SAA P t z * (e - as P t z) + P.gamma * SAE P t z * (pm - ps P t z))
        (cA P t z * (e - as P t z) + rE P t z * P.km 1) + P.kp 0 =
        med3 (cA P t z * (e - loB P t z)) (P.gamma * SAA P t z * (e - loI P t z pm))
          (cA P t z * (e - loS P t z)) := by
      rw [hmed_add, fb, fi, fs]; rfl
    refine clip_of hS h0lo (hlh.trans hhi1) (fun h0 => ?_) (fun h1 => ?_)
    · have : ld (U P t z fun _ => pm) e ≤ -P.kp 0 := ld_loF hU hcap h0
      rw [← key.2, ← hF, ← hg]; linarith [hd.1]
    · have : -P.kp 0 ≤ rd (U P t z fun _ => pm) e := rd_loF hU h1
      rw [← key.1, ← hF, ← hg]; linarith [hd.2]
  · set e := hiU P t z (fun _ => pm)
    have hg := grad_med hS hT1 z pm e p hopt hp0 hp1
    have hd := U_deriv_last hS hT1 z (fun _ => pm) (fun _ => p) e hopt.1 hopt.2
    have key := med_roots hc hA hc (a := e) (r1 := hiB P t z) (r2 := hiI P t z pm) (r3 := hiS P t z)
    have hF : med3 (cA P t z * (e - as P t z) - rE P t z * P.kp 1)
        (P.gamma * SAA P t z * (e - as P t z) + P.gamma * SAE P t z * (pm - ps P t z))
        (cA P t z * (e - as P t z) + rE P t z * P.km 1) + -P.km 0 =
        med3 (cA P t z * (e - hiB P t z)) (P.gamma * SAA P t z * (e - hiI P t z pm))
          (cA P t z * (e - hiS P t z)) := by
      rw [hmed_add, fb, fi, fs,
        show as P t z - (-P.km 0 - rE P t z * P.kp 1) / cA P t z = hiB P t z by simp only [hiB]; ring,
        show as P t z - (-P.km 0 + rE P t z * P.km 1) / cA P t z = hiS P t z by simp only [hiS]; ring,
        show as P t z - rA P t z * (pm - ps P t z) - -P.km 0 / (P.gamma * SAA P t z) = hiI P t z pm by
          simp only [hiI]; ring]
    refine clip_of hS (h0lo.trans hlh) hhi1 (fun h0 => ?_) (fun h1 => ?_)
    · have : ld (U P t z fun _ => pm) e ≤ P.km 0 := ld_hiF hU h0
      rw [← key.2, ← hF, ← hg]; linarith [hd.1]
    · have : P.km 0 ≤ rd (U P t z fun _ => pm) e := rd_hiF hU hcap h1
      rw [← key.1, ← hF, ← hg]; linarith [hd.2]

end Edges

/-! ### Part 2: generic tools -/

section Tools

open Function

variable {ι : Type} [DecidableEq ι]

/-- `F` depends only on the coordinates in `s`. -/
def DependsOn (F : (ι → ℝ) → ℝ) (s : Set ι) : Prop := ∀ x y, (∀ k ∈ s, x k = y k) → F x = F y

lemma dd_of_not_dep {F : (ι → ℝ) → ℝ} {s : Set ι} (hF : DependsOn F s) {D : Set (ι → ℝ)} {i j : ι}
    (h : i ∉ s ∨ j ∉ s) : DecDiff F D i j := by
  intro x s₁ s₂ t₁ t₂ _ _ _ _ _ _
  rcases h with h | h
  · have e : ∀ t, F (update (update x i s₂) j t) = F (update (update x i s₁) j t) := fun t =>
      hF _ _ fun k hk => by
        have hki : k ≠ i := fun he => h (he ▸ hk)
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [update_of_ne hkj, update_of_ne hki]
    rw [e, e]; simp
  · have e : ∀ s', F (update (update x i s') j t₂) = F (update (update x i s') j t₁) := fun s' =>
      hF _ _ fun k hk => by
        have hkj : k ≠ j := fun he => h (he ▸ hk)
        simp [update_of_ne hkj]
    rw [e, e]

lemma dd_add {F G : (ι → ℝ) → ℝ} {D : Set (ι → ℝ)} {i j : ι} (hF : DecDiff F D i j)
    (hG : DecDiff G D i j) : DecDiff (fun x => F x + G x) D i j := by
  intro x s₁ s₂ t₁ t₂ h1 h2 m1 m2 m3 m4
  have := hF x s₁ s₂ t₁ t₂ h1 h2 m1 m2 m3 m4
  have := hG x s₁ s₂ t₁ t₂ h1 h2 m1 m2 m3 m4
  simp only; linarith

/-- The mixed-difference property of a two-variable function on `S × T`. -/
def DD2 (φ : ℝ → ℝ → ℝ) (S T : Set ℝ) : Prop :=
  ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ t₁ ∈ T, ∀ t₂ ∈ T, s₁ ≤ s₂ → t₁ ≤ t₂ →
    φ s₂ t₂ - φ s₁ t₂ ≤ φ s₂ t₁ - φ s₁ t₁

/-- A term `φ(w k, w l)` has decreasing differences in `(k, l)` and `(l, k)` on a product of intervals. -/
lemma dd_two {I : ι → Set ℝ} {φ : ℝ → ℝ → ℝ} {k l : ι} (hkl : k ≠ l) (hφ : DD2 φ (I k) (I l)) :
    DecDiff (fun w => φ (w k) (w l)) (Box I) k l ∧ DecDiff (fun w => φ (w k) (w l)) (Box I) l k := by
  constructor
  · intro x s₁ s₂ t₁ t₂ h1 h2 m1 m2 _ _
    have a1 : s₁ ∈ I k := by have := m1 k (Set.mem_univ _); simpa [update_of_ne hkl] using this
    have a2 : s₂ ∈ I k := by have := m2 k (Set.mem_univ _); simpa [update_of_ne hkl] using this
    have b1 : t₁ ∈ I l := by have := m1 l (Set.mem_univ _); simpa using this
    have b2 : t₂ ∈ I l := by have := m2 l (Set.mem_univ _); simpa using this
    simp only [update_of_ne hkl, update_self]
    exact hφ s₁ a1 s₂ a2 t₁ b1 t₂ b2 h1 h2
  · intro x s₁ s₂ t₁ t₂ h1 h2 m1 m2 _ _
    have hlk := hkl.symm
    have a1 : s₁ ∈ I l := by have := m1 l (Set.mem_univ _); simpa [update_of_ne hlk] using this
    have a2 : s₂ ∈ I l := by have := m2 l (Set.mem_univ _); simpa [update_of_ne hlk] using this
    have b1 : t₁ ∈ I k := by have := m1 k (Set.mem_univ _); simpa using this
    have b2 : t₂ ∈ I k := by have := m2 k (Set.mem_univ _); simpa using this
    simp only [update_of_ne hlk, update_self]
    have := hφ t₁ b1 t₂ b2 s₁ a1 s₂ a2 h2 h1
    linarith

omit [DecidableEq ι] in
lemma dep_two (φ : ℝ → ℝ → ℝ) (k l : ι) : DependsOn (fun w => φ (w k) (w l)) {k, l} := fun x y h => by
  simp only
  rw [h k (by simp), h l (by simp)]

/-- Lemma B: a convex function of a difference has decreasing differences. -/
lemma lemmaB {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (S T : Set ℝ) :
    DD2 (fun s t => φ (s - t)) S T := by
  intro s₁ _ s₂ _ t₁ _ t₂ _ hs ht
  simp only
  set a := s₁ - t₂; set b := s₁ - t₁; set d := s₂ - s₁
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hd : 0 ≤ d := by simp only [d]; linarith
  have e1 : s₂ - t₂ = a + d := by simp only [a, d]; ring
  have e2 : s₂ - t₁ = b + d := by simp only [b, d]; ring
  rw [e1, e2]
  rcases hab.lt_or_eq with hab | hab
  · rcases hd.lt_or_eq with hd | hd
    · set L := (b - a) / (b - a + d)
      have hL0 : 0 < L := div_pos (by linarith) (by linarith)
      have hL1 : L < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      have c1 : a + d = L * a + (1 - L) * (b + d) := by
        simp only [L]; field_simp; ring
      have c2 : b = (1 - L) * a + L * (b + d) := by
        simp only [L]; field_simp; ring
      have i1 := hφ.2 (Set.mem_univ a) (Set.mem_univ (b + d)) hL0.le (by linarith : 0 ≤ 1 - L) (by ring)
      have i2 := hφ.2 (Set.mem_univ a) (Set.mem_univ (b + d)) (by linarith : 0 ≤ 1 - L) hL0.le (by ring)
      simp only [smul_eq_mul] at i1 i2
      rw [← c1] at i1; rw [← c2] at i2
      nlinarith
    · rw [← hd]; simp
  · rw [hab]

/-- Increasing differences under the flip `u = -a` become decreasing differences. -/
lemma dd2_flip {φ : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (h : ∀ a₁ ∈ S, ∀ a₂ ∈ S, ∀ p₁ ∈ T, ∀ p₂ ∈ T, a₁ ≤ a₂ → p₁ ≤ p₂ →
      φ a₂ p₁ - φ a₁ p₁ ≤ φ a₂ p₂ - φ a₁ p₂) :
    DD2 (fun u p => φ (-u) p) ((fun a => -a) '' S) T := by
  rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩ t₁ ht₁ t₂ ht₂ hs ht
  simp only [neg_neg]
  have := h a₂ ha₂ a₁ ha₁ t₁ ht₁ t₂ ht₂ (by linarith) ht
  linarith


/-- A two-coordinate term has decreasing differences in every pair. -/
lemma dd_term {I : ι → Set ℝ} {φ : ℝ → ℝ → ℝ} {k l : ι} (hkl : k ≠ l) (hφ : DD2 φ (I k) (I l)) :
    ∀ i j, i ≠ j → DecDiff (fun w => φ (w k) (w l)) (Box I) i j := by
  intro i j hij
  by_cases h1 : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h1; exact (dd_two hkl hφ).1
  by_cases h2 : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h2; exact (dd_two hkl hφ).2
  refine dd_of_not_dep (dep_two φ k l) ?_
  by_contra hc
  push Not at hc
  obtain ⟨hi, hj⟩ := hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hij rfl
  · exact h1 ⟨rfl, rfl⟩
  · exact h2 ⟨rfl, rfl⟩
  · exact hij rfl

/-- Argmin monotonicity: with increasing differences and unique minimizers, the minimizer is
nonincreasing in the parameter. -/
lemma argmin_anti {f : ℝ → ℝ → ℝ} {S T : Set ℝ} {m : ℝ → ℝ}
    (hID : ∀ a₁ ∈ S, ∀ a₂ ∈ S, ∀ p₁ ∈ T, ∀ p₂ ∈ T, a₁ ≤ a₂ → p₁ ≤ p₂ →
      f a₂ p₁ - f a₁ p₁ ≤ f a₂ p₂ - f a₁ p₂)
    (hmem : ∀ p ∈ T, m p ∈ S) (hmin : ∀ p ∈ T, ∀ a ∈ S, f (m p) p ≤ f a p)
    (huniq : ∀ p ∈ T, ∀ a ∈ S, (∀ b ∈ S, f a p ≤ f b p) → a = m p) :
    AntitoneOn m T := by
  intro p₁ hp₁ p₂ hp₂ hp
  by_contra hlt
  push Not at hlt
  have h1 := hmin p₁ hp₁ (m p₂) (hmem p₂ hp₂)
  have h2 := hmin p₂ hp₂ (m p₁) (hmem p₁ hp₁)
  have hd := hID (m p₁) (hmem p₁ hp₁) (m p₂) (hmem p₂ hp₂) p₁ hp₁ p₂ hp₂ hlt.le hp
  have heq : f (m p₂) p₁ ≤ f (m p₁) p₁ := by linarith
  have : m p₂ = m p₁ := huniq p₁ hp₁ (m p₂) (hmem p₂ hp₂) fun b hb => heq.trans (hmin p₁ hp₁ b hb)
  linarith

end Tools

/-! ### Part 2: increasing differences -/

section Part2

open Function Novel.M7DynamicBundlingBandProof

variable {P : M6 (1 + 1) Z Ω}

omit [Fintype Ω] in
lemma mark_join (a p : ℝ) (g : Fin (1 + 1) → ℝ) :
    mark (join a fun _ => p) g = join (a * g 0) fun _ => p * g 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Subsingleton.elim j 0]; rfl

lemma track_join (hS : Setting P) (t : ℕ) (z : Z) (a p : ℝ) :
    track P t z (join a fun _ => p) = P.gamma / 2 * (SAA P t z * (a - as P t z) ^ 2 +
      2 * SAE P t z * (a - as P t z) * (p - ps P t z) + SE P t z * (p - ps P t z) ^ 2) := by
  have h10 := sig_symm hS t z
  simp only [track, dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.sub_apply, join,
    Fin.cons_zero, Fin.cons_succ, add_zero]
  simp only [SAA, SAE, SE, as, ps] at *
  simp only [Fin.succ_zero_eq_one, h10]
  ring

omit [Fintype Ω] in
lemma cost_join (u w : ℝ) : cost P (join u fun _ => w) = costA P u + c1 (P.kp 1) (P.km 1) w := by
  simp [cost, costA, c1, Fin.sum_univ_succ, join]

/-- `V_t` on the fund and ETF holdings. -/
def V2 (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (a p : ℝ) : ℝ := V P t z (join a fun _ => p)

/-- `G_t` on the fund and ETF holdings. -/
def G2 (P : M6 (1 + 1) Z Ω) (t : ℕ) (z : Z) (a p : ℝ) : ℝ := G P t z (join a fun _ => p)

/-- Increasing differences of `G_t` on the quadrant, from those of `V_{t+1}`. -/
lemma G_ID (hS : Setting P) (hsign : ∀ t z, 0 ≤ SAE P t z) (t : ℕ) (z : Z)
    (hV : ∀ z', IncDiff (V2 P (t + 1) z') (Set.Ici 0) (Set.Ici 0)) :
    IncDiff (G2 P t z) (Set.Ici 0) (Set.Ici 0) := by
  intro a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ ha hp
  simp only [G2, G, track_join hS, mark_join]
  have hg : ∀ ω i, 0 < P.gross ω i := hS.2.2.2.2.2.2.2.2.2.2
  have hq : ∀ ω, 0 ≤ P.prob t z ω := hS.2.2.2.2.2.2.2.2.1 t z
  have hc : ∀ ω, V2 P (t + 1) (P.next ω) (a₂ * P.gross ω 0) (p₁ * P.gross ω 1) -
      V2 P (t + 1) (P.next ω) (a₁ * P.gross ω 0) (p₁ * P.gross ω 1) ≤
      V2 P (t + 1) (P.next ω) (a₂ * P.gross ω 0) (p₂ * P.gross ω 1) -
      V2 P (t + 1) (P.next ω) (a₁ * P.gross ω 0) (p₂ * P.gross ω 1) := fun ω =>
    hV _ _ (mul_nonneg (Set.mem_Ici.mp ha₁) (hg ω 0).le) _ (mul_nonneg (Set.mem_Ici.mp ha₂) (hg ω 0).le)
      _ (mul_nonneg (Set.mem_Ici.mp hp₁) (hg ω 1).le) _ (mul_nonneg (Set.mem_Ici.mp hp₂) (hg ω 1).le)
      (mul_le_mul_of_nonneg_right ha (hg ω 0).le) (mul_le_mul_of_nonneg_right hp (hg ω 1).le)
  have hsum : ∑ ω, P.prob t z ω * (V2 P (t + 1) (P.next ω) (a₂ * P.gross ω 0) (p₁ * P.gross ω 1) -
      V2 P (t + 1) (P.next ω) (a₁ * P.gross ω 0) (p₁ * P.gross ω 1)) ≤
      ∑ ω, P.prob t z ω * (V2 P (t + 1) (P.next ω) (a₂ * P.gross ω 0) (p₂ * P.gross ω 1) -
      V2 P (t + 1) (P.next ω) (a₁ * P.gross ω 0) (p₂ * P.gross ω 1)) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hc ω) (hq ω)
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  simp only [V2] at hsum
  have hβ := hS.2.2.2.2.1.le
  have hcross : 0 ≤ P.gamma * SAE P t z * ((a₂ - a₁) * (p₂ - p₁)) :=
    mul_nonneg (mul_nonneg hS.2.2.2.1.le (hsign t z)) (mul_nonneg (by linarith) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ]

/-- The flipped coordinates `(u, p) ↦ (a, p) = (-u, p)` as a two-instrument holding. -/
def orig (x : Fin 2 → ℝ) : Fin (1 + 1) → ℝ := join (-x 0) fun _ => x 1

/-- The flipped fund-and-ETF domain `(-∞, 0] × [0, ∞)`. -/
def Iq : Fin 2 → Set ℝ := ![Set.Iic 0, Set.Ici 0]

/-- The flipped box `[-x̄_A, 0] × [0, x̄_E]`. -/
def Jb (P : M6 (1 + 1) Z Ω) : Fin 2 → Set ℝ := ![Set.Icc (-P.cap 0) 0, Set.Icc 0 (P.cap 1)]

lemma ord_Iq : ∀ i, (Iq i).OrdConnected := fun i => by
  fin_cases i
  · exact Set.ordConnected_Iic
  · exact Set.ordConnected_Ici

omit [Fintype Ω] in
lemma ord_Jb : ∀ i, (Jb P i).OrdConnected := fun i => by
  fin_cases i <;> exact Set.ordConnected_Icc

omit [Fintype Ω] in
lemma orig_sub (x y : Fin 2 → ℝ) : orig y - orig x = join (x 0 - y 0) fun _ => y 1 - x 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [orig, join]; ring
  · rw [Subsingleton.elim j 0]; simp [orig, join]

lemma F_split (t : ℕ) (z : Z) (x y : Fin 2 → ℝ) :
    Novel.M6QuarterlyBandStaticCeilingProof.Fobj P t z (orig x) (orig y) =
      costA P (x 0 - y 0) + c1 (P.kp 1) (P.km 1) (y 1 - x 1) + G2 P t z (-y 0) (y 1) := by
  rw [Novel.M6QuarterlyBandStaticCeilingProof.Fobj, orig_sub, cost_join]; rfl

omit [Fintype Ω] in
lemma mem_Jb {y : Fin 2 → ℝ} : y ∈ Box (Jb P) ↔ orig y ∈ box P := by
  simp only [Box, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_two, Jb, box, orig,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [join]; constructor <;> linarith
    · rw [Subsingleton.elim j 0]; simp [join]; exact ⟨h3, h4⟩
  · intro h
    have h0 := h 0; have h1 := h 1
    simp [join] at h0 h1
    exact ⟨⟨by linarith, by linarith⟩, h1⟩

omit [Fintype Ω] in
lemma orig_of (p : Fin (1 + 1) → ℝ) : orig ![-p 0, p 1] = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [orig, join]
  · rw [Subsingleton.elim j 0]; simp [orig, join]

lemma dd2_cost {k1 k2 : ℝ} (h1 : 0 ≤ k1) (h2 : 0 ≤ k2) (S T : Set ℝ) :
    DD2 (fun s t => c1 k1 k2 (s - t)) S T := by
  have := c1_convex h1 h2 (x := 0)
  simp only [sub_zero] at this
  exact lemmaB this S T

/-- The value step: increasing differences of `G_t` give those of `V_t` (AX-14). -/
lemma V_step (hAX : AX14) (hS : Setting P) {t : ℕ} (ht : t < P.T) (z : Z)
    (hG : IncDiff (G2 P t z) (Set.Ici 0) (Set.Ici 0)) : IncDiff (V2 P t z) (Set.Ici 0) (Set.Ici 0) := by
  set F : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ := fun x y =>
    Novel.M6QuarterlyBandStaticCeilingProof.Fobj P t z (orig x) (orig y)
  set K : Fin 2 ⊕ Fin 2 → Set ℝ := Sum.elim Iq (Jb P)
  have hK : ∀ i, (K i).OrdConnected := fun i => by
    rcases i with i | i
    · exact ord_Iq i
    · exact ord_Jb i
  have hk0 := hS.2.2.2.2.2.2.1 0
  have hk1 := hS.2.2.2.2.2.2.1 1
  have hcA : ∀ u, costA P u = c1 (P.kp 0) (P.km 0) u := fun u => rfl
  -- the three pairwise terms
  have hFt : (fun w : Fin 2 ⊕ Fin 2 → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) =
      fun w => ((fun w => (fun s t => c1 (P.kp 0) (P.km 0) (s - t)) (w (Sum.inl 0)) (w (Sum.inr 0))) w +
        (fun w => (fun s t => c1 (P.kp 1) (P.km 1) (s - t)) (w (Sum.inr 1)) (w (Sum.inl 1))) w) +
        (fun w => (fun u p => G2 P t z (-u) p) (w (Sum.inr 0)) (w (Sum.inr 1))) w := by
    funext w; simp only [F, F_split, hcA, Function.comp]
  have d1 : DD2 (fun s t => c1 (P.kp 0) (P.km 0) (s - t)) (K (Sum.inl 0)) (K (Sum.inr 0)) :=
    dd2_cost hk0.1 hk0.2.2.1 _ _
  have d2 : DD2 (fun s t => c1 (P.kp 1) (P.km 1) (s - t)) (K (Sum.inr 1)) (K (Sum.inl 1)) :=
    dd2_cost hk1.1 hk1.2.2.1 _ _
  have d3 : DD2 (fun u p => G2 P t z (-u) p) (K (Sum.inr 0)) (K (Sum.inr 1)) := by
    have hK0 : K (Sum.inr 0) = (fun a => -a) '' Set.Icc 0 (P.cap 0) := by
      simp only [K, Sum.elim_inr, Jb, Matrix.cons_val_zero]
      rw [Set.image_neg_Icc, neg_zero]
    rw [hK0]
    exact dd2_flip fun a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ h1 h2 =>
      hG a₁ ha₁.1 a₂ ha₂.1 p₁ hp₁.1 p₂ hp₂.1 h1 h2
  have hpw : ∀ i j, i ≠ j → DecDiff (fun w : Fin 2 ⊕ Fin 2 → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) (Box K) i j :=
    fun i j hij => by
      rw [hFt]
      exact dd_add (dd_add (dd_term (by decide) d1 i j hij) (dd_term (by decide) d2 i j hij))
        (dd_term (by decide) d3 i j hij)
  have hsub := (hAX.1 (Fin 2 ⊕ Fin 2) K _).1 hK hpw
  -- attainment
  have hatt : ∀ x ∈ Box Iq, ∃ y ∈ Box (Jb P), ∀ y' ∈ Box (Jb P), F x y ≤ F x y' := by
    intro x _
    obtain ⟨p, hp, hmin, -⟩ := Novel.M6QuarterlyBandStaticCeilingProof.V_attain hS ht z
      (Novel.M6QuarterlyBandStaticCeilingProof.G_facts hS t z).2.2 (orig x)
    refine ⟨![-p 0, p 1], mem_Jb.mpr (by rw [orig_of]; exact hp), fun y' hy' => ?_⟩
    simp only [F, orig_of]
    exact hmin (mem_Jb.mp hy')
  have hV := hAX.2 (Fin 2) (Fin 2) Iq (Jb P) F ord_Iq ord_Jb hsub hatt
  -- the partial minimum is `V_t`
  have hVeq : ∀ x, sInf (F x '' Box (Jb P)) = V2 P t z (-x 0) (x 1) := fun x => by
    simp only [V2]
    rw [Novel.M6QuarterlyBandStaticCeilingProof.V_lt P ht]
    congr 1
    ext r
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨orig y, mem_Jb.mp hy, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨![-p 0, p 1], mem_Jb.mpr (by rw [orig_of]; exact hp), by simp only [F, orig_of]; rfl⟩
  have hdd := (hAX.1 (Fin 2) Iq (fun x => sInf (F x '' Box (Jb P)))).2 ord_Iq hV 0 1 (by decide)
  intro a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ ha hp
  have hm : ∀ s t : ℝ, s ≤ 0 → 0 ≤ t → update (update (0 : Fin 2 → ℝ) 0 s) 1 t ∈ Box Iq :=
    fun s t hs ht => by
      simp only [Box, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_two, Iq,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [update, hs, ht]
  have := hdd 0 (-a₂) (-a₁) p₁ p₂ (by linarith) hp (hm _ _ (by linarith [Set.mem_Ici.mp ha₂]) hp₁)
    (hm _ _ (by linarith [Set.mem_Ici.mp ha₁]) hp₂) (hm _ _ (by linarith [Set.mem_Ici.mp ha₂]) hp₂)
    (hm _ _ (by linarith [Set.mem_Ici.mp ha₁]) hp₁)
  simp only [hVeq] at this
  simp [update] at this
  linarith

/-- Part 2a for `V`: increasing differences at every review, by backward induction. -/
theorem V_ID (hAX : AX14) (hS : Setting P) (hsign : ∀ t z, 0 ≤ SAE P t z) :
    ∀ t z, IncDiff (V2 P t z) (Set.Ici 0) (Set.Ici 0) := by
  suffices h : ∀ k t, P.T - t = k → ∀ z, IncDiff (V2 P t z) (Set.Ici 0) (Set.Ici 0) from
    fun t z => h _ t rfl z
  intro k
  induction k with
  | zero =>
    intro t ht z a₁ _ a₂ _ p₁ _ p₂ _ _ _
    simp only [V2, Novel.M6QuarterlyBandStaticCeilingProof.V_ge P (by omega : P.T ≤ t)]
    rfl
  | succ k ih =>
    intro t ht z
    exact V_step hAX hS (by omega) z (G_ID hS hsign t z fun z' => ih (t + 1) (by omega) z')

/-- The flipped domain `[-x̄_A, 0] × [0, ∞)` for `(u, p⁻)`. -/
def I2 (P : M6 (1 + 1) Z Ω) : Fin 2 → Set ℝ := ![Set.Icc (-P.cap 0) 0, Set.Ici 0]

/-- The ETF box as a one-coordinate product. -/
def J1 (P : M6 (1 + 1) Z Ω) : Fin 1 → Set ℝ := ![Set.Icc 0 (P.cap 1)]

omit [Fintype Ω] in
lemma ord_I2 : ∀ i, (I2 P i).OrdConnected := fun i => by
  fin_cases i
  · exact Set.ordConnected_Icc
  · exact Set.ordConnected_Ici

omit [Fintype Ω] in
lemma ord_J1 : ∀ i, (J1 P i).OrdConnected := fun i => by
  fin_cases i; exact Set.ordConnected_Icc

omit [Fintype Ω] in
lemma J1_eq : Box (J1 P) = ebox P := by
  ext y
  simp only [Box, Set.mem_pi, Set.mem_univ, true_implies, J1, ebox, Set.mem_ofPred_eq]
  constructor
  · intro h j; rw [Subsingleton.elim j 0]; simpa using h 0
  · intro h i; rw [Subsingleton.elim i 0]; simpa using h 0

omit [Fintype Ω] in
lemma fin1_eta (y : Fin 1 → ℝ) : y = fun _ => y 0 := funext fun i => by rw [Subsingleton.elim i 0]

lemma Fe_split (t : ℕ) (z : Z) (x : Fin 2 → ℝ) (y : Fin 1 → ℝ) :
    Fe P t z (fun _ => x 1) (-x 0) y = G2 P t z (-x 0) (y 0) + c1 (P.kp 1) (P.km 1) (y 0 - x 1) := by
  simp only [Fe, G2]
  rw [← fin1_eta y]
  simp [costE, c1]

/-- Part 2a for `U`: increasing differences in `(a, p⁻)` (AX-14). -/
lemma U_ID (hAX : AX14) (hS : Setting P) (t : ℕ) (z : Z)
    (hG : IncDiff (G2 P t z) (Set.Ici 0) (Set.Ici 0)) :
    IncDiff (fun a pm => U P t z (fun _ => pm) a) (Set.Icc 0 (P.cap 0)) (Set.Ici 0) := by
  set F : (Fin 2 → ℝ) → (Fin 1 → ℝ) → ℝ := fun x y => Fe P t z (fun _ => x 1) (-x 0) y
  set K : Fin 2 ⊕ Fin 1 → Set ℝ := Sum.elim (I2 P) (J1 P)
  have hK : ∀ i, (K i).OrdConnected := fun i => by
    rcases i with i | i
    · exact ord_I2 i
    · exact ord_J1 i
  have hk1 := hS.2.2.2.2.2.2.1 1
  have hFt : (fun w : Fin 2 ⊕ Fin 1 → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) =
      fun w => (fun w => (fun u p => G2 P t z (-u) p) (w (Sum.inl 0)) (w (Sum.inr 0))) w +
        (fun w => (fun s r => c1 (P.kp 1) (P.km 1) (s - r)) (w (Sum.inr 0)) (w (Sum.inl 1))) w := by
    funext w; simp only [F, Fe_split, Function.comp]
  have d3 : DD2 (fun u p => G2 P t z (-u) p) (K (Sum.inl 0)) (K (Sum.inr 0)) := by
    have hK0 : K (Sum.inl 0) = (fun a => -a) '' Set.Icc 0 (P.cap 0) := by
      simp only [K, Sum.elim_inl, I2, Matrix.cons_val_zero]
      rw [Set.image_neg_Icc, neg_zero]
    rw [hK0]
    exact dd2_flip fun a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ h1 h2 =>
      hG a₁ ha₁.1 a₂ ha₂.1 p₁ hp₁.1 p₂ hp₂.1 h1 h2
  have d2 : DD2 (fun s r => c1 (P.kp 1) (P.km 1) (s - r)) (K (Sum.inr 0)) (K (Sum.inl 1)) :=
    dd2_cost hk1.1 hk1.2.2.1 _ _
  have hpw : ∀ i j, i ≠ j → DecDiff (fun w : Fin 2 ⊕ Fin 1 → ℝ => F (w ∘ Sum.inl) (w ∘ Sum.inr)) (Box K) i j :=
    fun i j hij => by
      rw [hFt]
      exact dd_add (dd_term (by decide) d3 i j hij) (dd_term (by decide) d2 i j hij)
  have hsub := (hAX.1 (Fin 2 ⊕ Fin 1) K _).1 hK hpw
  have hatt : ∀ x ∈ Box (I2 P), ∃ y ∈ Box (J1 P), ∀ y' ∈ Box (J1 P), F x y ≤ F x y' := by
    intro x _
    obtain ⟨p, hp, hmin, -⟩ := U_attain hS t z (fun _ => x 1) (-x 0)
    exact ⟨p, J1_eq ▸ hp, fun y' hy' => hmin y' (J1_eq ▸ hy')⟩
  have hV := hAX.2 (Fin 2) (Fin 1) (I2 P) (J1 P) F ord_I2 ord_J1 hsub hatt
  have hVeq : ∀ x, sInf (F x '' Box (J1 P)) = U P t z (fun _ => x 1) (-x 0) := fun x => by
    simp only [F, U, J1_eq]
  have hdd := (hAX.1 (Fin 2) (I2 P) (fun x => sInf (F x '' Box (J1 P)))).2 ord_I2 hV 0 1 (by decide)
  intro a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ ha hp
  have hm : ∀ s r : ℝ, -P.cap 0 ≤ s → s ≤ 0 → 0 ≤ r → update (update (0 : Fin 2 → ℝ) 0 s) 1 r ∈ Box (I2 P) :=
    fun s r hs1 hs2 hr => by
      simp only [Box, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_two, I2,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      simp [update, hs1, hs2, hr]
  have := hdd 0 (-a₂) (-a₁) p₁ p₂ (by linarith) hp
    (hm _ _ (by linarith [ha₂.2]) (by linarith [ha₂.1]) hp₁) (hm _ _ (by linarith [ha₁.2]) (by linarith [ha₁.1]) hp₂)
    (hm _ _ (by linarith [ha₂.2]) (by linarith [ha₂.1]) hp₂) (hm _ _ (by linarith [ha₁.2]) (by linarith [ha₁.1]) hp₁)
  simp only [hVeq] at this
  simp [update] at this
  simp only
  linarith

/-- `p ↦ G_t(join a p)` is strictly convex. -/
lemma G2_strict (hS : Setting P) (t : ℕ) (z : Z) (a : ℝ) : StrictConvexOn ℝ Set.univ (G2 P t z a) := by
  have hG := (Novel.M6QuarterlyBandStaticCeilingProof.G_facts hS t z).1
  refine ⟨convex_univ, fun x _ y _ hxy u v hu hv huv => ?_⟩
  have hne : (join a fun _ : Fin 1 => x) ≠ join a fun _ : Fin 1 => y := by
    intro h
    apply hxy
    have := congrFun h (Fin.succ (0 : Fin 1))
    rw [join_succ, join_succ] at this
    exact this
  have h := hG.2 (Set.mem_univ _) (Set.mem_univ _) hne hu hv huv
  have e : u • (join a fun _ : Fin 1 => x) + v • (join a fun _ : Fin 1 => y) =
      join a fun _ : Fin 1 => u * x + v * y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [join]; rw [← add_mul, huv, one_mul]
    · simp [join]
  simp only [G2, smul_eq_mul]
  rw [e] at h
  simpa using h

/-- The fund's minimizers from an incumbent `am` are exactly the clip of `am` to the band. -/
lemma band_min (hS : Setting P) {t : ℕ} (ht : t < P.T) (z : Z) (pm : Fin 1 → ℝ) (am : ℝ) :
    (∀ b, 0 ≤ b → b ≤ P.cap 0 → costA P (min (max am (loU P t z pm)) (hiU P t z pm) - am) +
        U P t z pm (min (max am (loU P t z pm)) (hiU P t z pm)) ≤ costA P (b - am) + U P t z pm b) ∧
    ∀ a, 0 ≤ a → a ≤ P.cap 0 → (∀ b, 0 ≤ b → b ≤ P.cap 0 → costA P (a - am) + U P t z pm a ≤
        costA P (b - am) + U P t z pm b) → a = min (max am (loU P t z pm)) (hiU P t z pm) := by
  obtain ⟨-, -, -, -, -, -, hEB⟩ := effectiveBand 1 Z Ω P hS t z ht pm
  constructor
  · obtain ⟨x', hx'⟩ := Novel.M6QuarterlyBandStaticCeilingProof.opt_exists hS ht z (join am pm)
    rw [join_eta x'] at hx'
    have h1 := ((hEB am _ _).1.mp hx').1
    have h2 := (hEB am _ _).2 hx'
    rw [← h2.1]
    exact h1.2.2
  · intro a ha0 ha1 hmin
    obtain ⟨q, hq, hqmin, -⟩ := U_attain hS t z pm a
    have hopt := (hEB am a q).1.mpr ⟨⟨ha0, ha1, hmin⟩, hq, hqmin⟩
    exact ((hEB am a q).2 hopt).1

theorem mono2 : Monotone2 := by
  intro hAX Z Ω _ P hS hsign t z ht
  have hVID := V_ID hAX hS hsign
  have hGID := G_ID hS hsign t z fun z' => hVID (t + 1) z'
  have hUID := U_ID hAX hS t z hGID
  have hk0 := hS.2.2.2.2.2.2.1 0
  have hk1 := hS.2.2.2.2.2.2.1 1
  have hc0 := hS.2.2.2.2.2.2.2.1 0
  have hc1 := hS.2.2.2.2.2.2.2.1 1
  have hEB := fun pm => effectiveBand 1 Z Ω P hS t z ht pm
  -- the fund's edges
  have fund_edge : ∀ am, 0 ≤ am → am ≤ P.cap 0 → AntitoneOn
      (fun pm => min (max am (loU P t z fun _ => pm)) (hiU P t z fun _ => pm)) (Set.Ici 0) := by
    intro am _ _
    refine argmin_anti (f := fun a pm => costA P (a - am) + U P t z (fun _ => pm) a)
      (S := Set.Icc 0 (P.cap 0)) (fun a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ h1 h2 => ?_) (fun pm _ => ?_)
      (fun pm _ a ha => ?_) (fun pm _ a ha hmin => ?_)
    · have := hUID a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ h1 h2
      simp only at this ⊢; linarith
    · obtain ⟨_, _, _, h0, hlh, hh1, _⟩ := hEB (fun _ => pm)
      exact ⟨le_min (h0.trans (le_max_right _ _)) (h0.trans hlh), (min_le_right _ _).trans hh1⟩
    · exact (band_min hS ht z _ am).1 a ha.1 ha.2
    · exact (band_min hS ht z _ am).2 a ha.1 ha.2 fun b hb0 hb1 => hmin b ⟨hb0, hb1⟩
  have lo_eq : ∀ pm : ℝ, min (max 0 (loU P t z fun _ => pm)) (hiU P t z fun _ => pm) = loU P t z fun _ => pm :=
    fun pm => by
      obtain ⟨_, _, _, h0, hlh, _, _⟩ := hEB (fun _ => pm)
      rw [max_eq_right h0, min_eq_left hlh]
  have hi_eq : ∀ pm : ℝ, min (max (P.cap 0) (loU P t z fun _ => pm)) (hiU P t z fun _ => pm) =
      hiU P t z fun _ => pm := fun pm => by
    obtain ⟨_, _, _, _, hlh, hh1, _⟩ := hEB (fun _ => pm)
    rw [max_eq_left (hlh.trans hh1), min_eq_right hh1]
  -- the ETF's edges
  have hconv : ∀ a, ConvexOn ℝ Set.univ (G2 P t z a) := fun a => (G2_strict hS t z a).convexOn
  have etf_edge : ∀ x, 0 ≤ x → x ≤ P.cap 1 → AntitoneOn
      (fun a => projF (G2 P t z a) (P.kp 1) (P.km 1) (P.cap 1) x) (Set.Icc 0 (P.cap 0)) := by
    intro x _ _
    refine argmin_anti (f := fun p a => c1 (P.kp 1) (P.km 1) (p - x) + G2 P t z a p)
      (S := Set.Icc 0 (P.cap 1)) (fun p₁ hp₁ p₂ hp₂ a₁ ha₁ a₂ ha₂ h1 h2 => ?_) (fun a _ => ?_)
      (fun a _ p hp => ?_) (fun a _ p hp hmin => ?_)
    · have := hGID a₁ ha₁.1 a₂ ha₂.1 p₁ hp₁.1 p₂ hp₂.1 h2 h1
      simp only [G2] at this ⊢; linarith
    · exact projF_mem (hconv a) hk1.1 hk1.2.2.1 hc1 x
    · exact optF (hconv a) hk1.1 hk1.2.2.1 hc1 x hp.1 hp.2
    · exact min_unique hk1.1 hk1.2.2.1 (G2_strict hS t z a) x hp
        (projF_mem (hconv a) hk1.1 hk1.2.2.1 hc1 x) (fun y hy0 hyc => hmin y ⟨hy0, hyc⟩)
        (fun y hy0 hyc => optF (hconv a) hk1.1 hk1.2.2.1 hc1 x hy0 hyc)
  have loE_eq : ∀ a, projF (G2 P t z a) (P.kp 1) (P.km 1) (P.cap 1) 0 = loE P t z a := fun a => by
    have h0 := (loF_bounds (f := G2 P t z a) (kp := P.kp 1) hc1).1
    have hlh := loF_le_hiF (hconv a) hk1.1 hk1.2.2.1 hc1
    simp only [projF, max_eq_right h0, min_eq_left hlh]; rfl
  have hiE_eq : ∀ a, projF (G2 P t z a) (P.kp 1) (P.km 1) (P.cap 1) (P.cap 1) = hiE P t z a := fun a => by
    have h1 := (hiF_bounds (f := G2 P t z a) (km := P.km 1) hc1).2
    have hlh := loF_le_hiF (hconv a) hk1.1 hk1.2.2.1 hc1
    simp only [projF, max_eq_left (hlh.trans h1), min_eq_right h1]; rfl
  refine ⟨hVID t z, fun a₁ ha₁ a₂ ha₂ p₁ hp₁ p₂ hp₂ h1 h2 =>
      hGID a₁ ha₁.1 a₂ ha₂.1 p₁ hp₁.1 p₂ hp₂.1 h1 h2, hUID,
    fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_,
    fun x hx y hy hxy => ?_, fun a p => ?_⟩
  · have := fund_edge 0 le_rfl hc0.le hx hy hxy; simp only [lo_eq] at this; exact this
  · have := fund_edge (P.cap 0) hc0.le le_rfl hx hy hxy; simp only [hi_eq] at this; exact this
  · have := etf_edge 0 le_rfl hc1.le hx hy hxy; simp only [loE_eq] at this; exact this
  · have := etf_edge (P.cap 1) hc1.le le_rfl hx hy hxy; simp only [hiE_eq] at this; exact this
  · -- the region
    obtain ⟨_, _, _, h0, hlh, hh1, hIso⟩ := hEB (fun _ => p)
    constructor
    · rintro ⟨hbox, hopt⟩
      have hb0 : 0 ≤ a ∧ a ≤ P.cap 0 := hbox 0
      have hb1 : 0 ≤ p ∧ p ≤ P.cap 1 := hbox 1
      have hclip := ((hIso a a (fun _ => p)).2 hopt).2.mp rfl
      have hE := ((hIso a a (fun _ => p)).1.mp hopt).2
      -- the ETF holding `p` minimizes, so it is its own clip
      have hmin : ∀ y, 0 ≤ y → y ≤ P.cap 1 → c1 (P.kp 1) (P.km 1) (p - p) + G2 P t z a p ≤
          c1 (P.kp 1) (P.km 1) (y - p) + G2 P t z a y := fun y hy0 hyc => by
        have := hE.2 (fun _ => y) (by intro j; rw [Subsingleton.elim j 0]; exact ⟨hy0, hyc⟩)
        simpa [Fe, G2, costE, c1, add_comm] using this
      have hp := min_unique hk1.1 hk1.2.2.1 (G2_strict hS t z a) p ⟨hb1.1, hb1.2⟩
        (projF_mem (hconv a) hk1.1 hk1.2.2.1 hc1 p) hmin
        (fun y hy0 hyc => optF (hconv a) hk1.1 hk1.2.2.1 hc1 p hy0 hyc)
      have hlhE := loF_le_hiF (hconv a) hk1.1 hk1.2.2.1 hc1
      refine ⟨⟨hb0.1, hb0.2, hb1.1, hb1.2⟩, hclip.1, hclip.2, ?_, ?_⟩
      · rw [hp]; exact le_min (le_max_right _ _) hlhE
      · rw [hp]; exact min_le_right _ _
    · rintro ⟨⟨ha0, ha1, hp0, hp1⟩, hl, hh, hlE, hhE⟩
      have hboxj : (join a fun _ => p) ∈ box P := fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨ha0, ha1⟩
        · rw [Subsingleton.elim j 0]; exact ⟨hp0, hp1⟩
      refine ⟨hboxj, (hIso a a (fun _ => p)).1.mpr ⟨⟨ha0, ha1, ?_⟩, fun j => by
        rw [Subsingleton.elim j 0]; exact ⟨hp0, hp1⟩, ?_⟩⟩
      · have := (band_min hS ht z (fun _ => p) a).1
        rwa [max_eq_left hl, min_eq_left hh] at this
      · intro q hq
        have hpp : projF (G2 P t z a) (P.kp 1) (P.km 1) (P.cap 1) p = p := by
          simp only [projF]
          rw [max_eq_left (show loF (G2 P t z a) (P.kp 1) (P.cap 1) ≤ p from hlE),
            min_eq_left (show p ≤ hiF (G2 P t z a) (P.km 1) (P.cap 1) from hhE)]
        have := optF (hconv a) hk1.1 hk1.2.2.1 hc1 p (hq 0).1 (hq 0).2
        rw [hpp] at this
        rw [fin1_eta q]
        simpa [Fe, G2, costE, c1, add_comm] using this

end Part2

theorem proof : Standalone.M7DynamicBundlingShape.statement :=
  ⟨edges, bend, widths, staticShape, mono2, frozen, idleVariance, lastFree⟩

end

end Novel.M7DynamicBundlingShapeProof

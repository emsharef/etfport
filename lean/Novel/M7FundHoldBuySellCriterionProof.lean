import Novel.M7TwoStageExactnessLossProof
import Novel.M6QuarterlyBandStaticCeilingProof
import Standalone.M7FundHoldBuySellCriterion

/-!
# Claim 102: proof

Part 1 is claim 104's part 0 (the AX-13 application), with uniqueness from strict concavity and the
per-instrument readings from the slope sets and box signs. Part 2 compares the full and ETF-only
optima through that criterion. Part 3 reads claim 104's 2a through the clip of the band holding.
Parts 4-5(a): at the optimum the ETF lines give `g_E = η 1 + (1 + η) t_E`, and claim 104's fund line
turns fund `i`'s `R_i` into `A_i - η(1 - Σ_j r_ij) - (1 + η)(t_i - r_i't_E)`; `r_i't_E` lies in
`[-h⁺_i, h⁻_i]`, with the ends attained under the re-hedges.
-/

namespace Novel.M7FundHoldBuySellCriterionProof

open Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M7FundHoldBuySellCriterion Novel.M7TwoStageExactnessLossProof
open Standalone.M2TwoStageSeparation (Inputs)

noncomputable section

variable {S : Type} [Fintype S]

/-! ### Part 1 -/

omit [Fintype S] in
lemma w0_nonneg {m n K : ℕ} {D : Data m n K S} (hI : Inputs D) (l : Inst m n) : 0 ≤ w0 D l :=
  div_nonneg (hI.1.2.1 l) hI.1.1.le

/-- Strict concavity at the midpoint: `Q(mid) ≥ (Q(x) + Q(y))/2 + (γ/8)(x - y)'Σ(x - y)`. -/
lemma score_mid {m n K : ℕ} {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
    (x y : Inst m n → ℝ) :
    (score D x θ + score D y θ) / 2 + D.gamma / 8 * ((x - y) ⬝ᵥ (covariance D *ᵥ (x - y))) ≤
      score D ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) θ := by
  have hs : ∀ w, score D w θ = mu D θ ⬝ᵥ w - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) -
      tau D (w - w0 D) := fun w => by rw [mu_dot]; rfl
  have ht := Novel.M2ActionClassesProof.tau_convex D hI.2.1 (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (x - w0 D) (y - w0 D)
  rw [← Novel.M2ActionClassesProof.comb_sub x y (w0 D) (by norm_num)] at ht
  have hq : ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ⬝ᵥ (covariance D *ᵥ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) =
      (x ⬝ᵥ (covariance D *ᵥ x) + y ⬝ᵥ (covariance D *ᵥ y)) / 2 -
        ((x - y) ⬝ᵥ (covariance D *ᵥ (x - y))) / 4 := by
    rw [Novel.M2ActionClassesProof.quad_eq, Novel.M2ActionClassesProof.quad_eq,
      Novel.M2ActionClassesProof.quad_eq, Novel.M2ActionClassesProof.quad_eq]
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, sub_dotProduct]
    rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hs, hs, hs, hq, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  nlinarith [hI.2.2.2]

lemma unique_max {m n K : ℕ} {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
    (hSig : (covariance D).PosDef) (hγ : 0 < D.gamma) {w₁ w₂ : Inst m n → ℝ} (h₁ : w₁ ∈ F D) (h₂ : w₂ ∈ F D)
    (hm₁ : IsMaxOn (fun w => score D w θ) (F D) w₁) (hm₂ : IsMaxOn (fun w => score D w θ) (F D) w₂) :
    w₁ = w₂ := by
  have hmid : (1 / 2 : ℝ) • w₁ + (1 / 2 : ℝ) • w₂ ∈ F D :=
    Novel.M2TwoStageSeparationProof.F_convex hI h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  have a1 : score D ((1 / 2 : ℝ) • w₁ + (1 / 2 : ℝ) • w₂) θ ≤ score D w₁ θ := hm₁ hmid
  have a2 : score D w₂ θ ≤ score D w₁ θ := hm₁ h₂
  have a3 : score D w₁ θ ≤ score D w₂ θ := hm₂ h₁
  have hsm := score_mid θ hI w₁ w₂
  have hQ : (w₁ - w₂) ⬝ᵥ (covariance D *ᵥ (w₁ - w₂)) ≤ 0 := by
    have : D.gamma / 8 * ((w₁ - w₂) ⬝ᵥ (covariance D *ᵥ (w₁ - w₂))) ≤ 0 := by linarith
    by_contra h; push Not at h
    have := mul_pos (by positivity : 0 < D.gamma / 8) h; linarith
  by_contra hne
  have := hSig.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  simp only [star_trivial] at this
  linarith

theorem criterion : Criterion := by
  intro m n K S _ D θ hI hSig hγ
  refine ⟨Novel.M2TwoStageSeparationProof.J_attain θ hI, fun w₁ h₁ w₂ h₂ hm₁ hm₂ =>
    unique_max θ hI hSig hγ h₁ h₂ hm₁ hm₂, fun hAX w hw =>
      ⟨jointOptimality hAX m n K S D θ hI w hw, fun hmax => ?_⟩⟩
  obtain ⟨η, t, hη, hηk, ht, hR⟩ := (jointOptimality hAX m n K S D θ hI w hw).mp hmax
  refine ⟨η, hη, hηk, fun l => ?_⟩
  obtain ⟨t1, t2, tp, tm⟩ := ht l
  obtain ⟨b1, b2⟩ := hR l
  have hw0 := w0_nonneg hI l
  have hwb : w0 D l ≤ D.wbar l := hI.1.2.2.2 l
  have h1η : 0 ≤ 1 + η := by linarith
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_,
    fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩
  · have := b1 h2; have := b2 (by linarith); rw [tp h1] at *; linarith
  · have := b2 (by linarith); rw [tp h1] at this; linarith
  · have := b1 (by linarith); have := b2 h2; rw [tm h1] at *; linarith
  · have := b1 (by linarith); rw [tm h1] at this; linarith
  · have e1 := b1 h3; have e2 := b2 h2
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left t1 h1η, mul_le_mul_of_nonneg_left t2 h1η]
  · have := b1 h3; nlinarith [mul_le_mul_of_nonneg_left t2 h1η]
  · have := b2 h2; nlinarith [mul_le_mul_of_nonneg_left t1 h1η]

/-! ### Part 2 -/

theorem etfTest : EtfTest := by
  intro hAX m n K S _ D θ hI hSig hγ xE hxE hmaxE w hw hmax
  have hcrit := jointOptimality hAX m n K S D θ hI xE hxE.1
  have hfund : ∀ i, xE (Sum.inl i) = w0 D (Sum.inl i) := fun i => congrFun hxE.2 i
  constructor
  · intro hact
    have hwE : w ∈ E0 D := ⟨hw, hact⟩
    have hmaxF : IsMaxOn (fun w => score D w θ) (F D) xE := fun y hy => by
      show score D y θ ≤ score D xE θ
      exact (hmax hy).trans (hmaxE hwE)
    obtain ⟨η, t, hη, hηk, ht, hR⟩ := hcrit.mp hmaxF
    refine ⟨η, ⟨hη, hηk, fun j => ⟨t (Sum.inr j), ht _, hR _⟩⟩, fun i =>
      ⟨t (Sum.inl i), (ht _).1, (ht _).2.1, hR _⟩⟩
  · rintro ⟨η, ⟨hη, hηk, hj⟩, hi⟩
    choose te hte hRe using hj
    choose ta hta1 hta2 hRa using hi
    have hmaxF : IsMaxOn (fun w => score D w θ) (F D) xE := by
      refine hcrit.mpr ⟨η, Sum.elim ta te, hη, hηk, ?_, ?_⟩
      · rintro (i | j)
        · refine ⟨hta1 i, hta2 i, fun h => ?_, fun h => ?_⟩ <;> rw [hfund i] at h <;> exact absurd h (lt_irrefl _)
        · exact hte j
      · rintro (i | j)
        · exact hRa i
        · exact hRe j
    have := unique_max θ hI hSig hγ hw hxE.1 hmax hmaxF
    rw [this]; exact hxE.2

/-! ### Part 3 -/

section Clip

variable {c kp km xm xbar : ℝ}

lemma above_iff (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) (al : ℝ) :
    xm < bandHold al c kp km xm xbar ↔ xm < (al - kp) / c ∧ xm < xbar := by
  constructor
  · intro h
    refine ⟨?_, h.trans_le (bandHold_mem (h0.trans h1)).2⟩
    by_contra hle
    push Not at hle
    have hu : max ((al - kp) / c) (min ((al + km) / c) xm) ≤ xm := max_le hle (min_le_right _ _)
    have : bandHold al c kp km xm xbar ≤ xm := by
      unfold bandHold
      exact max_le h0 ((min_le_right _ _).trans hu)
    linarith
  · rintro ⟨hlo, hx⟩
    unfold bandHold
    rw [max_eq_left ((min_le_right _ _).trans hlo.le)]
    exact lt_of_lt_of_le (lt_min hx hlo) (le_max_right _ _)

lemma below_iff (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (al : ℝ) :
    bandHold al c kp km xm xbar < xm ↔ (al + km) / c < xm ∧ 0 < xm := by
  have hlh : (al - kp) / c ≤ (al + km) / c := div_le_div_of_nonneg_right (by linarith) hc.le
  constructor
  · intro h
    refine ⟨?_, (bandHold_mem (h0.trans h1)).1.trans_lt h⟩
    by_contra hle
    push Not at hle
    have hu : xm ≤ max ((al - kp) / c) (min ((al + km) / c) xm) :=
      (le_min hle le_rfl).trans (le_max_right _ _)
    have : xm ≤ bandHold al c kp km xm xbar := by
      unfold bandHold
      exact (le_min h1 hu).trans (le_max_right _ _)
    linarith
  · rintro ⟨hhi, hx⟩
    unfold bandHold
    rw [min_eq_left hhi.le, max_eq_right hlh]
    exact max_lt hx (lt_of_le_of_lt (min_le_right _ _) hhi)

end Clip

theorem spanningRule : SpanningRule := by
  intro m K S _ D θ Sf v hI hFS wJ hwJ hmaxJ hk hE
  obtain ⟨hbJ, hfund, hetf, -⟩ := spanning m K S D θ Sf v hI hFS wJ hwJ hmaxJ hk hE
  obtain ⟨-, hBE, -, -, hv, -, hγ⟩ := hFS
  have hU : IsUnit D.BEᵀ.det := by rwa [det_transpose]
  refine ⟨fun i => ?_, ?_⟩
  · have hc : 0 < D.gamma * v i := mul_pos hγ (hv i)
    have hkp := (hI.2.1 (Sum.inl i)).1
    have hkm := (hI.2.1 (Sum.inl i)).2
    have hw0 := w0_nonneg hI (Sum.inl i)
    have hwb : w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := hI.1.2.2.2 _
    have hA := above_iff (c := D.gamma * v i) (kp := D.kplus (Sum.inl i)) (km := D.kminus (Sum.inl i)) hw0 hwb (θ.alpha i)
    have hB := below_iff hw0 hwb hc hkp hkm (θ.alpha i)
    rw [← hfund i] at hA hB
    have e1 : w0 D (Sum.inl i) < (θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i) ↔
        D.kplus (Sum.inl i) < θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) := by
      rw [lt_div_iff₀ hc]; constructor <;> intro h <;> linarith
    have e2 : (θ.alpha i + D.kminus (Sum.inl i)) / (D.gamma * v i) < w0 D (Sum.inl i) ↔
        θ.alpha i - D.gamma * v i * w0 D (Sum.inl i) < -D.kminus (Sum.inl i) := by
      rw [div_lt_iff₀ hc]; constructor <;> intro h <;> linarith
    refine ⟨hfund i, by rw [hA, e1], by rw [hB, e2], fun hz hx => ?_, fun hz hα => ?_, fun hpos => ?_⟩
    · rw [hz] at hA e1; rw [hA, e1]; simp [hx]
    · rw [hfund i, hz]
      unfold bandHold
      have h1 : (θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
      have h2 : max ((θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i))
          (min ((θ.alpha i + D.kminus (Sum.inl i)) / (D.gamma * v i)) 0) ≤ 0 :=
        max_le h1 (min_le_right _ _)
      exact le_antisymm (max_le le_rfl ((min_le_right _ _).trans h2)) (le_max_left _ _)
    · rw [hfund i]
      have hxb : 0 < D.wbar (Sum.inl i) := hpos.trans_le hwb
      have hlh : (θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i) ≤
          (θ.alpha i + D.kminus (Sum.inl i)) / (D.gamma * v i) :=
        div_le_div_of_nonneg_right (by linarith) hc.le
      unfold bandHold
      set lo := (θ.alpha i - D.kplus (Sum.inl i)) / (D.gamma * v i)
      set hi := (θ.alpha i + D.kminus (Sum.inl i)) / (D.gamma * v i)
      have ehi : hi ≤ 0 ↔ θ.alpha i ≤ -D.kminus (Sum.inl i) := by
        simp only [hi]; rw [div_nonpos_iff]; constructor
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · linarith [hc]
          · linarith
        · intro h; exact Or.inr ⟨by linarith, hc.le⟩
      rw [← ehi]
      constructor
      · intro h0
        have hm : min (D.wbar (Sum.inl i)) (max lo (min hi (w0 D (Sum.inl i)))) ≤ 0 := by
          have := le_max_right 0 (min (D.wbar (Sum.inl i)) (max lo (min hi (w0 D (Sum.inl i)))))
          linarith
        have hu : max lo (min hi (w0 D (Sum.inl i))) ≤ 0 := by
          rcases min_le_iff.mp hm with h | h
          · linarith
          · exact h
        have := (le_max_right lo (min hi (w0 D (Sum.inl i)))).trans hu
        rcases min_le_iff.mp this with h | h
        · exact h
        · linarith
      · intro h0
        have hu : max lo (min hi (w0 D (Sum.inl i))) ≤ 0 :=
          max_le (hlh.trans h0) ((min_le_left _ _).trans h0)
        exact le_antisymm (max_le le_rfl ((min_le_right _ _).trans hu)) (le_max_left _ _)
  · -- the netting decomposition
    have h0 : etf (w0 D) = (D.BEᵀ)⁻¹ *ᵥ (exposure D (w0 D) - D.BAᵀ *ᵥ active (w0 D)) := by
      show etf (w0 D) = (D.BEᵀ)⁻¹ *ᵥ (D.BAᵀ *ᵥ active (w0 D) + D.BEᵀ *ᵥ etf (w0 D) - D.BAᵀ *ᵥ active (w0 D))
      rw [add_sub_cancel_left, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
    have hs : ∑ i, (wJ (Sum.inl i) - w0 D (Sum.inl i)) • ((D.BEᵀ)⁻¹ *ᵥ D.BA i) =
        (D.BEᵀ)⁻¹ *ᵥ (D.BAᵀ *ᵥ (fun i => wJ (Sum.inl i) - w0 D (Sum.inl i))) := by
      rw [bat_sum D (fun i => wJ (Sum.inl i) - w0 D (Sum.inl i)), mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mulVec_smul]
    have ha : (fun i => wJ (Sum.inl i) - w0 D (Sum.inl i)) = active wJ - active (w0 D) := rfl
    rw [hs, hetf, h0, ← hbJ, ha, mulVec_sub D.BAᵀ, ← mulVec_sub, ← mulVec_sub]
    congr 1
    abel

/-! ### Parts 4-5(a) -/

omit [Fintype S] in
/-- `r't ∈ [-h⁺, h⁻]` for slopes in the rate intervals. -/
lemma rt_bounds {m K : ℕ} {D : Data m K K S} (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l)
    (r t : Fin K → ℝ) (ht : ∀ j, -D.kminus (Sum.inr j) ≤ t j ∧ t j ≤ D.kplus (Sum.inr j)) :
    -hPlus D r ≤ r ⬝ᵥ t ∧ r ⬝ᵥ t ≤ hMinus D r := by
  simp only [hPlus, hMinus, dotProduct, ← Finset.sum_neg_distrib]
  constructor <;> refine Finset.sum_le_sum fun j _ => ?_ <;> obtain ⟨a1, a2⟩ := ht j <;>
    obtain ⟨k1, k2⟩ := hr (Sum.inr j) <;> rcases le_total 0 (r j) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith
  · rw [max_eq_left h, max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith

/-- The core: at the optimum with interior ETFs, `R_i = A'_i - (1 + η)(t_i - r_i't_E)`. -/
lemma core (hAX : AX13) {m K : ℕ} {D : Data m K K S} (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ}
    {v : Fin m → ℝ} {SE : Matrix (Fin K) (Fin K) ℝ} (hI : Inputs D) (hR : RefCase D Sf (diagonal v) SE)
    (hBE : IsUnit D.BE.det) {x : Inst m K → ℝ} (hx : x ∈ F D)
    (hmax : IsMaxOn (fun w => score D w θ) (F D) x)
    (hE : ∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) :
    ∃ (η : ℝ) (t : Inst m K → ℝ), 0 ≤ η ∧ η * cash D x = 0 ∧ (∀ l, InSlope D x l (t l)) ∧
      ∀ i, BoxSign (D.wbar (Sum.inl i)) (x (Sum.inl i))
        (Ared D θ v SE x i - η * (1 - ∑ j, rvec D i j) -
          (1 + η) * (t (Sum.inl i) - rvec D i ⬝ᵥ (fun j => t (Sum.inr j)))) := by
  obtain ⟨η, t, hη, hηk, ht, hRb⟩ := (jointOptimality hAX m K K S D θ hI x hx).mp hmax
  refine ⟨η, t, hη, hηk, ht, fun i => ?_⟩
  have hEl : ∀ j, (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D x))) j - D.cE j -
      D.gamma * (SE *ᵥ etf x) j = η + (1 + η) * t (Sum.inr j) := fun j => by
    have h1 := (hRb (Sum.inr j)).1 (hE j).2
    have h2 := (hRb (Sum.inr j)).2 (hE j).1
    rw [grad_etf θ hR] at h1 h2
    linarith
  have hfl := fund_line θ hR hBE rfl η t hEl i
  have e : Ared D θ v SE x i - η * (1 - ∑ j, rvec D i j) -
      (1 + η) * (t (Sum.inl i) - rvec D i ⬝ᵥ (fun j => t (Sum.inr j))) =
      grad D θ x (Sum.inl i) - η - (1 + η) * t (Sum.inl i) := by
    rw [hfl]
    simp only [Ared, rvec, mulVec_diagonal, active, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  rw [e]; exact hRb (Sum.inl i)

/-- The core with its pieces: the ETF lines and the fund-line identity. -/
lemma core2 (hAX : AX13) {m K : ℕ} {D : Data m K K S} (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ}
    {v : Fin m → ℝ} {SE : Matrix (Fin K) (Fin K) ℝ} (hI : Inputs D) (hR : RefCase D Sf (diagonal v) SE)
    (hBE : IsUnit D.BE.det) {x : Inst m K → ℝ} (hx : x ∈ F D)
    (hmax : IsMaxOn (fun w => score D w θ) (F D) x)
    (hE : ∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) :
    ∃ (η : ℝ) (t : Inst m K → ℝ), 0 ≤ η ∧ η * cash D x = 0 ∧ (∀ l, InSlope D x l (t l)) ∧
      (∀ l, BoxSign (D.wbar l) (x l) (grad D θ x l - η - (1 + η) * t l)) ∧
      (∀ j, (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D x))) j - D.cE j -
        D.gamma * (SE *ᵥ etf x) j = η + (1 + η) * t (Sum.inr j)) ∧
      ∀ i, grad D θ x (Sum.inl i) - η - (1 + η) * t (Sum.inl i) =
        Ared D θ v SE x i - η * (1 - ∑ j, rvec D i j) -
          (1 + η) * (t (Sum.inl i) - rvec D i ⬝ᵥ (fun j => t (Sum.inr j))) := by
  obtain ⟨η, t, hη, hηk, ht, hRb⟩ := (jointOptimality hAX m K K S D θ hI x hx).mp hmax
  have hEl : ∀ j, (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D x))) j - D.cE j -
      D.gamma * (SE *ᵥ etf x) j = η + (1 + η) * t (Sum.inr j) := fun j => by
    have h1 := (hRb (Sum.inr j)).1 (hE j).2
    have h2 := (hRb (Sum.inr j)).2 (hE j).1
    rw [grad_etf θ hR] at h1 h2
    linarith
  refine ⟨η, t, hη, hηk, ht, hRb, hEl, fun i => ?_⟩
  rw [fund_line θ hR hBE rfl η t hEl i]
  simp only [Ared, rvec, mulVec_diagonal, active, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

lemma pur_rt {m K : ℕ} {D : Data m K K S} {x : Inst m K → ℝ} {t : Inst m K → ℝ} {r : Fin K → ℝ}
    (ht : ∀ l, InSlope D x l (t l)) (hp : PurchaseHedge D x r) :
    r ⬝ᵥ (fun j => t (Sum.inr j)) = -hPlus D r := by
  simp only [hPlus, dotProduct, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨p1, p2⟩ := hp j
  rcases lt_trichotomy (r j) 0 with h | h | h
  · rw [(ht (Sum.inr j)).2.2.1 (p2 h), max_eq_right h.le, max_eq_left (by linarith)]; ring
  · rw [h]; simp
  · rw [(ht (Sum.inr j)).2.2.2 (p1 h), max_eq_left h.le, max_eq_right (by linarith)]; ring

theorem pinned : Pinned := by
  intro hAX m K S _ D θ Sf v SE hI hR hBE x hx hmax hE
  obtain ⟨η, t, hη, hηk, ht, hRb, -, hid⟩ := core2 hAX θ hI hR hBE hx hmax hE
  refine ⟨η, hη, hηk, fun i => ?_⟩
  intro r A' tE
  have h1η : 0 < 1 + η := by linarith
  have hw0 := w0_nonneg hI (Sum.inl i)
  have hwb : w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := hI.1.2.2.2 _
  obtain ⟨b1, b2⟩ := hRb (Sum.inl i)
  rw [hid i] at b1 b2
  obtain ⟨t1, t2, tp, tm⟩ := ht (Sum.inl i)
  refine ⟨fun hpin => ?_, fun hp he h0 h1 hg => ?_⟩
  · have hrt : r ⬝ᵥ (fun j => t (Sum.inr j)) = r ⬝ᵥ tE := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hr0 : r j = 0
      · rw [hr0, zero_mul, zero_mul]
      · congr 1
        rcases lt_or_gt_of_ne (hpin j hr0) with h | h
        · simp only [tE, not_lt.mpr h.le, ↓reduceIte]; exact (ht (Sum.inr j)).2.2.2 h
        · simp only [tE, h, ↓reduceIte]; exact (ht (Sum.inr j)).2.2.1 h
    rw [hrt] at b1 b2
    refine ⟨fun hb hc => ?_, fun hb hc => ?_, fun hs h0 => ?_, fun hs h0 => ?_⟩
    · have e1 := b1 hc; have e2 := b2 (by linarith); rw [tp hb] at e1 e2; linarith
    · have e2 := b2 (by linarith); rw [tp hb] at e2; linarith
    · have e1 := b1 (by linarith); have e2 := b2 h0; rw [tm hs] at e1 e2; linarith
    · have e1 := b1 (by linarith); rw [tm hs] at e1; linarith
  · have e0 : grad D θ x (Sum.inl i) - η - (1 + η) * t (Sum.inl i) = 0 :=
      le_antisymm ((hRb (Sum.inl i)).1 h1) ((hRb (Sum.inl i)).2 h0)
    have hti : t (Sum.inl i) = D.kplus (Sum.inl i) := by
      rw [hg] at e0
      have : (1 + η) * (D.kplus (Sum.inl i) - t (Sum.inl i)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have e1 := b1 h1; have e2 := b2 h0
    rw [hti, pur_rt ht hp] at e1 e2
    show A' = _
    linarith

theorem budgetStrip : BudgetStrip := by
  intro hAX m K S _ D θ Sf v hI hFS x hx hmax hE
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ⟩ := hFS
  obtain ⟨η, t, hη, hηk, ht, hRb, hEl, hid⟩ := core2 hAX θ hI hR hBE hx hmax hE
  have h1η : 0 < 1 + η := by linarith
  have ht0 : ∀ j, t (Sum.inr j) = 0 := fun j => by
    obtain ⟨a1, a2, -, -⟩ := ht (Sum.inr j)
    rw [(hkE j).1] at a2; rw [(hkE j).2] at a1; linarith
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  refine ⟨η, hη, hηk, ?_, fun i => ?_⟩
  · -- the exposure: the ETF lines read `B^E e = η 1`
    have hBEe : D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D x)) = η • fun _ => 1 := by
      funext j
      have := hEl j
      rw [ht0, hcE, zero_mulVec] at this
      simp only [Pi.zero_apply, sub_zero, mul_zero, add_zero] at this
      simp [this]
    have he : θ.lam - D.gamma • (Sf *ᵥ exposure D x) = η • (D.BE⁻¹ *ᵥ fun _ => 1) := by
      have := congrArg (D.BE⁻¹ *ᵥ ·) hBEe
      simpa [mulVec_mulVec, nonsing_inv_mul _ hBE, mulVec_smul] using this
    have hb : (D.gamma • Sf) *ᵥ exposure D x = θ.lam - η • (D.BE⁻¹ *ᵥ fun _ => 1) := by
      rw [smul_mulVec, ← he]; abel
    rw [← hb, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  · intro sr
    have hc : 0 < D.gamma * v i := mul_pos hγ (hv i)
    have hkp := (hI.2.1 (Sum.inl i)).1
    have hkm := (hI.2.1 (Sum.inl i)).2
    have hw0 := w0_nonneg hI (Sum.inl i)
    have hwb : w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := hI.1.2.2.2 _
    obtain ⟨b1, b2⟩ := hRb (Sum.inl i)
    rw [hid i] at b1 b2
    have hA : Ared D θ v 0 x i = θ.alpha i - D.gamma * v i * x (Sum.inl i) := by
      simp [Ared, hcE]
    have hrt : rvec D i ⬝ᵥ (fun j => t (Sum.inr j)) = 0 := by simp [dotProduct, ht0]
    rw [hA, hrt, sub_zero] at b1 b2
    obtain ⟨t1, t2, tp, tm⟩ := ht (Sum.inl i)
    -- `x_i` maximizes the shifted one-variable objective
    have hmaxψ : IsMaxOn (psi (θ.alpha i - η * (1 - sr)) (D.gamma * v i) ((1 + η) * D.kplus (Sum.inl i))
        ((1 + η) * D.kminus (Sum.inl i)) (w0 D (Sum.inl i))) (Set.Icc 0 (D.wbar (Sum.inl i)))
        (x (Sum.inl i)) := by
      refine max_of_slope (t := (1 + η) * t (Sum.inl i)) hc (by nlinarith) (by nlinarith)
        (fun h => by rw [tp h]) (fun h => by rw [tm h]; ring) fun a ha => ?_
      rcases lt_trichotomy a (x (Sum.inl i)) with h | h | h
      · have := b2 (by linarith [ha.1])
        nlinarith
      · rw [h, sub_self, mul_zero]
      · have := b1 (by linarith [ha.2])
        nlinarith
    have hxi := eq_bandHold hc (by positivity) (by positivity) (hx.1 (Sum.inl i)) hmaxψ
    refine ⟨hxi, ?_, ?_⟩
    · rw [hxi, above_iff (c := D.gamma * v i) (kp := (1 + η) * D.kplus (Sum.inl i))
        (km := (1 + η) * D.kminus (Sum.inl i)) hw0 hwb, lt_div_iff₀ hc]
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩
    · rw [hxi, below_iff hw0 hwb hc (by positivity) (by positivity), div_lt_iff₀ hc]
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩

theorem reHedge : ReHedge := by
  intro hAX m K S _ D θ Sf v SE hI hR hBE x hx hmax hE
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  obtain ⟨η, t, hη, hηk, ht, hRb⟩ := core hAX θ hI hR hBE hx hmax hE
  refine ⟨η, hη, hηk, fun i => ?_⟩
  intro r A' kp km
  have h1η : 0 ≤ 1 + η := by linarith
  have hw0 := w0_nonneg hI (Sum.inl i)
  have hwb : w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := hI.1.2.2.2 _
  obtain ⟨b1, b2⟩ := hRb i
  have hbnd := rt_bounds hr r (fun j => t (Sum.inr j)) fun j => ⟨(ht (Sum.inr j)).1, (ht (Sum.inr j)).2.1⟩
  obtain ⟨t1, t2, tp, tm⟩ := ht (Sum.inl i)
  -- the re-hedges pin `r't_E`
  have hpur : PurchaseHedge D x r → r ⬝ᵥ (fun j => t (Sum.inr j)) = -hPlus D r := fun hp => by
    simp only [hPlus, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨p1, p2⟩ := hp j
    rcases lt_trichotomy (r j) 0 with h | h | h
    · rw [(ht (Sum.inr j)).2.2.1 (p2 h), max_eq_right h.le, max_eq_left (by linarith)]; ring
    · rw [h]; simp
    · rw [(ht (Sum.inr j)).2.2.2 (p1 h), max_eq_left h.le, max_eq_right (by linarith)]; ring
  have hsal : SaleHedge D x r → r ⬝ᵥ (fun j => t (Sum.inr j)) = hMinus D r := fun hp => by
    simp only [hMinus, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨p1, p2⟩ := hp j
    rcases lt_trichotomy (r j) 0 with h | h | h
    · rw [(ht (Sum.inr j)).2.2.2 (p2 h), max_eq_right h.le, max_eq_left (by linarith)]; ring
    · rw [h]; simp
    · rw [(ht (Sum.inr j)).2.2.1 (p1 h), max_eq_left h.le, max_eq_right (by linarith)]; ring
  refine ⟨fun hb => ?_, fun hs => ?_, fun he h0 h1 => ?_, fun hp hb => ⟨fun hc => ?_, fun hc => ?_⟩,
    fun hp hs => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · have := b2 (by linarith); rw [tp hb] at this
    nlinarith [mul_le_mul_of_nonneg_left hbnd.2 h1η]
  · have := b1 (by linarith); rw [tm hs] at this
    nlinarith [mul_le_mul_of_nonneg_left hbnd.1 h1η]
  · have e1 := b1 h1; have e2 := b2 h0
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hbnd.1 h1η, mul_le_mul_of_nonneg_left hbnd.2 h1η,
      mul_le_mul_of_nonneg_left t1 h1η, mul_le_mul_of_nonneg_left t2 h1η]
  · have e1 := b1 hc; have e2 := b2 (by linarith); rw [tp hb, hpur hp] at e1 e2; linarith
  · have e2 := b2 (by linarith); rw [tp hb, hpur hp] at e2; linarith
  · have e1 := b1 (by linarith); have e2 := b2 h0; rw [tm hs, hsal hp] at e1 e2; linarith
  · have e1 := b1 (by linarith); rw [tm hs, hsal hp] at e1; linarith

theorem sufficient : Sufficient := by
  intro hAX m K S _ D θ Sf v hI hR hBE hv hγ x hx hmax hk hE i
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  obtain ⟨η, t, hη, hηk, ht, hRb⟩ := core hAX θ hI hR hBE hx hmax hE
  have hη0 : η = 0 := by
    rcases mul_eq_zero.mp hηk with h | h
    · exact h
    · linarith
  subst hη0
  have hbnd := rt_bounds hr (rvec D i) (fun j => t (Sum.inr j))
    fun j => ⟨(ht (Sum.inr j)).1, (ht (Sum.inr j)).2.1⟩
  obtain ⟨b1, b2⟩ := hRb i
  obtain ⟨t1, t2, tp, tm⟩ := ht (Sum.inl i)
  have hA : ∀ y : Inst m K → ℝ, Ared D θ v 0 y i =
      θ.alpha i + rvec D i ⬝ᵥ D.cE - D.gamma * v i * y (Sum.inl i) := fun y => by
    simp [Ared]
  have hmono : x (Sum.inl i) ≤ w0 D (Sum.inl i) → Ared D θ v 0 (w0 D) i ≤ Ared D θ v 0 x i := fun h => by
    rw [hA, hA]; nlinarith [mul_nonneg hγ (hv i)]
  have hmono' : w0 D (Sum.inl i) ≤ x (Sum.inl i) → Ared D θ v 0 x i ≤ Ared D θ v 0 (w0 D) i := fun h => by
    rw [hA, hA]; nlinarith [mul_nonneg hγ (hv i)]
  have hwb : w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := hI.1.2.2.2 _
  have hk1 := (hr (Sum.inl i)).1
  have hk2 := (hr (Sum.inl i)).2
  simp only [zero_mul, sub_zero, add_zero, one_mul] at b1 b2
  constructor
  · intro hA0 hlt
    by_contra hno
    push Not at hno
    have hm := hmono hno
    rcases hno.lt_or_eq with h | h
    · have := b1 (by linarith); rw [tm h] at this; linarith [hbnd.1]
    · have := b1 (by rw [h]; exact hlt); linarith [hbnd.1]
  · intro hA0 hpos
    by_contra hno
    push Not at hno
    have hm := hmono' hno
    rcases hno.lt_or_eq with h | h
    · have := b2 (by linarith [w0_nonneg hI (Sum.inl i)]); rw [tp h] at this; linarith [hbnd.2]
    · have := b2 (by rw [← h]; exact hpos); linarith [hbnd.2]

/-! ### Part 6 -/

open Standalone.M6QuarterlyBandStaticCeiling in
theorem sureTrade : SureTrade := by
  intro Z Ω _ P hP hg t z ht
  obtain ⟨hband, -, hbr, -⟩ := Novel.M6QuarterlyBandStaticCeilingProof.proof
  obtain ⟨-, -, -, -, -, -, hlo0, hlohi, hhicap, -, hopt, -⟩ := hband Z Ω P hP t z ht
  obtain ⟨hb1, hb2⟩ := hbr Z Ω P hP t z ht
  have hgbar : gbar P t z = 1 := by
    simp only [gbar, hg, mul_one]; exact hP.2.2.2.2.2.2.2.2.2.1 t z
  have hc : 0 < curv P t z := by
    have := hP.2.2.1 t z (fun _ => 1) (fun h => by simpa using congrFun h 0)
    simp [mulVec, dotProduct] at this
    exact mul_pos hP.2.2.2.1 this
  have hcap := hP.2.2.2.2.2.2.2.1 0
  rw [hgbar, mul_one] at hb1 hb2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hpos : 0 < xs P t z - (P.kp 0 + P.beta * P.km 0) / curv P t z := by
      rw [sub_pos, div_lt_iff₀ hc]; linarith
    have hlo : 0 < lo P t z := lt_of_lt_of_le (lt_min hcap hpos) hb1
    refine ⟨hlo, ?_⟩
    have := hopt 0 le_rfl
    rwa [max_eq_right hlo0, min_eq_left hlohi] at this
  · have hneg : xs P t z + (P.km 0 + P.beta * P.kp 0) / curv P t z < 0 := by
      have : (P.km 0 + P.beta * P.kp 0) / curv P t z < -xs P t z := by
        rw [div_lt_iff₀ hc]; linarith
      linarith
    have hhi : hi P t z = 0 := le_antisymm (hb2.trans (max_eq_left hneg.le).le) (hlo0.trans hlohi)
    have := hopt (P.cap 0) hcap.le
    rwa [max_eq_left (hlohi.trans hhicap), hhi, min_eq_right hcap.le] at this

section OnlyIfSec

open Standalone.M6QuarterlyBandStaticCeiling

variable {Z Ω : Type} [Fintype Ω] {P : M6 1 Z Ω}

lemma fun_one (y : Fin 1 → ℝ) : y = fun _ => y 0 := funext fun i => by rw [Subsingleton.elim i 0]

/-- `G_t` on one instrument with pure-learning marking. -/
lemma G_one (hg : ∀ ω, P.gross ω 0 = 1) (t : ℕ) (z : Z) (y0 : ℝ) :
    G P t z (fun _ => y0) = curv P t z / 2 * (y0 - Standalone.M6QuarterlyBandStaticCeiling.xs P t z) ^ 2 +
      P.beta * ∑ ω, P.prob t z ω * V1 P (t + 1) (P.next ω) y0 := by
  have hm : ∀ ω, mark (fun _ : Fin 1 => y0) (P.gross ω) = fun _ => y0 := fun ω => by
    funext i; rw [Subsingleton.elim i 0]; simp [mark, hg ω]
  simp only [G, track, hm, V1, curv, Standalone.M6QuarterlyBandStaticCeiling.xs, dotProduct, mulVec,
    Fin.sum_univ_one, Pi.sub_apply]
  ring

omit [Fintype Ω] in
lemma cost_one (a b : ℝ) : Standalone.M6QuarterlyBandStaticCeiling.cost P ((fun _ => a) - fun _ => b) =
    P.kp 0 * max (a - b) 0 + P.km 0 * max (-(a - b)) 0 := by
  simp [Standalone.M6QuarterlyBandStaticCeiling.cost]

/-- The next review's value rises by at least `-κ⁺ y` from `0` and by at least `-κ⁻` per unit below the
cap. -/
lemma V_next (hP : Setting P) {t : ℕ} (z' : Z) (ht : t < P.T) :
    (∀ y, 0 ≤ y → -P.kp 0 * y ≤ V1 P (t + 1) z' y - V1 P (t + 1) z' 0) ∧
    (∀ y, y ≤ P.cap 0 → -P.km 0 * (P.cap 0 - y) ≤ V1 P (t + 1) z' y - V1 P (t + 1) z' (P.cap 0)) ∧
    (∀ y, 0 ≤ y → V1 P (t + 1) z' y - V1 P (t + 1) z' 0 ≤ P.km 0 * y) := by
  rcases Nat.lt_or_ge (t + 1) P.T with h | h
  · obtain ⟨hband, -⟩ := Novel.M6QuarterlyBandStaticCeilingProof.proof
    obtain ⟨-, -, hcv, -, hrd, hld, -⟩ := hband Z Ω P hP (t + 1) z' h
    have hcap := hP.2.2.2.2.2.2.2.1 0
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rcases hy.lt_or_eq with hy | hy
      · have hs := hcv.rightDeriv_le_slope_of_mem_interior (by simp) (Set.mem_univ y) hy
        have hr := (hrd 0 le_rfl).1
        rw [slope_def_field, sub_zero] at hs
        have := (le_div_iff₀ hy).mp (hr.trans hs)
        unfold rd at hr; linarith
      · rw [← hy]; simp
    · rcases hy.lt_or_eq with hy | hy
      · have hs := hcv.slope_le_leftDeriv_of_mem_interior (Set.mem_univ y) (by simp) hy
        have hl := (hld (P.cap 0) hcap).2
        have hr := (hrd (P.cap 0) hcap.le).2
        rw [slope_def_field] at hs
        have hsub : 0 < P.cap 0 - y := by linarith
        have := (div_le_iff₀ hsub).mp (hs.trans (hl.trans hr))
        unfold ld rd at *; linarith
      · rw [hy]; simp
    · rcases hy.lt_or_eq with hy | hy
      · have hs := hcv.slope_le_leftDeriv_of_mem_interior (Set.mem_univ 0) (by simp) hy
        have hl := (hld y hy).2
        have hr := (hrd y hy.le).2
        rw [slope_def_field, sub_zero] at hs
        have := (div_le_iff₀ hy).mp (hs.trans (hl.trans hr))
        unfold ld rd at *; linarith
      · rw [← hy]; simp
  · have hT : t + 1 = P.T := by omega
    have hV : ∀ x, V1 P (t + 1) z' x = 0 := fun x => by simp [V1, V, hT, Vk]
    have hk := hP.2.2.2.2.2.2.1 0
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩ <;> rw [hV, hV, sub_zero]
    · nlinarith [hk.1]
    · nlinarith [hk.2.2.1]
    · nlinarith [hk.2.2.1]

theorem onlyIf : OnlyIf := by
  intro Z Ω _ P hP hg t z ht
  obtain ⟨hband, -⟩ := Novel.M6QuarterlyBandStaticCeilingProof.proof
  obtain ⟨-, -, -, -, -, -, hlo0, hlohi, hhicap, huniq, hopt, -⟩ := hband Z Ω P hP t z ht
  have hc : 0 < curv P t z := by
    have := hP.2.2.1 t z (fun _ => 1) (fun h => by simpa using congrFun h 0)
    simp [mulVec, dotProduct] at this
    exact mul_pos hP.2.2.2.1 this
  have hβ0 := hP.2.2.2.2.1.le
  have hq0 := hP.2.2.2.2.2.2.2.2.1 t z
  have hq1 := hP.2.2.2.2.2.2.2.2.2.1 t z
  have hcap := hP.2.2.2.2.2.2.2.1 0
  have hk := hP.2.2.2.2.2.2.1 0
  have hsum : ∀ (f : Ω → ℝ) (L : ℝ), (∀ ω, L ≤ f ω) → L ≤ ∑ ω, P.prob t z ω * f ω := fun f L h => by
    calc L = ∑ ω, P.prob t z ω * L := by rw [← Finset.sum_mul, hq1, one_mul]
      _ ≤ ∑ ω, P.prob t z ω * f ω := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hq0 ω)
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · -- stay at zero
    have hopt0 : IsOpt P t z (fun _ => 0) (fun _ => 0) := by
      refine ⟨fun i => by rw [Subsingleton.elim i 0]; exact ⟨le_rfl, hcap.le⟩, fun y hy => ?_⟩
      have hy0 := (hy 0).1
      rw [fun_one y, cost_one, cost_one, G_one hg, G_one hg]
      simp only [sub_zero, sub_self, neg_zero, max_self, mul_zero, add_zero, zero_add]
      have hV := hsum (fun ω => V1 P (t + 1) (P.next ω) (y 0) - V1 P (t + 1) (P.next ω) 0)
        (-P.kp 0 * y 0) fun ω => (V_next hP (P.next ω) ht).1 (y 0) hy0
      simp only [mul_sub, Finset.sum_sub_distrib] at hV
      rw [max_eq_left hy0, max_eq_right (by linarith : -y 0 ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_left hV hβ0, mul_nonneg hc.le (sq_nonneg (y 0)),
        mul_le_mul_of_nonneg_left h hy0, mul_nonneg hy0 hk.1]
    refine ⟨hopt0, ?_⟩
    have h1 := hopt 0 le_rfl
    rw [max_eq_right hlo0, min_eq_left hlohi] at h1
    have := (huniq 0 le_rfl).unique hopt0 h1
    exact (congrFun this 0).symm
  · -- stay at the cap
    have hoptc : IsOpt P t z (fun _ => P.cap 0) (fun _ => P.cap 0) := by
      refine ⟨fun i => by rw [Subsingleton.elim i 0]; exact ⟨hcap.le, le_rfl⟩, fun y hy => ?_⟩
      have hy1 := (hy 0).2
      rw [fun_one y, cost_one, cost_one, G_one hg, G_one hg]
      simp only [sub_self, neg_zero, max_self, mul_zero, add_zero, zero_add]
      have hV := hsum (fun ω => V1 P (t + 1) (P.next ω) (y 0) - V1 P (t + 1) (P.next ω) (P.cap 0))
        (-P.km 0 * (P.cap 0 - y 0)) fun ω => (V_next hP (P.next ω) ht).2.1 (y 0) hy1
      simp only [mul_sub, Finset.sum_sub_distrib] at hV
      rw [max_eq_right (by linarith : y 0 - P.cap 0 ≤ 0), max_eq_left (by linarith : 0 ≤ -(y 0 - P.cap 0))]
      have hδ : 0 ≤ P.cap 0 - y 0 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hV hβ0, mul_nonneg hc.le (sq_nonneg (P.cap 0 - y 0)),
        mul_le_mul_of_nonneg_left h hδ, mul_nonneg hδ hk.2.2.1]
    refine ⟨hoptc, ?_⟩
    have h1 := hopt (P.cap 0) hcap.le
    rw [max_eq_left (hlohi.trans hhicap), min_eq_right hhicap] at h1
    have := (huniq (P.cap 0) hcap.le).unique hoptc h1
    exact (congrFun this 0).symm
  · -- sold out only if
    intro hhi
    have h1 := hopt (P.cap 0) hcap.le
    rw [max_eq_left (hlohi.trans hhicap), hhi, min_eq_right hcap.le] at h1
    have hkm := hk.2.2.1
    set a := curv P t z * Standalone.M6QuarterlyBandStaticCeiling.xs P t z + (1 - P.beta) * P.km 0
    have key : ∀ y, 0 < y → y ≤ P.cap 0 → a ≤ curv P t z / 2 * y := fun y hy0 hy1 => by
      have := h1.2 (fun _ => y) fun i => by rw [Subsingleton.elim i 0]; exact ⟨hy0.le, hy1⟩
      rw [cost_one, cost_one, G_one hg, G_one hg] at this
      have hV : ∑ ω, P.prob t z ω * (V1 P (t + 1) (P.next ω) y - V1 P (t + 1) (P.next ω) 0) ≤
          ∑ ω, P.prob t z ω * (P.km 0 * y) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          ((V_next hP (P.next ω) ht).2.2 y hy0.le) (hq0 ω)
      rw [← Finset.sum_mul, hq1, one_mul] at hV
      simp only [mul_sub, Finset.sum_sub_distrib] at hV
      rw [max_eq_right (by linarith : 0 - P.cap 0 ≤ 0), max_eq_left (by linarith : 0 ≤ -(0 - P.cap 0)),
        max_eq_right (by linarith : y - P.cap 0 ≤ 0), max_eq_left (by linarith : 0 ≤ -(y - P.cap 0))] at this
      have hb := mul_le_mul_of_nonneg_left hV hβ0
      simp only [a]
      have : y * (curv P t z * Standalone.M6QuarterlyBandStaticCeiling.xs P t z + (1 - P.beta) * P.km 0) ≤
          y * (curv P t z / 2 * y) := by nlinarith
      exact le_of_mul_le_mul_left this hy0
    by_contra hcon
    push Not at hcon
    have ha : 0 < a := by simp only [a]; linarith
    set y := min (P.cap 0) (a / curv P t z)
    have hy0 : 0 < y := lt_min hcap (div_pos ha hc)
    have hk2 := key y hy0 (min_le_left _ _)
    have : curv P t z / 2 * y ≤ a / 2 := by
      have := mul_le_mul_of_nonneg_left (min_le_right (P.cap 0) (a / curv P t z)) (by positivity : 0 ≤ curv P t z / 2)
      calc curv P t z / 2 * y ≤ curv P t z / 2 * (a / curv P t z) := this
        _ = a / 2 := by field_simp
    linarith

end OnlyIfSec

theorem proof : Standalone.M7FundHoldBuySellCriterion.statement :=
  ⟨criterion, etfTest, spanningRule, reHedge, pinned, sufficient, budgetStrip, sureTrade, onlyIf⟩

end

end Novel.M7FundHoldBuySellCriterionProof

import Novel.M7TwoStageExactnessLossProof
import Novel.M7PremiumErrorInFundChoiceProof
import Standalone.M7EtfOnlyRestrictionCost

/-!
# Claim 106: proof

- Part 1 compares the three nested classes' maximizers. The score is strictly concave when `Σ` is
  positive definite, so each class's maximizer is unique.
- Parts 2 and 3: at a class optimum with a slack budget and interior ETFs, claim 104's
  slack-dropping lemma frees the ETFs. The exposure part is then a constant under spanning, and
  claim 104's hedge value in 2c. The rest splits into one-variable fund objectives maximized over
  the class's range, `[0, x̄]`, `[0, x⁻]` or `{x⁻}`. Those maxima are band holdings, and their
  differences are the closed forms.
- Part 4 compares the optima with netted holdings. The exposure is unchanged, the fund parts
  change by the one-variable quadratics, and the ETF costs change by at most the re-hedge costs
  (subadditivity).
-/

namespace Novel.M7EtfOnlyRestrictionCostProof

open Filter Topology Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss
open Standalone.M7EtfOnlyRestrictionCost Novel.M7TwoStageExactnessLossProof
open Standalone.M2TwoStageSeparation (Inputs Gf Hr sigF sqN)
open Standalone.M5MissingDirectionLeak (Jmap Schur)

noncomputable section

variable {S : Type} [Fintype S]

/-! ### Uniqueness -/

omit [Fintype S] in
lemma w0_nonneg {m n K : ℕ} {D : Data m n K S} (hI : Inputs D) (l : Inst m n) : 0 ≤ w0 D l :=
  div_nonneg (hI.1.2.1 l) hI.1.1.le

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

/-- On a convex subset of `F`, the score has at most one maximizer. -/
lemma unique_on {m n K : ℕ} {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
    (hSig : (covariance D).PosDef) (hγ : 0 < D.gamma) {A : Set (Inst m n → ℝ)} (hA : Convex ℝ A)
    {w₁ w₂ : Inst m n → ℝ} (h₁ : w₁ ∈ A) (h₂ : w₂ ∈ A)
    (hm₁ : IsMaxOn (fun w => score D w θ) A w₁) (hm₂ : IsMaxOn (fun w => score D w θ) A w₂) :
    w₁ = w₂ := by
  have hmid : (1 / 2 : ℝ) • w₁ + (1 / 2 : ℝ) • w₂ ∈ A := hA h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
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

omit [Fintype S] in
lemma F_convex' {m n K : ℕ} {D : Data m n K S} (hI : Inputs D) : Convex ℝ (F D) :=
  (Novel.M2ActionClassesProof.classesConvex D hI.2.1).1

omit [Fintype S] in
lemma Em_convex {m n K : ℕ} {D : Data m n K S} (hI : Inputs D) : Convex ℝ (Em D) := by
  intro x hx y hy a b ha hb hab
  refine ⟨F_convex' hI hx.1 hy.1 ha hb hab, fun i => ?_⟩
  have h1 := hx.2 i; have h2 := hy.2 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : a * w0 D (Sum.inl i) + b * w0 D (Sum.inl i) = w0 D (Sum.inl i) := by
    rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

omit [Fintype S] in
lemma E0_convex {m n K : ℕ} {D : Data m n K S} (hI : Inputs D) : Convex ℝ (E0 D) := by
  intro x hx y hy a b ha hb hab
  refine ⟨F_convex' hI hx.1 hy.1 ha hb hab, ?_⟩
  have e : active (a • x + b • y) = a • active x + b • active y := rfl
  rw [e, hx.2, hy.2, ← add_smul, hab, one_smul]

/-! ### Part 1 -/

theorem structure' : Structure := by
  intro m n K S _ D θ hI hSig hγ wJ hwJ hmJ wm hwm hmm wf hwf hmf
  have hfm : wf ∈ Em D := ⟨hwf.1, fun i => le_of_eq (congrFun hwf.2 i)⟩
  have h1 : score D wf θ ≤ score D wm θ := hmm hfm
  have h2 : score D wm θ ≤ score D wJ θ := hmJ hwm.1
  have hfJ : score D wf θ ≤ score D wJ θ := hmJ hwf.1
  refine ⟨h1, h2, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ?_, ⟨fun h => ?_, fun h => ?_⟩,
    by ring⟩
  · have hmF : IsMaxOn (fun w => score D w θ) (F D) wm := fun y hy => by
      have : score D y θ ≤ score D wJ θ := hmJ hy
      show score D y θ ≤ score D wm θ; rw [← h]; exact this
    rw [unique_on θ hI hSig hγ (F_convex' hI) hwJ hwm.1 hmJ hmF]; exact hwm.2
  · have : score D wJ θ ≤ score D wm θ := hmm ⟨hwJ, h⟩
    exact le_antisymm this h2
  · have hfF : IsMaxOn (fun w => score D w θ) (F D) wf := fun y hy => by
      have : score D y θ ≤ score D wJ θ := hmJ hy
      show score D y θ ≤ score D wf θ; rw [← h]; exact this
    rw [unique_on θ hI hSig hγ (F_convex' hI) hwJ hwf.1 hmJ hfF]; exact hwf.2
  · have : score D wJ θ ≤ score D wf θ := hmf ⟨hwJ, h⟩
    exact le_antisymm this hfJ
  · intro hAX
    rw [← jointOptimality hAX m n K S D θ hI wf hwf.1]
    constructor
    · intro h y hy
      have : score D y θ ≤ score D wJ θ := hmJ hy
      show score D y θ ≤ score D wf θ; rw [← h]; exact this
    · intro h
      have : score D wJ θ ≤ score D wf θ := h hwJ
      exact le_antisymm this hfJ
  · have hfE : IsMaxOn (fun w => score D w θ) (Em D) wf := fun y hy => by
      have : score D y θ ≤ score D wm θ := hmm hy
      show score D y θ ≤ score D wf θ; rw [← h]; exact this
    rw [unique_on θ hI hSig hγ (Em_convex hI) hwm hfm hmm hfE]; exact hwf.2
  · have : score D wm θ ≤ score D wf θ := hmf ⟨hwm.1, h⟩
    exact le_antisymm this h1

/-! ### The one-fund forms -/

theorem oneFund : OneFund := by
  intro alpha c kp km xm xbar hc hkp hkm h0 h1
  have hlh : (alpha - kp) / c ≤ (alpha + km) / c := div_le_div_of_nonneg_right (by linarith) hc.le
  have clo : c * ((alpha - kp) / c) = alpha - kp := by field_simp
  have chi : c * ((alpha + km) / c) = alpha + km := by field_simp
  have ep : 0 < alpha - kp - c * xm ↔ xm < (alpha - kp) / c := by
    rw [lt_div_iff₀ hc]; constructor <;> intro h <;> linarith
  have es : 0 < c * xm - alpha - km ↔ (alpha + km) / c < xm := by
    rw [div_lt_iff₀ hc]; constructor <;> intro h <;> linarith
  unfold bandHold buyCost sellCost
  generalize (alpha - kp) / c = lo at clo hlh ep ⊢
  generalize (alpha + km) / c = hi at chi hlh es ⊢
  -- the incumbent against the band
  rcases lt_or_ge xm lo with hl | hl
  · -- purchase region: `u = lo > x⁻`
    have hu : max lo (min hi xm) = lo := max_eq_left ((min_le_right _ _).trans hl.le)
    have hlo0 : 0 < lo := lt_of_le_of_lt h0 hl
    have hs : ¬ (0 < c * xm - alpha - km) := by rw [es]; linarith
    have hp' := ep.mpr hl
    rw [hu, min_eq_left hl.le, max_eq_right h0]
    simp only [hp', hs, ↓reduceIte]
    refine ⟨?_, by simp [psi], ?_⟩
    · rcases le_or_gt lo xbar with hx | hx
      · rw [min_eq_right hx, max_eq_right hlo0.le]; simp only [hx, ↓reduceIte]
        simp only [psi]
        rw [max_eq_left (by linarith : 0 ≤ lo - xm), max_eq_right (by linarith : xm - lo ≤ 0), sub_self,
          max_self]
        have e : alpha - kp - c * xm = c * (lo - xm) := by linarith
        rw [e]; field_simp; nlinarith [clo]
      · rw [min_eq_left hx.le, max_eq_right (h0.trans h1)]; simp only [not_le.mpr hx, ↓reduceIte]
    · rw [min_eq_left (le_max_of_le_right (le_min h1 (hl.le.trans hlh)))]
  · rcases lt_or_ge hi xm with hh | hh
    · -- sale region: `u = hi < x⁻`
      have hu : max lo (min hi xm) = hi := by rw [min_eq_left hh.le, max_eq_right hlh]
      have hp : ¬ (0 < alpha - kp - c * xm) := by rw [ep]; linarith
      have hs' := es.mpr hh
      rw [hu, min_eq_right (hh.le.trans h1), min_eq_right hh.le, min_eq_right (max_le h0 hh.le)]
      simp only [hp, hs', ↓reduceIte]
      refine ⟨by simp, ?_, trivial⟩
      rcases le_or_gt 0 hi with hz | hz
      · rw [max_eq_right hz]; simp only [hz, ↓reduceIte]
        simp only [psi]
        rw [max_eq_right (by linarith : hi - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - hi), sub_self,
          max_self]
        have e : c * xm - alpha - km = c * (xm - hi) := by linarith
        rw [e]; field_simp; nlinarith [chi]
      · rw [max_eq_left hz.le]; simp only [not_le.mpr hz, ↓reduceIte]
    · -- hold region: `u = x⁻`
      have hu : max lo (min hi xm) = xm := by rw [min_eq_right hh, max_eq_right hl]
      have hp : ¬ (0 < alpha - kp - c * xm) := by rw [ep]; linarith
      have hs : ¬ (0 < c * xm - alpha - km) := by rw [es]; linarith
      rw [hu, min_eq_right h1, min_self, max_eq_right h0]
      simp only [hp, hs, ↓reduceIte]
      refine ⟨by simp, by simp, ?_⟩
      rw [min_eq_left (le_max_of_le_right (le_min h1 hh))]

/-! ### Parts 2-3: the class values -/

section Classes

variable {m n K : ℕ} {D : Data m n K S} (θ : Params m K)

/-- A class capping fund `k` at `U_k ≤ x̄_k`: at its optimum with a slack budget and interior ETFs, the
value is `C₀ + Σ_k (φ_k + ψ_k)(x_k)`, and each fund maximizes `φ_k + ψ_k` on `[0, U_k]`. -/
lemma class_upper (hI : Inputs D) (ψ : Fin m → ℝ → ℝ)
    (hdec : ∀ w, score D w θ = Gf D θ (exposure D w) + ∑ k, ψ k (w (Sum.inl k)))
    (Φ : (Fin m → ℝ) → ℝ) (C0 : ℝ) (φ : Fin m → ℝ → ℝ)
    (hle : ∀ w, Gf D θ (exposure D w) ≤ Φ (active w))
    (heq : ∀ a, ∃ z, Gf D θ (exposure D (Sum.elim a z)) = Φ a)
    (hsep : ∀ a, Φ a = C0 + ∑ k, φ k (a k))
    (U : Fin m → ℝ) (hUx : ∀ k, U k ≤ D.wbar (Sum.inl k))
    {wc : Inst m n → ℝ} (hwc : wc ∈ F D) (hwcU : ∀ k, wc (Sum.inl k) ≤ U k)
    (hmax : ∀ w ∈ F D, (∀ k, w (Sum.inl k) ≤ U k) → score D w θ ≤ score D wc θ)
    (hk : 0 < cash D wc) (hE : ∀ j, 0 < wc (Sum.inr j) ∧ wc (Sum.inr j) < D.wbar (Sum.inr j)) :
    score D wc θ = C0 + ∑ k, (φ k (wc (Sum.inl k)) + ψ k (wc (Sum.inl k))) ∧
    ∀ k, IsMaxOn (fun y => φ k y + ψ k y) (Set.Icc 0 (U k)) (wc (Sum.inl k)) := by
  have hA : Convex ℝ {w : Inst m n → ℝ | ∀ k, w (Sum.inl k) ≤ U k} := by
    intro x hx y hy a b ha hb hab k
    have h1 := hx k; have h2 := hy k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : a * U k + b * U k = U k := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hP : ∀ l : Inst m n, l.isRight = true → 0 < wc l ∧ wc l < D.wbar l := by
    rintro (l | l) hl
    · simp at hl
    · exact hE l
  have key : ∀ a : Fin m → ℝ, (∀ k, 0 ≤ a k ∧ a k ≤ U k) →
      C0 + ∑ k, (φ k (a k) + ψ k (a k)) ≤ score D wc θ := by
    intro a ha
    obtain ⟨z, hz⟩ := heq a
    have h := drop_slack_gen (fun l => l.isRight = true) (fun w => score D w θ) (score_ineq θ hI) hA hwc
      hwcU (fun w hw hA' => hmax w hw hA') hk hP (z := Sum.elim a z) (fun k => (ha k).2) (by
        rintro (l | l) hl
        · exact ⟨(ha l).1, (ha l).2.trans (hUx l)⟩
        · simp at hl)
    rw [hdec, hz, hsep] at h
    simp only [Sum.elim_inl] at h
    rw [Finset.sum_add_distrib]; linarith
  have hval : score D wc θ = C0 + ∑ k, (φ k (wc (Sum.inl k)) + ψ k (wc (Sum.inl k))) := by
    apply le_antisymm
    · rw [hdec, Finset.sum_add_distrib]
      have := hle wc; rw [hsep] at this; simp only [active] at this; linarith
    · exact key (active wc) fun k => ⟨(hwc.1 (Sum.inl k)).1, hwcU k⟩
  refine ⟨hval, fun k y hy => ?_⟩
  have h := key (Function.update (active wc) k y) fun j => by
    by_cases hj : j = k
    · subst hj; simpa using hy
    · simp only [Function.update_of_ne hj]; exact ⟨(hwc.1 (Sum.inl j)).1, hwcU j⟩
  rw [hval] at h
  have h' : ∑ j, (φ j (Function.update (active wc) k y j) + ψ j (Function.update (active wc) k y j)) ≤
      ∑ j, (φ j (active wc j) + ψ j (active wc j)) := by
    simp only [active] at h ⊢; linarith
  exact sum_update_le (fun j x => φ j x + ψ j x) (active wc) k y h'

/-- The frozen class: at its optimum with a slack budget and interior ETFs, the value is
`C₀ + Σ_k (φ_k + ψ_k)(x⁻_k)`. -/
lemma class_frozen (hI : Inputs D) (ψ : Fin m → ℝ → ℝ)
    (hdec : ∀ w, score D w θ = Gf D θ (exposure D w) + ∑ k, ψ k (w (Sum.inl k)))
    (Φ : (Fin m → ℝ) → ℝ) (C0 : ℝ) (φ : Fin m → ℝ → ℝ)
    (hle : ∀ w, Gf D θ (exposure D w) ≤ Φ (active w))
    (heq : ∀ a, ∃ z, Gf D θ (exposure D (Sum.elim a z)) = Φ a)
    (hsep : ∀ a, Φ a = C0 + ∑ k, φ k (a k))
    {wf : Inst m n → ℝ} (hwf : wf ∈ E0 D) (hmax : IsMaxOn (fun w => score D w θ) (E0 D) wf)
    (hk : 0 < cash D wf) (hE : ∀ j, 0 < wf (Sum.inr j) ∧ wf (Sum.inr j) < D.wbar (Sum.inr j)) :
    score D wf θ = C0 + ∑ k, (φ k (w0 D (Sum.inl k)) + ψ k (w0 D (Sum.inl k))) := by
  have hA : Convex ℝ {w : Inst m n → ℝ | active w = active (w0 D)} := by
    intro x hx y hy a b _ _ hab
    show active (a • x + b • y) = active (w0 D)
    have e : active (a • x + b • y) = a • active x + b • active y := rfl
    rw [e, show active x = active (w0 D) from hx, show active y = active (w0 D) from hy, ← add_smul, hab,
      one_smul]
  have hP : ∀ l : Inst m n, l.isRight = true → 0 < wf l ∧ wf l < D.wbar l := by
    rintro (l | l) hl
    · simp at hl
    · exact hE l
  have hfa : ∀ k, wf (Sum.inl k) = w0 D (Sum.inl k) := fun k => congrFun hwf.2 k
  apply le_antisymm
  · rw [hdec, Finset.sum_add_distrib]
    have := hle wf; rw [hsep] at this
    simp only [active, hfa] at this ⊢
    linarith
  · obtain ⟨z, hz⟩ := heq (active (w0 D))
    have h := drop_slack_gen (fun l => l.isRight = true) (fun w => score D w θ) (score_ineq θ hI) hA hwf.1
      hwf.2 (fun w hw hA' => hmax ⟨hw, hA'⟩) hk hP (z := Sum.elim (active (w0 D)) z) rfl (by
        rintro (l | l) hl
        · exact ⟨w0_nonneg hI _, hI.1.2.2.2 _⟩
        · simp at hl)
    rw [hdec, hz, hsep] at h
    simp only [Sum.elim_inl, active] at h
    rw [Finset.sum_add_distrib]; linarith

end Classes

/-- From the class values to the closed forms. -/
lemma finish {m : ℕ} (C0 : ℝ) (al c kp km xm xbar : Fin m → ℝ) (hc : ∀ k, 0 < c k)
    (hkp : ∀ k, 0 ≤ kp k) (hkm : ∀ k, 0 ≤ km k) (h0 : ∀ k, 0 ≤ xm k) (h1 : ∀ k, xm k ≤ xbar k)
    (aJ am : Fin m → ℝ) (sJ sm sf : ℝ)
    (hJ : sJ = C0 + ∑ k, psi (al k) (c k) (kp k) (km k) (xm k) (aJ k))
    (hm : sm = C0 + ∑ k, psi (al k) (c k) (kp k) (km k) (xm k) (am k))
    (hf : sf = C0 + ∑ k, psi (al k) (c k) (kp k) (km k) (xm k) (xm k))
    (hmaxJ : ∀ k, IsMaxOn (psi (al k) (c k) (kp k) (km k) (xm k)) (Set.Icc 0 (xbar k)) (aJ k))
    (hmaxm : ∀ k, IsMaxOn (psi (al k) (c k) (kp k) (km k) (xm k)) (Set.Icc 0 (xm k)) (am k))
    (hbJ : ∀ k, aJ k ∈ Set.Icc 0 (xbar k)) (hbm : ∀ k, am k ∈ Set.Icc 0 (xm k)) :
    sJ - sm = ∑ k, (psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xbar k)) -
      psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xm k))) ∧
    sJ - sm = ∑ k, buyCost (al k) (c k) (kp k) (km k) (xm k) (xbar k) ∧
    sm - sf = ∑ k, (psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xm k)) -
      psi (al k) (c k) (kp k) (km k) (xm k) (xm k)) ∧
    sm - sf = ∑ k, sellCost (al k) (c k) (kp k) (km k) (xm k) := by
  have eJ : ∀ k, aJ k = bandHold (al k) (c k) (kp k) (km k) (xm k) (xbar k) := fun k =>
    eq_bandHold (hc k) (hkp k) (hkm k) (hbJ k) (hmaxJ k)
  have em : ∀ k, am k = bandHold (al k) (c k) (kp k) (km k) (xm k) (xm k) := fun k =>
    eq_bandHold (hc k) (hkp k) (hkm k) (hbm k) (hmaxm k)
  have d1 : sJ - sm = ∑ k, (psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xbar k)) -
      psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xm k))) := by
    rw [hJ, hm, Finset.sum_sub_distrib]; simp only [eJ, em]; ring
  have d2 : sm - sf = ∑ k, (psi (al k) (c k) (kp k) (km k) (xm k) (bandHold (al k) (c k) (kp k) (km k) (xm k) (xm k)) -
      psi (al k) (c k) (kp k) (km k) (xm k) (xm k)) := by
    rw [hm, hf, Finset.sum_sub_distrib]; simp only [em]; ring
  refine ⟨d1, ?_, d2, ?_⟩
  · rw [d1]; exact Finset.sum_congr rfl fun k _ =>
      (oneFund (al k) (c k) (kp k) (km k) (xm k) (xbar k) (hc k) (hkp k) (hkm k) (h0 k) (h1 k)).1
  · rw [d2]; exact Finset.sum_congr rfl fun k _ =>
      (oneFund (al k) (c k) (kp k) (km k) (xm k) (xbar k) (hc k) (hkp k) (hkm k) (h0 k) (h1 k)).2.1

theorem spanning2 : Spanning2 := by
  intro m K S _ D θ Sf v hI hFS wJ hwJ hmJ wm hwm hmm wf hwf hmf hsl ψ a am
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ⟩ := hFS
  have hsig : sigF D = Sf := hR.1
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  set bTB := (D.gamma • Sf)⁻¹ *ᵥ θ.lam
  have hTB : D.gamma • (sigF D *ᵥ bTB) = θ.lam := by
    rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hle : ∀ w, Gf D θ (exposure D w) ≤ (fun _ : Fin m → ℝ => Gf D θ bTB) (active w) := fun w => by
    show Gf D θ (exposure D w) ≤ Gf D θ bTB
    rw [G_TB θ hTB]
    nlinarith [Novel.M2TwoStageSeparationProof.sqN_nonneg D hI.2.2.1 (exposure D w - bTB)]
  have heq : ∀ a' : Fin m → ℝ, ∃ z, Gf D θ (exposure D (Sum.elim a' z)) =
      (fun _ : Fin m → ℝ => Gf D θ bTB) a' := fun a' =>
    ⟨(D.BEᵀ)⁻¹ *ᵥ (bTB - D.BAᵀ *ᵥ a'), by show _ = _; rw [realize D hBE]⟩
  have hsep : ∀ a' : Fin m → ℝ, (fun _ : Fin m → ℝ => Gf D θ bTB) a' =
      Gf D θ bTB + ∑ k, (fun (_ : Fin m) (_ : ℝ) => (0 : ℝ)) k (a' k) := fun a' => by simp
  have hdec := score_span θ hR hcE hkE
  have sJ := hsl wJ (by simp)
  have sm := hsl wm (by simp)
  have sf := hsl wf (by simp)
  have cJ := class_upper θ hI _ hdec (fun _ => Gf D θ bTB) (Gf D θ bTB) (fun _ _ => 0) hle heq hsep
    (fun k => D.wbar (Sum.inl k)) (fun k => le_rfl)
    hwJ (fun k => (hwJ.1 (Sum.inl k)).2) (fun w hw _ => hmJ hw) sJ.1 sJ.2
  have cm := class_upper θ hI _ hdec (fun _ => Gf D θ bTB) (Gf D θ bTB) (fun _ _ => 0) hle heq hsep
    (fun k => w0 D (Sum.inl k))
    (fun k => hI.1.2.2.2 _) hwm.1 hwm.2 (fun w hw hA => hmm ⟨hw, hA⟩) sm.1 sm.2
  have cf := class_frozen θ hI _ hdec (fun _ => Gf D θ bTB) (Gf D θ bTB) (fun _ _ => 0) hle heq hsep hwf
    hmf sf.1 sf.2
  simp only [zero_add] at cJ cm cf
  have hc : ∀ k, 0 < D.gamma * v k := fun k => mul_pos hγ (hv k)
  have fin := finish (Gf D θ bTB) (fun k => θ.alpha k) (fun k => D.gamma * v k) (fun k => D.kplus (Sum.inl k))
    (fun k => D.kminus (Sum.inl k)) (fun k => w0 D (Sum.inl k)) (fun k => D.wbar (Sum.inl k)) hc
    (fun k => (hI.2.1 _).1) (fun k => (hI.2.1 _).2) (fun k => w0_nonneg hI _) (fun k => hI.1.2.2.2 _)
    (fun k => wJ (Sum.inl k)) (fun k => wm (Sum.inl k)) _ _ _ cJ.1 cm.1 cf cJ.2 cm.2
    (fun k => hwJ.1 (Sum.inl k)) (fun k => ⟨(hwm.1.1 (Sum.inl k)).1, hwm.2 k⟩)
  obtain ⟨f1, f2, f3, f4⟩ := fin
  refine ⟨f1, f2, f3, f4, fun hz => ⟨?_, ?_⟩⟩
  · rw [f2]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨hz0, hlo⟩ := hz k
    simp only [buyCost, hz0, mul_zero, sub_zero]
    by_cases hp : 0 < θ.alpha k - D.kplus (Sum.inl k)
    · simp only [hp, hlo, ↓reduceIte, max_eq_left hp.le]
    · simp only [hp, ↓reduceIte, max_eq_right (not_lt.mp hp)]; ring
  · rw [f4]
    refine Finset.sum_eq_zero fun k _ => ?_
    obtain ⟨hz0, -⟩ := hz k
    simp only [sellCost, hz0, mul_zero, zero_sub]
    split_ifs with h1 h2
    · exfalso
      have : 0 ≤ θ.alpha k + D.kminus (Sum.inl k) := by
        have := (div_nonneg_iff.mp h2)
        rcases this with ⟨ha, _⟩ | ⟨ha, hb⟩
        · exact ha
        · linarith [hc k]
      linarith
    · ring
    · rfl

theorem unreach3 : Unreach3 := by
  intro m n K S _ D θ Sf v i hI hOU wJ hwJ hmJ wm hwm hmm wf hwf hmf hsl al vv
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ := hOU
  have hsig : sigF D = Sf := hR.1
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  obtain ⟨b0, hb0⟩ : ∃ b0, D.gamma • (sigF D *ᵥ b0) = θ.lam :=
    ⟨(D.gamma • Sf)⁻¹ *ᵥ θ.lam, by
      rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]⟩
  have hsU : 0 < D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i) := sU_pos hBE hSf hu
  set p := D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam) with hp
  set sU := D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i) with hsUdef
  set C := Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0)) with hC
  let φ : Fin m → ℝ → ℝ := fun k y => if k = i then psi p (D.gamma * sU) 0 0 0 y else 0
  let Φ : (Fin m → ℝ) → ℝ := fun a => C + psi p (D.gamma * sU) 0 0 0 (a i)
  have hle : ∀ w, Gf D θ (exposure D w) ≤ Φ (active w) := fun w =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth (active w))).1 (etf w)
  have heq : ∀ a : Fin m → ℝ, ∃ z, Gf D θ (exposure D (Sum.elim a z)) = Φ a := fun a =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth a)).2
  have hsep : ∀ a : Fin m → ℝ, Φ a = C + ∑ k, φ k (a k) := fun a => by
    simp only [Φ, φ]
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp
  have hdec := score_span θ hR hcE hkE
  have sJ := hsl wJ (by simp)
  have sm := hsl wm (by simp)
  have sf := hsl wf (by simp)
  have cJ := class_upper θ hI _ hdec Φ C φ hle heq hsep (fun k => D.wbar (Sum.inl k)) (fun k => le_rfl)
    hwJ (fun k => (hwJ.1 (Sum.inl k)).2) (fun w hw _ => hmJ hw) sJ.1 sJ.2
  have cm := class_upper θ hI _ hdec Φ C φ hle heq hsep (fun k => w0 D (Sum.inl k))
    (fun k => hI.1.2.2.2 _) hwm.1 hwm.2 (fun w hw hA => hmm ⟨hw, hA⟩) sm.1 sm.2
  have cf := class_frozen θ hI _ hdec Φ C φ hle heq hsep hwf hmf sf.1 sf.2
  have hpt : ∀ k y, φ k y + psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
      (w0 D (Sum.inl k)) y = psi (al k) (D.gamma * vv k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
      (w0 D (Sum.inl k)) y := by
    intro k y
    by_cases hk : k = i
    · subst hk; simp only [φ, al, vv, ↓reduceIte, psi]; ring
    · simp only [φ, al, vv, hk, ↓reduceIte, zero_add]
  simp only [hpt] at cJ cm cf
  have hc : ∀ k, 0 < D.gamma * vv k := fun k => by
    by_cases hk : k = i
    · subst hk; simp only [vv, ↓reduceIte]; exact mul_pos hγ (by linarith [hv k, hsU])
    · simp only [vv, hk, ↓reduceIte]; exact mul_pos hγ (hv k)
  have fin := finish C al (fun k => D.gamma * vv k) (fun k => D.kplus (Sum.inl k))
    (fun k => D.kminus (Sum.inl k)) (fun k => w0 D (Sum.inl k)) (fun k => D.wbar (Sum.inl k)) hc
    (fun k => (hI.2.1 _).1) (fun k => (hI.2.1 _).2) (fun k => w0_nonneg hI _) (fun k => hI.1.2.2.2 _)
    (fun k => wJ (Sum.inl k)) (fun k => wm (Sum.inl k)) _ _ _ cJ.1 cm.1 cf cJ.2 cm.2
    (fun k => hwJ.1 (Sum.inl k)) (fun k => ⟨(hwm.1.1 (Sum.inl k)).1, hwm.2 k⟩)
  exact ⟨fin.2.1, fin.2.2.2⟩

/-! ### Part 4 -/

section Frictions

lemma gval_ge {c mm d δ : ℝ} (hc : 0 < c) (h0 : 0 ≤ δ) (h1 : δ ≤ d) :
    mm * δ - c / 2 * δ ^ 2 ≤ gval c mm d := by
  unfold gval
  split_ifs with ha hb
  · nlinarith
  · have : mm ^ 2 / (2 * c) - (mm * δ - c / 2 * δ ^ 2) = (mm - c * δ) ^ 2 / (2 * c) := by
      field_simp; ring
    have := div_nonneg (sq_nonneg (mm - c * δ)) (by positivity : (0 : ℝ) ≤ 2 * c)
    linarith
  · push Not at ha hb
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h1), mul_le_mul_of_nonneg_left h1 hc.le]

lemma garg_val {c mm d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    garg c mm d ∈ Set.Icc 0 d ∧ mm * garg c mm d - c / 2 * garg c mm d ^ 2 = gval c mm d := by
  unfold garg gval
  refine ⟨⟨le_max_left _ _, max_le hd (min_le_left _ _)⟩, ?_⟩
  split_ifs with ha hb
  · rw [max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg ha hc.le))]; ring
  · have hq : mm / c ≤ d := by rw [div_le_iff₀ hc]; linarith
    rw [min_eq_right hq, max_eq_right (div_nonneg (not_le.mp ha).le hc.le)]
    field_simp; ring
  · push Not at hb
    have hq : d ≤ mm / c := by rw [le_div_iff₀ hc]; linarith
    rw [min_eq_left hq, max_eq_right hd]

variable {m K : ℕ} {D : Data m K K S}

/-- The ETF cost `τ_E(u) = Σ_j [κ⁺_j u_j⁺ + κ⁻_j u_j⁻]`. -/
def tauE (D : Data m K K S) (u : Fin K → ℝ) : ℝ :=
  ∑ j, (D.kplus (Sum.inr j) * max (u j) 0 + D.kminus (Sum.inr j) * max (-u j) 0)

omit [Fintype S] in
lemma tauE_sub (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l) (u Δ : Fin K → ℝ) :
    tauE D (u + Δ) - tauE D u ≤ tauE D Δ := by
  simp only [tauE, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := cost_change (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) 0 (u j) (u j + Δ j) (hr _).1 (hr _).2
  simp only [sub_zero, zero_sub, Pi.add_apply] at h ⊢
  rw [show u j + Δ j - u j = Δ j by ring, show u j - (u j + Δ j) = -Δ j by ring] at h
  linarith

omit [Fintype S] in
lemma tauE_sum (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l) (δ : Fin m → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (s : Fin m → Fin K → ℝ) :
    tauE D (fun j => ∑ i, δ i * s i j) ≤ ∑ i, δ i * tauE D (s i) := by
  simp only [tauE, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : max (∑ i, δ i * s i j) 0 ≤ ∑ i, δ i * max (s i j) 0 :=
    max_le (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hδ i))
      (Finset.sum_nonneg fun i _ => mul_nonneg (hδ i) (le_max_right _ _))
  have h2 : max (-∑ i, δ i * s i j) 0 ≤ ∑ i, δ i * max (-s i j) 0 := by
    refine max_le ?_ (Finset.sum_nonneg fun i _ => mul_nonneg (hδ i) (le_max_right _ _))
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => by
      rw [show -(δ i * s i j) = δ i * (-s i j) by ring]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hδ i)
  have e : ∑ i, δ i * (D.kplus (Sum.inr j) * max (s i j) 0 + D.kminus (Sum.inr j) * max (-s i j) 0) =
      D.kplus (Sum.inr j) * ∑ i, δ i * max (s i j) 0 + D.kminus (Sum.inr j) * ∑ i, δ i * max (-s i j) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 (hr (Sum.inr j)).1, mul_le_mul_of_nonneg_left h2 (hr (Sum.inr j)).2]

omit [Fintype S] in
lemma tauE_neg_r (r : Fin K → ℝ) : tauE D (-r) = hP D r := by
  simp only [tauE, hP, Pi.neg_apply, neg_neg]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype S] in
lemma tauE_r (r : Fin K → ℝ) : tauE D r = hM D r := by
  simp only [tauE, hM]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `H` in part 4's setting: the fund objectives, less the ETF fees and costs. -/
lemma Hr_split (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ} {v : Fin m → ℝ}
    (hR : RefCase D Sf (diagonal v) 0) (w : Inst m K → ℝ) :
    Hr D θ w = ∑ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i))
      (w0 D (Sum.inl i)) (w (Sum.inl i)) - etf w ⬝ᵥ D.cE - tauE D (etf w - etf (w0 D)) := by
  have hτ : tau D (w - w0 D) = ∑ i, (D.kplus (Sum.inl i) * max (w (Sum.inl i) - w0 D (Sum.inl i)) 0 +
      D.kminus (Sum.inl i) * max (w0 D (Sum.inl i) - w (Sum.inl i)) 0) + tauE D (etf w - etf (w0 D)) := by
    simp only [tau, tauE, Fintype.sum_sum_type, Pi.sub_apply, neg_sub, etf]
  have hq : active w ⬝ᵥ (diagonal v *ᵥ active w) = ∑ i, v i * w (Sum.inl i) ^ 2 := by
    simp only [dotProduct, mulVec_diagonal, active]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have ha : active w ⬝ᵥ θ.alpha = ∑ i, θ.alpha i * w (Sum.inl i) := by
    simp only [dotProduct, active]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hψ : ∑ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i))
      (w0 D (Sum.inl i)) (w (Sum.inl i)) = ∑ i, θ.alpha i * w (Sum.inl i) -
      D.gamma / 2 * ∑ i, v i * w (Sum.inl i) ^ 2 -
      ∑ i, (D.kplus (Sum.inl i) * max (w (Sum.inl i) - w0 D (Sum.inl i)) 0 +
        D.kminus (Sum.inl i) * max (w0 D (Sum.inl i) - w (Sum.inl i)) 0) := by
    simp only [psi]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [Hr_ref θ hR, hτ, hq, ha, hψ, zero_mulVec, dotProduct_zero, add_zero]
  ring

omit [Fintype S] in
lemma move_active (x : Inst m K → ℝ) (δ : Fin m → ℝ) : active (move D x δ) = active x + δ := by
  funext i; simp [move, active]

omit [Fintype S] in
lemma move_etf (x : Inst m K → ℝ) (δ : Fin m → ℝ) :
    etf (move D x δ) = etf x - fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j := by
  funext j; simp [move, etf]

lemma exposure_move (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) (δ : Fin m → ℝ) :
    exposure D (move D x δ) = exposure D x := by
  have hr : ∀ i, D.BEᵀ *ᵥ ((D.BE⁻¹)ᵀ *ᵥ D.BA i) = D.BA i := fun i => by
    rw [mulVec_mulVec, ← transpose_mul, nonsing_inv_mul _ hBE, transpose_one, one_mulVec]
  have hsum : (fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j) = ∑ i, δ i • ((D.BE⁻¹)ᵀ *ᵥ D.BA i) := by
    funext j; simp [Finset.sum_apply]
  show D.BAᵀ *ᵥ active (move D x δ) + D.BEᵀ *ᵥ etf (move D x δ) = D.BAᵀ *ᵥ active x + D.BEᵀ *ᵥ etf x
  rw [move_active, move_etf, hsum, mulVec_add, mulVec_sub, mulVec_sum, bat_sum D δ]
  simp only [mulVec_smul, hr]
  abel

/-- The score change of a netted move: fund objectives, fee credit, and ETF cost change. -/
lemma score_move (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ} {v : Fin m → ℝ}
    (hR : RefCase D Sf (diagonal v) 0) (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) (δ : Fin m → ℝ) :
    score D (move D x δ) θ - score D x θ =
      ∑ i, (psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (x (Sum.inl i) + δ i) -
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (x (Sum.inl i))) +
      ∑ i, δ i * (((D.BE⁻¹)ᵀ *ᵥ D.BA i) ⬝ᵥ D.cE) -
      (tauE D ((etf x - etf (w0 D)) + -(fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j)) -
        tauE D (etf x - etf (w0 D))) := by
  rw [Novel.M2TwoStageSeparationProof.split, Novel.M2TwoStageSeparationProof.split D θ x,
    exposure_move hBE, Hr_split θ hR, Hr_split θ hR, move_etf]
  have hfund : ∀ i, move D x δ (Sum.inl i) = x (Sum.inl i) + δ i := fun i => rfl
  have hfee : (etf x - fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j) ⬝ᵥ D.cE =
      etf x ⬝ᵥ D.cE - ∑ i, δ i * (((D.BE⁻¹)ᵀ *ᵥ D.BA i) ⬝ᵥ D.cE) := by
    rw [sub_dotProduct]
    congr 1
    simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have htau : etf x - (fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j) - etf (w0 D) =
      (etf x - etf (w0 D)) + -(fun j => ∑ i, δ i * ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j) := by abel
  simp only [hfund]
  rw [hfee, htau, Finset.sum_sub_distrib]
  ring

variable {alpha c kp km xm : ℝ}

/-- Buying `δ` from `y ≤ x⁻` raises `ψ` by at least `(α - c x⁻ - κ⁺)δ - (c/2)δ²`. -/
lemma buy_lower (hc : 0 ≤ c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) {y δ : ℝ} (hy : y ≤ xm) (hδ : 0 ≤ δ) :
    (alpha - c * xm - kp) * δ - c / 2 * δ ^ 2 ≤ psi alpha c kp km xm (y + δ) - psi alpha c kp km xm y := by
  have hcc := cost_change kp km xm y (y + δ) hkp hkm
  rw [show y + δ - y = δ by ring, show y - (y + δ) = -δ by ring, max_eq_left hδ,
    max_eq_right (by linarith : -δ ≤ 0)] at hcc
  simp only [psi]
  nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hc hδ)]

/-- Selling `δ` from the incumbent changes `ψ` by exactly `(-α + c x⁻ - κ⁻)δ - (c/2)δ²`. -/
lemma sell_exact {δ : ℝ} (hδ : 0 ≤ δ) :
    psi alpha c kp km xm (xm - δ) - psi alpha c kp km xm xm = (-alpha + c * xm - km) * δ - c / 2 * δ ^ 2 := by
  simp only [psi]
  rw [show xm - δ - xm = -δ by ring, show xm - (xm - δ) = δ by ring, max_eq_right (by linarith : -δ ≤ 0),
    max_eq_left hδ, sub_self, max_self]
  ring

/-- Undoing a purchase: `ψ(y) - ψ(y - (y - x⁻)⁺) = (α - c x⁻ - κ⁺)δ - (c/2)δ²` with `δ = (y - x⁻)⁺`. -/
lemma undo_buy (y : ℝ) :
    psi alpha c kp km xm y - psi alpha c kp km xm (y - max (y - xm) 0) =
      (alpha - c * xm - kp) * max (y - xm) 0 - c / 2 * max (y - xm) 0 ^ 2 := by
  rcases le_total y xm with h | h
  · rw [max_eq_right (by linarith : y - xm ≤ 0)]; ring
  · rw [max_eq_left (by linarith : 0 ≤ y - xm), show y - (y - xm) = xm by ring]
    simp only [psi]
    rw [max_eq_left (by linarith : 0 ≤ y - xm), max_eq_right (by linarith : xm - y ≤ 0), sub_self, max_self]
    ring

end Frictions

theorem frictions4 : Frictions4 := by
  intro m K S _ D θ Sf v hI hR hBE hv hγ wJ hwJ hmJ wm hwm hmm wf hwf hmf r c A0 room δL δU δS δV hL hU hS hV
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  have hc : ∀ i, 0 < c i := fun i => mul_pos hγ (hv i)
  have hw0 := fun i => w0_nonneg hI (D := D) (Sum.inl i)
  have hwb : ∀ i, w0 D (Sum.inl i) ≤ D.wbar (Sum.inl i) := fun i => hI.1.2.2.2 _
  have hroom : ∀ i, 0 ≤ room i := fun i => sub_nonneg.mpr (hwb i)
  -- the ETF cost of the netting trades
  have hτP : ∀ (x : Inst m K → ℝ) (δ : Fin m → ℝ), (∀ i, 0 ≤ δ i) →
      tauE D ((etf x - etf (w0 D)) + -(fun j => ∑ i, δ i * r i j)) - tauE D (etf x - etf (w0 D)) ≤
        ∑ i, δ i * hP D (r i) := fun x δ hδ => by
    refine (tauE_sub hr _ _).trans ?_
    have e : -(fun j => ∑ i, δ i * r i j) = fun j => ∑ i, δ i * (-r i) j := by
      funext j; simp [Finset.sum_neg_distrib]
    rw [e]
    refine (tauE_sum hr δ hδ (fun i => -r i)).trans (le_of_eq ?_)
    simp only [tauE_neg_r]
  have hτM : ∀ (x : Inst m K → ℝ) (δ : Fin m → ℝ), (∀ i, 0 ≤ δ i) →
      tauE D ((etf x - etf (w0 D)) + -(fun j => ∑ i, (-δ i) * r i j)) - tauE D (etf x - etf (w0 D)) ≤
        ∑ i, δ i * hM D (r i) := fun x δ hδ => by
    refine (tauE_sub hr _ _).trans ?_
    have e : -(fun j => ∑ i, (-δ i) * r i j) = fun j => ∑ i, δ i * r i j := by
      funext j; simp [Finset.sum_neg_distrib]
    rw [e]
    refine (tauE_sum hr δ hδ r).trans (le_of_eq ?_)
    simp only [tauE_r]
  have hfneg : ∀ δ : Fin m → ℝ, ∑ i, (-δ i) * (r i ⬝ᵥ D.cE) = -∑ i, δ i * (r i ⬝ᵥ D.cE) := fun δ => by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lower bound on `C^-`: buy `δL` from the `E^-` optimum, netted
    have hδ : ∀ i, 0 ≤ δL i := fun i => (garg_val (hc i) (hroom i)).1.1
    have hmv := score_move θ hR hBE wm δL
    have h1 : score D (move D wm δL) θ ≤ score D wJ θ := hmJ hL
    have hf : ∀ i, (θ.alpha i - c i * w0 D (Sum.inl i) - D.kplus (Sum.inl i)) * δL i - c i / 2 * δL i ^ 2 ≤
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wm (Sum.inl i) + δL i) -
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wm (Sum.inl i)) := fun i =>
      buy_lower (hc i).le (hr _).1 (hr _).2 (hwm.2 i) (hδ i)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hf i
    have htau := hτP wm δL hδ
    have hg : ∑ i, gval (c i) (A0 i - D.kplus (Sum.inl i) - hP D (r i)) (room i) =
        ∑ i, ((θ.alpha i - c i * w0 D (Sum.inl i) - D.kplus (Sum.inl i)) * δL i - c i / 2 * δL i ^ 2) +
        ∑ i, δL i * (r i ⬝ᵥ D.cE) - ∑ i, δL i * hP D (r i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← (garg_val (hc i) (hroom i)).2]
      simp only [A0, δL]; ring
    linarith
  · -- upper bound on `C^-`: undo the joint optimum's purchases, netted
    have hδ : ∀ i, 0 ≤ δU i := fun i => le_max_right _ _
    have hmv := score_move θ hR hBE wJ (fun i => -δU i)
    simp only [show ∀ i, (D.BE⁻¹)ᵀ *ᵥ D.BA i = r i from fun i => rfl] at hmv
    have hfund : ∀ i, move D wJ (fun i => -δU i) (Sum.inl i) ≤ w0 D (Sum.inl i) := fun i => by
      show wJ (Sum.inl i) + -δU i ≤ w0 D (Sum.inl i)
      have := le_max_left (wJ (Sum.inl i) - w0 D (Sum.inl i)) 0
      simp only [δU]; linarith
    have h1 : score D (move D wJ (fun i => -δU i)) θ ≤ score D wm θ := hmm ⟨hU, hfund⟩
    have hf : ∀ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wJ (Sum.inl i) + -δU i) -
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wJ (Sum.inl i)) =
        -((θ.alpha i - c i * w0 D (Sum.inl i) - D.kplus (Sum.inl i)) * δU i - c i / 2 * δU i ^ 2) := fun i => by
      rw [← sub_eq_add_neg, ← undo_buy]; ring
    simp only [hf, hfneg] at hmv
    have htau := hτM wJ δU hδ
    have hle : ∀ i, (A0 i - D.kplus (Sum.inl i) + hM D (r i)) * δU i - c i / 2 * δU i ^ 2 ≤
        gval (c i) (A0 i - D.kplus (Sum.inl i) + hM D (r i)) (room i) := fun i =>
      gval_ge (hc i) (hδ i) (by
        have := (hwJ.1 (Sum.inl i)).2
        simp only [δU, room]; exact max_le (by linarith) (hroom i))
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
    have hsplit : ∑ i, ((A0 i - D.kplus (Sum.inl i) + hM D (r i)) * δU i - c i / 2 * δU i ^ 2) =
        ∑ i, ((θ.alpha i - c i * w0 D (Sum.inl i) - D.kplus (Sum.inl i)) * δU i - c i / 2 * δU i ^ 2) +
        ∑ i, δU i * (r i ⬝ᵥ D.cE) + ∑ i, δU i * hM D (r i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [A0]; ring
    rw [Finset.sum_neg_distrib] at hmv
    linarith
  · -- lower bound on `J^- - J^0`: sell `δS` from the `E^0` optimum, netted
    have hδ : ∀ i, 0 ≤ δS i := fun i => (garg_val (hc i) (hw0 i)).1.1
    have hfa : ∀ i, wf (Sum.inl i) = w0 D (Sum.inl i) := fun i => congrFun hwf.2 i
    have hmv := score_move θ hR hBE wf (fun i => -δS i)
    simp only [show ∀ i, (D.BE⁻¹)ᵀ *ᵥ D.BA i = r i from fun i => rfl] at hmv
    have hfund : ∀ i, move D wf (fun i => -δS i) (Sum.inl i) ≤ w0 D (Sum.inl i) := fun i => by
      show wf (Sum.inl i) + -δS i ≤ w0 D (Sum.inl i); rw [hfa]; linarith [hδ i]
    have h1 : score D (move D wf (fun i => -δS i)) θ ≤ score D wm θ := hmm ⟨hS, hfund⟩
    have hf : ∀ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wf (Sum.inl i) + -δS i) -
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wf (Sum.inl i)) =
        (-θ.alpha i + c i * w0 D (Sum.inl i) - D.kminus (Sum.inl i)) * δS i - c i / 2 * δS i ^ 2 := fun i => by
      rw [hfa, ← sub_eq_add_neg]; exact sell_exact (hδ i)
    simp only [hf, hfneg] at hmv
    have htau := hτM wf δS hδ
    have hg : ∑ i, gval (c i) (-A0 i - D.kminus (Sum.inl i) - hM D (r i)) (w0 D (Sum.inl i)) =
        ∑ i, ((-θ.alpha i + c i * w0 D (Sum.inl i) - D.kminus (Sum.inl i)) * δS i - c i / 2 * δS i ^ 2) -
        ∑ i, δS i * (r i ⬝ᵥ D.cE) - ∑ i, δS i * hM D (r i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← (garg_val (hc i) (hw0 i)).2]
      simp only [A0, δS]; ring
    linarith
  · -- upper bound on `J^- - J^0`: buy back the `E^-` optimum's sales, netted
    have hδ : ∀ i, 0 ≤ δV i := fun i => sub_nonneg.mpr (hwm.2 i)
    have hmv := score_move θ hR hBE wm δV
    have hE0 : move D wm δV ∈ E0 D := ⟨hV, by
      funext i; show wm (Sum.inl i) + δV i = w0 D (Sum.inl i); simp only [δV]; ring⟩
    have h1 : score D (move D wm δV) θ ≤ score D wf θ := hmf hE0
    have hf : ∀ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wm (Sum.inl i) + δV i) -
        psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i)) (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
          (wm (Sum.inl i)) =
        -((-θ.alpha i + c i * w0 D (Sum.inl i) - D.kminus (Sum.inl i)) * δV i - c i / 2 * δV i ^ 2) := fun i => by
      have e1 : wm (Sum.inl i) + δV i = w0 D (Sum.inl i) := by simp only [δV]; ring
      have e2 : wm (Sum.inl i) = w0 D (Sum.inl i) - δV i := by simp only [δV]; ring
      rw [e1]; conv_lhs => rw [e2]
      rw [← sell_exact (hδ i)]; ring
    simp only [hf] at hmv
    have htau := hτP wm δV hδ
    have hle : ∀ i, (-A0 i - D.kminus (Sum.inl i) + hP D (r i)) * δV i - c i / 2 * δV i ^ 2 ≤
        gval (c i) (-A0 i - D.kminus (Sum.inl i) + hP D (r i)) (w0 D (Sum.inl i)) := fun i =>
      gval_ge (hc i) (hδ i) (by simp only [δV]; linarith [(hwm.1.1 (Sum.inl i)).1])
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hle i
    have hsplit : ∑ i, ((-A0 i - D.kminus (Sum.inl i) + hP D (r i)) * δV i - c i / 2 * δV i ^ 2) =
        ∑ i, ((-θ.alpha i + c i * w0 D (Sum.inl i) - D.kminus (Sum.inl i)) * δV i - c i / 2 * δV i ^ 2) -
        ∑ i, δV i * (r i ⬝ᵥ D.cE) + ∑ i, δV i * hP D (r i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [A0]; ring
    rw [Finset.sum_neg_distrib] at hmv
    linarith

theorem proof : Standalone.M7EtfOnlyRestrictionCost.statement :=
  ⟨structure', oneFund, spanning2, unreach3, frictions4⟩

end

end Novel.M7EtfOnlyRestrictionCostProof

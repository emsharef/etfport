import Standalone.M7IncumbentAwareFirstStage
import Novel.M7TwoStageExactnessLossProof
import Novel.M7EtfsAtZeroCostsBudgetProof

/-!
# Claim 111: proof

The Lagrangian inequality at a point with trade-sign slopes and a budget multiplier gives the joint
criterion's sufficiency and, after regrouping the ETF lines through `w = x^E + Q x^A`, part 1's strong
supergradient inequality. The lower bound on the loss is strong concavity along the segment from the
joint optimum. The quadratic-form lemmas are claim 040's (`qf_add`, `qf_nonneg`, `eq_of_qf`).
-/

namespace Novel.M7IncumbentAwareFirstStageProof

open Matrix Standalone.M2ScoreAccounting Standalone.M2ActionClasses Standalone.M7TwoStageExactnessLoss
  Standalone.M7IncumbentAwareFirstStage Standalone.M7FundDecisionEtfsAtZero

noncomputable section

variable {m K : ℕ} {S : Type} [Fintype S]

/-! ### The score, the costs and the budget -/

section General

variable {m n K : ℕ} (D : Data m n K S) (θ : Params m K)

/-- The score is an exact quadratic plus the cost: `Q(y) = Q(x) + g(x)'(y - x) - (γ/2)(y - x)'Σ(y - x)
- [τ(y - x⁻) - τ(x - x⁻)]`. -/
lemma score_expand' (x d : Inst m n → ℝ) :
    score D (x + d) θ = score D x θ + grad D θ x ⬝ᵥ d -
      D.gamma / 2 * (d ⬝ᵥ (covariance D *ᵥ d)) -
      (tau D (x + d - w0 D) - tau D (x - w0 D)) := by
  have hq := Novel.M2SoftTargetTwoStageProof.quad_seg D x d 1
  rw [one_smul] at hq
  have hs : ∀ w, score D w θ = mu D θ ⬝ᵥ w - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) -
      tau D (w - w0 D) := fun w => by
    rw [score, ← Novel.M7TwoStageExactnessLossProof.mu_dot]
  have hg : grad D θ x ⬝ᵥ d = mu D θ ⬝ᵥ d - D.gamma * (x ⬝ᵥ (covariance D *ᵥ d)) := by
    simp only [grad, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm (covariance D *ᵥ x), Novel.M7TwoStageExactnessLossProof.cov_symm D d x]
  rw [hs, hs, hg, dotProduct_add, hq]
  ring

/-- The score is an exact quadratic plus the cost: `Q(y) = Q(x) + g(x)'(y - x) - (γ/2)(y - x)'Σ(y - x)
- [τ(y - x⁻) - τ(x - x⁻)]`. -/
lemma score_expand (x y : Inst m n → ℝ) :
    score D y θ = score D x θ + grad D θ x ⬝ᵥ (y - x) -
      D.gamma / 2 * ((y - x) ⬝ᵥ (covariance D *ᵥ (y - x))) -
      (tau D (y - w0 D) - tau D (x - w0 D)) := by
  have := score_expand' D θ x (y - x)
  rwa [add_sub_cancel] at this

/-- A slope in `T_l(x)` is a subgradient of instrument `l`'s cost at `x`. -/
lemma cost_sub (hr : RatesNonneg D) {x : Inst m n → ℝ} {l : Inst m n} {t : ℝ}
    (ht : InSlope D x l t) (y : Inst m n → ℝ) :
    t * (y l - x l) ≤ (D.kplus l * max ((y - w0 D) l) 0 + D.kminus l * max (-(y - w0 D) l) 0) -
      (D.kplus l * max ((x - w0 D) l) 0 + D.kminus l * max (-(x - w0 D) l) 0) := by
  obtain ⟨h1, h2, hp, hm⟩ := ht
  obtain ⟨hkp, hkm⟩ := hr l
  simp only [Pi.sub_apply]
  set a := y l
  set h := x l
  set xm := w0 D l
  have c1 : t * (a - xm) ≤ D.kplus l * max (a - xm) 0 + D.kminus l * max (-(a - xm)) 0 := by
    rcases le_total a xm with ha | ha
    · rw [max_eq_right (by linarith : a - xm ≤ 0), max_eq_left (by linarith : 0 ≤ -(a - xm))]
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ xm - a)]
    · rw [max_eq_left (by linarith : 0 ≤ a - xm), max_eq_right (by linarith : -(a - xm) ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : 0 ≤ a - xm)]
  have c2 : D.kplus l * max (h - xm) 0 + D.kminus l * max (-(h - xm)) 0 = t * (h - xm) := by
    rcases lt_trichotomy h xm with hh | hh | hh
    · rw [hm hh, max_eq_right (by linarith : h - xm ≤ 0), max_eq_left (by linarith : 0 ≤ -(h - xm))]
      ring
    · rw [hh]; simp
    · rw [hp hh, max_eq_left (by linarith : 0 ≤ h - xm), max_eq_right (by linarith : -(h - xm) ≤ 0)]
      ring
  have e : t * (a - h) = t * (a - xm) - t * (h - xm) := by ring
  linarith

lemma tau_sub (hr : RatesNonneg D) {x : Inst m n → ℝ} {t : Inst m n → ℝ}
    (ht : ∀ l, InSlope D x l (t l)) (y : Inst m n → ℝ) :
    ∑ l, t l * (y l - x l) ≤ tau D (y - w0 D) - tau D (x - w0 D) := by
  simp only [tau, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun l _ => cost_sub D hr (ht l) y

omit [Fintype S] in
lemma cash_diff (x y : Inst m n → ℝ) :
    cash D y - cash D x = -∑ l, (y l - x l) - (tau D (y - w0 D) - tau D (x - w0 D)) := by
  simp only [cash]
  have : ∑ l, (y l - w0 D l) - ∑ l, (x l - w0 D l) = ∑ l, (y l - x l) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  linarith

/-- The Lagrangian inequality: with `η ≥ 0`, `η k(x) = 0` and slopes `t_l ∈ T_l(x)`, every `y` with
`k(y) ≥ 0` has `Q(y) ≤ Q(x) + Σ_l R_l (y_l - x_l) - (γ/2)(y - x)'Σ(y - x)`, where
`R_l = g_l(x) - η - (1 + η) t_l`. -/
lemma lagr (hr : RatesNonneg D) {x : Inst m n → ℝ} {η : ℝ} {t : Inst m n → ℝ} (hη : 0 ≤ η)
    (hc : η * cash D x = 0) (ht : ∀ l, InSlope D x l (t l)) {y : Inst m n → ℝ} (hy : 0 ≤ cash D y) :
    score D y θ ≤ score D x θ + ∑ l, (grad D θ x l - η - (1 + η) * t l) * (y l - x l) -
      D.gamma / 2 * ((y - x) ⬝ᵥ (covariance D *ᵥ (y - x))) := by
  have he := score_expand D θ x y
  have hd := cash_diff D x y
  have hs := tau_sub D hr ht y
  have hid : ∑ l, (grad D θ x l - η - (1 + η) * t l) * (y l - x l) =
      grad D θ x ⬝ᵥ (y - x) - η * ∑ l, (y l - x l) - (1 + η) * ∑ l, t l * (y l - x l) := by
    simp only [dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : 0 ≤ η * cash D y := mul_nonneg hη hy
  have h2 : (1 + η) * ∑ l, t l * (y l - x l) ≤
      (1 + η) * (tau D (y - w0 D) - tau D (x - w0 D)) :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  have h3 : η * cash D y = η * (cash D y - cash D x) := by rw [mul_sub, hc, sub_zero]
  rw [hd] at h3
  nlinarith

/-- The box signs make each term of the Lagrangian inequality nonpositive on the box. -/
lemma box_term {xbar x y R : ℝ} (hb : BoxSign xbar x R) (hy0 : 0 ≤ y) (hy1 : y ≤ xbar) :
    R * (y - x) ≤ 0 := by
  obtain ⟨b1, b2⟩ := hb
  rcases lt_trichotomy y x with h | h | h
  · have := b2 (by linarith)
    nlinarith
  · rw [h, sub_self, mul_zero]
  · have := b1 (by linarith)
    nlinarith

lemma cov_nonneg (hq : ∀ s, 0 ≤ D.q s) (d : Inst m n → ℝ) : 0 ≤ d ⬝ᵥ (covariance D *ᵥ d) := by
  rw [Novel.M2SoftTargetTwoStageProof.cov_bilin]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (mul_self_nonneg _)

/-- The joint criterion is sufficient (no AX-13 needed). -/
lemma suff (hI : Standalone.M2TwoStageSeparation.Inputs D) {x : Inst m n → ℝ}
    (h : JointCriterion D θ x) : IsMaxOn (fun w => score D w θ) (F D) x := by
  obtain ⟨η, t, hη, hc, ht, hb⟩ := h
  intro y hy
  show score D y θ ≤ score D x θ
  have hl := lagr D θ hI.2.1 hη hc ht hy.2
  have hsum : ∑ l, (grad D θ x l - η - (1 + η) * t l) * (y l - x l) ≤ 0 :=
    Finset.sum_nonpos fun l _ => box_term (hb l) (hy.1 l).1 (hy.1 l).2
  have hq := mul_nonneg (by linarith [hI.2.2.2] : 0 ≤ D.gamma / 2) (cov_nonneg D hI.2.2.1 (y - x))
  linarith

omit [Fintype S] in
/-- `F` is convex. -/
lemma F_seg (hr : RatesNonneg D) {x y : Inst m n → ℝ} (hx : x ∈ F D) (hy : y ∈ F D) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : (1 - ε) • x + ε • y ∈ F D := by
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(hx.1 i).1, (hy.1 i).1]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(hx.1 i).2, (hy.1 i).2]
  · have := Novel.M2ActionClassesProof.cash_concave D hr (by linarith : 0 ≤ 1 - ε) h0 (by ring) x y
    nlinarith [hx.2, hy.2]

/-- Strong concavity at the joint optimum: `Q(x_J) - Q(y) ≥ (γ/2)(x_J - y)'Σ(x_J - y)` for every
`y ∈ F`. -/
lemma strong (hI : Standalone.M2TwoStageSeparation.Inputs D) {xJ : Inst m n → ℝ} (hxJ : xJ ∈ F D)
    (hmax : IsMaxOn (fun w => score D w θ) (F D) xJ) {y : Inst m n → ℝ} (hy : y ∈ F D) :
    D.gamma / 2 * ((xJ - y) ⬝ᵥ (covariance D *ᵥ (xJ - y))) ≤ score D xJ θ - score D y θ := by
  set δ := y - xJ with hδ
  have hsym : (xJ - y) ⬝ᵥ (covariance D *ᵥ (xJ - y)) = δ ⬝ᵥ (covariance D *ᵥ δ) := by
    rw [show xJ - y = -δ by simp [hδ], mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  rw [hsym]
  set B := D.gamma / 2 * (δ ⬝ᵥ (covariance D *ᵥ δ))
  have hB : 0 ≤ B := mul_nonneg (by linarith [hI.2.2.2]) (cov_nonneg D hI.2.2.1 δ)
  have hy2 := score_expand D θ xJ y
  rw [← hδ] at hy2
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → B - (score D xJ θ - score D y θ) ≤ ε * B := by
    intro ε he0 he1
    have hmem := F_seg D hI.2.1 hxJ hy he0.le he1
    have hle : score D ((1 - ε) • xJ + ε • y) θ ≤ score D xJ θ := hmax hmem
    have hd : (1 - ε) • xJ + ε • y - xJ = ε • δ := by
      funext l; simp only [hδ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have he := score_expand D θ xJ ((1 - ε) • xJ + ε • y)
    rw [hd] at he
    have ht := Novel.M2ActionClassesProof.tau_convex D hI.2.1 (by linarith : 0 ≤ 1 - ε) he0.le
      (xJ - w0 D) (y - w0 D)
    rw [← Novel.M2ActionClassesProof.comb_sub xJ y (w0 D) (by ring)] at ht
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at he
    have hgd : grad D θ xJ ⬝ᵥ δ - (tau D (y - w0 D) - tau D (xJ - w0 D)) =
        score D y θ - score D xJ θ + D.gamma / 2 * (δ ⬝ᵥ (covariance D *ᵥ δ)) := by
      rw [hy2]; ring
    have h3 : ε * (B - (score D xJ θ - score D y θ)) ≤ ε * (ε * B) := by
      simp only [B] at hgd ⊢
      nlinarith
    exact le_of_mul_le_mul_left h3 he0
  have hΛ : 0 ≤ score D xJ θ - score D y θ := sub_nonneg.2 (hmax hy)
  by_contra hcon
  push Not at hcon
  set A := B - (score D xJ θ - score D y θ) with hAdef
  have hA : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have h := key (A / (2 * B)) (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have e : A / (2 * B) * B = A / 2 := by field_simp
  linarith

end General

/-! ### Quadratic forms -/

section Quad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completing the square: `s'd - (c/2) d'Ad ≤ s'A⁻¹s/(2c)` for `A` positive definite and `c > 0`. -/
lemma csq {A : Matrix ι ι ℝ} (h : A.PosDef) {c : ℝ} (hc : 0 < c) (s d : ι → ℝ) :
    s ⬝ᵥ d - c / 2 * (d ⬝ᵥ (A *ᵥ d)) ≤ s ⬝ᵥ (A⁻¹ *ᵥ s) / (2 * c) := by
  have hs := Novel.M7FundDecisionEtfsAtZeroProof.symm_of_posDef h
  have hU : IsUnit A.det := h.det_pos.ne'.isUnit
  set u := c⁻¹ • (A⁻¹ *ᵥ s) with hu
  have hAu : A *ᵥ u = c⁻¹ • s := by
    rw [hu, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have key := Novel.M7FundDecisionEtfsAtZeroProof.qf_nonneg h (d + (-1 : ℝ) • u)
  rw [Novel.M7FundDecisionEtfsAtZeroProof.qf_add hs, Novel.M7FundDecisionEtfsAtZeroProof.qf_smul]
    at key
  simp only [Novel.M7FundDecisionEtfsAtZeroProof.qf, mulVec_smul, hAu, dotProduct_smul,
    smul_eq_mul] at key
  have e1 : u ⬝ᵥ s = c⁻¹ * (s ⬝ᵥ (A⁻¹ *ᵥ s)) := by
    rw [hu, smul_dotProduct, smul_eq_mul, dotProduct_comm]
  rw [e1, dotProduct_comm d s] at key
  set q := d ⬝ᵥ (A *ᵥ d)
  set sd := s ⬝ᵥ d
  set Q := s ⬝ᵥ (A⁻¹ *ᵥ s)
  have k2 := mul_nonneg (by positivity : 0 ≤ c / 2) key
  have e : c / 2 * (q + 2 * (-1 * (c⁻¹ * sd)) + (-1) ^ 2 * (c⁻¹ * (c⁻¹ * Q))) =
      c / 2 * q - sd + Q / (2 * c) := by
    field_simp
    ring
  linarith

end Quad

/-! ### The claim's coordinates -/

section Claim

variable {D : Data m K K S} {θ : Params m K} {Sf : Matrix (Fin K) (Fin K) ℝ}
  {V : Matrix (Fin m) (Fin m) ℝ}

lemma Qm_eq (D : Data m K K S) : Qm D = (D.BEᵀ)⁻¹ * D.BAᵀ := by
  rw [← transpose_nonsing_inv]
  ext j i
  simp [Qm, rvec, mulVec, dotProduct, Matrix.mul_apply]

lemma qT (D : Data m K K S) (v : Fin K → ℝ) (i : Fin m) : ((Qm D)ᵀ *ᵥ v) i = rvec D i ⬝ᵥ v := by
  simp [Qm, mulVec, dotProduct]

omit [Fintype S] in
lemma unitT (hBE : IsUnit D.BE.det) : IsUnit D.BEᵀ.det := by rwa [det_transpose]

/-- `b(x) = B^E' w(x)`. -/
lemma expo_eq (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) : exposure D x = D.BEᵀ *ᵥ wexp D x := by
  simp only [wexp, Qm_eq, exposure, mulVec_add, mulVec_mulVec,
    mul_nonsing_inv_cancel_left _ _ (unitT hBE)]
  abel

lemma wexp_sub (x y : Inst m K → ℝ) : wexp D y - wexp D x = wexp D (y - x) := by
  have ha : active (y - x) = active y - active x := rfl
  have he : etf (y - x) = etf y - etf x := rfl
  simp only [wexp, ha, he, mulVec_sub]
  abel

omit [Fintype S] in
lemma sig_posDef (hBE : IsUnit D.BE.det) (hSf : Sf.PosDef) : (SigEE D Sf).PosDef := by
  have hinj : Function.Injective (D.BEᵀ).mulVec := by
    intro u v h
    have := congrArg (fun z => (D.BEᵀ)⁻¹ *ᵥ z) h
    simpa only [mulVec_mulVec, nonsing_inv_mul _ (unitT hBE), one_mulVec] using this
  have := hSf.conjTranspose_mul_mul_same hinj
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this

lemma qf_expo (hBE : IsUnit D.BE.det) (d : Inst m K → ℝ) :
    exposure D d ⬝ᵥ (Sf *ᵥ exposure D d) = qf (SigEE D Sf) (wexp D d) := by
  rw [expo_eq hBE, qf, SigEE, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec (wexp D d) D.BE, ← mulVec_transpose]

/-- With `Σ_E = 0`: `d'Σd = w(d)'Σ_EE w(d) + d_A'V d_A`. -/
lemma cov_split (hR : RefCase D Sf V 0) (hBE : IsUnit D.BE.det) (d : Inst m K → ℝ) :
    d ⬝ᵥ (covariance D *ᵥ d) = qf (SigEE D Sf) (wexp D d) + qf V (active d) := by
  rw [Novel.M7TwoStageExactnessLossProof.cov_ref hR d d, zero_mulVec, dotProduct_zero, add_zero,
    qf_expo hBE]
  rfl

lemma qfV_nonneg (hI : Standalone.M2TwoStageSeparation.Inputs D) (hR : RefCase D Sf V 0)
    (hBE : IsUnit D.BE.det) (u : Fin m → ℝ) : 0 ≤ qf V u := by
  set z : Inst m K → ℝ := Sum.elim u (-(Qm D *ᵥ u))
  have ha : active z = u := rfl
  have he : etf z = -(Qm D *ᵥ u) := rfl
  have hw : wexp D z = 0 := by rw [wexp, ha, he, neg_add_cancel]
  have := cov_nonneg D hI.2.2.1 z
  rw [cov_split hR hBE, hw, ha] at this
  simpa [qf] using this

omit [Fintype S] in
lemma qfE_nonneg (hBE : IsUnit D.BE.det) (hSf : Sf.PosDef) (u : Fin K → ℝ) :
    0 ≤ qf (SigEE D Sf) u :=
  Novel.M7FundDecisionEtfsAtZeroProof.qf_nonneg (sig_posDef hBE hSf) u

lemma gE_eq (hR : RefCase D Sf V 0) (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) :
    gE D θ x = (D.BE *ᵥ θ.lam - D.cE) - D.gamma • (SigEE D Sf *ᵥ wexp D x) := by
  funext j
  simp only [gE, Novel.M7TwoStageExactnessLossProof.grad_etf θ hR, zero_mulVec, Pi.zero_apply,
    mul_zero, sub_zero, expo_eq hBE, SigEE, mulVec_sub, mulVec_smul, mulVec_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mul_assoc]
  ring

lemma gA_eq (hR : RefCase D Sf V 0) (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) :
    gA D θ x = θ.alpha + (Qm D)ᵀ *ᵥ D.cE - D.gamma • (V *ᵥ active x) + (Qm D)ᵀ *ᵥ gE D θ x := by
  set e := θ.lam - D.gamma • (Sf *ᵥ exposure D x)
  have hg : gE D θ x = D.BE *ᵥ e - D.cE := by
    funext j
    simp only [gE, Novel.M7TwoStageExactnessLossProof.grad_etf θ hR, zero_mulVec, Pi.zero_apply,
      mul_zero, sub_zero, Pi.sub_apply, e]
  have hQ : (Qm D)ᵀ *ᵥ D.cE + (Qm D)ᵀ *ᵥ gE D θ x = D.BA *ᵥ e := by
    rw [hg, ← mulVec_add, add_sub_cancel, Qm_eq, transpose_mul, transpose_transpose,
      transpose_nonsing_inv, transpose_transpose, mulVec_mulVec, Matrix.mul_assoc,
      nonsing_inv_mul _ hBE, Matrix.mul_one]
  funext i
  have h1 := Novel.M7TwoStageExactnessLossProof.grad_fund θ hR x i
  have h2 := congrFun hQ i
  simp only [gA, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  rw [h1]
  linarith

theorem marginals : Marginals := by
  intro m K S _ D θ Sf V hS x
  have hc : (Qm D)ᵀ *ᵥ D.cE = fun i => rvec D i ⬝ᵥ D.cE := funext fun i => qT D D.cE i
  refine ⟨rfl, rfl, rfl, gE_eq hS.2.1 hS.2.2.1 x, ?_⟩
  rw [gA_eq hS.2.1 hS.2.2.1 x, hc]
  rfl

/-- Claim 102's identity with claim 040's reduced marginal: `g_i = A_i + r_i'g_E`. -/
lemma fund_id (hR : RefCase D Sf V 0) (hBE : IsUnit D.BE.det) (x : Inst m K → ℝ) (i : Fin m) :
    gA D θ x i = Ared D θ V 0 x i + rvec D i ⬝ᵥ gE D θ x := by
  have h := congrFun (gA_eq (θ := θ) hR hBE x) i
  rw [h]
  simp only [Ared, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, qT, zero_mulVec,
    smul_zero, add_zero]

/-! ### Part 1 -/

theorem supergradient : Supergradient := by
  intro m K S _ D θ Sf V hS x₂ hx₂ η t ζ hM x hx
  obtain ⟨hI, hR, hBE, hSf, hγ⟩ := hS
  obtain ⟨hη, hc, ht, hζ0, hζx, hbox⟩ := hM
  have hl := lagr D θ hI.2.1 hη hc ht hx.2
  set s := resid D θ x₂ η t ζ with hsdef
  set dA := active x - active x₂ with hdA
  set dE := etf x - etf x₂ with hdE
  have hsplit : ∑ l, (grad D θ x₂ l - η - (1 + η) * t l) * (x l - x₂ l) =
      ∑ i, (gA D θ x₂ i - η - (1 + η) * t (Sum.inl i)) * dA i +
        ∑ j, (gE D θ x₂ j - η - (1 + η) * t (Sum.inr j)) * dE j :=
    Fintype.sum_sum_type _
  have hζ1 : 0 ≤ ζ ⬝ᵥ etf x :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hζ0 j) ((hx.1 (Sum.inr j)).1)
  have hζ2 : ζ ⬝ᵥ etf x₂ = 0 := Finset.sum_eq_zero fun j _ => hζx j
  have hw : wexp D x - wexp D x₂ = dE + Qm D *ᵥ dA := by
    simp only [wexp, hdA, hdE, mulVec_sub]
    abel
  have hQ : s ⬝ᵥ (Qm D *ᵥ dA) = ((Qm D)ᵀ *ᵥ s) ⬝ᵥ dA := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have hsE : s ⬝ᵥ dE = ∑ j, (gE D θ x₂ j - η - (1 + η) * t (Sum.inr j)) * dE j +
      (ζ ⬝ᵥ etf x - ζ ⬝ᵥ etf x₂) := by
    rw [← dotProduct_sub]
    simp only [hsdef, resid, dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hdE]; simp only [Pi.sub_apply]; ring
  have hA : ∑ i, (gA D θ x₂ i - η - (1 + η) * t (Sum.inl i)) * dA i =
      ∑ i, (gA D θ x₂ i - η - (1 + η) * t (Sum.inl i) - ((Qm D)ᵀ *ᵥ s) i) * dA i +
        ((Qm D)ᵀ *ᵥ s) ⬝ᵥ dA := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbx : ∑ i, (gA D θ x₂ i - η - (1 + η) * t (Sum.inl i) - ((Qm D)ᵀ *ᵥ s) i) * dA i ≤ 0 :=
    Finset.sum_nonpos fun i _ => box_term (hbox i) (hx.1 (Sum.inl i)).1 (hx.1 (Sum.inl i)).2
  have hcov := cov_split hR hBE (x - x₂)
  rw [← wexp_sub] at hcov
  have hsw : s ⬝ᵥ (wexp D x - wexp D x₂) = s ⬝ᵥ dE + s ⬝ᵥ (Qm D *ᵥ dA) := by
    rw [hw, dotProduct_add]
  have hact : active (x - x₂) = dA := rfl
  rw [hact] at hcov
  rw [hsplit, hcov] at hl
  rw [hsw, hQ, hsE]
  nlinarith

lemma eq_of_quad (hBE : IsUnit D.BE.det) (hSf : Sf.PosDef) (hV : V.PosDef) {a b : Inst m K → ℝ}
    (h1 : qf (SigEE D Sf) (wexp D a - wexp D b) ≤ 0) (h2 : qf V (active a - active b) ≤ 0) :
    a = b := by
  have hw := Novel.M7FundDecisionEtfsAtZeroProof.eq_of_qf (sig_posDef hBE hSf) h1
  have ha := Novel.M7FundDecisionEtfsAtZeroProof.eq_of_qf hV h2
  have he : etf a - etf b = 0 := by
    have e : wexp D a - wexp D b = (etf a - etf b) + Qm D *ᵥ (active a - active b) := by
      simp only [wexp, mulVec_sub]
      abel
    rwa [e, ha, mulVec_zero, add_zero] at hw
  funext l
  rcases l with i | j
  · have := congrFun ha i
    simp only [Pi.sub_apply, Pi.zero_apply, active] at this
    linarith
  · have := congrFun he j
    simp only [Pi.sub_apply, Pi.zero_apply, etf] at this
    linarith

theorem lossBounds : LossBounds := by
  intro m K S _ D θ Sf V hS xJ hxJ hmax x₂ hx₂
  obtain ⟨hI, hR, hBE, hSf, hγ⟩ := hS
  have hst := strong D θ hI hxJ hmax hx₂
  rw [cov_split hR hBE, ← wexp_sub, show active (xJ - x₂) = active xJ - active x₂ from rfl] at hst
  have hE0' := qfE_nonneg hBE hSf (wexp D xJ - wexp D x₂)
  have hV0' := qfV_nonneg hI hR hBE (active xJ - active x₂)
  refine ⟨hst, fun hV => ⟨fun h0 => ?_, fun h => by rw [h, sub_self]⟩, fun η t ζ hM => ?_⟩
  · have h1 : qf (SigEE D Sf) (wexp D xJ - wexp D x₂) ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hγ hc]
    have h2 : qf V (active xJ - active x₂) ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hγ hc]
    exact (eq_of_quad hBE hSf hV h1 h2).symm
  have hsup := supergradient m K S D θ Sf V ⟨hI, hR, hBE, hSf, hγ⟩ x₂ hx₂ η t ζ hM xJ hxJ
  set s := resid D θ x₂ η t ζ
  set d := wexp D xJ - wexp D x₂
  set qE := qf (SigEE D Sf) d
  set qV := qf V (active xJ - active x₂)
  have hE0 : 0 ≤ qE := qfE_nonneg hBE hSf d
  have hV0 : 0 ≤ qV := qfV_nonneg hI hR hBE _
  have hΛ0 : 0 ≤ score D xJ θ - score D x₂ θ := sub_nonneg.2 (hmax hx₂)
  have hcs := csq (sig_posDef hBE hSf) hγ s d
  have hqs : 0 ≤ qf (SigEE D Sf)⁻¹ s :=
    Novel.M7FundDecisionEtfsAtZeroProof.qf_nonneg (sig_posDef hBE hSf).inv s
  change s ⬝ᵥ d - D.gamma / 2 * qE ≤ qf (SigEE D Sf)⁻¹ s / (2 * D.gamma) at hcs
  have hsq : D.gamma ^ 2 * qE ≤ qf (SigEE D Sf)⁻¹ s := by
    have h1 : D.gamma / 2 * qE ≤ qf (SigEE D Sf)⁻¹ s / (2 * D.gamma) := by
      nlinarith [mul_nonneg hγ.le hV0]
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨hΛ0, by nlinarith, by nlinarith, hsq, ?_⟩
  rw [le_div_iff₀ hγ]
  have e : Real.sqrt (D.gamma ^ 2 * qE) = D.gamma * Real.sqrt qE := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]
  calc Real.sqrt qE * D.gamma = Real.sqrt (D.gamma ^ 2 * qE) := by rw [e, mul_comm]
    _ ≤ Real.sqrt (qf (SigEE D Sf)⁻¹ s) := Real.sqrt_le_sqrt hsq

/-! ### Part 2 -/

/-- With `V` positive definite, anything scoring at least the joint optimum is the joint optimum. -/
lemma max_eq (hS : Setting D Sf V) (hV : V.PosDef) {xJ : Inst m K → ℝ} (hxJ : xJ ∈ F D)
    (hmax : IsMaxOn (fun x => score D x θ) (F D) xJ) {x : Inst m K → ℝ} (hx : x ∈ F D)
    (hle : score D xJ θ ≤ score D x θ) : x = xJ := by
  obtain ⟨hI, hR, hBE, hSf, hγ⟩ := hS
  have hst := strong D θ hI hxJ hmax hx
  rw [cov_split hR hBE, ← wexp_sub, show active (xJ - x) = active xJ - active x from rfl] at hst
  have h1 := qfE_nonneg hBE hSf (wexp D xJ - wexp D x)
  have h2 := qfV_nonneg hI hR hBE (active xJ - active x)
  have hq : qf (SigEE D Sf) (wexp D xJ - wexp D x) + qf V (active xJ - active x) ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos (by linarith : 0 < D.gamma / 2) hc
    linarith
  exact (eq_of_quad hBE hSf hV (by linarith) (by linarith)).symm

lemma opt_of_zero (hS : Setting D Sf V) {x₂ : Inst m K → ℝ} (hx₂ : x₂ ∈ F D) {η : ℝ}
    {t : Inst m K → ℝ} {ζ : Fin K → ℝ} (hM : FibreMult D θ x₂ η t ζ)
    (h0 : resid D θ x₂ η t ζ = 0) : IsMaxOn (fun x => score D x θ) (F D) x₂ := by
  intro y hy
  show score D y θ ≤ score D x₂ θ
  have h := supergradient m K S D θ Sf V hS x₂ hx₂ η t ζ hM y hy
  rw [h0, zero_dotProduct] at h
  have h1 := qfE_nonneg hS.2.2.1 hS.2.2.2.1 (wexp D y - wexp D x₂)
  have h2 := qfV_nonneg hS.1 hS.2.1 hS.2.2.1 (active y - active x₂)
  nlinarith [hS.2.2.2.2]

lemma pinned {x₂ : Inst m K → ℝ} {η : ℝ} {t : Inst m K → ℝ} {ζ : Fin K → ℝ}
    (hM : FibreMult D θ x₂ η t ζ) (hc : 0 < cash D x₂) {j : Fin K} (hj : 0 < x₂ (Sum.inr j)) :
    (w0 D (Sum.inr j) < x₂ (Sum.inr j) →
      resid D θ x₂ η t ζ j = gE D θ x₂ j - D.kplus (Sum.inr j)) ∧
    (x₂ (Sum.inr j) < w0 D (Sum.inr j) →
      resid D θ x₂ η t ζ j = gE D θ x₂ j + D.kminus (Sum.inr j)) := by
  obtain ⟨_, hcη, ht, _, hζx, _⟩ := hM
  have hη0 : η = 0 := (mul_eq_zero.1 hcη).resolve_right hc.ne'
  have hζ0 : ζ j = 0 := (mul_eq_zero.1 (hζx j)).resolve_right hj.ne'
  obtain ⟨_, _, hp, hm⟩ := ht (Sum.inr j)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [resid, hη0, hζ0, hp h]
    ring
  · simp only [resid, hη0, hζ0, hm h]
    ring

lemma exists_zero (hS : Setting D Sf V) (hax : AX13) {x₂ : Inst m K → ℝ} (hx₂ : x₂ ∈ F D)
    (hcap : ∀ j, x₂ (Sum.inr j) < D.wbar (Sum.inr j))
    (hopt : IsMaxOn (fun x => score D x θ) (F D) x₂) :
    ∃ η t ζ, FibreMult D θ x₂ η t ζ ∧ resid D θ x₂ η t ζ = 0 := by
  obtain ⟨η, t, hη, hc, ht, hb⟩ :=
    (Novel.M7TwoStageExactnessLossProof.jointOptimality hax m K K S D θ hS.1 x₂ hx₂).1 hopt
  let ζ : Fin K → ℝ := fun j => -(gE D θ x₂ j - η - (1 + η) * t (Sum.inr j))
  have h0 : resid D θ x₂ η t ζ = 0 := by
    funext j
    simp only [resid, ζ, Pi.zero_apply]
    ring
  refine ⟨η, t, ζ, ⟨hη, hc, ht, fun j => ?_, fun j => ?_, fun i => ?_⟩, h0⟩
  · have := (hb (Sum.inr j)).1 (hcap j)
    simp only [ζ, gE]
    linarith
  · by_cases hp : 0 < x₂ (Sum.inr j)
    · have hR : grad D θ x₂ (Sum.inr j) - η - (1 + η) * t (Sum.inr j) = 0 :=
        le_antisymm ((hb (Sum.inr j)).1 (hcap j)) ((hb (Sum.inr j)).2 hp)
      simp only [ζ, gE, hR, neg_zero, zero_mul]
    · have : x₂ (Sum.inr j) = 0 := le_antisymm (not_lt.1 hp) (hx₂.1 _).1
      rw [this, mul_zero]
  · rw [h0, mulVec_zero, Pi.zero_apply, sub_zero]
    exact hb (Sum.inl i)

/-- Fibre multipliers with `s = 0` are claim 109's criterion (part 4a's joint criterion). -/
lemma criterion_iff (hS : Setting D Sf V) {x₂ : Inst m K → ℝ} (hx₂ : x₂ ∈ F D) :
    (∃ η t ζ, FibreMult D θ x₂ η t ζ ∧ resid D θ x₂ η t ζ = 0) ↔
      Standalone.M7EtfsAtZeroCostsBudget.Criterion D θ V 0 x₂ := by
  obtain ⟨hI, hR, hBE, _, _⟩ := hS
  have hw0 : ∀ l, 0 ≤ w0 D l := fun l => div_nonneg (hI.1.2.1 l) hI.1.1.le
  constructor
  · rintro ⟨η, t, ζ, ⟨hη, hc, ht, hζ0, hζx, hbox⟩, h0⟩
    have hline : ∀ j, grad D θ x₂ (Sum.inr j) = η + (1 + η) * t (Sum.inr j) - ζ j := fun j => by
      have := congrFun h0 j
      simp only [resid, gE, Pi.zero_apply] at this
      linarith
    let t' : Inst m K → ℝ := Sum.elim (fun i => t (Sum.inl i))
      (fun j => if x₂ (Sum.inr j) = 0 then tconv D j else t (Sum.inr j))
    let ζ' : Fin K → ℝ := fun j =>
      if x₂ (Sum.inr j) = 0 then ζ j + (1 + η) * (tconv D j - t (Sum.inr j)) else ζ j
    have hline' : ∀ j, grad D θ x₂ (Sum.inr j) = η + (1 + η) * t' (Sum.inr j) - ζ' j := fun j => by
      by_cases h : x₂ (Sum.inr j) = 0
      · simp only [t', ζ', h, ite_true, Sum.elim_inr]
        rw [hline j]
        ring
      · simp only [t', ζ', h, ite_false, Sum.elim_inr]
        exact hline j
    -- at zero, the convention's slope is admissible, and it is at least `t_j`
    have hconv : ∀ j, x₂ (Sum.inr j) = 0 →
        InSlope D x₂ (Sum.inr j) (tconv D j) ∧ t (Sum.inr j) ≤ tconv D j := fun j h => by
      obtain ⟨hkp, hkm⟩ := hI.2.1 (Sum.inr j)
      obtain ⟨a1, a2, _, hm⟩ := ht (Sum.inr j)
      by_cases hw : w0 D (Sum.inr j) = 0
      · simp only [tconv, hw, ite_true]
        refine ⟨⟨by linarith, le_rfl, fun h' => ?_, fun h' => ?_⟩, a2⟩
        · simp [h, hw] at h'
        · simp [h, hw] at h'
      · have hlt : x₂ (Sum.inr j) < w0 D (Sum.inr j) := by
          rw [h]; exact lt_of_le_of_ne (hw0 _) (Ne.symm hw)
        have ht' := hm hlt
        simp only [tconv, hw, ite_false]
        refine ⟨?_, ht'.le⟩
        have := ht (Sum.inr j)
        rwa [ht'] at this
    refine ⟨η, t', ζ', hη, hc, ?_, ?_, fun j => ⟨?_, fun hp => ?_, hline' j⟩, fun i => ?_, fun i => ?_⟩
    · rintro (i | j)
      · exact ht (Sum.inl i)
      · by_cases h : x₂ (Sum.inr j) = 0
        · simp only [t', h, ite_true, Sum.elim_inr]
          exact (hconv j h).1
        · simp only [t', h, ite_false, Sum.elim_inr]
          exact ht (Sum.inr j)
    · intro j h
      simp only [t', h, ite_true, Sum.elim_inr]
    · by_cases h : x₂ (Sum.inr j) = 0
      · simp only [ζ', h, ite_true]
        have := (hconv j h).2
        have := hζ0 j
        nlinarith
      · simp only [ζ', h, ite_false]
        exact hζ0 j
    · have h : x₂ (Sum.inr j) ≠ 0 := hp.ne'
      simp only [ζ', h, ite_false]
      exact (mul_eq_zero.1 (hζx j)).resolve_right h
    · have hg : gE D θ x₂ = fun j => η + (1 + η) * t' (Sum.inr j) - ζ' j := funext hline'
      have hf := fund_id (θ := θ) hR hBE x₂ i
      simp only [gA] at hf
      rw [hf, hg]
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    · have := hbox i
      rw [h0, mulVec_zero, Pi.zero_apply, sub_zero] at this
      exact this
  · rintro ⟨η, t, ζ, hη, hc, ht, _, hE, _, hB⟩
    have h0 : resid D θ x₂ η t ζ = 0 := by
      funext j
      simp only [resid, gE, Pi.zero_apply, (hE j).2.2]
      ring
    refine ⟨η, t, ζ, ⟨hη, hc, ht, fun j => (hE j).1, fun j => ?_, fun i => ?_⟩, h0⟩
    · by_cases hp : 0 < x₂ (Sum.inr j)
      · rw [(hE j).2.1 hp, zero_mul]
      · rw [le_antisymm (not_lt.1 hp) (hx₂.1 _).1, mul_zero]
    · rw [h0, mulVec_zero, Pi.zero_apply, sub_zero]
      exact hB i

theorem exactness : Exactness := by
  intro m K S _ D θ Sf V hS xJ hxJ hmax x₂ hx₂
  have hopt_of : score D x₂ θ = score D xJ θ → IsMaxOn (fun x => score D x θ) (F D) x₂ :=
    fun e y hy => by
      show score D y θ ≤ score D x₂ θ
      rw [e]
      exact hmax hy
  refine ⟨criterion_iff hS hx₂, fun η t ζ hM h0 => ?_,
    fun hax hcap e => exists_zero hS hax hx₂ hcap (hopt_of e),
    fun η t ζ hM hc j hj => pinned hM hc hj, fun hax hcap e hc η t ζ hM j hj hne => ?_⟩
  · have hopt := opt_of_zero hS hx₂ hM h0
    have e : score D x₂ θ = score D xJ θ := le_antisymm (hmax hx₂) (hopt hxJ)
    exact ⟨e, fun hV => max_eq hS hV hxJ hmax hx₂ e.ge⟩
  · obtain ⟨η', t', ζ', hM', h0'⟩ := exists_zero hS hax hx₂ hcap (hopt_of e)
    have z : resid D θ x₂ η' t' ζ' j = 0 := by rw [h0']; rfl
    rcases lt_or_gt_of_ne hne with h | h
    · rw [(pinned hM hc hj).2 h]
      rw [(pinned hM' hc hj).2 h] at z
      exact z
    · rw [(pinned hM hc hj).1 h]
      rw [(pinned hM' hc hj).1 h] at z
      exact z

/-! ### Part 3 -/

lemma stage1_line {x₁ : Inst m K → ℝ} {η₁ : ℝ} {t₁ ζ₁ : Fin K → ℝ}
    (h1 : StageOneMult D θ x₁ η₁ t₁ ζ₁) (hc : 0 < cash D x₁) {j : Fin K}
    (hj : 0 < x₁ (Sum.inr j)) : gE D θ x₁ j = t₁ j := by
  obtain ⟨_, hcη, _, _, hζx, hl⟩ := h1
  have hη0 : η₁ = 0 := (mul_eq_zero.1 hcη).resolve_right hc.ne'
  have hζ0 : ζ₁ j = 0 := (mul_eq_zero.1 (hζx j)).resolve_right hj.ne'
  have := hl j
  rw [hη0, hζ0] at this
  linarith

lemma gE_fibre (hS : Setting D Sf V) {x y : Inst m K → ℝ} (h : wexp D x = wexp D y) :
    gE D θ x = gE D θ y := by
  rw [gE_eq hS.2.1 hS.2.2.1, gE_eq hS.2.1 hS.2.2.1, h]

lemma kept_zero (hS : Setting D Sf V) {x₁ x₂ : Inst m K → ℝ} (hw : wexp D x₂ = wexp D x₁)
    {η₁ : ℝ} {t₁ ζ₁ : Fin K → ℝ} (h1 : StageOneMult D θ x₁ η₁ t₁ ζ₁) (hc1 : 0 < cash D x₁)
    {η : ℝ} {t : Inst m K → ℝ} {ζ : Fin K → ℝ} (hM : FibreMult D θ x₂ η t ζ) (hc2 : 0 < cash D x₂)
    {j : Fin K} (hj1 : 0 < x₁ (Sum.inr j)) (hj2 : 0 < x₂ (Sum.inr j))
    (hdir : (w0 D (Sum.inr j) < x₁ (Sum.inr j) ∧ w0 D (Sum.inr j) < x₂ (Sum.inr j)) ∨
      (x₁ (Sum.inr j) < w0 D (Sum.inr j) ∧ x₂ (Sum.inr j) < w0 D (Sum.inr j))) :
    resid D θ x₂ η t ζ j = 0 := by
  have hl := stage1_line h1 hc1 hj1
  have hg := congrFun (gE_fibre (θ := θ) hS hw) j
  obtain ⟨_, _, ht1, _, _, _⟩ := h1
  obtain ⟨_, _, hp, hm⟩ := ht1 j
  rcases hdir with ⟨a, b⟩ | ⟨a, b⟩
  · rw [(pinned hM hc2 hj2).1 b, hg, hl, hp a]
    ring
  · rw [(pinned hM hc2 hj2).2 b, hg, hl, hm a]
    ring

theorem holdAll : HoldAll := by
  intro m K S _ D θ Sf V hS x₁ hx₁ η₁ t₁ ζ₁ h1 hfund
  have hI := hS.1
  obtain ⟨hη, hcη, ht1, hζ0, hζx, hl⟩ := h1
  have hact : ∀ i, x₁ (Sum.inl i) = w0 D (Sum.inl i) := fun i => congrFun hx₁.2 i
  have h1η : 0 < 1 + η₁ := by linarith
  let u : Fin m → ℝ := fun i => (gA D θ x₁ i - η₁) / (1 + η₁)
  let tA : Fin m → ℝ := fun i => max (-D.kminus (Sum.inl i)) (min (D.kplus (Sum.inl i)) (u i))
  have hJC : JointCriterion D θ x₁ := by
    refine ⟨η₁, Sum.elim tA t₁, hη, hcη, ?_, ?_⟩
    · rintro (i | j)
      · obtain ⟨hkp, hkm⟩ := hI.2.1 (Sum.inl i)
        refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _), fun h => ?_, fun h => ?_⟩
        · rw [hact i] at h
          exact absurd h (lt_irrefl _)
        · rw [hact i] at h
          exact absurd h (lt_irrefl _)
      · exact ht1 j
    · rintro (i | j)
      · obtain ⟨hlo, hhi⟩ := hfund i
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have hup : u i ≤ D.kplus (Sum.inl i) := by
            simp only [u]
            rw [div_le_iff₀ h1η]
            linarith [hhi h]
          have : u i ≤ tA i := le_max_of_le_right (le_min hup le_rfl)
          have hu : (1 + η₁) * u i = gA D θ x₁ i - η₁ := by
            simp only [u]
            field_simp
          show grad D θ x₁ (Sum.inl i) - η₁ - (1 + η₁) * tA i ≤ 0
          simp only [gA] at hu
          nlinarith
        · have hlo' : -D.kminus (Sum.inl i) ≤ u i := by
            simp only [u]
            rw [le_div_iff₀ h1η]
            linarith [hlo h]
          have : tA i ≤ u i := max_le hlo' (min_le_right _ _)
          have hu : (1 + η₁) * u i = gA D θ x₁ i - η₁ := by
            simp only [u]
            field_simp
          show 0 ≤ grad D θ x₁ (Sum.inl i) - η₁ - (1 + η₁) * tA i
          simp only [gA] at hu
          nlinarith
      · have hR : grad D θ x₁ (Sum.inr j) - η₁ - (1 + η₁) * t₁ j = -ζ₁ j := by
          have := hl j
          simp only [gE] at this
          linarith
        refine ⟨fun _ => ?_, fun h => ?_⟩
        · show grad D θ x₁ (Sum.inr j) - η₁ - (1 + η₁) * t₁ j ≤ 0
          rw [hR]
          linarith [hζ0 j]
        · have : ζ₁ j = 0 := (mul_eq_zero.1 (hζx j)).resolve_right h.ne'
          show 0 ≤ grad D θ x₁ (Sum.inr j) - η₁ - (1 + η₁) * t₁ j
          rw [hR, this, neg_zero]
  have hopt := suff D θ hI hJC
  refine ⟨hopt, fun hV x₂ hx₂ hmax2 => ?_⟩
  have hle : score D x₁ θ ≤ score D x₂ θ := hmax2 ⟨hx₁.1, rfl⟩
  exact max_eq hS hV hx₁.1 hopt hx₂.1 hle

theorem allTraded : AllTraded := by
  intro m K S _ D θ Sf V hS x₁ hx₁ η₁ t₁ ζ₁ h1 hc1 hE1 x₂ hx₂ hc2 hE2 η t ζ hM
  have h0 : resid D θ x₂ η t ζ = 0 := by
    funext j
    have hdir : (w0 D (Sum.inr j) < x₁ (Sum.inr j) ∧ w0 D (Sum.inr j) < x₂ (Sum.inr j)) ∨
        (x₁ (Sum.inr j) < w0 D (Sum.inr j) ∧ x₂ (Sum.inr j) < w0 D (Sum.inr j)) := by
      rcases lt_or_gt_of_ne (hE1 j).2 with h | h
      · exact Or.inr ⟨h, (hE2 j).2.2 h⟩
      · exact Or.inl ⟨h, (hE2 j).2.1 h⟩
    exact kept_zero hS hx₂.2 h1 hc1 hM hc2 (hE1 j).1 (hE2 j).1 hdir
  exact ⟨h0, opt_of_zero hS hx₂.1 hM h0⟩

theorem fixedEtfs : FixedEtfs := by
  intro m K S _ D θ Sf V hS x₁ hx₁ η₁ t₁ ζ₁ h1 hc1 x₂ hx₂ hc2 T hT hF
  refine ⟨fun η t ζ hM j hj =>
    kept_zero hS hx₂.2 h1 hc1 hM hc2 (hT j hj).1 (hT j hj).2.1 (hT j hj).2.2, fun j hj => ?_,
    fun hfund => ?_⟩
  · have hw := congrFun hx₂.2 j
    have hact : active x₁ = active (w0 D) := hx₁.2
    have he : x₂ (Sum.inr j) = x₁ (Sum.inr j) := hF j hj
    simp only [wexp, Pi.add_apply, etf] at hw
    rw [← hact, mulVec_sub, Pi.sub_apply]
    linarith
  · choose τ hτ using hfund
    obtain ⟨_, hcη1, ht1, hζ0, hζx, hl⟩ := h1
    have hη0 : η₁ = 0 := (mul_eq_zero.1 hcη1).resolve_right hc1.ne'
    have hg : gE D θ x₂ = gE D θ x₁ := gE_fibre hS hx₂.2
    have hJC : JointCriterion D θ x₂ := by
      refine ⟨0, Sum.elim τ t₁, le_rfl, by simp, ?_, ?_⟩
      · rintro (i | j)
        · exact (hτ i).1
        · by_cases hj : j ∈ T
          · obtain ⟨_, _, hdir⟩ := hT j hj
            obtain ⟨a1, a2, hp, hm⟩ := ht1 j
            refine ⟨a1, a2, fun h => ?_, fun h => ?_⟩
            · rcases hdir with ⟨b1, _⟩ | ⟨_, b2⟩
              · exact hp b1
              · exact absurd (h.trans b2) (lt_irrefl _)
            · rcases hdir with ⟨_, b2⟩ | ⟨b1, _⟩
              · exact absurd (h.trans b2) (lt_irrefl _)
              · exact hm b1
          · have := ht1 j
            unfold InSlope at this ⊢
            rw [hF j hj]
            exact this
      · rintro (i | j)
        · have := (hτ i).2
          show BoxSign _ _ (grad D θ x₂ (Sum.inl i) - 0 - (1 + 0) * τ i)
          simpa [gA] using this
        · have hR : grad D θ x₂ (Sum.inr j) - 0 - (1 + 0) * t₁ j = -ζ₁ j := by
            have h3 := hl j
            have hgj := congrFun hg j
            simp only [gE] at h3 hgj
            rw [hη0] at h3
            rw [hgj]
            linarith
          refine ⟨fun _ => ?_, fun h => ?_⟩
          · show grad D θ x₂ (Sum.inr j) - 0 - (1 + 0) * t₁ j ≤ 0
            rw [hR]
            linarith [hζ0 j]
          · have hpos1 : 0 < x₁ (Sum.inr j) := by
              by_cases hj : j ∈ T
              · exact (hT j hj).1
              · rw [← hF j hj]
                exact h
            have : ζ₁ j = 0 := (mul_eq_zero.1 (hζx j)).resolve_right hpos1.ne'
            show 0 ≤ grad D θ x₂ (Sum.inr j) - 0 - (1 + 0) * t₁ j
            rw [hR, this, neg_zero]
    exact suff D θ hS.1 hJC

end Claim

theorem proof : Standalone.M7IncumbentAwareFirstStage.statement :=
  ⟨marginals, supergradient, lossBounds, exactness, holdAll, allTraded, fixedEtfs⟩

end

end Novel.M7IncumbentAwareFirstStageProof

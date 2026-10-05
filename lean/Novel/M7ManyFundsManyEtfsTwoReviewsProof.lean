import Novel.M7TwoReviewsBindingBudgetProof
import Novel.M7OneEtfTwoScalarsProof
import Standalone.M7ManyFundsManyEtfsTwoReviews

/-!
# Claim 048: proof

Part 1 is claim 044's parts 2 and 4(a), which hold for any finite instrument set. Part 2 rests on
the factor form of the root's marginals:
- `g_{0,E} = B^E w`, where `w = λ̂ - γ Σ~_f b_0` is the factor marginal;
- `g_{0,i} = α̂_i - γ v_i x_i + (B^A w)_i = α̂_i - γ v_i x_i + r_i' g_{0,E}`, since `R B^E = I`.
The frictionless interior ETF lines are equalities, `g_{0,E} = η̂_0 1 - S_E`, so
`w = R(η̂_0 1 - S_E)`, which is the exposure display. A fund's line is then
`α^res_i - γ v_i x_i - (1 + η̂_0) t_i` in the box's normal cone, so the fund is claim 104's band
holding at the scaled rates. Sufficiency reverses the substitution, with claim 110's clip
subgradient supplying the slopes, and concludes by claim 044's sufficiency. Part 3 is algebra on
the lines.
-/

namespace Novel.M7ManyFundsManyEtfsTwoReviewsProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7ManyFundsManyEtfsTwoReviews Finset
open Standalone.M7TwoStageExactnessLoss (bandHold psi)
open Novel.M7TwoReviewsBindingBudgetProof (bs_le etaHat_nonneg)

noncomputable section

set_option linter.unusedSectionVars false

variable {N K : ℕ} {Z : Type} [Fintype Z]

/-- The factor marginal `w = λ̂ - γ Σ~_f b`. -/
def fw (F : Fac N K) (γ : ℝ) (x : Ins N K → ℝ) (k : Fin K) : ℝ :=
  F.lh k - γ * ∑ l, F.Sf k l * expo F x l

lemma sig_apply (F : Fac N K) (x : Ins N K → ℝ) (a : Ins N K) :
    ∑ b, facSig F a b * x b = ∑ k, Bf F a k * ∑ l, F.Sf k l * expo F x l +
      Sum.elim (fun i => F.v i * x (Sum.inl i)) (fun _ => 0) a := by
  simp only [facSig, add_mul, sum_add_distrib]
  congr 1
  · simp only [expo, sum_mul, mul_sum]
    rw [sum_comm]; refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]; exact sum_congr rfl fun l _ => sum_congr rfl fun b _ => by ring
  · rcases a with i | j
    · simp [Fintype.sum_sum_type]
    · simp

lemma g0_etf {P : Two (Ins N K) Z} {F : Fac N K} (hm : P.mu0 = facMu F) (hs : P.S0 = facSig F)
    (x : Ins N K → ℝ) (j : Fin K) :
    g0 P x (Sum.inr j) = ∑ k, F.BE j k * fw F P.gamma x k := by
  simp only [g0, marg, hm, hs, sig_apply, facMu, Sum.elim_inr, Bf, fw, add_zero, mul_sub,
    sum_sub_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

lemma g0_fund {P : Two (Ins N K) Z} {F : Fac N K} (hm : P.mu0 = facMu F) (hs : P.S0 = facSig F)
    (x : Ins N K → ℝ) (i : Fin N) :
    g0 P x (Sum.inl i) = F.ah i - P.gamma * F.v i * x (Sum.inl i) + ∑ k, F.BA i k * fw F P.gamma x k := by
  simp only [g0, marg, hm, hs, sig_apply, facMu, Sum.elim_inl, Bf, fw, mul_sub, sum_sub_distrib,
    mul_sum, mul_add]
  have e : ∑ k, ∑ l, P.gamma * (F.BA i k * (F.Sf k l * expo F x l)) =
      ∑ k, ∑ l, F.BA i k * (P.gamma * (F.Sf k l * expo F x l)) :=
    sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [e]; ring

/-- `Σ_k R_kj Σ_j' B^E_j'k y_j' = y_j`. -/
lemma R_BE {F : Fac N K} (hF : FacHyp F) (y : Fin K → ℝ) (j : Fin K) :
    ∑ k, F.R k j * ∑ j', F.BE j' k * y j' = y j := by
  have e : ∑ k, F.R k j * ∑ j', F.BE j' k * y j' = ∑ j', (∑ k, F.BE j' k * F.R k j) * y j' := by
    simp only [mul_sum, sum_mul]; rw [sum_comm]
    exact sum_congr rfl fun j' _ => sum_congr rfl fun k _ => by ring
  rw [e]; simp [hF.2.1, ite_mul]

/-- `Σ_j B^E_jk... `: applying `R` to `B^E w` recovers `w`. -/
lemma R_of_BE {F : Fac N K} (hF : FacHyp F) (w : Fin K → ℝ) (k : Fin K) :
    ∑ j, F.R k j * ∑ k', F.BE j k' * w k' = w k := by
  have e : ∑ j, F.R k j * ∑ k', F.BE j k' * w k' = ∑ k', (∑ j, F.R k j * F.BE j k') * w k' := by
    simp only [mul_sum, sum_mul]; rw [sum_comm]
    exact sum_congr rfl fun k' _ => sum_congr rfl fun j _ => by ring
  rw [e]; simp [hF.1, ite_mul]

/-- `Σ_j r_ij Σ_k B^E_jk w_k = (B^A w)_i`. -/
lemma net_BE {F : Fac N K} (hF : FacHyp F) (w : Fin K → ℝ) (i : Fin N) :
    ∑ j, netw F i j * ∑ k, F.BE j k * w k = ∑ k, F.BA i k * w k := by
  have e : ∑ j, netw F i j * ∑ k, F.BE j k * w k =
      ∑ k', F.BA i k' * ∑ j, F.R k' j * ∑ k, F.BE j k * w k := by
    simp only [netw, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun k' _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [e]
  exact sum_congr rfl fun k' _ => by rw [R_of_BE hF w k']

lemma BE_of_R {F : Fac N K} (hF : FacHyp F) (y : Fin K → ℝ) (j : Fin K) :
    ∑ k, F.BE j k * ∑ j', F.R k j' * y j' = y j := by
  have e : ∑ k, F.BE j k * ∑ j', F.R k j' * y j' = ∑ j', (∑ k, F.BE j k * F.R k j') * y j' := by
    simp only [mul_sum, sum_mul]; rw [sum_comm]
    exact sum_congr rfl fun j' _ => sum_congr rfl fun k _ => by ring
  rw [e]; simp [hF.2.1, ite_mul]

/-- The fund's line in residual form, given the ETFs' marginals `g_{0,E} = e 1 - S_E`. -/
lemma fund_line {P : Two (Ins N K) Z} {F : Fac N K} (hF : FacHyp F) (hm : P.mu0 = facMu F)
    (hs : P.S0 = facSig F) {x : Ins N K → ℝ} {e : ℝ} {η1 : Z → ℝ} {t1 : Z → Ins N K → ℝ}
    (hE : ∀ j, g0 P x (Sum.inr j) = e - Sinc P η1 t1 (Sum.inr j)) (i : Fin N) (t : ℝ) :
    g0 P x (Sum.inl i) + Sinc P η1 t1 (Sum.inl i) - e - (1 + e) * t =
      alphaRes P F e η1 t1 i - P.gamma * F.v i * x (Sum.inl i) - (1 + e) * t := by
  have hn := net_BE hF (fw F P.gamma x) i
  simp only [← g0_etf hm hs, hE] at hn
  rw [g0_fund hm hs, ← hn]
  simp only [alphaRes, mul_sub, sum_sub_distrib, ← sum_mul]
  rw [mul_comm (∑ j, netw F i j) e]
  ring

/-! ### Part 1 -/

theorem structure_ : Standalone.M7ManyFundsManyEtfsTwoReviews.Structure := by
  intro N K Z _ P hP
  refine ⟨fun X hX hL => Novel.M7TwoReviewsBindingBudgetProof.sufficient _ Z P hP X hX hL,
    fun hAX X hO => Novel.M7TwoReviewsBindingBudgetProof.necessary hAX _ Z P hP X hO,
    fun X η0 η1 t0 t1 hT hR hX0 hX1 =>
      (Novel.M7TwoReviewsBindingBudgetProof.twoScalar _ Z P hP X η0 η1 t0 t1 hT hR hX0 hX1).1⟩

/-! ### Part 2 -/

theorem separation : Separation := by
  intro N K Z _ P F hP ⟨hF, hm, hs, hE0⟩ X η0 η1 t0 t1 hX hT hR hh hEin
  dsimp only
  have h0 : η0 = 0 := by
    rcases mul_eq_zero.mp hR.2.1 with h | h
    · exact h
    · linarith
  set e := etaHat P η0 η1 with he
  -- the ETF lines are equalities
  have hE : ∀ j, g0 P X.1 (Sum.inr j) = e - Sinc P η1 t1 (Sum.inr j) := fun j => by
    obtain ⟨⟨ta, tb, -, -⟩, b1, b2⟩ := hR.2.2 (Sum.inr j)
    rw [(hE0 j).1] at tb; rw [(hE0 j).2] at ta
    have ht : t0 (Sum.inr j) = 0 := by linarith
    have e1 := b1 (hEin j).2; have e2 := b2 (hEin j).1
    rw [ht] at e1 e2; linarith
  have hw : ∀ k, fw F P.gamma X.1 k = ∑ j, F.R k j * (e - Sinc P η1 t1 (Sum.inr j)) := fun k => by
    rw [← R_of_BE hF (fw F P.gamma X.1) k]
    exact sum_congr rfl fun j _ => by rw [← g0_etf hm hs, hE]
  refine ⟨h0, fun k => ?_, fun i => ?_, fun j => ?_⟩
  · have := hw k
    simp only [fw] at this
    simp only [lamRes, mul_sub, sum_sub_distrib] at this ⊢
    linarith
  · have hr := hP.2.2.2.2.2.2.2.2 (Sum.inl i)
    have h1e : 0 < 1 + e := by linarith [etaHat_nonneg hP hR.1 fun z => (hT z).1]
    have hc : 0 < P.gamma * F.v i := mul_pos hP.1 (hF.2.2 i)
    obtain ⟨⟨ta, tb, tp, tm⟩, b1, b2⟩ := hR.2.2 (Sum.inl i)
    have hline := fund_line hF hm hs hE i (t0 (Sum.inl i))
    have hmem : X.1 (Sum.inl i) ∈ Set.Icc 0 (P.xbar (Sum.inl i)) := hX.1 (Sum.inl i)
    have hmax := Novel.M7TwoStageExactnessLossProof.max_of_slope (alpha := alphaRes P F e η1 t1 i)
      (c := P.gamma * F.v i) (kp := (1 + e) * P.kp (Sum.inl i)) (km := (1 + e) * P.km (Sum.inl i))
      (xm := P.xm (Sum.inl i)) (xbar := P.xbar (Sum.inl i)) (h := X.1 (Sum.inl i))
      (t := (1 + e) * t0 (Sum.inl i)) hc
      (by nlinarith) (by nlinarith) (fun h => by rw [tp (sub_pos.mpr h)]) (fun h => by rw [tm (sub_neg.mpr h)]; ring)
      (fun a ha => by
        have := bs_le (hR.2.2 (Sum.inl i)).2 hmem.1 hmem.2 ha.1 ha.2
        rw [hline] at this; linarith)
    exact Novel.M7TwoStageExactnessLossProof.eq_bandHold hc (by nlinarith [hr.1]) (by nlinarith [hr.2.1])
      hmem hmax
  · have hx : ∀ k, expo F X.1 k - ∑ i, F.BA i k * X.1 (Sum.inl i) = ∑ j', F.BE j' k * X.1 (Sum.inr j') := by
      intro k; simp only [expo, Fintype.sum_sum_type, Bf, Sum.elim_inl, Sum.elim_inr]; ring
    simp only [hx]
    exact (R_BE hF (fun j' => X.1 (Sum.inr j')) j).symm

theorem sepSufficient : SepSufficient := by
  intro N K Z _ P F hP ⟨hF, hm, hs, hE0⟩ X η1 t1 hX hT hEin
  dsimp only
  intro hexp hfund
  set e := etaHat P 0 η1 with he
  have he0 : 0 ≤ e := etaHat_nonneg hP le_rfl fun z => (hT z).1
  have h1e : 0 < 1 + e := by linarith
  have hw : ∀ k, fw F P.gamma X.1 k = ∑ j, F.R k j * (e - Sinc P η1 t1 (Sum.inr j)) := fun k => by
    have := hexp k
    simp only [lamRes] at this
    simp only [fw, mul_sub, sum_sub_distrib] at this ⊢
    linarith
  have hE : ∀ j, g0 P X.1 (Sum.inr j) = e - Sinc P η1 t1 (Sum.inr j) := fun j => by
    rw [g0_etf hm hs]
    simp only [hw]
    exact BE_of_R hF (fun j' => e - Sinc P η1 t1 (Sum.inr j')) j
  -- the funds' slopes from the clip
  have hsub : ∀ i, ∃ t, Slope (P.kp (Sum.inl i)) (P.km (Sum.inl i)) (X.1 (Sum.inl i) - P.xm (Sum.inl i)) t ∧
      BoxSign (P.xbar (Sum.inl i)) (X.1 (Sum.inl i))
        (alphaRes P F e η1 t1 i - P.gamma * F.v i * X.1 (Sum.inl i) - (1 + e) * t) := fun i => by
    have hr := hP.2.2.2.2.2.2.2.2 (Sum.inl i)
    obtain ⟨t, t1', t2', tp, tm, b1, b2⟩ := Novel.M7OneEtfTwoScalarsProof.clip_sub
      (a := alphaRes P F e η1 t1 i) (c := P.gamma * F.v i) (kp := (1 + e) * P.kp (Sum.inl i))
      (km := (1 + e) * P.km (Sum.inl i)) (mul_pos hP.1 (hF.2.2 i)) (by nlinarith [hr.1])
      (by nlinarith [hr.2.1]) hr.2.2.2.1 hr.2.2.2.2
    have hy : Novel.M7OneEtfTwoScalarsProof.clipB
        ((alphaRes P F e η1 t1 i - (1 + e) * P.kp (Sum.inl i)) / (P.gamma * F.v i))
        ((alphaRes P F e η1 t1 i + (1 + e) * P.km (Sum.inl i)) / (P.gamma * F.v i))
        (P.xm (Sum.inl i)) (P.xbar (Sum.inl i)) = X.1 (Sum.inl i) := (hfund i).symm
    simp only [hy] at tp tm b1 b2
    refine ⟨t / (1 + e), ⟨?_, ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
    · rw [le_div_iff₀ h1e]; linarith
    · rw [div_le_iff₀ h1e]; linarith
    · rw [tp (by linarith)]; field_simp
    · rw [tm (by linarith)]; field_simp
    · intro h; rw [mul_div_cancel₀ _ h1e.ne']; exact b1 h
    · intro h; rw [mul_div_cancel₀ _ h1e.ne']; exact b2 h
  choose tf htf using hsub
  refine Novel.M7TwoReviewsBindingBudgetProof.sufficient _ Z P hP X hX
    ⟨0, η1, Sum.elim tf (fun _ => 0), t1, hT, le_rfl, by rw [zero_mul], fun a => ?_⟩
  rcases a with i | j
  · refine ⟨(htf i).1, ?_⟩
    simp only [Sum.elim_inl]
    rw [fund_line hF hm hs hE i]
    exact (htf i).2
  · simp only [Sum.elim_inr]
    refine ⟨⟨by rw [(hE0 j).2]; simp, by rw [(hE0 j).1], fun _ => by rw [(hE0 j).1],
      fun _ => by rw [(hE0 j).2]; simp⟩, ?_⟩
    rw [hE j, ← he]
    constructor <;> intro _ <;> simp

/-! ### Part 3 -/

theorem interaction : Interaction := by
  intro N K Z _ P F hP ⟨hF, hm, hs, hE0⟩ X η0 η1 t0 t1 hT hR hh hEin bTB hTB
  have h0 : η0 = 0 := by
    rcases mul_eq_zero.mp hR.2.1 with h | h
    · exact h
    · linarith
  set e := etaHat P η0 η1 with he
  have hE : ∀ j, g0 P X.1 (Sum.inr j) = e - Sinc P η1 t1 (Sum.inr j) := fun j => by
    obtain ⟨⟨ta, tb, -, -⟩, b1, b2⟩ := hR.2.2 (Sum.inr j)
    rw [(hE0 j).1] at tb; rw [(hE0 j).2] at ta
    have ht : t0 (Sum.inr j) = 0 := by linarith
    have e1 := b1 (hEin j).2; have e2 := b2 (hEin j).1
    rw [ht] at e1 e2; linarith
  have hw : ∀ k, fw F P.gamma X.1 k = ∑ j, F.R k j * (e - Sinc P η1 t1 (Sum.inr j)) := fun k => by
    rw [← R_of_BE hF (fw F P.gamma X.1) k]
    exact sum_congr rfl fun j _ => by rw [← g0_etf hm hs, hE]
  refine ⟨fun k => ?_, fun j => ?_⟩
  · have := hw k
    have := hTB k
    simp only [fw] at *
    simp only [mul_sub, sum_sub_distrib] at *
    linarith
  · have ht : ∀ z, t1 z (Sum.inr j) = 0 := fun z => by
      obtain ⟨⟨ta, tb, -, -⟩, -⟩ := (hT z).2.2 (Sum.inr j)
      rw [(hE0 j).1] at tb; rw [(hE0 j).2] at ta; linarith
    simp only [Sinc, sval, ht, mul_zero, add_zero, he, etaHat, h0, zero_add, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun z _ => by ring

theorem proof : Standalone.M7ManyFundsManyEtfsTwoReviews.statement :=
  ⟨structure_, separation, sepSufficient, interaction⟩

end

end Novel.M7ManyFundsManyEtfsTwoReviewsProof

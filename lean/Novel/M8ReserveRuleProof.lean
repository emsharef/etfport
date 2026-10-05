import Standalone.M8ReserveRule
import Novel.M7TwoReviewsBoundsProof

/-!
# Claim 047: proof

Claim 046's state-by-state facts (`big_mult`, `covered_pos`) do the work. With cash carried, a state
covered by it has no positive multiplier. Every state's multiplier is at most `η̄`, because a larger
one needs nothing traded and all cash spent, but the cash is `h⁺_0 > 0` then. Part 3 is algebra on
claim 044's lines and readings. Part 4 is calculus on the active set.
-/

namespace Novel.M8ReserveRuleProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds Standalone.M8ReserveRule
  Novel.M7TwoReviewsBoundsProof Filter Topology

noncomputable section

variable {ι Z : Type} [Fintype ι]

lemma need_nonneg {P : Two ι Z} (hP : Hyp P) (z : Z) (x0 : ι → ℝ) : 0 ≤ need P z x0 :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [(rates hP i).1]) (le_max_right _ _)

lemma need_le_NN [Fintype Z] (P : Two ι Z) (z : Z) (x0 : ι → ℝ) : need P z x0 ≤ NN P x0 :=
  le_ciSup (f := fun z => need P z x0) (Set.finite_range _).bddAbove z

/-- With nothing traded tomorrow, the cash is today's. -/
lemma h1_of_nothing {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z}
    (hnt : ∀ i, X.2 z i = carry P z X.1 i) : h1 P X.1 X.2 z = h0 P X.1 := by
  have e1 := h1_eq P X z
  simp only [hnt, sub_self, pc, max_self, neg_zero, mul_zero, add_zero, Finset.sum_const_zero,
    sub_zero] at e1
  exact e1

/-- With cash carried, a covered state has no positive multiplier. -/
lemma zero_of_covered {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ}
    (hP : Hyp P) (hC : Cov P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (hpos : 0 < h0 P X.1)
    (hcov : need P z X.1 ≤ h0 P X.1) : e = 0 := by
  rcases h.1.eq_or_lt with h' | h'
  · exact h'.symm
  · exact absurd (covered_pos hP hC hX h hcov h').2 hpos.ne'

/-- With cash carried, every state's multiplier is at most `η̄`. -/
lemma le_etaBar_of_cash {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ}
    (hP : Hyp P) (hC : Cov P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (hpos : 0 < h0 P X.1) :
    e ≤ etaBar P z := by
  by_contra hgt
  push Not at hgt
  obtain ⟨hnt, hh1⟩ := big_mult hP hC hX h hgt
  rw [h1_of_nothing hnt] at hh1
  linarith

theorem noReserve : NoReserve := by
  intro ι Z _ _ P hP hC X hX η0 η1 t1 hT hpos hN
  have hz : ∀ z, η1 z = 0 := fun z =>
    zero_of_covered hP hC hX (hT z) hpos ((need_le_NN P z X.1).trans hN)
  exact ⟨hz, by simp [etaHat, hz]⟩

theorem revisionMax : RevisionMax := by
  intro mu0 b el ea elmax eamax hb hl ha
  have := mul_le_mul_of_nonneg_left hl hb
  constructor <;> linarith

theorem needBound : NeedBound := by
  intro ι Z _ _ P hP muMax gmin sig x0 hmu hg hsig hsig0 hx0
  refine Real.iSup_le (fun z => Finset.sum_le_sum fun i _ => ?_)
    (Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [(rates hP i).1]) (le_max_right _ _))
  have hk : 0 ≤ 1 + P.kp i := by linarith [(rates hP i).1]
  refine mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hk
  have hc : 0 < P.gamma * sig i := mul_pos hP.1 (hsig0 i)
  have h1 : xhat P z i ≤ max (muMax i - P.kp i) 0 / (P.gamma * sig i) := by
    unfold xhat
    rw [hsig z i]
    exact div_le_div_of_nonneg_right (max_le_max (by linarith [hmu z i]) le_rfl) hc.le
  have h2 : gmin i * x0 i ≤ carry P z x0 i := mul_le_mul_of_nonneg_right (hg z i) (hx0 i)
  linarith

theorem budgetChannel : BudgetChannel := by
  intro ι Z _ _ P hP hC X hX η1 t1 hT hpos
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hβ : 0 < P.beta := hP.2.1
  refine ⟨Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hq z).le, fun i => ?_⟩
  · split_ifs with hc
    · exact le_etaBar_of_cash hP hC hX (hT z) hpos
    · exact (zero_of_covered hP hC hX (hT z) hpos (not_lt.1 hc)).le
  · unfold Sinc
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) hβ.le
    refine mul_le_mul_of_nonneg_left ?_ (mul_pos (hq z) (hP.2.2.2.2.2.2.2.1 z i)).le
    have ht := ((hT z).2.2 i).1
    have he := (hT z).1
    split_ifs with hc
    · have h1 := le_etaBar_of_cash hP hC hX (hT z) hpos
      have hk := (rates hP i).1
      simp only [sval]
      nlinarith [ht.2.1]
    · have h0z := zero_of_covered hP hC hX (hT z) hpos (not_lt.1 hc)
      simp [sval, h0z]

theorem reservePremium : ReservePremium := by
  intro ι Z _ _ P X η0 η1 t0 t1 i hT prem
  have h2 : prem = P.beta * ∑ z, P.q z * (P.g z i * sval η1 t1 z i - η1 z * (1 + t0 i)) := by
    simp only [prem, Sinc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  refine ⟨by simp only [prem, etaHat]; ring, h2, fun hsold ht0 => ?_⟩
  rw [h2]
  have hs : ∀ z, sval η1 t1 z i = η1 z - (1 + η1 z) * P.km i := fun z =>
    (Novel.M7TwoReviewsBindingBudgetProof.readings ι Z P X η1 t1 hT z i).2.2.1 (hsold z)
  simp only [hs, ht0, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun z _ => by ring

theorem growth : Growth := by
  refine ⟨fun mu0 c m k e hc h1 h2 => ⟨?_, ?_⟩, fun n km gmin g hn hkm hg hgg => ?_⟩
  · -- near `e` the need is affine in the revision
    have hev : ∀ᶠ ε in 𝓝 e, 0 < mu0 + ε - k ∧ m < (mu0 + ε - k) / c := by
      have hcont : Continuous fun ε : ℝ => mu0 + ε - k := by fun_prop
      have hcont2 : Continuous fun ε : ℝ => (mu0 + ε - k) / c := by fun_prop
      exact (hcont.continuousAt.eventually (lt_mem_nhds h1)).and
        (hcont2.continuousAt.eventually (lt_mem_nhds h2))
    have hd : HasDerivAt (fun ε => (1 + k) * ((mu0 + ε - k) / c - m)) ((1 + k) / c) e := by
      have := ((((hasDerivAt_id e).const_add mu0).sub_const k).div_const c).sub_const m
      exact (this.const_mul (1 + k)).congr_deriv (by ring)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hev] with ε hε
    rw [max_eq_left hε.1.le, max_eq_left (by linarith [hε.2])]
  · have hev : ∀ᶠ κ in 𝓝 k, 0 < mu0 + e - κ ∧ m < (mu0 + e - κ) / c := by
      have hcont : Continuous fun κ : ℝ => mu0 + e - κ := by fun_prop
      have hcont2 : Continuous fun κ : ℝ => (mu0 + e - κ) / c := by fun_prop
      exact (hcont.continuousAt.eventually (lt_mem_nhds h1)).and
        (hcont2.continuousAt.eventually (lt_mem_nhds h2))
    have hd : HasDerivAt (fun κ => (1 + κ) * ((mu0 + e - κ) / c - m))
        (((mu0 + e - k) / c - m) - (1 + k) / c) k := by
      have ha := (hasDerivAt_id k).const_add 1
      have hb := ((((hasDerivAt_id k).const_sub (mu0 + e)).div_const c).sub_const m)
      exact (ha.mul hb).congr_deriv (by simp only [id]; ring)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hev] with κ hκ
    rw [max_eq_left hκ.1.le, max_eq_left (by linarith [hκ.2])]
  · have h1 : 0 < 1 - km := by linarith
    have hd : 0 < (1 - km) * gmin := mul_pos h1 hg
    have hq : 0 ≤ n / ((1 - km) * gmin) := div_nonneg hn hd.le
    have : (1 - km) * gmin * (n / ((1 - km) * gmin)) = n := by field_simp
    have hle : (1 - km) * gmin ≤ (1 - km) * g := mul_le_mul_of_nonneg_left hgg h1.le
    nlinarith

theorem cashMax : CashMax := by
  intro ι Z _ _ P hP hC X hX hex hall
  obtain ⟨η1, t1, hT⟩ := hex
  have hstrict : 0 < h0 P X.1 → h0 P X.1 < NN P X.1 := by
    intro hpos
    by_contra hle
    push Not at hle
    obtain ⟨z, hz⟩ := hall η1 t1 hT
    have := (noReserve ι Z P hP hC X hX 0 η1 t1 hT hpos hle).1 z
    linarith
  refine ⟨?_, hstrict⟩
  rcases lt_or_ge 0 (h0 P X.1) with hpos | hle
  · exact (hstrict hpos).le
  · exact hle.trans (Real.iSup_nonneg fun z => need_nonneg hP z X.1)

theorem certificate : Certificate := by
  intro ι Z _ _ P hP hC X hX η0 t0 t1 hT hR hpos hN
  refine ⟨Novel.M7TwoReviewsBindingBudgetProof.sufficient ι Z P hP X hX
    ⟨η0, fun _ => 0, t0, t1, hT, hR⟩, fun η1 t1' hT' => ?_⟩
  exact (noReserve ι Z P hP hC X hX 0 η1 t1' hT' hpos hN).1

theorem thresholdError : ThresholdError := by
  intro e0 eh B kp km h1 h2 hkp hkm
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem costShift : CostShift := by
  intro ι Z _ _ P hP xf xm E tf tm t1 hmove hSE hm hf
  have hγ : 0 < P.gamma := hP.1
  have hc : 0 < P.gamma * P.S0 E E := mul_pos hγ hSE
  have hg := g0_move P hmove E
  have hΔ : xf E - xm E = (Sinc P (fun _ => 0) t1 E - (tf - tm)) / (P.gamma * P.S0 E E) := by
    rw [eq_div_iff hc.ne']
    rw [hg, hm] at hf
    linarith
  refine ⟨hΔ, fun ht1 htf1 htf2 htm1 htm2 => ?_, by rw [hm]; ring⟩
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hgz : ∀ z, 0 < P.g z E := fun z => hP.2.2.2.2.2.2.2.1 z E
  have hβ : 0 < P.beta := hP.2.1
  have hS : |Sinc P (fun _ => 0) t1 E| ≤ P.beta * max (P.kp E) (P.km E) * ∑ z, P.q z * P.g z E := by
    unfold Sinc sval
    simp only [zero_add, add_zero, one_mul]
    rw [abs_mul, abs_of_pos hβ, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [abs_mul, abs_of_pos (mul_pos (hq z) (hgz z))]
    have : |t1 z E| ≤ max (P.kp E) (P.km E) :=
      abs_le.2 ⟨by linarith [(ht1 z).1, le_max_right (P.kp E) (P.km E)],
        (ht1 z).2.trans (le_max_left _ _)⟩
    nlinarith [mul_pos (hq z) (hgz z)]
  have hd : |tf - tm| ≤ P.kp E + P.km E := abs_le.2 ⟨by linarith, by linarith⟩
  rw [hΔ, abs_div, abs_of_pos hc]
  refine div_le_div_of_nonneg_right ?_ hc.le
  calc |Sinc P (fun _ => 0) t1 E - (tf - tm)| ≤ |Sinc P (fun _ => 0) t1 E| + |tf - tm| := abs_sub _ _
    _ ≤ _ := by linarith

theorem proof : Standalone.M8ReserveRule.statement :=
  ⟨noReserve, revisionMax, needBound, budgetChannel, reservePremium, growth, cashMax, certificate,
    thresholdError, costShift⟩

end

end Novel.M8ReserveRuleProof

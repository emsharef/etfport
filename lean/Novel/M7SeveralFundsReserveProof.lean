import Standalone.M7SeveralFundsReserve
import Novel.M7TwoReviewsBoundsProof

/-!
# Claim 113: proof

1b is the factor identity for the marginal, then a one-variable case analysis turning a fund's line
into claim 110's clip. 2a extends claim 046's state-by-state argument with the ETF's sale. A positive
multiplier with `need ≤ liq` forces nothing traded, so the ETF sits at or below its clipped sale
threshold and `liq` is today's cash, and claim 046's covered case applies. The rest is algebra.
-/

namespace Novel.M7SeveralFundsReserveProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds
  Standalone.M7SeveralFundsReserve Novel.M7TwoReviewsBoundsProof

noncomputable section

variable {ι Z : Type} [Fintype ι] [DecidableEq ι]

/-! ### Part 1b -/

theorem fundMarginal : FundMarginal := by
  intro ι Z _ _ _ P E b s v hF x i
  obtain ⟨hbE, hS⟩ := hF
  have hsum : ∑ j, P.S0 i j * x j = b i * s * ∑ j, b j * x j + v i * x i := by
    simp only [hS, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [g0, marg, hsum, alt, rw, mx]
  field_simp
  ring

/-- A fund's line in its box, with a trade-sign slope, is claim 110's clip. -/
lemma line_clip {L η c kp km xbar xm a t : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (_hkp : 0 ≤ kp)
    (_hkm : 0 ≤ km) (ha0 : 0 ≤ a) (ha1 : a ≤ xbar) (hxm0 : 0 ≤ xm) (hxm1 : xm ≤ xbar)
    (ht : Slope kp km (a - xm) t) (hb : BoxSign xbar a (L - c * a - η - (1 + η) * t)) :
    a = clip L η c kp km xbar xm := by
  obtain ⟨t1, t2, tp, tm⟩ := ht
  have h1η : 0 ≤ 1 + η := by linarith
  set lo := (L - η - (1 + η) * kp) / c with hlo
  set hi := (L - η + (1 + η) * km) / c with hhi
  have elo : lo * c = L - η - (1 + η) * kp := div_mul_cancel₀ _ hc.ne'
  have ehi : hi * c = L - η + (1 + η) * km := div_mul_cancel₀ _ hc.ne'
  -- the line's value between the band's ends
  have hlo_le : lo * c ≤ L - η - (1 + η) * t := by rw [elo]; nlinarith
  have hhi_ge : L - η - (1 + η) * t ≤ hi * c := by rw [ehi]; nlinarith
  have lohi : lo ≤ hi := by nlinarith
  unfold clip
  rw [← hlo, ← hhi]
  rcases lt_or_eq_of_le ha0 with hpos | hzero
  · rcases lt_or_eq_of_le ha1 with hlt | heq
    · -- strictly inside: the line is an equality
      have hR : L - c * a - η - (1 + η) * t = 0 := le_antisymm (hb.1 hlt) (hb.2 hpos)
      have hlo_a : lo ≤ a := by nlinarith
      have ha_hi : a ≤ hi := by nlinarith
      have hy : max lo (min hi xm) = a := by
        rcases lt_trichotomy xm a with hx | hx | hx
        · have := tp (by linarith)
          rw [this] at hR
          have : lo = a := by nlinarith
          rw [min_eq_right (by linarith), max_eq_left (by linarith)]
          exact this
        · rw [hx, min_eq_right ha_hi, max_eq_right hlo_a]
        · have := tm (by linarith)
          rw [this] at hR
          have : hi = a := by nlinarith
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          exact this
      rw [hy, min_eq_right hlt.le, max_eq_right hpos.le]
    · -- at the cap
      have hR := hb.2 hpos
      have hhi_x : xbar ≤ hi := by nlinarith
      have hy : xbar ≤ max lo (min hi xm) := by
        rcases lt_or_eq_of_le hxm1 with hx | hx
        · have := tp (by linarith)
          rw [this] at hR
          have : xbar ≤ lo := by nlinarith
          exact le_max_of_le_left this
        · rw [hx]
          exact le_max_of_le_right (le_min hhi_x le_rfl)
      rw [min_eq_left hy, max_eq_right (by linarith)]
      exact heq
  · -- at zero
    rw [← hzero]
    rcases lt_or_eq_of_le (hzero ▸ ha1 : (0 : ℝ) ≤ xbar) with hx | hx
    · have hR := hb.1 (by rw [← hzero]; exact hx)
      rw [← hzero] at hR
      have hlo0 : lo ≤ 0 := by nlinarith
      have hmin : min hi xm ≤ 0 := by
        rcases lt_or_eq_of_le hxm0 with hm | hm
        · have := tm (by rw [← hzero]; linarith)
          rw [this] at hR
          exact min_le_of_left_le (by nlinarith)
        · rw [← hm]
          exact min_le_right _ _
      have : min xbar (max lo (min hi xm)) ≤ 0 := min_le_of_right_le (max_le hlo0 hmin)
      exact (max_eq_left this).symm
    · rw [← hx]
      exact (max_eq_left (min_le_left _ _)).symm

theorem rootClip : RootClip := by
  intro ι Z _ _ _ P E b s v hP hF X hX η0 η1 t0 t1 hT hR i hv
  obtain ⟨hη0, _, hl⟩ := hR
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hηh : 0 ≤ etaHat P η0 η1 := by
    unfold etaHat
    have : 0 ≤ ∑ z, P.q z * η1 z := Finset.sum_nonneg fun z _ => mul_nonneg (hq z).le (hT z).1
    nlinarith [hP.2.1]
  have hr := hP.2.2.2.2.2.2.2.2 i
  have hc : 0 < P.gamma * v i := mul_pos hP.1 hv
  have hm := fundMarginal ι Z P E b s v hF X.1 i
  refine line_clip hc hηh hr.1 hr.2.1 (hX.1 i).1 (hX.1 i).2 hr.2.2.2.1 hr.2.2.2.2 (hl i).1 ?_
  have := (hl i).2
  rw [hm] at this
  convert this using 1
  ring

/-! ### Part 2 -/

section Liq

variable {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ} {E : ι}

/-- A positive multiplier with `need ≤ liq` forces nothing traded, today's cash spent, and the state
covered by cash alone. -/
lemma liq_facts (hP : Hyp P) (hC : Cov P) (hX : X ∈ Feas P) (h : LinesAt P X z e t)
    (hle : need P z X.1 ≤ liq P z E X.1) (he : 0 < e) :
    (∀ j, X.2 z j = carry P z X.1 j) ∧ h0 P X.1 = 0 ∧ need P z X.1 ≤ h0 P X.1 := by
  have hx : ∀ j, 0 ≤ X.2 z j := fun j => ((hX.2.1 z) j).1
  have hh1 : h1 P X.1 X.2 z = 0 := (mul_eq_zero.1 h.2.1).resolve_left he.ne'
  have hγS : ∀ j, 0 < P.gamma * P.S1 z j j := fun j => mul_pos hP.1 (hC.2 z j)
  set M := max (xhatS P z E) 0 with hM
  -- a purchase stops strictly short of the solo target
  have hxhat : ∀ j, carry P z X.1 j < X.2 z j → X.2 z j < xhat P z j := by
    intro j hb
    have h1 := line_bought hP hX h j hb
    have h2 := g1_le (z := z) hP hC hx j
    have hk := (rates hP j).1
    have h3 : P.gamma * (P.S1 z j j * X.2 z j) < max (P.mu1 z j - P.kp j) 0 := by
      nlinarith [le_max_left (P.mu1 z j - P.kp j) 0, mul_pos he (by linarith : (0 : ℝ) < 1 + P.kp j)]
    unfold xhat
    rw [lt_div_iff₀ (hγS j)]
    linarith
  -- the ETF ends at or below its clipped sale threshold
  have hEle : X.2 z E ≤ M := by
    rcases lt_or_eq_of_le (hx E) with hpos | hzero
    · have h1 := line_lower h E hpos
      have h2 := g1_le (z := z) hP hC hx E
      have hk := rates hP E
      have h3 : P.gamma * (P.S1 z E E * X.2 z E) ≤ P.mu1 z E + P.km E := by nlinarith
      have : X.2 z E ≤ xhatS P z E := by
        unfold xhatS
        rw [le_div_iff₀ (hγS E)]
        linarith
      exact this.trans (le_max_left _ _)
    · rw [← hzero]
      exact le_max_right _ _
  set D := fun j => (X.2 z j - carry P z X.1 j) + pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j)
  set sale := (1 - P.km E) * max (P.g z E * X.1 E - M) 0
  have hkE := rates hP E
  have hcarry : carry P z X.1 E = P.g z E * X.1 E := rfl
  -- every trade's cash is at most its part of the need, the ETF's less its counted proceeds
  have hterm : ∀ j, D j ≤ needI P z X.1 j - if j = E then sale else 0 := by
    intro j
    have htl := term_le hP j (X.2 z j - carry P z X.1 j)
    have hk : 0 ≤ 1 + P.kp j := by linarith [(rates hP j).1]
    have hmono : (1 + P.kp j) * max (X.2 z j - carry P z X.1 j) 0 ≤ needI P z X.1 j := by
      unfold needI
      refine mul_le_mul_of_nonneg_left ?_ hk
      by_cases hb : carry P z X.1 j < X.2 z j
      · exact max_le_max (by linarith [hxhat j hb]) le_rfl
      · rw [max_eq_right (by linarith [not_lt.1 hb])]
        exact le_max_right _ _
    by_cases hjE : j = E
    · subst hjE
      simp only [ite_true]
      by_cases hs : M < carry P z X.1 j
      · -- the ETF is sold at least down to `M`
        have hsold : X.2 z j < carry P z X.1 j := lt_of_le_of_lt hEle hs
        have hd : D j = (X.2 z j - carry P z X.1 j) * (1 - P.km j) := by
          simp only [D, pc]
          rw [max_eq_right (by linarith), max_eq_left (by linarith)]
          ring
        have hsale : sale = (1 - P.km j) * (carry P z X.1 j - M) := by
          simp only [sale]
          rw [← hcarry, max_eq_left (by linarith)]
        have hn : 0 ≤ needI P z X.1 j := mul_nonneg hk (le_max_right _ _)
        rw [hd, hsale]
        nlinarith
      · have hsale : sale = 0 := by
          simp only [sale]
          rw [← hcarry, max_eq_right (by linarith [not_lt.1 hs]), mul_zero]
        rw [hsale, sub_zero]
        exact htl.trans hmono
    · simp only [hjE, ite_false, sub_zero]
      exact htl.trans hmono
  have hsum : ∑ j, D j ≤ need P z X.1 - sale := by
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ E (fun _ => sale)] at this
    simpa [need, needI] using this
  have hliq : liq P z E X.1 = h0 P X.1 + sale := rfl
  have e1 := h1_eq P X z
  -- no purchase: one would leave cash
  have hnb : ∀ j, ¬ carry P z X.1 j < X.2 z j := by
    intro j0 hb
    have hstrict : D j0 < needI P z X.1 j0 - if j0 = E then sale else 0 := by
      have htl := term_le hP j0 (X.2 z j0 - carry P z X.1 j0)
      have hx' := hxhat j0 hb
      have hk : 0 < 1 + P.kp j0 := by linarith [(rates hP j0).1]
      rw [max_eq_left (by linarith)] at htl
      have hlt : D j0 < needI P z X.1 j0 := by
        unfold needI
        rw [max_eq_left (by linarith)]
        nlinarith
      by_cases hjE : j0 = E
      · subst hjE
        have hsale : sale = 0 := by
          simp only [sale]
          rw [← hcarry, max_eq_right (by linarith), mul_zero]
        simpa [hsale] using hlt
      · simpa [hjE] using hlt
    have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
      ⟨j0, Finset.mem_univ _, hstrict⟩
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ E (fun _ => sale)] at hlt
    simp only [Finset.mem_univ, ite_true] at hlt
    have : ∑ j, D j < need P z X.1 - sale := by simpa [need, needI] using hlt
    linarith
  have hnt := nothing_traded hP hX h he hnb
  have hh0 : h0 P X.1 = 0 := by
    simp only [hnt, sub_self, pc, max_self, neg_zero, mul_zero, add_zero, Finset.sum_const_zero,
      sub_zero] at e1
    linarith
  have hsale0 : sale = 0 := by
    simp only [sale]
    rw [← hcarry, ← hnt E, max_eq_right (by linarith), mul_zero]
  exact ⟨hnt, hh0, by linarith⟩

end Liq

theorem liqTest : LiqTest := by
  intro ι Z _ _ _ P E hP hC X hX z e t h hle
  rcases h.1.eq_or_lt with he0 | he
  · exact ⟨t, he0 ▸ h⟩
  obtain ⟨_, _, hcov⟩ := liq_facts hP hC hX h hle he
  exact slackWhenCovered ι Z P hP hC X hX z e t h hcov

theorem noReserveLiq : NoReserveLiq := by
  intro ι Z _ _ _ P E hP hC X hX η0 η1 t1 hT hall
  have hsel := fun z => liqTest ι Z P E hP hC X hX z (η1 z) (t1 z) (hT z) (hall z)
  choose t' ht' using hsel
  have hsz : Tomorrow P X (fun _ => 0) t' := ht'
  refine ⟨⟨t', hsz, by simp [etaHat], fun i => ?_⟩, fun hpos => ?_⟩
  · have hb := brackets ι Z P hP X (fun _ => 0) t' hsz i
    simp only [zero_add, add_zero, one_mul] at hb
    exact ⟨hb.2.1, hb.1⟩
  · have hz : ∀ z, η1 z = 0 := fun z => by
      rcases (hT z).1.eq_or_lt with h | h
      · exact h.symm
      · exact absurd (liq_facts hP hC hX (hT z) (hall z) h).2.1 hpos.ne'
    refine ⟨hz, by simp [etaHat, hz], fun i => ?_⟩
    have hb := brackets ι Z P hP X η1 t1 hT i
    simp only [hz, zero_add, add_zero, one_mul] at hb
    exact ⟨hb.2.1, hb.1⟩

theorem pooling : Pooling := by
  intro ι Z _ _ _ P x0
  have hneed : ∀ z, need P z x0 = ∑ i, needI P z x0 i := fun z => rfl
  have bdd : ∀ i, BddAbove (Set.range fun z => needI P z x0 i) :=
    fun i => (Set.finite_range _).bddAbove
  refine ⟨?_, fun z0 hz0 => ?_⟩
  · rcases isEmpty_or_nonempty Z with hZ | hZ
    · simp
    · exact ciSup_le fun z => by
        rw [hneed]
        exact Finset.sum_le_sum fun i _ => le_ciSup (bdd i) z
  · have : Nonempty Z := ⟨z0⟩
    have hsup : ∀ i, (⨆ z, needI P z x0 i) = needI P z0 x0 i := fun i =>
      le_antisymm (ciSup_le fun z => hz0 i z) (le_ciSup (bdd i) z0)
    have hN : (⨆ z, need P z x0) = need P z0 x0 := by
      refine le_antisymm (ciSup_le fun z => ?_) (le_ciSup (f := fun z => need P z x0)
        (Set.finite_range _).bddAbove z0)
      rw [hneed, hneed]
      exact Finset.sum_le_sum fun i _ => hz0 i z
    rw [hN, hneed]
    exact Finset.sum_congr rfl fun i _ => (hsup i).symm

/-! ### Parts 3b and 4 -/

theorem correctedSign : CorrectedSign := by
  intro al r S mdyn mmy ehat emy κ c adyn amy hc h1 h2
  rw [eq_div_iff hc.ne']
  linarith

theorem wealth : Wealth := by
  intro ι Z _ _ _ P E xd xy
  have hs : ∀ f : ι → ℝ, ∑ i, f i = f E + ∑ i ∈ Finset.univ.erase E, f i := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ E)).symm
  simp only [h0]
  rw [hs fun i => xd i - P.xm i, hs fun i => xy i - P.xm i]
  have : ∑ i ∈ Finset.univ.erase E, (xy i - xd i) =
      ∑ i ∈ Finset.univ.erase E, (xy i - P.xm i) - ∑ i ∈ Finset.univ.erase E, (xd i - P.xm i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

theorem clipLipschitz : ClipLipschitz := by
  intro L L' η η' c kp km xbar xm hc hkp hkm hkm1
  unfold clip
  set lo := (L - η - (1 + η) * kp) / c
  set lo' := (L' - η' - (1 + η') * kp) / c
  set hi := (L - η + (1 + η) * km) / c
  set hi' := (L' - η' + (1 + η') * km) / c
  set B := (|L - L'| + |η - η'| * (1 + kp)) / c
  have hlo : |lo - lo'| ≤ B := by
    have e : lo - lo' = ((L - L') - (η - η') * (1 + kp)) / c := by
      simp only [lo, lo']
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hc]
    refine div_le_div_of_nonneg_right ?_ hc.le
    calc |(L - L') - (η - η') * (1 + kp)| ≤ |L - L'| + |(η - η') * (1 + kp)| := abs_sub _ _
      _ = |L - L'| + |η - η'| * (1 + kp) := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + kp)]
  have hhi : |hi - hi'| ≤ B := by
    have e : hi - hi' = ((L - L') - (η - η') * (1 - km)) / c := by
      simp only [hi, hi']
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hc]
    refine div_le_div_of_nonneg_right ?_ hc.le
    calc |(L - L') - (η - η') * (1 - km)| ≤ |L - L'| + |(η - η') * (1 - km)| := abs_sub _ _
      _ = |L - L'| + |η - η'| * (1 - km) := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - km)]
      _ ≤ |L - L'| + |η - η'| * (1 + kp) := by
          have := abs_nonneg (η - η')
          nlinarith
  have h1 : |min hi xm - min hi' xm| ≤ B :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le hhi (by simp; positivity))
  have h2 : |max lo (min hi xm) - max lo' (min hi' xm)| ≤ B :=
    (abs_max_sub_max_le_max _ _ _ _).trans (max_le hlo h1)
  have h3 : |min xbar (max lo (min hi xm)) - min xbar (max lo' (min hi' xm))| ≤ B :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp; positivity) h2)
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) h3)

theorem clipIsXi : ClipIsXi := fun _ _ _ _ _ => rfl

theorem resR : ResR := by
  intro pd pm hd hm km gmin
  ring

theorem proof : Standalone.M7SeveralFundsReserve.statement :=
  ⟨clipIsXi, fundMarginal, rootClip, liqTest, noReserveLiq, pooling, correctedSign, wealth,
    clipLipschitz, resR⟩

end

end Novel.M7SeveralFundsReserveProof

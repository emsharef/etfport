import Standalone.M7TwoReviewsBounds
import Novel.M7TwoReviewsBindingBudgetProof
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Claim 045: proof

Case analysis on one state's lines (claim 044's), with `g_{1,i} ≤ μ_{1,i} - γ Σ_{1,ii} x_i` from the
nonnegative covariances. A state that buys pins its multiplier below `η̄`. A state that sells without
buying has cash left, so its multiplier is zero. A state that trades nothing admits the clamped
slopes at any multiplier between the lines' bounds.
-/

namespace Novel.M7TwoReviewsBoundsProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds Set Filter Topology

noncomputable section

variable {ι Z : Type} [Fintype ι]

/-! ### One state's lines -/

section State

variable {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ}

lemma rates (hP : Hyp P) (i : ι) : 0 ≤ P.kp i ∧ 0 ≤ P.km i ∧ P.km i < 1 :=
  ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1, (hP.2.2.2.2.2.2.2.2 i).2.2.1⟩

/-- With nonnegative covariances and a long-only holding, `g_{1,i} ≤ μ_{1,i} - γ Σ_{1,ii} x_i`. -/
lemma g1_le (hP : Hyp P) (hC : Cov P) {x : ι → ℝ} (hx : ∀ j, 0 ≤ x j) (i : ι) :
    g1 P z x i ≤ P.mu1 z i - P.gamma * (P.S1 z i i * x i) := by
  classical
  have hs := Finset.add_sum_erase Finset.univ (fun j => P.S1 z i j * x j) (Finset.mem_univ i)
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i, P.S1 z i j * x j :=
    Finset.sum_nonneg fun j hj => mul_nonneg (hC.1 z i j (Finset.ne_of_mem_erase hj).symm) (hx j)
  have hγ : 0 ≤ P.gamma := hP.1.le
  simp only [g1, marg]
  nlinarith

lemma carry_nonneg (hP : Hyp P) (hX : X ∈ Feas P) (i : ι) : 0 ≤ carry P z X.1 i :=
  mul_nonneg (hP.2.2.2.2.2.2.2.1 z i).le (hX.1 i).1

lemma line_upper (h : LinesAt P X z e t) (i : ι) (hx : X.2 z i < P.xbar i) :
    g1 P z (X.2 z) i ≤ e + (1 + e) * P.kp i := by
  obtain ⟨he, _, hl⟩ := h
  have hb := (hl i).2.1 hx
  have ht := (hl i).1.2.1
  nlinarith

lemma line_lower (h : LinesAt P X z e t) (i : ι) (hx : 0 < X.2 z i) :
    e - (1 + e) * P.km i ≤ g1 P z (X.2 z) i := by
  obtain ⟨he, _, hl⟩ := h
  have hb := (hl i).2.2 hx
  have ht := (hl i).1.1
  nlinarith

lemma line_bought (hP : Hyp P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (i : ι)
    (hb : carry P z X.1 i < X.2 z i) : e + (1 + e) * P.kp i ≤ g1 P z (X.2 z) i := by
  obtain ⟨he, _, hl⟩ := h
  have hpos : 0 < X.2 z i := lt_of_le_of_lt (carry_nonneg hP hX i) hb
  have hR := (hl i).2.2 hpos
  have ht := (hl i).1.2.2.1 (by linarith)
  rw [ht] at hR
  linarith

/-- The cash after tomorrow's trade, term by term. -/
lemma h1_eq (P : Two ι Z) (X : (ι → ℝ) × (Z → ι → ℝ)) (z : Z) :
    h1 P X.1 X.2 z = h0 P X.1 - ∑ i, ((X.2 z i - carry P z X.1 i) +
      pc (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i)) := by
  simp only [h1, cost, Pi.sub_apply, Finset.sum_add_distrib]
  ring

lemma term_le (hP : Hyp P) (i : ι) (u : ℝ) : u + pc (P.kp i) (P.km i) u ≤ (1 + P.kp i) * max u 0 := by
  obtain ⟨hkp, hkm, hk1⟩ := rates hP i
  simp only [pc]
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu, max_eq_left (by linarith : 0 ≤ -u)]
    nlinarith
  · rw [max_eq_left hu, max_eq_right (by linarith : -u ≤ 0)]
    ring_nf
    linarith

lemma term_neg (hP : Hyp P) (i : ι) {u : ℝ} (hu : u < 0) : u + pc (P.kp i) (P.km i) u < 0 := by
  obtain ⟨hkp, hkm, hk1⟩ := rates hP i
  simp only [pc]
  rw [max_eq_right hu.le, max_eq_left (by linarith : 0 ≤ -u)]
  nlinarith

/-- With a positive multiplier and nothing bought, nothing is traded: a sale would leave cash. -/
lemma nothing_traded (hP : Hyp P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (he : 0 < e)
    (hnb : ∀ i, ¬ carry P z X.1 i < X.2 z i) : ∀ i, X.2 z i = carry P z X.1 i := by
  have hh1 : h1 P X.1 X.2 z = 0 := (mul_eq_zero.1 h.2.1).resolve_left he.ne'
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hlt : X.2 z i - carry P z X.1 i < 0 := by
    have := not_lt.1 (hnb i)
    exact sub_neg.2 (lt_of_le_of_ne this hi)
  have hsum : ∑ j, ((X.2 z j - carry P z X.1 j) + pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j)) < 0 := by
    apply Finset.sum_neg'
    · intro j _
      have hj := not_lt.1 (hnb j)
      have := term_le hP j (X.2 z j - carry P z X.1 j)
      rw [max_eq_right (by linarith)] at this
      linarith
    · exact ⟨i, Finset.mem_univ _, term_neg hP i hlt⟩
  have := h1_eq P X z
  have h0nn := hX.2.2.1
  linarith

/-- With nothing traded, any multiplier within the lines' bounds is admissible with the clamped
slopes. -/
lemma clamp_lines (hP : Hyp P) (hnt : ∀ i, X.2 z i = carry P z X.1 i) {e' : ℝ} (he' : 0 ≤ e')
    (hc : e' * h1 P X.1 X.2 z = 0)
    (hb : ∀ i, (X.2 z i < P.xbar i → g1 P z (X.2 z) i ≤ e' + (1 + e') * P.kp i) ∧
      (0 < X.2 z i → e' - (1 + e') * P.km i ≤ g1 P z (X.2 z) i)) :
    ∃ t', LinesAt P X z e' t' := by
  have h1e : 0 < 1 + e' := by linarith
  let u : ι → ℝ := fun i => (g1 P z (X.2 z) i - e') / (1 + e')
  have hu : ∀ i, (1 + e') * u i = g1 P z (X.2 z) i - e' := fun i => by
    simp only [u]
    field_simp
  refine ⟨fun i => max (-P.km i) (min (P.kp i) (u i)), he', hc, fun i => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨hkp, hkm, _⟩ := rates hP i
    rw [hnt i, sub_self]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _), fun h => absurd h (lt_irrefl _),
      fun h => absurd h (lt_irrefl _)⟩
  · intro hx
    have hup : u i ≤ P.kp i := by
      have := (hb i).1 hx
      have := hu i
      nlinarith
    have : u i ≤ max (-P.km i) (min (P.kp i) (u i)) := le_max_of_le_right (le_min hup le_rfl)
    have := hu i
    nlinarith
  · intro hx
    have hlo : -P.km i ≤ u i := by
      have := (hb i).2 hx
      have := hu i
      nlinarith
    have : max (-P.km i) (min (P.kp i) (u i)) ≤ u i := max_le hlo (min_le_right _ _)
    have := hu i
    nlinarith

lemma etaBar_nonneg (hP : Hyp P) (z : Z) : 0 ≤ etaBar P z :=
  Real.iSup_nonneg fun i => div_nonneg (le_max_right _ _) (by linarith [(rates hP i).1])

lemma le_etaBar (P : Two ι Z) (z : Z) (i : ι) :
    max (P.mu1 z i - P.kp i) 0 / (1 + P.kp i) ≤ etaBar P z :=
  le_ciSup (f := fun i => max (P.mu1 z i - P.kp i) 0 / (1 + P.kp i)) (Set.finite_range _).bddAbove i

/-- `μ_{1,i} ≤ η̄ + (1 + η̄) κ⁺_i`. -/
lemma mu_le (hP : Hyp P) (z : Z) (i : ι) : P.mu1 z i ≤ etaBar P z + (1 + etaBar P z) * P.kp i := by
  have h1 := le_etaBar P z i
  have hk : 0 < 1 + P.kp i := by linarith [(rates hP i).1]
  rw [div_le_iff₀ hk] at h1
  have := le_max_left (P.mu1 z i - P.kp i) 0
  nlinarith [etaBar_nonneg hP z]

end State

/-! ### Part 1 -/

/-- A multiplier above `η̄` needs a state that trades nothing with all cash spent. -/
lemma big_mult {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ} (hP : Hyp P)
    (hC : Cov P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (hle : etaBar P z < e) :
    (∀ i, X.2 z i = carry P z X.1 i) ∧ h1 P X.1 X.2 z = 0 := by
  have he : 0 < e := lt_of_le_of_lt (etaBar_nonneg hP z) hle
  have hx : ∀ j, 0 ≤ X.2 z j := fun j => ((hX.2.1 z) j).1
  -- a purchase pins the multiplier below `η̄`
  have hnb : ∀ i, ¬ carry P z X.1 i < X.2 z i := by
    intro i hb
    have h1 := line_bought hP hX h i hb
    have h2 := g1_le (z := z) hP hC hx i
    have h3 : 0 ≤ P.gamma * (P.S1 z i i * X.2 z i) :=
      mul_nonneg hP.1.le (mul_nonneg (hC.2 z i).le (hx i))
    have h4 := mu_le hP z i
    have hk := (rates hP i).1
    nlinarith
  exact ⟨nothing_traded hP hX h he hnb, (mul_eq_zero.1 h.2.1).resolve_left he.ne'⟩

theorem cashPriceBound : CashPriceBound := by
  intro ι Z _ _ P hP hC X hX z e t h
  by_cases hle : e ≤ etaBar P z
  · exact ⟨e, t, h, hle, le_rfl⟩
  push Not at hle
  have hx : ∀ j, 0 ≤ X.2 z j := fun j => ((hX.2.1 z) j).1
  obtain ⟨hnt, hh1⟩ := big_mult hP hC hX h hle
  obtain ⟨t', ht'⟩ := clamp_lines hP hnt (etaBar_nonneg hP z) (by rw [hh1, mul_zero]) fun i =>
    ⟨fun _ => by
      have h2 := g1_le (z := z) hP hC hx i
      have h3 : 0 ≤ P.gamma * (P.S1 z i i * X.2 z i) :=
        mul_nonneg hP.1.le (mul_nonneg (hC.2 z i).le (hx i))
      have := mu_le hP z i
      linarith,
    fun hpos => by
      have := line_lower h i hpos
      have hk := rates hP i
      nlinarith⟩
  exact ⟨etaBar P z, t', ht', le_rfl, hle.le⟩

/-- A positive multiplier in a covered state needs nothing traded and all of today's cash spent. -/
lemma covered_pos {P : Two ι Z} {X : (ι → ℝ) × (Z → ι → ℝ)} {z : Z} {e : ℝ} {t : ι → ℝ} (hP : Hyp P)
    (hC : Cov P) (hX : X ∈ Feas P) (h : LinesAt P X z e t) (hneed : need P z X.1 ≤ h0 P X.1)
    (he : 0 < e) : (∀ i, X.2 z i = carry P z X.1 i) ∧ h0 P X.1 = 0 := by
  have hx : ∀ j, 0 ≤ X.2 z j := fun j => ((hX.2.1 z) j).1
  have hh1 : h1 P X.1 X.2 z = 0 := (mul_eq_zero.1 h.2.1).resolve_left he.ne'
  have hγS : ∀ j, 0 < P.gamma * P.S1 z j j := fun j => mul_pos hP.1 (hC.2 z j)
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
  have hterm : ∀ j, (X.2 z j - carry P z X.1 j) + pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j) ≤
      (1 + P.kp j) * max (xhat P z j - carry P z X.1 j) 0 := by
    intro j
    have h1 := term_le hP j (X.2 z j - carry P z X.1 j)
    have hk : 0 ≤ 1 + P.kp j := by linarith [(rates hP j).1]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hk)
    by_cases hb : carry P z X.1 j < X.2 z j
    · have := hxhat j hb
      exact max_le_max (by linarith) le_rfl
    · rw [max_eq_right (by linarith [not_lt.1 hb])]
      exact le_max_right _ _
  have hnb : ∀ j, ¬ carry P z X.1 j < X.2 z j := by
    intro j hb
    have hstrict : (X.2 z j - carry P z X.1 j) + pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j) <
        (1 + P.kp j) * max (xhat P z j - carry P z X.1 j) 0 := by
      have h1 := term_le hP j (X.2 z j - carry P z X.1 j)
      have hx' := hxhat j hb
      have hk : 0 < 1 + P.kp j := by linarith [(rates hP j).1]
      rw [max_eq_left (by linarith)] at h1
      rw [max_eq_left (by linarith)]
      nlinarith
    have hsum : ∑ j, ((X.2 z j - carry P z X.1 j) + pc (P.kp j) (P.km j) (X.2 z j - carry P z X.1 j)) <
        need P z X.1 :=
      Finset.sum_lt_sum (fun j _ => hterm j) ⟨j, Finset.mem_univ _, hstrict⟩
    have := h1_eq P X z
    linarith
  have hnt := nothing_traded hP hX h he hnb
  have hh0 : h0 P X.1 = 0 := by
    have e1 := h1_eq P X z
    simp only [hnt, sub_self, pc, max_self, neg_zero, mul_zero, add_zero, Finset.sum_const_zero,
      sub_zero] at e1
    linarith
  exact ⟨hnt, hh0⟩

theorem slackWhenCovered : SlackWhenCovered := by
  intro ι Z _ _ P hP hC X hX z e t h hneed
  rcases h.1.eq_or_lt with he0 | he
  · exact ⟨t, he0 ▸ h⟩
  have hx : ∀ j, 0 ≤ X.2 z j := fun j => ((hX.2.1 z) j).1
  have hγS : ∀ j, 0 < P.gamma * P.S1 z j j := fun j => mul_pos hP.1 (hC.2 z j)
  obtain ⟨hnt, hh0⟩ := covered_pos hP hC hX h hneed he
  have hcov : ∀ j, xhat P z j ≤ carry P z X.1 j := by
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (1 + P.kp j) * max (xhat P z j - carry P z X.1 j) 0 :=
      fun j _ => mul_nonneg (by linarith [(rates hP j).1]) (le_max_right _ _)
    have h0' : need P z X.1 = 0 := le_antisymm (hh0 ▸ hneed) (Finset.sum_nonneg hnn)
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0' j (Finset.mem_univ _)
    have hk : 0 < 1 + P.kp j := by linarith [(rates hP j).1]
    have hm : max (xhat P z j - carry P z X.1 j) 0 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have := le_max_left (xhat P z j - carry P z X.1 j) 0
    linarith
  refine clamp_lines hP hnt le_rfl (by rw [zero_mul]) fun j => ⟨fun _ => ?_, fun hpos => ?_⟩
  · have h2 := g1_le (z := z) hP hC hx j
    have hxe : P.gamma * P.S1 z j j * xhat P z j = max (P.mu1 z j - P.kp j) 0 := by
      unfold xhat
      exact mul_div_cancel₀ _ (hγS j).ne'
    have h3 : P.gamma * P.S1 z j j * xhat P z j ≤ P.gamma * P.S1 z j j * X.2 z j := by
      rw [hnt j]
      exact mul_le_mul_of_nonneg_left (hcov j) (hγS j).le
    have := le_max_left (P.mu1 z j - P.kp j) 0
    nlinarith
  · have := line_lower h j hpos
    have hk := rates hP j
    nlinarith

theorem dynamicCashPrice : DynamicCashPrice := by
  intro ι Z _ _ P hP hC X hX η0 η1 t1 hη0 hT
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hβ : 0 < P.beta := hP.2.1
  have J1 : ∀ z, (¬ (∀ i, X.2 z i = carry P z X.1 i) ∨ 0 < h1 P X.1 X.2 z) → η1 z ≤ etaBar P z := by
    intro z hz
    by_contra hgt
    push Not at hgt
    obtain ⟨hnt, hh1⟩ := big_mult hP hC hX (hT z) hgt
    rcases hz with h | h
    · exact h hnt
    · linarith
  have bound : ∀ e : Z → ℝ, (∀ z, 0 ≤ e z) → (∀ z, e z ≤ etaBar P z) →
      η0 ≤ etaHat P η0 e ∧ etaHat P η0 e ≤ η0 + P.beta * ∑ z, P.q z * etaBar P z := by
    intro e he0 hle
    have h1 : 0 ≤ ∑ z, P.q z * e z := Finset.sum_nonneg fun z _ => mul_nonneg (hq z).le (he0 z)
    have h2 := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hle z) (hq z).le
    unfold etaHat
    constructor <;> nlinarith
  refine ⟨J1, fun hall => bound η1 (fun z => (hT z).1) fun z => J1 z (hall z),
    fun hpos hcov => ?_, ?_, fun hcov => ?_⟩
  · have hz : ∀ z, η1 z = 0 := fun z => by
      rcases (hT z).1.eq_or_lt with h | h
      · exact h.symm
      · exact absurd (covered_pos hP hC hX (hT z) (hcov z) h).2 hpos.ne'
    exact ⟨hz, by simp [etaHat, hz]⟩
  · have hA := fun z => cashPriceBound ι Z P hP hC X hX z (η1 z) (t1 z) (hT z)
    choose e' t' hL hbar hle using hA
    exact ⟨e', t', hL, fun z => ⟨hbar z, hle z⟩, bound e' (fun z => (hL z).1) hbar⟩
  · have hB := fun z => slackWhenCovered ι Z P hP hC X hX z (η1 z) (t1 z) (hT z) (hcov z)
    choose t' ht' using hB
    exact ⟨t', ht', by simp [etaHat]⟩

/-! ### Part 2 -/

theorem brackets : Brackets := by
  intro ι Z _ _ P hP X η1 t1 hT i
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hg : ∀ z, 0 < P.g z i := fun z => hP.2.2.2.2.2.2.2.1 z i
  have hβ : 0 < P.beta := hP.2.1
  have hk := rates hP i
  have hs : ∀ z, η1 z - (1 + η1 z) * P.km i ≤ sval η1 t1 z i ∧
      sval η1 t1 z i ≤ η1 z + (1 + η1 z) * P.kp i := fun z => by
    have he := (hT z).1
    have ht := ((hT z).2.2 i).1
    simp only [sval]
    constructor <;> nlinarith [ht.1, ht.2.1]
  have hsl : ∀ z, -P.km i ≤ sval η1 t1 z i := fun z => by
    have := (hs z).1
    have := (hT z).1
    nlinarith
  have hw : ∀ z, 0 ≤ P.q z * P.g z i := fun z => (mul_pos (hq z) (hg z)).le
  intro lo hi
  have hlo : lo = P.beta * (∑ z, P.q z * (η1 z * (P.g z i * (1 - P.km i) - 1 - P.kp i)) -
      P.km i * ∑ z, P.q z * P.g z i) := rfl
  have hhi : hi = P.beta * ((∑ z, P.q z * (η1 z * (P.g z i - 1))) * (1 + P.kp i) +
      P.kp i * ∑ z, P.q z * P.g z i) := rfl
  have b1 : Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * (η1 z + (1 + η1 z) * P.kp i) := by
    unfold Sinc
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hs z).2 (hw z)) hβ.le
  have b2 : -(P.beta * ∑ z, P.q z * P.g z i * P.km i) ≤ Sinc P η1 t1 i := by
    unfold Sinc
    have := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hsl z) (hw z)
    have e : ∑ z, P.q z * P.g z i * -P.km i = -∑ z, P.q z * P.g z i * P.km i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [e] at this
    nlinarith
  have b3 : lo ≤ Resid P η1 t1 i := by
    have key : Resid P η1 t1 i - lo =
        P.beta * ∑ z, P.q z * P.g z i * (sval η1 t1 z i - (η1 z - (1 + η1 z) * P.km i)) := by
      rw [hlo]
      simp only [Resid, Sinc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    have : 0 ≤ P.beta * ∑ z, P.q z * P.g z i * (sval η1 t1 z i - (η1 z - (1 + η1 z) * P.km i)) :=
      mul_nonneg hβ.le (Finset.sum_nonneg fun z _ => mul_nonneg (hw z) (by linarith [(hs z).1]))
    linarith
  have b4 : Resid P η1 t1 i ≤ hi := by
    have key : hi - Resid P η1 t1 i =
        P.beta * ∑ z, P.q z * P.g z i * ((η1 z + (1 + η1 z) * P.kp i) - sval η1 t1 z i) := by
      rw [hhi]
      simp only [Resid, Sinc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    have : 0 ≤ P.beta * ∑ z, P.q z * P.g z i * ((η1 z + (1 + η1 z) * P.kp i) - sval η1 t1 z i) :=
      mul_nonneg hβ.le (Finset.sum_nonneg fun z _ => mul_nonneg (hw z) (by linarith [(hs z).2]))
    linarith
  exact ⟨b1, b2, b3, b4, fun hh => by linarith, fun hh => by linarith⟩

/-! ### Part 3 -/

theorem interiorTrade : InteriorTrade := by
  intro ι Z _ _ P hP X i hh0 hx0 hx1 η0 η1 t0 t1 hη0 hc ht0 v
  have hη : η0 = 0 := (mul_eq_zero.1 hc).resolve_right hh0.ne'
  have hbs : ∀ r : ℝ, BoxSign (P.xbar i) (X.1 i) r ↔ r = 0 := fun r =>
    ⟨fun h => le_antisymm (h.1 hx1) (h.2 hx0), fun h => ⟨fun _ => h.le, fun _ => h.ge⟩⟩
  refine ⟨fun hb hg => ?_, fun hs hg => ?_⟩
  · have ht : t0 i = P.kp i := ht0.2.2.1 (by linarith)
    have hv : v = Resid P η1 t1 i := by
      simp only [v, etaHat, Resid, hη, ht, hg]
      ring
    exact ⟨hv, by rw [hbs, hv]⟩
  · have ht : t0 i = -P.km i := ht0.2.2.2 (by linarith)
    have hv : v = Sinc P η1 t1 i - P.beta * (∑ z, P.q z * η1 z) * (1 - P.km i) := by
      simp only [v, etaHat, hη, ht, hg]
      ring
    exact ⟨hv, by rw [hbs, hv, sub_eq_zero]⟩

theorem costlessIdentity : CostlessIdentity := by
  intro ι Z _ _ P hP X η1 t1 i hT hkp hkm hslack
  have hη : ∀ z, η1 z = 0 := fun z => (mul_eq_zero.1 (hT z).2.1).resolve_right (hslack z).ne'
  have ht : ∀ z, t1 z i = 0 := fun z => by
    have := ((hT z).2.2 i).1
    rw [hkp, hkm] at this
    linarith [this.1, this.2.1]
  refine ⟨?_, by simp [hη]⟩
  simp [Sinc, sval, hη, ht]

theorem interiorTradeBinding : InteriorTradeBinding := by
  intro ι Z _ _ P hP X i hx0 hx1 η0 emy η1 t0 t1 ht0 v c
  have hbs : ∀ r : ℝ, BoxSign (P.xbar i) (X.1 i) r ↔ r = 0 := fun r =>
    ⟨fun h => le_antisymm (h.1 hx1) (h.2 hx0), fun h => ⟨fun _ => h.le, fun _ => h.ge⟩⟩
  have hk := rates hP i
  refine ⟨fun hb hg => ?_, fun hs hg => ?_⟩
  · have ht : t0 i = P.kp i := ht0.2.2.1 (by linarith)
    have hv : v = Sinc P η1 t1 i - c * (1 + P.kp i) := by
      simp only [v, c, etaHat, ht, hg]
      ring
    refine ⟨hv, by rw [hbs, hv, sub_eq_zero], fun h0 hB => ?_⟩
    rw [hbs, hv, sub_eq_zero] at hB
    rw [hB]
    have : 0 ≤ η0 * (1 + P.kp i) := mul_nonneg h0 (by linarith)
    simp only [c]
    nlinarith
  · have ht : t0 i = -P.km i := ht0.2.2.2 (by linarith)
    have hv : v = Sinc P η1 t1 i - c * (1 - P.km i) := by
      simp only [v, c, etaHat, ht, hg]
      ring
    refine ⟨hv, by rw [hbs, hv, sub_eq_zero], fun h0 hB => ?_⟩
    rw [hbs, hv, sub_eq_zero] at hB
    rw [hB]
    have : 0 ≤ η0 * (1 - P.km i) := mul_nonneg h0 (by linarith)
    simp only [c]
    nlinarith

/-! ### Part 4 -/

/-- Moving one coordinate moves every marginal by its covariance with it. -/
lemma g0_move (P : Two ι Z) {xm xr : ι → ℝ} {E : ι} (h : ∀ j, j ≠ E → xr j = xm j) (i : ι) :
    g0 P xr i = g0 P xm i - P.gamma * (P.S0 i E * (xr E - xm E)) := by
  have hs : ∑ j, P.S0 i j * xr j - ∑ j, P.S0 i j * xm j = P.S0 i E * (xr E - xm E) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single E]
    · ring
    · intro j _ hj
      rw [h j hj, sub_self]
    · intro hE
      exact absurd (Finset.mem_univ E) hE
  have e : ∑ j, P.S0 i j * xr j = ∑ j, P.S0 i j * xm j + P.S0 i E * (xr E - xm E) := by linarith
  simp only [g0, marg]
  rw [e]
  ring

theorem hedgeTerm : HedgeTerm := by
  intro ι Z _ _ P hP xm xr A E _ hmove hSE hA hE hkE η1 t1 hroot
  have hγ : 0 < P.gamma := hP.1
  have gA := g0_move P hmove A
  have gE := g0_move P hmove E
  rw [hA] at gA
  rw [hE] at gE
  have hΔ : P.gamma * (xr E - xm E) = (Sinc P η1 t1 E - etaHat P 0 η1) / P.S0 E E := by
    rw [eq_div_iff hSE.ne']
    linarith
  have hg : g0 P xr A = P.kp A - P.S0 A E / P.S0 E E * (Sinc P η1 t1 E - etaHat P 0 η1) := by
    rw [gA, show P.gamma * (P.S0 A E * (xr E - xm E)) = P.S0 A E * (P.gamma * (xr E - xm E)) by ring,
      hΔ]
    ring
  rw [hg]
  simp only [Resid, etaHat, hkE]
  ring

theorem concaveSign : ConcaveSign := by
  intro Jred φ lo hi am ad hc had hmax ham hle heq
  have key : ∀ t, t ∈ Icc lo hi → Jred am < Jred t →
      ¬ (ad ≤ am ∧ am < t) ∧ ¬ (t < am ∧ am ≤ ad) := by
    intro t ht hlt
    have hJ : Jred t ≤ Jred ad := hmax ht
    -- `am` lies between `ad` and `t`, so concavity puts `J^red(am)` above `min(J^red(ad), J^red(t))`
    have between : ∀ {u w : ℝ}, u ∈ Icc lo hi → w ∈ Icc lo hi → u ≤ am → am ≤ w → u < w →
        min (Jred u) (Jred w) ≤ Jred am := by
      intro u w hu hw h1 h2 h3
      exact hc.ge_on_segment hu hw (by rw [segment_eq_Icc h3.le]; exact ⟨h1, h2⟩)
    have ham' : am ∈ Icc lo hi := ⟨ham.1.le, ham.2.le⟩
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · rcases h1.lt_or_eq with h1 | h1
      · have := between had ht h1.le h2.le (h1.trans h2)
        have : min (Jred ad) (Jred t) = Jred t := min_eq_right hJ
        linarith
      · rw [h1] at hJ
        linarith
    · rcases h2.lt_or_eq with h2 | h2
      · have := between ht had h1.le h2.le (h1.trans h2)
        have : min (Jred t) (Jred ad) = Jred t := min_eq_left hJ
        linarith
      · rw [← h2] at hJ
        linarith
  constructor
  · intro v hd hv
    by_contra hna
    push Not at hna
    have hd' := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi am) (by simp)).1 (hd.mono Ioi_subset_Ici_self)
    have hev : ∀ᶠ t in nhdsWithin am (Ioi am), 0 < slope φ am t ∧ t < hi :=
      (hd'.eventually_const_lt hv).and
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ham.2))
    obtain ⟨t, ⟨hs, hthi⟩, htam⟩ := (hev.and self_mem_nhdsWithin).exists
    have htam' : am < t := htam
    have ht : t ∈ Icc lo hi := ⟨by linarith [ham.1], hthi.le⟩
    have hφ : φ am < φ t := by
      rw [slope_def_field] at hs
      have := (div_pos_iff.1 hs).resolve_right (fun h => by linarith [h.2])
      linarith [this.1]
    have := (key t ht (by linarith [hle t ht])).1 ⟨hna, htam'⟩
    exact this
  · intro v hd hv
    by_contra hna
    push Not at hna
    have hd' := (hasDerivWithinAt_iff_tendsto_slope' (s := Iio am) (by simp)).1 (hd.mono Iio_subset_Iic_self)
    have hev : ∀ᶠ t in nhdsWithin am (Iio am), slope φ am t < 0 ∧ lo < t :=
      (hd'.eventually_lt_const hv).and
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds ham.1))
    obtain ⟨t, ⟨hs, htlo⟩, htam⟩ := (hev.and self_mem_nhdsWithin).exists
    have htam' : t < am := htam
    have ht : t ∈ Icc lo hi := ⟨htlo.le, by linarith [ham.2]⟩
    have hφ : φ am < φ t := by
      rw [slope_def_field] at hs
      have := (div_neg_iff.1 hs).resolve_right (fun h => by linarith [h.2])
      linarith [this.1]
    have := (key t ht (by linarith [hle t ht])).2 ⟨htam', hna⟩
    exact this

theorem proof : Standalone.M7TwoReviewsBounds.statement :=
  ⟨cashPriceBound, slackWhenCovered, dynamicCashPrice, brackets, interiorTrade, costlessIdentity,
    interiorTradeBinding, hedgeTerm, concaveSign⟩

end

end Novel.M7TwoReviewsBoundsProof

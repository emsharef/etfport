import Standalone.M7QuantileFlexibility
import Novel.M7SeveralFundsReserveProof
import Novel.M7IncumbentAwareFirstStageProof

/-!
# Claim 049: proof

Part 1 extends claim 113's accounting to a set of ETFs. Part 2 is finite-law arithmetic. Part 3
combines four facts:
- today's strong concavity bound, from the myopic lines;
- the relaxed tomorrow's supergradient, from the relaxed lines;
- the budgeted tomorrow's Lagrangian bound (claim 044's `lag_max`) with part 1's accounting;
- claim 111's completed square.
-/

namespace Novel.M7QuantileFlexibilityProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M7TwoReviewsBounds
  Standalone.M7SeveralFundsReserve Standalone.M7QuantileFlexibility Novel.M7TwoReviewsBoundsProof
  Matrix

noncomputable section

variable {ι Z : Type} [Fintype ι]

/-! ### Part 1: the accounting with several ETFs -/

/-- An ETF's counted proceeds, `(1 - κ⁻_E)(g_E x_{0,E} - (x̌_E)⁺)⁺`. -/
def saleE (P : Two ι Z) (z : Z) (x0 : ι → ℝ) (E : ι) : ℝ :=
  (1 - P.km E) * max (P.g z E * x0 E - max (xhatS P z E) 0) 0

/-- The cash a state's holding `x` uses from the marked holdings. -/
def cu (P : Two ι Z) (z : Z) (x0 x : ι → ℝ) : ℝ :=
  ∑ j, ((x j - carry P z x0 j) + pc (P.kp j) (P.km j) (x j - carry P z x0 j))

section Acct

variable {P : Two ι Z} {z : Z} {x0 x : ι → ℝ} {e : ℝ} {t : ι → ℝ}

lemma buy_bound (hP : Hyp P) (hC : Cov P) (hx : ∀ i, 0 ≤ x i) (hx0 : ∀ i, 0 ≤ x0 i) (_he : 0 ≤ e)
    {j : ι} (hsl : Slope (P.kp j) (P.km j) (x j - carry P z x0 j) (t j))
    (hbs : BoxSign (P.xbar j) (x j) (g1 P z x j - e - (1 + e) * t j))
    (hb : carry P z x0 j < x j) :
    P.gamma * (P.S1 z j j * x j) ≤ P.mu1 z j - P.kp j - e * (1 + P.kp j) := by
  have hc0 : 0 ≤ carry P z x0 j := mul_nonneg (hP.2.2.2.2.2.2.2.1 z j).le (hx0 j)
  have ht := hsl.2.2.1 (by linarith)
  have hR := hbs.2 (by linarith)
  rw [ht] at hR
  have h2 := g1_le (z := z) hP hC hx j
  linarith

lemma xhat_of_buy (hP : Hyp P) (hC : Cov P) {j : ι} {e : ℝ} (he : 0 ≤ e)
    (h : P.gamma * (P.S1 z j j * x j) ≤ P.mu1 z j - P.kp j - e * (1 + P.kp j)) :
    x j ≤ xhat P z j := by
  have hc : 0 < P.gamma * P.S1 z j j := mul_pos hP.1 (hC.2 z j)
  have hk := (rates hP j).1
  unfold xhat
  rw [le_div_iff₀ hc]
  have := le_max_left (P.mu1 z j - P.kp j) 0
  nlinarith

lemma xhat_of_buy_lt (hP : Hyp P) (hC : Cov P) {j : ι} {e : ℝ} (he : 0 < e)
    (h : P.gamma * (P.S1 z j j * x j) ≤ P.mu1 z j - P.kp j - e * (1 + P.kp j)) :
    x j < xhat P z j := by
  have hc : 0 < P.gamma * P.S1 z j j := mul_pos hP.1 (hC.2 z j)
  have hk := (rates hP j).1
  unfold xhat
  rw [lt_div_iff₀ hc]
  have := le_max_left (P.mu1 z j - P.kp j) 0
  nlinarith [mul_pos he (by linarith : (0 : ℝ) < 1 + P.kp j)]

lemma etf_bound (hP : Hyp P) (hC : Cov P) (hx : ∀ i, 0 ≤ x i) (he : 0 ≤ e) {j : ι}
    (hsl : Slope (P.kp j) (P.km j) (x j - carry P z x0 j) (t j))
    (hbs : BoxSign (P.xbar j) (x j) (g1 P z x j - e - (1 + e) * t j)) :
    x j ≤ max (xhatS P z j) 0 := by
  rcases lt_or_eq_of_le (hx j) with hpos | hzero
  · have hR := hbs.2 hpos
    have h2 := g1_le (z := z) hP hC hx j
    have hk := rates hP j
    have hc : 0 < P.gamma * P.S1 z j j := mul_pos hP.1 (hC.2 z j)
    have h3 : P.gamma * (P.S1 z j j * x j) ≤ P.mu1 z j + P.km j := by nlinarith [hsl.1]
    have : x j ≤ xhatS P z j := by
      unfold xhatS
      rw [le_div_iff₀ hc]
      linarith
    exact this.trans (le_max_left _ _)
  · rw [← hzero]
    exact le_max_right _ _

/-- One instrument's cash use is at most its part of the need, less an ETF's counted proceeds. -/
lemma term_weak [DecidableEq ι] (hP : Hyp P) (_hx0 : ∀ i, 0 ≤ x0 i) (Es : Finset ι) {j : ι}
    (hbuy : carry P z x0 j < x j → x j ≤ xhat P z j) (hE : j ∈ Es → x j ≤ max (xhatS P z j) 0) :
    (x j - carry P z x0 j) + pc (P.kp j) (P.km j) (x j - carry P z x0 j) ≤
      needI P z x0 j - if j ∈ Es then saleE P z x0 j else 0 := by
  have htl := term_le hP j (x j - carry P z x0 j)
  have hk : 0 ≤ 1 + P.kp j := by linarith [(rates hP j).1]
  have hkm := rates hP j
  have hmono : (1 + P.kp j) * max (x j - carry P z x0 j) 0 ≤ needI P z x0 j := by
    unfold needI
    refine mul_le_mul_of_nonneg_left ?_ hk
    by_cases hb : carry P z x0 j < x j
    · exact max_le_max (by linarith [hbuy hb]) le_rfl
    · rw [max_eq_right (by linarith [not_lt.1 hb])]
      exact le_max_right _ _
  by_cases hjE : j ∈ Es
  · simp only [hjE, ite_true]
    have hEle := hE hjE
    have hcarry : carry P z x0 j = P.g z j * x0 j := rfl
    by_cases hs : max (xhatS P z j) 0 < carry P z x0 j
    · have hd : (x j - carry P z x0 j) + pc (P.kp j) (P.km j) (x j - carry P z x0 j) =
          (x j - carry P z x0 j) * (1 - P.km j) := by
        simp only [pc]
        rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      have hsale : saleE P z x0 j = (1 - P.km j) * (carry P z x0 j - max (xhatS P z j) 0) := by
        simp only [saleE]
        rw [← hcarry, max_eq_left (by linarith)]
      have hn : 0 ≤ needI P z x0 j := mul_nonneg hk (le_max_right _ _)
      rw [hd, hsale]
      nlinarith
    · have hsale : saleE P z x0 j = 0 := by
        simp only [saleE]
        rw [← hcarry, max_eq_right (by linarith [not_lt.1 hs]), mul_zero]
      rw [hsale, sub_zero]
      exact htl.trans hmono
  · simp only [hjE, ite_false, sub_zero]
    exact htl.trans hmono

lemma term_strict [DecidableEq ι] (hP : Hyp P) (_hx0 : ∀ i, 0 ≤ x0 i) (Es : Finset ι) {j : ι}
    (hb : carry P z x0 j < x j) (hlt : x j < xhat P z j)
    (hE : j ∈ Es → x j ≤ max (xhatS P z j) 0) :
    (x j - carry P z x0 j) + pc (P.kp j) (P.km j) (x j - carry P z x0 j) <
      needI P z x0 j - if j ∈ Es then saleE P z x0 j else 0 := by
  have htl := term_le hP j (x j - carry P z x0 j)
  have hk : 0 < 1 + P.kp j := by linarith [(rates hP j).1]
  rw [max_eq_left (by linarith)] at htl
  have hl : (x j - carry P z x0 j) + pc (P.kp j) (P.km j) (x j - carry P z x0 j) < needI P z x0 j := by
    unfold needI
    rw [max_eq_left (by linarith)]
    nlinarith
  have hsale : (if j ∈ Es then saleE P z x0 j else 0) = 0 := by
    split_ifs with hjE
    · have hEle := hE hjE
      simp only [saleE]
      have hcarry : carry P z x0 j = P.g z j * x0 j := rfl
      rw [← hcarry, max_eq_right (by linarith), mul_zero]
    · rfl
  rw [hsale, sub_zero]
  exact hl

lemma sum_ite_sale [DecidableEq ι] (P : Two ι Z) (z : Z) (x0 : ι → ℝ) (Es : Finset ι) :
    ∑ j, (needI P z x0 j - if j ∈ Es then saleE P z x0 j else 0) =
      need P z x0 - ∑ E ∈ Es, saleE P z x0 E := by
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-- The accounting at a point with its lines at any `e ≥ 0`: its cash use is at most the need less
the ETFs' counted proceeds. -/
lemma acct [DecidableEq ι] (hP : Hyp P) (hC : Cov P) (hx : ∀ i, 0 ≤ x i) (hx0 : ∀ i, 0 ≤ x0 i)
    (he : 0 ≤ e) (Es : Finset ι)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (x i - carry P z x0 i) (t i) ∧
      BoxSign (P.xbar i) (x i) (g1 P z x i - e - (1 + e) * t i)) :
    cu P z x0 x ≤ need P z x0 - ∑ E ∈ Es, saleE P z x0 E := by
  rw [← sum_ite_sale]
  exact Finset.sum_le_sum fun j _ => term_weak hP hx0 Es
    (fun hb => xhat_of_buy hP hC he (buy_bound hP hC hx hx0 he (hl j).1 (hl j).2 hb))
    (fun _ => etf_bound hP hC hx he (hl j).1 (hl j).2)

end Acct

theorem coverage : Coverage := by
  classical
  intro ι Z _ _ P Es hP hC X hX z e t h hle
  rcases h.1.eq_or_lt with he0 | he
  · exact ⟨t, he0 ▸ h⟩
  have hx0 : ∀ i, 0 ≤ X.1 i := fun i => (hX.1 i).1
  have hx : ∀ i, 0 ≤ X.2 z i := fun i => ((hX.2.1 z) i).1
  have hh1 : h1 P X.1 X.2 z = 0 := (mul_eq_zero.1 h.2.1).resolve_left he.ne'
  have hl := h.2.2
  have e1 := h1_eq P X z
  have hliq : liqM P z Es X.1 = h0 P X.1 + ∑ E ∈ Es, saleE P z X.1 E := rfl
  -- no purchase: it would leave cash
  have hnb : ∀ j, ¬ carry P z X.1 j < X.2 z j := by
    intro j0 hb
    have hlt : cu P z X.1 (X.2 z) < need P z X.1 - ∑ E ∈ Es, saleE P z X.1 E := by
      rw [← sum_ite_sale]
      refine Finset.sum_lt_sum (fun j _ => term_weak hP hx0 Es
        (fun hb => xhat_of_buy hP hC he.le (buy_bound hP hC hx hx0 he.le (hl j).1 (hl j).2 hb))
        (fun _ => etf_bound hP hC hx he.le (hl j).1 (hl j).2)) ⟨j0, Finset.mem_univ _, ?_⟩
      exact term_strict hP hx0 Es hb
        (xhat_of_buy_lt hP hC he (buy_bound hP hC hx hx0 he.le (hl j0).1 (hl j0).2 hb))
        (fun _ => etf_bound hP hC hx he.le (hl j0).1 (hl j0).2)
    have : h1 P X.1 X.2 z = h0 P X.1 - cu P z X.1 (X.2 z) := e1
    linarith
  have hnt := nothing_traded hP hX h he hnb
  have hsale : ∑ E ∈ Es, saleE P z X.1 E = 0 := Finset.sum_eq_zero fun E hE => by
    have hEle := etf_bound hP hC hx he.le (hl E).1 (hl E).2
    rw [hnt E] at hEle
    simp only [saleE]
    have hcarry : carry P z X.1 E = P.g z E * X.1 E := rfl
    rw [← hcarry, max_eq_right (by linarith), mul_zero]
  rw [hliq, hsale, add_zero] at hle
  exact slackWhenCovered ι Z P hP hC X hX z e t h hle

/-! ### Part 2 -/

section Law

variable {Z : Type} [Fintype Z]

lemma Pr_mono {q : Z → ℝ} (hq : ∀ z, 0 ≤ q z) {A B : Z → Prop} (h : ∀ z, A z → B z) :
    Pr q A ≤ Pr q B := by
  classical
  unfold Pr
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases ha : A z
  · simp [ha, h z ha]
  · simp only [ha, ite_false]
    split_ifs <;> linarith [hq z]

lemma Pr_compl (q : Z → ℝ) (A : Z → Prop) : Pr q A + Pr q (fun z => ¬ A z) = ∑ z, q z := by
  classical
  unfold Pr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases ha : A z <;> simp [ha]

lemma Pr_true (q : Z → ℝ) : Pr q (fun _ => True) = ∑ z, q z := by
  classical
  simp [Pr]

lemma Pr_false (q : Z → ℝ) {A : Z → Prop} (h : ∀ z, ¬ A z) : Pr q A = 0 := by
  classical
  unfold Pr
  exact Finset.sum_eq_zero fun z _ => by simp [h z]

/-- On a finite law, `VaR_{1-ε}(X) ≤ a` iff `P(X ≤ a) ≥ 1 - ε`. -/
lemma var_le_iff {q X : Z → ℝ} {ε a : ℝ} (hq : ∀ z, 0 ≤ q z) (h1 : ∑ z, q z = 1) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) : VaR q X ε ≤ a ↔ 1 - ε ≤ Pr q fun z => X z ≤ a := by
  classical
  have hne : Nonempty Z := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at h1
  set S : Set ℝ := {c | 1 - ε ≤ Pr q fun z => X z ≤ c} with hS
  have hmax : (⨆ z, X z) ∈ S := by
    show 1 - ε ≤ Pr q fun z => X z ≤ ⨆ z, X z
    have : Pr q (fun z => X z ≤ ⨆ z, X z) = ∑ z, q z := by
      rw [← Pr_true q]
      unfold Pr
      exact Finset.sum_congr rfl fun z _ => by
        simp [le_ciSup (f := X) (Set.finite_range _).bddAbove z]
    rw [this, h1]
    linarith
  have hlow : ∀ c ∈ S, (⨅ z, X z) ≤ c := by
    intro c hc
    by_contra hlt
    push Not at hlt
    have : Pr q (fun z => X z ≤ c) = 0 :=
      Pr_false q fun z hz => by
        have := ciInf_le (f := X) (Set.finite_range _).bddBelow z
        linarith
    have : 1 - ε ≤ 0 := by rw [← this]; exact hc
    linarith
  have hbdd : BddBelow S := ⟨_, hlow⟩
  constructor
  · intro hle
    by_contra hna
    push Not at hna
    -- the smallest value above `a`
    have hT : (Finset.univ.filter fun z => a < X z).Nonempty := by
      by_contra hT
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hT
      have : Pr q (fun z => X z ≤ a) = ∑ z, q z := by
        rw [← Pr_true q]
        unfold Pr
        exact Finset.sum_congr rfl fun z _ => by
          simp [not_lt.1 (hT (Finset.mem_univ z))]
      rw [this, h1] at hna
      linarith
    set m := (Finset.univ.filter fun z => a < X z).inf' hT X with hm
    have ham : a < m := by
      rw [hm, Finset.lt_inf'_iff]
      intro z hz
      exact (Finset.mem_filter.1 hz).2
    have hSm : ∀ c ∈ S, m ≤ c := by
      intro c hc
      by_contra hlt
      push Not at hlt
      have hsub : ∀ z, X z ≤ c → X z ≤ a := by
        intro z hz
        by_contra hza
        push Not at hza
        have : m ≤ X z := Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_univ z, hza⟩)
        linarith
      have := Pr_mono hq hsub
      have hc' : 1 - ε ≤ Pr q fun z => X z ≤ c := hc
      linarith
    have : m ≤ sInf S := le_csInf ⟨_, hmax⟩ hSm
    have hle' : sInf S ≤ a := hle
    linarith
  · intro ha
    exact csInf_le hbdd ha

lemma Pr_congr (q : Z → ℝ) {A B : Z → Prop} (h : ∀ z, A z ↔ B z) : Pr q A = Pr q B := by
  have : A = B := funext fun z => propext (h z)
  rw [this]

end Law

theorem varZero : VarZero := by
  intro Z _ q D ε hq h1 hε0 hε1 hD
  have hc := Pr_compl q fun z => D z ≤ 0
  rw [h1] at hc
  have hpos : Pr q (fun z => ¬ D z ≤ 0) = Pr q fun z => 0 < D z := Pr_congr q fun z => not_le
  have hge : 0 ≤ VaR q D ε := by
    by_contra hlt
    push Not at hlt
    have h := (var_le_iff hq h1 hε0 hε1).1 (le_refl (VaR q D ε))
    have : Pr q (fun z => D z ≤ VaR q D ε) = 0 := Pr_false q fun z hz => by linarith [hD z]
    linarith
  constructor
  · intro h0
    have := (var_le_iff hq h1 hε0 hε1).1 (le_of_eq h0)
    linarith
  · intro hp
    exact le_antisymm ((var_le_iff hq h1 hε0 hε1).2 (by linarith)) hge

theorem stateFree : StateFree := by
  intro Z _ q N L ε hq h1 hε0 hε1
  rw [var_le_iff hq h1 hε0 hε1]
  have hc := Pr_compl q fun z => N z ≤ L
  rw [h1] at hc
  have e : (Pr q fun z => 0 < max (N z - L) 0) = Pr q fun z => ¬ N z ≤ L :=
    Pr_congr q fun z => by
      rw [lt_max_iff, not_le]
      constructor
      · rintro (h | h)
        · linarith
        · exact absurd h (lt_irrefl 0)
      · intro h
        left
        linarith
  rw [e]
  constructor <;> intro h <;> linarith

theorem tailIdentity : TailIdentity := by
  classical
  intro Z _ q Y ε hq h1 hε hε1 hY hP
  have hmain : ∀ c, (∑ z, q z * Y z) / ε ≤ RU q Y ε c := by
    intro c
    have key : ∑ z, q z * Y z ≤ c * ε + ∑ z, q z * max (Y z - c) 0 := by
      rcases lt_or_ge c 0 with hc | hc
      swap
      · have hz : ∀ z, q z * Y z - c * (if 0 < Y z then q z else 0) ≤ q z * max (Y z - c) 0 := by
          intro z
          split_ifs with hy
          · nlinarith [le_max_left (Y z - c) 0, hq z]
          · have : Y z = 0 := le_antisymm (not_lt.1 hy) (hY z)
            rw [this]
            nlinarith [le_max_right (0 - c) 0, hq z]
        have hs := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hz z
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
        have hP' : (∑ z, if 0 < Y z then q z else 0) ≤ ε := hP
        nlinarith
      · have hz : ∀ z, q z * max (Y z - c) 0 = q z * Y z - c * q z := fun z => by
          rw [max_eq_left (by linarith [hY z])]
          ring
        rw [Finset.sum_congr rfl fun z _ => hz z, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
        nlinarith
    unfold RU
    rw [div_le_iff₀ hε, add_mul, div_mul_cancel₀ _ hε.ne']
    linarith
  have h0 : RU q Y ε 0 = (∑ z, q z * Y z) / ε := by
    unfold RU
    rw [zero_add]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by rw [sub_zero, max_eq_left (hY z)]
  refine ⟨⟨⟨0, h0⟩, fun v ⟨c, hc⟩ => hc ▸ hmain c⟩, fun M hM => (hmain M).trans (le_of_eq ?_)⟩
  unfold RU
  rw [Finset.sum_eq_zero fun z _ => by rw [max_eq_right (by linarith [hM z]), mul_zero], zero_div,
    add_zero]

/-! ### Part 3 -/

section Loss

variable [Fintype Z] {P : Two ι Z}

/-- Today's strong bound from the myopic root's lines: every root-feasible `y` has
`f_0(y) ≤ f_0(x) - (γ/2)(y - x)'Σ_0(y - x)`. -/
lemma today_strong (hP : Hyp P) {x y : ι → ℝ} {η0 : ℝ} {t0 : ι → ℝ} (hη0 : 0 ≤ η0)
    (hc0 : η0 * h0 P x = 0) (hx : Box P x) (hy : Box P y) (hhy : 0 ≤ h0 P y)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (x i - P.xm i) (t0 i) ∧
      BoxSign (P.xbar i) (x i) (g0 P x i - η0 - (1 + η0) * t0 i)) :
    Q0 P y - cost P (y - P.xm) ≤ Q0 P x - cost P (x - P.xm) - P.gamma / 2 * quad P.S0 (y - x) := by
  have hQ := Novel.M7TwoReviewsBindingBudgetProof.Qv_expand (mu := P.mu0) hP.2.2.2.2.1.1 P.gamma x
    (y - x) 1
  rw [one_smul, add_sub_cancel] at hQ
  simp only [one_mul, one_pow, Pi.sub_apply] at hQ
  have hC := Novel.M7TwoReviewsBindingBudgetProof.cost_ge (P := P) (u := x - P.xm) (fun i => (hl i).1) (y - P.xm)
  have e1 : ∑ i, t0 i * ((y - P.xm) i - (x - P.xm) i) = ∑ i, t0 i * (y i - x i) :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [e1] at hC
  have hbs : ∑ i, (g0 P x i - η0 - (1 + η0) * t0 i) * (y i - x i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Novel.M7TwoReviewsBindingBudgetProof.bs_le (hl i).2 (hx i).1 (hx i).2
      (hy i).1 (hy i).2
  rw [Novel.M7TwoReviewsBindingBudgetProof.sum_line] at hbs
  have hh : h0 P y - h0 P x = -∑ i, (y i - x i) - (cost P (y - P.xm) - cost P (x - P.xm)) := by
    simp only [h0]
    have : ∑ i, (y i - P.xm i) - ∑ i, (x i - P.xm i) = ∑ i, (y i - x i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hηy : 0 ≤ η0 * h0 P y := mul_nonneg hη0 hhy
  have hmarg : ∑ i, marg P.mu0 P.S0 P.gamma x i * (y i - x i) =
      ∑ i, g0 P x i * (y i - x i) := rfl
  have hQ0 : ∀ w, Q0 P w = Qv P.mu0 P.S0 P.gamma w := fun w => rfl
  rw [hQ0, hQ0, hQ]
  rw [hmarg]
  nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 1 + η0)]

/-- The relaxed tomorrow's supergradient: a relaxed point with its `η = 0` lines bounds every boxed
holding from any carried holdings. -/
lemma relaxed_bound (hP : Hyp P) (z : Z) {c c' xu tu x1 : ι → ℝ} (hxu : Box P xu) (hx1 : Box P x1)
    (hl : ∀ i, Slope (P.kp i) (P.km i) (xu i - c i) (tu i) ∧
      BoxSign (P.xbar i) (xu i) (g1 P z xu i - tu i)) :
    f1 P z c' x1 ≤ f1 P z c xu + ∑ i, tu i * (c' i - c i) := by
  have hQ := Novel.M7TwoReviewsBindingBudgetProof.Qv_le (mu := P.mu1 z) (hP.2.2.2.2.2.1 z) hP.1.le xu x1
  have hC := Novel.M7TwoReviewsBindingBudgetProof.cost_ge (P := P) (u := xu - c) (fun i => (hl i).1)
    (x1 - c')
  have hbs : ∑ i, (g1 P z xu i - tu i) * (x1 i - xu i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Novel.M7TwoReviewsBindingBudgetProof.bs_le (hl i).2 (hxu i).1
      (hxu i).2 (hx1 i).1 (hx1 i).2
  have e1 : ∑ i, tu i * ((x1 - c') i - (xu - c) i) =
      ∑ i, tu i * (x1 i - xu i) - ∑ i, tu i * (c' i - c i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  have e2 : ∑ i, (g1 P z xu i - tu i) * (x1 i - xu i) =
      ∑ i, marg (P.mu1 z) (P.S1 z) P.gamma xu i * (x1 i - xu i) - ∑ i, tu i * (x1 i - xu i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [g1]; ring
  rw [e1] at hC
  rw [e2] at hbs
  unfold f1 Q1
  linarith

/-- The budgeted tomorrow against the relaxed point: the gap is at most `η̄ D`. -/
lemma budget_tail [DecidableEq ι] (hP : Hyp P) (hC : Cov P) (Es : Finset ι) {X : (ι → ℝ) × (Z → ι → ℝ)}
    (hX : X ∈ Feas P) {z : Z} {e : ℝ} {t : ι → ℝ} (h : LinesAt P X z e t) {xu tu : ι → ℝ}
    (hxu : Box P xu) (hl : ∀ i, Slope (P.kp i) (P.km i) (xu i - carry P z X.1 i) (tu i) ∧
      BoxSign (P.xbar i) (xu i) (g1 P z xu i - tu i)) :
    f1 P z (carry P z X.1) xu - f1 P z (carry P z X.1) (X.2 z) ≤ etaBar P z * short P z Es X.1 := by
  obtain ⟨e', t', hL, hbar, _⟩ := cashPriceBound ι Z P hP hC X hX z e t h
  have hbox : Box P (X.2 z) := hX.2.1 z
  have hmax := Novel.M7TwoReviewsBindingBudgetProof.lag_max (mu := P.mu1 z) (S := P.S1 z)
    (c := carry P z X.1) (hP.2.2.2.2.2.1 z) hP.1.le hL.1 hbox hL.2.2 hxu
  have hlag : ∀ y, lagOne P (P.mu1 z) (P.S1 z) (carry P z X.1) e' y =
      f1 P z (carry P z X.1) y - e' * cu P z X.1 y := fun y => by
    simp only [lagOne, f1, Q1, cu, cost, Finset.sum_add_distrib, Pi.sub_apply]
    ring
  have hle : lagOne P (P.mu1 z) (P.S1 z) (carry P z X.1) e' xu ≤
      lagOne P (P.mu1 z) (P.S1 z) (carry P z X.1) e' (X.2 z) := hmax
  rw [hlag, hlag] at hle
  have hh1 : h1 P X.1 X.2 z = h0 P X.1 - cu P z X.1 (X.2 z) := h1_eq P X z
  have hcomp : e' * cu P z X.1 (X.2 z) = e' * h0 P X.1 := by
    have := hL.2.1
    rw [hh1] at this
    linarith [this]
  have hx0 : ∀ i, 0 ≤ X.1 i := fun i => (hX.1 i).1
  have hacc := acct (z := z) (x0 := X.1) (x := xu) (e := 0) (t := tu) hP hC (fun i => (hxu i).1) hx0
    le_rfl Es fun i => ⟨(hl i).1, by
      have := (hl i).2
      convert this using 1
      ring⟩
  have hliq : liqM P z Es X.1 = h0 P X.1 + ∑ E ∈ Es, saleE P z X.1 E := rfl
  have he' : 0 ≤ e' := hL.1
  have hsh1 : need P z X.1 - liqM P z Es X.1 ≤ short P z Es X.1 := le_max_left _ _
  have hsh0 : 0 ≤ short P z Es X.1 := le_max_right _ _
  have h1' : e' * (need P z X.1 - liqM P z Es X.1) ≤ e' * short P z Es X.1 :=
    mul_le_mul_of_nonneg_left hsh1 he'
  have h2' : e' * short P z Es X.1 ≤ etaBar P z * short P z Es X.1 :=
    mul_le_mul_of_nonneg_right hbar hsh0
  have h3' : e' * (cu P z X.1 xu - h0 P X.1) ≤ e' * (need P z X.1 - liqM P z Es X.1) :=
    mul_le_mul_of_nonneg_left (by linarith) he'
  nlinarith

lemma quad_eq (S : ι → ι → ℝ) (d : ι → ℝ) : quad S d = d ⬝ᵥ (Matrix.of S *ᵥ d) := by
  simp only [quad, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Loss

theorem lossBound : LossBound := by
  intro ι Z _ _ _ P Es hP hC hSig Xm hXm η0 t0 η1 t1 xu tu hη0 hc0 hl0 hT hrel S Xd hXd
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hβ : 0 < P.beta := hP.2.1
  have hγ : 0 < P.gamma := hP.1
  set d := Xd.1 - Xm.1 with hd
  have hJ : ∀ X : (ι → ℝ) × (Z → ι → ℝ), J P X = (Q0 P X.1 - cost P (X.1 - P.xm)) +
      P.beta * ∑ z, P.q z * f1 P z (carry P z X.1) (X.2 z) := fun X => rfl
  have h1 := today_strong hP hη0 hc0 hXm.1 hXd.1 hXd.2.2.1 hl0
  have h2 : ∀ z, f1 P z (carry P z Xd.1) (Xd.2 z) ≤
      f1 P z (carry P z Xm.1) (xu z) + ∑ i, tu z i * (P.g z i * d i) := fun z => by
    have := relaxed_bound (c := carry P z Xm.1) (c' := carry P z Xd.1) hP z (hrel z).1 (hXd.2.1 z)
      (hrel z).2
    convert this using 2
    exact Finset.sum_congr rfl fun i _ => by simp only [carry, hd, Pi.sub_apply]; ring
  have h3 : ∀ z, f1 P z (carry P z Xm.1) (xu z) - f1 P z (carry P z Xm.1) (Xm.2 z) ≤
      etaBar P z * short P z Es Xm.1 := fun z => budget_tail hP hC Es hXm (hT z) (hrel z).1 (hrel z).2
  have hSd : P.beta * ∑ z, P.q z * ∑ i, tu z i * (P.g z i * d i) = S ⬝ᵥ d := by
    simp only [S, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => by ring
  have hcsq := Novel.M7IncumbentAwareFirstStageProof.csq hSig hγ S d
  rw [← quad_eq] at hcsq
  -- the relaxed and the budgeted tomorrow, summed
  have hsum2 : ∑ z, P.q z * f1 P z (carry P z Xd.1) (Xd.2 z) ≤
      ∑ z, P.q z * f1 P z (carry P z Xm.1) (xu z) + ∑ z, P.q z * ∑ i, tu z i * (P.g z i * d i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (h2 z) (hq z).le
  have hsum3 : ∑ z, P.q z * f1 P z (carry P z Xm.1) (xu z) ≤
      ∑ z, P.q z * f1 P z (carry P z Xm.1) (Xm.2 z) + ∑ z, P.q z * (etaBar P z * short P z Es Xm.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [h3 z]) (hq z).le
  rw [hJ, hJ]
  have hb2 := mul_le_mul_of_nonneg_left hsum2 hβ.le
  have hb3 := mul_le_mul_of_nonneg_left hsum3 hβ.le
  rw [mul_add] at hb2 hb3
  nlinarith

theorem bandInputs : BandInputs := by
  intro ι Z _ _ _ P hP tu L htu hL hinv S
  have hq : ∀ z, 0 < P.q z := hP.2.2.2.2.2.2.1
  have hβ : 0 < P.beta := hP.2.1
  have hγ : 0 < P.gamma := hP.1
  have hSi : ∀ i, S i ^ 2 ≤ (P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i)) ^ 2 := by
    intro i
    have hab : |S i| ≤ P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i) := by
      simp only [S]
      rw [abs_mul, abs_of_pos hβ]
      refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun z _ => ?_)) hβ.le
      have hw : 0 < P.q z * P.g z i := mul_pos (hq z) (hP.2.2.2.2.2.2.2.1 z i)
      rw [← mul_assoc, abs_mul, abs_of_pos hw]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [(htu z i).1, le_max_right (P.kp i) (P.km i)],
        (htu z i).2.trans (le_max_left _ _)⟩) hw.le
    have h0 : 0 ≤ |S i| := abs_nonneg _
    calc S i ^ 2 = |S i| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ h0 hab 2
  have hSS : S ⬝ᵥ S ≤ ∑ i, (P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i)) ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_le_sum fun i _ => by rw [← sq]; exact hSi i
  have hmain : S ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ S) ≤
      L * ∑ i, (P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i)) ^ 2 :=
    (hinv S).trans (mul_le_mul_of_nonneg_left hSS hL)
  have h2γ : 0 < 2 * P.gamma := by positivity
  calc S ⬝ᵥ ((Matrix.of P.S0)⁻¹ *ᵥ S) / (2 * P.gamma)
      ≤ (L * ∑ i, (P.beta * ∑ z, P.q z * P.g z i * max (P.kp i) (P.km i)) ^ 2) / (2 * P.gamma) :=
        div_le_div_of_nonneg_right hmain h2γ.le
    _ = _ := by ring

theorem proof : Standalone.M7QuantileFlexibility.statement :=
  ⟨coverage, varZero, stateFree, tailIdentity, lossBound, bandInputs⟩

end

end Novel.M7QuantileFlexibilityProof

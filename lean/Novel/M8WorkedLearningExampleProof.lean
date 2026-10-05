import Novel.M7TwoReviewsBindingBudgetProof
import Standalone.M8WorkedLearningExample

/-!
# Claim 112: proof

Part 1: the filter block's algebra, the decomposition
`v'Σv = (σ_f² + p^λ)(b_A v_A + b_E v_E)² + (σ_A² + p^α) v_A² + σ_E² v_E²`, and the review problem's
strict concavity. Nonemptiness and the two-review structure come from claim 044's part 1, applied to
M8's tree. Part 2a: each moment reduces to the noise's first two moments inside the prior's, and
the tower property is finite Bayes. Part 3: each review spends at most `(1 + κ) Σ x̄` on purchases.
Part 4: exact arithmetic.
-/

namespace Novel.M8WorkedLearningExampleProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M8WorkedLearningExample Finset
open Novel.M7TwoReviewsBindingBudgetProof

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Part 1a -/

lemma postVar_eq {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) : postVar p s = s * p / (p + s) := by
  have : p + s ≠ 0 := by positivity
  simp only [postVar, gain]; field_simp; ring

lemma postVar_nonneg {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) : 0 ≤ postVar p s := by
  rw [postVar_eq hp hs]; positivity

theorem beliefs : Beliefs := by
  intro p s hp hs
  rw [postVar_eq hp hs.le]
  refine ⟨by positivity, ?_⟩
  field_simp; ring

/-! ### Part 1b -/

lemma quad_SigP (I : Inputs) (pl pa : ℝ) (v : Fin 2 → ℝ) :
    quad (SigP I pl pa) v = (I.sf2 + pl) * (I.bA * v 0 + I.bE * v 1) ^ 2 + (I.sA2 + pa) * v 0 ^ 2 +
      I.sE2 * v 1 ^ 2 := by
  simp only [quad, SigP, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma sigP_psd (I : Inputs) {pl pa : ℝ} (hf : 0 ≤ I.sf2) (hA : 0 < I.sA2) (hE : 0 < I.sE2) (hl : 0 ≤ pl)
    (ha : 0 ≤ pa) : PSD (SigP I pl pa) ∧ PosDefQ (SigP I pl pa) := by
  refine ⟨⟨fun i j => ?_, fun v => ?_⟩, fun v hv => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [SigP]
  · rw [quad_SigP]; positivity
  · rw [quad_SigP]
    have : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h; push Not at h
      exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases this with h | h
    · have := sq_pos_of_ne_zero h
      have : 0 < (I.sA2 + pa) * v 0 ^ 2 := by positivity
      nlinarith [mul_nonneg (add_nonneg hf hl) (sq_nonneg (I.bA * v 0 + I.bE * v 1)),
        mul_nonneg hE.le (sq_nonneg (v 1))]
    · have := sq_pos_of_ne_zero h
      have : 0 < I.sE2 * v 1 ^ 2 := by positivity
      nlinarith [mul_nonneg (add_nonneg hf hl) (sq_nonneg (I.bA * v 0 + I.bE * v 1)),
        mul_nonneg (add_nonneg hA.le ha) (sq_nonneg (v 0))]

theorem predRisk : PredRisk := by
  intro I pl pa lh ah γ hf hA hE hl ha hγ
  obtain ⟨hpsd, hpd⟩ := sigP_psd I hf hA hE hl ha
  refine ⟨hpsd, hpd, ?_⟩
  set a := I.bA ^ 2 * (I.sf2 + pl) + I.sA2 + pa with ha'
  set b := I.bA * I.bE * (I.sf2 + pl) with hb'
  set c := I.bE ^ 2 * (I.sf2 + pl) + I.sE2 with hc'
  have hdet : 0 < a * c - b * b := by
    have e : a * c - b * b = (I.sf2 + pl) * (I.bA ^ 2 * I.sE2 + I.bE ^ 2 * (I.sA2 + pa)) +
        (I.sA2 + pa) * I.sE2 := by rw [ha', hb', hc']; ring
    rw [e]
    have : 0 < (I.sA2 + pa) * I.sE2 := by positivity
    have : 0 ≤ (I.sf2 + pl) * (I.bA ^ 2 * I.sE2 + I.bE ^ 2 * (I.sA2 + pa)) := by positivity
    linarith
  have hS : ∀ x : Fin 2 → ℝ, ∀ i, ∑ j, SigP I pl pa i j * x j =
      if i = 0 then a * x 0 + b * x 1 else b * x 0 + c * x 1 := fun x i => by
    fin_cases i <;> simp [SigP, Fin.sum_univ_two, ha', hb', hc']
  have hm : ∀ i, muP I lh ah i = if i = 0 then I.bA * lh + ah else I.bE * lh - I.cE := fun i => by
    fin_cases i <;> simp [muP]
  set mA := I.bA * lh + ah
  set mE := I.bE * lh - I.cE
  refine ⟨![(c * mA - b * mE) / (γ * (a * c - b * b)), (a * mE - b * mA) / (γ * (a * c - b * b))],
    fun i => ?_, fun y hy => ?_⟩
  · have hD : a * c - b * b ≠ 0 := hdet.ne'
    have hγ0 : γ ≠ 0 := hγ.ne'
    have hg : γ / (γ * (a * c - b * b)) = 1 / (a * c - b * b) := by field_simp
    have ex0 : γ * (a * ((c * mA - b * mE) / (γ * (a * c - b * b))) +
        b * ((a * mE - b * mA) / (γ * (a * c - b * b)))) = mA := by
      calc _ = (a * (c * mA - b * mE) + b * (a * mE - b * mA)) * (γ / (γ * (a * c - b * b))) := by ring
        _ = mA * (a * c - b * b) * (1 / (a * c - b * b)) := by rw [hg]; ring
        _ = mA := by rw [mul_one_div, mul_div_assoc, div_self hD, mul_one]
    have ex1 : γ * (b * ((c * mA - b * mE) / (γ * (a * c - b * b))) +
        c * ((a * mE - b * mA) / (γ * (a * c - b * b)))) = mE := by
      calc _ = (b * (c * mA - b * mE) + c * (a * mE - b * mA)) * (γ / (γ * (a * c - b * b))) := by ring
        _ = mE * (a * c - b * b) * (1 / (a * c - b * b)) := by rw [hg]; ring
        _ = mE := by rw [mul_one_div, mul_div_assoc, div_self hD, mul_one]
    rw [hS, hm]
    fin_cases i
    · simpa using ex0
    · simpa using ex1
  · have h0 := hy 0; have h1 := hy 1
    rw [hS, hm] at h0 h1
    have h0 : γ * (a * y 0 + b * y 1) = mA := by simpa using h0
    have h1 : γ * (b * y 0 + c * y 1) = mE := by simpa using h1
    have e0 : y 0 = (c * mA - b * mE) / (γ * (a * c - b * b)) := by
      rw [eq_div_iff (by positivity)]; linear_combination c * h0 - b * h1
    have e1 : y 1 = (a * mE - b * mA) / (γ * (a * c - b * b)) := by
      rw [eq_div_iff (by positivity)]; linear_combination a * h1 - b * h0
    funext i; fin_cases i <;> simp [e0, e1]

/-! ### Parts 1c-1d -/

theorem marking : Marking := by
  intro ι Z _ _ P hg x hx z i
  exact mul_nonneg (hg z i).le (hx i)

variable {ι Z : Type} [Fintype ι] [Fintype Z]

lemma revSet_eq (P : Two ι Z) (c : ι → ℝ) (k : ℝ) : RevSet P c k = F1 P (c, k) := rfl

/-- Strict concavity at the midpoint. -/
lemma revObj_mid {P : Two ι Z} (hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i) {mu : ι → ℝ} {S : ι → ι → ℝ}
    (c x y : ι → ℝ) :
    (revObj P mu S c x + revObj P mu S c y) / 2 + P.gamma / 8 * quad S (x - y) ≤
      revObj P mu S c ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
  have hq := quad_comb S (1 / 2) x y
  have hc := cost_convex hr (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (x - c) (y - c)
  have e : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y - c = (1 / 2 : ℝ) • (x - c) + (1 / 2 : ℝ) • (y - c) := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have el : ∑ i, mu i * ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) i =
      (∑ i, mu i * x i + ∑ i, mu i * y i) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold revObj Qv
  rw [e]
  rw [show (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y by norm_num]
  rw [hq, el]
  nlinarith

theorem reviewFunding : ReviewFunding := by
  intro ι Z _ _ P hP c k hc hk
  have hr : ∀ i, 0 ≤ P.kp i ∧ 0 ≤ P.km i := fun i => ⟨(hP.2.2.2.2.2.2.2.2 i).1, (hP.2.2.2.2.2.2.2.2 i).2.1⟩
  have hne : (RevSet P c k).Nonempty := ⟨_, sell_feas hP hc hk⟩
  refine ⟨hne, fun mu S hS hpd => ?_⟩
  rw [revSet_eq] at hne ⊢
  obtain ⟨x, hx, hmax⟩ := (F1_compact P (c, k)).exists_isMaxOn hne
    (by unfold revObj Qv quad cost pc; fun_prop : Continuous (revObj P mu S c)).continuousOn
  refine ⟨x, ⟨hx, hmax⟩, fun y ⟨hy, hmy⟩ => ?_⟩
  by_contra hne'
  have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x ∈ F1 P (c, k) := by
    have := F1_comb hP hy hx (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1 / 2 : ℝ) • (c, k) + (1 / 2 : ℝ) • (c, k) = (c, k) by
      rw [← add_smul]; norm_num] at this
  have h1 := hmax hmid
  have h2 : revObj P mu S c y ≤ revObj P mu S c x := hmax hy
  have h3 : revObj P mu S c x ≤ revObj P mu S c y := hmy hx
  have hm := revObj_mid (mu := mu) (S := S) hr c y x
  have hq := hpd (y - x) (sub_ne_zero.mpr hne')
  have : 0 < P.gamma / 8 * quad S (y - x) := mul_pos (by linarith [hP.1]) hq
  simp only [Set.mem_ofPred_eq] at h1
  linarith

lemma hyp_toTwo {I : Inputs} {U : Setup} {T : Nodes Z} (h : FiniteLaw I U T) : Hyp (toTwo I U T) := by
  obtain ⟨hf, hA, hE, hl, ha, hγ, hβ, hβ1, hh, hq, hg, hr⟩ := h
  refine ⟨hγ, hβ, hβ1, hh, (sigP_psd I hf hA hE hl.le ha.le).1, fun z =>
    (sigP_psd I hf hA hE (postVar_nonneg hl hf) (postVar_nonneg ha hA.le)).1, hq, fun z i => ?_, hr⟩
  fin_cases i
  · exact (hg z).1
  · exact (hg z).2

theorem treeFunding : TreeFunding := by
  intro Z _ I U T h
  have hH := hyp_toTwo h
  obtain ⟨hf, hA, hE, hl, ha, -⟩ := h
  obtain ⟨hopt, -, -, -, hroot⟩ := structure_ (Fin 2) Z (toTwo I U T) hH
  exact ⟨hH, hopt, hroot, (sigP_psd I hf hA hE hl.le ha.le).2,
    (sigP_psd I hf hA hE (postVar_nonneg hl hf) (postVar_nonneg ha hA.le)).2⟩

/-! ### Part 3 -/

lemma spend_le {u xb kp km κ : ℝ} (hu : u ≤ xb) (hxb : 0 ≤ xb) (hkp : 0 ≤ kp) (hkm : 0 ≤ km)
    (hkm1 : km < 1) (hκ : kp ≤ κ) : u + pc kp km u ≤ (1 + κ) * xb := by
  unfold pc
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith
  · rw [max_eq_left h, max_eq_right (by linarith)]; nlinarith

theorem slackThreshold : SlackThreshold := by
  intro ι Z _ _ P hP κ hκ hth X hX0 hX1
  have hr := hP.2.2.2.2.2.2.2.2
  have hxb : ∀ i, 0 ≤ P.xbar i := fun i => by linarith [(hr i).2.2.2.1, (hr i).2.2.2.2]
  have s0 : ∑ i, ((X.1 i - P.xm i) + pc (P.kp i) (P.km i) (X.1 i - P.xm i)) ≤ (1 + κ) * ∑ i, P.xbar i := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => spend_le (by linarith [(hX0 i).2, (hr i).2.2.2.1]) (hxb i) (hr i).1
      (hr i).2.1 (hr i).2.2.1 (hκ i)
  have hh0 : h0 P X.1 = P.h - ∑ i, ((X.1 i - P.xm i) + pc (P.kp i) (P.km i) (X.1 i - P.xm i)) := by
    simp only [h0, cost, Pi.sub_apply, sum_add_distrib]; ring
  have hsum : 0 ≤ ∑ i, P.xbar i := sum_nonneg fun i _ => hxb i
  have hκ0 : 0 ≤ (1 + κ) * ∑ i, P.xbar i := by
    by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι; exact mul_nonneg (by linarith [(hr i).1, hκ i]) hsum
    · rw [show ∑ i, P.xbar i = 0 from sum_eq_zero fun i _ => (hι ⟨i⟩).elim, mul_zero]
  refine ⟨by rw [hh0]; linarith, fun z => ?_⟩
  have s1 : ∑ i, ((X.2 z i - carry P z X.1 i) + pc (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i)) ≤
      (1 + κ) * ∑ i, P.xbar i := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => spend_le (by
      have := mul_nonneg (hP.2.2.2.2.2.2.2.1 z i).le (hX0 i).1
      simp only [carry]; linarith [(hX1 z i).2]) (hxb i) (hr i).1 (hr i).2.1 (hr i).2.2.1 (hκ i)
  have hh1 : h1 P X.1 X.2 z = h0 P X.1 -
      ∑ i, ((X.2 z i - carry P z X.1 i) + pc (P.kp i) (P.km i) (X.2 z i - carry P z X.1 i)) := by
    simp only [h1, cost, Pi.sub_apply, sum_add_distrib]; ring
  rw [hh1, hh0]; linarith

/-! ### Part 2a: moments -/

section Moments

variable {Θ E : Type} [Fintype Θ] [Fintype E]

lemma inner_lin {v z : E → ℝ} (hv1 : ∑ e, v e = 1) (hvz : ∑ e, v e * z e = 0) (c d : ℝ) :
    ∑ e, v e * (c + d * z e) = c := by
  have : ∑ e, v e * (c + d * z e) = c * ∑ e, v e + d * ∑ e, v e * z e := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun e _ => by ring
  rw [this, hv1, hvz]; ring

lemma inner_sq {v z : E → ℝ} {s : ℝ} (hv1 : ∑ e, v e = 1) (hvz : ∑ e, v e * z e = 0)
    (hvs : ∑ e, v e * z e ^ 2 = s) (A B c d : ℝ) :
    ∑ e, v e * (A * (c + d * z e) ^ 2 + B) = A * (c ^ 2 + d ^ 2 * s) + B := by
  have : ∑ e, v e * (A * (c + d * z e) ^ 2 + B) =
      (A * c ^ 2 + B) * ∑ e, v e + 2 * A * c * d * ∑ e, v e * z e + A * d ^ 2 * ∑ e, v e * z e ^ 2 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [this, hv1, hvz, hvs]; ring

lemma outer_lin {w θ : Θ → ℝ} {m : ℝ} (hw1 : ∑ a, w a = 1) (hwθ : ∑ a, w a * θ a = m) (A B : ℝ) :
    ∑ a, w a * (A * (θ a - m) + B) = B := by
  have : ∑ a, w a * (A * (θ a - m) + B) = A * ∑ a, w a * θ a + (B - A * m) * ∑ a, w a := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  rw [this, hw1, hwθ]; ring

lemma outer_sq {w θ : Θ → ℝ} {m p : ℝ} (hw1 : ∑ a, w a = 1) (hwp : ∑ a, w a * (θ a - m) ^ 2 = p)
    (A B : ℝ) : ∑ a, w a * (A * (θ a - m) ^ 2 + B) = A * p + B := by
  have : ∑ a, w a * (A * (θ a - m) ^ 2 + B) = A * ∑ a, w a * (θ a - m) ^ 2 + B * ∑ a, w a := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring
  rw [this, hw1, hwp]; ring

lemma dsum (w : Θ → ℝ) (v : E → ℝ) (F : Θ → E → ℝ) :
    ∑ a, ∑ e, w a * v e * F a e = ∑ a, w a * ∑ e, v e * F a e :=
  sum_congr rfl fun a _ => by rw [mul_sum]; exact sum_congr rfl fun e _ => by ring

lemma tsum3 (w : Θ → ℝ) (v : E → ℝ) (F : Θ → E → E → ℝ) :
    ∑ a, ∑ e₁, ∑ e₂, w a * v e₁ * v e₂ * F a e₁ e₂ = ∑ a, w a * ∑ e₁, v e₁ * ∑ e₂, v e₂ * F a e₁ e₂ :=
  sum_congr rfl fun a _ => by
    rw [mul_sum]; exact sum_congr rfl fun e₁ _ => by
      rw [mul_sum, mul_sum]; exact sum_congr rfl fun e₂ _ => by ring

/-- The two-step variance identity: `(1 - k)² p + k² s = p_1`. -/
lemma err_var {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    (1 - gain p s) ^ 2 * p + gain p s ^ 2 * s = postVar p s := by
  have : p + s ≠ 0 := by positivity
  simp only [postVar, gain]; field_simp; ring

lemma innov_var {p s : ℝ} (hp : 0 < p) (hs : 0 < s) : gain p s ^ 2 * (p + s) = p - postVar p s := by
  have : p + s ≠ 0 := by positivity
  simp only [postVar, gain]; field_simp; ring

theorem moments : Moments := by
  intro Θ E _ _ w θ v z m p s hp hs ⟨_, hw1, hwθ, hwp, _, hv1, hvz, hvs⟩
  set k := gain p s with hk
  have hp1 : 0 < postVar p s := (beliefs p s hp hs).1
  set p1 := postVar p s with hp1d
  set k1 := gain p1 s with hk1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [dsum]
    rw [show ∑ a, w a * ∑ e, v e * (filt m p s (θ a + z e) - m) = ∑ a, w a * (k * (θ a - m) + 0) from
      sum_congr rfl fun a _ => by
        rw [← inner_lin hv1 hvz (k * (θ a - m) + 0) k]
        congr 1; exact sum_congr rfl fun e _ => by simp only [filt, ← hk]; ring]
    exact outer_lin hw1 hwθ k 0
  · rw [dsum]
    rw [show ∑ a, w a * ∑ e, v e * (filt m p s (θ a + z e) - m) ^ 2 =
        ∑ a, w a * (k ^ 2 * (θ a - m) ^ 2 + k ^ 2 * s) from sum_congr rfl fun a _ => by
      have := inner_sq hv1 hvz hvs 1 0 (k * (θ a - m)) k
      rw [show 1 * ((k * (θ a - m)) ^ 2 + k ^ 2 * s) + 0 = k ^ 2 * (θ a - m) ^ 2 + k ^ 2 * s by ring] at this
      rw [← this]; congr 1; exact sum_congr rfl fun e _ => by simp only [filt, ← hk]; ring]
    rw [outer_sq hw1 hwp, ← innov_var hp hs]; ring
  · rw [dsum]
    rw [show ∑ a, w a * ∑ e, v e * (θ a - filt m p s (θ a + z e)) ^ 2 =
        ∑ a, w a * ((1 - k) ^ 2 * (θ a - m) ^ 2 + k ^ 2 * s) from sum_congr rfl fun a _ => by
      have := inner_sq hv1 hvz hvs 1 0 ((1 - k) * (θ a - m)) (-k)
      rw [show 1 * (((1 - k) * (θ a - m)) ^ 2 + (-k) ^ 2 * s) + 0 =
        (1 - k) ^ 2 * (θ a - m) ^ 2 + k ^ 2 * s by ring] at this
      rw [← this]; congr 1; exact sum_congr rfl fun e _ => by simp only [filt, ← hk]; ring]
    rw [outer_sq hw1 hwp, hp1d, ← err_var hp hs]
  · rw [tsum3]
    rw [show ∑ a, w a * ∑ e₁, v e₁ * ∑ e₂, v e₂ *
        (filt (filt m p s (θ a + z e₁)) p1 s (θ a + z e₂) - filt m p s (θ a + z e₁)) =
        ∑ a, w a * (k1 * (1 - k) * (θ a - m) + 0) from sum_congr rfl fun a _ => by
      congr 1
      have hin : ∀ e₁, ∑ e₂, v e₂ * (filt (filt m p s (θ a + z e₁)) p1 s (θ a + z e₂) -
          filt m p s (θ a + z e₁)) = k1 * (θ a - filt m p s (θ a + z e₁)) + 0 := fun e₁ => by
        rw [← inner_lin hv1 hvz (k1 * (θ a - filt m p s (θ a + z e₁)) + 0) k1]
        exact sum_congr rfl fun e₂ _ => by simp only [filt, ← hk1]; ring
      simp only [hin]
      rw [← inner_lin hv1 hvz (k1 * (1 - k) * (θ a - m) + 0) (-(k1 * k))]
      exact sum_congr rfl fun e₁ _ => by simp only [filt, ← hk]; ring]
    exact outer_lin hw1 hwθ _ 0
  · rw [tsum3]
    rw [show ∑ a, w a * ∑ e₁, v e₁ * ∑ e₂, v e₂ *
        (filt (filt m p s (θ a + z e₁)) p1 s (θ a + z e₂) - filt m p s (θ a + z e₁)) ^ 2 =
        ∑ a, w a * (k1 ^ 2 * (1 - k) ^ 2 * (θ a - m) ^ 2 + (k1 ^ 2 * k ^ 2 * s + k1 ^ 2 * s)) from
      sum_congr rfl fun a _ => by
        congr 1
        have h2 := inner_sq hv1 hvz hvs (k1 ^ 2) (k1 ^ 2 * s) ((1 - k) * (θ a - m)) (-k)
        rw [show k1 ^ 2 * (((1 - k) * (θ a - m)) ^ 2 + (-k) ^ 2 * s) + k1 ^ 2 * s =
          k1 ^ 2 * (1 - k) ^ 2 * (θ a - m) ^ 2 + (k1 ^ 2 * k ^ 2 * s + k1 ^ 2 * s) by ring] at h2
        rw [← h2]
        refine sum_congr rfl fun e₁ _ => ?_
        congr 1
        have h1 := inner_sq hv1 hvz hvs 1 0 (k1 * (θ a - filt m p s (θ a + z e₁))) k1
        have e1 : 1 * ((k1 * (θ a - filt m p s (θ a + z e₁))) ^ 2 + k1 ^ 2 * s) + 0 =
            k1 ^ 2 * ((1 - k) * (θ a - m) + -k * z e₁) ^ 2 + k1 ^ 2 * s := by
          simp only [filt, ← hk]; ring
        rw [e1] at h1
        rw [← h1]
        exact sum_congr rfl fun e₂ _ => by simp only [filt, ← hk1]; ring]
    rw [outer_sq hw1 hwp]
    have hv := err_var hp hs
    have hi := innov_var hp1 hs
    rw [← hp1d] at hv
    rw [← hk] at hv; rw [← hk1] at hi
    linear_combination k1 ^ 2 * hv + hi

theorem crossMoment : CrossMoment := by
  intro Θ E Θ' E' _ _ _ _ w θ v z w' θ' v' z' m p s m' p' s' hp hs hp' hs' hL hL'
  have h1 := (moments Θ E w θ v z m p s hp hs hL).1
  have e : ∑ a, ∑ e, ∑ a', ∑ e', w a * v e * w' a' * v' e' *
      ((filt m p s (θ a + z e) - m) * (filt m' p' s' (θ' a' + z' e') - m')) =
      (∑ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m)) *
        ∑ a', ∑ e', w' a' * v' e' * (filt m' p' s' (θ' a' + z' e') - m') := by
    rw [sum_mul]; refine sum_congr rfl fun a _ => ?_
    rw [sum_mul]; refine sum_congr rfl fun e _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun a' _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun e' _ => by ring
  rw [e, h1, zero_mul]

end Moments

theorem tower : Tower := by
  intro Θ Y _ _ π θ w m hπ hw hm
  have e : ∀ y, (∑ a, π a y) * postMean π θ y = ∑ a, π a y * θ a := fun y => by
    unfold postMean
    by_cases h0 : ∑ a, π a y = 0
    · have hz : ∀ a, π a y = 0 := fun a =>
        (sum_eq_zero_iff_of_nonneg fun a _ => hπ a y).mp h0 a (mem_univ a)
      simp [hz]
    · field_simp
  rw [sum_congr rfl fun y _ => e y, sum_comm, ← hm]
  exact sum_congr rfl fun a _ => by rw [← sum_mul, hw]

theorem nonCoincidence : NonCoincidence := by
  intro E _ v z m d s y hd hs
  dsimp only
  intro heq hpos
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    rw [heq]
    rw [heq] at hpos
    field_simp [hpos.ne']
    ring
  · have hg : 0 < gain (d ^ 2) s := by unfold gain; positivity
    unfold filt
    intro h
    have : gain (d ^ 2) s * (y - m) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact hy (by linarith)

theorem redCounterexample : RedCounterexample := by
  unfold RedCounterexample
  intro θ w y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl <;>
    norm_num [θ, w, joint, filt, gain, Fintype.sum_bool]

theorem nodeA : NodeA := by
  unfold NodeA
  intro θ w z v
  refine ⟨⟨fun _ => by norm_num, ?_, ?_, ?_, fun _ => by norm_num, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    norm_num [θ, w, z, v, joint, filt, gain, Fintype.sum_bool, Fin.sum_univ_four]

theorem tableTwo : TableTwo := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · norm_num [gain, exInputs]
  · norm_num [gain, exInputs]
  · norm_num [postVar, gain, exInputs]
  · norm_num [postVar, gain, exInputs]
  · funext i; fin_cases i <;> norm_num [muP, exInputs]
  · funext i j; fin_cases i <;> fin_cases j <;> norm_num [SigP, exInputs]
  · have h0 := hx 0
    have h1 := hx 1
    simp only [SigP, muP, exInputs, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    norm_num at h0 h1
    have e0 : x 0 = 1447370 / 3567631 := by linarith
    have e1 : x 1 = 801992 / 3567631 := by linarith
    rw [e0, e1]
    norm_num [abs_lt]

theorem proof : Standalone.M8WorkedLearningExample.statement :=
  ⟨beliefs, predRisk, marking, reviewFunding, treeFunding, moments, crossMoment, tower, nonCoincidence,
    redCounterexample, nodeA, slackThreshold, tableTwo⟩

end

end Novel.M8WorkedLearningExampleProof

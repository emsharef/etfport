import Novel.M5LearningAimTwoSpeedsProof
import Standalone.M5WhenAnticipationMatters

/-!
# Claim 036: proof

The block's recursion is claim 032's with a general precision path. Its weights are positive and
sum to one by backward induction, so the learning factor, the renormalized weights and `M_t(φ)`
are convex-combination bounds. The rate comparisons are monotonicity of `X ↦ X/(λ + X)` along
the recursion, and the Lipschitz constant sums the one-step factors `λ/(λ + m)²`. The cost limits
follow `a_t → 0` as `λ_A → 0`.
-/

namespace Novel.M5WhenAnticipationMattersProof

open Filter Topology Standalone.M5PartialAdjustmentSplit Standalone.M5LearningAimTwoSpeeds
open Standalone.M5WhenAnticipationMatters Novel.M5LearningAimTwoSpeedsProof

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The block -/

section BlkLemmas

variable (B : Blk)

lemma a_lt {t : ℕ} (ht : t < B.T) : B.a t = B.lam - B.lam ^ 2 / B.d t := by
  rw [Blk.a, ite_eq_left ht]; rfl

lemma a_ge {t : ℕ} (ht : B.T ≤ t) : B.a t = 0 := by
  rw [Blk.a, ite_eq_right (by omega)]

variable {B} (hB : B.Setting)
include hB

lemma r_pos (t : ℕ) : 0 < B.r t := mul_pos hB.2.1 (by linarith [hB.2.2.1, hB.2.2.2.2.2 t])

lemma a_nonneg : ∀ t, 0 ≤ B.a t := by
  suffices h : ∀ k t, B.T - t = k → 0 ≤ B.a t from fun t => h _ t rfl
  intro k
  induction k with
  | zero => intro t ht; rw [a_ge B (by omega)]
  | succ k ih =>
    intro t ht
    have h1 := ih (t + 1) (by omega)
    have hl := hB.1
    have hd : B.lam ≤ B.d t := by
      rw [Blk.d]; nlinarith [r_pos hB t, mul_nonneg hB.2.2.2.1.le h1]
    rw [a_lt B (by omega), sub_nonneg, div_le_iff₀ (by linarith)]
    nlinarith

lemma dl_eq (t : ℕ) : B.d t - B.lam = B.r t + B.rho * B.a (t + 1) := by rw [Blk.d]; ring

lemma dl_pos (t : ℕ) : 0 < B.d t - B.lam := by
  rw [dl_eq hB]; nlinarith [r_pos hB t, mul_nonneg hB.2.2.2.1.le (a_nonneg hB (t + 1))]

lemma d_pos (t : ℕ) : 0 < B.d t := by linarith [dl_pos hB t, hB.1]

lemma a_pos {t : ℕ} (ht : t < B.T) : 0 < B.a t := by
  rw [a_lt B ht, sub_pos, div_lt_iff₀ (d_pos hB t)]
  nlinarith [dl_pos hB t, hB.1]

lemma w_nonneg : ∀ k t, 0 ≤ B.w k t := by
  intro k
  induction k with
  | zero => intro t; exact div_nonneg (r_pos hB t).le (dl_pos hB t).le
  | succ k ih =>
    intro t
    exact mul_nonneg (div_nonneg (mul_nonneg hB.2.2.2.1.le (a_nonneg hB _)) (dl_pos hB t).le) (ih _)

lemma w_pos : ∀ k t, k < B.T - t → 0 < B.w k t := by
  intro k
  induction k with
  | zero => intro t _; exact div_pos (r_pos hB t) (dl_pos hB t)
  | succ k ih =>
    intro t hk
    exact mul_pos (div_pos (mul_pos hB.2.2.2.1 (a_pos hB (by omega))) (dl_pos hB t)) (ih _ (by omega))

lemma w_sum : ∀ t, t < B.T → ∑ k ∈ Finset.range (B.T - t), B.w k t = 1 := by
  suffices h : ∀ n t, B.T - t = n + 1 → ∑ k ∈ Finset.range (B.T - t), B.w k t = 1 from
    fun t ht => h (B.T - t - 1) t (by omega)
  intro n
  induction n with
  | zero =>
    intro t ht
    rw [ht, Finset.sum_range_one, Blk.w, dl_eq hB, a_ge B (by omega), mul_zero, add_zero,
      div_self (r_pos hB t).ne']
  | succ n ih =>
    intro t ht
    rw [ht, Finset.sum_range_succ']
    simp only [Blk.w]
    rw [← Finset.mul_sum, show n + 1 = B.T - (t + 1) by omega, ih (t + 1) (by omega), mul_one]
    have h := dl_pos hB t
    rw [dl_eq hB] at h ⊢
    field_simp
    ring

lemma c_pos (s : ℕ) : 0 < B.sig2 / (B.sig2 + B.p s) :=
  div_pos hB.2.2.1 (by linarith [hB.2.2.1, hB.2.2.2.2.2 s])

lemma c_lt (s : ℕ) : B.sig2 / (B.sig2 + B.p s) < 1 := by
  rw [div_lt_one (by linarith [hB.2.2.1, hB.2.2.2.2.2 s])]; linarith [hB.2.2.2.2.2 s]

lemma ell_pos {t : ℕ} (ht : t < B.T) : 0 < B.ell t := by
  rw [Blk.ell, show B.T - t = (B.T - t - 1) + 1 by omega, Finset.sum_range_succ']
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ =>
    mul_nonneg (w_nonneg hB _ _) (c_pos hB _).le) (mul_pos (w_pos hB 0 t (by omega)) (c_pos hB _))

lemma ell_lt {t : ℕ} (ht : t < B.T) : B.ell t < 1 := by
  rw [← w_sum hB t ht, Blk.ell]
  refine Finset.sum_lt_sum (fun k _ => mul_le_of_le_one_right (w_nonneg hB _ _) (c_lt hB _).le)
    ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  exact mul_lt_of_lt_one_right (w_pos hB 0 t (by omega)) (c_lt hB _)

lemma ell_ge (hA : Antitone B.p) {t : ℕ} (ht : t < B.T) :
    B.sig2 / (B.sig2 + B.p t) ≤ B.ell t := by
  calc B.sig2 / (B.sig2 + B.p t) = ∑ k ∈ Finset.range (B.T - t), B.w k t * (B.sig2 / (B.sig2 + B.p t)) := by
        rw [← Finset.sum_mul, w_sum hB t ht, one_mul]
    _ ≤ B.ell t := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hB.2.2.1.le (by linarith [hB.2.2.1, hB.2.2.2.2.2 (t + k)])
          (by linarith [hA (Nat.le_add_right t k)])) (w_nonneg hB _ _)

end BlkLemmas

/-! ### Part 1 -/

theorem learningAim : LearningAim := by
  intro B hB hA t ht
  have hs := hB.2.2.1
  have hp := hB.2.2.2.2.2 t
  have hsp : 0 < B.sig2 + B.p t := by linarith
  have hk : 1 - B.kap t = B.sig2 / (B.sig2 + B.p t) := by rw [Blk.kap]; field_simp; ring
  have hodds : 1 + B.p t / B.sig2 = 1 / (1 - B.kap t) := by rw [hk]; field_simp
  have hL1 : 1 ≤ B.L t := by
    have := ell_ge hB hA ht
    rw [Blk.L]
    calc (1 : ℝ) = B.sig2 / (B.sig2 + B.p t) * ((B.sig2 + B.p t) / B.sig2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
  have hL2 : B.L t < 1 / (1 - B.kap t) := by
    rw [hk, one_div_div, Blk.L]
    calc B.ell t * ((B.sig2 + B.p t) / B.sig2) < 1 * ((B.sig2 + B.p t) / B.sig2) :=
          mul_lt_mul_of_pos_right (ell_lt hB ht) (by positivity)
      _ = _ := one_mul _
  have hexact : B.L t - 1 = ∑ k ∈ Finset.Ico 1 (B.T - t),
      B.w k t * ((B.p t - B.p (t + k)) / (B.sig2 + B.p (t + k))) := by
    have hfull : B.L t - 1 = ∑ k ∈ Finset.range (B.T - t),
        B.w k t * ((B.p t - B.p (t + k)) / (B.sig2 + B.p (t + k))) := by
      rw [Blk.L, Blk.ell, ← w_sum hB t ht, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : 0 < B.sig2 + B.p (t + k) := by linarith [hB.2.2.2.2.2 (t + k)]
      field_simp
      ring
    rw [hfull, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp
  refine ⟨fun ah => ?_, hL1, hL2, hodds, hexact, fun hS => ⟨fun h1 => ?_, fun h1 => ?_⟩,
    fun θ hθ hlt => ?_⟩
  · simp only [Blk.aimL, Blk.L, Blk.aimS]
    field_simp
  · by_contra hne
    have hlt : 1 < B.T - t := by omega
    have hpos : 0 < B.L t - 1 := by
      rw [hexact]
      refine Finset.sum_pos (fun k hk => ?_) ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩⟩
      have hk := Finset.mem_Ico.mp hk
      exact mul_pos (w_pos hB k t (by omega)) (div_pos (by linarith [hS (show t < t + k by omega)])
        (by linarith [hB.2.2.2.2.2 (t + k)]))
    linarith
  · have h := hexact
    rw [show B.T - t = 1 by omega] at h
    simp at h
    linarith
  · have hk0 : 0 < 1 - B.kap t := by rw [hk]; positivity
    have h2 : B.L t - 1 < B.kap t / (1 - B.kap t) := by
      have : 1 / (1 - B.kap t) = 1 + B.kap t / (1 - B.kap t) := by field_simp; ring
      linarith
    rw [lt_div_iff₀ hk0] at h2
    rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-! ### The link to claim 032 and the drift -/

theorem link : Link := by
  intro D hD t k
  have hB : (ofDir D).Setting :=
    ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2, fun u => dir_p_pos hD u⟩
  have ha : ∀ t, (ofDir D).a t = D.a t := by
    suffices h : ∀ n t, D.T - t = n → (ofDir D).a t = D.a t from fun t => h _ t rfl
    intro n
    induction n with
    | zero => intro t ht; rw [a_ge (ofDir D) (by simp [ofDir]; omega), dir_a_ge hD (by omega)]
    | succ n ih =>
      intro t ht
      have htT : t < D.T := by omega
      have e : D.a t = D.lam - D.lam ^ 2 / D.d t := by rw [Dir.a, dir_g_eq hD htT]; ring
      rw [a_lt (ofDir D) (by simpa [ofDir] using htT), Blk.d, Blk.r, ih (t + 1) (by omega), e]
      rfl
  have hd : ∀ t, (ofDir D).d t = D.d t := fun t => by
    rw [Blk.d, Blk.r, ha]; rfl
  have hw : ∀ k t, (ofDir D).w k t = D.w k t := by
    intro k
    induction k with
    | zero => intro t; simp only [Blk.w, Dir.w, hd, Blk.r]; rfl
    | succ k ih => intro t; simp only [Blk.w, Dir.w, hd, ha, ih]; rfl
  refine ⟨ha t, ?_, hw k t, ?_⟩
  · rw [Blk.g, ha, Dir.a]
    show D.lam * D.g t / D.lam = D.g t
    field_simp [hD.1.ne']
  · simp only [Blk.ell, Dir.ell, hw]; rfl

theorem drift : Drift := by
  intro B hB ah t
  have h1 : 0 < B.sig2 + B.p t := by linarith [hB.2.2.1, hB.2.2.2.2.2 t]
  have h2 : 0 < B.sig2 + B.p (t + 1) := by linarith [hB.2.2.1, hB.2.2.2.2.2 (t + 1)]
  have := hB.2.1
  simp only [Blk.aimS]
  field_simp

/-! ### Part 3 -/

theorem meanReversion : MeanReversion := by
  intro B hB t ht
  have he := ell_pos hB ht
  have hwt0 : ∀ k, 0 ≤ B.wt k t := fun k =>
    div_nonneg (mul_nonneg (w_nonneg hB _ _) (c_pos hB _).le) he.le
  have hsum : ∑ k ∈ Finset.range (B.T - t), B.wt k t = 1 := by
    simp only [Blk.wt]
    rw [← Finset.sum_div, ← Blk.ell, div_self he.ne']
  have hM1 : B.M t 1 = 1 := by simp only [Blk.M, one_pow, mul_one]; exact hsum
  have hn : B.T - t = (B.T - t - 1) + 1 := by omega
  refine ⟨fun abar ah phi => ?_, hwt0, hsum, hM1, fun a ha b hb hab => ?_, fun phi h0 h1 => ⟨?_, ?_⟩,
    ?_, fun hA => ?_⟩
  · have hg := hB.2.1
    have hs := hB.2.2.1
    have h1 : B.M t phi * B.ell t = ∑ k ∈ Finset.range (B.T - t),
        B.w k t * (B.sig2 / (B.sig2 + B.p (t + k))) * phi ^ k := by
      rw [Blk.M, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Blk.wt]; field_simp
    rw [show B.ell t * abar / (B.gam * B.sig2) + B.M t phi * (B.ell t * (ah - abar) / (B.gam * B.sig2)) =
      B.ell t * abar / (B.gam * B.sig2) + B.M t phi * B.ell t * (ah - abar) / (B.gam * B.sig2) by ring,
      h1, Blk.ell, Finset.sum_mul, Finset.sum_div, Finset.sum_mul, Finset.sum_div,
      ← Finset.sum_add_distrib, Blk.aimMR]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : 0 < B.sig2 + B.p (t + k) := by linarith [hB.2.2.2.2.2 (t + k)]
    field_simp
  · exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ha.1 hab k) (hwt0 k)
  · rw [Blk.M, hn, Finset.sum_range_succ', pow_zero, mul_one]
    have hrest : ∑ k ∈ Finset.range (B.T - t - 1), B.wt (k + 1) t = 1 - B.wt 0 t := by
      rw [hn, Finset.sum_range_succ'] at hsum; linarith
    have : (1 - B.wt 0 t) * phi ^ (B.T - 1 - t) ≤
        ∑ k ∈ Finset.range (B.T - t - 1), B.wt (k + 1) t * phi ^ (k + 1) := by
      rw [← hrest, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one h0 h1 (by simp at hk; omega)) (hwt0 _)
    linarith
  · rw [← hsum, Blk.M]
    exact Finset.sum_le_sum fun k _ => mul_le_of_le_one_right (hwt0 k) (pow_le_one₀ h0 h1)
  · rw [Blk.w, dl_eq hB]
  · have hc := ell_ge hB hA ht
    have hw0 := w_nonneg hB 0 t
    have : B.wt 0 t ≤ B.w 0 t := by
      rw [Blk.wt, add_zero, mul_div_assoc]
      exact mul_le_of_le_one_right hw0 ((div_le_one he).mpr hc)
    linarith

/-! ### Part 2 -/

section Rate

variable {lam rho : ℝ} (hl : 0 < lam) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
include hl hr0

lemma fmono {X X' : ℝ} (hX : 0 ≤ X) (h : X ≤ X') : X / (lam + X) ≤ X' / (lam + X') := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma fstrict {X X' : ℝ} (hX : 0 ≤ X) (h : X < X') : X / (lam + X) < X' / (lam + X') := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma cg_nonneg {r : ℝ} (hr : 0 ≤ r) : ∀ n, 0 ≤ cg lam rho r n
  | 0 => le_rfl
  | n + 1 => by
    have := cg_nonneg hr n
    simp only [cg]
    exact div_nonneg (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) this])
      (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) this])

lemma cg_mono {r r' : ℝ} (hr : 0 ≤ r) (h : r ≤ r') : ∀ n, cg lam rho r n ≤ cg lam rho r' n
  | 0 => le_rfl
  | n + 1 => by
    have ih := cg_mono hr h n
    have h0 := cg_nonneg hl hr0 hr n
    simp only [cg]
    rw [show lam + r + rho * lam * cg lam rho r n = lam + (r + rho * lam * cg lam rho r n) by ring,
      show lam + r' + rho * lam * cg lam rho r' n = lam + (r' + rho * lam * cg lam rho r' n) by ring]
    exact fmono hl hr0 (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) h0])
      (by nlinarith [mul_le_mul_of_nonneg_left ih (mul_nonneg hr0 hl.le)])

lemma cg_strict {r r' : ℝ} (hr : 0 ≤ r) (h : r < r') : ∀ n, 1 ≤ n → cg lam rho r n < cg lam rho r' n
  | 0, h0 => absurd h0 (by norm_num)
  | n + 1, _ => by
    have ih := cg_mono hl hr0 hr h.le n
    have h0 := cg_nonneg hl hr0 hr n
    simp only [cg]
    rw [show lam + r + rho * lam * cg lam rho r n = lam + (r + rho * lam * cg lam rho r n) by ring,
      show lam + r' + rho * lam * cg lam rho r' n = lam + (r' + rho * lam * cg lam rho r' n) by ring]
    exact fstrict hl hr0 (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) h0])
      (by nlinarith [mul_le_mul_of_nonneg_left ih (mul_nonneg hr0 hl.le)])

include hr1 in
lemma cg_lip {m r r' : ℝ} (hm : 0 ≤ m) (hr : m ≤ r) (hr' : m ≤ r') : ∀ n,
    |cg lam rho r n - cg lam rho r' n| ≤ n * (lam / (lam + m) ^ 2) * |r - r'|
  | 0 => by simp [cg]
  | n + 1 => by
    have ih := cg_lip hm hr hr' n
    have c0 := cg_nonneg hl hr0 (hm.trans hr) n
    have c0' := cg_nonneg hl hr0 (hm.trans hr') n
    set c := cg lam rho r n
    set c' := cg lam rho r' n
    set X := r + rho * lam * c
    set X' := r' + rho * lam * c'
    have hX : m ≤ X := by simp only [X]; nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) c0]
    have hX' : m ≤ X' := by simp only [X']; nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) c0']
    have hne : lam + X ≠ 0 := by linarith
    have hne' : lam + X' ≠ 0 := by linarith
    have e : cg lam rho r (n + 1) - cg lam rho r' (n + 1) = lam * (X - X') / ((lam + X) * (lam + X')) := by
      simp only [cg]
      rw [show lam + r + rho * lam * c = lam + X by simp only [X]; ring,
        show lam + r' + rho * lam * c' = lam + X' by simp only [X']; ring, div_sub_div _ _ hne hne']
      congr 1
      simp only [X, X']
      ring
    have hq : 0 < (lam + m) ^ 2 := by positivity
    have hden : (lam + m) ^ 2 ≤ (lam + X) * (lam + X') := by nlinarith
    have hXX : |X - X'| ≤ |r - r'| + rho * lam * |c - c'| := by
      have : X - X' = (r - r') + rho * lam * (c - c') := by simp only [X, X']; ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (mul_nonneg hr0 hl.le)]
    have hrl : rho * lam * lam / (lam + m) ^ 2 ≤ 1 := by
      rw [div_le_one hq]; nlinarith [mul_le_mul_of_nonneg_right hr1 (mul_nonneg hl.le hl.le)]
    rw [e, abs_div, abs_mul, abs_of_pos hl, abs_of_pos (mul_pos (by linarith) (by linarith) : 0 < (lam + X) * (lam + X'))]
    calc lam * |X - X'| / ((lam + X) * (lam + X')) ≤ lam * |X - X'| / (lam + m) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hq hden
      _ ≤ lam * (|r - r'| + rho * lam * |c - c'|) / (lam + m) ^ 2 := by gcongr
      _ = lam / (lam + m) ^ 2 * |r - r'| + (rho * lam * lam / (lam + m) ^ 2) * |c - c'| := by ring
      _ ≤ lam / (lam + m) ^ 2 * |r - r'| + 1 * (n * (lam / (lam + m) ^ 2) * |r - r'|) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * (lam / (lam + m) ^ 2) * |r - r'| := by push_cast; ring

end Rate

lemma g_rec {B : Blk} (hB : B.Setting) {t : ℕ} (ht : t < B.T) :
    B.g t = (B.r t + B.rho * B.lam * B.g (t + 1)) / (B.lam + (B.r t + B.rho * B.lam * B.g (t + 1))) := by
  have hl := hB.1
  have hd := d_pos hB t
  have e1 : B.a (t + 1) = B.lam * B.g (t + 1) := by rw [Blk.g]; field_simp
  rw [Blk.g, a_lt B ht]
  rw [Blk.d, e1] at hd ⊢
  set D := B.lam + B.r t + B.rho * (B.lam * B.g (t + 1)) with hDd
  rw [show B.lam + (B.r t + B.rho * B.lam * B.g (t + 1)) = D by rw [hDd]; ring,
    show B.r t + B.rho * B.lam * B.g (t + 1) = D - B.lam by rw [hDd]; ring]
  have hD : D ≠ 0 := hd.ne'
  field_simp

/-- The block's rate lies between the constant-risk rates at the smallest and largest risks ahead. -/
lemma g_between {B : Blk} (hB : B.Setting) {m R : ℝ} (hm : 0 ≤ m) : ∀ n t, B.T - t = n →
    (∀ s, t ≤ s → s < B.T → m ≤ B.r s ∧ B.r s ≤ R) →
    cg B.lam B.rho m n ≤ B.g t ∧ B.g t ≤ cg B.lam B.rho R n := by
  have hl := hB.1
  have hr0 := hB.2.2.2.1.le
  intro n
  induction n with
  | zero =>
    intro t ht _
    rw [Blk.g, a_ge B (by omega), zero_div]
    exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    intro t ht hrs
    have htT : t < B.T := by omega
    obtain ⟨i1, i2⟩ := ih (t + 1) (by omega) fun s h1 h2 => hrs s (by omega) h2
    obtain ⟨h1, h2⟩ := hrs t le_rfl htT
    have c0 := cg_nonneg hl hr0 hm n
    rw [g_rec hB htT]
    simp only [cg]
    constructor
    · rw [show B.lam + m + B.rho * B.lam * cg B.lam B.rho m n = B.lam + (m + B.rho * B.lam * cg B.lam B.rho m n) by ring]
      exact fmono hl hr0 (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) c0])
        (by nlinarith [mul_le_mul_of_nonneg_left i1 (mul_nonneg hr0 hl.le)])
    · rw [show B.lam + R + B.rho * B.lam * cg B.lam B.rho R n = B.lam + (R + B.rho * B.lam * cg B.lam B.rho R n) by ring]
      have g0 : 0 ≤ B.g (t + 1) := le_trans c0 i1
      exact fmono hl hr0 (by nlinarith [mul_nonneg (mul_nonneg hr0 hl.le) g0])
        (by nlinarith [mul_le_mul_of_nonneg_left i2 (mul_nonneg hr0 hl.le)])

theorem rateTrade : RateTrade := by
  intro B hB hA t ht
  have hl := hB.1
  have hr0 := hB.2.2.2.1.le
  have hr1 := hB.2.2.2.2.1
  have hg := hB.2.1
  have hs := hB.2.2.1
  have hm : 0 ≤ B.gam * B.sig2 := by positivity
  have hmr : ∀ s, B.gam * B.sig2 ≤ B.r s := fun s => by
    rw [Blk.r]; nlinarith [hB.2.2.2.2.2 s]
  have hrs : ∀ s, t ≤ s → B.r s ≤ B.r t := fun s h => by
    rw [Blk.r, Blk.r]; nlinarith [hA h]
  obtain ⟨lo, hi⟩ := g_between hB hm (B.T - t) t rfl fun s h1 _ => ⟨hmr s, hrs s h1⟩
  have hlip := fun n => cg_lip hl hr0 hr1 hm le_rfl (hmr t) n
  have hL := learningAim B hB hA t ht
  obtain ⟨haim, hL1, hL2, hodds, -, -, -⟩ := hL
  have hk : B.kap t < 1 := by
    rw [Blk.kap, div_lt_one (by linarith [hB.2.2.2.2.2 t])]; linarith
  have hkk : B.L t - 1 ≤ B.kap t / (1 - B.kap t) := by
    have : 1 / (1 - B.kap t) = 1 + B.kap t / (1 - B.kap t) := by
      field_simp [(sub_pos.mpr hk).ne']; ring
    linarith
  have hg0 : 0 ≤ B.g t := div_nonneg (a_nonneg hB t) hl.le
  have hgap : cg B.lam B.rho (B.r t) (B.T - t) - cg B.lam B.rho (B.gam * B.sig2) (B.T - t) ≤
      ((B.T - t : ℕ) : ℝ) * (B.lam / (B.lam + B.gam * B.sig2) ^ 2) * (B.gam * B.p t) := by
    have h := hlip (B.T - t)
    rw [abs_sub_comm, abs_sub_comm (B.gam * B.sig2) (B.r t),
      abs_of_nonneg (sub_nonneg.mpr (cg_mono hl hr0 hm (hmr t) _)),
      abs_of_nonneg (sub_nonneg.mpr (hmr t))] at h
    rw [show B.r t - B.gam * B.sig2 = B.gam * B.p t by rw [Blk.r]; ring] at h
    exact h
  refine ⟨lo, hi, fun n m r r' h0 h1 h2 => cg_lip hl hr0 hr1 h0 h1 h2 n,
    fun n r r' h0 h1 hn => cg_strict hl hr0 h0 h1 n hn, by linarith, fun ah x => ?_⟩
  have hid : B.g t * (B.aimL ah t - x) - cg B.lam B.rho (B.r t) (B.T - t) * (B.aimS ah t - x) =
      (B.g t - cg B.lam B.rho (B.r t) (B.T - t)) * (B.aimS ah t - x) +
        B.g t * (B.L t - 1) * B.aimS ah t := by rw [haim]; ring
  refine ⟨hid, ?_⟩
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonpos (by linarith)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  · rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkk hg0) (abs_nonneg _)

/-! ### Part 4(i): the zero-cost limits -/

section Zero

variable (B : Blk) (lam : ℝ)

@[simp] lemma bl_lam : (B.withLam lam).lam = lam := rfl
@[simp] lemma bl_gam : (B.withLam lam).gam = B.gam := rfl
@[simp] lemma bl_sig2 : (B.withLam lam).sig2 = B.sig2 := rfl
@[simp] lemma bl_rho : (B.withLam lam).rho = B.rho := rfl
@[simp] lemma bl_T : (B.withLam lam).T = B.T := rfl
@[simp] lemma bl_p : (B.withLam lam).p = B.p := rfl
@[simp] lemma bl_r : (B.withLam lam).r = B.r := rfl

lemma bl_a {t : ℕ} (ht : t < B.T) : (B.withLam lam).a t =
    lam - lam ^ 2 / (lam + B.r t + B.rho * (B.withLam lam).a (t + 1)) := by
  rw [a_lt (B.withLam lam) ht]; rfl

lemma bl_dl (t : ℕ) : (B.withLam lam).d t - (B.withLam lam).lam = B.r t + B.rho * (B.withLam lam).a (t + 1) := by
  simp only [Blk.d, bl_lam, bl_r, bl_rho]; ring

variable {B} (hB : B.Setting)
include hB

lemma zlim_a : ∀ t, Tendsto (fun lam => (B.withLam lam).a t) (𝓝[>] 0) (𝓝 0) := by
  suffices h : ∀ k t, B.T - t = k → Tendsto (fun lam => (B.withLam lam).a t) (𝓝[>] 0) (𝓝 0) from
    fun t => h _ t rfl
  have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  intro k
  induction k with
  | zero =>
    intro t ht
    simp only [a_ge (B.withLam _) (show (B.withLam _).T ≤ t by simp; omega)]
    exact tendsto_const_nhds
  | succ k ih =>
    intro t ht
    have htT : t < B.T := by omega
    have hd : Tendsto (fun lam => lam + B.r t + B.rho * (B.withLam lam).a (t + 1)) (𝓝[>] 0)
        (𝓝 (0 + B.r t + B.rho * 0)) :=
      (hid.add (tendsto_const_nhds (x := B.r t))).add ((tendsto_const_nhds (x := B.rho)).mul (ih (t + 1) (by omega)))
    have := hid.sub ((hid.pow 2).div hd (by rw [zero_add, mul_zero, add_zero]; exact (r_pos hB t).ne'))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at this
    exact this.congr fun lam => (bl_a B lam htT).symm

lemma zlim_w : ∀ k t, Tendsto (fun lam => (B.withLam lam).w k t) (𝓝[>] 0) (𝓝 (if k = 0 then 1 else 0)) := by
  intro k
  induction k with
  | zero =>
    intro t
    have hdl : Tendsto (fun lam => (B.withLam lam).d t - (B.withLam lam).lam) (𝓝[>] 0) (𝓝 (B.r t)) := by
      have := (tendsto_const_nhds (x := B.r t)).add ((tendsto_const_nhds (x := B.rho)).mul (zlim_a hB (t + 1)))
      rw [mul_zero, add_zero] at this
      exact this.congr fun lam => (bl_dl B lam t).symm
    have := (tendsto_const_nhds (x := B.r t)).div hdl (r_pos hB t).ne'
    rw [div_self (r_pos hB t).ne'] at this
    refine this.congr fun lam => ?_
    simp only [Pi.div_apply, Blk.w, bl_r]
  | succ k ih =>
    intro t
    have hdl : Tendsto (fun lam => (B.withLam lam).d t - (B.withLam lam).lam) (𝓝[>] 0) (𝓝 (B.r t)) := by
      have := (tendsto_const_nhds (x := B.r t)).add ((tendsto_const_nhds (x := B.rho)).mul (zlim_a hB (t + 1)))
      rw [mul_zero, add_zero] at this
      exact this.congr fun lam => (bl_dl B lam t).symm
    have := (((tendsto_const_nhds (x := B.rho)).mul (zlim_a hB (t + 1))).div hdl (r_pos hB t).ne').mul
      (ih (t + 1))
    rw [mul_zero, zero_div, zero_mul] at this
    simpa only [Blk.w, bl_rho, Nat.add_one_ne_zero, ite_false, Pi.div_apply] using this

lemma zlim_ell {t : ℕ} (ht : t < B.T) :
    Tendsto (fun lam => (B.withLam lam).ell t) (𝓝[>] 0) (𝓝 (B.sig2 / (B.sig2 + B.p t))) := by
  have := tendsto_finsetSum (Finset.range (B.T - t)) fun k _ =>
    (zlim_w hB k t).mul (tendsto_const_nhds (x := B.sig2 / (B.sig2 + B.p (t + k))))
  rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [ite_eq_right hb, zero_mul])
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h), ite_eq_left rfl, one_mul, add_zero] at this
  exact this

end Zero

theorem costEffect : CostEffect := by
  intro B hB t ht
  have hc := c_pos hB t
  have hE := zlim_ell hB ht
  refine ⟨by simpa using zlim_w hB 0 t, ?_, fun phi => ?_⟩
  · have := hE.mul_const ((B.sig2 + B.p t) / B.sig2)
    have hs := hB.2.2.1
    have hsp : 0 < B.sig2 + B.p t := by linarith [hB.2.2.2.2.2 t]
    rw [show B.sig2 / (B.sig2 + B.p t) * ((B.sig2 + B.p t) / B.sig2) = 1 by field_simp] at this
    exact this.congr fun lam => by simp [Blk.L]
  · have hwt : ∀ k, Tendsto (fun lam => (B.withLam lam).wt k t) (𝓝[>] 0)
        (𝓝 ((if k = 0 then 1 else 0) * (B.sig2 / (B.sig2 + B.p (t + k))) / (B.sig2 / (B.sig2 + B.p t)))) :=
      fun k => (((zlim_w hB k t).mul (tendsto_const_nhds (x := B.sig2 / (B.sig2 + B.p (t + k))))).div hE
        hc.ne').congr fun lam => by simp [Blk.wt]
    have := tendsto_finsetSum (Finset.range (B.T - t)) fun k _ => (hwt k).mul (tendsto_const_nhds (x := phi ^ k))
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [ite_eq_right hb, zero_mul, zero_div, zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h), ite_eq_left rfl, one_mul, add_zero,
      div_self hc.ne', pow_zero, mul_one] at this
    exact this.congr fun lam => by simp [Blk.M]

/-! ### The persistence lemma -/

section PersistProof

open Matrix Novel.M5PartialAdjustmentSplitProof

variable {ι π : Type} [Fintype ι] [DecidableEq ι] [Fintype π]
variable (Q : LQ ι π) (Phi : Matrix π π ℝ) (b : π → ℝ)

lemma ricP_fst : ∀ k, (ricP Q Phi b k).1 = (Q.ricK k).1
  | 0 => rfl
  | k + 1 => by simp only [ricP, LQ.ricK, ricP_fst k]

lemma AP_eq (t : ℕ) : (ricP Q Phi b (Q.T - t)).1 = Q.A t := ricP_fst Q Phi b _

lemma CP_ge {t : ℕ} (ht : Q.T ≤ t) : CP Q Phi b t = 0 := by
  simp [CP, Nat.sub_eq_zero_of_le ht, ricP]

lemma cP_ge {t : ℕ} (ht : Q.T ≤ t) : cP Q Phi b t = 0 := by
  simp [cP, Nat.sub_eq_zero_of_le ht, ricP]

lemma ricP_lt {t : ℕ} (ht : t < Q.T) :
    CP Q Phi b t = Q.Lam * (Q.D t)⁻¹ * (Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi)) ∧
    cP Q Phi b t = (Q.Lam * (Q.D t)⁻¹) *ᵥ (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e) := by
  have h1 : Q.T - t = (Q.T - (t + 1)) + 1 := by omega
  have h2 : Q.T - (Q.T - (t + 1) + 1) = t := by omega
  have hD : Q.Lam + Q.S t + Q.rho • (ricP Q Phi b (Q.T - (t + 1))).1 = Q.D t := by
    rw [AP_eq]; rfl
  simp only [CP, cP, h1, ricP, h2, hD]
  exact ⟨trivial, trivial⟩

/-- `q_t` under persistence, with `k` reviews left. -/
def qKP (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) : ℕ → (π → ℝ) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun m =>
    let t := Q.T - (k + 1)
    let v := (Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi)) *ᵥ m +
      (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e)
    (1 / 2) * (((Q.D t)⁻¹ *ᵥ v) ⬝ᵥ v) + Q.rho * E t (qKP E k) m

/-- `q_t` under persistence. -/
def qqP (E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)) (t : ℕ) : (π → ℝ) → ℝ := qKP Q Phi b E (Q.T - t)

lemma qqP_lt (E) {t : ℕ} (ht : t < Q.T) (m : π → ℝ) :
    qqP Q Phi b E t m = (1 / 2) * (((Q.D t)⁻¹ *ᵥ ((Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi)) *ᵥ m +
      (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e))) ⬝ᵥ
      ((Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi)) *ᵥ m +
      (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e))) +
      Q.rho * E t (qqP Q Phi b E (t + 1)) m := by
  have h1 : Q.T - t = (Q.T - (t + 1)) + 1 := by omega
  have h2 : Q.T - (Q.T - (t + 1) + 1) = t := by omega
  simp only [qqP, h1, qKP, h2]

/-- The expected continuation under affine mean dynamics. -/
lemma exp_JP {E : ℕ → ((π → ℝ) → ℝ) →ₗ[ℝ] ((π → ℝ) → ℝ)} (hE : AffineMean E Phi b)
    (q : ℕ → (π → ℝ) → ℝ) (t : ℕ) (x : ι → ℝ) (m : π → ℝ) :
    E t (fun m' => JP Q Phi b q (t + 1) x m') m =
      -(1 / 2) * (x ⬝ᵥ (Q.A (t + 1) *ᵥ x)) +
        x ⬝ᵥ ((CP Q Phi b (t + 1) * Phi) *ᵥ m + (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1))) +
        E t (q (t + 1)) m := by
  set a := -(1 / 2) * (x ⬝ᵥ (Q.A (t + 1) *ᵥ x)) + x ⬝ᵥ cP Q Phi b (t + 1)
  set w := x ᵥ* CP Q Phi b (t + 1)
  have hf : (fun m' => JP Q Phi b q (t + 1) x m') =
      (fun _ => a) + (∑ i, w i • (fun m' : π → ℝ => m' i)) + q (t + 1) := by
    funext m'
    simp only [JP, a, w, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      dotProduct_add, dotProduct_mulVec]
    simp only [dotProduct]
    ring
  rw [hf, map_add, map_add, map_sum]
  simp only [map_smul, hE.1, hE.2, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i, w i * ((Phi *ᵥ m) i + b i) = x ⬝ᵥ (CP Q Phi b (t + 1) *ᵥ (Phi *ᵥ m + b)) := by
    rw [dotProduct_mulVec]; simp only [w, dotProduct, Pi.add_apply]
  rw [e1, mulVec_add, ← mulVec_mulVec]
  simp only [a, dotProduct_add]
  ring

theorem persistence : Persistence := by
  intro ι π _ _ _ Q Phi b hS
  refine ⟨AP_eq Q Phi b, fun E hE => ⟨qqP Q Phi b E, fun m => by simp [qqP, qKP], fun t ht xm m => ?_⟩⟩
  have hA := (LQ.A_bounds hS (t + 1)).1
  set C' := CP Q Phi b (t + 1) * Phi
  set c' := CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)
  have hobj : ∀ x, objP Q Phi b E (qqP Q Phi b E) t xm m x =
      bellObj Q.Lam (Q.S t) (Q.A (t + 1)) (Q.G t) C' c' Q.e Q.rho
        (E t (qqP Q Phi b E (t + 1)) m) xm m x := fun x => by
    rw [objP, exp_JP Q Phi b hE, bellObj]
  have hpol : policyP Q Phi b t xm m = ((Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ * Q.Lam) *ᵥ xm +
      ((Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ * (Q.G t + Q.rho • C')) *ᵥ m +
      (Q.Lam + Q.S t + Q.rho • Q.A (t + 1))⁻¹ *ᵥ (Q.rho • c' - Q.e) := rfl
  obtain ⟨h1, h2⟩ := bellmanStep Q.Lam (Q.S t) (Q.A (t + 1)) (Q.G t) C' c' Q.e
    Q.rho (E t (qqP Q Phi b E (t + 1)) m) m hS.1 (hS.2.1 t) hA hS.2.2
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hobj, hobj, hpol]
    exact h1 xm x (by rw [← hpol]; exact hx)
  · rw [hobj, hpol, h2 xm]
    obtain ⟨eA, -, -⟩ := LQ.ric_lt Q ht
    obtain ⟨eC, ec⟩ := ricP_lt Q Phi b ht
    rw [JP, eA, eC, ec, qqP_lt Q Phi b E ht]
    rfl

/-- The aim's recursion: `aim_t = E'⁻¹(γΣ_t Markowitz_t + ρA_{t+1} aim_{t+1}(Φm + b))`. -/
lemma aimP_lt {t : ℕ} (ht : t < Q.T) (m : π → ℝ) :
    aimP Q Phi b t m = (Q.S t + Q.rho • Q.A (t + 1))⁻¹ *ᵥ
      (Q.S t *ᵥ Q.mkw t m + Q.rho • (Q.A (t + 1) *ᵥ aimP Q Phi b (t + 1) (Phi *ᵥ m + b))) := by
  rw [aimP, show Q.T - t = (Q.T - (t + 1)) + 1 by omega, Finset.sum_range_succ', aimP]
  simp only [LQ.W, fc, add_zero, mulVec_add, mulVec_smul, mulVec_sum, Finset.smul_sum]
  rw [add_comm]
  congr 1
  · rw [← mulVec_mulVec]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [show t + (d + 1) = t + 1 + d by ring]
    simp only [← mulVec_mulVec]
    rw [smul_mulVec, mulVec_smul]

lemma A_aimP (hS : Q.Setting) : ∀ s m, Q.A s *ᵥ aimP Q Phi b s m = CP Q Phi b s *ᵥ m + cP Q Phi b s := by
  suffices h : ∀ k s, Q.T - s = k → ∀ m, Q.A s *ᵥ aimP Q Phi b s m = CP Q Phi b s *ᵥ m + cP Q Phi b s from
    fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs m
    rw [LQ.A_ge Q (by omega), CP_ge Q Phi b (by omega), cP_ge Q Phi b (by omega)]
    simp
  | succ k ih =>
    intro s hs m
    have hsT : s < Q.T := by omega
    have hih := ih (s + 1) (by omega) (Phi *ᵥ m + b)
    have hE := LQ.E_pd hS (LQ.A_bounds hS (s + 1)).1
    set E' := Q.S s + Q.rho • Q.A (s + 1)
    have hEdet := pd_unit hE
    obtain ⟨eA, -, -⟩ := LQ.ric_lt Q hsT
    obtain ⟨eC, ec⟩ := ricP_lt Q Phi b hsT
    have hDE : Q.D s = Q.Lam + E' := LQ.D_split s
    have hDdet := pd_unit (LQ.D_pd hS s)
    have hA' : Q.A s = Q.Lam * (Q.D s)⁻¹ * E' := by
      rw [eA]
      have : E' = Q.D s - Q.Lam := by rw [hDE]; abel
      rw [this, Matrix.mul_sub, Matrix.mul_assoc Q.Lam _ (Q.D s), nonsing_inv_mul _ hDdet,
        Matrix.mul_one]
    have hSm : Q.S s *ᵥ Q.mkw s m = Q.G s *ᵥ m - Q.e := by
      simp only [LQ.mkw, mulVec_mulVec, mul_nonsing_inv _ (pd_unit (hS.2.1 s)), one_mulVec]
    have hc : ∀ w, (Q.Lam * (Q.D s)⁻¹ * E') *ᵥ (E'⁻¹ *ᵥ w) = (Q.Lam * (Q.D s)⁻¹) *ᵥ w := fun w => by
      rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hEdet, Matrix.mul_one]
    rw [hA', aimP_lt Q Phi b hsT, hc, hSm, hih, eC, ec, ← mulVec_mulVec m (Q.Lam * (Q.D s)⁻¹),
      ← mulVec_add]
    congr 1
    simp only [add_mulVec, smul_mulVec, smul_add, mulVec_add, ← mulVec_mulVec]
    abel

theorem persistAim : PersistAim := by
  intro ι π _ _ _ Q Phi b hS t ht xm m
  have hE := LQ.E_pd hS (LQ.A_bounds hS (t + 1)).1
  set E' := Q.S t + Q.rho • Q.A (t + 1)
  have hEdet := pd_unit hE
  have hDdet := pd_unit (LQ.D_pd hS t)
  have hDE : Q.D t = Q.Lam + E' := LQ.D_split t
  have hGam : Q.Gam t = (Q.D t)⁻¹ * E' := by
    have : E' = Q.D t - Q.Lam := by rw [hDE]; abel
    rw [this, Matrix.mul_sub, nonsing_inv_mul _ hDdet]
    rfl
  have hEaim : E' *ᵥ aimP Q Phi b t m = (Q.G t + Q.rho • (CP Q Phi b (t + 1) * Phi)) *ᵥ m +
      (Q.rho • (CP Q Phi b (t + 1) *ᵥ b + cP Q Phi b (t + 1)) - Q.e) := by
    have hSm : Q.S t *ᵥ Q.mkw t m = Q.G t *ᵥ m - Q.e := by
      simp only [LQ.mkw, mulVec_mulVec, mul_nonsing_inv _ (pd_unit (hS.2.1 t)), one_mulVec]
    rw [aimP_lt Q Phi b ht, mulVec_mulVec, mul_nonsing_inv _ hEdet, one_mulVec, A_aimP Q Phi b hS, hSm]
    simp only [add_mulVec, smul_mulVec, smul_add, mulVec_add, ← mulVec_mulVec]
    abel
  have hid : Q.Gam t = 1 - (Q.D t)⁻¹ * Q.Lam := rfl
  calc policyP Q Phi b t xm m
      = ((Q.D t)⁻¹ * Q.Lam) *ᵥ xm + (Q.D t)⁻¹ *ᵥ (E' *ᵥ aimP Q Phi b t m) := by
        rw [hEaim]
        simp only [policyP, LQ.K, ← mulVec_mulVec, mulVec_add, add_assoc]
    _ = xm + Q.Gam t *ᵥ (aimP Q Phi b t m - xm) := by
        rw [mulVec_mulVec, ← hGam, hid]
        simp only [sub_mulVec, one_mulVec, mulVec_sub]
        abel

end PersistProof

/-! ### The persistence lemma in the scalar block -/

section LinkScalar

open Matrix Novel.M5PartialAdjustmentSplitProof

lemma m11 (M N : Matrix (Fin 1) (Fin 1) ℝ) : (M * N) 0 0 = M 0 0 * N 0 0 := by simp [mul_apply]

lemma inv11 (M : Matrix (Fin 1) (Fin 1) ℝ) : M⁻¹ 0 0 = (M 0 0)⁻¹ := by
  rw [inv_def, adjugate_fin_one, det_unique, Ring.inverse_eq_inv']
  simp

variable {B : Blk} (hB : B.Setting)
include hB

lemma lq_A : ∀ s, B.lq.A s 0 0 = B.a s := by
  suffices h : ∀ k s, B.T - s = k → B.lq.A s 0 0 = B.a s from fun s => h _ s rfl
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [LQ.A_ge _ (show B.lq.T ≤ s by simp [Blk.lq]; omega), a_ge B (by omega)]
    rfl
  | succ k ih =>
    intro s hs
    have hsT : s < B.T := by omega
    obtain ⟨eA, -, -⟩ := LQ.ric_lt B.lq (show s < B.lq.T by simpa [Blk.lq] using hsT)
    have hD : B.lq.D s 0 0 = B.d s := by
      simp only [LQ.D, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ih (s + 1) (by omega)]
      simp [Blk.lq, Blk.d]
    rw [eA, Matrix.sub_apply, m11, m11, inv11, hD, a_lt B hsT]
    simp [Blk.lq]
    ring

lemma lq_W : ∀ d t, B.lq.W d t 0 0 = B.w d t := by
  have hE : ∀ t, (B.lq.S t + B.lq.rho • B.lq.A (t + 1)) 0 0 = B.d t - B.lam := fun t => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, lq_A hB, dl_eq hB]
    simp [Blk.lq]
  intro d
  induction d with
  | zero => intro t; rw [LQ.W, m11, inv11, hE, Blk.w]; simp [Blk.lq, div_eq_inv_mul]
  | succ d ih =>
    intro t
    rw [LQ.W, m11, m11, inv11, hE, ih, Blk.w, Matrix.smul_apply, lq_A hB]
    simp only [smul_eq_mul, Blk.lq]
    ring

lemma lq_mkw (s : ℕ) (m : Fin 1 → ℝ) : B.lq.mkw s m 0 = m 0 / B.r s := by
  simp [LQ.mkw, Blk.lq, mulVec, dotProduct, div_eq_inv_mul]

omit hB in
lemma fc_const (abar phi : ℝ) : ∀ d (ah : ℝ),
    fc (phi • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => (1 - phi) * abar) d (fun _ => ah) =
      fun _ => abar + phi ^ d * (ah - abar)
  | 0, ah => by funext i; simp [fc]
  | d + 1, ah => by
    have e : (phi • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ (fun _ => ah) + (fun _ => (1 - phi) * abar) =
        fun _ => phi * ah + (1 - phi) * abar := by
      funext i; simp [smul_mulVec]
    simp only [fc]
    rw [e, fc_const abar phi d]
    funext i
    ring

end LinkScalar

theorem persistLink : PersistLink := by
  intro B hB abar ah phi t ht
  simp only [aimP, Finset.sum_apply, Blk.aimMR]
  have hT : B.lq.T = B.T := rfl
  rw [hT]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [fc_const]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  rw [lq_W hB, lq_mkw hB, Blk.r]
  ring

/-! ### The claim -/

theorem proof : Standalone.M5WhenAnticipationMatters.statement :=
  ⟨link, learningAim, rateTrade, meanReversion, costEffect,
    Novel.M5PartialAdjustmentSplitProof.separation, drift, persistence, persistAim, persistLink⟩

end

end Novel.M5WhenAnticipationMattersProof

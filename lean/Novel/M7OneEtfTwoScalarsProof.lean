import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue
import Standalone.M7OneEtfTwoScalars

/-!
# Claim 110: proof

The one-fund problem is solved by a subgradient argument (`one_opt`). The Lagrangian at a fixed cash
price is maximized by a candidate built for each case of the status table, and a first-order bound
with a strong-concavity margin (`lag_bound`) makes it the unique maximizer. The cash price is the
exchange argument.
-/

namespace Novel.M7OneEtfTwoScalarsProof

open Standalone.M7OneEtfTwoScalars

noncomputable section

/-! ### The one-dimensional problem -/

section OneDim

/-- `max 0 (min x̄ (max lo (min hi x⁻)))`. -/
def clipB (lo hi xm xbar : ℝ) : ℝ := max 0 (min xbar (max lo (min hi xm)))

/-- The subgradient of the kinked cost at the clip, with the box signs of `a - c y* - t`. -/
lemma clip_sub {a c kp km xm xbar : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (h0 : 0 ≤ xm)
    (h1 : xm ≤ xbar) :
    let y := clipB ((a - kp) / c) ((a + km) / c) xm xbar
    ∃ t, -km ≤ t ∧ t ≤ kp ∧ (xm < y → t = kp) ∧ (y < xm → t = -km) ∧
      (y < xbar → a - c * y - t ≤ 0) ∧ (0 < y → 0 ≤ a - c * y - t) := by
  intro y
  have hlh : (a - kp) / c ≤ (a + km) / c := div_le_div_of_nonneg_right (by linarith) hc.le
  have elo : a - c * ((a - kp) / c) = kp := by field_simp; ring
  have ehi : a - c * ((a + km) / c) = -km := by field_simp; ring
  rcases le_total xm ((a - kp) / c) with hx | hx
  · -- u = lo
    have hu : max ((a - kp) / c) (min ((a + km) / c) xm) = (a - kp) / c :=
      max_eq_left ((min_le_right _ _).trans hx)
    simp only [y, clipB, hu]
    rcases le_total ((a - kp) / c) xbar with hb | hb
    · rw [min_eq_right hb, max_eq_right (h0.trans hx)]
      exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (not_lt.mpr hx), fun _ => by linarith,
        fun _ => by linarith⟩
    · rw [min_eq_left hb, max_eq_right (h0.trans h1)]
      have : a - c * xbar ≥ kp := by
        have := mul_le_mul_of_nonneg_left hb hc.le; linarith
      exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (not_lt.mpr h1),
        fun h => absurd h (lt_irrefl _), fun _ => by linarith⟩
  · rcases le_total xm ((a + km) / c) with hx2 | hx2
    · -- u = xm
      have hu : max ((a - kp) / c) (min ((a + km) / c) xm) = xm := by
        rw [min_eq_right hx2, max_eq_right hx]
      simp only [y, clipB, hu, min_eq_right h1, max_eq_right h0]
      have e1 : a - c * xm ≤ kp := by
        have := mul_le_mul_of_nonneg_left hx hc.le; linarith
      have e2 : -km ≤ a - c * xm := by
        have := mul_le_mul_of_nonneg_left hx2 hc.le; linarith
      exact ⟨a - c * xm, e2, e1, fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _),
        fun _ => by linarith, fun _ => by linarith⟩
    · -- u = hi
      have hu : max ((a - kp) / c) (min ((a + km) / c) xm) = (a + km) / c := by
        rw [min_eq_left hx2, max_eq_right hlh]
      simp only [y, clipB, hu, min_eq_right (hx2.trans h1)]
      rcases le_total 0 ((a + km) / c) with hb | hb
      · rw [max_eq_right hb]
        exact ⟨-km, le_rfl, by linarith, fun h => absurd h (not_lt.mpr hx2), fun _ => rfl,
          fun _ => by linarith, fun _ => by linarith⟩
      · rw [max_eq_left hb]
        have : a + km ≤ 0 := by
          have := mul_le_mul_of_nonneg_left hb hc.le; field_simp at this; linarith
        exact ⟨-km, le_rfl, by linarith, fun h => absurd h (not_lt.mpr h0), fun _ => rfl,
          fun _ => by linarith, fun h => absurd h (lt_irrefl _)⟩

/-- The subgradient inequality of the kinked cost. -/
lemma pc_sub {kp km xm y y' t : ℝ} (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (h1 : -km ≤ t) (h2 : t ≤ kp)
    (hp : xm < y → t = kp) (hm : y < xm → t = -km) :
    t * (y' - y) ≤ pc kp km (y' - xm) - pc kp km (y - xm) := by
  have l1 : kp * (y' - xm) ≤ pc kp km (y' - xm) := by
    simp only [pc]; nlinarith [le_max_left (y' - xm) 0, le_max_right (-(y' - xm)) 0]
  have l2 : km * (xm - y') ≤ pc kp km (y' - xm) := by
    simp only [pc]; nlinarith [le_max_left (-(y' - xm)) 0, le_max_right (y' - xm) 0]
  rcases lt_trichotomy xm y with h | h | h
  · have e : pc kp km (y - xm) = kp * (y - xm) := by
      simp only [pc, max_eq_left (by linarith : 0 ≤ y - xm), max_eq_right (by linarith : -(y - xm) ≤ 0)]; ring
    rw [hp h, e]; linarith
  · subst h
    have e : pc kp km (xm - xm) = 0 := by simp [pc]
    rw [e]
    rcases le_total xm y' with h' | h' <;> nlinarith
  · have e : pc kp km (y - xm) = km * (xm - y) := by
      simp only [pc, max_eq_right (by linarith : y - xm ≤ 0), max_eq_left (by linarith : 0 ≤ -(y - xm))]; ring
    rw [hm h, e]; linarith

/-- The one-dimensional problem `a y - (c/2) y² - pc(y - x⁻)` is maximized on `[0, x̄]` at the clip, with a
strong-concavity margin. -/
lemma one_opt {a c kp km xm xbar : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (h0 : 0 ≤ xm)
    (h1 : xm ≤ xbar) (y' : ℝ) (hy0 : 0 ≤ y') (hy1 : y' ≤ xbar) :
    let y := clipB ((a - kp) / c) ((a + km) / c) xm xbar
    a * y' - c / 2 * y' ^ 2 - pc kp km (y' - xm) + c / 2 * (y' - y) ^ 2 ≤
      a * y - c / 2 * y ^ 2 - pc kp km (y - xm) := by
  intro y
  obtain ⟨t, t1, t2, tp, tm, b1, b2⟩ := clip_sub (a := a) hc hkp hkm h0 h1
  have hs := pc_sub (y' := y') hkp hkm t1 t2 tp tm
  have hbox : (a - c * y - t) * (y' - y) ≤ 0 := by
    rcases lt_trichotomy y' y with h | h | h
    · have := b2 (lt_of_le_of_lt hy0 h); nlinarith
    · rw [h]; ring_nf; rfl
    · have := b1 (lt_of_lt_of_le h hy1); nlinarith
  nlinarith

lemma clipB_mem {lo hi xm xbar : ℝ} (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) :
    0 ≤ clipB lo hi xm xbar ∧ clipB lo hi xm xbar ≤ xbar :=
  ⟨le_max_left _ _, max_le (h0.trans h1) (min_le_left _ _)⟩

end OneDim

lemma clipB_mono {lo hi lo' hi' xm xbar : ℝ} (h1 : lo ≤ lo') (h2 : hi ≤ hi') :
    clipB lo hi xm xbar ≤ clipB lo' hi' xm xbar :=
  max_le_max_left _ (min_le_min_left _ (max_le_max h1 (min_le_min_right _ h2)))

lemma clipB_lip (lo hi xm xbar d : ℝ) :
    |clipB (lo + d) (hi + d) xm xbar - clipB lo hi xm xbar| ≤ |d| := by
  simp only [clipB]
  have a1 : |min (hi + d) xm - min hi xm| ≤ |d| := by
    have := abs_min_sub_min_le_max (hi + d) xm hi xm
    simp only [add_sub_cancel_left, sub_self, abs_zero] at this
    exact this.trans (max_le le_rfl (abs_nonneg _))
  have a2 : |max (lo + d) (min (hi + d) xm) - max lo (min hi xm)| ≤ |d| := by
    have := abs_max_sub_max_le_max (lo + d) (min (hi + d) xm) lo (min hi xm)
    simp only [add_sub_cancel_left] at this
    exact this.trans (max_le le_rfl a1)
  have a3 : |min xbar (max (lo + d) (min (hi + d) xm)) - min xbar (max lo (min hi xm))| ≤ |d| := by
    have := abs_min_sub_min_le_max xbar (max (lo + d) (min (hi + d) xm)) xbar (max lo (min hi xm))
    simp only [sub_self, abs_zero] at this
    exact this.trans (max_le (abs_nonneg _) a2)
  have := abs_max_sub_max_le_max 0 (min xbar (max (lo + d) (min (hi + d) xm))) 0
    (min xbar (max lo (min hi xm)))
  simp only [sub_self, abs_zero] at this
  exact this.trans (max_le (abs_nonneg _) a3)

/-- Above the incumbent iff the lower edge is above it and there is room. -/
lemma clipB_above {lo hi xm xbar : ℝ} (h0 : 0 ≤ xm) :
    xm < clipB lo hi xm xbar ↔ xm < lo ∧ xm < xbar := by
  simp only [clipB]
  rcases le_or_gt lo xm with h | h
  · have : max lo (min hi xm) ≤ xm := max_le h (min_le_right _ _)
    constructor
    · intro hc
      exfalso
      have : max 0 (min xbar (max lo (min hi xm))) ≤ xm :=
        max_le h0 ((min_le_right _ _).trans this)
      linarith
    · rintro ⟨h', -⟩; linarith
  · rw [max_eq_left ((min_le_right _ _).trans h.le)]
    constructor
    · intro hc
      refine ⟨h, ?_⟩
      by_contra hb; push Not at hb
      have : max 0 (min xbar lo) ≤ xm := max_le h0 ((min_le_left _ _).trans hb)
      linarith
    · rintro ⟨-, hb⟩
      exact lt_of_lt_of_le (lt_min hb h) (le_max_right _ _)

/-- Below the incumbent iff the upper edge is below it and it is positive. -/
lemma clipB_below {lo hi xm xbar : ℝ} (hlh : lo ≤ hi) (h0 : 0 ≤ xm) (h1 : xm ≤ xbar) :
    clipB lo hi xm xbar < xm ↔ hi < xm ∧ 0 < xm := by
  simp only [clipB]
  rcases le_or_gt xm hi with h | h
  · have : xm ≤ max lo (min hi xm) := by rw [min_eq_right h]; exact le_max_right _ _
    constructor
    · intro hc; exfalso
      have : xm ≤ max 0 (min xbar (max lo (min hi xm))) := (le_min h1 this).trans (le_max_right _ _)
      linarith
    · rintro ⟨h', -⟩; linarith
  · rw [min_eq_left h.le, max_eq_right hlh, min_eq_right (h.le.trans h1)]
    constructor
    · intro hc
      refine ⟨h, ?_⟩
      by_contra h0'; push Not at h0'
      have : xm = 0 := le_antisymm h0' h0
      rw [this] at hc; exact absurd (le_max_left 0 hi) (not_le.mpr hc)
    · rintro ⟨-, hp⟩
      exact max_lt hp h

/-! ### Part 1 -/

section Part1

variable {N : ℕ} {P : One N}

lemma xi_eq (m η : ℝ) (i : Fin N) :
    xi P m η i = clipB ((P.alt i + P.r i * m - η - (1 + η) * P.kp i) / (P.gamma * P.v i))
      ((P.alt i + P.r i * m - η + (1 + η) * P.km i) / (P.gamma * P.v i)) (P.xm i) (P.xbar i) := rfl

lemma pc_scale (s kp km u : ℝ) : pc (s * kp) (s * km) u = s * pc kp km u := by
  simp only [pc]; ring

lemma lohi (h : Hyp P) (m η : ℝ) (i : Fin N) (hη : 0 ≤ η) :
    (P.alt i + P.r i * m - η - (1 + η) * P.kp i) / (P.gamma * P.v i) ≤
      (P.alt i + P.r i * m - η + (1 + η) * P.km i) / (P.gamma * P.v i) := by
  obtain ⟨hv, hkp, hkm, -, -, -⟩ := h.2.2.2.2.2.2.2.2 i
  exact div_le_div_of_nonneg_right (by nlinarith) (mul_pos h.1 hv).le

lemma xi_mem (h : Hyp P) (m η : ℝ) (i : Fin N) : 0 ≤ xi P m η i ∧ xi P m η i ≤ P.xbar i := by
  obtain ⟨-, -, -, -, h0, h1⟩ := h.2.2.2.2.2.2.2.2 i
  exact clipB_mem h0 h1

/-- Fund `i`'s one-fund problem is maximized at its clip, with a strong-concavity margin. -/
lemma xi_opt (h : Hyp P) (m η : ℝ) (i : Fin N) (hη : 0 ≤ η) (y : ℝ) (hy0 : 0 ≤ y)
    (hy1 : y ≤ P.xbar i) :
    phi P m η i y + P.gamma * P.v i / 2 * (y - xi P m η i) ^ 2 ≤ phi P m η i (xi P m η i) := by
  obtain ⟨hv, hkp, hkm, -, h0, h1⟩ := h.2.2.2.2.2.2.2.2 i
  have h1η : 0 ≤ 1 + η := by linarith
  have := one_opt (a := P.alt i + P.r i * m - η) (mul_pos h.1 hv) (mul_nonneg h1η hkp)
    (mul_nonneg h1η hkm) h0 h1 y hy0 hy1
  simp only [phi, ← pc_scale]
  rw [xi_eq]
  linarith

theorem onePrice : OnePrice := by
  intro N P h
  have hγ := h.1; have hσ := h.2.1; have hsE := h.2.2.1
  have hvi : ∀ i, 0 < P.gamma * P.v i := fun i => mul_pos hγ (h.2.2.2.2.2.2.2.2 i).1
  have hB : ∀ m η, |qf P m η| ≤ ∑ i, |P.r i| * P.xbar i := fun m η => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (xi_mem h m η i).1]
    exact mul_le_mul_of_nonneg_left (xi_mem h m η i).2 (abs_nonneg _)
  have hxc : ∀ η i, Continuous fun m => xi P m η i := fun η i => by
    unfold xi; fun_prop
  have hqc : ∀ η, Continuous fun m => qf P m η := fun η => by
    unfold qf; exact continuous_finsetSum _ fun i _ => continuous_const.mul (hxc η i)
  have hxm : ∀ η i, Monotone fun m => P.r i * xi P m η i := fun η i m₁ m₂ hm => by
    simp only [xi_eq]
    rcases le_total 0 (P.r i) with hr | hr
    · refine mul_le_mul_of_nonneg_left (clipB_mono ?_ ?_) hr <;>
        exact div_le_div_of_nonneg_right (by nlinarith) (hvi i).le
    · refine mul_le_mul_of_nonpos_left (clipB_mono ?_ ?_) hr <;>
        exact div_le_div_of_nonneg_right (by nlinarith) (hvi i).le
  have hqm : ∀ η, Monotone fun m => qf P m η := fun η m₁ m₂ hm =>
    Finset.sum_le_sum fun i _ => hxm η i hm
  have hpc : ∀ η, Continuous fun m => pf P m η := fun η => by
    unfold pf; exact (continuous_const.sub continuous_id).div_const _ |>.sub (hqc η)
  have hpa : ∀ η, StrictAnti fun m => pf P m η := fun η m₁ m₂ hm => by
    simp only [pf]
    have := hqm η hm.le
    have : (P.muE - m₂) / (P.gamma * P.sEE) < (P.muE - m₁) / (P.gamma * P.sEE) :=
      div_lt_div_of_pos_right (by linarith) (mul_pos hγ hσ)
    linarith
  have hsurj : ∀ (f : ℝ → ℝ), Continuous f → ∀ (K A B : ℝ), 0 < K →
      (∀ m, |f m - (A - m / K)| ≤ B) → ∀ c, ∃ m, f m = c := by
    intro f hf K A B hK hb c
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb 0)
    set lo := K * (A - c - B) - 1
    set hi := K * (A - c + B) + 1
    have hlo := hb lo; have hhi := hb hi
    rw [abs_le] at hlo hhi
    have e1 : lo / K = A - c - B - 1 / K := by simp only [lo]; field_simp
    have e2 : hi / K = A - c + B + 1 / K := by simp only [hi]; field_simp
    have hK' : 0 < 1 / K := by positivity
    have flo : c ≤ f lo := by linarith
    have fhi : f hi ≤ c := by linarith
    have hlh : lo ≤ hi := by simp only [lo, hi]; nlinarith
    obtain ⟨m, -, hm⟩ := intermediate_value_Icc' hlh hf.continuousOn ⟨fhi, flo⟩
    exact ⟨m, hm⟩
  refine ⟨fun m η i hη => ⟨xi_mem h m η i, fun y hy0 hy1 => ?_, fun y hy0 hy1 hmax => ?_⟩,
    hxm, fun m i η₁ hη₁ η₂ hη₂ hη => ?_, fun η => ⟨hqc η, hqm η, fun m => hB m η⟩,
    fun η => ⟨hpc η, hpa η, fun c => ?_⟩, fun η => ⟨?_, fun c => ?_⟩⟩
  · have := xi_opt h m η i hη y hy0 hy1
    nlinarith [sq_nonneg (y - xi P m η i), hvi i]
  · have h1 := xi_opt h m η i hη y hy0 hy1
    have h2 := hmax _ (xi_mem h m η i).1 (xi_mem h m η i).2
    have : (y - xi P m η i) ^ 2 ≤ 0 := by nlinarith [hvi i]
    nlinarith [sq_nonneg (y - xi P m η i)]
  · obtain ⟨hv, hkp, hkm, hkm1, -, -⟩ := h.2.2.2.2.2.2.2.2 i
    simp only [xi_eq]
    refine clipB_mono ?_ ?_ <;> exact div_le_div_of_nonneg_right (by nlinarith) (hvi i).le
  · obtain ⟨m, hm⟩ := hsurj (fun m => pf P m η) (hpc η) (P.gamma * P.sEE)
      (P.muE / (P.gamma * P.sEE)) (∑ i, |P.r i| * P.xbar i) (mul_pos hγ hσ) (fun m => by
        simp only [pf]; rw [show (P.muE - m) / (P.gamma * P.sEE) - qf P m η -
          (P.muE / (P.gamma * P.sEE) - m / (P.gamma * P.sEE)) = -qf P m η by ring, abs_neg]
        exact hB m η) c
    exact ⟨m, hm, fun m' hm' => (hpa η).injective (hm'.trans hm.symm)⟩
  · intro m₁ m₂ hm
    simp only [eF]
    have := hpa η hm
    nlinarith [mul_nonneg hγ.le hsE]
  · have hmono : StrictMono fun m => eF P m η := fun m₁ m₂ hm => by
      simp only [eF]
      have := hpa η hm
      nlinarith [mul_nonneg hγ.le hsE]
    have hK : 0 < P.gamma * P.sEE / (P.gamma * P.sEE + P.gamma * P.sE) := by
      have : 0 < P.gamma * P.sEE + P.gamma * P.sE := by nlinarith [mul_nonneg hγ.le hsE, mul_pos hγ hσ]
      positivity
    obtain ⟨m, hm⟩ := hsurj (fun m => -eF P m η) (by unfold eF pf; fun_prop)
      (P.gamma * P.sEE / (P.gamma * P.sEE + P.gamma * P.sE))
      (P.gamma * P.sE * P.muE / (P.gamma * P.sEE)) (P.gamma * P.sE * ∑ i, |P.r i| * P.xbar i) hK
      (fun m => by
        have hq := hB m η
        have hsum : 0 < P.gamma * P.sEE + P.gamma * P.sE := by
          nlinarith [mul_nonneg hγ.le hsE, mul_pos hγ hσ]
        have e : -eF P m η - (P.gamma * P.sE * P.muE / (P.gamma * P.sEE) -
            m / (P.gamma * P.sEE / (P.gamma * P.sEE + P.gamma * P.sE))) = -(P.gamma * P.sE * qf P m η) := by
          simp only [eF, pf]; field_simp; ring
        rw [e, abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hγ.le hsE)]
        exact mul_le_mul_of_nonneg_left hq (mul_nonneg hγ.le hsE)) (-c)
    exact ⟨m, by linarith, fun m' hm' => hmono.injective (hm'.trans (by linarith))⟩

end Part1

/-! ### Part 4: readings -/

section Part4

variable {N : ℕ} {P : One N}

theorem readings : Readings := by
  intro N P h m η i hη
  obtain ⟨hv, hkp, hkm, hkm1, h0, h1⟩ := h.2.2.2.2.2.2.2.2 i
  have hc : 0 < P.gamma * P.v i := mul_pos h.1 hv
  have hlh := lohi h m η i hη
  refine ⟨?_, ?_, fun m' => ?_⟩
  · rw [xi_eq, clipB_above h0, lt_div_iff₀ hc]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩
  · rw [xi_eq, clipB_below hlh h0 h1, div_lt_iff₀ hc]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩
  · have e : ∀ k : ℝ, (P.alt i + P.r i * m' - η + k) / (P.gamma * P.v i) =
        (P.alt i + P.r i * m - η + k) / (P.gamma * P.v i) + P.r i * (m' - m) / (P.gamma * P.v i) :=
      fun k => by field_simp; ring
    have e1 := e (-((1 + η) * P.kp i)); have e2 := e ((1 + η) * P.km i)
    simp only [← sub_eq_add_neg] at e1
    rw [xi_eq, xi_eq, e1, e2]
    refine (clipB_lip _ _ _ _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_of_pos hc]; ring

end Part4

/-! ### Part 1's marginal identity -/

theorem marginal : Marginal := by
  intro N P x p i
  have hs : ∀ t, (∑ j, (P.alt j * Function.update x i t j - P.gamma * P.v j / 2 * Function.update x i t j ^ 2)) =
      (∑ j, (P.alt j * x j - P.gamma * P.v j / 2 * x j ^ 2)) +
        ((P.alt i * t - P.gamma * P.v i / 2 * t ^ 2) - (P.alt i * x i - P.gamma * P.v i / 2 * x i ^ 2)) := by
    intro t
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp
  have hw : ∀ t, wx P (Function.update x i t) p = wx P x p + P.r i * (t - x i) := by
    intro t
    simp only [wx]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp; ring
  have hl : HasDerivAt (fun t => wx P x p + P.r i * (t - x i)) (P.r i) (x i) := by
    have := HasDerivAt.const_add (c := wx P x p)
      (HasDerivAt.const_mul (P.r i) (HasDerivAt.sub_const (x i) (hasDerivAt_id' (x i))))
    simpa using this
  have ha : HasDerivAt (fun t => P.alt i * t - P.gamma * P.v i / 2 * t ^ 2)
      (P.alt i - P.gamma * P.v i / 2 * (2 * x i)) (x i) := by
    have := HasDerivAt.sub (HasDerivAt.const_mul (P.alt i) (hasDerivAt_id' (x i)))
      (HasDerivAt.const_mul (P.gamma * P.v i / 2) (hasDerivAt_pow 2 (x i)))
    exact this.congr_deriv (by push_cast; ring)
  set K := ∑ j, (P.alt j * x j - P.gamma * P.v j / 2 * x j ^ 2)
  set K2 := P.alt i * x i - P.gamma * P.v i / 2 * x i ^ 2
  have htot := HasDerivAt.sub (HasDerivAt.sub (HasDerivAt.add (HasDerivAt.const_add (c := K) (HasDerivAt.sub_const K2 ha))
    (HasDerivAt.const_mul P.muE hl)) (HasDerivAt.const_mul (P.gamma * P.sEE / 2) (HasDerivAt.pow (n := 2) hl)))
    (hasDerivAt_const (x i) (P.gamma * P.sE / 2 * p ^ 2))
  refine (htot.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp only [hs, hw]; rfl
  · simp only [mw, sub_self, mul_zero, add_zero]; ring

/-! ### The Lagrangian at a fixed cash price -/

section Lag

variable {N : ℕ} {P : One N}

/-- The Lagrangian split into the one-fund problems at any price `m`. -/
lemma lag_split (η m : ℝ) (x : Fin N → ℝ) (p : ℝ) :
    lag P η (x, p) = ∑ i, phi P m η i (x i) - m * ∑ i, P.r i * x i + P.muE * wx P x p -
      P.gamma * P.sEE / 2 * wx P x p ^ 2 - P.gamma * P.sE / 2 * p ^ 2 - η * p -
      (1 + η) * pc P.kpE P.kmE (p - P.pm) + η * (P.h + ∑ i, P.xm i + P.pm) := by
  have hphi : ∑ i, phi P m η i (x i) = ∑ i, (P.alt i * x i - P.gamma * P.v i / 2 * x i ^ 2) +
      m * ∑ i, P.r i * x i - η * ∑ i, x i - (1 + η) * costA P x := by
    have e : ∀ i, phi P m η i (x i) = (P.alt i * x i - P.gamma * P.v i / 2 * x i ^ 2) +
        m * (P.r i * x i) - η * x i - (1 + η) * pc (P.kp i) (P.km i) (x i - P.xm i) := fun i => by
      simp only [phi]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, costA]
  have hxm : ∑ i, (x i - P.xm i) = ∑ i, x i - ∑ i, P.xm i := Finset.sum_sub_distrib ..
  simp only [lag, Qobj, kb]
  rw [hphi, hxm]
  ring

/-- The ETF's line at `(m, p)` with slope `t_E`: the trade sign, and the box sign of
`g = m - γσ_E p - η - (1 + η) t_E` at `p ≥ 0`. -/
def ELine (P : One N) (η m p tE : ℝ) : Prop :=
  -P.kmE ≤ tE ∧ tE ≤ P.kpE ∧ (P.pm < p → tE = P.kpE) ∧ (p < P.pm → tE = -P.kmE) ∧
    m - P.gamma * P.sE * p - η - (1 + η) * tE ≤ 0 ∧ (0 < p → m - P.gamma * P.sE * p - η - (1 + η) * tE = 0)

/-- The first-order bound with the strong-concavity margin. -/
lemma lag_bound (h : Hyp P) {η : ℝ} (hη : 0 ≤ η) {x : Fin N → ℝ} {p tE : ℝ}
    (hx : ∀ i, x i = xi P (mw P (wx P x p)) η i) (hE : ELine P η (mw P (wx P x p)) p tE)
    (z : (Fin N → ℝ) × ℝ) (hz : z ∈ S P) :
    lag P η z + P.gamma / 2 * (∑ i, P.v i * (z.1 i - x i) ^ 2 + P.sEE * (wx P z.1 z.2 - wx P x p) ^ 2 +
      P.sE * (z.2 - p) ^ 2) ≤ lag P η (x, p) := by
  obtain ⟨x', p'⟩ := z
  obtain ⟨hx', hp'⟩ := hz
  simp only at hx' hp' ⊢
  set m := mw P (wx P x p)
  rw [lag_split η m x' p', lag_split η m x p]
  have hphi : ∀ i, phi P m η i (x' i) + P.gamma * P.v i / 2 * (x' i - x i) ^ 2 ≤ phi P m η i (x i) :=
    fun i => by rw [hx i]; exact xi_opt h m η i hη (x' i) (hx' i).1 (hx' i).2
  have hsum : ∑ i, phi P m η i (x' i) + P.gamma / 2 * ∑ i, P.v i * (x' i - x i) ^ 2 ≤
      ∑ i, phi P m η i (x i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by have := hphi i; linarith
  obtain ⟨t1, t2, tp, tm, g1, g2⟩ := hE
  have hk := h.2.2.2.2.1; have hk2 := h.2.2.2.2.2.1
  have hpc := pc_sub (y' := p') hk hk2 t1 t2 tp tm
  have hg : (m - P.gamma * P.sE * p - η - (1 + η) * tE) * (p' - p) ≤ 0 := by
    rcases lt_trichotomy p' p with hl | he | hg'
    · rw [g2 (lt_of_le_of_lt hp' hl)]; ring_nf; rfl
    · rw [he]; ring_nf; rfl
    · nlinarith
  have hw : wx P x' p' - wx P x p = (p' - p) + (∑ i, P.r i * x' i - ∑ i, P.r i * x i) := by
    simp only [wx]; ring
  have hm : m = P.muE - P.gamma * P.sEE * wx P x p := rfl
  have h1η : 0 ≤ 1 + η := by linarith
  have hpcE := mul_le_mul_of_nonneg_left hpc h1η
  have I1 : P.muE * wx P x' p' - P.gamma * P.sEE / 2 * wx P x' p' ^ 2 -
      (P.muE * wx P x p - P.gamma * P.sEE / 2 * wx P x p ^ 2) =
      m * ((p' - p) + (∑ i, P.r i * x' i - ∑ i, P.r i * x i)) -
        P.gamma * P.sEE / 2 * (wx P x' p' - wx P x p) ^ 2 := by
    rw [← hw, hm]; ring
  have I2 : -(P.gamma * P.sE / 2 * p' ^ 2) + P.gamma * P.sE / 2 * p ^ 2 =
      -(P.gamma * P.sE * p * (p' - p)) - P.gamma * P.sE / 2 * (p' - p) ^ 2 := by ring
  have I3 : (m - P.gamma * P.sE * p - η - (1 + η) * tE) * (p' - p) =
      m * (p' - p) - P.gamma * P.sE * p * (p' - p) - η * (p' - p) - (1 + η) * (tE * (p' - p)) := by ring
  have I4 : P.gamma / 2 * (∑ i, P.v i * (x' i - x i) ^ 2 + P.sEE * (wx P x' p' - wx P x p) ^ 2 +
      P.sE * (p' - p) ^ 2) = P.gamma / 2 * ∑ i, P.v i * (x' i - x i) ^ 2 +
        P.gamma * P.sEE / 2 * (wx P x' p' - wx P x p) ^ 2 + P.gamma * P.sE / 2 * (p' - p) ^ 2 := by ring
  have I5 : m * ((p' - p) + (∑ i, P.r i * x' i - ∑ i, P.r i * x i)) =
      m * (p' - p) + m * ∑ i, P.r i * x' i - m * ∑ i, P.r i * x i := by ring
  have I6 : (1 + η) * (pc P.kpE P.kmE (p' - P.pm) - pc P.kpE P.kmE (p - P.pm)) =
      (1 + η) * pc P.kpE P.kmE (p' - P.pm) - (1 + η) * pc P.kpE P.kmE (p - P.pm) := by ring
  linarith

/-- The candidate at a price `m`: every fund at its clip, the ETF at `p(m, η)`. -/
def cand (P : One N) (m η : ℝ) : (Fin N → ℝ) × ℝ := (fun i => xi P m η i, pf P m η)

lemma mw_cand (h : Hyp P) (m η : ℝ) : mw P (wx P (cand P m η).1 (cand P m η).2) = m := by
  simp only [cand, wx, pf, qf, mw]
  field_simp [h.1.ne', h.2.1.ne']
  ring

/-- A candidate with the ETF's line is the unique maximizer of the Lagrangian. -/
lemma cand_max (h : Hyp P) {η : ℝ} (hη : 0 ≤ η) {m tE : ℝ} (hp : 0 ≤ pf P m η)
    (hE : ELine P η m (pf P m η) tE) :
    cand P m η ∈ S P ∧ IsMaxOn (lag P η) (S P) (cand P m η) ∧
      ∀ z ∈ S P, IsMaxOn (lag P η) (S P) z → z = cand P m η := by
  have hm := mw_cand h m η
  have hx : ∀ i, (cand P m η).1 i = xi P (mw P (wx P (cand P m η).1 (cand P m η).2)) η i := fun i => by
    rw [hm]; rfl
  have hE' : ELine P η (mw P (wx P (cand P m η).1 (cand P m η).2)) (cand P m η).2 tE := by
    rw [hm]; exact hE
  have hS : cand P m η ∈ S P := ⟨fun i => xi_mem h m η i, hp⟩
  have hb := fun z hz => lag_bound h hη hx hE' z hz
  have hγ := h.1; have hσ := h.2.1; have hsE := h.2.2.1
  have hmarg : ∀ z : (Fin N → ℝ) × ℝ, 0 ≤ P.gamma / 2 * (∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 +
      P.sEE * (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2) ^ 2 +
      P.sE * (z.2 - (cand P m η).2) ^ 2) := fun z => by
    have : 0 ≤ ∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (h.2.2.2.2.2.2.2.2 i).1.le (sq_nonneg _)
    positivity
  refine ⟨hS, fun z hz => ?_, fun z hz hzmax => ?_⟩
  · have := hb z hz; have := hmarg z
    simp only [Set.mem_ofPred_eq]; linarith
  · have h1 := hb z hz
    have h2 := hzmax hS
    simp only [Set.mem_ofPred_eq] at h2
    have hz0 : P.gamma / 2 * (∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 +
        P.sEE * (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2) ^ 2 +
        P.sE * (z.2 - (cand P m η).2) ^ 2) ≤ 0 := by linarith
    have hs1 : ∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 = 0 := by
      have a : 0 ≤ ∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (h.2.2.2.2.2.2.2.2 i).1.le (sq_nonneg _)
      have b : 0 ≤ P.sEE * (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2) ^ 2 :=
        mul_nonneg hσ.le (sq_nonneg _)
      have c : 0 ≤ P.sE * (z.2 - (cand P m η).2) ^ 2 := mul_nonneg hsE (sq_nonneg _)
      have : ∑ i, P.v i * (z.1 i - (cand P m η).1 i) ^ 2 + P.sEE * (wx P z.1 z.2 -
          wx P (cand P m η).1 (cand P m η).2) ^ 2 + P.sE * (z.2 - (cand P m η).2) ^ 2 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith
    have hxe : ∀ i, z.1 i = (cand P m η).1 i := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (h.2.2.2.2.2.2.2.2 j).1.le (sq_nonneg (z.1 j - (cand P m η).1 j))).mp hs1 i
        (Finset.mem_univ _)
      have hv := (h.2.2.2.2.2.2.2.2 i).1
      have : (z.1 i - (cand P m η).1 i) ^ 2 = 0 := by
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hv.ne'
        · exact h0
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
    have hw : wx P z.1 z.2 = wx P (cand P m η).1 (cand P m η).2 := by
      have : P.sEE * (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2) ^ 2 ≤ 0 := by
        have c : 0 ≤ P.sE * (z.2 - (cand P m η).2) ^ 2 := mul_nonneg hsE (sq_nonneg _)
        nlinarith
      have : (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (wx P z.1 z.2 - wx P (cand P m η).1 (cand P m η).2)]
      linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this]
    have hx1 : z.1 = (cand P m η).1 := funext hxe
    have hp1 : z.2 = (cand P m η).2 := by
      simp only [wx, hx1] at hw; linarith
    exact Prod.ext hx1 hp1

lemma root_spec {f : ℝ → ℝ} {c : ℝ} (h : ∃ m, f m = c) : f (root f c) = c :=
  Classical.epsilon_spec h

theorem status : Status := by
  intro N P h η hη
  obtain ⟨-, -, -, -, hpf, heF⟩ := onePrice N P h
  obtain ⟨-, hpa, hpr⟩ := hpf η
  obtain ⟨hem, her⟩ := heF η
  have hkp := h.2.2.2.2.1; have hkm := h.2.2.2.2.2.1; have hpm := h.2.2.2.2.2.2.2.1
  have h1η : 0 < 1 + η := by linarith
  have hth : ths P η ≤ thb P η := by simp only [ths, thb]; nlinarith
  -- the roots
  have hm0 : pf P (m0 P η) η = 0 := root_spec (hpr 0).exists
  have hmI : pf P (mI P η) η = P.pm := root_spec (hpr P.pm).exists
  have hmb : eF P (mT P η (thb P η)) η = thb P η := root_spec (her _).exists
  have hms : eF P (mT P η (ths P η)) η = ths P η := root_spec (her _).exists
  have he0 : eF P (m0 P η) η = m0 P η := by simp only [eF, hm0, mul_zero, sub_zero]
  have heI : eF P (mI P η) η = mI P η - P.gamma * P.sE * P.pm := by simp only [eF, hmI]
  -- the ETF's line determines the regime
  -- a candidate with the ETF's line exists
  obtain ⟨mh, tE, hp0, hE⟩ : ∃ m tE, 0 ≤ pf P m η ∧ ELine P η m (pf P m η) tE := by
    rcases hpm.lt_or_eq with hpos | hzero
    · rcases lt_or_ge (thb P η) (eF P (mI P η) η) with hA | hA
      · -- bought
        refine ⟨mT P η (thb P η), P.kpE, ?_⟩
        have hlt : mT P η (thb P η) < mI P η := hem.lt_iff_lt.mp (by rw [hmb]; exact hA)
        have hp : P.pm < pf P (mT P η (thb P η)) η := by rw [← hmI]; exact hpa hlt
        refine ⟨by linarith, le_trans (by linarith) le_rfl |>.trans' (neg_nonpos.mpr hkm), le_rfl,
          fun _ => rfl, fun h' => absurd h' (not_lt.mpr hp.le), ?_, fun _ => ?_⟩
        · have := hmb; simp only [eF] at this; linarith [show thb P η = η + (1 + η) * P.kpE from rfl]
        · have := hmb; simp only [eF] at this; linarith [show thb P η = η + (1 + η) * P.kpE from rfl]
      · rcases le_or_gt (ths P η) (eF P (mI P η) η) with hB | hB
        · -- idle
          refine ⟨mI P η, (eF P (mI P η) η - η) / (1 + η), by rw [hmI]; exact hpm, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [le_div_iff₀ h1η]; simp only [ths] at hB; linarith
          · rw [div_le_iff₀ h1η]; simp only [thb] at hA; linarith
          · intro h'; rw [hmI] at h'; exact absurd h' (lt_irrefl _)
          · intro h'; rw [hmI] at h'; exact absurd h' (lt_irrefl _)
          · have : (1 + η) * ((eF P (mI P η) η - η) / (1 + η)) = eF P (mI P η) η - η := by field_simp
            simp only [eF] at this ⊢; linarith
          · intro _
            have : (1 + η) * ((eF P (mI P η) η - η) / (1 + η)) = eF P (mI P η) η - η := by field_simp
            simp only [eF] at this ⊢; linarith
        · rcases lt_or_ge (ths P η) (m0 P η) with hC | hC
          · -- sold, interior
            refine ⟨mT P η (ths P η), -P.kmE, ?_⟩
            have hgt : mI P η < mT P η (ths P η) := hem.lt_iff_lt.mp (by rw [hms]; exact hB)
            have hlt0 : mT P η (ths P η) < m0 P η := hem.lt_iff_lt.mp (by rw [hms, he0]; exact hC)
            have hp1 : pf P (mT P η (ths P η)) η < P.pm := by rw [← hmI]; exact hpa hgt
            have hp2 : 0 < pf P (mT P η (ths P η)) η := by rw [← hm0]; exact hpa hlt0
            refine ⟨hp2.le, le_rfl, by linarith, fun h' => absurd h' (not_lt.mpr hp1.le), fun _ => rfl, ?_,
              fun _ => ?_⟩
            · have := hms; simp only [eF] at this; linarith [show ths P η = η - (1 + η) * P.kmE from rfl]
            · have := hms; simp only [eF] at this; linarith [show ths P η = η - (1 + η) * P.kmE from rfl]
          · -- sold out
            refine ⟨m0 P η, -P.kmE, by rw [hm0], le_rfl, by linarith, fun h' => ?_, fun _ => rfl, ?_,
              fun h' => ?_⟩
            · rw [hm0] at h'; linarith
            · rw [hm0]; simp only [ths] at hC; linarith
            · rw [hm0] at h'; exact absurd h' (lt_irrefl _)
    · rcases le_or_gt (m0 P η) (thb P η) with hE' | hF
      · -- at zero
        refine ⟨m0 P η, P.kpE, by rw [hm0], by linarith, le_rfl, fun _ => rfl, fun h' => ?_, ?_,
          fun h' => ?_⟩
        · rw [hm0] at h'; linarith
        · rw [hm0]; simp only [thb] at hE'; linarith
        · rw [hm0] at h'; exact absurd h' (lt_irrefl _)
      · -- bought from zero
        refine ⟨mT P η (thb P η), P.kpE, ?_⟩
        have hlt : mT P η (thb P η) < m0 P η := hem.lt_iff_lt.mp (by rw [hmb, he0]; exact hF)
        have hp : 0 < pf P (mT P η (thb P η)) η := by rw [← hm0]; exact hpa hlt
        refine ⟨hp.le, by linarith, le_rfl, fun _ => rfl, fun h' => ?_, ?_, fun _ => ?_⟩
        · rw [← hzero] at h'; linarith
        · have := hmb; simp only [eF] at this; linarith [show thb P η = η + (1 + η) * P.kpE from rfl]
        · have := hmb; simp only [eF] at this; linarith [show thb P η = η + (1 + η) * P.kpE from rfl]
  obtain ⟨hmem, hmax, huniq⟩ := cand_max h hη hp0 hE
  refine ⟨⟨cand P mh η, ⟨hmem, hmax⟩, fun z hz => huniq z hz.1 hz.2⟩, fun z hz hzmax => ?_⟩
  obtain rfl := huniq z hz hzmax
  have hm' : mw P (wx P (cand P mh η).1 (cand P mh η).2) = mh := mw_cand h mh η
  dsimp only
  rw [hm']
  obtain ⟨t1, t2, tp, tm, g1, g2⟩ := hE
  have hc2 : (cand P mh η).2 = pf P mh η := rfl
  rw [hc2]
  set p := pf P mh η with hpdef
  set mb := mT P η (thb P η)
  set ms := mT P η (ths P η)
  have hg : mh - P.gamma * P.sE * p = eF P mh η := rfl
  rw [hg] at g1 g2
  have lt_e : ∀ {a b}, a < b → eF P a η < eF P b η := fun hab => hem hab
  have lt_p : ∀ {a b}, pf P b η < pf P a η → a < b := fun h' => (StrictAnti.lt_iff_gt hpa).mp h'
  -- the three regimes, read off the ETF's line
  have R1 : P.pm < p → mh = mb ∧ thb P η < eF P (mI P η) η := fun hp => by
    have e1 := tp hp
    have e2 := g2 (lt_of_le_of_lt hpm hp)
    have hb : eF P mh η = thb P η := by rw [e1] at e2; simp only [thb]; linarith
    have hlt : mh < mI P η := lt_p (by rw [hmI]; exact hp)
    exact ⟨hem.injective (hb.trans hmb.symm), hb ▸ lt_e hlt⟩
  have R2 : p = P.pm → 0 < P.pm → mh = mI P η ∧ ths P η ≤ eF P (mI P η) η ∧ eF P (mI P η) η ≤ thb P η :=
    fun hp hpos => by
      have hmi : mh = mI P η := hpa.injective (hp.trans hmI.symm)
      have e2 := g2 (hp ▸ hpos)
      rw [hmi] at e2
      refine ⟨hmi, ?_, ?_⟩ <;> simp only [ths, thb] <;> nlinarith
  have R3a : p < P.pm → eF P (mI P η) η < eF P mh η := fun hp => lt_e (lt_p (by rw [hmI]; exact hp))
  have R3b : p < P.pm → 0 < p → mh = ms ∧ eF P (mI P η) η < ths P η ∧ ths P η < m0 P η := fun hp hpos => by
    have e1 := tm hp
    have e2 := g2 hpos
    have hs : eF P mh η = ths P η := by rw [e1] at e2; simp only [ths]; linarith
    have hlt0 : mh < m0 P η := lt_p (by rw [hm0]; exact hpos)
    have h3 := lt_e hlt0
    rw [hs, he0] at h3
    exact ⟨hem.injective (hs.trans hms.symm), hs ▸ R3a hp, h3⟩
  have R3c : p < P.pm → p = 0 → mh = m0 P η ∧ m0 P η ≤ ths P η ∧ eF P (mI P η) η < ths P η :=
    fun hp h0 => by
      have e1 := tm hp
      have hm0' : mh = m0 P η := hpa.injective (h0.trans hm0.symm)
      have g1' := g1
      rw [e1, hm0', he0] at g1'
      have hle : m0 P η ≤ ths P η := by simp only [ths]; linarith
      have hI := R3a hp
      rw [hm0', he0] at hI
      exact ⟨hm0', hle, lt_of_lt_of_le hI hle⟩
  -- `p < p⁻` gives `e(m_I) < θ_s`
  have R3 : p < P.pm → eF P (mI P η) η < ths P η := fun hp => by
    rcases hp0.lt_or_eq with hp' | hp'
    · exact (R3b hp hp').2.1
    · exact (R3c hp hp'.symm).2.2
  refine ⟨fun i => rfl, rfl, fun hpos => ?_, fun hzero => ?_, fun hsE => ?_⟩
  · have hlt_of : eF P (mI P η) η < ths P η → p < P.pm := fun hC => by
      rcases lt_trichotomy p P.pm with hl | he | hg'
      · exact hl
      · linarith [(R2 he hpos).2.1]
      · linarith [(R1 hg').2]
    have hgt_of : thb P η < eF P (mI P η) η → P.pm < p := fun hA => by
      rcases lt_trichotomy p P.pm with hl | he | hg'
      · linarith [R3 hl]
      · linarith [(R2 he hpos).2.2]
      · exact hg'
    refine ⟨⟨⟨fun hp => (R1 hp).2, hgt_of⟩, fun hA => (R1 (hgt_of hA)).1⟩,
      ⟨⟨fun hp => (R2 hp hpos).2, fun hB => ?_⟩, fun hB1 hB2 => ?_⟩,
      ⟨⟨R3, hlt_of⟩, fun hC hC0 => ?_, fun hC hC0 => ?_⟩⟩
    · rcases lt_trichotomy p P.pm with hl | he | hg'
      · linarith [R3 hl, hB.1]
      · exact he
      · linarith [(R1 hg').2, hB.2]
    · rcases lt_trichotomy p P.pm with hl | he | hg'
      · linarith [R3 hl]
      · exact (R2 he hpos).1
      · linarith [(R1 hg').2]
    · have hl := hlt_of hC
      rcases hp0.lt_or_eq with hp' | hp'
      · exact ⟨(R3b hl hp').1, hp'⟩
      · linarith [(R3c hl hp'.symm).2.1]
    · have hl := hlt_of hC
      rcases hp0.lt_or_eq with hp' | hp'
      · linarith [(R3b hl hp').2.2]
      · exact ⟨(R3c hl hp'.symm).1, hp'.symm⟩
  · -- `p⁻ = 0`
    have key0 : p = 0 → mh = m0 P η ∧ m0 P η ≤ thb P η := fun h0 => by
      have hm0' : mh = m0 P η := hpa.injective (h0.trans hm0.symm)
      have g1' := g1
      rw [hm0', he0] at g1'
      refine ⟨hm0', ?_⟩
      simp only [thb]; nlinarith
    have keyp : 0 < p → mh = mb ∧ thb P η < m0 P η := fun hpos => by
      have e1 := tp (by rw [hzero]; exact hpos)
      have e2 := g2 hpos
      have hb : eF P mh η = thb P η := by rw [e1] at e2; simp only [thb]; linarith
      have hlt0 : mh < m0 P η := lt_p (by rw [hm0]; exact hpos)
      have h3 := lt_e hlt0
      rw [hb, he0] at h3
      exact ⟨hem.injective (hb.trans hmb.symm), h3⟩
    refine ⟨⟨fun h0 => (key0 h0).2, fun hle => ?_⟩, fun hle => ?_, fun hlt => ?_⟩
    · by_contra hn
      linarith [(keyp (lt_of_le_of_ne hp0 (Ne.symm hn))).2]
    · by_cases h0 : p = 0
      · exact (key0 h0).1
      · linarith [(keyp (lt_of_le_of_ne hp0 (Ne.symm h0))).2]
    · by_cases h0 : p = 0
      · linarith [(key0 h0).2]
      · exact ⟨(keyp (lt_of_le_of_ne hp0 (Ne.symm h0))).1, lt_of_le_of_ne hp0 (Ne.symm h0)⟩
  · have hid : ∀ m', eF P m' η = m' := fun m' => by simp [eF, hsE]
    refine ⟨?_, ?_, hid⟩
    · have := hmb; rw [hid] at this; exact this
    · have := hms; rw [hid] at this; exact this
end Lag


/-! ### Part 3: the cash price -/

section Part3

variable {N : ℕ} {P : One N}

lemma zOpt_spec (h : Hyp P) {η : ℝ} (hη : 0 ≤ η) :
    zOpt P η ∈ S P ∧ IsMaxOn (lag P η) (S P) (zOpt P η) := by
  obtain ⟨⟨z, hz, -⟩, -⟩ := status _ P h η hη
  exact Classical.epsilon_spec (p := fun z => z ∈ S P ∧ IsMaxOn (lag P η) (S P) z) ⟨z, hz⟩

lemma lag_eq (η : ℝ) (z : (Fin N → ℝ) × ℝ) : lag P η z = Qobj P z.1 z.2 + η * kb P z.1 z.2 := rfl

theorem cashPrice : CashPrice := by
  intro N P h
  have hS := fun η (hη : 0 ≤ η) => zOpt_spec h hη
  refine ⟨fun η₁ hη₁ η₂ hη₂ hle => ?_, fun hk => ⟨(hS 0 le_rfl).1, fun y hy => ?_⟩,
    fun η hη hk => ⟨(hS η hη.le).1, fun y hy => ?_, fun z hz hkz hzmax => ?_⟩⟩
  · rcases hle.lt_or_eq with hlt | heq
    · have h1 := (hS η₁ hη₁).2 (hS η₂ hη₂).1
      have h2 := (hS η₂ hη₂).2 (hS η₁ hη₁).1
      simp only [Set.mem_ofPred_eq, lag_eq] at h1 h2
      simp only
      nlinarith
    · rw [heq]
  · have := (hS 0 le_rfl).2 hy.1
    simp only [Set.mem_ofPred_eq, lag_eq, zero_mul, add_zero] at this ⊢
    exact this
  · have := (hS η hη.le).2 hy.1
    simp only [Set.mem_ofPred_eq, lag_eq, hk, mul_zero, add_zero] at this ⊢
    nlinarith [mul_nonneg hη.le hy.2]
  · -- a constrained maximizer maximizes the Lagrangian, so it is the Lagrangian's maximizer
    have hzη : zOpt P η ∈ {z | z ∈ S P ∧ 0 ≤ kb P z.1 z.2} := ⟨(hS η hη.le).1, hk.symm ▸ le_rfl⟩
    have hQ := hzmax hzη
    simp only [Set.mem_ofPred_eq] at hQ
    have hlagmax : IsMaxOn (lag P η) (S P) z := fun y hy => by
      have := (hS η hη.le).2 hy
      simp only [Set.mem_ofPred_eq, lag_eq] at this ⊢
      rw [hk, mul_zero, add_zero] at this
      nlinarith [mul_nonneg hη.le hkz]
    obtain ⟨-, huniq⟩ := status _ P h η hη.le
    obtain ⟨⟨w, hw, hwu⟩, -⟩ := status _ P h η hη.le
    exact (hwu z ⟨hz, hlagmax⟩).trans (hwu _ ⟨(hS η hη.le).1, (hS η hη.le).2⟩).symm

end Part3

theorem proof : Standalone.M7OneEtfTwoScalars.statement :=
  ⟨onePrice, marginal, status, cashPrice, readings⟩

end

end Novel.M7OneEtfTwoScalarsProof

import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Standalone.M2NoActiveTradeBand

/-!
# Proof of claim 009: the M2 no-active-trade band after ETF optimization

The family criterion is `Q_x(w) = μ(x)'w - (γ/2) w'Σw - τ(w - w⁻)` (belief averaging), so the
exact expansion `Q_x(z) - Q_x(w) = g'(z - w) - (γ/2)(z - w)'Σ(z - w) - [τ(z - w⁻) - τ(w - w⁻)]`
holds with `g = μ(x) - γ Σ w`.

* Sufficiency is the certificate inequality (as in claim 007): a multiplier `η` with cash
  complementarity, a cost subgradient `t`, and position-sign conditions on the residual
  `g - η - (1 + η) t` give global optimality.
* Necessity is proved by explicit feasible moves rather than by the paper's finite-cone argument.
  Along a direction `d`, the piecewise-linear cost is exactly linear for small steps; if the
  one-sided derivative `g'd - c'd` is positive and the step is funded and within bounds, a small
  step strictly improves the criterion. The moves used are: buy an ETF from slack cash, sell an
  ETF into cash, swap one ETF for another (for `I`); and buy the active fund from cash or from an
  ETF sale, sell it into cash or into an ETF (for the band). This establishes the same necessary
  conditions without any constraint qualification.
-/

namespace Novel.M2NoActiveTradeBandProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M2ActionClasses
  Standalone.M2NoActiveTradeBand

variable {n K : ℕ} {S : Type} [Fintype S] {T : Type} [Fintype T]

/-! ### The family criterion -/

/-- The mean vector `μ(x)`. -/
noncomputable def meanVec (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (x : ℝ) :
    Inst 1 n → ℝ :=
  Sum.elim (fun _ => (D.BA *ᵥ lamBar par pi) 0 + x) (fun j => (D.BE *ᵥ lamBar par pi) j - D.cE j)

/-- The smooth marginal `g = μ(x) - γ Σ w`. -/
noncomputable def gv (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (x : ℝ)
    (w : Inst 1 n → ℝ) : Inst 1 n → ℝ :=
  meanVec D par pi x - D.gamma • (covariance D *ᵥ w)

omit [Fintype S] in
lemma sum_inst (f : Inst 1 n → ℝ) : ∑ i, f i = f (Sum.inl 0) + ∑ j, f (Sum.inr j) := by
  simp [Fintype.sum_sum_type]

lemma dot_wsum {ι : Type} [Fintype ι] (e : ι → ℝ) (pi : T → ℝ) (l : T → ι → ℝ) :
    e ⬝ᵥ (∑ t, pi t • l t) = ∑ t, pi t * (e ⬝ᵥ l t) := by
  rw [dotProduct_sum]
  exact sum_congr rfl fun t _ => by rw [dotProduct_smul, smul_eq_mul]

lemma Qx_eq (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (x : ℝ) (w : Inst 1 n → ℝ) :
    Qx D par pi x w = meanVec D par pi x ⬝ᵥ w - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w))
      - tau D (w - w0 D) := by
  have hmean : meanVec D par pi x ⬝ᵥ w
      = exposure D w ⬝ᵥ lamBar par pi + w (Sum.inl 0) * x - etf w ⬝ᵥ D.cE := by
    rw [exposure, add_dotProduct, mulVec_transpose, mulVec_transpose, ← dotProduct_mulVec,
      ← dotProduct_mulVec]
    simp only [meanVec, dotProduct, sum_inst, Sum.elim_inl, Sum.elim_inr, active, etf,
      Fin.sum_univ_one]
    have e : ∑ j, ((D.BE *ᵥ lamBar par pi) j - D.cE j) * w (Sum.inr j)
        = ∑ j, w (Sum.inr j) * (D.BE *ᵥ lamBar par pi) j - ∑ j, w (Sum.inr j) * D.cE j := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [e]
    ring
  have hlam : ∑ h, pi h * (exposure D w ⬝ᵥ (par h).lam) = exposure D w ⬝ᵥ lamBar par pi := by
    rw [lamBar, beliefMean, dot_wsum]
  have hab : ∑ h, pi h * (par h).alpha 0 = abar0 par pi := rfl
  rw [hmean]
  simp only [Qx, beliefScore, score, famPar]
  have : ∀ h, pi h * (exposure D w ⬝ᵥ (par h).lam
        + active w ⬝ᵥ (fun _ => (par h).alpha 0 - abar0 par pi + x) - etf w ⬝ᵥ D.cE
        - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D))
      = pi h * (exposure D w ⬝ᵥ (par h).lam) + w (Sum.inl 0) * (pi h * (par h).alpha 0)
        + pi h * (w (Sum.inl 0) * (x - abar0 par pi) - etf w ⬝ᵥ D.cE
          - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D)) := by
    intro h
    simp only [dotProduct, Fin.sum_univ_one, active]
    ring
  simp only [this, sum_add_distrib, ← mul_sum, ← sum_mul, hlam, hab, hpi]
  ring

lemma Qx_shift (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (x y : ℝ) (w : Inst 1 n → ℝ) :
    Qx D par pi x w = Qx D par pi y w + (x - y) * w (Sum.inl 0) := by
  rw [Qx_eq D par pi hpi, Qx_eq D par pi hpi]
  simp only [meanVec, dotProduct, sum_inst, Sum.elim_inl, Sum.elim_inr]
  ring

/-! ### Covariance facts -/

lemma quad_eq (D : Data 1 n K S) (w : Inst 1 n → ℝ) :
    w ⬝ᵥ (covariance D *ᵥ w) = ∑ s, D.q s * (w ⬝ᵥ xi D s) ^ 2 := by
  symm
  calc ∑ s, D.q s * (w ⬝ᵥ xi D s) ^ 2
      = ∑ s, ∑ i, ∑ j, D.q s * (w i * xi D s i * (w j * xi D s j)) := by
        simp only [dotProduct, sq]
        simp only [Finset.sum_mul_sum]
        simp only [mul_sum]
    _ = ∑ i, ∑ j, ∑ s, D.q s * (w i * xi D s i * (w j * xi D s j)) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ = w ⬝ᵥ (covariance D *ᵥ w) := by
        simp only [dotProduct, mulVec, covariance, mul_sum, sum_mul]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring

lemma quad_nonneg (D : Data 1 n K S) (hq : ∀ s, 0 ≤ D.q s) (w : Inst 1 n → ℝ) :
    0 ≤ w ⬝ᵥ (covariance D *ᵥ w) := by
  rw [quad_eq]
  exact sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)

lemma cov_symm (D : Data 1 n K S) : (covariance D)ᵀ = covariance D := by
  ext i j
  simp only [transpose_apply, covariance]
  exact sum_congr rfl fun s _ => by ring

lemma quad_expand (D : Data 1 n K S) (w d : Inst 1 n → ℝ) :
    (w + d) ⬝ᵥ (covariance D *ᵥ (w + d))
      = w ⬝ᵥ (covariance D *ᵥ w) + 2 * ((covariance D *ᵥ w) ⬝ᵥ d)
        + d ⬝ᵥ (covariance D *ᵥ d) := by
  have h1 : w ⬝ᵥ (covariance D *ᵥ d) = (covariance D *ᵥ w) ⬝ᵥ d := by
    rw [dotProduct_mulVec, ← mulVec_transpose, cov_symm]
  have h2 : d ⬝ᵥ (covariance D *ᵥ w) = (covariance D *ᵥ w) ⬝ᵥ d := dotProduct_comm _ _
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2]
  ring

/-- The exact expansion of the criterion around `w`. -/
lemma Qx_expand (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (x : ℝ) (w d : Inst 1 n → ℝ) :
    Qx D par pi x (w + d) - Qx D par pi x w
      = gv D par pi x w ⬝ᵥ d - D.gamma / 2 * (d ⬝ᵥ (covariance D *ᵥ d))
        - (tau D (w + d - w0 D) - tau D (w - w0 D)) := by
  rw [Qx_eq D par pi hpi, Qx_eq D par pi hpi, quad_expand, gv, sub_dotProduct, smul_dotProduct,
    dotProduct_add, smul_eq_mul]
  ring

/-! ### The cost: subgradients and local linearity -/

/-- One coordinate's cost. -/
noncomputable def cst (kp km y : ℝ) : ℝ := kp * max y 0 + km * max (-y) 0

omit [Fintype S] in
lemma tau_eq_sum (D : Data 1 n K S) (v : Inst 1 n → ℝ) :
    tau D v = ∑ i, cst (D.kplus i) (D.kminus i) (v i) := rfl

/-- The slope of `cst` at `y` in the direction `dd`. -/
noncomputable def slope (kp km y dd : ℝ) : ℝ :=
  if 0 < y then kp else if y < 0 then -km else if 0 ≤ dd then kp else -km

lemma cst_lin (kp km y dd : ℝ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → cst kp km (y + ε * dd) = cst kp km y + ε * (slope kp km y dd * dd) := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · refine ⟨-y / (|dd| + 1), div_pos (by linarith) (by positivity), fun ε hε hle => ?_⟩
    have hd := neg_abs_le dd
    have h1 : ε * |dd| < -y := by
      have : ε * (|dd| + 1) ≤ -y := by rwa [le_div_iff₀ (by positivity)] at hle
      nlinarith [abs_nonneg dd]
    have h2 : y + ε * dd < 0 := by nlinarith [le_abs_self dd]
    simp only [cst, slope, not_lt.mpr hy.le, hy, ↓reduceIte]
    rw [max_eq_right h2.le, max_eq_left (by linarith), max_eq_right hy.le, max_eq_left (by linarith)]
    ring
  · subst hy
    refine ⟨1, one_pos, fun ε hε _ => ?_⟩
    simp only [cst, slope, lt_irrefl, ↓reduceIte, zero_add, neg_zero, max_self, mul_zero,
      add_zero]
    by_cases hd : 0 ≤ dd
    · simp only [hd, ↓reduceIte]
      rw [max_eq_left (mul_nonneg hε.le hd), max_eq_right (by nlinarith)]
      ring
    · push Not at hd
      simp only [not_le.mpr hd, ↓reduceIte]
      rw [max_eq_right (by nlinarith), max_eq_left (by nlinarith)]
      ring
  · refine ⟨y / (|dd| + 1), div_pos hy (by positivity), fun ε hε hle => ?_⟩
    have h1 : ε * |dd| < y := by
      have : ε * (|dd| + 1) ≤ y := by rwa [le_div_iff₀ (by positivity)] at hle
      nlinarith [abs_nonneg dd]
    have h2 : 0 < y + ε * dd := by nlinarith [neg_abs_le dd]
    simp only [cst, slope, hy, ↓reduceIte]
    rw [max_eq_left h2.le, max_eq_right (by linarith), max_eq_left hy.le, max_eq_right (by linarith)]
    ring

/-- The cost slope vector along `d` at `w`. -/
noncomputable def cvec (D : Data 1 n K S) (w d : Inst 1 n → ℝ) : Inst 1 n → ℝ :=
  fun i => slope (D.kplus i) (D.kminus i) (w i - w0 D i) (d i)

lemma inst_nonempty : (Finset.univ : Finset (Inst 1 n)).Nonempty := ⟨Sum.inl 0, mem_univ _⟩

omit [Fintype S] in
lemma tau_lin (D : Data 1 n K S) (w d : Inst 1 n → ℝ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ →
      tau D (w + ε • d - w0 D) = tau D (w - w0 D) + ε * (cvec D w d ⬝ᵥ d) := by
  choose e he hlin using fun i => cst_lin (D.kplus i) (D.kminus i) (w i - w0 D i) (d i)
  refine ⟨univ.inf' inst_nonempty e, (lt_inf'_iff _).mpr fun i _ => he i, fun ε hε hle => ?_⟩
  rw [tau_eq_sum, tau_eq_sum, dotProduct, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have := hlin i ε hε (hle.trans (inf'_le _ (mem_univ i)))
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cvec]
  rw [show w i + ε * d i - w0 D i = w i - w0 D i + ε * d i by ring, this]

lemma max_parts' (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-! ### Sufficiency: the certificate inequality -/

/-- `t` is a subgradient of `cst` at `y`. -/
def SubG (kp km y t : ℝ) : Prop :=
  (0 < y → t = kp) ∧ (y < 0 → t = -km) ∧ (y = 0 → -km ≤ t ∧ t ≤ kp)

lemma cst_subgrad {kp km y t : ℝ} (hp : 0 ≤ kp) (hm : 0 ≤ km) (h : SubG kp km y t) (y' : ℝ) :
    cst kp km y + t * (y' - y) ≤ cst kp km y' := by
  obtain ⟨h1, h2, h3⟩ := h
  have a1 := le_max_left y' 0
  have a2 := le_max_right y' 0
  have a3 := le_max_left (-y') 0
  have a4 := le_max_right (-y') 0
  unfold cst
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [h2 hy, max_eq_right hy.le, max_eq_left (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left a3 hm, mul_le_mul_of_nonneg_left a2 hp]
  · obtain ⟨ht1, ht2⟩ := h3 hy
    subst hy
    simp only [max_self, neg_zero, mul_zero, add_zero, sub_zero, zero_add]
    have e := max_parts' y'
    nlinarith [mul_le_mul_of_nonneg_left a2 (by linarith : (0 : ℝ) ≤ kp - t),
      mul_le_mul_of_nonneg_left a4 (by linarith : (0 : ℝ) ≤ km + t)]
  · rw [h1 hy, max_eq_left hy.le, max_eq_right (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left a1 hp, mul_le_mul_of_nonneg_left a4 hm]

omit [Fintype S] in
lemma cash_sub (D : Data 1 n K S) (w z : Inst 1 n → ℝ) :
    cash D w - cash D z = ∑ i, (z i - w i) + (tau D (z - w0 D) - tau D (w - w0 D)) := by
  have h : ∑ i, (z i - w0 D i) - ∑ i, (w i - w0 D i) = ∑ i, (z i - w i) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  unfold cash
  linarith

/-- The certificate inequality: a funded comparator `z` does not beat `w`. -/
lemma cert (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (hr : RatesNonneg D) (hg : 0 ≤ D.gamma) (hq : ∀ s, 0 ≤ D.q s) (x : ℝ) (w z : Inst 1 n → ℝ)
    (hz : 0 ≤ cash D z) (η : ℝ) (hη : 0 ≤ η) (hcomp : η * cash D w = 0) (t : Inst 1 n → ℝ)
    (ht : ∀ i, SubG (D.kplus i) (D.kminus i) (w i - w0 D i) (t i))
    (hR : ∑ i, (gv D par pi x w i - η - (1 + η) * t i) * (z i - w i) ≤ 0) :
    Qx D par pi x z ≤ Qx D par pi x w := by
  have hexp := Qx_expand D par pi hpi x w (z - w)
  rw [add_sub_cancel] at hexp
  have hsub : ∑ i, t i * (z i - w i) ≤ tau D (z - w0 D) - tau D (w - w0 D) := by
    rw [tau_eq_sum, tau_eq_sum, ← sum_sub_distrib]
    refine sum_le_sum fun i _ => ?_
    have := cst_subgrad (hr i).1 (hr i).2 (ht i) (z i - w0 D i)
    simp only [Pi.sub_apply]
    have e : z i - w0 D i - (w i - w0 D i) = z i - w i := by ring
    rw [e] at this
    linarith
  have hgd : gv D par pi x w ⬝ᵥ (z - w)
      = ∑ i, (gv D par pi x w i - η - (1 + η) * t i) * (z i - w i)
        + η * ∑ i, (z i - w i) + (1 + η) * ∑ i, t i * (z i - w i) := by
    simp only [dotProduct, Pi.sub_apply, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hc := cash_sub D w z
  have hQ := quad_nonneg D hq (z - w)
  have h1 : (1 + η) * (∑ i, t i * (z i - w i) - (tau D (z - w0 D) - tau D (w - w0 D))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h2 : 0 ≤ η * cash D z := mul_nonneg hη hz
  have h3 : 0 ≤ D.gamma / 2 * ((z - w) ⬝ᵥ (covariance D *ᵥ (z - w))) := by positivity
  nlinarith

/-- Per-coordinate residual sign: bounds and signs make each term nonpositive. -/
lemma resid_term {R wi zi wb : ℝ} (hwi : 0 ≤ wi ∧ wi ≤ wb) (hzi : 0 ≤ zi ∧ zi ≤ wb)
    (hR : (wi < wb → R ≤ 0) ∧ (0 < wi → 0 ≤ R)) : R * (zi - wi) ≤ 0 := by
  rcases lt_trichotomy R 0 with h | h | h
  · have : ¬ 0 < wi := fun h' => absurd (hR.2 h') (not_le.mpr h)
    have hw0 : wi = 0 := le_antisymm (not_lt.mp this) hwi.1
    rw [hw0]; nlinarith [hzi.1]
  · rw [h, zero_mul]
  · have : ¬ wi < wb := fun h' => absurd (hR.1 h') (not_le.mpr h)
    have hwb : wi = wb := le_antisymm hwi.2 (not_lt.mp this)
    rw [hwb]; nlinarith [hzi.2]

/-! ### Necessity: improving moves -/

omit [Fintype S] in
lemma box_step (D : Data 1 n K S) (w d : Inst 1 n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ D.wbar i)
    (hsl : ∀ i, (0 < d i → w i < D.wbar i) ∧ (d i < 0 → 0 < w i)) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ → ∀ i, 0 ≤ w i + ε * d i ∧ w i + ε * d i ≤ D.wbar i := by
  let e : Inst 1 n → ℝ := fun i =>
    if 0 < d i then (D.wbar i - w i) / d i else if d i < 0 then w i / (-d i) else 1
  have he : ∀ i, 0 < e i := by
    intro i
    simp only [e]
    split_ifs with h1 h2
    · exact div_pos (by linarith [(hsl i).1 h1]) h1
    · exact div_pos ((hsl i).2 h2) (by linarith)
    · exact one_pos
  refine ⟨univ.inf' inst_nonempty e, (lt_inf'_iff _).mpr fun i _ => he i, fun ε hε hle i => ?_⟩
  have hei : ε ≤ e i := hle.trans (inf'_le _ (mem_univ i))
  simp only [e] at hei
  obtain ⟨h0, hb⟩ := hw i
  split_ifs at hei with h1 h2
  · rw [le_div_iff₀ h1] at hei
    constructor <;> nlinarith
  · rw [le_div_iff₀ (by linarith)] at hei
    constructor <;> nlinarith
  · have : d i = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    rw [this]; constructor <;> linarith

omit [Fintype S] in
lemma cash_step (D : Data 1 n K S) (w d : Inst 1 n → ℝ) (ε : ℝ)
    (hτ : tau D (w + ε • d - w0 D) = tau D (w - w0 D) + ε * (cvec D w d ⬝ᵥ d)) :
    cash D (w + ε • d) = cash D w - ε * (∑ i, d i + cvec D w d ⬝ᵥ d) := by
  have := cash_sub D w (w + ε • d)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, ← mul_sum] at this
  rw [hτ] at this
  linarith

/-- A funded, bounded direction with positive one-sided derivative improves `w`. -/
lemma improve (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (hg : 0 ≤ D.gamma) (hq : ∀ s, 0 ≤ D.q s) (x : ℝ) (w d : Inst 1 n → ℝ) (hw : w ∈ F D)
    (hsl : ∀ i, (0 < d i → w i < D.wbar i) ∧ (d i < 0 → 0 < w i))
    (hcash : ∑ i, d i + cvec D w d ⬝ᵥ d ≤ 0 ∨ 0 < cash D w)
    (hΔ : 0 < gv D par pi x w ⬝ᵥ d - cvec D w d ⬝ᵥ d) :
    ∃ ε : ℝ, 0 < ε ∧ w + ε • d ∈ F D ∧ Qx D par pi x w < Qx D par pi x (w + ε • d) := by
  obtain ⟨ε₀, h₀, hτ⟩ := tau_lin D w d
  obtain ⟨ε₁, h₁, hbox⟩ := box_step D w d hw.1 hsl
  set Δ := gv D par pi x w ⬝ᵥ d - cvec D w d ⬝ᵥ d
  set M := d ⬝ᵥ (covariance D *ᵥ d)
  set σ := ∑ i, d i + cvec D w d ⬝ᵥ d
  have hM := quad_nonneg D hq d
  let ε₂ : ℝ := if σ ≤ 0 then 1 else cash D w / σ
  have h₂ : 0 < ε₂ := by
    simp only [ε₂]
    split_ifs with h
    · exact one_pos
    · exact div_pos (hcash.resolve_left h) (not_le.mp h)
  let ε₃ : ℝ := Δ / (D.gamma * M + 1)
  have h₃ : 0 < ε₃ := div_pos hΔ (by positivity)
  set ε := min (min ε₀ ε₁) (min ε₂ ε₃)
  have hε : 0 < ε := lt_min (lt_min h₀ h₁) (lt_min h₂ h₃)
  have hε₀ : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₂ : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₃ : ε ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hτε := hτ ε hε hε₀
  refine ⟨ε, hε, ⟨fun i => ?_, ?_⟩, ?_⟩
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hbox ε hε hε₁ i
  · rw [cash_step D w d ε hτε]
    by_cases hσ : σ ≤ 0
    · nlinarith [hw.2]
    · have : ε ≤ cash D w / σ := by simpa [ε₂, hσ] using hε₂
      rw [le_div_iff₀ (not_le.mp hσ)] at this
      linarith
  · have hexp := Qx_expand D par pi hpi x w (ε • d)
    rw [hτε, dotProduct_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, smul_eq_mul] at hexp
    have h3 : ε * (D.gamma * M + 1) ≤ Δ := by
      have := hε₃
      rwa [le_div_iff₀ (by positivity)] at this
    have hgM : 0 ≤ D.gamma * M := mul_nonneg hg hM
    have : 0 < ε * (Δ - D.gamma / 2 * (ε * M)) := by
      apply mul_pos hε
      nlinarith
    nlinarith

lemma not_max_F (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (hg : 0 ≤ D.gamma) (hq : ∀ s, 0 ≤ D.q s) (x : ℝ) (w d : Inst 1 n → ℝ) (hw : w ∈ F D)
    (hsl : ∀ i, (0 < d i → w i < D.wbar i) ∧ (d i < 0 → 0 < w i))
    (hcash : ∑ i, d i + cvec D w d ⬝ᵥ d ≤ 0 ∨ 0 < cash D w)
    (hΔ : 0 < gv D par pi x w ⬝ᵥ d - cvec D w d ⬝ᵥ d) :
    ¬ IsMaxOn (Qx D par pi x) (F D) w := by
  obtain ⟨ε, _, hF, hlt⟩ := improve D par pi hpi hg hq x w d hw hsl hcash hΔ
  exact fun h => absurd (h hF) (not_le.mpr hlt)

lemma not_max_E (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (hpi : ∑ h, pi h = 1)
    (hg : 0 ≤ D.gamma) (hq : ∀ s, 0 ≤ D.q s) (x : ℝ) (w d : Inst 1 n → ℝ) (hw : w ∈ E D)
    (hdA : d (Sum.inl 0) = 0)
    (hsl : ∀ i, (0 < d i → w i < D.wbar i) ∧ (d i < 0 → 0 < w i))
    (hcash : ∑ i, d i + cvec D w d ⬝ᵥ d ≤ 0 ∨ 0 < cash D w)
    (hΔ : 0 < gv D par pi x w ⬝ᵥ d - cvec D w d ⬝ᵥ d) :
    ¬ IsMaxOn (Qx D par pi x) (E D) w := by
  obtain ⟨ε, _, hF, hlt⟩ := improve D par pi hpi hg hq x w d hw.1 hsl hcash hΔ
  have hE : w + ε • d ∈ E D := by
    refine ⟨hF, ?_⟩
    funext j
    rw [← hw.2]
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [active, hdA]
  exact fun h => absurd (h hE) (not_le.mpr hlt)

/-! ### Facts at an ETF-only maximizer -/

section AtWE

variable (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ)

lemma gv_inl (x : ℝ) (w : Inst 1 n → ℝ) :
    gv D par pi x w (Sum.inl 0) = x - alphaC D par pi w := by
  simp only [gv, meanVec, alphaC, Pi.sub_apply, Pi.smul_apply, Sum.elim_inl, smul_eq_mul]
  ring

lemma gv_inr (x : ℝ) (w : Inst 1 n → ℝ) (j : Fin n) :
    gv D par pi x w (Sum.inr j) = gE D par pi w j := by
  simp only [gv, meanVec, gE, Pi.sub_apply, Pi.smul_apply, Sum.elim_inr, smul_eq_mul]

omit [Fintype S] in
lemma slope_up (w : Inst 1 n → ℝ) (j : Fin n) {dd : ℝ} (hd : 0 < dd) :
    slope (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) (w (Sum.inr j) - w0 D (Sum.inr j)) dd
      = uE D w j := by
  unfold slope uE
  rcases lt_trichotomy (w (Sum.inr j)) (w0 D (Sum.inr j)) with h | h | h
  · simp [h, not_lt.mpr h.le, sub_neg.mpr h]
  · simp [h, hd.le]
  · simp [sub_pos.mpr h, not_lt.mpr h.le]

omit [Fintype S] in
lemma slope_down (w : Inst 1 n → ℝ) (j : Fin n) {dd : ℝ} (hd : dd < 0) :
    slope (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) (w (Sum.inr j) - w0 D (Sum.inr j)) dd
      = ellE D w j := by
  unfold slope ellE
  rcases lt_trichotomy (w (Sum.inr j)) (w0 D (Sum.inr j)) with h | h | h
  · simp [not_lt.mpr h.le, sub_neg.mpr h]
  · simp [h, not_le.mpr hd]
  · simp [h, sub_pos.mpr h]

omit [Fintype S] in
lemma slope_zero {kp km y dd : ℝ} (hy : y = 0) :
    slope kp km y dd = if 0 ≤ dd then kp else -km := by
  simp [slope, hy]

omit [Fintype S] in
lemma ell_pos (hr : RatesNonneg D) (h1 : ∀ i, D.kplus i < 1 ∧ D.kminus i < 1) (w : Inst 1 n → ℝ)
    (j : Fin n) : 0 < 1 + ellE D w j := by
  unfold ellE
  split_ifs
  · linarith [(hr (Sum.inr j)).1]
  · linarith [(h1 (Sum.inr j)).2]

omit [Fintype S] in
lemma u_pos (hr : RatesNonneg D) (h1 : ∀ i, D.kplus i < 1 ∧ D.kminus i < 1) (w : Inst 1 n → ℝ)
    (j : Fin n) : 0 < 1 + uE D w j := by
  unfold uE
  split_ifs
  · linarith [(h1 (Sum.inr j)).2]
  · linarith [(hr (Sum.inr j)).1]

omit [Fintype S] in
lemma ell_le_u (hr : RatesNonneg D) (w : Inst 1 n → ℝ) (j : Fin n) : ellE D w j ≤ uE D w j := by
  unfold ellE uE
  have := hr (Sum.inr j)
  split_ifs with h1 h2
  · exact absurd h2 (lt_asymm h1)
  · linarith
  · linarith
  · linarith

/-- An E-maximizer at one `x₀` is an E-maximizer at every `x`. -/
lemma Emax_all (hpi : ∑ h, pi h = 1) {x₀ : ℝ} {wE : Inst 1 n → ℝ}
    (hwE : wE ∈ maximizers (Qx D par pi x₀) (E D)) (x : ℝ) :
    IsMaxOn (Qx D par pi x) (E D) wE := by
  intro z hz
  have h1 := hwE.2 z hz
  have ha : z (Sum.inl 0) = wE (Sum.inl 0) := by
    have := congrFun (hz.2.trans hwE.1.2.symm) 0
    simpa [active] using this
  simp only [Set.mem_ofPred_eq]
  rw [Qx_shift D par pi hpi x x₀ z, Qx_shift D par pi hpi x x₀ wE, ha]
  linarith

omit [Fintype S] in
lemma wE_active {wE : Inst 1 n → ℝ} (h : wE ∈ E D) : wE (Sum.inl 0) = w0 D (Sum.inl 0) := by
  simpa [active] using congrFun h.2 0

/-- One-coordinate direction. -/
noncomputable def e1 (i : Inst 1 n) (a : ℝ) : Inst 1 n → ℝ := Pi.single i a

/-- Two-coordinate direction. -/
noncomputable def e2 (i j : Inst 1 n) (a b : ℝ) : Inst 1 n → ℝ := Pi.single i a + Pi.single j b

omit [Fintype S] in
lemma one_dir (w : Inst 1 n → ℝ) (i : Inst 1 n) (a : ℝ) (v : Inst 1 n → ℝ) :
    ∑ k, e1 i a k = a ∧ v ⬝ᵥ e1 i a = v i * a ∧
    cvec D w (e1 i a) ⬝ᵥ e1 i a
      = slope (D.kplus i) (D.kminus i) (w i - w0 D i) a * a := by
  unfold e1
  refine ⟨by simp [Finset.sum_pi_single'], dotProduct_single _ _ _, ?_⟩
  rw [dotProduct_single]
  simp [cvec]

omit [Fintype S] in
lemma one_dir_sl (w : Inst 1 n → ℝ) (i : Inst 1 n) (a : ℝ)
    (h1 : 0 < a → w i < D.wbar i) (h2 : a < 0 → 0 < w i) :
    ∀ k, (0 < e1 i a k → w k < D.wbar k) ∧ (e1 i a k < 0 → 0 < w k) := by
  intro k
  unfold e1
  by_cases hk : k = i
  · subst hk; simpa using ⟨h1, h2⟩
  · simp [hk]

omit [Fintype S] in
lemma two_dir (w : Inst 1 n → ℝ) (i j : Inst 1 n) (hij : i ≠ j) (a b : ℝ) (v : Inst 1 n → ℝ) :
    ∑ k, (e2 i j a b) k = a + b ∧
    v ⬝ᵥ (e2 i j a b) = v i * a + v j * b ∧
    cvec D w (e2 i j a b) ⬝ᵥ (e2 i j a b)
      = slope (D.kplus i) (D.kminus i) (w i - w0 D i) a * a
        + slope (D.kplus j) (D.kminus j) (w j - w0 D j) b * b := by
  unfold e2
  refine ⟨by simp [Finset.sum_add_distrib, Finset.sum_pi_single'], by
    rw [dotProduct_add, dotProduct_single, dotProduct_single], ?_⟩
  rw [dotProduct_add, dotProduct_single, dotProduct_single]
  simp [cvec, hij, hij.symm]

omit [Fintype S] in
lemma two_dir_sl (w : Inst 1 n → ℝ) (i j : Inst 1 n) (hij : i ≠ j) (a b : ℝ)
    (h1 : 0 < a → w i < D.wbar i) (h2 : a < 0 → 0 < w i)
    (h3 : 0 < b → w j < D.wbar j) (h4 : b < 0 → 0 < w j) :
    ∀ k, (0 < (e2 i j a b) k → w k < D.wbar k) ∧
      ((e2 i j a b) k < 0 → 0 < w k) := by
  intro k
  unfold e2
  by_cases hk : k = i
  · subst hk; simpa [Pi.single_apply, hij] using ⟨h1, h2⟩
  · by_cases hk' : k = j
    · subst hk'; simpa [Pi.single_apply, hk] using ⟨h3, h4⟩
    · simp [hk, hk']

end AtWE

/-! ### The multiplier interval -/

section Interval

variable {D : Data 1 n K S} {par : T → Params 1 K} {pi : T → ℝ}

/-- Unpacked setting. -/
lemma setting_parts (h : BandSetting D pi) :
    InitialPosition D ∧ RatesNonneg D ∧ (∀ i, D.kplus i < 1 ∧ D.kminus i < 1) ∧
    (∀ i, D.wbar i ≤ 1) ∧ 0 ≤ D.gamma ∧ (∀ s, 0 ≤ D.q s) ∧ MassesSumToOne D ∧
    ∑ h, pi h = 1 := h

variable (hS : BandSetting D pi) {wE : Inst 1 n → ℝ}
  (hwE : ∀ x, IsMaxOn (Qx D par pi x) (E D) wE) (hmem : wE ∈ E D)
include hS hwE hmem

/-- (E1) buying an ETF from slack cash does not improve. -/
lemma E_buy (hc : 0 < cash D wE) (j : Fin n) (hj : wE (Sum.inr j) < D.wbar (Sum.inr j)) :
    gE D par pi wE j ≤ uE D wE j := by
  obtain ⟨_, _, _, _, hg, hq, _, hpi⟩ := setting_parts hS
  by_contra hlt
  push Not at hlt
  obtain ⟨_, h2, h3⟩ := one_dir D wE (Sum.inr j) 1 (gv D par pi 0 wE)
  apply not_max_E D par pi hpi hg hq 0 wE (e1 (Sum.inr j) 1) hmem (by simp [e1])
    (one_dir_sl D wE _ 1 (fun _ => hj) (fun h => absurd h (by norm_num))) (Or.inr hc) _ (hwE 0)
  rw [h2, h3, gv_inr, slope_up D wE j one_pos]
  linarith

/-- (E2) selling an ETF into cash does not improve. -/
lemma E_sell (j : Fin n) (hj : 0 < wE (Sum.inr j)) : ellE D wE j ≤ gE D par pi wE j := by
  obtain ⟨_, hr, h1, _, hg, hq, _, hpi⟩ := setting_parts hS
  by_contra hlt
  push Not at hlt
  obtain ⟨h0, h2, h3⟩ := one_dir D wE (Sum.inr j) (-1) (gv D par pi 0 wE)
  have hl := ell_pos D hr h1 wE j
  apply not_max_E D par pi hpi hg hq 0 wE (e1 (Sum.inr j) (-1)) hmem (by simp [e1])
    (one_dir_sl D wE _ (-1) (fun h => absurd h (by norm_num)) (fun _ => hj)) (Or.inl ?_) ?_
    (hwE 0)
  · rw [h0, h3, slope_down D wE j (by norm_num : (-1 : ℝ) < 0)]; linarith
  · rw [h2, h3, gv_inr, slope_down D wE j (by norm_num : (-1 : ℝ) < 0)]; linarith

/-- (E3) swapping ETF `j` for ETF `i` does not improve. -/
lemma E_swap (i j : Fin n) (hij : i ≠ j) (hi : wE (Sum.inr i) < D.wbar (Sum.inr i))
    (hj : 0 < wE (Sum.inr j)) :
    (gE D par pi wE i - uE D wE i) * (1 + ellE D wE j)
      ≤ (gE D par pi wE j - ellE D wE j) * (1 + uE D wE i) := by
  obtain ⟨_, hr, h1, _, hg, hq, _, hpi⟩ := setting_parts hS
  have hl := ell_pos D hr h1 wE j
  have hu := u_pos D hr h1 wE i
  have hne : (Sum.inr i : Inst 1 n) ≠ Sum.inr j := fun h => hij (Sum.inr_injective h)
  by_contra hlt
  push Not at hlt
  obtain ⟨h0, h2, h3⟩ := two_dir D wE (Sum.inr i) (Sum.inr j) hne (1 + ellE D wE j)
    (-(1 + uE D wE i)) (gv D par pi 0 wE)
  apply not_max_E D par pi hpi hg hq 0 wE _ hmem (by simp [e2])
    (two_dir_sl D wE _ _ hne (1 + ellE D wE j) (-(1 + uE D wE i)) (fun _ => hi) (fun h => absurd h (by linarith))
      (fun h => absurd h (by linarith)) (fun _ => hj)) (Or.inl ?_) ?_ (hwE 0)
  · rw [h0, h3, slope_up D wE i (by linarith), slope_down D wE j (by linarith)]; nlinarith
  · rw [h2, h3, gv_inr, gv_inr, slope_up D wE i (by linarith), slope_down D wE j (by linarith)]
    nlinarith

lemma swap_ok (i j : Fin n) (hi : wE (Sum.inr i) < D.wbar (Sum.inr i))
    (hj : 0 < wE (Sum.inr j)) :
    (gE D par pi wE i - uE D wE i) / (1 + uE D wE i)
      ≤ (gE D par pi wE j - ellE D wE j) / (1 + ellE D wE j) := by
  obtain ⟨_, hr, h1, _⟩ := setting_parts hS
  have hl := ell_pos D hr h1 wE j
  have hu := u_pos D hr h1 wE i
  rw [div_le_div_iff₀ hu hl]
  by_cases hij : i = j
  · subst hij
    have hs := E_sell hS hwE hmem i hj
    have hlu := ell_le_u D hr wE i
    nlinarith
  · exact E_swap hS hwE hmem i j hij hi hj

lemma zero_le_h (j : Fin n) (hj : 0 < wE (Sum.inr j)) :
    0 ≤ (gE D par pi wE j - ellE D wE j) / (1 + ellE D wE j) := by
  obtain ⟨_, hr, h1, _⟩ := setting_parts hS
  exact div_nonneg (by linarith [E_sell hS hwE hmem j hj]) (ell_pos D hr h1 wE j).le

omit hS hwE hmem in
lemma loSet_ne : (loSet D par pi wE).Nonempty := Finset.insert_nonempty _ _

omit hS hwE hmem in
lemma lo_eq (hc0 : ¬ 0 < cash D wE) :
    lo D par pi wE = (loSet D par pi wE).max' loSet_ne := by
  simp only [lo, hc0, ↓reduceIte]

omit hS hwE hmem in
lemma mem_loSet {i : Fin n} (hi : wE (Sum.inr i) < D.wbar (Sum.inr i)) :
    (gE D par pi wE i - uE D wE i) / (1 + uE D wE i) ∈ loSet D par pi wE :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨mem_univ _, hi⟩))

omit hS hwE hmem in
lemma mem_hiSet {j : Fin n} (hj : 0 < wE (Sum.inr j)) :
    (gE D par pi wE j - ellE D wE j) / (1 + ellE D wE j) ∈ hiSet D par pi wE :=
  Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨mem_univ _, hj⟩)

omit hwE in
lemma mem_I_iff (hc0 : ¬ 0 < cash D wE) (η : ℝ) :
    η ∈ Iset D par pi wE ↔ lo D par pi wE ≤ η ∧ ∀ v ∈ hiSet D par pi wE, η ≤ v := by
  obtain ⟨_, hr, h1, _⟩ := setting_parts hS
  have hc : cash D wE = 0 := le_antisymm (not_lt.mp hc0) hmem.1.2
  rw [lo_eq hc0]
  constructor
  · rintro ⟨hη, _, hj⟩
    refine ⟨Finset.max'_le _ _ _ fun v hv => ?_, fun v hv => ?_⟩
    · rw [loSet, Finset.mem_insert, Finset.mem_image] at hv
      rcases hv with rfl | ⟨i, hi, rfl⟩
      · exact hη
      · rw [Finset.mem_filter] at hi
        rw [div_le_iff₀ (u_pos D hr h1 wE i)]; linarith [(hj i).1 hi.2]
    · rw [hiSet, Finset.mem_image] at hv
      obtain ⟨j, hj', rfl⟩ := hv
      rw [Finset.mem_filter] at hj'
      rw [le_div_iff₀ (ell_pos D hr h1 wE j)]; linarith [(hj j).2 hj'.2]
  · rintro ⟨hlo, hhi⟩
    have hle : ∀ v ∈ loSet D par pi wE, v ≤ η := fun v hv => (Finset.le_max' _ _ hv).trans hlo
    refine ⟨hle 0 (Finset.mem_insert_self _ _), by rw [hc, mul_zero], fun j => ⟨fun hj => ?_,
      fun hj => ?_⟩⟩
    · have := hle _ (mem_loSet hj)
      rw [div_le_iff₀ (u_pos D hr h1 wE j)] at this; linarith
    · have := hhi _ (mem_hiSet hj)
      rw [le_div_iff₀ (ell_pos D hr h1 wE j)] at this; linarith

omit hwE hmem in
lemma w0_k0_sum : ∑ i, w0 D i + k0 D = 1 := by
  obtain ⟨hIP, _⟩ := setting_parts hS
  have hW0 : D.h0 + ∑ i, D.x0 i = W0 D := rfl
  simp only [w0, k0]
  rw [← Finset.sum_div, ← add_div, add_comm, hW0, div_self hIP.1.ne']

omit hwE in
lemma hiFinite_of (ha : w0 D (Sum.inl 0) < 1) : HiFinite D par pi wE := by
  obtain ⟨hIP, hr, h1, _⟩ := setting_parts hS
  by_contra hne
  have hc0 : ¬ 0 < cash D wE := fun h => hne (Or.inl h)
  have hz : ∀ j, ¬ 0 < wE (Sum.inr j) := fun j hj => hne (Or.inr ⟨_, mem_hiSet hj⟩)
  have hc : cash D wE = 0 := le_antisymm (not_lt.mp hc0) hmem.1.2
  have hp0 : ∀ j, wE (Sum.inr j) = 0 := fun j => le_antisymm (not_lt.mp (hz j)) (hmem.1.1 _).1
  have hA := wE_active D hmem
  have hw0nn : ∀ i, 0 ≤ w0 D i := fun i => div_nonneg (hIP.2.1 i) hIP.1.le
  have hk0 : 0 ≤ k0 D := div_nonneg hIP.2.2.1 hIP.1.le
  have hsum : ∑ i, (wE i - w0 D i) = -∑ j, w0 D (Sum.inr j) := by
    rw [sum_inst, hA, sub_self, zero_add, ← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by rw [hp0 j]; ring
  have htau : tau D (wE - w0 D) = ∑ j, D.kminus (Sum.inr j) * w0 D (Sum.inr j) := by
    rw [tau_eq_sum, sum_inst]
    simp only [Pi.sub_apply, hA, sub_self, cst, max_self, neg_zero, mul_zero, add_zero, zero_add]
    refine sum_congr rfl fun j _ => ?_
    rw [hp0 j, zero_sub, neg_neg, max_eq_right (by linarith [hw0nn (Sum.inr j)]),
      max_eq_left (hw0nn _)]
    ring
  have hterm : ∀ j, 0 ≤ (1 - D.kminus (Sum.inr j)) * w0 D (Sum.inr j) :=
    fun j => mul_nonneg (by linarith [(h1 (Sum.inr j)).2]) (hw0nn _)
  have hsplit : ∑ j, (1 - D.kminus (Sum.inr j)) * w0 D (Sum.inr j)
      = ∑ j, w0 D (Sum.inr j) - ∑ j, D.kminus (Sum.inr j) * w0 D (Sum.inr j) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hcash : cash D wE = k0 D + ∑ j, (1 - D.kminus (Sum.inr j)) * w0 D (Sum.inr j) := by
    rw [cash, hsum, htau, hsplit]
    ring
  have hnn := sum_nonneg fun j (_ : j ∈ univ) => hterm j
  have hsum0 : ∑ j, (1 - D.kminus (Sum.inr j)) * w0 D (Sum.inr j) = 0 := by linarith
  have hk00 : k0 D = 0 := by linarith
  have hpz : ∀ j, w0 D (Sum.inr j) = 0 := by
    intro j
    have := (sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum0 j (mem_univ j)
    rcases mul_eq_zero.mp this with h | h
    · linarith [(h1 (Sum.inr j)).2]
    · exact h
  have := w0_k0_sum hS
  rw [sum_inst] at this
  simp only [hpz, sum_const_zero, add_zero, hk00] at this
  linarith

/-- The multiplier interval. -/
lemma interval :
    (HiFinite D par pi wE → Iset D par pi wE = Set.Icc (lo D par pi wE) (hi D par pi wE)) ∧
    (¬ HiFinite D par pi wE → Iset D par pi wE = Set.Ici (lo D par pi wE)) ∧
    lo D par pi wE ∈ Iset D par pi wE ∧
    (0 < cash D wE → Iset D par pi wE = {0}) ∧
    (w0 D (Sum.inl 0) < 1 → HiFinite D par pi wE) := by
  obtain ⟨_, hr, h1, _⟩ := setting_parts hS
  by_cases hc : 0 < cash D wE
  · have hI : Iset D par pi wE = {0} := by
      ext η
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, hη, _⟩
        rcases mul_eq_zero.mp hη with h | h
        · exact h
        · exact absurd h hc.ne'
      · rintro rfl
        refine ⟨le_rfl, zero_mul _, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
        · have := E_buy hS hwE hmem hc j hj; linarith
        · have := E_sell hS hwE hmem j hj; linarith
    have hlo : lo D par pi wE = 0 := by simp [lo, hc]
    have hhi : hi D par pi wE = 0 := by simp [hi, hc]
    refine ⟨fun _ => by rw [hI, hlo, hhi, Set.Icc_self], fun h => absurd (Or.inl hc) h,
      by rw [hI, hlo]; rfl, fun _ => hI, fun _ => Or.inl hc⟩
  · have hlo_mem : lo D par pi wE ∈ Iset D par pi wE := by
      rw [mem_I_iff hS hmem hc]
      refine ⟨le_rfl, fun v hv => ?_⟩
      rw [lo_eq hc]
      refine Finset.max'_le _ _ _ fun u hu => ?_
      simp only [hiSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      simp only [loSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hu
      rcases hu with rfl | ⟨i, hi, rfl⟩
      · exact zero_le_h hS hwE hmem j hj
      · exact swap_ok hS hwE hmem i j hi hj
    refine ⟨fun hF => ?_, fun hF => ?_, hlo_mem, fun h => absurd h hc,
      fun ha => hiFinite_of hS hmem ha⟩
    · have hne : (hiSet D par pi wE).Nonempty := hF.resolve_left hc
      ext η
      rw [mem_I_iff hS hmem hc, Set.mem_Icc]
      simp only [hi, hc, ↓reduceIte, hne, ↓reduceDIte, Finset.le_min'_iff]
    · have he : hiSet D par pi wE = ∅ := by
        by_contra h
        exact hF (Or.inr (Finset.nonempty_iff_ne_empty.mpr h))
      ext η
      rw [mem_I_iff hS hmem hc, Set.mem_Ici, he]
      simp

/-! ### The band -/

omit [Fintype S] hS hwE hmem in
lemma slope_A (hmem' : wE ∈ E D) (dd : ℝ) :
    slope (D.kplus (Sum.inl 0)) (D.kminus (Sum.inl 0)) (wE (Sum.inl 0) - w0 D (Sum.inl 0)) dd
      = if 0 ≤ dd then D.kplus (Sum.inl 0) else -D.kminus (Sum.inl 0) :=
  slope_zero (by rw [wE_active D hmem', sub_self])

omit hwE in
/-- Necessity of the band bounds, by active-fund moves. -/
lemma F_necessary (x : ℝ) (hF : IsMaxOn (Qx D par pi x) (F D) wE) :
    (w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) →
      x - alphaC D par pi wE ≤ D.kplus (Sum.inl 0) + (1 + D.kplus (Sum.inl 0)) * hi D par pi wE) ∧
    (0 < w0 D (Sum.inl 0) →
      -D.kminus (Sum.inl 0) + (1 - D.kminus (Sum.inl 0)) * lo D par pi wE
        ≤ x - alphaC D par pi wE) := by
  obtain ⟨_, hr, h1, hbar, hg, hq, _, hpi⟩ := setting_parts hS
  have hA := wE_active D hmem
  have hb := (hr (Sum.inl 0)).1
  have hs := (hr (Sum.inl 0)).2
  have hs1 := (h1 (Sum.inl 0)).2
  have hneAj : ∀ j : Fin n, (Sum.inl 0 : Inst 1 n) ≠ Sum.inr j := fun j h => Sum.inl_ne_inr h
  -- (M2) selling the active fund into cash does not improve
  have hM2 : 0 < w0 D (Sum.inl 0) → -D.kminus (Sum.inl 0) ≤ x - alphaC D par pi wE := by
    intro hpos
    by_contra hlt
    push Not at hlt
    obtain ⟨h0, h2, h3⟩ := one_dir D wE (Sum.inl 0) (-1) (gv D par pi x wE)
    apply not_max_F D par pi hpi hg hq x wE (e1 (Sum.inl 0) (-1)) hmem.1
      (one_dir_sl D wE _ (-1) (fun h => absurd h (by norm_num)) (fun _ => by rw [hA]; exact hpos))
      (Or.inl ?_) ?_ hF
    · rw [h0, h3, slope_A hmem]; norm_num; linarith
    · rw [h2, h3, gv_inl, slope_A hmem]; norm_num; linarith
  refine ⟨fun hup => ?_, fun hpos => ?_⟩
  · by_cases hc : 0 < cash D wE
    · -- (M1) buying the active fund from slack cash does not improve
      have hhi : hi D par pi wE = 0 := by simp [hi, hc]
      rw [hhi, mul_zero, add_zero]
      by_contra hlt
      push Not at hlt
      obtain ⟨_, h2, h3⟩ := one_dir D wE (Sum.inl 0) 1 (gv D par pi x wE)
      apply not_max_F D par pi hpi hg hq x wE (e1 (Sum.inl 0) 1) hmem.1
        (one_dir_sl D wE _ 1 (fun _ => by rw [hA]; exact hup) (fun h => absurd h (by norm_num)))
        (Or.inr hc) ?_ hF
      rw [h2, h3, gv_inl, slope_A hmem]; norm_num; linarith
    · -- (M3) buying the active fund with an ETF sale does not improve
      have hfin := hiFinite_of (par := par) hS hmem (lt_of_lt_of_le hup (hbar _))
      have hne : (hiSet D par pi wE).Nonempty := hfin.resolve_left hc
      have hhi : hi D par pi wE = (hiSet D par pi wE).min' hne := by
        simp only [hi, hc, ↓reduceIte, hne, ↓reduceDIte]
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp (hhi ▸ Finset.min'_mem _ hne :
        hi D par pi wE ∈ hiSet D par pi wE)
      rw [Finset.mem_filter] at hj
      have hl := ell_pos D hr h1 wE j
      rw [← hjv]
      by_contra hlt
      push Not at hlt
      have hh : (gE D par pi wE j - ellE D wE j) / (1 + ellE D wE j) * (1 + ellE D wE j)
          = gE D par pi wE j - ellE D wE j := div_mul_cancel₀ _ hl.ne'
      have hlt2 := mul_lt_mul_of_pos_right hlt hl
      obtain ⟨h0, h2, h3⟩ := two_dir D wE (Sum.inl 0) (Sum.inr j) (hneAj j) (1 + ellE D wE j)
        (-(1 + D.kplus (Sum.inl 0))) (gv D par pi x wE)
      apply not_max_F D par pi hpi hg hq x wE _ hmem.1
        (two_dir_sl D wE _ _ (hneAj j) (1 + ellE D wE j) (-(1 + D.kplus (Sum.inl 0)))
          (fun _ => by rw [hA]; exact hup) (fun h => absurd h (by linarith))
          (fun h => absurd h (by linarith)) (fun _ => hj.2)) (Or.inl ?_) ?_ hF
      · have hpos' : (0 : ℝ) ≤ 1 + ellE D wE j := hl.le
        rw [h0, h3, slope_A hmem, slope_down D wE j (by linarith)]
        simp only [hpos', ↓reduceIte]
        nlinarith
      · have hpos' : (0 : ℝ) ≤ 1 + ellE D wE j := hl.le
        rw [h2, h3, gv_inl, gv_inr, slope_A hmem, slope_down D wE j (by linarith)]
        simp only [hpos', ↓reduceIte]
        nlinarith
  · have hm2 := hM2 hpos
    by_cases hc : 0 < cash D wE
    · have hlo : lo D par pi wE = 0 := by simp [lo, hc]
      rw [hlo, mul_zero, add_zero]; exact hm2
    · have hmem' := Finset.max'_mem (loSet D par pi wE) loSet_ne
      rw [← lo_eq hc] at hmem'
      rw [loSet, Finset.mem_insert, Finset.mem_image] at hmem'
      rcases hmem' with h0 | ⟨i, hi, hiv⟩
      · rw [h0, mul_zero, add_zero]; exact hm2
      · -- (M4) selling the active fund to buy an ETF does not improve
        rw [Finset.mem_filter] at hi
        have hu := u_pos D hr h1 wE i
        rw [← hiv]
        by_contra hlt
        push Not at hlt
        obtain ⟨h0, h2, h3⟩ := two_dir D wE (Sum.inl 0) (Sum.inr i) (hneAj i)
          (-(1 + uE D wE i)) (1 - D.kminus (Sum.inl 0)) (gv D par pi x wE)
        have hlt' : x - alphaC D par pi wE + D.kminus (Sum.inl 0)
            < (1 - D.kminus (Sum.inl 0)) * ((gE D par pi wE i - uE D wE i) / (1 + uE D wE i)) := by
          linarith
        rw [mul_div_assoc', lt_div_iff₀ hu] at hlt'
        apply not_max_F D par pi hpi hg hq x wE _ hmem.1
          (two_dir_sl D wE _ _ (hneAj i) (-(1 + uE D wE i)) (1 - D.kminus (Sum.inl 0))
            (fun h => absurd h (by linarith)) (fun _ => by rw [hA]; exact hpos)
            (fun _ => hi.2) (fun h => absurd h (by linarith))) (Or.inl ?_) ?_ hF
        · have hneg : ¬ (0 : ℝ) ≤ -(1 + uE D wE i) := by linarith
          rw [h0, h3, slope_A hmem, slope_up D wE i (by linarith)]
          simp only [hneg, ↓reduceIte]
          nlinarith
        · have hneg : ¬ (0 : ℝ) ≤ -(1 + uE D wE i) := by linarith
          rw [h2, h3, gv_inl, gv_inr, slope_A hmem, slope_up D wE i (by linarith)]
          simp only [hneg, ↓reduceIte]
          nlinarith

/-- The marginal condition at `x`. -/
def Marg (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (wE : Inst 1 n → ℝ) (x : ℝ) :
    Prop :=
  ∃ η ∈ Iset D par pi wE, ∃ tA, -D.kminus (Sum.inl 0) ≤ tA ∧ tA ≤ D.kplus (Sum.inl 0) ∧
    (w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) → x - alphaC D par pi wE - η - (1 + η) * tA ≤ 0) ∧
    (0 < w0 D (Sum.inl 0) → 0 ≤ x - alphaC D par pi wE - η - (1 + η) * tA)

/-- The band bounds at `x`. -/
def Bounds (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (wE : Inst 1 n → ℝ) (x : ℝ) :
    Prop :=
  (w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) →
    x - alphaC D par pi wE ≤ D.kplus (Sum.inl 0) + (1 + D.kplus (Sum.inl 0)) * hi D par pi wE) ∧
  (0 < w0 D (Sum.inl 0) →
    -D.kminus (Sum.inl 0) + (1 - D.kminus (Sum.inl 0)) * lo D par pi wE ≤ x - alphaC D par pi wE)

lemma lo_le_of_mem {η : ℝ} (hη : η ∈ Iset D par pi wE) : lo D par pi wE ≤ η := by
  obtain ⟨hI1, hI2, _⟩ := interval hS hwE hmem
  by_cases hF : HiFinite D par pi wE
  · rw [hI1 hF] at hη; exact hη.1
  · rw [hI2 hF] at hη; exact hη

lemma build (x : ℝ) (hB : Bounds D par pi wE x) : Marg D par pi wE x := by
  obtain ⟨hIP, hr, h1, hbar, _⟩ := setting_parts hS
  obtain ⟨hI1, _, hlo, _⟩ := interval hS hwE hmem
  have hb := (hr (Sum.inl 0)).1
  have hs := (hr (Sum.inl 0)).2
  have hs1 := (h1 (Sum.inl 0)).2
  have hlo0 : 0 ≤ lo D par pi wE := hlo.1
  set gA := x - alphaC D par pi wE
  set b := D.kplus (Sum.inl 0)
  set sr := D.kminus (Sum.inl 0)
  have hA0 : 0 ≤ w0 D (Sum.inl 0) := div_nonneg (hIP.2.1 _) hIP.1.le
  by_cases hup : w0 D (Sum.inl 0) < D.wbar (Sum.inl 0)
  · have hfin := hiFinite_of (par := par) hS hmem (lt_of_lt_of_le hup (hbar _))
    have hloh : lo D par pi wE ≤ hi D par pi wE := by
      have := hlo; rw [hI1 hfin] at this; exact this.2
    have hU := hB.1 hup
    set η := max (lo D par pi wE) ((gA - b) / (1 + b))
    have hη1 : lo D par pi wE ≤ η := le_max_left _ _
    have hη2 : (gA - b) / (1 + b) ≤ η := le_max_right _ _
    have hηhi : η ≤ hi D par pi wE := by
      refine max_le hloh ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    have hηI : η ∈ Iset D par pi wE := by rw [hI1 hfin]; exact ⟨hη1, hηhi⟩
    have hη0 : 0 ≤ η := hlo0.trans hη1
    have hgA : gA ≤ b + (1 + b) * η := by
      rw [div_le_iff₀ (by linarith)] at hη2; linarith
    rcases eq_or_lt_of_le hA0 with hz | hpos
    · refine ⟨η, hηI, b, by linarith, le_rfl, fun _ => by nlinarith, fun h => absurd h (by
        rw [← hz]; exact lt_irrefl 0)⟩
    · have hL := hB.2 hpos
      refine ⟨η, hηI, (gA - η) / (1 + η), ?_, ?_, fun _ => ?_, fun _ => ?_⟩
      · rw [le_div_iff₀ (by linarith)]
        -- gA ≥ -s + (1 - s) η
        rcases le_total ((gA - b) / (1 + b)) (lo D par pi wE) with h | h
        · have : η = lo D par pi wE := max_eq_left h
          rw [this]; nlinarith
        · have hηe : η = (gA - b) / (1 + b) := max_eq_right h
          have hgb : b ≤ gA := by
            have := hlo0.trans h
            rw [le_div_iff₀ (by linarith)] at this; linarith
          have hη' : η * (1 + b) = gA - b := by rw [hηe]; field_simp
          nlinarith
      · rw [div_le_iff₀ (by linarith)]; nlinarith
      · rw [mul_div_cancel₀ _ (by linarith : (1 + η) ≠ 0)]; linarith
      · rw [mul_div_cancel₀ _ (by linarith : (1 + η) ≠ 0)]; linarith
  · refine ⟨lo D par pi wE, hlo, -sr, le_rfl, by linarith, fun h => absurd h hup, fun hpos => ?_⟩
    have := hB.2 hpos
    nlinarith

lemma extract (x : ℝ) (hM : Marg D par pi wE x) : Bounds D par pi wE x := by
  obtain ⟨_, hr, h1, hbar, _⟩ := setting_parts hS
  obtain ⟨hI1, _, _, _⟩ := interval hS hwE hmem
  obtain ⟨η, hη, tA, htl, htu, hR1, hR2⟩ := hM
  have hη0 : 0 ≤ η := hη.1
  have hlo := lo_le_of_mem hS hwE hmem hη
  have hs1 := (h1 (Sum.inl 0)).2
  refine ⟨fun hup => ?_, fun hpos => ?_⟩
  · have hfin := hiFinite_of (par := par) hS hmem (lt_of_lt_of_le hup (hbar _))
    have hηhi : η ≤ hi D par pi wE := by have := hη; rw [hI1 hfin] at this; exact this.2
    have := hR1 hup
    nlinarith [mul_le_mul_of_nonneg_left htu (by linarith : (0 : ℝ) ≤ 1 + η),
      mul_le_mul_of_nonneg_left hηhi (by linarith [(hr (Sum.inl 0)).1] :
        (0 : ℝ) ≤ 1 + D.kplus (Sum.inl 0))]
  · have := hR2 hpos
    nlinarith [mul_le_mul_of_nonneg_left htl (by linarith : (0 : ℝ) ≤ 1 + η),
      mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 1 - D.kminus (Sum.inl 0))]

omit hwE in
lemma sufficient (x : ℝ) (hM : Marg D par pi wE x) : IsMaxOn (Qx D par pi x) (F D) wE := by
  obtain ⟨_, hr, h1, _, hg, hq, _, hpi⟩ := setting_parts hS
  obtain ⟨η, ⟨hη0, hηc, hηj⟩, tA, htl, htu, hR1, hR2⟩ := hM
  have hA := wE_active D hmem
  let v : Fin n → ℝ := fun j => (gE D par pi wE j - η) / (1 + η)
  have hv : ∀ j, (1 + η) * v j = gE D par pi wE j - η := fun j => mul_div_cancel₀ _ (by linarith)
  let t : Inst 1 n → ℝ :=
    Sum.elim (fun _ => tA) (fun j => max (ellE D wE j) (min (v j) (uE D wE j)))
  intro z hz
  simp only [Set.mem_ofPred_eq]
  refine cert D par pi hpi hr hg hq x wE z hz.2 η hη0 hηc t (fun i => ?_) ?_
  · rcases i with k | j
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      refine ⟨fun h => absurd h (by rw [hA, sub_self]; exact lt_irrefl 0),
        fun h => absurd h (by rw [hA, sub_self]; exact lt_irrefl 0), fun _ => ⟨htl, htu⟩⟩
    · have hlu := ell_le_u D hr wE j
      have hkp := (hr (Sum.inr j)).1
      have hkm := (hr (Sum.inr j)).2
      refine ⟨fun hy => ?_, fun hy => ?_, fun hy => ?_⟩
      · have he : ellE D wE j = D.kplus (Sum.inr j) := by
          simp [ellE, sub_pos.mp hy]
        have hu : uE D wE j = D.kplus (Sum.inr j) := by
          simp [uE, not_lt.mpr (sub_pos.mp hy).le]
        simp only [t, Sum.elim_inr, he, hu]
        exact max_eq_left (min_le_right _ _)
      · have he : ellE D wE j = -D.kminus (Sum.inr j) := by
          simp [ellE, not_lt.mpr (sub_neg.mp hy).le]
        have hu : uE D wE j = -D.kminus (Sum.inr j) := by
          simp [uE, sub_neg.mp hy]
        simp only [t, Sum.elim_inr, he, hu]
        exact max_eq_left (min_le_right _ _)
      · have heq : wE (Sum.inr j) = w0 D (Sum.inr j) := sub_eq_zero.mp hy
        have he : ellE D wE j = -D.kminus (Sum.inr j) := by simp [ellE, heq]
        have hu : uE D wE j = D.kplus (Sum.inr j) := by simp [uE, heq]
        simp only [t, Sum.elim_inr]
        rw [he, hu] at hlu ⊢
        exact ⟨le_max_left _ _, max_le hlu (min_le_right _ _)⟩
  · refine sum_nonpos fun i _ => ?_
    rcases i with k | j
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simp only [t, Sum.elim_inl, gv_inl]
      exact resid_term (hmem.1.1 _) (hz.1 _)
        ⟨fun h => hR1 (by rwa [hA] at h), fun h => hR2 (by rwa [hA] at h)⟩
    · simp only [t, Sum.elim_inr, gv_inr]
      refine resid_term (hmem.1.1 _) (hz.1 _) ⟨fun h => ?_, fun h => ?_⟩
      · have hvu : v j ≤ uE D wE j := by
          have := (hηj j).1 h
          rw [div_le_iff₀ (by linarith)]; linarith
        have : v j ≤ max (ellE D wE j) (min (v j) (uE D wE j)) :=
          le_max_of_le_right (le_min le_rfl hvu)
        nlinarith [hv j, mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 + η)]
      · have hlv : ellE D wE j ≤ v j := by
          have := (hηj j).2 h
          rw [le_div_iff₀ (by linarith)]; linarith
        have : max (ellE D wE j) (min (v j) (uE D wE j)) ≤ v j :=
          max_le hlv (min_le_left _ _)
        nlinarith [hv j, mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 + η)]

lemma Fopt_iff (x : ℝ) : IsMaxOn (Qx D par pi x) (F D) wE ↔ Marg D par pi wE x :=
  ⟨fun h => build hS hwE hmem x (F_necessary hS hmem x h), sufficient hS hmem x⟩

lemma Marg_iff (x : ℝ) : Marg D par pi wE x ↔ Bounds D par pi wE x :=
  ⟨extract hS hwE hmem x, build hS hwE hmem x⟩

omit hS in
lemma C_iff (x : ℝ) : x ∈ Cset D par pi ↔ IsMaxOn (Qx D par pi x) (F D) wE := by
  constructor
  · rintro ⟨w, hwF, hmax, hwa⟩
    have hwE' : w ∈ E D := ⟨hwF, by funext k; obtain rfl : k = 0 := Subsingleton.elim _ _; exact hwa⟩
    have h1 : Qx D par pi x w ≤ Qx D par pi x wE := hwE x hwE'
    intro z hz
    have := hmax hz
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  · intro h
    exact ⟨wE, hmem.1, h, wE_active D hmem⟩

end Interval

/-! ### Attainment for every real `x` -/

omit [Fintype S] in
lemma continuous_tau (D : Data 1 n K S) : Continuous (tau D) := by
  unfold tau
  fun_prop

omit [Fintype S] in
lemma continuous_cash (D : Data 1 n K S) : Continuous (cash D) := by
  have := continuous_tau D
  unfold cash
  fun_prop

lemma continuous_Qx (D : Data 1 n K S) (par : T → Params 1 K) (pi : T → ℝ) (x : ℝ) :
    Continuous (Qx D par pi x) := by
  have := continuous_tau D
  unfold Qx beliefScore score exposure active etf covariance
  simp only [Pi.add_apply, mulVec, dotProduct]
  fun_prop

omit [Fintype S] in
lemma isClosed_F (D : Data 1 n K S) : IsClosed (F D) := by
  have h1 : IsClosed {w : Inst 1 n → ℝ | ∀ i, 0 ≤ w i ∧ w i ≤ D.wbar i} := by
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_apply i) continuous_const)
  exact h1.inter (isClosed_le continuous_const (continuous_cash D))

omit [Fintype S] in
lemma isCompact_F (D : Data 1 n K S) : IsCompact (F D) :=
  isCompact_Icc.of_isClosed_subset (isClosed_F D) fun _ hw =>
    ⟨fun i => (hw.1 i).1, fun i => (hw.1 i).2⟩

omit [Fintype S] in
lemma isCompact_E (D : Data 1 n K S) : IsCompact (E D) := by
  refine (isCompact_F D).of_isClosed_subset ((isClosed_F D).inter (isClosed_eq ?_ continuous_const))
    fun _ hw => hw.1
  unfold active
  fun_prop

omit [Fintype S] in
lemma w0_mem_E (D : Data 1 n K S) (h : InitialPosition D) : w0 D ∈ E D := by
  refine ⟨⟨fun i => ⟨div_nonneg (h.2.1 i) h.1.le, h.2.2.2 i⟩, ?_⟩, rfl⟩
  have : cash D (w0 D) = k0 D := by simp [cash, tau]
  rw [this]
  exact div_nonneg h.2.2.1 h.1.le

/-! ### Assembling the statement -/

section Assemble

variable {D : Data 1 n K S} {par : T → Params 1 K} {pi : T → ℝ}

lemma alphaFamily (hS : BandSetting D pi) :
    (∀ x, (beliefMean (famPar par pi x) pi).alpha = fun _ => x) ∧
    (∀ x h s j, ret D (famPar par pi x h) s (Sum.inr j) = ret D (par h) s (Sum.inr j)) ∧
    (∀ x, x ∈ Jset D par pi ↔ ∀ h s, alphaMinTerm D par pi h s < x) ∧
    (∃ αmin, Jset D par pi = Set.Ioi αmin ∧ (∃ h s, αmin = alphaMinTerm D par pi h s) ∧
      ∀ h s, alphaMinTerm D par pi h s ≤ αmin) ∧
    ((∀ h s, 0 < 1 + ret D (par h) s (Sum.inl 0)) → abar0 par pi ∈ Jset D par pi) ∧
    ((∀ h s j, 0 < 1 + ret D (par h) s (Sum.inr j)) →
      ∀ x ∈ Jset D par pi, ∀ h s i, 0 < 1 + ret D (famPar par pi x h) s i) := by
  obtain ⟨_, _, _, _, _, _, hmass, hpi⟩ := setting_parts hS
  have hretA : ∀ x h s, 1 + ret D (famPar par pi x h) s (Sum.inl 0)
      = x - alphaMinTerm D par pi h s := by
    intro x h s
    simp only [ret, famPar, alphaMinTerm, xi, Sum.elim_inl, Pi.add_apply, mulVec_add]
    ring
  have hJ : ∀ x, x ∈ Jset D par pi ↔ ∀ h s, alphaMinTerm D par pi h s < x := by
    intro x
    simp only [Jset, Set.mem_ofPred_eq, hretA, sub_pos]
  have hretE : ∀ x h s j, ret D (famPar par pi x h) s (Sum.inr j) = ret D (par h) s (Sum.inr j) := by
    intro x h s j
    simp only [ret, famPar, Sum.elim_inr]
  refine ⟨fun x => ?_, hretE, hJ, ?_, fun hpos => ?_, fun hpos x hx h s i => ?_⟩
  · funext k
    simp only [beliefMean, famPar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∑ h, pi h * ((par h).alpha 0 - abar0 par pi + x)
        = abar0 par pi + (x - abar0 par pi) * ∑ h, pi h := by
      rw [abar0, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun h _ => by ring
    rw [e, hpi]
    ring
  · have hSne : (univ : Finset S).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have := hmass
      simp [MassesSumToOne, h] at this
    have hTne : (univ : Finset T).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h] at hpi
    have hne : (univ ×ˢ univ : Finset (T × S)).Nonempty := hTne.product hSne
    let f : T × S → ℝ := fun p => alphaMinTerm D par pi p.1 p.2
    refine ⟨(univ ×ˢ univ).sup' hne f, ?_, ?_, fun h s => ?_⟩
    · ext x
      rw [hJ, Set.mem_Ioi, Finset.sup'_lt_iff]
      exact ⟨fun H p _ => H p.1 p.2, fun H h s => H (h, s) (mem_product.mpr ⟨mem_univ _, mem_univ _⟩)⟩
    · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne f
      exact ⟨p.1, p.2, hp⟩
    · have hm : (h, s) ∈ (univ ×ˢ univ : Finset (T × S)) := mem_product.mpr ⟨mem_univ h, mem_univ s⟩
      exact (Finset.le_sup' (b := (h, s)) f hm : f (h, s) ≤ _)
  · rw [hJ]
    intro h s
    have := hpos h s
    have e := hretA (abar0 par pi) h s
    have e2 : ret D (famPar par pi (abar0 par pi) h) s (Sum.inl 0) = ret D (par h) s (Sum.inl 0) := by
      simp only [ret, famPar, Sum.elim_inl, sub_add_cancel, Pi.add_apply]
    rw [e2] at e
    linarith
  · rcases i with k | j
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [hretA]; exact sub_pos.mpr ((hJ x).mp hx h s)
    · rw [hretE]; exact hpos h s j

lemma eOptima (hS : BandSetting D pi) :
    (∀ x, ∃ w ∈ E D, IsMaxOn (Qx D par pi x) (E D) w) ∧
    (∀ x, ∃ w ∈ F D, IsMaxOn (Qx D par pi x) (F D) w) ∧
    (∀ x y, maximizers (Qx D par pi x) (E D) = maximizers (Qx D par pi y) (E D)) ∧
    ∀ x₀ wE, wE ∈ maximizers (Qx D par pi x₀) (E D) →
      ∀ x, x ∈ Cset D par pi ↔ IsMaxOn (Qx D par pi x) (F D) wE := by
  obtain ⟨hIP, _, _, _, _, _, _, hpi⟩ := setting_parts hS
  refine ⟨fun x => (isCompact_E D).exists_isMaxOn ⟨_, w0_mem_E D hIP⟩ (continuous_Qx D par pi x).continuousOn,
    fun x => (isCompact_F D).exists_isMaxOn ⟨_, (w0_mem_E D hIP).1⟩ (continuous_Qx D par pi x).continuousOn,
    fun x y => ?_, fun x₀ wE hwE x => C_iff (Emax_all D par pi hpi hwE) hwE.1 x⟩
  ext w
  constructor
  · intro hw
    exact ⟨hw.1, Emax_all D par pi hpi hw y⟩
  · intro hw
    exact ⟨hw.1, Emax_all D par pi hpi hw x⟩

lemma bandTable (hS : BandSetting D pi) {x₀ : ℝ} {wE : Inst 1 n → ℝ}
    (hwE : wE ∈ maximizers (Qx D par pi x₀) (E D)) :
    (0 < w0 D (Sum.inl 0) → w0 D (Sum.inl 0) < D.wbar (Sum.inl 0) →
      Cset D par pi = Set.Icc (Lb D par pi wE) (Ub D par pi wE)) ∧
    (w0 D (Sum.inl 0) = 0 → 0 < D.wbar (Sum.inl 0) → Cset D par pi = Set.Iic (Ub D par pi wE)) ∧
    (0 < w0 D (Sum.inl 0) → w0 D (Sum.inl 0) = D.wbar (Sum.inl 0) →
      Cset D par pi = Set.Ici (Lb D par pi wE)) ∧
    (w0 D (Sum.inl 0) = 0 → D.wbar (Sum.inl 0) = 0 → Cset D par pi = Set.univ) ∧
    Ub D par pi wE - Lb D par pi wE
      = D.kplus (Sum.inl 0) * (1 + hi D par pi wE) + D.kminus (Sum.inl 0) * (1 + lo D par pi wE)
        + (hi D par pi wE - lo D par pi wE) := by
  obtain ⟨_, _, _, _, _, _, _, hpi⟩ := setting_parts hS
  have hall := Emax_all D par pi hpi hwE
  have hC : ∀ x, x ∈ Cset D par pi ↔ Bounds D par pi wE x := fun x =>
    (C_iff hall hwE.1 x).trans ((Fopt_iff hS hall hwE.1 x).trans (Marg_iff hS hall hwE.1 x))
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, by
    simp only [Lb, Ub]; ring⟩
  · ext x
    rw [hC, Set.mem_Icc]
    simp only [Bounds, Lb, Ub, h1, h2, true_implies]
    constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · ext x
    rw [hC, Set.mem_Iic]
    simp only [Bounds, Ub, h1, h2, true_implies, lt_irrefl, false_implies, and_true]
    constructor <;> intro h <;> linarith
  · ext x
    rw [hC, Set.mem_Ici]
    simp only [Bounds, Lb, ← h2, lt_irrefl, false_implies, h1, true_implies, true_and]
    constructor <;> intro h <;> linarith
  · ext x
    rw [hC]
    simp [Bounds, h1, h2]

/-! ### Uniqueness under strictness -/

lemma cst_mid {kp km : ℝ} (hp : 0 ≤ kp) (hm : 0 ≤ km) (a b : ℝ) :
    cst kp km ((a + b) / 2) ≤ (cst kp km a + cst kp km b) / 2 := by
  have h1 : max ((a + b) / 2) 0 ≤ (max a 0 + max b 0) / 2 :=
    max_le (by linarith [le_max_left a 0, le_max_left b 0])
      (by linarith [le_max_right a 0, le_max_right b 0])
  have h2 : max (-((a + b) / 2)) 0 ≤ (max (-a) 0 + max (-b) 0) / 2 :=
    max_le (by linarith [le_max_left (-a) 0, le_max_left (-b) 0])
      (by linarith [le_max_right (-a) 0, le_max_right (-b) 0])
  unfold cst
  nlinarith [mul_le_mul_of_nonneg_left h1 hp, mul_le_mul_of_nonneg_left h2 hm]

/-- The midpoint. -/
noncomputable def mid (w z : Inst 1 n → ℝ) : Inst 1 n → ℝ := fun i => (w i + z i) / 2

omit [Fintype S] in
lemma tau_mid (hr : RatesNonneg D) (w z : Inst 1 n → ℝ) :
    tau D (mid w z - w0 D) ≤ (tau D (w - w0 D) + tau D (z - w0 D)) / 2 := by
  rw [tau_eq_sum, tau_eq_sum, tau_eq_sum, ← sum_add_distrib, sum_div]
  refine sum_le_sum fun i _ => ?_
  have := cst_mid (hr i).1 (hr i).2 (w i - w0 D i) (z i - w0 D i)
  simp only [Pi.sub_apply, mid]
  rw [show (w i + z i) / 2 - w0 D i = ((w i - w0 D i) + (z i - w0 D i)) / 2 by ring]
  exact this

omit [Fintype S] in
lemma mid_mem_F (hr : RatesNonneg D) {w z : Inst 1 n → ℝ} (hw : w ∈ F D) (hz : z ∈ F D) :
    mid w z ∈ F D := by
  refine ⟨fun i => ⟨by simp only [mid]; linarith [(hw.1 i).1, (hz.1 i).1],
    by simp only [mid]; linarith [(hw.1 i).2, (hz.1 i).2]⟩, ?_⟩
  have ht := tau_mid hr w z
  have hs : ∑ i, (mid w z i - w0 D i) = (∑ i, (w i - w0 D i) + ∑ i, (z i - w0 D i)) / 2 := by
    rw [← sum_add_distrib, sum_div]
    exact sum_congr rfl fun i _ => by simp only [mid]; ring
  have := hw.2
  have := hz.2
  unfold cash at *
  rw [hs]
  linarith

omit [Fintype S] in
lemma mid_mem_E (hr : RatesNonneg D) {w z : Inst 1 n → ℝ} (hw : w ∈ E D) (hz : z ∈ E D) :
    mid w z ∈ E D := by
  refine ⟨mid_mem_F hr hw.1 hz.1, ?_⟩
  funext k
  have h1 := congrFun hw.2 k
  have h2 := congrFun hz.2 k
  simp only [active, mid] at h1 h2 ⊢
  rw [h1, h2]; ring

lemma mid_strict (hS : BandSetting D pi) (hgpos : 0 < D.gamma)
    (hPD : ∀ v : Inst 1 n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (covariance D *ᵥ v)) (x : ℝ)
    {w z : Inst 1 n → ℝ} (hne : w ≠ z) :
    Qx D par pi x w + Qx D par pi x z < 2 * Qx D par pi x (mid w z) := by
  obtain ⟨_, hr, _, _, _, _, _, hpi⟩ := setting_parts hS
  let d : Inst 1 n → ℝ := fun i => (w i - z i) / 2
  have hw : mid w z + d = w := by funext i; simp only [mid, d, Pi.add_apply]; ring
  have hz : mid w z + -d = z := by funext i; simp only [mid, d, Pi.add_apply, Pi.neg_apply]; ring
  have hd : d ≠ 0 := by
    intro h
    apply hne
    funext i
    have := congrFun h i
    simp only [d, Pi.zero_apply] at this
    linarith
  have e1 := Qx_expand D par pi hpi x (mid w z) d
  have e2 := Qx_expand D par pi hpi x (mid w z) (-d)
  rw [hw] at e1
  rw [hz] at e2
  rw [dotProduct_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at e2
  have ht := tau_mid hr w z
  have hq := hPD d hd
  nlinarith [mul_pos hgpos hq]

lemma uniqueness (hS : BandSetting D pi) (hgpos : 0 < D.gamma)
    (hPD : ∀ v : Inst 1 n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (covariance D *ᵥ v)) (x : ℝ) :
    (∀ w w', w ∈ maximizers (Qx D par pi x) (F D) → w' ∈ maximizers (Qx D par pi x) (F D) →
      w = w') ∧
    (∀ w w', w ∈ maximizers (Qx D par pi x) (E D) → w' ∈ maximizers (Qx D par pi x) (E D) →
      w = w') := by
  obtain ⟨_, hr, _⟩ := setting_parts hS
  refine ⟨fun w w' hw hw' => ?_, fun w w' hw hw' => ?_⟩
  · by_contra hne
    have := mid_strict (par := par) hS hgpos hPD x hne
    have h1 := hw.2 _ (mid_mem_F hr hw.1 hw'.1)
    have h2 := hw'.2 _ (mid_mem_F hr hw.1 hw'.1)
    linarith
  · by_contra hne
    have := mid_strict (par := par) hS hgpos hPD x hne
    have h1 := hw.2 _ (mid_mem_E hr hw.1 hw'.1)
    have h2 := hw'.2 _ (mid_mem_E hr hw.1 hw'.1)
    linarith

end Assemble

/-! ### The counterexamples -/

section Counter

variable {a₀ p₀ h₀ : ℝ}

lemma cx_W0 (hW : h₀ + (a₀ + p₀) = 1) : W0 (cxData a₀ p₀ h₀) = 1 := by
  rw [W0, sum_inst]; simpa [cxData] using hW

lemma cx_w0 (hW : h₀ + (a₀ + p₀) = 1) : w0 (cxData a₀ p₀ h₀) = hold a₀ p₀ := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
    simp only [w0, cx_W0 hW, div_one] <;> simp [cxData, hold]

lemma cx_tau (v : Inst 1 1 → ℝ) : tau (cxData a₀ p₀ h₀) v = 0 := by
  simp [tau, cxData]

lemma cx_cash (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    cash (cxData a₀ p₀ h₀) (hold a p) = 1 - a - p := by
  rw [cash, cx_tau, sum_inst, cx_w0 hW, k0, cx_W0 hW]
  simp [hold, cxData]
  linarith

lemma hold_inj' {a p a' p' : ℝ} : hold a p = hold a' p' ↔ a = a' ∧ p = p' :=
  ⟨fun h => ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0)⟩, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩

lemma cx_hold_surj (w : Inst 1 1 → ℝ) : w = hold (w (Sum.inl 0)) (w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

lemma cx_mem_F (hW : h₀ + (a₀ + p₀) = 1) (a p : ℝ) :
    hold a p ∈ F (cxData a₀ p₀ h₀) ↔ (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ p ∧ p ≤ 1) ∧ a + p ≤ 1 := by
  simp only [F, Set.mem_ofPred_eq, cx_cash hW]
  simp only [Sum.forall, Fin.forall_fin_one, hold, cxData, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩

lemma cx_Qx (x : ℝ) (w : Inst 1 1 → ℝ) : Qx (cxData a₀ p₀ h₀) cxPar cxPi x w = x * w (Sum.inl 0) := by
  rw [Qx_eq _ _ _ (by simp [cxPi]) x w, cx_tau]
  simp [meanVec, cxData, dotProduct]

lemma cx_setting (hW : h₀ + (a₀ + p₀) = 1) (ha : 0 ≤ a₀) (hp : 0 ≤ p₀) (hh : 0 ≤ h₀)
    (ha1 : a₀ ≤ 1) (hp1 : p₀ ≤ 1) : BandSetting (cxData a₀ p₀ h₀) cxPi := by
  refine ⟨⟨by rw [cx_W0 hW]; norm_num, fun i => ?_, hh, fun i => ?_⟩, fun i => ?_, fun i => ?_,
    fun i => ?_, by simp [cxData], fun s => by simp [cxData], by simp [MassesSumToOne, cxData],
    by simp [cxPi]⟩
  · rcases i with k | k <;> simpa [cxData]
  · rw [cx_w0 hW]; rcases i with k | k <;> simpa [hold, cxData]
  · simp [cxData]
  · simp [cxData]
  · simp [cxData]

lemma cx_J : Jset (cxData a₀ p₀ h₀) cxPar cxPi = Set.Ioi (-1) := by
  ext x
  simp [Jset, ret, famPar, cxData, cxPar, abar0, neg_lt_iff_pos_add, add_comm]

lemma counterexamples : Counterexamples := by
  have hW1 : (0 : ℝ) + (1 / 2 + 1 / 2) = 1 := by norm_num
  have hW2 : (0 : ℝ) + (1 + 0) = 1 := by norm_num
  have hF1 := cx_mem_F (a₀ := 1 / 2) (p₀ := 1 / 2) (h₀ := 0) hW1
  have hF2 := cx_mem_F (a₀ := 1) (p₀ := 0) (h₀ := 0) hW2
  have hE1 : ∀ a p, hold a p ∈ E (cxData (1 / 2) (1 / 2) 0) ↔
      hold a p ∈ F (cxData (1 / 2) (1 / 2) 0) ∧ a = 1 / 2 := by
    intro a p
    refine and_congr Iff.rfl ?_
    rw [cx_w0 hW1]
    exact ⟨fun h => congrFun h 0, fun h => by funext k; simp [active, hold, h]⟩
  have hE2 : ∀ a p, hold a p ∈ E (cxData 1 0 0) ↔ hold a p ∈ F (cxData 1 0 0) ∧ a = 1 := by
    intro a p
    refine and_congr Iff.rfl ?_
    rw [cx_w0 hW2]
    exact ⟨fun h => congrFun h 0, fun h => by funext k; simp [active, hold, h]⟩
  have hcash1 : cash (cxData (1 / 2) (1 / 2) 0) (hold (1 / 2) (1 / 2)) = 0 := by
    rw [cx_cash hW1]; norm_num
  have hcash2 : cash (cxData 1 0 0) (hold 1 0) = 0 := by rw [cx_cash hW2]; norm_num
  refine ⟨cx_setting hW1 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num),
    cx_setting hW2 (by norm_num) le_rfl le_rfl le_rfl (by norm_num), cx_J, cx_J,
    ?_, (hF1 0 1).mpr ⟨by norm_num, by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  -- first counterexample: every funded holding is optimal at x = 0
  · ext w
    simp only [maximizers, Set.mem_ofPred_eq, cx_Qx, zero_mul, le_refl, implies_true, and_true]
  · refine ⟨(hE1 _ _).mpr ⟨(hF1 _ _).mpr ⟨by norm_num, by norm_num, by norm_num⟩, rfl⟩,
      fun z _ => ?_⟩
    simp [cx_Qx]
  · ext η
    simp only [Iset, Set.mem_ofPred_eq, Set.mem_singleton_iff, hcash1, mul_zero, true_and]
    have hg : ∀ j, gE (cxData (1 / 2) (1 / 2) 0) cxPar cxPi (hold (1 / 2) (1 / 2)) j = 0 := by
      intro j; simp [gE, cxData, lamBar]
    have hl : ∀ j, ellE (cxData (1 / 2) (1 / 2) 0) (hold (1 / 2) (1 / 2)) j = 0 := by
      intro j; simp [ellE, hold, cxData]
    have hu : ∀ j, uE (cxData (1 / 2) (1 / 2) 0) (hold (1 / 2) (1 / 2)) j = 0 := by
      intro j; simp [uE, hold, cxData]
    simp only [hg, hl, hu, zero_add, add_zero, one_mul, Fin.forall_fin_one]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact le_antisymm (h2 (by norm_num [hold])) h0
    · rintro rfl
      exact ⟨le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
  · simp [alphaC, cxData, lamBar]
  · ext x
    simp only [Cset, Set.mem_ofPred_eq, Set.mem_singleton_iff, cx_w0 hW1]
    constructor
    · rintro ⟨w, hw, hmax, hwa⟩
      have hA : w (Sum.inl 0) = 1 / 2 := by simpa [hold] using hwa
      have h1 := hmax ((hF1 1 0).mpr ⟨by norm_num, by norm_num, by norm_num⟩)
      have h2 := hmax ((hF1 0 0).mpr ⟨by norm_num, by norm_num, by norm_num⟩)
      simp only [Set.mem_ofPred_eq, cx_Qx, hA, hold, Sum.elim_inl] at h1 h2
      linarith
    · rintro rfl
      refine ⟨hold (1 / 2) (1 / 2), (hF1 _ _).mpr ⟨by norm_num, by norm_num, by norm_num⟩,
        fun z _ => by simp [cx_Qx], by simp [hold]⟩
  -- second counterexample: E is the incumbent alone and C = [0, ∞)
  · ext w
    rw [cx_hold_surj w, hE2, hF2, Set.mem_singleton_iff, hold_inj']
    constructor
    · rintro ⟨⟨_, ⟨hp, _⟩, ht⟩, ha⟩
      exact ⟨ha, by linarith⟩
    · rintro ⟨ha, hp⟩
      rw [ha, hp]
      exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, rfl⟩
  · rintro (h | ⟨v, hv⟩)
    · rw [hcash2] at h; exact lt_irrefl 0 h
    · simp only [hiSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨j, hj, _⟩ := hv
      simp [hold] at hj
  · ext η
    simp only [Iset, Set.mem_ofPred_eq, Set.mem_Ici, hcash2, mul_zero, true_and]
    have hg : ∀ j, gE (cxData 1 0 0) cxPar cxPi (hold 1 0) j = 0 := by
      intro j; simp [gE, cxData, lamBar]
    have hu : ∀ j, uE (cxData 1 0 0) (hold 1 0) j = 0 := by
      intro j; simp [uE, hold, cxData]
    simp only [hg, hu, zero_add, add_zero, one_mul, Fin.forall_fin_one]
    constructor
    · rintro ⟨h0, _⟩; exact h0
    · intro h0
      refine ⟨h0, fun _ => h0, fun h => absurd h (by simp [hold])⟩
  · ext x
    simp only [Cset, Set.mem_ofPred_eq, Set.mem_Ici, cx_w0 hW2]
    constructor
    · rintro ⟨w, hw, hmax, hwa⟩
      have hA : w (Sum.inl 0) = 1 := by simpa [hold] using hwa
      have h2 := hmax ((hF2 0 0).mpr ⟨by norm_num, by norm_num, by norm_num⟩)
      simp only [Set.mem_ofPred_eq, cx_Qx, hA, hold, Sum.elim_inl] at h2
      linarith
    · intro hx
      refine ⟨hold 1 0, (hF2 _ _).mpr ⟨by norm_num, by norm_num, by norm_num⟩, fun z hz => ?_,
        by simp [hold]⟩
      rw [cx_hold_surj z] at hz ⊢
      obtain ⟨⟨_, ha1⟩, _⟩ := (hF2 _ _).mp hz
      simp only [Set.mem_ofPred_eq, cx_Qx, hold, Sum.elim_inl]
      nlinarith
  · intro x hx
    simp only [cx_Qx, hold, Sum.elim_inl]
    linarith

end Counter

theorem proof : Standalone.M2NoActiveTradeBand.statement :=
  ⟨fun _ _ _ _ _ _ _ _ _ hS => alphaFamily hS,
   fun _ _ _ _ _ _ _ _ _ hS => eOptima hS,
   fun _ _ _ _ _ _ _ par pi hS x₀ wE hwE => by
     obtain ⟨_, _, _, _, _, _, _, hpi⟩ := setting_parts hS
     exact interval hS (Emax_all _ par pi hpi hwE) hwE.1,
   fun _ _ _ _ _ _ _ _ _ hS _ _ hwE => bandTable hS hwE,
   fun _ _ _ _ _ _ _ par pi hS x₀ wE hwE x => by
     obtain ⟨_, _, _, _, _, _, _, hpi⟩ := setting_parts hS
     have hall := Emax_all _ par pi hpi hwE
     exact (C_iff hall hwE.1 x).trans (Fopt_iff hS hall hwE.1 x),
   fun _ _ _ _ _ _ _ _ _ hS hg hPD x => uniqueness hS hg hPD x,
   counterexamples⟩

end Novel.M2NoActiveTradeBandProof

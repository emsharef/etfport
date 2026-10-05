import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Novel.M2SoftTargetTwoStageProof
import Novel.M2TwoStageSeparationProof
import Novel.M5MissingDirectionLeakProof
import Standalone.M7TwoStageExactnessLoss
import Upstream.PolyKKT

/-!
# Claim 104: proof (work in progress)

Part 1: under the reference case the cross moments vanish, so claim 027's concavity applies, and
every positive semidefinite triple is realized by `±` scenarios along its square root's columns.

Part 3b: the lower end is strong concavity of `ψ` along the segment from `a_J` toward `a*`. The upper
end expands the quadratic exactly at `a_J` and bounds the cost's change by its slopes. At an
interior `a_J`, a small step would raise `ψ` if the marginal left the cost band.
-/

namespace Novel.M7TwoStageExactnessLossProof

open Filter Topology Matrix Standalone.M2ScoreAccounting Standalone.M7TwoStageExactnessLoss

noncomputable section

set_option linter.unusedSectionVars false

lemma max_sub_le (x y : ℝ) : max x 0 - max y 0 ≤ max (x - y) 0 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy <;> simp [hx, hy]

/-- The cost rises by at most `κ⁺` per unit bought and `κ⁻` per unit sold. -/
lemma cost_change (kp km xm a b : ℝ) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) :
    (kp * max (b - xm) 0 + km * max (xm - b) 0) - (kp * max (a - xm) 0 + km * max (xm - a) 0) ≤
      kp * max (b - a) 0 + km * max (a - b) 0 := by
  have h1 := mul_le_mul_of_nonneg_left (max_sub_le (b - xm) (a - xm)) hkp
  have h2 := mul_le_mul_of_nonneg_left (max_sub_le (xm - b) (xm - a)) hkm
  rw [show b - xm - (a - xm) = b - a by ring] at h1
  rw [show xm - b - (xm - a) = a - b by ring] at h2
  linarith

lemma psi_eq (alpha c kp km xm a : ℝ) : psi alpha c kp km xm a =
    alpha * a - c / 2 * a ^ 2 - (kp * max (a - xm) 0 + km * max (xm - a) 0) := by
  rw [psi]; ring

section Psi

variable (alpha c kp km xm : ℝ)

/-- The cost `κ⁺(a - x⁻)⁺ + κ⁻(x⁻ - a)⁺`. -/
def cst (a : ℝ) : ℝ := kp * max (a - xm) 0 + km * max (xm - a) 0

lemma psi_diff (a b : ℝ) : psi alpha c kp km xm a - psi alpha c kp km xm b =
    (alpha - c * a) * (a - b) + c / 2 * (a - b) ^ 2 + (cst kp km xm b - cst kp km xm a) := by
  simp only [psi, cst]; ring

variable {alpha c kp km xm} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km)
include hc hkp hkm

lemma upper_end (a b mu : ℝ) (h1 : alpha - c * a ≤ kp + mu) (h2 : -km - mu ≤ alpha - c * a) :
    psi alpha c kp km xm a - psi alpha c kp km xm b ≤ c / 2 * (a - b) ^ 2 + (kp + km + mu) * |a - b| := by
  rw [psi_diff]
  have hcost := cost_change kp km xm a b hkp hkm
  simp only [cst]
  rcases le_total 0 (a - b) with hΔ | hΔ
  · rw [abs_of_nonneg hΔ]
    rw [max_eq_right (show b - a ≤ 0 by linarith), max_eq_left (show 0 ≤ a - b by linarith)] at hcost
    nlinarith [mul_le_mul_of_nonneg_right h1 hΔ]
  · rw [abs_of_nonpos hΔ]
    rw [max_eq_left (show 0 ≤ b - a by linarith), max_eq_right (show a - b ≤ 0 by linarith)] at hcost
    nlinarith [mul_le_mul_of_nonpos_right h2 hΔ]

lemma cst_convex (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cst kp km xm (a + t * (b - a)) ≤ (1 - t) * cst kp km xm a + t * cst kp km xm b := by
  simp only [cst]
  have c1 : max (a + t * (b - a) - xm) 0 ≤ (1 - t) * max (a - xm) 0 + t * max (b - xm) 0 := by
    apply max_le
    · nlinarith [le_max_left (a - xm) 0, le_max_left (b - xm) 0]
    · nlinarith [le_max_right (a - xm) 0, le_max_right (b - xm) 0]
  have c2 : max (xm - (a + t * (b - a))) 0 ≤ (1 - t) * max (xm - a) 0 + t * max (xm - b) 0 := by
    apply max_le
    · nlinarith [le_max_left (xm - a) 0, le_max_left (xm - b) 0]
    · nlinarith [le_max_right (xm - a) 0, le_max_right (xm - b) 0]
  nlinarith [mul_le_mul_of_nonneg_left c1 hkp, mul_le_mul_of_nonneg_left c2 hkm]

lemma lower_end {xbar a b : ℝ} (ha : a ∈ Set.Icc 0 xbar)
    (hmax : IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) a) (hb : b ∈ Set.Icc 0 xbar) :
    c / 2 * (a - b) ^ 2 ≤ psi alpha c kp km xm a - psi alpha c kp km xm b := by
  have seg : ∀ t : ℝ, 0 < t → t ≤ 1 →
      c / 2 * (1 - t) * (a - b) ^ 2 ≤ psi alpha c kp km xm a - psi alpha c kp km xm b := by
    intro t ht0 ht1
    have hmem : a + t * (b - a) ∈ Set.Icc 0 xbar := by
      constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
    have hle : psi alpha c kp km xm (a + t * (b - a)) ≤ psi alpha c kp km xm a := hmax hmem
    have hcv := cst_convex (xm := xm) hc hkp hkm a b t ht0.le ht1
    have hq : psi alpha c kp km xm (a + t * (b - a)) = (1 - t) * psi alpha c kp km xm a +
        t * psi alpha c kp km xm b + c / 2 * t * (1 - t) * (a - b) ^ 2 +
        ((1 - t) * cst kp km xm a + t * cst kp km xm b - cst kp km xm (a + t * (b - a))) := by
      simp only [psi, cst]; ring
    have : t * (c / 2 * (1 - t) * (a - b) ^ 2) ≤ t * (psi alpha c kp km xm a - psi alpha c kp km xm b) := by
      nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hlim : Tendsto (fun t : ℝ => c / 2 * (1 - t) * (a - b) ^ 2) (𝓝[>] 0)
      (𝓝 (c / 2 * (1 - 0) * (a - b) ^ 2)) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const).tendsto 0
      |>.mono_left nhdsWithin_le_nhds
  rw [sub_zero, mul_one] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact seg t ht.1 ht.2.le

lemma band {xbar a : ℝ} (hmax : IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) a) (h0 : 0 < a)
    (h1 : a < xbar) : -km ≤ alpha - c * a ∧ alpha - c * a ≤ kp := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hε : 0 < min (a / 2) ((-km - (alpha - c * a)) / c) := lt_min (by linarith) (div_pos (by linarith) hc)
    set ε := min (a / 2) ((-km - (alpha - c * a)) / c)
    have hεa : ε ≤ a / 2 := min_le_left _ _
    have hεc : c * ε ≤ -km - (alpha - c * a) := by
      have := min_le_right (a / 2) ((-km - (alpha - c * a)) / c)
      rw [le_div_iff₀ hc] at this; linarith
    have hle : psi alpha c kp km xm (a - ε) ≤ psi alpha c kp km xm a := hmax ⟨by linarith, by linarith⟩
    have hd := psi_diff alpha c kp km xm a (a - ε)
    have hcost := cost_change kp km xm a (a - ε) hkp hkm
    rw [show a - ε - a = -ε by ring, show a - (a - ε) = ε by ring, max_eq_right (show -ε ≤ 0 by linarith),
      max_eq_left hε.le] at hcost
    simp only [cst] at hd
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hε : 0 < min ((xbar - a) / 2) (((alpha - c * a) - kp) / c) :=
      lt_min (by linarith) (div_pos (by linarith) hc)
    set ε := min ((xbar - a) / 2) (((alpha - c * a) - kp) / c)
    have hεa : ε ≤ (xbar - a) / 2 := min_le_left _ _
    have hεc : c * ε ≤ (alpha - c * a) - kp := by
      have := min_le_right ((xbar - a) / 2) (((alpha - c * a) - kp) / c)
      rw [le_div_iff₀ hc] at this; linarith
    have hle : psi alpha c kp km xm (a + ε) ≤ psi alpha c kp km xm a := hmax ⟨by linarith, by linarith⟩
    have hd := psi_diff alpha c kp km xm a (a + ε)
    have hcost := cost_change kp km xm a (a + ε) hkp hkm
    rw [show a + ε - a = ε by ring, show a - (a + ε) = -ε by ring, max_eq_left hε.le,
      max_eq_right (show -ε ≤ 0 by linarith)] at hcost
    simp only [cst] at hd
    nlinarith

end Psi

theorem bracket : Bracket := by
  intro alpha c kp km xm xbar aJ as hc hkp hkm haJ hmax has
  dsimp only
  have hmx2 := le_max_left (alpha - c * aJ - kp) (-km - (alpha - c * aJ))
  have hmx3 := le_max_right (alpha - c * aJ - kp) (-km - (alpha - c * aJ))
  have hmx1 := le_max_right (0 : ℝ) (max (alpha - c * aJ - kp) (-km - (alpha - c * aJ)))
  refine ⟨lower_end hc hkp hkm haJ hmax has, upper_end hc hkp hkm aJ as _ (by linarith) (by linarith),
    fun h0 h1 => ?_⟩
  obtain ⟨b1, b2⟩ := band hc hkp hkm hmax h0 h1
  exact max_eq_left (max_le (by linarith) (by linarith))

/-! ### Part 1: the reference case and the transfer -/

lemma mom_dot {S : Type} [Fintype S] {a b : ℕ} (q : S → ℝ) (x : S → Fin a → ℝ) (y : S → Fin b → ℝ)
    (u : Fin a → ℝ) (v : Fin b → ℝ) :
    ∑ s, q s * ((u ⬝ᵥ x s) * (v ⬝ᵥ y s)) = u ⬝ᵥ (mom q x y *ᵥ v) := by
  simp only [mom, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun s j => ∑ i, q s * (u i * x s i * (v j * y s j)))]
  simp_rw [Finset.sum_comm (f := fun s i => q s * (u i * x s i * (v _ * y s _)))]
  rw [Finset.sum_comm (f := fun j i => ∑ s, q s * (u i * x s i * (v j * y s j)))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

lemma psd_factor {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, A = R * Rᵀ := by
  set U : Matrix (Fin k) (Fin k) ℝ := (hA.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  set ev := hA.1.eigenvalues
  have hspec := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hev : ∀ i, 0 ≤ ev i := hA.eigenvalues_nonneg
  refine ⟨U * diagonal (fun i => Real.sqrt (ev i)), ?_⟩
  rw [transpose_mul, diagonal_transpose, ← hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal]
  have hf : (fun i => Real.sqrt (ev i) * Real.sqrt (ev i)) = RCLike.ofReal ∘ ev :=
    funext fun i => by simp [Real.mul_self_sqrt (hev i)]
  rw [hf, ← Matrix.mul_assoc]
  exact hspec

section Rep

variable (K m n : ℕ)

/-- The scenario type: one idle scenario, and `±` along each column of each block's square root. -/
abbrev RepS := Option ((Fin K ⊕ Fin m ⊕ Fin n) × Bool)

def repL : ℝ := ((K + m + n : ℕ) : ℝ) + 1

def repq : RepS K m n → ℝ
  | none => 1 / repL K m n
  | some _ => 1 / (2 * repL K m n)

def sg (b : Bool) : ℝ := if b then 1 else -1

variable {K m n}

def repf (Rf : Matrix (Fin K) (Fin K) ℝ) : RepS K m n → Fin K → ℝ
  | some (Sum.inl k, b) => fun i => sg b * Real.sqrt (repL K m n) * Rf i k
  | _ => 0

def repA (RV : Matrix (Fin m) (Fin m) ℝ) : RepS K m n → Fin m → ℝ
  | some (Sum.inr (Sum.inl j), b) => fun i => sg b * Real.sqrt (repL K m n) * RV i j
  | _ => 0

def repE (RE : Matrix (Fin n) (Fin n) ℝ) : RepS K m n → Fin n → ℝ
  | some (Sum.inr (Sum.inr j), b) => fun i => sg b * Real.sqrt (repL K m n) * RE i j
  | _ => 0

lemma repL_pos : 0 < repL K m n := by unfold repL; positivity

lemma sqrtL : Real.sqrt (repL K m n) * Real.sqrt (repL K m n) = repL K m n :=
  Real.mul_self_sqrt repL_pos.le

lemma repq_sum : ∑ s, repq K m n s = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [repq, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
  have := repL_pos (K := K) (m := m) (n := n)
  unfold repL at this ⊢
  field_simp
  push_cast
  ring

lemma sq_term (a b : ℝ) : 1 / (2 * repL K m n) * (√(repL K m n) * a * (√(repL K m n) * b)) +
    1 / (2 * repL K m n) * (-√(repL K m n) * a * (-√(repL K m n) * b)) = a * b := by
  have h := sqrtL (K := K) (m := m) (n := n)
  have hL := (repL_pos (K := K) (m := m) (n := n)).ne'
  rw [show √(repL K m n) * a * (√(repL K m n) * b) = (√(repL K m n) * √(repL K m n)) * (a * b) by ring,
    show -√(repL K m n) * a * (-√(repL K m n) * b) = (√(repL K m n) * √(repL K m n)) * (a * b) by ring, h]
  field_simp
  ring

lemma mom_f (Rf : Matrix (Fin K) (Fin K) ℝ) :
    mom (repq K m n) (repf (m := m) (n := n) Rf) (repf Rf) = Rf * Rfᵀ := by
  funext i j
  simp only [mom, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_bool,
    repq, repf, sg, mul_apply, transpose_apply, ite_true, Bool.false_eq_true, ite_false]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, one_mul,
    neg_one_mul, sq_term]

lemma mom_A (RV : Matrix (Fin m) (Fin m) ℝ) :
    mom (repq K m n) (repA (K := K) (n := n) RV) (repA RV) = RV * RVᵀ := by
  funext i j
  simp only [mom, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_bool,
    repq, repA, sg, mul_apply, transpose_apply, ite_true, Bool.false_eq_true, ite_false]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, one_mul,
    neg_one_mul, sq_term]

lemma mom_E (RE : Matrix (Fin n) (Fin n) ℝ) :
    mom (repq K m n) (repE (K := K) (m := m) RE) (repE RE) = RE * REᵀ := by
  funext i j
  simp only [mom, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_bool,
    repq, repE, sg, mul_apply, transpose_apply, ite_true, Bool.false_eq_true, ite_false]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, one_mul,
    neg_one_mul, sq_term]

lemma mom_cross (Rf : Matrix (Fin K) (Fin K) ℝ) (RV : Matrix (Fin m) (Fin m) ℝ) (RE : Matrix (Fin n) (Fin n) ℝ) :
    mom (repq K m n) (repA RV) (repE RE) = 0 ∧ mom (repq K m n) (repf Rf) (repA RV) = 0 ∧
      mom (repq K m n) (repf Rf) (repE RE) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i j <;>
    simp [mom, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_sum_type, repq, repA, repE, repf]

lemma mean_zero {a : ℕ} (z : RepS K m n → Fin a → ℝ) (hz0 : z none = 0)
    (hz : ∀ x, z (some (x, false)) = -z (some (x, true))) : ∑ s, repq K m n s • z s = 0 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hz0, smul_zero, zero_add, repq, hz, smul_neg, add_neg_cancel,
    Finset.sum_const_zero]

end Rep

theorem represent : Represent := by
  intro m n K Sf V SE hSf hV hSE
  obtain ⟨Rf, hRf⟩ := psd_factor hSf
  obtain ⟨RV, hRV⟩ := psd_factor hV
  obtain ⟨RE, hRE⟩ := psd_factor hSE
  obtain ⟨c1, c2, c3⟩ := mom_cross (m := m) (n := n) Rf RV RE
  refine ⟨RepS K m n, inferInstance, repq K m n, repf Rf, repA RV, repE RE, fun s => ?_, repq_sum,
    mean_zero _ rfl fun x => ?_, mean_zero _ rfl fun x => ?_, mean_zero _ rfl fun x => ?_,
    (mom_f Rf).trans hRf.symm, (mom_A RV).trans hRV.symm, (mom_E RE).trans hRE.symm, c1, c2, c3⟩
  · have := repL_pos (K := K) (m := m) (n := n)
    cases s <;> simp only [repq] <;> positivity
  all_goals
    rcases x with k | k | k <;> funext i <;> simp [repf, repA, repE, sg]

lemma cross_zero {m n K : ℕ} {S : Type} [Fintype S] {D : Data m n K S} {Sf V SE}
    (hR : RefCase D Sf V SE) (w : Inst m n → ℝ) : Standalone.M2TwoStageSeparation.crossM D w = 0 := by
  obtain ⟨_, _, _, _, h5, h6⟩ := hR
  funext k
  have e : Standalone.M2TwoStageSeparation.crossM D w k =
      ∑ i, active w i * mom D.q D.zf D.zA k i + ∑ j, etf w j * mom D.q D.zf D.zE k j := by
    simp only [Standalone.M2TwoStageSeparation.crossM, Standalone.M2TwoStageSeparation.rres, mom,
      dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> rw [Finset.sum_comm] <;> exact Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  rw [e, h5, h6]; simp

lemma res_eq {m n K : ℕ} {S : Type} [Fintype S] {D : Data m n K S} {Sf V SE}
    (hR : RefCase D Sf V SE) (w : Inst m n → ℝ) : Standalone.M2TwoStageSeparation.resM D w =
      active w ⬝ᵥ (V *ᵥ active w) + etf w ⬝ᵥ (SE *ᵥ etf w) := by
  obtain ⟨_, h2, h3, h4, _, _⟩ := hR
  have e1 := mom_dot D.q D.zA D.zA (active w) (active w)
  have e2 := mom_dot D.q D.zA D.zE (active w) (etf w)
  have e3 := mom_dot D.q D.zE D.zE (etf w) (etf w)
  rw [h2] at e1
  rw [h4, zero_mulVec, dotProduct_zero] at e2
  rw [h3] at e3
  rw [← e1, ← e3]
  have : Standalone.M2TwoStageSeparation.resM D w = ∑ s, D.q s * ((active w ⬝ᵥ D.zA s) * (active w ⬝ᵥ D.zA s)) +
      2 * ∑ s, D.q s * ((active w ⬝ᵥ D.zA s) * (etf w ⬝ᵥ D.zE s)) +
      ∑ s, D.q s * ((etf w ⬝ᵥ D.zE s) * (etf w ⬝ᵥ D.zE s)) := by
    simp only [Standalone.M2TwoStageSeparation.resM, Standalone.M2TwoStageSeparation.rres, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this, e2]
  ring

theorem transfer : Transfer := by
  intro m n K S _ D θ Sf V SE hin hR
  refine ⟨hR.1, cross_zero hR, res_eq hR,
    (Novel.M2TwoStageSeparationProof.splitThm.2.2 m n K S D θ hin).2.2.2.2.2.1 fun w _ => cross_zero hR w⟩

/-! ### Part 2a: the band holding -/

section BandHold

variable {alpha c kp km xm : ℝ}

/-- A slope `t ∈ T(h)` is a subgradient of the cost at `h`. -/
lemma cst_sub {h t : ℝ} (ht1 : -km ≤ t) (ht2 : t ≤ kp) (htp : xm < h → t = kp)
    (htm : h < xm → t = -km) (a : ℝ) : t * (a - h) ≤ cst kp km xm a - cst kp km xm h := by
  have h1 : t * (a - xm) ≤ cst kp km xm a := by
    simp only [cst]
    rcases le_total a xm with ha | ha
    · rw [max_eq_right (by linarith : a - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - a)]
      nlinarith [mul_le_mul_of_nonneg_right ht1 (by linarith : 0 ≤ xm - a)]
    · rw [max_eq_left (by linarith : 0 ≤ a - xm), max_eq_right (by linarith : xm - a ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_right ht2 (by linarith : 0 ≤ a - xm)]
  have h2 : cst kp km xm h = t * (h - xm) := by
    simp only [cst]
    rcases lt_trichotomy h xm with hh | hh | hh
    · rw [htm hh, max_eq_right (by linarith : h - xm ≤ 0), max_eq_left (by linarith : 0 ≤ xm - h)]; ring
    · subst hh; simp
    · rw [htp hh, max_eq_left (by linarith : 0 ≤ h - xm), max_eq_right (by linarith : xm - h ≤ 0)]; ring
  have e : t * (a - h) = t * (a - xm) - t * (h - xm) := by ring
  linarith

/-- The one-variable case of part 0: `h` maximizes `ψ` on the box when its marginal less a slope in
`T(h)` points into the box's normal cone. -/
lemma max_of_slope {xbar h t : ℝ} (hc : 0 < c) (ht1 : -km ≤ t) (ht2 : t ≤ kp)
    (htp : xm < h → t = kp) (htm : h < xm → t = -km)
    (hR : ∀ a ∈ Set.Icc 0 xbar, (alpha - c * h - t) * (a - h) ≤ 0) :
    IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) h := by
  intro a ha
  show psi alpha c kp km xm a ≤ psi alpha c kp km xm h
  have hd := psi_diff alpha c kp km xm h a
  have hs := cst_sub (xm := xm) ht1 ht2 htp htm a
  have hr := hR a ha
  have e : (alpha - c * h - t) * (a - h) = (alpha - c * h) * (a - h) - t * (a - h) := by ring
  nlinarith [mul_nonneg hc.le (sq_nonneg (h - a))]

lemma bandHold_mem {xbar : ℝ} (hx : 0 ≤ xbar) :
    bandHold alpha c kp km xm xbar ∈ Set.Icc 0 xbar :=
  ⟨le_max_left _ _, max_le hx (min_le_left _ _)⟩

/-- The band holding maximizes `ψ` on `[0, x̄]`. -/
lemma bandHold_max {xbar : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (hx : 0 ≤ xbar) :
    IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) (bandHold alpha c kp km xm xbar) := by
  have clo : c * ((alpha - kp) / c) = alpha - kp := by field_simp
  have chi : c * ((alpha + km) / c) = alpha + km := by field_simp
  have hlh : (alpha - kp) / c ≤ (alpha + km) / c := div_le_div_of_nonneg_right (by linarith) hc.le
  unfold bandHold
  generalize (alpha - kp) / c = lo at clo hlh ⊢
  generalize (alpha + km) / c = hi at chi hlh ⊢
  have hu : (xm < lo ∧ max lo (min hi xm) = lo) ∨ (hi < xm ∧ max lo (min hi xm) = hi) ∨
      (lo ≤ xm ∧ xm ≤ hi ∧ max lo (min hi xm) = xm) := by
    rcases lt_or_ge xm lo with h1 | h1
    · exact Or.inl ⟨h1, max_eq_left (le_trans (min_le_right _ _) h1.le)⟩
    · rcases lt_or_ge hi xm with h2 | h2
      · exact Or.inr (Or.inl ⟨h2, by rw [min_eq_left h2.le, max_eq_right hlh]⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, by rw [min_eq_right h2, max_eq_right h1]⟩)
  generalize max lo (min hi xm) = u at hu
  rcases le_or_gt u 0 with hu0 | hu0
  · rw [max_eq_left (le_trans (min_le_right _ _) hu0)]
    have cu : c * u ≤ 0 := by nlinarith
    have key : ∃ t, -km ≤ t ∧ t ≤ kp ∧ (xm < 0 → t = kp) ∧ (0 < xm → t = -km) ∧ alpha - t ≤ 0 := by
      rcases hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
      · exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (by linarith), by linarith⟩
      · rcases lt_or_ge 0 xm with hx0 | hx0
        · exact ⟨-km, le_rfl, by linarith, fun h => absurd h (by linarith), fun _ => rfl, by linarith⟩
        · exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (by linarith), by linarith⟩
      · have : c * lo ≤ c * u := mul_le_mul_of_nonneg_left h1 hc.le
        exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (by linarith), by linarith⟩
    obtain ⟨t, ht1, ht2, htp, htm, hR⟩ := key
    refine max_of_slope hc ht1 ht2 (by simpa using htp) (by simpa using htm) fun a ha => ?_
    nlinarith [ha.1]
  · rcases le_or_gt xbar u with hux | hux
    · rw [min_eq_left hux, max_eq_right hx]
      have cu : c * xbar ≤ c * u := mul_le_mul_of_nonneg_left hux hc.le
      have key : ∃ t, -km ≤ t ∧ t ≤ kp ∧ (xm < xbar → t = kp) ∧ (xbar < xm → t = -km) ∧
          0 ≤ alpha - c * xbar - t := by
        rcases hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
        · rcases le_or_gt xm xbar with hx1 | hx1
          · exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (by linarith), by linarith⟩
          · exact ⟨-km, le_rfl, by linarith, fun h => absurd h (by linarith), fun _ => rfl, by linarith⟩
        · exact ⟨-km, le_rfl, by linarith, fun h => absurd h (by linarith), fun _ => rfl, by linarith⟩
        · have a1 : c * lo ≤ c * u := mul_le_mul_of_nonneg_left h1 hc.le
          have a2 : c * u ≤ c * hi := mul_le_mul_of_nonneg_left h2 hc.le
          rcases lt_or_eq_of_le hux with hx1 | hx1
          · exact ⟨-km, le_rfl, by linarith, fun h => absurd h (by linarith), fun _ => rfl, by linarith⟩
          · exact ⟨alpha - c * u, by linarith, by linarith, fun h => absurd h (by linarith),
              fun h => absurd h (by linarith), by rw [hx1]; linarith⟩
      obtain ⟨t, ht1, ht2, htp, htm, hR⟩ := key
      refine max_of_slope hc ht1 ht2 htp htm fun a ha => ?_
      nlinarith [ha.2]
    · rw [min_eq_right hux.le, max_eq_right hu0.le]
      have key : ∃ t, -km ≤ t ∧ t ≤ kp ∧ (xm < u → t = kp) ∧ (u < xm → t = -km) ∧
          alpha - c * u - t = 0 := by
        rcases hu with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
        · exact ⟨kp, by linarith, le_rfl, fun _ => rfl, fun h => absurd h (by linarith), by linarith⟩
        · exact ⟨-km, le_rfl, by linarith, fun h => absurd h (by linarith), fun _ => rfl, by linarith⟩
        · have a1 : c * lo ≤ c * u := mul_le_mul_of_nonneg_left h1 hc.le
          have a2 : c * u ≤ c * hi := mul_le_mul_of_nonneg_left h2 hc.le
          exact ⟨alpha - c * u, by linarith, by linarith, fun h => absurd h (lt_irrefl _),
            fun h => absurd h (lt_irrefl _), by ring⟩
      obtain ⟨t, ht1, ht2, htp, htm, hR⟩ := key
      refine max_of_slope hc ht1 ht2 htp htm fun a ha => ?_
      rw [hR, zero_mul]

/-- `ψ` has one maximizer on the box. -/
lemma max_unique {xbar a b : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (ha : a ∈ Set.Icc 0 xbar)
    (hb : b ∈ Set.Icc 0 xbar) (hma : IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) a)
    (hmb : IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) b) : a = b := by
  have h1 := lower_end hc hkp hkm ha hma hb
  have h3 : psi alpha c kp km xm a ≤ psi alpha c kp km xm b := hmb ha
  have : (a - b) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- A maximizer of `ψ` on the box is the band holding. -/
lemma eq_bandHold {xbar a : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (ha : a ∈ Set.Icc 0 xbar)
    (hma : IsMaxOn (psi alpha c kp km xm) (Set.Icc 0 xbar) a) : a = bandHold alpha c kp km xm xbar :=
  max_unique hc hkp hkm ha (bandHold_mem (ha.1.trans ha.2)) hma
    (bandHold_max hc hkp hkm (ha.1.trans ha.2))

end BandHold

/-! ### Part 2a: spanning frictionless ETFs -/

section Spanning

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN sigF Inputs)

/-- Every fund in its box; ETFs and cash free. -/
def fundBox {m n K : ℕ} (D : Data m n K S) : Set (Inst m n → ℝ) :=
  {w | ∀ i, 0 ≤ w (Sum.inl i) ∧ w (Sum.inl i) ≤ D.wbar (Sum.inl i)}

/-- A concave `f` maximal on `F ∩ A` (`A` convex) at a point `x` with a slack budget and every
coordinate in `P` strictly inside its box is maximal on the points of `A` that keep only the other
coordinates in their boxes: the segment toward such a point starts inside `F ∩ A`. -/
lemma drop_slack_gen {m n K : ℕ} {D : Data m n K S} (P : Inst m n → Prop)
    (f : (Inst m n → ℝ) → ℝ)
    (hf : ∀ (x y : Inst m n → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      (1 - ε) * f x + ε * f y ≤ f ((1 - ε) • x + ε • y))
    {A : Set (Inst m n → ℝ)} (hA : Convex ℝ A) {x : Inst m n → ℝ} (hxF : x ∈ F D) (hxA : x ∈ A)
    (hmax : ∀ w ∈ F D, w ∈ A → f w ≤ f x) (hk : 0 < cash D x)
    (hP : ∀ l, P l → 0 < x l ∧ x l < D.wbar l)
    {z : Inst m n → ℝ} (hzA : z ∈ A) (hz : ∀ l, ¬ P l → 0 ≤ z l ∧ z l ≤ D.wbar l) : f z ≤ f x := by
  let y : ℝ → Inst m n → ℝ := fun ε => (1 - ε) • x + ε • z
  have hyc : Continuous y := by fun_prop
  have hy0 : y 0 = x := by simp [y]
  have ev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < cash D (y ε) := by
    have h : Tendsto (fun ε => cash D (y ε)) (𝓝 0) (𝓝 (cash D x)) := by
      rw [← hy0]; exact ((Novel.M2ActionClassesProof.continuous_cash D).comp hyc).tendsto 0
    exact h.eventually (lt_mem_nhds hk)
  have ev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ l, P l → 0 < y ε l ∧ y ε l < D.wbar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : P l
    · have h : Tendsto (fun ε => y ε l) (𝓝 0) (𝓝 (x l)) := by
        rw [← hy0]; exact ((continuous_apply _).comp hyc).tendsto 0
      exact ((h.eventually (lt_mem_nhds (hP l hl).1)).and (h.eventually (gt_mem_nhds (hP l hl).2))).mono
        fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hl
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (((ev1.and ev2).filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have hyF : y ε ∈ F D := by
    refine ⟨fun l => ?_, h1.le⟩
    by_cases hl : P l
    · exact ⟨(h2 l hl).1.le, (h2 l hl).2.le⟩
    · have a1 := hxF.1 l
      have a2 := hz l hl
      simp only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor <;> nlinarith [h3.1, h3.2]
  have hyA : y ε ∈ A := hA hxA hzA (by linarith [h3.2]) h3.1.le (by ring)
  have hc := hf x z ε h3.1.le h3.2.le
  have hle : f (y ε) ≤ f x := hmax _ hyF hyA
  have : ε * f z ≤ ε * f x := by simp only [y] at hle; nlinarith
  exact le_of_mul_le_mul_left this h3.1

lemma score_ineq {m n K : ℕ} {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
    (x y : Inst m n → ℝ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (1 - ε) * score D x θ + ε * score D y θ ≤ score D ((1 - ε) • x + ε • y) θ :=
  Novel.M2ActionClassesProof.score_concave D hI.2.2.2 hI.2.1 hI.2.2.1 (by linarith) h0 (by ring) x y θ

/-- At a joint optimum with a slack budget and every ETF strictly inside its box, the score is
maximal on the fund box too. -/
lemma drop_slack {m n K : ℕ} {D : Data m n K S} (θ : Params m K) (hI : Inputs D)
    {wJ : Inst m n → ℝ} (hwJ : wJ ∈ F D) (hmax : IsMaxOn (fun w => score D w θ) (F D) wJ)
    (hk : 0 < cash D wJ) (hE : ∀ j, 0 < wJ (Sum.inr j) ∧ wJ (Sum.inr j) < D.wbar (Sum.inr j))
    {z : Inst m n → ℝ} (hz : z ∈ fundBox D) : score D z θ ≤ score D wJ θ := by
  have hP : ∀ l : Inst m n, l.isRight = true → 0 < wJ l ∧ wJ l < D.wbar l := by
    rintro (l | l) hl
    · simp at hl
    · exact hE l
  have hZ : ∀ l : Inst m n, ¬ l.isRight = true → 0 ≤ z l ∧ z l ≤ D.wbar l := by
    rintro (l | l) hl
    · exact hz l
    · simp at hl
  exact drop_slack_gen _ (fun w => score D w θ) (score_ineq θ hI) convex_univ hwJ (Set.mem_univ _)
    (fun w hw _ => hmax hw) hk hP (Set.mem_univ _) hZ

/-- With frictionless residual-free ETFs and `V = diag v`, `Q(w) = G(b(w)) + Σ_i ψ_i(a_i)`. -/
lemma score_span {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ}
    {v : Fin m → ℝ} (hR : RefCase D Sf (diagonal v) 0) (hcE : D.cE = 0)
    (hkE : ∀ j, D.kplus (Sum.inr j) = 0 ∧ D.kminus (Sum.inr j) = 0) (w : Inst m n → ℝ) :
    score D w θ = Gf D θ (exposure D w) + ∑ i, psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i)) (w (Sum.inl i)) := by
  rw [Novel.M2TwoStageSeparationProof.split]
  congr 1
  rw [Hr, cross_zero hR, res_eq hR, hcE]
  simp only [tau, Fintype.sum_sum_type, hkE, zero_mul, add_zero, dotProduct_zero, zero_mulVec,
    mul_zero, psi, Pi.sub_apply]
  rw [Finset.sum_const_zero, add_zero, sub_zero, zero_add]
  simp only [dotProduct, mulVec_diagonal, active, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_sub]
  ring

/-- With `B^E` invertible, every fund vector and exposure is realized by some holding. -/
lemma realize {m K : ℕ} (D : Data m K K S) (hBE : IsUnit D.BE.det) (a : Fin m → ℝ) (b : Fin K → ℝ) :
    exposure D (Sum.elim a ((D.BEᵀ)⁻¹ *ᵥ (b - D.BAᵀ *ᵥ a))) = b := by
  have hU : IsUnit D.BEᵀ.det := by rwa [det_transpose]
  show D.BAᵀ *ᵥ a + D.BEᵀ *ᵥ ((D.BEᵀ)⁻¹ *ᵥ (b - D.BAᵀ *ᵥ a)) = b
  rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  abel

lemma sum_update_le {m : ℕ} (f : Fin m → ℝ → ℝ) (a : Fin m → ℝ) (i : Fin m) (y : ℝ)
    (h : ∑ k, f k (Function.update a i y k) ≤ ∑ k, f k (a k)) : f i y ≤ f i (a i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Function.update_self] at h
  have : ∑ k ∈ Finset.univ.erase i, f k (Function.update a i y k) =
      ∑ k ∈ Finset.univ.erase i, f k (a k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  linarith

/-- `G` around its unconstrained maximizer. -/
lemma G_TB {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {bTB : Fin K → ℝ}
    (h : D.gamma • (sigF D *ᵥ bTB) = θ.lam) (b : Fin K → ℝ) :
    Gf D θ b = Gf D θ bTB - D.gamma / 2 * sqN D (b - bTB) := by
  rw [Novel.M2TwoStageSeparationProof.G_expand D θ b bTB, h, sub_self, dotProduct_zero, add_zero]

lemma sqN_zero {m n K : ℕ} {D : Data m n K S} {Sf : Matrix (Fin K) (Fin K) ℝ} (hsig : sigF D = Sf)
    (hSf : Sf.PosDef) {x : Fin K → ℝ} (hx : sqN D x ≤ 0) : x = 0 := by
  by_contra h
  have := hSf.dotProduct_mulVec_pos h
  simp only [star_trivial] at this
  simp only [sqN, hsig] at hx
  linarith

lemma sqN_nonpos {g x : ℝ} (hg : 0 < g) (h : g / 2 * x ≤ 0) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  have := mul_pos (half_pos hg) hx
  linarith

theorem spanning : Spanning := by
  intro m K S _ D θ Sf v hI hFS wJ hwJ hmax hk hE
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ⟩ := hFS
  have hsig : sigF D = Sf := hR.1
  have hkp : ∀ i, 0 ≤ D.kplus i := fun i => (hI.2.1 i).1
  have hkm : ∀ i, 0 ≤ D.kminus i := fun i => (hI.2.1 i).2
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  intro bTB
  have hTB : D.gamma • (sigF D *ᵥ bTB) = θ.lam := by
    rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hG := G_TB θ hTB
  have key : ∀ z ∈ fundBox D, score D z θ ≤ score D wJ θ := fun z hz =>
    drop_slack θ hI hwJ hmax hk hE hz
  have dec := score_span θ hR hcE hkE
  have hbox : ∀ i, wJ (Sum.inl i) ∈ Set.Icc 0 (D.wbar (Sum.inl i)) := fun i => hwJ.1 (Sum.inl i)
  -- the exposure
  have hbJ : exposure D wJ = bTB := by
    have hz : (Sum.elim (active wJ) ((D.BEᵀ)⁻¹ *ᵥ (bTB - D.BAᵀ *ᵥ active wJ)) : Inst m K → ℝ) ∈
        fundBox D := fun i => hbox i
    have h1 := key _ hz
    rw [dec, dec wJ, realize D hBE] at h1
    simp only [Sum.elim_inl] at h1
    have h2 := hG (exposure D wJ)
    simp only [active] at h1
    rw [add_le_add_iff_right] at h1
    have h3 := sqN_nonpos hγ (show D.gamma / 2 * sqN D (exposure D wJ - bTB) ≤ 0 by linarith)
    exact sub_eq_zero.mp (sqN_zero hsig hSf h3)
  -- the funds
  have hfund : ∀ i, IsMaxOn (psi (θ.alpha i) (D.gamma * v i) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))) (Set.Icc 0 (D.wbar (Sum.inl i))) (wJ (Sum.inl i)) := by
    intro i y hy
    let a2 := Function.update (active wJ) i y
    have hz : (Sum.elim a2 ((D.BEᵀ)⁻¹ *ᵥ (exposure D wJ - D.BAᵀ *ᵥ a2)) : Inst m K → ℝ) ∈
        fundBox D := fun k => by
      show a2 k ∈ Set.Icc 0 (D.wbar (Sum.inl k))
      by_cases hki : k = i
      · subst hki; simpa [a2] using hy
      · simpa [a2, hki, active] using hbox k
    have h1 := key _ hz
    rw [dec, dec wJ, realize D hBE] at h1
    simp only [Sum.elim_inl, add_le_add_iff_left] at h1
    exact sum_update_le (fun k => psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k))) (active wJ) i y h1
  have hc : ∀ i, 0 < D.gamma * v i := fun i => mul_pos hγ (hv i)
  refine ⟨hbJ, fun i => eq_bandHold (hc i) (hkp _) (hkm _) (hbox i) (hfund i), ?_, ?_, ?_, ?_, ?_⟩
  · -- the ETFs
    have hU' : IsUnit D.BEᵀ.det := by rwa [det_transpose]
    rw [← hbJ]
    show etf wJ = (D.BEᵀ)⁻¹ *ᵥ (D.BAᵀ *ᵥ active wJ + D.BEᵀ *ᵥ etf wJ - D.BAᵀ *ᵥ active wJ)
    rw [add_sub_cancel_left, mulVec_mulVec, nonsing_inv_mul _ hU', one_mulVec]
  · -- stage 1
    intro bs _ hmaxG
    have h1 : Gf D θ bTB ≤ Gf D θ bs := hmaxG ⟨wJ, hwJ, hbJ⟩
    have h2 := hG bs
    have h3 := sqN_nonpos hγ (show D.gamma / 2 * sqN D (bs - bTB) ≤ 0 by linarith)
    exact sub_eq_zero.mp (sqN_zero hsig hSf h3)
  · -- stage 2
    intro w₂ hw₂ hmax₂
    have h1 : Hr D θ wJ ≤ Hr D θ w₂ := hmax₂ ⟨hwJ, hbJ⟩
    have h2 : score D wJ θ ≤ score D w₂ θ := by
      rw [Novel.M2TwoStageSeparationProof.split, Novel.M2TwoStageSeparationProof.split D θ w₂, hbJ,
        hw₂.2]
      linarith
    rw [dec, dec w₂, hbJ, hw₂.2, add_le_add_iff_left] at h2
    have hle : ∀ k ∈ Finset.univ, psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
        (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (w₂ (Sum.inl k)) ≤
        psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
        (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (wJ (Sum.inl k)) :=
      fun k _ => hfund k (hw₂.1.1 (Sum.inl k))
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) h2)
    funext k
    refine max_unique (hc k) (hkp _) (hkm _) (hw₂.1.1 (Sum.inl k)) (hbox k) (fun y hy => ?_) (hfund k)
    show _ ≤ psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
      (w0 D (Sum.inl k)) (w₂ (Sum.inl k))
    rw [heq k (Finset.mem_univ k)]
    exact hfund k hy
  · -- T = J
    rw [(Novel.M2TwoStageSeparationProof.J_eq θ hI hwJ hmax).1, hbJ]
  · -- the soft procedure
    intro R hRB bs hbs hmaxR
    have h1 : Gf D θ bTB ≤ Gf D θ bs := hmaxR (hRB ⟨wJ, hwJ, hbJ⟩)
    have h2 := hG bs
    have h3 := sqN_nonpos hγ (show D.gamma / 2 * sqN D (bs - bTB) ≤ 0 by linarith)
    have hbs' : bs = bTB := sub_eq_zero.mp (sqN_zero hsig hSf h3)
    have hnu : Standalone.M2SoftTargetTwoStage.nu D θ bs = 0 := by
      rw [hbs']
      change θ.lam - D.gamma • (sigF D *ᵥ bTB) = 0
      rw [hTB, sub_self]
    refine ⟨hnu, fun w₂ hw₂ hm₂ => ?_⟩
    have h4 := (Novel.M2SoftTargetTwoStageProof.identification m K K S D θ bs).2.2 (F D) hnu w₂ hw₂ hm₂
    exact le_antisymm (hmax hw₂) (h4 hwJ)

end Spanning

/-! ### Part 2c: one unreachable fund -/

section Hedge

open Standalone.M5MissingDirectionLeak (PiR PiU RRinv Jmap Schur)
open Novel.M5MissingDirectionLeakProof

variable {K n : ℕ} {BE : Matrix (Fin n) (Fin K) ℝ} {Sg : Matrix (Fin K) (Fin K) ℝ}
  (hBE : IsUnit (BE * BEᵀ).det) (hSg : Sg.PosDef)
include hBE hSg

lemma schur_sym : (Schur BE Sg)ᵀ = Schur BE Sg :=
  Novel.M5PartialAdjustmentSplitProof.transpose_of_psd (schur_psd hBE hSg)

lemma schur_kill {y : Fin K → ℝ} (hy : PiU BE *ᵥ y = 0) : Schur BE Sg *ᵥ y = 0 := by
  rw [schur_pu hBE hSg, ← mulVec_mulVec, hy, mulVec_zero]

/-- The Schur form ignores components in `L_E`. -/
lemma schur_form_add (x : Fin K → ℝ) {y : Fin K → ℝ} (hy : PiU BE *ᵥ y = 0) :
    (x + y) ⬝ᵥ (Schur BE Sg *ᵥ (x + y)) = x ⬝ᵥ (Schur BE Sg *ᵥ x) := by
  have h0 := schur_kill hBE hSg hy
  have hs : y ⬝ᵥ (Schur BE Sg *ᵥ x) = 0 := by
    rw [Novel.M5PartialAdjustmentSplitProof.sym_dot (schur_sym hBE hSg), h0, dotProduct_zero]
  rw [mulVec_add, h0, add_zero, add_dotProduct, hs, add_zero]

/-- `s_U > 0` when the unreachable part `u = Π_U β` is nonzero. -/
lemma sU_pos {β : Fin K → ℝ} (hu : PiU BE *ᵥ β ≠ 0) : 0 < β ⬝ᵥ (Schur BE Sg *ᵥ β) := by
  have hsplit : β = PiU BE *ᵥ β + PiR BE *ᵥ β := by
    rw [← add_mulVec, add_comm, pr_add_pu hBE, one_mulVec]
  have hr : PiU BE *ᵥ (PiR BE *ᵥ β) = 0 := by rw [mulVec_mulVec, pu_pr hBE, zero_mulVec]
  have hur : PiR BE *ᵥ (PiU BE *ᵥ β) = 0 := by rw [mulVec_mulVec, pr_pu hBE, zero_mulVec]
  rw [hsplit, schur_form_add hBE hSg _ hr]
  exact schur_pd_u hBE hSg hur hu

/-- `γ Σ~_{U.R} b₀ = J'λ` when `γ Σ~ b₀ = λ`. -/
lemma schur_b0 {g : ℝ} {b0 lam : Fin K → ℝ} (hb0 : g • (Sg *ᵥ b0) = lam) :
    g • (Schur BE Sg *ᵥ b0) = (Jmap BE Sg)ᵀ *ᵥ lam := by
  rw [← schur_eq hBE hSg, jt_eq hBE hSg, ← hb0]
  simp only [sub_mulVec, one_mulVec, mulVec_smul, smul_sub, ← mulVec_mulVec]

/-- The Schur form along `a β - b₀`. -/
lemma schur_line (b0 β : Fin K → ℝ) (a : ℝ) :
    (a • β - b0) ⬝ᵥ (Schur BE Sg *ᵥ (a • β - b0)) =
      a ^ 2 * (β ⬝ᵥ (Schur BE Sg *ᵥ β)) - 2 * a * (β ⬝ᵥ (Schur BE Sg *ᵥ b0)) +
        b0 ⬝ᵥ (Schur BE Sg *ᵥ b0) := by
  have hs := Novel.M5PartialAdjustmentSplitProof.sym_dot (schur_sym hBE hSg) b0 β
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  rw [hs]
  ring

end Hedge

section Unreach

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN sigF Inputs)
open Standalone.M5MissingDirectionLeak (PiR PiU RRinv Jmap Schur)
open Novel.M5MissingDirectionLeakProof

lemma bat_sum {m n K : ℕ} (D : Data m n K S) (a : Fin m → ℝ) : D.BAᵀ *ᵥ a = ∑ k, a k • D.BA k := by
  funext l
  simp [mulVec, dotProduct, Finset.sum_apply, transpose_apply, mul_comm]

lemma bat_update {m n K : ℕ} (D : Data m n K S) (a : Fin m → ℝ) (k : Fin m) (y : ℝ) :
    D.BAᵀ *ᵥ Function.update a k y = D.BAᵀ *ᵥ a + (y - a k) • D.BA k := by
  rw [bat_sum, bat_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self]
  have : ∑ j ∈ Finset.univ.erase k, Function.update a k y j • D.BA j =
      ∑ j ∈ Finset.univ.erase k, a j • D.BA j :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, sub_smul]
  abel

/-- The fund loadings other than `β_i` lie in `L_E`, so `Π_U B^A'a = a_i Π_U β_i`. -/
lemma pu_fund {m n K : ℕ} {D : Data m n K S} {i : Fin m}
    (hoth : ∀ k, k ≠ i → PiU D.BE *ᵥ D.BA k = 0) (a : Fin m → ℝ) :
    PiU D.BE *ᵥ (D.BAᵀ *ᵥ a - a i • D.BA i) = 0 := by
  rw [bat_sum, mulVec_sub, mulVec_sum, Finset.sum_eq_single i]
  · rw [mulVec_smul, sub_self]
  · intro k _ hk; rw [mulVec_smul, hoth k hk, smul_zero]
  · simp

lemma pu_bet {m n K : ℕ} {D : Data m n K S} (hBE : IsUnit (D.BE * D.BEᵀ).det) (z : Fin n → ℝ) :
    PiU D.BE *ᵥ (D.BEᵀ *ᵥ z) = 0 := by
  rw [mulVec_mulVec, Standalone.M5MissingDirectionLeak.PiU, Matrix.sub_mul, Matrix.one_mul,
    pr_bet hBE, sub_self, zero_mulVec]

/-- A loading in `L_E` is `B^E'g` for `g = (B^E B^E')⁻¹ B^E β`. -/
lemma pr_fix {K n : ℕ} {BE : Matrix (Fin n) (Fin K) ℝ} (hBE : IsUnit (BE * BEᵀ).det)
    {β : Fin K → ℝ} (hβ : PiU BE *ᵥ β = 0) : BEᵀ *ᵥ ((BE * BEᵀ)⁻¹ *ᵥ (BE *ᵥ β)) = β := by
  have h1 : PiR BE *ᵥ β = β := by
    conv_rhs => rw [← one_mulVec β, ← pr_add_pu hBE, add_mulVec, hβ, add_zero]
  rw [← h1]
  simp only [Standalone.M5MissingDirectionLeak.PiR, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc BE BEᵀ, ← Matrix.mul_assoc (BE * BEᵀ)⁻¹ (BE * BEᵀ), nonsing_inv_mul _ hBE,
    Matrix.one_mul]

/-- The hedged value of a fund-`i` position `c`: with `PiU (x - cβ) = 0`, the best ETF hedge gives
`G(x + B^E'z) ≤ C + (p c - (γ s_U/2) c²)`, attained. -/
lemma hedge {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ}
    (hsig : sigF D = Sf) (hBE : IsUnit (D.BE * D.BEᵀ).det) (hSf : Sf.PosDef) (hγ : 0 ≤ D.gamma)
    {b0 : Fin K → ℝ} (hb0 : D.gamma • (sigF D *ᵥ b0) = θ.lam) (i : Fin m) {x : Fin K → ℝ} {c : ℝ}
    (hx : PiU D.BE *ᵥ (x - c • D.BA i) = 0) :
    (∀ z, Gf D θ (x + D.BEᵀ *ᵥ z) ≤ (Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))) +
      psi (D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)) (D.gamma * (D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)))
        0 0 0 c) ∧
    ∃ z, Gf D θ (x + D.BEᵀ *ᵥ z) = (Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))) +
      psi (D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)) (D.gamma * (D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)))
        0 0 0 c := by
  have hG := G_TB θ hb0
  have hsq : ∀ y, sqN D y = y ⬝ᵥ (Sf *ᵥ y) := fun y => by rw [sqN, hsig]
  have e : ∀ z, x + D.BEᵀ *ᵥ z - b0 = (x - b0) - D.BEᵀ *ᵥ (-z) := fun z => by
    rw [mulVec_neg]; abel
  have hq : (x - b0) ⬝ᵥ (Schur D.BE Sf *ᵥ (x - b0)) =
      (c • D.BA i - b0) ⬝ᵥ (Schur D.BE Sf *ᵥ (c • D.BA i - b0)) := by
    rw [show x - b0 = (c • D.BA i - b0) + (x - c • D.BA i) by abel, schur_form_add hBE hSf _ hx]
  have hp : D.gamma * (D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ b0)) = D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam) := by
    rw [← schur_b0 hBE hSf (show D.gamma • (Sf *ᵥ b0) = θ.lam by rw [← hsig]; exact hb0),
      dotProduct_smul, smul_eq_mul]
  have hval : Gf D θ b0 - D.gamma / 2 * ((x - b0) ⬝ᵥ (Schur D.BE Sf *ᵥ (x - b0))) =
      (Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))) +
      psi (D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)) (D.gamma * (D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)))
        0 0 0 c := by
    rw [hq, schur_line hBE hSf, psi, ← hp]
    ring
  refine ⟨fun z => ?_, ⟨-((D.BE * Sf * D.BEᵀ)⁻¹ *ᵥ (D.BE *ᵥ (Sf *ᵥ (x - b0)))), ?_⟩⟩
  · rw [← hval, hG, hsq, e z]
    have h1 := (schur_min hBE hSf (x - b0) (-z)).1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ D.gamma / 2)
    linarith
  · rw [← hval, hG, hsq, e, neg_neg, ← (schur_min hBE hSf (x - b0) 0).2]

lemma sum_update_le2 {m : ℕ} (g : ℝ → ℝ) (f : Fin m → ℝ → ℝ) (a : Fin m → ℝ) (i : Fin m) (y : ℝ)
    (h : g y + ∑ k, f k (Function.update a i y k) ≤ g (a i) + ∑ k, f k (a k)) :
    g y + f i y ≤ g (a i) + f i (a i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Function.update_self] at h
  have : ∑ k ∈ Finset.univ.erase i, f k (Function.update a i y k) =
      ∑ k ∈ Finset.univ.erase i, f k (a k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  linarith

lemma G_ineq {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (hq : ∀ s, 0 ≤ D.q s)
    (hγ : 0 ≤ D.gamma) (x y : Inst m n → ℝ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (1 - ε) * Gf D θ (exposure D x) + ε * Gf D θ (exposure D y) ≤
      Gf D θ (exposure D ((1 - ε) • x + ε • y)) := by
  rw [Novel.M2ActionClassesProof.exposure_comb]
  have e : (1 - ε) • exposure D x + ε • exposure D y =
      exposure D x + ε • (exposure D y - exposure D x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [e, Novel.M2TwoStageSeparationProof.G_seg,
    Novel.M2TwoStageSeparationProof.G_expand D θ (exposure D y) (exposure D x)]
  have := Novel.M2TwoStageSeparationProof.sqN_nonneg D hq (exposure D y - exposure D x)
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (mul_nonneg hγ this)]

lemma psi_ineq {alpha c kp km xm : ℝ} (hc : 0 < c) (hkp : 0 ≤ kp) (hkm : 0 ≤ km) (a b ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (1 - ε) * psi alpha c kp km xm a + ε * psi alpha c kp km xm b ≤
      psi alpha c kp km xm ((1 - ε) * a + ε * b) := by
  have hcv := cst_convex (xm := xm) hc hkp hkm a b ε h0 h1
  rw [show (1 - ε) * a + ε * b = a + ε * (b - a) by ring]
  simp only [psi_eq, cst] at hcv ⊢
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (mul_nonneg hc.le (sq_nonneg (a - b)))]

lemma bandHold_zero (p c xbar : ℝ) : bandHold p c 0 0 0 xbar = max 0 (min xbar (p / c)) := by
  unfold bandHold
  rw [sub_zero, add_zero, max_eq_left (min_le_left _ _)]

/-- The joint optimum under one unreachable fund: fund `i` maximizes its reduced objective on its box,
every other fund maximizes its own `ψ_k` on `ℝ`, the value splits, and the ETFs give the best hedge
of the funds held. -/
lemma unreach_joint {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf : Matrix (Fin K) (Fin K) ℝ}
    {v : Fin m → ℝ} {i : Fin m} (hI : Inputs D) (hOU : OneUnreachable D Sf v i)
    {wJ : Inst m n → ℝ} (hwJ : wJ ∈ F D) (hmaxJ : IsMaxOn (fun w => score D w θ) (F D) wJ)
    (hsJ : SlackBut D i wJ) {b0 : Fin K → ℝ} (hb0 : D.gamma • (sigF D *ᵥ b0) = θ.lam) :
    IsMaxOn (psi (θ.alpha i + D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam))
      (D.gamma * (v i + D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i))) (D.kplus (Sum.inl i))
      (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))) (Set.Icc 0 (D.wbar (Sum.inl i))) (wJ (Sum.inl i)) ∧
    (∀ k, k ≠ i → ∀ y, psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
      (w0 D (Sum.inl k)) y ≤ psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
      (D.kminus (Sum.inl k)) (w0 D (Sum.inl k)) (wJ (Sum.inl k))) ∧
    score D wJ θ = (Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))) +
      psi (D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)) (D.gamma * (D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)))
        0 0 0 (wJ (Sum.inl i)) +
      ∑ k, psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k)) (D.kminus (Sum.inl k))
        (w0 D (Sum.inl k)) (wJ (Sum.inl k)) ∧
    ∀ z, Gf D θ (D.BAᵀ *ᵥ active wJ + D.BEᵀ *ᵥ z) ≤ Gf D θ (exposure D wJ) := by
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ := hOU
  let p := D.BA i ⬝ᵥ ((Jmap D.BE Sf)ᵀ *ᵥ θ.lam)
  let sU := D.BA i ⬝ᵥ (Schur D.BE Sf *ᵥ D.BA i)
  let psiR := psi (θ.alpha i + p) (D.gamma * (v i + sU)) (D.kplus (Sum.inl i))
    (D.kminus (Sum.inl i)) (w0 D (Sum.inl i))
  have hsig : sigF D = Sf := hR.1
  have hkp : ∀ l, 0 ≤ D.kplus l := fun l => (hI.2.1 l).1
  have hkm : ∀ l, 0 ≤ D.kminus l := fun l => (hI.2.1 l).2
  let ψ : Fin m → ℝ → ℝ := fun k => psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
    (D.kminus (Sum.inl k)) (w0 D (Sum.inl k))
  let C := Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))
  let φ := psi p (D.gamma * sU) 0 0 0
  have e : ∀ a, psiR a = φ a + ψ i a := fun a => by simp only [psiR, φ, ψ, psi]; ring
  have dec : ∀ w, score D w θ = Gf D θ (exposure D w) + ∑ k, ψ k (w (Sum.inl k)) :=
    score_span θ hR hcE hkE
  have hHr : ∀ w, Hr D θ w = ∑ k, ψ k (w (Sum.inl k)) := fun w => by
    have := Novel.M2TwoStageSeparationProof.split D θ w
    rw [dec] at this; linarith
  have hle : ∀ w, Gf D θ (exposure D w) ≤ C + φ (w (Sum.inl i)) := fun w =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth (active w))).1 (etf w)
  have heq : ∀ a : Fin m → ℝ, ∃ z, Gf D θ (exposure D (Sum.elim a z)) = C + φ (a i) := fun a =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth a)).2
  -- the joint optimum
  have keyJ : ∀ z : Inst m n → ℝ, 0 ≤ z (Sum.inl i) → z (Sum.inl i) ≤ D.wbar (Sum.inl i) →
      score D z θ ≤ score D wJ θ := fun z h0 h1 =>
    drop_slack_gen (fun l => l ≠ Sum.inl i) (fun w => score D w θ) (score_ineq θ hI) convex_univ hwJ
      (Set.mem_univ _) (fun w hw _ => hmaxJ hw) hsJ.1 hsJ.2 (Set.mem_univ _)
      (fun l hl => by push Not at hl; subst hl; exact ⟨h0, h1⟩)
  have hJval : score D wJ θ = C + φ (wJ (Sum.inl i)) + ∑ k, ψ k (wJ (Sum.inl k)) := by
    apply le_antisymm
    · rw [dec]; linarith [hle wJ]
    · obtain ⟨z, hz⟩ := heq (active wJ)
      have := keyJ (Sum.elim (active wJ) z) (hwJ.1 (Sum.inl i)).1 (hwJ.1 (Sum.inl i)).2
      rw [dec, hz] at this
      exact this
  have hJ1 : IsMaxOn psiR (Set.Icc 0 (D.wbar (Sum.inl i))) (wJ (Sum.inl i)) := by
    intro y hy
    obtain ⟨z, hz⟩ := heq (Function.update (active wJ) i y)
    have h1 := keyJ (Sum.elim (Function.update (active wJ) i y) z) (by simpa using hy.1)
      (by simpa using hy.2)
    rw [dec, hz, hJval] at h1
    have h1' : φ y + ∑ k, ψ k (Function.update (active wJ) i y k) ≤
        φ (active wJ i) + ∑ k, ψ k (active wJ k) := by
      simp only [active, Sum.elim_inl, Function.update_self] at h1 ⊢; linarith
    have h2 := sum_update_le2 φ ψ (active wJ) i y h1'
    show psiR y ≤ psiR (wJ (Sum.inl i))
    rw [e, e]; exact h2
  have hJ2 : ∀ k, k ≠ i → ∀ y, ψ k y ≤ ψ k (wJ (Sum.inl k)) := by
    intro k hk y
    obtain ⟨z, hz⟩ := heq (Function.update (active wJ) k y)
    have hi : Function.update (active wJ) k y i = wJ (Sum.inl i) := by
      rw [Function.update_of_ne (Ne.symm hk)]; rfl
    have h1 := keyJ (Sum.elim (Function.update (active wJ) k y) z)
      (by simp only [Sum.elim_inl]; rw [hi]; exact (hwJ.1 _).1)
      (by simp only [Sum.elim_inl]; rw [hi]; exact (hwJ.1 _).2)
    rw [dec, hz, hJval, hi] at h1
    have h1' : ∑ j, ψ j (Function.update (active wJ) k y j) ≤ ∑ j, ψ j (active wJ j) := by
      simp only [active, Sum.elim_inl] at h1 ⊢; linarith
    exact sum_update_le ψ (active wJ) k y h1'
  have hETF : ∀ z, Gf D θ (D.BAᵀ *ᵥ active wJ + D.BEᵀ *ᵥ z) ≤ Gf D θ (exposure D wJ) := by
    intro z
    have h1 := keyJ (Sum.elim (active wJ) z) (hwJ.1 (Sum.inl i)).1 (hwJ.1 (Sum.inl i)).2
    rw [dec, dec wJ] at h1
    have h2 : Gf D θ (exposure D (Sum.elim (active wJ) z)) ≤ Gf D θ (exposure D wJ) := by
      simp only [active, Sum.elim_inl] at h1; linarith
    exact h2
  exact ⟨hJ1, hJ2, hJval, hETF⟩

theorem unreachable : Unreachable := by
  intro m n K S _ D θ Sf v i hI hOU wJ hwJ hmaxJ hsJ bs hbs hmaxG w₂ hw₂ hmaxH hs₂
  obtain ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ := hOU
  intro p sU aS psiR aJ
  have hsig : sigF D = Sf := hR.1
  have hkp : ∀ l, 0 ≤ D.kplus l := fun l => (hI.2.1 l).1
  have hkm : ∀ l, 0 ≤ D.kminus l := fun l => (hI.2.1 l).2
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  obtain ⟨b0, hb0⟩ : ∃ b0, D.gamma • (sigF D *ᵥ b0) = θ.lam :=
    ⟨(D.gamma • Sf)⁻¹ *ᵥ θ.lam, by
      rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]⟩
  have hsU : 0 < sU := sU_pos hBE hSf hu
  let ψ : Fin m → ℝ → ℝ := fun k => psi (θ.alpha k) (D.gamma * v k) (D.kplus (Sum.inl k))
    (D.kminus (Sum.inl k)) (w0 D (Sum.inl k))
  let C := Gf D θ b0 - D.gamma / 2 * (b0 ⬝ᵥ (Schur D.BE Sf *ᵥ b0))
  let φ := psi p (D.gamma * sU) 0 0 0
  have e : ∀ a, psiR a = φ a + ψ i a := fun a => by simp only [psiR, φ, ψ, psi]; ring
  have dec : ∀ w, score D w θ = Gf D θ (exposure D w) + ∑ k, ψ k (w (Sum.inl k)) :=
    score_span θ hR hcE hkE
  have hHr : ∀ w, Hr D θ w = ∑ k, ψ k (w (Sum.inl k)) := fun w => by
    have := Novel.M2TwoStageSeparationProof.split D θ w
    rw [dec] at this; linarith
  have hle : ∀ w, Gf D θ (exposure D w) ≤ C + φ (w (Sum.inl i)) := fun w =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth (active w))).1 (etf w)
  have heq : ∀ a : Fin m → ℝ, ∃ z, Gf D θ (exposure D (Sum.elim a z)) = C + φ (a i) := fun a =>
    (hedge θ hsig hBE hSf hγ.le hb0 i (pu_fund hoth a)).2
  obtain ⟨hJ1, hJ2, hJval, -⟩ := unreach_joint θ hI ⟨hR, hBE, hcE, hkE, hv, hSf, hγ, hu, hoth⟩ hwJ hmaxJ
    hsJ hb0
  have hJ1 : IsMaxOn psiR (Set.Icc 0 (D.wbar (Sum.inl i))) (wJ (Sum.inl i)) := hJ1
  have hJ2 : ∀ k, k ≠ i → ∀ y, ψ k y ≤ ψ k (wJ (Sum.inl k)) := hJ2
  have hJval : score D wJ θ = C + φ (wJ (Sum.inl i)) + ∑ k, ψ k (wJ (Sum.inl k)) := hJval
  -- stage 1
  have hbsw : exposure D w₂ = bs := hw₂.2
  have key1 : ∀ z : Inst m n → ℝ, 0 ≤ z (Sum.inl i) → z (Sum.inl i) ≤ D.wbar (Sum.inl i) →
      Gf D θ (exposure D z) ≤ Gf D θ (exposure D w₂) := fun z h0 h1 =>
    drop_slack_gen (fun l => l ≠ Sum.inl i) (fun w => Gf D θ (exposure D w))
      (G_ineq D θ hI.2.2.1 hI.2.2.2) convex_univ hw₂.1 (Set.mem_univ _)
      (fun w hw _ => by rw [hbsw]; exact hmaxG ⟨w, hw, rfl⟩) hs₂.1 hs₂.2 (Set.mem_univ _)
      (fun l hl => by push Not at hl; subst hl; exact ⟨h0, h1⟩)
  have hS1 : IsMaxOn φ (Set.Icc 0 (D.wbar (Sum.inl i))) (w₂ (Sum.inl i)) := by
    intro y hy
    obtain ⟨z, hz⟩ := heq (Function.update (active w₂) i y)
    have h1 := key1 (Sum.elim (Function.update (active w₂) i y) z) (by simpa using hy.1)
      (by simpa using hy.2)
    rw [hz] at h1
    have h2 := hle w₂
    simp only [Function.update_self] at h1
    show φ y ≤ φ (w₂ (Sum.inl i))
    linarith
  have hGbs : Gf D θ bs = C + φ (w₂ (Sum.inl i)) := by
    apply le_antisymm
    · rw [← hbsw]; exact hle w₂
    · obtain ⟨z, hz⟩ := heq (active w₂)
      have := key1 (Sum.elim (active w₂) z) (hw₂.1.1 _).1 (hw₂.1.1 _).2
      rw [hz, hbsw] at this; exact this
  have ha2 : w₂ (Sum.inl i) = aS := by
    rw [eq_bandHold (mul_pos hγ hsU) le_rfl le_rfl (hw₂.1.1 _) hS1, bandHold_zero]
  -- stage 2
  have hAconv : Convex ℝ {w : Inst m n → ℝ | exposure D w = bs} := by
    intro x hx y hy a b _ _ hab
    show exposure D (a • x + b • y) = bs
    rw [Novel.M2ActionClassesProof.exposure_comb, show exposure D x = bs from hx,
      show exposure D y = bs from hy, ← add_smul, hab, one_smul]
  have hHineq : ∀ (x y : Inst m n → ℝ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      (1 - ε) * Hr D θ x + ε * Hr D θ y ≤ Hr D θ ((1 - ε) • x + ε • y) := by
    intro x y ε h0 h1
    rw [hHr, hHr, hHr, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := psi_ineq (xm := w0 D (Sum.inl k)) (alpha := θ.alpha k) (mul_pos hγ (hv k))
      (hkp (Sum.inl k)) (hkm (Sum.inl k)) (x (Sum.inl k)) (y (Sum.inl k)) ε h0 h1
    simpa [ψ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have key2 : ∀ z : Inst m n → ℝ, exposure D z = bs → 0 ≤ z (Sum.inl i) →
      z (Sum.inl i) ≤ D.wbar (Sum.inl i) → Hr D θ z ≤ Hr D θ w₂ := fun z hzA h0 h1 =>
    drop_slack_gen (fun l => l ≠ Sum.inl i) (Hr D θ) hHineq hAconv hw₂.1 hbsw
      (fun w hw hA => hmaxH ⟨hw, hA⟩) hs₂.1 hs₂.2 hzA
      (fun l hl => by push Not at hl; subst hl; exact ⟨h0, h1⟩)
  have hT1 : ∀ k, k ≠ i → ∀ y, ψ k y ≤ ψ k (w₂ (Sum.inl k)) := by
    intro k hk y
    let g := (D.BE * D.BEᵀ)⁻¹ *ᵥ (D.BE *ᵥ D.BA k)
    let z : Inst m n → ℝ :=
      Sum.elim (Function.update (active w₂) k y) (etf w₂ - (y - w₂ (Sum.inl k)) • g)
    have hzA : exposure D z = bs := by
      rw [← hbsw]
      show D.BAᵀ *ᵥ Function.update (active w₂) k y + D.BEᵀ *ᵥ (etf w₂ - (y - w₂ (Sum.inl k)) • g) =
        D.BAᵀ *ᵥ active w₂ + D.BEᵀ *ᵥ etf w₂
      rw [bat_update, mulVec_sub, mulVec_smul, pr_fix hBE (hoth k hk)]
      simp only [active]; abel
    have hi : z (Sum.inl i) = w₂ (Sum.inl i) := by
      show Function.update (active w₂) k y i = _
      rw [Function.update_of_ne (Ne.symm hk)]; rfl
    have h1 := key2 z hzA (by rw [hi]; exact (hw₂.1.1 _).1) (by rw [hi]; exact (hw₂.1.1 _).2)
    rw [hHr, hHr] at h1
    have h1' : ∑ j, ψ j (Function.update (active w₂) k y j) ≤ ∑ j, ψ j (active w₂ j) := h1
    exact sum_update_le ψ (active w₂) k y h1'
  have hVr : Vr D θ bs = Hr D θ w₂ := by
    have hg : IsGreatest (Hr D θ '' fibre D bs) (Hr D θ w₂) :=
      ⟨⟨w₂, hw₂, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmaxH hw⟩
    exact hg.csSup_eq
  -- the loss
  have hrest : ∀ k ∈ Finset.univ.erase i, ψ k (wJ (Sum.inl k)) = ψ k (w₂ (Sum.inl k)) :=
    fun k hk => le_antisymm (hT1 k (Finset.ne_of_mem_erase hk) _) (hJ2 k (Finset.ne_of_mem_erase hk) _)
  have hsum : ∑ k, ψ k (wJ (Sum.inl k)) - ψ i (wJ (Sum.inl i)) =
      ∑ k, ψ k (w₂ (Sum.inl k)) - ψ i (w₂ (Sum.inl i)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      Finset.sum_congr rfl hrest]
    ring
  have hJ : wJ (Sum.inl i) = aJ :=
    eq_bandHold (mul_pos hγ (add_pos (hv i) hsU)) (hkp _) (hkm _) (hwJ.1 _) hJ1
  have hLam : score D wJ θ - (Gf D θ bs + Vr D θ bs) = psiR aJ - psiR aS := by
    rw [hJval, hGbs, hVr, hHr, e, e, ← hJ, ← ha2]
    linarith [hsum]
  have hmaxR : IsMaxOn psiR (Set.Icc 0 (D.wbar (Sum.inl i))) aJ := by rw [← hJ]; exact hJ1
  have hJbox : aJ ∈ Set.Icc 0 (D.wbar (Sum.inl i)) := by rw [← hJ]; exact hwJ.1 _
  have hSbox : aS ∈ Set.Icc 0 (D.wbar (Sum.inl i)) := by rw [← ha2]; exact hw₂.1.1 _
  have hc : 0 < D.gamma * (v i + sU) := mul_pos hγ (add_pos (hv i) hsU)
  have hiff : aS = aJ ↔ IsMaxOn psiR (Set.Icc 0 (D.wbar (Sum.inl i))) aS :=
    ⟨fun h => by rw [h]; exact hmaxR, fun h => max_unique hc (hkp _) (hkm _) hSbox hJbox h hmaxR⟩
  refine ⟨hsU, ha2, hJ, hLam, by linarith [show psiR aS ≤ psiR aJ from hmaxR hSbox],
    ⟨fun h => ?_, fun h => ?_⟩, hiff⟩
  · apply hiff.mpr
    intro y hy
    show psiR y ≤ psiR aS
    linarith [show psiR y ≤ psiR aJ from hmaxR hy]
  · rw [h] at hLam; linarith

end Unreach

/-! ### AX-13 -/

/-- The statement's `AX13` is the Upstream structure `PolyKKT` for every concave `f` and constraint
system. -/
theorem ax13_iff : AX13 ↔ ∀ (ι Λ : Type) [Fintype ι] [Fintype Λ] (f : (ι → ℝ) → ℝ) (a : Λ → ι → ℝ)
    (b : Λ → ℝ), Upstream.KKT.PolyKKT f a b :=
  ⟨fun h ι Λ _ _ f a b => ⟨fun hf x hx => h ι Λ f a b hf x hx⟩,
    fun h ι Λ _ _ f a b hf x hx => (h ι Λ f a b).kkt hf x hx⟩

/-! ### Part 0: the lifted problem and AX-13 -/

section Part0

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Inputs)

/-- Lifted variables `(x, y)`: holdings and per-instrument cost bounds. -/
abbrev Io (m n : ℕ) := Inst m n ⊕ Inst m n

/-- Lifted constraints: upper box, lower box, the two cost pieces, and the budget. -/
abbrev Lm (m n : ℕ) := (Inst m n ⊕ Inst m n) ⊕ ((Inst m n ⊕ Inst m n) ⊕ Unit)

def xs {m n : ℕ} (z : Io m n → ℝ) : Inst m n → ℝ := fun l => z (Sum.inl l)

def ys {m n : ℕ} (z : Io m n → ℝ) : Inst m n → ℝ := fun l => z (Sum.inr l)

/-- Constraint normals. -/
def cA {m n K : ℕ} (D : Data m n K S) : Lm m n → Io m n → ℝ
  | Sum.inl (Sum.inl l) => fun z => if z = Sum.inl l then 1 else 0
  | Sum.inl (Sum.inr l) => fun z => if z = Sum.inl l then -1 else 0
  | Sum.inr (Sum.inl (Sum.inl l)) => fun z =>
      (if z = Sum.inl l then D.kplus l else 0) + (if z = Sum.inr l then -1 else 0)
  | Sum.inr (Sum.inl (Sum.inr l)) => fun z =>
      (if z = Sum.inl l then -D.kminus l else 0) + (if z = Sum.inr l then -1 else 0)
  | Sum.inr (Sum.inr _) => fun _ => 1

/-- Constraint levels. -/
def cB {m n K : ℕ} (D : Data m n K S) : Lm m n → ℝ
  | Sum.inl (Sum.inl l) => D.wbar l
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr (Sum.inl (Sum.inl l)) => D.kplus l * w0 D l
  | Sum.inr (Sum.inl (Sum.inr l)) => -(D.kminus l * w0 D l)
  | Sum.inr (Sum.inr _) => k0 D + ∑ l, w0 D l

/-- The lifted objective `μ'x - (γ/2) x'Σx - Σ y`. -/
def fL {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (z : Io m n → ℝ) : ℝ :=
  mu D θ ⬝ᵥ xs z - D.gamma / 2 * (xs z ⬝ᵥ (covariance D *ᵥ xs z)) - ∑ l, ys z l

/-- Instrument `l`'s cost `κ⁺(w - w⁻)⁺ + κ⁻(w⁻ - w)⁺`. -/
def costl {m n K : ℕ} (D : Data m n K S) (w : Inst m n → ℝ) (l : Inst m n) : ℝ :=
  D.kplus l * max (w l - w0 D l) 0 + D.kminus l * max (-(w l - w0 D l)) 0

def lift {m n K : ℕ} (D : Data m n K S) (w : Inst m n → ℝ) : Io m n → ℝ := Sum.elim w (costl D w)

section Dots

variable {m n K : ℕ} (D : Data m n K S) (z : Io m n → ℝ) (l : Inst m n)

lemma dot_up : cA D (Sum.inl (Sum.inl l)) ⬝ᵥ z = z (Sum.inl l) := by
  simp [cA, dotProduct, ite_mul]

lemma dot_lo : cA D (Sum.inl (Sum.inr l)) ⬝ᵥ z = -z (Sum.inl l) := by
  simp [cA, dotProduct, ite_mul]

lemma dot_cp : cA D (Sum.inr (Sum.inl (Sum.inl l))) ⬝ᵥ z = D.kplus l * z (Sum.inl l) - z (Sum.inr l) := by
  simp [cA, dotProduct, add_mul, ite_mul, Finset.sum_add_distrib]; ring

lemma dot_cm : cA D (Sum.inr (Sum.inl (Sum.inr l))) ⬝ᵥ z = -D.kminus l * z (Sum.inl l) - z (Sum.inr l) := by
  simp [cA, dotProduct, add_mul, ite_mul, Finset.sum_add_distrib]; ring

lemma dot_bud (u : Unit) : cA D (Sum.inr (Sum.inr u)) ⬝ᵥ z = ∑ l, xs z l + ∑ l, ys z l := by
  simp [cA, dotProduct, Fintype.sum_sum_type, xs, ys]

variable (η : Lm m n → ℝ)

lemma comp_x : (∑ c, η c • cA D c) (Sum.inl l) =
    η (Sum.inl (Sum.inl l)) - η (Sum.inl (Sum.inr l)) + η (Sum.inr (Sum.inl (Sum.inl l))) * D.kplus l -
      η (Sum.inr (Sum.inl (Sum.inr l))) * D.kminus l + η (Sum.inr (Sum.inr ())) := by
  rw [Finset.sum_apply]
  simp [Fintype.sum_sum_type, cA, mul_ite]
  ring

lemma comp_y : (∑ c, η c • cA D c) (Sum.inr l) =
    -η (Sum.inr (Sum.inl (Sum.inl l))) - η (Sum.inr (Sum.inl (Sum.inr l))) + η (Sum.inr (Sum.inr ())) := by
  rw [Finset.sum_apply]
  simp [Fintype.sum_sum_type, cA, mul_ite]
  ring

end Dots

lemma costl_eq {m n K : ℕ} {D : Data m n K S} (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l)
    (w : Inst m n → ℝ) (l : Inst m n) :
    costl D w l = max (D.kplus l * (w l - w0 D l)) (D.kminus l * (w0 D l - w l)) := by
  obtain ⟨h1, h2⟩ := hr l
  simp only [costl]
  rcases le_total (w l) (w0 D l) with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_left (by nlinarith)]; ring

lemma tau_costl {m n K : ℕ} (D : Data m n K S) (w : Inst m n → ℝ) :
    tau D (w - w0 D) = ∑ l, costl D w l := rfl

lemma mu_dot {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ) :
    mu D θ ⬝ᵥ w = exposure D w ⬝ᵥ θ.lam + active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE := by
  have e1 : mu D θ ⬝ᵥ w = (D.BA *ᵥ θ.lam + θ.alpha) ⬝ᵥ active w + (D.BE *ᵥ θ.lam - D.cE) ⬝ᵥ etf w := by
    simp only [dotProduct, Fintype.sum_sum_type, mu, Sum.elim_inl, Sum.elim_inr, active, etf]
  have e2 : exposure D w ⬝ᵥ θ.lam = (D.BA *ᵥ θ.lam) ⬝ᵥ active w + (D.BE *ᵥ θ.lam) ⬝ᵥ etf w := by
    simp only [exposure, add_dotProduct]
    rw [mulVec_transpose, mulVec_transpose, ← dotProduct_mulVec, ← dotProduct_mulVec,
      dotProduct_comm (active w), dotProduct_comm (etf w)]
  rw [e1, e2]
  simp only [add_dotProduct, sub_dotProduct]
  rw [dotProduct_comm θ.alpha, dotProduct_comm D.cE]
  ring

lemma fL_lift {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (w : Inst m n → ℝ) :
    fL D θ (lift D w) = score D w θ := by
  simp only [fL, score, mu_dot, tau_costl]
  rfl

lemma cov_symm {m n K : ℕ} (D : Data m n K S) (x d : Inst m n → ℝ) :
    x ⬝ᵥ (covariance D *ᵥ d) = d ⬝ᵥ (covariance D *ᵥ x) := by
  rw [Novel.M2SoftTargetTwoStageProof.cov_bilin, Novel.M2SoftTargetTwoStageProof.cov_bilin]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The lifted objective is an exact quadratic: `f(z + d) = f(z) + ∇f(z)·d - (γ/2) d_x'Σd_x`. -/
lemma fL_expand {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (z d : Io m n → ℝ) :
    fL D θ (z + d) = fL D θ z + (grad D θ (xs z) ⬝ᵥ xs d - ∑ l, ys d l) -
      D.gamma / 2 * (xs d ⬝ᵥ (covariance D *ᵥ xs d)) := by
  have hx : xs (z + d) = xs z + (1 : ℝ) • xs d := by rw [one_smul]; rfl
  have hy : ∀ l, ys (z + d) l = ys z l + ys d l := fun l => rfl
  have hq := Novel.M2SoftTargetTwoStageProof.quad_seg D (xs z) (xs d) 1
  rw [one_smul] at hx hq
  simp only [fL, hx, hq, hy, Finset.sum_add_distrib, grad, sub_dotProduct, smul_dotProduct,
    smul_eq_mul, dotProduct_add]
  rw [dotProduct_comm (covariance D *ᵥ xs z), cov_symm D (xs d) (xs z)]
  ring

lemma fL_concave {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (hq : ∀ s, 0 ≤ D.q s)
    (hγ : 0 ≤ D.gamma) : ConcaveOn ℝ Set.univ (fL D θ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hQ := Novel.M2ActionClassesProof.quad_convex D hq ha hb hab (xs x) (xs y)
  have hxs : xs (a • x + b • y) = a • xs x + b • xs y := rfl
  have hys : ∀ l, ys (a • x + b • y) l = a * ys x l + b * ys y l := fun l => rfl
  simp only [smul_eq_mul, fL, hxs, hys, Finset.sum_add_distrib, ← Finset.mul_sum, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ D.gamma / 2)]

lemma le_of_forall_eps {A B : ℝ} (hB : 0 ≤ B) (h : ∀ ε : ℝ, 0 < ε → A ≤ ε * B) : A ≤ 0 := by
  by_contra hA
  push Not at hA
  have h1 := h (A / (B + 1)) (by positivity)
  have h2 : A / (B + 1) * B < A := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- A supergradient of the lifted objective is its gradient, and conversely. -/
lemma super_iff {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (hq : ∀ s, 0 ≤ D.q s)
    (hγ : 0 ≤ D.gamma) (z s : Io m n → ℝ) :
    (∀ y, fL D θ y ≤ fL D θ z + s ⬝ᵥ (y - z)) ↔
      ∀ l, s (Sum.inl l) = grad D θ (xs z) l ∧ s (Sum.inr l) = -1 := by
  have hQ : ∀ d : Io m n → ℝ, 0 ≤ xs d ⬝ᵥ (covariance D *ᵥ xs d) := fun d => by
    rw [Novel.M2ActionClassesProof.quad_eq]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)
  have hsd : ∀ d : Io m n → ℝ, s ⬝ᵥ d = ∑ l, s (Sum.inl l) * xs d l + ∑ l, s (Sum.inr l) * ys d l :=
    fun d => by simp [dotProduct, Fintype.sum_sum_type, xs, ys]
  constructor
  · intro h
    -- the gradient pairing equals `s` in every direction
    have key : ∀ d : Io m n → ℝ, grad D θ (xs z) ⬝ᵥ xs d - ∑ l, ys d l = s ⬝ᵥ d := by
      have half : ∀ d : Io m n → ℝ, grad D θ (xs z) ⬝ᵥ xs d - ∑ l, ys d l - s ⬝ᵥ d ≤ 0 := fun d => by
        refine le_of_forall_eps (mul_nonneg (by positivity : 0 ≤ D.gamma / 2) (hQ d)) fun ε hε => ?_
        have h1 := h (z + ε • d)
        rw [fL_expand, add_sub_cancel_left] at h1
        have hxd : xs (ε • d) = ε • xs d := rfl
        have hyd : ∀ l, ys (ε • d) l = ε * ys d l := fun l => rfl
        simp only [hxd, hyd, dotProduct_smul, smul_eq_mul, smul_dotProduct, ← Finset.mul_sum] at h1
        rw [mulVec_smul, dotProduct_smul, smul_eq_mul] at h1
        have h2 : ε * (grad D θ (xs z) ⬝ᵥ xs d - ∑ l, ys d l - s ⬝ᵥ d) ≤
            ε * (ε * (D.gamma / 2 * (xs d ⬝ᵥ (covariance D *ᵥ xs d)))) := by nlinarith
        have := le_of_mul_le_mul_left h2 hε
        linarith
      intro d
      have h1 := half d
      have h2 := half (-d)
      have hxn : xs (-d) = -xs d := rfl
      have hyn : ∀ l, ys (-d) l = -ys d l := fun l => rfl
      simp only [hxn, hyn, dotProduct_neg, Finset.sum_neg_distrib] at h2
      linarith
    intro l
    constructor
    · have := key (Pi.single (Sum.inl l) 1)
      simp [xs, ys, dotProduct, Pi.single_apply] at this
      linarith
    · have := key (Pi.single (Sum.inr l) 1)
      simp [xs, ys, dotProduct, Pi.single_apply] at this
      linarith
  · intro h y
    have e := fL_expand D θ z (y - z)
    rw [add_sub_cancel] at e
    rw [e, hsd]
    have hg : grad D θ (xs z) ⬝ᵥ xs (y - z) = ∑ l, s (Sum.inl l) * xs (y - z) l := by
      simp only [dotProduct, (h _).1]
    have hy : ∑ l, s (Sum.inr l) * ys (y - z) l = -∑ l, ys (y - z) l := by
      simp only [(h _).2, neg_one_mul, Finset.sum_neg_distrib]
    rw [hg, hy]
    nlinarith [hQ (y - z), hγ]

lemma lift_feas {m n K : ℕ} {D : Data m n K S} (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l)
    {w : Inst m n → ℝ} (hw : w ∈ F D) : ∀ c, cA D c ⬝ᵥ lift D w ≤ cB D c := by
  have hcl := costl_eq hr w
  rintro ((l | l) | ((l | l) | u))
  · rw [dot_up]; exact (hw.1 l).2
  · rw [dot_lo]; simp only [cB, lift, Sum.elim_inl]; linarith [(hw.1 l).1]
  · rw [dot_cp]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr]
    have := le_max_left (D.kplus l * (w l - w0 D l)) (D.kminus l * (w0 D l - w l))
    rw [← hcl] at this; linarith
  · rw [dot_cm]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr]
    have := le_max_right (D.kplus l * (w l - w0 D l)) (D.kminus l * (w0 D l - w l))
    rw [← hcl] at this; linarith
  · rw [dot_bud]
    have h := hw.2
    simp only [cash, tau_costl, Finset.sum_sub_distrib] at h
    simp only [cB, xs, ys, lift, Sum.elim_inl, Sum.elim_inr]
    linarith

/-- A lifted feasible point projects into `F`, with `y` above the cost. -/
lemma lift_proj {m n K : ℕ} {D : Data m n K S} (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l)
    {z : Io m n → ℝ} (hz : ∀ c, cA D c ⬝ᵥ z ≤ cB D c) :
    xs z ∈ F D ∧ ∀ l, costl D (xs z) l ≤ ys z l := by
  have hc : ∀ l, costl D (xs z) l ≤ ys z l := fun l => by
    rw [costl_eq hr]
    have h1 := hz (Sum.inr (Sum.inl (Sum.inl l)))
    have h2 := hz (Sum.inr (Sum.inl (Sum.inr l)))
    rw [dot_cp] at h1; rw [dot_cm] at h2
    simp only [cB] at h1 h2
    apply max_le <;> simp only [xs, ys] <;> linarith
  refine ⟨⟨fun l => ⟨?_, ?_⟩, ?_⟩, hc⟩
  · have := hz (Sum.inl (Sum.inr l)); rw [dot_lo] at this; simp only [cB] at this
    show 0 ≤ z (Sum.inl l); linarith
  · have := hz (Sum.inl (Sum.inl l)); rw [dot_up] at this; exact this
  · have h := hz (Sum.inr (Sum.inr ())); rw [dot_bud] at h; simp only [cB] at h
    have hs := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hc l
    simp only [cash, tau_costl, Finset.sum_sub_distrib]
    simp only [xs] at h hs ⊢
    linarith

/-- The lifted problem has the same optimum. -/
lemma lift_max {m n K : ℕ} {D : Data m n K S} (θ : Params m K)
    (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l) {w : Inst m n → ℝ} :
    IsMaxOn (fL D θ) {y | ∀ c, cA D c ⬝ᵥ y ≤ cB D c} (lift D w) ↔
      IsMaxOn (fun w => score D w θ) (F D) w := by
  constructor
  · intro h w' hw'
    have := h (show lift D w' ∈ {y | ∀ c, cA D c ⬝ᵥ y ≤ cB D c} from lift_feas hr hw')
    simp only [Set.mem_ofPred_eq, fL_lift] at this
    exact this
  · intro h z hz
    show fL D θ z ≤ fL D θ (lift D w)
    obtain ⟨hF, hc⟩ := lift_proj hr hz
    have h1 : fL D θ z ≤ fL D θ (lift D (xs z)) := by
      simp only [fL]
      have hs := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hc l
      have e1 : xs (lift D (xs z)) = xs z := rfl
      have e2 : ∀ l, ys (lift D (xs z)) l = costl D (xs z) l := fun l => rfl
      simp only [e1, e2]
      linarith
    rw [fL_lift] at h1
    rw [fL_lift]
    exact h1.trans (h hF)

/-- The multipliers built from the criterion. -/
def mults {m n : ℕ} (R p : Inst m n → ℝ) (e : ℝ) : Lm m n → ℝ
  | Sum.inl (Sum.inl l) => max (R l) 0
  | Sum.inl (Sum.inr l) => max (-R l) 0
  | Sum.inr (Sum.inl (Sum.inl l)) => (1 + e) * p l
  | Sum.inr (Sum.inl (Sum.inr l)) => (1 + e) * (1 - p l)
  | Sum.inr (Sum.inr _) => e

theorem jointOptimality : JointOptimality := by
  intro hAX m n K S _ D θ hI w hw
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  have hq := hI.2.2.1
  have hγ := hI.2.2.2
  have hcl := costl_eq hr w
  have hxw : xs (lift D w) = w := rfl
  have hyw : ∀ l, ys (lift D w) l = costl D w l := fun l => rfl
  have hfeas := lift_feas hr hw
  rw [← lift_max θ hr, hAX (Io m n) (Lm m n) (fL D θ) (cA D) (cB D) (fL_concave D θ hq hγ) (lift D w) hfeas]
  -- cost pieces at `w`
  have hup : ∀ l, w0 D l < w l → costl D w l = D.kplus l * (w l - w0 D l) := fun l h => by
    simp only [costl]; rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hdn : ∀ l, w l < w0 D l → costl D w l = D.kminus l * (w0 D l - w l) := fun l h => by
    simp only [costl]; rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  constructor
  · rintro ⟨η, hη0, hsl, hsup⟩
    have hs := (super_iff D θ hq hγ (lift D w) _).mp hsup
    set e := η (Sum.inr (Sum.inr ())) with he_def
    have he : 0 ≤ e := hη0 _
    have hy : ∀ l, η (Sum.inr (Sum.inl (Sum.inl l))) + η (Sum.inr (Sum.inl (Sum.inr l))) = 1 + e :=
      fun l => by have := (hs l).2; rw [comp_y] at this; linarith
    have hx : ∀ l, grad D θ w l = η (Sum.inl (Sum.inl l)) - η (Sum.inl (Sum.inr l)) +
        η (Sum.inr (Sum.inl (Sum.inl l))) * D.kplus l - η (Sum.inr (Sum.inl (Sum.inr l))) * D.kminus l + e :=
      fun l => by have := (hs l).1; rw [comp_x, hxw] at this; linarith
    have h1e : 0 < 1 + e := by linarith
    refine ⟨e, fun l => (η (Sum.inr (Sum.inl (Sum.inl l))) * D.kplus l -
      η (Sum.inr (Sum.inl (Sum.inr l))) * D.kminus l) / (1 + e), he, ?_, fun l => ?_, fun l => ?_⟩
    · -- complementary slackness of the budget
      by_cases he0 : e = 0
      · rw [he0, zero_mul]
      · have hb := hfeas (Sum.inr (Sum.inr ()))
        have htight : ¬ cA D (Sum.inr (Sum.inr ())) ⬝ᵥ lift D w < cB D (Sum.inr (Sum.inr ())) :=
          fun hlt => he0 (hsl _ hlt)
        have heq := le_antisymm hb (not_lt.mp htight)
        rw [dot_bud] at heq
        simp only [cB, hxw, hyw] at heq
        have : cash D w = 0 := by
          simp only [cash, tau_costl, Finset.sum_sub_distrib]; linarith
        rw [this, mul_zero]
    · -- slopes
      obtain ⟨hkp, hkm⟩ := hr l
      have hbp := hη0 (Sum.inr (Sum.inl (Sum.inl l)))
      have hbm := hη0 (Sum.inr (Sum.inl (Sum.inr l)))
      have hyl := hy l
      refine ⟨?_, ?_, fun hlt => ?_, fun hlt => ?_⟩
      · rw [le_div_iff₀ h1e]; nlinarith [mul_nonneg hbp (add_nonneg hkp hkm)]
      · rw [div_le_iff₀ h1e]; nlinarith [mul_nonneg hbm (add_nonneg hkp hkm)]
      · -- after a purchase the sale piece is slack unless both rates vanish
        have hz : η (Sum.inr (Sum.inl (Sum.inr l))) * (D.kplus l + D.kminus l) = 0 := by
          rcases (add_nonneg hkp hkm).lt_or_eq with hpos | hzero
          · have hslk : cA D (Sum.inr (Sum.inl (Sum.inr l))) ⬝ᵥ lift D w <
                cB D (Sum.inr (Sum.inl (Sum.inr l))) := by
              rw [dot_cm]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hup l hlt]
              nlinarith [mul_pos hpos (show 0 < w l - w0 D l by linarith)]
            rw [hsl _ hslk, zero_mul]
          · rw [← hzero, mul_zero]
        rw [div_eq_iff h1e.ne']; nlinarith
      · have hz : η (Sum.inr (Sum.inl (Sum.inl l))) * (D.kplus l + D.kminus l) = 0 := by
          rcases (add_nonneg hkp hkm).lt_or_eq with hpos | hzero
          · have hslk : cA D (Sum.inr (Sum.inl (Sum.inl l))) ⬝ᵥ lift D w <
                cB D (Sum.inr (Sum.inl (Sum.inl l))) := by
              rw [dot_cp]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hdn l hlt]
              nlinarith [mul_pos hpos (show 0 < w0 D l - w l by linarith)]
            rw [hsl _ hslk, zero_mul]
          · rw [← hzero, mul_zero]
        rw [div_eq_iff h1e.ne']; nlinarith
    · -- box signs: `R = ν⁺ - ν⁻`
      have hR : grad D θ w l - e - (1 + e) * ((η (Sum.inr (Sum.inl (Sum.inl l))) * D.kplus l -
          η (Sum.inr (Sum.inl (Sum.inr l))) * D.kminus l) / (1 + e)) =
          η (Sum.inl (Sum.inl l)) - η (Sum.inl (Sum.inr l)) := by
        rw [mul_div_cancel₀ _ h1e.ne', hx l]; ring
      rw [hR]
      refine ⟨fun hlt => ?_, fun hpos => ?_⟩
      · have hslk : cA D (Sum.inl (Sum.inl l)) ⬝ᵥ lift D w < cB D (Sum.inl (Sum.inl l)) := by
          rw [dot_up]; exact hlt
        rw [hsl _ hslk]; linarith [hη0 (Sum.inl (Sum.inr l))]
      · have hslk : cA D (Sum.inl (Sum.inr l)) ⬝ᵥ lift D w < cB D (Sum.inl (Sum.inr l)) := by
          rw [dot_lo]; simp only [cB, lift, Sum.elim_inl]; linarith
        rw [hsl _ hslk]; linarith [hη0 (Sum.inl (Sum.inl l))]
  · rintro ⟨e, t, he, hek, ht, hR⟩
    let R : Inst m n → ℝ := fun l => grad D θ w l - e - (1 + e) * t l
    let p : Inst m n → ℝ := fun l =>
      if 0 < D.kplus l + D.kminus l then (t l + D.kminus l) / (D.kplus l + D.kminus l) else 1
    have hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1 ∧ p l * D.kplus l - (1 - p l) * D.kminus l = t l := fun l => by
      obtain ⟨hkp, hkm⟩ := hr l
      obtain ⟨ht1, ht2, -, -⟩ := ht l
      by_cases hs : 0 < D.kplus l + D.kminus l
      · simp only [p, hs, ite_true]
        refine ⟨div_nonneg (by linarith) hs.le, (div_le_one hs).mpr (by linarith), ?_⟩
        field_simp; ring
      · simp only [p, hs, ite_false]
        have h0 : D.kplus l = 0 := by linarith
        have h1 : D.kminus l = 0 := by linarith
        refine ⟨zero_le_one, le_rfl, ?_⟩
        simp only [h0, h1] at ht1 ht2 ⊢; linarith
    have h1e : 0 < 1 + e := by linarith
    refine ⟨mults R p e, ?_, ?_, (super_iff D θ hq hγ (lift D w) _).mpr fun l => ⟨?_, ?_⟩⟩
    · rintro ((l | l) | ((l | l) | u))
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact mul_nonneg h1e.le (hp l).1
      · exact mul_nonneg h1e.le (by linarith [(hp l).2.1])
      · exact he
    · rintro ((l | l) | ((l | l) | u)) hlt
      · rw [dot_up] at hlt
        exact max_eq_right ((hR l).1 hlt)
      · rw [dot_lo] at hlt; simp only [cB, lift, Sum.elim_inl] at hlt
        exact max_eq_right (by linarith [(hR l).2 (by linarith)])
      · rw [dot_cp] at hlt; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hcl l] at hlt
        obtain ⟨hkp, hkm⟩ := hr l
        have hlt' : D.kplus l * (w l - w0 D l) < D.kminus l * (w0 D l - w l) := by
          by_contra hc; push Not at hc; rw [max_eq_left hc] at hlt; linarith
        have hwl : w l < w0 D l := by
          by_contra hc; push Not at hc; nlinarith [mul_nonneg hkp (sub_nonneg.mpr hc),
            mul_nonneg hkm (sub_nonneg.mpr hc)]
        have hs : 0 < D.kplus l + D.kminus l := by
          by_contra hc; push Not at hc
          have : D.kplus l = 0 := by linarith
          have : D.kminus l = 0 := by linarith
          simp_all
        show (1 + e) * p l = 0
        simp only [p, hs, ite_true, (ht l).2.2.2 hwl]
        simp
      · rw [dot_cm] at hlt; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hcl l] at hlt
        obtain ⟨hkp, hkm⟩ := hr l
        have hlt' : D.kminus l * (w0 D l - w l) < D.kplus l * (w l - w0 D l) := by
          by_contra hc; push Not at hc; rw [max_eq_right hc] at hlt; linarith
        have hwl : w0 D l < w l := by
          by_contra hc; push Not at hc; nlinarith [mul_nonneg hkp (sub_nonneg.mpr hc),
            mul_nonneg hkm (sub_nonneg.mpr hc)]
        have hs : 0 < D.kplus l + D.kminus l := by
          by_contra hc; push Not at hc
          have : D.kplus l = 0 := by linarith
          have : D.kminus l = 0 := by linarith
          simp_all
        show (1 + e) * (1 - p l) = 0
        simp only [p, hs, ite_true, (ht l).2.2.1 hwl]
        rw [div_self hs.ne', sub_self, mul_zero]
      · rw [dot_bud] at hlt
        simp only [cB, hxw, hyw] at hlt
        have hc : 0 < cash D w := by
          simp only [cash, tau_costl, Finset.sum_sub_distrib]; linarith
        show e = 0
        rcases mul_eq_zero.mp hek with h | h
        · exact h
        · linarith
    · rw [comp_x, hxw]
      simp only [mults]
      have hRl : max (R l) 0 - max (-R l) 0 = R l := max_zero_sub_max_neg_zero_eq_self (R l)
      have hpl := (hp l).2.2
      simp only [R] at hRl
      nlinarith
    · rw [comp_y]; simp only [mults]; ring

end Part0

/-! ### Parts 2b, 3c and 3d -/

section Criteria

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN sigF Inputs)

/-- The covariance form in the reference case: `d'Σw = b_d'Σ~_f b_w + a_d'V a_w + p_d'Σ_E p_w`. -/
lemma cov_ref {m n K : ℕ} {D : Data m n K S} {Sf V SE} (hR : RefCase D Sf V SE)
    (d w : Inst m n → ℝ) :
    d ⬝ᵥ (covariance D *ᵥ w) = exposure D d ⬝ᵥ (Sf *ᵥ exposure D w) + active d ⬝ᵥ (V *ᵥ active w) +
      etf d ⬝ᵥ (SE *ᵥ etf w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  rw [Novel.M2SoftTargetTwoStageProof.cov_bilin]
  have e : ∀ s, D.q s * ((d ⬝ᵥ xi D s) * (w ⬝ᵥ xi D s)) =
      D.q s * ((exposure D d ⬝ᵥ D.zf s) * (exposure D w ⬝ᵥ D.zf s)) +
      D.q s * ((active d ⬝ᵥ D.zA s) * (active w ⬝ᵥ D.zA s)) +
      D.q s * ((etf d ⬝ᵥ D.zE s) * (etf w ⬝ᵥ D.zE s)) +
      (D.q s * ((exposure D d ⬝ᵥ D.zf s) * (active w ⬝ᵥ D.zA s)) +
        D.q s * ((exposure D w ⬝ᵥ D.zf s) * (active d ⬝ᵥ D.zA s)) +
        D.q s * ((exposure D d ⬝ᵥ D.zf s) * (etf w ⬝ᵥ D.zE s)) +
        D.q s * ((exposure D w ⬝ᵥ D.zf s) * (etf d ⬝ᵥ D.zE s)) +
        D.q s * ((active d ⬝ᵥ D.zA s) * (etf w ⬝ᵥ D.zE s)) +
        D.q s * ((active w ⬝ᵥ D.zA s) * (etf d ⬝ᵥ D.zE s))) := fun s => by
    rw [Novel.M2TwoStageSeparationProof.wxi, Novel.M2TwoStageSeparationProof.wxi]
    simp only [Standalone.M2TwoStageSeparation.rres]
    ring
  rw [Finset.sum_congr rfl fun s _ => e s]
  simp only [Finset.sum_add_distrib, mom_dot, h1, h2, h3, h4, h5, h6, zero_mulVec, dotProduct_zero]
  ring

/-- The marginal at `w` in the reference case, with `e = λ - γ Σ~_f b(w)`. -/
lemma grad_fund {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE}
    (hR : RefCase D Sf V SE) (w : Inst m n → ℝ) (i : Fin m) :
    grad D θ w (Sum.inl i) = θ.alpha i + (D.BA *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D w))) i -
      D.gamma * (V *ᵥ active w) i := by
  have hc := cov_ref hR (Pi.single (Sum.inl i) 1) w
  have ha : active (Pi.single (Sum.inl i) (1 : ℝ) : Inst m n → ℝ) = Pi.single i 1 := by
    funext k; simp [active, Pi.single_apply]
  have he : etf (Pi.single (Sum.inl i) (1 : ℝ) : Inst m n → ℝ) = 0 := by
    funext k; simp [etf]
  have hb : exposure D (Pi.single (Sum.inl i) (1 : ℝ)) = D.BA i := by
    funext k; simp [exposure, ha, he]
  rw [single_dotProduct, one_mul, hb, ha, he, single_dotProduct, one_mul, zero_dotProduct,
    add_zero] at hc
  simp only [grad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, mu, Sum.elim_inl, Pi.add_apply,
    mulVec_sub, mulVec_smul]
  simp only [mulVec, dotProduct]
  ring

lemma grad_etf {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE}
    (hR : RefCase D Sf V SE) (w : Inst m n → ℝ) (j : Fin n) :
    grad D θ w (Sum.inr j) = (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ exposure D w))) j - D.cE j -
      D.gamma * (SE *ᵥ etf w) j := by
  have hc := cov_ref hR (Pi.single (Sum.inr j) 1) w
  have ha : active (Pi.single (Sum.inr j) (1 : ℝ) : Inst m n → ℝ) = 0 := by
    funext k; simp [active]
  have he : etf (Pi.single (Sum.inr j) (1 : ℝ) : Inst m n → ℝ) = Pi.single j 1 := by
    funext k; simp [etf, Pi.single_apply]
  have hb : exposure D (Pi.single (Sum.inr j) (1 : ℝ)) = D.BE j := by
    funext k; simp [exposure, ha, he]
  rw [single_dotProduct, one_mul, hb, ha, he, single_dotProduct, one_mul, zero_dotProduct,
    add_zero] at hc
  simp only [grad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, mu, Sum.elim_inr,
    mulVec_sub, mulVec_smul]
  simp only [mulVec, dotProduct]
  ring

/-- The two-stage value is the score at the stage-2 holding. -/
lemma T_eq {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {bs : Fin K → ℝ} {x₂ : Inst m n → ℝ}
    (hx : x₂ ∈ fibre D bs) (hmax : IsMaxOn (Hr D θ) (fibre D bs) x₂) :
    Gf D θ bs + Vr D θ bs = score D x₂ θ := by
  have hV : Vr D θ bs = Hr D θ x₂ :=
    (show IsGreatest (Hr D θ '' fibre D bs) (Hr D θ x₂) from
      ⟨⟨x₂, hx, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmax hw⟩).csSup_eq
  rw [hV, Novel.M2TwoStageSeparationProof.split, hx.2]

/-- `T = J` iff the stage-2 holding is a joint optimum. -/
lemma TJ_iff {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {wJ : Inst m n → ℝ} (hwJ : wJ ∈ F D)
    (hmaxJ : IsMaxOn (fun w => score D w θ) (F D) wJ) {bs : Fin K → ℝ} {x₂ : Inst m n → ℝ}
    (hx : x₂ ∈ fibre D bs) (hmax : IsMaxOn (Hr D θ) (fibre D bs) x₂) :
    Gf D θ bs + Vr D θ bs = score D wJ θ ↔ IsMaxOn (fun w => score D w θ) (F D) x₂ := by
  rw [T_eq θ hx hmax]
  constructor
  · intro h w hw
    show score D w θ ≤ score D x₂ θ
    rw [h]; exact hmaxJ hw
  · intro h
    exact le_antisymm (hmaxJ hx.1) (h hwJ)

/-- With spanning ETFs strictly inside their boxes and a slack budget at a holding on the fibre of
`b*`, the ETFs alone move the exposure through a neighbourhood of `b*`, so `b*` is interior to `B_F`. -/
lemma bs_interior {m K : ℕ} {D : Data m K K S} (hBE : IsUnit D.BE.det) {bs : Fin K → ℝ}
    {x₂ : Inst m K → ℝ} (hx : x₂ ∈ fibre D bs) (hk : 0 < cash D x₂)
    (hE : ∀ j, 0 < x₂ (Sum.inr j) ∧ x₂ (Sum.inr j) < D.wbar (Sum.inr j)) : bs ∈ interior (BF D) := by
  have hU : IsUnit D.BEᵀ.det := by rwa [det_transpose]
  let φ : (Fin K → ℝ) → Inst m K → ℝ := fun b =>
    Sum.elim (active x₂) (etf x₂ + (D.BEᵀ)⁻¹ *ᵥ (b - bs))
  have hφc : Continuous φ := by
    apply continuous_pi
    rintro (i | j)
    · exact continuous_const
    · show Continuous fun b => (etf x₂ + (D.BEᵀ)⁻¹ *ᵥ (b - bs)) j
      simp only [Pi.add_apply, mulVec, dotProduct, Pi.sub_apply]
      fun_prop
  have hφ0 : φ bs = x₂ := by
    funext l; rcases l with i | j <;> simp [φ, active, etf]
  have hexp : ∀ b, exposure D (φ b) = b := by
    intro b
    show D.BAᵀ *ᵥ active x₂ + D.BEᵀ *ᵥ (etf x₂ + (D.BEᵀ)⁻¹ *ᵥ (b - bs)) = b
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec, ← add_assoc]
    rw [show D.BAᵀ *ᵥ active x₂ + D.BEᵀ *ᵥ etf x₂ = bs from hx.2]
    abel
  have hset : φ ⁻¹' {w | 0 < cash D w ∧ ∀ j, 0 < w (Sum.inr j) ∧ w (Sum.inr j) < D.wbar (Sum.inr j)} =
      {b | 0 < cash D (φ b)} ∩ ⋂ j, ({b | 0 < φ b (Sum.inr j)} ∩ {b | φ b (Sum.inr j) < D.wbar (Sum.inr j)}) := by
    ext b; simp [Set.mem_iInter]
  have hopen : IsOpen (φ ⁻¹' {w | 0 < cash D w ∧ ∀ j, 0 < w (Sum.inr j) ∧ w (Sum.inr j) < D.wbar (Sum.inr j)}) := by
    rw [hset]
    refine (isOpen_lt continuous_const ((Novel.M2ActionClassesProof.continuous_cash D).comp hφc)).inter
      (isOpen_iInter_of_finite fun j => ?_)
    have hc : Continuous fun b => φ b (Sum.inr j) := (continuous_apply (Sum.inr j)).comp hφc
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  rw [mem_interior]
  refine ⟨_, fun b hb => ⟨φ b, ⟨fun l => ?_, hb.1.le⟩, hexp b⟩, hopen, ?_⟩
  · rcases l with i | j
    · exact hx.1.1 (Sum.inl i)
    · exact ⟨(hb.2 j).1.le, (hb.2 j).2.le⟩
  · rw [Set.mem_preimage, hφ0]; exact ⟨hk, hE⟩

/-- The fund line: once the ETF lines hold, fund `i`'s `R_i` is claim 104's displayed expression
(`g_i = A_i + r_i'g_E`, with `e` cancelling). -/
lemma fund_line {m K : ℕ} {D : Data m K K S} (θ : Params m K) {Sf V SE} (hR : RefCase D Sf V SE)
    (hBE : IsUnit D.BE.det) {x₂ : Inst m K → ℝ} {b : Fin K → ℝ} (hb : exposure D x₂ = b) (η : ℝ)
    (t : Inst m K → ℝ)
    (hEl : ∀ j, (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ b))) j - D.cE j - D.gamma * (SE *ᵥ etf x₂) j =
      η + (1 + η) * t (Sum.inr j)) (i : Fin m) :
    grad D θ x₂ (Sum.inl i) - η - (1 + η) * t (Sum.inl i) =
      θ.alpha i - D.gamma * (V *ᵥ active x₂) i +
        ((D.BE⁻¹)ᵀ *ᵥ D.BA i) ⬝ᵥ (D.cE + D.gamma • (SE *ᵥ etf x₂)) +
        η * ∑ j, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) j - η -
        (1 + η) * (t (Sum.inl i) - ((D.BE⁻¹)ᵀ *ᵥ D.BA i) ⬝ᵥ (fun j => t (Sum.inr j))) := by
  rw [grad_fund θ hR, hb]
  have hBEe : D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ b)) =
      fun j => D.cE j + D.gamma * (SE *ᵥ etf x₂) j + η + (1 + η) * t (Sum.inr j) := by
    funext j; have := hEl j; linarith
  have hBA : (D.BA *ᵥ (θ.lam - D.gamma • (Sf *ᵥ b))) i =
      ((D.BE⁻¹)ᵀ *ᵥ D.BA i) ⬝ᵥ (D.BE *ᵥ (θ.lam - D.gamma • (Sf *ᵥ b))) := by
    rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, nonsing_inv_mul _ hBE, one_mulVec]
    rfl
  rw [hBA, hBEe]
  simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x * ((1 + η) * t (Sum.inr x)) =
      (1 + η) * ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x * t (Sum.inr x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x * η = η * ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x * (D.gamma * (SE *ᵥ etf x₂) x) =
      D.gamma * ∑ x, ((D.BE⁻¹)ᵀ *ᵥ D.BA i) x * (SE *ᵥ etf x₂) x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3]
  ring

theorem frictions : Frictions := by
  intro hAX m K S _ D θ Sf V SE hI hR hBE hSf hγ wJ hwJ hmaxJ bs hbs hmaxG x₂ hx₂ hmaxH hk hE
  have hTJ := TJ_iff θ hwJ hmaxJ hx₂ hmaxH
  have hsig : sigF D = Sf := hR.1
  have hint := bs_interior hBE hx₂ hk hE
  have he0 := Novel.M2TwoStageSeparationProof.grad_zero θ hI hwJ hmaxJ hbs hmaxG hint
  have he : θ.lam - D.gamma • (Sf *ᵥ exposure D x₂) = 0 := by rw [hx₂.2, ← hsig, he0, sub_self]
  have hgf : ∀ i, grad D θ x₂ (Sum.inl i) = θ.alpha i - D.gamma * (V *ᵥ active x₂) i := fun i => by
    rw [grad_fund θ hR, he, mulVec_zero, Pi.zero_apply, add_zero]
  have hge : ∀ j, grad D θ x₂ (Sum.inr j) = -D.cE j - D.gamma * (SE *ᵥ etf x₂) j := fun j => by
    rw [grad_etf θ hR, he, mulVec_zero, Pi.zero_apply, zero_sub]
  have hcrit := jointOptimality hAX m K K S D θ hI x₂ hx₂.1
  have h2 : Gf D θ bs + Vr D θ bs = score D wJ θ ↔
      (∀ j, InSlope D x₂ (Sum.inr j) (-D.cE j - D.gamma * (SE *ᵥ etf x₂) j)) ∧
      ∀ i, ∃ t, InSlope D x₂ (Sum.inl i) t ∧
        BoxSign (D.wbar (Sum.inl i)) (x₂ (Sum.inl i)) (θ.alpha i - D.gamma * (V *ᵥ active x₂) i - t) := by
    rw [hTJ, hcrit]
    constructor
    · rintro ⟨η, t, hη, hηk, ht, hRb⟩
      have hη0 : η = 0 := by
        rcases mul_eq_zero.mp hηk with h | h
        · exact h
        · linarith
      subst hη0
      refine ⟨fun j => ?_, fun i => ⟨t (Sum.inl i), ht _, ?_⟩⟩
      · have h1 := (hRb (Sum.inr j)).1 (hE j).2
        have h2 := (hRb (Sum.inr j)).2 (hE j).1
        have : grad D θ x₂ (Sum.inr j) = t (Sum.inr j) := by linarith
        rw [← hge j, this]; exact ht _
      · have := hRb (Sum.inl i)
        rw [hgf i] at this
        simpa using this
    · rintro ⟨hj, hi⟩
      choose t ht hb using hi
      refine ⟨0, Sum.elim t (fun j => -D.cE j - D.gamma * (SE *ᵥ etf x₂) j), le_rfl, zero_mul _,
        ?_, ?_⟩
      · rintro (i | j)
        · exact ht i
        · exact hj j
      · rintro (i | j)
        · simp only [Sum.elim_inl, hgf]
          simpa using hb i
        · simp only [Sum.elim_inr, hge]
          exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  refine ⟨hTJ, h2, fun hSE hTJ' j => ?_⟩
  obtain ⟨hj, -⟩ := h2.mp hTJ'
  obtain ⟨a1, a2, a3, a4⟩ := hj j
  rw [hSE, zero_mulVec, Pi.zero_apply, mul_zero, sub_zero] at a1 a2 a3 a4
  refine ⟨fun h => by linarith [a3 h], fun h => by linarith [a4 h], by linarith, by linarith⟩

theorem bindingBudget : BindingBudget := by
  intro hAX m K S _ D θ Sf V SE hI hR hBE wJ hwJ hmaxJ bs hbs x₂ hx₂ hmaxH hE e r
  rw [TJ_iff θ hwJ hmaxJ hx₂ hmaxH, jointOptimality hAX m K K S D θ hI x₂ hx₂.1]
  have hge : ∀ j, grad D θ x₂ (Sum.inr j) = (D.BE *ᵥ e) j - D.cE j - D.gamma * (SE *ᵥ etf x₂) j :=
    fun j => by rw [grad_etf θ hR, hx₂.2]
  have hfl := fun η t hEl i => fund_line θ hR hBE hx₂.2 η t hEl i
  constructor
  · rintro ⟨η, t, hη, hηk, ht, hRb⟩
    have hEl : ∀ j, (D.BE *ᵥ e) j - D.cE j - D.gamma * (SE *ᵥ etf x₂) j = η + (1 + η) * t (Sum.inr j) :=
      fun j => by
        have h1 := (hRb (Sum.inr j)).1 (hE j).2
        have h2 := (hRb (Sum.inr j)).2 (hE j).1
        rw [hge j] at h1 h2
        linarith
    refine ⟨η, t, hη, hηk, ht, hEl, fun i => ?_⟩
    have := hRb (Sum.inl i)
    rwa [hfl η t hEl i] at this
  · rintro ⟨η, t, hη, hηk, ht, hEl, hFl⟩
    refine ⟨η, t, hη, hηk, ht, ?_⟩
    rintro (i | j)
    · rw [hfl η t hEl i]; exact hFl i
    · have : grad D θ x₂ (Sum.inr j) - η - (1 + η) * t (Sum.inr j) = 0 := by rw [hge j, hEl j]; ring
      rw [this]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

theorem softMultiplier : SoftMultiplier := by
  intro m n K S _ D θ Sf hI hsig hSf hγ R bs hbs hmax
  have hU : IsUnit (D.gamma • Sf).det := by
    rw [det_smul]; exact (mul_pos (pow_pos hγ _) hSf.det_pos).ne'.isUnit
  have hTB : D.gamma • (sigF D *ᵥ ((D.gamma • Sf)⁻¹ *ᵥ θ.lam)) = θ.lam := by
    rw [hsig, ← smul_mulVec, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun hc b hb => ?_⟩
  · have h1 : D.gamma • (Sf *ᵥ bs) = θ.lam := by
      have h' : θ.lam - D.gamma • (sigF D *ᵥ bs) = 0 := h
      rw [← hsig]; exact (sub_eq_zero.mp h').symm
    have hbs' : bs = (D.gamma • Sf)⁻¹ *ᵥ θ.lam := by
      rw [← h1, ← smul_mulVec, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
    rw [← hbs']; exact hbs
  · have h1 : Gf D θ ((D.gamma • Sf)⁻¹ *ᵥ θ.lam) ≤ Gf D θ bs := hmax h
    have h2 := G_TB θ hTB bs
    have h3 := sqN_nonpos hγ (show D.gamma / 2 * sqN D (bs - (D.gamma • Sf)⁻¹ *ᵥ θ.lam) ≤ 0 by linarith)
    have hbs' : bs = (D.gamma • Sf)⁻¹ *ᵥ θ.lam := sub_eq_zero.mp (sqN_zero hsig hSf h3)
    show θ.lam - D.gamma • (sigF D *ᵥ bs) = 0
    rw [hbs', hTB, sub_self]
  · have := Novel.M2TwoStageSeparationProof.foc D θ hI.2.2.1 hI.2.2.2 hc hbs hmax hb
    rw [dotProduct_comm]; exact this

end Criteria

/-! ### Part 3a: norms -/

section Norms

variable {k : ℕ}

lemma enorm2_nonneg (v : Fin k → ℝ) : 0 ≤ enorm2 v := Real.sqrt_nonneg _

lemma dot_self_nonneg (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma enorm2_sq (v : Fin k → ℝ) : enorm2 v ^ 2 = v ⬝ᵥ v := Real.sq_sqrt (dot_self_nonneg v)

/-- Cauchy-Schwarz. -/
lemma dot_le (u v : Fin k → ℝ) : u ⬝ᵥ v ≤ enorm2 u * enorm2 v := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have e : u ⬝ᵥ v = ∑ i, u i * v i := rfl
  have eu : u ⬝ᵥ u = ∑ i, u i ^ 2 := by simp [dotProduct, sq]
  have ev : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
  rw [← e, ← eu, ← ev] at h
  have hsq : (u ⬝ᵥ v) ^ 2 ≤ (enorm2 u * enorm2 v) ^ 2 := by rw [mul_pow, enorm2_sq, enorm2_sq]; exact h
  exact abs_le_of_sq_le_sq' hsq (mul_nonneg (enorm2_nonneg u) (enorm2_nonneg v)) |>.2

lemma enorm2_add (u v : Fin k → ℝ) : enorm2 (u + v) ≤ enorm2 u + enorm2 v := by
  have h1 := dot_le u v
  have h2 : (u + v) ⬝ᵥ (u + v) ≤ (enorm2 u + enorm2 v) ^ 2 := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm v u, add_sq, enorm2_sq,
      enorm2_sq]
    linarith
  calc enorm2 (u + v) = Real.sqrt ((u + v) ⬝ᵥ (u + v)) := rfl
    _ ≤ Real.sqrt ((enorm2 u + enorm2 v) ^ 2) := Real.sqrt_le_sqrt h2
    _ = enorm2 u + enorm2 v := Real.sqrt_sq (add_nonneg (enorm2_nonneg u) (enorm2_nonneg v))

lemma enorm2_neg (v : Fin k → ℝ) : enorm2 (-v) = enorm2 v := by
  simp [enorm2, neg_dotProduct, dotProduct_neg]

lemma enorm2_smul (c : ℝ) (v : Fin k → ℝ) : enorm2 (c • v) = |c| * enorm2 v := by
  simp only [enorm2, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc]
  rw [Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

lemma enorm2_abs (v : Fin k → ℝ) : enorm2 (fun i => |v i|) = enorm2 v := by
  simp [enorm2, dotProduct, abs_mul_abs_self]

/-- Coordinatewise `|p| ≤ x̄` bounds the norm. -/
lemma enorm2_mono {p x : Fin k → ℝ} (h : ∀ i, |p i| ≤ x i) : enorm2 p ≤ enorm2 x := by
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => by
    have := h i
    nlinarith [abs_nonneg (p i), abs_mul_abs_self (p i)]

/-- Cauchy-Schwarz for a positive semidefinite symmetric form. -/
lemma psd_cs {M : Matrix (Fin k) (Fin k) ℝ} (hM : ∀ y, 0 ≤ y ⬝ᵥ (M *ᵥ y)) (hs : Mᵀ = M)
    (x y : Fin k → ℝ) : (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  have hsym := Novel.M5PartialAdjustmentSplitProof.sym_dot hs x y
  have hq : ∀ t : ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) - 2 * t * (x ⬝ᵥ (M *ᵥ y)) + t ^ 2 * (y ⬝ᵥ (M *ᵥ y)) := by
    intro t
    have := hM (x - t • y)
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at this
    rw [hsym] at this ⊢
    nlinarith [this]
  rcases (hM y).lt_or_eq with hpos | hzero
  · have := hq ((x ⬝ᵥ (M *ᵥ y)) / (y ⬝ᵥ (M *ᵥ y)))
    field_simp at this
    nlinarith
  · have hc : x ⬝ᵥ (M *ᵥ y) = 0 := by
      by_contra hc
      have h1 := hq ((x ⬝ᵥ (M *ᵥ x) + 1) / (2 * (x ⬝ᵥ (M *ᵥ y))))
      rw [← hzero] at h1
      have e : 2 * ((x ⬝ᵥ (M *ᵥ x) + 1) / (2 * (x ⬝ᵥ (M *ᵥ y)))) * (x ⬝ᵥ (M *ᵥ y)) =
          x ⬝ᵥ (M *ᵥ x) + 1 := by field_simp
      linarith
    rw [hc, ← hzero]; simp

end Norms

/-! ### Part 3a: the ETF friction bound -/

section EtfBound

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN sigF Inputs)

/-- The ETF direction `(0, δ)`. -/
def esh {m n : ℕ} (δ : Fin n → ℝ) : Inst m n → ℝ := Sum.elim 0 δ

lemma Hr_ref {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE} (hR : RefCase D Sf V SE)
    (w : Inst m n → ℝ) :
    Hr D θ w = active w ⬝ᵥ θ.alpha - etf w ⬝ᵥ D.cE -
      D.gamma / 2 * (active w ⬝ᵥ (V *ᵥ active w) + etf w ⬝ᵥ (SE *ᵥ etf w)) - tau D (w - w0 D) := by
  simp only [Standalone.M2TwoStageSeparation.Hr, cross_zero hR, res_eq hR, dotProduct_zero, mul_zero,
    zero_add]

lemma mom_symm {S : Type} [Fintype S] {a : ℕ} (q : S → ℝ) (x : S → Fin a → ℝ) :
    (mom q x x)ᵀ = mom q x x := by
  funext i j; simp only [transpose_apply, mom]; exact Finset.sum_congr rfl fun _ _ => by ring

/-- Moving the ETFs by `ε δ` lowers `H` by at most the fee, residual and cost slopes, to second
order. -/
lemma Hr_shift {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE} (hR : RefCase D Sf V SE)
    (hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l) (w : Inst m n → ℝ) (δ : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    Hr D θ w - ε * (δ ⬝ᵥ D.cE + D.gamma * (δ ⬝ᵥ (SE *ᵥ etf w)) +
        ∑ j, max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) * |δ j|) -
      D.gamma / 2 * (ε ^ 2 * (δ ⬝ᵥ (SE *ᵥ δ))) ≤ Hr D θ (w + ε • esh δ) := by
  have hSE : SEᵀ = SE := by rw [← hR.2.2.1]; exact mom_symm _ _
  have ha : active (w + ε • esh δ) = active w := by funext i; simp [active, esh]
  have he : etf (w + ε • esh δ) = etf w + ε • δ := by funext j; simp [etf, esh]
  have htau : tau D (w + ε • esh δ - w0 D) - tau D (w - w0 D) ≤
      ε * ∑ j, max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) * |δ j| := by
    simp only [tau, Fintype.sum_sum_type, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, esh,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, add_zero]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨h1, h2⟩ := hr (Sum.inr j)
    have hc := cost_change (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) (w0 D (Sum.inr j))
      (w (Sum.inr j)) (w (Sum.inr j) + ε * δ j) h1 h2
    rw [show w (Sum.inr j) + ε * δ j - w (Sum.inr j) = ε * δ j by ring,
      show w (Sum.inr j) - (w (Sum.inr j) + ε * δ j) = -(ε * δ j) by ring] at hc
    have hk : D.kplus (Sum.inr j) * max (ε * δ j) 0 + D.kminus (Sum.inr j) * max (-(ε * δ j)) 0 ≤
        ε * (max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) * |δ j|) := by
      rcases le_total 0 (δ j) with hd | hd
      · rw [max_eq_left (mul_nonneg hε hd), max_eq_right (by nlinarith), abs_of_nonneg hd]
        nlinarith [le_max_left (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)), mul_nonneg hε hd]
      · rw [max_eq_right (by nlinarith), max_eq_left (by nlinarith), abs_of_nonpos hd]
        nlinarith [le_max_right (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)),
          mul_nonneg hε (neg_nonneg.mpr hd)]
    have e1 : -(w (Sum.inr j) + ε * δ j - w0 D (Sum.inr j)) = w0 D (Sum.inr j) - (w (Sum.inr j) + ε * δ j) := by
      ring
    have e2 : -(w (Sum.inr j) - w0 D (Sum.inr j)) = w0 D (Sum.inr j) - w (Sum.inr j) := by ring
    rw [e1, e2]
    linarith
  have hq : (etf w + ε • δ) ⬝ᵥ (SE *ᵥ (etf w + ε • δ)) =
      etf w ⬝ᵥ (SE *ᵥ etf w) + 2 * ε * (δ ⬝ᵥ (SE *ᵥ etf w)) + ε ^ 2 * (δ ⬝ᵥ (SE *ᵥ δ)) := by
    have hs := Novel.M5PartialAdjustmentSplitProof.sym_dot hSE (etf w) δ
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [hs]; ring
  rw [Hr_ref θ hR, Hr_ref θ hR, ha, he, hq]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm δ D.cE] at *
  nlinarith [htau]

/-- Along a continuous path starting at a holding with a slack budget and interior ETFs, and keeping
the funds in their boxes, the path stays in `F` for small positive times. -/
lemma eventually_F {m n K : ℕ} {D : Data m n K S} {x : Inst m n → ℝ} (hk : 0 < cash D x)
    (hE : ∀ j, 0 < x (Sum.inr j) ∧ x (Sum.inr j) < D.wbar (Sum.inr j)) (y : ℝ → Inst m n → ℝ)
    (hyc : Continuous y) (hy0 : y 0 = x)
    (hfund : ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ i, 0 ≤ y ε (Sum.inl i) ∧ y ε (Sum.inl i) ≤ D.wbar (Sum.inl i)) :
    ∀ᶠ ε in 𝓝[>] 0, y ε ∈ F D := by
  have ev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < cash D (y ε) := by
    have h : Tendsto (fun ε => cash D (y ε)) (𝓝 0) (𝓝 (cash D x)) := by
      rw [← hy0]; exact ((Novel.M2ActionClassesProof.continuous_cash D).comp hyc).tendsto 0
    exact h.eventually (lt_mem_nhds hk)
  have ev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j, 0 < y ε (Sum.inr j) ∧ y ε (Sum.inr j) < D.wbar (Sum.inr j) := by
    rw [Filter.eventually_all]
    intro j
    have h : Tendsto (fun ε => y ε (Sum.inr j)) (𝓝 0) (𝓝 (x (Sum.inr j))) := by
      rw [← hy0]; exact ((continuous_apply _).comp hyc).tendsto 0
    exact (h.eventually (lt_mem_nhds (hE j).1)).and (h.eventually (gt_mem_nhds (hE j).2))
  filter_upwards [(ev1.and ev2).filter_mono nhdsWithin_le_nhds,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε ⟨h1, h2⟩ h3
  refine ⟨fun l => ?_, h1.le⟩
  rcases l with i | j
  · exact hfund ε h3.1.le h3.2.le i
  · exact ⟨(h2 j).1.le, (h2 j).2.le⟩

lemma le_of_eventually {A B Q : ℝ} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A ≤ B + ε * Q) : A ≤ B := by
  have ht : Tendsto (fun ε : ℝ => B + ε * Q) (𝓝[>] 0) (𝓝 (B + 0 * Q)) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto ht h

lemma en_SE {k : ℕ} {SE : Matrix (Fin k) (Fin k) ℝ} {σE : ℝ} (hσ : 0 ≤ σE)
    (hσE : ∀ p, (SE *ᵥ p) ⬝ᵥ (SE *ᵥ p) ≤ σE ^ 2 * (p ⬝ᵥ p)) (p : Fin k → ℝ) :
    enorm2 (SE *ᵥ p) ≤ σE * enorm2 p := by
  calc enorm2 (SE *ᵥ p) ≤ Real.sqrt (σE ^ 2 * (p ⬝ᵥ p)) := Real.sqrt_le_sqrt (hσE p)
    _ = σE * enorm2 p := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ]; rfl

lemma exposure_add {m n K : ℕ} (D : Data m n K S) (x y : Inst m n → ℝ) :
    exposure D (x + y) = exposure D x + exposure D y := by
  have ha : active (x + y) = active x + active y := rfl
  have he : etf (x + y) = etf x + etf y := rfl
  simp only [exposure, ha, he, mulVec_add]; abel

lemma exposure_smul {m n K : ℕ} (D : Data m n K S) (c : ℝ) (x : Inst m n → ℝ) :
    exposure D (c • x) = c • exposure D x := by
  have ha : active (c • x) = c • active x := rfl
  have he : etf (c • x) = c • etf x := rfl
  simp only [exposure, ha, he, mulVec_smul, smul_add]

lemma exposure_esh {m n K : ℕ} (D : Data m n K S) (δ : Fin n → ℝ) :
    exposure D (esh δ) = D.BEᵀ *ᵥ δ := by
  have ha : active (esh δ : Inst m n → ℝ) = 0 := by funext i; simp [active, esh]
  have he : etf (esh δ : Inst m n → ℝ) = δ := by funext j; simp [etf, esh]
  simp only [exposure, ha, he, mulVec_zero, zero_add]

theorem etfFrictionBound : EtfFrictionBound := by
  intro m K S _ D θ Sf V SE L0 σE hI hR hBE hSf hγ hL0 hL hσ hσE wJ hwJ hmaxJ bs hbs hmaxG x₂ hx₂
    hmaxH hk hE LE
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  have hsig : sigF D = Sf := hR.1
  have hq := hI.2.2.1
  set C := enorm2 D.cE + D.gamma * σE * enorm2 (fun j => D.wbar (Sum.inr j)) +
    enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) with hC
  have hLE : LE = L0 * C := rfl
  have hC0 : 0 ≤ C := by
    have := enorm2_nonneg D.cE
    have := enorm2_nonneg (fun j => D.wbar (Sum.inr j))
    have := enorm2_nonneg (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)))
    have := mul_nonneg (mul_nonneg hγ.le hσ) (enorm2_nonneg (fun j => D.wbar (Sum.inr j)))
    linarith
  -- the slope term is at most `C ‖δ‖`
  have hslope : ∀ z : Inst m K → ℝ, (∀ j, 0 ≤ z (Sum.inr j) ∧ z (Sum.inr j) ≤ D.wbar (Sum.inr j)) →
      ∀ δ : Fin K → ℝ, δ ⬝ᵥ D.cE + D.gamma * (δ ⬝ᵥ (SE *ᵥ etf z)) +
        ∑ j, max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) * |δ j| ≤ C * enorm2 δ := by
    intro z hz δ
    have h1 := dot_le δ D.cE
    have h2 := dot_le δ (SE *ᵥ etf z)
    have h3 := en_SE hσ hσE (etf z)
    have h4 : enorm2 (etf z) ≤ enorm2 (fun j => D.wbar (Sum.inr j)) :=
      enorm2_mono fun j => by
        show |z (Sum.inr j)| ≤ _
        rw [abs_of_nonneg (hz j).1]; exact (hz j).2
    have h5 := dot_le (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) (fun j => |δ j|)
    rw [enorm2_abs] at h5
    have h5' : ∑ j, max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) * |δ j| ≤
        enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) * enorm2 δ := h5
    have hδ0 := enorm2_nonneg δ
    have h6 : δ ⬝ᵥ (SE *ᵥ etf z) ≤ enorm2 δ * (σE * enorm2 (fun j => D.wbar (Sum.inr j))) :=
      h2.trans (mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hσ)) hδ0)
    rw [hC]
    nlinarith [mul_le_mul_of_nonneg_left h6 hγ.le]
  have hVbs : Vr D θ bs = Hr D θ x₂ :=
    (show IsGreatest (Hr D θ '' fibre D bs) (Hr D θ x₂) from
      ⟨⟨x₂, hx₂, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmaxH hw⟩).csSup_eq
  have hSE0 : ∀ y, 0 ≤ y ⬝ᵥ (SE *ᵥ y) := fun y => by
    rw [← hR.2.2.1, ← mom_dot]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (mul_self_nonneg _)
  have hU : IsUnit D.BEᵀ.det := by rwa [det_transpose]
  -- part (b): the value gap is at most `C ‖δ‖`, with `δ` the ETF shift back to `b*`
  have hbJ : exposure D wJ ∈ BF D := ⟨wJ, hwJ, rfl⟩
  obtain ⟨x', hx', -, hV'⟩ := Novel.M2TwoStageSeparationProof.V_attain θ hI hbJ
  set δ := (D.BEᵀ)⁻¹ *ᵥ (bs - exposure D wJ) with hδ
  have hgap : Hr D θ x' - Hr D θ x₂ ≤ C * enorm2 δ := by
    let y : ℝ → Inst m K → ℝ := fun ε => (1 - ε) • x₂ + ε • x' + ε • esh δ
    have hyc : Continuous y := by fun_prop
    have hy0 : y 0 = x₂ := by simp [y]
    have hfund : ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ i, 0 ≤ y ε (Sum.inl i) ∧ y ε (Sum.inl i) ≤ D.wbar (Sum.inl i) := by
      intro ε h0 h1 i
      have a1 := hx₂.1.1 (Sum.inl i)
      have a2 := hx'.1.1 (Sum.inl i)
      simp only [y, esh, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Pi.zero_apply, mul_zero,
        add_zero]
      constructor <;> nlinarith
    have hexp : ∀ ε, exposure D (y ε) = bs := fun ε => by
      simp only [y, exposure_add, exposure_smul, exposure_esh, hδ, mulVec_mulVec, mul_nonsing_inv _ hU,
        one_mulVec, hx₂.2, hx'.2]
      module
    refine le_of_eventually (Q := D.gamma / 2 * (δ ⬝ᵥ (SE *ᵥ δ))) ?_
    filter_upwards [eventually_F hk hE y hyc hy0 hfund, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with ε hyF hε
    have h1 : Hr D θ (y ε) ≤ Hr D θ x₂ := hmaxH ⟨hyF, hexp ε⟩
    have hz : (1 - ε) • x₂ + ε • x' ∈ F D :=
      Novel.M2TwoStageSeparationProof.F_convex hI hx₂.1 hx'.1 (by linarith [hε.2]) hε.1.le (by ring)
    have h2 := Novel.M2TwoStageSeparationProof.H_concave θ hI (fun w _ => cross_zero hR w) hx₂.1 hx'.1
      (a := 1 - ε) (b := ε) (by linarith [hε.2]) hε.1.le (by ring)
    have h3 := Hr_shift θ hR hr ((1 - ε) • x₂ + ε • x') δ hε.1.le
    have h4 := hslope ((1 - ε) • x₂ + ε • x') (fun j => hz.1 (Sum.inr j)) δ
    have hQ := hSE0 δ
    have h5 : ε * (Hr D θ x' - Hr D θ x₂) ≤ ε * (C * enorm2 δ + ε * (D.gamma / 2 * (δ ⬝ᵥ (SE *ᵥ δ)))) := by
      simp only [y] at h1
      nlinarith [mul_le_mul_of_nonneg_left h4 hε.1.le]
    exact le_of_mul_le_mul_left h5 hε.1
  -- `‖δ‖ ≤ L0 ‖b_J - b*‖_{Σ~}`
  have hsym : Sfᵀ = Sf := Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hSf.posSemidef
  have hSfU := Novel.M5PartialAdjustmentSplitProof.pd_unit hSf
  have hSf0 : ∀ y, 0 ≤ y ⬝ᵥ (Sf *ᵥ y) := fun y => by
    have := hSf.posSemidef.dotProduct_mulVec_nonneg y; simpa using this
  have hsqN : sqN D (exposure D wJ - bs) = (bs - exposure D wJ) ⬝ᵥ (Sf *ᵥ (bs - exposure D wJ)) := by
    simp only [sqN, hsig]
    rw [show exposure D wJ - bs = -(bs - exposure D wJ) by abel, mulVec_neg, neg_dotProduct,
      dotProduct_neg, neg_neg]
  have hδn : enorm2 δ ≤ L0 * Real.sqrt (sqN D (exposure D wJ - bs)) := by
    set Δ := bs - exposure D wJ
    have hRt : (D.BEᵀ)⁻¹ = (D.BE⁻¹)ᵀ := (transpose_nonsing_inv D.BE).symm
    have hδ' : δ = (D.BE⁻¹)ᵀ *ᵥ Δ := by rw [hδ, hRt]
    have hdd : δ ⬝ᵥ δ = Δ ⬝ᵥ (D.BE⁻¹ *ᵥ δ) := by
      calc δ ⬝ᵥ δ = ((D.BE⁻¹)ᵀ *ᵥ Δ) ⬝ᵥ δ := by rw [← hδ']
        _ = Δ ⬝ᵥ (D.BE⁻¹ *ᵥ δ) := by
          have gen : ∀ (A : Matrix (Fin K) (Fin K) ℝ) (u v : Fin K → ℝ), (Aᵀ *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) :=
            fun A u v => by rw [mulVec_transpose, ← dotProduct_mulVec]
          exact gen _ _ _
    have hinvs : (Sf⁻¹)ᵀ = Sf⁻¹ := Novel.M5PartialAdjustmentSplitProof.inv_sym hsym
    have hcs := psd_cs hSf0 hsym Δ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ δ))
    have hSS : Sf *ᵥ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ δ)) = D.BE⁻¹ *ᵥ δ := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hSfU, one_mulVec]
    rw [hSS, ← hdd] at hcs
    have hyy : (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ δ)) ⬝ᵥ (D.BE⁻¹ *ᵥ δ) ≤ L0 ^ 2 * (δ ⬝ᵥ δ) := by
      rw [dotProduct_comm]; exact hL δ
    have hdd0 := dot_self_nonneg δ
    have hΔ0 := hSf0 Δ
    have key : δ ⬝ᵥ δ ≤ L0 ^ 2 * (Δ ⬝ᵥ (Sf *ᵥ Δ)) := by
      rcases hdd0.lt_or_eq with hpos | hzero
      · have : (δ ⬝ᵥ δ) ^ 2 ≤ (Δ ⬝ᵥ (Sf *ᵥ Δ)) * (L0 ^ 2 * (δ ⬝ᵥ δ)) :=
          hcs.trans (mul_le_mul_of_nonneg_left hyy hΔ0)
        nlinarith
      · rw [← hzero]; positivity
    rw [hsqN]
    calc enorm2 δ = Real.sqrt (δ ⬝ᵥ δ) := rfl
      _ ≤ Real.sqrt (L0 ^ 2 * (Δ ⬝ᵥ (Sf *ᵥ Δ))) := Real.sqrt_le_sqrt key
      _ = L0 * Real.sqrt (Δ ⬝ᵥ (Sf *ᵥ Δ)) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL0]
  have hVgap : Vr D θ (exposure D wJ) - Vr D θ bs ≤ LE * Real.sqrt (sqN D (exposure D wJ - bs)) := by
    rw [hV', hVbs, hLE]
    calc Hr D θ x' - Hr D θ x₂ ≤ C * enorm2 δ := hgap
      _ ≤ C * (L0 * Real.sqrt (sqN D (exposure D wJ - bs))) := mul_le_mul_of_nonneg_left hδn hC0
      _ = L0 * C * Real.sqrt (sqN D (exposure D wJ - bs)) := by ring
  refine ⟨fun s hs => ?_, hVgap, ?_⟩
  · -- part (a): each coordinate of `u = -(c^E + γ Σ_E p + B^E s)` is at most `κ^max` in size
    have hu : ∀ j, |-D.cE j - D.gamma * (SE *ᵥ etf x₂) j - (D.BE *ᵥ s) j| ≤
        max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) := by
      intro j
      have side : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
          σ * (-D.cE j - D.gamma * (SE *ᵥ etf x₂) j - (D.BE *ᵥ s) j) ≤
            max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) := by
        intro σ hσ1
        have hσa : |σ| = 1 := by rcases hσ1 with rfl | rfl <;> simp
        set d : Fin K → ℝ := σ • Pi.single j 1 with hd
        let y : ℝ → Inst m K → ℝ := fun ε => x₂ + ε • esh d
        have hyc : Continuous y := by fun_prop
        have hy0 : y 0 = x₂ := by simp [y]
        have hfund : ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ i, 0 ≤ y ε (Sum.inl i) ∧ y ε (Sum.inl i) ≤ D.wbar (Sum.inl i) :=
          fun ε _ _ i => by simpa [y, esh] using hx₂.1.1 (Sum.inl i)
        have hdc : d ⬝ᵥ D.cE = σ * D.cE j := by simp [hd]
        have hds : d ⬝ᵥ (SE *ᵥ etf x₂) = σ * (SE *ᵥ etf x₂) j := by simp [hd]
        have hdk : ∑ i, max (D.kplus (Sum.inr i)) (D.kminus (Sum.inr i)) * |d i| =
            max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) := by
          rw [Finset.sum_eq_single j (fun b _ hb => by simp [hd, hb]) (by simp)]
          simp [hd, hσa]
        have hdb : s ⬝ᵥ (D.BEᵀ *ᵥ d) = σ * (D.BE *ᵥ s) j := by
          rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]; simp [hd]
        refine le_of_eventually (Q := D.gamma / 2 * (d ⬝ᵥ (SE *ᵥ d))) ?_
        filter_upwards [eventually_F hk hE y hyc hy0 hfund, self_mem_nhdsWithin] with ε hyF (hε : 0 < ε)
        have hex : exposure D (y ε) = bs + ε • (D.BEᵀ *ᵥ d) := by
          simp only [y, exposure_add, exposure_smul, exposure_esh, hx₂.2]
        have h1 : Hr D θ (y ε) ≤ Vr D θ (bs + ε • (D.BEᵀ *ᵥ d)) :=
          Novel.M2TwoStageSeparationProof.H_le_V θ hI ⟨hyF, hex⟩
        have h2 := hs _ ⟨y ε, hyF, hex⟩
        rw [add_sub_cancel_left, dotProduct_smul, smul_eq_mul, hdb] at h2
        have h3 := Hr_shift θ hR hr x₂ d hε.le
        rw [hdc, hds, hdk] at h3
        rw [hVbs] at h2
        have h4 : ε * (σ * (-D.cE j - D.gamma * (SE *ᵥ etf x₂) j - (D.BE *ᵥ s) j)) ≤
            ε * (max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j)) + ε * (D.gamma / 2 * (d ⬝ᵥ (SE *ᵥ d)))) := by
          simp only [y] at h1
          nlinarith
        exact le_of_mul_le_mul_left h4 hε
      have hp := side 1 (Or.inl rfl)
      have hn := side (-1) (Or.inr rfl)
      rw [abs_le]; constructor <;> linarith
    -- `s = R w` with `w = B^E s`
    set w := D.BE *ᵥ s with hw
    have hsw : s = D.BE⁻¹ *ᵥ w := by rw [hw, mulVec_mulVec, nonsing_inv_mul _ hBE, one_mulVec]
    have hwv : w = -(D.cE + D.gamma • (SE *ᵥ etf x₂) + fun j => -D.cE j - D.gamma * (SE *ᵥ etf x₂) j - w j) := by
      funext j; simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hen : enorm2 w ≤ C := by
      rw [hwv, enorm2_neg]
      refine (enorm2_add _ _).trans ?_
      have h1 := enorm2_add D.cE (D.gamma • (SE *ᵥ etf x₂))
      rw [enorm2_smul, abs_of_pos hγ] at h1
      have h2 := en_SE hσ hσE (etf x₂)
      have h3 : enorm2 (etf x₂) ≤ enorm2 (fun j => D.wbar (Sum.inr j)) :=
        enorm2_mono fun j => by
          show |x₂ (Sum.inr j)| ≤ _
          rw [abs_of_nonneg (hx₂.1.1 (Sum.inr j)).1]; exact (hx₂.1.1 (Sum.inr j)).2
      have h4 : enorm2 (fun j => -D.cE j - D.gamma * (SE *ᵥ etf x₂) j - w j) ≤
          enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) :=
        enorm2_mono fun j => hu j
      rw [hC]
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hσ)) hγ.le]
    rw [hsw, hLE]
    have h1 := hL w
    have h2 : w ⬝ᵥ w ≤ C ^ 2 := by
      rw [← enorm2_sq]; exact pow_le_pow_left₀ (enorm2_nonneg w) hen 2
    calc (D.BE⁻¹ *ᵥ w) ⬝ᵥ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ w)) ≤ L0 ^ 2 * (w ⬝ᵥ w) := h1
      _ ≤ L0 ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (L0 * C) ^ 2 := by ring
  · -- part (c): the loss bound
    have h1 := (Novel.M2TwoStageSeparationProof.lossBound θ hI hwJ hmaxJ hbs hmaxG).1
    set x := Real.sqrt (sqN D (exposure D wJ - bs))
    have hQ := Novel.M2TwoStageSeparationProof.sqN_nonneg D hq (exposure D wJ - bs)
    have hx2 : x ^ 2 = sqN D (exposure D wJ - bs) := Real.sq_sqrt hQ
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    rw [← hx2] at h1
    refine le_min ?_ (by nlinarith [mul_nonneg hγ.le (sq_nonneg x)])
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (LE - D.gamma * x)]

end EtfBound

/-! ### Part 3c's bound: the stage-2 problem's multipliers -/

section FibreKKT

variable {S : Type} [Fintype S]

open Standalone.M2TwoStageSeparation (Gf Hr BF fibre Vr sqN sigF Inputs)

/-- Stage-2 constraints: the lifted rows plus the exposure rows `b(x) ≤ b*` and `-b(x) ≤ -b*`. -/
abbrev Lf (m n K : ℕ) := Lm m n ⊕ (Fin K ⊕ Fin K)

/-- The exposure row `z ↦ b(x)_k`. -/
def eA {m n K : ℕ} (D : Data m n K S) (k : Fin K) : Io m n → ℝ
  | Sum.inl (Sum.inl i) => D.BA i k
  | Sum.inl (Sum.inr j) => D.BE j k
  | Sum.inr _ => 0

def fA {m n K : ℕ} (D : Data m n K S) : Lf m n K → Io m n → ℝ :=
  Sum.elim (cA D) (Sum.elim (eA D) (fun k => -eA D k))

def fB {m n K : ℕ} (D : Data m n K S) (bs : Fin K → ℝ) : Lf m n K → ℝ :=
  Sum.elim (cB D) (Sum.elim bs (fun k => -bs k))

/-- The lifted stage-2 objective (claim 104's `H` in the reference case, with the cost lifted). -/
def fH {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (V : Matrix (Fin m) (Fin m) ℝ)
    (SE : Matrix (Fin n) (Fin n) ℝ) (z : Io m n → ℝ) : ℝ :=
  active (xs z) ⬝ᵥ θ.alpha - etf (xs z) ⬝ᵥ D.cE -
    D.gamma / 2 * (active (xs z) ⬝ᵥ (V *ᵥ active (xs z)) + etf (xs z) ⬝ᵥ (SE *ᵥ etf (xs z))) -
    ∑ l, ys z l

lemma dot_eA {m n K : ℕ} (D : Data m n K S) (k : Fin K) (z : Io m n → ℝ) :
    eA D k ⬝ᵥ z = exposure D (xs z) k := by
  simp [eA, dotProduct, Fintype.sum_sum_type, exposure, mulVec, xs, active, etf, transpose_apply,
    mul_comm]

lemma fH_lift {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE} (hR : RefCase D Sf V SE)
    (x : Inst m n → ℝ) : fH D θ V SE (lift D x) = Hr D θ x := by
  rw [Hr_ref θ hR, tau_costl]; rfl

lemma mom_convex {a : ℕ} (q : S → ℝ) (hq : ∀ s, 0 ≤ q s) (x : S → Fin a → ℝ) (u v : Fin a → ℝ)
    {α β : ℝ} (ha : 0 ≤ α) (hb : 0 ≤ β) (hab : α + β = 1) :
    (α • u + β • v) ⬝ᵥ (mom q x x *ᵥ (α • u + β • v)) ≤
      α * (u ⬝ᵥ (mom q x x *ᵥ u)) + β * (v ⬝ᵥ (mom q x x *ᵥ v)) := by
  simp only [← mom_dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hb' : β = 1 - α := by linarith
  subst hb'
  nlinarith [mul_nonneg (hq s) (mul_nonneg ha hb), sq_nonneg (u ⬝ᵥ x s - v ⬝ᵥ x s)]

lemma fH_concave {m n K : ℕ} {D : Data m n K S} (θ : Params m K) {Sf V SE}
    (hR : RefCase D Sf V SE) (hq : ∀ s, 0 ≤ D.q s) (hγ : 0 ≤ D.gamma) :
    ConcaveOn ℝ Set.univ (fH D θ V SE) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨-, h2, h3, -, -, -⟩ := hR
  have hA := mom_convex D.q hq D.zA (active (xs x)) (active (xs y)) ha hb hab
  have hE := mom_convex D.q hq D.zE (etf (xs x)) (etf (xs y)) ha hb hab
  rw [h2] at hA; rw [h3] at hE
  have hxa : active (xs (a • x + b • y)) = a • active (xs x) + b • active (xs y) := rfl
  have hxe : etf (xs (a • x + b • y)) = a • etf (xs x) + b • etf (xs y) := rfl
  have l1 : (a • active (xs x) + b • active (xs y)) ⬝ᵥ θ.alpha =
      a * (active (xs x) ⬝ᵥ θ.alpha) + b * (active (xs y) ⬝ᵥ θ.alpha) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have l2 : (a • etf (xs x) + b • etf (xs y)) ⬝ᵥ D.cE =
      a * (etf (xs x) ⬝ᵥ D.cE) + b * (etf (xs y) ⬝ᵥ D.cE) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have l3 : ∑ l, ys (a • x + b • y) l = a * ∑ l, ys x l + b * ∑ l, ys y l := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; rfl
  show a * fH D θ V SE x + b * fH D θ V SE y ≤ fH D θ V SE (a • x + b • y)
  simp only [fH]
  rw [hxa, hxe, l1, l2, l3]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hA hE) (by positivity : 0 ≤ D.gamma / 2)]

/-- A supergradient's pairing with a direction along which `f` is an exact quadratic is the slope. -/
lemma deriv_eq {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℝ} {z s d : ι → ℝ} {g q : ℝ} (hq : 0 ≤ q)
    (hp : ∀ ε : ℝ, f (z + ε • d) = f z + ε * g - ε ^ 2 * q)
    (hsup : ∀ y, f y ≤ f z + s ⬝ᵥ (y - z)) : g = s ⬝ᵥ d := by
  have half : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → σ * (g - s ⬝ᵥ d) ≤ 0 := fun σ hσ => by
    refine le_of_forall_eps hq fun ε hε => ?_
    have h := hsup (z + (σ * ε) • d)
    rw [hp, add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at h
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have e1 : (σ * ε) ^ 2 * q = ε * (ε * q) := by rw [mul_pow, hσ2]; ring
    have e2 : ε * (σ * (g - s ⬝ᵥ d)) = σ * ε * g - σ * ε * (s ⬝ᵥ d) := by ring
    have h' : ε * (σ * (g - s ⬝ᵥ d)) ≤ ε * (ε * q) := by linarith
    exact le_of_mul_le_mul_left h' hε
  have h1 := half 1 (Or.inl rfl)
  have h2 := half (-1) (Or.inr rfl)
  linarith

lemma fH_etf_dir {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (V : Matrix (Fin m) (Fin m) ℝ)
    {SE : Matrix (Fin n) (Fin n) ℝ} (hSE : SEᵀ = SE) (z : Io m n → ℝ) (j : Fin n) (ε : ℝ) :
    fH D θ V SE (z + ε • Pi.single (Sum.inl (Sum.inr j)) 1) = fH D θ V SE z +
      ε * (-D.cE j - D.gamma * (SE *ᵥ etf (xs z)) j) - ε ^ 2 * (D.gamma / 2 * SE j j) := by
  have ha : active (xs (z + ε • Pi.single (Sum.inl (Sum.inr j)) 1)) = active (xs z) := by
    funext i; simp [xs, active]
  have he : etf (xs (z + ε • Pi.single (Sum.inl (Sum.inr j)) 1)) = etf (xs z) + ε • Pi.single j 1 := by
    funext k; by_cases hk : k = j
    · subst hk; simp [xs, etf]
    · simp [xs, etf, hk]
  have hy : ∀ l, ys (z + ε • Pi.single (Sum.inl (Sum.inr j)) 1) l = ys z l := fun l => by simp [ys]
  have hs := Novel.M5PartialAdjustmentSplitProof.sym_dot hSE (etf (xs z)) (Pi.single j 1)
  have hjj : Pi.single j (1 : ℝ) ⬝ᵥ (SE *ᵥ Pi.single j 1) = SE j j := by
    rw [single_dotProduct, one_mul]; simp [mulVec, dotProduct, Pi.single_apply]
  simp only [fH, ha, he, hy, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [hs, hjj, single_dotProduct, single_dotProduct, one_mul, one_mul]
  ring

lemma fH_y_dir {m n K : ℕ} (D : Data m n K S) (θ : Params m K) (V : Matrix (Fin m) (Fin m) ℝ)
    (SE : Matrix (Fin n) (Fin n) ℝ) (z : Io m n → ℝ) (l : Inst m n) (ε : ℝ) :
    fH D θ V SE (z + ε • Pi.single (Sum.inr l) 1) = fH D θ V SE z + ε * (-1) - ε ^ 2 * 0 := by
  have hx : xs (z + ε • Pi.single (Sum.inr l) 1) = xs z := by funext i; simp [xs]
  have hy : ∑ k, ys (z + ε • Pi.single (Sum.inr l) 1) k = ∑ k, ys z k + ε := by
    simp only [ys, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [fH, hx, hy]
  ring

lemma split_fA {m n K : ℕ} (D : Data m n K S) (η : Lf m n K → ℝ) :
    (∑ c, η c • fA D c) = (∑ c, η (Sum.inl c) • cA D c) +
      ∑ k, (η (Sum.inr (Sum.inl k)) - η (Sum.inr (Sum.inr k))) • eA D k := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_sum_type]
  simp only [fA, Sum.elim_inr, Sum.elim_inl]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_smul, smul_neg]; abel

theorem budgetBound : BudgetBound := by
  intro hAX m K S _ D θ Sf V SE L0 σE hI hR hBE hSf hγ hL0 hL hσ hσE wJ hwJ hmaxJ bs hbs hmaxG x₂ hx₂
    hmaxH hE
  have hr : ∀ l, 0 ≤ D.kplus l ∧ 0 ≤ D.kminus l := hI.2.1
  have hq := hI.2.2.1
  have hsig : sigF D = Sf := hR.1
  have hSE : SEᵀ = SE := by rw [← hR.2.2.1]; exact mom_symm _ _
  have hxl : xs (lift D x₂) = x₂ := rfl
  -- the lifted stage-2 problem and its optimum
  have hfeas2 : ∀ c, fA D c ⬝ᵥ lift D x₂ ≤ fB D bs c := by
    rintro (c | (k | k))
    · exact lift_feas hr hx₂.1 c
    · simp only [fA, fB, Sum.elim_inl, Sum.elim_inr, dot_eA, hxl, hx₂.2, le_refl]
    · simp only [fA, fB, Sum.elim_inr, neg_dotProduct, dot_eA, hxl, hx₂.2, le_refl]
  have hopt : IsMaxOn (fH D θ V SE) {y | ∀ c, fA D c ⬝ᵥ y ≤ fB D bs c} (lift D x₂) := by
    intro y hy
    have hy' : ∀ c, fA D c ⬝ᵥ y ≤ fB D bs c := hy
    obtain ⟨hF, hc⟩ := lift_proj hr fun c => hy' (Sum.inl c)
    have hexp : exposure D (xs y) = bs := by
      funext k
      have h1 := hy' (Sum.inr (Sum.inl k))
      have h2 := hy' (Sum.inr (Sum.inr k))
      simp only [fA, fB, Sum.elim_inr, Sum.elim_inl, neg_dotProduct, dot_eA] at h1 h2
      linarith
    show fH D θ V SE y ≤ fH D θ V SE (lift D x₂)
    have h1 : fH D θ V SE y ≤ fH D θ V SE (lift D (xs y)) := by
      simp only [fH]
      have hs := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hc l
      have e1 : xs (lift D (xs y)) = xs y := rfl
      have e2 : ∀ l, ys (lift D (xs y)) l = costl D (xs y) l := fun l => rfl
      simp only [e1, e2]
      linarith
    rw [fH_lift θ hR] at h1
    rw [fH_lift θ hR]
    exact h1.trans (hmaxH ⟨hF, hexp⟩)
  obtain ⟨η, hη0, hsl, hsup⟩ := (hAX (Io m K) (Lf m K K) (fH D θ V SE) (fA D) (fB D bs)
    (fH_concave θ hR hq hI.2.2.2) (lift D x₂) hfeas2).mp hopt
  set η₂ := η (Sum.inl (Sum.inr (Sum.inr ()))) with hη₂
  set π : Fin K → ℝ := fun k => η (Sum.inr (Sum.inl k)) - η (Sum.inr (Sum.inr k)) with hπ
  have hcs : ∀ c, η c * (fB D bs c - fA D c ⬝ᵥ lift D x₂) = 0 := fun c => by
    rcases (hfeas2 c).lt_or_eq with h | h
    · rw [hsl c h, zero_mul]
    · rw [h, sub_self, mul_zero]
  have hkey : ∀ z, fH D θ V SE z ≤ fH D θ V SE (lift D x₂) + ∑ c, η c * (fA D c ⬝ᵥ z - fB D bs c) := by
    intro z
    have h := hsup z
    have e : (∑ c, η c • fA D c) ⬝ᵥ (z - lift D x₂) = ∑ c, η c * (fA D c ⬝ᵥ z - fB D bs c) := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_dotProduct, smul_eq_mul, dotProduct_sub]
      linarith [hcs c]
    linarith
  -- the rows at a lifted holding in the box
  have hrow : ∀ x : Inst m K → ℝ, (∀ l, 0 ≤ x l ∧ x l ≤ D.wbar l) →
      ∑ c, η c * (fA D c ⬝ᵥ lift D x - fB D bs c) ≤
        -(η₂ * cash D x) + ∑ k, π k * (exposure D x k - bs k) := by
    intro x hx
    have hcl := costl_eq hr x
    have hdec : ∀ T : Lf m K K → ℝ, ∑ c, T c =
        (∑ l, T (Sum.inl (Sum.inl (Sum.inl l))) + ∑ l, T (Sum.inl (Sum.inl (Sum.inr l)))) +
        ((∑ l, T (Sum.inl (Sum.inr (Sum.inl (Sum.inl l)))) + ∑ l, T (Sum.inl (Sum.inr (Sum.inl (Sum.inr l))))) +
          ∑ u, T (Sum.inl (Sum.inr (Sum.inr u)))) +
        (∑ k, T (Sum.inr (Sum.inl k)) + ∑ k, T (Sum.inr (Sum.inr k))) := fun T => by
      simp only [Fintype.sum_sum_type]
    rw [hdec]
    simp only [fA, fB, Sum.elim_inl, Sum.elim_inr, neg_dotProduct, dot_eA]
    have t1 : ∑ l, η (Sum.inl (Sum.inl (Sum.inl l))) *
        (cA D (Sum.inl (Sum.inl l)) ⬝ᵥ lift D x - cB D (Sum.inl (Sum.inl l))) ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hη0 _) (by
        rw [dot_up]; simp only [cB, lift, Sum.elim_inl]; linarith [(hx l).2])
    have t2 : ∑ l, η (Sum.inl (Sum.inl (Sum.inr l))) *
        (cA D (Sum.inl (Sum.inr l)) ⬝ᵥ lift D x - cB D (Sum.inl (Sum.inr l))) ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hη0 _) (by
        rw [dot_lo]; simp only [cB, lift, Sum.elim_inl]; linarith [(hx l).1])
    have t3 : ∑ l, η (Sum.inl (Sum.inr (Sum.inl (Sum.inl l)))) *
        (cA D (Sum.inr (Sum.inl (Sum.inl l))) ⬝ᵥ lift D x - cB D (Sum.inr (Sum.inl (Sum.inl l)))) ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hη0 _) (by
        rw [dot_cp]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hcl l]
        linarith [le_max_left (D.kplus l * (x l - w0 D l)) (D.kminus l * (w0 D l - x l))])
    have t4 : ∑ l, η (Sum.inl (Sum.inr (Sum.inl (Sum.inr l)))) *
        (cA D (Sum.inr (Sum.inl (Sum.inr l))) ⬝ᵥ lift D x - cB D (Sum.inr (Sum.inl (Sum.inr l)))) ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hη0 _) (by
        rw [dot_cm]; simp only [cB, lift, Sum.elim_inl, Sum.elim_inr, hcl l]
        linarith [le_max_right (D.kplus l * (x l - w0 D l)) (D.kminus l * (w0 D l - x l))])
    have t5 : ∑ u : Unit, η (Sum.inl (Sum.inr (Sum.inr u))) *
        (cA D (Sum.inr (Sum.inr u)) ⬝ᵥ lift D x - cB D (Sum.inr (Sum.inr u))) = -(η₂ * cash D x) := by
      rw [Fintype.sum_unique]
      simp only [dot_bud, cB, xs, ys, lift, Sum.elim_inl, Sum.elim_inr, cash, tau_costl,
        Finset.sum_sub_distrib]
      show η₂ * _ = _
      ring
    have t6 : ∑ k, η (Sum.inr (Sum.inl k)) * (exposure D (xs (lift D x)) k - bs k) +
        ∑ k, η (Sum.inr (Sum.inr k)) * (-exposure D (xs (lift D x)) k - -bs k) =
        ∑ k, π k * (exposure D x k - bs k) := by
      have hxs : xs (lift D x) = x := rfl
      simp only [hxs]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hπ]; ring
    linarith
  -- the multiplier's defining property and complementary slackness
  have hlag : ∀ x : Inst m K → ℝ, (∀ l, 0 ≤ x l ∧ x l ≤ D.wbar l) → exposure D x = bs →
      Hr D θ x + η₂ * cash D x ≤ Hr D θ x₂ := by
    intro x hx hb
    have h1 := hkey (lift D x)
    have h2 := hrow x hx
    rw [fH_lift θ hR, fH_lift θ hR] at h1
    simp only [hb, sub_self, mul_zero, Finset.sum_const_zero, add_zero] at h2
    linarith
  have hηk : η₂ * cash D x₂ = 0 := by
    have h := hcs (Sum.inl (Sum.inr (Sum.inr ())))
    have e : fB D bs (Sum.inl (Sum.inr (Sum.inr ()))) - fA D (Sum.inl (Sum.inr (Sum.inr ()))) ⬝ᵥ lift D x₂ =
        cash D x₂ := by
      simp only [fA, fB, Sum.elim_inl]
      rw [dot_bud]
      simp only [cB, xs, ys, lift, Sum.elim_inl, Sum.elim_inr, cash, tau_costl, Finset.sum_sub_distrib]
      ring
    rw [e] at h; exact h
  -- `π` is a supergradient of `V` at `b*`
  have hVbs : Vr D θ bs = Hr D θ x₂ :=
    (show IsGreatest (Hr D θ '' fibre D bs) (Hr D θ x₂) from
      ⟨⟨x₂, hx₂, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmaxH hw⟩).csSup_eq
  have hsuper : ∀ b ∈ BF D, Vr D θ b ≤ Vr D θ bs + π ⬝ᵥ (b - bs) := by
    intro b hb
    obtain ⟨x, hx, -, hVx⟩ := Novel.M2TwoStageSeparationProof.V_attain θ hI hb
    have h1 := hkey (lift D x)
    have h2 := hrow x hx.1.1
    rw [fH_lift θ hR, fH_lift θ hR] at h1
    rw [hVx, hVbs]
    have hc := mul_nonneg (show 0 ≤ η₂ from hη0 _) hx.1.2
    have e : ∑ k, π k * (b k - bs k) = π ⬝ᵥ (b - bs) := by simp [dotProduct]
    simp only [hx.2] at h2
    rw [e] at h2
    linarith
  -- the ETF lines of the stage-2 problem give `B^E π`
  have hsup' : ∀ y, fH D θ V SE y ≤ fH D θ V SE (lift D x₂) + (∑ c, η c • fA D c) ⬝ᵥ (y - lift D x₂) := hsup
  have hline : ∀ j, (D.BE *ᵥ π) j = -D.cE j - D.gamma * (SE *ᵥ etf x₂) j - η₂ -
      (η (Sum.inl (Sum.inr (Sum.inl (Sum.inl (Sum.inr j))))) * D.kplus (Sum.inr j) -
        η (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr j))))) * D.kminus (Sum.inr j)) ∧
      η (Sum.inl (Sum.inr (Sum.inl (Sum.inl (Sum.inr j))))) +
        η (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr j))))) = 1 + η₂ := by
    intro j
    have hjj : 0 ≤ SE j j := by
      rw [← hR.2.2.1]; exact Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (mul_self_nonneg _)
    have hx := deriv_eq (by positivity) (fH_etf_dir D θ V hSE (lift D x₂) j) hsup'
    have hy := deriv_eq le_rfl (fH_y_dir D θ V SE (lift D x₂) (Sum.inr j)) hsup'
    rw [dotProduct_single, mul_one, split_fA, Pi.add_apply, comp_x, Finset.sum_apply] at hx
    rw [dotProduct_single, mul_one, split_fA, Pi.add_apply, comp_y, Finset.sum_apply] at hy
    have hup : η (Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))) = 0 := hsl _ (by
      simp only [fA, fB, Sum.elim_inl]; rw [dot_up]; exact (hE j).2)
    have hlo : η (Sum.inl (Sum.inl (Sum.inr (Sum.inr j)))) = 0 := hsl _ (by
      simp only [fA, fB, Sum.elim_inl]; rw [dot_lo]; simp only [cB, lift, Sum.elim_inl]; linarith [(hE j).1])
    have hsum_x : ∑ k, ((η (Sum.inr (Sum.inl k)) - η (Sum.inr (Sum.inr k))) • eA D k) (Sum.inl (Sum.inr j)) =
        (D.BE *ᵥ π) j := by
      simp [eA, hπ, mulVec, dotProduct, mul_comm]
    have hsum_y : ∑ k, ((η (Sum.inr (Sum.inl k)) - η (Sum.inr (Sum.inr k))) • eA D k) (Sum.inr (Sum.inr j)) = 0 := by
      simp [eA]
    rw [hsum_x, hup, hlo] at hx
    rw [hsum_y] at hy
    simp only [hxl] at hx
    constructor <;> linarith
  refine ⟨η₂, hη0 _, hηk, hlag, ?_⟩
  intro LE
  set C := enorm2 D.cE + D.gamma * σE * enorm2 (fun j => D.wbar (Sum.inr j)) + η₂ * Real.sqrt K +
    (1 + η₂) * enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) with hC
  have hLE : LE = L0 * C := rfl
  have hη₂ : 0 ≤ η₂ := hη0 _
  have hC0 : 0 ≤ C := by
    have := enorm2_nonneg D.cE
    have := mul_nonneg (mul_nonneg hγ.le hσ) (enorm2_nonneg (fun j => D.wbar (Sum.inr j)))
    have := mul_nonneg hη₂ (Real.sqrt_nonneg (K : ℝ))
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + η₂)
      (enorm2_nonneg (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))))
    linarith
  -- `B^E π = -(c^E + γ Σ_E p + η₂ 1 + τ)` with `|τ_j| ≤ (1 + η₂) κ^max_j`
  set τ : Fin K → ℝ := fun j => η (Sum.inl (Sum.inr (Sum.inl (Sum.inl (Sum.inr j))))) * D.kplus (Sum.inr j) -
    η (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr j))))) * D.kminus (Sum.inr j) with hτ
  have hτb : ∀ j, |τ j| ≤ ((1 + η₂) • fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) j := by
    intro j
    obtain ⟨-, hsum⟩ := hline j
    have hp := hη0 (Sum.inl (Sum.inr (Sum.inl (Sum.inl (Sum.inr j)))))
    have hm := hη0 (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr j)))))
    obtain ⟨hk1, hk2⟩ := hr (Sum.inr j)
    have m1 := le_max_left (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))
    have m2 := le_max_right (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))
    simp only [Pi.smul_apply, smul_eq_mul, hτ]
    rw [abs_le]; constructor <;> nlinarith [mul_le_mul_of_nonneg_left m1 hp, mul_le_mul_of_nonneg_left m2 hm,
      mul_nonneg hp hk1, mul_nonneg hm hk2]
  set w := D.BE *ᵥ π with hw
  have hwv : w = -(D.cE + D.gamma • (SE *ᵥ etf x₂) + η₂ • (fun _ => (1 : ℝ)) + τ) := by
    funext j
    have := (hline j).1
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hτ, mul_one]
    rw [hw]; linarith
  have hones : enorm2 (fun _ : Fin K => (1 : ℝ)) = Real.sqrt K := by
    simp [enorm2, dotProduct]
  have hen : enorm2 w ≤ C := by
    rw [hwv, enorm2_neg]
    refine (enorm2_add _ _).trans ?_
    have h1 := enorm2_add (D.cE + D.gamma • (SE *ᵥ etf x₂)) (η₂ • fun _ => (1 : ℝ))
    have h2 := enorm2_add D.cE (D.gamma • (SE *ᵥ etf x₂))
    rw [enorm2_smul, abs_of_pos hγ] at h2
    rw [enorm2_smul, abs_of_nonneg hη₂, hones] at h1
    have h3 := en_SE hσ hσE (etf x₂)
    have h4 : enorm2 (etf x₂) ≤ enorm2 (fun j => D.wbar (Sum.inr j)) :=
      enorm2_mono fun j => by
        show |x₂ (Sum.inr j)| ≤ _
        rw [abs_of_nonneg (hx₂.1.1 (Sum.inr j)).1]; exact (hx₂.1.1 (Sum.inr j)).2
    have h5 : enorm2 τ ≤ (1 + η₂) * enorm2 (fun j => max (D.kplus (Sum.inr j)) (D.kminus (Sum.inr j))) := by
      have := enorm2_mono hτb
      rwa [enorm2_smul, abs_of_nonneg (by linarith)] at this
    rw [hC]
    nlinarith [mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hσ)) hγ.le]
  have hπw : π = D.BE⁻¹ *ᵥ w := by rw [hw, mulVec_mulVec, nonsing_inv_mul _ hBE, one_mulVec]
  have hdual : π ⬝ᵥ (Sf⁻¹ *ᵥ π) ≤ LE ^ 2 := by
    rw [hπw, hLE]
    have h2 : w ⬝ᵥ w ≤ C ^ 2 := by
      rw [← enorm2_sq]; exact pow_le_pow_left₀ (enorm2_nonneg w) hen 2
    calc (D.BE⁻¹ *ᵥ w) ⬝ᵥ (Sf⁻¹ *ᵥ (D.BE⁻¹ *ᵥ w)) ≤ L0 ^ 2 * (w ⬝ᵥ w) := hL w
      _ ≤ L0 ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (L0 * C) ^ 2 := by ring
  -- the value gap through `π`
  have hsym : Sfᵀ = Sf := Novel.M5PartialAdjustmentSplitProof.transpose_of_psd hSf.posSemidef
  have hSfU := Novel.M5PartialAdjustmentSplitProof.pd_unit hSf
  have hSf0 : ∀ y, 0 ≤ y ⬝ᵥ (Sf *ᵥ y) := fun y => by
    have := hSf.posSemidef.dotProduct_mulVec_nonneg y; simpa using this
  have hbJ : exposure D wJ ∈ BF D := ⟨wJ, hwJ, rfl⟩
  have hLE0 : 0 ≤ LE := mul_nonneg hL0 hC0
  have hgap : Vr D θ (exposure D wJ) - Vr D θ bs ≤ LE * Real.sqrt (sqN D (exposure D wJ - bs)) := by
    have h1 := hsuper _ hbJ
    set Δ := exposure D wJ - bs
    have hSS : Sf *ᵥ (Sf⁻¹ *ᵥ π) = π := by rw [mulVec_mulVec, mul_nonsing_inv _ hSfU, one_mulVec]
    have hcs := psd_cs hSf0 hsym (Sf⁻¹ *ᵥ π) Δ
    have e1 : (Sf⁻¹ *ᵥ π) ⬝ᵥ (Sf *ᵥ Δ) = π ⬝ᵥ Δ := by
      rw [← Novel.M5PartialAdjustmentSplitProof.move_left hsym, hSS]
    have e2 : (Sf⁻¹ *ᵥ π) ⬝ᵥ (Sf *ᵥ (Sf⁻¹ *ᵥ π)) = π ⬝ᵥ (Sf⁻¹ *ᵥ π) := by
      rw [hSS, dotProduct_comm]
    rw [e1, e2] at hcs
    have hsq : sqN D Δ = Δ ⬝ᵥ (Sf *ᵥ Δ) := by simp only [sqN, hsig]
    have hΔ0 := hSf0 Δ
    have h3 : (π ⬝ᵥ Δ) ^ 2 ≤ (LE * Real.sqrt (sqN D Δ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by rw [hsq]; exact hΔ0), hsq]
      exact hcs.trans (mul_le_mul_of_nonneg_right hdual hΔ0)
    have h4 := abs_le_of_sq_le_sq' h3 (mul_nonneg hLE0 (Real.sqrt_nonneg _))
    linarith [h4.2]
  refine ⟨⟨π, hsuper, hdual⟩, hgap, ?_⟩
  have h1 := (Novel.M2TwoStageSeparationProof.lossBound θ hI hwJ hmaxJ hbs hmaxG).1
  set x := Real.sqrt (sqN D (exposure D wJ - bs))
  have hQ := Novel.M2TwoStageSeparationProof.sqN_nonneg D hq (exposure D wJ - bs)
  have hx2 : x ^ 2 = sqN D (exposure D wJ - bs) := Real.sq_sqrt hQ
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  rw [← hx2] at h1
  refine le_min ?_ (by nlinarith [mul_nonneg hγ.le (sq_nonneg x)])
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (LE - D.gamma * x)]

end FibreKKT

/-! ### The claim so far -/

theorem proof : Standalone.M7TwoStageExactnessLoss.statement :=
  ⟨jointOptimality, Novel.M2TwoStageSeparationProof.proof, Novel.M2SoftTargetTwoStageProof.proof,
    transfer, represent, spanning, frictions, unreachable, etfFrictionBound, bracket, bindingBudget,
    budgetBound, softMultiplier⟩

end

end Novel.M7TwoStageExactnessLossProof

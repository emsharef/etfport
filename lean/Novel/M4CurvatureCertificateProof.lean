import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Matrix
import Standalone.M4CurvatureCertificate
import Novel.M2ActionClassesProof
import Novel.M4CurvedEntryRateProof

/-!
# Proof of claim 018: curvature controls certification with costs and binding constraints

This proof imports claim 004's proof module and claim 017's (`depends_on: [4, 17]`; Q-04). Claim
017's module brings claim 016's generic lemmas with it.
- Claim 004 supplies the action geometry: `F` and `E` are closed, bounded and convex, the
  incumbent is in `E`, the cost is convex and the risk term is a sum of squares.
- Claim 016 supplies the Moore–Penrose facts for `J J'` and the variance tail bound.
- Claim 017 supplies the hard subfamily and its lower bound.

* **Quadratic gap.** The score is `θ'A w` plus a `θ`-free part. That part is concave with an
  exact `(γ/2) a b (x-y)'Σ(x-y)` defect, so at a maximizer `w` over a convex class,
  `Q(w) - Q(v) ≥ (γ/2)(w-v)'Σ(w-v)` (the `h → 0` argument). Both maxima are therefore unique,
  and `G_* = Ĝ` at every parameter.
* **K.** The ratio is continuous and homogeneous of degree zero, so it attains its maximum on the
  unit sphere.
* **Errors.** With `Ω = J J'`, every `e ∈ A_{N,η}` is `J y` with `‖y‖² ≤ r_N²`. So
  `(e'A d)² ≤ γ u_N d'Σd`.
* **Value bounds.** The ETF value bound holds for any two parameters whose difference obeys that
  inequality. Applied in both directions, it gives the certificate and the power bound.
-/

namespace Novel.M4CurvatureCertificateProof

open Matrix Finset MeasureTheory Standalone.M2ScoreAccounting Standalone.M4CurvatureCertificate
open Standalone.M2ActionClasses (InitialPosition RatesNonneg)
open Standalone.M4InformationObstruction (toPar Theta4 M4Admissible Record record hist mass X
  thetaHat zeta Omega pinv errN TN tcrit Aset Cset etfSup Adv Gstar LN LexLE lexSel wHatF vHatE)
open Standalone.M4JointDirectionalRate (InKJ)
open Novel.M2ActionClassesProof (quad_eq tau_convex comb_sub classesConvex isClosed_F isClosed_E
  F_subset_box continuous_beliefScore dot_comb exposure_comb)
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {n : ℕ} {S : Type} [Fintype S]

/-! ### The score as an affine function of the parameter -/

/-- The parameter-free part of the score. -/
def R0 (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) : ℝ :=
  -(etf w ⬝ᵥ D.cE) - D.gamma / 2 * (w ⬝ᵥ (covariance D *ᵥ w)) - tau D (w - w0 D)

lemma score_split (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) :
    score D w (toPar θ) = θ ⬝ᵥ Aw D w + R0 D w := by
  simp only [score, R0, Aw, toPar, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
    Fin.sum_univ_one, active]
  simp
  ring

lemma score_shift (D : Data 1 n 2 S) (w : Inst 1 n → ℝ) (φ ψ : Fin 3 → ℝ) :
    score D w (toPar φ) = score D w (toPar ψ) - (ψ - φ) ⬝ᵥ Aw D w := by
  rw [score_split, score_split, sub_dotProduct]; ring

lemma Aw_comb (D : Data 1 n 2 S) (x y : Inst 1 n → ℝ) (a b : ℝ) :
    Aw D (a • x + b • y) = a • Aw D x + b • Aw D y := by
  have h := exposure_comb D x y a b
  funext i
  fin_cases i <;> simp [Aw, h]

lemma Aw_sub (D : Data 1 n 2 S) (x y : Inst 1 n → ℝ) : Aw D (x - y) = Aw D x - Aw D y := by
  have h := Aw_comb D x y 1 (-1)
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at h
  exact h

lemma Aw_smul (D : Data 1 n 2 S) (t : ℝ) (z : Inst 1 n → ℝ) : Aw D (t • z) = t • Aw D z := by
  have h := Aw_comb D z 0 t 0
  simpa using h

lemma Aw_zero (D : Data 1 n 2 S) : Aw D 0 = 0 := by
  have h := Aw_smul D 0 0
  simpa using h

/-! ### Strong concavity and the quadratic gap -/

/-- `pS z = z'Σz`. -/
def pS (D : Data 1 n 2 S) (z : Inst 1 n → ℝ) : ℝ := z ⬝ᵥ (covariance D *ᵥ z)

lemma pS_nonneg (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (z : Inst 1 n → ℝ) : 0 ≤ pS D z := by
  rw [pS, quad_eq]; exact sum_nonneg fun s _ => mul_nonneg (hq s) (sq_nonneg _)

lemma quad_comb (D : Data 1 n 2 S) {a b : ℝ} (hab : a + b = 1) (x y : Inst 1 n → ℝ) :
    pS D (a • x + b • y) = a * pS D x + b * pS D y - a * b * pS D (x - y) := by
  simp only [pS, quad_eq, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [dot_comb, sub_dotProduct]
  have hb : b = 1 - a := by linarith
  subst hb; ring

lemma score_strong (D : Data 1 n 2 S) (hr : RatesNonneg D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (x y : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) :
    a * score D x (toPar θ) + b * score D y (toPar θ) + D.gamma / 2 * (a * b * pS D (x - y))
      ≤ score D (a • x + b • y) (toPar θ) := by
  have ht := tau_convex D hr ha hb (x - w0 D) (y - w0 D)
  rw [← comb_sub x y (w0 D) hab] at ht
  have hq := quad_comb D hab x y
  have hetf : etf (a • x + b • y) = a • etf x + b • etf y := rfl
  simp only [pS] at hq
  simp only [score_split, R0, Aw_comb, dotProduct_add, dotProduct_smul, smul_eq_mul, hetf,
    dot_comb, hq, pS]
  nlinarith [ht]

/-- The quadratic gap at a maximizer over a convex set, without differentiability. -/
lemma qgap (D : Data 1 n 2 S) (hr : RatesNonneg D) (hq : ∀ s, 0 ≤ D.q s) (hg : 0 ≤ D.gamma)
    {C : Set (Inst 1 n → ℝ)} (hC : Convex ℝ C) {θ : Fin 3 → ℝ} {w v : Inst 1 n → ℝ}
    (hw : w ∈ maximizers (fun u => score D u (toPar θ)) C) (hv : v ∈ C) :
    D.gamma / 2 * pS D (w - v) ≤ score D w (toPar θ) - score D v (toPar θ) := by
  set c := D.gamma / 2 * pS D (w - v) with hc
  set g := score D w (toPar θ) - score D v (toPar θ) with hgdef
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) (pS_nonneg D hq _)
  have key : ∀ h : ℝ, 0 < h → h < 1 → c * (1 - h) ≤ g := by
    intro h h0 h1
    have hm := hw.2 ((1 - h) • w + h • v) (hC hw.1 hv (by linarith) h0.le (by ring))
    have hs := score_strong D hr (by linarith : (0 : ℝ) ≤ 1 - h) h0.le (by ring) w v θ
    have : h * (c * (1 - h)) ≤ h * g := by
      simp only [hc, hgdef]; nlinarith
    exact le_of_mul_le_mul_left this h0
  by_contra hlt
  rw [not_le] at hlt
  have h2 := key (1 / 2) (by norm_num) (by norm_num)
  have hcpos : 0 < c := by linarith
  have hh0 : 0 < (c - g) / (2 * c) := div_pos (by linarith) (by linarith)
  have hh1 : (c - g) / (2 * c) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := key _ hh0 hh1
  have e : c * (1 - (c - g) / (2 * c)) = (c + g) / 2 := by field_simp; ring
  linarith

/-! ### The setting's inputs, existence and uniqueness -/

lemma inputs {D : Data 1 n 2 S} {V : Finset (Fin 3 → ℝ)} (h : M4Admissible D V) :
    InitialPosition D ∧ RatesNonneg D ∧ (∀ s, 0 ≤ D.q s) ∧ 0 ≤ D.gamma ∧ w0 D ∈ F D := by
  obtain ⟨-, -, hq, -, -, -, -, hg, hx, hh, hW, hw0, hrate, -⟩ := h
  exact ⟨⟨hW, hx, hh, fun i => (hw0.1 i).2⟩, fun i => ⟨(hrate i).1, (hrate i).2.2.1⟩, hq, hg, hw0⟩

lemma cont_score (D : Data 1 n 2 S) (θ : Params 1 2) : Continuous fun w => score D w θ := by
  have e : beliefScore D (T := Unit) (fun _ => θ) (fun _ => 1) = fun w => score D w θ := by
    funext w; simp [beliefScore]
  rw [← e]; exact continuous_beliefScore D _ _

lemma E_sub_F (D : Data 1 n 2 S) : E D ⊆ F D := fun _ hw => hw.1

lemma compact_F (D : Data 1 n 2 S) : IsCompact (F D) :=
  isCompact_Icc.of_isClosed_subset (isClosed_F D) (F_subset_box D)

lemma compact_E (D : Data 1 n 2 S) : IsCompact (E D) :=
  (compact_F D).of_isClosed_subset (isClosed_E D) (E_sub_F D)

lemma w0_mem_E {D : Data 1 n 2 S} (h : w0 D ∈ F D) : w0 D ∈ E D := ⟨h, rfl⟩

lemma lexSel_single (x : Inst 1 n → ℝ) : lexSel ({x} : Set (Inst 1 n → ℝ)) = x := by
  have h : ∃ w, w ∈ ({x} : Set (Inst 1 n → ℝ)) ∧ ∀ v ∈ ({x} : Set (Inst 1 n → ℝ)), LexLE w v :=
    ⟨x, rfl, fun v hv => Or.inl hv.symm⟩
  exact (Classical.epsilon_spec h).1

section Setting

variable {D : Data 1 n 2 S} {V : Finset (Fin 3 → ℝ)} {J : Matrix (Fin 3) (Fin 3) ℝ}
  {U : S → Fin 3 → ℝ}

lemma pd_zero (hs : CurvSetting D V J U) {z : Inst 1 n → ℝ} (h : pS D z ≤ 0) : z = 0 := by
  by_contra hz
  exact absurd (hs.2.2.1 z hz) (not_lt.mpr h)

lemma max_unique (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) {C : Set (Inst 1 n → ℝ)}
    (hC : Convex ℝ C) (hK : IsCompact C) (hne : C.Nonempty) :
    ∃ w, maximizers (fun u => score D u (toPar θ)) C = {w} := by
  obtain ⟨-, hr, hq, hg, -⟩ := inputs hs.1
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hne (cont_score D _).continuousOn
  have hwm : w ∈ maximizers (fun u => score D u (toPar θ)) C := ⟨hw, fun w' hw' => hmax hw'⟩
  refine ⟨w, Set.ext fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · have hgap := qgap D hr hq hg hC hwm hu.1
    have hle := hu.2 w hw
    have hγ := hs.2.1
    have : pS D (w - u) ≤ 0 := by
      by_contra h
      rw [not_le] at h
      have : 0 < D.gamma / 2 * pS D (w - u) := mul_pos (by linarith) h
      linarith
    exact (sub_eq_zero.mp (pd_zero hs this)).symm
  · rw [Set.mem_singleton_iff.mp hu]; exact hwm

lemma maxF (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    maximizers (fun w => score D w (toPar θ)) (F D) = {wHatF D θ} := by
  obtain ⟨-, hr, -, -, hw0⟩ := inputs hs.1
  obtain ⟨w, hw⟩ := max_unique hs θ (classesConvex D hr).1 (compact_F D) ⟨_, hw0⟩
  rw [wHatF, hw, lexSel_single]

lemma maxE (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    maximizers (fun w => score D w (toPar θ)) (E D) = {vHatE D θ} := by
  obtain ⟨-, hr, -, -, hw0⟩ := inputs hs.1
  obtain ⟨w, hw⟩ := max_unique hs θ (classesConvex D hr).2.1 (compact_E D) ⟨_, w0_mem_E hw0⟩
  rw [vHatE, hw, lexSel_single]

lemma wHatF_mem (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    wHatF D θ ∈ maximizers (fun w => score D w (toPar θ)) (F D) := by
  rw [maxF hs θ]; rfl

lemma vHatE_mem (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    vHatE D θ ∈ maximizers (fun w => score D w (toPar θ)) (E D) := by
  rw [maxE hs θ]; rfl

lemma etfSup_eq (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    etfSup D θ = score D (vHatE D θ) (toPar θ) := by
  have hm := vHatE_mem hs θ
  refine IsGreatest.csSup_eq ⟨⟨_, hm.1, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hm.2 w hw

lemma Gstar_eq (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) : Gstar D θ = Ghat D θ := by
  have hm := wHatF_mem hs θ
  have hF : sSup ((fun w => score D w (toPar θ)) '' F D) = score D (wHatF D θ) (toPar θ) := by
    refine IsGreatest.csSup_eq ⟨⟨_, hm.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hm.2 w hw
  rw [Gstar, hF, etfSup_eq hs, Ghat]

lemma Ghat_nonneg (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) : 0 ≤ Ghat D θ := by
  have := (wHatF_mem hs θ).2 _ (E_sub_F D (vHatE_mem hs θ).1)
  rw [Ghat]; linarith

/-- The quadratic gap between the two plug-in optima: `γ d'Σd ≤ 2 Ĝ`. -/
lemma gap_F (hs : CurvSetting D V J U) (θ : Fin 3 → ℝ) :
    D.gamma / 2 * pS D (wHatF D θ - vHatE D θ) ≤ Ghat D θ := by
  obtain ⟨-, hr, hq, hg, -⟩ := inputs hs.1
  exact qgap D hr hq hg (classesConvex D hr).1 (wHatF_mem hs θ) (E_sub_F D (vHatE_mem hs θ).1)

end Setting

/-! ### The curvature ratio `K` -/

/-- `gJ z = ‖J'Az‖²`. -/
def gJ (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) (z : Inst 1 n → ℝ) : ℝ :=
  (Jᵀ *ᵥ Aw D z) ⬝ᵥ (Jᵀ *ᵥ Aw D z)

lemma Kc_eq (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    Kc D J = (1 / D.gamma) * sSup {r | ∃ z : Inst 1 n → ℝ, z ≠ 0 ∧ r = gJ D J z / pS D z} := rfl

lemma gJ_nonneg (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) (z : Inst 1 n → ℝ) :
    0 ≤ gJ D J z := Novel.M4JointDirectionalRateProof.dot_self_nonneg _

lemma gJ_smul (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (z : Inst 1 n → ℝ) :
    gJ D J (t • z) = t ^ 2 * gJ D J z := by
  simp only [gJ, Aw_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma pS_smul (D : Data 1 n 2 S) (t : ℝ) (z : Inst 1 n → ℝ) : pS D (t • z) = t ^ 2 * pS D z := by
  simp only [pS, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma gJ_zero (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) : gJ D J 0 = 0 := by
  simp [gJ, Aw_zero]

lemma pS_zero (D : Data 1 n 2 S) : pS D 0 = 0 := by simp [pS]

lemma cont_Aw (D : Data 1 n 2 S) : Continuous (Aw D) := by
  have he : Continuous (exposure D) := by unfold exposure active etf; fun_prop
  refine continuous_pi fun i => ?_
  fin_cases i
  · have := (continuous_apply (0 : Fin 2)).comp he
    simpa [Aw, Function.comp_def] using this
  · have := (continuous_apply (1 : Fin 2)).comp he
    simpa [Aw, Function.comp_def] using this
  · simpa [Aw] using continuous_apply (Sum.inl 0)

lemma cont_gJ (D : Data 1 n 2 S) (J : Matrix (Fin 3) (Fin 3) ℝ) : Continuous (gJ D J) := by
  have h : Continuous fun z => Jᵀ *ᵥ Aw D z := continuous_const.matrix_mulVec (cont_Aw D)
  exact h.dotProduct h

lemma cont_pS (D : Data 1 n 2 S) : Continuous (pS D) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

section Setting

variable {D : Data 1 n 2 S} {V : Finset (Fin 3 → ℝ)} {J : Matrix (Fin 3) (Fin 3) ℝ}
  {U : S → Fin 3 → ℝ}

/-- `K` is finite and nonnegative, bounds every direction, and is attained on `z'Σz = 1`. -/
lemma K_facts (hs : CurvSetting D V J U) :
    0 ≤ Kc D J ∧ (∀ z, gJ D J z ≤ D.gamma * Kc D J * pS D z) ∧
      ∃ z, pS D z = 1 ∧ gJ D J z = D.gamma * Kc D J := by
  have hγ := hs.2.1
  have hpd := hs.2.2.1
  have hsph : ∀ z ∈ Metric.sphere (0 : Inst 1 n → ℝ) 1, z ≠ 0 := fun z hz h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hz; norm_num at hz
  have hne : (Metric.sphere (0 : Inst 1 n → ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : ContinuousOn (fun z => gJ D J z / pS D z) (Metric.sphere (0 : Inst 1 n → ℝ) 1) :=
    (cont_gJ D J).continuousOn.div (cont_pS D).continuousOn fun z hz => (hpd z (hsph z hz)).ne'
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : Inst 1 n → ℝ) 1).exists_isMaxOn hne hcont
  set M := gJ D J u / pS D u with hM
  have hpu : 0 < pS D u := hpd u (hsph u hu)
  have hf : ∀ z, z ≠ 0 → gJ D J z / pS D z ≤ M := by
    intro z hz
    set t := ‖z‖ with ht
    have ht0 : 0 < t := norm_pos_iff.mpr hz
    have hu' : t⁻¹ • z ∈ Metric.sphere (0 : Inst 1 n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0, ← ht,
        inv_mul_cancel₀ ht0.ne']
    have hz' : z = t • (t⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    have := hmax hu'
    simp only [Set.mem_ofPred_eq] at this
    rw [hz', gJ_smul, pS_smul, mul_div_mul_left _ _ (by positivity)]
    exact this
  have hsup : sSup {r | ∃ z : Inst 1 n → ℝ, z ≠ 0 ∧ r = gJ D J z / pS D z} = M :=
    IsGreatest.csSup_eq ⟨⟨u, hsph u hu, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hf z hz⟩
  have hK : Kc D J = M / D.gamma := by rw [Kc_eq, hsup]; ring
  have hM0 : 0 ≤ M := div_nonneg (gJ_nonneg D J u) hpu.le
  have hγK : D.gamma * Kc D J = M := by rw [hK, mul_div_cancel₀ _ hγ.ne']
  refine ⟨by rw [hK]; positivity, fun z => ?_, ?_⟩
  · rw [hγK]
    by_cases hz : z = 0
    · simp [hz, gJ_zero, pS_zero]
    · have hp : 0 < pS D z := hpd z hz
      have := hf z hz
      rwa [div_le_iff₀ hp] at this
  · refine ⟨(Real.sqrt (pS D u))⁻¹ • u, ?_, ?_⟩
    · rw [pS_smul, inv_pow, Real.sq_sqrt hpu.le, inv_mul_cancel₀ hpu.ne']
    · rw [gJ_smul, inv_pow, Real.sq_sqrt hpu.le, hγK, hM]; ring

lemma uN_nonneg (hs : CurvSetting D V J U) (N : ℕ) (η : ℝ) : 0 ≤ uN D J N η :=
  mul_nonneg (K_facts hs).1 (sq_nonneg _)

/-! ### Mean errors -/

lemma omega_gen (hs : CurvSetting D V J U) : Omega D = J * Jᵀ := by
  obtain ⟨-, -, -, hK, hz⟩ := hs
  ext i k
  simp only [Omega, hz, Novel.M4JointDirectionalRateProof.mulVec_row]
  rw [Novel.M4JointDirectionalRateProof.second_dot hK]
  simp [Matrix.mul_apply, dotProduct]

/-- Every error in `A_{N,η}` satisfies `(e'A d)² ≤ γ u_N d'Σd`. -/
lemma err_bound (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) {η : ℝ} {e : Fin 3 → ℝ}
    (he : e ∈ Aset D N η) (d : Inst 1 n → ℝ) :
    (e ⬝ᵥ Aw D d) ^ 2 ≤ D.gamma * uN D J N η * pS D d := by
  obtain ⟨⟨x, rfl⟩, hq⟩ := he
  rw [omega_gen hs] at hq ⊢
  rw [Novel.M4JointDirectionalRateProof.quad_omega J x] at hq
  set y := Jᵀ *ᵥ x with hydef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hy : y ⬝ᵥ y ≤ rN D N η ^ 2 := by
    have h0 := Novel.M4JointDirectionalRateProof.dot_self_nonneg y
    have h1 : y ⬝ᵥ y ≤ tcrit D N η / N := by rw [le_div_iff₀ hNr]; linarith
    rw [rN, Real.sq_sqrt (h0.trans h1)]; exact h1
  have e1 : ((J * Jᵀ) *ᵥ x) ⬝ᵥ Aw D d = y ⬝ᵥ (Jᵀ *ᵥ Aw D d) := by
    rw [← Matrix.mulVec_mulVec, Novel.M4JointDirectionalRateProof.dot_mulVec, hydef]
  rw [e1]
  have hg := (K_facts hs).2.1 d
  have hc := Novel.M4JointDirectionalRateProof.cs3 y (Jᵀ *ᵥ Aw D d)
  calc (y ⬝ᵥ (Jᵀ *ᵥ Aw D d)) ^ 2 ≤ (y ⬝ᵥ y) * gJ D J d := hc
    _ ≤ rN D N η ^ 2 * gJ D J d := mul_le_mul_of_nonneg_right hy (gJ_nonneg D J d)
    _ ≤ rN D N η ^ 2 * (D.gamma * Kc D J * pS D d) := mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    _ = D.gamma * uN D J N η * pS D d := by rw [uN]; ring

end Setting

/-- The latent sample mean `Ū`. -/
def Ub {N : ℕ} (U : S → Fin 3 → ℝ) (σ : Fin N → S) : Fin 3 → ℝ := (1 / (N : ℝ)) • ∑ l, U (σ l)

lemma errN_J {D : Data 1 n 2 S} {J : Matrix (Fin 3) (Fin 3) ℝ} {U : S → Fin 3 → ℝ}
    (hz : ∀ s, zeta D s = J *ᵥ U s) {N : ℕ} (σ : Fin N → S) : errN D σ = J *ᵥ Ub U σ := by
  simp only [errN, Ub, hz, mulVec_smul, mulVec_sum]

lemma X_rec (D : Data 1 n 2 S) (θ : Fin 3 → ℝ) (s : S) : X D (record D θ s) = θ + zeta D s := by
  funext i
  fin_cases i <;> simp [X, record, zeta, ret, toPar, mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.vecHead, Matrix.vecTail]
  ring

lemma thetaHat_hist (D : Data 1 n 2 S) {N : ℕ} (hN : 0 < N) (θ : Fin 3 → ℝ) (σ : Fin N → S) :
    thetaHat D (hist D θ σ) = θ + errN D σ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext i
  simp only [thetaHat, hist, X_rec, errN, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  field_simp

/-! ### M4's discrete quantile for any number of ETFs -/

section Quantile

variable (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (hq1 : ∑ s, D.q s = 1)
include hq hq1

lemma mass_nonneg {N : ℕ} (σ : Fin N → S) : 0 ≤ mass D σ := Finset.prod_nonneg fun _ _ => hq _

omit hq in
lemma mass_sum (N : ℕ) : ∑ σ : Fin N → S, mass D σ = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum (fun _ : Fin N => fun s => D.q s)]
  simp [hq1]

lemma tq_mem (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ tcrit D N ε then mass D σ else 0 := by
  set T := {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
    1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} with hT
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := mass_sum D hq1 N
  have hmass := mass_nonneg D hq hq1 (N := N)
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 := by
    by_contra h
    have : ∑ σ : Fin N → S, mass D σ ≤ 0 :=
      Finset.sum_nonpos fun σ _ => not_lt.mp fun hp => h ⟨σ, hp⟩
    linarith
  have hfin : T.Finite := (Set.finite_range (TN D)).subset fun t ht => by
    obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ) (TN D) ⟨σ0, by simp [hσ0]⟩
  have hne : T.Nonempty := by
    refine ⟨TN D σm, ⟨σm, (Finset.mem_filter.mp hσm).2, rfl⟩, ?_⟩
    have e : ∑ σ : Fin N → S, (if TN D σ ≤ TN D σm then mass D σ else 0) = 1 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rcases (hmass σ).lt_or_eq with h | h
      · have := hmax σ (by simp [h])
        split_ifs with hc
        · rfl
        · exact absurd this hc
      · rw [← h]; split_ifs <;> rfl
    linarith
  exact (hne.csInf_mem hfin).2

lemma tq_le (N : ℕ) {ε : ℝ} (hε1 : ε < 1) (Pσ : (Fin N → S) → Prop) [DecidablePred Pσ] (T0 : ℝ)
    (hP : 1 - ε ≤ ∑ σ : Fin N → S, if Pσ σ then mass D σ else 0)
    (hPT : ∀ σ, Pσ σ → TN D σ ≤ T0) : tcrit D N ε ≤ T0 := by
  have hmass := mass_nonneg D hq hq1 (N := N)
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : Fin N → S, 0 < mass D σ0 ∧ Pσ σ0 := by
    by_contra h
    have : ∑ σ : Fin N → S, (if Pσ σ then mass D σ else 0) ≤ 0 :=
      Finset.sum_nonpos fun σ _ => by
        split_ifs with h'
        · exact not_lt.mp fun hp => h ⟨σ, hp, h'⟩
        · exact le_rfl
    linarith
  obtain ⟨σm, hσm, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : Fin N → S => 0 < mass D σ ∧ Pσ σ) (TN D) ⟨σ0, by simp [hσ0]⟩
  have hσm' := (Finset.mem_filter.mp hσm).2
  have hmemT : TN D σm ∈ {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} := by
    refine ⟨⟨σm, hσm'.1, rfl⟩, le_trans hP (Finset.sum_le_sum fun σ _ => ?_)⟩
    by_cases h : Pσ σ
    · rcases (hmass σ).lt_or_eq with hp | hp
      · have := hmax σ (by simp [hp, h])
        simp only [h, this, ↓reduceIte, le_refl]
      · rw [← hp]; split_ifs <;> exact le_rfl
    · simp only [h, ↓reduceIte]; split_ifs <;> linarith [hmass σ]
  have hbdd : BddBelow {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - ε ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0} :=
    ((Set.finite_range (TN D)).subset fun t ht => by
      obtain ⟨⟨σ, -, rfl⟩, -⟩ := ht; exact ⟨σ, rfl⟩).bddBelow
  exact (csInf_le hbdd hmemT).trans (hPT σm hσm'.2)

end Quantile

section Setting

variable {D : Data 1 n 2 S} {V : Finset (Fin 3 → ℝ)} {J : Matrix (Fin 3) (Fin 3) ℝ}
  {U : S → Fin 3 → ℝ}

/-- On `T_N ≤ t_{N,η}` the truth is in `C_N`. -/
lemma cover (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) (η : ℝ) {θ : Fin 3 → ℝ}
    (hθ : θ ∈ Theta4 V) (σ : Fin N → S) (hT : TN D σ ≤ tcrit D N η) :
    θ ∈ Cset D V N η (thetaHat D (hist D θ σ)) := by
  refine ⟨hθ, errN D σ, ⟨?_, hT⟩, ?_⟩
  · obtain ⟨x, hx, -⟩ := Novel.M4JointDirectionalRateProof.J_range J (Ub U σ)
    exact ⟨x, by rw [omega_gen hs, errN_J hs.2.2.2.2, hx]⟩
  · rw [thetaHat_hist D hN]; abel

/-- `t_{N,ε} ≤ 12 log(6/ε)` once `N ≥ 81 log(6/ε)`. -/
lemma tcrit_12 (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hNb : 81 * Real.log (6 / ε) ≤ N) :
    tcrit D N ε ≤ 12 * Real.log (6 / ε) := by
  have hΩ : Omega D = J * Jᵀ := omega_gen hs
  obtain ⟨-, -, -, hK, hz⟩ := hs
  obtain ⟨hq, hq1, hU0, hU2, hU⟩ := id hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Real.log (6 / ε) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  set a := 2 * Real.sqrt (L / N) with hadef
  have ha : 0 < a := by positivity
  have ha2 : a ^ 2 = 4 * L / N := by
    rw [hadef, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have ha29 : a ≤ 2 / 9 := by
    have : a ^ 2 ≤ (2 / 9) ^ 2 := by
      rw [ha2, div_le_iff₀ hNr]; nlinarith
    exact (pow_le_pow_iff_left₀ ha.le (by norm_num) two_ne_zero).mp this
  have hmass : ∀ σ : Fin N → S, 0 ≤ mass D σ := fun σ => Finset.prod_nonneg fun _ _ => hq _
  have hsum : ∑ σ : Fin N → S, mass D σ = 1 := mass_sum D hq1 N
  have hUb : ∀ (σ : Fin N → S) c, Ub U σ c = (1 / (N : ℝ)) * ∑ l, U (σ l) c := fun σ c => by
    simp [Ub, Finset.sum_apply]
  have htail : ∀ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ub U σ c| then mass D σ else 0) ≤ ε / 3 := by
    intro c
    have h := Novel.M4JointDirectionalRateProof.tailV (Y := fun s => U s c) hq hq1 (hU0 c)
      (by simpa [sq] using hU2 c c)
      (fun s => (Novel.M4JointDirectionalRateProof.coord_sq_le (U s) c).trans (hU s)) hN ha ha29
    have e : 2 * Real.exp (-(N * a ^ 2) / 4) = ε / 3 := by
      rw [ha2]
      have : -((N : ℝ) * (4 * L / N)) / 4 = -L := by field_simp
      rw [this, Real.exp_neg, hLdef, Real.exp_log (by positivity)]
      field_simp
      norm_num
    rw [← e]
    simp only [hUb]
    exact h
  have hP : 1 - ε ≤ ∑ σ : Fin N → S, (if ∀ c, |Ub U σ c| < a then mass D σ else 0) := by
    have hle : ∀ σ : Fin N → S, mass D σ - (if ∀ c, |Ub U σ c| < a then mass D σ else 0)
        ≤ ∑ c : Fin 3, (if a ≤ |Ub U σ c| then mass D σ else 0) := by
      intro σ
      split_ifs with h
      · rw [sub_self]
        exact Finset.sum_nonneg fun c _ => by split_ifs <;> linarith [hmass σ]
      · rw [sub_zero]
        obtain ⟨c, hc⟩ := not_forall.mp h
        have hc' : a ≤ |Ub U σ c| := not_lt.mp hc
        calc mass D σ = (if a ≤ |Ub U σ c| then mass D σ else 0) := by simp [hc']
          _ ≤ _ := Finset.single_le_sum (f := fun c => if a ≤ |Ub U σ c| then mass D σ else 0)
              (fun c _ => by split_ifs <;> linarith [hmass σ]) (Finset.mem_univ c)
    have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hle σ
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_comm] at this
    have h3 : ∑ c : Fin 3, ∑ σ : Fin N → S, (if a ≤ |Ub U σ c| then mass D σ else 0) ≤ ε := by
      calc _ ≤ ∑ _c : Fin 3, ε / 3 := Finset.sum_le_sum fun c _ => htail c
        _ = ε := by simp; ring
    linarith
  refine tq_le D hq hq1 N hε1 _ _ hP fun σ hσ => ?_
  obtain ⟨x, hx, hxb⟩ := Novel.M4JointDirectionalRateProof.J_range J (Ub U σ)
  have hTN : TN D σ = N * ((J * Jᵀ) *ᵥ x ⬝ᵥ (pinv (J * Jᵀ) *ᵥ ((J * Jᵀ) *ᵥ x))) := by
    rw [TN, errN_J hz, hx, hΩ]
  rw [hTN, Novel.M4JointDirectionalRateProof.quad_omega]
  have hUb3 : Ub U σ ⬝ᵥ Ub U σ ≤ 3 * a ^ 2 := by
    rw [Novel.M4JointDirectionalRateProof.dot3]
    have := fun c => (sq_lt_sq' (abs_lt.mp (hσ c)).1 (abs_lt.mp (hσ c)).2).le
    nlinarith [this 0, this 1, this 2]
  calc (N : ℝ) * ((Jᵀ *ᵥ x) ⬝ᵥ (Jᵀ *ᵥ x)) ≤ N * (3 * a ^ 2) :=
        mul_le_mul_of_nonneg_left (hxb.trans hUb3) hNr.le
    _ = 12 * L := by rw [ha2]; field_simp; ring

/-! ### The ETF value bound and the certificate -/

lemma amgm_le {Z a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Z ^ 2 ≤ a * b) : Z ≤ (a + b) / 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (Z - (a + b) / 2)]

/-- The ETF value bound: if `e = ψ - φ` obeys `(e'A d)² ≤ γ u d'Σd`, then
`sup_E Q(·; φ) ≤ Q(v̂_E(ψ); ψ) - e'A v̂_E(ψ) + u/2`. The whole class `E` is compared. -/
lemma vbound (hs : CurvSetting D V J U) {φ ψ : Fin 3 → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hE : ∀ d, ((ψ - φ) ⬝ᵥ Aw D d) ^ 2 ≤ D.gamma * u * pS D d) :
    score D (vHatE D φ) (toPar φ)
      ≤ score D (vHatE D ψ) (toPar ψ) - (ψ - φ) ⬝ᵥ Aw D (vHatE D ψ) + u / 2 := by
  obtain ⟨-, hr, hq, hg, -⟩ := inputs hs.1
  have hv : vHatE D φ ∈ E D := (vHatE_mem hs φ).1
  have hgap := qgap D hr hq hg (classesConvex D hr).2.1 (vHatE_mem hs ψ) hv
  have hZ := hE (vHatE D ψ - vHatE D φ)
  rw [Aw_sub, dotProduct_sub] at hZ
  have hP := pS_nonneg D hq (vHatE D ψ - vHatE D φ)
  have key := amgm_le (mul_nonneg hg hP) hu (by linarith [hZ] :
    ((ψ - φ) ⬝ᵥ Aw D (vHatE D ψ) - (ψ - φ) ⬝ᵥ Aw D (vHatE D φ)) ^ 2
      ≤ (D.gamma * pS D (vHatE D ψ - vHatE D φ)) * u)
  rw [score_shift D (vHatE D φ) φ ψ]
  linarith

/-- The certificate inequality in both directions:
`Q(ŵ_F(ψ); φ) - sup_E Q(·; φ) ≥ Ĝ(ψ) - √(2 u Ĝ(ψ)) - u/2`. -/
lemma gbound (hs : CurvSetting D V J U) {φ ψ : Fin 3 → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hE : ∀ d, ((ψ - φ) ⬝ᵥ Aw D d) ^ 2 ≤ D.gamma * u * pS D d) :
    Ghat D ψ - Real.sqrt (2 * u * Ghat D ψ) - u / 2
      ≤ score D (wHatF D ψ) (toPar φ) - score D (vHatE D φ) (toPar φ) := by
  have hv := vbound hs hu hE
  have hgap := gap_F hs ψ
  have hZ := hE (wHatF D ψ - vHatE D ψ)
  rw [Aw_sub, dotProduct_sub] at hZ
  have hZ2 : ((ψ - φ) ⬝ᵥ Aw D (wHatF D ψ) - (ψ - φ) ⬝ᵥ Aw D (vHatE D ψ)) ^ 2
      ≤ 2 * u * Ghat D ψ := by
    linarith [mul_le_mul_of_nonneg_left hgap hu]
  have hs2 := (abs_le.mp (Real.abs_le_sqrt hZ2)).2
  have hG : Ghat D ψ = score D (wHatF D ψ) (toPar ψ) - score D (vHatE D ψ) (toPar ψ) := rfl
  rw [score_shift D (wHatF D ψ) φ ψ]
  linarith

/-- `ℓ_N ≤ Adv(ŵ_F; θ)` at every `θ ∈ C_N`. -/
lemma ell_le_Adv (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) {η : ℝ} {th θ : Fin 3 → ℝ}
    (hθ : θ ∈ Cset D V N η th) : ellG D J N η th ≤ Adv D (wHatF D th) θ := by
  obtain ⟨-, e, he, rfl⟩ := hθ
  have hE : ∀ d, ((th - (th - e)) ⬝ᵥ Aw D d) ^ 2 ≤ D.gamma * uN D J N η * pS D d := by
    intro d; rw [sub_sub_cancel]; exact err_bound hs hN he d
  have := gbound hs (uN_nonneg hs N η) hE
  rw [Adv, etfSup_eq hs, ellG]
  linarith

lemma flb {u g : ℝ} (hu : 0 ≤ u) (hg : 96 * u ≤ g) :
    4 / 5 * g ≤ g - Real.sqrt (2 * u * g) - u / 2 := by
  have hg0 : 0 ≤ g := by linarith
  have hs : Real.sqrt (2 * u * g) ≤ g / 6 := by
    rw [show g / 6 = Real.sqrt ((g / 6) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- Power on coverage: with the roles of the estimate and the truth reversed. -/
lemma power_cov (hs : CurvSetting D V J U) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) {η : ℝ}
    (hu : uN D J N η ≤ δ / 128) {th θ : Fin 3 → ℝ} (hθ : θ ∈ Cset D V N η th)
    (hG : δ ≤ Gstar D θ) : δ / 2 < ellG D J N η th := by
  obtain ⟨-, e, he, hθe⟩ := hθ
  have hE : ∀ d, ((θ - th) ⬝ᵥ Aw D d) ^ 2 ≤ D.gamma * uN D J N η * pS D d := by
    intro d
    have : θ - th = -e := by rw [hθe]; abel
    rw [this, neg_dotProduct, neg_sq]; exact err_bound hs hN he d
  have hu0 := uN_nonneg hs N η
  have h1 := gbound hs hu0 hE
  have h2 : score D (wHatF D θ) (toPar th) ≤ score D (wHatF D th) (toPar th) :=
    (wHatF_mem hs th).2 _ (wHatF_mem hs θ).1
  rw [Gstar_eq hs] at hG
  have h3 := flb hu0 (by linarith : 96 * uN D J N η ≤ Ghat D θ)
  have hGt : Ghat D th = score D (wHatF D th) (toPar th) - score D (vHatE D th) (toPar th) := rfl
  have h4 : 4 / 5 * δ ≤ Ghat D th := by linarith
  have h5 := flb hu0 (by linarith : 96 * uN D J N η ≤ Ghat D th)
  rw [ellG]; linarith

/-- `ℓ_N > δ_econ ≥ 0` forces an active change. -/
lemma active_change (hs : CurvSetting D V J U) {N : ℕ} {η δe : ℝ} {th : Fin 3 → ℝ}
    (hδ : 0 ≤ δe) (h : δe < ellG D J N η th) : wHatF D th (Sum.inl 0) ≠ w0 D (Sum.inl 0) := by
  intro heq
  have hmem : wHatF D th ∈ E D := ⟨(wHatF_mem hs th).1, by
    funext j; fin_cases j; exact heq⟩
  have hle : score D (wHatF D th) (toPar th) ≤ score D (vHatE D th) (toPar th) :=
    (vHatE_mem hs th).2 _ hmem
  have hu := uN_nonneg hs N η
  have hsq := Real.sqrt_nonneg (2 * uN D J N η * Ghat D th)
  have hG : Ghat D th = score D (wHatF D th) (toPar th) - score D (vHatE D th) (toPar th) := rfl
  rw [ellG] at h
  linarith

/-! ### The gate's requirements -/

lemma dirac_toReal (w : Inst 1 n → ℝ) (T : Set (Inst 1 n → ℝ)) :
    (Measure.dirac w T).toReal = if w ∈ T then 1 else 0 := by
  by_cases h : w ∈ T <;> simp [h]

/-- The action the gate implements. -/
def actG (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (J : Matrix (Fin 3) (Fin 3) ℝ) {N : ℕ}
    (η δe : ℝ) (H : Fin N → Record n) : Inst 1 n → ℝ :=
  if certG D V J η δe H then wHatF D (thetaHat D H) else vHatE D (thetaHat D H)

lemma gate_kernel (N : ℕ) (η δe : ℝ) (H : Fin N → Record n) :
    (gateG D V J N η δe).kernel H = Measure.dirac (actG D V J η δe H) := rfl

lemma act_fallback {N : ℕ} {η δe : ℝ} {H : Fin N → Record n} (hs : CurvSetting D V J U)
    (h : ¬ certG D V J η δe H) : actG D V J η δe H ∈ E D := by
  simp only [actG, h, ↓reduceIte]; exact (vHatE_mem hs _).1

lemma false_le (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) {η δe : ℝ} (hη : 0 ≤ η)
    {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V) : falseG D δe θ (gateG D V J N η δe) ≤ η := by
  obtain ⟨-, -, hq, -, -⟩ := inputs hs.1
  have hq1 : ∑ s, D.q s = 1 := hs.1.2.2.2.1
  have hmass := mass_nonneg D hq hq1 (N := N)
  have hcov := tq_mem D hq hq1 N hη
  have hsum := mass_sum D hq1 N
  have each : ∀ σ : Fin N → S, mass D σ * ((gateG D V J N η δe).kernel (hist D θ σ)
      {w | w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧ Adv D w θ ≤ δe}).toReal
      ≤ mass D σ - (if TN D σ ≤ tcrit D N η then mass D σ else 0) := by
    intro σ
    rw [gate_kernel, dirac_toReal]
    by_cases hT : TN D σ ≤ tcrit D N η
    · have hC := cover hs hN η hθ σ hT
      have hout : actG D V J η δe (hist D θ σ)
          ∉ {w | w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧ Adv D w θ ≤ δe} := by
        by_cases hc : certG D V J η δe (hist D θ σ)
        · simp only [actG, hc, ↓reduceIte]
          rintro ⟨-, hA⟩
          have := ell_le_Adv hs hN hC
          linarith [hc.2]
        · rintro ⟨ha, -⟩
          exact ha (congrFun (act_fallback hs hc).2 0)
      simp only [hout, hT, ↓reduceIte]; simp
    · simp only [hT, ↓reduceIte, sub_zero]
      split_ifs <;> linarith [hmass σ]
  calc falseG D δe θ (gateG D V J N η δe)
      ≤ ∑ σ : Fin N → S, (mass D σ - (if TN D σ ≤ tcrit D N η then mass D σ else 0)) :=
        Finset.sum_le_sum fun σ _ => each σ
    _ ≤ η := by rw [Finset.sum_sub_distrib, hsum]; linarith

lemma admits (hs : CurvSetting D V J U) {N : ℕ} {η δe : ℝ} (hδ : 0 ≤ δe) :
    AdmitsG D (gateG D V J N η δe) := by
  intro H
  rw [gate_kernel, Measure.dirac_apply]
  have hout : actG D V J η δe H ∉ {w | ¬ (w ∈ F D ∧ w (Sum.inl 0) ≠ w0 D (Sum.inl 0)) ∧ w ∉ E D} := by
    by_cases hc : certG D V J η δe H
    · simp only [actG, hc, ↓reduceIte]
      rintro ⟨h, -⟩
      exact h ⟨(wHatF_mem hs _).1, active_change hs hδ hc.2⟩
    · rintro ⟨-, h⟩
      exact h (act_fallback hs hc)
  exact Set.indicator_of_notMem hout _

lemma power_ge (hs : CurvSetting D V J U) {N : ℕ} (hN : 0 < N) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hu : uN D J N ε ≤ δ / 128) {θ : Fin 3 → ℝ} (hθ : θ ∈ Theta4 V)
    (hG : δ ≤ Gstar D θ) : 1 - ε ≤ powerG D (δ / 4) θ (gateG D V J N ε (δ / 4)) := by
  obtain ⟨-, -, hq, -, -⟩ := inputs hs.1
  have hq1 : ∑ s, D.q s = 1 := hs.1.2.2.2.1
  have hmass := mass_nonneg D hq hq1 (N := N)
  have hcov := tq_mem D hq hq1 N hε
  refine hcov.trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [gate_kernel, dirac_toReal]
  by_cases hT : TN D σ ≤ tcrit D N ε
  · have hC := cover hs hN ε hθ σ hT
    have hl := power_cov hs hδ hN hu hC hG
    have hc : certG D V J ε (δ / 4) (hist D θ σ) := ⟨⟨θ, hC⟩, by linarith⟩
    have hin : actG D V J ε (δ / 4) (hist D θ σ)
        ∈ {w | w (Sum.inl 0) ≠ w0 D (Sum.inl 0) ∧ δ / 4 < Adv D w θ} := by
      simp only [actG, hc, ↓reduceIte]
      refine ⟨active_change hs (by linarith) hc.2, ?_⟩
      have := ell_le_Adv hs hN hC
      linarith
    simp only [hin, hT, ↓reduceIte, mul_one, le_refl]
  · simp only [hT, ↓reduceIte]
    split_ifs <;> linarith [hmass σ]

/-- Both requirements at the sufficient length. -/
lemma sufficient (hs : CurvSetting D V J U) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1)
    {N : ℕ} (hNb : max 324 (1536 * Kc D J / δ) * Real.log (6 / ε) ≤ N) :
    AdmitsG D (gateG D V J N ε (δ / 4)) ∧ MeetsG D V δ ε (gateG D V J N ε (δ / 4)) := by
  set L := Real.log (6 / ε) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hK0 := (K_facts hs).1
  have h324 : 324 * L ≤ N := le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le) hNb
  have hKb : 1536 * Kc D J / δ * L ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le) hNb
  have hNr : (0 : ℝ) < N := by linarith [mul_pos (by norm_num : (0 : ℝ) < 324) hL]
  have hN : 0 < N := by exact_mod_cast hNr
  have ht := tcrit_12 hs hN hε hε1 (by linarith)
  have hr2 : rN D N ε ^ 2 ≤ 12 * L / N := by
    have h1 : rN D N ε ≤ Real.sqrt (12 * L / N) :=
      Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right hNr).mpr ht)
    calc rN D N ε ^ 2 ≤ Real.sqrt (12 * L / N) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      _ = 12 * L / N := Real.sq_sqrt (by positivity)
  have hKL : 1536 * Kc D J * L ≤ δ * N := by
    have := mul_le_mul_of_nonneg_left hKb hδ.le
    rwa [show δ * (1536 * Kc D J / δ * L) = 1536 * Kc D J * L by field_simp] at this
  have hu : uN D J N ε ≤ δ / 128 := by
    rw [uN]
    calc Kc D J * rN D N ε ^ 2 ≤ Kc D J * (12 * L / N) := mul_le_mul_of_nonneg_left hr2 hK0
      _ ≤ δ / 128 := by
        rw [← mul_div_assoc, div_le_iff₀ hNr]; linarith
  exact ⟨admits hs (by linarith), fun θ hθ => false_le hs hN hε.le hθ,
    fun θ hθ hG => power_ge hs hN hδ hε.le hu hθ hG⟩

/-- `K = 0`: every score difference is estimated exactly, so `ℓ_N = G_*(θ_*)`. -/
lemma K_zero (hs : CurvSetting D V J U) (hK : Kc D J = 0) {N : ℕ} (hN : 0 < N) (η : ℝ)
    (θ : Fin 3 → ℝ) (σ : Fin N → S) :
    ellG D J N η (thetaHat D (hist D θ σ)) = Gstar D θ := by
  set th := thetaHat D (hist D θ σ) with hth
  have hu : uN D J N η = 0 := by rw [uN, hK, zero_mul]
  have h3 : ∀ w, score D w (toPar th) = score D w (toPar θ) := by
    intro w
    have hg := (K_facts hs).2.1 w
    rw [hK, mul_zero, zero_mul] at hg
    have h0 : Jᵀ *ᵥ Aw D w = 0 :=
      dotProduct_self_eq_zero.mp (le_antisymm hg (gJ_nonneg D J w))
    have he : (θ - th) ⬝ᵥ Aw D w = 0 := by
      rw [hth, thetaHat_hist D hN, sub_add_cancel_left, neg_dotProduct, errN_J hs.2.2.2.2,
        Novel.M4JointDirectionalRateProof.dot_mulVec, h0, dotProduct_zero, neg_zero]
    rw [score_shift D w th θ, he, sub_zero]
  have hfun : (fun w => score D w (toPar th)) = fun w => score D w (toPar θ) := funext h3
  have h1 : wHatF D th = wHatF D θ := by unfold wHatF; rw [hfun]
  have h2 : vHatE D th = vHatE D θ := by unfold vHatE; rw [hfun]
  rw [ellG, hu, Gstar_eq hs, Ghat, Ghat, h1, h2, h3, h3]
  simp

end Setting

/-! ### Parts 1 and 2 -/

theorem certificate : Certificate := by
  intro n S _ D V J U hs
  refine ⟨K_facts hs, fun th => ⟨maxF hs th, maxE hs th, Ghat_nonneg hs th⟩,
    fun N η th hN hne => ?_, fun N η δe th hδ h => active_change hs hδ h,
    fun N η δe hN hη θ hθ => false_le hs hN hη hθ⟩
  simp only [LN, hne.ne_empty, ↓reduceIte]
  exact le_iInf₂ fun θ hθ => EReal.coe_le_coe_iff.mpr (ell_le_Adv hs hN hθ)

theorem power : Power := fun _ _ _ _ _ _ _ hs =>
  ⟨fun _ hδ _ _ hN hu _ _ hθ hG => power_cov hs hδ hN hu hθ hG,
    fun _ _ hδ hε hε1 _ hNb => sufficient hs hδ hε hε1 hNb,
    fun hK _ hN η θ σ => K_zero hs hK hN η θ σ⟩

/-! ### Part 3: claim 017's subfamily -/

section Class

open Standalone.M4CurvedEntryRate (data)

lemma Aw_d (s : ℝ) (q : S → ℝ) (U : S → Fin 3 → ℝ) (z : Inst 1 1 → ℝ) :
    Aw (data s q U) z = ![z (Sum.inl 0), z (Sum.inr 0), z (Sum.inl 0)] := by
  funext i
  fin_cases i <;> simp [Aw, exposure, data, active, etf, mulVec, dotProduct]

/-- Claim 017's family with `s = √κ` lies in the setting with `J = s I` and `K = s²`. -/
lemma class_mem {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 100) {q : S → ℝ} {U : S → Fin 3 → ℝ}
    (hK : InKJ q U) :
    CurvSetting (data s q U) (Standalone.M4CurvedEntryRate.V4 s) (s • 1) U ∧
      Kc (data s q U) (s • 1) = s ^ 2 := by
  obtain ⟨hadm, -, -, hcov, -⟩ := Novel.M4CurvedEntryRateProof.geometry s hs0 hs1 S q U hK
  have hγ : (data s q U).gamma = 1 / s ^ 2 := rfl
  have hp : ∀ z : Inst 1 1 → ℝ,
      pS (data s q U) z = s ^ 2 * (2 * z (Sum.inl 0) ^ 2 + z (Sum.inr 0) ^ 2) := by
    intro z
    rw [pS, hcov]
    simp [dotProduct, mulVec_diagonal, Standalone.M4CurvedEntryRate.act, Fintype.sum_sum_type]
    ring
  have hg : ∀ z, gJ (data s q U) (s • 1) z = pS (data s q U) z := by
    intro z
    rw [hp, gJ, Aw_d]
    simp [transpose_smul, smul_mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hpd : ∀ z : Inst 1 1 → ℝ, z ≠ 0 → 0 < pS (data s q U) z := by
    intro z hz
    rw [hp]
    have hsq : ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2 := fun x hx =>
      lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
    have hs2 : 0 < s ^ 2 := by positivity
    by_cases ha : z (Sum.inl 0) = 0
    · have hb : z (Sum.inr 0) ≠ 0 := by
        intro hb
        exact hz (funext fun i => by rcases i with j | j <;> fin_cases j <;> simp [ha, hb])
      have := hsq _ hb
      exact mul_pos hs2 (by nlinarith [sq_nonneg (z (Sum.inl 0))])
    · have := hsq _ ha
      exact mul_pos hs2 (by nlinarith [sq_nonneg (z (Sum.inr 0))])
  have hne1 : (fun _ => (1 : ℝ)) ≠ (0 : Inst 1 1 → ℝ) := fun h => by
    have := congrFun h (Sum.inl 0); simp at this
  refine ⟨⟨hadm, by rw [hγ]; positivity, hpd, hK, fun x => ?_⟩, ?_⟩
  · rw [Novel.M4CurvedEntryRateProof.zeta_d s q U x, smul_mulVec, one_mulVec]
  · have hset : {r | ∃ z : Inst 1 1 → ℝ, z ≠ 0 ∧
        r = gJ (data s q U) (s • 1) z / pS (data s q U) z} = {1} := by
      ext r
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hg, div_self (hpd z hz).ne']; rfl
      · rintro rfl
        exact ⟨_, hne1, by rw [hg, div_self (hpd _ hne1).ne']⟩
    rw [Kc_eq, hset, csSup_singleton, hγ]
    field_simp

lemma sqrt_facts {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000) :
    0 < Real.sqrt κ ∧ Real.sqrt κ ≤ 1 / 100 ∧ Real.sqrt κ ^ 2 = κ := by
  refine ⟨Real.sqrt_pos.mpr hκ, ?_, Real.sq_sqrt hκ.le⟩
  rw [Real.sqrt_le_left (by norm_num)]; norm_num; linarith

theorem classRate : ClassRate := by
  refine ⟨?_, ?_, ?_⟩
  · intro κ δ ε hκ hκ1 hδ hδκ hε hε1 N hN hyp
    obtain ⟨hs0, hs1, hss⟩ := sqrt_facts hκ hκ1
    set s := Real.sqrt κ
    have := Novel.M4CurvedEntryRateProof.lowerBound s δ ε hs0 hs1 hδ (by rw [hss]; exact hδκ)
      hε hε1 N hN ?_
    · rwa [hss] at this
    intro S _ q U hK
    obtain ⟨hcs, hKc⟩ := class_mem hs0 hs1 hK
    obtain ⟨ρ, hA, hM⟩ := hyp 1 S (data s q U) _ _ U hcs (by rw [hKc, hss])
    have hw0 : w0 (data s q U) = 0 := Novel.M4CurvedEntryRateProof.w0_d s q U
    have hmass : ∀ σ : Fin N → S, 0 ≤ mass (data s q U) σ :=
      fun σ => Finset.prod_nonneg fun _ _ => hK.1 _
    refine ⟨⟨ρ.kernel, ρ.isProb⟩, fun H => ?_, fun θ hθ => ?_, fun θ hθ hG => ?_⟩
    · refine measure_mono_null (fun w hw => ?_) (hA H)
      refine ⟨fun hF => hw.1 ⟨hF.1, ?_⟩, hw.2⟩
      have h0 := (hF.1.1 (Sum.inl 0)).1
      have h1 := hF.2
      rw [hw0] at h1
      exact lt_of_le_of_ne h0 (Ne.symm h1)
    · refine le_trans ?_ (hM.1 θ hθ)
      unfold Standalone.M4BoundedLawRate.falseP falseG
      refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hmass σ)
      have := ρ.isProb (hist (data s q U) θ σ)
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun w hw => ⟨?_, hw.2⟩)
      rw [hw0]; exact hw.1.ne'
    · refine le_trans (hM.2 θ hθ hG) ?_
      unfold Standalone.M4BoundedLawRate.powerP powerG
      refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hmass σ)
      have := ρ.isProb (hist (data s q U) θ σ)
      refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
      set Hh := hist (data s q U) θ σ
      calc ρ.kernel Hh {w | w (Sum.inl 0) ≠ w0 (data s q U) (Sum.inl 0) ∧
              δ / 4 < Adv (data s q U) w θ}
          ≤ ρ.kernel Hh ({w | 0 < w (Sum.inl 0) ∧ δ / 4 < Adv (data s q U) w θ} ∪
              {w | ¬ (w ∈ F (data s q U) ∧ w (Sum.inl 0) ≠ w0 (data s q U) (Sum.inl 0)) ∧
                w ∉ E (data s q U)}) := by
            refine measure_mono fun w hw => ?_
            obtain ⟨hne, hadv⟩ := hw
            by_cases hF : w ∈ F (data s q U)
            · left
              have h0 := (hF.1 (Sum.inl 0)).1
              rw [hw0] at hne
              exact ⟨lt_of_le_of_ne h0 (Ne.symm hne), hadv⟩
            · right
              exact ⟨fun h => hF h.1, fun hE => hF hE.1⟩
        _ ≤ _ := measure_union_le _ _
        _ = _ := by rw [hA Hh, add_zero]
  · intro κ δ ε hδ hδκ hε hε1 N hNb n S _ D V J U hs hK
    apply sufficient hs hδ hε hε1
    have hL : 0 < Real.log (6 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hL.le) hNb
    have hκδ : 128 ≤ κ / δ := by rw [le_div_iff₀ hδ]; linarith
    refine max_le (by linarith) ?_
    rw [mul_div_assoc]
    gcongr
  · intro κ hκ hκ1
    obtain ⟨hs0, hs1, hss⟩ := sqrt_facts hκ hκ1
    obtain ⟨h1, h2⟩ := class_mem hs0 hs1
      (Novel.M4JointDirectionalRateProof.latent_inKJ (k := 2) le_rfl)
    exact ⟨_, inferInstance, _, _, _, _, h1, h2.trans hss⟩

end Class

/-- Claim 018, all parts. -/
theorem proof : Standalone.M4CurvatureCertificate.statement := ⟨certificate, power, classRate⟩

end

end Novel.M4CurvatureCertificateProof

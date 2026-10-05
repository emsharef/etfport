import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Standalone.M7FineCostSandwich
import Novel.M7FineBandOneCostlyEtfProof

/-!
# Claim 043: proof

The one-instrument pieces reuse claim 042's corrector (`wp`, `wpp`, `correctorC2`, lean's module), per
Q-04. They take symmetric rates and are integrated once. The sub- and supersolutions are the sum of a fund
piece in `y_a` and an ETF piece in `e` (proof part 2).
-/

namespace Novel.M7FineCostSandwichProof

open Standalone.M7FineCostSandwich Standalone.M7FineBandOneCostlyEtf Filter Topology Set

noncomputable section

/-! ### The one-instrument pieces -/

section Piece

variable {c v k : ℝ}

/-- The piece's gradient: claim 042's `w'` with symmetric rates `k`, at `Δ(k)`. -/
abbrev g1 (c v k : ℝ) : ℝ → ℝ := wp c v k k (Dl c v k)

/-- The piece's second derivative. -/
abbrev g2 (c v k : ℝ) : ℝ → ℝ := wpp c v (Dl c v k)

/-- The piece itself, `∫₀^y w'`. -/
def pw (c v k : ℝ) (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, g1 c v k t

lemma X_nonneg (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) : 0 ≤ 3 * (2 * k) * v / (4 * c) := by
  positivity

lemma Dl_nonneg (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) : 0 ≤ Dl c v k :=
  Real.rpow_nonneg (X_nonneg hc hv hk) _

lemma Dl_cube (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) : Dl c v k ^ 3 = 3 * (2 * k) * v / (4 * c) := by
  unfold Dl
  rw [← Real.rpow_natCast, ← Real.rpow_mul (X_nonneg hc hv hk)]
  norm_num

lemma aOne_eq (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) : aOne c v k = c * Dl c v k ^ 2 / 2 := by
  unfold aOne Dl
  rw [← Real.rpow_natCast, ← Real.rpow_mul (X_nonneg hc hv hk)]
  norm_num
  ring

lemma Dl_zero (c v : ℝ) : Dl c v 0 = 0 := by
  simp [Dl]

lemma aOne_zero (c v : ℝ) : aOne c v 0 = 0 := by
  simp [aOne]

/-- What the construction uses of one piece. -/
structure PieceSpec (c v k : ℝ) : Prop where
  hasDeriv : ∀ y, HasDerivAt (g1 c v k) (g2 c v k y) y
  cont : Continuous (g2 c v k)
  bound : ∀ y, |g1 c v k y| ≤ k
  off : ∀ y, Dl c v k < |y| → |g1 c v k y| = k
  top : g1 c v k (Dl c v k) = k
  bot : g1 c v k (-Dl c v k) = -k
  zero : g1 c v k 0 = 0
  nonneg2 : ∀ y, 0 ≤ g2 c v k y
  hjb : ∀ y, aOne c v k ≤ v / 2 * g2 c v k y + c / 2 * y ^ 2
  hjb_eq : ∀ y, |y| ≤ Dl c v k → v / 2 * g2 c v k y + c / 2 * y ^ 2 = aOne c v k

lemma off_of (c v k D y : ℝ) (h : D < |y|) : |wp c v k k D y| = |k| := by
  unfold wp
  split_ifs with h1 h2
  · simp
  · rfl
  · exfalso
    rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> linarith

lemma wp_zero (c v k D : ℝ) (hD : 0 ≤ D) : wp c v k k D 0 = 0 := by
  unfold wp
  split_ifs with h1 h2
  · linarith
  · linarith
  · ring

lemma wpp_nonneg (c v D y : ℝ) (hc : 0 < c) (hv : 0 < v) : 0 ≤ wpp c v D y := by
  unfold wpp
  split_ifs with h
  · apply div_nonneg _ hv.le
    have : y ^ 2 ≤ D ^ 2 := by
      have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
      exact this
    nlinarith
  · exact le_rfl

theorem pieceSpec (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) : PieceSpec c v k := by
  rcases hk.eq_or_lt with h0 | hpos
  · subst h0
    have h1 : ∀ y, wp c v 0 0 0 y = 0 := by
      intro y
      unfold wp
      split_ifs with ha hb
      · simp
      · rfl
      · have : y = 0 := by linarith
        subst this
        ring
    have h2 : ∀ y, wpp c v 0 y = 0 := by
      intro y
      unfold wpp
      split_ifs with h
      · have : y = 0 := abs_nonpos_iff.1 h
        subst this
        ring
      · rfl
    have e1 : g1 c v 0 = fun _ => 0 := by
      funext y
      simp only [g1, Dl_zero, h1]
    have e2 : g2 c v 0 = fun _ => 0 := by
      funext y
      simp only [g2, Dl_zero, h2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [e1, e2]
      exact hasDerivAt_const _ _
    · rw [e2]
      exact continuous_const
    · intro y
      simp [e1]
    · intro y _
      simp [e1]
    · simp [e1]
    · simp [e1]
    · simp [e1]
    · intro y
      simp [e2]
    · intro y
      rw [e2, aOne_zero]
      positivity
    · intro y hy
      rw [Dl_zero] at hy
      have : y = 0 := abs_nonpos_iff.1 hy
      subst this
      simp [e2, aOne_zero]
  · set D := Dl c v k with hDdef
    have hX : 0 < 3 * (2 * k) * v / (4 * c) := by positivity
    have hD : 0 < D := Real.rpow_pos_of_pos hX _
    have hD3 : D ^ 3 = 3 * (k + k) * v / (4 * c) := by
      rw [hDdef, Dl_cube hc hv hk]
      ring
    have H := (Novel.M7FineBandOneCostlyEtfProof.correctorC2 c v k k hc hv hk hk (by linarith)).2 D hD hD3
    simp only at H
    obtain ⟨_, hder, hcont, _, _, hbd, hbot, htop, hjb, hjbeq, _, _⟩ := H
    have ha : aOne c v k = c * D ^ 2 / 2 := aOne_eq hc hv hk
    refine ⟨hder, hcont, fun y => abs_le.2 (hbd y), fun y hy => ?_, htop, hbot,
      wp_zero c v k D hD.le, fun y => wpp_nonneg c v D y hc hv, fun y => ?_, fun y hy => ?_⟩
    · rw [off_of c v k D y hy, abs_of_pos hpos]
    · rw [ha]
      exact hjb y
    · rw [ha]
      exact hjbeq y hy

variable (h : PieceSpec c v k)
include h

lemma PieceSpec.cont1 : Continuous (g1 c v k) :=
  continuous_iff_continuousAt.2 fun y => (h.hasDeriv y).continuousAt

lemma PieceSpec.hasDerivAt_pw (y : ℝ) : HasDerivAt (pw c v k) (g1 c v k y) y :=
  (h.cont1.integral_hasStrictDerivAt 0 y).hasDerivAt

lemma PieceSpec.contDiff : ContDiff ℝ 2 (pw c v k) := by
  have hd : deriv (pw c v k) = g1 c v k := funext fun y => (h.hasDerivAt_pw y).deriv
  have hd2 : deriv (g1 c v k) = g2 c v k := funext fun y => (h.hasDeriv y).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun y => (h.hasDerivAt_pw y).differentiableAt, by simp, ?_⟩
  rw [hd, contDiff_one_iff_deriv, hd2]
  exact ⟨fun y => (h.hasDeriv y).differentiableAt, h.cont⟩

lemma PieceSpec.mono : Monotone (g1 c v k) :=
  monotone_of_deriv_nonneg (fun y => (h.hasDeriv y).differentiableAt)
    (fun y => by rw [(h.hasDeriv y).deriv]; exact h.nonneg2 y)

omit h in
/-- The tangent line of a function with monotone derivative lies below it. -/
lemma tangent {f f' : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f' y) y) (hm : Monotone f') (y₀ y : ℝ) :
    f y₀ + f' y₀ * (y - y₀) ≤ f y := by
  rcases lt_trichotomy y₀ y with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hs⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
    have h1 : f' y₀ ≤ f' ξ := hm hξ.1.le
    rw [hs, le_div_iff₀ (sub_pos.2 hlt)] at h1
    linarith
  · subst heq
    simp
  · obtain ⟨ξ, hξ, hs⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
    have h1 : f' ξ ≤ f' y₀ := hm hξ.2.le
    rw [hs, div_le_iff₀ (sub_pos.2 hgt)] at h1
    nlinarith

lemma PieceSpec.pw_le (y : ℝ) : pw c v k y ≤ k * |y| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y) (C := k)
    (f := g1 c v k) (fun t _ => by simpa [Real.norm_eq_abs] using h.bound t)
  rw [Real.norm_eq_abs, sub_zero] at hb
  exact (le_abs_self _).trans hb

lemma PieceSpec.pw_ge (hc : 0 < c) (hv : 0 < v) (hk : 0 ≤ k) (y : ℝ) :
    k * |y| - k * Dl c v k ≤ pw c v k y := by
  have hD := Dl_nonneg hc hv hk
  have p0 : pw c v k 0 = 0 := intervalIntegral.integral_same
  have tD := tangent h.hasDerivAt_pw h.mono (Dl c v k) y
  have tmD := tangent h.hasDerivAt_pw h.mono (-Dl c v k) y
  have t0 := tangent h.hasDerivAt_pw h.mono 0 (Dl c v k)
  have t0' := tangent h.hasDerivAt_pw h.mono 0 (-Dl c v k)
  rw [h.top] at tD
  rw [h.bot] at tmD
  rw [h.zero, p0] at t0 t0'
  rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy] <;> nlinarith

end Piece

/-! ### Separable functions on the plane -/

section Sep

/-- `(y_a, e) ↦ f(y_a) + g(e)`. -/
def sep (f g : ℝ → ℝ) : ℝ × ℝ → ℝ := fun y => f y.1 + g y.2

variable {f g f' g' f'' g'' : ℝ → ℝ}

lemma hasFDerivAt_sep {a b : ℝ} {y : ℝ × ℝ} (hf : HasDerivAt f a y.1) (hg : HasDerivAt g b y.2) :
    HasFDerivAt (sep f g) (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
  (hf.comp_hasFDerivAt y hasFDerivAt_fst).add (hg.comp_hasFDerivAt y hasFDerivAt_snd)

lemma fderiv_sep (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t) (z u : ℝ × ℝ) :
    fderiv ℝ (sep f g) z u = f' z.1 * u.1 + g' z.2 * u.2 := by
  rw [(hasFDerivAt_sep (hf z.1) (hg z.2)).fderiv]
  simp [mul_comm]

lemma d2_sep (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hf2 : ∀ t, HasDerivAt f' (f'' t) t) (hg2 : ∀ t, HasDerivAt g' (g'' t) t) (y u w : ℝ × ℝ) :
    d2 (sep f g) y u w = f'' y.1 * u.1 * w.1 + g'' y.2 * u.2 * w.2 := by
  have e : (fun z => fderiv ℝ (sep f g) z u) = sep (fun t => f' t * u.1) (fun t => g' t * u.2) :=
    funext fun z => fderiv_sep hf hg z u
  unfold d2
  rw [e, fderiv_sep (fun t => (hf2 t).mul_const u.1) (fun t => (hg2 t).mul_const u.2)]

lemma grad_sep (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t) (y : ℝ × ℝ) :
    grad (sep f g) y = (f' y.1, g' y.2) := by
  simp [grad, fderiv_sep hf hg]

lemma diffusion_sep (P : Inputs) (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hf2 : ∀ t, HasDerivAt f' (f'' t) t) (hg2 : ∀ t, HasDerivAt g' (g'' t) t) (y : ℝ × ℝ) :
    diffusion P (sep f g) y = (P.vA * f'' y.1 + P.vBeff * g'' y.2) / 2 := by
  simp only [diffusion, d2_sep hf hg hf2 hg2]
  ring

lemma contDiff_sep (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) : ContDiff ℝ 2 (sep f g) :=
  (hf.comp contDiff_fst).add (hg.comp contDiff_snd)

end Sep

/-! ### The standing hypotheses -/

section SettingFacts

variable {P : Inputs} (hS : Setting P)
include hS

lemma cres_pos : 0 < P.cres := by
  have hs := hS.sEE_pos
  have : 0 < P.sAA - P.sAE ^ 2 / P.sEE := by
    rw [sub_pos, div_lt_iff₀ hs]
    exact hS.det_pos
  exact mul_pos hS.gamma_pos this

lemma cE_pos : 0 < P.cE := mul_pos hS.gamma_pos hS.sEE_pos

lemma vBeff_pos : 0 < P.vBeff := by
  have hs : Real.sqrt (P.vA * P.vB) = Real.sqrt P.vA * Real.sqrt P.vB :=
    Real.sqrt_mul hS.vA_pos.le _
  have ha := Real.sq_sqrt hS.vA_pos.le
  have hb := Real.sq_sqrt hS.vB_pos.le
  have e : P.vBeff = (1 - P.r ^ 2) * P.vB + (P.r * Real.sqrt P.vB + P.rho * Real.sqrt P.vA) ^ 2 := by
    unfold Inputs.vBeff
    rw [hs]
    linear_combination (-(P.r ^ 2)) * hb - P.rho ^ 2 * ha
  rw [e]
  have : 0 < (1 - P.r ^ 2) * P.vB := mul_pos (by linarith [hS.r_sq]) hS.vB_pos
  positivity

end SettingFacts

/-! ### Proof part 2: the sub- and supersolutions -/

section Construction

variable {P : Inputs}

/-- The subsolution `w_{k_A'}(y_a) + w_{k_E'}(e)`. -/
def wSub (P : Inputs) (kA' kE' : ℝ) : ℝ × ℝ → ℝ := sep (pw P.cres P.vA kA') (pw P.cE P.vBeff kE')

/-- The supersolution `w_{κ_A + |ρ_h|κ_E}(y_a) + w_{κ_E}(e)`. -/
def wSuper (P : Inputs) : ℝ × ℝ → ℝ :=
  sep (pw P.cres P.vA (P.kA + |P.rho| * P.kE)) (pw P.cE P.vBeff P.kE)

lemma abs_e_le (ρ a e : ℝ) : |e| ≤ |e - ρ * a| + |ρ| * |a| := by
  have := abs_add_le (e - ρ * a) (ρ * a)
  rwa [sub_add_cancel, abs_mul] at this

theorem isSub (hS : Setting P) {kA' kE' : ℝ} (hadm : Adm P kA' kE') :
    IsSub P (wSub P kA' kE') (aA P kA' + aE P kE') := by
  obtain ⟨h1, h2, h3, h4⟩ := hadm
  have sA := pieceSpec (cres_pos hS) hS.vA_pos h1
  have sE := pieceSpec (cE_pos hS) (vBeff_pos hS) h2
  refine ⟨contDiff_sep sA.contDiff sE.contDiff, ⟨0, fun y => ?_⟩, fun y => ⟨?_, ?_⟩⟩
  · have ha := sA.pw_le y.1
    have he := sE.pw_le y.2
    have t := mul_le_mul_of_nonneg_left (abs_e_le P.rho y.1 y.2) h2
    have t2 := mul_le_mul_of_nonneg_right h4 (abs_nonneg (y.2 - P.rho * y.1))
    have t3 := mul_le_mul_of_nonneg_right h3 (abs_nonneg y.1)
    simp only [wSub, sep, deltaC]
    nlinarith
  · rw [wSub, diffusion_sep P sA.hasDerivAt_pw sE.hasDerivAt_pw sA.hasDeriv sE.hasDeriv]
    have ha := sA.hjb y.1
    have he := sE.hjb y.2
    simp only [aA, aE, cost]
    linarith
  · rw [wSub, grad_sep sA.hasDerivAt_pw sE.hasDerivAt_pw]
    have ba := sA.bound y.1
    have be := sE.bound y.2
    refine ⟨?_, be.trans h4⟩
    calc |g1 P.cres P.vA kA' y.1 + P.rho * g1 P.cE P.vBeff kE' y.2|
        ≤ |g1 P.cres P.vA kA' y.1| + |P.rho| * |g1 P.cE P.vBeff kE' y.2| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ kA' + |P.rho| * kE' := by gcongr
      _ ≤ P.kA := h3

theorem isSuper (hS : Setting P) : IsSuper P (wSuper P) (upper P) := by
  set kP := P.kA + |P.rho| * P.kE with hkP
  have hkP0 : 0 ≤ kP := by have := abs_nonneg P.rho; have := hS.kE_pos; have := hS.kA_pos; positivity
  have sA := pieceSpec (cres_pos hS) hS.vA_pos hkP0
  have sE := pieceSpec (cE_pos hS) (vBeff_pos hS) hS.kE_pos.le
  refine ⟨contDiff_sep sA.contDiff sE.contDiff,
    ⟨kP * Dl P.cres P.vA kP + P.kE * Dl P.cE P.vBeff P.kE, fun y => ?_⟩, fun y => ?_⟩
  · have ha := sA.pw_ge (cres_pos hS) hS.vA_pos hkP0 y.1
    have he := sE.pw_ge (cE_pos hS) (vBeff_pos hS) hS.kE_pos.le y.2
    have t : |y.2 - P.rho * y.1| ≤ |y.2| + |P.rho| * |y.1| := by
      have := abs_sub (y.2) (P.rho * y.1)
      rwa [abs_mul] at this
    have t2 := mul_le_mul_of_nonneg_left t hS.kE_pos.le
    simp only [wSuper, sep, deltaC]
    nlinarith
  · rw [wSuper, grad_sep sA.hasDerivAt_pw sE.hasDerivAt_pw]
    by_cases h1 : |y.1| ≤ Dl P.cres P.vA kP
    · by_cases h2 : |y.2| ≤ Dl P.cE P.vBeff P.kE
      · left
        rw [diffusion_sep P sA.hasDerivAt_pw sE.hasDerivAt_pw sA.hasDeriv sE.hasDeriv]
        have ha := sA.hjb_eq y.1 h1
        have he := sE.hjb_eq y.2 h2
        simp only [upper, aA, aE, cost]
        linarith
      · right
        rintro ⟨_, hlt⟩
        rw [sE.off y.2 (lt_of_not_ge h2)] at hlt
        exact lt_irrefl _ hlt
    · right
      rintro ⟨hlt, _⟩
      have ea := sA.off y.1 (lt_of_not_ge h1)
      have be := sE.bound y.2
      have t : |g1 P.cres P.vA kP y.1| ≤
          |g1 P.cres P.vA kP y.1 + P.rho * g1 P.cE P.vBeff P.kE y.2| +
            |P.rho| * |g1 P.cE P.vBeff P.kE y.2| := by
        have := abs_sub (g1 P.cres P.vA kP y.1 + P.rho * g1 P.cE P.vBeff P.kE y.2)
          (P.rho * g1 P.cE P.vBeff P.kE y.2)
        rwa [add_sub_cancel_right, abs_mul] at this
      have t2 := mul_le_mul_of_nonneg_left be (abs_nonneg P.rho)
      simp only at hlt
      linarith

end Construction

/-! ### Continuity of the eigenvalue formula -/

lemma continuous_aOne (c v : ℝ) : Continuous (aOne c v) := by
  unfold aOne
  exact continuous_const.mul
    ((by fun_prop : Continuous fun k : ℝ => 3 * (2 * k) * v / (4 * c)).rpow_const
      (fun _ => Or.inr (by norm_num)))

/-! ### Part 1 -/

theorem sandwich : Sandwich := by
  intro P hS
  refine ⟨fun _ _ hadm => ⟨_, isSub hS hadm⟩, ⟨_, isSuper hS⟩, ?_, fun a ha => ?_⟩
  · let S : Set (ℝ × ℝ) := {q | Adm P q.1 q.2}
    have hcl : IsClosed S := by
      simp only [S, Adm, Set.ofPred_and]
      exact (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const continuous_snd).inter
          ((isClosed_le (by fun_prop) continuous_const).inter
            (isClosed_le continuous_snd continuous_const)))
    have hsub : S ⊆ Icc 0 P.kA ×ˢ Icc 0 P.kE := by
      rintro q ⟨h1, h2, h3, h4⟩
      have : 0 ≤ |P.rho| * q.2 := mul_nonneg (abs_nonneg _) h2
      exact ⟨⟨h1, by linarith⟩, ⟨h2, h4⟩⟩
    have hSc : IsCompact S := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hcl hsub
    have hne : S.Nonempty :=
      ⟨(0, 0), le_rfl, le_rfl, by simp [hS.kA_pos.le], hS.kE_pos.le⟩
    have hcont : ContinuousOn (fun q : ℝ × ℝ => aA P q.1 + aE P q.2) S :=
      (((continuous_aOne _ _).comp continuous_fst).add
        ((continuous_aOne _ _).comp continuous_snd)).continuousOn
    obtain ⟨q, hq, hmax⟩ := hSc.exists_isMaxOn hne hcont
    exact ⟨q, hq, fun q' hq' => hmax hq'⟩
  · obtain ⟨hlo, hhi⟩ := ha
    refine ⟨fun kA' kE' hadm => hlo _ _ (isSub hS hadm), hhi _ _ (isSuper hS), fun hx => ?_⟩
    exact hlo _ _ (isSub hS ⟨by linarith, hS.kE_pos.le, by linarith, le_rfl⟩)

/-! ### Part 2 -/

theorem uncorrelated : Standalone.M7FineCostSandwich.Uncorrelated := by
  intro P hS h0 a ha
  obtain ⟨_, _, _, hb⟩ := sandwich P hS
  have hr : P.rho = 0 := by simp [Inputs.rho, h0]
  obtain ⟨_, hu, hd⟩ := hb a ha
  have hl := hd (by rw [hr]; simp [hS.kA_pos])
  simp only [lower, upper, hr, abs_zero, zero_mul, sub_zero, add_zero] at hl hu
  linarith

/-! ### Part 3 -/

lemma aOne_scale {c v : ℝ} (hc : 0 < c) (hv : 0 < v) {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) :
    aOne c v (k * t) = aOne c v k * t ^ ((2 : ℝ) / 3) := by
  unfold aOne
  rw [show 3 * (2 * (k * t)) * v / (4 * c) = 3 * (2 * k) * v / (4 * c) * t by ring,
    Real.mul_rpow (X_nonneg hc hv hk) ht]
  ring

theorem gap : Gap := by
  intro P hS hx
  have hkA := hS.kA_pos
  have hc := cres_pos hS
  have hv := hS.vA_pos
  have hx0 : 0 ≤ x P := by
    unfold x
    have := hS.kE_pos
    positivity
  have e1 : P.kA - |P.rho| * P.kE = P.kA * (1 - x P) := by
    unfold x
    field_simp
  have e2 : P.kA + |P.rho| * P.kE = P.kA * (1 + x P) := by
    unfold x
    field_simp
  have hpos : 0 < aA P P.kA := by
    unfold aA aOne
    have hX : 0 < 3 * (2 * P.kA) * P.vA / (4 * P.cres) := by positivity
    have := Real.rpow_pos_of_pos hX ((2 : ℝ) / 3)
    positivity
  have f1 : aA P (P.kA - |P.rho| * P.kE) = aA P P.kA * (1 - x P) ^ ((2 : ℝ) / 3) := by
    rw [e1]
    exact aOne_scale hc hv hkA.le (by linarith)
  have f2 : aA P (P.kA + |P.rho| * P.kE) = aA P P.kA * (1 + x P) ^ ((2 : ℝ) / 3) := by
    rw [e2]
    exact aOne_scale hc hv hkA.le (by linarith)
  refine ⟨hpos, f1, f2, ?_, ?_⟩
  · unfold upper lower
    rw [f1, f2]
    field_simp
    ring
  · have hcc := Real.concaveOn_rpow (p := (2 : ℝ) / 3) (by norm_num) (by norm_num)
    have m1 : 1 + x P ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
    have m2 : 1 - x P ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
    have h := hcc.2 m1 m2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at h
    rw [show (1 / 2 : ℝ) * (1 + x P) + 1 / 2 * (1 - x P) = 1 by ring, Real.one_rpow] at h
    linarith

/-! ### Part 4 -/

theorem effectiveRate : EffectiveRate := by
  intro P hS hle a ha
  obtain ⟨_, _, _, hb⟩ := sandwich P hS
  obtain ⟨hl, hu, _⟩ := hb a ha
  have hlo := hl (P.kA - |P.rho| * P.kE) P.kE ⟨by linarith, hS.kE_pos.le, by linarith, le_rfl⟩
  have hab : P.kA - |P.rho| * P.kE ≤ P.kA + |P.rho| * P.kE := by
    have := mul_nonneg (abs_nonneg P.rho) hS.kE_pos.le
    linarith
  have hcont : ContinuousOn (fun k => aA P k + aE P P.kE)
      (Icc (P.kA - |P.rho| * P.kE) (P.kA + |P.rho| * P.kE)) :=
    ((continuous_aOne _ _).add continuous_const).continuousOn
  obtain ⟨k, hk, hk'⟩ := intermediate_value_Icc hab hcont ⟨hlo, hu⟩
  exact ⟨k, hk, hk'.symm⟩

theorem bandRatio : BandRatio := by
  intro P hS hx k hk
  have hkA := hS.kA_pos
  have hc := cres_pos hS
  have hv := hS.vA_pos
  have e1 : (1 - x P) * P.kA = P.kA - |P.rho| * P.kE := by
    unfold x
    field_simp
  have e2 : (1 + x P) * P.kA = P.kA + |P.rho| * P.kE := by
    unfold x
    field_simp
  have hlo : 0 ≤ P.kA - |P.rho| * P.kE := by
    rw [← e1]
    exact mul_nonneg (by linarith) hkA.le
  have hk0 : 0 ≤ k := hlo.trans hk.1
  rw [Dl_cube hc hv hk0, Dl_cube hc hv hkA.le]
  have e : 3 * (2 * k) * P.vA / (4 * P.cres) / (3 * (2 * P.kA) * P.vA / (4 * P.cres)) =
      k / P.kA := by
    field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ hkA]
    linarith [hk.1]
  · rw [div_le_iff₀ hkA]
    linarith [hk.2]

theorem smallEtfRate : SmallEtfRate := by
  intro P hS a ha
  let Q : ℝ → Inputs := fun k => { P with kE := k }
  have hQ : ∀ k, 0 < k → Setting (Q k) := fun k hk =>
    ⟨hS.gamma_pos, hS.sEE_pos, hS.det_pos, hS.vA_pos, hS.vB_pos, hS.r_sq, hS.kA_pos, hk⟩
  have hA := continuous_aOne P.cres P.vA
  have hE := continuous_aOne P.cE P.vBeff
  have hE0 : Tendsto (fun k => aE P k) (𝓝 0) (𝓝 0) := by
    have := hE.tendsto 0
    rwa [aOne_zero] at this
  have hL : Tendsto (fun k => aA P (P.kA - |P.rho| * k) + aE P k) (𝓝[>] 0) (𝓝 (aA P P.kA)) := by
    have h1 : Tendsto (fun k => aA P (P.kA - |P.rho| * k)) (𝓝 0) (𝓝 (aA P P.kA)) := by
      have := (hA.comp (by fun_prop : Continuous fun k : ℝ => P.kA - |P.rho| * k)).tendsto 0
      simpa [Function.comp_def, aA] using this
    simpa using (h1.add hE0).mono_left nhdsWithin_le_nhds
  have hU : Tendsto (fun k => aA P (P.kA + |P.rho| * k) + aE P k) (𝓝[>] 0) (𝓝 (aA P P.kA)) := by
    have h1 : Tendsto (fun k => aA P (P.kA + |P.rho| * k)) (𝓝 0) (𝓝 (aA P P.kA)) := by
      have := (hA.comp (by fun_prop : Continuous fun k : ℝ => P.kA + |P.rho| * k)).tendsto 0
      simpa [Function.comp_def, aA] using this
    simpa using (h1.add hE0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), 0 < k ∧ |P.rho| * k < P.kA := by
    have h1 : ∀ᶠ k in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
    have ht : Tendsto (fun k : ℝ => |P.rho| * k) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul |P.rho|
      rwa [mul_zero] at this
    have h2 : ∀ᶠ k in 𝓝[>] (0 : ℝ), |P.rho| * k < P.kA :=
      (ht.eventually (gt_mem_nhds hS.kA_pos)).filter_mono nhdsWithin_le_nhds
    exact h1.and h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [hev] with k hk
    obtain ⟨_, _, _, hb⟩ := sandwich (Q k) (hQ k hk.1)
    exact (hb (a k) (ha k hk.1)).2.2 hk.2
  · filter_upwards [hev] with k hk
    obtain ⟨_, _, _, hb⟩ := sandwich (Q k) (hQ k hk.1)
    exact (hb (a k) (ha k hk.1)).2.1

/-! ### Functions of the ETF's gap -/

section Lin

/-- `(y_a, e) ↦ f(e - ρ y_a)`. -/
def lin (f : ℝ → ℝ) (ρ : ℝ) : ℝ × ℝ → ℝ := fun y => f (y.2 - ρ * y.1)

variable {f f' f'' : ℝ → ℝ} {ρ : ℝ}

lemma hasFDerivAt_lin {a : ℝ} {y : ℝ × ℝ} (hf : HasDerivAt f a (y.2 - ρ * y.1)) :
    HasFDerivAt (lin f ρ)
      (a • (ContinuousLinearMap.snd ℝ ℝ ℝ - ρ • ContinuousLinearMap.fst ℝ ℝ ℝ)) y := by
  have hL : HasFDerivAt (fun y : ℝ × ℝ => y.2 - ρ * y.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ρ • ContinuousLinearMap.fst ℝ ℝ ℝ) y := by
    have := (ContinuousLinearMap.snd ℝ ℝ ℝ - ρ • ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := y)
    convert this using 1
    funext z
    simp
  exact hf.comp_hasFDerivAt y hL

lemma fderiv_lin (hf : ∀ t, HasDerivAt f (f' t) t) (z u : ℝ × ℝ) :
    fderiv ℝ (lin f ρ) z u = f' (z.2 - ρ * z.1) * (u.2 - ρ * u.1) := by
  rw [(hasFDerivAt_lin (hf _)).fderiv]
  simp [smul_eq_mul]

lemma d2_lin (hf : ∀ t, HasDerivAt f (f' t) t) (hf2 : ∀ t, HasDerivAt f' (f'' t) t)
    (y u w : ℝ × ℝ) :
    d2 (lin f ρ) y u w = f'' (y.2 - ρ * y.1) * (u.2 - ρ * u.1) * (w.2 - ρ * w.1) := by
  have e : (fun z => fderiv ℝ (lin f ρ) z u) = lin (fun t => f' t * (u.2 - ρ * u.1)) ρ :=
    funext fun z => fderiv_lin hf z u
  unfold d2
  rw [e, fderiv_lin (fun t => (hf2 t).mul_const _)]

lemma grad_lin (hf : ∀ t, HasDerivAt f (f' t) t) (y : ℝ × ℝ) :
    grad (lin f ρ) y = (f' (y.2 - ρ * y.1) * (-ρ), f' (y.2 - ρ * y.1)) := by
  simp [grad, fderiv_lin hf]

lemma contDiff_lin (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (lin f ρ) :=
  hf.comp (by fun_prop)

end Lin

/-! ### The third lower bound -/

section Third

variable {P : Inputs}

lemma cb_pos (hS : Setting P) : 0 < cb P := by
  have := cres_pos hS
  have := cE_pos hS
  unfold cb
  positivity

/-- The pair's cost is at least `(c_b/2) y_b²` at the gap `y_b = e - ρ_h y_a`. -/
lemma cost_ge (hS : Setting P) (y : ℝ × ℝ) : cb P / 2 * (y.2 - P.rho * y.1) ^ 2 ≤ cost P y := by
  have hc := cres_pos hS
  have hE := cE_pos hS
  have hD : 0 < P.cres + P.rho ^ 2 * P.cE := by positivity
  have key : cb P * (y.2 - P.rho * y.1) ^ 2 ≤ P.cres * y.1 ^ 2 + P.cE * y.2 ^ 2 := by
    unfold cb
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    nlinarith [sq_nonneg (P.cres * y.1 + P.rho * P.cE * y.2)]
  unfold cost
  linarith

theorem isSub3 (hS : Setting P) :
    IsSub P (lin (pw (cb P) P.vB P.kE) P.rho) (ab P P.kE) := by
  have s := pieceSpec (cb_pos hS) hS.vB_pos hS.kE_pos.le
  refine ⟨contDiff_lin s.contDiff, ⟨0, fun y => ?_⟩, fun y => ⟨?_, ?_⟩⟩
  · have h1 := s.pw_le (y.2 - P.rho * y.1)
    have h2 : 0 ≤ P.kA * |y.1| := mul_nonneg hS.kA_pos.le (abs_nonneg _)
    simp only [lin, deltaC]
    linarith
  · have hv : P.vA * P.rho ^ 2 - 2 * P.wc * P.rho + P.vBeff = P.vB := by
      unfold Inputs.wc Inputs.vBeff
      ring
    have hd : diffusion P (lin (pw (cb P) P.vB P.kE) P.rho) y =
        P.vB / 2 * g2 (cb P) P.vB P.kE (y.2 - P.rho * y.1) := by
      simp only [diffusion, d2_lin s.hasDerivAt_pw s.hasDeriv]
      rw [← hv]
      ring
    rw [hd]
    have := s.hjb (y.2 - P.rho * y.1)
    have := cost_ge hS y
    unfold ab
    linarith
  · rw [grad_lin s.hasDerivAt_pw]
    refine ⟨?_, s.bound _ |>.trans le_rfl⟩
    simp only
    rw [show g1 (cb P) P.vB P.kE (y.2 - P.rho * y.1) * -P.rho +
        P.rho * g1 (cb P) P.vB P.kE (y.2 - P.rho * y.1) = 0 by ring, abs_zero]
    exact hS.kA_pos.le

theorem gapBound : GapBound := fun _ hS =>
  ⟨⟨_, isSub3 hS⟩, fun _ ha => ha.1 _ _ (isSub3 hS)⟩

lemma tendsto_aOne {c v : ℝ} (hc : 0 < c) (hv : 0 < v) : Tendsto (aOne c v) atTop atTop := by
  have h1 : Tendsto (fun k : ℝ => 3 * (2 * k) * v / (4 * c)) atTop atTop := by
    have : (fun k : ℝ => 3 * (2 * k) * v / (4 * c)) = fun k => (3 * 2 * v / (4 * c)) * k := by
      funext k
      ring
    rw [this]
    exact tendsto_id.const_mul_atTop (by positivity)
  have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h1
  exact h2.const_mul_atTop (by positivity)

theorem frozenEnd : FrozenEnd := by
  intro P hS a ha
  have hQ : ∀ k, 0 < k → Setting { P with kE := k } := fun k hk =>
    ⟨hS.gamma_pos, hS.sEE_pos, hS.det_pos, hS.vA_pos, hS.vB_pos, hS.r_sq, hS.kA_pos, hk⟩
  refine tendsto_atTop_mono' atTop ?_ (tendsto_aOne (cb_pos hS) hS.vB_pos)
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (gapBound _ (hQ k hk)).2 (a k) (ha k hk)

end Third

theorem proof : Standalone.M7FineCostSandwich.statement :=
  ⟨sandwich, gapBound, uncorrelated, gap, effectiveRate, bandRatio, smallEtfRate, frozenEnd⟩

end

end Novel.M7FineCostSandwichProof

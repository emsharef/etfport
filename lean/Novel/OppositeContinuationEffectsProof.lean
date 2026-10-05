import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Standalone.OppositeContinuationEffects
import Novel.M3FiniteContinuationProof

/-!
# Proof of claim 012: opposite continuation effects in M3

This proof uses claim 011's machine-checked results (attainment `Vmax`, `V_neg`, the class and CE
orders) by importing its proof module (`depends_on: [11]`; Q-04). Every certainty-equivalent bound
comes from one of three facts about the two-state criterion `Φ = -(e^{-20 W₊} + e^{-20 W₋})/2`
(`W₀⁻ = 1`):

* a feasible policy with both terminal wealths at least `L` gives `CE ≥ L`;
* if every feasible policy has mean terminal wealth at most `B`, then `CE ≤ B` (convexity of
  `exp`, the paper's AM-GM step);
* a strict bound `CE < c` follows from `Φ < -e^{-20c}` on the whole policy set.

The ETF-only-at-both-reviews bound uses `exp x ≥ 1 + x` and `e > 2` in place of the paper's
derivative sign of `f`.
-/

namespace Novel.OppositeContinuationEffectsProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M3FiniteContinuation
  Standalone.OppositeContinuationEffects Novel.M3FiniteContinuationProof

variable {bA bE sA sE : ℝ}

/-! ### The instance -/

/-- The gross returns: `(3/2, 1/2)` under `θ₊` and `(1/2, 3/2)` under `θ₋`, in both quarters. -/
noncomputable def gr : Bool → Inst 1 1 → ℝ
  | true => Sum.elim (fun _ => 3 / 2) (fun _ => 1 / 2)
  | false => Sum.elim (fun _ => 1 / 2) (fun _ => 3 / 2)

lemma gross_eq (t : Bool) (s : Fin 1) (i : Inst 1 1) :
    1 + ret (ocInst bA bE sA sE).D ((ocInst bA bE sA sE).par t) s i = gr t i := by
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> cases t <;>
    simp [ret, ocInst, ocData, ocPar, gr, Matrix.vecHead, Matrix.vecTail] <;> norm_num

lemma W0_oc : W0 (ocInst bA bE sA sE).D = 1 := by
  simp [W0, ocInst, ocData]

lemma setting (hb : InBox bA bE sA sE) : M3Setting (ocInst bA bE sA sE) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  refine ⟨by norm_num [ocInst], fun s => by simp [ocInst, ocData], by simp [ocInst, ocData],
    fun t => by norm_num [ocInst], by norm_num [ocInst], fun i => ?_, fun i => by simp [ocInst, ocData],
    by norm_num [ocInst, ocData], by rw [W0_oc]; norm_num, fun t s i => ?_⟩
  · rcases i with k | k <;> simp [ocInst, ocData] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rw [gross_eq]
    rcases i with k | k <;> cases t <;> norm_num [gr]

lemma obs_ne : obs (ocInst bA bE sA sE) true (0 : Fin 1) ≠ obs (ocInst bA bE sA sE) false 0 := by
  intro h
  have := congrFun (congrArg Prod.snd h) (Sum.inl 0)
  have e1 := gross_eq (bA := bA) (bE := bE) (sA := sA) (sE := sE) true 0 (Sum.inl 0)
  have e2 := gross_eq (bA := bA) (bE := bE) (sA := sA) (sE := sE) false 0 (Sum.inl 0)
  simp only [obs] at this
  simp only [gr, Sum.elim_inl] at e1 e2
  linarith

/-- `Φ` on this instance: the two-state average of `-exp(-20 W₂)`. -/
lemma Phi_oc (π : Policy (ocInst bA bE sA sE)) :
    Phi (ocInst bA bE sA sE) π
      = -(Real.exp (-20 * W2 (ocInst bA bE sA sE) π true 0 0)
          + Real.exp (-20 * W2 (ocInst bA bE sA sE) π false 0 0)) / 2 := by
  simp only [Phi, U, W0_oc, div_one, Fintype.sum_bool, Fin.sum_univ_one]
  simp [ocInst, ocData]
  ring

/-! ### Three certainty-equivalent bounds -/

section CEBounds

variable (hb : InBox bA bE sA sE)
include hb

omit hb in
lemma CE_of_V (d r : Cls) :
    CE (ocInst bA bE sA sE) d r = -(1 / 20) * Real.log (-V (ocInst bA bE sA sE) d r) := rfl

lemma CE_ge {d r : Cls} {L : ℝ} {π : Policy (ocInst bA bE sA sE)}
    (hπ : π ∈ Pol (ocInst bA bE sA sE) d r) (h1 : L ≤ W2 (ocInst bA bE sA sE) π true 0 0)
    (h2 : L ≤ W2 (ocInst bA bE sA sE) π false 0 0) : L ≤ CE (ocInst bA bE sA sE) d r := by
  have hS := setting hb
  obtain ⟨π', _, hmax, hV⟩ := Vmax hS d r
  have hVn := V_neg hS d r
  have hle : Phi (ocInst bA bE sA sE) π ≤ V (ocInst bA bE sA sE) d r := by rw [← hV]; exact hmax hπ
  rw [Phi_oc] at hle
  have e1 : Real.exp (-20 * W2 (ocInst bA bE sA sE) π true 0 0) ≤ Real.exp (-20 * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-20 * W2 (ocInst bA bE sA sE) π false 0 0) ≤ Real.exp (-20 * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hneg : -V (ocInst bA bE sA sE) d r ≤ Real.exp (-20 * L) := by linarith
  have hlog := Real.log_le_log (by linarith) hneg
  rw [Real.log_exp] at hlog
  rw [CE_of_V]
  linarith

omit hb in
lemma exp_mid (x y : ℝ) : Real.exp ((x + y) / 2) ≤ (Real.exp x + Real.exp y) / 2 := by
  have := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  rw [show (x + y) / 2 = 1 / 2 * x + 1 / 2 * y by ring]
  linarith

omit hb in
/-- `Φ` is at most `-exp(-20 × mean terminal wealth)`. -/
lemma Phi_le_mean (π : Policy (ocInst bA bE sA sE)) :
    Phi (ocInst bA bE sA sE) π ≤ -Real.exp (-20 * ((W2 (ocInst bA bE sA sE) π true 0 0
      + W2 (ocInst bA bE sA sE) π false 0 0) / 2)) := by
  rw [Phi_oc]
  have := exp_mid (-20 * W2 (ocInst bA bE sA sE) π true 0 0) (-20 * W2 (ocInst bA bE sA sE) π false 0 0)
  rw [show (-20 * W2 (ocInst bA bE sA sE) π true 0 0 + -20 * W2 (ocInst bA bE sA sE) π false 0 0) / 2
    = -20 * ((W2 (ocInst bA bE sA sE) π true 0 0 + W2 (ocInst bA bE sA sE) π false 0 0) / 2) by ring]
    at this
  linarith

lemma CE_le {d r : Cls} {B : ℝ}
    (hB : ∀ π ∈ Pol (ocInst bA bE sA sE) d r,
      (W2 (ocInst bA bE sA sE) π true 0 0 + W2 (ocInst bA bE sA sE) π false 0 0) / 2 ≤ B) :
    CE (ocInst bA bE sA sE) d r ≤ B := by
  have hS := setting hb
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  have h1 := Phi_le_mean π
  have h2 : Real.exp (-20 * B) ≤ Real.exp (-20 * ((W2 (ocInst bA bE sA sE) π true 0 0
      + W2 (ocInst bA bE sA sE) π false 0 0) / 2)) := Real.exp_le_exp.mpr (by linarith [hB π hπ])
  have hneg : Real.exp (-20 * B) ≤ -V (ocInst bA bE sA sE) d r := by rw [← hV]; linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hneg
  rw [Real.log_exp] at hlog
  rw [CE_of_V]
  linarith

lemma CE_lt {d r : Cls} {c : ℝ}
    (hc : ∀ π ∈ Pol (ocInst bA bE sA sE) d r, Phi (ocInst bA bE sA sE) π < -Real.exp (-20 * c)) :
    CE (ocInst bA bE sA sE) d r < c := by
  have hS := setting hb
  obtain ⟨π, hπ, _, hV⟩ := Vmax hS d r
  have hneg : Real.exp (-20 * c) < -V (ocInst bA bE sA sE) d r := by rw [← hV]; linarith [hc π hπ]
  have hlog := Real.log_lt_log (Real.exp_pos _) hneg
  rw [Real.log_exp] at hlog
  rw [CE_of_V]
  linarith

end CEBounds

/-! ### Wealth formulas -/

section Wealth

variable (bA bE sA sE)

/-- Shorthand for the instance. -/
noncomputable abbrev Q : M3 1 2 (Fin 1) Bool := ocInst bA bE sA sE

lemma sum_inst1 (f : Inst 1 1 → ℝ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

lemma x0_oc : (Q bA bE sA sE).D.x0 = 0 := rfl

lemma obs_gross (t : Bool) (i : Inst 1 1) :
    1 + ((obsY (Q bA bE sA sE) t 0 : Yset (Q bA bE sA sE)) : Obs 1 2).2 i = gr t i :=
  gross_eq t 0 i

variable {bA bE sA sE}

lemma W1m_oc (π : Policy (Q bA bE sA sE)) (t : Bool) :
    W1m (Q bA bE sA sE) π t 0
      = h1 (Q bA bE sA sE) π.1 + π.1 (Sum.inl 0) * gr t (Sum.inl 0)
        + π.1 (Sum.inr 0) * gr t (Sum.inr 0) := by
  rw [W1m_eq, sum_inst1, gross_eq, gross_eq, x0_oc]
  simp only [Pi.zero_apply, zero_add]
  ring

lemma W2_oc (π : Policy (Q bA bE sA sE)) (t : Bool) :
    W2 (Q bA bE sA sE) π t 0 0
      = (h1 (Q bA bE sA sE) π.1 - ∑ i, π.2 (obsY (Q bA bE sA sE) t 0) i
          - cost (Q bA bE sA sE).D (π.2 (obsY (Q bA bE sA sE) t 0)))
        + (gr t (Sum.inl 0) * π.1 (Sum.inl 0) + π.2 (obsY (Q bA bE sA sE) t 0) (Sum.inl 0))
            * gr t (Sum.inl 0)
        + (gr t (Sum.inr 0) * π.1 (Sum.inr 0) + π.2 (obsY (Q bA bE sA sE) t 0) (Sum.inr 0))
            * gr t (Sum.inr 0) := by
  rw [W2_eq]
  simp only [sum_inst1, x1, x0_oc, Pi.zero_apply, zero_add]
  have e1 := obs_gross bA bE sA sE t (Sum.inl 0)
  have e2 := obs_gross bA bE sA sE t (Sum.inr 0)
  simp only [obsY] at e1 e2
  rw [e1, e2, gross_eq, gross_eq]
  ring

lemma root_budget (hb : InBox bA bE sA sE) {d r : Cls} {π : Policy (Q bA bE sA sE)}
    (hπ : π ∈ Pol (Q bA bE sA sE) d r) :
    0 ≤ π.1 (Sum.inl 0) ∧ 0 ≤ π.1 (Sum.inr 0) ∧ 0 ≤ h1 (Q bA bE sA sE) π.1 ∧
      π.1 (Sum.inl 0) + π.1 (Sum.inr 0) + h1 (Q bA bE sA sE) π.1 ≤ 1 := by
  have hS := setting hb
  have hrw := root_wealth (P := Q bA bE sA sE) π.1
  have hc := cost_nonneg (Q bA bE sA sE) (rates_nonneg hS) π.1
  rw [sum_inst1, W0_oc, x0_oc] at hrw
  simp only [Pi.zero_apply, zero_add] at hrw
  have ha := hπ.1.1 (Sum.inl 0)
  have hp := hπ.1.1 (Sum.inr 0)
  simp only [x0_oc, Pi.zero_apply, zero_add] at ha hp
  exact ⟨ha, hp, hπ.1.2.1, by linarith⟩

/-- `W₂ ≤ M W₁⁻` when every second-quarter gross return is at most `M ≥ 1`. -/
lemma W2_le_W1m (hb : InBox bA bE sA sE) {d r : Cls} {π : Policy (Q bA bE sA sE)}
    (hπ : π ∈ Pol (Q bA bE sA sE) d r) (t : Bool) {M : ℝ} (hM1 : 1 ≤ M)
    (hM : ∀ i, gr t i ≤ M) : W2 (Q bA bE sA sE) π t 0 0 ≤ M * W1m (Q bA bE sA sE) π t 0 := by
  have hS := setting hb
  have hnode : Feas1 (Q bA bE sA sE) r (x1 (Q bA bE sA sE) (obs (Q bA bE sA sE) t 0) π.1)
      (h1 (Q bA bE sA sE) π.1) (π.2 (obsY (Q bA bE sA sE) t 0)) := hπ.2 (obsY _ t 0)
  have hc1 := cost_nonneg (Q bA bE sA sE) (rates_nonneg hS) (π.2 (obsY _ t 0))
  have hpw := post_wealth (P := Q bA bE sA sE) (x1 (Q bA bE sA sE) (obs (Q bA bE sA sE) t 0) π.1)
    (h1 (Q bA bE sA sE) π.1) (π.2 (obsY _ t 0))
  have hml := marked_le hnode.2.1 hnode.1 hM1 (g := fun i => 1 + ret (Q bA bE sA sE).D
    ((Q bA bE sA sE).par t) 0 i) (fun i => by rw [gross_eq]; exact hM i)
  rw [W2_eq]
  have hle : (h1 (Q bA bE sA sE) π.1 - ∑ i, π.2 (obsY _ t 0) i - cost (Q bA bE sA sE).D (π.2 (obsY _ t 0)))
      + ∑ i, (x1 (Q bA bE sA sE) (obs (Q bA bE sA sE) t 0) π.1 i + π.2 (obsY _ t 0) i)
      ≤ W1m (Q bA bE sA sE) π t 0 := by
    simp only [W1m]; linarith
  calc _ ≤ M * ((h1 (Q bA bE sA sE) π.1 - ∑ i, π.2 (obsY _ t 0) i
          - cost (Q bA bE sA sE).D (π.2 (obsY _ t 0)))
        + ∑ i, (x1 (Q bA bE sA sE) (obs (Q bA bE sA sE) t 0) π.1 i + π.2 (obsY _ t 0) i)) := hml
    _ ≤ M * W1m (Q bA bE sA sE) π t 0 := mul_le_mul_of_nonneg_left hle (by linarith)

end Wealth

/-! ### Observations and costs -/

section Policies

lemma gr_tA : gr true (Sum.inl 0) = 3 / 2 := rfl
lemma gr_tE : gr true (Sum.inr 0) = 1 / 2 := rfl
lemma gr_fA : gr false (Sum.inl 0) = 1 / 2 := rfl
lemma gr_fE : gr false (Sum.inr 0) = 3 / 2 := rfl

lemma obsA (t : Bool) :
    ((obsY (Q bA bE sA sE) t 0 : Yset (Q bA bE sA sE)) : Obs 1 2).2 (Sum.inl 0)
      = if t then 1 / 2 else -1 / 2 := by
  have := obs_gross bA bE sA sE t (Sum.inl 0)
  cases t <;> simp only [gr, Sum.elim_inl] at this <;> simp <;> linarith

lemma yset_eq (y : Yset (Q bA bE sA sE)) : ∃ t, y = obsY (Q bA bE sA sE) t 0 := by
  obtain ⟨t, s, h⟩ := obs_mem y
  obtain rfl : s = 0 := Subsingleton.elim _ _
  exact ⟨t, Subtype.ext h.symm⟩

lemma cost_oc (u : Inst 1 1 → ℝ) :
    cost (Q bA bE sA sE).D u = bA * max (u (Sum.inl 0)) 0 + sA * max (-u (Sum.inl 0)) 0
      + (bE * max (u (Sum.inr 0)) 0 + sE * max (-u (Sum.inr 0)) 0) := by
  simp [cost, ocInst, ocData]

lemma h1_zero : h1 (Q bA bE sA sE) (0 : Inst 1 1 → ℝ) = 1 := by
  simp only [h1, cost_zero]
  simp [ocInst, ocData]

lemma x1_zero (y : Obs 1 2) : x1 (Q bA bE sA sE) y 0 = 0 := by
  funext i; simp [x1, x0_oc]

/-- Hold everything in cash at both reviews. -/
noncomputable def cashPol : Policy (Q bA bE sA sE) := (0, fun _ => 0)

lemma cashPol_mem (d r : Cls) :
    (cashPol : Policy (Q bA bE sA sE)) ∈ Pol (Q bA bE sA sE) d r := by
  refine ⟨feas_zero d (fun i => le_rfl) (by norm_num [ocInst, ocData]), fun y => ?_⟩
  show Feas1 _ r (x1 _ (y : Obs 1 2) (0 : Inst 1 1 → ℝ)) (h1 _ (0 : Inst 1 1 → ℝ)) 0
  rw [x1_zero, h1_zero]
  exact feas_zero r (fun i => le_rfl) zero_le_one

lemma cashPol_W2 (t : Bool) : W2 (Q bA bE sA sE) cashPol t 0 0 = 1 := by
  rw [W2_oc]
  show h1 _ (0 : Inst 1 1 → ℝ) - _ - cost _ (0 : Inst 1 1 → ℝ) + _ + _ = 1
  rw [h1_zero, cost_zero]
  simp [cashPol]

/-- The full-root policy with future ETF adjustment: root `(7/15, 8/15)/(1 + 1/100)`. -/
noncomputable def aS : ℝ := 7 / 15 / (101 / 100)
noncomputable def pS : ℝ := 8 / 15 / (101 / 100)

noncomputable def rootFE : Inst 1 1 → ℝ := Sum.elim (fun _ => aS) (fun _ => pS)

variable (bA bE sA sE) in
noncomputable def uFE (y : Yset (Q bA bE sA sE)) : Inst 1 1 → ℝ :=
  if (y : Obs 1 2).2 (Sum.inl 0) = 1 / 2 then Sum.elim (fun _ => 0) (fun _ => -(pS / 2)) else 0

variable (bA bE sA sE) in
noncomputable def polFE : Policy (Q bA bE sA sE) := (rootFE, uFE bA bE sA sE)

lemma aS_pos : 0 < aS := by norm_num [aS]
lemma pS_pos : 0 < pS := by norm_num [pS]

lemma h1_FE : h1 (Q bA bE sA sE) rootFE = 1 - aS - pS - bA * aS - bE * pS := by
  simp only [h1, rootFE, cost_oc, sum_inst1, Sum.elim_inl, Sum.elim_inr]
  rw [max_eq_left aS_pos.le, max_eq_right (by linarith [aS_pos]), max_eq_left pS_pos.le,
    max_eq_right (by linarith [pS_pos])]
  simp [ocInst, ocData]
  ring

lemma uFE_true : uFE bA bE sA sE (obsY (Q bA bE sA sE) true 0)
    = Sum.elim (fun _ => 0) (fun _ => -(pS / 2)) := by
  simp [uFE, obsA]

lemma uFE_false : uFE bA bE sA sE (obsY (Q bA bE sA sE) false 0) = 0 := by
  simp only [uFE, obsA]; norm_num

lemma x1_obs (t : Bool) (u : Inst 1 1 → ℝ) (i : Inst 1 1) :
    x1 (Q bA bE sA sE) (obsY (Q bA bE sA sE) t 0 : Obs 1 2) u i = gr t i * u i := by
  simp only [x1, x0_oc, Pi.zero_apply, zero_add, obs_gross]

lemma polFE_mem (hb : InBox bA bE sA sE) : polFE bA bE sA sE ∈ Pol (Q bA bE sA sE) .F .E := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  have hh := h1_FE (bA := bA) (bE := bE) (sA := sA) (sE := sE)
  have hh0 : 0 ≤ h1 (Q bA bE sA sE) rootFE := by
    rw [hh]; norm_num [aS, pS]; nlinarith
  refine ⟨⟨fun i => ?_, hh0, trivial⟩, fun y => ?_⟩
  · rcases i with k | k <;> simp [polFE, rootFE, x0_oc, aS_pos.le, pS_pos.le]
  · obtain ⟨t, rfl⟩ := yset_eq y
    show Feas1 _ .E (x1 _ (obsY (Q bA bE sA sE) t 0 : Obs 1 2) rootFE) (h1 _ rootFE)
      (uFE bA bE sA sE (obsY (Q bA bE sA sE) t 0))
    cases t
    · rw [uFE_false]
      refine feas_zero .E (fun i => ?_) hh0
      rw [x1_obs]
      rcases i with k | k <;> simp [rootFE, gr, aS_pos.le, pS_pos.le]
    · rw [uFE_true]
      refine ⟨fun i => ?_, ?_, rfl⟩
      · rw [x1_obs]
        rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
        · norm_num [rootFE, gr]; linarith [aS_pos]
        · norm_num [rootFE, gr]; linarith
      · rw [cost_oc, sum_inst1, hh]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [max_self, neg_zero, max_self, max_eq_right (by linarith [pS_pos]),
          max_eq_left (by linarith [pS_pos])]
        norm_num [aS, pS]
        nlinarith

lemma polFE_W2 (hb : InBox bA bE sA sE) (t : Bool) :
    657 / 505 ≤ W2 (Q bA bE sA sE) (polFE bA bE sA sE) t 0 0 := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  rw [W2_oc]
  show 657 / 505 ≤ h1 _ rootFE - _ - _ + _ + _
  rw [h1_FE]
  cases t
  · show 657 / 505 ≤ _ - ∑ i, uFE bA bE sA sE (obsY (Q bA bE sA sE) false 0) i
      - cost _ (uFE bA bE sA sE (obsY (Q bA bE sA sE) false 0))
      + (gr false (Sum.inl 0) * rootFE (Sum.inl 0) + uFE bA bE sA sE (obsY _ false 0) (Sum.inl 0))
        * gr false (Sum.inl 0)
      + (gr false (Sum.inr 0) * rootFE (Sum.inr 0) + uFE bA bE sA sE (obsY _ false 0) (Sum.inr 0))
        * gr false (Sum.inr 0)
    rw [uFE_false, cost_zero]
    simp only [rootFE, gr_fA, gr_fE, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, sum_const_zero]
    norm_num [aS, pS]
    nlinarith
  · show 657 / 505 ≤ _ - ∑ i, uFE bA bE sA sE (obsY (Q bA bE sA sE) true 0) i
      - cost _ (uFE bA bE sA sE (obsY (Q bA bE sA sE) true 0))
      + (gr true (Sum.inl 0) * rootFE (Sum.inl 0) + uFE bA bE sA sE (obsY _ true 0) (Sum.inl 0))
        * gr true (Sum.inl 0)
      + (gr true (Sum.inr 0) * rootFE (Sum.inr 0) + uFE bA bE sA sE (obsY _ true 0) (Sum.inr 0))
        * gr true (Sum.inr 0)
    rw [uFE_true, cost_oc, sum_inst1]
    simp only [rootFE, gr_tA, gr_tE, Sum.elim_inl, Sum.elim_inr]
    rw [max_self, neg_zero, max_self, max_eq_right (by linarith [pS_pos]),
      max_eq_left (by linarith [pS_pos])]
    norm_num [aS, pS]
    nlinarith

variable (bA bE sA sE) in
/-- The ETF-only-root policy: cash at the root, then buy the observed winner. -/
noncomputable def uEF (y : Yset (Q bA bE sA sE)) : Inst 1 1 → ℝ :=
  if (y : Obs 1 2).2 (Sum.inl 0) = 1 / 2 then Sum.elim (fun _ => 1 / (1 + bA)) (fun _ => 0)
  else Sum.elim (fun _ => 0) (fun _ => 1 / (1 + bE))

variable (bA bE sA sE) in
noncomputable def polEF : Policy (Q bA bE sA sE) := (0, uEF bA bE sA sE)

lemma uEF_true : uEF bA bE sA sE (obsY (Q bA bE sA sE) true 0)
    = Sum.elim (fun _ => 1 / (1 + bA)) (fun _ => 0) := by simp [uEF, obsA]

lemma uEF_false : uEF bA bE sA sE (obsY (Q bA bE sA sE) false 0)
    = Sum.elim (fun _ => 0) (fun _ => 1 / (1 + bE)) := by simp only [uEF, obsA]; norm_num

/-- Spending all cash on one fund at rate `b`: holding `1/(1+b)`, zero cash left. -/
lemma buy_all {b : ℝ} (hb : 0 ≤ b) : 1 - 1 / (1 + b) - b * (1 / (1 + b)) = 0 := by
  field_simp
  ring

lemma polEF_mem (hb : InBox bA bE sA sE) : polEF bA bE sA sE ∈ Pol (Q bA bE sA sE) .E .F := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  refine ⟨feas_zero .E (fun i => le_rfl) (by norm_num [ocInst, ocData]), fun y => ?_⟩
  obtain ⟨t, rfl⟩ := yset_eq y
  show Feas1 _ .F (x1 _ (obsY (Q bA bE sA sE) t 0 : Obs 1 2) (0 : Inst 1 1 → ℝ))
    (h1 _ (0 : Inst 1 1 → ℝ)) (uEF bA bE sA sE (obsY (Q bA bE sA sE) t 0))
  rw [x1_zero, h1_zero]
  have hA : 0 < 1 / (1 + bA) := by positivity
  have hE : 0 < 1 / (1 + bE) := by positivity
  cases t
  · rw [uEF_false]
    refine ⟨fun i => ?_, ?_, trivial⟩
    · rcases i with k | k
      · simp
      · simp; positivity
    · rw [cost_oc, sum_inst1]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
      have := buy_all h3'
      linarith
  · rw [uEF_true]
    refine ⟨fun i => ?_, ?_, trivial⟩
    · rcases i with k | k
      · simp; positivity
      · simp
    · rw [cost_oc, sum_inst1]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
      have := buy_all h1'
      linarith

lemma polEF_W2 (hb : InBox bA bE sA sE) (t : Bool) :
    W2 (Q bA bE sA sE) (polEF bA bE sA sE) t 0 0
      = if t then 3 / 2 * (1 / (1 + bA)) else 3 / 2 * (1 / (1 + bE)) := by
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hb
  have hA : 0 < 1 / (1 + bA) := by positivity
  have hE : 0 < 1 / (1 + bE) := by positivity
  rw [W2_oc]
  show h1 _ (0 : Inst 1 1 → ℝ) - _ - _ + _ + _ = _
  rw [h1_zero]
  cases t
  · show 1 - ∑ i, uEF bA bE sA sE (obsY (Q bA bE sA sE) false 0) i
      - cost _ (uEF bA bE sA sE (obsY (Q bA bE sA sE) false 0))
      + (gr false (Sum.inl 0) * (0 : Inst 1 1 → ℝ) (Sum.inl 0)
          + uEF bA bE sA sE (obsY _ false 0) (Sum.inl 0)) * gr false (Sum.inl 0)
      + (gr false (Sum.inr 0) * (0 : Inst 1 1 → ℝ) (Sum.inr 0)
          + uEF bA bE sA sE (obsY _ false 0) (Sum.inr 0)) * gr false (Sum.inr 0) = _
    rw [uEF_false, cost_oc, sum_inst1]
    simp only [Sum.elim_inl, Sum.elim_inr, gr_fA, gr_fE, Pi.zero_apply, mul_zero, zero_add]
    rw [max_self, neg_zero, max_self, max_eq_left hE.le, max_eq_right (by linarith)]
    have := buy_all h3'
    simp only [Bool.false_eq_true, ↓reduceIte]
    linarith
  · show 1 - ∑ i, uEF bA bE sA sE (obsY (Q bA bE sA sE) true 0) i
      - cost _ (uEF bA bE sA sE (obsY (Q bA bE sA sE) true 0))
      + (gr true (Sum.inl 0) * (0 : Inst 1 1 → ℝ) (Sum.inl 0)
          + uEF bA bE sA sE (obsY _ true 0) (Sum.inl 0)) * gr true (Sum.inl 0)
      + (gr true (Sum.inr 0) * (0 : Inst 1 1 → ℝ) (Sum.inr 0)
          + uEF bA bE sA sE (obsY _ true 0) (Sum.inr 0)) * gr true (Sum.inr 0) = _
    rw [uEF_true, cost_oc, sum_inst1]
    simp only [Sum.elim_inl, Sum.elim_inr, gr_tA, gr_tE, Pi.zero_apply, mul_zero, zero_add]
    rw [max_self, neg_zero, max_self, max_eq_left hA.le, max_eq_right (by linarith)]
    have := buy_all h1'
    simp only [↓reduceIte]
    linarith

end Policies

/-! ### The bounds -/

section Main

lemma exp_facts : 11 * Real.exp (-30) ≤ Real.exp (-20) ∧ 2 * Real.exp (-21) < Real.exp (-20) := by
  have h10 : 11 ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have h1 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have e1 : Real.exp (-20) = Real.exp (-30) * Real.exp 10 := by rw [← Real.exp_add]; norm_num
  have e2 : Real.exp (-20) = Real.exp (-21) * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have p30 := Real.exp_pos (-30)
  have p21 := Real.exp_pos (-21)
  constructor <;> nlinarith

/-- ETF-only trading at both reviews: `Φ < -e^{-21}` for every policy, so `CE_{E,E} < 21/20`. -/
lemma Phi_EE (hb : InBox bA bE sA sE) {π : Policy (Q bA bE sA sE)}
    (hπ : π ∈ Pol (Q bA bE sA sE) .E .E) : Phi (Q bA bE sA sE) π < -Real.exp (-21) := by
  have hS := setting hb
  obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hb hπ
  have hA : π.1 (Sum.inl 0) = 0 := hπ.1.2.2
  set p := π.1 (Sum.inr 0)
  set h := h1 (Q bA bE sA sE) π.1
  -- θ₊: terminal wealth at most 1 - p/2
  have hnode : Feas1 (Q bA bE sA sE) .E (x1 (Q bA bE sA sE) (obsY (Q bA bE sA sE) true 0 : Obs 1 2) π.1)
      h (π.2 (obsY (Q bA bE sA sE) true 0)) := hπ.2 _
  have huA : π.2 (obsY (Q bA bE sA sE) true 0) (Sum.inl 0) = 0 := hnode.2.2
  have huE := hnode.1 (Sum.inr 0)
  rw [x1_obs, gr_tE] at huE
  have hc1 := cost_nonneg (Q bA bE sA sE) (rates_nonneg hS) (π.2 (obsY (Q bA bE sA sE) true 0))
  have hWp : W2 (Q bA bE sA sE) π true 0 0 ≤ 1 - p / 2 := by
    rw [W2_oc, sum_inst1, gr_tA, gr_tE, huA, hA]
    nlinarith
  -- θ₋: terminal wealth at most 3/2 + 3p/4
  have hWm : W2 (Q bA bE sA sE) π false 0 0 ≤ 3 / 2 + 3 * p / 4 := by
    have := W2_le_W1m hb hπ false (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    rw [W1m_oc, gr_fA, gr_fE, hA] at this
    nlinarith
  -- exponential bounds
  obtain ⟨hf1, hf2⟩ := exp_facts
  have e1 : Real.exp (-20 * (1 - p / 2)) = Real.exp (-20) * Real.exp (10 * p) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-20 * (3 / 2 + 3 * p / 4)) = Real.exp (-30) * Real.exp (-(15 * p)) := by
    rw [← Real.exp_add]; ring_nf
  have b1 := Real.add_one_le_exp (10 * p)
  have b2 := Real.add_one_le_exp (-(15 * p))
  have m1 : Real.exp (-20 * (1 - p / 2)) ≤ Real.exp (-20 * W2 (Q bA bE sA sE) π true 0 0) :=
    Real.exp_le_exp.mpr (by linarith)
  have m2 : Real.exp (-20 * (3 / 2 + 3 * p / 4)) ≤ Real.exp (-20 * W2 (Q bA bE sA sE) π false 0 0) :=
    Real.exp_le_exp.mpr (by linarith)
  have p20 := Real.exp_pos (-20)
  have p30 := Real.exp_pos (-30)
  have hsum : Real.exp (-20) < Real.exp (-20 * (1 - p / 2)) + Real.exp (-20 * (3 / 2 + 3 * p / 4)) := by
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left b1 p20.le, mul_le_mul_of_nonneg_left b2 p30.le,
      mul_nonneg hp0 (by linarith : (0 : ℝ) ≤ 10 * Real.exp (-20) - 15 * Real.exp (-30))]
  rw [Phi_oc]
  linarith

lemma bounds (hb : InBox bA bE sA sE) :
    let P := ocInst bA bE sA sE
    0 ≤ Delta P .N ∧ Delta P .N ≤ 1 / 4 ∧ 507 / 2020 < Delta P .E ∧
    0 ≤ Delta P .F ∧ Delta P .F ≤ 3 / 202 ∧
    1 / 1010 < Delta P .E - Delta P .N ∧ Delta P .F - Delta P .E < -477 / 2020 := by
  intro P
  have hS := setting hb
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := id hb
  have hcomp := classComparison hS
  -- future no trade
  have hFN : CE P .F .N ≤ 5 / 4 := CE_le hb fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ hπ
    have z1 : π.2 (obsY (Q bA bE sA sE) true 0) = 0 := (hπ.2 _).2.2
    have z2 : π.2 (obsY (Q bA bE sA sE) false 0) = 0 := (hπ.2 _).2.2
    rw [W2_oc, W2_oc, z1, z2, cost_zero]
    simp only [Pi.zero_apply, sum_const_zero, gr_tA, gr_tE, gr_fA, gr_fE]
    nlinarith
  have hEN : 1 ≤ CE P .E .N := CE_ge ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ (cashPol_mem .E .N)
    (by rw [cashPol_W2]) (by rw [cashPol_W2])
  -- future ETF-only trading
  have hFE : 657 / 505 ≤ CE P .F .E := CE_ge ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩
    (polFE_mem ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩) (polFE_W2 ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ true)
    (polFE_W2 ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ false)
  have hEE : CE P .E .E < 21 / 20 := CE_lt ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ fun π hπ => by
    rw [show -20 * (21 / 20 : ℝ) = -21 by norm_num]
    exact Phi_EE ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ hπ
  -- future full trading
  have hFF : CE P .F .F ≤ 3 / 2 := CE_le ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ hπ
    have w1 := W2_le_W1m ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ hπ true (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    have w2 := W2_le_W1m ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ hπ false (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    rw [W1m_oc, gr_tA, gr_tE] at w1
    rw [W1m_oc, gr_fA, gr_fE] at w2
    nlinarith
  have hEF : 150 / 101 ≤ CE P .E .F := by
    have hA : 150 / 101 ≤ 3 / 2 * (1 / (1 + bA)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
    have hE : 150 / 101 ≤ 3 / 2 * (1 / (1 + bE)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]; nlinarith
    exact CE_ge ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ (polEF_mem ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩)
      (by rw [polEF_W2 ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩]; simpa using hA)
      (by rw [polEF_W2 ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩]; simpa using hE)
  have hN0 := ((hcomp.2.2 .N).1)
  have hF0 := ((hcomp.2.2 .F).1)
  simp only [Delta] at hN0 hF0 ⊢
  refine ⟨hN0, by linarith, by linarith, hF0, by linarith, by linarith, by linarith⟩

lemma activePurchase (hb : InBox bA bE sA sE) (π : Policy (Q bA bE sA sE))
    (hπ : π ∈ Pol (Q bA bE sA sE) .F .E) (hmax : IsMaxOn (Phi (Q bA bE sA sE)) (Pol (Q bA bE sA sE) .F .E) π) :
    0 < π.1 (Sum.inl 0) := by
  have hS := setting hb
  obtain ⟨ha0, _, _, _⟩ := root_budget hb hπ
  by_contra hle
  have hA : π.1 (Sum.inl 0) = 0 := le_antisymm (not_lt.mp hle) ha0
  have hπE : π ∈ Pol (Q bA bE sA sE) .E .E := ⟨⟨hπ.1.1, hπ.1.2.1, hA⟩, hπ.2⟩
  obtain ⟨πE, _, hmaxE, hVE⟩ := Vmax hS .E .E
  have hV : V (Q bA bE sA sE) .F .E ≤ V (Q bA bE sA sE) .E .E := by
    rw [V_eq_of_max hπ hmax, ← hVE]; exact hmaxE hπE
  have hCE := CE_mono hS hV
  have := (bounds hb).2.2.1
  simp only [Delta] at this
  linarith

lemma zeroFee :
    Delta (ocInst 0 0 0 0) .F = 0 ∧
    ∃ π ∈ Pol (ocInst 0 0 0 0) .F .F, IsMaxOn (Phi (ocInst 0 0 0 0)) (Pol (ocInst 0 0 0 0) .F .F) π ∧
      π.1 = 0 := by
  have hb : InBox 0 0 0 0 := by norm_num [InBox]
  have hS := setting hb
  have hcomp := classComparison hS
  have hW : ∀ t, W2 (Q 0 0 0 0) (polEF 0 0 0 0) t 0 0 = 3 / 2 := fun t => by
    rw [polEF_W2 hb]; cases t <;> norm_num
  have hmean : ∀ π ∈ Pol (Q 0 0 0 0) .F .F,
      (W2 (Q 0 0 0 0) π true 0 0 + W2 (Q 0 0 0 0) π false 0 0) / 2 ≤ 3 / 2 := fun π hπ => by
    obtain ⟨ha0, hp0, hh0, hbud⟩ := root_budget hb hπ
    have w1 := W2_le_W1m hb hπ true (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    have w2 := W2_le_W1m hb hπ false (M := 3 / 2) (by norm_num)
      (fun i => by rcases i with k | k <;> norm_num [gr])
    rw [W1m_oc, gr_tA, gr_tE] at w1
    rw [W1m_oc, gr_fA, gr_fE] at w2
    nlinarith
  have hFF : CE (ocInst 0 0 0 0) .F .F ≤ 3 / 2 := CE_le hb hmean
  have hEF : 3 / 2 ≤ CE (ocInst 0 0 0 0) .E .F :=
    CE_ge hb (polEF_mem hb) (le_of_eq (hW true).symm) (le_of_eq (hW false).symm)
  have hord := (hcomp.1 .F).2.2.2
  have hmemF : polEF 0 0 0 0 ∈ Pol (Q 0 0 0 0) .F .F := ⟨feas_EF (polEF_mem hb).1, (polEF_mem hb).2⟩
  refine ⟨by simp only [Delta]; linarith, polEF 0 0 0 0, hmemF, fun π hπ => ?_, rfl⟩
  have h1 := Phi_le_mean π
  have h2 : Real.exp (-20 * (3 / 2)) ≤ Real.exp (-20 * ((W2 (Q 0 0 0 0) π true 0 0
      + W2 (Q 0 0 0 0) π false 0 0) / 2)) := Real.exp_le_exp.mpr (by linarith [hmean π hπ])
  simp only [Set.mem_ofPred_eq]
  rw [Phi_oc (π := polEF 0 0 0 0), hW, hW]
  linarith

end Main

theorem proof : Standalone.OppositeContinuationEffects.statement :=
  ⟨fun _ _ _ _ hb => ⟨setting hb, obs_ne⟩, fun _ _ _ _ hb => bounds hb,
   fun _ _ _ _ hb π hπ hmax => activePurchase hb π hπ hmax, zeroFee⟩

end Novel.OppositeContinuationEffectsProof

import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# AX-04: the stitched time-uniform boundary (howard2021time Definitions 1-2, Theorem 1)

This mirrors ledger entry AX-04 (`ledger/AXIOMS.md`, audited ok on 2026-09-28). It is a hypothesis
structure for a cited result (AGENTS.md rule 6). The theorem is not proved here and no Novel file
re-proves it.

- `IsSubPsi` is Definition 1 (p.5). `(S_t)` and `(V_t)` are real-valued and adapted, with
  `S_0 = V_0 = 0` and `V_t ≥ 0`. For each `λ` in the domain there is a supermartingale `L_t(λ)`
  with `E L_0(λ) ≤ l₀` and `exp(λ S_t - ψ(λ) V_t) ≤ L_t(λ)` a.s. for all `t`.
- `psiG c λ = λ²/(2(1 - cλ))` on `0 ≤ λ`, `cλ < 1` (p.5; the same as `λ < 1/(c ∨ 0)`).
- `stitch` is `S_α` of equation (8) (p.7):
  `S_α(v) = √(k₁² v ℓ(v) + k₂² c² ℓ(v)²) + k₂ c ℓ(v)`, where
  `ℓ(v) = log h(log_η(v/m)) + log(l₀/α)`, `k₁ = (η^{1/4} + η^{-1/4})/√2` and `k₂ = (√η + 1)/2`.
- `StitchedBoundary` holds Theorem 1 (p.8) for a given process and parameters. Under the theorem's
  hypotheses, `P(∃ t ≥ 1 : S_t ≥ S_α(V_t ∨ m)) ≤ α`, and for `v₀ ≥ m`,
  `P(∃ t ≥ 1 : V_t ≥ v₀, S_t ≥ S_α(V_t)) ≤ Σ_{k ≥ ⌊log_η(v₀/m)⌋} α/h(k)`, which is (9).

The boundary is one-sided, as the ledger records. Two-sided use needs a union bound over `(-S_t)`,
and nothing here gives an M4 reading.

**Instance (degenerate, disclosed; genuine, not vacuous).** This is the ledger's instance.
- The process: `S_t = V_t = 0` on the one-point space with the trivial filtration.
- The parameters: `c = 0`, `l₀ = 1`, `α = 1/2`, `η = 2`, `m = 1` and `h(x) = 2^(x+1)`.
- `zero_isSubPsi` proves every premise with the constant supermartingale `L = 1`, and
  `zero_params` proves the parameter conditions.
- `stitchedBoundary_zero` proves both conclusions. The zero process never crosses, since
  `S_α(m) > 0`, and `V_t = 0 < v₀`.

It is degenerate because a faithful instance would re-derive the theorem, which rule 6 forbids.
-/

namespace Upstream.Stitched

open MeasureTheory

/-- Definition 1: `(S_t)` is `l₀`-sub-`ψ` with variance process `(V_t)`; `dom` is the domain of `λ`. -/
def IsSubPsi {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (S V : ℕ → Ω → ℝ) (ψ : ℝ → ℝ) (dom : ℝ → Prop) (l0 : ℝ) : Prop :=
  Adapted ℱ S ∧ Adapted ℱ V ∧ (∀ ω, S 0 ω = 0) ∧ (∀ ω, V 0 ω = 0) ∧ (∀ t ω, 0 ≤ V t ω) ∧
  ∀ lam, dom lam → ∃ L : ℕ → Ω → ℝ, Supermartingale L ℱ P ∧ ∫ ω, L 0 ω ∂P ≤ l0 ∧
    ∀ t, ∀ᵐ ω ∂P, Real.exp (lam * S t ω - ψ lam * V t ω) ≤ L t ω

/-- The sub-gamma function `ψ_{G,c}(λ) = λ²/(2(1 - cλ))`. -/
noncomputable def psiG (c lam : ℝ) : ℝ := lam ^ 2 / (2 * (1 - c * lam))

/-- Its domain `0 ≤ λ < 1/(c ∨ 0)`. -/
def domG (c lam : ℝ) : Prop := 0 ≤ lam ∧ c * lam < 1

/-- `ℓ(v) = log h(log_η(v/m)) + log(l₀/α)`. -/
noncomputable def ell (l0 α η m : ℝ) (h : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.log (h (Real.logb η (v / m))) + Real.log (l0 / α)

/-- The stitching function `S_α` of equation (8). -/
noncomputable def stitch (l0 c α η m : ℝ) (h : ℝ → ℝ) (v : ℝ) : ℝ :=
  let k1 := (η ^ (1 / 4 : ℝ) + η ^ (-(1 / 4) : ℝ)) / Real.sqrt 2
  let k2 := (Real.sqrt η + 1) / 2
  Real.sqrt (k1 ^ 2 * v * ell l0 α η m h v + k2 ^ 2 * c ^ 2 * ell l0 α η m h v ^ 2)
    + k2 * c * ell l0 α η m h v

/-- Theorem 1's hypotheses on the parameters. -/
def Params (l0 c α η m : ℝ) (h : ℝ → ℝ) : Prop :=
  1 ≤ l0 ∧ 0 ≤ c ∧ 0 < α ∧ α < 1 ∧ 1 < η ∧ 0 < m ∧ MonotoneOn h (Set.Ici 0) ∧
  (∀ x, 0 ≤ x → 0 < h x) ∧ Summable (fun k : ℕ => 1 / h k) ∧ ∑' k : ℕ, 1 / h k ≤ 1

/-- AX-04, Theorem 1, for a given process and parameters. -/
structure StitchedBoundary {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (S V : ℕ → Ω → ℝ) (l0 c α η m : ℝ) (h : ℝ → ℝ) : Prop where
  crossing : IsProbabilityMeasure P → Params l0 c α η m h →
    IsSubPsi P ℱ S V (psiG c) (domG c) l0 →
    P {ω | ∃ t, 1 ≤ t ∧ stitch l0 c α η m h (max (V t ω) m) ≤ S t ω} ≤ ENNReal.ofReal α
  tail : IsProbabilityMeasure P → Params l0 c α η m h →
    IsSubPsi P ℱ S V (psiG c) (domG c) l0 → ∀ v0, m ≤ v0 →
    P {ω | ∃ t, 1 ≤ t ∧ v0 ≤ V t ω ∧ stitch l0 c α η m h (V t ω) ≤ S t ω}
      ≤ ENNReal.ofReal (∑' k : ℕ, if ⌊Real.logb η (v0 / m)⌋₊ ≤ k then α / h k else 0)

/-! ### The disclosed degenerate instance -/

/-- `h(x) = 2^(x+1)`. -/
noncomputable def h2 (x : ℝ) : ℝ := (2 : ℝ) ^ (x + 1)

/-- The zero process. -/
def zeroProc : ℕ → Unit → ℝ := fun _ _ => 0

/-- The parameter conditions hold for `l₀ = 1`, `c = 0`, `α = 1/2`, `η = 2`, `m = 1`, `h = h2`. -/
theorem zero_params : Params 1 0 (1 / 2) 2 1 h2 := by
  have hs : (fun k : ℕ => 1 / h2 k) = fun k : ℕ => (1 / 2 : ℝ) * (1 / 2) ^ k := by
    funext k
    simp only [h2]
    rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast]
    field_simp
    rw [← mul_pow]; norm_num
  refine ⟨le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, ?_, fun x _ => ?_,
    ?_, ?_⟩
  · intro x _ y _ hxy
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · rw [hs]; exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · rw [hs, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

/-- Every premise of Definition 1 holds for the zero process, with `L_t(λ) = 1`. -/
theorem zero_isSubPsi :
    IsSubPsi (Measure.dirac ()) ⊥ zeroProc zeroProc (psiG 0) (domG 0) 1 := by
  refine ⟨fun _ => measurable_const, fun _ => measurable_const, fun _ => rfl,
    fun _ => rfl, fun _ _ => le_rfl, fun lam _ => ⟨fun _ _ => 1,
      (martingale_const _ _ (1 : ℝ)).supermartingale, by simp, fun t => ae_of_all _ fun ω => ?_⟩⟩
  simp [zeroProc]

lemma stitch_pos : 0 < stitch 1 0 (1 / 2) 2 1 h2 1 := by
  have hl : 0 < ell 1 (1 / 2) 2 1 h2 1 := by
    simp only [ell, div_one, Real.logb_one, h2, zero_add, Real.rpow_one]
    have : Real.log (1 / (1 / 2)) = Real.log 2 := by norm_num
    rw [this]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  simp only [stitch, mul_zero, zero_pow two_ne_zero, zero_mul, add_zero, mul_one]
  apply Real.sqrt_pos.mpr
  have hk : 0 < ((2 : ℝ) ^ (1 / 4 : ℝ) + (2 : ℝ) ^ (-(1 / 4) : ℝ)) / Real.sqrt 2 := by positivity
  positivity

/-- The instance: both conclusions of Theorem 1 hold for the zero process. -/
theorem stitchedBoundary_zero :
    StitchedBoundary (Measure.dirac ()) ⊥ zeroProc zeroProc 1 0 (1 / 2) 2 1 h2 := by
  refine ⟨fun _ _ _ => ?_, fun _ _ _ v0 hv0 => ?_⟩
  · have : {ω : Unit | ∃ t, 1 ≤ t ∧ stitch 1 0 (1 / 2) 2 1 h2 (max (zeroProc t ω) 1)
        ≤ zeroProc t ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro t _
      simp only [zeroProc, max_eq_right (zero_le_one' ℝ)]
      exact stitch_pos
    rw [this, measure_empty]; exact bot_le
  · have : {ω : Unit | ∃ t, 1 ≤ t ∧ v0 ≤ zeroProc t ω ∧ stitch 1 0 (1 / 2) 2 1 h2 (zeroProc t ω)
        ≤ zeroProc t ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro t _ hv
      simp only [zeroProc] at hv
      linarith
    rw [this, measure_empty]; exact bot_le

end Upstream.Stitched

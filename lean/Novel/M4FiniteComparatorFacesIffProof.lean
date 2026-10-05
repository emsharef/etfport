import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Standalone.M4FiniteComparatorFacesIff
import Upstream.LPVertex
import Novel.M4CurvatureCertificateProof

/-!
# Proof of claim 020: the finite comparator faces of the funded ETF class, and when they are exact

This proof imports claim 018's proof module (`depends_on: [17, 18]`; Q-04), which brings claim
017's and claim 004's with it.

* **Cells and `AX-05`.** The finiteness of `Vert(F)` and `Vert(E)` and the crude counts are
  `AX-05` part (i), the linear-programming vertex theorem. It is not proved here: it enters as the
  hypothesis structure `Upstream.LP.LPVertex` (`Upstream/LPVertex.lean`, with its disclosed
  degenerate instance). The statement's `AX05i` is that structure for every constraint system
  (`AX05i_iff`). The proof checks its premises for each cell, nonempty or empty and bounded by the
  position limits. `AX-05`'s part (ii) (attainment at an extreme point) is not used: the face
  maxima come from M4's own lexicographic selection, which is claim-specific (below).
* **Lexicographic minima.** Every compact nonempty set of holdings has a lexicographic minimum in
  M4's coordinate order, obtained by minimizing one coordinate at a time. A lexicographic minimum
  is an extreme point of any set containing it.
  - The maximizers of a function that is affine on a cell form a face of the cell.
  - So M4's plug-in selection over a finite union of cells is an extreme point of one cell. This
    also gives the face maxima.
-/

namespace Novel.M4FiniteComparatorFacesIffProof

open Matrix Finset Standalone.M2ScoreAccounting Standalone.M4FiniteComparatorFacesIff
open Standalone.M4InformationObstruction (toPar Theta4 M4Admissible thetaHat Omega pinv
  IsMoorePenrose tcrit TN errN mass Aset Cset etfSup Adv Gstar LN LexLE lexSel lexIdx wHatF vHatE
  sg zeta)
open Standalone.M4CurvatureCertificate (Aw)
open Novel.M4CurvatureCertificateProof (R0 score_split score_shift Aw_comb Aw_sub cont_score
  compact_F compact_E E_sub_F w0_mem_E)
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Polyhedra -/

section Poly

variable {ι Λ : Type} [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ)

/-- The polyhedron `{x : g_l'x ≤ h_l for all l}`. -/
def poly : Set (ι → ℝ) := {x | ∀ l, g l ⬝ᵥ x ≤ h l}

end Poly

/-! ### Lexicographic minima in M4's coordinate order -/

section Lex

variable {n : ℕ}

lemma lexIdx_inj : Function.Injective (lexIdx : Inst 1 n → ℕ) := by
  rintro (i | i) (j | j) hij <;> simp [lexIdx] at hij
  · rw [Subsingleton.elim i j]
  · exact congrArg Sum.inr (Fin.ext hij)

lemma lexIdx_lt (i : Inst 1 n) : lexIdx i < n + 1 := by
  rcases i with i | i
  · simp [lexIdx]
  · simp [lexIdx, i.isLt]

lemma lexIdx_surj {k : ℕ} (hk : k < n + 1) : ∃ i : Inst 1 n, lexIdx i = k := by
  rcases k with _ | k
  · exact ⟨Sum.inl 0, rfl⟩
  · exact ⟨Sum.inr ⟨k, by omega⟩, rfl⟩

/-- A lexicographically smaller point contradicts `LexLE`. -/
lemma lex_not_lt {x y : Inst 1 n → ℝ} (hxy : LexLE x y) {i : Inst 1 n}
    (hag : ∀ j, lexIdx j < lexIdx i → y j = x j) (hi : y i < x i) : False := by
  rcases hxy with rfl | ⟨i', hbelow, hlt⟩
  · exact lt_irrefl _ hi
  · rcases lt_trichotomy (lexIdx i') (lexIdx i) with h | h | h
    · rw [hag i' h] at hlt; exact lt_irrefl _ hlt
    · rw [lexIdx_inj h] at hlt; linarith
    · rw [hbelow i h] at hi; exact lt_irrefl _ hi

/-- A lexicographic minimum of a set is an extreme point of it. -/
lemma lexmin_extreme {A : Set (Inst 1 n → ℝ)} {x : Inst 1 n → ℝ} (hx : x ∈ A)
    (hmin : ∀ y ∈ A, LexLE x y) : x ∈ Set.extremePoints ℝ A := by
  refine mem_extremePoints_iff_left.mpr ⟨hx, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
  by_contra hne
  have hyz : y ≠ z := by
    rintro rfl
    apply hne
    rw [← hxe, ← add_smul, hab, one_smul]
  obtain ⟨i, hi, himin⟩ := Finset.exists_min_image (Finset.univ.filter fun j => y j ≠ z j)
    lexIdx (by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hyz
      exact ⟨j, by simp [hj]⟩)
  have hiyz : y i ≠ z i := (Finset.mem_filter.mp hi).2
  have hxi : x i = a * y i + b * z i := by rw [← hxe]; simp
  have hbelow : ∀ j, lexIdx j < lexIdx i → y j = z j := by
    intro j hj
    by_contra hne'
    exact absurd (himin j (by simp [hne'])) (not_le.mpr hj)
  have hxj : ∀ j, lexIdx j < lexIdx i → x j = y j := by
    intro j hj
    have := hbelow j hj
    rw [← hxe]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← this]
    rw [← add_mul, hab, one_mul]
  have ea : a = 1 - b := by linarith
  rcases lt_or_gt_of_ne hiyz with hlt | hlt
  · have : 0 < b * (z i - y i) := mul_pos hb (by linarith)
    exact lex_not_lt (hmin y hy) (fun j hj => (hxj j hj).symm) (by rw [hxi, ea]; nlinarith)
  · have : 0 < a * (y i - z i) := mul_pos ha (by linarith)
    have eb : b = 1 - a := by linarith
    exact lex_not_lt (hmin z hz) (fun j hj => by rw [hxj j hj, hbelow j hj])
      (by rw [hxi, eb]; nlinarith)

/-- Every compact nonempty set of holdings has a lexicographic minimum. -/
lemma lexmin_exists {M : Set (Inst 1 n → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ x ∈ M, ∀ y ∈ M, LexLE x y := by
  have key : ∀ k, k ≤ n + 1 → ∃ Mk ⊆ M, IsCompact Mk ∧ Mk.Nonempty ∧ ∀ x ∈ Mk, ∀ y ∈ M,
      (∃ i, lexIdx i < k ∧ (∀ j, lexIdx j < lexIdx i → x j = y j) ∧ x i < y i) ∨
      ((∀ j, lexIdx j < k → x j = y j) ∧ y ∈ Mk) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨M, le_rfl, hM, hne, fun x _ y hy => Or.inr ⟨fun j hj => absurd hj
        (Nat.not_lt_zero _), hy⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨Mk, hsub, hc, hn, hprop⟩ := ih (by omega)
      obtain ⟨ik, hik⟩ := lexIdx_surj (n := n) (by omega : k < n + 1)
      obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hn (continuous_apply ik).continuousOn
      refine ⟨Mk ∩ {w | w ik = m ik}, fun w hw => hsub hw.1,
        hc.inter_right (isClosed_eq (continuous_apply ik) continuous_const), ⟨m, hm, rfl⟩, ?_⟩
      intro x hx y hy
      rcases hprop x hx.1 y hy with ⟨i, hi, hag, hlt⟩ | ⟨hag, hyk⟩
      · exact Or.inl ⟨i, by omega, hag, hlt⟩
      · have hmy : m ik ≤ y ik := hmin hyk
        have hxm : x ik = m ik := hx.2
        rcases lt_or_eq_of_le hmy with hlt | heq
        · exact Or.inl ⟨ik, by omega, fun j hj => hag j (by omega), by rw [hxm]; exact hlt⟩
        · refine Or.inr ⟨fun j hj => ?_, hyk, show y ik = m ik from heq.symm⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact hag j hj
          · rw [lexIdx_inj (hj.trans hik.symm), hxm, heq]
  obtain ⟨Mk, hsub, -, ⟨x, hx⟩, hprop⟩ := key (n + 1) le_rfl
  refine ⟨x, hsub hx, fun y hy => ?_⟩
  rcases hprop x hx y hy with ⟨i, -, hag, hlt⟩ | ⟨hag, -⟩
  · exact Or.inr ⟨i, hag, hlt⟩
  · exact Or.inl (funext fun j => hag j (lexIdx_lt j))

lemma lexSel_spec {M : Set (Inst 1 n → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    lexSel M ∈ M ∧ ∀ y ∈ M, LexLE (lexSel M) y :=
  Classical.epsilon_spec (lexmin_exists hM hne)

/-- The maximizers of a function affine on `K` form a face of `K`. -/
lemma face_extreme {K : Set (Inst 1 n → ℝ)} {f : (Inst 1 n → ℝ) → ℝ}
    (haff : ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a * f x + b * f y)
    {x : Inst 1 n → ℝ} (hxK : x ∈ K) (hmax : ∀ y ∈ K, f y ≤ f x)
    (hext : x ∈ Set.extremePoints ℝ {y | y ∈ K ∧ f x ≤ f y}) : x ∈ Set.extremePoints ℝ K := by
  refine mem_extremePoints_iff_left.mpr ⟨hxK, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
  have hf : f x = a * f y + b * f z := by rw [← hxe, haff y hy z hz a b ha.le hb.le hab]
  have hfy := hmax y hy
  have hfz := hmax z hz
  have hsum : (a + b) * f x = f x := by rw [hab, one_mul]
  have hy' : f x ≤ f y := by
    by_contra hlt
    have := mul_lt_mul_of_pos_left (not_le.mp hlt) ha
    have := mul_le_mul_of_nonneg_left hfz hb.le
    linarith
  have hz' : f x ≤ f z := by
    by_contra hlt
    have := mul_lt_mul_of_pos_left (not_le.mp hlt) hb
    have := mul_le_mul_of_nonneg_left hfy ha.le
    linarith
  exact (mem_extremePoints_iff_left.mp hext).2 y ⟨hy, hy'⟩ z ⟨hz, hz'⟩ ⟨a, b, ha, hb, hab, hxe⟩

/-- M4's lexicographic selection of the maximizers over a finite union of cells, each carrying an
affine objective, is an extreme point of one cell. -/
lemma lexSel_face {ι : Type} (cells : ι → Set (Inst 1 n → ℝ)) {C : Set (Inst 1 n → ℝ)}
    (hC : C = ⋃ c, cells c) (hcomp : IsCompact C) (hne : C.Nonempty)
    {f : (Inst 1 n → ℝ) → ℝ} (hcont : Continuous f)
    (haff : ∀ c, ∀ x ∈ cells c, ∀ y ∈ cells c, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a * f x + b * f y) :
    lexSel (maximizers f C) ∈ ⋃ c, Set.extremePoints ℝ (cells c) ∧
      lexSel (maximizers f C) ∈ maximizers f C := by
  obtain ⟨w, hw, hwmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  have hM : maximizers f C = C ∩ {y | f w ≤ f y} := by
    ext y
    exact ⟨fun hy => ⟨hy.1, hy.2 w hw⟩, fun hy => ⟨hy.1, fun y' hy' => (hwmax hy').trans hy.2⟩⟩
  have hMc : IsCompact (maximizers f C) := by
    rw [hM]; exact hcomp.inter_right (isClosed_le continuous_const hcont)
  obtain ⟨hxM, hxmin⟩ := lexSel_spec hMc ⟨w, hw, fun y hy => hwmax hy⟩
  set x := lexSel (maximizers f C)
  refine ⟨?_, hxM⟩
  have hxC := hxM.1
  rw [hC] at hxC
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hxC
  have hsubC : ∀ y ∈ cells c, y ∈ C := fun y hy => hC ▸ Set.mem_iUnion.mpr ⟨c, hy⟩
  refine Set.mem_iUnion.mpr ⟨c, face_extreme (haff c) hc (fun y hy => hxM.2 y (hsubC y hy)) ?_⟩
  refine lexmin_extreme ⟨hc, le_rfl⟩ fun y hy => hxmin y ⟨hsubC y hy.1, fun y' hy' => ?_⟩
  exact (hxM.2 y' hy').trans hy.2

end Lex

/-! ### Part 1: the cost-sign cells -/

section Cells

variable {n : ℕ} {S : Type} [Fintype S]

/-- The rate charged on the side of the cell: `κ⁺` for purchases, `κ⁻` for sales. -/
def ksel (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) (i : Inst 1 n) : ℝ :=
  if σ i then D.kplus i else D.kminus i

/-- The per-unit funding coefficient `1 + t_σ` on the cell. -/
def cf (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) (i : Inst 1 n) : ℝ := 1 + sg (σ i) * ksel D σ i

lemma tau_lin (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) {v : Inst 1 n → ℝ}
    (hv : ∀ i, 0 ≤ sg (σ i) * v i) : tau D v = ∑ i, sg (σ i) * ksel D σ i * v i := by
  unfold tau
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hv i
  cases hσ : σ i <;> simp only [hσ, sg, ksel, Bool.false_eq_true, ↓reduceIte] at this ⊢
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma cash_lin (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) {w : Inst 1 n → ℝ}
    (hv : ∀ i, 0 ≤ sg (σ i) * (w i - w0 D i)) :
    cash D w = k0 D - ∑ i, cf D σ i * (w i - w0 D i) := by
  rw [cash, tau_lin D σ (v := w - w0 D) hv]
  simp only [cf, Pi.sub_apply, add_mul, one_mul, Finset.sum_add_distrib]
  ring

/-- The constraint index of an `F` cell: box, sign and one funding constraint. -/
abbrev LamF (n : ℕ) := (Inst 1 n × Fin 3) ⊕ Unit

def gF (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) : LamF n → Inst 1 n → ℝ :=
  Sum.elim (fun p => if p.2 = 0 then -Pi.single p.1 1 else if p.2 = 1 then Pi.single p.1 1
    else -(sg (σ p.1) • Pi.single p.1 1)) (fun _ => cf D σ)

def hF (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) : LamF n → ℝ :=
  Sum.elim (fun p => if p.2 = 0 then 0 else if p.2 = 1 then D.wbar p.1
    else -(sg (σ p.1) * w0 D p.1)) (fun _ => k0 D + ∑ i, cf D σ i * w0 D i)

lemma sum_cf_sub (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) (w : Inst 1 n → ℝ) :
    ∑ i, cf D σ i * (w i - w0 D i) = cf D σ ⬝ᵥ w - ∑ i, cf D σ i * w0 D i := by
  simp only [mul_sub, Finset.sum_sub_distrib, dotProduct]

lemma cellF_eq (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) : cellF D σ = poly (gF D σ) (hF D σ) := by
  ext w
  constructor
  · rintro ⟨⟨hbox, hcash⟩, hsgn⟩ l
    rcases l with ⟨i, k⟩ | u
    · fin_cases k <;> simp [gF, hF, single_dotProduct]
      · exact (hbox i).1
      · exact (hbox i).2
      · have := hsgn i; linarith [mul_sub (sg (σ i)) (w i) (w0 D i)]
    · have := cash_lin D σ hsgn
      rw [sum_cf_sub] at this
      simp only [gF, hF, Sum.elim_inr]
      linarith
  · intro hw
    have hsgn : ∀ i, 0 ≤ sg (σ i) * (w i - w0 D i) := fun i => by
      have := hw (Sum.inl (i, 2)); simp [gF, hF, single_dotProduct] at this
      linarith [mul_sub (sg (σ i)) (w i) (w0 D i)]
    refine ⟨⟨fun i => ⟨?_, ?_⟩, ?_⟩, hsgn⟩
    · have := hw (Sum.inl (i, 0)); simpa [gF, hF, single_dotProduct] using this
    · have := hw (Sum.inl (i, 1)); simpa [gF, hF, single_dotProduct] using this
    · have := hw (Sum.inr ()); simp only [gF, hF, Sum.elim_inr] at this
      rw [cash_lin D σ hsgn, sum_cf_sub]; linarith

lemma poly_closed {ι Λ : Type} [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ) :
    IsClosed (poly g h) := by
  have : poly g h = ⋂ l, {x | g l ⬝ᵥ x ≤ h l} := by ext x; simp [poly]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le (continuous_const.dotProduct continuous_id)
    continuous_const

lemma poly_convex {ι Λ : Type} [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ) :
    Convex ℝ (poly g h) := by
  intro x hx y hy a b ha hb hab l
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hx l) ha
  have h2 := mul_le_mul_of_nonneg_left (hy l) hb
  have h3 : (a + b) * h l = h l := by rw [hab, one_mul]
  linarith

lemma card_LamF : Fintype.card (LamF n) = 3 * n + 4 := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

lemma card_inst : Fintype.card (Inst 1 n) = n + 1 := by simp [Fintype.card_sum]; ring

/-- The sign pattern `σ` of the ETF cell `E_ρ` (the active coordinate does not trade). -/
def sigE (ρ : Fin n → Bool) : Inst 1 n → Bool := Sum.elim (fun _ => true) ρ

lemma cellE_eq_inter (D : Data 1 n 2 S) (ρ : Fin n → Bool) :
    cellE D ρ = {w | w (Sum.inl 0) = w0 D (Sum.inl 0)} ∩ cellF D (sigE ρ) := by
  ext w
  constructor
  · rintro ⟨⟨hF, hact⟩, hsgn⟩
    have ha : w (Sum.inl 0) = w0 D (Sum.inl 0) := congrFun hact 0
    refine ⟨ha, hF, fun i => ?_⟩
    rcases i with i | j
    · rw [Subsingleton.elim i 0, ha, sub_self, mul_zero]
    · exact hsgn j
  · rintro ⟨ha, hF, hsgn⟩
    exact ⟨⟨hF, funext fun i => by rw [Subsingleton.elim i 0]; exact ha⟩, fun j => hsgn (Sum.inr j)⟩

lemma cellF_compact_convex (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) :
    IsCompact (cellF D σ) ∧ Convex ℝ (cellF D σ) := by
  rw [cellF_eq]
  refine ⟨(Novel.M4CurvatureCertificateProof.compact_F D).of_isClosed_subset (poly_closed _ _)
    (fun w hw => ?_), poly_convex _ _⟩
  rw [← cellF_eq] at hw; exact hw.1

lemma cellE_compact_convex (D : Data 1 n 2 S) (ρ : Fin n → Bool) :
    IsCompact (cellE D ρ) ∧ Convex ℝ (cellE D ρ) := by
  rw [cellE_eq_inter]
  obtain ⟨hc, hv⟩ := cellF_compact_convex D (sigE ρ)
  refine ⟨hc.inter_left (isClosed_eq (continuous_apply _) continuous_const), ?_⟩
  refine Convex.inter ?_ hv
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  rw [hx, hy, ← add_mul, hab, one_mul]

lemma F_union (D : Data 1 n 2 S) : F D = ⋃ σ, cellF D σ := by
  ext w
  refine ⟨fun hw => Set.mem_iUnion.mpr ⟨fun i => decide (w0 D i ≤ w i), hw, fun i => ?_⟩,
    fun hw => (Set.mem_iUnion.mp hw).choose_spec.1⟩
  by_cases h : w0 D i ≤ w i
  · simp [h, sg]
  · simp [h, sg]; linarith [not_le.mp h]

lemma E_union (D : Data 1 n 2 S) : E D = ⋃ ρ, cellE D ρ := by
  ext w
  refine ⟨fun hw => Set.mem_iUnion.mpr ⟨fun j => decide (w0 D (Sum.inr j) ≤ w (Sum.inr j)), hw,
    fun j => ?_⟩, fun hw => (Set.mem_iUnion.mp hw).choose_spec.1⟩
  by_cases h : w0 D (Sum.inr j) ≤ w (Sum.inr j)
  · simp [h, sg]
  · simp [h, sg]; linarith [not_le.mp h]

lemma w0_mem_cells (D : Data 1 n 2 S) (h : w0 D ∈ F D) :
    (∀ σ, w0 D ∈ cellF D σ) ∧ ∀ ρ, w0 D ∈ cellE D ρ :=
  ⟨fun σ => ⟨h, fun i => by simp⟩, fun ρ => ⟨⟨h, rfl⟩, fun j => by simp⟩⟩

/-! ETF cells in the ETF coordinates. -/

/-- The constraint index of an `E` cell in the ETF coordinates. -/
abbrev LamE (n : ℕ) := (Fin n × Fin 3) ⊕ Unit

def gE (D : Data 1 n 2 S) (ρ : Fin n → Bool) : LamE n → Fin n → ℝ :=
  Sum.elim (fun p => if p.2 = 0 then -Pi.single p.1 1 else if p.2 = 1 then Pi.single p.1 1
    else -(sg (ρ p.1) • Pi.single p.1 1)) (fun _ j => cf D (sigE ρ) (Sum.inr j))

def hE (D : Data 1 n 2 S) (ρ : Fin n → Bool) : LamE n → ℝ :=
  Sum.elim (fun p => if p.2 = 0 then 0 else if p.2 = 1 then D.wbar (Sum.inr p.1)
    else -(sg (ρ p.1) * w0 D (Sum.inr p.1)))
    (fun _ => k0 D + ∑ j, cf D (sigE ρ) (Sum.inr j) * w0 D (Sum.inr j))

/-- The holding with active part `a⁻` and ETF part `p`. -/
def emb (D : Data 1 n 2 S) (p : Fin n → ℝ) : Inst 1 n → ℝ :=
  Sum.elim (fun _ => w0 D (Sum.inl 0)) p

lemma cellE_eq (D : Data 1 n 2 S) (ρ : Fin n → Bool) :
    cellE D ρ = {w | w (Sum.inl 0) = w0 D (Sum.inl 0) ∧
      (0 ≤ w0 D (Sum.inl 0) ∧ w0 D (Sum.inl 0) ≤ D.wbar (Sum.inl 0)) ∧
      etf w ∈ poly (gE D ρ) (hE D ρ)} := by
  rw [cellE_eq_inter, cellF_eq]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ha, hw⟩
    refine ⟨ha, ?_, fun l => ?_⟩
    · have h0 := hw (Sum.inl (Sum.inl 0, 0))
      have h1 := hw (Sum.inl (Sum.inl 0, 1))
      simp [gF, hF, single_dotProduct] at h0 h1
      rw [ha] at h0 h1; exact ⟨h0, h1⟩
    · rcases l with ⟨j, k⟩ | u
      · have := hw (Sum.inl (Sum.inr j, k))
        fin_cases k <;> simpa [gF, hF, gE, hE, single_dotProduct, sigE, etf] using this
      · have := hw (Sum.inr ())
        simp only [gF, hF, gE, hE, Sum.elim_inr, dotProduct, Fintype.sum_sum_type,
          Finset.univ_unique, Finset.sum_singleton, etf] at this ⊢
        have hd : (default : Fin 1) = 0 := Subsingleton.elim _ _
        rw [hd, ha] at this
        linarith
  · rintro ⟨ha, ⟨hb0, hb1⟩, hp⟩
    refine ⟨ha, fun l => ?_⟩
    rcases l with ⟨i | j, k⟩ | u
    · rw [Subsingleton.elim i 0]
      fin_cases k <;> simp [gF, hF, single_dotProduct, ha, sigE, sg] <;> linarith
    · have := hp (Sum.inl (j, k))
      fin_cases k <;> simpa [gF, hF, gE, hE, single_dotProduct, sigE, etf] using this
    · have := hp (Sum.inr ())
      simp only [gF, hF, gE, hE, Sum.elim_inr, dotProduct, Fintype.sum_sum_type,
        Finset.univ_unique, Finset.sum_singleton, etf] at this ⊢
      have hd : (default : Fin 1) = 0 := Subsingleton.elim _ _
      rw [hd, ha]
      linarith

lemma ext_cellE_sub (D : Data 1 n 2 S) (ρ : Fin n → Bool) :
    Set.extremePoints ℝ (cellE D ρ) ⊆ emb D '' Set.extremePoints ℝ (poly (gE D ρ) (hE D ρ)) := by
  intro w hw
  have hmem := hw.1
  rw [cellE_eq] at hmem
  obtain ⟨ha, hbox, hp⟩ := hmem
  have hwe : w = emb D (etf w) := by
    funext i; rcases i with i | j
    · rw [Subsingleton.elim i 0]; exact ha
    · rfl
  have hin : ∀ p ∈ poly (gE D ρ) (hE D ρ), emb D p ∈ cellE D ρ := fun p hp' => by
    rw [cellE_eq]; exact ⟨rfl, hbox, hp'⟩
  refine ⟨etf w, mem_extremePoints_iff_left.mpr ⟨hp, fun y hy z hz hseg => ?_⟩, hwe.symm⟩
  obtain ⟨a, b, ha', hb', hab, hye⟩ := hseg
  have hseg' : w ∈ openSegment ℝ (emb D y) (emb D z) := by
    refine ⟨a, b, ha', hb', hab, ?_⟩
    funext i; rcases i with i | j
    · simp only [emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl]
      rw [← add_mul, hab, one_mul, Subsingleton.elim i 0, ha]
    · simp only [emb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr]
      have := congrFun hye j
      simpa [etf] using this
  have := (mem_extremePoints_iff_left.mp hw).2 _ (hin y hy) _ (hin z hz) hseg'
  rw [← this]; rfl

/-- The statement's `AX05i` is the Upstream structure `LPVertex` for every constraint system. -/
lemma AX05i_iff : AX05i ↔ ∀ (ι Λ : Type) [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ),
    Upstream.LP.LPVertex g h :=
  ⟨fun hA _ _ _ _ g h => ⟨hA _ _ g h⟩, fun hL _ _ _ _ g h => (hL _ _ g h).finite_card⟩

/-- `AX-05` (i) applied to a bounded polyhedron, empty or not. -/
lemma ax05_apply (hA : AX05i) {ι Λ : Type} [Fintype ι] [Fintype Λ] (g : Λ → ι → ℝ) (h : Λ → ℝ)
    (hb : Bornology.IsBounded (poly g h)) :
    (Set.extremePoints ℝ (poly g h)).Finite ∧
      (Set.extremePoints ℝ (poly g h)).ncard ≤ (Fintype.card Λ).choose (Fintype.card ι) := by
  rcases (poly g h).eq_empty_or_nonempty with he | hne
  · rw [he, extremePoints_empty]; simp
  · exact hA ι Λ g h hne hb

/-- The `F` cells: finitely many extreme points, at most `binom(3n+4, n+1)`, by `AX-05` (i). -/
lemma cellF_ext (hA : AX05i) (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) :
    (Set.extremePoints ℝ (cellF D σ)).Finite ∧
      (Set.extremePoints ℝ (cellF D σ)).ncard ≤ (3 * n + 4).choose (n + 1) := by
  have hb : Bornology.IsBounded (poly (gF D σ) (hF D σ)) := by
    rw [← cellF_eq]
    exact (Metric.isBounded_Icc 0 D.wbar).subset fun w hw => Novel.M2ActionClassesProof.F_subset_box D hw.1
  have := ax05_apply hA (gF D σ) (hF D σ) hb
  rw [← cellF_eq, card_LamF, card_inst] at this
  exact this

/-- The `E` cells in the ETF coordinates: at most `binom(3n+1, n)`, by `AX-05` (i). -/
lemma cellE_ext (hA : AX05i) (D : Data 1 n 2 S) (ρ : Fin n → Bool) :
    (Set.extremePoints ℝ (poly (gE D ρ) (hE D ρ))).Finite ∧
      (Set.extremePoints ℝ (poly (gE D ρ) (hE D ρ))).ncard ≤ (3 * n + 1).choose n := by
  have hb : Bornology.IsBounded (poly (gE D ρ) (hE D ρ)) := by
    refine (Metric.isBounded_Icc (0 : Fin n → ℝ) (fun j => D.wbar (Sum.inr j))).subset
      fun p hp => ⟨fun j => ?_, fun j => ?_⟩
    · have := hp (Sum.inl (j, 0))
      simp [gE, hE, single_dotProduct] at this
      exact this
    · have := hp (Sum.inl (j, 1))
      simpa [gE, hE, single_dotProduct] using this
  obtain ⟨hfin, hcard⟩ := ax05_apply hA (gE D ρ) (hE D ρ) hb
  have hcardE : Fintype.card (LamE n) = 3 * n + 1 := by
    simp [Fintype.card_sum, Fintype.card_prod]; ring
  rw [hcardE, Fintype.card_fin] at hcard
  exact ⟨hfin, hcard⟩

lemma VertF_card (hA : AX05i) (D : Data 1 n 2 S) :
    (VertF D).Finite ∧ (VertF D).ncard ≤ 2 ^ (n + 1) * (3 * n + 4).choose (n + 1) := by
  have hc : ∀ σ, (Set.extremePoints ℝ (cellF D σ)).Finite ∧
      (Set.extremePoints ℝ (cellF D σ)).ncard ≤ (3 * n + 4).choose (n + 1) := fun σ =>
    cellF_ext hA D σ
  refine ⟨Set.finite_iUnion fun σ => (hc σ).1, ?_⟩
  calc (VertF D).ncard ≤ ∑ σ : Inst 1 n → Bool, (Set.extremePoints ℝ (cellF D σ)).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _σ : Inst 1 n → Bool, (3 * n + 4).choose (n + 1) := Finset.sum_le_sum fun σ _ => (hc σ).2
    _ = 2 ^ (n + 1) * (3 * n + 4).choose (n + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, card_inst,
          smul_eq_mul]

lemma VertE_card (hA : AX05i) (D : Data 1 n 2 S) :
    (VertE D).Finite ∧ (VertE D).ncard ≤ 2 ^ n * (3 * n + 1).choose n := by
  have hc : ∀ ρ, (Set.extremePoints ℝ (cellE D ρ)).Finite ∧
      (Set.extremePoints ℝ (cellE D ρ)).ncard ≤ (3 * n + 1).choose n := fun ρ => by
    obtain ⟨hfin, hcard⟩ := cellE_ext hA D ρ
    have himg := hfin.image (emb D)
    refine ⟨himg.subset (ext_cellE_sub D ρ), ?_⟩
    calc _ ≤ (emb D '' Set.extremePoints ℝ (poly (gE D ρ) (hE D ρ))).ncard :=
          Set.ncard_le_ncard (ext_cellE_sub D ρ) himg
      _ ≤ _ := Set.ncard_image_le hfin
      _ ≤ _ := hcard
  refine ⟨Set.finite_iUnion fun ρ => (hc ρ).1, ?_⟩
  calc (VertE D).ncard ≤ ∑ ρ : Fin n → Bool, (Set.extremePoints ℝ (cellE D ρ)).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _ρ : Fin n → Bool, (3 * n + 1).choose n := Finset.sum_le_sum fun ρ _ => (hc ρ).2
    _ = 2 ^ n * (3 * n + 1).choose n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, smul_eq_mul]

lemma vert_indep (D D' : Data 1 n 2 S) (hwb : D'.wbar = D.wbar) (hw0 : w0 D' = w0 D)
    (hk0 : k0 D' = k0 D) (hkp : D'.kplus = D.kplus) (hkm : D'.kminus = D.kminus) :
    VertF D' = VertF D ∧ VertE D' = VertE D := by
  have hF : F D' = F D := by
    ext w; simp only [F, cash, tau, hwb, hw0, hk0, hkp, hkm]
  have hE : E D' = E D := by
    ext w; simp only [E, hF, hw0]
  constructor
  · simp only [VertF, cellF, hF, hw0]
  · simp only [VertE, cellE, hE, hw0]

end Cells

/-! ### Part 2: the linear score -/

section Linear

variable {n : ℕ} {S : Type} [Fintype S]

lemma score_split0 {D : Data 1 n 2 S} (hγ : D.gamma = 0) (w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) :
    score D w (toPar θ) = θ ⬝ᵥ Aw D w + cF D w := by
  rw [score_split]; simp [R0, cF, hγ]

lemma cF_affine (D : Data 1 n 2 S) (σ : Inst 1 n → Bool) {x y : Inst 1 n → ℝ}
    (hx : x ∈ cellF D σ) (hy : y ∈ cellF D σ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : cF D (a • x + b • y) = a * cF D x + b * cF D y := by
  have hetf : etf (a • x + b • y) = a • etf x + b • etf y := rfl
  have hc : a • x + b • y - w0 D = a • (x - w0 D) + b • (y - w0 D) :=
    Novel.M2ActionClassesProof.comb_sub x y (w0 D) hab
  have hsx : ∀ i, 0 ≤ sg (σ i) * (x - w0 D) i := hx.2
  have hsy : ∀ i, 0 ≤ sg (σ i) * (y - w0 D) i := hy.2
  have hs : ∀ i, 0 ≤ sg (σ i) * (a • (x - w0 D) + b • (y - w0 D)) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hsx i), mul_nonneg hb (hsy i)]
  simp only [cF, hetf, hc, tau_lin D σ hs, tau_lin D σ hsx, tau_lin D σ hsy,
    Novel.M2ActionClassesProof.dot_comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show -(a * (etf x ⬝ᵥ D.cE) + b * (etf y ⬝ᵥ D.cE)) = a * -(etf x ⬝ᵥ D.cE) +
    b * -(etf y ⬝ᵥ D.cE) by ring]
  have e : ∑ i, sg (σ i) * ksel D σ i * (a * (x - w0 D) i + b * (y - w0 D) i)
      = ∑ i, (a * (sg (σ i) * ksel D σ i * (x - w0 D) i) +
        b * (sg (σ i) * ksel D σ i * (y - w0 D) i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma score_affine {D : Data 1 n 2 S} (hγ : D.gamma = 0) (θ : Fin 3 → ℝ) (σ : Inst 1 n → Bool) :
    ∀ x ∈ cellF D σ, ∀ y ∈ cellF D σ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      score D (a • x + b • y) (toPar θ) = a * score D x (toPar θ) + b * score D y (toPar θ) := by
  intro x hx y hy a b ha hb hab
  rw [score_split0 hγ, score_split0 hγ, score_split0 hγ, Aw_comb, cF_affine D σ hx hy ha hb hab,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

lemma cellE_sub (D : Data 1 n 2 S) (ρ : Fin n → Bool) : cellE D ρ ⊆ cellF D (sigE ρ) :=
  fun w hw => by rw [cellE_eq_inter] at hw; exact hw.2

lemma VertF_sub (D : Data 1 n 2 S) : VertF D ⊆ F D := fun w hw => by
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hw; exact hσ.1.1

lemma VertE_sub (D : Data 1 n 2 S) : VertE D ⊆ E D := fun w hw => by
  obtain ⟨ρ, hρ⟩ := Set.mem_iUnion.mp hw; exact hρ.1.1

section Faces

variable {D : Data 1 n 2 S} (hγ : D.gamma = 0) (h0 : w0 D ∈ F D)
include hγ h0

lemma wHatF_face (θ : Fin 3 → ℝ) : wHatF D θ ∈ VertF D ∧
    wHatF D θ ∈ maximizers (fun w => score D w (toPar θ)) (F D) :=
  lexSel_face (cellF D) (F_union D) (compact_F D) ⟨_, h0⟩ (cont_score D _)
    (fun σ => score_affine hγ θ σ)

lemma vHatE_face (θ : Fin 3 → ℝ) : vHatE D θ ∈ VertE D ∧
    vHatE D θ ∈ maximizers (fun w => score D w (toPar θ)) (E D) :=
  lexSel_face (cellE D) (E_union D) (compact_E D) ⟨_, w0_mem_E h0⟩ (cont_score D _)
    (fun ρ x hx y hy => score_affine hγ θ (sigE ρ) x (cellE_sub D ρ hx) y (cellE_sub D ρ hy))

omit hγ h0 in
lemma sSup_max {A : Set (Inst 1 n → ℝ)} {f : (Inst 1 n → ℝ) → ℝ} {w : Inst 1 n → ℝ}
    (hw : w ∈ maximizers f A) : sSup (f '' A) = f w :=
  IsGreatest.csSup_eq ⟨⟨w, hw.1, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hw.2 v hv⟩

lemma etfSup_eq0 (θ : Fin 3 → ℝ) : etfSup D θ = score D (vHatE D θ) (toPar θ) :=
  sSup_max (vHatE_face hγ h0 θ).2

lemma Fsup_eq0 (θ : Fin 3 → ℝ) :
    sSup ((fun w => score D w (toPar θ)) '' F D) = score D (wHatF D θ) (toPar θ) :=
  sSup_max (wHatF_face hγ h0 θ).2

lemma Adv_least (θ : Fin 3 → ℝ) (w : Inst 1 n → ℝ) :
    IsLeast ((fun v => mv D v w θ) '' VertE D) (Adv D w θ) := by
  have hv := vHatE_face hγ h0 θ
  refine ⟨⟨_, hv.1, by simp [mv, Adv, etfSup_eq0 hγ h0]⟩, ?_⟩
  rintro _ ⟨v, hvV, rfl⟩
  have := hv.2.2 v (VertE_sub D hvV)
  simp only [mv, Adv, etfSup_eq0 hγ h0]
  linarith

lemma Adv_inf (θ : Fin 3 → ℝ) (w : Inst 1 n → ℝ) :
    ((Adv D w θ : ℝ) : EReal) = ⨅ v ∈ VertE D, ((mv D v w θ : ℝ) : EReal) := by
  obtain ⟨⟨v0, hv0, he⟩, hlow⟩ := Adv_least hγ h0 θ w
  refine le_antisymm (le_iInf₂ fun v hv => EReal.coe_le_coe_iff.mpr (hlow ⟨v, hv, rfl⟩)) ?_
  exact iInf₂_le_of_le v0 hv0 (by rw [← he])

lemma Gstar_greatest (θ : Fin 3 → ℝ) :
    IsGreatest ((fun u => Adv D u θ) '' VertF D) (Gstar D θ) := by
  have hw := wHatF_face hγ h0 θ
  refine ⟨⟨_, hw.1, by simp [Adv, Gstar, Fsup_eq0 hγ h0]⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have := hw.2.2 u (VertF_sub D hu)
  simp only [Adv, Gstar, Fsup_eq0 hγ h0]
  linarith

end Faces

lemma mv_affine (D : Data 1 n 2 S) (v w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) :
    mv D v w θ = Aw D (w - v) ⬝ᵥ θ + (R0 D w - R0 D v) := by
  rw [mv, score_split, score_split, Aw_sub, sub_dotProduct, dotProduct_comm (Aw D w),
    dotProduct_comm (Aw D v)]
  ring

theorem linearReduction : LinearReduction := by
  intro n S _ D hγ h0
  refine ⟨fun θ => ⟨?_, ?_, Gstar_greatest hγ h0 θ⟩, fun θ w => Adv_least hγ h0 θ w,
    fun v w => ⟨Aw D (w - v), R0 D w - R0 D v, fun θ => mv_affine D v w θ⟩, fun C w => ?_,
    fun th => ⟨(wHatF_face hγ h0 th).1, (vHatE_face hγ h0 th).1⟩⟩
  · have hv := vHatE_face hγ h0 θ
    refine ⟨⟨_, hv.1, (etfSup_eq0 hγ h0 θ).symm⟩, ?_⟩
    rintro _ ⟨v, hvV, rfl⟩
    rw [etfSup_eq0 hγ h0]; exact hv.2.2 v (VertE_sub D hvV)
  · have hw := wHatF_face hγ h0 θ
    refine ⟨⟨_, hw.1, (Fsup_eq0 hγ h0 θ).symm⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [Fsup_eq0 hγ h0]; exact hw.2.2 u (VertF_sub D hu)
  · simp_rw [Adv_inf hγ h0 _ w]
    exact iInf₂_comm _

end Linear

/-! ### Part 3: finitely many scalar contrasts -/

section Contrasts

variable {n : ℕ} {S : Type} [Fintype S]

lemma mv_lin0 {D : Data 1 n 2 S} (hγ : D.gamma = 0) (v w : Inst 1 n → ℝ) (θ : Fin 3 → ℝ) :
    mv D v w θ = Aw D (w - v) ⬝ᵥ θ + (cF D w - cF D v) := by
  rw [mv, score_split0 hγ, score_split0 hγ, Aw_sub, sub_dotProduct, dotProduct_comm (Aw D w),
    dotProduct_comm (Aw D v)]
  ring

lemma Adv_le_iff {D : Data 1 n 2 S} (hγ : D.gamma = 0) (h0 : w0 D ∈ F D) (θ : Fin 3 → ℝ)
    (u : Inst 1 n → ℝ) (δe : ℝ) : Adv D u θ ≤ δe ↔ ∃ v ∈ VertE D, mv D v u θ ≤ δe := by
  obtain ⟨⟨v0, hv0, he⟩, hlow⟩ := Adv_least hγ h0 θ u
  have he' : mv D v0 u θ = Adv D u θ := he
  exact ⟨fun h => ⟨v0, hv0, he' ▸ h⟩, fun ⟨v, hv, hle⟩ => (hlow ⟨v, hv, rfl⟩).trans hle⟩

lemma null_eq {D : Data 1 n 2 S} (hγ : D.gamma = 0) (h0 : w0 D ∈ F D) (δe : ℝ) :
    {θ | Gstar D θ ≤ δe} = ⋂ u ∈ VertF D, ⋃ v ∈ VertE D, Hs D u v δe := by
  ext θ
  obtain ⟨⟨u0, hu0, he⟩, hup⟩ := Gstar_greatest hγ h0 θ
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Hs, exists_prop]
  constructor
  · intro hG u hu
    exact (Adv_le_iff hγ h0 θ u δe).mp ((hup ⟨u, hu, rfl⟩).trans hG)
  · intro h
    rw [← he]
    exact (Adv_le_iff hγ h0 θ u0 δe).mpr (h u0 hu0)

theorem finiteContrasts : FiniteContrasts := by
  intro n S _ D hγ h0
  refine ⟨fun I th θs δe hθs => ?_, fun δe => ⟨null_eq hγ h0 δe, fun u v => ?_, ?_, ?_⟩⟩
  · set CD := {θ | ∀ d ∈ contrasts D, d ⬝ᵥ θ ∈ I d}
    set w := wHatF D th
    have hwV := (wHatF_face hγ h0 th).1
    have h1 : ellD D I w ≤ ⨅ θ ∈ CD, ((Adv D w θ : ℝ) : EReal) := by
      refine le_iInf₂ fun θ hθ => ?_
      rw [Adv_inf hγ h0 θ w]
      refine iInf₂_mono fun v hv => ?_
      have hd : Aw D (w - v) ∈ contrasts D := ⟨w, hwV, v, hv, rfl⟩
      have hle : (⨅ x ∈ I (Aw D (w - v)), (x : EReal)) ≤ ((Aw D (w - v) ⬝ᵥ θ : ℝ) : EReal) :=
        iInf₂_le _ (hθ _ hd)
      calc (⨅ x ∈ I (Aw D (w - v)), (x : EReal)) + ((cF D w - cF D v : ℝ) : EReal)
          ≤ ((Aw D (w - v) ⬝ᵥ θ : ℝ) : EReal) + ((cF D w - cF D v : ℝ) : EReal) :=
            add_le_add_left hle _
        _ = ((mv D v w θ : ℝ) : EReal) := by rw [mv_lin0 hγ, EReal.coe_add]
    have h2 : ⨅ θ ∈ CD, ((Adv D w θ : ℝ) : EReal) ≤ ((Adv D w θs : ℝ) : EReal) :=
      iInf₂_le θs hθs
    refine ⟨hθs, h1, h2, fun _ hδ => ?_⟩
    exact EReal.coe_lt_coe_iff.mp (hδ.trans_le (h1.trans h2))
  · rcases eq_or_ne (Aw D (u - v)) 0 with ha | ha
    · by_cases hb : R0 D u - R0 D v ≤ δe
      · right; left
        ext θ; simp [Hs, mv_affine, ha, hb]
      · right; right
        ext θ; simp [Hs, mv_affine, ha, hb]
    · left
      refine ⟨Aw D (u - v), ha, δe - (R0 D u - R0 D v), ?_⟩
      ext θ; simp only [Hs, mv_affine, Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  · intro hA
    have hFf := (VertF_card hA D).1
    have hEf := (VertE_card hA D).1
    have : Finite (VertF D) := hFf.to_subtype
    have : Finite (VertE D) := hEf.to_subtype
    refine ⟨VertF D → VertE D, inferInstance, fun _ => VertF D, fun _ => inferInstance,
      fun i k => Aw D (k.1 - (i k).1), fun i k => δe - (R0 D k.1 - R0 D (i k).1), ?_⟩
    rw [null_eq hγ h0]
    ext θ
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq, Hs, exists_prop]
    constructor
    · intro h
      choose f hf using fun k : VertF D => h k.1 k.2
      refine ⟨fun k => ⟨f k, (hf k).1⟩, fun k => ?_⟩
      have := (hf k).2
      rw [mv_affine] at this
      linarith
    · rintro ⟨i, hi⟩ u hu
      refine ⟨(i ⟨u, hu⟩).1, (i ⟨u, hu⟩).2, ?_⟩
      have := hi ⟨u, hu⟩
      rw [mv_affine]
      linarith
  · intro ψ u hu
    rw [null_eq hγ h0]
    refine le_iInf₂ fun θ hθ => ?_
    have hθu := Set.mem_iInter₂.mp hθ u hu
    obtain ⟨v, hv, hH⟩ := Set.mem_iUnion₂.mp hθu
    exact iInf₂_le_of_le v hv (iInf₂_le θ hH)

end Contrasts

/-! ### Part 1 for one ETF: the three faces of `E` -/

section One

variable {S : Type} [Fintype S] (D : Data 1 1 2 S)

/-- The holding `(a⁻, t)`. -/
def e1 (t : ℝ) : Inst 1 1 → ℝ := Sum.elim (fun _ => w0 D (Sum.inl 0)) (fun _ => t)

/-- `{(a⁻, p) : lo ≤ p ≤ hi}`. -/
def seg1 (lo hi : ℝ) : Set (Inst 1 1 → ℝ) :=
  {w | w (Sum.inl 0) = w0 D (Sum.inl 0) ∧ lo ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ hi}

lemma inst1_ext {w : Inst 1 1 → ℝ} (ha : w (Sum.inl 0) = w0 D (Sum.inl 0)) :
    w = e1 D (w (Sum.inr 0)) := by
  funext i; rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> simp [e1, ha]

lemma e1_lo_ext {lo hi : ℝ} (hlh : lo ≤ hi) : e1 D lo ∈ Set.extremePoints ℝ (seg1 D lo hi) := by
  refine mem_extremePoints_iff_left.mpr ⟨⟨rfl, le_rfl, hlh⟩, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hp := congrFun he (Sum.inr 0)
  simp only [e1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr] at hp
  have hy0 : y (Sum.inr 0) = lo := by
    by_contra hne
    have h1 : 0 < a * (y (Sum.inr 0) - lo) := mul_pos ha (by
      have := hy.2.1; exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm hne)))
    have h2 : 0 ≤ b * (z (Sum.inr 0) - lo) := mul_nonneg hb.le (by linarith [hz.2.1])
    have h3 : (a + b) * lo = lo := by rw [hab, one_mul]
    linarith
  rw [inst1_ext D hy.1, hy0]

lemma e1_hi_ext {lo hi : ℝ} (hlh : lo ≤ hi) : e1 D hi ∈ Set.extremePoints ℝ (seg1 D lo hi) := by
  refine mem_extremePoints_iff_left.mpr ⟨⟨rfl, hlh, le_rfl⟩, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hp := congrFun he (Sum.inr 0)
  simp only [e1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr] at hp
  have hy0 : y (Sum.inr 0) = hi := by
    by_contra hne
    have h1 : 0 < a * (hi - y (Sum.inr 0)) := mul_pos ha (by
      have := hy.2.2; exact sub_pos.mpr (lt_of_le_of_ne this hne))
    have h2 : 0 ≤ b * (hi - z (Sum.inr 0)) := mul_nonneg hb.le (by linarith [hz.2.2])
    have h3 : (a + b) * hi = hi := by rw [hab, one_mul]
    linarith
  rw [inst1_ext D hy.1, hy0]

lemma ext_seg1 {lo hi : ℝ} (hlh : lo ≤ hi) :
    Set.extremePoints ℝ (seg1 D lo hi) = {e1 D lo, e1 D hi} := by
  ext w
  constructor
  · intro hw
    obtain ⟨⟨ha, hlo, hhi⟩, hext⟩ := mem_extremePoints_iff_left.mp hw
    have hw' := inst1_ext D ha
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    have hp1 : w (Sum.inr 0) ≠ lo := fun h => hne.1 (by rw [hw', h])
    have hp2 : w (Sum.inr 0) ≠ hi := fun h => hne.2 (by rw [hw', h])
    have hlt1 : lo < w (Sum.inr 0) := lt_of_le_of_ne hlo (Ne.symm hp1)
    have hlt2 : w (Sum.inr 0) < hi := lt_of_le_of_ne hhi hp2
    have hd : 0 < hi - lo := by linarith
    have hseg : w ∈ openSegment ℝ (e1 D lo) (e1 D hi) := by
      refine ⟨(hi - w (Sum.inr 0)) / (hi - lo), (w (Sum.inr 0) - lo) / (hi - lo),
        div_pos (by linarith) hd, div_pos (by linarith) hd, by field_simp; ring, ?_⟩
      conv_rhs => rw [hw']
      funext i
      rcases i with i | i <;> simp only [e1, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Sum.elim_inl, Sum.elim_inr] <;> field_simp <;> ring
    have := hext _ (e1_lo_ext D hlh).1 _ (e1_hi_ext D hlh).1 hseg
    exact hp1 (by rw [← this]; rfl)
  · rintro (rfl | rfl)
    · exact e1_lo_ext D hlh
    · exact e1_hi_ext D hlh

variable {D}

lemma cash_one {ρ : Fin 1 → Bool} {w : Inst 1 1 → ℝ} (ha : w (Sum.inl 0) = w0 D (Sum.inl 0))
    (hs : 0 ≤ sg (ρ 0) * (w (Sum.inr 0) - w0 D (Sum.inr 0))) :
    cash D w = k0 D - cf D (sigE ρ) (Sum.inr 0) * (w (Sum.inr 0) - w0 D (Sum.inr 0)) := by
  have hsg : ∀ i, 0 ≤ sg (sigE ρ i) * (w i - w0 D i) := fun i => by
    rcases i with i | i <;> rw [Subsingleton.elim i 0]
    · simp [ha]
    · simpa [sigE] using hs
  rw [cash_lin D (sigE ρ) hsg]
  simp [Fintype.sum_sum_type, ha]

lemma cellE_one (h0 : w0 D ∈ F D) (hkp : 0 ≤ D.kplus (Sum.inr 0))
    (hkm : D.kminus (Sum.inr 0) ≤ 1) (ρ : Fin 1 → Bool) :
    cellE D ρ = if ρ 0 then seg1 D (w0 D (Sum.inr 0)) (w0 D (Sum.inr 0) +
      min (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0)) (k0 D / (1 + D.kplus (Sum.inr 0))))
      else seg1 D 0 (w0 D (Sum.inr 0)) := by
  have hk0 : 0 ≤ k0 D := by
    have := h0.2; rwa [Novel.M2ActionClassesProof.cash_w0] at this
  have hbA := h0.1 (Sum.inl 0)
  have hbE := h0.1 (Sum.inr 0)
  have hcf : cf D (sigE ρ) (Sum.inr 0) = 1 + sg (ρ 0) * (if ρ 0 then D.kplus (Sum.inr 0)
      else D.kminus (Sum.inr 0)) := rfl
  ext w
  constructor
  · rintro ⟨⟨⟨hbox, hcash⟩, hact⟩, hsgn⟩
    have ha : w (Sum.inl 0) = w0 D (Sum.inl 0) := congrFun hact 0
    have hs := hsgn 0
    rw [cash_one ha hs, hcf] at hcash
    cases hρ : ρ 0 <;> simp only [hρ, sg, Bool.false_eq_true, ↓reduceIte] at hs hcash ⊢
    · exact ⟨ha, (hbox _).1, by linarith⟩
    · refine ⟨ha, by linarith, ?_⟩
      have h1 : w (Sum.inr 0) - w0 D (Sum.inr 0) ≤ k0 D / (1 + D.kplus (Sum.inr 0)) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have h2 := (hbox (Sum.inr 0)).2
      have := le_min (show w (Sum.inr 0) - w0 D (Sum.inr 0) ≤ D.wbar (Sum.inr 0) -
        w0 D (Sum.inr 0) by linarith) h1
      linarith
  · intro hw
    have ha : w (Sum.inl 0) = w0 D (Sum.inl 0) := by
      split_ifs at hw <;> exact hw.1
    have hact : active w = active (w0 D) := funext fun i => by rw [Subsingleton.elim i 0]; exact ha
    have hbox_a : 0 ≤ w (Sum.inl 0) ∧ w (Sum.inl 0) ≤ D.wbar (Sum.inl 0) := by rw [ha]; exact hbA
    cases hρ : ρ 0 <;> simp only [hρ, Bool.false_eq_true, ↓reduceIte] at hw
    · obtain ⟨-, hlo, hhi⟩ := hw
      have hs : 0 ≤ sg (ρ 0) * (w (Sum.inr 0) - w0 D (Sum.inr 0)) := by
        simp only [hρ, sg, Bool.false_eq_true, ↓reduceIte]; linarith
      refine ⟨⟨⟨fun i => ?_, ?_⟩, hact⟩, fun j => by rw [Subsingleton.elim j 0]; exact hs⟩
      · rcases i with i | i <;> rw [Subsingleton.elim i 0]
        · exact hbox_a
        · exact ⟨hlo, hhi.trans hbE.2⟩
      · rw [cash_one ha hs, hcf]
        simp only [hρ, sg, Bool.false_eq_true, ↓reduceIte]
        nlinarith
    · obtain ⟨-, hlo, hhi⟩ := hw
      have hs : 0 ≤ sg (ρ 0) * (w (Sum.inr 0) - w0 D (Sum.inr 0)) := by
        simp only [hρ, sg, ↓reduceIte]; linarith
      have hm1 := min_le_left (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0))
        (k0 D / (1 + D.kplus (Sum.inr 0)))
      have hm2 := min_le_right (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0))
        (k0 D / (1 + D.kplus (Sum.inr 0)))
      refine ⟨⟨⟨fun i => ?_, ?_⟩, hact⟩, fun j => by rw [Subsingleton.elim j 0]; exact hs⟩
      · rcases i with i | i <;> rw [Subsingleton.elim i 0]
        · exact hbox_a
        · exact ⟨by linarith [hbE.1], by linarith⟩
      · rw [cash_one ha hs, hcf]
        simp only [hρ, sg, ↓reduceIte]
        have h1 : w (Sum.inr 0) - w0 D (Sum.inr 0) ≤ k0 D / (1 + D.kplus (Sum.inr 0)) := by
          linarith
        rw [le_div_iff₀ (by linarith)] at h1
        linarith

lemma vertE_one (h0 : w0 D ∈ F D) (hkp : 0 ≤ D.kplus (Sum.inr 0))
    (hkm : D.kminus (Sum.inr 0) ≤ 1) :
    VertE D = {e1 D 0, e1 D (w0 D (Sum.inr 0)), e1 D (w0 D (Sum.inr 0) +
      min (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0)) (k0 D / (1 + D.kplus (Sum.inr 0))))} := by
  have hk0 : 0 ≤ k0 D := by
    have := h0.2; rwa [Novel.M2ActionClassesProof.cash_w0] at this
  have hp0 : 0 ≤ w0 D (Sum.inr 0) := (h0.1 (Sum.inr 0)).1
  have hmin : 0 ≤ min (D.wbar (Sum.inr 0) - w0 D (Sum.inr 0)) (k0 D / (1 + D.kplus (Sum.inr 0))) :=
    le_min (by linarith [(h0.1 (Sum.inr 0)).2]) (div_nonneg hk0 (by linarith))
  have hF : ∀ ρ : Fin 1 → Bool, ρ = fun _ => ρ 0 := fun ρ => funext fun j => by
    rw [Subsingleton.elim j 0]
  ext w
  simp only [VertE, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, hw⟩
    rw [cellE_one h0 hkp hkm] at hw
    cases hρ : ρ 0 <;> simp only [hρ, Bool.false_eq_true, ↓reduceIte] at hw
    · rw [ext_seg1 D hp0] at hw
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [ext_seg1 D (by linarith)] at hw
      rcases hw with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · refine ⟨fun _ => false, ?_⟩
      rw [cellE_one h0 hkp hkm]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ext_seg1 D hp0, h]; exact Or.inl rfl
    · refine ⟨fun _ => false, ?_⟩
      rw [cellE_one h0 hkp hkm]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ext_seg1 D hp0, h]; exact Or.inr rfl
    · refine ⟨fun _ => true, ?_⟩
      rw [cellE_one h0 hkp hkm]; simp only [↓reduceIte]
      rw [ext_seg1 D (by linarith), h]; exact Or.inr rfl

end One

/-! ### The error set `A_{N,η}` for any admissible instance -/

section ErrorSet

variable {n : ℕ} {S : Type} [Fintype S]

lemma omega_symm (D : Data 1 n 2 S) : (Omega D)ᵀ = Omega D := by
  ext i j; simp only [Omega, transpose_apply]; exact Finset.sum_congr rfl fun s _ => by ring

lemma mp_exists_herm (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) :
    ∃ G, IsMoorePenrose A G := by
  have hs := hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hs
  set W : Matrix (Fin 3) (Fin 3) ℝ := (hA.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ) with hW
  have h2 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hst : star W = Wᵀ := by
    rw [Matrix.star_eq_conjTranspose, Novel.M4JointDirectionalRateProof.ct_eq]
  set e : Fin 3 → ℝ := RCLike.ofReal ∘ hA.eigenvalues
  set Dg := diagonal e
  set Dp := diagonal fun i => (e i)⁻¹
  have hΩ : A = W * Dg * star W := hs
  have cm : ∀ X Y : Matrix (Fin 3) (Fin 3) ℝ,
      (W * X * star W) * (W * Y * star W) = W * (X * Y) * star W := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star W) W, h2, Matrix.one_mul]
  have ct : ∀ X : Matrix (Fin 3) (Fin 3) ℝ, Xᵀ = X → (W * X * star W)ᵀ = W * X * star W := by
    intro X hX
    rw [hst, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX,
      Matrix.mul_assoc]
  have dT : ∀ f : Fin 3 → ℝ, (diagonal f)ᵀ = diagonal f := fun f => Matrix.diagonal_transpose f
  refine ⟨W * Dp * star W, ?_, ?_, ?_, ?_⟩
  · rw [hΩ, cm, cm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      show (fun i => e i * (e i)⁻¹ * e i) = e from
        funext (Novel.M4JointDirectionalRateProof.diag_mid e)]
  · rw [hΩ, cm, cm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      show (fun i => (e i)⁻¹ * e i * (e i)⁻¹) = fun i => (e i)⁻¹ from funext fun i => by
        by_cases h : e i = 0
        · simp [h]
        · field_simp]
  · rw [hΩ, cm, Matrix.diagonal_mul_diagonal]; exact ct _ (dT _)
  · rw [hΩ, cm, Matrix.diagonal_mul_diagonal]; exact ct _ (dT _)

lemma pinv_mp (D : Data 1 n 2 S) : IsMoorePenrose (Omega D) (pinv (Omega D)) := by
  have hH : (Omega D).IsHermitian := by
    rw [Matrix.IsHermitian, Novel.M4JointDirectionalRateProof.ct_eq, omega_symm]
  exact Classical.epsilon_spec (mp_exists_herm _ hH)

lemma bil_eq (D : Data 1 n 2 S) (x y : Fin 3 → ℝ) :
    x ⬝ᵥ (Omega D *ᵥ y) = ∑ s, D.q s * ((zeta D s ⬝ᵥ x) * (zeta D s ⬝ᵥ y)) := by
  simp only [dotProduct, mulVec, Omega, Fin.sum_univ_three, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma quad_nonneg (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (x : Fin 3 → ℝ) :
    0 ≤ x ⬝ᵥ (Omega D *ᵥ x) := by
  rw [bil_eq]; exact Finset.sum_nonneg fun s _ => mul_nonneg (hq s) (mul_self_nonneg _)

lemma bil_symm (D : Data 1 n 2 S) (x y : Fin 3 → ℝ) :
    x ⬝ᵥ (Omega D *ᵥ y) = y ⬝ᵥ (Omega D *ᵥ x) := by
  rw [bil_eq, bil_eq]; exact Finset.sum_congr rfl fun s _ => by ring

lemma bil_cs (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (x y : Fin 3 → ℝ) :
    (x ⬝ᵥ (Omega D *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (Omega D *ᵥ x)) * (y ⬝ᵥ (Omega D *ᵥ y)) := by
  rw [bil_eq, bil_eq, bil_eq]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun s => Real.sqrt (D.q s) * (zeta D s ⬝ᵥ x)) (fun s => Real.sqrt (D.q s) * (zeta D s ⬝ᵥ y))
  have hsq : ∀ s, Real.sqrt (D.q s) ^ 2 = D.q s := fun s => Real.sq_sqrt (hq s)
  convert this using 2
  · exact Finset.sum_congr rfl fun s _ => by
      linear_combination (-(zeta D s ⬝ᵥ x * (zeta D s ⬝ᵥ y))) * hsq s
  · exact Finset.sum_congr rfl fun s _ => by
      linear_combination (-(zeta D s ⬝ᵥ x * (zeta D s ⬝ᵥ x))) * hsq s
  · exact Finset.sum_congr rfl fun s _ => by
      linear_combination (-(zeta D s ⬝ᵥ y * (zeta D s ⬝ᵥ y))) * hsq s

lemma quad_G (D : Data 1 n 2 S) (x : Fin 3 → ℝ) :
    (Omega D *ᵥ x) ⬝ᵥ (pinv (Omega D) *ᵥ (Omega D *ᵥ x)) = x ⬝ᵥ (Omega D *ᵥ x) :=
  Novel.M4BoundedLawRateProof.quad_range (omega_symm D) (pinv_mp D).1 x

/-- A shock with positive mass lies in `Im Ω`. -/
lemma zeta_range (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) {s : S} (hs : 0 < D.q s) :
    zeta D s = Omega D *ᵥ ((pinv (Omega D))ᵀ *ᵥ zeta D s) := by
  obtain ⟨h1, -, -, h4⟩ := pinv_mp D
  have hsym := omega_symm D
  set Ω := Omega D
  set G := pinv Ω
  set r := zeta D s - (G * Ω) *ᵥ zeta D s
  have hΩr : Ω *ᵥ r = 0 := by
    simp only [r, mulVec_sub, mulVec_mulVec]
    rw [← Matrix.mul_assoc, h1, sub_self]
  have hPr : (G * Ω) *ᵥ r = 0 := by
    simp only [r, mulVec_sub, mulVec_mulVec]
    rw [show G * Ω * (G * Ω) = G * (Ω * G * Ω) by simp [Matrix.mul_assoc], h1, sub_self]
  have hq0 : ∑ t, D.q t * ((zeta D t ⬝ᵥ r) * (zeta D t ⬝ᵥ r)) = 0 := by
    rw [← bil_eq, hΩr, dotProduct_zero]
  have hzr : zeta D s ⬝ᵥ r = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun t _ =>
      mul_nonneg (hq t) (mul_self_nonneg _)).mp hq0 s (Finset.mem_univ _)
    rcases mul_eq_zero.mp hall with h | h
    · exact absurd h hs.ne'
    · exact mul_self_eq_zero.mp h
  have hPz : ((G * Ω) *ᵥ zeta D s) ⬝ᵥ r = 0 := by
    rw [Novel.M4JointDirectionalRateProof.dot_mulVec, h4, hPr, dotProduct_zero]
  have hrr : r ⬝ᵥ r = 0 := by
    have : r ⬝ᵥ r = zeta D s ⬝ᵥ r - ((G * Ω) *ᵥ zeta D s) ⬝ᵥ r := by
      simp only [r]; rw [sub_dotProduct]
    rw [this, hzr, hPz, sub_zero]
  have hGΩ : G * Ω = Ω * Gᵀ := by
    rw [← h4, Matrix.transpose_mul, hsym]
  have := sub_eq_zero.mp (dotProduct_self_eq_zero.mp hrr)
  conv_lhs => rw [this]
  rw [hGΩ, ← mulVec_mulVec]

lemma TN_nonneg (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) {N : ℕ} {σ : Fin N → S}
    (hm : 0 < mass D σ) : 0 ≤ TN D σ := by
  have hpos : ∀ l, 0 < D.q (σ l) := fun l => lt_of_le_of_ne (hq _) (fun h => by
    have : mass D σ = 0 := Finset.prod_eq_zero (Finset.mem_univ l) h.symm
    linarith)
  set G := pinv (Omega D)
  have he : errN D σ = Omega D *ᵥ (Gᵀ *ᵥ errN D σ) := by
    simp only [errN, mulVec_smul, mulVec_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => zeta_range D hq (hpos l)
  rw [TN, he, quad_G]
  exact mul_nonneg (Nat.cast_nonneg _) (quad_nonneg D hq _)

lemma tcrit_nonneg (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (N : ℕ) (η : ℝ) :
    0 ≤ tcrit D N η := by
  unfold tcrit
  by_cases hne : {t | (∃ σ : Fin N → S, 0 < mass D σ ∧ TN D σ = t) ∧
      1 - η ≤ ∑ σ : Fin N → S, if TN D σ ≤ t then mass D σ else 0}.Nonempty
  · exact le_csInf hne fun t ⟨⟨σ, hm, ht⟩, _⟩ => ht ▸ TN_nonneg D hq hm
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

lemma mem_Aset (D : Data 1 n 2 S) {N : ℕ} {η : ℝ} {e : Fin 3 → ℝ} :
    e ∈ Aset D N η ↔ ∃ x, e = Omega D *ᵥ x ∧ (N : ℝ) * (x ⬝ᵥ (Omega D *ᵥ x)) ≤ tcrit D N η := by
  constructor
  · rintro ⟨⟨x, rfl⟩, h⟩; exact ⟨x, rfl, by rwa [quad_G] at h⟩
  · rintro ⟨x, rfl, h⟩; exact ⟨⟨x, rfl⟩, by rwa [quad_G]⟩

lemma mv_sub (D : Data 1 n 2 S) (v w : Inst 1 n → ℝ) (th e : Fin 3 → ℝ) :
    mv D v w (th - e) = mv D v w th - e ⬝ᵥ Aw D (w - v) := by
  rw [mv_affine, mv_affine, dotProduct_sub, dotProduct_comm e]; ring

lemma closed_form (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) {N : ℕ} (hN : 0 < N) (η : ℝ)
    (th : Fin 3 → ℝ) (v w : Inst 1 n → ℝ) :
    let d := Aw D (w - v)
    let r := Real.sqrt (tcrit D N η / N)
    ⨅ e ∈ Aset D N η, ((mv D v w (th - e) : ℝ) : EReal)
        = ((mv D v w th - r * Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d)) : ℝ) : EReal) ∧
      (0 < d ⬝ᵥ (Omega D *ᵥ d) →
        (r / Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) • (Omega D *ᵥ d) ∈ Aset D N η ∧
        mv D v w (th - (r / Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) • (Omega D *ᵥ d))
          = mv D v w th - r * Real.sqrt (d ⬝ᵥ (Omega D *ᵥ d))) ∧
      (d ⬝ᵥ (Omega D *ᵥ d) = 0 → (0 : Fin 3 → ℝ) ∈ Aset D N η) := by
  intro d r
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 := tcrit_nonneg D hq N η
  have htN : 0 ≤ tcrit D N η / N := div_nonneg ht0 hNr.le
  have hr2 : r ^ 2 = tcrit D N η / N := Real.sq_sqrt htN
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set P := d ⬝ᵥ (Omega D *ᵥ d) with hP
  have hP0 : 0 ≤ P := quad_nonneg D hq d
  -- the lower bound on the whole error set
  have hlow : ∀ e ∈ Aset D N η, mv D v w th - r * Real.sqrt P ≤ mv D v w (th - e) := by
    intro e he
    obtain ⟨x, rfl, hx⟩ := (mem_Aset D).mp he
    rw [mv_sub, Novel.M4JointDirectionalRateProof.dot_mulVec, omega_symm]
    have hxx : x ⬝ᵥ (Omega D *ᵥ x) ≤ r ^ 2 := by
      rw [hr2, le_div_iff₀ hNr]; linarith
    have hcs := bil_cs D hq x d
    have h2 : (x ⬝ᵥ (Omega D *ᵥ d)) ^ 2 ≤ (r * Real.sqrt P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0]
      exact hcs.trans (mul_le_mul_of_nonneg_right hxx hP0)
    have := sq_le_sq.mp h2
    linarith [le_abs_self (x ⬝ᵥ (Omega D *ᵥ d)), abs_of_nonneg (by positivity : 0 ≤ r * Real.sqrt P)]
  have hzero : P = 0 → (0 : Fin 3 → ℝ) ∈ Aset D N η := fun _ =>
    (mem_Aset D).mpr ⟨0, by simp, by simp [ht0]⟩
  have hattain : 0 < P → (r / Real.sqrt P) • (Omega D *ᵥ d) ∈ Aset D N η ∧
      mv D v w (th - (r / Real.sqrt P) • (Omega D *ᵥ d)) = mv D v w th - r * Real.sqrt P := by
    intro hPp
    have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hPp
    have hsP2 : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP0
    refine ⟨(mem_Aset D).mpr ⟨(r / Real.sqrt P) • d, (mulVec_smul _ _ _).symm, ?_⟩, ?_⟩
    · rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hP]
      have : r / Real.sqrt P * (r / Real.sqrt P * P) = r ^ 2 := by
        field_simp; rw [hsP2]
      rw [this, hr2, mul_div_cancel₀ _ hNr.ne']
    · rw [mv_sub, smul_dotProduct, smul_eq_mul, Novel.M4JointDirectionalRateProof.dot_mulVec,
        omega_symm, ← hP]
      have : r / Real.sqrt P * P = r * Real.sqrt P := by
        field_simp; rw [hsP2]
      rw [this]
  refine ⟨le_antisymm ?_ (le_iInf₂ fun e he => EReal.coe_le_coe_iff.mpr (hlow e he)),
    hattain, hzero⟩
  rcases hP0.lt_or_eq with hPp | hPe
  · obtain ⟨hmem, heq⟩ := hattain hPp
    exact iInf₂_le_of_le _ hmem (by rw [heq])
  · refine iInf₂_le_of_le _ (hzero hPe.symm) ?_
    rw [sub_zero, ← hPe, Real.sqrt_zero, mul_zero, sub_zero]

lemma Aset_closed (D : Data 1 n 2 S) (N : ℕ) (η : ℝ) : IsClosed (Aset D N η) := by
  have hr : Set.range (Omega D).mulVec = ((LinearMap.range (Omega D).mulVecLin : Submodule ℝ _) :
      Set (Fin 3 → ℝ)) := by
    ext e; simp [LinearMap.mem_range]
  have h1 : IsClosed (Set.range (Omega D).mulVec) := by
    rw [hr]; exact Submodule.closed_of_finiteDimensional _
  have h2 : IsClosed {e : Fin 3 → ℝ | (N : ℝ) * (e ⬝ᵥ (pinv (Omega D) *ᵥ e)) ≤ tcrit D N η} :=
    isClosed_le (continuous_const.mul (continuous_id.dotProduct
      (continuous_const.matrix_mulVec continuous_id))) continuous_const
  exact h1.inter h2

lemma Aset_convex (D : Data 1 n 2 S) (hq : ∀ s, 0 ≤ D.q s) (N : ℕ) (η : ℝ) :
    Convex ℝ (Aset D N η) := by
  intro e1 he1 e2 he2 a b ha hb hab
  obtain ⟨x1, rfl, h1⟩ := (mem_Aset D).mp he1
  obtain ⟨x2, rfl, h2⟩ := (mem_Aset D).mp he2
  refine (mem_Aset D).mpr ⟨a • x1 + b • x2, by simp [mulVec_add, mulVec_smul], ?_⟩
  have hq12 := quad_nonneg D hq (x1 - x2)
  have hexp : (a • x1 + b • x2) ⬝ᵥ (Omega D *ᵥ (a • x1 + b • x2)) = a * (x1 ⬝ᵥ (Omega D *ᵥ x1))
      + b * (x2 ⬝ᵥ (Omega D *ᵥ x2)) - a * b * ((x1 - x2) ⬝ᵥ (Omega D *ᵥ (x1 - x2))) := by
    simp only [bil_eq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [hexp]
  have := mul_nonneg hN0 (mul_nonneg (mul_nonneg ha hb) hq12)
  have e3 : (N : ℝ) * (a * (x1 ⬝ᵥ (Omega D *ᵥ x1)) + b * (x2 ⬝ᵥ (Omega D *ᵥ x2))) =
      a * (N * (x1 ⬝ᵥ (Omega D *ᵥ x1))) + b * (N * (x2 ⬝ᵥ (Omega D *ᵥ x2))) := by ring
  have h1' := mul_le_mul_of_nonneg_left h1 ha
  have h2' := mul_le_mul_of_nonneg_left h2 hb
  have h3 : (a + b) * tcrit D N η = tcrit D N η := by rw [hab, one_mul]
  nlinarith

lemma Cset_compact_convex (D : Data 1 n 2 S) (V : Finset (Fin 3 → ℝ)) (hq : ∀ s, 0 ≤ D.q s)
    (N : ℕ) (η : ℝ) (th : Fin 3 → ℝ) :
    IsCompact (Cset D V N η th) ∧ Convex ℝ (Cset D V N η th) := by
  have hC : Cset D V N η th = Theta4 V ∩ (fun θ => th - θ) ⁻¹' Aset D N η := by
    ext θ
    simp only [Cset, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_congr_right fun _ => ⟨fun ⟨e, he, h⟩ => by rw [h, sub_sub_cancel]; exact he,
      fun h => ⟨th - θ, h, by abel⟩⟩
  rw [hC]
  have hT : IsCompact (Theta4 V) := Set.Finite.isCompact_convexHull (𝕜 := ℝ) (hs := V.finite_toSet)
  have hTc : Convex ℝ (Theta4 V) := convex_convexHull ℝ _
  refine ⟨hT.inter_right ((Aset_closed D N η).preimage (continuous_const.sub continuous_id)),
    hTc.inter ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_preimage] at hx hy ⊢
  have : th - (a • x + b • y) = a • (th - x) + b • (th - y) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  rw [this]
  exact Aset_convex D hq N η hx hy ha hb hab

theorem errorSet : ErrorSet := by
  intro n S _ D V hadm N η hN
  obtain ⟨-, -, hq, -, -, -, -, -, -, -, -, h0, -, -⟩ := hadm
  refine ⟨fun th v w => closed_form D hq hN η th v w, fun th => Cset_compact_convex D V hq N η th,
    fun hγ th w hne => ?_⟩
  have hL : LN D V N η th w = ⨅ θ ∈ Cset D V N η th, ((Adv D w θ : ℝ) : EReal) := by
    simp only [LN, hne.ne_empty, ↓reduceIte]
  have hLv : LN D V N η th w = ⨅ v ∈ VertE D, ⨅ θ ∈ Cset D V N η th, ((mv D v w θ : ℝ) : EReal) := by
    rw [hL]; simp_rw [Adv_inf hγ h0 _ w]; exact iInf₂_comm _
  refine ⟨hLv, ?_⟩
  rw [hLv]
  refine iInf₂_mono fun v _ => ?_
  rw [← (closed_form D hq hN η th v w).1]
  refine le_iInf₂ fun θ hθ => ?_
  obtain ⟨-, e, he, rfl⟩ := hθ
  exact iInf₂_le e he

end ErrorSet

/-! ### Part 1 -/

theorem facesFinite : FacesFinite := by
  refine ⟨fun n S _ D => ⟨fun σ => ⟨(cellF_compact_convex D σ).1, (cellF_compact_convex D σ).2,
    ?_⟩, fun ρ => ⟨(cellE_compact_convex D ρ).1, (cellE_compact_convex D ρ).2, fun h0 => ?_⟩,
    w0_mem_cells D, F_union D, E_union D, fun hA => ⟨(VertF_card hA D).1, (VertF_card hA D).2,
      (VertE_card hA D).1, (VertE_card hA D).2⟩, fun D' h1 h2 h3 h4 h5 => vert_indep D D' h1 h2 h3 h4 h5⟩,
    fun S _ D h0 hkp hkm => vertE_one h0 hkp hkm⟩
  · have hc : Fintype.card (LamF n) = 3 * (n + 1) + 1 := by rw [card_LamF]; ring
    set e := Fintype.equivFinOfCardEq hc
    refine ⟨gF D σ ∘ e.symm, hF D σ ∘ e.symm, ?_⟩
    rw [cellF_eq]
    ext w
    exact ⟨fun hw l => hw _, fun hw l => by simpa using hw (e l)⟩
  · have hc : Fintype.card (LamE n) = 3 * n + 1 := by
      simp [Fintype.card_sum, Fintype.card_prod]; ring
    set e := Fintype.equivFinOfCardEq hc
    refine ⟨gE D ρ ∘ e.symm, hE D ρ ∘ e.symm, ?_⟩
    rw [cellE_eq]
    have hbox := h0.1 (Sum.inl 0)
    ext w
    simp only [Set.mem_ofPred_eq, Function.comp]
    exact ⟨fun ⟨ha, _, hp⟩ => ⟨ha, fun l => hp _⟩,
      fun ⟨ha, hp⟩ => ⟨ha, hbox, fun l => by simpa using hp (e l)⟩⟩

/-! ### Part 4: the curvature deficit -/

section Deficit

variable {n : ℕ} {S : Type} [Fintype S]

lemma pS_neg (D : Data 1 n 2 S) (z : Inst 1 n → ℝ) :
    Novel.M4CurvatureCertificateProof.pS D (-z) = Novel.M4CurvatureCertificateProof.pS D z := by
  simp [Novel.M4CurvatureCertificateProof.pS, mulVec_neg]

lemma maxE_unique {D : Data 1 n 2 S} (hr : Standalone.M2ActionClasses.RatesNonneg D)
    (hq : ∀ s, 0 ≤ D.q s) (h0 : w0 D ∈ F D) (hγ : 0 < D.gamma)
    (hpd : ∀ z : Inst 1 n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (covariance D *ᵥ z)) (θ : Fin 3 → ℝ) :
    maximizers (fun v => score D v (toPar θ)) (E D) = {vHatE D θ} := by
  obtain ⟨w, hw, hmax⟩ := (compact_E D).exists_isMaxOn ⟨_, w0_mem_E h0⟩
    (cont_score D (toPar θ)).continuousOn
  have hwm : w ∈ maximizers (fun v => score D v (toPar θ)) (E D) :=
    ⟨hw, fun w' hw' => hmax hw'⟩
  have hset : maximizers (fun v => score D v (toPar θ)) (E D) = {w} := by
    refine Set.ext fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · have hgap := Novel.M4CurvatureCertificateProof.qgap D hr hq hγ.le
        (Novel.M2ActionClassesProof.classesConvex D hr).2.1 hwm hu.1
      have hle := hu.2 w hw
      have hP : Novel.M4CurvatureCertificateProof.pS D (w - u) ≤ 0 := by
        by_contra h
        have : 0 < D.gamma / 2 * Novel.M4CurvatureCertificateProof.pS D (w - u) :=
          mul_pos (by linarith) (not_le.mp h)
        linarith
      have : w - u = 0 := by
        by_contra hne; exact absurd (hpd _ hne) (not_lt.mpr hP)
      exact (sub_eq_zero.mp this).symm
    · rw [Set.mem_singleton_iff.mp hu]; exact hwm
  rw [vHatE, hset, Novel.M4CurvatureCertificateProof.lexSel_single]

theorem curvatureDeficit : CurvatureDeficit := by
  intro n S _ D V hr hq h0 hγ hpd Sf hS hSE
  have hmax := maxE_unique hr hq h0 hγ hpd
  have hvm : ∀ θ, vHatE D θ ∈ maximizers (fun v => score D v (toPar θ)) (E D) := fun θ => by
    rw [hmax θ]; rfl
  have hsup : ∀ θ, etfSup D θ = score D (vHatE D θ) (toPar θ) := fun θ => sSup_max (hvm θ)
  have hdef : ∀ θ, D.gamma / 2 * Sf.inf' hS (fun v =>
      (v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ)))
      ≤ etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) := by
    intro θ
    obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_sup' hS (fun v => score D v (toPar θ))
    have hgap := Novel.M4CurvatureCertificateProof.qgap D hr hq hγ.le
      (Novel.M2ActionClassesProof.classesConvex D hr).2.1 (hvm θ) (hSE hv)
    have hle := Finset.inf'_le (fun v => (v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ))) hv
    have hneg : Novel.M4CurvatureCertificateProof.pS D (vHatE D θ - v)
        = (v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ)) := by
      rw [← neg_sub, pS_neg]; rfl
    rw [hneg] at hgap
    rw [hsup θ, hve]
    exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans hgap
  refine ⟨fun θ => ⟨hmax θ, hdef θ, fun w => ?_⟩, fun δe hδ θ hθ => ?_⟩
  · obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_sup' hS (fun v => score D v (toPar θ))
    have : Sf.inf' hS (fun v => mv D v w θ)
        = score D w (toPar θ) - Sf.sup' hS (fun v => score D v (toPar θ)) := by
      refine le_antisymm ?_ (Finset.le_inf' _ _ fun v' hv' => ?_)
      · refine (Finset.inf'_le _ hv).trans ?_
        simp only [mv, hve, le_refl]
      · simp only [mv]
        linarith [Finset.le_sup' (fun v => score D v (toPar θ)) hv']
    rw [this, Adv]; ring
  · obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_inf' hS (fun v =>
      (v - vHatE D θ) ⬝ᵥ (covariance D *ᵥ (v - vHatE D θ)))
    refine ⟨v, hv, Real.sqrt_le_sqrt ?_⟩
    have h1 := (hdef θ).trans (hδ θ hθ)
    rw [hve] at h1
    rw [le_div_iff₀ hγ]
    linarith

end Deficit

section Family

open Standalone.M4CurvedEntryRate (data xs act cC)

lemma dist_fin {m : ℕ} {k k' : Fin (m + 1)} (h : k ≠ k') : 1 ≤ |(k : ℝ) - k'| := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hl | hl
  · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hl
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hl
    rw [abs_of_nonneg (by linarith)]; linarith

/-- The pigeonhole: some grid point in `[1/4 - s, 1/4 + s]` is `s/(m+1)`-far from all `m` points. -/
lemma pigeon {s : ℝ} (hs : 0 < s) (Sf : Finset (Inst 1 1 → ℝ)) :
    ∃ k : Fin (Sf.card + 1), ∀ v ∈ Sf, s / (Sf.card + 1) ≤
      |(1 / 4 - s + (2 * (k : ℝ) + 1) * (s / (Sf.card + 1))) - v (Sum.inr 0)| := by
  set m := Sf.card
  set t := s / ((m : ℝ) + 1)
  have ht : 0 < t := by positivity
  by_contra hcon
  push Not at hcon
  choose f hf using hcon
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin (m + 1))) := by
    intro k _ k' _ hkk
    by_contra hne
    have h1 := (hf k).2
    have h2 := (hf k').2
    rw [hkk] at h1
    have hd := dist_fin hne
    have e : (1 / 4 - s + (2 * (k : ℝ) + 1) * t) - (1 / 4 - s + (2 * (k' : ℝ) + 1) * t)
        = 2 * t * ((k : ℝ) - k') := by ring
    have h3 : |(1 / 4 - s + (2 * (k : ℝ) + 1) * t) - (1 / 4 - s + (2 * (k' : ℝ) + 1) * t)| < 2 * t := by
      calc _ ≤ |(1 / 4 - s + (2 * (k : ℝ) + 1) * t) - f k' (Sum.inr 0)| +
            |f k' (Sum.inr 0) - (1 / 4 - s + (2 * (k' : ℝ) + 1) * t)| := abs_sub_le _ _ _
        _ < t + t := by rw [abs_sub_comm (f k' (Sum.inr 0))]; exact add_lt_add h1 h2
        _ = 2 * t := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * t)] at h3
    nlinarith
  have := Finset.card_le_card_of_injOn f (fun k _ => (hf k).1) hinj
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact absurd this (by omega)

theorem familyDeficit : FamilyDeficit := by
  intro s hs0 hs1 S _ q U hK D Sf hS hSE
  obtain ⟨-, hT, -, -, hF, hE, hscore, hgeo⟩ :=
    Novel.M4CurvedEntryRateProof.geometry s hs0 hs1 S q U hK
  have hw0 : w0 D = 0 := Novel.M4CurvedEntryRateProof.w0_d s q U
  set m := Sf.card
  set t := s / ((m : ℝ) + 1) with htdef
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have ht : 0 < t := by positivity
  have htm : t * ((m : ℝ) + 1) = s := by rw [htdef]; field_simp
  have hvE : ∀ v ∈ Sf, v (Sum.inl 0) = 0 ∧ 0 ≤ v (Sum.inr 0) ∧ v (Sum.inr 0) ≤ 1 := fun v hv => by
    have := hSE hv; rw [hE] at this; exact this
  -- the far parameter
  obtain ⟨k, hk⟩ := pigeon hs0 Sf
  set c := 1 / 4 - s + (2 * (k : ℝ) + 1) * t with hc
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hc1 : |c - 1 / 4| ≤ s := by
    rw [abs_le]; constructor <;> nlinarith
  set θ : Fin 3 → ℝ := ![0, c, 0] with hθdef
  have hθ : θ ∈ Theta4 (Standalone.M4CurvedEntryRate.V4 s) := by
    rw [hT]; intro i; fin_cases i
    · simp [θ, cC, hs0.le]
    · change |c - cC 1| ≤ s; simpa [cC] using hc1
    · simp [θ, cC, hs0.le]
  obtain ⟨-, -, hsupE, -, -, -, hAdv, -, -⟩ := hgeo θ hθ
  have hθ1 : θ 1 = c := rfl
  have hxs : xs θ = 0 := by simp [xs, θ]
  have hQv : ∀ v ∈ Sf, score D v (toPar θ) = v (Sum.inr 0) * c - v (Sum.inr 0) ^ 2 / 2 := by
    intro v hv; rw [hscore, hxs, (hvE v hv).1, hθ1]; ring
  have hfar : ∀ v ∈ Sf, t ^ 2 / 2 ≤ etfSup D θ - score D v (toPar θ) := by
    intro v hv
    rw [hsupE, hQv v hv, hθ1]
    have h1 := hk v hv
    have h2 : t ^ 2 ≤ (c - v (Sum.inr 0)) ^ 2 := by
      rw [← sq_abs (c - _)]; exact pow_le_pow_left₀ ht.le h1 2
    nlinarith
  have ht2 : t ^ 2 = s ^ 2 / ((m : ℝ) + 1) ^ 2 := by rw [htdef, div_pow]
  have hdefi : s ^ 2 / (2 * ((m : ℝ) + 1) ^ 2) ≤
      etfSup D θ - Sf.sup' hS (fun v => score D v (toPar θ)) := by
    obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_sup' hS (fun v => score D v (toPar θ))
    rw [hve]
    have := hfar v hv
    rw [ht2] at this
    calc s ^ 2 / (2 * ((m : ℝ) + 1) ^ 2) = s ^ 2 / ((m : ℝ) + 1) ^ 2 / 2 := by
          rw [div_div, mul_comm]
      _ ≤ _ := this
  refine ⟨⟨θ, hθ, rfl, rfl, hdefi, ?_⟩, fun δ hδ hδs hall => ?_⟩
  · set a := s / (2 * ((m : ℝ) + 1)) with hadef
    have ha : a = t / 2 := by rw [hadef, htdef]; field_simp
    have hc0 : 0 ≤ c := by nlinarith
    have hcle : c ≤ 1 / 4 + s := by linarith [(abs_le.mp hc1).2]
    have hsq : a ^ 2 = s ^ 2 / (4 * ((m : ℝ) + 1) ^ 2) := by rw [hadef, div_pow]; ring
    have hta : t ≤ s := by
      rw [htdef, div_le_iff₀ hm1]; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    refine ⟨?_, ?_, ?_, fun v hv => ?_⟩
    · rw [hF]; simp only [act, Sum.elim_inl, Sum.elim_inr, Set.mem_ofPred_eq]
      refine ⟨by positivity, by rw [hθ1]; exact hc0, ?_⟩
      rw [hθ1, ha]; linarith
    · rw [hw0]; simp only [act, Sum.elim_inl, Pi.zero_apply]; positivity
    · rw [hAdv, hxs, hsq]; ring
    · have hQw : score D (act a (θ 1)) (toPar θ) = c ^ 2 / 2 - a ^ 2 := by
        rw [hscore, hxs]; simp only [act, Sum.elim_inl, Sum.elim_inr, hθ1]; ring
      have h1 := hfar v hv
      rw [hsupE, hQv v hv, hθ1] at h1
      rw [mv, hQw, hQv v hv, ← hsq]
      have : a ^ 2 = t ^ 2 / 4 := by rw [ha]; ring
      linarith
  · have h1 := hdefi.trans (hall θ hθ)
    have hm2 : 2 * s ^ 2 / δ ≤ ((m : ℝ) + 1) ^ 2 := by
      rw [div_le_iff₀ hδ]
      rw [div_le_iff₀ (by positivity)] at h1
      nlinarith
    have hsq : s * Real.sqrt (2 / δ) = Real.sqrt (2 * s ^ 2 / δ) := by
      rw [show 2 * s ^ 2 / δ = s ^ 2 * (2 / δ) by ring, Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hs0.le]
    rw [hsq]
    constructor
    · rw [Real.sqrt_le_left (by positivity)]; exact hm2
    · rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ hδ]; nlinarith

end Family

/-! ### Part 5: exactness under curvature -/

section Exact

variable {n : ℕ} {S : Type} [Fintype S]

lemma cont_score_th (D : Data 1 n 2 S) (v : Inst 1 n → ℝ) :
    Continuous (fun θ : Fin 3 → ℝ => score D v (toPar θ)) := by
  have e : (fun θ : Fin 3 → ℝ => score D v (toPar θ)) = fun θ => θ ⬝ᵥ Aw D v + R0 D v :=
    funext fun θ => Novel.M4CurvatureCertificateProof.score_split D v θ
  rw [e]
  exact (continuous_id.dotProduct continuous_const).add continuous_const

theorem exactIff : ExactIff := by
  intro n S _ D hr hq h0 hγ hpd Sf hS hSE T hT hTne
  have hmax := maxE_unique hr hq h0 hγ hpd
  have hvm : ∀ θ, vHatE D θ ∈ maximizers (fun v => score D v (toPar θ)) (E D) := fun θ => by
    rw [hmax θ]; rfl
  have hsup : ∀ θ, etfSup D θ = score D (vHatE D θ) (toPar θ) := fun θ => sSup_max (hvm θ)
  have huniq : ∀ θ v, v ∈ E D → score D v (toPar θ) = score D (vHatE D θ) (toPar θ) →
      v = vHatE D θ := fun θ v hv he => by
    have hm : v ∈ maximizers (fun v => score D v (toPar θ)) (E D) :=
      ⟨hv, fun w hw => by show score D w (toPar θ) ≤ score D v (toPar θ); rw [he]; exact (hvm θ).2 w hw⟩
    rw [hmax θ] at hm; exact hm
  constructor
  · intro hex
    have hmem : ∀ θ ∈ T, vHatE D θ ∈ Sf := by
      intro θ hθ
      obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_sup' hS (fun v => score D v (toPar θ))
      have h1 := hex θ hθ
      rw [hsup θ, hve] at h1
      rw [← huniq θ v (hSE hv) h1.symm]; exact hv
    have hloc : ∀ θ0 ∈ T, ∀ᶠ θ in nhdsWithin θ0 T, vHatE D θ = vHatE D θ0 := by
      intro θ0 hθ0
      have hstrict : ∀ v' ∈ Sf, v' ≠ vHatE D θ0 →
          score D v' (toPar θ0) < score D (vHatE D θ0) (toPar θ0) := fun v' hv' hne =>
        lt_of_le_of_ne ((hvm θ0).2 v' (hSE hv')) (fun h => hne (huniq θ0 v' (hSE hv') h))
      have hev : ∀ᶠ θ in nhds θ0, ∀ v' ∈ Sf, v' ≠ vHatE D θ0 →
          score D v' (toPar θ) < score D (vHatE D θ0) (toPar θ) := by
        rw [Filter.eventually_all_finset]
        intro v' hv'
        by_cases hne : v' = vHatE D θ0
        · exact Filter.Eventually.of_forall fun θ h => absurd hne h
        · have hc := ((cont_score_th D v').sub (cont_score_th D (vHatE D θ0))).continuousAt (x := θ0)
          have := hc.eventually (gt_mem_nhds (show score D v' (toPar θ0)
            - score D (vHatE D θ0) (toPar θ0) < 0 by linarith [hstrict v' hv' hne]))
          filter_upwards [this] with θ hθ _
          have : score D v' (toPar θ) - score D (vHatE D θ0) (toPar θ) < 0 := hθ
          linarith
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with θ hθ hθT
      by_contra hne
      have h1 := hθ _ (hmem θ hθT) hne
      have h2 := (hvm θ).2 (vHatE D θ0) (hvm θ0).1
      simp only at h2
      linarith
    obtain ⟨θ0, hθ0⟩ := hTne
    refine ⟨vHatE D θ0, hmem θ0 hθ0, fun θ hθ => ?_⟩
    have hcont : ContinuousOn (vHatE D) T := fun θ' hθ' =>
      (continuousWithinAt_const (b := vHatE D θ')).congr_of_eventuallyEq (hloc θ' hθ') rfl
    exact hT.isPreconnected.constant_of_mapsTo Sf.finite_toSet.isDiscrete hcont
      (fun θ' hθ' => hmem θ' hθ') hθ hθ0
  · rintro ⟨v0, hv0, hc⟩ θ hθ
    rw [hsup θ, hc θ hθ]
    refine le_antisymm (Finset.le_sup' (fun v => score D v (toPar θ)) hv0)
      (Finset.sup'_le hS _ fun v hv => ?_)
    have := (hvm θ).2 v (hSE hv)
    rw [hc θ hθ] at this
    exact this

end Exact

/-! ### Part 5: experiment 009's fixture -/

section Fixture

/-- The fixture's quadratic form: `w'Σw = 54/10⁶ a² + 85/10⁶ a p + 145/(4·10⁶) p²`. -/
lemma quad009 (w : Inst 1 1 → ℝ) : w ⬝ᵥ (covariance fix009 *ᵥ w)
    = 54 / 1000000 * w (Sum.inl 0) ^ 2 + 85 / 1000000 * w (Sum.inl 0) * w (Sum.inr 0)
      + 145 / 4000000 * w (Sum.inr 0) ^ 2 := by
  rw [Novel.M2ActionClassesProof.quad_eq]
  simp only [fix009, xi, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one, Fintype.sum_prod_type,
    Fintype.sum_bool, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, mulVec, Fin.sum_univ_two, sg,
    ↓reduceIte, Bool.false_eq_true, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

lemma w0_009 : w0 fix009 = hold (1 / 2) := by
  have hW : W0 fix009 = 1 := by
    simp only [W0, fix009, Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr]
    norm_num
  funext i
  simp only [w0, hW, div_one]
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> rfl

lemma k0_009 : k0 fix009 = 1 / 5 := by
  simp only [k0, W0, fix009, Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr]
  norm_num

lemma hold_eta (w : Inst 1 1 → ℝ) (h : w (Sum.inl 0) = 3 / 10) : w = hold (w (Sum.inr 0)) := by
  funext i
  rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;> simp [hold, h]

lemma tau_hold (p : ℝ) : tau fix009 (hold p - w0 fix009)
    = 1 / 2000 * (max (p - 1 / 2) 0 + max (-(p - 1 / 2)) 0) := by
  rw [w0_009]
  simp only [tau, Fintype.sum_sum_type, Fin.sum_univ_one, hold, fix009, Pi.sub_apply, Sum.elim_inl,
    Sum.elim_inr, sub_self, neg_zero, max_self, mul_zero, add_zero, zero_add]
  ring

/-- The fixture's score on the ETF-only holdings. -/
lemma score_hold (p : ℝ) (θ : Fin 3 → ℝ) : score fix009 (hold p) (toPar θ)
    = θ 0 * (3 / 10 + p) + θ 1 * (3 / 20) + θ 2 * (3 / 10)
      - (54 / 1000000 * (3 / 10) ^ 2 + 85 / 1000000 * (3 / 10) * p + 145 / 4000000 * p ^ 2)
      - 1 / 2000 * (max (p - 1 / 2) 0 + max (-(p - 1 / 2)) 0) := by
  rw [score, quad009, tau_hold]
  simp only [exposure, active, etf, hold, fix009, toPar, dotProduct, mulVec, Fin.sum_univ_one,
    Fin.sum_univ_two, transpose_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Pi.zero_apply]
  ring

/-- The cash-exhausting purchase beats every other ETF-only holding on `Θ₄`, strictly. -/
lemma hold_best {θ : Fin 3 → ℝ} (hθ : θ ∈ box009) {p : ℝ} (_hp0 : 0 ≤ p) (hpc : p ≤ 2801 / 4002) :
    (2801 / 4002 - p) * (2600957 / 276000000) ≤
      score fix009 (hold (2801 / 4002)) (toPar θ) - score fix009 (hold p) (toPar θ) := by
  obtain ⟨h1, -, -, -, -, -⟩ := hθ
  rw [score_hold, score_hold]
  rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 2801 / 4002 - 1 / 2),
    max_eq_right (by norm_num : -((2801 : ℝ) / 4002 - 1 / 2) ≤ 0)]
  have hab : max (p - 1 / 2) 0 + max (-(p - 1 / 2)) 0 ≥ p - 1 / 2 := by
    rcases le_total 0 (p - 1 / 2) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; linarith
    · rw [max_eq_right h, max_eq_left (by linarith)]; linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2801 / 4002 - p) (by linarith : (0 : ℝ) ≤ θ 0 - 1 / 100),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2801 / 4002 - p) (by linarith : (0 : ℝ) ≤ 2801 / 4002 - p)]

lemma E009 {w : Inst 1 1 → ℝ} (hw : w ∈ E fix009) :
    w = hold (w (Sum.inr 0)) ∧ 0 ≤ w (Sum.inr 0) ∧ w (Sum.inr 0) ≤ 2801 / 4002 := by
  have ha : w (Sum.inl 0) = 3 / 10 := by
    have := congrFun hw.2 0
    simp only [active] at this
    rw [this, w0_009]; rfl
  have he := hold_eta w ha
  refine ⟨he, (hw.1.1 (Sum.inr 0)).1, ?_⟩
  have hc := hw.1.2
  rw [he] at hc
  simp only [cash] at hc
  rw [tau_hold, k0_009, w0_009] at hc
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, hold, Sum.elim_inl,
    Sum.elim_inr, sub_self, zero_add] at hc
  rcases le_total 0 (w (Sum.inr 0) - 1 / 2) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)] at hc; linarith
  · linarith

lemma hold_mem : hold (2801 / 4002) ∈ E fix009 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
      simp [hold, fix009] <;> norm_num
  · simp only [cash]
    rw [tau_hold, k0_009, w0_009]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_one, hold, Sum.elim_inl,
      Sum.elim_inr, sub_self, zero_add]
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 2801 / 4002 - 1 / 2),
      max_eq_right (by norm_num : -((2801 : ℝ) / 4002 - 1 / 2) ≤ 0)]
    norm_num
  · funext j; rw [w0_009]; rfl

lemma max009 {θ : Fin 3 → ℝ} (hθ : θ ∈ box009) :
    maximizers (fun v => score fix009 v (toPar θ)) (E fix009) = {hold (2801 / 4002)} := by
  refine Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨he, hp0, hpc⟩ := E009 hw.1
    have hle := hw.2 _ hold_mem
    have hb := hold_best hθ hp0 hpc
    rw [he] at hle
    simp only at hle
    have : w (Sum.inr 0) = 2801 / 4002 := by
      by_contra hne
      have hlt : w (Sum.inr 0) < 2801 / 4002 := lt_of_le_of_ne hpc hne
      nlinarith
    rw [Set.mem_singleton_iff, he, this]
  · rw [Set.mem_singleton_iff.mp hw]
    refine ⟨hold_mem, fun v hv => ?_⟩
    obtain ⟨he, hp0, hpc⟩ := E009 hv
    rw [he]
    have := hold_best hθ hp0 hpc
    show score fix009 (hold (v (Sum.inr 0))) (toPar θ) ≤ score fix009 (hold (2801 / 4002)) (toPar θ)
    nlinarith

theorem fixture : Fixture := by
  refine ⟨⟨fun i => ?_, fun _ => by norm_num [fix009], ?_, by norm_num [fix009], fun z hz => ?_⟩,
    hold_mem, fun θ hθ => ?_, fun θ => ?_, fun S _ D h0 hcap => ?_⟩
  · rcases i with k | k <;> simp [fix009]
  · refine ⟨fun i => ?_, ?_⟩
    · rw [w0_009]
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _ <;>
        simp [hold, fix009] <;> norm_num
    · rw [Novel.M2ActionClassesProof.cash_w0, k0_009]; norm_num
  · rw [quad009]
    have hne : z (Sum.inl 0) ≠ 0 ∨ z (Sum.inr 0) ≠ 0 := by
      by_contra h; push Not at h
      apply hz; funext i
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
      · exact h.1
      · exact h.2
    rcases hne with h | h
    · nlinarith [sq_nonneg (z (Sum.inl 0) + 85 / 108 * z (Sum.inr 0)), sq_pos_of_ne_zero h,
        sq_nonneg (z (Sum.inr 0))]
    · nlinarith [sq_nonneg (z (Sum.inl 0) + 85 / 108 * z (Sum.inr 0)), sq_pos_of_ne_zero h]
  · have hm := max009 hθ
    have hv : vHatE fix009 θ = hold (2801 / 4002) := by
      rw [vHatE, hm, Novel.M4CurvatureCertificateProof.lexSel_single]
    refine ⟨hv, ?_⟩
    have hmem : hold (2801 / 4002) ∈ maximizers (fun v => score fix009 v (toPar θ)) (E fix009) := by
      rw [hm]; rfl
    exact sSup_max hmem
  · refine ⟨θ 0 - 51 / 2000000 - 145 / 2000000 * (2801 / 4002) - 1 / 2000, ?_, fun hθ => ?_,
      fun h => ?_⟩
    · have hpoly : HasDerivAt (fun p : ℝ => θ 0 * (3 / 10 + p) + θ 1 * (3 / 20) + θ 2 * (3 / 10)
          - (54 / 1000000 * (3 / 10) ^ 2 + 85 / 1000000 * (3 / 10) * p + 145 / 4000000 * p ^ 2)
          - 1 / 2000 * (p - 1 / 2))
          (θ 0 - 51 / 2000000 - 145 / 2000000 * (2801 / 4002) - 1 / 2000) (2801 / 4002) := by
        have h1 := ((hasDerivAt_id (2801 / 4002 : ℝ)).const_add (3 / 10)).const_mul (θ 0)
        have h2 := ((hasDerivAt_id (2801 / 4002 : ℝ)).const_mul (85 / 1000000 * (3 / 10))).const_add
          (54 / 1000000 * (3 / 10) ^ 2)
        have h3 := ((hasDerivAt_id (2801 / 4002 : ℝ)).pow 2).const_mul (145 / 4000000)
        have h4 := ((hasDerivAt_id (2801 / 4002 : ℝ)).sub_const (1 / 2)).const_mul (1 / 2000)
        convert ((h1.add_const (θ 1 * (3 / 20) + θ 2 * (3 / 10))).sub (h2.add h3)).sub h4 using 1
        · funext p; simp only [id, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring
        · simp only [id]; norm_num; ring
      refine hpoly.congr_of_eventuallyEq ?_
      have hev : ∀ᶠ p in nhds (2801 / 4002 : ℝ), (1 / 2 : ℝ) < p := lt_mem_nhds (by norm_num)
      filter_upwards [hev] with p hp
      rw [score_hold, max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · obtain ⟨h1, -⟩ := hθ; norm_num at h1 ⊢; linarith
    · rw [h]; norm_num
  · refine Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · have hp := hw.1.1 (Sum.inr 0)
      have hp0 := h0.1 (Sum.inr 0)
      rw [hcap] at hp hp0
      rw [Set.mem_singleton_iff]
      funext i
      rcases i with k | k <;> obtain rfl : k = 0 := Subsingleton.elim _ _
      · exact congrFun hw.2 0
      · linarith [hp.1, hp.2, hp0.1, hp0.2]
    · rw [Set.mem_singleton_iff.mp hw]; exact Novel.M4CurvatureCertificateProof.w0_mem_E h0

end Fixture

/-- Claim 020, parts 1-5. -/
theorem proof : Standalone.M4FiniteComparatorFacesIff.statement :=
  ⟨facesFinite, linearReduction, errorSet, finiteContrasts, curvatureDeficit, familyDeficit,
    exactIff, fixture⟩

end

end Novel.M4FiniteComparatorFacesIffProof

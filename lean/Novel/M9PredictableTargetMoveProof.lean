import Novel.M7TwoReviewsBindingBudgetProof
import Standalone.M9PredictableTargetMove

/-!
# Claim 114: proof

1a is linear algebra, plus the block moments of the innovation `φ k (y - m)` under finite laws: mean
zero, variance `φ² k² (p + s) = φ² (p - p^u)`, and independent blocks. 1b is entrywise algebra of
`G diag(Δ) G'`. Part 2 moves the sum through the involution: `D = P(u > δ)`, so
`U - D = P(-δ < u ≤ δ)`. For 3a-3b, the myopic root maximizes today's score and cost over the root
polyhedron, and with tomorrow's budget slack claim 044's supergradient of `V_1` is `s(z)` alone. So
the root objective lies below the tangent plane of slopes `S_j`. An optimal policy's root maximizes
the root objective (`V_1` is attained, claim 044's part 1).
-/

namespace Novel.M9PredictableTargetMoveProof

open Standalone.M7TwoReviewsBindingBudget Standalone.M8WorkedLearningExample
open Standalone.M9PredictableTargetMove Finset Matrix
open Novel.M7TwoReviewsBindingBudgetProof

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Part 1a -/

theorem decomposition : Decomposition := by
  intro I T lh ah pl pa yl ya A0 A1
  dsimp only
  have hμ : muP I (mNext T.φl T.lb lh pl I.sf2 yl) (mNext T.φa T.ab ah pa I.sA2 ya) =
      predVec I T lh ah + muP I lh ah +
        innovVec I (T.φl * (filt lh pl I.sf2 yl - lh)) (T.φa * (filt ah pa I.sA2 ya - ah)) := by
    funext i; fin_cases i <;> simp [muP, predVec, innovVec, mNext] <;> ring
  rw [hμ, mulVec_add, mulVec_add, sub_mulVec]
  abel

section Moments

variable {Θ E Θ' E' : Type} [Fintype Θ] [Fintype E] [Fintype Θ'] [Fintype E']

lemma block_mean {w : Θ → ℝ} {θ : Θ → ℝ} {v : E → ℝ} {z : E → ℝ} {m p s : ℝ}
    (hL : BlockLaw w θ v z m p s) :
    ∑ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) = 0 := by
  obtain ⟨_, hw1, hwθ, _, _, hv1, hvz, _⟩ := hL
  have : ∀ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) =
      gain p s * (w a * θ a - m * w a) * ∑ e, v e + gain p s * w a * ∑ e, v e * z e := fun a => by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by simp only [filt]; ring
  simp only [this, hv1, hvz, mul_one, mul_zero, add_zero]
  rw [← mul_sum, sum_sub_distrib, ← mul_sum, hwθ, hw1]; ring

lemma block_var {w : Θ → ℝ} {θ : Θ → ℝ} {v : E → ℝ} {z : E → ℝ} {m p s : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hL : BlockLaw w θ v z m p s) :
    ∑ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) ^ 2 = p - postVar p s := by
  obtain ⟨_, hw1, hwθ, hwp, _, hv1, hvz, hvs⟩ := hL
  have : ∀ a, ∑ e, w a * v e * (filt m p s (θ a + z e) - m) ^ 2 =
      gain p s ^ 2 * (w a * (θ a - m) ^ 2 * ∑ e, v e + 2 * w a * (θ a - m) * ∑ e, v e * z e +
        w a * ∑ e, v e * z e ^ 2) := fun a => by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun e _ => by simp only [filt]; ring
  simp only [this, hv1, hvz, hvs, mul_one, mul_zero, add_zero]
  rw [← mul_sum, sum_add_distrib, ← sum_mul, hwp, hw1]
  have h : p + s ≠ 0 := by positivity
  simp only [postVar, gain]; field_simp; ring

lemma block_one {w : Θ → ℝ} {θ : Θ → ℝ} {v : E → ℝ} {z : E → ℝ} {m p s : ℝ}
    (hL : BlockLaw w θ v z m p s) : ∑ a, ∑ e, w a * v e * 1 = 1 := by
  obtain ⟨_, hw1, _, _, _, hv1, _, _⟩ := hL
  simp only [mul_one, ← mul_sum, hv1, hw1]

lemma s4_sep (w : Θ → ℝ) (v : E → ℝ) (w' : Θ' → ℝ) (v' : E' → ℝ) (c : ℝ) (F : Θ → E → ℝ)
    (G : Θ' → E' → ℝ) :
    ∑ a, ∑ e, ∑ a', ∑ e', w a * v e * w' a' * v' e' * (c * (F a e * G a' e')) =
      c * ((∑ a, ∑ e, w a * v e * F a e) * ∑ a', ∑ e', w' a' * v' e' * G a' e') := by
  rw [sum_mul, mul_sum]; refine sum_congr rfl fun a _ => ?_
  rw [sum_mul, mul_sum]; refine sum_congr rfl fun e _ => ?_
  rw [mul_sum, mul_sum]; refine sum_congr rfl fun a' _ => ?_
  rw [mul_sum, mul_sum]; exact sum_congr rfl fun e' _ => by ring

theorem innovMoments : InnovMoments := by
  intro Θ E Θ' E' _ _ _ _ w θ v z w' θ' v' z' m p s m' p' s' φ φ' M hp hs hp' hs' hL hL'
  dsimp only
  have mX := block_mean hL
  have mY := block_mean hL'
  have vX := block_var hp hs hL
  have vY := block_var hp' hs' hL'
  have oX := block_one hL
  have oY := block_one hL'
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have e : ∀ a e a' e', w a * v e * w' a' * v' e' *
        ∑ k, M i k * ![φ * (filt m p s (θ a + z e) - m), φ' * (filt m' p' s' (θ' a' + z' e') - m')] k =
        w a * v e * w' a' * v' e' * ((M i 0 * φ) * ((filt m p s (θ a + z e) - m) * 1)) +
          w a * v e * w' a' * v' e' * ((M i 1 * φ') * (1 * (filt m' p' s' (θ' a' + z' e') - m'))) :=
      fun a e a' e' => by simp [Fin.sum_univ_two]; ring
    simp only [e, sum_add_distrib]
    rw [s4_sep, s4_sep, mX, mY, oX, oY]; ring
  · have e : ∀ a e a' e', w a * v e * w' a' * v' e' *
        ((∑ k, M i k * ![φ * (filt m p s (θ a + z e) - m), φ' * (filt m' p' s' (θ' a' + z' e') - m')] k) *
          (∑ k, M j k * ![φ * (filt m p s (θ a + z e) - m), φ' * (filt m' p' s' (θ' a' + z' e') - m')] k)) =
        w a * v e * w' a' * v' e' * ((M i 0 * M j 0 * φ ^ 2) * ((filt m p s (θ a + z e) - m) ^ 2 * 1)) +
          w a * v e * w' a' * v' e' * ((M i 0 * M j 1 + M i 1 * M j 0) * φ * φ' *
            ((filt m p s (θ a + z e) - m) * (filt m' p' s' (θ' a' + z' e') - m'))) +
          w a * v e * w' a' * v' e' * ((M i 1 * M j 1 * φ' ^ 2) *
            (1 * (filt m' p' s' (θ' a' + z' e') - m') ^ 2)) :=
      fun a e a' e' => by simp [Fin.sum_univ_two]; ring
    simp only [e, sum_add_distrib]
    rw [s4_sep, s4_sep, s4_sep, vX, vY, oX, oY, mX]; ring

end Moments

/-! ### Part 1b -/

theorem width : Width := by
  intro I φ q p s
  refine ⟨by simp only [pNext]; ring, fun pl pa pl' pa' => ⟨⟨?_, ?_, ?_, ?_⟩, fun h1 h2 => ?_,
    fun h1 h2 => ?_, fun h1 h2 => by rw [h1, h2], fun hb => ?_⟩⟩
  · simp [SigP]; ring
  · simp [SigP]; ring
  · simp [SigP]; ring
  · simp [SigP]; ring
  · simp [SigP]
    constructor <;> nlinarith [sq_nonneg I.bA, sq_nonneg I.bE]
  · simp [SigP]
    constructor <;> nlinarith [sq_nonneg I.bA, sq_nonneg I.bE]
  · simp [SigP]
    have hb2 : 0 < I.bE ^ 2 := by positivity
    constructor
    · intro h; by_contra hc; push Not at hc; nlinarith
    · intro h; nlinarith

theorem perInstrument : PerInstrument := by
  intro I pl pa pl' pa'
  simp only [SigP, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp
  constructor <;> constructor <;> intro h <;> linarith

section Conv

variable {φ q s : ℝ}

lemma pv_eq {p : ℝ} (hs : 0 < s) (hp : 0 ≤ p) : postVar p s = s * p / (p + s) := by
  have : p + s ≠ 0 := by positivity
  simp only [postVar, gain]; field_simp; ring

lemma T_mono (hs : 0 < s) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : pNext φ q a s ≤ pNext φ q b s := by
  unfold pNext
  rw [pv_eq hs ha, pv_eq hs (ha.trans hab)]
  have : s * a / (a + s) ≤ s * b / (b + s) := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg s)]
  nlinarith [sq_nonneg φ]

lemma T_nonneg (hs : 0 < s) (hq : 0 ≤ q) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ pNext φ q p s := by
  unfold pNext; rw [pv_eq hs hp]; positivity

lemma T_le (hs : 0 < s) {p : ℝ} (hp : 0 ≤ p) : pNext φ q p s ≤ φ ^ 2 * s + q := by
  unfold pNext; rw [pv_eq hs hp]
  have : s * p / (p + s) ≤ s := by rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith [sq_nonneg φ]

lemma T_cont (hs : 0 < s) {p : ℝ} (hp : 0 ≤ p) : ContinuousAt (fun p => pNext φ q p s) p := by
  have : p + s ≠ 0 := by positivity
  unfold pNext postVar gain
  fun_prop (disch := assumption)

end Conv

theorem convergence : Convergence := by
  intro φ q s p0 hs hq hp0
  set T : ℝ → ℝ := fun p => pNext φ q p s with hT
  have hsucc : ∀ n, T^[n + 1] p0 = T (T^[n] p0) := fun n => Function.iterate_succ_apply' T n p0
  have hnn : ∀ n, 0 ≤ T^[n] p0 := fun n => by
    induction n with
    | zero => exact hp0
    | succ n ih => rw [hsucc]; exact T_nonneg hs hq ih
  have hbd : ∀ n, T^[n] p0 ≤ max p0 (φ ^ 2 * s + q) := fun n => by
    cases n with
    | zero => exact le_max_left _ _
    | succ n => rw [hsucc]; exact (T_le hs (hnn n)).trans (le_max_right _ _)
  refine ⟨?_, fun hc a b ha hb hfa hfb => ?_⟩
  · -- a monotone bounded sequence converges
    have hlim : ∃ L, Filter.Tendsto (fun n => T^[n] p0) Filter.atTop (nhds L) := by
      by_cases h : p0 ≤ T p0
      · have hmono : Monotone (fun n => T^[n] p0) := monotone_nat_of_le_succ fun n => by
          induction n with
          | zero => simpa using h
          | succ n ih =>
            show T^[n + 1] p0 ≤ T^[n + 1 + 1] p0
            rw [hsucc (n + 1)]
            conv_lhs => rw [hsucc n]
            exact T_mono hs (hnn n) ih
        exact ⟨_, tendsto_atTop_ciSup hmono ⟨_, fun _ ⟨n, hn⟩ => by rw [← hn]; exact hbd n⟩⟩
      · push Not at h
        have hanti : Antitone (fun n => T^[n] p0) := antitone_nat_of_succ_le fun n => by
          induction n with
          | zero => simpa using h.le
          | succ n ih =>
            show T^[n + 1 + 1] p0 ≤ T^[n + 1] p0
            rw [hsucc (n + 1)]
            conv_rhs => rw [hsucc n]
            exact T_mono hs (hnn (n + 1)) ih
        exact ⟨_, tendsto_atTop_ciInf hanti ⟨0, fun _ ⟨n, hn⟩ => by rw [← hn]; exact hnn n⟩⟩
    obtain ⟨L, hL⟩ := hlim
    have hL0 : 0 ≤ L := ge_of_tendsto' hL hnn
    have h1 : Filter.Tendsto (fun n => T (T^[n] p0)) Filter.atTop (nhds (T L)) :=
      (T_cont hs hL0).tendsto.comp hL
    have h2 : Filter.Tendsto (fun n => T (T^[n] p0)) Filter.atTop (nhds L) := by
      have := (Filter.tendsto_add_atTop_iff_nat 1).mpr hL
      simpa [hsucc] using this
    exact ⟨L, hL0, tendsto_nhds_unique h1 h2, hL⟩
  · -- two nonnegative fixed points of `p² + (s - φ²s - q) p - q s = 0` coincide
    have ea : a * (a + s) = φ ^ 2 * s * a + q * (a + s) := by
      have := hfa; unfold pNext at this; rw [pv_eq hs ha] at this
      have h' : a + s ≠ 0 := by positivity
      field_simp at this; linarith
    have eb : b * (b + s) = φ ^ 2 * s * b + q * (b + s) := by
      have := hfb; unfold pNext at this; rw [pv_eq hs hb] at this
      have h' : b + s ≠ 0 := by positivity
      field_simp at this; linarith
    by_contra hne
    have hsum : a + b + s - φ ^ 2 * s - q = 0 := by
      have : (a - b) * (a + b + s - φ ^ 2 * s - q) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    have hprod : a * b = -(q * s) := by nlinarith
    rcases hc with hq' | hφ
    · nlinarith [mul_nonneg ha hb, mul_pos hq' hs]
    · have hq0 : q = 0 := by nlinarith [mul_nonneg ha hb, mul_nonneg hq hs.le]
      nlinarith

theorem mixedBlocks : MixedBlocks := by
  intro I hA hE pl pa
  simp only [SigP, Matrix.cons_val_zero, Matrix.cons_val_one, hA, hE]
  constructor <;> nlinarith

/-! ### Part 2 -/

lemma sum_invol {Ω : Type} [Fintype Ω] {σ : Ω → Ω} (hσ : ∀ ω, σ (σ ω) = ω) (f : Ω → ℝ) :
    ∑ ω, f (σ ω) = ∑ ω, f ω :=
  Equiv.sum_comp (Function.Involutive.toPerm σ hσ) f

theorem tilt : Tilt := by
  intro Ω _ π u σ hπ h1 hσ hπσ huσ δ
  dsimp only
  -- `P(u < a) = P(u > -a)` through the involution
  have hsym : ∀ a : ℝ, prob π u (fun x => x < a) = prob π u (fun x => -a < x) := fun a => by
    unfold prob
    rw [← sum_invol hσ (fun ω => if u ω < a then π ω else 0)]
    refine sum_congr rfl fun ω _ => ?_
    simp only [huσ, hπσ]
    by_cases h : -u ω < a
    · rw [ite_eq_left h, ite_eq_left (by linarith)]
    · rw [ite_eq_right h, ite_eq_right (by linarith)]
  have hW0 : 0 ≤ prob π u (fun x => -|δ| < x ∧ x ≤ |δ|) :=
    sum_nonneg fun ω _ => by split_ifs <;> [exact hπ ω; exact le_rfl]
  have hsub : ∀ a b : ℝ, a ≤ b → prob π u (fun x => a < x) - prob π u (fun x => b < x) =
      prob π u (fun x => a < x ∧ x ≤ b) := fun a b hab => by
    unfold prob; rw [← sum_sub_distrib]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h1 : a < u ω <;> by_cases h2 : b < u ω <;> simp [h1, h2]
    all_goals linarith
  have hU1 : 0 ≤ δ → prob π u (fun x => -δ < x) - prob π u (fun x => x < -δ) =
      prob π u (fun x => -|δ| < x ∧ x ≤ |δ|) := fun hd => by
    rw [hsym, neg_neg, abs_of_nonneg hd]; exact hsub _ _ (by linarith)
  have hU2 : δ ≤ 0 → prob π u (fun x => -δ < x) - prob π u (fun x => x < -δ) =
      -prob π u (fun x => -|δ| < x ∧ x ≤ |δ|) := fun hd => by
    rw [hsym, neg_neg, abs_of_nonpos hd, neg_neg, ← hsub _ _ (by linarith)]; ring
  have hWid : prob π u (fun x => -|δ| < x ∧ x ≤ |δ|) =
      prob π u (fun x => |x| ≤ |δ|) - prob π u (fun x => x = -|δ|) := by
    unfold prob; rw [← sum_sub_distrib]
    refine sum_congr rfl fun ω _ => ?_
    by_cases hC : u ω = -|δ|
    · have hA : ¬(-|δ| < u ω ∧ u ω ≤ |δ|) := fun h => by linarith [h.1]
      have hB : |u ω| ≤ |δ| := by rw [hC, abs_neg, abs_abs]
      rw [ite_eq_right hA, ite_eq_left hB, ite_eq_left hC, sub_self]
    · have hAB : (-|δ| < u ω ∧ u ω ≤ |δ|) ↔ |u ω| ≤ |δ| := by
        rw [abs_le]
        exact ⟨fun h => ⟨h.1.le, h.2⟩, fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm hC), h.2⟩⟩
      rw [ite_eq_right hC, sub_zero]
      by_cases hB : |u ω| ≤ |δ|
      · rw [ite_eq_left (hAB.mpr hB), ite_eq_left hB]
      · rw [ite_eq_right (fun h => hB (hAB.mp h)), ite_eq_right hB]
  refine ⟨hU1, hU2, hWid, hW0, fun hna => ?_, fun β κ c hβ hκ hc => ⟨fun hd => ?_, fun hd => ?_⟩,
    fun hs => ?_, fun hs => ?_⟩
  · rw [hWid]
    have : prob π u (fun x => x = -|δ|) = 0 :=
      sum_eq_zero fun ω _ => ite_eq_right (hna ω)
    rw [this, sub_zero]
  · rw [hU1 hd]; positivity
  · rw [hU2 hd]
    have : 0 ≤ β * κ * prob π u (fun x => -|δ| < x ∧ x ≤ |δ|) / c := by positivity
    rw [mul_neg, neg_div]; linarith
  · unfold prob; rw [← h1]
    exact sum_congr rfl fun ω _ => ite_eq_left (by linarith [(abs_lt.mp (hs ω)).1])
  · unfold prob; rw [← h1]
    exact sum_congr rfl fun ω _ => ite_eq_left (by linarith [(abs_lt.mp (hs ω)).2])

/-! ### Part 3 -/

variable {ι Z : Type} [Fintype ι] [Fintype Z]

theorem rootOpt : RootOpt := by
  intro ι Z _ _ P hP X ⟨hX, hmax⟩
  have hroot : X.1 ∈ RootSet P := ⟨hX.1, hX.2.2.1⟩
  refine ⟨hroot, fun y hy => ?_⟩
  -- attain `V_1` at every state from `y`
  have hat : ∀ z, ∃ x ∈ F1 P (carry P z y, h0 P y), V1 P z (carry P z y, h0 P y) =
      f1 P z (carry P z y, h0 P y) x := fun z => by
    obtain ⟨x, hx, -, he⟩ := V1_attain P z (dom_mem hP hy z); exact ⟨x, hx, he⟩
  choose y1 hy1 hyv using hat
  have hY : (y, y1) ∈ Feas P := ⟨hy.1, fun z => (hy1 z).1, hy.2, fun z => (hy1 z).2⟩
  have hJY : J P (y, y1) = RootObj P y := by
    unfold J RootObj; simp only [hyv]; rfl
  have hJX : J P X ≤ RootObj P X.1 := by
    unfold J RootObj
    have : ∀ z, P.q z * (Q1 P z (X.2 z) - cost P (X.2 z - carry P z X.1)) ≤
        P.q z * V1 P z (carry P z X.1, h0 P X.1) := fun z =>
      mul_le_mul_of_nonneg_left (le_V1 P z (dom_mem hP hroot z)
        (show X.2 z ∈ F1 P (carry P z X.1, h0 P X.1) from ⟨hX.2.1 z, hX.2.2.2 z⟩))
        (hP.2.2.2.2.2.2.1 z).le
    have := mul_le_mul_of_nonneg_left (sum_le_sum fun z (_ : z ∈ univ) => this z) hP.2.1.le
    linarith
  show RootObj P y ≤ RootObj P X.1
  have := hmax hY
  simp only [Set.mem_ofPred_eq] at this
  linarith

/-- The tangent plane at the myopic root, with tomorrow's budget slack. -/
lemma tangent {P : Two ι Z} (hP : Hyp P) {X : (ι → ℝ) × (Z → ι → ℝ)} {η1 : Z → ℝ} {t1 : Z → ι → ℝ}
    (hM : Myopic P X) (hT : Tomorrow P X η1 t1) (hs : ∀ z, 0 < h1 P X.1 X.2 z) {y : ι → ℝ}
    (hy : y ∈ RootSet P) :
    RootObj P y ≤ RootObj P X.1 + ∑ j, Sinc P η1 t1 j * (y j - X.1 j) := by
  have hz := eta1_zero hT hs
  have hT0 : Q0 P y - cost P (y - P.xm) ≤ Q0 P X.1 - cost P (X.1 - P.xm) := hM.2.1 hy
  have hV : ∀ z, V1 P z (carry P z y, h0 P y) ≤ V1 P z (carry P z X.1, h0 P X.1) +
      ∑ j, sval η1 t1 z j * (P.g z j * (y j - X.1 j)) := fun z => by
    have hx1 : X.2 z ∈ F1 P (carry P z X.1, h0 P X.1) := (hM.2.2 z).1
    have hsup := V1_super hP z hx1 (hT z).1 (hT z).2.1 (hT z).2.2 (dom_mem hP hy z)
    have hlow := le_V1 P z (dom_mem hP hM.1 z) hx1
    simp only [hz, zero_mul, add_zero, zero_add, one_mul] at hsup
    have e : ∑ i, t1 z i * ((carry P z y, h0 P y).1 i - (carry P z X.1, h0 P X.1).1 i) =
        ∑ j, sval η1 t1 z j * (P.g z j * (y j - X.1 j)) :=
      sum_congr rfl fun j _ => by simp only [sval, hz, carry]; ring
    rw [e] at hsup
    linarith
  have hs2 := mul_le_mul_of_nonneg_left (sum_le_sum fun z (_ : z ∈ univ) =>
    mul_le_mul_of_nonneg_left (hV z) (hP.2.2.2.2.2.2.1 z).le) hP.2.1.le
  have e : P.beta * ∑ z, P.q z * (V1 P z (carry P z X.1, h0 P X.1) +
      ∑ j, sval η1 t1 z j * (P.g z j * (y j - X.1 j))) =
      P.beta * ∑ z, P.q z * V1 P z (carry P z X.1, h0 P X.1) + ∑ j, Sinc P η1 t1 j * (y j - X.1 j) := by
    simp only [Sinc, mul_add, sum_add_distrib, mul_sum, sum_mul]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun z _ => by ring
  rw [e] at hs2
  unfold RootObj
  linarith

theorem loading : Loading := by
  intro ι Z _ _ P hP hZ X η1 t1 hM hT hs
  have hz := eta1_zero hT hs
  have htan := fun y hy => tangent hP hM hT hs (y := y) hy
  have hwq : ∀ z i, 0 < P.q z * P.g z i := fun z i =>
    mul_pos (hP.2.2.2.2.2.2.1 z) (hP.2.2.2.2.2.2.2.1 z i)
  have hsum_single : ∀ (i : ι) (y : ι → ℝ), (∀ j, j ≠ i → y j = X.1 j) →
      ∑ j, Sinc P η1 t1 j * (y j - X.1 j) = Sinc P η1 t1 i * (y i - X.1 i) := fun i y hy => by
    rw [sum_eq_single i (fun j _ hj => by rw [hy j hj, sub_self, mul_zero]) (by simp)]
  refine ⟨htan, fun i => ⟨fun hbuy hkp => ?_, fun hsell hkm => ?_⟩⟩
  · have hS : Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * P.kp i := by
      unfold Sinc; congr 1
      exact sum_congr rfl fun z _ => by
        rw [((readings ι Z P X η1 t1 hT z i).2.1 (hbuy z)), hz]; ring
    have hSp : 0 < Sinc P η1 t1 i := by
      rw [hS]; exact mul_pos hP.2.1 (sum_pos (fun z _ => mul_pos (hwq z i) hkp) univ_nonempty)
    have hdec : ∀ y ∈ RootSet P, (∀ j, j ≠ i → y j = X.1 j) → y i < X.1 i → RootObj P y < RootObj P X.1 :=
      fun y hy hyj hlt => by
        have := htan y hy
        rw [hsum_single i y hyj] at this
        nlinarith
    refine ⟨hS, hdec, fun Xd hO hXd => ?_⟩
    by_contra hlt; push Not at hlt
    obtain ⟨hr, hmax⟩ := rootOpt ι Z P hP Xd hO
    have h1 := hdec Xd.1 hr hXd hlt
    have h2 : RootObj P X.1 ≤ RootObj P Xd.1 := hmax hM.1
    linarith
  · have hS : Sinc P η1 t1 i = -(P.beta * ∑ z, P.q z * P.g z i * P.km i) := by
      unfold Sinc
      rw [← mul_neg, ← sum_neg_distrib]; congr 1
      exact sum_congr rfl fun z _ => by
        rw [((readings ι Z P X η1 t1 hT z i).2.2.1 (hsell z)), hz]; ring
    have hSn : Sinc P η1 t1 i < 0 := by
      rw [hS, neg_lt_zero]
      exact mul_pos hP.2.1 (sum_pos (fun z _ => mul_pos (hwq z i) hkm) univ_nonempty)
    have hdec : ∀ y ∈ RootSet P, (∀ j, j ≠ i → y j = X.1 j) → X.1 i < y i → RootObj P y < RootObj P X.1 :=
      fun y hy hyj hlt => by
        have := htan y hy
        rw [hsum_single i y hyj] at this
        nlinarith
    refine ⟨hS, hdec, fun Xd hO hXd => ?_⟩
    by_contra hlt; push Not at hlt
    obtain ⟨hr, hmax⟩ := rootOpt ι Z P hP Xd hO
    have h1 := hdec Xd.1 hr hXd hlt
    have h2 : RootObj P X.1 ≤ RootObj P Xd.1 := hmax hM.1
    linarith

theorem threshold : Threshold := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR hh hs i hbuy hb hc
  have hz := eta1_zero hT hs
  have h0 : η0 = 0 := by
    rcases mul_eq_zero.mp hR.2.1 with h | h
    · exact h
    · linarith
  have hxm := (hP.2.2.2.2.2.2.2.2 i).2.2.2.1
  obtain ⟨hsl, b1, b2⟩ := hR.2.2 i
  have e1 := b1 hc; have e2 := b2 (by linarith)
  have hS : Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * P.kp i := by
    unfold Sinc; congr 1
    exact sum_congr rfl fun z _ => by
      rw [((readings ι Z P X η1 t1 hT z i).2.1 (hbuy z)), hz]; ring
  have he : etaHat P η0 η1 = 0 := by simp [etaHat, h0, hz]
  rw [he, hS, hsl.2.2.1 (by linarith), ← sum_mul] at e1 e2
  linarith

theorem thresholdBound : ThresholdBound := by
  intro ι Z _ _ P hP X η0 η1 t0 t1 hT hR hh hs i
  have hz := eta1_zero hT hs
  have h0 : η0 = 0 := by
    rcases mul_eq_zero.mp hR.2.1 with h | h
    · exact h
    · linarith
  have hS : Sinc P η1 t1 i = P.beta * ∑ z, P.q z * P.g z i * t1 z i := by
    unfold Sinc; congr 1; exact sum_congr rfl fun z _ => by simp [sval, hz]
  have hwq : ∀ z, 0 < P.q z * P.g z i := fun z =>
    mul_pos (hP.2.2.2.2.2.2.1 z) (hP.2.2.2.2.2.2.2.1 z i)
  have hgap : P.beta * ∑ z, P.q z * P.g z i * P.kp i - Sinc P η1 t1 i =
      P.beta * ∑ z, P.q z * P.g z i * (P.kp i - t1 z i) := by
    rw [hS, ← mul_sub, ← sum_sub_distrib]; congr 1
    exact sum_congr rfl fun z _ => by ring
  have hterm : ∀ z, 0 ≤ P.q z * P.g z i * (P.kp i - t1 z i) := fun z =>
    mul_nonneg (hwq z).le (by linarith [((hT z).2.2 i).1.2.1])
  have hle : Sinc P η1 t1 i ≤ P.beta * ∑ z, P.q z * P.g z i * P.kp i := by
    have := mul_nonneg hP.2.1.le (sum_nonneg fun z (_ : z ∈ univ) => hterm z)
    linarith
  refine ⟨hle, fun hb hc => ?_⟩
  have hxm := (hP.2.2.2.2.2.2.2.2 i).2.2.2.1
  obtain ⟨hsl, b1, b2⟩ := hR.2.2 i
  have e1 := b1 hc; have e2 := b2 (by linarith)
  have he : etaHat P η0 η1 = 0 := by simp [etaHat, h0, hz]
  rw [he, hsl.2.2.1 (by linarith)] at e1 e2
  have hg0 : g0 P X.1 i = P.kp i - Sinc P η1 t1 i := by linarith
  have hk : (1 - P.beta * ∑ z, P.q z * P.g z i) * P.kp i =
      P.kp i - P.beta * ∑ z, P.q z * P.g z i * P.kp i := by rw [← sum_mul]; ring
  rw [hg0, hk]
  refine ⟨by linarith, ⟨fun heq => ?_, fun hall => ?_⟩⟩
  · have hsum : P.beta * ∑ z, P.q z * P.g z i * (P.kp i - t1 z i) = 0 := by linarith
    have hsum' : ∑ z, P.q z * P.g z i * (P.kp i - t1 z i) = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · linarith [hP.2.1]
      · exact h
    intro z
    have := (sum_eq_zero_iff_of_nonneg fun z (_ : z ∈ univ) => hterm z).mp hsum' z (mem_univ z)
    rcases mul_eq_zero.mp this with h | h
    · linarith [hwq z]
    · linarith
  · have : P.beta * ∑ z, P.q z * P.g z i * (P.kp i - t1 z i) = 0 := by
      simp [hall]
    linarith

theorem proof : Standalone.M9PredictableTargetMove.statement :=
  ⟨decomposition, innovMoments, width, perInstrument, convergence, mixedBlocks, tilt, loading, threshold,
    thresholdBound, rootOpt⟩

end

end Novel.M9PredictableTargetMoveProof

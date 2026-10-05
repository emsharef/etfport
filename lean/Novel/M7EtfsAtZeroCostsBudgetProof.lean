import Novel.M7FundDecisionEtfsAtZeroProof
import Novel.M7TwoStageExactnessLossProof
import Novel.M7TwoStageEtfsAtZeroProof
import Standalone.M7EtfsAtZeroCostsBudget

/-!
# Proof of claim 109

Uses the proof modules of claims 040, 041 and 104 (`depends_on` lists them, Q-04). From claim 040 it
takes part 1, the block splitting and the invertibility of `Σ_TT`. From claim 041 it takes stage 1's
complementarity. From claim 104 it takes part 0, the joint optimality criterion under AX-13.

* **Part 2.** The traded rows `μ_T - γ(Σ_TT w_T + Σ_TF w_F) = π_T` give `w_T`. Substituting into the
  fixed rows gives the Schur complement. In a fund's marginal the fixed rows' `Σ_FT Σ_TT⁻¹ π_T` moves
  onto `ρ` by the symmetry of `Σ_EE`.
-/

namespace Novel.M7EtfsAtZeroCostsBudgetProof

open Matrix Standalone.M7FundDecisionEtfsAtZero Standalone.M7EtfsAtZeroCostsBudget
open Novel.M7FundDecisionEtfsAtZeroProof

noncomputable section

variable {M N : ℕ} {P : Coord M N}

/-! ### Part 2 -/

section Part2

variable (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (F : Finset (Fin M))
include hγ hS

omit hγ in
lemma SZc_T : (SZc P F)ᵀ = ScZ P F := by
  ext i j
  have h := congrFun (congrFun (symm_of_posDef hS) i.val) j.val
  simp only [transpose_apply] at h
  simp [SZc, ScZ, transpose_apply, h]

omit hγ in
lemma Scc_inv_T : ((Scc P F)⁻¹)ᵀ = (Scc P F)⁻¹ := by
  have : (Scc P F)ᵀ = Scc P F := by
    ext i j
    have h := congrFun (congrFun (symm_of_posDef hS) i.val) j.val
    simp only [transpose_apply] at h
    simp [Scc, transpose_apply, h]
  rw [transpose_nonsing_inv, this]

omit hγ hS in
/-- The exposure's rows split into the fixed and traded blocks. -/
lemma rows_T (w : Fin M → ℝ) (j : Out F) :
    (P.Sig *ᵥ w) j = (ScZ P F *ᵥ fun k : In F => w k) j + (Scc P F *ᵥ fun k : Out F => w k) j := by
  rw [split_mulVec F]; rfl

omit hγ hS in
lemma rows_F (w : Fin M → ℝ) (j : In F) :
    (P.Sig *ᵥ w) j = (SZZ P F *ᵥ fun k : In F => w k) j + (SZc P F *ᵥ fun k : Out F => w k) j := by
  rw [split_mulVec F]; rfl

theorem explicit_of (xA : Fin N → ℝ) (xE : Fin M → ℝ) (eta : ℝ) (t : Fin M → ℝ)
    (hT : ∀ j : Out F, gE P (expo P xA xE) j = piT F eta t j) :
    (fun j : Out F => expo P xA xE j) =
        (Scc P F)⁻¹ *ᵥ ((1 / P.gamma) • ((fun j : Out F => P.mu j) - piT F eta t) -
          ScZ P F *ᵥ wF P F xA xE) ∧
      (∀ j : In F, gE P (expo P xA xE) j =
        (muZc P F + SZc P F *ᵥ ((Scc P F)⁻¹ *ᵥ piT F eta t) - P.gamma • (schur P F *ᵥ wF P F xA xE)) j) ∧
      (∀ i, gA P xA (expo P xA xE) i = alphaFT P F eta t xE i - P.gamma * (VZ P F *ᵥ xA) i) ∧
      ∀ i (ti : ℝ), (gA P xA (expo P xA xE) i = eta + (1 + eta) * ti ↔
        P.alt i + rF P F i ⬝ᵥ muZc P F - P.gamma * (rF P F i ⬝ᵥ (schur P F *ᵥ xF F xE)) -
          P.gamma * (VZ P F *ᵥ xA) i + (1 + eta) * (rho P F i ⬝ᵥ fun j => t j) -
          eta * (1 - rho P F i ⬝ᵥ fun _ => 1) = (1 + eta) * ti) := by
  set W := expo P xA xE
  set wT : Out F → ℝ := fun j => W j
  set wFv : In F → ℝ := wF P F xA xE
  have hwF : wFv = fun k : In F => W k := rfl
  have hunit := scc_unit hS F
  have hγ0 : P.gamma ≠ 0 := hγ.ne'
  -- 2a
  have hScc : Scc P F *ᵥ wT = (1 / P.gamma) • ((fun j : Out F => P.mu j) - piT F eta t) - ScZ P F *ᵥ wFv := by
    funext j
    have h := hT j
    simp only [gE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [rows_T F W j] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wT, hwF]
    field_simp
    linarith
  have h2a : wT = (Scc P F)⁻¹ *ᵥ ((1 / P.gamma) • ((fun j : Out F => P.mu j) - piT F eta t) -
      ScZ P F *ᵥ wFv) := by
    rw [← hScc, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  -- 2b
  have h2b : ∀ j : In F, gE P W j =
      (muZc P F + SZc P F *ᵥ ((Scc P F)⁻¹ *ᵥ piT F eta t) - P.gamma • (schur P F *ᵥ wFv)) j := by
    intro j
    simp only [gE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [rows_F F W j, ← hwF]
    change P.mu j - P.gamma * ((SZZ P F *ᵥ wFv) j + (SZc P F *ᵥ wT) j) = _
    rw [h2a]
    simp only [muZc, schur, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mulVec,
      mulVec_sub, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc]
    field_simp
    ring
  -- 2c
  have hsplitQ : ∀ i, (P.Qᵀ *ᵥ gE P W) i = rT P F i ⬝ᵥ (fun j : Out F => gE P W j) +
      rF P F i ⬝ᵥ (fun j : In F => gE P W j) := by
    intro i
    simp only [mulVec, dotProduct, transpose_apply, rT, rF]
    rw [split_sum F]; ring
  have hTvals : (fun j : Out F => gE P W j) = piT F eta t := funext hT
  have hFvals : (fun j : In F => gE P W j) =
      muZc P F + SZc P F *ᵥ ((Scc P F)⁻¹ *ᵥ piT F eta t) - P.gamma • (schur P F *ᵥ wFv) := funext h2b
  have hmove : ∀ i, rF P F i ⬝ᵥ (SZc P F *ᵥ ((Scc P F)⁻¹ *ᵥ piT F eta t)) =
      ((Scc P F)⁻¹ *ᵥ (ScZ P F *ᵥ rF P F i)) ⬝ᵥ piT F eta t := by
    intro i
    rw [dotProduct_mulVec, dotProduct_mulVec, ← mulVec_transpose, ← mulVec_transpose, SZc_T hS F,
      Scc_inv_T hS F]
  have hwFsplit : wFv = QZ P F *ᵥ xA + xF F xE := by
    funext j; simp [wFv, wF, expo, QZ, xF, mulVec, dotProduct, add_comm]
  have hVZ : ∀ i, rF P F i ⬝ᵥ (schur P F *ᵥ (QZ P F *ᵥ xA)) = (((QZ P F)ᵀ * schur P F * QZ P F) *ᵥ xA) i := by
    intro i
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    simp [mulVec, dotProduct, transpose_apply, rF, QZ]
  have h2c : ∀ i, gA P xA W i = alphaFT P F eta t xE i - P.gamma * (VZ P F *ᵥ xA) i := by
    intro i
    simp only [gA, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsplitQ, hTvals, hFvals, hwFsplit]
    simp only [alphaFT, rho, VZ, add_mulVec, dotProduct_add, dotProduct_sub, add_dotProduct,
      dotProduct_smul, smul_eq_mul, mulVec_add, Pi.add_apply]
    rw [hmove, hVZ]
    ring
  have hrho : ∀ i, rho P F i ⬝ᵥ piT F eta t =
      eta * (rho P F i ⬝ᵥ fun _ => 1) + (1 + eta) * (rho P F i ⬝ᵥ fun j => t j) := by
    intro i
    simp only [piT, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨h2a, h2b, h2c, fun i ti => ?_⟩
  rw [h2c i]
  simp only [alphaFT]
  rw [hrho i]
  constructor <;> intro h <;> linarith

end Part2

/-! ### Part 2d -/

lemma atZero_of (hγ : 0 < P.gamma) (hS : P.Sig.PosDef) (xA : Fin N → ℝ) (xE : Fin M → ℝ) (j : Fin M)
    (eta kp ζ : ℝ) (hx : 0 ≤ xE j) (hζ : 0 ≤ ζ) (hζ0 : 0 < xE j → ζ = 0)
    (hline : gE P (expo P xA xE) j = thr eta kp - ζ) :
    (xE j = 0 → gE P (expo P xA xE) j ≤ thr eta kp) ∧
    (0 < xE j → gE P (expo P xA xE) j = thr eta kp) ∧
    (gE P (expo P xA xE) j < thr eta kp → xE j = 0) ∧
    (xE j = 0 ↔ gE P (expo P xA xE) j + P.gamma * P.Sig j j * xE j ≤ thr eta kp) := by
  have hd : 0 < P.Sig j j := hS.diag_pos
  have hb : 0 < xE j → gE P (expo P xA xE) j = thr eta kp := fun h => by rw [hline, hζ0 h, sub_zero]
  refine ⟨fun _ => by linarith, hb, fun hlt => ?_, ⟨fun h0 => by rw [h0]; linarith, fun h => ?_⟩⟩
  · by_contra hne
    have := hb (lt_of_le_of_ne hx (Ne.symm hne)); linarith
  · by_contra hne
    have hpos : 0 < xE j := lt_of_le_of_ne hx (Ne.symm hne)
    have := hb hpos
    have : 0 < P.gamma * P.Sig j j * xE j := by positivity
    linarith

theorem atZeroTests : AtZeroTests := fun _ _ _ hγ hS xA xE j eta kp ζ hx hζ hζ0 hline =>
  atZero_of hγ hS xA xE j eta kp ζ hx hζ hζ0 hline

/-! ### Part 2e -/

theorem bracket : Bracket := by
  intro M F kpE kmE ρ t eta heta ht
  have h1 : -hP F kpE kmE ρ ≤ ρ ⬝ᵥ fun j => t j := by
    simp only [hP, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨hl, hu⟩ := ht j
    rcases le_total 0 (ρ j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -ρ j ≤ 0)]; nlinarith
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -ρ j)]; nlinarith
  have h2 : (ρ ⬝ᵥ fun j => t j) ≤ hM F kpE kmE ρ := by
    simp only [hM, dotProduct]
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨hl, hu⟩ := ht j
    rcases le_total 0 (ρ j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -ρ j ≤ 0)]; nlinarith
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -ρ j)]; nlinarith
  have h1e : (0 : ℝ) ≤ 1 + eta := by linarith
  exact ⟨by nlinarith, mul_le_mul_of_nonneg_left h2 h1e⟩

/-! ### Part 3 -/

theorem oneOne : OneOne := by
  intro P hγ hS a p eta tE tA
  have hgE : gE P (expo P (fun _ => a) (fun _ => p)) 0 = P.mu 0 - P.gamma * P.Sig 0 0 * (p + P.Q 0 0 * a) := by
    simp [gE, expo, mulVec, dotProduct]; ring
  have hgA : gA P (fun _ => a) (expo P (fun _ => a) (fun _ => p)) 0 =
      P.alt 0 - P.gamma * P.V 0 0 * a + P.Q 0 0 * gE P (expo P (fun _ => a) (fun _ => p)) 0 := by
    simp [gA, mulVec, dotProduct, transpose_apply]; ring
  refine ⟨fun hT => ?_, ?_, fun kp ζ hp hζ hζ0 hline => ?_⟩
  · rw [hgA, hT]; constructor <;> intro h <;> linarith
  · rw [hgA, hgE]; constructor <;> intro h <;> nlinarith
  · have h := (atZero_of hγ hS (fun _ => a) (fun _ => p) 0 eta kp ζ hp hζ hζ0 hline).2.2.2
    rw [hgE] at h
    have e : P.mu 0 - P.gamma * P.Sig 0 0 * (p + P.Q 0 0 * a) + P.gamma * P.Sig 0 0 * p =
        P.mu 0 - P.gamma * P.Sig 0 0 * P.Q 0 0 * a := by ring
    rw [e] at h
    exact h

/-! ### Part 4b -/

theorem etfLines : EtfLines := by
  intro eta ζ kp km t heta hζ hkp hkm hline
  refine ⟨fun ht => ?_, fun ht => by rw [ht] at hline; linarith, fun hl _ => ?_⟩
  · rw [ht] at hline
    have h1 : 0 ≤ (1 + eta) * kp := mul_nonneg (by linarith) hkp
    have hz : ζ = 0 := by linarith
    have he : eta = 0 := by linarith
    refine ⟨he, ?_, hz⟩
    rw [he] at h1 hline; linarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith

/-! ### Part 4c -/

section Soft

variable (hγ : 0 < P.gamma) (hS : P.Sig.PosDef)
include hγ hS

lemma GE_mid {w v : Fin M → ℝ} (hne : w ≠ v) :
    (GE P w + GE P v) / 2 < GE P ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • v) := by
  have hs := symm_of_posDef hS
  have e : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • v = w + (1 / 2 : ℝ) • (v - w) := by module
  have h2 := GE_add hs w (v - w)
  rw [add_sub_cancel] at h2
  rw [e, GE_add hs, h2]
  have hq : 0 < qf P.Sig (v - w) := by
    rcases lt_or_eq_of_le (qf_nonneg hS (v - w)) with h | h
    · exact h
    · exact absurd (eq_of_qf hS h.symm.le) (sub_ne_zero.2 hne.symm)
  have hsc : qf P.Sig ((1 / 2 : ℝ) • (v - w)) = 1 / 4 * qf P.Sig (v - w) := by
    simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  rw [hsc, dotProduct_smul, smul_eq_mul]
  nlinarith

omit hγ in
/-- `G_E` around `w_s`: `G_E(e) = G_E(w_s) + ν'(e - w_s) - (γ/2)(e - w_s)'Σ(e - w_s)`. -/
lemma GE_around (ws e : Fin M → ℝ) :
    GE P e = GE P ws + (P.mu - P.gamma • (P.Sig *ᵥ ws)) ⬝ᵥ (e - ws) -
      P.gamma / 2 * ((e - ws) ⬝ᵥ (P.Sig *ᵥ (e - ws))) := by
  have h := GE_add (symm_of_posDef hS) ws (e - ws)
  rw [add_sub_cancel] at h
  rw [h]
  simp only [zof, qf, sub_dotProduct]
  ring

omit hγ hS in
lemma expo_mid (p q : (Fin N → ℝ) × (Fin M → ℝ)) :
    expo P ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).1 ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).2 =
      (1 / 2 : ℝ) • expo P p.1 p.2 + (1 / 2 : ℝ) • expo P q.1 q.2 := by
  simp only [expo, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add, mulVec_smul]
  module

theorem soft_of (Feas : Set ((Fin N → ℝ) × (Fin M → ℝ))) (K : (Fin N → ℝ) × (Fin M → ℝ) → ℝ)
    (hF : Convex ℝ Feas) (hK : ConcaveOn ℝ Feas K) (RE : Set (Fin M → ℝ)) (ws : Fin M → ℝ)
    (ps pJ : (Fin N → ℝ) × (Fin M → ℝ)) (_hws : ws ∈ RE) (hmax : IsMaxOn (GE P) RE ws)
    (hps : ps ∈ Feas)
    (hsoft : IsMaxOn (fun q => -(P.gamma / 2 * ((expo P q.1 q.2 - ws) ⬝ᵥ
      (P.Sig *ᵥ (expo P q.1 q.2 - ws)))) + K q) Feas ps)
    (hpJ : pJ ∈ Feas) (hJ : IsMaxOn (fun q => GE P (expo P q.1 q.2) + K q) Feas pJ) :
    let nu := P.mu - P.gamma • (P.Sig *ᵥ ws)
    let Ls := (GE P (expo P pJ.1 pJ.2) + K pJ) - (GE P (expo P ps.1 ps.2) + K ps)
    (wTB P ∈ RE → nu = 0 ∧ Ls = 0) ∧ 0 ≤ Ls ∧
      Ls ≤ nu ⬝ᵥ (expo P pJ.1 pJ.2 - expo P ps.1 ps.2) ∧
      (Ls = 0 ↔ IsMaxOn (fun q => -(P.gamma / 2 * ((expo P q.1 q.2 - ws) ⬝ᵥ
        (P.Sig *ᵥ (expo P q.1 q.2 - ws)))) + K q) Feas pJ) := by
  intro nu Ls
  set Jf : (Fin N → ℝ) × (Fin M → ℝ) → ℝ := fun q => GE P (expo P q.1 q.2) + K q
  set Sf : (Fin N → ℝ) × (Fin M → ℝ) → ℝ := fun q => -(P.gamma / 2 * ((expo P q.1 q.2 - ws) ⬝ᵥ
    (P.Sig *ᵥ (expo P q.1 q.2 - ws)))) + K q
  have hid : ∀ q, Jf q = Sf q + GE P ws + nu ⬝ᵥ (expo P q.1 q.2 - ws) := by
    intro q; simp only [Jf, Sf]; rw [GE_around hS ws]; ring
  have hLs0 : 0 ≤ Ls := sub_nonneg.2 (hJ hps)
  have hsJ := hsoft hpJ
  simp only [Set.mem_ofPred_eq] at hsJ
  have hdiff : nu ⬝ᵥ (expo P pJ.1 pJ.2 - ws) - nu ⬝ᵥ (expo P ps.1 ps.2 - ws) =
      nu ⬝ᵥ (expo P pJ.1 pJ.2 - expo P ps.1 ps.2) := by
    rw [← dotProduct_sub]; congr 1; abel
  have hLsle : Ls ≤ nu ⬝ᵥ (expo P pJ.1 pJ.2 - expo P ps.1 ps.2) := by
    have e1 := hid pJ; have e2 := hid ps
    change Jf pJ - Jf ps ≤ _
    linarith
  -- strict concavity of `Jf` across different exposures
  have hstrict : ∀ p q, p ∈ Feas → q ∈ Feas → expo P p.1 p.2 ≠ expo P q.1 q.2 →
      (Jf p + Jf q) / 2 < Jf ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) := by
    intro p q hp hq hne
    have h1 := GE_mid hγ hS hne
    have h2 := hK.2 hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [Jf]
    rw [expo_mid]
    simp only [smul_eq_mul] at h2
    linarith
  have hmid : ∀ p q, p ∈ Feas → q ∈ Feas → (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ Feas := fun p q hp hq =>
    hF hp hq (by norm_num) (by norm_num) (by norm_num)
  have hlinmid : ∀ p q : (Fin N → ℝ) × (Fin M → ℝ),
      nu ⬝ᵥ (expo P ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).1 ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).2 - ws) =
        (nu ⬝ᵥ (expo P p.1 p.2 - ws) + nu ⬝ᵥ (expo P q.1 q.2 - ws)) / 2 := by
    intro p q
    rw [expo_mid, show (1 / 2 : ℝ) • expo P p.1 p.2 + (1 / 2 : ℝ) • expo P q.1 q.2 - ws =
      (1 / 2 : ℝ) • (expo P p.1 p.2 - ws) + (1 / 2 : ℝ) • (expo P q.1 q.2 - ws) by module]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  refine ⟨fun hTB => ?_, hLs0, hLsle, ⟨fun h0 => ?_, fun hsp => ?_⟩⟩
  · -- `w_TB ∈ R_E` forces `w_s = w_TB` and `ν = 0`
    have hs := symm_of_posDef hS
    have hTBgrad : P.gamma • (P.Sig *ᵥ wTB P) = P.mu := by
      have hdet : IsUnit (P.gamma • P.Sig).det := by
        rw [det_smul, IsUnit.mul_iff]
        exact ⟨isUnit_iff_ne_zero.2 (pow_ne_zero _ hγ.ne'),
          (isUnit_iff_isUnit_det _).mp hS.isUnit⟩
      rw [← smul_mulVec, wTB, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hle : ∀ w, GE P w ≤ GE P (wTB P) := by
      intro w
      have := GE_around hS (wTB P) w
      rw [hTBgrad, sub_self, zero_dotProduct, add_zero] at this
      have := qf_nonneg hS (w - wTB P)
      simp only [qf] at this
      nlinarith
    have hge := hmax hTB
    simp only [Set.mem_ofPred_eq] at hge
    have heq : ws = wTB P := by
      by_contra hne
      have := GE_mid hγ hS hne
      have := hle ((1 / 2 : ℝ) • ws + (1 / 2 : ℝ) • wTB P)
      have := hle ws
      linarith
    have hnu : nu = 0 := by simp only [nu]; rw [heq, hTBgrad, sub_self]
    refine ⟨hnu, le_antisymm ?_ hLs0⟩
    rw [hnu, zero_dotProduct] at hLsle; exact hLsle
  · -- `Λ_s = 0`: `p_s` is a joint maximizer, so it shares `p_J`'s exposure
    have heq : expo P pJ.1 pJ.2 = expo P ps.1 ps.2 := by
      by_contra hne
      have h1 := hstrict pJ ps hpJ hps hne
      have h2 := hJ (hmid pJ ps hpJ hps)
      simp only [Set.mem_ofPred_eq] at h2
      change Jf pJ - Jf ps = 0 at h0
      linarith
    intro q hq
    have h1 := hsoft hq
    simp only [Set.mem_ofPred_eq] at h1 ⊢
    have e1 := hid pJ; have e2 := hid ps
    rw [heq] at e1
    change Jf pJ - Jf ps = 0 at h0
    change Sf q ≤ Sf pJ
    change Sf q ≤ Sf ps at h1
    linarith
  · -- both maximize the soft objective, so they share the exposure
    have h1 := hsp hps
    simp only [Set.mem_ofPred_eq] at h1
    change Sf ps ≤ Sf pJ at h1
    change Sf pJ ≤ Sf ps at hsJ
    have heq : expo P pJ.1 pJ.2 = expo P ps.1 ps.2 := by
      by_contra hne
      have hs1 := hstrict pJ ps hpJ hps hne
      have hs2 := hsoft (hmid pJ ps hpJ hps)
      simp only [Set.mem_ofPred_eq] at hs2
      change Sf ((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • ps) ≤ Sf ps at hs2
      have e1 := hid pJ; have e2 := hid ps; have e3 := hid ((1 / 2 : ℝ) • pJ + (1 / 2 : ℝ) • ps)
      rw [hlinmid] at e3
      linarith
    have e1 := hid pJ; have e2 := hid ps
    rw [heq] at e1
    change Jf pJ - Jf ps = 0
    linarith

end Soft

theorem explicit : Explicit := fun _ _ _ hγ hS F xA xE eta t hT => explicit_of hγ hS F xA xE eta t hT

theorem soft : Soft := fun _ _ _ hγ hS Feas K hF hK RE ws ps pJ hws hmax hps hsoft hpJ hJ =>
  soft_of hγ hS Feas K hF hK RE ws ps pJ hws hmax hps hsoft hpJ hJ


/-! ### Part 2c's special cases -/

lemma sum_univ_in {M : ℕ} (f : Fin M → ℝ) : ∑ j : In (Finset.univ : Finset (Fin M)), f j = ∑ j, f j := by
  have : IsEmpty (Out (Finset.univ : Finset (Fin M))) := ⟨fun j => j.2 (Finset.mem_univ _)⟩
  have h := split_sum Finset.univ f
  rw [Finset.univ_eq_empty (α := Out (Finset.univ : Finset (Fin M))), Finset.sum_empty, add_zero] at h
  exact h.symm

theorem specialCases : SpecialCases := by
  intro M N P eta t xE xA i
  have he : IsEmpty (In (∅ : Finset (Fin M))) := ⟨fun j => absurd j.2 (Finset.notMem_empty _)⟩
  have hu : IsEmpty (Out (Finset.univ : Finset (Fin M))) := ⟨fun j => j.2 (Finset.mem_univ _)⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, fun F hpi hxF => ?_⟩
  · funext j
    simp [rho, rT, rF, mulVec, dotProduct]
  · ext a b
    simp [VZ, QZ, Matrix.mul_apply, transpose_apply]
  · have hr : rho P ∅ i = (fun j : Out (∅ : Finset (Fin M)) => P.Q j i) := by
      funext j; simp [rho, rT, rF, mulVec, dotProduct]
    simp only [alphaFT, hr]
    simp [dotProduct, rF, piT, mulVec]
  · have hmu : muZc P Finset.univ = fun j : In (Finset.univ : Finset (Fin M)) => P.mu j := by
      funext j; simp [muZc, mulVec, dotProduct]
    have hsch : schur P Finset.univ = SZZ P Finset.univ := by
      ext a b; simp [schur, Matrix.mul_apply]
    simp only [alphaFT, hmu, hsch]
    have hrho : rho P Finset.univ i ⬝ᵥ piT Finset.univ eta t = 0 := by
      simp [dotProduct]
    rw [hrho, add_zero]
    have h1 : rF P Finset.univ i ⬝ᵥ (fun j : In (Finset.univ : Finset (Fin M)) => P.mu j) =
        ∑ j, P.Q j i * P.mu j := by
      simp only [dotProduct, rF]; exact sum_univ_in (fun j => P.Q j i * P.mu j)
    have h2 : rF P Finset.univ i ⬝ᵥ (SZZ P Finset.univ *ᵥ xF Finset.univ xE) =
        ∑ j, P.Q j i * (P.Sig *ᵥ xE) j := by
      simp only [dotProduct, rF, mulVec, SZZ, xF, submatrix_apply]
      rw [sum_univ_in (fun j => P.Q j i * ∑ k : In (Finset.univ : Finset (Fin M)), P.Sig j k * xE k)]
      exact Finset.sum_congr rfl fun j _ => by rw [sum_univ_in (fun k => P.Sig j k * xE k)]
    rw [h1, h2]
  · have hsch : schur P Finset.univ = SZZ P Finset.univ := by
      ext a b; simp [schur, Matrix.mul_apply]
    simp only [VZ, hsch, add_mulVec, Pi.add_apply]
    congr 1
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, transpose_apply, QZ, SZZ, submatrix_apply, id]
    rw [sum_univ_in (fun j => P.Q j i * ∑ k : In (Finset.univ : Finset (Fin M)),
      P.Sig j k * ∑ l, P.Q k l * xA l)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [sum_univ_in (fun k => P.Sig j k * ∑ l, P.Q k l * xA l)]
  · have hp : piT F eta t = 0 := funext hpi
    have hx : xF F xE = 0 := funext fun j => hxF j.1 j.2
    simp only [alphaFT, alphaZ, hp, hx, mulVec_zero, dotProduct_zero, mul_zero, sub_zero, add_zero,
      Pi.add_apply]
    simp [dotProduct, rF, QZ, mulVec, transpose_apply]

/-! ### Part 1 and 4a (given AX-13) -/

section Crit

open Standalone.M2ScoreAccounting Standalone.M2ActionClasses Standalone.M7TwoStageExactnessLoss

theorem part1 : Part1 := by
  intro hAX m K S _ D θ Sf V SE hIn hRef hBE x hx hcap
  constructor
  · intro hmax
    obtain ⟨η, t, ζ, h1, h2, h3, h4, h5, -, h7, h8⟩ :=
      Novel.M7FundDecisionEtfsAtZeroProof.oneSided hAX m K S D θ Sf V SE hIn hRef hBE x hx hmax hcap
    exact ⟨η, t, ζ, h1, h2, h3, h4, h5, h7, h8⟩
  · rintro ⟨η, t, ζ, h1, h2, h3, -, h5, -, h8⟩
    refine (Novel.M7TwoStageExactnessLossProof.jointOptimality hAX m K K S D θ hIn x hx).2
      ⟨η, t, h1, h2, h3, fun l => ?_⟩
    cases l with
    | inl i => exact h8 i
    | inr j =>
      obtain ⟨hz0, hzpos, hline⟩ := h5 j
      rw [hline]
      refine ⟨fun _ => by linarith, fun hpos => ?_⟩
      rw [hzpos hpos]; linarith

theorem exactAtX2 : ExactAtX2 := by
  intro hAX m K S _ D θ Sf V SE hIn hRef hBE x2 hx2 hcap xJ hxJ hJ
  rw [← part1 hAX m K S D θ Sf V SE hIn hRef hBE x2 hx2 hcap]
  constructor
  · intro heq y hy
    have := hJ hy
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  · intro hmax
    have h1 := hmax hxJ
    have h2 := hJ hx2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith

end Crit

open Standalone.M7TwoStageEtfsAtZero Standalone.M7TwoStageEtfsAtZero.TS in
theorem linesAtX2 : LinesAtX2 := by
  intro M N P hS ws x2 hws hmax hx2 xE2
  have hexpo : expo P.toCoord x2 xE2 = ws := by
    simp only [expo, xE2]; abel
  have hgE : gE P.toCoord ws = -P.zeta ws := by
    simp only [gE, TS.zeta]; abel
  refine ⟨hexpo, hgE, fun i => ?_, fun j hj => ?_⟩
  · simp only [gA, hgE, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_neg,
      Pi.neg_apply]
    ring
  · have hlt : (P.Q *ᵥ x2) j < ws j := by
      have : 0 < ws j - (P.Q *ᵥ x2) j := by simpa [xE2] using hj
      linarith
    have hz := Novel.M7TwoStageEtfsAtZeroProof.zeta_comp hS hws hmax hx2 j hlt
    refine ⟨hz, fun eta kp km t heta hkp hkm hline => ?_⟩
    have h0 : -(0 : ℝ) = eta + (1 + eta) * t := by
      rw [← hline, hgE, Pi.neg_apply, hz]
    obtain ⟨hb, hs, hu⟩ := etfLines eta 0 kp km t heta le_rfl hkp hkm h0
    refine ⟨fun ht => ⟨(hb ht).1, (hb ht).2.1⟩, fun ht => by have := hs ht; linarith,
      fun hl hu' => by have := hu hl hu'; simpa using this⟩

/-- Claim 109, parts 1-4. -/
theorem proof : Standalone.M7EtfsAtZeroCostsBudget.statement :=
  ⟨part1, explicit, specialCases, atZeroTests, bracket, oneOne, exactAtX2, linesAtX2, etfLines, soft⟩

end

end Novel.M7EtfsAtZeroCostsBudgetProof

import TotientAbel
import ShiftedEulerUniform

/-! Actual outer arithmetic sums with logarithmically rescaled smooth profiles.
The coprime inner-sum replacement is a separate obligation. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.LogProfileSum
open TotientAbel TotientHarmonic ShiftedTotient ShiftedEulerUniform
set_option maxHeartbeats 1000000

def coordinate (L U t : ℝ) : ℝ := U-Real.log t/L

theorem coordinate_mem (L U t : ℝ) (hL : 0 < L) (ht : t ∈ Set.Icc 1 (Real.exp (L*U))) :
    coordinate L U t ∈ Set.Icc 0 U := by
  have hlog := (Real.log_le_iff_le_exp (by linarith [ht.1] : 0 < t)).mpr ht.2
  have hn := Real.log_nonneg ht.1
  unfold coordinate
  constructor
  · have hh : Real.log t/L ≤ U := (div_le_iff₀ hL).mpr (by nlinarith)
    linarith
  · have := div_nonneg hn hL.le; linarith

theorem log_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L U : ℝ) (hL : 0 < L) (hU : 0 ≤ U) (H : ℝ → E) (hc : Continuous H) :
    (∫ t in 1..Real.exp (L*U), (t⁻¹/L) • H (coordinate L U t)) = ∫ u in 0..U, H u := by
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le hU)
  have hd : ∀ t ∈ Set.uIcc 1 (Real.exp (L*U)),
      HasDerivAt (fun t => Real.log t/L) (t⁻¹/L) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact (Real.hasDerivAt_log (by linarith [ht.1])).div_const L
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹/L) (Set.uIcc 1 (Real.exp (L*U))) := by
    rw [Set.uIcc_of_le hx]
    exact (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).div_const L
  have h := intervalIntegral.integral_deriv_smul_comp (g := fun v => H (U-v)) hd hcont
    (hc.comp (continuous_const.sub continuous_id))
  simp only [Real.log_one, zero_div, Real.log_exp, mul_div_cancel_left₀ U hL.ne'] at h
  simpa only [Function.comp_apply, coordinate, intervalIntegral.integral_comp_sub_left,
    sub_self, sub_zero] using h

def zeroSum (L U : ℝ) (H : ℝ → ℂ) : ℂ :=
  testedSum (Real.exp (L*U)) (fun t => H (coordinate L U t)) / (L:ℂ)

theorem zeroSum_error (L U M D : ℝ) (H H' : ℝ → ℂ)
    (hL : 0 < L) (hU : 0 ≤ U)
    (hd : ∀ u, HasDerivAt H (H' u) u) (hc : Continuous H')
    (hM : ‖H 0‖ ≤ M) (hD : ∀ u ∈ Set.Icc 0 U, ‖H' u‖ ≤ D) :
    ‖zeroSum L U H - ∫ u in 0..U, H u‖ ≤ errorConstant*(M+U*D)/L := by
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le hU)
  have hH : Continuous H := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  let F := fun t => H (coordinate L U t)
  let F' := fun t => (-(t⁻¹/L) : ℝ) • H' (coordinate L U t)
  have hder : ∀ t ∈ Set.Icc 1 (Real.exp (L*U)), HasDerivAt F (F' t) t := by
    intro t ht
    exact (hd _).scomp t (((Real.hasDerivAt_log (by linarith [ht.1])).div_const L).const_sub U)
  have hcoord : ContinuousOn (coordinate L U) (Set.Icc 1 (Real.exp (L*U))) :=
    continuousOn_const.sub ((continuousOn_id.log (fun t ht =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).div_const L)
  have hcont : ContinuousOn F' (Set.Icc 1 (Real.exp (L*U))) :=
    (((continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).div_const L).neg).smul
      (hc.comp_continuousOn hcoord)
  have hb := weighted_error_bound _ hx F F' hder hcont
  have he : (∫ t in 1..Real.exp (L*U), F t/(t:ℂ))/(L:ℂ) = ∫ u in 0..U, H u := by
    rw [← intervalIntegral.integral_div]
    convert log_rescale L U hL hU H hH using 1
    congr 1; funext t
    simp only [Complex.real_smul, F, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  have hn : (∫ t in 1..Real.exp (L*U), ‖F' t‖) = ∫ u in 0..U, ‖H' u‖ := by
    rw [← log_rescale L U hL hU (fun u => ‖H' u‖) hc.norm]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 ≤ t := (by norm_num : (0:ℝ) ≤ 1).trans ht.1
    simp only [F', norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (div_nonneg (inv_nonneg.mpr ht0) hL.le), smul_eq_mul]
  have hint : (∫ u in 0..U, ‖H' u‖) ≤ U*D := by
    calc
      _ ≤ ∫ u in 0..U, D := intervalIntegral.integral_mono_on hU
        (hc.norm.intervalIntegrable _ _) intervalIntegrable_const hD
      _ = _ := by simp
  have hend : F (Real.exp (L*U)) = H 0 := by
    simp [F, coordinate, Real.log_exp, hL.ne']
  rw [zeroSum, ← he, ← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  apply hb.trans
  rw [hn, hend]
  exact mul_le_mul_of_nonneg_left (add_le_add hM hint) errorConstant_nonneg

def shiftedSum (L U : ℝ) (A B : ℂ) (H : ℝ → ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
    outerWeight (A/L) (B/L) g * H (coordinate L U g))/(L:ℂ)

theorem shiftedSum_sub_zeroSum (L U : ℝ) (A B : ℂ) (H : ℝ → ℂ) :
    shiftedSum L U A B H-zeroSum L U H =
      (∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
        (outerWeight (A/L) (B/L) g-outerWeight 0 0 g)*H (coordinate L U g))/(L:ℂ) := by
  unfold shiftedSum zeroSum testedSum
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  rw [outerWeight_zero g (mem_Ioc.mp hg).1.ne']
  change _ = (_-((TotientConvolution.weight g:ℝ):ℂ))*_
  ring

def error (L C U M D : ℝ) : ℝ :=
  M*((U+errorConstant/L)*envelope C U L)+errorConstant*(M+U*D)/L

theorem shiftedSum_error (L C U M D : ℝ) (A B : ℂ) (H H' : ℝ → ℂ)
    (hL : 0 < L) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L)
    (hd : ∀ u, HasDerivAt H (H' u) u) (hc : Continuous H')
    (hH : ∀ u ∈ Set.Icc 0 U, ‖H u‖ ≤ M)
    (hD : ∀ u ∈ Set.Icc 0 U, ‖H' u‖ ≤ D) :
    ‖shiftedSum L U A B H-∫ u in 0..U, H u‖ ≤ error L C U M D := by
  have hzero := zeroSum_error L U M D H H' hL hU hd hc (hH 0 ⟨le_rfl,hU⟩) hD
  have hshift := tested_weight_error_bound L C U M A B
    (fun g => H (coordinate L U g)) hL hU hM hA hB hCU hlarge (by
      intro g hg
      apply hH
      apply coordinate_mem L U g hL
      exact ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
        (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩)
  rw [← shiftedSum_sub_zeroSum] at hshift
  exact (norm_sub_le_norm_sub_add_norm_sub _ (zeroSum L U H) _).trans
    (add_le_add hshift hzero)

theorem error_tendsto (C U M D : ℝ) : Tendsto (fun L => error L C U M D) atTop (nhds 0) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have he := ((hi.const_mul errorConstant).const_add U).mul (envelope_tendsto C U)
  have h := (he.const_mul M).add (hi.const_mul (errorConstant*(M+U*D)))
  simpa only [error, div_eq_mul_inv, mul_zero, add_zero] using h

theorem shifted_family_uniform {ι : Type*} (s : Set ι) (A B : ι → ℂ)
    (H H' : ι → ℝ → ℂ) (C U M D : ℝ) (hU : 0 ≤ U) (hM : 0 ≤ M) (hCU : C*U ≤ 1)
    (hA : ∀ p ∈ s, ‖A p‖ ≤ C) (hB : ∀ p ∈ s, ‖B p‖ ≤ C)
    (hd : ∀ p ∈ s, ∀ u, HasDerivAt (H p) (H' p u) u)
    (hc : ∀ p ∈ s, Continuous (H' p))
    (hH : ∀ p ∈ s, ∀ u ∈ Set.Icc 0 U, ‖H p u‖ ≤ M)
    (hD : ∀ p ∈ s, ∀ u ∈ Set.Icc 0 U, ‖H' p u‖ ≤ D) :
    TendstoUniformlyOn (fun L p => shiftedSum L U (A p) (B p) (H p))
      (fun p => ∫ u in 0..U, H p u) atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (8*C),
    (error_tendsto C U M D).eventually (gt_mem_nhds heps)] with L hL hlarge he
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (shiftedSum_error L C U M D (A p) (B p) (H p) (H' p) hL hU hM
    (hA p hp) (hB p hp) hCU hlarge (hd p hp) (hc p hp) (hH p hp) (hD p hp)).trans_lt he

#print axioms shiftedSum_sub_zeroSum
#print axioms shiftedSum_error
#print axioms shifted_family_uniform
#print axioms log_rescale
#print axioms zeroSum_error
end XiPrime8845.LogProfileSum

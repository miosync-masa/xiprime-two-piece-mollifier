import PRZZContourKernel
import Zeta23.WeilEF.Effective

/-! A supplied polynomial envelope for completed zeta away from its poles.
Reflection covers the left half of the strip. This is an input to contour
estimates, not itself a contour-shift or residue-remainder theorem. -/
noncomputable section
open Complex
namespace XiPrime8845.PRZZCompletedStrip
set_option maxHeartbeats 2000000

theorem gammaR_bound (s : ℂ) (hl : (1/2:ℝ) ≤ s.re) (hu : s.re ≤ 10) :
    ‖Gammaℝ s‖ ≤ 24 := by
  rw [Gammaℝ_def,norm_mul]
  have hp : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-s/2).re = -(s.re/2) := by simp; ring
    rw [he,Real.rpow_neg Real.pi_pos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith))
  have hg : ‖Gamma (s/2)‖ ≤ 24 := by
    apply (Zeta23.WeilEF.norm_Gamma_le_Gamma_re (z := s/2) (by simp; linarith)).trans
    apply Zeta23.WeilEF.Real_Gamma_le_24 <;> simp <;> linarith
  nlinarith [norm_nonneg ((Real.pi:ℂ)^(-s/2)),norm_nonneg (Gamma (s/2))]

theorem right_bound (s : ℂ) (hl : (1/2:ℝ) ≤ s.re) (hu : s.re ≤ 10)
    (hi : 1 ≤ |s.im|) : ‖completedRiemannZeta s‖ ≤ 36+48*‖s‖ := by
  have hs : s ≠ 1 := by intro h; norm_num [h] at hi
  have hn : 1 ≤ ‖1-s‖ := hi.trans (by simpa using abs_im_le_norm (1-s))
  have hz := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (by linarith : 0 < s.re) hs
  have hd : ‖s‖/s.re ≤ 2*‖s‖ := (div_le_iff₀ (by linarith)).mpr (by nlinarith [norm_nonneg s])
  have hr : 1/‖1-s‖ ≤ (1:ℝ) := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
  rw [PRZZContourKernel.completed_factor s (by linarith),norm_mul]
  have hg := gammaR_bound s hl hu
  have hz' : ‖riemannZeta s‖ ≤ 3/2+2*‖s‖ := by linarith
  calc
    _ ≤ 24*(3/2+2*‖s‖) := mul_le_mul hg hz' (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Constants independent of the point, including its imaginary height. -/
theorem strip_bound (s : ℂ) (hl : -9 ≤ s.re) (hu : s.re ≤ 10)
    (hi : 1 ≤ |s.im|) : ‖completedRiemannZeta s‖ ≤ 84+48*‖s‖ := by
  by_cases hr : (1/2:ℝ) ≤ s.re
  · exact (right_bound s hr hu hi).trans (by linarith)
  · rw [← completedRiemannZeta_one_sub s]
    have hh := right_bound (1-s) (by simp; linarith) (by simp; linarith) (by simpa using hi)
    have hn : ‖1-s‖ ≤ 1+‖s‖ := by simpa using norm_sub_le (1:ℂ) s
    linarith

/-- Both regular completed-zeta factors in the two noncentral residues.
The hypotheses are geometric bounds, not estimates on zeta. -/
theorem residue_factors (z w : ℂ) (t : ℝ)
    (hz : 1/4 ≤ z.re ∧ z.re ≤ 3/4) (hw : 1/4 ≤ w.re ∧ w.re ≤ 3/4)
    (hzN : ‖z‖ ≤ t+1) (hwN : ‖w‖ ≤ t+1) (him : 1 ≤ |(w-z).im|) :
    ‖completedRiemannZeta (w-z)‖ ≤ 228+96*t ∧
      ‖completedRiemannZeta (w+(1-z))‖ ≤ 228+96*t := by
  have h1 := strip_bound (w-z) (by simp; linarith [hz.1,hz.2,hw.1,hw.2])
    (by simp; linarith [hz.1,hz.2,hw.1,hw.2]) him
  have h2 := strip_bound (w+(1-z)) (by simp; linarith [hz.1,hz.2,hw.1,hw.2])
    (by simp; linarith [hz.1,hz.2,hw.1,hw.2]) (by simpa [sub_eq_add_neg] using him)
  have hn1 := norm_sub_le w z
  have hn2 : ‖w+(1-z)‖ ≤ ‖w‖+1+‖z‖ := by
    have hh := (norm_add_le w (1-z)).trans (add_le_add le_rfl (norm_sub_le (1:ℂ) z))
    simpa [add_assoc] using hh
  constructor <;> linarith

/-- Supplied bounds for the actual left-factor poles. The reflected
ordering follows from the same geometric lemma `residue_factors`. -/
theorem actual_residue_factors (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖completedRiemannZeta (PRZZAFEDual.rightArg b t-PRZZAFEDual.leftArg a t)‖ ≤ 228+96*t ∧
    ‖completedRiemannZeta (PRZZAFEDual.rightArg b t+(1-PRZZAFEDual.leftArg a t))‖ ≤ 228+96*t := by
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hai := abs_le.mp ((abs_im_le_norm a).trans ha)
  have hbi := abs_le.mp ((abs_im_le_norm b).trans hb)
  have hz : ‖PRZZAFEDual.leftArg a t‖ ≤ t+1 := by
    have h := (norm_add_le ((1/2:ℂ)+a) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) a) le_rfl)
    simp [PRZZAFEDual.leftArg,norm_mul,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  have hw : ‖PRZZAFEDual.rightArg b t‖ ≤ t+1 := by
    have h := (norm_sub_le ((1/2:ℂ)+b) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) b) le_rfl)
    simp [PRZZAFEDual.rightArg,norm_mul,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  refine residue_factors _ _ t ?_ ?_ hz hw ?_
  · simp [PRZZAFEDual.leftArg]; constructor <;> linarith
  · simp [PRZZAFEDual.rightArg]; constructor <;> linarith
  · simp only [PRZZAFEDual.leftArg,PRZZAFEDual.rightArg,sub_im,add_im,
      div_ofNat_im,one_im,zero_div,mul_im,ofReal_re,I_im,ofReal_im,I_re,
      mul_one,mul_zero,add_zero,zero_add]
    have hh := neg_le_abs (b.im-t-(a.im+t))
    linarith

#print axioms residue_factors
#print axioms actual_residue_factors
#print axioms gammaR_bound
#print axioms right_bound
#print axioms strip_bound
end XiPrime8845.PRZZCompletedStrip

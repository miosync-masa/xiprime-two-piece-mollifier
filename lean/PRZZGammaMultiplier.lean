import PRZZDualError

/-! Low-dependency Gamma-minus-power estimates, shared by diagonal
main-kernel comparison and the existing zero-frequency correction.
The original theorem namespace is preserved. -/
noncomputable section
open Complex Set Filter Topology
namespace XiPrime8845.PRZZZeroGammaBound
set_option maxHeartbeats 6000000

theorem multiplier_difference (a b : ℂ) (T t : ℝ)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) (hT : 2 ≤ T) (ht : T ≤ t) :
    ‖PRZZAFEDual.dualMultiplier a b t-((t/(2*Real.pi):ℝ):ℂ)^(-(a+b))‖ ≤
      ‖((t/(2*Real.pi):ℝ):ℂ)^(-(a+b))‖*(7/T)*Real.exp (7/T) := by
  have hs : ‖-(a+b)‖ ≤ 1/8 := by
    rw [norm_neg]; exact (norm_add_le _ _).trans (by linarith)
  have hi := (Complex.abs_im_le_norm (-(a+b))).trans hs
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (-(a+b))).trans hs)).1
  have hh := PRZZGammaMain.ratio_relative_bound_strip T t a b (-(a+b))
    hT ht (by linarith) (by linarith) (by linarith) hre
  have hc : 2*‖-(a+b)‖*(26+‖-(a+b)‖)/T ≤ 7/T := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [norm_nonneg (-(a+b))]
  rw [PRZZDualError.multiplier_ratio]
  exact hh.trans (by gcongr)

theorem scaled_power_cap (S T t : ℝ) (A B : ℂ) (hS : 0 ≤ S)
    (hT : 1 < T) (ht : 2*Real.pi ≤ t) (htT : t/(2*Real.pi) ≤ T)
    (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) :
    ‖((t/(2*Real.pi):ℝ):ℂ)^((A+B)/(Real.log T:ℂ))‖ ≤ Real.exp (2*S) := by
  have hq : 1 ≤ t/(2*Real.pi) := (le_div_iff₀ (by positivity)).mpr (by simpa using ht)
  have hq0 : 0 < t/(2*Real.pi) := by linarith
  have h := PRZZDualError.dilation_cap S T (t/(2*Real.pi)) A B hS hT hq htT hA hB
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne'),
    ← Complex.ofReal_log hq0.le]
  simpa only [mul_comm] using h

theorem multiplier_scaled_difference (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ t ∈ Icc T (2*T),
      ‖PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
        ((t/(2*Real.pi):ℝ):ℂ)^(-((A+B)/(Real.log T:ℂ)))‖ ≤
          (7*Real.exp (2*S+7))/T := by
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2*Real.pi),eventually_ge_atTop (2:ℝ)] with T hsmall hpi hT
  intro A B hA hB t ht
  have hp := scaled_power_cap S T t (-A) (-B) hS (by linarith) (hpi.trans ht.1)
    (by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [ht.2,Real.pi_gt_three])
    (by simpa using hA) (by simpa using hB)
  have hh := multiplier_difference _ _ T t (hsmall.2 A hA) (hsmall.2 B hB) hT ht.1
  have he : -A+-B = -(A+B) := by ring
  rw [he,neg_div] at hp
  rw [← add_div] at hh
  calc
    _ ≤ Real.exp (2*S)*(7/T)*Real.exp 7 := by
      apply hh.trans
      gcongr
      exact (div_le_iff₀ (by linarith : 0 < T)).mpr (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

#print axioms multiplier_difference
#print axioms scaled_power_cap
#print axioms multiplier_scaled_difference
end XiPrime8845.PRZZZeroGammaBound

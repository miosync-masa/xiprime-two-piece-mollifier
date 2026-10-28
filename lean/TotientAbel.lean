import TotientHarmonic

/-! Actual reciprocal-totient sums tested against complex smooth weights.
No shift-dependent Euler weight is silently replaced by its zero-shift value. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace XiPrime8845.TotientAbel
open TotientHarmonic TotientConvolution
set_option maxHeartbeats 1000000

theorem complex_summatory (t : ℝ) :
    (∑ n ∈ Icc 0 ⌊t⌋₊, (weight n:ℂ)) = (summatory t:ℂ) := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
  simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_add]
  simp only [summatory, Complex.ofReal_sum]
  rfl

def testedSum (x : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, F n * (weight n:ℂ)

theorem abel_identity (x : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x)) :
    testedSum x F = F x*(summatory x:ℂ) -
      ∫ t in 1..x, F' t*(summatory t:ℂ) := by
  have hi : IntegrableOn (deriv F) (Set.Icc 1 x) := by
    apply (hc.integrableOn_compact isCompact_Icc).congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (weight n:ℂ)) (by simp) x
    (fun t ht => (hd t ht).differentiableAt) hi
  simp only [complex_summatory] at h
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons] at h
  simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, zero_add] at h
  rw [intervalIntegral.integral_of_le hx]
  convert h using 1
  · rfl
  · apply congrArg (fun z => F x*(summatory x:ℂ)-z)
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]

theorem weighted_error_identity (x : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x)) :
    testedSum x F - (∫ t in 1..x, F t/(t:ℂ)) =
      F x*((summatory x-Real.log x:ℝ):ℂ) -
      ∫ t in 1..x, F' t*((summatory t-Real.log t:ℝ):ℂ) := by
  have hF : ContinuousOn F (Set.Icc 1 x) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hlog : ContinuousOn (fun t => (Real.log t:ℂ)) (Set.Icc (1:ℝ) x) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hdiv : ContinuousOn (fun t => F t/(t:ℂ)) (Set.Icc (1:ℝ) x) :=
    hF.div (Complex.continuous_ofReal.continuousOn) (fun t ht => by
      exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hi₁ : IntervalIntegrable (fun t => F t/(t:ℂ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (hdiv.integrableOn_compact isCompact_Icc)
  have hi₂ : IntervalIntegrable (fun t => F' t*(Real.log t:ℂ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ((hc.mul hlog).integrableOn_compact isCompact_Icc)
  have hdprod (t : ℝ) (ht : t ∈ Set.uIcc 1 x) :
      HasDerivAt (fun t => F t*(Real.log t:ℂ))
        (F t/(t:ℂ)+F' t*(Real.log t:ℂ)) t := by
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    convert! (hd t ht).mul ((Real.hasDerivAt_log ht0).ofReal_comp) using 1 <;>
      simp only [Complex.ofReal_inv] <;> ring
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt hdprod (hi₁.add hi₂)
  rw [intervalIntegral.integral_add hi₁ hi₂] at hp
  simp only [Real.log_one, Complex.ofReal_zero, mul_zero, sub_zero] at hp
  have hisum : IntervalIntegrable (fun t => F' t*(summatory t:ℂ)) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    simpa only [complex_summatory] using integrableOn_mul_sum_Icc (m := 0)
      (fun n => (weight n:ℂ)) (by norm_num : (0:ℝ) ≤ 1)
      (hc.integrableOn_compact isCompact_Icc)
  simp_rw [Complex.ofReal_sub, mul_sub]
  rw [intervalIntegral.integral_sub hisum hi₂, abel_identity x hx F F' hd hc]
  linear_combination -hp

theorem weighted_error_bound (x : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x)) :
    ‖testedSum x F - (∫ t in 1..x, F t/(t:ℂ))‖ ≤
      errorConstant*(‖F x‖ + ∫ t in 1..x, ‖F' t‖) := by
  have hlog : ContinuousOn (fun t => (Real.log t:ℂ)) (Set.Icc (1:ℝ) x) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hisum : IntegrableOn (fun t => F' t*(summatory t:ℂ)) (Set.Icc 1 x) := by
    simpa only [complex_summatory] using integrableOn_mul_sum_Icc (m := 0)
      (fun n => (weight n:ℂ)) (by norm_num : (0:ℝ) ≤ 1)
      (hc.integrableOn_compact isCompact_Icc)
  have hir : IntervalIntegrable
      (fun t => F' t*((summatory t-Real.log t:ℝ):ℂ)) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    have hsub : IntegrableOn (fun t => F' t*(summatory t:ℂ) - F' t*(Real.log t:ℂ))
        (Set.Icc 1 x) := hisum.sub ((hc.mul hlog).integrableOn_compact isCompact_Icc)
    simpa only [Complex.ofReal_sub, mul_sub] using hsub
  have hin : IntervalIntegrable (fun t => ‖F' t‖*errorConstant) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((hc.norm.mul_const errorConstant).integrableOn_compact isCompact_Icc)
  have hbound (t : ℝ) (ht : 1 ≤ t) :
      ‖((summatory t-Real.log t:ℝ):ℂ)‖ ≤ errorConstant := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using summatory_log_bound t ht
  rw [weighted_error_identity x hx F F' hd hc]
  apply (norm_sub_le _ _).trans
  have hend := mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg (F x))
  have hint : ‖∫ t in 1..x, F' t*((summatory t-Real.log t:ℝ):ℂ)‖ ≤
      (∫ t in 1..x, ‖F' t‖)*errorConstant := by
    rw [← intervalIntegral.integral_mul_const]
    apply (intervalIntegral.norm_integral_le_integral_norm hx).trans
    apply intervalIntegral.integral_mono_on hx hir.norm hin
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound t ht.1) (norm_nonneg _)
  rw [norm_mul]
  nlinarith [hend, hint]

#print axioms abel_identity
#print axioms weighted_error_identity
#print axioms weighted_error_bound
end XiPrime8845.TotientAbel

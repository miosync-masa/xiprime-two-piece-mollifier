import RationalBounds

/-! Kernel-checked rational bounds for the fixed coefficient expression.
The conclusion concerns the finite differentiated functional, not zero counting. -/
namespace XiPrime8845.FixedCertificate
open RationalEvaluator RationalBounds
set_option maxRecDepth 100000

theorem finiteValue_upper : NumericalGate.finiteValue.re ≤ 1.12820 := by
  have hm : (minusValue:ℝ) ≤ (-5883815413543881 / 10^10 : ℝ) := by
    exact_mod_cast rational_bounds.1
  have hp0 : (0:ℝ) ≤ (plusValue:ℝ) := by exact_mod_cast rational_bounds.2.1
  have hp : (plusValue:ℝ) ≤ (728627019299614 / 10^10 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr rational_bounds.2.2
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h
  have he := NumericalGate.dual_exp_bounds.2.le
  have hmul := mul_le_mul he hp hp0 (by norm_num : (0:ℝ) ≤ 8.075224414566)
  have hexp : Complex.exp (2*(NumericalGate.R:ℂ)) =
      (Real.exp (2*NumericalGate.R):ℂ) := by rw [Complex.ofReal_exp]; congr 1; push_cast; rfl
  have hr : NumericalGate.finiteValue.re =
      (minusValue:ℝ) + Real.exp (2*NumericalGate.R)*(plusValue:ℝ) := by
    rw [RationalEvaluator.finiteValue_exact, hexp]
    norm_cast
  rw [hr]
  linarith

theorem actual_upper : NumericalGate.actual.re ≤ 1.128201 := by
  have h := NumericalGate.re_le_of_norm_sub_le _ _ _ NumericalGate.actual_sub_finite
  linarith [finiteValue_upper]

/-- Unconditional finite-functional gate. No arithmetic-asymptotic or counting
claim is imported or inferred. -/
theorem fixed_functional_gate : NumericalGate.actual.re < NumericalGate.target :=
  NumericalGate.fixed_finite_gate finiteValue_upper

#print axioms finiteValue_upper
#print axioms actual_upper
#print axioms fixed_functional_gate
end XiPrime8845.FixedCertificate

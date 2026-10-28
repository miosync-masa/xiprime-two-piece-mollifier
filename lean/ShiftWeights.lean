import ElementaryGcd

/-! Absorbing small complex shifts into smooth logarithmic weights.
No Mobius cancellation estimate or PNT is asserted here. -/
noncomputable section
open Complex
namespace XiPrime8845.ShiftWeights

def weight (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-A * t) * P.eval (((u-t)/θ : ℝ) : ℂ)

theorem shift_absorption (m L : ℝ) (hm : 0 < m) (A : ℂ) :
    (m : ℂ)^(-A/(L : ℂ)) = Complex.exp (-A * (Real.log m / L : ℝ)) := by
  rw [GcdDecomposition.positive_cpow m hm]
  push_cast
  congr 1
  ring

theorem profile_absorption (m x L θ : ℝ) (hm : 0 < m) (hx : 0 < x)
    (A : ℂ) (P : Polynomial ℂ) :
    (m : ℂ)^(-A/(L : ℂ)) * P.eval ((Real.log (x/m)/(θ*L) : ℝ) : ℂ) =
      weight A (Real.log x/L) θ P (Real.log m/L) := by
  rw [shift_absorption m L hm]
  unfold weight
  rw [Real.log_div hx.ne' hm.ne']
  congr 2
  push_cast
  ring

theorem weight_smooth (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℝ ⊤ (weight A u θ P) := by
  have hreal : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  unfold weight
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  fun_prop

theorem normalized_log_mem (m L U : ℝ) (hm : 1 ≤ m) (hL : 0 < L)
    (hmU : Real.log m ≤ L*U) : Real.log m/L ∈ Set.Icc 0 U := by
  exact ⟨div_nonneg (Real.log_nonneg hm) hL.le,
    (div_le_iff₀ hL).mpr (by nlinarith)⟩

theorem exp_weight_bound (A : ℂ) (t C U : ℝ) (hA : ‖A‖ ≤ C)
    (ht : |t| ≤ U) : ‖Complex.exp (-A*t)‖ ≤ Real.exp (C*U) := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hA ht (abs_nonneg _) ((norm_nonneg _).trans hA)

theorem weight_bound (A : ℂ) (u θ t C U M : ℝ) (P : Polynomial ℂ)
    (hA : ‖A‖ ≤ C) (ht : |t| ≤ U)
    (hP : ‖P.eval (((u-t)/θ : ℝ) : ℂ)‖ ≤ M) :
    ‖weight A u θ P t‖ ≤ Real.exp (C*U)*M := by
  rw [weight, norm_mul]
  exact mul_le_mul (exp_weight_bound A t C U hA ht) hP (norm_nonneg _)
    (Real.exp_pos _).le

/-- An explicit local modulus in A, uniform in t and the profile evaluation.
This is not a uniform PNT for the resulting family of weights. -/
theorem weight_shift_modulus (A B : ℂ) (u θ t C U M : ℝ) (P : Polynomial ℂ)
    (hB : ‖B‖ ≤ C) (ht : |t| ≤ U)
    (hP : ‖P.eval (((u-t)/θ : ℝ) : ℂ)‖ ≤ M)
    (hsmall : ‖A-B‖*U ≤ 1) :
    ‖weight A u θ P t - weight B u θ P t‖ ≤
      Real.exp (C*U) * (2*(‖A-B‖*U)) * M := by
  have hU : 0 ≤ U := (abs_nonneg t).trans ht
  have hz : ‖-(A-B)*(t : ℂ)‖ ≤ ‖A-B‖*U := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have he : Complex.exp (-A*t) - Complex.exp (-B*t) =
      Complex.exp (-B*t) * (Complex.exp (-(A-B)*t)-1) := by
    rw [mul_sub_one, ← Complex.exp_add]
    congr 2
    ring
  simp only [weight, ← sub_mul, he, norm_mul]
  apply mul_le_mul _ hP (norm_nonneg _) (by positivity)
  exact mul_le_mul (exp_weight_bound B t C U hB ht)
    ((Complex.norm_exp_sub_one_le (hz.trans hsmall)).trans (by linarith))
    (norm_nonneg _) (Real.exp_pos _).le

#print axioms shift_absorption
#print axioms profile_absorption
#print axioms weight_smooth
#print axioms normalized_log_mem
#print axioms exp_weight_bound
#print axioms weight_bound
#print axioms weight_shift_modulus
end XiPrime8845.ShiftWeights

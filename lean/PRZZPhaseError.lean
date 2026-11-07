import PRZZReplacementIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Quadratic error in the actual logarithmic off-diagonal phase.
The small-ratio condition is explicit. Finite arithmetic aggregation keeps
the coefficient norms; no optimized coefficient sum is assumed. -/
noncomputable section
open scoped BigOperators
open Complex Finset
namespace XiPrime8845.PRZZPhaseError

theorem exp_phase_lipschitz (s t : ℝ) :
    ‖exp (I*(s:ℂ))-exp (I*(t:ℂ))‖ ≤ |s-t| := by
  have he : exp (I*(s:ℂ))-exp (I*(t:ℂ)) =
      exp (I*(t:ℂ))*(exp (I*((s-t:ℝ):ℂ))-1) := by
    rw [mul_sub,← exp_add,mul_one]
    congr 1
    push_cast
    ring
  rw [he,norm_mul]
  have hn : ‖exp (I*(t:ℂ))‖ = 1 := by simp [norm_exp]
  rw [hn,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s-t))

theorem log_remainder (u : ℝ) (hu : |u| ≤ 1/2) :
    |Real.log (1+u)-u| ≤ 2*u^2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by simpa using (show |u| < 1 by linarith)) 1
  norm_num only [sum_range_one,pow_one,Nat.cast_zero,zero_add,div_one,abs_neg] at h
  have he : -u+Real.log (1- -u) = Real.log (1+u)-u := by rw [sub_neg_eq_add]; ring
  rw [he] at h
  have hd : 0 < 1-|u| := by linarith
  apply h.trans
  apply (div_le_iff₀ hd).mpr
  rw [sq_abs]
  nlinarith [sq_nonneg u]

theorem phase_error (t u : ℝ) (hu : |u| ≤ 1/2) :
    ‖exp (I*((t*Real.log (1+u):ℝ):ℂ))-exp (I*((t*u:ℝ):ℂ))‖ ≤
      2*|t| *u^2 := by
  apply (exp_phase_lipschitz _ _).trans
  rw [← mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_left (log_remainder u hu) (abs_nonneg t)).trans_eq (by ring)

/-- The original ratio Delta/(m*n1), with its denominator retained. -/
theorem offDiagonal_error (t delta m n : ℝ) (h : |delta/(m*n)| ≤ 1/2) :
    ‖exp (I*((t*Real.log (1+delta/(m*n)):ℝ):ℂ))-
      exp (I*((t*delta/(m*n):ℝ):ℂ))‖ ≤ 2*|t| *delta^2/(m*n)^2 := by
  convert phase_error t (delta/(m*n)) h using 1 <;> push_cast <;> ring

theorem finite_error {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u : ι → ℝ) (t : ℝ) (hu : ∀ i ∈ s, |u i| ≤ 1/2) :
    ‖(∑ i ∈ s, c i*exp (I*((t*Real.log (1+u i):ℝ):ℂ)))-
      ∑ i ∈ s, c i*exp (I*((t*u i:ℝ):ℂ))‖ ≤
      2*|t| *∑ i ∈ s, ‖c i‖*(u i)^2 := by
  rw [← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [← mul_sub,norm_mul]
  exact (mul_le_mul_of_nonneg_left (phase_error t (u i) (hu i hi))
    (norm_nonneg _)).trans_eq (by ring)

#print axioms exp_phase_lipschitz
#print axioms log_remainder
#print axioms phase_error
#print axioms offDiagonal_error
#print axioms finite_error

/-- Time integration after summing the finite off-diagonal terms. The
coefficient mass remains explicit, before any source-specific count. -/
theorem weighted_finite_error {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u : ι → ℝ) (hu : ∀ i ∈ s, |u i| ≤ 1/2)
    (w : ℝ → ℂ) (hw : Continuous w) (A B : ℝ) :
    ‖∫ t in Set.Icc A B, w t*((∑ i ∈ s, c i*exp (I*((t*Real.log (1+u i):ℝ):ℂ)))-
      ∑ i ∈ s, c i*exp (I*((t*u i:ℝ):ℂ)))‖ ≤
      (2*∑ i ∈ s, ‖c i‖*(u i)^2)*∫ t in Set.Icc A B, ‖w t‖*|t| := by
  have hc : Continuous (fun t : ℝ =>
      (2*∑ i ∈ s, ‖c i‖*(u i)^2)*(‖w t‖*|t|)) := by fun_prop
  have hi : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (2*∑ i ∈ s, ‖c i‖*(u i)^2)*(‖w t‖*|t|)) (Set.Icc A B) := hc.integrableOn_Icc
  apply (MeasureTheory.norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t in Set.Icc A B, (2*∑ i ∈ s, ‖c i‖*(u i)^2)*(‖w t‖*|t|) := by
      apply MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (finite_error s c u t hu)
        (norm_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [MeasureTheory.integral_const_mul]

#print axioms weighted_finite_error
end XiPrime8845.PRZZPhaseError

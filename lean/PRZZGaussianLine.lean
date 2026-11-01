import PRZZDyadicEnvelope
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Gaussian evaluation on the original vertical line Re w = 2.
This evaluates the entire Gaussian kernel; PRZZGaussianTail supplies
its primitive with the factor 1/w. No contour shift or W bound is assumed. -/
noncomputable section
open MeasureTheory Complex
namespace XiPrime8845.PRZZGaussianLine
set_option maxHeartbeats 2000000

def line (t : ℝ) : ℂ := 2+(t:ℂ)*I

theorem exponent (l t : ℝ) :
    (line t)^2-(l:ℂ)*line t =
      (-1:ℂ)*(t:ℂ)^2+((4-(l:ℂ))*I)*(t:ℂ)+(4-2*(l:ℂ)) := by
  unfold line
  ring_nf
  simp only [I_sq]
  ring

theorem gaussian_integrable (l : ℝ) :
    Integrable (fun t : ℝ => exp ((line t)^2-(l:ℂ)*line t)) := by
  simp_rw [exponent]
  exact integrable_cexp_quadratic' (by norm_num : (-1:ℂ).re < 0) _ _

/-- Direct real Gaussian integration: no deformation of a contour. -/
theorem gaussian_integral (l : ℝ) :
    (∫ t : ℝ, exp ((line t)^2-(l:ℂ)*line t)) =
      (Real.pi:ℂ)^(1/2:ℂ)*exp (-(l:ℂ)^2/4) := by
  simp_rw [exponent]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re < 0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [I_sq]
    ring

theorem power_exp (x t : ℝ) (hx : 0 < x) :
    (x:ℂ)^(-line t)*exp ((line t)^2) =
      exp ((line t)^2-(Real.log x:ℂ)*line t) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),ofReal_log hx.le,← exp_add]
  congr 1
  ring

theorem mellin_gaussian_integral (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ, (x:ℂ)^(-line t)*exp ((line t)^2)) =
      (Real.pi:ℂ)^(1/2:ℂ)*exp (-(Real.log x:ℂ)^2/4) := by
  simp_rw [power_exp x _ hx]
  exact gaussian_integral _

#print axioms gaussian_integrable
#print axioms gaussian_integral
#print axioms power_exp
#print axioms mellin_gaussian_integral
end XiPrime8845.PRZZGaussianLine

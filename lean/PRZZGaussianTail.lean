import PRZZGaussianLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The pole kernel 1/w on Re w=2 is a Laplace integral. Absolute
integrability is proved before Fubini; no contour deformation is used. -/
noncomputable section
open MeasureTheory Complex Set
namespace XiPrime8845.PRZZGaussianTail
open PRZZGaussianLine
set_option maxHeartbeats 2000000

def gaussian (u t : ℝ) : ℂ := exp ((line t)^2-(u:ℂ)*line t)

theorem gaussian_norm (u t : ℝ) :
    ‖gaussian u t‖ = Real.exp (-t^2)*Real.exp (4-2*u) := by
  rw [gaussian,norm_exp,exponent]
  norm_num [pow_two]
  rw [← Real.exp_add]

theorem laplace_integral (l t : ℝ) :
    (∫ u in Ioi l, gaussian u t) = gaussian l t/line t := by
  have he (u : ℝ) : gaussian u t = exp ((line t)^2)*exp (-line t*(u:ℂ)) := by
    rw [← exp_add,gaussian]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_complex_Ioi (by simp [line] : (-line t).re < 0)]
  ring

theorem joint_integrable (l : ℝ) :
    Integrable (fun p : ℝ × ℝ => gaussian p.2 p.1)
      (volume.prod (volume.restrict (Ioi l))) := by
  have ht : Integrable (fun t : ℝ => Real.exp (-t^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have hu : Integrable (fun u : ℝ => Real.exp (4-2*u)) (volume.restrict (Ioi l)) := by
    have h := (integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ) < 0) l).const_mul (Real.exp 4)
    simpa only [← Real.exp_add,neg_mul,sub_eq_add_neg] using h
  apply (ht.mul_prod hu).mono'
  · exact (by unfold gaussian line; fun_prop : Continuous (fun p : ℝ × ℝ => gaussian p.2 p.1)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p => (gaussian_norm p.2 p.1).le)

/-- The actual pole integral is a Gaussian tail, with all constants intact. -/
theorem pole_integral (l : ℝ) :
    (∫ t : ℝ, gaussian l t/line t) =
      (Real.pi:ℂ)^(1/2:ℂ)*(∫ u in Ioi l, exp (-(u:ℂ)^2/4)) := by
  simp_rw [← laplace_integral l]
  rw [integral_integral_swap (joint_integrable l)]
  simp only [gaussian,gaussian_integral]
  rw [integral_const_mul]

theorem pole_integrable (l : ℝ) :
    Integrable (fun t : ℝ => gaussian l t/line t) := by
  simpa only [laplace_integral] using (joint_integrable l).integral_prod_left

#print axioms laplace_integral
#print axioms joint_integrable
#print axioms pole_integral
#print axioms pole_integrable
end XiPrime8845.PRZZGaussianTail

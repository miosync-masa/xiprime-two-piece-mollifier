import PRZZPoissonTimeChange
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The final spatial substitution X=n1*n2*x in the post-Poisson W term.
The spatial amplitude is retained literally, including any power and cutoff.
This is not an application of Poisson to the original Gamma weight. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZPoissonSpatial
open PRZZAStar PRZZKloostermanInputs PRZZPoissonTimeChange

def beforeSpatial (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (X t : ℝ) : ℂ :=
  e ((z.2.1:ℝ)*t/(2*Real.pi*X)) *
    W (2*Real.pi*X^2/((z.1.1:ℝ)*z.1.2*t))*Phi (t/T)

theorem kernel_scaled (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x t : ℝ)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) :
    beforeSpatial W Phi T z (((z.1.1:ℝ)*z.1.2)*x) t = timeKernel W Phi T z x t := by
  have hn0 : (z.1.1:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (z.1.2:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold beforeSpatial timeKernel
  congr 2
  · congr 1; ring
  · congr 1
    by_cases ht : t = 0
    · simp [ht]
    · field_simp

/-- The Jacobian and both oscillatory arguments are transformed together.
No rearrangement of time and space integrals occurs. -/
theorem spatial_integral (f W Phi : ℝ → ℂ) (T : ℝ) (z : Index)
    (hn : 0 < z.1.1) (hm : 0 < z.1.2) :
    (∫ X in Ioi (0:ℝ), f X*e (-(z.2.2:ℝ)*X/((z.1.1:ℝ)*z.1.2))*
      ∫ t : ℝ, beforeSpatial W Phi T z X t) =
    (((z.1.1:ℝ)*z.1.2:ℝ):ℂ)*
      ∫ x in Ioi (0:ℝ), f (((z.1.1:ℝ)*z.1.2)*x)*e (-(z.2.2:ℝ)*x)*
        ∫ t : ℝ, timeKernel W Phi T z x t := by
  have hs : 0 < (z.1.1:ℝ)*z.1.2 := by positivity
  have h := integral_comp_mul_left_Ioi'
    (fun X => f X*e (-(z.2.2:ℝ)*X/((z.1.1:ℝ)*z.1.2))*
      ∫ t : ℝ, beforeSpatial W Phi T z X t) 0 hs
  simp only [mul_zero,Complex.real_smul] at h
  rw [← h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  simp_rw [kernel_scaled W Phi T z x _ hn hm]
  have he : -(z.2.2:ℝ)*(((z.1.1:ℝ)*z.1.2)*x)/((z.1.1:ℝ)*z.1.2) =
      -(z.2.2:ℝ)*x := by field_simp
  rw [he]

#print axioms kernel_scaled
#print axioms spatial_integral
end XiPrime8845.PRZZPoissonSpatial

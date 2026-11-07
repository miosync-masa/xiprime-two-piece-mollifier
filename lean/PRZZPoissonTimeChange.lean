import PRZZAStar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Time substitution in the retained post-Poisson W kernel, after the
spatial scale has been changed to the final A* variable. Compare
Pratt--Robles 1706.04593v3, pp. 10 and 15. This proves t=x*n1*n2*y
with its Jacobian. It does not replace the original Gamma kernel by W,
linearize the logarithmic phase, or remove the Poisson frequency tails. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace XiPrime8845.PRZZPoissonTimeChange
open PRZZAStar PRZZKloostermanInputs

def timeKernel (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x t : ℝ) : ℂ :=
  e ((z.2.1:ℝ)*t/(2*Real.pi*(x*z.1.1*z.1.2))) *
    W (2*Real.pi*x*(x*z.1.1*z.1.2)/t)*Phi (t/T)

theorem timeKernel_scaled (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x y : ℝ)
    (hx : 0 < x) (hn : 0 < z.1.1) (hm : 0 < z.1.2) :
    timeKernel W Phi T z x ((x*z.1.1*z.1.2)*y) = innerKernel W Phi T z x y := by
  have hn0 : (z.1.1:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (z.1.2:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold timeKernel innerKernel
  congr 2
  · congr 1; field_simp
  · congr 1
    by_cases hy : y = 0
    · simp [hy]
    · field_simp
  · congr 1; ring

theorem time_integral (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x : ℝ)
    (hx : 0 < x) (hn : 0 < z.1.1) (hm : 0 < z.1.2) :
    (∫ t : ℝ, timeKernel W Phi T z x t) =
      ((x*z.1.1*z.1.2:ℝ):ℂ)*(∫ y : ℝ, innerKernel W Phi T z x y) := by
  have hS : 0 < x*(z.1.1:ℝ)*z.1.2 := by positivity
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (timeKernel W Phi T z x) (x*(z.1.1:ℝ)*z.1.2)
  simp_rw [timeKernel_scaled W Phi T z x _ hx hn hm] at h
  rw [abs_of_pos (inv_pos.mpr hS),Complex.real_smul] at h
  have hSc : ((x*(z.1.1:ℝ)*z.1.2:ℝ):ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  rw [h,Complex.ofReal_inv]
  field_simp

/-- All original finite masks and coefficients are unchanged. Only the
time integral is transformed; no Fubini assumption is needed here. -/
theorem literal_time_form (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) :
    literal N d D H T a F1 F2 FM W Phi alpha beta =
      ∑ z ∈ indices N d D H, prefactor a F1 F2 d alpha beta z *
        ∫ x in Ioi (0:ℝ),
          (outerKernel FM alpha beta z x/((x*z.1.1*z.1.2:ℝ):ℂ))*
            ∫ t : ℝ, timeKernel W Phi T z x t := by
  unfold literal
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have hn := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  have hn1 : 0 < z.1.1 := by have := (Finset.mem_Icc.mp hn.1).1; omega
  have hn2 : 0 < z.1.2 := by have := (Finset.mem_Icc.mp hn.2).1; omega
  dsimp only
  rw [time_integral W Phi T z x hx hn1 hn2]
  have hs : ((x*(z.1.1:ℝ)*z.1.2:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (show x*(z.1.1:ℝ)*z.1.2 ≠ 0 by positivity)
  field_simp

#print axioms timeKernel_scaled
#print axioms time_integral
#print axioms literal_time_form
end XiPrime8845.PRZZPoissonTimeChange

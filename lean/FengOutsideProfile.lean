import FengOutside
import WeightDerivatives
import BetaKernel

/-! Identification of the outside convolution's limiting profile.
This is an exact analytic identity, not a limit theorem for the finite
prime-power transform. That arithmetic convergence remains a separate input. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.FengOutsideProfile
open ShiftWeights WeightDerivatives BetaKernel

def convolution (A : ℂ) (u θ : ℝ) (G : Polynomial ℂ) : ℂ :=
  ∫ t in 0..u, (t:ℂ)*Complex.exp (-A*t)*D 1 A θ (u-t) G

theorem convolution_inverse (A : ℂ) (u θ : ℝ) (G : Polynomial ℂ) (hG : G.eval 0 = 0) :
    convolution A u θ G = D (-1) A θ u G := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (t:ℂ)*weight A u θ G t)
      (weight A u θ G t-(t:ℂ)*Complex.exp (-A*t)*D 1 A θ (u-t) G) t := by
    convert! (Complex.hasDerivAt_ofReal t).mul (weight_hasDerivAt A u θ t G) using 1
    all_goals dsimp [first,weight,D]; ring
  have hw : Continuous (weight A u θ G) := (weight_smooth A u θ G).continuous
  have hc : Continuous (fun t : ℝ => (t:ℂ)*Complex.exp (-A*t)*D 1 A θ (u-t) G) := by
    unfold D
    norm_num
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((hw.sub hc).intervalIntegrable 0 u)
  rw [intervalIntegral.integral_sub (hw.intervalIntegrable 0 u) (hc.intervalIntegrable 0 u)] at hh
  simp only [weight,sub_self,zero_div,Complex.ofReal_zero,hG,mul_zero,zero_mul,sub_zero] at hh
  change convolution A u θ G = ∫ t in 0..u, weight A u θ G t
  exact sub_eq_zero.mp hh |>.symm

/-- The candidate outer profile has exactly the E(1,-1,1) normalization. -/
theorem outer_integral (A B : ℂ) (θ : ℝ) (P G : Polynomial ℂ) (hG : G.eval 0 = 0) :
    (∫ v in 0..θ, D 1 A θ (θ-v) P*convolution B (θ-v) θ G) =
      monomialIntegral A B θ P G 1 (-1) 1 := by
  simp only [convolution_inverse B _ θ G hG,monomialIntegral,Nat.sub_self,
    pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul]

#print axioms convolution_inverse
#print axioms outer_integral
end XiPrime8845.FengOutsideProfile

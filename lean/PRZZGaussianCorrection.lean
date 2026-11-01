import PRZZGaussianTail

/-! The first Gaussian moment supplies the polynomial correction to W. -/
noncomputable section
open MeasureTheory Complex Set Filter Topology
namespace XiPrime8845.PRZZGaussianCorrection
open PRZZGaussianLine PRZZGaussianTail
set_option maxHeartbeats 2000000

theorem line_norm_le (t : ℝ) : ‖line t‖ ≤ 2+|t| := by
  exact (norm_add_le _ _).trans_eq (by simp)

theorem moment_integrable (l : ℝ) :
    Integrable (fun t : ℝ => line t*gaussian l t) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-t^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have h1 : Integrable (fun t : ℝ => |t| * Real.exp (-t^2)) := by
    simpa [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).norm
  have hi := ((h0.const_mul 2).add h1).mul_const (Real.exp (4-2*l))
  apply hi.mono' (by unfold gaussian line; fun_prop)
  apply Eventually.of_forall
  intro t
  rw [norm_mul,gaussian_norm]
  have hh := mul_le_mul_of_nonneg_right (line_norm_le t)
    (mul_nonneg (Real.exp_pos (-t^2)).le (Real.exp_pos (4-2*l)).le)
  exact hh.trans_eq (by dsimp only [Pi.add_apply]; ring)

theorem gaussian_deriv (l t : ℝ) :
    HasDerivAt (gaussian l) (((2*line t-(l:ℂ))*I)*gaussian l t) t := by
  have hw : HasDerivAt line I t := by
    change HasDerivAt (fun x : ℝ => 2+(x:ℂ)*I) I t
    simpa only [id_eq,Complex.ofReal_one,one_mul] using
      (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add 2
  convert ((hw.pow 2).sub (hw.const_mul (l:ℂ))).cexp using 1
  · rfl
  · dsimp [gaussian]
    ring

theorem moment_integral (l : ℝ) :
    (∫ t : ℝ, line t*gaussian l t) =
      ((l:ℂ)/2)*((Real.pi:ℂ)^(1/2:ℂ)*exp (-(l:ℂ)^2/4)) := by
  have hg : Integrable (gaussian l) := gaussian_integrable l
  have hi : Integrable (fun t : ℝ => ((2*line t-(l:ℂ))*I)*gaussian l t) := by
    convert ((moment_integrable l).const_mul (2*I)).sub
      (hg.const_mul ((l:ℂ)*I)) using 1
    funext t
    dsimp [gaussian]
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable (gaussian_deriv l) hi
    hg
  have he (t : ℝ) : ((2*line t-(l:ℂ))*I)*gaussian l t =
      (2*I)*(line t*gaussian l t)-((l:ℂ)*I)*gaussian l t := by ring
  simp_rw [he] at hz
  rw [integral_sub ((moment_integrable l).const_mul _) (hg.const_mul _),
    integral_const_mul,integral_const_mul,show (∫ t : ℝ, gaussian l t) =
      (Real.pi:ℂ)^(1/2:ℂ)*exp (-(l:ℂ)^2/4) from gaussian_integral l] at hz
  linear_combination (norm := ring_nf) (-I/2)*hz
  simp only [I_sq]
  ring

#print axioms moment_integrable
#print axioms moment_integral
end XiPrime8845.PRZZGaussianCorrection

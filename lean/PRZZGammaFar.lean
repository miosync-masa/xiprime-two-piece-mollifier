import PRZZGammaPath
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Global bounds for Gamma factors, including the Mellin region where
the imaginary parts of the numerator can vanish. Reflection controls the
reciprocal denominators; no vertical Stirling estimate is used there. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZGammaFar
set_option maxHeartbeats 2000000

theorem gamma_norm_le (z : ℂ) (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, GammaIntegral, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem sin_norm_le (z : ℂ) : ‖sin z‖ ≤ Real.exp |z.im| := by
  have h := norm_sub_le (exp (-z*I)) (exp (z*I))
  have he := congrArg norm (Complex.two_sin (x := z))
  simp only [norm_mul,Complex.norm_ofNat,norm_I,mul_one,norm_exp,
    mul_re,neg_re,neg_im,I_re,I_im,mul_zero,mul_one,zero_sub,neg_neg] at he h
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

theorem gamma_inv_bound (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    ‖(Gamma z)⁻¹‖ ≤ Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|)/Real.pi := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg := Gamma_ne_zero_of_re_pos hz
  have hsin : sin ((Real.pi:ℂ)*z) ≠ 0 := by
    intro hh
    have he := Gamma_mul_Gamma_one_sub z
    rw [hh,div_zero] at he
    exact (mul_ne_zero hg (Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hz1))) he
  have he : (Gamma z)⁻¹ = Gamma (1-z)*sin ((Real.pi:ℂ)*z)/(Real.pi:ℂ) := by
    have hh := (eq_div_iff hsin).mp (Gamma_mul_Gamma_one_sub z)
    field_simp [hg,hpi]
    rw [mul_comm (Real.pi:ℂ) z] at hh
    linear_combination -hh
  rw [he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply mul_le_mul (gamma_norm_le _ (by simpa using sub_pos.mpr hz1)) _ (norm_nonneg _)
    ((norm_nonneg _).trans (gamma_norm_le _ (by simpa using sub_pos.mpr hz1)))
  simpa [mul_im,abs_mul,abs_of_pos Real.pi_pos] using sin_norm_le ((Real.pi:ℂ)*z)

/-- No restriction on the imaginary part of w is needed. -/
theorem quotient_bound (z w : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1)
    (hw : 0 < w.re) :
    ‖Gamma w/Gamma z‖ ≤ Real.Gamma w.re *
      (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|)/Real.pi) := by
  rw [div_eq_mul_inv,norm_mul]
  exact mul_le_mul (gamma_norm_le w hw) (gamma_inv_bound z hz hz1)
    (norm_nonneg _) ((norm_nonneg _).trans (gamma_norm_le w hw))

/-- Uniform in the numerator's imaginary shift, including cancellation
of the original height. The constant depends only on the fixed shift. -/
theorem shifted_quotient_bound (a : ℂ) (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t v : ℝ,
      ‖Gamma ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2) /
        Gamma ((1/2+a+(t:ℂ)*I)/2)‖ ≤ C*Real.exp (Real.pi*|t|) := by
  let r := (1/2+a.re)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hr' : r < 1 := by dsimp [r]; linarith
  let C := Real.Gamma (r+1)*Real.Gamma (1-r)/Real.pi*Real.exp (Real.pi*|a.im|)
  have h1 := Real.Gamma_pos_of_pos (show 0 < r+1 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < 1-r by linarith)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t v
  have he : ((1/2+a+(t:ℂ)*I)/2).re = r := by simp [r]
  have he' : ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2).re = r+1 := by simp [r]; ring
  have hh := quotient_bound ((1/2+a+(t:ℂ)*I)/2)
    ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2)
    (by rw [he]; exact hr) (by rw [he]; exact hr') (by rw [he']; linarith)
  rw [he,he'] at hh
  have him : |((1/2+a+(t:ℂ)*I)/2).im| ≤ |a.im|+|t| := by
    simp only [div_ofNat_im,add_im,one_im,zero_div,mul_im,ofReal_re,I_im,
      ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add,abs_div]
    norm_num only
    have := abs_add_le a.im t
    linarith [abs_nonneg a.im,abs_nonneg t]
  apply hh.trans
  calc
    _ ≤ Real.Gamma (r+1)*(Real.Gamma (1-r)*
        Real.exp (Real.pi*(|a.im|+|t|))/Real.pi) := by gcongr
    _ = C*Real.exp (Real.pi*|t|) := by
      rw [mul_add,Real.exp_add]
      dsimp [C]
      ring

/-- A global envelope for the actual two-factor AFE ratio. Its constant
precedes both height and Mellin frequency; no central-region premise. -/
theorem actual_ratio_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t v : ℝ,
      ‖PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤
        C*Real.exp (2*Real.pi*|t|) := by
  obtain ⟨Ca,hCa,hA⟩ := shifted_quotient_bound a ha ha'
  obtain ⟨Cb,hCb,hB⟩ := shifted_quotient_bound b hb hb'
  refine ⟨Real.pi^(-2:ℝ)*Ca*Cb,by positivity,?_⟩
  intro t v
  have he : PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t =
      (Real.pi:ℂ)^(-(2+(v:ℂ)*I)) *
      (Gamma ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2)) *
      (Gamma ((1/2+b+(2+(v:ℂ)*I)+((-t:ℝ):ℂ)*I)/2)/Gamma ((1/2+b+((-t:ℝ):ℂ)*I)/2)) := by
    simp only [PRZZAFEGamma.gammaRatio,ofReal_neg,neg_mul,sub_eq_add_neg]
    ring
  rw [he,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  rw [show (-(2+(v:ℂ)*I)).re = (-2:ℝ) by simp]
  have hB' := hB (-t) v
  rw [abs_neg] at hB'
  calc
    _ ≤ Real.pi^(-2:ℝ)*(Ca*Real.exp (Real.pi*|t|))*(Cb*Real.exp (Real.pi*|t|)) := by
      gcongr
      exact hA t v
    _ = _ := by rw [show 2*Real.pi*|t| = Real.pi*|t|+Real.pi*|t| by ring,Real.exp_add]; ring

theorem gaussian_norm (v : ℝ) :
    ‖exp ((2+(v:ℂ)*I)^2)‖ = Real.exp (4-v^2) := by
  rw [norm_exp]
  congr 1
  simp [pow_two,mul_re,mul_im]
  ring

/-- The exponential height loss from reflection is absorbed on the far
Mellin region. The remaining majorant is an integrable Gaussian in v. -/
theorem far_core_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t v : ℝ, 256*Real.pi ≤ T → |t| ≤ 2*T → T/4 ≤ |v| →
      ‖exp ((2+(v:ℂ)*I)^2)*PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤
        C*Real.exp (-T^2/64)*Real.exp (-v^2/2) := by
  obtain ⟨C,hC,h⟩ := actual_ratio_bound a b ha ha' hb hb'
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro T t v hT ht hv
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hquad : 4*Real.pi*T ≤ T^2/64 := by nlinarith
  have hv2 : T^2/16 ≤ v^2 := by nlinarith [sq_abs v]
  have hex : 4-v^2+2*Real.pi*|t| ≤ 4-T^2/64-v^2/2 := by
    nlinarith [Real.pi_pos]
  rw [norm_mul,gaussian_norm]
  calc
    _ ≤ Real.exp (4-v^2)*(C*Real.exp (2*Real.pi*|t|)) := by gcongr; exact h t v
    _ = C*Real.exp (4-v^2+2*Real.pi*|t|) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.exp (4-T^2/64-v^2/2) := by gcongr
    _ = _ := by rw [show 4-T^2/64-v^2/2 = 4+(-T^2/64)+(-v^2/2) by ring,
        Real.exp_add,Real.exp_add]; ring

#print axioms gaussian_norm
#print axioms far_core_bound
#print axioms actual_ratio_bound
#print axioms shifted_quotient_bound
#print axioms quotient_bound
#print axioms gamma_norm_le
#print axioms sin_norm_le
#print axioms gamma_inv_bound
end XiPrime8845.PRZZGammaFar

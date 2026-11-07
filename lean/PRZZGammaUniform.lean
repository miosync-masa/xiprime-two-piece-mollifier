import PRZZGammaFar

/-! Compact real-part envelopes for the far Mellin region. Constants are
chosen before the shifts, the height and the Mellin frequency. -/
noncomputable section
open Complex Set
namespace XiPrime8845.PRZZGammaUniform
set_option maxHeartbeats 2000000

theorem real_gamma_cap : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc (1/8:ℝ) 2, Real.Gamma r ≤ C := by
  have hc : ContinuousOn (fun r : ℝ => Gamma (r:ℂ)) (Icc (1/8:ℝ) 2) := by
    intro r hr
    exact ((PRZZGammaPath.gamma_analytic (r:ℂ) (by simpa using
      (show 0 < r by linarith [hr.1]))).continuousAt.comp
        (x := r) Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro r hr
  have hh := hC r hr
  have he : Real.Gamma r ≤ ‖Gamma (r:ℂ)‖ := by
    change (Gamma (r:ℂ)).re ≤ _
    exact Complex.re_le_norm _
  exact he.trans (hh.trans (by linarith [le_max_left C 0]))

theorem shifted_quotient_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a : ℂ, ‖a‖ ≤ 1/4 →
    ∀ t v : ℝ,
      ‖Gamma ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2) /
        Gamma ((1/2+a+(t:ℂ)*I)/2)‖ ≤ C*Real.exp (Real.pi*|t|) := by
  obtain ⟨C,hC,hcap⟩ := real_gamma_cap
  refine ⟨C*C/Real.pi*Real.exp (Real.pi/4),by positivity,?_⟩
  intro a ha t v
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hai := (Complex.abs_im_le_norm a).trans ha
  let r := (1/2+a.re)/2
  have hr : 1/8 ≤ r ∧ r ≤ 3/8 := by dsimp [r]; constructor <;> linarith [har.1,har.2]
  have he : ((1/2+a+(t:ℂ)*I)/2).re = r := by simp [r]
  have he' : ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2).re = r+1 := by simp [r]; ring
  have hh := PRZZGammaFar.quotient_bound ((1/2+a+(t:ℂ)*I)/2)
    ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2)
    (by rw [he]; linarith [hr.1]) (by rw [he]; linarith [hr.2])
    (by rw [he']; linarith [hr.1])
  rw [he,he'] at hh
  have him : |((1/2+a+(t:ℂ)*I)/2).im| ≤ 1/4+|t| := by
    simp only [div_ofNat_im,add_im,one_im,zero_div,mul_im,ofReal_re,I_im,
      ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add,abs_div]
    norm_num only
    have := abs_add_le a.im t
    linarith [abs_nonneg t]
  have h1 := hcap (r+1) ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have h2 := hcap (1-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have hgpos : 0 < Real.Gamma (1-r) := Real.Gamma_pos_of_pos (by linarith [hr.2])
  apply hh.trans
  calc
    _ ≤ C*(C*Real.exp (Real.pi*(1/4+|t|))/Real.pi) := by
      gcongr
    _ = _ := by rw [mul_add,Real.exp_add,show Real.pi*(1/4) = Real.pi/4 by ring]; ring

#print axioms real_gamma_cap
#print axioms shifted_quotient_uniform

theorem actual_ratio_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → ∀ t v : ℝ,
      ‖PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤ C*Real.exp (2*Real.pi*|t|) := by
  obtain ⟨C,hC,h⟩ := shifted_quotient_uniform
  refine ⟨Real.pi^(-2:ℝ)*C*C,by positivity,?_⟩
  intro a b ha hb t v
  have he : PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t =
      (Real.pi:ℂ)^(-(2+(v:ℂ)*I)) *
      (Gamma ((1/2+a+(2+(v:ℂ)*I)+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2)) *
      (Gamma ((1/2+b+(2+(v:ℂ)*I)+((-t:ℝ):ℂ)*I)/2)/Gamma ((1/2+b+((-t:ℝ):ℂ)*I)/2)) := by
    simp only [PRZZAFEGamma.gammaRatio,ofReal_neg,neg_mul,sub_eq_add_neg]; ring
  rw [he,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  rw [show (-(2+(v:ℂ)*I)).re = (-2:ℝ) by simp]
  have hA := h a ha t v
  have hB := h b hb (-t) v
  rw [abs_neg] at hB
  calc
    _ ≤ Real.pi^(-2:ℝ)*(C*Real.exp (Real.pi*|t|))*(C*Real.exp (Real.pi*|t|)) := by gcongr
    _ = _ := by rw [show 2*Real.pi*|t| = Real.pi*|t|+Real.pi*|t| by ring,Real.exp_add]; ring

theorem far_core_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → ∀ T t v : ℝ,
    256*Real.pi ≤ T → |t| ≤ 2*T → T/4 ≤ |v| →
      ‖exp ((2+(v:ℂ)*I)^2)*PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤
        C*Real.exp (-T^2/64)*Real.exp (-v^2/2) := by
  obtain ⟨C,hC,h⟩ := actual_ratio_uniform
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro a b ha hb T t v hT ht hv
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hquad : 4*Real.pi*T ≤ T^2/64 := by nlinarith
  have hv2 : T^2/16 ≤ v^2 := by nlinarith [sq_abs v]
  have hex : 4-v^2+2*Real.pi*|t| ≤ 4-T^2/64-v^2/2 := by nlinarith [Real.pi_pos]
  rw [norm_mul,PRZZGammaFar.gaussian_norm]
  calc
    _ ≤ Real.exp (4-v^2)*(C*Real.exp (2*Real.pi*|t|)) := by gcongr; exact h a b ha hb t v
    _ = C*Real.exp (4-v^2+2*Real.pi*|t|) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.exp (4-T^2/64-v^2/2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hC.le
    _ = _ := by rw [show 4-T^2/64-v^2/2 = 4+(-T^2/64)+(-v^2/2) by ring,
        Real.exp_add,Real.exp_add]; ring

#print axioms actual_ratio_uniform
#print axioms far_core_uniform
end XiPrime8845.PRZZGammaUniform

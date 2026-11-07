import PRZZLeftCentral

/-! Far-region Gamma envelopes on Re(s)=-1/8. All constants precede the
small shifts and the original height. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZLeftFar
set_option maxHeartbeats 3000000

theorem shifted_quotient_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a : ℂ, ‖a‖ ≤ 1/4 →
    ∀ t v : ℝ,
      ‖Gamma ((1/2+a+(-1/8+(v:ℂ)*I)+(t:ℂ)*I)/2) /
        Gamma ((1/2+a+(t:ℂ)*I)/2)‖ ≤ C*Real.exp (Real.pi*|t|) := by
  obtain ⟨C,hC,hcap⟩ := PRZZDifferenceDecay.gamma_cap
  refine ⟨C*C/Real.pi*Real.exp (Real.pi/4),by positivity,?_⟩
  intro a ha t v
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hai := (Complex.abs_im_le_norm a).trans ha
  let r := (1/2+a.re)/2
  have hr : 1/8 ≤ r ∧ r ≤ 3/8 := by dsimp [r]; constructor <;> linarith [har.1,har.2]
  have he : ((1/2+a+(t:ℂ)*I)/2).re = r := by simp [r]
  have he' : ((1/2+a+(-1/8+(v:ℂ)*I)+(t:ℂ)*I)/2).re = r-1/16 := by simp [r]; ring
  have hh := PRZZGammaFar.quotient_bound ((1/2+a+(t:ℂ)*I)/2)
    ((1/2+a+(-1/8+(v:ℂ)*I)+(t:ℂ)*I)/2)
    (by rw [he]; linarith [hr.1]) (by rw [he]; linarith [hr.2])
    (by rw [he']; linarith [hr.1])
  rw [he,he'] at hh
  have him : |((1/2+a+(t:ℂ)*I)/2).im| ≤ 1/4+|t| := by
    simp only [div_ofNat_im,add_im,one_im,zero_div,mul_im,ofReal_re,I_im,
      ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add,abs_div]
    norm_num only
    have := abs_add_le a.im t
    linarith [abs_nonneg t]
  have h1 := hcap (r-1/16) ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have h2 := hcap (1-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩
  have hgpos : 0 < Real.Gamma (1-r) := Real.Gamma_pos_of_pos (by linarith [hr.2])
  apply hh.trans
  calc
    _ ≤ C*(C*Real.exp (Real.pi*(1/4+|t|))/Real.pi) := by
      gcongr
    _ = _ := by rw [mul_add,Real.exp_add,show Real.pi*(1/4) = Real.pi/4 by ring]; ring

#print axioms shifted_quotient_uniform

theorem actual_ratio_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → ∀ t v : ℝ,
      ‖PRZZAFEGamma.gammaRatio a b (-1/8+(v:ℂ)*I) t‖ ≤ C*Real.exp (2*Real.pi*|t|) := by
  obtain ⟨C,hC,h⟩ := shifted_quotient_uniform
  refine ⟨Real.pi^(1/8:ℝ)*C*C,by positivity,?_⟩
  intro a b ha hb t v
  have he : PRZZAFEGamma.gammaRatio a b (-1/8+(v:ℂ)*I) t =
      (Real.pi:ℂ)^(-(-1/8+(v:ℂ)*I)) *
      (Gamma ((1/2+a+(-1/8+(v:ℂ)*I)+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2)) *
      (Gamma ((1/2+b+(-1/8+(v:ℂ)*I)+((-t:ℝ):ℂ)*I)/2)/Gamma ((1/2+b+((-t:ℝ):ℂ)*I)/2)) := by
    simp only [PRZZAFEGamma.gammaRatio,ofReal_neg,neg_mul,sub_eq_add_neg]; ring
  rw [he,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  rw [show (-(-1/8+(v:ℂ)*I)).re = (1/8:ℝ) by norm_num]
  have hA := h a ha t v
  have hB := h b hb (-t) v
  rw [abs_neg] at hB
  calc
    _ ≤ Real.pi^(1/8:ℝ)*(C*Real.exp (Real.pi*|t|))*(C*Real.exp (Real.pi*|t|)) := by gcongr
    _ = _ := by rw [show 2*Real.pi*|t| = Real.pi*|t|+Real.pi*|t| by ring,Real.exp_add]; ring


theorem far_core_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → ∀ T t v : ℝ,
    256*Real.pi ≤ T → |t| ≤ 2*T → T/4 ≤ |v| →
      ‖exp ((PRZZLeftCentral.line v)^2)*
        PRZZAFEGamma.gammaRatio a b (PRZZLeftCentral.line v) t‖ ≤
        C*Real.exp (-T^2/64)*Real.exp (-v^2/2) := by
  obtain ⟨C,hC,h⟩ := actual_ratio_uniform
  refine ⟨C*Real.exp 4,by positivity,?_⟩
  intro a b ha hb T t v hT ht hv
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hquad : 4*Real.pi*T ≤ T^2/64 := by nlinarith
  have hv2 : T^2/16 ≤ v^2 := by nlinarith [sq_abs v]
  have hex : 4-v^2+2*Real.pi*|t| ≤ 4-T^2/64-v^2/2 := by nlinarith [Real.pi_pos]
  rw [norm_mul]
  calc
    _ ≤ Real.exp (4-v^2)*(C*Real.exp (2*Real.pi*|t|)) := by
      gcongr
      · exact PRZZLeftCentral.gaussian_line v
      · exact h a b ha hb t v
    _ = C*Real.exp (4-v^2+2*Real.pi*|t|) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.exp (4-T^2/64-v^2/2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hC.le
    _ = _ := by rw [show 4-T^2/64-v^2/2 = 4+(-T^2/64)+(-v^2/2) by ring,
        Real.exp_add,Real.exp_add]; ring

theorem far_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x q v : ℝ,
    256*Real.pi ≤ T → |t| ≤ 2*T → 0 < x → 0 < q → T/4 ≤ |v| →
      ‖PRZZDifferenceRegular.regular a b x t q (PRZZLeftCentral.line v)‖ ≤
        C*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*(1+q^(-1/8:ℝ))*Real.exp (-T^2/64)*
          PRZZCentralIntegral.majorant v := by
  obtain ⟨C,hC,h⟩ := far_core_uniform
  refine ⟨8*(C+Real.exp 4),by positivity,?_⟩
  intro a b ha hb hs T t x q v hT ht hx hq hv
  let s := PRZZLeftCentral.line v
  let F := Real.exp (-T^2/64)
  let G := Real.exp (-v^2/2)
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hv2 : T^2/16 ≤ v^2 := by nlinarith [sq_abs v]
  have he : ‖exp (s^2)‖ ≤ Real.exp 4*F*G := by
    apply (PRZZLeftCentral.gaussian_line v).trans
    dsimp [F,G]
    rw [← Real.exp_add,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hqpow : ‖(q:ℂ)^s‖ = q^(-1/8:ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hq,PRZZLeftCentral.line_re]
    norm_num
  have hxp : ‖(x:ℂ)^(-s)‖ = x^(1/8:ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx,neg_re,PRZZLeftCentral.line_re]; norm_num
  have hbnd : ‖exp (s^2)‖*‖PRZZDifferenceRegular.numerator a b t q s‖ ≤
      (C+Real.exp 4)*(1+q^(-1/8:ℝ))*F*G := by
    have hg := h a b ha hb T t v hT ht hv
    rw [norm_mul] at hg
    have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ q^(-1/8:ℝ) by positivity)
    have htri := mul_le_mul_of_nonneg_left
      (norm_sub_le (PRZZAFEGamma.gammaRatio a b s t) ((q:ℂ)^s)) (norm_nonneg (exp (s^2)))
    rw [hqpow] at htri
    have hn : 0 ≤ C*q^(-1/8:ℝ)*F*G := by dsimp [F,G]; positivity
    change ‖exp (s^2)‖*‖PRZZDifferenceRegular.numerator a b t q s‖ ≤ _ at htri
    dsimp only [F,G,s] at *
    nlinarith only [hg,hm,htri,hn,show 0 ≤ Real.exp 4*Real.exp (-T^2/64)*Real.exp (-v^2/2) by positivity]
  have ar := (abs_le.mp ((abs_re_le_norm a).trans ha)).1
  have br := (abs_le.mp ((abs_re_le_norm b).trans hb)).1
  rw [PRZZDifferenceRegular.regular_eq a b s x t q (by linarith) (by linarith)
    (PRZZLeftCentral.line_ne_zero v),div_eq_mul_inv]
  simp only [norm_mul,hxp]
  calc
    _ = x^(1/8:ℝ)*‖PRZZDyadicEnvelope.annihilator (a+b) s‖*‖s⁻¹‖*
        (‖exp (s^2)‖*‖PRZZDifferenceRegular.numerator a b t q s‖) := by ring
    _ ≤ x^(1/8:ℝ)*((1+32/‖a+b‖^2)*(1+v^2))*8*
        ((C+Real.exp 4)*(1+q^(-1/8:ℝ))*F*G) := by
      gcongr
      · exact PRZZLeftCentral.annihilator_line (a+b) hs v
      · exact PRZZLeftCentral.inverse_bound v
    _ = (8*(C+Real.exp 4))*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*(1+q^(-1/8:ℝ))*F*((1+v^2)*G) := by ring
    _ ≤ _ := by
      dsimp [PRZZCentralIntegral.majorant,F,G]
      gcongr
      nlinarith [sq_nonneg (v^2)]

#print axioms far_bound
#print axioms far_core_uniform
#print axioms actual_ratio_uniform
end XiPrime8845.PRZZLeftFar

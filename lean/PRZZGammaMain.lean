import PRZZGammaCentral
import PRZZKernelDifference

/-! Central Gamma factors and cancellation of their signed reference phases.
All error constants below are independent of the small shifts. -/
noncomputable section
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.PRZZGammaMain
set_option maxHeartbeats 3000000

theorem single_factor_strip (T t : ℝ) (a s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ |t|) (ha : ‖a‖ ≤ 1/4) (hs : |s.im| ≤ T/4) (hsr : -(1/8:ℝ) ≤ s.re) :
    ∃ E : ℂ, ‖E‖ ≤ ‖s‖*(26+‖s‖)/T ∧
      Gamma ((1/2+a+s+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2) =
        exp ((s/2)*log ((t:ℂ)*I/2)+E) := by
  let z : ℂ := (1/2+a+(t:ℂ)*I)/2
  let d : ℂ := s/2
  let w : ℂ := (t:ℂ)*I/2
  have he (u : ℝ) : z+(u:ℂ)*d = (1/2+a+(u:ℂ)*s+(t:ℂ)*I)/2 := by dsimp [z,d]; ring
  have har : -(1/4:ℝ) ≤ a.re := by
    have := (Complex.abs_re_le_norm a).trans ha
    linarith [(abs_le.mp this).1]
  have hr (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : 0 < (z+(u:ℂ)*d).re := by
    rw [he]
    simp only [div_ofNat_re,add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_self,sub_zero,add_zero]
    norm_num
    nlinarith [hu.2,mul_nonneg hu.1 (show 0 ≤ s.re+1/8 by linarith)]
  have hp : Continuous (fun u : ℝ => z+(u:ℂ)*d) := by fun_prop
  have hc : ContinuousOn (fun u : ℝ => d*digamma (z+(u:ℂ)*d)) (Icc 0 1) := by
    intro u hu
    have hg := PRZZGammaPath.gamma_analytic _ (hr u hu)
    have hh : ContinuousAt digamma (z+(u:ℂ)*d) :=
      hg.deriv.continuousAt.div hg.continuousAt (Gamma_ne_zero_of_re_pos (hr u hu))
    exact (continuousAt_const.mul (hh.comp (x := u) hp.continuousAt)).continuousWithinAt
  have hb (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      ‖d*(digamma (z+(u:ℂ)*d)-log w)‖ ≤ ‖s‖*(26+‖s‖)/T := by
    have hui : |((u:ℂ)*s).im| ≤ T/4 := by
      simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,abs_mul,abs_of_nonneg hu.1]
      nlinarith [hu.2,abs_nonneg s.im]
    have hg := PRZZAFEGamma.gamma_argument_error T t a ((u:ℂ)*s) hT ht
      ((Complex.abs_im_le_norm a).trans (ha.trans (by linarith))) hui (by
        simp only [add_re,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
        norm_num
        nlinarith [hu.2,mul_nonneg hu.1 (show 0 ≤ s.re+1/8 by linarith)])
    have hl := PRZZGammaCentral.actual_log_comparison T t u a s hT ht hu ha hs
    rw [← he] at hg hl
    have htri : ‖digamma (z+(u:ℂ)*d)-log w‖ ≤ 50/T+2*(1+‖s‖)/T := by
      calc
        _ ≤ ‖digamma (z+(u:ℂ)*d)-log (z+(u:ℂ)*d)‖+
          ‖log (z+(u:ℂ)*d)-log w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := add_le_add hg hl
    rw [norm_mul]
    have hd : ‖d‖ = ‖s‖/2 := by simp [d]
    rw [hd]
    exact (mul_le_mul_of_nonneg_left htri (by positivity)).trans_eq (by ring)
  let E := ∫ u in (0:ℝ)..1, d*(digamma (z+(u:ℂ)*d)-log w)
  refine ⟨E, ?_, ?_⟩
  · have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (fun u hu => hb u (by
        simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),mem_Ioc] at hu
        exact ⟨hu.1.le,hu.2⟩))
    simpa [E] using hh
  · have hE : E = (∫ u in (0:ℝ)..1, d*digamma (z+(u:ℂ)*d))-d*log w := by
      dsimp [E]; simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc (by norm_num)) intervalIntegrable_const]
      simp
    have hh := PRZZGammaPath.ratio_eq_exp_integral z d hr
    have hz : z+d = (1/2+a+s+(t:ℂ)*I)/2 := by dsimp [z,d]; ring
    rw [hz] at hh
    rw [hh,hE]
    congr 1
    dsimp [d,w]; ring

#print axioms single_factor_strip

theorem reference_phases (t : ℝ) (ht : 0 < t) :
    log ((t:ℂ)*I/2)+log ((-t:ℝ)*I/2) = 2*(Real.log (t/2):ℂ) := by
  have h1 := log_mul_ofReal (t/2) (by positivity) I I_ne_zero
  have h2 := log_mul_ofReal (t/2) (by positivity) (-I) (neg_ne_zero.mpr I_ne_zero)
  have he1 : (t:ℂ)*I/2 = I*(t/2:ℝ) := by push_cast; ring
  have he2 : ((-t:ℝ):ℂ)*I/2 = (-I)*(t/2:ℝ) := by push_cast; ring
  rw [he1,he2,h1,h2,log_I,log_neg_I]
  ring

/-- The principal reference phases cancel exactly, before taking norms. -/
theorem main_phase (t : ℝ) (s : ℂ) (ht : 0 < t) :
    (Real.pi:ℂ)^(-s)*exp ((s/2)*log ((t:ℂ)*I/2)+(s/2)*log ((-t:ℝ)*I/2)) =
      (t/(2*Real.pi):ℝ)^s := by
  rw [show (s/2)*log ((t:ℂ)*I/2)+(s/2)*log ((-t:ℝ)*I/2) =
    (s/2)*(log ((t:ℂ)*I/2)+log ((-t:ℝ)*I/2)) by ring,
    reference_phases t ht]
  rw [cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero),
    cpow_def_of_ne_zero (by exact_mod_cast (show (t/(2*Real.pi):ℝ) ≠ 0 by positivity)),
    ← exp_add, ← ofReal_log Real.pi_pos.le,
    ← ofReal_log (show 0 ≤ t/(2*Real.pi) by positivity)]
  congr 1
  rw [show t/(2*Real.pi) = (t/2)/Real.pi by ring,
    Real.log_div (by positivity) Real.pi_ne_zero,ofReal_sub]
  ring

#print axioms reference_phases
#print axioms main_phase

theorem ratio_main_error_strip (T t : ℝ) (a b s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ t) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : |s.im| ≤ T/4) (hsr : -(1/8:ℝ) ≤ s.re) :
    ∃ E : ℂ, ‖E‖ ≤ 2*‖s‖*(26+‖s‖)/T ∧
      PRZZAFEGamma.gammaRatio a b s t = (t/(2*Real.pi):ℝ)^s*exp E := by
  have ht0 : 0 < t := by linarith
  obtain ⟨Ea,haE,haq⟩ := single_factor_strip T t a s hT (by rwa [abs_of_pos ht0]) ha hs hsr
  obtain ⟨Eb,hbE,hbq⟩ := single_factor_strip T (-t) b s hT (by rwa [abs_neg,abs_of_pos ht0]) hb hs hsr
  refine ⟨Ea+Eb,(norm_add_le _ _).trans ((add_le_add haE hbE).trans_eq (by ring)),?_⟩
  have he : PRZZAFEGamma.gammaRatio a b s t = (Real.pi:ℂ)^(-s)*
      (Gamma ((1/2+a+s+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2))*
      (Gamma ((1/2+b+s+((-t:ℝ):ℂ)*I)/2)/Gamma ((1/2+b+((-t:ℝ):ℂ)*I)/2)) := by
    simp only [PRZZAFEGamma.gammaRatio,ofReal_neg,neg_mul,sub_eq_add_neg]
    ring
  rw [he,haq,hbq,exp_add,exp_add]
  calc
    _ = ((Real.pi:ℂ)^(-s)*exp ((s/2)*log ((t:ℂ)*I/2)+(s/2)*log ((-t:ℝ)*I/2)))*exp (Ea+Eb) := by
      simp only [exp_add]; ring
    _ = _ := by rw [main_phase t s ht0]

theorem ratio_relative_bound_strip (T t : ℝ) (a b s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ t) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : |s.im| ≤ T/4) (hsr : -(1/8:ℝ) ≤ s.re) :
    ‖PRZZAFEGamma.gammaRatio a b s t-(t/(2*Real.pi):ℝ)^s‖ ≤
      ‖((t/(2*Real.pi):ℝ):ℂ)^s‖ *
        (2*‖s‖*(26+‖s‖)/T)*Real.exp (2*‖s‖*(26+‖s‖)/T) := by
  obtain ⟨E,hE,he⟩ := ratio_main_error_strip T t a b s hT ht ha hb hs hsr
  rw [he,← mul_sub_one,norm_mul]
  have hh : ‖exp E-1‖ ≤ ‖E‖*Real.exp ‖E‖ := by
    simpa using norm_exp_sub_sum_le_norm_mul_exp E 1
  apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans
  rw [mul_assoc]
  gcongr

#print axioms ratio_main_error_strip
#print axioms ratio_relative_bound_strip

/-- Compatibility on the original right half-plane. -/
theorem single_factor (T t : ℝ) (a s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ |t|) (ha : ‖a‖ ≤ 1/4) (hs : |s.im| ≤ T/4) (hsr : 0 ≤ s.re) :
    ∃ E : ℂ, ‖E‖ ≤ ‖s‖*(26+‖s‖)/T ∧
      Gamma ((1/2+a+s+(t:ℂ)*I)/2)/Gamma ((1/2+a+(t:ℂ)*I)/2) =
        exp ((s/2)*log ((t:ℂ)*I/2)+E) :=
  single_factor_strip T t a s hT ht ha hs (by linarith)

theorem ratio_main_error (T t : ℝ) (a b s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ t) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : |s.im| ≤ T/4) (hsr : 0 ≤ s.re) :
    ∃ E : ℂ, ‖E‖ ≤ 2*‖s‖*(26+‖s‖)/T ∧
      PRZZAFEGamma.gammaRatio a b s t = (t/(2*Real.pi):ℝ)^s*exp E :=
  ratio_main_error_strip T t a b s hT ht ha hb hs (by linarith)

theorem ratio_relative_bound (T t : ℝ) (a b s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ t) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : |s.im| ≤ T/4) (hsr : 0 ≤ s.re) :
    ‖PRZZAFEGamma.gammaRatio a b s t-(t/(2*Real.pi):ℝ)^s‖ ≤
      ‖((t/(2*Real.pi):ℝ):ℂ)^s‖ *
        (2*‖s‖*(26+‖s‖)/T)*Real.exp (2*‖s‖*(26+‖s‖)/T) :=
  ratio_relative_bound_strip T t a b s hT ht ha hb hs (by linarith)

#print axioms single_factor
#print axioms ratio_main_error
#print axioms ratio_relative_bound
end XiPrime8845.PRZZGammaMain

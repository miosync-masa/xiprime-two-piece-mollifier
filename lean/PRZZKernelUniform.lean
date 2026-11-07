import PRZZCentralIntegral
import PRZZGammaUniform

/-! A uniform integrated comparison of the actual Gamma kernel with sourceW.
The sum-of-shifts singularity and the x/height scale remain explicit. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZKernelUniform
open PRZZMellinTail PRZZKernelDifference PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem far_integral_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x q : ℝ,
    256*Real.pi ≤ T → |t| ≤ 2*T → 0 < x → 0 < q →
      (∫ v in {v : ℝ | T/4 ≤ |v|}, ‖errorIntegrand a b x t q v‖) ≤
        C*(1+q^2)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64) := by
  obtain ⟨C,hC,h⟩ := PRZZGammaUniform.far_core_uniform
  let J := ∫ v, majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by dsimp [majorant]; positivity)
  refine ⟨(C+Real.exp 4)*(J+1),by positivity,?_⟩
  intro a b ha hb hs T t x q hT ht hx hq
  let S := {v : ℝ | T/4 ≤ |v|}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  let B := (C+Real.exp 4)*(1+q^2)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := majorant_integrable.const_mul B
  have hp : ∀ v ∈ S, ‖errorIntegrand a b x t q v‖ ≤ B*majorant v := by
    intro v hv
    have h1 : ‖integrand a b x t v‖ ≤
        C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)*majorant v := by
      rw [integrand,norm_mul]
      exact (mul_le_mul (factor_bound (a+b) hs x v hx) (h a b ha hb T t v hT ht hv)
        (norm_nonneg _) (by positivity)).trans_eq (by dsimp [majorant]; ring)
    have h2 := far_main_bound (a+b) hs T x q v
      (by have := Real.pi_pos; linarith) hx hq hv
    rw [error_eq]
    apply (norm_sub_le _ _).trans
    have hn : 0 ≤ x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)*majorant v := by
      dsimp [majorant]; positivity
    have hh := mul_nonneg (show 0 ≤ C*q^2+Real.exp 4 by positivity) hn
    dsimp [B,majorant] at *
    nlinarith only [h1,h2,hh]
  have he : (∫ v in S, ‖errorIntegrand a b x t q v‖) ≤ ∫ v in S, B*majorant v := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => norm_nonneg _)) hg.integrableOn
    filter_upwards [ae_restrict_mem hS] with v hv
    exact hp v hv
  apply he.trans
  apply (setIntegral_le_integral (s := S) hg
    (Filter.Eventually.of_forall (fun v => mul_nonneg hB (by dsimp [majorant]; positivity)))).trans
  rw [integral_const_mul]
  dsimp [B,J]
  nlinarith only [hB]

/-- One constant works for all small shifts. This is an actual integrated
V-W estimate, not a premise on the central or far error. -/
theorem difference_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤
        C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*
          ((t/(2*Real.pi))^2/T+(1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64)) := by
  obtain ⟨Cc,hCc,hc⟩ := PRZZCentralIntegral.central_integral_bound
  obtain ⟨Cf,hCf,hf⟩ := far_integral_uniform
  refine ⟨(Cc+Cf)/(2*Real.pi),by positivity,?_⟩
  intro a b ha hb hs T t x hT hT' ht ht2 hx
  have ht0 : 0 < t := by linarith
  have hq : 0 < t/(2*Real.pi) := by positivity
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  have hra : -(1/2:ℝ) < a.re := by linarith [har.1]
  have hra' : a.re < 3/2 := by linarith [har.2]
  have hrb : -(1/2:ℝ) < b.re := by linarith [hbr.1]
  have hrb' : b.re < 3/2 := by linarith [hbr.2]
  have hsplit := integral_add_compl (s := {v : ℝ | |v| < T/4})
    (isOpen_lt continuous_abs continuous_const).measurableSet
    (error_integrable a b hra hra' hrb hrb' hs x t (t/(2*Real.pi)) hx hq).norm
  have hbnd := hf a b ha hb hs T t x (t/(2*Real.pi)) hT (by simpa [abs_of_pos ht0] using ht2) hx hq
  have hcb := hc a b ha hb hs T t x hT' ht hx
  have hn := difference_norm_le a b hra hra' hrb hrb' hs x t hx ht0
  rw [← hsplit] at hn
  simp only [Set.compl_ofPred,not_lt] at hn
  have he := mul_le_mul_of_nonneg_left (add_le_add hcb hbnd) (show 0 ≤ 1/(2*Real.pi) by positivity)
  apply hn.trans (he.trans _)
  have h1 : 0 ≤ Cf*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(t/(2*Real.pi))^2/T := by positivity
  have h2 : 0 ≤ Cc*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64) := by positivity
  have hh := mul_nonneg (show 0 ≤ 1/(2*Real.pi) by positivity) (add_nonneg h1 h2)
  apply sub_nonneg.mp
  convert hh using 1; ring

#print axioms far_integral_uniform
#print axioms difference_uniform

/-- Uniformity for the actual logarithmically scaled shift family.
The separation r keeps the source annihilator away from its singularity. -/
theorem scaled_difference (S r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ t x : ℝ,
      T ≤ t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) x t-
        sourceW ((A+B)/(Real.log T:ℂ)) (x/(t/(2*Real.pi)))‖ ≤
        C*x^(-2:ℝ)*(1+16*(Real.log T)^2/r^2)*
          ((t/(2*Real.pi))^2/T+(1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64)) := by
  obtain ⟨C,hC,h⟩ := difference_uniform
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZGammaCentral.log_scaled_shifts_eventually S,
    Filter.eventually_ge_atTop (256*Real.pi),Filter.eventually_ge_atTop (128:ℝ)] with T hsmall hT hT'
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  intro A B hA hB hsep t x ht ht2 hx
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hLc
  have hh := h _ _ (hsmall A B hA hB).1 (hsmall A B hA hB).2 hs T t x hT hT' ht ht2 hx
  rw [← add_div] at hh
  have he : 16/‖(A+B)/(Real.log T:ℂ)‖^2 = 16*(Real.log T)^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

#print axioms scaled_difference
end XiPrime8845.PRZZKernelUniform

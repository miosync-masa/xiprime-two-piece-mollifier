import PRZZAFEGamma
import WuEdgeLog

/-! Exact Gamma ratios from logarithmic derivatives along a segment.
The segment stays in the right half-plane. No choice of the principal
logarithm of Gamma across its branch cut is used. -/
noncomputable section
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.PRZZGammaPath
set_option maxHeartbeats 2000000

theorem gamma_analytic (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ Gamma z := by
  apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) _
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  intro w hw
  apply (Complex.differentiableAt_Gamma w _).differentiableWithinAt
  intro m he
  have hh := congrArg Complex.re he
  simp only [Complex.neg_re,Complex.natCast_re] at hh
  have := Nat.cast_nonneg (α := ℝ) m
  change 0 < w.re at hw
  linarith

theorem ratio_eq_exp_integral (z d : ℂ)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 0 < (z+(u:ℂ)*d).re) :
    Gamma (z+d)/Gamma z =
      exp (∫ u in (0:ℝ)..1, d*digamma (z+(u:ℂ)*d)) := by
  obtain ⟨q,hq⟩ := XiPrime8845.WuLittlewood.edgeLog_exists Gamma z d 0 1 0
    (by norm_num) (fun u hu => gamma_analytic _ (hr u hu))
    (fun u hu => Gamma_ne_zero_of_re_pos (hr u hu))
    (log (Gamma z)) (by
      simpa using exp_log (Gamma_ne_zero_of_re_pos (by simpa using hr 0 (by norm_num))))
  have he := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    (by simpa using q.continuous) (by simpa using q.derivative) q.integrable
  change (∫ u in (0:ℝ)..1, d*digamma (z+(u:ℂ)*d)) = q.value 1-q.value 0 at he
  rw [he,Complex.exp_sub,q.exp_eq 1 right_mem_uIcc,q.exp_eq 0 left_mem_uIcc]
  simp

/-- An explicit uniform error in the logarithm of the Gamma ratio.
The integral of log along the same path is retained for the next expansion. -/
theorem integrated_error (T : ℝ) (z d : ℂ) (hT : 2 ≤ T)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 0 < (z+(u:ℂ)*d).re)
    (hi : ∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |(z+(u:ℂ)*d).im|) :
    ‖∫ u in (0:ℝ)..1, d*(digamma (z+(u:ℂ)*d)-log (z+(u:ℂ)*d))‖ ≤
      ‖d‖*(50/T) := by
  have hb : ∀ u ∈ Icc (0:ℝ) 1,
      ‖d*(digamma (z+(u:ℂ)*d)-log (z+(u:ℂ)*d))‖ ≤ ‖d‖*(50/T) := by
    intro u hu
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (PRZZAFEGamma.digamma_error T _ hT (hr u hu) (hi u hu)) (norm_nonneg _)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (fun u hu => hb u (by
      simp only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),Set.mem_Ioc] at hu
      exact ⟨hu.1.le,hu.2⟩))
  simpa only [sub_zero,abs_one,mul_one] using hh

/-- The ratio itself, with a supplied exponent error rather than an
assumed relative-error estimate. -/
theorem ratio_with_error (T : ℝ) (z d : ℂ) (hT : 2 ≤ T)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 0 < (z+(u:ℂ)*d).re)
    (hi : ∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |(z+(u:ℂ)*d).im|) :
    ∃ E : ℂ, ‖E‖ ≤ ‖d‖*(50/T) ∧
      Gamma (z+d)/Gamma z = exp ((∫ u in (0:ℝ)..1, d*log (z+(u:ℂ)*d))+E) := by
  refine ⟨∫ u in (0:ℝ)..1, d*(digamma (z+(u:ℂ)*d)-log (z+(u:ℂ)*d)),
    integrated_error T z d hT hr hi,?_⟩
  have hp : Continuous (fun u : ℝ => z+(u:ℂ)*d) := by fun_prop
  have hc : ContinuousOn (fun u : ℝ => d*digamma (z+(u:ℂ)*d)) (Icc 0 1) := by
    intro u hu
    have hg := gamma_analytic _ (hr u hu)
    have hh : ContinuousAt digamma (z+(u:ℂ)*d) :=
      hg.deriv.continuousAt.div hg.continuousAt
        (Gamma_ne_zero_of_re_pos (hr u hu))
    exact (continuousAt_const.mul (hh.comp (x := u) hp.continuousAt)).continuousWithinAt
  have hl : ContinuousOn (fun u : ℝ => d*log (z+(u:ℂ)*d)) (Icc 0 1) := by
    intro u hu
    exact (continuousAt_const.mul ((Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hr u hu)))).continuousAt.comp
        (x := u) hp.continuousAt)).continuousWithinAt
  rw [ratio_eq_exp_integral z d hr]
  congr 1
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
    (hc.intervalIntegrable_of_Icc (by norm_num))
    (hl.intervalIntegrable_of_Icc (by norm_num))]
  ring

#print axioms ratio_with_error
#print axioms gamma_analytic
#print axioms ratio_eq_exp_integral
#print axioms integrated_error
end XiPrime8845.PRZZGammaPath

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The complex-rate Euler integral needed for Abel regularization.
Positive-real decay cannot simply be replaced by epsilon plus or minus I in the
real scaling formula. Integrability and holomorphic parameter dependence
are established here before applying an analytic identity principle. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZGammaLaplace
set_option maxHeartbeats 5000000

def kernel (z c : ℂ) (x : ℝ) : ℂ := (x:ℂ)^(z-1)*Complex.exp (-c*(x:ℂ))
def laplace (z c : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), kernel z c x

theorem real_majorant_integrable (a r : ℝ) (ha : -1 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x^a*Real.exp (-r*x)) (Ioi (0:ℝ)) := by
  have hg := Real.GammaIntegral_convergent (s := a+1) (by linarith)
  simp only [add_sub_cancel_right] at hg
  have hsc : IntegrableOn (fun x : ℝ => Real.exp (-(r*x))*(r*x)^a) (Ioi (0:ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)*x^a) 0 hr).mpr
    simpa only [mul_zero] using hg
  have hs : IntegrableOn (fun x : ℝ => r^(-a)*(Real.exp (-(r*x))*(r*x)^a)) (Ioi 0) := hsc.const_mul _
  apply IntegrableOn.congr_fun hs _ measurableSet_Ioi
  intro x hx
  dsimp only
  simp only [neg_mul]
  rw [Real.mul_rpow hr.le hx.le]
  calc
    _ = (r^(-a)*r^a)*(x^a*Real.exp (-r*x)) := by ring
    _ = _ := by rw [← Real.rpow_add hr,neg_add_cancel,Real.rpow_zero,one_mul]; simp only [neg_mul]

theorem kernel_continuous (z c : ℂ) : ContinuousOn (kernel z c) (Ioi (0:ℝ)) := by
  intro x hx
  have hp := (continuousAt_cpow_const (b := z-1) (Complex.ofReal_mem_slitPlane.mpr hx)).comp
    (x := x) Complex.continuous_ofReal.continuousAt
  exact (hp.mul (by fun_prop : ContinuousAt (fun y : ℝ => Complex.exp (-c*(y:ℂ))) x)).continuousWithinAt

theorem kernel_norm (z c : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖kernel z c x‖ = x^(z.re-1)*Real.exp (-c.re*x) := by
  rw [kernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
  simp only [sub_re,one_re,mul_re,neg_re,neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem kernel_integrable (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    IntegrableOn (kernel z c) (Ioi (0:ℝ)) := by
  apply (real_majorant_integrable (z.re-1) c.re (by linarith) hc).mono'
    ((kernel_continuous z c).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (kernel_norm z c x hx).le

theorem kernel_hasDerivAt (z c : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => kernel z w x) (-(x:ℂ)*kernel z c x) c := by
  have hh := ((Complex.hasDerivAt_exp (-c*(x:ℂ))).comp c
    ((hasDerivAt_id c).neg.mul_const (x:ℂ))).const_mul ((x:ℂ)^(z-1))
  simpa only [Function.comp_apply,Pi.neg_apply,id_eq,one_mul,kernel,
    mul_neg,neg_mul,mul_comm,mul_left_comm,mul_assoc] using hh

theorem derivative_norm (z c : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖-(x:ℂ)*kernel z c x‖ = x^z.re*Real.exp (-c.re*x) := by
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,kernel_norm z c x hx]
  rw [show z.re = 1+(z.re-1) by ring,Real.rpow_add hx,Real.rpow_one]
  ring

theorem laplace_differentiableAt (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    DifferentiableAt ℂ (laplace z) c := by
  let b := fun x : ℝ => x^z.re*Real.exp (-(c.re/2)*x)
  have hb : IntegrableOn b (Ioi (0:ℝ)) := real_majorant_integrable z.re (c.re/2) (by linarith) (by linarith)
  have hmeas : ∀ᶠ w : ℂ in 𝓝 c, AEStronglyMeasurable (kernel z w) (volume.restrict (Ioi (0:ℝ))) :=
    Filter.Eventually.of_forall (fun w => (kernel_continuous z w).aestronglyMeasurable measurableSet_Ioi)
  have hdmeas : AEStronglyMeasurable (fun x : ℝ => -(x:ℂ)*kernel z c x) (volume.restrict (Ioi (0:ℝ))) :=
    (continuous_ofReal.neg.continuousOn.mul (kernel_continuous z c)).aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      ∀ w ∈ Metric.ball c (c.re/2), ‖-(x:ℂ)*kernel z w x‖ ≤ b x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro w hw
    have hn : ‖w-c‖ < c.re/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hl : c.re/2 ≤ w.re := by
      have hh := (neg_le_abs ((w-c).re)).trans (Complex.abs_re_le_norm (w-c))
      simp only [sub_re] at hh
      linarith
    rw [derivative_norm z w x hx]
    dsimp [b]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hl) hx.le)
  have hdiff : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      ∀ w ∈ Metric.ball c (c.re/2), HasDerivAt (fun w => kernel z w x) (-(x:ℂ)*kernel z w x) w :=
    Filter.Eventually.of_forall (fun x w hw => kernel_hasDerivAt z w x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds c (by linarith : 0 < c.re/2)) hmeas
    (kernel_integrable z c hz hc) hdmeas hbound hb hdiff).2.differentiableAt

/-- Euler's integral with a genuine complex decay parameter. -/
theorem laplace_eq (z c : ℂ) (hz : 0 < z.re) (hc : 0 < c.re) :
    laplace z c = c^(-z)*Complex.Gamma z := by
  let U : Set ℂ := {w | 0 < w.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (laplace z) U :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (laplace_differentiableAt z w hz hw).differentiableWithinAt) ho
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => w^(-z)*Complex.Gamma z) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro w hw
    exact (((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) w).cpow_const
      (Complex.mem_slitPlane_iff.mpr (Or.inl hw))).mul_const _).differentiableWithinAt
  have hconv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change 0 < (a • x+b • y).re
    simp only [add_re,Complex.smul_re,smul_eq_mul]
    change 0 < x.re at hx
    change 0 < y.re at hy
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_add] at hab
      simpa [hab] using hy
    · have hax := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx
      linarith [mul_nonneg hb hy.le]
  have hreal : ∀ r : ℝ, 0 < r → laplace z (r:ℂ) = (r:ℂ)^(-z)*Complex.Gamma z := by
    intro r hr
    have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hz hr
    simpa only [laplace,kernel,Complex.ofReal_mul,one_div,
      Complex.inv_cpow_ofReal_nonneg hr.le,Complex.cpow_neg,neg_mul] using hh
  let seq : ℕ → ℂ := fun n => ((1+1/((n:ℝ)+1):ℝ):ℂ)
  have hlim : Tendsto seq atTop (𝓝 (1:ℂ)) := by
    have hh := ((tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)))
    simpa only [seq,Function.comp_def,add_zero,Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp hh
  have hcl : (1:ℂ) ∈ closure ({w | laplace z w = w^(-z)*Complex.Gamma z} \ {(1:ℂ)}) := by
    apply mem_closure_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨hreal _ (by positivity),?_⟩
    simp only [mem_singleton_iff]
    intro hh
    have hr := congrArg Complex.re hh
    dsimp [seq] at hr
    norm_num only [Complex.ofReal_re,Complex.one_re] at hr
    have hp : 0 < 1/((n:ℝ)+1) := by positivity
    linarith
  exact hf.eqOn_of_preconnected_of_mem_closure hg hconv.isPreconnected
    (show (1:ℂ) ∈ U by norm_num [U]) hcl hc

#print axioms laplace_eq
#print axioms real_majorant_integrable
#print axioms kernel_continuous
#print axioms kernel_norm
#print axioms kernel_integrable
#print axioms kernel_hasDerivAt
#print axioms derivative_norm
#print axioms laplace_differentiableAt
end XiPrime8845.PRZZGammaLaplace

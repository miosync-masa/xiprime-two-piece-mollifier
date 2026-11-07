import PRZZGammaFar

/-! The original AFE Mellin integrand, including its pole annihilator.
The far-domain estimate retains all shift dependence explicitly. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZMellinTail
open PRZZDyadicEnvelope PRZZGammaFar
set_option maxHeartbeats 2000000

def factor (sigma : ℂ) (x v : ℝ) : ℂ :=
  (x:ℂ)^(-(2+(v:ℂ)*I))*annihilator sigma (2+(v:ℂ)*I)/(2+(v:ℂ)*I)

def integrand (a b : ℂ) (x t v : ℝ) : ℂ :=
  factor (a+b) x v * (exp ((2+(v:ℂ)*I)^2)*PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t)

theorem kernel_eq (a b : ℂ) (x t : ℝ) :
    PRZZAFEGamma.kernel a b x t = (1/(2*Real.pi):ℂ)*∫ v, integrand a b x t v := by
  unfold PRZZAFEGamma.kernel integrand factor
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by ring)

theorem factor_bound (sigma : ℂ) (hs : sigma ≠ 0) (x v : ℝ) (hx : 0 < x) :
    ‖factor sigma x v‖ ≤ x^(-2:ℝ)*(1+16/‖sigma‖^2)*(1+v^2) := by
  let s : ℂ := 2+(v:ℂ)*I
  have hs2 : ‖s‖^2 = 4+v^2 := by simp [s,Complex.sq_norm,Complex.normSq_apply]; ring
  have hs1 : 1 ≤ ‖s‖ := by have := norm_nonneg s; nlinarith [sq_nonneg v]
  have hn : 0 < ‖sigma‖ := norm_pos_iff.mpr hs
  have ha' : ‖annihilator sigma s‖ ≤ 1+4*(4+v^2)/‖sigma‖^2 := by
    -- Choose L=1, r=norm sigma so the inverse-square dependence is explicit.
    have h := annihilator_bound sigma s 1 ‖sigma‖ (by norm_num) hn (by simp)
    simpa only [hs2,one_div,div_eq_mul_inv,one_mul,inv_pow] using h
  have hp : 1+4*(4+v^2)/‖sigma‖^2 ≤ (1+16/‖sigma‖^2)*(1+v^2) := by
    apply sub_nonneg.mp
    have hh : 0 ≤ v^2+12*v^2/‖sigma‖^2 := by positivity
    convert hh using 1
    ring
  have hpow : ‖(x:ℂ)^(-s)‖ = x^(-2:ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  change ‖(x:ℂ)^(-s)*annihilator sigma s/s‖ ≤ _
  rw [norm_div,norm_mul,hpow]
  calc
    _ ≤ x^(-2:ℝ)*‖annihilator sigma s‖ := div_le_self (by positivity) hs1
    _ ≤ x^(-2:ℝ)*((1+16/‖sigma‖^2)*(1+v^2)) := by gcongr; exact ha'.trans hp
    _ = _ := by ring

theorem far_integrand_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t x v : ℝ, 256*Real.pi ≤ T → |t| ≤ 2*T →
      0 < x → T/4 ≤ |v| →
      ‖integrand a b x t v‖ ≤
        C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)*
          ((1+v^2)*Real.exp (-v^2/2)) := by
  obtain ⟨C,hC,h⟩ := far_core_bound a b ha ha' hb hb'
  refine ⟨C,hC,?_⟩
  intro T t x v hT ht hx hv
  rw [integrand,norm_mul]
  exact (mul_le_mul (factor_bound (a+b) hs x v hx) (h T t v hT ht hv)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

def majorant (v : ℝ) : ℝ := (1+v^2)*Real.exp (-v^2/2)

theorem majorant_integrable : Integrable majorant := by
  have h0 := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 2)
  have he : majorant = (fun v : ℝ => Real.exp (-(1/2:ℝ)*v^2)) +
      (fun v : ℝ => v^(2:ℝ)*Real.exp (-(1/2:ℝ)*v^2)) := by
    funext v
    simp only [majorant,Pi.add_apply,Real.rpow_two]
    rw [show -v^2/2 = -(1/2:ℝ)*v^2 by ring]
    ring
  rw [he]
  exact h0.add h2

/-- The far tail of the literal AFE kernel has an exponentially small
integral bound, with constants before T,t,x. -/
theorem far_integral_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t x : ℝ, 256*Real.pi ≤ T → |t| ≤ 2*T → 0 < x →
      ‖∫ v in {v : ℝ | T/4 ≤ |v|}, integrand a b x t v‖ ≤
        C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64) := by
  obtain ⟨C,hC,h⟩ := far_integrand_bound a b ha ha' hb hb' hs
  let J := ∫ v, majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by dsimp [majorant]; positivity)
  refine ⟨C*(J+1),by positivity,?_⟩
  intro T t x hT ht hx
  let S := {v : ℝ | T/4 ≤ |v|}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  let B := C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := majorant_integrable.const_mul B
  have he : ‖∫ v in S, integrand a b x t v‖ ≤ ∫ v in S, B*majorant v := by
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem hS] with v hv
    exact h T t x v hT ht hx hv
  apply he.trans
  have hi := setIntegral_le_integral (s := S) hg
    (Filter.Eventually.of_forall (fun v => mul_nonneg hB (by dsimp [majorant]; positivity)))
  apply hi.trans
  rw [integral_const_mul]
  dsimp [B,J]
  nlinarith [mul_nonneg hB (show (0:ℝ) ≤ 1 by norm_num)]

theorem integrand_continuous (a b : ℂ) (x t : ℝ) (hx : 0 < x)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    Continuous (integrand a b x t) := by
  have hg (c : ℂ) (y : ℝ) (hc : -(1/2:ℝ) < c.re) :
      Continuous (fun v : ℝ => Gamma ((1/2+c+(2+(v:ℂ)*I)+(y:ℂ)*I)/2)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (PRZZGammaPath.gamma_analytic _ (by simp; linarith)).continuousAt.comp
      (x := v)
    fun_prop
  have hga := hg a t ha
  have hgb := hg b (-t) hb
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hs : ∀ v : ℝ, (2+(v:ℂ)*I) ≠ 0 := by
    intro v he
    have hh := congrArg Complex.re he
    norm_num at hh
  have hr : Continuous (fun v : ℝ => PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t) := by
    unfold PRZZAFEGamma.gammaRatio
    simp only [ofReal_neg,neg_mul,← sub_eq_add_neg] at hgb
    apply Continuous.div_const
    apply Continuous.mul
    · simp_rw [Complex.cpow_def_of_ne_zero hpi]
      fun_prop
    · exact hga.mul hgb
  unfold integrand factor
  apply Continuous.mul _ (by fun_prop)
  apply Continuous.div _ (by fun_prop) hs
  simp_rw [Complex.cpow_def_of_ne_zero hx']
  unfold annihilator
  fun_prop

/-- Absolute integrability of the actual, untruncated Gamma-ratio kernel.
This supplies the side condition needed for integral subtraction. -/
theorem integrand_integrable (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x t : ℝ) (hx : 0 < x) : Integrable (integrand a b x t) := by
  obtain ⟨C,hC,h⟩ := actual_ratio_bound a b ha ha' hb hb'
  let B := x^(-2:ℝ)*(1+16/‖a+b‖^2)*C*Real.exp (4+2*Real.pi*|t|)
  apply (majorant_integrable.const_mul B).mono'
    (integrand_continuous a b x t hx ha hb).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  have hg : ‖exp ((2+(v:ℂ)*I)^2)*PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t‖ ≤
      C*Real.exp (4+2*Real.pi*|t|)*Real.exp (-v^2/2) := by
    rw [norm_mul,gaussian_norm]
    calc
      _ ≤ Real.exp (4-v^2)*(C*Real.exp (2*Real.pi*|t|)) := by gcongr; exact h t v
      _ = C*Real.exp (4-v^2+2*Real.pi*|t|) := by rw [Real.exp_add]; ring
      _ ≤ C*Real.exp (4+2*Real.pi*|t|+(-v^2/2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])) hC.le
      _ = _ := by rw [Real.exp_add]; ring
  rw [integrand,norm_mul]
  exact (mul_le_mul (factor_bound (a+b) hs x v hx) hg (norm_nonneg _) (by positivity)).trans_eq
    (by dsimp [B,majorant]; ring)

#print axioms integrand_continuous
#print axioms integrand_integrable
#print axioms majorant_integrable
#print axioms far_integral_bound
#print axioms kernel_eq
#print axioms factor_bound
#print axioms far_integrand_bound
end XiPrime8845.PRZZMellinTail

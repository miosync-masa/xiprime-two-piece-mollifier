import PRZZMellinTail

/-! Exact subtraction of the actual Gamma-ratio kernel and the rescaled
source weight. Integrability is proved before subtracting the integrals.
This identity does not assert a central-region asymptotic estimate. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZKernelDifference
open PRZZMellinTail PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def mainIntegrand (sigma : ℂ) (x q v : ℝ) : ℂ :=
  factor sigma x v * (exp ((2+(v:ℂ)*I)^2)*(q:ℂ)^(2+(v:ℂ)*I))

theorem main_eq_rescaled (sigma : ℂ) (x q v : ℝ) (hx : 0 < x) (hq : 0 < q) :
    mainIntegrand sigma x q v =
      ((x/q:ℝ):ℂ)^(-(2+(v:ℂ)*I))*exp ((2+(v:ℂ)*I)^2)*
        annihilator sigma (2+(v:ℂ)*I)/(2+(v:ℂ)*I) := by
  rw [ofReal_div,Complex.div_cpow_ofReal_nonneg hx.le hq.le,Complex.cpow_neg,
    Complex.cpow_neg]
  unfold mainIntegrand factor
  rw [Complex.cpow_neg]
  simp only [div_eq_mul_inv,inv_inv]
  ring

theorem main_integrable (sigma : ℂ) (hs : sigma ≠ 0) (x q : ℝ)
    (hx : 0 < x) (hq : 0 < q) : Integrable (mainIntegrand sigma x q) := by
  have he : mainIntegrand sigma x q = fun v : ℝ =>
      ((x/q:ℝ):ℂ)^(-(2+(v:ℂ)*I))*exp ((2+(v:ℂ)*I)^2)*
        annihilator sigma (2+(v:ℂ)*I)/(2+(v:ℂ)*I) :=
    funext (fun v => main_eq_rescaled sigma x q v hx hq)
  rw [he]
  exact PRZZSourceW.source_integrable sigma hs (x/q) (div_pos hx hq)

theorem sourceW_rescaled (sigma : ℂ) (x q : ℝ) (hx : 0 < x) (hq : 0 < q) :
    sourceW sigma (x/q) = (1/(2*Real.pi):ℂ)*∫ v, mainIntegrand sigma x q v := by
  unfold sourceW
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => (main_eq_rescaled sigma x q v hx hq).symm)

def errorIntegrand (a b : ℂ) (x t q v : ℝ) : ℂ :=
  factor (a+b) x v * exp ((2+(v:ℂ)*I)^2) *
    (PRZZAFEGamma.gammaRatio a b (2+(v:ℂ)*I) t-(q:ℂ)^(2+(v:ℂ)*I))

theorem error_eq (a b : ℂ) (x t q v : ℝ) :
    errorIntegrand a b x t q v = integrand a b x t v-mainIntegrand (a+b) x q v := by
  unfold errorIntegrand integrand mainIntegrand
  ring

theorem error_integrable (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x t q : ℝ) (hx : 0 < x) (hq : 0 < q) : Integrable (errorIntegrand a b x t q) := by
  have he : errorIntegrand a b x t q = integrand a b x t-mainIntegrand (a+b) x q :=
    funext (error_eq a b x t q)
  rw [he]
  exact (integrand_integrable a b ha ha' hb hb' hs x t hx).sub
    (main_integrable (a+b) hs x q hx hq)

/-- Literal V-W identity with the scale q=t/(2*pi). No assumed Fubini,
summability, or kernel-error premise is used. -/
theorem difference_eq (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi))) =
      (1/(2*Real.pi):ℂ)*∫ v, errorIntegrand a b x t (t/(2*Real.pi)) v := by
  have hq : 0 < t/(2*Real.pi) := by positivity
  rw [kernel_eq,sourceW_rescaled (a+b) x _ hx hq,← mul_sub]
  rw [← integral_sub (integrand_integrable a b ha ha' hb hb' hs x t hx)
    (main_integrable (a+b) hs x _ hx hq)]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun v => (error_eq a b x t _ v).symm))

theorem difference_norm_le (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0)
    (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤
      (1/(2*Real.pi))*∫ v, ‖errorIntegrand a b x t (t/(2*Real.pi)) v‖ := by
  rw [difference_eq a b ha ha' hb hb' hs x t hx ht,norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = (1/(2*Real.pi):ℝ) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

/-- The W main term has a Gaussian far tail as well. -/
theorem far_main_bound (sigma : ℂ) (hs : sigma ≠ 0) (T x q v : ℝ)
    (hT : 0 ≤ T) (hx : 0 < x) (hq : 0 < q) (hv : T/4 ≤ |v|) :
    ‖mainIntegrand sigma x q v‖ ≤
      Real.exp 4*q^2*x^(-2:ℝ)*(1+16/‖sigma‖^2)*Real.exp (-T^2/64)*majorant v := by
  have hv2 : T^2/16 ≤ v^2 := by nlinarith [sq_abs v]
  have he : Real.exp (4-v^2) ≤ Real.exp 4*Real.exp (-T^2/64)*Real.exp (-v^2/2) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg T]
  have hp : ‖(q:ℂ)^(2+(v:ℂ)*I)‖ = q^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
    simp
  rw [mainIntegrand,norm_mul,norm_mul,PRZZGammaFar.gaussian_norm,hp]
  exact (mul_le_mul (factor_bound sigma hs x v hx)
    (mul_le_mul_of_nonneg_right he (sq_nonneg q)) (by positivity) (by positivity)).trans_eq
      (by dsimp [majorant]; ring)

/-- Exponentially small absolute tail of V-W itself. The central error is
not a premise, and is not silently declared small by this theorem. -/
theorem far_error_integral_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t x q : ℝ, 256*Real.pi ≤ T → |t| ≤ 2*T → 0 < x → 0 < q →
      (∫ v in {v : ℝ | T/4 ≤ |v|}, ‖errorIntegrand a b x t q v‖) ≤
        C*(1+q^2)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64) := by
  obtain ⟨C,hC,h⟩ := far_integrand_bound a b ha ha' hb hb' hs
  let J := ∫ v, majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by dsimp [majorant]; positivity)
  refine ⟨(C+Real.exp 4)*(J+1),by positivity,?_⟩
  intro T t x q hT ht hx hq
  let S := {v : ℝ | T/4 ≤ |v|}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  let B := (C+Real.exp 4)*(1+q^2)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := majorant_integrable.const_mul B
  have hp : ∀ v ∈ S, ‖errorIntegrand a b x t q v‖ ≤ B*majorant v := by
    intro v hv
    rw [error_eq]
    apply (norm_sub_le _ _).trans
    have h1 := h T t x v hT ht hx hv
    have h2 := far_main_bound (a+b) hs T x q v
      (by have := Real.pi_pos; linarith) hx hq hv
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

theorem difference_split_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ T t x : ℝ, 256*Real.pi ≤ T → 0 < t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤
        (1/(2*Real.pi))*((∫ v in {v : ℝ | |v| < T/4},
          ‖errorIntegrand a b x t (t/(2*Real.pi)) v‖)+
          C*(1+(t/(2*Real.pi))^2)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*Real.exp (-T^2/64)) := by
  obtain ⟨C,hC,h⟩ := far_error_integral_bound a b ha ha' hb hb' hs
  refine ⟨C,hC,?_⟩
  intro T t x hT ht ht2 hx
  have hq : 0 < t/(2*Real.pi) := by positivity
  have hsplit := integral_add_compl (s := {v : ℝ | |v| < T/4})
    (isOpen_lt continuous_abs continuous_const).measurableSet
    (error_integrable a b ha ha' hb hb' hs x t (t/(2*Real.pi)) hx hq).norm
  have hbnd := h T t x (t/(2*Real.pi)) hT (by simpa [abs_of_pos ht] using ht2) hx hq
  have hn := difference_norm_le a b ha ha' hb hb' hs x t hx ht
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← hsplit]
  apply add_le_add_right _ _
  simpa only [Set.compl_ofPred,not_lt] using hbnd

#print axioms far_main_bound
#print axioms far_error_integral_bound
#print axioms difference_split_bound
#print axioms difference_norm_le
#print axioms main_eq_rescaled
#print axioms main_integrable
#print axioms sourceW_rescaled
#print axioms error_eq
#print axioms error_integrable
#print axioms difference_eq
end XiPrime8845.PRZZKernelDifference

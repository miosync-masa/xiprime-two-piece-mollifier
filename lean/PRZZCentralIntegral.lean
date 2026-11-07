import PRZZGammaMain

/-! The central exponential error is absorbed by the Mellin Gaussian.
The bound is uniform over both small shifts; the singular sum is explicit. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZCentralIntegral
set_option maxHeartbeats 3000000

theorem exponent_budget (T v : ℝ) (hT : 128 ≤ T) :
    2*‖(2:ℂ)+(v:ℂ)*I‖*(26+‖(2:ℂ)+(v:ℂ)*I‖)/T ≤ 174*(1+v^2)/T ∧
    2*‖(2:ℂ)+(v:ℂ)*I‖*(26+‖(2:ℂ)+(v:ℂ)*I‖)/T ≤ 2+v^2/2 := by
  let n := ‖(2:ℂ)+(v:ℂ)*I‖
  have hn : n ≤ 2+|v| := by
    simpa [n,norm_mul] using norm_add_le (2:ℂ) ((v:ℂ)*I)
  have hn0 : 0 ≤ n := norm_nonneg _
  have hv : 0 ≤ |v| := abs_nonneg v
  have hsq : |v|^2 = v^2 := sq_abs v
  have h1 : 2*n*(26+n) ≤ 142+32*v^2 := by
    nlinarith [sq_nonneg (|v|-1)]
  constructor
  · apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
    change 2*n*(26+n) ≤ _
    nlinarith [sq_nonneg v]
  · apply (div_le_iff₀ (by linarith : 0 < T)).mpr
    change 2*n*(26+n) ≤ _
    nlinarith [sq_nonneg v,mul_nonneg (show 0 ≤ T-128 by linarith) (sq_nonneg v)]

theorem central_integrand_bound (T t x v : ℝ) (a b : ℂ) (hT : 128 ≤ T)
    (ht : T ≤ t) (hx : 0 < x) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (hv : |v| ≤ T/4) :
    ‖PRZZKernelDifference.errorIntegrand a b x t (t/(2*Real.pi)) v‖ ≤
      (174*Real.exp 6)*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(t/(2*Real.pi))^2/T *
        ((1+v^2)^2*Real.exp (-v^2/2)) := by
  let q := t/(2*Real.pi)
  let s : ℂ := 2+(v:ℂ)*I
  let D := 2*‖s‖*(26+‖s‖)/T
  have ht0 : 0 < t := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound := PRZZGammaMain.ratio_relative_bound T t a b s (by linarith) ht ha hb
    (by simpa [s] using hv) (by simp [s])
  have hnorm : ‖(q:ℂ)^s‖ = q^2 := by
    rw [norm_cpow_eq_rpow_re_of_pos hq]
    simp [s]
  change ‖PRZZAFEGamma.gammaRatio a b s t-(q:ℂ)^s‖ ≤ ‖(q:ℂ)^s‖*D*Real.exp D at hbound
  rw [hnorm] at hbound
  have hbud := exponent_budget T v hT
  have hex : Real.exp (4-v^2)*Real.exp D ≤ Real.exp 6*Real.exp (-v^2/2) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hbud.2
    change D ≤ 2+v^2/2 at this
    linarith
  have hf := PRZZMellinTail.factor_bound (a+b) hs x v hx
  rw [PRZZKernelDifference.errorIntegrand,norm_mul,norm_mul,PRZZGammaFar.gaussian_norm]
  calc
    _ ≤ (x^(-2:ℝ)*(1+16/‖a+b‖^2)*(1+v^2))*Real.exp (4-v^2)*
        (q^2*D*Real.exp D) := by gcongr
    _ = (x^(-2:ℝ)*(1+16/‖a+b‖^2)*(1+v^2))*q^2*D*
        (Real.exp (4-v^2)*Real.exp D) := by ring
    _ ≤ (x^(-2:ℝ)*(1+16/‖a+b‖^2)*(1+v^2))*q^2*(174*(1+v^2)/T)*
        (Real.exp 6*Real.exp (-v^2/2)) := by gcongr; exact hbud.1
    _ = _ := by dsimp [q]; ring

#print axioms exponent_budget
#print axioms central_integrand_bound

def majorant (v : ℝ) : ℝ := (1+v^2)^2*Real.exp (-v^2/2)

theorem majorant_integrable : Integrable majorant := by
  have h0 := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 2)
  have h4 := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 4)
  have he : majorant = (fun v : ℝ => Real.exp (-(1/2:ℝ)*v^2)) +
      (fun v : ℝ => 2*(v^(2:ℝ)*Real.exp (-(1/2:ℝ)*v^2))) +
      (fun v : ℝ => v^(4:ℝ)*Real.exp (-(1/2:ℝ)*v^2)) := by
    funext v
    norm_num [majorant,Pi.add_apply,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
    rw [show -v^2/2 = -(1/2:ℝ)*v^2 by ring]
    ring
  rw [he]
  exact (h0.add (h2.const_mul 2)).add h4

theorem central_integral_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x : ℝ,
    128 ≤ T → T ≤ t → 0 < x →
      (∫ v in {v : ℝ | |v| < T/4},
        ‖PRZZKernelDifference.errorIntegrand a b x t (t/(2*Real.pi)) v‖) ≤
        C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(t/(2*Real.pi))^2/T := by
  let J := ∫ v, majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by dsimp [majorant]; positivity)
  refine ⟨174*Real.exp 6*(J+1),by positivity,?_⟩
  intro a b ha hb hs T t x hT ht hx
  have ht0 : 0 < t := by linarith
  let B := 174*Real.exp 6*x^(-2:ℝ)*(1+16/‖a+b‖^2)*(t/(2*Real.pi))^2/T
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  have hi := (PRZZKernelDifference.error_integrable a b
    (by linarith [har.1]) (by linarith [har.2])
    (by linarith [hbr.1]) (by linarith [hbr.2]) hs x t (t/(2*Real.pi)) hx (by positivity)).norm
  let S := {v : ℝ | |v| < T/4}
  have hS : MeasurableSet S := isOpen_lt continuous_abs continuous_const |>.measurableSet
  have hmajor := majorant_integrable.const_mul B
  have hh : (∫ v in S, ‖PRZZKernelDifference.errorIntegrand a b x t (t/(2*Real.pi)) v‖) ≤
      ∫ v in S, B*majorant v := by
    apply integral_mono_ae hi.integrableOn hmajor.integrableOn
    filter_upwards [ae_restrict_mem hS] with v hv
    exact central_integrand_bound T t x v a b hT ht hx ha hb hs hv.le
  apply hh.trans
  apply (setIntegral_le_integral hmajor (Filter.Eventually.of_forall
    (fun v => mul_nonneg hB (by dsimp [majorant]; positivity)))).trans
  rw [integral_const_mul]
  change B*J ≤ _
  have hh := mul_le_mul_of_nonneg_left (show J ≤ J+1 by linarith) hB
  exact hh.trans_eq (by dsimp only [B]; ring)

#print axioms majorant_integrable
#print axioms central_integral_bound
end XiPrime8845.PRZZCentralIntegral

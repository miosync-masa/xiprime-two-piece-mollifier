import PRZZCosineTimeMellin
import PRZZZeroCosine

/-! Exact reciprocal substitution for the actual zero-frequency spatial
weight on positive finite intervals. The reversed orientation and the
Jacobian are explicit; no conditional Fubini assertion is used. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroReciprocal
open PRZZCosineSpatialJets PRZZDyadicEnvelope
set_option maxHeartbeats 6000000

def weight (sigma : ℂ) (k omega x : ℝ) : ℂ :=
  exp (-(sigma+1)*(Real.log x:ℂ))*sourceW sigma (k*x^2)*cos ((omega/x:ℝ):ℂ)

theorem reciprocal_deriv (omega x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => omega/y) (-omega/x^2) x := by
  have h := (hasDerivAt_const x omega).div (hasDerivAt_id x) hx.ne'
  convert h using 1 <;> first | rfl | skip
  simp only [Pi.div_apply,id_eq,mul_one,zero_mul,zero_sub]

theorem power_jacobian (sigma : ℂ) (omega x : ℝ) (ho : 0 < omega) (hx : 0 < x) :
    exp (-(sigma+1)*(Real.log x:ℂ)) =
      exp (-sigma*(Real.log omega:ℂ))*power (sigma-1) (omega/x)*(omega/x^2:ℝ) := by
  have he : exp (-sigma*(Real.log omega:ℂ))*power (sigma-1) (omega/x) =
      exp (-(sigma+1)*(Real.log x:ℂ))*((x:ℂ)^2/(omega:ℂ)) := by
    have hl : exp ((Real.log x:ℂ)+(Real.log x:ℂ)-(Real.log omega:ℂ)) = (x:ℂ)^2/(omega:ℂ) := by
      rw [exp_sub,exp_add,← Complex.ofReal_exp,← Complex.ofReal_exp,
        Real.exp_log hx,Real.exp_log ho]
      ring
    rw [power,Real.log_div ho.ne' hx.ne',Complex.ofReal_sub,← exp_add,← hl,← exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  field_simp [show (omega:ℂ) ≠ 0 by exact_mod_cast ho.ne',
    show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne']

theorem weight_jacobian (sigma : ℂ) (k omega x : ℝ) (ho : 0 < omega) (hx : 0 < x) :
    weight sigma k omega x =
      -exp (-sigma*(Real.log omega:ℂ))*
        ((-omega/x^2) • (primitive (sigma-1) sigma (k*omega^2) (omega/x)*cos ((omega/x:ℝ):ℂ))) := by
  have harg : PRZZCosineSpatialJets.arg (k*omega^2) (omega/x) = k*x^2 := by
    unfold PRZZCosineSpatialJets.arg
    field_simp
  rw [weight,power_jacobian sigma omega x ho hx,primitive,harg]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow]
  ring

theorem finite_substitution (sigma : ℂ) (hs : sigma ≠ 0) (k omega a b : ℝ)
    (hk : 0 < k) (ho : 0 < omega) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, weight sigma k omega x) = exp (-sigma*(Real.log omega:ℂ))*
      ∫ y in (omega/b)..(omega/a), primitive (sigma-1) sigma (k*omega^2) y*cos (y:ℂ) := by
  have hx (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x : ℝ => omega/x) (-omega/x^2) x :=
    fun x h => reciprocal_deriv omega x (hx x h)
  have hc : ContinuousOn (fun x : ℝ => -omega/x^2) (uIcc a b) := by
    intro x h
    have hn : x ≠ 0 := (hx x h).ne'
    fun_prop (disch := exact pow_ne_zero 2 hn)
  have hg : ContinuousOn (fun y : ℝ => primitive (sigma-1) sigma (k*omega^2) y*cos (y:ℂ))
      ((fun x : ℝ => omega/x) '' uIcc a b) := by
    intro y hy
    obtain ⟨x,hx',rfl⟩ := hy
    exact ((primitive_deriv (sigma-1) sigma hs (k*omega^2) (omega/x) (by positivity)
      (div_pos ho (hx x hx'))).continuousAt.mul
      (Complex.hasDerivAt_cos ((omega/x:ℝ):ℂ)).comp_ofReal.continuousAt).continuousWithinAt
  have hh := intervalIntegral.integral_deriv_smul_comp' hd hc hg
  simp only [Function.comp_apply] at hh
  have he : (∫ x in a..b, weight sigma k omega x) = -exp (-sigma*(Real.log omega:ℂ))*
      ∫ x in a..b, (-omega/x^2) •
        (primitive (sigma-1) sigma (k*omega^2) (omega/x)*cos ((omega/x:ℝ):ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x h
    exact weight_jacobian sigma k omega x ho (hx x h)
  rw [he,hh,intervalIntegral.integral_symm (omega/a) (omega/b)]
  ring

#print axioms reciprocal_deriv
#print axioms power_jacobian
#print axioms weight_jacobian
#print axioms finite_substitution
end XiPrime8845.PRZZZeroReciprocal

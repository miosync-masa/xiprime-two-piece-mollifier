import PRZZDifferenceContour
import PRZZCentralIntegral

/-! Height-uniform central comparison on the shifted line Re(s)=-1/8.
The positive power of x and negative power of q are retained explicitly. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZLeftCentral
open PRZZDifferenceRegular PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

def line (v : ℝ) : ℂ := -1/8+(v:ℂ)*I

theorem line_re (v : ℝ) : (line v).re = -(1/8:ℝ) := by norm_num [line]
theorem line_im (v : ℝ) : (line v).im = v := by simp [line]

theorem exponent_budget (T v : ℝ) (hT : 128 ≤ T) :
    2*‖line v‖*(26+‖line v‖)/T ≤ 174*(1+v^2)/T ∧
    2*‖line v‖*(26+‖line v‖)/T ≤ 2+v^2/2 := by
  let n := ‖line v‖
  have hn : n ≤ 2+|v| := by
    have hh := norm_le_abs_re_add_abs_im (line v)
    rw [line_re,line_im] at hh
    norm_num at hh
    dsimp [n]; linarith
  have hn0 : 0 ≤ n := norm_nonneg _
  have hv : 0 ≤ |v| := abs_nonneg v
  have hsq : |v|^2 = v^2 := sq_abs v
  have h1 : 2*n*(26+n) ≤ 142+32*v^2 := by nlinarith [sq_nonneg (|v|-1)]
  constructor
  · apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
    change 2*n*(26+n) ≤ _
    nlinarith [sq_nonneg v]
  · apply (div_le_iff₀ (by linarith : 0 < T)).mpr
    change 2*n*(26+n) ≤ _
    nlinarith [sq_nonneg v,mul_nonneg (show 0 ≤ T-128 by linarith) (sq_nonneg v)]

theorem line_ne_zero (v : ℝ) : line v ≠ 0 := by
  intro hh
  have he := congrArg Complex.re hh
  rw [line_re] at he
  norm_num at he

theorem inverse_bound (v : ℝ) : ‖(line v)⁻¹‖ ≤ 8 := by
  have hh := abs_re_le_norm (line v)
  rw [line_re] at hh
  norm_num at hh
  rw [norm_inv]
  have hi := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) < 1/8) hh
  simpa only [one_div,inv_div,div_one,inv_inv] using hi

theorem annihilator_line (sigma : ℂ) (hs : sigma ≠ 0) (v : ℝ) :
    ‖annihilator sigma (line v)‖ ≤ (1+32/‖sigma‖^2)*(1+v^2) := by
  have hh := norm_le_abs_re_add_abs_im (line v)
  rw [line_re,line_im] at hh
  norm_num at hh
  have hsn : ‖line v‖^2 ≤ 8*(1+v^2) := by
    nlinarith [sq_abs v,sq_nonneg (|v|-1),norm_nonneg (line v),abs_nonneg v]
  have han := annihilator_bound sigma (line v) 1 ‖sigma‖ (by norm_num)
    (norm_pos_iff.mpr hs) (by simp)
  apply han.trans
  rw [div_pow,one_pow]
  simp only [mul_one_div]
  calc
    _ ≤ 1+4*(8*(1+v^2))/‖sigma‖^2 := by gcongr
    _ = 1+(32/‖sigma‖^2)*(1+v^2) := by ring
    _ ≤ (1+v^2)+(32/‖sigma‖^2)*(1+v^2) := by gcongr; nlinarith [sq_nonneg v]
    _ = _ := by ring

theorem gaussian_line (v : ℝ) : ‖exp ((line v)^2)‖ ≤ Real.exp (4-v^2) := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [pow_two,mul_re,line_re,line_im]
  nlinarith

theorem central_bound (T t x v : ℝ) (a b : ℂ) (hT : 128 ≤ T)
    (ht : T ≤ t) (hx : 0 < x) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (hv : |v| ≤ T/4) :
    ‖regular a b x t (t/(2*Real.pi)) (line v)‖ ≤
      (1392*Real.exp 6)*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*(t/(2*Real.pi))^(-1/8:ℝ)/T *
        PRZZCentralIntegral.majorant v := by
  let q := t/(2*Real.pi)
  let D := 2*‖line v‖*(26+‖line v‖)/T
  have ht0 : 0 < t := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound := PRZZGammaMain.ratio_relative_bound_strip T t a b (line v)
    (by linarith) ht ha hb (by simpa [line_im] using hv) (by rw [line_re])
  have hnorm : ‖(q:ℂ)^(line v)‖ = q^(-1/8:ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hq,line_re]
    norm_num
  change ‖PRZZAFEGamma.gammaRatio a b (line v) t-(q:ℂ)^(line v)‖ ≤
    ‖(q:ℂ)^(line v)‖*D*Real.exp D at hbound
  rw [hnorm] at hbound
  have hbud := exponent_budget T v hT
  have hex : Real.exp (4-v^2)*Real.exp D ≤ Real.exp 6*Real.exp (-v^2/2) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hbud.2
    change D ≤ 2+v^2/2 at this
    linarith
  have hp : ‖(x:ℂ)^(-(line v))‖ = x^(1/8:ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx,neg_re,line_re]
    norm_num
  have ar := (abs_le.mp ((abs_re_le_norm a).trans ha)).1
  have br := (abs_le.mp ((abs_re_le_norm b).trans hb)).1
  rw [regular_eq a b _ x t _ (by linarith) (by linarith) (line_ne_zero v),
    div_eq_mul_inv]
  simp only [norm_mul,hp,numerator]
  calc
    _ ≤ x^(1/8:ℝ)*Real.exp (4-v^2)*((1+32/‖a+b‖^2)*(1+v^2))*8*
        (q^(-1/8:ℝ)*D*Real.exp D) := by
      gcongr
      · exact gaussian_line v
      · exact annihilator_line (a+b) hs v
      · exact inverse_bound v
    _ = (8*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*(1+v^2))*q^(-1/8:ℝ)*D*
        (Real.exp (4-v^2)*Real.exp D) := by ring
    _ ≤ (8*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*(1+v^2))*q^(-1/8:ℝ)*(174*(1+v^2)/T)*
        (Real.exp 6*Real.exp (-v^2/2)) := by gcongr; exact hbud.1
    _ = _ := by dsimp [q,PRZZCentralIntegral.majorant]; ring

#print axioms exponent_budget
#print axioms line_ne_zero
#print axioms inverse_bound
#print axioms annihilator_line
#print axioms gaussian_line
#print axioms central_bound
end XiPrime8845.PRZZLeftCentral

import PRZZSourceW

/-! Quantitative decay of the actual Gaussian tail in sourceW.
The constants are explicit. This does not estimate the gamma-ratio AFE
kernel or assert that its differentiated tails have already been summed. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZSourceDecay
open PRZZSourceW

theorem gaussian_linear_bound (a u : ℝ) :
    Real.exp (-u^2/4) ≤ Real.exp (a^2)*Real.exp (-a*u) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (u-2*a)]

/-- Any positive exponential rate is available in logarithmic coordinates. -/
theorem tail_exp_bound (a l : ℝ) (ha : 0 < a) :
    tail l ≤ Real.exp (a^2)*(-Real.exp (-a*l)/(-a)) := by
  have hi : Integrable (fun u : ℝ => Real.exp (-u^2/4)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4) using 1
    funext u; congr 1; ring
  have hj := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) l).const_mul (Real.exp (a^2))
  unfold tail
  calc
    _ ≤ ∫ u in Ioi l, Real.exp (a^2)*Real.exp (-a*u) := by
      apply setIntegral_mono_on hi.integrableOn hj measurableSet_Ioi
      intro u _; exact gaussian_linear_bound a u
    _ = _ := by rw [integral_const_mul,integral_exp_mul_Ioi (neg_neg_of_pos ha)]

/-- The polynomial correction has the same arbitrary exponential rate. -/
theorem correction_exp_bound (a l : ℝ) :
    |l*Real.exp (-l^2/4)| ≤
      (2+2*|a|)*Real.exp (a^2)*Real.exp (-a*l) := by
  have h := correction_bound (l-2*a)
  rw [abs_mul,abs_of_pos (Real.exp_pos _)] at h ⊢
  have he : Real.exp (-(l-2*a)^2/4) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (l-2*a)]
  have hl : |l| ≤ |l-2*a|+2*|a| := by
    have hh := abs_add_le (l-2*a) (2*a)
    simpa [abs_mul] using hh
  have hb : |l| * Real.exp (-(l-2*a)^2/4) ≤ 2+2*|a| := by
    nlinarith [mul_le_mul_of_nonneg_right hl (Real.exp_pos (-(l-2*a)^2/4)).le,
      mul_le_mul_of_nonneg_left he (show 0 ≤ 2*|a| by positivity)]
  have hm := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ Real.exp (a^2)*Real.exp (-a*l) by positivity)
  calc
    _ = |l| * Real.exp (-(l-2*a)^2/4) * (Real.exp (a^2)*Real.exp (-a*l)) := by
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ _ := hm.trans_eq (by ring)

/-- Arbitrary power decay of the literal contour weight, with its
shift-separation cost explicit rather than hidden in a height constant. -/
theorem sourceW_decay (sigma : ℂ) (hs : sigma ≠ 0) (a x : ℝ)
    (ha : 0 < a) (hx : 0 < x) :
    ‖PRZZDyadicEnvelope.sourceW sigma x‖ ≤
      (Real.exp (a^2)/(2*Real.sqrt Real.pi*a)+
        (2+2*|a|)*Real.exp (a^2)/(Real.sqrt Real.pi*‖sigma‖^2))*x^(-a) := by
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have ht := tail_exp_bound a (Real.log x) ha
  have hc := correction_exp_bound a (Real.log x)
  have he : Real.exp (-a*Real.log x) = x^(-a) := by
    rw [Real.rpow_def_of_pos hx]; congr 1; ring
  simp only [neg_div_neg_eq] at ht
  rw [he] at ht hc
  rw [sourceW_eq sigma hs x hx]
  apply (norm_sub_le _ _).trans
  have ht0 := (tail_bounds (Real.log x)).1
  have h1 : ‖(tail (Real.log x):ℂ)/(2*(Real.sqrt Real.pi:ℂ))‖ ≤
      (Real.exp (a^2)*(x^(-a)/a))/(2*Real.sqrt Real.pi) := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_le_div_of_nonneg_right ht (by positivity)
  have h2 : ‖((Real.log x*Real.exp (-(Real.log x)^2/4):ℝ):ℂ)/
      ((Real.sqrt Real.pi:ℂ)*sigma^2)‖ ≤
      ((2+2*|a|)*Real.exp (a^2)*x^(-a))/(Real.sqrt Real.pi*‖sigma‖^2) := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_le_div_of_nonneg_right hc (by positivity)
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- FTC for the actual Gaussian tail, including its integrability supplier. -/
theorem tail_hasDerivAt (l : ℝ) :
    HasDerivAt tail (-Real.exp (-l^2/4)) l := by
  have hi : Integrable (fun u : ℝ => Real.exp (-u^2/4)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4) using 1
    funext u; congr 1; ring
  have hc : Continuous (fun u : ℝ => Real.exp (-u^2/4)) := by fun_prop
  have he : tail = fun x => tail 0 - ∫ u in (0:ℝ)..x, Real.exp (-u^2/4) := by
    funext x
    have hh := intervalIntegral.integral_Ioi_sub_Ioi' (a := (0:ℝ)) (b := x)
      hi.integrableOn hi.integrableOn
    dsimp [tail]
    linarith
  rw [he]
  simpa using (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 l) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_sub (tail 0)

#print axioms tail_hasDerivAt
#print axioms sourceW_decay
#print axioms gaussian_linear_bound
#print axioms tail_exp_bound
#print axioms correction_exp_bound
end XiPrime8845.PRZZSourceDecay

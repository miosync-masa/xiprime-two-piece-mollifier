import PRZZGaussianCorrection

/-! Exact evaluation of the literal source weight, away from sigma=0.
The height dependence is explicit and requires a separated shift sum. -/
noncomputable section
open MeasureTheory Complex Set
namespace XiPrime8845.PRZZSourceW
open PRZZGaussianLine PRZZGaussianTail PRZZGaussianCorrection PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def tail (l : ℝ) : ℝ := ∫ u in Ioi l, Real.exp (-u^2/4)

theorem root_eq : (Real.pi:ℂ)^(1/2:ℂ) = (Real.sqrt Real.pi:ℂ) := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; rfl,
    ← ofReal_cpow Real.pi_pos.le,← Real.sqrt_eq_rpow]

theorem tail_complex (l : ℝ) :
    (∫ u in Ioi l, exp (-(u:ℂ)^2/4)) = (tail l:ℂ) := by
  simp only [tail,← ofReal_exp,← ofReal_pow,← ofReal_neg,← ofReal_ofNat,
    ← ofReal_div,integral_complex_ofReal]

theorem integrand_eq (sigma : ℂ) (hs : sigma ≠ 0) (x t : ℝ) (hx : 0 < x) :
    (x:ℂ)^(-line t)*exp ((line t)^2)*annihilator sigma (line t)/line t =
      gaussian (Real.log x) t/line t-(4/sigma^2)*(line t*gaussian (Real.log x) t) := by
  have hw : line t ≠ 0 := by
    intro hh
    have := congrArg Complex.re hh
    simp [line] at this
  rw [power_exp x t hx]
  unfold annihilator gaussian
  field_simp
  ring

/-- Integrability of the literal contour integrand, not an assumed input. -/
theorem source_integrable (sigma : ℂ) (hs : sigma ≠ 0) (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-line t)*exp ((line t)^2)*
      annihilator sigma (line t)/line t) := by
  simp_rw [integrand_eq sigma hs x _ hx]
  exact (pole_integrable _).sub ((moment_integrable _).const_mul _)

/-- Gaussian tail and the exact shift-dependent polynomial correction. -/
theorem sourceW_eq (sigma : ℂ) (hs : sigma ≠ 0) (x : ℝ) (hx : 0 < x) :
    sourceW sigma x = (tail (Real.log x):ℂ)/(2*(Real.sqrt Real.pi:ℂ))-
      ((Real.log x*Real.exp (-(Real.log x)^2/4):ℝ):ℂ)/
        ((Real.sqrt Real.pi:ℂ)*sigma^2) := by
  have hr : (Real.sqrt Real.pi:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hr2 : (Real.sqrt Real.pi:ℂ)^2 = (Real.pi:ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  change (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
    (x:ℂ)^(-line t)*exp ((line t)^2)*annihilator sigma (line t)/line t) = _
  simp_rw [integrand_eq sigma hs x _ hx]
  rw [integral_sub (pole_integrable _) ((moment_integrable _).const_mul _),
    integral_const_mul,pole_integral,moment_integral,root_eq,tail_complex]
  have he : exp (-(Real.log x:ℂ)^2/4) = (Real.exp (-(Real.log x)^2/4):ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [he]
  push_cast
  rw [← hr2]
  field_simp
  ring

theorem tail_bounds (l : ℝ) : 0 ≤ tail l ∧ tail l ≤ 2*Real.sqrt Real.pi := by
  have hi : Integrable (fun u : ℝ => Real.exp (-u^2/4)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4) using 1
    funext u
    congr 1
    ring
  refine ⟨integral_nonneg (fun _ => (Real.exp_pos _).le),?_⟩
  have hh := setIntegral_le_integral (s := Ioi l) hi
    (Filter.Eventually.of_forall (fun u => (Real.exp_pos (-u^2/4)).le))
  have he : (∫ u : ℝ, Real.exp (-u^2/4)) = 2*Real.sqrt Real.pi := by
    calc
      _ = ∫ u : ℝ, Real.exp (-(1/4:ℝ)*u^2) := by
        congr 1
        funext u
        congr 1
        ring
      _ = Real.sqrt (Real.pi/(1/4:ℝ)) := integral_gaussian _
      _ = _ := by norm_num [Real.sqrt_div]; ring
  exact hh.trans_eq he

theorem correction_bound (l : ℝ) : |l*Real.exp (-l^2/4)| ≤ 2 := by
  have he := Real.add_one_le_exp (l^2/4)
  have hh : |l| ≤ 2*Real.exp (l^2/4) := by
    nlinarith [sq_nonneg (|l|-1),sq_abs l]
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-l^2/4)).le
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  apply hm.trans_eq
  rw [mul_assoc,← Real.exp_add]
  rw [show l^2/4 + -l^2/4 = 0 by ring,Real.exp_zero,mul_one]

/-- Uniform over every positive x; sigma=0 is deliberately excluded. -/
theorem sourceW_bound (sigma : ℂ) (hs : sigma ≠ 0) (x : ℝ) (hx : 0 < x) :
    ‖sourceW sigma x‖ ≤ 1+2/(Real.sqrt Real.pi*‖sigma‖^2) := by
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have ht := tail_bounds (Real.log x)
  rw [sourceW_eq sigma hs x hx]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_one (by positivity)).mpr ht.2
  · rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact div_le_div_of_nonneg_right (correction_bound _) (by positivity)

/-- A single bound works for every x>0 and every separated shift pair.
The only height loss is the displayed L^2, not a compactness constant. -/
theorem sourceW_scaled_bound (A B : ℂ) (L r x : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hsep : r ≤ ‖A+B‖) (hx : 0 < x) :
    ‖sourceW ((A+B)/(L:ℂ)) x‖ ≤ 1+2*L^2/(Real.sqrt Real.pi*r^2) := by
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  apply (sourceW_bound _ (div_ne_zero hab hLc) x hx).trans
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hi : ‖A+B‖⁻¹ ≤ r⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hr hsep
  have hi2 := mul_self_le_mul_self (by positivity : 0 ≤ ‖A+B‖⁻¹) hi
  have hh := mul_le_mul_of_nonneg_left hi2
    (by positivity : 0 ≤ 2*L^2/(Real.sqrt Real.pi))
  simp only [pow_two,div_eq_mul_inv,mul_inv_rev,inv_inv] at hh ⊢
  nlinarith only [hh]

#print axioms source_integrable
#print axioms sourceW_eq
#print axioms tail_bounds
#print axioms correction_bound
#print axioms sourceW_bound
#print axioms sourceW_scaled_bound
end XiPrime8845.PRZZSourceW

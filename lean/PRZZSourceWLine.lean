import PRZZSourceW

/-! The literal sourceW on any positive vertical line. Gaussian and
Laplace evaluations supply contour independence, including integrability;
no contour-shift or horizontal-edge hypothesis is assumed. -/
noncomputable section
open MeasureTheory Complex Set Filter Topology
namespace XiPrime8845.PRZZSourceWLine
open PRZZDyadicEnvelope
set_option maxHeartbeats 5000000

def line (c t : ℝ) : ℂ := (c:ℂ)+(t:ℂ)*I
def gaussian (c l t : ℝ) : ℂ := exp ((line c t)^2-(l:ℂ)*line c t)
def weight (sigma : ℂ) (x c t : ℝ) : ℂ :=
  (x:ℂ)^(-line c t)*exp ((line c t)^2)*annihilator sigma (line c t)/line c t

theorem exponent (c l t : ℝ) :
    (line c t)^2-(l:ℂ)*line c t =
      (-1:ℂ)*(t:ℂ)^2+((2*(c:ℂ)-(l:ℂ))*I)*(t:ℂ)+((c:ℂ)^2-(l:ℂ)*c) := by
  unfold line
  ring_nf
  simp only [I_sq]
  ring

theorem gaussian_integrable (c l : ℝ) : Integrable (gaussian c l) := by
  change Integrable (fun t : ℝ => exp ((line c t)^2-(l:ℂ)*line c t))
  simp_rw [exponent]
  exact integrable_cexp_quadratic' (by norm_num : (-1:ℂ).re < 0) _ _

theorem gaussian_integral (c l : ℝ) :
    (∫ t : ℝ, gaussian c l t) = (Real.pi:ℂ)^(1/2:ℂ)*exp (-(l:ℂ)^2/4) := by
  simp only [gaussian,exponent]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re < 0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [I_sq]
    ring

theorem gaussian_norm (c l t : ℝ) :
    ‖gaussian c l t‖ = Real.exp (-t^2)*Real.exp (c^2-c*l) := by
  rw [gaussian,norm_exp,exponent]
  norm_num [pow_two]
  rw [← Real.exp_add]
  congr 1
  ring

theorem laplace_integral (c l t : ℝ) (hc : 0 < c) :
    (∫ u in Ioi l, gaussian c u t) = gaussian c l t/line c t := by
  have he (u : ℝ) : gaussian c u t = exp ((line c t)^2)*exp (-line c t*(u:ℂ)) := by
    rw [← exp_add,gaussian]; congr 1; ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_complex_Ioi (by simp [line]; linarith : (-line c t).re < 0)]
  ring

theorem joint_integrable (c l : ℝ) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => gaussian c p.2 p.1)
      (volume.prod (volume.restrict (Ioi l))) := by
  have ht : Integrable (fun t : ℝ => Real.exp (-t^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have hu : Integrable (fun u : ℝ => Real.exp (c^2-c*u)) (volume.restrict (Ioi l)) := by
    have hh := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) l).const_mul (Real.exp (c^2))
    simpa only [← Real.exp_add,neg_mul,sub_eq_add_neg] using hh
  apply (ht.mul_prod hu).mono'
  · exact (by unfold gaussian line; fun_prop : Continuous (fun p : ℝ × ℝ => gaussian c p.2 p.1)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun p => (gaussian_norm c p.2 p.1).le)

theorem pole_integral (c l : ℝ) (hc : 0 < c) :
    (∫ t : ℝ, gaussian c l t/line c t) =
      (Real.pi:ℂ)^(1/2:ℂ)*(∫ u in Ioi l, exp (-(u:ℂ)^2/4)) := by
  simp_rw [← laplace_integral c l _ hc]
  rw [integral_integral_swap (joint_integrable c l hc)]
  simp only [gaussian_integral]
  rw [integral_const_mul]

theorem pole_integrable (c l : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => gaussian c l t/line c t) := by
  simpa only [laplace_integral c l _ hc] using (joint_integrable c l hc).integral_prod_left

theorem moment_integrable (c l : ℝ) : Integrable (fun t : ℝ => line c t*gaussian c l t) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-t^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have h1 : Integrable (fun t : ℝ => |t| * Real.exp (-t^2)) := by
    simpa [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).norm
  have hi := ((h0.const_mul |c|).add h1).mul_const (Real.exp (c^2-c*l))
  apply hi.mono' (by unfold gaussian line; fun_prop)
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_mul,gaussian_norm]
  have hl : ‖line c t‖ ≤ |c|+|t| := by
    simpa [line,norm_mul,Complex.norm_real,Real.norm_eq_abs] using norm_add_le (c:ℂ) ((t:ℂ)*I)
  exact (mul_le_mul_of_nonneg_right hl (by positivity)).trans_eq (by dsimp only [Pi.add_apply]; ring)

theorem gaussian_deriv (c l t : ℝ) :
    HasDerivAt (gaussian c l) (((2*line c t-(l:ℂ))*I)*gaussian c l t) t := by
  have hw : HasDerivAt (line c) I t := by
    change HasDerivAt (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) I t
    simpa only [id_eq,Complex.ofReal_one,one_mul] using
      (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (c:ℂ)
  convert ((hw.pow 2).sub (hw.const_mul (l:ℂ))).cexp using 1
  · rfl
  · dsimp [gaussian]; ring

theorem moment_integral (c l : ℝ) :
    (∫ t : ℝ, line c t*gaussian c l t) =
      ((l:ℂ)/2)*((Real.pi:ℂ)^(1/2:ℂ)*exp (-(l:ℂ)^2/4)) := by
  have hg := gaussian_integrable c l
  have hi : Integrable (fun t : ℝ => ((2*line c t-(l:ℂ))*I)*gaussian c l t) := by
    convert ((moment_integrable c l).const_mul (2*I)).sub (hg.const_mul ((l:ℂ)*I)) using 1
    funext t; dsimp [gaussian]; ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable (gaussian_deriv c l) hi hg
  have he (t : ℝ) : ((2*line c t-(l:ℂ))*I)*gaussian c l t =
      (2*I)*(line c t*gaussian c l t)-((l:ℂ)*I)*gaussian c l t := by ring
  simp_rw [he] at hz
  rw [integral_sub ((moment_integrable c l).const_mul _) (hg.const_mul _),
    integral_const_mul,integral_const_mul,gaussian_integral] at hz
  linear_combination (norm := ring_nf) (-I/2)*hz
  simp only [I_sq]
  ring

theorem weight_eq (sigma : ℂ) (hs : sigma ≠ 0) (x c t : ℝ) (hx : 0 < x) (hc : 0 < c) :
    weight sigma x c t = gaussian c (Real.log x) t/line c t-
      (4/sigma^2)*(line c t*gaussian c (Real.log x) t) := by
  have hn : line c t ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp [line] at hh; linarith
  have he : (x:ℂ)^(-line c t)*exp ((line c t)^2) = gaussian c (Real.log x) t := by
    unfold gaussian
    rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),← ofReal_log hx.le,← exp_add]
    congr 1; ring
  unfold weight
  rw [he]
  unfold annihilator
  field_simp
  ring

theorem weight_integrable (sigma : ℂ) (hs : sigma ≠ 0) (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Integrable (weight sigma x c) := by
  change Integrable (fun t : ℝ => weight sigma x c t)
  simp_rw [weight_eq sigma hs x c _ hx hc]
  exact (pole_integrable c _ hc).sub ((moment_integrable c _).const_mul _)

/-- Genuine independence of the positive abscissa, obtained from the
Gaussian pole and moment evaluations. No crossed pole lies in c>0. -/
theorem sourceW_shift (sigma : ℂ) (hs : sigma ≠ 0) (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    sourceW sigma x = (1/(2*Real.pi):ℂ)*(∫ t : ℝ, weight sigma x c t) := by
  have he : sourceW sigma x = (1/(2*Real.pi):ℂ)*(∫ t : ℝ, weight sigma x 2 t) := rfl
  rw [he]
  congr 1
  simp_rw [weight_eq sigma hs x c _ hx hc,weight_eq sigma hs x 2 _ hx (by norm_num)]
  rw [integral_sub (pole_integrable 2 _ (by norm_num)) ((moment_integrable 2 _).const_mul _),
    integral_sub (pole_integrable c _ hc) ((moment_integrable c _).const_mul _),
    integral_const_mul,integral_const_mul,pole_integral 2 _ (by norm_num),pole_integral c _ hc,
    moment_integral 2,moment_integral c]

#print axioms exponent
#print axioms gaussian_integrable
#print axioms gaussian_integral
#print axioms gaussian_norm
#print axioms laplace_integral
#print axioms joint_integrable
#print axioms pole_integral
#print axioms pole_integrable
#print axioms moment_integrable
#print axioms gaussian_deriv
#print axioms moment_integral
#print axioms weight_eq
#print axioms weight_integrable
#print axioms sourceW_shift
end XiPrime8845.PRZZSourceWLine

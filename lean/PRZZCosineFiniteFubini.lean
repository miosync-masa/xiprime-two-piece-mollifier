import PRZZCosineMellin
import Mathlib.MeasureTheory.Integral.Prod

/-! Supplied joint integrability of the explicitly differentiated Mellin
density on 0<y<=R, and its cosine/Mellin exchange. Identifying the y-wise
Mellin integral with the actual second sourceW derivative is separate;
no such conclusion is made into a premise. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineFiniteFubini
open PRZZCosineMellinCore PRZZCosineMellin
set_option maxHeartbeats 5000000

def density (sigma : ℂ) (X tau y : ℝ) : ℂ :=
  coefficient sigma X tau*exp ((line tau)^2)*
    ((exponent sigma tau-1)*(exponent sigma tau-2))*
      exp ((exponent sigma tau-3)*(Real.log y:ℂ))*cos (y:ℂ)

theorem density_eq (sigma : ℂ) (X tau y : ℝ) (hy : 0 < y) :
    density sigma X tau y = coefficient sigma X tau*exp ((line tau)^2)*
      ((exponent sigma tau-1)*(exponent sigma tau-2))*
        ((y:ℂ)^(exponent sigma tau-3)*cos (y:ℂ)) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),← Complex.ofReal_log hy.le]
  unfold density
  rw [mul_comm (exponent sigma tau-3) (Real.log y:ℂ)]
  ring

theorem density_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X tau y : ℝ) (hX : 0 < X) (hy : 0 < y) :
    ‖density sigma X tau y‖ ≤
      (42*Real.exp 2*X^(-5/4:ℝ)*(1+16/‖sigma‖^2))*
        ((1+|tau|)^4*Real.exp (-tau^2))*y^(sigma.re-1/2) := by
  let V := 1+|tau|
  have hV : 1 ≤ V := by dsimp [V]; linarith [abs_nonneg tau]
  have hz : ‖exponent sigma tau‖ ≤ 5*V := by
    have hh := norm_add_le (2*line tau) sigma
    norm_num [norm_mul] at hh
    have hl := (line_bounds tau).2
    dsimp [exponent,V]; linarith
  have hp1 : ‖exponent sigma tau-1‖ ≤ 6*V := by
    have hh := norm_sub_le (exponent sigma tau) (1:ℂ)
    norm_num at hh; linarith
  have hp2 : ‖exponent sigma tau-2‖ ≤ 7*V := by
    have hh := norm_sub_le (exponent sigma tau) (2:ℂ)
    norm_num at hh; linarith
  have he : ‖exp ((line tau)^2)‖ ≤ Real.exp 2*Real.exp (-tau^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp [line,pow_two,mul_re]
    nlinarith
  have hc : ‖(y:ℂ)^(exponent sigma tau-3)*cos (y:ℂ)‖ ≤ y^(sigma.re-1/2) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hreal : (exponent sigma tau-3).re = sigma.re-1/2 := by
      simp [exponent,line]; ring
    rw [hreal]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hy.le _) (by
      simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one y)
  rw [density_eq sigma X tau y hy]
  simp only [norm_mul]
  simp only [norm_mul] at hc
  have hh := mul_le_mul
    (mul_le_mul (coefficient_cap sigma hs X tau hX) he (norm_nonneg _) (by positivity))
    (mul_le_mul hp1 hp2 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
  have hh' := mul_le_mul hh hc (by positivity) (by positivity)
  apply hh'.trans_eq
  dsimp [V]
  ring

theorem joint_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R) :
    Integrable (fun p : ℝ × ℝ => density sigma X p.1 p.2)
      (volume.prod (volume.restrict (Ioc (0:ℝ) R))) := by
  let C := 42*Real.exp 2*X^(-5/4:ℝ)*(1+16/‖sigma‖^2)
  have ht := (gaussian_power_integrable 4).const_mul C
  have ha : -1 < sigma.re-1/2 := by
    have hh := (abs_le.mp ((abs_re_le_norm sigma).trans hn)).1
    linarith
  have hy : IntegrableOn (fun y : ℝ => y^(sigma.re-1/2)) (Ioc (0:ℝ) R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp (intervalIntegral.intervalIntegrable_rpow' ha)
  apply (ht.mul_prod hy).mono'
  · have hcoef := (coefficient_continuous sigma X hX).measurable
    exact (by
      unfold density
      have hh : Measurable (fun p : ℝ × ℝ => coefficient sigma X p.1) := hcoef.comp measurable_fst
      unfold exponent line
      fun_prop : Measurable (fun p : ℝ × ℝ => density sigma X p.1 p.2)).aestronglyMeasurable
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂volume.prod (volume.restrict (Ioc (0:ℝ) R)), p.2 ∈ Ioc (0:ℝ) R :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hpos] with p hp
    exact density_bound sigma hs hn X p.1 p.2 hX hp.1

theorem density_integral (sigma : ℂ) (X R tau : ℝ) (hR : 0 ≤ R) :
    (∫ y in Ioc (0:ℝ) R, density sigma X tau y) = truncated sigma X R tau := by
  have he : (∫ y in Ioc (0:ℝ) R, density sigma X tau y) =
      (coefficient sigma X tau*exp ((line tau)^2)*((exponent sigma tau-1)*(exponent sigma tau-2)))*
        ∫ y in Ioc (0:ℝ) R, (y:ℂ)^(exponent sigma tau-3)*cos (y:ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact density_eq sigma X tau y hy.1
  rw [he]
  unfold truncated moment cutCos
  rw [intervalIntegral.integral_of_le hR]
  ring

theorem finite_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R) :
    (∫ y in Ioc (0:ℝ) R, ∫ tau : ℝ, density sigma X tau y) =
      ∫ tau : ℝ, truncated sigma X R tau := by
  rw [← integral_integral_swap (joint_integrable sigma hs hn X R hX hR)]
  simp_rw [density_integral sigma X R _ hR]

theorem spatial_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun R : ℝ => ∫ y in Ioc (0:ℝ) R, ∫ tau : ℝ, density sigma X tau y) atTop
      (𝓝 (∫ tau : ℝ, evaluated sigma X tau)) := by
  apply (integral_exchange sigma hs hn X hX).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  exact (finite_exchange sigma hs hn X R hX hR).symm

#print axioms density_eq
#print axioms density_bound
#print axioms joint_integrable
#print axioms density_integral
#print axioms finite_exchange
#print axioms spatial_limit
end XiPrime8845.PRZZCosineFiniteFubini

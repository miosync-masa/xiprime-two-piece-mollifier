import PRZZCosineAbel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Ordinary oscillatory tails: one spatial integration by parts leaves
an absolutely integrable derivative for Re z < 1. These are genuine
limits of finite interval integrals, not totalized Bochner integrals. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineImproper
open PRZZGammaLaplace
set_option maxHeartbeats 5000000

theorem tail_norm (z c : ℂ) (hc : 0 ≤ c.re) (x : ℝ) (hx : 0 < x) :
    ‖kernel z c x‖ ≤ x^(z.re-1) := by
  rw [kernel_norm z c x hx]
  apply mul_le_of_le_one_right (Real.rpow_nonneg hx.le _)
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem derivative_tail_integrable (z c : ℂ) (hz : z.re < 1) (hc : 0 ≤ c.re) :
    IntegrableOn (kernel (z-1) c) (Ioi (1:ℝ)) := by
  apply (integrableOn_Ioi_rpow_of_lt (a := z.re-2) (by linarith) zero_lt_one).mono'
    (((kernel_continuous (z-1) c).mono (by
      intro x hx
      change (0:ℝ) < x
      exact lt_of_lt_of_le zero_lt_one (show (1:ℝ) ≤ x from le_of_lt hx))).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [sub_re,one_re,sub_sub,one_add_one_eq_two] using tail_norm (z-1) c hc x (lt_trans zero_lt_one hx)

theorem spatial_derivative (z c : ℂ) (hz : z.re < 1) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (kernel z c)
      ((z-1)*kernel (z-1) c x-c*kernel z c x) x := by
  have hn : z-1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hp := hasDerivAt_ofReal_cpow_const hx.ne' hn
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul (-c)).cexp
  have hh := hp.mul he
  convert hh using 1 <;> (try rfl) <;> (try dsimp [kernel]) <;> ring

theorem finite_tail (z c : ℂ) (hz : z.re < 1) (hc : c ≠ 0)
    (R : ℝ) (hR : 1 ≤ R) :
    (∫ x in (1:ℝ)..R, kernel z c x) =
      (kernel z c 1-kernel z c R+(z-1)*(∫ x in (1:ℝ)..R, kernel (z-1) c x))/c := by
  have hi (w : ℂ) : IntervalIntegrable (kernel w c) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    apply (kernel_continuous w c).mono
    rw [uIcc_of_le hR]
    intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := kernel z c) (f' := fun x => (z-1)*kernel (z-1) c x-c*kernel z c x)
    (a := (1:ℝ)) (b := R) (fun x hx => spatial_derivative z c hz x (by
      rw [uIcc_of_le hR] at hx; exact lt_of_lt_of_le zero_lt_one hx.1))
    (((hi (z-1)).const_mul (z-1)).sub ((hi z).const_mul c))
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hh
  · apply (eq_div_iff hc).mpr
    linear_combination -hh
  · exact (hi (z-1)).const_mul _
  · exact (hi z).const_mul _

theorem boundary_zero (z c : ℂ) (hz : z.re < 1) (hc : 0 ≤ c.re) :
    Tendsto (kernel z c) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x^(z.re-1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hz)
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact tail_norm z c hc x hx

def tailValue (z c : ℂ) : ℂ :=
  (kernel z c 1+(z-1)*(∫ x in Ioi (1:ℝ), kernel (z-1) c x))/c

theorem ordinary_tail_limit (z c : ℂ) (hz : z.re < 1)
    (hc : 0 ≤ c.re) (hn : c ≠ 0) :
    Tendsto (fun R : ℝ => ∫ x in (1:ℝ)..R, kernel z c x) atTop (𝓝 (tailValue z c)) := by
  have hi := intervalIntegral_tendsto_integral_Ioi (1:ℝ)
    (derivative_tail_integrable z c hz hc) tendsto_id
  have hh := (((tendsto_const_nhds (x := kernel z c 1)).sub (boundary_zero z c hz hc)).add
    (hi.const_mul (z-1))).div_const c
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  exact (finite_tail z c hz hn R hR).symm

theorem parameter_limit (z omega : ℂ) (s : Set ℝ) (hs : s ⊆ Ioi 0)
    (hm : MeasurableSet s) (hi : IntegrableOn (fun x : ℝ => x^(z.re-1)) s)
    (hw : omega.re = 0) :
    Tendsto (fun eps : ℝ => ∫ x in s, kernel z ((eps:ℂ)+omega) x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in s, kernel z omega x)) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => x^(z.re-1))
  · exact Filter.Eventually.of_forall (fun eps =>
      ((kernel_continuous z _).mono hs).aestronglyMeasurable hm)
  · filter_upwards [self_mem_nhdsWithin] with eps he
    filter_upwards [ae_restrict_mem hm] with x hx
    apply tail_norm z _ _ x (hs hx)
    simp only [add_re,ofReal_re,hw,add_zero]
    exact le_of_lt he
  · exact hi
  · apply Filter.Eventually.of_forall
    intro x
    have hh : Continuous (fun eps : ℝ => kernel z ((eps:ℂ)+omega) x) := by
      unfold kernel; fun_prop
    simpa only [ofReal_zero,zero_add] using
      (hh.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))

def fullValue (z c : ℂ) : ℂ := (∫ x in Ioc (0:ℝ) 1, kernel z c x)+tailValue z c

theorem full_parameter_limit (z omega : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1)
    (hw : omega.re = 0) (hn : omega ≠ 0) :
    Tendsto (fun eps : ℝ => fullValue z ((eps:ℂ)+omega))
      (𝓝[>] (0:ℝ)) (𝓝 (fullValue z omega)) := by
  have hpow : IntegrableOn (fun x : ℝ => x^(z.re-1)) (Ioc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hnear := parameter_limit z omega (Ioc 0 1) Ioc_subset_Ioi_self measurableSet_Ioc hpow hw
  have htail := parameter_limit (z-1) omega (Ioi 1)
    (by intro x hx; exact lt_trans (show (0:ℝ) < 1 by norm_num) hx) measurableSet_Ioi
    (by simpa only [sub_re,one_re,sub_sub,one_add_one_eq_two] using
      integrableOn_Ioi_rpow_of_lt (a := z.re-2) (by linarith) zero_lt_one) hw
  have hrate : Tendsto (fun eps : ℝ => (eps:ℂ)+omega) (𝓝[>] (0:ℝ)) (𝓝 omega) := by
    simpa only [ofReal_zero,zero_add] using
      ((Complex.continuous_ofReal.continuousAt (x := (0:ℝ))).add_const omega).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hk : Continuous (fun c : ℂ => kernel z c 1) := by unfold kernel; fun_prop
  exact hnear.add (((hk.continuousAt.tendsto.comp hrate).add
    (htail.const_mul (z-1))).div hrate hn)

theorem full_eq_laplace (z c : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) (hc : 0 < c.re) :
    fullValue z c = laplace z c := by
  have hi := kernel_integrable z c hz hc
  have hit : IntegrableOn (kernel z c) (Ioi (1:ℝ)) := hi.mono_set (by
    intro x hx; exact lt_trans (show (0:ℝ) < 1 by norm_num) hx)
  have hn : c ≠ 0 := by intro h; simp [h] at hc
  have he := tendsto_nhds_unique (ordinary_tail_limit z c hz1 hc.le hn)
    (intervalIntegral_tendsto_integral_Ioi (1:ℝ) hit tendsto_id)
  unfold fullValue
  rw [he,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact intervalIntegral.integral_interval_add_Ioi hi hit

theorem ordinary_full_limit (z c : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1)
    (hc : 0 ≤ c.re) (hn : c ≠ 0) :
    Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..R, kernel z c x) atTop (𝓝 (fullValue z c)) := by
  have hpow : IntegrableOn (fun x : ℝ => x^(z.re-1)) (Ioc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hi : IntervalIntegrable (kernel z c) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
    apply hpow.mono' (((kernel_continuous z c).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact tail_norm z c hc x hx.1
  have hh := (ordinary_tail_limit z c hz1 hc hn).const_add (∫ x in (0:ℝ)..1, kernel z c x)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hj : IntervalIntegrable (kernel z c) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    apply (kernel_continuous z c).mono
    rw [uIcc_of_le hR]; intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using
    intervalIntegral.integral_add_adjacent_intervals hi hj

theorem full_boundary_value (z omega : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1)
    (hw : omega.re = 0) (hn : omega ≠ 0) :
    fullValue z omega = omega^(-z)*Complex.Gamma z := by
  have hslit : omega ∈ slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    intro h
    apply hn
    apply Complex.ext <;> simp_all
  have hrate : Tendsto (fun eps : ℝ => (eps:ℂ)+omega) (𝓝[>] (0:ℝ)) (𝓝 omega) := by
    simpa only [ofReal_zero,zero_add] using
      ((Complex.continuous_ofReal.continuousAt (x := (0:ℝ))).add_const omega).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hh := ((continuousAt_cpow_const (b := -z) hslit).mul_const (Complex.Gamma z)).tendsto.comp hrate
  have he : (fun eps : ℝ => fullValue z ((eps:ℂ)+omega)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun eps : ℝ => ((eps:ℂ)+omega)^(-z)*Complex.Gamma z) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have hc : 0 < ((eps:ℂ)+omega).re := by simpa [hw] using heps
    rw [full_eq_laplace z _ hz hz1 hc,laplace_eq z _ hz hc]
  exact tendsto_nhds_unique (full_parameter_limit z omega hz hz1 hw hn) (hh.congr' he.symm)

theorem local_integrable (z c : ℂ) (hz : 0 < z.re) (hc : 0 ≤ c.re)
    (R : ℝ) (hR : 0 ≤ R) : IntervalIntegrable (kernel z c) volume 0 R := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
  have hpow : IntegrableOn (fun x : ℝ => x^(z.re-1)) (Ioc (0:ℝ) R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  apply hpow.mono' (((kernel_continuous z c).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact tail_norm z c hc x hx.1

/-- The usual improper cosine Mellin integral, as an actual R→∞
limit of the integrals from zero to R. Both strip conditions are used. -/
theorem ordinary_cosine_limit (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..R, (x:ℂ)^(z-1)*Complex.cos (x:ℂ))
      atTop (𝓝 (Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*z/2))) := by
  have hp := ordinary_full_limit z (-I) hz hz1 (by simp) (neg_ne_zero.mpr I_ne_zero)
  have hm := ordinary_full_limit z I hz hz1 (by simp) I_ne_zero
  have hh := (hp.add hm).div_const (2:ℂ)
  have hv : (fullValue z (-I)+fullValue z I)/2 = Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*z/2) := by
    rw [full_boundary_value z (-I) hz hz1 (by simp) (neg_ne_zero.mpr I_ne_zero),
      full_boundary_value z I hz hz1 (by simp) I_ne_zero]
    calc
      _ = Complex.Gamma z/2*((-I)^(-z)+I^(-z)) := by ring
      _ = _ := by rw [PRZZCosineAbel.imaginary_powers]; ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  have hi := local_integrable z (-I) hz (by simp) R hR
  have hj := local_integrable z I hz (by simp) R hR
  rw [← intervalIntegral.integral_add hi hj,← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  simpa only [PRZZCosineAbel.integrand,ofReal_zero,neg_zero,zero_mul,
    Complex.exp_zero,mul_one,zero_sub,zero_add] using (PRZZCosineAbel.exponential_pair z 0 x).symm

/-- The two spatial derivatives in the actual zero mode are restored
before evaluation. This retains the cosine argument z-2, including its sign. -/
theorem twice_differentiated_cosine (z : ℂ) (hz : 2 < z.re) (hz1 : z.re < 3) :
    Tendsto (fun R : ℝ => (z-1)*(z-2)*
      (∫ x in (0:ℝ)..R, (x:ℂ)^(z-3)*Complex.cos (x:ℂ))) atTop
      (𝓝 (Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*(z-2)/2))) := by
  have h0 : 0 < (z-2).re := by norm_num [sub_re]; linarith
  have h1 : (z-2).re < 1 := by norm_num [sub_re]; linarith
  have hn : z-2 ≠ 0 := by intro h; simp [h] at h0
  have hn1 : z-1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hg : (z-1)*(z-2)*Complex.Gamma (z-2) = Complex.Gamma z := by
    have ha := Complex.Gamma_add_one (z-2) hn
    have hb := Complex.Gamma_add_one (z-1) hn1
    rw [show z-2+1 = z-1 by ring] at ha
    rw [show z-1+1 = z by ring] at hb
    rw [hb,ha]; ring
  have hh := (ordinary_cosine_limit (z-2) h0 h1).const_mul ((z-1)*(z-2))
  simpa only [show z-2-1 = z-3 by ring,← mul_assoc,hg] using hh

/-- The original initial line Re s=5/4 lies in the genuine improper
cosine strip after two derivatives, uniformly over the small shift disc. -/
theorem source_vertical_cosine (sigma : ℂ) (hs : ‖sigma‖ ≤ 1/8) (tau : ℝ) :
    let s : ℂ := (5/4:ℝ)+(tau:ℂ)*I
    let z : ℂ := 2*s+sigma
    Tendsto (fun R : ℝ => (z-1)*(z-2)*
      (∫ x in (0:ℝ)..R, (x:ℂ)^(z-3)*Complex.cos (x:ℂ))) atTop
      (𝓝 (Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*(z-2)/2))) := by
  dsimp only
  have hb := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hs)
  apply twice_differentiated_cosine <;>
    simp only [add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,mul_one,sub_zero] <;> norm_num <;> linarith

#print axioms twice_differentiated_cosine
#print axioms source_vertical_cosine
#print axioms full_boundary_value
#print axioms local_integrable
#print axioms ordinary_cosine_limit
#print axioms parameter_limit
#print axioms full_parameter_limit
#print axioms full_eq_laplace
#print axioms ordinary_full_limit
#print axioms tail_norm
#print axioms derivative_tail_integrable
#print axioms spatial_derivative
#print axioms finite_tail
#print axioms boundary_zero
#print axioms ordinary_tail_limit
end XiPrime8845.PRZZCosineImproper

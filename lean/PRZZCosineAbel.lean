import PRZZGammaLaplace

/-! Abel-regularized cosine Mellin integral. The rate is complex, and
integrability is proved before splitting the two exponentials. The Abel
limit is not identified here with an ordinary improper integral or with
the full zero-mode Mellin interchange. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineAbel
open PRZZGammaLaplace
set_option maxHeartbeats 5000000

def integrand (z : ℂ) (eps x : ℝ) : ℂ :=
  (x:ℂ)^(z-1)*Complex.exp (-(eps:ℂ)*(x:ℂ))*Complex.cos (x:ℂ)

theorem exponential_pair (z : ℂ) (eps x : ℝ) :
    integrand z eps x =
      (kernel z ((eps:ℂ)-I) x+kernel z ((eps:ℂ)+I) x)/2 := by
  unfold integrand kernel
  rw [Complex.cos]
  have hp : -((eps:ℂ)-I)*(x:ℂ) = -(eps:ℂ)*(x:ℂ)+(x:ℂ)*I := by ring
  have hm : -((eps:ℂ)+I)*(x:ℂ) = -(eps:ℂ)*(x:ℂ)+(-((x:ℂ)*I)) := by ring
  rw [hp,hm,Complex.exp_add,Complex.exp_add]
  ring_nf

theorem integrable (z : ℂ) (eps : ℝ) (hz : 0 < z.re) (he : 0 < eps) :
    IntegrableOn (integrand z eps) (Ioi (0:ℝ)) := by
  have hp := kernel_integrable z ((eps:ℂ)-I) hz (by simpa using he)
  have hm := kernel_integrable z ((eps:ℂ)+I) hz (by simpa using he)
  have hh : IntegrableOn (fun x => (kernel z ((eps:ℂ)-I) x+
      kernel z ((eps:ℂ)+I) x)/2) (Ioi (0:ℝ)) := (hp.add hm).div_const (2:ℂ)
  exact IntegrableOn.congr_fun hh (fun x _ => (exponential_pair z eps x).symm) measurableSet_Ioi

theorem integral_eq (z : ℂ) (eps : ℝ) (hz : 0 < z.re) (he : 0 < eps) :
    (∫ x in Ioi (0:ℝ), integrand z eps x) =
      Complex.Gamma z/2*(((eps:ℂ)-I)^(-z)+((eps:ℂ)+I)^(-z)) := by
  simp_rw [exponential_pair]
  rw [integral_div,integral_add
    (kernel_integrable z ((eps:ℂ)-I) hz (by simpa using he))
    (kernel_integrable z ((eps:ℂ)+I) hz (by simpa using he))]
  change (laplace z ((eps:ℂ)-I)+laplace z ((eps:ℂ)+I))/2 = _
  rw [laplace_eq z _ hz (by simpa using he),laplace_eq z _ hz (by simpa using he)]
  ring

theorem imaginary_powers (z : ℂ) :
    (-I)^(-z)+I^(-z) = 2*Complex.cos ((Real.pi:ℂ)*z/2) := by
  rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero),
    Complex.cpow_def_of_ne_zero I_ne_zero,Complex.log_neg_I,Complex.log_I]
  have hp : (-((Real.pi:ℂ)/2)*I)*(-z) = ((Real.pi:ℂ)*z/2)*I := by ring
  have hm : ((Real.pi:ℂ)/2*I)*(-z) = -(((Real.pi:ℂ)*z/2)*I) := by ring
  rw [hp,hm,Complex.cos]
  ring

/-- The limit is a one-sided Abel limit, not a Bochner integral of the
undamped oscillatory integrand. No restriction Re z < 1 is needed here. -/
theorem abel_limit (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun eps : ℝ => ∫ x in Ioi (0:ℝ), integrand z eps x)
      (𝓝[>] (0:ℝ)) (𝓝 (Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*z/2))) := by
  have hp : ContinuousAt (fun eps : ℝ => ((eps:ℂ)-I)^(-z)) 0 := by
    exact (continuousAt_cpow_const (a := (0:ℂ)-I) (b := -z) (by
      simp [Complex.mem_slitPlane_iff])).comp (x := (0:ℝ))
        (Complex.continuous_ofReal.continuousAt.sub continuousAt_const)
  have hm : ContinuousAt (fun eps : ℝ => ((eps:ℂ)+I)^(-z)) 0 := by
    exact (continuousAt_cpow_const (a := (0:ℂ)+I) (b := -z) (by
      simp [Complex.mem_slitPlane_iff])).comp (x := (0:ℝ))
        (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
  have hh := ((hp.add hm).const_mul (Complex.Gamma z/2)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have he : Complex.Gamma z/2*(((-I)^(-z))+I^(-z)) =
      Complex.Gamma z*Complex.cos ((Real.pi:ℂ)*z/2) := by rw [imaginary_powers]; ring
  simp only [Pi.add_apply,Complex.ofReal_zero,zero_sub,zero_add,he] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact (integral_eq z eps hz heps).symm

#print axioms exponential_pair
#print axioms integrable
#print axioms integral_eq
#print axioms imaginary_powers
#print axioms abel_limit
end XiPrime8845.PRZZCosineAbel

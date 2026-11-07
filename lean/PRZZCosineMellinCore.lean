import PRZZCosineDominated
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability is supplied for the actual finite cosine moments,
before using dominated convergence in the Mellin variable. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineMellinCore
set_option maxHeartbeats 5000000

def line (tau : ℝ) : ℂ := (5/4:ℝ)+(tau:ℂ)*I
def exponent (sigma : ℂ) (tau : ℝ) : ℂ := 2*line tau+sigma
def cutCos (sigma : ℂ) (R tau : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..R, (x:ℂ)^(exponent sigma tau-3)*Complex.cos (x:ℂ)
def moment (sigma : ℂ) (R tau : ℝ) : ℂ :=
  (exponent sigma tau-1)*(exponent sigma tau-2)*cutCos sigma R tau
def limitMoment (sigma : ℂ) (tau : ℝ) : ℂ :=
  Complex.Gamma (exponent sigma tau)*Complex.cos ((Real.pi:ℂ)*(exponent sigma tau-2)/2)

theorem cutCos_continuous (sigma : ℂ) (hs : ‖sigma‖ ≤ 1/8)
    (R : ℝ) (hR : 0 ≤ R) : Continuous (cutCos sigma R) := by
  apply continuous_iff_continuousAt.mpr
  intro tau
  have hb := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hs)
  let a : ℝ := sigma.re-1/2
  have ha : -1 < a := by dsimp [a]; linarith
  have hp (v : ℝ) (x : ℝ) (hx : 0 < x) :
      ‖(x:ℂ)^(exponent sigma v-3)*Complex.cos (x:ℂ)‖ ≤ x^a := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have he : (exponent sigma v-3).re = a := by
      dsimp [exponent,line,a]; norm_num; ring
    rw [he]
    apply mul_le_of_le_one_right (Real.rpow_nonneg hx.le _)
    simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one x
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => x^a)
  · apply Filter.Eventually.of_forall
    intro v
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    intro x hx
    rw [uIoc_of_le hR] at hx
    have hh := (continuousAt_cpow_const (b := exponent sigma v-3)
      (Complex.ofReal_mem_slitPlane.mpr hx.1)).comp (x := x) Complex.continuous_ofReal.continuousAt
    exact (hh.mul (by fun_prop)).continuousWithinAt
  · exact Filter.Eventually.of_forall (fun v => Filter.Eventually.of_forall (fun x hx =>
      hp v x (by rw [uIoc_of_le hR] at hx; exact hx.1)))
  · exact intervalIntegral.intervalIntegrable_rpow' ha
  · apply Filter.Eventually.of_forall
    intro x hx
    rw [uIoc_of_le hR] at hx
    have hh : Continuous (fun v : ℝ => (x:ℂ)^(exponent sigma v-3)*Complex.cos (x:ℂ)) := by
      apply Continuous.mul _ continuous_const
      apply continuous_iff_continuousAt.mpr
      intro v
      apply (continuousAt_const_cpow (a := (x:ℂ)) (by exact_mod_cast hx.1.ne')).comp
      dsimp [exponent,line]; fun_prop
    exact hh.continuousAt.tendsto

theorem moment_continuous (sigma : ℂ) (hs : ‖sigma‖ ≤ 1/8)
    (R : ℝ) (hR : 0 ≤ R) : Continuous (moment sigma R) := by
  have hh := cutCos_continuous sigma hs R hR
  unfold moment
  apply Continuous.mul _ hh
  dsimp [exponent,line]; fun_prop

theorem moment_tendsto (sigma : ℂ) (hs : ‖sigma‖ ≤ 1/8) (tau : ℝ) :
    Tendsto (fun R : ℝ => moment sigma R tau) atTop (𝓝 (limitMoment sigma tau)) :=
  PRZZCosineImproper.source_vertical_cosine sigma hs tau

theorem gaussian_power_integrable (n : ℕ) :
    Integrable (fun t : ℝ => (1+|t|)^n*Real.exp (-t^2)) := by
  have h (k : ℕ) : Integrable (fun t : ℝ => |t|^k*Real.exp (-t^2)) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)) (s := (k:ℝ))
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simpa only [Real.rpow_natCast,one_mul,neg_mul,norm_mul,Real.norm_eq_abs,
      abs_pow,Real.abs_exp] using hh.norm
  have hi := integrable_finsetSum (Finset.range (n+1))
    (fun k hk => (h (n-k)).const_mul (n.choose k:ℝ))
  have he : (fun t : ℝ => (1+|t|)^n*Real.exp (-t^2)) =
      (fun t : ℝ => ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ)*(|t|^(n-k)*Real.exp (-t^2))) := by
    funext t
    rw [add_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [one_pow,one_mul]
    ring
  rw [he]
  exact hi

#print axioms cutCos_continuous
#print axioms moment_continuous
#print axioms moment_tendsto
#print axioms gaussian_power_integrable
end XiPrime8845.PRZZCosineMellinCore

import PRZZKernelTime
import PRZZActualDirectSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Time integration of the actual infinite direct series on compact intervals.
The envelope is uniform in time and arithmetic indices, but may grow
exponentially with the fixed interval radius. This is not the AFE identity. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZArithmeticTime
open PRZZKernelTime PRZZMellinTail PRZZActualDirectSum PRZZL1Finite
set_option maxHeartbeats 3000000

theorem kernel_measurable (a b : ℂ) (x : ℝ) (hx : 0 < x)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    StronglyMeasurable (fun t => PRZZAFEGamma.kernel a b x t) := by
  simp_rw [kernel_eq]
  exact ((joint_continuous a b x hx ha hb).stronglyMeasurable.integral_prod_right').const_mul _

theorem kernel_window_bound (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ, |t| ≤ R →
      ‖PRZZAFEGamma.kernel a b x t‖ ≤ C*x^(-2:ℝ) := by
  obtain ⟨B,hB,h⟩ := uniform_space_majorant a b ha ha' hb hb' hs R
  refine ⟨(1/(2*Real.pi))*B*(∫ v, majorant v),by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun v => by unfold majorant; positivity),?_⟩
  intro x hx t ht
  rw [kernel_eq,norm_mul]
  have hi := integrand_integrable a b ha ha' hb hb' hs x t hx
  have he := integral_mono hi.norm (majorant_integrable.const_mul (B*x^(-2:ℝ))) (h x hx t · ht)
  have hh := (norm_integral_le_integral_norm _).trans he
  have hp : ‖(1/(2*Real.pi):ℂ)‖ = (1/(2*Real.pi):ℝ) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hp]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
  rw [integral_const_mul]
  ring

/-- A continuous time weight is bounded on the retained compact interval;
no summability or integral-interchange premise is requested. -/
theorem weighted_time_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) :
    (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R,
      φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) =
      ∫ t in Icc (-R) R, ∑' p : ℕ × ℕ,
        φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  let E := max D 0
  have hE : 0 ≤ E := le_max_right _ _
  obtain ⟨C,hC,h⟩ := kernel_window_bound a b ha ha' hb hb' hs R
  let w := fun p : ℕ × ℕ => C*(1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)
  have hw (p : ℕ × ℕ) : 0 ≤ w p := by dsimp [w]; positivity
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hws : Summable w := by
    simpa [w,mul_assoc] using
      ((hp.mul_of_nonneg hp (by intro n; positivity) (by intro n; positivity)).mul_left C)
  have hbound (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc (-R) R) :
      ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ w p := by
    have hd := denominator_one a b ha.le hb.le t (p.1+1) (p.2+1) (by omega) (by omega)
    rw [directTerm,norm_div]
    apply (div_le_self (norm_nonneg _) hd).trans
    apply (h _ (by positivity) t (abs_le.mpr ht)).trans_eq
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    dsimp [w]
    push_cast
    field_simp
  have hweighted (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc (-R) R) :
      ‖φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ E*w p := by
    rw [norm_mul]
    exact mul_le_mul ((hD t ht).trans (le_max_left _ _)) (hbound p t ht)
      (norm_nonneg _) hE
  have hconst (p : ℕ × ℕ) : IntegrableOn (fun _ : ℝ => E*w p) (Icc (-R) R) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hi (p : ℕ × ℕ) : IntegrableOn
      (fun t => φ t * directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) (Icc (-R) R) := by
    apply (hconst p).mono'
    · apply StronglyMeasurable.aestronglyMeasurable
      apply hφ.stronglyMeasurable.mul
      unfold directTerm actualWeight
      apply StronglyMeasurable.div
      · exact kernel_measurable a b _ (by positivity) ha hb
      · apply Continuous.stronglyMeasurable
        have hm : ((p.1+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.1)
        have hk : ((p.2+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero p.2)
        simp_rw [Complex.cpow_def_of_ne_zero hm,Complex.cpow_def_of_ne_zero hk]
        fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hweighted p t ht
  apply integral_tsum_of_summable_integral_norm hi
  apply ((hws.mul_left E).mul_right (volume (Icc (-R) R)).toReal).of_nonneg_of_le
  · intro p; exact integral_nonneg (fun t => norm_nonneg _)
  · intro p
    have hh := setIntegral_mono_on (hi p).norm (hconst p)
      measurableSet_Icc (hweighted p)
    simpa only [setIntegral_const,smul_eq_mul,Measure.real,mul_comm] using hh

theorem actual_time_swap (a b : ℂ)
    (ha : -(1/2:ℝ) < a.re) (ha' : a.re < 3/2)
    (hb : -(1/2:ℝ) < b.re) (hb' : b.re < 3/2) (hs : a+b ≠ 0) (R : ℝ) :
    (∑' p : ℕ × ℕ, ∫ t in Icc (-R) R,
      directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) =
      ∫ t in Icc (-R) R, ∑' p : ℕ × ℕ,
        directTerm a b (actualWeight a b) t (p.1+1) (p.2+1) := by
  simpa only [one_mul] using weighted_time_swap a b ha ha' hb hb' hs R
    (fun _ => 1) continuous_const

#print axioms weighted_time_swap
#print axioms kernel_measurable
#print axioms kernel_window_bound
#print axioms actual_time_swap
end XiPrime8845.PRZZArithmeticTime

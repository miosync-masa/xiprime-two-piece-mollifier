import FengMixedMoment

/-! Abel identities for the actual signed Conrey/shared arithmetic measure.
No positivity of the weight or additional scalar asymptotic is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.FengMixedAbel
open FengMixedMoment LogProfileSum
set_option maxHeartbeats 1000000

theorem weight_zero : weight 0 = 0 := by simp [weight]

theorem weight_cast (g : ℕ) :
    (weight g : ℂ) = (μ g:ℂ)*FengMarkedProfile.primeMoment g/(g.totient:ℂ) := by
  simp only [weight,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_natCast,FengMarkedAbel.primeMoment_real]

theorem complex_summatory (x : ℝ) :
    (∑ n ∈ Icc 0 ⌊x⌋₊, (weight n:ℂ)) = (summatory x:ℂ) := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _),sum_cons,weight_zero]
  simp only [Complex.ofReal_zero,zero_add,summatory,Complex.ofReal_sum]

def testedSum (x : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, F n * (weight n:ℂ)


/-- Cubic normalization of the literal signed weighted sum. -/
def profileSum (L U : ℝ) (H : ℝ → ℂ) : ℂ :=
  testedSum (Real.exp (L*U)) (fun t => H (coordinate L U t))/(L:ℂ)^3

theorem profileSum_eq (L U : ℝ) (H : ℝ → ℂ) :
    profileSum L U H =
      (∑ g ∈ Ioc 0 (CoprimeEndpoint.cutoff L U),
        (μ g:ℂ)*FengMarkedProfile.primeMoment g/(g.totient:ℂ) *
          H (coordinate L U g))/(L:ℂ)^3 := by
  simp only [profileSum,testedSum,CoprimeEndpoint.cutoff,weight_cast,mul_comm]

theorem abel_identity (x : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x)) :
    testedSum x F = F x*(summatory x:ℂ) - ∫ t in 1..x, F' t*(summatory t:ℂ) := by
  have hi : IntegrableOn (deriv F) (Set.Icc 1 x) := by
    apply (hc.integrableOn_compact isCompact_Icc).congr_fun _ measurableSet_Icc
    intro t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_integral_mul₀ (fun n => (weight n:ℂ))
    (by simp [weight_zero]) x (fun t ht => (hd t ht).differentiableAt) hi
  simp only [complex_summatory] at h
  rw [Icc_eq_cons_Ioc (Nat.zero_le _),sum_cons] at h
  simp only [weight_zero,Complex.ofReal_zero,mul_zero,zero_add] at h
  rw [intervalIntegral.integral_of_le hx]
  convert h using 1
  · rfl
  · apply congrArg (fun z => F x*(summatory x:ℂ)-z)
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]

theorem weighted_error_identity (x c : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x)) :
    testedSum x F - (∫ t in 1..x, F t * (3*c*(Real.log t)^2/t : ℝ)) =
      F x*((summatory x-c*(Real.log x)^3:ℝ):ℂ) -
      ∫ t in 1..x, F' t*((summatory t-c*(Real.log t)^3:ℝ):ℂ) := by
  have hF : ContinuousOn F (Set.Icc 1 x) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hlog : ContinuousOn Real.log (Set.Icc (1:ℝ) x) :=
    continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hJ : ContinuousOn (fun t => ((c*(Real.log t)^3:ℝ):ℂ)) (Set.Icc 1 x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (hlog.pow 3))
  have hdJ (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => ((c*(Real.log t)^3:ℝ):ℂ)) (3*c*(Real.log t)^2/t:ℝ) t := by
    have hr : HasDerivAt (fun t : ℝ => c*(Real.log t)^3) (3*c*(Real.log t)^2/t) t := by
      convert! ((Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).pow 3).const_mul c using 1
      norm_num
      ring
    exact hr.ofReal_comp
  have hJ' : ContinuousOn (fun t => (3*c*(Real.log t)^2/t:ℝ)) (Set.Icc 1 x) :=
    (continuousOn_const.mul (hlog.pow 2)).div continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hi₁ : IntervalIntegrable (fun t => F t*(3*c*(Real.log t)^2/t:ℝ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((hF.mul (Complex.continuous_ofReal.comp_continuousOn hJ')).integrableOn_compact isCompact_Icc)
  have hi₂ : IntervalIntegrable (fun t => F' t*((c*(Real.log t)^3:ℝ):ℂ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ((hc.mul hJ).integrableOn_compact isCompact_Icc)
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hd t (by simpa only [Set.uIcc_of_le hx] using ht)).mul
      (hdJ t (by simpa only [Set.uIcc_of_le hx] using ht))) (hi₂.add hi₁)
  rw [intervalIntegral.integral_add hi₂ hi₁] at hp
  change (∫ t in 1..x, F' t*((c*(Real.log t)^3:ℝ):ℂ)) +
    (∫ t in 1..x, F t*(3*c*(Real.log t)^2/t:ℝ)) =
    F x*((c*(Real.log x)^3:ℝ):ℂ)-F 1*((c*(Real.log 1)^3:ℝ):ℂ) at hp
  simp only [Real.log_one,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,mul_zero,Complex.ofReal_zero,sub_zero] at hp
  have hisum : IntervalIntegrable (fun t => F' t*(summatory t:ℂ)) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    simpa only [complex_summatory] using integrableOn_mul_sum_Icc (m:=0)
      (fun n => (weight n:ℂ)) (by norm_num : (0:ℝ)≤1) (hc.integrableOn_compact isCompact_Icc)
  simp_rw [Complex.ofReal_sub,mul_sub]
  rw [intervalIntegral.integral_sub hisum hi₂,abel_identity x hx F F' hd hc]
  linear_combination -hp

theorem weighted_error_bound (x c E : ℝ) (hx : 1 ≤ x) (F F' : ℝ → ℂ)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt F (F' t) t)
    (hc : ContinuousOn F' (Set.Icc 1 x))
    (hE : ∀ t ∈ Set.Icc 1 x, |summatory t-c*(Real.log t)^3| ≤ E) :
    ‖testedSum x F - (∫ t in 1..x, F t*(3*c*(Real.log t)^2/t:ℝ))‖ ≤
      E*(‖F x‖+∫ t in 1..x, ‖F' t‖) := by
  have hlog : ContinuousOn (fun t => ((c*(Real.log t)^3:ℝ):ℂ)) (Set.Icc (1:ℝ) x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      ((continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).pow 3))
  have hisum : IntegrableOn (fun t => F' t*(summatory t:ℂ)) (Set.Icc 1 x) := by
    simpa only [complex_summatory] using integrableOn_mul_sum_Icc (m:=0)
      (fun n => (weight n:ℂ)) (by norm_num : (0:ℝ)≤1) (hc.integrableOn_compact isCompact_Icc)
  have hir : IntervalIntegrable (fun t => F' t*((summatory t-c*(Real.log t)^3:ℝ):ℂ)) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    have hsub : IntegrableOn (fun t => F' t*(summatory t:ℂ)-F' t*((c*(Real.log t)^3:ℝ):ℂ))
        (Set.Icc 1 x) := hisum.sub ((hc.mul hlog).integrableOn_compact isCompact_Icc)
    simpa only [Complex.ofReal_sub,mul_sub] using hsub
  have hin : IntervalIntegrable (fun t => ‖F' t‖*E) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((hc.norm.mul_const E).integrableOn_compact isCompact_Icc)
  rw [weighted_error_identity x c hx F F' hd hc]
  apply (norm_sub_le _ _).trans
  have hb (t : ℝ) (ht : t ∈ Set.Icc 1 x) : ‖((summatory t-c*(Real.log t)^3:ℝ):ℂ)‖ ≤ E := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hE t ht
  have hend := mul_le_mul_of_nonneg_left (hb x ⟨hx,le_rfl⟩) (norm_nonneg (F x))
  have hint : ‖∫ t in 1..x, F' t*((summatory t-c*(Real.log t)^3:ℝ):ℂ)‖ ≤
      (∫ t in 1..x, ‖F' t‖)*E := by
    rw [← intervalIntegral.integral_mul_const]
    apply (intervalIntegral.norm_integral_le_integral_norm hx).trans
    apply intervalIntegral.integral_mono_on hx hir.norm hin
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
  rw [norm_mul]
  nlinarith [hend,hint]


#print axioms weight_zero
#print axioms weight_cast
#print axioms complex_summatory
#print axioms profileSum_eq
#print axioms abel_identity
#print axioms weighted_error_identity
#print axioms weighted_error_bound
end XiPrime8845.FengMixedAbel

import FengMarkedProfile

/-! Abel reduction of the actual marked arithmetic measure.
The scalar cumulative asymptotic is an explicit input, not a new axiom.
All prime-power contributions in primeMoment are retained. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.FengMarkedAbel
open FengMarkedProfile LogProfileSum
set_option maxHeartbeats 1000000

def weight (g : ℕ) : ℝ := (primeMoment g).re ^ 2 / g.totient

theorem primeMoment_real (g : ℕ) : ((primeMoment g).re : ℂ) = primeMoment g := by
  have he : Complex.ofReal (∑ p ∈ g.primeFactors, (Real.log p)^2 * (μ (g/p^(g.factorization p)):ℝ)) =
      primeMoment g := by
    simp only [primeMoment,Complex.ofReal_sum,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_intCast]
  rw [← he,Complex.ofReal_re]

theorem weight_cast (g : ℕ) : (weight g : ℂ) = (primeMoment g)^2 / (g.totient:ℂ) := by
  rw [weight, Complex.ofReal_div, Complex.ofReal_pow, primeMoment_real]
  norm_cast

theorem weight_nonneg (g : ℕ) : 0 ≤ weight g := by unfold weight; positivity

theorem weight_zero : weight 0 = 0 := by simp [weight]

/-- An unconditional majorant for the actual marked weight, including
non-squarefree g. It controls mass but does not determine its leading constant. -/
theorem weight_bound (g : ℕ) (hg : g ≠ 0) :
    weight g ≤ (Real.log g)^4 * ((1/(g:ℝ))*SupportTail.eulerMass g 0^2) := by
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hg
  have hg0 : (0:ℝ) < g := lt_of_lt_of_le zero_lt_one hg1
  have hφ : (0:ℝ) < g.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hg)
  have hm := FengSharedTail.mark_bound g hg 1 (Real.log g) (by norm_num)
    (by simp only [div_one,abs_of_nonneg (Real.log_nonneg hg1),le_refl])
  rw [mark_eq_moment] at hm
  norm_num only [Complex.ofReal_one,one_pow,div_one] at hm
  rw [← primeMoment_real,Complex.norm_real,Real.norm_eq_abs] at hm
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hm 2
  rw [sq_abs] at hsq
  have hφg : (g.totient:ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
  have hE : 1 ≤ SupportTail.eulerMass g 0 := by
    rw [TotientWeight.eulerMass_zero g hg]
    exact (one_le_div hφ).mpr hφg
  have hEE : SupportTail.eulerMass g 0 ≤ SupportTail.eulerMass g 0^2 := by nlinarith
  have he : 1/(g.totient:ℝ) = (1/(g:ℝ))*SupportTail.eulerMass g 0 := by
    rw [TotientWeight.eulerMass_zero g hg]
    field_simp
  calc
    weight g ≤ (Real.log g)^4/(g.totient:ℝ) := by
      apply div_le_div_of_nonneg_right _ hφ.le
      nlinarith [hsq]
    _ = (Real.log g)^4*((1/(g:ℝ))*SupportTail.eulerMass g 0) := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hEE (by positivity)) (by positivity)

def summatory (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, weight n

theorem complex_summatory (x : ℝ) :
    (∑ n ∈ Icc 0 ⌊x⌋₊, (weight n:ℂ)) = (summatory x:ℂ) := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _),sum_cons,weight_zero]
  simp only [Complex.ofReal_zero,zero_add,summatory,Complex.ofReal_sum]

def testedSum (x : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, F n * (weight n:ℂ)

theorem markedProfileSum_eq (L U : ℝ) (H : ℝ → ℂ) :
    markedProfileSum L U H =
      testedSum (Real.exp (L*U)) (fun t => H (coordinate L U t)) / (L:ℂ)^5 := by
  unfold markedProfileSum testedSum CoprimeEndpoint.cutoff
  simp only [sum_div,weight_cast]
  apply sum_congr rfl
  intros
  ring

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
    testedSum x F - (∫ t in 1..x, F t * (5*c*(Real.log t)^4/t : ℝ)) =
      F x*((summatory x-c*(Real.log x)^5:ℝ):ℂ) -
      ∫ t in 1..x, F' t*((summatory t-c*(Real.log t)^5:ℝ):ℂ) := by
  have hF : ContinuousOn F (Set.Icc 1 x) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hlog : ContinuousOn Real.log (Set.Icc (1:ℝ) x) :=
    continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hJ : ContinuousOn (fun t => ((c*(Real.log t)^5:ℝ):ℂ)) (Set.Icc 1 x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (hlog.pow 5))
  have hdJ (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      HasDerivAt (fun t : ℝ => ((c*(Real.log t)^5:ℝ):ℂ)) (5*c*(Real.log t)^4/t:ℝ) t := by
    have hr : HasDerivAt (fun t : ℝ => c*(Real.log t)^5) (5*c*(Real.log t)^4/t) t := by
      convert! ((Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).pow 5).const_mul c using 1
      norm_num
      ring
    exact hr.ofReal_comp
  have hJ' : ContinuousOn (fun t => (5*c*(Real.log t)^4/t:ℝ)) (Set.Icc 1 x) :=
    (continuousOn_const.mul (hlog.pow 4)).div continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hi₁ : IntervalIntegrable (fun t => F t*(5*c*(Real.log t)^4/t:ℝ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((hF.mul (Complex.continuous_ofReal.comp_continuousOn hJ')).integrableOn_compact isCompact_Icc)
  have hi₂ : IntervalIntegrable (fun t => F' t*((c*(Real.log t)^5:ℝ):ℂ)) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ((hc.mul hJ).integrableOn_compact isCompact_Icc)
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hd t (by simpa only [Set.uIcc_of_le hx] using ht)).mul
      (hdJ t (by simpa only [Set.uIcc_of_le hx] using ht))) (hi₂.add hi₁)
  rw [intervalIntegral.integral_add hi₂ hi₁] at hp
  change (∫ t in 1..x, F' t*((c*(Real.log t)^5:ℝ):ℂ)) +
    (∫ t in 1..x, F t*(5*c*(Real.log t)^4/t:ℝ)) =
    F x*((c*(Real.log x)^5:ℝ):ℂ)-F 1*((c*(Real.log 1)^5:ℝ):ℂ) at hp
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
    (hE : ∀ t ∈ Set.Icc 1 x, |summatory t-c*(Real.log t)^5| ≤ E) :
    ‖testedSum x F - (∫ t in 1..x, F t*(5*c*(Real.log t)^4/t:ℝ))‖ ≤
      E*(‖F x‖+∫ t in 1..x, ‖F' t‖) := by
  have hlog : ContinuousOn (fun t => ((c*(Real.log t)^5:ℝ):ℂ)) (Set.Icc (1:ℝ) x) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      ((continuousOn_id.log (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).pow 5))
  have hisum : IntegrableOn (fun t => F' t*(summatory t:ℂ)) (Set.Icc 1 x) := by
    simpa only [complex_summatory] using integrableOn_mul_sum_Icc (m:=0)
      (fun n => (weight n:ℂ)) (by norm_num : (0:ℝ)≤1) (hc.integrableOn_compact isCompact_Icc)
  have hir : IntervalIntegrable (fun t => F' t*((summatory t-c*(Real.log t)^5:ℝ):ℂ)) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    have hsub : IntegrableOn (fun t => F' t*(summatory t:ℂ)-F' t*((c*(Real.log t)^5:ℝ):ℂ))
        (Set.Icc 1 x) := hisum.sub ((hc.mul hlog).integrableOn_compact isCompact_Icc)
    simpa only [Complex.ofReal_sub,mul_sub] using hsub
  have hin : IntervalIntegrable (fun t => ‖F' t‖*E) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      ((hc.norm.mul_const E).integrableOn_compact isCompact_Icc)
  rw [weighted_error_identity x c hx F F' hd hc]
  apply (norm_sub_le _ _).trans
  have hb (t : ℝ) (ht : t ∈ Set.Icc 1 x) : ‖((summatory t-c*(Real.log t)^5:ℝ):ℂ)‖ ≤ E := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hE t ht
  have hend := mul_le_mul_of_nonneg_left (hb x ⟨hx,le_rfl⟩) (norm_nonneg (F x))
  have hint : ‖∫ t in 1..x, F' t*((summatory t-c*(Real.log t)^5:ℝ):ℂ)‖ ≤
      (∫ t in 1..x, ‖F' t‖)*E := by
    rw [← intervalIntegral.integral_mul_const]
    apply (intervalIntegral.norm_integral_le_integral_norm hx).trans
    apply intervalIntegral.integral_mono_on hx hir.norm hin
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
  rw [norm_mul]
  nlinarith [hend,hint]

#print axioms primeMoment_real
#print axioms weight_cast
#print axioms weight_nonneg
#print axioms weight_zero
#print axioms weight_bound
#print axioms complex_summatory
#print axioms markedProfileSum_eq
#print axioms abel_identity
#print axioms weighted_error_identity
#print axioms weighted_error_bound
end XiPrime8845.FengMarkedAbel

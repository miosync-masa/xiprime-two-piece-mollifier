import PRZZZeroCoupled
import PRZZDualError
import PRZZDiagonalMass

/-! The genuine Gamma-minus-power discrepancy gains 1/T. The contour
correction mass is supplied by the proved diagonal arithmetic estimate;
no estimate for the original nonzero Fourier remainder is asserted. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroGammaBound
open PRZZZeroCross PRZZCoupledAFE
set_option maxHeartbeats 6000000

theorem multiplier_difference (a b : ℂ) (T t : ℝ)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) (hT : 2 ≤ T) (ht : T ≤ t) :
    ‖PRZZAFEDual.dualMultiplier a b t-((t/(2*Real.pi):ℝ):ℂ)^(-(a+b))‖ ≤
      ‖((t/(2*Real.pi):ℝ):ℂ)^(-(a+b))‖*(7/T)*Real.exp (7/T) := by
  have hs : ‖-(a+b)‖ ≤ 1/8 := by
    rw [norm_neg]; exact (norm_add_le _ _).trans (by linarith)
  have hi := (Complex.abs_im_le_norm (-(a+b))).trans hs
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (-(a+b))).trans hs)).1
  have hh := PRZZGammaMain.ratio_relative_bound_strip T t a b (-(a+b))
    hT ht (by linarith) (by linarith) (by linarith) hre
  have hc : 2*‖-(a+b)‖*(26+‖-(a+b)‖)/T ≤ 7/T := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [norm_nonneg (-(a+b))]
  rw [PRZZDualError.multiplier_ratio]
  exact hh.trans (by gcongr)

theorem scaled_power_cap (S T t : ℝ) (A B : ℂ) (hS : 0 ≤ S)
    (hT : 1 < T) (ht : 2*Real.pi ≤ t) (htT : t/(2*Real.pi) ≤ T)
    (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) :
    ‖((t/(2*Real.pi):ℝ):ℂ)^((A+B)/(Real.log T:ℂ))‖ ≤ Real.exp (2*S) := by
  have hq : 1 ≤ t/(2*Real.pi) := (le_div_iff₀ (by positivity)).mpr (by simpa using ht)
  have hq0 : 0 < t/(2*Real.pi) := by linarith
  have h := PRZZDualError.dilation_cap S T (t/(2*Real.pi)) A B hS hT hq htT hA hB
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne'),
    ← Complex.ofReal_log hq0.le]
  simpa only [mul_comm] using h

theorem multiplier_scaled_difference (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ t ∈ Icc T (2*T),
      ‖PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
        ((t/(2*Real.pi):ℝ):ℂ)^(-((A+B)/(Real.log T:ℂ)))‖ ≤
          (7*Real.exp (2*S+7))/T := by
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2*Real.pi),eventually_ge_atTop (2:ℝ)] with T hsmall hpi hT
  intro A B hA hB t ht
  have hp := scaled_power_cap S T t (-A) (-B) hS (by linarith) (hpi.trans ht.1)
    (by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [ht.2,Real.pi_gt_three])
    (by simpa using hA) (by simpa using hB)
  have hh := multiplier_difference _ _ T t (hsmall.2 A hA) (hsmall.2 B hB) hT ht.1
  have he : -A+-B = -(A+B) := by ring
  rw [he,neg_div] at hp
  rw [← add_div] at hh
  calc
    _ ≤ Real.exp (2*S)*(7/T)*Real.exp 7 := by
      apply hh.trans
      gcongr
      exact (div_le_iff₀ (by linarith : 0 < T)).mpr (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

/-- Both actual finite arithmetic correction sums, with no mass premise. -/
theorem correction_scaled_bound (js : List ℕ) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T t : ℝ) (A B : ℂ),
      1 ≤ N → 1 < T → (N:ℝ) ≤ T → T ≤ t →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ‖correction N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
      C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
        (1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
  obtain ⟨C,hC,h⟩ := PRZZDiagonalAssembly.assembled_error
  obtain ⟨D,hD,hm⟩ := PRZZDiagonalMass.actual_mass_with_caps js 1 1 S
    (by norm_num) (by norm_num) hS
  refine ⟨C*D,by positivity,?_⟩
  intro N T t A B hN hT hNT ht hA hB hsep hn
  have hL : 0 < Real.log T := Real.log_pos hT
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hLc
  have hn' : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/8 := by rwa [← add_div]
  have ha : |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    gcongr
  have hb : |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
    apply (abs_re_le_norm _).trans
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    gcongr
  have hm' := hm (fun _ => 1) (fun _ => 1) (by simp) (by simp)
    N T _ _ hN hT hNT ha hb
  have hh := h N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun _ => 1) (fun _ => 1) _ _ T t hs hn' (by linarith) ht
  rw [← correction_eq N _ _ _ hs hn' t (lt_of_lt_of_le (by linarith) ht)] at hh
  have he : 16/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2 =
      16*(Real.log T)^2/‖A+B‖^2 := by
    rw [← add_div,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  calc
    _ ≤ C*(1+16*(Real.log T)^2/r^2)*
      (D*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*(1+Real.log N)^(2*PRZZGCoefficient.degree js+2)) := by
      apply hh.trans
      gcongr
      unfold PRZZDiagonalAssembly.errorMass
      positivity
    _ = _ := by ring

/-- Full coefficient sums are evaluated before the 1/T Gamma gain is
spent. The fixed left contour yields N^(1/4) T^(-9/8), explicitly. -/
theorem defect_scaled_bound (js : List ℕ) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T → ∀ t ∈ Icc T (2*T),
      ‖gammaDefect N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (1+Real.log N)^(2*PRZZGCoefficient.degree js+2) := by
  obtain ⟨D,hD,hc⟩ := correction_scaled_bound js S r hS hr
  refine ⟨7*Real.exp (2*S+7)*D*(1+Real.exp (2*S)),by positivity,?_⟩
  filter_upwards [multiplier_scaled_difference S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2*Real.pi),eventually_ge_atTop (2:ℝ)] with T hm hsmall hpi hT
  intro A B hA hB hsep N hN hNT t ht
  have hT1 : 1 < T := by linarith
  have hsmallSum : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [add_div]
    exact (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  have hcd := hc N T t A B hN hT1 hNT ht.1 hA hB hsep hsmallSum
  have hcr := hc N T t (-B) (-A) hN hT1 hNT ht.1
    (by simpa using hB) (by simpa using hA)
    (by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep)
    (by simpa only [show -B+-A = -(A+B) by ring,neg_div,norm_neg] using hsmallSum)
  simp only [neg_div] at hcr
  have hp := scaled_power_cap S T t A B hS hT1 (hpi.trans ht.1)
    (by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [ht.2,Real.pi_gt_three]) hA hB
  have hmul := hm A B hA hB t ht
  rw [add_div] at hmul hp
  let V := D*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(1/8:ℝ))*
    (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)
  have hsub : ‖correction N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t-
      ((t/(2*Real.pi):ℝ):ℂ)^(A/(Real.log T:ℂ)+B/(Real.log T:ℂ))*
      correction N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ V+Real.exp (2*S)*V := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add hcr (mul_le_mul hp hcd (norm_nonneg _) (by positivity))
  unfold gammaDefect
  rw [norm_mul]
  have hh := mul_le_mul hmul hsub
    (norm_nonneg _) (by positivity : 0 ≤ (7*Real.exp (2*S+7))/T)
  apply hh.trans_eq
  rw [show -(9/8:ℝ) = -(1/8:ℝ)-1 by norm_num,Real.rpow_sub (by linarith : 0 < T)]
  norm_num only [Real.rpow_one]
  dsimp [V]
  ring

theorem defect_time_bound (js : List ℕ) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T → ∀ phi : ℝ → ℂ, Continuous phi →
      ‖∫ t in Icc T (2*T), phi t*gammaDefect N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
            (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := defect_scaled_bound js S r hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB hsep N hN hNT phi hp
  let E := C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
    (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)
  have hi : IntegrableOn (fun t : ℝ => E*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hp.norm).integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h A B hA hB hsep N hN hNT t ht)
      (norm_nonneg _)).trans_eq (by dsimp [E]; ring)

#print axioms defect_scaled_bound
#print axioms defect_time_bound
#print axioms multiplier_difference
#print axioms scaled_power_cap
#print axioms multiplier_scaled_difference
#print axioms correction_scaled_bound
end XiPrime8845.PRZZZeroGammaBound

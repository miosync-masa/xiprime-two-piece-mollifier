import ShiftWeights

/-! Explicit real derivatives and coefficient bounds for shifted profiles. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.WeightDerivatives
open ShiftWeights

def first (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  -A * weight A u θ P t - (θ : ℂ)⁻¹ * weight A u θ P.derivative t

def second (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  -A * first A u θ P t - (θ : ℂ)⁻¹ * first A u θ P.derivative t

theorem weight_hasDerivAt (A : ℂ) (u θ t : ℝ) (P : Polynomial ℂ) :
    HasDerivAt (weight A u θ P) (first A u θ P t) t := by
  have hp := (P.hasDerivAt (((u : ℂ) - (t : ℂ)) / θ)).comp (t : ℂ)
    (((hasDerivAt_id (t : ℂ)).const_sub (u : ℂ)).div_const (θ : ℂ))
  have he := (((hasDerivAt_id (t : ℂ)).const_mul (-A)).cexp).mul hp
  convert! he.comp_ofReal using 1
  all_goals first
    | (funext y; simp [weight, Complex.ofReal_div, Complex.ofReal_sub])
    | (simp [weight, first, Complex.ofReal_div, Complex.ofReal_sub]; ring)

theorem first_hasDerivAt (A : ℂ) (u θ t : ℝ) (P : Polynomial ℂ) :
    HasDerivAt (first A u θ P) (second A u θ P t) t := by
  exact ((weight_hasDerivAt A u θ t P).const_mul (-A)).sub
    ((weight_hasDerivAt A u θ t P.derivative).const_mul (θ : ℂ)⁻¹)

theorem second_continuous (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) :
    Continuous (second A u θ P) := by
  unfold second first
  exact ((weight_smooth A u θ P).continuous.const_mul (-A) |>.sub
    ((weight_smooth A u θ P.derivative).continuous.const_mul (θ : ℂ)⁻¹)).const_mul (-A) |>.sub
    (((weight_smooth A u θ P.derivative).continuous.const_mul (-A) |>.sub
    ((weight_smooth A u θ P.derivative.derivative).continuous.const_mul (θ : ℂ)⁻¹)).const_mul (θ : ℂ)⁻¹)

def polyCap (P : Polynomial ℂ) (V : ℝ) : ℝ :=
  ∑ d ∈ P.support, ‖P.coeff d‖ * V^d

theorem polyCap_nonneg (P : Polynomial ℂ) (V : ℝ) (hV : 0 ≤ V) :
    0 ≤ polyCap P V := by unfold polyCap; positivity

theorem eval_bound (P : Polynomial ℂ) (z : ℂ) (V : ℝ) (hz : ‖z‖ ≤ V) :
    ‖P.eval z‖ ≤ polyCap P V := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz d) (norm_nonneg _)

def firstCap (P : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  C * (Real.exp (C*U) * polyCap P (U/θ)) +
    |θ⁻¹| * (Real.exp (C*U) * polyCap P.derivative (U/θ))

def secondCap (P : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  C * firstCap P θ C U + |θ⁻¹| * firstCap P.derivative θ C U

theorem firstCap_nonneg (P : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) : 0 ≤ firstCap P θ C U := by
  unfold firstCap
  exact add_nonneg (mul_nonneg hC (mul_nonneg (Real.exp_pos _).le
    (polyCap_nonneg _ _ (div_nonneg hU hθ.le))))
    (mul_nonneg (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le
    (polyCap_nonneg _ _ (div_nonneg hU hθ.le))))

theorem secondCap_nonneg (P : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) : 0 ≤ secondCap P θ C U :=
  add_nonneg (mul_nonneg hC (firstCap_nonneg _ _ _ _ hθ hC hU))
    (mul_nonneg (abs_nonneg _) (firstCap_nonneg _ _ _ _ hθ hC hU))

theorem weight_interval_bound (A : ℂ) (u θ t C U : ℝ) (P : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ≤ U) (ht : t ∈ Set.Icc 0 u) :
    ‖weight A u θ P t‖ ≤ Real.exp (C*U) * polyCap P (U/θ) := by
  apply weight_bound A u θ t C U _ P hA
    (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hu)
  apply eval_bound
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ht.2) hθ.le)]
  exact div_le_div_of_nonneg_right (by linarith [ht.1]) hθ.le

theorem first_bound (A : ℂ) (u θ t C U : ℝ) (P : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ≤ U) (ht : t ∈ Set.Icc 0 u) :
    ‖first A u θ P t‖ ≤ firstCap P θ C U := by
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  apply add_le_add
  · exact mul_le_mul hA (weight_interval_bound A u θ t C U P hθ hA hu ht)
      (norm_nonneg _) ((norm_nonneg _).trans hA)
  · simpa only [abs_inv] using mul_le_mul_of_nonneg_left
      (weight_interval_bound A u θ t C U P.derivative hθ hA hu ht) (abs_nonneg θ⁻¹)

theorem second_bound (A : ℂ) (u θ t C U : ℝ) (P : Polynomial ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ≤ U) (ht : t ∈ Set.Icc 0 u) :
    ‖second A u θ P t‖ ≤ secondCap P θ C U := by
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  apply add_le_add
  · exact mul_le_mul hA (first_bound A u θ t C U P hθ hA hu ht)
      (norm_nonneg _) ((norm_nonneg _).trans hA)
  · simpa only [abs_inv] using mul_le_mul_of_nonneg_left
      (first_bound A u θ t C U P.derivative hθ hA hu ht) (abs_nonneg θ⁻¹)

theorem first_zero (A : ℂ) (u θ : ℝ) (P : Polynomial ℂ) :
    -first A u θ P 0 = A * P.eval ((u/θ : ℝ) : ℂ) +
      P.derivative.eval ((u/θ : ℝ) : ℂ) / θ := by
  simp [first, weight]
  ring

#print axioms weight_hasDerivAt
#print axioms first_hasDerivAt
#print axioms second_continuous
#print axioms eval_bound
#print axioms first_bound
#print axioms second_bound
#print axioms first_zero
end XiPrime8845.WeightDerivatives

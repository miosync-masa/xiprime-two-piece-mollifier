import PRZZReplacementHeight

/-! Local product scales in the actual V-W replacement. Constants precede
the scale and finite index set; zero coefficients need no scale premise.
This does not claim that all AFE terms have product comparable to height. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory Set
namespace XiPrime8845.PRZZLocalReplacement
open PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def error (a b : ℂ) (x t : ℝ) : ℂ :=
  PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))

/-- Keep the product scale instead of summing a global x^-2 majorant. -/
theorem local_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t R x : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < R → R ≤ x →
    ‖error a b x t‖ ≤ C*(1+16/‖a+b‖^2)*T/R^2 := by
  obtain ⟨C,hC,h⟩ := PRZZKernelUniform.difference_uniform
  refine ⟨2*C,by positivity,?_⟩
  intro a b ha hb hs T t R x hT hT' ht ht2 hR hx
  have hx0 : 0 < x := hR.trans_le hx
  have hh := h a b ha hb hs T t x hT hT' ht ht2 hx0
  change ‖error a b x t‖ ≤ C*x^(-2:ℝ)*(1+16/‖a+b‖^2)*
    PRZZReplacementIntegral.cost T t at hh
  have hp : x^(-2:ℝ) ≤ 1/R^2 := by
    rw [Real.rpow_neg hx0.le,Real.rpow_two,inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity : 0 < R^2)
      (by nlinarith : R^2 ≤ x^2)
  have hc := PRZZReplacementHeight.cost_upper T t hT' ht ht2
  have hc0 : 0 ≤ PRZZReplacementIntegral.cost T t := by
    unfold PRZZReplacementIntegral.cost
    positivity
  apply hh.trans
  calc
    _ ≤ C*(1/R^2)*(1+16/‖a+b‖^2)*(2*T) := by gcongr
    _ = _ := by ring

/-- Any retained finite domain is allowed, including both sharp AFE cutoffs.
The exact coefficient mass is retained; no extra counting factor occurs. -/
theorem finite_bound {ι : Type*} : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < R →
    ∀ (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ),
    (∀ i ∈ s, c i ≠ 0 → R ≤ x i) →
    ‖∑ i ∈ s, c i*error a b (x i) t‖ ≤
      (C*(1+16/‖a+b‖^2)*T/R^2)*(∑ i ∈ s, ‖c i‖) := by
  obtain ⟨C,hC,h⟩ := local_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t R hT hT' ht ht2 hR s c x hx
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  by_cases hc : c i = 0
  · simp [hc]
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (h a b ha hb hs T t R (x i) hT hT' ht ht2 hR (hx i hi hc))
      (norm_nonneg (c i))).trans_eq (by ring)

/-- At product scale R=lambda*T the explicit loss becomes 1/T.
This is conditional on support scale, not a claim about small products. -/
theorem height_scale_bound {ι : Type*} : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t lam : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < lam →
    ∀ (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ),
    (∀ i ∈ s, c i ≠ 0 → lam*T ≤ x i) →
    ‖∑ i ∈ s, c i*error a b (x i) t‖ ≤
      (C*(1+16/‖a+b‖^2)/(lam^2*T))*(∑ i ∈ s, ‖c i‖) := by
  obtain ⟨C,hC,h⟩ := finite_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t lam hT hT' ht ht2 hlam s c x hx
  have hT0 : 0 < T := by linarith
  have hh := h a b ha hb hs T t (lam*T) hT hT' ht ht2 (by positivity) s c x hx
  convert hh using 1 <;> field_simp <;> ring

/-- A nonzero scaled cutoff supplies the local scale, not an extra
assumption that every point in the original finite domain is nonzero. -/
theorem cutoff_scale (F : ℝ → ℂ) (hs : Function.support F ⊆ Icc (1:ℝ) 2)
    (R x : ℝ) (hR : 0 < R) (hf : F (x/R) ≠ 0) : R ≤ x := by
  have hh := (hs hf).1
  simpa using (le_div_iff₀ hR).mp hh

/-- The support premise is supplied by the actual cutoff. Both sharp
truncations can be retained in s; zeros outside the local scale disappear. -/
theorem cutoff_finite_bound {ι : Type*} : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < R →
    ∀ (F : ℝ → ℂ), Function.support F ⊆ Icc (1:ℝ) 2 →
    ∀ (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ),
    ‖∑ i ∈ s, (c i*F (x i/R))*error a b (x i) t‖ ≤
      (C*(1+16/‖a+b‖^2)*T/R^2)*(∑ i ∈ s, ‖c i*F (x i/R)‖) := by
  obtain ⟨C,hC,h⟩ := finite_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t R hT hT' ht ht2 hR F hF s c x
  apply h a b ha hb hs T t R hT hT' ht ht2 hR s _ x
  intro i hi hci
  exact cutoff_scale F hF R (x i) hR (mul_ne_zero_iff.mp hci).2

/-- Weighted time integration with the local product scale and the exact
finite coefficient mass still outside the integral. -/
theorem cutoff_time_bound {ι : Type*} : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → 0 < R →
    ∀ (F : ℝ → ℂ), Function.support F ⊆ Icc (1:ℝ) 2 →
    ∀ (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ) (phi : ℝ → ℂ), Continuous phi →
    ‖∫ t in Icc T (2*T), phi t*∑ i ∈ s, (c i*F (x i/R))*error a b (x i) t‖ ≤
      (C*(1+16/‖a+b‖^2)*T/R^2)*(∑ i ∈ s, ‖c i*F (x i/R)‖)*
        (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := cutoff_finite_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T R hT hT' hR F hF s c x phi hphi
  rw [← integral_const_mul]
  have hi : Continuous (fun t : ℝ =>
      (C*(1+16/‖a+b‖^2)*T/R^2)*(∑ i ∈ s, ‖c i*F (x i/R)‖)*‖phi t‖) := by
    fun_prop
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (h a b ha hb hs T t R hT hT' ht.1 ht.2 hR F hF s c x)
    (norm_nonneg _)).trans_eq (by ring)

#print axioms local_bound
#print axioms finite_bound
#print axioms height_scale_bound
#print axioms cutoff_scale
#print axioms cutoff_finite_bound
#print axioms cutoff_time_bound
end XiPrime8845.PRZZLocalReplacement

import PRZZGCoefficient
import PRZZCutoffPhase

/-! A supplied arithmetic mass for the actual convolution coefficients.
This cardinality bound is deliberately not the optimized PRZZ error budget.
The finite index set may retain all coprimality and product restrictions. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZArithmeticMass
open PRZZGCoefficient

theorem pair_bound (js : List ℕ) (N m n : ℕ) (hN : 1 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖(coefficient js m : ℂ) * star (coefficient js n : ℂ)‖ ≤
      (Real.log N)^(2*degree js) := by
  rw [norm_mul, norm_star]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hh := mul_le_mul (coefficient_bound js N hN m hm hmN)
    (coefficient_bound js N hN n hn hnN) (abs_nonneg _) (pow_nonneg hlog _)
  exact hh.trans_eq (by rw [← pow_add]; congr 1; omega)

/-- The coefficient mass itself is bounded; no coefficient envelope premise
is supplied. Repeated labels in the finite family are counted separately. -/
theorem mass_bound {ι : Type*} (s : Finset ι) (js : List ℕ) (N : ℕ)
    (m n : ι → ℕ) (hN : 1 ≤ N)
    (hm : ∀ i ∈ s, 1 ≤ m i ∧ m i ≤ N)
    (hn : ∀ i ∈ s, 1 ≤ n i ∧ n i ≤ N) :
    (∑ i ∈ s, ‖(coefficient js (m i) : ℂ) * star (coefficient js (n i) : ℂ)‖) ≤
      (s.card : ℝ)*(Real.log N)^(2*degree js) := by
  calc
    _ ≤ ∑ _i ∈ s, (Real.log N)^(2*degree js) := Finset.sum_le_sum
      (fun i hi => pair_bound js N (m i) (n i) hN (hm i hi).1 (hm i hi).2
        (hn i hi).1 (hn i hi).2)
    _ = _ := by simp

/-- Additional analytic factors can be inserted without losing any masks
in the original finite index set. Their envelope is still explicit. -/
theorem weighted_mass_bound {ι : Type*} (s : Finset ι) (js : List ℕ) (N : ℕ)
    (m n : ι → ℕ) (u : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (hN : 1 ≤ N)
    (hm : ∀ i ∈ s, 1 ≤ m i ∧ m i ≤ N)
    (hn : ∀ i ∈ s, 1 ≤ n i ∧ n i ≤ N)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ B) :
    (∑ i ∈ s, ‖((coefficient js (m i) : ℂ) * star (coefficient js (n i) : ℂ))*u i‖) ≤
      (s.card : ℝ)*(Real.log N)^(2*degree js)*B := by
  calc
    _ ≤ ∑ i ∈ s, ‖(coefficient js (m i) : ℂ)*star (coefficient js (n i) : ℂ)‖*B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hu i hi) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖(coefficient js (m i) : ℂ)*star (coefficient js (n i) : ℂ)‖)*B := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mass_bound s js N m n hN hm hn) hB

/-- Insert the actual arithmetic mass into the small-ratio phase budget.
Only the remaining analytic envelope B and the ratio bound are premises. -/
theorem phase_mass_bound {ι : Type*} (s : Finset ι) (js : List ℕ) (N : ℕ)
    (m n : ι → ℕ) (u : ι → ℂ) (v : ι → ℝ) (B P : ℝ)
    (hB : 0 ≤ B) (hP : 0 < P) (hN : 1 ≤ N)
    (hm : ∀ i ∈ s, 1 ≤ m i ∧ m i ≤ N)
    (hn : ∀ i ∈ s, 1 ≤ n i ∧ n i ≤ N)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ B) (hv : ∀ i ∈ s, |v i| ≤ 4/P) :
    (∑ i ∈ s, ‖((coefficient js (m i) : ℂ)*star (coefficient js (n i) : ℂ))*u i‖*(v i)^2) ≤
      (16/P^2)*((s.card : ℝ)*(Real.log N)^(2*degree js)*B) := by
  exact (PRZZCutoffPhase.mass_bound s _ v P hP hv).trans
    (mul_le_mul_of_nonneg_left (weighted_mass_bound s js N m n u B hB hN hm hn hu)
      (by positivity))

#print axioms phase_mass_bound
#print axioms pair_bound
#print axioms mass_bound
#print axioms weighted_mass_bound
end XiPrime8845.PRZZArithmeticMass

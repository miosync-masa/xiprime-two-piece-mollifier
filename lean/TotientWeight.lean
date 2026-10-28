import SupportTail

/-! Exact identification of the zero-shift Euler weight.
The harmonic asymptotic for mu(n)^2/phi(n) is not asserted here. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.TotientWeight
open SupportTail

theorem totient_product_real (g : ℕ) :
    (g.totient : ℝ) = (g : ℝ)*∏ p ∈ g.primeFactors, (1-(p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors g)
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
    Rat.cast_one, Rat.cast_inv] using h

theorem eulerMass_zero (g : ℕ) (hg : g ≠ 0) :
    eulerMass g 0 = (g : ℝ)/(g.totient : ℝ) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have ht0 : (g.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_eq_zero.not.mpr hg)
  have he : eulerMass g 0 = (∏ p ∈ g.primeFactors, (1-(p : ℝ)⁻¹))⁻¹ := by
    simp [eulerMass, Finset.prod_inv_distrib, Real.rpow_neg_one]
  rw [he, totient_product_real]
  field_simp

/-- The two Euler factors really yield mu^2/phi, not mu^2/g. -/
theorem zero_shift_weight (g : ℕ) (hg : g ≠ 0) :
    (μ g : ℝ)^2 * (g.totient : ℝ)/(g : ℝ)^2 * eulerMass g 0 * eulerMass g 0 =
      (μ g : ℝ)^2/(g.totient : ℝ) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have ht0 : (g.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_eq_zero.not.mpr hg)
  rw [eulerMass_zero g hg]
  field_simp

#print axioms totient_product_real
#print axioms eulerMass_zero
#print axioms zero_shift_weight
end XiPrime8845.TotientWeight

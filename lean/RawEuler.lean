import FengMixedShift

/-! Raw Euler factorization for every nonzero integer, including prime powers.
No cancellation by a Mobius coefficient is used. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.RawEuler
open ElementaryGcd ShiftedTotient
set_option maxHeartbeats 1000000

theorem prime_pow_succ (s : ℂ) (p k : ℕ) (hp : p.Prime) :
    generalizedTotient s (p^(k+1)) = ((p^(k+1):ℕ):ℂ)^s-((p^k:ℕ):ℂ)^s := by
  have h1 := sum_generalizedTotient s (p^(k+1)) (pow_pos hp.pos _)
  have h0 := sum_generalizedTotient s (p^k) (pow_pos hp.pos _)
  rw [Nat.sum_divisors_prime_pow hp, sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h0
  rw [h0] at h1
  linear_combination h1

theorem prime_pow_factor (s : ℂ) (p k : ℕ) (hp : p.Prime) :
    generalizedTotient s (p^(k+1)) = ((p^(k+1):ℕ):ℂ)^s*(1-(p:ℂ)^(-s)) := by
  rw [prime_pow_succ s p k hp, pow_succ, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
  have hn : (p:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne_zero))
  field_simp

theorem generalizedTotient_product (s : ℂ) (g : ℕ) (hg : g ≠ 0) :
    generalizedTotient s g = (g:ℂ)^s * ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-s)) := by
  have hf := (phiAF_multiplicative s).multiplicative_factorization (phiAF s) hg
  have hp := (powerAF_multiplicative s).multiplicative_factorization (powerAF s) hg
  simp only [Finsupp.prod, Nat.support_factorization] at hf hp
  rw [phiAF_eq] at hf
  rw [hf]
  have he : ∀ p ∈ g.primeFactors, phiAF s (p^g.factorization p) =
      powerAF s (p^g.factorization p)*(1-(p:ℂ)^(-s)) := by
    intro p hpg
    have hprime := Nat.prime_of_mem_primeFactors hpg
    have hk : g.factorization p ≠ 0 := by
      exact Finsupp.mem_support_iff.mp (show p ∈ g.factorization.support from hpg)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [hk, phiAF_eq]
    simpa [powerAF, hprime.ne_zero] using prime_pow_factor s p k hprime
  rw [prod_congr rfl he]
  rw [prod_mul_distrib, ← hp]
  simp [powerAF, hg]

theorem rawWeight_product (a b : ℂ) (g : ℕ) (hg : g ≠ 0) :
    FengMixedShift.rawWeight a b g = (1/(g:ℂ))*
      ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-(1+a+b))) := by
  unfold FengMixedShift.rawWeight
  rw [generalizedTotient_product _ g hg, show (2:ℂ)+a+b=1+(1+a+b) by ring,
    Complex.cpow_add _ (1+a+b) (by exact_mod_cast hg), Complex.cpow_one]
  have hn : (g:ℂ)^(1+a+b) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hg))
  field_simp

theorem rawWeight_factor (L : ℝ) (g : ℕ) (hg : g ≠ 0) (A B : ℂ) :
    FengMixedShift.rawWeight (A/L) (B/L) g =
      FengSharedLimit.zeroWeight g * BareEuler.ratio A B L g := by
  rw [← FengMixedShift.rawWeight_zero, rawWeight_product _ _ g hg,
    rawWeight_product _ _ g hg, mul_assoc, BareEuler.ratio, ← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  simpa only [add_zero, Complex.cpow_neg_one] using
    BareEuler.prime_factor A B L p (Nat.prime_of_mem_primeFactors hp)

#print axioms prime_pow_succ
#print axioms prime_pow_factor
#print axioms generalizedTotient_product
#print axioms rawWeight_product
#print axioms rawWeight_factor
end XiPrime8845.RawEuler

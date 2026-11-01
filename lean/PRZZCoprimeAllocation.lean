import PRZZGCoefficient

/-! Local arithmetic allocation used in separating the original coefficient.
A weighted von Mangoldt factor cannot straddle coprime arguments. This is
the local support identity, not yet the full convolution subset expansion. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction
namespace XiPrime8845.PRZZCoprimeAllocation
open PRZZLambda
set_option maxHeartbeats 1000000

theorem primePower_coprime_split (m n : ℕ) (hc : m.Coprime n)
    (hp : IsPrimePow (m*n)) : m = 1 ∨ n = 1 := by
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff (m*n)).mp hp
  have hm : m ∣ p^k := he.symm ▸ Nat.dvd_mul_right m n
  have hn : n ∣ p^k := he.symm ▸ Nat.dvd_mul_left n m
  obtain ⟨i,hi,hmi⟩ := (Nat.dvd_prime_pow hp).mp hm
  obtain ⟨j,hj,hnj⟩ := (Nat.dvd_prime_pow hp).mp hn
  by_cases hi0 : i = 0
  · left; simpa [hi0] using hmi
  by_cases hj0 : j = 0
  · right; simpa [hj0] using hnj
  have hpm : p ∣ m := by
    rw [hmi]; simpa only [pow_one] using Nat.pow_dvd_pow p (show 1 ≤ i by omega)
  have hpn : p ∣ n := by
    rw [hnj]; simpa only [pow_one] using Nat.pow_dvd_pow p (show 1 ≤ j by omega)
  exact False.elim (hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn))

theorem weightedLambda_mul_coprime (j m n : ℕ) (hc : m.Coprime n) :
    weightedLambda j (m*n) =
      weightedLambda j m*(1 : ArithmeticFunction ℝ) n+
      (1 : ArithmeticFunction ℝ) m*weightedLambda j n := by
  by_cases hm : m = 1
  · subst m; simp [weightedLambda]
  by_cases hn : n = 1
  · subst n; simp [weightedLambda]
  have hp : ¬IsPrimePow (m*n) := by
    intro h
    exact (primePower_coprime_split m n hc h).elim hm hn
  simp [weightedLambda,vonMangoldt_apply,hp,one_apply,hm,hn]

/-- Multiplication by the Mobius factor separates exactly on coprime
arguments; no absolute-value replacement is made here. -/
theorem mu_mul_coprime (m n : ℕ) (hc : m.Coprime n) :
    PRZZ.muReal (m*n) = PRZZ.muReal m*PRZZ.muReal n := by
  exact (isMultiplicative_moebius.intCast (R := ℝ)).map_mul_of_coprime hc

#print axioms primePower_coprime_split
#print axioms weightedLambda_mul_coprime
#print axioms mu_mul_coprime

/-- Exact subset allocation of the weighted prime-power factors in a
single convolution summand. The identity factors force every factor to
live on one side; repeated orders remain distinct labelled factors. -/
theorem weighted_product_allocation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (j m n : ι → ℕ) (hc : ∀ i ∈ s, (m i).Coprime (n i)) :
    (∏ i ∈ s, weightedLambda (j i) (m i*n i)) =
      ∑ t ∈ s.powerset,
        (∏ i ∈ t, weightedLambda (j i) (m i)*(1 : ArithmeticFunction ℝ) (n i))*
        (∏ i ∈ s \ t, (1 : ArithmeticFunction ℝ) (m i)*weightedLambda (j i) (n i)) := by
  calc
    _ = ∏ i ∈ s, (weightedLambda (j i) (m i)*(1 : ArithmeticFunction ℝ) (n i)+
        (1 : ArithmeticFunction ℝ) (m i)*weightedLambda (j i) (n i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact weightedLambda_mul_coprime (j i) (m i) (n i) (hc i hi)
    _ = _ := Finset.prod_add _ _ _

#print axioms weighted_product_allocation
end XiPrime8845.PRZZCoprimeAllocation

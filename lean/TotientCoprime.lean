import TotientHarmonic

/-! Exact removal of prime coprimality for the squarefree totient weight.
The bounds are uniform in the excluded primes; no restricted asymptotic is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction
namespace XiPrime8845.TotientCoprime
open TotientConvolution
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def total (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, weight n
def restricted (N q : ℕ) : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q), weight n

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  change 0 ≤ (μ n : ℝ)^2 / n.totient
  positivity

theorem total_eq (x : ℝ) : total ⌊x⌋₊ = TotientHarmonic.summatory x := by
  simp only [total,TotientHarmonic.summatory,weight,coe_mk]
  congr 1

theorem restricted_nonneg (N q : ℕ) : 0 ≤ restricted N q :=
  sum_nonneg (fun n _ => weight_nonneg n)

theorem restricted_le_total (N q : ℕ) : restricted N q ≤ total N :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => weight_nonneg n)

theorem weight_prime_mul (p n : ℕ) (hp : p.Prime) :
    weight (p*n) = if n.Coprime p then weight n / (p-1:ℝ) else 0 := by
  by_cases hc : n.Coprime p
  · rw [if_pos hc,weight_multiplicative.map_mul_of_coprime hc.symm,weight_prime p hp]
    ring
  · rw [if_neg hc]
    have hs : ¬ Squarefree (p*n) := fun h => hc (Nat.coprime_of_squarefree_mul h).symm
    simp [weight,moebius_eq_zero_of_not_squarefree hs]

theorem multiples (N p : ℕ) (hp : p.Prime) :
    (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n), weight n) =
      restricted (N/p) p / (p-1:ℝ) := by
  have h := ElementaryGcd.sum_multiples N p hp.pos (fun n => (weight n : ℂ))
  have hr : (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n), weight n) =
      ∑ n ∈ Icc 1 (N/p), weight (p*n) := by exact_mod_cast h
  rw [hr,restricted,Finset.sum_div]
  simp only [weight_prime_mul p _ hp,sum_filter]

/-- Exact identity, valid also when the prime exceeds the cutoff. -/
theorem prime_removal (N p : ℕ) (hp : p.Prime) :
    total N - restricted N p = restricted (N/p) p / (p-1:ℝ) := by
  rw [← multiples N p hp]
  unfold total restricted
  simp only [sum_filter,← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hc : n.Coprime p ↔ ¬ p ∣ n := by rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  by_cases h : p ∣ n <;> simp [hc,h]

theorem prime_exclusion_bound (N p : ℕ) (hp : p.Prime) :
    0 ≤ total N-restricted N p ∧
      total N-restricted N p ≤ total (N/p)/(p-1:ℝ) := by
  refine ⟨sub_nonneg.mpr (restricted_le_total N p),?_⟩
  rw [prime_removal N p hp]
  apply div_le_div_of_nonneg_right (restricted_le_total _ _)
  have : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  linarith

/-- Union bound: no distinctness hypothesis and no prime-dependent big-O constant. -/
theorem product_exclusion (N p q : ℕ) :
    total N-restricted N (p*q) ≤ (total N-restricted N p)+(total N-restricted N q) := by
  unfold total restricted
  simp only [sum_filter,← sum_sub_distrib,← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  simp only [Nat.coprime_mul_iff_right]
  by_cases hp : n.Coprime p
  · by_cases hq : n.Coprime q
    · rw [if_pos hp,if_pos hq,if_pos (And.intro hp hq)]
      linarith
    · rw [if_pos hp,if_neg hq,if_neg (fun h => hq h.2)]
      linarith
  · by_cases hq : n.Coprime q
    · rw [if_neg hp,if_pos hq,if_neg (fun h => hp h.1)]
      linarith
    · rw [if_neg hp,if_neg hq,if_neg (fun h => hp h.1)]
      linarith [weight_nonneg n]

theorem two_prime_exclusion_bound (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    0 ≤ total N-restricted N (p*q) ∧
      total N-restricted N (p*q) ≤ total (N/p)/(p-1:ℝ)+total (N/q)/(q-1:ℝ) :=
  ⟨sub_nonneg.mpr (restricted_le_total _ _),
    (product_exclusion N p q).trans (add_le_add
      (prime_exclusion_bound N p hp).2 (prime_exclusion_bound N q hq).2)⟩

/-- A common logarithmic majorant, including the empty natural cutoff. -/
theorem total_log_bound (N : ℕ) :
    total N ≤ Real.log (max (N:ℝ) 1)+TotientHarmonic.errorConstant := by
  by_cases hN : N = 0
  · simp [hN,total,TotientHarmonic.errorConstant_nonneg]
  have hn : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have h := (le_abs_self _).trans (TotientHarmonic.summatory_log_bound N hn)
  rw [← total_eq,Nat.floor_natCast] at h
  rw [max_eq_left hn]
  linarith

theorem total_mono {M N : ℕ} (h : M ≤ N) : total M ≤ total N :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h) (fun n _ _ => weight_nonneg n)

theorem prime_exclusion_log (N p : ℕ) (hp : p.Prime) :
    total N-restricted N p ≤
      (Real.log (max (N:ℝ) 1)+TotientHarmonic.errorConstant)/(p-1:ℝ) := by
  apply (prime_exclusion_bound N p hp).2.trans
  apply div_le_div_of_nonneg_right ((total_mono (Nat.div_le_self N p)).trans (total_log_bound N))
  have : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  linarith

theorem two_prime_exclusion_log (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    total N-restricted N (p*q) ≤
      (Real.log (max (N:ℝ) 1)+TotientHarmonic.errorConstant)*
        ((p-1:ℝ)⁻¹+(q-1:ℝ)⁻¹) := by
  have h := (product_exclusion N p q).trans (add_le_add
    (prime_exclusion_log N p hp) (prime_exclusion_log N q hq))
  simpa only [div_eq_mul_inv,mul_add] using h

#print axioms weight_nonneg
#print axioms total_eq
#print axioms restricted_nonneg
#print axioms restricted_le_total
#print axioms weight_prime_mul
#print axioms multiples
#print axioms prime_removal
#print axioms prime_exclusion_bound
#print axioms product_exclusion
#print axioms two_prime_exclusion_bound
#print axioms total_log_bound
#print axioms total_mono
#print axioms prime_exclusion_log
#print axioms two_prime_exclusion_log
end XiPrime8845.TotientCoprime

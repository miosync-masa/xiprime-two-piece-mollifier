import FengSharedTail
import Zeta23.XiPrime.Coeff.PrimeSums

/-! Uniform cost of removing primes dividing a growing modulus. All higher
prime powers are controlled by a convergent mass, not silently discarded. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengPrimeExclusion
open Zeta23.XiPrime
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def mass (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / n * Real.log n

theorem mass_nonneg (n : ℕ) : 0 ≤ mass n := by
  by_cases hn : n = 0
  · simp [hn,mass]
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))

theorem excluded_mass_bound (g : ℕ) (hg : g ≠ 0) (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ (Ioc 0 ⌊Real.exp x⌋₊).filter (fun n => ¬ n.Coprime g), mass n) ≤
      Real.log g+2*Cdef := by
  let s := (Ioc 0 ⌊Real.exp x⌋₊).filter (fun n => ¬ n.Coprime g)
  have he : (∑ n ∈ s, mass n) =
      (∑ n ∈ s.filter Nat.Prime, mass n)+(∑ n ∈ s.filter (fun n => ¬ n.Prime), mass n) :=
    (sum_filter_add_sum_filter_not s Nat.Prime mass).symm
  rw [show (Ioc 0 ⌊Real.exp x⌋₊).filter (fun n => ¬ n.Coprime g) = s from rfl,he]
  have hp : (∑ n ∈ s.filter Nat.Prime, mass n) ≤ Real.log g := by
    apply le_trans _ (FengSharedTail.prime_log_square_div_sum g hg)
    have hs : s.filter Nat.Prime ⊆ g.primeFactors := by
      intro p hp
      obtain ⟨hp,hprime⟩ := mem_filter.mp hp
      have hnc := (mem_filter.mp hp).2
      exact Nat.mem_primeFactors.mpr ⟨hprime,not_not.mp
        (fun h => hnc (hprime.coprime_iff_not_dvd.mpr h)),hg⟩
    calc
      _ = ∑ p ∈ s.filter Nat.Prime, (Real.log p)^2/(p:ℝ) := by
        apply sum_congr rfl
        intro p hp
        rw [mass,ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
        ring
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
  have hq : (∑ n ∈ s.filter (fun n => ¬ n.Prime), mass n) ≤ 2*Cdef := by
    have hh := sum_not_prime_lam_logpow_div_le 2 (by norm_num) hx
    norm_num only [Nat.sub_self,pow_zero,one_mul,show 2-1=1 by omega,pow_one] at hh
    apply le_trans _ hh
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨(mem_filter.mp hn).1,hp⟩
    · intro n _ _; exact mass_nonneg n
  linarith

theorem excluded_mass_scaled (g : ℕ) (hg : g ≠ 0) (L u U : ℝ)
    (hL : 0 < L) (hu : 0 ≤ u) (hgL : Real.log g ≤ L*U) :
    (∑ n ∈ (Ioc 0 ⌊Real.exp (L*u)⌋₊).filter (fun n => ¬ n.Coprime g), mass n)/L^2 ≤
      U/L+2*Cdef/L^2 := by
  apply (div_le_div_of_nonneg_right
    ((excluded_mass_bound g hg (L*u) (mul_nonneg hL.le hu)).trans
      (show Real.log g+2*Cdef ≤ L*U+2*Cdef by linarith)) (sq_nonneg L)).trans_eq
  field_simp

#print axioms excluded_mass_bound
#print axioms excluded_mass_scaled
end XiPrime8845.FengPrimeExclusion

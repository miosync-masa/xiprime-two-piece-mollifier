import Mathlib

/-! An elementary summability criterion from bounded finite Euler products. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.MultiplicativeSummability

theorem summable_of_local_mass (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfmul : ∀ {m n}, m.Coprime n → f (m*n) = f m*f n)
    (hf : ∀ n, 0 ≤ f n) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hs : Summable b)
    (hl : ∀ p, p.Prime → HasSum (fun k : ℕ => f (p^k)) (1+b p)) :
    Summable f := by
  apply summable_of_sum_le hf (c := Real.exp (∑' n, b n))
  intro s
  classical
  let primes := s.biUnion Nat.primeFactors
  have hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖f (p^k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using (hl p hp).summable
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf1 hfmul hlocal primes).2
  have hi := hasSum_subtype_iff_indicator.mp h
  calc
    ∑ n ∈ s, f n = ∑ n ∈ s, (Nat.factoredNumbers primes).indicator f n := by
      apply sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · subst n; simp [Set.indicator, hf0]
      apply (Set.indicator_of_mem _ f).symm
      rw [Nat.mem_factoredNumbers']
      intro p hp hpn
      exact mem_biUnion.mpr ⟨n, hn, Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0⟩⟩
    _ ≤ ∏ p ∈ primes.filter Nat.Prime, ∑' k : ℕ, f (p^k) :=
      sum_le_hasSum s (fun n _ => Set.indicator_nonneg (fun n _ => hf n) n) hi
    _ = ∏ p ∈ primes.filter Nat.Prime, (1+b p) := by
      apply prod_congr rfl
      intro p hp
      exact (hl p (mem_filter.mp hp).2).tsum_eq
    _ ≤ ∏ p ∈ primes.filter Nat.Prime, Real.exp (b p) := by
      apply prod_le_prod (fun p _ => by linarith [hb p])
      intro p hp
      simpa only [add_comm] using Real.add_one_le_exp (b p)
    _ = Real.exp (∑ p ∈ primes.filter Nat.Prime, b p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n, b n) := Real.exp_le_exp.mpr
      (Summable.sum_le_tsum _ (fun n _ => hb n) hs)

#print axioms summable_of_local_mass
end XiPrime8845.MultiplicativeSummability

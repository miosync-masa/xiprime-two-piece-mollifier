import FengMarkedArithmetic

/-! Exact global diagonal and ordered cross decomposition of the actual marked
summatory function. No scalar asymptotic is assumed in these finite identities. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction
namespace XiPrime8845.FengMarkedDecomposition
open FengMarkedProfile FengMarkedArithmetic TotientCoprime
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem prime_sum (N n : ℕ) (hn : n ∈ Icc 1 N) (f : ℕ → ℝ) :
    (∑ p ∈ n.primeFactors, f p) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, if p ∣ n then f p else 0 := by
  rw [← sum_filter]
  congr 1
  ext p
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp only [Nat.mem_primeFactors,mem_filter,mem_Icc]
  constructor
  · rintro ⟨hp,hpn,_⟩
    exact ⟨⟨⟨hp.pos,(Nat.le_of_dvd (mem_Icc.mp hn).1 hpn).trans (mem_Icc.mp hn).2⟩,hp⟩,hpn⟩
  · rintro ⟨⟨_,hp⟩,hpn⟩; exact ⟨hp,hpn,hn0⟩

theorem prime_pair_expand (N n : ℕ) (hn : n ∈ Icc 1 N) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ n.primeFactors, ∑ q ∈ n.primeFactors.erase p, f p q) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        ∑ q ∈ ((Icc 1 N).filter Nat.Prime).erase p,
          if p ∣ n ∧ q ∣ n then f p q else 0 := by
  have herase (s : Finset ℕ) (p : ℕ) (f : ℕ → ℝ) :
      (∑ q ∈ s.erase p, f q) = ∑ q ∈ s, if q ≠ p then f q else 0 := by
    rw [← filter_ne',sum_filter]
  simp_rw [herase]
  rw [prime_sum N n hn]
  apply sum_congr rfl
  intro p hp
  rw [prime_sum N n hn]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    apply sum_congr rfl
    intro q hq
    by_cases hqn : q ∣ n <;> by_cases he : q = p <;> simp [hpn,hqn,he]
  · rw [if_neg hpn]
    simp [hpn]

theorem prime_pair_swap (N : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.primeFactors, ∑ q ∈ n.primeFactors.erase p, f n p q) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        ∑ q ∈ ((Icc 1 N).filter Nat.Prime).erase p,
          ∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n), f n p q := by
  rw [sum_congr rfl (fun n hn => prime_pair_expand N n hn (f n)),sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  simp only [sum_filter]

theorem cross_reindex (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.primeFactors, ∑ q ∈ n.primeFactors.erase p,
      (Real.log p)^2*(Real.log q)^2 *
        ((μ (n/p^(n.factorization p)):ℝ)*(μ (n/q^(n.factorization q)):ℝ)/n.totient)) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        ∑ q ∈ ((Icc 1 N).filter Nat.Prime).erase p,
          (Real.log p)^2*(Real.log q)^2 *
            (restricted (N/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ))) := by
  rw [prime_pair_swap]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  rw [← mul_sum,crossAt_reindex N p q (mem_filter.mp hp).2
    (mem_filter.mp (mem_erase.mp hq).2).2 (mem_erase.mp hq).1.symm]

def diagonal (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, (Real.log p)^4 *
    ∑ a ∈ range (Nat.log p N),
      restricted (N/p^(a+1)) p / ((p^(a+1)).totient : ℝ)

def cross (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    ∑ q ∈ ((Icc 1 N).filter Nat.Prime).erase p,
      (Real.log p)^2*(Real.log q)^2 *
        (restricted (N/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ)))

/-- Exact scalar arithmetic target, with all diagonal powers and ordered pairs. -/
theorem summatory_decomposition (x : ℝ) :
    FengMarkedAbel.summatory x = diagonal ⌊x⌋₊ + cross ⌊x⌋₊ := by
  rw [diagonal,cross,← diagonal_reindex,← cross_reindex,← sum_add_distrib]
  unfold FengMarkedAbel.summatory
  have he : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  rw [he]
  apply sum_congr rfl
  intro n hn
  have h := primeMoment_square n
  rw [← FengMarkedAbel.primeMoment_real n] at h
  have hr : (primeMoment n).re^2 =
      (∑ p ∈ n.primeFactors, (Real.log p)^4*(μ (n/p^(n.factorization p)):ℝ)^2) +
      ∑ p ∈ n.primeFactors, ∑ q ∈ n.primeFactors.erase p,
        (Real.log p)^2*(Real.log q)^2 *
          ((μ (n/p^(n.factorization p)):ℝ)*(μ (n/q^(n.factorization q)):ℝ)) := by
    norm_cast at h ⊢
    simpa only [Int.cast_mul,mul_assoc] using h
  unfold FengMarkedAbel.weight
  rw [hr,add_div]
  simp only [sum_div]
  congr 1
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  ring

#print axioms prime_sum
#print axioms prime_pair_expand
#print axioms prime_pair_swap
#print axioms cross_reindex
#print axioms summatory_decomposition
end XiPrime8845.FengMarkedDecomposition

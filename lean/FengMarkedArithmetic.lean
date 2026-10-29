import FengMarkedAbel
import FengResidual
import TotientCoprime

/-! Finite arithmetic suppliers for the marked scalar asymptotic.
All prime powers are retained. These identities do not assert a limiting constant. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction
namespace XiPrime8845.FengMarkedArithmetic
open FengMarkedProfile TotientCoprime
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def diagonalAt (N p : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if p ∣ n then
    (μ (n/p^(n.factorization p)) : ℝ)^2 / n.totient else 0

theorem diagonalAt_prime_powers (N p : ℕ) (hp : p.Prime) :
    diagonalAt N p = ∑ a ∈ range (Nat.log p N),
      restricted (N/p^(a+1)) p / ((p^(a+1)).totient : ℝ) := by
  have h := FengResidual.prime_power_reindex N p hp (fun n =>
    ((if p ∣ n then (μ (n/p^(n.factorization p)) : ℝ)^2/n.totient else 0 : ℝ) : ℂ))
  have hr : diagonalAt N p = ∑ a ∈ range (Nat.log p N+1),
      ∑ m ∈ (Icc 1 (N/p^a)).filter (fun m => p.Coprime m),
        if p ∣ p^a*m then (μ ((p^a*m)/p^((p^a*m).factorization p)) : ℝ)^2 /
          (p^a*m).totient else 0 := by
    unfold diagonalAt
    exact_mod_cast h
  rw [hr,sum_range_succ']
  have hz : (∑ m ∈ (Icc 1 (N/p^0)).filter (fun m => p.Coprime m),
      if p ∣ p^0*m then (μ ((p^0*m)/p^((p^0*m).factorization p)) : ℝ)^2 /
        (p^0*m).totient else 0) = 0 := by
    apply sum_eq_zero
    intro m hm
    simp only [pow_zero,one_mul]
    exact if_neg (hp.coprime_iff_not_dvd.mp (mem_filter.mp hm).2)
  rw [hz,add_zero]
  apply sum_congr rfl
  intro a ha
  unfold restricted
  rw [sum_div]
  have he : (Icc 1 (N/p^(a+1))).filter (fun m => p.Coprime m) =
      (Icc 1 (N/p^(a+1))).filter (fun m => m.Coprime p) := by
    ext m; simp [Nat.coprime_comm]
  rw [he]
  apply sum_congr rfl
  intro m hm
  have hc := (mem_filter.mp hm).2.symm
  have hm0 : m ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hm).1).1; omega
  rw [if_pos (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m),
    FengResidual.factorization_pow_mul p (a+1) m hp hm0 hc,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos _),Nat.totient_mul (hc.pow_left _)]
  simp only [Nat.cast_mul,TotientConvolution.weight,coe_mk]
  ring

/-- The diagonal in primeMoment_square, now with the outer prime sum exposed. -/
theorem diagonal_swap (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.primeFactors,
      (Real.log p)^4*(μ (n/p^(n.factorization p)) : ℝ)^2/n.totient) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, (Real.log p)^4*diagonalAt N p := by
  have he (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ p ∈ n.primeFactors, (Real.log p)^4*(μ (n/p^(n.factorization p)) : ℝ)^2/n.totient) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        if p ∣ n then (Real.log p)^4*(μ (n/p^(n.factorization p)) : ℝ)^2/n.totient else 0 := by
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    rw [← sum_filter]
    congr 1
    ext p
    simp only [Nat.mem_primeFactors,mem_filter,mem_Icc]
    constructor
    · rintro ⟨hp,hpn,_⟩
      exact ⟨⟨⟨hp.pos,(Nat.le_of_dvd (mem_Icc.mp hn).1 hpn).trans (mem_Icc.mp hn).2⟩,hp⟩,hpn⟩
    · rintro ⟨⟨_,hp⟩,hpn⟩; exact ⟨hp,hpn,hn0⟩
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [diagonalAt,mul_sum]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

theorem diagonal_reindex (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.primeFactors,
      (Real.log p)^4*(μ (n/p^(n.factorization p)) : ℝ)^2/n.totient) =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, (Real.log p)^4 *
        ∑ a ∈ range (Nat.log p N),
          restricted (N/p^(a+1)) p / ((p^(a+1)).totient : ℝ) := by
  rw [diagonal_swap]
  apply sum_congr rfl
  intro p hp
  rw [diagonalAt_prime_powers N p (mem_filter.mp hp).2]

theorem mobius_residue_squarefree (g p : ℕ) (hg : Squarefree g)
    (hp : p.Prime) (hpg : p ∣ g) :
    μ (g/p^(g.factorization p)) = -μ g := by
  have hc := Nat.coprime_ordCompl hp hg.ne_zero
  have hm := isMultiplicative_moebius.map_mul_of_coprime hc
  have he := Nat.ordProj_mul_ordCompl_eq_self g p
  have hv := Nat.factorization_eq_one_of_squarefree hg hp hpg
  rw [hv,pow_one] at he
  rw [hv,pow_one] at hm ⊢
  rw [he,moebius_apply_prime hp] at hm
  linarith

/-- Two distinct marked residues can both be squarefree only if g is. -/
theorem squarefree_of_two_residues (g p q : ℕ) (hg : g ≠ 0) (hpq : p ≠ q)
    (hp : Squarefree (g/p^(g.factorization p)))
    (hq : Squarefree (g/q^(g.factorization q))) : Squarefree g := by
  apply Nat.squarefree_of_factorization_le_one hg
  intro r
  by_cases hr : r = p
  · subst r
    have h := hq.natFactorization_le_one p
    rw [Nat.factorization_ordCompl,Finsupp.erase_ne hpq] at h
    exact h
  · have h := hp.natFactorization_le_one r
    rw [Nat.factorization_ordCompl,Finsupp.erase_ne hr] at h
    exact h

/-- The ordered cross term is supported precisely on squarefree g.
This assertion is NOT true for the same-prime diagonal. -/
theorem cross_residue (g p q : ℕ) (hg : g ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpg : p ∣ g) (hqg : q ∣ g) :
    μ (g/p^(g.factorization p))*μ (g/q^(g.factorization q)) = (μ g)^2 := by
  by_cases hs : Squarefree g
  · rw [mobius_residue_squarefree g p hs hp hpg,mobius_residue_squarefree g q hs hq hqg]
    ring
  · rw [moebius_eq_zero_of_not_squarefree hs,zero_pow (by norm_num : 2 ≠ 0)]
    by_cases h : μ (g/p^(g.factorization p)) = 0
    · simp [h]
    · have hq0 : μ (g/q^(g.factorization q)) = 0 := by
        by_contra hq0
        exact hs (squarefree_of_two_residues g p q hg hpq
          (moebius_ne_zero_iff_squarefree.mp h) (moebius_ne_zero_iff_squarefree.mp hq0))
      simp [hq0]

theorem weight_two_prime_mul (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    TotientConvolution.weight (p*q*n) = if n.Coprime (p*q) then
      TotientConvolution.weight n / ((p-1:ℝ)*(q-1:ℝ)) else 0 := by
  by_cases hc : n.Coprime (p*q)
  · rw [if_pos hc,TotientConvolution.weight_multiplicative.map_mul_of_coprime hc.symm,
      TotientConvolution.weight_multiplicative.map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hpq),
      TotientConvolution.weight_prime p hp,TotientConvolution.weight_prime q hq]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [if_neg hc]
    have hs : ¬ Squarefree (p*q*n) := fun h => hc (Nat.coprime_of_squarefree_mul h).symm
    simp [TotientConvolution.weight,moebius_eq_zero_of_not_squarefree hs]

/-- Exact pq reindexing for the ordered cross term after residue cancellation. -/
theorem crossAt_reindex (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n),
      (μ (n/p^(n.factorization p)):ℝ)*(μ (n/q^(n.factorization q)):ℝ)/n.totient) =
      restricted (N/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ)) := by
  have he : (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n) =
      (Icc 1 N).filter (fun n => p*q ∣ n) := by
    ext n
    simp only [mem_filter]
    apply and_congr_right
    intro _
    exact ⟨fun h => ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd h.1 h.2,
      fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩⟩
  have ht : (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n),
      (μ (n/p^(n.factorization p)):ℝ)*(μ (n/q^(n.factorization q)):ℝ)/n.totient) =
      ∑ n ∈ (Icc 1 N).filter (fun n => p*q ∣ n), TotientConvolution.weight n := by
    rw [← he]
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega
    have h := congrArg (fun z : ℤ => (z:ℝ))
      (cross_residue n p q hn0 hp hq hpq (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2)
    simp only [Int.cast_mul,Int.cast_pow] at h
    change _ = (μ n:ℝ)^2/n.totient
    rw [h]
  have h := ElementaryGcd.sum_multiples N (p*q) (Nat.mul_pos hp.pos hq.pos)
    (fun n => (TotientConvolution.weight n : ℂ))
  have hr : (∑ n ∈ (Icc 1 N).filter (fun n => p*q ∣ n), TotientConvolution.weight n) =
      ∑ n ∈ Icc 1 (N/(p*q)), TotientConvolution.weight (p*q*n) := by exact_mod_cast h
  rw [ht,hr,restricted,sum_div]
  simp only [weight_two_prime_mul p q _ hp hq hpq,sum_filter]

#print axioms weight_two_prime_mul
#print axioms crossAt_reindex
#print axioms mobius_residue_squarefree
#print axioms squarefree_of_two_residues
#print axioms cross_residue
#print axioms diagonalAt_prime_powers
#print axioms diagonal_swap
#print axioms diagonal_reindex
end XiPrime8845.FengMarkedArithmetic

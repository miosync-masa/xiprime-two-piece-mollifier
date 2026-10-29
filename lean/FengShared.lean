import FengPrimeCancellation

/-! Global finite shared-prime cancellation, retaining full valuations and
the original sharedBlock cutoff. No asymptotic estimate is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.FengShared
open FengAtG FengPrimeCancellation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem prime_power_base_eq (p q k e : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hk : 0 < k) (h : p^k ∣ q^e) : p = q := by
  have hd : p ∣ q^e := (dvd_pow_self p hk.ne').trans h
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)

/-- Each nonzero marked divisor belongs to exactly one prime string. -/
theorem shared_divisor_partition (g v r : ℕ) (hg : g ≠ 0) (hv : v ≠ 0)
    (hr : r ∣ v) (f : ℕ → ℂ) :
    (if r.Coprime g then 0 else mark r*f r) =
      ∑ p ∈ g.primeFactors, if r ∣ p^(v.factorization p) then mark r*f r else 0 := by
  by_cases hpp : IsPrimePow r
  · obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hunique (q : ℕ) (hq : q ∈ g.primeFactors) (hne : q ≠ p) :
        ¬ p^k ∣ q^(v.factorization q) := by
      intro hd
      exact hne (prime_power_base_eq p q k _ hp (Nat.prime_of_mem_primeFactors hq) hk hd).symm
    by_cases hpg : p ∣ g
    · have hmem : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpg,hg⟩
      have hcop : ¬ (p^k).Coprime g := by
        simpa only [Nat.coprime_pow_left_iff hk,hp.coprime_iff_not_dvd,not_not] using hpg
      rw [if_neg hcop,Finset.sum_eq_single p]
      · rw [if_pos ((hp.pow_dvd_iff_dvd_ordProj hv).mp hr)]
      · intro q hq hne; exact if_neg (hunique q hq hne)
      · exact fun h => False.elim (h hmem)
    · have hcop : (p^k).Coprime g := (hp.coprime_iff_not_dvd.mpr hpg).pow_left k
      rw [if_pos hcop]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      apply if_neg
      apply hunique q hq
      intro heq
      exact hpg (heq ▸ Nat.dvd_of_mem_primeFactors hq)
  · rw [mark_zero_of_not_prime_pow r hpp]
    simp

theorem divisors_filter_ordProj (v p : ℕ) (hv : v ≠ 0) :
    v.divisors.filter (fun r => r ∣ p^(v.factorization p)) =
      (p^(v.factorization p)).divisors := by
  ext r
  simp only [Finset.mem_filter,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hr,_⟩,hd⟩
    exact ⟨hd,(Nat.ordProj_pos v p).ne'⟩
  · rintro ⟨hd,_⟩
    exact ⟨⟨hd.trans (Nat.ordProj_dvd v p),hv⟩,hd⟩

/-- The literal shared divisor sum, regrouped without dropping any prime power. -/
theorem shared_prime_strings (g n : ℕ) (hg : g ≠ 0) (hn : n ≠ 0) :
    shared g n = ∑ p ∈ g.primeFactors,
      ∑ k ∈ range ((g*n).factorization p+1),
        mark (p^k)*(μ ((g*n)/p^k):ℂ) := by
  have hv := mul_ne_zero hg hn
  have he : shared g n = ∑ r ∈ (g*n).divisors,
      if r.Coprime g then 0 else mark r*(μ ((g*n)/r):ℂ) := by
    simp only [shared,Finset.sum_filter]
    apply sum_congr rfl
    intro r hr
    split_ifs <;> simp_all
  rw [he]
  trans ∑ r ∈ (g*n).divisors, ∑ p ∈ g.primeFactors,
    if r ∣ p^((g*n).factorization p) then mark r*(μ ((g*n)/r):ℂ) else 0
  · apply sum_congr rfl
    intro r hr
    exact shared_divisor_partition g (g*n) r hg hv (Nat.dvd_of_mem_divisors hr)
      (fun d => (μ ((g*n)/d):ℂ))
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter,divisors_filter_ordProj _ p hv,
    Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-- Quotients along one prime string have a fixed p-free residual factor. -/
theorem quotient_prime_string (v p k : ℕ) (hk : k ≤ v.factorization p) :
    v/p^k = p^(v.factorization p-k)*(v/p^(v.factorization p)) := by
  have hp0 : p^k ≠ 0 := by
    have hpow : p^k ∣ p^(v.factorization p) := pow_dvd_pow p hk
    exact ne_zero_of_dvd_ne_zero (Nat.ordProj_pos v p).ne' hpow
  have hsplit : v = p^k*(p^(v.factorization p-k)*(v/p^(v.factorization p))) := by
    rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hk]
    exact (Nat.ordProj_mul_ordCompl_eq_self v p).symm
  conv_lhs => rw [hsplit]
  exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)

/-- Global cancellation: shared primes survive through the p-free residual.
In particular mu(g) is NOT factored out of this expression. -/
theorem shared_eq_prime_residues (g n : ℕ) (hg : g ≠ 0) (hn : n ≠ 0) :
    shared g n = ∑ p ∈ g.primeFactors,
      (μ ((g*n)/p^((g*n).factorization p)):ℂ)*(Real.log p:ℂ)^2 := by
  rw [shared_prime_strings g n hg hn]
  apply sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hv := mul_ne_zero hg hn
  have he : 0 < (g*n).factorization p := hprime.factorization_pos_of_dvd hv
    ((Nat.dvd_of_mem_primeFactors hp).trans (dvd_mul_right g n))
  have hc := Nat.coprime_ordCompl hprime hv
  have h := shared_local_cancellation p ((g*n).factorization p)
    ((g*n)/p^((g*n).factorization p)) hprime he hc
  convert h using 1
  apply sum_congr rfl
  intro k hk
  rw [quotient_prime_string _ p k (by have := mem_range.mp hk; omega)]

/-- Splitting off the p-parts of g and n preserves the residual product. -/
theorem shared_eq_residue_products (g n : ℕ) (hg : g ≠ 0) (hn : n ≠ 0) :
    shared g n = ∑ p ∈ g.primeFactors,
      (μ ((g/p^(g.factorization p))*(n/p^(n.factorization p))):ℂ)*(Real.log p:ℂ)^2 := by
  rw [shared_eq_prime_residues g n hg hn]
  apply sum_congr rfl
  intro p hp
  rw [Nat.ordCompl_mul]

/-- Regression for arbitrary repeated powers, including non-squarefree g. -/
theorem shared_two_prime_powers (p b a : ℕ) (hp : p.Prime) (hb : 0 < b) :
    shared (p^b) (p^a) = (Real.log p:ℂ)^2 := by
  rw [shared_eq_residue_products _ _ (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hb.ne' hp,Finset.sum_singleton,
    Nat.ordCompl_self_pow hp,Nat.ordCompl_self_pow hp]
  simp

/-- A finite coefficient bound after cancellation, with no valuation growth. -/
theorem shared_norm_le (g n : ℕ) (hg : g ≠ 0) (hn : n ≠ 0) :
    ‖shared g n‖ ≤ ∑ p ∈ g.primeFactors, (Real.log p)^2 := by
  rw [shared_eq_prime_residues g n hg hn]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hm : ‖(μ ((g*n)/p^((g*n).factorization p)):ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using (show |(μ ((g*n)/p^((g*n).factorization p)):ℝ)| ≤ 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=((g*n)/p^((g*n).factorization p))))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (sq_nonneg (Real.log p))

#print axioms prime_power_base_eq
#print axioms shared_divisor_partition
#print axioms divisors_filter_ordProj
#print axioms shared_prime_strings
#print axioms quotient_prime_string
#print axioms shared_eq_prime_residues
#print axioms shared_eq_residue_products
#print axioms shared_two_prime_powers
#print axioms shared_norm_le
end XiPrime8845.FengShared

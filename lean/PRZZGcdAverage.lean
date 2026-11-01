import Mathlib

/-! Exact divisor bookkeeping for the Type I frequency average.
The gcd factor is averaged, not discarded. Coprimality is expanded before
any cancellation estimate; no estimate for a restricted Kloosterman sum
is inferred merely from an estimate for the unrestricted sum. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZGcdAverage
set_option maxHeartbeats 1000000

theorem sum_multiples {R : Type*} [AddCommMonoid R] (A d : ℕ) (hd : 0 < d)
    (w : ℕ → R) :
    (∑ n ∈ (Icc 1 A).filter (fun n => d ∣ n), w n) =
      ∑ k ∈ Icc 1 (A/d), w (d*k) := by
  apply sum_bij (fun n _ => n/d)
  · intro n hn
    obtain ⟨hn,hdn⟩ := mem_filter.mp hn
    have he := Nat.mul_div_cancel' hdn
    apply mem_Icc.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      rw [hz,mul_zero] at he
      exact (Nat.ne_zero_of_lt (mem_Icc.mp hn).1) he.symm
    · exact Nat.div_le_div_right (mem_Icc.mp hn).2
  · intro n hn m hm he
    have hn' := Nat.mul_div_cancel' (mem_filter.mp hn).2
    have hm' := Nat.mul_div_cancel' (mem_filter.mp hm).2
    exact hn'.symm.trans ((congrArg (fun k => d*k) he).trans hm')
  · intro k hk
    refine ⟨d*k,mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith [(mem_Icc.mp hk).1],
      ?_⟩,dvd_mul_right d k⟩,?_⟩
    · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp hk).2
    · exact Nat.mul_div_right k hd
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

theorem common_divisors (n q : ℕ) (hq : q ≠ 0) :
    q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
  ext d
  simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
  have hg : n.gcd q ≠ 0 := by simp [Nat.gcd_eq_zero_iff,hq]
  tauto

theorem gcd_sum (A q : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Icc 1 A, n.gcd q) = ∑ d ∈ q.divisors, d.totient*(A/d) := by
  have he (n : ℕ) : n.gcd q = ∑ d ∈ q.divisors, if d ∣ n then d.totient else 0 := by
    rw [← sum_filter,common_divisors n q hq,Nat.sum_totient]
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter,sum_multiples A d (Nat.pos_of_mem_divisors hd)]
  simp [Nat.mul_comm]

theorem gcd_sum_le (A q : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Icc 1 A, n.gcd q) ≤ A*q.divisors.card := by
  rw [gcd_sum A q hq]
  calc
    _ ≤ ∑ d ∈ q.divisors, A := sum_le_sum (fun d _ =>
      (Nat.mul_le_mul_right (A/d) (Nat.totient_le d)).trans (Nat.mul_div_le A d))
    _ = _ := by simp [Nat.mul_comm]

theorem coprime_indicator (n q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, if d ∣ n then (μ d : ℂ) else 0) =
      if n.Coprime q then 1 else 0 := by
  rw [← sum_filter,common_divisors n q hq]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (n.gcd q))
    (coe_moebius_mul_coe_zeta (R := ℂ))
  rw [coe_mul_zeta_apply] at h
  simpa [Nat.Coprime,ArithmeticFunction.one_apply] using h

theorem coprime_sum (s : Finset ℕ) (q : ℕ) (hq : q ≠ 0) (w : ℕ → ℂ) :
    (∑ n ∈ s.filter (fun n => n.Coprime q), w n) =
      ∑ d ∈ q.divisors, (μ d : ℂ)*(∑ n ∈ s.filter (fun n => d ∣ n), w n) := by
  simp only [sum_filter,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have h := congrArg (fun z : ℂ => z*w n) (coprime_indicator n q hq)
  simpa only [sum_mul,ite_mul,zero_mul,one_mul,mul_ite,mul_zero] using h.symm

#print axioms sum_multiples
#print axioms common_divisors
#print axioms gcd_sum
#print axioms gcd_sum_le
#print axioms coprime_indicator
#print axioms coprime_sum
end XiPrime8845.PRZZGcdAverage

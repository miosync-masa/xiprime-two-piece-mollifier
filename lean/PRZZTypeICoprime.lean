import PRZZGcdAverage
import PRZZTypeI

/-! Exact removal of the extra d-coprimality in a Type I row, before
using cancellation. The inverse residue at ell*k remains literal: this
module does not assume Weil for an arbitrarily restricted sum. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.PRZZTypeICoprime
open PRZZKloostermanInputs PRZZGcdAverage
set_option maxHeartbeats 2000000

def restrictedSum (d q N : ℕ) (a : ℤ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, if d.Coprime n ∧ n.Coprime q then
    w n*e ((a:ℝ)*inverseResidue q n/q) else 0

theorem divisor_rows (d q N : ℕ) (hd : d ≠ 0) (a : ℤ) (w : ℕ → ℂ) :
    restrictedSum d q N a w = ∑ ell ∈ d.divisors, (μ ell:ℂ)*
      ∑ k ∈ Icc 1 (N/ell), if (ell*k).Coprime q then
        w (ell*k)*e ((a:ℝ)*inverseResidue q (ell*k)/q) else 0 := by
  classical
  have he : restrictedSum d q N a w =
      ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime d),
        if n.Coprime q then w n*e ((a:ℝ)*inverseResidue q n/q) else 0 := by
    simp only [restrictedSum,sum_filter]
    apply sum_congr rfl; intro n hn
    split_ifs <;> aesop (add safe forward Nat.Coprime.symm)
  rw [he,coprime_sum _ d hd]
  apply sum_congr rfl; intro ell hell
  rw [sum_multiples N ell (Nat.pos_of_mem_divisors hell)]

/-- Divisors sharing a prime with the modulus vanish exactly. The sharp
length N/ell and the scaled analytic weight are not dropped. -/
theorem coprime_divisor_rows (d q N : ℕ) (hd : d ≠ 0) (a : ℤ) (w : ℕ → ℂ) :
    restrictedSum d q N a w =
      ∑ ell ∈ d.divisors.filter (fun ell => ell.Coprime q), (μ ell:ℂ)*
        ∑ k ∈ Icc 1 (N/ell), if k.Coprime q then
          w (ell*k)*e ((a:ℝ)*inverseResidue q (ell*k)/q) else 0 := by
  classical
  rw [divisor_rows d q N hd a w,sum_filter]
  apply sum_congr rfl; intro ell hell
  by_cases he : ell.Coprime q
  · rw [if_pos he]
    congr 1
    apply sum_congr rfl; intro k hk
    have hh : (ell*k).Coprime q ↔ k.Coprime q := by
      exact ⟨fun h => (Nat.coprime_mul_iff_left.mp h).2,
        fun h => Nat.coprime_mul_iff_left.mpr ⟨he,h⟩⟩
    exact if_congr hh rfl rfl
  · rw [if_neg he]
    have hz : ∀ k, ¬ (ell*k).Coprime q :=
      fun k h => he (Nat.coprime_mul_iff_left.mp h).1
    simp only [if_neg (hz _),sum_const_zero,mul_zero]

#print axioms divisor_rows
#print axioms coprime_divisor_rows
end XiPrime8845.PRZZTypeICoprime

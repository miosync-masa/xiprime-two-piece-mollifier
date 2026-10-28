import TotientWeight
import MobiusHarmonic

/-! Dirichlet correction of the squarefree reciprocal-totient weight. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset
namespace XiPrime8845.TotientConvolution
open MobiusHarmonic

def weight : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ)^2 / n.totient, by simp⟩

theorem weight_multiplicative : weight.IsMultiplicative := by
  refine ⟨by norm_num [weight], ?_⟩
  intro m n h
  change (μ (m*n) : ℝ)^2 / (m*n).totient = _
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  simp only [Int.cast_mul, Nat.cast_mul, mul_pow, weight, coe_mk, div_mul_div_comm]

theorem mobiusReciprocal_multiplicative : mobiusReciprocal.IsMultiplicative := by
  refine ⟨by norm_num [mobiusReciprocal], ?_⟩
  intro m n h
  change (μ (m*n) : ℝ)/(m*n : ℕ) = _
  rw [isMultiplicative_moebius.map_mul_of_coprime h]
  simp [mobiusReciprocal, div_mul_div_comm]

def correction : ArithmeticFunction ℝ := weight * mobiusReciprocal

theorem correction_multiplicative : correction.IsMultiplicative :=
  weight_multiplicative.mul mobiusReciprocal_multiplicative

theorem correction_convolution : correction * reciprocal = weight := by
  rw [correction, mul_assoc, reciprocal_convolution, mul_one]

theorem harmonic_representation (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (μ n : ℝ)^2 / n.totient) =
      ∑ d ∈ Ioc 0 N, correction d * MobiusHarmonic.harmonic (N/d) := by
  have h := sum_Ioc_mul_eq_sum_sum correction reciprocal N
  rw [correction_convolution] at h
  simpa [weight, reciprocal, MobiusHarmonic.harmonic] using h

theorem weight_prime (p : ℕ) (hp : p.Prime) : weight p = 1 / (p-1 : ℝ) := by
  simp [weight, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le]

theorem weight_prime_pow_ge_two (p k : ℕ) (hp : p.Prime) :
    weight (p^(k+2)) = 0 := by
  simp [weight, moebius_apply_prime_pow hp (by omega : k+2 ≠ 0),
    show k+2 ≠ 1 by omega]

theorem correction_prime_pow (p k : ℕ) (hp : p.Prime) :
    correction (p^k) = if k = 0 then 1 else if k = 1 then 1/((p:ℝ)*(p-1))
      else if k = 2 then -1/((p:ℝ)*(p-1)) else 0 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  cases k with
  | zero => simpa using correction_multiplicative.map_one
  | succ k =>
    rw [correction, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => weight a * mobiusReciprocal b),
      Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : (∑ i ∈ Finset.range k, weight (p^(i+1+1)) *
        mobiusReciprocal (p^(k+1)/p^(i+1+1))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [show i+1+1=i+2 by omega, weight_prime_pow_ge_two p i hp, zero_mul]
    simp only [pow_zero, Nat.div_one, Nat.zero_add, pow_one] at *
    rw [hz, zero_add, weight_prime p hp]
    have hdiv : p^(k+1)/p = p^k := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    rw [hdiv]
    simp only [weight, coe_mk, moebius_apply_one, Int.cast_one, one_pow,
      Nat.totient_one, Nat.cast_one, div_one, one_mul, mobiusReciprocal]
    cases k with
    | zero => simp [moebius_apply_prime hp]; field_simp; ring
    | succ k =>
      simp only [moebius_apply_prime_pow hp (by omega : k+1+1 ≠ 0),
        if_neg (by omega : k+1+1 ≠ 1), Int.cast_zero, zero_div, add_zero,
        moebius_apply_prime_pow hp (by omega : k+1 ≠ 0)]
      by_cases hk : k = 0
      · subst k; norm_num; field_simp
      · simp [hk, show k+1 ≠ 1 by omega, show k+1+1 ≠ 2 by omega]

#print axioms correction_convolution
#print axioms harmonic_representation
#print axioms correction_prime_pow
end XiPrime8845.TotientConvolution

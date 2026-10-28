import Mathlib

/-! Finite removal of coprimality by the g-supported convolution. No PNT or
uniform error estimate is used. Prime powers in the supported factor are retained. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction Finset

namespace XiPrime8845.SmoothMobius
attribute [local instance] Classical.propDecidable

def supported (g n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ∣ g

theorem supported_mul (g a b : ℕ) :
    supported g (a*b) ↔ supported g a ∧ supported g b := by
  constructor
  · intro h
    exact ⟨fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha, hb⟩ p hp h
    exact (hp.dvd_mul.mp h).elim (ha p hp) (hb p hp)

theorem supported_prime_pow (g p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    supported g (p^k) ↔ p ∣ g := by
  constructor
  · intro h
    exact h p hp (dvd_pow_self p hk.ne')
  · intro h q hq hqp
    have hqp' := hq.dvd_of_dvd_pow hqp
    have he : q = p := (Nat.dvd_prime hp).mp hqp' |>.resolve_left hq.ne_one
    simpa [he] using h

def restricted (g : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Coprime g then (μ n : ℂ) else 0, by simp⟩

theorem restricted_apply (g n : ℕ) :
    restricted g n = if n.Coprime g then (μ n : ℂ) else 0 := rfl

theorem restricted_multiplicative (g : ℕ) : (restricted g).IsMultiplicative := by
  refine ⟨by simp [restricted_apply], ?_⟩
  intro a b hab
  change (if (a*b).Coprime g then (μ (a*b) : ℂ) else 0) = _
  simp only [Nat.coprime_mul_iff_left,
    isMultiplicative_moebius.map_mul_of_coprime hab, restricted_apply, Int.cast_mul]
  split_ifs <;> simp_all

def supportedWeight (g : ℕ) : ArithmeticFunction ℂ := restricted g * ζ

theorem supportedWeight_prime_pow (g p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    supportedWeight g (p^k) = if p ∣ g then 1 else 0 := by
  by_cases hpg : p ∣ g
  · rw [if_pos hpg, supportedWeight, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, restricted_apply, moebius_apply_one, Int.cast_one]
    have hn (i : ℕ) : ¬ (p^(i+1)).Coprime g := by
      simpa only [Nat.coprime_pow_left_iff (Nat.succ_pos i), hp.coprime_iff_not_dvd,
        not_not] using hpg
    simp only [hn, ↓reduceIte, Finset.sum_const_zero, zero_add]
    exact if_pos (Nat.coprime_one_left g)
  · rw [if_neg hpg, supportedWeight, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    have hc (i : ℕ) : (p^i).Coprime g := (hp.coprime_iff_not_dvd.mpr hpg).pow_left i
    simp only [restricted_apply]
    simp_rw [if_pos (hc _)]
    have h := congrArg (fun f : ArithmeticFunction ℂ => f (p^k))
      (coe_moebius_mul_coe_zeta (R := ℂ))
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp] at h
    simpa [ArithmeticFunction.one_apply, hp.ne_one, hk.ne'] using h

/-- The convolution weight is exactly a 0/1 supported-number indicator. -/
theorem supportedWeight_eq (g n : ℕ) :
    supportedWeight g n = if n ≠ 0 ∧ supported g n then 1 else 0 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [supportedWeight, restricted_apply, supported]
  | prime_pow p k hp hk =>
    rw [supportedWeight_prime_pow g p k hp hk]
    simp only [pow_ne_zero _ hp.ne_zero, ne_eq, not_false_eq_true, true_and,
      supported_prime_pow g p k hp hk]
  | coprime a b ha hb hab ih₁ ih₂ =>
    have hm : (supportedWeight g).IsMultiplicative :=
      (restricted_multiplicative g).mul isMultiplicative_zeta.natCast
    rw [hm.map_mul_of_coprime hab, ih₁, ih₂]
    simp only [ne_eq, mul_eq_zero, not_or, supported_mul]
    split_ifs <;> simp_all

/-- Exact convolution identity removing coprimality without a divisor-count bound. -/
theorem restricted_convolution (g : ℕ) :
    restricted g = supportedWeight g * (μ : ArithmeticFunction ℂ) := by
  rw [supportedWeight, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

theorem restricted_divisor_sum (g n : ℕ) :
    (if n.Coprime g then (μ n : ℂ) else 0) =
      ∑ x ∈ n.divisorsAntidiagonal,
        (if supported g x.1 then 1 else 0) * (μ x.2 : ℂ) := by
  change restricted g n = _
  rw [restricted_convolution, mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [supportedWeight_eq]
  have hx0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
  simp [hx0]

/-- The Conrey coefficient at g*n, without a squarefree assumption on g. -/
theorem moebius_mul_indicator (g n : ℕ) :
    (μ (g*n) : ℂ) = (μ g : ℂ) * (if n.Coprime g then (μ n : ℂ) else 0) := by
  by_cases h : n.Coprime g
  · rw [if_pos h, isMultiplicative_moebius.map_mul_of_coprime h.symm]
    push_cast
    rfl
  · have hsq : ¬ Squarefree (g*n) := fun hs => h (Nat.coprime_of_squarefree_mul hs).symm
    rw [if_neg h, moebius_eq_zero_of_not_squarefree hsq]
    simp

#print axioms supported_mul
#print axioms supported_prime_pow
#print axioms restricted_multiplicative
#print axioms supportedWeight_prime_pow
#print axioms supportedWeight_eq
#print axioms restricted_convolution
#print axioms restricted_divisor_sum
#print axioms moebius_mul_indicator
end XiPrime8845.SmoothMobius

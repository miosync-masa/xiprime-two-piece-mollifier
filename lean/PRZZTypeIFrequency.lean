import PRZZTypeI
import PRZZGcdAverage

/-! Positive-frequency aggregation of the literal weighted Type I sum.
The divisor count is retained explicitly. Additional source coprimality,
coefficient growth, and the e,v,h sums are separate obligations. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTypeIFrequency
open PRZZTypeI PRZZGcdAverage PRZZKloostermanInputs
set_option maxHeartbeats 1000000

theorem gcd_sum_real (A q : ℕ) (hq : q ≠ 0) :
    (∑ a ∈ Icc 1 A, (a.gcd q : ℝ)) ≤ (A:ℝ)*q.divisors.card := by
  exact_mod_cast gcd_sum_le A q hq

/-- The constant is chosen before the modulus, cutoff and weight. -/
theorem positive_frequency_bound (hWeil : WeilIncomplete) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q → ∀ A M H : ℕ, ∀ w : ℕ → ℂ,
      (∑ a ∈ Icc 1 A, ‖weightedSum q (a:ℤ) M H w‖) ≤
        C*Real.rpow q (1/2+ε)*(1+(H:ℝ)/q)*variation w H*(A:ℝ)*q.divisors.card := by
  obtain ⟨C,hC,h⟩ := weighted_bound hWeil ε hε
  refine ⟨C,hC,?_⟩
  intro q hq A M H w
  let B := C*Real.rpow q (1/2+ε)*(1+(H:ℝ)/q)*variation w H
  have hv : 0 ≤ variation w H := by unfold variation; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (by positivity)) hv
  calc
    _ ≤ ∑ a ∈ Icc 1 A, B*(a.gcd q:ℝ) := by
      apply sum_le_sum
      intro a ha
      have hh := h q hq (a:ℤ) M H w
      simp only [Int.natAbs_natCast] at hh
      exact hh.trans_eq (by dsimp [B]; ring)
    _ = B*(∑ a ∈ Icc 1 A, (a.gcd q:ℝ)) := by rw [mul_sum]
    _ ≤ B*((A:ℝ)*q.divisors.card) :=
      mul_le_mul_of_nonneg_left (gcd_sum_real A q (by omega)) hB
    _ = _ := by dsimp [B]; ring

#print axioms gcd_sum_real
#print axioms positive_frequency_bound
end XiPrime8845.PRZZTypeIFrequency

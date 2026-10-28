import RationalEvaluator

/-! Exact rational inequalities, checked by kernel reduction. -/
namespace XiPrime8845.RationalBounds
open RationalEvaluator
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem rational_bounds :
    minusValue ≤ (-5883815413543881 / 10^10 : ℚ) ∧
    0 ≤ plusValue ∧ plusValue ≤ (728627019299614 / 10^10 : ℚ) := by
  decide +kernel

#print axioms rational_bounds
end XiPrime8845.RationalBounds

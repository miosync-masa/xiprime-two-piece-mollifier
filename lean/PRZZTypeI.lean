import PRZZKloostermanInputs

/-! Conditional Type I analytic adapter: discrete partial summation of the
literal incomplete inverse-phase sum. The total variation is retained.
PRZZ-specific smooth weights, the extra coprimality with d, and aggregation
over a,e,v are not silently absorbed into a T^epsilon factor here. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTypeI
open PRZZKloostermanInputs
set_option maxHeartbeats 1000000

def term (q : ℕ) (a : ℤ) (M j : ℕ) : ℂ :=
  if (M+j+1).Coprime q then e ((a:ℝ)*inverseResidue q (M+j+1)/q) else 0

theorem incomplete_eq_range (q : ℕ) (a : ℤ) (M H : ℕ) :
    incompleteSum q a M H = ∑ j ∈ range H, term q a M j := by
  unfold incompleteSum
  rw [sum_filter]
  have he : Ioc M (M+H) = Ico (M+1) (M+H+1) := by ext n; simp only [mem_Ioc,mem_Ico]; omega
  rw [he,sum_Ico_eq_sum_range]
  simp only [show M+H+1-(M+1)=H by omega]
  apply sum_congr rfl
  intro j hj
  simp only [term,show M+1+j=M+j+1 by omega]

def variation (w : ℕ → ℂ) (H : ℕ) : ℝ :=
  ‖w (H-1)‖+∑ j ∈ range (H-1), ‖w (j+1)-w j‖

/-- No positivity of the complex summands or weights is required. -/
theorem abel_bound (w z : ℕ → ℂ) (H : ℕ) (B : ℝ)
    (hz : ∀ k ≤ H, ‖∑ j ∈ range k, z j‖ ≤ B) :
    ‖∑ j ∈ range H, w j*z j‖ ≤ B*variation w H := by
  have he := sum_range_by_parts w z H
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖w (H-1)*(∑ j ∈ range H, z j)‖ ≤ ‖w (H-1)‖*B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hz H le_rfl) (norm_nonneg _)
  have hrest : ‖∑ j ∈ range (H-1), (w (j+1)-w j)*(∑ i ∈ range (j+1), z i)‖ ≤
      ∑ j ∈ range (H-1), ‖w (j+1)-w j‖*B := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro j hj
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hz (j+1) (by have := mem_range.mp hj; omega)) (norm_nonneg _)
  apply (add_le_add hfirst hrest).trans_eq
  rw [← sum_mul]
  unfold variation
  ring

def weightedSum (q : ℕ) (a : ℤ) (M H : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ j ∈ range H, w j*term q a M j

/-- Uniform in the starting point, interval length and chosen weight.
WeilIncomplete is a hypothesis, not an axiom installed by this theorem. -/
theorem weighted_bound (hWeil : WeilIncomplete) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q → ∀ a : ℤ, ∀ M H : ℕ, ∀ w : ℕ → ℂ,
      ‖weightedSum q a M H w‖ ≤
        C*Real.rpow q (1/2+ε)*(a.natAbs.gcd q)*(1+(H:ℝ)/q)*variation w H := by
  obtain ⟨C,hC,h⟩ := hWeil ε hε
  refine ⟨C,hC,?_⟩
  intro q hq a M H w
  apply abel_bound
  intro k hk
  rw [← incomplete_eq_range]
  apply (h q hq a M k).trans
  have hbase : 0 ≤ C*Real.rpow (q:ℝ) (1/2+ε)*(a.natAbs.gcd q:ℝ) :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hbase
  exact add_le_add_right (div_le_div_of_nonneg_right
    (show (k:ℝ) ≤ H by exact_mod_cast hk) (show (0:ℝ) ≤ q from Nat.cast_nonneg q)) 1

#print axioms incomplete_eq_range
#print axioms abel_bound
#print axioms weighted_bound
end XiPrime8845.PRZZTypeI

import PRZZHBBranches
import PRZZRowWindow

/-! Cutoff-local re-expansion of the full coefficient against the literal
source row. Branch lists are not identified: their evaluated sums agree
on the retained support. This identity also applies to small local scales;
it is not a Type I/II estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZLocalReexpansion
open PRZZHBBranches PRZZGCoefficient PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

theorem local_coefficient (M K n : ℕ) (js : List ℕ) (hK : 0 < K) (hn : n ≤ M) :
    coefficient js n = total (branches ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js) n := by
  apply coefficient_branches
  exact root_cutoff_range (M:ℝ) (Nat.cast_nonneg _) K hK n (by exact_mod_cast hn)

/-- Cutoffs may differ; only evaluation on their common valid range agrees. -/
theorem change_cutoff (y M K n : ℕ) (js : List ℕ) (hK : 0 < K)
    (hy : n < (y+1)^K) (hn : n ≤ M) :
    total (branches y K js) n = total (branches ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js) n := by
  rw [← coefficient_branches y K js n hy, ← local_coefficient M K n js hK hn]

/-- Any remaining coprimality predicate and analytic factor stay inside
the sum. No norm or absolute value is taken during re-expansion. -/
theorem masked_sum (s : Finset ℕ) (M K : ℕ) (js : List ℕ) (hK : 0 < K)
    (p : ℕ → Prop) [DecidablePred p] (w F : ℕ → ℂ)
    (hw : ∀ n ∈ s, M < n → w n = 0) :
    (∑ n ∈ s, if p n then (coefficient js n:ℂ)*w n*F n else 0) =
      ∑ n ∈ s, if p n then
        (total (branches ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js) n:ℂ)*w n*F n else 0 := by
  apply sum_congr rfl
  intro n hn
  by_cases h : n ≤ M
  · rw [local_coefficient M K n js hK h]
  · simp [hw n hn (lt_of_not_ge h)]

/-- The actual source mask supplies the smaller cutoff, including ef <= N
after n=ef. The second coefficient and frequency phase remain arbitrary F. -/
theorem row_sum (N d h j K : ℕ) (js : List ℕ) (hd : 0 < d) (hh : 0 < h)
    (hK : 0 < K) (F1 : ℝ → ℂ) (α : ℂ) (t : ℝ) (F : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, if d.Coprime n then (coefficient js n:ℂ)*
      PRZZResidualRow.weight N d j h F1 α t n*F n else 0) =
      ∑ n ∈ Icc 1 N, if d.Coprime n then
        (total (branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K js) n:ℂ)*
          PRZZResidualRow.weight N d j h F1 α t n*F n else 0 := by
  apply masked_sum _ _ _ _ hK
  intro n hn hlarge
  rw [PRZZRowWindow.weight_eq N d h j hd hh]
  simp [PRZZMaskedVariation.mask, not_le.mpr hlarge]

#print axioms local_coefficient
#print axioms change_cutoff
#print axioms masked_sum
#print axioms row_sum
end XiPrime8845.PRZZLocalReexpansion

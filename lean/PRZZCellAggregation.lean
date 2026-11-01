import PRZZAllBranchCells
import PRZZDyadicBudget

/-! The exact local HB expansion with all scalar weights and all indexed
dyadic cells charged. A bound on the literal unscaled cells remains an
explicit analytic input; no selected-cell or positivity shortcut is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZCellAggregation
open PRZZHBBranches PRZZActualBranchCells
set_option maxHeartbeats 2000000

theorem scalar (N : ℕ) (b : Branch) (w : ℕ → ℂ) :
    (∑ k : Fin b.2.length → Fin (Nat.log 2 N+1), ∑ n ∈ Icc 1 N,
      w n*(b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ)) =
    (b.1:ℂ)*(∑ k : Fin b.2.length → Fin (Nat.log 2 N+1), ∑ n ∈ Icc 1 N,
      w n*(group N b (fun i => (k i).val) univ n:ℂ)) := by
  simp only [mul_sum]
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro n hn
  ring

theorem grid_bound (N : ℕ) (b : Branch) (w : ℕ → ℂ) (B : ℝ)
    (hb : ∀ k : Fin b.2.length → Fin (Nat.log 2 N+1),
      ‖∑ n ∈ Icc 1 N, w n*(group N b (fun i => (k i).val) univ n:ℂ)‖ ≤ B) :
    ‖∑ k : Fin b.2.length → Fin (Nat.log 2 N+1), ∑ n ∈ Icc 1 N,
      w n*(group N b (fun i => (k i).val) univ n:ℂ)‖ ≤
        (Nat.log 2 N+1:ℝ)^b.2.length*B := by
  apply (norm_sum_le _ _).trans
  have h := sum_le_sum (fun k (_ : k ∈ univ) => hb k)
  simpa [Fintype.card_fun] using h

/-- A single constant precedes the local cutoff, height and original
weight. In particular repeated branches contribute their full list mass. -/
theorem local_bound (K : ℕ) (js : List ℕ) (hK : 0 < K)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 1 ≤ N → ∀ T B : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B → ∀ w : ℕ → ℂ,
      (∀ n ∈ Icc 1 N, M < n → w n = 0) →
      (∀ b ∈ branches ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js,
        ∀ k : Fin b.2.length → Fin (Nat.log 2 N+1),
          ‖∑ n ∈ Icc 1 N, w n*(group N b (fun i => (k i).val) univ n:ℂ)‖ ≤ B) →
      ‖∑ n ∈ Icc 1 N, w n*(PRZZGCoefficient.coefficient js n:ℂ)‖ ≤ C*T^eta*B := by
  obtain ⟨D,hD,hd⟩ := PRZZDyadicBudget.grids_absorbed ((js.length+1)*(2*K)) eta heta
  have hm := PRZZBranchMass.mass_nonneg K js
  refine ⟨PRZZBranchMass.mass K js*D+1,by positivity,?_⟩
  intro N M hN T B hNT hL hB w hw hb
  rw [PRZZAllBranchCells.local_all N M K js hK w hw]
  simp_rw [scalar]
  have hh := PRZZBranchMass.sum_bound ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js
    (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1), ∑ n ∈ Icc 1 N,
      w n*(group N b (fun i => (k i).val) univ n:ℂ)) (D*T^eta*B) (by
        intro b hbr
        exact (grid_bound N b w B (hb b hbr)).trans
          (mul_le_mul_of_nonneg_right (hd N hN T hNT hL b.2.length
            (PRZZBranchDegrees.branches_length _ K js b hbr)) hB))
  apply hh.trans
  have ht : 0 ≤ T^eta := Real.rpow_nonneg
    ((by exact_mod_cast (Nat.zero_le N) : (0:ℝ)≤N).trans hNT) _
  nlinarith

#print axioms scalar
#print axioms grid_bound
#print axioms local_bound
end XiPrime8845.PRZZCellAggregation

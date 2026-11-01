import PRZZAllBranchCells

/-! Effective boxes for the actual masked HB groups. The minimum with N
is essential: an inflated dyadic upper bound need not be <=N. The sharp
product restriction and arbitrary weight survive the rectangularization. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZActualSupportBoxes
open PRZZActualBranchCells PRZZHBBranches
set_option maxHeartbeats 2000000

def upper (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) : ℕ := min N (∏ i ∈ s, 2^(k i+1))

theorem bounds (N : ℕ) (hN : 1 ≤ N) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) : 1 ≤ upper N b k s ∧ upper N b k s ≤ N := by
  refine ⟨le_min hN ?_,min_le_left _ _⟩
  exact one_le_prod (fun i _ => Nat.one_le_pow _ _ (by norm_num))

theorem vanishes (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (n : ℕ) (hn : n ≤ N) (hu : upper N b k s < n) :
    group N b k s n = 0 := by
  by_contra hz
  have hs := (group_support N b k s n hz).2
  exact (not_lt_of_ge (le_min hn hs)) hu

/-- The complete product-limited matrix is exactly its effective box.
No product cutoff is replaced by two independent cutoffs. -/
theorem rectangle (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (w : ℕ → ℕ → ℂ) :
    (∑ e ∈ Icc 1 N, ∑ f ∈ Icc 1 N, if e*f ≤ N then
      w e f*(group N b k s e:ℂ)*(group N b k (univ \ s) f:ℂ) else 0) =
    ∑ e ∈ Icc 1 (upper N b k s), ∑ f ∈ Icc 1 (upper N b k (univ \ s)),
      if e*f ≤ N then w e f*(group N b k s e:ℂ)*(group N b k (univ \ s) f:ℂ) else 0 := by
  symm
  trans ∑ e ∈ Icc 1 (upper N b k s), ∑ f ∈ Icc 1 N, if e*f ≤ N then
    w e f*(group N b k s e:ℂ)*(group N b k (univ \ s) f:ℂ) else 0
  · apply sum_congr rfl
    intro e he
    apply sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _))
    intro f hf hnot
    have hu : upper N b k (univ \ s) < f := by
      have hpos := (mem_Icc.mp hf).1
      by_contra hn
      exact hnot (mem_Icc.mpr ⟨hpos,le_of_not_gt hn⟩)
    simp [vanishes N b k (univ \ s) f (mem_Icc.mp hf).2 hu]
  · apply sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _))
    intro e he hnot
    have hu : upper N b k s < e := by
      have hpos := (mem_Icc.mp he).1
      by_contra hn
      exact hnot (mem_Icc.mpr ⟨hpos,le_of_not_gt hn⟩)
    simp [vanishes N b k s e (mem_Icc.mp he).2 hu]

#print axioms bounds
#print axioms vanishes
#print axioms rectangle
end XiPrime8845.PRZZActualSupportBoxes

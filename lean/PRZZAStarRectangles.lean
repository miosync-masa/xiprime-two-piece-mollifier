import PRZZAStarNu
import PRZZDyadic

/-! Exact dyadic rectangles of the complete original coefficient pair.
No coefficient is replaced by an envelope. Coprimality stays in the sum;
the d*n cutoffs and the dyadic restrictions are separate zero extensions
in each coordinate. This is not the balanced Heath-Brown factor grouping. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZAStarRectangles
open PRZZAStarNu PRZZNuCoefficient PRZZDyadic PRZZMellinSeparation
set_option maxHeartbeats 2000000

def rectangle (N d j l : ℕ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) : ℂ :=
  ∑ n1 ∈ cell N j, ∑ n2 ∈ cell N l,
    if n1.Coprime n2 ∧ d*n1 ≤ N ∧ d*n2 ≤ N then
      pairCoeff d a F1 F2 FM α β x t (n1,n2)*
        PRZZKloostermanInputs.e (-(k:ℝ)*PRZZKloostermanInputs.inverseResidue n2 n1/n2)
    else 0

theorem pair_partition (N d : ℕ) (f : (ℕ × ℕ) → ℂ) :
    (∑ i ∈ pairs N d, f i) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ n1 ∈ cell N j, ∑ n2 ∈ cell N l,
          if n1.Coprime n2 ∧ d*n1 ≤ N ∧ d*n2 ≤ N then f (n1,n2) else 0 := by
  simp only [pairs,sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  rw [sum_partition N]
  apply sum_congr rfl
  intro j hj
  simp_rw [sum_partition N]
  rw [sum_comm]

def firstCoeff (N d j : ℕ) (a : ℕ → ℂ) (F1 : ℝ → ℂ) (α : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ cell N j ∧ d*n ≤ N then a (d*n)*F1 (d*n)/(n:ℂ)^α*twist n t else 0

def secondCoeff (N d l : ℕ) (a : ℕ → ℂ) (F2 FM : ℝ → ℂ) (β : ℂ)
    (x t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ cell N l ∧ d*n ≤ N then
    star (a (d*n))*F2 (d*n)*FM (x*n)/(n:ℂ)^β*twist n t else 0

/-- Coordinate zero extensions, rather than deletion of restrictions
inside a cancellation estimate. This is the full arithmetic coefficient. -/
theorem rectangle_separated (N d j l : ℕ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) :
    rectangle N d j l a F1 F2 FM α β x t k =
      ∑ n1 ∈ Icc 1 N, ∑ n2 ∈ (Icc 1 N).filter (fun n2 => n1.Coprime n2),
        firstCoeff N d j a F1 α t n1*secondCoeff N d l a F2 FM β x t n2*
          PRZZKloostermanInputs.e (-(k:ℝ)*PRZZKloostermanInputs.inverseResidue n2 n1/n2) := by
  unfold rectangle firstCoeff secondCoeff pairCoeff
  simp only [cell,sum_filter,mem_filter]
  apply sum_congr rfl
  intro n1 hn1
  by_cases hj : Nat.log 2 n1 = j
  · simp only [hj,if_true,hn1,true_and]
    apply sum_congr rfl
    intro n2 hn2
    simp only [hn2,true_and]
    by_cases hl : Nat.log 2 n2 = l <;> by_cases hc : n1.Coprime n2 <;>
      by_cases h1 : d*n1 ≤ N <;> by_cases h2 : d*n2 ≤ N <;>
      simp [hl,hc,h1,h2]
  · simp [hj]

theorem signedSum_rectangles (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x y t : ℝ) :
    signedSum N d D H a F1 F2 FM α β x y t =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ k ∈ (frequencies d D H).image freq,
          nu (frequencies d D H) x y k * rectangle N d j l a F1 F2 FM α β x t k := by
  unfold signedSum
  simp_rw [pair_partition,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  simp only [rectangle,mul_sum]

#print axioms pair_partition
#print axioms rectangle_separated
#print axioms signedSum_rectangles
end XiPrime8845.PRZZAStarRectangles

import PRZZFreeLogCoprime
import PRZZHiAllocatedCells

/-! Exact free-factor transport of the literal source row. The free
dyadic cell is retained inside the Weil weight, not silently removed.
This module does not assert the full signedCells budget. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZFreeSource
open PRZZSupportedBranches PRZZKloostermanInputs
set_option maxHeartbeats 3000000

def freeWeight (N d j h e r m : ℕ) (F0 : ℝ → ℂ) (Q t : ℝ) (alpha : ℂ) (n : ℕ) : ℂ :=
  if n ∈ PRZZDyadic.cell N r then
    PRZZFreeLogCoprime.row N d j (h*e) m F0 Q t alpha n else 0

/-- The complementary product is fixed before using the inverse-product
identity. Both d-coprimality and coprimality to the right index remain. -/
theorem slice_eq (N d j l h e r m : ℕ) (b : ℕ → ℂ)
    (F0 F2 FM : ℝ → ℂ) (Q x t : ℝ) (alpha beta : ℂ) (k : ℤ) :
    (∑ n ∈ Icc 1 N, if d.Coprime (e*n) ∧ d*(h*(e*n)) ≤ N then
      (if n ∈ PRZZDyadic.cell N r then (Real.log n:ℂ)^m else 0) *
        row N d j l (fun _ => 1) b (PRZZMellinSeparation.scaledCutoff F0 Q)
          F2 FM alpha beta x t k (h*(e*n)) else 0) =
    ∑ q ∈ PRZZDyadic.cell N l,
      if d.Coprime e ∧ (h*e).Coprime q ∧ d*q ≤ N then
        (star (b (d*q))*F2 (d*q)*FM (x*q)/(q:ℂ)^beta*PRZZMellinSeparation.twist q t) *
        PRZZTypeICoprime.restrictedSum d q N
          ((-k)*(inverseResidue q (h*e):ℤ)) (freeWeight N d j h e r m F0 Q t alpha)
      else 0 := by
  classical
  have ifsum (p : Prop) [Decidable p] (s : Finset ℕ) (v : ℕ → ℂ) :
      (if p then ∑ q ∈ s, v q else 0) = ∑ q ∈ s, if p then v q else 0 := by
    by_cases hp : p <;> simp [hp]
  unfold row
  simp only [mul_sum,ite_mul,mul_ite,zero_mul,mul_zero,ifsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  have hq0 : 0 < q := (mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  simp only [PRZZTypeICoprime.restrictedSum,mul_sum,ifsum]
  apply sum_congr rfl
  intro n hn
  have hephase (he : (h*e).Coprime q) (hnq : n.Coprime q) :
      PRZZKloostermanInputs.e (-(k:ℝ)*inverseResidue q (h*(e*n))/q) =
      PRZZKloostermanInputs.e ((((-k)*(inverseResidue q (h*e):ℤ)):ℤ)*inverseResidue q n/q) := by
    simpa only [mul_assoc,Int.cast_neg] using
      PRZZInversePhase.phase_product q (h*e) n hq0 he hnq (-k)
  simp only [freeWeight,PRZZFreeLogCoprime.row,PRZZResidualRow.weight,
    Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_left,mul_assoc]
  by_cases hde : d.Coprime e <;> by_cases hdn : d.Coprime n <;>
    by_cases hhq : h.Coprime q <;> by_cases heq : e.Coprime q <;>
    by_cases hnq : n.Coprime q <;> by_cases hdq : d*q ≤ N <;>
    by_cases hcut : d*(h*(e*n)) ≤ N <;>
    by_cases hj : h*(e*n) ∈ PRZZDyadic.cell N j <;>
    by_cases hr : n ∈ PRZZDyadic.cell N r
  all_goals simp [hde,hdn,hhq,heq,hnq,hdq,hcut,hj,hr,mul_assoc]
  all_goals
    simp only [if_pos (And.intro hde hdn),if_pos (And.intro hhq (And.intro heq hnq)),
      if_pos (And.intro hde (And.intro hhq heq)),if_pos (And.intro hdn hnq)]
    have hp := hephase (Nat.coprime_mul_iff_left.mpr ⟨hhq,heq⟩) hnq
    simp only [Int.cast_mul,Int.cast_neg,Int.cast_natCast,neg_mul,mul_assoc] at hp
    rw [hp]
    ring

#print axioms slice_eq

/-- The actual transformed frequency has exactly the original gcd cost. -/
theorem slice_frequency_gcd (q h e : ℕ) (hq : 0 < q) (he : (h*e).Coprime q) (k : ℤ) :
    ((-k)*(inverseResidue q (h*e):ℤ)).natAbs.gcd q = k.natAbs.gcd q := by
  simpa only [Int.natAbs_neg] using PRZZTypeICost.frequency_gcd q (h*e) hq he (-k)

#print axioms slice_frequency_gcd
end XiPrime8845.PRZZFreeSource

import PRZZSourceGroupDI
import PRZZResidualRow

/-! Exact identification of the negative-frequency source row with the
positive-phase DI matrix for every actual HB cell. No norm is taken before
the rearrangement; all coprimality and sharp product masks are retained. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZActualRowRectangle
open PRZZActualBranchCells PRZZHBBranches PRZZActualSupportBoxes
set_option maxHeartbeats 3000000

def complexGroup (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) : ArithmeticFunction ℂ :=
  ⟨fun n => (group N b k s n:ℂ), by simp⟩

theorem split (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) :
    complexGroup N b k univ = complexGroup N b k s*complexGroup N b k (univ \ s) := by
  ext n
  change (group N b k univ n:ℂ) = _
  rw [group_split N b k s, mul_apply, mul_apply]
  push_cast
  rfl

theorem coefficient_eq (N d : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) :
    (PRZZResidualCoprime.restrict d (complexGroup N b k s) : ℕ → ℂ) =
      PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1) := by
  funext n
  simp [PRZZResidualCoprime.restrict,complexGroup,PRZZActualBranchDI.coefficient,Set.indicator]

theorem shrink_local (N E F : ℕ) (hE : E ≤ N) (hF : F ≤ N)
    (V A : ℝ) (h : ℕ) (r beta nu alpha w : ℕ → ℂ)
    (ha : ∀ n ≤ N, E < n → alpha n = 0) (hb : ∀ n ≤ N, F < n → beta n = 0) :
    PRZZWeightedDI.weighted N V N A N h r beta nu alpha w =
      PRZZWeightedDI.weighted N V F A E h r beta nu alpha w := by
  unfold PRZZWeightedDI.weighted
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  trans ∑ f ∈ Icc 1 F, if c.Coprime (h*f) then
    ∑ a ∈ Icc 1 ⌊A⌋₊, ∑ e ∈ Icc 1 N, if e.Coprime c then
      if e*f ≤ N then w (e*f)*(r c*beta f*(nu a*alpha e)*
        PRZZKloostermanInputs.e ((a:ℝ)*PRZZKloostermanInputs.inverseResidue c (h*e*f)/c)) else 0 else 0 else 0
  · symm
    apply sum_subset (Icc_subset_Icc le_rfl hF)
    intro f hf hnot
    have hz := hb f (mem_Icc.mp hf).2 (by have := (mem_Icc.mp hf).1; simpa [mem_Icc,this] using hnot)
    simp [hz]
  · apply sum_congr rfl; intro f hf
    split_ifs with hc
    · apply sum_congr rfl; intro a ha'
      symm
      apply sum_subset (Icc_subset_Icc le_rfl hE)
      intro e he hnot
      have hz := ha e (mem_Icc.mp he).2 (by have := (mem_Icc.mp he).1; simpa [mem_Icc,this] using hnot)
      simp [hz]
    · rfl

theorem row_eq (N d j l h : ℕ) (A : ℝ) (b : Branch)
    (k : Fin b.2.length → ℕ) (s : Finset (Fin b.2.length))
    (right nu : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x t : ℝ) :
    (∑ a ∈ Icc 1 ⌊A⌋₊, nu a * ∑ n ∈ Icc 1 N,
      if d.Coprime n ∧ d*(h*n) ≤ N then
        (group N b k univ n:ℂ)*PRZZSupportedBranches.row N d j l (fun _ => 1)
          right F1 F2 FM alpha beta x t (-(a:ℤ)) (h*n) else 0) =
    PRZZWeightedDI.weighted N N (upper N b k (univ \ s)) A (upper N b k s) h
      (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
      (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) nu
      (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
      (PRZZResidualRow.weight N d j h F1 alpha t) := by
  have he (n : ℕ) : (group N b k univ n:ℂ) =
      (complexGroup N b k s*complexGroup N b k (univ \ s)) n := by
    rw [← split]; rfl
  simp_rw [he]
  rw [PRZZResidualRow.row_eq,PRZZResidualWeighted.grouped_eq,coefficient_eq,coefficient_eq]
  apply shrink_local N _ _ (min_le_left _ _) (min_le_left _ _)
  · intro n hn hu
    simp [PRZZActualBranchDI.coefficient,vanishes N b k s n hn hu]
  · intro n hn hu
    simp [PRZZActualBranchDI.coefficient,vanishes N b k (univ \ s) n hn hu]

#print axioms split
#print axioms coefficient_eq
#print axioms shrink_local
#print axioms row_eq
end XiPrime8845.PRZZActualRowRectangle

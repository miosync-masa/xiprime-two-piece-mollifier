import PRZZActualRowRectangle

/-! Positive original frequencies produce the negative DI phase.
All coefficients, cutoffs and coprimality conditions remain unchanged. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZPositiveRow
open PRZZKloostermanInputs PRZZResidualCoprime PRZZGroupedConvolution PRZZWeightedDI
open PRZZSupportedBranches PRZZMellinSeparation PRZZAStarRectangles
open PRZZActualRowRectangle PRZZActualBranchCells PRZZHBBranches PRZZActualSupportBoxes
open PRZZResidualRow (weight)
set_option maxHeartbeats 3000000

def grouped (N d : ℕ) (V A : ℝ) (h : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) : ℂ :=
  ∑ c ∈ (Icc 1 ⌊V⌋₊).filter (fun c => c.Coprime h), ∑ a ∈ Icc 1 ⌊A⌋₊,
    ∑ n ∈ Icc 1 N, if d.Coprime n ∧ n.Coprime c then
      w n*(r c*nu a*e (-((a:ℝ)*inverseResidue c (h*n)/c))*(f*g) n) else 0

theorem grouped_eq (N d : ℕ) (V A : ℝ) (h : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) :
    grouped N d V A h r nu f g w =
      negative N V N A N h r (restrict d g) nu (restrict d f) w := by
  have he : grouped N d V A h r nu f g w =
      ∑ c ∈ (Icc 1 ⌊V⌋₊).filter (fun c => c.Coprime h), ∑ a ∈ Icc 1 ⌊A⌋₊,
        ∑ n ∈ Icc 1 N,
          (if n.Coprime c then w n*(r c*nu a*e (-((a:ℝ)*inverseResidue c (h*n)/c))) else 0)*
            (restrict d f*restrict d g) n := by
    simp_rw [← restrict_mul]
    unfold grouped
    apply sum_congr rfl; intro c hc
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro n hn
    change (if d.Coprime n ∧ n.Coprime c then _ else 0) =
      (if n.Coprime c then _ else 0)*(if d.Coprime n then (f*g) n else 0)
    split_ifs <;> simp_all [mul_assoc]
  rw [he]
  simp_rw [weighted_convolution]
  unfold negative
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  split_ifs with hr
  · simp only [Nat.coprime_mul_iff_right]
    conv_lhs => enter [2,a]; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    by_cases hmc : m.Coprime c
    · rw [if_pos ⟨hr,hmc.symm⟩]
      simp_rw [Nat.coprime_mul_iff_left]
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro n hn
      by_cases hnc : n.Coprime c <;> by_cases hcut : n*m ≤ N <;>
        simp [hnc,hmc,hcut,Nat.coprime_mul_iff_left,mul_assoc] <;> ring
      rw [if_pos ⟨hnc,hmc⟩,if_pos hnc]
    · simp [Nat.coprime_mul_iff_left,hmc,show ¬c.Coprime m from fun h => hmc h.symm]
  · simp [hr,Nat.coprime_mul_iff_right]


theorem source_row_eq (N d j l h : ℕ) (A : ℝ) (b nu : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (f g : ArithmeticFunction ℂ) :
    (∑ a ∈ Icc 1 ⌊A⌋₊, nu a * ∑ n ∈ Icc 1 N,
      if d.Coprime n ∧ d*(h*n) ≤ N then
        (f*g) n*row N d j l (fun _ => 1) b F1 F2 FM α β x t (a:ℤ) (h*n) else 0) =
      grouped N d N A h (secondCoeff N d l b F2 FM β x t) nu f g (weight N d j h F1 α t) := by
  have ifsum (p : Prop) [Decidable p] (s : Finset ℕ) (v : ℕ → ℂ) :
      (if p then ∑ c ∈ s, v c else 0) = ∑ c ∈ s, if p then v c else 0 := by
    by_cases hp : p <;> simp [hp]
  unfold row grouped secondCoeff weight
  simp only [Nat.floor_natCast,PRZZDyadic.cell,sum_filter,mem_filter]
  simp only [mul_sum,ite_mul,mul_ite,zero_mul,mul_zero,ifsum]
  conv_lhs => enter [2,a]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro n hn
  have hc1 := (mem_Icc.mp hc).1
  have hn1 := (mem_Icc.mp hn).1
  simp only [hc,true_and,Nat.coprime_mul_iff_left,
    Int.cast_neg,Int.cast_natCast,neg_neg,one_mul,neg_mul,neg_div]
  by_cases hhc : h.Coprime c <;> by_cases hnc : n.Coprime c <;>
    by_cases hdn : d.Coprime n <;> by_cases hcut : d*(h*n) ≤ N <;>
    by_cases hdc : d*c ≤ N <;> by_cases hj : h*n ∈ Icc 1 N ∧ Nat.log 2 (h*n)=j <;>
    by_cases hl : Nat.log 2 c=l <;>
    simp [hhc,hnc,hdn,hcut,hdc,hj,hl,Nat.coprime_comm,mul_assoc] <;> ring_nf
  all_goals split_ifs <;> simp_all [Nat.coprime_comm]


theorem negative_shrink_local (N E F : ℕ) (hE : E ≤ N) (hF : F ≤ N)
    (V A : ℝ) (h : ℕ) (r beta nu alpha w : ℕ → ℂ)
    (ha : ∀ n ≤ N, E < n → alpha n = 0) (hb : ∀ n ≤ N, F < n → beta n = 0) :
    negative N V N A N h r beta nu alpha w = negative N V F A E h r beta nu alpha w := by
  rw [negative_eq,negative_eq]
  congr 1
  apply PRZZActualRowRectangle.shrink_local N E F hE hF
  · intro n hn he; simp [ha n hn he]
  · intro n hn hf; simp [hb n hn hf]

theorem actual_row_eq (N d j l h : ℕ) (A : ℝ) (b : Branch)
    (k : Fin b.2.length → ℕ) (s : Finset (Fin b.2.length))
    (right nu : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x t : ℝ) :
    (∑ a ∈ Icc 1 ⌊A⌋₊, nu a * ∑ n ∈ Icc 1 N,
      if d.Coprime n ∧ d*(h*n) ≤ N then
        (group N b k univ n:ℂ)*PRZZSupportedBranches.row N d j l (fun _ => 1)
          right F1 F2 FM alpha beta x t (a:ℤ) (h*n) else 0) =
    PRZZWeightedDI.negative N N (upper N b k (univ \ s)) A (upper N b k s) h
      (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
      (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) nu
      (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
      (PRZZResidualRow.weight N d j h F1 alpha t) := by
  have he (n : ℕ) : (group N b k univ n:ℂ) =
      (complexGroup N b k s*complexGroup N b k (univ \ s)) n := by
    rw [← split]; rfl
  simp_rw [he]
  rw [source_row_eq,grouped_eq,coefficient_eq,coefficient_eq]
  apply negative_shrink_local N _ _ (min_le_left _ _) (min_le_left _ _)
  · intro n hn hu
    simp [PRZZActualBranchDI.coefficient,vanishes N b k s n hn hu]
  · intro n hn hu
    simp [PRZZActualBranchDI.coefficient,vanishes N b k (univ \ s) n hn hu]


#print axioms grouped_eq
#print axioms source_row_eq
#print axioms negative_shrink_local
#print axioms actual_row_eq
end XiPrime8845.PRZZPositiveRow

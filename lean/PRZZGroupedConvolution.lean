import PRZZFullHeathBrown
import PRZZSignedTypeII
import PRZZSmoothMellin

/-! Exact factor regrouping with the product cutoff kept visible.
The weight may contain the original dyadic restriction, coprimality,
complex powers and exponential phase. No restricted cancellation bound
is inferred by deleting that weight. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZGroupedConvolution
set_option maxHeartbeats 2000000

theorem weighted_convolution (N : ℕ) (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, w n*(f*g) n) =
      ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        if e*m ≤ N then w (e*m)*f e*g m else 0 := by
  simp only [mul_apply,mul_sum]
  trans ∑ n ∈ Icc 1 N, ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1*p.2=n),
    w n*(f p.1*g p.2)
  · apply sum_congr rfl
    intro n hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
      (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2]
    rfl
  · simp only [sum_filter]
    rw [sum_comm,Finset.sum_product]
    apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro m hm
    have hpos : 1 ≤ e*m := by nlinarith [(mem_Icc.mp he).1,(mem_Icc.mp hm).1]
    simp [mem_Icc,hpos,mul_assoc]

/-- Any grouping of the factor list has exactly the grouped convolution.
This is an equality of arithmetic functions, before introducing weights. -/
theorem regroup_factors (fs left right : List (ArithmeticFunction ℂ))
    (hp : fs.Perm (left++right)) : fs.prod = left.prod*right.prod := by
  rw [hp.prod_eq,List.prod_append]

/-- A grouped factor list in an original weighted sum retains e*m <= N.
In particular a dyadic/product restriction inside w cannot be dropped. -/
theorem factor_sum (N : ℕ) (fs left right : List (ArithmeticFunction ℂ))
    (hp : fs.Perm (left++right)) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, w n*fs.prod n) =
      ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        if e*m ≤ N then w (e*m)*left.prod e*right.prod m else 0 := by
  rw [regroup_factors fs left right hp]
  exact weighted_convolution N left.prod right.prod w

def box (E : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ E then f n else 0, by simp⟩

/-- Two separately truncated factor groups give a genuine rectangular
convolution. This does not identify a sharp cutoff on their product with
separate cutoffs. -/
theorem boxed_weighted (E F : ℕ) (hE : 0 < E) (hF : 0 < F)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 (E*F), w n*(box E f*box F g) n) =
      ∑ e ∈ Icc 1 E, ∑ m ∈ Icc 1 F, w (e*m)*f e*g m := by
  rw [weighted_convolution]
  have heN : E ≤ E*F := Nat.le_mul_of_pos_right E hF
  have hfN : F ≤ E*F := by simpa [mul_comm] using Nat.le_mul_of_pos_right F hE
  symm
  trans ∑ e ∈ Icc 1 E, ∑ m ∈ Icc 1 (E*F),
    if e*m ≤ E*F then w (e*m)*(box E f) e*(box F g) m else 0
  · apply sum_congr rfl
    intro e he
    trans ∑ m ∈ Icc 1 F,
      if e*m ≤ E*F then w (e*m)*(box E f) e*(box F g) m else 0
    · apply sum_congr rfl
      intro m hm
      have hp := Nat.mul_le_mul (mem_Icc.mp he).2 (mem_Icc.mp hm).2
      simp [box,(mem_Icc.mp he).2,(mem_Icc.mp hm).2,hp]
    · apply sum_subset (Icc_subset_Icc le_rfl hfN)
      intro m hm hnot
      have hn : ¬m ≤ F := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,h⟩)
      simp [box,hn]
  · apply sum_subset (Icc_subset_Icc le_rfl heN)
    intro e he hnot
    have hn : ¬e ≤ E := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp he).1,h⟩)
    simp [box,hn]

#print axioms weighted_convolution
#print axioms regroup_factors
#print axioms factor_sum
#print axioms boxed_weighted
end XiPrime8845.PRZZGroupedConvolution

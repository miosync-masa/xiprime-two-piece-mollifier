import PRZZL1Finite

/-! Rectangular cutoff removal for the literal direct AFE sum.
Joint summability is an explicit hypothesis, not a claimed property of
the unconstructed gamma-ratio kernel. No limit/integral exchange occurs. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.PRZZL1Truncation
open PRZZL1Finite

theorem positive_sum (f : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Icc 1 M, f n) = ∑ n ∈ range M, f (n+1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_Icc_succ_top (by omega),sum_range_succ,ih]

theorem rectangles_tendsto :
    Tendsto (fun M : ℕ => (range M) ×ˢ (range M)) atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro M N hMN
    exact Finset.product_subset_product (range_mono hMN) (range_mono hMN)
  · intro p
    exact ⟨max p.1 p.2+1,by simp only [mem_product,mem_range]; omega⟩

theorem directSum_tendsto (alpha beta : ℂ) (V : ℕ → ℝ → ℂ) (t : ℝ)
    (hs : Summable (fun p : ℕ × ℕ => directTerm alpha beta V t (p.1+1) (p.2+1))) :
    Tendsto (fun M => directSum M alpha beta V t) atTop
      (nhds (∑' p : ℕ × ℕ, directTerm alpha beta V t (p.1+1) (p.2+1))) := by
  have h := hs.hasSum.comp rectangles_tendsto
  simpa only [directSum,positive_sum,Finset.sum_product,Function.comp_def] using h

#print axioms positive_sum
#print axioms rectangles_tendsto
#print axioms directSum_tendsto
end XiPrime8845.PRZZL1Truncation

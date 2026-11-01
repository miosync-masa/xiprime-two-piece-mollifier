import PRZZHBAtomSupply
import PRZZDyadicSupport

/-! Duplicate-preserving index groups for every literal HB branch.
Partitions act on Fin length, never on a set of coefficient values. The
dyadic scales and nonzero tuple conditions remain explicit inputs. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZBranchGrouping
open PRZZHBBranches PRZZHBAtomSupply PRZZGroupBounds PRZZTypedClassification PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

def factor (b : Branch) (i : Fin b.2.length) : ArithmeticFunction ℝ := b.2[i]

theorem factor_prod (b : Branch) : (∏ i, factor b i) = b.2.prod := by
  change (∏ i : Fin b.2.length, b.2[i]) = b.2.prod
  rw [← List.prod_ofFn]
  have he : List.ofFn (fun i : Fin b.2.length => b.2[i]) = b.2 := by
    apply List.ext_getElem
    · simp
    · intro n hn hn'
      simp
  exact congrArg List.prod he

theorem subset_product {ι : Type*} [DecidableEq ι] {R : Type*} [CommMonoid R]
    (s t : Finset ι) (ht : t ⊆ s) (f : ι → R) :
    (∏ i ∈ s, f i) = (∏ i ∈ t, f i)*(∏ i ∈ s \ t, f i) := by
  rw [mul_comm]
  exact (prod_sdiff ht).symm

/-- No branch scalar is discarded, including signed/repeated branches. -/
theorem branch_grouped (b : Branch) (t : Finset (Fin b.2.length)) :
    value b = b.1 • ((∏ i ∈ t, factor b i)*(∏ i ∈ univ \ t, factor b i)) := by
  rw [← subset_product univ t (subset_univ t),factor_prod]
  rfl

/-- The numerical Type II subset is now a concrete factorization of the
actual branch. Type I identifies a literal free weighted factor. -/
theorem classify_branch (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (m : Fin b.2.length → ℕ)
    (x : Fin b.2.length → ℝ) (U W : ℝ)
    (hW : 1 < W) (hx : ∀ i, 1 ≤ x i) (hp : ∏ i, x i = U)
    (hs : W^3 ≤ U) (hy : (y:ℝ) ≤ U/W)
    (hm : ∀ i, x i ≤ m i ∧ factor b i (m i) ≠ 0) :
    (∃ i, (∃ J a, Free a ∧ factor b i = weight J (atom a)) ∧
      U/W < x i ∧ (∏ j ∈ univ.erase i, x j) < W) ∨
    (∃ t : Finset (Fin b.2.length),
      W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ U/W ∧
      W ≤ ∏ i ∈ univ \ t, x i ∧ (∏ i ∈ univ \ t, x i) ≤ U/W ∧
      value b = b.1 • ((∏ i ∈ t, factor b i)*(∏ i ∈ univ \ t, factor b i))) := by
  have hh := branch_classify y K js b hb univ (factor b) m x U W
    (fun i _ => List.getElem_mem i.isLt) hW (fun i _ => hx i) hp hs hy (fun i _ => hm i)
  rcases hh with ⟨i,hi,hf,hbig,hrest⟩ | ⟨t,ht,hlo,hhi,hlo',hhi'⟩
  · exact Or.inl ⟨i,hf,hbig,hrest⟩
  · exact Or.inr ⟨t,hlo,hhi,hlo',hhi',branch_grouped b t⟩

#print axioms factor_prod
#print axioms subset_product
#print axioms branch_grouped
#print axioms classify_branch
end XiPrime8845.PRZZBranchGrouping

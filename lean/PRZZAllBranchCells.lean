import PRZZActualBranchCells
import PRZZLocalReexpansion

/-! Exact dyadic expansion of every occurrence of every HB branch.
The finite function index retains repeated factors; weighted sums can
keep arbitrary coprimality, sharp product and analytic restrictions. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZAllBranchCells
open PRZZBranchEnvelope PRZZBranchGrouping PRZZHBBranches PRZZActualBranchCells
set_option maxHeartbeats 2000000

theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp only [sum_insert ha,ArithmeticFunction.add_apply,ih]

theorem factor_partition (N n : ℕ) (hn : n ≤ N) (f : ArithmeticFunction ℝ) :
    (∑ k : Fin (Nat.log 2 N+1), mask (↑(PRZZDyadic.cell N k)) f) n = f n := by
  classical
  rw [eval_sum]
  by_cases hz : n=0
  · subst n; simp
  let k : Fin (Nat.log 2 N+1) := ⟨Nat.log 2 n,Nat.lt_succ_of_le (Nat.log_mono_right hn)⟩
  rw [sum_eq_single k]
  · have hc : n ∈ PRZZDyadic.cell N k := by
      simp [PRZZDyadic.cell,k,show 1 ≤ n by omega,hn]
    simp [mask,hc]
  · intro l hl hne
    have he : Nat.log 2 n ≠ l.val := by
      intro he
      apply hne
      apply Fin.ext
      exact he.symm
    simp [mask,PRZZDyadic.cell,he]
  · simp

theorem product_local {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ArithmeticFunction ℝ) (N : ℕ)
    (he : ∀ i ∈ s, ∀ n ≤ N, f i n = g i n) (n : ℕ) (hn : n ≤ N) :
    (∏ i ∈ s, f i) n = (∏ i ∈ s, g i) n := by
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha,prod_insert ha]
    exact PRZZFullHeathBrown.convolution_congr_below _ _ _ _ (N+1) n
      (fun m hm => he a (mem_insert_self _ _) m (by omega))
      (fun m hm => ih (fun i hi => he i (mem_insert_of_mem hi)) m (by omega)) (by omega)

/-- Literal indexed cells, matching group rather than a new coefficient proxy. -/
theorem branch_cells (N n : ℕ) (b : Branch) (hn : n ≤ N) :
    b.2.prod n = ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
      group N b (fun i => (k i).val) univ n := by
  classical
  rw [← factor_prod b]
  trans (∏ i : Fin b.2.length, ∑ k : Fin (Nat.log 2 N+1),
    mask (↑(PRZZDyadic.cell N k)) (factor b i)) n
  · apply product_local _ _ _ N _ n hn
    intro i hi m hm
    exact (factor_partition N m hm (factor b i)).symm
  · rw [Fintype.prod_sum,eval_sum]
    rfl

theorem weighted_branch (N : ℕ) (b : Branch) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, w n*(value b n:ℂ)) =
      ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
        ∑ n ∈ Icc 1 N, w n*(b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ) := by
  classical
  trans ∑ n ∈ Icc 1 N, ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
    w n*(b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ)
  · apply sum_congr rfl
    intro n hn
    change w n*((b.1*b.2.prod n:ℝ):ℂ) = _
    rw [Complex.ofReal_mul]
    rw [branch_cells N n b (mem_Icc.mp hn).2]
    push_cast
    simp only [mul_sum]
    apply sum_congr rfl; intros; ring
  · rw [sum_comm]

#print axioms factor_partition
#print axioms product_local
#print axioms branch_cells
#print axioms weighted_branch

theorem all_weighted (N : ℕ) (bs : List Branch) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, w n*(total bs n:ℂ)) =
      (bs.map (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
        ∑ n ∈ Icc 1 N, w n*(b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ))).sum := by
  induction bs with
  | nil => simp [total]
  | cons b bs ih =>
    have he : total (b::bs) = value b+total bs := by simp [total]
    simp only [he,ArithmeticFunction.add_apply,Complex.ofReal_add,mul_add,sum_add_distrib,
      List.map_cons,List.sum_cons]
    rw [ih,weighted_branch]

/-- Re-expands the original whole coefficient locally and then all its
ordered branches. w can contain the literal row, coprimality and phase. -/
theorem local_all (N M K : ℕ) (js : List ℕ) (hK : 0 < K) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Icc 1 N, M < n → w n = 0) :
    (∑ n ∈ Icc 1 N, w n*(PRZZGCoefficient.coefficient js n:ℂ)) =
      ((branches ⌊(M:ℝ)^((K:ℝ)⁻¹)⌋₊ K js).map
        (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
          ∑ n ∈ Icc 1 N, w n*(b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ))).sum := by
  rw [← all_weighted]
  apply sum_congr rfl
  intro n hn
  by_cases hm : n ≤ M
  · rw [PRZZLocalReexpansion.local_coefficient M K n js hK hm]
  · simp [hw n hn (lt_of_not_ge hm)]

#print axioms all_weighted
#print axioms local_all
end XiPrime8845.PRZZAllBranchCells

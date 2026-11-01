import PRZZBranchGrouping
import PRZZBranchEnvelope

/-! Suppliers for literal dyadic cells of every HB branch. A nonzero cell
supplies its own nonzero factor witnesses. Group envelopes are uniform in
the branch, the cutoff, the dyadic indices and the chosen index subset.
The numerical scale range remains explicit; this does not put Type I cells
into the balanced Type II case. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZActualBranchCells
open PRZZBranchGrouping PRZZBranchEnvelope PRZZHBBranches PRZZWeightedHeathBrown
open PRZZTypedClassification PRZZGroupBounds PRZZBranchDegrees
set_option maxHeartbeats 2000000

def piece (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ) (i : Fin b.2.length) :
    ArithmeticFunction ℝ := mask (↑(PRZZDyadic.cell N (k i))) (factor b i)

def group (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) : ArithmeticFunction ℝ := ∏ i ∈ s, piece N b k i

theorem group_split (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) :
    group N b k univ = group N b k s * group N b k (univ \ s) :=
  subset_product univ s (subset_univ s) _

/-- No nonzero tuple premise: the actual cell itself supplies witnesses. -/
theorem witnesses (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (hn : group N b k univ ≠ 0) :
    ∃ m : Fin b.2.length → ℕ, ∀ i,
      (2:ℝ)^(k i) ≤ m i ∧ factor b i (m i) ≠ 0 := by
  classical
  have hp (i : Fin b.2.length) : piece N b k i ≠ 0 := by
    intro hi
    apply hn
    unfold group
    exact prod_eq_zero (mem_univ i) hi
  have hm (i : Fin b.2.length) : ∃ n, piece N b k i n ≠ 0 := by
    by_contra h
    apply hp i
    ext n
    simpa using not_exists.mp h n
  choose m hm using hm
  refine ⟨m,?_⟩
  intro i
  have h := hm i
  by_cases hc : m i ∈ PRZZDyadic.cell N (k i)
  · refine ⟨by exact_mod_cast (PRZZDyadic.mem_cell _ _ _ |>.mp hc).2.1,?_⟩
    simpa [piece,mask,hc] using h
  · simp [piece,mask,hc] at h

/-- All cells: zero, a literal free Type I factor, or a balanced pair of
actual masked convolution groups. Repeated factors retain their indices. -/
theorem classify (N y K : ℕ) (js : List ℕ) (b : Branch) (hb : b ∈ branches y K js)
    (k : Fin b.2.length → ℕ) (U W : ℝ) (hW : 1 < W)
    (hprod : ∏ i, (2:ℝ)^(k i) = U) (hscale : W^3 ≤ U) (hshort : (y:ℝ) ≤ U/W) :
    group N b k univ = 0 ∨
    (∃ i, (∃ J a, Free a ∧ factor b i = weight J (atom a)) ∧
      U/W < (2:ℝ)^(k i) ∧ (∏ j ∈ univ.erase i, (2:ℝ)^(k j)) < W) ∨
    (∃ s : Finset (Fin b.2.length),
      W ≤ ∏ i ∈ s, (2:ℝ)^(k i) ∧ (∏ i ∈ s, (2:ℝ)^(k i)) ≤ U/W ∧
      W ≤ ∏ i ∈ univ \ s, (2:ℝ)^(k i) ∧ (∏ i ∈ univ \ s, (2:ℝ)^(k i)) ≤ U/W ∧
      group N b k univ = group N b k s * group N b k (univ \ s)) := by
  classical
  by_cases hn : group N b k univ = 0
  · exact Or.inl hn
  obtain ⟨m,hm⟩ := witnesses N b k hn
  rcases classify_branch y K js b hb m (fun i => (2:ℝ)^(k i)) U W hW
    (fun i => one_le_pow₀ (by norm_num)) hprod hscale hshort hm with hi | hii
  · exact Or.inr (Or.inl hi)
  · obtain ⟨s,h1,h2,h3,h4,_⟩ := hii
    exact Or.inr (Or.inr ⟨s,h1,h2,h3,h4,group_split N b k s⟩)

/-- A single constant for every actual index group, not a supplied
coefficient envelope. It also covers both complementary balanced groups. -/
theorem common_envelope (K : ℕ) (js : List ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y b, b ∈ branches y K js →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ n : ℕ, 0 < n → |group N b k s n| ≤ C*(n:ℝ)^eps := by
  classical
  obtain ⟨C,hC,h⟩ := bounded_product js.sum ((js.length+1)*(2*K)) eps heps
  refine ⟨C,hC,?_⟩
  intro N y b hb k s n hn
  have hl : (s.toList.map (piece N b k)).length ≤ (js.length+1)*(2*K) := by
    simp only [List.length_map,Finset.length_toList]
    exact (card_le_card (subset_univ s)).trans (by simpa using branches_length y K js b hb)
  have hf : ∀ f ∈ s.toList.map (piece N b k), Bounded y js.sum f := by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
    exact mask_bounded y js.sum _ _
      (branches_degrees y K js b hb _ (List.getElem_mem i.isLt))
  have hh := h y _ hl hf n hn
  simpa only [Finset.prod_map_toList,group] using hh

/-- Coprimality masks and unit Mellin twists may be applied to either
actual group. The same C is fixed before all branches and rectangle sizes. -/
theorem common_rectangle (K : ℕ) (js : List ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y b, b ∈ branches y K js →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ q : Set ℕ, ∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
      ∀ X : ℝ, 1 ≤ X → ∀ n ∈ Icc 1 ⌊X⌋₊,
        ‖q.indicator (fun n => (group N b k s n:ℂ)*w n) n‖ ≤ C*X^eps := by
  classical
  obtain ⟨C,hC,h⟩ := common_envelope K js eps heps
  refine ⟨C,hC,?_⟩
  intro N y b hb k s q w hw X hX n hn
  by_cases hq : n ∈ q
  · simp only [Set.indicator_of_mem hq,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (hw n) (abs_nonneg _)).trans
    rw [mul_one]
    exact (h N y b hb k s n (mem_Icc.mp hn).1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))) heps.le) hC.le)
  · simp only [Set.indicator_of_notMem hq,norm_zero]
    positivity

theorem group_support (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (n : ℕ) (hn : group N b k s n ≠ 0) :
    (∏ i ∈ s, 2^(k i)) ≤ n ∧ n ≤ ∏ i ∈ s, 2^(k i+1) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    have he : n = 1 := by
      by_contra he
      exact hn (by simp [group,one_apply,he])
    simp [he]
  | @insert i s hi ih =>
    by_contra h
    apply hn
    simp only [group,prod_insert hi]
    rw [mul_apply]
    apply sum_eq_zero
    intro p hp
    by_cases h1 : piece N b k i p.1 = 0
    · simp [h1]
    by_cases h2 : group N b k s p.2 = 0
    · change piece N b k i p.1 * group N b k s p.2 = 0
      rw [h2,mul_zero]
    have hc : p.1 ∈ PRZZDyadic.cell N (k i) := by
      by_contra hc
      exact h1 (by simp [piece,mask,hc])
    have hb := (PRZZDyadic.mem_cell _ _ _).mp hc
    have hg := ih p.2 h2
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    apply (h ?_).elim
    rw [prod_insert hi,prod_insert hi,← he]
    exact ⟨Nat.mul_le_mul hb.2.1 hg.1,Nat.mul_le_mul hb.2.2.le hg.2⟩

/-- The actual selected group has its full product support. The upper
endpoint carries one factor 2 for each occurrence, including duplicates. -/
theorem balanced_support (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (U W : ℝ)
    (hlo : W ≤ ∏ i ∈ s, (2:ℝ)^(k i))
    (hhi : (∏ i ∈ s, (2:ℝ)^(k i)) ≤ U/W)
    (n : ℕ) (hn : group N b k s n ≠ 0) :
    W ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2^s.card*(U/W) := by
  have hg := group_support N b k s n hn
  have hl : (∏ i ∈ s, (2:ℝ)^(k i)) ≤ n := by exact_mod_cast hg.1
  have hu : (n:ℝ) ≤ ∏ i ∈ s, (2:ℝ)^(k i+1) := by exact_mod_cast hg.2
  have he : (∏ i ∈ s, (2:ℝ)^(k i+1)) = 2^s.card*(∏ i ∈ s, (2:ℝ)^(k i)) := by
    simp_rw [pow_succ]
    rw [prod_mul_distrib,prod_const,mul_comm]
  exact ⟨hlo.trans hl,hu.trans (he.le.trans (mul_le_mul_of_nonneg_left hhi (by positivity)))⟩

/-- The regrouping preserves any original sharp cutoff and arithmetic
or analytic weight w. This is a finite identity, before applying a norm. -/
theorem weighted_group_split (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (q : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ q, w n * (b.1 * group N b k univ n:ℂ)) =
      ∑ n ∈ q, w n * (b.1 * (group N b k s * group N b k (univ \ s)) n:ℂ) := by
  rw [group_split N b k s]

#print axioms group_split
#print axioms witnesses
#print axioms classify
#print axioms common_envelope
#print axioms common_rectangle
#print axioms group_support
#print axioms balanced_support
#print axioms weighted_group_split
end XiPrime8845.PRZZActualBranchCells

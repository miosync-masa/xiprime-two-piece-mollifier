import PRZZActualAggregate

/-! A common constant for a fixed finite set of scale indices. This does
NOT turn height-dependent grids into a height-independent finite set.
The seven actual cap components and labelled allocation multiplicities
are retained in the budget comparison. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZIndexedCaps
open PRZZActualAggregate
set_option maxHeartbeats 6000000

def constantCaps (B : ℝ) (hB : 0 < B) : Caps :=
  ⟨B,B,B,B,B,B,B,hB,hB,hB,hB,hB,hB,hB⟩

def dominates (c e : Caps) : Prop := c.small ≤ e.small ∧ c.typeI ≤ e.typeI ∧
  c.g ≤ e.g ∧ c.di ≤ e.di ∧ c.right ≤ e.right ∧ c.phase ≤ e.phase ∧ c.variation ≤ e.variation

theorem row_mono (c e : Caps) (hc : dominates c e) (eps eta T A : ℝ)
    (N K j l : ℕ) (ks : List ℕ) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    row c eps eta T A N K j l ks ≤ row e eps eta T A N K j l ks := by
  rcases hc with ⟨hs,hi,hg,hd,hr,hp,hv⟩
  rcases c.positive with ⟨hs0,hi0,hg0,hd0,hr0,hp0,hv0⟩
  rcases e.positive with ⟨hs1,hi1,hg1,hd1,hr1,hp1,hv1⟩
  have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  unfold row PRZZActualCaseSum.smallBudget PRZZActualCaseSum.largeBudget PRZZCommonCellBound.budget
    PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
  dsimp only
  gcongr

theorem budget_mono (C E : ℝ) (w v : (List ℕ × List ℕ) → ℝ)
    (caps more : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (hC : 0 ≤ C) (hCE : C ≤ E) (hw : ∀ q, 0 ≤ w q)
    (hv : ∀ q ∈ PRZZCoefficientSeparation.allocations js, w q ≤ v q)
    (hc : ∀ q ∈ PRZZCoefficientSeparation.allocations js, dominates (caps q) (more q))
    (eps eta b T A : ℝ) (N d K : ℕ) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    totalBudget C w caps js eps eta b T A N d K ≤ totalBudget E v more js eps eta b T A N d K := by
  unfold totalBudget
  apply sum_le_sum; intro j hj
  apply sum_le_sum; intro l hl
  have he : 0 ≤ E := hC.trans hCE
  have hleft : 0 ≤ ((PRZZCoefficientSeparation.allocations js).map (fun q =>
      w q*T^eta*row (caps q) eps eta T A N K j l q.2)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (mul_nonneg (hw q) (Real.rpow_nonneg hT eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ hT hA)
  apply mul_le_mul
  · gcongr
  · apply List.sum_le_sum
    intro q hq
    have hr0 := row_nonneg (caps q) eps eta T A N K j l q.2 hT hA
    have hr1 := row_nonneg (more q) eps eta T A N K j l q.2 hT hA
    have hw0 := hw q
    have hv0 : 0 ≤ v q := hw0.trans (hv q hq)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hv q hq) (Real.rpow_nonneg hT eta))
      (row_mono _ _ (hc q hq) eps eta T A N K j l q.2 hT hA) hr0 (by positivity)
  · exact hleft
  · positivity

/-- A common scalar dominates every ACTUAL component on the fixed finite
scale/allocation set. Its dependence on that set is not suppressed. -/
theorem finite_caps {ι : Type*} (I : Finset ι) (qs : List (List ℕ × List ℕ))
    (C : ι → ℝ) (w : ι → (List ℕ × List ℕ) → ℝ)
    (caps : ι → (List ℕ × List ℕ) → Caps) :
    ∃ B : ℝ, ∃ hB : 0 < B, ∀ i ∈ I,
      C i ≤ B ∧ ∀ q ∈ qs, w i q ≤ B ∧ dominates (caps i q) (constantCaps B hB) := by
  classical
  let cost := fun i q => |w i q|+|(caps i q).small|+|(caps i q).typeI|+
    |(caps i q).g|+|(caps i q).di|+|(caps i q).right|+|(caps i q).phase|+|(caps i q).variation|
  let B := 1+∑ i ∈ I, (|C i|+∑ q ∈ qs.toFinset, cost i q)
  have hcost : ∀ i q, 0 ≤ cost i q := by intro i q; dsimp [cost]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro i hi
  have hi' := single_le_sum (fun j hj => show 0 ≤ |C j|+∑ q ∈ qs.toFinset, cost j q by positivity) hi
  refine ⟨?_,?_⟩
  · have hCi := le_abs_self (C i)
    have hz : 0 ≤ ∑ q ∈ qs.toFinset, cost i q := sum_nonneg (fun q hq => hcost i q)
    dsimp [B]; linarith
  · intro q hq
    have hq' := single_le_sum (fun r hr => hcost i r) (List.mem_toFinset.mpr hq)
    have hz := abs_nonneg (C i)
    have hh : cost i q ≤ B := by dsimp [B]; linarith
    dsimp [cost] at hh
    rcases (caps i q).positive with ⟨hsm,hti,hg,hdi,hr,hph,hv⟩
    simp only [abs_of_pos hsm,abs_of_pos hti,abs_of_pos hg,abs_of_pos hdi,
      abs_of_pos hr,abs_of_pos hph,abs_of_pos hv] at hh
    simp only [dominates,constantCaps]
    constructor
    · linarith [le_abs_self (w i q)]
    · exact ⟨by linarith [le_abs_self (caps i q).small,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).typeI,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).g,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).di,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).right,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).phase,abs_nonneg (w i q)],
        by linarith [le_abs_self (caps i q).variation,abs_nonneg (w i q)]⟩

/-- Uniform comparison for all heights and arithmetic data AFTER fixing
the finite scale set I. No supremum over an increasing I(T) is inferred. -/
theorem finite_budget_uniform {ι : Type*} (I : Finset ι)
    (C : ι → ℝ) (w : ι → (List ℕ × List ℕ) → ℝ)
    (caps : ι → (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (hC : ∀ i, 0 ≤ C i) (hw : ∀ i q, 0 ≤ w i q) :
    ∃ B : ℝ, ∃ hB : 0 < B, ∀ i ∈ I, ∀ eps eta b T A : ℝ, ∀ N d K : ℕ,
      0 ≤ T → 0 ≤ A →
      totalBudget (C i) (w i) (caps i) js eps eta b T A N d K ≤
        totalBudget B (fun _ => B) (fun _ => constantCaps B hB) js eps eta b T A N d K := by
  obtain ⟨B,hB,h⟩ := finite_caps I (PRZZCoefficientSeparation.allocations js) C w caps
  refine ⟨B,hB,?_⟩
  intro i hi eps eta b T A N d K hT hA
  have hb := h i hi
  exact budget_mono (C i) B (w i) (fun _ => B) (caps i) (fun _ => constantCaps B hB) js
    (hC i) hb.1 (hw i) (fun q hq => (hb.2 q hq).1) (fun q hq => (hb.2 q hq).2)
    eps eta b T A N d K hT hA

#print axioms finite_budget_uniform
#print axioms row_mono
#print axioms budget_mono
#print axioms finite_caps
end XiPrime8845.PRZZIndexedCaps

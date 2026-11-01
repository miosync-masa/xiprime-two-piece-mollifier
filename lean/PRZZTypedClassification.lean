import PRZZGroupBounds
import PRZZDyadic

/-! Type I/II numerical classification with the short-Mobius exclusion
proved for typed HB factors. A large free atom may still carry a mask;
Type I smooth variation is a separate analytic obligation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZTypedClassification
open PRZZGroupBounds PRZZWeightedHeathBrown
set_option maxHeartbeats 2000000

def Free : Atom → Prop
  | .mu _ => False
  | .zeta => True
  | .log => True
  | .restrict a _ => Free a

def Short (Y : ℝ) : Atom → Prop
  | .mu y => (y:ℝ) ≤ Y
  | .zeta => True
  | .log => True
  | .restrict a _ => Short Y a

/-- A nonzero factor above the common short cutoff cannot be Mobius. -/
theorem large_free (a : Atom) (J n : ℕ) (Y : ℝ) (hshort : Short Y a)
    (hn : Y < n) (hne : weight J (atom a) n ≠ 0) : Free a := by
  classical
  induction a with
  | mu y =>
    have hy : ¬n ≤ y := by
      intro h
      have hh : (n:ℝ) ≤ y := by exact_mod_cast h
      exact (not_lt_of_ge (hh.trans hshort)) hn
    exfalso
    apply hne
    change Real.log n^J*(if n ≤ y then PRZZ.muReal n else 0) = 0
    simp [hy]
  | zeta => trivial
  | log => trivial
  | restrict a s ih =>
    apply ih hshort
    intro hz
    apply hne
    change Real.log n^J*(if n ∈ s then atom a n else 0) = 0
    split_ifs
    · exact hz
    · ring

/-- A dyadic scale x_i is bounded by a nonzero representative m_i.
The Type I alternative explicitly identifies a free (possibly masked)
atom, while Type II supplies two complementary product ranges. -/
theorem classify_typed {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → Atom) (J m : ι → ℕ) (x : ι → ℝ) (U W : ℝ)
    (hW : 1 < W) (hx : ∀ i ∈ s, 1 ≤ x i)
    (hprod : ∏ i ∈ s, x i = U) (hscale : W^3 ≤ U)
    (hshort : ∀ i ∈ s, Short (U/W) (a i))
    (hm : ∀ i ∈ s, x i ≤ m i ∧ weight (J i) (atom (a i)) (m i) ≠ 0) :
    (∃ i ∈ s, Free (a i) ∧ U/W < x i ∧ (∏ j ∈ s.erase i, x j) < W) ∨
    (∃ t ⊆ s, W ≤ ∏ i ∈ t, x i ∧ (∏ i ∈ t, x i) ≤ U/W ∧
      W ≤ ∏ i ∈ s \ t, x i ∧ (∏ i ∈ s \ t, x i) ≤ U/W) := by
  rcases PRZZDyadic.classify s x U W hW hx hprod hscale with h | h
  · obtain ⟨i,hi,hbig,hrest⟩ := h
    exact Or.inl ⟨i,hi,large_free (a i) (J i) (m i) (U/W) (hshort i hi)
      (hbig.trans_le (hm i hi).1) (hm i hi).2,hbig,hrest⟩
  · exact Or.inr h

/-- Orient the complementary groups by their size. With W=U^(1/4),
the smaller group lies in the exact seven-term balanced range. -/
theorem orient_groups (E F U W : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hprod : E*F=U) (hWE : W ≤ E) (hWF : W ≤ F) :
    W ≤ min E F ∧ min E F ≤ Real.sqrt U ∧ min E F*max E F=U := by
  have hU : 0 ≤ U := hprod ▸ mul_nonneg hE hF
  have hs := Real.sq_sqrt hU
  refine ⟨le_min hWE hWF,?_,?_⟩
  · by_cases h : E ≤ F
    · rw [min_eq_left h]
      nlinarith [Real.sqrt_nonneg U,mul_le_mul_of_nonneg_left h hE]
    · rw [min_eq_right (le_of_not_ge h)]
      nlinarith [Real.sqrt_nonneg U,mul_le_mul_of_nonneg_left (le_of_not_ge h) hF]
  · by_cases h : E ≤ F
    · rwa [min_eq_left h,max_eq_right h]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),mul_comm,hprod]

#print axioms large_free
#print axioms classify_typed
#print axioms orient_groups
end XiPrime8845.PRZZTypedClassification

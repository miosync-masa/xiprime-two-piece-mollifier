import PRZZPrunedAFEError
import PRZZNativeGcdGrid

/-! Selected native components of the actual retained field. Every
native gap and the small-gap branch remains in the same row; the cutoff
complement is not silently replaced by a rectangle. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZRetainedNative
open PRZZNativeComponents PRZZNativeFamily
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def selectedPart (part : Part) (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ PRZZAFEIndices.labels L N, if z.2.1 ≠ 0 ∧ R s z then
    ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, if PRZZWRowReindex.pairMatches z n r then
      row part L J (PRZZWRowLimit.profile F) G H ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-z.2.1,1)) alpha beta a (Nat.gcd n r) t
    else 0 else 0

theorem selected_decomposition (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    PRZZSourceMaskFamily.selectedFamily L J N F G H a R alpha beta t =
      selectedPart .central L J N F G H a R alpha beta t+
      selectedPart .tail L J N F G H a R alpha beta t-
      selectedPart .boundary L J N F G H a R alpha beta t+
      selectedPart .freeze L J N F G H a R alpha beta t+
      selectedPart .outside L J N F G H a R alpha beta t := by
  unfold PRZZSourceMaskFamily.selectedFamily selectedPart
  simp only [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro z hz
  split_ifs
  · simp only [← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl; intro n hn
    apply sum_congr rfl; intro r hr
    split_ifs
    · exact row_decomposition L J (PRZZWRowLimit.profile F) G H _ _ alpha beta a _ t
    · ring
  · ring

theorem selected_reindex (part : Part) (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    selectedPart part L J N F G H a R alpha beta t =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          ∑ delta ∈ gaps L N (d*u) (d*v),
            if delta ≠ 0 ∧ R s (pairLabel (d*u) (d*v) delta) then
              row part L J (PRZZWRowLimit.profile F) G H ((2:ℝ)^s)
                ((u,v),(-delta,1)) alpha beta a d t else 0 else 0 := by
  unfold selectedPart
  apply sum_congr rfl; intro s hs
  trans ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, ∑ delta ∈ gaps L N n r,
    if delta ≠ 0 ∧ R s (pairLabel n r delta) then
      row part L J (PRZZWRowLimit.profile F) G H ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta a (Nat.gcd n r) t else 0
  · rw [← all_pairs]
    apply sum_congr rfl; intro z hz
    by_cases hh : z.2.1 ≠ 0 ∧ R s z
    · simp only [if_pos hh]
      apply sum_congr rfl; intro n hn
      apply sum_congr rfl; intro r hr
      by_cases hp : PRZZWRowReindex.pairMatches z n r
      · rw [matching_label z n r hp]; simp [hp,hh]
      · simp [hp]
    · simp only [if_neg hh]
      symm
      apply sum_eq_zero; intro n hn
      apply sum_eq_zero; intro r hr
      by_cases hp : PRZZWRowReindex.pairMatches z n r
      · rw [matching_label z n r hp]; simp [hp,hh]
      · simp [hp]
  · exact PRZZNativeGcdGrid.sum_reindex N (fun n r d u v =>
      ∑ delta ∈ gaps L N n r, if delta ≠ 0 ∧ R s (pairLabel n r delta) then
        row part L J (PRZZWRowLimit.profile F) G H ((2:ℝ)^s)
          ((u,v),(-delta,1)) alpha beta a d t else 0)

/-- The actual retained field, not a newly supplied central family.
Four other native components and the valued cutoff complement remain. -/
theorem kept_decomposition (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t =
      (PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
       PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)+
      (selectedPart .central L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
       selectedPart .tail L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t-
       selectedPart .boundary L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
       selectedPart .freeze L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
       selectedPart .outside L J N (fun x => (P x:ℂ))
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t) := by
  rw [PRZZPrunedAFEError.kept_field_partition,selected_decomposition]

#print axioms selected_decomposition
#print axioms selected_reindex
#print axioms kept_decomposition
end XiPrime8845.PRZZRetainedNative

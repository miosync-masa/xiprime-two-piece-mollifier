import PRZZArithmeticCutoffPartition

/-! Row-local Fourier cutoffs on the actual selected native grid.
Central and infinite tail are transported together; their difference is
an explicit central-band transfer, never an omitted intermediate band. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZSelectedLocalFourier
open PRZZNativeComponents PRZZRetainedNative
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def sourceCutoff (T eH : ℝ) (s _d _u v : ℕ) (_delta : ℤ) : ℕ :=
  ⌈PRZZSourceCutoffs.poissonCutoff 1 T ((2:ℝ)^s) (v:ℝ) eH⌉₊

/-- Exactly the normalized cutoff appearing inside nativeMass's paired
tail: modulus one and the reduced right length v, not the original V/d. -/
theorem source_tail (L s d u v : ℕ) (delta : ℤ) (W G H : ℝ → ℂ)
    (a : ℕ → ℂ) (T eH t : ℝ) (A B : ℂ) :
    row .tail L (sourceCutoff T eH s d u v delta) W G H ((2:ℝ)^s)
      ((u,v),(-delta,1)) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) a d t =
      if |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 then
        (PRZZUnfrozenPoisson.arithmetic a G H d (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ))
          ((u,v),(-delta,1))/((u:ℂ)*(v:ℂ)))*
        PRZZUnitTailMass.tail W ((2:ℝ)^s) T eH t A B (-delta) 1
          (PRZZCentralTail.residue ((u,v),(-delta,1))/v) (u,v) else 0 := by
  simp only [row,sourceCutoff,PRZZUnitTailMass.tail,add_div]

theorem row_central_tail (L J J' d : ℕ) (F G H : ℝ → ℂ) (M : ℝ)
    (z : PRZZAStar.Index) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hM : 0 < M) (ht : 0 < t) (hu : 0 < z.1.1) (hv : 0 < z.1.2)
    (hs : alpha+beta ≠ 0) :
    row .central L J F G H M z alpha beta a d t+
      row .tail L J F G H M z alpha beta a d t =
    row .central L J' F G H M z alpha beta a d t+
      row .tail L J' F G H M z alpha beta a d t := by
  have hp := PRZZCentralTail.poisson_split F hF hsF M 1
    (PRZZCentralTail.residue z/z.1.2) t z alpha beta (alpha+beta) J hM (by norm_num) ht hu hv hs
  have hq := PRZZCentralTail.poisson_split F hF hsF M 1
    (PRZZCentralTail.residue z/z.1.2) t z alpha beta (alpha+beta) J' hM (by norm_num) ht hu hv hs
  have he := hp.symm.trans hq
  simp only [row]
  split_ifs
  · simpa only [mul_add] using congrArg (fun c : ℂ =>
      (PRZZUnfrozenPoisson.arithmetic a G H d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ)))*c) he
  · rfl

def localPart (part : Part) (L N : ℕ) (Jloc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ)
    (F G H : ℝ → ℂ) (a : ℕ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if delta ≠ 0 ∧ R s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
          row part L (Jloc s d u v delta) (PRZZWRowLimit.profile F) G H ((2:ℝ)^s)
            ((u,v),(-delta,1)) alpha beta a d t else 0 else 0

theorem selected_central_tail (L J N : ℕ) (Jloc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ)
    (F G H : ℝ → ℂ) (a : ℕ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    (alpha beta : ℂ) (t : ℝ) (hF : ContDiff ℝ ∞ F)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (ht : 0 < t) (hs : alpha+beta ≠ 0) :
    selectedPart .central L J N F G H a R alpha beta t+
      selectedPart .tail L J N F G H a R alpha beta t =
    localPart .central L N Jloc F G H a R alpha beta t+
      localPart .tail L N Jloc F G H a R alpha beta t := by
  rw [selected_reindex,selected_reindex]
  unfold localPart
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro s hss
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had,← sum_add_distrib]
    apply sum_congr rfl; intro delta hdel
    split_ifs
    · have hp := PRZZWRowLimit.profile_regular F hF hleft hright
      exact row_central_tail L J (Jloc s d u v delta) d _ G H _ _ a alpha beta t
        hp.1 hp.2.2 (by positivity) ht (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs
    · simp
  · simp [had]

/-- The transferred band is exactly the change in the central block.
This identity works whether the local cutoff increases or decreases J. -/
theorem tail_transfer (L J N : ℕ) (Jloc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ)
    (F G H : ℝ → ℂ) (a : ℕ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    (alpha beta : ℂ) (t : ℝ) (hF : ContDiff ℝ ∞ F)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (ht : 0 < t) (hs : alpha+beta ≠ 0) :
    selectedPart .tail L J N F G H a R alpha beta t =
      localPart .tail L N Jloc F G H a R alpha beta t+
      (localPart .central L N Jloc F G H a R alpha beta t-
        selectedPart .central L J N F G H a R alpha beta t) := by
  have hh := selected_central_tail L J N Jloc F G H a R alpha beta t hF hleft hright ht hs
  linear_combination hh

/-- Substitute row-local central+tail into the actual selected family.
The boundary, freezing defect, and outside branch are still exact terms. -/
theorem selected_local_decomposition (L J N : ℕ) (Jloc : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ)
    (F G H : ℝ → ℂ) (a : ℕ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
    (alpha beta : ℂ) (t : ℝ) (hF : ContDiff ℝ ∞ F)
    (hleft : ∀ x ≤ (1/2:ℝ), F x = 1) (hright : ∀ x, 1 ≤ x → F x = 0)
    (ht : 0 < t) (hs : alpha+beta ≠ 0) :
    PRZZSourceMaskFamily.selectedFamily L J N F G H a R alpha beta t =
      localPart .central L N Jloc F G H a R alpha beta t+
      localPart .tail L N Jloc F G H a R alpha beta t-
      selectedPart .boundary L J N F G H a R alpha beta t+
      selectedPart .freeze L J N F G H a R alpha beta t+
      selectedPart .outside L J N F G H a R alpha beta t := by
  have hh := selected_central_tail L J N Jloc F G H a R alpha beta t hF hleft hright ht hs
  rw [selected_decomposition]
  linear_combination hh

/-- Both connections on the original full family: arithmetic partition
reconstruction and the native tail theorem's local cutoff. The single-
window cutoff complement is replaced by the exact partition, not bounded
as an error. Discarded rows, boundary and freezing terms stay explicit. -/
theorem partition_local (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps eH : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hPr : ∀ x, 1 ≤ x → P x = 0) (hK : (N:ℝ) ≤ (2:ℝ)^K/2)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0) (hT : 0 < T) (ht : 0 < t)
    (hs : alpha+beta ≠ 0) (hheight : 8 ≤ T^(1-eps)) :
    PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t =
    ∑ p ∈ range K ×ˢ range K,
      let g := PRZZMellinSeparation.scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
      let h := PRZZMellinSeparation.scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
      let R := fun s z => ¬PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z
      localPart .central L N (sourceCutoff T eH) F g h a R alpha beta t+
      localPart .tail L N (sourceCutoff T eH) F g h a R alpha beta t-
      selectedPart .boundary L J N F g h a R alpha beta t+
      selectedPart .freeze L J N F g h a R alpha beta t+
      PRZZSourceMaskFamily.selectedFamily L J N F g h a
        (PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps) alpha beta t := by
  rw [← PRZZArithmeticCutoffPartition.family_partition P F K L J N a alpha beta t hPl hPr hK]
  apply sum_congr rfl
  intro p hp
  dsimp only
  let g := PRZZMellinSeparation.scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
  let h := PRZZMellinSeparation.scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
  let R := fun s z => ¬PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z
  have he := selected_local_decomposition L J N (sourceCutoff T eH) F g h a R alpha beta t
    hF hFl hFr ht hs
  have hz := PRZZRejectedExhaustion.retained_outside_zero L J N F (PRZZWRowLimit.profile P)
    h a ((2:ℝ)^p.1) T eps alpha beta t (by positivity) hT
    (PRZZWRowLimit.profile_regular P hP hPl hPr).2.2 hheight
  change selectedPart .outside L J N F g h a R alpha beta t = 0 at hz
  rw [hz,add_zero] at he
  have hf := PRZZSourceMaskFamily.family_partition L J N F g h a
    (PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps) alpha beta t
  change PRZZAllPoissonRows.family L J N F g h a alpha beta t = _
  rw [he] at hf
  linear_combination hf

#print axioms row_central_tail
#print axioms source_tail
#print axioms selected_central_tail
#print axioms tail_transfer
#print axioms selected_local_decomposition
#print axioms partition_local
end XiPrime8845.PRZZSelectedLocalFourier

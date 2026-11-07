import PRZZLiteralAFEJoin

/-! Scope of the actual remainingField and lossless arithmetic reconstruction.
A single-window complement is not a negligible tail. Summing the uncorrected
keptField duplicates the complete field; remove that complement exactly once
before using the valued partition. No analytic smallness is asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory
namespace XiPrime8845.PRZZResidualPartition
open PRZZMellinSeparation PRZZAllPoissonRows PRZZFreezeRemovedLiteral PRZZIntegratedFreezeAFE
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem selected_zero (L J N : ℕ) (F H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    PRZZSourceMaskFamily.selectedFamily L J N F (fun _ => 0) H a R alpha beta t = 0 := by
  have hz (M : ℝ) (z : PRZZAStar.Index) (d : ℕ) :
      resolved L J (PRZZWRowLimit.profile F) (fun _ => 0) H M z alpha beta a d t = 0 := by
    rw [PRZZArithmeticCutoffPartition.resolved_values]
    simp
  unfold PRZZSourceMaskFamily.selectedFamily
  simp_rw [hz]
  simp

theorem selected_part_zero (part : PRZZNativeComponents.Part) (L J N : ℕ) (F H : ℝ → ℂ)
    (a : ℕ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    PRZZRetainedNative.selectedPart part L J N F (fun _ => 0) H a R alpha beta t = 0 := by
  have hz (M : ℝ) (z : PRZZAStar.Index) (d : ℕ) :
      PRZZNativeComponents.row part L J (PRZZWRowLimit.profile F) (fun _ => 0) H M z alpha beta a d t = 0 := by
    cases part <;> simp [PRZZNativeComponents.row,PRZZUnfrozenPoisson.arithmetic,PRZZUnfrozenPoisson.afeRow]
  unfold PRZZRetainedNative.selectedPart
  simp_rw [hz]
  simp

/-- Exact obstruction to treating arbitrary single-window remainingPair
as an analytic error: a zero valued cutoff leaves the complete field. -/
theorem remaining_zero_window (P : ℝ → ℝ) (H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    remainingField P (fun _ => 0) H js L J N T Q V eps alpha beta t =
      PRZZExhaustiveAFEError.field L J N (fun x => (P x:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t := by
  simp [remainingField,withoutFreeze,freezeField,centralField,PRZZPrunedAFEError.keptField,
    PRZZDiscardedTimePair.selected,show scaledCutoff (fun _ => (0:ℂ)) Q = (fun _ => 0) from rfl,
    selected_zero,selected_part_zero]

def complement (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t-family L J N F G H a alpha beta t

/-- A single complement equals the OTHER valued windows, not a small
error and not another copy of the complete family. -/
theorem complement_other_windows (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (alpha beta : ℂ) (t : ℝ) (p : ℕ × ℕ) (hp : p ∈ range K ×ˢ range K)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    complement L J N F (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a alpha beta t =
    ∑ q ∈ (range K ×ˢ range K).erase p, family L J N F
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^q.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^q.2)) a alpha beta t := by
  unfold complement
  rw [← PRZZArithmeticCutoffPartition.family_partition P F K L J N a alpha beta t hleft hright hK]
  exact sub_eq_iff_eq_add.mpr (Finset.sum_erase_add _ _ hp).symm

/-- Reconstruct the original field by summing each retained window after
removing its full-field complement. Discarded source rows remain exact. -/
theorem kept_reconstruction (P : ℝ → ℝ) (K L J N : ℕ) (js : List ℕ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    let W := PRZZWRowLimit.profile (fun x => (P x:ℂ))
    (∑ p ∈ range K ×ˢ range K,
      (PRZZPrunedAFEError.keptField P W W js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t-
       complement L J N (fun x => (P x:ℂ)) (scaledCutoff W ((2:ℝ)^p.1))
        (scaledCutoff W ((2:ℝ)^p.2)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)) =
      family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
      ∑ p ∈ range K ×ˢ range K, PRZZDiscardedTimePair.selected P W W js L J N T
        ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t := by
  dsimp only
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have he (p : ℕ × ℕ) : PRZZPrunedAFEError.keptField P
      (PRZZWRowLimit.profile (fun x => (P x:ℂ))) (PRZZWRowLimit.profile (fun x => (P x:ℂ))) js
      L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t-
      complement L J N (fun x => (P x:ℂ))
        (scaledCutoff (PRZZWRowLimit.profile (fun x => (P x:ℂ))) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile (fun x => (P x:ℂ))) ((2:ℝ)^p.2))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t =
      family L J N (fun x => (P x:ℂ))
        (scaledCutoff (PRZZWRowLimit.profile (fun x => (P x:ℂ))) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile (fun x => (P x:ℂ))) ((2:ℝ)^p.2))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
      PRZZDiscardedTimePair.selected P (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
        (PRZZWRowLimit.profile (fun x => (P x:ℂ))) js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t := by
    unfold PRZZPrunedAFEError.keptField complement
    rw [PRZZExhaustiveAFEError.field_eq]
    exact (show ∀ x y z : ℂ, (x-z)-(x-y) = y-z by intros; ring) _ _ _
  simp_rw [he]
  rw [sum_sub_distrib,PRZZArithmeticCutoffPartition.family_partition
    (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) K L J N _ alpha beta t hl hr hK]

/-- Exact reconstruction under the actual time integral. Continuity of
all finite families supplies integrability; no Fubini premise is added. -/
theorem kept_reconstruction_time (P : ℝ → ℝ) (K L J N : ℕ) (js : List ℕ)
    (phi : ℝ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Set.Icc T (2*T))) :
    let W := PRZZWRowLimit.profile (fun x => (P x:ℂ))
    (∫ t in Set.Icc T (2*T), phi t*∑ p ∈ range K ×ˢ range K,
      (PRZZPrunedAFEError.keptField P W W js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t-
       complement L J N (fun x => (P x:ℂ)) (scaledCutoff W ((2:ℝ)^p.1))
        (scaledCutoff W ((2:ℝ)^p.2)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)) =
      (∫ t in Set.Icc T (2*T), phi t*family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)-
      ∑ p ∈ range K ×ˢ range K, ∫ t in Set.Icc T (2*T), phi t*
        PRZZDiscardedTimePair.selected P W W js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t := by
  dsimp only
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  let W := PRZZWRowLimit.profile (fun x => (P x:ℂ))
  have hd (p : ℕ × ℕ) : IntegrableOn (fun t => phi t*
      PRZZDiscardedTimePair.selected P W W js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t)
      (Set.Icc T (2*T)) :=
    (hphi.mul (PRZZPrunedAFEError.selected_continuous L J N _ _ _ hP hl hr
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps) alpha beta hs T hT)).integrableOn_compact isCompact_Icc
  have hf : IntegrableOn (fun t => phi t*family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t) (Set.Icc T (2*T)) :=
    (hphi.mul (PRZZArithmeticCutoffPartition.family_continuous L J N _ _ _ _ alpha beta T hP hl hr hs hT)).integrableOn_compact isCompact_Icc
  conv_lhs => arg 2; ext t; rw [kept_reconstruction P K L J N js T eps alpha beta t hleft hright hK]
  simp only [mul_sub,mul_sum]
  rw [integral_sub hf (integrable_finsetSum _ (fun p hp => hd p)),integral_finsetSum _ (fun p hp => hd p)]

#print axioms kept_reconstruction_time
#print axioms selected_zero
#print axioms selected_part_zero
#print axioms remaining_zero_window
#print axioms complement_other_windows
#print axioms kept_reconstruction
end XiPrime8845.PRZZResidualPartition

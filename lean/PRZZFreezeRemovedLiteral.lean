import PRZZIntegratedFreezeAFE
import PRZZKeptLiteral

/-! The actual freeze-removed retained field integrated into literal A*.
Zero and negative frequencies and native rectangle rejection are explicit.
The row-local cutoff transfer is retained; no arbitrary-J tail estimate
or exhaustion of a growing spatial family is asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZFreezeRemovedLiteral
open PRZZMellinSeparation PRZZRetainedNative PRZZNativeCentralLiteral PRZZIntegratedFreezeAFE
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def centralField (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  selectedPart .central L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t

def remainingField (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  withoutFreeze P G H js L J N T Q V eps alpha beta t-
    centralField P G H js L J N T Q V eps alpha beta t

def literalCentral (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ d ∈ Finset.Icc 1 N,
    (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      2 T ((2:ℝ)^s) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (scaledCutoff G Q) (scaledCutoff H V) (PRZZWRowLimit.profile (fun x => (P x:ℂ))) Phi beta alpha (alpha+beta)+
     PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps) ((J:ℝ)+1) T
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
      (fun y => PRZZWRowLimit.profile (fun x => (P x:ℂ)) (((2:ℝ)^s)⁻¹*y))
      (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
     PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      ((J:ℝ)+1) T ((2:ℝ)^s) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (scaledCutoff G Q) (scaledCutoff H V) (PRZZWRowLimit.profile (fun x => (P x:ℂ))) Phi beta alpha (alpha+beta)-
     ∫ t : ℝ, rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile (fun x => (P x:ℂ))) (scaledCutoff G Q) (scaledCutoff H V)
      Phi (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)

theorem profile_time (Phi f : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ t in Icc T (2*T), Phi (t/T)*f t) = ∫ t : ℝ, Phi (t/T)*f t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz : Phi (t/T) = 0 := by
    by_contra hn
    have hh := hsP hn
    exact ht ⟨by have := (le_div_iff₀ hT).mp hh.1; linarith,
      by have := (div_le_iff₀ hT).mp hh.2; linarith⟩
  simp [hz]

theorem central_integrable (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    Integrable (fun t : ℝ => Phi (t/T)*centralField P G H js L J N T Q V eps alpha beta t) := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have hp := PRZZWRowLimit.profile_regular _ hP hl hr
  unfold centralField
  simp_rw [retained_central_cells]
  apply integrable_finsetSum; intro s hss
  apply integrable_finsetSum; intro d hd
  change Integrable (fun t => cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
    T ((2:ℝ)^s) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
    (scaledCutoff G Q) (scaledCutoff H V) Phi (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)
  simp_rw [cell_rectangle]
  apply integrable_finsetSum; intro z hz
  by_cases hg : good L N d ((2:ℝ)^s) z
  · simp only [if_pos hg]
    have huv := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact term_integrable d J _ _ _ Phi _ T _ alpha beta z hp.1.continuous hPhi hT
      (by positivity) (mem_Icc.mp huv.1).1 (mem_Icc.mp huv.2).1 hs hp.2.2 hsPhi
  · simp only [if_neg hg]; exact integrable_zero _ _ _

theorem central_time (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t in Icc T (2*T), Phi (t/T)*centralField P G H js L J N T Q V eps alpha beta t) =
      literalCentral P G H Phi js L J N T Q V eps alpha beta := by
  rw [profile_time Phi _ T hT hsPhi]
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  exact retained_central_time L J N _ _ _ Phi _ hP hl hr hPhi hsPhi T Q eps hT alpha beta hs

theorem without_time (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t in Icc T (2*T), Phi (t/T)*withoutFreeze P G H js L J N T Q V eps alpha beta t) =
      literalCentral P G H Phi js L J N T Q V eps alpha beta+
        ∫ t in Icc T (2*T), Phi (t/T)*remainingField P G H js L J N T Q V eps alpha beta t := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have hfield := PRZZPrunedAFEError.field_continuous L J N _ hP hl hr
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta hs T hT
  have hdiscard := PRZZPrunedAFEError.selected_continuous L J N _ (scaledCutoff G Q) (scaledCutoff H V)
    hP hl hr (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (PRZZSourceMaskFamily.discarded T Q eps) alpha beta hs T hT
  have hfreeze := PRZZNativeFreezeTime.selected_continuous L J N (fun x => (P x:ℂ))
    (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta T hT hs
  have hw : ContinuousOn (withoutFreeze P G H js L J N T Q V eps alpha beta) (Icc T (2*T)) :=
    (hfield.sub hdiscard).sub hfreeze
  have hi : IntegrableOn (fun t => Phi (t/T)*withoutFreeze P G H js L J N T Q V eps alpha beta t)
      (Icc T (2*T)) := ((hPhi.comp (continuous_id.div_const T)).continuousOn.mul hw).integrableOn_compact isCompact_Icc
  have hc : IntegrableOn (fun t => Phi (t/T)*centralField P G H js L J N T Q V eps alpha beta t)
      (Icc T (2*T)) := (central_integrable P G H Phi js L J N hP hleft hright hPhi hsPhi
    T Q V eps hT alpha beta hs).integrableOn
  rw [← central_time P G H Phi js L J N hP hleft hright hPhi hsPhi T Q V eps hT alpha beta hs]
  simp only [remainingField,mul_sub]
  rw [integral_sub hi hc]
  ring

/-- Exact connection to the native tail's cutoff. The intermediate band
is part of the remainder, not silently discarded. -/
theorem remaining_local (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps eH t : ℝ) (ht : 0 < t) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    let seed := fun x => (P x:ℂ)
    let g := scaledCutoff G Q
    let h := scaledCutoff H V
    let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let R := fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z
    let loc := PRZZSelectedLocalFourier.localPart
    remainingField P G H js L J N T Q V eps alpha beta t =
      (PRZZAllPoissonRows.family L J N seed (fun _ => 1) (fun _ => 1) a alpha beta t-
       PRZZAllPoissonRows.family L J N seed g h a alpha beta t)+
      (loc .tail L N (PRZZSelectedLocalFourier.sourceCutoff T eH) seed g h a R alpha beta t+
       (loc .central L N (PRZZSelectedLocalFourier.sourceCutoff T eH) seed g h a R alpha beta t-
        centralField P G H js L J N T Q V eps alpha beta t)-
       selectedPart .boundary L J N seed g h a R alpha beta t+
       selectedPart .outside L J N seed g h a R alpha beta t) := by
  dsimp only
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have he := PRZZSelectedLocalFourier.tail_transfer L J N (PRZZSelectedLocalFourier.sourceCutoff T eH)
    (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t hP hl hr ht hs
  unfold remainingField
  rw [without_freeze_field,he]
  unfold centralField
  ring

#print axioms profile_time
#print axioms central_integrable
#print axioms central_time
#print axioms without_time
#print axioms remaining_local
end XiPrime8845.PRZZFreezeRemovedLiteral

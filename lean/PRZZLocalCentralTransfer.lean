import PRZZLocalTailBudget

/-! Exact common-to-local Fourier transfer on the actual selected native
rows. The central transfer band is retained through central+tail invariance,
before norms. All arithmetic coefficients, source masks and the genuine
dual Gamma factor are included. The polynomial spatial window is explicit;
its large-M complement and local central arithmetic estimate are separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter MeasureTheory Set
namespace XiPrime8845.PRZZLocalCentralTransfer
open PRZZNativeComponents PRZZSelectedLocalFourier PRZZMellinSeparation
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def partField (part : Part) (cut : ℕ → ℕ → ℕ → ℕ → ℤ → ℕ)
    (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD t : ℝ) (A B : ℂ) : ℂ :=
  ∑ s ∈ PRZZWindowGrids.spatial L T b, ∑ d ∈ Icc 1 N,
    ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
              (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
            PRZZResolvedTailMass.branch dual A B T t *
              row part L (cut s d u v delta) W (scaledCutoff F Q) (scaledCutoff G V)
                ((2:ℝ)^s) ((u,v),(-delta,1))
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t
          else 0 else 0

theorem local_tail_eq (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    partField .tail (sourceCutoff T eH) F G W js L N dual T Q V b eD t A B =
      PRZZLocalTailBudget.field F G W js L N dual T Q V b eD eH t A B := rfl

/-- Identify the common-cutoff field with the original selectedPart,
including its original label filters and the exact polynomial M mask. -/
theorem common_eq_selected (part : Part) (F G W : ℝ → ℂ) (js : List ℕ)
    (L N J : ℕ) (dual : Bool) (T Q V b eD t : ℝ) (A B : ℂ) :
    partField part (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B =
    PRZZResolvedTailMass.branch dual A B T t *
      PRZZRetainedNative.selectedPart part L J N W (scaledCutoff F Q) (scaledCutoff G V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t := by
  rw [PRZZRetainedNative.selected_reindex]
  unfold partField PRZZWindowGrids.spatial
  simp only [sum_filter,mul_sum]
  apply sum_congr rfl; intro s hs
  by_cases hp : (2:ℝ)^s ≤ T^b <;> simp [hp,mul_sum,mul_ite]

/-- The band is handled by equality, not by a presumed tail monotonicity.
This holds for every common J, not merely J above a height threshold. -/
theorem central_tail (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (ht : 0 < t) (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    partField .central (fun _ _ _ _ _ => J) F G W js L N dual T Q V b eD t A B+
      partField .tail (fun _ _ _ _ _ => J) F G W js L N dual T Q V b eD t A B =
    partField .central (sourceCutoff T eH) F G W js L N dual T Q V b eD t A B+
      partField .tail (sourceCutoff T eH) F G W js L N dual T Q V b eD t A B := by
  unfold partField
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro s hss
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had,← sum_add_distrib]
    apply sum_congr rfl; intro delta hdel
    split_ifs
    · rw [← mul_add,← mul_add]
      congr 1
      exact row_central_tail L J (sourceCutoff T eH s d u v delta) d W
        (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(-delta,1))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t hW hsW (by positivity) ht
        (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs
    · simp
  · simp [had]

def remainder (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  partField .central (fun _ _ _ _ _ => J) F G W js L N dual T Q V b eD t A B+
    partField .tail (fun _ _ _ _ _ => J) F G W js L N dual T Q V b eD t A B-
    partField .central (sourceCutoff T eH) F G W js L N dual T Q V b eD t A B

theorem remainder_eq (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (ht : 0 < t) (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    remainder F G W js L N J dual T Q V b eD eH t A B =
      PRZZLocalTailBudget.field F G W js L N dual T Q V b eD eH t A B := by
  have hh := central_tail F G W js L N J dual T Q V b eD eH t A B hW hsW ht hs
  rw [local_tail_eq] at hh
  unfold remainder
  linear_combination hh

/-- The remainder stated on the original label-indexed central and tail
fields. Only the new local central part is written on native indices. -/
def selectedRemainder (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  PRZZResolvedTailMass.branch dual A B T t *
    (PRZZRetainedNative.selectedPart .central L J N W (scaledCutoff F Q) (scaledCutoff G V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t+
    PRZZRetainedNative.selectedPart .tail L J N W (scaledCutoff F Q) (scaledCutoff G V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)-
    partField .central (sourceCutoff T eH) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B

theorem selected_remainder_eq (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    selectedRemainder F G W js L N J dual T Q V b eD eH t A B =
      remainder F G (PRZZWRowLimit.profile W) js L N J dual T Q V b eD eH t A B := by
  unfold selectedRemainder remainder
  rw [common_eq_selected,common_eq_selected]
  ring

/-- Return to the original selected AFE family. Boundary, freezing and
outside terms stay exact; none is silently included in the tail bound. -/
theorem selected_family_decomposition (F G W : ℝ → ℂ) (js : List ℕ)
    (L N J : ℕ) (dual : Bool) (T Q V b eD eH t : ℝ) (A B : ℂ) :
    let mask := fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z
    let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let alpha := A/(Real.log T:ℂ)
    let beta := B/(Real.log T:ℂ)
    PRZZResolvedTailMass.branch dual A B T t *
      PRZZSourceMaskFamily.selectedFamily L J N W (scaledCutoff F Q) (scaledCutoff G V)
        a mask alpha beta t =
    partField .central (sourceCutoff T eH) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B+
    selectedRemainder F G W js L N J dual T Q V b eD eH t A B+
    PRZZResolvedTailMass.branch dual A B T t *
      (-PRZZRetainedNative.selectedPart .boundary L J N W (scaledCutoff F Q) (scaledCutoff G V)
        a mask alpha beta t+
       PRZZRetainedNative.selectedPart .freeze L J N W (scaledCutoff F Q) (scaledCutoff G V)
        a mask alpha beta t+
       PRZZRetainedNative.selectedPart .outside L J N W (scaledCutoff F Q) (scaledCutoff G V)
        a mask alpha beta t) := by
  dsimp only
  rw [PRZZRetainedNative.selected_decomposition]
  unfold selectedRemainder
  ring

/-- Full arithmetic profile grid, actual scaled time cutoff, and both
Gamma branches. No coefficient-mass or local-tail estimate is assumed.
The exhaustion L and common Fourier J are unrestricted and uniform. -/
theorem actual_partition (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N J : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
          selectedRemainder (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) F
            js L N J dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZLocalTailBudget.actual_partition P F Phi hP hPl hPr hF hFl hFr
    hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T h hT
  intro L N J dual A B hN hNT hA hB hsep
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  have heq : (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
      ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
        remainder (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
          js L N J dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B‖) =
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
      ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
        PRZZLocalTailBudget.field (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
          (PRZZWRowLimit.profile F) js L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B‖) := by
    apply sum_congr rfl; intro p hp
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [remainder_eq (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
      (PRZZWRowLimit.profile F) js L N J dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2)
      b eD eH t A B hf.1 hf.2.2 (by linarith [ht.1]) hs]
  simp_rw [selected_remainder_eq]
  rw [heq]
  exact h L N dual A B hN hNT hA hB hsep

#print axioms local_tail_eq
#print axioms common_eq_selected
#print axioms central_tail
#print axioms remainder_eq
#print axioms selected_remainder_eq
#print axioms selected_family_decomposition
#print axioms actual_partition
end XiPrime8845.PRZZLocalCentralTransfer

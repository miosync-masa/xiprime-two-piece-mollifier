import PRZZLocalCentralTransfer
import PRZZWindowBandMass
import PRZZSubunitWindowMass

/-! Actual native central fields at fixed arithmetic-window cutoffs.
The subunit window is replaced by its zero mode, not by zero. Its signed
correction and the window/native transfer band retain the original masks.
The two absolute masses below are the previously evaluated real masses. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZWindowCentralAssembly
open PRZZLocalCentralTransfer PRZZMellinSeparation
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def windowCut (T V eH : ℝ) (s d _u _v : ℕ) (_gap : ℤ) : ℕ :=
  PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH

/-- At the endpoint Hraw=1 the zero-mode branch is chosen once only. -/
def bodyCut (T V eH : ℝ) (s d u v : ℕ) (gap : ℤ) : ℕ :=
  if PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1 then 0
  else windowCut T V eH s d u v gap

def transfer (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  partField .central (windowCut T V eH) F G W js L N dual T Q V b eD t A B-
    partField .central (PRZZSelectedLocalFourier.sourceCutoff T eH)
      F G W js L N dual T Q V b eD t A B

def subunit (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  partField .central (windowCut T V eH) F G W js L N dual T Q V b eD t A B-
    partField .central (bodyCut T V eH) F G W js L N dual T Q V b eD t A B

theorem central_decomposition (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    partField .central (PRZZSelectedLocalFourier.sourceCutoff T eH)
      F G W js L N dual T Q V b eD t A B =
    partField .central (bodyCut T V eH) F G W js L N dual T Q V b eD t A B+
      subunit F G W js L N dual T Q V b eD eH t A B-
      transfer F G W js L N dual T Q V b eD eH t A B := by
  unfold subunit transfer
  ring

private theorem source_gap (N d u v : ℕ) (T Q eD : ℝ) (s : ℕ) (gap : ℤ)
    (hd : 0 < d) (had : PRZZDiagonalAssembly.admissible N d u v)
    (h : ¬PRZZSourceMaskFamily.discarded T Q eD s
      (PRZZNativeFamily.pairLabel (d*u) (d*v) gap)) :
    |(gap:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d := by
  have hg : Nat.gcd (d*u) (d*v) = d := by
    rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
  have hh : (d:ℝ)*|(gap:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD := by
    simpa only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le] using h
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  exact (le_div_iff₀ hdR).mpr (by nlinarith)

/-- The transfer is dominated by the evaluated mass with every arithmetic
coefficient and the real dual Gamma multiplier still present. -/
theorem transfer_bound (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖transfer F G W js L N dual T Q V b eD eH t A B‖ ≤
      PRZZWindowBandMass.mass F G W js L N dual T Q V b eD eH t A B := by
  rw [← PRZZWindowBandMass.native_mass F G W js L N dual T Q V b eD eH t A B hT hQ hQT]
  unfold transfer partField
  simp only [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    simp only [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro gap hg
    by_cases hh : gap ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
      (PRZZNativeFamily.pairLabel (d*u) (d*v) gap)
    · simp only [if_pos hh,← mul_sub,windowCut,PRZZSelectedLocalFourier.sourceCutoff]
      rw [PRZZWindowBandMass.central_row_difference]
      have hgap := source_gap N d u v T Q eD s gap (mem_Icc.mp hd).1 had hh.2
      by_cases hsmall : |(gap:ℝ)| ≤ (2:ℝ)^s*u/4
      · simp [hh.1,hsmall,hgap,Int.cast_neg,abs_neg,mul_assoc]
      · simp [hsmall,Int.cast_neg,abs_neg]
    · simp only [if_neg hh,sub_self,norm_zero]
      positivity
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had',sub_self,norm_zero,le_refl]

/-- The subunit correction includes all nonzero signs; its zero mode
remains in the body. No complex tail monotonicity is used. -/
theorem subunit_bound (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖subunit F G W js L N dual T Q V b eD eH t A B‖ ≤
      PRZZSubunitWindowMass.mass F G W js L N dual T Q V b eD eH t A B := by
  rw [← PRZZSubunitWindowMass.native_mass F G W js L N dual T Q V b eD eH t A B hT hQ hQT]
  unfold subunit partField
  simp only [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    simp only [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro gap hg
    by_cases hh : gap ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
      (PRZZNativeFamily.pairLabel (d*u) (d*v) gap)
    · simp only [if_pos hh,← mul_sub,bodyCut]
      by_cases hraw : PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1
      · simp only [if_pos hraw,windowCut]
        rw [PRZZSubunitWindowMass.central_row_difference]
        have hgap := source_gap N d u v T Q eD s gap (mem_Icc.mp hd).1 had hh.2
        by_cases hsmall : |(gap:ℝ)| ≤ (2:ℝ)^s*u/4
        · simp [hh.1,hsmall,hgap,hraw,Int.cast_neg,abs_neg,mul_assoc]
        · simp [hsmall,Int.cast_neg,abs_neg]
      · simp [hraw]
    · simp only [if_neg hh,sub_self,norm_zero]
      positivity
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had',sub_self,norm_zero,le_refl]

/-- Direct substitution into the original selected common central+tail
field. All three corrections have their actual, matching source masks. -/
theorem common_decomposition (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    partField .central (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B+
    partField .tail (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B =
    partField .central (bodyCut T V eH) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B+
    subunit F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B-
    transfer F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B+
    selectedRemainder F G W js L N J dual T Q V b eD eH t A B := by
  rw [selected_remainder_eq]
  unfold remainder subunit transfer
  ring

theorem central_bound (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖partField .central (PRZZSelectedLocalFourier.sourceCutoff T eH)
      F G W js L N dual T Q V b eD t A B‖ ≤
    ‖partField .central (bodyCut T V eH) F G W js L N dual T Q V b eD t A B‖+
      PRZZSubunitWindowMass.mass F G W js L N dual T Q V b eD eH t A B+
      PRZZWindowBandMass.mass F G W js L N dual T Q V b eD eH t A B := by
  rw [central_decomposition F G W js L N dual T Q V b eD eH t A B]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl
      (subunit_bound F G W js L N dual T Q V b eD eH t A B hT hQ hQT)))
    (transfer_bound F G W js L N dual T Q V b eD eH t A B hT hQ hQT))

/-- Actual common central+tail minus the fixed-window body, bounded in one
step. The local tail is the original selectedRemainder, not an unnamed error. -/
theorem common_error_bound (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖partField .central (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD t A B+
      partField .tail (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD t A B-
      partField .central (bodyCut T V eH) F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD t A B‖ ≤
      PRZZSubunitWindowMass.mass F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B+
      PRZZWindowBandMass.mass F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B+
      ‖selectedRemainder F G W js L N J dual T Q V b eD eH t A B‖ := by
  have he := common_decomposition F G W js L N J dual T Q V b eD eH t A B
  have he' : partField .central (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B+
    partField .tail (fun _ _ _ _ _ => J) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B-
    partField .central (bodyCut T V eH) F G (PRZZWRowLimit.profile W)
      js L N dual T Q V b eD t A B =
    subunit F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B-
      transfer F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B+
      selectedRemainder F G W js L N J dual T Q V b eD eH t A B := by
    linear_combination he
  rw [he']
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      (subunit_bound F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B hT hQ hQT)
      (transfer_bound F G (PRZZWRowLimit.profile W) js L N dual T Q V b eD eH t A B hT hQ hQT))) le_rfl)

/-- An evaluated envelope for the three corrections in common_decomposition.
It is written as a sum of genuine integrals, without presupposing an
unjustified integral_add for any reconstructed complex field. -/
def errorBudget (P F Phi : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T b eD eH : ℝ) (A B : ℂ) : ℝ :=
  (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
    ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
      selectedRemainder (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) F
        js L N J dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B‖)+
  (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
    ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖*
      PRZZSubunitWindowMass.mass (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
        (PRZZWRowLimit.profile F) js L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B)+
  (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
    ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖*
      PRZZWindowBandMass.mass (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
        (PRZZWRowLimit.profile F) js L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B)

theorem actual_partition (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N J : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      errorBudget P F Phi js L N J dual T b eD eH A B ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨Ct,hCt,ht⟩ := PRZZLocalCentralTransfer.actual_partition P F Phi hP hPl hPr hF hFl hFr
    hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  obtain ⟨Cs,hCs,hs⟩ := PRZZSubunitWindowMass.actual_partition P F Phi hP hPl hPr hF hFl hFr
    hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  obtain ⟨Cb,hCb,hband⟩ := PRZZWindowBandMass.actual_partition P F Phi hP hPl hPr hF hFl hFr
    hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  refine ⟨Ct+Cs+Cb,by positivity,?_⟩
  filter_upwards [ht,hs,hband] with T ht hs hband
  intro L N J dual A B hN hNT hA hB hsep
  exact (add_le_add (add_le_add (ht L N J dual A B hN hNT hA hB hsep)
    (hs L N dual A B hN hNT hA hB hsep))
    (hband L N dual A B hN hNT hA hB hsep)).trans_eq (by ring)

#print axioms common_decomposition
#print axioms common_error_bound
#print axioms central_bound
#print axioms actual_partition
#print axioms central_decomposition
#print axioms transfer_bound
#print axioms subunit_bound
end XiPrime8845.PRZZWindowCentralAssembly

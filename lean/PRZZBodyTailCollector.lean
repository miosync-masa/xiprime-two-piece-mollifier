import PRZZBodyTailTime
import PRZZTailRowIntegrable
import PRZZNativeTailRectangle

/-! Return the strict literal tail collector to the evaluated closed
native mass. The native exhaustion R and the spatial length L are
independent. The genuine dual multiplier uses inverse-reflected shifts. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZBodyTailCollector
open PRZZMellinSeparation PRZZNativeCentralLiteral PRZZWindowCentralAssembly
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

def profile (dual : Bool) (Phi : ℝ → ℂ) (T : ℝ) (A B : ℂ) : ℝ → ℂ :=
  if dual then PRZZKeptLiteral.dualProfile Phi T ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ)) else Phi

theorem profile_time (dual : Bool) (Phi : ℝ → ℂ) (T t : ℝ) (A B : ℂ) (hT : T ≠ 0) :
    profile dual Phi T A B (t/T) = Phi (t/T)*PRZZResolvedTailMass.branch dual A B T t := by
  cases dual
  · simp [profile,PRZZResolvedTailMass.branch]
  · simp only [profile,if_true,PRZZKeptLiteral.dualProfile,PRZZResolvedTailMass.branch]
    rw [show T*(t/T) = t by field_simp]

def density (F G W : ℝ → ℂ) (js : List ℕ) (R L N : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) : ℝ :=
  ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Finset.Icc 1 N,
    ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) 2,
      if good R N d ((2:ℝ)^s) z then
        ‖PRZZResolvedTailMass.branch dual A B T t *
          PRZZNativeComponents.row .tail R (bodyCut T V eH s d 0 0 0) W
            (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) z
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t‖ else 0

theorem density_bound (F G W : ℝ → ℂ) (js : List ℕ) (R L N : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) (hLR : L ≤ R) :
    density F G W js R L N dual T Q V eD eH t A B ≤
      PRZZBodyTailMass.mass F G W js R N dual T Q V 4 eD eH t A B := by
  unfold density
  calc
    _ ≤ ∑ s ∈ PRZZWindowGrids.spatial R T 4, ∑ d ∈ Finset.Icc 1 N,
        ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) 2,
          if good R N d ((2:ℝ)^s) z then
            ‖PRZZResolvedTailMass.branch dual A B T t *
              PRZZNativeComponents.row .tail R (bodyCut T V eH s d 0 0 0) W
                (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) z
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t‖ else 0 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro s hs
        obtain ⟨hs,hm⟩ := mem_filter.mp hs
        exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hs; omega),hm.le⟩
      · intro s hs hnot
        positivity
    _ ≤ _ := by
      unfold PRZZBodyTailMass.mass
      apply sum_le_sum; intro s hss
      apply sum_le_sum; intro d hd
      rw [PRZZNativeTailRectangle.rectangle]
      apply sum_le_sum; intro u hu
      apply sum_le_sum; intro v hv
      by_cases had : PRZZDiagonalAssembly.admissible N d u v
      · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
        simp only [if_pos had,if_pos had']
        apply sum_le_sum; intro gap hg
        by_cases hh : gap ≠ 0 ∧ |(gap:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d
        · rw [if_pos hh]
          by_cases hm : |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4
          · have hc : gap ≠ 0 ∧ |((-gap:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
                |((-gap:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
              ⟨hh.1,hm,by simpa only [Int.cast_neg,abs_neg] using hh.2.le⟩
            rw [if_pos hm,if_pos hc]
            rfl
          · rw [if_neg hm]
            split_ifs <;> positivity
        · rw [if_neg hh]
          split_ifs <;> positivity
      · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
        simp only [if_neg had,if_neg had',le_refl]

theorem mass_time (P F Phi : ℝ → ℂ) (js : List ℕ) (R K L N : ℕ) (dual : Bool)
    (T eD eH : ℝ) (A B : ℂ)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous (profile dual Phi T A B)) (hT : 0 < T)
    (hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0) :
    PRZZActualTailCollector.mass P F (profile dual Phi T A B) R K L N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eD
      (PRZZCommonSignedWindow.cutoff T eH) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
    ∑ p ∈ range K ×ˢ range K, ∫ t in Icc T (2*T), ‖Phi (t/T)‖*
      density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
        js R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B := by
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  unfold PRZZActualTailCollector.mass PRZZActualTailCollector.nativeCellMass
  apply sum_congr rfl
  intro p hp
  let ss := (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))
  let term := fun s d z t => if good R N d ((2:ℝ)^s) z then
    ‖profile dual Phi T A B (t/T)*PRZZNativeComponents.row .tail R
      (PRZZCommonSignedWindow.cutoff T eH p s d) (PRZZWRowLimit.profile F)
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) ((2:ℝ)^s) z
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t‖ else 0
  have hi (s d : ℕ) (z : PRZZAStar.Index)
      (hz : z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) 2) :
      IntegrableOn (term s d z) (Icc T (2*T)) := by
    have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    by_cases hg : good R N d ((2:ℝ)^s) z
    · have hn := (PRZZTailRowIntegrable.native_integrable R d
        (PRZZCommonSignedWindow.cutoff T eH p s d) (PRZZWRowLimit.profile F)
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) (profile dual Phi T A B)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) hf.1 hPhi hf.2.2 T ((2:ℝ)^s)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) z hT
        (by positivity) (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs).norm
      apply hn.congr
      exact Eventually.of_forall (fun t => by simp only [term,if_pos hg])
    · simp only [term,if_neg hg]
      exact integrableOn_zero
  have he (t : ℝ) : ‖Phi (t/T)‖*density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
      (PRZZWRowLimit.profile F) js R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B =
      ∑ s ∈ ss, ∑ d ∈ Finset.Icc 1 N,
        ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) 2,
          term s d z t := by
    unfold density
    simp only [mul_sum]
    apply sum_congr rfl; intro s hss
    apply sum_congr rfl; intro d hd
    apply sum_congr rfl; intro z hz
    by_cases hg : good R N d ((2:ℝ)^s) z
    · simp only [term,if_pos hg,profile_time dual Phi T t A B hT.ne',
        norm_mul,PRZZCommonSignedWindow.cutoff,mul_assoc]
    · simp only [term,if_neg hg,mul_zero]
  simp_rw [he]
  rw [integral_finsetSum _ (fun s hss => integrable_finsetSum _
    (fun d hd => integrable_finsetSum _ (fun z hz => hi s d z hz)))]
  apply sum_congr rfl; intro s hss
  rw [integral_finsetSum _ (fun d hd => integrable_finsetSum _ (fun z hz => hi s d z hz))]
  apply sum_congr rfl; intro d hd
  rw [integral_finsetSum _ (fun z hz => hi s d z hz)]
  apply sum_congr rfl; intro z hz
  by_cases hg : good R N d ((2:ℝ)^s) z <;> simp only [term,hg,if_true,if_false,integral_zero]

#print axioms profile_time
#print axioms density_bound
#print axioms mass_time
end XiPrime8845.PRZZBodyTailCollector

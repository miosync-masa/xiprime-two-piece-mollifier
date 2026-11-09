import PRZZCappedBandOuter
import PRZZSameMaskResidual

/-! Exact strict-source common/local central band for arbitrary coefficients.
Boundary and outside elimination are reused on the original unchanged mask. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZCappedSameMask
open PRZZMellinSeparation PRZZRetainedNative PRZZSelectedLocalFourier PRZZSameMaskResidual
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def bandField (P F G : ℝ → ℂ) (c : ℕ → ℂ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) : ℂ :=
  PRZZResolvedTailMass.branch dual A B T t *
    (selectedPart .central L J N P (scaledCutoff F Q) (scaledCutoff G V)
      c (keep T Q eD)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
    localPart .central L N (sourceCutoff T eH) P (scaledCutoff F Q) (scaledCutoff G V)
      c (keep T Q eD)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)

/-- Identify the signed selected band with its original native rows before
taking any norm. This is the common-minus-local sign. -/
theorem band_reindex (P F G : ℝ → ℂ) (c : ℕ → ℂ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) :
    bandField P F G c L N J dual T Q V eD eH t A B =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
            if delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
              PRZZResolvedTailMass.branch dual A B T t *
                (if |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 then
                  PRZZCappedTailMass.coeff F G c d Q V T A B ((u,v),(-delta,1))*
                    PRZZBandOuterMass.band (PRZZWRowLimit.profile P) ((2:ℝ)^s) T eH t A B J
                      ((u,v),(-delta,1)) else 0) else 0 else 0 := by
  unfold bandField
  rw [selected_reindex]
  simp only [localPart,← sum_sub_distrib,ite_sub_ite,sub_self,mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply sum_congr rfl; intro delta hdel
    by_cases hk : delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · simp only [if_pos hk,sourceCutoff]
      rw [PRZZCappedBandOuter.central_row_difference]
      simp only [mul_ite,mul_zero]
    · simp only [if_neg hk]
  · simp only [if_neg had]

theorem band_dominated (P F G : ℝ → ℂ) (c : ℕ → ℂ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖bandField P F G c L N J dual T Q V eD eH t A B‖ ≤
      PRZZCappedBandOuter.mass F G (PRZZWRowLimit.profile P) c L N J dual T Q V 4 eD eH t A B := by
  rw [band_reindex,← PRZZCappedBandOuter.native_mass F G (PRZZWRowLimit.profile P) c L N J dual
    T Q V 4 eD eH t A B hT hQ hQT]
  unfold PRZZWindowGrids.spatial
  rw [sum_filter]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  by_cases hsmallM : (2:ℝ)^s < T^(4:ℝ)
  · rw [if_pos hsmallM.le]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro d hd
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro u hu
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro v hv
    by_cases had : PRZZDiagonalAssembly.admissible N d u v
    · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
      simp only [if_pos had,if_pos had']
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro delta hdel
      by_cases hk : delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
      · rw [if_pos hk]
        have hgcd : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
        have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
        have hf : |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d := by
          rw [le_div_iff₀ hd0]
          have hh := hk.2.2
          simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hgcd,not_le] at hh
          simpa only [Int.cast_neg,abs_neg,mul_comm] using hh.le
        by_cases hg : |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4
        · have hcond : delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
              |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
            ⟨hk.1,hg,hf⟩
          rw [if_pos hg,if_pos hcond]
          exact le_of_eq (by congr 1; ring)
        · rw [if_neg hg]
          simp only [mul_zero,norm_zero]
          split_ifs <;> positivity
      · simp only [if_neg hk,norm_zero]
        split_ifs <;> positivity
    · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
      simp only [if_neg had,if_neg had',norm_zero,le_refl]
  · simp only [keep,hsmallM,false_and,and_false,if_false,ite_self,sum_const_zero,norm_zero]
    split_ifs <;> positivity

#print axioms band_reindex
#print axioms band_dominated
end XiPrime8845.PRZZCappedSameMask

import PRZZStrictSmallTail
import PRZZCappedNativeTail

/-! Actual strict-source local Fourier tails with a common coefficient cap.
The signed original row is used; support witnesses are not requested for
zero terms. This retains, rather than changes, the source Fourier cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter MeasureTheory
namespace XiPrime8845.PRZZCappedStrictTail
open PRZZSelectedLocalFourier PRZZMellinSeparation
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def field (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^b), ∑ d ∈ Icc 1 N,
    ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
              (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
            PRZZResolvedTailMass.branch dual A B T t *
              PRZZNativeComponents.row .tail L (sourceCutoff T eH s d u v delta) W
                (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(-delta,1))
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                c d t
          else 0 else 0

theorem native_row_bound (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V _b eD eH t : ℝ) (A B : ℂ) (s : ℕ) :
    ‖(∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
              (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
            PRZZResolvedTailMass.branch dual A B T t *
              PRZZNativeComponents.row .tail L (sourceCutoff T eH s d u v delta) W
                (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(-delta,1))
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                c d t
          else 0 else 0)‖ ≤
    ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d then
            ‖PRZZResolvedTailMass.branch dual A B T t *
              PRZZCappedTailMass.coeff F G c d Q V T A B ((u,v),(-delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^s) T eH t A B (-delta) 1
                (PRZZCentralTail.residue ((u,v),(-delta,1))/v) (u,v)‖ else 0 else 0 := by
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
    by_cases hr : delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · rw [if_pos hr,source_tail]
      have hg : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
      have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hf : |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d := by
        have hh := hr.2
        simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le] at hh
        simp only [Int.cast_neg,abs_neg]
        exact ((lt_div_iff₀ hd0).mpr (by simpa only [mul_comm] using hh)).le
      simp only [Int.cast_neg,abs_neg] at hf
      by_cases hsmall : |(delta:ℝ)| ≤ (2:ℝ)^s*u/4
      · have hsmall' : |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 := by simpa only [Int.cast_neg,abs_neg] using hsmall
        have hcond : delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
          ⟨hr.1,hsmall',by simpa only [Int.cast_neg,abs_neg] using hf⟩
        rw [if_pos hcond,if_pos hsmall']
        simp only [PRZZCappedTailMass.coeff,mul_assoc,le_refl]
      · simp only [Int.cast_neg,abs_neg,hsmall,and_false,false_and,if_false,mul_zero,norm_zero,le_refl]
    · rw [if_neg hr,norm_zero]
      split_ifs <;> positivity
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had',norm_zero,le_refl]


theorem native_dominates (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    ‖field F G W c L N dual T Q V b eD eH t A B‖ ≤
      PRZZCappedNativeTail.nativeMass F G W c L N dual T Q V b eD eH t A B := by
  rw [← PRZZCappedNativeTail.flat_eq]
  unfold field PRZZCappedNativeTail.flatMass
  unfold PRZZWindowGrids.spatial
  rw [sum_filter,sum_filter]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  by_cases hm : (2:ℝ)^s < T^b
  · rw [if_pos hm,if_pos hm.le]
    exact native_row_bound F G W c L N dual T Q V b eD eH t A B s
  · simp only [if_neg hm,norm_zero]
    split_ifs <;> positivity

/-- Constants precede every arithmetic scale, truncation, and branch. -/
theorem uniform (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < Q → t ∈ Set.Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖field F G W c L N dual T Q V b eD eH t A B‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := PRZZCappedWindowTime.uniform F G W hF hG hcF hcG hsF hW hsW
    Hcap hHcap a b S r eD eH power ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c L N dual Q V t A B hcoef hN hNT hQ ht hA hB hsep
  apply (native_dominates F G W c L N dual T Q V b eD eH t A B).trans
  rw [PRZZCappedNativeTail.native_eq_all F G W c L N dual T Q V b eD eH t A B hT hNT hQ hsF]
  exact h c L N dual Q V t A B hcoef hN hNT hQ ht hA hB hsep

theorem time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L N : ℕ) (dual : Bool) (Q V P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 ≤ P → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Set.Icc T (2*T), ‖phi t‖) ≤ P*T →
      (∫ t in Set.Icc T (2*T), ‖phi t*field F G W c L N dual T Q V b eD eH t A B‖) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := uniform F G W hF hG hcF hcG hsF hW hsW Hcap hHcap a b S r eD eH
    (1-delta) ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c L N dual Q V P A B phi hcoef hN hNT hQ hP hA hB hsep hphi hmass
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun t => C*T^(-(1-delta))*‖phi t‖) (Set.Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  have hh : (∫ t in Set.Icc T (2*T), ‖phi t*field F G W c L N dual T Q V b eD eH t A B‖) ≤
      C*T^(-(1-delta))*(∫ t in Set.Icc T (2*T), ‖phi t‖) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h c L N dual Q V t A B hcoef hN hNT hQ ht hA hB hsep)
      (norm_nonneg _)).trans_eq (by ring)
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*T^(-(1-delta))*(P*T) := hh.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = C*P*T^delta := by
      rw [show -(1-delta) = delta-1 by ring,Real.rpow_sub hT0,Real.rpow_one]
      field_simp
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

theorem local_identification (P F G : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) :
    PRZZResolvedTailMass.branch dual A B T t *
      localPart .tail L N (sourceCutoff T eH) P (scaledCutoff F Q) (scaledCutoff G V)
        c (PRZZSameMaskResidual.keep T Q eD)
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t =
      field F G (PRZZWRowLimit.profile P) c L N dual T Q V 4 eD eH t A B := by
  unfold localPart field
  simp only [sum_filter,mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl; intro s hs
  by_cases hm : (2:ℝ)^s < T^(4:ℝ)
  · simp only [PRZZSameMaskResidual.keep,hm,true_and,ite_true]
  · simp only [PRZZSameMaskResidual.keep,hm,false_and,and_false,if_false,ite_self,sum_const_zero]

#print axioms local_identification
#print axioms native_row_bound
#print axioms native_dominates
#print axioms uniform
#print axioms time
end XiPrime8845.PRZZCappedStrictTail

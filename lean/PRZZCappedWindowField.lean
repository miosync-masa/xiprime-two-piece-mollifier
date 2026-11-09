import PRZZCappedWindowTime
import PRZZClassZeroCorrection

/-! Actual complex Fourier tails on the native polynomial spatial window.
The common coefficient cap precedes both independent slots and height.
This does not identify the source-cutoff tail with a different global
cutoff, nor estimate the separate freezing or large-spatial corrections. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZCappedWindowField
open PRZZCappedWindowMass PRZZMellinSeparation PRZZResolvedTailMass
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def field (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  ∑ k ∈ PRZZWindowGrids.spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
      ∑ delta ∈ PRZZWindowGrids.gaps T b eD,
        if |(delta:ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k) Q eD/d then
          ∑ p ∈ nativePairs L N d j l k delta,
            branch dual A B T t * PRZZCappedTailMass.coeff F G c d Q V T A B (p,(delta,1)) *
              PRZZUnitTailMass.tail W ((2:ℝ)^k) T eH t A B delta 1
                (PRZZCentralTail.residue (p,(delta,1))/p.2) p
        else 0

theorem norm_le_mass (F G W : ℝ → ℂ) (c : ℕ → ℂ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    ‖field F G W c L N dual T Q V b eD eH t A B‖ ≤
      mass F G W c L N dual T Q V b eD eH t A B := by
  unfold field mass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro k hk
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro j hj
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro l hl
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro delta hdelta
  unfold term
  split_ifs
  · exact norm_sum_le _ _
  · simp

theorem mixed_time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c d : ℕ → ℂ) (L N : ℕ) (dual : Bool) (Q V : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi →
      (∫ t in Icc T (2*T), ‖phi t * PRZZMixedPoisson.lift
        (fun e => field F G W e L N dual T Q V b eD eH t A B) c d‖) ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZCappedWindowTime.uniform F G W hF hG hcF hcG hsF hW hsW
    (2*Hcap) (by positivity) a b S r eD eH power ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c d L N dual Q V A B phi hc hd hN hNT hQ hA hB hsep hphi
  have hp (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖PRZZMixedPoisson.lift (fun e => field F G W e L N dual T Q V b eD eH t A B) c d‖ ≤ C*T^(-power) := by
    apply PRZZClassZeroCorrection.lift_bound
    intro z hz
    exact (norm_le_mass F G W _ L N dual T Q V b eD eH t A B).trans
      (h _ L N dual Q V t A B
        (PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hd z hz)
        hN hNT hQ ht hA hB hsep)
  have hi : IntegrableOn (fun t => C*T^(-power)*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hp t ht) (norm_nonneg _)).trans_eq (by ring)

#print axioms norm_le_mass
#print axioms mixed_time
end XiPrime8845.PRZZCappedWindowField

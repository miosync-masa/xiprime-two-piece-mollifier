import PRZZCappedStrictFreeze
import PRZZCappedTailBand

/-! The actual reconstructed strict freezing field, not a separate row proxy.
Both original arithmetic grids and the genuine dual multiplier are retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set MeasureTheory Filter
namespace XiPrime8845.PRZZCappedFreezeCollector
open PRZZMellinSeparation PRZZRetainedNative PRZZSameMaskResidual PRZZReconstructedAFE
set_option maxHeartbeats 10000000

theorem freezing_time (P phi : ℝ → ℂ) (c : ℕ → ℂ) (K L J N : ℕ)
    (T eps : ℝ) (alpha beta : ℂ) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (hphi : Continuous phi) :
    (∫ t in Icc T (2*T), phi t*freezing P P K L J N c T eps alpha beta t) =
      ∑ p ∈ range K ×ˢ range K, ∫ t in Icc T (2*T), phi t*
        selectedPart .freeze L J N P
          (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
          (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) c
          (keep T ((2:ℝ)^p.1) eps) alpha beta t := by
  unfold freezing
  simp only [mul_sum]
  apply integral_finsetSum
  intro p hp
  exact (hphi.continuousOn.mul (PRZZNativeFreezeTime.selected_continuous
    L J N P _ _ c _ alpha beta T hT hs)).integrableOn_compact isCompact_Icc

theorem field_bound (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (L J N : ℕ) (T : ℝ) (A B : ℂ)
      (phi : ℝ → ℂ) (U : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → Continuous phi → 0 ≤ U → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ U) →
      ‖∫ t in Icc T (2*T), phi t*freezing P P (Nat.log 2 N+2) L J N c T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*U*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨hw,hcw,hsw⟩ := PRZZWRowLimit.profile_regular P hP hl hright
  obtain ⟨C,hC,h⟩ := PRZZCappedStrictFreeze.partition_bound P _ _ hP hl hright
    hw.continuous hw.continuous hcw hcw hsw hsw Hcap hHcap S r eps eta delta
      hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro c L J N T A B phi U hc hA hB hsep hN hT hlog hleta hscale hh hphi hU hp
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  rw [freezing_time P phi c _ L J N T eps _ _ (by linarith) hs hphi]
  exact (norm_sum_le _ _).trans
    (h c L J N T A B phi U hc hA hB hsep hN hT hlog hleta hscale hh hphi hU hp)

theorem paired_mixed_bound (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c d : ℕ → ℂ) (L J N : ℕ) (A B : ℂ) (Phi : ℝ → ℂ) (U : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → Continuous Phi → 0 ≤ U → (∀ x, ‖Phi x‖ ≤ U) →
      ‖PRZZMixedPoisson.lift (fun a => PRZZRemainderBudget.paired
        (freezing P P (Nat.log 2 N+2) L J N a T eps) Phi T
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤
        C*U*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := field_bound P hP hl hright (2*Hcap) (by positivity)
    S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C*(1+Real.exp (2*S+7)),by positivity,?_⟩
  filter_upwards [PRZZDualError.multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hg hsmall
  intro c d L J N A B Phi U hc hd hA hB hsep hN hT hlog hleta hscale hh hPhi hU hp
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  have hcoef := PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hd z hz
  have hphi : Continuous (fun t : ℝ => Phi (t/T)) := hPhi.comp (continuous_id.div_const T)
  have hgam := (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).continuous
  have hcap (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖Phi (t/T)*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        U*Real.exp (2*S+7) := by
    rw [norm_mul]
    exact mul_le_mul (hp _) (hg A B hA hB t ht) (norm_nonneg _) hU
  have hs' : r ≤ ‖-B+-A‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have h1 := h _ L J N T A B _ U hcoef hA hB hsep hN hT hlog hleta hscale hh
    hphi hU (fun t ht => hp _)
  have h2 := h _ L J N T (-B) (-A) _ (U*Real.exp (2*S+7)) hcoef
    (by simpa using hB) (by simpa using hA) hs' hN hT hlog hleta hscale hh
    (hphi.mul hgam) (by positivity) hcap
  simp only [neg_div] at h2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

#print axioms freezing_time
#print axioms field_bound
#print axioms paired_mixed_bound
end XiPrime8845.PRZZCappedFreezeCollector

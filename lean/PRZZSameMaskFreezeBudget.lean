import PRZZSameMaskResidual

/-! Sharp freezing budget for the exact strict-small source mask.
Both AFE branches keep their original Gamma multiplier. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZSameMaskFreezeBudget
open PRZZMellinSeparation PRZZRetainedNative PRZZSameMaskResidual
set_option maxHeartbeats 9000000

def freezePair (P : ℝ → ℂ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N P
    (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (keep T Q eps) alpha beta t)+
  ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
    selectedPart .freeze L J N P (scaledCutoff G Q) (scaledCutoff H V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (keep T Q eps) (-beta) (-alpha) t

theorem freeze_pair_charge (P : ℝ → ℂ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Icc T (2*T))) :
    ‖freezePair P G H phi js L J N T Q V eps alpha beta‖ ≤
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile P)
        G H phi js T 1 Q V eps alpha beta+
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile P)
        G H (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t) js
        T 1 Q V eps (-beta) (-alpha) := by
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  unfold freezePair
  exact (norm_add_le _ _).trans (add_le_add
    (freeze_charge L J N P G H phi js T Q V eps alpha beta hT hs hphi)
    (freeze_charge L J N P G H _ js T Q V eps (-beta) (-alpha) hT hs'
      (hphi.mul hg.continuousOn)))

theorem partition_bound (P : ℝ → ℂ) (G H : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) (hsH : Function.support H ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ) (U : ℝ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → 0 ≤ U → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ U) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ‖freezePair P G H phi js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖) ≤
        C*U*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨hf,hcf,hsf⟩ := PRZZWRowLimit.profile_regular P hP hleft hright
  let W := PRZZWRowLimit.profile P
  obtain ⟨Cf,hCf,hfbound⟩ := PRZZFullFreezeBudget.partition_bound W G H hf hcf hsf
    hG hH hcG hcH hsG hsH js S r eps eta delta hS hr heps heta heta1 hmargin
  obtain ⟨Cd,hCd,hdbound⟩ := PRZZDualNativeFreeze.partition_bound W G H hf hcf hsf
    hG hH hcG hcH hsG hsH js S r eps eta delta hS hr heps heps1 heta heta1 hmargin
  refine ⟨Cf+Cd,by positivity,?_⟩
  filter_upwards [hdbound,PRZZRejectedExhaustion.height_eventually eps heps1,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (max 1 (2*S/eta))),
    Filter.eventually_ge_atTop (1:ℝ)] with T hd hheight hsmall hlog hT
  intro L J N A B phi U hN hscale hA hB hsep hphi hU hcap
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (ne_of_gt (show 0 < Real.log T by linarith [le_max_left 1 (2*S/eta)])))
  have hprimal := hfbound L J N (L+2) T 1 0 A B phi U hA hB hsep hN hT
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hscale hheight.2
    (by norm_num) hphi hU hcap
  have hdual := hd L J N (L+2) 1 A B phi U hN hscale (by norm_num) hA hB hsep hphi hU hcap
  calc
    _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        (PRZZFullFreezeBudget.fullMass L J W phi js N (L+2) T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2)
          eps 0 G H (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))+
         PRZZNativeFreezeEnvelope.charge L J N (L+2) W G H (PRZZDualNativeFreeze.weight phi T A B)
          js T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))) := by
      apply sum_le_sum; intro p hp
      apply (freeze_pair_charge P G H phi js L J N T _ _ eps hT0 _ _
        (hsmall.2 A hA) (hsmall.2 B hB) hs hphi.continuousOn).trans
      apply add_le_add
      · simpa only [add_div] using PRZZNativeFreezeEnvelope.dominates L J N (L+2) W G H phi js
          T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps 0 _ _ hf hsf hsG hT0 (by norm_num)
          (by positivity) hs hheight.2
      · simp only [neg_div]; exact le_rfl
    _ ≤ _ := by
      rw [sum_add_distrib]
      exact (add_le_add hprimal hdual).trans_eq (by ring)


#print axioms freeze_pair_charge
#print axioms partition_bound
end XiPrime8845.PRZZSameMaskFreezeBudget


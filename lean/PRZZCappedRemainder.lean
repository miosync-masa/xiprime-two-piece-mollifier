import PRZZCappedFreezeCollector
import PRZZCappedDiscardedFamily
import PRZZCappedLarge

/-! All actual reconstructed residual components with one common coefficient
cap. Constants precede both coefficient slots, height and sharp cutoffs.
This is a residual bound, not discharge of the public witness input. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set MeasureTheory Filter
namespace XiPrime8845.PRZZCappedRemainder
open PRZZMellinSeparation PRZZReconstructedAFE PRZZRemainderBudget
set_option maxHeartbeats 12000000

theorem remainderPair_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c d : ℕ → ℂ) (L J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun a => remainderPair
        (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) L J N a T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hdelta : 0 ≤ delta := by linarith
  obtain ⟨Ct,hCt,ht⟩ := PRZZCappedTailBand.mixed_tailBand_target F Phi hP hFl hFr
    hPhi.continuous hcPhi Hcap hHcap S r eps eH delta hS hr heps.le heps1 he hdelta
  obtain ⟨Cf,hCf,hf⟩ := PRZZCappedFreezeCollector.paired_mixed_bound F hP hFl hFr
    Hcap hHcap S r eps eta delta hS hr heps.le heta heta1 hmargin
  obtain ⟨Cd,hCd,hd⟩ := PRZZCappedDiscardedFamily.mixed_discarded_absorbed Phi P
    hPhi hcPhi hsPhi hP hm hlo hhi hl hright Hcap hHcap S r eps 0 hS hr heps heps1.le
  obtain ⟨Cl,hCl,hlarge⟩ := PRZZCappedLarge.paired_mixed_time P hm hlo hhi hl hright hP
    Phi hPhi.continuous Hcap hHcap S r hS hr
  obtain ⟨U0,hU0⟩ := hcPhi.exists_bound_of_continuous hPhi.continuous
  let U := max U0 1
  have hU : 0 ≤ U := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hcap (x : ℝ) : ‖Phi x‖ ≤ U := (hU0 x).trans (le_max_left _ _)
  obtain ⟨V,hV,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi.continuous hcPhi
  refine ⟨Ct+Cf*U+Cd+Cl*V,by positivity,?_⟩
  filter_upwards [ht,hf,hd,hlarge,PRZZRejectedExhaustion.height_eventually eps heps1,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*S/eta))),
    eventually_ge_atTop (2:ℝ)] with T ht hf hd hlrg hh hsmall hlog hT
  intro c d L J N A B hc hdcoef hN hscale hL hJ hA hB hsep
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (4/7:ℝ) ≤ 1))
  have h1 := ht c d L J N A B hc hdcoef hN hNT hL hJ hA hB hsep
  have h2 := hf c d L J N A B Phi U hc hdcoef hA hB hsep hN hT1
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hscale hh.2 hPhi.continuous hU hcap
  have h3 := hd c d L J N A B hc hdcoef hN hNT hA hB hsep
  simp only [neg_zero,Real.rpow_zero,mul_one] at h3
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have h3' := h3.trans ((le_mul_of_one_le_right hCd.le (Real.one_le_rpow hT1 hdelta)).trans
    (le_mul_of_one_le_right (by positivity) htarg))
  have h4 := hlrg c d L J N A B hc hdcoef hN hNT hA hB hsep
  have h4' := h4.trans ((mul_le_mul_of_nonneg_left (by
    simpa only [scaledCutoff,inv_mul_eq_div] using (hcut T hT0).2) (by positivity)).trans
      (PRZZRemainderAbsorption.small_error_absorb Cl V T delta N hCl.le hV.le hT1 hdelta hN))
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  rw [PRZZCappedTailBand.mixed_remainder_split F F Phi _ L J N c d T eps _ _
    hP hFl hFr hPhi.continuous hsPhi hT0 (hsmall.2 A hA) (hsmall.2 B hB) hs]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2)) h3')) h4')).trans_eq (by ring)

/-- Exact return to the original moment: the computed residual is precisely
the difference between the literal-model error and the actual AFE-model error.
The latter is retained here, not silently set to zero. -/
theorem original_moment_residual (P F Phi : ℝ → ℂ) (K L J N : ℕ) (c d : ℕ → ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    (PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-
      PRZZMixedPoisson.lift (fun a => PRZZSmallCentralLiteral.literalModel P F Phi K L J N a T eps alpha beta) c d)-
    (PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-
      PRZZMixedPoisson.model L J N F c d alpha beta T (scaledCutoff Phi T)) =
    PRZZMixedPoisson.lift (fun a => remainderPair P F Phi K L J N a T eps alpha beta) c d := by
  have hm := PRZZCappedTailBand.original_moment_split P F Phi K L J N c d hPl hPr hK
    hF hFl hFr hPhi hsPhi T eps hT alpha beta ha hb hs
  have hr := PRZZCappedTailBand.mixed_remainder_split P F Phi K L J N c d T eps alpha beta
    hF hFl hFr hPhi hsPhi hT ha hb hs
  linear_combination hm-hr

#print axioms original_moment_residual
#print axioms remainderPair_bound
end XiPrime8845.PRZZCappedRemainder

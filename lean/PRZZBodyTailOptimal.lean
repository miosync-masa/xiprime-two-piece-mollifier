import PRZZBodyTailCollector

/-! The evaluated source, band and subunit masses bound the original
paired literal tail. Native exhaustion is chosen after fixing height;
all analytic constants are uniform before that choice. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZBodyTailOptimal
open PRZZMellinSeparation PRZZBodyTailCollector
set_option maxHeartbeats 15000000

theorem uniform_mass (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eD eH delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (R L N : ℕ) (dual : Bool) (A B : ℂ),
      L ≤ R → 1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZActualTailCollector.mass P F (profile dual Phi T A B) R (Nat.log 2 N+2) L N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eD
        (PRZZCommonSignedWindow.cutoff T eH) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨Cb,hCb,hbody⟩ := PRZZBodyTailMass.uniform _ _ _ hp.1.continuous hp.1.continuous
    hp.2.1 hp.2.1 hp.2.2 hp.2.2 hf.1 hf.2.2 js 1 4 S r eD eH (2-delta)
    (by norm_num) (by norm_num) hS hr heD he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  obtain ⟨P0,hP0,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨D*Cb*P0,by positivity,?_⟩
  filter_upwards [hbody,PRZZGammaCentral.log_scaled_shifts_eventually S,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hbody hsmall hT hlog
  intro R L N dual A B hLR hN hNT hA hB hsep
  have hT0 : 0 < T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have hprofile : Continuous (profile dual Phi T A B) := by
    cases dual
    · exact hPhi
    · exact (PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T
        ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))
        (by simpa only [neg_div,norm_neg] using (hsmall A B hA hB).2)
        (by simpa only [neg_div,norm_neg] using (hsmall A B hA hB).1)).1
  rw [mass_time P F Phi js R (Nat.log 2 N+2) L N dual T eD eH A B hF hFl hFr hprofile hT0 hs]
  have hi : IntegrableOn (fun t : ℝ => Cb*T^(-(2-delta))*‖Phi (t/T)‖) (Icc T (2*T)) :=
    (continuous_const.mul (hPhi.comp (continuous_id.div_const T)).norm).integrableOn_Icc
  have hphiMass : (∫ t in Icc T (2*T), ‖Phi (t/T)‖) ≤ P0*T := by
    simpa only [scaledCutoff,div_eq_mul_inv,mul_comm] using (hcut T hT0).2
  have hbnd (p : ℕ × ℕ) :
      (∫ t in Icc T (2*T), ‖Phi (t/T)‖*
        density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
          js R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B) ≤
      Cb*T^(-(2-delta))*(P0*T) := by
    have hh : (∫ t in Icc T (2*T), ‖Phi (t/T)‖*
        density (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
          js R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B) ≤
        ∫ t in Icc T (2*T), Cb*T^(-(2-delta))*‖Phi (t/T)‖ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun t =>
        mul_nonneg (norm_nonneg (Phi (t/T))) (by unfold density; positivity))) hi ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hh := (density_bound _ _ _ js R L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B hLR).trans
        (hbody R N dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B hN hNT
          (by positivity) (by positivity) ht hA hB hsep)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (Phi (t/T)))).trans_eq (by ring)
    rw [integral_const_mul] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_left hphiMass (by positivity)
  have hgrid' : ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ) ≤ D*T := by
    simpa only [Real.rpow_one] using hgrid N hN T hNT hlog
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), Cb*T^(-(2-delta))*(P0*T) :=
      sum_le_sum (fun p hp => hbnd p)
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*(Cb*T^(-(2-delta))*(P0*T)) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*(Cb*T^(-(2-delta))*(P0*T)) := mul_le_mul_of_nonneg_right hgrid' (by positivity)
    _ = (D*Cb*P0)*T^delta := by
      have he : T*T^(-(2-delta))*T = T^delta := by
        calc
          _ = T^(1:ℝ)*T^(-(2-delta))*T^(1:ℝ) := by simp only [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT0,← Real.rpow_add hT0]; congr 1; ring
      calc
        _ = (D*Cb*P0)*(T*T^(-(2-delta))*T) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

theorem actual_tail_uniform (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eD eH delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (heD1 : eD < 1) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCommonCutMoment.actualTail P Phi js N T eD eH A B‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := uniform_mass P P Phi hP hPl hPr hP hPl hPr hPhi hcPhi hsPhi
    js S r eD eH delta hS hr heD he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [h,PRZZRejectedExhaustion.height_eventually eD heD1,
    PRZZGammaCentral.log_scaled_shifts_eventually S,eventually_ge_atTop (2:ℝ)] with T h hheight hsmall hT
  intro N A B hN hNT hA hB hsep
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne'
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hL
  apply PRZZActualTailCollector.actual_tail_of_native_budget P Phi js N T eD eH _ A B
    hP hPl hPr hPhi hsPhi hheight.1 hheight.2 (hsmall A B hA hB).1 (hsmall A B hA hB).2 hs
  filter_upwards [eventually_ge_atTop (PRZZLiteralExhaustion.spatialLength T)] with R hR
  have hp := h R (PRZZLiteralExhaustion.spatialLength T) N false A B hR hN hNT hA hB hsep
  have hsep' : r ≤ ‖(-B)+(-A)‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have hq := h R (PRZZLiteralExhaustion.spatialLength T) N true (-B) (-A) hR hN hNT
    (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA) hsep'
  have hh := add_le_add hp hq
  simpa only [PRZZActualTailCollector.pairedMass,profile,Bool.false_eq_true,if_false,if_true,neg_neg,neg_div,
    show C*T^delta*PRZZOptimalPowers.target N T+C*T^delta*PRZZOptimalPowers.target N T =
      (2*C)*T^delta*PRZZOptimalPowers.target N T by ring] using hh

#print axioms uniform_mass
#print axioms actual_tail_uniform
end XiPrime8845.PRZZBodyTailOptimal

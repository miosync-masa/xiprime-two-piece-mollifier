import PRZZNativeFreezeEnvelope

/-! Actual Gamma-weighted reflected freezing integrals. Kernel shifts
are -B/log T,-A/log T while the Gamma multiplier is that of A/log T,B/log T.
All arithmetic cutoff windows and finite spatial scales are retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Filter MeasureTheory
namespace XiPrime8845.PRZZDualNativeFreeze
open PRZZNativeFreezeEnvelope
set_option maxHeartbeats 8000000

def weight (phi : ℝ → ℂ) (T : ℝ) (A B : ℂ) (t : ℝ) : ℂ :=
  phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t

theorem weight_uniform (S : ℝ) (hS : 0 ≤ S) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop, ∀ (A B : ℂ) (phi : ℝ → ℂ) (P : ℝ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → Continuous phi → 0 ≤ P →
      (∀ t ∈ Set.Icc T (2*T), ‖phi t‖ ≤ P) →
      Continuous (weight phi T A B) ∧ ∀ t ∈ Set.Icc T (2*T), ‖weight phi T A B t‖ ≤ D*P := by
  refine ⟨Real.exp (2*S+7),by positivity,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    PRZZDualError.multiplier_scaled_cap S hS] with T hsmall hcap
  intro A B phi P hA hB hphi hP hp
  have hc := (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).continuous
  refine ⟨hphi.mul hc,?_⟩
  intro t ht
  rw [weight,norm_mul,mul_comm (Real.exp (2*S+7)) P]
  exact mul_le_mul (hp t ht) (hcap A B hA hB t ht) (norm_nonneg _) hP

theorem partition_bound (F G H : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hsH : Function.support H ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N K : ℕ) (M : ℝ) (A B : ℂ) (phi : ℝ → ℂ) (P : ℝ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → 0 < M →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → Continuous phi → 0 ≤ P →
      (∀ t ∈ Set.Icc T (2*T), ‖phi t‖ ≤ P) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        charge L J N K F G H (weight phi T A B) js T M ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hbound⟩ := PRZZFullFreezeBudget.partition_bound F G H hF hcF hsF hG hH hcG hcH hsG hsH
    js S r eps eta delta hS hr heps heta heta1 hmargin
  obtain ⟨D,hD,hweight⟩ := weight_uniform S hS
  refine ⟨C*D,by positivity,?_⟩
  filter_upwards [hweight,PRZZRejectedExhaustion.height_eventually eps heps1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*S/eta))),
    eventually_ge_atTop (1:ℝ)] with T hw hh hlog hT
  intro L J N K M A B phi P hN hscale hM hA hB hsep hphi hP hp
  obtain ⟨hcont,hcap⟩ := hw A B phi P hA hB hphi hP hp
  have hsep' : r ≤ ‖-B+-A‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have hs : (-B)/(Real.log T:ℂ)+(-A)/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep'))
      (by exact_mod_cast (ne_of_gt (show 0 < Real.log T by linarith [le_max_left 1 (2*S/eta)])))
  have he := hbound L J N K T M 0 (-B) (-A) (weight phi T A B) (D*P)
    (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA) hsep' hN hT
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hscale hh.2 hM hcont (by positivity) hcap
  calc
    _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        PRZZFullFreezeBudget.fullMass L J F (weight phi T A B) js N K T M ((2:ℝ)^p.1) ((2:ℝ)^p.2)
          eps 0 G H ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))
          (((-B)+(-A))/(Real.log T:ℂ)) := by
      apply sum_le_sum; intro p hp'
      simpa only [add_div] using dominates L J N K F G H (weight phi T A B) js T M
        ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps 0 _ _ hF hsF hsG hh.1 hM (by positivity) hs hh.2
    _ ≤ _ := he.trans_eq (by ring)

#print axioms weight_uniform
#print axioms partition_bound
end XiPrime8845.PRZZDualNativeFreeze

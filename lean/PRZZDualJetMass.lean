import PRZZDualJetTransfer

/-! Every genuine Gamma jet is inserted into the actual sourceW/cutoff
Leibniz mass. The same height threshold works for every derivative order;
only the explicit finite binomial constants depend on that order. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set Filter Topology MeasureTheory Finset
namespace XiPrime8845.PRZZDualJetMass
open PRZZDualJetTransfer PRZZFullWeightJets
set_option maxHeartbeats 8000000

theorem all_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2) (S rate : ℝ) (hS : 0 ≤ S) (hr : 0 < rate) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        ∀ (n : ℕ) (k : ℝ) (sigma : ℂ), 0 < k → sigma ≠ 0 →
        PRZZDualTimeIBP.jetMass F T k (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) sigma n ≤
          Real.exp (2*S+7)*
            convolution constant (fun j => convolution C (fun i => D i+E i/‖sigma‖^2) j) n*
              (k/(2*T))^(-rate)*T/T^n := by
  obtain ⟨C,D,E,hpos,hm⟩ := PRZZTimeAmplitude.mass F hF hcF rate hr
  refine ⟨C,D,E,hpos,?_⟩
  filter_upwards [scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (4:ℝ)] with T hcap hsmall hT
  intro A B hA hB n k sigma hk hs
  let a := A/(Real.log T:ℂ)
  let b := B/(Real.log T:ℂ)
  let V := fun j => convolution C (fun i => D i+E i/‖sigma‖^2) j
  have hT0 : 0 < T := by linarith
  have hV (j : ℕ) : 0 ≤ V j := by
    unfold V PRZZFullWeightJets.convolution
    exact sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
      (add_nonneg (hpos (j-i)).2.1 (div_nonneg (hpos (j-i)).2.2 (sq_nonneg _))))
  have hmass (j : ℕ) : (∫ t : ℝ, ‖iteratedDeriv j (PRZZTimeAmplitude.amplitude F T k sigma) t‖) ≤
      V j*(k/(2*T))^(-rate)*T/T^j := by
    have hh := hm j T k sigma hT0 hk hs
    rw [← PRZZTimeAmplitude.mass_window F hsF T k sigma hT0 j] at hh
    exact hh
  unfold PRZZDualTimeIBP.jetMass
  change _ ≤ Real.exp (2*S+7)*convolution constant V n*(k/(2*T))^(-rate)*T/T^n
  unfold PRZZFullWeightJets.convolution
  simp only [mul_sum,Finset.sum_mul,Finset.sum_div]
  apply sum_le_sum; intro i hi
  have hin : i ≤ n := by have := mem_range.mp hi; omega
  have hCi := constant_nonneg i
  have hmixed := PRZZDualFirstJet.mixed_mass F hF hsF T k
    (Real.exp (2*S+7)*constant i/T^i) a b sigma hT0 hk
    (hsmall.2 A hA) (hsmall.2 B hB) hs i (n-i)
    (by intro t ht; exact hcap A B hA hB i t ht)
  have hh := hmixed.trans (mul_le_mul_of_nonneg_left (hmass (n-i)) (by positivity))
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ (n.choose i:ℝ) by positivity)
  apply hh'.trans_eq
  have hp : T^i*T^(n-i) = T^n := by rw [← pow_add,Nat.add_sub_of_le hin]
  rw [← hp]
  field_simp
  <;> ring

#print axioms all_mass
end XiPrime8845.PRZZDualJetMass

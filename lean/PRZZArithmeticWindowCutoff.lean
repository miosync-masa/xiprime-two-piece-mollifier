import PRZZLocalFrequencyLoss
import PRZZSelectedLocalFourier
import PRZZCompatibleTail

/-! Adapter from the actual modulus-dependent local cutoff to a fixed
arithmetic-window cutoff. The condition Hraw>=1 is explicit: rounding a
subunit cutoff must not silently introduce a nonzero Fourier mode into
an otherwise empty source range. No transfer-band estimate is assumed. -/
noncomputable section
open scoped ContDiff
namespace XiPrime8845.PRZZArithmeticWindowCutoff
open PRZZSourceCutoffs PRZZMellinSeparation
set_option maxHeartbeats 4000000

def cutoff (d : ℕ) (T M V eH : ℝ) : ℕ := ⌈poissonCutoff d T M (3*V) eH⌉₊

/-- The actual evaluated right cutoff supplies the modulus upper bound. -/
theorem source_le_window (G : ℝ → ℂ) (d s u v : ℕ) (gap : ℤ)
    (T V eH : ℝ) (hd : 0 < d) (hT : 0 ≤ T) (hV : 0 < V)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hG : scaledCutoff G V ((d:ℝ)*v) ≠ 0) :
    PRZZSelectedLocalFourier.sourceCutoff T eH s d u v gap ≤ cutoff d T ((2:ℝ)^s) V eH := by
  have hg : G (V⁻¹*((d:ℝ)*v)) ≠ 0 := hG
  have hp := (hsG hg).2
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hpower : 0 ≤ T^eH := Real.rpow_nonneg hT eH
  have hv : (d:ℝ)*v ≤ 3*V := by
    calc
      _ = V*(V⁻¹*((d:ℝ)*v)) := by field_simp
      _ ≤ V*3 := mul_le_mul_of_nonneg_left hp hV.le
      _ = _ := by ring
  unfold PRZZSelectedLocalFourier.sourceCutoff cutoff
  apply Nat.ceil_le_ceil
  change poissonCutoff 1 T ((2:ℝ)^s) v eH ≤ poissonCutoff d T ((2:ℝ)^s) (3*V) eH
  unfold poissonCutoff
  rw [one_mul]
  calc
    _ = ((d:ℝ)*v)*T^eH/((d:ℝ)*(2:ℝ)^s) := by field_simp
    _ ≤ _ := by gcongr

/-- The strict H parameter corresponding to central modes |h|<=cutoff.
Above the unit threshold, ceiling plus one costs at most a factor three. -/
theorem rounded_height (d : ℕ) (T M V eH : ℝ)
    (h : 1 ≤ poissonCutoff d T M (3*V) eH) :
    (cutoff d T M V eH:ℝ)+1 ≤ 3*poissonCutoff d T M (3*V) eH := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ poissonCutoff d T M (3*V) eH by linarith)
  unfold cutoff
  linarith

/-- A fixed-window frequency range suitable for the existing signed
arithmetic evaluator, with all three rounding losses displayed. -/
theorem empty_or_frequency (N d : ℕ) (T M Q V eD eH : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hQ : 0 ≤ Q)
    (hraw : 1 ≤ poissonCutoff d T M (3*V) eH) :
    PRZZAStar.indices N d (deltaCutoff T M Q eD) ((cutoff d T M V eH:ℝ)+1) = ∅ ∨
      (1 ≤ PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q eD)
          ((cutoff d T M V eH:ℝ)+1) ∧
       (PRZZActualSignedBranches.frequencyBound d (deltaCutoff T M Q eD)
          ((cutoff d T M V eH:ℝ)+1):ℝ) ≤
          (18*T^(eD+eH))*(Q*V/((d:ℝ)^2*T))) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hD : 0 ≤ deltaCutoff T M Q eD := by unfold deltaCutoff; positivity
  have hp := cutoff_product d T M Q (3*V) eD eH hdR hT hM
  have hs : deltaCutoff T M Q eD*((cutoff d T M V eH:ℝ)+1)/(d:ℝ) ≤
      (9*T^(eD+eH))*(Q*V/((d:ℝ)^2*T)) := by
    calc
      _ ≤ deltaCutoff T M Q eD*(3*poissonCutoff d T M (3*V) eH)/(d:ℝ) := by
        gcongr
        exact rounded_height d T M V eH hraw
      _ = 3*(deltaCutoff T M Q eD*poissonCutoff d T M (3*V) eH/(d:ℝ)) := by ring
      _ = _ := by rw [hp]; ring
  have hh := PRZZSourceFrequency.empty_or_source_frequency N d (deltaCutoff T M Q eD)
    ((cutoff d T M V eH:ℝ)+1) Q V T (9*T^(eD+eH)) hs
  simpa only [show (2:ℝ)*(9*T^(eD+eH)) = 18*T^(eD+eH) by ring] using hh

/-- The actual central transfer band to the fixed arithmetic-window
cutoff, obtained from the proved Fourier-tail bound. This is pointwise;
its outer coefficient aggregation is not silently assumed. -/
theorem window_band (W G : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (a b S r eD eH power : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S)
    (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T Q V t residue : ℝ) (d s u v : ℕ) (gap : ℤ) (A B : ℂ),
      36 ≤ T → 1 ≤ Real.log T → (2:ℝ)^s ≤ T^b → 0 < u → 0 < v → (v:ℝ) ≤ T →
      t ∈ Set.Icc T (2*T) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      0 < d → 0 < Q → 0 < V → Q/2 ≤ (d:ℝ)*u →
      |(gap:ℝ)| ≤ deltaCutoff T ((2:ℝ)^s) Q eD/d →
      scaledCutoff G V ((d:ℝ)*v) ≠ 0 →
      ‖PRZZCentralTail.central W ((2:ℝ)^s) 1 residue ((u,v),(gap,1))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) t
          (cutoff d T ((2:ℝ)^s) V eH)-
        PRZZCentralTail.central W ((2:ℝ)^s) 1 residue ((u,v),(gap,1))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) t
          (PRZZSelectedLocalFourier.sourceCutoff T eH s d u v gap)‖ ≤
        ‖Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log (v:ℝ):ℂ))‖*(K*T^(-power)) := by
  obtain ⟨K,hK,h⟩ := PRZZCompatibleTail.central_band W hW hsW a b S r eD eH power
    ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro T Q V t residue d s u v gap A B hT hlog hM hu hv hvT ht hA hB hsep hd hQ hV hleft hgap hG
  have hcut := source_le_window G d s u v gap T V eH hd (by linarith) hV hsG hG
  exact h T ((2:ℝ)^s) t residue d Q (cutoff d T ((2:ℝ)^s) V eH) ((u,v),(gap,1)) A B
    hT hlog (by have hh : (1:ℝ) ≤ (2:ℝ)^s := one_le_pow₀ (by norm_num); linarith) hM
    hu hv hvT ht hA hB hsep (by exact_mod_cast hd) hQ hleft hgap hcut

#print axioms source_le_window
#print axioms rounded_height
#print axioms empty_or_frequency
#print axioms window_band
end XiPrime8845.PRZZArithmeticWindowCutoff

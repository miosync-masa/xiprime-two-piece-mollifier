import PRZZActualAggregate
import PRZZPositiveOuter

/-! Substitution of all actual arithmetic cases into the original literal A*.
The explicit finite dyadic/allocation budget, outer L1 mass and weighted
Mellin mass are retained. This is not an assertion of the optimized PRZZ
error exponent, nor the separate approximate-functional-equation reduction. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Complex
namespace XiPrime8845.PRZZActualAStar
open PRZZActualAggregate PRZZGCoefficient PRZZMellinSeparation
set_option maxHeartbeats 4000000

/-- Only Weil and DI are estimate premises. No CellBound, decomposition
equality, Fubini hypothesis, or global continuity of sourceW is supplied. -/
theorem literal_sourceW_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d : ℕ, ∀ T Q D H A B : ℝ, ∀ alpha betaShift sigma : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      sigma ≠ 0 → 0 < A → 0 < B → Function.support FM ⊆ Set.Icc A B →
      ∀ Phi : ℝ → ℂ, ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Set.Icc (1:ℝ) 2 →
      ‖PRZZAStar.literal N d D H T (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW sigma) Phi alpha betaShift‖ ≤
      (1/(2*Real.pi)) *
        (∫ p, ‖PRZZAStarIntegralBound.common N d T A B
          (PRZZDyadicEnvelope.sourceW sigma) alpha betaShift p‖) *
        totalBudget C w caps js eps eta beta T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K *
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C,hC,hw,harith⟩ := PRZZActualAggregate.signedSum_bound
    hWeil hDI K hK js eps eta beta S Z heps heta hbeta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d T Q D H A B alpha betaShift sigma hN hd hT hNT hdT hlog hfreq ha hz hb hsigma hA hB hsM Phi hPhi hsP
  apply PRZZPositiveOuter.literal_linear_positive N d D H T A B _ _ _ _ _ _ _ _ _
    hM (PRZZSourceWOuter.sourceW_continuous sigma hsigma) hPhi hsP hsM hN hd (by linarith) hA hB
  · exact totalBudget_nonneg C w caps js eps eta beta T _ N d K hC.le
      (fun q => (hw q).le) (by linarith) (by positivity)
  · intro p hp t
    exact harith N d T Q D H p.1 p.2 t alpha betaShift hN hd hT hNT hdT hlog hfreq ha hz hb

#print axioms literal_sourceW_bound
end XiPrime8845.PRZZActualAStar

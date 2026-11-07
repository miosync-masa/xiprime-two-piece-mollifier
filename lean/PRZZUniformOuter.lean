import PRZZUniformAggregate
import PRZZNegativeOuter

/-! Arithmetic constants for positive and negative integrals selected
before BOTH arithmetic and spatial scales, not indexed finite maxima. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZUniformOuter
open PRZZMellinSeparation PRZZActualAggregate PRZZNegativeArithmetic
set_option maxHeartbeats 10000000

theorem reflect_scaled (F : ℝ → ℂ) (Q : ℝ) :
    reflect (scaledCutoff F Q) = scaledCutoff (reflect F) Q := by
  funext x
  simp [reflect,scaledCutoff]

section
open PRZZNegativeArithmetic
open Complex Finset MeasureTheory
open PRZZAStar PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation PRZZKloostermanInputs
open PRZZActualAggregate
theorem negative_arithmetic
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 QM : ℝ, ∀ N d : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖negativeSum N d D H (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x y t‖ ≤
        totalBudget C w caps js eps eta b T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K*(1+|t|) := by
  have hrM : Continuous (reflect FM) := hM.comp continuous_neg
  have hrcM : HasCompactSupport (reflect FM) := hcM.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨caps,w,C,hC,hw,h⟩ := PRZZUniformAggregate.signedSum_bound hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 (reflect FM) hf hc hF hcF hrM hrcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 QM N d T Q D H x y t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb'
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  rw [negative_reflection,reflect_scaled]
  exact h Q2 QM N d T Q D H (-x) (-y) t alpha beta hN hd hT hNT hdT hlog hfreq ha hz hb'

end

#print axioms negative_arithmetic

section
open PRZZActualAStar
open MeasureTheory Complex
open PRZZActualAggregate PRZZGCoefficient PRZZMellinSeparation
theorem positive_sourceW
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 QM : ℝ, ∀ N d : ℕ, ∀ T Q D H A B : ℝ, ∀ alpha betaShift sigma : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      sigma ≠ 0 → 0 < A → 0 < B → Function.support (PRZZMellinSeparation.scaledCutoff FM QM) ⊆ Set.Icc A B →
      ∀ Phi : ℝ → ℂ, ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Set.Icc (1:ℝ) 2 →
      ‖PRZZAStar.literal N d D H T (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha betaShift‖ ≤
      (1/(2*Real.pi)) *
        (∫ p, ‖PRZZAStarIntegralBound.common N d T A B
          (PRZZDyadicEnvelope.sourceW sigma) alpha betaShift p‖) *
        totalBudget C w caps js eps eta beta T
          (PRZZActualSignedBranches.frequencyBound d D H) N d K *
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C,hC,hw,harith⟩ := PRZZUniformAggregate.signedSum_bound
    hWeil hDI K hK js eps eta beta S Z heps heta hbeta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 QM N d T Q D H A B alpha betaShift sigma hN hd hT hNT hdT hlog hfreq ha hz hb hsigma hA hB hsM Phi hPhi hsP
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  apply PRZZPositiveOuter.literal_linear_positive N d D H T A B _ _ _ _ _ _ _ _ _
    (hM.comp (continuous_const.mul continuous_id)) (PRZZSourceWOuter.sourceW_continuous sigma hsigma) hPhi hsP hsM hN hd (by linarith) hA hB
  · exact totalBudget_nonneg C w caps js eps eta beta T _ N d K hC.le
      (fun q => (hw q).le) (by linarith) (by positivity)
  · intro p hp t
    exact harith Q2 QM N d T Q D H p.1 p.2 t alpha betaShift hN hd hT hNT hdT hlog hfreq ha hz hb

end

#print axioms positive_sourceW

theorem negative_cell_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF2 : Continuous F2) (hcF2 : HasCompactSupport F2)
    (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ M Q2 : ℝ, ∀ N d J : ℕ, ∀ T Q D : ℝ, ∀ alpha beta : ℂ,
      0 < M → 0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖PRZZCentralArithmeticJoin.negativeCell N d J D T M
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F (scaledCutoff F0 Q) (scaledCutoff F2 Q2) Phi alpha beta‖ ≤
        PRZZCentralArithmeticJoin.positiveBudget C w caps js K N d J eps eta b D T M Phi alpha beta := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := negative_arithmetic hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 F hf hc hF2 hcF2 hF hcF
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro M Q2 N d J T Q D alpha beta hM hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs Phi hPhi hsPhi
  apply PRZZNegativeOuter.literal_linear N d D ((J:ℝ)+1) T M _ _ _ _ F Phi beta alpha (alpha+beta)
    hF hPhi hsF hsPhi hN hd (by linarith) hM hs
  intro p hp t
  exact h Q2 M N d T Q D ((J:ℝ)+1) p.1 p.2 t beta alpha hN hd hT hNT hdT hlog hfreq hbeta hz halpha

#print axioms negative_cell_uniform
#print axioms reflect_scaled
open PRZZCentralArithmeticJoin

theorem positive_cell_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF2 : Continuous F2) (hcF2 : HasCompactSupport F2)
    (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ M Q2 : ℝ, ∀ N d J : ℕ, ∀ T Q D : ℝ, ∀ alpha beta : ℂ,
      0 < M → 0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d J D T M (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        F (scaledCutoff F0 Q) (scaledCutoff F2 Q2) Phi alpha beta‖ ≤
        positiveBudget C w caps js K N d J eps eta b D T M Phi alpha beta := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := positive_sourceW hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 F hf hc hF2 hcF2 hF hcF
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro M Q2 N d J T Q D alpha beta hM hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs Phi hPhi hsPhi
  have hsM : Function.support (scaledCutoff F M) ⊆ Icc (M/2) (3*M) := by
    intro y hy
    have hh := hsF hy
    have he : M*(M⁻¹*y)=y := by field_simp
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hM.le,
      mul_le_mul_of_nonneg_left hh.2 hM.le]
  exact h Q2 M N d T Q D ((J:ℝ)+1) (M/2) (3*M) beta alpha (alpha+beta)
    hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs (by positivity) (by positivity) hsM Phi hPhi hsPhi

#print axioms positive_cell_uniform
end XiPrime8845.PRZZUniformOuter

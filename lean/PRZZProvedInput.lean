import PRZZWitnessBridge

/-! Proved replacement of the former public PRZZ witness axiom.
DeepInputs bundles explicit Weil/DI hypotheses, not an axiom or a default
instance. Headline theorems expose both hypotheses separately. -/
noncomputable section
namespace XiPrime8845
namespace PRZZProvedInput
class DeepInputs : Prop where
  weil : PRZZKloostermanInputs.WeilIncomplete
  di : PRZZKloostermanInputs.DeshouillersIwaniecLemma1
end PRZZProvedInput
namespace PRZZ

/-- The former witness input, now proved from the two stated deep inputs. -/
theorem przz41_case3_K2_witness
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (theta : ℝ) (hTheta0 : 0 < theta) (hTheta1 : theta < 4/7)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (shiftBound poleGap eps : ℝ) (hShift : 0 < shiftBound)
    (hGap : 0 < poleGap) (hEps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖twistedMoment witness witness theta T Phi A B -
        densityGcdMainTerm witness witness theta T Phi A B‖ ≤
        C * Real.rpow T eps *
          (Real.rpow (length theta T) (7/4) +
           Real.rpow (length theta T) (7/8) * Real.rpow T (1/2)) :=
  PRZZWitnessBridge.witness_estimate hWeil hDI theta hTheta0 hTheta1 Phi hPhi
    shiftBound poleGap eps hShift hGap hEps

/-- Apply only the witness input, returning the historical square main
term by the proved finite-sum symmetry, not by a general-profile axiom. -/
theorem witness_przz_estimate [PRZZProvedInput.DeepInputs]
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (shiftBound poleGap : ℝ) (hShift : 0 < shiftBound) (hGap : 0 < poleGap) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖twistedMoment witness witness (4/7-1/1000000) T Phi A B -
        gcdMainTerm witness witness (4/7-1/1000000) T Phi A B‖ ≤
        C * Real.rpow T (7/16000000) *
          (Real.rpow (length (4/7-1/1000000) T) (7/4) +
           Real.rpow (length (4/7-1/1000000) T) (7/8) * Real.rpow T (1/2)) := by
  simpa only [witness_densityGcdMainTerm_eq] using
    (przz41_case3_K2_witness PRZZProvedInput.DeepInputs.weil PRZZProvedInput.DeepInputs.di _ (by norm_num) (by norm_num)
      Phi hPhi shiftBound poleGap _ hShift hGap (by norm_num))

#print axioms przz41_case3_K2_witness
#print axioms witness_przz_estimate
end PRZZ
end XiPrime8845

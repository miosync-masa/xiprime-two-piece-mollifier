import PRZZAStarWindow

/-! A window-localized product majorant for Mellin Fubini. Measurability
and the actual amplitude envelope remain explicit until supplied for
the separated arithmetic kernel. No untruncated Fubini is asserted. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZWindowDominance

theorem joint_integrable (N : ℕ) (T A B C : ℝ) (M : ℝ → ℂ)
    (K : (ℝ × ℝ) → ℝ → ℂ) (hM : Integrable M)
    (hK : AEStronglyMeasurable (Function.uncurry K))
    (hbound : ∀ p t, ‖K p t‖ ≤
      (PRZZAStarWindow.window N T A B).indicator (fun _ => C) p * ‖M t‖) :
    Integrable (Function.uncurry K) := by
  have hs : IsCompact (PRZZAStarWindow.window N T A B) :=
    isCompact_Icc.prod isCompact_Icc
  have hi : Integrable ((PRZZAStarWindow.window N T A B).indicator (fun _ => C)) :=
    (integrable_indicator_iff hs.measurableSet).mpr
      (ContinuousOn.integrableOn_compact hs continuousOn_const)
  exact (hi.mul_prod hM.norm).mono' hK (Filter.Eventually.of_forall
    (fun q => hbound q.1 q.2))

theorem mellin_swap (N : ℕ) (T A B C : ℝ) (M : ℝ → ℂ)
    (K : (ℝ × ℝ) → ℝ → ℂ) (hM : Integrable M)
    (hK : AEStronglyMeasurable (Function.uncurry K))
    (hbound : ∀ p t, ‖K p t‖ ≤
      (PRZZAStarWindow.window N T A B).indicator (fun _ => C) p * ‖M t‖) :
    (∫ p, ∫ t, K p t) = ∫ t, ∫ p, K p t :=
  integral_integral_swap (joint_integrable N T A B C M K hM hK hbound)

#print axioms joint_integrable
#print axioms mellin_swap
end XiPrime8845.PRZZWindowDominance

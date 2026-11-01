import PRZZDyadicSupport

/-! A genuinely grouped sharp convolution is bounded by the seven DI
terms in its supplied support boxes. Coefficient envelopes are explicit;
balancing the boxes and summing the original d/h decomposition is separate. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZGroupedSeven
open PRZZSharpDI PRZZSharpGrouped PRZZDyadicSupport PRZZKloostermanInputs PRZZDISeven
set_option maxHeartbeats 2000000

theorem grouped_seven (hDI : DeshouillersIwaniecLemma1) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ N E F : ℕ, 1 ≤ E → E ≤ N → 1 ≤ F → F ≤ N →
      ∀ A V : ℝ, 1 ≤ A → 1 ≤ V → ∀ h : ℕ, 1 ≤ h →
      ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ (r nu : ℕ → ℂ) (alpha beta : ArithmeticFunction ℂ),
      (∀ n, E < n → alpha n = 0) → (∀ n, F < n → beta n = 0) →
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) → (∀ f ∈ Icc 1 F, ‖beta f‖ ≤ S) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nu a‖ ≤ P) → (∀ e ∈ Icc 1 E, ‖alpha e‖ ≤ Q) →
      ‖grouped N V A h r nu alpha beta‖ ≤
        (1+2*Real.log ((F:ℝ)+1))*(R*S*(P*Q)*K*
          ((V*F*A*E)^eps*seven h E A ((E:ℝ)*F) V)) := by
  obtain ⟨K,hK,hb⟩ := sharpBlock_log_bound hDI eps heps
  refine ⟨K,hK,?_⟩
  intro N E F hE hEN hF hFN A V hA hV h hh R S P Q hR hS hP hQ r nu alpha beta
    hsalpha hsbeta hr hbeta hnu halpha
  rw [grouped_eq,sharp_shrink N E F hEN hFN V A h r beta nu alpha hsalpha hsbeta]
  have hER : (1:ℝ) ≤ E := by exact_mod_cast hE
  have hFR : (1:ℝ) ≤ F := by exact_mod_cast hF
  have hb' := hb N V F A E hV hFR hA hER h hh R S P Q hR hS hP hQ
    r beta nu alpha hr (by simpa only [Nat.floor_natCast] using hbeta)
    hnu (by simpa only [Nat.floor_natCast] using halpha)
  simp only [Nat.floor_natCast] at hb'
  apply hb'.trans
  have hl : 0 ≤ 1+2*Real.log ((F:ℝ)+1) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ (F:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) F; linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (PRZZDIExpansion.diBound_seven eps E A F V h hh
      (by linarith) (by linarith) (by linarith) (by linarith)) (by positivity)) hl

#print axioms grouped_seven
end XiPrime8845.PRZZGroupedSeven

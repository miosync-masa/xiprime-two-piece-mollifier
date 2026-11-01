import PRZZBranchEnvelope
import PRZZSharpAggregation

/-! Substitute the proved envelopes of actual HB subgroups into signed DI.
The sharp product cutoff and both frequency signs are retained. This does
not identify the original frequency coefficient nu or sum branch weights. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZBranchSeven
open PRZZBranchEnvelope PRZZHBBranches PRZZSharpDI PRZZDISeven PRZZKloostermanInputs
set_option maxHeartbeats 2000000

theorem signed_branch_seven (hDI : DeshouillersIwaniecLemma1)
    (K : ℕ) (js : List ℕ) (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y b, b ∈ branches y K js →
      ∀ left right : List (ArithmeticFunction ℝ × Set ℕ),
      (left.map Prod.fst).Sublist b.2 → (right.map Prod.fst).Sublist b.2 →
      ∀ sl sr : Set ℕ, ∀ wl wr : ℕ → ℂ,
      (∀ n, ‖wl n‖ ≤ 1) → (∀ n, ‖wr n‖ ≤ 1) →
      ∀ N : ℕ, ∀ A E F V : ℝ, 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ h : ℕ, 1 ≤ h → ∀ R P : ℝ, 0 ≤ R → 0 < P →
      ∀ r nuPlus nuMinus : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nuPlus a‖ ≤ P) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nuMinus a‖ ≤ P) →
      ‖sharpNegativeBlock N V F A E h r (coefficient right sr wr) nuPlus (coefficient left sl wl)+
        sharpBlock N V F A E h r (coefficient right sr wr) nuMinus (coefficient left sl wl)‖ ≤
      2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*(R*(C*F^eta)*(P*(C*E^eta))*D*
        ((V*F*A*E)^eps*seven h E A (E*F) V))) := by
  obtain ⟨C,hC,hc⟩ := branch_rectangle K js eta heta
  obtain ⟨D,hD,hd⟩ := PRZZSharpAggregation.sharp_signed_seven hDI eps heps
  refine ⟨C,D,hC,hD,?_⟩
  intro y b hb left right hl hr sl sr wl wr hwl hwr N A E F V hA hE hF hV h hh R P hR hP
    r np nm hrv hnp hnm
  exact hd N A E F V hA hE hF hV h hh R (C*F^eta) P (C*E^eta) hR
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)) hP
    (mul_pos hC (Real.rpow_pos_of_pos (by linarith) _))
    r (coefficient right sr wr) np nm (coefficient left sl wl) hrv
    (hc y b hb right hr sr wr hwr F hF) hnp hnm (hc y b hb left hl sl wl hwl E hE)

#print axioms signed_branch_seven
end XiPrime8845.PRZZBranchSeven

import PRZZActualBranchCells
import PRZZWeightedDI

/-! DI bounds with the envelopes of actual complementary HB cell groups
supplied, including arbitrary arithmetic masks and unit twists. The source
row identification, Type I estimates and normalized h-average scale range
remain separate. The product weight and its variation cost are retained. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZActualBranchDI
open PRZZActualBranchCells PRZZHBBranches
set_option maxHeartbeats 2000000

def coefficient (N : ℕ) (b : Branch) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (q : Set ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  q.indicator (fun n => (group N b k s n:ℂ)*w n) n

/-- C and D precede every literal branch, dyadic cell and group selection.
Neither subgroup coefficient bound is an input. DI alone is explicit. -/
theorem signed_group_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (js : List ℕ) (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ N y b, b ∈ branches y K js →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ q1 q2 : Set ℕ, ∀ t1 t2 : ℕ → ℂ,
      (∀ n, ‖t1 n‖ ≤ 1) → (∀ n, ‖t2 n‖ ≤ 1) →
      ∀ V F A E : ℝ, 1 ≤ V → 1 ≤ F → 1 ≤ A → 1 ≤ E →
      ∀ h : ℕ, 1 ≤ h → ∀ R P : ℝ, 0 ≤ R → 0 < P →
      ∀ r np nm w : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊V⌋₊, ‖r c‖ ≤ R) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖np a‖ ≤ P) →
      (∀ a ∈ Icc 1 ⌊A⌋₊, ‖nm a‖ ≤ P) →
      ‖PRZZWeightedDI.negative N V F A E h r
          (coefficient N b k (univ \ s) q2 t2) np (coefficient N b k s q1 t1) w +
        PRZZWeightedDI.weighted N V F A E h r
          (coefficient N b k (univ \ s) q2 t2) nm (coefficient N b k s q1 t1) w‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*(R*(C*F^eta)*(P*(C*E^eta))*D*
          ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V)))*
            PRZZTypeI.variation (fun j => w (j+1)) N := by
  obtain ⟨C,hC,hc⟩ := common_rectangle K js eta heta
  obtain ⟨D,hD,hd⟩ := PRZZWeightedDI.signed_seven hDI eps heps
  refine ⟨C,D,hC,hD,?_⟩
  intro N y b hb k s q1 q2 t1 t2 ht1 ht2 V F A E hV hF hA hE h hh R P hR hP r np nm w hr hp hm
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  exact hd N V F A E hV hF hA hE h hh R (C*F^eta) P (C*E^eta)
    hR (by positivity) hP (by positivity) r _ np nm _ w hr
    (hc N y b hb k (univ \ s) q2 t2 ht2 F hF) hp hm
    (hc N y b hb k s q1 t1 ht1 E hE)

#print axioms signed_group_seven
end XiPrime8845.PRZZActualBranchDI

/- Spatial cutoff support is unrestricted here: only its common norm cap is used. -/
import PRZZClassSources
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZClassSpatialSources
open PRZZClassSources PRZZActualBranchCells PRZZHBBranches PRZZMellinSeparation
open PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 8000000
theorem small_source_class (K : ℕ) (ks js : List ℕ) (eta S width : ℝ)
    (heta : 0 < eta) (hS : 0 ≤ S) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) →
      ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ U T Q x y0 t D H A : ℝ, ∀ alpha beta : ℂ,
      (∏ i, (2:ℝ)^(k i)) = U → U ≤ 2*2^((ks.length+1)*(2*K)) →
      0 < N → 0 < d → 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*T^eta*A^eta*A*((2:ℝ)^(l+1)) := by
  obtain ⟨C,hC,h⟩ := small_source K ks js eta S heta hS (jets 0) (jets 0) (jets 0)
    (hj 0) (hj 0) (hj 0)
  refine ⟨C,hC,?_⟩
  intro F0 F2 FM h0 h2 hm
  exact h F0 F2 FM (member_sup width jets F0 h0) (member_sup width jets F2 h2)
    hm

#print axioms small_source_class
end XiPrime8845.PRZZClassSpatialSources

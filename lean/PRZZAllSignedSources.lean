import PRZZActualSignedBranches
import PRZZAllocationMass

/-! The original signedSum in actual signed-source cells, simultaneously
for every labelled allocation, supported h, HB branch and dyadic grid.
This exact identity supplies the decomposition, not the analytic bounds. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZAllSignedSources
open PRZZActualSignedBranches PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
open PRZZCoefficientSeparation PRZZSupportedSplit PRZZGCoefficient
set_option maxHeartbeats 2000000

def blocks (N d h j l K : ℕ) (ks js : List ℕ) (D H x y t : ℝ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ((branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks).map
    (fun b => (b.1:ℂ)*∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
      PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b (fun i => (k i).val)
        (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y (a:ℤ))
        (fun a => nu (frequencies d D H) x y (-(a:ℤ))))).sum

theorem signedCells_eq (N d K : ℕ) (D H : ℝ) (js : List ℕ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    PRZZHiAllocatedCells.signedCells N d K D H js F1 F2 FM alpha beta x y t =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
          (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 js D H x y t F1 F2 FM alpha beta)).sum := by
  unfold PRZZHiAllocatedCells.signedCells
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro l hl
  rw [sum_list]
  congr 1
  apply List.map_congr_left; intro q hq
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro h hh
  unfold blocks
  rw [← cells_eq_sources N d h j l K q.2 js D H x y t F1 F2 FM alpha beta,mul_sum]
  apply sum_congr rfl; intro v hv
  ring

/-- No decomposition hypothesis is assumed: every original arithmetic
coefficient and every original finite cutoff occurs on the right. -/
theorem signedSum_eq (N d K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H : ℝ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x y t : ℝ) :
    signedSum N d D H (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x y t =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
          (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 js D H x y t F1 F2 FM alpha beta)).sum := by
  rw [PRZZHiAllocatedCells.signedSum_eq N d K hd hK,signedCells_eq]

#print axioms signedCells_eq
#print axioms signedSum_eq

/-- Scalar branch weights and every factor-grid multiplicity are supplied
uniformly in the actual local cutoff. Only the cell's analytic bound B
remains an input; no positivity of the complex arithmetic sum is used. -/
theorem blocks_bound (K : ℕ) (ks : List ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d h j l : ℕ, 1 ≤ N → ∀ T B : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B →
      ∀ js : List ℕ, ∀ D H x y t : ℝ, ∀ F1 F2 FM : ℝ → ℂ, ∀ alpha beta : ℂ,
      (∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
        ∀ k : Fin b.2.length → Fin (Nat.log 2 N+1),
          ‖PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b (fun i => (k i).val)
            (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t
            (fun a => nu (frequencies d D H) x y (a:ℤ))
            (fun a => nu (frequencies d D H) x y (-(a:ℤ)))‖ ≤ B) →
      ‖blocks N d h j l K ks js D H x y t F1 F2 FM alpha beta‖ ≤ C*T^eta*B := by
  obtain ⟨D,hD,hd⟩ := PRZZDyadicBudget.grids_absorbed ((ks.length+1)*(2*K)) eta heta
  have hm := PRZZBranchMass.mass_nonneg K ks
  refine ⟨PRZZBranchMass.mass K ks*D+1,by positivity,?_⟩
  intro N d h j l hN T B hNT hT hB js DD H x y t F1 F2 FM alpha beta hb
  unfold blocks
  have hs := PRZZBranchMass.sum_bound ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks
    (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
      PRZZSignedSourceCell.source N d j l h (frequencyBound d DD H) b (fun i => (k i).val)
        (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t
        (fun a => nu (frequencies d DD H) x y (a:ℤ))
        (fun a => nu (frequencies d DD H) x y (-(a:ℤ)))) (D*T^eta*B) (by
      intro b hbr
      apply (norm_sum_le _ _).trans
      have hg := sum_le_sum (fun k (_ : k ∈ univ) => hb b hbr k)
      have hg' : (∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
          ‖PRZZSignedSourceCell.source N d j l h (frequencyBound d DD H) b (fun i => (k i).val)
            (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t
            (fun a => nu (frequencies d DD H) x y (a:ℤ))
            (fun a => nu (frequencies d DD H) x y (-(a:ℤ)))‖) ≤
          (Nat.log 2 N+1:ℝ)^b.2.length*B := by simpa [Fintype.card_fun] using hg
      exact hg'.trans (mul_le_mul_of_nonneg_right
        (hd N hN T hNT hT b.2.length (PRZZBranchDegrees.branches_length _ K ks b hbr)) hB))
  have ht : 0 ≤ T^eta := Real.rpow_nonneg ((Nat.cast_nonneg N).trans hNT) _
  exact hs.trans (by nlinarith)

#print axioms blocks_bound
end XiPrime8845.PRZZAllSignedSources

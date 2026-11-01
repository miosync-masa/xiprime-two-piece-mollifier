import PRZZSupportedSource
import PRZZAllBranchCells
import PRZZLinearOuter

/-! Literal signed source expanded into every allocated local HB cell.
The local cutoff is N/(d*h); all phases, coprimality and sharp constraints
stay inside the summand. No analytic block bound is assumed here. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZAllocatedCells
open PRZZHBBranches PRZZActualBranchCells PRZZSupportedSplit PRZZSupportedAllocation
open PRZZSupportedBranches PRZZSupportedSource PRZZGCoefficient PRZZCoefficientSeparation
open PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def cells (N d h K : ℕ) (js : List ℕ) (F : ℕ → ℂ) : ℂ :=
  ((branches ⌊((N/(d*h):ℕ):ℝ)^((K:ℝ)⁻¹)⌋₊ K js).map
    (fun b => ∑ k : Fin b.2.length → Fin (Nat.log 2 N+1),
      ∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
        (b.1:ℂ)*(group N b (fun i => (k i).val) univ n:ℂ)*F (h*n) else 0)).sum

theorem residual_eq (N d h K : ℕ) (js : List ℕ) (F : ℕ → ℂ)
    (hd : 0 < d) (hh : 0 < h) (hK : 0 < K) :
    residual N d js F h = cells N d h K js F := by
  let w := fun n => if d.Coprime n ∧ d*(h*n) ≤ N then F (h*n) else 0
  have hw : ∀ n ∈ Icc 1 N, N/(d*h) < n → w n = 0 := by
    intro n hn hlarge
    have hc : ¬d*(h*n) ≤ N := by
      intro hc
      have hh' : n ≤ N/(d*h) := (Nat.le_div_iff_mul_le (Nat.mul_pos hd hh)).mpr (by nlinarith)
      omega
    simp [w,hc]
  have he := PRZZAllBranchCells.local_all N (N/(d*h)) K js hK w hw
  have hl : residual N d js F h = ∑ n ∈ Icc 1 N, w n*(coefficient js n:ℂ) := by
    unfold PRZZSupportedAllocation.residual
    apply sum_congr rfl; intro n hn
    dsimp [w]; split_ifs <;> ring
  rw [hl,he,cells]
  congr 1
  apply List.map_congr_left; intro b hb
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro n hn
  dsimp [w]; split_ifs <;> ring

def signedCells (N d K : ℕ) (D H : ℝ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
    ∑ m ∈ (frequencies d D H).image freq,
      nu (frequencies d D H) x y m *
        ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
          (sourceG q.1 0 0 d h:ℂ)*cells N d h K q.2
            (row N d j l (fun _ => 1) (fun n => (coefficient js n:ℂ))
              F1 F2 FM alpha beta x t m))).sum

theorem signedSum_eq (N d K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H : ℝ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x y t : ℝ) :
    signedSum N d D H (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x y t =
      signedCells N d K D H js F1 F2 FM alpha beta x y t := by
  rw [signedSum_allocated N d hd,signedAllocated,signedCells]
  apply sum_congr rfl; intro j hj
  apply sum_congr rfl; intro l hl
  apply sum_congr rfl; intro m hm
  congr 1
  unfold allocatedRectangle
  congr 1
  apply List.map_congr_left; intro q hq
  apply sum_congr rfl; intro h hh
  rw [residual_eq N d h K q.2 _ (by omega) (by have := (mem_hSupport N d h hh).1; omega) hK]

#print axioms residual_eq
#print axioms signedSum_eq

/-- The original A* consumes the displayed full local-cell sum. Its
decomposition and Mellin outer integration are supplied, not hypotheses.
The remaining input is a uniform bound on this explicit arithmetic sum. -/
theorem literal_bound (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d K : ℕ, 0 < N → 0 < d → 0 < K → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ D H M : ℝ, 0 ≤ M →
      ∀ (js : List ℕ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(alpha+beta).re| ≤ S/Real.log T →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t : ℝ,
        ‖signedCells N d K D H js F1 F2 FM alpha beta p.1 p.2 t‖ ≤ M*(1+|t|)) →
      ‖PRZZAStar.literal N d D H T (fun n => (coefficient js n:ℂ)) F1 F2 FM W Phi alpha beta‖ ≤
        C*(T/d)*M := by
  obtain ⟨C,hC,h⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  refine ⟨C,hC,?_⟩
  intro N d K hN hd hK T hT hL hNT D H M hM js F1 F2 FM alpha beta hFM hsM hz hb
  apply h N d hN hd T hT hL hNT D H M hM _ F1 F2 FM alpha beta hFM hsM hz
  intro p hp t
  rw [signedSum_eq N d K (by omega) hK]
  exact hb p hp t

#print axioms literal_bound
end XiPrime8845.PRZZAllocatedCells

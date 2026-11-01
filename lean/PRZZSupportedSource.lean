import PRZZSupportedAllocation
import PRZZSupportedBranches

/-! Source rectangles and the literal signed integrand in allocated h form.
The remaining balanced DI norm supplier is not disguised as an identity. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZSupportedSource
open PRZZSupportedSplit PRZZSupportedAllocation PRZZSupportedBranches
open PRZZHBRectangles PRZZGCoefficient PRZZCoefficientSeparation
open PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 2000000

theorem row_factor (N d j l : ℕ) (a b : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) (n : ℕ) :
    row N d j l a b F1 F2 FM α β x t k n =
      a (d*n)*row N d j l (fun _ => 1) b F1 F2 FM α β x t k n := by
  unfold row
  split_ifs with hn
  · rw [mul_sum]
    apply sum_congr rfl
    intros
    split_ifs <;> ring
  · simp

def allocatedRectangle (N d j l : ℕ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x t : ℝ) (k : ℤ) : ℂ :=
  ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
    (sourceG q.1 0 0 d h:ℂ)*residual N d q.2
      (row N d j l (fun _ => 1) (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x t k) h)).sum

theorem rectangle_allocated (N d j l : ℕ) (hd : 1 ≤ d) (js : List ℕ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    PRZZAStarRectangles.rectangle N d j l (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x t k =
      allocatedRectangle N d j l js F1 F2 FM α β x t k := by
  rw [← mixed_diagonal,mixed_row]
  simp_rw [row_factor N d j l (fun n => (coefficient js n:ℂ))
    (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x t k]
  exact weighted_source N d hd js _

def signedAllocated (N d : ℕ) (D H : ℝ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (α β : ℂ) (x y t : ℝ) : ℂ :=
  ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
    ∑ k ∈ (frequencies d D H).image freq,
      nu (frequencies d D H) x y k * allocatedRectangle N d j l js F1 F2 FM α β x t k

theorem signedSum_allocated (N d : ℕ) (hd : 1 ≤ d) (D H : ℝ) (js : List ℕ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x y t : ℝ) :
    signedSum N d D H (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x y t =
      signedAllocated N d D H js F1 F2 FM α β x y t := by
  rw [PRZZAStarRectangles.signedSum_rectangles]
  simp_rw [rectangle_allocated N d _ _ hd]
  rfl

/-- Compose the exact source rectangle with the existing G average.
Constants are chosen before all cutoffs, shifts, weights and frequencies.
The only analytic block input is now the norm of the displayed residual. -/
theorem rectangle_average (η β0 : ℝ) (hη : 0 < η) (hβ : 0 < β0) :
    ∃ C : List ℕ → ℝ, (∀ js, 0 < C js) ∧
      ∀ N d j l : ℕ, 1 ≤ N → 1 ≤ d → ∀ js : List ℕ,
      ∀ (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ),
      ∀ (X A V B : ℝ) (E : ℕ → ℝ), 0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ B →
      (∀ h ∈ hSupport N d, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      (∀ q ∈ allocations js, ∀ h ∈ hSupport N d,
        ‖residual N d q.2 (row N d j l (fun _ => 1) (fun n => (coefficient js n:ℂ))
          F1 F2 FM α β x t k) h‖ ≤ B*PRZZDISeven.seven h (E h) A (X/h) V) →
      ‖PRZZAStarRectangles.rectangle N d j l (fun n => (coefficient js n:ℂ))
        F1 F2 FM α β x t k‖ ≤
      ((allocations js).map (fun q =>
        B*(PRZZDISeven.envelope X A V*(C q.1*(d:ℝ)^η*(N:ℝ)^β0)))).sum := by
  choose C hC hb using (fun js => residual_average js η β0 hη hβ)
  refine ⟨C,hC,?_⟩
  intro N d j l hN hd js F1 F2 FM α β x t k X A V B E hX hA hV hB hE hblocks
  rw [rectangle_allocated N d j l hd,allocatedRectangle]
  apply list_budget
  intro q hq
  exact hb q.1 N d hN hd q.2 X A V B E _ hX hA hV hB hE (hblocks q hq)

/-- External integration now consumes the explicit allocated source sum;
there is no assumed A-star decomposition in this interface. The remaining
uniform arithmetic budget M must still be proved from Weil/DI estimates. -/
theorem literal_uniform_allocated (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T → ∀ D H M : ℝ, 0 ≤ M →
      ∀ (js : List ℕ) (F1 F2 FM : ℝ → ℂ) (α β : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(α+β).re| ≤ S/Real.log T →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t : ℝ,
        ‖signedAllocated N d D H js F1 F2 FM α β p.1 p.2 t‖ ≤ M) →
      ‖PRZZAStar.literal N d D H T (fun n => (coefficient js n:ℂ)) F1 F2 FM W Phi α β‖ ≤
        C*(T/d)*M := by
  obtain ⟨C,hC,h⟩ := PRZZOuterMass.literal_uniform W Phi hW hPhi hsP A B S hA hB hS
  refine ⟨C,hC,?_⟩
  intro N d hN hd T hT hL hNT D H M hM js F1 F2 FM α β hFM hsM hz hb
  apply h N d hN hd T hT hL hNT D H M hM _ F1 F2 FM α β hFM hsM hz
  intro p hp t
  rw [signedSum_allocated N d hd]
  exact hb p hp t

#print axioms literal_uniform_allocated
#print axioms rectangle_average
#print axioms row_factor
#print axioms rectangle_allocated
#print axioms signedSum_allocated
end XiPrime8845.PRZZSupportedSource

import PRZZOriginalRowWindow
import PRZZAllSignedSources

/-! The original row's retained Mellin window and its exact signed HB
branches. All arithmetic restrictions and allocation multiplicities remain. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZRowMellinBranches
open PRZZAStar PRZZAStarNu PRZZNuCoefficient PRZZMellinSeparation
open PRZZOriginalRowWindow PRZZActualMellin PRZZAStarMellin
open PRZZAllSignedSources PRZZSupportedSource PRZZCoefficientSeparation
open PRZZSupportedSplit PRZZGCoefficient
set_option maxHeartbeats 3000000

def signedRow (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  ∑ v ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y v *
    PRZZAStarRectangles.rectangle N d j l a F1 F2 FM alpha beta x t v

theorem signedRow_blocks (N d j l K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H : ℝ) (js : List ℕ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x y t : ℝ) :
    signedRow N d j l D H (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x y t =
      ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
        (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 js D H x y t F1 F2 FM alpha beta)).sum := by
  unfold signedRow
  simp_rw [rectangle_allocated N d j l hd,allocatedRectangle]
  rw [PRZZActualSignedBranches.sum_list]
  congr 1
  apply List.map_congr_left
  intro q hq
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h hh
  have he (v : ℤ) := PRZZHiAllocatedCells.residual_eq N d h j K q.2
    (PRZZSupportedBranches.row N d j l (fun _ => 1)
      (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t v) hK (by
        intro n hcut hlarge
        exact PRZZHiAllocatedCells.row_vanish N d h j l (by omega)
          (by have := (mem_hSupport N d h hh).1; omega)
          (fun _ => 1) (fun n => (coefficient js n:ℂ)) F1 F2 FM alpha beta x t v n hcut hlarge)
  simp_rw [he]
  unfold blocks
  rw [← PRZZActualSignedBranches.cells_eq_sources,mul_sum]
  apply sum_congr rfl
  intro v hv
  ring

theorem row_amplitude (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    (∑ z ∈ rowIndices N d j l D H,
      amplitude d a F1 F2 FM W alpha beta x y z*twist z.1.1 t*twist z.1.2 t) =
      (W (2*Real.pi*x/y)/((d:ℂ)*(x:ℂ)^(alpha+beta)))*
        signedRow N d j l D H a F1 F2 FM alpha beta x y t := by
  classical
  let ps := (pairs N d).filter (fun i => i.1 ∈ PRZZDyadic.cell N j ∧ i.2 ∈ PRZZDyadic.cell N l)
  have hidx : rowIndices N d j l D H = ps.product (frequencies d D H) := by
    ext z
    simp [rowIndices,ps,indices,pairs,frequencies,and_assoc,and_left_comm,and_comm]
  have hr (v : ℤ) : PRZZAStarRectangles.rectangle N d j l a F1 F2 FM alpha beta x t v =
      ∑ i ∈ ps, pairCoeff d a F1 F2 FM alpha beta x t i *
        PRZZKloostermanInputs.e (-(v:ℝ)*PRZZKloostermanInputs.inverseResidue i.2 i.1/i.2) := by
    simp only [ps,pairs,PRZZAStarRectangles.rectangle,PRZZDyadic.cell,
      sum_filter,Finset.product_eq_sprod,Finset.sum_product,mem_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hj : Nat.log 2 n = j
    · simp only [hj,if_true,hn,true_and]
      apply sum_congr rfl
      intro m hm
      by_cases hl : Nat.log 2 m = l <;>
        by_cases hc : n.Coprime m ∧ d*n ≤ N ∧ d*m ≤ N <;> simp [hm,hl,hc]
    · simp [hj,hn]
  unfold signedRow
  simp_rw [hr]
  rw [← PRZZNuCoefficient.separate,hidx]
  simp only [Finset.product_eq_sprod,Finset.sum_product,mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro q hq
  simp only [amplitude,prefactor,outerKernel,pairCoeff,PRZZNuCoefficient.oscillation,freq,
    Int.cast_mul,Int.cast_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

theorem row_localized (N d j l : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (p : ℝ × ℝ) (t : ℝ) :
    (∑ z ∈ rowIndices N d j l D H,
      localized N d T A B a F1 F2 FM W Phi alpha beta z p t) =
      (PRZZAStarWindow.window N T A B).indicator
        (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))) p *
      mellin Phi (t*I)*twist (p.1*p.2/T) t *
      signedRow N d j l D H a F1 F2 FM alpha beta p.1 p.2 t := by
  by_cases hp : p ∈ PRZZAStarWindow.window N T A B
  · simp only [localized,Set.indicator_of_mem hp]
    have he := row_amplitude N d j l D H a F1 F2 FM W alpha beta p.1 p.2 t
    calc
      _ = (mellin Phi (t*I)*twist (p.1*p.2/T) t)*
          ∑ z ∈ rowIndices N d j l D H,
            amplitude d a F1 F2 FM W alpha beta p.1 p.2 z*twist z.1.1 t*twist z.1.2 t := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = _ := by rw [he]; ring
  · simp [localized,hp]

theorem row_mellin_blocks (N d j l K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H T M : ℝ) (js : List ℕ) (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T (fun n => (coefficient js n:ℂ))
      F1 F2 FM W Phi alpha beta (x,y)) =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l)).indicator (fun p =>
          (PRZZAStarWindow.window N T (M/2) (3*M)).indicator
            (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))) p *
          mellin Phi (t*I)*twist (p.1*p.2/T) t *
          ((allocations js).map (fun q => ∑ h ∈ hSupport N d,
            (sourceG q.1 0 0 d h:ℂ)*blocks N d h j l K q.2 js D H
              p.1 p.2 t F1 F2 FM alpha beta)).sum) p := by
  rw [row_iterated_eq N d j l D H T M _ F1 F2 FM W Phi alpha beta
    hT hM hFM hW hPhi.continuous hsM hsP]
  rw [row_mellin_window N d j l D H T M _ F1 F2 FM W Phi alpha beta
    hN hT hM hFM hW hPhi hsM hsP]
  simp_rw [row_localized,signedRow_blocks N d j l K hd hK]

#print axioms signedRow_blocks
#print axioms row_amplitude
#print axioms row_localized
#print axioms row_mellin_blocks
end XiPrime8845.PRZZRowMellinBranches

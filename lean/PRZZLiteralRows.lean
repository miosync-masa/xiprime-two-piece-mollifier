import PRZZRowMellinBranches

/-! Exact reassembly of the original A* from all dyadic row integrals.
Finite-sum interchange is justified by the actual kernel integrability. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set
namespace XiPrime8845.PRZZLiteralRows
open PRZZAStar PRZZOriginalRowWindow
set_option maxHeartbeats 3000000

theorem index_partition (N d : ℕ) (D H : ℝ) (f : Index → ℂ) :
    (∑ z ∈ indices N d D H, f z) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ z ∈ rowIndices N d j l D H, f z := by
  classical
  symm
  simp only [rowIndices,sum_filter]
  conv_lhs => enter [2,j]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro z hz
  have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  have hj : Nat.log 2 z.1.1 ∈ range (Nat.log 2 N+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hn.1).2))
  have hl : Nat.log 2 z.1.2 ∈ range (Nat.log 2 N+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Icc.mp hn.2).2))
  simp only [PRZZDyadic.cell,mem_filter,hn.1,hn.2,true_and]
  have he (j l : ℕ) :
      (if Nat.log 2 z.1.1 = j ∧ Nat.log 2 z.1.2 = l then f z else 0) =
      (if Nat.log 2 z.1.1 = j then (if Nat.log 2 z.1.2 = l then f z else 0) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp [hj,hl]

theorem literal_rows (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0)) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    literal N d D H T a F1 F2 FM W Phi alpha beta =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∫ x in Ioi (0:ℝ), ∫ y,
          rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y) := by
  have hi (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (fun p : ℝ × ℝ => kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2) := by
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact PRZZPositiveMellin.kernel_integrable_positive d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hFM hW hPhi hsM hsP
      (by positivity) (by positivity) hT
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hz0 (z : Index) (hz : z ∈ indices N d D H) (x : ℝ) (hx : x ∉ Ioi (0:ℝ)) :
      (∫ y, kernel d T a F1 F2 FM W Phi alpha beta z x y) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change kernel d T a F1 F2 FM W Phi alpha beta z x y = 0
    have hp : (x,y) ∉ PRZZAStarWindow.window N T (M/2) (3*M) := by
      intro hh
      exact hx ((div_pos (by positivity) (by exact_mod_cast hN)).trans_le hh.1.1)
    have he := congrFun (PRZZAStarWindow.indicator_kernel N d D H T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hsM hsP (by positivity) (by positivity) hT hz) (x,y)
    simpa only [Set.indicator_of_notMem hp] using he.symm
  rw [literal_eq_sum_integrals]
  have he : (∑ z ∈ indices N d D H, ∫ x in Ioi (0:ℝ), ∫ y,
      kernel d T a F1 F2 FM W Phi alpha beta z x y) =
      ∑ z ∈ indices N d D H, ∫ p : ℝ × ℝ,
        kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2 := by
    apply sum_congr rfl
    intro z hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hz0 z hz)]
    exact (integral_prod _ (hi z hz)).symm
  rw [he,index_partition]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro l hl
  rw [row_iterated_eq N d j l D H T M a F1 F2 FM W Phi alpha beta hT hM hFM hW hPhi hsM hsP]
  exact (integral_finsetSum _ (fun z hz => hi z (mem_filter.mp hz).1)).symm

#print axioms index_partition
#print axioms literal_rows

/-- The literal A* is the sum of its row-local Mellin/HB integrals.
Both indicators survive on every row, with no decomposition premise. -/
theorem literal_windowed_blocks (N d K : ℕ) (hd : 1 ≤ d) (hK : 0 < K)
    (D H T M : ℝ) (js : List ℕ) (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0)) (hPhi : ContDiff ℝ ∞ Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    literal N d D H T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      F1 F2 FM W Phi alpha beta =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
          (PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l)).indicator (fun p =>
            (PRZZAStarWindow.window N T (M/2) (3*M)).indicator
              (fun p => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))) p *
            mellin Phi (t*Complex.I)*PRZZMellinSeparation.twist (p.1*p.2/T) t *
            ((PRZZCoefficientSeparation.allocations js).map (fun q =>
              ∑ h ∈ PRZZSupportedSplit.hSupport N d,
                (PRZZGCoefficient.sourceG q.1 0 0 d h:ℂ)*
                  PRZZAllSignedSources.blocks N d h j l K q.2 js D H p.1 p.2 t
                    F1 F2 FM alpha beta)).sum) p := by
  rw [literal_rows N d D H T M _ F1 F2 FM W Phi alpha beta hN hT hM
    hFM hW hPhi.continuous hsM hsP]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro l hl
  exact PRZZRowMellinBranches.row_mellin_blocks N d j l K hd hK D H T M js
    F1 F2 FM W Phi alpha beta hN hT hM hFM hW hPhi hsM hsP

#print axioms literal_windowed_blocks
end XiPrime8845.PRZZLiteralRows

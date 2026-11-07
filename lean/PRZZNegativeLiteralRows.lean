import PRZZNegativeRowIntegral
import PRZZLiteralRows

/-! Exact reassembly of the actual negative literal from all original
modulated row integrals. The original reflected activity mask is retained
when empty rows are removed, before taking positive budget sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZNegativeLiteralRows
open PRZZAStar PRZZNegativeMellin PRZZNegativeArithmetic PRZZMellinSeparation
open PRZZNegativeRowWindow PRZZNegativeRowIntegral
open PRZZOriginalRowWindow (rowIndices)
set_option maxHeartbeats 8000000

theorem integral_rows (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0)) (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∑ z ∈ indices N d D H, ∫ x in Ioi (0:ℝ), ∫ y,
      modulation z x*kernel d T a F1 F2 FM W Phi alpha beta z x y) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∫ x in Ioi (0:ℝ), ∫ y,
          rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y) := by
  have hi (z : Index) (hz : z ∈ indices N d D H) :
      Integrable (fun p : ℝ × ℝ => modulation z p.1*kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2) := by
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    have hb := PRZZPositiveMellin.kernel_integrable_positive d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hFM hW hPhi hsM hsP
      (by positivity) (by positivity) hT
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
    have hm : Measurable (fun p : ℝ × ℝ => modulation z p.1) := by
      unfold modulation PRZZKloostermanInputs.e
      fun_prop
    apply (hb.mul_bdd hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (modulation_norm z p.1).le))).congr
    exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
  have hz0 (z : Index) (hz : z ∈ indices N d D H) (x : ℝ) (hx : x ∉ Ioi (0:ℝ)) :
      (∫ y, modulation z x*kernel d T a F1 F2 FM W Phi alpha beta z x y) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change modulation z x*kernel d T a F1 F2 FM W Phi alpha beta z x y = 0
    have hp : (x,y) ∉ PRZZAStarWindow.window N T (M/2) (3*M) := by
      intro hh
      exact hx ((div_pos (by positivity) (by exact_mod_cast hN)).trans_le hh.1.1)
    have he := congrFun (PRZZAStarWindow.indicator_kernel N d D H T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hsM hsP (by positivity) (by positivity) hT hz) (x,y)
    have hk : kernel d T a F1 F2 FM W Phi alpha beta z x y = 0 := by
      simpa only [Set.indicator_of_notMem hp] using he.symm
    simp only [hk,mul_zero]
  have he : (∑ z ∈ indices N d D H, ∫ x in Ioi (0:ℝ), ∫ y,
      modulation z x*kernel d T a F1 F2 FM W Phi alpha beta z x y) =
      ∑ z ∈ indices N d D H, ∫ p : ℝ × ℝ,
        modulation z p.1*kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2 := by
    apply sum_congr rfl
    intro z hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hz0 z hz)]
    exact (integral_prod _ (hi z hz)).symm
  rw [he,PRZZLiteralRows.index_partition]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro l hl
  rw [row_iterated_eq N d j l D H T M a F1 F2 FM W Phi alpha beta hT hM hFM hW hPhi hsM hsP]
  exact (integral_finsetSum _ (fun z hz => hi z (mem_filter.mp hz).1)).symm


theorem literal_rows (N d : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M) (hsigma : sigma ≠ 0)
    (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    PRZZSignedCentral.signedLiteral (-1) N d D H T M a F1 F2 F Phi alpha beta sigma =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 (scaledCutoff F M)
          (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta (x,y) := by
  rw [literal_original N d D H T M a F1 F2 F Phi alpha beta sigma hM]
  exact integral_rows N d D H T M a F1 F2 (scaledCutoff F M)
    (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta hN hT hM
    (hF.comp (continuous_const.mul continuous_id))
    (PRZZSourceWOuter.sourceW_continuous sigma hsigma) hPhi
    (PRZZWindowScaleSupply.scaled_support F M hM hsF) hsP

theorem inactive_integral (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (ha : ¬ PRZZActiveRows.Active N d j l D H a F1 F2 (reflect FM) alpha beta) :
    (∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)) = 0 := by
  have hz : ∀ x y t, PRZZRowMellinBranches.signedRow N d j l D H a F1 F2 (reflect FM) alpha beta x y t = 0 := by
    simpa only [PRZZActiveRows.Active,not_exists,not_not] using ha
  have h := row_integral_bound N d j l D H T M 0 a F1 F2 FM W Phi alpha beta
    hN hd hT hM hFM hW hPhi hsM hsP le_rfl (by intros; simp [PRZZNegativeLocalRows.row,hz])
  simpa using h


#print axioms integral_rows
#print axioms literal_rows
#print axioms inactive_integral
end XiPrime8845.PRZZNegativeLiteralRows


import PRZZOriginalRowWindow
import PRZZNegativeMellin
import PRZZNegativeLocalRows

/-! Row-local Mellin transfer for the actual negative unit modulation.
The original strict indices, dyadic support and both integration variables
are retained. Joint integrability is proved, not supplied as a premise. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZNegativeRowWindow
open PRZZAStar PRZZDyadicWindow PRZZNegativeMellin
open PRZZOriginalRowWindow (rowIndices)
set_option maxHeartbeats 6000000

def rowKernel (N d j l : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ z ∈ rowIndices N d j l D H,
    modulation z p.1*kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2

theorem row_indicator (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hT : 0 < T) (hM : 0 < M)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (box T M ((2:ℝ)^j) ((2:ℝ)^l)).indicator
      (rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta) =
      rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta := by
  apply Set.indicator_eq_self.mpr
  intro p hp
  by_contra hn
  apply hp
  apply sum_eq_zero
  intro z hz
  have h := (mem_filter.mp hz).2
  have h1 := (PRZZDyadic.mem_cell N j z.1.1).mp h.1
  have h2 := (PRZZDyadic.mem_cell N l z.1.2).mp h.2
  have hb1 : (z.1.1:ℝ) ∈ Icc ((2:ℝ)^j) (2*(2:ℝ)^j) := by
    constructor
    · exact_mod_cast h1.2.1
    · have hh : (z.1.1:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast h1.2.2
      rw [pow_succ] at hh
      linarith
  have hb2 : (z.1.2:ℝ) ∈ Icc ((2:ℝ)^l) (2*(2:ℝ)^l) := by
    constructor
    · exact_mod_cast h2.2.1
    · have hh : (z.1.2:ℝ) < (2:ℝ)^(l+1) := by exact_mod_cast h2.2.2
      rw [pow_succ] at hh
      linarith
  have hk : kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2 = 0 := by
    by_contra hk
    exact hn (support_box d T M _ _ a F1 F2 FM W Phi alpha beta z
    hT hM (by positivity) (by positivity) hb1 hb2 hsM hsP hk)
  rw [hk,mul_zero]


theorem row_mellin_window (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ p, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta p) =
      (1/(2*Real.pi):ℂ)*∫ t : ℝ, ∫ p : ℝ × ℝ,
        (box T M ((2:ℝ)^j) ((2:ℝ)^l)).indicator (fun p =>
          ∑ z ∈ rowIndices N d j l D H,
            PRZZNegativeMellin.localizedMinus N d T (M/2) (3*M)
              a F1 F2 FM W Phi alpha beta z p t) p := by
  let f := fun p t => ∑ z ∈ rowIndices N d j l D H,
    PRZZNegativeMellin.localizedMinus N d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z p t
  let s := box T M ((2:ℝ)^j) ((2:ℝ)^l)
  have his (z : Index) (hz : z ∈ rowIndices N d j l D H) :
      Integrable (Function.uncurry (PRZZNegativeMellin.localizedMinus N d T (M/2) (3*M)
        a F1 F2 FM W Phi alpha beta z)) := by
    have hz' := (mem_filter.mp hz).1
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz').1).1
    exact PRZZNegativeMellin.localized_integrable N d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hFM hW hPhi hsP hN hT (by positivity) (by positivity)
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hi : Integrable (Function.uncurry f) := integrable_finsetSum _ his
  have hm : MeasurableSet s := (isCompact_Icc.prod isCompact_Icc).measurableSet
  have hj : Integrable (Function.uncurry (fun p t => s.indicator (fun p => f p t) p)) := by
    apply (hi.indicator (hm.preimage measurable_fst)).congr
    apply Filter.Eventually.of_forall
    intro q
    by_cases hp : q.1 ∈ s <;> simp [Function.uncurry,Set.indicator,hp]
  change _ = (1/(2*Real.pi):ℂ)*∫ t, ∫ p, s.indicator (fun p => f p t) p
  rw [← integral_integral_swap hj,← integral_const_mul]
  apply integral_congr_ae
  have hall : ∀ᵐ p, ∀ z ∈ rowIndices N d j l D H,
      Integrable (fun t => PRZZNegativeMellin.localizedMinus N d T (M/2) (3*M)
        a F1 F2 FM W Phi alpha beta z p t) :=
    (Filter.eventually_all_finset _).mpr (fun z hz => (his z hz).prod_right_ae)
  filter_upwards [hall] with p hip
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp]
    dsimp only [f,rowKernel]
    rw [integral_finsetSum _ hip,mul_sum]
    apply sum_congr rfl
    intro z hz
    have he := PRZZAStarTransform.kernel_inversion N d D H T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hPhi hsP hsM hN hT
      (by positivity) (by positivity) (mem_filter.mp hz).1 p
    rw [he]
    simp only [PRZZNegativeMellin.localizedMinus,integral_const_mul]
    ring
  · simp only [Set.indicator_of_notMem hp,integral_zero,mul_zero]
    have he := congrFun (row_indicator N d j l D H T M a F1 F2 FM W Phi
      alpha beta hT hM hsM hsP) p
    have hp' : p ∉ box T M ((2:ℝ)^j) ((2:ℝ)^l) := hp
    simpa only [Set.indicator_of_notMem hp'] using he.symm


theorem row_iterated_eq (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : Continuous Phi)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)) =
      ∫ p, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta p := by
  have hi : Integrable (rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta) := by
    apply integrable_finsetSum
    intro z hz
    have hz' := (mem_filter.mp hz).1
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz').1).1
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
  have hz (x : ℝ) (hx : x ∉ Ioi (0:ℝ)) :
      (∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y) = 0
    have hp : (x,y) ∉ box T M ((2:ℝ)^j) ((2:ℝ)^l) := by
      intro hh
      exact hx ((by positivity : 0 < M/(4*(2:ℝ)^l)).trans_le hh.1.1)
    have he := congrFun (row_indicator N d j l D H T M a F1 F2 FM W Phi alpha beta
      hT hM hsM hsP) (x,y)
    simpa only [Set.indicator_of_notMem hp] using he.symm
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact (integral_prod _ hi).symm


#print axioms row_indicator
#print axioms row_mellin_window
#print axioms row_iterated_eq
end XiPrime8845.PRZZNegativeRowWindow


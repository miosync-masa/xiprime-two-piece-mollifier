import PRZZDyadicWindow
import PRZZDyadic
import PRZZPositiveMellin

/-! Local windows for rows of the original finite A* index set, before
Mellin inversion. Strict frequency, coprimality and product cutoffs stay
inside indices. No positivity or absolute-value replacement is used. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set
namespace XiPrime8845.PRZZOriginalRowWindow
open PRZZAStar PRZZDyadicWindow
set_option maxHeartbeats 2000000

def rowIndices (N d j l : ℕ) (D H : ℝ) : Finset Index :=
  (indices N d D H).filter (fun z => z.1.1 ∈ PRZZDyadic.cell N j ∧ z.1.2 ∈ PRZZDyadic.cell N l)

def rowKernel (N d j l : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ z ∈ rowIndices N d j l D H, kernel d T a F1 F2 FM W Phi alpha beta z p.1 p.2

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
  by_contra hk
  exact hn (support_box d T M _ _ a F1 F2 FM W Phi alpha beta z
    hT hM (by positivity) (by positivity) hb1 hb2 hsM hsP hk)

/-- Equality for the original row's iterated integral. No exchange of
integrals or integrability premise is hidden in this support identity. -/
theorem row_integral_window (N d j l : ℕ) (D H T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hT : 0 < T) (hM : 0 < M)
    (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)) =
      ∫ x in Ioi (0:ℝ), ∫ y, (box T M ((2:ℝ)^j) ((2:ℝ)^l)).indicator
        (rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta) (x,y) := by
  rw [row_indicator N d j l D H T M a F1 F2 FM W Phi alpha beta hT hM hsM hsP]

#print axioms row_indicator
#print axioms row_integral_window

/-- Rowwise Mellin inversion and Fubini with the original dyadic window
retained. Continuity of W is needed only on positive arguments. -/
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
            PRZZActualMellin.localized N d T (M/2) (3*M)
              a F1 F2 FM W Phi alpha beta z p t) p := by
  let f := fun p t => ∑ z ∈ rowIndices N d j l D H,
    PRZZActualMellin.localized N d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z p t
  let s := box T M ((2:ℝ)^j) ((2:ℝ)^l)
  have his (z : Index) (hz : z ∈ rowIndices N d j l D H) :
      Integrable (Function.uncurry (PRZZActualMellin.localized N d T (M/2) (3*M)
        a F1 F2 FM W Phi alpha beta z)) := by
    have hz' := (mem_filter.mp hz).1
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz').1).1
    exact PRZZPositiveMellin.localized_integrable_positive N d T (M/2) (3*M)
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
      Integrable (fun t => PRZZActualMellin.localized N d T (M/2) (3*M)
        a F1 F2 FM W Phi alpha beta z p t) :=
    (Filter.eventually_all_finset _).mpr (fun z hz => (his z hz).prod_right_ae)
  filter_upwards [hall] with p hip
  by_cases hp : p ∈ s
  · simp only [Set.indicator_of_mem hp]
    dsimp only [f,rowKernel]
    rw [integral_finsetSum _ hip,mul_sum]
    apply sum_congr rfl
    intro z hz
    exact PRZZAStarTransform.kernel_inversion N d D H T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hPhi hsP hsM hN hT
      (by positivity) (by positivity) (mem_filter.mp hz).1 p
  · simp only [Set.indicator_of_notMem hp,integral_zero,mul_zero]
    have he := congrFun (row_indicator N d j l D H T M a F1 F2 FM W Phi
      alpha beta hT hM hsM hsP) p
    have hp' : p ∉ box T M ((2:ℝ)^j) ((2:ℝ)^l) := hp
    simpa only [Set.indicator_of_notMem hp'] using he.symm

#print axioms row_mellin_window

/-- The original positive-x iterated row integral equals its product
integral; integrability is supplied for every original summand. -/
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
    exact PRZZPositiveMellin.kernel_integrable_positive d T (M/2) (3*M)
      a F1 F2 FM W Phi alpha beta z hFM hW hPhi hsM hsP
      (by positivity) (by positivity) hT
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
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

#print axioms row_iterated_eq
end XiPrime8845.PRZZOriginalRowWindow

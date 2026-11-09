import PRZZClassRows
import PRZZActiveRows

/-! Exact mixed arithmetic slots in the original literal geometry. The floor
weights are used only at finite arithmetic sample points, never differentiated.
All analytic estimates use the original smooth cutoffs and mixed row supplier. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZMixedLiteral
open PRZZMellinSeparation PRZZOriginalRowWindow
set_option maxHeartbeats 8000000

def leftFold (a : ℕ → ℂ) (F : ℝ → ℂ) (x : ℝ) : ℂ := a ⌊x⌋₊*F x
def rightFold (b : ℕ → ℂ) (F : ℝ → ℂ) (x : ℝ) : ℂ := star (b ⌊x⌋₊)*F x

theorem left_support (a : ℕ → ℂ) (F : ℝ → ℂ) :
    Function.support (leftFold a F) ⊆ Function.support F := by
  intro x hx
  change a ⌊x⌋₊*F x ≠ 0 at hx
  change F x ≠ 0
  intro hz
  exact hx (by rw [hz,mul_zero])

theorem right_support (b : ℕ → ℂ) (F : ℝ → ℂ) :
    Function.support (rightFold b F) ⊆ Function.support F := by
  intro x hx
  change star (b ⌊x⌋₊)*F x ≠ 0 at hx
  change F x ≠ 0
  intro hz
  exact hx (by rw [hz,mul_zero])

theorem signedRow_fold (N d j l : ℕ) (D H : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    PRZZRowMellinBranches.signedRow N d j l D H (fun _ => 1)
      (leftFold a F1) (rightFold b F2) FM alpha beta x y t =
    PRZZFiniteFamilyRows.signedRow N d j l D H a b F1 F2 FM alpha beta x y t := by
  unfold PRZZRowMellinBranches.signedRow PRZZFiniteFamilyRows.signedRow
  apply sum_congr rfl
  intro v hv
  congr 1
  unfold PRZZAStarRectangles.rectangle PRZZHBRectangles.mixed
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  split_ifs <;> simp [PRZZAStarNu.pairCoeff,leftFold,rightFold,← Nat.cast_mul,mul_assoc]

/-- The literal finite mixed sum, with both coefficient slots visible. -/
def literal (N d : ℕ) (D H T : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D H,
    (a (d*z.1.1)*star (b (d*z.1.2)))*
      PRZZAStar.prefactor (fun _ => 1) F1 F2 d alpha beta z *
      ∫ x in Ioi (0:ℝ), PRZZAStar.outerKernel FM alpha beta z x *
        ∫ y, PRZZAStar.innerKernel W Phi T z x y

theorem literal_fold (N d : ℕ) (D H T : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ) :
    literal N d D H T a b F1 F2 FM W Phi alpha beta =
      PRZZAStar.literal N d D H T (fun _ => 1)
        (leftFold a F1) (rightFold b F2) FM W Phi alpha beta := by
  unfold literal PRZZAStar.literal
  apply sum_congr rfl
  intro z hz
  simp only [PRZZAStar.prefactor,leftFold,rightFold,← Nat.cast_mul,Nat.floor_natCast,
    star_one,one_mul]
  ring

/-- Genuine original spatial integral, with its common mass and Mellin cost. -/
theorem row_integral_bound (N d j l : ℕ) (D H T M B : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) (hB : 0 ≤ B)
    (hb : ∀ p ∈ PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l), ∀ t : ℝ,
      ‖PRZZFiniteFamilyRows.signedRow N d j l D H a b F1 F2 FM alpha beta p.1 p.2 t‖ ≤ B*(1+|t|)) :
    ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T (fun _ => 1)
      (leftFold a F1) (rightFold b F2) FM W Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        W (alpha+beta) p‖)*B*(∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  apply PRZZRowIntegralBudget.row_integral_bound N d j l D H T M B (fun _ => 1)
    (leftFold a F1) (rightFold b F2) FM W Phi alpha beta hN hd hT hM hFM hW hPhi hsM hsP hB
  intro p hp t
  rw [signedRow_fold]
  exact hb p hp t

#print axioms left_support
#print axioms right_support
#print axioms signedRow_fold
#print axioms literal_fold
#print axioms row_integral_bound
end XiPrime8845.PRZZMixedLiteral

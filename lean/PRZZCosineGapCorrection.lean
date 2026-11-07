import PRZZReflectedContour

/-! The absolutely summed evaluated cosine kernel is now on the same
contour as the opposite diagonal correction. No equality with the actual
uncut zero Fourier field is assumed or asserted. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineGapCorrection
open PRZZReflectedEnvelope PRZZCosineMellinCore
set_option maxHeartbeats 5000000

theorem kernel_correction (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (1/(2*Real.pi):ℂ)*(∫ v : ℝ, kernel sigma X (((5/4:ℝ):ℂ)+(v:ℂ)*I)) =
      PRZZDiagonalMellin.diagonal (-sigma) X-riemannZeta (1-sigma) := by
  rw [PRZZReflectedContour.integral_shift sigma hs hn X hX]
  have hneg := MeasureTheory.Measure.integral_comp_mul_left
    (fun v : ℝ => PRZZDiagonalMellin.integrand (-sigma) X
      (((-(1/8):ℝ):ℂ)+(v:ℂ)*I)) (-1)
  have he : (∫ v : ℝ, kernel sigma X (((1/8:ℝ):ℂ)+(v:ℂ)*I)) =
      ∫ v : ℝ, PRZZDiagonalMellin.integrand (-sigma) X (((-(1/8):ℝ):ℂ)+(v:ℂ)*I) := by
    simpa only [kernel,neg_add,neg_mul,Complex.ofReal_neg,neg_one_mul,
      one_mul,inv_neg,inv_one,abs_neg,abs_one,one_smul] using hneg
  rw [he]
  have hh := PRZZDiagonalContour.shifted_identity (-sigma) (neg_ne_zero.mpr hs)
    (by simpa using hn) X hX
  simpa only [sub_eq_add_neg,Complex.ofReal_neg] using hh.symm

theorem evaluated_gap_correction (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
      (2*∑' n : ℕ, ∫ tau : ℝ, PRZZCosineGapMellin.term sigma (2*Real.pi*t/P) n tau) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        (PRZZDiagonalMellin.diagonal (-sigma) (t/(2*Real.pi*P))-riemannZeta (1-sigma)) := by
  rw [PRZZCosineGapMellin.reflected_gap_integral sigma hs hn P t hP ht]
  have hh := kernel_correction sigma hs hn (t/(2*Real.pi*P)) (by positivity)
  change (1/(2*Real.pi):ℂ)*(∫ tau : ℝ,
    PRZZDiagonalMellin.integrand (-sigma) (t/(2*Real.pi*P)) (-line tau)) = _ at hh
  rw [mul_assoc,hh]

/-- Algebraic balance with the actual opposite diagonal W series.
Using this for the original zero mode still requires the actual
improper-transform theorem, including its integration-by-parts sign. -/
theorem evaluated_diagonal_balance (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*PRZZDiagonalMellin.diagonal (-sigma) (t/(2*Real.pi*P))-
      (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        (2*∑' n : ℕ, ∫ tau : ℝ, PRZZCosineGapMellin.term sigma (2*Real.pi*t/P) n tau) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*riemannZeta (1-sigma) := by
  rw [evaluated_gap_correction sigma hs hn P t hP ht]
  ring

#print axioms kernel_correction
#print axioms evaluated_gap_correction
#print axioms evaluated_diagonal_balance
end XiPrime8845.PRZZCosineGapCorrection

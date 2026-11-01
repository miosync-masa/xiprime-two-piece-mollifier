import PRZZAStarIntegrability
import PRZZSmoothMellin

/-! Mellin separation of the literal A* finite integrand, on Re(w)=0.
The original arithmetic, phases and frequency cutoffs are retained. This
does not exchange the Mellin integral with the outer x,y integrals or
identify the resulting arithmetic sum with the rectangular DI block. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Complex
namespace XiPrime8845.PRZZAStarMellin
open PRZZAStar PRZZKloostermanInputs PRZZMellinSeparation
set_option maxHeartbeats 2000000

def amplitude (d : ℕ) (a : ℕ → ℂ) (F1 F2 FM W : ℝ → ℂ)
    (α β : ℂ) (x y : ℝ) (z : Index) : ℂ :=
  prefactor a F1 F2 d α β z*outerKernel FM α β z x*
    e ((z.2.1:ℝ)*y/(2*Real.pi))*W (2*Real.pi*x/y)

theorem kernel_amplitude (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index) (x y : ℝ) :
    kernel d T a F1 F2 FM W Phi α β z x y =
      amplitude d a F1 F2 FM W α β x y z*Phi ((x*y/T)*z.1.1*z.1.2) := by
  unfold kernel innerKernel amplitude
  rw [show x*y*(z.1.1:ℝ)*z.1.2/T = (x*y/T)*z.1.1*z.1.2 by ring]
  ring

/-- Smooth compact support supplies both Mellin convergence and vertical
L1 decay. No Mellin equality or convergence is assumed as a new input. -/
theorem finite_integrand_mellin (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (x y : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hPhi : ContDiff ℝ ∞ Phi) (hs : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) :
    (∑ z ∈ indices N d D H, kernel d T a F1 F2 FM W Phi α β z x y) =
      (1/(2*Real.pi):ℂ)*(∫ t : ℝ, mellin Phi (t*I)*twist (x*y/T) t*
        ∑ z ∈ indices N d D H,
          amplitude d a F1 F2 FM W α β x y z*twist z.1.1 t*twist z.1.2 t) := by
  simp_rw [kernel_amplitude]
  apply sum_separate (indices N d D H) _ _ _ (x*y/T) (by positivity)
  · intro z hz
    have hn := Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact_mod_cast (Finset.mem_Icc.mp hn.1).1
  · intro z hz
    have hn := Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
    exact_mod_cast (Finset.mem_Icc.mp hn.2).1
  · exact PRZZSmoothMellin.mellin_convergent Phi 1 2 (by norm_num) hs hPhi.continuous
  · exact PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hs hPhi
  · intros; exact hPhi.continuous.continuousAt

#print axioms kernel_amplitude
#print axioms finite_integrand_mellin
end XiPrime8845.PRZZAStarMellin

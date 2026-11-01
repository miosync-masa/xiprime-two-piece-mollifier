import PRZZAStar

/-! Actual height-cutoff support supplies the inner y integrability.
The singular-looking W(2*pi*x/y) is only used on a compact positive
interval. Outer x integrability and Mellin interchange remain separate. -/
noncomputable section
open MeasureTheory Set
namespace XiPrime8845.PRZZAStarIntegrability
open PRZZAStar PRZZKloostermanInputs
set_option maxHeartbeats 2000000

theorem inner_integrable (W Phi : ℝ → ℂ) (T : ℝ) (z : Index) (x : ℝ)
    (hW : Continuous W) (hPhi : Continuous Phi)
    (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hx : 0 < x) (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (innerKernel W Phi T z x) := by
  let c : ℝ := x*z.1.1*z.1.2/T
  have hc : 0 < c := by dsimp [c]; positivity
  have he (y : ℝ) : x*y*z.1.1*z.1.2/T = c*y := by dsimp [c]; ring
  have hsupport : Function.support (innerKernel W Phi T z x) ⊆ Icc (1/c) (2/c) := by
    intro y hy
    have hp : Phi (x*y*z.1.1*z.1.2/T) ≠ 0 := by
      intro hz
      exact hy (by simp [innerKernel,hz])
    have hh := hs hp
    rw [he y] at hh
    exact ⟨(div_le_iff₀ hc).mpr (by nlinarith [hh.1]),
      (le_div_iff₀ hc).mpr (by nlinarith [hh.2])⟩
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hne : ∀ y ∈ Icc (1/c) (2/c), y ≠ 0 := by
    intro y hy
    exact ne_of_gt ((one_div_pos.mpr hc).trans_le hy.1)
  unfold innerKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · unfold e; fun_prop
    · exact hW.comp_continuousOn (continuousOn_const.div continuousOn_id hne)
  · fun_prop

/-- The prefactors of the literal source kernel do not change y
integrability. This supplies the inner hypothesis at every positive x. -/
theorem kernel_integrable_y (d : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (z : Index) (x : ℝ)
    (hW : Continuous W) (hPhi : Continuous Phi)
    (hs : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hx : 0 < x) (hn1 : 0 < z.1.1) (hn2 : 0 < z.1.2) :
    Integrable (kernel d T a F1 F2 FM W Phi α β z x) :=
  (inner_integrable W Phi T z x hW hPhi hs hT hx hn1 hn2).const_mul _

#print axioms inner_integrable
#print axioms kernel_integrable_y

/-- The inner integrability premise is now supplied by the actual cutoff.
Only the outer x integrability remains an explicit obligation here. -/
theorem literal_eq_integral_sum_of_cutoff (N d : ℕ) (D H T : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hW : Continuous W) (hPhi : Continuous Phi)
    (hs : Function.support Phi ⊆ Icc (1:ℝ) 2) (hT : 0 < T)
    (hx : ∀ z ∈ indices N d D H, IntegrableOn
      (fun x => ∫ y, kernel d T a F1 F2 FM W Phi α β z x y) (Ioi (0:ℝ))) :
    literal N d D H T a F1 F2 FM W Phi α β =
      ∫ x in Ioi (0:ℝ), ∫ y, ∑ z ∈ indices N d D H,
        kernel d T a F1 F2 FM W Phi α β z x y := by
  apply literal_eq_integral_sum N d D H T a F1 F2 FM W Phi α β _ hx
  intro x hx' z hz
  have hn := Finset.mem_product.mp
    (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1
  exact kernel_integrable_y d T a F1 F2 FM W Phi α β z x hW hPhi hs hT hx'
    (by have := (Finset.mem_Icc.mp hn.1).1; omega)
    (by have := (Finset.mem_Icc.mp hn.2).1; omega)

#print axioms literal_eq_integral_sum_of_cutoff
end XiPrime8845.PRZZAStarIntegrability

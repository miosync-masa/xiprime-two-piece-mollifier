import PRZZAStarMellin

/-! A fixed positive window supplies a W envelope. The constant may depend
on the window and on W: no uniform-in-T source estimate is asserted.
The window must be retained when using this envelope after Mellin inversion. -/
noncomputable section
open Set MeasureTheory
namespace XiPrime8845.PRZZWindowWeight

theorem window_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b c d : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      ‖W (2*Real.pi*x/y)‖ ≤ C := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => W (2*Real.pi*p.1/p.2))
      (Icc a b ×ˢ Icc c d) := by
    apply hW.comp_continuousOn
    exact (continuousOn_const.mul continuous_fst.continuousOn).div
      continuous_snd.continuousOn (fun p hp => (hc.trans_le hp.2.1).ne')
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx y hy
  exact (hC (x,y) ⟨hx,hy⟩).trans (le_max_left _ _)

/-- Multiplying by the unit Mellin twists does not change the W budget. -/
theorem twisted_window_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b c d : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      ∀ q : ℝ, 0 < q → ∀ t : ℝ,
      ‖W (2*Real.pi*x/y)*PRZZMellinSeparation.twist q t‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := window_bound W hW a b c d hc
  refine ⟨C,hC,?_⟩
  intro x hx y hy q hq t
  rw [norm_mul,PRZZMellinSeparation.twist_norm q t hq,mul_one]
  exact h x hx y hy

#print axioms window_bound
#print axioms twisted_window_bound
end XiPrime8845.PRZZWindowWeight

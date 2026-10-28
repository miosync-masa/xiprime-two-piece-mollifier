import Mathlib

/-! Compact parameter integrals with a complex analytic core and a real weight.
This file has no arithmetic or zero-counting assumptions. -/
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory

namespace XiPrime8845.CompactShiftIntegral

abbrev Shift := ℂ × ℂ

def partialMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : Shift × ℂ → E) (z : Shift × ℂ) : Shift →L[ℂ] E :=
  (fderiv ℂ F z).comp (ContinuousLinearMap.inl ℂ Shift ℂ)

theorem partialMap_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Shift × ℂ → E} {U : Set Shift} {V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F (U ×ˢ V)) :
    ContDiffOn ℂ ∞ (partialMap F) (U ×ˢ V) := by
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen (hU.prod hV)).mp hF
  exact hd.2.clm_comp contDiffOn_const

theorem compact_integral_hasFDerivAt {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (F : Shift × ℂ → E) (c : ℝ → ℂ) (a b : ℝ) (U : Set Shift) (V : Set ℂ)
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F (U ×ˢ V))
    (hc : ContinuousOn c (Icc a b)) (hseg : ∀ t ∈ Icc a b, (t : ℂ) ∈ V)
    (p : Shift) (hp : p ∈ U) :
    HasFDerivAt (fun z => ∫ t in Icc a b, c t • F (z, (t : ℂ)))
      (∫ t in Icc a b, c t • partialMap F (p, (t : ℂ))) p := by
  have hD := (partialMap_smooth hU hV hF).continuousOn
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  have core_cont : ∀ z ∈ U, ContinuousOn (fun t : ℝ => F (z, (t : ℂ))) (Icc a b) := by
    intro z hz
    exact hF.continuousOn.comp (by fun_prop) (fun t ht => ⟨hz, hseg t ht⟩)
  have der_cont : ∀ z ∈ U, ContinuousOn (fun t : ℝ => partialMap F (z, (t : ℂ))) (Icc a b) := by
    intro z hz
    exact hD.comp (by fun_prop) (fun t ht => ⟨hz, hseg t ht⟩)
  have joint : ContinuousOn (fun q : Shift × ℝ => c q.2 • partialMap F (q.1, (q.2 : ℂ)))
      (Metric.closedBall p r ×ˢ Icc a b) := by
    apply (hc.comp continuousOn_snd (fun q hq => hq.2)).smul
    exact hD.comp (by fun_prop) (fun q hq => ⟨hrU hq.1, hseg q.2 hq.2⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p r).prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn joint
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall p r) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds p hr)
  · filter_upwards [hU.mem_nhds hp] with z hz
    exact (hc.smul (core_cont z hz)).aestronglyMeasurable measurableSet_Icc
  · exact (hc.smul (core_cont p hp)).integrableOn_compact isCompact_Icc
  · exact (hc.smul (der_cont p hp)).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro z hz
    exact hC (z,t) ⟨hz,ht⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro z hz
    have hd := ((hF (z, (t : ℂ)) ⟨hrU hz, hseg t ht⟩).contDiffAt
      ((hU.prod hV).mem_nhds ⟨hrU hz, hseg t ht⟩)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (t : ℂ) z))).const_smul (c t)

/-- All complex parameter derivatives exist, even though the weight is only continuous. -/
theorem compact_integral_smooth_nat (n : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (F : Shift × ℂ → E) (c : ℝ → ℂ) (a b : ℝ) (U : Set Shift) (V : Set ℂ)
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F (U ×ˢ V))
    (hc : ContinuousOn c (Icc a b)) (hseg : ∀ t ∈ Icc a b, (t : ℂ) ∈ V) :
    ContDiffOn ℂ n (fun z => ∫ t in Icc a b, c t • F (z, (t : ℂ))) U := by
  have hd := compact_integral_hasFDerivAt F c a b U V hU hV hF hc hseg
  induction n generalizing E with
  | zero =>
    simp only [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [show (↑(n+1) : WithTop ℕ∞) = ↑n + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hi := ih (partialMap F) (partialMap_smooth hU hV hF)
      (compact_integral_hasFDerivAt _ c a b U V hU hV (partialMap_smooth hU hV hF) hc hseg)
    apply hi.congr
    intro p hp
    exact (hd p hp).fderiv

theorem compact_integral_smooth {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (F : Shift × ℂ → E) (c : ℝ → ℂ) (a b : ℝ) (U : Set Shift) (V : Set ℂ)
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F (U ×ˢ V))
    (hc : ContinuousOn c (Icc a b)) (hseg : ∀ t ∈ Icc a b, (t : ℂ) ∈ V) :
    ContDiffOn ℂ ∞ (fun z => ∫ t in Icc a b, c t • F (z, (t : ℂ))) U := by
  rw [contDiffOn_infty]
  exact fun n => compact_integral_smooth_nat n F c a b U V hU hV hF hc hseg

def rightIterated (n : ℕ) (f : Shift → ℂ) (p : Shift) : ℂ :=
  iteratedDeriv n (fun y => f (p.1,y)) p.2

/-- Taking right-coordinate derivatives retains joint smoothness on the open domain. -/
theorem rightIterated_smooth (n : ℕ) (f : Shift → ℂ) (U : Set Shift)
    (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) :
    ContDiffOn ℂ ∞ (rightIterated n f) U := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hd := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp ih
    have hs := hd.2.clm_apply (contDiffOn_const (c := ((0,1) : Shift)))
    apply hs.congr
    intro p hp
    have hdiff := ((ih p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    have h := hdiff.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    simpa only [rightIterated, iteratedDeriv_succ, Function.comp_def, id_eq] using h.deriv

#print axioms rightIterated_smooth
#print axioms compact_integral_hasFDerivAt
#print axioms compact_integral_smooth

end XiPrime8845.CompactShiftIntegral

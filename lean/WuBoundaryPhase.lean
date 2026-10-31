import WuAuxiliaryHorizontal
import WuRightLittlewood

/-! Compatible edge phases in Littlewood's boundary expression.
Only variations from the common right anchors are estimated. The right
vertical phase is retained explicitly, rather than bounding arbitrary
branches of argument by a horizontal O(log T) estimate. -/
noncomputable section
open scoped BigOperators
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuBoundaryPhase
open WuLittlewood WuAuxiliaryBoundary
set_option maxHeartbeats 2000000

theorem edge_increment {f : ℂ → ℂ} {z d : ℂ} {a b : ℝ}
    (q : EdgeLog f z d a b) (hab : a ≤ b) (x y : ℝ)
    (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    (∫ t in x..y, d*logDeriv f (z+t*d)) = q.value y-q.value x := by
  have hsub : Icc x y ⊆ uIcc a b := by
    rw [uIcc_of_le hab]
    exact fun t ht => ⟨hx.trans ht.1,ht.2.trans hy⟩
  apply integral_eq_sub_of_hasDerivAt_of_le hxy (q.continuous.mono hsub)
    (fun t ht => q.derivative t (by
      simp only [min_eq_left hab,max_eq_right hab,mem_Ioo]
      exact ⟨hx.trans_lt ht.1,ht.2.trans_le hy⟩))
  exact q.integrable.mono_set (by simpa only [uIcc_of_le hxy] using hsub)

theorem boundary_horizontal_error (f : ℂ → ℂ) (a b u v K : ℝ)
    (q : BoundaryLogs f a b u v) (hab : a ≤ b)
    (hb : ∀ x ∈ Icc a b, |(∫ σ in x..b, logDeriv f (point σ u)).im| ≤ K)
    (ht : ∀ x ∈ Icc a b, |(∫ σ in x..b, logDeriv f (point σ v)).im| ≤ K) :
    |((∫ x in a..b, (q.top.value x).im)-(∫ x in a..b, (q.bottom.value x).im))-
      (b-a)*((q.right.value v).im-(q.right.value u).im)| ≤ 2*(b-a)*K := by
  let F := fun x => ((q.top.value x).im-(q.top.value b).im)-
    ((q.bottom.value x).im-(q.bottom.value b).im)
  have hi : ContinuousOn F (uIcc a b) :=
    ((Complex.continuous_im.comp_continuousOn q.top.continuous).sub continuousOn_const).sub
      ((Complex.continuous_im.comp_continuousOn q.bottom.continuous).sub continuousOn_const)
  have hf : ∀ x ∈ uIoc a b, ‖F x‖ ≤ 2*K := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le,hx.2⟩
    have he (e : EdgeLog f (u*I) 1 a b) := edge_increment e hab x b hx.1.le hx.2 le_rfl
    have htop := edge_increment q.top hab x b hx.1.le hx.2 le_rfl
    have hbot := edge_increment q.bottom hab x b hx.1.le hx.2 le_rfl
    simp only [one_mul,mul_one,add_comm (↑v*I),add_comm (↑u*I)] at htop hbot
    have ht' := ht x hx'
    have hb' := hb x hx'
    change |(∫ σ in x..b, logDeriv f ((σ:ℂ)+v*I)).im| ≤ K at ht'
    change |(∫ σ in x..b, logDeriv f ((σ:ℂ)+u*I)).im| ≤ K at hb'
    rw [htop,sub_im,abs_sub_comm] at ht'
    rw [hbot,sub_im,abs_sub_comm] at hb'
    exact (abs_sub _ _).trans (by simpa [two_mul] using add_le_add ht' hb')
  have he : (∫ x in a..b, F x) =
      ((∫ x in a..b, (q.top.value x).im)-(∫ x in a..b, (q.bottom.value x).im))-
        (b-a)*((q.right.value v).im-(q.right.value u).im) := by
    have htI := (Complex.continuous_im.comp_continuousOn q.top.continuous).intervalIntegrable (μ := volume)
    have hbI := (Complex.continuous_im.comp_continuousOn q.bottom.continuous).intervalIntegrable (μ := volume)
    dsimp only [Function.comp_def] at htI hbI
    dsimp only [F]
    rw [integral_sub (htI.sub (intervalIntegrable_const (c := (q.top.value b).im)))
      (hbI.sub (intervalIntegrable_const (c := (q.bottom.value b).im))),
      integral_sub htI intervalIntegrable_const,integral_sub hbI intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,smul_eq_mul,q.top_right,q.bottom_right]
    ring
  have hh := norm_integral_le_of_norm_le_const hf
  rw [he,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  nlinarith

theorem boundaryLog_le (f : ℂ → ℂ) (a b u v K : ℝ)
    (q : BoundaryLogs f a b u v) (hab : a ≤ b)
    (hb : ∀ x ∈ Icc a b, |(∫ σ in x..b, logDeriv f (point σ u)).im| ≤ K)
    (ht : ∀ x ∈ Icc a b, |(∫ σ in x..b, logDeriv f (point σ v)).im| ≤ K) :
    boundaryLog f a b u v q ≤
      (∫ t in u..v, Real.log ‖f (point a t)‖)-
      (∫ t in u..v, Real.log ‖f (point b t)‖)+
      (b-a)*((q.right.value v).im-(q.right.value u).im)+2*(b-a)*K := by
  have h := (abs_le.mp (boundary_horizontal_error f a b u v K q hab hb ht)).2
  unfold boundaryLog
  linarith

/-- The horizontal supplier is discharged for the actual moving family;
the right lift's phase is still visible in the exact boundary budget. -/
theorem auxiliary_boundaryLog_le : ∀ᶠ T : ℝ in atTop, ∀ a u v : ℝ,
    7/16 ≤ a → a ≤ 3 → T ≤ u → u ≤ v → v ≤ 2*T →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    ∀ q : BoundaryLogs (auxiliary T) a 3 u v,
      boundaryLog (auxiliary T) a 3 u v q ≤
        (∫ t in u..v, Real.log ‖auxiliary T (point a t)‖)-
        (∫ t in u..v, Real.log ‖auxiliary T (point 3 t)‖)+
        (3-a)*((q.right.value v).im-(q.right.value u).im)+
        2*(3-a)*(WuHorizontalBound.phaseConstant+3*WuStirling.firstConstant)*Real.log T := by
  filter_upwards [WuAuxiliaryHorizontal.auxiliary_horizontal_safe] with T hT
  intro a u v ha hab hu huv hv hsu hsv q
  exact (boundaryLog_le _ _ _ _ _ _ q hab
    (fun x hx => hT u ⟨hu,huv.trans hv⟩ hsu x 3 (ha.trans hx.1) hx.2 le_rfl)
    (fun x hx => hT v ⟨hu.trans huv,hv⟩ hsv x 3 (ha.trans hx.1) hx.2 le_rfl)).trans_eq (by ring)

#print axioms edge_increment
#print axioms boundary_horizontal_error
#print axioms boundaryLog_le
#print axioms auxiliary_boundaryLog_le
end XiPrime8845.WuBoundaryPhase

import WuContourCounting

/-! The gamma contribution with counterclockwise orientation fixed.
H has no zeros in these positive-height rectangles. Its weighted Littlewood
boundary is exactly zero; its unweighted phase supplies length*log(T)/2.
No estimate for the residual V phase is assumed here. -/
noncomputable section
open scoped BigOperators
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuGammaPhase
open WuLittlewood WuStirling WuContourCounting WuBoundaryPhase
set_option maxHeartbeats 2000000

theorem point_ne_one (x t : ℝ) (ht : 0 < t) : point x t ≠ 1 := by
  intro he
  have := congrArg Complex.im he
  simp [point] at this
  linarith

theorem rectangle_regular (a b u v : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hab : a ≤ b) (huv : u ≤ v) :
    AnalyticOnNhd ℂ H (Rectangle (point a u) (point b v)) ∧
      ∀ s ∈ Rectangle (point a u) (point b v), H s ≠ 0 := by
  have hr (s : ℂ) (hs : s ∈ Rectangle (point a u) (point b v)) :=
    (rectangle_membership a b u v hab huv s).mp hs
  have hn (s : ℂ) (hs : s ∈ Rectangle (point a u) (point b v)) : s ≠ 1 := by
    intro he
    have hh := (hr s hs).2.1
    rw [he] at hh
    norm_num at hh
    linarith
  exact ⟨fun s hs => H_analytic s (ha.trans_le (hr s hs).1.1),
    fun s hs => H_ne_zero s (ha.trans_le (hr s hs).1.1) (hn s hs)⟩

theorem otherPhase_eq (a b u v : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hab : a ≤ b) (huv : u ≤ v) :
    otherPhase H a b u v = verticalPhase H a u v := by
  obtain ⟨hf,hn⟩ := rectangle_regular a b u v ha hu hab huv
  have hh := argument_count H a b u v hab huv hf
    (fun s hs => hn s (rectangleBorder_subset_rectangle _ _ hs)) ∅ (by
      intro s
      constructor
      · simp
      · intro hs; exact False.elim (hn s hs.1 hs.2))
  simpa only [Finset.sum_empty,mul_zero,sub_eq_zero] using hh

theorem boundary_zero (a b u v : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hab : a ≤ b) (huv : u ≤ v) (q : BoundaryLogs H a b u v) :
    boundaryLog H a b u v q = 0 := by
  obtain ⟨hf,hn⟩ := rectangle_regular a b u v ha hu hab huv
  have hh := littlewood H a b u v hab huv hf
    (fun s hs => hn s (rectangleBorder_subset_rectangle _ _ hs)) ∅
    (fun s hs => by simp [hn s hs]) (by simp) q
  simpa using hh.symm

theorem vertical_main_bound (T a u v : ℝ) (hT : 4 ≤ T) (ha : 0 < a)
    (ha3 : a ≤ 3) (hu : T ≤ u) (huv : u ≤ v) (hv : v ≤ 2*T) :
    |verticalPhase H a u v-(v-u)*Real.log T/2| ≤ firstConstant*(v-u) := by
  have hreg (t : ℝ) (ht : t ∈ Icc u v) :
      AnalyticAt ℂ H (point a t) ∧ H (point a t) ≠ 0 := by
    have hr : 0 < (point a t).re := by simpa [point] using ha
    exact ⟨H_analytic _ hr,H_ne_zero _ hr (point_ne_one a t (by linarith [ht.1]))⟩
  have hi : IntervalIntegrable (fun t => I*logDeriv H (point a t)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le huv] at ht
    have hh := hreg t ht
    exact (continuousAt_const.mul (((hh.1.deriv.continuousAt).div hh.1.continuousAt hh.2).comp
      (show ContinuousAt (fun t : ℝ => point a t) t by unfold point; fun_prop))).continuousWithinAt
  have he : verticalPhase H a u v-(v-u)*Real.log T/2 =
      (∫ t in u..v, I*logDeriv H (point a t)-I*(Real.log T:ℂ)/2).im := by
    rw [integral_sub hi intervalIntegrable_const]
    simp [verticalPhase,intervalIntegral.integral_const,mul_im,mul_re]
  rw [he]
  apply (Complex.abs_im_le_norm _).trans
  have hb : ∀ t ∈ uIoc u v, ‖I*logDeriv H (point a t)-I*(Real.log T:ℂ)/2‖ ≤ firstConstant := by
    intro t ht
    rw [uIoc_of_le huv] at ht
    have hr : 0 < (point a t).re := by simpa [point] using ha
    rw [show logDeriv H (point a t) = Zeta23.XiPrime.Lfn (point a t) from
      H_logDeriv _ hr (point_ne_one a t (by linarith [ht.1]))]
    rw [show I*Zeta23.XiPrime.Lfn (point a t)-I*(Real.log T:ℂ)/2 =
      I*(Zeta23.XiPrime.Lfn (point a t)-(Real.log T:ℂ)/2) by ring,norm_mul,norm_I,one_mul]
    exact Lfn_stirling_bound T _ hT hr (by simp [point]; linarith)
      (by simp [point]; linarith [ht.1]) (by simp [point]; linarith [ht.2])
  simpa only [abs_of_nonneg (sub_nonneg.mpr huv)] using norm_integral_le_of_norm_le_const hb

theorem otherPhase_main_bound (T a b u v : ℝ) (hT : 4 ≤ T) (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 3) (hu : T ≤ u) (huv : u ≤ v) (hv : v ≤ 2*T) :
    |otherPhase H a b u v-(v-u)*Real.log T/2| ≤ firstConstant*(v-u) := by
  rw [otherPhase_eq a b u v ha (by linarith) hab huv]
  exact vertical_main_bound T a u v hT ha (hab.trans hb) hu huv hv

#print axioms rectangle_regular
#print axioms otherPhase_eq
#print axioms boundary_zero
#print axioms vertical_main_bound
#print axioms otherPhase_main_bound
end XiPrime8845.WuGammaPhase

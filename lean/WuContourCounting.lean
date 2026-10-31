import WuParallelReturn

/-! Finite merger of the original eta argument principle and auxiliary
Littlewood. The original eta right and horizontal phases remain explicit;
this is not yet the normalized local Wu counting inequality. -/
noncomputable section
open scoped BigOperators
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuContourCounting
open WuLittlewood WuAuxiliary WuAuxiliaryBoundary WuBoundaryPhase
set_option maxHeartbeats 2000000

def verticalPhase (f : ℂ → ℂ) (a u v : ℝ) : ℝ :=
  (∫ t in u..v, I*logDeriv f (point a t)).im

def otherPhase (f : ℂ → ℂ) (a b u v : ℝ) : ℝ :=
  (∫ x in a..b, logDeriv f (point x u)).im+
    verticalPhase f b u v-(∫ x in a..b, logDeriv f (point x v)).im

/-- Counterclockwise rectangle: bottom + right - top - left.
The signs here fix the orientation of the parallel critical-edge detour. -/
theorem rectangle_phase (f : ℂ → ℂ) (a b u v : ℝ) :
    (RectangleIntegral (logDeriv f) (point a u) (point b v)).im =
      otherPhase f a b u v-verticalPhase f a u v := by
  simp only [RectangleIntegral,HIntegral,VIntegral,point,add_re,ofReal_re,mul_re,
    ofReal_im,I_re,I_im,mul_zero,sub_self,add_zero,add_im,mul_im,mul_one,zero_add,
    smul_eq_mul,← intervalIntegral.integral_const_mul,verticalPhase,otherPhase,
    add_im,sub_im]
  ring

theorem argument_count (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (hf : AnalyticOnNhd ℂ f (Rectangle (point a u) (point b v)))
    (hn : ∀ s ∈ RectangleBorder (point a u) (point b v), f s ≠ 0)
    (W : Finset ℂ)
    (hW : ∀ s, s ∈ W ↔ s ∈ Rectangle (point a u) (point b v) ∧ f s = 0) :
    otherPhase f a b u v-verticalPhase f a u v =
      2*Real.pi*(∑ s ∈ W, (analyticOrderNatAt f s:ℝ)) := by
  have h := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (g := fun _ => (1:ℂ))
    (by simpa [point] using hab) (by simpa [point] using huv) hf
    (fun _ _ => analyticAt_const) hn W
    (fun s hs => ⟨fun hz => (hW s).mpr ⟨hs,hz⟩,fun hz => ((hW s).mp hz).2⟩)
    (fun s hs => ((hW s).mp hs).1)
  simp only [one_mul,mul_one] at h
  change (1/(2*↑Real.pi*I))*RectangleIntegral (logDeriv f) (point a u) (point b v) = _ at h
  have hp : (2*↑Real.pi*I:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have he : RectangleIntegral (logDeriv f) (point a u) (point b v) =
      (2*↑Real.pi*I)*∑ s ∈ W, (analyticOrderNatAt f s:ℂ) := by
    rw [← h]; field_simp
  rw [← rectangle_phase,he]
  simp [mul_im,mul_re,Complex.re_sum,Complex.im_sum]

/-- The two boundary identities meet through the SAME eta zero set W.
W is counted with full orders; the auxiliary sum may also include psi
zeros. No estimate for otherPhase is smuggled into this merger. -/
theorem phase_littlewood (T a c b u v ε : ℝ) (hT : 1 < T)
    (hac : a ≤ c) (hcb : c ≤ b) (huv : u ≤ v)
    (S W Z : Finset ℂ)
    (hW : ∀ s, s ∈ W ↔ s ∈ Rectangle (point c u) (point b v) ∧ eta (Real.log T) s = 0)
    (hn : ∀ s ∈ RectangleBorder (point c u) (point b v), eta (Real.log T) s ≠ 0)
    (hWZ : W ⊆ Z) (hWre : ∀ s ∈ W, c ≤ s.re) (hZre : ∀ s ∈ Z, a ≤ s.re)
    (q : BoundaryLogs (auxiliary T) a b u v)
    (hl : 2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a)) =
      boundaryLog (auxiliary T) a b u v q)
    (hp : |verticalPhase (eta (Real.log T)) c u v| ≤
      Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)+ε) :
    (c-a)*(otherPhase (eta (Real.log T)) c b u v-
      Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)-ε) ≤
        boundaryLog (auxiliary T) a b u v q := by
  have hc := argument_count (eta (Real.log T)) c b u v hcb huv
    (fun s _ => (eta_entire _).analyticAt s) hn W hW
  have hw := WuRightLittlewood.eta_count_le_boundary T a c b u v hT hac W Z hWZ hWre hZre q hl
  have hv := (le_abs_self _).trans hp
  have hh := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hac)
  nlinarith

/-- Supplies the original eta phase hypothesis in the merger, on either
side of the critical line and for every sufficiently close parallel path.
The radius depends on this frozen window, as allowed by finite contour use. -/
theorem original_eta_phase_supplier (T u v : ℝ) (hT : 1 < T) (huv : u ≤ v) :
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ Zeta23.XiPrime.xiDeriv s = 0) ∧
      ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, 0 < |c-1/2| → |c-1/2| < r →
        (∀ t ∈ Icc u v, eta (Real.log T) (point c t) ≠ 0) ∧
        |verticalPhase (eta (Real.log T)) c u v| ≤
          Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)+ε :=
  WuParallelReturn.parallel_phase_count (Real.log T) u v (Real.log_pos hT).ne' huv

theorem rectangle_membership (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v) (s : ℂ) :
    s ∈ Rectangle (point a u) (point b v) ↔ s.re ∈ Icc a b ∧ s.im ∈ Icc u v := by
  simp [Rectangle,point,mem_reProdIm,uIcc_of_le hab,uIcc_of_le huv]

/-- Actual finite-window merger. The parallel eta rectangle and its exact
zero set are constructed, not supplied as a counting hypothesis. The
auxiliary Littlewood identity is precisely the existing boundary input. -/
theorem actual_window_merger (T a u v : ℝ) (hT : 1 < T) (ha : a < 1/2) (huv : u ≤ v)
    (hu : u ∉ WuSafeEndpoints.badHeights (auxiliary T))
    (hv : v ∉ WuSafeEndpoints.badHeights (auxiliary T))
    (hr : ∀ t ∈ Icc u v, auxiliary T (point 3 t) ≠ 0)
    (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle (point a u) (point 3 v) ∧ auxiliary T s = 0)
    (q : BoundaryLogs (auxiliary T) a 3 u v)
    (hl : 2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a)) =
      boundaryLog (auxiliary T) a 3 u v q) :
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ Zeta23.XiPrime.xiDeriv s = 0) ∧
      ∀ ε > 0, ∃ c ∈ Ioo (1/2:ℝ) 3,
        (c-a)*(otherPhase (eta (Real.log T)) c 3 u v-
          Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)-ε) ≤
            boundaryLog (auxiliary T) a 3 u v q := by
  classical
  obtain ⟨S,hS,hphase⟩ := original_eta_phase_supplier T u v hT huv
  refine ⟨S,hS,?_⟩
  intro ε hε
  obtain ⟨r,hr0,hrphase⟩ := hphase ε hε
  let c := 1/2+(min r 1)/2
  have hc : 1/2 < c ∧ c < 3 := by
    have hmin : 0 < min r 1 := lt_min hr0 (by norm_num)
    have hmax : min r 1 ≤ 1 := min_le_right _ _
    dsimp [c]; constructor <;> linarith
  have hdist : |c-1/2| < r := by
    have hm : min r 1 ≤ r := min_le_left _ _
    rw [abs_of_pos (sub_pos.mpr hc.1)]
    dsimp [c]; linarith
  obtain ⟨hleft,hp⟩ := hrphase c (abs_pos.mpr (sub_ne_zero.mpr hc.1.ne')) hdist
  have heZero (s : ℂ) (hs : eta (Real.log T) s = 0) : auxiliary T s = 0 := by
    unfold auxiliary; rw [hs,zero_mul]
  have hsafe (t : ℝ) (ht : t ∉ WuSafeEndpoints.badHeights (auxiliary T)) :
      t ∉ WuSafeEndpoints.badHeights (eta (Real.log T)) := by
    rintro ⟨s,hs,rfl⟩
    exact ht ⟨s,heZero s hs,rfl⟩
  have hright (t : ℝ) (ht : t ∈ Icc u v) : eta (Real.log T) (point 3 t) ≠ 0 :=
    fun hz => hr t ht (heZero _ hz)
  have hn := WuSafeEndpoints.boundary_nonzero _ c 3 u v hc.2.le huv
    (hsafe u hu) (hsafe v hv) hleft hright
  have hf : AnalyticOnNhd ℂ (eta (Real.log T)) (Rectangle (point c u) (point 3 v)) :=
    fun s _ => (eta_entire _).analyticAt s
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf (left_mem_rect _ _)
    (hleft u ⟨le_rfl,huv⟩)
  let W := hfin.toFinset
  have hW (s : ℂ) : s ∈ W ↔ s ∈ Rectangle (point c u) (point 3 v) ∧ eta (Real.log T) s = 0 := by
    simp [W]
  refine ⟨c,hc,phase_littlewood T a c 3 u v ε hT (by linarith [hc.1]) hc.2.le huv
    S W Z hW hn ?_ ?_ ?_ q hl hp⟩
  · intro s hs
    obtain ⟨hs,hzero⟩ := (hW s).mp hs
    have hm := (rectangle_membership c 3 u v hc.2.le huv s).mp hs
    exact (hZ s).mpr ⟨(rectangle_membership a 3 u v (by linarith) huv s).mpr
      ⟨⟨by linarith [hm.1.1,hc.1],hm.1.2⟩,hm.2⟩,heZero s hzero⟩
  · intro s hs
    exact ((rectangle_membership c 3 u v hc.2.le huv s).mp ((hW s).mp hs).1).1.1
  · intro s hs
    exact ((rectangle_membership a 3 u v (by linarith) huv s).mp ((hZ s).mp hs).1).1.1

/-- Supplies both rectangles, the original eta phase transfer, the return
of the auxiliary left logarithmic integral, and the uniform horizontal
budget. No auxiliary zero set or Littlewood equality is an input here.
The remaining main-phase evaluation is explicit in otherPhase. -/
theorem eventual_window_merger : ∀ᶠ T : ℝ in atTop,
    ∀ a u v ε w : ℝ, 7/16+w ≤ a → a < 1/2 →
    T ≤ u → u ≤ v → v ≤ 2*T → 0 < ε → 0 < w →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    ∃ x ∈ Ioo (a-w) a, ∃ q : BoundaryLogs (auxiliary T) x 3 u v, ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ Zeta23.XiPrime.xiDeriv s = 0) ∧
      (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖auxiliary T (point a t)‖)+ε ∧
      (∀ κ > 0, ∃ c ∈ Ioo (1/2:ℝ) 3,
        (c-x)*(otherPhase (eta (Real.log T)) c 3 u v-
          Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)-κ) ≤
            boundaryLog (auxiliary T) x 3 u v q) ∧
      boundaryLog (auxiliary T) x 3 u v q ≤
        (∫ t in u..v, Real.log ‖auxiliary T (point x t)‖)-
        (∫ t in u..v, Real.log ‖auxiliary T (point 3 t)‖)+
        (3-x)*verticalPhase (auxiliary T) 3 u v+
        2*(3-x)*(WuHorizontalBound.phaseConstant+3*WuStirling.firstConstant)*Real.log T := by
  filter_upwards [WuRightLittlewood.littlewood_eventually,WuRightBoundary.right_nonzero,
    auxiliary_boundaryLog_le,eventually_gt_atTop (1:ℝ)] with T hl hr hh hT
  intro a u v ε w ha ha' hu huv hv hε hw hsu hsv
  obtain ⟨x,hx,Z,q,hZ,he,hleft⟩ := hl a u v ε w (by linarith) hu huv hv hε hw hsu hsv
  obtain ⟨S,hS,hcount⟩ := actual_window_merger T x u v hT (hx.2.trans ha') huv hsu hsv
    (fun t ht => hr t ⟨hu.trans ht.1,ht.2.trans hv⟩) Z hZ q he
  refine ⟨x,hx,q,S,hS,hleft,hcount,?_⟩
  have hb := hh x u v (by linarith [hx.1]) (by linarith [hx.2]) hu huv hv hsu hsv q
  have heq : verticalPhase (auxiliary T) 3 u v =
      (q.right.value v).im-(q.right.value u).im := by
    simpa [verticalPhase,point] using congrArg Complex.im
      (edge_increment q.right huv u v le_rfl huv le_rfl)
  rwa [heq]

#print axioms rectangle_phase
#print axioms argument_count
#print axioms phase_littlewood
#print axioms original_eta_phase_supplier
#print axioms actual_window_merger
#print axioms eventual_window_merger
end XiPrime8845.WuContourCounting

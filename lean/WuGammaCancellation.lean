import WuGammaPhase

/-! Exact removal of a zero-free gamma factor from compatible boundary
logarithms. All lifts are subtracted together, including their right anchors.
This is a finite identity, not a bound on principal arguments. -/
noncomputable section
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuGammaCancellation
open WuLittlewood WuStirling WuAuxiliary WuAuxiliaryBoundary WuGammaPhase
set_option maxHeartbeats 2000000

def edgeQuotient {f g : ℂ → ℂ} {z d : ℂ} {a b : ℝ}
    (q : EdgeLog f z d a b) (r : EdgeLog g z d a b)
    (hl : ∀ t ∈ uIcc a b, logDeriv (fun s => f s/g s) (z+t*d) =
      logDeriv f (z+t*d)-logDeriv g (z+t*d)) :
    EdgeLog (fun s => f s/g s) z d a b where
  value t := q.value t-r.value t
  continuous := q.continuous.sub r.continuous
  exp_eq t ht := by rw [Complex.exp_sub,q.exp_eq t ht,r.exp_eq t ht]
  derivative t ht := by
    have hh := (q.derivative t ht).sub (r.derivative t ht)
    rw [hl t (by exact ⟨ht.1.le,ht.2.le⟩)]
    exact hh.congr_deriv (by ring)
  integrable := (q.integrable.sub r.integrable).congr (fun t ht => by
    rw [hl t (uIoc_subset_uIcc ht)]; ring)

def quotientLogs (f g : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (q : BoundaryLogs f a b u v) (r : BoundaryLogs g a b u v)
    (hl : ∀ s ∈ RectangleBorder (point a u) (point b v),
      logDeriv (fun s => f s/g s) s = logDeriv f s-logDeriv g s) :
    BoundaryLogs (fun s => f s/g s) a b u v := by
  have hh (x y : ℝ) (hx : x ∈ uIcc a b) (hy : y = u ∨ y = v) :
      y*I+(x:ℂ)*1 ∈ RectangleBorder (point a u) (point b v) := by
    rw [uIcc_of_le hab] at hx
    rcases hy with rfl | rfl <;>
      simp [RectangleBorder,mem_reProdIm,point,uIcc_of_le hab,uIcc_of_le huv,hx,add_comm]
  have hv (x y : ℝ) (hx : x = a ∨ x = b) (hy : y ∈ uIcc u v) :
      (x:ℂ)+y*I ∈ RectangleBorder (point a u) (point b v) := by
    rw [uIcc_of_le huv] at hy
    rcases hx with rfl | rfl <;>
      simp [RectangleBorder,mem_reProdIm,point,uIcc_of_le hab,uIcc_of_le huv,hy]
  exact {
    bottom := edgeQuotient q.bottom r.bottom (fun t ht => hl _ (hh t u ht (Or.inl rfl)))
    top := edgeQuotient q.top r.top (fun t ht => hl _ (hh t v ht (Or.inr rfl)))
    left := edgeQuotient q.left r.left (fun t ht => hl _ (hv a t (Or.inl rfl) ht))
    right := edgeQuotient q.right r.right (fun t ht => hl _ (hv b t (Or.inr rfl) ht))
    bottom_right := by simp [edgeQuotient,q.bottom_right,r.bottom_right]
    top_right := by simp [edgeQuotient,q.top_right,r.top_right] }

theorem quotient_boundary (f g : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (q : BoundaryLogs f a b u v) (r : BoundaryLogs g a b u v)
    (hl : ∀ s ∈ RectangleBorder (point a u) (point b v),
      logDeriv (fun s => f s/g s) s = logDeriv f s-logDeriv g s) :
    boundaryLog (fun s => f s/g s) a b u v (quotientLogs f g a b u v hab huv q r hl) =
      boundaryLog f a b u v q-boundaryLog g a b u v r := by
  have he (x : ℂ) (Q : EdgeLog f x I u v) (R : EdgeLog g x I u v)
      (h : ∀ t ∈ uIcc u v, logDeriv (fun s => f s/g s) (x+t*I) =
        logDeriv f (x+t*I)-logDeriv g (x+t*I)) :
      (∫ t in u..v, Real.log ‖f (x+t*I)/g (x+t*I)‖) =
        (∫ t in u..v, Real.log ‖f (x+t*I)‖)-(∫ t in u..v, Real.log ‖g (x+t*I)‖) := by
    have eq1 := (edgeQuotient Q R h).real_eq
    have hQ := (Complex.continuous_re.comp_continuousOn Q.continuous).intervalIntegrable (μ := volume)
    have hR := (Complex.continuous_re.comp_continuousOn R.continuous).intervalIntegrable (μ := volume)
    dsimp only [Function.comp_def] at hQ hR
    calc
      _ = ∫ t in u..v, (Q.value t).re-(R.value t).re := integral_congr (fun t ht => by
        simpa [edgeQuotient] using (eq1 t ht).symm)
      _ = _ := by
        rw [integral_sub hQ hR]
        congr 1 <;> apply integral_congr <;> intro t ht
        · exact Q.real_eq t ht
        · exact R.real_eq t ht
  let p := quotientLogs f g a b u v hab huv q r hl
  have hleft : (∫ t in u..v, Real.log ‖f (point a t)/g (point a t)‖) =
      (∫ t in u..v, Real.log ‖f (point a t)‖)-(∫ t in u..v, Real.log ‖g (point a t)‖) := by
    apply he a q.left r.left
    intro t ht
    apply hl
    simp only [uIcc_of_le huv] at ht
    simp [RectangleBorder,point,mem_reProdIm,uIcc_of_le hab,uIcc_of_le huv,ht]
  have hright : (∫ t in u..v, Real.log ‖f (point b t)/g (point b t)‖) =
      (∫ t in u..v, Real.log ‖f (point b t)‖)-(∫ t in u..v, Real.log ‖g (point b t)‖) := by
    apply he b q.right r.right
    intro t ht
    apply hl
    simp only [uIcc_of_le huv] at ht
    simp [RectangleBorder,point,mem_reProdIm,uIcc_of_le hab,uIcc_of_le huv,ht]
  unfold boundaryLog
  rw [hleft,hright]
  simp only [quotientLogs,edgeQuotient,sub_im]
  have hqt := (Complex.continuous_im.comp_continuousOn q.top.continuous).intervalIntegrable (μ := volume)
  have hrt := (Complex.continuous_im.comp_continuousOn r.top.continuous).intervalIntegrable (μ := volume)
  have hqb := (Complex.continuous_im.comp_continuousOn q.bottom.continuous).intervalIntegrable (μ := volume)
  have hrb := (Complex.continuous_im.comp_continuousOn r.bottom.continuous).intervalIntegrable (μ := volume)
  dsimp only [Function.comp_def] at hqt hrt hqb hrb
  rw [integral_sub hqt hrt,integral_sub hqb hrb]
  ring

/-- H is removed exactly, including all horizontal and right-edge phases.
The quotient is the original V_T psi_T, not a replacement mollifier. -/
theorem auxiliary_cancellation (T a b u v : ℝ) (ha : 0 < a) (hu : 0 < u)
    (hab : a ≤ b) (huv : u ≤ v)
    (hn : ∀ s ∈ RectangleBorder (point a u) (point b v), auxiliary T s ≠ 0)
    (q : BoundaryLogs (auxiliary T) a b u v) :
    ∃ p : BoundaryLogs (fun s => V T s*psi T s) a b u v,
      boundaryLog (auxiliary T) a b u v q = boundaryLog (fun s => V T s*psi T s) a b u v p := by
  obtain ⟨hH,hHn⟩ := rectangle_regular a b u v ha hu hab huv
  obtain ⟨r⟩ := boundaryLogs_exists H a b u v hab huv hH
    (fun s hs => hHn s (rectangleBorder_subset_rectangle _ _ hs))
  have hl (s : ℂ) (hs : s ∈ RectangleBorder (point a u) (point b v)) :
      logDeriv (fun s => auxiliary T s/H s) s = logDeriv (auxiliary T) s-logDeriv H s :=
    logDeriv_div s (hn s hs) (hHn s (rectangleBorder_subset_rectangle _ _ hs))
      (auxiliary_entire T).differentiableAt (hH s (rectangleBorder_subset_rectangle _ _ hs)).differentiableAt
  have he : (fun s => auxiliary T s/H s) = (fun s => V T s*psi T s) := by
    funext s; unfold auxiliary V; ring
  have hp := quotient_boundary (auxiliary T) H a b u v hab huv q r hl
  rw [boundary_zero a b u v ha hu hab huv r,sub_zero] at hp
  have hex : ∃ p : BoundaryLogs (fun s => auxiliary T s/H s) a b u v,
      boundaryLog (auxiliary T) a b u v q = boundaryLog (fun s => auxiliary T s/H s) a b u v p :=
    ⟨_,hp.symm⟩
  exact (congrArg (fun f : ℂ → ℂ => ∃ p : BoundaryLogs f a b u v,
    boundaryLog (auxiliary T) a b u v q = boundaryLog f a b u v p) he).mp hex

/-- Uniform gamma-free Littlewood budget. The right phase costs only pi;
the horizontal cost is the already proved V_T psi_T bound. -/
theorem gamma_free_boundary_bound : ∀ᶠ T : ℝ in atTop, ∀ a u v : ℝ,
    7/16 ≤ a → a ≤ 3 → T ≤ u → u ≤ v → v ≤ 2*T →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    (∀ s ∈ RectangleBorder (point a u) (point 3 v), auxiliary T s ≠ 0) →
    ∀ q : BoundaryLogs (auxiliary T) a 3 u v,
      boundaryLog (auxiliary T) a 3 u v q ≤
        (∫ t in u..v, Real.log ‖V T (point a t)*psi T (point a t)‖)-
        (∫ t in u..v, Real.log ‖V T (point 3 t)*psi T (point 3 t)‖)+
        (3-a)*Real.pi+2*(3-a)*WuHorizontalBound.phaseConstant*Real.log T := by
  filter_upwards [WuHorizontalBound.horizontal_safe,WuRightBoundary.right_phase_bound,
    eventually_gt_atTop (0:ℝ)] with T hh hr hT
  intro a u v ha hab hu huv hv hsu hsv hn q
  obtain ⟨p,hp⟩ := auxiliary_cancellation T a 3 u v (by linarith) (by linarith) hab huv hn q
  rw [hp]
  have hb := WuBoundaryPhase.boundaryLog_le _ a 3 u v _ p hab
    (fun x hx => hh u ⟨hu,huv.trans hv⟩ hsu x 3 (ha.trans hx.1) hx.2 le_rfl)
    (fun x hx => hh v ⟨hu.trans huv,hv⟩ hsv x 3 (ha.trans hx.1) hx.2 le_rfl)
  have he := congrArg Complex.im (WuBoundaryPhase.edge_increment p.right huv u v le_rfl huv le_rfl)
  have hr' := hr u v hu huv hv
  simp only [sub_im] at he
  rw [show (fun t : ℝ => logDeriv (fun s => V T s*psi T s) (point 3 t)*I) =
    (fun t : ℝ => I*logDeriv (fun s => V T s*psi T s) ((3:ℝ)+t*I)) from by
      funext t; simp only [point]; ring] at hr'
  rw [he] at hr'
  have hs := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hr') (sub_nonneg.mpr hab)
  exact hb.trans (by linarith)

#print axioms quotient_boundary
#print axioms auxiliary_cancellation
#print axioms gamma_free_boundary_bound
end XiPrime8845.WuGammaCancellation

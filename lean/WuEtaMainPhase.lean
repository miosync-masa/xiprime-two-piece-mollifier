import WuVHorizontal
import WuGammaCancellation

/-! The previously explicit otherPhase is evaluated for the actual eta_T.
The gamma main term and the residual V phase have separate proven bounds,
uniform in the height and in both chosen safe horizontal endpoints. -/
noncomputable section
open scoped BigOperators
open Complex Set Filter Topology MeasureTheory intervalIntegral
namespace XiPrime8845.WuEtaMainPhase
open WuLittlewood WuAuxiliary WuAuxiliaryBoundary WuStirling WuContourCounting WuGammaPhase
set_option maxHeartbeats 2000000

theorem path_integrable (f : ℂ → ℂ) (z d : ℂ) (a b : ℝ)
    (hf : ∀ t ∈ uIcc a b, AnalyticAt ℂ f (z+t*d))
    (hn : ∀ t ∈ uIcc a b, f (z+t*d) ≠ 0) :
    IntervalIntegrable (fun t => d*logDeriv f (z+t*d)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact (continuousAt_const.mul (((hf t ht).deriv.continuousAt.div (hf t ht).continuousAt
    (hn t ht)).comp (f := fun t : ℝ => z+t*d)
      (show ContinuousAt (fun t : ℝ => z+t*d) t by fun_prop))).continuousWithinAt

theorem eta_path_split (T : ℝ) (z d : ℂ) (a b : ℝ)
    (hr : ∀ t ∈ uIcc a b, 0 < (z+t*d).re)
    (h1 : ∀ t ∈ uIcc a b, z+t*d ≠ 1)
    (hn : ∀ t ∈ uIcc a b, eta (Real.log T) (z+t*d) ≠ 0) :
    (∫ t in a..b, d*logDeriv (eta (Real.log T)) (z+t*d)) =
      (∫ t in a..b, d*logDeriv H (z+t*d))+
        ∫ t in a..b, d*logDeriv (V T) (z+t*d) := by
  have hH (t : ℝ) (ht : t ∈ uIcc a b) := H_ne_zero _ (hr t ht) (h1 t ht)
  have hiH := path_integrable H z d a b (fun t ht => H_analytic _ (hr t ht)) hH
  have hiV := path_integrable (V T) z d a b
    (fun t ht => ((eta_entire _).analyticAt _).div (H_analytic _ (hr t ht)) (hH t ht))
    (fun t ht => div_ne_zero (hn t ht) (hH t ht))
  rw [← integral_add hiH hiV]
  apply integral_congr
  intro t ht
  have he := logDeriv_div (z+t*d) (hn t ht) (hH t ht)
    (eta_entire _).differentiableAt (H_analytic _ (hr t ht)).differentiableAt
  change logDeriv (V T) (z+t*d) = _ at he
  dsimp only
  rw [he]
  ring

theorem otherPhase_split (T a b u v : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hu : 0 < u) (huv : u ≤ v)
    (hbottom : ∀ x ∈ Icc a b, eta (Real.log T) (point x u) ≠ 0)
    (htop : ∀ x ∈ Icc a b, eta (Real.log T) (point x v) ≠ 0)
    (hright : ∀ t ∈ Icc u v, eta (Real.log T) (point b t) ≠ 0) :
    otherPhase (eta (Real.log T)) a b u v = otherPhase H a b u v+otherPhase (V T) a b u v := by
  have hh (t : ℝ) (ht : 0 < t)
      (hn : ∀ x ∈ Icc a b, eta (Real.log T) (point x t) ≠ 0) :=
    eta_path_split T (t*I) 1 a b (by
      intro x hx; rw [uIcc_of_le hab] at hx; simp; linarith [hx.1])
      (by intro x hx; simpa [point,mul_one,add_comm] using point_ne_one x t ht)
      (by intro x hx; rw [uIcc_of_le hab] at hx; simpa [point,mul_one,add_comm] using hn x hx)
  have hb := hh u hu hbottom
  have ht := hh v (hu.trans_le huv) htop
  have hr := eta_path_split T b I u v
    (by intro t ht; simp; linarith)
    (by intro t ht; rw [uIcc_of_le huv] at ht; exact point_ne_one b t (hu.trans_le ht.1))
    (by intro t ht; rw [uIcc_of_le huv] at ht; exact hright t ht)
  simp only [one_mul,mul_one,add_comm (↑u*I),add_comm (↑v*I)] at hb ht
  unfold otherPhase verticalPhase
  change (∫ x in a..b, logDeriv (eta (Real.log T)) (x+u*I)).im+
    (∫ t in u..v, I*logDeriv (eta (Real.log T)) (b+t*I)).im-
    (∫ x in a..b, logDeriv (eta (Real.log T)) (x+v*I)).im = _
  rw [hb,ht,hr]
  simp only [add_im,point]
  ring

/-- Main term for the original eta, not for eta times the mollifier.
No zero-free condition on the left parallel edge is needed for these
three edges. The same constants work for all a in [7/16,3]. -/
theorem otherPhase_main : ∀ᶠ T : ℝ in atTop, ∀ a u v : ℝ,
    7/16 ≤ a → a ≤ 3 → T ≤ u → u ≤ v → v ≤ 2*T →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    |otherPhase (eta (Real.log T)) a 3 u v-(v-u)*Real.log T/2| ≤
      firstConstant*(v-u)+2*WuVHorizontal.phaseConstant*Real.log T+Real.pi := by
  filter_upwards [WuVHorizontal.horizontal_bound,WuVHorizontal.right_phase_bound,
    WuRightBoundary.right_nonzero,eventually_ge_atTop (4:ℝ)] with T hh hr hn hT
  intro a u v ha ha3 hu huv hv hsu hsv
  have hz (s : ℂ) (hs : auxiliary T s ≠ 0) : eta (Real.log T) s ≠ 0 := by
    intro he; apply hs; simp [auxiliary,he]
  have he (t : ℝ) (hs : t ∉ WuSafeEndpoints.badHeights (auxiliary T)) (x : ℝ) :=
    hz (point x t) (WuSafeEndpoints.horizontal_nonzero _ t hs x)
  have hV (t : ℝ) (hs : t ∉ WuSafeEndpoints.badHeights (auxiliary T))
      (ht : T ≤ t) (x : ℝ) (hx : x ∈ Icc a 3) : V T (point x t) ≠ 0 :=
    div_ne_zero (he t hs x) (H_ne_zero _ (by simp [point]; linarith [hx.1])
      (point_ne_one x t (by linarith)))
  have hb := hh u ⟨hu,huv.trans hv⟩ a 3 ha ha3 le_rfl (hV u hsu hu)
  have ht := hh v ⟨hu.trans huv,hv⟩ a 3 ha ha3 le_rfl (hV v hsv (hu.trans huv))
  have hvp := hr u v hu huv hv
  have hp : |otherPhase (V T) a 3 u v| ≤ 2*WuVHorizontal.phaseConstant*Real.log T+Real.pi := by
    unfold otherPhase
    exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hb hvp)) ht).trans_eq (by ring))
  have hg := otherPhase_main_bound T a 3 u v hT (by linarith) ha3 le_rfl hu huv hv
  rw [otherPhase_split T a 3 u v (by linarith) ha3 (by linarith) huv
    (fun x _ => he u hsu x) (fun x _ => he v hsv x)
    (fun t ht => hz _ (hn t ⟨hu.trans ht.1,ht.2.trans hv⟩))]
  have hh := (abs_add_le (otherPhase H a 3 u v-(v-u)*Real.log T/2)
    (otherPhase (V T) a 3 u v)).trans (add_le_add hg hp)
  rw [show otherPhase H a 3 u v+otherPhase (V T) a 3 u v-(v-u)*Real.log T/2 =
    (otherPhase H a 3 u v-(v-u)*Real.log T/2)+otherPhase (V T) a 3 u v by ring]
  exact hh.trans_eq (by ring)

/-- Finite counting merger with otherPhase evaluated and H cancelled.
The actual Littlewood zero set and identity are the existing finite
interface. Returning the left line to sigma0 and normalizing the count
are not asserted by this theorem. -/
theorem gamma_free_merger : ∀ᶠ T : ℝ in atTop, ∀ a u v : ℝ,
    7/16 ≤ a → a < 1/2 → T ≤ u → u ≤ v → v ≤ 2*T →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    (∀ s ∈ RectangleBorder (point a u) (point 3 v), auxiliary T s ≠ 0) →
    ∀ Z : Finset ℂ,
    (∀ s, s ∈ Z ↔ s ∈ Rectangle (point a u) (point 3 v) ∧ auxiliary T s = 0) →
    ∀ q : BoundaryLogs (auxiliary T) a 3 u v,
    (2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a)) =
      boundaryLog (auxiliary T) a 3 u v q) →
    ∃ S : Finset ℂ,
      (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧ Zeta23.XiPrime.xiDeriv s = 0) ∧
      ∀ κ > 0, ∃ c ∈ Ioo (1/2:ℝ) 3,
        (c-a)*((v-u)*Real.log T/2-
          (firstConstant*(v-u)+2*WuVHorizontal.phaseConstant*Real.log T+Real.pi)-
          Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)-κ) ≤
        (∫ t in u..v, Real.log ‖V T (point a t)*psi T (point a t)‖)-
        (∫ t in u..v, Real.log ‖V T (point 3 t)*psi T (point 3 t)‖)+
        (3-a)*Real.pi+2*(3-a)*WuHorizontalBound.phaseConstant*Real.log T := by
  filter_upwards [otherPhase_main,WuGammaCancellation.gamma_free_boundary_bound,
    WuRightBoundary.right_nonzero,eventually_gt_atTop (1:ℝ)] with T hm hb hr hT
  intro a u v ha ha' hu huv hv hsu hsv hn Z hZ q hq
  obtain ⟨S,hS,hs⟩ := actual_window_merger T a u v hT ha' huv hsu hsv
    (fun t ht => hr t ⟨hu.trans ht.1,ht.2.trans hv⟩) Z hZ q hq
  refine ⟨S,hS,?_⟩
  intro κ hκ
  obtain ⟨c,hc,hcount⟩ := hs κ hκ
  refine ⟨c,hc,?_⟩
  have hl := (abs_le.mp (hm c u v (by linarith [hc.1]) hc.2.le hu huv hv hsu hsv)).1
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ c-a by linarith [hc.1])
  have hbound := hb a u v ha (by linarith) hu huv hv hsu hsv hn q
  nlinarith

#print axioms eta_path_split
#print axioms otherPhase_split
#print axioms otherPhase_main
#print axioms gamma_free_merger
end XiPrime8845.WuEtaMainPhase

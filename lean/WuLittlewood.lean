import Zeta23.Analytic.RectangleLogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Rectangle Littlewood with explicit edge logarithms. The logarithms are
continuous lifts, not the principal argument. Only their right-hand corners
are matched; matching all four corners would incorrectly exclude zeros.
WuEdgeLog constructs these lifts from analyticity and a zero-free boundary. -/
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.WuLittlewood
set_option maxHeartbeats 2000000

def point (x y : ℝ) : ℂ := x+y*I

/-- Logarithm data on a parametrized straight edge. -/
structure EdgeLog (f : ℂ → ℂ) (z d : ℂ) (u v : ℝ) where
  value : ℝ → ℂ
  continuous : ContinuousOn value (uIcc u v)
  exp_eq : ∀ t ∈ uIcc u v, exp (value t) = f (z+t*d)
  derivative : ∀ t ∈ Ioo (min u v) (max u v),
    HasDerivAt value (d*logDeriv f (z+t*d)) t
  integrable : IntervalIntegrable (fun t => d*logDeriv f (z+t*d)) volume u v

theorem EdgeLog.real_eq {f : ℂ → ℂ} {z d : ℂ} {u v : ℝ}
    (q : EdgeLog f z d u v) (t : ℝ) (ht : t ∈ uIcc u v) :
    (q.value t).re = Real.log ‖f (z+t*d)‖ := by
  rw [← q.exp_eq t ht, norm_exp, Real.log_exp]

theorem EdgeLog.parts {f : ℂ → ℂ} {z d : ℂ} {u v : ℝ}
    (q : EdgeLog f z d u v) (a : ℝ) :
    (∫ t in u..v, (z+t*d-a)*(d*logDeriv f (z+t*d))) =
      (z+v*d-a)*q.value v-(z+u*d-a)*q.value u-
        d*(∫ t in u..v, q.value t) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => z+t*d-a) (u' := fun _ => d)
    (by fun_prop) q.continuous
    (fun t _ => by
      simpa using (((Complex.ofRealCLM.hasDerivAt).mul_const d).const_add z).sub_const (a:ℂ))
    q.derivative intervalIntegrable_const q.integrable
  simpa only [intervalIntegral.integral_const_mul] using h

structure BoundaryLogs (f : ℂ → ℂ) (a b u v : ℝ) where
  bottom : EdgeLog f (u*I) 1 a b
  top : EdgeLog f (v*I) 1 a b
  left : EdgeLog f a I u v
  right : EdgeLog f b I u v
  bottom_right : (bottom.value b).im = (right.value u).im
  top_right : (top.value b).im = (right.value v).im

def boundaryLog (f : ℂ → ℂ) (a b u v : ℝ) (q : BoundaryLogs f a b u v) : ℝ :=
  (∫ t in u..v, Real.log ‖f (point a t)‖)-
  (∫ t in u..v, Real.log ‖f (point b t)‖)+
  (∫ x in a..b, (q.top.value x).im)-(∫ x in a..b, (q.bottom.value x).im)

/-- Boundary conversion, before using the argument principle. -/
theorem contour_boundary (f : ℂ → ℂ) (a b u v : ℝ) (q : BoundaryLogs f a b u v) :
    (RectangleIntegral (fun s => (s-a)*logDeriv f s) (point a u) (point b v)).im =
      boundaryLog f a b u v q := by
  have hb := q.bottom.parts a
  have ht := q.top.parts a
  have hl := q.left.parts a
  have hr := q.right.parts a
  simp only [mul_one,one_mul] at hb ht
  have he : RectangleIntegral (fun s => (s-a)*logDeriv f s) (point a u) (point b v) =
      ((point b u-a)*q.bottom.value b-(point a u-a)*q.bottom.value a-
        ∫ x in a..b, q.bottom.value x)-
      ((point b v-a)*q.top.value b-(point a v-a)*q.top.value a-
        ∫ x in a..b, q.top.value x)+
      ((point b v-a)*q.right.value v-(point b u-a)*q.right.value u-
        I*(∫ t in u..v, q.right.value t))-
      ((point a v-a)*q.left.value v-(point a u-a)*q.left.value u-
        I*(∫ t in u..v, q.left.value t)) := by
    simp only [RectangleIntegral,HIntegral,VIntegral,point,add_re,ofReal_re,mul_re,
      ofReal_im,I_re,I_im,mul_zero,sub_self,add_zero,add_im,mul_im,
      mul_one,zero_add,smul_eq_mul,← intervalIntegral.integral_const_mul]
    have hhb : (∫ x in a..b, (↑x+↑u*I-↑a)*logDeriv f (↑x+↑u*I)) =
        (↑b+↑u*I-↑a)*q.bottom.value b-(↑a+↑u*I-↑a)*q.bottom.value a-
        ∫ x in a..b, q.bottom.value x := by
      simpa only [add_comm (↑u*I)] using hb
    have hht : (∫ x in a..b, (↑x+↑v*I-↑a)*logDeriv f (↑x+↑v*I)) =
        (↑b+↑v*I-↑a)*q.top.value b-(↑a+↑v*I-↑a)*q.top.value a-
        ∫ x in a..b, q.top.value x := by
      simpa only [add_comm (↑v*I)] using ht
    rw [hhb,hht]
    have hhr := hr
    have hhl := hl
    have er : (∫ t in u..v, I*((↑b+↑t*I-↑a)*logDeriv f (↑b+↑t*I))) =
        ∫ t in u..v, (↑b+↑t*I-↑a)*(I*logDeriv f (↑b+↑t*I)) := by
      apply integral_congr; intro t _; ring
    have el : (∫ t in u..v, I*((↑a+↑t*I-↑a)*logDeriv f (↑a+↑t*I))) =
        ∫ t in u..v, (↑a+↑t*I-↑a)*(I*logDeriv f (↑a+↑t*I)) := by
      apply integral_congr; intro t _; ring
    rw [er,el,hhr,hhl]
    simp only [intervalIntegral.integral_const_mul]
  have hc1 := q.bottom.real_eq a (left_mem_uIcc)
  have hc2 := q.bottom.real_eq b (right_mem_uIcc)
  have hc3 := q.top.real_eq a (left_mem_uIcc)
  have hc4 := q.top.real_eq b (right_mem_uIcc)
  have hc5 := q.left.real_eq u (left_mem_uIcc)
  have hc6 := q.left.real_eq v (right_mem_uIcc)
  have hc7 := q.right.real_eq u (left_mem_uIcc)
  have hc8 := q.right.real_eq v (right_mem_uIcc)
  simp only [mul_one] at hc1 hc2 hc3 hc4
  rw [he]
  unfold boundaryLog
  have hlr : (∫ t in u..v, q.left.value t).re =
      ∫ t in u..v, Real.log ‖f (point a t)‖ := by
    exact (Complex.reCLM.intervalIntegral_comp_comm q.left.continuous.intervalIntegrable).symm.trans
      (integral_congr (fun t ht => q.left.real_eq t ht))
  have hrr : (∫ t in u..v, q.right.value t).re =
      ∫ t in u..v, Real.log ‖f (point b t)‖ := by
    exact (Complex.reCLM.intervalIntegral_comp_comm q.right.continuous.intervalIntegrable).symm.trans
      (integral_congr (fun t ht => q.right.real_eq t ht))
  have hbi := Complex.imCLM.intervalIntegral_comp_comm (μ := volume) q.bottom.continuous.intervalIntegrable
  have hti := Complex.imCLM.intervalIntegral_comp_comm (μ := volume) q.top.continuous.intervalIntegrable
  simp only [imCLM_apply] at hbi hti
  simp only [point,add_im,sub_im,mul_im,sub_re,add_re,ofReal_re,ofReal_im,
    I_re,I_im,mul_zero,zero_mul,mul_one,zero_add,add_zero,sub_zero] at *
  rw [hlr,hrr,← hbi,← hti]
  simp only [add_comm (↑u*I),add_comm (↑v*I)] at hc1 hc2 hc3 hc4
  rw [hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,q.bottom_right,q.top_right]
  simp only [mul_I_re,ofReal_im,neg_zero]
  ring

/-- Multiplicity-weighted Littlewood identity. No principal-argument branch
or equality of the two left-hand argument endpoints is assumed. -/
theorem littlewood (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (hf : AnalyticOnNhd ℂ f (Rectangle (point a u) (point b v)))
    (hn : ∀ s ∈ RectangleBorder (point a u) (point b v), f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle (point a u) (point b v), f s = 0 ↔ s ∈ Z)
    (hsub : (Z : Set ℂ) ⊆ Rectangle (point a u) (point b v))
    (q : BoundaryLogs f a b u v) :
    2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt f s:ℝ)*(s.re-a)) = boundaryLog f a b u v q := by
  have hre : (point a u).re ≤ (point b v).re := by simpa [point] using hab
  have him : (point a u).im ≤ (point b v).im := by simpa [point] using huv
  have h := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv (g := fun s => s-a)
    hre him hf (fun s _ => analyticAt_id.sub analyticAt_const) hn Z hZ hsub
  change (1/(2*↑Real.pi*I))*RectangleIntegral (fun s => (s-a)*logDeriv f s)
    (point a u) (point b v) = _ at h
  have hp : (2*↑Real.pi*I:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have he : RectangleIntegral (fun s => (s-a)*logDeriv f s) (point a u) (point b v) =
      (2*↑Real.pi*I)*∑ s ∈ Z, (analyticOrderNatAt f s:ℂ)*(s-a) := by
    rw [← h]
    field_simp
  rw [← contour_boundary,he]
  simp [mul_im,mul_re,Complex.re_sum,Complex.im_sum]

#print axioms EdgeLog.real_eq
#print axioms EdgeLog.parts
#print axioms contour_boundary
#print axioms littlewood

end XiPrime8845.WuLittlewood

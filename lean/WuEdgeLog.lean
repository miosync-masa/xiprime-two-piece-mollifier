import WuLittlewood
import Mathlib.Topology.Order.ProjIcc

/-! Construct edge logarithms by integrating the logarithmic derivative.
No branch of the principal argument is differentiated across its cut. -/
noncomputable section
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.WuLittlewood
set_option maxHeartbeats 2000000

theorem path_log_exists (F F' : ℝ → ℂ) (u v c : ℝ) (hc : c ∈ Icc u v)
    (hd : ∀ t ∈ Icc u v, HasDerivAt F (F' t) t)
    (hdc : ContinuousOn F' (Icc u v)) (hn : ∀ t ∈ Icc u v, F t ≠ 0)
    (q0 : ℂ) (hq0 : exp q0 = F c) :
    ∃ q : ℝ → ℂ, Continuous q ∧ q c = q0 ∧
      (∀ t ∈ Icc u v, exp (q t) = F t) ∧
      (∀ t ∈ Icc u v, HasDerivAt q (F' t/F t) t) := by
  have huv : u ≤ v := hc.1.trans hc.2
  have hFc : ContinuousOn F (Icc u v) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  let h : ℝ → ℂ := fun t => F' (projIcc u v huv t)/F (projIcc u v huv t)
  have hh : Continuous h := (continuousOn_iff_continuous_domRestrict.mp (hdc.div hFc hn)).comp
    continuous_projIcc
  have he (t : ℝ) (ht : t ∈ Icc u v) : h t = F' t/F t := by
    simp [h,projIcc_of_mem huv ht]
  let q : ℝ → ℂ := fun t => q0+∫ x in c..t, h x
  have hqd (t : ℝ) : HasDerivAt q (h t) t := by
    simpa [q] using (integral_hasDerivAt_right (hh.intervalIntegrable c t)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt).const_add q0
  have hqc : Continuous q := continuous_iff_continuousAt.mpr (fun t => (hqd t).continuousAt)
  have hbase : q c = q0 := by simp [q]
  have hzero (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivAt (fun x => exp (-q x)*F x) 0 t := by
    have h1 := ((hqd t).neg.cexp).mul (hd t ht)
    apply h1.congr_deriv
    rw [he t ht]
    field_simp [hn t ht]
    ring
  refine ⟨q,hqc,hbase,?_,fun t ht => he t ht ▸ hqd t⟩
  intro t ht
  have hconst := integral_eq_sub_of_hasDerivAt
    (fun x hx => hzero x (uIcc_subset_Icc hc ht hx)) (intervalIntegrable_const (c := (0:ℂ)))
  rw [intervalIntegral.integral_zero,hbase,← hq0,← exp_add,neg_add_cancel,exp_zero] at hconst
  have hz : exp (-q t)*F t = 1 := by linear_combination -hconst
  calc
    exp (q t) = exp (q t)*(exp (-q t)*F t) := by rw [hz,mul_one]
    _ = F t := by rw [← mul_assoc,← exp_add,add_neg_cancel,exp_zero,one_mul]

theorem edgeLog_exists (f : ℂ → ℂ) (z d : ℂ) (u v c : ℝ) (hc : c ∈ Icc u v)
    (hf : ∀ t ∈ Icc u v, AnalyticAt ℂ f (z+t*d))
    (hn : ∀ t ∈ Icc u v, f (z+t*d) ≠ 0)
    (q0 : ℂ) (hq0 : exp q0 = f (z+c*d)) :
    ∃ q : EdgeLog f z d u v, q.value c = q0 := by
  have hp : Continuous (fun t : ℝ => z+t*d) := by fun_prop
  have hd (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivAt (fun t : ℝ => f (z+t*d)) (d*deriv f (z+t*d)) t := by
    simpa only [Function.comp_def,ofRealCLM_apply,ofReal_one,mul_one,smul_eq_mul,mul_comm] using (hf t ht).differentiableAt.hasDerivAt.scomp t
      ((Complex.ofRealCLM.hasDerivAt.mul_const d).const_add z)
  have hdc : ContinuousOn (fun t : ℝ => d*deriv f (z+t*d)) (Icc u v) := by
    intro t ht
    have hdf : ContinuousAt (deriv f) (z+t*d) := (hf t ht).deriv.continuousAt
    have hcomp : ContinuousAt (fun t : ℝ => deriv f (z+t*d)) t :=
      ContinuousAt.comp (f := fun t : ℝ => z+t*d) (x := t) hdf hp.continuousAt
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  obtain ⟨q,hqc,hbase,hqe,hqd⟩ := path_log_exists (fun t : ℝ => f (z+t*d))
    (fun t : ℝ => d*deriv f (z+t*d)) u v c hc hd hdc hn q0 hq0
  have huv := hc.1.trans hc.2
  have hld : ContinuousOn (fun t : ℝ => d*logDeriv f (z+t*d)) (Icc u v) := by
    have haux := hdc.div (fun t ht => (hd t ht).continuousAt.continuousWithinAt) hn
    change ContinuousOn (fun t : ℝ => (d*deriv f (z+t*d))/f (z+t*d)) (Icc u v) at haux
    simpa only [logDeriv_apply,mul_div_assoc] using haux
  refine ⟨⟨q,hqc.continuousOn,?_,?_,?_⟩,hbase⟩
  · simpa only [uIcc_of_le huv] using hqe
  · intro t ht
    have ht' : t ∈ Icc u v := ⟨by simpa only [min_eq_left huv] using ht.1.le,
      by simpa only [max_eq_right huv] using ht.2.le⟩
    simpa only [logDeriv_apply,mul_div_assoc] using hqd t ht'
  · exact (by simpa only [uIcc_of_le huv] using hld :
      ContinuousOn _ (uIcc u v)).intervalIntegrable

theorem boundaryLogs_exists (f : ℂ → ℂ) (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (hf : AnalyticOnNhd ℂ f (Rectangle (point a u) (point b v)))
    (hn : ∀ s ∈ RectangleBorder (point a u) (point b v), f s ≠ 0) :
    Nonempty (BoundaryLogs f a b u v) := by
  have hh (x y : ℝ) (hx : x ∈ Icc a b) (hy : y = u ∨ y = v) :
      point x y ∈ RectangleBorder (point a u) (point b v) := by
    rcases hy with rfl | rfl <;>
      simp [RectangleBorder,mem_reProdIm,point,uIcc_of_le hab,uIcc_of_le huv,hx]
  have hv (x y : ℝ) (hx : x = a ∨ x = b) (hy : y ∈ Icc u v) :
      point x y ∈ RectangleBorder (point a u) (point b v) := by
    rcases hx with rfl | rfl <;>
      simp [RectangleBorder,mem_reProdIm,point,uIcc_of_le hab,uIcc_of_le huv,hy]
  have ha (s : ℂ) (hs : s ∈ RectangleBorder (point a u) (point b v)) : AnalyticAt ℂ f s :=
    hf s (rectangleBorder_subset_rectangle _ _ hs)
  obtain ⟨right,hr⟩ := edgeLog_exists f b I u v u ⟨le_rfl,huv⟩
    (fun t ht => ha _ (hv b t (Or.inr rfl) ht))
    (fun t ht => hn _ (hv b t (Or.inr rfl) ht))
    (log (f (point b u))) (exp_log (hn _ (hv b u (Or.inr rfl) ⟨le_rfl,huv⟩)))
  obtain ⟨left,hl⟩ := edgeLog_exists f a I u v u ⟨le_rfl,huv⟩
    (fun t ht => ha _ (hv a t (Or.inl rfl) ht))
    (fun t ht => hn _ (hv a t (Or.inl rfl) ht))
    (log (f (point a u))) (exp_log (hn _ (hv a u (Or.inl rfl) ⟨le_rfl,huv⟩)))
  have hbottom (x : ℝ) (hx : x ∈ Icc a b) :
      u*I+(x:ℂ)*1 ∈ RectangleBorder (point a u) (point b v) := by
    simpa only [point,mul_one,add_comm (↑u*I)] using hh x u hx (Or.inl rfl)
  have htop (x : ℝ) (hx : x ∈ Icc a b) :
      v*I+(x:ℂ)*1 ∈ RectangleBorder (point a u) (point b v) := by
    simpa only [point,mul_one,add_comm (↑v*I)] using hh x v hx (Or.inr rfl)
  obtain ⟨bottom,hbottom⟩ := edgeLog_exists f (u*I) 1 a b b ⟨hab,le_rfl⟩
    (fun x hx => ha _ (hbottom x hx)) (fun x hx => hn _ (hbottom x hx))
    (right.value u) (by simpa only [mul_one,add_comm (↑u*I)] using right.exp_eq u left_mem_uIcc)
  obtain ⟨top,htop⟩ := edgeLog_exists f (v*I) 1 a b b ⟨hab,le_rfl⟩
    (fun x hx => ha _ (htop x hx)) (fun x hx => hn _ (htop x hx))
    (right.value v) (by simpa only [mul_one,add_comm (↑v*I)] using right.exp_eq v right_mem_uIcc)
  exact ⟨⟨bottom,top,left,right,congrArg Complex.im hbottom,congrArg Complex.im htop⟩⟩

/-- Abstract Littlewood from just analyticity and a zero-free boundary:
the compatible edge logarithms are constructed, not an extra premise. -/
theorem littlewood_of_boundary_nonzero (f : ℂ → ℂ) (a b u v : ℝ)
    (hab : a ≤ b) (huv : u ≤ v)
    (hf : AnalyticOnNhd ℂ f (Rectangle (point a u) (point b v)))
    (hn : ∀ s ∈ RectangleBorder (point a u) (point b v), f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle (point a u) (point b v), f s = 0 ↔ s ∈ Z)
    (hsub : (Z : Set ℂ) ⊆ Rectangle (point a u) (point b v)) :
    ∃ q : BoundaryLogs f a b u v,
      2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt f s:ℝ)*(s.re-a)) = boundaryLog f a b u v q := by
  obtain ⟨q⟩ := boundaryLogs_exists f a b u v hab huv hf hn
  exact ⟨q,littlewood f a b u v hab huv hf hn Z hZ hsub q⟩

#print axioms path_log_exists
#print axioms edgeLog_exists
#print axioms boundaryLogs_exists
#print axioms littlewood_of_boundary_nonzero
end XiPrime8845.WuLittlewood

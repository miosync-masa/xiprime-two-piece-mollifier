import PRZZFiniteContour
import PRZZHorizontalDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Infinite vertical-line identity obtained from the actual finite AFE
rectangle. Time is fixed during the truncation limit. Arithmetic-series
identification and Poisson summation are not asserted here. -/
noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
namespace XiPrime8845.PRZZInfiniteContour
open PRZZAFEDual PRZZFiniteContour
set_option maxHeartbeats 3000000

theorem vertical_continuous (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (t c : ℝ) (hc : c = -2 ∨ c = 2) :
    Continuous (fun v : ℝ => integrand a b t ((c:ℂ)+(v:ℂ)*I)) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  apply continuous_iff_continuousAt.mpr
  intro v
  have hd := PRZZContourKernel.contour_differentiable a b ((c:ℂ)+(v:ℂ)*I) t
  have hn : (c:ℂ)+(v:ℂ)*I ∉ PRZZContourKernel.poles a b t := by
    simp only [PRZZContourKernel.poles,mem_insert_iff,mem_singleton_iff,not_or]
    rcases hc with rfl | rfl <;> (repeat' constructor) <;>
      intro he <;> have hh := congrArg Complex.re he <;>
      simp [leftArg,rightArg] at hh <;> linarith
  have hp : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) := by fun_prop
  exact (hd hn).continuousAt.comp (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) hp.continuousAt

/-- Actual vertical integrability: compact continuity plus the supplied
Gaussian contour bound, with no integrability premise. -/
theorem vertical_integrable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : c = -2 ∨ c = 2) :
    Integrable (fun v : ℝ => integrand a b t ((c:ℂ)+(v:ℂ)*I)) := by
  have hcont := vertical_continuous a b ha hb t c hc
  obtain ⟨C,hC,hbound⟩ := PRZZHorizontalDecay.horizontal_bound a b ha hb hs t ht
  have hg : Integrable (fun v : ℝ => (16*C)*(v^4*Real.exp (-v^2))) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      (by norm_num : (-1:ℝ) < 4)
    norm_num [Real.rpow_natCast] at hh
    exact hh.const_mul (16*C)
  have htail : IntegrableOn (fun v : ℝ => integrand a b t ((c:ℂ)+(v:ℂ)*I))
      (Icc (-(t+2)) (t+2))ᶜ := by
    apply hg.integrableOn.mono' hcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
    have hv' : t+2 ≤ |v| := by
      simp only [mem_compl_iff,mem_Icc,not_and_or,not_le] at hv
      rcases hv with hv | hv
      · linarith [neg_le_abs v]
      · linarith [le_abs_self v]
    have hh := hbound ((c:ℂ)+(v:ℂ)*I)
      (by rcases hc with rfl | rfl <;> norm_num) (by simpa using hv')
    have hh' : ‖integrand a b t ((c:ℂ)+(v:ℂ)*I)‖ ≤
        C*(|v|+1)^4*Real.exp (-|v|^2) := by simpa [integrand] using hh
    apply hh'.trans
    calc
      _ ≤ C*(2*|v|)^4*Real.exp (-|v|^2) := by gcongr; linarith
      _ = _ := by
        rw [sq_abs,mul_pow,pow_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ v^4)]
        ring
  have hcompact : IntegrableOn (fun v : ℝ => integrand a b t ((c:ℂ)+(v:ℂ)*I))
      (Icc (-(t+2)) (t+2)) volume :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hh := integrableOn_union.mpr ⟨hcompact,htail⟩
  simpa using hh

theorem vertical_limit (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (hc : c = -2 ∨ c = 2) :
    Tendsto (fun H : ℝ => ∫ v in -H..H, integrand a b t ((c:ℂ)+(v:ℂ)*I)) atTop
      (nhds (∫ v : ℝ, integrand a b t ((c:ℂ)+(v:ℂ)*I))) :=
  intervalIntegral_tendsto_integral (vertical_integrable a b ha hb hs t ht c hc)
    tendsto_neg_atTop_atBot tendsto_id

/-- Pass the supplied finite identity to infinite height. Both horizontal
edges disappear and both vertical integrals converge absolutely. -/
theorem infinite_rectangle (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (t : ℝ) (ht : 1 ≤ t) :
    (1/(2*(Real.pi:ℂ)))*
      ((∫ v : ℝ, integrand a b t ((2:ℂ)+(v:ℂ)*I))-
       (∫ v : ℝ, integrand a b t ((-2:ℂ)+(v:ℂ)*I))) =
      ∑ p ∈ poleSet a b t, residue (integrand a b t) p := by
  let f := integrand a b t
  have hb0 : Tendsto (fun H : ℝ => HIntegral f (-2) 2 (-H)) atTop (nhds 0) := by
    simpa [f,HIntegral,integrand] using
      PRZZHorizontalDecay.horizontal_integral_tendsto a b ha hb hs t (by linarith)
        (-1) (by norm_num)
  have ht0 : Tendsto (fun H : ℝ => HIntegral f (-2) 2 H) atTop (nhds 0) := by
    simpa [f,HIntegral,integrand] using
      PRZZHorizontalDecay.horizontal_integral_tendsto a b ha hb hs t (by linarith)
        1 (by norm_num)
  have hr := (vertical_limit a b ha hb hs t (by linarith) 2 (Or.inr rfl)).const_mul I
  have hl := (vertical_limit a b ha hb hs t (by linarith) (-2) (Or.inl rfl)).const_mul I
  have hlim := (((hb0.sub ht0).add hr).sub hl).const_mul (1/(2*(Real.pi:ℂ)*I))
  have hrect : Tendsto (fun H : ℝ => RectangleIntegral' f
      ((-2:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) atTop
      (nhds ((1/(2*(Real.pi:ℂ)*I))*(I*(∫ v : ℝ, f (2+(v:ℂ)*I))-
        I*(∫ v : ℝ, f (-2+(v:ℂ)*I))))) := by
    simpa [RectangleIntegral',RectangleIntegral,VIntegral,smul_eq_mul,f] using hlim
  have hevent : (fun H : ℝ => RectangleIntegral' f
      ((-2:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) =ᶠ[atTop]
        (fun _ => ∑ p ∈ poleSet a b t, residue f p) := by
    filter_upwards [eventually_gt_atTop (t+1)] with H hH
    exact finite_rectangle a b t H ha hb hs ht hH
  have heq := tendsto_nhds_unique hrect (tendsto_const_nhds.congr' hevent.symm)
  have hscalar : (1/(2*(Real.pi:ℂ)*I))*I = 1/(2*(Real.pi:ℂ)) := by
    field_simp
  rw [← mul_sub,← mul_assoc,hscalar] at heq
  exact heq

#print axioms infinite_rectangle
#print axioms vertical_continuous
#print axioms vertical_integrable
#print axioms vertical_limit
end XiPrime8845.PRZZInfiniteContour

import PRZZDifferenceDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Infinite contour movement for the actual V-W difference. The central
singularity is removed, no Gamma pole is crossed, and all convergence
premises are supplied. Constants used for this limit may depend on time. -/
noncomputable section
open Complex Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZDifferenceContour
open PRZZDifferenceRegular PRZZDifferenceDecay
set_option maxHeartbeats 3000000

theorem vertical_continuous (a b : ℂ) (x t q c : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hx : 0 < x) (hq : 0 < q)
    (hc : c ∈ Icc (-1/8:ℝ) 2) :
    Continuous (fun v : ℝ => regular a b x t q ((c:ℂ)+(v:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hh := pole_free_strip a b x t q ha hb hx hq ((c:ℂ)+(v:ℂ)*I)
    (by change -(1/4:ℝ) < _; simp; linarith [hc.1])
  exact hh.continuousAt.comp (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) (by fun_prop)

theorem vertical_integrable (a b : ℂ) (x t q c : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (hx : 0 < x) (hq : 0 < q) (hc : c ∈ Icc (-1/8:ℝ) 2) :
    Integrable (fun v : ℝ => regular a b x t q ((c:ℂ)+(v:ℂ)*I)) := by
  have hcont := vertical_continuous a b x t q c ha hb hx hq hc
  obtain ⟨C,hC,hbound⟩ := tail_bound a b x t q ha hb hs hx hq
  have hg : Integrable (fun v : ℝ => (16*C)*(v^4*Real.exp (-v^2))) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      (by norm_num : (-1:ℝ) < 4)
    norm_num [Real.rpow_natCast] at hh
    exact hh.const_mul (16*C)
  have htail : IntegrableOn (fun v : ℝ => regular a b x t q ((c:ℂ)+(v:ℂ)*I))
      (Icc (-1:ℝ) 1)ᶜ := by
    apply hg.integrableOn.mono' hcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
    have hv' : 1 ≤ |v| := by
      simp only [mem_compl_iff,mem_Icc,not_and_or,not_le] at hv
      rcases hv with hv | hv
      · linarith [neg_le_abs v]
      · linarith [le_abs_self v]
    have hh := hbound ((c:ℂ)+(v:ℂ)*I) (by simpa using hc) (by simpa using hv')
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
      add_zero,zero_add] at hh
    apply hh.trans
    calc
      _ ≤ C*(2*|v|)^4*Real.exp (-|v|^2) := by gcongr; linarith
      _ = _ := by
        rw [sq_abs,mul_pow,pow_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ v^4)]
        ring
  have hcompact := hcont.continuousOn.integrableOn_compact
    (μ := volume) (K := Icc (-1:ℝ) 1) isCompact_Icc
  have hh := integrableOn_union.mpr ⟨hcompact,htail⟩
  simpa using hh

theorem horizontal_tendsto (a b : ℂ) (x t q c : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (hx : 0 < x) (hq : 0 < q) (hc : c ∈ Icc (-1/8:ℝ) 2)
    (e : ℝ) (he : |e| = 1) :
    Tendsto (fun H : ℝ => HIntegral (regular a b x t q) c 2 (e*H))
      atTop (nhds 0) := by
  obtain ⟨C,hC,h⟩ := tail_bound a b x t q ha hb hs hx hq
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun H => norm_nonneg _)) _
    (by simpa using PRZZHorizontalDecay.majorant_tendsto.const_mul ((2-c)*C))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with H hH
  have hH0 : 0 ≤ H := by linarith
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c) (b := 2) (C := C*(H+1)^4*Real.exp (-H^2))
    (f := fun u : ℝ => regular a b x t q ((u:ℂ)+(e*H:ℝ)*I)) (by
      intro u hu
      have hu' : u ∈ Ioc c 2 := by simpa [Set.uIoc_of_le hc.2] using hu
      have hh := h ((u:ℂ)+(e*H:ℝ)*I)
        (by simpa using (show u ∈ Icc (-1/8:ℝ) 2 from ⟨hc.1.trans hu'.1.le,hu'.2⟩))
        (by simpa [abs_mul,he,abs_of_nonneg hH0] using hH)
      simpa [abs_mul,he,abs_of_nonneg hH0] using hh)
  rw [abs_of_nonneg (sub_nonneg.mpr hc.2)] at hbnd
  simpa [HIntegral,mul_assoc,mul_comm,mul_left_comm] using hbnd

/-- Move the actual regularized difference from Re(s)=2 to any line in
[-1/8,2], including the left line. There is no assumed edge limit. -/
theorem integral_shift (a b : ℂ) (x t q c : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (hx : 0 < x) (hq : 0 < q) (hc : c ∈ Icc (-1/8:ℝ) 2) :
    (∫ v : ℝ, regular a b x t q ((2:ℂ)+(v:ℂ)*I)) =
      ∫ v : ℝ, regular a b x t q ((c:ℂ)+(v:ℂ)*I) := by
  let f := regular a b x t q
  have hb0 : Tendsto (fun H : ℝ => HIntegral f c 2 (-H)) atTop (nhds 0) := by
    simpa [f] using horizontal_tendsto a b x t q c ha hb hs hx hq hc (-1) (by norm_num)
  have ht0 : Tendsto (fun H : ℝ => HIntegral f c 2 H) atTop (nhds 0) := by
    simpa [f] using horizontal_tendsto a b x t q c ha hb hs hx hq hc 1 (by norm_num)
  have hr := (intervalIntegral_tendsto_integral
    (vertical_integrable a b x t q 2 ha hb hs hx hq (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hl := (intervalIntegral_tendsto_integral
    (vertical_integrable a b x t q c ha hb hs hx hq hc)
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hlim := ((hb0.sub ht0).add hr).sub hl
  have hrect : Tendsto (fun H : ℝ => RectangleIntegral f
      ((c:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) atTop
      (nhds (I*(∫ v : ℝ, f (2+(v:ℂ)*I))-I*(∫ v : ℝ, f ((c:ℂ)+(v:ℂ)*I)))) := by
    simpa [RectangleIntegral,VIntegral,smul_eq_mul,f] using hlim
  have hevent : (fun H : ℝ => RectangleIntegral f
      ((c:ℂ)-(H:ℂ)*I) ((2:ℂ)+(H:ℂ)*I)) =ᶠ[atTop] (fun _ => 0) := by
    apply Filter.Eventually.of_forall
    intro H
    exact finite_rectangle a b _ _ x t q ha hb hx hq
      (by simp; linarith [hc.1]) (by norm_num)
  have heq := tendsto_nhds_unique hrect (tendsto_const_nhds.congr' hevent.symm)
  apply mul_left_cancel₀ I_ne_zero
  exact sub_eq_zero.mp heq

/-- The literal V-W difference on the shifted line, with its original
normalization. In particular c=-1/8 is allowed. -/
theorem difference_shifted (a b : ℂ) (x t c : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (hx : 0 < x) (ht : 0 < t) (hc : c ∈ Icc (-1/8:ℝ) 2) :
    PRZZAFEGamma.kernel a b x t-PRZZDyadicEnvelope.sourceW (a+b) (x/(t/(2*Real.pi))) =
      (1/(2*Real.pi):ℂ)*∫ v : ℝ,
        regular a b x t (t/(2*Real.pi)) ((c:ℂ)+(v:ℂ)*I) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  rw [PRZZKernelDifference.difference_eq a b (by linarith) (by linarith)
    (by linarith) (by linarith) hs x t hx ht]
  have he : PRZZKernelDifference.errorIntegrand a b x t (t/(2*Real.pi)) =
      fun v : ℝ => regular a b x t (t/(2*Real.pi)) (2+(v:ℂ)*I) := by
    funext v
    exact (on_original_line a b x t _ v (by linarith) (by linarith)).symm
  rw [he,integral_shift a b x t (t/(2*Real.pi)) c ha hb hs hx (by positivity) hc]

#print axioms difference_shifted
#print axioms vertical_continuous
#print axioms vertical_integrable
#print axioms horizontal_tendsto
#print axioms integral_shift
end XiPrime8845.PRZZDifferenceContour

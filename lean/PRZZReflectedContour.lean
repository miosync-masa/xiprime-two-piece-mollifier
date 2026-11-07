import PRZZReflectedEnvelope
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Genuine reflected diagonal shift from Re w=-5/4 to Re w=-1/8.
The positive-coordinate kernel has no pole in the intervening strip.
Both edge disappearance and vertical integrability are supplied. -/
noncomputable section
open Complex Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZReflectedContour
open PRZZReflectedEnvelope
set_option maxHeartbeats 5000000

def majorant (v : ℝ) : ℝ := (1+|v|)^4*Real.exp (-v^2/2)

theorem majorant_integrable : Integrable majorant := by
  have h0 : Integrable (fun v : ℝ => Real.exp (-v^2/2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2) using 1
    funext v
    congr 1
    ring
  have h4 : Integrable (fun v : ℝ => v^4*Real.exp (-v^2/2)) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq (b := (1/2:ℝ)) (s := ((4:ℕ):ℝ))
      (by norm_num) (by norm_num)
    simp only [Real.rpow_natCast] at hh
    convert hh using 1
    funext v
    congr 1
    congr 1
    ring
  have hi := (h0.add h4).const_mul 16
  apply hi.mono'
  · unfold majorant; fun_prop
  · apply Filter.Eventually.of_forall
    intro v
    have hp : (1+|v|)^4 ≤ 16*(1+|v|^4) := by
      by_cases hv : |v| ≤ 1
      · have hh : (1+|v|)^4 ≤ (2:ℝ)^4 := by gcongr; linarith
        nlinarith [show 0 ≤ |v|^4 by positivity]
      · have hh : (1+|v|)^4 ≤ (2*|v|)^4 := by gcongr; linarith
        nlinarith
    have hv4 : |v|^4 = v^4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
    rw [hv4] at hp
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold majorant; positivity)]
    exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq (by dsimp only [Pi.add_apply]; ring)

theorem majorant_limit : Tendsto majorant atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun v => by unfold majorant; positivity)) _
    (by simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul 16)
  filter_upwards [eventually_ge_atTop (2:ℝ)] with v hv
  dsimp [majorant]
  rw [abs_of_nonneg (by linarith)]
  calc
    _ ≤ (2*v)^4*Real.exp (-v) := by gcongr <;> nlinarith
    _ = _ := by ring

theorem vertical_continuous (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (X c : ℝ) (hX : 0 < X) (hc : c ∈ Icc (1/8:ℝ) (5/4)) :
    Continuous (fun v : ℝ => kernel sigma X ((c:ℂ)+(v:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (analytic sigma hn X hX _ (by simp; linarith [hc.1])).continuousAt.comp
    (f := fun v : ℝ => (c:ℂ)+(v:ℂ)*I) (by fun_prop)

theorem vertical_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X c : ℝ) (hX : 0 < X) (hc : c ∈ Icc (1/8:ℝ) (5/4)) :
    Integrable (fun v : ℝ => kernel sigma X ((c:ℂ)+(v:ℂ)*I)) := by
  have hcont := vertical_continuous sigma hn X c hX hc
  obtain ⟨C,hC,hb⟩ := tail_bound sigma hs hn X hX
  have ht : IntegrableOn (fun v : ℝ => kernel sigma X ((c:ℂ)+(v:ℂ)*I)) (Icc (-1:ℝ) 1)ᶜ := by
    apply (majorant_integrable.const_mul C).integrableOn.mono' hcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
    have hv' : 1 ≤ |v| := by
      simp only [mem_compl_iff,mem_Icc,not_and_or,not_le] at hv
      rcases hv with hv | hv
      · linarith [neg_le_abs v]
      · linarith [le_abs_self v]
    simpa only [majorant,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_zero,add_zero,add_im,mul_im,mul_one,zero_add,mul_assoc] using
      hb ((c:ℂ)+(v:ℂ)*I) (by simpa using hc.1) (by simpa using hc.2) (by simpa using hv')
  have hcpt := hcont.continuousOn.integrableOn_compact (μ := volume)
    (K := Icc (-1:ℝ) 1) isCompact_Icc
  simpa using integrableOn_union.mpr ⟨hcpt,ht⟩

theorem finite_rectangle (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (X H : ℝ) (hX : 0 < X) :
    RectangleIntegral (kernel sigma X) (((1/8:ℝ):ℂ)-(H:ℂ)*I) (((5/4:ℝ):ℂ)+(H:ℂ)*I) = 0 := by
  have hh : HolomorphicOn (kernel sigma X) {s : ℂ | 1/16 < s.re} := by
    intro s hs
    exact (analytic sigma hn X hX s hs).differentiableWithinAt
  apply hh.vanishesOnRectangle
  intro s hs
  change s.re ∈ uIcc _ _ ∧ s.im ∈ uIcc _ _ at hs
  have hsre : s.re ∈ Icc (1/8:ℝ) (5/4) := by
    simpa only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_zero,add_zero,uIcc_of_le (by norm_num : (1/8:ℝ) ≤ 5/4)] using hs.1
  change 1/16 < s.re
  linarith [hsre.1]

theorem horizontal_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (e : ℝ) (he : |e| = 1) :
    Tendsto (fun H : ℝ => HIntegral (kernel sigma X) (1/8) (5/4) (e*H)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := tail_bound sigma hs hn X hX
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun H => norm_nonneg _)) _
    (by simpa using majorant_limit.const_mul ((9/8:ℝ)*C))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with H hH
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1/8:ℝ)) (b := (5/4:ℝ)) (C := C*(1+H)^4*Real.exp (-H^2/2))
    (f := fun u : ℝ => kernel sigma X ((u:ℂ)+(e*H:ℝ)*I)) (by
      intro u hu
      have hu' : u ∈ Ioc (1/8:ℝ) (5/4) := by
        simpa only [uIoc_of_le (by norm_num : (1/8:ℝ) ≤ 5/4)] using hu
      have hh := hb ((u:ℂ)+(e*H:ℝ)*I) (by simpa using hu'.1.le)
        (by simpa using hu'.2) (by simpa [abs_mul,he,abs_of_nonneg (by linarith : 0 ≤ H)] using hH)
      simpa [abs_mul,he,abs_of_nonneg (by linarith : 0 ≤ H),← sq_abs (e*H)] using hh)
  norm_num at hbnd
  simpa [HIntegral,majorant,abs_of_nonneg (by linarith : 0 ≤ H),mul_assoc,mul_comm,mul_left_comm] using hbnd

theorem integral_shift (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (∫ v : ℝ, kernel sigma X (((5/4:ℝ):ℂ)+(v:ℂ)*I)) =
      ∫ v : ℝ, kernel sigma X (((1/8:ℝ):ℂ)+(v:ℂ)*I) := by
  let f := kernel sigma X
  have hb := horizontal_limit sigma hs hn X hX (-1) (by norm_num)
  have ht := horizontal_limit sigma hs hn X hX 1 (by norm_num)
  have hr := (intervalIntegral_tendsto_integral
    (vertical_integrable sigma hs hn X (5/4) hX (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hl := (intervalIntegral_tendsto_integral
    (vertical_integrable sigma hs hn X (1/8) hX (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id).const_mul I
  have hlim := ((hb.sub ht).add hr).sub hl
  have hrect : Tendsto (fun H : ℝ => RectangleIntegral f
      (((1/8:ℝ):ℂ)-(H:ℂ)*I) (((5/4:ℝ):ℂ)+(H:ℂ)*I)) atTop
      (𝓝 (I*(∫ v : ℝ, f (((5/4:ℝ):ℂ)+(v:ℂ)*I))-
        I*(∫ v : ℝ, f (((1/8:ℝ):ℂ)+(v:ℂ)*I)))) := by
    simpa [f,RectangleIntegral,VIntegral,smul_eq_mul] using hlim
  have hevent : (fun H : ℝ => RectangleIntegral f
      (((1/8:ℝ):ℂ)-(H:ℂ)*I) (((5/4:ℝ):ℂ)+(H:ℂ)*I)) =ᶠ[atTop] (fun _ => 0) :=
    Filter.Eventually.of_forall (fun H => finite_rectangle sigma hn X H hX)
  have heq := tendsto_nhds_unique hrect (tendsto_const_nhds.congr' hevent.symm)
  exact mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp heq)

/-- The literal diagonal variable, including the imaginary-coordinate
reversal; it contributes no minus sign to the Lebesgue integral. -/
theorem reflected_shift (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (∫ v : ℝ, PRZZDiagonalMellin.integrand (-sigma) X
        (((-(5/4):ℝ):ℂ)+(v:ℂ)*I)) =
      ∫ v : ℝ, PRZZDiagonalMellin.integrand (-sigma) X
        (((-(1/8):ℝ):ℂ)+(v:ℂ)*I) := by
  have he (c : ℝ) : (∫ v : ℝ, kernel sigma X ((c:ℂ)+(v:ℂ)*I)) =
      ∫ v : ℝ, PRZZDiagonalMellin.integrand (-sigma) X (((-c:ℝ):ℂ)+(v:ℂ)*I) := by
    have hh := MeasureTheory.Measure.integral_comp_mul_left
      (fun v : ℝ => PRZZDiagonalMellin.integrand (-sigma) X (((-c:ℝ):ℂ)+(v:ℂ)*I)) (-1)
    simpa only [kernel,neg_add_rev,Complex.ofReal_neg,neg_mul,neg_one_mul,
      inv_neg,inv_one,abs_neg,abs_one,one_smul,neg_add,one_mul,add_comm] using hh
  have hh := integral_shift sigma hs hn X hX
  simpa only [he] using hh

#print axioms majorant_integrable
#print axioms majorant_limit
#print axioms vertical_continuous
#print axioms vertical_integrable
#print axioms finite_rectangle
#print axioms horizontal_limit
#print axioms integral_shift
#print axioms reflected_shift
end XiPrime8845.PRZZReflectedContour

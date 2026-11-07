import PRZZResidueEnvelope

/-! Bounds for the actual completed AFE contour on horizontal edges.
The height t and shifts are fixed before the truncation height H tends to
infinity. No residue theorem or Poisson identification is assumed. -/
noncomputable section
open Complex Filter Topology MeasureTheory Set
namespace XiPrime8845.PRZZHorizontalDecay
open PRZZAFEDual PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem horizontal_bound (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ 2 → t+2 ≤ |s.im| →
      ‖contourNumerator a b s t/s‖ ≤ C*(|s.im|+1)^4*Real.exp (-|s.im|^2) := by
  let C := Real.exp 4*(1+16/‖a+b‖^2)*324^2*‖(gammaPair a b t)⁻¹‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s hsr hsi
  let H := |s.im|
  have hH : 0 ≤ H := abs_nonneg _
  have hH1 : 1 ≤ H := by dsimp [H]; linarith
  have hsn : ‖s‖ ≤ H+2 := by
    have hh := norm_le_abs_re_add_abs_im s
    dsimp [H]; linarith
  have hsinv : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hH1.trans (abs_im_le_norm s))
  have harg (z : ℂ) (hz : ‖z‖ ≤ 1/4) (u : ℝ) (hu : |u| ≤ t) :
      ‖completedRiemannZeta (1/2+z+(u:ℂ)*I+s)‖ ≤ 324*(H+1) := by
    have hzre := abs_le.mp ((abs_re_le_norm z).trans hz)
    have hzim := (abs_im_le_norm z).trans hz
    have hsre := abs_le.mp hsr
    have him : 1 ≤ |(1/2+z+(u:ℂ)*I+s).im| := by
      have hh := abs_add_le (z.im+u+s.im) (-(z.im+u))
      have hzui := abs_add_le z.im u
      have he : z.im+u+s.im+-(z.im+u) = s.im := by ring
      rw [he,abs_neg] at hh
      simp only [add_im,div_ofNat_im,one_im,zero_div,mul_im,ofReal_re,I_im,
        ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add]
      linarith
    have hh := PRZZCompletedStrip.strip_bound (1/2+z+(u:ℂ)*I+s)
      (by simp; linarith) (by simp; linarith) him
    have hn := norm_add_le (1/2+z+(u:ℂ)*I) s
    have hn' := norm_add_le ((1/2:ℂ)+z) ((u:ℂ)*I)
    have hn'' := norm_add_le (1/2:ℂ) z
    simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      norm_div,norm_one,Complex.norm_ofNat] at hn' hn''
    dsimp [H] at *
    linarith
  have hl := harg a ha t (by simpa [abs_of_nonneg ht])
  have hr := harg b hb (-t) (by simp [abs_of_nonneg ht])
  have hl' : ‖completedRiemannZeta (leftArg a t+s)‖ ≤ 324*(H+1) := hl
  have hr' : ‖completedRiemannZeta (rightArg b t+s)‖ ≤ 324*(H+1) := by
    simpa [rightArg,sub_eq_add_neg] using hr
  have he : ‖exp (s^2)‖ ≤ Real.exp 4*Real.exp (-H^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := abs_le.mp hsr
    simp only [pow_two,mul_re]
    dsimp [H]
    nlinarith [sq_abs s.im]
  have han := annihilator_bound (a+b) s 1 ‖a+b‖ (by norm_num)
    (norm_pos_iff.mpr hs) (by simp)
  have han' : ‖annihilator (a+b) s‖ ≤ (1+16/‖a+b‖^2)*(H+1)^2 := by
    have hn : ‖s‖ ≤ 2*(H+1) := by linarith
    have hpow : (1:ℝ) ≤ (H+1)^2 := by nlinarith
    apply han.trans
    rw [div_pow,one_pow]
    simp only [mul_one_div]
    calc
      _ ≤ 1+4*(2*(H+1))^2/‖a+b‖^2 := by gcongr
      _ ≤ _ := by
        calc
          _ = 1+(16/‖a+b‖^2)*(H+1)^2 := by ring
          _ ≤ (H+1)^2+(16/‖a+b‖^2)*(H+1)^2 := add_le_add hpow le_rfl
          _ = _ := by ring
  have hid : contourNumerator a b s t/s = exp (s^2)*annihilator (a+b) s*
      (completedRiemannZeta (leftArg a t+s)*completedRiemannZeta (rightArg b t+s))*
      (gammaPair a b t)⁻¹*s⁻¹ := by unfold contourNumerator completedPair; ring
  rw [hid]
  simp only [norm_mul]
  calc
    _ ≤ (Real.exp 4*Real.exp (-H^2))*((1+16/‖a+b‖^2)*(H+1)^2)*
        ((324*(H+1))*(324*(H+1)))*‖(gammaPair a b t)⁻¹‖*1 := by gcongr
    _ = _ := by dsimp [C,H]; ring

/-- The supplied horizontal majorant vanishes at infinite truncation. -/
theorem majorant_tendsto : Tendsto (fun H : ℝ => (H+1)^4*Real.exp (-H^2))
    atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun H => by positivity))
    ((eventually_ge_atTop (1:ℝ)).mono (fun H hH => ?_))
    (by simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul 16)
  calc
    _ ≤ (2*H)^4*Real.exp (-H) := by
      gcongr
      · linarith
      · nlinarith
    _ = 16*(H^4*Real.exp (-H)) := by ring

/-- Both horizontal sides of the actual completed contour disappear.
The sign is selected before the limiting truncation height; the integral
is oriented left to right (the upper contour side uses its negative). -/
theorem horizontal_integral_tendsto (a b : ℂ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (e : ℝ) (he : |e| = 1) :
    Tendsto (fun H : ℝ => ∫ u in (-2:ℝ)..2,
      contourNumerator a b ((u:ℂ)+(e*H:ℝ)*I) t/((u:ℂ)+(e*H:ℝ)*I))
      atTop (nhds 0) := by
  obtain ⟨C,hC,h⟩ := horizontal_bound a b ha hb hs t ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun H => norm_nonneg _)) _
    (by simpa using majorant_tendsto.const_mul (4*C))
  filter_upwards [eventually_ge_atTop (t+2)] with H hH
  have hH0 : 0 ≤ H := by linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-2:ℝ)) (b := 2) (C := C*(H+1)^4*Real.exp (-H^2))
    (f := fun u : ℝ => contourNumerator a b ((u:ℂ)+(e*H:ℝ)*I) t/
      ((u:ℂ)+(e*H:ℝ)*I)) (by
        intro u hu
        have hu' : u ∈ Set.Ioc (-2:ℝ) 2 := by simpa using hu
        have hh := h ((u:ℂ)+(e*H:ℝ)*I)
          (by simpa using (abs_le.mpr ⟨hu'.1.le,hu'.2⟩))
          (by simpa [abs_mul,he,abs_of_nonneg hH0] using hH)
        simpa [abs_mul,he,abs_of_nonneg hH0] using hh)
  norm_num at hbound
  simpa only [Complex.ofReal_mul,mul_assoc,mul_comm,mul_left_comm] using hbound

#print axioms horizontal_integral_tendsto
#print axioms majorant_tendsto
#print axioms horizontal_bound
end XiPrime8845.PRZZHorizontalDecay

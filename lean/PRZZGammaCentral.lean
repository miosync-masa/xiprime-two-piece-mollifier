import PRZZGammaPath

/-! Quantitative logarithm comparison along slit-plane segments.
The branch condition is retained, not inferred from a formal log identity. -/
noncomputable section
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.PRZZGammaCentral
set_option maxHeartbeats 2000000

theorem log_segment_bound (z d : ℂ) (M : ℝ) (hM : 0 < M)
    (hs : ∀ u ∈ Icc (0:ℝ) 1, z+(u:ℂ)*d ∈ slitPlane)
    (hn : ∀ u ∈ Icc (0:ℝ) 1, M ≤ ‖z+(u:ℂ)*d‖) :
    ‖log (z+d)-log z‖ ≤ ‖d‖/M := by
  have hp : Continuous (fun u : ℝ => z+(u:ℂ)*d) := by fun_prop
  have hz : ∀ u ∈ Icc (0:ℝ) 1, z+(u:ℂ)*d ≠ 0 := fun u hu =>
    norm_pos_iff.mp (hM.trans_le (hn u hu))
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => log (z+(u:ℂ)*d)) (d/(z+(u:ℂ)*d)) u := by
    simpa using ((((hasDerivAt_id u).ofReal_comp).mul_const d).const_add z).clog_real (hs u hu)
  have hc : ContinuousOn (fun u : ℝ => log (z+(u:ℂ)*d)) (Icc 0 1) :=
    fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hi : ContinuousOn (fun u : ℝ => d/(z+(u:ℂ)*d)) (Icc 0 1) :=
    continuousOn_const.div hp.continuousOn hz
  have he := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1) hc
    (fun u hu => hd u ⟨hu.1.le,hu.2.le⟩) (hi.intervalIntegrable_of_Icc (by norm_num))
  simp only [ofReal_one,ofReal_zero,one_mul,zero_mul,add_zero] at he
  rw [← he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ => d/(z+(u:ℂ)*d)) (a := (0:ℝ)) (b := 1) (C := ‖d‖/M) (fun u hu => by
    have hu' : u ∈ Icc (0:ℝ) 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),mem_Ioc] at hu
      exact ⟨hu.1.le,hu.2⟩
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hM (hn u hu'))
  simpa only [sub_zero,abs_one,mul_one] using hb

#print axioms log_segment_bound

/-- The main logarithm can be frozen at a reference point. Both path
conditions are geometric, not assumed estimates on the Gamma quotient. -/
theorem ratio_reference_error (T M : ℝ) (z d w : ℂ) (hT : 2 ≤ T) (hM : 0 < M)
    (hr : ∀ u ∈ Icc (0:ℝ) 1, 0 < (z+(u:ℂ)*d).re)
    (hi : ∀ u ∈ Icc (0:ℝ) 1, T/4 ≤ |(z+(u:ℂ)*d).im|)
    (hs : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      w+(v:ℂ)*(z+(u:ℂ)*d-w) ∈ slitPlane)
    (hn : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      M ≤ ‖w+(v:ℂ)*(z+(u:ℂ)*d-w)‖) :
    ∃ E : ℂ, ‖E‖ ≤ ‖d‖*(50/T+(‖z-w‖+‖d‖)/M) ∧
      Gamma (z+d)/Gamma z = exp (d*log w+E) := by
  obtain ⟨E,hE,he⟩ := PRZZGammaPath.ratio_with_error T z d hT hr hi
  have hp : Continuous (fun u : ℝ => z+(u:ℂ)*d) := by fun_prop
  have hl : ContinuousOn (fun u : ℝ => d*log (z+(u:ℂ)*d)) (Icc 0 1) := by
    intro u hu
    exact (continuousAt_const.mul ((Complex.hasDerivAt_log
      (mem_slitPlane_iff.mpr (Or.inl (hr u hu)))).continuousAt.comp
        (x := u) hp.continuousAt)).continuousWithinAt
  have hb : ∀ u ∈ Icc (0:ℝ) 1,
      ‖d*(log (z+(u:ℂ)*d)-log w)‖ ≤ ‖d‖*((‖z-w‖+‖d‖)/M) := by
    intro u hu
    have hh := log_segment_bound w (z+(u:ℂ)*d-w) M hM (hs u hu) (hn u hu)
    rw [add_sub_cancel] at hh
    have huN : ‖(u:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1] using hu.2
    have hz : ‖z+(u:ℂ)*d-w‖ ≤ ‖z-w‖+‖d‖ := by
      calc
        _ = ‖(z-w)+(u:ℂ)*d‖ := by congr 1; ring
        _ ≤ ‖z-w‖+‖(u:ℂ)*d‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; nlinarith [norm_nonneg d]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hh.trans (div_le_div_of_nonneg_right hz hM.le)) (norm_nonneg d)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (fun u hu => hb u (by
      simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),mem_Ioc] at hu
      exact ⟨hu.1.le,hu.2⟩))
  have hid : (∫ u in (0:ℝ)..1, d*(log (z+(u:ℂ)*d)-log w)) =
      (∫ u in (0:ℝ)..1, d*log (z+(u:ℂ)*d))-d*log w := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hl.intervalIntegrable_of_Icc (by norm_num))
      intervalIntegrable_const]
    simp
  rw [hid] at hb'
  simp only [sub_zero,abs_one,mul_one] at hb'
  refine ⟨((∫ u in (0:ℝ)..1, d*log (z+(u:ℂ)*d))-d*log w)+E, ?_, ?_⟩
  · exact (norm_add_le _ _).trans ((add_le_add hb' hE).trans_eq (by ring))
  · rw [he]; congr 1; ring

/-- Uniform small shifts: the threshold depends only on the fixed cap S.
No constant is chosen after the individual shifts or the height. -/
theorem log_scaled_shift_bound (S L : ℝ) (A : ℂ) (hL : 0 < L)
    (hA : ‖A‖ ≤ S) (hSL : 4*S ≤ L) :
    ‖A/(L:ℂ)‖ ≤ 1/4 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ hL).mpr
  linarith

#print axioms ratio_reference_error
#print axioms log_scaled_shift_bound

/-- A single eventual threshold works for the whole bounded shift family. -/
theorem log_scaled_shifts_eventually (S : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ‖A/(Real.log T:ℂ)‖ ≤ 1/4 ∧ ‖B/(Real.log T:ℂ)‖ ≤ 1/4 := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (Filter.eventually_gt_atTop (max (4*S) 0))] with T hT
  have hL : 0 < Real.log T := lt_of_le_of_lt (le_max_right _ _) hT
  have hSL : 4*S ≤ Real.log T := (le_max_left _ _).trans hT.le
  intro A B hA hB
  exact ⟨log_scaled_shift_bound S _ A hL hA hSL,
    log_scaled_shift_bound S _ B hL hB hSL⟩

#print axioms log_scaled_shifts_eventually

/-- An explicit central-region geometry supplier, valid in either half
plane. The reference logarithm and its perturbation use the same branch. -/
theorem log_vertical_reference (T : ℝ) (w d : ℂ) (hT : 0 < T)
    (hw : T/2 ≤ |w.im|) (hd : |d.im| ≤ T/4) :
    ‖log (w+d)-log w‖ ≤ 4*‖d‖/T := by
  have hi (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      T/4 ≤ |(w+(u:ℂ)*d).im| := by
    have hd' : |u*d.im| ≤ T/4 := by
      rw [abs_mul,abs_of_nonneg hu.1]
      nlinarith [abs_nonneg d.im,hu.1,hu.2]
    have hh := abs_add_le (w.im+u*d.im) (-(u*d.im))
    simp only [add_neg_cancel_right,abs_neg] at hh
    simp only [add_im,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero]
    linarith
  have hs (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : w+(u:ℂ)*d ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    exact abs_pos.mp (lt_of_lt_of_le (by linarith : 0 < T/4) (hi u hu))
  have hn (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : T/4 ≤ ‖w+(u:ℂ)*d‖ :=
    (hi u hu).trans (Complex.abs_im_le_norm _)
  exact (log_segment_bound w d (T/4) (by linarith) hs hn).trans_eq (by ring)

#print axioms log_vertical_reference

/-- Actual Gamma-path logarithm, with an absolute constant for every shift
of norm at most 1/4. Signed t covers both Gamma factors. -/
theorem actual_log_comparison (T t u : ℝ) (a s : ℂ) (hT : 2 ≤ T)
    (ht : T ≤ |t|) (hu : u ∈ Icc (0:ℝ) 1) (ha : ‖a‖ ≤ 1/4)
    (hs : |s.im| ≤ T/4) :
    ‖log ((1/2+a+(u:ℂ)*s+(t:ℂ)*I)/2)-log ((t:ℂ)*I/2)‖ ≤
      2*(1+‖s‖)/T := by
  let d : ℂ := (1/2+a+(u:ℂ)*s)/2
  have ha' : |a.im| ≤ 1/4 := (Complex.abs_im_le_norm a).trans ha
  have hus : |u*s.im| ≤ T/4 := by
    rw [abs_mul,abs_of_nonneg hu.1]
    nlinarith [abs_nonneg s.im,hu.1,hu.2]
  have hd : |d.im| ≤ T/4 := by
    have hh := abs_add_le a.im (u*s.im)
    dsimp [d]
    simp only [div_ofNat_im,add_im,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero]
    norm_num
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hw : T/2 ≤ |((t:ℂ)*I/2).im| := by
    simp only [div_ofNat_im,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hh := log_vertical_reference T ((t:ℂ)*I/2) d (by linarith) hw hd
  have hdn : ‖d‖ ≤ (1+‖s‖)/2 := by
    have huN : ‖(u:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1] using hu.2
    have h1 := norm_add_le (1/2+a) ((u:ℂ)*s)
    have h2 := norm_add_le (1/2:ℂ) a
    norm_num only [norm_div, norm_one, Complex.norm_ofNat] at h2
    rw [norm_mul] at h1
    dsimp [d]
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    nlinarith [norm_nonneg s]
  have he : (t:ℂ)*I/2+d = (1/2+a+(u:ℂ)*s+(t:ℂ)*I)/2 := by dsimp [d]; ring
  rw [he] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
  linarith

#print axioms actual_log_comparison
end XiPrime8845.PRZZGammaCentral

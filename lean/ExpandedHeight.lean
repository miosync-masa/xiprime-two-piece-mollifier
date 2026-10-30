import ExpandedGcd
import HeightScaling

/-! Fixed expanded-support height limits. Constants are independent of shifts,
but may depend on the fixed weight. No rescaling of the arithmetic height. -/
noncomputable section
open Filter Topology MeasureTheory Complex
namespace XiPrime8845.ExpandedHeight
open ExpandedGcd
open HeightScaling (phase phase_exact)

def logCap : ℝ :=
  |Real.log (2*Real.pi)| + |Real.log (1/2:ℝ)| + |Real.log (5/2:ℝ)|

theorem logCap_nonneg : 0 ≤ logCap := by unfold logCap; positivity

theorem log_height_bound (u : ℝ) (hu : u ∈ Set.Icc (1/2 : ℝ) (5/2)) :
    |Real.log (2*Real.pi/u)| ≤ logCap := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hlo := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hu.1
  have hhi := Real.log_le_log hu0 hu.2
  have hb : |Real.log u| ≤ |Real.log (1/2:ℝ)| + |Real.log (5/2:ℝ)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log (1/2:ℝ)), abs_nonneg (Real.log (5/2:ℝ))]
    · linarith [le_abs_self (Real.log (5/2:ℝ)), abs_nonneg (Real.log (1/2:ℝ))]
  rw [Real.log_div (by positivity) hu0.ne']
  exact (abs_sub _ _).trans (by dsimp [logCap]; linarith)

theorem phase_error_bound (T u bound : ℝ) (s : ℂ) (hT : 1 < T)
    (hu : u ∈ Set.Icc (1/2 : ℝ) (5/2)) (hs : ‖s‖ ≤ bound)
    (hsmall : bound * logCap / Real.log T ≤ 1) :
    ‖phase T u s - Complex.exp (-s)‖ ≤
      Real.exp bound * (2 * (bound * logCap / Real.log T)) := by
  have hL : 0 < Real.log T := Real.log_pos hT
  have hb : 0 ≤ bound := (norm_nonneg s).trans hs
  have hz : ‖s * (Real.log (2*Real.pi/u) : ℂ) / (Real.log T : ℂ)‖ ≤
      bound * logCap / Real.log T := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (mul_le_mul hs (log_height_bound u hu)
      (abs_nonneg _) hb) hL.le
  rw [phase_exact T u hT (by linarith [hu.1]) s, ← mul_sub_one, norm_mul]
  apply mul_le_mul
  · exact (Complex.norm_exp_le_exp_norm (-s)).trans (Real.exp_le_exp.mpr (by simpa using hs))
  · exact (Complex.norm_exp_sub_one_le (hz.trans hsmall)).trans (by linarith)
  · exact norm_nonneg _
  · exact (Real.exp_pos _).le

theorem phase_uniform (bound : ℝ) :
    TendstoUniformlyOn (fun (T : ℝ) (p : ℝ × ℂ) => phase T p.1 p.2)
      (fun p => Complex.exp (-p.2)) atTop
      {p | p.1 ∈ Set.Icc (1/2 : ℝ) (5/2) ∧ ‖p.2‖ ≤ bound} := by
  have hinv : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall : Tendsto (fun T : ℝ => bound * logCap / Real.log T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (bound * logCap)
  have herr : Tendsto (fun T : ℝ => Real.exp bound * (2*(bound*logCap/Real.log T)))
      atTop (nhds 0) := by simpa using (hsmall.const_mul 2).const_mul (Real.exp bound)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    herr.eventually (gt_mem_nhds heps)] with T hT hsmallT herrT
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (phase_error_bound T p.1 bound p.2 hT hp.1 hp.2 hsmallT.le).trans_lt herrT

theorem rescale_integral (f : ℝ → ℂ) (T : ℝ) (hT : 0 < T) :
    (∫ t in Set.Icc (T/2) (5/2*T), f t) / (T : ℂ) =
      ∫ u in Set.Icc (1/2 : ℝ) (5/2), f (T*u) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : T/2 ≤ 5/2*T),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 5/2)]
  have h := intervalIntegral.integral_comp_mul_left (a := (1/2:ℝ)) (b := (5/2:ℝ)) f hT.ne'
  simp only [Complex.real_smul, Complex.ofReal_inv] at h
  rw [show T*(1/2) = T/2 by ring, show T*(5/2) = 5/2*T by ring] at h
  rw [h]
  ring

theorem mass_rescale (Phi : ℝ → ℝ) (T : ℝ) (hT : 0 < T) :
    mass Phi T / (T : ℂ) = ∫ u in Set.Icc (1/2 : ℝ) (5/2), (Phi u : ℂ) := by
  rw [mass, rescale_integral _ T hT]
  simp only [mul_div_cancel_left₀ _ hT.ne']

theorem heightFactor_rescale (Phi : ℝ → ℝ) (T : ℝ) (hT : 1 < T) (s : ℂ) :
    heightFactor Phi T (s/(Real.log T : ℂ)) / (T : ℂ) =
      ∫ u in Set.Icc (1/2 : ℝ) (5/2), phase T u s * (Phi u : ℂ) := by
  rw [heightFactor, rescale_integral _ T (by linarith)]
  simp only [phase, mul_div_cancel_left₀ _ (ne_of_gt (show 0 < T by linarith))]

theorem phase_continuousOn (T : ℝ) (hT : 1 < T) (s : ℂ) :
    ContinuousOn (fun u => phase T u s) (Set.Icc (1/2 : ℝ) (5/2)) := by
  apply ContinuousOn.congr _ (fun u hu => phase_exact T u hT (by linarith [hu.1]) s)
  apply continuousOn_const.mul
  apply ContinuousOn.cexp
  apply ContinuousOn.div_const
  apply continuousOn_const.mul
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.log
  · exact continuousOn_const.div continuousOn_id (fun u hu => by linarith [hu.1])
  · intro u hu
    exact (div_pos (by positivity) (by linarith [hu.1])).ne'

theorem heightFactor_error_bound (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi)
    (T bound C : ℝ) (s : ℂ) (hT : 1 < T) (hs : ‖s‖ ≤ bound)
    (hPhiC : ∀ u ∈ Set.Icc (1/2 : ℝ) (5/2), ‖(Phi u : ℂ)‖ ≤ C)
    (hsmall : bound*logCap/Real.log T ≤ 1) :
    ‖heightFactor Phi T (s/(Real.log T : ℂ))/(T : ℂ) -
      Complex.exp (-s) * (∫ u in Set.Icc (1/2 : ℝ) (5/2), (Phi u : ℂ))‖ ≤
      Real.exp bound * (2*(bound*logCap/Real.log T)) * C * 2 := by
  have hc : Continuous (fun u => (Phi u : ℂ)) :=
    Complex.continuous_ofReal.comp hPhi.1.continuous
  have hi : IntegrableOn (fun u => phase T u s * (Phi u : ℂ)) (Set.Icc (1/2 : ℝ) (5/2)) :=
    ((phase_continuousOn T hT s).mul hc.continuousOn).integrableOn_compact isCompact_Icc
  have hj : IntegrableOn (fun u => Complex.exp (-s) * (Phi u : ℂ)) (Set.Icc (1/2 : ℝ) (5/2)) :=
    (hc.continuousOn.integrableOn_compact isCompact_Icc).const_mul (Complex.exp (-s))
  rw [heightFactor_rescale Phi T hT s, ← integral_const_mul, ← integral_sub hi hj]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Icc (1/2 : ℝ) (5/2)) (by simp) (fun u hu => show
      ‖phase T u s * (Phi u : ℂ) - Complex.exp (-s) * (Phi u : ℂ)‖ ≤
        Real.exp bound * (2*(bound*logCap/Real.log T)) * C from by
      rw [← sub_mul, norm_mul]
      apply mul_le_mul (phase_error_bound T u bound s hT hu hs hsmall) (hPhiC u hu)
        (norm_nonneg _)
      have hb := (norm_nonneg s).trans hs
      have hl := (Real.log_pos hT).le
      have hc := logCap_nonneg
      positivity)
  norm_num at h
  simpa only [mul_comm] using h

/-- The actual normalized height integral, uniformly in a bounded complex shift.
SmoothWeight supplies the bounded real weight; no positivity of Phi is used. -/
theorem heightFactor_uniform (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (bound : ℝ) :
    TendstoUniformlyOn
      (fun T s => heightFactor Phi T (s/(Real.log T : ℂ))/(T : ℂ))
      (fun s => Complex.exp (-s) * (∫ u in Set.Icc (1/2 : ℝ) (5/2), (Phi u : ℂ)))
      atTop {s : ℂ | ‖s‖ ≤ bound} := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (K := Set.Icc (1/2 : ℝ) (5/2)) (hPhi.1.continuous.norm.continuousOn)
  have hPhiC : ∀ u ∈ Set.Icc (1/2 : ℝ) (5/2), ‖(Phi u : ℂ)‖ ≤ C := by
    intro u hu
    simpa only [Complex.norm_real] using hC ⟨u, hu, rfl⟩
  have hinv : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall : Tendsto (fun T : ℝ => bound*logCap/Real.log T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (bound*logCap)
  have herr : Tendsto (fun T : ℝ => Real.exp bound*(2*(bound*logCap/Real.log T))*C*2)
      atTop (nhds 0) := by simpa using (((hsmall.const_mul 2).const_mul (Real.exp bound)).mul_const C).mul_const 2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    herr.eventually (gt_mem_nhds heps)] with T hT hs he
  intro s hs'
  rw [dist_comm, dist_eq_norm]
  exact (heightFactor_error_bound Phi hPhi T bound C s hT hs' hPhiC hs.le).trans_lt he


theorem mass_full (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (T : ℝ) (hT : 0 < T) :
    mass Phi T/(T:ℂ) = (PRZZLocalization.fullMass Phi:ℂ) := by
  rw [mass_rescale Phi T hT, PRZZLocalization.fullMass_eq hPhi]
  exact integral_complex_ofReal

#print axioms log_height_bound
#print axioms phase_error_bound
#print axioms rescale_integral
#print axioms mass_full
#print axioms heightFactor_uniform
end XiPrime8845.ExpandedHeight


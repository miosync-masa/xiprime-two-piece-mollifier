import PRZZZeroReciprocalRows
import PRZZCosineMovingWindow

/-! Remove the time-dependent reciprocal endpoints in an actual zero
row. Absolute integrability is used only after time integration or on
finite spatial windows. The conditional fixed-time kernel is never
silently assigned a Bochner integral. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroRowMellin
open PRZZZeroReciprocalRows PRZZZeroReciprocal PRZZCosineMovingWindow PRZZCosineMellin
set_option maxHeartbeats 6000000

def value (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta t : ℝ) : ℂ :=
  (Phi (t/T)*exp (-sigma*(Real.log (t*delta/u):ℂ)))*
    (-((1/(2*Real.pi):ℂ)*∫ tau : ℝ,
      evaluated sigma ((2*Real.pi*u/t)*(t*delta/u)^2) tau))

theorem row_measurable (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    AEStronglyMeasurable (row Phi T u sigma delta) (volume.restrict (Ioi (0:ℝ))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => integrand Phi T u sigma delta p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc T (2*T)))) := by
    rw [Measure.prod_restrict]
    exact (positive_continuous Phi hPhi T u sigma delta hT hu hs).aestronglyMeasurable
      (measurableSet_Ioi.prod measurableSet_Icc)
  simpa only [← time_window Phi hsPhi T u sigma delta _ hT] using hm.integral_prod_right'

theorem row_integrable (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (hd : 0 < delta) :
    IntegrableOn (row Phi T u sigma delta) (Ioi (0:ℝ)) := by
  obtain ⟨B,hB,hb⟩ := PRZZZeroGap.core_envelope Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  apply (PRZZZeroGap.envelope_integrable.const_mul (B/delta^2)).mono'
    (row_measurable Phi hPhi.continuous hsPhi T u sigma delta hT hu hs)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have he : PRZZZeroGap.core Phi T u sigma delta x+PRZZZeroGap.core Phi T u sigma (-delta) x =
      2*row Phi T u sigma delta x := by
    simpa only [row,mul_assoc] using PRZZZeroCosine.core_cosine Phi hPhi hsPhi T u delta x sigma hT hu hx hs
  have hp := hb delta x hd.ne' hx
  have hm := hb (-delta) x (neg_ne_zero.mpr hd.ne') hx
  simp only [abs_neg,abs_of_pos hd] at hp hm
  have hh := norm_add_le (PRZZZeroGap.core Phi T u sigma delta x) (PRZZZeroGap.core Phi T u sigma (-delta) x)
  rw [he,norm_mul,Complex.norm_ofNat] at hh
  have hh' : ‖row Phi T u sigma delta x‖ ≤ B*PRZZZeroGap.envelope x/delta^2 := by linarith
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh'

theorem scale (t u delta : ℝ) (ht : 0 < t) (hu : 0 < u) :
    (2*Real.pi*u/t)*(t*delta/u)^2 = (2*Real.pi*delta^2/u)*t := by
  field_simp

/-- One actual positive-gap row, including its original time cutoff. -/
theorem actual_row (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (hd : 0 < delta) :
    (∫ x in Ioi (0:ℝ), row Phi T u sigma delta x) =
      ∫ t in Icc T (2*T), value Phi T u sigma delta t := by
  let A := (2*Real.pi*delta^2/u)*T
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨C,hC,hbound⟩ := interval_uniform sigma hs hn A hA
  let B := fun t : ℝ => C*‖Phi (t/T)*exp (-sigma*(Real.log (t*delta/u):ℂ))‖
  have hB : IntegrableOn B (Icc T (2*T)) := by
    have hPhic := hPhi.continuous
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro t ht
    have ht0 : 0 < t := hT.trans_le ht.1
    have hlog : ContinuousAt (fun t : ℝ => Real.log (t*delta/u)) t := by
      have hp : t*delta/u ≠ 0 := ne_of_gt (by positivity)
      fun_prop
    have hlogc := Complex.continuous_ofReal.continuousAt.comp hlog
    have hTc := hT.ne'
    dsimp [B]
    apply ContinuousAt.continuousWithinAt
    fun_prop
  let f := fun (R t : ℝ) => ∫ x in (1/R)..R, integrand Phi T u sigma delta x t
  have hfinite (R t : ℝ) (hR : 1 ≤ R) (ht : t ∈ Icc T (2*T)) :
      f R t = (Phi (t/T)*exp (-sigma*(Real.log (t*delta/u):ℂ)))*
        ∫ y in ((t*delta/u)/R)..((t*delta/u)*R),
          PRZZCosineSpatialJets.primitive (sigma-1) sigma ((2*Real.pi*u/t)*(t*delta/u)^2) y*cos (y:ℂ) := by
    have ht0 : 0 < t := hT.trans_le ht.1
    have hR0 : 0 < R := by linarith
    dsimp [f,integrand]
    rw [intervalIntegral.integral_const_mul,
      finite_substitution sigma hs _ _ (1/R) R (by positivity) (by positivity) (by positivity)
        ((div_le_iff₀ hR0).mpr (by nlinarith))]
    simp only [one_div,div_inv_eq_mul]
    ring
  have hlim : Tendsto (fun R : ℝ => ∫ t in Icc T (2*T), f R t) atTop
      (𝓝 (∫ t in Icc T (2*T), value Phi T u sigma delta t)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      have hi := (finite_joint_integrable Phi hPhi.continuous T u (1/R) R sigma delta hT hu
        (by positivity) hs).integral_prod_right
      have hRR : 1/R ≤ R := (div_le_iff₀ (show 0 < R by linarith)).mpr (by nlinarith)
      simpa only [f,intervalIntegral.integral_of_le hRR] using
        hi.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [hfinite R t hR ht,norm_mul]
      have ht0 : 0 < t := hT.trans_le ht.1
      have hR0 : 0 < R := by linarith
      have ho : 0 < t*delta/u := by positivity
      have hX : A ≤ (2*Real.pi*u/t)*(t*delta/u)^2 := by
        rw [scale t u delta ht0 hu]
        dsimp [A]
        gcongr
        exact ht.1
      have hb := hbound _ ((t*delta/u)/R) ((t*delta/u)*R) hX (div_pos ho hR0)
        ((div_le_iff₀ hR0).mpr (by
          have hh := mul_le_mul_of_nonneg_left (show 1 ≤ R*R by nlinarith) ho.le
          nlinarith only [hh]))
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by dsimp [B]; ring)
    · exact hB
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : 0 < t := hT.trans_le ht.1
      have hh := (scaled_improper sigma hs hn ((2*Real.pi*u/t)*(t*delta/u)^2) (t*delta/u)
        (by positivity) (by positivity)).const_mul (Phi (t/T)*exp (-sigma*(Real.log (t*delta/u):ℂ)))
      apply hh.congr'
      filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      exact (hfinite R t hR ht).symm
  have hactual := PRZZCosineSpatialImproper.integral_window_limit _
    (row_integrable Phi hPhi hcPhi hsPhi T u sigma delta hT hu hs hn hd)
  apply tendsto_nhds_unique hactual
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  exact (finite_time_exchange Phi hPhi.continuous hsPhi T u (1/R) R sigma delta hT hu
    (by positivity) ((div_le_iff₀ hR0).mpr (by nlinarith)) hs).symm

#print axioms row_measurable
#print axioms row_integrable
#print axioms scale
#print axioms actual_row
end XiPrime8845.PRZZZeroRowMellin

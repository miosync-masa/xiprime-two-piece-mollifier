import PRZZCosineDerivativeMellin
import PRZZCosineTimeDomination

/-! Apply the actual second-derivative Mellin identity under a weighted
time integral. Positive compact time intervals supply a common scale
lower bound; the second spatial cutoff is removed under that integral.
This does not assert the separate reciprocal-variable change for the
original time-first zero-frequency field. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineTimeMellin
open PRZZCosineSpatialJets PRZZCosineMellin PRZZCosineDerivativeMellin PRZZCosineTimeDomination
open PRZZCosineMellinCore
set_option maxHeartbeats 6000000

theorem evaluated_scale (sigma : ℂ) (X tau : ℝ) (hX : 0 < X) :
    evaluated sigma X tau = exp (-(line tau)*(Real.log X:ℂ))*evaluated sigma 1 tau := by
  unfold evaluated coefficient
  rw [cpow_def_of_ne_zero (by exact_mod_cast hX.ne'),← Complex.ofReal_log hX.le]
  simp only [Complex.ofReal_one,one_cpow]
  rw [mul_comm (Real.log X:ℂ) (-line tau)]
  ring

theorem time_mellin_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    Integrable (fun p : ℝ × ℝ => Phi p.1*evaluated sigma (k*p.1) p.2)
      ((volume.restrict (Icc T U)).prod volume) := by
  have hi := evaluated_integrable sigma hs hn 1 (by norm_num)
  let D := (k*T)^(-5/4:ℝ)
  have ht : IntegrableOn (fun t : ℝ => ‖Phi t‖*D) (Icc T U) :=
    hPhi.norm.continuousOn.integrableOn_Icc.mul_const D
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Phi p.1*exp (-(line p.2)*(Real.log (k*p.1):ℂ))*evaluated sigma 1 p.2)
      ((volume.restrict (Icc T U)).prod volume) := by
    have he : AEStronglyMeasurable (fun p : ℝ × ℝ => evaluated sigma 1 p.2)
        ((volume.restrict (Icc T U)).prod volume) :=
      hi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hc : Measurable (fun p : ℝ × ℝ => Phi p.1*exp (-(line p.2)*(Real.log (k*p.1):ℂ))) := by
      have hp := hPhi.measurable
      unfold line
      fun_prop
    exact hc.aestronglyMeasurable.mul he
  have hpos : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Icc T U)).prod volume, p.1 ∈ Icc T U :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  apply (ht.mul_prod hi.norm).mono'
  · apply hm.congr
    filter_upwards [hpos] with p hp
    rw [evaluated_scale sigma (k*p.1) p.2 (mul_pos hk (hT.trans_le hp.1))]
    ring
  · filter_upwards [hpos] with p hp
    have hkt : 0 < k*p.1 := mul_pos hk (hT.trans_le hp.1)
    have he : ‖exp (-(line p.2)*(Real.log (k*p.1):ℂ))‖ = (k*p.1)^(-5/4:ℝ) := by
      rw [norm_exp,Real.rpow_def_of_pos hkt]
      congr 1
      simp [line]
      ring
    have hb : (k*p.1)^(-5/4:ℝ) ≤ D :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hk hT) (by nlinarith [hp.1]) (by norm_num)
    rw [evaluated_scale sigma (k*p.1) p.2 hkt,norm_mul,norm_mul,he]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)

theorem weighted_identity (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) :
    (∫ t in Icc T U, Phi t*(∫ y in Ioi (0:ℝ), second (sigma-1) sigma (k*t) y*cos (y:ℂ))) =
      (1/(2*Real.pi):ℂ)*∫ t in Icc T U, Phi t*(∫ tau : ℝ, evaluated sigma (k*t) tau) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [actual_integral sigma hs hn (k*t) (mul_pos hk (hT.trans_le ht.1))]
  ring

theorem exchanged_identity (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∫ y in Ioi (0:ℝ), ∫ t in Icc T U, Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ)) =
      (1/(2*Real.pi):ℂ)*∫ t in Icc T U, Phi t*(∫ tau : ℝ, evaluated sigma (k*t) tau) := by
  rw [← time_spatial_exchange sigma hs hn k T U hk hT Phi hPhi]
  simp_rw [mul_assoc (Phi _),integral_const_mul]
  exact weighted_identity sigma hs hn k T U hk hT Phi

/-- Time and the evaluated Mellin integral genuinely commute. The actual
weighted sourceW second derivative is on the left. -/
theorem time_mellin_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∫ t in Icc T U, Phi t*(∫ y in Ioi (0:ℝ), second (sigma-1) sigma (k*t) y*cos (y:ℂ))) =
      (1/(2*Real.pi):ℂ)*∫ tau : ℝ, ∫ t in Icc T U, Phi t*evaluated sigma (k*t) tau := by
  rw [weighted_identity sigma hs hn k T U hk hT Phi]
  congr 1
  calc
    _ = ∫ t in Icc T U, ∫ tau : ℝ, Phi t*evaluated sigma (k*t) tau := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => (integral_const_mul (Phi t) _).symm)
    _ = _ := integral_integral_swap (time_mellin_integrable sigma hs hn k T U hk hT Phi hPhi)

theorem finite_time_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U R : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∫ t in Icc T U, ∫ y in Ioc (0:ℝ) R, Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ)) =
      ∫ y in Ioc (0:ℝ) R, ∫ t in Icc T U, Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ) := by
  apply integral_integral_swap
  have hi := time_spatial_integrable sigma hs hn k T U hk hT Phi hPhi
  rw [Measure.prod_restrict] at hi ⊢
  change IntegrableOn (fun p : ℝ × ℝ => Phi p.1*second (sigma-1) sigma (k*p.1) p.2*cos (p.2:ℂ))
    ((Icc T U).prod (Ioi (0:ℝ))) (volume.prod volume) at hi
  change IntegrableOn (fun p : ℝ × ℝ => Phi p.1*second (sigma-1) sigma (k*p.1) p.2*cos (p.2:ℂ))
    ((Icc T U).prod (Ioc (0:ℝ) R)) (volume.prod volume)
  exact hi.mono_set (fun p hp => ⟨hp.1,hp.2.1⟩)

/-- Actual removal of the spatial cutoff after time integration. Joint
integrability is supplied by one envelope, uniform in the whole time interval. -/
theorem time_cutoff_limit (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    Tendsto (fun R : ℝ => ∫ t in Icc T U, ∫ y in Ioc (0:ℝ) R,
      Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ)) atTop
      (𝓝 ((1/(2*Real.pi):ℂ)*∫ t in Icc T U, Phi t*(∫ tau : ℝ, evaluated sigma (k*t) tau))) := by
  have hi := (time_spatial_integrable sigma hs hn k T U hk hT Phi hPhi).integral_prod_right
  have hh := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hi tendsto_id
  rw [exchanged_identity sigma hs hn k T U hk hT Phi hPhi] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  simp only [id_eq]
  rw [intervalIntegral.integral_of_le hR]
  exact (finite_time_exchange sigma hs hn k T U R hk hT Phi hPhi).symm

#print axioms weighted_identity
#print axioms evaluated_scale
#print axioms time_mellin_integrable
#print axioms time_mellin_exchange
#print axioms exchanged_identity
#print axioms finite_time_exchange
#print axioms time_cutoff_limit
end XiPrime8845.PRZZCosineTimeMellin

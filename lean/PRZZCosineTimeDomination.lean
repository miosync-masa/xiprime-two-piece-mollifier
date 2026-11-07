import PRZZCosineSpatialImproper
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual second derivative admits one spatial envelope for every
positive scale above a fixed lower scale. This supplies time/spatial
Fubini on a positive compact time interval, without a Fubini hypothesis. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineTimeDomination
open PRZZCosineSpatialJets PRZZCosineSpatialBoundary PRZZSourceWDerivatives
set_option maxHeartbeats 6000000

theorem second_power_uniform (sigma : ℂ) (hs : sigma ≠ 0) (A a : ℝ)
    (hA : 0 < A) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ X y : ℝ, A ≤ X → 0 < y →
      ‖second (sigma-1) sigma X y‖ ≤ C*y^(sigma.re+2*a-3) := by
  obtain ⟨B,hB,hb⟩ := source_caps sigma hs a ha
  let p := sigma-1
  let P := ‖p*(p-1)‖+‖6-4*p‖+4
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨B*P*A^(-a),by positivity,?_⟩
  intro X y hAX hy
  have hX : 0 < X := hA.trans_le hAX
  have hu : 0 < PRZZCosineSpatialJets.arg X y := by unfold PRZZCosineSpatialJets.arg; positivity
  obtain ⟨hw,hj,hj'⟩ := hb (PRZZCosineSpatialJets.arg X y) hu
  have hinner : ‖p*(p-1)*PRZZDyadicEnvelope.sourceW sigma (PRZZCosineSpatialJets.arg X y)+
      (6-4*p)*(PRZZCosineSpatialJets.arg X y:ℂ)*jet sigma 0 (PRZZCosineSpatialJets.arg X y)+
        4*(PRZZCosineSpatialJets.arg X y:ℂ)^2*jet sigma 1 (PRZZCosineSpatialJets.arg X y)‖ ≤
      P*(B*(PRZZCosineSpatialJets.arg X y)^(-a)) := by
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hu]
    have h0 := mul_le_mul_of_nonneg_left hw (norm_nonneg (p*(p-1)))
    have h1 := mul_le_mul_of_nonneg_left hj (norm_nonneg (6-4*p))
    rw [norm_mul] at h0
    simp only [P,norm_mul]
    nlinarith only [h0,h1,hj']
  change ‖second p sigma X y‖ ≤ _
  rw [second,norm_mul,norm_div,power_norm p y hy,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
  apply (mul_le_mul_of_nonneg_left hinner (by positivity)).trans
  change (y^p.re/y^2)*(P*(B*(PRZZCosineSpatialJets.arg X y)^(-a))) ≤
    (B*P*A^(-a))*y^(sigma.re+2*a-3)
  have he := normalized_power p X y a 2 hX hy
  norm_num only [Nat.cast_ofNat] at he
  have hpow : X^(-a) ≤ A^(-a) := Real.rpow_le_rpow_of_nonpos hA hAX (by linarith)
  calc
    _ = (B*P)*((y^p.re/y^2)*(PRZZCosineSpatialJets.arg X y)^(-a)) := by ring
    _ = (B*P)*(X^(-a)*y^(sigma.re+2*a-3)) := by
      rw [he]
      have he' : p.re+2*a-2 = sigma.re+2*a-3 := by
        change (sigma.re-1)+2*a-2 = _
        ring
      rw [he']
    _ ≤ (B*P*A^(-a))*y^(sigma.re+2*a-3) := by
      have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ B*P by positivity)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hy.le (sigma.re+2*a-3))

theorem second_envelope_uniform (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X y : ℝ, A ≤ X → 0 < y →
      ‖second (sigma-1) sigma X y‖ ≤ C*PRZZZeroGap.envelope y := by
  obtain ⟨C,hC,hc⟩ := second_power_uniform sigma hs A (1/8) hA (by norm_num)
  obtain ⟨D,hD,hd⟩ := second_power_uniform sigma hs A 2 hA (by norm_num)
  refine ⟨C+D,by positivity,?_⟩
  intro X y hAX hy
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  by_cases hyl : y ≤ 1
  · rw [PRZZZeroGap.envelope,if_pos hyl,mul_one]
    have hp : y^(sigma.re+2*(2:ℝ)-3) ≤ 1 :=
      Real.rpow_le_one hy.le hyl (by linarith [hr.1])
    have hh := (hd X y hAX hy).trans (mul_le_mul_of_nonneg_left hp hD.le)
    nlinarith
  · rw [PRZZZeroGap.envelope,if_neg hyl]
    apply (hc X y hAX hy).trans
    have hp : y^(sigma.re+2*(1/8:ℝ)-3) ≤ y^(-2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hr.2])
    exact (mul_le_mul_of_nonneg_left hp hC.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hy.le _))

theorem second_joint_continuous (sigma : ℂ) (hs : sigma ≠ 0) (k T U : ℝ)
    (hk : 0 < k) (hT : 0 < T) :
    ContinuousOn (fun p : ℝ × ℝ => second (sigma-1) sigma (k*p.1) p.2)
      ((Icc T U).prod (Ioi (0:ℝ))) := by
  intro p hp
  have ht : 0 < p.1 := hT.trans_le hp.1.1
  have hy : 0 < p.2 := hp.2
  have hx : 0 < PRZZCosineSpatialJets.arg (k*p.1) p.2 := by
    unfold PRZZCosineSpatialJets.arg; positivity
  have harg : ContinuousAt (fun p : ℝ × ℝ => PRZZCosineSpatialJets.arg (k*p.1) p.2) p := by
    unfold PRZZCosineSpatialJets.arg
    fun_prop (disch := exact pow_ne_zero 2 hy.ne')
  have hw := (source_hasDerivAt sigma hs _ hx).continuousAt.comp (f := fun p : ℝ × ℝ => PRZZCosineSpatialJets.arg (k*p.1) p.2) harg
  have hj := (jet_hasDerivAt sigma 0 _ hx).continuousAt.comp (f := fun p : ℝ × ℝ => PRZZCosineSpatialJets.arg (k*p.1) p.2) harg
  have hj' := (jet_hasDerivAt sigma 1 _ hx).continuousAt.comp (f := fun p : ℝ × ℝ => PRZZCosineSpatialJets.arg (k*p.1) p.2) harg
  have hpw := (power_deriv (sigma-1) p.2 hy).continuousAt.comp continuous_snd.continuousAt
  have hyc : ContinuousAt (fun p : ℝ × ℝ => (p.2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp continuous_snd.continuousAt
  have hac := Complex.continuous_ofReal.continuousAt.comp (f := fun p : ℝ × ℝ => PRZZCosineSpatialJets.arg (k*p.1) p.2) harg
  apply ContinuousAt.continuousWithinAt
  unfold second
  fun_prop (disch := exact pow_ne_zero 2 (show (p.2:ℂ) ≠ 0 by exact_mod_cast hy.ne'))

theorem time_spatial_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    Integrable (fun p : ℝ × ℝ => Phi p.1*second (sigma-1) sigma (k*p.1) p.2*cos (p.2:ℂ))
      ((volume.restrict (Icc T U)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  obtain ⟨C,hC,hc⟩ := second_envelope_uniform sigma hs hn (k*T) (mul_pos hk hT)
  have ht : IntegrableOn (fun t : ℝ => ‖Phi t‖*C) (Icc T U) :=
    (hPhi.norm.continuousOn.integrableOn_Icc).mul_const C
  apply (ht.mul_prod PRZZZeroGap.envelope_integrable).mono'
  · have hh := second_joint_continuous sigma hs k T U hk hT
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Phi p.1*second (sigma-1) sigma (k*p.1) p.2*cos (p.2:ℂ))
        ((Icc T U).prod (Ioi (0:ℝ))) := by fun_prop
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Ioi)
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Icc T U)).prod (volume.restrict (Ioi (0:ℝ))),
        p.1 ∈ Icc T U ∧ p.2 ∈ Ioi (0:ℝ) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with p hp hq
      exact ⟨hp,hq⟩
    filter_upwards [hpos] with p hp
    rw [norm_mul,norm_mul]
    apply (mul_le_of_le_one_right (by positivity) (show ‖cos (p.2:ℂ)‖ ≤ 1 from by
      simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one p.2)).trans
    exact (mul_le_mul_of_nonneg_left (hc (k*p.1) p.2 (by nlinarith [hp.1.1]) hp.2)
      (norm_nonneg _)).trans_eq (by ring)

theorem time_spatial_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (k T U : ℝ) (hk : 0 < k) (hT : 0 < T) (Phi : ℝ → ℂ) (hPhi : Continuous Phi) :
    (∫ t in Icc T U, ∫ y in Ioi (0:ℝ),
      Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ)) =
    ∫ y in Ioi (0:ℝ), ∫ t in Icc T U,
      Phi t*second (sigma-1) sigma (k*t) y*cos (y:ℂ) :=
  integral_integral_swap (time_spatial_integrable sigma hs hn k T U hk hT Phi hPhi)

#print axioms second_power_uniform
#print axioms second_envelope_uniform
#print axioms second_joint_continuous
#print axioms time_spatial_integrable
#print axioms time_spatial_exchange
end XiPrime8845.PRZZCosineTimeDomination

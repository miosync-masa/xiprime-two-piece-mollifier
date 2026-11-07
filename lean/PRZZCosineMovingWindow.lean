import PRZZCosineTimeMellin

/-! Reciprocal substitution produces (omega/R, omega*R), not
(1/R,R). Supply the corresponding improper limit and a common bound
for every positive spatial subinterval and every scale above A. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineMovingWindow
open PRZZCosineSpatialJets PRZZCosineSpatialBoundary PRZZCosineSpatialImproper
open PRZZCosineTimeDomination PRZZCosineDerivativeMellin PRZZCosineMellin
set_option maxHeartbeats 6000000

theorem scaled_integral_limit (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi (0:ℝ)))
    (omega : ℝ) (ho : 0 < omega) :
    Tendsto (fun R : ℝ => ∫ y in (omega/R)..(omega*R), g y) atTop
      (𝓝 (∫ y in Ioi (0:ℝ), g y)) := by
  have hlo : Tendsto (fun R : ℝ => omega/R) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := omega)).mul tendsto_inv_atTop_zero
  have hhi : Tendsto (fun R : ℝ => omega*R) atTop atTop :=
    Tendsto.const_mul_atTop ho tendsto_id
  have hh : Tendsto (fun R : ℝ => ∫ y in Ioi (0:ℝ), (Ioc (omega/R) (omega*R)).indicator g y) atTop
      (𝓝 (∫ y in Ioi (0:ℝ), g y)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => ‖g y‖)
    · exact Eventually.of_forall (fun R => hg.aestronglyMeasurable.indicator measurableSet_Ioc)
    · exact Eventually.of_forall (fun R => Eventually.of_forall (fun y => by
        by_cases hy : y ∈ Ioc (omega/R) (omega*R)
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy,norm_zero]; exact norm_nonneg _))
    · exact hg.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      apply tendsto_const_nhds.congr'
      filter_upwards [hlo.eventually (eventually_lt_nhds hy),hhi.eventually_ge_atTop y] with R hl hr
      rw [Set.indicator_of_mem (show y ∈ Ioc (omega/R) (omega*R) from ⟨hl,hr⟩)]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  have hle : omega/R ≤ omega*R := (div_le_iff₀ hR0).mpr (by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ R*R by nlinarith) ho.le
    nlinarith only [hh])
  have hsub : Ioc (omega/R) (omega*R) ⊆ Ioi (0:ℝ) :=
    fun y hy => (div_pos ho hR0).trans hy.1
  rw [intervalIntegral.integral_of_le hle,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hsub]

theorem scaled_improper (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X omega : ℝ) (hX : 0 < X) (ho : 0 < omega) :
    Tendsto (fun R : ℝ => ∫ y in (omega/R)..(omega*R),
      primitive (sigma-1) sigma X y*cos (y:ℂ)) atTop
      (𝓝 (-((1/(2*Real.pi):ℂ)*∫ tau : ℝ, evaluated sigma X tau))) := by
  have hlo : Tendsto (fun R : ℝ => omega/R) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [div_eq_mul_inv,mul_zero] using
        (tendsto_const_nhds (x := omega)).mul tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
      exact div_pos ho hR
  have hhi : Tendsto (fun R : ℝ => omega*R) atTop atTop :=
    Tendsto.const_mul_atTop ho tendsto_id
  have hb := boundary_limits sigma hs hn X hX
  have hi := scaled_integral_limit _ (second_integrable sigma hs hn X hX).2 omega ho
  have hh := ((hb.1.comp hhi).sub (hb.2.comp hlo)).sub hi
  simp only [sub_zero,zero_sub] at hh
  rw [actual_integral sigma hs hn X hX] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  exact (finite_cosine_ibp (sigma-1) sigma hs X (omega/R) (omega*R) hX (div_pos ho hR0)
    ((div_le_iff₀ hR0).mpr (by
      have hh := mul_le_mul_of_nonneg_left (show 1 ≤ R*R by nlinarith) ho.le
      nlinarith only [hh]))).symm

theorem first_two_uniform (sigma : ℂ) (hs : sigma ≠ 0) (A a : ℝ)
    (hA : 0 < A) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ X y : ℝ, A ≤ X → 0 < y →
      ‖primitive (sigma-1) sigma X y‖ ≤ C*y^((sigma-1).re+2*a) ∧
      ‖first (sigma-1) sigma X y‖ ≤ C*(‖sigma-1‖+2)*y^((sigma-1).re+2*a-1) := by
  obtain ⟨B,hB,hb⟩ := source_caps sigma hs a ha
  refine ⟨B*A^(-a),by positivity,?_⟩
  intro X y hAX hy
  have hX : 0 < X := hA.trans_le hAX
  have hu : 0 < PRZZCosineSpatialJets.arg X y := by unfold PRZZCosineSpatialJets.arg; positivity
  obtain ⟨hw,hj,hj'⟩ := hb (PRZZCosineSpatialJets.arg X y) hu
  have hpow : X^(-a) ≤ A^(-a) := Real.rpow_le_rpow_of_nonpos hA hAX (by linarith)
  have hinner : ‖(sigma-1)*PRZZDyadicEnvelope.sourceW sigma (PRZZCosineSpatialJets.arg X y)-
      2*(PRZZCosineSpatialJets.arg X y:ℂ)*PRZZSourceWDerivatives.jet sigma 0 (PRZZCosineSpatialJets.arg X y)‖ ≤
      (‖sigma-1‖+2)*(B*(PRZZCosineSpatialJets.arg X y)^(-a)) := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
    have hh := mul_le_mul_of_nonneg_left hw (norm_nonneg (sigma-1))
    nlinarith only [hh,hj]
  constructor
  · rw [primitive,norm_mul,power_norm _ y hy]
    apply (mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hy.le _)).trans
    change y^((sigma-1).re)*(B*(PRZZCosineSpatialJets.arg X y)^(-a)) ≤
      (B*A^(-a))*y^((sigma-1).re+2*a)
    have he := normalized_power (sigma-1) X y a 0 hX hy
    simp only [pow_zero,div_one,Nat.cast_zero,sub_zero] at he
    calc
      _ = B*(X^(-a)*y^((sigma-1).re+2*a)) := by rw [← he]; ring
      _ ≤ (B*A^(-a))*y^((sigma-1).re+2*a) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hB.le) (Real.rpow_nonneg hy.le ((sigma-1).re+2*a))
  · rw [first,norm_mul,norm_div,power_norm _ y hy,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    apply (mul_le_mul_of_nonneg_left hinner (by positivity)).trans
    change (y^((sigma-1).re)/y)*((‖sigma-1‖+2)*(B*(PRZZCosineSpatialJets.arg X y)^(-a))) ≤
      (B*A^(-a))*(‖sigma-1‖+2)*y^((sigma-1).re+2*a-1)
    have he := normalized_power (sigma-1) X y a 1 hX hy
    simp only [pow_one,Nat.cast_one] at he
    calc
      _ = (B*(‖sigma-1‖+2))*((y^((sigma-1).re)/y)*(PRZZCosineSpatialJets.arg X y)^(-a)) := by ring
      _ = (B*(‖sigma-1‖+2))*(X^(-a)*y^((sigma-1).re+2*a-1)) := by rw [he]
      _ ≤ (B*A^(-a))*(‖sigma-1‖+2)*y^((sigma-1).re+2*a-1) := by
        have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ B*(‖sigma-1‖+2) by positivity)
        simpa only [mul_assoc,mul_comm,mul_left_comm] using
          mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hy.le ((sigma-1).re+2*a-1))

theorem boundary_uniform (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X y : ℝ, A ≤ X → 0 < y → ‖boundary sigma X y‖ ≤ C := by
  obtain ⟨C,hC,hc⟩ := first_two_uniform sigma hs A (1/8) hA (by norm_num)
  obtain ⟨D,hD,hd⟩ := first_two_uniform sigma hs A 2 hA (by norm_num)
  let P := ‖sigma-1‖+2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨(C+D)*(1+P),by positivity,?_⟩
  intro X y hAX hy
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  apply (boundary_norm sigma X y).trans
  by_cases hyl : y ≤ 1
  · obtain ⟨h0,h1⟩ := hd X y hAX hy
    have hp0 : y^((sigma-1).re+2*(2:ℝ)) ≤ 1 := Real.rpow_le_one hy.le hyl (by simp; linarith [hr.1])
    have hp1 : y^((sigma-1).re+2*(2:ℝ)-1) ≤ 1 := Real.rpow_le_one hy.le hyl (by simp; linarith [hr.1])
    have h0' := h0.trans (mul_le_mul_of_nonneg_left hp0 hD.le)
    have h1' := h1.trans (mul_le_mul_of_nonneg_left hp1 (show 0 ≤ D*P by positivity))
    change _ ≤ (C+D)*(1+P)
    nlinarith
  · obtain ⟨h0,h1⟩ := hc X y hAX hy
    have hp0 : y^((sigma-1).re+2*(1/8:ℝ)) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ y by linarith)
        (show (sigma-1).re+2*(1/8:ℝ) ≤ 0 by simp; linarith [hr.2])
    have hp1 : y^((sigma-1).re+2*(1/8:ℝ)-1) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ y by linarith)
        (show (sigma-1).re+2*(1/8:ℝ)-1 ≤ 0 by simp; linarith [hr.2])
    have h0' := h0.trans (mul_le_mul_of_nonneg_left hp0 hC.le)
    have h1' := h1.trans (mul_le_mul_of_nonneg_left hp1 (show 0 ≤ C*P by positivity))
    change _ ≤ (C+D)*(1+P)
    nlinarith

theorem interval_uniform (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X a b : ℝ, A ≤ X → 0 < a → a ≤ b →
      ‖∫ y in a..b, primitive (sigma-1) sigma X y*cos (y:ℂ)‖ ≤ C := by
  obtain ⟨K,hK,hb⟩ := boundary_uniform sigma hs hn A hA
  obtain ⟨D,hD,hd⟩ := second_envelope_uniform sigma hs hn A hA
  let J := ∫ y in Ioi (0:ℝ), PRZZZeroGap.envelope y
  have hJ : 0 ≤ J := integral_nonneg (fun y => PRZZZeroGap.envelope_nonneg y)
  refine ⟨2*K+D*J,by positivity,?_⟩
  intro X a b hAX ha hab
  have hX : 0 < X := hA.trans_le hAX
  let g := fun y : ℝ => second (sigma-1) sigma X y*cos (y:ℂ)
  have hi : IntegrableOn g (Ioi (0:ℝ)) := (second_integrable sigma hs hn X hX).2
  have hg : ∀ y : ℝ, 0 < y → ‖g y‖ ≤ D*PRZZZeroGap.envelope y := by
    intro y hy
    dsimp [g]
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (show ‖cos (y:ℂ)‖ ≤ 1 from by
      simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one y)).trans
    exact hd X y hAX hy
  have hmass : (∫ y in Ioi (0:ℝ), ‖g y‖) ≤ D*J := by
    have hh := integral_mono_ae hi.norm (PRZZZeroGap.envelope_integrable.const_mul D) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hg y hy)
    simpa only [integral_const_mul,J] using hh
  have hsub : (∫ y in Ioc a b, ‖g y‖) ≤ ∫ y in Ioi (0:ℝ), ‖g y‖ :=
    setIntegral_mono_set hi.norm (Eventually.of_forall (fun y => norm_nonneg _))
      (Eventually.of_forall (fun y hy => ha.trans hy.1))
  have hgi : ‖∫ y in a..b, g y‖ ≤ D*J := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    rw [intervalIntegral.integral_of_le hab]
    exact hsub.trans hmass
  rw [finite_cosine_ibp (sigma-1) sigma hs X a b hX ha hab]
  have hh := (norm_sub_le (boundary sigma X b-boundary sigma X a) (∫ y in a..b, g y)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  change ‖boundary sigma X b-boundary sigma X a-∫ y in a..b, g y‖ ≤ _
  have hb0 := hb X b hAX (ha.trans_le hab)
  have ha0 := hb X a hAX ha
  linarith

#print axioms scaled_integral_limit
#print axioms scaled_improper
#print axioms first_two_uniform
#print axioms boundary_uniform
#print axioms interval_uniform
end XiPrime8845.PRZZCosineMovingWindow

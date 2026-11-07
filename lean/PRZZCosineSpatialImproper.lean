import PRZZCosineSpatialBoundary
import PRZZZeroGap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual second spatial derivative integrability and removal of the
two endpoint terms in cosine integration by parts. The original
undifferentiated oscillatory integral is represented by an improper
limit, not by the default value of a nonintegrable Bochner integral. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineSpatialImproper
open PRZZCosineSpatialJets PRZZCosineSpatialBoundary PRZZSourceWDerivatives
set_option maxHeartbeats 5000000

theorem second_continuous (sigma : ℂ) (hs : sigma ≠ 0) (X : ℝ) (hX : 0 < X) :
    ContinuousOn (second (sigma-1) sigma X) (Ioi (0:ℝ)) := by
  intro y hy
  have hypos : 0 < y := hy
  have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have ha := arg_deriv X y hy
  have hp := (power_deriv (sigma-1) y hy).continuousAt
  have hw := ((source_hasDerivAt sigma hs (arg X y) (by unfold PRZZCosineSpatialJets.arg; positivity)).scomp y ha).continuousAt
  have hj := ((jet_hasDerivAt sigma 0 (arg X y) (by unfold PRZZCosineSpatialJets.arg; positivity)).scomp y ha).continuousAt
  have hj' := ((jet_hasDerivAt sigma 1 (arg X y) (by unfold PRZZCosineSpatialJets.arg; positivity)).scomp y ha).continuousAt
  have haC := ha.ofReal_comp.continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold second
  fun_prop (disch := simp [hyC])

theorem second_envelope (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    ∃ K : ℝ, 0 < K ∧ ∀ y : ℝ, 0 < y →
      ‖second (sigma-1) sigma X y‖ ≤ K*PRZZZeroGap.envelope y := by
  obtain ⟨C,hC,hb⟩ := bounds (sigma-1) sigma hs X (1/8) hX (by norm_num)
  obtain ⟨D,hD,hd⟩ := bounds (sigma-1) sigma hs X 2 hX (by norm_num)
  let P := ‖(sigma-1)*(sigma-1-1)‖+‖6-4*(sigma-1)‖+4
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨(C+D)*P+1,by positivity,?_⟩
  intro y hy
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  by_cases hyl : y ≤ 1
  · have hh := (hd y hy).2.2
    have hp : y^((sigma-1).re+2*(2:ℝ)-2) ≤ 1 :=
      Real.rpow_le_one hy.le hyl (by simp; linarith [hr.1])
    have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ D*P by positivity)
    change _ ≤ ((C+D)*P+1)*PRZZZeroGap.envelope y
    rw [PRZZZeroGap.envelope,if_pos hyl,mul_one]
    change ‖second (sigma-1) sigma X y‖ ≤ D*P*y^((sigma-1).re+2*2-2) at hh
    nlinarith
  · have hh := (hb y hy).2.2
    have hp : y^((sigma-1).re+2*(1/8:ℝ)-2) ≤ y^(-2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith [hr.2])
    have hb' := mul_le_mul_of_nonneg_left hp (show 0 ≤ C*P by positivity)
    change _ ≤ ((C+D)*P+1)*PRZZZeroGap.envelope y
    rw [PRZZZeroGap.envelope,if_neg hyl]
    change ‖second (sigma-1) sigma X y‖ ≤ C*P*y^((sigma-1).re+2*(1/8)-2) at hh
    apply (hh.trans hb').trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hD.le hP.le])
      (Real.rpow_nonneg hy.le (-2))

theorem second_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    IntegrableOn (second (sigma-1) sigma X) (Ioi (0:ℝ)) ∧
      IntegrableOn (fun y : ℝ => second (sigma-1) sigma X y*cos (y:ℂ)) (Ioi (0:ℝ)) := by
  obtain ⟨K,hK,hb⟩ := second_envelope sigma hs hn X hX
  have hc := second_continuous sigma hs X hX
  have hi : IntegrableOn (second (sigma-1) sigma X) (Ioi (0:ℝ)) := by
    apply (PRZZZeroGap.envelope_integrable.const_mul K).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hb y hy
  refine ⟨hi,?_⟩
  apply hi.norm.mono' ((hc.mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi)
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one y)

def boundary (sigma : ℂ) (X y : ℝ) : ℂ :=
  primitive (sigma-1) sigma X y*sin (y:ℂ)+first (sigma-1) sigma X y*cos (y:ℂ)

theorem boundary_norm (sigma : ℂ) (X y : ℝ) :
    ‖boundary sigma X y‖ ≤ ‖primitive (sigma-1) sigma X y‖+‖first (sigma-1) sigma X y‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add <;> rw [norm_mul] <;> apply mul_le_of_le_one_right (norm_nonneg _)
  · simpa only [← Complex.ofReal_sin,Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one y
  · simpa only [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one y

theorem boundary_limits (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (boundary sigma X) atTop (𝓝 0) ∧
      Tendsto (boundary sigma X) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hi := endpoint_infinity sigma hs hn X hX
  have hz := endpoint_zero sigma hs hn X hX
  constructor
  · apply squeeze_zero_norm' (Filter.Eventually.of_forall (boundary_norm sigma X))
    simpa using hi.1.norm.add hi.2.norm
  · apply squeeze_zero_norm' (Filter.Eventually.of_forall (boundary_norm sigma X))
    simpa using hz.1.norm.add hz.2.norm

theorem integral_window_limit (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi (0:ℝ))) :
    Tendsto (fun R : ℝ => ∫ y in (1/R)..R, g y) atTop
      (𝓝 (∫ y in Ioi (0:ℝ), g y)) := by
  have hh : Tendsto (fun R : ℝ => ∫ y in Ioi (0:ℝ), (Ioc (1/R) R).indicator g y) atTop
      (𝓝 (∫ y in Ioi (0:ℝ), g y)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => ‖g y‖)
    · exact Filter.Eventually.of_forall (fun R => hg.aestronglyMeasurable.indicator measurableSet_Ioc)
    · exact Filter.Eventually.of_forall (fun R => Filter.Eventually.of_forall (fun y => by
        simp only [one_div]
        by_cases hy : y ∈ Ioc R⁻¹ R
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy,norm_zero]; exact norm_nonneg _))
    · exact hg.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (2/y),eventually_ge_atTop y] with R hR hRy hRy'
      have hR0 : 0 < R := by linarith
      have hlo : 1/R < y := (div_lt_iff₀ hR0).mpr (by
        have hh := (div_le_iff₀ hy).mp hRy
        nlinarith)
      have hmem : y ∈ Ioc R⁻¹ R := by simpa only [one_div] using (show y ∈ Ioc (1/R) R from ⟨hlo,hRy'⟩)
      simp only [one_div]
      rw [Set.indicator_of_mem hmem]
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  have hle : 1/R ≤ R := (div_le_iff₀ hR0).mpr (by nlinarith)
  have hsub : Ioc (1/R) R ⊆ Ioi (0:ℝ) := fun y hy => (by positivity : (0:ℝ) < 1/R).trans hy.1
  rw [intervalIntegral.integral_of_le hle,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hsub]

/-- Genuine improper cosine integral of the actual source weight.
Both spatial endpoint corrections have been proved to vanish. -/
theorem improper_cosine (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun R : ℝ => ∫ y in (1/R)..R, primitive (sigma-1) sigma X y*cos (y:ℂ)) atTop
      (𝓝 (-(∫ y in Ioi (0:ℝ), second (sigma-1) sigma X y*cos (y:ℂ)))) := by
  have hb := boundary_limits sigma hs hn X hX
  have hR : Tendsto (fun R : ℝ => 1/R) atTop (𝓝[>] (0:ℝ)) := by
    simpa only [one_div] using (tendsto_inv_atTop_nhdsGT_zero :
      Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝[>] (0:ℝ)))
  have hi := integral_window_limit (fun y : ℝ => second (sigma-1) sigma X y*cos (y:ℂ))
    (second_integrable sigma hs hn X hX).2
  have hh := (hb.1.sub (hb.2.comp hR)).sub hi
  simp only [sub_self,zero_sub] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  exact (finite_cosine_ibp (sigma-1) sigma hs X (1/R) R hX (by positivity)
    ((div_le_iff₀ hR0).mpr (by nlinarith))).symm

#print axioms second_continuous
#print axioms second_envelope
#print axioms second_integrable
#print axioms boundary_norm
#print axioms boundary_limits
#print axioms integral_window_limit
#print axioms improper_cosine
end XiPrime8845.PRZZCosineSpatialImproper

import PRZZCosineMellinCore
import PRZZDyadicEnvelope

/-! Full source Mellin coefficient: actual annihilator, reciprocal s,
positive scale and Gaussian. The cosine truncation limit commutes with
this Mellin integral. Identification with the original zero spatial
integral and the sourceW contour shift are separate assertions. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineMellin
open PRZZCosineMellinCore PRZZDyadicEnvelope
set_option maxHeartbeats 5000000

def coefficient (sigma : ℂ) (X tau : ℝ) : ℂ :=
  (X:ℂ)^(-line tau)*annihilator sigma (line tau)/line tau
def truncated (sigma : ℂ) (X R tau : ℝ) : ℂ :=
  coefficient sigma X tau*(Complex.exp ((line tau)^2)*moment sigma R tau)
def evaluated (sigma : ℂ) (X tau : ℝ) : ℂ :=
  coefficient sigma X tau*(Complex.exp ((line tau)^2)*limitMoment sigma tau)

theorem line_bounds (tau : ℝ) : 1 ≤ ‖line tau‖ ∧ ‖line tau‖ ≤ 2*(1+|tau|) := by
  have hlo := Complex.abs_re_le_norm (line tau)
  have hhi := norm_add_le (((5/4:ℝ):ℂ)) ((tau:ℂ)*I)
  norm_num [line,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hlo hhi ⊢
  constructor <;> linarith [abs_nonneg tau]

theorem line_ne (tau : ℝ) : line tau ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (line_bounds tau).1)

theorem scale_norm (X tau : ℝ) (hX : 0 < X) :
    ‖(X:ℂ)^(-line tau)‖ = X^(-5/4:ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  congr 1
  simp [line]
  ring

theorem annihilator_cap (sigma : ℂ) (hs : sigma ≠ 0) (tau : ℝ) :
    ‖annihilator sigma (line tau)‖ ≤ (1+16/‖sigma‖^2)*(1+|tau|)^2 := by
  have hn : 0 < ‖sigma‖ := norm_pos_iff.mpr hs
  have hh := annihilator_bound sigma (line tau) 1 ‖sigma‖ zero_lt_one hn (by simp)
  norm_num only [one_div,div_pow] at hh
  have hp : 1 ≤ (1+|tau|)^2 := by nlinarith [abs_nonneg tau]
  calc
    _ ≤ 1+4*(2*(1+|tau|))^2*(‖sigma‖⁻¹)^2 := by
      apply hh.trans
      gcongr
      exact (line_bounds tau).2
    _ = 1+(16/‖sigma‖^2)*(1+|tau|)^2 := by simp only [div_eq_mul_inv,inv_pow]; ring
    _ ≤ _ := by nlinarith

theorem coefficient_cap (sigma : ℂ) (hs : sigma ≠ 0) (X tau : ℝ) (hX : 0 < X) :
    ‖coefficient sigma X tau‖ ≤
      X^(-5/4:ℝ)*(1+16/‖sigma‖^2)*(1+|tau|)^2 := by
  rw [coefficient,norm_div,norm_mul,scale_norm X tau hX]
  apply (div_le_self (by positivity) (line_bounds tau).1).trans
  exact (mul_le_mul_of_nonneg_left (annihilator_cap sigma hs tau) (by positivity)).trans_eq (by ring)

theorem coefficient_continuous (sigma : ℂ) (X : ℝ) (hX : 0 < X) :
    Continuous (coefficient sigma X) := by
  have hp : Continuous (fun tau : ℝ => (X:ℂ)^(-line tau)) := by
    apply continuous_iff_continuousAt.mpr
    intro tau
    apply (continuousAt_const_cpow (a := (X:ℂ)) (by exact_mod_cast hX.ne')).comp
    dsimp [line]; fun_prop
  have ha : Continuous (fun tau : ℝ => annihilator sigma (line tau)) := by
    dsimp [annihilator,line]; fun_prop
  have hl : Continuous line := by unfold line; fun_prop
  exact (hp.mul ha).div hl line_ne

theorem truncated_continuous (sigma : ℂ) (hs : ‖sigma‖ ≤ 1/8)
    (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R) : Continuous (truncated sigma X R) := by
  have hm := moment_continuous sigma hs R hR
  have he : Continuous (fun tau : ℝ => Complex.exp ((line tau)^2)) := by dsimp [line]; fun_prop
  exact (coefficient_continuous sigma X hX).mul (he.mul hm)

theorem full_majorant : ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℂ) (X : ℝ),
    sigma ≠ 0 → ‖sigma‖ ≤ 1/8 → 0 < X →
    Integrable (fun tau : ℝ => C*X^(-5/4:ℝ)*(1+16/‖sigma‖^2)*
      ((1+|tau|)^5*Real.exp (-tau^2))) ∧
    ∀ R : ℝ, 1 ≤ R → ∀ tau : ℝ,
    ‖truncated sigma X R tau‖ ≤ C*X^(-5/4:ℝ)*(1+16/‖sigma‖^2)*
      ((1+|tau|)^5*Real.exp (-tau^2)) := by
  obtain ⟨C,hC,hi,h⟩ := PRZZCosineDominated.gaussian_source_uniform
  refine ⟨C,hC,?_⟩
  intro sigma X hs hn hX
  refine ⟨(gaussian_power_integrable 5).const_mul _,?_⟩
  intro R hR tau
  have hh := h sigma tau R hn hR
  change ‖Complex.exp ((line tau)^2)*moment sigma R tau‖ ≤ _ at hh
  unfold truncated
  rw [norm_mul]
  exact (mul_le_mul (coefficient_cap sigma hs X tau hX) hh (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

theorem integral_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun R : ℝ => ∫ tau : ℝ, truncated sigma X R tau) atTop
      (𝓝 (∫ tau : ℝ, evaluated sigma X tau)) := by
  obtain ⟨C,hC,h⟩ := full_majorant
  have hh := h sigma X hs hn hX
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun tau : ℝ => C*X^(-5/4:ℝ)*(1+16/‖sigma‖^2)*((1+|tau|)^5*Real.exp (-tau^2)))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact (truncated_continuous sigma hn X R hX (by linarith)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact Filter.Eventually.of_forall (hh.2 R hR)
  · exact hh.1
  · apply Filter.Eventually.of_forall
    intro tau
    exact ((moment_tendsto sigma hn tau).const_mul (Complex.exp ((line tau)^2))).const_mul
      (coefficient sigma X tau)

/-- The evaluated Gamma integral is genuinely integrable; its value is
not obtained by the default value of a nonintegrable Bochner integral. -/
theorem evaluated_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) : Integrable (evaluated sigma X) := by
  have ht (tau : ℝ) : Tendsto (fun R : ℝ => truncated sigma X R tau) atTop
      (𝓝 (evaluated sigma X tau)) :=
    ((moment_tendsto sigma hn tau).const_mul (Complex.exp ((line tau)^2))).const_mul
      (coefficient sigma X tau)
  have hm : AEStronglyMeasurable (evaluated sigma X) := by
    apply aestronglyMeasurable_of_tendsto_ae (f := fun n : ℕ => truncated sigma X ((n:ℝ)+1)) atTop
    · intro n
      exact (truncated_continuous sigma hn X _ hX (by positivity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun tau => (ht tau).comp
        (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop))
  obtain ⟨C,hC,h⟩ := full_majorant
  have hh := h sigma X hs hn hX
  apply hh.1.mono' hm
  apply Filter.Eventually.of_forall
  intro tau
  apply le_of_tendsto (ht tau).norm
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  exact hh.2 R hR tau

#print axioms evaluated_integrable
#print axioms line_bounds
#print axioms line_ne
#print axioms scale_norm
#print axioms annihilator_cap
#print axioms coefficient_cap
#print axioms coefficient_continuous
#print axioms truncated_continuous
#print axioms full_majorant
#print axioms integral_exchange
end XiPrime8845.PRZZCosineMellin

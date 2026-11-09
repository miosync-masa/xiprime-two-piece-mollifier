import PRZZMellinInterval
import PRZZProfileScale

/-! Quantitative Mellin classes for varying arithmetic cutoffs. Smoothness,
positive compact support and dimensionless jets are retained explicitly.
The class constant precedes the function and the support scale. This is a
DI block supplier, not yet a class-uniform theorem for the full moment. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZProfileMellin
open PRZZMellinSeparation PRZZSmoothMellin PRZZMellinSeminorm
set_option maxHeartbeats 8000000

def massCap (width : ℝ) (jets : ℕ → ℝ) : ℝ :=
  4*(width*(jets 0+jets 1+3*jets 2+jets 3))*(∫ t : ℝ, (1+t^2)⁻¹)

/-- The class does not infer smoothness from totalized derivative bounds. -/
structure Member (width : ℝ) (jets : ℕ → ℝ) (f : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ f
  supported : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ Function.support f ⊆ Icc a b ∧
    Real.log (b/a) ≤ width
  jet_bound : ∀ n (x : ℝ), ‖(x:ℂ)^n*iteratedDeriv n f x‖ ≤ jets n

theorem massCap_nonneg (width : ℝ) (hw : 0 ≤ width) (jets : ℕ → ℝ)
    (hj : ∀ n, 0 ≤ jets n) : 0 ≤ massCap width jets := by
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 2
  have h3 := hj 3
  have hi : 0 ≤ ∫ t : ℝ, (1+t^2)⁻¹ := integral_nonneg (fun _ => by positivity)
  unfold massCap
  positivity

theorem member_mass (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (f : ℝ → ℂ) (hf : Member width jets f) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤ massCap width jets := by
  obtain ⟨a,b,ha,hab,hs,hw⟩ := hf.supported
  apply (PRZZMellinInterval.uniform_mass_from_scaled_jets f hf.smooth a b ha hab hs jets hj hf.jet_bound).trans
  have h0 := hj 0
  have h1 := hj 1
  have h2 := hj 2
  have h3 := hj 3
  have hi : 0 ≤ ∫ t : ℝ, (1+t^2)⁻¹ := integral_nonneg (fun _ => by positivity)
  unfold massCap
  gcongr

theorem member_unweighted_mass (width : ℝ) (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n)
    (f : ℝ → ℂ) (hf : Member width jets f) :
    (∫ t : ℝ, ‖mellin f (t*I)‖) ≤ massCap width jets := by
  obtain ⟨a,b,ha,hab,hs,hw⟩ := hf.supported
  have hi : Integrable (fun t : ℝ => (1+|t|)*‖mellin f (t*I)‖) := by
    simpa only [pow_zero,one_mul,pow_one,add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable f a b ha hs hf.smooth 0).add
      (PRZZMellinMoment.polynomial_integrable f a b ha hs hf.smooth 1)
  exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
    (Filter.Eventually.of_forall (fun t => by nlinarith [norm_nonneg (mellin f (t*I)),abs_nonneg t]))).trans
      (member_mass width jets hj f hf)

/-- DI's constant is selected before every member of the quantitative class. -/
theorem coupled_bound_class (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps width : ℝ) (heps : 0 < eps) (hw : 0 ≤ width)
    (jets : ℕ → ℝ) (hj : ∀ n, 0 ≤ jets n) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Finset.Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ d ∈ Finset.Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Finset.Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ f : ℝ → ℂ, Member width jets f → ∀ kappa : ℝ, 0 < kappa →
      ‖PRZZMellinTypeII.coupled C D U V rho r beta nu alpha f kappa‖ ≤
        K*(R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho) := by
  obtain ⟨K,hK,h⟩ := PRZZMellinTypeII.coupled_bound hDI eps heps
  let M := massCap width jets
  have hM : 0 ≤ M := massCap_nonneg width hw jets hj
  refine ⟨K*((1/(2*Real.pi))*M+1),by positivity,?_⟩
  intro C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn hal f hf kappa hk
  obtain ⟨a,b,ha,hab,hs,hw'⟩ := hf.supported
  have hh := h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ
    r beta nu alpha hr hb hn hal f hf.smooth.continuous
      (mellin_convergent f a b ha hs hf.smooth.continuous)
      (vertical_integrable f a b ha hs hf.smooth) kappa hk
  have hx : 0 ≤ R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho := by
    have hC0 : 0 ≤ C := le_trans (by norm_num) hC
    have hD0 : 0 ≤ D := le_trans (by norm_num) hD
    have hU0 : 0 ≤ U := le_trans (by norm_num) hU
    have hV0 : 0 ≤ V := le_trans (by norm_num) hV
    unfold PRZZKloostermanInputs.diBound
    apply mul_nonneg (by positivity)
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)))
  have hm := mul_le_mul_of_nonneg_left (member_unweighted_mass width jets hj f hf)
    (show 0 ≤ (1/(2*Real.pi))*(R*S*(P*Q)*K*PRZZKloostermanInputs.diBound eps C D U V rho) by
      have := mul_nonneg hK.le hx
      nlinarith [show 0 < 1/(2*Real.pi) by positivity])
  apply hh.trans (hm.trans _)
  change _ ≤ K*((1/(2*Real.pi))*M+1)*(R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho)
  dsimp only [M] at *
  nlinarith [mul_nonneg hK.le hx]

/-- Actual seven-profile cutoffs enter one class, before Y,Q or the label. -/
theorem profiles_member (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ ∀ (Y Q : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y →
      Member (Real.log (hi/lo)) jets (PRZZProfileScale.cutoffRaw F Y Q i) := by
  choose jets hj h using (fun n => PRZZProfileScale.scaled_uniform F hF lo hi hlo hs n)
  refine ⟨jets,hj,?_⟩
  intro Y Q i hY hQ hQY
  have hQ0 : 0 < Q := by linarith
  have hY0 : 0 < Y := by linarith
  refine ⟨PRZZProfileScale.cutoffRaw_smooth F hF lo hi hlo hs Y Q i hY0 hQ0,?_,?_⟩
  · refine ⟨lo*Q,hi*Q,by positivity,mul_le_mul_of_nonneg_right hlohi hQ0.le,?_,?_⟩
    · intro x hx
      have hFx : F (Q⁻¹*x) ≠ 0 := by
        intro hz
        exact hx (by simp [PRZZProfileScale.cutoffRaw,scaledCutoff,hz])
      have hxx := hs hFx
      constructor
      · have hh := mul_le_mul_of_nonneg_right hxx.1 hQ0.le
        simpa [mul_assoc,mul_left_comm,mul_comm,hQ0.ne'] using hh
      · have hh := mul_le_mul_of_nonneg_right hxx.2 hQ0.le
        simpa [mul_assoc,mul_left_comm,mul_comm,hQ0.ne'] using hh
    · have he : hi*Q/(lo*Q) = hi/lo := by field_simp
      rw [he]
  · intro n x
    exact h n Y Q x i hY hQ hQY

theorem profiles_mass (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ M : ℝ, 0 < M ∧ ∀ (Y Q : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ Q → Q ≤ Y →
      (∫ t : ℝ, (1+|t|)*‖mellin (PRZZProfileScale.cutoffRaw F Y Q i) (t*I)‖) ≤ M := by
  obtain ⟨jets,hj,h⟩ := profiles_member F hF lo hi hlo hlohi hs
  have hw : 0 ≤ Real.log (hi/lo) := Real.log_nonneg ((one_le_div hlo).mpr hlohi)
  refine ⟨massCap (Real.log (hi/lo)) jets+1,by have := massCap_nonneg _ hw jets hj; positivity,?_⟩
  intro Y Q i hY hQ hQY
  exact (member_mass _ jets hj _ (h Y Q i hY hQ hQY)).trans (by linarith)

/-- The class estimate instantiated at every actual profile, with one DI
constant before height, dyadic scale, profile label and arithmetic data. -/
theorem coupled_bound_profiles (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (eps : ℝ) (heps : 0 < eps) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (lo hi : ℝ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hs : Function.support F ⊆ Icc lo hi) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y scale : ℝ) (i : Fin 7),
      1 ≤ Real.log Y → 1 ≤ scale → scale ≤ Y →
      ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Finset.Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) →
      (∀ d ∈ Finset.Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Finset.Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) →
      (∀ v ∈ Finset.Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ kappa : ℝ, 0 < kappa →
      ‖PRZZMellinTypeII.coupled C D U V rho r beta nu alpha
        (PRZZProfileScale.cutoffRaw F Y scale i) kappa‖ ≤
        K*(R*S*(P*Q)*PRZZKloostermanInputs.diBound eps C D U V rho) := by
  obtain ⟨jets,hj,hprofile⟩ := profiles_member F hF lo hi hlo hlohi hs
  have hw : 0 ≤ Real.log (hi/lo) := Real.log_nonneg ((one_le_div hlo).mpr hlohi)
  obtain ⟨K,hK,h⟩ := coupled_bound_class hDI eps (Real.log (hi/lo)) heps hw jets hj
  refine ⟨K,hK,?_⟩
  intro Y scale i hY hscale hscaleY C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn hal kappa hk
  exact h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn hal
    _ (hprofile Y scale i hY hscale hscaleY) kappa hk

#print axioms coupled_bound_profiles
#print axioms massCap_nonneg
#print axioms member_mass
#print axioms member_unweighted_mass
#print axioms coupled_bound_class
#print axioms profiles_member
#print axioms profiles_mass
end XiPrime8845.PRZZProfileMellin

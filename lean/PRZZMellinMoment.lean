import PRZZSmoothMellin

/-! Polynomial Mellin-frequency costs are integrable and independent of
the cutoff scale. This supplies the analytic cost of variation growth;
it does not assert a uniform bound on the frequency-dependent DI block. -/
noncomputable section
open scoped FourierTransform SchwartzMap ContDiff
open MeasureTheory Complex
namespace XiPrime8845.PRZZMellinMoment
open PRZZSmoothMellin PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem polynomial_integrable (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Set.Icc a b) (hf : ContDiff ℝ ∞ F) (k : ℕ) :
    Integrable (fun t : ℝ => |t|^k*‖mellin F (t*I)‖) := by
  let g := logSchwartz F a b ha hs hf
  have hg := (𝓕 g).integrable_pow_mul volume k
  have h := (hg.comp_mul_right' (show (2*Real.pi)⁻¹ ≠ 0 by positivity)).const_mul ((2*Real.pi)^k)
  have he : (fun t : ℝ => (2*Real.pi)^k*
      (‖t*(2*Real.pi)⁻¹‖^k*‖(𝓕 g) (t*(2*Real.pi)⁻¹)‖)) =
      (fun t : ℝ => |t|^k*‖mellin F (t*I)‖) := by
    funext t
    rw [mellin_fourier]
    change _ = |t|^k*‖(𝓕 g) (t/(2*Real.pi))‖
    rw [← div_eq_mul_inv,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi),div_pow]
    field_simp
  rwa [he] at h

/-- One fixed constant absorbs a constant plus a linear frequency cost.
The Mellin cutoff scale N is quantified after that constant. -/
theorem linear_mass (F : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support F ⊆ Set.Icc a b) (hf : ContDiff ℝ ∞ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℝ, 0 < N →
      Integrable (fun t : ℝ => (1+|t|)*‖mellin (scaledCutoff F N) (t*I)‖) ∧
      (∫ t : ℝ, (1+|t|)*‖mellin (scaledCutoff F N) (t*I)‖) = M := by
  have hi : Integrable (fun t : ℝ => (1+|t|)*‖mellin F (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using (polynomial_integrable F a b ha hs hf 0).add
      (polynomial_integrable F a b ha hs hf 1)
  refine ⟨∫ t : ℝ, (1+|t|)*‖mellin F (t*I)‖,
    integral_nonneg (fun t => by positivity),?_⟩
  intro N hN
  simp only [scaled_mellin_norm F N _ hN]
  exact ⟨hi,True.intro⟩

#print axioms polynomial_integrable
#print axioms linear_mass
end XiPrime8845.PRZZMellinMoment

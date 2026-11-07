import PRZZSourceWDerivatives
import PRZZSmoothWeights

/-! The W(k*x^2) factor in the real post-Poisson weight. Its first scaled
derivative is supplied from sourceW, uniformly in k and sigma with explicit
sigma dependence. This is not the full oscillatory weight's IBP estimate. -/
noncomputable section
open scoped ContDiff
namespace XiPrime8845.PRZZPoissonWDerivative
open PRZZDyadicEnvelope PRZZSourceWDerivatives

def quadratic (sigma : ℂ) (k x : ℝ) : ℂ := sourceW sigma (k*x^2)

theorem quadratic_hasDerivAt (sigma : ℂ) (hs : sigma ≠ 0)
    (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    HasDerivAt (quadratic sigma k) (((2*k*x:ℝ):ℂ)*jet sigma 0 (k*x^2)) x := by
  change HasDerivAt (fun y : ℝ => sourceW sigma (k*y^2)) _ x
  have h := (source_hasDerivAt sigma hs (k*x^2) (by positivity)).scomp x
    (((hasDerivAt_id x).pow 2).const_mul k)
  simpa [quadratic,Function.comp_def,Complex.real_smul,
    mul_assoc,mul_comm,mul_left_comm] using h

theorem quadratic_scaled_decay (a : ℝ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 →
    ∀ k x : ℝ, 0 < k → 0 < x →
    ‖(x:ℂ)*deriv (quadratic sigma k) x‖ ≤
      2*(C+D/‖sigma‖^2)*(k*x^2)^(-a) := by
  obtain ⟨C,D,hC,hD,h⟩ := source_derivative_decay 0 a
  refine ⟨C,D,hC,hD,?_⟩
  intro sigma hs k x hk hx
  have hy : 0 < k*x^2 := by positivity
  have hh := h sigma hs (k*x^2) hy
  rw [source_iterated sigma hs 0 (k*x^2) hy] at hh
  simp only [zero_add,pow_one] at hh
  rw [(quadratic_hasDerivAt sigma hs k x hk hx).deriv]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx,abs_of_pos hk]
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(k*x^2) by positivity)
  convert hh' using 1 <;> first | rfl | (field_simp <;> ring)

#print axioms quadratic_hasDerivAt
#print axioms quadratic_scaled_decay

/-- A fixed smooth compact cutoff supplies the constants for the actual
cutoff times W(k*x^2), before the cutoff scale, k, sigma and x are chosen. -/
theorem cutoff_scaled_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : HasCompactSupport F) (a : ℝ) (ha : 0 < a) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ sigma : ℂ, sigma ≠ 0 →
    ∀ N k x : ℝ, 0 < k → 0 < x →
    ‖(x:ℂ)*deriv (fun y => PRZZMellinSeparation.scaledCutoff F N y*quadratic sigma k y) x‖ ≤
      (C+D/‖sigma‖^2)*(k*x^2)^(-a) := by
  obtain ⟨E0,E1,hE0,hE1,hE⟩ := PRZZSmoothWeights.cutoff_bounds F hF hsF
  obtain ⟨C0,D0,hC0,hD0,h0⟩ := source_all_decay 0 a ha
  obtain ⟨C1,D1,hC1,hD1,h1⟩ := quadratic_scaled_decay a
  refine ⟨E1*C0+2*E0*C1,E1*D0+2*E0*D1,by positivity,by positivity,?_⟩
  intro sigma hs N k x hk hx
  have hq := quadratic_hasDerivAt sigma hs k x hk hx
  have hf := PRZZSmoothWeights.scaled_hasDerivAt F hF N x
  have hprod := hf.differentiableAt.hasDerivAt.mul hq.differentiableAt.hasDerivAt
  change HasDerivAt (fun y => PRZZMellinSeparation.scaledCutoff F N y*quadratic sigma k y) _ x at hprod
  rw [hprod.deriv]
  have he : (x:ℂ)*(deriv (PRZZMellinSeparation.scaledCutoff F N) x*quadratic sigma k x+
      PRZZMellinSeparation.scaledCutoff F N x*deriv (quadratic sigma k) x) =
      ((x:ℂ)*deriv (PRZZMellinSeparation.scaledCutoff F N) x)*quadratic sigma k x+
      PRZZMellinSeparation.scaledCutoff F N x*((x:ℂ)*deriv (quadratic sigma k) x) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hb0 : ‖quadratic sigma k x‖ ≤ (C0+D0/‖sigma‖^2)*(k*x^2)^(-a) := by
    simpa [quadratic] using h0 sigma hs (k*x^2) (by positivity)
  have hh := add_le_add
    (mul_le_mul (hE N x).2 hb0 (norm_nonneg _) hE1)
    (mul_le_mul (hE N x).1 (h1 sigma hs k x hk hx) (norm_nonneg _) hE0)
  convert hh using 1 <;> first | rfl | ((try simp only [norm_mul]) <;> ring)

#print axioms cutoff_scaled_decay
end XiPrime8845.PRZZPoissonWDerivative

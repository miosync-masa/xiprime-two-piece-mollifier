import PRZZSmoothMellin
import PRZZTypeIWeights

/-! Fixed smooth cutoffs supply uniform scaled Type I cutoff bounds.
Constants are chosen before N, kappa, x and the complex exponent. The
remaining power/log estimates and arithmetic coprimality sums are separate. -/
noncomputable section
open scoped ContDiff
open Set Complex
namespace XiPrime8845.PRZZSmoothWeights
open PRZZMellinSeparation PRZZTypeIWeights
set_option maxHeartbeats 1000000

theorem scaled_hasDerivAt (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (N x : ℝ) :
    HasDerivAt (scaledCutoff F N)
      ((N⁻¹:ℝ) • deriv F (N⁻¹*x)) x := by
  exact ((hf.differentiable (by simp)).differentiableAt.hasDerivAt).scomp x
    (by simpa only [mul_one,id_eq] using (hasDerivAt_id x).const_mul N⁻¹)

theorem scaled_deriv (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (N x : ℝ) :
    deriv (scaledCutoff F N) x = (N⁻¹:ℝ) • deriv F (N⁻¹*x) :=
  (scaled_hasDerivAt F hf N x).deriv

theorem cutoff_bounds (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ N x : ℝ,
      ‖scaledCutoff F N x‖ ≤ C0 ∧ ‖(x:ℂ)*deriv (scaledCutoff F N) x‖ ≤ C1 := by
  obtain ⟨C0,h0⟩ := hs.exists_bound_of_continuous hf.continuous
  have hc : Continuous (fun x : ℝ => (x:ℂ)*deriv F x) :=
    Complex.continuous_ofReal.mul (hf.continuous_deriv (by simp))
  have hcs : HasCompactSupport (fun x : ℝ => (x:ℂ)*deriv F x) := hs.deriv.mul_left
  obtain ⟨C1,h1⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨C0,C1,(norm_nonneg _).trans (h0 0),(norm_nonneg _).trans (h1 0),?_⟩
  intro N x
  refine ⟨h0 _,?_⟩
  rw [scaled_deriv F hf N x]
  have he : (x:ℂ)*((N⁻¹:ℝ) • deriv F (N⁻¹*x)) =
      (N⁻¹*x:ℝ)*deriv F (N⁻¹*x) := by
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he]
  exact h1 _

/-- Supplies the two previously explicit cutoff envelopes in the actual
power/log/cutoff derivative. No Mellin or derivative bound is assumed. -/
theorem source_bound_uniform (F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ N kappa x : ℝ, ∀ z : ℂ, ∀ j : ℕ,
      ∀ P L : ℝ, 0 < x → 0 ≤ P → 0 ≤ L → ‖(x:ℂ)^z‖ ≤ P → |Real.log x| ≤ L →
      ‖(x:ℂ)*deriv (sourceWeight z j kappa (scaledCutoff F N)) x‖ ≤
        P*((‖z‖*L^j+(j:ℝ)*L^(j-1))*C0+L^j*C1) := by
  obtain ⟨C0,C1,h0,h1,h⟩ := cutoff_bounds F hf hs
  refine ⟨C0,C1,h0,h1,?_⟩
  intro N kappa x z j P L hx hP hL hp hl
  have hd := source_hasDerivAt z j kappa x (scaledCutoff F N) (deriv (scaledCutoff F N)) hx
    ((scaled_hasDerivAt F hf N (kappa*x)).differentiableAt.hasDerivAt)
  rw [hd.deriv]
  exact source_derivative_bound z j kappa x _ _ P L C0 C1 hx hP hL h0 h1 hp hl
    (h N (kappa*x)).1 (by simpa only [Complex.ofReal_mul] using (h N (kappa*x)).2)

#print axioms scaled_hasDerivAt
#print axioms scaled_deriv
#print axioms cutoff_bounds
#print axioms source_bound_uniform
end XiPrime8845.PRZZSmoothWeights

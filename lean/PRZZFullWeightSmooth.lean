import PRZZPoissonWDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! The complete frozen-time spatial weight, with cutoff, complex power,
reciprocal phase and the actual sourceW. Every ordinary derivative is bounded
on a fixed positive compact interval. Constants here may depend on all fixed
parameters: this is not yet a height-uniform quantitative IBP estimate. -/
noncomputable section
open scoped ContDiff
open Set Polynomial
namespace XiPrime8845.PRZZFullWeightSmooth
open PRZZDyadicEnvelope PRZZSourceWDerivatives PRZZLogDerivatives

theorem scaled_smooth (n : ℕ) (P : Polynomial ℝ) :
    ContDiffOn ℝ ∞ (scaled n P) (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp : ContDiff ℝ ∞ (fun y : ℝ => P.eval y) := by
    simpa using P.contDiff_aeval (𝕜 := ℝ) ∞
  have hpx : ContDiffWithinAt ℝ ∞ (fun y : ℝ => P.eval (Real.log y)) (Ioi 0) x :=
    hp.contDiffAt.comp_contDiffWithinAt x (by fun_prop)
  unfold scaled PRZZGaussianDerivatives.weighted
  exact (hpx.mul (by fun_prop)).div (by fun_prop) (pow_ne_zero _ hx0)

theorem jet_smooth (sigma : ℂ) (n : ℕ) :
    ContDiffOn ℝ ∞ (jet sigma n) (Ioi 0) := by
  unfold jet
  exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn (scaled_smooth _ _)).div_const _).sub
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (scaled_smooth _ _)).div_const _)

theorem source_smooth (sigma : ℂ) (hs : sigma ≠ 0) :
    ContDiffOn ℝ ∞ (sourceW sigma) (Ioi 0) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (source_hasDerivAt sigma hs x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply (jet_smooth sigma 0).congr
  intro x hx
  exact (source_hasDerivAt sigma hs x hx).deriv

/-- exp(-z log x) is the positive-real complex power x^(-z).
omega is the frozen reciprocal phase parameter. -/
def weight (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ) (x : ℝ) : ℂ :=
  F (N⁻¹*x) * Complex.exp (-z*(Real.log x:ℂ)) *
    Complex.exp (Complex.I*(omega/x:ℝ)) * sourceW sigma (k*x^2)

theorem weight_eq (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (x : ℝ) (hx : 0 < x) :
    weight F N k omega z sigma x =
      F (N⁻¹*x) * (x:ℂ)^(-z) * Complex.exp (Complex.I*(omega/x:ℝ)) *
        sourceW sigma (k*x^2) := by
  rw [weight, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.ofReal_log hx.le, mul_comm (-z)]

theorem weight_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hk : 0 < k) (hs : sigma ≠ 0) :
    ContDiffOn ℝ ∞ (weight F N k omega z sigma) (Ioi 0) := by
  have hw : ContDiffOn ℝ ∞ (fun x : ℝ => sourceW sigma (k*x^2)) (Ioi 0) :=
    (source_smooth sigma hs).comp (by fun_prop) (by
      intro x hx
      have hx' : 0 < x := hx
      change 0 < k*x^2
      positivity)
  unfold weight
  apply ContDiffOn.mul _ hw
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hf : ContDiffWithinAt ℝ ∞ (fun y : ℝ => F (N⁻¹*y)) (Ioi 0) x :=
    (hF.comp (contDiff_const.mul contDiff_id)).contDiffAt.contDiffWithinAt
  have hl : ContDiffWithinAt ℝ ∞ (fun y : ℝ => (Real.log y:ℂ)) (Ioi 0) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt x
      (Real.contDiffAt_log.mpr hx0).contDiffWithinAt
  have ho : ContDiffWithinAt ℝ ∞ (fun y : ℝ => (omega/y:ℝ) : ℝ → ℂ) (Ioi 0) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt x
      (contDiffWithinAt_const.div contDiffWithinAt_id hx0)
  exact (hf.mul (by fun_prop)).mul (by fun_prop)

theorem weight_iterated_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hk : 0 < k) (hs : sigma ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n (weight F N k omega z sigma)) (Ioi 0) := by
  induction n with
  | zero => simpa using weight_smooth F hF N k omega z sigma hk hs
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- All factors are differentiated together. This bound supplies existence
of the derivative envelope, rather than assuming derivative norms as input. -/
theorem weight_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hk : 0 < k) (hs : sigma ≠ 0)
    (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b,
      ‖iteratedDeriv n (weight F N k omega z sigma) x‖ ≤ C := by
  have hc := (weight_iterated_smooth F hF N k omega z sigma hk hs n).continuousOn
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (fun x hx => ha.trans_le hx.1))
  exact ⟨max C 0,le_max_right _ _,fun x hx => (hC x hx).trans (le_max_left _ _)⟩

#print axioms source_smooth
#print axioms weight_eq
#print axioms weight_smooth
#print axioms weight_iterated_smooth
#print axioms weight_derivative_bound
end XiPrime8845.PRZZFullWeightSmooth

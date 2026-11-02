import Mathlib.Analysis.Fourier.PoissonSummation

/-! Exact Poisson summation on a residue progression for smooth compact
weights, including the modulus Jacobian, reciprocal frequency and explicit
residue phase. No identification with the actual AFE kernel or A* is asserted.
There is no assumed Poisson formula or Fourier-decay premise. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace
open Complex Real
namespace XiPrime8845.PRZZL1Poisson
set_option maxHeartbeats 2000000

def scaled (f : ℝ → ℂ) (q : ℝ) (x : ℝ) : ℂ := f (q*x)

theorem progression (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (q a : ℝ) (hq : q ≠ 0) :
    (∑' n : ℤ, f (a+q*n)) =
      ∑' n : ℤ, 𝓕 (scaled f q) n * fourier n ((a/q : ℝ) : UnitAddCircle) := by
  have hc : HasCompactSupport (scaled f q) := by
    change HasCompactSupport (fun x => f (q*x))
    exact hs.comp_homeomorph (Homeomorph.mulLeft₀ q hq)
  have hd : ContDiff ℝ ∞ (scaled f q) := hf.comp (contDiff_const.mul contDiff_id)
  have h := (hc.toSchwartzMap hd).tsum_eq_tsum_fourier (a/q)
  simp only [SchwartzMap.fourier_coe] at h
  have he : (hc.toSchwartzMap hd : ℝ → ℂ) = scaled f q := rfl
  rw [he] at h
  convert h using 1
  apply tsum_congr
  intro n
  change f (a+q*n) = f (q*(a/q+n))
  congr 1
  field_simp

#print axioms progression

/-- The modulus Jacobian and reciprocal frequency, with no decay premise. -/
theorem scaled_fourier (f : ℝ → ℂ) (q ξ : ℝ) (hq : 0 < q) :
    𝓕 (scaled f q) ξ = q⁻¹ • 𝓕 f (ξ/q) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have he : (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I)) •
      scaled f q x) =
      (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * ⟪q*x, ξ/q⟫) * Complex.I)) • f (q*x)) := by
    funext x
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    field_simp
  rw [he]
  simpa only [abs_of_pos (inv_pos.mpr hq)] using
    MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => Complex.exp ((↑(-2 * Real.pi * ⟪y, ξ/q⟫) * Complex.I)) • f y) q

#print axioms scaled_fourier

/-- Explicit residue phase and modulus normalization. This still requires
identifying the actual AFE weight before it can be used for A*. -/
theorem progression_normalized (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (q a : ℝ) (hq : 0 < q) :
    (∑' n : ℤ, f (a+q*n)) =
      ∑' n : ℤ, ((q⁻¹:ℝ):ℂ) * 𝓕 f ((n:ℝ)/q) *
        Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(a:ℂ)/(q:ℂ)) := by
  rw [progression f hf hs q a hq.ne']
  apply tsum_congr
  intro n
  rw [scaled_fourier f q n hq, fourier_coe_apply]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, div_one]
  congr 2; ring

#print axioms progression_normalized
end XiPrime8845.PRZZL1Poisson

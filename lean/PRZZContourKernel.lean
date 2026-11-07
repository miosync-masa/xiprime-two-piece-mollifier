import PRZZAFEDual
import PRZZGammaPath

/-! Identification of the completed contour with the actual Gamma-ratio
integrand and its possible poles. This does not move the contour or bound
the residues of the four noncentral poles. -/
noncomputable section
open Complex Set
namespace XiPrime8845.PRZZContourKernel
open PRZZAFEDual PRZZAFEGamma PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem gammaRatio_pair (a b s : ℂ) (t : ℝ) :
    gammaRatio a b s t = gammaPair (a+s) (b+s) t/gammaPair a b t := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : -(1+(a+s)+(b+s))/2 = -s+(-(1+a+b)/2) := by ring
  have hp : (Real.pi:ℂ)^(-(1+a+b)/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  rw [gammaPair_formula,gammaPair_formula,he,Complex.cpow_add _ _ hpi]
  unfold gammaRatio leftArg rightArg
  have h1 : 1/2+(a+s)+(t:ℂ)*I = 1/2+a+s+(t:ℂ)*I := by ring
  have h2 : 1/2+(b+s)-(t:ℂ)*I = 1/2+b+s-(t:ℂ)*I := by ring
  rw [h1,h2]
  field_simp

theorem completed_factor (z : ℂ) (hz : 0 < z.re) :
    completedRiemannZeta z = Gammaℝ z*riemannZeta z := by
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  rw [riemannZeta_def_of_ne_zero hn]
  field_simp [Gammaℝ_ne_zero_of_re_pos hz]

/-- Exact pointwise identification, including all pi/Gamma factors.
On Re s=2 the two positivity conditions follow from small shifts. -/
theorem numerator_eq_actual (a b s : ℂ) (t : ℝ)
    (ha : 0 < (leftArg a t+s).re) (hb : 0 < (rightArg b t+s).re) :
    contourNumerator a b s t = exp (s^2)*annihilator (a+b) s*
      gammaRatio a b s t*
        (riemannZeta (leftArg a t+s)*riemannZeta (rightArg b t+s)) := by
  have h1 : leftArg (a+s) t = leftArg a t+s := by unfold leftArg; ring
  have h2 : rightArg (b+s) t = rightArg b t+s := by unfold rightArg; ring
  rw [contourNumerator,completedPair,completed_factor _ ha,completed_factor _ hb,
    gammaRatio_pair]
  simp only [gammaPair,h1,h2]
  ring

def poles (a b : ℂ) (t : ℝ) : Set ℂ :=
  {0,-leftArg a t,1-leftArg a t,-rightArg b t,1-rightArg b t}

/-- The four shifted completed-zeta poles and the central Mellin pole
are an exhaustive possible-pole set, not a claim that each survives. -/
theorem contour_differentiable (a b s : ℂ) (t : ℝ) (hs : s ∉ poles a b t) :
    DifferentiableAt ℂ (fun w => contourNumerator a b w t/w) s := by
  have hs0 : s ≠ 0 := by intro h; apply hs; simp [poles,h]
  have hzero (z : ℂ) (hz : s ≠ -z) : z+s ≠ 0 := by
    intro h; apply hz; linear_combination h
  have hone (z : ℂ) (hz : s ≠ 1-z) : z+s ≠ 1 := by
    intro h; apply hz; linear_combination h
  have hla : s ≠ -leftArg a t := by intro h; apply hs; simp [poles,h]
  have hlb : s ≠ 1-leftArg a t := by intro h; apply hs; simp [poles,h]
  have hra : s ≠ -rightArg b t := by intro h; apply hs; simp [poles,h]
  have hrb : s ≠ 1-rightArg b t := by intro h; apply hs; simp [poles,h]
  have hl := (differentiableAt_completedZeta (hzero _ hla) (hone _ hlb)).comp s
    ((differentiableAt_const _).add differentiableAt_id)
  have hr := (differentiableAt_completedZeta (hzero _ hra) (hone _ hrb)).comp s
    ((differentiableAt_const _).add differentiableAt_id)
  unfold contourNumerator completedPair annihilator
  exact (((((differentiableAt_id.pow 2).cexp.mul
    (((differentiableAt_const _).sub (((differentiableAt_const _).mul differentiableAt_id).pow 2)).div_const _)).mul
    (hl.mul hr)).div_const _).div differentiableAt_id hs0)

/-- An exact expansion exposing both poles of each completed zeta factor.
It retains all cross terms and remains valid at Lean's totalized values. -/
theorem completedPair_pole_expansion (a b s : ℂ) (t : ℝ) :
    completedPair a b s t =
      (completedRiemannZeta₀ (leftArg a t+s)-1/(leftArg a t+s)-1/(1-(leftArg a t+s)))*
      (completedRiemannZeta₀ (rightArg b t+s)-1/(rightArg b t+s)-1/(1-(rightArg b t+s))) := by
  unfold completedPair
  rw [completedRiemannZeta_eq,completedRiemannZeta_eq]

#print axioms gammaRatio_pair
#print axioms completed_factor
#print axioms numerator_eq_actual
#print axioms contour_differentiable
#print axioms completedPair_pole_expansion
end XiPrime8845.PRZZContourKernel

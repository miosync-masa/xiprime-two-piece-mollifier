import PRZZAFEGamma
import PRZZL1Residue
import PRZZAStar

/-! Exact functional-equation and residue-phase bookkeeping for L1.
The dual multiplier is a quotient of actual Gamma factors. No contour
shift, pole remainder bound, or identification of the AFE Fourier weight
with the A* integral is asserted by these identities. -/
noncomputable section
open Complex
open scoped FourierTransform ContDiff
namespace XiPrime8845.PRZZAFEDual
set_option maxHeartbeats 2000000

def leftArg (a : ℂ) (t : ℝ) : ℂ := 1/2+a+t*I
def rightArg (b : ℂ) (t : ℝ) : ℂ := 1/2+b-t*I
def gammaPair (a b : ℂ) (t : ℝ) : ℂ := Gammaℝ (leftArg a t)*Gammaℝ (rightArg b t)
def dualMultiplier (a b : ℂ) (t : ℝ) : ℂ := gammaPair (-b) (-a) t/gammaPair a b t
def completedPair (a b s : ℂ) (t : ℝ) : ℂ :=
  completedRiemannZeta (leftArg a t+s)*completedRiemannZeta (rightArg b t+s)

theorem gammaPair_formula (a b : ℂ) (t : ℝ) :
    gammaPair a b t = (Real.pi:ℂ)^(-(1+a+b)/2)*
      (Gamma (leftArg a t/2)*Gamma (rightArg b t/2)) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : -(1+a+b)/2 = -(leftArg a t)/2-(rightArg b t)/2 := by
    unfold leftArg rightArg; ring
  rw [he,sub_eq_add_neg,Complex.cpow_add _ _ hpi]
  unfold gammaPair Gammaℝ
  ring

/-- The explicit multiplier in Pratt--Robles (2.4), with the two numerator
Gamma factors commuted to the (-b,-a) direct-term convention. -/
theorem dualMultiplier_formula (a b : ℂ) (t : ℝ) :
    dualMultiplier a b t = (Real.pi:ℂ)^(a+b)*
      (Gamma (leftArg (-b) t/2)*Gamma (rightArg (-a) t/2)) /
      (Gamma (leftArg a t/2)*Gamma (rightArg b t/2)) := by
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : -(1+-b+-a)/2 = (a+b)+(-(1+a+b)/2) := by ring
  rw [dualMultiplier,gammaPair_formula,gammaPair_formula,he,
    Complex.cpow_add _ _ hpi]
  have hp : (Real.pi:ℂ)^(-(1+a+b)/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  field_simp

theorem reflected_arguments (a b s : ℂ) (t : ℝ) :
    leftArg (-b) t-s = 1-(rightArg b t+s) ∧
    rightArg (-a) t-s = 1-(leftArg a t+s) := by
  constructor <;> unfold leftArg rightArg <;> ring

/-- The reflection needed on the shifted contour, before any integration. -/
theorem completed_reflection (a b s : ℂ) (t : ℝ) :
    completedPair a b s t = completedPair (-b) (-a) (-s) t := by
  have h := reflected_arguments a b s t
  simp only [completedPair,← sub_eq_add_neg,h.1,h.2,completedRiemannZeta_one_sub]
  ring

theorem gammaPair_ne_zero (a b : ℂ) (t : ℝ)
    (ha : 0 < (leftArg a t).re) (hb : 0 < (rightArg b t).re) :
    gammaPair a b t ≠ 0 := by
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos ha) (Gammaℝ_ne_zero_of_re_pos hb)

/-- Pointwise functional equation with the actual dual Gamma quotient.
This is not the approximate functional equation (no Mellin contour yet). -/
theorem zeta_product_reflection (a b : ℂ) (t : ℝ)
    (ha : 0 < (leftArg a t).re) (hb : 0 < (rightArg b t).re)
    (ha' : 0 < (leftArg (-b) t).re) (hb' : 0 < (rightArg (-a) t).re) :
    riemannZeta (leftArg a t)*riemannZeta (rightArg b t) =
      dualMultiplier a b t*
        (riemannZeta (leftArg (-b) t)*riemannZeta (rightArg (-a) t)) := by
  have hn (z : ℂ) (hz : 0 < z.re) : z ≠ 0 := by
    intro h; simp [h] at hz
  rw [riemannZeta_def_of_ne_zero (hn _ ha),riemannZeta_def_of_ne_zero (hn _ hb),
    riemannZeta_def_of_ne_zero (hn _ ha'),riemannZeta_def_of_ne_zero (hn _ hb')]
  have h := completed_reflection a b 0 t
  simp only [completedPair,add_zero,neg_zero] at h
  simp only [dualMultiplier,gammaPair]
  rw [← mul_div_mul_comm,← mul_div_mul_comm,← h]
  have hg := gammaPair_ne_zero (-b) (-a) t ha' hb'
  unfold gammaPair at hg
  field_simp [Gammaℝ_ne_zero_of_re_pos ha, Gammaℝ_ne_zero_of_re_pos hb,
    Gammaℝ_ne_zero_of_re_pos ha', Gammaℝ_ne_zero_of_re_pos hb']

/-- The annihilator is unchanged by simultaneous dual reflection. -/
theorem annihilator_reflection (a b s : ℂ) :
    PRZZDyadicEnvelope.annihilator (-b+-a) (-s) =
      PRZZDyadicEnvelope.annihilator (a+b) s := by
  unfold PRZZDyadicEnvelope.annihilator
  congr 1 <;> ring

def contourNumerator (a b s : ℂ) (t : ℝ) : ℂ :=
  exp (s^2)*PRZZDyadicEnvelope.annihilator (a+b) s*completedPair a b s t /
    gammaPair a b t

/-- Exact reflected contour numerator, including the dual multiplier.
Division by the reflected Mellin variable introduces a minus sign. -/
theorem contour_reflection (a b s : ℂ) (t : ℝ)
    (ha : 0 < (leftArg (-b) t).re) (hb : 0 < (rightArg (-a) t).re) :
    contourNumerator a b s t = dualMultiplier a b t*contourNumerator (-b) (-a) (-s) t := by
  have hg := gammaPair_ne_zero (-b) (-a) t ha hb
  unfold contourNumerator dualMultiplier
  rw [neg_sq,annihilator_reflection,← completed_reflection]
  field_simp

theorem contour_integrand_reflection (a b s : ℂ) (t : ℝ)
    (ha : 0 < (leftArg (-b) t).re) (hb : 0 < (rightArg (-a) t).re) :
    contourNumerator a b s t/s =
      -(dualMultiplier a b t*(contourNumerator (-b) (-a) (-s) t/(-s))) := by
  rw [contour_reflection a b s t ha hb]
  ring

theorem contourNumerator_zero (a b : ℂ) (t : ℝ) (hs : a+b ≠ 0)
    (ha : leftArg a t ≠ 0) (hb : rightArg b t ≠ 0) :
    contourNumerator a b 0 t = riemannZeta (leftArg a t)*riemannZeta (rightArg b t) := by
  rw [riemannZeta_def_of_ne_zero ha,riemannZeta_def_of_ne_zero hb]
  simp [contourNumerator,PRZZDyadicEnvelope.annihilator,hs,completedPair,gammaPair,
    mul_div_mul_comm]

/-- The residue at the central Mellin pole is the literal zeta product.
The other crossed poles and the horizontal contour limits are separate. -/
theorem central_residue (a b : ℂ) (t : ℝ) (hs : a+b ≠ 0)
    (ha : leftArg a t ≠ 0) (hb : rightArg b t ≠ 0)
    (ha1 : leftArg a t ≠ 1) (hb1 : rightArg b t ≠ 1) :
    Filter.Tendsto (fun s : ℂ => s*(contourNumerator a b s t/s))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (riemannZeta (leftArg a t)*riemannZeta (rightArg b t))) := by
  have hc : ContinuousAt (fun s : ℂ => contourNumerator a b s t) 0 := by
    have hl0 : ContinuousAt completedRiemannZeta (leftArg a t+(0:ℂ)) := by
      simpa using (differentiableAt_completedZeta ha ha1).continuousAt
    have hr0 : ContinuousAt completedRiemannZeta (rightArg b t+(0:ℂ)) := by
      simpa using (differentiableAt_completedZeta hb hb1).continuousAt
    have hleft : ContinuousAt (fun s : ℂ => completedRiemannZeta (leftArg a t+s)) 0 :=
      hl0.comp (continuousAt_const.add continuousAt_id)
    have hright : ContinuousAt (fun s : ℂ => completedRiemannZeta (rightArg b t+s)) 0 :=
      hr0.comp (continuousAt_const.add continuousAt_id)
    unfold contourNumerator completedPair PRZZDyadicEnvelope.annihilator
    exact (((continuousAt_id.pow 2).cexp.mul
      ((continuousAt_const.sub ((continuousAt_const.mul continuousAt_id).pow 2)).div_const _)).mul
        (hleft.mul hright)).div_const _
  have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rw [contourNumerator_zero a b t hs ha hb] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs0
  have hn : s ≠ 0 := by simpa using hs0
  field_simp

/-- For the existing directTerm convention Delta = k*r-m*n.
This fixes the inverse-residue sign without changing the AFE indices. -/
theorem offDiagonal_residue (m k n r : ℕ) :
    (n:ZMod r)*(m:ZMod r) = -(((k:ℤ)*r-(m:ℤ)*n:ℤ):ZMod r) := by
  push_cast
  simp only [ZMod.natCast_self,mul_zero,zero_sub,neg_neg]
  ring

theorem offDiagonal_inverse (m k n r : ℕ) (hn : n.Coprime r) :
    (m:ZMod r) = -(((k:ℤ)*r-(m:ℤ)*n:ℤ):ZMod r)*(n:ZMod r)⁻¹ :=
  (PRZZL1Residue.residue_iff n r hn _ _).mp (offDiagonal_residue m k n r)

/-- The exact phase in the literal A* prefactor is the Poisson residue
phase for the actual off-diagonal difference. The Fourier weight is kept. -/
theorem offDiagonal_poisson (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (m k n r : ℕ) (hr : 0 < r) :
    (∑' z : ℤ, f (-((k:ℝ)*r-(m:ℝ)*n)*PRZZKloostermanInputs.inverseResidue r n+(r:ℝ)*z)) =
      ∑' h : ℤ, (((r:ℝ)⁻¹:ℝ):ℂ)*𝓕 f ((h:ℝ)/r)*
        PRZZKloostermanInputs.e
          (-((h:ℝ)*((k:ℝ)*r-(m:ℝ)*n))*PRZZKloostermanInputs.inverseResidue r n/r) := by
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
    PRZZL1Residue.poisson_inverse_progression f hf hs r n hr ((k:ℤ)*r-(m:ℤ)*n)

#print axioms reflected_arguments
#print axioms gammaPair_formula
#print axioms dualMultiplier_formula
#print axioms completed_reflection
#print axioms gammaPair_ne_zero
#print axioms zeta_product_reflection
#print axioms annihilator_reflection
#print axioms contourNumerator_zero
#print axioms central_residue
#print axioms contour_reflection
#print axioms contour_integrand_reflection
#print axioms offDiagonal_residue
#print axioms offDiagonal_inverse
#print axioms offDiagonal_poisson
end XiPrime8845.PRZZAFEDual

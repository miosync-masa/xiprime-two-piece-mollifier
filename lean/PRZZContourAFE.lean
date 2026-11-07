import PRZZInfiniteContour

/-! Contour form of the AFE, with the actual dual Gamma multiplier and
all noncentral residues retained. Identification of the positive integral
with the arithmetic double series is a separate step. -/
noncomputable section
open Complex MeasureTheory
open scoped BigOperators
namespace XiPrime8845.PRZZContourAFE
open PRZZAFEDual PRZZFiniteContour
set_option maxHeartbeats 2000000

def positiveIntegral (a b : ℂ) (t : ℝ) : ℂ :=
  (1/(2*(Real.pi:ℂ)))*(∫ v : ℝ, integrand a b t ((2:ℂ)+(v:ℂ)*I))

def noncentralSum (a b : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (poleSet a b t).erase 0, residue (integrand a b t) p

/-- Reflection of the entire left line, including its Mellin minus sign.
The real change of variables does not introduce an additional sign. -/
theorem left_integral (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) :
    (∫ v : ℝ, integrand a b t ((-2:ℂ)+(v:ℂ)*I)) =
      -(dualMultiplier a b t *
        (∫ v : ℝ, integrand (-b) (-a) t ((2:ℂ)+(v:ℂ)*I))) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have ha' : 0 < (leftArg (-b) t).re := by simp [leftArg]; linarith
  have hb' : 0 < (rightArg (-a) t).re := by simp [rightArg]; linarith
  have he : (fun v : ℝ => integrand a b t ((-2:ℂ)+(v:ℂ)*I)) =
      (fun v : ℝ => -(dualMultiplier a b t *
        integrand (-b) (-a) t ((2:ℂ)+((-v:ℝ):ℂ)*I))) := by
    funext v
    have hh := contour_integrand_reflection a b ((-2:ℂ)+(v:ℂ)*I) t ha' hb'
    have hv : -((-2:ℂ)+(v:ℂ)*I) = (2:ℂ)+((-v:ℝ):ℂ)*I := by push_cast; ring
    simpa only [integrand,hv] using hh
  rw [he,integral_neg,integral_const_mul]
  congr 1
  congr 1
  exact integral_neg_eq_self (fun v : ℝ => integrand (-b) (-a) t ((2:ℂ)+(v:ℂ)*I)) volume

theorem central_value (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) :
    residue (integrand a b t) 0 =
      riemannZeta (leftArg a t)*riemannZeta (rightArg b t) := by
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hla : leftArg a t ≠ 0 ∧ leftArg a t ≠ 1 := by
    constructor <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [leftArg] at hh <;> linarith
  have hrb : rightArg b t ≠ 0 ∧ rightArg b t ≠ 1 := by
    constructor <;> intro he <;> have hh := congrArg Complex.re he <;>
      simp [rightArg] at hh <;> linarith
  apply residue_eq_of_tendsto
  simpa [integrand] using central_residue a b t hs hla.1 hrb.1 hla.2 hrb.2

/-- An actual contour identity, not an assumed AFE. The pole remainder
is subtracted, rather than discarded as if the annihilator killed it. -/
theorem contour_afe (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) :
    riemannZeta (leftArg a t)*riemannZeta (rightArg b t) =
      positiveIntegral a b t + dualMultiplier a b t*positiveIntegral (-b) (-a) t -
        noncentralSum a b t := by
  have h := PRZZInfiniteContour.infinite_rectangle a b ha hb hs t ht
  rw [left_integral a b t ha hb] at h
  have hz : (0:ℂ) ∈ poleSet a b t := by simp [poleSet]
  have hsum := Finset.sum_erase_add (poleSet a b t)
    (fun p => residue (integrand a b t) p) hz
  rw [central_value a b t ha hb hs] at hsum
  change noncentralSum a b t + _ = _ at hsum
  rw [← hsum] at h
  unfold positiveIntegral
  linear_combination -h

#print axioms left_integral
#print axioms central_value
#print axioms contour_afe
end XiPrime8845.PRZZContourAFE

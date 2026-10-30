import ExpandedRegularity
import ZetaMomentIntegral

/-! Exact expanded-support differentiation; all original full-line integrals
and logarithmic chain factors are retained. No PRZZ estimate is used. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set MeasureTheory
namespace XiPrime8845.ExpandedZetaIntegral
open CompactShiftIntegral ArithmeticRegularity PRZZ ZetaMomentIntegral
set_option maxHeartbeats 1000000
def integral (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  ∫ t in Icc (T/2) (5/2*T), momentWeight P Q θ T Phi t • core a b T ((A,B),(t:ℂ))

theorem integral_left_deriv (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    HasDerivAt (fun w => integral a b P Q θ T Phi w B)
      (integral (a+1) b P Q θ T Phi A B) A :=
  compact_deriv _ _ _ _ _ _ negativeShifts_open timeStrip_open (core_smooth a b T hT)
    (ExpandedRegularity.momentWeight_continuous P Q θ T Phi hPhi).continuousOn (ExpandedRegularity.time_segment T (by linarith))
    (fun w => (w,B)) A (1,0) ((hasDerivAt_id A).prodMk (hasDerivAt_const A B)) ⟨hA,hB⟩
    _ (fun t ht => core_left_deriv a b T hT A B _ hA (ExpandedRegularity.time_segment T (by linarith) t ht))

theorem integral_right_deriv (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    HasDerivAt (fun w => integral a b P Q θ T Phi A w)
      (integral a (b+1) P Q θ T Phi A B) B :=
  compact_deriv _ _ _ _ _ _ negativeShifts_open timeStrip_open (core_smooth a b T hT)
    (ExpandedRegularity.momentWeight_continuous P Q θ T Phi hPhi).continuousOn (ExpandedRegularity.time_segment T (by linarith))
    (fun w => (A,w)) B (0,1) ((hasDerivAt_const B A).prodMk (hasDerivAt_id B)) ⟨hA,hB⟩
    _ (fun t ht => core_right_deriv a b T hT A B _ hB (ExpandedRegularity.time_segment T (by linarith) t ht))

theorem integral_zero (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) :
    integral 0 0 P Q θ T Phi A B = twistedMoment P Q θ T Phi A B := by
  rw [twistedMoment,ExpandedGcd.weighted_integral_restrict _ Phi hPhi T (by linarith)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight,core,scaledZeta,iteratedDeriv_zero,pow_zero,div_one,smul_eq_mul]
  ring

/-- The original real-line integral, with the exact total chain factor. -/
theorem integral_eq_full (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) :
    integral a b P Q θ T Phi A B =
      (∫ t : ℝ, iteratedDeriv a riemannZeta (1/2+A/(Real.log T:ℂ)+t*Complex.I) *
        iteratedDeriv b riemannZeta (1/2+B/(Real.log T:ℂ)-t*Complex.I) *
        dirichletPolynomial (coefficient P θ T) (cutoff θ T) (1/2+t*Complex.I) *
        star (dirichletPolynomial (coefficient Q θ T) (cutoff θ T) (1/2+t*Complex.I)) *
        (Phi (t/T):ℂ))/(Real.log T:ℂ)^(a+b) := by
  rw [ExpandedGcd.weighted_integral_restrict _ Phi hPhi T (by linarith),← integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight,core,scaledZeta,smul_eq_mul,pow_add,div_eq_mul_inv,mul_inv_rev]
  ring

theorem integral_iterated_left (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    iteratedDeriv a (fun x => integral 0 b P Q θ T Phi x B) A = integral a b P Q θ T Phi A B := by
  induction a generalizing A with
  | zero => rfl
  | succ a ih =>
    rw [iteratedDeriv_succ]
    have he : (fun x => iteratedDeriv a (fun w => integral 0 b P Q θ T Phi w B) x) =ᶠ[nhds A]
        (fun x => integral a b P Q θ T Phi x B) := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hA] with x hx
      exact ih x hx
    rw [he.deriv_eq]
    exact (integral_left_deriv a b P Q θ T Phi hPhi hT A B hA hB).deriv

theorem integral_iterated_right (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    iteratedDeriv b (fun y => integral a 0 P Q θ T Phi A y) B = integral a b P Q θ T Phi A B := by
  induction b generalizing B with
  | zero => rfl
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have he : (fun y => iteratedDeriv b (fun w => integral a 0 P Q θ T Phi A w) y) =ᶠ[nhds B]
        (fun y => integral a b P Q θ T Phi A y) := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hB] with y hy
      exact ih y hy
    rw [he.deriv_eq]
    exact (integral_right_deriv a b P Q θ T Phi hPhi hT A B hA hB).deriv

/-- Independent derivative orders and their exact logarithmic chain factors. -/
theorem twistedMoment_mixed_deriv (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    iteratedDeriv a (fun x => iteratedDeriv b (twistedMoment P Q θ T Phi x) B) A =
      integral a b P Q θ T Phi A B := by
  have he : (fun x => iteratedDeriv b (twistedMoment P Q θ T Phi x) B) =ᶠ[nhds A]
      (fun x => integral 0 b P Q θ T Phi x B) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hA] with x hx
    have hf : twistedMoment P Q θ T Phi x = (fun y => integral 0 0 P Q θ T Phi x y) :=
      funext (fun y => (integral_zero P Q θ T Phi hPhi hT x y).symm)
    rw [hf]
    exact integral_iterated_right 0 b P Q θ T Phi hPhi hT x B hx hB
  rw [he.iteratedDeriv_eq a]
  exact integral_iterated_left a b P Q θ T Phi hPhi hT A B hA hB


#print axioms integral_left_deriv
#print axioms integral_right_deriv
#print axioms integral_zero
#print axioms integral_eq_full
#print axioms twistedMoment_mixed_deriv
end XiPrime8845.ExpandedZetaIntegral


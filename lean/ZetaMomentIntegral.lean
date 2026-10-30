import ArithmeticRegularity

/-! Exact differentiation of the literal PRZZ integral. The mollifier and height
weight do not depend on either shift. All identities retain finite T and the
original support; no asymptotic input is used. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set MeasureTheory
namespace XiPrime8845.ZetaMomentIntegral
open CompactShiftIntegral ArithmeticRegularity PRZZ
set_option maxHeartbeats 1000000

theorem zeta_derivative_analytic (n : ℕ) (s : ℂ) (hs : s ≠ 1) :
    AnalyticAt ℂ (iteratedDeriv n riemannZeta) s := by
  induction n with
  | zero => exact analyticOn_riemannZeta s hs
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

def scaledZeta (n : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  iteratedDeriv n riemannZeta s / (Real.log T : ℂ)^n

theorem scaledZeta_smooth (n : ℕ) (T : ℝ) (s : ℂ) (hs : s ≠ 1) :
    ContDiffAt ℂ ∞ (scaledZeta n T) s :=
  (zeta_derivative_analytic n s hs).contDiffAt.div_const _

theorem scaledZeta_shift_deriv (n : ℕ) (T : ℝ) (c A : ℂ)
    (hs : c+A/(Real.log T : ℂ) ≠ 1) :
    HasDerivAt (fun z => scaledZeta n T (c+z/(Real.log T : ℂ)))
      (scaledZeta (n+1) T (c+A/(Real.log T : ℂ))) A := by
  have hd := (zeta_derivative_analytic n _ hs).differentiableAt.hasDerivAt
  -- Use the affine argument, including its logarithmic chain factor.
  have h' := (hd.comp A (((hasDerivAt_id A).div_const (Real.log T : ℂ)).const_add c)).div_const
    ((Real.log T : ℂ)^n)
  convert! h' using 1
  simp only [scaledZeta,iteratedDeriv_succ,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

def core (a b : ℕ) (T : ℝ) (q : Shift × ℂ) : ℂ :=
  scaledZeta a T (1/2+q.1.1/(Real.log T : ℂ)+q.2*Complex.I) *
  scaledZeta b T (1/2+q.1.2/(Real.log T : ℂ)-q.2*Complex.I)

theorem core_smooth (a b : ℕ) (T : ℝ) (hT : 1 < T) :
    ContDiffOn ℂ ∞ (core a b T) (negativeShifts ×ˢ timeStrip) := by
  intro q hq
  unfold core
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.mul
  · exact (scaledZeta_smooth a T _ (zeta_shift_ne_one T hT _ _ hq.1.1 hq.2.2).1).comp q
      (show ContDiffAt ℂ ∞ (fun w : Shift × ℂ => 1/2+w.1.1/(Real.log T:ℂ)+w.2*Complex.I) q by fun_prop)
  · exact (scaledZeta_smooth b T _ (zeta_shift_ne_one T hT _ _ hq.1.2 hq.2.2).2).comp q
      (show ContDiffAt ℂ ∞ (fun w : Shift × ℂ => 1/2+w.1.2/(Real.log T:ℂ)-w.2*Complex.I) q by fun_prop)

/-- Directional differentiation under a compact integral; the proposed
integrand derivative is checked pointwise, not taken as an analytic axiom. -/
theorem compact_deriv (F : Shift × ℂ → ℂ) (c : ℝ → ℂ) (a b : ℝ)
    (U : Set Shift) (V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ ∞ F (U ×ˢ V)) (hc : ContinuousOn c (Icc a b))
    (hseg : ∀ t ∈ Icc a b, (t:ℂ) ∈ V)
    (γ : ℂ → Shift) (z : ℂ) (v : Shift) (hγ : HasDerivAt γ v z) (hz : γ z ∈ U)
    (G : ℝ → ℂ) (hG : ∀ t ∈ Icc a b, HasDerivAt (fun w => F (γ w,(t:ℂ))) (G t) z) :
    HasDerivAt (fun w => ∫ t in Icc a b, c t • F (γ w,(t:ℂ)))
      (∫ t in Icc a b, c t • G t) z := by
  have hd := (compact_integral_hasFDerivAt F c a b U V hU hV hF hc hseg _ hz).comp_hasDerivAt z hγ
  have hi : IntegrableOn (fun t : ℝ => c t • partialMap F (γ z,(t:ℂ))) (Icc a b) := by
    have hh : ContinuousOn (fun t : ℝ => partialMap F (γ z,(t:ℂ))) (Icc a b) :=
      (partialMap_smooth hU hV hF).continuousOn.comp (by fun_prop)
        (fun t ht => ⟨hz,hseg t ht⟩)
    exact (hc.smul hh).integrableOn_compact isCompact_Icc
  have he : (∫ t in Icc a b, c t • partialMap F (γ z,(t:ℂ))) v =
      ∫ t in Icc a b, c t • G t := by
    rw [ContinuousLinearMap.integral_apply hi]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hf := ((hF (γ z,(t:ℂ)) ⟨hz,hseg t ht⟩).contDiffAt
      ((hU.prod hV).mem_nhds ⟨hz,hseg t ht⟩)).differentiableAt (by simp)
    have hh := hf.hasFDerivAt.comp_hasDerivAt z (hγ.prodMk (hasDerivAt_const z (t:ℂ)))
    have heq := hh.unique (hG t ht)
    simpa [partialMap,ContinuousLinearMap.comp_apply] using congrArg (fun w : ℂ => c t • w) heq
  simpa only [Function.comp_def,he] using hd

def integral (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  ∫ t in Icc T (2*T), momentWeight P Q θ T Phi t • core a b T ((A,B),(t:ℂ))

theorem core_left_deriv (a b : ℕ) (T : ℝ) (hT : 1 < T)
    (A B z : ℂ) (hA : A.re < 0) (hz : z ∈ timeStrip) :
    HasDerivAt (fun w => core a b T ((w,B),z)) (core (a+1) b T ((A,B),z)) A := by
  have hn := (zeta_shift_ne_one T hT A z hA hz.2).1
  have he : 1/2+A/(Real.log T:ℂ)+z*Complex.I = (1/2+z*Complex.I)+A/(Real.log T:ℂ) := by ring
  rw [he] at hn
  have h := (scaledZeta_shift_deriv a T (1/2+z*Complex.I) A hn).mul_const
    (scaledZeta b T (1/2+B/(Real.log T:ℂ)-z*Complex.I))
  simpa only [core,show ∀ w : ℂ, 1/2+w/(Real.log T:ℂ)+z*Complex.I =
    (1/2+z*Complex.I)+w/(Real.log T:ℂ) from fun w => by ring] using h

theorem core_right_deriv (a b : ℕ) (T : ℝ) (hT : 1 < T)
    (A B z : ℂ) (hB : B.re < 0) (hz : z ∈ timeStrip) :
    HasDerivAt (fun w => core a b T ((A,w),z)) (core a (b+1) T ((A,B),z)) B := by
  have hn := (zeta_shift_ne_one T hT B z hB hz.2).2
  have he : 1/2+B/(Real.log T:ℂ)-z*Complex.I = (1/2-z*Complex.I)+B/(Real.log T:ℂ) := by ring
  rw [he] at hn
  have h := (scaledZeta_shift_deriv b T (1/2-z*Complex.I) B hn).const_mul
    (scaledZeta a T (1/2+A/(Real.log T:ℂ)+z*Complex.I))
  simpa only [core,show ∀ w : ℂ, 1/2+w/(Real.log T:ℂ)-z*Complex.I =
    (1/2-z*Complex.I)+w/(Real.log T:ℂ) from fun w => by ring] using h

theorem integral_left_deriv (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    HasDerivAt (fun w => integral a b P Q θ T Phi w B)
      (integral (a+1) b P Q θ T Phi A B) A :=
  compact_deriv _ _ _ _ _ _ negativeShifts_open timeStrip_open (core_smooth a b T hT)
    (momentWeight_continuous P Q θ T Phi hPhi).continuousOn (time_segment T (by linarith))
    (fun w => (w,B)) A (1,0) ((hasDerivAt_id A).prodMk (hasDerivAt_const A B)) ⟨hA,hB⟩
    _ (fun t ht => core_left_deriv a b T hT A B _ hA (time_segment T (by linarith) t ht))

theorem integral_right_deriv (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    HasDerivAt (fun w => integral a b P Q θ T Phi A w)
      (integral a (b+1) P Q θ T Phi A B) B :=
  compact_deriv _ _ _ _ _ _ negativeShifts_open timeStrip_open (core_smooth a b T hT)
    (momentWeight_continuous P Q θ T Phi hPhi).continuousOn (time_segment T (by linarith))
    (fun w => (A,w)) B (0,1) ((hasDerivAt_const B A).prodMk (hasDerivAt_id B)) ⟨hA,hB⟩
    _ (fun t ht => core_right_deriv a b T hT A B _ hB (time_segment T (by linarith) t ht))

theorem integral_zero (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) :
    integral 0 0 P Q θ T Phi A B = twistedMoment P Q θ T Phi A B := by
  rw [twistedMoment,weighted_integral_restrict _ Phi hPhi T (by linarith)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight,core,scaledZeta,iteratedDeriv_zero,pow_zero,div_one,smul_eq_mul]
  ring

/-- The original real-line integral, with the exact total chain factor. -/
theorem integral_eq_full (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) :
    integral a b P Q θ T Phi A B =
      (∫ t : ℝ, iteratedDeriv a riemannZeta (1/2+A/(Real.log T:ℂ)+t*Complex.I) *
        iteratedDeriv b riemannZeta (1/2+B/(Real.log T:ℂ)-t*Complex.I) *
        dirichletPolynomial (coefficient P θ T) (cutoff θ T) (1/2+t*Complex.I) *
        star (dirichletPolynomial (coefficient Q θ T) (cutoff θ T) (1/2+t*Complex.I)) *
        (Phi (t/T):ℂ))/(Real.log T:ℂ)^(a+b) := by
  rw [weighted_integral_restrict _ Phi hPhi T (by linarith),← integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [momentWeight,core,scaledZeta,smul_eq_mul,pow_add,div_eq_mul_inv,mul_inv_rev]
  ring

theorem integral_iterated_left (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
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
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
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
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
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

#print axioms zeta_derivative_analytic
#print axioms scaledZeta_shift_deriv
#print axioms core_smooth
#print axioms compact_deriv
#print axioms core_left_deriv
#print axioms core_right_deriv
#print axioms integral_left_deriv
#print axioms integral_right_deriv
#print axioms integral_zero
#print axioms integral_eq_full
#print axioms integral_iterated_left
#print axioms integral_iterated_right
#print axioms twistedMoment_mixed_deriv
end XiPrime8845.ZetaMomentIntegral


import ExpandedZetaIntegral
import ZetaMomentPolynomial
/-! Exact full-line polynomial moment identity for expanded-support weights. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter Set MeasureTheory
namespace XiPrime8845.ExpandedZetaPolynomial
open ArithmeticRegularity PRZZ FiniteJet CauchyJetTransfer ZetaMomentIntegral
open ZetaMomentPolynomial
set_option maxHeartbeats 1000000
theorem mixedIntegrand_integrable (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    IntegrableOn (fun t : ℝ => momentWeight P Q θ T Phi t • core a b T ((A,B),(t:ℂ))) (Icc (T/2) (5/2*T)) := by
  have hc : ContinuousOn (fun t : ℝ => core a b T ((A,B),(t:ℂ))) (Icc (T/2) (5/2*T)) :=
    (core_smooth a b T hT).continuousOn.comp (by fun_prop)
      (fun t ht => ⟨⟨hA,hB⟩,ExpandedRegularity.time_segment T (by linarith) t ht⟩)
  exact ((ExpandedRegularity.momentWeight_continuous P Q θ T Phi hPhi).continuousOn.smul hc).integrableOn_compact isCompact_Icc

theorem moment_expansion (D : ℕ) (q : ℕ → ℂ) (P Q : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T)
    (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    moment D q P Q θ T Phi A B =
      (∑ a ∈ Finset.range (D+1), ∑ b ∈ Finset.range (D+1),
        (q a*(-1:ℂ)^a)*(q b*(-1:ℂ)^b)*ExpandedZetaIntegral.integral a b P Q θ T Phi A B)/(T:ℂ) := by
  rw [moment,ExpandedGcd.weighted_integral_restrict _ Phi hPhi T (by linarith)]
  congr 1
  let c := fun a b => (q a*(-1:ℂ)^a)*(q b*(-1:ℂ)^b)
  have he : (fun t : ℝ =>
      differentialPolynomial D q T (1/2+A/(Real.log T:ℂ)+t*Complex.I) *
      differentialPolynomial D q T (1/2+B/(Real.log T:ℂ)-t*Complex.I) *
      dirichletPolynomial (coefficient P θ T) (cutoff θ T) (1/2+t*Complex.I) *
      star (dirichletPolynomial (coefficient Q θ T) (cutoff θ T) (1/2+t*Complex.I)) *
      (Phi (t/T):ℂ)) =
      (fun t => ∑ a ∈ Finset.range (D+1), ∑ b ∈ Finset.range (D+1),
        c a b * (momentWeight P Q θ T Phi t • core a b T ((A,B),(t:ℂ)))) := by
    funext t
    simp only [differentialPolynomial,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [c,momentWeight,core,smul_eq_mul]
    ring
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      exact integral_const_mul _ _
    · intro b hb
      exact (mixedIntegrand_integrable a b P Q θ T Phi hPhi hT A B hA hB).const_mul _
  · intro a ha
    exact integrable_finsetSum _ (fun b hb =>
      (mixedIntegrand_integrable a b P Q θ T Phi hPhi hT A B hA hB).const_mul _)

/-- Both normalized jets are literal zeta-derivative integrals. -/
theorem normalized_jet₂ (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    jet₂ a b (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ)) A B =
      ExpandedZetaIntegral.integral a b P Q θ T Phi A B / ((T:ℂ)*(a.factorial:ℂ)*(b.factorial:ℂ)) := by
  simp only [jet₂,jet,div_eq_mul_inv,iteratedDeriv_mul_const_field]
  rw [ExpandedZetaIntegral.twistedMoment_mixed_deriv a b P Q θ T Phi hPhi hT A B hA hB]
  ring

/-- Exact finite-T operator identity: the factorials in opMinus cancel those
in jet2; log T chain factors and signs remain in differentialPolynomial. -/
theorem contract₂_eq_moment (D : ℕ) (q : ℕ → ℂ) (P Q : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (hT : 1 < T)
    (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    contract₂ D (opMinus q) (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ)) A B =
      moment D q P Q θ T Phi A B := by
  have hr := regularNegative_of_smooth (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ))
    ((ExpandedRegularity.twistedMoment_smooth P Q θ T Phi hPhi hT).div_const (T:ℂ))
  rw [contract₂_rect D (opMinus q) _ A B (fun b _ => hr.2 B hB b A hA D),
    moment_expansion D q P Q θ T Phi hPhi hT A B hA hB,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  rw [normalized_jet₂ a b P Q θ T Phi hPhi hT A B hA hB]
  have ha0 : (a.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb0 : (b.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  unfold opMinus
  field_simp


#print axioms moment_expansion
#print axioms normalized_jet₂
#print axioms contract₂_eq_moment
end XiPrime8845.ExpandedZetaPolynomial


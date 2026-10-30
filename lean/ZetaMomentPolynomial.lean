import ZetaMomentIntegral
import CauchyJetTransfer

/-! Exact finite zeta-derivative moments. The coefficients may be complex and
the two derivative orders remain independent. For real coefficients and equal
real shifts the literal bilinear integral is a weighted absolute square.
No PRZZ asymptotic is used in these identities. -/
noncomputable section
open scoped BigOperators ContDiff ComplexConjugate
open Filter Set MeasureTheory
namespace XiPrime8845.ZetaMomentPolynomial
open ZetaMomentIntegral ArithmeticRegularity PRZZ FiniteJet CauchyJetTransfer
set_option maxHeartbeats 1000000

/-- q(-d/ds / log T) applied to zeta; no factorial remains. -/
def differentialPolynomial (D : ℕ) (q : ℕ → ℂ) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ a ∈ Finset.range (D+1), q a*(-1:ℂ)^a*scaledZeta a T s

def moment (D : ℕ) (q : ℕ → ℂ) (P Q : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  (∫ t : ℝ,
    differentialPolynomial D q T (1/2+A/(Real.log T:ℂ)+t*Complex.I) *
    differentialPolynomial D q T (1/2+B/(Real.log T:ℂ)-t*Complex.I) *
    dirichletPolynomial (coefficient P θ T) (cutoff θ T) (1/2+t*Complex.I) *
    star (dirichletPolynomial (coefficient Q θ T) (cutoff θ T) (1/2+t*Complex.I)) *
    (Phi (t/T):ℂ))/(T:ℂ)

theorem mixedIntegrand_integrable (a b : ℕ) (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    IntegrableOn (fun t : ℝ => momentWeight P Q θ T Phi t • core a b T ((A,B),(t:ℂ))) (Icc T (2*T)) := by
  have hc : ContinuousOn (fun t : ℝ => core a b T ((A,B),(t:ℂ))) (Icc T (2*T)) :=
    (core_smooth a b T hT).continuousOn.comp (by fun_prop)
      (fun t ht => ⟨⟨hA,hB⟩,time_segment T (by linarith) t ht⟩)
  exact ((momentWeight_continuous P Q θ T Phi hPhi).continuousOn.smul hc).integrableOn_compact isCompact_Icc

theorem moment_expansion (D : ℕ) (q : ℕ → ℂ) (P Q : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) (hT : 1 < T)
    (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    moment D q P Q θ T Phi A B =
      (∑ a ∈ Finset.range (D+1), ∑ b ∈ Finset.range (D+1),
        (q a*(-1:ℂ)^a)*(q b*(-1:ℂ)^b)*integral a b P Q θ T Phi A B)/(T:ℂ) := by
  rw [moment,weighted_integral_restrict _ Phi hPhi T (by linarith)]
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
    (hPhi : SmoothWeight Phi) (hT : 1 < T) (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    jet₂ a b (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ)) A B =
      integral a b P Q θ T Phi A B / ((T:ℂ)*(a.factorial:ℂ)*(b.factorial:ℂ)) := by
  simp only [jet₂,jet,div_eq_mul_inv,iteratedDeriv_mul_const_field]
  rw [twistedMoment_mixed_deriv a b P Q θ T Phi hPhi hT A B hA hB]
  ring

/-- Exact finite-T operator identity: the factorials in opMinus cancel those
in jet2; log T chain factors and signs remain in differentialPolynomial. -/
theorem contract₂_eq_moment (D : ℕ) (q : ℕ → ℂ) (P Q : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi) (hT : 1 < T)
    (A B : ℂ) (hA : A.re < 0) (hB : B.re < 0) :
    contract₂ D (opMinus q) (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ)) A B =
      moment D q P Q θ T Phi A B := by
  have hr := regularNegative_of_smooth (fun x y => twistedMoment P Q θ T Phi x y/(T:ℂ))
    ((twistedMoment_smooth P Q θ T Phi hPhi hT).div_const (T:ℂ))
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

theorem zeta_derivative_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (conj s) = conj (iteratedDeriv n riemannZeta s) := by
  induction n generalizing s with
  | zero => exact riemannZeta_conj s
  | succ n ih =>
    have he : conj ∘ iteratedDeriv n riemannZeta ∘ conj = iteratedDeriv n riemannZeta := by
      funext z
      simp only [Function.comp_def,ih,Complex.conj_conj]
    have hh := congrFun (deriv_conj_conj (f := iteratedDeriv n riemannZeta)) (conj s)
    rw [he] at hh
    simpa only [iteratedDeriv_succ,Function.comp_def,Complex.conj_conj] using hh

theorem differentialPolynomial_conj (D : ℕ) (q : ℕ → ℝ) (T : ℝ) (s : ℂ) :
    differentialPolynomial D (fun n => (q n:ℂ)) T (conj s) =
      conj (differentialPolynomial D (fun n => (q n:ℂ)) T s) := by
  simp only [differentialPolynomial,scaledZeta,zeta_derivative_conj,map_sum,map_mul,map_pow,map_div₀,
    map_neg,map_one,Complex.conj_ofReal]

/-- The mollifier stays on Re(s)=1/2, exactly as in PRZZ.twistedMoment. -/
def squareMoment (D : ℕ) (q : ℕ → ℝ) (P : Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (σ : ℝ) : ℝ :=
  (∫ t : ℝ, ‖differentialPolynomial D (fun n => (q n:ℂ)) T ((σ:ℂ)+t*Complex.I) *
    dirichletPolynomial (coefficient P θ T) (cutoff θ T) (1/2+t*Complex.I)‖^2 * Phi (t/T))/T

theorem moment_eq_square (D : ℕ) (q : ℕ → ℝ) (P : Profiles) (θ T r : ℝ) (Phi : ℝ → ℝ) :
    moment D (fun n => (q n:ℂ)) P P θ T Phi (r:ℂ) (r:ℂ) =
      (squareMoment D q P θ T Phi (1/2+r/Real.log T):ℂ) := by
  unfold moment squareMoment
  rw [Complex.ofReal_div,← integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hc : 1/2+(r:ℂ)/(Real.log T:ℂ)-t*Complex.I =
      conj (1/2+(r:ℂ)/(Real.log T:ℂ)+t*Complex.I) := by
    simp only [map_add,map_div₀,map_mul,map_ofNat,map_one,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hc,differentialPolynomial_conj]
  rw [← Complex.normSq_eq_norm_sq,Complex.ofReal_mul,← Complex.mul_conj,map_mul]
  push_cast
  simp only [Complex.star_def]
  ring

#print axioms mixedIntegrand_integrable
#print axioms moment_expansion
#print axioms normalized_jet₂
#print axioms contract₂_eq_moment
#print axioms zeta_derivative_conj
#print axioms differentialPolynomial_conj
#print axioms moment_eq_square
end XiPrime8845.ZetaMomentPolynomial


import CoefficientEvaluator
import KernelAlgebra

/-! Kernel-checked exponential and aggregate-error bounds for the fixed witness.
The scalar helper retains the coefficient-value inequality as an explicit premise.
FixedCertificate discharges it; neither module proves a zero-counting theorem. -/
noncomputable section
open scoped BigOperators

namespace XiPrime8845.NumericalGate
open Polynomial TaylorEnvelope FiniteJet
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

def R : ℝ := 1.04440033
def θ : ℝ := 4/7 - 1/1000000
def target : ℝ := Real.exp (R * (1 - 0.8845))

def F : Polynomial ℂ := C (-0.30528514)*X + C 2.50038954*X^2 -
  C 1.12177152*X^3 - C 0.07333288*X^4
def G : Polynomial ℂ := C 1.89779072*X + C 0.56594804*X^2 + C 0.07023055*X^3
def qCoeff : ℕ → ℂ
  | 0 => 1
  | 1 => -2.27043254
  | 2 => 0.304358115
  | 3 => 0.16793368
  | 4 => 4.34152016
  | 5 => -5.3105844
  | 6 => 1.7701948
  | _ => 0

theorem profile_witness_matches (x : ℚ) :
    F.eval (x:ℂ) = (XiPrime8845.p1 x : ℂ) ∧
    G.eval (x:ℂ) = (XiPrime8845.p2 x : ℂ) := by
  norm_num [F, G, XiPrime8845.p1, XiPrime8845.p2]

theorem q_witness_matches (x : ℚ) :
    (∑ i ∈ Finset.range 7, qCoeff i * (x:ℂ)^i) = (XiPrime8845.q x : ℂ) := by
  norm_num [qCoeff, XiPrime8845.q, Finset.sum_range_succ]
  ring

theorem parameters_match :
    R = (XiPrime8845.radiusParameter : ℝ) ∧ θ = (XiPrime8845.theta : ℝ) := by
  norm_num [R, θ, XiPrime8845.radiusParameter, XiPrime8845.theta]

theorem coeffNorm_range (P : Polynomial ℂ) (n : ℕ) (h : P.natDegree < n) :
    coeffNorm P = ∑ d ∈ Finset.range n, ‖P.coeff d‖ := by
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_range.mpr ((Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hd)).trans_lt h)
  · intro d _ hd
    have hz : P.coeff d = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hd
    simp [hz]

theorem profile_norm_bounds :
    coeffNorm F ≤ 5 ∧ coeffNorm G ≤ 5 ∧
    coeffNorm F.derivative ≤ 10 ∧ coeffNorm G.derivative ≤ 10 := by
  have hF : F.natDegree < 5 := by unfold F; compute_degree!
  have hG : G.natDegree < 5 := by unfold G; compute_degree!
  have hdF : F.derivative.natDegree < 5 :=
    (Polynomial.natDegree_derivative_le F).trans_lt (by omega)
  have hdG : G.derivative.natDegree < 5 :=
    (Polynomial.natDegree_derivative_le G).trans_lt (by omega)
  rw [coeffNorm_range F 5 hF, coeffNorm_range G 5 hG,
    coeffNorm_range F.derivative 5 hdF, coeffNorm_range G.derivative 5 hdG]
  norm_num [F, G, Finset.sum_range_succ, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_derivative, Complex.norm_def]

theorem target_lower : (1.1282054105 : ℝ) < target := by
  have h := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ R * (1 - 0.8845) by norm_num [R]) 7
  have hs : (1.1282054105 : ℝ) <
      ∑ j ∈ Finset.range 7, (R * (1 - 0.8845))^j / (j.factorial : ℝ) := by
    norm_num [R, Finset.sum_range_succ, Nat.factorial]
  exact hs.trans_le h

theorem half_radius_exp :
    (1.685732462167650 : ℝ) < Real.exp (R/2) ∧
    Real.exp (R/2) < 1.685732462167651 := by
  have h := Real.exp_bound (x := R/2) (by norm_num [R]) (n := 16) (by decide)
  rw [abs_le] at h
  norm_num [R, Finset.sum_range_succ, Nat.factorial] at h
  norm_num [R]
  constructor <;> linarith [h.1, h.2]

theorem dual_exp_bounds :
    (8.075224414565 : ℝ) < Real.exp (2*R) ∧
    Real.exp (2*R) < 8.075224414566 := by
  have h := half_radius_exp
  have he : Real.exp (2*R) = Real.exp (R/2)^4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.685732462167650) h.1.le 4
  have hu := pow_le_pow_left₀ (Real.exp_nonneg _) h.2.le 4
  constructor
  · exact (by norm_num : (8.075224414565:ℝ) < (1.685732462167650:ℝ)^4).trans_le hl
  · exact hu.trans_lt (by norm_num)

theorem witness_domain : R ≠ 0 ∧ 0 < θ ∧ |R| * θ ≤ 1 := by
  norm_num [R, θ]

/-- This is the scalar Taylor factor only, not the composed K2 error. -/
theorem tail_factor_24 :
    0 ≤ TaylorEnvelope.tailFactor 24 (|R| * θ) ∧
    TaylorEnvelope.tailFactor 24 (|R| * θ) < 1/1000000000000000000000000000000 := by
  norm_num [TaylorEnvelope.tailFactor, R, θ, Nat.factorial]

/-- Coarse bounds are intentional: the degree-24 tail leaves ample room. -/
theorem inverse_bound_le (a : ℕ) (C : ℝ) (hC : 0 ≤ C) (hC5 : C ≤ 5) :
    inverseBound a θ C ≤ 15 := by
  have ht : 0 ≤ θ ∧ θ ≤ 1 := by norm_num [θ]
  have hp : θ^(a+1) ≤ 1 := pow_le_one₀ ht.1 ht.2
  have hf : (1 : ℝ) ≤ a.factorial := by exact_mod_cast Nat.factorial_pos a
  have ha : (1 : ℝ) ≤ a+1 := by
    have : (0:ℝ) ≤ a := by positivity
    linarith
  unfold inverseBound
  apply (div_le_iff₀ (by positivity)).mpr
  have h1 : 3*C*θ^(a+1) ≤ 15 := by nlinarith [pow_nonneg ht.1 (a+1)]
  have h2 : (1 : ℝ) ≤ (a.factorial : ℝ)*(a+1) := by nlinarith
  linarith

theorem operator_bounds (P : Polynomial ℂ) (e : ℤ) (a : ℕ) (A : ℂ)
    (hP : coeffNorm P ≤ 5) (hdP : coeffNorm P.derivative ≤ 10) (hA : ‖A‖ = R) :
    0 ≤ operatorBound e a A θ P ∧ operatorBound e a A θ P ≤ 35 ∧
    0 ≤ operatorError 24 e a A θ P ∧ operatorError 24 e a A θ P ≤ 15/10^30 := by
  have ht : 0 < θ := witness_domain.2.1
  have hr0 : 0 < R := by norm_num [R]
  have hC := coeffNorm_nonneg P
  have hdC := coeffNorm_nonneg P.derivative
  have hb := inverse_bound_le a (coeffNorm P) hC hP
  have hb0 := inverseBound_nonneg a θ (coeffNorm P) ht.le hC
  have htail := tail_factor_24
  have htail' : tailFactor 24 (‖A‖*θ) ≤ 1/10^30 := by
    rw [hA]
    norm_num [abs_of_pos hr0] at htail ⊢
    exact htail.2.le
  have htail0 : 0 ≤ tailFactor 24 (‖A‖*θ) := by unfold tailFactor; positivity
  by_cases he : e = -1
  · simp only [operatorBound, operatorError, he, ↓reduceIte]
    refine ⟨hb0, hb.trans (by norm_num), mul_nonneg hb0 htail0, ?_⟩
    calc
      _ ≤ 15*(1/10^30) := mul_le_mul hb htail' htail0 (by norm_num)
      _ = _ := by ring
  · simp only [operatorBound, operatorError, he, ↓reduceIte, hA]
    refine ⟨by positivity, ?_, le_rfl, by norm_num⟩
    have hdiv : coeffNorm P.derivative / θ ≤ 20 := by
      apply (div_le_iff₀ ht).mpr
      norm_num [θ] at *
      linarith
    have hm : (R+1)*coeffNorm P ≤ 15 := by
      have hr : 0 ≤ R+1 ∧ R+1 ≤ 3 := by norm_num [R]
      nlinarith
    linarith

theorem product_error_bound (P Q : Polynomial ℂ) (e f : ℤ) (i j : ℕ) (A B : ℂ)
    (hP : coeffNorm P ≤ 5) (hdP : coeffNorm P.derivative ≤ 10)
    (hQ : coeffNorm Q ≤ 5) (hdQ : coeffNorm Q.derivative ≤ 10)
    (hA : ‖A‖ = R) (hB : ‖B‖ = R) :
    productError 24 e f i j A B θ P Q ≤ 1/10^26 := by
  obtain ⟨hp0, hp, he0, he⟩ := operator_bounds P e i A hP hdP hA
  obtain ⟨hq0, hq, hf0, hf⟩ := operator_bounds Q f j B hQ hdQ hB
  have h1 := mul_le_mul he hq hq0 (by norm_num : (0:ℝ) ≤ 15/10^30)
  have h2 := mul_le_mul hf hp hp0 (by norm_num : (0:ℝ) ≤ 15/10^30)
  have h3 := mul_le_mul he hf hf0 (by norm_num : (0:ℝ) ≤ 15/10^30)
  unfold productError
  nlinarith

theorem outer_error_bound (P Q : Polynomial ℂ) (e f : ℤ) (i j n : ℕ) (A B : ℂ)
    (hP : coeffNorm P ≤ 5) (hdP : coeffNorm P.derivative ≤ 10)
    (hQ : coeffNorm Q ≤ 5) (hdQ : coeffNorm Q.derivative ≤ 10)
    (hA : ‖A‖ = R) (hB : ‖B‖ = R) :
    productError 24 e f i j A B θ P Q * θ^n / (n.factorial : ℝ) ≤ 1/10^26 := by
  have hp := product_error_bound P Q e f i j A B hP hdP hQ hdQ hA hB
  have ht : 0 ≤ θ ∧ θ ≤ 1 := by norm_num [θ]
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpow : θ^n ≤ 1 := pow_le_one₀ ht.1 ht.2
  apply (div_le_iff₀ (by positivity)).mpr
  have hm : productError 24 e f i j A B θ P Q * θ^n ≤ (1/10^26 : ℝ) :=
    (mul_le_mul_of_nonneg_right hp (pow_nonneg ht.1 n)).trans
      (by nlinarith)
  nlinarith

theorem poleError_mono (l m : ℕ) (E : ℤ → ℤ → ℕ → ℝ) (c : ℝ)
    (h : ∀ e f n, E e f n ≤ c) :
    poleError l m E ≤ poleError l m (fun _ _ _ => c) := by
  unfold poleError
  gcongr with k hk r hr t ht
  exact h _ _ _

theorem H_error_bound (P Q : Polynomial ℂ) (l m i j : ℕ) (A B : ℂ)
    (hl : l = 0 ∨ l = 2) (hm : m = 0 ∨ m = 2)
    (hP : coeffNorm P ≤ 5) (hdP : coeffNorm P.derivative ≤ 10)
    (hQ : coeffNorm Q ≤ 5) (hdQ : coeffNorm Q.derivative ≤ 10)
    (hA : ‖A‖ = R) (hB : ‖B‖ = R) :
    HError 24 l m i j A B θ P Q ≤ 1/10^23 := by
  have hp := poleError_mono l m _ (1/10^26)
    (fun e f n => outer_error_bound P Q e f i j n A B hP hdP hQ hdQ hA hB)
  unfold HError
  apply (div_le_div_of_nonneg_right hp (by norm_num [θ])).trans
  rcases hl with rfl | rfl <;> rcases hm with rfl | rfl <;>
    norm_num [poleError, Finset.sum_range_succ, Nat.descFactorial,
      norm_mul, norm_pow, θ]

theorem four_error_bound (i j : ℕ) (A B : ℂ) (hA : ‖A‖ = R) (hB : ‖B‖ = R) :
    fourError 24 i j A B θ F G ≤ 4/10^23 := by
  obtain ⟨hF, hG, hdF, hdG⟩ := profile_norm_bounds
  have h00 := H_error_bound F F 0 0 i j A B (Or.inl rfl) (Or.inl rfl) hF hdF hF hdF hA hB
  have h02 := H_error_bound F G 0 2 i j A B (Or.inl rfl) (Or.inr rfl) hF hdF hG hdG hA hB
  have h20 := H_error_bound G F 2 0 i j A B (Or.inr rfl) (Or.inl rfl) hG hdG hF hdF hA hB
  have h22 := H_error_bound G G 2 2 i j A B (Or.inr rfl) (Or.inr rfl) hG hdG hG hdG hA hB
  unfold fourError
  linarith

theorem op_norm_bounds (i : ℕ) (hi : i ≤ 6) :
    ‖opMinus qCoeff i‖ ≤ 5000 ∧ ‖opPlus 6 qCoeff i‖ ≤ 5000 := by
  interval_cases i <;>
    norm_num [opMinus, opPlus, qCoeff, Finset.sum_Ico_eq_sub,
      Finset.sum_range_succ, Nat.factorial, Nat.choose, Complex.norm_def]

theorem reciprocal_bound (s : ℂ) (a b : ℕ) (ha : a ≤ 6) (hb : b ≤ 6)
    (hs : 1 ≤ ‖s‖) : ‖reciprocalCoeff s a b‖ ≤ 4096 := by
  have hc : (Nat.choose (a+b) a : ℝ) ≤ 4096 := by
    have h := (Nat.choose_le_two_pow (a+b) a).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show a+b ≤ 12 by omega))
    exact_mod_cast h
  have hp : 1 ≤ ‖s‖^(a+b+1) := one_le_pow₀ hs
  norm_num only [reciprocalCoeff, norm_div, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, norm_natCast]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem W_bound (op : ℕ → ℂ) (s : ℂ) (i j : ℕ)
    (hop : ∀ a ≤ 6, ‖op a‖ ≤ 5000) (hs : 1 ≤ ‖s‖) :
    ‖W 6 op s i j‖ ≤ 10^13 := by
  unfold W
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ Finset.Ico i 7, ∑ b ∈ Finset.Ico j 7, (5000*5000*4096 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      have ha6 : a ≤ 6 := by have := (Finset.mem_Ico.mp ha).2; omega
      have hb6 : b ≤ 6 := by have := (Finset.mem_Ico.mp hb).2; omega
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul (hop a ha6) (hop b hb6) (norm_nonneg _) (by norm_num))
        (reciprocal_bound s (a-i) (b-j) (by omega) (by omega) hs)
        (norm_nonneg _) (by norm_num)
    _ ≤ 10^13 := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hi : ((7-i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast Nat.sub_le 7 i
      have hj : ((7-j : ℕ) : ℝ) ≤ 7 := by exact_mod_cast Nat.sub_le 7 j
      have hj0 : (0:ℝ) ≤ ((7-j : ℕ) : ℝ) := by positivity
      nlinarith

theorem weighted_error_bound (op : ℕ → ℂ) (s A B : ℂ)
    (hop : ∀ a ≤ 6, ‖op a‖ ≤ 5000) (hs : 1 ≤ ‖s‖)
    (hA : ‖A‖ = R) (hB : ‖B‖ = R) :
    (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
      ‖W 6 op s i j‖ * fourError 24 i j A B θ F G) ≤ 196/10^10 := by
  calc
    _ ≤ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7, (10^13*(4/10^23) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ‖W 6 op s i j‖*(4/10^23) := mul_le_mul_of_nonneg_left
          (four_error_bound i j A B hA hB) (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right (W_bound op s i j hop hs) (by norm_num)
    _ = _ := by norm_num

theorem total_error_bound :
    evaluatorError 24 6 qCoeff (-R) (-R) θ F G ≤ 0.000001 := by
  have hm : ‖(-(R:ℂ))‖ = R := by norm_num [R, norm_neg, Complex.norm_real]
  have hp : ‖(R:ℂ)‖ = R := by norm_num [R, Complex.norm_real]
  have hsm : 1 ≤ ‖(-(R:ℂ)) + -(R:ℂ)‖ := by
    norm_num [R, Complex.norm_def]
  have hsp : 1 ≤ ‖-(-(R:ℂ)) + -(-(R:ℂ))‖ := by
    norm_num [R, Complex.norm_def]
  have h1 := weighted_error_bound (opMinus qCoeff) _ _ _
    (fun a ha => (op_norm_bounds a ha).1) hsm hm hm
  have h2 := weighted_error_bound (opPlus 6 qCoeff) _ (-(-(R:ℂ))) (-(-(R:ℂ)))
    (fun a ha => (op_norm_bounds a ha).2) hsp (by simpa only [neg_neg] using hp)
      (by simpa only [neg_neg] using hp)
  have hexp : ‖Complex.exp (-(-(R:ℂ)) - (-(R:ℂ)))‖ ≤ 9 := by
    rw [Complex.norm_exp]
    have he : (-(-(R:ℂ)) - (-(R:ℂ))).re = 2*R := by simp; ring
    rw [he]
    exact dual_exp_bounds.2.le.trans (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left h2
    (norm_nonneg (Complex.exp (-(-(R:ℂ)) - (-(R:ℂ)))))
  have hu := mul_le_mul_of_nonneg_right hexp (by norm_num : (0:ℝ) ≤ 196/10^10)
  unfold evaluatorError
  linarith

def actual : ℂ := contract₂ 6 (opMinus qCoeff)
  (fun x y => BetaKernel.shiftedFunctional x y θ F G) (-R) (-R)
def finiteValue : ℂ := CoefficientEvaluator.cachedEvaluator 24 6 qCoeff R θ F G

theorem actual_sub_finite : ‖actual - finiteValue‖ ≤ 0.000001 := by
  exact (CoefficientEvaluator.K2_cached_enclosure 24 6 qCoeff R θ F G
    witness_domain.1 witness_domain.2.1 witness_domain.2.2).trans total_error_bound

/-- Convert a complex norm enclosure to the one-sided real inequality needed
at the counting interface. No assertion of reality is smuggled into the bound. -/
theorem re_le_of_norm_sub_le (z c : ℂ) (ε : ℝ) (h : ‖z-c‖ ≤ ε) :
    z.re ≤ c.re + ε := by
  have hr := Complex.re_le_norm (z-c)
  simp only [Complex.sub_re] at hr
  linarith

/-- Final scalar arithmetic once a finite evaluator and its total error have
been certified. The hypotheses remain explicit until the fixed sums are closed. -/
theorem scalar_gate (z c : ℂ)
    (hc : c.re ≤ 1.12819) (he : ‖z-c‖ ≤ 0.00001) : z.re < target := by
  have h := re_le_of_norm_sub_le z c 0.00001 he
  have ht := target_lower
  linarith

/-- Scalar helper with an explicit coefficient bound. FixedCertificate supplies
that bound by a kernel-checked rational calculation. -/
theorem fixed_finite_gate (hc : finiteValue.re ≤ 1.12820) : actual.re < target := by
  have h := re_le_of_norm_sub_le actual finiteValue 0.000001 actual_sub_finite
  have ht := target_lower
  linarith

#print axioms coeffNorm_range
#print axioms profile_witness_matches
#print axioms q_witness_matches
#print axioms parameters_match
#print axioms profile_norm_bounds
#print axioms target_lower
#print axioms half_radius_exp
#print axioms dual_exp_bounds
#print axioms witness_domain
#print axioms tail_factor_24
#print axioms inverse_bound_le
#print axioms operator_bounds
#print axioms product_error_bound
#print axioms outer_error_bound
#print axioms poleError_mono
#print axioms H_error_bound
#print axioms four_error_bound
#print axioms op_norm_bounds
#print axioms reciprocal_bound
#print axioms W_bound
#print axioms weighted_error_bound
#print axioms total_error_bound
#print axioms actual_sub_finite
#print axioms re_le_of_norm_sub_le
#print axioms scalar_gate
#print axioms fixed_finite_gate

end XiPrime8845.NumericalGate

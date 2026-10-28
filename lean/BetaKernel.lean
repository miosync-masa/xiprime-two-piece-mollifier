import Mathlib

/-! Beta integration and the linear assembly of the four K2 kernels.
No analytic main-term or Mellin-inversion assertion is made here. -/
noncomputable section
open scoped BigOperators

namespace XiPrime8845.BetaKernel

theorem beta_recurrence (j d : ℕ) (w : ℝ) :
    (j + 1 : ℝ) * (∫ x in 0..w, x ^ j * (w - x) ^ (d + 1)) =
      (d + 1 : ℝ) * (∫ x in 0..w, x ^ (j + 1) * (w - x) ^ d) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ (j + 1) * (w - x) ^ (d + 1))
      ((j + 1 : ℝ) * (x ^ j * (w - x) ^ (d + 1)) -
        (d + 1 : ℝ) * (x ^ (j + 1) * (w - x) ^ d)) x := by
    convert! ((hasDerivAt_id x).pow (j + 1)).mul
      (((hasDerivAt_id x).const_sub w).pow (d + 1)) using 1
    first | rfl | (simp; ring)
  have hi₁ : IntervalIntegrable (fun x : ℝ =>
      (j + 1 : ℝ) * (x ^ j * (w - x) ^ (d + 1))) MeasureTheory.volume 0 w := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₂ : IntervalIntegrable (fun x : ℝ =>
      (d + 1 : ℝ) * (x ^ (j + 1) * (w - x) ^ d)) MeasureTheory.volume 0 w := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hi₁.sub hi₂)
  rw [intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa using (sub_eq_zero.mp (by simpa using h))

/-- Integer beta integral, including w=0 and oriented negative intervals. -/
theorem beta_monomial (j d : ℕ) (w : ℝ) :
    (∫ x in 0..w, x ^ j * (w - x) ^ d) =
      (j.factorial : ℝ) * d.factorial / (j + d + 1).factorial * w ^ (j + d + 1) := by
  induction d generalizing j with
  | zero =>
    simp [integral_pow, Nat.factorial_succ]
    field_simp
  | succ d ih =>
    have h := beta_recurrence j d w
    rw [ih] at h
    have hj : (j + 1 : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hj)
    rw [h]
    have he : j + (d + 1) + 1 = (j + 1) + d + 1 := by omega
    rw [he, Nat.factorial_succ j, Nat.factorial_succ d]
    push_cast
    ring

/-- The exact coefficient used in the outer v-integral in numerical_interval.py. -/
theorem outer_beta (n d : ℕ) (w : ℝ) :
    (∫ v in 0..w, v ^ n / (n.factorial : ℝ) * (w - v) ^ d) =
      (d.factorial : ℝ) / (d + n + 1).factorial * w ^ (d + n + 1) := by
  simp_rw [div_mul_eq_mul_div]
  rw [intervalIntegral.integral_div, beta_monomial]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.add_comm n d]
  field_simp

/-- One monomial of fs(P,-1,A): differentiate exp(-A*y) first, then
truncate its Taylor expansion in y. This is not a derivative of expTrunc N. -/
theorem inverse_jet_beta_term (a j d : ℕ) (A θ w p : ℝ) :
    (∫ y in 0..w,
      (p / θ ^ d * (-1 : ℝ) ^ a * (-A) ^ j /
        ((a.factorial : ℝ) * j.factorial)) * (y ^ (a + j) * (w - y) ^ d)) =
      (p / θ ^ d * (-1 : ℝ) ^ a * (-A) ^ j * (a + j).factorial * d.factorial /
        ((a.factorial : ℝ) * j.factorial * (d + 1 + a + j).factorial)) *
          w ^ (d + 1 + a + j) := by
  rw [intervalIntegral.integral_const_mul, beta_monomial]
  have he : a + j + d + 1 = d + 1 + a + j := by omega
  rw [he]
  ring

/-- The scalar polynomial represented by fs(P,-1,A)[a] in the evaluator. -/
def inverseJetEval (degree order a : ℕ) (p : ℕ → ℝ) (A θ w : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (degree + 1), ∑ j ∈ Finset.range (order + 1),
    (p d / θ ^ d * (-1 : ℝ) ^ a * (-A) ^ j * (a + j).factorial * d.factorial /
      ((a.factorial : ℝ) * j.factorial * (d + 1 + a + j).factorial)) *
        w ^ (d + 1 + a + j)

theorem inverseJetEval_eq_integral (degree order a : ℕ) (p : ℕ → ℝ) (A θ w : ℝ) :
    (∫ y in 0..w, ∑ d ∈ Finset.range (degree + 1),
      ∑ j ∈ Finset.range (order + 1),
        (p d / θ ^ d * (-1 : ℝ) ^ a * (-A) ^ j /
          ((a.factorial : ℝ) * j.factorial)) * (y ^ (a + j) * (w - y) ^ d)) =
      inverseJetEval degree order a p A θ w := by
  rw [intervalIntegral.integral_finsetSum]
  · unfold inverseJetEval
    apply Finset.sum_congr rfl
    intro d hd
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact inverse_jet_beta_term a j d A θ w (p d)
    · intro j hj
      apply Continuous.intervalIntegrable
      fun_prop
  · intro d hd
    apply Continuous.intervalIntegrable
    fun_prop

theorem outer_beta_order (n d : ℕ) (hn : 0 < n) (w : ℝ) :
    (∫ v in 0..w, v ^ (n - 1) / ((n - 1).factorial : ℝ) * (w - v) ^ d) =
      w ^ (d + n) * d.factorial / (d + n).factorial := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel]
    rw [outer_beta]
    simp only [Nat.add_assoc]
    ring

/-- Direct beta evaluator for an arbitrary polynomial in w-v. -/
theorem outer_polynomial (n : ℕ) (w : ℝ) (P : Polynomial ℝ) :
    (∫ v in 0..w, v ^ n / (n.factorial : ℝ) * P.eval (w - v)) =
      ∑ d ∈ P.support,
        P.coeff d * ((d.factorial : ℝ) / (d + n + 1).factorial * w ^ (d + n + 1)) := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d hd
    have he : (fun v : ℝ => v ^ n / (n.factorial : ℝ) * (P.coeff d * (w - v) ^ d)) =
        fun v => P.coeff d * (v ^ n / (n.factorial : ℝ) * (w - v) ^ d) := by
      funext v
      ring
    rw [he, intervalIntegral.integral_const_mul, outer_beta]
  · intro d hd
    apply Continuous.intervalIntegrable
    fun_prop

/-- The coefficient sum from the full Mellin-pole expansion, with an arbitrary
linear evaluation E of each Laurent monomial. Integers retain inverse powers. -/
def poleSum (l m : ℕ) (E : ℤ → ℤ → ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.range (min l m + 1),
    ∑ r ∈ Finset.range (l - k + 1),
      ∑ t ∈ Finset.range (m - k + 1),
        ((Nat.choose l k : ℂ) * m.descFactorial k *
          Nat.choose (l - k) r * Nat.choose (m - k) t * (-1 : ℂ) ^ (l + m + r + t)) *
        E (1 - (l : ℤ) + k + r) (1 - (m : ℤ) + k + t) (1 + 2*k + r + t)

theorem assemble00 (E : ℤ → ℤ → ℕ → ℂ) : poleSum 0 0 E = E 1 1 1 := by
  norm_num [poleSum, Finset.sum_range_succ, Nat.descFactorial]

theorem assemble20 (E : ℤ → ℤ → ℕ → ℂ) :
    poleSum 2 0 E = E 1 1 3 - 2 * E 0 1 2 + E (-1) 1 1 := by
  norm_num [poleSum, Finset.sum_range_succ, Nat.descFactorial]
  ring

theorem assemble02 (E : ℤ → ℤ → ℕ → ℂ) :
    poleSum 0 2 E = E 1 1 3 - 2 * E 1 0 2 + E 1 (-1) 1 := by
  norm_num [poleSum, Finset.sum_range_succ, Nat.descFactorial]
  ring

theorem assemble22 (E : ℤ → ℤ → ℕ → ℂ) :
    poleSum 2 2 E =
      7 * E 1 1 5 - 6 * (E 1 0 4 + E 0 1 4) +
      E 1 (-1) 3 + E (-1) 1 3 + 8 * E 0 0 3 -
      2 * (E (-1) 0 2 + E 0 (-1) 2) + E (-1) (-1) 1 := by
  norm_num [poleSum, Finset.sum_range_succ, Nat.descFactorial]
  ring

/-- The three inverse operators actually occurring in K2. The zero default is
not used by any of the four expansion theorems. Endpoints are real. -/
def D (e : ℤ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) : ℂ :=
  if e = 1 then F.derivative.eval ((w / θ : ℝ) : ℂ) / θ + A * F.eval ((w / θ : ℝ) : ℂ)
  else if e = 0 then F.eval ((w / θ : ℝ) : ℂ)
  else if e = -1 then
    ∫ y in 0..w, Complex.exp (-A * y) * F.eval (((w - y) / θ : ℝ) : ℂ)
  else 0

def monomialIntegral (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (e f : ℤ) (n : ℕ) : ℂ :=
  ∫ v in 0..θ, (v : ℂ) ^ (n - 1) / ((n - 1).factorial : ℂ) *
    D e A θ (θ - v) F * D f B θ (θ - v) G

theorem monomialIntegral_swap (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ)
    (e f : ℤ) (n : ℕ) :
    monomialIntegral A B θ F G e f n = monomialIntegral B A θ G F f e n := by
  unfold monomialIntegral
  congr 1
  funext v
  ring

/-- Equal-length H_lm, before dualization or application of q. -/
def H (l m : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  poleSum l m (monomialIntegral A B θ F G) / (θ : ℂ) ^ (l + m)

theorem H02_swap (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    H 0 2 A B θ F G = H 2 0 B A θ G F := by
  simp only [H, assemble02, assemble20]
  rw [monomialIntegral_swap A B θ F G 1 1 3,
    monomialIntegral_swap A B θ F G 1 0 2,
    monomialIntegral_swap A B θ F G 1 (-1) 1]

/-- Keep both ordered cross terms until their swapped-shift identity is used. -/
def fourTerms (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  H 0 0 A B θ F F + H 0 2 A B θ F G +
    H 2 0 A B θ G F + H 2 2 A B θ G G

theorem fourTerms_diagonal (A : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    fourTerms A A θ F G =
      H 0 0 A A θ F F + 2 * H 2 0 A A θ G F + H 2 2 A A θ G G := by
  rw [fourTerms, H02_swap]
  ring

/-- The full shifted functional; analytic identification and q-jet evaluation
are separate proof obligations. -/
def shiftedFunctional (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  (fourTerms A B θ F G - Complex.exp (-A - B) * fourTerms (-B) (-A) θ F G) /
    (A + B)

/-- Exact finite transposition behind the W contraction. This lemma does not
identify a chosen matrix K with analytic quotient derivatives. -/
theorem weighted_sum_transpose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (op : ι → ℂ) (K : ι → κ → ℂ) (J : κ → ℂ) :
    (∑ a, op a * ∑ i, K a i * J i) =
      ∑ i, (∑ a, op a * K a i) * J i := by
  simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The binomial sum used for the positive-side op coefficients is the
coefficient of q(X+1). This is an algebraic identity, not yet the analytic
conjugation of q(-partial) through the exponential dual. -/
theorem shifted_q_coefficient (q : Polynomial ℂ) (i : ℕ) :
    (q.comp (Polynomial.X + Polynomial.C 1)).coeff i =
      ∑ j ∈ q.support, (Nat.choose j i : ℂ) * q.coeff j := by
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_apply, Polynomial.eval_sum]
  simp [Polynomial.sum_def]

#print axioms beta_recurrence
#print axioms beta_monomial
#print axioms outer_beta
#print axioms inverse_jet_beta_term
#print axioms inverseJetEval_eq_integral
#print axioms outer_beta_order
#print axioms outer_polynomial
#print axioms assemble00
#print axioms assemble20
#print axioms assemble02
#print axioms assemble22
#print axioms monomialIntegral_swap
#print axioms H02_swap
#print axioms fourTerms_diagonal
#print axioms weighted_sum_transpose
#print axioms shifted_q_coefficient

end XiPrime8845.BetaKernel

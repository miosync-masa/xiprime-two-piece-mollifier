import Mathlib

/-! Finite K2 evaluation foundations. No PRZZ axiom is imported.

The polynomial integral theorem evaluates the *truncated* exponential convolution
exactly. It does not identify an inverse Mellin contour integral and does not
assert that a truncated exponential equals the exponential.
-/
noncomputable section
open scoped BigOperators
open Polynomial

namespace XiPrime8845.FiniteJet

/-- Normalized shift derivative; order six is the witness specialization. -/
def jet (n : ℕ) (f : ℂ → ℂ) (A : ℂ) : ℂ :=
  iteratedDeriv n f A / (n.factorial : ℂ)

theorem polynomial_iteratedDeriv (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) =
      fun z => ((Polynomial.derivative^[n]) p).eval z := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext z
    simp [Function.iterate_succ_apply', Polynomial.deriv]

/-- Coefficients are genuine normalized derivatives, not sampled finite differences. -/
theorem polynomial_jet_zero (p : ℂ[X]) (n : ℕ) :
    jet n (fun z => p.eval z) 0 = p.coeff n := by
  rw [jet, polynomial_iteratedDeriv]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, Nat.descFactorial_self,
    Nat.factorial_ne_zero]

theorem jet_translate (f : ℂ → ℂ) (A : ℂ) (n : ℕ) :
    jet n (fun z => f (A + z)) 0 = jet n f A := by
  simp [jet, iteratedDeriv_comp_const_add]

theorem polynomial_jet_at (p : ℂ[X]) (A : ℂ) (n : ℕ) :
    jet n (fun z => p.eval z) A = (p.comp (C A + X)).coeff n := by
  rw [← polynomial_jet_zero, ← jet_translate]
  congr 2
  funext z
  simp

/-- Exact exponential shift jet at any complex base point. -/
theorem exponential_jet (A c : ℂ) (n : ℕ) :
    jet n (fun z => Complex.exp (c * z)) A =
      c ^ n * Complex.exp (c * A) / (n.factorial : ℂ) := by
  simp [jet, iteratedDeriv_cexp_const_mul]

/-- Reciprocal jet used for the denominator A+B. Nonzero is required when
using this as a holomorphic jet, even though Lean totalizes inversion. -/
theorem reciprocal_jet (A : ℂ) (n : ℕ) :
    jet n (fun z => 1 / z) A = (-1 : ℂ) ^ n * A ^ (-1 - (n : ℤ)) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℂ) n isOpen_univ (Set.mem_univ A)
  simp only [iteratedDerivWithin_univ] at h
  unfold jet
  rw [h]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem denominator_jet (A B : ℂ) (n : ℕ) :
    jet n (fun z => 1 / (B + z)) A =
      (-1 : ℂ) ^ n * (B + A) ^ (-1 - (n : ℤ)) := by
  simpa only [jet, iteratedDeriv_comp_const_add] using reciprocal_jet (B + A) n

/-- The sign and factorial used in the inverse-operator integrand. -/
theorem inverse_integrand_jet (A y C : ℂ) (n : ℕ) :
    jet n (fun z => Complex.exp (-y * z) * C) A =
      (-y) ^ n * Complex.exp (-y * A) * C / (n.factorial : ℂ) := by
  unfold jet
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_cexp_const_mul]

/-- Exact signed derivative under the reflected shift, before multiplying by exp. -/
theorem reflected_jet (f : ℂ → ℂ) (A : ℂ) (n : ℕ) :
    jet n (fun z => f (-z)) A = (-1 : ℂ) ^ n * jet n f (-A) := by
  simp [jet, iteratedDeriv_comp_neg, smul_eq_mul, mul_div_assoc]

/-- Leibniz rule for the exponential-reflected factor in the dual term. -/
theorem dual_derivative (f : ℂ → ℂ) (A : ℂ) (n : ℕ)
    (hf : ContDiff ℂ n f) :
    iteratedDeriv n (fun z => Complex.exp (-z) * f (-z)) A =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * ((-1 : ℂ) ^ i * Complex.exp (-A)) *
          ((-1 : ℂ) ^ (n - i) * iteratedDeriv (n - i) f (-A)) := by
  have he : ContDiffAt ℂ n (fun z : ℂ => Complex.exp (-z)) A := by fun_prop
  have hr : ContDiffAt ℂ n (fun z : ℂ => f (-z)) A :=
    (hf.comp contDiff_neg).contDiffAt
  rw [iteratedDeriv_fun_mul he hr]
  apply Finset.sum_congr rfl
  intro i hi
  have hexp : iteratedDeriv i (fun z : ℂ => Complex.exp (-z)) A =
      (-1 : ℂ) ^ i * Complex.exp (-A) := by
    simpa using congrFun (iteratedDeriv_cexp_const_mul i (-1)) A
  rw [hexp, iteratedDeriv_comp_neg]
  rfl

/-- Rectangular normalized jet: both orders range independently through six. -/
def jet₂ (i j : ℕ) (H : ℂ → ℂ → ℂ) (A B : ℂ) : ℂ :=
  jet i (fun a => jet j (H a) B) A

theorem separable_jet₂ (f g : ℂ → ℂ) (A B : ℂ) (i j : ℕ) :
    jet₂ i j (fun a b => f a * g b) A B = jet i f A * jet j g B := by
  simp only [jet₂, jet, iteratedDeriv_const_mul_field,
    iteratedDeriv_div_const, iteratedDeriv_mul_const_field]
  ring

/-- A finite, exactly integrable real polynomial representation. -/
def integralEval (p : ℝ[X]) (a b : ℝ) : ℝ :=
  ∑ k ∈ p.support, p.coeff k * (b ^ (k + 1) - a ^ (k + 1)) / (k + 1)

theorem integral_polynomial (p : ℝ[X]) (a b : ℝ) :
    (∫ x in a..b, p.eval x) = integralEval p a b := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp [integralEval, intervalIntegral.integral_const_mul,
      integral_pow, mul_div_assoc]
  · intro k hk
    exact (continuous_const.mul (continuous_id.pow k)).intervalIntegrable a b

/-- Polynomial in the integration variable for the Nth exponential truncation. -/
def expTrunc (N : ℕ) (A : ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (N + 1), Polynomial.C ((-A) ^ j / j.factorial) * X ^ j

def scaledProfile (F : ℝ[X]) (θ w : ℝ) : ℝ[X] :=
  F.comp ((Polynomial.C w - X) * Polynomial.C θ⁻¹)

def inverseTrunc (N : ℕ) (A θ w : ℝ) (F : ℝ[X]) : ℝ :=
  integralEval (expTrunc N A * scaledProfile F θ w) 0 w

theorem expTrunc_eval (N : ℕ) (A y : ℝ) :
    (expTrunc N A).eval y =
      ∑ j ∈ Finset.range (N + 1), (-A) ^ j / j.factorial * y ^ j := by
  simp [expTrunc, Polynomial.eval_finsetSum]

/-- Exact finite evaluation of D_{-1} after Taylor truncation; no quadrature. -/
theorem inverseTrunc_eq_integral (N : ℕ) (A θ w : ℝ) (F : ℝ[X]) :
    inverseTrunc N A θ w F =
      ∫ y in 0..w,
        (∑ j ∈ Finset.range (N + 1), (-A) ^ j / j.factorial * y ^ j) *
          F.eval ((w - y) / θ) := by
  rw [inverseTrunc, ← integral_polynomial]
  congr 1
  funext y
  simp [expTrunc_eval, scaledProfile, div_eq_mul_inv]

/-- The actual finite real inverse operator, kept separate from its truncation. -/
def inverseExact (A θ w : ℝ) (F : ℝ[X]) : ℝ :=
  ∫ y in 0..w, Real.exp (-A * y) * F.eval ((w - y) / θ)

def operatorZero (θ w : ℝ) (F : ℝ[X]) : ℝ := F.eval (w / θ)
def operatorOne (A θ w : ℝ) (F : ℝ[X]) : ℝ :=
  F.derivative.eval (w / θ) / θ + A * F.eval (w / θ)

/-- Complex shift polynomial for the truncated inverse operator. The profile and
integration endpoints are fixed, so q never differentiates them. -/
def inverseShiftPoly (N : ℕ) (θ w : ℝ) (F : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (N + 1),
    C (((-1 : ℂ) ^ j / j.factorial) *
      (∫ y in 0..w, (y : ℂ) ^ j * F.eval (((w - y) / θ : ℝ) : ℂ))) * X ^ j

theorem inverseShiftPoly_eval (N : ℕ) (θ w : ℝ) (F : ℂ[X]) (A : ℂ) :
    (inverseShiftPoly N θ w F).eval A =
      ∫ y in 0..w,
        ∑ j ∈ Finset.range (N + 1),
          (((-1 : ℂ) ^ j / j.factorial) * A ^ j) *
            ((y : ℂ) ^ j * F.eval (((w - y) / θ : ℝ) : ℂ)) := by
  classical
  rw [intervalIntegral.integral_finsetSum]
  · simp only [inverseShiftPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      intervalIntegral.integral_const_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    apply Continuous.intervalIntegrable
    fun_prop

/-- All orders, including the required 0..6, of the finite inverse shift jet.
This uses the integral identity above, not a numerical derivative. -/
theorem inverseShiftPoly_jet (N n : ℕ) (θ w : ℝ) (F : ℂ[X]) (A : ℂ) :
    jet n (fun z => (inverseShiftPoly N θ w F).eval z) A =
      ((inverseShiftPoly N θ w F).comp (C A + X)).coeff n :=
  polynomial_jet_at _ _ _

#print axioms polynomial_jet_zero
#print axioms polynomial_jet_at
#print axioms exponential_jet
#print axioms reciprocal_jet
#print axioms denominator_jet
#print axioms inverse_integrand_jet
#print axioms reflected_jet
#print axioms dual_derivative
#print axioms separable_jet₂
#print axioms integral_polynomial
#print axioms inverseTrunc_eq_integral
#print axioms inverseShiftPoly_eval
#print axioms inverseShiftPoly_jet

end XiPrime8845.FiniteJet

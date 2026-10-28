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

/-- Composition of derivative orders, also for totalized derivatives. -/
theorem iteratedDeriv_iterated (i j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i + j) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- The reciprocal coefficient occurring in W. -/
def reciprocalCoeff (s : ℂ) (i j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (i + j) * (Nat.choose (i + j) i : ℂ) / s ^ (i + j + 1)

/-- Genuine rectangular normalized derivatives of the quotient denominator.
The explicit nonzero hypothesis records the holomorphic domain. -/
theorem reciprocal_mixed_jet (A B : ℂ) (h : A + B ≠ 0) (i j : ℕ) :
    jet₂ i j (fun a b => 1 / (a + b)) A B = reciprocalCoeff (A + B) i j := by
  simp only [jet₂, jet, iteratedDeriv_comp_const_add, iteratedDeriv_div_const,
    iteratedDeriv_comp_add_const, iteratedDeriv_iterated]
  have hd := iteratedDerivWithin_one_div (𝕜 := ℂ) (i + j)
    isOpen_univ (Set.mem_univ (A + B))
  simp only [iteratedDerivWithin_univ] at hd
  rw [hd]
  have he : (-1 - ((i + j : ℕ) : ℤ)) = -((i + j + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hc : (Nat.choose (i + j) i : ℂ) * i.factorial * j.factorial =
      ((i + j).factorial : ℂ) := by
    exact_mod_cast (by simpa using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)))
  unfold reciprocalCoeff
  rw [← hc]
  field_simp

/-- Normalized Leibniz rule: factorials remove the binomial coefficients. -/
theorem jet_mul (f g : ℂ → ℂ) (A : ℂ) (n : ℕ)
    (hf : ContDiffAt ℂ n f A) (hg : ContDiffAt ℂ n g A) :
    jet n (fun z => f z * g z) A =
      ∑ i ∈ Finset.range (n + 1), jet i f A * jet (n - i) g A := by
  unfold jet
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hc : (Nat.choose n i : ℂ) * i.factorial * (n - i).factorial =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  field_simp
  rw [← hc]
  ring

/-- Signed dual derivative, indexed by the derivative order on f.
This is the analytic source of the positive-side binomial op weights. -/
theorem signed_dual_derivative (f : ℂ → ℂ) (A : ℂ) (n : ℕ)
    (hf : ContDiffAt ℂ n f (-A)) :
    (-1 : ℂ) ^ n * iteratedDeriv n (fun z => Complex.exp (-z) * f (-z)) A =
      Complex.exp (-A) * ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * iteratedDeriv i f (-A) := by
  have he : ContDiffAt ℂ n (fun z : ℂ => Complex.exp (-z)) A := by fun_prop
  have hr : ContDiffAt ℂ n (fun z : ℂ => f (-z)) A :=
    hf.comp A contDiffAt_id.neg
  have hd : iteratedDeriv n (fun z => Complex.exp (-z) * f (-z)) A =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * ((-1 : ℂ) ^ i * Complex.exp (-A)) *
          ((-1 : ℂ) ^ (n - i) * iteratedDeriv (n - i) f (-A)) := by
    rw [iteratedDeriv_fun_mul he hr]
    apply Finset.sum_congr rfl
    intro i hi
    have hexp : iteratedDeriv i (fun z : ℂ => Complex.exp (-z)) A =
        (-1 : ℂ) ^ i * Complex.exp (-A) := by
      simpa using congrFun (iteratedDeriv_cexp_const_mul i (-1)) A
    rw [hexp, iteratedDeriv_comp_neg]
    rfl
  rw [hd, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_range_reflect (fun i => Complex.exp (-A) *
    ((Nat.choose n i : ℂ) * iteratedDeriv i f (-A))) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hsub : n + 1 - 1 - i = n - i := by omega
  rw [hsub, Nat.choose_symm hin]
  have hp : (-1 : ℂ) ^ n * ((-1 : ℂ) ^ i * (-1 : ℂ) ^ (n - i)) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le hin, ← pow_two, ← pow_mul]
    simp [Nat.mul_comm n 2, pow_mul]
  calc
    _ = ((-1 : ℂ) ^ n * ((-1 : ℂ) ^ i * (-1 : ℂ) ^ (n - i))) *
        (Complex.exp (-A) * ((Nat.choose n i : ℂ) * iteratedDeriv (n - i) f (-A))) := by ring
    _ = _ := by rw [hp, one_mul]

/-- Reindexing a finite triangular sum; no infinite rearrangement. -/
theorem sum_lower_swap (D : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (a + 1), F a i) =
      ∑ i ∈ Finset.range (D + 1), ∑ a ∈ Finset.Ico i (D + 1), F a i := by
  simpa only [Nat.Ico_zero_eq_range] using
    (Finset.sum_Ico_Ico_comm 0 (D + 1) (fun i a => F a i)).symm

def opMinus (q : ℕ → ℂ) (i : ℕ) : ℂ := q i * (-1 : ℂ) ^ i * i.factorial
def opPlus (D : ℕ) (q : ℕ → ℂ) (i : ℕ) : ℂ :=
  i.factorial * ∑ a ∈ Finset.Ico i (D + 1), q a * (Nat.choose a i : ℂ)

/-- The positive op array is obtained from actual dual derivatives.
Only one variable is transformed here; the two-variable application uses this
identity once per variable, retaining the swapped arguments. -/
theorem dual_op_contraction (D : ℕ) (q : ℕ → ℂ) (f : ℂ → ℂ) (A : ℂ)
    (hf : ContDiffAt ℂ D f (-A)) :
    (∑ n ∈ Finset.range (D + 1), opMinus q n *
      jet n (fun z => Complex.exp (-z) * f (-z)) A) =
      Complex.exp (-A) * ∑ i ∈ Finset.range (D + 1), opPlus D q i * jet i f (-A) := by
  have hn (n : ℕ) (hn : n ∈ Finset.range (D + 1)) :
      opMinus q n * jet n (fun z => Complex.exp (-z) * f (-z)) A =
      ∑ i ∈ Finset.range (n + 1), Complex.exp (-A) *
        (q n * (Nat.choose n i : ℂ) * iteratedDeriv i f (-A)) := by
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hnd : n ≤ D := by simpa using hn
    have hs := signed_dual_derivative f A n (hf.of_le (by exact_mod_cast hnd))
    unfold opMinus jet
    calc
      _ = q n * ((-1 : ℂ) ^ n * iteratedDeriv n
        (fun z => Complex.exp (-z) * f (-z)) A) := by field_simp
      _ = _ := by rw [hs]; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl
                  intro i hi; ring
  rw [Finset.sum_congr rfl hn, sum_lower_swap]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hfac : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  simp only [opPlus, jet, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  field_simp

theorem jet_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (A : ℂ) (n : ℕ)
    (hf : ∀ i ∈ s, ContDiffAt ℂ n (f i) A) :
    jet n (fun z => ∑ i ∈ s, f i z) A = ∑ i ∈ s, jet n (f i) A := by
  simp only [jet, iteratedDeriv_fun_sum hf, Finset.sum_div]

theorem reciprocal_slice_smooth (A B : ℂ) (h : A + B ≠ 0) (i j : ℕ) :
    ContDiffAt ℂ i (fun a => jet j (fun b => 1 / (a + b)) B) A := by
  simp only [denominator_jet]
  have he : (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) := by omega
  simp only [he, zpow_neg, zpow_natCast]
  have hp : (A + B) ^ (j + 1) ≠ 0 := pow_ne_zero _ h
  fun_prop

theorem jet_const_mul (n : ℕ) (c : ℂ) (f : ℂ → ℂ) (A : ℂ) :
    jet n (fun z => c * f z) A = c * jet n f A := by
  simp only [jet, iteratedDeriv_const_mul_field, mul_div_assoc]

/-- The separable numerator quotient is expanded by genuine iterated
derivatives, on the open set A+B != 0. -/
theorem quotient_separable_jet (f g : ℂ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (i j : ℕ) (hf : ContDiff ℂ i f) (hg : ContDiff ℂ j g) :
    jet₂ i j (fun a b => f a * g b / (a + b)) A B =
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        jet a f A * jet b g B * reciprocalCoeff (A + B) (i - a) (j - b) := by
  have hx : ∀ᶠ x : ℂ in nhds A, x + B ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne h
  have hi' : (fun x => jet j (fun y => f x * g y / (x + y)) B) =ᶠ[nhds A]
      (fun x => ∑ b ∈ Finset.range (j + 1),
        f x * jet b g B * jet (j - b) (fun y => 1 / (x + y)) B) := by
    filter_upwards [hx] with x hx
    have he : (fun y => f x * g y / (x + y)) =
        (fun y => f x * (g y * (1 / (x + y)))) := by funext y; ring
    rw [he]
    rw [jet_const_mul]
    rw [jet_mul g _ B j hg.contDiffAt (by fun_prop)]
    simp only [Finset.mul_sum, mul_assoc]
  unfold jet₂
  have he := hi'.iteratedDeriv_eq i
  rw [show jet i (fun x => jet j (fun y => f x * g y / (x + y)) B) A =
      jet i (fun x => ∑ b ∈ Finset.range (j + 1),
        f x * jet b g B * jet (j - b) (fun y => 1 / (x + y)) B) A by
        exact congrArg (fun v : ℂ => v / (i.factorial : ℂ)) he]
  rw [jet_sum _ _ A i (by
    intro b hb
    exact (hf.contDiffAt.mul contDiffAt_const).mul
      (reciprocal_slice_smooth A B h i (j - b)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [jet_mul _ _ A i (hf.contDiffAt.mul contDiffAt_const)
    (reciprocal_slice_smooth A B h i (j - b))]
  apply Finset.sum_congr rfl
  intro a ha
  have hr := reciprocal_mixed_jet A B h (i - a) (j - b)
  change _ * jet₂ (i - a) (j - b) (fun x y => 1 / (x + y)) A B = _
  rw [hr]
  simp only [jet, iteratedDeriv_mul_const_field]
  ring

/-- The matrix in the evaluator, with independent upper orders on both sides. -/
def W (D : ℕ) (op : ℕ → ℂ) (s : ℂ) (i j : ℕ) : ℂ :=
  ∑ a ∈ Finset.Ico i (D + 1), ∑ b ∈ Finset.Ico j (D + 1),
    op a * op b * reciprocalCoeff s (a - i) (b - j)

theorem W_eq_evaluator (D : ℕ) (op : ℕ → ℂ) (A : ℂ) (i j : ℕ) :
    W D op (2 * A) i j =
      ∑ a ∈ Finset.Ico i (D + 1), ∑ b ∈ Finset.Ico j (D + 1),
        op a * op b * (-1 : ℂ) ^ (a + b - i - j) *
          (Nat.choose (a + b - i - j) (a - i) : ℂ) /
            (2 * A) ^ (a + b - i - j + 1) := by
  unfold W
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : (a - i) + (b - j) = a + b - i - j := by
    simp only [Finset.mem_Ico] at ha hb
    omega
  simp only [reciprocalCoeff, he]
  ring

/-- Finite adjoint contraction of the rectangular quotient convolution. -/
theorem W_contraction (D : ℕ) (op f g : ℕ → ℂ) (s : ℂ) :
    (∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
      op a * op b * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        f i * g j * reciprocalCoeff s (a - i) (b - j))) =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op s i j * f i * g j := by
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ a ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (a + 1),
          ∑ b ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (b + 1),
            op a * op b * (f i * g j * reciprocalCoeff s (a - i) (b - j)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ i ∈ Finset.range (D + 1), ∑ a ∈ Finset.Ico i (D + 1),
          ∑ b ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (b + 1),
            op a * op b * (f i * g j * reciprocalCoeff s (a - i) (b - j)) :=
      sum_lower_swap D _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [sum_lower_swap D]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [W, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- W is the contraction of actual quotient derivatives, not an assumed
matrix of derivatives. Specialize D=6 and A=B for the witness. -/
theorem quotient_W_contraction (D : ℕ) (op : ℕ → ℂ) (f g : ℂ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (hf : ContDiff ℂ D f) (hg : ContDiff ℂ D g) :
    (∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
      op a * op b * jet₂ a b (fun x y => f x * g y / (x + y)) A B) =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op (A + B) i j * jet i f A * jet j g B := by
  rw [← W_contraction]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [quotient_separable_jet f g A B h a b
    (hf.of_le (by exact_mod_cast (show a ≤ D by simpa using ha)))
    (hg.of_le (by exact_mod_cast (show b ≤ D by simpa using hb)))]

/-- A finite polynomial differential operator acting on normalized jets. -/
def contract (D : ℕ) (op : ℕ → ℂ) (f : ℂ → ℂ) (A : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (D + 1), op n * jet n f A

def contract₂ (D : ℕ) (op : ℕ → ℂ) (H : ℂ → ℂ → ℂ) (A B : ℂ) : ℂ :=
  contract D op (fun x => contract D op (H x) B) A

theorem contract_const_mul (D : ℕ) (op : ℕ → ℂ) (c : ℂ) (f : ℂ → ℂ) (A : ℂ) :
    contract D op (fun x => c * f x) A = c * contract D op f A := by
  simp only [contract, jet_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem contract_congr (D : ℕ) (op : ℕ → ℂ) (f g : ℂ → ℂ) (A : ℂ)
    (h : f =ᶠ[nhds A] g) : contract D op f A = contract D op g A := by
  unfold contract
  apply Finset.sum_congr rfl
  intro n hn
  rw [jet, jet, h.iteratedDeriv_eq n]

theorem contract_sum {ι : Type*} (s : Finset ι) (D : ℕ) (op : ℕ → ℂ)
    (f : ι → ℂ → ℂ) (A : ℂ) (hf : ∀ i ∈ s, ContDiffAt ℂ D (f i) A) :
    contract D op (fun x => ∑ i ∈ s, f i x) A =
      ∑ i ∈ s, contract D op (f i) A := by
  unfold contract
  calc
    _ = ∑ n ∈ Finset.range (D + 1), ∑ i ∈ s, op n * jet n (f i) A := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [jet_sum s f A n (by
        intro i hi
        exact (hf i hi).of_le (by exact_mod_cast (show n ≤ D by simpa using hn)))]
      exact Finset.mul_sum _ _ _
    _ = _ := Finset.sum_comm

/-- Two independent order ranges, not a total-order cutoff. -/
theorem contract₂_rect (D : ℕ) (op : ℕ → ℂ) (H : ℂ → ℂ → ℂ) (A B : ℂ)
    (hH : ∀ b ∈ Finset.range (D + 1),
      ContDiffAt ℂ D (fun x => jet b (H x) B) A) :
    contract₂ D op H A B =
      ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
        op a * op b * jet₂ a b H A B := by
  unfold contract₂
  change contract D op (fun x => ∑ b ∈ Finset.range (D + 1), op b * jet b (H x) B) A = _
  rw [contract_sum _ D op _ A (by intro b hb; exact contDiffAt_const.mul (hH b hb))]
  simp only [contract, jet_const_mul, jet₂]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Local two-variable dual conjugation. The hypotheses state only smoothness
of slices and their jets, not the desired derivative or matrix identity.
To dualize a swapped kernel, apply this to H(x,y)=G(y,x). -/
theorem dual_contract₂ (D : ℕ) (q : ℕ → ℂ) (H : ℂ → ℂ → ℂ) (A B : ℂ)
    (hinner : ∀ᶠ x in nhds (-A), ContDiffAt ℂ D (H x) (-B))
    (houter : ∀ b ∈ Finset.range (D + 1),
      ContDiffAt ℂ D (fun x => jet b (H x) (-B)) (-A)) :
    contract₂ D (opMinus q) (fun x y => Complex.exp (-x - y) * H (-x) (-y)) A B =
      Complex.exp (-A - B) *
        ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
          opPlus D q a * opPlus D q b * jet₂ a b H (-A) (-B) := by
  have hnear : ∀ᶠ x in nhds A, ContDiffAt ℂ D (H (-x)) (-B) :=
    (continuousAt_id.neg).tendsto.eventually hinner
  have hfun : (fun x => contract D (opMinus q)
      (fun y => Complex.exp (-x - y) * H (-x) (-y)) B) =ᶠ[nhds A]
      (fun x => Complex.exp (-B) * ∑ b ∈ Finset.range (D + 1),
        opPlus D q b * (Complex.exp (-x) * jet b (H (-x)) (-B))) := by
    filter_upwards [hnear] with x hx
    have he : (fun y => Complex.exp (-x - y) * H (-x) (-y)) =
        (fun y => Complex.exp (-x) * (Complex.exp (-y) * H (-x) (-y))) := by
      funext y
      rw [sub_eq_add_neg, Complex.exp_add]
      ring
    rw [he, contract_const_mul]
    change Complex.exp (-x) * (∑ n ∈ Finset.range (D + 1), opMinus q n *
      jet n (fun y => Complex.exp (-y) * H (-x) (-y)) B) = _
    rw [dual_op_contraction D q (H (-x)) B hx]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  unfold contract₂
  rw [contract_congr D (opMinus q) _ _ A hfun, contract_const_mul]
  rw [contract_sum _ D (opMinus q) _ A (by
    intro b hb
    apply contDiffAt_const.mul
    apply ContDiffAt.mul
    · fun_prop
    · exact (houter b hb).comp A contDiffAt_id.neg)]
  simp only [contract_const_mul]
  have hd (b : ℕ) (hb : b ∈ Finset.range (D + 1)) :
      contract D (opMinus q) (fun x => Complex.exp (-x) * jet b (H (-x)) (-B)) A =
      Complex.exp (-A) * ∑ a ∈ Finset.range (D + 1),
        opPlus D q a * jet₂ a b H (-A) (-B) :=
    dual_op_contraction D q (fun x => jet b (H x) (-B)) A (houter b hb)
  calc
    _ = Complex.exp (-B) * ∑ b ∈ Finset.range (D + 1), opPlus D q b *
        (Complex.exp (-A) * ∑ a ∈ Finset.range (D + 1),
          opPlus D q a * jet₂ a b H (-A) (-B)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [hd b hb]
    _ = _ := by
      rw [sub_eq_add_neg, Complex.exp_add]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- The slice-jet regularity required by the two-variable dual is proved for
separable quotient numerators, away from the actual pole. -/
theorem quotient_slice_smooth (f g : ℂ → ℂ) (A B : ℂ) (h : A + B ≠ 0)
    (D j : ℕ) (hf : ContDiff ℂ D f) (hg : ContDiff ℂ j g) :
    ContDiffAt ℂ D (fun x => jet j (fun y => f x * g y / (x + y)) B) A := by
  have hx : ∀ᶠ x : ℂ in nhds A, x + B ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne h
  have he : (fun x => jet j (fun y => f x * g y / (x + y)) B) =ᶠ[nhds A]
      (fun x => ∑ b ∈ Finset.range (j + 1),
        f x * jet b g B * jet (j - b) (fun y => 1 / (x + y)) B) := by
    filter_upwards [hx] with x hx
    have he' : (fun y => f x * g y / (x + y)) =
        (fun y => f x * (g y * (1 / (x + y)))) := by funext y; ring
    rw [he', jet_const_mul, jet_mul g _ B j hg.contDiffAt (by fun_prop)]
    simp only [Finset.mul_sum, mul_assoc]
  apply ContDiffAt.congr_of_eventuallyEq _ he
  apply ContDiffAt.sum
  intro b hb
  exact (hf.contDiffAt.mul contDiffAt_const).mul
    (reciprocal_slice_smooth A B h D (j - b))

theorem quotient_contract₂_W (D : ℕ) (op : ℕ → ℂ) (f g : ℂ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (hf : ContDiff ℂ D f) (hg : ContDiff ℂ D g) :
    contract₂ D op (fun x y => f x * g y / (x + y)) A B =
      ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        W D op (A + B) i j * jet i f A * jet j g B := by
  rw [contract₂_rect D op _ A B (by
    intro b hb
    exact quotient_slice_smooth f g A B h D b hf
      (hg.of_le (by exact_mod_cast (show b ≤ D by simpa using hb))))]
  exact quotient_W_contraction D op f g A B h hf hg

/-- The minus sign of the dual numerator cancels the reflected denominator.
The swapped f/g order is retained on the right. -/
theorem dual_quotient_W (D : ℕ) (q : ℕ → ℂ) (f g : ℂ → ℂ) (A B : ℂ)
    (h : A + B ≠ 0) (hf : ContDiff ℂ D f) (hg : ContDiff ℂ D g) :
    contract₂ D (opMinus q)
      (fun x y => -(Complex.exp (-x - y) * (f (-y) * g (-x))) / (x + y)) A B =
      Complex.exp (-A - B) *
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          W D (opPlus D q) (-A + -B) i j * jet i g (-A) * jet j f (-B) := by
  have hn : -A + -B ≠ 0 := by simpa only [← neg_add, neg_ne_zero] using h
  have he : (fun x y => -(Complex.exp (-x - y) * (f (-y) * g (-x))) / (x + y)) =
      (fun x y => Complex.exp (-x - y) * (g (-x) * f (-y) / (-x + -y))) := by
    funext x y
    rw [← neg_add, div_neg]
    ring
  rw [he, dual_contract₂ D q (fun x y => g x * f y / (x + y)) A B]
  · rw [quotient_W_contraction D (opPlus D q) g f (-A) (-B) hn hg hf]
  · have hx : ∀ᶠ x : ℂ in nhds (-A), x + -B ≠ 0 :=
      (continuousAt_id.add continuousAt_const).eventually_ne hn
    filter_upwards [hx] with x hx
    exact (contDiffAt_const.mul hf.contDiffAt).div
      (contDiffAt_const.add contDiffAt_id) hx
  · intro b hb
    exact quotient_slice_smooth g f (-A) (-B) hn D b hg
      (hf.of_le (by exact_mod_cast (show b ≤ D by simpa using hb)))

theorem reciprocalCoeff_symm (s : ℂ) (i j : ℕ) :
    reciprocalCoeff s i j = reciprocalCoeff s j i := by
  unfold reciprocalCoeff
  have hc : Nat.choose (i + j) i = Nat.choose (i + j) j := by
    simpa using (Nat.choose_symm (Nat.le_add_right i j)).symm
  rw [hc, Nat.add_comm j i]

theorem W_symm (D : ℕ) (op : ℕ → ℂ) (s : ℂ) (i j : ℕ) :
    W D op s i j = W D op s j i := by
  unfold W
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [reciprocalCoeff_symm]
  ring

/-- Symmetry after contraction; unlike an undifferentiated diagonal identity,
this applies to independent derivative arrays on the two sides. -/
theorem W_profile_swap (D : ℕ) (op f g : ℕ → ℂ) (s : ℂ) :
    (∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D op s i j * f i * g j) =
    ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
      W D op s i j * g i * f j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [W_symm D op s j i]
  ring

set_option maxHeartbeats 800000 in
theorem dual_quotient_diagonal (D : ℕ) (q : ℕ → ℂ) (f g : ℂ → ℂ) (A : ℂ)
    (h : A ≠ 0) (hf : ContDiff ℂ D f) (hg : ContDiff ℂ D g) :
    contract₂ D (opMinus q)
      (fun x y => -(Complex.exp (-x - y) * (f (-y) * g (-x))) / (x + y)) A A =
      Complex.exp (-2 * A) *
        ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          W D (opPlus D q) (2 * -A) i j * jet i f (-A) * jet j g (-A) := by
  have hsum : A + A ≠ 0 := by rw [← two_mul]; exact mul_ne_zero (by norm_num) h
  rw [dual_quotient_W D q f g A A hsum hf hg, W_profile_swap]
  congr 1
  · congr 1
    ring
  · rw [two_mul]

#print axioms quotient_slice_smooth
#print axioms quotient_contract₂_W
#print axioms dual_quotient_W
#print axioms W_symm
#print axioms W_profile_swap
#print axioms dual_quotient_diagonal
#print axioms dual_contract₂
#print axioms contract₂_rect
#print axioms W_eq_evaluator
#print axioms W_contraction
#print axioms quotient_W_contraction
#print axioms dual_op_contraction
#print axioms reciprocal_slice_smooth
#print axioms quotient_separable_jet
#print axioms reciprocal_mixed_jet
#print axioms jet_mul
#print axioms signed_dual_derivative
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

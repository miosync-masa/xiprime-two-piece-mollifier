import TaylorEnvelope

/-! Exact beta-coefficient semantics of the differentiate-then-truncate evaluator.
No floating-point or Python execution semantics are asserted. -/
noncomputable section
open scoped BigOperators Interval
open Polynomial

namespace XiPrime8845.CoefficientEvaluator
open IntegralJet TaylorEnvelope FiniteJet
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem complex_beta (j d : ℕ) (w : ℝ) :
    (∫ x in 0..w, (x : ℂ)^j * ((w-x : ℝ) : ℂ)^d) =
      (j.factorial : ℂ) * d.factorial / (j+d+1).factorial * (w : ℂ)^(j+d+1) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (BetaKernel.beta_monomial j d w)
  simpa only [← intervalIntegral.integral_ofReal, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using h

/-- The coefficient inserted by the k=1 inverse branch of fs. -/
def inverseCoeff (a j d : ℕ) (p A : ℂ) (θ : ℝ) : ℂ :=
  p / (θ : ℂ)^d * (-1 : ℂ)^a * (-A)^j * (a+j).factorial * d.factorial /
    ((a.factorial : ℂ) * j.factorial * (d+1+a+j).factorial)

def inversePoly (N a : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) : Polynomial ℂ :=
  ∑ d ∈ F.support, ∑ j ∈ Finset.range (N+1),
    C (inverseCoeff a j d (F.coeff d) A θ) * X^(d+1+a+j)

theorem inverse_term (a j d : ℕ) (p A : ℂ) (θ w : ℝ) :
    (∫ y in 0..w, (p / (θ : ℂ)^d * (-1 : ℂ)^a * (-A)^j /
      ((a.factorial : ℂ)*j.factorial)) * ((y : ℂ)^(a+j) * ((w-y : ℝ) : ℂ)^d)) =
      inverseCoeff a j d p A θ * (w : ℂ)^(d+1+a+j) := by
  rw [intervalIntegral.integral_const_mul, complex_beta]
  have he : a+j+d+1 = d+1+a+j := by omega
  rw [he]
  unfold inverseCoeff
  ring

/-- Repeated output degrees are added, as in the evaluator's plus dictionary helper. -/
theorem inversePoly_coeff (N a b : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) :
    (inversePoly N a A θ F).coeff b =
      ∑ d ∈ F.support, ∑ j ∈ Finset.range (N+1),
        if d+1+a+j = b then inverseCoeff a j d (F.coeff d) A θ else 0 := by
  simp [inversePoly, Polynomial.finsetSum_coeff, eq_comm]

theorem inversePoly_eval (N a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) :
    (inversePoly N a A θ F).eval (w : ℂ) = inverseApprox N a A θ w F := by
  classical
  rw [inverseApprox, ← intervalIntegral.integral_div]
  have he : (fun y : ℝ =>
      (-(y : ℂ))^a * expPartial N (-A*y) * F.eval (((w-y)/θ : ℝ) : ℂ) / a.factorial) =
      fun y : ℝ => ∑ d ∈ F.support, ∑ j ∈ Finset.range (N+1),
        (F.coeff d / (θ : ℂ)^d * (-1 : ℂ)^a * (-A)^j /
          ((a.factorial : ℂ)*j.factorial)) * ((y : ℂ)^(a+j) * ((w-y : ℝ) : ℂ)^d) := by
    funext y
    simp only [expPartial, Polynomial.eval_eq_sum, Polynomial.sum,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_pow (y : ℂ) a]
    push_cast
    simp only [mul_pow, pow_add,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, intervalIntegral.integral_finsetSum]
  · simp only [inversePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro d hd
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact (inverse_term a j d (F.coeff d) A θ w).symm
    · intro j hj
      apply Continuous.intervalIntegrable
      fun_prop
  · intro d hd
    apply Continuous.intervalIntegrable
    fun_prop

def scale (θ : ℝ) (F : Polynomial ℂ) : Polynomial ℂ :=
  F.comp (C (θ : ℂ)⁻¹ * X)

theorem scale_eval (θ w : ℝ) (F : Polynomial ℂ) :
    (scale θ F).eval (w : ℂ) = F.eval (((w/θ : ℝ) : ℂ)) := by
  simp only [scale, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Complex.ofReal_div]
  congr 1
  ring

/-- Polynomial represented by fs(P,e,A)[a], for the three K2 exponents. -/
def fsPoly (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ : ℝ) (F : Polynomial ℂ) : Polynomial ℂ :=
  if e = -1 then inversePoly N a A θ F
  else if a = 0 then
    if e = 1 then C (θ : ℂ)⁻¹ * scale θ F.derivative + C A * scale θ F
    else if e = 0 then scale θ F else 0
  else if e = 1 ∧ a = 1 then scale θ F else 0

theorem fsPoly_eval (N : ℕ) (e : ℤ) (a : ℕ) (A : ℂ) (θ w : ℝ) (F : Polynomial ℂ) :
    (fsPoly N e a A θ F).eval (w : ℂ) = operatorApprox N e a A θ w F := by
  by_cases hm : e = -1
  · simp [fsPoly, operatorApprox, hm, inversePoly_eval]
  · simp only [fsPoly, operatorApprox, operatorJet, hm, ↓reduceIte]
    split_ifs <;> simp_all [BetaKernel.D, scale_eval, div_eq_mul_inv, mul_comm]

/-- The outer beta sum, indexed as in the evaluator's theta^(d+n)*d!/(d+n)!. -/
def betaEval (n : ℕ) (θ : ℝ) (P : Polynomial ℂ) : ℂ :=
  ∑ d ∈ P.support, P.coeff d * ((θ : ℂ)^(d+n) * d.factorial / (d+n).factorial)

theorem betaEval_integral (n : ℕ) (hn : 0 < n) (θ : ℝ) (P : Polynomial ℂ) :
    betaEval n θ P = ∫ v in 0..θ,
      (v : ℂ)^(n-1) / ((n-1).factorial : ℂ) * P.eval ((θ-v : ℝ) : ℂ) := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · unfold betaEval
    apply Finset.sum_congr rfl
    intro d hd
    have he : (fun v : ℝ => (v : ℂ)^(n-1) / ((n-1).factorial : ℂ) *
        (P.coeff d * ((θ-v : ℝ) : ℂ)^d)) =
        fun v : ℝ => P.coeff d / ((n-1).factorial : ℂ) *
          ((v : ℂ)^(n-1) * ((θ-v : ℝ) : ℂ)^d) := by funext v; ring
    rw [he, intervalIntegral.integral_const_mul, complex_beta]
    have he : n-1+d+1 = d+n := by omega
    rw [he]
    have hf : ((n-1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-1)
    field_simp
  · intro d hd
    apply Continuous.intervalIntegrable
    fun_prop

theorem monomial_coefficients (N : ℕ) (e f : ℤ) (n i j : ℕ) (hn : 0 < n)
    (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    monomialApprox N e f n i j A B θ F G =
      betaEval n θ (fsPoly N e i A θ F * fsPoly N f j B θ G) := by
  rw [betaEval_integral n hn, monomialApprox]
  congr 1
  funext v
  rw [Polynomial.eval_mul, fsPoly_eval, fsPoly_eval]
  ring

/-- Linearity of the outer beta coefficient sum. -/
def betaMap (n : ℕ) (θ : ℝ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  Polynomial.lsum (fun d =>
    { toFun := fun c => c * ((θ : ℂ)^(d+n) * d.factorial / (d+n).factorial)
      map_add' := by intros; ring
      map_smul' := by intros; simp only [smul_eq_mul, RingHom.id_apply]; ring })

theorem betaMap_apply (n : ℕ) (θ : ℝ) (P : Polynomial ℂ) :
    betaMap n θ P = betaEval n θ P := rfl

theorem betaEval_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ) (n : ℕ) (θ : ℝ) :
    betaEval n θ (∑ i ∈ s, p i) = ∑ i ∈ s, betaEval n θ (p i) :=
  map_sum (betaMap n θ) p s

theorem betaEval_C_mul (n : ℕ) (θ : ℝ) (c : ℂ) (P : Polynomial ℂ) :
    betaEval n θ (C c * P) = c * betaEval n θ P := by
  change betaMap n θ (C c * P) = c * betaMap n θ P
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  rfl

/-- The evaluator's cached contraction polynomial before outer integration. -/
def fusedPoly (D : ℕ) (W : ℕ → ℕ → ℂ) (f g : ℕ → Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1), C (W i j) * (f i * g j)

theorem fusedPoly_beta (D n : ℕ) (θ : ℝ) (W : ℕ → ℕ → ℂ) (f g : ℕ → Polynomial ℂ) :
    betaEval n θ (fusedPoly D W f g) =
      ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
        W i j * betaEval n θ (f i * g j) := by
  simp only [fusedPoly, betaEval_sum, betaEval_C_mul]

/-- First form wg for each left jet, then multiply and accumulate the polynomial. -/
theorem fusedPoly_cached (D : ℕ) (W : ℕ → ℕ → ℂ) (f g : ℕ → Polynomial ℂ) :
    fusedPoly D W f g = ∑ i ∈ Finset.range (D+1),
      f i * (∑ j ∈ Finset.range (D+1), C (W i j) * g j) := by
  simp only [fusedPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Polynomial multiplication accumulates precisely at degree da+db. -/
theorem fusedPoly_coeff (D d : ℕ) (W : ℕ → ℕ → ℂ) (f g : ℕ → Polynomial ℂ) :
    (fusedPoly D W f g).coeff d =
      ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
        W i j * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d,
          (f i).coeff ab.1 * (g j).coeff ab.2 := by
  simp only [fusedPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  simp only [Polynomial.coeff_mul]

def Hcoeff (N l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  BetaKernel.poleSum l m (fun e f n =>
    betaEval n θ (fsPoly N e i A θ F * fsPoly N f j B θ G)) / (θ : ℂ)^(l+m)

theorem HApprox_coefficients (N l m i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    HApprox N l m i j A B θ F G = Hcoeff N l m i j A B θ F G := by
  unfold HApprox Hcoeff BetaKernel.poleSum
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  rw [monomial_coefficients N _ _ _ i j (by omega) A B θ F G]

def fourCoeff (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  Hcoeff N 0 0 i j A B θ F F + Hcoeff N 0 2 i j A B θ F G +
    Hcoeff N 2 0 i j A B θ G F + Hcoeff N 2 2 i j A B θ G G

theorem fourApprox_coefficients (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    fourApprox N i j A B θ F G = fourCoeff N i j A B θ F G := by
  simp only [fourApprox, fourCoeff, HApprox_coefficients]

/-- Coefficient-only semantics: no integral or derivative occurs in this definition. -/
def coefficientEvaluator (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℂ :=
  (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
    W D (opMinus q) (A+B) i j * fourCoeff N i j A B θ F G) +
  Complex.exp (-A-B) *
    ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
      W D (opPlus D q) (-A + -B) i j * fourCoeff N i j (-A) (-B) θ F G

theorem finiteEvaluator_coefficients (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) :
    finiteEvaluator N D q A B θ F G = coefficientEvaluator N D q A B θ F G := by
  simp only [finiteEvaluator, coefficientEvaluator, fourApprox_coefficients]

theorem K2_coefficient_enclosure (N D : ℕ) (q : ℕ → ℂ) (A B : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) (h : A+B ≠ 0) (hθ : 0 < θ)
    (hA : ‖A‖*θ ≤ 1) (hB : ‖B‖*θ ≤ 1) :
    ‖contract₂ D (opMinus q) (fun x y => BetaKernel.shiftedFunctional x y θ F G) A B -
      coefficientEvaluator N D q A B θ F G‖ ≤ evaluatorError N D q A B θ F G := by
  rw [← finiteEvaluator_coefficients]
  exact K2_Taylor_enclosure N D q A B θ F G h hθ hA hB

theorem weighted_poleSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (l m : ℕ)
    (E : ι → ℤ → ℤ → ℕ → ℂ) :
    (∑ a ∈ s, c a * BetaKernel.poleSum l m (E a)) =
      BetaKernel.poleSum l m (fun e f n => ∑ a ∈ s, c a * E a e f n) := by
  simp only [BetaKernel.poleSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem Hcoeff02_swap (N i j : ℕ) (A B : ℂ) (θ : ℝ) (F G : Polynomial ℂ) :
    Hcoeff N 0 2 i j A B θ F G = Hcoeff N 2 0 j i B A θ G F := by
  simp only [Hcoeff, BetaKernel.assemble02, BetaKernel.assemble20]
  simp only [mul_comm]

def pairEvaluator (N D l m : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℂ :=
  ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
    W D op (2*A) i j * Hcoeff N l m i j A A θ F G

/-- The pole-loop computation with cached W-contracted polynomials. -/
def pairFusedEvaluator (N D l m : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℂ :=
  BetaKernel.poleSum l m (fun e f n => betaEval n θ
    (fusedPoly D (W D op (2*A))
      (fun i => fsPoly N e i A θ F) (fun j => fsPoly N f j A θ G))) / (θ : ℂ)^(l+m)

theorem pairEvaluator_fused (N D l m : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) :
    pairEvaluator N D l m op A θ F G = pairFusedEvaluator N D l m op A θ F G := by
  unfold pairEvaluator Hcoeff pairFusedEvaluator
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp_rw [weighted_poleSum]
  have ho := weighted_poleSum (Finset.range (D+1)) (fun _ => 1) l m
    (fun i e f n => ∑ j ∈ Finset.range (D+1),
      W D op (2*A) i j * betaEval n θ (fsPoly N e i A θ F * fsPoly N f j A θ G))
  simp only [one_mul] at ho
  rw [ho]
  simp only [fusedPoly_beta]

theorem pair_cross_swap (N D : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) :
    pairEvaluator N D 0 2 op A θ F G = pairEvaluator N D 2 0 op A θ G F := by
  unfold pairEvaluator
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [W_symm, Hcoeff02_swap]

/-- The three profile pairs retained by the evaluator's symmetry=1,2,1 loop. -/
def sideEvaluator (N D : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) : ℂ :=
  pairEvaluator N D 0 0 op A θ F F + 2 * pairEvaluator N D 0 2 op A θ F G +
    pairEvaluator N D 2 2 op A θ G G

theorem fourCoeff_contracted (N D : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ)
    (F G : Polynomial ℂ) :
    (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
      W D op (2*A) i j * fourCoeff N i j A A θ F G) =
      sideEvaluator N D op A θ F G := by
  simp only [fourCoeff, mul_add, Finset.sum_add_distrib]
  change pairEvaluator N D 0 0 op A θ F F + pairEvaluator N D 0 2 op A θ F G +
    pairEvaluator N D 2 0 op A θ G F + pairEvaluator N D 2 2 op A θ G G = _
  rw [← pair_cross_swap]
  unfold sideEvaluator
  ring

/-- Exact arithmetic semantics of the two-sign, symmetry-reduced evaluator. -/
theorem coefficientEvaluator_diagonal (N D : ℕ) (q : ℕ → ℂ) (R θ : ℝ)
    (F G : Polynomial ℂ) :
    coefficientEvaluator N D q (-R) (-R) θ F G =
      sideEvaluator N D (opMinus q) (-R) θ F G + Complex.exp (2*(R : ℂ)) *
        sideEvaluator N D (opPlus D q) R θ F G := by
  unfold coefficientEvaluator
  simp only [neg_neg, ← two_mul]
  rw [fourCoeff_contracted, fourCoeff_contracted]
  congr 2
  ring

def cachedSide (N D : ℕ) (op : ℕ → ℂ) (A : ℂ) (θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  pairFusedEvaluator N D 0 0 op A θ F F + 2 * pairFusedEvaluator N D 0 2 op A θ F G +
    pairFusedEvaluator N D 2 2 op A θ G G

/-- Exact complex-arithmetic model of the evaluator's total, before interval rounding. -/
def cachedEvaluator (N D : ℕ) (q : ℕ → ℂ) (R θ : ℝ) (F G : Polynomial ℂ) : ℂ :=
  cachedSide N D (opMinus q) (-R) θ F G + Complex.exp (2*(R : ℂ)) *
    cachedSide N D (opPlus D q) R θ F G

theorem finiteEvaluator_cached (N D : ℕ) (q : ℕ → ℂ) (R θ : ℝ) (F G : Polynomial ℂ) :
    finiteEvaluator N D q (-R) (-R) θ F G = cachedEvaluator N D q R θ F G := by
  rw [finiteEvaluator_coefficients, coefficientEvaluator_diagonal]
  simp only [sideEvaluator, pairEvaluator_fused, cachedEvaluator, cachedSide]

theorem K2_cached_enclosure (N D : ℕ) (q : ℕ → ℂ) (R θ : ℝ) (F G : Polynomial ℂ)
    (hR : R ≠ 0) (hθ : 0 < θ) (hsize : |R| * θ ≤ 1) :
    ‖contract₂ D (opMinus q) (fun x y => BetaKernel.shiftedFunctional x y θ F G) (-R) (-R) -
      cachedEvaluator N D q R θ F G‖ ≤ evaluatorError N D q (-R) (-R) θ F G := by
  have hn : (-(R : ℂ)) + (-(R : ℂ)) ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr (by exact_mod_cast hR))
  have hs : ‖-(R : ℂ)‖*θ ≤ 1 := by simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using hsize
  simpa only [finiteEvaluator_cached] using K2_Taylor_enclosure N D q (-R) (-R) θ F G hn hθ hs hs

#print axioms complex_beta
#print axioms inversePoly_eval
#print axioms inversePoly_coeff
#print axioms fsPoly_eval
#print axioms betaEval_integral
#print axioms monomial_coefficients
#print axioms fusedPoly_beta
#print axioms fusedPoly_coeff
#print axioms fusedPoly_cached
#print axioms HApprox_coefficients
#print axioms finiteEvaluator_coefficients
#print axioms K2_coefficient_enclosure
#print axioms pair_cross_swap
#print axioms weighted_poleSum
#print axioms pairEvaluator_fused
#print axioms coefficientEvaluator_diagonal
#print axioms finiteEvaluator_cached
#print axioms K2_cached_enclosure
end XiPrime8845.CoefficientEvaluator

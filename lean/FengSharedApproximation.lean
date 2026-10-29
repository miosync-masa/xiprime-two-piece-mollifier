import FengResidual
import CoprimeEulerCompletion

/-! Finite coprime-main replacement for the shared block. The proxy retains
all translated profiles; its error is not asserted to be o(1). -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.FengSharedApproximation
open FengAtG FengResidual CoprimeShift CoprimeEulerCompletion
set_option maxHeartbeats 1000000

def transform (N g : ℕ) (L : ℝ) (A : ℂ) (X : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
    (μ (g/p^(g.factorization p)):ℂ) *
      ∑ a ∈ range (Nat.log p N+1), supportFactor (p^a) L A*X p a

def actualArray (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) (p a : ℕ) : ℂ :=
  coprimeScaled (N/p^a) ((g/p^(g.factorization p))*p)
    L (u-Real.log (p^a)/L) θ P A

def mainArray (g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) (p a : ℕ) : ℂ :=
  zeroEulerMain ((g/p^(g.factorization p))*p) (u-Real.log (p^a)/L) θ P A

def mainProxy (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  transform N g L A (mainArray g L u θ P A)

theorem sharedBlock_transform (N g : ℕ) (hg : g ≠ 0)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    sharedBlock N g L u θ P A = transform N g L A (actualArray N g L u θ P A) :=
  sharedBlock_coprimeScaled N g hg L u θ P A

theorem transform_sub (N g : ℕ) (L : ℝ) (A : ℂ) (X Y : ℕ → ℕ → ℂ) :
    transform N g L A X-transform N g L A Y =
      transform N g L A (fun p a => X p a-Y p a) := by
  simp only [transform,mul_sub,Finset.sum_sub_distrib]

def errorWeight (p g : ℕ) (L : ℝ) : ℝ :=
  (Real.log p)^2/|L|^2 * ‖(μ (g/p^(g.factorization p)):ℂ)‖

theorem transform_error (N g : ℕ) (L : ℝ) (A : ℂ) (X Y : ℕ → ℕ → ℂ) :
    ‖transform N g L A X-transform N g L A Y‖ ≤
      ∑ p ∈ g.primeFactors, errorWeight p g L *
        ∑ a ∈ range (Nat.log p N+1), ‖supportFactor (p^a) L A‖*‖X p a-Y p a‖ := by
  rw [transform_sub,transform]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul,norm_mul,norm_div,norm_pow,norm_pow,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_mul] using norm_sum_le (range (Nat.log p N+1))
    (fun a => supportFactor (p^a) L A*(X p a-Y p a))

def errorBudget (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℝ :=
  ∑ p ∈ g.primeFactors, errorWeight p g L *
    ∑ a ∈ range (Nat.log p N+1), ‖supportFactor (p^a) L A‖ *
      ‖actualArray N g L u θ P A p a-mainArray g L u θ P A p a‖

theorem errorBudget_nonneg (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    0 ≤ errorBudget N g L u θ P A := by
  unfold errorBudget errorWeight
  positivity

theorem sharedBlock_main_error (N g : ℕ) (hg : g ≠ 0)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    ‖sharedBlock N g L u θ P A-mainProxy N g L u θ P A‖ ≤
      errorBudget N g L u θ P A := by
  rw [sharedBlock_transform N g hg,mainProxy]
  exact transform_error N g L A _ _

/-- Actual finite arithmetic error returned to the outer harmonic average.
Neither a fixed-g limit nor a rate uniform in g is smuggled in here. -/
theorem shared_error_average (M : ℕ) (N : ℕ → ℕ) (L θ : ℝ) (u : ℕ → ℝ)
    (P : Polynomial ℂ) (A : ℂ) :
    (∑ g ∈ Icc 1 M, (1/(g:ℝ))*
      ‖sharedBlock (N g) g L (u g) θ P A-mainProxy (N g) g L (u g) θ P A‖) ≤
      ∑ g ∈ Icc 1 M, (1/(g:ℝ))*errorBudget (N g) g L (u g) θ P A := by
  apply sum_le_sum
  intro g hg
  have hg0 : g ≠ 0 := by have := (mem_Icc.mp hg).1; omega
  exact mul_le_mul_of_nonneg_left (sharedBlock_main_error (N g) g hg0 L (u g) θ P A) (by positivity)

#print axioms sharedBlock_transform
#print axioms transform_sub
#print axioms transform_error
#print axioms errorBudget_nonneg
#print axioms sharedBlock_main_error
#print axioms shared_error_average
end XiPrime8845.FengSharedApproximation

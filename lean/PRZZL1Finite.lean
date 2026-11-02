import PRZZInterface

/-! L1 bookkeeping for the direct approximate-functional-equation block.
The two AFE indices are finitely truncated; the mollifier is the literal
PRZZ polynomial. This proves neither the AFE nor removal of its truncation,
Poisson summation, or the reduction to A*. Those analytic steps are separate.
-/
noncomputable section
open scoped BigOperators
open Finset Complex
namespace XiPrime8845.PRZZL1Finite

def directTerm (alpha beta : ℂ) (V : ℕ → ℝ → ℂ) (t : ℝ) (m k : ℕ) : ℂ :=
  V (m*k) t / ((m:ℂ)^(1/2+alpha+t*I)*(k:ℂ)^(1/2+beta-t*I))

def directSum (M : ℕ) (alpha beta : ℂ) (V : ℕ → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 M, ∑ k ∈ Icc 1 M, directTerm alpha beta V t m k

def term (a b : ℕ → ℂ) (alpha beta : ℂ) (V : ℕ → ℝ → ℂ)
    (t : ℝ) (m k n r : ℕ) : ℂ :=
  directTerm alpha beta V t m k * (a n/(n:ℂ)^(1/2+t*I)) *
    star (b r/(r:ℂ)^(1/2+t*I))

/-- Exact finite expansion, retaining the conjugated second mollifier. -/
theorem direct_expansion (M N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (V : ℕ → ℝ → ℂ) (t : ℝ) :
    directSum M alpha beta V t * PRZZ.dirichletPolynomial a N (1/2+t*I) *
      star (PRZZ.dirichletPolynomial b N (1/2+t*I)) =
      ∑ m ∈ Icc 1 M, ∑ k ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        term a b alpha beta V t m k n r := by
  rw [directSum,Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl; intro m hm
  rw [Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl; intro k hk
  simp only [PRZZ.dirichletPolynomial,star_sum,Finset.mul_sum,Finset.sum_mul,term]
  rw [Finset.sum_comm]

/-- The diagonal is m*n=k*r for this explicit choice of zeta/mollifier
index order. No reciprocal phase or coprimality reindexing is hidden. -/
theorem diagonal_split (M N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (V : ℕ → ℝ → ℂ) (t : ℝ) :
    directSum M alpha beta V t * PRZZ.dirichletPolynomial a N (1/2+t*I) *
      star (PRZZ.dirichletPolynomial b N (1/2+t*I)) =
      (∑ m ∈ Icc 1 M, ∑ k ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        if m*n=k*r then term a b alpha beta V t m k n r else 0) +
      (∑ m ∈ Icc 1 M, ∑ k ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
        if m*n=k*r then 0 else term a b alpha beta V t m k n r) := by
  rw [direct_expansion]
  simp only [← Finset.sum_add_distrib]
  apply sum_congr rfl; intro m hm
  apply sum_congr rfl; intro k hk
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro r hr
  split_ifs <;> simp

#print axioms direct_expansion
#print axioms diagonal_split
end XiPrime8845.PRZZL1Finite

import FengShared

/-! Exact sharedBlock after global prime-string cancellation. Residual sums
still range over the original n cutoff; their asymptotics are not assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.FengSharedBlock
open FengAtG FengShared ShiftWeights
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- Swap the actual n sum and the primes of g only after local cancellation. -/
theorem shared_weighted (N g : ℕ) (hg : g ≠ 0) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, shared g n*w n) =
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2 * ∑ n ∈ Icc 1 N,
        (μ ((g/p^(g.factorization p))*(n/p^(n.factorization p))):ℂ)*w n := by
  trans ∑ n ∈ Icc 1 N, ∑ p ∈ g.primeFactors,
    (μ ((g/p^(g.factorization p))*(n/p^(n.factorization p))):ℂ)*(Real.log p:ℂ)^2*w n
  · apply sum_congr rfl
    intro n hn
    rw [shared_eq_residue_products g n hg (by have := (mem_Icc.mp hn).1; omega),Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intros
  ring

/-- The p-free residual inner sum. It is not the unrestricted Mobius sum:
the profile and denominator still use n, not its p-free part. -/
def residualInner (N p h : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N,
    (if (n/p^(n.factorization p)).Coprime h then (μ (n/p^(n.factorization p)):ℂ) else 0)/n *
      weight A u θ P (Real.log n/L)

/-- Exact residual formula for sharedBlock. The p-free part of g may be
non-squarefree; its Mobius factor is retained, never replaced by mu(g). -/
theorem sharedBlock_residual (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ)
    (hg : g ≠ 0) :
    sharedBlock N g L u θ P A =
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ) * ((L:ℂ)*residualInner N p
          (g/p^(g.factorization p)) L u θ P A) := by
  have he : sharedBlock N g L u θ P A = (L:ℂ)/(L:ℂ)^2 *
      ∑ n ∈ Icc 1 N, shared g n*(weight A u θ P (Real.log n/L)/(n:ℂ)) := by
    simp only [sharedBlock,Finset.mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [he,shared_weighted N g hg,Finset.mul_sum]
  apply sum_congr rfl
  intro p hp
  simp only [residualInner,Finset.mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [SmoothMobius.moebius_mul_indicator]
  ring

theorem residualInner_entire (N p h : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℂ ⊤ (residualInner N p h L u θ P) := by
  unfold residualInner weight
  fun_prop

theorem sharedBlock_entire (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) :
    ContDiff ℂ ⊤ (sharedBlock N g L u θ P) := by
  unfold sharedBlock weight
  fun_prop

/-- A finite absolute bound for arbitrary complex weights, after cancellation.
This is not asserted to be a sufficiently sharp asymptotic or endpoint bound. -/
theorem shared_weighted_norm (N g : ℕ) (hg : g ≠ 0) (w : ℕ → ℂ) :
    ‖∑ n ∈ Icc 1 N, shared g n*w n‖ ≤
      (∑ p ∈ g.primeFactors, (Real.log p)^2) * ∑ n ∈ Icc 1 N, ‖w n‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (shared_norm_le g n hg (by have := (mem_Icc.mp hn).1; omega)) (norm_nonneg _)

/-- The bound keeps the actual profile weight and the exact original cutoff. -/
theorem sharedBlock_norm (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ)
    (hg : g ≠ 0) :
    ‖sharedBlock N g L u θ P A‖ ≤
      (|L|/|L|^2) * ((∑ p ∈ g.primeFactors, (Real.log p)^2) *
        ∑ n ∈ Icc 1 N, ‖weight A u θ P (Real.log n/L)‖/(n:ℝ)) := by
  have he : sharedBlock N g L u θ P A = (L:ℂ)/(L:ℂ)^2 *
      ∑ n ∈ Icc 1 N, shared g n*(weight A u θ P (Real.log n/L)/(n:ℂ)) := by
    simp only [sharedBlock,Finset.mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [he,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have h := shared_weighted_norm N g hg (fun n => weight A u θ P (Real.log n/L)/(n:ℂ))
  simp only [norm_div,Complex.norm_natCast] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

#print axioms shared_weighted
#print axioms sharedBlock_residual
#print axioms residualInner_entire
#print axioms sharedBlock_entire
#print axioms shared_weighted_norm
#print axioms sharedBlock_norm
end XiPrime8845.FengSharedBlock

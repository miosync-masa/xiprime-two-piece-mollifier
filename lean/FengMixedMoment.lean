import FengMarkedCrossLimit

/-! Signed Conrey/shared arithmetic moment. The Mobius factor on the Conrey
side kills non-squarefree g; this is not valid for the shared/shared moment.
The scalar limit does not yet assert a full K20 or K22 asymptotic. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengMixedMoment
open FengMarkedProfile TotientCoprime FengMertensModels FengMarkedDiagonal
set_option maxHeartbeats 1000000

theorem mobius_mark (g : ℕ) :
    (μ g:ℂ)*primeMoment g = -(μ g:ℂ)^2 *
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2 := by
  simp only [primeMoment,mul_sum]
  apply sum_congr rfl
  intro p hp
  by_cases hs : Squarefree g
  · rw [FengMarkedArithmetic.mobius_residue_squarefree g p hs
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    push_cast
    ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

def weight (g : ℕ) : ℝ := (μ g:ℝ)*(primeMoment g).re/g.totient

theorem weight_eq (g : ℕ) :
    weight g = -TotientConvolution.weight g * ∑ p ∈ g.primeFactors, (Real.log p)^2 := by
  have h := mobius_mark g
  rw [← FengMarkedAbel.primeMoment_real] at h
  norm_cast at h
  push_cast at h
  change (μ g:ℝ)*(primeMoment g).re/(g.totient:ℝ) =
    -((μ g:ℝ)^2/(g.totient:ℝ)) * _
  rw [h]
  ring

theorem weight_nonpos (g : ℕ) : weight g ≤ 0 := by
  rw [weight_eq]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (TotientCoprime.weight_nonneg g))
    (sum_nonneg (fun _ _ => sq_nonneg _))

def summatory (x : ℝ) : ℝ := ∑ g ∈ Ioc 0 ⌊x⌋₊, weight g
def primeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    (Real.log p)^2 * (restricted (N/p) p/(p-1:ℝ))

/-- Exact reindexing, including the original cutoff and prime coprimality. -/
theorem summatory_reindex (x : ℝ) : summatory x = -primeSum ⌊x⌋₊ := by
  have hi : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by
    ext n; simp only [mem_Ioc,mem_Icc]; omega
  unfold summatory
  rw [hi]
  simp_rw [weight_eq,mul_sum]
  rw [sum_congr rfl (fun n hn => FengMarkedDecomposition.prime_sum ⌊x⌋₊ n hn
    (fun p => -TotientConvolution.weight n*(Real.log p)^2)),sum_comm]
  unfold primeSum
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← TotientCoprime.multiples _ p (mem_filter.mp hp).2,sum_filter,mul_sum,
    ← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> ring

theorem primeSum_error (X : ℝ) (hX : 0 ≤ X) :
    |primeSum ⌊Real.exp X⌋₊-smooth 2 X| ≤
      2*TotientHarmonic.errorConstant*moment 2 X+
        (6*X+4*TotientHarmonic.errorConstant)*Zeta23.XiPrime.Cdef := by
  have hi : Icc 1 ⌊Real.exp X⌋₊ = Ioc 0 ⌊Real.exp X⌋₊ := by
    ext n; simp only [mem_Icc,mem_Ioc]; omega
  unfold primeSum smooth
  rw [hi]
  change |(∑ p ∈ primes X, _) - ∑ p ∈ primes X, _| ≤ _
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primes X, (Real.log p)^2 *
        (2*TotientHarmonic.errorConstant/(p:ℝ)+
          (6*X+4*TotientHarmonic.errorConstant)/(p:ℝ)^2) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro p hp
      have he : (Real.log p)^2*(restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ))-
          (Real.log p)^2/(p:ℝ)*(X-Real.log p) =
          (Real.log p)^2*(restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)-(X-Real.log p)/(p:ℝ)) := by ring
      rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (head_point_error X hX p hp) (sq_nonneg _)
    _ = 2*TotientHarmonic.errorConstant*moment 2 X+
        (6*X+4*TotientHarmonic.errorConstant)*FengMarkedCrossLimit.squareMoment X := by
      unfold moment FengMarkedCrossLimit.squareMoment
      simp only [mul_sum,← sum_add_distrib]
      apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (FengMarkedCrossLimit.squareMoment_bound X) (by
          have := TotientHarmonic.errorConstant_nonneg
          positivity))

theorem primeSum_error_polynomial : ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
    |primeSum ⌊Real.exp X⌋₊-smooth 2 X| ≤ C*(1+X)^2 := by
  obtain ⟨D,hD,h⟩ := moment_upper 2 (by norm_num)
  let E := TotientHarmonic.errorConstant
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  refine ⟨2*E*D+(6+4*E)*Zeta23.XiPrime.Cdef,fun X hX => ?_⟩
  apply (primeSum_error X hX).trans
  have h1 := mul_le_mul_of_nonneg_left (h X hX) (show 0≤2*E by positivity)
  have h2 : 6*X+4*E ≤ (6+4*E)*(1+X)^2 := by
    calc
      _ ≤ (6+4*E)*(1+X) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith : 1+X ≤ (1+X)^2) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2
    (show 0≤Zeta23.XiPrime.Cdef by norm_num [Zeta23.XiPrime.Cdef])
  dsimp only [E] at h1 h3 ⊢
  nlinarith

theorem primeSum_limit : Tendsto (fun X => primeSum ⌊Real.exp X⌋₊/X^3)
    atTop (nhds (1/6:ℝ)) := by
  obtain ⟨C,h⟩ := primeSum_error_polynomial
  have he := normalized_error_zero (fun X => primeSum ⌊Real.exp X⌋₊-smooth 2 X)
    3 (by norm_num) 0 C (by intro X hX; simpa using h X hX)
  have hm := smooth_normalized 2 (by norm_num)
  norm_num at hm
  simpa only [sub_zero,zero_add,sub_div,sub_add_cancel] using he.add hm

/-- The actual signed mixed measure has coefficient -1/6, not +7/120. -/
theorem mixed_scalar_limit : Tendsto (fun X => summatory (Real.exp X)/X^3)
    atTop (nhds (-1/6:ℝ)) := by
  simpa only [summatory_reindex,neg_div] using primeSum_limit.neg

#print axioms mobius_mark
#print axioms weight_eq
#print axioms weight_nonpos
#print axioms summatory_reindex
#print axioms primeSum_error
#print axioms primeSum_error_polynomial
#print axioms primeSum_limit
#print axioms mixed_scalar_limit
end XiPrime8845.FengMixedMoment

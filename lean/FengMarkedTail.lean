import FengMarkedDecomposition
import Zeta23.XiPrime.Coeff.PrimeSums

/-! The actual higher-prime-power diagonal is negligible on the fifth-log scale.
A cubic bound suffices; no uniform prime-by-prime asymptotic is assumed. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengMarkedTail
open TotientCoprime FengMarkedDecomposition
set_option maxHeartbeats 1000000

def primeHead (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    (Real.log p)^4 * (restricted (N/p) p / (p-1:ℝ))

def higherPowers (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, (Real.log p)^4 *
    ∑ a ∈ range (Nat.log p N-1),
      restricted (N/p^(a+2)) p / ((p^(a+2)).totient:ℝ)

theorem diagonal_split (N : ℕ) : diagonal N = primeHead N + higherPowers N := by
  rw [diagonal,primeHead,higherPowers,← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hpp := (mem_filter.mp hp).2
  have hlog : 1 ≤ Nat.log p N :=
    Nat.le_log_of_pow_le hpp.one_lt (by simpa using (mem_Icc.mp (mem_filter.mp hp).1).2)
  conv_lhs => rw [show Nat.log p N = (Nat.log p N-1)+1 by omega,sum_range_succ']
  simp only [Nat.add_assoc,show (1:ℕ)+1=2 from rfl,pow_one,zero_add,
    Nat.totient_prime hpp,Nat.cast_sub hpp.one_lt.le,Nat.cast_one,mul_add]
  exact add_comm _ _

theorem higherPowers_nonneg (N : ℕ) : 0 ≤ higherPowers N := by
  unfold higherPowers
  exact sum_nonneg fun p _ => mul_nonneg (by positivity)
    (sum_nonneg fun a _ => div_nonneg (restricted_nonneg _ _) (Nat.cast_nonneg _))

theorem totient_power_tail (p M : ℕ) (hp : p.Prime) :
    (∑ a ∈ range M, 1/((p^(a+2)).totient:ℝ)) ≤ 4/(p:ℝ)^2 := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have he : (∑ a ∈ range M, 1/((p^(a+2)).totient:ℝ)) =
      (∑ a ∈ range M, 1/((p^(a+1):ℕ):ℝ))/(p-1:ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro a ha
    rw [show a+2 = (a+1)+1 by omega,Nat.totient_prime_pow_succ hp]
    push_cast
    rw [Nat.cast_sub hp.one_lt.le]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  apply (div_le_div_of_nonneg_right (FengSharedTail.reciprocal_positive_powers p M hp)
    (by linarith)).trans
  apply (div_le_iff₀ (by linarith : (0:ℝ)<p-1)).mpr
  apply (div_le_iff₀ (by linarith : (0:ℝ)<p)).mpr
  field_simp
  nlinarith

theorem prime_fourth_square_bound (X : ℝ) (_hX : 0 ≤ X) :
    (∑ p ∈ (Icc 1 ⌊Real.exp X⌋₊).filter Nat.Prime,
      (Real.log p)^4/(p:ℝ)^2) ≤ X^2*Zeta23.XiPrime.Cdef := by
  have he : Icc 1 ⌊Real.exp X⌋₊ = Ioc 0 ⌊Real.exp X⌋₊ := by
    ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [he]
  calc
    _ ≤ X^2*∑ p ∈ (Ioc 0 ⌊Real.exp X⌋₊).filter Nat.Prime,
        (Real.log p)^2/(p:ℝ)^2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hl := Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp (mem_filter.mp hp).1
      have hl0 := Real.log_natCast_nonneg p
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2) (sq_nonneg (Real.log p))
      convert div_le_div_of_nonneg_right hh (sq_nonneg (p:ℝ)) using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Zeta23.XiPrime.sum_prime_log_sq_div_sq_le _) (sq_nonneg X)

theorem higherPowers_bound (X : ℝ) (hX : 0 ≤ X) :
    higherPowers ⌊Real.exp X⌋₊ ≤
      4*(X+TotientHarmonic.errorConstant)*X^2*Zeta23.XiPrime.Cdef := by
  have htot : total ⌊Real.exp X⌋₊ ≤ X+TotientHarmonic.errorConstant := by
    rw [total_eq]
    have h := (abs_le.mp (TotientHarmonic.summatory_log_bound (Real.exp X)
      (Real.one_le_exp_iff.mpr hX))).2
    rw [Real.log_exp] at h
    linarith
  have hC : 0 ≤ X+TotientHarmonic.errorConstant :=
    add_nonneg hX TotientHarmonic.errorConstant_nonneg
  calc
    _ ≤ ∑ p ∈ (Icc 1 ⌊Real.exp X⌋₊).filter Nat.Prime,
        (Real.log p)^4*((X+TotientHarmonic.errorConstant)*(4/(p:ℝ)^2)) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply le_trans _ (mul_le_mul_of_nonneg_left
        (totient_power_tail p (Nat.log p ⌊Real.exp X⌋₊-1) (mem_filter.mp hp).2) hC)
      rw [mul_sum]
      apply sum_le_sum
      intro a ha
      have h := (restricted_le_total (⌊Real.exp X⌋₊/p^(a+2)) p).trans
        ((total_mono (Nat.div_le_self _ _)).trans htot)
      convert div_le_div_of_nonneg_right h (Nat.cast_nonneg ((p^(a+2)).totient)) using 1
      ring
    _ = 4*(X+TotientHarmonic.errorConstant) *
        ∑ p ∈ (Icc 1 ⌊Real.exp X⌋₊).filter Nat.Prime, (Real.log p)^4/(p:ℝ)^2 := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (prime_fourth_square_bound X hX)
        (mul_nonneg (by norm_num : (0:ℝ)≤4) hC)
      simpa only [mul_assoc] using h

theorem higherPowers_normalized :
    Tendsto (fun X : ℝ => higherPowers ⌊Real.exp X⌋₊ / X^5) atTop (nhds 0) := by
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hb : Tendsto (fun X : ℝ =>
      4*Zeta23.XiPrime.Cdef*(X⁻¹^2+TotientHarmonic.errorConstant*X⁻¹^3))
      atTop (nhds 0) := by
    simpa using ((hinv.pow 2).add ((hinv.pow 3).const_mul TotientHarmonic.errorConstant)).const_mul
      (4*Zeta23.XiPrime.Cdef)
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact div_nonneg (higherPowers_nonneg _) (pow_nonneg hX.le _)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    have h := div_le_div_of_nonneg_right (higherPowers_bound X hX.le) (pow_nonneg hX.le 5)
    convert h using 1 <;> first | rfl | field_simp

#print axioms diagonal_split
#print axioms higherPowers_nonneg
#print axioms totient_power_tail
#print axioms prime_fourth_square_bound
#print axioms higherPowers_bound
#print axioms higherPowers_normalized
end XiPrime8845.FengMarkedTail


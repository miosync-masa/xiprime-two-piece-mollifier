import PRZZZeroNativeTail
import PRZZCentralMainAssembly
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Exact original strict INTEGER Delta sum, including its arithmetic
prefactor, rewritten as paired positive gaps.  No sign or boundary is
dropped.  This is an equality of actual nested integrals. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Filter Topology
namespace XiPrime8845.PRZZZeroIntegerReindex
open Finset PRZZZeroOmittedGaps PRZZDiagonalAssembly
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def deltas (B : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈B⌉) ⌈B⌉).filter (fun delta : ℤ => 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < B)

theorem integer_pair_sum (B : ℝ) (f : ℤ → ℂ) :
    (∑ delta ∈ deltas B, f delta) =
      ∑' n : ℕ, if ((n+1:ℕ):ℝ) < B then f (n+1)+f (-(n+1)) else 0 := by
  let g := fun delta : ℤ => if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < B then f delta else 0
  have hz : ∀ delta ∉ deltas B, g delta = 0 := by
    intro delta hd
    have hnot : ¬(0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < B) := by
      simpa only [deltas,PRZZAStar.delta_cutoff_iff] using hd
    exact if_neg hnot
  have hs : Summable g := summable_of_ne_finset_zero hz
  have he : (∑' delta : ℤ, g delta) = ∑ delta ∈ deltas B, f delta := by
    rw [tsum_eq_sum hz]
    apply sum_congr rfl
    intro delta hd
    exact if_pos ((PRZZAStar.delta_cutoff_iff B delta).mp hd)
  have h0 : g 0 = 0 := by simp [g]
  have hh := tsum_nat_add_neg hs
  have hn := (hs.nat_add_neg).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,neg_zero,h0,zero_add] at hn
  rw [h0,add_zero,he,← hn] at hh
  rw [← hh]
  apply tsum_congr
  intro n
  dsimp only [g]
  have hp : (0:ℝ) < (n+1:ℕ) := by positivity
  simp only [Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_natCast,Int.cast_one,
    Int.cast_neg,abs_neg,abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1),
    show 0 < (n:ℝ)+1 by positivity,true_and]
  split_ifs <;> simp

theorem cell_coefficient (a : ℕ → ℂ) (G H : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (delta : ℤ) (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    PRZZFilteredResidual.signedPrefactor a G H d alpha beta ((u,v),(delta,1)) 0 /
      ((u:ℂ)*(v:ℂ)) = coefficient a G H alpha beta d u v := by
  have huC : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [coefficient_eq a G H alpha beta d u v hd hu hv]
  unfold PRZZFilteredResidual.signedPrefactor PRZZUnfrozenPoisson.arithmetic PRZZKloostermanInputs.e
  simp only [Int.cast_zero,zero_mul,neg_zero,zero_div,Complex.ofReal_zero,
    Complex.exp_zero,mul_one,Complex.cpow_add _ _ huC,Complex.cpow_add _ _ hvC,Complex.cpow_one]
  push_cast
  ring_nf
  simp only [Complex.exp_zero,mul_one]

theorem cell_integer_sum (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) (hd : 0 < d) :
    PRZZCentralArithmeticJoin.zeroCell N d D T M a F G H Phi alpha beta =
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if admissible N d u v then coefficient a G H alpha beta d u v *
          (∑ delta ∈ deltas (D/d), value F Phi M T u v delta (alpha+beta)) else 0 := by
  have h2 : (Finset.Icc 1 ⌊(2:ℝ)⌋₊).filter (fun h : ℕ => (h:ℝ)<2) = {1} := by
    ext h
    rw [PRZZAStar.h_cutoff_iff,Finset.mem_singleton]
    constructor
    · intro hh
      have hh' : h < 2 := by exact_mod_cast hh.2
      omega
    · rintro rfl
      norm_num
  unfold PRZZCentralArithmeticJoin.zeroCell PRZZSignedCentral.signedLiteral PRZZAStar.indices
  rw [h2]
  simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_singleton,Int.zero_mul,Int.cast_zero,zero_mul]
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  by_cases had : admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro delta hdelta
    rw [cell_coefficient a G H alpha beta d u v delta hd (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hv).1]
    simp only [value,add_comm alpha beta]
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had']

theorem cell_paired_sum (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) (hd : 0 < d) :
    PRZZCentralArithmeticJoin.zeroCell N d D T M a F G H Phi alpha beta =
      ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
        if admissible N d u v then coefficient a G H alpha beta d u v *
          (∑' n : ℕ, if ((n+1:ℕ):ℝ) < D/d then
            value F Phi M T u v ((n+1:ℕ):ℝ) (alpha+beta)+
              value F Phi M T u v (-((n+1:ℕ):ℝ)) (alpha+beta) else 0) else 0 := by
  rw [cell_integer_sum N d D T M a F G H Phi alpha beta hd]
  simp_rw [integer_pair_sum]
  simp only [Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_neg,Nat.cast_add,Nat.cast_one]

#print axioms integer_pair_sum
#print axioms cell_coefficient
#print axioms cell_integer_sum
#print axioms cell_paired_sum
end XiPrime8845.PRZZZeroIntegerReindex

import PRZZSharpAggregation
import PRZZGroupedConvolution

/-! The original sharp cutoff on a grouped convolution is retained during
the exact DI reindexing. Additional factor masks may already be present in
f and g. No balanced partition or smooth product separation is inferred. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZSharpGrouped
open PRZZKloostermanInputs PRZZGroupedConvolution PRZZSharpDI
set_option maxHeartbeats 2000000

def grouped (N : ℕ) (C U : ℝ) (rho : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) : ℂ :=
  ∑ c ∈ (Icc 1 ⌊C⌋₊).filter (fun c => c.Coprime rho), ∑ a ∈ Icc 1 ⌊U⌋₊,
    ∑ n ∈ Icc 1 N,
      (if n.Coprime c then r c*nu a*e ((a:ℝ)*inverseResidue c (rho*n)/c) else 0)*(f*g) n

theorem grouped_eq (N : ℕ) (C U : ℝ) (rho : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) :
    grouped N C U rho r nu f g = sharpBlock N C N U N rho r g nu f := by
  unfold grouped
  simp_rw [weighted_convolution]
  unfold sharpBlock
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  split_ifs with hr
  · simp only [Nat.coprime_mul_iff_right]
    conv_lhs => enter [2,a]; rw [sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    by_cases hmc : m.Coprime c
    · rw [if_pos ⟨hr,hmc.symm⟩]
      simp_rw [Nat.coprime_mul_iff_left]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro n hn
      by_cases hnc : n.Coprime c <;> by_cases hcut : n*m ≤ N <;>
        simp [hnc,hmc,hcut,Nat.coprime_mul_iff_left,mul_assoc] <;> ring
      rw [if_pos ⟨hnc,hmc⟩,if_pos hnc]
    · simp [Nat.coprime_mul_iff_left,hmc,show ¬c.Coprime m from fun h => hmc h.symm]
  · simp [hr,Nat.coprime_mul_iff_right]

/-- Any verified factor-list permutation supplies the grouped coefficient.
The identity does not assert that its groups satisfy balanced size bounds. -/
theorem factor_grouped_eq (N : ℕ) (C U : ℝ) (rho : ℕ) (r nu : ℕ → ℂ)
    (fs left right : List (ArithmeticFunction ℂ)) (hp : fs.Perm (left++right)) :
    (∑ c ∈ (Icc 1 ⌊C⌋₊).filter (fun c => c.Coprime rho), ∑ a ∈ Icc 1 ⌊U⌋₊,
      ∑ n ∈ Icc 1 N,
        (if n.Coprime c then r c*nu a*e ((a:ℝ)*inverseResidue c (rho*n)/c) else 0)*fs.prod n) =
      sharpBlock N C N U N rho r right.prod nu left.prod := by
  rw [regroup_factors fs left right hp]
  exact grouped_eq N C U rho r nu left.prod right.prod

#print axioms grouped_eq
#print axioms factor_grouped_eq
end XiPrime8845.PRZZSharpGrouped

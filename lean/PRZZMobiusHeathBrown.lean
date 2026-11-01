import PRZZHeathBrown

/-! The leading mu factor also needs Heath-Brown decomposition before the
Type I/II classification ([58], arXiv:1706.04593v3, p.17). All mu factors
on the right are truncated. No Type I designation is inferred merely
from the numerical size of an arbitrary untruncated arithmetic factor. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZMobiusHeathBrown
open PRZZ PRZZHeathBrown

theorem moebius_binomial (y K n : ℕ) (hn : n < (y+1)^K) :
    muReal n = (∑ j ∈ range K,
      (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
        truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j) n := by
  have h := binomial_remainder (truncatedMu y*(ζ : ArithmeticFunction ℝ)) K
  have he : (1-remainder y^K)*muReal = ∑ j ∈ range K,
      (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
        truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j := by
    rw [remainder,h,sum_mul]
    apply sum_congr rfl
    intro j hj
    rw [mul_pow,pow_succ (ζ : ArithmeticFunction ℝ)]
    have hz : (ζ : ArithmeticFunction ℝ)*muReal = 1 := coe_zeta_mul_coe_moebius
    calc
      _ = (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
          truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*((ζ : ArithmeticFunction ℝ)*muReal) := by ring
      _ = _ := by rw [hz,mul_one]
  have hv := congrArg (fun f : ArithmeticFunction ℝ => f n) he
  rw [sub_mul,one_mul] at hv
  change muReal n-(remainder y^K*muReal) n = _ at hv
  rwa [remainder_pow_mul_vanish y K n hn,sub_zero] at hv

/-- A nonzero truncated Mobius factor cannot be a large free factor. -/
theorem truncated_factor_small (y n : ℕ) (h : truncatedMu y n ≠ 0) : n ≤ y := by
  by_contra hn
  exact h (if_neg hn)

#print axioms moebius_binomial
#print axioms truncated_factor_small
end XiPrime8845.PRZZMobiusHeathBrown

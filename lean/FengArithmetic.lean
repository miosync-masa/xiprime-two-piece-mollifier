import ElementaryGcd

/-! Exact logarithmic decomposition of the original Feng arithmetic function.
Prime powers are retained. No squarefree truncation, factorial normalization,
or arithmetic main-term asymptotic is asserted. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction
namespace XiPrime8845.FengArithmetic
open PRZZ
set_option maxHeartbeats 1000000

def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n * f n, by simp⟩

theorem logWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logWeight f n = Real.log n * f n := rfl

theorem logWeight_neg (f : ArithmeticFunction ℝ) : logWeight (-f) = -logWeight f := by
  ext n
  simp [logWeight_apply]

/-- The logarithmic weight is a derivation for Dirichlet convolution. -/
theorem logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f*g) = logWeight f * g + f * logWeight g := by
  ext n
  simp only [logWeight_apply, mul_apply, ArithmeticFunction.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have he : x.1*x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hx₁ : (x.1:ℝ) ≠ 0 := by exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
  have hx₂ : (x.2:ℝ) ≠ 0 := by exact_mod_cast Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
  rw [← he, Nat.cast_mul, Real.log_mul hx₁ hx₂]
  ring

theorem logWeight_mu_zeta : logWeight muReal * (ζ : ArithmeticFunction ℝ) = -vonMangoldt := by
  ext n
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ n.divisors, Real.log d * (μ d:ℝ)) = -vonMangoldt n
  simpa only [ArithmeticFunction.log_apply, mul_comm] using
    (sum_moebius_mul_log_eq (n := n))

theorem logWeight_mu : logWeight muReal = -(muReal * vonMangoldt) := by
  have hm : (ζ : ArithmeticFunction ℝ) * muReal = 1 := coe_zeta_mul_coe_moebius
  calc
    _ = (logWeight muReal * ζ) * muReal := by rw [mul_assoc, hm, mul_one]
    _ = -(muReal * vonMangoldt) := by rw [logWeight_mu_zeta]; ring

theorem mu_vonMangoldt : muReal * vonMangoldt = -logWeight muReal := by
  rw [logWeight_mu, neg_neg]

/-- The extra log-weighted Mangoldt convolution carries the repeated-prime terms. -/
theorem feng_log_decomposition :
    fengArithmetic = logWeight (logWeight muReal) + muReal * logWeight vonMangoldt := by
  have h := congrArg logWeight mu_vonMangoldt
  rw [logWeight_mul, logWeight_neg] at h
  nth_rw 1 [logWeight_mu] at h
  unfold fengArithmetic
  linear_combination -h

theorem feng_divisor_formula (n : ℕ) :
    fengArithmetic n = (muReal n) * (Real.log n)^2 +
      ∑ d ∈ n.divisors, (vonMangoldt d * Real.log d) * muReal (n/d) := by
  rw [feng_log_decomposition, ArithmeticFunction.add_apply, mul_comm muReal (logWeight vonMangoldt), mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m => logWeight vonMangoldt d * muReal m)]
  simp only [logWeight_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro d hd
    ring

theorem feng_prime (p : ℕ) (hp : p.Prime) : fengArithmetic p = 0 := by
  rw [feng_divisor_formula, hp.divisors]
  simp [muReal, moebius_apply_prime hp, vonMangoldt_apply_prime hp, Nat.div_self hp.pos]
  ring

/-- A regression guard: removing nonsquarefree indices would erase this term. -/
theorem feng_prime_square (p : ℕ) (hp : p.Prime) :
    fengArithmetic (p^2) = (Real.log p)^2 := by
  rw [feng_divisor_formula, Nat.sum_divisors_prime_pow hp]
  norm_num [Finset.sum_range_succ, muReal, moebius_apply_prime_pow hp,
    moebius_apply_prime hp, vonMangoldt_apply_pow, vonMangoldt_apply_prime hp,
    Nat.pow_succ, Nat.mul_div_cancel_left _ hp.pos, hp.ne_zero, Real.log_pow]
  have hm : μ (p*p) = 0 := by
    simpa [pow_two] using moebius_apply_prime_pow hp (by norm_num : (2:ℕ) ≠ 0)
  have hv : vonMangoldt (p*p) = Real.log p := by
    rw [← pow_two, vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
      vonMangoldt_apply_prime hp]
  rw [hm,hv]
  norm_num
  ring

/-- Finite weighted Feng sum split into a Mobius log-square sum and a
log-weighted prime-power convolution. The cutoff N/r is exact. -/
theorem weighted_feng_expansion (N : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (fengArithmetic n : ℂ)*w n) =
      (∑ n ∈ Finset.Icc 1 N, ((muReal n * (Real.log n)^2 : ℝ):ℂ)*w n) +
      ∑ r ∈ Finset.Icc 1 N, ((vonMangoldt r * Real.log r : ℝ):ℂ) *
        ∑ m ∈ Finset.Icc 1 (N/r), (muReal m : ℂ)*w (r*m) := by
  simp_rw [feng_divisor_formula]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  exact ElementaryGcd.weighted_divisor_reindex N
    (fun r => (vonMangoldt r : ℂ)*(Real.log r : ℂ)) (fun m => (muReal m : ℂ)) w

#print axioms logWeight_mul
#print axioms logWeight_mu_zeta
#print axioms logWeight_mu
#print axioms mu_vonMangoldt
#print axioms feng_log_decomposition
#print axioms feng_divisor_formula
#print axioms feng_prime
#print axioms feng_prime_square
#print axioms weighted_feng_expansion
end XiPrime8845.FengArithmetic

import PRZZLambda

/-! L2: the finite convolution form of Heath-Brown's identity.
Compare PRZZ arXiv:1802.10521v3, p. 20, the display preceding the dyadic
decomposition (J=0). The cutoff is an integer y; the valid range is
n < (y+1)^K, which includes n <= y^K when K >= 1.
The J>0 multinomial distribution of logarithms and real-x cutoff adapter
remain separate; no Type I/II estimate is asserted.
-/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZHeathBrown
open PRZZ
set_option maxHeartbeats 1000000

def truncatedMu (y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ y then muReal n else 0, by simp⟩

def remainder (y : ℕ) : ArithmeticFunction ℝ := 1-truncatedMu y * ζ

theorem remainder_small (y n : ℕ) (hn : n ≤ y) : remainder y n = 0 := by
  have he : (truncatedMu y * ζ) n = (muReal * ζ) n := by
    rw [coe_mul_zeta_apply, coe_mul_zeta_apply]
    apply sum_congr rfl
    intro d hd
    change (if d ≤ y then muReal d else 0) = muReal d
    exact if_pos ((Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
      (Nat.dvd_of_mem_divisors hd)).trans hn)
  change (1 : ArithmeticFunction ℝ) n - (truncatedMu y * ζ) n = 0
  rw [he, show muReal * (ζ : ArithmeticFunction ℝ) = 1 from coe_moebius_mul_coe_zeta]
  exact sub_self _

/-- A product of K factors supported on n >= M is supported on n >= M^K. -/
theorem pow_vanish_below (f : ArithmeticFunction ℝ) (M : ℕ)
    (hf : ∀ n < M, f n = 0) (K n : ℕ) (hn : n < M^K) : (f^K) n = 0 := by
  induction K generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    simp
  | succ K ih =>
    rw [pow_succ, mul_apply]
    apply sum_eq_zero
    intro d hd
    have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
    by_cases h₁ : d.1 < M^K
    · rw [ih _ h₁, zero_mul]
    · have h₂ : d.2 < M := by
        by_contra h₂
        have hh := Nat.mul_le_mul (Nat.le_of_not_gt h₁) (Nat.le_of_not_gt h₂)
        rw [he, ← pow_succ] at hh
        omega
      rw [hf _ h₂, mul_zero]

theorem remainder_pow_mul_vanish (y K n : ℕ) (hn : n < (y+1)^K)
    (f : ArithmeticFunction ℝ) : (remainder y ^ K * f) n = 0 := by
  rw [mul_apply]
  apply sum_eq_zero
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hdn : d.1 ≤ n := by
    rw [← he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd))
  rw [pow_vanish_below (remainder y) (y+1)
    (fun m hm => remainder_small y m (by omega)) K d.1 (hdn.trans_lt hn), zero_mul]

/-- Algebraic identity with its exact remainder, before any cutoff restriction. -/
theorem heathBrown_remainder (y K : ℕ) :
    vonMangoldt - remainder y ^ K * vonMangoldt =
      (∑ j ∈ range K, remainder y ^ j) * truncatedMu y * ArithmeticFunction.log := by
  have hz : (ζ : ArithmeticFunction ℝ) * vonMangoldt = ArithmeticFunction.log :=
    zeta_mul_vonMangoldt
  have hs : (∑ j ∈ range K, remainder y ^ j) * (1-remainder y) = 1-remainder y ^ K := by
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ, add_mul, ih, pow_succ]; ring
  calc
    _ = (1-remainder y ^ K)*vonMangoldt := by ring
    _ = ((∑ j ∈ range K, remainder y ^ j)*(1-remainder y))*vonMangoldt := by rw [hs]
    _ = _ := by
      rw [remainder]
      simp only [sub_sub_cancel]
      rw [mul_assoc, mul_assoc, hz, ← mul_assoc]

/-- Finite Heath-Brown identity in geometric convolution form; all cutoffs
and the discarded remainder are proved, not assumed. -/
theorem heathBrown (y K n : ℕ) (hn : n < (y+1)^K) :
    vonMangoldt n = ((∑ j ∈ range K, remainder y ^ j) * truncatedMu y *
      ArithmeticFunction.log) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (heathBrown_remainder y K)
  change vonMangoldt n - (remainder y^K*vonMangoldt) n = _ at h
  rwa [remainder_pow_mul_vanish y K n hn, sub_zero] at h

/-- Binomial form, indexed by j+1 to avoid truncated subtraction in powers. -/
theorem binomial_remainder {R : Type*} [CommRing R] (x : R) (K : ℕ) :
    1-(1-x)^K = ∑ j ∈ range K, (-1:R)^j*x^(j+1)*(K.choose (j+1):R) := by
  have h := add_pow (-x) (1:R) K
  rw [sum_range_succ'] at h
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at h
  have he : (∑ j ∈ range K, (-x)^(j+1)*(K.choose (j+1):R)) =
      -(∑ j ∈ range K, (-1:R)^j*x^(j+1)*(K.choose (j+1):R)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    rw [neg_pow, pow_succ (-1:R)]
    ring
  rw [he] at h
  rw [show 1-x = -x+1 by ring, h]
  ring

/-- The exact finite binomial convolution identity in PRZZ p. 20 (J=0).
The coefficient (-1)^j * choose K (j+1) is a scalar arithmetic function,
so multiplication here remains Dirichlet convolution throughout. -/
theorem heathBrown_binomial (y K n : ℕ) (hn : n < (y+1)^K) :
    vonMangoldt n = (∑ j ∈ range K,
      (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
        truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*ArithmeticFunction.log) n := by
  have h := binomial_remainder (truncatedMu y*(ζ : ArithmeticFunction ℝ)) K
  have he : (1-remainder y^K)*vonMangoldt = ∑ j ∈ range K,
      (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
        truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*ArithmeticFunction.log := by
    rw [remainder, h, sum_mul]
    apply sum_congr rfl
    intro j hj
    rw [mul_pow, pow_succ (ζ : ArithmeticFunction ℝ)]
    calc
      _ = (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
          truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*((ζ : ArithmeticFunction ℝ)*vonMangoldt) := by ring
      _ = _ := by rw [zeta_mul_vonMangoldt]
  have hv := congrArg (fun f : ArithmeticFunction ℝ => f n) he
  rw [sub_mul, one_mul] at hv
  change vonMangoldt n - (remainder y^K*vonMangoldt) n = _ at hv
  rwa [remainder_pow_mul_vanish y K n hn, sub_zero] at hv

#print axioms remainder_small
#print axioms pow_vanish_below
#print axioms heathBrown_remainder
#print axioms heathBrown
#print axioms heathBrown_binomial
end XiPrime8845.PRZZHeathBrown

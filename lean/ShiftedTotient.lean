import TotientWeight

/-! Exact shifted outer Euler weights. No limit of the gcd sum is asserted. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset Complex
namespace XiPrime8845.ShiftedTotient
open ElementaryGcd

def powerAF (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n:ℂ)^s, by simp⟩

theorem powerAF_multiplicative (s : ℂ) : (powerAF s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [powerAF], ?_⟩
  intro m n hm hn hmn
  simp only [powerAF, coe_mk, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn), Nat.cast_mul]
  exact Complex.natCast_mul_natCast_cpow m n s

def phiAF (s : ℂ) : ArithmeticFunction ℂ := (μ : ArithmeticFunction ℂ) * powerAF s

theorem phiAF_eq (s : ℂ) (n : ℕ) : phiAF s n = generalizedTotient s n := by
  rw [phiAF, mul_apply, generalizedTotient]
  apply sum_congr rfl
  intro d hd
  simp [powerAF, Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd]

theorem phiAF_multiplicative (s : ℂ) : (phiAF s).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (powerAF_multiplicative s)

theorem phiAF_prime (s : ℂ) (p : ℕ) (hp : p.Prime) : phiAF s p = (p:ℂ)^s-1 := by
  rw [phiAF, mul_apply]
  simp only [intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℂ)*powerAF s b),
    hp.divisors]
  rw [sum_insert (by simpa using hp.ne_one.symm), sum_singleton]
  simp [hp.ne_zero, powerAF, moebius_apply_prime hp]
  ring

theorem generalizedTotient_squarefree (s : ℂ) (g : ℕ) (hg : Squarefree g) :
    generalizedTotient s g = ∏ p ∈ g.primeFactors, ((p:ℂ)^s-1) := by
  rw [← phiAF_eq, ← (phiAF_multiplicative s).prod_primeFactors hg]
  exact prod_congr rfl (fun p hp => phiAF_prime s p (Nat.prime_of_mem_primeFactors hp))

theorem generalizedTotient_one (g : ℕ) : generalizedTotient 1 g = (g.totient:ℂ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (n.totient:ℂ)) (g := fun n => (n:ℂ))).mp (by
      intro n hn
      exact_mod_cast Nat.sum_totient n)
  by_cases hg : g = 0
  · subst g; simp [generalizedTotient]
  simpa only [generalizedTotient, cpow_one] using h g (Nat.pos_of_ne_zero hg)

def euler (a : ℂ) (g : ℕ) : ℂ :=
  ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-(1+a)))⁻¹

def outerWeight (a b : ℂ) (g : ℕ) : ℂ :=
  (μ g:ℂ)^2 * generalizedTotient (1+a+b) g / (g:ℂ)^(2+a+b) * euler a g * euler b g

theorem euler_zero (g : ℕ) : euler 0 g = (SupportTail.eulerMass g 0:ℂ) := by
  simp only [euler, add_zero, neg_add_rev, neg_zero, zero_add,
    Complex.cpow_neg_one, SupportTail.eulerMass, sub_zero, zero_sub, Real.rpow_neg_one]
  push_cast
  rfl

theorem outerWeight_zero (g : ℕ) (hg : g ≠ 0) :
    outerWeight 0 0 g = ((μ g:ℝ)^2/(g.totient:ℝ):ℝ) := by
  unfold outerWeight
  simp only [add_zero, generalizedTotient_one, euler_zero, cpow_ofNat]
  exact_mod_cast TotientWeight.zero_shift_weight g hg

theorem cpow_squarefree (s : ℂ) (g : ℕ) (hg : Squarefree g) :
    (g:ℂ)^s = ∏ p ∈ g.primeFactors, (p:ℂ)^s := by
  have h := (powerAF_multiplicative s).prod_primeFactors hg
  simp only [powerAF, coe_mk, if_neg hg.ne_zero] at h
  rw [← h]
  apply prod_congr rfl
  intro p hp
  rw [if_neg (Nat.pos_of_mem_primeFactors hp).ne']

def localFactor (a b : ℂ) (p : ℕ) : ℂ :=
  (1-(p:ℂ)^(-(1+a+b))) / ((1-(p:ℂ)^(-(1+a)))*(1-(p:ℂ)^(-(1+b))))

theorem local_power_identity (s : ℂ) (p : ℕ) (hp : p ≠ 0) :
    ((p:ℂ)^s-1)/(p:ℂ)^(1+s) = (1-(p:ℂ)^(-s))/(p:ℂ) := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp
  have hs0 : (p:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  rw [cpow_add _ _ hp0, cpow_one, cpow_neg]
  field_simp

/-- Literal outer weight after inserting the two full coprimality Euler
factors. This is an exact finite product, not its averaged asymptotic. -/
theorem outerWeight_product (a b : ℂ) (g : ℕ) :
    outerWeight a b g = (μ g:ℂ)^2/(g:ℂ) *
      ∏ p ∈ g.primeFactors, localFactor a b p := by
  by_cases hg : Squarefree g
  · unfold outerWeight
    rw [generalizedTotient_squarefree _ g hg, cpow_squarefree _ g hg]
    have he : (2:ℂ)+a+b = 1+(1+a+b) := by ring
    rw [he]
    simp only [mul_div_assoc]
    rw [← Finset.prod_div_distrib]
    have ht : (∏ p ∈ g.primeFactors, ((p:ℂ)^(1+a+b)-1)/(p:ℂ)^(1+(1+a+b))) =
        ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-(1+a+b)))/(p:ℂ) := by
      apply prod_congr rfl
      intro p hp
      exact local_power_identity _ p (Nat.pos_of_mem_primeFactors hp).ne'
    rw [ht]
    simp only [euler, ← Finset.prod_mul_distrib, mul_assoc]
    have hgprod : (∏ p ∈ g.primeFactors, (p:ℂ)) = (g:ℂ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hg]
    simp only [localFactor, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv_rev]
    rw [hgprod]
    ring
  · simp [outerWeight, moebius_eq_zero_of_not_squarefree hg]

/-- The first-order shift terms cancel locally. The defect contains BOTH
shift increments; this identity alone is not a uniform averaged estimate. -/
theorem local_ratio_defect (z x y : ℂ) (hx : 1-z*x ≠ 0) (hy : 1-z*y ≠ 0) :
    (1-z)*(1-z*x*y)/((1-z*x)*(1-z*y))-1 =
      -z*(1-x)*(1-y)/((1-z*x)*(1-z*y)) := by
  field_simp
  ring

#print axioms generalizedTotient_squarefree
#print axioms generalizedTotient_one
#print axioms outerWeight_zero
#print axioms outerWeight_product
#print axioms local_ratio_defect
end XiPrime8845.ShiftedTotient

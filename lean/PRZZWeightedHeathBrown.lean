import PRZZHeathBrown

/-! Logarithmic weights in the finite Heath-Brown identity (PRZZ v3 p.20).
`expand` is the multinomial expansion encoded as successive binomial splits;
`allocationCoeff_sum` identifies its coefficients with List.multinomial.
No dyadic decomposition or exponential-sum estimate is assumed here. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZWeightedHeathBrown
open PRZZ PRZZHeathBrown
set_option maxHeartbeats 1000000

def weight (J : ℕ) : ArithmeticFunction ℝ →ₗ[ℝ] ArithmeticFunction ℝ where
  toFun f := ⟨fun n => Real.log n ^ J * f n, by simp⟩
  map_add' f g := by
    ext n
    change Real.log n ^ J * (f n+g n) = Real.log n ^ J * f n + Real.log n ^ J * g n
    ring
  map_smul' c f := by ext n; change _ * (c*f n) = c*(_*f n); ring

@[simp] theorem weight_apply (J : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    weight J f n = Real.log n ^ J * f n := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [sum_insert hi, ih]

theorem weight_one (J : ℕ) : weight J (1 : ArithmeticFunction ℝ) = if J=0 then 1 else 0 := by
  ext n
  cases J <;> by_cases hn : n=1 <;> simp [weight_apply,one_apply,hn]

/-- Exact Leibniz/binomial split for Dirichlet convolution. -/
theorem weight_mul (J : ℕ) (f g : ArithmeticFunction ℝ) :
    weight J (f*g) = ∑ k ∈ range (J+1), (J.choose k:ℝ) • (weight k f * weight (J-k) g) := by
  ext n
  simp only [weight_apply,mul_apply,sum_apply,smul_map,smul_eq_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have h₁ : (d.1:ℝ) ≠ 0 := by exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd
  have h₂ : (d.2:ℝ) ≠ 0 := by exact_mod_cast Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd
  rw [← he,Nat.cast_mul,Real.log_mul h₁ h₂,add_pow,sum_mul]
  apply sum_congr rfl
  intro k hk
  ring

/-- Successive binomial splits, with all coefficient functions still separate. -/
def expand (J : ℕ) : List (ArithmeticFunction ℝ) → ArithmeticFunction ℝ
  | [] => if J=0 then 1 else 0
  | f::fs => ∑ k ∈ range (J+1), (J.choose k:ℝ) • (weight k f * expand (J-k) fs)

theorem expand_eq_weight (fs : List (ArithmeticFunction ℝ)) (J : ℕ) :
    expand J fs = weight J fs.prod := by
  induction fs generalizing J with
  | nil => exact (weight_one J).symm
  | cons f fs ih => simp only [expand,List.prod_cons,weight_mul,ih]

/-- The coefficient along one branch of the successive binomial expansion. -/
def allocationCoeff : ℕ → List ℕ → ℕ
  | J, [] => if J=0 then 1 else 0
  | J, k::ks => J.choose k * allocationCoeff (J-k) ks

theorem allocationCoeff_sum (ks : List ℕ) :
    allocationCoeff ks.sum ks = ks.multinomial := by
  induction ks with
  | nil => simp [allocationCoeff,List.multinomial,Finsupp.multinomial]
  | cons k ks ih => simp [allocationCoeff,List.multinomial_cons,ih]

/-- Literal multinomial distribution on any nonzero factor tuple. -/
theorem log_product_multinomial {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : ∀ i, m i ≠ 0) (J : ℕ) :
    Real.log (∏ i, m i : ℕ)^J =
      ∑ k ∈ piAntidiag (univ : Finset ι) J,
        (Nat.multinomial univ k:ℝ)*∏ i, Real.log (m i)^k i := by
  classical
  rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast hm i)]
  exact sum_pow_eq_sum_piAntidiag _ _ _

/-- j+1 short Mobius factors, j unrestricted zeta factors, one final log.
There are exactly 2*(j+1) factors, as in the source's j=1,...,K indexing. -/
def factors (y j : ℕ) : List (ArithmeticFunction ℝ) :=
  List.replicate (j+1) (truncatedMu y) ++ List.replicate j (ζ : ArithmeticFunction ℝ) ++
    [ArithmeticFunction.log]

theorem factors_length (y j : ℕ) : (factors y j).length = 2*(j+1) := by simp [factors]; omega

theorem factors_prod (y j : ℕ) :
    (factors y j).prod = truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*ArithmeticFunction.log := by
  simp [factors,mul_assoc]

theorem scalar_coefficient (j K : ℕ) (f : ArithmeticFunction ℝ) :
    (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*f =
      ((-1:ℝ)^j*(K.choose (j+1):ℝ)) • f := by
  rw [Algebra.smul_def]
  simp

/-- Arbitrary J, retaining the original short-factor cutoffs. No asymptotic
replacement is made. The expansion is a finite sum of separate log-weighted
factors, not just log(n)^J multiplied onto an unexpanded identity. -/
theorem heathBrown_weighted (J y K n : ℕ) (hn : n < (y+1)^K) :
    Real.log n ^ J * vonMangoldt n =
      (∑ j ∈ range K, ((-1:ℝ)^j*(K.choose (j+1):ℝ)) • expand J (factors y j)) n := by
  have hh := heathBrown_binomial y K n hn
  have he : (∑ j ∈ range K,
      (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
        truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j*ArithmeticFunction.log) =
      ∑ j ∈ range K, ((-1:ℝ)^j*(K.choose (j+1):ℝ)) • (factors y j).prod := by
    apply sum_congr rfl
    intro j hj
    rw [factors_prod,← scalar_coefficient]
    ring
  rw [he] at hh
  rw [hh]
  change weight J (∑ j ∈ range K, ((-1:ℝ)^j*(K.choose (j+1):ℝ)) • (factors y j).prod) n = _
  simp only [map_sum,map_smul,expand_eq_weight]

/-- The source's real cutoff x^(1/K), with n <= x (including the endpoint). -/
theorem root_cutoff_range (x : ℝ) (hx : 0 ≤ x) (K : ℕ) (hK : 0 < K)
    (n : ℕ) (hn : (n:ℝ) ≤ x) : n < (⌊Real.rpow x (K:ℝ)⁻¹⌋₊+1)^K := by
  have hr : 0 ≤ Real.rpow x (K:ℝ)⁻¹ := Real.rpow_nonneg hx _
  have hf := Nat.lt_floor_add_one (Real.rpow x (K:ℝ)⁻¹)
  have hp := pow_lt_pow_left₀ hf hr hK.ne'
  change (x ^ ((K:ℝ)⁻¹))^K < (⌊Real.rpow x (K:ℝ)⁻¹⌋₊+1:ℝ)^K at hp
  rw [Real.rpow_inv_natCast_pow hx hK.ne'] at hp
  exact_mod_cast hn.trans_lt hp

theorem heathBrown_weighted_real (J K n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hK : 0 < K) (hn : (n:ℝ) ≤ x) :
    Real.log n ^ J * vonMangoldt n =
      (∑ j ∈ range K, ((-1:ℝ)^j*(K.choose (j+1):ℝ)) •
        expand J (factors ⌊Real.rpow x (K:ℝ)⁻¹⌋₊ j)) n :=
  heathBrown_weighted J _ K n (root_cutoff_range x hx K hK n hn)

#print axioms weight_mul
#print axioms expand_eq_weight
#print axioms allocationCoeff_sum
#print axioms log_product_multinomial
#print axioms heathBrown_weighted
#print axioms root_cutoff_range
#print axioms heathBrown_weighted_real
end XiPrime8845.PRZZWeightedHeathBrown

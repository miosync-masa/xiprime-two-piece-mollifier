import TotientConvolution
import MultiplicativeSummability

/-! Absolute convergence with a positive power margin for the correction. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset
namespace XiPrime8845.TotientSummability
open TotientConvolution

def localMass (n : ℕ) : ℝ :=
  ((n:ℝ)^(1/4:ℝ)+(n:ℝ)^(1/2:ℝ))/((n:ℝ)*(n-1))

theorem localMass_nonneg (n : ℕ) : 0 ≤ localMass n := by
  by_cases hn : n = 0
  · simp [localMass, hn]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  unfold localMass
  positivity

theorem localMass_bound (n : ℕ) : localMass n ≤ 4*(n:ℝ)^(-3/2:ℝ) := by
  rcases n with _ | _ | n
  · norm_num [localMass]
  · norm_num [localMass]
  have hx : (2:ℝ) ≤ n+2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : (0:ℝ) < n+2 := by positivity
  have ha : (n+2:ℝ)^(1/4:ℝ) ≤ (n+2:ℝ)^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have he : 4*(n+2:ℝ)^(-3/2:ℝ) = 4*(n+2:ℝ)^(1/2:ℝ)/(n+2)^2 := by
    rw [show (-3/2:ℝ)=1/2-2 by norm_num, Real.rpow_sub hx0,
      Real.rpow_two]
    ring
  simp only [localMass, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two, Nat.cast_ofNat]
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hx0 (by linarith)) (sq_pos_of_pos hx0)).mpr
  have hp := Real.rpow_pos_of_pos hx0 (1/2:ℝ)
  nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) hp.le,
    mul_le_mul_of_nonneg_right ha (sq_nonneg (n+2:ℝ))]

theorem localMass_summable : Summable localMass :=
  Summable.of_nonneg_of_le localMass_nonneg localMass_bound
    ((Real.summable_nat_rpow.mpr (by norm_num : (-3/2:ℝ)< -1)).mul_left 4)

def powerMass (n : ℕ) : ℝ := |correction n| * (n:ℝ)^(1/4:ℝ)

theorem powerMass_nonneg (n : ℕ) : 0 ≤ powerMass n := by
  unfold powerMass; positivity

theorem powerMass_local (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => powerMass (p^k)) (1+localMass p) := by
  have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℕ) (s := Finset.range 3)
    (f := fun k : ℕ => powerMass (p^k)) (by
      intro k hk
      have hk3 : 3 ≤ k := by simpa using hk
      simp [powerMass, correction_prime_pow p k hp, show k ≠ 0 by omega,
        show k ≠ 1 by omega, show k ≠ 2 by omega])
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (0:ℝ) < p-1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    powerMass, correction_prime_pow p _ hp]
  norm_num [abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hp1,
    localMass, ← Real.rpow_natCast_mul hp0.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem powerMass_summable : Summable powerMass := by
  apply MultiplicativeSummability.summable_of_local_mass powerMass
    (by simp [powerMass]) (by simp [powerMass, correction_multiplicative.map_one])
    ?_ powerMass_nonneg localMass localMass_nonneg localMass_summable powerMass_local
  intro m n hmn
  simp only [powerMass, correction_multiplicative.map_mul_of_coprime hmn,
    abs_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem correction_abs_summable : Summable (fun n => |correction n|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ powerMass_summable
  intro n
  by_cases hn : n = 0
  · simp [hn, powerMass]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1/4)
  simpa only [mul_one, powerMass] using mul_le_mul_of_nonneg_left h (abs_nonneg (correction n))

theorem correction_local (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => correction (p^k)) 1 := by
  have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℕ) (s := Finset.range 3)
    (f := fun k : ℕ => correction (p^k)) (by
      intro k hk
      have hk3 : 3 ≤ k := by simpa using hk
      simp [correction_prime_pow p k hp, show k ≠ 0 by omega,
        show k ≠ 1 by omega, show k ≠ 2 by omega])
  convert h using 1
  norm_num [Finset.sum_range_succ, correction_prime_pow p _ hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem correction_mass_one : (∑' n, correction n) = 1 := by
  have hs : Summable (fun n => ‖correction n‖) := correction_abs_summable
  have h := correction_multiplicative.eulerProduct_tprod hs
  have he (p : Nat.Primes) : (∑' k : ℕ, correction ((p:ℕ)^k)) = 1 :=
    (correction_local p p.prop).tsum_eq
  simpa only [he, tprod_one] using h.symm

#print axioms powerMass_summable
#print axioms correction_mass_one

end XiPrime8845.TotientSummability

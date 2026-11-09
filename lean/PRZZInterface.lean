import Mathlib

/-! Definitions and elementary witness algebra only. No external analytic
axiom is declared here. The proved Weil/DI input lives in PRZZProvedInput. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Filter
namespace XiPrime8845.PRZZ

structure Profiles where
  conrey : Polynomial ℝ
  feng : Polynomial ℝ

def muReal : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ), by simp⟩

def fengArithmetic : ArithmeticFunction ℝ :=
  muReal * ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt

def length (theta T : ℝ) : ℝ := Real.rpow T theta
def cutoff (theta T : ℝ) : ℕ := ⌊length theta T⌋₊

def coefficient (P : Profiles) (theta T : ℝ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ (n : ℝ) ≤ length theta T then
    let u := Real.log (length theta T / n) / Real.log (length theta T)
    ((muReal n * P.conrey.eval u + fengArithmetic n * P.feng.eval u /
      (Real.log (length theta T))^2 : ℝ) : ℂ)
  else 0

/-- Uniform in T. The fixed witness instance is proved below. -/
def Subpower (a : ℝ → ℕ → ℂ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ n : ℕ, 1 ≤ n → ‖a T n‖ ≤ C * Real.rpow n eps

def dirichletPolynomial (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ)^s

def twistedMoment (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  ∫ t : ℝ,
    riemannZeta (1/2 + A/(Real.log T : ℂ) + t*I) *
    riemannZeta (1/2 + B/(Real.log T : ℂ) - t*I) *
    dirichletPolynomial (coefficient P theta T) (cutoff theta T) (1/2 + t*I) *
    star (dirichletPolynomial (coefficient Q theta T) (cutoff theta T) (1/2 + t*I)) *
    (Phi (t/T) : ℂ)

/-- Literal double-sum main term, only asserted away from A+B=0.
At A+B=0 the bracket formally becomes `2 * riemannZeta 1`, not the
removable holomorphic extension; this formula is used analytically only
for A+B ≠ 0. The two pole terms must be regularized together. -/
def gcdMainTerm (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  let alpha := A/(Real.log T : ℂ)
  let beta := B/(Real.log T : ℂ)
  ∑ d ∈ Finset.Icc 1 (cutoff theta T), ∑ e ∈ Finset.Icc 1 (cutoff theta T),
    coefficient P theta T d * star (coefficient Q theta T e) / (Nat.lcm d e : ℂ) *
    (Nat.gcd d e : ℂ)^(alpha+beta) / ((d : ℂ)^alpha * (e : ℂ)^beta) *
    ∫ t : ℝ, (riemannZeta (1+alpha+beta) + riemannZeta (1-alpha-beta) *
      ((2*Real.pi*d*e/(t*(Nat.gcd d e)^2) : ℝ) : ℂ)^(alpha+beta)) * (Phi (t/T) : ℂ)

/-- A fixed C-infinity weight, not a real-analytic weight. The explicit
`ℕ∞` annotation matters: an untyped `⊤` has order omega in `ℕ∞ω`.
Constants in the external estimate may depend on this fixed weight. -/
def SmoothWeight (Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Phi ∧ Function.support Phi ⊆ Set.Icc 1 2

def witness : Profiles where
  conrey := Polynomial.C (-0.30528514) * Polynomial.X + Polynomial.C 2.50038954 * Polynomial.X^2 -
    Polynomial.C 1.12177152 * Polynomial.X^3 - Polynomial.C 0.07333288 * Polynomial.X^4
  feng := Polynomial.C 1.89779072 * Polynomial.X + Polynomial.C 0.56594804 * Polynomial.X^2 +
    Polynomial.C 0.07023055 * Polynomial.X^3

theorem witness_endpoints : witness.conrey.eval 0 = 0 ∧ witness.feng.eval 0 = 0 ∧
    witness.conrey.eval 1 = 1 := by
  norm_num [witness]

theorem witness_length : (0 : ℝ) < 4/7-1/1000000 ∧ (4/7-1/1000000 : ℝ) < 4/7 := by
  norm_num

theorem coefficient_support (P : Profiles) (theta T : ℝ) (n : ℕ)
    (hn : ¬(1 ≤ n ∧ (n : ℝ) ≤ length theta T)) : coefficient P theta T n = 0 := by
  simp [coefficient, hn]

theorem abs_muReal_le_one (n : ℕ) : |muReal n| ≤ 1 := by
  change |(ArithmeticFunction.moebius n : ℝ)| ≤ 1
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem abs_mu_vonMangoldt_le_log (n : ℕ) :
    |(muReal * ArithmeticFunction.vonMangoldt) n| ≤ Real.log n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun x y => muReal x * ArithmeticFunction.vonMangoldt y)]
  calc
    _ ≤ ∑ d ∈ n.divisors, |muReal (n / d) * ArithmeticFunction.vonMangoldt d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (abs_muReal_le_one _)
    _ = Real.log n := ArithmeticFunction.vonMangoldt_sum

theorem abs_fengArithmetic_le_log_sq (n : ℕ) (hn : 1 ≤ n) :
    |fengArithmetic n| ≤ (Real.log n)^2 := by
  rw [fengArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun x y =>
      (muReal * ArithmeticFunction.vonMangoldt) x * ArithmeticFunction.vonMangoldt y)]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        |(muReal * ArithmeticFunction.vonMangoldt) (n / d) * ArithmeticFunction.vonMangoldt d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, Real.log n * ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
      apply (abs_mu_vonMangoldt_le_log _).trans
      apply Real.log_le_log
      · exact_mod_cast Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd))
          (Nat.pos_of_mem_divisors hd)
      · exact_mod_cast Nat.div_le_self n d
    _ = (Real.log n)^2 := by
      rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum, pow_two]

theorem witness_profile_bounds (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |witness.conrey.eval u| ≤ 4.00077908 ∧ |witness.feng.eval u| ≤ 2.53396931 := by
  have hp (k : ℕ) : |u^k| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 hu1
  have term (c : ℝ) (k : ℕ) : |c * u^k| ≤ |c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hp k)
  have t1 := term (-0.30528514) 1
  have t2 := term 2.50038954 2
  have t3 := term 1.12177152 3
  have t4 := term 0.07333288 4
  have t5 := term 1.89779072 1
  have t6 := term 0.56594804 2
  have t7 := term 0.07023055 3
  simp only [pow_one] at t1 t5
  constructor
  · simp only [witness, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc
      _ ≤ |(-0.30528514 : ℝ)*u| + |2.50038954*u^2| + |1.12177152*u^3| +
          |0.07333288*u^4| := by
        exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ |(-0.30528514 : ℝ)| + |(2.50038954 : ℝ)| + |(1.12177152 : ℝ)| +
          |(0.07333288 : ℝ)| := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
      _ = _ := by norm_num
  · simp only [witness, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc
      _ ≤ |(1.89779072 : ℝ)*u| + |0.56594804*u^2| + |0.07023055*u^3| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |(1.89779072 : ℝ)| + |(0.56594804 : ℝ)| + |(0.07023055 : ℝ)| :=
        add_le_add (add_le_add t5 t6) t7
      _ = _ := by norm_num

theorem witness_coefficient_bound (theta T : ℝ) (htheta : 0 < theta) (hT : 2 ≤ T)
    (n : ℕ) : ‖coefficient witness theta T n‖ ≤ 6.53474839 := by
  by_cases hs : 1 ≤ n ∧ (n : ℝ) ≤ length theta T
  · have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hs.1
    have hy : 1 < length theta T := Real.one_lt_rpow (by linarith) htheta
    have hlog : 0 < Real.log (length theta T) := Real.log_pos hy
    have hu0 : 0 ≤ Real.log (length theta T / n) / Real.log (length theta T) :=
      div_nonneg (Real.log_nonneg ((one_le_div hn).mpr hs.2)) hlog.le
    have hu1 : Real.log (length theta T / n) / Real.log (length theta T) ≤ 1 := by
      apply (div_le_one hlog).mpr
      apply Real.log_le_log (div_pos (by linarith) hn)
      exact div_le_self (by linarith) hn1
    obtain ⟨hP, hF⟩ := witness_profile_bounds _ hu0 hu1
    have hln0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hln : Real.log (n : ℝ) ≤ Real.log (length theta T) := Real.log_le_log hn hs.2
    have har : |fengArithmetic n| / (Real.log (length theta T))^2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos hlog)).mpr
      exact (abs_fengArithmetic_le_log_sq n hs.1).trans (by nlinarith)
    simp only [coefficient, if_pos hs, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |muReal n| * |witness.conrey.eval _| +
          (|fengArithmetic n| / (Real.log (length theta T))^2) * |witness.feng.eval _| := by
        have h := abs_add_le (muReal n * witness.conrey.eval
          (Real.log (length theta T / n) / Real.log (length theta T)))
          (fengArithmetic n * witness.feng.eval
          (Real.log (length theta T / n) / Real.log (length theta T)) /
          (Real.log (length theta T))^2)
        simpa only [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (Real.log (length theta T))),
          div_mul_eq_mul_div] using h
      _ ≤ 1 * 4.00077908 + 1 * 2.53396931 := by
        exact add_le_add
          (mul_le_mul (abs_muReal_le_one n) hP (abs_nonneg _) (by norm_num))
          (mul_le_mul har hF (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  · norm_num [coefficient, hs]

theorem witness_subpower (theta : ℝ) (htheta : 0 < theta) :
    Subpower (coefficient witness theta) := by
  intro eps heps
  refine ⟨6.53474839, by norm_num, ?_⟩
  intro T hT n hn
  apply (witness_coefficient_bound theta T htheta hT n).trans
  exact le_mul_of_one_le_right (by norm_num) (Real.one_le_rpow (by exact_mod_cast hn) heps.le)

/-- Correct orientation for the stated density: d carries beta and e alpha.
The bracket in gcdMainTerm is symmetric in the shifts, so this definition
changes their arithmetic placement only. No analytic estimate is asserted. -/
def densityGcdMainTerm (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) : ℂ :=
  gcdMainTerm P Q theta T Phi B A

theorem coefficient_star (P : Profiles) (theta T : ℝ) (n : ℕ) :
    star (coefficient P theta T n) = coefficient P theta T n := by
  unfold coefficient
  split_ifs <;> simp

/-- Exact finite-sum symmetry, independent of the analytic input. -/
theorem gcdMainTerm_swap (P Q : Profiles) (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) :
    gcdMainTerm P Q theta T Phi A B = gcdMainTerm Q P theta T Phi B A := by
  unfold gcdMainTerm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d hd
  apply Finset.sum_congr rfl; intro e he
  rw [coefficient_star,coefficient_star]
  simp only [Nat.lcm_comm e d,Nat.gcd_comm e d]
  have hs : B/(Real.log T:ℂ)+A/(Real.log T:ℂ) =
      A/(Real.log T:ℂ)+B/(Real.log T:ℂ) := by ring
  have hp : (1:ℂ)+B/(Real.log T:ℂ)+A/(Real.log T:ℂ) =
      1+A/(Real.log T:ℂ)+B/(Real.log T:ℂ) := by ring
  have hm : (1:ℂ)-B/(Real.log T:ℂ)-A/(Real.log T:ℂ) =
      1-A/(Real.log T:ℂ)-B/(Real.log T:ℂ) := by ring
  have hx : ∀ t : ℝ, 2*Real.pi*(e:ℝ)*d/(t*(Nat.gcd d e)^2) =
      2*Real.pi*(d:ℝ)*e/(t*(Nat.gcd d e)^2) := by intro t; ring
  simp_rw [hs,hp,hm,hx]
  ring

theorem witness_densityGcdMainTerm_eq (theta T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) :
    densityGcdMainTerm witness witness theta T Phi A B =
      gcdMainTerm witness witness theta T Phi A B :=
  gcdMainTerm_swap witness witness theta T Phi B A

/-- The literal PRZZ error envelope, normalized by T. -/
theorem normalized_error_tendsto_zero (theta eps : ℝ)
    (h1 : eps + theta * (7/4) < 1)
    (h2 : eps + theta * (7/8) + 1/2 < 1) :
    Tendsto (fun T : ℝ => Real.rpow T eps *
      (Real.rpow (length theta T) (7/4) +
       Real.rpow (length theta T) (7/8) * Real.rpow T (1/2)) / T)
      atTop (nhds 0) := by
  have hlim (a : ℝ) (ha : a < 1) :
      Tendsto (fun T : ℝ => Real.rpow T (a-1)) atTop (nhds 0) := by
    change Tendsto (fun T : ℝ => T ^ (a-1)) atTop (nhds 0)
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (show 0 < 1-a by linarith)
  have h := (hlim _ h1).add (hlim _ h2)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  change T ^ (eps + theta * (7/4) - 1) + T ^ (eps + theta * (7/8) + 1/2 - 1) =
    T ^ eps * ((T ^ theta) ^ (7/4 : ℝ) + (T ^ theta) ^ (7/8 : ℝ) * T ^ (1/2 : ℝ)) / T
  simp only [Real.rpow_sub hT, Real.rpow_one,
    Real.rpow_add hT, Real.rpow_mul hT.le]
  ring

theorem witness_normalized_error_tendsto_zero :
    Tendsto (fun T : ℝ => Real.rpow T (7/16000000) *
      (Real.rpow (length (4/7-1/1000000) T) (7/4) +
       Real.rpow (length (4/7-1/1000000) T) (7/8) * Real.rpow T (1/2)) / T)
      atTop (nhds 0) :=
  normalized_error_tendsto_zero _ _ (by norm_num) (by norm_num)

#print axioms witness_normalized_error_tendsto_zero
#print axioms witness_coefficient_bound
#print axioms witness_subpower
#print axioms witness_profile_bounds
#print axioms abs_fengArithmetic_le_log_sq
#print axioms witness_endpoints
#print axioms coefficient_star
#print axioms gcdMainTerm_swap
#print axioms witness_densityGcdMainTerm_eq
end XiPrime8845.PRZZ

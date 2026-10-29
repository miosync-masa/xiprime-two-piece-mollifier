import FengArithmetic
import CoprimeShift

/-! Exact shifted Feng decomposition. The logarithmic Mobius part is a second
shift derivative; the remaining prime-power convolution is not discarded or
assigned an asymptotic. No differentiation of the profile or cutoff occurs. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.FengShift
open ShiftWeights CoprimeShift
set_option maxHeartbeats 1000000

def inner (N : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (PRZZ.fengArithmetic n : ℂ)/n *
    weight A u θ P (Real.log n/L)

theorem weight_iteratedDeriv (k : ℕ) (u θ v : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    iteratedDeriv k (fun z => weight z u θ P v) A =
      (-(v : ℂ))^k * weight A u θ P v := by
  have he : (fun z => weight z u θ P v) =
      (fun z => Complex.exp (-(v : ℂ)*z) * P.eval (((u-v)/θ : ℝ):ℂ)) := by
    funext z
    unfold weight
    congr 2
    ring
  rw [he,iteratedDeriv_mul_const_field,iteratedDeriv_cexp_const_mul]
  dsimp only
  unfold weight
  rw [show -(v : ℂ)*A = -A*v by ring]
  ring

theorem conrey_inner_iteratedDeriv (k N : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    iteratedDeriv k (CoprimeShift.inner N L u θ P) A =
      ∑ n ∈ Finset.Icc 1 N, (μ n : ℂ)/n *
        (-(Real.log n/L : ℝ):ℂ)^k * weight A u θ P (Real.log n/L) := by
  unfold CoprimeShift.inner
  rw [iteratedDeriv_fun_sum (by intros; unfold weight; fun_prop)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_const_mul_field,weight_iteratedDeriv]
  ring

/-- All powers of each prime occur in the second sum, with exact cutoff N/r. -/
theorem shifted_feng_expansion (N : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    inner N L u θ P A =
      (∑ n ∈ Finset.Icc 1 N, (μ n : ℂ)/n * (Real.log n : ℂ)^2 *
        weight A u θ P (Real.log n/L)) +
      ∑ r ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt r * Real.log r : ℝ):ℂ) *
        supportFactor r L A * CoprimeShift.inner (N/r) L (u-Real.log r/L) θ P A := by
  unfold inner
  simp_rw [div_mul_eq_mul_div,mul_div_assoc]
  have h := FengArithmetic.weighted_feng_expansion N
    (fun n => weight A u θ P (Real.log n/L)/(n:ℂ))
  simp only [PRZZ.muReal,ArithmeticFunction.coe_mk,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_intCast] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  unfold CoprimeShift.inner
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by
    have := (Finset.mem_Icc.mp hr).1; omega)
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by
    have := (Finset.mem_Icc.mp hm).1; omega)
  rw [Nat.cast_mul,Real.log_mul hr0 hm0,add_div,weight_translate]
  unfold supportFactor
  push_cast
  ring

/-- Exact connection to the existing shift derivative, BEFORE any limit.
There is no extra 2! division in the original Feng coefficient. -/
theorem shifted_feng_derivative (N : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ)
    (hL : L ≠ 0) :
    inner N L u θ P A = (L:ℂ)^2 * iteratedDeriv 2 (CoprimeShift.inner N L u θ P) A +
      ∑ r ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt r * Real.log r : ℝ):ℂ) *
        supportFactor r L A * CoprimeShift.inner (N/r) L (u-Real.log r/L) θ P A := by
  rw [shifted_feng_expansion,conrey_inner_iteratedDeriv,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL
  simp only [Complex.ofReal_div]
  field_simp

#print axioms weight_iteratedDeriv
#print axioms conrey_inner_iteratedDeriv
#print axioms shifted_feng_expansion
#print axioms shifted_feng_derivative
end XiPrime8845.FengShift

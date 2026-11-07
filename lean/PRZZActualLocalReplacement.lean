import PRZZLocalReplacement
import PRZZAFEIndices

/-! Substitute the literal four-index AFE terms into the local replacement
bound. Both AFE cutoffs and mollifier denominators remain intact. Small
product contour improvement is not asserted by this adapter. -/
noncomputable section
open scoped BigOperators
open Finset Set MeasureTheory
namespace XiPrime8845.PRZZActualLocalReplacement
open PRZZAFEIndices PRZZL1Finite PRZZLocalReplacement PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def coefficient (a b : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) (i : Index) : ℂ :=
  term a b alpha beta (fun _ _ => 1) t i.1.1 i.1.2 i.2.1 i.2.2

def product (i : Index) : ℝ := (i.1.1:ℝ)*i.1.2

def localizedKernel (F : ℝ → ℂ) (R : ℝ) (V : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ :=
  fun n t => F ((n:ℝ)/R)*V n t

/-- Exact replacement identity at every original index, including zeros.
The coefficient includes the two time-dependent Dirichlet denominators. -/
theorem term_difference (a b : ℕ → ℂ) (alpha beta : ℂ) (t R : ℝ)
    (F : ℝ → ℂ) (i : Index) :
    term a b alpha beta
      (localizedKernel F R (fun n t => PRZZAFEGamma.kernel alpha beta n t))
      t i.1.1 i.1.2 i.2.1 i.2.2 -
    term a b alpha beta
      (localizedKernel F R (fun n t => sourceW (alpha+beta) ((n:ℝ)/(t/(2*Real.pi)))))
      t i.1.1 i.1.2 i.2.1 i.2.2 =
    (coefficient a b alpha beta t i*F (product i/R))*error alpha beta (product i) t := by
  simp only [term,directTerm,localizedKernel,coefficient,product,error,Nat.cast_mul]
  ring

/-- All actual retained indices at once. No all-row scale hypothesis or
abstract CellBound is supplied: support of F supplies the product scale. -/
theorem all_rows : ∃ C : ℝ, 0 < C ∧ ∀ alpha beta : ℂ,
    ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 → ∀ T t R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < R →
    ∀ F : ℝ → ℂ, Function.support F ⊆ Icc (1:ℝ) 2 →
    ∀ (L N : ℕ) (a b : ℕ → ℂ),
    ‖∑ i ∈ indices L N,
      (term a b alpha beta
        (localizedKernel F R (fun n t => PRZZAFEGamma.kernel alpha beta n t))
        t i.1.1 i.1.2 i.2.1 i.2.2 -
       term a b alpha beta
        (localizedKernel F R (fun n t => sourceW (alpha+beta) ((n:ℝ)/(t/(2*Real.pi)))))
        t i.1.1 i.1.2 i.2.1 i.2.2)‖ ≤
      (C*(1+16/‖alpha+beta‖^2)*T/R^2)*
        ∑ i ∈ indices L N, ‖coefficient a b alpha beta t i*F (product i/R)‖ := by
  obtain ⟨C,hC,h⟩ := cutoff_finite_bound (ι := Index)
  refine ⟨C,hC,?_⟩
  intro alpha beta ha hb hs T t R hT hT' ht ht2 hR F hF L N a b
  simp_rw [term_difference]
  exact h alpha beta ha hb hs T t R hT hT' ht ht2 hR F hF (indices L N) _ product

/-- Gcd/gap/dyadic grouping leaves the coefficient mass unchanged. -/
theorem grouped_mass (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (t R : ℝ) (F : ℝ → ℂ) :
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖coefficient a b alpha beta t i*F (product i/R)‖) =
    ∑ i ∈ indices L N, ‖coefficient a b alpha beta t i*F (product i/R)‖ :=
  mass_exact L N _

/-- The actual arithmetic coefficient has time-independent norm. -/
theorem coefficient_norm (a b : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ) (i : Index)
    (hm : 0 < i.1.1) (hk : 0 < i.1.2) (hn : 0 < i.2.1) (hr : 0 < i.2.2) :
    ‖coefficient a b alpha beta t i‖ = ‖coefficient a b alpha beta 0 i‖ := by
  have hm' : (0:ℝ) < i.1.1 := by exact_mod_cast hm
  have hk' : (0:ℝ) < i.1.2 := by exact_mod_cast hk
  have hn' : (0:ℝ) < i.2.1 := by exact_mod_cast hn
  have hr' : (0:ℝ) < i.2.2 := by exact_mod_cast hr
  simp only [coefficient,term,directTerm,norm_mul,norm_div,norm_star,norm_one]
  simp only [← Complex.ofReal_natCast]
  simp only [
    Complex.norm_cpow_eq_rpow_re_of_pos hm',Complex.norm_cpow_eq_rpow_re_of_pos hk',
    Complex.norm_cpow_eq_rpow_re_of_pos hn',Complex.norm_cpow_eq_rpow_re_of_pos hr']
  simp

theorem mass_time_independent (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (t R : ℝ) (F : ℝ → ℂ) :
    (∑ i ∈ indices L N, ‖coefficient a b alpha beta t i*F (product i/R)‖) =
      ∑ i ∈ indices L N, ‖coefficient a b alpha beta 0 i*F (product i/R)‖ := by
  apply sum_congr rfl
  intro i hi
  obtain ⟨hmk,hnr⟩ := mem_product.mp hi
  obtain ⟨hm,hk⟩ := mem_product.mp hmk
  obtain ⟨hn,hr⟩ := mem_product.mp hnr
  simp only [norm_mul]
  rw [coefficient_norm a b alpha beta t i (mem_Icc.mp hm).1 (mem_Icc.mp hk).1
    (mem_Icc.mp hn).1 (mem_Icc.mp hr).1]

/-- The original four-index replacement under weighted time integration.
No time-uniform coefficient bound is assumed; its exact mass is supplied. -/
theorem all_rows_time : ∃ C : ℝ, 0 < C ∧ ∀ alpha beta : ℂ,
    ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 → ∀ T R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → 0 < R →
    ∀ F : ℝ → ℂ, Function.support F ⊆ Icc (1:ℝ) 2 →
    ∀ (L N : ℕ) (a b : ℕ → ℂ) (phi : ℝ → ℂ), Continuous phi →
    ‖∫ t in Icc T (2*T), phi t*∑ i ∈ indices L N,
      (term a b alpha beta
        (localizedKernel F R (fun n t => PRZZAFEGamma.kernel alpha beta n t))
        t i.1.1 i.1.2 i.2.1 i.2.2 -
       term a b alpha beta
        (localizedKernel F R (fun n t => sourceW (alpha+beta) ((n:ℝ)/(t/(2*Real.pi)))))
        t i.1.1 i.1.2 i.2.1 i.2.2)‖ ≤
      (C*(1+16/‖alpha+beta‖^2)*T/R^2)*
        (∑ i ∈ indices L N, ‖coefficient a b alpha beta 0 i*F (product i/R)‖)*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := all_rows
  refine ⟨C,hC,?_⟩
  intro alpha beta ha hb hs T R hT hT' hR F hF L N a b phi hphi
  rw [← integral_const_mul]
  have hi : Continuous (fun t : ℝ =>
      (C*(1+16/‖alpha+beta‖^2)*T/R^2)*
        (∑ i ∈ indices L N, ‖coefficient a b alpha beta 0 i*F (product i/R)‖)*‖phi t‖) := by
    fun_prop
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hh := h alpha beta ha hb hs T t R hT hT' ht.1 ht.2 hR F hF L N a b
  rw [mass_time_independent] at hh
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (phi t))).trans_eq (by ring)

#print axioms coefficient_norm
#print axioms mass_time_independent
#print axioms all_rows_time
#print axioms term_difference
#print axioms all_rows
#print axioms grouped_mass
end XiPrime8845.PRZZActualLocalReplacement

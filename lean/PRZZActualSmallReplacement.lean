import PRZZActualLocalReplacement
import PRZZLeftUniform

/-! The shifted-contour improvement on the literal retained four-index AFE.
The exact coefficient mass is time independent. Neither removal of the
arithmetic truncation nor a bound for the sum over product scales is asserted. -/
noncomputable section
open scoped BigOperators
open Finset Set MeasureTheory
namespace XiPrime8845.PRZZActualSmallReplacement
open PRZZAFEIndices PRZZL1Finite PRZZLocalReplacement PRZZDyadicEnvelope
open PRZZActualLocalReplacement
set_option maxHeartbeats 2000000

theorem cutoff_finite {ι : Type*} : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t R : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < R →
    ∀ F : ℝ → ℂ, Function.support F ⊆ Icc (1:ℝ) 2 →
    ∀ (s : Finset ι) (c : ι → ℂ) (x : ι → ℝ),
    ‖∑ i ∈ s, (c i*F (x i/R))*error a b (x i) t‖ ≤
      (C*(1+32/‖a+b‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ))*
        ∑ i ∈ s, ‖c i*F (x i/R)‖ := by
  obtain ⟨C,hC,h⟩ := PRZZLeftUniform.small_product_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t R hT hT' ht ht2 hR F hF s c x
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  by_cases hz : c i*F (x i/R) = 0
  · simp [hz]
  have hf := (mul_ne_zero_iff.mp hz).2
  have hx0 : 0 < x i := hR.trans_le (cutoff_scale F hF R (x i) hR hf)
  have hx2 : x i ≤ 2*R := (div_le_iff₀ hR).mp (hF hf).2
  have hh := h a b ha hb hs T t (x i) hT hT' ht ht2 hx0
  have hbnd : ‖error a b (x i) t‖ ≤
      C*(1+32/‖a+b‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ) := by
    apply hh.trans
    gcongr
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)).trans_eq (by ring)

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
      (C*(1+32/‖alpha+beta‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ))*
        ∑ i ∈ indices L N, ‖coefficient a b alpha beta t i*F (product i/R)‖ := by
  obtain ⟨C,hC,h⟩ := cutoff_finite (ι := Index)
  refine ⟨C,hC,?_⟩
  intro alpha beta ha hb hs T t R hT hT' ht ht2 hR F hF L N a b
  simp_rw [term_difference]
  exact h alpha beta ha hb hs T t R hT hT' ht ht2 hR F hF (indices L N) _ product

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
      (C*(1+32/‖alpha+beta‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ))*
        (∑ i ∈ indices L N, ‖coefficient a b alpha beta 0 i*F (product i/R)‖)*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := all_rows
  refine ⟨C,hC,?_⟩
  intro alpha beta ha hb hs T R hT hT' hR F hF L N a b phi hphi
  rw [← integral_const_mul]
  have hi : Continuous (fun t : ℝ =>
      (C*(1+32/‖alpha+beta‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ))*
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


/-- Exact coefficient mass, with the localized product sum kept intact.
No cardinality of the gcd/gap/dyadic label set is paid. -/
theorem mass_factorized (L N : ℕ) (a b : ℕ → ℂ) (alpha beta : ℂ)
    (R : ℝ) (F : ℝ → ℂ) :
    (∑ i ∈ indices L N, ‖coefficient a b alpha beta 0 i*F (product i/R)‖) =
      (∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
        ‖directTerm alpha beta (fun _ _ => 1) 0 m k‖*‖F ((m:ℝ)*k/R)‖)*
      (∑ n ∈ Finset.Icc 1 N, ‖a n/(n:ℂ)^(1/2:ℂ)‖)*
      (∑ n ∈ Finset.Icc 1 N, ‖b n/(n:ℂ)^(1/2:ℂ)‖) := by
  simp only [indices,sum_product]
  rw [Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl; intro m hm
  rw [Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl; intro k hk
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro r hr
  simp only [coefficient,term,product,norm_mul,norm_star,Complex.ofReal_zero,zero_mul,add_zero]
  ring

theorem factorized_time : ∃ C : ℝ, 0 < C ∧ ∀ alpha beta : ℂ,
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
      (C*(1+32/‖alpha+beta‖^2)*(2*R)^(1/8:ℝ)*T^(-9/8:ℝ))*
        ((∑ m ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 L,
          ‖directTerm alpha beta (fun _ _ => 1) 0 m k‖*‖F ((m:ℝ)*k/R)‖)*
         (∑ n ∈ Finset.Icc 1 N, ‖a n/(n:ℂ)^(1/2:ℂ)‖)*
         (∑ n ∈ Finset.Icc 1 N, ‖b n/(n:ℂ)^(1/2:ℂ)‖))*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := all_rows_time
  refine ⟨C,hC,?_⟩
  intro alpha beta ha hb hs T R hT hT' hR F hF L N a b phi hphi
  have hh := h alpha beta ha hb hs T R hT hT' hR F hF L N a b phi hphi
  rw [mass_factorized] at hh
  exact hh

#print axioms factorized_time
#print axioms mass_factorized
#print axioms cutoff_finite
#print axioms all_rows
#print axioms all_rows_time
end XiPrime8845.PRZZActualSmallReplacement

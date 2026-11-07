import PRZZHeightMass
import PRZZReplacementIntegral

/-! Retain the square-root denominators of the actual mollifiers when
aggregating the V-W error. This improves the N^2 coefficient loss to N;
the contour-line cost is still explicit, not the optimized PRZZ remainder. -/
noncomputable section
open scoped BigOperators
open Finset Complex MeasureTheory Set
namespace XiPrime8845.PRZZReplacementMass
open PRZZGCoefficient PRZZReplacementIntegral PRZZMollifiedTime
set_option maxHeartbeats 3000000

theorem reciprocal_sqrt_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1/Real.sqrt n) ≤ 2*Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hs : 0 < Real.sqrt ((N:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have hstep : 1/Real.sqrt ((N:ℝ)+1) ≤
        2*(Real.sqrt ((N:ℝ)+1)-Real.sqrt N) := by
      apply (div_le_iff₀ hs).mpr
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity),
        Real.sq_sqrt (show 0 ≤ (N:ℝ)+1 by positivity),
        sq_nonneg (Real.sqrt ((N:ℝ)+1)-Real.sqrt N)]
    push_cast
    linarith

theorem polynomial_bound (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖PRZZ.dirichletPolynomial (fun n => (coefficient js n:ℂ)) N (1/2+t*I)‖ ≤
      2*Real.sqrt N*(Real.log N)^degree js := by
  unfold PRZZ.dirichletPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (Real.log N)^degree js*(1/Real.sqrt n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
      rw [norm_div,← Complex.ofReal_natCast n,norm_cpow_eq_rpow_re_of_pos hn0]
      have he : (1/2+(t:ℂ)*I).re = (1/2:ℝ) := by simp
      rw [he,← Real.sqrt_eq_rpow]
      have hc : ‖(coefficient js n:ℂ)‖ ≤ (Real.log N)^degree js := by
        simpa using coefficient_bound js N hN n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
      exact (div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _)).trans_eq (by ring)
    _ = (Real.log N)^degree js*(∑ n ∈ Finset.Icc 1 N, 1/Real.sqrt n) := by rw [mul_sum]
    _ ≤ (Real.log N)^degree js*(2*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (reciprocal_sqrt_sum N)
        (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)
    _ = _ := by ring

/-- The actual two mollifiers are bounded together; the imaginary time
shift contributes no growth to the square-root denominators. -/
theorem source_weight_bound (js : List ℕ) (N : ℕ) (hN : 1 ≤ N)
    (phi : ℝ → ℂ) (t : ℝ) :
    ‖mollifierWeight phi (fun n => (coefficient js n:ℂ))
      (fun n => (coefficient js n:ℂ)) N t‖ ≤
      (4*(N:ℝ)*(Real.log N)^(2*degree js))*‖phi t‖ := by
  unfold mollifierWeight
  rw [norm_mul,norm_mul,norm_star]
  have hp := polynomial_bound js N hN t
  have hB : 0 ≤ 2*Real.sqrt N*(Real.log N)^degree js := by
    have := Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN)
    positivity
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hp
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB)).trans_eq
  rw [show 2*degree js=degree js+degree js by omega,pow_add]
  calc
    _ = 4*(Real.sqrt N)^2*((Real.log N)^degree js*(Real.log N)^degree js)*‖phi t‖ := by ring
    _ = _ := by rw [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)]

/-- Substitutes the concrete arithmetic mass in the existing integrated
V-W estimate. No coefficient-mass or error estimate is supplied as a premise. -/
theorem integrated_source : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ js : List ℕ, ∀ N : ℕ, 1 ≤ N →
    ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), mollifierWeight phi (fun n => (coefficient js n:ℂ))
      (fun n => (coefficient js n:ℂ)) N t*difference a b t‖ ≤
      C*(1+16/‖a+b‖^2)*arithmeticMass *
        (4*(N:ℝ)*(Real.log N)^(2*degree js)) *
          ∫ t in Icc T (2*T), ‖phi t‖*cost T t := by
  obtain ⟨C,hC,h⟩ := weighted_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T hT hT' js N hN phi hphi
  have hh := h a b ha hb hs T hT hT' _
    (mollifierWeight_continuous phi hphi (fun n => (coefficient js n:ℂ))
      (fun n => (coefficient js n:ℂ)) N)
  apply hh.trans
  have hc : Continuous (fun t : ℝ =>
      (4*(N:ℝ)*(Real.log N)^(2*degree js))*‖phi t‖*cost T t) := by
    unfold cost; fun_prop
  have hi : (∫ t in Icc T (2*T),
      ‖mollifierWeight phi (fun n => (coefficient js n:ℂ))
        (fun n => (coefficient js n:ℂ)) N t‖*cost T t) ≤
      (4*(N:ℝ)*(Real.log N)^(2*degree js))*∫ t in Icc T (2*T), ‖phi t‖*cost T t := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => by unfold cost; positivity))
      (by simpa only [IntegrableOn,mul_assoc] using
        (hc.integrableOn_Icc : IntegrableOn _ (Icc T (2*T))))
    apply Filter.Eventually.of_forall
    intro t
    exact (mul_le_mul_of_nonneg_right (source_weight_bound js N hN phi t)
      (by unfold cost; positivity)).trans_eq (by ring)
  have hm : 0 ≤ arithmeticMass := tsum_nonneg (by intro p; positivity)
  convert mul_le_mul_of_nonneg_left hi
    (show 0 ≤ C*(1+16/‖a+b‖^2)*arithmeticMass by positivity) using 1 <;> ring

#print axioms reciprocal_sqrt_sum
#print axioms polynomial_bound
#print axioms source_weight_bound
#print axioms integrated_source
end XiPrime8845.PRZZReplacementMass

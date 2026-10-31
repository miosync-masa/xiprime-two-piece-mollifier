import WuAuxiliaryMultiplicity

/-! Critical-line zeros of eta are charged with their full analytic order
to xi'. This is the zero correction needed by a phase-counting argument;
the crossing/variation inequality itself is not asserted here. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex
namespace XiPrime8845.WuCriticalMultiplicity
open WuAuxiliary WuAuxiliaryBoundary WuAuxiliaryMultiplicity Zeta23.XiPrime
set_option maxHeartbeats 2000000

theorem eta_conj (L : ℝ) (s : ℂ) : eta L (conj s) = conj (eta L s) := by
  simp [WuAuxiliary.eta,xi_derivative_conj,map_sum,map_mul,map_pow]

theorem realtype_iterated (f : ℂ → ℂ) (hf : ∀ s, f (conj s) = conj (f s))
    (n : ℕ) (s : ℂ) : iteratedDeriv n f (conj s) = conj (iteratedDeriv n f s) := by
  induction n generalizing s with
  | zero => exact hf s
  | succ n ih =>
    have he : conj ∘ iteratedDeriv n f ∘ conj = iteratedDeriv n f := by
      funext z
      simp only [Function.comp_def,ih,Complex.conj_conj]
    have hh := congrFun (deriv_conj_conj (f := iteratedDeriv n f)) (conj s)
    rw [he] at hh
    simpa only [iteratedDeriv_succ,Function.comp_def,Complex.conj_conj] using hh

theorem realtype_order (f : ℂ → ℂ) (ha : Differentiable ℂ f)
    (hf : ∀ s, f (conj s) = conj (f s)) (s : ℂ) :
    analyticOrderAt f (conj s) = analyticOrderAt f s := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha.analyticAt _)]
  simp only [realtype_iterated f hf, map_eq_zero]

theorem reflected_order (L t : ℝ) :
    analyticOrderAt (fun s => eta L (1-s)) (critical t) = analyticOrderAt (eta L) (critical t) := by
  have he := analyticOrderAt_comp_of_deriv_ne_zero (f := eta L) (z₀ := critical t)
    (show AnalyticAt ℂ (fun s : ℂ => 1-s) (critical t) by fun_prop)
    (show deriv (fun s : ℂ => 1-s) (critical t) ≠ 0 by simp)
  have hc : 1-critical t = conj (critical t) := by
    apply Complex.ext <;> norm_num [critical]
  simpa only [Function.comp_def,hc,realtype_order _ (eta_entire L) (eta_conj L)] using he

theorem eta_order_le_xiDeriv (L t : ℝ) (hL : L ≠ 0) :
    analyticOrderNatAt (eta L) (critical t) ≤ analyticOrderNatAt xiDeriv (critical t) := by
  have hmin := le_analyticOrderAt_sub (f := eta L) (g := fun s => eta L (1-s)) (z₀ := critical t)
  rw [reflected_order,min_self] at hmin
  have hc : 2*((rCoeff 1:ℂ)/(L:ℂ)) ≠ 0 := mul_ne_zero (by norm_num)
    (div_ne_zero (by exact_mod_cast linear_coefficient_pos.ne') (by exact_mod_cast hL))
  have he : WuAuxiliary.eta L-(fun s => eta L (1-s)) = (fun _ : ℂ => 2*((rCoeff 1:ℂ)/(L:ℂ)))*xiDeriv :=
    funext (eta_reflection_difference L)
  have hc0 : analyticOrderAt (fun _ : ℂ => 2*((rCoeff 1:ℂ)/(L:ℂ))) (critical t) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hc)
  rw [he,analyticOrderAt_mul analyticAt_const (xiDeriv_differentiable.analyticAt _),
    hc0,zero_add] at hmin
  have heta := entire_order_ne_top _ (eta_entire L) (eta_not_identically_zero L hL) (critical t)
  have hxi := analyticOrderAt_xiDeriv_ne_top (critical t)
  exact_mod_cast (show (analyticOrderNatAt (eta L) (critical t):ℕ∞) ≤
      (analyticOrderNatAt xiDeriv (critical t):ℕ∞) by
    simpa only [Nat.cast_analyticOrderNatAt heta,Nat.cast_analyticOrderNatAt hxi] using hmin)

/-- Every finite critical-line selection, including zeros of eta itself.
No simplicity, parity, or nonvanishing hypothesis on eta is imposed. -/
theorem critical_zero_budget (L : ℝ) (hL : L ≠ 0) (S : Finset ℝ) :
    (∑ t ∈ S, analyticOrderNatAt (eta L) (critical t)) ≤
      ∑ t ∈ S, analyticOrderNatAt xiDeriv (critical t) :=
  Finset.sum_le_sum (fun t _ => eta_order_le_xiDeriv L t hL)

#print axioms eta_conj
#print axioms realtype_order
#print axioms reflected_order
#print axioms eta_order_le_xiDeriv
#print axioms critical_zero_budget
end XiPrime8845.WuCriticalMultiplicity

import PRZZOptimalPowers
import PRZZSourceWOuter

/-! The actual Gaussian source-weight mass times the local nine-term budget.
The local X,V factors cancel before summation. This does not supply the
identification of every actual arithmetic cell with this local budget.
The logarithmic and frequency losses have separately named exponents. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Complex
namespace XiPrime8845.PRZZOptimalOuter
open PRZZOptimalPowers PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

theorem source_mass_budget (m : ℕ) (K S r eps : ℝ)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (N T M X V freq lam : ℝ) (A B : ℂ),
      0 < d → 1 ≤ N → N ≤ T → 0 < M → 0 < X → X ≤ N → 0 < V → V ≤ N →
      1 ≤ Real.log T → r ≤ ‖A+B‖ →
      |Real.log M|+|Real.log V| ≤ K*Real.log T →
      |(((A+B)/(Real.log T:ℂ))).re| ≤ S/Real.log T →
      0 ≤ freq → 1 ≤ lam → freq ≤ lam*(X*V/T) →
      (∫ p, ‖common d T M X V (sourceW ((A+B)/(Real.log T:ℂ)))
        ((A+B)/(Real.log T:ℂ)) p‖)*(Real.log T)^m *
        PRZZCombinedBudget.total X freq V ≤ C*T^eps*lam*target N T/(d:ℝ) := by
  obtain ⟨C,hC,h⟩ := PRZZSourceWOuter.actual_mass_absorbed m K S r eps hK hS hr heps
  refine ⟨11*C,by positivity,?_⟩
  intro d N T M X V freq lam A B hd hN hNT hM hX hXN hV hVN hL hsep hscale hz hf hl hfreq
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  have hb : 0 ≤ PRZZCombinedBudget.total X freq V := by
    unfold PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  have hm := h d T M X V A B hd (hN.trans hNT) hM hX hV hL hsep hscale hz
  calc
    _ ≤ (C*T^eps*T/((d:ℝ)*X*V))*PRZZCombinedBudget.total X freq V :=
      mul_le_mul_of_nonneg_right hm hb
    _ = (C*T^eps)*(T/((d:ℝ)*X*V)*PRZZCombinedBudget.total X freq V) := by ring
    _ ≤ (C*T^eps)*(lam*(11*target N T/(d:ℝ))) :=
      mul_le_mul_of_nonneg_left
        (source_frequency_bound N T X V d freq lam hN hNT hX hXN hV hVN hd0 hf hl hfreq)
        (by positivity)
    _ = _ := by ring

#print axioms source_mass_budget

/-- The same constant works for every selected local box. Local masses
are multiplied by their own budgets before the finite sum is taken.
The explicit weight mass is not silently declared polylogarithmic. -/
theorem finite_source_mass_budget (m : ℕ) (K S r eps : ℝ)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (s : Finset ι) (w M X V freq : ι → ℝ)
      (d : ℕ) (N T lam : ℝ) (A B : ℂ),
      0 < d → 1 ≤ N → N ≤ T → 1 ≤ Real.log T → 1 ≤ lam → r ≤ ‖A+B‖ →
      |(((A+B)/(Real.log T:ℂ))).re| ≤ S/Real.log T →
      (∀ i ∈ s, 0 ≤ w i ∧ 0 < M i ∧ 0 < X i ∧ X i ≤ N ∧ 0 < V i ∧ V i ≤ N ∧
        |Real.log (M i)|+|Real.log (V i)| ≤ K*Real.log T ∧
        0 ≤ freq i ∧ freq i ≤ lam*(X i*V i/T)) →
      (∑ i ∈ s, w i*((∫ p, ‖common d T (M i) (X i) (V i)
        (sourceW ((A+B)/(Real.log T:ℂ))) ((A+B)/(Real.log T:ℂ)) p‖)*
        (Real.log T)^m*PRZZCombinedBudget.total (X i) (freq i) (V i))) ≤
        (C*T^eps*lam*target N T/(d:ℝ))*(∑ i ∈ s, w i) := by
  obtain ⟨C,hC,h⟩ := source_mass_budget m K S r eps hK hS hr heps
  refine ⟨C,hC,?_⟩
  intro ι s w M X V freq d N T lam A B hd hN hNT hL hl hsep hz hcells
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hw,hM,hX,hXN,hV,hVN,hscale,hf,hfreq⟩ := hcells i hi
  exact (mul_le_mul_of_nonneg_left
    (h d N T (M i) (X i) (V i) (freq i) lam A B hd hN hNT hM hX hXN hV hVN
      hL hsep hscale hz hf hl hfreq) hw).trans_eq (mul_comm _ _)

#print axioms finite_source_mass_budget

/-- Spend an explicit strict exponent margin on the remaining logarithms.
The power a is retained, rather than silently renamed epsilon. -/
theorem power_log_absorbed (m : ℕ) (a delta : ℝ) (hmargin : a < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      T^a*(Real.log T)^m ≤ C*T^delta := by
  obtain ⟨C,hC,h⟩ := PRZZGAbsorption.log_pow_bound m (delta-a) (by linarith)
  refine ⟨C,hC,?_⟩
  intro T hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc
    _ ≤ T^a*(C*T^(delta-a)) := mul_le_mul_of_nonneg_left (h T hT) (by positivity)
    _ = C*T^delta := by rw [mul_left_comm,← Real.rpow_add hT0]; congr 1; ring

#print axioms power_log_absorbed
end XiPrime8845.PRZZOptimalOuter

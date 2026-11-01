import PRZZSharpAggregation

/-! Explicit upper-box inflation in the seven Type II terms (PRZZ v3,
section 4, p.21). EF is not silently identified with the reference U.
The constant c is independent of height and all h in the supported sum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZInflatedSeven
open PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem power_bound (E U Y c e u : ℝ) (hU : 0 < U) (hY : 0 ≤ Y)
    (hc : 1 ≤ c) (hlo : U^(1/4:ℝ) ≤ E) (hhi : E ≤ c*U^(1/2:ℝ))
    (hprod : Y ≤ c*U) (hu : 0 ≤ u) (hexp : max e 0+u ≤ 2) :
    E^e*Y^u ≤ c^2*U^((if e ≤ 0 then (1/4:ℝ) else 1/2)*e+u) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hE : 0 < E := (Real.rpow_pos_of_pos hU _).trans_le hlo
  have he : E^e ≤ c^(max e 0)*U^((if e ≤ 0 then (1/4:ℝ) else 1/2)*e) := by
    by_cases he0 : e ≤ 0
    · simp only [if_pos he0,max_eq_right he0,Real.rpow_zero,one_mul]
      rw [Real.rpow_mul hU.le]
      exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU _) hlo he0
    · simp only [if_neg he0,max_eq_left (le_of_lt (lt_of_not_ge he0))]
      rw [Real.rpow_mul hU.le,← Real.mul_rpow hc0.le (Real.rpow_nonneg hU.le _)]
      exact Real.rpow_le_rpow hE.le hhi (le_of_lt (lt_of_not_ge he0))
  have hy : Y^u ≤ c^u*U^u := by
    rw [← Real.mul_rpow hc0.le hU.le]
    exact Real.rpow_le_rpow hY hprod hu
  have hh := mul_le_mul he hy (Real.rpow_nonneg hY _) (by positivity)
  have hid : (c^(max e 0)*U^((if e ≤ 0 then (1/4:ℝ) else 1/2)*e))*(c^u*U^u) =
      c^(max e 0+u)*U^((if e ≤ 0 then (1/4:ℝ) else 1/2)*e+u) := by
    rw [Real.rpow_add hc0,Real.rpow_add hU]
    ring
  rw [hid] at hh
  apply hh.trans
  have hb : c^(max e 0+u) ≤ c^2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc hexp
  exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hU.le _)

theorem seven_balanced (h E A U Y V c : ℝ) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hU : 0 < U) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hc : 1 ≤ c)
    (hlo : U^(1/4:ℝ) ≤ E) (hhi : E ≤ c*U^(1/2:ℝ)) (hprod : Y ≤ c*U) :
    seven h E A Y V ≤ c^2*∑ i : Fin 7, h^(hp i)*A^(ap i)*U^(balancedPower i)*V^(vp i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hb := power_bound E U Y c (ep i) (up i) hU hY hc hlo hhi hprod
    (by fin_cases i <;> norm_num [up]) (by fin_cases i <;> norm_num [ep,up])
  rw [balanced_exponents] at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ h^(hp i)*A^(ap i)*V^(vp i) by positivity)
  convert hm using 1 <;> ring

theorem seven_h_bound (h E X Y A V c : ℝ) (hh : 1 ≤ h) (hX : 0 < X)
    (hY : 0 ≤ Y) (hA : 0 ≤ A) (hV : 0 ≤ V) (hc : 1 ≤ c)
    (hlo : (X/h)^(1/4:ℝ) ≤ E) (hhi : E ≤ c*(X/h)^(1/2:ℝ))
    (hprod : Y ≤ c*(X/h)) :
    seven h E A Y V ≤ c^2*(envelope X A V/h^(3/8:ℝ)) := by
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one hh
  apply (seven_balanced h E A (X/h) Y V c hh0.le hA (div_pos hX hh0) hY hV hc hlo hhi hprod).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
  rw [balanced_h_sum h X A V hh0 hX.le]
  unfold envelope
  rw [sum_div]
  apply sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hh0 _)
    (Real.rpow_le_rpow_of_exponent_le hh (decay_lower i))

#print axioms power_bound
#print axioms seven_balanced
#print axioms seven_h_bound
end XiPrime8845.PRZZInflatedSeven

import Mathlib

/-! Algebraic bookkeeping of the seven displayed Type II terms, PRZZ
arXiv:1802.10521v3 p.21. Columns are powers of h,E,A,U,V in that order.
This does not assert that the actual Type II sum satisfies this display.
The DI substitution, source coefficient budgets and A-star identification
remain separate. The exact balanced range is U^(1/4) <= E <= U^(1/2);
constants in the source's Vinogradov range still need to be transported. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZDISeven
set_option maxHeartbeats 1000000

def hp : Fin 7 → ℝ := ![0,1/4,1/4,1/4,1/2,1/4,1/2]
def ep : Fin 7 → ℝ := ![-1/2,0,1/4,-1/4,1/4,1/4,3/4]
def ap : Fin 7 → ℝ := ![1/2,1,3/4,1,1,1/2,1/2]
def up : Fin 7 → ℝ := ![1,1,1,3/4,3/4,3/4,3/4]
def vp : Fin 7 → ℝ := ![1,1/2,1/2,1,3/4,1,3/4]
def balancedPower : Fin 7 → ℝ := ![7/8,1,9/8,11/16,7/8,7/8,9/8]

def seven (h E A U V : ℝ) : ℝ :=
  ∑ i : Fin 7, h^(hp i)*E^(ep i)*A^(ap i)*U^(up i)*V^(vp i)

/-- Literal order of the seven monomials in the source display. -/
theorem seven_expand (h E A U V : ℝ) : seven h E A U V =
    E^(-1/2:ℝ)*A^(1/2:ℝ)*U*V+
    h^(1/4:ℝ)*A*U*V^(1/2:ℝ)+
    h^(1/4:ℝ)*E^(1/4:ℝ)*A^(3/4:ℝ)*U*V^(1/2:ℝ)+
    h^(1/4:ℝ)*E^(-1/4:ℝ)*A*U^(3/4:ℝ)*V+
    h^(1/2:ℝ)*E^(1/4:ℝ)*A*U^(3/4:ℝ)*V^(3/4:ℝ)+
    h^(1/4:ℝ)*E^(1/4:ℝ)*A^(1/2:ℝ)*U^(3/4:ℝ)*V+
    h^(1/2:ℝ)*E^(3/4:ℝ)*A^(1/2:ℝ)*U^(3/4:ℝ)*V^(3/4:ℝ) := by
  norm_num [seven,Fin.sum_univ_succ,hp,ep,ap,up,vp]
  ring

theorem balanced_exponents (i : Fin 7) :
    (if ep i ≤ 0 then (1/4:ℝ) else 1/2)*ep i+up i = balancedPower i := by
  fin_cases i <;> norm_num [ep,up,balancedPower]

theorem balance_power (E U e u : ℝ) (hU : 0 < U)
    (hlo : U^(1/4:ℝ) ≤ E) (hhi : E ≤ U^(1/2:ℝ)) :
    E^e*U^u ≤ U^((if e ≤ 0 then (1/4:ℝ) else 1/2)*e+u) := by
  rw [Real.rpow_add hU]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU.le _)
  split_ifs with he
  · rw [Real.rpow_mul hU.le]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hU _) hlo he
  · rw [Real.rpow_mul hU.le]
    exact Real.rpow_le_rpow ((Real.rpow_pos_of_pos hU _).le.trans hlo) hhi (by linarith)

theorem seven_balanced (h E A U V : ℝ) (hh : 0 ≤ h) (hA : 0 ≤ A) (hU : 0 < U)
    (hV : 0 ≤ V) (hlo : U^(1/4:ℝ) ≤ E) (hhi : E ≤ U^(1/2:ℝ)) :
    seven h E A U V ≤
      ∑ i : Fin 7, h^(hp i)*A^(ap i)*U^(balancedPower i)*V^(vp i) := by
  apply Finset.sum_le_sum
  intro i hi
  have hb := balance_power E U (ep i) (up i) hU hlo hhi
  rw [balanced_exponents] at hb
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hh (hp i)) (Real.rpow_nonneg hA (ap i)))
    (Real.rpow_nonneg hV (vp i)))
  convert hm using 1 <;> ring

/-- Exact extraction of the hidden negative h power in U=X/h. -/
theorem h_power_transfer (h X p q : ℝ) (hh : 0 < h) (hX : 0 ≤ X) :
    h^p*(X/h)^q = X^q/h^(q-p) := by
  rw [Real.div_rpow hX hh.le,Real.rpow_sub hh]
  have hp0 := (Real.rpow_pos_of_pos hh p).ne'
  have hq0 := (Real.rpow_pos_of_pos hh q).ne'
  field_simp

/-- All seven terms retain a strictly positive h-decay exponent. -/
theorem decay_positive (i : Fin 7) : 0 < balancedPower i-hp i := by
  fin_cases i <;> norm_num [balancedPower,hp]

theorem decay_lower (i : Fin 7) : (3/8:ℝ) ≤ balancedPower i-hp i := by
  fin_cases i <;> norm_num [balancedPower,hp]

theorem balanced_h_sum (h X A V : ℝ) (hh : 0 < h) (hX : 0 ≤ X) :
    (∑ i : Fin 7, h^(hp i)*A^(ap i)*(X/h)^(balancedPower i)*V^(vp i)) =
      ∑ i : Fin 7, A^(ap i)*X^(balancedPower i)*V^(vp i)/h^(balancedPower i-hp i) := by
  apply Finset.sum_congr rfl
  intro i hi
  have he := h_power_transfer h X (hp i) (balancedPower i) hh hX
  calc
    _ = (h^(hp i)*(X/h)^(balancedPower i))*(A^(ap i)*V^(vp i)) := by ring
    _ = _ := by rw [he]; ring

def envelope (X A V : ℝ) : ℝ :=
  ∑ i : Fin 7, A^(ap i)*X^(balancedPower i)*V^(vp i)

/-- One positive h-decay budget works for all seven balanced terms. -/
theorem seven_h_bound (h E X A V : ℝ) (hh : 1 ≤ h) (hX : 0 < X)
    (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hlo : (X/h)^(1/4:ℝ) ≤ E) (hhi : E ≤ (X/h)^(1/2:ℝ)) :
    seven h E A (X/h) V ≤ envelope X A V/h^(3/8:ℝ) := by
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one hh
  apply (seven_balanced h E A (X/h) V hh0.le hA (div_pos hX hh0) hV hlo hhi).trans
  rw [balanced_h_sum h X A V hh0 hX.le]
  unfold envelope
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hX.le _))
      (Real.rpow_nonneg hV _))
    (Real.rpow_pos_of_pos hh0 _) (Real.rpow_le_rpow_of_exponent_le hh (decay_lower i))

/-- Finite h aggregation. A bound for the actual G(h) moment on the
right remains an arithmetic supplier; none is postulated here. -/
theorem finite_h_bound (s : Finset ℕ) (G E : ℕ → ℝ) (X A V : ℝ)
    (hX : 0 < X) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hs : ∀ h ∈ s, 1 ≤ h ∧ 0 ≤ G h ∧
      (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) :
    (∑ h ∈ s, G h*seven h (E h) A (X/h) V) ≤
      envelope X A V*(∑ h ∈ s, G h/(h:ℝ)^(3/8:ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  obtain ⟨h1,hG,hlo,hhi⟩ := hs h hh
  exact (mul_le_mul_of_nonneg_left
    (seven_h_bound h (E h) X A V (by exact_mod_cast h1) hX hA hV hlo hhi) hG).trans_eq (by ring)

#print axioms seven_expand
#print axioms balanced_exponents
#print axioms balance_power
#print axioms seven_balanced
#print axioms h_power_transfer
#print axioms decay_positive
#print axioms decay_lower
#print axioms balanced_h_sum
#print axioms seven_h_bound
#print axioms finite_h_bound
end XiPrime8845.PRZZDISeven

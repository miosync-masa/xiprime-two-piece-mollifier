import CoprimeEulerCompletion

/-! The literal outer prefactor before either coprimality Euler factor.
Prime head/tail control, rather than a fixed-g limit, will control its ratio. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.BareEuler
open ShiftedTotient ShiftedEulerLocal ShiftedEulerUniform
set_option maxHeartbeats 1000000

def weight (a b : ℂ) (g : ℕ) : ℂ :=
  (μ g:ℂ)^2 * ElementaryGcd.generalizedTotient (1+a+b) g / (g:ℂ)^(2+a+b)

theorem weight_product (a b : ℂ) (g : ℕ) :
    weight a b g = (μ g:ℂ)^2/(g:ℂ) *
      ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-(1+a+b))) := by
  by_cases hg : Squarefree g
  · unfold weight
    rw [generalizedTotient_squarefree _ g hg, cpow_squarefree _ g hg]
    rw [show (2:ℂ)+a+b = 1+(1+a+b) by ring]
    simp only [mul_div_assoc]
    rw [← Finset.prod_div_distrib]
    have ht : (∏ p ∈ g.primeFactors, ((p:ℂ)^(1+a+b)-1)/(p:ℂ)^(1+(1+a+b))) =
        ∏ p ∈ g.primeFactors, (1-(p:ℂ)^(-(1+a+b)))/(p:ℂ) := by
      exact prod_congr rfl (fun p hp => local_power_identity _ p (Nat.pos_of_mem_primeFactors hp).ne')
    rw [ht, Finset.prod_div_distrib]
    have hp : (∏ p ∈ g.primeFactors, (p:ℂ)) = (g:ℂ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hg]
    rw [hp]; ring
  · simp [weight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hg]

def primeRatio (A B : ℂ) (L : ℝ) (p : ℕ) : ℂ :=
  (1-(p:ℂ)⁻¹*twist A L p*twist B L p)/(1-(p:ℂ)⁻¹)

def ratio (A B : ℂ) (L : ℝ) (g : ℕ) : ℂ :=
  ∏ p ∈ g.primeFactors, primeRatio A B L p

theorem prime_factor (A B : ℂ) (L : ℝ) (p : ℕ) (hp : p.Prime) :
    1-(p:ℂ)^(-(1+A/L+B/L)) = (1-(p:ℂ)⁻¹)*primeRatio A B L p := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : (1:ℂ)-(p:ℂ)⁻¹ ≠ 0 := by
    intro h
    have he : (p:ℂ)⁻¹ = 1 := by linear_combination -h
    have := inv_eq_one.mp he
    exact hp.ne_one (by exact_mod_cast this)
  rw [primeRatio, mul_div_cancel₀ _ hd, twist_cpow A L p hp.ne_zero,
    twist_cpow B L p hp.ne_zero]
  rw [show -(1+A/(L:ℂ)+B/(L:ℂ)) = (-1:ℂ)+(-(A/(L:ℂ)))+(-(B/(L:ℂ))) by ring,
    Complex.cpow_add _ _ hp0, Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]

theorem weight_factor (A B : ℂ) (L : ℝ) (g : ℕ) :
    weight (A/L) (B/L) g = weight 0 0 g * ratio A B L g := by
  rw [weight_product, weight_product, mul_assoc, ratio, ← Finset.prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  simpa only [add_zero, Complex.cpow_neg_one] using prime_factor A B L p (Nat.prime_of_mem_primeFactors hp)

theorem prime_defect (A B : ℂ) (L C U : ℝ) (p : ℕ) (hp : p.Prime)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hpL : Real.log p ≤ L*U) (hCU : C*U ≤ 1) :
    ‖primeRatio A B L p-1‖ ≤ (16*C/L)*(Real.log p/p) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hC := (norm_nonneg A).trans hA
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  let d := 2*C*Real.log p/L
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd2 : d ≤ 2 := by
    dsimp [d]; apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpL hC]
  have hx := twist_bound A L C U p hp hL hA hpL hCU
  have hy := twist_bound B L C U p hp hL hB hpL hCU
  have hxn : ‖twist A L p‖ ≤ 3 := by
    have := norm_add_le (twist A L p-1) (1:ℂ)
    rw [sub_add_cancel, norm_one] at this
    linarith
  have hxy : ‖twist A L p*twist B L p-1‖ ≤ 4*d := by
    rw [show twist A L p*twist B L p-1 = twist A L p*(twist B L p-1)+(twist A L p-1) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hm := mul_le_mul hxn hy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
    linarith
  have hz : (p:ℝ)⁻¹ ≤ 1/2 := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hp2
  have hn : ‖(1:ℂ)-(p:ℂ)⁻¹‖ = 1-(p:ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hden : (1/2:ℝ) ≤ ‖(1:ℂ)-(p:ℂ)⁻¹‖ := by rw [hn]; linarith
  have hd : (1:ℂ)-(p:ℂ)⁻¹ ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : primeRatio A B L p-1 =
      -(p:ℂ)⁻¹*(twist A L p*twist B L p-1)/(1-(p:ℂ)⁻¹) := by
    unfold primeRatio
    apply (eq_div_iff hd).mpr
    rw [sub_mul, div_mul_cancel₀ _ hd]
    ring
  rw [he, norm_div, norm_mul, norm_neg, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ ((p:ℝ)⁻¹*(4*d))/(1/2) := div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hxy (by positivity)) (by norm_num) hden
    _ = _ := by dsimp [d]; ring

theorem prime_log_head_tail (g Q : ℕ) (hg : g ≠ 0) (hQ : 0 < Q) :
    (∑ p ∈ g.primeFactors, Real.log p/p) ≤ (Q+1:ℝ)+Real.log g/Q := by
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast hQ
  have hh : (∑ p ∈ g.primeFactors, if p ≤ Q then (1:ℝ) else 0) ≤ (Q+1:ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hc : (g.primeFactors.filter (fun p => p ≤ Q)).card ≤ (range (Q+1)).card :=
      card_le_card (by intro p hp; exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2))
    simpa using (show ((g.primeFactors.filter (fun p => p ≤ Q)).card:ℝ) ≤ ((range (Q+1)).card:ℝ) by exact_mod_cast hc)
  calc
    _ ≤ ∑ p ∈ g.primeFactors, ((if p ≤ Q then (1:ℝ) else 0)+Real.log p/Q) := by
      apply sum_le_sum
      intro p hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
      have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      split_ifs with h
      · have hb : Real.log p/p ≤ 1 := (div_le_one hp0).mpr
          ((Real.log_le_sub_one_of_pos hp0).trans (by linarith))
        have := div_nonneg hl hQ0.le; linarith
      · rw [zero_add]
        exact div_le_div_of_nonneg_left hl hQ0 (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h)))
    _ = (∑ p ∈ g.primeFactors, if p ≤ Q then (1:ℝ) else 0)+
        (∑ p ∈ g.primeFactors, Real.log p)/Q := by rw [sum_add_distrib, sum_div]
    _ ≤ _ := add_le_add hh (div_le_div_of_nonneg_right (prime_log_sum_le g hg) hQ0.le)

def envelope (C U : ℝ) (Q : ℕ) (L : ℝ) : ℝ :=
  Real.exp (16*C*((Q+1:ℝ)/L+U/Q))-1

theorem ratio_bound (A B : ℂ) (L C U : ℝ) (g Q : ℕ) (hg : g ≠ 0) (hQ : 0 < Q)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hgL : Real.log g ≤ L*U) (hCU : C*U ≤ 1) :
    ‖ratio A B L g-1‖ ≤ envelope C U Q L := by
  have hC := (norm_nonneg A).trans hA
  have hs : (∑ p ∈ g.primeFactors, ‖primeRatio A B L p-1‖) ≤
      16*C*((Q+1:ℝ)/L+U/Q) := by
    calc
      _ ≤ ∑ p ∈ g.primeFactors, (16*C/L)*(Real.log p/p) := by
        apply sum_le_sum
        intro p hp
        have hpg : (p:ℝ) ≤ g := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mem_primeFactors hp)
        exact prime_defect A B L C U p (Nat.prime_of_mem_primeFactors hp) hL hA hB
          ((Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_primeFactors hp) hpg).trans hgL) hCU
      _ = (16*C/L)*∑ p ∈ g.primeFactors, Real.log p/p := (mul_sum ..).symm
      _ ≤ (16*C/L)*((Q+1:ℝ)+Real.log g/Q) :=
        mul_le_mul_of_nonneg_left (prime_log_head_tail g Q hg hQ) (by positivity)
      _ ≤ (16*C/L)*((Q+1:ℝ)+L*U/Q) := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (div_le_div_of_nonneg_right hgL (show (0:ℝ) ≤ Q by positivity))) (by positivity)
      _ = _ := by field_simp
  have h := Finset.norm_prod_one_add_sub_one_le g.primeFactors (fun p => primeRatio A B L p-1)
  simp only [add_sub_cancel] at h
  exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hs) 1)

#print axioms weight_factor
#print axioms prime_defect
#print axioms prime_log_head_tail
#print axioms ratio_bound
end XiPrime8845.BareEuler

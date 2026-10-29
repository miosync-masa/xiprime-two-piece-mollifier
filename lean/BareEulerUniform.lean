import BareEuler

/-! Uniform control of the literal prefactor and the weighted replacement of
the two zero-shift inner Euler masses by the shifted masses. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.BareEulerUniform
open BareEuler ShiftedTotient
set_option maxHeartbeats 1000000

def tailLimit (C U : ℝ) (Q : ℕ) : ℝ := Real.exp (16*C*U/Q)-1

theorem envelope_tendsto (C U : ℝ) (Q : ℕ) :
    Tendsto (BareEuler.envelope C U Q) atTop (nhds (tailLimit C U Q)) := by
  change Tendsto (fun L : ℝ => Real.exp (16*C*((Q+1:ℝ)/L+U/Q))-1) atTop
    (nhds (Real.exp (16*C*U/Q)-1))
  have h : Tendsto (fun L : ℝ => 16*C*((Q+1:ℝ)/L+U/Q)) atTop (nhds (16*C*U/Q)) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_add,mul_assoc] using
      ((tendsto_inv_atTop_zero.const_mul (Q+1:ℝ)).add_const (U/Q)).const_mul (16*C)
  simpa only [BareEuler.envelope,tailLimit,Function.comp_apply] using
    ((Real.continuous_exp.tendsto _).comp h).sub_const 1

theorem tailLimit_tendsto (C U : ℝ) : Tendsto (tailLimit C U) atTop (nhds 0) := by
  change Tendsto (fun Q : ℕ => Real.exp (16*C*U/(Q:ℝ))-1) atTop (nhds 0)
  have hi : Tendsto (fun Q : ℕ => (Q:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun Q : ℕ => 16*C*U/(Q:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul (16*C*U)
  simpa only [tailLimit,Function.comp_apply,Real.exp_zero,sub_self] using
    ((Real.continuous_exp.tendsto _).comp h).sub_const 1

theorem ratio_uniform (C U : ℝ) (hCU : C*U ≤ 1) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (g : ℕ) (A B : ℂ),
      g ≠ 0 → (g:ℝ) ≤ Real.exp (L*U) → ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖BareEuler.ratio A B L g-1‖ < eps := by
  intro eps heps
  obtain ⟨Q,hQ,hsmall⟩ := ((eventually_gt_atTop (0:ℕ)).and
    ((tailLimit_tendsto C U).eventually (gt_mem_nhds heps))).exists
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (envelope_tendsto C U Q).eventually (gt_mem_nhds hsmall)] with L hL he
  intro g A B hg hcut hA hB
  exact (BareEuler.ratio_bound A B L C U g Q hg hQ hL hA hB
    ((Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hg)).mpr hcut) hCU).trans_lt he

theorem zero_weight_norm (g : ℕ) (hg : g ≠ 0) : ‖weight 0 0 g‖ ≤ 1/(g:ℝ) := by
  have hm : ‖(μ g:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast, Int.cast_abs] using
      (show (|(μ g)|:ℝ) ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g))
  have hp : ‖∏ p ∈ g.primeFactors, (1-(p:ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_prod]
    apply prod_le_one
    · intro p hp; exact norm_nonneg _
    · intro p hp
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      have hi : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      have : 0 ≤ (p:ℝ)⁻¹ := by positivity
      linarith
  rw [weight_product]
  simp only [add_zero,Complex.cpow_neg_one,norm_mul,norm_div,norm_pow,Complex.norm_natCast]
  have hmu : ‖(μ g:ℂ)‖^2 ≤ 1 := by nlinarith [norm_nonneg (μ g:ℂ)]
  have hh := mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hp
    (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1/(g:ℝ))
  simpa only [mul_one] using hh

/-- A common O(1/g) bound for the ACTUAL arithmetic prefactor. -/
theorem weight_bound_eventually (C U : ℝ) (hCU : C*U ≤ 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (g : ℕ) (A B : ℂ),
      g ≠ 0 → (g:ℝ) ≤ Real.exp (L*U) → ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖weight (A/L) (B/L) g‖ ≤ 2/(g:ℝ) := by
  filter_upwards [ratio_uniform C U hCU 1 (by norm_num)] with L hL
  intro g A B hg hcut hA hB
  have hr := hL g A B hg hcut hA hB
  have hn : ‖BareEuler.ratio A B L g‖ ≤ 2 := by
    have := norm_add_le (BareEuler.ratio A B L g-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at this; linarith
  rw [weight_factor,norm_mul]
  have h := mul_le_mul (zero_weight_norm g hg) hn (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1/(g:ℝ))
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

theorem zeroEuler_weight_factor (A B : ℂ) (L : ℝ) (g : ℕ) :
    weight (A/L) (B/L) g * euler 0 g * euler 0 g =
      outerWeight 0 0 g * BareEuler.ratio A B L g := by
  rw [weight_factor]
  unfold weight outerWeight
  ring

/-- The weighted difference of the TWO Euler-factor products. Neither
factor is divided out, and mu(g)=0 is retained. -/
theorem weighted_Euler_difference (A B : ℂ) (L : ℝ) (g : ℕ) :
    weight (A/L) (B/L) g * (euler 0 g*euler 0 g-euler (A/L) g*euler (B/L) g) =
      outerWeight 0 0 g * (BareEuler.ratio A B L g-ShiftedEulerUniform.ratio A B L g) := by
  have h := zeroEuler_weight_factor A B L g
  have hs := ShiftedEulerUniform.outerWeight_factor A B L g
  change weight (A/L) (B/L) g * euler (A/L) g * euler (B/L) g = _ at hs
  rw [mul_sub,mul_sub]
  linear_combination h-hs

theorem weighted_Euler_error_uniform (C U : ℝ) (hCU : C*U ≤ 1) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (g : ℕ) (A B : ℂ),
      g ≠ 0 → (g:ℝ) ≤ Real.exp (L*U) → ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖weight (A/L) (B/L) g * (euler 0 g*euler 0 g-euler (A/L) g*euler (B/L) g)‖ ≤
        ((μ g:ℝ)^2/g.totient)*eps := by
  intro eps heps
  filter_upwards [ratio_uniform C U hCU (eps/2) (by positivity),
    ShiftedEulerUniform.ratio_uniform_growing C U hCU (eps/2) (by positivity)] with L hL hS
  intro g A B hg hcut hA hB
  have hb := hL g A B hg hcut hA hB
  have hs := hS g A B hg hcut hA hB
  have hd : ‖BareEuler.ratio A B L g-ShiftedEulerUniform.ratio A B L g‖ ≤ eps := by
    have := norm_sub_le_norm_sub_add_norm_sub (BareEuler.ratio A B L g) 1
      (ShiftedEulerUniform.ratio A B L g)
    rw [norm_sub_rev (1:ℂ)] at this; linarith
  rw [weighted_Euler_difference,norm_mul,outerWeight_zero g hg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hd (by positivity)

#print axioms ratio_uniform
#print axioms weight_bound_eventually
#print axioms weighted_Euler_difference
#print axioms weighted_Euler_error_uniform
end XiPrime8845.BareEulerUniform

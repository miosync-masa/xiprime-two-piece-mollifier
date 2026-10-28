import ShiftedEulerLocal
import ShiftedMobius
import TotientHarmonic

/-! Uniform Euler-ratio control for a growing arithmetic cutoff and both
reflected shift regions. No full coprime-sum or gcd-kernel limit is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.ShiftedEulerUniform
open ShiftedEulerLocal ShiftedTotient
set_option maxHeartbeats 1000000

def ratio (A B : ℂ) (L : ℝ) (g : ℕ) : ℂ :=
  ∏ p ∈ g.primeFactors, primeRatio A B L p

def envelope (C U L : ℝ) : ℝ := Real.exp (64*C^2*U/L)-1

theorem prime_log_sum_le (g : ℕ) (hg : g ≠ 0) :
    (∑ p ∈ g.primeFactors, Real.log p) ≤ Real.log g := by
  have hp : ∀ p ∈ g.primeFactors, (p:ℝ) ≠ 0 := by
    intro p hp; exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
  rw [← Real.log_prod hp, ← Nat.cast_prod]
  apply Real.log_le_log
  · exact_mod_cast Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.prod_primeFactors_dvd g)

theorem ratio_bound (A B : ℂ) (L C U : ℝ) (g : ℕ) (hg : g ≠ 0)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hgL : Real.log g ≤ L*U) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L) :
    ‖ratio A B L g-1‖ ≤ envelope C U L := by
  have hsum : (∑ p ∈ g.primeFactors, ‖primeRatio A B L p-1‖) ≤ 64*C^2*U/L := by
    calc
      _ ≤ ∑ p ∈ g.primeFactors, (64*C^2/L^2)*Real.log p := by
        apply sum_le_sum
        intro p hp
        have hpg : (p:ℝ) ≤ g := by
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mem_primeFactors hp)
        have hlog := Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_primeFactors hp) hpg
        exact prime_defect_bound A B L C U p (Nat.prime_of_mem_primeFactors hp)
          hL hA hB (hlog.trans hgL) hCU hlarge
      _ = (64*C^2/L^2)*∑ p ∈ g.primeFactors, Real.log p := (mul_sum ..).symm
      _ ≤ (64*C^2/L^2)*(L*U) := mul_le_mul_of_nonneg_left
        ((prime_log_sum_le g hg).trans hgL) (by positivity)
      _ = _ := by field_simp
  have h := Finset.norm_prod_one_add_sub_one_le g.primeFactors
    (fun p => primeRatio A B L p-1)
  simp only [add_sub_cancel] at h
  exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem outerWeight_factor (A B : ℂ) (L : ℝ) (g : ℕ) :
    outerWeight (A/L) (B/L) g = outerWeight 0 0 g * ratio A B L g := by
  rw [outerWeight_product, outerWeight_product, mul_assoc, ratio, ← Finset.prod_mul_distrib]
  congr 1
  exact prod_congr rfl (fun p hp => primeRatio_factor A B L p (Nat.prime_of_mem_primeFactors hp))

theorem outerWeight_error (A B : ℂ) (L C U : ℝ) (g : ℕ) (hg : g ≠ 0)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hgL : Real.log g ≤ L*U) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L) :
    ‖outerWeight (A/L) (B/L) g - outerWeight 0 0 g‖ ≤
      ((μ g:ℝ)^2/g.totient) * envelope C U L := by
  rw [outerWeight_factor, ← mul_sub_one, norm_mul, outerWeight_zero g hg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (ratio_bound A B L C U g hg hL hA hB hgL hCU hlarge)
    (by positivity)

theorem envelope_tendsto (C U : ℝ) : Tendsto (envelope C U) atTop (nhds 0) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h : Tendsto (fun L : ℝ => 64*C^2*U/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (64*C^2*U)
  change Tendsto (fun L : ℝ => Real.exp (64*C^2*U/L)-1) atTop (nhds 0)
  simpa only [Function.comp_apply, Real.exp_zero, sub_self] using
    ((Real.continuous_exp.tendsto 0).comp h).sub_const 1

/-- The cutoff grows WITH L; the threshold is common to every g and both shifts. -/
theorem ratio_uniform_growing (C U : ℝ) (hCU : C*U ≤ 1) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (g : ℕ) (A B : ℂ),
      g ≠ 0 → (g:ℝ) ≤ Real.exp (L*U) → ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖ratio A B L g-1‖ < eps := by
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (8*C),
    (envelope_tendsto C U).eventually (gt_mem_nhds heps)] with L hL hlarge he
  intro g A B hg hgL hA hB
  have hlog := (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hg)).mpr hgL
  exact (ratio_bound A B L C U g hg hL hA hB hlog hCU hlarge).trans_lt he

theorem envelope_nonneg (C U L : ℝ) (hU : 0 ≤ U) (hL : 0 ≤ L) :
    0 ≤ envelope C U L := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))

def averageError (L U : ℝ) (A B : ℂ) : ℝ :=
  (∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
    ‖outerWeight (A/L) (B/L) g-outerWeight 0 0 g‖)/L

theorem averageError_nonneg (L U : ℝ) (A B : ℂ) (hL : 0 ≤ L) :
    0 ≤ averageError L U A B := by unfold averageError; positivity

/-- Actual arithmetic weights, averaged up to the moving exponential cutoff. -/
theorem averageError_bound (L C U : ℝ) (A B : ℂ) (hL : 0 < L) (hU : 0 ≤ U)
    (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L) :
    averageError L U A B ≤
      (U+TotientHarmonic.errorConstant/L)*envelope C U L := by
  have hs : (∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
      ‖outerWeight (A/L) (B/L) g-outerWeight 0 0 g‖) ≤
      TotientHarmonic.summatory (Real.exp (L*U))*envelope C U L := by
    rw [TotientHarmonic.summatory, Finset.sum_mul]
    apply sum_le_sum
    intro g hg
    have hg0 := (mem_Ioc.mp hg).1
    have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
    have hlog := (Real.log_le_iff_le_exp (by exact_mod_cast hg0)).mpr hgexp
    exact outerWeight_error A B L C U g hg0.ne' hL hA hB hlog hCU hlarge
  have ha := TotientHarmonic.normalized_bound L U hL hU
  have hb : TotientHarmonic.summatory (Real.exp (L*U))/L ≤ U+TotientHarmonic.errorConstant/L := by
    linarith [le_abs_self (TotientHarmonic.summatory (Real.exp (L*U))/L-U)]
  calc
    _ ≤ (TotientHarmonic.summatory (Real.exp (L*U))*envelope C U L)/L :=
      div_le_div_of_nonneg_right hs hL.le
    _ = (TotientHarmonic.summatory (Real.exp (L*U))/L)*envelope C U L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (envelope_nonneg C U L hU hL.le)

/-- Uniformly bounded profile products can be inserted without losing the
arithmetic error estimate. No regularity of this finite test array is needed. -/
theorem tested_weight_error_bound (L C U M : ℝ) (A B : ℂ) (f : ℕ → ℂ)
    (hL : 0 < L) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L)
    (hf : ∀ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊, ‖f g‖ ≤ M) :
    ‖(∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
      (outerWeight (A/L) (B/L) g-outerWeight 0 0 g)*f g)/(L:ℂ)‖ ≤
      M*((U+TotientHarmonic.errorConstant/L)*envelope C U L) := by
  have hs : ‖∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
      (outerWeight (A/L) (B/L) g-outerWeight 0 0 g)*f g‖ ≤
      M*∑ g ∈ Ioc 0 ⌊Real.exp (L*U)⌋₊,
        ‖outerWeight (A/L) (B/L) g-outerWeight 0 0 g‖ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro g hg
    rw [norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hf g hg) (norm_nonneg _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  apply (div_le_div_of_nonneg_right hs hL.le).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (averageError_bound L C U A B hL hU hA hB hCU hlarge) hM

theorem averageError_uniform (C U : ℝ) (hU : 0 ≤ U) (hCU : C*U ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageError L U p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have hc : Tendsto (fun L : ℝ => TotientHarmonic.errorConstant/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul TotientHarmonic.errorConstant
  have hlim : Tendsto (fun L : ℝ => (U+TotientHarmonic.errorConstant/L)*envelope C U L)
      atTop (nhds 0) := by simpa using (hc.const_add U).mul (envelope_tendsto C U)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (8*C),
    hlim.eventually (gt_mem_nhds heps)] with L hL hlarge he
  intro p hp
  rw [dist_comm, Real.dist_eq, sub_zero, abs_of_nonneg (averageError_nonneg L U p.1 p.2 hL.le)]
  exact (averageError_bound L C U p.1 p.2 hL hU hp.1 hp.2 hCU hlarge).trans_lt he

theorem witness_size : (5*PRZZAsymptotic.R/4)*PRZZAsymptotic.theta ≤ 1 := by
  norm_num [PRZZAsymptotic.R, PRZZAsymptotic.theta, XiPrime8845.radiusParameter]

/-- Positive and negative bidiscs are included simultaneously; no continuation
from one side to the other is used. -/
theorem ratio_twoBidiscs_uniform :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ (g : ℕ) (p : ℂ × ℂ),
      g ≠ 0 → (g:ℝ) ≤ Real.exp (L*PRZZAsymptotic.theta) →
      p ∈ ElementaryGcd.twoBidiscs → ‖ratio p.1 p.2 L g-1‖ < eps := by
  intro eps heps
  filter_upwards [ratio_uniform_growing (5*PRZZAsymptotic.R/4) PRZZAsymptotic.theta
    witness_size eps heps] with L hL
  intro g p hg hcut hp
  exact hL g p.1 p.2 hg hcut (ShiftedMobius.twoBidiscs_norm p hp).1
    (ShiftedMobius.twoBidiscs_norm p hp).2

theorem averageError_twoBidiscs_uniform :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => averageError L PRZZAsymptotic.theta p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs := by
  apply (averageError_uniform (5*PRZZAsymptotic.R/4) PRZZAsymptotic.theta
    (by norm_num [PRZZAsymptotic.theta]) witness_size).mono
  intro p hp
  exact ShiftedMobius.twoBidiscs_norm p hp

#print axioms tested_weight_error_bound
#print axioms averageError_bound
#print axioms averageError_uniform
#print axioms ratio_twoBidiscs_uniform
#print axioms averageError_twoBidiscs_uniform
#print axioms prime_log_sum_le
#print axioms ratio_bound
#print axioms outerWeight_factor
#print axioms outerWeight_error
#print axioms ratio_uniform_growing
end XiPrime8845.ShiftedEulerUniform

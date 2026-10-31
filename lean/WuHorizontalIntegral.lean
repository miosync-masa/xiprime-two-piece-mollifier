/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license; see licenses/AF-Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
-/
import WuDiskGrowth
import Zeta23.XiPrime.ZeroCount.Generic

/-! Explicit horizontal phase estimate from finite partial fractions.
Adapted from AF Zeta23.XiPrime.ZeroCount.horizontal_bound_two_line,
with separate zero-mass and remainder bounds and arbitrary endpoints. -/
noncomputable section
open scoped BigOperators
open Complex Set Metric MeasureTheory intervalIntegral
namespace XiPrime8845.WuHorizontalIntegral
open Zeta23.XiPrime.ZeroCount
set_option maxHeartbeats 2000000

theorem horizontal_of_partial_fraction (f : ℂ → ℂ) (a b T N M : ℝ) (Z : Finset ℂ)
    (hab : a ≤ b)
    (hf : ∀ σ ∈ Icc a b, AnalyticAt ℂ f ((σ:ℂ)+T*I))
    (hn : ∀ σ ∈ Icc a b, f ((σ:ℂ)+T*I) ≠ 0)
    (hZoff : ∀ ρ ∈ Z, ∀ σ ∈ Icc a b, (σ:ℂ)+T*I ≠ ρ)
    (hcount : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ:ℝ) ≤ N)
    (hpf : ∀ σ ∈ Icc a b,
      ‖logDeriv f ((σ:ℂ)+T*I)-
        ∑ ρ ∈ Z, (analyticOrderNatAt f ρ:ℂ)/((σ:ℂ)+T*I-ρ)‖ ≤ M) :
    |(∫ σ in a..b, logDeriv f ((σ:ℂ)+T*I)).im| ≤ Real.pi*N+(b-a)*M := by
  have hZoff' : ∀ ρ ∈ Z, ∀ σ ∈ uIcc a b, (σ:ℂ)+T*I ≠ ρ := by
    rw [uIcc_of_le hab]; exact hZoff
  set PF : ℝ → ℂ := fun σ => ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) + T * I - ρ) with hPF
  set E : ℝ → ℂ := fun σ => logDeriv f ((σ : ℂ) + T * I) - PF σ with hE
  have hEbound : ∀ σ ∈ Set.uIoc a b, ‖E σ‖ ≤ M := by
    intro σ hσ
    have hσ' : σ ∈ Icc a b := by
      rw [uIoc_of_le hab] at hσ
      exact ⟨hσ.1.le, hσ.2⟩
    exact hpf σ hσ'
  -- continuity / integrability
  have hcontLD : ContinuousOn (fun σ : ℝ => logDeriv f ((σ : ℂ) + T * I)) (uIcc a b) := by
    intro σ hσ
    rw [uIcc_of_le hab] at hσ
    have ha := hf σ hσ
    have hY := hn σ hσ
    have hc : ContinuousAt (logDeriv f) ((σ : ℂ) + T * I) := by
      have := (ha.deriv.continuousAt).div ha.continuousAt hY
      simpa only [logDeriv] using this
    exact (hc.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)).continuousWithinAt
  have hintLD : IntervalIntegrable (fun σ : ℝ => logDeriv f ((σ : ℂ) + T * I)) volume a b :=
    hcontLD.intervalIntegrable
  have hintTerm : ∀ ρ ∈ Z, IntervalIntegrable
      (fun σ : ℝ => (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) + T * I - ρ)) volume a b := by
    intro ρ hρ
    have := (intervalIntegrable_inv_sub (hZoff' ρ hρ)).const_mul (analyticOrderNatAt f ρ : ℂ)
    exact this.congr fun σ _ => by simp [div_eq_mul_inv]
  have hintPF : IntervalIntegrable PF volume a b := by
    have := IntervalIntegrable.sum Z hintTerm
    exact this.congr fun σ _ => by simp [hPF, Finset.sum_apply]
  have hintE : IntervalIntegrable E volume a b := hintLD.sub hintPF
  -- split the integral
  have hsplit : (∫ σ in a..b, logDeriv f ((σ : ℂ) + T * I))
      = (∫ σ in a..b, PF σ) + ∫ σ in a..b, E σ := by
    rw [← integral_add hintPF hintE]
    apply integral_congr
    intro σ _
    simp [hE]
  -- the partial-fraction part: Im = Σ m_ρ · Im ∫ (s−ρ)⁻¹, each |·| ≤ π
  have hPFint : (∫ σ in a..b, PF σ)
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * ∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹ := by
    simp only [hPF]
    rw [integral_finsetSum hintTerm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    simp only [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have hPFim : |(∫ σ in a..b, PF σ).im| ≤ Real.pi * N := by
    rw [hPFint, Complex.im_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ ρ ∈ Z, |((analyticOrderNatAt f ρ : ℂ)
        * ∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im|
        ≤ (analyticOrderNatAt f ρ : ℝ) * Real.pi := by
      intro ρ hρ
      have him : ((analyticOrderNatAt f ρ : ℂ) * ∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im
          = (analyticOrderNatAt f ρ : ℝ) * (∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im := by
        rw [Complex.mul_im]; simp
      rw [him, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (abs_im_integral_inv_sub_le_pi hab T ρ (hZoff ρ hρ)) (Nat.cast_nonneg _)
    calc ∑ ρ ∈ Z, |((analyticOrderNatAt f ρ : ℂ)
            * ∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im|
        ≤ ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) * Real.pi := Finset.sum_le_sum hterm
      _ = Real.pi * ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ Real.pi * N := mul_le_mul_of_nonneg_left hcount Real.pi_pos.le
  -- the remainder part
  have hEim : |(∫ σ in a..b, E σ).im| ≤ (b-a)*M := by
    refine (Complex.abs_im_le_norm _).trans ?_
    have := intervalIntegral.norm_integral_le_of_norm_le_const hEbound
    calc ‖∫ σ in a..b, E σ‖ ≤ M * |b-a| := this
      _ = (b-a)*M := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; ring
  rw [hsplit, Complex.add_im]
  calc |(∫ σ in a..b, PF σ).im + (∫ σ in a..b, E σ).im|
      ≤ |(∫ σ in a..b, PF σ).im| + |(∫ σ in a..b, E σ).im| := abs_add_le _ _
    _ ≤ Real.pi * N + (b-a)*M := add_le_add hPFim hEim

#print axioms horizontal_of_partial_fraction
end XiPrime8845.WuHorizontalIntegral


import TotientSummability

/-! The squarefree reciprocal-totient harmonic main term with bounded error. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.TotientHarmonic
open TotientConvolution TotientSummability
set_option maxHeartbeats 1000000

def summatory (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ)^2/n.totient
def errorConstant : ℝ :=
  (6+|Real.eulerMascheroniConstant|)*(∑' n, powerMass n)

theorem harmonic_kernel_bound (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : 0 < n) :
    |MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x| ≤
      2+|Real.eulerMascheroniConstant|+Real.log n := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  by_cases hnx : (n:ℝ) ≤ x
  · have hratio : 1 ≤ x/n := (one_le_div hn0).mpr hnx
    have h := MobiusHarmonic.harmonicError_bound (x/n) hratio
    have hb : 2/(x/n) ≤ 2 := (div_le_self (by norm_num) hratio)
    have he : MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x =
        MobiusHarmonic.harmonicError (x/n) + Real.eulerMascheroniConstant - Real.log n := by
      unfold MobiusHarmonic.harmonicError
      rw [Real.log_div (by linarith : x ≠ 0) hn0.ne']
      ring
    rw [he]
    have ht := abs_sub (MobiusHarmonic.harmonicError (x/n)+Real.eulerMascheroniConstant) (Real.log n)
    have ht' := abs_add_le (MobiusHarmonic.harmonicError (x/n)) Real.eulerMascheroniConstant
    rw [abs_of_nonneg hln] at ht
    linarith
  · have hfloor : ⌊x/n⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hn0).mpr (lt_of_not_ge hnx))
    rw [hfloor]
    simp only [MobiusHarmonic.harmonic, Finset.Ioc_self, Finset.sum_empty, zero_sub, abs_neg,
      abs_of_nonneg (Real.log_nonneg hx)]
    have hlog := Real.log_le_log (by linarith : 0 < x) (le_of_not_ge hnx)
    linarith [abs_nonneg Real.eulerMascheroniConstant]

theorem correction_kernel_bound (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    |correction n * (MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x)| ≤
      (6+|Real.eulerMascheroniConstant|)*powerMass n := by
  by_cases hn : n = 0
  · simp [hn, powerMass]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hp : 1 ≤ (n:ℝ)^(1/4:ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hl := Real.log_natCast_le_rpow_div n (by norm_num : (0:ℝ)<1/4)
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_left (harmonic_kernel_bound x hx n (Nat.pos_of_ne_zero hn))
    (abs_nonneg (correction n))).trans
  unfold powerMass
  have he : 2+|Real.eulerMascheroniConstant|+Real.log n ≤
      (6+|Real.eulerMascheroniConstant|)*(n:ℝ)^(1/4:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2+|Real.eulerMascheroniConstant| by positivity)
    norm_num at hl
    nlinarith
  have hh := mul_le_mul_of_nonneg_left he (abs_nonneg (correction n))
  nlinarith [hh]

theorem summatory_eq_tsum (x : ℝ) :
    summatory x = ∑' n, correction n * MobiusHarmonic.harmonic ⌊x/n⌋₊ := by
  rw [tsum_eq_sum (s := Ioc 0 ⌊x⌋₊)]
  · simp only [Nat.floor_div_natCast]
    exact harmonic_representation ⌊x⌋₊
  · intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have hnx : ⌊x⌋₊ < n := by
      have hnpos := Nat.pos_of_ne_zero hn0
      simp only [mem_Ioc, not_and] at hn
      exact Nat.lt_of_not_ge (hn hnpos)
    rw [Nat.floor_div_natCast, Nat.div_eq_of_lt hnx]
    simp [MobiusHarmonic.harmonic]

theorem summatory_log_bound (x : ℝ) (hx : 1 ≤ x) :
    |summatory x - Real.log x| ≤ errorConstant := by
  have hmajor := powerMass_summable.mul_left (6+|Real.eulerMascheroniConstant|)
  have herr : Summable (fun n => correction n *
      (MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x)) :=
    hmajor.of_norm_bounded (by intro n; simpa only [Real.norm_eq_abs] using correction_kernel_bound x hx n)
  have hc0 : Summable (fun n => correction n) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using correction_abs_summable)
  have hc : Summable (fun n => correction n * Real.log x) := hc0.mul_right _
  have he : summatory x - Real.log x =
      ∑' n, correction n * (MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x) := by
    have h := herr.tsum_add hc
    simp only [← mul_add, sub_add_cancel] at h
    rw [← summatory_eq_tsum, tsum_mul_right, correction_mass_one, one_mul] at h
    linarith
  rw [he]
  calc
    _ ≤ ∑' n, |correction n * (MobiusHarmonic.harmonic ⌊x/n⌋₊ - Real.log x)| :=
      (norm_tsum_le_tsum_norm herr.norm)
    _ ≤ ∑' n, (6+|Real.eulerMascheroniConstant|)*powerMass n :=
      Summable.tsum_le_tsum (correction_kernel_bound x hx) herr.abs hmajor
    _ = errorConstant := by rw [tsum_mul_left]; rfl

theorem errorConstant_nonneg : 0 ≤ errorConstant := by
  unfold errorConstant
  exact mul_nonneg (by positivity) (tsum_nonneg powerMass_nonneg)

theorem normalized_bound (L u : ℝ) (hL : 0 < L) (hu : 0 ≤ u) :
    |summatory (Real.exp (L*u))/L-u| ≤ errorConstant/L := by
  have h := summatory_log_bound (Real.exp (L*u))
    (Real.one_le_exp_iff.mpr (mul_nonneg hL.le hu))
  rw [Real.log_exp] at h
  have he : summatory (Real.exp (L*u))/L-u =
      (summatory (Real.exp (L*u))-L*u)/L := by field_simp
  rw [he, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right h hL.le

open Filter Topology in
/-- Uniform on the entire nonnegative logarithmic axis, including u=0. -/
theorem normalized_uniform :
    TendstoUniformlyOn (fun (L : ℝ) u => summatory (Real.exp (L*u))/L)
      (fun u => u) atTop (Set.Ici 0) := by
  have h : Tendsto (fun L : ℝ => errorConstant/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul errorConstant
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ), h.eventually (gt_mem_nhds heps)] with L hL he
  intro u hu
  rw [dist_comm, Real.dist_eq]
  exact (normalized_bound L u hL hu).trans_lt he

#print axioms summatory_log_bound
#print axioms normalized_uniform
end XiPrime8845.TotientHarmonic

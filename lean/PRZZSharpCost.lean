import PRZZSharpCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Logarithmic L1 cost of the exact sharp-comparison kernel. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace XiPrime8845.PRZZSharpCost
open PRZZSharpCutoff
set_option maxHeartbeats 2000000

def density (F : ℕ) (x : ℝ) : ℝ := ‖kernel F (x : PRZZSharpCutoff.Circle)‖

theorem density_continuous (F : ℕ) : Continuous (density F) :=
  ((kernel_continuous F).comp (AddCircle.continuous_mk' (1:ℝ))).norm

theorem density_even (F : ℕ) (x : ℝ) : density F (-x) = density F x := by
  have h (k : ℤ) : fourier k ((-x : ℝ) : PRZZSharpCutoff.Circle) =
      starRingEnd ℂ (fourier k (x : PRZZSharpCutoff.Circle)) := by
    rw [fourier_coe_apply,fourier_coe_apply,← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  unfold density kernel
  simp_rw [h,← map_sum]
  exact Complex.norm_conj _

theorem denominator_lower (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    4*x ≤ ‖fourier (-1) (x : PRZZSharpCutoff.Circle)-1‖ := by
  rw [fourier_coe_apply]
  norm_num only [Int.cast_neg,Int.cast_one,Complex.ofReal_one]
  have he : (2*(Real.pi:ℂ)*Complex.I*(-1)*(x:ℂ)/1) =
      Complex.I*((-2*Real.pi*x:ℝ):ℂ) := by push_cast; ring
  rw [he,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs := Real.mul_le_sin (show 0 ≤ Real.pi*x by positivity)
    (show Real.pi*x ≤ Real.pi/2 by nlinarith [Real.pi_pos])
  have hs' : 2*x ≤ Real.sin (Real.pi*x) := by
    convert hs using 1
    field_simp
  rw [show -2*Real.pi*x/2 = -(Real.pi*x) by ring,Real.sin_neg,
    Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    abs_of_nonneg (by linarith : 0 ≤ Real.sin (Real.pi*x))]
  linarith

theorem density_inv_bound (F : ℕ) (x : ℝ) (hx : 0 < x) (hx' : x ≤ 1/2) :
    density F x ≤ x⁻¹ := by
  have hd := kernel_decay F (x : PRZZSharpCutoff.Circle)
  have hl := mul_le_mul_of_nonneg_left (denominator_lower x hx.le hx')
    (norm_nonneg (kernel F (x : PRZZSharpCutoff.Circle)))
  rw [← one_div]
  apply (le_div_iff₀ hx).mpr
  dsimp [density] at *
  nlinarith [norm_nonneg (kernel F (x : PRZZSharpCutoff.Circle))]

theorem cost_interval (F : ℕ) :
    cost F = ∫ x in (-1/2:ℝ)..(1/2:ℝ), density F x := by
  rw [cost,AddCircle.integral_haarAddCircle]
  simp only [inv_one,one_smul]
  have h := AddCircle.intervalIntegral_preimage (1:ℝ) (-1/2)
    (fun t => ‖kernel F t‖)
  norm_num only [show (-1/2:ℝ)+1=1/2 by norm_num] at h
  simpa only [density,neg_div] using h.symm

theorem cost_half (F : ℕ) : cost F = 2*(∫ x in (0:ℝ)..(1/2:ℝ), density F x) := by
  have hi (a b : ℝ) : IntervalIntegrable (density F) volume a b :=
    (density_continuous F).intervalIntegrable a b
  have hs := intervalIntegral.integral_comp_neg (density F) (a := (0:ℝ)) (b := (1/2:ℝ))
  simp only [density_even,neg_zero,← neg_div] at hs
  rw [cost_interval,← intervalIntegral.integral_add_adjacent_intervals (hi (-1/2) 0) (hi 0 (1/2)),← hs]
  ring

/-- Logarithmic, not linear, loss in the factor-box size. -/
theorem cost_log (F : ℕ) : cost F ≤ 1+2*Real.log ((F:ℝ)+1) := by
  let M : ℝ := (F:ℝ)+1
  let a : ℝ := 1/(2*M)
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α := ℝ) F]
  have ha : 0 < a := by dsimp [a]; positivity
  have hah : a ≤ 1/2 := by
    dsimp [a]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*M) (by norm_num : (0:ℝ)<2)).mpr
    linarith
  have hi (a b : ℝ) : IntervalIntegrable (density F) volume a b :=
    (density_continuous F).intervalIntegrable a b
  have hfirst : (∫ x in (0:ℝ)..a, density F x) ≤ 1/2 := by
    calc
      _ ≤ ∫ _ in (0:ℝ)..a, M := intervalIntegral.integral_mono_on ha.le (hi _ _)
        intervalIntegrable_const (fun x _ => kernel_norm_le F (x : PRZZSharpCutoff.Circle))
      _ = _ := by rw [intervalIntegral.integral_const]; dsimp [a]; field_simp; ring
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a (1/2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro x hx
    rw [uIcc_of_le hah] at hx
    exact (ha.trans_le hx.1).ne'
  have hlast : (∫ x in a..(1/2:ℝ), density F x) ≤ Real.log M := by
    calc
      _ ≤ ∫ x in a..(1/2:ℝ), x⁻¹ := intervalIntegral.integral_mono_on hah (hi _ _) hinv
        (fun x hx => density_inv_bound F x (ha.trans_le hx.1) hx.2)
      _ = _ := by
        rw [integral_inv_of_pos ha (by norm_num)]
        congr 1
        dsimp [a]
        field_simp
  rw [cost_half,← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a (1/2))]
  dsimp only [M] at hlast
  linarith

#print axioms density_even
#print axioms denominator_lower
#print axioms density_inv_bound
#print axioms cost_interval
#print axioms cost_half
#print axioms cost_log
end XiPrime8845.PRZZSharpCost

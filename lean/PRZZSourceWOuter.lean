import PRZZSourceW
import PRZZGAbsorption

/-! Actual source-weight suppliers for the dyadic outer mass. Constants
precede height, shifts and scales. The arithmetic signedSum estimate is
not supplied by these analytic bounds. -/
noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace XiPrime8845.PRZZSourceWOuter
open PRZZSourceW PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

theorem tail_continuous : Continuous tail := by
  have hi : Integrable (fun u : ℝ => Real.exp (-u^2/4)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4) using 1
    funext u
    congr 1
    ring
  have hc : Continuous (fun u : ℝ => Real.exp (-u^2/4)) := by fun_prop
  have he (l : ℝ) : tail l = tail 0-(∫ u in (0:ℝ)..l, Real.exp (-u^2/4)) := by
    have hh := intervalIntegral.integral_interval_add_Ioi
      (hi.integrableOn (s := Ioi (0:ℝ))) (hi.integrableOn (s := Ioi l))
    change (∫ u in (0:ℝ)..l, Real.exp (-u^2/4))+tail l = tail 0 at hh
    linarith
  rw [show tail = (fun l => tail 0-(∫ u in (0:ℝ)..l, Real.exp (-u^2/4))) from funext he]
  apply continuous_const.sub
  exact continuous_iff_continuousAt.mpr (fun l =>
    (hc.integral_hasStrictDerivAt 0 l).hasDerivAt.continuousAt)

theorem sourceW_continuous (sigma : ℂ) (hs : sigma ≠ 0) :
    ContinuousOn (sourceW sigma) (Ioi 0) := by
  have hl : ContinuousOn Real.log (Ioi (0:ℝ)) := Real.continuousOn_log.mono
    (fun x hx => ne_of_gt hx)
  have ht := tail_continuous.comp_continuousOn hl
  apply ContinuousOn.congr _ (fun x hx => sourceW_eq sigma hs x hx)
  exact ((Complex.continuous_ofReal.comp_continuousOn ht).div_const _).sub
    ((Complex.continuous_ofReal.comp_continuousOn
      (hl.mul (Real.continuous_exp.comp_continuousOn ((hl.pow 2).neg.div_const 4)))).div_const _)

theorem actual_mass (d : ℕ) (T M X V K S r : ℝ) (A B : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hL : 1 ≤ Real.log T) (hK : 0 ≤ K) (hS : 0 ≤ S) (hr : 0 < r)
    (hsep : r ≤ ‖A+B‖)
    (hscale : |Real.log M|+|Real.log V| ≤ K*Real.log T)
    (hz : |(((A+B)/(Real.log T:ℂ))).re| ≤ S/Real.log T) :
    (∫ p, ‖common d T M X V (sourceW ((A+B)/(Real.log T:ℂ)))
      ((A+B)/(Real.log T:ℂ)) p‖) ≤
      24*((1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*
        Real.exp ((K+Real.log 4)*S))*T/((d:ℝ)*X*V) := by
  have hL0 : 0 < Real.log T := by linarith
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL0.ne')
  exact common_mass d T M X V K S _ _ _ hd hT hM hX hV hL hK hS (by positivity)
    hscale hz (sourceW_continuous _ hs)
    (fun x hx => sourceW_scaled_bound A B (Real.log T) r x hL0 hr hsep hx)

/-- Any fixed additional logarithmic power is absorbed with the W cost.
No exponent is silently spent: eps is the explicit allocated slack. -/
theorem envelope_absorbed (m : ℕ) (r eps : ℝ) (hr : 0 < r) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      (1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*(Real.log T)^m ≤ C*T^eps := by
  obtain ⟨C,hC,h⟩ := PRZZGAbsorption.log_pow_bound (m+2) eps heps
  refine ⟨(1+2/(Real.sqrt Real.pi*r^2))*C,by positivity,?_⟩
  intro T hT hL
  have hsq : 1 ≤ (Real.log T)^2 := by nlinarith
  have hp : 0 ≤ (Real.log T)^m := pow_nonneg (by linarith) _
  calc
    _ ≤ ((1+2/(Real.sqrt Real.pi*r^2))*(Real.log T)^2)*(Real.log T)^m := by
      apply mul_le_mul_of_nonneg_right _ hp
      calc
        _ = 1+(2/(Real.sqrt Real.pi*r^2))*(Real.log T)^2 := by ring
        _ ≤ (Real.log T)^2+(2/(Real.sqrt Real.pi*r^2))*(Real.log T)^2 :=
          add_le_add hsq le_rfl
        _ = _ := by ring
    _ = (1+2/(Real.sqrt Real.pi*r^2))*(Real.log T)^(m+2) := by rw [pow_add]; ring
    _ ≤ (1+2/(Real.sqrt Real.pi*r^2))*(C*T^eps) :=
      mul_le_mul_of_nonneg_left (h T hT) (by positivity)
    _ = _ := by ring

/-- The actual outer mass, including all fixed logarithmic losses, has a
single constant chosen before height, shifts, d and the dyadic scales. -/
theorem actual_mass_absorbed (m : ℕ) (K S r eps : ℝ)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (T M X V : ℝ) (A B : ℂ),
      0 < d → 1 ≤ T → 0 < M → 0 < X → 0 < V → 1 ≤ Real.log T →
      r ≤ ‖A+B‖ → |Real.log M|+|Real.log V| ≤ K*Real.log T →
      |(((A+B)/(Real.log T:ℂ))).re| ≤ S/Real.log T →
      (∫ p, ‖common d T M X V (sourceW ((A+B)/(Real.log T:ℂ)))
        ((A+B)/(Real.log T:ℂ)) p‖)*(Real.log T)^m ≤
        C*T^eps*T/((d:ℝ)*X*V) := by
  obtain ⟨C,hC,h⟩ := envelope_absorbed m r eps hr heps
  refine ⟨24*Real.exp ((K+Real.log 4)*S)*C,by positivity,?_⟩
  intro d T M X V A B hd hT hM hX hV hL hsep hscale hz
  have hT0 : 0 < T := by linarith
  have hm := actual_mass d T M X V K S r A B hd hT0 hM hX hV hL hK hS hr hsep hscale hz
  have hp : 0 ≤ (Real.log T)^m := pow_nonneg (by linarith) _
  calc
    _ ≤ (24*((1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*
        Real.exp ((K+Real.log 4)*S))*T/((d:ℝ)*X*V))*(Real.log T)^m :=
      mul_le_mul_of_nonneg_right hm hp
    _ = ((1+2*(Real.log T)^2/(Real.sqrt Real.pi*r^2))*(Real.log T)^m)*
        (24*Real.exp ((K+Real.log 4)*S)*T/((d:ℝ)*X*V)) := by ring
    _ ≤ (C*T^eps)*(24*Real.exp ((K+Real.log 4)*S)*T/((d:ℝ)*X*V)) :=
      mul_le_mul_of_nonneg_right (h T hT hL) (by positivity)
    _ = _ := by ring

/-- Retaining an additional original cutoff window cannot increase the
outer norm mass. This applies in particular to the window intersection
in PRZZWindowComposition.literal_windowed_nu. -/
theorem restricted_mass (d : ℕ) (T M X V : ℝ) (sigma z : ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hX : 0 < X) (hV : 0 < V)
    (hsigma : sigma ≠ 0) (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    (∫ p, ‖s.indicator (common d T M X V (sourceW sigma) z) p‖) ≤
      ∫ p, ‖common d T M X V (sourceW sigma) z p‖ := by
  have hi := common_integrable d T M X V (sourceW sigma) z hd hT hM hX hV
    (sourceW_continuous sigma hsigma)
  apply integral_mono (hi.indicator hs).norm hi.norm
  intro p
  by_cases hp : p ∈ s
  · simp [hp]
  · simp [hp]

#print axioms tail_continuous
#print axioms sourceW_continuous
#print axioms actual_mass
#print axioms envelope_absorbed
#print axioms actual_mass_absorbed
#print axioms restricted_mass
end XiPrime8845.PRZZSourceWOuter

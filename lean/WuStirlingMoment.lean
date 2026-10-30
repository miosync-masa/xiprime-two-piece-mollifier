import WuStirlingTransfer

/-! Smoothed L2 cost of the actual Stirling replacement. The fixed smooth
weight is retained. Only the bounded derivative moments use PRZZ. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset MeasureTheory
namespace XiPrime8845.WuStirlingMoment
open WuAuxiliary WuStirling WuStirlingTransfer ZetaMomentIntegral
set_option maxHeartbeats 2000000

def errorMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t : ℝ, ‖(V T (leftPoint T t)-U T (leftPoint T t))*psi T (leftPoint T t)‖^2*
    Phi (t/T))/T

theorem weight_support (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (T : ℝ) (hT : 0 < T) (t : ℝ) (ht : Phi (t/T) ≠ 0) :
    t ∈ Set.Icc T (2*T) := by
  have hh := hPhi.2 (Function.mem_support.mpr ht)
  exact ⟨by have := (le_div_iff₀ hT).mp hh.1; linarith,
    by have := (div_le_iff₀ hT).mp hh.2; linarith⟩

theorem weighted_integrable (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc T (2*T))) :
    Integrable (fun t => ‖f t‖^2*Phi (t/T)) := by
  apply (integrableOn_iff_integrable_of_support_subset (s:=Set.Icc T (2*T)) ?_).mp
  · exact ((hf.norm.pow 2).mul
      ((hPhi.1.continuous.comp (continuous_id.div_const T)).continuousOn)).integrableOn_compact isCompact_Icc
  · intro t ht
    apply weight_support Phi hPhi T hT t
    intro hz
    exact ht (by simp [hz])

theorem derivative_integrable (k : ℕ) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun t => ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T)) := by
  apply weighted_integrable Phi hPhi T hT
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
  have hreg : ContinuousOn (iteratedDeriv k riemannZeta) {(1:ℂ)}ᶜ := by
    rw [iteratedDeriv_eq_iterate]
    exact (analyticOn_riemannZeta.iterated_deriv k).continuousOn
  exact (hreg.comp hp.continuousOn (by
    intro t ht
    change leftPoint T t ≠ 1
    intro hh
    have hh' := congrArg Complex.im hh
    simp [leftPoint] at hh'
    linarith [ht.1])).div_const _

theorem error_integrable (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (T : ℝ) (hT : 4 ≤ T)
    (hs : (1/2-PRZZAsymptotic.R/Real.log T) ∈ Set.Icc (7/16) 3) :
    Integrable (fun t => ‖(V T (leftPoint T t)-U T (leftPoint T t))*
      psi T (leftPoint T t)‖^2*Phi (t/T)) := by
  apply weighted_integrable Phi hPhi T (by linarith)
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hz (t : ℝ) (ht : t ∈ Set.Icc T (2*T)) :
      0 < (leftPoint T t).re ∧ leftPoint T t ≠ 1 := by
    constructor
    · simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
      linarith [hs.1]
    · intro he
      have hh := congrArg Complex.im he
      simp [leftPoint] at hh
      linarith [ht.1]
  have hV : ContinuousOn (fun t => V T (leftPoint T t)) (Set.Icc T (2*T)) := by
    intro t ht
    exact (((eta_entire (Real.log T) _).continuousAt.div
      (H_analytic _ (hz t ht).1).continuousAt (H_ne_zero _ (hz t ht).1 (hz t ht).2)).comp
      hp.continuousAt).continuousWithinAt
  have hU : ContinuousOn (fun t => U T (leftPoint T t)) (Set.Icc T (2*T)) := by
    unfold U ZetaMomentPolynomial.differentialPolynomial
    apply continuousOn_finsetSum
    intro k hk
    have hreg : ContinuousOn (iteratedDeriv k riemannZeta) {(1:ℂ)}ᶜ := by
      rw [iteratedDeriv_eq_iterate]
      exact (analyticOn_riemannZeta.iterated_deriv k).continuousOn
    exact continuousOn_const.mul
      ((hreg.comp hp.continuousOn (fun t ht => (hz t ht).2)).div_const _)
  exact (hV.sub hU).mul ((psi_entire T).continuous.comp hp).continuousOn

theorem square_error_bound (T t : ℝ)
    (hh : ‖V T (leftPoint T t)-U T (leftPoint T t)‖ ≤
      (transferConstant/Real.log T)*∑ k ∈ range 7, ‖scaledZeta k T (leftPoint T t)‖) :
    ‖(V T (leftPoint T t)-U T (leftPoint T t))*psi T (leftPoint T t)‖^2 ≤
      7*(transferConstant/Real.log T)^2*
        ∑ k ∈ range 7, ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖^2 := by
  have h := mul_le_mul_of_nonneg_right hh (norm_nonneg (psi T (leftPoint T t)))
  have he : ‖(V T (leftPoint T t)-U T (leftPoint T t))*psi T (leftPoint T t)‖ ≤
      (transferConstant/Real.log T)*∑ k ∈ range 7, ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖ := by
    simpa only [norm_mul,sum_mul,mul_assoc] using h
  have hp := pow_le_pow_left₀ (norm_nonneg _) he 2
  have hc := sum_mul_sq_le_sq_mul_sq (range 7)
    (fun k => ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,card_range,nsmul_eq_mul] at hc
  rw [mul_pow] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by ring))

theorem errorMoment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ errorMoment Phi T ∧
      errorMoment Phi T ≤ 7*(transferConstant/Real.log T)^2*
        ∑ k ∈ range 7, derivativeMoment k Phi T := by
  filter_upwards [difference_left_bound,leftPoint_strip] with T hb hstrip
  have hT : 0 < T := by linarith [hstrip.1]
  refine ⟨div_nonneg (integral_nonneg (fun t => mul_nonneg (sq_nonneg _) (hPhi0 _))) hT.le,?_⟩
  have hi := integral_mono
    (error_integrable Phi hPhi T hstrip.1 hstrip.2.2)
    ((integrable_finsetSum (range 7) (fun k _ => derivative_integrable k Phi hPhi T hT)).const_mul
      (7*(transferConstant/Real.log T)^2)) (fun t => ?_)
  · apply (div_le_div_of_nonneg_right hi hT.le).trans_eq
    rw [integral_const_mul,integral_finsetSum (range 7) (fun k _ => derivative_integrable k Phi hPhi T hT)]
    simp only [derivativeMoment,sum_div,mul_div_assoc]
  · by_cases hz : Phi (t/T) = 0
    · simp [hz]
    · have ht := weight_support Phi hPhi T hT t hz
      have hh := mul_le_mul_of_nonneg_right (square_error_bound T t (hb t ht)) (hPhi0 (t/T))
      simpa only [sum_mul,mul_assoc] using hh

/-- The actual replacement costs O((log T)^-2) for each fixed nonnegative
smooth weight. This is not removal of smoothing. -/
theorem errorMoment_rate (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      0 ≤ errorMoment Phi T ∧ errorMoment Phi T ≤ C/(Real.log T)^2 := by
  obtain ⟨C,hC,hb⟩ := derivativeMoments_bounded Phi hPhi
  refine ⟨49*transferConstant^2*C,by positivity,?_⟩
  filter_upwards [errorMoment_bound Phi hPhi hPhi0,hb] with T hT hder
  refine ⟨hT.1,hT.2.trans ?_⟩
  have hs : (∑ k ∈ range 7, derivativeMoment k Phi T) ≤ 7*C := by
    calc
      _ ≤ ∑ k ∈ range 7, C := sum_le_sum (fun k hk =>
        (le_abs_self _).trans (hder k (by have := mem_range.mp hk; omega)))
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

theorem errorMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    Tendsto (errorMoment Phi) atTop (nhds 0) := by
  obtain ⟨C,hC,h⟩ := errorMoment_rate Phi hPhi hPhi0
  have ht : Tendsto (fun T : ℝ => C/(Real.log T)^2) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,mul_zero] using
      ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).pow 2).const_mul C
  exact squeeze_zero' (h.mono (fun _ h => h.1)) (h.mono (fun _ h => h.2)) ht

#print axioms weight_support
#print axioms weighted_integrable
#print axioms derivative_integrable
#print axioms error_integrable
#print axioms square_error_bound
#print axioms errorMoment_bound
#print axioms errorMoment_rate
#print axioms errorMoment_tendsto
end XiPrime8845.WuStirlingMoment


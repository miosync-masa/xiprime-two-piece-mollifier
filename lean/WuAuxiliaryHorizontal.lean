import WuHorizontalBound

/-! Horizontal phase for eta_T psi_T itself. The real leading logarithm
of H contributes no imaginary part; its horizontal phase is bounded by a
height-independent constant. No branch of arg is fixed in this theorem. -/
noncomputable section
open Filter Topology Set Complex MeasureTheory
namespace XiPrime8845.WuAuxiliaryHorizontal
open WuAuxiliary WuAuxiliaryBoundary WuStirling WuLittlewood WuHorizontalBound
set_option maxHeartbeats 2000000

theorem logDeriv_factor (T : ℝ) (s : ℂ) (hr : 0 < s.re) (hs : s ≠ 1)
    (hn : auxiliary T s ≠ 0) :
    logDeriv (auxiliary T) s = Zeta23.XiPrime.Lfn s+
      logDeriv (fun z => V T z*psi T z) s := by
  have he : (fun z => auxiliary T z/H z) = (fun z => V T z*psi T z) := by
    funext z
    unfold auxiliary V
    ring
  have hh := logDeriv_div s hn (H_ne_zero s hr hs)
    ((auxiliary_entire T).differentiableAt) ((H_analytic s hr).differentiableAt)
  rw [he,show logDeriv H s = Zeta23.XiPrime.Lfn s from H_logDeriv s hr hs] at hh
  linear_combination -hh

theorem logDeriv_integrable (f : ℂ → ℂ) (a b t : ℝ) (hab : a ≤ b)
    (ha : ∀ σ ∈ Icc a b, AnalyticAt ℂ f (point σ t))
    (hn : ∀ σ ∈ Icc a b, f (point σ t) ≠ 0) :
    IntervalIntegrable (fun σ => logDeriv f (point σ t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro σ hσ
  rw [uIcc_of_le hab] at hσ
  have hc : ContinuousAt (logDeriv f) (point σ t) :=
    ((ha σ hσ).deriv.continuousAt).div (ha σ hσ).continuousAt (hn σ hσ)
  exact (hc.comp (f := fun σ : ℝ => point σ t)
    (show ContinuousAt (fun σ : ℝ => point σ t) σ by unfold point; fun_prop)).continuousWithinAt

theorem auxiliary_horizontal_safe : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    t ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    ∀ a b : ℝ, 7/16 ≤ a → a ≤ b → b ≤ 3 →
    |(∫ σ in a..b, logDeriv (auxiliary T) (point σ t)).im| ≤
      (phaseConstant+3*firstConstant)*Real.log T := by
  filter_upwards [horizontal_safe,eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hh hT hL
  intro t ht hsafe a b ha hab hb
  have hn (σ : ℝ) : auxiliary T (point σ t) ≠ 0 :=
    WuSafeEndpoints.horizontal_nonzero _ t hsafe σ
  have hr (σ : ℝ) (hσ : σ ∈ Icc a b) : 0 < (point σ t).re := by
    simp [point]; linarith [hσ.1]
  have hne (σ : ℝ) : point σ t ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp [point] at hi
    linarith [ht.1]
  have hiH := logDeriv_integrable H a b t hab
    (fun σ hσ => H_analytic _ (hr σ hσ)) (fun σ hσ => H_ne_zero _ (hr σ hσ) (hne σ))
  have hiA := logDeriv_integrable (auxiliary T) a b t hab
    (fun σ _ => (auxiliary_entire T).analyticAt _) (fun σ _ => hn σ)
  have he (σ : ℝ) (hσ : σ ∈ Icc a b) : logDeriv (auxiliary T) (point σ t) =
      logDeriv H (point σ t)+logDeriv (fun z => V T z*psi T z) (point σ t) := by
    rw [show logDeriv H (point σ t) = Zeta23.XiPrime.Lfn (point σ t) from
      H_logDeriv _ (hr σ hσ) (hne σ)]
    exact logDeriv_factor T _ (hr σ hσ) (hne σ) (hn σ)
  have hiP : IntervalIntegrable (fun σ => logDeriv (fun z => V T z*psi T z) (point σ t)) volume a b :=
    (hiA.sub hiH).congr (fun σ hσ => by
      rw [uIoc_of_le hab] at hσ
      have hx := he σ ⟨hσ.1.le,hσ.2⟩
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx))
  have hsplit : (∫ σ in a..b, logDeriv (auxiliary T) (point σ t)) =
      (∫ σ in a..b, logDeriv H (point σ t))+
        ∫ σ in a..b, logDeriv (fun z => V T z*psi T z) (point σ t) := by
    rw [← intervalIntegral.integral_add hiH hiP]
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hab] at hσ
    exact he σ hσ
  have him : |(∫ σ in a..b, logDeriv H (point σ t)).im| ≤ firstConstant*(b-a) := by
    have him_eq : (∫ σ in a..b, logDeriv H (point σ t)).im =
        ∫ σ in a..b, (logDeriv H (point σ t)).im := by
      simpa using (Complex.imCLM.intervalIntegral_comp_comm hiH).symm
    rw [him_eq]
    have hbound : ∀ σ ∈ uIoc a b, ‖(logDeriv H (point σ t)).im‖ ≤ firstConstant := by
      intro σ hσ
      rw [uIoc_of_le hab] at hσ
      have hx : σ ∈ Icc a b := ⟨hσ.1.le,hσ.2⟩
      rw [show logDeriv H (point σ t) = Zeta23.XiPrime.Lfn (point σ t) from H_logDeriv _ (hr σ hx) (hne σ)]
      have hs := Lfn_stirling_bound T (point σ t) hT (hr σ hx)
        (by simp [point]; linarith [hx.2]) (by simp [point]; linarith [ht.1])
        (by simp [point]; linarith [ht.2])
      have hm := (Complex.abs_im_le_norm (Zeta23.XiPrime.Lfn (point σ t)-(Real.log T:ℂ)/2)).trans hs
      simpa using hm
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hsplit,Complex.add_im]
  have hp := hh t ht hsafe a b ha hab hb
  have hC : 0 ≤ firstConstant := by unfold firstConstant; positivity
  have hlen : b-a ≤ 3 := by linarith
  have hgamma := mul_le_mul_of_nonneg_left hlen hC
  have hlarge := mul_le_mul_of_nonneg_left hL (show 0 ≤ 3*firstConstant by positivity)
  exact (abs_add_le _ _).trans ((add_le_add him hp).trans (by nlinarith))

#print axioms logDeriv_factor
#print axioms logDeriv_integrable
#print axioms auxiliary_horizontal_safe
end XiPrime8845.WuAuxiliaryHorizontal

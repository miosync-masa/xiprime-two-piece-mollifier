import WuSubintervalLog

/-! The actual eta*psi boundary function and its left-edge logarithm.
The H factor is retained exactly. Nonvanishing and horizontal phase bounds
for this function are not inferred from AF's estimates for xi'/GammaR. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory
namespace XiPrime8845.WuAuxiliaryBoundary
open WuAuxiliary WuStirling WuUnsmoothing WuLittlewood WuSubintervalLog
open Zeta23.XiPrime (xiDeriv)
set_option maxHeartbeats 2000000

def auxiliary (T : ℝ) (s : ℂ) : ℂ := eta (Real.log T) s*psi T s

theorem auxiliary_entire (T : ℝ) : Differentiable ℂ (auxiliary T) :=
  (eta_entire _).mul (psi_entire T)

/-- The only odd derivative in eta is the first one. -/
theorem eta_reflection_difference (L : ℝ) (s : ℂ) :
    eta L s-eta L (1-s) = 2*((rCoeff 1:ℂ)/(L:ℂ))*xiDeriv s := by
  simp only [eta,xi_derivative_one_sub,Finset.sum_range_succ,Finset.sum_range_zero,rCoeff]
  norm_num [iteratedDeriv_one,Zeta23.XiPrime.xiDeriv]
  ring

/-- Nontriviality of eta is proved, not assumed from its being entire. -/
theorem eta_not_identically_zero (L : ℝ) (hL : L ≠ 0) : ∃ s : ℂ, eta L s ≠ 0 := by
  obtain ⟨s,hs⟩ := Zeta23.XiPrime.exists_xiDeriv_ne_zero
  by_contra! he
  have h := eta_reflection_difference L s
  rw [he s,he (1-s),sub_self] at h
  have hr : (rCoeff 1:ℂ) ≠ 0 := by exact_mod_cast linear_coefficient_pos.ne'
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero hr hLc)) hs) h.symm

theorem auxiliary_factor (T : ℝ) (s : ℂ) (hH : H s ≠ 0) :
    auxiliary T s = H s*(V T s*psi T s) := by
  unfold auxiliary V
  field_simp

/-- Pointwise logarithmic identity, only where the actual function is nonzero. -/
theorem log_auxiliary (T : ℝ) (s : ℂ) (hH : H s ≠ 0) (hf : auxiliary T s ≠ 0) :
    Real.log ‖auxiliary T s‖ = Real.log ‖H s‖+Real.log ‖V T s*psi T s‖ := by
  have hv : V T s*psi T s ≠ 0 := by
    intro h
    apply hf
    rw [auxiliary_factor T s hH,h,mul_zero]
  rw [auxiliary_factor T s hH,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr hH)
    (norm_ne_zero_iff.mpr hv)]

theorem log_auxiliary_left (T t : ℝ) (hH : H (leftPoint T t) ≠ 0)
    (hf : auxiliary T (leftPoint T t) ≠ 0) :
    Real.log ‖auxiliary T (leftPoint T t)‖ =
      Real.log ‖H (leftPoint T t)‖+Real.log (density T t)/2 := by
  rw [log_auxiliary T _ hH hf]
  unfold density
  rw [Real.log_pow]
  norm_num

/-- Regularization is an upper bound on the true log, not an equality. -/
theorem log_auxiliary_left_le (T t ρ : ℝ) (hρ : 0 < ρ)
    (hH : H (leftPoint T t) ≠ 0) (hf : auxiliary T (leftPoint T t) ≠ 0) :
    Real.log ‖auxiliary T (leftPoint T t)‖-Real.log ‖H (leftPoint T t)‖ ≤
      Real.log (density T t+ρ)/2 := by
  have hv : V T (leftPoint T t)*psi T (leftPoint T t) ≠ 0 := by
    intro h
    apply hf
    rw [auxiliary_factor T _ hH,h,mul_zero]
  have hd : 0 < density T t := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [log_auxiliary_left T t hH hf,add_sub_cancel_left]
  exact div_le_div_of_nonneg_right (Real.log_le_log hd (by linarith)) (by norm_num)

/-- The H nonvanishing hypothesis on the left edge is supplied by Stirling's
existing strip lemma. This is NOT nonvanishing of eta or psi. -/
theorem H_left_eventually_nonzero :
    ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T), H (leftPoint T t) ≠ 0 := by
  filter_upwards [WuStirlingTransfer.leftPoint_strip] with T hs
  intro t ht
  apply H_ne_zero
  · have hh := hs.2.2.1
    simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,sub_self,add_zero]
    linarith
  · intro he
    have hh := congrArg Complex.im he
    simp [leftPoint] at hh
    linarith [hs.1,ht.1]

/-- Integral form used by Littlewood. Only a nonvanishing left edge is
assumed; the logarithm itself need not be positive. -/
theorem left_log_integral_le (T u v ρ c : ℝ) (huv : u < v) (hρ : 0 < ρ)
    (hH : ∀ t ∈ Icc u v, H (leftPoint T t) ≠ 0)
    (hf : ∀ t ∈ Icc u v, auxiliary T (leftPoint T t) ≠ 0)
    (hHc : ContinuousOn (fun t => H (leftPoint T t)) (Icc u v))
    (hd : ContinuousOn (density T) (Icc u v))
    (hmean : subLogMean T u v ρ ≤ Real.log c/2) :
    (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖-Real.log ‖H (leftPoint T t)‖) ≤
      (v-u)*Real.log c/2 := by
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have ha : ContinuousOn (fun t => auxiliary T (leftPoint T t)) (Icc u v) :=
    ((auxiliary_entire T).continuous.comp hp).continuousOn
  have hi : IntegrableOn (fun t => Real.log ‖auxiliary T (leftPoint T t)‖-
      Real.log ‖H (leftPoint T t)‖) (Icc u v) :=
    ((ha.norm.log (fun t ht => norm_ne_zero_iff.mpr (hf t ht))).sub
      (hHc.norm.log (fun t ht => norm_ne_zero_iff.mpr (hH t ht)))).integrableOn_compact isCompact_Icc
  have hr : IntegrableOn (fun t => Real.log (density T t+ρ)) (Icc u v) :=
    ((hd.add continuousOn_const).log (fun t ht => ne_of_gt (by
      have hn : 0 ≤ density T t := sq_nonneg _
      change 0 < density T t+ρ
      linarith))).integrableOn_compact isCompact_Icc
  have hb := setIntegral_mono_on hi (hr.div_const 2) measurableSet_Icc
    (fun t ht => log_auxiliary_left_le T t ρ hρ (hH t ht) (hf t ht))
  rw [integral_div] at hb
  have hm := (div_le_iff₀ (show 0 < 2*(v-u) by linarith)).mp hmean
  exact hb.trans (by nlinarith)

/-- The original PRZZ moment now controls the actual left logarithm on
every inward unit trim. Nonvanishing of eta*psi stays explicit. -/
theorem left_log_eventually_le :
    ∀ δ : ℝ, 0 < δ → δ < 1/2 → ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1), ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T),
      (∀ t ∈ Icc u v, auxiliary T (leftPoint T t) ≠ 0) →
      (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖-Real.log ‖H (leftPoint T t)‖) ≤
        (v-u)*Real.log WitnessMomentBound.countingCap/2 := by
  obtain ⟨ρ0,hρ0,hmean⟩ := subLogMean_eventually_le
  intro δ hδ hd
  filter_upwards [hmean δ hδ hd,H_left_eventually_nonzero,WuStirlingTransfer.leftPoint_strip,
    WuTrimmedLog.density_continuous] with T hm hH hs hdensity
  intro u hu v hv hf
  have hsub : Icc u v ⊆ Icc T (2*T) := by
    intro t ht
    constructor <;> nlinarith [hu.1,hv.2,ht.1,ht.2,hs.1]
  apply left_log_integral_le T u v ρ0 _ (hm u hu v hv).1 hρ0
    (fun t ht => hH t (hsub ht)) hf _ (hdensity.mono hsub)
    ((hm u hu v hv).2 ρ0 hρ0 le_rfl)
  intro t ht
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hr : 0 < (leftPoint T t).re := by
    simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
    linarith [hs.2.2.1]
  exact ((H_analytic _ hr).continuousAt.comp hp.continuousAt).continuousWithinAt

#print axioms auxiliary_entire
#print axioms eta_reflection_difference
#print axioms eta_not_identically_zero
#print axioms auxiliary_factor
#print axioms log_auxiliary
#print axioms log_auxiliary_left
#print axioms log_auxiliary_left_le
#print axioms H_left_eventually_nonzero
#print axioms left_log_integral_le
#print axioms left_log_eventually_le
end XiPrime8845.WuAuxiliaryBoundary

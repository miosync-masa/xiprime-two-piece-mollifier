import MobiusPNTBridge

/-! General weighted Mobius smoothing via a finite continuous hinge kernel.
No derivative of the arithmetic step function is asserted. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology MeasureTheory

namespace XiPrime8845.WeightedMobius
open MobiusHarmonic

def logKernel (t : ℝ) : ℝ := logMean (Real.exp t)

/-- On a bounded interval the logarithmic primitive is a finite sum of hinges. -/
theorem logKernel_finite (T t : ℝ) (ht : t ≤ T) :
    logKernel t = ∑ n ∈ Ioc 0 ⌊Real.exp T⌋₊,
      (μ n : ℝ) / n * max (t - Real.log n) 0 := by
  unfold logKernel logMean
  trans ∑ n ∈ Ioc 0 ⌊Real.exp t⌋₊, (μ n : ℝ) / n * max (t - Real.log n) 0
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnt : (n : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).mp (Finset.mem_Ioc.mp hn).2
    have hl : Real.log n ≤ t := (Real.log_le_iff_le_exp hn0).mpr hnt
    rw [Real.log_div (Real.exp_ne_zero _) hn0.ne', Real.log_exp, max_eq_left (by linarith)]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl
    (Nat.floor_mono (Real.exp_le_exp.mpr ht)))
  intro n hn hnot
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hnt : Real.exp t < n := by
    have : ¬ n ≤ ⌊Real.exp t⌋₊ := fun h => hnot (Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1, h⟩)
    exact lt_of_not_ge (fun h => this ((Nat.le_floor_iff (Real.exp_pos t).le).mpr h))
  have hl : t < Real.log n := by
    rw [← Real.exp_lt_exp, Real.exp_log hn0]
    exact hnt
  rw [max_eq_right (by linarith), mul_zero]

theorem logKernel_continuous : Continuous logKernel := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have he : logKernel =ᶠ[nhds t] fun v => ∑ n ∈ Ioc 0 ⌊Real.exp (t+1)⌋₊,
      (μ n : ℝ) / n * max (v - Real.log n) 0 := by
    filter_upwards [eventually_lt_nhds (show t < t+1 by linarith)] with v hv
    exact logKernel_finite (t+1) v hv.le
  apply ContinuousAt.congr_of_eventuallyEq _ he
  fun_prop

theorem logKernel_tendsto : Tendsto logKernel atTop (nhds 1) :=
  MobiusPNTBridge.logMean_tendsto.comp Real.tendsto_exp_atTop

theorem logKernel_zero : logKernel 0 = 0 := by
  simp [logKernel, logMean]

/-- Taylor's integral identity with the expansion based at the upper endpoint. -/
theorem endpoint_taylor (F F₁ F₂ : ℝ → ℂ) (a u : ℝ)
    (hF : ∀ v, HasDerivAt F (F₁ v) v) (hF₁ : ∀ v, HasDerivAt F₁ (F₂ v) v)
    (hc : Continuous F₂) (hu : F u = 0) :
    F a = -((u-a : ℝ) : ℂ) * F₁ u + ∫ v in a..u, ((v-a : ℝ) : ℂ) * F₂ v := by
  have hd (v : ℝ) : HasDerivAt
      (fun v : ℝ => ((v-a : ℝ) : ℂ) * F₁ v - F v)
      (((v-a : ℝ) : ℂ) * F₂ v) v := by
    have hc : HasDerivAt (fun v : ℝ => ((v-a : ℝ) : ℂ)) (1 : ℂ) v := by
      simpa using ((hasDerivAt_id v).sub_const a).ofReal_comp
    convert! (hc.mul (hF₁ v)).sub (hF v) using 1
    simp only [one_mul, add_sub_cancel_left]
  have hi : IntervalIntegrable (fun v : ℝ => ((v-a : ℝ) : ℂ) * F₂ v) volume a u := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul hc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi
  simp only [sub_self, Complex.ofReal_zero, zero_mul, zero_sub, hu, sub_zero, sub_neg_eq_add] at h
  rw [h]
  ring

/-- The hinge integral has no contribution below its knot. -/
theorem hinge_integral (f : ℝ → ℂ) (hc : Continuous f) (a u : ℝ)
    (ha : 0 ≤ a) (hau : a ≤ u) :
    (∫ v in 0..u, (max (v-a) 0 : ℝ) * f v) =
      ∫ v in a..u, ((v-a : ℝ) : ℂ) * f v := by
  have hcont : Continuous (fun v : ℝ => (max (v-a) 0 : ℝ) * f v) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 a)
    (hcont.intervalIntegrable a u)]
  have hzero : (∫ v in 0..a, (max (v-a) 0 : ℝ) * f v) = 0 := by
    trans ∫ v in 0..a, (0 : ℂ)
    · apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le ha] at hv
      dsimp only
      rw [max_eq_right (by linarith [hv.2])]
      simp
    · simp
  rw [hzero, zero_add]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hau] at hv
  dsimp only
  rw [max_eq_left (by linarith [hv.1])]

theorem logKernel_scaled_finite (L u v : ℝ) (hL : 0 < L) (hv : v ≤ u) :
    (logKernel (L*v) : ℂ) =
      ∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊,
        ((L * ((μ n : ℝ)/n) : ℝ) : ℂ) * (max (v-Real.log n/L) 0 : ℝ) := by
  rw [logKernel_finite (L*u) (L*v) (mul_le_mul_of_nonneg_left hv hL.le)]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have he : max (L*v-Real.log n) 0 = L * max (v-Real.log n/L) 0 := by
    rw [mul_max_of_nonneg _ _ hL.le, mul_zero]
    congr 1
    field_simp
  rw [he]
  push_cast
  ring

/-- Finite-knot version of twice integration by parts; all smoothness belongs
to the weight, not to the piecewise-linear kernel. -/
theorem finite_weighted_identity {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → ℝ)
    (u : ℝ) (ha : ∀ n ∈ s, 0 ≤ a n ∧ a n ≤ u)
    (F F₁ F₂ : ℝ → ℂ) (hF : ∀ v, HasDerivAt F (F₁ v) v)
    (hF₁ : ∀ v, HasDerivAt F₁ (F₂ v) v) (hc : Continuous F₂) (hu : F u = 0) :
    (∑ n ∈ s, c n * F (a n)) =
      -(∑ n ∈ s, c n * ((u-a n : ℝ) : ℂ)) * F₁ u +
      ∫ v in 0..u, (∑ n ∈ s, c n * (max (v-a n) 0 : ℝ)) * F₂ v := by
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hinge_integral F₂ hc (a n) u (ha n hn).1 (ha n hn).2,
      endpoint_taylor F F₁ F₂ (a n) u hF hF₁ hc hu]
    ring
  · intro n hn
    apply Continuous.intervalIntegrable
    fun_prop

def weightedSum (L u : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊, ((μ n : ℝ)/n : ℝ) * F (Real.log n/L)

theorem weighted_mobius_twice_ibp (L u : ℝ) (hL : 0 < L) (hu0 : 0 ≤ u)
    (F F₁ F₂ : ℝ → ℂ) (hF : ∀ v, HasDerivAt F (F₁ v) v)
    (hF₁ : ∀ v, HasDerivAt F₁ (F₂ v) v) (hc : Continuous F₂) (hu : F u = 0) :
    (L : ℂ) * weightedSum L u F =
      -(logKernel (L*u) : ℂ) * F₁ u +
        ∫ v in 0..u, (logKernel (L*v) : ℂ) * F₂ v := by
  have ha (n : ℕ) (hn : n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊) :
      0 ≤ Real.log n/L ∧ Real.log n/L ≤ u := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    refine ⟨div_nonneg (Real.log_nonneg hn1) hL.le, (div_le_iff₀ hL).mpr ?_⟩
    have hnexp := (Nat.le_floor_iff (Real.exp_pos (L*u)).le).mp (Finset.mem_Ioc.mp hn).2
    have hlog := (Real.log_le_iff_le_exp hn0).mpr hnexp
    nlinarith
  have h := finite_weighted_identity (Ioc 0 ⌊Real.exp (L*u)⌋₊)
    (fun n => ((L*((μ n : ℝ)/n) : ℝ) : ℂ)) (fun n => Real.log n/L) u ha
    F F₁ F₂ hF hF₁ hc hu
  have hend : (logKernel (L*u) : ℂ) = ∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊,
      ((L*((μ n : ℝ)/n) : ℝ) : ℂ) * ((u-Real.log n/L : ℝ) : ℂ) := by
    rw [logKernel_scaled_finite L u u hL le_rfl]
    apply Finset.sum_congr rfl
    intro n hn
    rw [max_eq_left (sub_nonneg.mpr (ha n hn).2)]
  rw [hend]
  have hi : (∫ v in 0..u, (logKernel (L*v) : ℂ) * F₂ v) =
      ∫ v in 0..u, (∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊,
        ((L*((μ n : ℝ)/n) : ℝ) : ℂ) * (max (v-Real.log n/L) 0 : ℝ)) * F₂ v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hu0] at hv
    dsimp only
    rw [logKernel_scaled_finite L u v hL hv.2]
  rw [hi, ← h]
  simp only [weightedSum, Finset.mul_sum, Complex.ofReal_mul, mul_assoc]

/-- Exact residual after subtracting the 1/L leading term. -/
theorem weighted_mobius_residual (L u : ℝ) (hL : 0 < L) (hu0 : 0 ≤ u)
    (F F₁ F₂ : ℝ → ℂ) (hF : ∀ v, HasDerivAt F (F₁ v) v)
    (hF₁ : ∀ v, HasDerivAt F₁ (F₂ v) v) (hc : Continuous F₂) (hu : F u = 0) :
    (L : ℂ) * weightedSum L u F + F₁ 0 =
      -((logKernel (L*u) : ℂ)-1) * F₁ u +
        ∫ v in 0..u, ((logKernel (L*v) : ℂ)-1) * F₂ v := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hF₁ v) (hc.intervalIntegrable 0 u)
  have hj : IntervalIntegrable (fun v : ℝ => (logKernel (L*v) : ℂ)*F₂ v) volume 0 u := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp (logKernel_continuous.comp
      (continuous_const.mul continuous_id))).mul hc
  simp_rw [sub_mul, one_mul]
  rw [intervalIntegral.integral_sub hj (hc.intervalIntegrable 0 u), hi,
    weighted_mobius_twice_ibp L u hL hu0 F F₁ F₂ hF hF₁ hc hu]
  ring

/-- Continuous nonnegative errors tending to zero have vanishing integral means. -/
theorem cesaro_zero (f : ℝ → ℝ) (hc : Continuous f) (hn : ∀ t, 0 ≤ f t)
    (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun T : ℝ => (∫ t in 0..T, f t) / T) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hf (eps/2) (by positivity)
  let k := max K 0
  have hk : 0 ≤ k := le_max_right _ _
  have hhead : Tendsto (fun T : ℝ => (∫ t in 0..k, f t) / T) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (∫ t in 0..k, f t)
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hhead (eps/2) (by positivity)
  refine ⟨max (max X k) 1, fun T hT => ?_⟩
  have hTk : k ≤ T := (le_max_right X k).trans ((le_max_left _ _).trans hT)
  have hTX : X ≤ T := (le_max_left X k).trans ((le_max_left _ _).trans hT)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hT)
  have htail : (∫ t in k..T, f t) ≤ (T-k)*(eps/2) := by
    calc
      _ ≤ ∫ t in k..T, eps/2 := intervalIntegral.integral_mono_on hTk
        (hc.intervalIntegrable _ _) intervalIntegrable_const (fun t ht => by
          have h := hK t ((le_max_left K 0).trans ht.1)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (hn t)] at h
          exact h.le)
      _ = _ := by simp; ring
  have hheadsmall := hX T hTX
  rw [Real.dist_eq, sub_zero] at hheadsmall ⊢
  rw [abs_of_nonneg (div_nonneg (intervalIntegral.integral_nonneg_of_forall
    hT0.le hn) hT0.le)]
  have hsplit : (∫ t in 0..k, f t) + (∫ t in k..T, f t) = ∫ t in 0..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 k) (hc.intervalIntegrable k T)
  have hheadupper : (∫ t in 0..k, f t) / T < eps/2 :=
    (le_abs_self _).trans_lt hheadsmall
  have htailupper : (∫ t in k..T, f t) / T ≤ eps/2 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith
  rw [← hsplit, add_div]
  linarith

def absoluteError (t : ℝ) : ℝ := |logKernel t - 1|

theorem absoluteError_continuous : Continuous absoluteError :=
  (logKernel_continuous.sub continuous_const).abs

theorem absoluteError_tendsto : Tendsto absoluteError atTop (nhds 0) := by
  change Tendsto (fun t => |logKernel t - 1|) atTop (nhds 0)
  simpa only [sub_self, abs_zero] using (logKernel_tendsto.sub_const 1).abs

theorem absoluteError_cesaro :
    Tendsto (fun T : ℝ => (∫ t in 0..T, absoluteError t) / T) atTop (nhds 0) :=
  cesaro_zero absoluteError absoluteError_continuous (fun _ => abs_nonneg _)
    absoluteError_tendsto

theorem weighted_residual_bound (L u C₁ C₂ : ℝ) (hL : 0 < L) (hu0 : 0 ≤ u)
    (F F₁ F₂ : ℝ → ℂ) (hF : ∀ v, HasDerivAt F (F₁ v) v)
    (hF₁ : ∀ v, HasDerivAt F₁ (F₂ v) v) (hc : Continuous F₂) (hu : F u = 0)
    (h₁ : ‖F₁ u‖ ≤ C₁) (h₂ : ∀ v ∈ Set.Icc 0 u, ‖F₂ v‖ ≤ C₂) :
    ‖(L : ℂ)*weightedSum L u F + F₁ 0‖ ≤
      absoluteError (L*u)*C₁ + (∫ v in 0..u, absoluteError (L*v))*C₂ := by
  rw [weighted_mobius_residual L u hL hu0 F F₁ F₂ hF hF₁ hc hu]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, norm_neg]
    have he : ‖(logKernel (L*u) : ℂ)-1‖ = absoluteError (L*u) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rfl
    rw [he]
    exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)
  · apply (intervalIntegral.norm_integral_le_integral_norm hu0).trans
    have he : (∫ v in 0..u, absoluteError (L*v))*C₂ =
        ∫ v in 0..u, absoluteError (L*v)*C₂ :=
      (intervalIntegral.integral_mul_const C₂ _).symm
    rw [he]
    apply intervalIntegral.integral_mono_on hu0
    · apply Continuous.intervalIntegrable
      exact (((Complex.continuous_ofReal.comp (logKernel_continuous.comp
        (continuous_const.mul continuous_id))).sub continuous_const).mul hc).norm
    · exact ((absoluteError_continuous.comp (continuous_const.mul continuous_id)).mul_const C₂).intervalIntegrable _ _
    · intro v hv
      rw [norm_mul]
      have he : ‖(logKernel (L*v) : ℂ)-1‖ = absoluteError (L*v) := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rfl
      rw [he]
      exact mul_le_mul_of_nonneg_left (h₂ v hv) (abs_nonneg _)

theorem error_integral_rescale (L U : ℝ) (hL : L ≠ 0) :
    (∫ v in 0..U, absoluteError (L*v)) =
      (∫ t in 0..(L*U), absoluteError t) / L := by
  rw [intervalIntegral.integral_comp_mul_left _ hL]
  simp only [mul_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem error_integral_tendsto (U : ℝ) (hU : 0 < U) :
    Tendsto (fun L : ℝ => ∫ v in 0..U, absoluteError (L*v)) atTop (nhds 0) := by
  have h := (absoluteError_cesaro.comp (tendsto_id.atTop_mul_const hU)).mul_const U
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  dsimp only [Function.comp_apply, id_eq]
  rw [error_integral_rescale L U hL.ne']
  field_simp

/-- Uniform transfer for any family of twice differentiable complex weights.
Only uniform derivative bounds are required; the index may contain both the
complex shift and the cutoff. The endpoint u=0 is deliberately excluded. -/
theorem weighted_family_uniform {ι : Type*} (s : Set ι) (u : ι → ℝ)
    (F F₁ F₂ : ι → ℝ → ℂ) (u₀ U C₁ C₂ : ℝ) (hu₀ : 0 < u₀) (hU : 0 < U)
    (hC₂ : 0 ≤ C₂) (hu : ∀ p ∈ s, u p ∈ Set.Icc u₀ U)
    (hF : ∀ p ∈ s, ∀ v, HasDerivAt (F p) (F₁ p v) v)
    (hF₁ : ∀ p ∈ s, ∀ v, HasDerivAt (F₁ p) (F₂ p v) v)
    (hc : ∀ p ∈ s, Continuous (F₂ p)) (hend : ∀ p ∈ s, F p (u p) = 0)
    (h₁ : ∀ p ∈ s, ‖F₁ p (u p)‖ ≤ C₁)
    (h₂ : ∀ p ∈ s, ∀ v ∈ Set.Icc 0 (u p), ‖F₂ p v‖ ≤ C₂) :
    TendstoUniformlyOn (fun (L : ℝ) p => (L : ℂ)*weightedSum L (u p) (F p))
      (fun p => -F₁ p 0) atTop s := by
  have htail : Tendsto (fun L : ℝ => (∫ v in 0..U, absoluteError (L*v))*C₂)
      atTop (nhds 0) := by simpa using (error_integral_tendsto U hU).mul_const C₂
  have hboundary : Tendsto (fun t => absoluteError t*C₁) atTop (nhds 0) := by
    simpa using absoluteError_tendsto.mul_const C₁
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hboundary (eps/2) (by positivity)
  have hscale : Tendsto (fun L : ℝ => L*u₀) atTop atTop :=
    tendsto_id.atTop_mul_const hu₀
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hscale.eventually (eventually_ge_atTop X),
    htail.eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < eps/2))]
      with L hL hLX htailL
  intro p hp
  have hup : 0 ≤ u p := (hu₀.le.trans (hu p hp).1)
  have hbound := weighted_residual_bound L (u p) C₁ C₂ hL hup
    (F p) (F₁ p) (F₂ p) (hF p hp) (hF₁ p hp) (hc p hp)
    (hend p hp) (h₁ p hp) (h₂ p hp)
  have hpoint := hX (L*u p) (hLX.trans (mul_le_mul_of_nonneg_left (hu p hp).1 hL.le))
  rw [Real.dist_eq, sub_zero] at hpoint
  have hpoint' : absoluteError (L*u p)*C₁ < eps/2 := (le_abs_self _).trans_lt hpoint
  have htail' : (∫ v in 0..U, absoluteError (L*v))*C₂ < eps/2 := by
    have ht : |(∫ v in 0..U, absoluteError (L*v))*C₂| < eps/2 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using htailL
    exact (le_abs_self _).trans_lt ht
  have hint : (∫ v in 0..u p, absoluteError (L*v)) ≤
      ∫ v in 0..U, absoluteError (L*v) := by
    apply intervalIntegral.integral_mono_interval le_rfl hup (hu p hp).2
    · exact Filter.Eventually.of_forall (fun v => abs_nonneg _)
    · exact (absoluteError_continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hmul := mul_le_mul_of_nonneg_right hint hC₂
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add]
  exact hbound.trans_lt (by linarith)

#print axioms logKernel_finite
#print axioms logKernel_continuous
#print axioms logKernel_tendsto
#print axioms endpoint_taylor
#print axioms finite_weighted_identity
#print axioms weighted_mobius_twice_ibp
#print axioms weighted_mobius_residual
#print axioms cesaro_zero
#print axioms absoluteError_cesaro
#print axioms weighted_residual_bound
#print axioms error_integral_tendsto
#print axioms weighted_family_uniform
end XiPrime8845.WeightedMobius

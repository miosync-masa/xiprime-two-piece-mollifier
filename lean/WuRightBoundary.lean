import WuRightMollifier
import Zeta23.XiPrime.ZeroCount.ArgBound

/-! Actual right-edge estimates at Re s = 3, uniform for T <= Im s <= 2T.
The original moving mollifier is used. The logarithmic integral is o(T),
which is sufficient after multiplying by log(T) in the counting argument.
No horizontal phase estimate or local counting inequality is inferred. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset Set MeasureTheory
namespace XiPrime8845.WuRightBoundary
open WuAuxiliary WuStirling WuLittlewood ZetaMomentIntegral WuRightMollifier
set_option maxHeartbeats 2000000

def zetaCap (k : ℕ) : ℝ := (k.factorial:ℝ)*(Real.pi^2/6)

theorem zetaCap_nonneg (k : ℕ) : 0 ≤ zetaCap k := by unfold zetaCap; positivity

theorem zeta_derivative_bound (k : ℕ) (s : ℂ) (hs : 3 ≤ s.re) :
    ‖iteratedDeriv k riemannZeta s‖ ≤ zetaCap k := by
  have hre (w : ℂ) (hw : dist w s ≤ 1) : 2 ≤ w.re := by
    have hh := Complex.abs_re_le_norm (w-s)
    rw [Complex.sub_re,← dist_eq_norm] at hh
    have := (abs_le.mp (hh.trans hw)).1
    linarith
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball s 1) :=
    DifferentiableOn.diffContOnCl (by
      intro w hw
      have hr := hre w (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw))
      exact (differentiableAt_riemannZeta (by intro he; rw [he] at hr; norm_num at hr)).differentiableWithinAt)
  simpa only [one_pow,div_one,zetaCap] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0:ℝ)<1) hd
      (fun w hw => Zeta23.RvM.norm_riemannZeta_le_of_two_le_re (hre w (Metric.mem_sphere.mp hw).le))

theorem scaled_bound (k : ℕ) (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 3 ≤ s.re) :
    ‖scaledZeta k T s‖ ≤ zetaCap k := by
  rw [scaledZeta,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hL)).trans (zeta_derivative_bound k s hs)

theorem scaled_succ_bound (k : ℕ) (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 3 ≤ s.re) :
    ‖scaledZeta (k+1) T s‖ ≤ zetaCap (k+1)/Real.log T := by
  rw [scaledZeta,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  apply (div_le_div_of_nonneg_right (zeta_derivative_bound _ s hs) (by positivity)).trans
  apply div_le_div_of_nonneg_left (zetaCap_nonneg _) (by linarith)
  rw [pow_succ]
  exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ hL)

def operatorCap : ℝ := ∑ k ∈ range 6, ‖NumericalGate.qCoeff (k+1)‖*zetaCap (k+1)
def differenceCap : ℝ := operatorCap+WuStirlingTransfer.transferConstant*∑ k ∈ range 7, zetaCap k

theorem differenceCap_nonneg : 0 ≤ differenceCap := by
  unfold differenceCap operatorCap
  exact add_nonneg (sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (zetaCap_nonneg _)))
    (mul_nonneg WuStirlingTransfer.transferConstant_nonneg (sum_nonneg (fun _ _ => zetaCap_nonneg _)))

theorem U_sub_zeta_bound (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 3 ≤ s.re) :
    ‖U T s-riemannZeta s‖ ≤ operatorCap/Real.log T := by
  have he : U T s-riemannZeta s = ∑ k ∈ range 6,
      NumericalGate.qCoeff (k+1)*(-1:ℂ)^(k+1)*scaledZeta (k+1) T s := by
    unfold U ZetaMomentPolynomial.differentialPolynomial
    simp only [WitnessMomentBound.qReal_cast]
    rw [sum_range_succ']
    simp [NumericalGate.qCoeff,scaledZeta]
  rw [he,operatorCap,sum_div]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k hk
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one]
  exact (mul_le_mul_of_nonneg_left (scaled_succ_bound k T hL s hs) (norm_nonneg _)).trans_eq (by ring)

theorem V_sub_zeta_bound (T t : ℝ) (hT : 4 ≤ T) (hL : 1 ≤ Real.log T) (ht : t ∈ Icc T (2*T)) :
    ‖V T (point 3 t)-riemannZeta (point 3 t)‖ ≤ differenceCap/Real.log T := by
  have hr : 3 ≤ (point 3 t).re := by simp [point]
  have h1 := WuStirlingTransfer.difference_bound T t 3 hT hL ht (by norm_num)
  have h2 := U_sub_zeta_bound T hL (point 3 t) hr
  have hsum := sum_le_sum (fun k (_ : k ∈ range 7) => scaled_bound k T hL (point 3 t) hr)
  have h3 := mul_le_mul_of_nonneg_left hsum
    (div_nonneg WuStirlingTransfer.transferConstant_nonneg (by linarith : 0 ≤ Real.log T))
  have hh := norm_sub_le_norm_sub_add_norm_sub (V T (point 3 t)) (U T (point 3 t)) (riemannZeta (point 3 t))
  apply hh.trans
  exact (add_le_add (h1.trans h3) h2).trans_eq (by unfold differenceCap; ring)

/-- Genuine moving-family uniform convergence, not a fixed-T right limit. -/
theorem product_uniform :
    ∀ ε > 0, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ‖V T (point 3 t)*psi T (point 3 t)-1‖ < ε := by
  have hd : Tendsto (fun T : ℝ => (differenceCap/Real.log T)*(7*(Real.pi^2/6))) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul differenceCap).mul_const (7*(Real.pi^2*6⁻¹))
  intro ε hε
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    hd.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp zeta_psi_uniform (ε/2) (by positivity)] with T hT hL hdT hz
  intro t ht
  have hs : 2 ≤ (point 3 t).re := by norm_num [point]
  have hz' := hz (point 3 t) hs
  rw [dist_comm,dist_eq_norm] at hz'
  have hmul := mul_le_mul (V_sub_zeta_bound T t hT hL ht) (psi_bound T (by linarith) _ hs)
    (norm_nonneg _) (div_nonneg differenceCap_nonneg (by linarith))
  have he : V T (point 3 t)*psi T (point 3 t)-1 =
      (V T (point 3 t)-riemannZeta (point 3 t))*psi T (point 3 t)+
        (riemannZeta (point 3 t)*psi T (point 3 t)-1) := by ring
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul]
  linarith

theorem right_nonzero : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    WuAuxiliaryBoundary.auxiliary T (point 3 t) ≠ 0 := by
  filter_upwards [product_uniform (1/2) (by norm_num)] with T hT
  intro t ht
  have hH : H (point 3 t) ≠ 0 := H_ne_zero _ (by norm_num [point])
    (by intro h; have := congrArg Complex.re h; norm_num [point] at this)
  rw [WuAuxiliaryBoundary.auxiliary_factor T _ hH]
  apply mul_ne_zero hH
  intro he
  have hh := hT t ht
  rw [he] at hh
  norm_num at hh

def rightLog (T t : ℝ) : ℝ := Real.log ‖V T (point 3 t)*psi T (point 3 t)‖

theorem rightLog_uniform : ∀ ε > 0, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T), |rightLog T t| < ε := by
  have hc : ContinuousAt (fun z : ℂ => Real.log ‖z‖) 1 := continuousAt_id.norm.log (by simp)
  intro ε hε
  obtain ⟨d,hd,hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  filter_upwards [product_uniform d hd] with T hT
  intro t ht
  have h := hh (by simpa only [dist_eq_norm] using hT t ht)
  simpa only [rightLog,norm_one,Real.log_one,Real.dist_eq,sub_zero] using h

theorem right_analytic (T t : ℝ) :
    AnalyticAt ℂ (fun s => V T s*psi T s) (point 3 t) := by
  have hr : 0 < (point 3 t).re := by norm_num [point]
  have hne : point 3 t ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [point] at this
  exact (((eta_entire _).analyticAt _).div (H_analytic _ hr) (H_ne_zero _ hr hne)).mul
    ((psi_entire T).analyticAt _)

theorem right_real_pos : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    0 < (V T (point 3 t)*psi T (point 3 t)).re := by
  filter_upwards [product_uniform (1/2) (by norm_num)] with T hT
  intro t ht
  have hh := (Complex.abs_re_le_norm (V T (point 3 t)*psi T (point 3 t)-1)).trans_lt (hT t ht)
  rw [Complex.sub_re,Complex.one_re] at hh
  have := (abs_lt.mp hh).1
  linarith

theorem rightLog_integrable : ∀ᶠ T : ℝ in atTop, IntegrableOn (rightLog T) (Icc T (2*T)) := by
  filter_upwards [right_real_pos] with T hT
  have hp : Continuous (point (3:ℝ)) := by unfold point; fun_prop
  have hc : ContinuousOn (rightLog T) (Icc T (2*T)) := by
    intro t ht
    exact ((((right_analytic T t).continuousAt.comp hp.continuousAt).norm).log
      (norm_ne_zero_iff.mpr (by
        intro he
        change V T (point 3 t)*psi T (point 3 t) = 0 at he
        have hh := hT t ht
        rw [he] at hh
        norm_num at hh))).continuousWithinAt
  exact hc.integrableOn_compact isCompact_Icc

/-- Every shortened right edge has the same small absolute log budget. -/
theorem rightLog_integral_bound : ∀ ε > 0, ∀ᶠ T : ℝ in atTop,
    ∀ u v : ℝ, T ≤ u → u ≤ v → v ≤ 2*T →
      |∫ t in Icc u v, rightLog T t| ≤ ε*(v-u) := by
  intro ε hε
  filter_upwards [rightLog_uniform ε hε] with T hT
  intro u v hu huv hv
  have hh := norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top (μ := volume))
    (fun t (ht : t ∈ Icc u v) => (show ‖rightLog T t‖ ≤ ε by
      simpa only [Real.norm_eq_abs] using (hT t ⟨hu.trans ht.1,ht.2.trans hv⟩).le))
  simpa only [Real.norm_eq_abs,Real.volume_real_Icc_of_le huv] using hh

theorem normalized_rightLog_tendsto :
    Tendsto (fun T => (∫ t in Icc T (2*T), rightLog T t)/T) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T0,h0⟩ := eventually_atTop.mp ((rightLog_integral_bound (ε/2) (by positivity)).and
    (eventually_gt_atTop (0:ℝ)))
  refine ⟨T0,?_⟩
  intro T hT
  obtain ⟨hh,hpos⟩ := h0 T hT
  have hb := hh T (2*T) le_rfl (by linarith) le_rfl
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos]
  apply (div_le_div_of_nonneg_right hb hpos.le).trans_lt
  have he : ε/2*(2*T-T)/T = ε/2 := by field_simp; ring
  rw [he]
  linarith

/-- Actual right vertical phase, uniformly in T and both endpoints.
This is not the horizontal Backlund estimate. -/
theorem right_phase_bound : ∀ᶠ T : ℝ in atTop, ∀ u v : ℝ,
    T ≤ u → u ≤ v → v ≤ 2*T →
      |(∫ t in u..v, logDeriv (fun s => V T s*psi T s) (point 3 t)*Complex.I).im| ≤ Real.pi := by
  filter_upwards [right_real_pos] with T hT
  intro u v hu huv hv
  exact Zeta23.XiPrime.ZeroCount.abs_im_integral_logDeriv_vertical_le_pi huv
    (fun t _ => right_analytic T t) (fun t ht => hT t ⟨hu.trans ht.1,ht.2.trans hv⟩)

#print axioms zeta_derivative_bound
#print axioms scaled_bound
#print axioms scaled_succ_bound
#print axioms U_sub_zeta_bound
#print axioms V_sub_zeta_bound
#print axioms product_uniform
#print axioms right_nonzero
#print axioms rightLog_uniform
#print axioms right_analytic
#print axioms right_real_pos
#print axioms rightLog_integrable
#print axioms rightLog_integral_bound
#print axioms normalized_rightLog_tendsto
#print axioms right_phase_bound
end XiPrime8845.WuRightBoundary

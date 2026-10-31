import WuDiskGrowth

/-! Uniform normalization at the centre of the moving Landau discs.
The height, shifts, and original mollifier all retain their T dependence. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset Set
namespace XiPrime8845.WuDiskCenter
open WuAuxiliary WuStirling WuLittlewood WuDiskGrowth WuRightMollifier ZetaMomentIntegral
set_option maxHeartbeats 2000000

theorem centerCap_nonneg (k : ℕ) : 0 ≤ centerCap k := by
  have := halfPlaneCap_nonneg
  unfold centerCap
  positivity

theorem scaled_bound (k : ℕ) (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖scaledZeta k T s‖ ≤ centerCap k := by
  rw [scaledZeta,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hL)).trans (center_derivative_bound k s hs)

theorem scaled_succ_bound (k : ℕ) (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖scaledZeta (k+1) T s‖ ≤ centerCap (k+1)/Real.log T := by
  rw [scaledZeta,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  apply (div_le_div_of_nonneg_right (center_derivative_bound _ s hs) (by positivity)).trans
  apply div_le_div_of_nonneg_left (centerCap_nonneg _) (by linarith)
  rw [pow_succ]
  exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ hL)

def operatorCap : ℝ := ∑ k ∈ range 6, ‖NumericalGate.qCoeff (k+1)‖*centerCap (k+1)
def differenceCap : ℝ := operatorCap+WuStirlingTransfer.transferConstant*∑ k ∈ range 7, centerCap k

theorem differenceCap_nonneg : 0 ≤ differenceCap := by
  unfold differenceCap operatorCap
  exact add_nonneg (sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (centerCap_nonneg _)))
    (mul_nonneg WuStirlingTransfer.transferConstant_nonneg (sum_nonneg (fun _ _ => centerCap_nonneg _)))

theorem U_sub_zeta_bound (T : ℝ) (hL : 1 ≤ Real.log T) (s : ℂ) (hs : 2 ≤ s.re) :
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
    ‖V T (point 2 t)-riemannZeta (point 2 t)‖ ≤ differenceCap/Real.log T := by
  have hr : 2 ≤ (point 2 t).re := by simp [point]
  have h1 := WuStirlingTransfer.difference_bound T t 2 hT hL ht (by norm_num)
  have h2 := U_sub_zeta_bound T hL (point 2 t) hr
  have hsum := sum_le_sum (fun k (_ : k ∈ range 7) => scaled_bound k T hL (point 2 t) hr)
  have h3 := mul_le_mul_of_nonneg_left hsum
    (div_nonneg WuStirlingTransfer.transferConstant_nonneg (by linarith : 0 ≤ Real.log T))
  have hh := norm_sub_le_norm_sub_add_norm_sub (V T (point 2 t)) (U T (point 2 t)) (riemannZeta (point 2 t))
  apply hh.trans
  exact (add_le_add (h1.trans h3) h2).trans_eq (by unfold differenceCap; ring)

/-- Genuine moving-family uniform convergence, not a fixed-T right limit. -/
theorem product_uniform :
    ∀ ε > 0, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ‖V T (point 2 t)*psi T (point 2 t)-1‖ < ε := by
  have hd : Tendsto (fun T : ℝ => (differenceCap/Real.log T)*(7*(Real.pi^2/6))) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul differenceCap).mul_const (7*(Real.pi^2*6⁻¹))
  intro ε hε
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    hd.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp zeta_psi_uniform (ε/2) (by positivity)] with T hT hL hdT hz
  intro t ht
  have hs : 2 ≤ (point 2 t).re := by norm_num [point]
  have hz' := hz (point 2 t) hs
  rw [dist_comm,dist_eq_norm] at hz'
  have hmul := mul_le_mul (V_sub_zeta_bound T t hT hL ht) (psi_bound T (by linarith) _ hs)
    (norm_nonneg _) (div_nonneg differenceCap_nonneg (by linarith))
  have he : V T (point 2 t)*psi T (point 2 t)-1 =
      (V T (point 2 t)-riemannZeta (point 2 t))*psi T (point 2 t)+
        (riemannZeta (point 2 t)*psi T (point 2 t)-1) := by ring
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul]
  linarith


theorem center_lower : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
    1/2 ≤ ‖V T (point 2 t)*psi T (point 2 t)‖ := by
  filter_upwards [product_uniform (1/2) (by norm_num)] with T hT
  intro t ht
  have hh := norm_sub_le (V T (point 2 t)*psi T (point 2 t)) 1
  have hn := norm_le_norm_sub_add (1:ℂ) (V T (point 2 t)*psi T (point 2 t))
  rw [norm_sub_rev, norm_one] at hn
  linarith [hT t ht]

#print axioms V_sub_zeta_bound
#print axioms product_uniform
#print axioms center_lower
end XiPrime8845.WuDiskCenter


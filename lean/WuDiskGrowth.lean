import WuWideGamma

/-! Height-independent envelopes on the actual moving Wu discs. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset Set Metric
namespace XiPrime8845.WuDiskGrowth
open WuAuxiliary WuStirling WuGammaJets WuRightMollifier ZetaMomentIntegral
set_option maxHeartbeats 2000000

def halfPlaneCap : ℝ := ∑' n : ℕ, 1/(n:ℝ)^(3/2:ℝ)

theorem halfPlaneCap_nonneg : 0 ≤ halfPlaneCap := tsum_nonneg (fun _ => by positivity)

theorem zeta_halfPlane_bound (s : ℂ) (hs : 3/2 ≤ s.re) : ‖riemannZeta s‖ ≤ halfPlaneCap := by
  have hsum := Complex.summable_one_div_nat_cpow.mpr (show 1 < s.re by linarith)
  have hb := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ)<3/2)
  rw [zeta_eq_tsum_one_div_nat_cpow (show 1 < s.re by linarith)]
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply hsum.norm.tsum_le_tsum _ hb
  intro n
  by_cases hn : n = 0
  · have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
    simp [hn,Complex.zero_cpow hs0]
  have hp := Nat.pos_of_ne_zero hn
  rw [norm_div,norm_one,Complex.norm_natCast_cpow_of_pos hp]
  exact one_div_le_one_div_of_le (by positivity)
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hs)

def centerCap (k : ℕ) : ℝ := (k.factorial:ℝ)*halfPlaneCap/(1/2:ℝ)^k

theorem center_derivative_bound (k : ℕ) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖iteratedDeriv k riemannZeta s‖ ≤ centerCap k := by
  have hre (w : ℂ) (hw : dist w s ≤ 1/2) : 3/2 ≤ w.re := by
    have hh := Complex.abs_re_le_norm (w-s)
    rw [Complex.sub_re,← dist_eq_norm] at hh
    have := (abs_le.mp (hh.trans hw)).1
    linarith
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num)
    (DifferentiableOn.diffContOnCl (by
      intro w hw
      have hr := hre w (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw))
      exact (differentiableAt_riemannZeta (by intro he; rw [he] at hr; norm_num at hr)).differentiableWithinAt))
    (fun w hw => zeta_halfPlane_bound w (hre w (Metric.mem_sphere.mp hw).le))

def derivativeCap (k : ℕ) : ℝ := (k.factorial:ℝ)*60/(1/128:ℝ)^k

theorem disk_derivative_bound (k : ℕ) (T t : ℝ) (hT : 4 ≤ T)
    (ht : t ∈ Icc T (2*T)) (s : ℂ) (hs : ‖s-center t‖ ≤ 19/10) :
    ‖iteratedDeriv k riemannZeta s‖ ≤ derivativeCap k*T := by
  have hreg (w : ℂ) (hw : dist w s ≤ 1/128) :
      1/16 ≤ w.re ∧ T/2 ≤ w.im ∧ w.im ≤ 3*T := by
    have hh := norm_sub_le_norm_sub_add_norm_sub w s (center t)
    rw [dist_eq_norm] at hw
    have hb : ‖w-center t‖ ≤ 19/10+1/128 := by linarith
    have hr := (Complex.abs_re_le_norm (w-center t)).trans hb
    have hi := (Complex.abs_im_le_norm (w-center t)).trans hb
    norm_num [WuGammaJets.center] at hr hi
    obtain ⟨hr1,hr2⟩ := abs_le.mp hr
    obtain ⟨hi1,hi2⟩ := abs_le.mp hi
    exact ⟨by linarith,by linarith [ht.1],by linarith [ht.2]⟩
  have hb (w : ℂ) (hw : dist w s ≤ 1/128) : ‖riemannZeta w‖ ≤ 60*T := by
    have hr := hreg w hw
    have hh := Zeta23.RvM.riemannZeta_linear_growth (by norm_num : (0:ℝ)<1/16) hr.1
      (by rw [abs_of_nonneg (by linarith : 0 ≤ w.im)]; linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ w.im)] at hh
    norm_num at hh
    linarith [hr.2.2]
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0:ℝ)<1/128)
    (DifferentiableOn.diffContOnCl (by
      intro w hw
      have hr := hreg w (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw))
      exact (differentiableAt_riemannZeta (by intro he; rw [he] at hr; norm_num at hr; linarith)).differentiableWithinAt))
    (fun w hw => hb w (Metric.mem_sphere.mp hw).le)
  exact hh.trans_eq (by unfold derivativeCap; ring)

def vCap : ℝ := ∑ n ∈ range 7, ∑ j ∈ range (n+1),
  |rCoeff n| * (n.choose j:ℝ)*(1+WuWideGamma.jetConstant j)*derivativeCap (n-j)

theorem vCap_nonneg : 0 ≤ vCap := by
  apply sum_nonneg
  intro n hn
  apply sum_nonneg
  intro j hj
  have := WuWideGamma.jetConstant_nonneg j
  unfold derivativeCap
  positivity

theorem V_disk_bound (T t : ℝ) (hT : 4 ≤ T) (hL : 1 ≤ Real.log T)
    (ht : t ∈ Icc T (2*T)) (s : ℂ) (hs : ‖s-center t‖ ≤ 19/10) :
    ‖V T s‖ ≤ vCap*T := by
  have hz := disc_strip T t _ s hT ht (by norm_num : (19/10:ℝ)<2) hs
  rw [V_expansion T s hz.1 hz.2.2.2.2 (by linarith)]
  apply (norm_sum_le _ _).trans
  unfold vCap
  rw [sum_mul]
  apply sum_le_sum
  intro n hn
  apply (norm_sum_le _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  have hj6 : j ≤ 6 := by have := mem_range.mp hn; have := mem_range.mp hj; omega
  have hjet : ‖jet j T s‖ ≤ 1+WuWideGamma.jetConstant j := by
    have hwide : ‖s-center t‖ ≤ WuWideGamma.radius j := hs.trans (by
      have hj' : (j:ℝ) ≤ 6 := by exact_mod_cast hj6
      unfold WuWideGamma.radius; linarith)
    have he := WuWideGamma.jet_bound j hj6 T t hT hL ht s hwide
    have hc := div_le_self (WuWideGamma.jetConstant_nonneg j) hL
    have hp : ‖(1/2:ℂ)^j‖ ≤ 1 := by
      rw [norm_pow]; norm_num; exact pow_le_one₀ (by norm_num) (by norm_num)
    have hh := norm_le_norm_sub_add (jet j T s) ((1/2:ℂ)^j)
    linarith
  have hd : ‖scaledZeta (n-j) T s‖ ≤ derivativeCap (n-j)*T := by
    rw [scaledZeta,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ hL)).trans (disk_derivative_bound _ T t hT ht s hs)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hjet (by positivity)) hd (norm_nonneg _)
    (by have := WuWideGamma.jetConstant_nonneg j; positivity)).trans_eq (by ring)

theorem psi_polynomial_bound (T : ℝ) (hT : 2 ≤ T) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖psi T s‖ ≤ 7*T := by
  unfold psi PRZZ.dirichletPolynomial
  apply (norm_sum_le _ _).trans
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 (PRZZ.cutoff PRZZAsymptotic.theta T)) :
      ‖PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T n /
        (n:ℂ)^(s+(PRZZAsymptotic.R/Real.log T:ℝ))‖ ≤ 7 := by
    have hp : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [norm_div,Complex.norm_natCast_cpow_of_pos hp]
    apply (div_le_self (norm_nonneg _) ?_).trans
    · exact (PRZZ.witness_coefficient_bound _ T (by norm_num [PRZZAsymptotic.theta]) hT n).trans (by norm_num)
    · apply Real.one_le_rpow (by exact_mod_cast hp)
      simp only [Complex.add_re,Complex.ofReal_re]
      exact add_nonneg hs (div_nonneg PRZZAsymptotic.radius_pos.le (Real.log_nonneg (by linarith)))
  have hh := sum_le_sum hterm
  have hcut : (PRZZ.cutoff PRZZAsymptotic.theta T:ℝ) ≤ T := by
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ T) _)).trans
    calc
      T^PRZZAsymptotic.theta ≤ T^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num [PRZZAsymptotic.theta])
      _ = T := Real.rpow_one T
  simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hh
  exact hh.trans (by nlinarith)

theorem product_disk_bound (T t : ℝ) (hT : 4 ≤ T) (hL : 1 ≤ Real.log T)
    (ht : t ∈ Icc T (2*T)) (s : ℂ) (hs : ‖s-center t‖ ≤ 19/10) :
    ‖V T s*psi T s‖ ≤ (7*vCap)*T^2 := by
  have hr := disc_strip T t _ s hT ht (by norm_num : (19/10:ℝ)<2) hs
  rw [norm_mul]
  exact (mul_le_mul (V_disk_bound T t hT hL ht s hs)
    (psi_polynomial_bound T (by linarith) s hr.1.le) (norm_nonneg _)
    (mul_nonneg vCap_nonneg (by linarith))).trans_eq (by ring)

#print axioms zeta_halfPlane_bound
#print axioms center_derivative_bound
#print axioms disk_derivative_bound
#print axioms V_disk_bound
#print axioms psi_polynomial_bound
#print axioms product_disk_bound
end XiPrime8845.WuDiskGrowth

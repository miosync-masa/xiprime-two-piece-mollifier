import FengInverseProducts

/-! Actual outside/outside arithmetic limit. Both finite outside sums are
replaced before the positive totient measure is used; the shifted ratio is
retained until its uniform limit is applied. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengOutsideSquare
open FengAtG FengLogProducts FengOutsidePartner FengOutsidePrime FengInverseProfile
open FengInverseProducts CoprimeEndpoint LogProfileSum
set_option maxHeartbeats 1000000

theorem proxy_product_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    productSum FengOutside.mainProxy FengOutside.mainProxy L θ P G A B =
      (∑ g ∈ Ioc 0 (cutoff L θ), (TotientConvolution.weight g:ℂ)*BareEuler.ratio A B L g*
        (restrictedTransform L (coordinate L θ g) θ g P A*
          restrictedTransform L (coordinate L θ g) θ g G B))/(L:ℂ) := by
  unfold productSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [mainProxy_eq,mainProxy_eq]
  have he : (SupportTail.eulerMass g 0:ℂ) = ShiftedTotient.euler 0 g :=
    (ShiftedTotient.euler_zero g).symm
  rw [he]
  calc
    _ = (BareEuler.weight (A/L) (B/L) g*ShiftedTotient.euler 0 g*ShiftedTotient.euler 0 g)*
        (restrictedTransform L (coordinate L θ g) θ g P A*
          restrictedTransform L (coordinate L θ g) θ g G B) := by
      unfold FengMixedShift.rawWeight BareEuler.weight; ring
    _ = _ := by
      rw [BareEulerUniform.zeroEuler_weight_factor,ShiftedTotient.outerWeight_zero g (mem_Ioc.mp hg).1.ne']
      rfl

/-- Positive totient mass transfers a pointwise test error with no Euler
factor left over. -/
theorem totient_test_error (L θ d : ℝ) (X Y : ℕ → ℂ) (hL : 0 < L)
    (h : ∀ g ∈ Ioc 0 (cutoff L θ), ‖X g-Y g‖ ≤ d) :
    ‖(∑ g ∈ Ioc 0 (cutoff L θ), (TotientConvolution.weight g:ℂ)*(X g-Y g))/(L:ℂ)‖ ≤
      (TotientHarmonic.summatory (Real.exp (L*θ))/L)*d := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hb : (∑ g ∈ Ioc 0 (cutoff L θ), ‖(TotientConvolution.weight g:ℂ)*(X g-Y g)‖) ≤
      TotientHarmonic.summatory (Real.exp (L*θ))*d := by
    unfold TotientHarmonic.summatory
    rw [sum_mul]
    apply sum_le_sum
    intro g hg
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ TotientConvolution.weight g by
        change 0 ≤ (μ g:ℝ)^2/(g.totient:ℝ); positivity)]
    exact mul_le_mul_of_nonneg_left (h g hg) (by
      change 0 ≤ (μ g:ℝ)^2/(g.totient:ℝ); positivity)
  exact (div_le_div_of_nonneg_right ((norm_sum_le _ _).trans hb) hL.le).trans_eq (by ring)

theorem triple_error (r x y a b : ℂ) (e V W : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hV : 0 ≤ V) (_hW : 0 ≤ W)
    (hr : ‖r-1‖ ≤ e) (hx : ‖x-a‖ ≤ e) (hy : ‖y-b‖ ≤ e)
    (ha : ‖a‖ ≤ V) (hb : ‖b‖ ≤ W) :
    ‖r*(x*y)-a*b‖ ≤ e*(2*(W+1+V)+V*W) := by
  have hr2 : ‖r‖ ≤ 2 := by
    have h := norm_add_le (r-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at h
    linarith
  have hy1 : ‖y‖ ≤ W+1 := by
    have h := norm_sub_le_norm_sub_add_norm_sub y b 0
    rw [sub_zero,sub_zero] at h
    linarith
  have hxy : ‖x*y-a*b‖ ≤ e*(W+1+V) := by
    rw [show x*y-a*b=(x-a)*y+a*(y-b) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    have h1 := mul_le_mul hx hy1 (norm_nonneg _) he
    have h2 := mul_le_mul ha hy (norm_nonneg _) hV
    nlinarith
  rw [show r*(x*y)-a*b=r*(x*y-a*b)+(r-1)*(a*b) by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have h1 := mul_le_mul hr2 hxy (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have h2 := mul_le_mul hr (mul_le_mul ha hb (norm_nonneg _) hV)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) he
  nlinarith

theorem proxy_sub_profile_uniform (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) =>
        productSum FengOutside.mainProxy FengOutside.mainProxy L θ P G p.1 p.2-
          zeroSum L θ (doubleProfile θ P G p.1 p.2))
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  let V := inverseCap P θ C θ
  let W := inverseCap G θ C θ
  let K := 2*(W+1+V)+V*W
  have hV : 0 ≤ V := inverseCap_nonneg P θ C θ hθ hθ.le
  have hW : 0 ≤ W := inverseCap_nonneg G θ C θ hθ hθ.le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  let e := min 1 (eps/(2*((θ+1)*K+1)))
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have hesmall : e*((θ+1)*K+1) ≤ eps/2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (eps/(2*((θ+1)*K+1))))
      (show 0≤(θ+1)*K+1 by positivity)
    have heq : eps/(2*((θ+1)*K+1))*((θ+1)*K+1) = eps/2 := by field_simp
    exact h.trans_eq heq
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Metric.tendstoUniformlyOn_iff.mp TotientHarmonic.normalized_uniform 1 (by norm_num),
    BareEulerUniform.ratio_uniform C θ hsize e he,
    (errorEnvelope_tendsto θ C θ P).eventually (gt_mem_nhds he),
    (errorEnvelope_tendsto θ C θ G).eventually (gt_mem_nhds he)]
    with L hL ht hr hEP hEG
  intro p hp
  have hmass : TotientHarmonic.summatory (Real.exp (L*θ))/L ≤ θ+1 := by
    have hh := ht θ hθ.le
    rw [dist_comm,Real.dist_eq] at hh
    linarith [le_abs_self (TotientHarmonic.summatory (Real.exp (L*θ))/L-θ)]
  have hb := totient_test_error L θ (e*K)
    (fun g => BareEuler.ratio p.1 p.2 L g*
      (restrictedTransform L (coordinate L θ g) θ g P p.1*
        restrictedTransform L (coordinate L θ g) θ g G p.2))
    (fun g => doubleProfile θ P G p.1 p.2 (coordinate L θ g)) hL (by
      intro g hg
      have hg0 := (mem_Ioc.mp hg).1.ne'
      have hg1 : (1:ℝ)≤g := by exact_mod_cast (mem_Ioc.mp hg).1
      have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
      have hglog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<g)).mpr hgexp
      have hu := coordinate_mem L θ g hL ⟨hg1,hgexp⟩
      exact triple_error _ _ _ _ _ e V W he.le he1 hV hW (hr g p.1 p.2 hg0 hgexp hp.1 hp.2).le
        ((restrictedTransform_bound L _ θ C θ g P hP p.1 hL hθ hC hu hg0 hglog hp.1).trans hEP.le)
        ((restrictedTransform_bound L _ θ C θ g G hG p.2 hL hθ hC hu hg0 hglog hp.2).trans hEG.le)
        (inverse_bound P p.1 θ C θ _ hθ hp.1 hu) (inverse_bound G p.2 θ C θ _ hθ hp.2 hu))
  rw [dist_comm,dist_eq_norm,sub_zero,proxy_product_eq,zeroSum,TotientAbel.testedSum,← sub_div]
  change ‖((∑ g ∈ Ioc 0 (cutoff L θ), (TotientConvolution.weight g:ℂ)*BareEuler.ratio p.1 p.2 L g*
      (restrictedTransform L (coordinate L θ g) θ g P p.1*
        restrictedTransform L (coordinate L θ g) θ g G p.2))-
    ∑ g ∈ Ioc 0 (cutoff L θ), doubleProfile θ P G p.1 p.2 (coordinate L θ g)*
      (TotientConvolution.weight g:ℂ))/(L:ℂ)‖ < eps
  rw [← sum_sub_distrib]
  have hid : (∑ g ∈ Ioc 0 (cutoff L θ),
      ((TotientConvolution.weight g:ℂ)*BareEuler.ratio p.1 p.2 L g*
        (restrictedTransform L (coordinate L θ g) θ g P p.1*
          restrictedTransform L (coordinate L θ g) θ g G p.2)-
        doubleProfile θ P G p.1 p.2 (coordinate L θ g)*(TotientConvolution.weight g:ℂ))) =
      ∑ g ∈ Ioc 0 (cutoff L θ), (TotientConvolution.weight g:ℂ)*
        (BareEuler.ratio p.1 p.2 L g*
          (restrictedTransform L (coordinate L θ g) θ g P p.1*
            restrictedTransform L (coordinate L θ g) θ g G p.2)-
          doubleProfile θ P G p.1 p.2 (coordinate L θ g)) := by
    apply sum_congr rfl; intros; ring
  rw [hid]
  apply hb.trans_lt
  have hm := mul_le_mul_of_nonneg_right hmass (mul_nonneg he.le hK)
  nlinarith

theorem proxy_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) =>
        productSum FengOutside.mainProxy FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) (-1) 1)
      atTop ElementaryGcd.twoBidiscs := by
  have he := (proxy_sub_profile_uniform P G hP hG PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4)
    (by norm_num [PRZZAsymptotic.theta]) (by have := PRZZAsymptotic.radius_pos; positivity)
    ShiftedEulerUniform.witness_size).mono (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have hm := double_profile_twoBidiscs P G
  simpa only [Pi.add_def,sub_add_cancel,zero_add] using he.add hm

theorem outside_outside_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) (-1) 1)
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [Pi.add_def,sub_add_cancel,zero_add] using
    (outside_outside_sub_proxy P G hP hG).add (proxy_twoBidiscs P G hP hG)

theorem outside_outside_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock outsideBlock L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G (-1) (-1) 1)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (outside_outside_twoBidiscs P G hP hG)

#print axioms proxy_product_eq
#print axioms totient_test_error
#print axioms triple_error
#print axioms proxy_sub_profile_uniform
#print axioms proxy_twoBidiscs
#print axioms outside_outside_twoBidiscs
#print axioms outside_outside_reflected
end XiPrime8845.FengOutsideSquare


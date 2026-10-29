import FengOutsideAverage
import FengCrossAssembly

/-! The literal shifted outer Conrey/outside sum differs from the finite
mainProxy sum by o(1), on both reflected bidiscs. This is the replacement
step, not yet the limiting profile integral of that outer proxy. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengOutsideReplacement
open FengOutsideAverage FengCrossAssembly FengMixedInterior CoprimeEndpoint LogProfileSum
set_option maxHeartbeats 1000000

theorem outer_error_bound (L θ D : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hL : 0 < L) (hD : 0 ≤ D)
    (hx : ∀ g ∈ Ioc 0 (cutoff L θ),
      ‖conrey L g (coordinate L θ g) θ P A‖ ≤ D*SupportTail.eulerMass g 0)
    (hr : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.ratio A B L g‖ ≤ 2) :
    ‖outsideSum L θ P G A B-outsideProxy L θ P G A B‖ ≤
      2*D*averageError L θ θ G B := by
  rw [outsideSum,outsideProxy,← sub_div,← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hs : (∑ g ∈ Ioc 0 (cutoff L θ),
      ‖FengMixedShift.rawWeight (A/L) (B/L) g*conrey L g (coordinate L θ g) θ P A*
        FengAtG.outsideBlock (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B-
        FengMixedShift.rawWeight (A/L) (B/L) g*conrey L g (coordinate L θ g) θ P A*
        FengOutside.mainProxy (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B‖) ≤
      2*D*∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*SupportTail.eulerMass g 0*
        replacementError L (coordinate L θ g) θ g G B := by
    rw [mul_sum]
    apply sum_le_sum
    intro g hg
    rw [← mul_sub,FengMixedShift.mixed_weight_factor,norm_mul,norm_mul,norm_mul]
    have hE := euler_nonneg g (mem_Ioc.mp hg).1.ne'
    have h1 := mul_le_mul (hx g hg) (le_refl (replacementError L (coordinate L θ g) θ g G B))
      (norm_nonneg _) (mul_nonneg hD hE)
    have h2 := mul_le_mul (FengSharedLimit.zeroWeight_norm g (mem_Ioc.mp hg).1.ne') h1
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity : (0:ℝ)≤1/(g:ℝ))
    have h3 := mul_le_mul h2 (hr g hg) (norm_nonneg _)
      (by exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hD hE) (norm_nonneg _)))
    simpa only [replacementError,mul_assoc,mul_left_comm,mul_comm] using h3
  have hh := div_le_div_of_nonneg_right ((norm_sum_le _ _).trans hs) hL.le
  have he : Ioc 0 (cutoff L θ) = Icc 1 (cutoff L θ) := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  unfold averageError
  rw [he] at hh ⊢
  simpa only [mul_div_assoc,cutoff] using hh

theorem outside_sub_proxy_uniform (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hCθ : C*θ ≤ 1) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideSum L θ P G p.1 p.2-outsideProxy L θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hbound⟩ := FengSharedInterior.actual_coprime_bound P hP θ C θ hθ hC hθ.le
  have hh := averageError_uniform G hG θ C θ hθ hC hθ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps/(2*D+1) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),BareEulerUniform.ratio_uniform C θ hCθ 1 (by norm_num),
    Metric.tendstoUniformlyOn_iff.mp hh _ he] with L hL hr hsmall
  intro p hp
  have hx : ∀ g ∈ Ioc 0 (cutoff L θ),
      ‖conrey L g (coordinate L θ g) θ P p.1‖ ≤ D*SupportTail.eulerMass g 0 := by
    intro g hg
    have hgi : g ∈ Icc 1 (cutoff L θ) := by simpa only [mem_Ioc,mem_Icc,Nat.succ_le_iff] using hg
    have hu := translated_mem L θ θ hL ⟨hθ.le,le_rfl⟩ g hgi
    rw [conrey,norm_mul]
    exact (mul_le_mul (moebius_norm g) (hbound L hL g (mem_Ioc.mp hg).1.ne' _ hu p.1 hp.1)
      (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  have hr' : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.ratio p.1 p.2 L g‖ ≤ 2 := by
    intro g hg
    have h := hr g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2
    have ht := norm_add_le (BareEuler.ratio p.1 p.2 L g-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at ht
    linarith
  have hs := hsmall p.2 hp.2
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (averageError_nonneg L θ θ G p.2 hL.le)] at hs
  rw [dist_comm,dist_eq_norm,sub_zero]
  apply (outer_error_bound L θ D P G p.1 p.2 hL hD hx hr').trans_lt
  have ht := mul_le_mul_of_nonneg_left hs.le (show 0≤2*D by positivity)
  apply ht.trans_lt
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ (by positivity : 0<2*D+1)).mpr (by nlinarith)

theorem outside_sub_proxy_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideSum L PRZZAsymptotic.theta P G p.1 p.2-
        outsideProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs :=
  (outside_sub_proxy_uniform P G hP hG PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4)
    (by norm_num [PRZZAsymptotic.theta]) (by have := PRZZAsymptotic.radius_pos; positivity)
    ShiftedEulerUniform.witness_size).mono (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

theorem outside_sub_proxy_reflected (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => outsideSum L PRZZAsymptotic.theta P G (-p.2) (-p.1)-
        outsideProxy L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun _ => 0) atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (outside_sub_proxy_twoBidiscs P G hP hG)

#print axioms outer_error_bound
#print axioms outside_sub_proxy_uniform
#print axioms outside_sub_proxy_twoBidiscs
#print axioms outside_sub_proxy_reflected
end XiPrime8845.FengOutsideReplacement

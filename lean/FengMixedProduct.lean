import FengMixedInterior
import FengMixedLimit
import FengSharedLimit

/-! Actual Conrey/shared blocks with the explicit zero-shift outer weight phi(g)/g^2.
The finite profile main term is identified exactly and the averaged error is o(1),
including the cutoff endpoint and both reflected bidiscs. The generalized shifted
totient prefactor and other Feng blocks remain separate obligations. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengMixedProduct
open FengAtG FengMixedInterior FengMarkedProfile LogProfileSum CoprimeEndpoint
open FengSharedLimit (zeroWeight zeroWeight_norm)
set_option maxHeartbeats 1000000

def actualSum (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L U), zeroWeight g *
    conrey L g (coordinate L U g) θ P A *
    sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B)/(L:ℂ)

def mainSum (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L U), zeroWeight g *
    conreyMain g (coordinate L U g) θ P A * FengSharedInterior.main L g (coordinate L U g) θ G B)/(L:ℂ)

/-- Exact signed mixed measure, before taking a limit. No squarefree
restriction is inserted into the shared block. -/
theorem mainSum_eq (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    mainSum L U θ P G A B = FengMixedAbel.profileSum L U (OuterProfile.profile θ P G A B) := by
  rw [mainSum,FengMixedAbel.profileSum_eq,Finset.sum_div,Finset.sum_div]
  apply sum_congr rfl
  intro g hg
  have hg0 : g ≠ 0 := (mem_Ioc.mp hg).1.ne'
  have hgc : (g:ℂ) ≠ 0 := by exact_mod_cast hg0
  have htc : (g.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_eq_zero.not.mpr hg0)
  simp only [zeroWeight,conreyMain,FengSharedInterior.main,
    CoprimeEulerCompletion.zeroEulerMain,mark_eq_moment,
    TotientWeight.eulerMass_zero g hg0,OuterProfile.profile]
  push_cast
  by_cases hL : (L:ℂ) = 0
  · simp [hL]
  · field_simp

theorem actual_sub_main_bound (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hL : 0 < L) :
    ‖actualSum L U θ P G A B-mainSum L U θ P G A B‖ ≤
      averageRemainder L U θ P G A B := by
  rw [actualSum,mainSum,← sub_div,← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  unfold averageRemainder
  apply div_le_div_of_nonneg_right _ hL.le
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro g hg
  rw [show zeroWeight g * conrey L g (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B-
      zeroWeight g * conreyMain g (coordinate L U g) θ P A * FengSharedInterior.main L g (coordinate L U g) θ G B =
      zeroWeight g * (conrey L g (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B-
      conreyMain g (coordinate L U g) θ P A * FengSharedInterior.main L g (coordinate L U g) θ G B) by ring,norm_mul]
  exact mul_le_mul_of_nonneg_right (zeroWeight_norm g (mem_Ioc.mp hg).1.ne') (norm_nonneg _)

/-- The actual weighted product minus the literal signed profile sum is o(1).
The g cutoff grows with L, and u=0 is included in the averaged estimate. -/
theorem actual_sub_profile_uniform (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => actualSum L U θ P G p.1 p.2 -
      FengMixedAbel.profileSum L U (OuterProfile.profile θ P G p.1 p.2))
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have h := averageRemainder_uniform P G hP hG θ C U hθ hC hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),Metric.tendstoUniformlyOn_iff.mp h eps heps]
    with L hL hbound
  intro p hp
  have he := hbound p hp
  rw [dist_comm,Real.dist_eq,sub_zero] at he
  rw [dist_comm,dist_eq_norm,sub_zero,← mainSum_eq]
  exact (actual_sub_main_bound L U θ P G p.1 p.2 hL).trans_lt
    ((le_abs_self _).trans_lt he)

theorem actualSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have he := averageRemainder_twoBidiscs P G hP hG _ _ hθ hθ
  have hm := FengMixedLimit.mixed_profile_twoBidiscs P G
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Metric.tendstoUniformlyOn_iff.mp he (eps/2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hm (eps/2) (by positivity)] with L hL heL hmL
  intro p hp
  have hb := actual_sub_main_bound L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2 hL
  have he' := heL p hp
  have hm' := hmL p hp
  rw [dist_comm,Real.dist_eq,sub_zero] at he'
  rw [dist_comm,dist_eq_norm] at hm' ⊢
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)
    (mainSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)
    (-BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 3)
  rw [mainSum_eq] at hb ht
  linarith [le_abs_self (averageRemainder L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)]

theorem actualSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => -BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 1 3)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (actualSum_twoBidiscs P G hP hG)

#print axioms mainSum_eq
#print axioms actual_sub_main_bound
#print axioms actual_sub_profile_uniform
#print axioms actualSum_twoBidiscs
#print axioms actualSum_reflected
end XiPrime8845.FengMixedProduct


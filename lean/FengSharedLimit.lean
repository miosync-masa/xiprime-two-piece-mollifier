import FengMarkedCrossLimit

/-! The actual shared/shared blocks with the ZERO-SHIFT outer totient weight.
The shift-dependent generalized-totient prefactor is not substituted here.
Non-squarefree g are retained, unlike the Conrey outer weight. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSharedLimit
open FengAtG FengSharedInterior FengMarkedProfile LogProfileSum CoprimeEndpoint
set_option maxHeartbeats 1000000

def zeroWeight (g : ℕ) : ℂ := (g.totient:ℂ)/(g:ℂ)^2

theorem zeroWeight_norm (g : ℕ) (hg : g ≠ 0) : ‖zeroWeight g‖ ≤ 1/(g:ℝ) := by
  have hg0 : (0:ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero hg
  rw [zeroWeight,norm_div,norm_pow,Complex.norm_natCast,Complex.norm_natCast]
  calc
    _ ≤ (g:ℝ)/(g:ℝ)^2 := div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.totient_le g) (sq_nonneg _)
    _ = _ := by field_simp

def actualSum (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L U), zeroWeight g *
    sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ P A *
    sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B)/(L:ℂ)

def mainSum (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L U), zeroWeight g *
    main L g (coordinate L U g) θ P A * main L g (coordinate L U g) θ G B)/(L:ℂ)

theorem mainSum_eq (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    mainSum L U θ P G A B = markedProfileSum L U (OuterProfile.profile θ P G A B) := by
  unfold mainSum
  simp only [zeroWeight]
  rw [main_sum_profile]
  congr 1
  funext u
  simp only [OuterProfile.profile,ShiftedMobius.mainTerm,BetaKernel.D,↓reduceIte]
  ring

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
  rw [show zeroWeight g * sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B-
      zeroWeight g * main L g (coordinate L U g) θ P A * main L g (coordinate L U g) θ G B =
      zeroWeight g * (sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B-
      main L g (coordinate L U g) θ P A * main L g (coordinate L U g) θ G B) by ring,norm_mul]
  exact mul_le_mul_of_nonneg_right (zeroWeight_norm g (mem_Ioc.mp hg).1.ne') (norm_nonneg _)

theorem actualSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => 7*BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 5)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have he := averageRemainder_twoBidiscs P G hP hG _ _ hθ hθ
  have hm := FengMarkedCrossLimit.marked_profile_twoBidiscs P G
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
    (7*BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 5)
  rw [mainSum_eq] at hb ht
  linarith [le_abs_self (averageRemainder L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)]

theorem actualSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => 7*BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 1 5)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (actualSum_twoBidiscs P G hP hG)

#print axioms zeroWeight_norm
#print axioms mainSum_eq
#print axioms actual_sub_main_bound
#print axioms actualSum_twoBidiscs
#print axioms actualSum_reflected
end XiPrime8845.FengSharedLimit

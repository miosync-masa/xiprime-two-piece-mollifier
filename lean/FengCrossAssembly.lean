import FengLogMainTerm
import FengOutsideProfile

/-! Exact Conrey/Feng assembly and the remaining outside arithmetic obligation.
The only new limit hypothesis below is stated for the literal finite outside
sum. It is not an axiom, and no unconditional K02/K20 limit is claimed. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengCrossAssembly
open FengAtG FengMixedInterior LogProfileSum CoprimeEndpoint BetaKernel
set_option maxHeartbeats 1000000

def outsideSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g *
    conrey L g (coordinate L θ g) θ P A *
    outsideBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/(L:ℂ)

def fullSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g *
    conrey L g (coordinate L θ g) θ P A *
    fengBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/(L:ℂ)

def outsideProxy (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g *
    conrey L g (coordinate L θ g) θ P A *
    FengOutside.mainProxy ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/(L:ℂ)

/-- The actual raw-weighted outer error, still with its finite prime-power
budget. Decay of this right side is NOT asserted by the inequality. -/
theorem outside_proxy_error (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    ‖outsideSum L θ P G A B-outsideProxy L θ P G A B‖ ≤
      (∑ g ∈ Ioc 0 (cutoff L θ),
        ‖FengMixedShift.rawWeight (A/L) (B/L) g*conrey L g (coordinate L θ g) θ P A‖*
        FengOutside.errorBudget ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/|L| := by
  rw [outsideSum,outsideProxy,← sub_div,← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg L)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro g hg
  rw [← mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (FengOutside.outsideBlock_main_error _ g L _ θ G B)
    (norm_nonneg _)

theorem fullSum_decomposition (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    fullSum L θ P G A B = FengLogMainTerm.actualSum L θ P G A B+
      outsideSum L θ P G A B+FengMixedShift.actualSum L θ θ P G A B := by
  unfold fullSum FengLogMainTerm.actualSum outsideSum FengMixedShift.actualSum
  rw [← add_div,← add_div,← sum_add_distrib,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [fengBlock_decomposition _ g _ _ _ _ _ (mem_Ioc.mp hg).1.ne']
  ring

/-- The exact error identity exposes the missing prime-power limit. -/
theorem fullSum_residual (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    fullSum L θ P G A B-poleSum 0 2 (monomialIntegral A B θ P G) =
      (FengLogMainTerm.actualSum L θ P G A B-
        (2*monomialIntegral A B θ P G 1 1 3-2*monomialIntegral A B θ P G 1 0 2))+
      (FengMixedShift.actualSum L θ θ P G A B+monomialIntegral A B θ P G 1 1 3)+
      (outsideSum L θ P G A B-monomialIntegral A B θ P G 1 (-1) 1) := by
  rw [fullSum_decomposition,assemble02]
  ring

/-- Actual outside arithmetic convergence, not merely its candidate integral. -/
def OutsideAsymptotic (P G : Polynomial ℂ) : Prop :=
  TendstoUniformlyOn
    (fun L (p : ℂ × ℂ) => outsideSum L PRZZAsymptotic.theta P G p.1 p.2)
    (fun p => monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 (-1) 1)
    atTop ElementaryGcd.twoBidiscs

/-- Conditional assembly before the common theta^-2 normalization. -/
theorem fullSum_twoBidiscs_of_outside (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (hout : OutsideAsymptotic P G) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => poleSum 0 2 (monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G))
      atTop ElementaryGcd.twoBidiscs := by
  have hl := FengLogMainTerm.actualSum_twoBidiscs P G hP hG
  have hs := FengMixedShift.actualSum_twoBidiscs P G hP hG
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hl (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hs (eps/3) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hout (eps/3) (by positivity)] with L hL hS hO
  intro p hp
  have h1 := hL p hp
  have h2 := hS p hp
  have h3 := hO p hp
  rw [dist_comm,dist_eq_norm] at h1 h3 ⊢
  rw [dist_comm,dist_eq_norm,sub_neg_eq_add] at h2
  rw [fullSum_residual]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans_lt
  linarith

theorem fullSum_reflected_of_outside (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (hout : OutsideAsymptotic P G) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => fullSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => poleSum 0 2 (monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (fullSum_twoBidiscs_of_outside P G hP hG hout)

#print axioms fullSum_decomposition
#print axioms outside_proxy_error
#print axioms fullSum_residual
#print axioms fullSum_twoBidiscs_of_outside
#print axioms fullSum_reflected_of_outside
end XiPrime8845.FengCrossAssembly

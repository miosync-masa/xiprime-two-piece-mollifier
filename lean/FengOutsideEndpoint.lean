import FengOutsideBounds

/-! Actual off-g correction products in the endpoint window. This is not a
shared-prime estimate or the interior main-term asymptotic. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengOutsideEndpoint
open FengAtG FengOutsideBounds CoprimeEndpoint
set_option maxHeartbeats 1000000

def endpointProduct (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (g : ℕ) : ℝ :=
  let u := LogProfileSum.coordinate L U g
  ‖outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A *
    outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B‖

theorem outside_product_endpoint (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U eps : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U),
          (1/(g:ℝ))*endpointProduct L U θ P G A B g)/L < eps := by
  obtain ⟨DP,hDP,hPbound⟩ := outsideBlock_euler_bound P hP θ C U hθ hC hU.le
  obtain ⟨DG,hDG,hGbound⟩ := outsideBlock_euler_bound G hG θ C U hθ hC hU.le
  obtain ⟨δ,hδ,hδU,hsmall⟩ := FengLogEndpoint.euler_window_small U (DP*DG) eps
    hU (mul_nonneg hDP hDG) heps
  refine ⟨δ,hδ,hδU,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with L hL hs
  intro A B hA hB
  apply hs
  intro g hg
  have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
  have hu := EndpointAverage.endpoint_cutoff_mem L U δ hL g hg
  have hu' : LogProfileSum.coordinate L U g ∈ Set.Icc 0 U := ⟨hu.1,hu.2.trans hδU⟩
  have hx := hPbound L hL g hg0 _ hu' A hA
  have hy := hGbound L hL g hg0 _ hu' B hB
  have hh := mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hDP (euler_nonneg g hg0))
  simpa only [endpointProduct,norm_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

theorem outside_product_endpoint_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) (θ U eps : ℝ)
    (hθ : 0 < θ) (hU : 0 < U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ p ∈ ElementaryGcd.twoBidiscs,
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U),
          (1/(g:ℝ))*endpointProduct L U θ P G p.1 p.2 g)/L < eps := by
  obtain ⟨δ,hd,hdU,h⟩ := outside_product_endpoint P G hP hG θ (5*PRZZAsymptotic.R/4) U eps
    hθ (by have := PRZZAsymptotic.radius_pos; positivity) hU heps
  refine ⟨δ,hd,hdU,?_⟩
  filter_upwards [h] with L hL
  intro p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact hL p.1 p.2 hs.1 hs.2

#print axioms outside_product_endpoint
#print axioms outside_product_endpoint_twoBidiscs
end XiPrime8845.FengOutsideEndpoint

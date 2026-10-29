import FengSharedBounds
import FengOutsideBounds

/-! Endpoint control including the shared correction and the complete Feng
block. This does not identify the interior asymptotic with H20/H02/H22. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSharedEndpoint
open FengAtG FengSharedBounds FengLogBounds FengOutsideBounds FengLogEndpoint
open CoprimeEndpoint SupportTail
set_option maxHeartbeats 1000000

/-- All three actual blocks, with their original signs and nonsquarefree terms. -/
theorem fengBlock_euler_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖fengBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ D*eulerMass g 0 := by
  obtain ⟨D₁,hD₁,h₁⟩ := logBlock_euler_bound P hP θ C U V hθ hC hU hV
  obtain ⟨D₂,hD₂,h₂⟩ := outsideBlock_euler_bound P hP θ C U hθ hC hU
  obtain ⟨D₃,hD₃,h₃⟩ := sharedBlock_euler_bound P hP θ C U V hθ hC hU
  refine ⟨D₁+D₂+D₃,by positivity,?_⟩
  intro L hL g hg ht u hu A hA
  rw [fengBlock_decomposition _ g L u θ P A hg]
  apply (norm_add_le _ _).trans
  have hn := norm_add_le (logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A)
    (outsideBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A)
  have ha := h₁ L hL g hg ht u hu A hA
  have hb := h₂ L hL g hg u hu A hA
  have hc := h₃ L hL g hg ht u hu A hA
  nlinarith

/-- Generic endpoint transfer for two actual families with growing-g envelopes.
It also applies to mixed log/outside/shared products, without pointwise
convergence at the cutoff endpoint. -/
theorem block_product_endpoint
    (X Y : ℝ → ℕ → ℝ → ℂ → ℂ) (C U DX DY eps : ℝ)
    (hU : 0 < U) (hDX : 0 ≤ DX) (hDY : 0 ≤ DY) (heps : 0 < eps)
    (hX : ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 → |Real.log g/L| ≤ U →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C → ‖X L g u A‖ ≤ DX*eulerMass g 0)
    (hY : ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 → |Real.log g/L| ≤ U →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C → ‖Y L g u A‖ ≤ DY*eulerMass g 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*
          ‖X L g (LogProfileSum.coordinate L U g) A*
            Y L g (LogProfileSum.coordinate L U g) B‖)/L < eps := by
  obtain ⟨δ,hδ,hδU,hsmall⟩ := euler_window_small U (DX*DY) eps hU (mul_nonneg hDX hDY) heps
  refine ⟨δ,hδ,hδU,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hsmall] with L hL hs
  intro A B hA hB
  apply hs
  intro g hg
  have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hg0
  have hgexp : (g:ℝ) ≤ Real.exp (L*U) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  have hglog : Real.log g ≤ L*U := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<g)).mpr hgexp
  have ht := ShiftWeights.normalized_log_mem g L U hg1 hL hglog
  have ht' : |Real.log g/L| ≤ U := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hu := EndpointAverage.endpoint_cutoff_mem L U δ hL g hg
  have hu' : LogProfileSum.coordinate L U g ∈ Set.Icc 0 U := ⟨hu.1,hu.2.trans hδU⟩
  have hx := hX L hL g hg0 ht' _ hu' A hA
  have hy := hY L hL g hg0 ht' _ hu' B hB
  have hh := mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hDX (euler_nonneg g hg0))
  simpa only [norm_mul,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Both choices are actual coefficients: false selects sharedBlock alone,
true selects the full Feng block before theta^-2. -/
def selectedBlock (full : Bool) := if full then fengBlock else sharedBlock

theorem selectedBlock_euler_bound (full : Bool) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ U → ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖selectedBlock full ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ D*eulerMass g 0 := by
  cases full with
  | false => exact sharedBlock_euler_bound P hP θ C U U hθ hC hU
  | true => exact fengBlock_euler_bound P hP θ C U U hθ hC hU hU

theorem product_endpoint_twoBidiscs (leftFull rightFull : Bool)
    (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ U eps : ℝ) (hθ : 0 < θ) (hU : 0 < U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ U ∧ ∀ᶠ L : ℝ in atTop,
      ∀ p ∈ ElementaryGcd.twoBidiscs,
        (∑ g ∈ Ioc (cutoff L (U-δ)) (cutoff L U), (1/(g:ℝ))*
          ‖selectedBlock leftFull ⌊Real.exp (L*LogProfileSum.coordinate L U g)⌋₊
              g L (LogProfileSum.coordinate L U g) θ P p.1 *
            selectedBlock rightFull ⌊Real.exp (L*LogProfileSum.coordinate L U g)⌋₊
              g L (LogProfileSum.coordinate L U g) θ G p.2‖)/L < eps := by
  have hC : 0 ≤ 5*PRZZAsymptotic.R/4 := by have := PRZZAsymptotic.radius_pos; positivity
  obtain ⟨DP,hDP,hPb⟩ := selectedBlock_euler_bound leftFull P hP θ _ U hθ hC hU.le
  obtain ⟨DG,hDG,hGb⟩ := selectedBlock_euler_bound rightFull G hG θ _ U hθ hC hU.le
  obtain ⟨δ,hd,hdU,h⟩ := block_product_endpoint
    (fun L g u A => selectedBlock leftFull ⌊Real.exp (L*u)⌋₊ g L u θ P A)
    (fun L g u A => selectedBlock rightFull ⌊Real.exp (L*u)⌋₊ g L u θ G A)
    (5*PRZZAsymptotic.R/4) U DP DG eps hU hDP hDG heps hPb hGb
  refine ⟨δ,hd,hdU,?_⟩
  filter_upwards [h] with L hL
  intro p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact hL p.1 p.2 hs.1 hs.2

#print axioms fengBlock_euler_bound
#print axioms block_product_endpoint
#print axioms selectedBlock_euler_bound
#print axioms product_endpoint_twoBidiscs
end XiPrime8845.FengSharedEndpoint

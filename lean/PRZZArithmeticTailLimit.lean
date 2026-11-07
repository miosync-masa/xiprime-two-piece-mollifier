import PRZZWeilDIMainBound

/-! Actual paired Fourier-tail removal for the explicit arithmetic model.
The cutoff threshold may depend on T,N and the shifts. No polynomial
height bound for that threshold, or uniform-J Weil/DI budget, is inferred. -/
noncomputable section
open scoped ContDiff Topology
open Complex Set Filter
namespace XiPrime8845.PRZZArithmeticTailLimit
open PRZZCentralMainAssembly
set_option maxHeartbeats 6000000

def pairedTail (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  branchPair (fun Phi alpha beta => tailPart P F Phi K
    (PRZZLiteralExhaustion.spatialLength T) J N a T eps alpha beta) Phi T alpha beta

theorem paired_tail_tendsto (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => pairedTail P F Phi K J N a T eps alpha beta) atTop (𝓝 0) := by
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]
    exact neg_ne_zero.mpr hs
  have h1 := tail_part_tendsto P F Phi K (PRZZLiteralExhaustion.spatialLength T) N a
    hF hl hr hPhi hsPhi T eps hT alpha beta hs
  have h2 := tail_part_tendsto P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
    K (PRZZLiteralExhaustion.spatialLength T) N a hF hl hr hd.1 hd.2 T eps hT (-beta) (-alpha) hs'
  simpa only [pairedTail,branchPair,add_zero] using h1.add h2

theorem tail_eventually_power (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps rate : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    ∃ J0 : ℕ, ∀ J ≥ J0, ‖pairedTail P F Phi K J N a T eps alpha beta‖ ≤ T^(-rate) := by
  have h := (paired_tail_tendsto P F Phi K N a hF hl hr hPhi hsPhi T eps hT
    alpha beta ha hb hs).norm
  have hh : ∀ᶠ J : ℕ in atTop, ‖pairedTail P F Phi K J N a T eps alpha beta‖ < T^(-rate) :=
    h.eventually (eventually_lt_nhds (by simpa using Real.rpow_pos_of_pos hT (-rate)))
  obtain ⟨J0,hJ⟩ := eventually_atTop.mp hh
  exact ⟨J0,fun J hj => (hJ J hj).le⟩

/-- The complete arithmetic residual is independent of the auxiliary
finite Fourier split, although its positive and negative budgets need not be. -/
theorem residual_independent (P F Phi : ℝ → ℂ) (K J J' N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    arithmeticResidual P F Phi K J N a T eps alpha beta =
      arithmeticResidual P F Phi K J' N a T eps alpha beta := by
  have h1 := model_main_arithmetic P F Phi K J N a T eps alpha beta
  have h2 := model_main_arithmetic P F Phi K J' N a T eps alpha beta
  linear_combination h2-h1

#print axioms paired_tail_tendsto
#print axioms tail_eventually_power
#print axioms residual_independent
end XiPrime8845.PRZZArithmeticTailLimit

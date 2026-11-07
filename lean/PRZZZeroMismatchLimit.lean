import PRZZCentralMainAssembly
import PRZZZeroDualExhaustion

/-! The native zero grid and the unrestricted zero exhaustion have
different cutoffs. Their ACTUAL difference converges to zeroMismatch;
zeroMismatch is not asserted to vanish. Auxiliary-cutoff errors are
quantified at fixed height, not at an unproved height-dependent rate. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZZeroMismatchLimit
open PRZZCentralMainAssembly PRZZMellinSeparation
set_option maxHeartbeats 6000000

def cutoffDifference (S : ℝ → ℝ) (P F Phi : ℝ → ℂ) (K L N : ℕ)
    (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  branchPair (fun Phi alpha beta => zeroPart P F Phi K
    (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta-
      PRZZZeroDualExhaustion.finitePair S L N a Phi alpha beta T

theorem difference_error (S : ℝ → ℝ) (P F Phi : ℝ → ℂ) (K L N : ℕ)
    (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ) :
    cutoffDifference S P F Phi K L N a T eps alpha beta-
      zeroMismatch P F Phi K N a T eps alpha beta =
    PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T)-
      PRZZZeroDualExhaustion.finitePair S L N a Phi alpha beta T := by
  unfold cutoffDifference zeroMismatch
  ring

theorem difference_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ) (T eps : ℝ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => cutoffDifference S P F Phi K L N a T eps alpha beta) atTop
      (𝓝 (zeroMismatch P F Phi K N a T eps alpha beta)) := by
  have h := PRZZZeroDualExhaustion.pair_limit S hS hm hlo hhi hleft hright N a Phi alpha beta T
    ha hb hPhi hcPhi hsPhi hT hs hn
  have hc : Tendsto (fun _ : ℕ => branchPair (fun Phi alpha beta => zeroPart P F Phi K
      (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta) atTop
      (𝓝 (branchPair (fun Phi alpha beta => zeroPart P F Phi K
        (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta) Phi T alpha beta)) := tendsto_const_nhds
  have he : (fun t : ℝ => Phi (t/T)) = PRZZMellinSeparation.scaledCutoff Phi T := by
    funext t
    simp [PRZZMellinSeparation.scaledCutoff,div_eq_mul_inv,mul_comm]
  rw [he] at h
  exact hc.sub h

/-- Quantitative auxiliary L removal at a fixed height. No polynomial
bound for L0(T) and no bound on the native cutoffDifference are assumed. -/
theorem eventual_power (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ) (T eps rate : ℝ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    ∃ L0 : ℕ, ∀ L ≥ L0,
      ‖cutoffDifference S P F Phi K L N a T eps alpha beta-
        zeroMismatch P F Phi K N a T eps alpha beta‖ ≤ T^(-rate) ∧
      ‖zeroMismatch P F Phi K N a T eps alpha beta‖ ≤
        ‖cutoffDifference S P F Phi K L N a T eps alpha beta‖+T^(-rate) := by
  have h := difference_limit S hS hm hlo hhi hleft hright P F Phi K N a T eps alpha beta
    ha hb hPhi hcPhi hsPhi hT hs hn
  obtain ⟨L0,hL0⟩ := Metric.tendsto_atTop.mp h (T^(-rate)) (Real.rpow_pos_of_pos hT _)
  refine ⟨L0,?_⟩
  intro L hL
  have hh : ‖cutoffDifference S P F Phi K L N a T eps alpha beta-
      zeroMismatch P F Phi K N a T eps alpha beta‖ ≤ T^(-rate) := by
    simpa only [dist_eq_norm] using (hL0 L hL).le
  refine ⟨hh,?_⟩
  have he : zeroMismatch P F Phi K N a T eps alpha beta =
      cutoffDifference S P F Phi K L N a T eps alpha beta-
        (cutoffDifference S P F Phi K L N a T eps alpha beta-zeroMismatch P F Phi K N a T eps alpha beta) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hh)

#print axioms difference_error
#print axioms difference_limit
#print axioms eventual_power
end XiPrime8845.PRZZZeroMismatchLimit

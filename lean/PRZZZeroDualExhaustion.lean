import PRZZDualSmooth

/-! Genuine Gamma-weighted zero exhaustion in the second AFE branch.
The scaled Gamma cutoff is proved smooth and compactly supported, then
both actual finite spatial/gap exhaustions are inserted into cross cancellation. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroDualExhaustion
open PRZZZeroOuterMellin PRZZZeroExhaustionCross
set_option maxHeartbeats 7000000

def dualCutoff (Phi : ℝ → ℂ) (a b : ℂ) (T y : ℝ) : ℂ :=
  Phi y*PRZZAFEDual.dualMultiplier a b (T*y)

theorem cutoff_regular (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) (a b : ℂ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (T : ℝ) :
    ContDiff ℝ ∞ (dualCutoff Phi a b T) ∧ HasCompactSupport (dualCutoff Phi a b T) ∧
      Function.support (dualCutoff Phi a b T) ⊆ Icc (1:ℝ) 2 := by
  refine ⟨hPhi.mul ((PRZZDualSmooth.multiplier_contDiff a b ha hb).comp
    (contDiff_const.mul contDiff_id)),?_,?_⟩
  · exact hcPhi.mul_right
  · intro y hy
    apply hsPhi
    intro hz
    exact hy (by simp [dualCutoff,hz])

theorem actual_dual_zero_time (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (T : ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    arithmeticZero N a (fun _ => 1) (fun _ => 1) (dualCutoff Phi alpha beta T) (-beta) (-alpha) T =
      ∫ t in Icc T (2*T), (Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t)*
        PRZZZeroCross.zero N a (-beta) (-alpha) t := by
  obtain ⟨hf,hc,hp⟩ := cutoff_regular Phi hPhi hcPhi hsPhi alpha beta ha hb T
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  rw [actual_zero_time N a _ _ _ T hf hc hp hT hs' hn']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have he : T*(t/T)=t := by field_simp
  simp only [dualCutoff,he]

def finitePair (S : ℝ → ℝ) (L N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ)
    (alpha beta : ℂ) (T : ℝ) : ℂ :=
  finiteArithmeticZero S L N a (fun _ => 1) (fun _ => 1) Phi alpha beta T+
    finiteArithmeticZero S L N a (fun _ => 1) (fun _ => 1) (dualCutoff Phi alpha beta T) (-beta) (-alpha) T

theorem pair_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => finitePair S L N a Phi alpha beta T) atTop
      (𝓝 (PRZZZeroCoupled.zeroPair N a alpha beta T (fun t => Phi (t/T)))) := by
  obtain ⟨hf,hc,hp⟩ := cutoff_regular Phi hPhi hcPhi hsPhi alpha beta ha hb T
  have hs' : -beta+-alpha ≠ 0 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hs
  have hn' : ‖-beta+-alpha‖ ≤ 1/8 := by
    simpa only [show -beta+-alpha = -(alpha+beta) by ring,norm_neg] using hn
  have hd := arithmetic_exhaustion S hS hm hlo hhi hleft hright N a (fun _ => 1) (fun _ => 1)
    Phi alpha beta T hPhi hcPhi hsPhi hT hs hn
  have hu := arithmetic_exhaustion S hS hm hlo hhi hleft hright N a (fun _ => 1) (fun _ => 1)
    (dualCutoff Phi alpha beta T) (-beta) (-alpha) T hf hc hp hT hs' hn'
  rw [actual_zero_time N a Phi alpha beta T hPhi hcPhi hsPhi hT hs hn] at hd
  rw [actual_dual_zero_time N a Phi alpha beta ha hb T hPhi hcPhi hsPhi hT hs hn] at hu
  exact hd.add hu

theorem cross_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (N : ℕ) (a : ℕ → ℂ) (Phi : ℝ → ℂ) (alpha beta : ℂ) (T : ℝ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => PRZZCoupledAFE.correctionPair N a alpha beta T (fun t => Phi (t/T))+
      finitePair S L N a Phi alpha beta T) atTop
      (𝓝 (∫ t in Icc T (2*T), Phi (t/T)*PRZZZeroCross.gammaDefect N a alpha beta t)) := by
  have h := (pair_limit S hS hm hlo hhi hleft hright N a Phi alpha beta T ha hb
    hPhi hcPhi hsPhi hT hs hn).const_add
    (PRZZCoupledAFE.correctionPair N a alpha beta T (fun t => Phi (t/T)))
  rwa [PRZZZeroCoupled.integrated_cross N a alpha beta ha hb hs hn T hT
    (fun t => Phi (t/T)) (hPhi.continuous.comp (continuous_id.div_const T))] at h

#print axioms cutoff_regular
#print axioms actual_dual_zero_time
#print axioms pair_limit
#print axioms cross_limit
end XiPrime8845.PRZZZeroDualExhaustion

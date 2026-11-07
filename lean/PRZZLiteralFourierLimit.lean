import PRZZFourierExhaustion
import PRZZLiteralExhaustion

/-! The J-limit of the actual literal model, including the original
strict spatial windows, arithmetic cutoff values and genuine dual profile.
The limit is an absolutely convergent series of integrated Fourier pairs. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZLiteralFourierLimit
open PRZZMellinSeparation PRZZSmallCentralLiteral PRZZFourierExhaustion PRZZNativeCentralLiteral
set_option maxHeartbeats 9000000

def cellPrefix (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  PRZZSignedCentral.signedLiteral 0 N d D 2 T M a G H F Phi beta alpha (alpha+beta)+
    PRZZAStar.literal N d D ((J:ℝ)+1) T a G H (fun y => F (M⁻¹*y))
      (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
    PRZZSignedCentral.signedLiteral (-1) N d D ((J:ℝ)+1) T M a G H F Phi beta alpha (alpha+beta)

def cellFull (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  ∑ z ∈ PRZZAStar.indices N d D 2, allModes d F G H Phi a T M alpha beta z

theorem cellPrefix_time (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    cellPrefix N d J D T M a F G H Phi alpha beta =
      ∑ z ∈ PRZZAStar.indices N d D 2, ∫ t in Icc T (2*T), centralTerm d J F G H Phi a T M alpha beta z t := by
  have hi (z : PRZZAStar.Index) (hz : z ∈ PRZZAStar.indices N d D 2) :
      Integrable (centralTerm d J F G H Phi a T M alpha beta z) := by
    have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact term_integrable d J F G H Phi a T M alpha beta z hF.continuous hPhi hT hM
      (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs hsF hsPhi
  unfold cellPrefix
  rw [← PRZZSignedCentral.central_time N d J D T M a G H F Phi beta alpha (alpha+beta)
    hF.continuous hPhi hT hM hs hsF hsPhi]
  change (∫ t : ℝ, ∑ z ∈ PRZZAStar.indices N d D 2, centralTerm d J F G H Phi a T M alpha beta z t) = _
  rw [integral_finsetSum _ hi]
  apply sum_congr rfl
  intro z hz
  exact (PRZZFreezeRemovedLiteral.profile_time Phi _ T hT hsPhi).symm

theorem cell_tendsto (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => cellPrefix N d J D T M a F G H Phi alpha beta) atTop
      (𝓝 (cellFull N d D T M a F G H Phi alpha beta)) := by
  simp_rw [cellPrefix_time N d _ D T M a F G H Phi alpha beta hF hPhi hsF hsPhi hT hM hs]
  unfold cellFull
  apply tendsto_finsetSum
  intro z hz
  have hp := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
  exact central_time_tendsto d F G H Phi a hF hPhi hsF hsPhi T M alpha beta z hT hM
    (mem_Icc.mp hp.1).1 (mem_Icc.mp hp.2).1 hs

def rowFull (L N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
    cellFull N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps) T ((2:ℝ)^s)
      a (PRZZWRowLimit.profile P) G H Phi alpha beta

theorem row_tendsto (L N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => cleanRowLiteral L J N P G H Phi a T Q eps alpha beta) atTop
      (𝓝 (rowFull L N P G H Phi a T Q eps alpha beta)) := by
  have hp := PRZZWRowLimit.profile_regular P hP hl hr
  change Tendsto (fun J : ℕ => ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
    ∑ d ∈ Icc 1 N, cellPrefix N d J (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) a (PRZZWRowLimit.profile P) G H Phi alpha beta) atTop _
  unfold rowFull
  apply tendsto_finsetSum
  intro s hss
  apply tendsto_finsetSum
  intro d hd
  exact cell_tendsto N d _ T _ a _ G H Phi alpha beta hp.1 hPhi hp.2.2 hsPhi hT (by positivity) hs

def centralFull (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, rowFull L N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a T ((2:ℝ)^p.1) eps alpha beta

theorem central_tendsto (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => cleanCentralLiteral P F Phi K L J N a T eps alpha beta) atTop
      (𝓝 (centralFull P F Phi K L N a T eps alpha beta)) := by
  unfold cleanCentralLiteral centralFull
  apply tendsto_finsetSum
  intro p hp
  exact row_tendsto L N F _ _ Phi a hF hl hr hPhi hsPhi T _ eps hT alpha beta hs

def fullModel (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
    ((centralFull P F Phi K (PRZZLiteralExhaustion.spatialLength T) N a T eps alpha beta+
      centralFull P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
        K (PRZZLiteralExhaustion.spatialLength T) N a T eps (-beta) (-alpha))-
      PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T))+
    ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t

theorem model_tendsto (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => PRZZLiteralExhaustion.limitModel P F Phi K J N a T eps alpha beta) atTop
      (𝓝 (fullModel P F Phi K N a T eps alpha beta)) := by
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := central_tendsto P F Phi K (PRZZLiteralExhaustion.spatialLength T) N a
    hF hl hr hPhi hsPhi T eps hT alpha beta hs
  have h2 := central_tendsto P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
    K (PRZZLiteralExhaustion.spatialLength T) N a hF hl hr hd.1 hd.2 T eps hT (-beta) (-alpha) hs'
  exact (tendsto_const_nhds.add ((h1.add h2).sub tendsto_const_nhds)).add tendsto_const_nhds

#print axioms cellPrefix_time
#print axioms cell_tendsto
#print axioms row_tendsto
#print axioms central_tendsto
#print axioms model_tendsto
end XiPrime8845.PRZZLiteralFourierLimit


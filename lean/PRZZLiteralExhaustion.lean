import PRZZSmallCentralLiteral

/-! Genuine removal of the original L-exhaustion at a fixed Fourier cutoff.
Strict-small spatial indices form a finite set at each height, and the
native rejection vanishes eventually on the entire arithmetic grid.
No convergence premise on the literal model is used. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZLiteralExhaustion
open PRZZMellinSeparation PRZZSmallCentralLiteral
set_option maxHeartbeats 5000000

def spatialLength (T : ℝ) : ℕ := ⌈T^(4:ℝ)⌉₊+1

theorem strict_index_lt (T : ℝ) (s : ℕ) (hs : (2:ℝ)^s < T^(4:ℝ)) :
    s < spatialLength T := by
  have hsR : (s:ℝ) < T^(4:ℝ) := (show (s:ℝ) ≤ (2:ℝ)^s by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := s)))).trans_lt hs
  have hc : T^(4:ℝ) ≤ (⌈T^(4:ℝ)⌉₊:ℝ) := Nat.le_ceil _
  have hsn : s < ⌈T^(4:ℝ)⌉₊ := by exact_mod_cast hsR.trans_le hc
  unfold spatialLength
  omega

theorem strict_grid_stable (T : ℝ) (L : ℕ) (hL : spatialLength T ≤ L) :
    (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)) =
      (range (spatialLength T+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)) := by
  classical
  ext s
  simp only [Finset.mem_filter,Finset.mem_range]
  constructor
  · intro hs
    exact ⟨by have := strict_index_lt T s hs.2; omega,hs.2⟩
  · intro hs
    exact ⟨by have := strict_index_lt T s hs.2; omega,hs.2⟩

theorem clean_central_stable (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (hL : spatialLength T ≤ L) :
    cleanCentralLiteral P F Phi K L J N a T eps alpha beta =
      cleanCentralLiteral P F Phi K (spatialLength T) J N a T eps alpha beta := by
  unfold cleanCentralLiteral
  apply sum_congr rfl
  intro p hp
  unfold cleanRowLiteral
  rw [strict_grid_stable T L hL]

def limitModel (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
    ((cleanCentralLiteral P F Phi K (spatialLength T) J N a T eps alpha beta+
      cleanCentralLiteral P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
        K (spatialLength T) J N a T eps (-beta) (-alpha))-
      PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T))+
    ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t

/-- One exhaustion threshold works for every Fourier cutoff and both
time profiles; the limiting expression still retains its explicit J. -/
theorem model_eventually_eq (P : ℝ → ℂ) (K N : ℕ)
    (hsP : Function.support (PRZZWRowLimit.profile P) ⊆ Icc (1/2:ℝ) 3)
    (T eps : ℝ) (hT : 0 < T) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in atTop, ∀ (J : ℕ) (F Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ),
      literalModel P F Phi K L J N a T eps alpha beta =
        limitModel P F Phi K J N a T eps alpha beta := by
  filter_upwards [centralLiteral_clean_eventually P K N hsP T eps hT hheight,
    eventually_ge_atTop (spatialLength T)] with L hL hsize
  intro J F Phi a alpha beta
  unfold literalModel limitModel
  rw [hL J F Phi a alpha beta,hL J F (PRZZKeptLiteral.dualProfile Phi T alpha beta) a (-beta) (-alpha),
    clean_central_stable P F Phi K L J N a T eps alpha beta hsize,
    clean_central_stable P F (PRZZKeptLiteral.dualProfile Phi T alpha beta) K L J N a T eps (-beta) (-alpha) hsize]

theorem model_tendsto (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (hsP : Function.support (PRZZWRowLimit.profile P) ⊆ Icc (1/2:ℝ) 3)
    (T eps : ℝ) (hT : 0 < T) (hheight : 8 ≤ T^(1-eps)) (alpha beta : ℂ) :
    Tendsto (fun L : ℕ => literalModel P F Phi K L J N a T eps alpha beta) atTop
      (𝓝 (limitModel P F Phi K J N a T eps alpha beta)) := by
  have he := (model_eventually_eq P K N hsP T eps hT hheight).mono
    (fun L hL => hL J F Phi a alpha beta)
  exact tendsto_const_nhds.congr' (he.mono (fun L hL => hL.symm))

#print axioms strict_index_lt
#print axioms strict_grid_stable
#print axioms clean_central_stable
#print axioms model_eventually_eq
#print axioms model_tendsto
end XiPrime8845.PRZZLiteralExhaustion


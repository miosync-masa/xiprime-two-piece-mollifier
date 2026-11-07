import PRZZDualProfileUniform
import PRZZMellinSeminorm
import PRZZWeilDIMainBound

/-! A HEIGHT-UNIFORM weighted Mellin mass for the genuine Gamma dual
profile, and its substitution into the actual indexed Weil/DI grid.
Spatial and second-arithmetic-profile constants remain explicit. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZDualMellinUniform
open PRZZMellinSeparation PRZZCentralGridWeilDI PRZZActualAggregate
set_option maxHeartbeats 10000000

theorem dual_linear_mass (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S →
      (∫ t : ℝ, (1+|t|)*‖mellin (PRZZKeptLiteral.dualProfile Phi T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) (t*I)‖) ≤ M := by
  obtain ⟨U,hU,h⟩ := PRZZDualProfileUniform.profile_uniform Phi hPhi hcPhi hsPhi S hS
  have h0 := hU 0
  have h1 := hU 1
  have h2 := hU 2
  have h3 := hU 3
  refine ⟨4*(Real.log 2*(U 0+2*U 1+12*U 2+8*U 3))*(∫ t : ℝ, (1+t^2)⁻¹),?_,?_⟩
  · have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hi : 0 ≤ ∫ t : ℝ, (1+t^2)⁻¹ := integral_nonneg (fun t => by positivity)
    positivity
  · filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T h hsmall
    intro A B hA hB
    have hf : ContDiff ℝ ∞ (PRZZKeptLiteral.dualProfile Phi T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) :=
      hPhi.mul ((PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).comp
        (contDiff_const.mul contDiff_id))
    have hs := (PRZZKeptLiteral.dual_profile_regular Phi hPhi.continuous hsPhi T _ _
      (hsmall.2 A hA) (hsmall.2 B hB)).2
    exact PRZZMellinSeminorm.uniform_mass_from_jets _ hf hs U hU (h A B hA hB)

/-- The actual grid budget with its common time Mellin mass removed. -/
def gridEnvelope (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b T eCut : ℝ) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ range Kgrid ×ˢ range Kgrid,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
      (1/(2*Real.pi)) *
        (∫ q, ‖PRZZAStarIntegralBound.common N d T (((2:ℝ)^s)/2) (3*(2:ℝ)^s)
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) beta alpha q‖) *
        totalBudget (C (p.2,s)) (w (p.2,s)) (caps (p.2,s)) js eps eta b T
          (PRZZActualSignedBranches.frequencyBound d
            (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) ((J:ℝ)+1)) N d K

theorem grid_factor (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b T eCut : ℝ)
    (Phi : ℝ → ℂ) (alpha beta : ℂ) :
    gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta =
      gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut alpha beta*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  simp only [gridBudget,gridEnvelope,PRZZCentralArithmeticJoin.positiveBudget,sum_mul]

theorem grid_envelope_nonneg (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hw : ∀ i q, 0 ≤ w i q)
    (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b T eCut : ℝ)
    (hT : 0 ≤ T) (alpha beta : ℂ) :
    0 ≤ gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut alpha beta := by
  unfold gridEnvelope
  apply sum_nonneg; intro p hp
  apply sum_nonneg; intro s hs
  apply sum_nonneg; intro d hd
  apply mul_nonneg
  · exact mul_nonneg (by positivity) (integral_nonneg (fun q => norm_nonneg _))
  · exact totalBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ (hC _) (hw _) hT (by positivity)

/-- Uniform time-mass absorption in EVERY actual grid, including the
genuine dual branch. Constants are fixed before all grid sizes and scales. -/
theorem dual_grid_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
        (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ),
      (∀ i, 0 ≤ C i) → (∀ i q, 0 ≤ w i q) →
      ∀ (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b eCut : ℝ) (alpha beta : ℂ),
      gridBudget caps w C js K Kgrid L J N eps eta b T eCut
        (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) alpha beta ≤
      gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut alpha beta*M := by
  obtain ⟨M,hM,h⟩ := dual_linear_mass Phi hPhi hcPhi hsPhi S hS
  refine ⟨M,hM,?_⟩
  filter_upwards [h,eventually_ge_atTop (0:ℝ)] with T h hT
  intro A B hA hB caps w C hC hw js K Kgrid L J N eps eta b eCut alpha beta
  rw [grid_factor]
  exact mul_le_mul_of_nonneg_left (h A B hA hB)
    (grid_envelope_nonneg caps w C hC hw js K Kgrid L J N eps eta b T eCut hT alpha beta)

/-- Both time Mellin masses are absorbed into ONE constant, chosen before
height, shifts, grid sizes and the indexed arithmetic constants. -/
theorem paired_grid_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
        (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ),
      (∀ i, 0 ≤ C i) → (∀ i q, 0 ≤ w i q) →
      ∀ (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b eCut : ℝ),
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta+
        gridBudget caps w C js K Kgrid L J N eps eta b T eCut
          (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha) ≤
      M*(gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut alpha beta+
        gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut (-beta) (-alpha)) := by
  obtain ⟨D,hD,h⟩ := dual_linear_mass Phi hPhi hcPhi hsPhi S hS
  obtain ⟨M0,hM0,hbase⟩ := PRZZMellinMoment.linear_mass Phi 1 2 (by norm_num) hsPhi hPhi
  have he : scaledCutoff Phi 1 = Phi := by funext x; simp [scaledCutoff]
  have h0 : (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) = M0 := by
    simpa only [he] using (hbase 1 (by norm_num)).2
  refine ⟨M0+D,add_nonneg hM0 hD,?_⟩
  filter_upwards [h,eventually_ge_atTop (0:ℝ)] with T h hT
  intro A B hA hB caps w C hC hw js K Kgrid L J N eps eta b eCut
  dsimp only
  rw [grid_factor,grid_factor,h0]
  have hp := grid_envelope_nonneg caps w C hC hw js K Kgrid L J N eps eta b T eCut hT
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  have hm := grid_envelope_nonneg caps w C hC hw js K Kgrid L J N eps eta b T eCut hT
    (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ)))
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left (show M0 ≤ M0+D by linarith) hp)
    (mul_le_mul_of_nonneg_left ((h A B hA hB).trans (show D ≤ M0+D by linarith)) hm)
  exact hh.trans_eq (by ring)

/-- Substitute the uniform paired mass into the ACTUAL evaluatedBudget
on the right of WeilDIMainBound.moment_evaluated. -/
theorem evaluated_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
        (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ),
      (∀ i, 0 ≤ C i) → (∀ i q, 0 ≤ w i q) →
      ∀ (P F : ℝ → ℂ) (js : List ℕ) (K Kgrid J N : ℕ) (epsA etaA b eps : ℝ),
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let L := PRZZLiteralExhaustion.spatialLength T
      PRZZWeilDIMainBound.evaluatedBudget caps w C P F Phi js K Kgrid J N epsA etaA b T eps alpha beta ≤
        ‖PRZZCentralMainAssembly.zeroMismatch P F Phi Kgrid N a T eps alpha beta‖+
          M*(gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps alpha beta+
            gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps (-beta) (-alpha))+
          ‖PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
            PRZZCentralMainAssembly.negativePart P F Phi Kgrid L J N a T eps alpha beta) Phi T alpha beta‖+
          ‖PRZZCentralMainAssembly.branchPair (fun Phi alpha beta =>
            PRZZCentralMainAssembly.tailPart P F Phi Kgrid L J N a T eps alpha beta) Phi T alpha beta‖ := by
  obtain ⟨M,hM,h⟩ := paired_grid_bound Phi hPhi hcPhi hsPhi S hS
  refine ⟨M,hM,?_⟩
  filter_upwards [h] with T h
  intro A B hA hB caps w C hC hw P F js K Kgrid J N epsA etaA b eps
  dsimp only
  unfold PRZZWeilDIMainBound.evaluatedBudget
  exact add_le_add (add_le_add (add_le_add le_rfl
    (h A B hA hB caps w C hC hw js K Kgrid (PRZZLiteralExhaustion.spatialLength T) J N epsA etaA b eps)) le_rfl) le_rfl

#print axioms dual_linear_mass
#print axioms grid_factor
#print axioms grid_envelope_nonneg
#print axioms dual_grid_bound
#print axioms paired_grid_bound
#print axioms evaluated_uniform
end XiPrime8845.PRZZDualMellinUniform

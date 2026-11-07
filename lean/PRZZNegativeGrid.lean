import PRZZNegativeOuter
import PRZZDualMellinUniform

/-! Actual negative grid, including both genuine AFE branches. Arithmetic
constants remain indexed by spatial/second arithmetic scale; only the
common Mellin mass is absorbed uniformly before height. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZNegativeGrid
open PRZZCentralArithmeticJoin PRZZCentralMainAssembly PRZZCentralGridWeilDI
open PRZZMellinSeparation PRZZActualAggregate PRZZDualMellinUniform
set_option maxHeartbeats 10000000

theorem negative_grid_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ,
      (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧
      ∀ Kgrid L J N : ℕ, ∀ T eCut : ℝ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖negativePart P F Phi Kgrid L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eCut alpha beta‖ ≤
        gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  have hex (i : ℕ × ℕ) := PRZZNegativeOuter.negative_cell_weil_di hWeil hDI K hK js eps eta b S Z ((2:ℝ)^i.2)
    heps heta hb hS hZ (by positivity) (PRZZWRowLimit.profile P)
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^i.1)) (PRZZWRowLimit.profile F)
    hp.1 hp.2.1
    (hp.1.continuous.comp (continuous_const.mul continuous_id))
    (hp.2.1.comp_homeomorph (Homeomorph.mulLeft₀ (((2:ℝ)^i.1)⁻¹) (by positivity)))
    hf.1.continuous hf.2.1 hf.2.2
  choose caps w C hC hw hbound using hex
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid L J N T eCut alpha beta hN hNT hlog hbeta hz halpha hs Phi hPhi hsPhi
  have hT : 1 < T := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold negativePart collect gridBudget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro p hp'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdT : (d:ℝ) ≤ T := (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)
  exact hbound (p.2,s) N d J T ((2:ℝ)^p.1)
    (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) alpha beta
    (by omega) hd0 hT hNT hdT hlog
    (frequency_positive d J _ hd0 (by unfold PRZZSourceCutoffs.deltaCutoff; positivity))
    hbeta hz halpha hs Phi hPhi hsPhi


theorem paired_negative_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ,
      (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧
      ∀ Kgrid L J N : ℕ, ∀ T eCut : ℝ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 →
      ∀ Phi : ℝ → ℂ, ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eCut alpha beta)
        Phi T alpha beta‖ ≤
      gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta+
        gridBudget caps w C js K Kgrid L J N eps eta b T eCut
          (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := negative_grid_bound hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ P F hP hF hPl hPr hFl hFr
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid L J N T eCut alpha beta hN hNT hlog hbeta hzb halpha hza ha hb' hs Phi hPhi hsPhi
  dsimp only
  have hd : ContDiff ℝ ∞ (PRZZKeptLiteral.dualProfile Phi T alpha beta) :=
    hPhi.mul ((PRZZDualSmooth.multiplier_contDiff alpha beta ha hb').comp
      (contDiff_const.mul contDiff_id))
  have hsd := (PRZZKeptLiteral.dual_profile_regular Phi hPhi.continuous hsPhi T alpha beta ha hb').2
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact h Kgrid L J N T eCut alpha beta hN hNT hlog hbeta hzb halpha hs Phi hPhi hsPhi
  · exact h Kgrid L J N T eCut (-beta) (-alpha) hN hNT hlog
      (by simpa using halpha) (by simpa using hza) (by simpa using hbeta)
      (by rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs) _ hd hsd

/-- Every original finite grid and BOTH actual branches; one time-mass
constant is chosen before height and all grid sizes. No negative norm is
left on the right. Scale-indexed arithmetic constants are still explicit. -/
theorem paired_negative_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S)
    (P F Phi : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ, ∃ M : ℝ,
      (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → A+B ≠ 0 →
      ∀ Kgrid L J N : ℕ, 1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → ∀ eCut : ℝ,
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eCut alpha beta)
        Phi T alpha beta‖ ≤
      M*(gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut alpha beta+
        gridEnvelope caps w C js K Kgrid L J N eps eta b T eCut (-beta) (-alpha)) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := paired_negative_bound hWeil hDI K hK js eps eta b S (1+S)
    heps heta hb hS (by linarith) P F hP hF hPl hPr hFl hFr
  obtain ⟨M,hM,hm⟩ := paired_grid_bound Phi hPhi hcPhi hsPhi S hS
  refine ⟨caps,w,C,M,hC,hw,hM,?_⟩
  filter_upwards [hm,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hm hsmall
  intro A B hA hB hs Kgrid L J N hN hNT hlog eCut
  dsimp only
  have hc := scaled_shift_conditions S T A B hS hlog hA hB
  have hc' := scaled_shift_conditions S T B A hS hlog hB hA
  have hs' : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hs (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  exact (h Kgrid L J N T eCut _ _ hN hNT hlog hc.1 hc.2.1 hc.2.2 hc'.2.1
    (hsmall.2 A hA) (hsmall.2 B hB) hs' Phi hPhi hsPhi).trans
      (hm A B hA hB caps w C (fun i => (hC i).le) (fun i q => (hw i q).le)
        js K Kgrid L J N eps eta b eCut)

#print axioms paired_negative_bound
#print axioms paired_negative_uniform
#print axioms negative_grid_bound
end XiPrime8845.PRZZNegativeGrid

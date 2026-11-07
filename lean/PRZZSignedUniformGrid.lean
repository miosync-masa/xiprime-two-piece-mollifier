import PRZZUniformGrid
import PRZZWeilDIErrorJoin

/-! Uniform cap suppliers for the actual positive and negative branches.
No arithmetic cap depends on the growing dyadic or spatial index. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZSignedUniformGrid
open PRZZCentralArithmeticJoin PRZZCentralMainAssembly PRZZCentralGridWeilDI
open PRZZMellinSeparation PRZZActualAggregate PRZZDualMellinUniform PRZZUniformGrid
set_option maxHeartbeats 10000000


theorem paired_positive_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (List ℕ × List ℕ) → Caps,
      ∃ w : (List ℕ × List ℕ) → ℝ, ∃ C : ℝ,
      0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Kgrid L J N : ℕ, ∀ T eCut : ℝ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 →
      ∀ Phi : ℝ → ℂ, ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      ‖branchPair (fun Phi alpha beta => positivePart P F Phi Kgrid L J N a T eCut alpha beta)
        Phi T alpha beta‖ ≤
      gridBudget (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N eps eta b T eCut Phi alpha beta+
        gridBudget (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N eps eta b T eCut
          (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := positive_grid_uniform hWeil hDI K hK js eps eta b S Z
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
theorem paired_positive_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S)
    (P F Phi : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∃ caps : (List ℕ × List ℕ) → Caps,
      ∃ w : (List ℕ × List ℕ) → ℝ, ∃ C : ℝ, ∃ M : ℝ,
      0 < C ∧ (∀ q, 0 < w q) ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → A+B ≠ 0 →
      ∀ Kgrid L J N : ℕ, 1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → ∀ eCut : ℝ,
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      ‖branchPair (fun Phi alpha beta => positivePart P F Phi Kgrid L J N a T eCut alpha beta)
        Phi T alpha beta‖ ≤
      M*(gridEnvelope (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N eps eta b T eCut alpha beta+
        gridEnvelope (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N eps eta b T eCut (-beta) (-alpha)) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := paired_positive_bound hWeil hDI K hK js eps eta b S (1+S)
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
      (hm A B hA hB (fun _ => caps) (fun _ => w) (fun _ => C) (fun _ => hC.le) (fun _ q => (hw q).le)
        js K Kgrid L J N eps eta b eCut)


#print axioms paired_positive_bound
#print axioms paired_positive_uniform
end XiPrime8845.PRZZSignedUniformGrid


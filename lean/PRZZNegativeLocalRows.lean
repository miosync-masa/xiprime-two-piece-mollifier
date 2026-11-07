import PRZZWideActiveRows
import PRZZNegativeArithmetic
import PRZZUniformOuter

/-! Negative arithmetic rows on the original dyadic grid, with an exact
reassembly into negativeSum. Spatial reflection changes only FM, never
coefficients or complex shifts. The integral transfer is kept separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZNegativeLocalRows
open PRZZNegativeArithmetic PRZZMellinSeparation PRZZActualAggregate
open PRZZRowMellinBranches PRZZRowIntegralBudget PRZZActiveRows PRZZGCoefficient
set_option maxHeartbeats 6000000

def row (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  signedRow N d j l D H a F1 F2 (reflect FM) alpha beta (-x) (-y) t

theorem reassemble (N d : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) :
    negativeSum N d D H a F1 F2 FM alpha beta x y t =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        row N d j l D H a F1 F2 FM alpha beta x y t := by
  rw [negative_reflection,PRZZAStarRectangles.signedSum_rectangles]
  rfl

/-- A nonzero negative row supplies the ORIGINAL two cutoff witnesses.
No branch or arithmetic coefficient is assumed nonzero. -/
theorem witnesses (N d j l : ℕ) (D H : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ)
    (hn : row N d j l D H a F1 F2 FM alpha beta x y t ≠ 0) :
    ∃ n ∈ PRZZDyadic.cell N j, F1 ((d:ℝ)*n) ≠ 0 ∧
      ∃ m ∈ PRZZDyadic.cell N l, F2 ((d:ℝ)*m) ≠ 0 := by
  obtain ⟨x',t',v,n,hh⟩ := active_witness N d j l D H a F1 F2 (reflect FM) alpha beta
    ⟨-x,-y,t,hn⟩
  obtain ⟨hnj,hf1,m,hml,hf2⟩ := PRZZActualCasePowers.row_nonzero_cutoffs
    N d j l n a a F1 F2 (reflect FM) alpha beta x' t' v hh
  exact ⟨n,hnj,hf1,m,hml,hf2⟩

theorem row_uniform
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 QM : ℝ, ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖row N d j l D H (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 Q2) (scaledCutoff FM QM) alpha betaShift x y t‖ ≤
      rowBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|) := by
  have hrM : Continuous (reflect FM) := hM.comp continuous_neg
  have hrcM : HasCompactSupport (reflect FM) := hcM.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨caps,w,C,hC,hw,h⟩ := PRZZWideActiveRows.signedRow_uniform hWeil hDI K hK js
    eps eta beta S Z heps heta hbeta hS hZ F0 F2 (reflect FM) hf hc hF hcF hrM hrcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 QM N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  unfold row
  rw [PRZZUniformOuter.reflect_scaled]
  exact h Q2 QM N d j l T Q D H (-x) (-y) t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb

theorem budget_absorbed (C0 : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ) (K : ℕ)
    (eps eta rho b delta gamma L S r : ℝ) (hC0 : 0 < C0) (hw : ∀ q, 0 < w q)
    (he : 0 ≤ eps) (hn : 0 ≤ eta) (hrho : 0 ≤ rho) (hb : 0 ≤ b)
    (hgamma : 0 < gamma) (hL : 0 ≤ L) (hS : 0 ≤ S) (hr : 0 < r)
    (hmargin : (6+rho)*eta+(3+rho)*eps+b < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d : ℕ) (D H T M A lam Q1 Q2 : ℝ)
      (alpha beta z1 z2 : ℂ) (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ),
      1 ≤ (N:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      0 ≤ A → A ≤ T^rho → 0 < d → (d:ℝ) ≤ T → 1 ≤ lam → 0 < M →
      0 ≤ Q1 → 0 ≤ Q2 → Function.support F1 ⊆ Icc (Q1/2) (3*Q1) →
      Function.support F2 ⊆ Icc (Q2/2) (3*Q2) →
      A ≤ lam*(Q1*Q2/((d:ℝ)^2*T)) → r ≤ ‖alpha+beta‖ →
      (∀ l ∈ range (Nat.log 2 N+1), |Real.log M|+|Real.log ((2:ℝ)^l)| ≤ L*Real.log T) →
      |((alpha+beta)/(Real.log T:ℂ)).re| ≤ S/Real.log T →
      PRZZWideActiveRows.activeBudget C0 w caps js K N d eps eta b D H T M A alpha beta z1 z2 a F1 F2 (reflect FM) ≤
        C*T^(delta+gamma)*lam*PRZZOptimalPowers.target N T/d := by
  obtain ⟨C,hC,h⟩ := PRZZWideActiveRows.active_total_absorbed C0 w caps js K eps eta rho b delta gamma L S r
    hC0 hw he hn hrho hb hgamma hL hS hr hmargin
  refine ⟨C,hC,?_⟩
  intro N d D H T M A lam Q1 Q2 alpha beta z1 z2 a F1 F2 FM
    hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hfreq hsep hscale hshift
  exact h N d D H T M A lam Q1 Q2 alpha beta z1 z2 a F1 F2 (reflect FM)
    hN hNT hlog hA hAT hd hdT hlam hM hQ1 hQ2 hF1 hF2 hfreq hsep hscale hshift


#print axioms budget_absorbed
#print axioms reassemble
#print axioms witnesses
#print axioms row_uniform
end XiPrime8845.PRZZNegativeLocalRows


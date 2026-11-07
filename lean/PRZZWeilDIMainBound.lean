import PRZZCentralGridWeilDI

/-! One bound for the original moment minus its zeta diagonal main term:
sharp AFE reduction + actual two-branch Weil/DI positive-grid evaluation
+ evaluated Gamma defect. Remaining signed modes and indexed constants
are explicit; this is not yet the optimized PRZZ moment asymptotic. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZWeilDIMainBound
open PRZZCentralArithmeticJoin PRZZCentralMainAssembly PRZZCentralGridWeilDI PRZZActualAggregate
open PRZZMellinSeparation
set_option maxHeartbeats 10000000

def evaluatedBudget (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (P F Phi : ℝ → ℂ) (js : List ℕ) (K Kgrid J N : ℕ)
    (epsA etaA b T eps : ℝ) (alpha beta : ℂ) : ℝ :=
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let L := PRZZLiteralExhaustion.spatialLength T
  ‖zeroMismatch P F Phi Kgrid N a T eps alpha beta‖+
    (gridBudget caps w C js K Kgrid L J N epsA etaA b T eps Phi alpha beta+
      gridBudget caps w C js K Kgrid L J N epsA etaA b T eps
        (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
    ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eps alpha beta)
      Phi T alpha beta‖+
    ‖branchPair (fun Phi alpha beta => tailPart P F Phi Kgrid L J N a T eps alpha beta)
      Phi T alpha beta‖

/-- All positive cells have their Weil/DI budgets SUBSTITUTED, not assumed.
The indexed scale constants and the dual Gamma-weighted Mellin mass stay
visible inside evaluatedBudget. In particular this is not a uniform-J
absorption theorem for that budget. -/
theorem moment_evaluated
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (epsA etaA b : ℝ)
    (hepsA : 0 < epsA) (hetaA : 0 < etaA) (hb : 0 < b)
    (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ,
      ∃ Cr Cg : ℝ, (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧ 0 < Cr ∧ 0 < Cg ∧
      ∀ᶠ T : ℝ in atTop, ∀ (J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        Cr*T^delta*PRZZOptimalPowers.target N T+
          evaluatedBudget caps w C (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi js
            K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta+
          Cg*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  obtain ⟨caps,w,C,hC,hw,hcells⟩ := paired_residual_weil_di hWeil hDI K hK js epsA etaA b S (1+S)
    hepsA hetaA hb hS (by linarith) F F hP hP hFl hFr hFl hFr
  obtain ⟨Cr,Cg,hCr,hCg,hmain⟩ := moment_main_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  refine ⟨caps,w,C,Cr,Cg,hC,hw,hCr,hCg,?_⟩
  filter_upwards [hmain,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hmain hsmall
  intro J N A B hN hscale hNT hlog hA hB hsep
  dsimp only
  have h1 := scaled_shift_conditions S T A B hS hlog hA hB
  have h2 := scaled_shift_conditions S T B A hS hlog hB hA
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show (Real.log T:ℝ) ≠ 0 by linarith))
  have heval := hcells (Nat.log 2 N+2) J N T eps _ _ hN hNT hlog
    h1.1 h1.2.1 h1.2.2 h2.2.1 (hsmall.2 A hA) (hsmall.2 B hB) hs Phi hPhi hsPhi
  have hmom := hmain J N A B hN hscale hA hB hsep
  exact hmom.trans (add_le_add (add_le_add le_rfl heval) le_rfl)

#print axioms moment_evaluated
end XiPrime8845.PRZZWeilDIMainBound

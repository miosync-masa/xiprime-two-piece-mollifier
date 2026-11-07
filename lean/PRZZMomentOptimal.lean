import PRZZBodyTailOptimal

/-! The original moment estimate with the actual paired Fourier tail
evaluated. Weil and DI remain explicit deep inputs. The smooth plateau
seed, bounded separated logarithmic shifts and N <= T^(4/7) are retained.
This does not assert a new unconditional theorem about zeta zeros. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZMomentOptimal
open PRZZMellinSeparation
set_option maxHeartbeats 15000000

theorem moment_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r)
    (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨eD,eH,Cm,hD,hD1,hDH,hCm,hmain⟩ := PRZZCommonCutMoment.moment_bound
    hWeil hDI K hK js tau S r htau hS hr P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
  have hPl : ∀ x ≤ (1/2:ℝ), (P x:ℂ) = 1 := by intro x hx; simp only [hl x hx,ofReal_one]
  have hPr : ∀ x, 1 ≤ x → (P x:ℂ) = 0 := by intro x hx; simp only [hright x hx,ofReal_zero]
  obtain ⟨Ct,hCt,htail⟩ := PRZZBodyTailOptimal.actual_tail_uniform (fun x => (P x:ℂ)) Phi
    hP hPl hPr hPhi.continuous hcPhi hsPhi js S r eD eH tau hS hr hD.le hD1 hDH
  refine ⟨Cm+Ct,by positivity,?_⟩
  filter_upwards [hmain,htail] with T hmain htail
  intro N A B hN hscale hNT hlog hA hB hsep
  have h0 := hmain N A B hN hscale hNT hlog hA hB hsep
  have h1 := htail N A B hN (by linarith) hA hB hsep
  dsimp only at h0 ⊢
  exact h0.trans ((add_le_add le_rfl h1).trans_eq (by ring))

#print axioms moment_bound
end XiPrime8845.PRZZMomentOptimal

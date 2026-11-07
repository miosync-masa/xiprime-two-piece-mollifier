import PRZZCommonCutMoment
import PRZZWindowSpatialJoin

/-! The SAME cutoff pair is valid for the original moment estimate and
the evaluated native transfer/subunit/large-scale residual budgets.
No equality between the actual variable Fourier tail and these native
budgets is assumed: that final reindexing interface stays visible. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZCommonResidualJoin
open PRZZMellinSeparation PRZZCommonCutMoment
set_option maxHeartbeats 12000000

def nativeError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (js : List ℕ) (N J : ℕ)
    (dual : Bool) (T eD eH : ℝ) (A B : ℂ) : ℝ :=
  PRZZWindowCentralAssembly.errorBudget (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
    Phi js (PRZZLiteralExhaustion.spatialLength T) N J dual T 4 eD eH A B+
  (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
    (PRZZResolvedTailMass.branch dual A B T t *
      PRZZWindowSpatialJoin.closedLarge (PRZZLiteralExhaustion.spatialLength T) J N
        (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^(4:ℝ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖)

theorem moment_and_native_errors
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
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧ 0 < C ∧
      ∀ᶠ T : ℝ in atTop, ∀ (N J : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖+
        nativeError P Phi js N J false T eD eH A B+
        nativeError P Phi js N J true T eD eH A B ≤
        C*T^tau*PRZZOptimalPowers.target N T+
          ‖actualTail (fun x => (P x:ℂ)) Phi js N T eD eH A B‖ := by
  obtain ⟨eD,eH,C,hD,hD1,hDH,hC,hmain⟩ := moment_bound
    hWeil hDI K hK js tau S r htau hS hr P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
  obtain ⟨Ce,hCe,herrors⟩ := PRZZWindowSpatialJoin.actual_join_strict P hm hlo hhi hl hright hP
    Phi hPhi.continuous hcPhi js 1 4 S r eD eH tau (by norm_num) (by norm_num)
    hS hr hD.le hDH (by linarith)
  refine ⟨eD,eH,C+2*Ce,hD,hD1,hDH,by positivity,?_⟩
  filter_upwards [hmain,herrors] with T hmain herrors
  intro N J A B hN hscale hNT hlog hA hB hsep
  have h0 := hmain N A B hN hscale hNT hlog hA hB hsep
  have h1 := herrors (PRZZLiteralExhaustion.spatialLength T) J N false A B hN (by linarith) hA hB hsep
  have h2 := herrors (PRZZLiteralExhaustion.spatialLength T) J N true A B hN (by linarith) hA hB hsep
  change nativeError P Phi js N J false T eD eH A B ≤ Ce*T^tau*PRZZOptimalPowers.target N T at h1
  change nativeError P Phi js N J true T eD eH A B ≤ Ce*T^tau*PRZZOptimalPowers.target N T at h2
  dsimp only at h0 ⊢
  have hh := add_le_add (add_le_add h0 h1) h2
  convert hh using 1 <;> first | rfl | ring

#print axioms moment_and_native_errors
end XiPrime8845.PRZZCommonResidualJoin

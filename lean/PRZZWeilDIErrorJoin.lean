import PRZZGammaBudgetAbsorption
import PRZZArithmeticTailLimit

/-! Gamma budget and actual paired Fourier-tail absorption into the original
Weil/DI moment estimate. Large-J thresholds retain their full dependence. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZWeilDIErrorJoin
open PRZZActualAggregate PRZZMellinSeparation PRZZCentralMainAssembly
open PRZZDualMellinUniform PRZZWeilDIZeroJoin PRZZGammaBudgetAbsorption
open PRZZArithmeticTailLimit
set_option maxHeartbeats 10000000

theorem moment_gamma_absorbed
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
      ∃ Cr M : ℝ, (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧ 0 < Cr ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in atTop, ∀ (J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        Cr*T^delta*PRZZOptimalPowers.target N T+
          nonzeroEnvelope M caps w C (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi js
            K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta := by
  obtain ⟨caps,w,C,Cr,Cg,M,hC,hw,hCr,hCg,hM,hmain⟩ := moment_zero_absorbed
    hWeil hDI K hK epsA etaA b hepsA hetaA hb P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨D,hD,hgamma⟩ := gamma_budget_target Phi hPhi.continuous hcPhi js r hr
  refine ⟨caps,w,C,Cr+Cg*D,M,hC,hw,by positivity,hM,?_⟩
  filter_upwards [hmain,eventually_ge_atTop (1:ℝ)] with T hmain hT
  intro J N A B hN hscale hNT hlog hA hB hsep
  dsimp only
  have h1 := hmain J N A B hN hscale hNT hlog hA hB hsep
  dsimp only at h1
  have h2 := mul_le_mul_of_nonneg_left (hgamma N T hN (by linarith) hlog) hCg.le
  unfold gammaBudget at h2
  have htarget : 0 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    positivity
  have h3 := mul_le_mul_of_nonneg_left
    (Real.one_le_rpow hT (show 0 ≤ delta by linarith))
    (show 0 ≤ Cg*D*PRZZOptimalPowers.target N T by positivity)
  nlinarith only [h1,h2,h3]

def centralEnvelope (M : ℝ) (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (P F Phi : ℝ → ℂ) (js : List ℕ) (K Kgrid J N : ℕ)
    (epsA etaA b T eps : ℝ) (alpha beta : ℂ) : ℝ :=
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let L := PRZZLiteralExhaustion.spatialLength T
  M*(gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps alpha beta+
    gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps (-beta) (-alpha))+
  ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eps alpha beta)
    Phi T alpha beta‖

theorem nonzero_split (M : ℝ) (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (P F Phi : ℝ → ℂ) (js : List ℕ) (K Kgrid J N : ℕ)
    (epsA etaA b T eps : ℝ) (alpha beta : ℂ) :
    nonzeroEnvelope M caps w C P F Phi js K Kgrid J N epsA etaA b T eps alpha beta =
      centralEnvelope M caps w C P F Phi js K Kgrid J N epsA etaA b T eps alpha beta+
        ‖pairedTail P F Phi Kgrid J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eps alpha beta‖ := rfl

/-- The true paired Fourier tail is absorbed for sufficiently large J.
The threshold depends on T,N,A,B; no uniform-J or polynomial cutoff
bound is claimed for the remaining signed central envelope. -/
theorem moment_central_eventually
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
      ∃ Cr M : ℝ, (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧ 0 < Cr ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∃ J0 : ℕ, ∀ J ≥ J0,
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        Cr*T^delta*PRZZOptimalPowers.target N T+
          centralEnvelope M caps w C (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi js
            K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta := by
  obtain ⟨caps,w,C,Cr,M,hC,hw,hCr,hM,hmain⟩ := moment_gamma_absorbed
    hWeil hDI K hK epsA etaA b hepsA hetaA hb P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  refine ⟨caps,w,C,Cr+1,M,hC,hw,by positivity,hM,?_⟩
  filter_upwards [hmain,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with T hmain hsmall hT
  intro N A B hN hscale hNT hlog hA hB hsep
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  obtain ⟨J0,hJ⟩ := tail_eventually_power F F Phi (Nat.log 2 N+2) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) hP hFl hFr hPhi.continuous hsPhi
    T eps 0 hT0 (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    (hsmall.2 A hA) (hsmall.2 B hB) hs
  refine ⟨J0,?_⟩
  intro J hj
  dsimp only
  have h1 := hmain J N A B hN hscale hNT hlog hA hB hsep
  have h2 := hJ J hj
  dsimp only [F] at h2
  dsimp only at h1
  rw [nonzero_split] at h1
  simp only [neg_zero,Real.rpow_zero] at h2
  have h3 := one_le_sharp_scale N T delta hN hT (by linarith)
  nlinarith only [h1,h2,h3]

#print axioms moment_central_eventually
#print axioms nonzero_split
#print axioms moment_gamma_absorbed
end XiPrime8845.PRZZWeilDIErrorJoin


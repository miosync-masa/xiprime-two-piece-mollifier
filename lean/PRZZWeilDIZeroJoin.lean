import PRZZDualMellinUniform
import PRZZZeroMismatchHeight

/-! Substitute the proved native zero-mode rate into the actual Weil/DI
moment budget. Genuine dual Mellin masses are uniformly paid for too.
The nonzero spatial/arithmetic envelopes and signed tails remain explicit. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZWeilDIZeroJoin
open PRZZActualAggregate PRZZMellinSeparation PRZZCentralMainAssembly
open PRZZCentralGridWeilDI PRZZWeilDIMainBound PRZZDualMellinUniform
set_option maxHeartbeats 10000000

def nonzeroEnvelope (M : ℝ) (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (P F Phi : ℝ → ℂ) (js : List ℕ) (K Kgrid J N : ℕ)
    (epsA etaA b T eps : ℝ) (alpha beta : ℂ) : ℝ :=
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let L := PRZZLiteralExhaustion.spatialLength T
  M*(gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps alpha beta+
    gridEnvelope caps w C js K Kgrid L J N epsA etaA b T eps (-beta) (-alpha))+
  ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eps alpha beta)
    Phi T alpha beta‖+
  ‖branchPair (fun Phi alpha beta => tailPart P F Phi Kgrid L J N a T eps alpha beta)
    Phi T alpha beta‖

/-- Both time Mellin masses and the actual zeroMismatch norm are supplied
by proved uniform estimates. No zero-error or dual-mass premise remains. -/
theorem evaluated_zero_removed (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (eps r S rate : ℝ)
    (heps : 0 < eps) (hr : 0 < r) (hS : 0 ≤ S) (hrate : 0 ≤ rate) :
    ∃ Cz M : ℝ, 0 < Cz ∧ 0 ≤ M ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
        (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ),
      (∀ i, 0 ≤ C i) → (∀ i q, 0 ≤ w i q) →
      ∀ (K J N : ℕ) (epsA etaA b : ℝ), 1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      evaluatedBudget caps w C (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi js
        K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta ≤
      Cz*T^(-rate)+nonzeroEnvelope M caps w C (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
        Phi js K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta := by
  obtain ⟨Cz,hCz,hz⟩ := PRZZZeroMismatchHeight.przz_window_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eps r S rate heps hr hS hrate
  obtain ⟨M,hM,hb⟩ := evaluated_uniform Phi hPhi hcPhi hsPhi S hS
  refine ⟨Cz,M,hCz,hM,?_⟩
  filter_upwards [hz,hb] with T hz hb
  intro A B hA hB hsep caps w C hC hw K J N epsA etaA b hN hNT
  dsimp only
  have h1 := hz N A B hN hNT hA hB hsep
  have h2 := hb A B hA hB caps w C hC hw (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
    js K (Nat.log 2 N+2) J N epsA etaA b eps
  dsimp only at h2
  unfold nonzeroEnvelope
  dsimp only
  linarith only [h1,h2]

/-- The existing sharp-AFE scale is at least one. Thus a bounded zero
error can be absorbed without changing its N,T powers. -/
theorem one_le_sharp_scale (N : ℕ) (T delta : ℝ)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hd : 0 ≤ delta) :
    1 ≤ T^delta*PRZZOptimalPowers.target N T := by
  have hNN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn := Real.one_le_rpow hNN (by norm_num : (0:ℝ) ≤ 7/4)
  have ht := Real.one_le_rpow hT hd
  have htarget : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    have hh : 0 ≤ T^(1/2:ℝ)*(N:ℝ)^(7/8:ℝ) := by positivity
    linarith
  nlinarith

/-- Original Weil/DI moment estimate after actual zero-mode substitution.
The zero contribution is absorbed in the existing sharp-AFE N,T scale;
nonzero envelopes and signed Fourier tails are not declared optimized. -/
theorem moment_zero_absorbed
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
      ∃ Cr Cg M : ℝ, (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧ 0 < Cr ∧ 0 < Cg ∧ 0 ≤ M ∧
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
            K (Nat.log 2 N+2) J N epsA etaA b T eps alpha beta+
          Cg*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨caps,w,C,Cr,Cg,hC,hw,hCr,hCg,hmain⟩ := moment_evaluated
    hWeil hDI K hK epsA etaA b hepsA hetaA hb P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨Cz,M,hCz,hM,hzero⟩ := evaluated_zero_removed P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js eps r S 0 heps hr hS (by norm_num)
  refine ⟨caps,w,C,Cr+Cz,Cg,M,hC,hw,by positivity,hCg,hM,?_⟩
  filter_upwards [hmain,hzero,eventually_ge_atTop (1:ℝ)] with T hmain hzero hT
  intro J N A B hN hscale hNT hlog hA hB hsep
  dsimp only
  have h1 := hmain J N A B hN hscale hNT hlog hA hB hsep
  have h2 := hzero A B hA hB hsep caps w C (fun i => (hC i).le)
    (fun i q => (hw i q).le) K J N epsA etaA b hN hscale
  dsimp only at h1 h2
  simp only [neg_zero,Real.rpow_zero,mul_one] at h2
  have h3 := mul_le_mul_of_nonneg_left
    (one_le_sharp_scale N T delta hN hT (by linarith)) hCz.le
  nlinarith only [h1,h2,h3]

#print axioms moment_zero_absorbed
#print axioms evaluated_zero_removed
#print axioms one_le_sharp_scale
end XiPrime8845.PRZZWeilDIZeroJoin

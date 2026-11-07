import PRZZCommonWindowCollector
import PRZZZeroMismatchHeight
import PRZZGammaBudgetAbsorption

/-! Substitute both signed optimized collectors, with ONE cutoff pair,
in the original moment bound. Zero mismatch and Gamma-defect budgets
are evaluated. The actual paired variable-cutoff Fourier tail remains
explicit, not identified by fiat with a native-family error envelope. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZCommonCutMoment
open PRZZMellinSeparation PRZZCommonWindowCollector
set_option maxHeartbeats 12000000

def actualTail (P : ℝ → ℂ) (Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZCentralMainAssembly.branchPair
    (fun Phi alpha beta => PRZZWindowMoment.tail P P Phi (Nat.log 2 N+2)
      (PRZZLiteralExhaustion.spatialLength T) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta)
    Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

theorem model_eq (P Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ)
    (T eD eH : ℝ) (A B : ℂ) :
    let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let alpha := A/(Real.log T:ℂ)
    let beta := B/(Real.log T:ℂ)
    PRZZLiteralFourierLimit.fullModel P P Phi (Nat.log 2 N+2) N a T eD alpha beta =
      PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
      PRZZCentralMainAssembly.zeroMismatch P P Phi (Nat.log 2 N+2) N a T eD alpha beta+
      PRZZCentralMainAssembly.branchPair
        (fun Phi alpha beta => signed false P P Phi (PRZZLiteralExhaustion.spatialLength T)
          N js T eD eH alpha beta) Phi T alpha beta+
      PRZZCentralMainAssembly.branchPair
        (fun Phi alpha beta => signed true P P Phi (PRZZLiteralExhaustion.spatialLength T)
          N js T eD eH alpha beta) Phi T alpha beta+
      actualTail P Phi js N T eD eH A B+
      ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  dsimp only
  rw [PRZZWindowMoment.model_main P P Phi (Nat.log 2 N+2) N _ T eD
    (PRZZCommonSignedWindow.cutoff T eH)]
  simp [PRZZWindowMoment.residual,signed,actualTail,add_assoc]

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
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧ 0 < C ∧
      ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T+
          ‖actualTail (fun x => (P x:ℂ)) Phi js N T eD eH A B‖ := by
  have hPl : ∀ x ≤ (1/2:ℝ), (P x:ℂ) = 1 := by intro x hx; simp [hl x hx]
  have hPr : ∀ x, 1 ≤ x → (P x:ℂ) = 0 := by intro x hx; simp [hright x hx]
  obtain ⟨eD,eH,eta,Cc,hD,hD1,hDH,heta,heta1,hmarg,hCc,hcentral⟩ := paired_collectors
    hWeil hDI K hK js (tau/2) S r (by linarith) hS hr
    _ _ hP hP hPl hPr hPl hPr Phi hPhi hcPhi hsPhi
  obtain ⟨C0,D,hC0,hD0,hmain⟩ := PRZZWindowMoment.moment_main_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eD eH eta (tau/2) hS hr hD hD1 hDH heta heta1 hmarg
  obtain ⟨Cz,hCz,hzero⟩ := PRZZZeroMismatchHeight.przz_window_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eD r S 0 hD hr hS le_rfl
  obtain ⟨Cg,hCg,hgamma⟩ := PRZZGammaBudgetAbsorption.gamma_budget_target Phi hPhi.continuous hcPhi js r hr
  refine ⟨eD,eH,C0+2*Cc+Cz+D*Cg+1,hD,hD1,hDH,by positivity,?_⟩
  filter_upwards [hcentral,hmain,hzero,eventually_ge_atTop (72:ℝ)] with T hc hm hz hT
  intro N A B hN hscale hNT hlog hA hB hsep
  let Pc : ℝ → ℂ := fun x => (P x:ℂ)
  let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  let L := PRZZLiteralExhaustion.spatialLength T
  have hp := hc false L N A B hN hT hNT hlog hA hB hsep
  have hn := hc true L N A B hN hT hNT hlog hA hB hsep
  have hz' : ‖PRZZCentralMainAssembly.zeroMismatch Pc Pc Phi (Nat.log 2 N+2) N a T eD alpha beta‖ ≤ Cz := by
    simpa only [neg_zero,Real.rpow_zero,mul_one] using hz N A B hN hscale hA hB hsep
  have hbase := hm N A B hN hscale hA hB hsep (PRZZCommonSignedWindow.cutoff T eH)
  dsimp only at hbase ⊢
  have hR : ‖PRZZWindowMoment.residual Pc Pc Phi (Nat.log 2 N+2) N a T eD
      (PRZZCommonSignedWindow.cutoff T eH) alpha beta‖ ≤
      Cz+Cc*T^(tau/2)*PRZZOptimalPowers.target N T+
        Cc*T^(tau/2)*PRZZOptimalPowers.target N T+‖actualTail Pc Phi js N T eD eH A B‖ := by
    change ‖PRZZCentralMainAssembly.zeroMismatch Pc Pc Phi (Nat.log 2 N+2) N a T eD alpha beta+
      PRZZCentralMainAssembly.branchPair (fun Phi alpha beta => signed false Pc Pc Phi L N js T eD eH alpha beta) Phi T alpha beta+
      PRZZCentralMainAssembly.branchPair (fun Phi alpha beta => signed true Pc Pc Phi L N js T eD eH alpha beta) Phi T alpha beta+
      actualTail Pc Phi js N T eD eH A B‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hz' hp)) hn)) le_rfl)
  have htarg0 : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have htarg1 : 1 ≤ PRZZOptimalPowers.target N T := by
    have hNN : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hh := Real.one_le_rpow hNN (by norm_num : (0:ℝ) ≤ 7/4)
    unfold PRZZOptimalPowers.target
    have hh' : 0 ≤ T^(1/2:ℝ)*(N:ℝ)^(7/8:ℝ) := by positivity
    linarith
  let X := T^tau*PRZZOptimalPowers.target N T
  have hTX : PRZZOptimalPowers.target N T ≤ X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.one_le_rpow (by linarith : 1 ≤ T) htau.le) htarg0
  have hX : 1 ≤ X := htarg1.trans hTX
  have hsmall : T^(tau/2)*PRZZOptimalPowers.target N T ≤ X :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith)) htarg0
  have hb0 := mul_le_mul_of_nonneg_left hsmall hC0.le
  have hb1 := mul_le_mul_of_nonneg_left hsmall hCc.le
  have hbz := mul_le_mul_of_nonneg_left hX hCz.le
  have hg := mul_le_mul_of_nonneg_left (hgamma N T hN (by linarith) hlog) hD0.le
  have hgt := mul_le_mul_of_nonneg_left hTX (mul_nonneg hD0.le hCg.le)
  have hbase' : ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
      PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
    C0*T^(tau/2)*PRZZOptimalPowers.target N T+
    ‖PRZZWindowMoment.residual Pc Pc Phi (Nat.log 2 N+2) N a T eD
      (PRZZCommonSignedWindow.cutoff T eH) alpha beta‖+
    D*PRZZGammaBudgetAbsorption.gammaBudget Phi js r N T := by
    convert hbase using 1 <;> unfold PRZZGammaBudgetAbsorption.gammaBudget <;> ring
  simp only [mul_assoc]
  change _ ≤ (C0+2*Cc+Cz+D*Cg+1)*X+‖actualTail Pc Phi js N T eD eH A B‖
  nlinarith only [hbase',hR,hb0,hb1,hbz,hg,hgt,hX]

#print axioms model_eq
#print axioms moment_bound
end XiPrime8845.PRZZCommonCutMoment

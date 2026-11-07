import PRZZSignedUniformGrid

/-! The original moment reduced to two scalar, uniform-cap signed grids.
All zero, Gamma and actual Fourier-tail errors are paid for. The finite
frequency-dependent grid envelopes are NOT declared optimized. -/
noncomputable section
open scoped ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZSignedMomentBudget
open PRZZActualAggregate PRZZMellinSeparation PRZZCentralMainAssembly PRZZDualMellinUniform
open PRZZWeilDIZeroJoin PRZZGammaBudgetAbsorption PRZZArithmeticTailLimit
set_option maxHeartbeats 12000000

def pairedEnvelope (caps : (List ℕ × List ℕ) → Caps)
    (w : (List ℕ × List ℕ) → ℝ) (C M : ℝ) (js : List ℕ)
    (K Kgrid L J N : ℕ) (epsA etaA b T eps : ℝ) (alpha beta : ℂ) : ℝ :=
  M*(gridEnvelope (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N epsA etaA b T eps alpha beta+
    gridEnvelope (fun _ => caps) (fun _ => w) (fun _ => C) js K Kgrid L J N epsA etaA b T eps (-beta) (-alpha))

theorem moment_scalar_signed
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
    ∃ capsP capsN : (List ℕ × List ℕ) → Caps,
      ∃ wP wN : (List ℕ × List ℕ) → ℝ, ∃ CP CN MP MN Cr : ℝ,
      0 < CP ∧ 0 < CN ∧ (∀ q, 0 < wP q) ∧ (∀ q, 0 < wN q) ∧
      0 ≤ MP ∧ 0 ≤ MN ∧ 0 < Cr ∧
      ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∃ J0 : ℕ, ∀ J ≥ J0,
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let L := PRZZLiteralExhaustion.spatialLength T
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        Cr*T^delta*PRZZOptimalPowers.target N T+
          pairedEnvelope capsP wP CP MP js K (Nat.log 2 N+2) L J N epsA etaA b T eps alpha beta+
          pairedEnvelope capsN wN CN MN js K (Nat.log 2 N+2) L J N epsA etaA b T eps alpha beta := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  obtain ⟨capsP,wP,CP,MP,hCP,hwP,hMP,hpos⟩ := PRZZSignedUniformGrid.paired_positive_uniform
    hWeil hDI K hK js epsA etaA b S hepsA hetaA hb hS F F Phi hP hP hFl hFr hFl hFr
      hPhi hcPhi hsPhi
  obtain ⟨capsN,wN,CN,MN,hCN,hwN,hMN,hneg⟩ := PRZZUniformGrid.paired_negative_uniform
    hWeil hDI K hK js epsA etaA b S hepsA hetaA hb hS F F Phi hP hP hFl hFr hFl hFr
      hPhi hcPhi hsPhi
  obtain ⟨Cr,Cg,hCr,hCg,hmain⟩ := moment_main_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨Cz,hCz,hzero⟩ := PRZZZeroMismatchHeight.przz_window_power P hP hm hlo hhi hl hright
    Phi hPhi hcPhi hsPhi js eps r S 0 heps hr hS (by norm_num)
  obtain ⟨D,hD,hgamma⟩ := gamma_budget_target Phi hPhi.continuous hcPhi js r hr
  refine ⟨capsP,capsN,wP,wN,CP,CN,MP,MN,Cr+Cz+Cg*D+1,
    hCP,hCN,hwP,hwN,hMP,hMN,by positivity,?_⟩
  filter_upwards [hpos,hneg,hmain,hzero,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with T hpos hneg hmain hzero hsmall hT
  intro N A B hN hscale hNT hlog hA hB hsep
  have hT0 : 0 < T := by linarith
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hab (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  obtain ⟨J0,hJ⟩ := tail_eventually_power F F Phi (Nat.log 2 N+2) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) hP hFl hFr hPhi.continuous hsPhi
    T eps 0 hT0 (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    (hsmall.2 A hA) (hsmall.2 B hB) hs
  refine ⟨J0,?_⟩
  intro J hj
  dsimp only
  have hp := hpos A B hA hB hab (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T)
    J N hN hNT hlog eps
  have hn := hneg A B hA hB hab (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T)
    J N hN hNT hlog eps
  have hz := hzero N A B hN hscale hA hB hsep
  have ht := hJ J hj
  have hmom := hmain J N A B hN hscale hA hB hsep
  dsimp only [F] at hp hn ht
  dsimp only at hmom
  simp only [neg_zero,Real.rpow_zero,mul_one] at hz ht
  have hg := mul_le_mul_of_nonneg_left (hgamma N T hN (by linarith) hlog) hCg.le
  unfold gammaBudget at hg
  have htarget : 0 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    positivity
  have hpower := Real.one_le_rpow hT (show 0 ≤ delta by linarith)
  have hzg := mul_le_mul_of_nonneg_left
    (one_le_sharp_scale N T delta hN hT (by linarith)) hCz.le
  have hgg := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ Cg*D*PRZZOptimalPowers.target N T by positivity)
  have hscl := one_le_sharp_scale N T delta hN hT (by linarith)
  have hfour (z p n t : ℂ) : ‖z+p+n+t‖ ≤ ‖z‖+‖p‖+‖n‖+‖t‖ := by
    linarith only [norm_add_le (z+p+n) t,norm_add_le (z+p) n,norm_add_le z p]
  have hres :
      ‖arithmeticResidual (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
        (Nat.log 2 N+2) J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      ‖zeroMismatch (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖+
      ‖branchPair (fun Phi alpha beta => positivePart (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
        (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) J N
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖+
      ‖branchPair (fun Phi alpha beta => negativePart (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
        (Nat.log 2 N+2) (PRZZLiteralExhaustion.spatialLength T) J N
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖+
      ‖pairedTail (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ := by
    unfold arithmeticResidual pairedTail
    exact hfour _ _ _ _
  unfold pairedEnvelope
  nlinarith only [hmom,hres,hp,hn,hz,ht,hg,hzg,hgg,hscl]

#print axioms moment_scalar_signed
end XiPrime8845.PRZZSignedMomentBudget


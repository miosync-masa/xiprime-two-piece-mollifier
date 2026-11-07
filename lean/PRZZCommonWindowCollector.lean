import PRZZCommonSignedWindow
import PRZZWindowMoment
import PRZZDualMellinUniform

/-! The actual original strict-spatial moment collectors at ONE common
body cutoff. The genuine Gamma dual profile is used, with its proved
height-uniform Mellin mass; no independent dual test weight is substituted. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Finset Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZCommonWindowCollector
open PRZZMellinSeparation
set_option maxHeartbeats 12000000

def signed (neg : Bool) (P F Phi : ℝ → ℂ) (L N : ℕ) (js : List ℕ)
    (T eD eH : ℝ) (alpha beta : ℂ) : ℂ :=
  (if neg then PRZZWindowMoment.negative else PRZZWindowMoment.positive)
    P F Phi (Nat.log 2 N+2) L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    T eD (PRZZCommonSignedWindow.cutoff T eH) alpha beta

theorem signed_grid (neg : Bool) (P F Phi : ℝ → ℂ) (L N : ℕ) (js : List ℕ)
    (T eD eH : ℝ) (A B : ℂ) :
    signed neg P F Phi L N js T eD eH (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
      PRZZCommonSignedWindow.grid neg (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P)
        (PRZZWRowLimit.profile F) Phi js N
        ((range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ))) T eD eH A B := by
  cases neg <;> rfl

theorem collectors
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ eD eH eta C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧
      0 < eta ∧ eta ≤ 1 ∧ 6*eD+2*eta < tau ∧ 0 < C ∧
      ∀ (neg : Bool) (L N : ℕ) (T : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖signed neg P F Phi L N js T eD eH (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T*(∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨eD,eH,eta,C,hD,hD1,hDH,heta,heta1,hmarg,hC,hgrid⟩ := PRZZCommonSignedWindow.grids
    hWeil hDI K hK js tau S r 4 htau hS hr (by norm_num)
    _ _ _ hp.1 hp.2.1 hp.1.continuous hp.2.1 hf.1.continuous hf.2.1 hp.2.2 hp.2.2 hf.2.2
  refine ⟨eD,eH,eta,C,hD,hD1,hDH,heta,heta1,hmarg,hC,?_⟩
  intro neg L N T A B Phi hN hT hNT hlog hA hB hsep hPhi hsPhi
  rw [signed_grid]
  apply hgrid neg L N _ T A B Phi hN hT hNT hlog _ hA hB hsep hPhi hsPhi
  intro s hs
  exact mem_filter.mpr ⟨(mem_filter.mp hs).1,(mem_filter.mp hs).2.le⟩

theorem paired_collectors
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∃ eD eH eta C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧
      0 < eta ∧ eta ≤ 1 ∧ 6*eD+2*eta < tau ∧ 0 < C ∧
      ∀ᶠ T : ℝ in atTop, ∀ (neg : Bool) (L N : ℕ) (A B : ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZCentralMainAssembly.branchPair
        (fun Phi alpha beta => signed neg P F Phi L N js T eD eH alpha beta)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨eD,eH,eta,C,hD,hD1,hDH,heta,heta1,hmarg,hC,h⟩ := collectors
    hWeil hDI K hK js tau S r htau hS hr P F hP hF hPl hPr hFl hFr
  obtain ⟨M,hM,hm⟩ := PRZZDualMellinUniform.dual_linear_mass Phi hPhi hcPhi hsPhi S hS
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  refine ⟨eD,eH,eta,C*(J+M+1),hD,hD1,hDH,heta,heta1,hmarg,by positivity,?_⟩
  filter_upwards [hm,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hm hsmall
  intro neg L N A B hN hT hNT hlog hA hB hsep
  let Psi := PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  have hPsi : ContDiff ℝ ∞ Psi := hPhi.mul
    ((PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).comp
      (contDiff_const.mul contDiff_id))
  have hsPsi : Function.support Psi ⊆ Icc (1:ℝ) 2 :=
    (PRZZKeptLiteral.dual_profile_regular Phi hPhi.continuous hsPhi T _ _
      (hsmall.2 A hA) (hsmall.2 B hB)).2
  have hp := h neg L N T A B Phi hN hT hNT hlog hA hB hsep hPhi hsPhi
  have hsep' : r ≤ ‖-B + -A‖ := by rw [show -B + -A = -(A+B) by ring,norm_neg]; exact hsep
  have hd := h neg L N T (-B) (-A) Psi hN hT hNT hlog
    (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA) hsep' hPsi hsPsi
  have hmass := hm A B hA hB
  have hn : 0 ≤ C*T^tau*PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hmass hn)
  simp only [neg_div] at hd'
  change ‖signed neg P F Phi L N js T eD eH _ _ +
    signed neg P F Psi L N js T eD eH _ _‖ ≤ _
  apply (norm_add_le _ _).trans ((add_le_add hp hd').trans _)
  change C*T^tau*PRZZOptimalPowers.target N T*J+
    C*T^tau*PRZZOptimalPowers.target N T*M ≤ _
  nlinarith only [hn]

#print axioms signed_grid
#print axioms collectors
#print axioms paired_collectors
end XiPrime8845.PRZZCommonWindowCollector

import PRZZNegativeWindowCell
import PRZZPositiveOuterGrid

/-! One source cutoff pair for BOTH actual signed central fields.
The original row windows, shift-slot swap and height-uniform constants
are retained. The extra inequalities also supply the AFE loss margin. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZCommonSignedWindow
open PRZZMellinSeparation PRZZCentralArithmeticJoin
set_option maxHeartbeats 12000000

def cutoff (T eH : ℝ) (p : ℕ × ℕ) (s d : ℕ) : ℕ :=
  PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0

def cell (neg : Bool) (F0 F2 FM Phi : ℝ → ℂ) (js : List ℕ)
    (N d s : ℕ) (T Q V eD eH : ℝ) (A B : ℂ) : ℂ :=
  (if neg then negativeCell else positiveCell) N d
    (PRZZWindowCentralAssembly.bodyCut T V eH s d 0 0 0)
    (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD) T ((2:ℝ)^s)
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) FM
    (scaledCutoff F0 Q) (scaledCutoff F2 V) Phi
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

def grid (neg : Bool) (F0 F2 FM Phi : ℝ → ℂ) (js : List ℕ)
    (N : ℕ) (ss : Finset ℕ) (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    cell neg F0 F2 FM Phi js N d s T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH A B

theorem cells
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hFM : Continuous FM) (hcM : HasCompactSupport FM)
    (hs0 : Function.support F0 ⊆ Icc (1/2:ℝ) 3)
    (hs2 : Function.support F2 ⊆ Icc (1/2:ℝ) 3)
    (hsM : Function.support FM ⊆ Icc (1/2:ℝ) 3) :
    ∃ eD eH eta C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧
      0 < eta ∧ eta ≤ 1 ∧ 6*eD+2*eta < tau ∧ 0 < C ∧
      ∀ (neg : Bool) (N d s : ℕ) (T Q V : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 72 ≤ T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      0 < Q → 0 < V → Q ≤ 2*T → V ≤ 2*T → (2:ℝ)^s ≤ T^geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖cell neg F0 F2 FM Phi js N d s T Q V eD eH A B‖ ≤
        C*T^(tau/2)*PRZZOptimalPowers.target N T/d*
          (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let u : ℝ := min (tau/400) (1/100)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  have huT : u ≤ tau/400 := min_le_left _ _
  have hu1 : u ≤ 1/100 := min_le_right _ _
  have hmarg : (8+u+2*u)*u+(5+u+2*u)*u+u < 20*u := by
    nlinarith [mul_le_mul_of_nonneg_left hu1 hu.le]
  obtain ⟨Cp,hCp,hp⟩ := PRZZWindowOptimalCell.positive_body
    hWeil hDI K hK js u u u (20*u) u S r geom u (2*u)
    hu hu hu hu hS hr hgeom hu.le (by positivity) hmarg
    F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  obtain ⟨Cn,hCn,hn⟩ := PRZZNegativeWindowCell.negative_body
    hWeil hDI K hK js u u u (20*u) u S r geom u (2*u)
    hu hu hu hu hS hr hgeom hu.le (by positivity) hmarg
    F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  refine ⟨u,2*u,u,Cp+Cn,hu,by linarith,by linarith,hu,by linarith,by nlinarith,by positivity,?_⟩
  intro neg N d s T Q V A B Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp hA hB hsep hPhi hsPhi
  have hp' := hp N d s T Q V B A Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp
    hB hA (by simpa only [add_comm] using hsep) hPhi hsPhi
  have hn' := hn N d s T Q V B A Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp
    hB hA (by simpa only [add_comm] using hsep) hPhi hsPhi
  have hscale : (fun y : ℝ => FM (((2:ℝ)^s)⁻¹*y)) = scaledCutoff FM ((2:ℝ)^s) := rfl
  have hmass : 0 ≤ ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖ := integral_nonneg (fun t => by positivity)
  have htarget : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have hfirst : ‖cell neg F0 F2 FM Phi js N d s T Q V u (2*u) A B‖ ≤
      (Cp+Cn)*T^(20*u+u+u+2*u)*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
    cases neg
    · have he : ‖cell false F0 F2 FM Phi js N d s T Q V u (2*u) A B‖ ≤
          Cp*T^(20*u+u+u+2*u)*PRZZOptimalPowers.target N T/d*
            (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
        simpa only [cell,Bool.false_eq_true,if_false,positiveCell,hscale,← add_div,add_comm] using hp'
      exact he.trans (by gcongr; linarith)
    · have he : ‖cell true F0 F2 FM Phi js N d s T Q V u (2*u) A B‖ ≤
          Cn*T^(20*u+u+u+2*u)*PRZZOptimalPowers.target N T/d*
            (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
        simpa [cell,negativeCell,← add_div,add_comm] using hn'
      exact he.trans (by gcongr; linarith)
  apply hfirst.trans
  have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
    (show 20*u+u+u+2*u ≤ tau/2 by nlinarith)
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (add_nonneg hCp.le hCn.le)) htarget)
      (by positivity)) hmass

theorem grids
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hFM : Continuous FM) (hcM : HasCompactSupport FM)
    (hs0 : Function.support F0 ⊆ Icc (1/2:ℝ) 3)
    (hs2 : Function.support F2 ⊆ Icc (1/2:ℝ) 3)
    (hsM : Function.support FM ⊆ Icc (1/2:ℝ) 3) :
    ∃ eD eH eta C : ℝ, 0 < eD ∧ eD < 1 ∧ eD < eH ∧
      0 < eta ∧ eta ≤ 1 ∧ 6*eD+2*eta < tau ∧ 0 < C ∧
      ∀ (neg : Bool) (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖grid neg F0 F2 FM Phi js N ss T eD eH A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T*
          (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨eD,eH,eta,C,hD,hD1,hDH,heta,heta1,hmarg,hC,hcell⟩ := cells
    hWeil hDI K hK js tau S r geom htau hS hr hgeom F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  obtain ⟨Co,hCo,houter⟩ := PRZZPositiveOuterGrid.sum_bound geom (tau/2) (tau/2) hgeom (by linarith)
  refine ⟨eD,eH,eta,Co*C,hD,hD1,hDH,heta,heta1,hmarg,by positivity,?_⟩
  intro neg L N ss T A B Phi hN hT hNT hlog hss hA hB hsep hPhi hsPhi
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  have hh := houter L N T (C*J) ss
    (fun p s d => cell neg F0 F2 FM Phi js N d s T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH A B)
    hN (by linarith) hlog (mul_nonneg hC.le hJ) hss (by
      intro p hp s hs d hd
      have hq := (PRZZPositiveOuterGrid.dyadic_scale N p.1 hN (mem_product.mp hp).1).trans
        (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hv := (PRZZPositiveOuterGrid.dyadic_scale N p.2 hN (mem_product.mp hp).2).trans
        (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hc := hcell neg N d s T ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B Phi
        (by omega) (Finset.mem_Icc.mp hd).1 hT hNT
        ((by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)) hlog
        (by positivity) (by positivity) hq hv (mem_filter.mp (hss hs)).2 hA hB hsep hPhi hsPhi
      calc
        _ ≤ C*T^(tau/2)*PRZZOptimalPowers.target N T/(d:ℝ)*J := hc
        _ = _ := by ring)
  change ‖grid neg F0 F2 FM Phi js N ss T eD eH A B‖ ≤ _ at hh
  convert hh using 1
  dsimp only [J]
  ring_nf
  simp only [mul_comm]

#print axioms cells
#print axioms grids
end XiPrime8845.PRZZCommonSignedWindow

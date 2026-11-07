import PRZZNegativeWindowCell
import PRZZPositiveOuterGrid

/-! The actual negative fixed-window cells over the full d,Q,V,M grid.
The original strict spatial window is an allowed subset; constants and
cutoff exponents precede height and the exhaustion length. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZNegativeOuterGrid
open PRZZMellinSeparation PRZZCentralArithmeticJoin
open PRZZPositiveOuterGrid (sum_bound dyadic_scale)
set_option maxHeartbeats 10000000

def grid (F0 F2 FM Phi : ℝ → ℂ) (js : List ℕ) (N : ℕ) (ss : Finset ℕ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), ∑ s ∈ ss, ∑ d ∈ Icc 1 N,
    negativeCell N d (PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) T ((2:ℝ)^s)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) FM
      (scaledCutoff F0 ((2:ℝ)^p.1)) (scaledCutoff F2 ((2:ℝ)^p.2)) Phi
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))


theorem optimized
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
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < eH ∧ 0 < C ∧
      ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖grid F0 F2 FM Phi js N ss T eD eH A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T*
          (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨eD,eH,C,hD,hDH,hC,hcell⟩ := PRZZNegativeWindowCell.negative_body_epsilon
    hWeil hDI K hK js (tau/2) S r geom (by linarith) hS hr hgeom
    F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  obtain ⟨Co,hCo,houter⟩ := sum_bound geom (tau/2) (tau/2) hgeom (by linarith)
  refine ⟨eD,eH,Co*C,hD,hDH,by positivity,?_⟩
  intro L N ss T A B Phi hN hT hNT hlog hss hA hB hsep hPhi hsPhi
  let J := ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  have hh := houter L N T (C*J) ss
    (fun p s d => negativeCell N d (PRZZWindowCentralAssembly.bodyCut T ((2:ℝ)^p.2) eH s d 0 0 0)
      (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eD) T ((2:ℝ)^s)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) FM
      (scaledCutoff F0 ((2:ℝ)^p.1)) (scaledCutoff F2 ((2:ℝ)^p.2)) Phi
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
    hN (by linarith) hlog (mul_nonneg hC.le hJ) hss (by
      intro p hp s hs d hd
      have hsp := (mem_filter.mp (hss hs)).2
      have hq := (dyadic_scale N p.1 hN (mem_product.mp hp).1).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hv := (dyadic_scale N p.2 hN (mem_product.mp hp).2).trans (by linarith : 2*(N:ℝ) ≤ 2*T)
      have hc := hcell N d s T ((2:ℝ)^p.1) ((2:ℝ)^p.2) B A Phi
        (by omega) (Finset.mem_Icc.mp hd).1 hT hNT
        ((by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)) hlog
        (by positivity) (by positivity) hq hv hsp hB hA (by simpa only [add_comm] using hsep) hPhi hsPhi
      calc
        _ ≤ C*T^(tau/2)*PRZZOptimalPowers.target N T/(d:ℝ)*J := by
          simpa only [negativeCell,← add_div,add_comm,J] using hc
        _ = _ := by ring)
  change ‖grid F0 F2 FM Phi js N ss T eD eH A B‖ ≤ _ at hh
  convert hh using 1
  dsimp only [J]
  ring_nf
  simp only [mul_comm]


#print axioms optimized
end XiPrime8845.PRZZNegativeOuterGrid


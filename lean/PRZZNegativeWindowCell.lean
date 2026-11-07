import PRZZNegativeActiveRows
import PRZZWindowOptimalCell

/-! Optimal negative signedLiteral cells at the actual arithmetic-window
cutoff, with the original positive spatial support retained. Empty source
ranges and inactive arithmetic rows are removed before budget absorption. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Set Complex MeasureTheory
namespace XiPrime8845.PRZZNegativeWindowCell
open PRZZMellinSeparation PRZZSourceCutoffs PRZZWindowScaleSupply
set_option maxHeartbeats 10000000

theorem negative_body
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ)
    (eps eta b delta gamma S r geom eD eH : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hgamma : 0 < gamma)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom) (heD : 0 ≤ eD) (heH : 0 ≤ eH)
    (hmargin : (8+eD+eH)*eta+(5+eD+eH)*eps+b < delta)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hFM : Continuous FM) (hcM : HasCompactSupport FM)
    (hs0 : Function.support F0 ⊆ Icc (1/2:ℝ) 3)
    (hs2 : Function.support F2 ⊆ Icc (1/2:ℝ) 3)
    (hsM : Function.support FM ⊆ Icc (1/2:ℝ) 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N d s : ℕ) (T Q V : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 72 ≤ T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      0 < Q → 0 < V → Q ≤ 2*T → V ≤ 2*T → (2:ℝ)^s ≤ T^geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let J := PRZZWindowCentralAssembly.bodyCut T V eH s d 0 0 0
      ‖PRZZSignedCentral.signedLiteral (-1) N d (deltaCutoff T ((2:ℝ)^s) Q eD) ((J:ℝ)+1) T ((2:ℝ)^s)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 V) FM Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))‖ ≤
      C*T^(delta+gamma+eD+eH)*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨C,hC,h⟩ := PRZZNegativeActiveRows.rows_absorbed hWeil hDI K hK js
    eps eta b (eD+eH+2) delta gamma S (1+S) (geom+1) (2*S) r
    heps heta hb (by linarith) hgamma hS (by linarith) (by linarith) (by linarith) hr
    (by convert hmargin using 1; ring)
    F0 F2 FM hf hc hF hcF hFM hcM
  refine ⟨18*C,by positivity,?_⟩
  intro N d s T Q V A B Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp hA hB hsep hPhi hsPhi
  dsimp only
  have ht : 1 < T := by linarith
  have hshift := PRZZCentralGridWeilDI.scaled_shift_conditions S T A B hS hlog hA hB
  have hm : 0 < (2:ℝ)^s := by positivity
  let D := deltaCutoff T ((2:ℝ)^s) Q eD
  let J := PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) V eH
  by_cases hraw : poissonCutoff d T ((2:ℝ)^s) (3*V) eH ≤ 1
  · have hz : PRZZAStar.indices N d D 1 = ∅ := by simp [PRZZAStar.indices]
    dsimp only [D] at hz
    simp only [PRZZWindowCentralAssembly.bodyCut,if_pos hraw,Nat.cast_zero,zero_add]
    simp only [PRZZSignedCentral.signedLiteral,hz,sum_empty,norm_zero]
    unfold PRZZOptimalPowers.target
    positivity
  · have hj : PRZZWindowCentralAssembly.bodyCut T V eH s d 0 0 0 = J := by
      simp only [PRZZWindowCentralAssembly.bodyCut,if_neg hraw,PRZZWindowCentralAssembly.windowCut,J]
    rw [hj]
    rcases empty_or_envelope N d T ((2:ℝ)^s) Q V eD eH hd hT hm hQ.le hV.le hQT hVT
      (le_of_not_ge hraw) with hempty | ⟨hfreq,hpower,hlocal⟩
    · dsimp only [J]
      simp only [PRZZSignedCentral.signedLiteral,hempty,sum_empty,norm_zero]
      unfold PRZZOptimalPowers.target
      positivity
    · have hlam : 1 ≤ 18*T^(eD+eH) := by
        have hp := Real.one_le_rpow ht.le (show 0 ≤ eD+eH by linarith)
        linarith
      have hscale : ∀ l ∈ range (Nat.log 2 N+1),
          |Real.log ((2:ℝ)^s)|+|Real.log ((2:ℝ)^l)| ≤ (geom+1)*Real.log T := by
        intro l hl
        have hp : (2:ℝ)^l ≤ N := by
          exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
            (Nat.le_of_lt_succ (mem_range.mp hl))).trans
              (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
        exact row_log_scale N s l T geom ht hsp hp (by linarith)
      have hh := h V ((2:ℝ)^s) N d T Q D ((J:ℝ)+1) ((2:ℝ)^s) (18*T^(eD+eH)) Q V A B Phi
        hN hd ht hNT hdT hlog (by dsimp only [D,J]; exact_mod_cast hfreq) hpower hlocal hlam hm hQ.le hV.le
        (scaled_support F0 Q hQ hs0) (scaled_support F2 V hV hs2)
        (scaled_support FM ((2:ℝ)^s) hm hsM) hshift.2.2
        (PRZZCentralGridWeilDI.scaled_shift_conditions S T B A hS hlog hB hA).2.1
        hshift.1 hsep (sum_shift S T A B (by linarith) hA hB) hscale hPhi hsPhi
      rw [PRZZNegativeLiteralRows.literal_rows N d D ((J:ℝ)+1) T ((2:ℝ)^s)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 V) FM Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))
        hN (by linarith) hm
        (div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
          (by exact_mod_cast (show Real.log T ≠ 0 by linarith)))
        hFM hPhi.continuous hsM hsPhi]
      apply hh.trans_eq
      have hp : T^(delta+gamma+eD+eH) = T^(delta+gamma)*T^(eD+eH) := by
        rw [show delta+gamma+eD+eH = (delta+gamma)+(eD+eH) by ring,
          Real.rpow_add (by linarith : 0 < T)]
      rw [hp]
      ring


theorem negative_body_epsilon
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
      ∀ (N d s : ℕ) (T Q V : ℝ) (A B : ℂ) (Phi : ℝ → ℂ),
      0 < N → 0 < d → 72 ≤ T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      0 < Q → 0 < V → Q ≤ 2*T → V ≤ 2*T → (2:ℝ)^s ≤ T^geom →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let J := PRZZWindowCentralAssembly.bodyCut T V eH s d 0 0 0
      ‖PRZZSignedCentral.signedLiteral (-1) N d (deltaCutoff T ((2:ℝ)^s) Q eD) ((J:ℝ)+1) T ((2:ℝ)^s)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (scaledCutoff F0 Q) (scaledCutoff F2 V) FM Phi
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))‖ ≤
      C*T^tau*PRZZOptimalPowers.target N T/d*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨eps,eta,b,delta,gamma,eD,eH,heps,heta,hb,hgamma,heD,he,hmarg,htotal⟩ := PRZZWindowOptimalCell.choose_losses tau htau
  obtain ⟨C,hC,h⟩ := negative_body hWeil hDI K hK js eps eta b delta gamma S r geom eD eH
    heps heta hb hgamma hS hr hgeom heD.le (heD.trans he).le hmarg
    F0 F2 FM hf hc hF hcF hFM hcM hs0 hs2 hsM
  refine ⟨eD,eH,C,heD,he,hC,?_⟩
  intro N d s T Q V A B Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp hA hB hsep hPhi hsPhi
  have hh := h N d s T Q V A B Phi hN hd hT hNT hdT hlog hQ hV hQT hVT hsp hA hB hsep hPhi hsPhi
  apply hh.trans
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) htotal.le
  have hmellin : 0 ≤ ∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖ := integral_nonneg (fun t => by positivity)
  have htarget : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  gcongr


#print axioms negative_body
#print axioms negative_body_epsilon
end XiPrime8845.PRZZNegativeWindowCell


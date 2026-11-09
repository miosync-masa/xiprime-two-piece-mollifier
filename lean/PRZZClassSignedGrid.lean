import PRZZClassPositiveGrid
import PRZZClassNegativeGrid

/-! Both spatial frequency signs at one common body cutoff. Zero modes,
Fourier tails and the other original residuals are not included here. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZClassSignedGrid
open PRZZMellinSeparation
set_option maxHeartbeats 10000000

def grid (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (js ks : List ℕ)
    (N : ℕ) (ss : Finset ℕ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ)
    (T eD eH : ℝ) (A B : ℂ) : ℂ :=
  PRZZClassPositiveGrid.grid F0 F2 F Phi js ks N ss w T eD eH A B+
    PRZZClassNegativeGrid.grid F0 F2 F Phi js ks N ss w T eD eH A B

theorem grid_target
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eD eH tau gamma S r geom : ℝ)
    (heD : 0 ≤ eD) (heH : 0 ≤ eH) (htau : 0 < tau) (hgamma : 0 < gamma)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ)
      (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets (F0 k)) →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets
        (scaledCutoff (F2 k) ((2:ℝ)^k))) →
      (∀ s ∈ ss, PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s))) →
      (∀ k, Function.support (F0 k) ⊆ Icc (1/2:ℝ) 3) →
      (∀ k, Function.support (F2 k) ⊆ Icc (1/2:ℝ) 3) →
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N, ‖w p s d‖ ≤ 1) →
      ‖grid F0 F2 F Phi js ks N ss w T eD eH A B‖ ≤
        C*T^(tau+eD+eH+gamma)*PRZZOptimalPowers.target N T := by
  obtain ⟨Cp,hCp,hp⟩ := PRZZClassPositiveGrid.grid_target hWeil hDI K hK js ks eD eH tau gamma
    S r geom heD heH htau hgamma hS hr hgeom width jets hjets widthPhi hwPhi jetsPhi hjPhi
  obtain ⟨Cn,hCn,hn⟩ := PRZZClassNegativeGrid.grid_target hWeil hDI K hK js ks eD eH tau gamma
    S r geom heD heH htau hgamma hS hr hgeom width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨Cp+Cn,by positivity,?_⟩
  intro L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  have hp' := hp L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  have hn' := hn L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  exact (norm_add_le _ _).trans ((add_le_add hp' hn').trans_eq (by ring))

theorem grid_optimized
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau)
    (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (widthPhi : ℝ) (hwPhi : 0 ≤ widthPhi) (jetsPhi : ℕ → ℝ) (hjPhi : ∀ n, 0 ≤ jetsPhi n) :
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < eH ∧ 0 < C ∧ ∀ (L N : ℕ) (ss : Finset ℕ) (T : ℝ) (A B : ℂ)
      (F0 F2 : ℕ → ℝ → ℂ) (F Phi : ℝ → ℂ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ),
      1 ≤ N → 72 ≤ T → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → S ≤ Real.log T →
      ss ⊆ PRZZWindowGrids.spatial L T geom →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets (F0 k)) →
      (∀ k ∈ range (Nat.log 2 N+2), PRZZProfileMellin.Member width jets
        (scaledCutoff (F2 k) ((2:ℝ)^k))) →
      (∀ s ∈ ss, PRZZProfileMellin.Member width jets (scaledCutoff F ((2:ℝ)^s))) →
      (∀ k, Function.support (F0 k) ⊆ Icc (1/2:ℝ) 3) →
      (∀ k, Function.support (F2 k) ⊆ Icc (1/2:ℝ) 3) →
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZProfileMellin.Member widthPhi jetsPhi Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N, ‖w p s d‖ ≤ 1) →
      ‖grid F0 F2 F Phi js ks N ss w T eD eH A B‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := grid_target hWeil hDI K hK js ks (tau/16) (tau/8) (tau/4) (tau/4)
    S r geom (by linarith) (by linarith) (by linarith) (by linarith) hS hr hgeom
    width jets hjets widthPhi hwPhi jetsPhi hjPhi
  refine ⟨tau/16,tau/8,C,by linarith,by linarith,hC,?_⟩
  intro L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hPhi hsPhi hw
  have hh := h L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF
    hA hB hsep hPhi hsPhi hw
  apply hh.trans
  have htar : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (by linarith : tau/4+tau/16+tau/8+tau/4 ≤ tau)) hC.le) htar


#print axioms grid_target
#print axioms grid_optimized
end XiPrime8845.PRZZClassSignedGrid

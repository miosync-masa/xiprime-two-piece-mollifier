import PRZZClassPositiveGrid
import PRZZClassDualProfile

/-! Both positive-body AFE branches with the genuine dual Gamma time
profile, at one common arithmetic cutoff. This leaves negative modes,
tails, boundary/freezing and zero-frequency corrections explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZClassPairedGrid
open PRZZMellinSeparation PRZZClassPositiveGrid
set_option maxHeartbeats 10000000

theorem paired_grid_optimized
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (tau S r geom : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) (hgeom : 0 ≤ geom)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∃ eD eH C : ℝ, 0 < eD ∧ eD < eH ∧ 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (ss : Finset ℕ) (A B : ℂ) (F0 F2 : ℕ → ℝ → ℂ)
        (F : ℝ → ℂ) (w : (ℕ × ℕ) → ℕ → ℕ → ℂ),
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
      (∀ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∀ s ∈ ss, ∀ d ∈ Finset.Icc 1 N, ‖w p s d‖ ≤ 1) →
      ‖grid F0 F2 F Phi js ks N ss w T eD eH A B+
        grid F0 F2 F (PRZZKeptLiteral.dualProfile Phi T
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) js ks N ss w T eD eH (-B) (-A)‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨J,hJ,hplain,hdual⟩ := PRZZClassDualProfile.common_members Phi hPhi hcPhi hsPhi S hS
  obtain ⟨eD,eH,C,hD,hDH,hC,h⟩ := grid_optimized hWeil hDI K hK js ks tau S r geom htau hS hr hgeom
    width jets hjets (Real.log 6) (Real.log_nonneg (by norm_num)) J hJ
  refine ⟨eD,eH,2*C,hD,hDH,by positivity,?_⟩
  filter_upwards [hdual] with T hdual
  intro L N ss A B F0 F2 F w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF hA hB hsep hw
  have h1 := h L N ss T A B F0 F2 F Phi w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF
    hA hB hsep hplain hsPhi hw
  have hsdual : Function.support (PRZZKeptLiteral.dualProfile Phi T
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) ⊆ Icc (1:ℝ) 2 := by
    intro x hx
    exact hsPhi (fun hz => hx (by simp [PRZZKeptLiteral.dualProfile,hz]))
  have hsep' : r ≤ ‖-B + -A‖ := by
    rw [show -B + -A = -(A+B) by ring,norm_neg]
    exact hsep
  have h2 := h L N ss T (-B) (-A) F0 F2 F _ w hN hT hNT hlog hST hss hf0 hf2 hfM hs0 hs2 hsF
    (by simpa only [norm_neg] using hB) (by simpa only [norm_neg] using hA) hsep'
    (hdual A B hA hB) hsdual hw
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

#print axioms paired_grid_optimized
end XiPrime8845.PRZZClassPairedGrid

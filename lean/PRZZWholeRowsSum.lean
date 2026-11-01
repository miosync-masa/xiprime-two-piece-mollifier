import PRZZZeroExtension
import PRZZSplitScaleOuter

/-! The supported h-average with actual whole-row variation supplied.
Arithmetic estimates and physical scale allocation remain explicit; there
are no retained-interval placement or zero-extension hypotheses. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZWholeRowsSum
open PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem rows_sum (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (js : List ℕ) (k : ℕ) (eps S Z c eta beta : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hc : 1 ≤ c)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T Q t sigma X A V Bs Bl : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → sigma ≤ 0 → 0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl →
      ∀ alpha : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ∀ s : Finset ℕ, ∀ j : ℕ → ℕ, ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ,
      (∀ h ∈ s, X/h ≤ c → ‖z h‖ ≤ Bs*PRZZTypeI.variation
        (fun n => PRZZResidualRow.weight N d (j h) h
          (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N) →
      (∀ h ∈ s, c < X/h → ‖z h‖ ≤ Bl*PRZZTypeI.variation
        (fun n => PRZZResidualRow.weight N d (j h) h
          (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N*
          seven h (E h) A (Y h) V) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        C*T^eps*(Bs+Bl*c^2*envelope X A V)*(d:ℝ)^eta*(N:ℝ)^beta*(1+|t|) := by
  obtain ⟨Cr,hCr,hr⟩ := PRZZZeroExtension.full_variation F0 hf hcF eps S Z heps hS hZ
  obtain ⟨Cg,hCg,hg⟩ := PRZZSplitScaleSum.mixed_sum js k eta beta heta hbeta
  refine ⟨Cg*Cr,by positivity,?_⟩
  intro N d hN hd T Q t sigma X A V Bs Bl hT hNT hsig hX hA hV hBs hBl
    alpha halpha hz s j E Y hs hscale z hzS hzL
  have hv (h : ℕ) (hh : h ∈ s) := hr N d h (j h) T Q t alpha hd (hs h hh).1 hT hNT
    ((by exact_mod_cast (show h ≤ N by nlinarith [(hs h hh).2.1]) : (h:ℝ) ≤ N).trans
      (by linarith)) halpha hz
  have hb := hg sigma d N hsig hd hN s X A V (Bs*(Cr*(1+|t|)*T^eps))
    (Bl*(Cr*(1+|t|)*T^eps)) c hX hA hV (by positivity) (by positivity) hc hs E Y hscale z
    (by intro h hh hU; exact (hzS h hh hU).trans (mul_le_mul_of_nonneg_left (hv h hh) hBs))
    (by
      intro h hh hU
      have hEh : 0 ≤ E h := (Real.rpow_nonneg (div_nonneg hX.le (Nat.cast_nonneg h)) _).trans
        (hscale h hh hU).2.1
      have hYh := (hscale h hh hU).1
      have hn : 0 ≤ seven h (E h) A (Y h) V := by unfold seven; positivity
      exact (hzL h hh hU).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv h hh) hBl) hn))
  exact hb.trans_eq (by ring)

#print axioms rows_sum

/-- The original outer integral with the whole-row variation discharged.
The literal decomposition, arithmetic block estimates and scale allocation
are still hypotheses, not an assertion of the completed PRZZ estimate. -/
theorem literal_rows (W Phi F0 : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (A B S Z c eps eta beta : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S)
    (hZ : 0 ≤ Z) (hc : 1 ≤ c) (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta)
    (js : List ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T Q : ℝ,
      1 < T → 1 ≤ Real.log T → (N:ℝ)+1 ≤ T →
      ∀ D H sigma X A0 V Bs Bl : ℝ,
      sigma ≤ 0 → 0 < X → 0 ≤ A0 → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl →
      ∀ s : Finset ℕ, ∀ j : ℕ → ℕ, ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ (a : ℕ → ℂ) (F2 FM : ℝ → ℂ) (alpha betaShift : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B →
      |(alpha+betaShift).re| ≤ S/Real.log T → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ∀ z : (ℝ × ℝ) → ℝ → ℕ → ℂ,
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t,
        PRZZAStarNu.signedSum N d D H a (PRZZMellinSeparation.scaledCutoff F0 Q)
          F2 FM alpha betaShift p.1 p.2 t = ∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z p t h) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        X/h ≤ c → ‖z p t h‖ ≤ Bs*PRZZTypeI.variation
          (fun n => PRZZResidualRow.weight N d (j h) h
            (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        c < X/h → ‖z p t h‖ ≤ Bl*PRZZTypeI.variation
          (fun n => PRZZResidualRow.weight N d (j h) h
            (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N*seven h (E h) A0 (Y h) V) →
      ‖PRZZAStar.literal N d D H T a (PRZZMellinSeparation.scaledCutoff F0 Q)
        F2 FM W Phi alpha betaShift‖ ≤
        C*(T/d)*T^eps*(Bs+Bl*c^2*envelope X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨Cr,hCr,hr⟩ := rows_sum F0 hf hcF js k eps S Z c eta beta heps hS hZ hc heta hbeta
  obtain ⟨Co,hCo,ho⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  refine ⟨Co*Cr,by positivity,?_⟩
  intro N d hN hd T Q hT hL hNT D H sigma X A0 V Bs Bl hsig hX hA0 hV hBs hBl
    s j E Y hs hscale a F2 FM alpha betaShift hFM hsM hshift halpha hz z hsplit hsmall hlarge
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T (by linarith) hL (by linarith) D H
    (Cr*T^eps*(Bs+Bl*c^2*envelope X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta) (by positivity)
    a (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift hFM hsM hshift (by
      intro p hp t
      rw [hsplit p hp t]
      exact hr N d hN hd T Q t sigma X A0 V Bs Bl hT hNT hsig hX hA0 hV hBs hBl
        alpha halpha hz s j E Y hs hscale (z p t) (hsmall p hp t) (hlarge p hp t))
  exact hb.trans_eq (by ring)

#print axioms literal_rows
end XiPrime8845.PRZZWholeRowsSum

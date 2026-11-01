import PRZZSplitScaleSum
import PRZZActualRowSmooth

/-! Both scale cases pass through the actual outer Mellin integral.
Small blocks use absolute supported G mass; only large blocks require
balanced scales. Literal decomposition and block estimates are explicit
inputs, not assertions that all original branches have been supplied. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZSplitScaleOuter
open PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem literal_mixed (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S)
    (js : List ℕ) (k : ℕ) (eta beta : ℝ) (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T →
      ∀ D H sigma X A0 V Bs Bl c : ℝ,
      sigma ≤ 0 → 0 < X → 0 ≤ A0 → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl → 1 ≤ c →
      ∀ s : Finset ℕ, ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha betaShift : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(alpha+betaShift).re| ≤ S/Real.log T →
      ∀ z : (ℝ × ℝ) → ℝ → ℕ → ℂ,
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t,
        PRZZAStarNu.signedSum N d D H a F1 F2 FM alpha betaShift p.1 p.2 t =
          ∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z p t h) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        X/h ≤ c → ‖z p t h‖ ≤ Bs*(1+|t|)) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        c < X/h → ‖z p t h‖ ≤ Bl*(1+|t|)*seven h (E h) A0 (Y h) V) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi alpha betaShift‖ ≤
        C*(T/d)*(Bs+Bl*c^2*envelope X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨Co,hCo,ho⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := PRZZSplitScaleSum.mixed_sum js k eta beta heta hbeta
  refine ⟨Co*Cg,by positivity,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V Bs Bl c hsig hX hA0 hV hBs hBl hc
    s E Y hs hscale a F1 F2 FM alpha betaShift hFM hsM hshift z hsplit hsmall hlarge
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (Cg*(Bs+Bl*c^2*envelope X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta) (by positivity)
    a F1 F2 FM alpha betaShift hFM hsM hshift (by
      intro p hp t
      rw [hsplit p hp t]
      have hh := hg sigma d N hsig hd hN s X A0 V (Bs*(1+|t|)) (Bl*(1+|t|)) c
        hX hA0 hV (by positivity) (by positivity) hc hs E Y hscale (z p t)
        (hsmall p hp t) (hlarge p hp t)
      exact hh.trans_eq (by ring))
  exact hb.trans_eq (by ring)

/-- Actual row variation is supplied, rather than left as an assumption.
Only the arithmetic block bounds and placement of the large intervals
remain inputs. The result has the frequency growth used by literal_mixed. -/
theorem rows_sum (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hcF : HasCompactSupport F0)
    (js : List ℕ) (k : ℕ) (eps S Z c eta beta : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hc : 1 ≤ c)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d → ∀ T Q t sigma X A V Bs Bl : ℝ,
      1 < T → (N:ℝ) ≤ T → sigma ≤ 0 → 0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl →
      ∀ alpha : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ∀ s : Finset ℕ, ∀ j a H : ℕ → ℕ, ∀ F E Y : ℕ → ℝ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, X/h ≤ c → (PRZZRowWindow.hi N d h (j h):ℝ) ≤ c*(X/h)) →
      (∀ h ∈ s, c < X/h → 1 ≤ a h ∧ a h ≤ PRZZRowWindow.hi N d h (j h) ∧
        0 < F h ∧ F h ≤ a h ∧ (a h:ℝ)+H h ≤ T ∧ (H h:ℝ) ≤ 2*F h) →
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ,
      (∀ h ∈ s, X/h ≤ c → ‖z h‖ ≤ Bs*PRZZTypeI.variation
        (PRZZActualRowSmooth.selected N d (j h) h (a h) F0 Q t (X/h) c alpha) (H h)) →
      (∀ h ∈ s, c < X/h → ‖z h‖ ≤ Bl*PRZZTypeI.variation
        (PRZZActualRowSmooth.selected N d (j h) h (a h) F0 Q t (X/h) c alpha) (H h)*
          seven h (E h) A (Y h) V) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        C*T^eps*(Bs+Bl*c^2*envelope X A V)*(d:ℝ)^eta*(N:ℝ)^beta*(1+|t|) := by
  obtain ⟨Cr,hCr,hr⟩ := PRZZActualRowSmooth.selected_variation F0 hf hcF eps S Z c
    heps hS hZ (by linarith)
  obtain ⟨Cg,hCg,hg⟩ := PRZZSplitScaleSum.mixed_sum js k eta beta heta hbeta
  refine ⟨Cg*Cr,by positivity,?_⟩
  intro N d hN hd T Q t sigma X A V Bs Bl hT hNT hsig hX hA hV hBs hBl
    alpha halpha hz s j a H F E Y hs hsmall hlarge hscale z hzS hzL
  have hv (h : ℕ) (hh : h ∈ s) := hr N d (j h) h (a h) (H h) T Q (F h) t (X/h) alpha
    hd (hs h hh).1 hT hNT
    ((by exact_mod_cast (show h ≤ N by nlinarith [(hs h hh).2.1]) : (h:ℝ) ≤ N).trans hNT)
    halpha hz (hsmall h hh) (hlarge h hh)
  have hcost : 0 ≤ Cr*(1+|t|)*T^eps := by positivity
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

#print axioms literal_mixed
#print axioms rows_sum
end XiPrime8845.PRZZSplitScaleOuter

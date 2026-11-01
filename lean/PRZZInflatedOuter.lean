import PRZZInflatedSeven
import PRZZLinearOuter

/-! Supported G average and actual outer integration with inflated DI
boxes and an explicit variation budget. Source decomposition and the
analytic variation supplier remain hypotheses, not new axioms. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory
namespace XiPrime8845.PRZZInflatedOuter
open PRZZDISeven PRZZGCoefficient
set_option maxHeartbeats 2000000

theorem source_h_sum (js : List ℕ) (k : ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, ∀ d N : ℕ,
      sigma ≤ 0 → 1 ≤ d → 1 ≤ N → ∀ s : Finset ℕ, ∀ X A V B c : ℝ,
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ B → 1 ≤ c →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ, (∀ h ∈ s, ‖z h‖ ≤ B*seven h (E h) A (Y h) V) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        B*c^2*envelope X A V*(C*(d:ℝ)^eta*(N:ℝ)^beta) := by
  obtain ⟨C,hC,hg⟩ := PRZZGAbsorption.sourceG_average_power js k (3/8) eta beta
    (by norm_num) heta hbeta
  refine ⟨C,hC,?_⟩
  intro sigma d N hsig hd hN s X A V B c hX hA hV hB hc hs E Y hscale z hz
  have he : 0 ≤ envelope X A V := by unfold envelope; positivity
  have hb := PRZZSharpAggregation.branch_sum_bound s (fun h => (sourceG js k sigma d h:ℂ)) z
    (fun h => B*(c^2*(envelope X A V/(h:ℝ)^(3/8:ℝ)))) (by
      intro h hh
      exact (hz h hh).trans (mul_le_mul_of_nonneg_left
        (PRZZInflatedSeven.seven_h_bound h (E h) X (Y h) A V c
          (by exact_mod_cast (hs h hh).1) hX (hscale h hh).1 hA hV hc
          (hscale h hh).2.1 (hscale h hh).2.2.1 (hscale h hh).2.2.2) hB))
  simp only [Complex.norm_real,Real.norm_eq_abs] at hb
  have heq : (∑ h ∈ s, |sourceG js k sigma d h| * (B*(c^2*(envelope X A V/(h:ℝ)^(3/8:ℝ))))) =
      B*c^2*envelope X A V*(∑ h ∈ s, |sourceG js k sigma d h|/(h:ℝ)^(3/8:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [heq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hg sigma d N hsig hd hN s hs) (by positivity))

/-- The variation may grow linearly in Mellin frequency, not in the
height-dependent outer constant. Fixed cutoff Mellin mass absorbs it. -/
theorem literal_variation_blocks (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S)
    (js : List ℕ) (k : ℕ) (eta beta : ℝ) (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T →
      ∀ D H sigma X A0 V B0 J c : ℝ,
      sigma ≤ 0 → 0 < X → 0 ≤ A0 → 0 ≤ V → 0 ≤ B0 → 0 ≤ J → 1 ≤ c →
      ∀ s : Finset ℕ, ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha betaShift : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(alpha+betaShift).re| ≤ S/Real.log T →
      ∀ z : (ℝ × ℝ) → ℝ → ℕ → ℂ, ∀ variation : (ℝ × ℝ) → ℝ → ℕ → ℝ,
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t,
        PRZZAStarNu.signedSum N d D H a F1 F2 FM alpha betaShift p.1 p.2 t =
          ∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z p t h) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        ‖z p t h‖ ≤ B0*variation p t h*seven h (E h) A0 (Y h) V) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        variation p t h ≤ J*(1+|t|)) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi alpha betaShift‖ ≤
        C*(T/d)*B0*J*c^2*envelope X A0 V*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨Co,hCo,ho⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := source_h_sum js k eta beta heta hbeta
  refine ⟨Co*Cg,by positivity,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V B0 J c hsig hX hA0 hV hB0 hJ hc s E Y hs hscale
    a F1 F2 FM alpha betaShift hFM hsM hshift z variation hsplit hblock hvar
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (B0*J*c^2*envelope X A0 V*(Cg*(d:ℝ)^eta*(N:ℝ)^beta)) (by positivity)
    a F1 F2 FM alpha betaShift hFM hsM hshift (by
      intro p hp t
      rw [hsplit p hp t]
      have hh := hg sigma d N hsig hd hN s X A0 V (B0*J*(1+|t|)) c hX hA0 hV
        (by positivity) hc hs E Y hscale (z p t) (by
          intro h hh
          have hEh : 0 ≤ E h := (Real.rpow_nonneg (div_nonneg hX.le (Nat.cast_nonneg h)) _).trans (hscale h hh).2.1
          have hYh : 0 ≤ Y h := (hscale h hh).1
          have hn : 0 ≤ seven h (E h) A0 (Y h) V := by unfold seven; positivity
          exact (hblock p hp t h hh).trans ((mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hvar p hp t h hh) hB0) hn).trans_eq (by ring)))
      exact hh.trans_eq (by ring))
  exact hb.trans_eq (by ring)

#print axioms source_h_sum
#print axioms literal_variation_blocks
end XiPrime8845.PRZZInflatedOuter

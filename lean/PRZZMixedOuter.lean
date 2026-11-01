import PRZZCombinedBudget
import PRZZSplitScaleSum

/-! Joint transport of small cells and Type I plus Type II large cells.
The supported G average is supplied; cell bounds and the exact original
arithmetic decomposition remain explicit hypotheses. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZMixedOuter
open PRZZGCoefficient PRZZDISeven PRZZCombinedBudget
set_option maxHeartbeats 2000000

theorem mixed_sum (js : List ℕ) (k : ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, ∀ d N : ℕ,
      sigma ≤ 0 → 1 ≤ d → 1 ≤ N → ∀ s : Finset ℕ, ∀ X A V Bs Bl c : ℝ,
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ Bs → 0 ≤ Bl → 1 ≤ c →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ E Y : ℕ → ℝ,
      (∀ h ∈ s, c < X/h → 0 ≤ Y h ∧ (X/h)^(1/4:ℝ) ≤ E h ∧
        E h ≤ c*(X/h)^(1/2:ℝ) ∧ Y h ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ,
      (∀ h ∈ s, X/h ≤ c → ‖z h‖ ≤ Bs) →
      (∀ h ∈ s, c < X/h → ‖z h‖ ≤ Bl*(typeI (X/h) A V+seven h (E h) A (Y h) V)) →
      ‖∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z h‖ ≤
        C*(Bs+Bl*c^2*total X A V)*(d:ℝ)^eta*(N:ℝ)^beta := by
  classical
  obtain ⟨Cs,hCs,hsmall⟩ := PRZZSplitScaleSum.absolute_mass js k eta beta heta hbeta
  obtain ⟨Cl,hCl,hlarge⟩ := PRZZCombinedBudget.source_h_sum js k eta beta heta hbeta
  refine ⟨Cs+Cl,by positivity,?_⟩
  intro sigma d N hsig hd hN s X A V Bs Bl c hX hA hV hBs hBl hc hs E Y hscale z hzS hzL
  let q := fun h : ℕ => X/(h:ℝ) ≤ c
  have ha : ‖∑ h ∈ s.filter q, (sourceG js k sigma d h:ℂ)*z h‖ ≤
      Bs*(Cs*(d:ℝ)^eta*(N:ℝ)^beta) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ h ∈ s.filter q, |sourceG js k sigma d h| * Bs := by
        apply sum_le_sum
        intro h hh
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hzS h (mem_filter.mp hh).1 (mem_filter.mp hh).2) (abs_nonneg _)
      _ = Bs*(∑ h ∈ s.filter q, |sourceG js k sigma d h|) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hsmall sigma d N hsig hd hN _ (fun h hh => hs h (mem_filter.mp hh).1)) hBs
  have hb := hlarge sigma d N hsig hd hN (s.filter (fun h => ¬q h)) X A V Bl c
    hX hA hV hBl hc (fun h hh => hs h (mem_filter.mp hh).1) E Y
    (fun h hh => hscale h (mem_filter.mp hh).1 (lt_of_not_ge (mem_filter.mp hh).2)) z
    (fun h hh => hzL h (mem_filter.mp hh).1 (lt_of_not_ge (mem_filter.mp hh).2))
  rw [← sum_filter_add_sum_filter_not s q]
  apply (norm_add_le _ _).trans
  apply (add_le_add ha hb).trans
  have he : 0 ≤ total X A V := by unfold total typeI envelope; positivity
  have hde : 0 ≤ (d:ℝ)^eta := by positivity
  have hnb : 0 ≤ (N:ℝ)^beta := by positivity
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCs.le hBl) (sq_nonneg c)) he,
    mul_nonneg hCl.le hBs,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs.le hBl) (sq_nonneg c)) he) hde) hnb,
    mul_nonneg (mul_nonneg (mul_nonneg hCl.le hBs) hde) hnb]


#print axioms mixed_sum

/-- The fixed Mellin L1 cost absorbs the linear frequency loss in both
scale regimes. No balanced box is required for a small h-block. -/
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
        c < X/h → ‖z p t h‖ ≤ Bl*(1+|t|)*(typeI (X/h) A0 V+seven h (E h) A0 (Y h) V)) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi alpha betaShift‖ ≤
        C*(T/d)*(Bs+Bl*c^2*total X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨Co,hCo,ho⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := mixed_sum js k eta beta heta hbeta
  refine ⟨Co*Cg,by positivity,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V Bs Bl c hsig hX hA0 hV hBs hBl hc s E Y hs hscale
    a F1 F2 FM alpha betaShift hFM hsM hshift z hsplit hsmall hlarge
  have he : 0 ≤ total X A0 V := by unfold total typeI envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (Cg*(Bs+Bl*c^2*total X A0 V)*(d:ℝ)^eta*(N:ℝ)^beta) (by positivity)
    a F1 F2 FM alpha betaShift hFM hsM hshift (by
      intro p hp t
      rw [hsplit p hp t]
      have hh := hg sigma d N hsig hd hN s X A0 V (Bs*(1+|t|)) (Bl*(1+|t|)) c
        hX hA0 hV (by positivity) (by positivity) hc hs E Y hscale (z p t)
        (hsmall p hp t) (hlarge p hp t)
      exact hh.trans_eq (by ring))
  exact hb.trans_eq (by ring)

#print axioms literal_mixed
end XiPrime8845.PRZZMixedOuter

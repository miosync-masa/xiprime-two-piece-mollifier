import PRZZEffectiveBalance
import PRZZInflatedOuter

/-! Supported h averaging for literal clipped HB boxes. The analytic
block estimate remains explicit; scale conditions refer to actual factors,
not an independently postulated E,Y family. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZEffectiveAverage
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZGCoefficient PRZZDISeven
set_option maxHeartbeats 2000000

theorem source_h_sum (js : List ℕ) (j : ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, ∀ d N : ℕ,
      sigma ≤ 0 → 1 ≤ d → 1 ≤ N → ∀ s : Finset ℕ, ∀ X A V B c : ℝ,
      0 < X → 0 ≤ A → 0 ≤ V → 0 ≤ B → 1 ≤ c →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ b : ℕ → Branch, ∀ k : (h : ℕ) → Fin (b h).2.length → ℕ,
      ∀ idx : (h : ℕ) → Finset (Fin (b h).2.length),
      (∀ h ∈ s, 1 ≤ X/h ∧ X/h ≤ N ∧
        (X/h)^(1/4:ℝ) ≤ ∏ i ∈ idx h, (2:ℝ)^(k h i)) →
      (∀ h ∈ s,
        (∏ i ∈ idx h, (2:ℝ)^(k h i+1)) ≤ c*(X/h)^(1/2:ℝ) ∧
        (∏ i ∈ idx h, (2:ℝ)^(k h i+1))*(∏ i ∈ univ \ idx h, (2:ℝ)^(k h i+1)) ≤ c*(X/h)) →
      ∀ z : ℕ → ℂ,
      (∀ h ∈ s, ‖z h‖ ≤ B*seven h (upper N (b h) (k h) (idx h)) A
        ((upper N (b h) (k h) (idx h):ℝ)*(upper N (b h) (k h) (univ \ idx h):ℝ)) V) →
      ‖∑ h ∈ s, (sourceG js j sigma d h:ℂ)*z h‖ ≤
        B*c^2*envelope X A V*(C*(d:ℝ)^eta*(N:ℝ)^beta) := by
  obtain ⟨C,hC,h⟩ := PRZZInflatedOuter.source_h_sum js j eta beta heta hbeta
  refine ⟨C,hC,?_⟩
  intro sigma d N hsig hd hN s X A V B c hX hA hV hB hc hs b k idx hlo hhi z hz
  exact h sigma d N hsig hd hN s X A V B c hX hA hV hB hc hs
    (fun h => upper N (b h) (k h) (idx h))
    (fun h => (upper N (b h) (k h) (idx h):ℝ)*(upper N (b h) (k h) (univ \ idx h):ℝ))
    (fun h hh => PRZZEffectiveBalance.clipped N (b h) (k h) (idx h) (X/h) c
      (hlo h hh).1 (hlo h hh).2.1 (hlo h hh).2.2 (hhi h hh).1 (hhi h hh).2) z hz

#print axioms source_h_sum
/-- The variation may grow linearly in Mellin frequency, not in the
height-dependent outer constant. Fixed cutoff Mellin mass absorbs it. -/
theorem literal_actual_boxes (W Phi : ℝ → ℂ) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (A B S : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 ≤ S)
    (js : List ℕ) (k : ℕ) (eta beta : ℝ) (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d : ℕ, 0 < N → 0 < d → ∀ T : ℝ,
      0 < T → 1 ≤ Real.log T → (N:ℝ) ≤ T →
      ∀ D H sigma X A0 V B0 J c : ℝ,
      sigma ≤ 0 → 0 < X → 0 ≤ A0 → 0 ≤ V → 0 ≤ B0 → 0 ≤ J → 1 ≤ c →
      ∀ s : Finset ℕ, ∀ b : ℕ → Branch,
      ∀ ks : (h : ℕ) → Fin (b h).2.length → ℕ,
      ∀ idx : (h : ℕ) → Finset (Fin (b h).2.length),
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, 1 ≤ X/h ∧ X/h ≤ N ∧
        (X/h)^(1/4:ℝ) ≤ ∏ i ∈ idx h, (2:ℝ)^(ks h i)) →
      (∀ h ∈ s,
        (∏ i ∈ idx h, (2:ℝ)^(ks h i+1)) ≤ c*(X/h)^(1/2:ℝ) ∧
        (∏ i ∈ idx h, (2:ℝ)^(ks h i+1))*(∏ i ∈ univ \ idx h, (2:ℝ)^(ks h i+1)) ≤ c*(X/h)) →
      ∀ (a : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha betaShift : ℂ),
      Continuous FM → Function.support FM ⊆ Set.Icc A B → |(alpha+betaShift).re| ≤ S/Real.log T →
      ∀ z : (ℝ × ℝ) → ℝ → ℕ → ℂ, ∀ variation : (ℝ × ℝ) → ℝ → ℕ → ℝ,
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t,
        PRZZAStarNu.signedSum N d D H a F1 F2 FM alpha betaShift p.1 p.2 t =
          ∑ h ∈ s, (sourceG js k sigma d h:ℂ)*z p t h) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        ‖z p t h‖ ≤ B0*variation p t h*seven h (upper N (b h) (ks h) (idx h)) A0 ((upper N (b h) (ks h) (idx h):ℝ)*(upper N (b h) (ks h) (univ \ idx h):ℝ)) V) →
      (∀ p ∈ PRZZAStarWindow.window N T A B, ∀ t, ∀ h ∈ s,
        variation p t h ≤ J*(1+|t|)) →
      ‖PRZZAStar.literal N d D H T a F1 F2 FM W Phi alpha betaShift‖ ≤
        C*(T/d)*B0*J*c^2*envelope X A0 V*(d:ℝ)^eta*(N:ℝ)^beta := by
  obtain ⟨Co,hCo,ho⟩ := PRZZLinearOuter.literal_linear_uniform W Phi hW hPhi hsP A B S hA hB hS
  obtain ⟨Cg,hCg,hg⟩ := source_h_sum js k eta beta heta hbeta
  refine ⟨Co*Cg,by positivity,?_⟩
  intro N d hN hd T hT hL hNT D H sigma X A0 V B0 J c hsig hX hA0 hV hB0 hJ hc s b ks idx hs hlo hhi
    a F1 F2 FM alpha betaShift hFM hsM hshift z variation hsplit hblock hvar
  have he : 0 ≤ envelope X A0 V := by unfold envelope; positivity
  have hb := ho N d hN hd T hT hL hNT D H
    (B0*J*c^2*envelope X A0 V*(Cg*(d:ℝ)^eta*(N:ℝ)^beta)) (by positivity)
    a F1 F2 FM alpha betaShift hFM hsM hshift (by
      intro p hp t
      rw [hsplit p hp t]
      have hh := hg sigma d N hsig hd hN s X A0 V (B0*J*(1+|t|)) c hX hA0 hV
        (by positivity) hc hs b ks idx hlo hhi (z p t) (by
          intro h hh
          have hn : 0 ≤ seven h (upper N (b h) (ks h) (idx h)) A0
              ((upper N (b h) (ks h) (idx h):ℝ)*(upper N (b h) (ks h) (univ \ idx h):ℝ)) V := by
            unfold seven; positivity
          exact (hblock p hp t h hh).trans ((mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hvar p hp t h hh) hB0) hn).trans_eq (by ring)))
      exact hh.trans_eq (by ring))
  exact hb.trans_eq (by ring)

#print axioms literal_actual_boxes
end XiPrime8845.PRZZEffectiveAverage

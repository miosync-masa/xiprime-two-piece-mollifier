import PRZZDualDiscardedBudget
import PRZZDiscardedAFEBridge
import PRZZWindowErrorJoin

/-! The genuine dual discarded integral joins the existing optimal budget.
The original selected AFE family is identified exactly, including cutoff
values. These displayed errors are not declared the entire AFE remainder. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Filter
namespace XiPrime8845.PRZZDualWindowErrorJoin
open PRZZMellinSeparation PRZZWindowErrorJoin
set_option maxHeartbeats 8000000

theorem selected_family_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (Q V : ℝ) (A B : ℂ) (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ (fun x => (P x:ℂ)) → Antitone P →
      (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖∫ t : ℝ, (scaledCutoff F T t*
        PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)*
        PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
          (scaledCutoff G Q) (scaledCutoff H V)
          (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
          (PRZZSourceMaskFamily.discarded T Q eps)
          (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,hh⟩ := PRZZDualDiscardedBudget.scaled_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps power hS hr he he1
  refine ⟨C,hC,?_⟩
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with T hh hT
  intro L J N Q V A B P hN hNT hQ hA hB hsep hP hm hlo hhi hleft hright
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  rw [← PRZZDiscardedAFEBridge.outer_family F G H P js L J N hsF hP hleft hright
    T Q V eps (by linarith) hQ _ _ hs]
  exact hh N (L+2) 1 Q V 1 A B P (fun _ _ => Finset.range L ×ˢ Finset.range L)
    hN hNT (by norm_num) hQ (by norm_num) hA hB hsep hm hlo hhi hleft hright

/-- No dual Gamma derivative or coefficient-mass cap is a premise.
Both actual discarded integrals share the existing PRZZ target. -/
theorem common_budget (F G H W : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 < eD) (heD1 : eD ≤ 1) (he : eD < eH) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N K : ℕ) (dual : Bool) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d → 4*(N:ℝ)*T^b ≤ L →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖replacement F js N T A B‖+
        ‖PRZZValuedSourceDiscarded.error F G H P js N K T M Q V d eD A B s‖+
        (∫ t in Icc T (2*T), ‖scaledCutoff F T t‖*
          PRZZWindowNativeTail.nativeMass G H W js L N dual T Q V b eD eH t A B)+
        ‖boundary F G H W js L J N dual T Q V b A B‖+
        ‖PRZZDualDiscardedIBP.outerValue F G H P js N K T M Q V d eD
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) s‖ ≤
          C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hh⟩ := PRZZWindowErrorJoin.common_budget F G H W hF hcF hsF
    hG hH hcG hcH hsG hW hsW js a b S r eD eH delta ha hb hS hr heD heD1 he hdelta
  obtain ⟨D,hD,hd⟩ := PRZZDualDiscardedBudget.scaled_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eD 0 hS hr heD heD1
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hh,hd,eventually_ge_atTop (1:ℝ)] with T hh hd hT
  intro L J N K dual M Q V d A B P s hN hNT hM hQ hd0 hL hA hB hsep hm hlo hhi hleft hright
  have h1 := hh L J N K dual M Q V d A B P s hN hNT hM hQ hd0 hL
    hA hB hsep hm hlo hhi hleft hright
  have h2 := hd N K M Q V d A B P s hN hNT hM hQ hd0 hA hB hsep hm hlo hhi hleft hright
  simp only [neg_zero,Real.rpow_zero,mul_one] at h2
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbase : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    (Real.one_le_rpow hT hdelta.le).trans (le_mul_of_one_le_right (by positivity) htarg)
  have h2' := h2.trans (le_mul_of_one_le_right hD.le hbase)
  nlinarith only [h1,h2']

#print axioms selected_family_negligible
#print axioms common_budget
end XiPrime8845.PRZZDualWindowErrorJoin

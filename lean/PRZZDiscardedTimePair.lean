import PRZZDualWindowErrorJoin

/-! The two actual discarded selected-family integrals. The direct
exact phase is reconstructed before applying its arithmetic bound; the
dual Gamma multiplier stays inside the time integral. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Filter
namespace XiPrime8845.PRZZDiscardedTimePair
open PRZZMellinSeparation PRZZDiscardedOuter PRZZDiscardedAFEBridge
set_option maxHeartbeats 8000000

def selected (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
    (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (PRZZSourceMaskFamily.discarded T Q eps) alpha beta t

theorem time_window (F : ℝ → ℂ) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) :
    (∫ t : ℝ, scaledCutoff F T t*f t) = ∫ t in Set.Icc T (2*T), scaledCutoff F T t*f t := by
  calc
    _ = ∫ t : ℝ, (Set.Icc T (2*T)).indicator (fun t => scaledCutoff F T t*f t) t := by
      apply integral_congr_ae
      apply Eventually.of_forall; intro t
      by_cases ht : t ∈ Set.Icc T (2*T)
      · simp [ht]
      · have hz : scaledCutoff F T t = 0 := by
          by_contra hn
          have hh := hsF (show F (T⁻¹*t) ≠ 0 from hn)
          have he : T*(T⁻¹*t) = t := by field_simp
          exact ht ⟨by nlinarith [mul_le_mul_of_nonneg_left hh.1 hT.le],
            by nlinarith [mul_le_mul_of_nonneg_left hh.2 hT.le]⟩
        simp [ht,hz]
    _ = _ := integral_indicator measurableSet_Icc

theorem direct_family (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (hQ : 0 < Q) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    tailError F js N T alpha beta (alpha+beta)
      (fun _ _ => range L ×ˢ range L)
      (fun u v p => (scaledCutoff G Q u*scaledCutoff H V v)*
        sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p) =
      ∫ t : ℝ, scaledCutoff F T t*selected P G H js L J N T Q V eps alpha beta t := by
  unfold tailError
  have hp (t : ℝ) :
      (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        row F T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta (alpha+beta) u v
          (range L ×ˢ range L) (fun p => (scaledCutoff G Q u*scaledCutoff H V v)*
            sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p) t) =
        scaledCutoff F T t*PRZZSourceMaskFamily.masked L N P (scaledCutoff G Q)
          (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T Q eps alpha beta t := by
    calc
      _ = scaledCutoff F T t*∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ range L ×ˢ range L,
          ((scaledCutoff G Q u*scaledCutoff H V v)*
            sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p)*
          PRZZL1Finite.term (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta
            (PRZZActualDirectSum.mainWeight alpha beta) t (p.1+1) (p.2+1) u v := by
        simp only [row,mul_sum]
        apply sum_congr rfl; intro u hu
        apply sum_congr rfl; intro v hv
        apply sum_congr rfl; intro p hp
        rw [term_phase _ alpha beta _ t _ _ u v (by omega) (by omega)
          (mem_Icc.mp hu).1 (mem_Icc.mp hv).1,PRZZWRowReindex.weight_eq]
        unfold PRZZTimeAmplitude.amplitude PRZZTimeJets.reciprocal
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        ring
      _ = _ := by
        unfold PRZZSourceMaskFamily.masked
        congr 1
        have hh := four_sum L N (fun i =>
          ((scaledCutoff G Q i.2.1*scaledCutoff H V i.2.2)*
            sourceMask P (scaledCutoff G Q) (L+2) T 1 Q 1 eps i.2.1 i.2.2
              (i.1.1-1,i.1.2-1))*
          PRZZL1Finite.term (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta
            (PRZZActualDirectSum.mainWeight alpha beta) t i.1.1 i.1.2 i.2.1 i.2.2)
        simpa only [Nat.add_sub_cancel,Prod.mk.eta] using hh
  apply integral_congr_ae
  apply Eventually.of_forall; intro t
  dsimp only
  rw [hp]
  by_cases hf : scaledCutoff F T t = 0
  · simp [hf]
  · have hh := (hsF (show F (T⁻¹*t) ≠ 0 from hf)).1
    have ht : 0 < t := by
      have he : T*(T⁻¹*t) = t := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hh hT.le]
    rw [PRZZSourceMaskFamily.masked_family L J N P _ _ hP hleft hright _
      T Q eps hT hQ alpha beta hs t ht]
    rfl

def pair (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Set.Icc T (2*T), scaledCutoff F T t*selected P G H js L J N T Q V eps alpha beta t)+
    ∫ t in Set.Icc T (2*T), (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
      selected P G H js L J N T Q V eps (-beta) (-alpha) t

theorem scaled_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (Q V : ℝ) (A B : ℂ) (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ (fun x => (P x:ℂ)) → Antitone P →
      (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖pair F G H P js L J N T Q V eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-power) := by
  obtain ⟨Cd,hCd,hd⟩ := PRZZValuedSourceDiscarded.scaled_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps power hr he he1
  obtain ⟨Ce,hCe,hh⟩ := PRZZDualWindowErrorJoin.selected_family_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps power hS hr he he1
  refine ⟨Cd+Ce,by positivity,?_⟩
  filter_upwards [hd,hh,eventually_gt_atTop (1:ℝ)] with T hd hh hT
  intro L J N Q V A B P hN hNT hQ hA hB hsep hP hm hlo hhi hleft hright
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  have h1 := hd N (L+2) 1 Q V 1 A B P (fun _ _ => range L ×ˢ range L)
    hN hNT (by norm_num) hQ (by norm_num) hA hB hsep hm hlo hhi hleft hright
  have heq : PRZZValuedSourceDiscarded.error F G H P js N (L+2) T 1 Q V 1 eps A B
      (fun _ _ => range L ×ˢ range L) =
      ∫ t in Set.Icc T (2*T), scaledCutoff F T t*
        selected P G H js L J N T Q V eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t := by
    unfold PRZZValuedSourceDiscarded.error
    simp only [one_mul]
    rw [add_div,direct_family F G H P js L J N hsF hP hleft hright T Q V eps
      (by linarith) hQ _ _ hs,time_window F hsF T (by linarith)]
  rw [heq] at h1
  have h2 := hh L J N Q V A B P hN hNT hQ hA hB hsep hP hm hlo hhi hleft hright
  simp_rw [mul_assoc] at h2
  rw [time_window F hsF T (by linarith)] at h2
  simp_rw [← mul_assoc] at h2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

#print axioms time_window
#print axioms direct_family
#print axioms scaled_negligible
end XiPrime8845.PRZZDiscardedTimePair

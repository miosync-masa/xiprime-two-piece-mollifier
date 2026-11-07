import PRZZAllPoissonAFE
import PRZZLiteralComplement

/-! Transfer the actual source-cutoff complement estimate to the full
resolved Poisson family. The source Delta mask is NOT confused with the
small-ratio guard deciding whether a row is Poisson-expanded. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Finset
namespace XiPrime8845.PRZZResolvedComplement
open PRZZAllPoissonRows PRZZAllOffDiagonalRows PRZZWRowReindex PRZZWRowLimit PRZZAFEIndices
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def masked (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ range (L+2), ∑ z ∈ labels L N, if z.2.1 ≠ 0 ∧ R s z then
    ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, if pairMatches z n r then
      resolved L J (profile F) F1 F2 ((2:ℝ)^s)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-z.2.1,1)) alpha beta a (Nat.gcd n r) t
    else 0 else 0

theorem exhaustive (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    family L J N F F1 F2 a alpha beta t =
      masked L J N F F1 F2 a R alpha beta t+
      masked L J N F F1 F2 a (fun s z => ¬R s z) alpha beta t := by
  unfold family masked
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro s hss
  apply sum_congr rfl
  intro z hz
  by_cases hg : z.2.1 ≠ 0 <;> by_cases hr : R s z <;> simp [hg,hr]

theorem masked_original (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (a : ℕ → ℂ) (R : ℕ → Label → Prop) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    masked L J N F F1 F2 a R alpha beta t =
      PRZZWRowLimit.retained L N F R (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t := by
  have hf := profile_regular F hF hlo hhi
  unfold masked PRZZWRowLimit.retained
  apply sum_congr rfl
  intro s hss
  apply sum_congr rfl
  intro z hz
  by_cases hg : z.2.1 ≠ 0 ∧ R s z
  · simp only [if_pos hg]
    rw [row_reindex]
    unfold literalRows
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro r hr
    by_cases hp : pairMatches z n r
    · simp only [if_pos hp]
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hr0 : 0 < r := (mem_Icc.mp hr).1
      have hd : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn0
      have hu : 0 < n/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_left r hn0) hd
      have hv : 0 < r/Nat.gcd n r := Nat.div_pos (Nat.gcd_le_right n hr0) hd
      exact (row_resolved L J (profile F) F1 F2 hf.1 hf.2.2 _ _ alpha beta a _ t
        (by positivity) ht hd hu hv (Nat.coprime_div_gcd_div_gcd hd) hs).symm
    · simp only [if_neg hp]
  · simp only [if_neg hg]

theorem complement_original (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (a : ℕ → ℂ) (R : ℕ → Label → Prop) (alpha beta : ℂ)
    (hs : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    masked L J N F F1 F2 a (fun s z => ¬R s z) alpha beta t =
      PRZZWRowLimit.complement L N F R (leftCoefficient a F1) (rightCoefficient a F2) alpha beta t := by
  rw [masked_original L J N F F1 F2 hF hlo hhi a (fun s z => ¬R s z) alpha beta hs t ht]
  unfold PRZZWRowLimit.retained PRZZWRowLimit.complement
  apply sum_congr rfl
  intro s hss
  apply sum_congr rfl
  intro z hz
  split_ifs <;> rfl

/-- Arbitrary-power source Delta decay, now for the actual fully
resolved complement, uniformly in both sharp and Fourier cutoffs L,J. -/
theorem source_complement_bound (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (eps power r : ℝ) (he : 0 < eps) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L J N : ℕ) (A B : ℂ) (T Q V : ℝ) (P : ℝ → ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 < T → 1 ≤ Real.log T → r ≤ ‖A+B‖ →
      0 ≤ 1/2+(A/(Real.log T:ℂ)).re → 0 ≤ 1/2+(B/(Real.log T:ℂ)).re →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ContDiff ℝ ∞ (fun x => (P x:ℂ)) → 0 < Q → 1 ≤ T^(1-eps) →
      ‖∫ t : ℝ, PRZZMellinSeparation.scaledCutoff F T t *
        masked L J N (fun x => (P x:ℂ))
          (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun j z => ¬ |(z.2.1:ℝ)| < PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ E*T^(-power) := by
  obtain ⟨E,hE,h⟩ := PRZZLiteralComplement.complete_complement_negligible F G H
    hF hcF hsF hG hH hcG hcH hsG js eps power r he hr
  refine ⟨E,hE,?_⟩
  intro L J N A B T Q V P hN hNT hT hlog hsep ha hb hP hp0 hp1 hleft hright hPs hQ hheight
  have hL : 0 < Real.log T := Real.log_pos hT
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL.ne')
  have hEq : (∫ t : ℝ, PRZZMellinSeparation.scaledCutoff F T t *
      masked L J N (fun x => (P x:ℂ)) (PRZZMellinSeparation.scaledCutoff G Q)
        (PRZZMellinSeparation.scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun j z => ¬ |(z.2.1:ℝ)| < PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) =
      ∫ t : ℝ, PRZZMellinSeparation.scaledCutoff F T t *
        PRZZWRowLimit.complement L N (fun x => (P x:ℂ))
          (fun j z => |(z.2.1:ℝ)| < PRZZSourceCutoffs.deltaCutoff T (2^j) Q eps/(z.1:ℝ))
          (leftCoefficient (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZMellinSeparation.scaledCutoff G Q))
          (rightCoefficient (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZMellinSeparation.scaledCutoff H V))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    by_cases hz : PRZZMellinSeparation.scaledCutoff F T t = 0
    · simp only [hz,zero_mul]
    · have hh := hsF hz
      have ht : 0 < t := by
        by_contra hn
        have hz' : T⁻¹*t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
          (by positivity) (le_of_not_gt hn)
        linarith [hh.1]
      rw [complement_original L J N _ _ _ hPs
        (by intro y hy; simp [hleft y hy]) (by intro y hy; simp [hright y hy]) _ _ _ _ hs t ht]
  rw [hEq]
  exact h L N A B T Q V P hN hNT hT hlog hsep ha hb hP hp0 hp1 hleft hright hQ hheight

#print axioms exhaustive
#print axioms masked_original
#print axioms complement_original
#print axioms source_complement_bound
end XiPrime8845.PRZZResolvedComplement

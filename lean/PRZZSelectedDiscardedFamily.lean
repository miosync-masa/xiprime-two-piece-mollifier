import PRZZSelectedDiscarded
import PRZZSmallCentralLiteral

/-! Exact selected spatial source masks on the original AFE indices.
The mask is combined before applying the direct and dual IBP bounds. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set MeasureTheory Filter
namespace XiPrime8845.PRZZSelectedDiscardedFamily
open PRZZAFEIndices PRZZWRowReindex PRZZWRowLimit PRZZMellinSeparation PRZZDiscardedAFEBridge PRZZDiscardedOuter
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

def region (R : ℕ → Prop) (T Q eps : ℝ) (s : ℕ) (z : Label) : Prop :=
  R s ∧ PRZZSourceMaskFamily.discarded T Q eps s z

theorem mask_values (L : ℕ) (P : ℝ → ℝ) (R : ℕ → Prop) (G H : ℝ → ℂ)
    (T Q eps : ℝ) (i : Index) (hm : 0 < i.1.1) (hk : 0 < i.1.2) :
    (G i.2.1*H i.2.2)*PRZZSelectedDiscarded.sourceMask P R G (L+2)
      T 1 Q 1 eps i.2.1 i.2.2 (i.1.1-1,i.1.2-1) =
    ∑ s ∈ range (L+2), if region R T Q eps s (label i) then
      PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
        (G i.2.1*H i.2.2) else 0 := by
  have hm' : i.1.1-1+1 = i.1.1 := by omega
  have hk' : i.1.2-1+1 = i.1.2 := by omega
  have hmR : ((i.1.1-1:ℕ):ℝ)+1 = (i.1.1:ℝ) := by exact_mod_cast hm'
  have hkR : ((i.1.2-1:ℕ):ℝ)+1 = (i.1.2:ℝ) := by exact_mod_cast hk'
  by_cases hg : G i.2.1 = 0
  · simp [PRZZSelectedDiscarded.sourceMask,hg]
  · simp only [PRZZSelectedDiscarded.sourceMask,one_mul,if_neg hg,
      PRZZDiscardedPartition.mask,hmR,hkR,mul_one,div_one,Finset.mul_sum]
    apply sum_congr rfl; intro s hs
    rw [PRZZSourceMaskFamily.raw_gap]
    simp only [region,PRZZSourceMaskFamily.discarded]
    split_ifs <;> simp_all [mul_comm,mul_assoc] <;> linarith

/-- Exact same original finite four-index sum, not an enlarged grid. -/
def masked (L N : ℕ) (P : ℝ → ℝ) (R : ℕ → Prop) (G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ indices L N,
    ((G i.2.1*H i.2.2)*PRZZSelectedDiscarded.sourceMask P R G (L+2)
      T 1 Q 1 eps i.2.1 i.2.2 (i.1.1-1,i.1.2-1))*
      PRZZL1Finite.term a a alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
        t i.1.1 i.1.2 i.2.1 i.2.2

theorem masked_selected (L N : ℕ) (P : ℝ → ℝ) (R : ℕ → Prop) (G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (hT : 0 < T) (hQ : 0 < Q) (alpha beta : ℂ) (t : ℝ) :
    masked L N P R G H a T Q eps alpha beta t =
      PRZZAllOffDiagonalRows.selected L N (fun x => (P x:ℂ)) G H a
        (region R T Q eps) alpha beta t := by
  have hcut (s : ℕ) : 0 < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hm : masked L N P R G H a T Q eps alpha beta t =
      ∑ s ∈ range (L+2), ∑ i ∈ indices L N,
        if region R T Q eps s (label i) then
          PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
            PRZZL1Finite.term (leftCoefficient a G) (rightCoefficient a H)
              alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
                t i.1.1 i.1.2 i.2.1 i.2.2 else 0 := by
    unfold masked
    rw [sum_comm]
    apply sum_congr rfl; intro i hi
    obtain ⟨hmk,hnr⟩ := mem_product.mp hi
    obtain ⟨hmi,hki⟩ := mem_product.mp hmk
    rw [mask_values L P R G H T Q eps i (mem_Icc.mp hmi).1 (mem_Icc.mp hki).1,sum_mul]
    apply sum_congr rfl; intro s hs
    rw [term_cutoffs]
    split_ifs <;> ring
  rw [hm]
  unfold PRZZAllOffDiagonalRows.selected
  apply sum_congr rfl; intro s hs
  rw [grouped]
  apply sum_congr rfl; intro z hz
  have he : (∑ i ∈ fibre L N z,
      PRZZAFEProgression.piece (fun x => (P x:ℂ)) ((2:ℝ)^s) i.1.1*
        PRZZL1Finite.term (leftCoefficient a G) (rightCoefficient a H)
          alpha beta (PRZZActualDirectSum.mainWeight alpha beta)
            t i.1.1 i.1.2 i.2.1 i.2.2) =
      literalRows L N (fun x => (P x:ℂ)) s z a G H alpha beta t := by
    rw [PRZZExplicitDomain.fibre_explicit]
    exact row_reindex L N s z _ G H a alpha beta t
  by_cases hd : region R T Q eps s z
  · have hne : z.2.1 ≠ 0 := by
      intro hzero
      have hh := hd.2
      simp only [PRZZSourceMaskFamily.discarded,hzero,Int.cast_zero,abs_zero,mul_zero] at hh
      linarith [hcut s]
    simp only [if_pos (And.intro hne hd)]
    rw [← he]
    apply sum_congr rfl; intro i hi
    rw [(mem_filter.mp hi).2,if_pos hd]
  · simp only [show ¬(z.2.1 ≠ 0 ∧ region R T Q eps s z) from fun h => hd h.2,if_false]
    apply sum_eq_zero; intro i hi
    rw [(mem_filter.mp hi).2,if_neg hd]

theorem masked_family (L J N : ℕ) (P : ℝ → ℝ) (R : ℕ → Prop) (G H : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0)
    (a : ℕ → ℂ) (T Q eps : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) (t : ℝ) (ht : 0 < t) :
    masked L N P R G H a T Q eps alpha beta t =
      PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ)) G H a
        (region R T Q eps) alpha beta t := by
  rw [masked_selected L N P R G H a T Q eps hT hQ]
  exact PRZZSourceMaskFamily.selected_resolved L J N _ G H hP
    (by intro y hy; simp [hlo y hy]) (by intro y hy; simp [hhi y hy])
    a _ alpha beta hab t ht

def selected (P : ℝ → ℝ) (R : ℕ → Prop) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
    (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (region R T Q eps) alpha beta t

theorem direct_family (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (L J N : ℕ)
    (hsF : Function.support F ⊆ Set.Icc (1:ℝ) 2)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (hQ : 0 < Q) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    tailError F js N T alpha beta (alpha+beta)
      (fun _ _ => range L ×ˢ range L)
      (fun u v p => (scaledCutoff G Q u*scaledCutoff H V v)*
        PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p) =
      ∫ t : ℝ, scaledCutoff F T t*selected P R G H js L J N T Q V eps alpha beta t := by
  unfold tailError
  have hp (t : ℝ) :
      (∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        row F T (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta (alpha+beta) u v
          (range L ×ˢ range L) (fun p => (scaledCutoff G Q u*scaledCutoff H V v)*
            PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p) t) =
        scaledCutoff F T t*masked L N P R (scaledCutoff G Q)
          (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T Q eps alpha beta t := by
    calc
      _ = scaledCutoff F T t*∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ p ∈ range L ×ˢ range L,
          ((scaledCutoff G Q u*scaledCutoff H V v)*
            PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps u v p)*
          PRZZL1Finite.term (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta
            (PRZZActualDirectSum.mainWeight alpha beta) t (p.1+1) (p.2+1) u v := by
        simp only [PRZZDiscardedOuter.row,mul_sum]
        apply sum_congr rfl; intro u hu
        apply sum_congr rfl; intro v hv
        apply sum_congr rfl; intro p hp
        rw [term_phase _ alpha beta _ t _ _ u v (by omega) (by omega)
          (mem_Icc.mp hu).1 (mem_Icc.mp hv).1,PRZZWRowReindex.weight_eq]
        unfold PRZZTimeAmplitude.amplitude PRZZTimeJets.reciprocal
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        ring
      _ = _ := by
        unfold masked
        congr 1
        have hh := four_sum L N (fun i =>
          ((scaledCutoff G Q i.2.1*scaledCutoff H V i.2.2)*
            PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps i.2.1 i.2.2
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
    rw [masked_family L J N P R _ _ hP hleft hright _
      T Q eps hT hQ alpha beta hs t ht]
    rfl

theorem integrand_original (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ)
    (K n r : ℕ) (T M Q V eps : ℝ) (alpha beta : ℂ) (s : Finset (ℕ × ℕ)) (t : ℝ)
    (hn : 0 < n) (hr : 0 < r) :
    PRZZSelectedDiscarded.integrand F G H P R js K n r T M Q V 1 eps alpha beta s t =
      (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        ∑ p ∈ s, ((scaledCutoff G Q n*scaledCutoff H V r)*
          PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) K T M Q 1 eps n r p)*
            PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
              (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
              (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t (p.1+1) (p.2+1) n r := by
  unfold PRZZSelectedDiscarded.integrand
  rw [mul_sum]
  apply sum_congr rfl; intro p hp
  rw [term_phase _ (-beta) (-alpha) _ t (p.1+1) (p.2+1) n r (by omega) (by omega) hn hr,
    PRZZWRowReindex.weight_eq]
  unfold PRZZSelectedDiscarded.coefficient PRZZDualTimeIBP.weight
    PRZZTimeAmplitude.amplitude PRZZTimeJets.reciprocal
  simp only [Nat.cast_add,Nat.cast_one,one_mul,Nat.cast_mul]
  rw [show -beta+-alpha = -(alpha+beta) by ring]
  ring

/-- Pointwise identification of the *previous* IBP integrand, including
its true dual Gamma factor and time cutoff, with the original masked
AFE sum. The two sharp AFE cutoffs are unchanged. -/
theorem outer_integrand (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (L N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    (∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N,
      PRZZSelectedDiscarded.integrand F G H P R js (L+2) n r
        T 1 Q V 1 eps alpha beta (range L ×ˢ range L) t) =
      (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        masked L N P R (scaledCutoff G Q) (scaledCutoff H V)
          (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) T Q eps (-beta) (-alpha) t := by
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (r : ℕ) (hr : r ∈ Finset.Icc 1 N) :=
    integrand_original F G H P R js (L+2) n r T 1 Q V eps alpha beta
      (range L ×ˢ range L) t (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hr).1
  calc
    _ = (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        ∑ n ∈ Icc 1 N, ∑ r ∈ Icc 1 N, ∑ p ∈ range L ×ˢ range L,
          ((scaledCutoff G Q n*scaledCutoff H V r)*
            PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps n r p)*
              PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
                (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
                (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t (p.1+1) (p.2+1) n r := by
      simp only [mul_sum]
      apply sum_congr rfl; intro n hn
      apply sum_congr rfl; intro r hr
      simpa only [mul_sum] using he n hn r hr
    _ = _ := by
      unfold masked
      congr 1
      have h := four_sum L N (fun i =>
        ((scaledCutoff G Q i.2.1*scaledCutoff H V i.2.2)*
          PRZZSelectedDiscarded.sourceMask P R (scaledCutoff G Q) (L+2) T 1 Q 1 eps
            i.2.1 i.2.2 (i.1.1-1,i.1.2-1))*
          PRZZL1Finite.term (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
            (fun u => (PRZZGCoefficient.coefficient js u:ℂ)) (-beta) (-alpha)
            (PRZZActualDirectSum.mainWeight (-beta) (-alpha)) t i.1.1 i.1.2 i.2.1 i.2.2)
      simpa only [Nat.add_sub_cancel,Prod.mk.eta] using h

/-- The already estimated IBP family is now exactly the matching part
of the original resolved family, under the full real time integral. The
support of the fixed time cutoff supplies positivity; no Fubini or
reconstruction equality is assumed. -/
theorem outer_family (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (L J N : ℕ)
    (hF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hlo : ∀ y ≤ (1/2:ℝ), P y = 1) (hhi : ∀ y, 1 ≤ y → P y = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (alpha beta : ℂ) (hab : alpha+beta ≠ 0) :
    PRZZSelectedDiscarded.outerValue F G H P R js N (L+2) T 1 Q V 1 eps alpha beta
      (fun _ _ => range L ×ˢ range L) =
      ∫ t : ℝ, (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        PRZZSourceMaskFamily.selectedFamily L J N (fun x => (P x:ℂ))
          (scaledCutoff G Q) (scaledCutoff H V)
          (fun u => (PRZZGCoefficient.coefficient js u:ℂ))
          (region R T Q eps) (-beta) (-alpha) t := by
  unfold PRZZSelectedDiscarded.outerValue
  apply integral_congr_ae
  apply Filter.Eventually.of_forall; intro t
  dsimp only
  rw [outer_integrand]
  by_cases hf : scaledCutoff F T t = 0
  · simp only [hf,zero_mul]
  · have hx : F (T⁻¹*t) ≠ 0 := hf
    have hp := (hF hx).1
    have ht : 0 < t := by
      have he : T*(T⁻¹*t) = t := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hp hT.le]
    rw [masked_family L J N P R _ _ hP hlo hhi _ T Q eps hT hQ
      (-beta) (-alpha) (by simpa only [show -beta+-alpha = -(alpha+beta) by ring] using neg_ne_zero.mpr hab)
      t ht]


def pair (F G H : ℝ → ℂ) (P : ℝ → ℝ) (R : ℕ → Prop) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Icc T (2*T), scaledCutoff F T t*selected P R G H js L J N T Q V eps alpha beta t)+
    ∫ t in Icc T (2*T), (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
      selected P R G H js L J N T Q V eps (-beta) (-alpha) t

theorem pair_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (Q V : ℝ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ (fun x => (P x:ℂ)) → Antitone P →
      (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖pair F G H P R js L J N T Q V eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^(-power) := by
  obtain ⟨Cd,hCd,hd⟩ := PRZZSelectedDiscarded.direct_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps power hr he he1
  obtain ⟨Ce,hCe,hh⟩ := PRZZSelectedDiscarded.dual_negligible F G H hF hcF hsF
    hG hH hcG hcH hsG js S r eps power hS hr he he1
  refine ⟨Cd+Ce,by positivity,?_⟩
  filter_upwards [hd,hh,eventually_gt_atTop (1:ℝ)] with T hd hh hT
  intro L J N Q V A B P R hN hNT hQ hA hB hsep hP hm hlo hhi hleft hright
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  have h1 := hd N (L+2) 1 Q V 1 A B P R (fun _ _ => range L ×ˢ range L)
    hN hNT (by norm_num) hQ (by norm_num) hA hB hsep hm hlo hhi hleft hright
  have heq : PRZZSelectedDiscarded.directError F G H P R js N (L+2) T 1 Q V 1 eps A B
      (fun _ _ => range L ×ˢ range L) =
      ∫ t in Icc T (2*T), scaledCutoff F T t*
        selected P R G H js L J N T Q V eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t := by
    unfold PRZZSelectedDiscarded.directError
    simp only [one_mul]
    rw [add_div,direct_family F G H P R js L J N hsF hP hleft hright T Q V eps
      (by linarith) hQ _ _ hs,PRZZDiscardedTimePair.time_window F hsF T (by linarith)]
  rw [heq] at h1
  have h2 := hh N (L+2) 1 Q V 1 A B P R (fun _ _ => range L ×ˢ range L)
    hN hNT (by norm_num) hQ (by norm_num) hA hB hsep hm hlo hhi hleft hright
  rw [outer_family F G H P R js L J N hsF hP hleft hright T Q V eps
    (by linarith) hQ _ _ hs] at h2
  change ‖∫ t : ℝ, (scaledCutoff F T t*PRZZAFEDual.dualMultiplier _ _ t)*
    selected P R G H js L J N T Q V eps _ _ t‖ ≤ _ at h2
  simp_rw [mul_assoc] at h2
  rw [PRZZDiscardedTimePair.time_window F hsF T (by linarith)] at h2
  simp_rw [← mul_assoc] at h2
  unfold pair
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- Entire arithmetic profile grid; the spatial selector may depend on
height and is chosen AFTER the uniform constant. -/
theorem partition_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (P : ℝ → ℝ) (R : ℕ → Prop),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ContDiff ℝ ∞ (fun x => (P x:ℂ)) → Antitone P →
      (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ‖pair F G H P R js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖) ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := pair_negligible F G H hF hcF hsF hG hH hcG hcH hsG
    js S r eps (power+1) hS hr he he1
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  refine ⟨D*C,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro L J N A B P R hN hNT hA hB hsep hP hm hlo hhi hleft hright
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), C*T^(-(power+1)) := by
      apply sum_le_sum; intro p hp
      exact h L J N _ _ A B P R hN hNT (by positivity) hA hB hsep hP hm hlo hhi hleft hright
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*(C*T^(-(power+1))) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*(C*T^(-(power+1))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using hgrid N hN T hNT hlog
    _ = _ := by
      rw [show (D*T)*(C*T^(-(power+1))) = (D*C)*(T^(1:ℝ)*T^(-(power+1))) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT,show (1:ℝ)+-(power+1) = -power by ring]

theorem discarded_pair_time (Phi : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (K L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (hPhi : Continuous Phi) :
    (∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZReconstructedAFE.discarded
      (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) K L J N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta t)+
    (∫ t in Icc T (2*T), (scaledCutoff Phi T t*PRZZAFEDual.dualMultiplier alpha beta t)*
      PRZZReconstructedAFE.discarded (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) K L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (-beta) (-alpha) t) =
    ∑ p ∈ range K ×ˢ range K, pair Phi (profile (fun x => (P x:ℂ))) (profile (fun x => (P x:ℂ)))
      P (fun s => (2:ℝ)^s < T^(4:ℝ)) js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta := by
  have ht (alpha beta : ℂ) (hab : alpha+beta ≠ 0) (phi : ℝ → ℂ)
      (hp : ContinuousOn phi (Icc T (2*T))) :
      (∫ t in Icc T (2*T), phi t*PRZZReconstructedAFE.discarded
        (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) K L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta t) =
      ∑ p ∈ range K ×ˢ range K, ∫ t in Icc T (2*T), phi t*selected P
        (fun s => (2:ℝ)^s < T^(4:ℝ)) (profile (fun x => (P x:ℂ))) (profile (fun x => (P x:ℂ)))
        js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta t := by
    unfold PRZZReconstructedAFE.discarded
    simp only [mul_sum]
    apply integral_finsetSum
    intro p hp'
    exact (hp.mul (PRZZPrunedAFEError.selected_continuous L J N _ _ _ hP
      (by intro x hx; simp [hl x hx]) (by intro x hx; simp [hr x hx]) _ _ alpha beta hab T hT)).integrableOn_compact isCompact_Icc
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hphi : Continuous (scaledCutoff Phi T) := hPhi.comp (continuous_const.mul continuous_id)
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  rw [ht alpha beta hs (scaledCutoff Phi T) hphi.continuousOn,
    ht (-beta) (-alpha) hs' (fun t => scaledCutoff Phi T t*PRZZAFEDual.dualMultiplier alpha beta t)
      (hphi.mul hg).continuousOn]
  simp only [pair,sum_add_distrib]

theorem discarded_absorbed (Phi : ℝ → ℂ) (P : ℝ → ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (js : List ℕ) (S r eps power : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (A B : ℂ), 1 ≤ N → (N:ℝ) ≤ T →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖(∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZReconstructedAFE.discarded
        (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) (Nat.log 2 N+2) L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)+
      (∫ t in Icc T (2*T), (scaledCutoff Phi T t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)*
        PRZZReconstructedAFE.discarded (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) (Nat.log 2 N+2) L J N
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t)‖ ≤ C*T^(-power) := by
  have hp := profile_regular _ hP (by intro x hx; simp [hl x hx]) (by intro x hx; simp [hright x hx])
  obtain ⟨C,hC,h⟩ := partition_negligible Phi _ _ hPhi hcPhi hsPhi hp.1.continuous hp.1.continuous
    hp.2.1 hp.2.1 hp.2.2 js S r eps power hS hr he he1
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with T h hsmall hT
  intro L J N A B hN hNT hA hB hsep
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos hT).ne')
  rw [discarded_pair_time Phi P js _ L J N hP hl hright T eps (by linarith)
    _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs hPhi.continuous]
  exact (norm_sum_le _ _).trans (h L J N A B P _ hN hNT hA hB hsep hP hm hlo hhi hl hright)

#print axioms partition_negligible
#print axioms discarded_pair_time
#print axioms discarded_absorbed
#print axioms pair_negligible
#print axioms mask_values
#print axioms masked_selected
#print axioms masked_family
#print axioms direct_family
#print axioms integrand_original
#print axioms outer_integrand
#print axioms outer_family
end XiPrime8845.PRZZSelectedDiscardedFamily


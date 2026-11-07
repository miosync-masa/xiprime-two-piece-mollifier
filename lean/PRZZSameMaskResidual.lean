import PRZZSpatialReconstruction

/-! Suppliers on the SAME strict-small, strict-source mask used by the
reconstructed family. No cancellation of absolute masses is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZSameMaskResidual
open PRZZMellinSeparation PRZZRetainedNative PRZZSelectedLocalFourier
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def keep (T Q eps : ℝ) (s : ℕ) (z : PRZZAFEIndices.Label) : Prop :=
  (2:ℝ)^s < T^(4:ℝ) ∧ ¬PRZZSourceMaskFamily.discarded T Q eps s z

theorem boundary_zero (L J N : ℕ) (P G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps t : ℝ) (alpha beta : ℂ) (hN : 1 ≤ N)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0) (hL : 4*(N:ℝ)*T^(4:ℝ) ≤ L) :
    selectedPart .boundary L J N P G H a (keep T Q eps) alpha beta t = 0 := by
  rw [selected_reindex]
  apply sum_eq_zero; intro s hs
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  split_ifs with had
  · apply sum_eq_zero; intro delta hdel
    split_ifs with hkeep
    · unfold PRZZNativeComponents.row
      dsimp only
      split_ifs with hsmall
      · have hz := PRZZResolvedBoundary.bounded_cover_zero L N (T^(4:ℝ)) ((2:ℝ)^s) t
          (PRZZWRowLimit.profile P) ((u,v),(-delta,1)) alpha beta (alpha+beta)
          (by exact_mod_cast hN) (by positivity) hkeep.2.1.le
          (mem_Icc.mp hu).1 (mem_Icc.mp hu).2 (mem_Icc.mp hv).1
          (PRZZWRowLimit.profile_regular P hP hl hr).2.2 hsmall hL
        simp only [hz,mul_zero]
      · rfl
    · rfl
  · rfl

theorem outside_zero (L J N : ℕ) (P G H : ℝ → ℂ) (a : ℕ → ℂ)
    (Q T eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    selectedPart .outside L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t = 0 := by
  rw [selected_reindex]
  apply sum_eq_zero; intro s hs
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply sum_eq_zero; intro delta hdel
    by_cases hk : delta ≠ 0 ∧ keep T Q eps s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · rw [if_pos hk]
      by_cases hg : scaledCutoff G Q ((d:ℝ)*u) = 0
      · simp [PRZZNativeComponents.row,PRZZUnfrozenPoisson.afeRow,hg]
      · have hgcd : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
        have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
        have hf : |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
          rw [lt_div_iff₀ hd0]
          have hh := hk.2.2
          simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hgcd,not_le] at hh
          simpa only [mul_comm] using hh
        have hh := PRZZRejectedExhaustion.source_small_gap G Q T ((2:ℝ)^s) eps d u delta
          hQ hT (by positivity) (mem_Icc.mp hd).1 hsG hg hheight hf
        simp only [PRZZNativeComponents.row,Int.cast_neg,abs_neg,if_pos hh]
    · simp only [if_neg hk]
  · simp only [if_neg had]

def bandField (P F G : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) : ℂ :=
  PRZZResolvedTailMass.branch dual A B T t *
    (selectedPart .central L J N P (scaledCutoff F Q) (scaledCutoff G V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (keep T Q eD)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
    localPart .central L N (sourceCutoff T eH) P (scaledCutoff F Q) (scaledCutoff G V)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (keep T Q eD)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)

/-- Identify the signed selected band with its original native rows before
taking any norm. This is the common-minus-local sign. -/
theorem band_reindex (P F G : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) :
    bandField P F G js L N J dual T Q V eD eH t A B =
      ∑ s ∈ range (L+2), ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
            if delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
              PRZZResolvedTailMass.branch dual A B T t *
                (if |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 then
                  PRZZResolvedTailMass.coeff F G js d Q V T A B ((u,v),(-delta,1))*
                    PRZZBandOuterMass.band (PRZZWRowLimit.profile P) ((2:ℝ)^s) T eH t A B J
                      ((u,v),(-delta,1)) else 0) else 0 else 0 := by
  unfold bandField
  rw [selected_reindex]
  simp only [localPart,← sum_sub_distrib,ite_sub_ite,sub_self,mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro u hu
  apply sum_congr rfl; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply sum_congr rfl; intro delta hdel
    by_cases hk : delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · simp only [if_pos hk,sourceCutoff]
      rw [PRZZBandOuterMass.central_row_difference]
      simp only [mul_ite,mul_zero]
    · simp only [if_neg hk]
  · simp only [if_neg had]

theorem band_dominated (P F G : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V eD eH t : ℝ) (A B : ℂ) (hT : 1 ≤ T) (hQ : 0 ≤ Q) (hQT : Q ≤ 2*T) :
    ‖bandField P F G js L N J dual T Q V eD eH t A B‖ ≤
      PRZZBandOuterMass.mass F G (PRZZWRowLimit.profile P) js L N J dual T Q V 4 eD eH t A B := by
  rw [band_reindex,← PRZZBandOuterMass.native_mass F G (PRZZWRowLimit.profile P) js L N J dual
    T Q V 4 eD eH t A B hT hQ hQT]
  unfold PRZZWindowGrids.spatial
  rw [sum_filter]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  by_cases hsmallM : (2:ℝ)^s < T^(4:ℝ)
  · rw [if_pos hsmallM.le]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro d hd
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro u hu
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro v hv
    by_cases had : PRZZDiagonalAssembly.admissible N d u v
    · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
      simp only [if_pos had,if_pos had']
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro delta hdel
      by_cases hk : delta ≠ 0 ∧ keep T Q eD s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
      · rw [if_pos hk]
        have hgcd : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
        have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
        have hf : |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d := by
          rw [le_div_iff₀ hd0]
          have hh := hk.2.2
          simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hgcd,not_le] at hh
          simpa only [Int.cast_neg,abs_neg,mul_comm] using hh.le
        by_cases hg : |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4
        · have hcond : delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
              |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
            ⟨hk.1,hg,hf⟩
          rw [if_pos hg,if_pos hcond]
          exact le_of_eq (by congr 1; ring)
        · rw [if_neg hg]
          simp only [mul_zero,norm_zero]
          split_ifs <;> positivity
      · simp only [if_neg hk,norm_zero]
        split_ifs <;> positivity
    · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
      simp only [if_neg had,if_neg had',norm_zero,le_refl]
  · simp only [keep,hsmallM,false_and,and_false,if_false,ite_self,sum_const_zero,norm_zero]
    split_ifs <;> positivity

/-- Remove boundary and outside on precisely the same mask. No enlarged
source set or silently dropped arithmetic-cutoff complement is used. -/
theorem reduced_residual (L J N : ℕ) (P G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps eH t : ℝ) (alpha beta : ℂ) (hN : 1 ≤ N)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0) (hT : 0 < T) (ht : 0 < t) (hQ : 0 < Q)
    (hs : alpha+beta ≠ 0) (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hheight : 8 ≤ T^(1-eps)) (hL : 4*(N:ℝ)*T^(4:ℝ) ≤ L) :
    PRZZResolvedComplement.masked L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t-
      selectedPart .central L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t-
      selectedPart .freeze L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t =
      localPart .tail L N (sourceCutoff T eH) P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t+
      (localPart .central L N (sourceCutoff T eH) P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t-
        selectedPart .central L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t) := by
  have he := PRZZSpatialReconstruction.small_residual L J N P (scaledCutoff G Q) H a
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) T eH alpha beta t hP hl hr ht hs
  dsimp only at he
  change _ = _-selectedPart .boundary L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t+
    selectedPart .outside L J N P (scaledCutoff G Q) H a (keep T Q eps) alpha beta t at he
  rw [boundary_zero L J N P _ H a T Q eps t alpha beta hN hP hl hr hL,
    outside_zero L J N P G H a Q T eps alpha beta t hQ hT hsG hheight,sub_zero,add_zero] at he
  exact he

/-- The strict-small freezing subfamily is charged to the existing native
absolute mass. Subset selection is performed BEFORE taking the norm. -/
theorem freeze_charge (L J N : ℕ) (P G H phi : ℝ → ℂ) (js : List ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Set.Icc T (2*T))) :
    ‖∫ t in Set.Icc T (2*T), phi t*selectedPart .freeze L J N P
      (scaledCutoff G Q) (scaledCutoff H V) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (keep T Q eps) alpha beta t‖ ≤
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile P) G H phi js
        T 1 Q V eps alpha beta := by
  rw [PRZZNativeFreezeTime.selected_time L J N P _ _ phi _ _ alpha beta T hT hs hphi]
  unfold PRZZNativeFreezeTime.rows PRZZNativeFreezeEnvelope.charge
  rw [sum_comm (s := Icc 1 N)]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hss
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro delta hdel
    have hg : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
    have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have he : (¬PRZZSourceMaskFamily.discarded T Q eps s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)) ↔
        |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
      simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le]
      rw [lt_div_iff₀ hd0]
      simp only [mul_comm]
    have hn : delta ≠ 0 ↔ 0 < |(delta:ℝ)| := by
      rw [abs_pos]; exact_mod_cast Iff.rfl
    simp only [keep,he,hn,mul_one]
    split_ifs <;> simp_all
  · simp [had]

/-- Actual arithmetic partition scales automatically satisfy the upper
scale condition needed by native_mass when N<=T. -/
theorem grid_scale (N j : ℕ) (hN : 1 ≤ N) (hj : j ∈ range (Nat.log 2 N+2)) :
    (2:ℝ)^j ≤ 2*(N:ℝ) := by
  have hj' : j ≤ Nat.log 2 N+1 := by have := mem_range.mp hj; omega
  have hpow : (2:ℝ)^j ≤ (2:ℝ)^(Nat.log 2 N+1) := pow_le_pow_right₀ (by norm_num) hj'
  have hlog : (2:ℝ)^Nat.log 2 N ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  rw [pow_succ] at hpow
  nlinarith

open Set

/-- The norm of the SIGNED strict-small band, not merely its envelope,
is now summed over every arithmetic window and integrated in time. -/
theorem band_grid_time (P F G : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hF : Continuous F) (hG : Continuous G) (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a S r eD eH power : ℝ)
    (ha : 0 < a) (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L N J : ℕ) (dual : Bool) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Icc T (2*T), ‖phi t*bandField P F G js L N J dual T
          ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B‖) ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  have hp := PRZZWRowLimit.profile_regular P hP hl hright
  obtain ⟨C,hC,h⟩ := PRZZBandOuterMass.absorbed F G (PRZZWRowLimit.profile P)
    hF hG hcF hcG hp.1 hp.2.2 js a 4 S r eD eH (power+1)
    ha (by norm_num) hS hr heD he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  refine ⟨D*C,by positivity,?_⟩
  filter_upwards [h,Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro L N J dual A B phi hN hNT hA hB hsep hphi hJ
  have hT0 : 0 < T := by linarith
  have hh (p : ℕ × ℕ) (hp' : p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)) :
      (∫ t in Icc T (2*T), ‖phi t*bandField P F G js L N J dual T
        ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B‖) ≤
        C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖) := by
    have hQ : (2:ℝ)^p.1 ≤ 2*T := (grid_scale N p.1 hN (mem_product.mp hp').1).trans (by linarith)
    have hi : IntegrableOn (fun t : ℝ => C*T^(-(power+1))*‖phi t‖) (Icc T (2*T)) :=
      (continuous_const.mul hphi.norm).integrableOn_Icc
    apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi ?_).trans_eq
    · rw [integral_const_mul]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul]
      have hb := (band_dominated P F G js L N J dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eD eH t A B
        hT (by positivity) hQ).trans
        (h L N J dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B hN hNT (by positivity) hQ ht hA hB hsep
          (PRZZWindowTailTime.scaled_support F _ (by positivity) hsF) hJ)
      exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖) := sum_le_sum hh
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*
        (C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*(C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using hgrid N hN T hNT hlog
    _ = _ := by
      rw [show (D*T)*(C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) =
        (D*C)*(T^(1:ℝ)*T^(-(power+1)))*(∫ t in Icc T (2*T), ‖phi t‖) by rw [Real.rpow_one]; ring]
      rw [← Real.rpow_add hT0,show (1:ℝ)+-(power+1) = -power by ring]

#print axioms grid_scale
#print axioms band_grid_time
#print axioms reduced_residual
#print axioms freeze_charge
#print axioms boundary_zero
#print axioms outside_zero
#print axioms band_reindex
#print axioms band_dominated
end XiPrime8845.PRZZSameMaskResidual

import PRZZCappedFreezeBudget
import PRZZSameMaskResidual

/-! Strict native freezing selection with arbitrary capped coefficients.
The original signed gap and strict source mask are retained before norms. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex Set Filter
namespace XiPrime8845.PRZZCappedStrictFreeze
open PRZZNativeFreezeEnvelope PRZZPrefactorMass PRZZActiveFreezeBudget
open PRZZMellinSeparation PRZZRetainedNative PRZZSelectedLocalFourier PRZZSameMaskResidual
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def charge (L J N K : ℕ) (F G H phi : ℝ → ℂ) (c : ℕ → ℂ)
    (T M Q V eps : ℝ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ s ∈ range K, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if 0 < |(delta:ℝ)| ∧ |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s*M) Q eps/d then
          ‖∫ t in Set.Icc T (2*T), phi t*PRZZNativeComponents.row .freeze L J F
            (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V)
            ((2:ℝ)^s*M) ((u,v),(-delta,1)) alpha beta
            c d t‖ else 0 else 0

theorem dominates (L J N K : ℕ) (F G H phi : ℝ → ℂ) (c : ℕ → ℂ)
    (T M Q V eps eH : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q)
    (hs : alpha+beta ≠ 0) (hheight : 8 ≤ T^(1-eps)) :
    charge L J N K F G H phi c T M Q V eps alpha beta ≤
      PRZZCappedFreezeBudget.fullMass L J F phi c N K T M Q V eps eH G H alpha beta (alpha+beta) := by
  unfold charge PRZZCappedFreezeBudget.fullMass
  apply sum_le_sum; intro d hd
  have rotate (s t u : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) = ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, f i j k := by
    calc
      _ = ∑ i ∈ s, ∑ k ∈ u, ∑ j ∈ t, f i j k := by
        apply sum_congr rfl; intro i hi; rw [sum_comm]
      _ = _ := sum_comm
  let g := fun j l k => ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
      (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V),
      ‖PRZZActualPoissonError.rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta (alpha+beta)
        c d
        (PRZZMellinSeparation.scaledCutoff G Q) (PRZZMellinSeparation.scaledCutoff H V) phi‖
  change _ ≤ ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1), ∑ k ∈ range K, g j l k
  apply le_trans _ (le_of_eq (rotate (range (Nat.log 2 N+1)) (range (Nat.log 2 N+1)) (range K) g).symm)
  apply sum_le_sum; intro s hss
  let F1 := PRZZMellinSeparation.scaledCutoff G Q
  let F2 := PRZZMellinSeparation.scaledCutoff H V
  let a := c
  let D := PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s*M) Q eps
  let f := fun z => ‖∫ t in Set.Icc T (2*T), phi t*PRZZNativeComponents.row .freeze L J F F1 F2
    ((2:ℝ)^s*M) z alpha beta a d t‖
  rw [native_rectangle L N d D f]
  have he : (∑ z ∈ (PRZZAStar.indices N d D 2).filter
      (fun z => F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0), f z) =
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        ∑ z ∈ active N d j l D 2 F1 F2,
          ‖PRZZActualPoissonError.rowIntegral L J F ((2:ℝ)^s*M) T z alpha beta (alpha+beta) a d F1 F2 phi‖ := by
    rw [← active_grid N d D F1 F2 f]
    apply sum_congr rfl; intro j hj
    apply sum_congr rfl; intro l hl
    apply sum_congr rfl; intro z hz
    exact congrArg norm (PRZZCappedFreezeBudget.active_freeze_identity L J N d j l F hF hsF T
      ((2:ℝ)^s*M) Q eps z alpha beta a F1 F2 phi (mem_Icc.mp hd).1 hT (by positivity) hs
      (PRZZWindowTailTime.scaled_support G Q hQ hsG) hheight hz).symm
  apply le_trans _ he.le
  rw [sum_filter]
  apply sum_le_sum; intro z hz
  by_cases hc : F1 ((d:ℝ)*z.1.1) ≠ 0 ∧ F2 ((d:ℝ)*z.1.2) ≠ 0
  · rw [if_pos hc]
    split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  · have hz0 : F1 ((d:ℝ)*z.1.1) = 0 ∨ F2 ((d:ℝ)*z.1.2) = 0 := by tauto
    have hf : f z = 0 := by
      dsimp [f]
      rw [freeze_zero L J d F F1 F2 phi a T ((2:ℝ)^s*M) alpha beta z hz0,norm_zero]
    simp only [if_neg hc]
    change (if -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) then f z else 0) ≤ 0
    simp only [hf,ite_self,le_refl]

theorem freeze_charge (L J N : ℕ) (P G H phi : ℝ → ℂ) (c : ℕ → ℂ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Set.Icc T (2*T))) :
    ‖∫ t in Set.Icc T (2*T), phi t*selectedPart .freeze L J N P
      (scaledCutoff G Q) (scaledCutoff H V) c
      (keep T Q eps) alpha beta t‖ ≤
      charge L J N (L+2) (PRZZWRowLimit.profile P) G H phi c
        T 1 Q V eps alpha beta := by
  rw [PRZZNativeFreezeTime.selected_time L J N P _ _ phi _ _ alpha beta T hT hs hphi]
  unfold PRZZNativeFreezeTime.rows charge
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


theorem scaled_bound
    (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (L J N : ℕ) (T Q V eH : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (Pcap : ℝ),
      Continuous phi → 0 ≤ Pcap → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ Pcap) →
      ‖∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N P
        (scaledCutoff G1 Q) (scaledCutoff G2 V) c (keep T Q eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
          C*Pcap*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨hw,hcw,hsw⟩ := PRZZWRowLimit.profile_regular P hP hl hright
  obtain ⟨C,hC,h⟩ := PRZZCappedFreezeBudget.scaled_bound _ hw hcw hsw
    G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2 Hcap hHcap S r eps eta delta
      hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro c L J N T Q V eH A B hc hA hB hsep hN hT hlog hleta hscale hh hQ hV phi Pcap hphi hPc hp
  have ht : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  have h1 := freeze_charge L J N P G1 G2 phi c T Q V eps _ _ ht hs hphi.continuousOn
  have h2 := dominates L J N (L+2) (PRZZWRowLimit.profile P) G1 G2 phi c
    T 1 Q V eps eH _ _ hw hsw hsG1 ht (by norm_num) hQ hs hh
  have h3 := h c L J N (L+2) T 1 Q V eH A B hc hA hB hsep hN hT hlog hleta hscale
    hh (by norm_num) hQ hV phi Pcap hphi hPc hp
  rw [← add_div] at h2
  exact h1.trans (h2.trans h3)
theorem mixed_scaled_bound
    (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d : ℕ → ℂ) (L J N : ℕ) (T Q V eH : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (Pcap : ℝ),
      Continuous phi → 0 ≤ Pcap → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ Pcap) →
      ‖PRZZMixedPoisson.lift (fun c => ∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N P
        (scaledCutoff G1 Q) (scaledCutoff G2 V) c (keep T Q eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) c d‖ ≤
          C*Pcap*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_bound P hP hl hright G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    (2*Hcap) (by positivity) S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro c d L J N T Q V eH A B hc hd hA hB hsep hN hT hlog hleta hscale hh hQ hV phi Pcap hphi hPc hp
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact h _ L J N T Q V eH A B
    (PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hd z hz)
    hA hB hsep hN hT hlog hleta hscale hh hQ hV phi Pcap hphi hPc hp

theorem partition_bound (P G1 G2 : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3)
    (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (L J N : ℕ) (T : ℝ) (A B : ℂ) (phi : ℝ → ℂ) (U : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → Continuous phi → 0 ≤ U →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ U) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ‖∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N P
          (scaledCutoff G1 ((2:ℝ)^p.1)) (scaledCutoff G2 ((2:ℝ)^p.2)) c
          (keep T ((2:ℝ)^p.1) eps) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖) ≤
        C*U*T^delta*PRZZOptimalPowers.target N T := by
  let d0 := (6*eps+2*eta+delta)/2
  have hm : 6*eps+2*eta < d0 := by dsimp [d0]; linarith
  have hg : 0 < delta-d0 := by dsimp [d0]; linarith
  obtain ⟨C,hC,h⟩ := scaled_bound P hP hleft hright G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    Hcap hHcap S r eps eta d0 hS hr heps heta heta1 hm
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed (delta-d0) hg
  refine ⟨D*C,by positivity,?_⟩
  intro c L J N T A B phi U hc hA hB hsep hN hT hlog hleta hscale hheight hphi hU hp
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        C*U*T^d0*PRZZOptimalPowers.target N T := by
      apply sum_le_sum; intro p hp'
      exact h c L J N T _ _ 0 A B hc hA hB hsep hN hT hlog hleta hscale hheight
        (by positivity) (by positivity) phi U hphi hU hp
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*
        (C*U*T^d0*PRZZOptimalPowers.target N T) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T^(delta-d0))*(C*U*T^d0*PRZZOptimalPowers.target N T) := by
      apply mul_le_mul_of_nonneg_right (hgrid N hN T hNT hlog)
      unfold PRZZOptimalPowers.target; positivity
    _ = _ := by
      rw [show delta = (delta-d0)+d0 by ring,Real.rpow_add hT0]
      ring

#print axioms partition_bound
#print axioms mixed_scaled_bound
#print axioms scaled_bound
#print axioms dominates
#print axioms freeze_charge
end XiPrime8845.PRZZCappedStrictFreeze

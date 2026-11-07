import PRZZBandOuterMass
import PRZZSpatialErrorJoin

/-! Lossless arithmetic reconstruction on the strictly small spatial region.
The complementary large region is kept as one original resolved field.
The local transfer band has its signed value, not merely an upper bound.
No estimate for the complete remainingPair is asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZSpatialReconstruction
open PRZZResolvedComplement PRZZMellinSeparation PRZZRetainedNative PRZZSelectedLocalFourier
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem masked_cover {ι : Type*} (qs : Finset ι) (G H : ι → ℝ → ℂ)
    (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ)
    (hcover : ∀ n ∈ Icc 1 N, ∀ r ∈ Icc 1 N, (∑ i ∈ qs, G i n*H i r) = 1) :
    (∑ i ∈ qs, masked L J N F (G i) (H i) a R alpha beta t) =
      masked L J N F (fun _ => 1) (fun _ => 1) a R alpha beta t := by
  unfold masked
  rw [sum_comm]
  apply sum_congr rfl; intro s hs
  rw [sum_comm]
  apply sum_congr rfl; intro z hz
  by_cases hc : z.2.1 ≠ 0 ∧ R s z
  · simp only [if_pos hc]
    rw [sum_comm]
    apply sum_congr rfl; intro n hn
    rw [sum_comm]
    apply sum_congr rfl; intro r hr
    by_cases hp : PRZZWRowReindex.pairMatches z n r
    · simp only [if_pos hp]
      conv_lhs => arg 2; ext i; rw [PRZZArithmeticCutoffPartition.resolved_values]
      have hn' : (Nat.gcd n r:ℝ)*(n/Nat.gcd n r:ℕ) = n := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
      have hr' : (Nat.gcd n r:ℝ)*(r/Nat.gcd n r:ℕ) = r := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)
      dsimp only
      rw [hn',hr',← sum_mul,hcover n hn r hr]
      simp
    · simp [hp]
  · simp [hc]

theorem masked_partition (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    (∑ p ∈ range K ×ˢ range K, masked L J N F
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a R alpha beta t) =
      masked L J N F (fun _ => 1) (fun _ => 1) a R alpha beta t := by
  apply masked_cover
  intro n hn r hr'
  exact PRZZArithmeticCutoffPartition.product_unity P K N n r hl hr hn hr' hK

theorem masked_split (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R U : ℕ → PRZZAFEIndices.Label → Prop) (alpha beta : ℂ) (t : ℝ) :
    masked L J N F G H a R alpha beta t =
      masked L J N F G H a (fun s z => R s z ∧ ¬U s z) alpha beta t+
      masked L J N F G H a (fun s z => R s z ∧ U s z) alpha beta t := by
  unfold masked
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro z hz
  by_cases hg : z.2.1 ≠ 0 <;> by_cases hr : R s z <;> by_cases hu : U s z <;> simp [hg,hr,hu]

/-- Signed residual after removing the same retained central and freezing
fields. Its cutoff-transfer term is local central minus common central. -/
theorem small_residual (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (T eH : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0) (ht : 0 < t) (hs : alpha+beta ≠ 0) :
    let U := fun s z => (2:ℝ)^s < T^(4:ℝ) ∧ R s z
    masked L J N F G H a U alpha beta t-
      selectedPart .central L J N F G H a U alpha beta t-
      selectedPart .freeze L J N F G H a U alpha beta t =
      localPart .tail L N (sourceCutoff T eH) F G H a U alpha beta t+
      (localPart .central L N (sourceCutoff T eH) F G H a U alpha beta t-
        selectedPart .central L J N F G H a U alpha beta t)-
      selectedPart .boundary L J N F G H a U alpha beta t+
      selectedPart .outside L J N F G H a U alpha beta t := by
  dsimp only
  have he := selected_local_decomposition L J N (sourceCutoff T eH) F G H a
    (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧ R s z) alpha beta t hF hl hr ht hs
  change masked L J N F G H a _ alpha beta t = _ at he
  linear_combination he

/-- Exact full-family reconstruction: strict small-M retained and discarded
windows plus the single collective large-M field. Endpoint M=T^4 occurs
only in the large piece. All source masks and cutoff values are retained. -/
theorem family_small_large (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t =
      (∑ p ∈ range K ×ˢ range K,
        let g := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
        let h := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
        masked L J N F g h a
          (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
            ¬PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z) alpha beta t+
        masked L J N F g h a
          (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
            PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z) alpha beta t)+
      masked L J N F (fun _ => 1) (fun _ => 1) a
        (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t := by
  rw [PRZZLargeResolvedPruning.family_split L J N F _ _ a alpha beta t (T^(4:ℝ))]
  simp only [not_le]
  rw [← masked_partition P F K L J N a (fun s _ => (2:ℝ)^s < T^(4:ℝ)) alpha beta t hl hr hK]
  congr 1
  apply sum_congr rfl; intro p hp
  exact masked_split L J N F _ _ a (fun s _ => (2:ℝ)^s < T^(4:ℝ))
    (PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps) alpha beta t

/-- Substitute the small residual's actual row-local Fourier decomposition
into the complete reconstructed family. Only the small field is expanded;
the large field is the original collectively estimated expression. -/
theorem family_local_small_large (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps eH : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (ht : 0 < t) (hs : alpha+beta ≠ 0) :
    PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t =
      (∑ p ∈ range K ×ˢ range K,
        let g := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
        let h := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
        let R := fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
          ¬PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z
        selectedPart .central L J N F g h a R alpha beta t+
        localPart .tail L N (sourceCutoff T eH) F g h a R alpha beta t+
        (localPart .central L N (sourceCutoff T eH) F g h a R alpha beta t-
          selectedPart .central L J N F g h a R alpha beta t)-
        selectedPart .boundary L J N F g h a R alpha beta t+
        selectedPart .freeze L J N F g h a R alpha beta t+
        selectedPart .outside L J N F g h a R alpha beta t+
        masked L J N F g h a (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
          PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z) alpha beta t)+
      masked L J N F (fun _ => 1) (fun _ => 1) a
        (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t := by
  rw [family_small_large P F K L J N a T eps alpha beta t hl hr hK]
  congr 1
  apply sum_congr rfl; intro p hp
  dsimp only
  have he := selected_local_decomposition L J N (sourceCutoff T eH) F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
    (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
      ¬PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z)
    alpha beta t hF hFl hFr ht hs
  change masked L J N F _ _ a _ alpha beta t = _ at he
  linear_combination he

/-- The original time integral is reconstructed without copying the large
field once per arithmetic window. Actual finite-family continuity supplies
all sum/integral interchanges, also for a time-varying Gamma weight. -/
theorem partition_spatial_time (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (alpha beta : ℂ) (phi : ℝ → ℂ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hs : alpha+beta ≠ 0) (hT : 0 < T) (hphi : ContinuousOn phi (Set.Icc T (2*T))) :
    (∫ t in Set.Icc T (2*T), phi t*
      PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t) =
      (∑ p ∈ range K ×ˢ range K, ∫ t in Set.Icc T (2*T), phi t*
        masked L J N F (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
          (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
          (fun s _ => (2:ℝ)^s < T^(4:ℝ)) alpha beta t)+
      ∫ t in Set.Icc T (2*T), phi t*masked L J N F (fun _ => 1) (fun _ => 1) a
        (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t := by
  have hi (G H : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop) :
      IntegrableOn (fun t => phi t*masked L J N F G H a R alpha beta t) (Set.Icc T (2*T)) := by
    exact (hphi.mul (PRZZPrunedAFEError.selected_continuous L J N F G H hF hFl hFr a R
      alpha beta hs T hT)).integrableOn_compact isCompact_Icc
  have he (t : ℝ) : PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t =
      (∑ p ∈ range K ×ˢ range K, masked L J N F
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
        (fun s _ => (2:ℝ)^s < T^(4:ℝ)) alpha beta t)+
      masked L J N F (fun _ => 1) (fun _ => 1) a
        (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t := by
    rw [PRZZLargeResolvedPruning.family_split L J N F _ _ a alpha beta t (T^(4:ℝ))]
    simp only [not_le]
    rw [masked_partition P F K L J N a _ alpha beta t hl hr hK]
  conv_lhs => arg 2; ext t; rw [he,mul_add,mul_sum]
  rw [integral_add (integrable_finsetSum _ (fun p hp => hi _ _ _)) (hi _ _ _)]
  rw [integral_finsetSum _ (fun p hp => hi _ _ _)]

/-- The transfer-band budget and the SINGLE collective large-M integral
share a height-uniform bound. Both genuine Gamma branches are included.
This does not identify the complete small residual with its band alone. -/
theorem band_large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun x => (S x:ℂ)))
    (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a Z r eD eH : ℝ)
    (ha : 0 < a) (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L N J : ℕ) (dual : Bool) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      Continuous phi → PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖phi t‖*PRZZBandOuterMass.mass F G W js L N J dual T
          ((2:ℝ)^p.1) ((2:ℝ)^p.2) 4 eD eH t A B)+
      ‖PRZZSpatialErrorJoin.large S js L J N dual T A B phi‖ ≤
        C*T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZBandOuterMass.grid_time F G W hF hG hcF hcG hsF hW hsW
    js a 4 Z r eD eH 2 ha (by norm_num) hZ hr heD he
  obtain ⟨D,hD,hd⟩ := PRZZSpatialErrorJoin.large_time S hm hlo hhi hleft hright hS js Z r hZ hr
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,hd] with T h hd
  intro L N J dual A B phi hN hNT hA hB hsep hphi hJ
  exact (add_le_add (h L N J dual A B phi hN hNT hA hB hsep hphi hJ)
    (hd L J N dual A B phi hN hNT hA hB hsep hphi)).trans_eq (by ring)

/-- Common PRZZ budget for local tails, the full weighted transfer mass,
and the one collective large-M field. The ordinary time L1 bound is the
only mass premise; the arithmetic and Gamma masses were supplied above.
Boundary, discarded and freezing terms in family_local_small_large remain
separate terms, not silently identified with this nonnegative budget. -/
theorem three_way_przz (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun x => (S x:ℂ)))
    (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a Z r eD eH delta : ℝ)
    (ha : 0 < a) (hZ : 0 ≤ Z) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH)
    (hdelta : 0 ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L N J : ℕ) (dual : Bool) (P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 ≤ P → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Set.Icc T (2*T), ‖phi t‖) ≤ P*T →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖phi t*PRZZLocalTailBudget.field F G W js L N dual T
          ((2:ℝ)^p.1) ((2:ℝ)^p.2) 4 eD eH t A B‖)+
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖phi t‖*PRZZBandOuterMass.mass F G W js L N J dual T
          ((2:ℝ)^p.1) ((2:ℝ)^p.2) 4 eD eH t A B)+
      ‖PRZZSpatialErrorJoin.large S js L J N dual T A B phi‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZLocalTailBudget.partition_time F G W hF hG hcF hcG hsF hW hsW
    js a 4 Z r eD eH delta 1 ha (by norm_num) hZ hr heD he (by norm_num)
  obtain ⟨D,hD,hd⟩ := band_large_time S hm hlo hhi hleft hright hS F G W hF hG hcF hcG
    hsF hW hsW js a Z r eD eH ha hZ hr heD he
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,hd,Filter.eventually_ge_atTop (1:ℝ)] with T h hd hT
  intro L N J dual P A B phi hN hNT hP hA hB hsep hphi hmass hJ
  have hT0 : 0 < T := by linarith
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hpw : T^(-1:ℝ) ≤ T^delta :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hh := h L N dual P A B phi hN hNT hP hA hB hsep hphi hmass
  have hd' := hd L N J dual A B phi hN hNT hA hB hsep hphi hJ
  have hb : D*T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) ≤
      D*P*T^delta*PRZZOptimalPowers.target N T := by
    calc
      _ ≤ D*T^(-2:ℝ)*(P*T) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = D*P*T^(-1:ℝ) := by
        rw [show D*T^(-2:ℝ)*(P*T) = D*P*(T^(-2:ℝ)*T^(1:ℝ)) by rw [Real.rpow_one]; ring,
          ← Real.rpow_add hT0]
        norm_num
      _ ≤ D*P*T^delta := mul_le_mul_of_nonneg_left hpw (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg
  nlinarith only [hh,hd',hb]

#print axioms three_way_przz
#print axioms partition_spatial_time
#print axioms family_local_small_large
#print axioms band_large_time
#print axioms masked_cover
#print axioms masked_partition
#print axioms masked_split
#print axioms small_residual
#print axioms family_small_large
end XiPrime8845.PRZZSpatialReconstruction

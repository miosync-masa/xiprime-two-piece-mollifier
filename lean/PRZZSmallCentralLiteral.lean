import PRZZReconstructedAFE

/-! Strict-small central cells integrated into literal signed AStar.
The zero/negative modes and original native rejection are explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory
namespace XiPrime8845.PRZZSmallCentralLiteral
open PRZZNativeCentralLiteral PRZZCentralTail PRZZMellinSeparation
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

theorem small_cells (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    Phi (t/T)*PRZZRetainedNative.selectedPart .central L J N P G H a
      (PRZZSameMaskResidual.keep T Q eps) alpha beta t =
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
        cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t := by
  rw [PRZZRetainedNative.selected_reindex]
  simp only [sum_filter,mul_sum,cell]
  apply sum_congr rfl; intro s hss
  by_cases hsmall : (2:ℝ)^s < T^(4:ℝ)
  · simp only [PRZZSameMaskResidual.keep,hsmall,true_and,ite_true]
    apply sum_congr rfl; intro d hd
    apply sum_congr rfl; intro u hu
    apply sum_congr rfl; intro v hv
    by_cases had : PRZZDiagonalAssembly.admissible N d u v
    · simp only [if_pos had,mul_sum]
      apply sum_congr rfl; intro delta hdelta
      have hg : Nat.gcd (d*u) (d*v) = d := by
        rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
      have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have he : (¬PRZZSourceMaskFamily.discarded T Q eps s
          (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)) ↔
          |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
        simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le]
        rw [lt_div_iff₀ hd0]
        simp only [mul_comm]
      by_cases hsource : ¬PRZZSourceMaskFamily.discarded T Q eps s
          (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
      · have hf := he.mp hsource
        by_cases hz : delta ≠ 0 <;> simp [hsource,hf,hz]
      · have hf : ¬|(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d :=
          fun h => hsource (he.mpr h)
        simp [hsource,hf]
    · simp only [if_neg had,mul_zero]
  · simp only [PRZZSameMaskResidual.keep,hsmall,false_and,and_false,if_false,ite_self,sum_const_zero,mul_zero]

theorem small_time (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hleft : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T Q eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t : ℝ, Phi (t/T)*PRZZRetainedNative.selectedPart .central L J N P G H a
      (PRZZSameMaskResidual.keep T Q eps) alpha beta t) =
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
        (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          2 T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)+
         PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T a G H (fun y => PRZZWRowLimit.profile P (((2:ℝ)^s)⁻¹*y))
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
         PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)-
         ∫ t : ℝ, rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t) := by
  have hp := PRZZWRowLimit.profile_regular P hP hleft hright
  have hi (s d : ℕ) : Integrable (cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta) := by
    change Integrable (fun t => cell L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
      T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t)
    simp_rw [cell_rectangle]
    apply integrable_finsetSum; intro z hz
    by_cases hg : good L N d ((2:ℝ)^s) z
    · simp only [if_pos hg]
      have hz' := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
      exact term_integrable d J _ G H Phi a T _ alpha beta z hp.1.continuous hPhi hT
        (by positivity) (mem_Icc.mp hz'.1).1 (mem_Icc.mp hz'.2).1 hs hp.2.2 hsPhi
    · simp only [if_neg hg]; exact integrable_zero ℝ ℂ volume
  simp_rw [small_cells]
  rw [integral_finsetSum _ (fun s hss => integrable_finsetSum _ (fun d hd => hi s d))]
  apply sum_congr rfl; intro s hss
  rw [integral_finsetSum _ (fun d hd => hi s d)]
  apply sum_congr rfl; intro d hd
  exact cell_time_literal L J N d _ T _ _ G H Phi a alpha beta hp.1.continuous hPhi hT
    (by positivity) hs hp.2.2 hsPhi


def rowLiteral (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) : ℂ :=
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
        (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          2 T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)+
         PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T a G H (fun y => PRZZWRowLimit.profile P (((2:ℝ)^s)⁻¹*y))
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
         PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)-
         ∫ t : ℝ, rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          T ((2:ℝ)^s) (PRZZWRowLimit.profile P) G H Phi a alpha beta t)

theorem selected_time_literal (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hr : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T Q eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t in Set.Icc T (2*T), Phi (t/T)*PRZZRetainedNative.selectedPart .central L J N P G H a
      (PRZZSameMaskResidual.keep T Q eps) alpha beta t) =
      rowLiteral L J N P G H Phi a T Q eps alpha beta := by
  rw [PRZZFreezeRemovedLiteral.profile_time Phi _ T hT hsPhi]
  exact small_time L J N P G H Phi a hP hl hr hPhi hsPhi T Q eps hT alpha beta hs

def centralLiteral (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, rowLiteral L J N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a T ((2:ℝ)^p.1) eps alpha beta

theorem central_time_literal (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0) :
    (∫ t in Set.Icc T (2*T), Phi (t/T)*PRZZReconstructedAFE.central P F K L J N a T eps alpha beta t) =
      centralLiteral P F Phi K L J N a T eps alpha beta := by
  unfold PRZZReconstructedAFE.central centralLiteral
  simp only [mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl; intro p hp
    exact selected_time_literal L J N F _ _ Phi a hF hl hr hPhi hsPhi T _ eps hT alpha beta hs
  · intro p hp
    exact (PRZZReconstructedAFE.selected_central_integrable L J N F _ _ Phi a _ T alpha beta
      hF hl hr hPhi hsPhi hT hs).integrableOn

def literalModel (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
    ((centralLiteral P F Phi K L J N a T eps alpha beta+
      centralLiteral P F (PRZZKeptLiteral.dualProfile Phi T alpha beta) K L J N a T eps (-beta) (-alpha))-
      PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T))+
    ∫ t in Set.Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t

theorem model_eq_literal (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZReconstructedAFE.model P F Phi K L J N a T eps alpha beta =
      literalModel P F Phi K L J N a T eps alpha beta := by
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := central_time_literal P F Phi K L J N a hF hl hr hPhi hsPhi T eps hT alpha beta hs
  have h2 := central_time_literal P F (PRZZKeptLiteral.dualProfile Phi T alpha beta) K L J N a
    hF hl hr hd.1 hd.2 T eps hT (-beta) (-alpha) hs'
  simp_rw [PRZZKeptLiteral.dual_profile_time Phi T hT alpha beta] at h2
  unfold PRZZReconstructedAFE.model literalModel
  rw [h1,h2]

theorem original_error_literal (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
      literalModel P F Phi K L J N a T eps alpha beta =
      (PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
        PRZZAllPoissonAFE.model L J N F a alpha beta T (scaledCutoff Phi T))+
      PRZZReconstructedAFE.remainderPair P F Phi K L J N a T eps alpha beta := by
  rw [← model_eq_literal P F Phi K L J N a hF hFl hFr hPhi hsPhi T eps hT alpha beta ha hb hs]
  exact PRZZReconstructedAFE.original_error_eq P F Phi K L J N a T eps alpha beta
    hPl hPr hK hF hFl hFr hPhi hsPhi hT ha hb hs

/-- Strict-small spatial indices lie in a fixed finite set at each
height, even though the original exhaustion range grows with L. -/
theorem small_rejected_eventually (N : ℕ) (G : ℝ → ℂ) (Q T eps : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ s : ℕ, (2:ℝ)^s < T^(4:ℝ) → ∀ d ∈ Icc 1 N,
      ∀ (J : ℕ) (F H Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ),
      rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps) T ((2:ℝ)^s)
        F (scaledCutoff G Q) H Phi a alpha beta t = 0 := by
  let K := ⌈T^(4:ℝ)⌉₊+1
  filter_upwards [PRZZRejectedExhaustion.bounded_windows_eventually N K G Q T eps hQ hT hsG hheight]
    with L hL
  intro s hs d hd J F H Phi a alpha beta t
  have hsR : (s:ℝ) < T^(4:ℝ) := (show (s:ℝ) ≤ (2:ℝ)^s by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := s)))).trans_lt hs
  have hc : T^(4:ℝ) ≤ (⌈T^(4:ℝ)⌉₊:ℝ) := Nat.le_ceil _
  have hsn : s < ⌈T^(4:ℝ)⌉₊ := by exact_mod_cast hsR.trans_le hc
  have hsK : s ∈ range K := mem_range.mpr (by dsimp [K]; omega)
  exact hL s hsK d hd J F H Phi a alpha beta t

def cleanRowLiteral (L J N : ℕ) (P G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q eps : ℝ) (alpha beta : ℂ) : ℂ :=
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
        (PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          2 T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta)+
         PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T a G H (fun y => PRZZWRowLimit.profile P (((2:ℝ)^s)⁻¹*y))
          (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
         PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps)
          ((J:ℝ)+1) T ((2:ℝ)^s) a G H (PRZZWRowLimit.profile P) Phi beta alpha (alpha+beta))

theorem rowLiteral_clean_eventually (N : ℕ) (G : ℝ → ℂ) (Q T eps : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ (J : ℕ) (P H Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ),
      rowLiteral L J N P (scaledCutoff G Q) H Phi a T Q eps alpha beta =
        cleanRowLiteral L J N P (scaledCutoff G Q) H Phi a T Q eps alpha beta := by
  filter_upwards [small_rejected_eventually N G Q T eps hQ hT hsG hheight] with L hL
  intro J P H Phi a alpha beta
  unfold rowLiteral cleanRowLiteral
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  have hz (t : ℝ) := hL s (mem_filter.mp hs).2 d hd J (PRZZWRowLimit.profile P) H Phi a alpha beta t
  simp_rw [hz]
  simp only [integral_zero,sub_zero]

def cleanCentralLiteral (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, cleanRowLiteral L J N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a T ((2:ℝ)^p.1) eps alpha beta

/-- Remove native rejection simultaneously on the whole arithmetic grid.
The exhaustion threshold is independent of J, the time profile and shifts,
so the same statement also applies to the genuine dual Gamma profile. -/
theorem centralLiteral_clean_eventually (P : ℝ → ℂ) (K N : ℕ)
    (hsP : Function.support (PRZZWRowLimit.profile P) ⊆ Set.Icc (1/2:ℝ) 3)
    (T eps : ℝ) (hT : 0 < T) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ (J : ℕ) (F Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ),
      centralLiteral P F Phi K L J N a T eps alpha beta =
        cleanCentralLiteral P F Phi K L J N a T eps alpha beta := by
  classical
  have hall (S : Finset (ℕ × ℕ)) : ∀ᶠ L : ℕ in Filter.atTop, ∀ p ∈ S,
      ∀ (J : ℕ) (F Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ),
      rowLiteral L J N F (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a T ((2:ℝ)^p.1) eps alpha beta =
      cleanRowLiteral L J N F (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) Phi a T ((2:ℝ)^p.1) eps alpha beta := by
    induction S using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (by simp)
    | @insert p S hp ih =>
      filter_upwards [ih, rowLiteral_clean_eventually N (PRZZWRowLimit.profile P)
        ((2:ℝ)^p.1) T eps (by positivity) hT hsP hheight] with L hL hpL
      intro q hq J F Phi a alpha beta
      rcases mem_insert.mp hq with rfl | hq
      · exact hpL J F _ Phi a alpha beta
      · exact hL q hq J F Phi a alpha beta
  filter_upwards [hall (range K ×ˢ range K)] with L hL
  intro J F Phi a alpha beta
  unfold centralLiteral cleanCentralLiteral
  apply sum_congr rfl
  intro p hp
  exact hL p hp J F Phi a alpha beta

#print axioms centralLiteral_clean_eventually
#print axioms small_rejected_eventually
#print axioms rowLiteral_clean_eventually

#print axioms selected_time_literal
#print axioms central_time_literal
#print axioms model_eq_literal
#print axioms original_error_literal
#print axioms small_cells
#print axioms small_time
end XiPrime8845.PRZZSmallCentralLiteral


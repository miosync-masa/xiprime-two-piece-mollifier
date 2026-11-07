import PRZZNativeCentralLiteral
import PRZZWindowTailTime
import PRZZKeptLiteral

/-! Remove the explicit rejected rectangle correction on bounded spatial
windows. Actual cutoff support supplies the small-gap test; positive
solutions of the coprime congruence supply native labels eventually in L.
No estimate on arbitrary Fourier tails or cutoff complements is asserted. -/
noncomputable section
open scoped BigOperators
open Finset Filter MeasureTheory
namespace XiPrime8845.PRZZRejectedExhaustion
open PRZZNativeCentralLiteral PRZZMellinSeparation
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem height_eventually (eps : ℝ) (heps : eps < 1) :
    ∀ᶠ T : ℝ in atTop, 0 < T ∧ 8 ≤ T^(1-eps) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0 < 1-eps by linarith)).eventually (eventually_ge_atTop (8:ℝ))]
    with T hT hh
  exact ⟨hT,hh⟩

theorem source_small_gap (G : ℝ → ℂ) (Q T M eps : ℝ) (d u : ℕ) (delta : ℤ)
    (hQ : 0 < Q) (hT : 0 < T) (hM : 0 ≤ M) (hd : 0 < d)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hg : scaledCutoff G Q ((d:ℝ)*u) ≠ 0)
    (hheight : 8 ≤ T^(1-eps))
    (hdelta : |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T M Q eps/d) :
    |(delta:ℝ)| ≤ M*u/4 := by
  have hcut := (PRZZWindowTailTime.scaled_support G Q hQ hs hg).1
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hp : 0 < T^(1-eps) := Real.rpow_pos_of_pos hT _
  have hh : |(delta:ℝ)| * ((T^(1-eps))*(d:ℝ)) < M*Q := by
    apply (lt_div_iff₀ (mul_pos hp hd0)).mp
    simpa only [PRZZSourceCutoffs.deltaCutoff,div_div] using hdelta
  have hu : 0 ≤ (u:ℝ) := by positivity
  have hq : M*Q ≤ M*(2*(d:ℝ)*u) := by nlinarith
  have hz := abs_nonneg (delta:ℝ)
  nlinarith [mul_nonneg hz (show 0 ≤ (T^(1-eps)-8)*(d:ℝ) by positivity)]

theorem central_zero (d J : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (T M : ℝ) (alpha beta : ℂ) (z : PRZZAStar.Index) (t : ℝ)
    (hg : G ((d:ℝ)*z.1.1) = 0) :
    centralTerm d J F G H Phi a T M alpha beta z t = 0 := by
  simp [centralTerm,PRZZUnfrozenPoisson.arithmetic,hg]

/-- The retained large-gap component is zero for every L, including the
growing spatial family. This is a support argument, not a tail estimate. -/
theorem retained_outside_zero (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (Q T eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    PRZZRetainedNative.selectedPart .outside L J N F (scaledCutoff G Q) H a
      (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t = 0 := by
  rw [PRZZRetainedNative.selected_reindex]
  apply sum_eq_zero; intro s hsL
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · simp only [if_pos had]
    apply sum_eq_zero; intro delta hdel
    by_cases hr : delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eps s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · rw [if_pos hr]
      by_cases hg : scaledCutoff G Q ((d:ℝ)*u) = 0
      · simp [PRZZNativeComponents.row,PRZZUnfrozenPoisson.afeRow,hg]
      · have hgcd : Nat.gcd (d*u) (d*v) = d := by
          rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
        have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
        have hf : |(delta:ℝ)| < PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps/d := by
          rw [lt_div_iff₀ hd0]
          have hh := hr.2
          simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hgcd,not_le] at hh
          simpa only [mul_comm] using hh
        have hh := source_small_gap G Q T ((2:ℝ)^s) eps d u delta hQ hT (by positivity)
          (mem_Icc.mp hd).1 hs hg hheight hf
        simp only [PRZZNativeComponents.row,Int.cast_neg,abs_neg,if_pos hh]
    · simp only [if_neg hr]
  · simp only [if_neg had]

/-- Remove the actual outside component from the previously displayed
remainder. The cutoff complement and the other three components remain
explicit; arbitrary single cutoff windows need not cover all coefficients. -/
theorem remainder_reduced (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    PRZZKeptLiteral.remainderField P G H js L J N T Q V eps alpha beta t =
      let seed := fun x => (P x:ℂ)
      let g := scaledCutoff G Q
      let h := scaledCutoff H V
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let part := fun which => PRZZRetainedNative.selectedPart which L J N seed g h a
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t
      (PRZZAllPoissonRows.family L J N seed (fun _ => 1) (fun _ => 1) a alpha beta t-
        PRZZAllPoissonRows.family L J N seed g h a alpha beta t)+
        (part .tail-part .boundary+part .freeze) := by
  unfold PRZZKeptLiteral.remainderField
  dsimp only
  rw [retained_outside_zero L J N _ G _ _ Q T eps alpha beta t hQ hT hs hheight,add_zero]

/-- Only genuinely missing finite AFE labels remain; failure of the
small-gap test contributes zero by the original scaled cutoff. -/
theorem rejected_native_only (L J N d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (Q T M eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hQ : 0 < Q) (hT : 0 < T) (hM : 0 ≤ M) (hd : 0 < d)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    rejected L J N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) T M
      F (scaledCutoff G Q) H Phi a alpha beta t =
    ∑ z ∈ PRZZAStar.indices N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2,
      if -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) then 0
      else centralTerm d J F (scaledCutoff G Q) H Phi a T M alpha beta z t := by
  unfold rejected
  apply sum_congr rfl
  intro z hz
  by_cases hg : scaledCutoff G Q ((d:ℝ)*z.1.1) = 0
  · have he := central_zero d J F (scaledCutoff G Q) H Phi a T M alpha beta z t hg
    simp only [he,ite_self]
  · have hdel := (mem_filter.mp (mem_product.mp (mem_product.mp hz).2).1).2.2
    have hh := source_small_gap G Q T M eps d z.1.1 z.2.1 hQ hT hM hd hs hg hheight hdel
    simp only [good,hh,and_true]

/-- Positive original AFE indices realize every signed coprime gap. -/
theorem positive_solution (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hc : u.Coprime v) (delta : ℤ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ (m:ℤ)*u-(k:ℤ)*v=delta := by
  let m0 := delta*(PRZZKloostermanInputs.inverseResidue v u:ℤ)
  have hdiv : (v:ℤ) ∣ m0*u-delta :=
    (PRZZCongruencePoisson.congruence_iff u v hv hc m0 delta).mpr (by simp [m0])
  obtain ⟨k0,hk0⟩ := hdiv
  let j := 1+|m0|+|k0|
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hu' : (1:ℤ) ≤ u := by exact_mod_cast hu
  have hv' : (1:ℤ) ≤ v := by exact_mod_cast hv
  have hm : 0 < m0+(v:ℤ)*j := by
    have hh := mul_le_mul_of_nonneg_right hv' hj
    dsimp [j] at hh
    linarith [neg_abs_le m0,abs_nonneg k0]
  have hk : 0 < k0+(u:ℤ)*j := by
    have hh := mul_le_mul_of_nonneg_right hu' hj
    dsimp [j] at hh
    linarith [neg_abs_le k0,abs_nonneg m0]
  refine ⟨(m0+v*j).toNat,(k0+u*j).toNat,by omega,by omega,?_⟩
  rw [Int.toNat_of_nonneg hm.le,Int.toNat_of_nonneg hk.le]
  nlinarith only [hk0]

theorem native_gap_eventually (N d u v : ℕ) (delta : ℤ) (hd : 0 < d)
    (hu : 0 < u) (hv : 0 < v) (hc : u.Coprime v)
    (hdu : d*u ≤ N) (hdv : d*v ≤ N) :
    ∀ᶠ L : ℕ in atTop, delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v) := by
  obtain ⟨m,k,hm,hk,he⟩ := positive_solution u v hu hv hc delta
  filter_upwards [eventually_ge_atTop (max m k)] with L hL
  rw [PRZZNativeFamily.mem_gaps]
  apply mem_image.mpr
  refine ⟨((m,k),(d*u,d*v)),?_,?_⟩
  · exact mem_product.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hm,(le_max_left _ _).trans hL⟩,
      mem_Icc.mpr ⟨hk,(le_max_right _ _).trans hL⟩⟩,
      mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hu,hdu⟩,
        mem_Icc.mpr ⟨Nat.mul_pos hd hv,hdv⟩⟩⟩
  · have hg : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]
    simp only [PRZZAFEIndices.label,PRZZNativeFamily.pairLabel,hg,
      Nat.mul_div_cancel_left _ hd,he]

/-- The threshold precedes the Fourier cutoff and time. It depends on the
fixed rectangle, not on the summands or on their analytic parameters. -/
theorem rectangle_eventually (N d : ℕ) (D : ℝ) (hd : 0 < d) :
    ∀ᶠ L : ℕ in atTop, ∀ z ∈ PRZZAStar.indices N d D 2,
      -z.2.1 ∈ PRZZNativeFamily.gaps L N (d*z.1.1) (d*z.1.2) := by
  apply (eventually_all_finset _).mpr
  intro z hz
  have hp := mem_filter.mp (mem_product.mp hz).1
  have huv := mem_product.mp hp.1
  exact native_gap_eventually N d z.1.1 z.1.2 (-z.2.1) hd
    (mem_Icc.mp huv.1).1 (mem_Icc.mp huv.2).1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- Exact disappearance of the rejected correction on every fixed window.
This does not interchange the growing spatial range with the L limit. -/
theorem rejected_eventually (N d : ℕ) (G : ℝ → ℂ) (Q T M eps : ℝ)
    (hQ : 0 < Q) (hT : 0 < T) (hM : 0 ≤ M) (hd : 0 < d)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in atTop, ∀ (J : ℕ) (F H Phi : ℝ → ℂ) (a : ℕ → ℂ)
      (alpha beta : ℂ) (t : ℝ),
      rejected L J N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) T M
        F (scaledCutoff G Q) H Phi a alpha beta t = 0 := by
  filter_upwards [rectangle_eventually N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) hd] with L hL
  intro J F H Phi a alpha beta t
  rw [rejected_native_only L J N d F G H Phi a Q T M eps alpha beta t hQ hT hM hd hs hheight]
  exact sum_eq_zero (fun z hz => if_pos (hL z hz))

/-- One L threshold for a fixed finite family of spatial windows and all
gcd rows; no additional dyadic or allocation counting loss is spent. -/
theorem bounded_windows_eventually (N K : ℕ) (G : ℝ → ℂ) (Q T eps : ℝ)
    (hQ : 0 < Q) (hT : 0 < T)
    (hs : Function.support G ⊆ Set.Icc (1/2:ℝ) 3) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in atTop, ∀ s ∈ range K, ∀ d ∈ Icc 1 N,
      ∀ (J : ℕ) (F H Phi : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ) (t : ℝ),
      rejected L J N d (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eps) T ((2:ℝ)^s)
        F (scaledCutoff G Q) H Phi a alpha beta t = 0 := by
  apply (eventually_all_finset _).mpr
  intro s hsK
  apply (eventually_all_finset _).mpr
  intro d hd
  exact rejected_eventually N d G Q T ((2:ℝ)^s) eps hQ hT (by positivity)
    (mem_Icc.mp hd).1 hs hheight

/-- Substitute exhaustion into the actual time-integral identity, retaining
the zero mode, the negative modes, and the genuine positive literal A*. -/
theorem cell_time_literal_eventually (N d : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (Q T M eps : ℝ) (alpha beta : ℂ)
    (hQ : 0 < Q) (hT : 0 < T) (hM : 0 < M) (hd : 0 < d)
    (hF : Continuous F) (hP : Continuous Phi) (hsigma : alpha+beta ≠ 0)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2) (hheight : 8 ≤ T^(1-eps)) :
    ∀ᶠ L : ℕ in atTop, ∀ J : ℕ,
      (∫ t : ℝ, cell L J N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) T M
        F (scaledCutoff G Q) H Phi a alpha beta t) =
      PRZZSignedCentral.signedLiteral 0 N d (PRZZSourceCutoffs.deltaCutoff T M Q eps)
        2 T M a (scaledCutoff G Q) H F Phi beta alpha (alpha+beta)+
      PRZZAStar.literal N d (PRZZSourceCutoffs.deltaCutoff T M Q eps) ((J:ℝ)+1) T
        a (scaledCutoff G Q) H (fun y => F (M⁻¹*y))
        (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha+
      PRZZSignedCentral.signedLiteral (-1) N d (PRZZSourceCutoffs.deltaCutoff T M Q eps)
        ((J:ℝ)+1) T M a (scaledCutoff G Q) H F Phi beta alpha (alpha+beta) := by
  filter_upwards [rejected_eventually N d G Q T M eps hQ hT hM.le hd hsG hheight] with L hL
  intro J
  rw [cell_time_literal L J N d _ T M F (scaledCutoff G Q) H Phi a alpha beta
    hF hP hT hM hsigma hsF hsP]
  simp only [hL J F H Phi a alpha beta,integral_zero,sub_zero]

#print axioms source_small_gap
#print axioms height_eventually
#print axioms central_zero
#print axioms retained_outside_zero
#print axioms remainder_reduced
#print axioms rejected_native_only
#print axioms positive_solution
#print axioms native_gap_eventually
#print axioms rectangle_eventually
#print axioms rejected_eventually
#print axioms bounded_windows_eventually
#print axioms cell_time_literal_eventually
end XiPrime8845.PRZZRejectedExhaustion

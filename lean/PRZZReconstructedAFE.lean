import PRZZSameMaskResidual
import PRZZSameMaskFreezeBudget

/-! One reconstructed arithmetic model, not a sum of single-window models.
The complementary large spatial family occurs exactly once per AFE branch.
All correction fields are explicit native expressions before integration. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Finset MeasureTheory Complex Set
namespace XiPrime8845.PRZZReconstructedAFE
open PRZZMellinSeparation PRZZRetainedNative PRZZSameMaskResidual PRZZResolvedComplement
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def central (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, selectedPart .central L J N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
    (keep T ((2:ℝ)^p.1) eps) alpha beta t

def tailBand (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K,
    let g := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
    let h := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
    masked L J N F g h a (keep T ((2:ℝ)^p.1) eps) alpha beta t-
      selectedPart .central L J N F g h a (keep T ((2:ℝ)^p.1) eps) alpha beta t-
      selectedPart .freeze L J N F g h a (keep T ((2:ℝ)^p.1) eps) alpha beta t

def freezing (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, selectedPart .freeze L J N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
    (keep T ((2:ℝ)^p.1) eps) alpha beta t

def discarded (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K, masked L J N F
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)) a
    (fun s z => (2:ℝ)^s < T^(4:ℝ) ∧
      PRZZSourceMaskFamily.discarded T ((2:ℝ)^p.1) eps s z) alpha beta t

def correction (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  tailBand P F K L J N a T eps alpha beta t+
    freezing P F K L J N a T eps alpha beta t+
    discarded P F K L J N a T eps alpha beta t+
    masked L J N F (fun _ => 1) (fun _ => 1) a
      (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t

theorem family_eq (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (t : ℝ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t =
      central P F K L J N a T eps alpha beta t+correction P F K L J N a T eps alpha beta t := by
  rw [PRZZSpatialReconstruction.family_small_large P F K L J N a T eps alpha beta t hl hr hK]
  unfold central correction tailBand freezing discarded
  dsimp only
  simp only [sum_add_distrib,sum_sub_distrib]
  unfold PRZZSameMaskResidual.keep
  ring

/-- Insert the supplied strict-small boundary/outside zeros into every
arithmetic window. The surviving band has LOCAL-minus-COMMON sign. -/
theorem tailBand_reduced (P F : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps eH : ℝ) (alpha beta : ℂ) (t : ℝ) (hN : 1 ≤ N)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0) (hT : 0 < T) (ht : 0 < t)
    (hs : alpha+beta ≠ 0) (hheight : 8 ≤ T^(1-eps)) (hL : 4*(N:ℝ)*T^(4:ℝ) ≤ L) :
    tailBand P F K L J N a T eps alpha beta t =
      ∑ p ∈ range K ×ˢ range K,
        let g := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1)
        let h := scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2)
        let R := keep T ((2:ℝ)^p.1) eps
        PRZZSelectedLocalFourier.localPart .tail L N (PRZZSelectedLocalFourier.sourceCutoff T eH)
          F g h a R alpha beta t+
        (PRZZSelectedLocalFourier.localPart .central L N (PRZZSelectedLocalFourier.sourceCutoff T eH)
          F g h a R alpha beta t-selectedPart .central L J N F g h a R alpha beta t) := by
  unfold tailBand
  apply sum_congr rfl; intro p hp
  exact reduced_residual L J N F (PRZZWRowLimit.profile P) _ a T ((2:ℝ)^p.1) eps eH t
    alpha beta hN hF hFl hFr hT ht (by positivity) hs
    (PRZZWRowLimit.profile_regular P hP hPl hPr).2.2 hheight hL

theorem selected_central_integrable (L J N : ℕ) (F G H Phi : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (T : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0) (hPhi : Continuous Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) (hT : 0 < T) (hs : alpha+beta ≠ 0) :
    Integrable (fun t => Phi (t/T)*selectedPart .central L J N F G H a R alpha beta t) := by
  simp_rw [selected_reindex]
  simp only [mul_sum,mul_ite,mul_zero]
  apply integrable_finsetSum; intro s hss
  apply integrable_finsetSum; intro d hd
  apply integrable_finsetSum; intro u hu
  apply integrable_finsetSum; intro v hv
  split_ifs
  · apply integrable_finsetSum; intro delta hdel
    split_ifs
    · unfold PRZZNativeComponents.row
      dsimp only
      split_ifs
      · exact PRZZNativeCentralLiteral.term_integrable d J (PRZZWRowLimit.profile F) G H Phi a T
          ((2:ℝ)^s) alpha beta ((u,v),(-delta,1))
          (PRZZWRowLimit.profile_regular F hF hl hr).1.continuous hPhi hT (by positivity)
          (mem_Icc.mp hu).1 (mem_Icc.mp hv).1 hs
          (PRZZWRowLimit.profile_regular F hF hl hr).2.2 hsPhi
      · simp
    · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _

/-- Integrate the actual reconstructed field. Integrability of the
correction is derived from its explicit family identity, not assumed. -/
theorem time_split (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) :
    (∫ t in Icc T (2*T), Phi (t/T)*PRZZAllPoissonRows.family L J N F
      (fun _ => 1) (fun _ => 1) a alpha beta t) =
      (∫ t in Icc T (2*T), Phi (t/T)*central P F K L J N a T eps alpha beta t)+
      ∫ t in Icc T (2*T), Phi (t/T)*correction P F K L J N a T eps alpha beta t := by
  have hc : Integrable (fun t => Phi (t/T)*central P F K L J N a T eps alpha beta t) := by
    unfold central
    simp only [mul_sum]
    apply integrable_finsetSum; intro p hp
    exact selected_central_integrable L J N F _ _ Phi a _ T alpha beta hF hFl hFr hPhi hsPhi hT hs
  have hi : IntegrableOn (fun t => Phi (t/T)*PRZZAllPoissonRows.family L J N F
      (fun _ => 1) (fun _ => 1) a alpha beta t) (Icc T (2*T)) :=
    ((hPhi.comp (continuous_id.div_const T)).continuousOn.mul
      (PRZZArithmeticCutoffPartition.family_continuous L J N F _ _ a alpha beta T hF hFl hFr hs hT)).integrableOn_compact isCompact_Icc
  have he (t : ℝ) := family_eq P F K L J N a T eps alpha beta t hPl hPr hK
  have hr : IntegrableOn (fun t => Phi (t/T)*correction P F K L J N a T eps alpha beta t)
      (Icc T (2*T)) := by
    have hh := hi.sub hc.integrableOn
    apply hh.congr
    apply Filter.Eventually.of_forall
    intro t
    change Phi (t/T)*PRZZAllPoissonRows.family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t-
      Phi (t/T)*central P F K L J N a T eps alpha beta t = _
    rw [he]
    ring
  conv_lhs => arg 2; ext t; rw [he,mul_add]
  exact integral_add hc.integrableOn hr

def model (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
    (((∫ t in Icc T (2*T), Phi (t/T)*central P F K L J N a T eps alpha beta t)+
      ∫ t in Icc T (2*T), (Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t)*
        central P F K L J N a T eps (-beta) (-alpha) t)-
      PRZZZeroCoupled.zeroPair N a alpha beta T (scaledCutoff Phi T))+
    ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t

def remainderPair (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Icc T (2*T), Phi (t/T)*correction P F K L J N a T eps alpha beta t)+
    ∫ t in Icc T (2*T), (Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t)*
      correction P F K L J N a T eps (-beta) (-alpha) t

theorem model_split (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZAllPoissonAFE.model L J N F a alpha beta T (scaledCutoff Phi T) =
      model P F Phi K L J N a T eps alpha beta+remainderPair P F Phi K L J N a T eps alpha beta := by
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := time_split P F Phi K L J N a T eps alpha beta hPl hPr hK hF hFl hFr hPhi hsPhi hT hs
  have h2 := time_split P F (PRZZKeptLiteral.dualProfile Phi T alpha beta) K L J N a T eps
    (-beta) (-alpha) hPl hPr hK hF hFl hFr hd.1 hd.2 hT hs'
  simp_rw [PRZZKeptLiteral.dual_profile_time Phi T hT alpha beta] at h2
  have he : scaledCutoff Phi T = fun t => Phi (t/T) := by
    funext t; simp [scaledCutoff,div_eq_mul_inv,mul_comm]
  unfold PRZZAllPoissonAFE.model model remainderPair
  simp_rw [he]
  rw [h1,h2]
  ring

theorem original_error_eq (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
      model P F Phi K L J N a T eps alpha beta =
      (PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
        PRZZAllPoissonAFE.model L J N F a alpha beta T (scaledCutoff Phi T))+
      remainderPair P F Phi K L J N a T eps alpha beta := by
  rw [model_split P F Phi K L J N a T eps alpha beta hPl hPr hK hF hFl hFr hPhi hsPhi hT ha hb hs]
  ring

/-- The original AFE limit transfers to the reconstructed model with its
EXPLICIT correction pair. This is not a bound on that pair: its freezing
and discarded subfamilies must still be absorbed with their exact masks. -/
theorem scaled_error_limit (P F Phi : ℝ → ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r delta eps : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ J : ℕ → ℕ, ∃ E : ℂ,
        Filter.Tendsto (fun L =>
          PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
          model P F Phi (Nat.log 2 N+2) L (J L) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))-
          remainderPair P F Phi (Nat.log 2 N+2) L (J L) N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) Filter.atTop (𝓝 E) ∧
        ‖E‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZAllPoissonAFE.scaled_afe_limit F hF hFl hFr js S r delta hS hr hd
  obtain ⟨U,hU,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨C*U,by positivity,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Filter.eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro A B hA hB hsep N hN hNT J
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  obtain ⟨E,hlim,hbound⟩ := h A B hA hB hsep N hN hNT (scaledCutoff Phi T) U
    (hPhi.comp (continuous_const.mul continuous_id)) hU.le (fun t _ => (hcut T hT0).1 t) J
  refine ⟨E,?_,by simpa only [mul_assoc] using hbound⟩
  convert hlim using 1
  funext L
  have he := model_split P F Phi (Nat.log 2 N+2) L (J L) N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps _ _ hPl hPr
    (PRZZArithmeticCutoffPartition.dyadic_scale_count N) hF hFl hFr hPhi hsPhi hT0
    (hsmall.2 A hA) (hsmall.2 B hB) hs
  rw [he]
  exact sub_sub _ _ _

/-- The actual freezing field in correction, integrated on BOTH branches,
is exactly the finite sum of the same-mask row-pair corrections. -/
theorem freezing_pair_time (P F phi : ℝ → ℂ) (K L J N : ℕ) (js : List ℕ)
    (T eps : ℝ) (alpha beta : ℂ) (hT : 0 < T)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Icc T (2*T))) :
    (∫ t in Icc T (2*T), phi t*freezing P F K L J N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta t)+
    (∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      freezing P F K L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (-beta) (-alpha) t) =
    ∑ p ∈ range K ×ˢ range K, PRZZSameMaskFreezeBudget.freezePair F
      (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) phi js L J N
      T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta := by
  have htime (alpha beta : ℂ) (hab : alpha+beta ≠ 0) (phi : ℝ → ℂ)
      (hp : ContinuousOn phi (Icc T (2*T))) :
      (∫ t in Icc T (2*T), phi t*freezing P F K L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps alpha beta t) =
      ∑ p ∈ range K ×ˢ range K, ∫ t in Icc T (2*T), phi t*selectedPart .freeze L J N F
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (keep T ((2:ℝ)^p.1) eps) alpha beta t := by
    unfold freezing
    simp only [mul_sum]
    apply integral_finsetSum
    intro p hp'
    exact (hp.mul (PRZZNativeFreezeTime.selected_continuous L J N F _ _ _ _ alpha beta T hT hab)).integrableOn_compact isCompact_Icc
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  rw [htime alpha beta hs phi hphi,htime (-beta) (-alpha) hs'
    (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t) (hphi.mul hg.continuousOn)]
  simp only [PRZZSameMaskFreezeBudget.freezePair,sum_add_distrib]

/-- The exact reconstructed freezing pair, rather than a supplied mass,
satisfies the sharp budget uniformly in both truncations. -/
theorem freezing_absorbed (P F : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ) (U : ℝ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → 0 ≤ U → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ U) →
      ‖(∫ t in Icc T (2*T), phi t*freezing P F (Nat.log 2 N+2) L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)+
        (∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)*
          freezing P F (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            T eps ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ)) t)‖ ≤
        C*U*T^delta*PRZZOptimalPowers.target N T := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  obtain ⟨C,hC,h⟩ := PRZZSameMaskFreezeBudget.partition_bound F _ _ hF hFl hFr
    hp.1.continuous hp.1.continuous hp.2.1 hp.2.1 hp.2.2 hp.2.2
    js S r eps eta delta hS hr heps heps1 heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Filter.eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro L J N A B phi U hN hscale hA hB hsep hphi hU hcap
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  rw [show (-B)/(Real.log T:ℂ) = -(B/(Real.log T:ℂ)) by ring,
    show (-A)/(Real.log T:ℂ) = -(A/(Real.log T:ℂ)) by ring,
    freezing_pair_time P F phi _ L J N js T eps _ _ (by linarith)
      (hsmall.2 A hA) (hsmall.2 B hB) hs hphi.continuousOn]
  exact (norm_sum_le _ _).trans (h L J N A B phi U hN hscale hA hB hsep hphi hU hcap)

#print axioms freezing_pair_time
#print axioms freezing_absorbed
#print axioms scaled_error_limit
#print axioms family_eq
#print axioms tailBand_reduced
#print axioms selected_central_integrable
#print axioms time_split
#print axioms model_split
#print axioms original_error_eq
end XiPrime8845.PRZZReconstructedAFE

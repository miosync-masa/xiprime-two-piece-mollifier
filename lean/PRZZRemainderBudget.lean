import PRZZStrictSmallTail
import PRZZSelectedDiscardedFamily

/-! A bound on the original reconstructed remainderPair. The strict source
mask, local-minus-common band, actual dual Gamma multiplier and the single
collective large spatial field are preserved throughout. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZRemainderBudget
open PRZZMellinSeparation PRZZReconstructedAFE PRZZRetainedNative
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def paired (f : ℂ → ℂ → ℝ → ℂ) (Phi : ℝ → ℂ) (T : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Icc T (2*T), Phi (t/T)*f alpha beta t)+
    ∫ t in Icc T (2*T), (Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t)*f (-beta) (-alpha) t

def largeField (F : ℝ → ℂ) (L J N : ℕ) (a : ℕ → ℂ) (T : ℝ)
    (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZResolvedComplement.masked L J N F (fun _ => 1) (fun _ => 1) a
    (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s) alpha beta t

theorem component_integrable (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hs : alpha+beta ≠ 0) :
    IntegrableOn (fun t => Phi (t/T)*tailBand P F K L J N a T eps alpha beta t) (Icc T (2*T)) ∧
    IntegrableOn (fun t => Phi (t/T)*freezing P F K L J N a T eps alpha beta t) (Icc T (2*T)) ∧
    IntegrableOn (fun t => Phi (t/T)*discarded P F K L J N a T eps alpha beta t) (Icc T (2*T)) ∧
    IntegrableOn (fun t => Phi (t/T)*largeField F L J N a T alpha beta t) (Icc T (2*T)) := by
  have hp : ContinuousOn (fun t => Phi (t/T)) (Icc T (2*T)) :=
    (hPhi.comp (continuous_id.div_const T)).continuousOn
  have hm (G H : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop) :
      IntegrableOn (fun t => Phi (t/T)*PRZZResolvedComplement.masked L J N F G H a R alpha beta t)
        (Icc T (2*T)) :=
    (hp.mul (PRZZPrunedAFEError.selected_continuous L J N F G H hF hl hr a R
      alpha beta hs T hT)).integrableOn_compact isCompact_Icc
  have hf (G H : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop) :
      IntegrableOn (fun t => Phi (t/T)*selectedPart .freeze L J N F G H a R alpha beta t)
        (Icc T (2*T)) :=
    (hp.mul (PRZZNativeFreezeTime.selected_continuous L J N F G H a R alpha beta T hT hs)).integrableOn_compact isCompact_Icc
  refine ⟨?_,?_,?_,hm _ _ _⟩
  · unfold tailBand
    simp only [mul_sum,mul_sub]
    apply integrable_finsetSum; intro p hpp
    exact ((hm _ _ _).sub
      (selected_central_integrable L J N F _ _ Phi a _ T alpha beta hF hl hr hPhi hsPhi hT hs).integrableOn).sub (hf _ _ _)
  · unfold freezing
    simp only [mul_sum]
    exact integrable_finsetSum _ (fun p hpp => hf _ _ _)
  · unfold discarded
    simp only [mul_sum]
    exact integrable_finsetSum _ (fun p hpp => hm _ _ _)

theorem remainder_split (P F Phi : ℝ → ℂ) (K L J N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    remainderPair P F Phi K L J N a T eps alpha beta =
      paired (tailBand P F K L J N a T eps) Phi T alpha beta+
      paired (freezing P F K L J N a T eps) Phi T alpha beta+
      paired (discarded P F K L J N a T eps) Phi T alpha beta+
      paired (largeField F L J N a T) Phi T alpha beta := by
  have ht (Psi : ℝ → ℂ) (hPsi : Continuous Psi)
      (hsPsi : Function.support Psi ⊆ Icc (1:ℝ) 2) (u v : ℂ) (huv : u+v ≠ 0) :
      (∫ t in Icc T (2*T), Psi (t/T)*correction P F K L J N a T eps u v t) =
      (∫ t in Icc T (2*T), Psi (t/T)*tailBand P F K L J N a T eps u v t)+
      (∫ t in Icc T (2*T), Psi (t/T)*freezing P F K L J N a T eps u v t)+
      (∫ t in Icc T (2*T), Psi (t/T)*discarded P F K L J N a T eps u v t)+
      (∫ t in Icc T (2*T), Psi (t/T)*largeField F L J N a T u v t) := by
    obtain ⟨h1,h2,h3,h4⟩ := component_integrable P F Psi K L J N a T eps u v hF hl hr hPsi hsPsi hT huv
    unfold correction
    simp only [mul_add]
    have e12 := integral_add h1 h2
    have e123 := integral_add (h1.add h2) h3
    have e := integral_add ((h1.add h2).add h3) h4
    simp only [Pi.add_apply] at e12 e123 e
    rw [e123,e12] at e
    simpa only [largeField] using e
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := ht Phi hPhi hsPhi alpha beta hs
  have h2 := ht (PRZZKeptLiteral.dualProfile Phi T alpha beta) hd.1 hd.2 (-beta) (-alpha) hs'
  simp_rw [PRZZKeptLiteral.dual_profile_time Phi T hT alpha beta] at h2
  unfold remainderPair paired
  rw [h1,h2]
  ring

theorem freezing_pair_eq (P F Phi : ℝ → ℂ) (K L J N : ℕ) (js : List ℕ)
    (T eps : ℝ) (alpha beta : ℂ) (hT : 0 < T) (hs : alpha+beta ≠ 0)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hPhi : Continuous Phi) :
    paired (freezing P F K L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps)
      Phi T alpha beta =
    ∑ p ∈ range K ×ˢ range K, PRZZSameMaskFreezeBudget.freezePair F
      (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (fun t => Phi (t/T)) js L J N T
      ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps alpha beta := by
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hp : Continuous (fun t => Phi (t/T)) := hPhi.comp (continuous_id.div_const T)
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  have hi (u v : ℂ) (huv : u+v ≠ 0) (phi : ℝ → ℂ) (hphi : Continuous phi)
      (p : ℕ × ℕ) : IntegrableOn (fun t => phi t*selectedPart .freeze L J N F
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
      (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps) u v t)
      (Icc T (2*T)) :=
    (hphi.continuousOn.mul (PRZZNativeFreezeTime.selected_continuous L J N F _ _ _ _ u v T hT huv)).integrableOn_compact isCompact_Icc
  unfold paired freezing PRZZSameMaskFreezeBudget.freezePair
  simp only [mul_sum,sum_add_distrib]
  rw [integral_finsetSum _ (fun p hp' => hi alpha beta hs _ hp p)]
  congr 1
  exact integral_finsetSum _ (fun p hp' => hi (-beta) (-alpha) hs'
    (fun t => Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t) (hp.mul hg) p)

/-- The original tail+band has arbitrary decay uniformly in L and J.
The card of the finite arithmetic grid is paid by height, never by L. -/
theorem tailBand_uniform (P : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0)
    (js : List ℕ) (S r eps eH power : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N : ℕ) (dual : Bool) (A B : ℂ) (t : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → t ∈ Icc T (2*T) →
      ‖PRZZResolvedTailMass.branch dual A B T t *
        tailBand P P (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^(-power) := by
  obtain ⟨hw,hcw,hsw⟩ := PRZZWRowLimit.profile_regular P hP hl hright
  let W := PRZZWRowLimit.profile P
  obtain ⟨Ct,hCt,htail⟩ := PRZZStrictSmallTail.uniform W W W hw.continuous hw.continuous hcw hcw hsw
    hw hsw js 1 4 S r eps eH (power+1) (by norm_num) (by norm_num) hS hr heps he
  obtain ⟨Cb,hCb,hband⟩ := PRZZBandOuterMass.uniform W W W hw.continuous hw.continuous hcw hcw hsw
    hw hsw js 1 4 S r eps eH (power+1) (by norm_num) (by norm_num) hS hr heps he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  refine ⟨D*(Ct+Cb),by positivity,?_⟩
  filter_upwards [htail,hband,PRZZRejectedExhaustion.height_eventually eps heps1,
    eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (S+1)))] with T ht hb hh hT hlog
  intro L J N dual A B t hN hNT hL hJ hA hB hsep htime
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
        ((le_max_left _ _).trans hlog))))
  rw [tailBand_reduced P P _ L J N _ T eps eH _ _ t hN hP hl hright hP hl hright hT0
    (lt_of_lt_of_le hT0 htime.1) hs hh.2 hL,mul_sum]
  have hrow (p : ℕ × ℕ) (hp : p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)) :
      ‖PRZZResolvedTailMass.branch dual A B T t *
        (PRZZSelectedLocalFourier.localPart .tail L N (PRZZSelectedLocalFourier.sourceCutoff T eH)
          P (scaledCutoff W ((2:ℝ)^p.1)) (scaledCutoff W ((2:ℝ)^p.2))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t+
         (PRZZSelectedLocalFourier.localPart .central L N (PRZZSelectedLocalFourier.sourceCutoff T eH)
          P (scaledCutoff W ((2:ℝ)^p.1)) (scaledCutoff W ((2:ℝ)^p.2))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
          selectedPart .central L J N P (scaledCutoff W ((2:ℝ)^p.1)) (scaledCutoff W ((2:ℝ)^p.2))
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t))‖ ≤ (Ct+Cb)*T^(-(power+1)) := by
    have hq : ((2:ℝ)^p.1) ≤ 2*T := by
      have hx : p.1 ≤ Nat.log 2 N+1 := by have := (mem_range.mp (mem_product.mp hp).1); omega
      have hpow : (2:ℝ)^(Nat.log 2 N) ≤ N := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      calc
        _ ≤ (2:ℝ)^(Nat.log 2 N+1) := pow_le_pow_right₀ (by norm_num) hx
        _ = 2*(2:ℝ)^(Nat.log 2 N) := by rw [pow_succ]; ring
        _ ≤ 2*T := by linarith
    have h1 := ht L N dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B hN hNT (by positivity) htime hA hB hsep
    have h2 := (PRZZSameMaskResidual.band_dominated P W W js L N J dual T
      ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps eH t A B hT
      (by positivity) hq).trans (hb L N J dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B
        hN hNT (by positivity) htime hA hB hsep hJ)
    rw [← PRZZStrictSmallTail.local_identification P W W js L N dual T _ _ eps eH t A B] at h1
    rw [mul_add]
    exact (norm_add_le _ _).trans ((add_le_add h1
      (by simpa only [PRZZSameMaskResidual.bandField,mul_sub,norm_sub_rev] using h2)).trans_eq (by ring))
  calc
    _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2), (Ct+Cb)*T^(-(power+1)) :=
      (norm_sum_le _ _).trans (sum_le_sum hrow)
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*((Ct+Cb)*T^(-(power+1))) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*((Ct+Cb)*T^(-(power+1))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using hgrid N hN T hNT ((le_max_left _ _).trans hlog)
    _ = _ := by
      rw [show (D*T)*((Ct+Cb)*T^(-(power+1))) = (D*(Ct+Cb))*(T^(1:ℝ)*T^(-(power+1))) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT0,show (1:ℝ)+-(power+1) = -power by ring]

#print axioms component_integrable
#print axioms remainder_split
#print axioms freezing_pair_eq
#print axioms tailBand_uniform
end XiPrime8845.PRZZRemainderBudget


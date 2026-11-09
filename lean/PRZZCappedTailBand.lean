import PRZZRemainderAbsorption
import PRZZCappedSameMask
import PRZZClassZeroCorrection

/-! Insert the actual strict-source tail and common/local transfer band
into the original reconstructed tailBand. Both Gamma branches, all native
filters and the original exhaustion condition are retained. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZCappedTailBand
open PRZZMellinSeparation PRZZReconstructedAFE PRZZRemainderBudget PRZZRetainedNative
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem tailBand_uniform (P : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eH power : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ℕ → ℂ) (L J N : ℕ) (dual : Bool) (A B : ℂ) (t : ℝ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → t ∈ Icc T (2*T) →
      ‖PRZZResolvedTailMass.branch dual A B T t *
        tailBand P P (Nat.log 2 N+2) L J N c
          T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^(-power) := by
  obtain ⟨hw,hcw,hsw⟩ := PRZZWRowLimit.profile_regular P hP hl hright
  let W := PRZZWRowLimit.profile P
  obtain ⟨Ct,hCt,htail⟩ := PRZZCappedStrictTail.uniform W W W hw.continuous hw.continuous hcw hcw hsw
    hw hsw Hcap hHcap 1 4 S r eps eH (power+1) (by norm_num) (by norm_num) hS hr heps he
  obtain ⟨Cb,hCb,hband⟩ := PRZZCappedBandOuter.uniform W W W hw.continuous hw.continuous hcw hcw hsw
    hw hsw Hcap hHcap 1 4 S r eps eH (power+1) (by norm_num) (by norm_num) hS hr heps he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  refine ⟨D*(Ct+Cb),by positivity,?_⟩
  filter_upwards [htail,hband,PRZZRejectedExhaustion.height_eventually eps heps1,
    eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (S+1)))] with T ht hb hh hT hlog
  intro c L J N dual A B t hcoef hN hNT hL hJ hA hB hsep htime
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
          c (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t+
         (PRZZSelectedLocalFourier.localPart .central L N (PRZZSelectedLocalFourier.sourceCutoff T eH)
          P (scaledCutoff W ((2:ℝ)^p.1)) (scaledCutoff W ((2:ℝ)^p.2))
          c (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t-
          selectedPart .central L J N P (scaledCutoff W ((2:ℝ)^p.1)) (scaledCutoff W ((2:ℝ)^p.2))
            c
            (PRZZSameMaskResidual.keep T ((2:ℝ)^p.1) eps) (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t))‖ ≤ (Ct+Cb)*T^(-(power+1)) := by
    have hq : ((2:ℝ)^p.1) ≤ 2*T := by
      have hx : p.1 ≤ Nat.log 2 N+1 := by have := (mem_range.mp (mem_product.mp hp).1); omega
      have hpow : (2:ℝ)^(Nat.log 2 N) ≤ N := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      calc
        _ ≤ (2:ℝ)^(Nat.log 2 N+1) := pow_le_pow_right₀ (by norm_num) hx
        _ = 2*(2:ℝ)^(Nat.log 2 N) := by rw [pow_succ]; ring
        _ ≤ 2*T := by linarith
    have h1 := ht c L N dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B hcoef hN hNT (by positivity) htime hA hB hsep
    have h2 := (PRZZCappedSameMask.band_dominated P W W c L N J dual T
      ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps eH t A B hT
      (by positivity) hq).trans (hb c L N J dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) t A B
        hcoef hN hNT (by positivity) htime hA hB hsep hJ)
    rw [← PRZZCappedStrictTail.local_identification P W W c L N dual T _ _ eps eH t A B] at h1
    rw [mul_add]
    exact (norm_add_le _ _).trans ((add_le_add h1
      (by simpa only [PRZZCappedSameMask.bandField,mul_sub,norm_sub_rev] using h2)).trans_eq (by ring))
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

theorem tailBand_time (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eH : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c : ℕ → ℂ) (L J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → 1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖paired (tailBand P P (Nat.log 2 N+2) L J N c T eps)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,hC,h⟩ := tailBand_uniform P hP hl hright Hcap hHcap S r eps eH 2 hS hr heps heps1 he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c L J N A B hcoef hN hNT hL hJ hA hB hsep
  have hi : IntegrableOn (fun t => C*T^(-2:ℝ)*‖scaledCutoff Phi T t‖) (Icc T (2*T)) :=
    (continuous_const.mul (hPhi.comp (continuous_const.mul continuous_id)).norm).integrableOn_Icc
  have hh (dual : Bool) (u v : ℂ) (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) (hs : r ≤ ‖u+v‖) :
      ‖∫ t in Icc T (2*T), scaledCutoff Phi T t*(PRZZResolvedTailMass.branch dual u v T t*
        tailBand P P (Nat.log 2 N+2) L J N c T eps
          (u/(Real.log T:ℂ)) (v/(Real.log T:ℂ)) t)‖ ≤
      C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h c L J N dual u v t hcoef hN hNT hL hJ hu hv hs ht)
      (norm_nonneg _)).trans_eq (by ring)
  have hs' : r ≤ ‖-B+-A‖ := by
    simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have hd := hh true (-B) (-A) (by simpa using hB) (by simpa using hA) hs'
  have hp := hh false A B hA hB hsep
  simp only [PRZZResolvedTailMass.branch,Bool.false_eq_true,if_false,one_mul] at hp
  simp only [PRZZResolvedTailMass.branch,if_true,neg_neg,neg_div,mul_assoc] at hd
  unfold paired
  simp only [mul_assoc]
  simp only [scaledCutoff,inv_mul_eq_div] at hp hd ⊢
  apply (norm_add_le _ _).trans
  calc
    _ ≤ C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖)+
        C*(T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖)) := add_le_add hp hd
    _ = _ := by ring

theorem mixed_tailBand_time (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eH : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (L J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun a => paired
        (tailBand P P (Nat.log 2 N+2) L J N a T eps) Phi T
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤
        C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,hC,h⟩ := tailBand_time P Phi hP hl hright hPhi (2*Hcap) (by positivity)
    S r eps eH hS hr heps heps1 he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro c d L J N A B hc hd hN hNT hL hJ hA hB hsep
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact h _ L J N A B (PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hd z hz)
    hN hNT hL hJ hA hB hsep

theorem mixed_remainder_split (P F Phi : ℝ → ℂ) (K L J N : ℕ) (c d : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZMixedPoisson.lift (fun a => remainderPair P F Phi K L J N a T eps alpha beta) c d =
      PRZZMixedPoisson.lift (fun a => paired (tailBand P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (freezing P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (discarded P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (largeField F L J N a T) Phi T alpha beta) c d := by
  have he (a : ℕ → ℂ) := remainder_split P F Phi K L J N a T eps alpha beta
    hF hl hr hPhi hsPhi hT ha hb hs
  simp only [PRZZMixedPoisson.lift,he]
  ring

/-- Return the exact mixed residual decomposition to the actual moment.
No bound for discarded or large-spatial pieces is inferred by this equality. -/
theorem original_moment_split (P F Phi : ℝ → ℂ) (K L J N : ℕ) (c d : ℕ → ℂ)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) (hF : ContDiff ℝ ∞ F)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-
      PRZZMixedPoisson.lift (fun a => PRZZSmallCentralLiteral.literalModel P F Phi K L J N a T eps alpha beta) c d =
    (PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-
      PRZZMixedPoisson.model L J N F c d alpha beta T (scaledCutoff Phi T))+
      PRZZMixedPoisson.lift (fun a => paired (tailBand P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (freezing P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (discarded P F K L J N a T eps) Phi T alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => paired (largeField F L J N a T) Phi T alpha beta) c d := by
  have he (a : ℕ → ℂ) := PRZZSmallCentralLiteral.original_error_literal P F Phi K L J N a
    hPl hPr hK hF hFl hFr hPhi hsPhi T eps hT alpha beta ha hb hs
  have hm (a : ℕ → ℂ) : PRZZAllPoissonAFE.model L J N F a alpha beta T (scaledCutoff Phi T) =
      PRZZSmallCentralLiteral.literalModel P F Phi K L J N a T eps alpha beta+
        remainderPair P F Phi K L J N a T eps alpha beta := by linear_combination he a
  have hp := mixed_remainder_split P F Phi K L J N c d T eps alpha beta hF hFl hFr hPhi hsPhi hT ha hb hs
  unfold PRZZMixedPoisson.model
  simp only [PRZZMixedPoisson.lift,hm] at hp ⊢
  linear_combination hp

theorem mixed_tailBand_target (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eH delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (he : eps < eH) (hdelta : 0 ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (L J N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) →
      1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.lift (fun a => paired
        (tailBand P P (Nat.log 2 N+2) L J N a T eps) Phi T
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := mixed_tailBand_time P Phi hP hl hright hPhi Hcap hHcap S r eps eH
    hS hr heps heps1 he
  obtain ⟨U,hU,hu⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨C*U,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro c d L J N A B hc hd hN hNT hL hJ hA hB hsep
  have ht : 0 < T := by linarith
  apply (h c d L J N A B hc hd hN hNT hL hJ hA hB hsep).trans
  exact (mul_le_mul_of_nonneg_left (hu T ht).2 (by positivity)).trans
    (PRZZRemainderAbsorption.small_error_absorb C U T delta N hC.le hU.le hT hdelta hN)

#print axioms mixed_tailBand_target
#print axioms mixed_tailBand_time
#print axioms mixed_remainder_split
#print axioms original_moment_split
#print axioms tailBand_uniform
#print axioms tailBand_time
end XiPrime8845.PRZZCappedTailBand

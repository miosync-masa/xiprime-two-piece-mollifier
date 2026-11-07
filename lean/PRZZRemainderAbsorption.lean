import PRZZRemainderBudget

/-! Insert actual analytic suppliers into the original remainderPair.
Constants precede height, all exhaustion parameters and the bounded
separated logarithmic shift family. No component estimate is a premise. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZRemainderAbsorption
open PRZZMellinSeparation PRZZReconstructedAFE PRZZRemainderBudget
set_option maxHeartbeats 12000000

theorem tailBand_time (P Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hright : ∀ x, 1 ≤ x → P x = 0) (hPhi : Continuous Phi)
    (js : List ℕ) (S r eps eH : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1) (he : eps < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖paired (tailBand P P (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps)
        Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
        C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,hC,h⟩ := tailBand_uniform P hP hl hright js S r eps eH 2 hS hr heps heps1 he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro L J N A B hN hNT hL hJ hA hB hsep
  have hi : IntegrableOn (fun t => C*T^(-2:ℝ)*‖scaledCutoff Phi T t‖) (Icc T (2*T)) :=
    (continuous_const.mul (hPhi.comp (continuous_const.mul continuous_id)).norm).integrableOn_Icc
  have hh (dual : Bool) (u v : ℂ) (hu : ‖u‖ ≤ S) (hv : ‖v‖ ≤ S) (hs : r ≤ ‖u+v‖) :
      ‖∫ t in Icc T (2*T), scaledCutoff Phi T t*(PRZZResolvedTailMass.branch dual u v T t*
        tailBand P P (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (u/(Real.log T:ℂ)) (v/(Real.log T:ℂ)) t)‖ ≤
      C*T^(-2:ℝ)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h L J N dual u v t hN hNT hL hJ hu hv hs ht)
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

theorem small_error_absorb (C U T delta : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hT : 1 ≤ T) (hd : 0 ≤ delta) (hN : 1 ≤ N) :
    C*T^(-2:ℝ)*(U*T) ≤ C*U*T^delta*PRZZOptimalPowers.target N T := by
  have hT0 : 0 < T := by linarith
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ = C*U*T^(-1:ℝ) := by
      rw [show C*T^(-2:ℝ)*(U*T) = C*U*(T^(-2:ℝ)*T^(1:ℝ)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT0]; norm_num
    _ ≤ C*U*T^delta := by gcongr; linarith
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

/-- Direct sharp bound for the original reconstructed remainder. The
common cutoff and sufficient original exhaustion are retained explicitly.
Both Gamma branches and all actual arithmetic profile values are present. -/
theorem remainderPair_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖remainderPair (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) L J N
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  obtain ⟨hw,hcw,hsw⟩ := PRZZWRowLimit.profile_regular F hP hFl hFr
  let W := PRZZWRowLimit.profile F
  obtain ⟨Ct,hCt,htail⟩ := tailBand_time F Phi hP hFl hFr hPhi.continuous js S r eps eH hS hr heps.le heps1 he
  obtain ⟨Cf,hCf,hfreeze⟩ := PRZZSameMaskFreezeBudget.partition_bound F W W hP hFl hFr
    hw.continuous hw.continuous hcw hcw hsw hsw js S r eps eta delta hS hr heps.le heps1 heta heta1 hmargin
  obtain ⟨Cd,hCd,hdiscard⟩ := PRZZSelectedDiscardedFamily.discarded_absorbed Phi P hPhi hcPhi hsPhi
    hP hm hlo hhi hl hright js S r eps 0 hS hr heps heps1.le
  obtain ⟨Cl,hCl,hlarge⟩ := PRZZSpatialErrorJoin.large_time P hm hlo hhi hl hright hP js S r hS hr
  obtain ⟨U,hU,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi.continuous hcPhi
  refine ⟨(Ct+Cf+2*Cl)*U+Cd,by positivity,?_⟩
  filter_upwards [htail,hfreeze,hdiscard,hlarge,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T ht hf hd hlg hsmall hT
  intro L J N A B hN hscale hL hJ hA hB hsep
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (4/7:ℝ) ≤ 1))
  have hdelta : 0 ≤ delta := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  let a : ℕ → ℂ := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  have h1 := ht L J N A B hN hNT hL hJ hA hB hsep
  have h1' : ‖paired (tailBand F F (Nat.log 2 N+2) L J N a T eps) Phi T alpha beta‖ ≤
      Ct*U*T^delta*PRZZOptimalPowers.target N T :=
    h1.trans ((mul_le_mul_of_nonneg_left (hcut T hT0).2 (by positivity)).trans
      (small_error_absorb Ct U T delta N hCt.le hU.le hT1 hdelta hN))
  have h2 := hf L J N A B (fun t => Phi (t/T)) U hN hscale hA hB hsep
    (hPhi.continuous.comp (continuous_id.div_const T)) hU.le
    (fun t ht => by simpa only [scaledCutoff,inv_mul_eq_div] using (hcut T hT0).1 t)
  have heq := freezing_pair_eq F F Phi (Nat.log 2 N+2) L J N js T eps alpha beta hT0 hs
    (hsmall.2 A hA) (hsmall.2 B hB) hPhi.continuous
  have h2' : ‖paired (freezing F F (Nat.log 2 N+2) L J N a T eps) Phi T alpha beta‖ ≤
      Cf*U*T^delta*PRZZOptimalPowers.target N T := by
    rw [heq]
    exact (norm_sum_le _ _).trans h2
  have h3 := hd L J N A B hN hNT hA hB hsep
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have h3' : ‖paired (discarded F F (Nat.log 2 N+2) L J N a T eps) Phi T alpha beta‖ ≤
      Cd*T^delta*PRZZOptimalPowers.target N T := by
    have hpow := Real.one_le_rpow hT1 hdelta
    apply le_trans (show ‖paired (discarded F F (Nat.log 2 N+2) L J N a T eps) Phi T alpha beta‖ ≤ Cd by
      simpa only [paired,scaledCutoff,inv_mul_eq_div,neg_zero,Real.rpow_zero,mul_one] using h3)
    exact (le_mul_of_one_le_right hCd.le hpow).trans
      (le_mul_of_one_le_right (by positivity) htarg)
  have hs' : r ≤ ‖-B+-A‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have hp := hlg L J N false A B (scaledCutoff Phi T) hN hNT hA hB hsep
    (hPhi.continuous.comp (continuous_const.mul continuous_id))
  have hq := hlg L J N true (-B) (-A) (scaledCutoff Phi T) hN hNT
    (by simpa using hB) (by simpa using hA) hs'
    (hPhi.continuous.comp (continuous_const.mul continuous_id))
  have h4 : ‖paired (largeField F L J N a T) Phi T alpha beta‖ ≤
      (2*Cl)*U*T^delta*PRZZOptimalPowers.target N T := by
    have heq : paired (largeField F L J N a T) Phi T alpha beta =
        PRZZSpatialErrorJoin.large P js L J N false T A B (scaledCutoff Phi T)+
        PRZZSpatialErrorJoin.large P js L J N true T (-B) (-A) (scaledCutoff Phi T) := by
      simp only [paired,largeField,PRZZSpatialErrorJoin.large,PRZZResolvedTailMass.branch,
        Bool.false_eq_true,if_false,if_true,neg_neg,mul_one,scaledCutoff,inv_mul_eq_div,neg_div]
      rfl
    rw [heq]
    apply (norm_add_le _ _).trans
    have hh := small_error_absorb Cl U T delta N hCl.le hU.le hT1 hdelta hN
    have hp' := hp.trans ((mul_le_mul_of_nonneg_left (hcut T hT0).2 (by positivity)).trans hh)
    have hq' := hq.trans ((mul_le_mul_of_nonneg_left (hcut T hT0).2 (by positivity)).trans hh)
    exact (add_le_add hp' hq').trans_eq (by ring)
  rw [remainder_split F F Phi _ L J N a T eps alpha beta hP hFl hFr hPhi.continuous hsPhi hT0
    (hsmall.2 A hA) (hsmall.2 B hB) hs]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1' h2')) h3')) h4)).trans_eq (by ring)

theorem original_error_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        PRZZSmallCentralLiteral.literalModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
          (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤
      ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        PRZZAllPoissonAFE.model L J N (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)‖+
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := remainderPair_bound P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
    js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro L J N A B hN hscale hL hJ hA hB hsep
  have hT0 : 0 < T := by linarith
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  rw [PRZZSmallCentralLiteral.original_error_literal F F Phi _ L J N _
    hFl hFr (PRZZArithmeticCutoffPartition.dyadic_scale_count N) hP hFl hFr
    hPhi.continuous hsPhi T eps hT0 _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (h L J N A B hN hscale hL hJ hA hB hsep))

#print axioms original_error_bound

#print axioms tailBand_time
#print axioms small_error_absorb
#print axioms remainderPair_bound
end XiPrime8845.PRZZRemainderAbsorption


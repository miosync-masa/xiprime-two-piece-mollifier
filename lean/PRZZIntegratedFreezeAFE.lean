import PRZZNativeFreezeTime

/-! Remove exactly the actual freezing field from the retained AFE model,
then put back its finite row integrals on both branches. All other native
components, the cutoff complement, zeroPair, gammaDefect and the original
AFE truncation error remain explicit. This is not full AFE closure. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZIntegratedFreezeAFE
open PRZZMellinSeparation PRZZNativeFreezeTime PRZZRetainedNative
set_option maxHeartbeats 10000000

def freezeField (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  selectedPart .freeze L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t

def withoutFreeze (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t-
    freezeField P G H js L J N T Q V eps alpha beta t

def freezeRows (P : ℝ → ℝ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  rows L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V) phi
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta T

/-- The untouched field is explicit, rather than an unidentified error. -/
theorem without_freeze_field (P : ℝ → ℝ) (G H : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) (t : ℝ) :
    withoutFreeze P G H js L J N T Q V eps alpha beta t =
      (PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t-
       PRZZAllPoissonRows.family L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t)+
      (selectedPart .central L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
       selectedPart .tail L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t-
       selectedPart .boundary L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t+
       selectedPart .outside L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta t) := by
  unfold withoutFreeze freezeField
  rw [kept_decomposition]
  ring

theorem kept_time_split (P : ℝ → ℝ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Icc T (2*T))) :
    (∫ t in Icc T (2*T), phi t*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t) =
      (∫ t in Icc T (2*T), phi t*withoutFreeze P G H js L J N T Q V eps alpha beta t)+
        freezeRows P G H phi js L J N T Q V eps alpha beta := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hr (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  have hf := PRZZPrunedAFEError.field_continuous L J N (fun x => (P x:ℂ))
    hP hl hr (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta hs T hT
  have hd := PRZZPrunedAFEError.selected_continuous L J N (fun x => (P x:ℂ))
    (scaledCutoff G Q) (scaledCutoff H V) hP hl hr
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (PRZZSourceMaskFamily.discarded T Q eps) alpha beta hs T hT
  have hk : ContinuousOn (PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta)
      (Icc T (2*T)) := hf.sub hd
  have hz : ContinuousOn (freezeField P G H js L J N T Q V eps alpha beta) (Icc T (2*T)) :=
    selected_continuous L J N _ _ _ _ _ alpha beta T hT hs
  have hi : IntegrableOn (fun t => phi t*PRZZPrunedAFEError.keptField P G H js L J N T Q V eps alpha beta t)
      (Icc T (2*T)) := (hphi.mul hk).integrableOn_compact isCompact_Icc
  have hj : IntegrableOn (fun t => phi t*freezeField P G H js L J N T Q V eps alpha beta t)
      (Icc T (2*T)) := (hphi.mul hz).integrableOn_compact isCompact_Icc
  have he := selected_time L J N (fun x => (P x:ℂ)) (scaledCutoff G Q) (scaledCutoff H V) phi
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (fun s z => ¬PRZZSourceMaskFamily.discarded T Q eps s z) alpha beta T hT hs hphi
  change (∫ t in Icc T (2*T), phi t*freezeField P G H js L J N T Q V eps alpha beta t) =
    freezeRows P G H phi js L J N T Q V eps alpha beta at he
  rw [← he]
  simp only [withoutFreeze,mul_sub]
  rw [integral_sub hi hj]
  ring

def freezePair (P : ℝ → ℝ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  freezeRows P G H phi js L J N T Q V eps alpha beta+
    freezeRows P G H (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t)
      js L J N T Q V eps (-beta) (-alpha)

def withoutFreezeModel (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    alpha beta T (scaledCutoff F T)+
    (((∫ t in Icc T (2*T), scaledCutoff F T t*withoutFreeze P G H js L J N T Q V eps alpha beta t)+
      ∫ t in Icc T (2*T), (scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)*
        withoutFreeze P G H js L J N T Q V eps (-beta) (-alpha) t)-
      PRZZZeroCoupled.zeroPair N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff F T))+
    ∫ t in Icc T (2*T), scaledCutoff F T t*
      PRZZZeroCross.gammaDefect N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t

theorem freeze_pair_charge (P : ℝ → ℝ) (G H phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0)
    (hphi : ContinuousOn phi (Icc T (2*T))) :
    ‖freezePair P G H phi js L J N T Q V eps alpha beta‖ ≤
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
        G H phi js T 1 Q V eps alpha beta+
      PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
        G H (fun t => phi t*PRZZAFEDual.dualMultiplier alpha beta t) js
        T 1 Q V eps (-beta) (-alpha) := by
  have hs' : -beta+-alpha ≠ 0 := by rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  have hdual := hphi.mul hg.continuousOn
  have he (alpha beta : ℂ) (hs : alpha+beta ≠ 0) (phi : ℝ → ℂ)
      (hp : ContinuousOn phi (Icc T (2*T))) :
      ‖freezeRows P G H phi js L J N T Q V eps alpha beta‖ ≤
        PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
          G H phi js T 1 Q V eps alpha beta := by
    unfold freezeRows
    rw [← selected_time L J N (fun x => (P x:ℂ)) _ _ phi _ _ alpha beta T hT hs hp]
    exact retained_charge L J N (fun x => (P x:ℂ)) G H phi js T Q V eps alpha beta hT hs hp
  exact (norm_add_le _ _).trans (add_le_add (he alpha beta hs phi hphi)
    (he (-beta) (-alpha) hs' _ hdual))

theorem model_split (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Continuous F) (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZPrunedAFEError.model F G H P js L J N T Q V eps alpha beta =
      withoutFreezeModel F G H P js L J N T Q V eps alpha beta+
        freezePair P G H (scaledCutoff F T) js L J N T Q V eps alpha beta := by
  have hc : Continuous (scaledCutoff F T) := hF.comp (continuous_const.mul continuous_id)
  have hg := (PRZZDualSmooth.multiplier_contDiff alpha beta ha hb).continuous
  have hs' : -beta+-alpha ≠ 0 := by rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := kept_time_split P G H (scaledCutoff F T) js L J N hP hleft hright
    T Q V eps hT alpha beta hs hc.continuousOn
  have h2 := kept_time_split P G H (fun t => scaledCutoff F T t*PRZZAFEDual.dualMultiplier alpha beta t)
    js L J N hP hleft hright T Q V eps hT (-beta) (-alpha) hs' (hc.mul hg).continuousOn
  unfold PRZZPrunedAFEError.model withoutFreezeModel freezePair
  rw [h1,h2]
  ring

theorem original_error_eq (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hF : Continuous F) (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      alpha beta T (scaledCutoff F T)-withoutFreezeModel F G H P js L J N T Q V eps alpha beta =
      (PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff F T)-PRZZAllPoissonAFE.model L J N
          (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff F T))+
        PRZZDiscardedTimePair.pair F G H P js L J N T Q V eps alpha beta+
        freezePair P G H (scaledCutoff F T) js L J N T Q V eps alpha beta := by
  have h1 := PRZZPrunedAFEError.all_model_error_eq F G H P js L J N hF hP hleft hright
    T Q V eps hT alpha beta ha hb hs
  rw [model_split F G H P js L J N hF hP hleft hright T Q V eps hT alpha beta ha hb hs] at h1
  linear_combination h1

/-- The exact two-branch row correction in original_error_eq satisfies
the sharp common budget, summed over all arithmetic windows, uniformly
in both truncations. The original Gamma multiplier stays in the weight. -/
theorem partition_bound (P : ℝ → ℝ) (G H : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) (hsH : Function.support H ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (L J N : ℕ) (A B : ℂ) (phi : ℝ → ℂ) (U : ℝ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → 0 ≤ U → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ U) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ‖freezePair P G H phi js L J N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖) ≤
        C*U*T^delta*PRZZOptimalPowers.target N T := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (P x:ℂ) = 1 := by simp [hleft x hx]
  have hh (x : ℝ) (hx : 1 ≤ x) : (P x:ℂ) = 0 := by simp [hright x hx]
  obtain ⟨hf,hcf,hsf⟩ := PRZZWRowLimit.profile_regular _ hP hl hh
  let W := PRZZWRowLimit.profile (fun x => (P x:ℂ))
  obtain ⟨Cf,hCf,hfbound⟩ := PRZZFullFreezeBudget.partition_bound W G H hf hcf hsf
    hG hH hcG hcH hsG hsH js S r eps eta delta hS hr heps heta heta1 hmargin
  obtain ⟨Cd,hCd,hdbound⟩ := PRZZDualNativeFreeze.partition_bound W G H hf hcf hsf
    hG hH hcG hcH hsG hsH js S r eps eta delta hS hr heps heps1 heta heta1 hmargin
  refine ⟨Cf+Cd,by positivity,?_⟩
  filter_upwards [hdbound,PRZZRejectedExhaustion.height_eventually eps heps1,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (max 1 (2*S/eta))),
    Filter.eventually_ge_atTop (1:ℝ)] with T hd hheight hsmall hlog hT
  intro L J N A B phi U hN hscale hA hB hsep hphi hU hcap
  have hT0 : 0 < T := by linarith
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (ne_of_gt (show 0 < Real.log T by linarith [le_max_left 1 (2*S/eta)])))
  have hprimal := hfbound L J N (L+2) T 1 0 A B phi U hA hB hsep hN hT
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hscale hheight.2
    (by norm_num) hphi hU hcap
  have hdual := hd L J N (L+2) 1 A B phi U hN hscale (by norm_num) hA hB hsep hphi hU hcap
  calc
    _ ≤ ∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        (PRZZFullFreezeBudget.fullMass L J W phi js N (L+2) T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2)
          eps 0 G H (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))+
         PRZZNativeFreezeEnvelope.charge L J N (L+2) W G H (PRZZDualNativeFreeze.weight phi T A B)
          js T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))) := by
      apply sum_le_sum; intro p hp
      apply (freeze_pair_charge P G H phi js L J N T _ _ eps hT0 _ _
        (hsmall.2 A hA) (hsmall.2 B hB) hs hphi.continuousOn).trans
      apply add_le_add
      · simpa only [add_div] using PRZZNativeFreezeEnvelope.dominates L J N (L+2) W G H phi js
          T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps 0 _ _ hf hsf hsG hT0 (by norm_num)
          (by positivity) hs hheight.2
      · simp only [neg_div]; exact le_rfl
    _ ≤ _ := by
      rw [sum_add_distrib]
      exact (add_le_add hprimal hdual).trans_eq (by ring)

#print axioms kept_time_split
#print axioms without_freeze_field
#print axioms freeze_pair_charge
#print axioms model_split
#print axioms original_error_eq
#print axioms partition_bound
end XiPrime8845.PRZZIntegratedFreezeAFE

import PRZZFreezeRemovedLiteral

/-! Both genuine AFE branches with their literal A* central expressions.
All remaining fields are joined in one exact original-error identity.
The displayed residual is not claimed negligible: it retains native
rejection (inside literalCentral), the local-cutoff transfer and the
collective spatial complement until their joint estimates are supplied. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZLiteralAFEJoin
open PRZZMellinSeparation PRZZFreezeRemovedLiteral PRZZIntegratedFreezeAFE
set_option maxHeartbeats 2000000

def remainingPair (P : ℝ → ℝ) (G H Phi : ℝ → ℂ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  (∫ t in Icc T (2*T), Phi (t/T)*remainingField P G H js L J N T Q V eps alpha beta t)+
    ∫ t in Icc T (2*T), (Phi (t/T)*PRZZAFEDual.dualMultiplier alpha beta t)*
      remainingField P G H js L J N T Q V eps (-beta) (-alpha) t

def literalModel (Phi G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (T Q V eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZCoupledAFE.diagonalMain N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    alpha beta T (scaledCutoff Phi T)+
    ((literalCentral P G H Phi js L J N T Q V eps alpha beta+
      literalCentral P G H (PRZZKeptLiteral.dualProfile Phi T alpha beta) js L J N T Q V eps (-beta) (-alpha))-
      PRZZZeroCoupled.zeroPair N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff Phi T))+
    ∫ t in Icc T (2*T), scaledCutoff Phi T t*
      PRZZZeroCross.gammaDefect N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta t

theorem model_split (Phi G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    withoutFreezeModel Phi G H P js L J N T Q V eps alpha beta =
      literalModel Phi G H P js L J N T Q V eps alpha beta+
        remainingPair P G H Phi js L J N T Q V eps alpha beta := by
  have hd := PRZZKeptLiteral.dual_profile_regular Phi hPhi hsPhi T alpha beta ha hb
  have hs' : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs
  have h1 := without_time P G H Phi js L J N hP hleft hright hPhi hsPhi T Q V eps hT alpha beta hs
  have h2 := without_time P G H (PRZZKeptLiteral.dualProfile Phi T alpha beta) js L J N
    hP hleft hright hd.1 hd.2 T Q V eps hT (-beta) (-alpha) hs'
  simp_rw [PRZZKeptLiteral.dual_profile_time Phi T hT alpha beta] at h2
  have he : scaledCutoff Phi T = fun t => Phi (t/T) := by
    funext t; simp [scaledCutoff,div_eq_mul_inv,mul_comm]
  unfold withoutFreezeModel literalModel remainingPair
  simp_rw [he]
  rw [h1,h2]
  ring

/-- Direct substitution into the original AFE error, not an assumed
representation of the moment or an assumed residual estimate. -/
theorem original_error_eq (Phi G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      alpha beta T (scaledCutoff Phi T)-literalModel Phi G H P js L J N T Q V eps alpha beta =
      (PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff Phi T)-PRZZAllPoissonAFE.model L J N
          (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff Phi T))+
        PRZZDiscardedTimePair.pair Phi G H P js L J N T Q V eps alpha beta+
        freezePair P G H (scaledCutoff Phi T) js L J N T Q V eps alpha beta+
        remainingPair P G H Phi js L J N T Q V eps alpha beta := by
  have he := PRZZIntegratedFreezeAFE.original_error_eq Phi G H P js L J N hPhi hP hleft hright
    T Q V eps hT alpha beta ha hb hs
  rw [model_split Phi G H P js L J N hP hleft hright hPhi hsPhi T Q V eps hT alpha beta ha hb hs] at he
  linear_combination he

/-- All identified errors merge by the triangle inequality. The actual
remainingPair is retained, rather than replaced by a budget hypothesis. -/
theorem error_budget (Phi G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (L J N : ℕ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T Q V eps : ℝ) (hT : 0 < T) (alpha beta : ℂ)
    (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4) (hs : alpha+beta ≠ 0) :
    ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      alpha beta T (scaledCutoff Phi T)-literalModel Phi G H P js L J N T Q V eps alpha beta‖ ≤
      ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        alpha beta T (scaledCutoff Phi T)-PRZZAllPoissonAFE.model L J N
          (fun x => (P x:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) alpha beta T (scaledCutoff Phi T)‖+
        ‖PRZZDiscardedTimePair.pair Phi G H P js L J N T Q V eps alpha beta‖+
        (PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
          G H (scaledCutoff Phi T) js T 1 Q V eps alpha beta+
         PRZZNativeFreezeEnvelope.charge L J N (L+2) (PRZZWRowLimit.profile (fun x => (P x:ℂ)))
          G H (fun t => scaledCutoff Phi T t*PRZZAFEDual.dualMultiplier alpha beta t)
          js T 1 Q V eps (-beta) (-alpha))+
        ‖remainingPair P G H Phi js L J N T Q V eps alpha beta‖ := by
  rw [original_error_eq Phi G H P js L J N hP hleft hright hPhi hsPhi T Q V eps hT alpha beta ha hb hs]
  have hc := PRZZIntegratedFreezeAFE.freeze_pair_charge P G H (scaledCutoff Phi T) js L J N
    T Q V eps hT alpha beta ha hb hs (hPhi.comp (continuous_const.mul continuous_id)).continuousOn
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) hc)

set_option maxHeartbeats 6000000

/-- The original AFE error, discarded pair and actual two-branch freezing
correction are all absorbed. Only the explicit remainingPair is removed
on the left; this is not a bound on that still unresolved field. -/
theorem scaled_join_eventually (Phi G H : ℝ → ℂ) (P : ℝ → ℝ)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3) (hsH : Function.support H ⊆ Icc (1/2:ℝ) 3)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 < eps) (heps1 : eps < 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      ∀ p ∈ Finset.range (Nat.log 2 N+2) ×ˢ Finset.range (Nat.log 2 N+2),
      ∀ J : ℕ → ℕ, ∀ᶠ L : ℕ in Filter.atTop,
      ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        literalModel Phi G H P js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))-
        remainingPair P G H Phi js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  have hd : 0 < delta := by nlinarith
  obtain ⟨Ce,hCe,he⟩ := PRZZPrunedAFEError.scaled_error_eventually Phi G H P hPhi hcPhi hsPhi
    hG hH hcG hcH hsG hP hm hlo hhi hleft hright js S r eps delta hS hr heps heps1.le hd
  obtain ⟨Cf,hCf,hf⟩ := PRZZIntegratedFreezeAFE.partition_bound P G H hP hleft hright
    hG hH hcG hcH hsG hsH js S r eps eta delta hS hr heps.le heps1 heta heta1 hmargin
  obtain ⟨U,hU,hcap⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi.continuous hcPhi
  refine ⟨Ce+Cf*U,by positivity,?_⟩
  filter_upwards [he,hf,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    Filter.eventually_ge_atTop (2:ℝ)] with T he hf hsmall hT
  intro A B hA hB hsep N hN hscale p hp J
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ T by linarith) (by norm_num : (4/7:ℝ) ≤ 1))
  have hphi : Continuous (scaledCutoff Phi T) := hPhi.continuous.comp (continuous_const.mul continuous_id)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  filter_upwards [he A B hA hB hsep N hN hNT ((2:ℝ)^p.1) ((2:ℝ)^p.2) (by positivity) J] with L hL
  have hf' := hf L (J L) N A B (scaledCutoff Phi T) U hN hscale hA hB hsep hphi hU.le
    (fun t _ => (hcap T hT0).1 t)
  have hfp : ‖freezePair P G H (scaledCutoff Phi T) js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ Cf*U*T^delta*PRZZOptimalPowers.target N T :=
    (Finset.single_le_sum (f := fun q : ℕ × ℕ =>
      ‖freezePair P G H (scaledCutoff Phi T) js L (J L) N T ((2:ℝ)^q.1) ((2:ℝ)^q.2) eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖) (fun q hq => norm_nonneg _) hp).trans hf'
  have hm := PRZZIntegratedFreezeAFE.model_split Phi G H P js L (J L) N hPhi.continuous hP hleft hright
    T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps hT0 _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs
  rw [model_split Phi G H P js L (J L) N hP hleft hright hPhi.continuous hsPhi
    T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps hT0 _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs] at hm
  have heq : PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        literalModel Phi G H P js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))-
        remainingPair P G H Phi js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
      (PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        PRZZPrunedAFEError.model Phi G H P js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))+
        freezePair P G H (scaledCutoff Phi T) js L (J L) N T ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) := by
    rw [hm]
    exact (show ∀ x c r f : ℂ, x-c-r = x-(c+r+f)+f by intros; ring) _ _ _ _
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hL hfp).trans_eq (by ring))

#print axioms model_split
#print axioms original_error_eq
#print axioms error_budget
#print axioms scaled_join_eventually
end XiPrime8845.PRZZLiteralAFEJoin

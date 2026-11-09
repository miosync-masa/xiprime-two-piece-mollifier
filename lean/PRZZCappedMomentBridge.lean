import PRZZCappedRemainder
import PRZZMixedMoment
import PRZZLiteralFourierLimit

/-! Actual mixed AFE replacement and reconstructed residual combined.
Both exhaustion limits are proved, not inferred from boundedness. The
remaining complete central arithmetic model is retained explicitly. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set MeasureTheory Filter
namespace XiPrime8845.PRZZCappedMomentBridge
open PRZZMellinSeparation PRZZMixedPoisson
set_option maxHeartbeats 12000000

def literalError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (c d : ℕ → ℂ)
    (L J N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
    PRZZMixedPoisson.lift (fun a => PRZZSmallCentralLiteral.literalModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
      Phi (Nat.log 2 N+2) L J N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d

def limitError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (c d : ℕ → ℂ)
    (J N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
    PRZZMixedPoisson.lift (fun a => PRZZLiteralExhaustion.limitModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
      Phi (Nat.log 2 N+2) J N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d

theorem eventually_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (H : ℝ) (hH : 0 ≤ H) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ J : ℕ → ℕ, (∀ᶠ L : ℕ in atTop, PRZZCompatibleTail.commonCutoff N T eH ≤ J L) →
      ∀ᶠ L : ℕ in atTop, ‖literalError P Phi c d L (J L) N T eps A B‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hdelta : 0 < delta := by linarith
  obtain ⟨Ca,hCa,hafe⟩ := scaled_error_limit F hP hFl hFr S r delta H hS hr hdelta hH
  obtain ⟨Cr,hCr,hrem⟩ := PRZZCappedRemainder.remainderPair_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi H hH S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨U,hU,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi.continuous hcPhi
  refine ⟨Ca*U+Cr+1,by positivity,?_⟩
  filter_upwards [hafe,hrem,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T ha hrm hsmall hT
  intro c d N A B hc hd hN hscale hA hB hsep J hJ
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (4/7:ℝ) ≤ 1))
  obtain ⟨E,hlim,hE⟩ := ha A B hA hB hsep c d N hN hNT hc hd (scaledCutoff Phi T) U
    (hPhi.continuous.comp (continuous_const.mul continuous_id)) hU.le
    (fun t ht => (hcut T hT0).1 t) J
  have hclose := hlim.norm.eventually (eventually_lt_nhds (show ‖E‖ < ‖E‖+1 by linarith))
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbudget : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT1 hdelta.le) htarg
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  filter_upwards [hclose,hJ,eventually_ge_atTop ⌈4*(N:ℝ)*T^(4:ℝ)⌉₊] with L hclose hJ hL
  have hLR : 4*(N:ℝ)*T^(4:ℝ) ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have hb := hrm c d L (J L) N A B hc hd hN hscale hLR hJ hA hB hsep
  have hid := PRZZCappedRemainder.original_moment_residual F F Phi _ L (J L) N c d
    hFl hFr (PRZZArithmeticCutoffPartition.dyadic_scale_count N) hP hFl hFr hPhi.continuous hsPhi
    T eps hT0 _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs
  have heq : literalError P Phi c d L (J L) N T eps A B =
      (moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
        model L (J L) N F c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T))+
      PRZZMixedPoisson.lift (fun a => PRZZReconstructedAFE.remainderPair F F Phi (Nat.log 2 N+2) L (J L) N a
        T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d := by
    dsimp only [literalError,F] at hid ⊢
    linear_combination hid
  rw [heq]
  apply (norm_add_le _ _).trans
  exact (add_le_add hclose.le hb).trans (by nlinarith only [hE,hbudget])

theorem lift_tendsto {ι : Type*} {l : Filter ι} (Q : ι → (ℕ → ℂ) → ℂ)
    (R : (ℕ → ℂ) → ℂ) (c d : ℕ → ℂ)
    (h : ∀ a, Tendsto (fun x => Q x a) l (𝓝 (R a))) :
    Tendsto (fun x => PRZZMixedPoisson.lift (Q x) c d) l (𝓝 (PRZZMixedPoisson.lift R c d)) := by
  unfold PRZZMixedPoisson.lift
  exact ((((h _).sub (h _)).add ((h _).const_mul I)).sub ((h _).const_mul I)).div_const (4:ℂ)

theorem limit_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (H : ℝ) (hH : 0 ≤ H) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N J : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      Tendsto (fun L : ℕ => PRZZMixedPoisson.lift (fun a => PRZZSmallCentralLiteral.literalModel
        (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) L J N a T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d) atTop
        (𝓝 (PRZZMixedPoisson.lift (fun a => PRZZLiteralExhaustion.limitModel
          (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) J N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d)) ∧
      ‖limitError P Phi c d J N T eps A B‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := eventually_total_bound P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
    H hH S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hp := PRZZWRowLimit.profile_regular F hP hFl hFr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZRejectedExhaustion.height_eventually eps heps1] with T h hh
  intro c d N J A B hc hd hN hscale hA hB hsep hJ
  have he := PRZZLiteralExhaustion.model_eventually_eq F (Nat.log 2 N+2) N hp.2.2 T eps hh.1 hh.2
  refine ⟨lift_tendsto _ _ c d (fun a => PRZZLiteralExhaustion.model_tendsto F F Phi _ J N a
    hp.2.2 T eps hh.1 hh.2 _ _),?_⟩
  have hb := h c d N A B hc hd hN hscale hA hB hsep (fun _ => J)
    (Eventually.of_forall (fun _ => hJ))
  obtain ⟨L,hbL,heL⟩ := (hb.and he).exists
  dsimp only [F] at heL
  unfold literalError PRZZMixedPoisson.lift at hbL
  simp_rw [heL J (fun x => (P x:ℂ)) Phi] at hbL
  exact hbL

def fullError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (c d : ℕ → ℂ)
    (N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
    PRZZMixedPoisson.lift (fun a => PRZZLiteralFourierLimit.fullModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
      Phi (Nat.log 2 N+2) N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d

theorem full_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (H : ℝ) (hH : 0 ≤ H) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Tendsto (fun J : ℕ => PRZZMixedPoisson.lift (fun a => PRZZLiteralExhaustion.limitModel
        (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) J N a T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d) atTop
        (𝓝 (PRZZMixedPoisson.lift (fun a => PRZZLiteralFourierLimit.fullModel
          (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi (Nat.log 2 N+2) N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d)) ∧
      ‖fullError P Phi c d N T eps A B‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := limit_total_bound P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
    H hH S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro c d N A B hc hd hN hscale hA hB hsep
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  have hfull := lift_tendsto _ _ c d (fun a => PRZZLiteralFourierLimit.model_tendsto
    F F Phi (Nat.log 2 N+2) N a hP hFl hFr hPhi.continuous hsPhi T eps (by linarith)
      _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs)
  refine ⟨hfull,?_⟩
  have hn : Tendsto (fun J : ℕ => ‖limitError P Phi c d J N T eps A B‖) atTop
      (𝓝 ‖fullError P Phi c d N T eps A B‖) := (tendsto_const_nhds.sub hfull).norm
  by_contra hb
  have hbad := hn.eventually (eventually_gt_nhds (lt_of_not_ge hb))
  obtain ⟨J,hJ,hbadJ⟩ := ((eventually_ge_atTop (PRZZCompatibleTail.commonCutoff N T eH)).and hbad).exists
  exact (not_lt_of_ge (h c d N J A B hc hd hN hscale hA hB hsep hJ).2) hbadJ

#print axioms full_total_bound
#print axioms lift_tendsto
#print axioms limit_total_bound
#print axioms eventually_total_bound
end XiPrime8845.PRZZCappedMomentBridge

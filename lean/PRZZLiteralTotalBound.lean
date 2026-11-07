import PRZZRemainderAbsorption
import PRZZLiteralExhaustion

/-! Sharp total error after the original spatial exhaustion.
Varying Fourier cutoffs give an eventual uniform error estimate; a fixed
sufficiently large Fourier cutoff gives a proved literal-model limit.
Neither claim infers convergence merely from boundedness. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZLiteralTotalBound
open PRZZMellinSeparation
set_option maxHeartbeats 10000000

def literalError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (js : List ℕ)
    (L J N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
  PRZZSmallCentralLiteral.literalModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
    (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

def limitError (P : ℝ → ℝ) (Phi : ℝ → ℂ) (js : List ℕ)
    (J N : ℕ) (T eps : ℝ) (A B : ℂ) : ℂ :=
  PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
  PRZZLiteralExhaustion.limitModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
    (Nat.log 2 N+2) J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))

/-- C precedes T,N,shifts and the Fourier sequence. Only the exhaustion
threshold may depend on those data; no uniform threshold is claimed. -/
theorem eventually_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ J : ℕ → ℕ,
      (∀ᶠ L : ℕ in atTop, PRZZCompatibleTail.commonCutoff N T eH ≤ J L) →
      ∀ᶠ L : ℕ in atTop, ‖literalError P Phi js L (J L) N T eps A B‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hdelta : 0 < delta := by linarith
  obtain ⟨Ca,hCa,hafe⟩ := PRZZAllPoissonAFE.scaled_afe_limit F hP hFl hFr js S r delta hS hr hdelta
  obtain ⟨Cr,hCr,hrem⟩ := PRZZRemainderAbsorption.original_error_bound P Phi hP hm hlo hhi
    hl hright hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨U,hU,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi.continuous hcPhi
  refine ⟨Ca*U+Cr+1,by positivity,?_⟩
  filter_upwards [hafe,hrem,eventually_ge_atTop (2:ℝ)] with T ha hrm hT
  intro N A B hN hscale hA hB hsep J hJ
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (4/7:ℝ) ≤ 1))
  obtain ⟨E,hlim,hE⟩ := ha A B hA hB hsep N hN hNT (scaledCutoff Phi T) U
    (hPhi.continuous.comp (continuous_const.mul continuous_id)) hU.le
    (fun t ht => (hcut T hT0).1 t) J
  have hclose := hlim.norm.eventually (eventually_lt_nhds (show ‖E‖ < ‖E‖+1 by linarith))
  have htarget : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbudget : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hT1 hdelta.le) htarget
  filter_upwards [hclose,hJ,eventually_ge_atTop ⌈4*(N:ℝ)*T^(4:ℝ)⌉₊] with L hclose hJ hL
  have hLR : 4*(N:ℝ)*T^(4:ℝ) ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have hb := hrm L (J L) N A B hN hscale hLR hJ hA hB hsep
  change ‖literalError P Phi js L (J L) N T eps A B‖ ≤
    ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
      PRZZAllPoissonAFE.model L (J L) N F (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)‖+
      Cr*T^delta*PRZZOptimalPowers.target N T at hb
  change ‖PRZZExhaustiveAFEError.moment N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)-
      PRZZAllPoissonAFE.model L (J L) N F (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (scaledCutoff Phi T)‖ < ‖E‖+1 at hclose
  nlinarith only [hb,hclose,hE,hbudget]

/-- The spatially untruncated literal model is explicit and is genuinely
the L-limit for each fixed sufficiently large Fourier cutoff. Its error
has the sharp total budget, with no convergence hypothesis supplied. -/
theorem limit_total_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (N J : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) →
      PRZZCompatibleTail.commonCutoff N T eH ≤ J →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Tendsto (fun L : ℕ => PRZZSmallCentralLiteral.literalModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
        (Nat.log 2 N+2) L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) atTop
        (𝓝 (PRZZLiteralExhaustion.limitModel (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
          (Nat.log 2 N+2) J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))) ∧
      ‖limitError P Phi js J N T eps A B‖ ≤ C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := eventually_total_bound P Phi hP hm hlo hhi hl hright hPhi hcPhi hsPhi
    js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  have hp := PRZZWRowLimit.profile_regular F hP hFl hFr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZRejectedExhaustion.height_eventually eps heps1] with T h hheight
  intro N J A B hN hscale hJ hA hB hsep
  have he := PRZZLiteralExhaustion.model_eventually_eq F (Nat.log 2 N+2) N hp.2.2 T eps hheight.1 hheight.2
  refine ⟨PRZZLiteralExhaustion.model_tendsto F F Phi _ J N _ hp.2.2 T eps hheight.1 hheight.2 _ _,?_⟩
  have hb := h N A B hN hscale hA hB hsep (fun _ => J) (Eventually.of_forall (fun _ => hJ))
  obtain ⟨L,hbL,heL⟩ := (hb.and he).exists
  unfold literalError at hbL
  rw [heL J F Phi (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) _ _] at hbL
  exact hbL

#print axioms eventually_total_bound
#print axioms limit_total_bound
end XiPrime8845.PRZZLiteralTotalBound


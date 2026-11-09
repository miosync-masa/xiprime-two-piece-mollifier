import PRZZCappedMomentBridge
import PRZZCentralMainAssembly

/-! Evaluated Gamma-to-density main-kernel error for arbitrary capped slots.
The density orientation is d^beta e^alpha. The complete central correction
is explicit and is not declared bounded by the main-kernel comparison. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set MeasureTheory Filter
namespace XiPrime8845.PRZZCappedMainTerm
open PRZZCoefficientPolarization PRZZMellinSeparation
set_option maxHeartbeats 10000000

theorem mainterm_absorbed (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (H S r tau : ℝ) (hH : 0 ≤ H) (hS : 0 ≤ S) (hr : 0 < r) (htau : 0 < tau) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (fun t => (Phi (t/T):ℂ))) c d-
        arithmeticPairing N (densityGcdKernel T Phi A B) c d‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZKernelComparison.arithmetic_defect_bound Phi hPhi S r hS hr
  obtain ⟨D,hD,hd⟩ := PRZZOptimalOuter.power_log_absorbed 2 0 tau htau
  refine ⟨2*C*H^2*D+1,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hL
  intro c d N A B hc hdcoef hN hNT hA hB hsep
  have hb := h N A B c d H H hNT hA hB hsep hH hH hc hdcoef
  have heq : arithmeticPairing N (fun n m =>
      PRZZDiagonalKernel.diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
        (fun t => (Phi (t/T):ℂ)) n m-densityGcdKernel T Phi A B n m) c d =
      arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T (fun t => (Phi (t/T):ℂ))) c d-
      arithmeticPairing N (densityGcdKernel T Phi A B) c d := by
    simp only [arithmeticPairing,mul_sub,sum_sub_distrib]
  rw [heq] at hb
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNT
  have hlog : Real.log T*(1+Real.log N) ≤ 2*(Real.log T)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log T by linarith) (sub_nonneg.mpr hlogN)]
  have hp := hd T hT.le
  simp only [Real.rpow_zero,one_mul] at hp
  have hpow : (N:ℝ) ≤ (N:ℝ)^(7/4:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (by norm_num : (1:ℝ) ≤ 7/4)
  have htarg : (N:ℝ) ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact hpow.trans (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*H*H*Real.log T*(N:ℝ)*(1+Real.log N) := hb
    _ = C*H^2*(N:ℝ)*(Real.log T*(1+Real.log N)) := by ring
    _ ≤ C*H^2*(N:ℝ)*(2*(D*T^tau)) := mul_le_mul_of_nonneg_left
      (hlog.trans (mul_le_mul_of_nonneg_left hp (by norm_num))) (by positivity)
    _ ≤ C*H^2*(PRZZOptimalPowers.target N T)*(2*(D*T^tau)) := by gcongr
    _ = (2*C*H^2*D)*T^tau*PRZZOptimalPowers.target N T := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by unfold PRZZOptimalPowers.target; positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith

def centralCorrection (P : ℝ → ℂ) (Phi : ℝ → ℂ) (N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) : ℂ :=
  PRZZLiteralFourierLimit.fullModel P P Phi (Nat.log 2 N+2) N a T eps alpha beta-
    PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)

theorem centralCorrection_eq (P Phi : ℝ → ℂ) (N J : ℕ) (c d : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) :
    PRZZMixedPoisson.lift (fun a => centralCorrection P Phi N a T eps alpha beta) c d =
      PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.arithmeticResidual
        P P Phi (Nat.log 2 N+2) J N a T eps alpha beta) c d+
      PRZZMixedPoisson.lift (fun a => ∫ t in Icc T (2*T), scaledCutoff Phi T t*
        PRZZZeroCross.gammaDefect N a alpha beta t) c d := by
  have he (a : ℕ → ℂ) := PRZZCentralMainAssembly.model_main_arithmetic P P Phi
    (Nat.log 2 N+2) J N a T eps alpha beta
  unfold centralCorrection PRZZMixedPoisson.lift
  simp_rw [he]
  ring

theorem density_error_eq (P Phi : ℝ → ℂ) (N : ℕ) (c d : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ) (K : ℕ → ℕ → ℂ) :
    PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-arithmeticPairing N K c d-
      PRZZMixedPoisson.lift (fun a => centralCorrection P Phi N a T eps alpha beta) c d =
    (PRZZMixedPoisson.moment N c d alpha beta T (scaledCutoff Phi T)-
      PRZZMixedPoisson.lift (fun a => PRZZLiteralFourierLimit.fullModel P P Phi (Nat.log 2 N+2)
        N a T eps alpha beta) c d)+
    (arithmeticPairing N (PRZZDiagonalKernel.diagonalKernel N alpha beta T (scaledCutoff Phi T)) c d-
      arithmeticPairing N K c d) := by
  rw [← PRZZMixedMoment.diagonal_eq]
  unfold centralCorrection PRZZMixedPoisson.lift
  ring

/-- Replacement, both exhaustion removals and the evaluated Gamma main-kernel
comparison in one actual moment equation. The complete central correction
remains explicit; no bound for it is assumed or inferred here. -/
theorem density_reduction (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi)
    (H : ℝ) (hH : 0 ≤ H) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
          (fun t => (Phi (t/T):ℂ))-
        arithmeticPairing N (densityGcdKernel T Phi A B) c d-
        PRZZMixedPoisson.lift (fun a => centralCorrection (fun x => (P x:ℂ)) (fun x => (Phi x:ℂ))
          N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  let Psi : ℝ → ℂ := fun x => (Phi x:ℂ)
  have hPsi : ContDiff ℝ ∞ Psi := Complex.ofRealCLM.contDiff.comp hPhi.1
  have hsPsi : Function.support Psi ⊆ Icc (1:ℝ) 2 := by
    intro x hx
    exact hPhi.2 (fun hz => hx (by simp [Psi,hz]))
  have hcPsi : HasCompactSupport Psi := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2))
    intro x hx
    by_contra hn
    exact hx (hsPsi hn)
  have hdelta : 0 < delta := by linarith
  obtain ⟨Cf,hCf,hf⟩ := PRZZCappedMomentBridge.full_total_bound P Psi hP hm hlo hhi hl hright
    hPsi hcPsi hsPsi H hH S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨Cm,hCm,hmain⟩ := mainterm_absorbed Phi hPhi H S r delta hH hS hr hdelta
  refine ⟨Cf+Cm,by positivity,?_⟩
  filter_upwards [hf,hmain,eventually_ge_atTop (2:ℝ)] with T hf hmain hT
  intro c d N A B hc hd hN hscale hA hB hsep
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by norm_num : (4/7:ℝ) ≤ 1))
  have h1 := (hf c d N A B hc hd hN hscale hA hB hsep).2
  have h2 := hmain c d N A B hc hd hN hNT hA hB hsep
  have heq := density_error_eq (fun x => (P x:ℂ)) Psi N c d T eps
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) (densityGcdKernel T Phi A B)
  unfold PRZZCappedMomentBridge.fullError at h1
  unfold PRZZMellinSeparation.scaledCutoff at heq h1
  simp only [inv_mul_eq_div,Psi] at heq h1
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

theorem family_density_reduction (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi)
    (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (z w : Fin 7 → ℂ) (N : ℕ) (A B : ℂ),
      0 < theta → (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      let c := family (PRZZWitnessBasis.basis theta T) z
      let d := family (PRZZWitnessBasis.basis theta T) w
      ‖PRZZMixedPoisson.moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
          (fun t => (Phi (t/T):ℂ))-
        arithmeticPairing N (densityGcdKernel T Phi A B) c d-
        PRZZMixedPoisson.lift (fun a => centralCorrection (fun x => (P x:ℂ)) (fun x => (Phi x:ℂ))
          N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := density_reduction P Phi hP hm hlo hhi hl hright hPhi
    84 (by norm_num) S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro theta z w N A B htheta hz hw hN hscale hA hB hsep
  exact h _ _ N A B
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT z hz n)
    (fun n _ => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT w hw n)
    hN hscale hA hB hsep

theorem zero_removed_reduction (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi)
    (H : ℝ) (hH : 0 ≤ H) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (N J : ℕ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖PRZZMixedPoisson.moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
          (fun t => (Phi (t/T):ℂ))-
        arithmeticPairing N (densityGcdKernel T Phi A B) c d-
        PRZZMixedPoisson.lift (fun a => PRZZClassZeroCorrection.nonzeroResidual
          (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) (fun x => (Phi x:ℂ))
          (Nat.log 2 N+2) J N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d-
        PRZZMixedPoisson.lift (fun a => ∫ t in Icc T (2*T), (Phi (t/T):ℂ)*
          PRZZZeroCross.gammaDefect N a (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) c d‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  let Psi : ℝ → ℂ := fun x => (Phi x:ℂ)
  have hPsi : ContDiff ℝ ∞ Psi := Complex.ofRealCLM.contDiff.comp hPhi.1
  have hsPsi : Function.support Psi ⊆ Icc (1:ℝ) 2 := by
    intro x hx
    exact hPhi.2 (fun hz => hx (by simp [Psi,hz]))
  have hcPsi : HasCompactSupport Psi := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2))
    intro x hx
    by_contra hn
    exact hx (hsPsi hn)
  obtain ⟨C,hC,h⟩ := density_reduction P Phi hP hm hlo hhi hl hright hPhi
    H hH S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  obtain ⟨Z,hZ,hzero⟩ := PRZZClassZeroCorrection.mixed_power P hP hm hlo hhi hl hright
    Psi hPsi hcPsi hsPsi H eps r S (4/7) 0 hH heps hr hS (by norm_num) (by norm_num)
  refine ⟨C+Z,by positivity,?_⟩
  filter_upwards [h,hzero,eventually_ge_atTop (2:ℝ)] with T h hz hT
  intro c d N J A B hc hd hN hscale hA hB hsep
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by norm_num : (4/7:ℝ) ≤ 1))
  have h1 := h c d N A B hc hd hN hscale hA hB hsep
  have h2 := hz N c d A B hc hd hN hscale hNT hA hB hsep
  simp only [neg_zero,Real.rpow_zero,mul_one] at h2
  have hcor := centralCorrection_eq F Psi N J c d T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  rw [PRZZClassZeroCorrection.arithmetic_split] at hcor
  have heq : PRZZMixedPoisson.moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
      (fun t => (Phi (t/T):ℂ))-arithmeticPairing N (densityGcdKernel T Phi A B) c d-
      PRZZMixedPoisson.lift (fun a => PRZZClassZeroCorrection.nonzeroResidual F F Psi
        (Nat.log 2 N+2) J N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d-
      PRZZMixedPoisson.lift (fun a => ∫ t in Icc T (2*T), (Phi (t/T):ℂ)*
        PRZZZeroCross.gammaDefect N a (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) c d =
      (PRZZMixedPoisson.moment N c d (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
        (fun t => (Phi (t/T):ℂ))-arithmeticPairing N (densityGcdKernel T Phi A B) c d-
        PRZZMixedPoisson.lift (fun a => centralCorrection F Psi N a T eps
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d)+
      PRZZMixedPoisson.lift (fun a => PRZZCentralMainAssembly.zeroMismatch F F Psi (Nat.log 2 N+2)
        N a T eps (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) c d := by
    unfold PRZZMellinSeparation.scaledCutoff at hcor
    simp only [inv_mul_eq_div,Psi] at hcor
    linear_combination hcor
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hbudget : 1 ≤ T^delta*PRZZOptimalPowers.target N T :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (by linarith)) htarg
  rw [heq]
  apply (norm_add_le _ _).trans
  exact (add_le_add h1 h2).trans (by nlinarith only [mul_le_mul_of_nonneg_left hbudget hZ.le])

#print axioms zero_removed_reduction
#print axioms family_density_reduction
#print axioms density_reduction
#print axioms mainterm_absorbed
#print axioms centralCorrection_eq
#print axioms density_error_eq
end XiPrime8845.PRZZCappedMainTerm

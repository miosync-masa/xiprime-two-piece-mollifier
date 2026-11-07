import PRZZNegativeMellin
import PRZZCentralArithmeticJoin

/-! Weil and DI on the actual negative signedLiteral, including its space
and time integrals. The fixed spatial scale precedes the arithmetic
constants. No negative-literal equality or Fubini estimate is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Complex Finset
namespace XiPrime8845.PRZZNegativeOuter
open PRZZAStar PRZZAStarWindow PRZZMellinSeparation PRZZNegativeArithmetic
open PRZZNegativeMellin PRZZActualAggregate
set_option maxHeartbeats 5000000

theorem literal_linear (N d : ℕ) (D H T M B : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hPhi : ContDiff ℝ ∞ Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hs : sigma ≠ 0)
    (hbound : ∀ p ∈ window N T (M/2) (3*M), ∀ t : ℝ,
      ‖negativeSum N d D H a F1 F2 (fun y => F (M⁻¹*y)) alpha beta p.1 p.2 t‖ ≤ B*(1+|t|)) :
    ‖PRZZSignedCentral.signedLiteral (-1) N d D H T M a F1 F2 F Phi alpha beta sigma‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖PRZZAStarIntegralBound.common N d T (M/2) (3*M)
        (PRZZDyadicEnvelope.sourceW sigma) alpha beta p‖)*B*
          (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let J := fun p t => ∑ z ∈ indices N d D H, localizedMinus N d T (M/2) (3*M) a F1 F2
    (fun y => F (M⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta z p t
  have hi : Integrable (Function.uncurry J) := by
    apply integrable_finsetSum
    intro z hz
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact localized_integrable N d T (M/2) (3*M) a F1 F2 _ _ Phi alpha beta z
      (hF.comp (continuous_const.mul continuous_id)) (PRZZSourceWOuter.sourceW_continuous sigma hs)
      hPhi hsP hN hT (by positivity) (by positivity)
      (by have := (mem_Icc.mp hn.1).1; omega) (by have := (mem_Icc.mp hn.2).1; omega)
  have hm : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hc := PRZZPositiveOuter.common_integrable_positive N d T (M/2) (3*M)
    (PRZZDyadicEnvelope.sourceW sigma) alpha beta (PRZZSourceWOuter.sourceW_continuous sigma hs)
    hN hd hT (by positivity) (by positivity)
  have hj := (hc.norm.mul_const B).mul_prod hm
  have hb : ∀ q : (ℝ × ℝ) × ℝ, ‖Function.uncurry J q‖ ≤
      (‖PRZZAStarIntegralBound.common N d T (M/2) (3*M)
        (PRZZDyadicEnvelope.sourceW sigma) alpha beta q.1‖*B)*
        ((1+|q.2|)*‖mellin Phi (q.2*I)‖) := by
    intro q
    change ‖∑ z ∈ indices N d D H, localizedMinus N d T (M/2) (3*M) a F1 F2 _ _ Phi
      alpha beta z q.1 q.2‖ ≤ _
    rw [localized_sum]
    by_cases hp : q.1 ∈ window N T (M/2) (3*M)
    · have hx : 0 < q.1.1 := (div_pos (by positivity : 0 < M/2) (by exact_mod_cast hN)).trans_le hp.1.1
      have hy : 0 < q.1.2 := (div_pos hT (by positivity)).trans_le hp.2.1
      simp only [norm_mul,twist_norm _ _ (div_pos (mul_pos hx hy) hT),mul_one]
      exact (mul_le_mul_of_nonneg_left (hbound q.1 hp q.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
    · simp [PRZZAStarIntegralBound.common,hp]
  rw [literal_mellin N d D H T M a F1 F2 F Phi alpha beta sigma hF hPhi hsF hsP hN hT hM hs]
  change ‖(1/(2*Real.pi):ℂ)*(∫ q : (ℝ × ℝ) × ℝ, Function.uncurry J q)‖ ≤ _
  rw [norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left (integral_mono hi.norm hj hb) (by positivity)).trans_eq
  change (1/(2*Real.pi))*(∫ q : (ℝ × ℝ) × ℝ,
    ‖PRZZAStarIntegralBound.common N d T (M/2) (3*M) (PRZZDyadicEnvelope.sourceW sigma)
      alpha beta q.1‖*B*((1+|q.2|)*‖mellin Phi (q.2*I)‖) ∂volume.prod volume) = _
  rw [integral_prod _ hj]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,integral_mul_const]
  ring

/-- The actual native negative cell, with its original shift-slot swap,
now has the same finite-budget shape as the positive cell. -/
theorem negative_cell_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z M : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hM : 0 < M)
    (F0 F2 F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF2 : Continuous F2) (hcF2 : HasCompactSupport F2)
    (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d J : ℕ, ∀ T Q D : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖PRZZCentralArithmeticJoin.negativeCell N d J D T M
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) F (scaledCutoff F0 Q) F2 Phi alpha beta‖ ≤
        PRZZCentralArithmeticJoin.positiveBudget C w caps js K N d J eps eta b D T M Phi alpha beta := by
  have hcM : HasCompactSupport (fun y => F (M⁻¹*y)) :=
    hcF.comp_homeomorph (Homeomorph.mulLeft₀ M⁻¹ (inv_ne_zero hM.ne'))
  obtain ⟨caps,w,C,hC,hw,h⟩ := negative_weil_di hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ F0 F2 (fun y => F (M⁻¹*y)) hf hc hF2 hcF2
    (hF.comp (continuous_const.mul continuous_id)) hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d J T Q D alpha beta hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs Phi hPhi hsPhi
  apply literal_linear N d D ((J:ℝ)+1) T M _ _ _ _ F Phi beta alpha (alpha+beta)
    hF hPhi hsF hsPhi hN hd (by linarith) hM hs
  intro p hp t
  exact h N d T Q D ((J:ℝ)+1) p.1 p.2 t beta alpha hN hd hT hNT hdT hlog hfreq hbeta hz halpha

#print axioms literal_linear
#print axioms negative_cell_weil_di
end XiPrime8845.PRZZNegativeOuter

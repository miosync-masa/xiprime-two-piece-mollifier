import PRZZPositiveMellin
import PRZZLinearOuter

/-! Linear-frequency norm transfer for the literal A*, requiring continuity
only at positive W arguments. In particular sourceW needs no artificial
continuous extension across zero. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZPositiveOuter
open PRZZAStar PRZZAStarNu PRZZActualMellin PRZZAStarWindow PRZZMellinSeparation
open PRZZAStarRectangles PRZZNuCoefficient PRZZAStarIntegralBound
set_option maxHeartbeats 2000000

theorem common_integrable_positive (N d : ℕ) (T A B : ℝ) (W : ℝ → ℂ) (α β : ℂ)
    (hW : ContinuousOn W (Set.Ioi 0)) (hN : 0 < N) (hd : 0 < d)
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) :
    Integrable (common N d T A B W α β) := by
  have hs : IsCompact (window N T A B) := isCompact_Icc.prod isCompact_Icc
  apply (integrable_indicator_iff hs.measurableSet).mpr
  apply ContinuousOn.integrableOn_compact hs
  have hx : ∀ p ∈ window N T A B, 0 < p.1 :=
    fun p hp => (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
  have hy : ∀ p ∈ window N T A B, 0 < p.2 :=
    fun p hp => (div_pos hT (by positivity)).trans_le hp.2.1
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1:ℂ)^(α+β)) (window N T A B) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.cpow_const
      (fun p hp => by simpa using hx p hp)
  apply ContinuousOn.div
  · exact hW.comp ((continuousOn_const.mul continuous_fst.continuousOn).div
      continuous_snd.continuousOn (fun p hp => (hy p hp).ne')) (by
      intro p hp
      exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hx p hp)) (hy p hp))
  · exact continuousOn_const.mul hc
  · intro p hp
    exact mul_ne_zero (by exact_mod_cast hd.ne')
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne')))

theorem literal_linear_positive (N d : ℕ) (D H T A B M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : ContinuousOn W (Set.Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (_hM : 0 ≤ M)
    (hbound : ∀ p ∈ window N T A B, ∀ t : ℝ,
      ‖signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ M*(1+|t|)) :
    ‖literal N d D H T a F1 F2 FM W Phi α β‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖common N d T A B W α β p‖)*M*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let J := fun p t => ∑ z ∈ indices N d D H,
    localized N d T A B a F1 F2 FM W Phi α β z p t
  have hi : Integrable (Function.uncurry J) := by
    apply integrable_finsetSum
    intro z hz
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact PRZZPositiveMellin.localized_integrable_positive N d T A B a F1 F2 FM W Phi α β z hFM hW hPhi hsP
      hN hT hA hB (by have := (mem_Icc.mp hn.1).1; omega)
      (by have := (mem_Icc.mp hn.2).1; omega)
  have hm : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hc := common_integrable_positive N d T A B W α β hW hN hd hT hA hB
  have hj := (hc.norm.mul_const M).mul_prod hm
  have hb : ∀ q : (ℝ × ℝ) × ℝ, ‖Function.uncurry J q‖ ≤
      (‖common N d T A B W α β q.1‖*M)*((1+|q.2|)*‖mellin Phi (q.2*I)‖) := by
    intro q
    change ‖∑ z ∈ indices N d D H, localized N d T A B a F1 F2 FM W Phi α β z q.1 q.2‖ ≤ _
    rw [localized_nu]
    change ‖common N d T A B W α β q.1 * mellin Phi (q.2*I) *
      twist (q.1.1*q.1.2/T) q.2 * signedSum N d D H a F1 F2 FM α β q.1.1 q.1.2 q.2‖ ≤ _
    by_cases hp : q.1 ∈ window N T A B
    · have hx : 0 < q.1.1 := (div_pos hA (by exact_mod_cast hN)).trans_le hp.1.1
      have hy : 0 < q.1.2 := (div_pos hT (by positivity)).trans_le hp.2.1
      simp only [norm_mul,twist_norm _ _ (div_pos (mul_pos hx hy) hT),mul_one]
      exact (mul_le_mul_of_nonneg_left (hbound q.1 hp q.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
    · simp [common,hp]
  rw [PRZZPositiveMellin.literal_mellin_positive N d D H T A B a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hT hA hB]
  change ‖(1/(2*Real.pi):ℂ)*(∫ t, ∫ p, J p t)‖ ≤ _
  have hprod := integral_prod (Function.uncurry J) hi
  simp only [Function.uncurry] at hprod
  rw [← integral_integral_swap hi,← hprod,norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left (integral_mono hi.norm hj hb) (by positivity)).trans_eq
  change (1/(2*Real.pi))*(∫ q : (ℝ × ℝ) × ℝ,
    ‖common N d T A B W α β q.1‖*M*((1+|q.2|)*‖mellin Phi (q.2*I)‖) ∂volume.prod volume) = _
  rw [integral_prod _ hj]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,integral_mul_const]
  ring

#print axioms common_integrable_positive
#print axioms literal_linear_positive
end XiPrime8845.PRZZPositiveOuter

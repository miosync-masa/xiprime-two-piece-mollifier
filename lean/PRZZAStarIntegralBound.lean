import PRZZAStarRectangles

/-! Norm transfer to the literal A*, retaining the outer common-window
L1 mass and the Mellin L1 mass. All integrability is supplied for the
actual kernel. Rectangle estimates remain explicit quantitative inputs;
no uniform-in-height bound on the outer mass is silently asserted. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZAStarIntegralBound
open PRZZAStar PRZZAStarNu PRZZActualMellin PRZZAStarWindow PRZZMellinSeparation
open PRZZAStarRectangles PRZZNuCoefficient
set_option maxHeartbeats 2000000

def common (N d : ℕ) (T A B : ℝ) (W : ℝ → ℂ) (α β : ℂ) (p : ℝ × ℝ) : ℂ :=
  (window N T A B).indicator
    (fun p : ℝ × ℝ => W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(α+β))) p

theorem common_integrable (N d : ℕ) (T A B : ℝ) (W : ℝ → ℂ) (α β : ℂ)
    (hW : Continuous W) (hN : 0 < N) (hd : 0 < d)
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
  · exact hW.comp_continuousOn ((continuousOn_const.mul continuous_fst.continuousOn).div
      continuous_snd.continuousOn (fun p hp => (hy p hp).ne'))
  · exact continuousOn_const.mul hc
  · intro p hp
    exact mul_ne_zero (by exact_mod_cast hd.ne')
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hx p hp).ne')))

theorem literal_bound (N d : ℕ) (D H T A B M : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (_hM : 0 ≤ M)
    (hbound : ∀ p ∈ window N T A B, ∀ t : ℝ,
      ‖signedSum N d D H a F1 F2 FM α β p.1 p.2 t‖ ≤ M) :
    ‖literal N d D H T a F1 F2 FM W Phi α β‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖common N d T A B W α β p‖)*M*
        (∫ t : ℝ, ‖mellin Phi (t*I)‖) := by
  let J := fun p t => ∑ z ∈ indices N d D H,
    localized N d T A B a F1 F2 FM W Phi α β z p t
  have hi : Integrable (Function.uncurry J) := by
    apply integrable_finsetSum
    intro z hz
    have hn := mem_product.mp (mem_filter.mp (mem_product.mp hz).1).1
    exact localized_integrable N d T A B a F1 F2 FM W Phi α β z hFM hW hPhi hsP
      hN hT hA hB (by have := (mem_Icc.mp hn.1).1; omega)
      (by have := (mem_Icc.mp hn.2).1; omega)
  have hm : Integrable (fun t : ℝ => mellin Phi (t*I)) := by
    simpa [VerticalIntegrable] using PRZZSmoothMellin.vertical_integrable Phi 1 2 (by norm_num) hsP hPhi
  have hc := common_integrable N d T A B W α β hW hN hd hT hA hB
  have hj := (hc.norm.mul_const M).mul_prod hm.norm
  have hb : ∀ q : (ℝ × ℝ) × ℝ, ‖Function.uncurry J q‖ ≤
      (‖common N d T A B W α β q.1‖*M)*‖mellin Phi (q.2*I)‖ := by
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
  rw [PRZZAStarTransform.literal_mellin N d D H T A B a F1 F2 FM W Phi α β
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
    ‖common N d T A B W α β q.1‖*M*‖mellin Phi (q.2*I)‖ ∂volume.prod volume) = _
  rw [integral_prod _ hj]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,integral_mul_const]
  ring

/-- Aggregates every original dyadic pair rectangle before applying the
actual integral transfer. The displayed two L1 costs are retained. -/
theorem literal_bound_of_rectangles (N d : ℕ) (D H T A B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (α β : ℂ) (b : ℕ → ℕ → ℝ)
    (hFM : Continuous FM) (hW : Continuous W)
    (hPhi : ContDiff ℝ ∞ Phi) (hsP : Function.support Phi ⊆ Set.Icc (1:ℝ) 2)
    (hsM : Function.support FM ⊆ Set.Icc A B)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hA : 0 < A) (hB : 0 < B)
    (hb : ∀ j l, 0 ≤ b j l)
    (hrect : ∀ p ∈ window N T A B, ∀ t : ℝ,
      ∀ j ∈ range (Nat.log 2 N+1), ∀ l ∈ range (Nat.log 2 N+1),
      ‖∑ k ∈ (frequencies d D H).image freq, nu (frequencies d D H) p.1 p.2 k *
        rectangle N d j l a F1 F2 FM α β p.1 t k‖ ≤ b j l) :
    ‖literal N d D H T a F1 F2 FM W Phi α β‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖common N d T A B W α β p‖)*
        (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1), b j l)*
        (∫ t : ℝ, ‖mellin Phi (t*I)‖) := by
  apply literal_bound N d D H T A B _ a F1 F2 FM W Phi α β
    hFM hW hPhi hsP hsM hN hd hT hA hB
    (sum_nonneg (fun j _ => sum_nonneg (fun l _ => hb j l)))
  intro p hp t
  rw [signedSum_rectangles]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  exact (norm_sum_le _ _).trans (sum_le_sum (fun l hl => hrect p hp t j hj l hl))

#print axioms common_integrable
#print axioms literal_bound
#print axioms literal_bound_of_rectangles
end XiPrime8845.PRZZAStarIntegralBound

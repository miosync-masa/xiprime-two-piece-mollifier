import PRZZTailTimeSum
import PRZZDyadicArithmeticMass

/-! Substitute the actual reciprocal arithmetic pair coefficients into the
masked finite Fourier-tail estimate. Subsets retain coprimality and product
restrictions. Source row geometry is still explicit. -/
noncomputable section
open scoped BigOperators FourierTransform ContDiff
open MeasureTheory Set
namespace XiPrime8845.PRZZArithmeticFourierTail
open PRZZTailTimeSum PRZZGCoefficient
set_option maxHeartbeats 3000000

theorem pair_integrated (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (a b S r eD eH A : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (js : List ℕ) (N j l : ℕ) (rows : Finset (ℕ × ℕ))
      (data : ℕ × ℕ → Row) (keep : ℕ × ℕ → Prop) [DecidablePred keep]
      (freq : Finset ℕ) (p m : (ℕ × ℕ) → ℝ → ℕ → ℂ)
      (d T : ℝ) (alpha beta : ℂ) (Phi : ℝ → ℂ),
      1 ≤ N → rows ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      0 < d → 36 ≤ T → 1 ≤ Real.log T → ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      Continuous Phi →
      (∀ i ∈ rows, keep i → Domain d T b eD eH (data i)) →
      (∀ i ∈ rows, ∀ t ∈ Icc T (2*T), ∀ v, ‖p i t v‖ ≤ 1 ∧ ‖m i t v‖ ≤ 1) →
      ‖∫ t in Icc T (2*T), Phi (t/T)*(∑ i ∈ rows,
        (((coefficient js i.1:ℂ)*star (coefficient js i.2:ℂ))/((i.1:ℂ)*(i.2:ℂ)))*
          (if keep i then finiteTail F T t alpha beta (data i) freq (p i t) (m i t) else 0))‖ ≤
        K*T^(-A)*(Real.log N)^(2*degree js)*(∫ t in Icc T (2*T), ‖Phi (t/T)‖) := by
  obtain ⟨K,hK,h⟩ := integrated F hF hsF a b S r eD eH A ha hb hS hr heD he
  refine ⟨K,hK,?_⟩
  intro js N j l rows data keep inst freq p m d T alpha beta Phi hN hrows hd hT hlog halpha hsep hPhi hdom hphase
  have hh := h (ℕ × ℕ) rows data keep
    (fun i => ((coefficient js i.1:ℂ)*star (coefficient js i.2:ℂ))/((i.1:ℂ)*(i.2:ℂ)))
    freq p m d T alpha beta Phi hd hT hlog halpha hsep hPhi hdom hphase
  have hm := PRZZDyadicArithmeticMass.weighted_pair_mass js N j l hN rows hrows
    (fun _ => 1) 1 (by norm_num) (by intro i hi; simp)
  simp only [mul_one] at hm
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by positivity))
    (integral_nonneg (fun t => norm_nonneg _))

/-- A reusable exchange criterion with its analytic obligations exposed.
It is not yet a measurability supplier for the actual time-dependent Fourier
weight. The summable envelope must be uniform throughout the time interval. -/
theorem time_swap (f : ℕ → ℝ → ℂ) (w : ℕ → ℝ) (T : ℝ)
    (hw : Summable w) (_hw0 : ∀ n, 0 ≤ w n)
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc T (2*T))))
    (hb : ∀ n, ∀ t ∈ Icc T (2*T), ‖f n t‖ ≤ w n) :
    (∑' n, ∫ t in Icc T (2*T), f n t) =
      ∫ t in Icc T (2*T), ∑' n, f n t := by
  have hc (n : ℕ) : IntegrableOn (fun _ : ℝ => w n) (Icc T (2*T)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hi (n : ℕ) : IntegrableOn (f n) (Icc T (2*T)) := by
    apply (hc n).mono' (hf n)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb n t ht
  apply integral_tsum_of_summable_integral_norm hi
  apply (hw.mul_right (volume (Icc T (2*T))).toReal).of_nonneg_of_le
  · intro n; exact integral_nonneg (fun t => norm_nonneg _)
  · intro n
    have hh := setIntegral_mono_on (hi n).norm (hc n) measurableSet_Icc (hb n)
    simpa only [setIntegral_const,smul_eq_mul,Measure.real,mul_comm] using hh

#print axioms pair_integrated
#print axioms time_swap
end XiPrime8845.PRZZArithmeticFourierTail

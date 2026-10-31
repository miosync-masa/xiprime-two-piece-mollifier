import WuPhaseCrossings
import WuAuxiliaryHorizontal

/-! Exact logarithmic-derivative comparison with the original eta.
The finite divisor is retained along any supplied zero-free detour.
On parallel vertical edges each removed factor costs at most pi, with
its full analytic multiplicity. No limiting contour is assumed here. -/
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory intervalIntegral
namespace XiPrime8845.WuDeflatedContour
open WuAuxiliary WuLittlewood WuFiniteDeflation WuCriticalDeflation
set_option maxHeartbeats 2000000

theorem divisor_logDeriv (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (hs : ∀ c ∈ Z, s ≠ c) :
    logDeriv (divisor Z m) s = ∑ c ∈ Z, (m c:ℂ)/(s-c) := by
  unfold divisor
  rw [logDeriv_prod (f := fun c z : ℂ => (z-c)^(m c))
    (fun c hc => pow_ne_zero _ (sub_ne_zero.mpr (hs c hc)))
    (fun c _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [logDeriv_fun_pow (by fun_prop)]
  simp [logDeriv_apply,div_eq_mul_inv]

theorem eta_logDeriv {L u v : ℝ} (d : Data L u v) (s : ℂ)
    (hs : ∀ c ∈ d.zeros, s ≠ c) (hg : d.etaPart s ≠ 0) :
    logDeriv (WuAuxiliary.eta L) s = logDeriv d.curve s+
      ∑ c ∈ d.zeros, (multiplicity L c:ℂ)/(s-c) := by
  have he : WuAuxiliary.eta L = fun z => divisor d.zeros (WuCriticalDeflation.multiplicity L) z*d.etaPart z :=
    funext d.eta_factor
  rw [he,logDeriv_mul s (by
    unfold divisor; exact Finset.prod_ne_zero_iff.mpr (fun c hc =>
      pow_ne_zero _ (sub_ne_zero.mpr (hs c hc)))) hg
    (divisor_entire _ _ s) (d.eta_entire s),divisor_logDeriv _ _ _ hs]
  change _ = logDeriv (fun z => I^d.totalOrder*d.etaPart z) s+_
  rw [logDeriv_const_mul _ _ (pow_ne_zero _ I_ne_zero)]
  ring

/-- Applies in particular to a piecewise smooth indentation, segment by
segment. gamma' is the supplied velocity; integrability is explicit. -/
theorem detour_integral {L u v : ℝ} (d : Data L u v)
    (γ γ' : ℝ → ℂ) (a b : ℝ)
    (hs : ∀ t ∈ uIcc a b, ∀ c ∈ d.zeros, γ t ≠ c)
    (hg : ∀ t ∈ uIcc a b, d.etaPart (γ t) ≠ 0)
    (hi : IntervalIntegrable (fun t => γ' t*logDeriv d.curve (γ t)) volume a b)
    (hp : ∀ c ∈ d.zeros, IntervalIntegrable (fun t => γ' t/(γ t-c)) volume a b) :
    (∫ t in a..b, γ' t*logDeriv (WuAuxiliary.eta L) (γ t)) =
      (∫ t in a..b, γ' t*logDeriv d.curve (γ t))+
        ∑ c ∈ d.zeros, (multiplicity L c:ℂ)*(∫ t in a..b, γ' t/(γ t-c)) := by
  have hterm := fun c hc => (hp c hc).const_mul (multiplicity L c:ℂ)
  simp_rw [← intervalIntegral.integral_const_mul]
  have hsum : IntervalIntegrable (fun t => ∑ c ∈ d.zeros,
      (multiplicity L c:ℂ)*(γ' t/(γ t-c))) volume a b := by
    exact (IntervalIntegrable.sum d.zeros hterm).congr (fun t _ => by simp only [Finset.sum_apply])
  rw [← integral_finsetSum hterm,← integral_add hi hsum]
  apply integral_congr
  intro t ht
  dsimp only
  rw [eta_logDeriv d _ (hs t ht) (hg t ht),mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

theorem vertical_pole_bound (x u v : ℝ) (c : ℂ) (huv : u ≤ v)
    (hc : ∀ t ∈ Icc u v, point x t ≠ c) :
    |(∫ t in u..v, I/(point x t-c)).im| ≤ Real.pi := by
  have he (t : ℝ) : (t:ℂ)+((-x:ℝ):ℂ)*I-(-I*c) = -I*(point x t-c) := by
    unfold point; push_cast; ring_nf; simp
  have hf (t : ℝ) : I/(point x t-c) = ((t:ℂ)+((-x:ℝ):ℂ)*I-(-I*c))⁻¹ := by
    rw [he,mul_inv_rev]
    simp [div_eq_mul_inv,mul_comm]
  simp_rw [hf]
  apply Zeta23.XiPrime.ZeroCount.abs_im_integral_inv_sub_le_pi huv (-x) (-I*c)
  intro t ht hh
  have hz : -I*(point x t-c) = 0 := by rw [← he,hh,sub_self]
  exact (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr (hc t ht))) hz

theorem vertical_comparison {L u v : ℝ} (d : Data L u v) (x : ℝ) (huv : u ≤ v)
    (hs : ∀ t ∈ Icc u v, ∀ c ∈ d.zeros, point x t ≠ c)
    (hg : ∀ t ∈ Icc u v, d.etaPart (point x t) ≠ 0) :
    |(∫ t in u..v, I*logDeriv (WuAuxiliary.eta L) (point x t)).im| ≤
      |(∫ t in u..v, I*logDeriv d.curve (point x t)).im|+Real.pi*d.totalOrder := by
  have hp (c : ℂ) (hc : c ∈ d.zeros) :
      IntervalIntegrable (fun t => I/(point x t-c)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by unfold point; fun_prop)
    intro t ht
    exact sub_ne_zero.mpr (hs t (by simpa [uIcc_of_le huv] using ht) c hc)
  have hi : IntervalIntegrable (fun t => I*logDeriv d.curve (point x t)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : d.curve (point x t) ≠ 0 := mul_ne_zero (pow_ne_zero _ I_ne_zero)
      (hg t (by simpa [uIcc_of_le huv] using ht))
    have ha : AnalyticAt ℂ d.curve (point x t) := analyticAt_const.mul (d.eta_entire.analyticAt _)
    exact (continuousAt_const.mul (((ha.deriv.continuousAt).div ha.continuousAt hn).comp
      (f := fun t => point x t) (by unfold point; fun_prop))).continuousWithinAt
  have he := detour_integral d (point x) (fun _ => I) u v
    (by simpa [uIcc_of_le huv] using hs) (by simpa [uIcc_of_le huv] using hg) hi hp
  rw [he,add_im,Complex.im_sum]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ c ∈ d.zeros, (multiplicity L c:ℝ)*Real.pi := by
      apply Finset.sum_le_sum
      intro c hc
      simp only [mul_im,natCast_re,natCast_im,zero_mul,add_zero,abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ (multiplicity L c:ℝ) from Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (vertical_pole_bound x u v c huv
        (fun t ht => hs t ht c hc)) (Nat.cast_nonneg _)
    _ = Real.pi*d.totalOrder := by simp [Data.totalOrder,Finset.mul_sum,mul_comm]

#print axioms divisor_logDeriv
#print axioms eta_logDeriv
#print axioms detour_integral
#print axioms vertical_pole_bound
#print axioms vertical_comparison
end XiPrime8845.WuDeflatedContour
